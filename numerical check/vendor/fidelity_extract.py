#!/usr/bin/env python3
"""Extract DLMF-tagged Lean declarations and check supported numeric claims.

The extractor parses Lean conclusions into numerical expressions using the
convention registry in oracle_bindings.py and compares sampled evaluations
with mpmath. Unsupported statements return an explicit unchecked verdict.
Use ../run_stale.py to run isolated Chapter 7 checks with resource limits.
"""
import json, os, re, sys, pathlib, signal, contextlib
import mpmath as mp

_PROGRESS = os.environ.get("FIDELITY_PROGRESS") == "1"


_TRIG_SIN_HEADS = {"sin", "Real.sin", "Complex.sin"}
_TRIG_COS_HEADS = {"cos", "Real.cos", "Complex.cos"}


def _complexify_trig(body, var):
    """For a Fourier-type series summand containing EXACTLY ONE sin/cos factor whose
    argument involves the index `var`, return (body', proj): body' replaces that factor
    with cexp(I·arg) and proj ∈ {'im','re'} projects the complexified sum back. The
    projection is only valid when the remaining factors are real — which is NOT checked
    here; the caller gates every projected candidate against genuine partial sums of the
    original series (_accelerated_nsum's direction gate), so a wrong projection is
    dropped, never returned. Returns None when the shape doesn't apply."""
    hits = []

    def walk(nd):
        if isinstance(nd, tuple):
            if nd[0] == "app" and isinstance(nd[1], tuple) and nd[1][0] == "var" \
                    and nd[1][1] in (_TRIG_SIN_HEADS | _TRIG_COS_HEADS) and len(nd[2]) == 1:
                sub = set()
                collect_free(nd[2][0], sub)
                if var in sub:
                    hits.append(nd)
                    return
            for x in nd[1:]:
                walk(x)
        elif isinstance(nd, list):
            for x in nd:
                walk(x)

    walk(body)
    if len(hits) != 1:
        return None
    target = hits[0]
    proj = "im" if target[1][1] in _TRIG_SIN_HEADS else "re"

    def rebuild(nd):
        if nd is target:
            return ("app", ("var", "cexp"), [("bin", "*", ("var", "I"), target[2][0])])
        if isinstance(nd, tuple):
            return tuple(nd[:1]) + tuple(rebuild(x) for x in nd[1:])
        if isinstance(nd, list):
            return [rebuild(x) for x in nd]
        return nd

    return rebuild(body), proj


def _bounded_nsum(f, start=0, bilateral=False, maxterms=4000, tol=mp.mpf("1e-25"),
                  accelerate=True, alt=None):
    """Truncated series with a HARD term cap. mp.nsum's adaptive precision/extrapolation can
    balloon memory on a (complex) series that converges slowly or not at all — and an OOM is a
    far worse failure than an honest skip. So we sum plain partial terms at the ambient
    precision and require the tail to have visibly settled; if it hasn't within `maxterms`,
    we RAISE (→ the sample point is dropped, never trusted with a half-converged value)."""
    total = mp.mpf(0)
    if bilateral:
        total = f(0)
        hist = []
        for n in range(1, maxterms // 2):
            total += f(n) + f(-n)
            hist.append(total)
            if len(hist) > 48:
                hist.pop(0)
            scale = tol * max(mp.mpf(1), abs(total))
            if n > 48 and all(abs(total - h) < scale for h in hist):
                return total
        raise Unparseable("series-not-converged")
    hist = []
    for n in range(start, start + maxterms):
        total += f(n)
        hist.append(total)
        if len(hist) > 48:
            hist.pop(0)
        # the TAIL must have SETTLED, not a single term: every partial sum over the last
        # window within tol of the current total. A lone small term is not convergence — an
        # oscillatory series (Σ cos(2πmx)/m²) has a tiny term at each cos zero-crossing, which
        # would otherwise return a half-summed value (a false FAIL against the true closed form).
        scale = tol * max(mp.mpf(1), abs(total))
        if n > start + 48 and all(abs(total - h) < scale for h in hist):
            return total
    # Naive partial sums never settled — the series converges too slowly for direct
    # summation (e.g. Σ 1/(x+n)² with tail ~1/N, or Σ sin(nθ)/n²). Fall back to
    # convergence acceleration, validated for ACTUAL convergence (not regularization).
    # `accelerate=False` SKIPS this fallback and RAISES instead: mp.nsum's dps=100
    # Euler–Maclaurin (finite-difference derivatives of a ψ-and-ascPochhammer summand) is a
    # long UNINTERRUPTIBLE C loop that the per-sample SIGALRM budget cannot stop, so on the
    # DLMF 15.8 log-case series (O(k)-per-term Pochhammer × ψ) it hangs the whole child past
    # the 240 s harness cap. Skipping accel makes an unsettled (near-boundary, ratio→1) sample
    # DROP fast instead — its neighbours strictly inside the domain still settle in the naive
    # loop and decide the row. Soundness is unchanged: a dropped point is never scored, only a
    # genuinely-settled partial sum is (a false identity still FAILs at the settled points).
    if not accelerate:
        raise Unparseable("series-not-converged")
    return _accelerated_nsum(f, start, total, maxterms, alt=alt)


def _accelerated_nsum(f, start, partial, ncap, alt=None):
    """Euler–Maclaurin / Richardson extrapolation of a slowly-convergent tail.

    SOUNDNESS — two-method agreement is NOT enough (both extrapolators return the same
    *regularized* value for a divergent series, e.g. Σ1/n ≈ 6.46, and so agree). The honest
    test is that the extrapolated value is the limit the genuine PARTIAL SUMS approach: for a
    convergent series the residual |v − S_N| shrinks as N grows, while a divergent series'
    partials run away from any finite regularized value. So we recompute two real partial
    sums (Sₙ at the cap, S₄ₙ four times deeper) and require the residual to shrink toward v
    and the terms to be decaying — else RAISE rather than trust a regularized value. This
    real-partial-sum gate is applied INDEPENDENTLY to each extrapolation method, so the
    method is just a candidate generator: only a value the genuine partials approach is ever
    returned (no method can smuggle a regularized sum past the gate)."""
    s1 = partial                                    # Σ over [start, start+ncap)
    # the deeper validation partial extends by a CAPPED extra block (≤3000 terms) so the
    # residual recomputation stays under the per-sample eval budget on an expensive summand
    # (ψ′ at 16k points blew the 3s gate); the residual-ratio gate is depth-agnostic for
    # soundness — it only needs S_deep strictly past S₁, not a fixed 4× depth.
    deep = start + ncap + min(3 * ncap, 3000)
    try:
        s2 = s1 + mp.fsum(f(n) for n in range(start + ncap, deep))
        tail_term = abs(f(deep - 1))
    except _EvalTimeout:
        raise
    except Exception:
        raise Unparseable("series-not-converged")
    if tail_term >= mp.mpf("1e-3"):                 # leading tail term hasn't decayed → reject
        raise Unparseable("series-not-converged")
    # COMPLEXIFIED trig candidates first (see _complexify_trig): for a Fourier-type summand
    # sin(nθ)·g(n) / cos(nθ)·g(n), Levin/Shanks on the REAL series stall at the extrapolator's
    # oscillation-truncation floor (~1e-9 for Σ sin((n+1)θ)/(n+1)² near θ→0, the Cl₂ 25.12.7
    # row — enough to pass the direction gate below yet FAIL a true identity), while the same
    # accelerators on the unit-modulus POWER series e^{inθ}g(n) reach ~1e-32 (measured on the
    # full default θ grid). Each projected candidate must still pass the SAME partial-sum
    # direction gate against the ORIGINAL series' s1/s2 — a wrong projection (complex-valued
    # g) or a divergent complexification can never be returned.
    if alt is not None:
        fc, proj = alt
        for _meth in ("s", "l", "a"):
            try:
                with mp.workdps(100):
                    vc = mp.nsum(fc, [start, mp.inf], method=_meth)
            except _EvalTimeout:
                raise
            except Exception:
                continue
            v = mp.im(vc) if proj == "im" else mp.re(vc)
            if not mp.isfinite(v):
                continue
            r1, r2 = abs(v - s1), abs(v - s2)
            if r2 <= mp.mpf("0.6") * r1:
                return v
    # The alternating-series / Euler transform ("a") nails conditionally-convergent
    # alternating series (Σ(-1)ⁿψ′(n)) — and is CHEAP (a handful of terms) where Euler–Maclaurin
    # ("e") is both wrong (~1e-3 off) and ruinously slow (finite-diff derivatives of ψ′).
    # Richardson ("r") nails smooth POSITIVE power-law tails (Σψ′(n+1)/n ~ Σ1/n², §5.16.2) in a
    # fraction of a second — exactly the regime where "e" is correct but ruinously slow (~22s on
    # ψ′, blowing the eval budget → a false timeout-skip of a true identity). So we try the cheap
    # "a" and "r" first, falling through to "e" only when both miss; each candidate must still
    # pass the partial-sum residual gate, so the order only affects cost, never soundness.
    #
    # PRECISION, not tolerance: an oscillatory power-tail (Σcos(2πmx)/m^{2n}, DLMF 24.8.1) can
    # have a genuinely-convergent Euler-transform accelerant whose OWN internal roundoff caps its
    # residual well above the 1e-18 equality gate at the ambient dps=30 (empirically ~4e-16 for
    # the slowest-converging row, n=1) — an accelerator-precision artifact, not a wrong identity:
    # the real partial sums keep closing in past that point, and pushing the SAME method's working
    # precision up recovers the extra digits at a rate far better than 1:1 with dps (measured:
    # dps=85 already clears 1e-18 with 3 orders of margin on the worst sampled point; dps=100 is
    # the safety margin adopted here). s1/s2 above are untouched, still computed at ambient dps=30,
    # so the residual-ratio gate is exactly as strict as before — only the extrapolator's own
    # arithmetic precision goes up, nothing about what counts as convergence is loosened. Every
    # candidate is computed at the boosted precision FIRST (a strict refinement of the same
    # extrapolator, never a different method), falling back to the ambient-precision value only if
    # the boosted evaluation itself is unavailable (raises or non-finite).
    for meth in ("a", "r", "e"):
        v = None
        try:
            with mp.workdps(100):
                v = mp.nsum(f, [start, mp.inf], method=meth)
        except _EvalTimeout:
            raise
        except Exception:
            v = None
        if v is None or not mp.isfinite(v):
            try:
                v = mp.nsum(f, [start, mp.inf], method=meth)
            except _EvalTimeout:
                raise
            except Exception:
                continue
        if not mp.isfinite(v):
            continue
        r1, r2 = abs(v - s1), abs(v - s2)
        # converging: residual to the deeper partial is smaller (≤0.6×). A divergent series
        # fails this (its partials move AWAY from v); a regularized value fails it too.
        if r2 <= mp.mpf("0.6") * r1:
            return v
    raise Unparseable("series-not-converged")


def _bounded_nprod(f, start=0, maxterms=4000, tol=mp.mpf("1e-25")):
    """Truncated infinite product with the same hard-cap discipline as `_bounded_nsum`: the
    PARTIAL PRODUCTS must settle. We accumulate plain partial products at the ambient
    precision and require the tail window to have visibly converged; if it hasn't within
    `maxterms`, we fall back to accelerating the log-sum ∏f = exp(∑ log f) — but ONLY when a
    genuine partial-product residual test confirms convergence. Otherwise RAISE (→ honest
    skip), never returning a half-converged value or letting an adaptive routine balloon
    memory. SOUNDNESS: identical to `_bounded_nsum` — a window-of-settled partials, not a
    single near-1 factor (a factor can momentarily touch 1 while the product still drifts)."""
    total = mp.mpf(1)
    hist = []
    for n in range(start, start + maxterms):
        total *= f(n)
        hist.append(total)
        if len(hist) > 48:
            hist.pop(0)
        # the TAIL of PARTIAL PRODUCTS must have SETTLED: every partial product over the last
        # window within tol of the current total. A lone factor ≈ 1 is not convergence — the
        # running product can still be drifting (slowly-convergent ∏(1+a/k²) with factor→1 but
        # partials only at 1+O(1/N)); that route is handled by the log-sum acceleration below.
        scale = tol * max(mp.mpf(1), abs(total))
        if n > start + 48 and all(abs(total - h) < scale for h in hist):
            return total
    # Naive partial products never settled — the product converges too slowly for direct
    # truncation (factors 1+O(1/k²), partials ~exp(C/N)). Accelerate the LOG-sum tail,
    # validated for ACTUAL convergence by a real partial-product residual test (a divergent
    # product's partials run away from any finite value).
    return _accelerated_nprod(f, start, total, maxterms)


def _richardson_logprod(f, start, base=16, levels=11, gate=mp.mpf("1e-20")):
    """Slowly-convergent infinite product ∏ₙ f(n) via step-halving (Romberg) Richardson
    extrapolation of the LOG partial sums — the reliable route where `_accelerated_nprod`'s
    single Euler–Maclaurin `nsum` stalls (it returns a value ~1e-4 off for the DLMF Gamma
    products, correctly rejected by its own residual gate, leaving the row an `undersampled`
    skip).

    The DLMF Weierstrass / ratio-Gamma products (5.8.2 `∏(1+z/k)e^{-z/k}`, 5.8.5
    `∏ₖ∏ⱼ(aⱼ+k)/(bⱼ+k)` under the balance ∑aⱼ=∑bⱼ) have log-partial residual that is a clean
    asymptotic series in 1/N: log P_N = log P_∞ + c₁/N + c₂/N² + … (the tail ∑_{k>N} log f(k)
    with log f(k)=O(1/k²)). Sampling log P_N at N = base·2ʲ halves the step h=1/N each level,
    so the Romberg table T[k] = (2ᵏ·T[k−1](j+1) − T[k−1](j))/(2ᵏ−1) eliminates successive 1/N
    powers and converges to full precision where naive truncation stalls at O(1/N).
    `exp(∑ log fₙ) = ∏ fₙ` exactly for ANY branch of log, so the recovered product is
    branch-independent (only the near-1 tail factors — whose principal logs are the continuous
    accumulation Lean's product converges to — drive the extrapolation).

    SOUNDNESS: returns ONLY when the extrapolation STABILISES — the change across the last
    Richardson diagonal step is below `gate` (≪ the eq tolerance TOL=1e-18), a genuine
    convergence witness. A DIVERGENT product (an UNBALANCED 5.8.5, ∑aⱼ≠∑bⱼ, has log f(k)=O(1/k)
    harmonic) never stabilises — its extrapolant keeps moving with maxN, stab≈6e-2 ≫ gate — so
    it RAISES → honest skip, never a fabricated value. A zero factor RAISES (log undefined).
    Validated against the independently mp.gamma-computed RHS at rel ≤ 1e-28 on real / complex
    / m=1..3 samples (docs/verification/resolve-surfaces/probe_n5*.py), so a WRONG identity
    still FAILs, never masked."""
    Ns = [base * (2 ** j) for j in range(levels)]
    marks = set(Ns)
    acc = mp.mpf(0)
    col = []
    for n in range(start, Ns[-1]):
        v = f(n)
        if v == 0:
            raise Unparseable("product-zero-factor")
        acc += mp.log(v)
        if (n + 1) in marks:
            col.append(acc + mp.mpf(0))
    if len(col) < 2:
        raise Unparseable("product-not-converged")
    table = [col]
    for k in range(1, levels):
        prev = table[k - 1]
        fac = mp.mpf(2) ** k
        table.append([(fac * prev[j + 1] - prev[j]) / (fac - 1)
                      for j in range(len(prev) - 1)])
    d1, d2 = table[-1][0], table[-2][0]            # final extrapolant + previous diagonal
    stab = abs(d1 - d2) / max(mp.mpf(1), abs(d1))
    if not mp.isfinite(stab) or stab > gate:
        raise Unparseable("product-not-converged")
    v = mp.e ** d1
    if not mp.isfinite(v):
        raise Unparseable("product-not-converged")
    return v


def _accelerated_nprod(f, start, partial, ncap):
    """Euler–Maclaurin acceleration of ∏f = exp(∑ Log f) over a slowly-convergent tail.

    SOUNDNESS — mirrors `_accelerated_nsum`. The honest test is that the accelerated value is
    the limit the genuine PARTIAL PRODUCTS approach: we recompute two real partial products
    (Pₙ at the cap, P₄ₙ four times deeper) and require the residual to shrink toward v and the
    factors to be decaying to 1 — else RAISE rather than trust a regularized value. The log
    must use the principal branch and the factors must be near 1 (so Log is the continuous
    accumulation Lean's product converges to); a factor that is ≤0 real or far from 1 in the
    tail aborts (the log-sum would not faithfully track the literal product).

    ADDITIVE first pass: the step-halving Richardson extrapolant of the log partials
    (`_richardson_logprod`), which resolves the slowly-convergent (log f = O(1/k²)) DLMF Gamma
    products this single-`nsum` route stalls on. It returns ONLY on a certified stabilisation
    and RAISEs otherwise, falling through to the unchanged logic below — so it can only turn a
    prior skip into a decided verdict, never alter an existing one."""
    try:
        return _richardson_logprod(f, start)
    except Unparseable:
        pass
    def logf(n):
        v = f(n)
        if v == 0:
            raise Unparseable("product-zero-factor")
        return mp.log(v)
    # require the tail factors to be genuinely near 1 (so the principal-Log sum equals the
    # literal partial-product limit — no branch wrap-around across the accelerated tail).
    for n in (start + ncap - 1, start + 2 * ncap, start + 4 * ncap - 1):
        if abs(f(n) - 1) > mp.mpf("0.25"):
            raise Unparseable("product-not-converged")
    try:
        logtail = mp.nsum(logf, [start, mp.inf], method="e")
    except Exception:
        raise Unparseable("product-not-converged")
    if not mp.isfinite(logtail):
        raise Unparseable("product-not-converged")
    v = mp.e ** logtail
    p1 = partial                                    # ∏ over [start, start+ncap)
    try:
        p2 = p1
        for n in range(start + ncap, start + 4 * ncap):
            p2 *= f(n)
        tail_dev = abs(f(start + 4 * ncap - 1) - 1)
    except Exception:
        raise Unparseable("product-not-converged")
    r1, r2 = abs(v - p1), abs(v - p2)
    # converging: residual to the deeper partial is smaller (≤0.6×) AND the leading factor has
    # decayed toward 1. A divergent product fails the first (its partials move AWAY from v).
    if r2 <= mp.mpf("0.6") * r1 and tail_dev < mp.mpf("1e-3"):
        return v
    raise Unparseable("product-not-converged")


def _lattice_tsum(f, L, nshell=64, wdps=80):
    """`∑' l : L.lattice, f l` — a tsum over the FULL period lattice {m·ω₁ + n·ω₂ : m,n ∈ ℤ}
    (the Weierstrass/Eisenstein index set of DLMF 23.2.4/23.2.5 and 23.3.1/23.3.2).
    Aggregated in concentric square shells max(|m|,|n|) = k, each shell summed EXACTLY —
    so the odd-order tail parts cancel by the l ↔ −l pairing within a shell (exactly as in
    the bilateral ℤ-sum), leaving an even power-law tail S∞ − S_K ~ c/K² + d/K³ + … — then
    Richardson-extrapolated over the shell index at guard precision (validated on the
    anchored g₂/g₃/℘/℘′ oracles: rel. err ≲ 1e-24 at nshell=64/wdps=80, vs ~1e-2 raw).
    The ORIGIN term f(0) is included: Lean's tsum ranges over the whole subtype, and its
    total-field junk values (1/0 = 0, 0⁻¹ = 0 — mirrored in evaluate's div/inv branches)
    make the l = 0 term exactly the finite value the Lean statement carries (e.g. the
    bare 1/z² of ℘'s series, and literal 0 for the Eisenstein l⁻⁴/l⁻⁶ sums).

    SOUNDNESS — the same residual gate as `_accelerated_nsum`: the extrapolated value must
    be the limit the GENUINE partial (shell) sums approach — the residual at the deepest
    partial ≤ 0.6× the half-depth one — else RAISE (honest point drop), never a
    half-converged or regularized value (a z ON the lattice makes the shells diverge and
    fails this gate)."""
    w1, w2 = L.w1, L.w2
    with mp.workdps(wdps):
        total = f(mp.mpc(0))
        S = []
        for k in range(1, nshell + 1):
            s = mp.mpc(0)
            for m in range(-k, k + 1):          # top and bottom edges n = ±k
                s += f(m * w1 + k * w2) + f(m * w1 - k * w2)
            for n in range(1 - k, k):           # left and right edges m = ±k (corners done)
                s += f(k * w1 + n * w2) + f(-k * w1 + n * w2)
            total += s
            S.append(total)
        v, _ = mp.richardson(S)
    r1, r2 = abs(v - S[nshell // 2 - 1]), abs(v - S[-1])
    if not (mp.isfinite(v) and r2 <= mp.mpf("0.6") * r1):
        raise Unparseable("lattice-series-not-converged")
    return v


_PRIME_CACHE = [2, 3, 5, 7, 11, 13]


def _first_primes(n):
    """The first n primes (deterministic incremental trial division against the cached
    primes — no sympy dependency; the cache always contains every prime up to its last
    entry, so trial division up to √c is complete). The 600-prime cap in
    `_bounded_prime_sum` keeps the largest candidate ≈ 4400, where this is trivially cheap."""
    while len(_PRIME_CACHE) < n:
        c = _PRIME_CACHE[-1] + 2
        while any(c % p == 0 for p in _PRIME_CACHE if p * p <= c):
            c += 2
        _PRIME_CACHE.append(c)
    return _PRIME_CACHE[:n]


_SIEVE_CACHE = {"limit": 0, "primes": []}


def _primes_upto(n):
    """All primes ≤ n via a cached Eratosthenes sieve (exact integers; the Mertens
    `Nat.primesLE ⌊x⌋₊` index sets, DLMF 27.11.8/27.11.10). The caller caps n."""
    n = int(n)
    if n < 2:
        return []
    if n > _SIEVE_CACHE["limit"]:
        lim = max(n, 1000)
        sieve = bytearray([1]) * (lim + 1)
        sieve[0] = sieve[1] = 0
        for i in range(2, int(lim ** 0.5) + 1):
            if sieve[i]:
                sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        _SIEVE_CACHE["limit"] = lim
        _SIEVE_CACHE["primes"] = [i for i in range(lim + 1) if sieve[i]]
    import bisect
    ps = _SIEVE_CACHE["primes"]
    return ps[:bisect.bisect_right(ps, n)]


def _bounded_prime_sum(f, maxterms=600, tol=mp.mpf("1e-25")):
    """Series over the PRIMES p = 2, 3, 5, … (a `∑' p : Nat.Primes, body` index type —
    e.g. the DLMF 25.2.11 logarithmic Euler product): the body is evaluated at successive
    numeric primes (the `↑p` coercion of the binder is just that number) and accumulated
    under the SAME settled-tail-window / hard-cap discipline as `_bounded_nsum`: every
    partial sum over the last 48-window must lie within tol of the current total, else
    RAISE (→ the sample point is dropped, never trusted with a half-converged value).
    NO extrapolation fallback: a prime-indexed summand is not smooth in the term index
    (prime gaps), so a Richardson/Euler–Maclaurin candidate would be meaningless — slow
    decay at small Re s is an honest per-point skip, exactly like the erratic-coefficient
    Dirichlet series (see the SAMPLES_C_RE1 note; the large-σ grid points settle).
    maxterms = 600 primes (p ≤ 4409) keeps an UNSETTLED point well under EVAL_BUDGET
    even with a nested inner ℕ-series per prime, so a slow small-σ point drops per-point
    instead of timing out the whole row."""
    total = mp.mpf(0)
    hist = []
    for i, p in enumerate(_first_primes(maxterms)):
        total += f(p)
        hist.append(total)
        if len(hist) > 48:
            hist.pop(0)
        scale = tol * max(mp.mpf(1), abs(total))
        if i > 48 and all(abs(total - h) < scale for h in hist):
            return total
    raise Unparseable("series-not-converged")


def _quad_ray(f, lo, tol=mp.mpf("1e-8")):
    """∫_lo^∞ f for rapidly/exponentially-decaying integrands (Laplace/Mellin transforms).
    mpmath's exp-sinh quadrature handles exponential decay over the infinite ray, but it
    SILENTLY truncates a divergent integrand and returns a huge value with a deceptively
    small *relative* error — so two explicit divergence guards run first, each RAISING (→
    the sample point is dropped, never trusted) when the integral does not exist:

      • tail (x→∞): the integrand must decay monotonically toward 0 — catches e^{−at}I₀(bt)
        with a<b (grows like e^{(b−a)t}), an out-of-domain Laplace point.
      • endpoint (x→lo⁺): (x−lo)·f(x) must →0 — else f ≳ 1/(x−lo) is non-integrable there,
        catching x^{k+α} with k+α ≤ −1 (an out-of-domain moment integral).

    Only then is the quadrature trusted, and its own error estimate gates residual settling."""
    far = [lo + d for d in (mp.mpf(40), mp.mpf(80), mp.mpf(160))]
    try:
        ftail = [abs(f(x)) for x in far]
    except (ValueError, ZeroDivisionError, OverflowError):
        raise Unparseable("infinite-integral-tail-undefined")
    if not (ftail[2] <= ftail[1] <= ftail[0]) or ftail[2] > mp.mpf("1e-4"):
        raise Unparseable("infinite-integral-nondecaying-tail")
    near = [lo + e for e in (mp.mpf("1e-2"), mp.mpf("1e-4"), mp.mpf("1e-6"))]
    try:
        wedge = [abs((x - lo) * f(x)) for x in near]
    except (ValueError, ZeroDivisionError, OverflowError):
        raise Unparseable("infinite-integral-endpoint-undefined")
    if not (wedge[2] <= wedge[1] <= wedge[0] + mp.mpf("1e-12")):
        raise Unparseable("infinite-integral-endpoint-singular")
    # DOUBLY-EXPONENTIALLY damped integrands on the right ray (exp(−z cosh t)·cosh(c t),
    # the DLMF 10.32.9 cosh integral rep for K_ν — besselK_half / besselK_recurrence):
    # mpmath's exp-sinh transform STALLS for minutes on the doubly-exponential decay
    # (measured >30 s per single quad → an honest eval-timeout skip of a TRUE identity),
    # while the integrand has already underflowed far inside the sampled window. When the
    # FIRST far-tail sample (at lo+40, already computed as `ftail[0]` above) certifies total
    # underflow (≤ 1e-35 — dozens of orders below every gate in play) and the tail is
    # monotone-decreasing past it (the `ftail` guard above), the omitted [lo+40, ∞) tail is
    # below any representable contribution at working precision, so integrate the truncated
    # [lo, lo+40] instead (measured ~0.03 s, reproduces DLMF 10.39.2 K_{1/2} to ~1e-30 and
    # DLMF 10.29.1 K_{ν−1}−K_{ν+1}=−(2ν/z)K_ν to ~1e-25). This mirrors the doubly-INFINITE
    # branch's identical certified-underflow truncation (exp(−M cosh x),
    # coshExp_integral_eq_two_besselK0). Compute-budget change scoped to this
    # certified-underflow shape; the error gate, tolerance and every non-underflowing ray
    # (Laplace/Mellin transforms, whose ftail[0] ≫ 1e-35) are unchanged.
    if ftail[0] <= mp.mpf("1e-35"):
        val, err = mp.quad(f, [lo, lo + 40], error=True)
    else:
        val, err = mp.quad(f, [lo, mp.inf], error=True)
    if err > tol * max(mp.mpf(1), abs(val)):
        raise Unparseable("infinite-integral-not-converged")
    return val


def _quad_ray_slow(f, lo, tol=mp.mpf("1e-9")):
    """∫_lo^∞ f for a MONOTONE-DECREASING but SLOW (algebraic/power-law) tail that `_quad_ray`
    rejects as `nondecaying-tail` — its |f(lo+160)| > 1e-4 fast-decay gate — even though the
    integral converges. This is the analytic-continuation Γ rep (DLMF 5.9.5, tail ~ t^{x+n−1}
    with −2 < x+n−1 < −1) and the Olver-𝐅 Mellin transform (DLMF 15.14.1, tail ~ x^{Re s−1−
    min(Re a,Re b)} < x^{−1}); both are genuinely improper-convergent power-law tails.

    SOUNDNESS — an error-estimate gate ALONE is NOT enough here: mpmath's exp-sinh silently
    truncates a monotone DIVERGENT monomial (∫ t^{−0.5}: measured value 2.8e17 with a spuriously
    tiny reported rel-error 3.6e-18) and would be falsely certified. So the integrability of the
    tail is established FIRST, independently, by estimating the power-law exponent p from two
    well-separated far samples and REQUIRING p < −1 with a margin (an integrable algebraic tail;
    the divergent controls t^{−0.5}/t^{−0.9}/1/t measure p ∈ {−0.5,−0.9,−1.0}, all rejected).
    Only then is mp.quad trusted, and only when its OWN relative error estimate also certifies
    convergence below `tol`. A tail that is non-monotone, has an estimated exponent ≥ −1, or whose
    quadrature error is not certified RAISES → the sample drops, never a fabricated value. Purely
    additive: fires only where `_quad_ray` already raised `nondecaying-tail`; nothing loosened."""
    xs = [lo + mp.mpf(40), lo + mp.mpf(160), lo + mp.mpf(640)]
    try:
        ft = [abs(f(x)) for x in xs]
    except (ValueError, ZeroDivisionError, OverflowError):
        raise Unparseable("infinite-integral-tail-undefined")
    if not (ft[2] <= ft[1] <= ft[0]) or ft[2] == 0 or ft[1] == 0 or ft[0] == 0:
        raise Unparseable("infinite-integral-nondecaying-tail")
    # power-law exponent from each consecutive far pair; both must certify an INTEGRABLE tail
    # (p < −1 with a 0.02 margin so the log-divergent boundary p = −1, i.e. 1/t, is excluded).
    p1 = mp.log(ft[1] / ft[0]) / mp.log(xs[1] / xs[0])
    p2 = mp.log(ft[2] / ft[1]) / mp.log(xs[2] / xs[1])
    if not (p1 < mp.mpf("-1.02") and p2 < mp.mpf("-1.02")):
        raise Unparseable("infinite-integral-nondecaying-tail")
    # endpoint guard (x → lo⁺), identical to `_quad_ray`: (x−lo)·f(x) must → 0.
    near = [lo + e for e in (mp.mpf("1e-2"), mp.mpf("1e-4"), mp.mpf("1e-6"))]
    try:
        wedge = [abs((x - lo) * f(x)) for x in near]
    except (ValueError, ZeroDivisionError, OverflowError):
        raise Unparseable("infinite-integral-endpoint-undefined")
    if not (wedge[2] <= wedge[1] <= wedge[0] + mp.mpf("1e-12")):
        raise Unparseable("infinite-integral-endpoint-singular")
    try:
        val, err = mp.quad(f, [lo, mp.inf], error=True)
    except Exception:
        raise Unparseable("infinite-integral-not-converged")
    if not (mp.isfinite(val) and mp.isfinite(err)
            and err <= tol * max(mp.mpf(1), abs(val))):
        raise Unparseable("infinite-integral-not-converged")
    return val


def _quad_ray_theta_sqrt(f, lo, tol=mp.mpf("1e-8")):
    """Evaluate a theta-function ray integral after ``t = lo + u²``.

    The theta heat kernels in DLMF 20.10.4/5 have an integrable ``t⁻¹ᐟ²``
    boundary profile at ``t = 0``.  Sending that profile directly through
    exp-sinh quadrature makes the oracle spend its whole per-sample budget at
    the endpoint.  The square-root substitution removes the profile:

        ∫ₗₒ^∞ f(t) dt = ∫₀^∞ 2u f(lo + u²) du.

    The value assigned at ``u = 0`` is measure-zero and avoids asking the theta
    oracle to evaluate the undefined lattice parameter ``τ = 0``.  Soundness is
    still provided by `_quad_ray`'s endpoint, tail, and quadrature-error gates;
    this changes coordinates, not the tolerance or the claimed value.
    """
    def g(u):
        if u == 0:
            return mp.mpc(0)
        return 2 * u * f(lo + u * u)
    return _quad_ray(g, mp.mpf(0), tol)


_TRIG_HEADS = {"Real.cos": "cos", "cos": "cos", "Complex.cos": "cos",
               "Real.sin": "sin", "sin": "sin", "Complex.sin": "sin"}


def _osc_phase(body, var, env):
    """Locate a `cos(g(t))` / `sin(g(t))` factor whose phase `g` depends on the integration
    variable `var`, anywhere in the integrand AST `body`. Return `(kind, phase)` where
    `kind ∈ {"cos","sin"}` and `phase(t) = g(t)` (a real callable), or None if no oscillatory
    trig factor is present. Only the FIRST such factor found drives the zero structure — for the
    §5.9.6–9 ray integrals there is exactly one (`cos t`, `sin t`, `cos(tⁿ)`, `sin(tⁿ)`)."""
    if not isinstance(body, tuple):
        return None
    if body[0] == "app" and body[1][0] == "var" and body[1][1] in _TRIG_HEADS and len(body[2]) == 1:
        arg = body[2][0]
        phase = lambda t: evaluate(arg, {**env, var: t})
        try:                                # the phase must genuinely vary with t (oscillatory),
            a = phase(mp.mpf("0.7")); b = phase(mp.mpf("3.1"))   # not a t-independent constant
        except Exception:
            a = b = None
        if a is not None and abs(b - a) > mp.mpf("1e-9"):
            return (_TRIG_HEADS[body[1][1]], phase)
    for c in body[1:]:
        r = _osc_phase(c, var, env)
        if r is not None:
            return r
    return None


def _osc_zeros_fn(kind, phase, lo):
    """Build the `zeros=` callback `mp.quadosc` needs: `zeros(k)` = the k-th zero of the
    oscillatory factor at/after `lo`. Zeros of `cos(g)` solve `g(t)=(k+½)π`; of `sin(g)`,
    `g(t)=kπ`. We require the phase `g` to be increasing (verified by the caller's tail guard
    + a local monotonicity check) and invert it by BISECTION — derivative-free and robust for
    both the period-2π cases (g(t)=t) and the chirps (g(t)=tⁿ, frequency growing). Returns None
    if the phase is not monotone increasing on the ray (then quadosc is not attempted)."""
    base = phase(lo)
    # the first relevant phase level STRICTLY above g(lo) — so every returned zero lies in the
    # open ray (lo, ∞); a level coinciding with g(lo) (e.g. sin's level 0 when g(lo)=0) is skipped.
    off = mp.mpf("0.5") if kind == "cos" else mp.mpf(0)
    m0 = mp.ceil(base / mp.pi - off)
    level = lambda k: (m0 + k + off) * mp.pi
    if level(0) <= base + mp.mpf("1e-12") * max(mp.mpf(1), abs(base)):
        m0 += 1
    # confirm g is increasing (a few probes); a non-monotone phase has no clean zero ladder.
    probes = [lo + d for d in (mp.mpf("0.5"), mp.mpf("2"), mp.mpf("8"), mp.mpf("32"))]
    pv = [phase(p) for p in probes]
    if not all(pv[i] < pv[i + 1] for i in range(len(pv) - 1)) or not (base <= pv[0]):
        return None

    def zero(k):
        target = level(k)
        a = lo
        # expand b until g(b) ≥ target
        b = max(lo + mp.mpf(1), lo)
        for _ in range(200):
            if phase(b) >= target:
                break
            b *= 2
        else:
            raise Unparseable("infinite-integral-oscillatory")
        for _ in range(200):                # bisection: g increasing ⇒ unique root
            m = (a + b) / 2
            if phase(m) < target:
                a = m
            else:
                b = m
            if b - a < mp.mpf("1e-25") * max(mp.mpf(1), abs(b)):
                break
        return (a + b) / 2
    return zero


def _quad_ray_osc(f, lo, body, var, env, tol=mp.mpf("1e-6")):
    """Evaluate a non-decaying / slowly-decaying OSCILLATORY ray integral ∫_lo^∞ f — the
    convergent (improper Riemann) value of an integrand whose amplitude does not decay fast enough
    for tanh-sinh but whose oscillation makes the integral converge. Covers the §5.9.6–9
    Cauchy–Saalschütz / Fresnel representations: ∫₀^∞ t^{x−1}cos t, …sin t, ∫₀^∞ cos(tⁿ), sin(tⁿ).

    METHOD. The zeros zₖ of the oscillatory factor partition (z₀,∞) into half-periods over which f
    has constant sign; the signed areas `aₖ = ∫_{zₖ}^{z_{k+1}} f` form a (rapidly settling)
    alternating series whose accelerated sum is the tail. The head [lo,z₀] is quadrated separately.

    SOUNDNESS — three independent gates, any of which DROPS the sample (raise), never a
    trusted-but-wrong value:
      (1) ENDPOINT head. The t→0 endpoint may carry an integrable singularity (t^{x−1}, x<1). Near
          the convergence boundary x→0⁺ tanh-sinh under-resolves it; the head is quadrated with
          `error=True` and REJECTED on its own error estimate (verified to track the true head
          error — ~1e-2 at x=0.05, ~1e-7 at x=0.2 — so x≲0.15 is dropped, not mis-PASSed).
      (2) DIRICHLET/LEIBNIZ shape. The half-period areas must ALTERNATE in sign with a
          non-increasing magnitude envelope — the condition under which the alternating tail
          series converges. (Magnitudes need NOT reach 0 within the window: a slowly-decaying
          envelope like t^{x−1} keeps them O(0.2), yet the alternation still converges.) A
          non-alternating or magnitude-growing tail is a divergent oscillation → DROP.
      (3) ACCELERATOR AGREEMENT. The tail is summed by TWO independent accelerators — van
          Wijngaarden repeated averaging and the Shanks (iterated Aitken) transform — applied to
          the same partial sums. They share no extrapolation machinery, so agreement to `tol` is
          strong evidence of the true alternating-series limit; disagreement DROPS the sample."""
    osc = _osc_phase(body, var, env)
    if osc is None:
        raise Unparseable("infinite-integral-nondecaying-tail")
    kind, phase = osc
    zeros = _osc_zeros_fn(kind, phase, lo)
    if zeros is None:
        raise Unparseable("infinite-integral-nondecaying-tail")
    z0 = zeros(0)
    try:
        head, head_err = mp.quad(f, [lo, z0], error=True)
    except Exception:
        raise Unparseable("infinite-integral-oscillatory")
    # (1) reject an under-resolved endpoint singularity (x→0⁺ boundary) on its OWN error.
    if head_err > tol * max(mp.mpf(1), abs(head)):
        raise Unparseable("infinite-integral-oscillatory")
    try:
        areas = [mp.quad(f, [zeros(k), zeros(k + 1)]) for k in range(28)]
    except Exception:
        raise Unparseable("infinite-integral-oscillatory")
    # (2) Dirichlet/Leibniz: areas must alternate in sign with a non-increasing magnitude
    # envelope (the convergence condition for the alternating tail). A growing or non-alternating
    # tail is a divergent oscillation. A small relative slack absorbs quadrature roundoff.
    tail = areas[-10:]
    mags = [abs(a) for a in tail]
    if any(a == 0 for a in tail):
        raise Unparseable("infinite-integral-oscillatory")
    if not all((tail[i] < 0) != (tail[i + 1] < 0) for i in range(len(tail) - 1)):
        raise Unparseable("infinite-integral-oscillatory")          # not alternating
    if not all(mags[i + 1] <= mags[i] * (1 + mp.mpf("1e-6")) for i in range(len(mags) - 1)):
        raise Unparseable("infinite-integral-oscillatory")          # magnitude not decreasing
    partials, acc = [], mp.mpf(0)
    for a in areas:
        acc += a
        partials.append(acc)
    s = list(partials)                     # van Wijngaarden: repeated partial-sum averaging
    while len(s) > 1:
        s = [(s[i] + s[i + 1]) / 2 for i in range(len(s) - 1)]
    val = head + s[0]
    try:                                   # independent accelerator: Shanks / iterated Aitken
        check = head + mp.shanks(partials)[-1][-1]
    except Exception:
        raise Unparseable("infinite-integral-oscillatory")
    # (3) the two accelerators must agree (and the second must be a finite real estimate).
    if not mp.isfinite(check) or abs(val - check) > tol * max(mp.mpf(1), abs(val)):
        raise Unparseable("infinite-integral-oscillatory")
    return val


def _quad_finite_osc(f, lo, hi, body, var, env, tol=mp.mpf("1e-6")):
    """∫_lo^hi f for a FINITE but wide interval whose integrand carries an oscillatory
    cos(g(t))/sin(g(t)) factor (DLMF 5.9.6–9's `Tendsto (fun R => ∫ t in 0..R, …) atTop …`
    improper-integral limit forms, sampled at increasing finite endpoints R). A single
    tanh-sinh `mp.quad(f, [lo, hi])` call is UNSOUND here: over many oscillation periods
    tanh-sinh's node placement is not phase-aligned, and for hi in the thousands the
    quadrature can silently return a value with large absolute error while reporting a
    deceptively small *relative* error estimate (verified empirically: hi=1000 on
    t^{x-1}cos t at x=1/2 gives a naive value ~0.94 away from the true integral, while
    panel-exact splitting at the oscillation's zeros gives ~0.026 — consistent with the
    genuinely-decaying oscillatory-tail envelope). Splitting at the zeros of the
    oscillatory factor makes each panel a definite-sign hump that tanh-sinh integrates
    accurately, and the finite panel sum is EXACT (no extrapolation, unlike the infinite-tail
    `_quad_ray_osc`) — so soundness reduces to each panel's own quadrature error estimate.

    Returns None (never raises) when no oscillatory factor is found, the phase isn't a clean
    increasing ladder from `lo`, or the zero count up to `hi` is too large to enumerate cheaply
    (a rapidly-chirping phase like tⁿ over a wide range — see the MAXPANELS guard below) —
    callers must fall back to plain `mp.quad` in that case; this function only ever KICKS IN
    for the moderate-period-count oscillatory shape it is built for (§5.9.6/5.9.7's period-2π
    cos t/sin t; §5.9.8/5.9.9's cos(tⁿ)/sin(tⁿ) chirp is left to the plain path when its zero
    count over [lo,hi] exceeds MAXPANELS, rather than risk a multi-minute bisection-per-zero
    enumeration — a capacity limit, never a soundness compromise: declining here is always a
    safe no-op, the row simply keeps whatever verdict the pre-existing path already gave it."""
    osc = _osc_phase(body, var, env)
    if osc is None:
        return None
    kind, phase = osc
    zeros = _osc_zeros_fn(kind, phase, lo)
    if zeros is None:
        return None
    MAXPANELS = 4000
    try:
        z0 = zeros(0)
    except Exception:
        return None
    if z0 >= hi:
        return None                            # too few oscillations before hi: not our regime
    # Cheap panel-COUNT estimate before committing to enumeration: binary-search (in k, not in
    # t) for the least k with zeros(k) >= hi. `zeros` is O(bisection) per call, so this costs
    # O(log MAXPANELS) zero-evaluations, not O(MAXPANELS) — safe to run before the real work.
    lo_k, hi_k = 0, 1
    try:
        while zeros(hi_k) < hi and hi_k <= MAXPANELS:
            lo_k = hi_k
            hi_k *= 2
    except Exception:
        return None
    if hi_k > MAXPANELS:
        return None                            # too many oscillation periods — decline, fall back
    nodes = [lo, z0]
    try:
        k = 0
        while True:
            zk1 = zeros(k + 1)
            if zk1 >= hi:
                break
            nodes.append(zk1)
            k += 1
    except Exception:
        return None
    nodes.append(hi)
    try:
        val, err = mp.quad(f, nodes, error=True)
    except Exception:
        return None
    if err > tol * max(mp.mpf(1), abs(val)):
        return None                            # own error estimate too large — don't trust it
    return val


def _quad_ray_smooth(f, lo, tol=mp.mpf("1e-6")):
    """Re-attempt a NON-oscillatory, exponentially-decaying ray integral ∫_lo^∞ f that tanh-sinh
    rejected as "not-converged" because of a REMOVABLE singularity at the endpoint — the integrand
    is analytically finite at lo (a 0/0 form) but a naive float evaluation there suffers
    catastrophic cancellation (e.g. Binet's `(1/(e^t−1) − 1/t + ½)/t`, whose two ~1/t terms cancel
    to ~t/12 near 0). Each sample at depth `t` is evaluated with `≈2·|log₁₀ t|` GUARD digits, so the
    cancellation is absorbed before rounding back. The split [lo,lo+1]+[lo+1,∞) keeps the singular
    head and the exponential tail on separate panels; convergence is gated by mpmath's OWN error
    estimate on each panel (same soundness contract as `_quad_ray` — a panel whose error exceeds
    `tol` RAISES, dropping the sample, never a trusted-but-wrong value)."""
    base = max(mp.mp.dps, 60)

    def fsafe(t):
        t = mp.mpf(t)
        if t == lo:
            return mp.mpc(0)                # endpoint: measure-zero, value irrelevant to the quad
        extra = int(2 * max(mp.mpf(0), -mp.log10(abs(t - lo)))) + 20
        with mp.workdps(base + extra):
            # Mellin/Laplace rows may be genuinely complex-valued.  Coercing
            # through mpf dropped such samples precisely in the critical strip.
            return mp.mpmathify(f(t))

    with mp.workdps(base):
        h, eh = mp.quad(fsafe, [lo, lo + 1], error=True)
        tl, et = mp.quad(fsafe, [lo + 1, mp.inf], error=True)
    val = h + tl
    if max(eh, et) > tol * max(mp.mpf(1), abs(val)):
        raise Unparseable("infinite-integral-not-converged")
    return val


class _SeriesStall(Exception):
    pass


def _series_alarm(signum, frame):
    raise _SeriesStall("nsum wall-clock guard")
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import oracle_bindings as ob

mp.mp.dps = 30
ROOT = pathlib.Path(__file__).resolve().parents[2] / "FLMF" / "Chapter7"
TOL = mp.mpf("1e-18")
# Pole-degeneracy magnitude cap for the equality sampler: at dps=30, an operand magnitude
# beyond ~1e25 on the standard O(1) sample grids signals a QUOTIENT EVALUATED AT A POLE
# (e.g. the Jacobi/Glaisher quotients cs/ds/nc/sc on the degenerate z = τ diagonal of the
# C×H grid, where sn(z,τ) is the dps-30 roundoff of an exact 0 and |cn/sn| ≈ 1.5e31 is pure
# cancellation noise). Such a sample carries no correct digits of the function, so it is
# DROPPED (counted unsampled, like the other soundness gates), never gated — see sweep_eq.
POLE_MAG = mp.mpf("1e25")
UNABLE = "unable to proceed"   # the verdict for a declaration the sweep could not numerically check
IND = "\U0001D44B"          # 𝑋 — synthetic name for the polynomial indeterminate


# ── FLMF namespace stripping for registry lookup ──────────────────────────────
# Statements often fully-qualify a function (`FLMF.Error.erf`, `FLMF.Fresnel.fresnelC`,
# `FLMF.Functions.Hermite.physHermite`) while the registry binds the SHORT leaf name
# (`erf`, …). We resolve by trying the exact name, then progressively dropping a
# *known* leading project-namespace segment — never an arbitrary one, so we cannot
# alias a genuinely different function onto a same-leaf name from outside FLMF.
_FLMF_NS_SEGS = {
    "FLMF", "Error", "Fresnel", "Voigt", "Hypergeometric", "ParabolicCylinder",
    "GoodwinStaton", "Functions", "Hermite", "Def",
    # `FLMF.JacobiElliptic.completeK` (theta_20_9_2, DLMF 20.9.2) — completeK itself is
    # registered bare; the namespace segment was missing so the head never resolved.
    "JacobiElliptic",
    # `FLMF.ExpIntegrals.Def.li` (expint_6_16_5, DLMF 6.16.5) — li is registered bare.
    "ExpIntegrals",
}


# (namespace-segment, leaf) pairs that must NEVER resolve by stripping: the FLMF function
# in that namespace is a DIFFERENT function from the bare registry key of the same leaf.
# `FLMF.JacobiElliptic.complementaryModulus (k : ℝ) = √(1−k²)` (JacobiSpecialValues.lean)
# vs the registered Theta-namespace τ-form `complementaryModulus τ = θ₄²/θ₃²` — aliasing
# them would evaluate the wrong function. Stays unresolved → honest `unbound:` skip
# (a registry binding under the qualified name is the correct fix).
_NS_STRIP_BLOCK = {("JacobiElliptic", "complementaryModulus")}

# The enclosing namespace of the decl currently being checked (e.g. "FLMF.JacobiElliptic"),
# set per-decl at the top of `classify_and_check` and reset for every decl (never stale).
# Used ONLY to qualify a BARE head whose (namespace-segment, leaf) pair is a `_NS_STRIP_BLOCK`
# collision: such a head, written bare inside its declaring namespace, must resolve to the
# QUALIFIED registry key, not the bare same-leaf key that names a DIFFERENT function.
_CUR_NS = ""


def _reg_resolve(name):
    """Canonical REGISTRY key for `name`, or None. Tries the exact name first, then
    strips KNOWN leading FLMF namespace segments one at a time (e.g.
    `FLMF.Error.erf` → `Error.erf` → `erf`). Only segments in `_FLMF_NS_SEGS` are
    stripped; an unknown leading segment stops the descent (stay unresolved → skip)."""
    if name in ob.REGISTRY:
        # A BARE head that also collides with a blocked (namespace, leaf) pair must, when the
        # declaring namespace supplies that segment, resolve to the QUALIFIED registry key —
        # NOT the bare same-leaf key, which names a different function (jacobiDn_completeK:
        # bare `complementaryModulus` in `namespace FLMF.JacobiElliptic` is the real √(1−k²)
        # form registered under the qualified key, not the bare Theta τ-form θ₄²/θ₃²). Qualify
        # with the current decl's namespace first; fall through to the bare key when no
        # qualified key exists. Gated on `_NS_STRIP_BLOCK`, so no other bare head is re-routed.
        if "." not in name and _CUR_NS:
            segs = _CUR_NS.split(".")
            if any((seg, name) in _NS_STRIP_BLOCK for seg in segs):
                for i in range(len(segs)):
                    cand = ".".join(segs[i:] + [name])
                    if cand in ob.REGISTRY:
                        return cand
        return name
    if "." not in name:
        return None
    parts = name.split(".")
    if any((seg, parts[-1]) in _NS_STRIP_BLOCK for seg in parts[:-1]):
        return None
    # peel known project segments off the front; the remaining tail must hit the registry
    while len(parts) > 1 and parts[0] in _FLMF_NS_SEGS:
        parts = parts[1:]
        cand = ".".join(parts)
        if cand in ob.REGISTRY:
            # COLLISION GUARD: a stripped leaf must be a scalar special-fn / const / power
            # series — never an orthogonal-polynomial family (`poly`/`lpoly`, indeterminate-
            # bound). Otherwise `FLMF.ParabolicCylinder.U` would alias the Chebyshev `U`
            # (`_chebyu`) and produce a WRONG number. Such a leaf stays unresolved (skip).
            if ob.REGISTRY[cand][0] in ("poly", "lpoly"):
                return None
            return cand
    return None


def _reg_get(name):
    """`(kind, fn)` for `name` after FLMF-namespace resolution, or None."""
    k = _reg_resolve(name)
    return ob.REGISTRY[k] if k is not None else None


def _is_ns_resolved(name):
    """True iff `name` binds to the registry ONLY after stripping a known FLMF namespace
    prefix (i.e. the exact name is NOT a registry key, but a stripped form is). Such a
    resolution is correct as a *name* match, but the underlying FLMF Lean convention vs the
    registry's mpmath convention (and the statement's intended domain) is not independently
    verified here — so a FAIL on a conclusion that uses one is treated as an UNVERIFIED skip
    rather than asserted, per the soundness-over-coverage gate (a possibly-spurious FAIL is
    worse than a skip). Exact-bound names keep full refutation authority."""
    return name not in ob.REGISTRY and _reg_resolve(name) is not None


def _concl_uses_ns_resolved(node):
    """True if any atom anywhere in the conclusion AST is a namespace-only-resolved name."""
    if isinstance(node, tuple):
        if node[0] == "var" and isinstance(node[1], str) and _is_ns_resolved(node[1]):
            return True
        return any(_concl_uses_ns_resolved(c) for c in node[1:])
    if isinstance(node, list):
        return any(_concl_uses_ns_resolved(c) for c in node)
    return False


def _has_biinf_integral(node):
    """True if the AST contains a doubly-infinite integral `∫_{−∞}^{∞}`. Such a contour
    integral (Mellin–Barnes vertical line, the §7.7 complex Fresnel auxiliaries) is valid only
    in a z-SECTOR the Tier-1 hypotheses do not encode, so sampling z over the full ℂ grid steps
    outside the representation's domain. We use this only to DOWNGRADE a FAIL to an honest skip
    (never to fabricate a PASS) — a sound contour identity must not be refuted off-sector."""
    if isinstance(node, tuple):
        if node[0] == "integral" and node[2] == ("neginf",) and node[3] == ("inf",):
            return True
        return any(_has_biinf_integral(c) for c in node[1:])
    if isinstance(node, list):
        return any(_has_biinf_integral(c) for c in node)
    return False


# ════════════════════════ 1. EXTRACT tagged declarations ════════════════════
# The name class includes subscript digits ₀-₉ (legal Lean identifier characters): without
# them a trailing subscript is silently stripped, so sibling theorems like
# wigner6j_eq_zero_of_triangle₁..₄ all extract under ONE name and clobber each other in the
# by-name prior-PASS cache / downstream by-name tooling. Four theorems ⇒ four distinct rows.
# Name class includes Greek letters (α-ω, Α-Ω) and subscript letters (ₐ-ₜ): Lean decl
# names like θ₃_add_tau_left or Eₙ_asymptotic are legal and DO occur — the old
# [A-Za-z0-9_'₀-₉] class silently truncated them (hasDerivAt_θ₃_fst extracted as the
# bogus row `hasDerivAt_`) or skipped them entirely, leaving tagged theorems unsweepable.
# Dots are included for qualified declaration names (`theorem _root_.Foo.bar`): without
# them the ChristoffelDarbouxBridge lemma extracted as the bogus row `_root_`.
DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_\'₀-₉α-ωΑ-Ωₐ-ₜ.]+)', re.M)
# A DLMF citation may spell the entry with a section sign — `DLMF §7.12.1` — or (docstring
# rewording, e.g. erfc_watson_series) cite `§7.12.1` bare, without the literal word `DLMF`
# in front. Both forms are accepted; the captured tag is identical, so previously-extracted
# rows are unchanged (ADDITIVE: the old `DLMF 7.12.1` spelling still matches). A DLMF *table*
# citation — `DLMF Table 22.5.1` (nc_zero/nd_zero's "standard non-vanishing hypotheses on
# the theta-nulls (DLMF Table 22.5.1)") — inserts the literal word `Table` between `DLMF`
# and the number; without it these decls' docstrings had NO TAG_RE match at all (tags = []),
# silently dropping tagged theorems from extraction. Additive: the bare `DLMF x.y.z` and
# `§x.y.z` spellings match exactly as before.
TAG_RE = re.compile(r'(?:DLMF\s+(?:Table\s+)?§?\s*|§)([0-9]+\.[0-9]+(?:\.[0-9]+)?)')


def _section_binders(text):
    """Lean `variable (u k : ℝ)` / `variable {z τ : ℂ}` SECTION declarations bind names that a
    theorem in that section uses WITHOUT re-listing them in its own binders (e.g.
    `deriv_jacobiSn`'s `u`,`k`; `theta_mul_sn`'s `z`,`τ`). Return {name -> base} for SAMPLEABLE
    scalar types only. SOUNDNESS: instance binders (`[CommRing R]`), `Type*`, structures
    (`PeriodPair`, `Measure ℝ`) are skipped — such a name stays unbound (honest skip), never
    sampled as a fresh real.

    An abstract scalar type variable `𝕂 : Type*` under `[RCLike 𝕂]` (e.g.
    `variable {𝕂 : Type*} [RCLike 𝕂] (a b : 𝕂)`, the Kummer-contiguous-relation
    pattern of DLMF 13.3.1–3 in KummerContiguous.lean, also GaussODE/KummerODE/
    KummerTransform/Appell/AppellF2/GaussValues) is mathematically forced to be
    ℝ or ℂ up to isomorphism — RCLike's own defining property — so it is exactly
    as sampleable as a literal `ℂ` binder; treat it as base `'C'`. A bare
    `[Field 𝕂] [CharZero 𝕂]` WITHOUT `RCLike` (e.g. KummerContiguous's own
    `Coefficients` section) stays unresolved: an abstract characteristic-zero
    field need not be ℝ/ℂ (could be ℚ, a number field, …), so sampling it as a
    concrete complex number would be unsound — such names keep the honest
    unbound skip."""
    out = {}
    base_of = {"ℝ": "R", "ℂ": "C", "ℕ": "N", "ℤ": "Z", "ℍ": "H", "UpperHalfPlane": "H"}
    # collect every type-variable name declared `[RCLike 𝕂]` (or `[RCLike 𝕜]`, …) ANYWHERE
    # in the file — `variable` sections accumulate across the file and a later section may
    # declare `(a b : 𝕂)` for a `𝕂` whose `[RCLike 𝕂]` instance was introduced earlier.
    rclike_tyvars = set(re.findall(r'\[RCLike\s+([A-Za-zα-ω𝕂𝕜]\w*)\]', text))
    for m in re.finditer(r'^\s*variable\b(.*)$', text, re.M):
        for grp in re.finditer(r'[({]([^:(){}\[\]]+?)\s*:\s*([^(){}\[\]]+?)[)}]', m.group(1)):
            typ = grp.group(2).strip()
            base = base_of.get(typ)
            if base is None and typ in rclike_tyvars:
                base = "C"                       # RCLike-instanced scalar type ≅ ℝ or ℂ
            if base is None:
                continue                         # not a sampleable scalar → leave unbound
            for nm in grp.group(1).split():
                out.setdefault(nm, base)         # first declaration of a name wins


    return out


def _section_finvecs(text, cinst):
    """File-level `variable (A B : Fin p → 𝕂)` Fin-indexed vector declarations (PFQ.lean's
    ₚFᵩ parameter tuples: `variable (A : Fin p → 𝕂) (B : Fin q → 𝕂)`). `_section_binders`
    drops FUNCTION-typed section vars, so `A`/`B` stayed `unbound` (`pFqCoefficient_succ_div`,
    `pFq_hasSum`). Tag them exactly like a THEOREM-HEAD `(A B : Fin q → ℂ)` finvec binder —
    base 'finvecC', cardinality dim recorded — so the sweep samples the dim as ℕ and builds
    A/B as `.q`-tagged callables (see sweep_eq's finvec resolution and `_veclist`).

    Returns {vec-name -> dim-name}. Scalar restricted to `ℂ` or a ℂ-instantiable tyvar
    (`cinst`, e.g. the RCLike/Field `𝕂` — sampling as complex is the sound ℂ-specialization):
    a `Fin p → ℝ` REAL vector is never captured (would be sampled at complex points)."""
    scalars = {'ℂ'} | set(cinst)
    out = {}
    for m in re.finditer(r'^\s*variable\b(.*)$', text, re.M):
        for g in re.finditer(r'[({]\s*([A-Za-zα-ω][\w\s\'′]*?)\s*:\s*Fin\s+'
                             r'([A-Za-zα-ω]\w*)\s*→\s*([A-Za-zα-ω𝕂𝕜𝔸ℂℝℚ]\w*)\s*[)}]',
                             m.group(1)):
            if g.group(3) in scalars:
                for nm in g.group(1).split():
                    out[nm] = g.group(2)
    return out


# ── ℂ-instantiation of scalar-polymorphic statements (𝕂 / 𝔸 / 𝕜 tyvars) ──────
# Instance classes ℂ itself satisfies — the single-subject form `[C X]`, plus the
# two-argument scalar-action forms `[C Y X]`/`[C X Y]` with every scalar type
# variable read at ℂ (`Algebra ℂ ℂ`, `NormedAlgebra ℂ ℂ`, … all hold). A type
# variable ALL of whose instance brackets fall inside this list may be soundly
# INSTANTIATED at ℂ for the numeric spot-check: instantiating a ∀-quantified type
# variable at an instance satisfying every stated hypothesis class is a logically
# valid specialization, so a numeric counterexample at ℂ genuinely refutes the
# polymorphic statement (a PASS is, as everywhere in Tier 1, evidence at the
# sampled instance only). A tyvar carrying ANY bracket outside this list (an
# order, finiteness, positive-characteristic, … hypothesis ℂ might not satisfy)
# is NEVER instantiated — such rows keep the honest `unparsed:char` skip.
# Candidates are restricted to Mathlib's double-struck scalar-type names (𝕂 𝕜 𝔸 𝔹 𝔽)
# so a Greek/Latin `{α : Type*}` can never collide with a same-named VALUE binder
# elsewhere in the file. ADDITIVE: rows without these characters are untouched
# (they previously hard-failed tokenize as `unparsed:char '𝕂'`).
_CINST_CLASSES1 = {
    "RCLike", "Field", "CharZero", "NontriviallyNormedField", "NormedField",
    "DivisionRing", "NormedDivisionRing", "Ring", "CommRing", "NormedRing",
    "TopologicalSpace", "IsTopologicalRing", "CompleteSpace", "NormedAddCommGroup",
}
_CINST_CLASSES2 = {"Algebra", "NormedAlgebra", "Module", "NormedSpace"}
_CINST_LEAD = "𝕂𝕜𝔸𝔹𝔽"


def _cinst_tyvars(text):
    """Names declared `X : Type*` (double-struck lead char only) whose every instance
    bracket in `text` is a ℂ-satisfied class — the set that may be read at ℂ."""
    cands = set()
    for m in re.finditer(r'[({]\s*([^:(){}]+?)\s*:\s*Type\s*\*?\s*[)}]', text):
        cands |= {nm for nm in m.group(1).split() if nm and nm[0] in _CINST_LEAD}
    out = set()
    allnames = cands | {"ℝ", "ℂ"}
    for x in cands:
        pat = re.compile(r'(?<![\w\'′₀-₉ℓ])' + re.escape(x) + r'(?![\w\'′₀-₉ℓ])')
        saw = True
        ok = None
        for br in re.findall(r'\[([^\[\]]+)\]', text):
            if not pat.search(br):
                continue
            toks = br.split()
            if len(toks) == 2 and toks[0] in _CINST_CLASSES1 and toks[1] == x:
                ok = True                        # a real, ℂ-satisfied instance constraint
                continue
            if len(toks) == 3 and toks[0] in _CINST_CLASSES2 and \
                    {toks[1], toks[2]} <= allnames and x in (toks[1], toks[2]):
                continue
            # instance binders always head with an UNDOTTED UpperCamelCase class name;
            # a lowercase- or dotted-headed bracket is a PROOF-BODY tactic list
            # (`rw [lemma_name 𝕂 …]`, `simp only [RCLike.foo]`) — not a hypothesis on
            # the tyvar, so it must not disqualify. Any instance-shaped bracket that
            # is NOT whitelisted (e.g. `[Fintype 𝕂]`, `[LinearOrder 𝕂]`) disqualifies.
            if re.match(r'[A-Z][A-Za-z0-9]*(\s|$)', br.strip()):
                saw = False
                break
        if saw and ok:
            out.add(x)
    return out


def _cinst_concl(concl, tyvars):
    """Rewrite each standalone occurrence of an instantiable scalar type variable in a
    CONCLUSION to `ℂ` (the 𝕂 := ℂ / 𝔸 := ℂ instantiation — see the soundness note
    above). Returns (new_concl, instantiated_names)."""
    hit = [x for x in tyvars if x in concl]
    for x in hit:
        concl = re.sub(r'(?<![\w\'′₀-₉ℓ])' + re.escape(x) + r'(?![\w\'′₀-₉ℓ])',
                       'ℂ', concl)
    return concl, hit


def _enclosing_ns(text_before):
    """The dotted namespace enclosing a decl, given the file text up to its position.
    Tracks `namespace X` pushes and pops only on a matching `end X` (so a `section …`/`end …`
    never disturbs the namespace stack, and an unnamed `end` is ignored). Used to qualify a
    bare head that collides with a `_NS_STRIP_BLOCK` pair (see `_reg_resolve`)."""
    stack = []
    for ln in text_before.split("\n"):
        s = ln.strip()
        m = re.match(r'namespace\s+([\w.]+)', s)
        if m:
            stack.append(m.group(1).split("."))
            continue
        m = re.match(r'end\s+([\w.]+)\s*$', s)
        if m and stack and stack[-1] == m.group(1).split("."):
            stack.pop()
    return ".".join(seg for grp in stack for seg in grp)


# Top-level `=` for the regex fallback of `_links_asserted`: an equality sign that is
# NOT part of `:=`, `==`, `=>`, `!=`, `<=`, `>=`. Lean spells ≤ ≥ ≠ with single
# characters carrying no '=', so every remaining hit is a genuine equality relation;
# `=O[…]`/`=o[…]`/`=ᶠ[…]` each count once, which is the intended unit.
_TOPEQ_RE = re.compile(r"(?<![:!<>=])=(?![=>])")


def _links_asserted(concl):
    """(links_asserted, links_source) for a conclusion string: how many identity LINKS
    the statement asserts — the unit the chain-display coverage gate counts (a DLMF
    display asserting N identities, via an `a = b = c` chain or multi-line align rows,
    must be carried by one tagged theorem asserting ≥ N links).

    AST path ("ast") — `parse` is defined further down this module and resolved at call
    time (module-level late binding), so no reordering is needed. After unwrapping the
    ("forall", binders, body) wrapper, an ("and", parts) root asserts ONE LINK PER
    CONJUNCT whatever each conjunct's shape (eq / ineq / ("forallq", …) / Tendsto /
    HasSum / HasDerivAt); every other root asserts 1. An ("exists", …) root counts 1
    even when its body is an ("and", …): that conjunction constrains a WITNESS, it is
    not a chain of display links.

    Regex fallback ("regex", taken iff the parse raised): iteratively delete
    brace-nested `{…}` content (set-builders, structure instances, implicit binders —
    the `chain_census.py` rule), then count top-level `=` per `_TOPEQ_RE`, floored at 1.
    Deliberately does NOT strip parenthesised subterms — a parenthesised `=` is still an
    asserted equality (`(L = R) ∧ …`, theta_20_5_9's shape).

    Metadata only: never a verdict, and no hash consumes it (`closure_hash` hashes
    SOURCE text via statement_closure.decl_signature; `fidelity_cache.tier1_hash`
    hashes concl/binders/constraints), so the field cannot invalidate a cached row."""
    try:
        node = parse(concl or "")
    except Exception:
        s, prev = concl or "", None
        while prev != s:
            prev = s
            s = re.sub(r"\{[^{}]*\}", " ", s)
        return max(1, len(_TOPEQ_RE.findall(s))), "regex"
    while isinstance(node, tuple) and node and node[0] == "forall":
        node = node[2]
    if isinstance(node, tuple) and node and node[0] == "and":
        return len(node[1]), "ast"
    return 1, "ast"


# Standing invariant (CLAUDE.md §"Tag-block completeness"): every DLMF-tagged
# theorem carries a full `DAG: E-x.y.z` / `Fidelity: tier1 …` / `Verified: …`
# docstring block. A file where every TAG_RE-matched, non-suppressed docstring
# honors that invariant has no bare-prose `DLMF x.y.z` mention that TAG_RE
# could have mistaken for a genuine tag — such a file is safe to walk
# unconditionally. A file with even one bare-prose citation stays opt-in via
# an explicit `--chapters Methods-<File>` (see `main`'s Methods walk).
_HOUSE_TAG_RE = re.compile(r'DAG:\s*E-.*Fidelity:\s*tier1.*Verified:', re.S)


def _methods_file_audited(path):
    """True iff every TAG_RE-matched, non-`-- no-dlmf`-suppressed docstring in
    `path` carries the full house DAG:/Fidelity:/Verified: tag block."""
    text = path.read_text()
    for m in re.finditer(r'/--(.*?)-/', text, re.S):
        doc = m.group(1)
        if not TAG_RE.search(doc):
            continue
        suppressed = False
        for ln in reversed(text[:m.start()].split("\n")):
            s = ln.strip()
            if not s:
                continue
            if s.startswith("-- no-dlmf"):
                suppressed = True
                break
            if not s.startswith("--"):
                break
        if suppressed:
            continue
        rest = text[m.end():]
        dm = DECL_RE.search(rest)
        if not dm or rest[:dm.start()].strip():
            continue
        if not _HOUSE_TAG_RE.search(doc):
            return False
    return True


def extract(path):
    """Yield dicts {name,file,line,tags,doc,concl} for each DLMF-tagged decl."""
    text = path.read_text()
    lines = text.split("\n")
    sectvars = _section_binders(text)            # file-level `variable …` declarations
    # scalar tyvars instantiable at ℂ; the RCLike-instanced subset also types its
    # theorem-head VALUE binders `(a b : 𝕂)` as 'C' (the _section_binders policy,
    # extended to binders the theorem declares in its own head)
    cinst = _cinst_tyvars(text)
    rclike_cinst = cinst & set(re.findall(r'\[RCLike\s+([A-Za-zα-ω𝕂𝕜]\w*)\]', text))
    sectfinvecs = _section_finvecs(text, cinst)  # file-level `(A B : Fin p → 𝕂)` vector tuples
    # find docstring blocks /-- ... -/ and the decl that follows
    for m in re.finditer(r'/--(.*?)-/', text, re.S):
        doc = m.group(1)
        tags = TAG_RE.findall(doc)
        if not tags:
            continue
        # `-- no-dlmf: <reason>` marker convention: authors flag infrastructure /
        # bookkeeping lemmas whose DOCSTRING merely MENTIONS a DLMF section in
        # prose (e.g. "… identity theorem, DLMF §15.2(ii)") without the decl
        # itself formalizing that numbered equation — TAG_RE cannot tell prose
        # from a genuine formalization claim, so it over-tags these (the ch15
        # human-review finding: pfaffExtension_eqOn_lens & co. in
        # Frameworks/Hypergeometric were auto-tagged this way). Honor the marker:
        # walking UP from the `/--` opener, only contiguous `--` comment lines and
        # blanks may intervene — the FIRST non-comment line ends the search, so a
        # marker belonging to the PREVIOUS decl (its body sits in between) can
        # never bleed into this one (kummerCoefficient_contiguous_a sat 3 lines
        # under kummerCoefficient_zero's marker and was wrongly suppressed by a
        # plain 3-line lookback).
        suppressed = False
        for ln in reversed(text[:m.start()].split("\n")):
            s = ln.strip()
            if not s:
                continue
            if s.startswith("-- no-dlmf"):
                suppressed = True
                break
            if not s.startswith("--"):
                break
        if suppressed:
            continue
        rest = text[m.end():]
        dm = DECL_RE.search(rest)
        if not dm or rest[:dm.start()].strip():     # decl must immediately follow doc
            continue
        # belt-and-braces: also honor a marker sitting between the docstring's
        # `-/` and the decl line. Currently unreachable in practice — any such
        # non-blank text already fails the "decl must immediately follow doc"
        # check above — but kept for robustness if that rule is ever relaxed.
        if any(ln.strip().startswith("-- no-dlmf")
               for ln in rest[:dm.start()].split("\n") if ln.strip()):
            continue
        name = dm.group(1)
        # conclusion = between the top-level ':' (after binders) and ':=' / 'by'
        sig = rest[dm.end():]
        concl = _conclusion(sig)
        concl, cinst_hit = _cinst_concl(concl, cinst)   # 𝕂/𝔸 ↦ ℂ (gated; see _cinst_tyvars)
        line = text[:m.end()].count("\n") + 1
        binders, cons = _binders(sig, concl, ctyvars=rclike_cinst)
        for nm, base in sectvars.items():        # fill section-variable gaps (theorem binders win)
            binders.setdefault(nm, base)
        for nm, dim in sectfinvecs.items():      # file-level Fin-vector tuples (A/B : Fin p → 𝕂)
            binders.setdefault(nm, 'finvecC')    # → sampled as a `.q`-tagged complex callable;
            binders.setdefault(dim, 'N')         # its cardinality dim is a ℕ binder
            cons.setdefault('_finvecdim', {}).setdefault(nm, dim)
        # `[Fact p.Prime]` on a FILE-LEVEL `variable` line (GaussSumDirichlet.lean declares
        # `variable {p : ℕ} [Fact p.Prime]` once for the section): the theorem-head scan in
        # _binders cannot see it, so a section modulus would draw from the cyclic-moduli
        # grid {5,7,9,11} — and 9 is OUTSIDE the primality hypothesis (the statement says
        # nothing there; a sample at 9 could fabricate a counterexample or an out-of-domain
        # PASS). Upgrade the flag to the 'prime' grid {2,3,5,7,11}. Additive: sampling
        # restricted to the stated hypothesis domain; a stronger structured flag is kept.
        for vm in re.finditer(r'^\s*variable\b(.*)$', text, re.M):
            for mm in re.finditer(r'\[\s*Fact\s+(?:\(\s*Nat\.Prime\s+([A-Za-zα-ω]\w*)\s*\)|'
                                  r'([A-Za-zα-ω]\w*)\.Prime)\s*\]', vm.group(1)):
                pv = mm.group(1) or mm.group(2)
                if pv in binders and cons.get(pv) in (None, 'modulus', 'pos', 'nonneg'):
                    cons[pv] = 'prime'
        _pearson_witness(text, sig, concl, binders, cons)
        _carrier_prop_pins(text, sig, binders, cons)
        _scalar_eq_pins(sig, binders, cons)      # bare scalar-equation hypotheses (31.7.5)
        _cf_witness(sig, concl, cons)
        _smooth_deriv_witness(sig, concl, cons)
        _solution_fn_witness(sig, concl, cons)
        _free_fn_witness(sig, concl, cons)
        _stieltjes_witness(sig, concl, binders, cons)   # §31.15 Stieltjes/Van Vleck roles
        links, links_src = _links_asserted(concl)   # chain-coverage metadata (no verdict)
        row = {"name": name, "file": str(path.relative_to(ROOT.parent.parent)),
               "line": line, "tags": tags, "doc": " ".join(doc.split())[:120],
               "concl": concl, "binders": binders, "constraints": cons,
               "ns": _enclosing_ns(text[:m.start()]),
               "links_asserted": links, "links_source": links_src}
        if cinst_hit:                            # record the instantiation honestly
            row["tyinst"] = {x: "ℂ" for x in cinst_hit}
        yield row


def _colon_index(sig):
    """Index of the colon that starts the conclusion: first ':' at depth 0 not part of ':='."""
    depth = 0
    for i, c in enumerate(sig):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and sig[i:i + 2] != ":=":
            return i
    return -1


def _cf_witness(sig, concl, cons):
    """Record, for a conclusion that applies `.convs` to a NAMED `GenContFract` def
    (`(heunEigenCF a q α β γ δ).convs`, DLMF 31.4.2), whether the row ALSO assumes the
    hypothesis carrier whose certified witnesses `handle_named_cf_tendsto` samples —
    `IsHeunEigenvalue a q α β γ δ` (DLMF 31.4.1), on exactly those arguments in that
    order.  Without such a hypothesis the fraction's convergence to the target is simply
    not claimed, and the eigenvalue witness ladder would be an out-of-domain sample: the
    flag is then absent and the row keeps its honest skip.  Keyed on the CF def and the
    carrier TYPE recorded in `ob.CF_REGISTRY`, never on a theorem name."""
    if ".convs" not in concl:
        return
    for name, spec in getattr(ob, "CF_REGISTRY", {}).items():
        m = re.search(r'\(' + re.escape(name) + r'((?:\s+[^\s()]+)+)\)\.convs', concl)
        if not m:
            continue
        args = m.group(1).split()
        if len(args) != spec["arity"] or len(set(args)) != len(args):
            continue
        colon = _colon_index(sig)
        head = sig[:colon] if colon >= 0 else ""
        pat = re.escape(spec["requires"]) + r'\s+' + r'\s+'.join(re.escape(a) for a in args)
        if re.search(pat, head):
            cons.setdefault('_cfwitness', {})[name] = args


def _pearson_witness(text, sig, concl, binders, cons):
    """∀-quantified Pearson system — a file-level `variable (P : PearsonSystem)`
    (Rodrigues.lean; DLMF 18.5.5) binds an abstract structure the oracle cannot sample
    as a scalar, so the sweep skipped `rodrigues_spec` as `unbound:k`. Like the
    IsCDSystem / IsMultiplicative ∀-witnesses, instantiate the system at the anchored
    Hermite-He row of DLMF Table 18.5.1 / §18.3 (w = e^{−x²/2}, F = 1, κₙ = (−1)ⁿ —
    ob._hermitePearson_w / _kernel / _norm, anchored in oracle_bindings.verify() to the
    18.5.5 defining identity κₙ·w(x)·Heₙ(x) = dⁿ/dxⁿ[w·Fⁿ](x) and the Pearson equation
    before the sweep trusts them). Keyed on the binder TYPE `PearsonSystem`, never on
    variable names; the κ-slot (the normalization function, first argument of
    `P.rodrigues κ …` — the abstract κₙ of 18.5.5) is coupled to the same table row.
    Sound as a refutation oracle: a numeric counterexample at the witness disproves the
    ∀-statement; passing is evidence.

    GUARDS (fail to the honest unbound skip, never a fabricated verdict):
      • only projections the witness map covers (w / kernel / rodrigues) may appear in
        the conclusion, and hypotheses may reach the system only through its weight
        (`P.w x ≠ 0` — satisfied identically: the witness w never vanishes). Any other
        projection (P.σ, P.τ, …) could carry a hypothesis the Hermite witness violates
        (σ = 1 has degree 0), fabricating a FAIL — such a row stays unbound.
      • the κ-slot may be constrained only by the 18.5.5 nonvanishing `κ n ≠ 0`
        (satisfied identically by (−1)ⁿ); any other hypothesis on it keeps the skip."""
    for pv in re.findall(r'^\s*variable\b[^\n]*[({]\s*([A-Za-zα-ω]\w*)\s*:\s*PearsonSystem'
                         r'\s*[)}]', text, re.M):
        pdot = re.escape(pv) + r'\.(\w+)'
        flds = set(re.findall(pdot, concl))
        if not flds or not flds <= {"w", "kernel", "rodrigues"}:
            continue
        colon = _colon_index(sig)
        head = sig[:colon] if colon >= 0 else ""
        if not set(re.findall(pdot, head)) <= {"w"}:
            continue
        wm = cons.setdefault('_fnwitness', {})
        wm[pv + '.w'] = 'hermitePearsonW'
        wm[pv + '.kernel'] = 'hermitePearsonKernel'
        wm[pv + '.rodrigues'] = 'hermitePearson.rodrigues'
        am = re.search(re.escape(pv) + r'\.rodrigues\s+([A-Za-zα-ω]\w*)\b', concl)
        if am:
            kv = am.group(1)
            if binders.get(kv) == "other" and kv not in wm:
                ok = True
                for grp in re.finditer(r'[({⦃]([^:(){}]+?)\s*:\s*([^(){}]+?)[)}⦄]', head):
                    ty = grp.group(2).strip()
                    if re.search(r'\b' + re.escape(kv) + r'\b', ty) and not \
                            re.fullmatch(re.escape(kv) + r'\s+[A-Za-zα-ω]\w*\s*≠\s*0', ty):
                        ok = False
                        break
                if ok:
                    wm[kv] = 'hermitePearsonNorm'


def _split_top_eq(s):
    """Split `A = B` at the single bracket-depth-0 '=' that is not part of ':=', '==',
    '≠', '≤', '≥'. Returns (A, B) or None when there is not exactly one such '='."""
    depth, cuts = 0, []
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "=" and depth == 0:
            if s[i - 1:i] in (":", "!", "<", ">", "=") or s[i + 1:i + 2] == "=":
                return None
            cuts.append(i)
    if len(cuts) != 1:
        return None
    return s[:cuts[0]].strip(), s[cuts[0] + 1:].strip()


# A same-file `def Name (…scalars…) : Prop := <eq> ∧ <eq> ∧ …` carrier body is admissible
# for the constructive pin below only when EVERY character of the substituted body is a
# scalar-arithmetic one: identifiers (ASCII or Greek), digits, the four operations, '^',
# parentheses, '=' and '∧'.  Anything else — a '∀'/'∃'/'→'/'↔', an inequality, a field
# projection '.', a set/function argument — means the carrier says more than a system of
# scalar equations, so nothing is recorded and the row keeps its honest verdict.
_PROP_CARRIER_BODY_RE = re.compile(r"^[\w\sα-ωΑ-Ωϵ'()+\-*/^=∧]+$")


def _local_prop_names(text):
    """Every same-file `def`/`abbrev` whose result type is `Prop`, INCLUDING the ones whose
    signature wraps over several lines (those are invisible to `_local_prop_defs`, which
    pins only single-line signatures — but they must still be COUNTED, or a second,
    unparsed carrier could be silently ignored while the first one is honored).
    A line scan, not a multi-line regex: the corpus has 25 000-line files."""
    out, cur, buf = set(), None, ""
    for ln in text.split("\n"):
        m = re.match(r'^(?:def|abbrev)\s+([A-Za-z_][\w\']*)(.*)$', ln)
        if m:
            cur, buf = m.group(1), m.group(2)
        elif cur is not None and ln.startswith((" ", "\t")):
            buf += " " + ln.strip()
        else:
            cur = None
            continue
        if ":=" in buf:
            if re.search(r':\s*Prop\s*:=', buf):
                out.add(cur)
            cur = None
    return out


def _local_prop_defs(text):
    """`{name: ([(param, base)], body)}` for every same-file
    `def Name (a b : ℂ) (c : ℝ) : Prop := <body>` whose parameters are ALL scalar (ℂ/ℝ).

    These are the §31.11-style hypothesis CARRIERS: a display that fixes its data by a
    system of equations is surfaced as a theorem quantified under such a carrier, and the
    carrier is exactly what pins the binders.  A parameter of any other type (a set, a
    sequence, a function) makes the carrier say more than a scalar system, and the def is
    skipped — see `_carrier_prop_pins` for the rest of the guards."""
    out, lines = {}, text.split("\n")
    for i, ln in enumerate(lines):
        m = re.match(r'^def\s+([A-Za-z_][\w\']*)\s*'
                     r'((?:\([^()]*\)\s*)*):\s*Prop\s*:=\s*(.*)$', ln)
        if not m:
            continue
        params, ok = [], True
        for pg in re.finditer(r'\(([^():]+):\s*([^()]+)\)', m.group(2)):
            ty = pg.group(2).strip()
            if ty not in ("ℂ", "ℝ"):
                ok = False
                break
            for nm in pg.group(1).split():
                params.append((nm, "C" if ty == "ℂ" else "R"))
        if not ok or not params:
            continue
        body = m.group(3).strip()
        for nxt in lines[i + 1:]:               # body = the indented continuation block
            if not nxt.strip():
                if body:
                    break
                continue
            if not nxt.startswith((" ", "\t")):
                break
            body += " " + nxt.strip()
        if body:
            out[m.group(1)] = (params, " ".join(body.split()))
    return out


def _carrier_prop_pins(text, sig, binders, cons):
    """Constructive pin ('_linpin') for a hypothesis that APPLIES a same-file scalar Prop
    carrier, `h : HeunSeriesTypeI1 α β ε lam mu` with
    `def HeunSeriesTypeI1 (α β ε lam mu : ℂ) : Prop := lam = α ∧ mu = β - ε`
    (DLMF 31.11.10; likewise 31.11.3/11/14–17 and the §31.11(iii) rows that assume them).

    The carrier is the ONLY thing tying the row's binders together: `collect_free` frees
    `lam`/`mu` from the conclusion, so the sampler otherwise draws them INDEPENDENTLY of
    `α, β, ε` and scores the display at points the hypothesis excludes — a fabricated
    refutation, not a DLMF discrepancy (this is the `heun_31_11_*` double-FAIL cluster).

    Record, for each conjunct of the substituted body, ONE variable to solve that conjunct
    for; `sweep_eq` drops it from the grid and computes it per sample by an affine solve
    whose residual is re-verified against the SAME parsed equation (see the '_linpin' block
    there).  ADDITIVE and sound: each pinned variable takes EXACTLY the value the stated
    hypothesis assigns it — nothing is loosened, no tolerance or gate moves, and a
    conjunct that is not affine in its pin variable fails the residual check and drops the
    point honestly.

    GUARDS — any failure records nothing and the row keeps its present verdict:
      • the carrier must be a same-file `def … : Prop` with all-scalar parameters, applied
        to exactly that many DISTINCT identifier arguments, each a declared scalar binder;
      • the substituted body must be a pure scalar-equation conjunction
        (`_PROP_CARRIER_BODY_RE`) — no quantifier, inequality, or projection;
      • every conjunct must receive a pin, and a pin variable may occur in NO OTHER
        conjunct (so the pins are mutually independent and order-free) and must not
        already be pinned by '_defeq' or by an `ob.CARRIER_PINS` ladder ('_carrier');
      • the head must assume EXACTLY ONE same-file Prop carrier.  Two carriers state a
        JOINT system (DLMF 31.11.13 assumes 31.11.3 AND 31.11.10 at once, which is
        over-determined and only consistent through the Fuchsian relation), and honoring
        one while ignoring the other would sample outside the row's stated hypotheses —
        exactly the fabricated refutation this pin exists to prevent.  Such a row keeps
        its present verdict untouched."""
    if '_carrier' in cons or '_linpin' in cons:
        return
    colon = _colon_index(sig)
    head = sig[:colon] if colon >= 0 else sig.split(":=")[0]
    allprops = _local_prop_names(text)
    if sum(1 for g in re.finditer(r'[({⦃]([^:(){}]+?)\s*:\s*([^(){}]+?)[)}⦄]', head)
           if g.group(2).strip().split(" ")[0] in allprops) != 1:
        return
    defs = None
    for grp in re.finditer(r'[({⦃]([^:(){}]+?)\s*:\s*([^(){}]+?)[)}⦄]', head):
        mm = re.fullmatch(r'([A-Za-z_][\w\']*)((?:\s+[A-Za-zα-ωΑ-Ω_][\w\']*)+)',
                          grp.group(2).strip())
        if not mm:
            continue
        if defs is None:
            defs = _local_prop_defs(text)
        spec = defs.get(mm.group(1))
        if spec is None:
            continue
        params, body = spec
        args = mm.group(2).split()
        if len(args) != len(params) or len(set(args)) != len(args):
            continue
        if any(binders.get(a) != b for a, (_, b) in zip(args, params)):
            continue
        sub = {p: a for (p, _), a in zip(params, args)}
        body = re.sub(r"(?<![\w'])(" + "|".join(re.escape(p) for p, _ in params) +
                      r")(?![\w'])", lambda x: sub[x.group(1)], body)
        if not _PROP_CARRIER_BODY_RE.fullmatch(body):
            continue
        parts = [_split_top_eq(p) for p in _split_top_and_text(body)]
        if not parts or any(p is None for p in parts):
            continue
        names = [set(re.findall(r"[A-Za-zα-ωΑ-Ω_][\w']*", lhs + " " + rhs))
                 for lhs, rhs in parts]
        taken = {q[0] for q in cons.get('_defeq', [])}
        pins = []
        for k, (lhs, rhs) in enumerate(parts):
            elsewhere = set().union(*[names[j] for j in range(len(parts)) if j != k]) \
                if len(parts) > 1 else set()
            cand = [v for v in re.findall(r"[A-Za-zα-ωΑ-Ω_][\w']*", lhs + " " + rhs)
                    if binders.get(v) in ("C", "R") and v not in elsewhere
                    and v not in taken
                    and len(re.findall(r"(?<![\w'])" + re.escape(v) + r"(?![\w'])",
                                       lhs + " " + rhs)) == 1]
            if not cand:
                break
            pick = lhs if lhs in cand else (rhs if rhs in cand else cand[0])
            taken.add(pick)
            pins.append((pick, lhs, rhs))
        if len(pins) != len(parts):
            continue
        cons['_linpin'] = pins
        return


# A BARE scalar-equation hypothesis (`ha : a * k ^ 2 = 1`) is admissible for the
# constructive pin below only when every character of its TYPE is scalar arithmetic:
# identifiers (ASCII or Greek), digits, the four operations, '^', parentheses and the
# single '='. Anything else — a '∀'/'∃'/'→'/'↔', an inequality, a field projection '.',
# a set/function argument — means the hypothesis says more than one scalar equation, so
# nothing is recorded and the row keeps its present sampling and verdict.
_SCALAR_EQ_HYP_RE = re.compile(r"^[\w\sα-ωΑ-Ωϵ'()+\-*/^=]+$")

_EQPIN_MAX_EQS = 12          # backtracking search is over ≤ this many equations …
_EQPIN_MAX_NODES = 20000     # … and bails after this many DFS nodes (cost guard only)


def _eqpin_affine(lhs, rhs, v, vars_):
    """Is the parsed equation `lhs = rhs` AFFINE in `v`, with non-degenerate slope?

    Decided numerically at two independent probe environments for the OTHER variables:
    `f(t) = lhs − rhs` at `v = 0, 1, 2` must satisfy the exact second-difference identity
    `f(2) − 2f(1) + f(0) = 0` and have a non-vanishing first difference.  Affine + non-
    degenerate ⇒ the stated equation determines `v` UNIQUELY from the other variables,
    which is what makes pinning it sound (no branch is silently chosen).  Any parse or
    evaluation failure answers "no", and the row simply keeps its present sampling.

    Selection only: the value actually used at each sample is re-solved and its residual
    re-verified against the SAME parsed equation in `sweep_eq`."""
    try:
        L, R = parse(lhs), parse(rhs)
        L = L[1] if L and L[0] == "expr" else L
        R = R[1] if R and R[0] == "expr" else R
    except Exception:
        return False
    for seed in (0, 3):
        env = {}
        for j, x in enumerate(sorted(vars_)):
            env[x] = mp.mpc(mp.mpf(3 + (7 * (j + seed)) % 11) / 10,
                            mp.mpf(1 + (5 * (j + seed)) % 7) / 10)
        vals = []
        for t in (0, 1, 2):
            e = dict(env)
            e[v] = mp.mpc(t)
            try:
                vals.append(mp.mpc(evaluate(L, e)) - mp.mpc(evaluate(R, e)))
            except Exception:
                return False
        f0, f1, f2 = vals
        scale = 1 + abs(f0) + abs(f1) + abs(f2)
        if abs(f2 - 2 * f1 + f0) > mp.mpf("1e-18") * scale:
            return False                       # not affine in v (a k², 1/v, eᵛ, …)
        if abs(f1 - f0) < mp.mpf("1e-8") * (1 + abs(f0)):
            return False                       # degenerate slope: v is not determined
    return True


def _scalar_eq_pins(sig, binders, cons):
    """Constructive pins ('_eqpin') for the row's BARE scalar-equation hypotheses — the
    singleton form of the `_linpin` carrier pin, with plain equations in the binder list
    instead of a named Prop.

    DLMF 31.7.5 (`heun_31_7_5`) is the model: the Lamé parameter dictionary is stated in
    its cleared-denominator form `(ha : a * k ^ 2 = 1) (hq : 4 * q + a * h = 0)
    (hα : 2 * α + ν = 0) (hβ : 2 * β = ν + 1) (hγ : 2 * γ = 1) (hδ : 2 * δ = 1)
    (hε : γ + δ + ε = α + β + 1)`, and those hypotheses are the ONLY thing tying the row's
    binders together.  Typed 'other' and otherwise dropped, they let the sampler draw
    a, q, α, β, γ, δ, ε INDEPENDENTLY of k, h, ν and score the display at points the
    hypotheses exclude — a fabricated refutation (all seven conjuncts FAIL), not a DLMF
    discrepancy.

    Record, for each such hypothesis, ONE variable to solve it for, in a SOLVE ORDER in
    which every other variable of the equation is either free-sampled or already pinned;
    `sweep_eq` drops the pinned variables from the grid, injects the equations' remaining
    inputs into it, and computes each pinned value per sample by an affine solve whose
    residual is re-verified against the SAME parsed equation.  ADDITIVE and sound: each
    pinned variable takes EXACTLY the value the stated hypotheses force — nothing is
    loosened, no tolerance, gate or settle window moves, and any point at which the solve
    or its residual check fails is dropped honestly rather than scored.

    GUARDS — any failure records nothing and the row keeps its present verdict:
      • the row must carry no other pin ladder ('_carrier'/'_linpin'), and no equation may
        mention a variable already pinned by '_defeq';
      • each hypothesis TYPE must be a single pure scalar equation (`_SCALAR_EQ_HYP_RE`,
        exactly one top-level '='), every identifier in which is a declared ℂ/ℝ binder —
        a function head, a projection or an integer binder disqualifies it;
      • a pin variable must occur EXACTLY ONCE in its equation, must carry no recorded
        domain constraint of its own (a pinned value could otherwise leave a stated
        domain), and the equation must be affine in it with non-degenerate slope
        (`_eqpin_affine`), so the hypothesis determines it uniquely;
      • the pins must be injective and their dependency graph acyclic, so a solve order
        exists; otherwise nothing is recorded."""
    if '_carrier' in cons or '_linpin' in cons or '_eqpin' in cons:
        return
    colon = _colon_index(sig)
    head = sig[:colon] if colon >= 0 else sig.split(":=")[0]
    taken = {q[0] for q in cons.get('_defeq', [])}

    def _constrained(v):
        """Does v carry any recorded domain constraint (flag, bound or pairwise)?"""
        if any(kk == v or kk.startswith(v + ".") for kk in cons if not kk.startswith('_')):
            return True
        for key in ('_flags', '_lower', '_upper', '_finvecdim', '_zmodchar', '_dirchmod'):
            d = cons.get(key) or {}
            if v in d or any(v == x for x in d.values()):
                return True
        for pr in cons.get('_pairs', []) or []:
            if any(isinstance(x, str) and re.search(r"(?<![\w'])" + re.escape(v) + r"(?![\w'])", x)
                   for x in pr):
                return True
        return False

    eqs = []                                   # [(vars, lhs, rhs, text)]
    for grp in _toplevel_binder_groups(head):
        if ":" not in grp:
            continue
        ty = " ".join(grp.split(":", 1)[1].split())
        if not _SCALAR_EQ_HYP_RE.fullmatch(ty):
            continue
        parts = _split_top_eq(ty)
        if parts is None:
            continue
        idents = re.findall(r"[A-Za-zα-ωΑ-Ωϵ_][\w']*", ty)
        if not idents or any(binders.get(v) not in ("C", "R") for v in idents):
            continue                           # not a pure scalar equation in this row's binders
        if any(v in taken for v in idents):
            continue                           # overlaps a '_defeq' pin — leave both alone
        eqs.append((set(idents), parts[0], parts[1], ty))
    if not eqs or len(eqs) > _EQPIN_MAX_EQS:
        return

    cands = []
    for vs, lhs, rhs, ty in eqs:
        pool = []
        for v in sorted(vs):
            if v in taken or _constrained(v):
                continue
            if len(re.findall(r"(?<![\w'])" + re.escape(v) + r"(?![\w'])", ty)) != 1:
                continue
            if not _eqpin_affine(lhs, rhs, v, vs):
                continue
            pool.append(v)
        # deterministic preference: a variable occurring in FEWER of the other equations
        # first (it constrains the solve order least), then by position in this equation.
        pool.sort(key=lambda v: (sum(1 for e in eqs if v in e[0]),
                                 re.search(r"(?<![\w'])" + re.escape(v) + r"(?![\w'])",
                                           ty).start()))
        cands.append(pool)
    if any(not c for c in cands):
        return

    n = len(eqs)

    def _solve_order(assign):
        """A topological solve order for `assign` (equation i pins assign[i]), or None."""
        src = {assign[i]: i for i in range(n)}
        deps = {i: {src[w] for w in eqs[i][0] if w in src and w != assign[i]}
                for i in range(n)}
        done, order = set(), []
        while len(order) < n:
            nxt = [i for i in range(n) if i not in done and deps[i] <= done]
            if not nxt:
                return None                    # cyclic: no equation can be solved next
            done.update(nxt)
            order.extend(nxt)
        return order

    found, nodes = [], [0]

    def _rec(i, used, assign):
        if found or nodes[0] > _EQPIN_MAX_NODES:
            return
        nodes[0] += 1
        if i == n:
            order = _solve_order(assign)
            if order is not None:
                found.append([(assign[j], eqs[j][1], eqs[j][2]) for j in order])
            return
        for v in cands[i]:
            if v in used:
                continue
            _rec(i + 1, used | {v}, assign + [v])
            if found:
                return

    _rec(0, set(taken), [])
    if found:
        cons['_eqpin'] = found[0]


def _head_groups(head):
    """Top-level bracket-balanced binder groups of a theorem head (the flat regex used
    elsewhere cannot see a hypothesis whose TYPE contains parentheses, e.g.
    `hw : DifferentiableAt ℝ (deriv w) z`). Returns the inner text of each group."""
    groups, depth, start = [], 0, None
    for j, c in enumerate(head):
        if c in "([{⦃":
            if depth == 0:
                start = j + 1
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(head[start:j])
                start = None
    return groups


def _smooth_wit_ast(i):
    """The i-th canonical everywhere-smooth TRANSCENDENTAL witness, as a lambda AST
    (`_subst_fn_witness` splices it in place of a ∀-quantified `w : ℝ → ℝ` binder).
    Each witness is entire (real-analytic on all of ℝ, so every DifferentiableAt /
    ContDiff-type hypothesis holds identically at every sampled point) and has no
    accidental parity/algebraic symmetry — w(y) = e^y sin y has w, w′, w″ pairwise
    independent, so the nested-deriv sweep genuinely exercises the identity. Distinct
    binder slots get DISTINCT witnesses (i cycles), so a statement true only on the
    diagonal w = v cannot pass by collapse. Built from the already-anchored exp/sin/cos
    registry heads; the bound variable is a private name no theorem binder can shadow."""
    y = ("var", "_wity")
    def app(h, a):
        return ("app", ("var", h), [a])
    bodies = (
        ("bin", "*", app("Real.exp", y), app("Real.sin", y)),                 # e^y sin y
        ("bin", "*", app("Real.exp", ("neg", y)), app("Real.cos", y)),        # e^{−y} cos y
        ("bin", "+", app("Real.sin", ("bin", "*", ("num", "2"), y)),
         app("Real.exp", ("bin", "*", ("num", "0.5"), y))),                   # sin 2y + e^{y/2}
    )
    return ("lam", "_wity", bodies[i % len(bodies)])


def _entire_wit_ast(i):
    """The i-th canonical ENTIRE ℂ→ℂ witness, as a lambda AST (`_subst_fn_witness` splices it
    in place of a HYPOTHESIS-FREE function binder `W : ℂ → ℂ`; see `_free_fn_witness`).
    Complex analogue of `_smooth_wit_ast`: each body is entire (so any analyticity /
    differentiability property one might state of such a binder holds identically), nowhere
    identically zero, and built only from already-anchored registry heads (`Complex.exp/sin/
    cos`). The witnesses are algebraically independent of one another and have no parity or
    functional-equation symmetry that an identity could exploit; distinct binder slots get
    DISTINCT witnesses (i cycles), so a claim true only on the diagonal cannot pass by
    collapse. The bound variable is a private name no theorem binder can shadow."""
    z = ("var", "_witz")

    def app(h, a):
        return ("app", ("var", h), [a])
    bodies = (
        ("bin", "*", app("Complex.exp", z), ("bin", "+", ("num", "1"), z)),      # (1+z)e^z
        ("bin", "+", app("Complex.sin", z), ("bin", "*", ("num", "2"), app("Complex.exp", ("neg", z)))),
                                                                                # sin z + 2e^{−z}
        ("bin", "+", ("bin", "*", ("num", "3"), app("Complex.cos", z)),
         ("bin", "*", z, z)),                                                    # 3cos z + z²
    )
    return ("lam", "_witz", bodies[i % len(bodies)])


# Higher-order heads that consume a function binder as a FUNCTION (not at a point): if the
# binder occurs under one of these, the plain application-witness route is not wired and the
# row keeps its honest skip.
_HO_HEADS = {"deriv", "logDeriv", "iteratedDeriv", "iteratedDerivWithin", "derivWithin",
             "HasDerivAt", "HasDerivWithinAt", "DifferentiableAt", "Differentiable",
             "ContDiff", "ContDiffAt", "AnalyticAt", "AnalyticOn", "AnalyticOnNhd",
             "Continuous", "ContinuousAt", "Tendsto", "Filter.Tendsto", "Summable",
             "IsBigO", "Asymptotics.IsBigO", "Set.EqOn", "EqOn", "Function.comp",
             "MeromorphicAt", "MeromorphicOn", "intervalIntegral", "IsHeunSolution"}


def _free_fn_witness(sig, concl, cons):
    """HYPOTHESIS-FREE function binder `(W : ℂ → ℂ)` that occurs in the conclusion ONLY in
    plain APPLICATION position (`W ξ`, `W t`) — e.g. the Weierstrass-form substitution
    heun_31_2_10 (Ch31DifferentialEquations.lean, DLMF 31.2.10), whose statement is an
    algebraic identity in the VALUES of an otherwise arbitrary unknown `W`. Such a binder
    cannot be sampled as a scalar, so the sweep skipped the row as `unbound:W`.

    Like the IsCompletelyMultiplicative / Pearson / CD-system / smooth-deriv witnesses,
    instantiate it at canonical entire witnesses (`_entire_wit_ast`). Sound as a refutation
    oracle: the theorem quantifies over ALL `W : ℂ → ℂ`, so a numeric counterexample at a
    concrete entire witness disproves it; passing is evidence. Keyed on the binder TYPE
    `ℂ → ℂ` and on the occurrence SHAPE, never on variable names.

    GUARDS (each failure keeps the honest `unbound` skip, never a fabricated verdict):
      • the name must resolve to nothing in the registry (a bound head is left alone, so no
        already-decided row can change);
      • NO hypothesis of the theorem may mention the binder — an unconstrained ∀ is what
        makes an arbitrary witness admissible; any hypothesis could be violated by the
        witness and fabricate a FAIL;
      • every conclusion occurrence must be an application `W <arg>` and must NOT sit under
        a higher-order head (`_HO_HEADS`: deriv, AnalyticAt, Tendsto, IsHeunSolution, …) —
        those consume the function itself, and this route is only wired for point values."""
    colon = _colon_index(sig)
    head = sig[:colon] if colon >= 0 else sig.split(":=")[0]
    groups = _head_groups(head)
    idx = 0
    for gi, g in enumerate(groups):
        ci = _colon_index(g)
        if ci < 0:
            continue
        names, typ = g[:ci].split(), g[ci + 1:].strip()
        if not re.fullmatch(r'ℂ\s*→\s*ℂ', typ):
            continue
        for f in names:
            if not re.fullmatch(r'[A-Za-zα-ω]\w*', f):
                continue
            if f in cons.get('_fnwitness', {}) or _reg_resolve(f) is not None:
                continue
            fe = re.escape(f)
            occ = re.compile(rf"(?<![\w.′]){fe}(?![\w.′'])")
            # any OTHER head group mentioning f is a hypothesis (or a coupled binder) on it
            if any(occ.search(h) for hi, h in enumerate(groups) if hi != gi):
                continue
            occs = list(occ.finditer(concl))
            if not occs:
                continue                       # W unused in the conclusion — nothing to do
            ok = True
            for m in occs:
                if not re.match(r'\s+[\w(⟨«]', concl[m.end():]):
                    ok = False                 # not applied to an argument
                    break
                pre = re.sub(r'[\s(]+$', '', concl[:m.start()])
                pt = re.search(r'[\w.]+$', pre)
                if pt and pt.group(0).split(".")[-1] in _HO_HEADS or pt and pt.group(0) in _HO_HEADS:
                    ok = False                 # consumed as a function, not at a point
                    break
            if not ok:
                continue
            cons.setdefault('_fnwitness', {})[f] = f'entirefn:{idx}'
            idx += 1


def _smooth_deriv_witness(sig, concl, cons):
    """∀-quantified plain smooth-function binder `(w : ℝ → ℝ)` that appears in the
    conclusion ONLY as the operand of (possibly nested) inline `deriv`, with every
    hypothesis on w a smoothness assumption (DifferentiableAt / Differentiable /
    ContDiffAt / ContDiff over ℝ, of w or a nested deriv of w) — the Sturm–Liouville
    expansion surface `deriv_oneSubSq_mul_deriv` (Spheroidal/Basic.lean, DLMF 30.2.1),
    which the sweep skipped as undersampled because the abstract w cannot be sampled
    as a scalar. Like the IsCompletelyMultiplicative / Pearson / CD-system witnesses,
    instantiate w at a canonical everywhere-smooth transcendental witness
    (_smooth_wit_ast: e^y·sin y, …), which satisfies every recorded hypothesis
    identically (an entire function is C^∞ at every point), and sweep the equality
    with the existing nested-deriv mp.diff path over the z grid. Sound as a
    refutation oracle: a numeric counterexample at the witness disproves the
    ∀-statement; passing is evidence. Keyed on the binder TYPE `ℝ → ℝ` and the
    recognized hypothesis SHAPES, never on variable names.

    GUARDS (fail to the honest unbound/undersampled skip, never a fabricated verdict):
      • any occurrence of w in the conclusion outside a `deriv` operand slot keeps
        the skip (the witness mechanism is only wired for the deriv paths);
      • any hypothesis mentioning w that is not one of the recognized smoothness
        shapes could be violated by the witness (fabricating a FAIL) — such a row
        keeps its skip."""
    colon = _colon_index(sig)
    head = sig[:colon] if colon >= 0 else sig.split(":=")[0]
    groups = _head_groups(head)
    idx = 0
    for gi, g in enumerate(groups):
        ci = _colon_index(g)
        if ci < 0:
            continue
        names, typ = g[:ci].split(), g[ci + 1:].strip()
        if not re.fullmatch(r'ℝ\s*→\s*ℝ', typ):
            continue
        for f in names:
            if not re.fullmatch(r'[A-Za-zα-ω]\w*', f):
                continue
            fe = re.escape(f)
            occ = re.compile(rf"(?<![\w.′]){fe}(?![\w.′'])")
            occs = list(occ.finditer(concl))
            if not occs:
                continue                       # w unused in the conclusion — nothing to do
            if not all(re.search(r'(?<![\w.])deriv\s*[(\s]\s*$', concl[:m.start()])
                       for m in occs):
                continue                       # w outside a deriv operand → honest skip
            # nested-deriv wrappings of w a smoothness hypothesis may mention
            fw = rf'(?:{fe}|\(\s*deriv\s+{fe}\s*\)|\(\s*deriv\s+\(\s*deriv\s+{fe}\s*\)\s*\))'
            smooth = re.compile(
                rf'(?:DifferentiableAt\s+ℝ\s+{fw}\s+\S+'
                rf'|Differentiable\s+ℝ\s+{fw}'
                rf'|ContDiffAt\s+ℝ\s+\S+\s+{fe}\s+\S+'
                rf'|ContDiff\s+ℝ\s+\S+\s+{fe})')
            if all(smooth.fullmatch(h[_colon_index(h) + 1:].strip())
                   for hi, h in enumerate(groups)
                   if hi != gi and _colon_index(h) >= 0
                   and occ.search(h[_colon_index(h) + 1:])):
                cons.setdefault('_fnwitness', {})[f] = f'smoothfn:{idx}'
                idx += 1


# Analyticity/smoothness hypothesis shapes an ANALYTIC witness satisfies identically at
# every point of its own domain of definition.  Used by `_solution_fn_witness` to decide
# whether an abstract `w : ℂ → ℂ` binder may be instantiated at a concrete analytic
# witness: any OTHER hypothesis on w could be violated by the witness (and so fabricate a
# verdict), and such a row keeps its honest skip.
# Only the POINTWISE ("…At") shapes are admitted: a GLOBAL hypothesis (`AnalyticOn ℂ w
# Set.univ`) is NOT satisfied by the local Heun witness, whose Maclaurin series defines it
# only inside its disc, and instantiating a ∀ at a witness that violates a hypothesis
# would make a disagreement prove nothing.
_ANALYTIC_HYP = (r'(?:AnalyticAt|DifferentiableAt|ContDiffAt|MeromorphicAt|ContinuousAt)')


def _solution_fn_witness(sig, concl, cons):
    """A ∀-quantified abstract solution binder `w : ℂ → ℂ` of an ODE-solution display
    (`IsHeunSolution a q α β γ δ w z ↔ <transformed equation> = 0`, DLMF 31.2.6/31.2.8),
    every hypothesis on which is an ANALYTICITY assumption (`hw : AnalyticAt ℂ w z`).

    Records `cons['_solfn'][w] = <the analyticity point's source text>` (or `True` when no
    hypothesis mentions w at all), which licenses `handle_solution_iff` to
    instantiate the ∀ at concrete ANALYTIC witnesses — the local Heun function `heunFn`
    (which makes the solution predicate HOLD) and the canonical entire witnesses of
    `_entire_wit_ast` (which make it FAIL).  Sound as a refutation oracle in exactly the
    sense of the IsCompletelyMultiplicative / Pearson / smoothfn witnesses: each witness
    satisfies every recorded hypothesis, so a disagreement between the two sides of the
    `↔` at a witness disproves the ∀-statement; agreement is evidence.

    This routine ONLY records admissibility — it is the sig-level half of the check, run
    where the hypothesis TEXT is still in hand.  The numeric half (which witnesses, which
    points, what residual gate) lives in `handle_solution_iff`.

    GUARDS — anything unrecognised simply is not recorded, and the row keeps its honest
    skip, never a fabricated verdict:
      • the binder type must be exactly `ℂ → ℂ`;
      • the name must not already carry a witness or resolve in the registry;
      • EVERY other head group mentioning w must be a POINTWISE `_ANALYTIC_HYP` shape
        `<Head> ℂ w <point>`, and all of them must name the SAME point — which
        `handle_solution_iff` then requires to be the display's own solution point, so a
        witness analytic only near that point is a legitimate instantiation."""
    # Restricted to the solution-predicate heads the numeric half actually serves, so the
    # constraint dict of every other row is left byte-identical (a stray '_solfn' key would
    # otherwise change unrelated rows' honest-skip MESSAGE without changing their verdict).
    # The four §31.12 confluent-Heun heads (Is{Confluent,DoublyConfluent,Biconfluent,
    # Triconfluent}HeunSolution) are served by `handle_ode_predicate_iff`, whose first guard
    # reads `cons['_solfn']` — the same sig-level/numeric-half split as the earlier
    # IsHeunSolution → IsFuchsianSolution extension for the §31.15 lane.
    if not re.search(r'(?<![\w.])(?:Is(?:Confluent|DoublyConfluent|Biconfluent|'
                     r'Triconfluent)?HeunSolution|IsFuchsianSolution)(?![\w.])', concl):
        return
    colon = _colon_index(sig)
    head = sig[:colon] if colon >= 0 else sig.split(":=")[0]
    groups = _head_groups(head)
    for gi, g in enumerate(groups):
        ci = _colon_index(g)
        if ci < 0:
            continue
        names, typ = g[:ci].split(), g[ci + 1:].strip()
        if not re.fullmatch(r'ℂ\s*→\s*ℂ', typ):
            continue
        for f in names:
            if not re.fullmatch(r'[A-Za-zα-ω]\w*', f):
                continue
            if f in cons.get('_fnwitness', {}) or _reg_resolve(f) is not None:
                continue
            fe = re.escape(f)
            occ = re.compile(rf"(?<![\w.′]){fe}(?![\w.′'])")
            if not occ.search(concl):
                continue                       # w unused in the conclusion — nothing to do
            hyp = re.compile(rf'^{_ANALYTIC_HYP}\s+(?:ℂ|ℝ)\s+{fe}\s+(\S.*)$')
            pts, ok = set(), True
            for hi, h in enumerate(groups):
                ci2 = _colon_index(h)
                if hi == gi or ci2 < 0 or not occ.search(h[ci2 + 1:]):
                    continue
                m2 = hyp.match(" ".join(h[ci2 + 1:].split()))
                if not m2:
                    ok = False                 # a hypothesis the witness might violate
                    break
                pts.add(_strip_outer_parens(m2.group(1).strip()))
            if ok and len(pts) <= 1:
                cons.setdefault('_solfn', {})[f] = pts.pop() if pts else True


def _strip_leading_lets(body):
    """δ-inline leading term-mode `let NAME : TYPE := VALUE` bindings of a conclusion so the
    real Prop is what remains. A `let`-prefixed conclusion (DLMF 15.10.3's Wronskian binds
    `f₁`/`f₂` as local functions before the equality) otherwise truncates at the let's OWN
    `:=` inside `_conclusion`, leaving a bogus `let f₁ : ℂ → ℂ` stub. Each leading line of the
    exact single-line shape `let name : type := value` is consumed as a binding, its NAME then
    whole-token-substituted `(value)` into the remaining body. Fires ONLY when the body's first
    non-space token is `let`; any other conclusion is returned unchanged (byte-identical)."""
    if not re.match(r'^\s*let\s', body):
        return body
    lines = body.split("\n")
    binds = []
    i = 0
    while i < len(lines):
        if not lines[i].strip():                 # skip blank lines before/between bindings
            i += 1
            continue
        m = re.match(r'^\s*let\s+([^\s:]+)\s*:\s*.*?:=\s*(.*\S)\s*$', lines[i])
        if not m:
            break
        binds.append((m.group(1), m.group(2).strip()))
        i += 1
    if not binds:
        return body
    rest = "\n".join(lines[i:])
    for name, val in binds:
        rest = re.sub(r'(?<![\w\'′₀-₉ℓ])' + re.escape(name) + r'(?![\w\'′₀-₉ℓ])',
                      f'({val})', rest)
    return rest


def _inline_lets(body):
    """Inline every single-line `let name : type := value` binding appearing ANYWHERE in a
    conclusion body — not only leading. DLMF 15.6.6/15.6.7 bind the Mellin–Barnes line
    parameter `t := σ + iu` INSIDE the integrand (the `let` sits on its own line after
    `∫ u : ℝ,`), so `_strip_leading_lets` — which fires only when the body's FIRST token is
    `let` — never reaches it and the parser mis-reads `t` as a free variable (`unbound:t`).
    Each exact `let name : type := value` line is consumed and its NAME whole-token-
    substituted `(value)` into all following text (a later let may reference an earlier one);
    any line that is not exactly such a binding is emitted byte-identical. Fires ONLY on lines
    matching the strict shape, so a body with no inline let is returned unchanged."""
    lines = body.split("\n")
    out, binds = [], []
    for line in lines:
        m = re.match(r'^\s*let\s+([^\s:]+)\s*:\s*.*?:=\s*(.*\S)\s*$', line)
        if m:
            val = m.group(2).strip()
            for nm, vv in binds:              # allow a later let to reference an earlier one
                val = re.sub(r'(?<![\w\'′₀-₉ℓ])' + re.escape(nm) + r'(?![\w\'′₀-₉ℓ])',
                             f'({vv})', val)
            binds.append((m.group(1), val))
            continue
        for nm, vv in binds:
            line = re.sub(r'(?<![\w\'′₀-₉ℓ])' + re.escape(nm) + r'(?![\w\'′₀-₉ℓ])',
                          f'({vv})', line)
        out.append(line)
    return "\n".join(out)


def _bracket_end(s, i):
    """Index just past the bracket matching the opener at s[i] (‹(›/‹[›/‹{›), or None if the
    group never closes. Counts (), [], {} together — bracket type is not distinguished, which
    is exactly right for well-formed Lean where they nest properly."""
    if i >= len(s) or s[i] not in "([{":
        return None
    depth = 0
    for j in range(i, len(s)):
        if s[j] in "([{":
            depth += 1
        elif s[j] in ")]}":
            depth -= 1
            if depth == 0:
                return j + 1
    return None


def _inline_struct_lets(body):
    """δ-inline a leading `let NAME : TYPE := { … }` binding whose VALUE is a (possibly
    multi-line) BRACE-delimited structure literal — the shape the single-line `_strip_leading_lets`
    regex cannot consume because the `{ … }` value spans several lines and contains its own field
    `:=`s. The §15.7 Gauss continued-fraction rows (Ch15ContinuedFractions.lean) bind
    `let g : GenContFract ℂ := { h := … , s := … }` before a `Tendsto g.convs …` Prop; without
    this the conclusion truncates at the let's own `:=`, leaving the bogus stub
    `let g : GenContFract ℂ` (the shared `non-equality` skip). Fires ONLY when the value's first
    non-space char after `:=` is `{`; any other let (single-line, non-struct) is left untouched for
    `_strip_leading_lets`/`_inline_lets`. The whole-token substitution matches those helpers."""
    guard = 0
    while guard < 8:
        guard += 1
        m = re.match(r'^\s*let\s+([^\s:]+)\s*:[^\n]*?:=\s*', body)
        if not m:
            break
        i = m.end()
        while i < len(body) and body[i].isspace():
            i += 1
        if i >= len(body) or body[i] != '{':
            break
        j = _bracket_end(body, i)
        if j is None:
            break
        name, val, rest = m.group(1), body[i:j], body[j:]
        rest = re.sub(r'(?<![\w\'′₀-₉ℓ])' + re.escape(name) + r'(?![\w\'′₀-₉ℓ])',
                      f'({val})', rest)
        body = rest
    return body


def _conclusion(sig):
    """The Prop after the binders' colon, up to ':=' or 'by' at depth 0."""
    colon = _colon_index(sig)
    if colon < 0:
        return ""
    body = _inline_lets(_strip_leading_lets(_inline_struct_lets(sig[colon + 1:])))
    # cut at ':=' or ' by ' / '\n  by' at depth 0
    depth = 0
    for j in range(len(body)):
        c = body[j]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and body[j:j + 2] == ":=":
            body = body[:j]
            break
        elif depth == 0 and re.match(r'(?:^|\s)by(?:\s|$)', body[j:j + 4]):
            body = body[:j]
            break
    return " ".join(body.split())


def _const_expr_val(s):
    """Evaluate a CONSTANT hypothesis-bound expression (`-(Real.sqrt 2 / 2)`, `1/2`, …) to an
    mpf through the full parser/evaluator, so an irrational bound (√2/2, π/4, …) becomes a
    numeric sample-filter threshold. Returns None if it fails to parse, contains a free
    variable, or evaluates to a non-real — the bound is then simply not registered (no
    spurious filter), exactly as before this generalisation."""
    s = s.strip()
    try:
        ast = parse(s)
    except Exception:
        return None
    node = ast[1] if ast and ast[0] == "expr" else ast
    fv = set()
    try:
        collect_free(node, fv)
    except Exception:
        return None
    if any(v != IND for v in fv):                 # a bound that still mentions a variable isn't a constant
        return None
    try:
        v = evaluate(node, {})
    except Exception:
        return None
    try:
        if mp.im(v) != 0:                          # complex bound — not an orderable real threshold
            return None
        return mp.mpf(mp.re(v))
    except (TypeError, ValueError):
        return None


def _const_val(s):
    """Parse a small literal constant from a hypothesis (`1`, `1/2`, `1.5`) → mpf, else None."""
    s = s.strip()
    try:
        if "/" in s:
            num, den = s.split("/")
            return mp.mpf(num.strip()) / mp.mpf(den.strip())
        return mp.mpf(s)
    except (ValueError, ZeroDivisionError):
        return None


# ── multi-hypothesis flag accumulation (one variable, several domain binders) ────
# `cons[v]` holds ONE flag, and each grid branch below reads that single flag — so a
# variable carrying TWO domain hypotheses (`hz : z ≠ 0` AND `hz1 : ‖z‖ < 1`, e.g.
# hypergeometric_15_4_1) used to keep only whichever binder the regex loop parsed LAST
# and silently DROP the other. Dropping `‖z‖ < 1` samples the row outside its stated
# disc; dropping `z ≠ 0` samples a punctured-domain row at 0. Fix: keep the single
# `cons[v]` (the grid-SHAPING flag, chosen by restrictiveness rank below, so every
# existing single-flag row is byte-for-byte unchanged) and ALSO record the full flag
# list under `cons['_flags'][v]`; the remaining flags are then enforced as a per-point
# FILTER on the built grid (_filter_extra_flags), so sampling honours the CONJUNCTION
# of all the hypotheses instead of one arbitrary member of it.
_FLAG_RANK = {                    # higher = more grid-shaping / restrictive → becomes cons[v]
    'nonzero': 1,                 # a pure puncture: never a good grid shape, always filterable
    'pos': 2, 'nonneg': 2, 'neg': 2, 'gt1': 2, 'ge1': 2, 'gehalf': 2, 'gtNegHalf': 2,
    'absge1': 2, 'impos': 2, 'imnonneg': 2, 'imneg': 2, 'modulus': 2,
    'odd': 3, 'prime': 3,         # shape flags (value sets), stronger than order relations
    'unit': 4,                    # bounded region grids
    'imaxis': 4,                  # τ.re = 0 — a LINE, stricter than the impos half-plane
    'roothyp': 5,                 # unsatisfiable by any grid → must survive as cons[v]
}
_TUPLE_FLAG_RANK = {'icc': 4, 'enum': 4, 'mod': 4, 'runion': 4,
                    'cdisk': 4, 'trigdisk': 4, 'latdisk': 4}


def _flag_rank(flag):
    if isinstance(flag, tuple) and flag:
        return _TUPLE_FLAG_RANK.get(flag[0], 4)
    return _FLAG_RANK.get(flag, 2)


def _add_flag(cons, v, flag):
    """Record domain `flag` for variable `v`, ACCUMULATING rather than overwriting.

    `cons[v]` keeps the highest-ranked (most grid-shaping) flag — the one the grid
    branches read — and every flag seen for `v` is appended to `cons['_flags'][v]`
    so `_filter_extra_flags` can enforce the others pointwise."""
    seen = cons.setdefault('_flags', {}).setdefault(v, [])
    if flag not in seen:
        seen.append(flag)
    cur = cons.get(v)
    if cur is None or _flag_rank(flag) > _flag_rank(cur):
        cons[v] = flag


def _binders(sig, concl, ctyvars=frozenset()):
    """Return (vars, constraints): vars name->base ('Z','N','R','C','other'); constraints
    name->flag ('pos','nonneg','nonzero','gt1','ge1') parsed from hypothesis binders, so
    sampling stays inside the stated domain (honoring `0 < x` etc. — avoids false branch-
    cut FAILs like log(xy)=logx+logy sampled at negatives).

    `ctyvars`: RCLike-instanced scalar type-variable names of the enclosing file
    (see _cinst_tyvars / _section_binders) — a theorem-head VALUE binder `(a b : 𝕂)`
    over such a 𝕂 is exactly as sampleable as a literal `ℂ` binder, base 'C'.
    Default empty: every existing call path is byte-for-byte unchanged."""
    colon = _colon_index(sig)                 # scan ONLY the binder region — never the
    head = sig[:colon] if colon >= 0 else sig.split(":=")[0]   # conclusion's (n : ℝ) casts
    out, cons = {}, {}
    for grp in re.finditer(r'[({⦃]([^:(){}]+?)\s*:\s*([^(){}]+?)[)}⦄]', head):
        typ = grp.group(2).strip()
        for pat, flag in [(r'^0\s*<\s*(\S+)$', 'pos'), (r'^0\s*≤\s*(\S+)$', 'nonneg'),
                          (r'^(\S+)\s*≠\s*0$', 'nonzero'), (r'^1\s*<\s*(\S+)$', 'gt1'),
                          (r'^1\s*≤\s*(\S+)$', 'ge1'), (r'^(\S+)\s*<\s*0$', 'neg'),
                          (r'^\|(\S+)\|\s*≤\s*1$', 'unit'), (r'^\|(\S+)\|\s*<\s*1$', 'unit'),
                          (r'^‖(\S+)‖\s*≤\s*1$', 'unit'), (r'^‖(\S+)‖\s*<\s*1$', 'unit'),  # ‖z‖<1 disk
                          (r'^(\S+)\s*\^\s*2\s*<\s*1$', 'unit'),     # k² < 1 ⇒ |k| < 1 (Jacobi modulus)
                          # k² ≤ 1 (closed modulus range, DLMF §19.9 incomplete-integral
                          # bounds) — same interior 'unit' grid; ADDITIVE: sampling stays
                          # inside the stated hypothesis (was: k unflagged → drawn at
                          # |k| > 1 where mp.ellipe(φ, k²) is complex, a fabricated FAIL
                          # on the proven sin φ ≤ E(φ,k))
                          (r'^(\S+)\s*\^\s*2\s*≤\s*1$', 'unit'),
                          (r'^1\s*≤\s*(\S+)\s*\^\s*2$', 'absge1'),   # |x| ≥ 1 (x² ≥ 1)
                          (r'^-\(1 / 2\)\s*<\s*(\S+)$', 'gtNegHalf'),  # ν > −1/2 (Bessel-K order)
                          (r'^1 / 2\s*≤\s*(\S+)$', 'gehalf'),          # ν ≥ 1/2 (Struve Poisson rep)
                          (r'^0\s*<\s*(\S+)\.im$', 'impos'),           # 0 < τ.im (upper half-plane)
                          # `hre : τ.re = 0` — the variable is confined to the IMAGINARY AXIS
                          # (theta_20_11_5's rectangular-lattice hypothesis, DLMF 20.11.5).
                          # Unfenced, τ drew the whole upper-half-plane grid, where the elliptic
                          # modulus k(τ) leaves the unit disc and Mathlib's `₂F₁ … (k τ)²` is its
                          # junk 0 while θ₃² is not — a sample OUTSIDE the stated hypothesis.
                          (r'^(\S+)\.re\s*=\s*0$', 'imaxis'),
                          # 0 ≤ z.im (CLOSED upper half-plane, DLMF §15.10(ii)'s `him` on the
                          # printed-phase connection rows 15.10.19/20/25/26/29–36): sampled on
                          # the open-half-plane grid, a strict subset of the stated hypothesis.
                          # Without it the flag landed on the junk key cons['z.im'] and z drew
                          # the whole-plane grid — Im z < 0 points where the conjugate phase
                          # makes the printed display genuinely fail (worst ≈ 1.0–1.9 fabricated
                          # on kernel-proven rows). ADDITIVE.
                          (r'^0\s*≤\s*(\S+)\.im$', 'imnonneg'),
                          (r'^(\S+)\.im\s*<\s*0$', 'imneg'),           # z.im < 0 (lower half-plane)
                          (r'^(\S+)\.Prime$', 'prime'), (r'^Nat\.Prime\s+(\S+)$', 'prime')]:
            mm = re.match(pat, typ)
            if mm:
                v = mm.group(1)
                # a SHAPE flag (odd/prime/enum/mod — parsed elsewhere in this same loop,
                # e.g. `Odd n`) restricts which VALUES are admissible and must not be
                # clobbered by a later plain order-relation hypothesis on the same
                # variable (e.g. `hlt : 1 < n` alongside `h_odd : Odd n`, DLMF 24.2 odd
                # Bernoulli vanishing): textual hypothesis order would otherwise let
                # whichever binder is parsed last silently overwrite `odd` with `gt1`,
                # so the sampler draws n=2 — OUTSIDE the Odd hypothesis — and fabricates
                # a "counterexample" B_2 ≠ 0 that is really just an unfenced sample.
                # Record the order relation as a `_lower`/`_upper` bound instead, so it
                # COMPOSES with the shape grid (odd ∩ >1) rather than replacing it.
                if cons.get(v) in ("odd", "prime") or \
                        (isinstance(cons.get(v), tuple) and cons[v] and cons[v][0] in ("enum", "mod")):
                    if flag in ("gt1", "pos"):
                        cons.setdefault('_lower', {}).setdefault(v, (mp.mpf(1), True))
                    elif flag in ("ge1", "nonneg"):
                        cons.setdefault('_lower', {}).setdefault(v, (mp.mpf(1), False))
                    elif flag == "neg":
                        cons.setdefault('_upper', {}).setdefault(v, (mp.mpf(0), True))
                    elif flag == "nonzero":
                        pass          # odd/prime/enum/mod values are already ≠ 0 generically
                else:
                    _add_flag(cons, v, flag)   # ACCUMULATE (was: last binder parsed wins)
        # Carlson symmetric-integral domain predicate `CarlsonRFDomain x y z`
        # (0 ≤ each coordinate, pairwise sums > 0 — DLMF §19.16(i)): sample every
        # coordinate on the strictly-positive grid, a SUBSET of the stated domain.
        # Without this rule the Prop-valued hypothesis was silently dropped and
        # x,y,z drew negative default-grid values, false-FAILing the proven
        # 19.26.18 duplication rows (worst=0.5336 traced to elliprf(0.3,−0.8,2.4)
        # going complex). ADDITIVE: sampling restricted to the hypothesis domain.
        mm = re.match(r'^(?:[\w.]*\.)?CarlsonRFDomain\s+(\S+)\s+(\S+)\s+(\S+)$', typ)
        if mm:
            for v in mm.groups():
                cons.setdefault(v, 'pos')
        # Implicit ROOT hypothesis `h : <fn> … v = 0` — the sampled variable is
        # constrained to be a zero of a special function (abs_lt_one_of_legendre_zero:
        # `hx : legendre n x = 0`). No grid can honor that implicit equation, and
        # silently dropping it samples v FREELY — fabricating a refutation of a true
        # theorem (margin=0.5833 traced to scoring x=2.4 as a "Legendre root"). Flag
        # the variable so the sweep SKIPS the row honestly instead of scoring it.
        mm = re.match(r'^[\w.]*[A-Za-z]\w*(?:\s+\S+)*\s+([A-Za-zα-ω]\w*)\s*=\s*0$', typ)
        if mm and mm.group(1) not in cons:
            cons[mm.group(1)] = 'roothyp'
        # MEMBERSHIP-form root hypothesis `hx : x ∈ P.roots` (Polynomial.roots multiset —
        # orthogonalPoly_roots_mem_Ioo, DLMF §18.2(vi)): the same implicit-equation shape as
        # the `f … v = 0` form above in `∈`-notation. No grid can honor it; silently dropping
        # it sampled x FREELY over the ℝ grid against the abstract bundle witness (lo:margin
        # = 1.471 fabricated on a true theorem). Flag 'roothyp' → honest SKIP, never scored.
        mm = re.match(r'^([A-Za-zα-ωΑ-Ω]\w*)\s*∈\s*[\w.\'′]+\.roots$', typ)
        if mm and mm.group(1) not in cons:
            cons[mm.group(1)] = 'roothyp'
        # prefix-`re` spelling of real-part positivity `0 < re s` (file has `open Complex`, so
        # `s.re` prints as `re s` — dirichletEta_tendsto_eq's DLMF 25.2.3 abscissa hypothesis
        # `0 < re s`): same constraint the dot form `0 < s.re` records under cons['s.re'] via
        # the plain 'pos' regex above, driving the SAMPLES_C_REPOS in-half-plane grid. Without
        # it s drew the default ℂ grid (Re s = −0.7 included) where the alternating partial
        # sums genuinely diverge — a fabricated FAIL outside the stated domain. ADDITIVE.
        mm = re.match(r'^0\s*<\s*re\s+([A-Za-zα-ωΑ-Ω]\w*)$', typ)
        if mm:
            cons.setdefault(mm.group(1) + '.re', 'pos')
        # general norm-disk hypothesis `‖v‖ < c` / `‖v‖ ≤ c` (or `|v| < c`), c ≠ 1 → sample inside
        # the radius-c disk (the convergence region of a power series ∑ aₖ vᵏ of radius c). c = 1
        # is already handled as the `unit` flag above; this generalises it (e.g. `‖z‖ < 2` for the
        # log Γ(1+z) / 1/Γ Taylor series, whose default complex grid drifts outside the disk → FAIL).
        mm = re.match(r'^[‖|](\S+?)[‖|]\s*[<≤]\s*(\d+(?:\.\d+)?|\d+\s*/\s*\d+)$', typ)
        if mm and _const_val(mm.group(2)) is not None and _const_val(mm.group(2)) != 1:
            _add_flag(cons, mm.group(1), ('cdisk', _const_val(mm.group(2))))
        # OFF-CENTER norm-disk hypothesis `‖v − k‖ < r` / `‖k − v‖ < r` (k, r numeric literals) —
        # e.g. the `z = 1` connection-formula lens `‖z − 1‖ < 1` (DLMF 15.10.21): a per-sample
        # filter that DROPS any point outside the stated disk about k (there the ₂F₁(…;1−z)
        # series diverges and the claim says nothing), never scores one. ADDITIVE: sampling is
        # restricted to the stated hypothesis domain only; no grid, tolerance or scoring change.
        mm = re.match(r'^[‖|]\s*([A-Za-zα-ω]\w*)\s*-\s*(\d+(?:\.\d+)?)\s*[‖|]\s*(<|≤)'
                      r'\s*(\d+(?:\.\d+)?|\d+\s*/\s*\d+)$', typ)
        if mm and _const_val(mm.group(4)) is not None:
            cons.setdefault('_pairs', []).append(
                ['normdisk', mm.group(1), _const_val(mm.group(2)),
                 _const_val(mm.group(4)), mm.group(3) == '<'])
        mm = re.match(r'^[‖|]\s*(\d+(?:\.\d+)?)\s*-\s*([A-Za-zα-ω]\w*)\s*[‖|]\s*(<|≤)'
                      r'\s*(\d+(?:\.\d+)?|\d+\s*/\s*\d+)$', typ)
        if mm and _const_val(mm.group(4)) is not None:
            cons.setdefault('_pairs', []).append(
                ['normdisk', mm.group(2), _const_val(mm.group(1)),
                 _const_val(mm.group(4)), mm.group(3) == '<'])
        # pairwise hypotheses (`hm : m.Coprime n`, `h : n ≠ m`) — recorded under '_pairs'
        # and honored as a per-sample-point filter, never matched as a variable flag
        mm = re.match(r'^(\S+)\.Coprime\s+(\S+)$', typ) or \
             re.match(r'^Nat\.Coprime\s+(\S+)\s+(\S+)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(['coprime', mm.group(1), mm.group(2)])
        mm = re.match(r'^(\S+)\s*≠\s*(\S+)$', typ)        # n ≠ m (two variables, not ≠ 0)
        if mm and mm.group(2) != '0':
            cons.setdefault('_pairs', []).append(['distinct', mm.group(1), mm.group(2)])
        # divisibility hypotheses `h : p ∣ n` / `h : ¬ p ∣ n` (e.g. the Ramanujan-sum
        # prime dichotomy c_p(n) = p−1 vs −1, DLMF 27.10) — honored as per-sample
        # filters exactly like Coprime: a sample violating the stated (non-)divisibility
        # is OUTSIDE the hypothesis, so scoring it would fabricate a counterexample,
        # not find a DLMF discrepancy. Additive: nothing loosened.
        mm = re.match(r'^(¬\s*)?([A-Za-zα-ω]\w*|\d+)\s*∣\s*([A-Za-zα-ω]\w*|\d+)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(
                ['notdvd' if mm.group(1) else 'dvd', mm.group(2), mm.group(3)])
        # disjunctive finite-value hypothesis `hm : m = 2 ∨ m = 3 ∨ m = 4` (all disjuncts
        # equate the SAME variable to an integer literal — the DLMF 20.11.9 combined-theta
        # index constraint) → sample m from EXACTLY that value set, recorded ('enum', vals).
        # Without it the default ℕ grid draws m ∉ {2,3,4}, where the Lean def's junk branch
        # (`thetaIdx _ = θ₁`) makes the sampled statement about a DIFFERENT function than
        # the hypothesis-guarded claim — a spurious FAIL, not a DLMF discrepancy. Sampling
        # inside the stated hypothesis only; nothing loosened.
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*=\s*(\d+)(?:\s*∨\s*\1\s*=\s*\d+)+$', typ)
        if mm:
            _add_flag(cons, mm.group(1),
                      ('enum', tuple(int(x) for x in re.findall(r'=\s*(\d+)', typ))))
        mm = re.match(r'^(\S+)\s*\+\s*(\S+)\s*<\s*(\S+)$', typ)   # triangle-violation a+b<c
        if mm:
            cons.setdefault('_pairs', []).append(['sumlt', mm.group(1), mm.group(2), mm.group(3)])
        # Complex diamond-domain hypothesis
        # `|β.re| + |β.im| ≤ ℓ` (DLMF 20.10.4–5). Sample strictly inside the
        # closed diamond: the boundary is part of the theorem but direct theta
        # quadrature at t → 0 is numerically ill-conditioned there, while
        # interior samples still lie in the stated domain.
        mm = re.match(
            r'^\|([A-Za-zα-ω]\w*)\.re\|\s*\+\s*'
            r'\|\1\.im\|\s*≤\s*([A-Za-zα-ωℓ]\w*)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(
                ['complex_l1_lt', mm.group(1), mm.group(2)])
        # Theta Fourier/Lambert series strips: |Im z| < Im τ and
        # |Im z| < Im τ / 2 (DLMF 20.5.10--13).  Retain the relation
        # jointly so the generic complex grids never score divergent
        # off-strip series.
        mm = re.match(
            r'^\|([^\W\d]\w*)\.im\|\s*<\s*([^\W\d]\w*)\.im'
            r'(?:\s*/\s*(2))?$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(
                ['compleximstrip', mm.group(1), mm.group(2),
                 mp.mpf(mm.group(3) or 1)])
        # difference-positivity hypotheses `0 < c − a − b` (⟺ a + b < c, e.g. Gauss's theorem
        # DLMF 15.4.20 convergence condition) and `0 < b − a` (⟺ a < b) — recorded as the
        # EXISTING sumlt/ltpair per-sample filters, so samples stay inside the stated domain
        # (outside it ₂F₁(a,b;c;x) genuinely diverges as x → 1⁻ and a "FAIL" there would be
        # a fabricated counterexample, not a DLMF discrepancy). ADDITIVE: the hypothesis is
        # honored exactly as stated; nothing loosened.
        mm = re.match(r'^0\s*<\s*([A-Za-zα-ω]\w*)\s*-\s*([A-Za-zα-ω]\w*)\s*-\s*([A-Za-zα-ω]\w*)$',
                      typ)
        if mm:
            cons.setdefault('_pairs', []).append(['sumlt', mm.group(2), mm.group(3), mm.group(1)])
        mm = re.match(r'^0\s*<\s*([A-Za-zα-ω]\w*)\s*-\s*([A-Za-zα-ω]\w*)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(['ltpair', mm.group(2), mm.group(1)])
        # convergence/domain hypothesis `c < v₁+v₂+…+vₙ` (e.g. `3 < a+b+c+d` for the Ramanujan
        # integral) — sample only where the sum exceeds c, so the integral actually converges.
        mm = re.match(r'^(\d+\s*/\s*\d+|\d+\.\d+|\d+)\s*<\s*([A-Za-zα-ω][\w\s+]*\+[\w\s+]*)$', typ)
        if mm and _const_val(mm.group(1)) is not None:
            terms = [t.strip() for t in mm.group(2).split('+')]
            if all(re.fullmatch(r'[A-Za-zα-ω]\w*', t) for t in terms):
                cons.setdefault('_pairs', []).append(['sumgt', terms, _const_val(mm.group(1))])
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*≤\s*([A-Za-zα-ω]\w*)$', typ)   # a ≤ b (two vars)
        if mm:
            cons.setdefault('_pairs', []).append(['lepair', mm.group(1), mm.group(2)])
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*<\s*([A-Za-zα-ω]\w*)$', typ)    # a < b (two vars)
        if mm:
            cons.setdefault('_pairs', []).append(['ltpair', mm.group(1), mm.group(2)])
        # affine ℕ-inequality hypothesis `h : a + k ≤ b` (k an integer literal) — e.g. the
        # Krawtchouk three-term recurrence's `hN : n + 2 ≤ N` (DLMF 18.22.3): a sample with
        # n + 2 > N is OUTSIDE the stated hypothesis, so it is dropped per-sample in
        # _pairs_ok, never scored. Additive: the hypothesis is honored exactly as stated;
        # nothing loosened.
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*\+\s*(\d+)\s*≤\s*([A-Za-zα-ω]\w*)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(
                ['lepairoff', mm.group(1), int(mm.group(2)), mm.group(3)])
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*\+\s*(\d+)\s*<\s*([A-Za-zα-ω]\w*)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(
                ['ltpairoff', mm.group(1), int(mm.group(2)), mm.group(3)])
        # affine REAL-shift hypothesis `h : v < w + k` / `v ≤ w + k` (k a numeric literal) —
        # e.g. the `z = 1` connection formula's `hac : c < a + 1` (DLMF 15.10.21). Same
        # per-sample discipline as `ltpairoff`: a sample violating it is OUTSIDE the stated
        # hypothesis and is dropped in _pairs_ok, never scored. ADDITIVE: the hypothesis is
        # honored exactly as stated; nothing loosened, no tolerance or scoring change.
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*(<|≤)\s*([A-Za-zα-ω]\w*)\s*\+\s*'
                      r'(\d+(?:\.\d+)?|\d+\s*/\s*\d+)$', typ)
        if mm and _const_val(mm.group(4)) is not None:
            cons.setdefault('_pairs', []).append(
                ['ltpluspair', mm.group(1), mm.group(3), _const_val(mm.group(4)),
                 mm.group(2) == '<'])
        # ∀-quantified POSITIVITY hypothesis on an abstract function binder — `ha : ∀ k,
        # 0 < a k` (the DLMF 5.13.5 de Branges–Wilson parameters a : Fin 4 → ℝ): recorded
        # under '_absfnpos' so the absfnR sampler draws only POSITIVE pointwise callables.
        # Without it 2 of the 3 default ABSFN_R samples violate the hypothesis (where the
        # identity is genuinely false — residue terms appear for Re aₖ ≤ 0) and the sweep
        # would fabricate a FAIL on a true statement. Sampling restricted to the stated
        # hypothesis domain only; nothing loosened.
        mm = re.match(r'^∀\s*\(?\s*([A-Za-zα-ω]\w*)(?:\s*:\s*[^,()]+)?\s*\)?\s*,\s*'
                      r'0\s*<\s*([A-Za-zα-ω]\w*)\s+\1$', typ)
        if mm:
            ap = cons.setdefault('_absfnpos', [])
            if mm.group(2) not in ap:
                ap.append(mm.group(2))
        mm = re.match(r'^Odd\s+(\S+)$', typ)             # `hn : Odd n` → odd-integer grid (Jacobi)
        if mm:
            _add_flag(cons, mm.group(1), 'odd')
        # residue hypothesis `hm : m % c = r` (e.g. `m % 4 = 1`, Jacobi reciprocity DLMF
        # 27.9.3) → sample m ONLY from the residue class {r, r+c, r+2c, …}. Without this
        # the binder is classified 'other' and m is drawn from the unconstrained grid,
        # where the claim says nothing (J(3|7)=-1 ≠ J(7|3)=+1 is OUTSIDE the m≡1 (mod 4)
        # hypothesis — a fabricated counterexample, not a DLMF discrepancy). Additive:
        # restricts sampling to the stated hypothesis domain; nothing loosened.
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*%\s*(\d+)\s*=\s*(\d+)$', typ)
        if mm:
            _add_flag(cons, mm.group(1), ('mod', int(mm.group(2)), int(mm.group(3))))
        mm = re.match(r'^(\S+)\s*\+\s*(\S+)\s*\+\s*(\S+)\s*≠\s*0$', typ)   # 3j selection rule
        if mm:
            cons.setdefault('_pairs', []).append(['sumnonzero', mm.group(1), mm.group(2), mm.group(3)])
        mm = re.match(r'^(\S+)\s*\+\s*(\S+)\s*\+\s*(\S+)\s*=\s*0$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(['sumzero', mm.group(1), mm.group(2), mm.group(3)])
        zm = re.match(r'^ZMod\s+(\S+)$', typ)          # a : ZMod k — element + its modulus k
        if zm:
            cons.setdefault(zm.group(1), 'modulus')    # k sampled from cyclic moduli
            for nm in grp.group(1).split():            # element → its modulus, so a⁻¹ can be
                cons.setdefault('_zmodmod', {})[nm] = zm.group(1)   # the MODULAR inverse mod k
        # unit hypothesis `ha : IsUnit a` on a ZMod binder — a must be invertible mod k
        # (gcd(a,k)=1); a sample violating it is OUT of the stated domain (Lean's a⁻¹ is
        # a junk value there), so it is filtered per-sample like Coprime, never scored.
        mm = re.match(r'^IsUnit\s+(\S+)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(['isunit', mm.group(1)])
        # NON-unit hypothesis `ha : ¬ IsUnit a` (gcd(a,k) > 1 — DLMF 27.8.4's "(n,k) > 1"):
        # dual per-sample filter; a sample that IS a unit is outside the stated hypothesis
        # (the claim says nothing there), so it is dropped, never scored.
        mm = re.match(r'^¬\s*IsUnit\s+(\S+)$', typ)
        if mm:
            cons.setdefault('_pairs', []).append(['notunit', mm.group(1)])
        # primitivity hypothesis `he : e.IsPrimitive` on an additive-character binder
        # (the DLMF §27.8 Gauss-sum magnitude surface, GaussSumDirichlet.lean): honored
        # per sample — a kernel index n with gcd(n, k) > 1 gives a NON-primitive ψₙ,
        # outside the stated hypothesis, so that sample is dropped, never scored.
        mm = re.match(r'^(\S+)\.IsPrimitive$', typ) or \
             re.match(r'^AddChar\.IsPrimitive\s+(\S+)$', typ)
        if mm:
            cons.setdefault('_primchar', []).append(mm.group(1))
        # ∀-quantified Dirichlet character `χ : DirichletCharacter ℂ k` (DLMF §27.8) —
        # sampled by INSTANTIATION from the concrete cyclic-modulus character model
        # (ob._dirichlet_char_sample, anchored in oracle_bindings.verify() to the 27.8.1–
        # 27.8.4 defining relations): χ's grid is a character INDEX t, resolved per sample
        # to the t-th character mod the sampled k. Records χ → k so the sample loop can
        # couple them; k joins the cyclic-moduli grid.
        dch = re.match(r'^DirichletCharacter\s+ℂ\s+(\S+)$', typ)
        if dch:
            cons.setdefault(dch.group(1), 'modulus')   # k drawn from the cyclic-moduli grid
            for nm in grp.group(1).split():
                cons.setdefault('_dirchmod', {})[nm] = dch.group(1)
        # ∀-quantified completely multiplicative arithmetic function: a hypothesis binder
        # `(hf : IsCompletelyMultiplicative f)` (DLMF 27.3.9: f(1)=1 ∧ f(mn)=f(m)f(n) for
        # ALL m,n) marks `f` as an abstract function the oracle cannot sample as a scalar
        # (the sweep skipped e.g. `apply_pow`, DLMF 27.3.10, as `unbound:f`). Like the
        # DirichletCharacter instantiation above and the Mathieu/Airy ∀-witnesses in
        # oracle_bindings.py, instantiate f at a CANONICAL registered witness: the
        # Liouville function λ(n) = (−1)^Ω(n) (DLMF 27.2), which satisfies the hypothesis
        # exactly (λ(0)=0 junk also matches Lean's `ArithmeticFunction` f(0)=0). The
        # hypothesis is anchored numerically in ob.verify() before the witness is trusted.
        # Sound as a refutation oracle: a numeric counterexample at the witness disproves
        # the ∀-statement; passing is evidence. Keyed on the HYPOTHESIS TYPE, never on the
        # variable's name — a bare `f` without this hypothesis keeps its honest skip.
        mm = re.match(r'^(?:FLMF\.)?(?:NumberTheory\.)?IsCompletelyMultiplicative\s+(\S+)$', typ)
        if mm:
            cons.setdefault('_fnwitness', {})[mm.group(1)] = 'liouville'
        # ∀-quantified MULTIPLICATIVE arithmetic function — `hf : IsMultiplicative f`
        # (Mathlib `ArithmeticFunction.IsMultiplicative`, prefix or dot form; DLMF 27.3.1:
        # f(1)=1 ∧ f(mn)=f(m)f(n) for coprime m,n). Same witness mechanism as above, but
        # this hypothesis is WEAKER than 27.3.9, so f is instantiated at EVERY member of
        # ob.MULTIPLICATIVE_WITNESSES (φ = totient — multiplicative but NOT completely,
        # the regime distinguishing 27.3.2 from 27.3.10 — and μ = moebius, which
        # exercises the vanishing branch): a tuple-valued witness makes the sweep check
        # all members (FAIL if any refutes; PASS only if every member's sweep passes).
        # Each witness's hypothesis clauses and its 27.3.2 product are anchored in
        # ob.verify(). Keyed on the hypothesis TYPE, never the variable's name; the
        # anchored `^` keeps IsCompletelyMultiplicative (above) on its own witness.
        mm = re.match(r'^(?:ArithmeticFunction\.)?IsMultiplicative\s+([A-Za-zα-ω]\w*)$', typ) or \
             re.match(r'^([A-Za-zα-ω]\w*)\.IsMultiplicative$', typ)
        if mm:
            cons.setdefault('_fnwitness', {})[mm.group(1)] = ob.MULTIPLICATIVE_WITNESSES
        # ∀-quantified Christoffel–Darboux system — `H : IsCDSystem p h a x y`
        # (ChristoffelDarboux.lean; DLMF 18.2.12): p is an abstract orthogonal-polynomial
        # family, h its squared norms, a the kₖ/(hₖ kₖ₊₁) coefficients, constrained only
        # by the base/step telescoping hypothesis (recurrence + orthogonality). The
        # sweep skipped these rows as `unbound:a` — instantiate the triple COHERENTLY
        # at the canonical Chebyshev-T witness (ob cdChebP/cdChebH/cdChebA: pₖ = Tₖ,
        # h₀ = π, hₖ≥₁ = π/2, aₖ = 1/π — DLMF Table 18.3.1), whose hypothesis clauses
        # and witness data are anchored in ob.verify() before the sweep trusts it.
        # x, y are the row's own real arguments (file-level IMPLICIT binders the head
        # scan cannot type), so register them for the real grid here. Keyed on the
        # hypothesis TYPE, never on variable names. Sound as a refutation oracle: a
        # numeric counterexample at the witness disproves the ∀-statement; passing is
        # evidence.
        mm = re.match(r'^(?:FLMF\.)?(?:Functions\.)?(?:OrthogonalPolynomials\.)?IsCDSystem\s+'
                      r'([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)\s+'
                      r'([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)$', typ)
        if mm:
            w = cons.setdefault('_fnwitness', {})
            w[mm.group(1)], w[mm.group(2)], w[mm.group(3)] = 'cdChebP', 'cdChebH', 'cdChebA'
            for nm in (mm.group(4), mm.group(5)):
                out.setdefault(nm, "R")
        # ∀-quantified CONFLUENT Christoffel–Darboux system — `H : IsConfluentCDSystem
        # p h D x` (ChristoffelDarboux.lean; DLMF 18.2.13, the y → x diagonal of
        # 18.2.12): `D k` abstracts the derivative cross term aₖ·(p′ₖ₊₁(x)pₖ(x) −
        # p′ₖ(x)pₖ₊₁(x)), so unlike the (p, h, a) triple above the witness for D
        # depends on the row's own point x. The sweep skipped this row as `unbound:x`
        # — instantiate COHERENTLY at the SAME Chebyshev-T witness (pₖ = Tₖ, h₀ = π,
        # hₖ≥₁ = π/2, aₖ = 1/π; exact T′ₙ = n·Uₙ₋₁, DLMF 18.9.21). D's witness spec
        # 'cdChebD@x' makes _subst_fn_witness rewrite the APPLICATION `D n` to
        # `cdChebD n x`, threading the sampled x as a trailing argument. Every
        # hypothesis clause is anchored in ob.verify() before the sweep trusts the
        # witness. Keyed on the hypothesis TYPE, never on variable names; sound as a
        # refutation oracle exactly like the 18.2.12 branch above.
        mm = re.match(r'^(?:FLMF\.)?(?:Functions\.)?(?:OrthogonalPolynomials\.)?IsConfluentCDSystem\s+'
                      r'([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)\s+'
                      r'([A-Za-zα-ω]\w*)$', typ)
        if mm:
            w = cons.setdefault('_fnwitness', {})
            w[mm.group(1)], w[mm.group(2)] = 'cdChebP', 'cdChebH'
            w[mm.group(3)] = 'cdChebD@' + mm.group(4)
            out.setdefault(mm.group(4), "R")
        # ∀-quantified Stirling asymptotic-coefficient sequences — a hypothesis binder
        # `h : SatisfiesStirlingRec a g` (Ch5Asymptotics.lean; DLMF 5.11.5/5.11.6) pins the
        # auxiliary aₖ and the Stirling coefficients gₖ UNIQUELY by the recurrence, so the
        # abstract sequences (skipped as `unbound:a`/`unbound:g`) are instantiated at their
        # canonical solution: g → stirlingRecG, a → stirlingRecA, synthesized from the
        # recurrence in oracle_bindings and anchored in ob.verify(). Keyed on the hypothesis
        # TYPE, never the variable names; sound as a refutation oracle (the recurrence has a
        # unique solution, so a numeric counterexample disproves the ∀-statement).
        # ── hypothesis-CARRIER ladder (`h : FuchsRelation a γ q α β`, DLMF 31.14.2;
        # `h : HeunHalfOddIntegerExponents m α β γ δ ε`, 31.8.1) ──  A row quantified under
        # a named Prop carrier is FALSE at a freely sampled point — the carrier is exactly
        # what pins the binders — so the sweep must build its samples INSIDE the hypothesis.
        # Record the carrier and its ARGUMENT LIST; `sweep_eq` then drops the binders the
        # display determines from the grid and computes them per sample from
        # `ob.CARRIER_PINS` (each an independent transcription of the DLMF display,
        # anchored in ob.verify() by a decorrelated route). Keyed on the hypothesis TYPE
        # and its exact arity, never on a theorem name; an unregistered carrier or a
        # duplicated/derived argument records nothing and the row keeps its honest skip.
        mm = re.fullmatch(r'(?:FLMF\.)?(?:Heun\.)?([A-Z]\w*)'
                          r'((?:\s+[A-Za-zα-ωΑ-Ω]\w*)+)', typ)
        if mm and mm.group(1) in getattr(ob, 'CARRIER_PINS', {}) and '_carrier' not in cons:
            _cargs = mm.group(2).split()
            if len(_cargs) == len(ob.CARRIER_PINS[mm.group(1)]["params"]) \
                    and len(set(_cargs)) == len(_cargs):
                cons['_carrier'] = [mm.group(1), _cargs]
        mm = re.match(r'^(?:FLMF\.)?(?:Functions\.)?(?:Gamma\.)?SatisfiesStirlingRec\s+'
                      r'([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)$', typ)
        if mm:
            w = cons.setdefault('_fnwitness', {})
            w[mm.group(1)] = 'stirlingRecA'
            w[mm.group(2)] = 'stirlingRecG'
        # ∀-quantified Gamma-ratio coefficient sequences — `hG : IsRatioCoeffs G a b`
        # (DLMF 5.11.13) and `hH : IsSymRatioCoeffs H a b` (DLMF 5.11.14). Each abstract
        # sequence (skipped `unbound:G`/`unbound:H`) is a FUNCTION of the row's own real
        # parameters a, b, so it is threaded via the multi-`@` witness spec
        # `ratioCoeffG@a@b` / `symRatioCoeffH@a@b` (_subst_fn_witness rewrites `G n` →
        # `ratioCoeffG n a b`), instantiating at the sequence synthesized from the DEFINING
        # asymptotic relation in oracle_bindings (anchored in ob.verify()). a, b join the
        # real grid. Keyed on the hypothesis TYPE; sound as a refutation oracle (the
        # asymptotic relation determines the coefficients uniquely).
        mm = re.match(r'^(?:FLMF\.)?(?:Functions\.)?(?:Gamma\.)?IsRatioCoeffs\s+'
                      r'([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)$', typ)
        if mm:
            cons.setdefault('_fnwitness', {})[mm.group(1)] = 'ratioCoeffG@' + mm.group(2) + '@' + mm.group(3)
            out.setdefault(mm.group(2), "R")
            out.setdefault(mm.group(3), "R")
        mm = re.match(r'^(?:FLMF\.)?(?:Functions\.)?(?:Gamma\.)?IsSymRatioCoeffs\s+'
                      r'([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)\s+([A-Za-zα-ω]\w*)$', typ)
        if mm:
            cons.setdefault('_fnwitness', {})[mm.group(1)] = 'symRatioCoeffH@' + mm.group(2) + '@' + mm.group(3)
            out.setdefault(mm.group(2), "R")
            out.setdefault(mm.group(3), "R")
        # upper-bound hypotheses `v < c` / `v ≤ c` (constant c) — stored SEPARATELY from the
        # lower-bound flag (which would otherwise overwrite it), so e.g. `0 < s` ∧ `s < 1` keeps
        # the `pos` grid but filters it to (0,1); avoids sampling s at 1.7/2.4 (a false ineq FAIL).
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*(<|≤)\s*(\d+\s*/\s*\d+|\d+\.\d+|\d+)$', typ)
        if mm and _const_val(mm.group(3)) is not None and _const_val(mm.group(3)) > 0:
            cons.setdefault('_upper', {})[mm.group(1)] = (_const_val(mm.group(3)), mm.group(2) == '<')
        # general CONSTANT-EXPRESSION bound hypotheses, where one side is a lone variable and the
        # other is an arbitrary constant expression the evaluator can reduce (an irrational
        # bound `-(Real.sqrt 2 / 2) < x`, `π / 4 ≤ y`, …). Evaluate the constant side to a float
        # and register a numeric lower/upper sample-filter threshold, so x is sampled only inside
        # the stated domain (the named-flag table above has no entry for an irrational bound, so
        # without this x would be drawn below the bound where the claim can be genuinely false).
        mm = re.match(r'^(.+?)\s*(<|≤)\s*([A-Za-zα-ω]\w*)$', typ)   # const-expr (</≤) var → lower bound
        if mm and not re.fullmatch(r'[A-Za-zα-ω]\w*', mm.group(1).strip()):
            cv = _const_expr_val(mm.group(1))
            if cv is not None:
                cons.setdefault('_lower', {})[mm.group(3)] = (cv, mm.group(2) == '<')
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*(<|≤)\s*(.+)$', typ)    # var (</≤) const-expr → upper bound
        if mm and not re.fullmatch(r'[A-Za-zα-ω]\w*', mm.group(3).strip()) \
                and not re.fullmatch(r'\d+\s*/\s*\d+|\d+\.\d+|\d+', mm.group(3).strip()):
            cv = _const_expr_val(mm.group(3))
            if cv is not None:
                cons.setdefault('_upper', {}).setdefault(mm.group(1), (cv, mm.group(2) == '<'))
        # single-binder REAL-PART upper bound `z.re < c` / `z.re ≤ c` (c a positive literal) —
        # DLMF 15.8.22/15.8.23's Re z < 1/2 validity strip for the √-argument quadratic
        # transformations. The displayed-arg slit guards (InPrincipalGaussDomain [z, 4√(1−1/z)/…²])
        # are NECESSARY but NOT sufficient: a point with Re z ≥ 1/2 can have BOTH z and the
        # transformed argument off the cut [1,∞) yet sit on the WRONG branch component, where the
        # analytically-continued ₂F₁ and the RHS composition genuinely differ (measured worst ≈ 1.5
        # at, e.g., z = 2 − 1.3i). Honored as a per-sample DROP filter ('reupper') PLUS a curated
        # Re z < c complex grid (the default ℂ grid is almost entirely Re ≥ 1/2, so the row would
        # otherwise starve). ADDITIVE: sampling restricted to the stated hypothesis only.
        mm = re.match(r'^([A-Za-zα-ω]\w*)\s*\.\s*re\s*(<|≤)\s*(\d+\s*/\s*\d+|\d+\.\d+|\d+)$', typ)
        if mm and _const_val(mm.group(3)) is not None:
            _rv, _rstrict = _const_val(mm.group(3)), mm.group(2) == '<'
            cons.setdefault('_pairs', []).append(['reupper', mm.group(1), _rv, _rstrict])
            cons[mm.group(1) + '.re'] = ('reupper', _rv, _rstrict)
        # relational lower bound `c ≤ v₁ − v₂` (e.g. `1 ≤ b − a`) — a per-sample filter so the
        # pair (v₁,v₂) is sampled with v₁ − v₂ ≥ c (the `ge1` regex misses it: spaces around `-`).
        mm = re.match(r'^(\d+\s*/\s*\d+|\d+\.\d+|\d+)\s*≤\s*([A-Za-zα-ω]\w*)\s*-\s*([A-Za-zα-ω]\w*)$', typ)
        if mm and _const_val(mm.group(1)) is not None:
            cons.setdefault('_pairs', []).append(['ge_diff', mm.group(2), mm.group(3), _const_val(mm.group(1))])
        # a genuinely `Fin q`-parametrized complex vector binder `(A B : Fin q → ℂ)`
        # (DLMF 16.17.1/16.18.1's Meijer-G / ₚFq parameter tuples, meijerG_eq_pFq):
        # tagged 'finvecC' with its CARDINALITY variable ('_finvecdim'), so the sweep
        # can sample q and then construct A/B as concrete `.q`-tagged callables
        # (see sweep_eq) — never sampled as a bare scalar (which would silently
        # misparse `A i`/`∏ i, Γ(Aᵢ)` and starve the row).
        _finm = re.fullmatch(r'Fin\s+([A-Za-zα-ω]\w*)\s*→\s*ℂ', typ)
        # a bare `Fin N` INDEX binder (`(j : Fin N)`, DLMF 31.14.5's distinguished
        # singularity): sampled as a small nonnegative integer index, so `a j`/`γ j`
        # hit the row's own Fin-vector callables. An index ≥ the sampled cardinality
        # raises in the callable → the point drops honestly (never wraps around).
        _finidx = re.fullmatch(r'Fin\s+([A-Za-zα-ω]\w*)', typ)
        base = ("Z" if typ in ("ℤ",) else "N" if typ in ("ℕ",) else
                "R" if typ in ("ℝ",) else "C" if typ in ("ℂ",) or typ in ctyvars else
                "H" if typ in ("ℍ", "UpperHalfPlane") else                # z : ℍ (Im z > 0)
                "zmod" if zm else                                         # a : ZMod k element
                "dirchar" if dch else                    # χ : DirichletCharacter ℂ k (index grid)
                # abstract-ring character binders `(χ : MulChar R R')` / `(ψ : AddChar R R')`
                # (the Gauss-sum defining surface, DLMF 27.10.9) — instantiated at R := ZMod k
                # from the anchored concrete characters (ob.SAMPLE_MULCHARS / _addchar_sample).
                # NOTE this paren-free type only matches an ABSTRACT ring: a concrete
                # `MulChar (ZMod p) ℂ` binder is not captured by the group regex at all —
                # it is handled by the paren-balanced '_zmodchar' scan below, which couples
                # the character to the row's OWN modulus binder p.
                "mulchar" if typ.startswith("MulChar ") else
                "addchar" if typ.startswith("AddChar ") else
                "finvecC" if _finm else                  # A/B : Fin q → ℂ (see above)
                "finidx" if _finidx else                 # j : Fin N (an index, see above)
                # abstract Finset binder `s : Finset ι` and its ι-indexed function binders
                # `c : ι → ℝ` / `m : ι → ℕ` (the DLMF 18.18 Laguerre sum rule): s sampled as
                # a small cardinality N, the functions as pointwise-sampled callables (see
                # the finset/absfnR/absfnN grids in sweep_eq and evaluate's fsumabs).
                "finset" if typ.startswith("Finset ") else
                "absfnR" if re.fullmatch(r'.+→\s*ℝ', typ) else
                "absfnN" if re.fullmatch(r'.+→\s*ℕ', typ) else
                "latticept" if typ.endswith(".lattice") else "other")   # l : L.lattice (a period)
        for nm in grp.group(1).split():
            # first binder wins: a variable's type comes from its DECLARATION `(k : ℕ)`,
            # never from a later coercion `(k : ℝ)` nested inside a hypothesis type.
            out.setdefault(nm, base)
            if _finm:
                cons.setdefault('_finvecdim', {})[nm] = _finm.group(1)
            elif _finidx:
                cons.setdefault('_finidxdim', {})[nm] = _finidx.group(1)
    # interval-membership hypotheses `x ∈ Set.Icc a b` (Icc/Ioo/Ico/Ioc) restrict x to
    # [a,b] — the parens break per-binder grouping, so scan `head`. Generalises the old
    # [-1,1]-only case to any integer-bounded interval (e.g. the Bernoulli-Fourier [0,1],
    # which the old regex missed → x sampled at 1.7 outside the period, a false FAIL).
    _icc_bound = r'\(?\s*(-?\d+)\s*(?::[^)]*)?\)?'
    for mm in re.finditer(r'(\w+)\s*∈\s*(?:Set\.)?(?:Icc|Ioo|Ico|Ioc)\s+'
                          + _icc_bound + r'\s+' + _icc_bound, head):
        _add_flag(cons, mm.group(1),
                  ('icc', mp.mpf(int(mm.group(2))), mp.mpf(int(mm.group(3)))))
    # `ν > −1/2` (Bessel-K real-order bridge) — the inner parens of `-(1 / 2)` break the
    # per-binder grouping, so scan `head` directly for `-(1 / 2) < ν`.
    for mm in re.finditer(r'-\s*\(\s*1\s*/\s*2\s*\)\s*<\s*(\w+)', head):
        _add_flag(cons, mm.group(1), 'gtNegHalf')
    # DISJUNCTIVE window hypothesis `hx : (a < x ∧ x < b) ∨ c < x` (qgamma_5_18_8,
    # DLMF 5.18.8: `(0 < x ∧ x < 1) ∨ 2 < x` — the q-monotonicity REVERSES on the excluded
    # middle band 1 < x < 2, DLMF 5.18.9, so sampling the default grid there fabricates a
    # refutation of a true theorem). Parens break per-binder grouping — scan `head`;
    # recorded as ('runion', a, b, c) and honored by _real_grid with points strictly
    # inside (a,b) ∪ (c,∞). Restricted sampling inside the stated hypothesis only;
    # setdefault so a structured flag from the per-binder scan is never clobbered.
    _rnum = r'(-?\d+(?:\s*/\s*\d+|\.\d+)?)'
    for mm in re.finditer(r'\(\s*' + _rnum + r'\s*<\s*(\w+)\s*∧\s*\2\s*<\s*' + _rnum
                          + r'\s*\)\s*∨\s*' + _rnum + r'\s*<\s*\2', head):
        _a, _b, _c = (_const_val(mm.group(i)) for i in (1, 3, 4))
        if _a is not None and _b is not None and _c is not None:
            cons.setdefault(mm.group(2), ('runion', _a, _b, _c))
    # theta power-series radius hypothesis (DLMF 20.6.1 / §20.6, Ch20PowerSeries.lean):
    #   `∀ m n : ℤ, [¬(m = 0 ∧ n = 0) →] ‖z‖ < ‖(m:ℂ) [− 1/2] + [(](n:ℂ) [− 1/2][)] * τ‖`
    # — ‖z‖ below EVERY point of the (possibly half-shifted) lattice ℤ+s + (ℤ+t)τ, i.e.
    # z inside the convergence disk of the 20.6.2–20.6.5 coefficient series. The nested
    # parens/∀ break per-binder grouping, so scan `head`; recorded as ('latdisk', s, t)
    # and honored by sampling z WELL INSIDE the minimal lattice distance over the τ grid
    # (restricted sampling inside the stated hypothesis — nothing loosened). Without it,
    # the default ℂ grid drifts outside the radius, the z-power series genuinely diverges
    # and the divergence-acceleration fallback burns the EVAL_BUDGET → a false
    # eval-timeout skip of a true identity.
    _lat = r'\(\s*(\w+)\s*:\s*ℂ\s*\)'
    mm = re.search(
        r'∀\s+(\w+)\s+(\w+)\s*:\s*ℤ\s*,\s*(?:¬\(\s*\1\s*=\s*0\s*∧\s*\2\s*=\s*0\s*\)\s*→\s*)?'
        r'‖(\w+)‖\s*<\s*‖\s*' + _lat + r'\s*(-\s*1\s*/\s*2)?\s*\+\s*'
        r'(?:' + _lat + r'|\(\s*' + _lat + r'\s*-\s*1\s*/\s*2\s*\))\s*\*\s*(\w+)\s*‖', head)
    if mm and mm.group(4) == mm.group(1) and (mm.group(6) or mm.group(7)) == mm.group(2):
        cons[mm.group(3)] = ('latdisk',
                             mp.mpf(-1) / 2 if mm.group(5) else mp.mpf(0),
                             mp.mpf(-1) / 2 if mm.group(7) else mp.mpf(0))
    # parity hypothesis on a PRODUCT `heven : Even (m * n)` (Gauss-sum reciprocity DLMF
    # 20.11.2: coprime m n with mn even — the identity is genuinely false at mn odd, so a
    # sample violating it fabricates a counterexample). The nested parens break the
    # per-binder grouping above, so scan `head` directly, like Icc/uIcc.
    for mm in re.finditer(r'\bEven\s+\(\s*(\w+)\s*\*\s*(\w+)\s*\)', head):
        cons.setdefault('_pairs', []).append(['evenprod', mm.group(1), mm.group(2)])
    # `0 ∉ Set.uIcc a b` (∫₁/x: the bounds must not straddle 0) — a joint same-sign filter.
    for mm in re.finditer(r'0[^∉]*∉\s*Set\.uI(?:cc|oo|oc|co)\s+(\w+)\s+(\w+)', head):
        cons.setdefault('_pairs', []).append(['samesign', mm.group(1), mm.group(2)])
    # real-part difference-positivity `0 < (c − d).re` on two COMPLEX binders (the DLMF
    # 15.6.8/15.6.9 Euler-integral convergence condition Re c > Re d > 0, paired with the
    # per-binder `0 < d.re`). The inner parens of `(c − d)` break per-binder grouping (the
    # `[^(){}]+?` type matcher stops at the `(`), so scan `head` directly like Icc/uIcc above.
    # The default product grid draws c, d incoherently — almost every pair has Re(c − d) ≤ 0,
    # where the integral's (1 − t)^{c−d−1} endpoint diverges — so a mere drop-filter would
    # starve the row. Record a CONSTRUCTIVE real-part ordering ('_reorder': (d, c)) instead:
    # the sampler pins Re d into the open interval (0, Re c) per sample, so BOTH `0 < d.re`
    # and `0 < (c − d).re` hold exactly by construction (cf. the `_finvecgt` / sumzero
    # constructive pins). ADDITIVE; sampling restricted to the stated hypothesis, nothing
    # loosened.
    for mm in re.finditer(r'0\s*<\s*\(\s*(\w+)\s*-\s*(\w+)\s*\)\s*\.\s*re\b', head):
        cons.setdefault('_reorder', []).append((mm.group(2), mm.group(1)))  # (d, c)
    # real-part ordering written with the PREFIX `re` function (`Complex.re` opened) instead of
    # the `.re` dot spelling: the DLMF 15.6.1 Euler-integral convergence pair `0 < re b`,
    # `re b < re c` (ordinaryHypergeometric_eq_betaIntegral_complex). This is the SAME
    # Re c > Re b > 0 window as the `(c − d).re` dot form handled just above, but the extractor's
    # `_reorder` regex only knew the dot spelling, so b and c stayed on the default incoherent
    # mixed-sign product grid — where the ∫₀¹ t^(b−1)(1−t)^(c−b−1)(1−zt)^(−a) endpoints are
    # non-integrable (almost every combo has Re(b−1) ≤ −1 at t→0 or Re(c−b−1) ≤ −1 at t→1) so
    # EVERY point dropped → a spurious `undersampled/domain` skip on a fully-proven theorem.
    # Record the identical constructive ('_reorder': (b, c)) pin — the sampler puts Re b at a
    # strict-interior fraction of Re c, so 0 < Re b < Re c holds by construction (b's sampled
    # imaginary part kept). Emitted ONLY when BOTH the `0 < re b` lower bound and the
    # `re b < re c` ordering are present, matching the stated hypothesis exactly. ADDITIVE:
    # sampling restricted to the stated hypothesis domain, nothing loosened.
    _re_pos = set(re.findall(r'0\s*<\s*re\s+(\w+)\b', head))
    for mm in re.finditer(r'\bre\s+(\w+)\s*<\s*re\s+(\w+)\b', head):
        if mm.group(1) in _re_pos:
            pair = (mm.group(1), mm.group(2))
            if pair not in cons.setdefault('_reorder', []):
                cons['_reorder'].append(pair)
    # real-part sign/vanishing hypothesis on a signed SUM of complex binders written with the
    # `0` on the RIGHT: `(c − a − b).re < 0`, `… > 0`, `… = 0` (the DLMF 15.4.22/15.4.23
    # argument-unity boundary regimes — Re(c−a−b) = 0 resp. < 0). Left the domain sampler
    # blind, so the default incoherent (a,b,c) product draws points OUTSIDE the stated regime
    # where the z→1⁻ limit genuinely diverges (Re(c−a−b) > 0 makes 15.4.23's F/(1−z)^{c−a−b}
    # blow up), fabricating a FAIL on a true theorem — exactly the DLMF 15.4.20 `0 < c−a−b`
    # hazard already noted at the Tendsto sampler. `< 0` / `> 0` are DROP filters (_pairs
    # 'relin', honored in _pairs_ok); `= 0` cannot be drop-filtered (the discrete complex grid
    # never lands on Re = 0 exactly), so it is a CONSTRUCTIVE pin ('_releq'): the +1-coefficient
    # binder's real part is set to make Re(sum) = 0 by construction (Im kept from the grid),
    # the same sound in-hypothesis construction as the `_reorder` real-part ordering above.
    # ADDITIVE: sampling is restricted to / constructed inside the stated hypothesis only.
    for mm in re.finditer(r'\(\s*(-?\s*[A-Za-zα-ωΑ-Ω_][\w\s+\-]*?)\s*\)\s*\.\s*re\s*'
                          r'(=|<|>)\s*0(?![.\d])', head):
        inner, op = mm.group(1).strip(), mm.group(2)
        if not re.fullmatch(r'[+\-]?\s*[A-Za-zα-ωΑ-Ω_]\w*'
                            r'(?:\s*[+\-]\s*[A-Za-zα-ωΑ-Ω_]\w*)*', inner):
            continue                       # only a pure signed sum of binder tokens
        coeffs = {}
        for sign, name in re.findall(r'([+\-]?)\s*([A-Za-zα-ωΑ-Ω_]\w*)', inner):
            coeffs[name] = coeffs.get(name, 0) + (-1 if sign == '-' else 1)
        coeffs = {k: v for k, v in coeffs.items() if v != 0}
        if not coeffs:
            continue
        if op in ('<', '>'):
            pr = ['relin', coeffs, 'lt' if op == '<' else 'gt']
            if pr not in cons.setdefault('_pairs', []):
                cons['_pairs'].append(pr)
        else:                              # `= 0` — constructive pin on a unit-coeff binder
            solve = next((k for k, c in coeffs.items() if c == 1),
                         next((k for k, c in coeffs.items() if c == -1), None))
            if solve is not None:
                pr = [solve, coeffs]
                if pr not in cons.setdefault('_releq', []):
                    cons['_releq'].append(pr)
    # CONSTANT-EXPRESSION bounds whose inner parens break per-binder grouping (the irrational
    # `-(Real.sqrt 2 / 2) < x` of erf_7_8_4 — `[^()]+?` stops at the `(`). Scan each TOP-LEVEL
    # `( … )` binder group with a paren-balanced matcher, take its `hyp : TYPE`, and if TYPE is
    # `‹const-expr› </≤ var` or `var </≤ ‹const-expr›`, evaluate the constant side to a numeric
    # lower/upper sample-filter threshold (keeps the named-flag/literal handling above intact).
    for grp in _toplevel_binder_groups(head):
        if ":" not in grp:
            continue
        ty = grp.split(":", 1)[1].strip()
        # DECLARATION-type repair: the flat per-binder regex above scans a nested
        # coercion cast `(n : 𝕂)` INSIDE an earlier hypothesis type exactly like a
        # declaration, and "first binder wins" then locks the LATER real declaration
        # `(n : ℕ)` out (frobCoeff_gauss: `hcd : ∀ n : ℕ, c + 2ρ + (n : 𝕂) ≠ 0`
        # precedes `(n : ℕ)`, so n was typed complex and every sample dropped). A
        # TOP-LEVEL binder group whose whole type is a PLAIN scalar IS the variable's
        # declaration — let it override whatever a nested cast set. ADDITIVE: fires
        # only on top-level `names : ℕ/ℤ/ℝ/ℂ/ℍ/‹RCLike tyvar›` groups; hypothesis
        # groups (compound types) and structured bases (zmod/dirchar/…) are untouched.
        if ty in P._TYPEMAP or ty in ctyvars:
            _declbase = "C" if ty in ctyvars else P._TYPEMAP[ty]
            for nm in grp.split(":", 1)[0].split():
                if re.fullmatch(r"[A-Za-zα-ωΑ-Ω_][\w'′₀-₉]*", nm):
                    out[nm] = _declbase
        # REAL Fin-vector binders `(γ a : Fin N → ℝ) (z : Fin (N - 1) → ℝ)` (the Stieltjes
        # weight of DLMF 31.15.12). The flat per-binder regex misses a PARENTHESIZED
        # dimension entirely (`z` was not a binder at all), and the pointwise `absfnR`
        # sampling it gives the others carries no cardinality, so a bare `∏ j, ∏ k, …`
        # over their two DIFFERENT `Fin` carriers had no range to run over. Record each
        # vector with its dimension EXPRESSION ('_finvecRdim'); sweep_eq turns them into
        # `.q`-tagged Fin-vector callables — but only for a row with no uncaptured
        # hypothesis binder (see the '_finvecRdim' guard there), so a row whose vectors are
        # constrained by a ∀-hypothesis keeps its present pointwise sampling and its skip.
        mm = re.fullmatch(r'Fin\s+(.+?)\s*→\s*ℝ', ty)
        if mm:
            for nm in grp.split(":", 1)[0].split():
                if re.fullmatch(r"[A-Za-zα-ωΑ-Ω_][\w'′₀-₉]*", nm):
                    out.setdefault(nm, "absfnR")
                    cons.setdefault('_finvecRdim', {})[nm] = \
                        " ".join(mm.group(1).strip("() ").split())
        # indicial-root hypothesis `hρ : ρ * (ρ + c − 1) = 0` (DLMF 15.10.2's z = 0
        # indicial equation, frobCoeff_gauss) — nested parens hide it from the flat
        # regex. Recorded as an 'indroot' pair; sweep_eq SOLVES it per sample
        # (ρ ∈ {0, 1 − c}), mirroring the sumzero constructive pins.
        mm = re.fullmatch(r'([A-Za-zα-ωΑ-Ω]\w*)\s*\*\s*\(\s*\1\s*\+\s*'
                          r'([A-Za-zα-ωΑ-Ω]\w*)\s*-\s*1\s*\)\s*=\s*0', ty)
        if mm:
            pr = ['indroot', mm.group(1), mm.group(2)]
            if pr not in cons.setdefault('_pairs', []):
                cons['_pairs'].append(pr)
        # ∀-quantified LOWER-BOUND hypothesis on a Fin-vector's real part, `hA : ∀ i, σ <
        # (A i).re` (DLMF 16.18.1's Mellin–Barnes contour-abscissa hypothesis `σ < Re Aᵢ`,
        # meijerG_eq_pFq): tags the 'finvecC' vector NAME with the OTHER binder it must
        # stay right of, so the finvecC sampler in sweep_eq can construct a witness
        # satisfying the hypothesis BY CONSTRUCTION (Re(Aᵢ) = lo + 1 + i/2 > lo for every
        # i), never by search — sound because the construction is checked against the
        # SAME parsed hypothesis, not assumed.
        mm = re.fullmatch(r'∀\s*(\w+)\s*,\s*(\w+)\s*<\s*\(\s*(\w+)\s+\1\s*\)\s*\.\s*re', ty)
        if mm:
            cons.setdefault('_finvecgt', {})[mm.group(3)] = mm.group(2)
        # ∀-quantified NONPOSITIVE-INTEGER-AVOIDANCE hypothesis on a Fin-vector, `hB : ∀ j
        # (k : ℕ), (k : ℂ) ≠ -B j` (DLMF 16.18.1's Γ(Bⱼ) pole-avoidance hypothesis): tags
        # the vector so the sampler avoids the poles by construction (a non-integer real
        # part), never by search.
        mm = re.fullmatch(r'∀\s*(\w+)\s*\(\s*(\w+)\s*:\s*ℕ\s*\)\s*,\s*\(\s*\2\s*:\s*(?:ℂ|𝕂|𝕜)\s*\)'
                          r'\s*≠\s*-\s*(\w+)\s+\1', ty)
        if mm:
            cons.setdefault('_finvecavoidnat', set()).add(mm.group(3))
        # SAME pole-avoidance hypothesis in the TWO-∀ `vⱼ ≠ −n` spelling of DLMF 5.8.5,
        # `hb : ∀ j, ∀ n : ℕ, b j ≠ -n` (the ratio product's `bⱼ` off the nonpositive integers,
        # so Γ(bⱼ) is finite and (k:ℂ) ≠ −bⱼ for every k:ℕ). Distinct surface shape from the
        # single-∀ `(n:ℂ) ≠ −Bⱼ` regex above; same '_finvecavoidnat' construction downstream.
        mm = re.fullmatch(r'∀\s*(\w+)\s*,\s*∀\s*(\w+)\s*:\s*ℕ\s*,\s*(\w+)\s+\1\s*'
                          r'≠\s*-\s*\2', ty)
        if mm and out.get(mm.group(3)) == "finvecC":
            cons.setdefault('_finvecavoidnat', set()).add(mm.group(3))
        # BALANCED-PAIR side condition (DLMF 5.8.4 `∑ₖ aₖ = ∑ₖ bₖ`, surfaced as the named
        # predicate `hsum : gamma_5_8_4 a b`): a hypothesis applying a predicate to exactly two
        # equal-cardinality 'finvecC' vectors is the equal-sum coupling that makes the DLMF 5.8.5
        # double product ∏ₖ∏ⱼ(aⱼ+k)/(bⱼ+k) converge (log fₖ = O(1/k²) iff ∑a=∑b; otherwise the
        # harmonic O(1/k) tail diverges). Recorded so the finvecC sampler constructs the two
        # vectors DISTINCT and balanced BY CONSTRUCTION (last bⱼ pinned to close ∑b=∑a) —
        # sampling the stated hypothesis domain, validated against the independent Γ-ratio RHS so
        # a misread can only skip/FAIL, never fabricate a PASS.
        mm = re.fullmatch(r'\w[\w.]*\s+(\w+)\s+(\w+)', ty)
        if mm and out.get(mm.group(1)) == "finvecC" and out.get(mm.group(2)) == "finvecC" \
                and mm.group(1) != mm.group(2):
            cons.setdefault('_finvecbalance', (mm.group(1), mm.group(2)))
        # CONCRETE character binders over the row's own modulus — `{χ : MulChar (ZMod p) ℂ}`
        # / `{e : AddChar (ZMod p) ℂ}` (the DLMF §27.8 Gauss-sum magnitude surface,
        # GaussSumDirichlet.lean). The parenthesized `(ZMod p)` breaks the flat per-binder
        # regex above (which skipped these as `unbound:χ`/`unbound:e`), so match them here
        # in the paren-balanced scan. The character's grid is an INDEX, resolved per sample
        # to a concrete character mod the SAME sampled p (ob._mulchar_sample /
        # ob._addchar_sample, anchored in oracle_bindings.verify() to the DLMF 27.8.1–27.8.4
        # / 27.10.9 defining relations, never by name); '_zmodchar' records var → p so the
        # sample loop can couple them, and p joins the cyclic-moduli grid.
        mm = re.fullmatch(r'(MulChar|AddChar)\s*\(\s*ZMod\s+([A-Za-zα-ω]\w*)\s*\)\s*ℂ', ty)
        if mm:
            for nm in grp.split(":", 1)[0].split():
                out.setdefault(nm, "mulchar" if mm.group(1) == "MulChar" else "addchar")
                cons.setdefault('_zmodchar', {})[nm] = mm.group(2)
            cons.setdefault(mm.group(2), 'modulus')
        mm = re.fullmatch(r'(.+?)\s*(<|≤)\s*([A-Za-zα-ω]\w*)', ty)   # const-expr (</≤) var
        if mm and not re.fullmatch(r'[A-Za-zα-ω]\w*', mm.group(1).strip()) \
                and mm.group(3) not in cons.get('_lower', {}):
            cv = _const_expr_val(mm.group(1))
            if cv is not None:
                cons.setdefault('_lower', {})[mm.group(3)] = (cv, mm.group(2) == '<')
        mm = re.fullmatch(r'([A-Za-zα-ω]\w*)\s*(<|≤)\s*(.+)', ty)    # var (</≤) const-expr
        if mm and not re.fullmatch(r'[A-Za-zα-ω]\w*', mm.group(3).strip()) \
                and mm.group(1) not in cons.get('_upper', {}):
            cv = _const_expr_val(mm.group(3))
            if cv is not None:
                cons.setdefault('_upper', {})[mm.group(1)] = (cv, mm.group(2) == '<')
        # DEFINING-EQUALITY hypothesis `hζ : ζ = <expr>` — a lone binder VARIABLE set equal
        # to an expression in the OTHER binder variables (DLMF 15.8.32's ζ = e^{2πi/3}(1−z)/
        # (z − e^{4πi/3})). collect_free frees ζ from the conclusion, so the sampler would
        # otherwise draw ζ INDEPENDENTLY of z and score the identity at points where the
        # STATED ζ = f(z) is violated — a fabricated FAIL, not a DLMF discrepancy. Record a
        # CONSTRUCTIVE pin ('_defeq'): the sample loop computes ζ := f(z) per env (mirroring
        # the sumzero / _reorder / _releq constructive pins) and ζ is dropped from the grid.
        # ADDITIVE — ζ is set to EXACTLY its stated value; nothing loosened. Fires only when
        # the whole type is `ident = expr`, the ident is a genuine scalar binder, and expr
        # parses to something that does NOT mention the ident itself (no self-reference).
        mm = re.fullmatch(r'([A-Za-zα-ωΑ-Ω]\w*)\s*=\s*(.+)', " ".join(ty.split()))
        if mm and out.get(mm.group(1)) in ("C", "R"):
            _dv, _dexpr = mm.group(1), " ".join(mm.group(2).split())
            try:
                _dast = parse(_dexpr)
                _dnode = _dast[1] if _dast and _dast[0] == "expr" else _dast
                _dfv = set(); collect_free(_dnode, _dfv)
            except Exception:
                _dfv = None
            if _dfv is not None and _dv not in _dfv \
                    and _dv not in [q[0] for q in cons.get('_defeq', [])]:
                cons.setdefault('_defeq', []).append((_dv, _dexpr))
        # LOWER-norm hypothesis `c < ‖v‖` / `c ≤ ‖v‖` (DLMF 15.8.32's 1 < ‖z‖) — the default ℂ
        # grid straddles the boundary, and OUTSIDE the stated domain the row's principal cpow
        # prefactors ((−z)^{3a}) follow a different branch than the analytically continued ₂F₁
        # (fabricating a branch-mismatch worst ≈ 1). Honored as a per-sample DROP filter
        # ('normlow') plus, when it is the only wedge/disk constraint on a ℂ variable, a curated
        # in-domain grid (see _domain_reject_grid). ADDITIVE: sampling restricted to the stated
        # hypothesis only. The bracketed content is stored verbatim (a bare var or an expression).
        mm = re.fullmatch(r'(.+?)\s*(<|≤)\s*[‖|]\s*(.+?)\s*[‖|]', ty)
        if mm:
            cv = _const_expr_val(mm.group(1))
            if cv is not None:
                pr = ['normlow', " ".join(mm.group(3).split()), cv, mm.group(2) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
        # PRINCIPAL-ARGUMENT WEDGE hypothesis `abs (Complex.arg (f v)) < θ` /`≤ θ` (DLMF
        # 15.8.32's |ph(−z)| < π/3): outside the wedge the (−z)^{3a} / (−ζ)^{2a} principal
        # powers cross their branch cut and the identity, stated only in the wedge, genuinely
        # fails — scoring it there fabricates a counterexample. Honored as a per-sample DROP
        # filter ('argwedge', evaluated as |arg(f v)| < θ through the SAME parser) plus a curated
        # in-wedge grid. ADDITIVE: sampling restricted to the stated hypothesis only.
        mm = re.fullmatch(r'(?:abs|\|·\|)\s*\(\s*Complex\.arg\s*\((.+)\)\s*\)\s*(<|≤)\s*(.+)', ty)
        if mm:
            bv = _const_expr_val(mm.group(3))
            if bv is not None:
                pr = ['argwedge', " ".join(mm.group(1).split()), bv, mm.group(2) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
        # pipe-abs spelling of the SAME wedge, `|Complex.arg b| < θ` (DLMF 7.14.1's
        # |ph b| < π/4, erf_7_14_1_full): the `abs (Complex.arg (…))` regex above cannot see
        # the |·| notation, so the wedge was silently dropped and b drew the whole nonzero ℂ
        # grid — outside the wedge Re(b²) < 0, erfc(bt) ceases to decay and the ∫₀^∞ identity
        # genuinely fails (rel = 1.0 measured at b = −0.8 − 1.1i), fabricating a FAIL on a
        # statement that checks to ≤ 1e-25 inside the wedge. Same 'argwedge' DROP filter (+
        # curated in-wedge grid) as above. ADDITIVE: sampling restricted to the stated wedge.
        mm = re.fullmatch(r'\|\s*Complex\.arg\s+([A-Za-zα-ωΑ-Ω]\w*[\'′]?)\s*\|\s*(<|≤)\s*(.+)', ty)
        if mm:
            bv = _const_expr_val(mm.group(3))
            if bv is not None:
                pr = ['argwedge', mm.group(1), bv, mm.group(2) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
        # principal-arg-SUM window `x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi` (DLMF 4.8.2's
        # sharp domain for log(xy) = log x + log y, log_mul_eq): outside it the two sides
        # differ by exactly ±2πi (rel = 1.0–1.6 measured at x = y = −2.4 + 0.35i), so scoring
        # there fabricates a counterexample on a Mathlib-proven statement. Two-variable DROP
        # filter 'argsumpv' (honored in _pairs_ok). ADDITIVE.
        mm = re.fullmatch(r'([A-Za-zα-ωΑ-Ω]\w*[\'′]?)\.arg\s*\+\s*([A-Za-zα-ωΑ-Ω]\w*[\'′]?)\.arg'
                          r'\s*∈\s*Set\.Ioc\s*\(\s*-\s*Real\.pi\s*\)\s*Real\.pi', ty)
        if mm:
            pr = ['argsumpv', mm.group(1), mm.group(2)]
            if pr not in cons.setdefault('_pairs', []):
                cons['_pairs'].append(pr)
        # ONE-SIDED principal-arg upper bound `z.arg ≤ θ` / `Complex.arg z < θ` (DLMF 11.2.2's
        # arg z ≤ π/2 window, struveLC_11_2_2: beyond it the i·z rotation crosses the principal
        # cpow cut and the L↔H identity is off by a phase — rel = 1.12 measured at arg z = 1.7,
        # exact to 1e-26 at arg z ≤ π/2). The principal arg is bounded below by −π automatically,
        # so the upper cut is the whole constraint. DROP filter 'arghigh' (in _pairs_ok). ADDITIVE.
        mm = re.fullmatch(r'(?:([A-Za-zα-ωΑ-Ω]\w*[\'′]?)\.arg|Complex\.arg\s+([A-Za-zα-ωΑ-Ω]\w*[\'′]?))'
                          r'\s*(<|≤)\s*(.+)', ty)
        if mm:
            bv = _const_expr_val(mm.group(4))
            if bv is not None:
                pr = ['arghigh', mm.group(1) or mm.group(2), bv, mm.group(3) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
        # 3j TRIANGLE-condition hypothesis `|j₁ − j₂| ≤ j₃ ∧ j₃ ≤ j₁ + j₂` (DLMF 34.2.1) and its
        # NEGATION `¬ (…)` (wigner3j_eq_zero_of_triangle_dlmf / orthSum_orthogonality_dlmf): the
        # ¬-form binder never even reached the flat regex (parenthesized type), so j's drew
        # triangle-SATISFYING triples where the 3j symbol is honestly nonzero (worst = 0.5774 =
        # |3j(1,1,0;1,−1,0)| = 1/√3) — a fabricated refutation of a kernel-proven selection
        # rule. DROP filters 'triangle'/'nottriangle' (in _pairs_ok), keeping only samples
        # inside the stated (non)triangle window. ADDITIVE.
        _V3 = r"[A-Za-zα-ωΑ-Ω][\w'′]*"
        mm = re.fullmatch(r'(¬\s*\(\s*)?\|\s*(' + _V3 + r')\s*-\s*(' + _V3 + r')\s*\|\s*≤\s*(' + _V3 + r')'
                          r'\s*∧\s*(' + _V3 + r')\s*≤\s*(' + _V3 + r')\s*\+\s*(' + _V3 + r')\s*(\))?', ty)
        if mm and (mm.group(1) is None) == (mm.group(8) is None) \
                and mm.group(4) == mm.group(5) and mm.group(2) == mm.group(6) \
                and mm.group(3) == mm.group(7):
            pr = ['nottriangle' if mm.group(1) else 'triangle',
                  mm.group(2), mm.group(3), mm.group(4)]
            if pr not in cons.setdefault('_pairs', []):
                cons['_pairs'].append(pr)
        # REAL-PART positivity of an EXPRESSION: `habc : 0 < (c − a − b).re` (the Gauss
        # summation hypothesis of DLMF 15.4.20 / ordinaryHypergeometric_one_dlmf_complex).
        # The flat per-binder regex records `0 < s.re` for a BARE variable only, and its
        # own grouping cannot even see this type (the inner parens break it), so the
        # hypothesis was dropped entirely and the row scored at parameters where the Gauss
        # series at z = 1 DIVERGES — i.e. where Lean's `₂F₁ … 1` is its junk 0 while the
        # Γ-quotient RHS is finite. Recorded as a per-sample DROP filter ('reexprpos', see
        # _pairs_ok). ADDITIVE: sampling restricted to the stated hypothesis only.
        mm = re.fullmatch(r'0\s*(<|≤)\s*\(\s*(.+?)\s*\)\s*\.re', ty)
        if mm and not re.fullmatch(r'[A-Za-zα-ωΑ-Ω]\w*', mm.group(2).strip()):
            _rexpr = " ".join(mm.group(2).split())
            try:
                _rast = P(tokenize(_rexpr)).expr()
                _rfv = set(); collect_free(_rast, _rfv)
            except Exception:
                _rfv = None
            if _rfv and all(x in out for x in _rfv):
                pr = ['reexprpos', _rexpr, mm.group(1) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
        # MAGNETIC-window hypothesis `|m₃| ≤ j₃` with a VARIABLE bound (DLMF §34.2 domain
        # conventions, orthSum_orthogonality_dlmf): distinct from the literal `|v| ≤ 1` unit
        # flag (numeric bounds never reach this identifier-only regex). Outside the window the
        # orthogonality sum is empty (0) while the δ-RHS is 1 — a fabricated counterexample
        # (worst = 1.0 measured). DROP filter 'absle' (in _pairs_ok). ADDITIVE.
        mm = re.fullmatch(r'\|\s*(' + _V3 + r')\s*\|\s*≤\s*(' + _V3 + r')', ty)
        if mm:
            pr = ['absle', mm.group(1), mm.group(2)]
            if pr not in cons.setdefault('_pairs', []):
                cons['_pairs'].append(pr)
        # REAL-PART strip hypothesis `|v.re| < c` (DLMF 15.4.14/16's |Re z| < π/2 —
        # the maximal strip of the principal extension, see ERRATA
        # ch15-4-14-16-principal-overreach). The pipe-abs-on-.re spelling reaches no
        # earlier rule, so the whole-plane grid sampled |Re z| > π/2 where the
        # (corrected) statement's own hypothesis fails. DROP filter 'absrelt'
        # (in _pairs_ok). ADDITIVE: restricts sampling to the stated hypothesis.
        mm = re.fullmatch(r'\|\s*(' + _V3 + r')\.re\s*\|\s*(<|≤)\s*(.+)', ty)
        if mm:
            _bexpr = " ".join(mm.group(3).split())
            try:
                _bast = P(tokenize(_bexpr)).expr()
                _bfv = set(); collect_free(_bast, _bfv)
            except Exception:
                _bfv = None
            if _bfv is not None and all(x in out for x in _bfv):
                pr = ['absrelt', mm.group(1), _bexpr, mm.group(2) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
        # COMPLEX-CENTERED off-center disk hypothesis `‖g(v)‖ < r` whose centre is NOT a plain
        # real literal (contains `Complex.I` / `Real.sqrt`, e.g. DLMF 15.8.33's twin disks
        # ‖z − 1/4 ± (√3/4)i‖ < √3/2). The real-centre `normdisk` regex above cannot see it
        # (its centre and radius are decimal literals only), so the default ℂ grid lands
        # entirely outside the twin-disk lens and the cubic map (1−z)/(1+2z) leaves the ₂F₁
        # disc, fabricating a branch worst ≈ 0.8. Honored as the existing per-sample `normexpr`
        # DROP filter plus a curated in-lens grid (rejection-sampled against these SAME disks).
        # ADDITIVE: sampling restricted to the stated hypotheses only. Trig discs (handled by
        # the trig-disc block, which also sets a curated grid) are deliberately excluded.
        mm = re.fullmatch(r'[‖|]\s*(.+?)\s*[‖|]\s*(<|≤)\s*(.+)', ty)
        if mm and re.search(r'Complex\.I\b|\bReal\.sqrt\b', mm.group(1)) \
                and not re.search(r'\b(?:sin|cos|tan|sinh|cosh|tanh)\b', mm.group(1)):
            rv = _const_expr_val(mm.group(3))
            _dexpr = " ".join(mm.group(1).split())
            if rv is not None and rv > 0 and not re.fullmatch(r'[A-Za-zα-ω]\w*', _dexpr):
                try:
                    _dast = parse(_dexpr)
                    _dnode = _dast[1] if _dast and _dast[0] == "expr" else _dast
                    _dfv = set(); collect_free(_dnode, _dfv)
                    _dvv = {x for x in _dfv if out.get(x) in ("C", "R")}
                except Exception:
                    _dvv = set()
                if len(_dvv) == 1:
                    pr = ['normexpr', _dexpr, rv, mm.group(2) == '<']
                    if pr not in cons.setdefault('_pairs', []):
                        cons['_pairs'].append(pr)
        # MIN-of-two-radii disc hypothesis `‖E‖ < min c ‖F‖` — the convergence disc of a
        # composed local expansion, where the radius is itself the smaller of a literal and a
        # norm in the OTHER parameters (DLMF 31.3.13's `‖z/(z−1)‖ < min 1 ‖a/(a−1)‖`, the
        # preimage of the transformed local-Heun disc under the homography z ↦ z/(z−1)). None
        # of the existing disc regexes can see it (its bound is not a constant), so the
        # hypothesis imposed NO filter at all and the row sampled OUTSIDE the disc, where the
        # transformed `heunFn` is Lean's junk tsum. Recorded as
        #   • 'normexprmin' — the FULL two-expression predicate ‖E‖ < min(c, ‖F‖), honored
        #     per sample in _pairs_ok exactly like the other disc filters, and
        #   • 'normexpr'    — the NECESSARY single-variable consequence ‖E‖ < c (valid because
        #     min(c,·) ≤ c), which additionally lets _filter_domain_pairs keep E's variable
        #     off the 24-combo window's out-of-disc values (only recorded when E involves a
        #     single sampled ℂ/ℝ binder, as that filter requires).
        # ADDITIVE: a previously-unenforced hypothesis now restricts sampling to the stated
        # domain; no tolerance, gate or scoring change.
        mm = re.fullmatch(r'[‖|]\s*(.+?)\s*[‖|]\s*(<|≤)\s*min\s+(\S+)\s+[‖|]\s*(.+?)\s*[‖|]', ty)
        if mm:
            _mE, _mF = " ".join(mm.group(1).split()), " ".join(mm.group(4).split())
            _mc = _const_expr_val(mm.group(3))
            try:
                _mEa = P(tokenize(_mE)).expr()
                _mFa = P(tokenize(_mF)).expr()
                _mEv = set(); collect_free(_mEa, _mEv)
                _mFv = set(); collect_free(_mFa, _mFv)
                _parsed = True
            except Exception:
                _parsed = False
            if _parsed and _mc is not None and _mc > 0 \
                    and all(x in out for x in (_mEv | _mFv)):
                pr = ['normexprmin', _mE, _mc, _mF, mm.group(2) == '<']
                if pr not in cons.setdefault('_pairs', []):
                    cons['_pairs'].append(pr)
                _mEvv = {x for x in _mEv if out.get(x) in ("C", "R")}
                if len(_mEvv) == 1:
                    pr = ['normexpr', _mE, _mc, mm.group(2) == '<']
                    if pr not in cons.setdefault('_pairs', []):
                        cons['_pairs'].append(pr)
        # nonvanishing hypotheses on a compound EXPRESSION, `h : f x (y + c) ≠ 0` (a lone-
        # variable `x ≠ 0` is already the 'nonzero' flag; the per-binder regex above cannot
        # even SEE these — the parens inside the type break its grouping, so only this
        # paren-balanced scan reaches them). Recorded verbatim under '_nonzero' and honored
        # as a per-sample-point domain filter in sweep_eq (see _nonzero_ok): a point where a
        # hypothesized-nonzero expression numerically vanishes is a point the theorem
        # explicitly EXCLUDES — gating the claim there compares 0/0 cancellation noise
        # (theta_20_7_34's z = τ = 0.5+0.8i lattice zero of θ₂(·, τ+1/2)). Only expressions
        # the conclusion grammar itself can parse are recorded; anything else imposes no
        # filter (behavior unchanged).
        mm = re.fullmatch(r'(.+?)\s*≠\s*0', ty)
        if mm and re.search(r'\s', mm.group(1).strip()):     # compound expr, not a lone var
            expr = " ".join(mm.group(1).split())
            # a pure scalar CAST `(v : ℝ) ≠ 0` is a single-VARIABLE nonvanishing hypothesis:
            # register the existing per-variable 'nonzero' GRID flag (v sampled away from 0 —
            # dualHahn_one's `(N : ℝ) ≠ 0` keeps N ∈ {1,2,3,5,8} rather than dropping every
            # N = 0 combo post-hoc), never overwriting a stronger recorded flag.
            cast = re.fullmatch(r'\(\s*([A-Za-zα-ω]\w*)\s*:\s*[ℝℂℚ]\s*\)', expr)
            # coupled-nat Pochhammer nonvanishing `(ascPochhammer ℝ (n + k)).eval (-(N : ℝ)) ≠ 0`
            # (dual Hahn three-term recurrence, DLMF 18.22): for ℕ binders n, N the product
            # (−N)(−N+1)⋯(−N+n+k−1) vanishes exactly at N ∈ {0,…,n+k−1}, so the hypothesis is
            # EQUIVALENT to `n + k ≤ N` — record it as the same 'lepairoff' pair the literal
            # Krawtchouk form `hN : n + 2 ≤ N` produces, so the pre-cap in-hypothesis filter
            # sees it and the 24-combo cap is not exhausted on N-frozen out-of-domain points
            # (a spurious `undersampled` skip). Additive: the hypothesis is honored exactly
            # as stated; nothing loosened, and the expression stays under '_nonzero' too.
            poch = re.fullmatch(
                r'\(ascPochhammer\s+ℝ\s+\((\w+)\s*\+\s*(\d+)\)\)\.eval\s+'
                r'\(-\((\w+)\s*:\s*ℝ\)\)', expr)
            if cast:
                cons.setdefault(cast.group(1), 'nonzero')
            else:
                if poch and out.get(poch.group(1)) == "N" and out.get(poch.group(3)) == "N":
                    pr = ['lepairoff', poch.group(1), int(poch.group(2)), poch.group(3)]
                    if pr not in cons.setdefault('_pairs', []):
                        cons['_pairs'].append(pr)
                try:
                    parse(expr)
                    if expr not in cons.setdefault('_nonzero', []):
                        cons['_nonzero'].append(expr)
                except Exception:
                    pass                                     # unparseable → no filter
        # general two-expression nonequality `h : f(…) ≠ g(…)`, neither side the literal 0
        # (that is the `≠ 0` block above) and at least one side a COMPOUND expression the
        # lone-variable `distinct` pair-filter (`n ≠ m`) cannot see — e.g. the addition-law
        # genericity `hne : L.weierstrassP u ≠ L.weierstrassP v` (DLMF 23.10.1). It is
        # equivalent to `f − g ≠ 0`, so record the DIFFERENCE under '_nonzero' and let
        # _nonzero_ok DROP any sample where the two sides numerically COINCIDE — exactly the
        # points the theorem excludes. Without it the same C-grid feeds u and v, so the
        # diagonal u = v is always sampled; there ℘(u) − ℘(v) = 0 and the addition law's
        # RHS is a 0/0 quotient of cancellation noise (fabricating worst ≈ 1.3), a sample
        # OUTSIDE the stated hypothesis, not a DLMF discrepancy. Only parseable differences
        # impose a filter; anything else is a no-op. ADDITIVE and fail-safe: honors the
        # stated hypothesis exactly, drops only out-of-domain points (must still clear the
        # UNCHANGED tolerance on ≥ 2 in-domain samples, else it skips honestly), never
        # loosens a tolerance or scores a point.
        mm = re.fullmatch(r'(.+?)\s*≠\s*(.+)', ty)
        if mm:
            lhs_s, rhs_s = " ".join(mm.group(1).split()), " ".join(mm.group(2).split())
            if rhs_s != '0' and (re.search(r'\s', lhs_s) or re.search(r'\s', rhs_s)):
                diff = f"({lhs_s}) - ({rhs_s})"
                try:
                    parse(diff)
                    if diff not in cons.setdefault('_nonzero', []):
                        cons['_nonzero'].append(diff)
                except Exception:
                    pass                                     # unparseable → no filter
    # instance-binder primality hypothesis `[Fact p.Prime]` / `[Fact (Nat.Prime p)]` —
    # the bracketed Mathlib form (Legendre-symbol reciprocity, DLMF 27.9.3). The
    # per-binder regex above only opens on `(`/`{`/`⦃`, so a square-bracket instance
    # binder is invisible to it and p would draw from the unconstrained ℕ grid (mostly
    # non-primes → every sample honestly dropped → a spurious undersampled skip). Give
    # the variable the same 'prime' grid as the named `(hp : p.Prime)` form handled
    # above. Additive: sampling restricted to the stated hypothesis domain.
    for mm in re.finditer(r'\[\s*Fact\s+(?:\(\s*Nat\.Prime\s+([A-Za-zα-ω]\w*)\s*\)|'
                          r'([A-Za-zα-ω]\w*)\.Prime)\s*\]', head):
        _add_flag(cons, mm.group(1) or mm.group(2), 'prime')
    # norm-of-a-TRIG-EXPRESSION disc hypothesis `‖f(v)‖ < c` / `≤ c`, where the norm content
    # is an analytic EXPRESSION in one variable, not the bare variable — e.g. the DLMF
    # 15.4.8/15.4.10 Gauss-series disc `‖-(tan z) ^ 2‖ < 1` and the 15.4.12/15.4.14/15.4.16
    # disc `‖(sin z) ^ 2‖ < 1`. The per-binder regex above cannot see these: the norm content
    # carries inner parens `(tan z)`, so the paren-free binder-group scan never captures the
    # hypothesis at all (leaving z on the unconstrained ℂ grid). Scanned here directly off the
    # ‖…‖ delimiters (which never nest), tolerating those inner parens.
    #
    # That expression IS the ₂F₁ argument, so a sample with ‖f(v)‖ ≥ c sits OUTSIDE the
    # defining unit disc; there the RHS (a principal cpow of a trig base, e.g. (cos z)^{2a})
    # follows a DIFFERENT branch than the analytically continued ₂F₁, and scoring it fabricates
    # a branch-mismatch "counterexample" (worst ≈ 1) rather than a DLMF discrepancy. Honor the
    # stated hypothesis two ADDITIVE ways (sampling restricted to the stated domain only — no
    # grid loosening, no tolerance/scoring change):
    #   (a) a per-sample filter (`normexpr`) that DROPS any point with ‖f(v)‖ ≥ c, and
    #   (b) a curated in-disc complex grid for v (`trigdisk`) so the row is exercised rather
    #       than left undersampled (the default ℂ grid lands entirely OUTSIDE the |sin z| < 1
    #       disc, so the filter alone would drop every point → a misleading undersampled skip).
    for mm in re.finditer(r'[‖|]\s*([^‖|]+?)\s*[‖|]\s*(<|≤)\s*(\d+(?:\.\d+)?|\d+\s*/\s*\d+)\b',
                          head):
        _inner = mm.group(1)
        _tvars = re.findall(r'(?<![\w.])(?:sin|cos|tan|sinh|cosh|tanh)\s+([A-Za-zα-ω]\w*)',
                            _inner)
        if not (_tvars and len(set(_tvars)) == 1):
            continue                               # not a single-variable trig disc → leave as-is
        _rad = _const_val(mm.group(3))
        if _rad is None:
            continue
        _tv = _tvars[0]
        if out.get(_tv) not in ("C", "R", None):   # only for a scalar disc variable
            continue
        try:                                        # confirm the expression parses/evals
            P(tokenize(_inner)).expr()
        except Exception:
            continue
        _pr = ['normexpr', _inner, _rad, mm.group(2) == '<']
        if _pr not in cons.setdefault('_pairs', []):
            cons['_pairs'].append(_pr)
        if out.get(_tv) == "C":                    # curated in-disc grid only for a ℂ variable
            cons.setdefault(_tv, ('trigdisk', _rad))
    # GENERAL single-variable norm-EXPRESSION disc `‖f(v)‖ < c` / `≤ c`, f not a bare
    # variable (that is the `unit`/`cdisk` flag) and not already covered by the trig block
    # above or the `Complex.I`/`Real.sqrt`-centred block earlier. The Gauss quadratic
    # transformations state their disc on the ₂F₁ ARGUMENT, not on the variable:
    # hypergeometric_15_4_7 binds `hz : ‖z ^ 2‖ < 1` and 15_4_11 binds `hz : ‖-(z ^ 2)‖ < 1`,
    # neither of which any earlier rule sees — so z drew the default ℂ grid and the row was
    # scored at arguments OUTSIDE the stated disc, where the Lean `₂F₁` is its junk 0 and the
    # closed-form RHS is not. Recorded as the existing per-sample `normexpr` DROP filter
    # (_pairs_ok), with _domain_reject_grid supplying in-disc points if the default grid
    # starves. ADDITIVE: sampling restricted to the stated hypothesis; nothing loosened.
    for mm in re.finditer(r'[‖|]\s*([^‖|]+?)\s*[‖|]\s*(<|≤)\s*([^\s,)]+)\s*(?:\)|,|$|\))',
                          head):
        _inner = " ".join(mm.group(1).split())
        if re.fullmatch(r'[A-Za-zα-ω]\w*', _inner):
            continue                               # bare ‖v‖ < c → the unit/cdisk flag
        if re.search(r'\b(?:sin|cos|tan|sinh|cosh|tanh)\b', _inner):
            continue                               # trig disc → handled above (curated grid)
        if 'Complex.arg' in _inner or re.search(r'\bph\b', _inner):
            continue                               # |ph z| < θ → the dedicated 'argwedge' rule
        _rad = _const_expr_val(mm.group(3))
        if _rad is None or _rad <= 0:
            continue
        try:
            _iast = P(tokenize(_inner)).expr()
            _ifv = set(); collect_free(_iast, _ifv)
        except Exception:
            continue
        _ivv = {x for x in _ifv if out.get(x) in ("C", "R")}
        if not _ivv or _ifv - _ivv:                # only declared scalar variables may occur
            continue
        try:                                       # the filter must be EVALUABLE, else it would
            abs(evaluate(_iast, {x: (mp.mpc("0.3", "0.2") if out.get(x) == "C"
                                     else mp.mpf("0.3")) for x in _ivv}))
        except Exception:                          # drop every sample point and starve the row
            continue
        _pr = ['normexpr', _inner, _rad, mm.group(2) == '<']
        if _pr not in cons.setdefault('_pairs', []):
            cons['_pairs'].append(_pr)
    # `_flags` (see _add_flag) is kept ONLY for variables that actually carry ≥2 domain
    # hypotheses — the ones whose extra flags the grid must still enforce. Pruning the
    # single-flag entries keeps every one-hypothesis row's `constraints` dict BYTE-
    # IDENTICAL to before this change, so its `fidelity_cache.tier1_hash` (which hashes
    # constraints) is unchanged and its cached verdict stays valid.
    _fl = cons.get('_flags')
    if _fl is not None:
        multi = {v: fs for v, fs in _fl.items() if len(fs) > 1}
        if multi:
            cons['_flags'] = multi
        else:
            del cons['_flags']
    return out, cons


def _toplevel_binder_groups(head):
    """Yield the content of each TOP-LEVEL `( … )`/`{ … }`/`⦃ … ⦄` binder group in `head`,
    tracking nesting so an inner `(Real.sqrt 2 / 2)` does not terminate the group early."""
    opens, closes = "({⦃", ")}⦄"
    i, n = 0, len(head)
    while i < n:
        if head[i] in opens:
            depth, j = 1, i + 1
            while j < n and depth > 0:
                if head[j] in opens:
                    depth += 1
                elif head[j] in closes:
                    depth -= 1
                j += 1
            yield head[i + 1:j - 1]
            i = j
        else:
            i += 1


# ════════════════════════ 2. TOKENIZE + PARSE the conclusion ════════════════
TOKEN_RE = re.compile(r"""
    (?P<num>\d+\.\d+[eE][+-]?\d+|\d+[eE][+-]?\d+|\d+\.\d+|\d+)
  | (?P<eval>\.eval\b)
  | (?P<inv>⁻¹)
  | (?P<onefone>₁F₁)
  | (?P<twofone>₂F₁)
  | (?P<dfact>‼)
  | (?P<cardset>\#\{)
  | (?P<rbrace>\})
  | (?P<veclit>!\[)
  | (?P<bang>!)
  | (?P<lfloor>⌊)
  | (?P<rfloor>⌋₊|⌋)
  | (?P<dotdot>\.\.)
  | (?P<dotm>\.[A-Za-z_][A-Za-z0-9_'₀-₉]*)
  | (?P<partial>∂)
  | (?P<lbrack>\[)
  | (?P<rbrack>\])
  | (?P<sum>∑'|∑)
  | (?P<prod>∏'|∏)
  | (?P<intg>∫)
  | (?P<mem>∈)
  | (?P<arrow>=>|↦)
  | (?P<tarrow>→)
  | (?P<sqrtsym>√)
  | (?P<dbar>‖)
  | (?P<bar>\|)
  | (?P<nhds>𝓝\[>\]|𝓝\[<\]|𝓝\[≥\]|𝓝\[≤\]|𝓝\[≠\]|𝓝)
  | (?P<asymp>∼|~)
  | (?P<ne>≠)
  | (?P<rel>≤|≥|<|>)
  | (?P<forall>∀)
  | (?P<exists>∃)
  | (?P<land>∧)
  | (?P<cdot>·)
  | (?P<prodtype>×)
  | (?P<mod>%)
  | (?P<op>[=+\-*/^,():•])
  | (?P<coe>↑|↗)
  | (?P<fourier>𝓕)
  | (?P<id>[A-Za-zα-ωΑ-Ωℝℕℤℂℚ℘ℓ_][\w'′₀-₉ℓ]*(?:\.[\w'′₀-₉ℓ]+)*)
  | (?P<ws>\s+)
""", re.X)


class Unparseable(Exception):
    pass


def _unbound_head_of(exc):
    """If an Unparseable reports a head with no oracle binding (`unbound head NAME`,
    `free symbol NAME`), return NAME so the skip is labelled `unbound:NAME` honestly
    instead of the misleading `undersampled/domain`. Otherwise None."""
    s = str(exc)
    for pre in ("unbound head ", "free symbol "):
        if s.startswith(pre):
            return s[len(pre):].strip()
    return None


# identifier tokens that must STOP juxtaposition-argument collection — they are
# keywords (`if x then a else b`, `∫ … in …`), not operands of an application.
_KEYWORDS = {"then", "else", "in", "by", "if"}


def tokenize(s):
    toks, i = [], 0
    while i < len(s):
        m = TOKEN_RE.match(s, i)
        if not m:
            raise Unparseable(f"char {s[i]!r}")
        i = m.end()
        if m.lastgroup == "ws":
            continue
        toks.append((m.lastgroup, m.group()))
    return toks


# AST nodes are tuples: ('num',v) ('var',name) ('app',head,[args]) ('eval',P,a)
#   ('bin',op,L,R) ('neg',E) ('inv',E) ('sum',startguess,var,body)
class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def eat(self, val=None):
        k, v = self.peek()
        if val and v != val:
            raise Unparseable(f"expected {val} got {v}")
        self.i += 1
        return v

    _TYPEMAP = {"ℕ": "N", "ℤ": "Z", "ℝ": "R", "ℂ": "C", "ℍ": "H"}

    def forall_binders(self, allow_fn=False, mems=None, default_ty=None):
        """Consume `∀ v₁ v₂ : T (w : S) , …` binders → {name: domaincode}; stop at the
        first comma. Anything unexpected (e.g. a `→` implication) aborts the parse.

        ADDITIVE options (defaults keep every existing call site byte-identical):
        - `allow_fn`: accept a FUNCTION-typed binder `P : ℤ → ℂ` (exists-witness parse,
          e.g. the DLMF 20.5.14–17 iterated-limit profiles) → domaincode "fn".
        - `mems`: a list; accept a MEMBERSHIP binder `x ∈ Set.Ioo a b` (bounded-exists
          sugar, e.g. gamma_5_4_20_min) — the (name, set-node) pair is appended and the
          binder typed "R".
        - `default_ty`: type an UNTYPED trailing binder (`∀ x, …`) with this code instead
          of silently dropping it (used only by the new exists-body ∀ parse)."""
        binders, pending = {}, []
        while True:
            k, v = self.peek()
            if v == ",":
                self.eat()
                if pending and default_ty is not None:
                    for vn in pending:
                        binders[vn] = default_ty
                break
            if v == "(":
                self.eat()
                grp = []
                while self.peek()[1] not in (":", ")", None):
                    grp.append(self.eat())
                self.eat(":"); ty = self.eat()
                if allow_fn and self.peek()[0] == "tarrow":   # (w : ℂ → ℂ) function binder
                    self.eat(); self.eat()
                    ty_code = "fn"
                else:
                    ty_code = self._TYPEMAP.get(ty, "R")
                self.eat(")")
                for vn in grp:
                    binders[vn] = ty_code
            elif v == ":":
                self.eat(); ty = self.eat()
                if allow_fn and self.peek()[0] == "tarrow":   # `P : ℤ → ℂ` function binder
                    self.eat(); self.eat()
                    for vn in pending:
                        binders[vn] = "fn"
                else:
                    for vn in pending:
                        binders[vn] = self._TYPEMAP.get(ty, "R")
                pending = []
            elif k == "mem" and mems is not None and pending:
                # `x ∈ <set-expr>` membership binder (∃-sugar): record (name, set-node);
                # the caller desugars it into explicit bound conjuncts.
                self.eat()
                setnode = self.app()
                for vn in pending:
                    binders[vn] = "R"
                    mems.append((vn, setnode))
                pending = []
            elif k == "id":
                pending.append(self.eat())
            else:
                raise Unparseable("forall binder")
        return binders

    def _asymp_filter(self):
        """Consume `[atTop]` / `[atBot]` after ~ / =O / =o; return the filter name."""
        self.eat()                              # [
        filt = self.eat()
        self.eat()                              # ]
        return filt

    def _int_cast_range(self):
        """Recognize `Set.range ((↑) : ℤ → ℚ)` (also an explicit `Int.cast`/`Nat.cast`
        head) right after `∈` — the image of the integer (natural) cast, i.e. the
        'e is an integer' membership predicate (von Staudt–Clausen, DLMF 24.10).
        On an exact match, consume the tokens and return ("intrange", "Z"|"N"); on ANY
        mismatch, consume NOTHING (position restored) so every other set-expression keeps
        its existing parse path. ADDITIVE: only Int/Nat casts are recognized — a field
        cast ascription (e.g. `(↑) : ℚ → ℝ`) falls through unchanged."""
        save = self.i
        try:
            if self.peek() != ("id", "Set.range"):
                raise Unparseable("not Set.range")
            self.eat()
            self.eat("(")
            ty = None
            if self.peek()[1] == "(":           # ((↑) : T → S) — the anonymous-coe form
                self.eat("(")
                if self.peek()[0] != "coe":
                    raise Unparseable("not a coe")
                self.eat()
                self.eat(")")
            elif self.peek() in (("id", "Int.cast"), ("id", "Nat.cast")):
                ty = "Z" if self.eat() == "Int.cast" else "N"
            else:
                raise Unparseable("not a cast")
            if self.peek()[1] == ":":           # type ascription `: ℤ → ℚ`
                self.eat(":")
                src = self.eat()
                if self.peek()[0] != "tarrow":
                    raise Unparseable("cast ascription")
                self.eat()                      # →
                self.eat()                      # target type
                ty = {"ℤ": "Z", "ℕ": "N"}.get(src, ty)
            self.eat(")")
            if ty is None:
                raise Unparseable("cast source type unknown")
            return ("intrange", ty)
        except Unparseable:
            self.i = save
            return None

    # relation:  expr (('=' | '≤' | '<' | '≥' | '>' | '~[f]' | '=O[f]' | '=o[f]') expr)?
    def relation(self):
        L = self.expr()
        if self.peek()[0] == "asymp":           # f ~[filter] g  — IsEquivalent (ratio → 1)
            self.eat()
            filt = self._asymp_filter()
            return ("asymp", "~", L, filt, self.expr())
        if self.peek()[1] == "=":
            self.eat("=")
            # `=O[filter]` / `=o[filter]` — IsBigO / IsLittleO (Landau notation)
            if self.peek()[1] in ("O", "o") and self.i + 1 < len(self.t) \
                    and self.t[self.i + 1][0] == "lbrack":
                kind = self.eat()
                filt = self._asymp_filter()
                return ("asymp", kind, L, filt, self.expr())
            return ("eq", L, self.expr())
        if self.peek()[0] == "ne":             # L ≠ R — refute only on a sampled |L−R| ≈ 0
            self.eat()
            return ("ne", L, self.expr())
        if self.peek()[0] == "rel":
            op = self.eat()
            return ("ineq", op, L, self.expr())
        if self.peek()[0] == "mem":            # e ∈ <set-expr> (interval membership)
            self.eat()
            rng = self._int_cast_range()
            if rng is not None:                # e ∈ Set.range ((↑) : ℤ/ℕ → _) — integrality
                return ("mem", L, rng)
            return ("mem", L, self.expr())
        # a PARENTHESIZED complete relation — `(L = R) ∧ …` (theta_20_5_9–13's first
        # conjuncts, Ch20Products.lean): atom()'s '(' handler recursed into relation(),
        # the finished ('eq', …) node propagated back up the expr chain unchanged and
        # lands here as `L`; blindly re-wrapping it ("expr", ('eq', …)) hides the
        # conjunct from the ∧-dispatcher in classify_and_check (which recognizes only
        # bare 'eq'/'ineq'/… conjuncts) → a silent 'unable to proceed'. Return the
        # already-complete relation node itself. Tendsto/HasDerivAt/HasSum conjuncts
        # parse to ('app', …) heads — not in this set — so their ("expr", …) wrap
        # (relied on by the ∧-dispatcher) is untouched. ADDITIVE: fires only when the
        # whole expression chain reduced to a bare relation tuple.
        if L[0] in ("eq", "ineq", "asymp", "mem", "ne"):
            return L
        return ("expr", L)

    def expr(self):  # + -
        node = self.term()
        while self.peek()[1] in ("+", "-"):
            op = self.eat()
            node = ("bin", op, node, self.term())
        return node

    def term(self):  # * / • %   (· is NOT multiply — it is the cdot section placeholder)
        node = self.power()
        while self.peek()[0] == "mod" or self.peek()[1] in ("*", "/", "•"):
            op = self.eat()
            op = "*" if op == "•" else op
            node = ("bin", op, node, self.power())
        return node

    def power(self):  # ^  (right assoc), unary minus
        if self.peek()[1] == "-":
            self.eat("-")
            return ("neg", self.power())
        base = self.postfix()
        if self.peek()[1] == "^":
            self.eat("^")
            if self.peek()[0] == "lbrack":      # f ^[n] arg — Function.iterate (formal d/dX iterate)
                self.eat()
                n = self.expr()
                if self.peek()[0] != "rbrack":
                    raise Unparseable("iterate close")
                self.eat()
                # `(OP^[n])` parenthesised on its own with NO inline argument — the iterate is
                # applied later by juxtaposition (DLMF 15.5.3/5/7/8/10: `(zDerivZ^[n]) g z`).
                # Previously self.power() ran straight into the closing `)` and raised
                # `unparsed:atom ')'`. Hand the operator back as a first-class ("iterop", n, base)
                # node so app() collects the trailing (g, z) as its arguments. ADDITIVE: fires
                # only when the argument is absent; the inline `deriv^[n] f x` path is unchanged.
                if self.peek()[1] == ")":
                    return ("iterop", n, base)
                return ("iterderiv", n, self.power(), base)
            return ("bin", "^", base, self.power())
        return base

    def _apply_postfix(self, node):
        """Apply ONE tight postfix operator (.eval / ⁻¹ / ! / ‼ / .method args) to `node`,
        returning (new_node, consumed). Shared by `postfix()` and argument-atom collection so
        a postfix on a function ARGUMENT (`(Γ z)⁻¹`, `(ψ w).im`) binds to that argument, not
        to the enclosing application."""
        k, v = self.peek()
        if k == "eval":
            self.eat()
            return ("eval", node, self.atom()), True
        if k == "inv":
            self.eat()
            return ("inv", node), True
        if k == "bang":             # `n !` → factorial (postfix); routes to DOT0['factorial']
            self.eat()
            return ("dotm", node, "factorial", []), True
        if k == "dfact":            # `n ‼` → double factorial (postfix); DOT0['dfactorial']
            self.eat()
            return ("dotm", node, "dfactorial", []), True
        if k == "dotm":             # (e).method args — postfix on a closed expression
            self.eat()
            mname = v[1:]
            args = []
            while self.peek()[0] in ("id", "num", "coe", "sqrtsym") or self.peek()[1] == "(":
                args.append(self.atom())
            if mname == "comp" and len(args) == 1:
                # (P).comp Q — polynomial composition: P with its indeterminate := Q,
                # which is EXACTLY the `eval` node's semantics (Q supplies the new X)
                return ("eval", node, args[0]), True
            return ("dotm", node, mname, args), True
        return node, False

    def postfix(self):  # application / .eval / ⁻¹ / .method
        node = self.app()
        while True:
            node, did = self._apply_postfix(node)
            if not did:
                return node

    def _atom_postfix(self):
        """One atom WITH its tight postfixes — a Finset bound like `(p / 2).succ`
        (Gauss's lemma, DLMF 27.9) needs the `.succ` applied to the parenthesised
        atom. Used only by the new countset parser; existing atom() call sites are
        untouched."""
        a = self.atom()
        while True:
            a, did = self._apply_postfix(a)
            if not did:
                return a

    def app(self):  # head applied to tight atoms (juxtaposition)
        head = self.atom()
        # bracket-indexed notation: P[l] (legendre), Q[m] (legendreQ), P[n,m] (assocLegendre).
        # The indices become a synthetic head `P[]`/`P[,]`/`Q[]`, trailing args follow.
        sym = None
        bracket = []
        if head[0] == "var" and self.peek()[0] == "lbrack":
            self.eat()
            bracket = [self.expr()]
            while self.peek()[1] == ",":
                self.eat(",")
                bracket.append(self.expr())
            if self.peek()[0] != "rbrack":
                raise Unparseable("bracket close")
            self.eat()
            sym = head[1] + "[" + "," * (len(bracket) - 1) + "]"
        args = []
        # "lfloor" is an argument starter: `apPrimeSum a ⌊x⌋₊` / `Nat.primeCounting ⌊x⌋₊`
        # (DLMF 27.11.11 / 6.16.5) apply a head to a floor atom by juxtaposition — atom()
        # already parses ⌊·⌋/⌊·⌋₊, it was just never collected as a tight argument.
        # "bar" is an argument starter too: `Real.log |x|` (expint_6_10_6, DLMF 6.10.6)
        # applies a head to an abs-atom by juxtaposition — atom() already parses |·|, it
        # was just never collected as a tight argument (the head stayed a bare var and
        # the row skipped as unbound). GUARDED by _bar_depth: inside an open |…| group
        # the next '|' is that group's CLOSER, never a new argument.
        while ((self.peek()[0] in ("id", "num", "coe", "nhds", "sqrtsym", "veclit", "onefone",
                                   "cdot", "lfloor")
                and self.peek()[1] not in _KEYWORDS) or self.peek()[1] == "("
               or (self.peek()[0] == "bar" and not getattr(self, "_bar_depth", 0))):
            a = self.atom()
            # tight postfix on the ARGUMENT atom: a function argument `(Γ z)⁻¹` / `n !` /
            # `(ψ w).im` binds the postfix to the atom, NOT to the whole application. Without
            # this the `⁻¹` of `HasSum f (Γ z)⁻¹` (or the `.im` of a digamma RHS) leaks up to
            # wrap the entire `HasSum (…)` app, dropping it from the RHS (a silently-wrong
            # second argument that then fails the HasSum/HasProd head-dispatch).
            while True:
                a, did = self._apply_postfix(a)
                if not did:
                    break
            if a[0] == "typearg":   # named type argument `(R := ℂ)` — elaboration data
                continue            # only, never a numeric operand (see atom())
            args.append(a)
        if sym is not None:
            return ("app", ("var", sym), bracket + args)
        return ("app", head, args) if args else head

    def atom(self):
        k, v = self.peek()
        # `J( a | n )` — FLMF Jacobi-symbol notation (DLMF 27.9). Intercept before the
        # generic '(' path so the inner '|' is the argument separator, not abs-bars.
        if k == "id" and v == "J" and self.i + 1 < len(self.t) and self.t[self.i + 1][1] == "(":
            self.eat()
            self.eat("(")
            a = self.expr()
            self.eat("|")
            n = self.expr()
            self.eat(")")
            return ("app", ("var", "jacobiSym"), [a, n])
        if v == "(":
            self.eat("(")
            # parenthesized ∀-quantified RELATION `(∀ n : ℤ, Tendsto …)` — a conjunct of a
            # quantified conjunction (the DLMF 20.5.14–17 iterated-limit surfaces). Consumed
            # into a ("forallq", binders, relation) node ONLY when the body is a single
            # relation ending exactly at the ")": an implication (`1 ≤ k → …`) or any other
            # trailing tokens keep the honest Unparseable abort (so hypothesis-guarded inner
            # ∀-clauses, e.g. gamma_5_11_6's recurrence, are never half-parsed into a
            # fabricated check). ADDITIVE: `(∀ …` previously always failed at atom '∀'.
            if self.peek()[0] == "forall":
                self.eat()
                fb = self.forall_binders()
                inner = self.relation()
                if self.peek()[1] != ")":
                    raise Unparseable("forall-body unconsumed")
                self.eat(")")
                return ("forallq", fb, inner)
            # named TYPE argument `(R := ℂ)` (Lean named-instance syntax, e.g.
            # `constantCoeff (R := 𝕂) …` after the 𝕂 ↦ ℂ instantiation): without this
            # the `:`-ascription path below misreads it as a cast of the free variable
            # `R` — a phantom `unbound:R`. Recognize exactly `(<id> := <type-token>)`
            # and hand back the bare type atom (the application layer already skips
            # type-name arguments); ANY other named-argument value stays an honest
            # Unparseable skip. ADDITIVE: `(x : T)` ascriptions have no `=` after `:`.
            if (self.i + 2 < len(self.t) and self.t[self.i][0] == "id"
                    and self.t[self.i + 1][1] == ":" and self.t[self.i + 2][1] == "="):
                self.eat(); self.eat(":"); self.eat("=")
                val = self.expr()
                self.eat(")")
                if val[0] == "var" and val[1] in ("ℝ", "ℂ", "ℕ", "ℤ", "ℚ"):
                    # hand back a dedicated ("typearg", …) marker — the application
                    # layer DROPS it (a named TYPE argument is elaboration data, not a
                    # numeric operand; returning the bare type atom leaked a free `ℂ`
                    # var into the sweep → heunSeries_constantCoeff's `unbound:ℂ`).
                    return ("typearg", val[1])
                raise Unparseable("named argument")
            node = self.relation()
            # type ascription (e : T) — drop the type, but REMEMBER when T is a real/complex
            # field. A `(n : ℝ)` cast (Gauss-multiplication half-power `(2π)^((n−1)/2)`, the
            # repeated-erfc prefactor `2^((n−1)/2)`) makes the subterm real-valued, so any `/`
            # inside it is REAL division — NOT the Nat/Int floor `/` of `(-1)^(m/2)`. Tokens
            # past the `:` are the type; if it names a non-integer field, wrap in ("real", …)
            # so `_all_int` / `_has_intvar` will not (mis)floor through the cast.
            real_cast = False
            zmod_tok = None
            princhar_tok = None
            if self.peek()[1] == ":":
                self.eat(":")
                asc_toks = []
                depth = 0                     # nested parens inside the ascribed TYPE,
                while self.peek()[1] is not None and \
                        not (depth == 0 and self.peek()[1] == ")"):   # e.g. MulChar (ZMod k) ℂ
                    if self.peek()[1] == "(":
                        depth += 1
                    elif self.peek()[1] == ")":
                        depth -= 1
                    asc_toks.append(self.peek()[1])
                    self.eat()
                # principal-character ascription `(1 : DirichletCharacter ℂ k)` (or the
                # unbundled `(1 : MulChar (ZMod k) ℂ)`): the numeral 1 of the character
                # monoid is the PRINCIPAL character mod k — DLMF 27.8.1's χ₁, defined by
                # χ₁(a) = 1 if gcd(a, k) = 1 else 0 (Mathlib `MulChar.one_apply` +
                # `map_nonunit`). Dropping the type (the default below) left the applied
                # head `(1) a` non-callable, so principal_apply_eq_one (DLMF 27.8.5)
                # skipped as undersampled/domain. Keep the modulus as a ("princhar", k)
                # head; the application evaluates by the defining gcd formula (see
                # evaluate's princhar branch), with (k, a) sampled by the existing
                # ZMod/IsUnit machinery. Only the literal-1 value with a single-token
                # modulus is modelled — any other ascription keeps its existing path.
                _idtok = r"[^\W\d]\w*|\d+"
                if (len(asc_toks) == 3 and asc_toks[0] == "DirichletCharacter"
                        and asc_toks[1] == "ℂ" and re.fullmatch(_idtok, asc_toks[2])):
                    princhar_tok = asc_toks[2]
                elif (len(asc_toks) == 6 and asc_toks[0] == "MulChar"
                        and asc_toks[1:3] == ["(", "ZMod"]
                        and re.fullmatch(_idtok, asc_toks[3])
                        and asc_toks[4:] == [")", "ℂ"]):
                    princhar_tok = asc_toks[3]
                # a `ZMod n` target: the ascribed value lives in ℤ/nℤ, so an equality on it
                # is a CONGRUENCE mod n. Dropping the cast (the default below) would compare
                # the two sides as real numbers — legendreSym_eq_pow (Euler's criterion,
                # `(legendreSym p a : ZMod p) = (a : ZMod p)^(p/2)`): at p=5, a=2 the claim
                # is -1 ≡ 4 (mod 5), TRUE, but -1 ≠ 4 as reals — a fabricated FAIL of a
                # Mathlib-proven statement. Remedy: keep the cast as a `("zmodcast", n, e)`
                # node — the operand evaluates as its ℤ-lift and sweep_eq scores the
                # equality as the congruence `L ≡ R (mod n)` (exact-integer gate, see the
                # zmod branch there). Only the simple `ZMod <var|literal>` shape is
                # modelled; any other modulus expression keeps the honest skip — the
                # reason stays visible, never a fabricated verdict.
                if princhar_tok is None and any(t == "ZMod" for t in asc_toks):
                    if len(asc_toks) == 2 and re.fullmatch(r"[^\W\d]\w*|\d+", asc_toks[1]):
                        zmod_tok = asc_toks[1]
                    else:
                        raise Unparseable("ZMod cast (unsupported modulus shape)")
                # a real/complex/rational target field (never ℕ/ℤ); integer targets keep
                # the bare node so genuine Nat floor-`/` (`(-1)^(m/2)`) is unaffected.
                # (a princhar match keeps its own node — the ℂ there is the character's
                # CODOMAIN, not a scalar cast of the ascribed value.)
                # a FUNCTION-type ascription `(₂F₁ a b c : ℂ → ℂ)` (the scalar-polymorphic
                # `(f : 𝕂 → 𝕂)` spelling after 𝕂 ↦ ℂ) ascribes the function itself, not a
                # scalar value: wrapping it as a scalar ("real", …) cast breaks every
                # function-position consumer (`deriv`, `HasDerivAt` — the operand stopped
                # looking like an application head). Drop the type entirely instead —
                # exactly what Lean's elaborator does with the ascription. Scalar casts
                # (no `→` in the type) keep the existing real-cast wrap unchanged.
                if princhar_tok is None and "→" not in asc_toks and \
                        any(t in ("ℝ", "ℂ", "ℚ", "Real", "Complex", "Rat",
                                  "NNReal", "ℝ≥0", "EReal", "ENNReal", "ℝ≥0∞") for t in asc_toks):
                    real_cast = True
            self.eat(")")
            node = node[1] if node[0] == "expr" else node
            if princhar_tok is not None:
                if node != ("num", 1):        # only the character-monoid numeral 1 is the
                    raise Unparseable("character ascription (non-principal)")   # principal χ₁
                node = ("princhar", princhar_tok)
            if real_cast:
                node = ("real", node)
            if zmod_tok is not None:
                node = ("zmodcast", zmod_tok, node)
            # cdot section: a parenthesised term containing the `·` placeholder is an anonymous
            # function `fun · => …` (e.g. `(jacobiTheta₂' · τ)` = fun x ↦ jacobiTheta₂' x τ).
            if _has_cdot(node):
                return ("lam", "·", node)
            return node
        if k == "cardset":
            # `#{x ∈ Ico lo hi | pred}` — Lean sugar for `(Finset.filter pred (Ico lo hi)).card`,
            # a filtered integer COUNT (Gauss's lemma μ, DLMF 27.9). The bound var ranges over
            # the ℕ-Finset (Ico half-open → inclusive lo..hi−1, same convention as _agg_expr);
            # the predicate is a single relation on the bound var. Anything else (a different
            # range head, a non-relational predicate) keeps the honest Unparseable skip.
            self.eat()
            if self.peek()[0] != "id":
                raise Unparseable("countset binder")
            var = self.eat()
            if self.peek()[0] != "mem":
                raise Unparseable("countset '∈'")
            self.eat()
            rng = self.eat()                # Ico / Icc / Ioc / range (Finset.-qualified or not)
            if "range" in (rng or ""):      # range N → 0 .. N−1
                N = self._atom_postfix()
                lo, hi = ("num", 0), ("bin", "-", N, ("num", 1))
            elif "Icc" in (rng or ""):      # Icc a b → a .. b
                lo = self._atom_postfix()
                hi = self._atom_postfix()
            elif "Ico" in (rng or ""):      # Ico a b → a .. b−1 (half-open)
                lo = self._atom_postfix()
                b = self._atom_postfix()
                hi = ("bin", "-", b, ("num", 1))
            elif "Ioc" in (rng or ""):      # Ioc a b → a+1 .. b
                a = self._atom_postfix()
                lo = ("bin", "+", a, ("num", 1))
                hi = self._atom_postfix()
            else:
                raise Unparseable(f"countset finset {rng}")
            self.eat("|")
            pred = self.relation()
            if self.peek()[0] != "rbrace":
                raise Unparseable("countset close")
            self.eat()
            return ("countset", var, lo, hi, pred)
        if k == "cdot":                     # the `·` placeholder, standing for the bound var
            self.eat()
            return ("var", "·")
        if k == "onefone":                  # ₁F₁ a b z — Kummer M head (a synthetic var head)
            self.eat()
            return ("var", "₁F₁")
        if k == "twofone":                  # ₂F₁ a b c z — Gauss hypergeometric head
            self.eat()
            return ("var", "₂F₁")
        if k == "veclit":                   # ![a, b, …] / ![] — Lean vector literal → ('vec', [..])
            self.eat()
            elems = []
            if self.peek()[0] != "rbrack":
                elems.append(self.relation())
                while self.peek()[1] == ",":
                    self.eat(",")
                    elems.append(self.relation())
            if self.peek()[0] != "rbrack":
                raise Unparseable("vector-literal close")
            self.eat()
            return ("vec", elems)
        if k == "coe":
            # `↑e` — a numeric coercion, transparent for evaluation. Also `↗f` (Mathlib
            # LSeries.notation): `↗f = fun n => ((f n : ℝ/ℤ) : ℂ)`, i.e. the arithmetic
            # function f under a value-preserving cast — numerically the plain f.
            self.eat()
            return self.atom()
        if k == "sqrtsym":                  # √ e  → Real.sqrt e
            self.eat()
            return ("app", ("var", "Real.sqrt"), [self.atom()])
        if k == "lfloor":                   # ⌊e⌋₊ — Nat.floor (clamped at 0) / ⌊e⌋ — Int.floor
            self.eat()
            e = self.expr()
            if self.peek()[0] != "rfloor":
                raise Unparseable("floor close")
            close = self.eat()
            return ("floor", "nat" if close == "⌋₊" else "int", e)
        if k == "bar":                      # |e|  → abs e
            self.eat()
            # track bar nesting so the application-argument collector (app()) never
            # mistakes THIS group's CLOSING '|' for a fresh abs-open (else `|f x|`
            # would consume its own closing bar as a new argument).
            self._bar_depth = getattr(self, "_bar_depth", 0) + 1
            try:
                e = self.expr()
            finally:
                self._bar_depth -= 1
            self.eat("|")
            return ("app", ("var", "abs"), [e])
        if k == "dbar":                     # ‖e‖  → norm = abs on ℝ/ℂ scalars
            self.eat()
            e = self.expr()
            self.eat("‖")
            return ("app", ("var", "abs"), [e])
        if k == "nhds":                     # 𝓝 a / 𝓝[>] a — neighbourhood filter
            self.eat()
            return ("nhds", v, self.atom())
        if k == "intg":
            return self.integral_expr()
        if k == "sum":
            return self.sum_expr()
        if k == "prod":
            return self.prod_expr()
        if k == "num":
            self.eat()
            return ("num", float(v) if ("." in v or "e" in v or "E" in v) else int(v))
        if k == "id":
            if v in ("fun", "λ"):           # fun x : T => body  /  λ x ↦ body
                return self.lambda_expr()
            if v == "if":                   # if cond then a else b
                return self.ite_expr()
            self.eat()
            if v == "X":
                return ("var", IND)
            return ("var", v)
        if k == "fourier":                  # 𝓕 — Fourier-transform operator (applied to a fn)
            self.eat()
            return ("var", "𝓕")
        raise Unparseable(f"atom {v!r}")

    def ite_expr(self):
        self.eat()                          # if
        cond = self.relation()
        # conjunctive condition `if m = 0 ∧ n = 0 then …` (the DLMF 20.5.14 double-product
        # center exclusion) → ("condand", c₁, c₂) nodes, decided by _cond_true as a plain
        # boolean AND. ADDITIVE: a ∧ here previously aborted at "ite 'then'".
        while self.peek()[0] == "land":
            self.eat()
            cond = ("condand", cond, self.relation())
        if self.peek()[1] != "then":
            raise Unparseable("ite 'then'")
        self.eat()
        a = self.expr()
        if self.peek()[1] != "else":
            raise Unparseable("ite 'else'")
        self.eat()
        return ("ite", cond, a, self.expr())

    def lambda_expr(self):
        self.eat()                          # fun / λ
        if self.peek()[1] == "(":           # parenthesized binder: fun (x : T) ↦ …
            self.eat()
        var = self.eat()                    # first binder name
        extras, typed = [], False           # EXTRA binder names of an untyped multi-binder
        while self.peek()[1] not in ("=>", "↦", None):   # lambda (`fun p k => …`, the
            t = self.eat()                  # Finsupp.prod shape); a ':' starts a type
            if t == ":":                    # annotation — everything after it is skipped
                typed = True                # exactly as before
            elif not typed and t not in ("(", ")"):
                extras.append(t)
        self.eat()                          # the arrow
        body = self.expr()
        # extra binders ride along as an OPTIONAL 4th element (existing consumers index
        # [0]/[1]/[2] only, so single-binder lambdas — and their handling — are unchanged);
        # collect_free discards them and the Finsupp.prod evaluator binds them.
        return ("lam", var, body, tuple(extras)) if extras else ("lam", var, body)

    def sum_expr(self):
        return self._agg_expr("fsum", "sum")

    def prod_expr(self):
        return self._agg_expr("fprod", "prod")

    def _agg_expr(self, finite_tag, infinite_tag):
        # ∑/∏ k ∈ range N | Finset.Icc a b , body   (finite, INCLUSIVE lo..hi bounds)
        # ∑'/∏' n : T , body  (infinite — the index type is KEPT: aggregating a
        # ℤ/Primes/lattice-indexed family over [0,∞) would fabricate a different value)
        tok = self.eat()                             # ∑ / ∑' / ∏ / ∏' — SPELLING kept on the
        # bare no-∈ form (5th node slot): Lean's bare `∑ x, body` is a Finset.univ sum over
        # a FINITE carrier (an infinite ℕ-series is always spelled `∑'`), so the evaluator
        # must not aggregate it over [0,∞) — see the univ-sum case in evaluate's "sum".
        var = "n"
        if self.peek()[0] == "id":
            var = self.eat()
        if self.peek()[0] == "mem":
            self.eat()
            rng = self.eat()                         # 'range' / 'Finset.range' / 'Finset.Icc'
            if rng and rng.endswith(".divisors"):    # ∑/∏ d ∈ n.divisors, body
                return (finite_tag + "set", "divisors", rng[:-len(".divisors")],
                        var, self._agg_body())
            if rng and rng.endswith(".primeFactors"):
                return (finite_tag + "set", "primeFactors", rng[:-len(".primeFactors")],
                        var, self._agg_body())
            if rng and rng.endswith(".divisorsAntidiagonal"):  # ∑ x ∈ n.divisorsAntidiagonal
                base = ("var", rng[:-len(".divisorsAntidiagonal")])
                return ("pairagg", finite_tag, "divantidiag", base, var, self._agg_body())
            if rng in ("Finset.antidiagonal", "antidiagonal"):  # ∑ ij ∈ Finset.antidiagonal n
                return ("pairagg", finite_tag, "antidiag", self.atom(), var, self._agg_body())
            if rng in ("Nat.primesLE", "primesLE"):
                # ∑/∏ p ∈ Nat.primesLE B, body — the primes p ≤ B (FLMF `Nat.primesLE n =
                # (Finset.Icc 0 n).filter Nat.Prime`, the Mertens surfaces DLMF 27.11.8/10).
                # The bound is an atom-with-postfix so `⌊x⌋₊` parses. Enumerated by an exact
                # sieve in evaluate (capped — an oversized bound raises → honest point drop).
                B = self._atom_postfix()
                self.eat(",")
                return (finite_tag + "primes", var, B, self.term())
            if rng in ("Finset.univ.filter", "univ.filter"):
                # ∏/∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), body —
                # the ordered pairs 0 ≤ i < j ≤ k−1 (the DLMF 5.13.5 de Branges–Wilson
                # product). ONLY the exact `p.1 < p.2` predicate over `Fin k × Fin k` (k a
                # literal) is modelled; any other filter keeps the honest Unparseable skip.
                self.eat("(")
                if self.peek() not in (("id", "fun"), ("id", "λ")):
                    raise Unparseable("univ.filter lambda")
                self.eat()
                pv = self.eat()
                if self.peek()[0] == "arrow":
                    # UNANNOTATED single-index filter `∏/∑ k ∈ Finset.univ.filter
                    # (fun k => j < k), body` over the ambient `Fin n` carrier (the pair
                    # product of the DLMF 31.15.12 Stieltjes weight, where the binder type
                    # is inferred in Lean and never written). The filter is kept as a
                    # PREDICATE node, decided per index by the same `_pred_holds` the
                    # countset path uses — no predicate shape is privileged, and an index
                    # whose predicate cannot be decided raises → honest point drop. The
                    # carrier size comes from the row's own data (a `.q`-tagged Fin-vector
                    # applied to the bound index in the body), exactly as for a bare
                    # `∏ k, …`; no carrier in scope ⇒ Unparseable, never a guessed range.
                    self.eat()
                    fpred = self.relation()
                    self.eat(")")
                    self.eat(",")
                    return ("funivfilter", finite_tag, var, pv, fpred, self.term())
                if self.eat() != ":":
                    raise Unparseable("univ.filter binder type")
                if self.eat() != "Fin":
                    raise Unparseable("univ.filter Fin")
                k1 = self.eat()
                if self.peek()[0] != "prodtype":
                    raise Unparseable("univ.filter product type")
                self.eat()
                if self.eat() != "Fin":
                    raise Unparseable("univ.filter Fin")
                k2 = self.eat()
                if self.peek()[0] != "arrow":
                    raise Unparseable("univ.filter arrow")
                self.eat()
                pred = self.relation()
                if not (pred[0] == "ineq" and pred[1] == "<"
                        and pred[2] == ("var", pv + ".1") and pred[3] == ("var", pv + ".2")
                        and k1 == k2 and k1 is not None and k1.isdigit()):
                    raise Unparseable("univ.filter predicate")
                self.eat(")")
                self.eat(",")
                return ("finpairs", finite_tag, int(k1), var, self.term())
            if rng in ("Finset.univ.erase", "univ.erase"):
                # ∑/∏ k ∈ Finset.univ.erase j, body — Finset.univ with the single index j
                # removed, i.e. Lean's spelling of DLMF's `Σ_{k=1, k≠j}^{N}` (31.14.5).
                # The erased index is an ordinary expression (a sampled `Fin N` binder);
                # the carrier size is read off the row's own `.q`-tagged Fin vectors in
                # `evaluate`, never guessed.
                ex = self.atom()
                self.eat(",")
                return ("funiverase", finite_tag, var, ex, self.term())
            if "range" in (rng or ""):               # range N  →  0 .. N−1
                N = self.atom()
                lo, hi = ("num", 0), ("bin", "-", N, ("num", 1))
            elif "Icc" in (rng or ""):               # Icc a b  →  a .. b
                lo = self.atom()
                hi = self.atom()
            elif "Ico" in (rng or ""):               # Ico a b  →  a .. b−1 (half-open)
                lo = self.atom()
                b = self.atom()
                hi = ("bin", "-", b, ("num", 1))
            elif "Ioc" in (rng or ""):               # Ioc a b  →  a+1 .. b (lo EXCLUSIVE —
                a = self.atom()                      # `∑ n ∈ Ioc 0 ⌊x⌋₊` sums n = 1..⌊x⌋,
                lo = ("bin", "+", a, ("num", 1))     # the DLMF 27.2.11 Chebyshev-ψ index set)
                hi = self.atom()
            else:
                # a BARE Finset binder `∑ i ∈ s, body` — `s : Finset ι` an ABSTRACT
                # hypothesis binder (the DLMF 18.18 Laguerre sum rule
                # laguerre_sum_eval_zero). Instantiation-sampled downstream: ι := ℕ,
                # s := Finset.range N for a small sampled cardinality N, and the ι-indexed
                # function binders in `body` (c : ι→ℝ, m : ι→ℕ) sampled pointwise — see
                # evaluate's fsumabs/fprodabs and the finset/absfnR/absfnN grids. Only a
                # plain identifier is treated this way (a Finset-typed binder); any other
                # `rng` keeps the honest Unparseable skip below.
                if rng and re.fullmatch(r"[A-Za-zα-ωΑ-Ω]\w*", rng):
                    self.eat(",")
                    return (finite_tag + "abs", var, rng, self.term())
                raise Unparseable(f"finset {rng}")
            # `with P` filter (Finset.filter sugar): `∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p`
            # — the DLMF 27.2.11 Chebyshev-ϑ index set. Only the PRIMALITY predicate on
            # the bound var is modelled (`p.Prime` / `Nat.Prime p` → sympy.isprime via
            # ob._isprime); any other predicate keeps the honest Unparseable skip. The
            # filter rides as an OPTIONAL 6th node slot — existing consumers index [1..4]
            # only, so unfiltered sums (and their handling) are unchanged.
            flt = None
            if self.peek() == ("id", "with"):
                self.eat()
                flt = self._agg_filter(var)
            self.eat(",")
            body = self.term()   # body at Lean big-op precedence 67 — see _agg_body note
            return ((finite_tag, var, lo, hi, body, flt) if flt is not None
                    else (finite_tag, var, lo, hi, body))
        ity = "ℕ"
        if self.peek()[1] == ":":                    # ∑'/∏' n : T , body
            self.eat(":")
            parts = []
            while self.peek()[1] not in (",", None):
                parts.append(self.eat())
            ity = " ".join(parts)
        if ity.startswith("Fin "):                   # ∑ i : Fin N, body — finite 0..N−1
            N = P(tokenize(ity[4:])).expr()
            self.eat(",")
            return (finite_tag, var, ("num", 0), ("bin", "-", N, ("num", 1)), self.term())
        self.eat(",")
        return (infinite_tag, var, self.term(), ity, tok)   # body at big-op prec 67 (see _agg_body)

    def _agg_body(self):
        self.eat(",")
        # Lean big-operator bodies (∑ / ∑' / ∏ / ∏') bind at notation precedence 67 —
        # TIGHTER than binary `+`/`-` (infixl:65) but looser than `*`/`/`/`•` (70/73). So
        # `∑ k ∈ s, f k + g` is `(∑ k ∈ s, f k) + g`, NOT `∑ k ∈ s, (f k + g)`: a top-level
        # `+`/`-` at the body's own depth TERMINATES the summand (an in-body sum/difference is
        # always parenthesised in Lean, and `self.term()`'s atom() consumes those parens).
        # Parse at the `term()` (`* / •`) level so the body stops at that `+`/`-`, matching Lean.
        # Previously `self.expr()` GREEDILY absorbed the trailing `+ …` into the summand — e.g.
        # DLMF 15.8.8-15.8.11's `coeff·∑_{k<m}(…) + coeff₂·∑'ₖ(…)` was mis-parsed as
        # `coeff·∑_{k<m}(… + coeff₂·∑'ₖ)`, adding the k-independent second term m times (and
        # giving 0 at m=0), a spurious FAIL of a TRUE identity (self-validated to 1e-17 in
        # docs/verification/ch15/probe_15_8_8_independent.py). Parse-fidelity fix, no tolerance
        # change; a genuinely parenthesised additive body is unaffected.
        return self.term()

    def _agg_filter(self, var):
        """The predicate of a `with P` Finset filter. Only primality of the BOUND
        variable is supported — `p.Prime` (one dotted id token) or `Nat.Prime p` —
        returned as the filter tag ('prime',). Anything else (a different predicate,
        or primality of some OTHER expression) raises: honest skip, never a guess."""
        k, v = self.peek()
        if k == "id" and v == var + ".Prime":
            self.eat()
            return ("prime",)
        if k == "id" and v == "Nat.Prime":
            self.eat()
            if self.peek() == ("id", var):
                self.eat()
                return ("prime",)
        raise Unparseable("finset-filter predicate")

    def integral_expr(self):
        # ∫ x in DOMAIN , body   (DOMAIN: Ioi a | Ici a | Icc a b | Ioo a b | a..b)
        # ∫ x, body ∂μ           (measure integral against a registered weight)
        self.eat()                                   # ∫
        var = self.eat()                             # bound variable
        if self.peek()[1] == ":":                    # ∫ x : ℝ, body — integral over all of ℝ
            self.eat(":"); self.eat()                # : ℝ
            if self.peek()[1] == "in":               # ∫ t : ℝ in Ioi 0, body — annotated domain
                self.eat()                           # (gamma_eq_mellin_integral, DLMF 5.2.1);
                lo, hi = self.domain()               # same node as the un-annotated `in` form
                self.eat(",")
                return ("integral", var, lo, hi, self.expr())
            self.eat(",")
            return ("integral", var, ("neginf",), ("inf",), self.expr())
        if self.peek()[1] == ",":                    # measure form: ∫ x, body ∂μ
            self.eat(",")
            body = self.expr()
            if self.peek()[0] != "partial":
                raise Unparseable("integral ',' without ∂μ")
            self.eat()                               # ∂
            meas = self.eat()                        # the measure name
            return ("mintegral", var, meas, body)
        if self.eat() != "in":                       # the 'in' keyword
            raise Unparseable("integral 'in'")
        lo, hi = self.domain()
        self.eat(",")
        return ("integral", var, lo, hi, self.expr())

    def domain(self):
        k, v = self.peek()
        open_ray = {"Ioi", "Set.Ioi", "Ici", "Set.Ici"}
        left_ray = {"Iic", "Set.Iic", "Iio", "Set.Iio"}   # ∫ t in Iic b — left-infinite ray
        closed = {"Icc", "Ioo", "Ioc", "Ico", "Set.Icc", "Set.Ioo", "Set.Ioc", "Set.Ico"}
        if v in open_ray:
            self.eat()
            return (self.atom(), ("inf",))
        if v in left_ray:                    # (−∞, b] (expint_6_2_5's PV split, DLMF 6.2.5)
            self.eat()
            return (("neginf",), self.atom())
        if v in closed:
            self.eat()
            return (self.atom(), self.atom())
        a = self.atom()                              # interval  a .. b
        if self.peek()[0] == "dotdot":
            self.eat()
            return (a, self.atom())
        raise Unparseable("integral domain")


def _mem_bound_parts(var, setnode):
    """Desugar a bounded-∃ membership binder `x ∈ Set.Ioo a b` (Icc/Ico/Ioc/Ioo and the
    rays Ioi/Ici/Iio/Iic) into explicit inequality conjuncts on the bound variable — the
    hypothesis is honored exactly as stated. Any other set shape aborts the parse
    (honest skip), never a guessed domain."""
    if setnode[0] == "app" and setnode[1][0] == "var":
        kindnm = setnode[1][1].split(".")[-1]
        a = setnode[2]
        two = {"Icc": ("≤", "≤"), "Ico": ("≤", "<"), "Ioc": ("<", "≤"), "Ioo": ("<", "<")}
        if kindnm in two and len(a) == 2:
            lo_op, hi_op = two[kindnm]
            return [("ineq", lo_op, a[0], ("var", var)),
                    ("ineq", hi_op, ("var", var), a[1])]
        if kindnm in ("Ioi", "Ici") and len(a) == 1:
            return [("ineq", "<" if kindnm == "Ioi" else "≤", a[0], ("var", var))]
        if kindnm in ("Iio", "Iic") and len(a) == 1:
            return [("ineq", "<" if kindnm == "Iio" else "≤", ("var", var), a[0])]
    raise Unparseable("exists-mem set")


def parse(concl):
    # `LSeries.notation` sugar (Mathlib `open scoped LSeries.notation`): `L ↗f s` is
    # notation for `LSeries ↗f s`, where `↗f : ℕ → ℂ` is the numeric coercion of the
    # arithmetic function f. The ↗ coercion is a NO-OP for the oracle — the registry
    # bindings (μ, vonMangoldt, …) are already numeric-valued — so pre-normalize the
    # text: `L ↗` → `LSeries ` (only a standalone `L` immediately applied to a ↗-coerced
    # argument, i.e. exactly the scoped notation), then strip every remaining bare `↗`.
    # Purely additive: the ↗ token previously hard-failed tokenize as `char '↗'`.
    if "↗" in concl:
        concl = re.sub(r"(?<![\w'′₀-₉ℓ])L\s*(?=↗)", "LSeries ", concl)
        concl = concl.replace("↗", "")
    # Leading pole-avoidance guard after ∀-scalar binders:
    #   ∀ <vars>, (∀ k : ℕ, (k : ℂ) ≠ -v) → <eq>
    # (DLMF 15.4.24 Chu–Vandermonde `sum_neg_one_pow_choose_ascPochhammer`: v = b off the
    # nonpositive integers). The antecedent is a domain guard that holds AUTOMATICALLY at
    # every point of the complex sampling grid — SAMPLES["C"] lies entirely off the negative
    # real axis (nonzero Im), so (k : ℂ) = −v is impossible for any k : ℕ — hence the
    # equality is scored only where the hypothesis is satisfied, never fabricated outside it.
    # Strip the guard so the ∀-body reduces to the bare equality the grammar consumes (the
    # grammar peels ∀-binders but not a leading `hyp →`, which otherwise skips as
    # `unparsed:forall-body unconsumed`). ADDITIVE: fires only on this exact `≠ −v` shape.
    _fg = re.match(r'(∀[^,]*,\s*)\(\s*∀\s*\w+\s*:\s*ℕ\s*,\s*\(\s*\w+\s*:\s*ℂ\s*\)'
                   r'\s*≠\s*-\s*\w+\s*\)\s*→\s*', concl)
    if _fg:
        concl = _fg.group(1) + concl[_fg.end():]
    p = P(tokenize(concl))
    if p.peek()[0] == "exists":                # ∃ v : T, body — existential (handled specially)
        p.eat()
        # binder extensions (see forall_binders): function-typed witnesses `P : ℤ → ℂ`
        # (DLMF 20.5.14–17 / 28.2.14) and bounded-∃ membership sugar `x₀ ∈ Set.Ioo 1 2`
        # (gamma_5_4_20_min). Membership desugars into explicit bound conjuncts below.
        ex_mems = []
        ex_binders = p.forall_binders(allow_fn=True, mems=ex_mems)
        # body: ∧-separated parts, each a relation or a ∀-quantified relation (`∀ x, eq` /
        # `∀ n : ℤ, Tendsto …` — the airy-Wronskian constancy and iterated-limit shapes).
        parts = []
        while True:
            if p.peek()[0] == "forall":
                p.eat()
                fb = p.forall_binders(default_ty="R")
                parts.append(("forallq", fb, p.relation()))
            else:
                parts.append(p.relation())
            if p.peek()[0] == "land":
                p.eat()
                continue
            break
        if p.peek()[1] is not None:            # trailing tokens — bail honestly
            raise Unparseable("exists-body unconsumed")
        mem_parts = [q for vn, s in ex_mems for q in _mem_bound_parts(vn, s)]
        if len(parts) == 1 and not mem_parts:
            return ("exists", ex_binders, parts[0])
        return ("exists", ex_binders, ("and", mem_parts + parts))
    fa_binders = {}
    while p.peek()[0] == "forall":             # ∀ v : T, … — universally-quantified body
        p.eat()
        fa_binders.update(p.forall_binders())
    node = p.relation()
    if p.peek()[0] == "land":                # top-level conjunction A ∧ B ∧ …
        parts = [node]
        while p.peek()[0] == "land":
            p.eat()
            # a ∀-QUANTIFIED conjunct. The PARENTHESIZED form `(∀ x, f x = g x)` already
            # parses (atom() → ("forallq", …), wrapped by relation() as ("expr", …)); the
            # UNPARENTHESIZED `… ∧ ∀ x, f x = g x` used to abort at atom '∀'. Accept it the
            # same way the ∃-body loop above does — but ONLY as the LAST conjunct: Lean's ∀
            # body extends maximally, so `A ∧ ∀ x, P ∧ Q` binds Q under the ∀ and treating Q
            # as a SIBLING would check a differently-scoped statement. A trailing ∧ therefore
            # aborts honestly (it aborted before this branch existed too — no coverage lost).
            if p.peek()[0] == "forall":
                p.eat()
                fb = p.forall_binders(default_ty="R")
                parts.append(("forallq", fb, p.relation()))
                if p.peek()[0] == "land":
                    raise Unparseable("forall-conjunct scope")
                continue
            parts.append(p.relation())
        node = ("and", parts)
    if p.peek()[1] is not None:              # ∀-body left unconsumed tokens (e.g. `→`) — bail
        if fa_binders:
            raise Unparseable("forall-body unconsumed")
    if fa_binders:                           # wrap so classify_and_check merges the ∀ binders
        return ("forall", fa_binders, node)
    return node


# ════════════════════════ 3. EVALUATE with sampled free vars ═════════════════
# Zero-arg dotted methods (`n.factorial`, `n.divisors.card`, …) — every entry is
# EXACT integer arithmetic (or an exact list, for the set-valued ones), so the
# equality gate sees no rounding. Unknown methods raise → honest skip.
import math as _math
DOT0 = {
    "succ":         lambda v: int(v) + 1,
    "cast":         lambda v: v,             # Nat.cast/Int.cast — value-preserving, numeric no-op
                                             # (`x.cast` inside a ZMod coercion, Gauss's lemma;
                                             # the mod-p reduction happens at the enclosing
                                             # `(… : ZMod p).val`, never here)
    "toNat":        lambda v: max(0, int(v)),                  # Int.toNat (clamps < 0 to 0)
    "factorial":    lambda v: _math.factorial(int(v)),
    "dfactorial":   lambda v: ob._double_factorial(v),        # n‼ (Nat: n≤0 ⇒ 1)
    "negOnePow":    lambda v: 1 if int(v) % 2 == 0 else -1,    # Int.negOnePow (any ℤ)
    "centralBinom": lambda v: _math.comb(2 * int(v), int(v)),
    "totient":      lambda v: ob._totient(v),
    "divisors":     lambda v: ob._divisors(v),                 # ℕ → exact divisor list
    "primeFactors": lambda v: ob._prime_factors(v),
    "card":         lambda v: len(v),                          # Finset.card of a set value
    "re":           lambda v: mp.re(v),
    "im":           lambda v: mp.im(v),
    "natAbs":       lambda v: abs(int(v)),                     # Int.natAbs (exact-int operand)
    "det":          lambda m: mp.det(m),   # Matrix.det of an evaluated mp.matrix value
                                           # (additionMatrix, DLMF 23.10.1); a non-matrix
                                           # operand raises inside mp.det → honest drop
}


def _desc_factorial(mval, nval):
    """Mathlib `Nat.descFactorial m n = m·(m−1)⋯(m−n+1)` (0 when n > m — a factor hits 0),
    computed in exact integers. Non-natural operands raise → honest point drop."""
    mv, nv = _near_int(mval), _near_int(nval)
    if mv is None or nv is None or mv < 0 or nv < 0:
        raise Unparseable("descFactorial non-natural operand")
    out = 1
    for i in range(nv):
        out *= (mv - i)
    return mp.mpf(0 if mv < nv else out)


def _dot_split(nm):
    """`n.divisors.card` → ['n','divisors','card'] iff every suffix part is a known
    zero-arg dot method; None otherwise (the name then stays whole → unbound skip)."""
    parts = nm.split(".")
    if len(parts) > 1 and parts[0] and all(p in DOT0 for p in parts[1:]):
        return parts
    return None


def _all_int(node, intvars):
    """True if `node` evaluates to an exact integer given the ℕ/ℤ-typed var names — a tree of
    integer literals, integer-typed vars, and +,−,*,^,/ thereof (a Nat/Int `/` is itself
    integer-valued, floor)."""
    k = node[0]
    if k == "num":
        return float(node[1]).is_integer()
    if k == "var":
        return node[1] in intvars
    if k == "real":          # an explicit real/complex cast (n : ℝ): NOT an exact integer
        return False
    if k == "zmodcast":      # (e : ZMod n) evaluates as its ℤ-lift — integer iff e is
        return _all_int(node[2], intvars)
    if k == "neg":
        return _all_int(node[1], intvars)
    if k == "bin" and node[1] in ("+", "-", "*", "^", "/"):
        return _all_int(node[2], intvars) and _all_int(node[3], intvars)
    return False


def _has_theta_head(node):
    """Whether an AST contains one of the four classical theta applications."""
    if isinstance(node, tuple):
        if node[0] == "app" and node[1][0] == "var" \
                and node[1][1].split(".")[-1] in {"θ₁", "θ₂", "θ₃", "θ₄"}:
            return True
        return any(_has_theta_head(c) for c in node[1:])
    if isinstance(node, list):
        return any(_has_theta_head(c) for c in node)
    return False


def _has_intvar(node, intvars):
    """True if `node` references an integer-typed variable. A `/` is Lean FLOOR division
    only when it actually involves such a variable (`m / 2` with m : ℕ); a pure-literal
    fraction like `1 / 2` in a real/complex formula is REAL division (= 0.5), never floored."""
    k = node[0]
    if k == "var":
        return node[1] in intvars
    if k == "real":          # a real/complex cast (n : ℝ) is a real-valued operand, not an
        return False         # integer var — a `/` involving only such operands is real division
    if k == "zmodcast":      # (e : ZMod n) — an integer-lift operand; look through the cast
        return _has_intvar(node[2], intvars)
    if k == "neg":
        return _has_intvar(node[1], intvars)
    if k == "bin":
        return _has_intvar(node[2], intvars) or _has_intvar(node[3], intvars)
    return False


# ── Weierstrass lattice dispatch (M15) ──────────────────────────────────────
# Lattice-method heads dispatch on a sampled `_Lattice` value in env (a new value type, not
# a REGISTRY callable). `L.weierstrassP z` parses as a dotted-var head `("var","L.weierstrassP")`
# (since `.` is in the id class); `(L.smul hlam).g₂` is the lone `dotm` form; `℘[L] z` uses the
# bracket head `℘[]`. The math lives in oracle_bindings (`ob._wp`, …).
_LDOT = {                                          # L.method args (z passed through)
    "weierstrassP": lambda L, a: ob._wp(L, a[0]),
    "derivWeierstrassP": lambda L, a: ob._wp_deriv(L, a[0]),
    "sigma": lambda L, a: ob._wsigma(L, a[0]), "zeta": lambda L, a: ob._wzeta(L, a[0]),
    "g₂": lambda L, a: ob._g2(L), "g₃": lambda L, a: ob._g3(L),
    "G": lambda L, a: ob._G_eisenstein(L, a[0]),
}
_LARG = {                                          # head applied to a lattice argument
    "discriminant": ob._wdisc, "FLMF.Weierstrass.discriminant": ob._wdisc,
    "modularInvariant": ob._modular_invariant, "kleinJ": ob._kleinJ,
    "e₁": ob._e1, "e₂": ob._e2, "e₃": ob._e3, "E₄": ob._wE4, "E₆": ob._wE6,
    # FULLY QUALIFIED spellings (as they appear outside `namespace FLMF.Weierstrass` — e.g. the
    # Ch31 Heun Weierstrass-form rows write `FLMF.Weierstrass.e₃ L`). The dotted-var branch above
    # partitions at the FIRST '.', so `FLMF.Weierstrass.e₃` looks up env["FLMF"] (never a lattice)
    # and falls through to here; without these keys the head stayed `unbound:FLMF.Weierstrass.e₃`.
    # Same functions as the bare keys — mirrors the existing `FLMF.Weierstrass.discriminant` entry.
    "FLMF.Weierstrass.e₁": ob._e1, "FLMF.Weierstrass.e₂": ob._e2,
    "FLMF.Weierstrass.e₃": ob._e3,
}


def _lam(env):
    return env.get("lam", env.get("λ", mp.mpc("1.3", "-0.4")))


def _aslat(node, env):
    """A node denoting a lattice value: bare `L` or `(L.smul hlam)`."""
    if node[0] == "var" and isinstance(env.get(node[1]), ob._Lattice):
        return env[node[1]]
    if node[0] == "app" and node[1][0] == "var" and node[1][1].endswith(".smul"):
        o = node[1][1][:-5]
        if isinstance(env.get(o), ob._Lattice):
            return env[o].smul(_lam(env))
    return None


def _bundle_fn(fnode, env):
    """`W.zeta` / `W.sigma` (lattice-bundled) → a one-argument callable, for deriv/logDeriv."""
    if fnode[0] == "var" and "." in fnode[1]:
        o, _, m = fnode[1].partition(".")
        if isinstance(env.get(o), ob._Lattice):
            if m == "zeta":
                return lambda t: ob._wzeta(env[o], t)
            if m == "sigma":
                return lambda t: ob._wsigma(env[o], t)
    return None


def _q_expansion_coeff(f, h, m, r=None, N=64):
    """The m-th coefficient of Mathlib's `qExpansion h f` (f : ℍ → ℂ, h-periodic, expanded
    in the nome q_h = e^{2πiτ/h}) — Cauchy coefficient extraction
        c_m = (2πi)⁻¹ ∮_{|q|=r} F(q) q^{−m−1} dq
    as an N-point DFT on the circle, with F(q) = f(τ(q)), τ = h·log q/(2πi) (the log branch
    only shifts τ by an integer multiple of h — invisible to an h-periodic form). The form
    is evaluated through its OWN oracle binding, so the coefficient stays decorrelated from
    any q-series identity under test. Truncation error ≈ |c_{m+N}|·r^N (level-1 modular-form
    coefficients grow polynomially ⇒ ≲ 1e-50 at r=0.1, N=64); the DFT amplifies the sample
    error by r^{−m} (~1e5 at the largest ℕ-grid m=5 — far below the equality gate)."""
    r = mp.mpf("0.1") if r is None else r
    i2pi = 2 * mp.pi * mp.mpc(0, 1)
    tot = mp.mpc(0)
    for j in range(N):
        w = mp.exp(i2pi * j / N)
        tot += f(h * mp.log(r * w) / i2pi) * w ** (-m)
    return tot / (N * r ** m)


def _is_parabolic_U(arg0, env):
    """`U`'s first argument decides Chebyshev Uₙ (a ring TYPE, e.g. `R`) vs parabolic-cylinder
    U(a,·) (a NUMBER). Parabolic iff arg0 is a numeric expression, or a variable whose declared
    binder is ℝ/ℂ (not a type)."""
    if arg0[0] in ("num", "bin", "neg", "inv"):
        return True
    if arg0[0] == "var":
        return env.get("_binders", {}).get(arg0[1]) in ("R", "C")
    return False


def _pred_holds(pred, env):
    """Decide a countset predicate (one relation node) on EXACT integers — the membership
    test of a ℕ-Finset filter is decidable integer arithmetic (Gauss's lemma residue test,
    DLMF 27.9), so both comparands must be exact ints (`_near_int`); anything inexact
    raises → the enclosing sample drops honestly, never a miscounted set."""
    k = pred[0]
    if k == "ineq":
        op, Lp, Rp = pred[1], pred[2], pred[3]
    elif k in ("eq", "ne"):
        op, Lp, Rp = ("=" if k == "eq" else "≠"), pred[1], pred[2]
    elif k == "expr" and pred[1][0] == "app" and pred[1][1][0] == "var":
        # Coprimality membership predicate — `n.Coprime x` (dotted head, one arg) or
        # `Nat.Coprime n x`: Mathlib's Nat.Coprime is DEFINED as gcd(n, x) = 1, so the
        # test is exact-integer gcd. This is the filter of the DLMF 27.2 defining count
        # φ(n) = #{a ∈ Finset.range n | n.Coprime a} (totient_eq_card_coprime). Operands
        # must be exact ints; any other applied predicate keeps the honest skip below.
        hn, pargs = pred[1][1][1], pred[1][2]
        ops = None
        if hn == "Nat.Coprime" and len(pargs) == 2:
            ops = (pargs[0], pargs[1])
        elif hn.endswith(".Coprime") and hn.count(".") == 1 and len(pargs) == 1:
            pre = hn[:-len(".Coprime")]
            ops = ((("num", int(pre)) if pre.isdigit() else ("var", pre)), pargs[0])
        if ops is None:
            raise Unparseable("countset predicate")
        ca, cb = _near_int(evaluate(ops[0], env)), _near_int(evaluate(ops[1], env))
        if ca is None or cb is None:
            raise Unparseable("countset predicate not exact-integer")
        return _math.gcd(int(ca), int(cb)) == 1
    else:
        raise Unparseable("countset predicate")
    a, b = _near_int(evaluate(Lp, env)), _near_int(evaluate(Rp, env))
    if a is None or b is None:
        raise Unparseable("countset predicate not exact-integer")
    return {"<": a < b, "≤": a <= b, ">": a > b, "≥": a >= b,
            "=": a == b, "≠": a != b}[op]


def _num_limUnder(nhds_node, lam_node, env):
    """Numeric evaluation of `limUnder (𝓝 pt) (fun x => body)` — a Filter.limUnder the
    checker cannot evaluate symbolically. Computes the limit by DIRECTIONAL sampling of the
    body as x → pt, with a 2-point Richardson extrapolation (removes the O(ε) approach term).

    SOUNDNESS: for the two-sided filter 𝓝 the limit is scored ONLY when it is
    direction-independent (the samples along +1, −1, +i, −i agree); a direction-dependent
    result means no two-sided limit exists (Mathlib's `limUnder` is then junk) and the point
    drops honestly via Unparseable. One-sided filters 𝓝[>]/𝓝[<] sample the single admissible
    real side. This mirrors the small-ε / coalescing numeric-limit reading of the FLMF
    principal-continuation defs (DLMF 15.2.5/15.2.6)."""
    pt = evaluate(nhds_node[2], env)
    filt = nhds_node[1]
    binder, body = lam_node[1], lam_node[2]

    def richardson(direction):
        e1, e2 = mp.mpf("1e-4"), mp.mpf("5e-5")
        v1 = evaluate(body, {**env, binder: pt + e1 * direction})
        v2 = evaluate(body, {**env, binder: pt + e2 * direction})
        return 2 * v2 - v1                         # L = 2·g(ε/2) − g(ε), leading error O(ε²)

    if filt == "𝓝":
        dirs = [mp.mpf(1), mp.mpf(-1), mp.mpc(0, 1), mp.mpc(0, -1)]
    elif filt in ("𝓝[>]", "𝓝[≥]"):
        dirs = [mp.mpf(1)]
    elif filt in ("𝓝[<]", "𝓝[≤]"):
        dirs = [mp.mpf(-1)]
    else:
        raise Unparseable(f"limUnder filter {filt}")
    vals = []
    for d in dirs:
        v = richardson(d)
        if not mp.isfinite(v):
            raise Unparseable("limUnder: non-finite directional value")
        vals.append(v)
    scale = max(mp.mpf(1), *[abs(v) for v in vals])
    for v in vals[1:]:
        if abs(v - vals[0]) / scale > mp.mpf("1e-6"):
            raise Unparseable("limUnder: directional limits disagree (no two-sided limit)")
    return sum(vals) / len(vals)


_THETA_HEADS = {"θ₁": 1, "θ₂": 2, "θ₃": 3, "θ₄": 4}


def _theta_laplace_value(var, lo, body, env):
    """Recognize the theta lattice-Laplace shape `∫₀^∞ e^{−s t} · θⱼ(z₀ | i·a·t) dt`
    (DLMF 20.10.4/20.10.5, the Laplace transforms of θⱼ w.r.t. the lattice parameter)
    and evaluate it by the TERMWISE heat-kernel transform `ob._theta_lattice_laplace`
    — so no quadrature ever samples the τ → 0 modular cusp, the regime where the
    generic `mp.quad` ray path balloons to a MemoryError/SIGKILL (5.7 GB, measured;
    targeted_check.py:16) on theta_20_10_4 / theta_20_10_5. Structural match only: the
    integrand must be a
    product of `cexp(linear in t)` and one θⱼ application whose lattice argument is
    `i·a·t` with `a > 0` real (a = π/ℓ²) and whose z-argument is constant in t.
    Returns the integral value, or None when the shape does not match (fall through to
    the generic ray quadrature — purely additive). Raises Unparseable only when the
    shape matches but the sample is out of the Laplace domain (Re s ≤ 0), so that
    sample is dropped honestly rather than mis-quadratured."""
    try:
        if abs(evaluate(lo, env)) > mp.mpf("1e-20"):
            return None                                  # lower limit must be 0
    except Exception:
        return None
    if not (isinstance(body, tuple) and body[0] == "bin" and body[1] == "*"):
        return None
    th = pref = None
    for f in (body[2], body[3]):
        if (isinstance(f, tuple) and f[0] == "app" and f[1][0] == "var"
                and f[1][1] in _THETA_HEADS and len(f[2]) == 2):
            th = f
        else:
            pref = f
    if th is None or pref is None:
        return None
    if not (isinstance(pref, tuple) and pref[0] == "app"
            and pref[1] == ("var", "cexp") and len(pref[2]) == 1):
        return None
    j = _THETA_HEADS[th[1][1]]
    z0node, taunode, argnode = th[2][0], th[2][1], pref[2][0]

    def ev(node, tval):
        return mp.mpc(evaluate(node, {**env, var: tval}))

    try:
        # z-argument must be independent of the integration variable t
        z0a, z0b = ev(z0node, mp.mpf("0.5")), ev(z0node, mp.mpf("1.5"))
        if abs(z0a - z0b) > mp.mpf("1e-18") * (1 + abs(z0a)):
            return None
        z0 = z0a
        # lattice argument must be τ(t) = i·a·t, a real > 0  (so a = π/ℓ²)
        t0, t1, t2 = ev(taunode, mp.mpf(0)), ev(taunode, mp.mpf(1)), ev(taunode, mp.mpf(2))
        if abs(t0) > mp.mpf("1e-18") or abs(t2 - 2 * t1) > mp.mpf("1e-16") * (1 + abs(t1)):
            return None
        if abs(mp.re(t1)) > mp.mpf("1e-16") * (1 + abs(t1)) or mp.im(t1) <= 0:
            return None
        ell = mp.sqrt(mp.pi / mp.im(t1))
        # prefactor exponent must be −s·t (linear in t, zero at t = 0)
        a0, a1, a2 = ev(argnode, mp.mpf(0)), ev(argnode, mp.mpf(1)), ev(argnode, mp.mpf(2))
        if abs(a0) > mp.mpf("1e-18") or abs(a2 - 2 * a1) > mp.mpf("1e-16") * (1 + abs(a1)):
            return None
        s = -a1
    except Exception:
        return None
    try:
        return ob._theta_lattice_laplace(j, z0, s, ell)
    except Exception:
        raise Unparseable("theta-laplace-out-of-domain")


def evaluate(node, env):
    k = node[0]
    if k == "num":
        return mp.mpf(node[1])
    if k == "var":
        nm = node[1]
        if nm in env:
            return env[nm]
        if "." in nm:                              # bare `L.g₂` (lattice dotted-var, no args)
            o, _, m = nm.partition(".")
            if isinstance(env.get(o), ob._Lattice) and m in _LDOT:
                return _LDOT[m](env[o], [])
            if m in ("1", "2") and isinstance(env.get(o), tuple):   # pair projection ij.1/ij.2
                return env[o][int(m) - 1]
        if nm in ("π", "Real.pi"):
            return mp.pi
        _re = _reg_get(nm)
        if _re is not None and _re[0] == "const":
            return _re[1]
        if _re is not None and _re[0] == "psfn":   # formal power series as its
            x = env.get(IND)                                     # generating function at X
            if x is None:
                raise Unparseable("psfn without indeterminate")
            return _re[1](x)
        if _re is not None and _re[0] == "envfn":  # env-dependent ∀-witness ATOM: a dotted
            # bundle-projection head with no explicit args (`O.P.roots.toFinset.card`,
            # DLMF §18.2(vi)) whose witness value depends on SAMPLED binders — the binding
            # receives the whole sample env and instantiates the quantified bundle at its
            # anchored canonical witness (ob._op_bundle_roots_card; a ValueError/KeyError
            # for a missing or out-of-range binder → honest point drop, never a number).
            return _re[1](env)
        if nm == "PowerSeries.X":                                # the formal indeterminate
            x = env.get(IND)
            if x is None:
                raise Unparseable("PowerSeries.X without indeterminate")
            return x
        sp = _dot_split(nm)                # n.factorial / p.succ / n.divisors.card …
        if sp and sp[0] in env:
            val = env[sp[0]]
            for m in sp[1:]:
                val = DOT0[m](val)
            return val
        raise Unparseable(f"free symbol {nm}")
    if k == "real":          # (e : ℝ)/(e : ℂ) cast — numerically transparent (just evaluate e)
        return evaluate(node[1], env)
    if k == "nearint":       # nearest-integer projection of the operand (the `∈ Set.range
        # ((↑) : ℤ/ℕ → _)` integrality predicate, DLMF 24.10): |e − nearint e| ≈ 0 ⟺ e is an
        # integer. For the ℕ-cast range the projection clamps at 0, so a NEGATIVE integer e
        # stays correctly refuted (−3 projects to 0, gap 3).
        v = evaluate(node[1], env)
        if isinstance(v, mp.mpc):
            r = mp.nint(v.real)
            return mp.mpc(r if node[2] == "Z" else max(r, mp.mpf(0)), 0)
        r = mp.nint(v)
        return r if node[2] == "Z" else max(r, mp.mpf(0))
    if k == "zmodcast":      # (e : ZMod n) — evaluate the ℤ-lift; the mod-n congruence is
        return evaluate(node[2], env)   # applied at the equality level (sweep_eq zmod branch)
    if k == "bool":          # a boolean '↔' side (handle_bool_iff): True ↦ 1, False ↦ 0 — so
        return mp.mpf(1 if _bool_spec_val(node[1], env) else 0)   # sweep_eq's exact gate
                                                                  # scores bool(L) = bool(R)
    if k == "neg":
        return -evaluate(node[1], env)
    if k == "floor":         # ⌊e⌋₊ — Nat.floor = max(0, ⌊e⌋); ⌊e⌋ — Int.floor = ⌊e⌋
        v = evaluate(node[2], env)
        f = mp.floor(v)
        return f if node[1] == "int" or f > 0 else mp.mpf(0)
    if k == "inv":
        # a⁻¹ on a ZMod-typed binder is the MODULAR inverse in (ℤ/kℤ)*, NOT the real
        # reciprocal: 1/2 = 0.5 fed to a character callable truncates to χ(int(0.5) % k)
        # = χ(0) = 0, which falsified the (Mathlib-proven) DLMF 27.8.6 orthogonality LHS
        # at every a ∈ {2,3}. Non-invertible a (gcd(a,k) ≠ 1 — Lean junk-value territory,
        # excluded by the IsUnit hypothesis) is an honest per-sample skip, never a number.
        if node[1][0] == "var" and env.get("_binders", {}).get(node[1][1]) == "zmod":
            knm = env.get("_zmodmod", {}).get(node[1][1])
            if knm is not None and knm in env and node[1][1] in env:
                kk = int(env[knm])
                try:
                    return mp.mpf(pow(int(env[node[1][1]]) % kk, -1, kk))
                except ValueError:
                    raise Unparseable("zmod-noninvertible")
        # Reciprocal at mpmath WORKING precision: `1 / v` with a Python-int operand
        # (e.g. `(k.factorial)⁻¹` — DOT0['factorial'] returns a Python int) is DOUBLE
        # float division (1/24 ≈ 0.041666666666666664, ~1e-17 error), which failed the
        # Lean-PROVEN hermite_isCDSystem step conjunct (DLMF 18.2.12, a n = 1/n!) at
        # the equality tolerance. mp.mpf(1)/v keeps mpf/mpc operands unchanged and
        # lifts int operands to full precision. Precision fix only — no tolerance,
        # domain, or semantics change.
        _iv = evaluate(node[1], env)
        # Lean/Mathlib `inv_zero : 0⁻¹ = 0` (GroupWithZero) — same total-field junk-value
        # convention as `div_zero` above (the l = 0 origin term of `∑' l : L.lattice,
        # ((l:ℂ)^4)⁻¹`, DLMF 23.3.1, is literally 0 in Lean). Exact-zero operand only.
        if _iv == 0:
            return mp.mpf(0)
        return mp.mpf(1) / _iv
    if k == "bin":
        op = node[1]
        # `^`: a Nat/Int `/` in the exponent floors ONLY for integer-base exponentiation
        # (`(-1)^(m/2)` — Monoid npow with a Nat exponent), NOT real rpow (`(2π)^((n-1)/2)`,
        # the Gauss-multiplication half-power, whose exponent is a real). So `_inexp` is set
        # for the exponent only when the BASE is integer-typed. Base eval'd without `_inexp`.
        if op == "^":
            base_int = _all_int(node[2], env.get("_intvars", ()))
            return evaluate(node[2], env) ** evaluate(node[3], {**env, "_inexp": base_int})
        a, b = evaluate(node[2], env), evaluate(node[3], env)
        if op == "+":
            return a + b
        if op == "-":
            return a - b
        if op == "*":
            return a * b
        if op == "%":
            # Lean `%` is Nat/Int modulo — integer operands. Use Python's floored mod for
            # Nat semantics (operands here are non-negative loop indices like `k % 2`).
            if b == 0:
                raise ZeroDivisionError
            return mp.mpf(int(a) % int(b))
        if op == "/":
            # Lean Nat/Int `/` is FLOOR division ONLY in a Nat exponent context (`(-1)^(m/2)`),
            # with integer operands and at least one integer VARIABLE. A `/` in a function
            # argument (`Γ(z + k/n)`, the Gauss-multiplication shift) or a coefficient
            # (`2/(2l+1)`) is REAL division — never floored.
            iv = env.get("_intvars", ())
            if (env.get("_inexp") and iv and _all_int(node[2], iv) and _all_int(node[3], iv)
                    and (_has_intvar(node[2], iv) or _has_intvar(node[3], iv))):
                if b == 0:
                    raise ZeroDivisionError
                return mp.floor(a / b)
            # Lean/Mathlib total-field convention `div_zero : a / 0 = 0` (DivisionRing):
            # this AST node IS Lean's `/`, so at an exact-zero denominator the Lean value
            # of the term is literally 0 — e.g. the k = 0 term `cos 0 / (0:ℝ) = 0` of the
            # Kummer-Fourier partial sums (gamma_kummer_even, DLMF 5.7), where mpmath's
            # mpf(1)/mpf(0) would instead raise and poison every sample. Exact-zero b only
            # (a roundoff-tiny denominator still divides and hits the pole guard as before);
            # never a fabricated value — it is the same junk-value semantics the Lean
            # statement itself is proven under.
            if b == 0:
                return mp.mpf(0)
            return a / b
    if k == "eval":          # (P).eval a  → evaluate P with the indeterminate := a
        a = evaluate(node[2], env)
        return evaluate(node[1], {**env, IND: a})
    if k == "iterderiv":     # (Polynomial.derivative^[n] P).eval x — n-fold formal d/dX
        n, arg, base = node[1], node[2], node[3]
        if base == ("var", "deriv"):
            # ANALYTIC n-fold derivative `deriv^[n] f x` (Function.iterate of Mathlib's
            # `deriv` — the dⁿ/dxⁿ operator of DLMF 18.5.5): the parser hands the
            # iterate's operand as the application node `(f …) x`, so differentiate the
            # function-position head with ONE higher-order mp.diff at the evaluated
            # point, exactly like inline `deriv` (finite differences of finite
            # differences would compound truncation error). Any other operand shape
            # keeps the honest Unparseable skip. ADDITIVE: the formal-polynomial
            # `Polynomial.derivative^[n]` path below is unchanged.
            if arg[0] == "app" and len(arg[2]) == 1:
                return mp.diff(_fn_callable(arg[1], env), evaluate(arg[2][0], env),
                               int(evaluate(n, env)))
            raise Unparseable("deriv-iterate shape")
        if base not in (("var", "Polynomial.derivative"), ("var", "derivative")):
            raise Unparseable("iterate of non-derivative")
        x = env.get(IND)
        if x is None:
            raise Unparseable("iterderiv without indeterminate")
        return mp.diff(lambda t: evaluate(arg, {**env, IND: t}), x, int(evaluate(n, env)))
    if k == "sum":
        var, body = node[1], node[2]
        ity = node[3] if len(node) > 3 else "ℕ"
        f = lambda n: evaluate(body, {**env, var: mp.mpf(n)})
        if ity == "ℤ":                         # bilateral series — sum over ALL of ℤ
            return _bounded_nsum(f, bilateral=True)
        if ity.startswith("DirichletCharacter"):  # ∑ χ : DirichletCharacter ℂ k, body — finite,
            kk = env.get(ity.split()[-1])      # over the φ(k) characters of a CYCLIC (ℤ/kℤ)*.
            chars = ob._dirichlet_chars(int(kk)) if kk is not None else None
            if chars is None:
                raise Unparseable("non-cyclic-modulus")
            return mp.fsum(evaluate(body, {**env, var: chi}) for chi in chars)
        if len(node) > 4 and node[4] == "∑":
            # a FINITE-spelled bare/typed sum `∑ x, body` / `∑ x : ZMod k, body` is Lean's
            # Finset.univ sum over a FINITE carrier (an infinite ℕ-series is always spelled
            # `∑'` — node[4] would be "∑'"); aggregating it over [0,∞) would fabricate a
            # different (divergent) value. The carrier size comes from the row's own data:
            # a `ZMod k` index type with k in env, else the `.modulus` tag of a sampled
            # character callable in env (the Gauss-sum surface `∑ x, χ x * ψ x`, DLMF
            # 27.10.9 — ob._mulchar_sample/_addchar_sample tag their carrier). No carrier
            # in scope → honest skip, never a fabricated aggregate.
            kk = env.get(ity.split()[-1]) if ity.startswith("ZMod") else None
            if kk is None:
                kk = next((getattr(vv, "modulus") for vv in env.values()
                           if hasattr(vv, "modulus")), None)
            if kk is None:
                # …or a `Fin q`-parametrized vector applied to the bound index — the SAME
                # carrier resolution the `∏` branch below already performs (`∑ j, γ j/(z−aⱼ)`
                # over `γ, a : Fin N → ℂ`, DLMF 31.15.1). Preferring the vector actually
                # APPLIED to the index keeps distinct-dimension tuples on their own range.
                # ADDITIVE and deliberately NARROWER than the product branch: only a vector
                # genuinely applied to the bound index supplies a carrier here — there is no
                # bare `.q` fallback, so an unrelated tuple in scope can never set the range.
                # Fires only where the lookup previously raised `univ-sum carrier`.
                kk = _finvec_applied_q(body, var, env)
            if kk is None:
                raise Unparseable("univ-sum carrier")
            return mp.fsum(f(j) for j in range(int(kk)))
        if ity == "Nat.Primes":                # ∑' p : Nat.Primes, body — the series over
            # the primes p = 2, 3, 5, … (the `↑p` coercion of the binder is just the
            # numeric prime; DLMF 25.2.11 logarithmic Euler product). Accumulated with
            # the same bounded-sum settled-tail cutoff as the ℕ path, prime-indexed and
            # without extrapolation (_bounded_prime_sum); an unsettled small-Re-s point
            # drops honestly, never a half-converged value.
            return _bounded_prime_sum(f)
        if ity.endswith(".lattice"):
            # `∑' l : L.lattice, body` — the period-lattice tsum (DLMF 23.2.4/23.3.1):
            # enumerate l = m·ω₁ + n·ω₂ over concentric shells with Richardson tail
            # extrapolation (_lattice_tsum, residual-gated). The prefix must resolve to a
            # sampled _Lattice in env; anything else keeps the honest series-index skip.
            pref = ity[: -len(".lattice")]
            if isinstance(env.get(pref), ob._Lattice):
                return _lattice_tsum(lambda l: evaluate(body, {**env, var: l}),
                                     env[pref])
        if ity != "ℕ":                         # other index types — nsum over
            raise Unparseable(f"series index {ity}")   # [0,∞) would be a DIFFERENT sum;
                                                       # never fabricate
        try:                                   # skip n=0 if singular (junk-value series)
            # A NON-FINITE f(0) (nan/inf) is the same junk-value case as a raising one:
            # mpmath 0^(−s) → inf, so `Λ(0)·0^(−s)` = 0·inf = nan, while the Lean term is
            # literally 0 (Mathlib `Complex.cpow` junk value 0^w = 0 for w ≠ 0, and the
            # coefficient at 0 vanishes — Λ(0) = μ(0) = 0). Without this the nan poisons
            # every partial sum of Σ' Λ(n)n^{−s} (DLMF 27.4.12) and the large-σ RE1 grid
            # points skip as undersampled. ADDITIVE: only the start index of the ℕ-tsum;
            # no tolerance change, the raising path below is unchanged.
            v0 = f(0)
            start = 0 if mp.isfinite(v0) else 1
        except Exception:
            start = 1
        # O(k)-per-term coefficient recurrences (see _COSTLY_RECURRENCE_HEADS): cap the
        # naive pre-loop at 300 terms so the accelerator is reached in seconds instead
        # of burning the whole O(K²) 4000-term cap (expint_6_10_1, DLMF 6.10.1).
        if _contains_head(body, _COSTLY_RECURRENCE_HEADS):
            return _bounded_nsum(f, start=start, maxterms=300)
        # DLMF 15.8.8-15.8.11 log-case linear transforms: an `∑'ₖ` whose summand carries BOTH
        # an O(k) `ascPochhammer` coefficient AND four `digamma`s — the near-boundary
        # (|z⁻¹|/|1−z|/|1−1/z| → 1) samples converge too slowly to settle and the dps=100
        # acceleration hangs the child (see _bounded_nsum's `accelerate` note). Cap the naive
        # loop at 800 terms (settles every sample strictly inside the domain — geometric ratio
        # ≲ 0.93 clears the 1e-25 tol) and DISABLE accel so a slower sample drops FAST rather
        # than hanging. Narrowly keyed on ascPochhammer∧digamma so the pure-ψ Kummer/Gauss
        # digamma series (realDigamma_…_tsum, gamma_5_7_7) that RELY on acceleration are
        # untouched. O(800²) per unsettled sample stays well under the per-sample budget.
        if _contains_head(body, {"ascPochhammer"}) and _contains_head(body, {"digamma"}):
            return _bounded_nsum(f, start=start, maxterms=800, accelerate=False)
        # Fourier-type summand (single sin/cos factor in the index) → hand the accelerator
        # a complexified e^{i·arg} candidate series (see _complexify_trig / the alt gate).
        alt = None
        _cx = _complexify_trig(body, var)
        if _cx is not None:
            _bc, _proj = _cx
            alt = ((lambda n, _b=_bc: evaluate(_b, {**env, var: mp.mpf(n)})), _proj)
        return _bounded_nsum(f, start=start, alt=alt)
    if k == "prod":                            # ∏' n : ℕ, body — bounded infinite product
        var, body = node[1], node[2]
        ity = node[3] if len(node) > 3 else "ℕ"
        if len(node) > 4 and node[4] == "∏":
            # a FINITE-spelled bare/typed product `∏ x, body` is Lean's Finset.univ
            # product over a FINITE carrier (a genuinely infinite product is always
            # spelled `∏'` — node[4] would be "∏'"); aggregating it over [0,∞) via
            # `_bounded_nprod` would fabricate a different (and generally divergent)
            # value. Mirrors the `∑` univ-carrier lookup above (DirichletCharacter/
            # AddChar `.modulus`): the FINITE carrier size q comes from any `.q`-tagged
            # finvecC callable reachable in env (meijerG_eq_pFq's `∏ i, Γ(Aᵢ)`,
            # DLMF 16.18.1). No such carrier in scope → honest skip, never a
            # fabricated aggregate.
            # Carrier size: the cardinality of the finvecC vector actually APPLIED to the
            # bound index in `body` (`∏ i, (A i + n)` → A's q = p), so distinct-dimension
            # tuples `A : Fin p → 𝕂`, `B : Fin q → 𝕂` (pFqCoefficient_succ_div, p ≠ q) each
            # get their OWN range — an arbitrary `.q` callable would iterate B past its length.
            # Falls back to any `.q` callable (equal-dim rows, meijerG_eq_pFq's `∏ i, Γ(Aᵢ)`).
            qq = _finvec_applied_q(body, var, env)
            if qq is None:
                qq = next((getattr(vv, "q", None) for vv in env.values()
                           if callable(vv) and hasattr(vv, "q")), None)
            if qq is None:
                raise Unparseable("univ-prod carrier")
            total = mp.mpf(1)
            for j in range(int(qq)):
                total *= evaluate(body, {**env, var: mp.mpf(j)})
            return total
        if ity != "ℕ":                         # Primes / lattice / … — same soundness rule
            raise Unparseable(f"product index {ity}")
        return _bounded_nprod(lambda n: evaluate(body, {**env, var: mp.mpf(n)}))
    if k == "countset":                        # #{x ∈ lo..hi | pred} — filtered integer count
        # (Gauss's lemma, DLMF 27.9: μ = #{x ∈ [1,(p−1)/2] : (a·x mod p) > p/2}). The set
        # lives in ℕ, so the bounds and any `/` of integer-typed operands inside are Lean
        # Nat FLOOR division — the whole subtree is evaluated in the `_inexp` integer
        # context, with the bound var added to `_intvars`. The predicate is decided on
        # EXACT integers only (`_pred_holds`); a non-integer comparand or bound raises →
        # honest skip, never a rounded count.
        var, lo, hi, pred = node[1], node[2], node[3], node[4]
        envN = {**env, "_inexp": True,
                "_intvars": set(env.get("_intvars", ())) | {var}}
        lov, hiv = _near_int(evaluate(lo, envN)), _near_int(evaluate(hi, envN))
        if lov is None or hiv is None:
            raise Unparseable("countset bounds not integers")
        cnt = 0
        for j in range(lov, hiv + 1):
            if _pred_holds(pred, {**envN, var: mp.mpf(j)}):
                cnt += 1
        return mp.mpf(cnt)
    if k in ("fsum", "fprod"):                 # ∑/∏ k ∈ lo..hi (INCLUSIVE), body
        var, lo, hi, body = node[1], node[2], node[3], node[4]
        lov, hiv = int(evaluate(lo, env)), int(evaluate(hi, env))
        idx = range(lov, hiv + 1)
        if len(node) > 5 and node[5] is not None:  # `with P` filter: ('prime',) keeps only
            if node[5][0] != "prime":              # the prime indices (sympy.isprime, the
                raise Unparseable("finset-filter kind")   # DLMF 27.2.11 ϑ index set)
            idx = [j for j in idx if ob._isprime(j)]
        terms = (evaluate(body, {**env, var: mp.mpf(j)}) for j in idx)
        if k == "fsum":
            return mp.fsum(terms)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k in ("fsumabs", "fprodabs"):           # ∑/∏ i ∈ s, body — s : Finset ι ABSTRACT
        # (DLMF 18.18 Laguerre sum rule): ι := ℕ, s := Finset.range N with N the sampled
        # cardinality (env[fsvar] is a small nat), and the ι-indexed function binders in
        # `body` (c : ι→ℝ, m : ι→ℕ) are sampled callables in env, applied pointwise at the
        # index i. The identity is termwise, so any sampled (c, m, N, α) exercises the same
        # underlying per-term check (Lₙ^α(0) vs (α+1)ₙ/n!). A non-sampled cardinality (s not
        # in env) raises → honest point drop, never a fabricated aggregate.
        var, fsvar, body = node[1], node[2], node[3]
        if fsvar not in env:
            raise Unparseable(f"abstract finset {fsvar} unsampled")
        N = int(evaluate(("var", fsvar), env))
        terms = [evaluate(body, {**env, var: mp.mpf(j)}) for j in range(N)]
        if k == "fsumabs":
            return mp.fsum(terms)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k == "pairagg":                         # ∑/∏ ij ∈ antidiagonal n / n.divisorsAntidiagonal
        tag, kind, base, var, body = node[1], node[2], node[3], node[4], node[5]
        n = int(evaluate(base, env))
        if kind == "antidiag":                 # {(i, n−i) : 0 ≤ i ≤ n}
            pairs = [(mp.mpf(i), mp.mpf(n - i)) for i in range(n + 1)]
        else:                                  # divisorsAntidiagonal: {(d, n/d) : d ∣ n}
            pairs = [(mp.mpf(d), mp.mpf(n // d)) for d in ob._divisors(n)]
        terms = [evaluate(body, {**env, var: p}) for p in pairs]
        if tag == "fsum":
            return mp.fsum(terms)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k in ("fsumprimes", "fprodprimes"):     # ∑/∏ p ∈ Nat.primesLE B, body — primes ≤ B
        var, B, body = node[1], node[2], node[3]
        bv = int(evaluate(B, env))
        if bv > 2_000_000:                     # sieve guard: an oversized bound drops the
            raise Unparseable("primesLE bound too large")   # point, never stalls the sweep
        terms = (evaluate(body, {**env, var: mp.mpf(pp)}) for pp in _primes_upto(bv))
        if k == "fsumprimes":
            return mp.fsum(terms)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k in ("funiverase", "funivfilter"):
        # ∑/∏ over a SUBSET of `Finset.univ` of a `Fin N` index type:
        #   funiverase   `∑ k ∈ Finset.univ.erase j, body`      — DLMF 31.14.5's Σ_{k≠j}
        #   funivfilter  `∏ k ∈ univ.filter (fun k => j < k), body` — 31.15.12's ∏_{j<k}
        # The carrier size is the row's OWN data: the cardinality of a `.q`-tagged
        # Fin-vector applied to the bound index inside the body (`γ k`, `z k`), falling
        # back to any `.q` callable in scope — exactly the rule the bare-univ `∑`/`∏`
        # cases use. No carrier ⇒ Unparseable (honest skip), never a guessed range.
        tag, var, body = node[1], node[2], node[-1]
        qq = _finvec_applied_q(body, var, env)
        if qq is None:
            qq = next((getattr(vv, "q", None) for vv in env.values()
                       if callable(vv) and hasattr(vv, "q")), None)
        if qq is None:
            raise Unparseable("univ-subset carrier")
        idx = []
        if k == "funiverase":
            drop = _near_int(evaluate(node[3], env))
            if drop is None:
                raise Unparseable("univ.erase index not an integer")
            idx = [i for i in range(int(qq)) if i != drop]
        else:
            pv, pred = node[3], node[4]
            for i in range(int(qq)):
                e2 = {**env, var: mp.mpf(i), pv: mp.mpf(i),
                      "_intvars": set(env.get("_intvars", ())) | {var, pv}}
                if _pred_holds(pred, e2):
                    idx.append(i)
        terms = [evaluate(body, {**env, var: mp.mpf(i)}) for i in idx]
        if tag == "fsum":
            return mp.fsum(terms) if terms else mp.mpf(0)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k == "finpairs":                        # ∑/∏ p ∈ univ.filter (p.1 < p.2 : Fin k × Fin k)
        tag, kk, var, body = node[1], node[2], node[3], node[4]
        terms = [evaluate(body, {**env, var + ".1": mp.mpf(i), var + ".2": mp.mpf(j)})
                 for i in range(kk) for j in range(i + 1, kk)]
        if tag == "fsum":
            return mp.fsum(terms)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k in ("fsumset", "fprodset"):           # ∑/∏ d ∈ n.divisors / n.primeFactors, body
        setkind, base, var, body = node[1], node[2], node[3], node[4]
        if base not in env:
            raise Unparseable(f"finset base {base}")
        items = (ob._divisors if setkind == "divisors" else ob._prime_factors)(env[base])
        terms = (evaluate(body, {**env, var: mp.mpf(d)}) for d in items)
        if k == "fsumset":
            return mp.fsum(terms)
        total = mp.mpf(1)
        for t in terms:
            total *= t
        return total
    if k == "dotm":                            # (e).method args — exact dotted postfix
        mname, args = node[2], node[3]
        # (e).derivative[.derivative…] — FORMAL polynomial derivative(s) w.r.t. the
        # indeterminate, as a postfix chain (the Laguerre/Hermite ODE identities).
        if mname == "derivative" and not args:
            order, base = 1, node[1]
            while base[0] == "dotm" and base[2] == "derivative" and not base[3]:
                order += 1
                base = base[1]
            x = env.get(IND)
            if x is None:
                raise Unparseable("derivative without indeterminate")
            return mp.diff(lambda t: evaluate(base, {**env, IND: t}), x, order)
        # (L.smul hlam).g₂ / .weierstrassP z — lattice method on a scaled lattice
        base = node[1]
        if (base[0] == "app" and base[1][0] == "var" and base[1][1].endswith(".smul")
                and mname in _LDOT):
            o = base[1][1][:-5]
            if isinstance(env.get(o), ob._Lattice):
                return _LDOT[mname](env[o].smul(_lam(env)), [evaluate(a, env) for a in args])
        if mname == "choose" and len(args) == 1:       # (p+1).choose i — Nat.choose
            return ob._choose(evaluate(node[1], env), evaluate(args[0], env))
        if mname == "descFactorial" and len(args) == 1:   # (e).descFactorial n — Nat falling
            return _desc_factorial(evaluate(node[1], env), evaluate(args[0], env))
        if (mname == "coeff" and len(args) == 1 and base[0] == "app" and base[1][0] == "var"
                and base[1][1].split(".")[-1] == "qExpansion" and len(base[2]) == 2):
            # (qExpansion h f).coeff m — the m-th q-expansion coefficient of a modular form
            # f : ℍ → ℂ (Mathlib `SlashInvariantForm.qExpansion`, nome q = e^{2πiτ/h}); the
            # Eisenstein σ-divisor expansions (EisensteinModular.lean). Cauchy DFT extraction,
            # decorrelated from the q-series under test (see `_q_expansion_coeff`).
            hh = int(evaluate(base[2][0], env))
            return _q_expansion_coeff(_fn_callable(base[2][1], env), hh,
                                      int(evaluate(args[0], env)))
        if mname == "coeff" and len(args) == 1:         # (P).coeff k — k-th polynomial coefficient
            kk = int(evaluate(args[0], env))            # = k-th Taylor coeff at 0 (exact for a poly)
            f = lambda t: evaluate(node[1], {**env, IND: t})
            return mp.taylor(f, 0, kk)[kk]
        if mname == "map":                              # (P).map (algebraMap ℚ ℂ) — a coefficient
            return evaluate(node[1], env)               # ring-hom cast; numerically the identity
        if mname == "val" and not args and base[0] == "zmodcast":
            # (e : ZMod n).val — the canonical representative of the ℤ-lift in [0, n),
            # i.e. exactly `e mod n` (Mathlib ZMod.val; the least-positive-residue test of
            # Gauss's lemma, DLMF 27.9). Exact-integer gate on the operand and a sampled
            # modulus; anything inexact/unsampled raises → honest point drop, never a
            # fabricated residue.
            ntok = base[1]
            nv = int(ntok) if ntok.isdigit() else env.get(ntok)
            if nv is None or int(nv) < 1:
                raise Unparseable("zmod-val modulus unsampled")
            ev = _near_int(evaluate(base[2], env))
            if ev is None:
                raise Unparseable("zmod-val non-integer operand")
            return mp.mpf(ev % int(nv))
        if mname == "leadingCoeff" and not args:
            # (P).leadingCoeff for a registered polynomial-family head P = head … n:
            # Mathlib defines `leadingCoeff p = p.coeff p.natDegree`, and every registered
            # 'poly'/'lpoly' family has natDegree = its index argument (degree-n families),
            # so this is EXACTLY the existing `.coeff`-at-degree extraction (mp.taylor at
            # the index) — no new convention, reusing the proven coeff machinery. A head
            # that does not resolve to a poly/lpoly entry keeps the honest dot-method skip.
            if base[0] == "app" and base[1][0] == "var":
                hnm = base[1][1]
                e = _reg_get(hnm)
                if e is None or e[0] not in ("poly", "lpoly"):
                    # a bare leaf (`physHermite`) whose registry key is FLMF-qualified
                    # (`FLMF.Functions.Hermite.physHermite` — _reg_resolve only strips
                    # qualified→bare, never the reverse): unique-FLMF-leaf reverse lookup,
                    # poly/lpoly kinds only. Ambiguous or absent → honest skip.
                    cands = [kk for kk in ob.REGISTRY
                             if kk.split(".")[-1] == hnm and kk.startswith("FLMF.")
                             and ob.REGISTRY[kk][0] in ("poly", "lpoly")]
                    e = ob.REGISTRY[cands[0]] if len(cands) == 1 else None
                if e is not None and e[0] in ("poly", "lpoly"):
                    fargs = base[2]
                    if e[0] == "poly":
                        idx = fargs[1] if len(fargs) >= 2 else fargs[0]
                        deg = int(evaluate(idx, env))
                        fn_ = e[1]
                        fnp = lambda t: fn_(deg, t)
                    else:
                        param = evaluate(fargs[0], env)
                        deg = int(evaluate(fargs[1], env))
                        fn_ = e[1]
                        fnp = lambda t: fn_(deg, param, t)
                    return mp.taylor(fnp, 0, deg)[deg]
        if mname in DOT0 and not args:
            return DOT0[mname](evaluate(node[1], env))
        raise Unparseable(f"dot-method {mname}")
    if k == "integral":                        # ∫ x in [lo,hi], body
        var, lo, hi, body = node[1], node[2], node[3], node[4]
        f = lambda t: evaluate(body, {**env, var: t})
        if hi == ("inf",) and lo not in (("inf",), ("neginf",)):
            # Theta lattice-Laplace transforms (DLMF 20.10.4/5): evaluate the term-by-term
            # heat-kernel transform in closed form — the generic ray quadrature below
            # samples the τ → 0 modular cusp and balloons to a MemoryError (docs/ERRATA.md).
            tl = _theta_laplace_value(var, lo, body, env)
            if tl is not None:
                return tl
            # right-infinite ray ∫_lo^∞ (Laplace/Mellin transforms): mpmath's exp-sinh
            # handles exponential decay; the error estimate gates convergence (M9).
            lov = evaluate(lo, env)
            # Theta heat kernels have an integrable t⁻¹ᐟ² endpoint profile.
            # Remove it by t = lo + u² before applying the unchanged guarded
            # ray quadrature.  This is what makes 20.10.4/5 numerically decidable
            # without raising the global evaluation budget.
            if _has_theta_head(body):
                return _quad_ray_theta_sqrt(f, lov)
            try:
                return _quad_ray(f, lov)
            except Unparseable as e:
                msg = str(e)
                # A non-decaying tail that is OSCILLATORY (a cos/sin factor in the integrand) is
                # not divergent but improper-convergent — the Cauchy–Saalschütz / Fresnel ray
                # integrals (§5.9.6–9). `_quad_ray` rejects them either as a non-decaying tail
                # (amplitude doesn't →0, e.g. cos(tⁿ)) or, when the amplitude DOES decay but
                # slowly, as "not-converged" (tanh-sinh stalls on the oscillation, e.g.
                # t^{x−1}sin t at x<0). When such an oscillatory factor is present, route to
                # `mp.quadosc` with a cross-validated value (`_quad_ray_osc`).
                if "nondecaying-tail" in msg or "not-converged" in msg:
                    if _osc_phase(body, var, env) is not None:
                        return _quad_ray_osc(f, lov, body, var, env)
                # A "nondecaying-tail" rejection with NO oscillatory factor can be a genuinely
                # improper-convergent SLOW (algebraic/power-law) tail — the analytic-continuation
                # Γ rep (DLMF 5.9.5, tail ~ t^{x+n−1}) or the Olver-𝐅 Mellin transform (DLMF
                # 15.14.1, tail ~ x^{Re s−1−min(Re a,Re b)}) — whose |f(lo+160)| merely exceeds the
                # 1e-4 FAST-decay gate. `_quad_ray_slow` re-decides it with an independent
                # tail-exponent < −1 integrability certificate PLUS the quadrature error gate (a
                # truly-divergent monomial is rejected by the exponent test); on any failure it
                # re-raises and the sample drops. Additive — reached only after `_quad_ray` raised.
                if "nondecaying-tail" in msg:
                    return _quad_ray_slow(f, lov)
                # A "not-converged" rejection with NO oscillatory factor is, for an exponentially
                # decaying integrand, the signature of a REMOVABLE endpoint singularity that
                # cancels catastrophically in float (Binet's §5.9.10″). Re-attempt with
                # depth-adaptive guard precision, still gated by the quadrature's own error.
                if "not-converged" in msg:
                    return _quad_ray_smooth(f, lov)
                raise
        if lo == ("neginf",) and hi == ("inf",):
            # doubly-infinite ∫_{−∞}^{∞}: trust ONLY a decaying integrand (Gaussian-damped
            # Fourier integrals). A non-decaying tail (e.g. Re b ≤ 0) is dropped, never
            # half-trusted — the soundness guard that lets us avoid an uncaptured Re b>0 hyp.
            far = [mp.mpf(15), mp.mpf(30), mp.mpf(60)]
            try:
                tail = [abs(f(x)) + abs(f(-x)) for x in far]
            except (ValueError, ZeroDivisionError, OverflowError):
                raise Unparseable("infinite-integral-tail-undefined")
            if not (tail[2] <= tail[1] <= tail[0]):
                # a NON-monotone (increasing/bumpy-growing) envelope is genuinely non-decaying —
                # divergent or out-of-domain, never trusted.
                raise Unparseable("infinite-integral-nondecaying")
            # A monotone-decreasing envelope that is still large at t=±60 (tail[2] > 1e-4) is a
            # SLOW power-law tail — the Barnes beta vertical-line rep DLMF 5.12.8 decays only like
            # |t|^{−(a+b)} with a+b>1 (down to |t|^{−1−ε}), so at t=60 the envelope is ~1e-2, far
            # above 1e-4 even though the integral converges. The old gate hard-rejected these
            # convergent contours together with the truly-divergent ones. DECIDE them the sound
            # way instead — the certified-quadrature error estimate below (same gate as the
            # ratio>0.02 branch) accepts a convergent contour (qerr/|v| ≈ 1e-18) and rejects a
            # divergent one (qerr ≈ 2). Route the slow monotone envelope straight to that decision.
            slow_monotone = tail[2] > mp.mpf("1e-4")
            # A SLOW (polynomial) tail envelope ⇒ an oscillatory / bumpy integrand with slowly
            # decaying amplitude — e.g. products of Γ(±t), whose reflection-formula sin-factors
            # give period-1 bumps decaying like t^{−p}. tanh-sinh `mp.quad` converges poorly there
            # (~1e-5, precision-independent); `mp.quadosc` is built for it. A FAST (exponential)
            # tail — Gaussian-damped Fourier integrals — has tail[2] ≈ 0 and stays on `mp.quad`.
            ratio = tail[2] / tail[1] if tail[1] > 0 else mp.mpf(0)
            if ratio > mp.mpf("0.02") or slow_monotone:
                # A SLOW (polynomial) tail envelope ⇒ an oscillatory / bumpy integrand with slowly
                # decaying amplitude — e.g. products of Γ(±t), whose reflection-formula sin-factors
                # give period-1 bumps decaying like t^{−p} (the Ramanujan integral §5.13.4). tanh-sinh
                # `mp.quad` stalls there (~1e-5); `mp.quadosc` does far better on well-conditioned
                # samples (verified 1e-12…1e-19 for a+b+c+d ≳ 5) but only ~1e-4…1e-6 near the
                # convergence boundary (a+b+c+d → 3⁺), where the integral is essentially divergent
                # and NO quadrature reaches the gate. Since the oracle cannot reliably DECIDE such a
                # sample, SKIP honestly rather than risk false-FAILing a true identity — a refutation
                # must come from a point we can actually evaluate. (FAST/exponential ∫_ℝ — Gaussian-
                # damped Fourier integrals — have tail[2] ≈ 0 and fall through to `mp.quad` below.)
                #
                # ADDITIVE certified-quadrature attempt (2026-07-21, unables-1 heavy-numeric):
                # the "tanh-sinh always stalls here" premise is too pessimistic for the
                # well-conditioned Barnes-type bi-infinite POWER-LAW contours (DLMF 5.12.8/9 beta
                # vertical-line reps, 5.13.4 Ramanujan reciprocal-Γ integral). The envelope is
                # ALREADY certified monotone-decaying (tail[2] ≤ tail[1] ≤ tail[0], checked above),
                # so the only question is whether `mp.quad` converges — and mp.quad carries its OWN
                # error estimate, the same soundness certificate `_quad_ray` uses on the semi-infinite
                # ray. Measured on the sampled grids: well-conditioned beta samples give qerr/|v| ≈
                # 1e-18…1e-44 (accept, rel-vs-RHS ≈ 1e-17), while a DIVERGENT integrand (a+b<1 for
                # 5.12.8) returns a huge value with qerr ≈ 2 (reject), and a near-convergence-boundary
                # Ramanujan sample (a+b+c+d → 3⁺) keeps qerr ≈ 0.2 (reject). So: trust mp.quad ONLY
                # when its own relative error estimate certifies convergence below QUAD_CONTOUR_GATE;
                # everything the estimate does not certify falls through to the honest skip below —
                # cannot fabricate a PASS (a wrong value that also had a tiny error estimate is
                # excluded by the estimate itself; the equality residual is still gated at TOL) and
                # cannot fabricate a FAIL (an uncertified sample is dropped, never scored). Purely
                # additive: strictly more well-conditioned contour samples become decidable, none of
                # the previously-skipped divergent/boundary samples change verdict.
                QUAD_CONTOUR_GATE = mp.mpf("1e-10")
                try:
                    _qv, _qerr = mp.quad(f, [-mp.inf, 0, mp.inf], error=True)
                except Exception:
                    _qv, _qerr = None, None
                if _qv is not None and mp.isfinite(_qv) and mp.isfinite(_qerr) \
                        and _qerr <= QUAD_CONTOUR_GATE * max(mp.mpf(1), abs(_qv)):
                    return _qv
                raise Unparseable("infinite-integral-oscillatory")
            # DOUBLY-EXPONENTIALLY damped integrands (exp(−M·cosh x), the DLMF 10.32.9 /
            # coshExp_integral_eq_two_besselK0 row): the literal infinite-interval tanh-sinh
            # transform stalls for minutes on them at EVERY M, while the integrand has
            # already underflowed far inside the sampled window. When the pre-check's own
            # tail samples certify total underflow at ±30 AND ±60 (≤ 1e-35 — dozens of
            # orders below every gate in play, reusing the `tail` values computed above),
            # integrate the truncated [−40, 40] instead: the omitted tails are below any
            # representable contribution at working precision (measured: reproduces
            # 2·K₀(M) to full precision in ~0.05 s at every sampled M vs a >30 s stall).
            # Pure compute-budget change scoped to this certified-underflow shape; the
            # tolerance/gates and every non-underflowing row's path are unchanged.
            if tail[1] <= mp.mpf("1e-35") and tail[2] <= mp.mpf("1e-35"):
                return mp.quad(f, [-40, 0, 40])
            # EXPONENTIALLY-DECAYING but not-yet-underflowed contour integrands — the
            # Barnes-ζ vertical-line reps Ln Γ(z+1) / ψ(z+1) (DLMF 5.9.11 / 5.9.17):
            # the integrand is π z^{-s} ζ(-s)/(s sin πs) on Re s = -c, whose 1/sin(πs)
            # forces a genuine e^{-π|t|} baseline envelope only partly offset by z^{-s}'s
            # e^{|arg z|·|t|} (|arg z| < π), so the envelope decays exponentially and is
            # ALREADY certified monotone-decreasing above (tail[2] ≤ tail[1] ≤ tail[0]).
            # But the literal [-∞,∞] tanh-sinh transform OVER-refines on the oscillatory
            # z^{-it}·ζ(c-it) phase and stalls past the 8 s per-sample EVAL_BUDGET → a false
            # eval-timeout skip of a TRUE identity (measured: >280 s for a single sample vs
            # 0.6 s for the finite window; docs/verification/resolve-surfaces/probe_zeta_all.py).
            # Generalise the fixed-[-40,40] underflow truncation to an ADAPTIVE finite window:
            # walk an increasing grid, REQUIRING the sampled envelope to keep strictly
            # decreasing (else bail to the infinite quad — a non-monotone tail is NOT
            # certifiable), and cut at the first T whose endpoint envelope has fallen below
            # 1e-30 — twelve orders below the tightest equality gate (TOL = 1e-18), so the
            # omitted tail (bounded by that already-decaying endpoint value times a finite
            # decay length) cannot move the residual past the gate. Purely additive: fires
            # ONLY on the exponentially-decaying samples that currently fall through to the
            # stalling infinite quad; a slow power-law contour was already routed to the
            # certified-quadrature gate above (ratio>0.02 / slow_monotone) and never reaches
            # here, and a correct integrand's finite window agrees with its infinite quad
            # (probe_zeta_all.py: rel ≤ 1.3e-26 at every curated in-domain sample).
            _prev, _Tcut = tail[1], None
            for _T in (40, 60, 80, 100, 140):
                try:
                    _e = abs(f(_T)) + abs(f(-_T))
                except (ValueError, ZeroDivisionError, OverflowError):
                    break
                if not mp.isfinite(_e) or _e > _prev:
                    break                                # envelope not certified-decreasing
                _prev = _e
                if _e <= mp.mpf("1e-30"):
                    _Tcut = _T
                    break
            if _Tcut is not None:
                return mp.quad(f, [-_Tcut, 0, _Tcut])
            return mp.quad(f, [-mp.inf, 0, mp.inf])   # 0 as a node helps centred integrands
        if lo == ("neginf",) and hi not in (("inf",), ("neginf",)):
            # left-infinite ray ∫_{−∞}^{b} (expint_6_2_5's Iic split, DLMF 6.2.5): reflect
            # t ↦ −u onto the right ray [−b, ∞) and reuse `_quad_ray` — its decay/endpoint
            # guards apply unchanged (a non-decaying reflected tail drops the point).
            hiv = evaluate(hi, env)
            return _quad_ray(lambda u: f(-u), -hiv)
        if lo in (("inf",), ("neginf",)) or hi in (("inf",), ("neginf",)):
            # other left-infinite rays stay deferred (oscillatory, ill-conditioned).
            raise Unparseable("infinite-integral")
        lov, hiv = evaluate(lo, env), evaluate(hi, env)
        # Endpoint-singular integrands (e.g. ∫₀¹ t^(z−1), Beta integrals) lose digits in
        # tanh-sinh at the base precision — ~7e-11 at 30 dps for strong singularities,
        # enough to FALSE-FAIL a proven identity against the 1e-12 quad gate. Doubling the
        # working precision recovers the accuracy WITHOUT loosening the gate (so real small
        # discrepancies are still caught). Endpoints passed as nodes so the singularity is split.
        # A WIDE interval (many periods) whose integrand carries an oscillatory cos/sin factor
        # (the §5.9.6–9 `Tendsto (fun R => ∫ t in 0..R, …) atTop …` improper-integral limit
        # forms, sampled at increasing finite R) is exactly where a single tanh-sinh call over
        # [lo,hi] is unsound — see `_quad_finite_osc`. Try the phase-aligned panel split FIRST;
        # it only activates (returns non-None) for that oscillatory/wide shape, so every other
        # finite interval integral (Beta, moment, …) is untouched.
        if hiv - lov > mp.mpf(20):
            osc_val = _quad_finite_osc(f, lov, hiv, body, var, env)
            if osc_val is not None:
                return osc_val
        # PIECEWISE integrands built on the fractional part (periodicBernoulli k t = Bₖ({t}),
        # Int.fract): tanh-sinh assumes analyticity — over [1, n] the integer kinks cost
        # ~1e-8 and FALSE-FAIL an exact Euler–Maclaurin identity (sum_klogk_eulerMaclaurin,
        # DLMF 5.17.6). Split at the interior integer breakpoints (each panel is analytic).
        # ADDITIVE: fires only when the body syntactically contains a fract-based head.
        if _contains_head(body, _FRACT_HEADS) and mp.isfinite(lov) and mp.isfinite(hiv) \
                and abs(hiv - lov) <= 1000:
            a, b = (lov, hiv) if lov <= hiv else (hiv, lov)
            brk = [a] + [mp.mpf(m) for m in range(int(mp.ceil(a)), int(mp.floor(b)) + 1)
                         if a < m < b] + [b]
            with mp.workdps(2 * mp.mp.dps):
                v = mp.quad(f, brk)
            return v if lov <= hiv else -v
        with mp.workdps(2 * mp.mp.dps):
            return mp.quad(f, [lov, hiv])
    if k == "mintegral":                       # ∫ x, body ∂μ  (weighted measure integral)
        var, meas, body = node[1], node[2], node[3]
        if meas not in MEASURES:
            raise Unparseable(f"measure {meas}")
        (mlo, mhi, weight, nodes) = MEASURES[meas]
        f = lambda t: evaluate(body, {**env, var: t}) * weight(t)
        with mp.workdps(2 * mp.mp.dps):        # raise precision for endpoint-singular weights
            return mp.quad(f, nodes)           # tanh-sinh handles the endpoint singularity
    if k == "ite":                             # if cond then a else b
        cond, a, b = node[1], node[2], node[3]
        return evaluate(a, env) if _cond_true(cond, env) else evaluate(b, env)
    if k == "app":
        head = node[1]
        args = node[2]
        while head[0] == "app":            # flatten a curried application: (f a) b → f a b
            args = head[2] + args
            head = head[1]
        if head[0] == "lam" and len(head) == 3 and len(args) == 1:
            # β-reduction: an explicit single-binder lambda applied to one argument —
            # `(fun x => …) t`, produced by the definitional unfolding of ODE-solution
            # predicates (_unfold_ode_pred: the bundled solution y applied at −x / x+2π).
            # The binder shadows any outer sample of the same name, exactly like the
            # _fn_callable lambda path. Multi-binder / partial shapes keep the honest skip.
            return evaluate(head[2], {**env, head[1]: evaluate(args[0], env)})
        if head[0] == "lam" and len(head) > 3 and len(args) == 1 + len(head[3]):
            # full β-reduction of a multi-binder lambda — `(fun k t => …) i x`, produced
            # by the IsCDSystem definitional unfolding (_unfold_cd_pred: the polynomial
            # system p applied at (index, point)). Arguments are evaluated in the OUTER
            # env, then all binders bound at once (same shadowing semantics as the
            # single-binder case). Partial applications keep the honest skip.
            sub = dict(env)
            for b, a in zip((head[1], *head[3]), args):
                sub[b] = evaluate(a, env)
            return evaluate(head[2], sub)
        if head[0] == "var" and head[1].split(".")[-1] == "limUnder" \
                and len(args) == 2 and args[0][0] == "nhds" and args[1][0] == "lam":
            # `limUnder (𝓝 pt) (fun x => …)` — a Filter.limUnder over a neighbourhood filter
            # (the coupled-parameter limit of DLMF 15.2.6, and the ε-boundary limits of
            # 15.2.3). Evaluated as a sound directional numeric limit (_num_limUnder): the
            # two-sided 𝓝 case is scored only when direction-independent, else honest skip.
            return _num_limUnder(args[0], args[1], env)
        if head[0] == "princhar":
            # `(1 : DirichletCharacter ℂ k) a` / `(1 : MulChar (ZMod k) ℂ) a` — the
            # PRINCIPAL character mod k applied to a residue (parsed to a ("princhar", k)
            # head by the ascription rule). Evaluated by the DLMF 27.8.1 defining formula:
            # χ₁(a) = 1 if gcd(a, k) = 1 else 0, with a taken as its ℤ-lift mod the
            # sampled k (the same int/gcd convention as the IsUnit pair filter in
            # _pairs_ok). A missing or non-integer (k, a) is an honest point drop, never
            # a fabricated number.
            if len(args) != 1:
                raise Unparseable("princhar arity")
            kv = env.get(head[1], head[1])
            try:
                kk = int(kv)
                av = int(evaluate(args[0], env))
            except (TypeError, ValueError):
                raise Unparseable("princhar operand")
            if kk < 1:
                raise Unparseable("princhar modulus")
            return mp.mpf(1) if _math.gcd(av % kk, kk) == 1 else mp.mpf(0)
        if head[0] == "iterop":
            # (OP^[n]) g pt — n-fold Function.iterate of a first-order differential operator
            # OP, applied to function g and evaluated at point pt (DLMF 15.5.3/5/7/8). The
            # operator transformers in _ITEROPS mirror the Lean file's private abbrevs EXACTLY
            # (Ch15DerivativesContiguous.lean:17-22); Function.iterate `^[n]` composes them n
            # times via nested high-precision mp.diff. A free-function operand (the abstract
            # `f` of 15.5.10) is not a lambda/registry fn, so _fn_callable raises → honest skip;
            # an unknown operator likewise raises. Validated in docs/verification/ch15/probe_ops.py.
            n_ast, base = head[1], head[2]
            if len(args) != 2 or base[0] != "var" or base[1] not in _ITEROPS:
                raise Unparseable("iterop shape")
            op = _ITEROPS[base[1]]
            h = _fn_callable(args[0], env)
            for _ in range(int(evaluate(n_ast, env))):
                h = op(h)
            return h(evaluate(args[1], env))
        if head[0] != "var":
            raise Unparseable("non-symbol head")
        name = head[1]
        if callable(env.get(name)):        # a function-valued binder (a Dirichlet character χ a)
            return env[name](*[evaluate(a, env) for a in args])
        # ── `n.factorization.prod fun p k => body` — Finsupp.prod over the prime
        # factorization of n (the DLMF 27.3.2 surface f(n) = ∏_p f(p^{a_p})): the exact
        # product of body(p, k) over the prime powers p^k ∥ n (ob._factorization, anchored
        # in oracle_bindings.verify() by reconstruction n = ∏ p^k). Mathlib's
        # `Nat.factorization 1 = 0` gives the empty product 1 at n = 1, matching. Only the
        # exact two-binder untyped-lambda shape is handled; anything else falls through to
        # the honest unbound/unparsed skip — never a fabricated value. ──
        if "." in name:
            o, _, m = name.partition(".")
            if (m == "factorization.prod" and o in env and len(args) == 1
                    and args[0][0] == "lam" and len(args[0]) > 3 and len(args[0][3]) == 1):
                lam = args[0]
                out = mp.mpf(1)
                for pr, ex in ob._factorization(env[o]):   # _nat-checked: a non-natural
                                                           # sample raises → point dropped
                    out *= evaluate(lam[2], {**env, lam[1]: mp.mpf(pr),
                                             lam[3][0]: mp.mpf(ex)})
                return out
        # ── real/complex power operator: `Real.rpow x y` / `Complex.cpow x y` = xʸ ──
        # (Lean's `**`; rpow's principal real power, cpow the principal complex branch). The
        # registry has no binding for these, so evaluate them directly. `mp.power` takes the
        # principal branch, matching Mathlib's `Real.rpow`/`Complex.cpow` on their domains
        # (Real.rpow of a negative base is a Mathlib junk convention — `mp.power` raises/goes
        # complex there, which surfaces as a dropped point, never a false number).
        if name in ("Real.rpow", "Complex.cpow", "NNReal.rpow", "rpow", "cpow") and len(args) == 2:
            return mp.power(evaluate(args[0], env), evaluate(args[1], env))
        # ── Weierstrass lattice dispatch (M15) ──
        if name in ("deriv", "logDeriv") and len(args) == 2:   # deriv/logDeriv of W.zeta/W.sigma
            f = _bundle_fn(args[0], env)
            if f is not None:
                x = evaluate(args[1], env)
                return mp.diff(f, x) if name == "deriv" else mp.diff(f, x) / f(x)
        if name == "℘[]":                          # ℘[L] z — Weierstrass ℘ bracket notation
            L = _aslat(args[0], env)
            if L is not None:
                return ob._wp(L, evaluate(args[1], env))
        if name.split(".")[-1] == "additionMatrix" and len(args) == 3:
            # `additionMatrix L u v` (WeierstrassAdditionDet.lean:64, DLMF 23.10.1) — the
            # explicit 3×3 matrix !![℘u, ℘'u, 1; ℘v, ℘'v, 1; ℘(u+v), −℘'(u+v), 1],
            # transcribed row-for-row from the Lean `!![…]` literal with the already-
            # anchored ob._wp/_wp_deriv (exact, no approximation). Consumed by the
            # `.det` dot-method (DOT0) — the value is an mp.matrix, never a scalar.
            La = _aslat(args[0], env)
            if La is not None:
                uu, vv = evaluate(args[1], env), evaluate(args[2], env)
                return mp.matrix(
                    [[ob._wp(La, uu), ob._wp_deriv(La, uu), mp.mpc(1)],
                     [ob._wp(La, vv), ob._wp_deriv(La, vv), mp.mpc(1)],
                     [ob._wp(La, uu + vv), -ob._wp_deriv(La, uu + vv), mp.mpc(1)]])
        if name == "secondDerivWeierstrassP" and len(args) == 2:   # ℘''(z): differentiate ℘'
            L = _aslat(args[0], env)                               # once (decorrelated from the
            if L is not None:                                     # 6℘²−g₂/2 identity it's tested on)
                return mp.diff(lambda zz: ob._wp_deriv(L, zz), evaluate(args[1], env))
        if "." in name:                            # L.weierstrassP z / L.G n (dotted-var head)
            o, _, m = name.partition(".")
            if isinstance(env.get(o), ob._Lattice) and m in _LDOT:
                return _LDOT[m](env[o], [evaluate(a, env) for a in args])
        if name in _LARG:                          # discriminant L / kleinJ L / eᵢ L / E₄ L
            L = _aslat(args[0], env)
            if L is not None:
                return _LARG[name](L)
        if name in ("derivative", "Polynomial.derivative"):
            # FORMAL polynomial derivative d/dX over R[X] — the polynomial-identity analog
            # of inline `deriv`: differentiate the operand w.r.t. the sampled indeterminate.
            if len(args) != 1:
                raise Unparseable("derivative arity")
            order, p = 1, args[0]
            while (p[0] == "app" and p[1] in (("var", "derivative"), ("var", "Polynomial.derivative"))
                   and len(p[2]) == 1):
                order += 1
                p = p[2][0]
            x = env.get(IND)
            if x is None:
                raise Unparseable("derivative without indeterminate")
            return mp.diff(lambda t: evaluate(p, {**env, IND: t}), x, order)
        if name.split(".")[-1] in ("cfConv", "cfConvC") and len(args) == 3:
            # FLMF.Error.cfConv a b N — the N-th Wallis convergent (DLMF §7.9 / §7.18.13). The
            # 7.18.13 row wraps this in `fun N => cfConv a b N`, so it reaches `evaluate` directly
            # (the 7.9.x rows pass the partial `cfConv a b` to _callable instead). Both routes
            # share `_cfconv_eval`; the two sequence args are `if k = … then …` lambdas.
            # `cfConvC` (ComplexErfExtra.lean, erf_7_9_3's Faddeeva CF) is the literal complex
            # analogue — same Wallis recurrence, and `_cfconv_eval` is already generic over
            # mpmath complex arithmetic, so the widened name-match is the whole fix.
            aseq, bseq = _seq_callable(args[0], env), _seq_callable(args[1], env)
            if aseq is None or bseq is None:
                raise Unparseable("cfConv non-lambda sequence")
            return _cfconv_eval(aseq, bseq, evaluate(args[2], env))
        if name.split(".")[-1] == "pFq":  # FLMF[.Hypergeometric].pFq A B z (DLMF 16.2.1) = ₚFᵩ(A;B;z)
            # Leaf-match (like `cfConv` above) so the fully-qualified head
            # `FLMF.Hypergeometric.pFq` — written verbatim in statements such as erf_7_11_7 —
            # is bound too (the `pFq` leaf is NOT a REGISTRY key, so namespace stripping does
            # not reach it). Anchored to the DLMF 16.2.1 defining series ₚFᵩ = mp.hyper(A,B,z),
            # reading the literal `![…]` upper/lower parameter vectors.
            if len(args) != 3:
                raise Unparseable("pFq arity")
            return mp.hyper(_veclist(args[0], env), _veclist(args[1], env), evaluate(args[2], env))
        if name.split(".")[-1] == "pFqCoefficient":
            # FLMF[.Hypergeometric].pFqCoefficient A B n (DLMF 16.2.1) = (∏ᵢ(Aᵢ)ₙ)/((∏ⱼ(Bⱼ)ₙ)·n!),
            # the ₚFᵩ series coefficient. Leaf-match (like `pFq` above) since the A/B parameter
            # tuples parse to finvecC callables `_veclist` reads (a registry 'fn' head cannot
            # receive them). Numeric kernel is the self-validated `ob._pFqCoefficient`.
            if len(args) != 3:
                raise Unparseable("pFqCoefficient arity")
            return ob._pFqCoefficient(_veclist(args[0], env), _veclist(args[1], env),
                                      evaluate(args[2], env))
        if name.split(".")[-1] == "meijerG":  # FLMF[.MeijerG].meijerG bNum aNum bDen aDen σ z
            # (DLMF 16.17.1, Frameworks/MeijerG.lean) — the Mellin–Barnes Meijer G-function.
            # Leaf-match (like `pFq`/`cfConv` above) so the fully-qualified head reaches this
            # branch too. The 4 parameter-vector args are read via `_veclist` (a `![…]`
            # literal, OR the `fun _ : Fin 0 => 0`/`(0 : ℂ)` EMPTY-vector idiom used by the
            # proven meijerG_exp / meijerG_eq_pFq_zero rows); σ (arg 5) is accepted but unused
            # (see `ob._meijerG`'s docstring: the value is contour-independent on any
            # admissible line, and mpmath.meijerg picks its own contour). Genuinely
            # `Fin (q+1)`-parametrized vector args (meijerG_eq_pFq's `fun i => 1 - A i`) are
            # NOT recognized by `_veclist` — that row (which also carries an intentional
            # `sorry`) keeps its own honest unbound/unparsed skip.
            if len(args) != 6:
                raise Unparseable("meijerG arity")
            bNum, aNum, bDen, aDen = (_veclist(a, env) for a in args[:4])
            z = evaluate(args[5], env)
            return ob._meijerG(bNum, aNum, bDen, aDen, z)
        if name.split(".")[-1] == "qHyper":  # FLMF.QSeries.qHyper r s ![a…] ![b…] q z
            # (DLMF 17.4.1, QHypergeometric.lean) — the basic hypergeometric series
            # ᵣφₛ(a;b;q,z). Leaf-match (like `pFq`/`meijerG` above) because its `![…]`
            # parameter vectors parse to ('vec', …) nodes that only an extractor-side
            # branch can read via _veclist — a registry 'fn' head cannot receive them.
            # The numeric kernel is the REGISTRY's own `qHyper` binding (bindings lane,
            # signature (r, s, [a…], [b…], q, z) mirroring the Lean def); while that
            # binding is absent the head keeps the honest `unbound:qHyper` skip.
            if len(args) != 6:
                raise Unparseable("qHyper arity")
            _qh = _reg_get("qHyper")
            if _qh is None or _qh[0] != "fn":
                raise Unparseable("unbound head qHyper")
            return _qh[1](evaluate(args[0], env), evaluate(args[1], env),
                          _veclist(args[2], env), _veclist(args[3], env),
                          evaluate(args[4], env), evaluate(args[5], env))
        if name in ("aeval", "Polynomial.aeval"):   # `aeval x P` = P evaluated at x (algebra eval)
            if len(args) != 2:
                raise Unparseable("aeval arity")
            return evaluate(args[1], {**env, IND: evaluate(args[0], env)})
        if name == "PowerSeries.exp":    # PowerSeries.exp A = Σ Xⁿ/n! = e^X (type arg dropped)
            x = env.get(IND)
            if x is None:
                raise Unparseable("PowerSeries.exp without indeterminate")
            return mp.e ** x
        if name == "PowerSeries.mk":     # PowerSeries.mk (fun n => cₙ) = Σ cₙ Xⁿ
            if len(args) != 1 or args[0][0] != "lam":
                raise Unparseable("PowerSeries.mk shape")
            lam, x = args[0], env.get(IND)
            if x is None:
                raise Unparseable("PowerSeries.mk without indeterminate")
            return _bounded_nsum(lambda n: evaluate(lam[2], {**env, lam[1]: mp.mpf(n)}) * x ** n,
                                 start=0)
        if name == "PowerSeries.rescale":  # rescale t f = f(tX) — substitute X ↦ tX in f
            if len(args) != 2:
                raise Unparseable("rescale arity")
            t, x = evaluate(args[0], env), env.get(IND)
            if x is None:
                raise Unparseable("rescale without indeterminate")
            return evaluate(args[1], {**env, IND: t * x})
        if name == "PowerSeries.coeff" and len(args) == 2:
            # `PowerSeries.coeff m (qExpansion h f)` — the PREFIX form of the dot-notation
            # `(qExpansion h f).coeff m` handled under "dotm" (discriminant_qExpansion_coeff_one,
            # ModularDiscriminant.lean): the m-th q_h-expansion coefficient of a modular form
            # f : ℍ → ℂ via the decorrelated Cauchy-DFT `_q_expansion_coeff` (self-validated
            # against the DLMF 23.17 anchor Δ = q∏(1−qⁿ)²⁴: coeffs = Ramanujan τ(m) —
            # 0, 1, −24, 252, −1472, 4830 for m = 0…5, reproduced to ~1e-27 at 40 dps).
            # Any other operand shape falls through to the honest `unbound head` skip.
            ser, sargs = args[1], []
            while ser[0] == "app":             # flatten a curried (qExpansion h) f
                sargs = ser[2] + sargs
                ser = ser[1]
            if ser[0] == "var" and ser[1].split(".")[-1] == "qExpansion" and len(sargs) == 2:
                hh = int(evaluate(sargs[0], env))
                return _q_expansion_coeff(_fn_callable(sargs[1], env), hh,
                                          int(evaluate(args[0], env)))
            # GENERIC formal-power-series coefficient (prefix form): `PowerSeries.coeff m S`
            # = the m-th Taylor coefficient at 0 of S's generating-function value — the same
            # extraction as the postfix `(P).coeff k` dotm branch above, now reachable when S
            # evaluates at the indeterminate (`PowerSeries.mk`-built series and the anchored
            # psfn/psfn1 g.f. bindings, e.g. `PowerSeries.coeff n (hermiteGF x)`,
            # coeff_hermiteGF / DLMF 18.12.16). Sound whenever the numeric value IS the sum
            # function on a positive radius about 0 (true for mk's bounded partial sum and
            # the entire/algebraic psfn g.f.s); an operand that cannot evaluate raises inside
            # the lambda → the honest unbound/unparsed skip, never a fabricated number.
            kk = int(evaluate(args[0], env))
            f = lambda t: evaluate(args[1], {**env, IND: t})
            return mp.taylor(f, 0, kk)[kk]
        if name == "U" and len(args) == 2 and _is_parabolic_U(args[0], env):
            # parabolic cylinder U(a,x) (DLMF 12.2) vs Chebyshev Uₙ (`U R n`, R a ring TYPE):
            # parabolic's first arg is a NUMBER (binder ℝ/ℂ or a literal expr), Chebyshev's is a
            # type. Disambiguate on the first arg's binder type (threaded in as env["_binders"]).
            return mp.pcfu(evaluate(args[0], env), evaluate(args[1], env))
        if name == "monomial":           # Polynomial.monomial n c = c·Xⁿ (at the indeterminate)
            if len(args) != 2:
                raise Unparseable("monomial arity")
            x = env.get(IND)
            if x is None:
                raise Unparseable("monomial without indeterminate")
            return evaluate(args[1], env) * x ** int(evaluate(args[0], env))
        if name == "hermitePearson.rodrigues":   # `… (fun n => (-1)ⁿ) n x` — leading λ is the
            # FIXED (−1)ⁿ normalization; drop it. The abstract Pearson-witness path
            # (_pearson_witness, rodrigues_spec) arrives with the κ-slot already
            # substituted to the anchored `hermitePearsonNorm` — the SAME (−1)ⁿ row of
            # DLMF Table 18.5.1 — so accept that var alongside the concrete λ form.
            if len(args) != 3 or not (args[0][0] == "lam"
                                      or args[0] == ("var", "hermitePearsonNorm")):
                raise Unparseable("hermitePearson.rodrigues shape")
            return ob._hermitePearson_rodrigues(evaluate(args[1], env), evaluate(args[2], env))
        if name == "mellin":            # Mathlib mellin f s = ∫₀^∞ t^{s−1} f(t) dt
            if len(args) != 2:
                raise Unparseable("mellin arity")
            g = _callable(args[0], env)  # the transformed function (a lambda / registry fn / indicator)
            if g is None:
                raise Unparseable("mellin func unsupported")
            s = evaluate(args[1], env)
            sup = _indicator_support(args[0], env)
            if sup is not None:          # masked to a FINITE interval (a,b]: integrate there
                lo, hi = sup             # directly (the jump at the endpoint would stall the ray quad)
                intg = lambda t: t ** (s - 1) * g(t)
                wedge = [abs((t - lo) * intg(t)) for t in
                         (lo + mp.mpf("1e-3"), lo + mp.mpf("1e-5"), lo + mp.mpf("1e-7"))]
                if not (wedge[2] <= wedge[1] <= wedge[0] + mp.mpf("1e-12")):
                    raise Unparseable("mellin-indicator-endpoint-singular")
                return mp.quad(intg, [lo, hi])
            return _quad_ray(lambda t: t ** (s - 1) * g(t), 0)
        if name == "laplace":           # FLMF laplace f s = ∫₀^∞ e^{−st} f(t) dt
            if len(args) != 2:
                raise Unparseable("laplace arity")
            g = _callable(args[0], env)
            if g is None:
                raise Unparseable("laplace func unsupported")
            s = evaluate(args[1], env)   # divergent (Re a > Re s) points drop via _quad_ray guards
            return _quad_ray(lambda t: mp.e ** (-s * t) * g(t), 0)
        if name.split(".")[-1] == "laplaceTransform":
            # Methods head `laplaceTransform f s = ∫_{(0,∞)} e^{−st} f(t) dt` (Methods/
            # LaplaceTransform.lean, DLMF 1.14.17): like `laplace`/`mellin`, its FIRST argument
            # is a FUNCTION (the DLMF 7.14.2 `fun t => (erf (b t) : ℂ)`), which must be routed
            # through `_callable`, not scalar `evaluate` (a bare `lam` node raises "node lam" →
            # every point drops → a spurious undersampled/domain skip). Delegate the quadrature
            # to the registry binding `ob._laplace_transform` (self-validated in
            # oracle_bindings.verify() against 𝓛[1] = 1/s and 𝓛[e^{−t}] = 1/(s+1), and its own
            # Re s ≤ 0.05 half-plane guard drops off-convergence points). ADDITIVE: fires only on
            # the `laplaceTransform` head with a supported function operand; any other spelling
            # keeps the honest skip.
            if len(args) != 2:
                raise Unparseable("laplaceTransform arity")
            g = _callable(args[0], env)
            if g is None:
                raise Unparseable("laplaceTransform func unsupported")
            s = evaluate(args[1], env)
            return ob._laplace_transform(g, s)
        if name.split(".")[-1] == "mathieuOp":
            # FLMF mathieuOp a q y x = y''(x) + (a − 2q·cos 2x)·y(x) — the Mathieu operator
            # (DLMF 28.2.1, Mathieu/Basic.lean). Higher-order head (like mellin/logDeriv):
            # the 3rd argument is a FUNCTION (a lambda / registry fn / partial application),
            # routed through _fn_callable, never scalar `evaluate`. Math in ob._mathieu_op
            # (self-validated against the 28.2.1 defining formula in oracle_bindings' anchors).
            if len(args) != 4:
                raise Unparseable("mathieuOp arity")
            g = _fn_callable(args[2], env)
            return ob._mathieu_op(evaluate(args[0], env), evaluate(args[1], env),
                                  g, evaluate(args[3], env))
        if name.split(".")[-1] in ("cdSummand", "cdCross"):
            # FLMF Christoffel–Darboux building blocks (ChristoffelDarboux.lean; DLMF
            # 18.2.12): cdSummand p h k x y = pₖ(x)pₖ(y)/hₖ (the kernel summand) and
            # cdCross p a k x y = aₖ·(pₖ₊₁(x)pₖ(y) − pₖ(x)pₖ₊₁(y)) (the cross term).
            # Higher-order heads (like mathieuOp/LSeries.term): the first TWO arguments
            # are FUNCTIONS (the ∀-quantified family, instantiated at the anchored
            # Chebyshev-T witness by the IsCDSystem '_fnwitness' rule in _binders),
            # routed through _fn_callable, never scalar `evaluate`. Math in
            # ob._cd_summand/_cd_cross, self-validated in oracle_bindings' anchors
            # against the DLMF 18.2.12 telescoping clauses, the orthogonality-integral
            # norms hₖ, and the leading-coefficient aₖ = kₖ/(hₖ kₖ₊₁) — never by name.
            if len(args) != 5:
                raise Unparseable(f"{name.split('.')[-1]} arity")
            f1, f2 = _fn_callable(args[0], env), _fn_callable(args[1], env)
            _cdfn = ob._cd_summand if name.split(".")[-1] == "cdSummand" else ob._cd_cross
            return _cdfn(f1, f2, evaluate(args[2], env), evaluate(args[3], env),
                         evaluate(args[4], env))
        if name == "LSeries.term":
            # Mathlib `LSeries.term f s n = if n = 0 then 0 else f n / n^s` — the Dirichlet-
            # series term of the DLMF 25.11 / §27.4 defining form Σ_{n≥1} f(n)·n^{−s}.
            # Higher-order head (like mellin/mathieuOp): the 1st argument is a FUNCTION
            # (`fun n => (μ n : ℂ)`), routed through _fn_callable, never scalar `evaluate`.
            # Math in ob._lseries_term (self-validated in oracle_bindings' anchors against
            # the DLMF 25.2.1 defining series ζ(s) = Σ n^{−s}, the 27.4.5 Möbius series
            # Σ μ(n)n^{−s} = 1/ζ(s), the n = 0 junk value, and the (f, s, n) arg order).
            if len(args) != 3:
                raise Unparseable("LSeries.term arity")
            g = _fn_callable(args[0], env)
            return ob._lseries_term(g, evaluate(args[1], env), evaluate(args[2], env))
        if name == "LSeries":
            # Mathlib `LSeries f s = ∑' n, LSeries.term f s n` — the DLMF 25.11 / §27.4
            # Dirichlet series Σ_{n≥1} f(n)·n^{−s} (term f s 0 = 0 is the Mathlib junk
            # value). Reached via the `L ↗f s` notation pre-normalization in parse().
            # Higher-order head (like LSeries.term/mathieuOp): the 1st argument is a
            # FUNCTION (a de-coerced `↗f` or a lambda), routed through _fn_callable,
            # never scalar `evaluate`. Math in ob._lseries (self-validated in
            # oracle_bindings' anchors against the DLMF 25.2.1 defining series
            # ζ(12)/ζ(12+3i) and the 27.4.5 Möbius series L μ = 1/ζ, all THROUGH the
            # binding), which sums the anchored ob._lseries_term under the same
            # settled-tail-or-raise discipline as _bounded_nsum but with NO extrapolation
            # (an erratic μ/Λ coefficient admits none): a sample point whose partial sums
            # cannot settle within the cap (small Re s — see SAMPLES_C_RE1) drops
            # honestly, never returning a half-converged truncation. No tolerance change.
            if len(args) != 2:
                raise Unparseable("LSeries arity")
            g = _fn_callable(args[0], env)
            return ob._lseries(g, evaluate(args[1], env))
        if name.split(".")[-1] == "gaussSum" and len(args) == 2:
            # `gaussSum` is OVERLOADED across FLMF: Mathlib's character Gauss sum
            # `gaussSum χ ψ = ∑ x, χ x * ψ x` (DLMF 27.10.9, GaussSumDirichlet.lean) takes
            # CHARACTER arguments (env-bound callables from the sampled MulChar/AddChar
            # binders), while the FLMF theta `gaussSum m n` (DLMF 20.11.1) takes NUMERIC
            # arguments. Dispatch on the evaluated argument kind: callables route to
            # ob._gauss_sum_char (anchored in oracle_bindings.verify() to G(1,(·|5)) = √5,
            # G(1,(·|7)) = i√7, |G(1,χ)|² = k, and the 27.10.10 separability), numbers keep
            # the registry `_gauss_sum` path bit-for-bit unchanged.
            a0, a1 = evaluate(args[0], env), evaluate(args[1], env)
            if callable(a0) or callable(a1):
                return ob._gauss_sum_char(a0, a1)
            return ob._gauss_sum(a0, a1)
        if name.split(".")[-1] == "wronskianD" and len(args) == 3:
            # `wronskianD f g x = f x * deriv g x - deriv f x * g x` — the deriv-slotted
            # Wronskian 𝒲{f,g} of §1.13(i) (FLMF Methods/Floquet.lean:139, transcribed from
            # that `def`, whose body IS this expression). Its first two arguments are
            # FUNCTIONS: routed through `_fn_callable` (scalar `evaluate` raises "node lam"
            # on the λ-operands of DLMF 31.9.3, dropping every point into a misleading
            # `unbound:wronskianD` skip), the point through the normal evaluator, and both
            # derivatives are mpmath finite differences exactly as the inline `deriv`
            # handler below takes them. ADDITIVE parse support only.
            f_ = _fn_callable(args[0], env)
            g_ = _fn_callable(args[1], env)
            x_ = evaluate(args[2], env)
            return f_(x_) * mp.diff(g_, x_) - mp.diff(f_, x_) * g_(x_)
        if name in ("logDeriv",):       # logDeriv f x = f'(x)/f(x) (e.g. logDeriv eta)
            if len(args) != 2:
                raise Unparseable("logDeriv arity")
            g = _callable(args[0], env)
            if g is None:
                raise Unparseable("logDeriv func unsupported")
            x = evaluate(args[1], env)
            return mp.diff(g, x) / g(x)
        if name == "deriv":              # inline derivative: deriv f x / deriv (deriv f) x
            if len(args) != 2:
                raise Unparseable("deriv arity")
            order, fnode = 1, args[0]
            # unwrap a nested `deriv (deriv f)` chain into ONE higher-order mp.diff — finite
            # differences of finite differences would compound the truncation error.
            while fnode[0] == "app" and fnode[1] == ("var", "deriv") and len(fnode[2]) == 1:
                order += 1
                fnode = fnode[2][0]
            # `deriv (iteratedDeriv m f)` = the (m+order)-th derivative — fold m into the order.
            if (fnode[0] == "app" and fnode[1] == ("var", "iteratedDeriv") and len(fnode[2]) == 2):
                order += int(evaluate(fnode[2][0], env))
                fnode = fnode[2][1]
            return mp.diff(_fn_callable(fnode, env), evaluate(args[1], env), order)
        if name == "iteratedDeriv":      # iteratedDeriv n f x = (d/dx)ⁿ f at x — order from AST
            if len(args) != 3:
                raise Unparseable("iteratedDeriv arity")
            order = int(evaluate(args[0], env))
            return mp.diff(_fn_callable(args[1], env), evaluate(args[2], env), order)
        if name == "starRingEnd" and len(args) == 2:
            # `(starRingEnd ℂ) z` / `(starRingEnd ℝ) x` — Mathlib's star ring endomorphism:
            # complex conjugation on ℂ and the identity on ℝ (the Gauss-sum magnitude
            # surface DLMF 27.8.6, `gaussSum χ e * (starRingEnd ℂ) (gaussSum χ e) = p`).
            # args[0] is the TYPE argument (ℂ/ℝ — never evaluated); mp.conj is exact
            # conjugation on mpc and the identity on mpf, matching both instances, so no
            # convention anchor is needed (there is no rival convention to reject).
            return mp.conj(evaluate(args[1], env))
        if name in ("Nat.card", "Fintype.card") and len(args) == 1:
            # Nat.card (DirichletCharacter ℂ k) — a TYPE-level cardinality: the number of
            # Dirichlet characters mod k (DLMF §27.8, text preceding 27.8.6). Counted by
            # ENUMERATING the character group (ob._dirichlet_char_count, the primitive-root
            # construction of _dirichlet_chars — CYCLIC (ℤ/kℤ)* only; anchored in
            # oracle_bindings.verify() against a brute-force homomorphism count). k = 0 or
            # non-cyclic modulus → that sample drops honestly; any OTHER type argument
            # falls through to the honest `unbound head Nat.card` skip — never fabricated.
            t, targs = args[0], []
            while t[0] == "app":               # flatten a curried (DirichletCharacter ℂ) k
                targs = t[2] + targs
                t = t[1]
            if t[0] == "var" and t[1].split(".")[-1] == "DirichletCharacter" and targs:
                n = ob._dirichlet_char_count(int(evaluate(targs[-1], env)))
                if n is None:
                    raise Unparseable("non-cyclic-modulus")
                return n
            # Fintype.card (ZMod k) / Nat.card (ZMod k) = k — the carrier size of ℤ/kℤ
            # (the RHS of DLMF 27.8.6 as stated in gaussSum_mul_conj_eq_card:
            # `… = Fintype.card (ZMod p)`). Faithful for BOTH heads: Mathlib's
            # `ZMod.card k = k` needs k ≥ 1 (ZMod 0 = ℤ has no Fintype instance, so a
            # Lean statement with this head cannot reach k = 0), and `Nat.card (ZMod 0)
            # = Nat.card ℤ = 0` — the k = 0 value is 0 for the Nat.card spelling and
            # unreachable for the Fintype.card one, so returning k is exact everywhere
            # the Lean expression exists.
            if t[0] == "var" and t[1].split(".")[-1] == "ZMod" and targs:
                kk = int(evaluate(targs[-1], env))
                if kk < 0:
                    raise Unparseable("ZMod negative modulus")
                return mp.mpf(kk)
        if "." in name:                  # `n.choose k` — Nat.choose written as a dotted method
            o, _, meth = name.partition(".")
            if o in env and meth == "choose" and len(args) == 1:
                return ob._choose(evaluate(("var", o), env), evaluate(args[0], env))
            # `m.descFactorial n` — Nat.descFactorial as a dotted method WITH an argument
            # (fallingFactorial_natCast, DLMF 26.8): m(m−1)⋯(m−n+1), exact integers.
            if o in env and meth == "descFactorial" and len(args) == 1:
                return _desc_factorial(evaluate(("var", o), env), evaluate(args[0], env))
        if name.split(".")[-1] == "cycle" and len(args) == 2 \
                and (_reg_get(name) or (None,))[0] == "fn":
            # unsigned Stirling-1 `cycle n k` (DLMF 26.8): the oracle binding's DP table is
            # sized by n alone, so a k > n query indexes out of range and crashes the sample
            # — but c(n,k) = 0 for k > n is EXACT (no permutation of n elements has more
            # than n cycles). Guard extractor-side (the binding file is owned by another
            # lane): return the exact 0 for k > n, delegate everything else unchanged.
            nv, kv = evaluate(args[0], env), evaluate(args[1], env)
            _ni, _ki = _near_int(nv), _near_int(kv)
            if _ni is not None and _ki is not None and _ki > _ni >= 0:
                return mp.mpf(0)
            return _reg_get(name)[1](nv, kv)
        _re = _reg_get(name)
        if _re is None:
            raise Unparseable(f"unbound head {name}")
        kind, fn = _re
        if kind == "const":
            return fn
        if kind == "fn":
            vals = [evaluate(a, env) for a in args]
            return fn(*vals)
        if kind == "psfn1":              # one-parameter power-series family (hermiteGF x):
            x = env.get(IND)             # its value is the anchored generating function,
            if x is None:                # evaluated at the sampled indeterminate
                raise Unparseable("psfn1 without indeterminate")
            if len(args) != 1:
                raise Unparseable("psfn1 arity")
            return fn(evaluate(args[0], env), x)
        if kind == "poly":               # T/U/hermite: head TYPE k  → P_k at indeterminate
            idx_arg = args[1] if len(args) >= 2 else args[0]   # args[0] is the scalar type
            kval = evaluate(idx_arg, env)
            x = env.get(IND)
            if x is None:
                raise Unparseable("poly without indeterminate")
            return fn(int(kval), x)
        if kind == "lpoly":              # laguerre α n: head PARAM DEGREE → P at indeterminate
            param, deg = evaluate(args[0], env), evaluate(args[1], env)
            x = env.get(IND)
            if x is None:
                raise Unparseable("lpoly without indeterminate")
            return fn(int(deg), param, x)
    raise Unparseable(f"node {k}")


def _fn_callable(fnode, env):
    """A function-position node (the operand of inline `deriv`) → a one-argument callable.
    Supports a lambda, a bare registry fn (`dawson`), and a PARTIAL application of a registry
    fn (`besselJ_nat n` ↦ λt. J(n,t)). Anything else is honestly unsupported."""
    if fnode[0] == "lam":
        return lambda t: evaluate(fnode[2], {**env, fnode[1]: t})
    if fnode[0] == "num" or (fnode[0] == "real" and fnode[1][0] == "num"):
        # constant function `(1 : ℝ → ℝ)` (the =O[atTop] 1 Mertens bounds, DLMF 27.11.10):
        # the function-type ascription drops to a bare numeral — a constant callable.
        cval = mp.mpf(fnode[1] if fnode[0] == "num" else fnode[1][1])
        return lambda t: cval
    if fnode[0] == "var":
        e = _reg_get(fnode[1])
        if e and e[0] == "fn":
            return e[1]
        # env-bound-lattice dotted method `L.weierstrassP` / `W.sigma` as a deriv/logDeriv
        # OPERAND (differential_equation_deriv's `deriv L.weierstrassP z`, DLMF 23.3.10):
        # delegate to the SAME _LDOT dispatch table the main evaluate() app branch already
        # uses for the fully-applied form, wrapped as a one-argument callable. ADDITIVE —
        # a non-lattice dotted name keeps the honest skip below.
        if "." in fnode[1]:
            o, _, m_ = fnode[1].partition(".")
            if isinstance(env.get(o), ob._Lattice) and m_ in _LDOT:
                Lo, fm = env[o], _LDOT[m_]
                return lambda t: fm(Lo, [t])
        raise Unparseable(f"deriv of {fnode[1]}")
    # curried `logDeriv f` / `deriv f` (ONE argument — not yet applied to a point) as a
    # deriv operand: `deriv (logDeriv W.sigma) z` (deriv_logDeriv_sigma, DLMF 23.2.6).
    # Mirrors the fully-applied `logDeriv f x = f'(x)/f(x)` branch of the main evaluator,
    # recursing through _fn_callable so the inner operand shares every case here
    # (including the lattice-dotted one just above).
    if fnode[0] == "app" and fnode[1] in (("var", "logDeriv"), ("var", "deriv")) \
            and len(fnode[2]) == 1:
        g_ = _fn_callable(fnode[2][0], env)
        if fnode[1][1] == "logDeriv":
            return lambda t: mp.diff(g_, t) / g_(t)
        return lambda t: mp.diff(g_, t)
    if fnode[0] == "app" and fnode[1][0] == "var":
        e = _reg_get(fnode[1][1])
        if e and e[0] == "fn":
            pre = [evaluate(a, env) for a in fnode[2]]
            return lambda t: e[1](*pre, t)
        if e and e[0] == "poly":          # (legendre n) ↦ λx. Pₙ(x) (index = last non-type arg)
            idx = fnode[2][1] if len(fnode[2]) >= 2 else fnode[2][0]
            kval = int(evaluate(idx, env))
            return lambda t: e[1](kval, t)
        if e and e[0] == "lpoly":         # (laguerre α n) ↦ λx. Lₙ^α(x)
            param, deg = evaluate(fnode[2][0], env), int(evaluate(fnode[2][1], env))
            return lambda t: e[1](deg, param, t)
    raise Unparseable("deriv func unsupported")


# weighted orthogonality measures: name -> (lo, hi, weight(x), quad-nodes). The Chebyshev
# weight 1/√(1−x²) on (−1,1) is endpoint-singular but integrable — mp.quad's tanh-sinh
# handles it given the endpoints as explicit nodes. (Mathlib `Polynomial.Chebyshev.measureT`.)
def _cheb_weight(x):
    return 1 / mp.sqrt(1 - x ** 2)


MEASURES = {
    "measureT":        (-1, 1, _cheb_weight, [-1, 1]),
    "chebyshevWeight": (-1, 1, _cheb_weight, [-1, 1]),
}


def _cond_true(cond, env):
    """Evaluate an `if` condition (an `=`/`≤`/`<`/`≥`/`>` relation node) to a bool. The
    `=` test uses a small tolerance so sampled equal indices (l = m) decide the branch."""
    if cond[0] == "expr":                    # a bare predicate (IsSquare n) parses as ("expr", …)
        cond = cond[1]
    if cond[0] == "condand":                 # c₁ ∧ c₂ (the 20.5.14 center-exclusion filter)
        return _cond_true(cond[1], env) and _cond_true(cond[2], env)
    if cond[0] == "eq":
        return abs(evaluate(cond[1], env) - evaluate(cond[2], env)) < mp.mpf("1e-9")
    if cond[0] == "ineq":
        op, a, b = cond[1], evaluate(cond[2], env), evaluate(cond[3], env)
        return {"≤": a <= b, "<": a < b, "≥": a >= b, ">": a > b}[op]
    if cond[0] == "app" and cond[1][0] == "var" and len(cond[2]) == 1:   # IsSquare/Even/Odd n
        nm, v = cond[1][1], int(evaluate(cond[2][0], env))
        if nm == "IsSquare":
            r = _math.isqrt(abs(v)); return r * r == v
        if nm == "Even":
            return v % 2 == 0
        if nm == "Odd":
            return v % 2 == 1
    raise Unparseable("ite condition")


_DERIV_HEADS = {("var", "deriv"), ("var", "derivative"), ("var", "Polynomial.derivative"),
                ("var", "logDeriv")}

# First-order differential operators of DLMF §15.5, transcribed VERBATIM from the private
# abbrevs in FLMF/Frameworks/Hypergeometric/Ch15DerivativesContiguous.lean:17-22 —
#   zDerivZ f             = fun z => z * deriv (fun w => w * f w) z
#   oneSubZDerivOneSubZ f = fun z => (1 - z) * deriv (fun w => (1 - w) * f w) z
# Each maps a callable f to the callable OP(f); Function.iterate `^[n]` composes n copies.
# Consumed by the ("iterop", …) app-node branch; anchored/validated numerically in
# docs/verification/ch15/probe_ops.py (identities hold to ~1e-41 at n=1..3).
_ITEROPS = {
    "zDerivZ":             lambda f: (lambda z: z * mp.diff(lambda w: w * f(w), z)),
    "oneSubZDerivOneSubZ": lambda f: (lambda z: (1 - z) * mp.diff(lambda w: (1 - w) * f(w), z)),
}


def _has_deriv(node):
    """True if the tree contains an inline `deriv` or formal-`derivative` application — its
    mp.diff evaluation carries finite-difference error, so the gate must widen to TOL_DERIV."""
    if isinstance(node, tuple):
        if node[0] == "app" and node[1][0] == "var" and node[1] in _DERIV_HEADS:
            return True
        return any(_has_deriv(c) for c in node[1:])
    if isinstance(node, list):
        return any(_has_deriv(c) for c in node)
    return False


def _is_const(nm):
    """A name bound in the registry as a constant (π, Complex.I, γ, …) — it is a value,
    not a free variable, so it must never be collected and sampled as a fresh real."""
    e = _reg_get(nm)
    return e is not None and e[0] == "const"


def _contains(node, kinds):
    """True if any sub-node has its head tag in `kinds` (e.g. a ∑/∑' anywhere in the tree)."""
    if isinstance(node, tuple):
        return node[0] in kinds or any(_contains(c, kinds) for c in node[1:])
    if isinstance(node, list):
        return any(_contains(c, kinds) for c in node)
    return False


def _has_cdot(node):
    """True if the tree contains the `·` cdot-section placeholder var `("var","·")`."""
    if isinstance(node, tuple):
        if node[0] == "var" and node[1] == "·":
            return True
        return any(_has_cdot(c) for c in node[1:])
    if isinstance(node, list):
        return any(_has_cdot(c) for c in node)
    return False


_LMETHODS = set(_LDOT) | {"zeta", "sigma", "smul"}   # lattice methods (suffix after `obj.`)


def _absfn_heads(node, acc):
    """Collect the VAR names in application-HEAD position anywhere in `node` (an abstract
    Finset-sum body): these are the ι-indexed function binders `c i`, `m i` (DLMF 18.18)
    that the generic app fallback of collect_free never frees. Registry heads swept in
    (C, laguerre) are harmless — sweep_eq drops them from sampling."""
    if isinstance(node, tuple):
        if node[0] == "app" and node[1][0] == "var":
            acc.add(node[1][1])
        for x in node[1:]:
            _absfn_heads(x, acc)
    elif isinstance(node, list):
        for x in node:
            _absfn_heads(x, acc)


def collect_free(node, acc, under_eval=False):
    k = node[0]
    # ── Weierstrass lattice forms: free the lattice symbol (L/W), never method names or the
    # smul proof `hlam` (M15) ──
    # A fully-qualified registry head (`ArithmeticFunction.sigma k n`) is a BOUND function,
    # not `<latticevar>.sigma` — exempt it from the lattice-method pattern below (a lattice
    # object is a bare binder like `L`/`W`, never a registry key).
    if k == "var" and "." in node[1] and node[1].partition(".")[2] in _LMETHODS \
            and _reg_resolve(node[1]) is None:
        acc.add(node[1].partition(".")[0]); return
    if k == "app" and node[1][0] == "var":
        hn = node[1][1]
        if hn == "℘[]":
            for a in node[2]:
                collect_free(a, acc, under_eval)
            return
        if "." in hn and hn.partition(".")[2] in _LMETHODS and _reg_resolve(hn) is None:
            acc.add(hn.partition(".")[0])
            if hn.partition(".")[2] != "smul":     # smul's arg is a proof `hlam`, not a value
                for a in node[2]:
                    collect_free(a, acc, under_eval)
            return
        if hn in _LARG:                            # discriminant L / (L.smul hlam)
            collect_free(node[2][0], acc, under_eval)
            return
        if hn in ("deriv", "logDeriv") and len(node[2]) == 2 \
                and node[2][0][0] == "var" and node[2][0][1].partition(".")[2] in _LMETHODS:
            acc.add(node[2][0][1].partition(".")[0])
            collect_free(node[2][1], acc, under_eval)
            return
    if k == "real":          # (e : ℝ)/(e : ℂ) cast — numerically transparent; free the operand
        collect_free(node[1], acc, under_eval); return
    if k == "zmodcast":      # (e : ZMod n) — frees the modulus n (when a var: it must be
        if not node[1].isdigit():          # sampled for the congruence gate) and the operand
            acc.add(node[1])
        collect_free(node[2], acc, under_eval); return
    if k == "princhar":      # (1 : DirichletCharacter ℂ k) — frees the modulus k (when a
        if not node[1].isdigit():          # var: the gcd formula needs the sampled k; the
            acc.add(node[1])               # head lives inside an "app" node whose generic
        return                             # fallback recurses only into ARGUMENTS)
    if k == "bool":          # a boolean '↔' side wrapper — free its numeric operands (and
        _bool_spec_free(node[1], acc, under_eval)     # the sqmod modulus) for sampling
        return
    if k == "var" and node[1] == "PowerSeries.X":          # the formal indeterminate
        acc.add(IND); return
    if k == "var" and node[1] not in ("π", "Real.pi") and not _is_const(node[1]):
        nm = node[1]
        if "." in nm and nm.rsplit(".", 1)[1] in ("1", "2"):  # pair projection ij.1/ij.2
            acc.add(nm.rsplit(".", 1)[0])                       # frees the pair var, not 'ij.1'
        else:
            sp = _dot_split(nm)            # n.factorial frees n, not 'n.factorial'
            acc.add(sp[0] if sp else nm)
    elif k in ("neg", "inv", "nearint"):       # nearint: nearest-integer projection — free
        collect_free(node[1], acc, under_eval)  # its operand (node[2] is the cast-type tag)
    elif k == "floor":                     # ⌊e⌋₊ / ⌊e⌋ — free the operand
        collect_free(node[2], acc, under_eval)
    elif k == "bin":
        collect_free(node[2], acc, under_eval); collect_free(node[3], acc, under_eval)
    elif k == "eval":                      # P.eval a — eval binds the indeterminate
        sub = set(); collect_free(node[1], sub, True); sub.discard(IND); acc |= sub
        collect_free(node[2], acc, under_eval)
    elif k in ("sum", "prod"):
        # a lattice-indexed tsum `∑' l : L.lattice, …` carries its lattice symbol only in
        # the index-type ANNOTATION (node[3]) — free it so the sweep samples L even when
        # no other atom of the conclusion mentions it (the L.g₂/℘ LHS usually does; this
        # is the belt-and-braces case). Additive: other index types are untouched.
        if len(node) > 3 and isinstance(node[3], str) and node[3].endswith(".lattice"):
            acc.add(node[3][: -len(".lattice")])
        sub = set(); collect_free(node[2], sub); sub.discard(node[1]); acc |= sub
    elif k in ("fsum", "fprod"):
        collect_free(node[2], acc, under_eval)       # lo bound
        collect_free(node[3], acc, under_eval)       # hi bound
        sub = set(); collect_free(node[4], sub); sub.discard(node[1]); acc |= sub
    elif k in ("fsumabs", "fprodabs"):               # ∑ i ∈ s, body — abstract Finset binder s
        acc.add(node[2])                             # the Finset binder s → sampled as |s| = N
        sub = set(); collect_free(node[3], sub, under_eval); sub.discard(node[1]); acc |= sub
        # the ι-indexed abstract function binders (c i, m i) sit in application-HEAD position,
        # which the generic app fallback never frees — free them explicitly so they are sampled
        # (as callables); the bound index var i is dropped, and registry heads (C, laguerre)
        # are filtered out of sampling later in sweep_eq exactly like any other bare-fn ref.
        heads = set(); _absfn_heads(node[3], heads)
        acc |= {h for h in heads if h != node[1]}
    elif k == "countset":                            # #{x ∈ lo..hi | pred} — frees the bounds
        collect_free(node[2], acc, under_eval)       # and the predicate minus the bound var
        collect_free(node[3], acc, under_eval)
        sub = set(); collect_free(node[4], sub); sub.discard(node[1]); acc |= sub
    elif k in ("fsumprimes", "fprodprimes"):         # ∑ p ∈ Nat.primesLE B, body — frees B
        collect_free(node[2], acc, under_eval)
        sub = set(); collect_free(node[3], sub); sub.discard(node[1]); acc |= sub
    elif k == "funiverase":                          # ∑ k ∈ Finset.univ.erase j, body
        collect_free(node[3], acc, under_eval)       # the ERASED index j (a sampled binder)
        sub = set(); collect_free(node[4], sub, under_eval); sub.discard(node[2]); acc |= sub
        heads = set(); _absfn_heads(node[4], heads)  # `γ k`, `a k` sit in HEAD position
        acc |= {h for h in heads if h != node[2] and _reg_resolve(h) is None}
    elif k == "funivfilter":                         # ∑ k ∈ univ.filter (fun k => P), body
        sub = set()
        collect_free(node[4], sub, under_eval)       # the predicate (frees its outer index)
        collect_free(node[5], sub, under_eval)       # the body
        sub -= {node[2], node[3]}                    # both spellings of the bound index
        acc |= sub
        heads = set(); _absfn_heads(node[5], heads)
        acc |= {h for h in heads if h not in (node[2], node[3]) and _reg_resolve(h) is None}
    elif k == "finpairs":                            # ∑ p ∈ univ.filter (p.1<p.2), body
        sub = set(); collect_free(node[4], sub, under_eval); sub.discard(node[3]); acc |= sub
        # applied-head abstract-fn binders (`a p.1` — DLMF 5.13.5's a : Fin 4 → ℝ) sit in
        # HEAD position, which the generic app fallback never frees — mirror fsumabs.
        heads = set(); _absfn_heads(node[4], heads)
        acc |= {h for h in heads if h != node[3] and _reg_resolve(h) is None}
    elif k == "condand":                             # conjunctive ite condition
        collect_free(node[1], acc, under_eval); collect_free(node[2], acc, under_eval)
    elif k in ("fsumset", "fprodset"):               # ∑ d ∈ n.divisors, body — frees n
        acc.add(node[2])
        sub = set(); collect_free(node[4], sub); sub.discard(node[3]); acc |= sub
    elif k == "pairagg":                              # ∑ ij ∈ antidiagonal n, body — frees n
        collect_free(node[3], acc, under_eval)        # base (the index n)
        sub = set(); collect_free(node[5], sub); sub.discard(node[4]); acc |= sub
    elif k == "dotm":
        if node[2] == "coeff":               # (P).coeff k — P is INDEXED, indeterminate bound away
            sub = set(); collect_free(node[1], sub, True); sub.discard(IND); acc |= sub
            for a in node[3]:
                collect_free(a, acc, under_eval)
        elif node[2] == "map":               # (P).map ringHom — the hom arg is not a sampleable
            collect_free(node[1], acc, under_eval)
        else:
            collect_free(node[1], acc, under_eval)
            for a in node[3]:
                collect_free(a, acc, under_eval)
    elif k == "iterderiv":                   # f^[n] P — n free; P differentiated w.r.t. IND (bound)
        collect_free(node[1], acc, under_eval)
        sub = set(); collect_free(node[2], sub, True); sub.discard(IND); acc |= sub
    elif k == "iterop":                      # (OP^[n]) — free the iterate count n; node[2] is the
        collect_free(node[1], acc, under_eval)  # operator NAME (never a sampled variable)
    elif k == "vec":                         # ![a, b, …] — free the entries
        for e in node[1]:
            collect_free(e[1] if e[0] == "expr" else e, acc, under_eval)
    elif k == "integral":
        for b in (node[2], node[3]):                 # lo, hi bounds
            if b not in (("inf",), ("neginf",)):
                collect_free(b, acc, under_eval)
        sub = set(); collect_free(node[4], sub); sub.discard(node[1]); acc |= sub
    elif k == "mintegral":                           # ∫ x, body ∂μ — frees body minus x
        sub = set(); collect_free(node[3], sub); sub.discard(node[1]); acc |= sub
    elif k == "ite":                                 # if cond then a else b
        for c in (node[1], node[2], node[3]):
            collect_free(c, acc, under_eval)
    elif k == "eq":                                  # relation inside an `if` condition
        collect_free(node[1], acc, under_eval); collect_free(node[2], acc, under_eval)
    elif k == "ineq":
        collect_free(node[2], acc, under_eval); collect_free(node[3], acc, under_eval)
    elif k == "lam":
        sub = set(); collect_free(node[2], sub, under_eval); sub.discard(node[1])
        for x in (node[3] if len(node) > 3 else ()):   # extra binders of a multi-binder
            sub.discard(x)                             # lambda (`fun p k => …`) are bound too
        acc |= sub
    elif k == "nhds":
        collect_free(node[2], acc, under_eval)
    elif k == "app":
        head = node[1]
        if head[0] == "lam":
            # β-redex head `(fun x => …) t` (from the ODE-predicate unfolding): the lambda
            # case above bounds its binder away; the argument(s) are free as usual. Without
            # this, free vars living ONLY inside the applied lambda body (the `n` of
            # `(fun x => Real.sin (n*x)) (−𝓍)`) would never be sampled.
            collect_free(head, acc, under_eval)
            for a in node[2]:
                collect_free(a, acc, under_eval)
        elif (head[0] == "var" and head[1].endswith(".factorization.prod")
                and _reg_resolve(head[1]) is None):
            # `n.factorization.prod fun p k => …` (Finsupp.prod over the prime
            # factorization, DLMF 27.3.2) — frees the base n; the lambda's own binders
            # p, k are bound by the "lam" case above.
            acc.add(head[1].split(".", 1)[0])
            for a in node[2]:
                collect_free(a, acc, under_eval)
        elif head[0] == "var" and head[1] in ("aeval", "Polynomial.aeval") and len(node[2]) == 2:
            collect_free(node[2][0], acc, under_eval)         # aeval x P — x free; P at x, IND bound
            sub = set(); collect_free(node[2][1], sub, True); sub.discard(IND); acc |= sub
        elif (head[0] == "var" and head[1] in ("indicator", "Set.indicator")
              and len(node[2]) == 2):                         # indicator (I a b) f
            setnode, inner = node[2]
            if setnode[0] == "app":
                for a in setnode[2]:
                    collect_free(a, acc, under_eval)
            collect_free(inner, acc, under_eval)
        elif head[0] == "var" and (_reg_get(head[1]) or (None,))[0] == "poly":
            # `T ℝ n` carries the scalar type in args[0]; `Polynomial.bernoulli n` does
            # not — mirror evaluate(): the index is args[1] if present, else args[0]
            for a in (node[2][1:] if len(node[2]) >= 2 else node[2]):
                collect_free(a, acc, under_eval)
            if not under_eval:             # a bare polynomial identity ⇒ indeterminate is free
                acc.add(IND)
        elif head[0] == "var" and (_reg_get(head[1]) or (None,))[0] == "lpoly":
            for a in node[2]:              # both the parameter and the degree are free vars
                collect_free(a, acc, under_eval)
            if not under_eval:
                acc.add(IND)
        elif head in (("var", "deriv"), ("var", "logDeriv")):
            # the operand of `deriv`/`logDeriv` is an OPERATOR position: a bare registry-fn
            # name there (`deriv dawson x`, `logDeriv eta z`) is the function differentiated,
            # not a free variable
            for a in node[2]:
                if a[0] == "var" and _reg_resolve(a[1]) is not None:
                    continue
                collect_free(a, acc, under_eval)
        elif head[0] == "princhar":
            # principal-character application `(1 : DirichletCharacter ℂ k) a` — the head
            # carries the modulus k (freed by the princhar case above); the residue
            # argument is free as usual.
            collect_free(head, acc, under_eval)
            for a in node[2]:
                collect_free(a, acc, under_eval)
        elif head[0] == "iterop":
            # `(OP^[n]) g pt` — the head carries the iterate count n (freed by the iterop case
            # above); the operand function g (a lambda: its binder w bound away, its parameters
            # a,b,c free) and the evaluation point pt are free as usual.
            collect_free(head, acc, under_eval)
            for a in node[2]:
                collect_free(a, acc, under_eval)
        else:
            for a in node[2]:
                if not (a[0] == "var" and a[1] in ("ℝ", "ℕ", "ℤ", "ℂ")):
                    collect_free(a, acc, under_eval)


def _is_zero_lit(node):
    """True if `node` is the literal constant 0 — for such a side, a `0 = …` check is the
    INTENDED test (confirming a vanishing/selection rule), not a hollow trivial-zero pass.
    See through a real/complex cast wrapper so `(0 : ℝ)` still counts as a literal zero."""
    if node[0] == "real":
        node = node[1]
    return node[0] == "num" and node[1] == 0


def _lattice_binders(free, binders):
    """Weierstrass file-level `variable (L : PeriodPair)` / `(W : WeierstrassZetaSigma L)` are
    not in the theorem's own binders, so a free `L`/`W` arrives unbound. Type them 'lattice'
    (sampled from `ob.SAMPLE_LATTICES`); `W` shares `L`'s lattice — coupled in the sweep loop."""
    if any(v in ("L", "W") for v in free):
        binders = {**binders}
        for v in ("L", "W"):
            # promote even when the extractor typed `(L : PeriodPair)` as the catch-all 'other'
            if v in free and binders.get(v) in (None, "other"):
                binders[v] = "lattice"
    return binders


def _f(*xs):
    return [mp.mpf(x) for x in xs]


# Instantiation-sampling of the abstract ι-indexed function binders of a Finset sum rule
# (DLMF 18.18 laguerre_sum_eval_zero): each entry is a deterministic pointwise callable
# j ↦ value applied at the sampled index. ABSFN_R samples a real coefficient c i; ABSFN_N
# samples a small natural degree m i ≤ 8 (the Laguerre order). The sum identity is termwise,
# so the concrete choices only need to be varied and in-range — the per-term content
# Lₙ^α(0) = (α+1)ₙ/n! is what the equality actually exercises.
ABSFN_R = [lambda j: mp.mpf(1) + mp.mpf("0.5") * int(j),
           lambda j: mp.cos(int(j) + mp.mpf("0.7")),
           lambda j: mp.mpf("-0.4") * (int(j) + 1)]
# POSITIVE pointwise callables for an absfnR binder carrying a `∀ k, 0 < a k` hypothesis
# ('_absfnpos', DLMF 5.13.5): varied, deterministic, strictly positive at every index.
ABSFN_R_POS = [lambda j: mp.mpf(1) + mp.mpf("0.5") * int(j),
               lambda j: mp.mpf("0.3") + mp.mpf("0.4") * ((3 * int(j) + 1) % 5),
               lambda j: mp.mpf("2.1") / (1 + int(j))]
ABSFN_N = [lambda j: mp.mpf(int(j) % 6),
           lambda j: mp.mpf((2 * int(j) + 1) % 8),
           lambda j: mp.mpf((int(j) + 2) % 7)]


SAMPLES = {"Z": _f(1, 2, 3, 5, 8), "N": _f(0, 1, 2, 3, 5),
           "R": _f("0.3", "1.7", "-0.8", "2.4"), IND: _f("0.4", "-0.7", "1.3", "2.1"),
           "C": [mp.mpc("0.5", "0.8"), mp.mpc("2.0", "-1.3"), mp.mpc("-0.7", "2.1"),
                 mp.mpc("1.4", "0.3")],
           "H": [mp.mpc(0, 1), mp.mpc("0.3", "1.1"), mp.mpc("0.5", "0.8"), mp.mpc("-0.2", "1.4")]}
# lower half-plane grid for a `z.im < 0` hypothesis ('imneg') — the conjugate of SAMPLES["H"].
# Without it the variable is unfenced and drawn over the full ℂ grid, including Im z > 0
# where a lower-sign continuation identity (DLMF 6.4.3–6.4.7 _of_im_neg) is off by 2πi —
# a fabricated FAIL on a numerically true statement.
SAMPLES_H_NEG = [p.conjugate() for p in SAMPLES["H"]]
# complex grid for a `Re s > 1` hypothesis (Dirichlet/ζ series convergence half-plane).
# Kept comfortably above 1 so a smooth ζ-type tail reaches full precision (near Re=1 the
# accelerated tail stalls at ~1e-7 and would FALSE-FAIL a true identity).
# The two large-σ points (ADDITIVE — sampling strictly inside the stated Re s > 1 domain,
# no tolerance change) cover Dirichlet series with ERRATIC coefficients (Σ μ(n)n^{−s},
# Σ Λ(n)n^{−s}, DLMF 27.4.5/27.4.12): μ/Λ carry no smooth tail, so no extrapolator
# accelerates them and at σ ≤ 3.5 the partial sums cannot settle within the 4000-term
# cap (tail ~ N^{1−σ}). At σ = 8.5 the |term| ≤ n^{−σ}·ln n window settles by n ≈ 1400
# with truncation ≲ 1e-24 ≪ TOL — the row is then genuinely exercised instead of
# skipping as undersampled.
SAMPLES_C_RE1 = [mp.mpc("1.7", "0.4"), mp.mpc("2.3", "-0.9"), mp.mpc("2.9", "0.3"),
                 mp.mpc("3.5", "-1.2"), mp.mpc("8.5", "0.7"), mp.mpc("11.5", "-1.3")]
# Distinct complex grids for hypotheses weaker than `Re s > 1`.  In particular,
# a `0 < s.re` theorem must actually be exercised in the critical strip; reusing
# SAMPLES_C_RE1 silently checked a strict subset of its domain.  The exact real
# point s = 1 is included because it is an interior point of `Re s > 0`; a theorem
# carrying `s ≠ 1` drops it through the existing `distinct` constraint filter.
SAMPLES_C_REPOS = [mp.mpc("0.2", "0.4"), mp.mpc("0.55", "-0.8"),
                   mp.mpc("0.9", "0.25"), mp.mpc(1, 0),
                   mp.mpc("1.4", "-0.6"), mp.mpc("2.3", "0.7")]
SAMPLES_C_REGE1 = [mp.mpc(1, 0), mp.mpc(1, "0.6"), mp.mpc("1.7", "-0.4"),
                   mp.mpc("2.5", "0.9")]
# Whole-plane grid for a complex nonzero hypothesis.  It spans both half-planes
# and includes s = 1 so removable-value branches are checked explicitly; s = 0
# itself is omitted by construction.
SAMPLES_C_NONZERO = [mp.mpc("-2.4", "0.35"), mp.mpc("-0.8", "-1.1"),
                     mp.mpc("0.35", "0.7"), mp.mpc(1, 0),
                     mp.mpc("1.6", "-0.5"), mp.mpc("2.4", "1.2")]
# interior of the unit disk ‖z‖ < 1 (the convergence region of a power series ∑ aₖ zᵏ, e.g. the
# digamma Taylor series §5.7.4). Kept away from the boundary so the tail reaches full precision.
SAMPLES_C_DISK = [mp.mpc("0.3", "0.2"), mp.mpc("-0.45", "0.35"), mp.mpc("0.5", "-0.6"),
                  mp.mpc("-0.2", "-0.7")]
# purely IMAGINARY grid for a `v.re = 0` hypothesis ('imaxis', DLMF 20.11.5's rectangular
# lattice τ = i·t). Every point also has Im > 0, so it stays inside a coexisting upper-half-
# plane hypothesis — sampling restricted to (a subset of) the stated domain.
SAMPLES_C_IMAXIS = [mp.mpc(0, "0.6"), mp.mpc(0, 1), mp.mpc(0, "1.7"), mp.mpc(0, "2.5")]


def _re_upper_grid(c):
    """Curated ℂ grid strictly inside a `z.re < c` half-plane strip (DLMF 15.8.22/23's
    Re z < 1/2 validity region for the √-argument quadratic transformations). Real parts are
    capped safely below c and imaginary parts are spread and nonzero, so every point also clears
    the [1,∞) slit for both z and the transformed argument. The per-sample 'reupper' filter is the
    soundness guarantee; this only supplies in-strip points the default ℂ grid (almost all
    Re ≥ 1/2) misses. ADDITIVE — sampling restricted to the stated hypothesis only."""
    top = c - mp.mpf("0.15")
    base = [(mp.mpf("-0.2"), mp.mpf("0.5")), (mp.mpf("-0.7"), mp.mpf("0.8")),
            (mp.mpf("0.25"), mp.mpf("-0.6")), (mp.mpf("-0.5"), mp.mpf("-0.9")),
            (mp.mpf("0.15"), mp.mpf("1.0")), (mp.mpf("-1.0"), mp.mpf("-0.35"))]
    return [mp.mpc(min(re, top), im) for re, im in base]
# small-modulus complex grid for a `‖f(z)‖ < 1` disc on a TRIG expression (DLMF 15.4.8–16):
# every point lies WELL inside both |tan z| < 1 (≤ 0.68) and |sin z| < 1 (≤ 0.57), and has
# sin z ≠ 0, cos z ≠ 0, so it satisfies the whole hypothesis set of those rows. The default
# ℂ grid lands OUTSIDE these discs (|sin z| ≥ 1.009 at every default point), which is what
# left the identities scored on their branch-crossing region; sampling here keeps every
# point inside the stated Gauss-series disc. Redundant with the `normexpr` filter (which is
# the soundness guarantee), but it EXERCISES the row instead of leaving it undersampled.
# complex grid for the ARGUMENT of a local-Heun sum (`heunFn`/`heunF0`/`heunF1`/
# `heunTheta`, DLMF 31.3.1) on a row that states NO disc hypothesis (the definitional
# displays 31.9.3/31.9.4). `Hℓ(a,q;…;z)` is the sum of its Maclaurin series, so it is
# meaningful only on `|z| < min(1,|a|)`, and the companion `f₁` of 31.9.4 evaluates
# `Hℓ(1−a,…;1−z)`, needing `|1−z| < min(1,|1−a|)` at the SAME sample. Every point below
# sits in the lens `|z| < 0.65 ∧ |1−z| < 0.66`, inside both discs for every point of the
# default ℂ grid of `a` (whose minimum `min(1,|a|)` is 0.94 and minimum `min(1,|1−a|)` is
# 0.5 — the 0.5 case simply drops in-loop). The default ℂ grid has a single point of
# modulus < 1 (0.5+0.8i, |·| = 0.9434), and when `a` draws that same point the disc test
# `|z| < |a|` is an equality, so EVERY combo dropped and 31.9.4 starved into
# `undersampled/domain`. Sampling is OUR choice on an unconstrained binder: this is a
# subdomain of the row's stated (unrestricted) domain — PASS evidence there, never a
# fabricated verdict outside it, and the oracle's own out-of-disc guard still drops any
# point whose series does not converge.
SAMPLES_HEUN_DISK = [mp.mpc("0.5", "0.25"), mp.mpc("0.45", "-0.3"), mp.mpc("0.6", "0.1"),
                     mp.mpc("0.35", "0.05")]
SAMPLES_TRIG_DISK = [mp.mpc("0.3", "0.1"), mp.mpc("-0.4", "0.2"), mp.mpc("0.5", "-0.15"),
                     mp.mpc("0.2", "-0.3")]
# constraint-restricted grids keep sampling inside the stated hypothesis domain
SAMPLES_R = {"pos": _f("0.3", "0.9", "1.7", "2.4"), "nonneg": _f(0, "0.3", "1.7", "2.4"),
             "nonzero": _f("0.3", "1.7", "-0.8", "2.4"), "gt1": _f("1.3", "1.7", "2.4", "3.1"),
             "ge1": _f(1, "1.7", "2.4"), "neg": _f("-0.3", "-0.9", "-1.7", "-2.4"),
             "unit": _f("-0.9", "-0.4", "0.3", "0.8"),    # |x| ≤ 1 hypothesis
             "absge1": _f("1.3", "1.7", "-1.3", "2.4"),    # |x| ≥ 1 hypothesis (x² ≥ 1)
             "gtNegHalf": _f("-0.4", "0.3", "1.3", "2.4"),  # ν > −1/2 hypothesis
             "gehalf": _f("0.5", "0.9", "1.7", "2.4")}      # ν ≥ 1/2 hypothesis
SAMPLES_INT = {"pos": _f(1, 2, 3, 5, 8), "gt1": _f(2, 3, 5, 8), "ge1": _f(1, 2, 3, 5),
               "nonneg": _f(0, 1, 2, 3, 5), "nonzero": _f(1, 2, 3, 5, 8),
               "prime": _f(2, 3, 5, 7, 11), "odd": _f(1, 3, 5, 7, 9)}


def _real_grid(flag):
    """Sample grid for a real variable given its hypothesis flag. A `('icc', a, b)` flag
    (a membership `x ∈ Icc/Ioo a b`) samples four points strictly inside [a,b] — so e.g.
    the Bernoulli-Fourier theorems fenced to [0,1] are not sampled at x=1.7. Named flags
    fall through to the SAMPLES_R table; an unconstrained var gets the default ℝ grid."""
    if isinstance(flag, tuple) and flag and flag[0] == "icc":
        a, b = flag[1], flag[2]
        return [a + (b - a) * mp.mpf(t) for t in ("0.1", "0.35", "0.65", "0.9")]
    if isinstance(flag, tuple) and flag and flag[0] == "runion":
        # disjunctive window (a, b) ∪ (c, ∞) — see the `(a < x ∧ x < b) ∨ c < x` scan in
        # _binders (DLMF 5.18.8): sample strictly inside BOTH branches of the disjunction.
        a, b, c = flag[1], flag[2], flag[3]
        return ([a + (b - a) * mp.mpf(t) for t in ("0.25", "0.55", "0.85")]
                + [c + mp.mpf("0.5"), c + mp.mpf("1.3")])
    if flag == "roothyp":
        # implicit root hypothesis `f(…) v = 0` (see the constraint scan): no grid can
        # honor the equation, so return NO points — the row drops to an honest
        # undersampled skip instead of scoring freely-sampled non-roots (the
        # abs_lt_one_of_legendre_zero fabricated FAIL).
        return []
    return SAMPLES_R.get(flag, SAMPLES["R"])


def _int_grid(flag, base):
    """Sample grid for a ℤ/ℕ variable given its hypothesis flag. An ('enum', vals) flag
    (a disjunctive hypothesis `m = 2 ∨ m = 3 ∨ m = 4`) samples EXACTLY that value set —
    the theorem says nothing outside it (e.g. the combinedTheta junk-index branch).
    Named flags fall through to SAMPLES_INT; an unconstrained var gets the default grid."""
    if isinstance(flag, tuple) and flag and flag[0] == "enum":
        return _f(*flag[1])
    # ('mod', c, r): residue hypothesis `v % c = r` — sample the residue class r, r+c, r+2c, …
    # (e.g. m ∈ {1, 5, 9, 13, 17} for `m % 4 = 1`, Jacobi reciprocity DLMF 27.9.3).
    if isinstance(flag, tuple) and flag and flag[0] == "mod":
        c, r = int(flag[1]), int(flag[2])
        return _f(*(r + c * k for k in range(5)))
    return SAMPLES_INT.get(flag, SAMPLES[base])


def _flag_holds(flag, x):
    """Does the sample point `x` satisfy domain `flag`?  UNKNOWN flags (and points whose
    shape the predicate cannot judge) answer True — this is a secondary filter layered on
    top of the grid the PRIMARY flag already shaped, so it may only ever REMOVE points a
    stated hypothesis excludes, never invent an opinion it does not have."""
    try:
        re_, im_ = mp.re(x), mp.im(x)
        real = re_ if im_ == 0 else None          # order flags judge REAL points only
        if isinstance(flag, tuple) and flag:
            if flag[0] == "icc":
                return real is None or (flag[1] <= real <= flag[2])
            if flag[0] == "cdisk":
                return abs(x) <= flag[1]
            if flag[0] == "enum":
                return real is None or int(real) in tuple(flag[1])
            if flag[0] == "mod":
                return real is None or int(real) % int(flag[1]) == int(flag[2])
            return True                            # runion / trigdisk / latdisk: not judged here
        if flag == "nonzero":
            return abs(x) > 0
        if flag == "unit":
            return abs(x) <= 1                     # `‖x‖ < 1` and `‖x‖ ≤ 1` share this flag
        if flag == "absge1":
            return abs(x) >= 1
        if flag == "imaxis":
            return re_ == 0
        if flag == "impos":
            return im_ > 0
        if flag == "imnonneg":
            return im_ >= 0
        if flag == "imneg":
            return im_ < 0
        if flag == "roothyp":
            return False                           # no grid point can witness `f(…) x = 0`
        if real is None:
            return True
        if flag == "pos":
            return real > 0
        if flag == "nonneg":
            return real >= 0
        if flag == "neg":
            return real < 0
        if flag == "gt1":
            return real > 1
        if flag == "ge1":
            return real >= 1
        if flag == "gehalf":
            return real >= mp.mpf("0.5")
        if flag == "gtNegHalf":
            return real > mp.mpf("-0.5")
        if flag == "odd":
            return real == int(real) and int(real) % 2 == 1
        if flag == "prime":
            n = int(real)
            return real == n and n >= 2 and all(n % k for k in range(2, int(n ** 0.5) + 1))
    except (TypeError, ValueError, ArithmeticError):
        return True
    return True


def _filter_extra_flags(v, grid, constraints):
    """Enforce the flags of a MULTI-hypothesis variable that `cons[v]` could not carry.

    `_binders`/`_add_flag` record every domain flag parsed for `v` in `cons['_flags'][v]`
    (only when there are ≥2 of them); `cons[v]` keeps the grid-shaping one. Everything
    else in that list is applied here as a pointwise filter, so a variable binding both
    `z ≠ 0` and `‖z‖ < 1` (hypergeometric_15_4_1) is sampled inside the CONJUNCTION
    rather than inside whichever hypothesis the regex loop happened to parse last.
    An empty result is returned as-is: no grid point satisfies the stated hypotheses, so
    the row must starve into an honest undersampled skip, never be scored out of domain.

    The PRIMARY flag is re-tested too (it costs nothing — every flag-shaped grid satisfies
    its own flag by construction) so that a caller whose grid branch does not implement
    that flag at all (e.g. `_grid`, which has no `unit` branch) still samples in-domain."""
    flags = (constraints or {}).get('_flags', {}).get(v)
    if not flags:
        return grid
    out = []
    for p in grid:
        if p is None or callable(p):               # placeholder / callable sample: not judged
            out.append(p)
        elif all(_flag_holds(f, p) for f in flags):
            out.append(p)
    return out


def _filter_domain_pairs(grids, binders, constraints):
    """Apply each SINGLE-VARIABLE norm/wedge domain hypothesis (`normlow` c ≤ ‖f(v)‖,
    `normexpr` ‖f(v)‖ < r, `argwedge` |ph(f(v))| < θ) to that variable's OWN grid, before
    the cartesian product is capped.

    These predicates are already the per-sample soundness filter (`_pairs_ok`), so removing
    the points they reject is semantically a NO-OP — it only happens EARLIER. That matters
    because the 24-combo cap windows a wide product at its LAST few variables: with seven ℂ
    binders (the DLMF 31.3 local-Heun rows) the leading variable is pinned at its first grid
    value for the first 4096 combos, so if that one value violates the row's own hypothesis
    (`1 ≤ ‖a‖`, whose default ℂ grid leads with a = 0.5+0.8i, ‖a‖ = 0.94) EVERY combo in the
    window is dropped in-loop and the row starves into `undersampled/domain` although the
    hypothesis domain is plainly non-empty on the same grid.

    Strictly a RESTRICTION of sampling to the stated hypothesis (never a new sample value, no
    tolerance/gate/scoring change); `_pairs_ok` still runs per sample. Fires only for a
    predicate whose free variables are exactly one directly-sampled scalar (ℂ/ℍ/ℝ) binder —
    multi-variable discs impose no single-variable grid (cf. `_domain_reject_grid`) and
    callable/character/lattice binders are resolved per sample, not on the grid. A filter that
    would EMPTY a grid is discarded (the row then starves exactly as it does today)."""
    preds = {}
    for p in (constraints or {}).get('_pairs', []):
        if p[0] not in ('normlow', 'normexpr', 'argwedge'):
            continue
        try:
            ast = P(tokenize(p[1])).expr()
            fv = set(); collect_free(ast, fv)
        except Exception:
            continue
        fv = {x for x in fv if x in (binders or {})}
        if len(fv) != 1:
            continue
        v = fv.pop()
        if binders.get(v) not in ("C", "H", "R"):
            continue
        preds.setdefault(v, []).append((p[0], ast, p[2], p[3]))
    if not preds:
        return grids
    out = []
    for v, g in grids:
        ps = preds.get(v)
        if not ps:
            out.append((v, g))
            continue
        kept = []
        for pt in g:
            if pt is None or callable(pt):        # placeholder/callable sample — not judged here
                kept.append(pt)
                continue
            ok = True
            for kind, ast, c, strict in ps:
                try:
                    val = evaluate(ast, {v: pt})
                except Exception:
                    ok = False                    # cannot certify the hypothesis — drop the point
                    break
                m = abs(mp.arg(val)) if kind == 'argwedge' else abs(val)
                if kind == 'normlow':
                    if (strict and not (m > c)) or (not strict and not (m >= c)):
                        ok = False
                        break
                elif (strict and not (m < c)) or (not strict and not (m <= c)):
                    ok = False
                    break
            if ok:
                kept.append(pt)
        out.append((v, kept if kept else g))      # empty ⇒ keep the old grid (honest starvation)
    return out


def _filter_int_bounds(v, grid, constraints):
    """Restrict an INTEGER (ℕ/ℤ) grid to any parsed `_lower`/`_upper` bound on `v`, so a
    shape flag (odd/prime/…) composes with a coexisting order hypothesis on the SAME
    variable (e.g. `h_odd : Odd n` ∧ `hlt : 1 < n`, DLMF 24.2 odd-Bernoulli vanishing) —
    without this, the grid built from the shape flag alone samples values the order
    hypothesis excludes (n=1 is odd but not > 1). Unlike `_filter_lower`/`_filter_upper`
    (real grids), this NEVER refills with fractional points on underflow — an integer
    grid must stay integral (and, if the flag was e.g. `odd`, odd); if filtering leaves
    no points the original grid is kept as-is rather than fabricating a value outside
    the shape constraint."""
    cons = constraints or {}
    out = list(grid)
    lb = cons.get('_lower', {}).get(v)
    if lb is not None:
        bound, strict = lb
        kept = [p for p in out if (p > bound if strict else p >= bound)]
        if kept:
            out = kept
    ub = cons.get('_upper', {}).get(v)
    if ub is not None:
        bound, strict = ub
        kept = [p for p in out if (p < bound if strict else p <= bound)]
        if kept:
            out = kept
    return out


def _filter_upper(v, grid, constraints):
    """Restrict a real grid to a parsed upper bound `v < c` / `v ≤ c` (from `_upper`),
    so a var with both a lower flag and an upper bound (e.g. `0 < s` ∧ `s < 1`) samples
    inside (0,1). If filtering leaves < 2 points, supplement with interior fractions of c."""
    ub = (constraints or {}).get('_upper', {}).get(v)
    if ub is None:
        return grid
    bound, strict = ub
    keep = [p for p in grid if (p < bound if strict else p <= bound)]
    if len(keep) < 2:                      # e.g. an unconstrained grid wiped out — refill inside (0,c)
        keep += [bound * mp.mpf(t) for t in ("0.2", "0.5", "0.8")]
        keep = [p for p in keep if (p < bound if strict else p <= bound)]
    return keep


def _filter_lower(v, grid, constraints):
    """Restrict a real grid to a parsed lower bound `c < v` / `c ≤ v` (from `_lower`, e.g. the
    irrational `-(√2/2) < x` of erf_7_8_4), so the variable is sampled only inside the stated
    domain. If filtering leaves < 2 points, supplement with points just ABOVE the bound."""
    lb = (constraints or {}).get('_lower', {}).get(v)
    if lb is None:
        return grid
    bound, strict = lb
    keep = [p for p in grid if (p > bound if strict else p >= bound)]
    if len(keep) < 2:                      # refill just above the bound (bound + {0.1, 0.5, 1.2, 2})
        keep += [bound + mp.mpf(t) for t in ("0.1", "0.5", "1.2", "2.0")]
        keep = [p for p in keep if (p > bound if strict else p >= bound)]
    return keep


def _domain_reject_grid(v, constraints, binders):
    """Curated in-domain complex grid for a ℂ variable constrained by domain hypotheses the
    default ℂ grid misses: a lower-norm `c < ‖v‖`, a principal-argument wedge `|arg(f v)| < θ`,
    or a complex-centered disk `‖g(v)‖ < r`. Rejection-samples a dense candidate lattice against
    the SAME parsed hypotheses that _pairs_ok honors per sample, returning up to 6 spread points
    strictly inside the stated domain (else None → the default grid is kept). ADDITIVE: sampling
    is restricted to the stated hypotheses only — no tolerance/gate/scoring change, and every
    returned point still runs the full per-sample filter chain. Only predicates in the SINGLE
    variable v are used (a multi-variable disc imposes no single-variable grid)."""
    preds = []
    for p in (constraints or {}).get('_pairs', []):
        if p[0] not in ('normlow', 'argwedge', 'normexpr'):
            continue
        expr_s = p[1]
        try:
            ast = P(tokenize(expr_s)).expr()
            fv = set(); collect_free(ast, fv)
        except Exception:
            continue
        if {x for x in fv if x in (binders or {})} != {v}:
            continue                              # references another sampled var → not a v-grid
        preds.append((p[0], ast, p[2], p[3]))
    if not preds:
        return None

    def _ok(cand):
        env = {v: cand}
        for kind, ast, c, strict in preds:
            try:
                val = evaluate(ast, env)
            except Exception:
                return False
            m = abs(mp.arg(val)) if kind == 'argwedge' else abs(val)
            if kind == 'normlow':
                if (strict and not (m > c)) or (not strict and not (m >= c)):
                    return False
            else:                                 # argwedge / normexpr — upper bound
                if (strict and not (m < c)) or (not strict and not (m <= c)):
                    return False
        return True

    # SAFETY: only override the default grid when it is genuinely STARVED (< 2 default ℂ
    # points satisfy the stated domain). If the default grid already exercises the domain,
    # keep it untouched — this makes the curated grid strictly a rescue for otherwise-
    # undersampled rows, never a silent grid change for a row the default already covers.
    if sum(1 for c in SAMPLES["C"] if _ok(c)) >= 2:
        return None

    survivors, step = [], 0.35
    xr = -4.0
    while xr <= 4.0 + 1e-9:
        yi = -3.0
        while yi <= 3.0 + 1e-9:
            cand = mp.mpc(xr, yi)
            if _ok(cand):
                survivors.append(cand)
            yi += step
        xr += step
    if not survivors:
        return None
    stride = max(1, len(survivors) // 6)          # spread evenly across the in-domain set
    return survivors[::stride][:6]


def _pairs_ok(env, constraints):
    """Honor pairwise hypotheses (Coprime …): a sample point violating one is OUT of
    the stated domain — checking the claim there would fabricate a counterexample."""
    for p in (constraints or {}).get('_pairs', []):
        kind = p[0]
        if kind == 'isunit':                         # ha : IsUnit a, a : ZMod k — a invertible mod k
            a = p[1]
            knm = (constraints or {}).get('_zmodmod', {}).get(a)
            if a in env and knm is not None and knm in env:
                try:
                    if _math.gcd(int(env[a]) % int(env[knm]), int(env[knm])) != 1:
                        return False
                except (ValueError, TypeError, OverflowError):
                    return False
            continue
        if kind == 'notunit':                        # ha : ¬ IsUnit a — a NOT invertible mod k
            a = p[1]                                 # (DLMF 27.8.4's "(n,k) > 1")
            knm = (constraints or {}).get('_zmodmod', {}).get(a)
            if a in env:
                if knm is None or knm not in env:
                    return False                     # modulus unknown: cannot certify ¬IsUnit —
                try:                                 # drop the sample (conservative, never scored)
                    if _math.gcd(int(env[a]) % int(env[knm]), int(env[knm])) == 1:
                        return False
                except (ValueError, TypeError, OverflowError):
                    return False
            continue
        if kind == 'sumlt':                          # triangle-violation hypothesis a+b<c
            a, b, c = p[1], p[2], p[3]
            if a in env and b in env and c in env and not (env[a] + env[b] < env[c]):
                return False
            continue
        if kind == 'complex_l1_lt':                  # |Re z| + |Im z| < ℓ
            z, ell = p[1], p[2]
            if z in env and ell in env:
                try:
                    if not (abs(mp.re(env[z])) + abs(mp.im(env[z])) < mp.re(env[ell])):
                        return False
                except (TypeError, ValueError):
                    return False
            continue
        if kind == 'compleximstrip':                 # |Im z| < Im τ / d
            z, tau, denom = p[1], p[2], p[3]
            if z in env and tau in env:
                try:
                    inside = abs(mp.im(env[z])) < mp.im(env[tau]) / denom
                except (TypeError, ValueError, ZeroDivisionError):
                    return False
                if not inside:
                    return False
            continue
        if kind == 'ltpluspair':                     # affine real hypothesis v < w + k / v ≤ w + k
            a, b, k, strict = p[1], p[2], p[3], p[4]
            if a in env and b in env:
                try:
                    lhs, rhs = mp.re(env[a]), mp.re(env[b]) + k
                except (TypeError, ValueError):
                    return False
                if (strict and not (lhs < rhs)) or (not strict and not (lhs <= rhs)):
                    return False
            continue
        if kind == 'normdisk':                       # off-center disk hypothesis ‖v − k‖ < r
            v, ctr, rad, strict = p[1], p[2], p[3], p[4]
            if v in env:
                try:
                    d = abs(env[v] - ctr)
                except (TypeError, ValueError):
                    return False
                if (strict and not (d < rad)) or (not strict and not (d <= rad)):
                    return False
            continue
        if kind == 'reexprpos':                       # 0 < Re f(vars) (DLMF 15.4.20's
            expr_s, strict = p[1], p[2]                # `0 < (c − a − b).re` convergence
            try:                                       # hypothesis at z = 1)
                r = mp.re(evaluate(P(tokenize(expr_s)).expr(), env))
            except Exception:
                return False                          # cannot certify 0 < Re f — drop
            if (strict and not (r > 0)) or (not strict and not (r >= 0)):
                return False
            continue
        if kind == 'absrelt':                         # |v.re| < c strip (DLMF 15.4.14/16's
            v, bexpr, strict = p[1], p[2], p[3]        # |Re z| < π/2 principal-extension domain)
            if v in env:
                try:
                    b = mp.re(evaluate(P(tokenize(bexpr)).expr(), env))
                    d = abs(mp.re(env[v]))
                except Exception:
                    return False                      # cannot certify |Re v| < c — drop
                if (strict and not (d < b)) or (not strict and not (d <= b)):
                    return False
            continue
        if kind == 'normexpr':                        # ‖f(v)‖ < r disc on a trig EXPRESSION
            expr_s, rad, strict = p[1], p[2], p[3]     # (DLMF 15.4.8/10 ‖-(tan z)²‖<1 etc.)
            try:
                d = abs(evaluate(P(tokenize(expr_s)).expr(), env))
            except Exception:
                return False                          # cannot certify ‖f(v)‖ < r — drop
            if (strict and not (d < rad)) or (not strict and not (d <= rad)):
                return False
            continue
        if kind == 'normexprmin':                     # ‖E‖ < min(c, ‖F‖) — composed local-
            expr_s, c, oth_s, strict = p[1], p[2], p[3], p[4]   # expansion disc (DLMF 31.3.13
            try:                                      # ‖z/(z−1)‖ < min 1 ‖a/(a−1)‖)
                d = abs(evaluate(P(tokenize(expr_s)).expr(), env))
                r = min(c, abs(evaluate(P(tokenize(oth_s)).expr(), env)))
            except Exception:
                return False                          # cannot certify the disc — drop
            if (strict and not (d < r)) or (not strict and not (d <= r)):
                return False
            continue
        if kind == 'normlow':                         # c < ‖f(v)‖ LOWER-norm (DLMF 15.8.32 1<‖z‖)
            expr_s, c, strict = p[1], p[2], p[3]       # OUTSIDE it the cpow prefactor branch-crosses
            try:
                d = abs(evaluate(P(tokenize(expr_s)).expr(), env))
            except Exception:
                return False                          # cannot certify c < ‖f(v)‖ — drop
            if (strict and not (d > c)) or (not strict and not (d >= c)):
                return False
            continue
        if kind == 'argwedge':                        # |arg(f(v))| < θ principal-arg wedge
            expr_s, c, strict = p[1], p[2], p[3]       # (DLMF 15.8.32 |ph(−z)| < π/3)
            try:
                d = abs(mp.arg(evaluate(P(tokenize(expr_s)).expr(), env)))
            except Exception:
                return False                          # cannot certify |arg(f(v))| < θ — drop
            if (strict and not (d < c)) or (not strict and not (d <= c)):
                return False
            continue
        if kind == 'samesign':                       # 0 ∉ uIcc a b — bounds same sign, ≠0
            a, b = p[1], p[2]
            if a in env and b in env and not (env[a] * env[b] > 0):
                return False
            continue
        if kind == 'ge_diff':                         # c ≤ v₁ − v₂ (e.g. 1 ≤ b − a)
            a, b, c = p[1], p[2], p[3]
            if a in env and b in env and not (mp.re(env[a]) - mp.re(env[b]) >= c):
                return False
            continue
        if kind == 'reupper':                         # z.re < c real-part strip (DLMF 15.8.22/23)
            v, c, strict = p[1], p[2], p[3]           # Re z < 1/2 validity half-plane
            if v in env:
                try:
                    r = mp.re(env[v])
                except (TypeError, ValueError):
                    return False
                if (strict and not (r < c)) or (not strict and not (r <= c)):
                    return False
            continue
        if kind == 'relin':                           # Re(Σ cᵥ·v) </> 0 (DLMF 15.4.23 regime)
            coeffs, op = p[1], p[2]
            if all(v in env for v in coeffs):
                try:
                    s = sum((coeffs[v] * mp.re(env[v]) for v in coeffs), mp.mpf(0))
                except (TypeError, ValueError):
                    return False
                if (op == 'lt' and not (s < 0)) or (op == 'gt' and not (s > 0)):
                    return False
            continue
        if kind == 'sumgt':                           # c < v₁+v₂+…+vₙ (e.g. 3 < a+b+c+d)
            terms, c = p[1], p[2]
            if all(t in env for t in terms) and not (sum((mp.re(env[t]) for t in terms), mp.mpf(0)) > c):
                return False
            continue
        if kind in ('dvd', 'notdvd'):                # h : a ∣ b / ¬ a ∣ b (divisibility)
            def _dvres(t):                           # token → exact int (env var or literal)
                if t in env:
                    v = env[t]
                    iv = int(v)
                    if iv != v:
                        raise ValueError(f"dvd filter: {t}={v} not an integer")
                    return iv
                return int(t)                        # integer literal (regex-guaranteed)
            try:
                a, b = _dvres(p[1]), _dvres(p[2])
                divides = (b == 0) if a == 0 else (b % a == 0)
            except (ValueError, TypeError, OverflowError, KeyError):
                return False                         # cannot certify the hypothesis — drop
            if (kind == 'dvd') != divides:
                return False
            continue
        if kind in ('sumnonzero', 'sumzero'):        # 3j magnetic selection rule a+b+c (≠)= 0
            a, b, c = p[1], p[2], p[3]
            if a in env and b in env and c in env:
                s0 = env[a] + env[b] + env[c]
                if (kind == 'sumnonzero' and s0 == 0) or (kind == 'sumzero' and s0 != 0):
                    return False
            continue
        if kind in ('lepairoff', 'ltpairoff'):       # affine ℕ-hypothesis a + k ≤ b / a + k < b
            a, k, b = p[1], p[2], p[3]               # (e.g. Krawtchouk `hN : n + 2 ≤ N`,
            if a in env and b in env:                # DLMF 18.22.3) — a sample violating it is
                try:                                 # OUTSIDE the stated hypothesis, never scored
                    lhs, rhs = mp.re(env[a]) + k, mp.re(env[b])
                except (TypeError, ValueError):
                    return False
                if (kind == 'lepairoff' and not (lhs <= rhs)) or \
                   (kind == 'ltpairoff' and not (lhs < rhs)):
                    return False
            continue
        if kind == 'distinct':
            # h : a ≠ b — an operand absent from env may be an integer LITERAL (the
            # `ha : a ≠ 1` of DLMF 27.8.6's zero case); resolve it so the hypothesis
            # actually filters, instead of being silently skipped. For a ZMod binder the
            # Lean `≠` is inequality IN ℤ/kℤ, so the sampled ℤ-lifts violate it exactly
            # when (va − vb) ≡ 0 (mod k) — compare via the recorded '_zmodmod' modulus.
            # Additive: a filter that only DROPS out-of-hypothesis samples, never scores.
            def _dires(t):
                if t in env:                  # non-numeric operands (a sampled character
                    v = env[t]                # callable, whose χ ≠ 1 is filtered at sample
                    return v if isinstance(v, (int, float, mp.mpf, mp.mpc)) else None
                return mp.mpf(int(t)) if re.fullmatch(r'-?\d+', t) else None
            va, vb = _dires(p[1]), _dires(p[2])
            if va is None or vb is None:
                continue
            knm = (constraints or {}).get('_zmodmod', {}).get(p[1]) \
                or (constraints or {}).get('_zmodmod', {}).get(p[2])
            if knm is not None and knm in env:
                try:
                    if (int(va) - int(vb)) % int(env[knm]) == 0:
                        return False
                except (ValueError, TypeError, OverflowError):
                    return False              # cannot certify the hypothesis — drop
                continue
            if va == vb:
                return False
            continue
        if kind == 'arghigh':                        # one-sided principal-arg bound v.arg ≤ θ
            v, c, strict = p[1], p[2], p[3]           # (DLMF 11.2.2 arg z ≤ π/2 — the lower −π
            if v in env:                              # side is automatic for the principal arg)
                try:
                    d = mp.arg(env[v])
                except (TypeError, ValueError):
                    return False                     # cannot certify the hypothesis — drop
                if (strict and not (d < c)) or (not strict and not (d <= c)):
                    return False
            continue
        if kind == 'argsumpv':                       # x.arg + y.arg ∈ (−π, π] (DLMF 4.8.2's
            x, y = p[1], p[2]                         # principal-value window for log(xy))
            if x in env and y in env:
                try:
                    s0 = mp.arg(env[x]) + mp.arg(env[y])
                except (TypeError, ValueError):
                    return False                     # cannot certify the hypothesis — drop
                if not (-mp.pi < s0 <= mp.pi):
                    return False
            continue
        if kind in ('triangle', 'nottriangle'):      # |a−b| ≤ c ∧ c ≤ a+b (DLMF 34.2.1), or ¬(…)
            a, b, c = p[1], p[2], p[3]
            if a in env and b in env and c in env:
                try:
                    tri = abs(env[a] - env[b]) <= env[c] <= env[a] + env[b]
                except (TypeError, ValueError):
                    return False                     # cannot certify the hypothesis — drop
                if (kind == 'triangle') != bool(tri):
                    return False
            continue
        if kind == 'absle':                          # |m| ≤ j, VARIABLE bound (DLMF §34.2 window)
            a, b = p[1], p[2]
            if a in env and b in env:
                try:
                    if not (abs(env[a]) <= mp.re(env[b])):
                        return False
                except (TypeError, ValueError):
                    return False                     # cannot certify the hypothesis — drop
            continue
        a, b = p[1], p[2]
        if a not in env or b not in env:
            continue
        if kind == 'coprime':
            try:
                if _math.gcd(int(env[a]), int(env[b])) != 1:
                    return False
            except (ValueError, TypeError, OverflowError):
                return False
        elif kind == 'evenprod':                     # hypothesis Even (a * b) — mn must be even
            try:
                if (int(env[a]) * int(env[b])) % 2 != 0:
                    return False
            except (ValueError, TypeError, OverflowError):
                return False
        elif kind == 'lepair' and not (env[a] <= env[b]):   # hypothesis a ≤ b
            return False
        elif kind == 'ltpair' and not (mp.re(env[a]) < mp.re(env[b])):   # hypothesis a < b
            return False
    return True


_NONZERO_EPS = mp.mpf("1e-25")   # numeric-zero threshold for hypothesized-nonzero exprs
_NONZERO_AST = {}                # parse cache: '_nonzero' constraint string → AST (or None)


def _nonzero_ok(env, constraints):
    """Honor nonvanishing hypotheses `h : f(…) ≠ 0` recorded under '_nonzero': a sample
    point where a hypothesized-nonzero expression evaluates to numerical zero is OUTSIDE
    the theorem's stated domain, so checking there compares 0/0 cancellation noise, not
    the identity. Concrete case (theta_20_7_34): the C×H diagonal z = τ = 0.5+0.8i puts
    z = -1/2 + (τ+1/2) on the zero lattice of θ₂(·, τ+1/2) — |θ₂| ≈ 6.4e-41 at 40 dps —
    and both quotient conjuncts are pure noise (rel-gap 0.56/0.29 vs ≤ 2.5e-31 on the
    other 15 grid points); the theorem's `h₂ : θ₂ z (τ + 1/2) ≠ 0` excludes exactly this
    point. ADDITIVE and fail-safe: an expression that fails to parse or evaluate imposes
    NO filter (behavior unchanged), and dropping a point can never fabricate a PASS — the
    row must still clear the UNCHANGED tolerance on ≥ 2 in-domain samples, else it skips
    honestly as undersampled."""
    for s in (constraints or {}).get('_nonzero', []):
        if s not in _NONZERO_AST:
            try:
                ast = parse(s)
                _NONZERO_AST[s] = ast[1] if ast and ast[0] == "expr" else ast
            except Exception:
                _NONZERO_AST[s] = None
        node = _NONZERO_AST[s]
        if node is None:
            continue
        try:
            fv = set()
            collect_free(node, fv)
            if any(v != IND and v not in env and _reg_resolve(v) is None for v in fv):
                continue                   # mentions an unsampled name — cannot filter here
            if abs(evaluate(node, env)) < _NONZERO_EPS:
                return False               # hypothesized-nonzero expr vanished — out of domain
        except Exception:
            continue                       # hypothesis not evaluable here — no filter
    return True


# ── angular-momentum structured sampling (M16, Agent D) ──────────────────────
# Generic positive-integer grids never satisfy the Wigner selection rules (m₁+m₂+m₃=0,
# |mᵢ|≤jᵢ, triangle), so the 3j/CG rows skip as trivial-zero. Sample instead from CURATED,
# sympy-verified valid configurations (a mix of non-zero + a few that vanish, so the `=0`
# selection-rule rows are also exercised). Physical 6-tuple order: (j₁,j₂,j₃,m₁,m₂,m₃).
_3J_TUPLES = [(1, 1, 2, 0, 0, 0), (2, 1, 1, 1, -1, 0), (1, 1, 0, 0, 0, 0), (2, 2, 2, 1, -1, 0),
              (2, 2, 2, 2, -2, 0), (1, 1, 2, 1, -1, 0), (2, 1, 1, 0, 0, 0),
              (1, 1, 3, 0, 0, 0), (1, 1, 4, 0, 0, 0), (2, 1, 4, 0, 0, 0),   # triangle violated → 0
              (1, 1, 1, 1, 0, 0), (1, 1, 2, 1, 1, 0), (2, 2, 2, 1, 1, 0),   # m-sum ≠ 0 → 0
              (2, 1, 1, 1, 1, 0)]
_6J_TUPLES = [(1, 1, 1, 1, 1, 1), (2, 2, 2, 2, 2, 2), (1, 1, 2, 1, 1, 2), (2, 1, 1, 1, 2, 2),
              (1, 2, 1, 2, 1, 2),
              (1, 1, 3, 1, 1, 1), (1, 1, 4, 1, 1, 1), (2, 1, 4, 2, 1, 1)]   # last 3: triad violated → 0
# per-head: arg-position of each physical quantity [j₁,j₂,j₃,m₁,m₂,m₃] (3j-class)
# or the 6 independent 6j entries.
_3J_ARGMAP = {"wigner3j": [0, 1, 2, 3, 4, 5], "clebschGordan": [0, 2, 4, 1, 3, 5]}


def _angmom_apps(node, acc):
    if isinstance(node, tuple):
        if node[0] == "app" and node[1][0] == "var" and node[1][1] in \
                ("wigner3j", "clebschGordan", "wigner6j", "racahW"):
            acc.append((node[1][1], node[2]))
        for c in node[1:]:
            _angmom_apps(c, acc)
    elif isinstance(node, list):
        for c in node:
            _angmom_apps(c, acc)


def _angmom_envs(L, R, free):
    """If the conclusion contains a Wigner/CG/Racah head whose argument slots are bare vars,
    negated vars, or integer literals, return a list of joint sample envs drawn from the
    curated valid tuples (each env assigns every free var). Returns None if not applicable —
    then sweep_eq falls back to the generic grid (no perturbation of non-angular-momentum rows)."""
    apps = []
    _angmom_apps(L, apps); _angmom_apps(R, apps)
    if not apps:
        return None
    for head, args in apps:
        if len(args) != 6:
            continue
        tuples = _6J_TUPLES if head in ("wigner6j", "racahW") else _3J_TUPLES
        argmap = (_3J_ARGMAP.get(head) if head in _3J_ARGMAP else [0, 1, 2, 3, 4, 5])
        envs = []
        for t in tuples:
            env, ok = {}, True
            for phys_k, val in enumerate(t):
                slot = args[argmap[phys_k]]
                if slot[0] == "var":
                    env[slot[1]] = mp.mpf(val)
                elif slot[0] == "neg" and slot[1][0] == "var":
                    env[slot[1][1]] = mp.mpf(-val)
                elif slot[0] == "num":
                    if slot[1] != val:
                        ok = False; break
                else:
                    ok = False; break
            if ok and all(v in env for v in free):
                envs.append(env)
        if envs:
            return envs
    return None


def _tonat_negative(node, env):
    """True if some `(expr).toNat` in the tree has expr < 0 at this env — the FLMF `.toNat`
    phase-clamp bug (docs/ERRATA wigner3j-tonat-phase). Such points are DEFERRED (not scored),
    so a rfl-true theorem built on the buggy def is never FAILed, while the bug stays logged."""
    if isinstance(node, tuple):
        if node[0] == "dotm" and node[2] == "toNat":
            try:
                if evaluate(node[1], env) < 0:
                    return True
            except Exception:
                pass
        return any(_tonat_negative(c, env) for c in node[1:])
    if isinstance(node, list):
        return any(_tonat_negative(c, env) for c in node)
    return False


def _natsub_negative(node, env):
    """True if a `^`-EXPONENT subtraction `a − b`, shaped exactly like a Lean ℕ term
    (integer literals, ℕ-typed binder vars, and +,−,*,^,/ thereof — NO unary neg, ℕ has
    none, and NO casts) — i.e. Lean `Nat.sub`, which TRUNCATES (`2*n − 1 = 0` at n = 0) —
    evaluates negative at this env.  The evaluator's `-` is true subtraction, so scoring
    such a point compares e.g. q^{−1} against Lean's q^0: a semantics mis-model, not a
    refutation (jtpFactor_eq, DLMF 20.5.3, proven by `rfl`, false-FAILed at rel 0.79 on
    the n = 0 grid point).  Such points are DEFERRED (not scored) — the same additive
    contract as the `.toNat` guard above: the row must still clear the gate on the
    remaining substantive samples, so a genuine disagreement still FAILs there.
    Why skip rather than model the clamp: the parser eats `↑` coercions transparently
    (a zpow exponent `2*↑n − 1` over ℤ parses identically to the ℕ `2*n − 1`), so
    committing to EITHER semantics blind could mis-score some rows in BOTH directions;
    dropping the boundary point is the only choice that can never fabricate a PASS or a
    FAIL.  Scope guards (each excludes a verified PASS row that a wider net regressed):
      • exponent-only — `ζ(1 − 2·↑n)` (riemannZeta_one_sub_two_mul_nat) is ℂ subtraction
        in ARGUMENT position, and the `∑ k ∈ range K` parse carries an internal `K − 1`
        bound the finite-sum evaluator already handles (gamma_5_11_10/11);
      • no-neg shape — `z ^ (−(n : ℤ) − 1)` (polygamma_5_15_5) is a zpow whose genuinely
        negative exponent the evaluator models correctly."""
    natvars = {v for v, t in env.get("_binders", {}).items() if t == "N"}
    if not natvars:
        return False

    def nat_shaped(nd):
        k = nd[0]
        if k == "num":
            return float(nd[1]).is_integer()
        if k == "var":
            return nd[1] in natvars
        if k == "bin" and nd[1] in ("+", "-", "*", "^", "/"):
            return nat_shaped(nd[2]) and nat_shaped(nd[3])
        return False                       # neg, real-cast, app, … — not a ℕ term shape

    def walk(nd, inexp):
        if isinstance(nd, tuple):
            if nd[0] == "bin" and nd[1] == "^":
                return walk(nd[2], inexp) or walk(nd[3], True)
            if (inexp and nd[0] == "bin" and nd[1] == "-"
                    and nat_shaped(nd[2]) and nat_shaped(nd[3])
                    and (_has_intvar(nd[2], natvars) or _has_intvar(nd[3], natvars))):
                try:
                    if evaluate(nd[2], env) < evaluate(nd[3], env):
                        return True
                except Exception:
                    pass
            return any(walk(c, inexp) for c in nd[1:])
        if isinstance(nd, list):
            return any(walk(c, inexp) for c in nd)
        return False

    return walk(node, False)


class _EvalTimeout(Exception):
    """One sample exceeded its wall-clock budget — the row is too costly to verify numerically
    (e.g. a doubly-nested quadrature), so it SKIPS honestly. A timeout is a classification,
    never a FAIL."""


_TIMEOUT_OK = hasattr(signal, "SIGALRM")
EVAL_BUDGET = 8.0       # seconds per sample before an honest "eval-timeout" skip. Headroom for a
                        # Richardson-accelerated expensive-summand tail (Σψ′(n+1)/n, §5.16.2: the
                        # plain-term warm-up + accel lands near 3s) — raising the cap only converts
                        # a timeout-skip into a decided verdict, it can never cause a false PASS/FAIL.


def _contains_head(node, names):
    """True when the AST `node` references (as a var / application head) any name whose
    LEAF segment is in `names`, anywhere in the tree. Generic tuple/list walker."""
    if isinstance(node, list):
        return any(_contains_head(x, names) for x in node)
    if not isinstance(node, tuple):
        return False
    if node[0] == "var" and isinstance(node[1], str):
        return node[1].split(".")[-1] in names
    return any(_contains_head(x, names) for x in node[1:])


# Registry heads that are THEMSELVES defined by a single adaptive mp.quad (their Lean
# defs are iterated-integral recursions): an OUTER ∫ or deriv over one of these is a
# doubly-nested quadrature — every outer node/finite-difference point triggers a full
# inner adaptive quadrature, blowing the default 8 s per-sample budget (measured:
# ∫ₓ^∞ bickleyKi(1,t) dt stalls past 30 s; ∫ₓ^∞ iRepErfc(1,t) dt = 9.93 s — both
# CORRECT values, pure cost). No analytic shortcut is admissible for the CHECK: a
# Fubini collapse recovers the head's own defining integral (LHS == LHS, circular).
_QUADDEF_HEADS = {"bickleyKi", "iRepErfc"}

# Heads whose value depends on the FRACTIONAL PART of the integration variable — piecewise-
# analytic with kinks at the integers (see the integer-breakpoint split in evaluate's
# finite-interval integral branch).
_FRACT_HEADS = {"periodicBernoulli", "periodicBernoulli₁", "fract", "Int.fract"}

# The Legendre elliptic-integral family — rows containing these heads sample an
# unconstrained real modulus `k` inside the principal window |k| < 1 (see sweep_eq).
_ELLIPTIC_HEADS = {"ellipticF", "ellipticE", "ellipticPi",
                   "ellipticIntegrand", "ellipticEIntegrand", "ellipticPiIntegrand"}

# Local-Heun heads whose value is the SUM of the Maclaurin series 31.3.1 (oracle
# `_heun_fn`), together with the ARITY at which their last argument is the series
# ARGUMENT z: heunFn a q α β γ δ z, heunF0/heunF1 a α β γ δ q z (DLMF 31.9.4),
# heunTheta a α β γ δ ε q ζ (DLMF 31.9.3).
_HEUN_SUM_HEADS = {"heunFn": 7, "heunF0": 7, "heunF1": 7, "heunTheta": 8}


def _heun_arg_vars(node, acc):
    """Collect the BARE variables occupying the series-argument slot of a local-Heun
    application (`heunFn … z`, `heunF1 … z`, `heunTheta … ζ`). Used only to choose a
    sampling window for such a variable — never to alter scoring."""
    if isinstance(node, list):
        for x in node:
            _heun_arg_vars(x, acc)
        return
    if not isinstance(node, tuple):
        return
    if node[0] == "app" and isinstance(node[1], tuple) and node[1][0] == "var" \
            and isinstance(node[1][1], str):
        ar = _HEUN_SUM_HEADS.get(node[1][1].split(".")[-1])
        if ar is not None and len(node[2]) == ar and node[2][-1][0] == "var":
            acc.add(node[2][-1][1])
    for x in node[1:]:
        _heun_arg_vars(x, acc)


def _nested_quad_shape(node):
    """The doubly-nested-quadrature row shape: an `integral` node — or an inline
    `deriv`/`logDeriv` operand — whose body applies a quad-defined registry head
    (`_QUADDEF_HEADS`). Used to grant a SHAPE-SCOPED per-sample budget raise plus a
    thinned sample grid in sweep_eq (bickleyKi_succ_eq / deriv_bickleyKi_succ /
    iRepErfc_succ_eq, DLMF 10.43 / 7.18.2). Budget only — tolerances unchanged."""
    if isinstance(node, list):
        return any(_nested_quad_shape(x) for x in node)
    if not isinstance(node, tuple):
        return False
    if node[0] == "integral" and _contains_head(node[4], _QUADDEF_HEADS):
        return True
    if (node[0] == "app" and node[1] in (("var", "deriv"), ("var", "logDeriv"))
            and node[2] and _contains_head(node[2][0], _QUADDEF_HEADS)):
        return True
    return any(_nested_quad_shape(x) for x in node[1:])


_NESTED_QUAD_BUDGET = 60.0   # seconds per sample for the certified nested-quad shape
                             # (≤ 3 samples × 60 s stays under the 240 s harness cap)

# Registry heads that are individually EXPENSIVE per evaluation (an analytic-continuation
# ₂F₁ / Olver bold-F: mp.hyp2f1 sums hundreds of terms at generic complex parameters). An
# `∫` whose integrand APPLIES one of these evaluates the head at every quadrature node, so a
# single valid-but-costly sample (measured: a 0..1 Euler integral with an in-integrand
# `principalOlver` at a large-imaginary-part sample, endpoint-singular Re d < 1, ~10 s) trips
# the default 8 s per-sample budget and aborts the WHOLE row on the FIRST such sample. These
# are NOT the doubly-nested quadrature of `_QUADDEF_HEADS` (principalOlver is a SERIES head,
# not a quad) — but they qualify for the same SHAPE-SCOPED budget raise + thinned grid. The
# DLMF 15.6.8/15.6.9 Euler integrals are exactly this shape.
_EXPENSIVE_INTEGRAND_HEADS = {"principalOlver", "principalGauss", "olverHypergeometric",
                              "principalOlverBoundaryAbove", "principalOlverBoundaryBelow"}


def _expensive_integrand_shape(node):
    """An `integral` whose body applies an `_EXPENSIVE_INTEGRAND_HEADS` head — the
    single-quad-over-an-expensive-series shape (DLMF 15.6.8/9). Grants the same per-sample
    budget raise + thinned grid as `_nested_quad_shape`; budget/sample-set only, no tolerance
    or scoring change."""
    if isinstance(node, list):
        return any(_expensive_integrand_shape(x) for x in node)
    if not isinstance(node, tuple):
        return False
    if node[0] == "integral" and _contains_head(node[4], _EXPENSIVE_INTEGRAND_HEADS):
        return True
    return any(_expensive_integrand_shape(x) for x in node[1:])


# n-fold iterated first-order differential operator `(OP^[n]) g pt` (the `iterop` AST head,
# DLMF 15.5.3/5/7/8): each Function.iterate step wraps the operand in ANOTHER numerical
# mp.diff (see _ITEROPS), so the per-sample cost grows ~10× per order — measured
# (docs/verification/ch15/probe_ops.py, dps 40): n=3 → 0.09 s, n=4 → 1.1 s, n=5 → 11.5 s.
# The default ℕ grid SAMPLES["N"] = {0,1,2,3,5} therefore blows the 8 s per-sample budget
# on its n=5 point and aborts the WHOLE row as a false `eval-timeout` skip, even though the
# identity is TRUE (probe_ops.py: rel ≤ 1e-31 at dps 30 on n=1,2,3, well under the exact
# 1e-18 gate). Cap the sampled operator order at _ITEROP_MAX_ORDER: n ∈ {0,1,2,3} still
# fully exercises the nested operator (n≥1 is non-trivial — n=0 alone would be tautological)
# and each point costs < 0.1 s. Sample-set only; tolerances, gates and settle windows are
# unchanged, and no other row shape is touched.
_ITEROP_MAX_ORDER = 3

# How far the trivial-zero RETRY (sweep_eq's `_diversify` window) may reach into the cartesian
# product when it strides for 24 combos. Bounded so the retry costs a bounded generator walk on
# a huge product; 8000 tuples span the whole product of a 6–7 binder row at 4–5 grid points per
# binder, which is exactly the shape whose lexicographic prefix pins the leading variables.
_DIVERSIFY_POOL = 8000


def _iterop_shape(node):
    """True when the conclusion contains an `iterop` head — an n-fold Function.iterate of a
    first-order differential operator (`zDerivZ`/`oneSubZDerivOneSubZ`, DLMF 15.5.3/5/7/8).
    Drives the operator-order cap in sweep_eq (see _ITEROP_MAX_ORDER)."""
    if isinstance(node, list):
        return any(_iterop_shape(x) for x in node)
    if not isinstance(node, tuple):
        return False
    if node[0] == "iterop":
        return True
    return any(_iterop_shape(x) for x in node[1:])


# Registry coefficient heads whose defining recurrence is itself O(k) work per NEW term
# (cCoeff, DLMF 6.10.3: c_k = −Σ_{j<k} c_j/(k−j)) — a naive tsum pre-loop over them is
# O(K²) (measured: 35.2 s just to build cCoeff up to the 4000-term cap), and a
# polynomially-convergent tail (expint_6_10_1's ~k^{−(x+1)}) can NEVER settle to the
# 1e-25 window by direct summation anyway. Cap the naive pre-loop at 300 terms so the
# row falls promptly to `_accelerated_nsum`'s Richardson/Euler–Maclaurin machinery
# (built for exactly this smooth power-law-tail regime, residual-gated); if the
# accelerator cannot certify, the point still drops honestly. Term cap only — the
# settle window, residual gates and tolerances are unchanged.
_COSTLY_RECURRENCE_HEADS = {"cCoeff"}


def _alarm(signum, frame):
    raise _EvalTimeout()


@contextlib.contextmanager
def _time_limit(secs):
    if not _TIMEOUT_OK or secs <= 0:
        yield
        return
    old = signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, secs)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)


def _func_eq(L, R):
    """Function-extensionality equality `f = g` (both sides are ℝ→… with no explicit argument,
    e.g. `iRepErfc 0 = erfc`): eta-expand — sample a point x and compare f(x), g(x). Functions
    whose domain rejects every REAL sample (modular forms on ℍ — the slash-action rows, where
    η raises off the upper half-plane) fall back to the upper-half-plane grid; the fallback
    fires ONLY when the real grid decided nothing (< 2 points), so it can turn a skip into a
    decided verdict but never changes a real-grid verdict (additive). Returns
    (verdict, detail) or None if either side isn't a unary callable."""
    gL, gR = _callable(L, {}), _callable(R, {})
    if gL is None or gR is None:
        return None
    for grid in (SAMPLES["R"] + SAMPLES_R["pos"], SAMPLES["H"]):
        worst, ok = mp.mpf(0), 0
        for x in grid:
            try:
                with _time_limit(EVAL_BUDGET):
                    a, b = gL(x), gR(x)
            except Exception:
                continue
            ok += 1
            worst = max(worst, abs(a - b) / max(mp.mpf(1), abs(a), abs(b)))
        if ok >= 2:
            return (("PASS" if worst < TOL_DERIV else "FAIL"),
                    f"funeq worst={mp.nstr(worst, 4)} over {ok}pts")
    return None


def _uses_indeterminate(node):
    """True if `node` contains a polynomial head used AS a polynomial (a poly/lpoly registry
    head or `monomial`/`X`) that needs the indeterminate — but NOT inside an `eval`/`aeval`/
    `coeff`/`iterderiv`, which bind the indeterminate themselves. Drives bare-poly-equality
    indeterminate sampling."""
    if isinstance(node, tuple):
        if node[0] in ("eval", "iterderiv"):
            return False
        if node[0] == "dotm" and node[2] in ("coeff", "derivative"):
            return False
        if node[0] == "app" and node[1][0] == "var":
            nm = node[1][1]
            if nm in ("aeval", "Polynomial.aeval"):     # rebinds X ↦ its first arg; self-contained
                return False
            if nm == "PowerSeries.coeff":  # prefix coeff m S — binds the indeterminate
                return False               # itself (mirrors the dotm "coeff" case above)
            if nm in ("monomial", "PowerSeries.exp", "PowerSeries.mk", "PowerSeries.rescale"):
                return True
            e = _reg_get(nm)
            if e and e[0] in ("poly", "lpoly", "psfn", "psfn1"):
                return True
        if node[0] == "var" and node[1] == IND:
            return True
        return any(_uses_indeterminate(c) for c in node[1:])
    if isinstance(node, list):
        return any(_uses_indeterminate(c) for c in node)
    return False


def _subst_fn_witness(node, wmap):
    """Rename ∀-quantified function VARIABLES to their registered concrete-witness heads
    (constraints['_fnwitness'], recorded by _binders from a hypothesis binder such as
    `hf : IsCompletelyMultiplicative f` ↦ {f: 'liouville'}). A pure name substitution on
    the AST — the witness satisfies every recorded hypothesis (anchored in ob.verify()),
    so checking the conclusion at the witness is sound as a refutation oracle: a numeric
    counterexample disproves the ∀-statement; passing is evidence.

    A 'head@v' spec (the confluent Christoffel–Darboux `D` of `IsConfluentCDSystem
    p h D x` ↦ {D: 'cdChebD@x'}, whose witness value depends on the row's own point
    variable v) rewrites the APPLICATION `D n` to `head n v` — the extra trailing
    argument is the bound variable v, sampled from its own grid. A bare (un-applied)
    occurrence of such a variable is deliberately NOT renamed, so it keeps its honest
    `unbound` skip rather than evaluating with a missing argument.

    A 'smoothfn:i' spec (a plain ∀-quantified smooth binder `w : ℝ → ℝ` recorded by
    `_smooth_deriv_witness` — DLMF 30.2.1 deriv_oneSubSq_mul_deriv) splices the i-th
    canonical everywhere-smooth transcendental witness LAMBDA (`_smooth_wit_ast`) in
    place of the variable, so `deriv w y` / `deriv (deriv w) z` reach the existing
    lambda-operand nested-deriv mp.diff path unchanged."""
    if isinstance(node, tuple):
        if (node[0] == "var" and isinstance(node[1], str)
                and isinstance(wmap.get(node[1]), str)
                and wmap[node[1]].startswith("smoothfn:")):
            return _smooth_wit_ast(int(wmap[node[1]].split(":", 1)[1]))
        # An 'entirefn:i' spec (a hypothesis-free `W : ℂ → ℂ` binder applied only at points,
        # recorded by `_free_fn_witness`) splices the i-th canonical ENTIRE witness lambda
        # (`_entire_wit_ast`), so `W ξ` reaches the existing β-reduction path in `evaluate`.
        if (node[0] == "var" and isinstance(node[1], str)
                and isinstance(wmap.get(node[1]), str)
                and wmap[node[1]].startswith("entirefn:")):
            return _entire_wit_ast(int(wmap[node[1]].split(":", 1)[1]))
        if (node[0] == "app" and isinstance(node[1], tuple) and node[1][0] == "var"
                and isinstance(wmap.get(node[1][1]), str) and "@" in wmap[node[1][1]]):
            head, *xvs = wmap[node[1][1]].split("@")
            # thread the row's own parameter variable(s) as trailing argument(s): the
            # single `cdChebD@x` case appends one; the N1 `ratioCoeffG@a@b` /
            # `symRatioCoeffH@a@b` witnesses append the sampled real pair (a, b).
            return ("app", ("var", head),
                    [_subst_fn_witness(c, wmap) for c in node[2]] + [("var", v) for v in xvs])
        if (node[0] == "var" and isinstance(node[1], str) and node[1] in wmap
                and not (isinstance(wmap[node[1]], str) and "@" in wmap[node[1]])):
            return ("var", wmap[node[1]])
        return (node[0],) + tuple(_subst_fn_witness(c, wmap) for c in node[1:])
    if isinstance(node, list):
        return [_subst_fn_witness(c, wmap) for c in node]
    return node


def _zmod_moduli(node, acc):
    """Collect the modulus tokens of every `("zmodcast", n, e)` node in the tree — the
    `(e : ZMod n)` casts introduced by the parser. A conclusion carrying such a cast is a
    CONGRUENCE mod n, not a real identity (sweep_eq zmod branch)."""
    if isinstance(node, tuple):
        if node[0] == "dotm" and node[2] == "val" and node[1][0] == "zmodcast":
            # (e : ZMod n).val is the ℕ-valued canonical REPRESENTATIVE — the cast is
            # consumed by `.val` in the evaluator (an exact integer, Gauss's lemma residue
            # test DLMF 27.9), so it must NOT flip the enclosing equality into congruence
            # mode. Still descend into the operand for any independent inner casts.
            _zmod_moduli(node[1][2], acc)
            _zmod_moduli(node[3], acc)
            return
        if node[0] == "zmodcast":
            acc.add(node[1])
        for c in node[1:]:
            _zmod_moduli(c, acc)
    elif isinstance(node, list):
        for c in node:
            _zmod_moduli(c, acc)


# ── §15.10 principal-Gauss connection rows (Ch15KummerPrincipal.lean, DLMF 15.10.19–35) ──
# These are pointwise ℂ equalities  principalW_i = Σ (Γ-ratio)·principalW_j  on the
# nonresonant principal domain (KummerRegular ∧ GammaFinite ∧ InPrincipalGaussDomain).
# The generic 4-point ℂ grid + 24-combo cap PINS a := g0, so every surviving combo
# coincides some parameter pair (b=a / c=a / c=b) — and any such coincidence sends a
# numerator Γ(b−a) or a Γ(c−a)/Γ(c−b) factor onto a Γ-pole (ValueError). On 15.10.25 ALL 24
# combos die that way → a spurious `undersampled/domain`, though the identity is checkable
# the instant a,b,c are distinct. Supplement with curated envs whose (a,b,c) are mutually
# distinct and non-integer-separated and whose z has Im z > 0 — i.e. STRICTLY inside every
# stated hypothesis: Im z > 0 puts z, 1−z AND 1/z off the cut [1,∞) at once, and (post the
# 2026-07 kummerPhase resolution) the §15.10(ii) rows are stated with DLMF's printed
# UPPER-half-plane phases (`him : 0 ≤/(<) z.im`), so a lower-half-plane env sits OUTSIDE
# the stated hypothesis, where the conjugate phase makes the printed display genuinely
# fail (rel ≈ 0.6–0.8 measured on 15.10.23 at the two pre-resolution Im z < 0 envs — a
# fabricated FAIL on a kernel-proven row). Additive: envs are only appended, no point is
# dropped and no tolerance/gate changes; a correctly-stated (phased) connection formula
# still PASSes at these points (checked: the phase-corrected 15.10.25 residual is ~1e-16
# here), only a mis-transcribed one FAILs.
_PRINCIPAL_GAUSS_HEADS = {"principalGauss", "principalW1", "principalW2",
                          "principalW3", "principalW4", "principalW5", "principalW6"}
_PRINCIPAL_GAUSS_ENVS = [
    {"a": mp.mpc("0.2", "0.1"),   "b": mp.mpc("0.35", "-0.15"),
     "c": mp.mpc("0.7", "0.3"),   "z": mp.mpc("0.3", "0.4")},
    {"a": mp.mpc("0.15", "-0.2"), "b": mp.mpc("0.5", "0.25"),
     "c": mp.mpc("0.85", "-0.1"), "z": mp.mpc("-0.2", "0.5")},
    {"a": mp.mpc("0.3", "0.35"),  "b": mp.mpc("0.1", "-0.4"),
     "c": mp.mpc("0.6", "0.2"),   "z": mp.mpc("0.35", "0.45")},
    {"a": mp.mpc("0.25", "-0.1"), "b": mp.mpc("0.45", "0.3"),
     "c": mp.mpc("0.9", "0.15"),  "z": mp.mpc("0.4", "0.3")},
]


# ── §15.6 vertical-line Mellin–Barnes reps of principalOlver (Ch15IntegralRepresentations.lean,
# DLMF 15.6.6 / 15.6.7) ──  These are  𝐅(a,b;c;z) = C · ∫_{σ−i∞}^{σ+i∞} (Γ-quotient)·w^t dt
# with t = σ + iu, w = −z (15.6.6) resp. 1−z (15.6.7).  The representation converges and holds
# ONLY on the intersection of three constraints the coarse ℂ grid cannot encode:
#   (i)  the vertical line is strictly interior to the pole-separating window
#          max(−Re a,−Re b) < σ < 0        (15.6.6)
#          max(−Re a,−Re b) < σ < min(0, Re(c−a−b))   (15.6.7)
#        — this separates the ascending Γ(a+t)Γ(b+t) pole ladders from the descending Γ(−t)
#          (and Γ(c−a−b−t)) ladders, exactly Barnes's contour condition;
#   (ii) w sits on the principal branch off its cut: |ph(−z)| < π (15.6.6) / |ph(1−z)| < π
#        (15.6.7), i.e. z ∉ [0,∞) resp. z ∉ [1,∞) — this is `InPrincipalGaussDomain [z]`;
#   (iii) a,b (and c−a,c−b for 15.6.7) are off the Γ poles — `GammaFinite …`.
# The parser lifts NONE of (i)-lower (a `max (…)(…)` bound), (ii), or (iii) into a per-sample
# filter, so the default grid samples σ below max(−Re a,−Re b) and z on the positive real axis
# — OFF the sector, where the contour rep is simply a different analytic branch — and the row
# FAILs spuriously (worst≈1.25/1.97), then downgrades to `contour-sector-unverified` (the free-ℂ
# biinf-integral guard, classify_and_check). Supplement/replace with curated envs whose σ is
# STRICTLY interior to the window valid for BOTH rows (max(−Re a,−Re b) < σ < 0, with c chosen so
# Re(c−a−b) > 0) and whose z has Im z ≠ 0 with −z, 1−z both well inside the principal cut — i.e.
# strictly inside every stated hypothesis.  SELF-VALIDATED against an INDEPENDENT vertical-line
# quadrature of the DEFINING Barnes integral (docs/verification/ch15/probe_g1_mb.py): 𝐅 = the
# curated-env integral to rel ≈ 1e-41 at every point, an anchor no mis-transcribed contour could
# meet.  Additive: fires ONLY on a principalOlver head + a doubly-infinite integral + a real σ
# binder (below); the biinf-integral evaluator's own certified-quadrature gate (QUAD_CONTOUR_GATE,
# evaluate ~3878) still refuses any sample whose u-quadrature does not converge, so a divergent
# contour is dropped, never scored.
_PRINCIPAL_MB_HEADS = {"principalOlver"}
_PRINCIPAL_MB_ENVS = [
    {"a": mp.mpc("0.5", "0.1"),   "b": mp.mpc("0.4", "-0.15"),
     "c": mp.mpc("1.3", "0.2"),   "z": mp.mpc("-0.3", "0.4"),  "σ": mp.mpf("-0.25")},
    {"a": mp.mpc("0.35", "-0.2"), "b": mp.mpc("0.6", "0.25"),
     "c": mp.mpc("1.6", "-0.1"),  "z": mp.mpc("-0.5", "0.3"),  "σ": mp.mpf("-0.2")},
    {"a": mp.mpc("0.45", "0.3"),  "b": mp.mpc("0.3", "-0.1"),
     "c": mp.mpc("1.1", "0.15"),  "z": mp.mpc("0.2", "0.5"),   "σ": mp.mpf("-0.15")},
    {"a": mp.mpc("0.6", "-0.1"),  "b": mp.mpc("0.55", "0.2"),
     "c": mp.mpc("1.4", "0.1"),   "z": mp.mpc("-0.4", "-0.35"), "σ": mp.mpf("-0.3")},
]


# ── DLMF 15.4.25 bilateral Gamma-ratio Dougall sum (Ch15SpecialCasesB.lean) ──
#   ∑_{n∈ℤ} Γ(a+n)Γ(b+n)/(Γ(c+n)Γ(d+n)) = π²/(sin πa · sin πb) ·
#            Γ(c+d−a−b−1)/(Γ(c−a)Γ(d−a)Γ(c−b)Γ(d−b))
# valid for a,b off ALL of ℤ and 1 < Re(c+d−a−b) (bilateral convergence). NEITHER hypothesis
# lifts into a per-sample filter, and — decisively — the bilateral `_bounded_nsum` has no
# convergence acceleration: its partial sums settle to 1e-25 only when the n^{−Re(c+d−a−b)} tail
# decays fast, so a coarse-grid point with small Re(c+d−a−b) never settles and drops (the
# `undersampled/domain` skip). Curated in-domain envs, self-validated to rel ≤ 3e-28
# (docs/verification/ch15/probe_15_4_25b.py): a,b at O(1) with NONZERO imaginary part — so a,b lie
# off every (real) integer and sin(πa),sin(πb) ≠ 0 BY CONSTRUCTION — and c,d near 7 with nonzero
# Im so Re(c+d−a−b) ≈ 13 (the tail settles in a few hundred terms) and every Γ argument is off its
# poles. ADDITIVE: sampling restricted to the stated hypothesis domain; no tolerance/gate change.
_BILATERAL_GAMMA_ENVS = [
    {"a": mp.mpc("0.4", "0.3"),   "b": mp.mpc("0.6", "-0.2"),
     "c": mp.mpc("6.7", "0.1"),   "d": mp.mpc("7.3", "-0.15")},
    {"a": mp.mpc("-0.35", "0.25"),"b": mp.mpc("0.7", "0.15"),
     "c": mp.mpc("6.2", "-0.1"),  "d": mp.mpc("7.1", "0.2")},
    {"a": mp.mpc("0.25", "-0.4"), "b": mp.mpc("-0.55", "0.5"),
     "c": mp.mpc("6.9", "0.2"),   "d": mp.mpc("7.4", "0.3")},
]


# ── §5.13 / §5.9 vertical-line & real-line Barnes integrals of Γ products (Ch5Tables.lean,
# Ch5IntegralReps.lean) ──  N3-barnes-vertical-line-integrals.  Four DLMF entries whose
# integrand is a product of Γ (and ζ / reciprocal-Γ) factors along a line, whose convergence
# hypotheses do NOT lift into per-sample filters, so the coarse grid samples OFF the stated
# domain (spurious contour-sector FAIL / undersampled / eval-timeout).  Each env set below is
# STRICTLY inside every stated hypothesis and SELF-VALIDATED against the DLMF DEFINING integral,
# computed by the SAME finite-window / mp.quad quadrature the evaluator uses
# (docs/verification/resolve-surfaces/probe_n3_ab.py, probe_5134.py, probe_zeta_all.py).

# DLMF 5.13.1  (1/2π)∫_ℝ Γ(c+it+a)Γ(b-(c+it)) z^{-(c+it)} dt = Γ(a+b) z^a/(1+z)^{a+b}.
# Hyps: -Re a < c < Re b, 0 < Re(a+b), z ∈ slitPlane. The Γ·Γ integrand decays like e^{-π|t|};
# the coarse ℂ grid samples c OUTSIDE (-Re a, Re b) and z on the slit — off the Barnes contour
# condition — giving a spurious FAIL that downgrades to contour-sector-unverified (worst≈1.114).
# Curated envs put c strictly interior to (-Re a, Re b), 0 < Re(a+b), z off the slit with
# Im z ≠ 0.  SELF-VALIDATED: rel ≤ 1e-31 at every point (probe_n3_ab.py).
_BARNES_2GAMMA_ENVS = [
    {"a": mp.mpc("0.3", "0.2"),  "b": mp.mpc("0.7", "-0.1"), "z": mp.mpc("0.6", "0.5"),  "c": mp.mpf("0.1")},
    {"a": mp.mpc("0.5", "-0.3"), "b": mp.mpc("0.9", "0.2"),  "z": mp.mpc("1.4", "-0.7"), "c": mp.mpf("0.2")},
    {"a": mp.mpc("0.4", "0.1"),  "b": mp.mpc("0.6", "0.3"),  "z": mp.mpc("-0.3", "0.9"), "c": mp.mpf("0.0")},
    {"a": mp.mpc("0.8", "-0.2"), "b": mp.mpc("0.5", "0.15"), "z": mp.mpc("0.9", "0.4"),  "c": mp.mpf("0.3")},
]

# DLMF 5.9.11 / 5.9.17  Barnes-ζ vertical-line reps of Ln Γ(z+1) and ψ(z+1), on Re s = -c with
# s = -c + it. Hyps: 1 < c < 2, z ∈ slitPlane. The default grid samples c outside (1,2) and z on
# the slit, and — decisively — the [-∞,∞] tanh-sinh transform stalls on the oscillatory ζ(c-it)
# integrand past the 8 s per-sample budget (eval-timeout). Curated envs put c strictly in (1,2)
# and z off the slit with Im z ≠ 0; the adaptive finite-window quad (evaluate ~4159) evaluates
# each in ≈0.6 s. SELF-VALIDATED: rel ≤ 1.3e-26 for BOTH rows at every point (probe_zeta_all.py).
_BARNES_ZETA_ENVS = [
    {"z": mp.mpc("0.6", "0.4"),  "c": mp.mpf("1.5")},
    {"z": mp.mpc("1.3", "-0.7"), "c": mp.mpf("1.4")},
    {"z": mp.mpc("-0.3", "0.9"), "c": mp.mpf("1.6")},
    {"z": mp.mpc("0.9", "0.3"),  "c": mp.mpf("1.5")},
]

# DLMF 5.13.4  Ramanujan reciprocal-Γ real integral ∫_ℝ dt/(Γ(a+t)Γ(b+t)Γ(c-t)Γ(d-t)) =
# Γ(a+b+c+d-3)/(Γ(a+c-1)Γ(a+d-1)Γ(b+c-1)Γ(b+d-1)), valid for a+b+c+d > 3. The tail decays only
# like |t|^{2-(a+b+c+d)}·(oscillation); the coarse grid samples a+b+c+d just above 3, where the
# tail is ~|t|^{-1} and NO quadrature settles (undersampled/domain). Curated envs put a+b+c+d
# well above 3 (∈ [9.6, 12]) so the tail is ~|t|^{-7} and mp.quad's OWN certified error estimate
# clears QUAD_CONTOUR_GATE (=1e-10). SELF-VALIDATED: rel ≤ 1e-12, qerr ≤ 2e-12 (probe_5134.py);
# a near-boundary sum→3⁺ sample keeps qerr ≈ 2e-9 and is still (soundly) dropped by that gate.
_RAMANUJAN_RECIP_ENVS = [
    {"a": mp.mpf("2.5"), "b": mp.mpf("2.3"), "c": mp.mpf("2.7"), "d": mp.mpf("2.1")},
    {"a": mp.mpf("3.0"), "b": mp.mpf("2.5"), "c": mp.mpf("3.5"), "d": mp.mpf("2.0")},
    {"a": mp.mpf("3.2"), "b": mp.mpf("2.8"), "c": mp.mpf("2.6"), "d": mp.mpf("3.4")},
    {"a": mp.mpf("2.8"), "b": mp.mpf("3.1"), "c": mp.mpf("2.4"), "d": mp.mpf("3.3")},
]


# ── DLMF 15.14.1 Mellin transform of Olver's 𝐅 on the negative axis (Ch15Integrals.lean) ──
#   ∫₀^∞ x^{s−1} 𝐅(a,b;c;−x) dx = Γ(s)Γ(a−s)Γ(b−s)/(Γ(a)Γ(b)Γ(c−s)), valid on the Mellin
# STRIP 0 < Re s < min(Re a, Re b). The strip hypotheses (`0 < s.re`, `s.re < a.re`,
# `s.re < b.re`) do NOT lift into per-sample filters (they constrain the real PARTS of ℂ
# binders and couple s to a, b), so the coarse ℂ grid samples s outside the strip — where
# the ray integral diverges at 0 or ∞ (the ray evaluator then drops the point) — and the
# row starves into `undersampled/domain`. Restrict to curated in-strip envs, each with
# 0 < Re s < min(Re a, Re b) and every Γ argument (s, a−s, b−s, a, b, c−s) off its poles,
# with nonzero imaginary parts so the branch is generic. Self-validated to rel ≤ 1e-21 vs the
# closed-form Γ-ratio (docs/verification/resolve-surfaces/probe_quad.py). Additive: sampling
# restricted to the stated hypothesis strip; the ray evaluator's tail-exponent + quadrature-
# error gates still decide each point, so a mis-transcribed rep FAILs and nothing is loosened.
_OLVER_MELLIN_ENVS = [
    {"a": mp.mpc("1.5", "0.1"),  "b": mp.mpc("1.3", "-0.15"),
     "c": mp.mpc("2.2", "0.2"),  "s": mp.mpc("0.6", "0.05")},
    {"a": mp.mpc("2.0", "-0.2"), "b": mp.mpc("1.8", "0.25"),
     "c": mp.mpc("3.0", "0.1"),  "s": mp.mpc("0.4", "-0.1")},
    {"a": mp.mpc("1.7", "0.3"),  "b": mp.mpc("2.1", "-0.2"),
     "c": mp.mpc("2.8", "0.1"),  "s": mp.mpc("0.5", "-0.15")},
    {"a": mp.mpc("1.4", "-0.1"), "b": mp.mpc("1.6", "0.2"),
     "c": mp.mpc("2.5", "-0.25"),"s": mp.mpc("0.7", "0.1")},
]


# ── DLMF 15.15.1 expansion of 𝐅(a,b;c;1/z) about 1/z₀ (Ch15Sums.lean) ──
#   𝐅(a,b;c;1/z) = (1−z₀/z)^{−a} Σ_{s≥0} ((a)ₛ/s!) 𝐅(−s,b;c;1/z₀) (1−z/z₀)^{−s},
# converging for |z−z₀| > max(|z₀|, |z₀−1|). The convergence hypothesis (`_hconv`) and the
# principal-domain hypothesis (`_hdom`) are underscore binders that never lift into per-sample
# filters, so the default ℂ grid overwhelmingly samples z OUTSIDE the convergence region — where
# the series diverges and the acceleration fallback (a dps=100 uninterruptible C loop) burns the
# whole eval budget, a false `hassum eval-timeout`. Restrict to curated envs sampled with a LARGE
# margin |z−z₀| ≫ max(|z₀|,|z₀−1|), strictly inside the stated convergence domain — where the
# series settles to <1e-30 by ~70 terms (probe_1515b.py). z far from a modest z₀ (both z-signs);
# the terminating value 𝐅(−s,b;c;1/z₀) is the exact polynomial for every 1/z₀ (the corrected
# _olverHypergeometric binding). Additive: sampling restricted to the theorem's own domain, no
# tolerance / gate / settle-window change; a false identity still FAILs at these in-domain points.
_GAUSS_1515_ENVS = [
    {"a": mp.mpc("0.3", "0.2"),   "b": mp.mpc("0.5", "-0.1"),
     "c": mp.mpc("1.3", "0.15"),  "z": mp.mpc("8.0", "1.0"),   "z₀": mp.mpc("0.6", "0.0")},
    {"a": mp.mpc("0.6", "0.1"),   "b": mp.mpc("0.7", "0.2"),
     "c": mp.mpc("1.6", "-0.1"),  "z": mp.mpc("-9.0", "2.0"),  "z₀": mp.mpc("0.7", "0.1")},
    {"a": mp.mpc("0.4", "-0.3"),  "b": mp.mpc("0.9", "0.4"),
     "c": mp.mpc("2.1", "0.2"),   "z": mp.mpc("12.0", "-3.0"), "z₀": mp.mpc("0.5", "-0.2")},
    {"a": mp.mpc("0.35", "0.15"), "b": mp.mpc("0.65", "-0.1"),
     "c": mp.mpc("1.45", "0.2"),  "z": mp.mpc("-20.0", "5.0"), "z₀": mp.mpc("2.0", "0.5")},
]


# ── DLMF 5.9.5 analytic-continuation Γ integral (Ch5IntegralReps.lean) ──
#   Γ(x) = ∫₀^∞ t^{x−1}(e^{−t} − Σ_{k=0}^{n} (−1)^k t^k/k!) dt, valid on the thin window
# −n−1 < x < −n. The extractor records NO constraints for this row (the two order hypotheses
# couple the ℕ binder n to the real x through a cast and never lift into per-sample filters),
# so the default (n, x) grid essentially never lands in (−n−1, −n) and the row starves into
# `undersampled/domain`. Restrict to curated in-window envs — x near the middle of each window
# for n = 0, 1, 2, where the slow power-law tail (t^{x+n−1}, exponent in (−2,−1)) is cleanly
# certified by `_quad_ray_slow`. Additive: sampling restricted to the stated hypothesis window;
# the ray evaluator's own gates still decide each point (a boundary/non-converging sample drops).
_GAMMA595_ENVS = [
    {"n": mp.mpf(0), "x": mp.mpf("-0.3")}, {"n": mp.mpf(0), "x": mp.mpf("-0.5")},
    {"n": mp.mpf(0), "x": mp.mpf("-0.7")}, {"n": mp.mpf(1), "x": mp.mpf("-1.3")},
    {"n": mp.mpf(1), "x": mp.mpf("-1.5")}, {"n": mp.mpf(2), "x": mp.mpf("-2.4")},
]


def _contains_fsum(node):
    """True iff the AST contains a `Finset.range` partial sum node (`fsum`)."""
    if isinstance(node, tuple):
        if node[0] == "fsum":
            return True
        return any(_contains_fsum(c) for c in node[1:])
    if isinstance(node, list):
        return any(_contains_fsum(c) for c in node)
    return False


def _is_gamma595_shape(L, R):
    """DLMF 5.9.5: one side is `Gamma x` and the other is a right-ray integral whose integrand
    carries BOTH a `Real.exp` factor and a `Finset.range` partial-Taylor sum — the exact
    analytic-continuation remainder shape the curated in-window envs are built for."""
    def is_gamma(n):
        return (isinstance(n, tuple) and n[0] == "app"
                and n[1] in (("var", "Gamma"), ("var", "Real.Gamma")) and len(n[2]) == 1)
    def ray_taylor(n):
        return (isinstance(n, tuple) and n[0] == "integral" and n[3] == ("inf",)
                and _contains_fsum(n[4])
                and _mentions_any_head(n[4], {"Real.exp", "exp", "Complex.exp"}))
    return (is_gamma(L) and ray_taylor(R)) or (is_gamma(R) and ray_taylor(L))


def _has_bilateral_zsum(node):
    """True iff the AST contains a bilateral ℤ-sum node (`∑' n : ℤ, …`, node[0]=='sum',
    node[3]=='ℤ') — the DLMF 15.4.25 doubly-infinite series shape."""
    if isinstance(node, tuple):
        if len(node) >= 4 and node[0] == "sum" and node[3] == "ℤ":
            return True
        return any(_has_bilateral_zsum(x) for x in node)
    if isinstance(node, list):
        return any(_has_bilateral_zsum(x) for x in node)
    return False


def _mentions_any_head(node, names):
    """True iff any application/var head anywhere in the AST is one of `names`."""
    if isinstance(node, tuple):
        if len(node) >= 2 and node[0] == "app" and isinstance(node[1], tuple) \
                and node[1] and node[1][0] == "var" and node[1][1] in names:
            return True
        if len(node) >= 2 and node[0] == "var" and node[1] in names:
            return True
        return any(_mentions_any_head(x, names) for x in node)
    if isinstance(node, list):
        return any(_mentions_any_head(x, names) for x in node)
    return False


def _dirichlet_sum_moduli(node, acc):
    """Collect the modulus VARIABLE of every character-group sum/product node whose domain
    annotation (node[3]) is `DirichletCharacter <ring> k` — `∑ χ : DirichletCharacter ℂ k,
    body` binds χ, so `collect_free` never surfaces k when it appears nowhere else in the
    conclusion (the DLMF 27.8.6 zero case `∑ χ, χ a = 0`); the evaluator still needs k in
    env to enumerate the φ(k) characters. Purely additive — callers inject a collected
    name only when it is a declared binder."""
    if isinstance(node, tuple):
        if node[0] in ("sum", "prod") and len(node) > 3 and isinstance(node[3], str):
            mm = re.match(r'DirichletCharacter\s+\S+\s+([A-Za-z_]\w*)$', node[3])
            if mm:
                acc.add(mm.group(1))
        for c in node[1:]:
            _dirichlet_sum_moduli(c, acc)
    elif isinstance(node, list):
        for c in node:
            _dirichlet_sum_moduli(c, acc)


def _near_int(x):
    """The exact integer a computed value represents, or None. Guards the ZMod congruence
    gate: a nonreal / non-integer / too-large-for-exact-float value (e.g. a ZMod inverse
    lifted as a real reciprocal) yields None — the sample drops honestly, since reducing an
    inexact float mod n could fabricate either verdict."""
    if isinstance(x, mp.mpc):
        if abs(x.imag) > mp.mpf("1e-12"):
            return None
        x = x.real
    if not mp.isfinite(x) or abs(x) > mp.mpf("1e15"):
        return None
    xi = mp.nint(x)
    if abs(x - xi) > mp.mpf("1e-9"):
        return None
    return int(xi)


def sweep_eq(L, R, binders, constraints=None, relation="eq", _diversify=False):
    """Sample free vars; return (verdict, detail). verdict ∈ PASS/FAIL/UNABLE("unable to proceed"); detail carries <why>.
    relation="eq": PASS iff L=R at every sample. relation="ne": L≠R — PASS iff the gap
    stays clear of 0 at every sample, FAIL on a sampled coincidence L≈R (refutation).

    `_diversify` is set ONLY by this function's own one-shot retry of a
    `trivial-zero/unexercised` skip (see that return): it selects the 24-combo window by
    STRIDING the same cartesian product instead of taking its lexicographic prefix, so a
    leading variable pinned at a both-sides-vanishing grid value no longer hides the points
    that exercise the row. Same grids, same filters, same tolerances."""
    constraints = constraints or {}
    # TRANSITIVE-POSITIVITY grid inference (ADDITIVE, sound): a chain hypothesis
    # `0 < x` ∧ `x < y` (ltpair/lepair) IMPLIES `0 < y`, but only x carries the `pos`
    # flag — y keeps the generic mixed-sign grid, and on a row like the ₂F₁ z = 1
    # connection formula (DLMF 15.10.21: `0 < b`, `b < c`, `c < 1`) the filtered pair
    # grid is empty and the row starves into `undersampled` even though the hypothesis
    # domain is plainly non-empty. Deriving the flag samples y on the positive grid —
    # strictly inside the stated hypothesis domain (the ltpair filter still applies
    # per sample); no tolerance or scoring change, nothing loosened.
    for _q in constraints.get('_pairs', []):
        if _q[0] in ('ltpair', 'lepair') and constraints.get(_q[1]) == 'pos' \
                and constraints.get(_q[2]) is None:
            constraints = {**constraints, _q[2]: 'pos'}
    # ELLIPTIC-MODULUS sampling window: rows over the Legendre elliptic family
    # (ellipticF/E/Pi and their integrand defs) sample an UNCONSTRAINED real modulus
    # binder `k` inside the principal interval |k| < 1. The FLMF defs are totalized
    # (junk-Real.sqrt) and identities like ellipticPi_characteristic_zero hold for all
    # real k, but outside |k| < 1 both sides can only be evaluated by junk-kink
    # quadrature whose noise (≈2.5e-2) swamps the equality gate — a fabricated FAIL.
    # Sampling is OUR choice: restricting to the principal window is sound (PASS
    # evidence on a subdomain, never a fabricated verdict outside it).
    if any(_contains_head(_side, _ELLIPTIC_HEADS) for _side in (L, R)):
        for _v, _b in binders.items():
            if _b == "R" and _v in ("k", "k'", "κ") and constraints.get(_v) is None:
                constraints = {**constraints, _v: 'unit'}
    # LOCAL-HEUN argument window (see SAMPLES_HEUN_DISK): an UNCONSTRAINED ℂ binder in the
    # series-argument slot of `heunFn`/`heunF0`/`heunF1`/`heunTheta` is sampled inside the
    # Maclaurin lens where those sums exist at all. Same rationale as the elliptic window
    # above: sampling a subdomain of the row's stated domain, never a scoring change.
    _hv = set()
    for _side in (L, R):
        _heun_arg_vars(_side, _hv)
    for _v in _hv:
        if binders.get(_v) == "C" and constraints.get(_v) is None:
            constraints = {**constraints, _v: 'heundisk'}
    # instantiate ∀-quantified function variables at their anchored witnesses BEFORE the
    # free/unbound scan, so e.g. `f (p^k) = f p ^ k` under `IsCompletelyMultiplicative f`
    # is checked at f = λ instead of skipping as `unbound:f`.
    wmap = constraints.get('_fnwitness') or {}
    # a TUPLE-valued witness (the `IsMultiplicative f` family ob.MULTIPLICATIVE_WITNESSES —
    # φ, μ) checks the row at EVERY member: a counterexample at any single witness already
    # disproves the ∀-statement (FAIL), PASS only when every member's sweep passes, and
    # otherwise the first non-PASS skip is reported honestly. Strictly stronger evidence
    # than one witness; recursion resolves one tuple per call, so several ∀-function
    # binders compose.
    for _wv, _ws in wmap.items():
        if isinstance(_ws, (tuple, list)):
            outs = [(w, sweep_eq(L, R, binders,
                                 {**constraints, '_fnwitness': {**wmap, _wv: w}}, relation))
                    for w in _ws]
            for w, o in outs:
                if o[0] == "FAIL":
                    return (o[0], f"{_wv}:={w} {o[1]}")
            if all(o[0] == "PASS" for _, o in outs):
                return ("PASS", "; ".join(f"{_wv}:={w} {o[1]}" for w, o in outs))
            return next(o for _, o in outs if o[0] != "PASS")
    if wmap:
        L, R = _subst_fn_witness(L, wmap), _subst_fn_witness(R, wmap)
    # ── ZMod-n congruence mode ──: a `(e : ZMod n)` cast anywhere in the conclusion means
    # the Lean `=` lives in ℤ/nℤ — the DLMF reading is the congruence L ≡ R (mod n) of the
    # ℤ-lifts (Euler's criterion legendreSym_eq_pow, DLMF 27.9: (a|p) ≡ a^((p−1)/2) mod p).
    # Both sides must evaluate to EXACT integers at each sample (_near_int gate) and are
    # scored by (L−R) mod n = 0; anything else keeps the honest skip/point-drop.
    zmods = set(); _zmod_moduli(L, zmods); _zmod_moduli(R, zmods)
    zmod_tok = None
    if zmods:
        if relation != "eq":
            return (UNABLE, "zmod-congruence (only = supported)")
        if len(zmods) > 1:
            return (UNABLE, f"zmod-congruence (mixed moduli {sorted(zmods)})")
        zmod_tok = next(iter(zmods))
        if not zmod_tok.isdigit() and zmod_tok not in binders:
            return (UNABLE, f"zmod-congruence (modulus {zmod_tok} not a sampleable binder)")
    free = set(); collect_free(L, free); collect_free(R, free)
    # a Finset.univ character-group sum `∑ χ : DirichletCharacter ℂ k, body` binds χ, but
    # its MODULUS k lives only in the sum's domain annotation, which collect_free never
    # scans — when k appears nowhere else in the conclusion (the pure-zero orthogonality
    # `∑ χ, χ a = 0`, DLMF 27.8.6) it is never sampled and the evaluator cannot enumerate
    # the φ(k) characters (every point drops). Inject the modulus when it is a declared
    # binder — mirrors the ∀-quantified `_dirchmod` character/modulus coupling below.
    dmods = set(); _dirichlet_sum_moduli(L, dmods); _dirichlet_sum_moduli(R, dmods)
    free |= {v for v in dmods if v in binders}
    binders = _lattice_binders(free, binders)
    # a `Fin q`-parametrized complex vector `A : Fin q → ℂ` (meijerG_eq_pFq's parameter
    # tuples) never mentions its CARDINALITY q as a literal token in the conclusion
    # (`A i`/`∏ i, Γ(Aᵢ)` carry no `q`), so collect_free cannot see it. Inject q — like
    # the DirichletCharacter modulus injection above — whenever a 'finvecC' vector is
    # free, so the sweep samples q and the per-env resolution below can construct A/B.
    finvecdim = (constraints or {}).get('_finvecdim', {})
    # a finvecC vector applied ONLY in application-HEAD position (`a j`, `b j` — the DLMF 5.8.5
    # ratio product ∏ₖ∏ⱼ(aⱼ+k)/(bⱼ+k)) is never surfaced by collect_free: the generic app
    # fallback frees the ARGUMENTS of `a j`, not the head `a`. Inject every finvecC binder the
    # extractor recorded a cardinality for (the `_finvecdim` keys are exactly the vectors this
    # theorem uses), so a/b are sampled and the per-env finvec construction below builds them.
    # These are DECLARED binders (typed 'finvecC'), so this can never produce an `unbound` skip;
    # additive — a redundant set-union for any vector collect_free already freed (direct-arg
    # usage like `pFq A B z`).
    free |= {v for v in finvecdim if binders.get(v) == "finvecC" and v in binders}
    finvec_dims = {finvecdim[v] for v in free
                   if binders.get(v) == "finvecC" and v in finvecdim}
    free |= {d for d in finvec_dims if d in binders}
    # ── hypothesis-CARRIER pin ('_carrier', see the binder scrape) ──────────────────────
    # The row assumes a named Prop carrier that DETERMINES some of its binders (DLMF
    # 31.14.2's {α,β} from (a,γ,q); 31.8.1's β,γ,δ,ε from (m,α)). Sampling those binders
    # freely would score the conclusion OUTSIDE the stated hypothesis — a fabricated
    # refutation — so they are dropped from the grid here and computed per sample from
    # `ob.CARRIER_PINS[…]['pin']` in the loop below. The remaining arguments (the free ones
    # the display does not fix) stay in the grid; a FUNCTION-valued one (`m : Fin 4 → ℕ`)
    # sits in application-HEAD position, which collect_free never frees, so inject it.
    # Fires ONLY when every argument's binder base matches the registry's declared kinds —
    # a carrier assumed on other data keeps the row's honest skip, never a wrong ladder.
    # ── REAL Fin-vector binders ('_finvecRdim', DLMF 31.15.12) ─────────────────────────
    # Promote the row's `Fin <dim> → ℝ` binders to `.q`-tagged Fin-vector callables so a
    # bare `∏ j, ∏ k, …` over two DIFFERENT Fin carriers finds each range in the row's own
    # data. GUARD — this fires only when the signature has NO uncaptured hypothesis binder
    # (no binder of base 'other'): those are exactly the rows whose vector data is free, so
    # constructing it is sound. A row like DLMF 31.15.4/31.15.7, whose vectors are pinned by
    # ∀-hypotheses the extractor cannot capture (the equilibrium relation, the partial-
    # fraction identity), keeps its present pointwise sampling and its honest skip — never
    # a fabricated refutation. Dimensions are the DECLARED expressions, evaluated per sample.
    _fvr = dict((constraints or {}).get('_finvecRdim', {}))
    if _fvr and any(t == "other" for t in binders.values()):
        _fvr = {}
    _fvr_dims = {}
    for _nm, _dx in list(_fvr.items()):
        try:
            _da = parse(_dx)
            _da = _da[1] if _da and _da[0] == "expr" else _da
        except Exception:
            _fvr = {}
            break
        _dfv = set(); collect_free(_da, _dfv)
        if not _dfv or any(binders.get(x) != "N" for x in _dfv):
            _fvr = {}
            break
        _fvr_dims[_nm] = (_da, _dfv)
    if _fvr:
        free |= set(_fvr)
        for _nm in _fvr:
            free |= _fvr_dims[_nm][1]
    _carrier, _cspec, _cargs = (constraints or {}).get('_carrier'), None, []
    if _carrier:
        _cspec = getattr(ob, 'CARRIER_PINS', {}).get(_carrier[0])
        _cargs = _carrier[1]
        if _cspec is not None and not all(
                binders.get(nm) == kd for nm, kd in zip(_cargs, _cspec["kinds"])):
            _cspec = None
    if _cspec is not None:
        free -= {_cargs[i] for i in _cspec["solves"]}
        # every argument the display does NOT determine joins the grid, even when this
        # particular conjunct does not mention it: the pin reads the whole carrier tuple
        # (31.8.1's γ is fixed by m alone, but β needs α as well), so a missing input would
        # drop every point. Extra sampled binders are inert for the operands themselves.
        free |= {nm for i, nm in enumerate(_cargs)
                 if i not in _cspec["solves"] and nm in binders}
    # a BARE polynomial equality (`Σ … bernoulliPoly k = monomial n …`, both sides ∈ R[X] with
    # no explicit `X`) must sample the indeterminate — else the poly heads raise "without
    # indeterminate" and every point drops. Inject IND when a poly head appears un-`eval`-ed.
    if IND not in free and (_uses_indeterminate(L) or _uses_indeterminate(R)):
        free.add(IND)
    # SOUNDNESS: a free symbol must be a declared binder or the indeterminate. An unknown
    # bare/dotted name (n.negOnePow, barnesGNat, γ, …) is UNSUPPORTED — skip, never sample
    # it as a fresh real (which would fabricate a mismatch or a spurious match).
    # a registry name in `free` is a FUNCTION reference (a bare fn like `erfc` in `f = g`),
    # not a variable: neither flagged unbound nor sampled. Sampleables = binders + indeterminate.
    unbound = [v for v in free if v != IND and v not in binders and _reg_resolve(v) is None]
    if unbound:
        return (UNABLE, f"unbound:{unbound[0]}")
    # an env-dependent ∀-witness ATOM (registry kind 'envfn', e.g. `O.P.roots.toFinset.card`
    # — DLMF §18.2(vi) at the canonical Laguerre witness) reads sampled binders that need
    # not occur syntactically in the conclusion (`… .card = O.P.natDegree` never mentions
    # n): keep every integer-sampleable DECLARED binder in the grid so the witness head
    # sees the degree it is instantiated at. Additive — fires only when an envfn atom is
    # present, and extra sampled vars are inert for the other operand.
    has_envfn = any((_reg_get(v) or (None,))[0] == "envfn"
                    for v in free if v != IND and v not in binders)
    free = {v for v in free if v == IND or v in binders}    # drop bare-fn refs from sampling
    # a defining-equality-pinned variable (`hζ : ζ = f(z)`, DLMF 15.8.32) is NOT sampled — it is
    # computed per env from its stated value in the loop below (the _defeq constructive pin).
    free -= {q[0] for q in (constraints or {}).get('_defeq', [])}
    # a scalar-Prop-CARRIER-pinned variable ('_linpin', `h : HeunSeriesTypeI1 α β ε lam mu`,
    # DLMF 31.11.3/10/11/14–17) is likewise NOT sampled: it is solved per env from the
    # carrier's own equation in the loop below, so the display is scored INSIDE the stated
    # hypothesis instead of at an independently drawn (λ, μ).
    # Only the pins whose variable this OPERAND actually mentions are active: a conjunction
    # is scored one conjunct at a time (see the ("and", …) dispatch), and a sibling
    # conjunct's pin would demand operands this one never samples — every point would then
    # drop into a spurious `undersampled/domain`. Each active pin's own equation brings its
    # inputs into the grid.
    linpins = []
    for _lv, _ls, _rs in (constraints or {}).get('_linpin', []):
        if _lv not in free:
            continue
        try:
            _la, _ra = parse(_ls), parse(_rs)
            _la = _la[1] if _la and _la[0] == "expr" else _la
            _ra = _ra[1] if _ra and _ra[0] == "expr" else _ra
            _lfv = set()
            collect_free(_la, _lfv)
            collect_free(_ra, _lfv)
        except Exception:
            linpins = []
            break
        linpins.append((_lv, _la, _ra, binders.get(_lv),
                        {x for x in _lfv if x in binders}))
    for _q in linpins:
        free |= _q[4]
    free -= {q[0] for q in linpins}
    # a BARE scalar-EQUATION hypothesis pin ('_eqpin', `ha : a * k ^ 2 = 1`, DLMF 31.7.5's
    # cleared-denominator Lamé dictionary): the same constructive treatment as '_linpin'
    # above, for equations stated directly in the binder list rather than through a named
    # Prop carrier. The pinned variables leave the grid and are solved per sample from the
    # stated equations (in the recorded solve order), so the display is scored INSIDE the
    # stated hypotheses instead of at independently drawn parameters. Their remaining
    # INPUTS join the grid even when this particular conjunct does not mention them — the
    # pin reads the whole system (31.7.5's `ε` needs α, β, γ, δ, hence ν), so a missing
    # input would drop every point — exactly as the '_carrier' ladder injects its own.
    # Like '_linpin', only the pins this OPERAND needs are activated — but TRANSITIVELY:
    # a pin whose equation READS another pinned variable must have that one computed too
    # (31.7.5's `ε` is fixed by `γ + δ + ε = α + β + 1`, so activating ε must also activate
    # γ, δ, α, β — sampling any of them freely would solve the Fuchsian relation at
    # parameters the dictionary excludes and fabricate `ε ≠ ½`). The remaining, genuinely
    # free inputs of the activated equations join the grid.
    eqpins, _eqspec, _eqok = [], [], True
    for _ev, _els, _ers in (constraints or {}).get('_eqpin', []):
        try:
            _ela, _era = parse(_els), parse(_ers)
            _ela = _ela[1] if _ela and _ela[0] == "expr" else _ela
            _era = _era[1] if _era and _era[0] == "expr" else _era
            _efv = set()
            collect_free(_ela, _efv)
            collect_free(_era, _efv)
        except Exception:
            _eqok = False
            break
        _eqspec.append((_ev, _ela, _era, binders.get(_ev),
                        {x for x in _efv if x in binders}))
    if _eqok and _eqspec:
        _bysrc = {q[0]: q for q in _eqspec}
        _need = {q[0] for q in _eqspec if q[0] in free}
        while True:
            _grow = {x for v in _need for x in _bysrc[v][4] if x in _bysrc} - _need
            if not _grow:
                break
            _need |= _grow
        eqpins = [q for q in _eqspec if q[0] in _need]   # keeps the recorded solve order
        for _q in eqpins:
            free |= {x for x in _q[4] if x not in _need}
        free -= _need
        linpins = linpins + eqpins
    if has_envfn:
        free |= {v for v, t in binders.items() if t in ("N", "Z")}
    # a ∀-quantified Dirichlet character (χ : DirichletCharacter ℂ k) sits in HEAD position
    # (χ a), which collect_free does not free — inject χ, and its modulus k, so the sample
    # loop can instantiate χ from the concrete cyclic-model characters
    # (ob._dirichlet_char_sample, anchored to the DLMF 27.8.1–27.8.4 defining relations).
    for dv, kv in (constraints or {}).get('_dirchmod', {}).items():
        if dv in binders:
            free.add(dv)
            if kv in binders:
                free.add(kv)
    # concrete character binders `{χ : MulChar (ZMod p) ℂ}` / `{e : AddChar (ZMod p) ℂ}`
    # ('_zmodchar', DLMF §27.8): inject the character vars and the row's own modulus p,
    # exactly like the DirichletCharacter coupling above.
    for cv, kv in (constraints or {}).get('_zmodchar', {}).items():
        if cv in binders:
            free.add(cv)
            if kv in binders:
                free.add(kv)
    # ── Wigner 3j magnetic selection rule, solved constructively (ADDITIVE) ─────
    # `h : m₁ + m₂ + m₃ = 0` ('sumzero') was previously only a per-sample REJECTION
    # filter — on the default ℤ grid (positive integers) NO sample can satisfy it, so a
    # 3j row whose argument slots defeat the curated _angmom_envs tuples (the stretched
    # `wigner3j j₁ j₂ (j₁ + j₂) m₁ m₂ m₃`, DLMF 34.3.4, has a compound j₃ slot) starves
    # into `undersampled/domain`. When all three names are ℤ-typed binders, SOLVE the
    # constraint instead: drop c from the independently sampled grids and pin it per
    # sample as c = −(a+b) — exactly the stated hypothesis, mirroring how other derived
    # quantities (Dirichlet characters, lattice periods) are resolved per sample. The
    # _pairs_ok 'sumzero' check below stays in place as a (now no-op) safety gate.
    # real-part ordering pins (DLMF 15.6.8/9 Re c > Re d > 0): [(d, c)] — env[d] gets
    # Re d pinned into (0, Re c) per sample, keeping its sampled imaginary part.
    reorder_pins = [(d, c) for (d, c) in (constraints or {}).get('_reorder', [])
                    if binders.get(d) == "C" and binders.get(c) == "C"]
    defeq_pins = []                       # [(v, ast)]: env[v] := evaluate(f(...)) — DLMF 15.8.32 ζ
    for _dv, _dexpr in (constraints or {}).get('_defeq', []):
        try:
            _da = parse(_dexpr)
            defeq_pins.append((_dv, _da[1] if _da and _da[0] == "expr" else _da))
        except Exception:
            pass
    sumzero_pins = []                     # [(c, a, b)]: env[c] := −(env[a] + env[b])
    _sz_pinned = set()
    for q in (constraints or {}).get('_pairs', []):
        if q[0] == 'sumzero' and all(binders.get(x) == "Z" for x in q[1:4]) \
                and set(q[1:4]) <= free and q[3] not in _sz_pinned:
            sumzero_pins.append((q[3], q[1], q[2]))
            _sz_pinned.add(q[3])
    # ── indicial-root hypothesis, solved constructively (ADDITIVE) ─────
    # `hρ : ρ * (ρ + c − 1) = 0` (the z = 0 indicial equation of the hypergeometric
    # ODE — frobCoeff_gauss, DLMF 15.10.2): ρ is NOT a free parameter — the stated
    # hypothesis pins it to a root, ρ ∈ {0, 1 − c}. Sampling ρ from the unconstrained
    # grid would fabricate a counterexample of a proven theorem (the identity is
    # claimed ONLY on roots). Mirror the sumzero solver: drop ρ from the independent
    # grids and pin it per sample to EACH root in turn (both Frobenius branches are
    # exercised). Sampling restricted to the stated hypothesis domain only; no
    # tolerance or scoring change.
    indroot_pins = []                     # [(v, w)]: env[v] ∈ {0, 1 − env[w]}
    for q in (constraints or {}).get('_pairs', []):
        if q[0] == 'indroot' and q[1] in free and q[2] in free \
                and q[1] not in _sz_pinned:
            indroot_pins.append((q[1], q[2]))
            _sz_pinned.add(q[1])
    # For those same rows, aim the integer grids at the PHYSICAL window (sympy's
    # wigner_3j vanishes identically outside |mᵢ| ≤ jᵢ, so far-from-window points are
    # either trivial zeros or dropped by the toNat phase guard): classify each bare-var
    # slot of a 3j-class head as a j-quantity (physical slots 0–2 → small nonnegative
    # grid) or an m-quantity (slots 3–5 → small symmetric grid, fenced per combo to
    # |mᵢ| ≤ jᵢ BEFORE the cap, like the order-pair hypotheses). Fires ONLY when a
    # sumzero pin is active — no other row's sampling is perturbed; nothing loosened,
    # sampling is re-aimed strictly inside the stated ℤ domain.
    w3j_jvars, w3j_mwin = set(), []
    if sumzero_pins:
        _amapps = []
        _angmom_apps(L, _amapps); _angmom_apps(R, _amapps)
        for _head, _args in _amapps:
            if _head in _3J_ARGMAP and len(_args) == 6:
                _amap = _3J_ARGMAP[_head]
                for _k in range(3):
                    _js, _ms = _args[_amap[_k]], _args[_amap[_k + 3]]
                    _jn = _js[1] if _js[0] == "var" else None
                    _mn = _ms[1] if _ms[0] == "var" else \
                        (_ms[1][1] if _ms[0] == "neg" and _ms[1][0] == "var" else None)
                    if _jn and binders.get(_jn) == "Z":
                        w3j_jvars.add(_jn)
                    if _mn and binders.get(_mn) == "Z" and _mn not in _sz_pinned:
                        w3j_mwin.append(
                            (_mn, _jn if (_jn and binders.get(_jn) == "Z") else None))
    w3j_mvars = {m for m, _ in w3j_mwin}
    grids = []
    for v in sorted(free):
        if v in _sz_pinned:
            continue                       # solved per sample from the sumzero hypothesis
        if v == IND:
            grids.append((v, SAMPLES[IND]))
        else:
            base = binders.get(v, "R")
            flag = constraints.get(v)
            if v in finvec_dims:               # q of a Fin-vector A/B : Fin q → ℂ — kept
                # SMALL (each extra q adds a Γ-product factor and another finvecC
                # construction; DLMF 16.18.1 needs only q = 0,1,2 to exercise the general
                # case beyond the q=0 anchor). EXCEPT when the row also carries a `Fin q`
                # INDEX binder singling out one component (DLMF 31.14.5's j, with its
                # `Σ_{k≠j}` erase-sum): there q ≤ 1 leaves the erase-sum EMPTY and q = 2
                # a single term, so the row would starve as `undersampled`. Shift the grid
                # to 2,3,4 for exactly those rows — a wider, strictly more exercised range,
                # no other row's sampling touched.
                grids.append((v, _f(2, 3, 4)
                              if v in ((constraints or {}).get('_finidxdim', {})).values()
                              else _f(0, 1, 2)))
            elif base == "finidx":             # j : Fin N — a small nonnegative index; a
                grids.append((v, _f(0, 1, 2)))  # draw ≥ the sampled N drops in the callable
            elif base == "finvecC":            # A/B : Fin q → ℂ — PLACEHOLDER (resolved to a
                grids.append((v, [None]))       # concrete `.q`-tagged callable per env below,
                                                # once q, and any lower-bound binder (σ), are
                                                # sampled; never sampled as a bare scalar)
            elif base == "finset":               # s : Finset ι — sampled as its cardinality N,
                grids.append((v, _f(3, 4, 5)))  # so s := Finset.range N (small; DLMF 18.18)
            elif v in _fvr:                    # γ/a/z : Fin <dim> → ℝ — PLACEHOLDER, built
                grids.append((v, [None]))       # per env once its dimension is sampled
            elif base == "absfnR":             # c : ι → ℝ — pointwise-sampled real callables
                # a `∀ k, 0 < a k` hypothesis ('_absfnpos') restricts to POSITIVE callables
                grids.append((v, list(ABSFN_R_POS
                                      if v in constraints.get('_absfnpos', [])
                                      else ABSFN_R)))
            elif base == "absfnN":             # m : ι → ℕ — pointwise-sampled small-nat (≤8) callables
                grids.append((v, list(ABSFN_N)))
            elif base == "lattice":
                grids.append((v, ob.SAMPLE_LATTICES))
            elif base == "dirchar":            # χ : DirichletCharacter ℂ k — character index t,
                grids.append((v, [mp.mpf(t) for t in ob.SAMPLE_DIRICHLET_TS]))   # resolved per
                                               # sample to the t-th character mod the sampled k
            elif base == "mulchar":            # χ : MulChar R R' (abstract ring, DLMF 27.10.9)
                # — instantiated at R := ZMod k from the anchored non-principal Dirichlet
                # characters (ob.SAMPLE_MULCHARS, each .modulus-tagged with its carrier k).
                # A CONCRETE `MulChar (ZMod p) ℂ` binder ('_zmodchar') instead samples a
                # character INDEX, resolved per sample to the t-th character mod the row's
                # OWN sampled p (its modulus must track p, not the fixed abstract grid).
                if v in constraints.get('_zmodchar', {}):
                    grids.append((v, [mp.mpf(t) for t in ob.SAMPLE_DIRICHLET_TS]))
                else:
                    grids.append((v, list(ob.SAMPLE_MULCHARS)))
            elif base == "addchar":            # ψ : AddChar R R' — kernel index n of
                # ψₙ(x) = e^{2πinx/k} (the DLMF 27.10.9 kernel); resolved per sample to
                # ob._addchar_sample(k, n) with k = the modulus of the sampled χ, so both
                # characters live on the SAME ring (see the loop below).
                grids.append((v, [mp.mpf(n) for n in ob.SAMPLE_ADDCHAR_NS]))
            elif base == "latticept":          # period l ∈ L.lattice — set to ω₁ in the loop
                grids.append((v, [mp.mpf(0)]))
            elif base in ("C", "H"):           # ℍ (upper half-plane) reuses the Im>0 grid
                # honour a `Re s > 1` / `Re s ≥ 1` hypothesis (ζ-type series convergence) by
                # sampling a Re-restricted complex grid — else s drifts to Re<1 and the tail
                # diverges (eval drops every point → a misleading undersampled skip).
                rec = constraints.get(v + ".re")
                if base == "C" and flag in ("impos", "imnonneg"):
                    # `0 < z.im` / `0 ≤ z.im` hypothesis → stay in the (open) upper half-plane,
                    # a strict subset of the stated domain (else the full ℂ grid false-FAILs)
                    grids.append((v, SAMPLES["H"]))
                elif base == "C" and flag == "imneg": # `z.im < 0` hypothesis → stay in the lower
                    grids.append((v, SAMPLES_H_NEG))  # half-plane (mirror of the impos fence)
                elif base == "C" and flag == "imaxis":   # `z.re = 0` → the imaginary axis
                    grids.append((v, SAMPLES_C_IMAXIS))
                elif base == "C" and flag == "unit":  # `‖z‖ < 1` hypothesis → interior of the unit
                    grids.append((v, SAMPLES_C_DISK)) # disk (else only 1 default point qualifies)
                elif base == "C" and flag == "heundisk":
                    # argument of a local-Heun Maclaurin sum on a row with no stated disc
                    # (DLMF 31.9.3/31.9.4) — the lens where `Hℓ(a,…;z)` AND its `1−z`
                    # companion both converge for the default `a` grid (SAMPLES_HEUN_DISK).
                    grids.append((v, SAMPLES_HEUN_DISK))
                elif base == "C" and isinstance(flag, tuple) and flag[0] == "trigdisk":
                    # `‖f(z)‖ < c` disc on a trig EXPRESSION (DLMF 15.4.8–16): small-modulus
                    # complex grid inside both |tan z| < 1 and |sin z| < 1 (the normexpr filter
                    # still drops anything outside the actual stated disc).
                    grids.append((v, SAMPLES_TRIG_DISK))
                elif base == "C" and isinstance(flag, tuple) and flag[0] == "cdisk":
                    # radius-c disk, sampled WELL inside (0.55·c) so a power series of radius c
                    # converges fast — points near the boundary (ratio→1) truncate at ~1e-13.
                    grids.append((v, [flag[1] * mp.mpf("0.55") * p for p in SAMPLES_C_DISK]))
                elif base == "C" and isinstance(flag, tuple) and flag[0] == "latdisk":
                    # `∀ m n : ℤ, ‖z‖ < ‖m + s + (n + t)τ‖` (theta power-series radius,
                    # DLMF 20.6.1/§20.6): z inside the MINIMAL shifted-lattice distance
                    # over the whole τ grid (τ carries `0 < τ.im` → SAMPLES["H"]), scaled
                    # 0.55 like cdisk, so every (z, τ) sample satisfies the hypothesis
                    # for every grid τ and the coefficient series settles fast. Sampling
                    # inside the stated domain only — no tolerance change.
                    s, t = flag[1], flag[2]
                    rmin = min(min(abs(mi + s + (ni + t) * tt)
                                   for mi in range(-3, 4) for ni in range(-3, 4)
                                   if abs(mi + s + (ni + t) * tt) > mp.mpf("1e-9"))
                               for tt in SAMPLES["H"])
                    grids.append((v, [rmin * mp.mpf("0.55") * p for p in SAMPLES_C_DISK]))
                elif base == "C" and rec == "gt1":
                    grids.append((v, SAMPLES_C_RE1))
                elif base == "C" and isinstance(rec, tuple) and rec[0] == "reupper":
                    # `z.re < c` strip (DLMF 15.8.22/23 Re z < 1/2): the default ℂ grid is
                    # almost all Re ≥ 1/2, so sample a curated in-strip spread; the per-sample
                    # 'reupper' filter remains the soundness guarantee.
                    grids.append((v, _re_upper_grid(rec[1])))
                elif base == "C" and rec == "ge1":
                    grids.append((v, SAMPLES_C_REGE1))
                elif base == "C" and rec == "pos":
                    grids.append((v, SAMPLES_C_REPOS))
                elif base == "C" and flag == "nonzero":
                    # a coexisting disc/wedge hypothesis on an EXPRESSION in v (e.g.
                    # hypergeometric_15_4_2's `‖z ^ 2‖ < 1` beside `z ≠ 0`) is invisible to
                    # the whole-plane nonzero grid, which then keeps at most one in-domain
                    # point and starves the row into `undersampled/domain`. Use the same
                    # rejection-built in-domain grid the unflagged branch below uses (it is
                    # returned ONLY when the default ℂ grid is genuinely starved), minus 0.
                    _nzg = _domain_reject_grid(v, constraints, binders)
                    grids.append((v, [p for p in _nzg if abs(p) > 0] if _nzg
                                  else SAMPLES_C_NONZERO))
                elif base == "C" and (_dg := _domain_reject_grid(v, constraints, binders)):
                    # a lower-norm / principal-arg-wedge / complex-centered-disk hypothesis
                    # (DLMF 15.8.32/15.8.33) that the default ℂ grid entirely misses — sample a
                    # curated set rejection-built INSIDE the stated domain, so the row is exercised
                    # rather than dropped as undersampled (the normlow/argwedge/normexpr filters
                    # remain the soundness guarantee; this only supplies in-domain points).
                    grids.append((v, _dg))
                else:
                    grids.append((v, SAMPLES[base]))
            elif base == "zmod":               # a : ZMod k — small element values (incl. a=1)
                grids.append((v, _f(1, 2, 3)))
            elif flag == "modulus":            # k of a `ZMod k` / DirichletCharacter — cyclic moduli
                grids.append((v, _f(5, 7, 9, 11)))
            elif base == "Z" and flag is None and v in w3j_jvars:
                # Wigner 3j physical window: jᵢ from small NONNEGATIVE integers (the
                # default ℤ grid never pairs with a satisfiable magnetic window here)
                grids.append((v, _f(0, 1, 2, 3)))
            elif base == "Z" and flag is None and v in w3j_mvars:
                # Wigner 3j physical window: mᵢ from a small SYMMETRIC grid, fenced per
                # combo to |mᵢ| ≤ jᵢ before the cap (see the combo filter below)
                grids.append((v, _f(-2, -1, 0, 1, 2)))
            elif base in ("Z", "N"):
                g = _int_grid(flag, base)
                # a function-witness row (wmap: the f(n) = ∏_p f(p^{a_p}) shapes,
                # DLMF 27.3.2/27.3.10) is substantively exercised only at n with ≥ 2
                # DISTINCT prime factors — the default small grid is all 1/primes/prime
                # powers, where both sides of 27.3.2 are literally the same term.
                # ADDITIVE: extra composite points strictly inside the stated domain
                # (only for flags that admit composites); no point removed, nothing
                # loosened.
                if wmap and base == "N" and flag in (None, "nonzero", "pos", "ge1", "nonneg"):
                    g = list(g) + _f(6, 12, 30)
                # compose a coexisting order hypothesis on the SAME variable (e.g. the
                # `hlt : 1 < n` alongside a shape flag `h_odd : Odd n`, DLMF 24.2 odd-
                # Bernoulli vanishing — see _binders' shape-flag guard) — else the shape
                # grid alone can include points the order hypothesis excludes (n=1).
                g = _filter_int_bounds(v, g, constraints)
                grids.append((v, g))
            else:
                grids.append((v, _filter_lower(v, _filter_upper(v, _real_grid(flag), constraints), constraints)))
    # A variable carrying SEVERAL domain hypotheses keeps only the grid-shaping one in
    # cons[v] (see _add_flag); enforce the rest pointwise so the sample stays inside the
    # CONJUNCTION of the stated hypotheses. No-op for every single-hypothesis variable.
    if (constraints or {}).get('_flags'):
        grids = [(v, _filter_extra_flags(v, g, constraints)) for v, g in grids]
    # Single-variable norm/wedge hypotheses applied to the OWN grid before the 24-combo cap
    # (see _filter_domain_pairs): on a wide product the cap windows only the last variables,
    # so an out-of-hypothesis leading value starves the row even though `_pairs_ok` would have
    # accepted points further along. Restriction to the stated domain only; nothing loosened.
    grids = _filter_domain_pairs(grids, binders, constraints)
    # angular-momentum structured envs (selection-rule-valid tuples) take precedence over the
    # generic cartesian grid for Wigner/CG/Racah rows; else cartesian product, capped.
    if not free:                          # `f = g` (no explicit argument) — eta-expand & sample
        fe = _func_eq(L, R)
        if fe is not None:
            return fe
    am_envs = _angmom_envs(L, R, free)
    import itertools
    nz_scored_cap = None                  # set when strided supplements are appended below
    if am_envs is not None:
        sample_envs = am_envs
    else:
        # DE-COINCIDENCE (additive, coverage-only): when ≥2 free COMPLEX parameters draw from
        # the SAME shared grid, the cap-24 cartesian window is saturated by coincident tuples
        # (a=b, or c∈{a,b}) — for a connection formula carrying a sin(π(b−a)) prefactor and
        # Γ(c−a)/Γ(c−b) denominators (DLMF 15.8.2/15.8.3) EVERY in-cap point is then either a
        # trivial 0=0 (a=b zeroes the prefactor) or a dropped Γ(0) pole (c=a / c=b), so the row
        # skips as trivial-zero/unexercised though the identity holds off the diagonal (verified
        # to 1e-29, docs/verification/ch15/probe_15_8_2.py). Rotate each complex var's grid by a
        # distinct offset. This is a PERMUTATION of that variable's OWN grid — it introduces NO
        # new sample value (so a domain-restricted argument z stays within its in-domain point
        # set) and changes no tolerance/gate; it only de-correlates the product so the window
        # contains non-coincident tuples. The full cartesian set is unchanged; only which 24 the
        # cap selects moves, and every selected point still runs the whole filter/pole/TOL chain,
        # so a false identity still FAILs. Scoped to ≥2 complex vars — the exact coincidence
        # condition — leaving integer/real grids (small-value base cases) untouched.
        _cvars = [i for i, g in enumerate(grids) if binders.get(g[0]) in ("C", "H")]
        if len(_cvars) >= 2:
            for j, i in enumerate(_cvars):
                v, gr = grids[i]
                gr = list(gr)
                if len(gr) > 1:
                    r = j % len(gr)
                    grids[i] = (v, gr[r:] + gr[:r])
        names = [g[0] for g in grids]
        if grids:
            combo_iter = itertools.product(*[g[1] for g in grids])
            # honor plain integer/order pair hypotheses (a ≤ b, a < b, a + k ≤ b, a + k < b)
            # BEFORE the 24-combo cap: on a same-grid product (e.g. Krawtchouk's (N, n) with
            # hN : n + 2 ≤ N, DLMF 18.22.3) the raw cap can be exhausted entirely by
            # out-of-hypothesis pairs, starving the row into `undersampled` even though
            # in-domain points exist further along. Filtering first only reorders which
            # IN-HYPOTHESIS combos survive the cap; nothing loosened, cap unchanged.
            order_pairs = [q for q in (constraints or {}).get('_pairs', [])
                           if q[0] in ('lepair', 'ltpair', 'lepairoff', 'ltpairoff')]
            if order_pairs:
                combo_iter = (c for c in combo_iter
                              if _pairs_ok(dict(zip(names, c)), {'_pairs': order_pairs}))
            # Wigner 3j physical window |mᵢ| ≤ jᵢ, applied BEFORE the cap (else the cap
            # is exhausted by out-of-window combos where the symbol is identically zero
            # and the row starves). Active only when a sumzero pin fired (above); cap
            # unchanged, nothing loosened.
            _w3j_win = [(m, j) for m, j in w3j_mwin if j is not None]
            if _w3j_win:
                def _w3j_window_ok(combo):
                    d = dict(zip(names, combo))
                    return all(abs(d[m]) <= d[j] for m, j in _w3j_win
                               if m in d and j in d)
                combo_iter = (c for c in combo_iter if _w3j_window_ok(c))
            # reorder feasibility (DLMF 15.6.8/9 Re c > Re d > 0), applied BEFORE the cap:
            # the constructive real-part ordering pin needs Re c > 0, but the de-correlating
            # grid rotation can leave c's LEADING value at Re ≤ 0, so the first-24 window
            # would be exhausted entirely by infeasible c (→ every point drops in-loop →
            # undersampled). Filtering first only reorders which IN-DOMAIN combos survive the
            # cap; nothing loosened, cap unchanged.
            _reord_c = [cv for (_dd, cv) in (constraints or {}).get('_reorder', [])]
            if _reord_c:
                combo_iter = (c for c in combo_iter
                              if all(mp.re(d) > 0 for cv, d in zip(names, c) if cv in _reord_c))
            if _diversify:
                # trivial-zero retry (see the skip site below): stride the SAME product so
                # every variable — not just the last two or three — sweeps its own grid.
                _tot = 1
                for _gv, _gg in grids:
                    _tot *= max(1, len(_gg))
                _step = max(1, min(_tot, _DIVERSIFY_POOL) // 24)
                combos = list(itertools.islice(combo_iter, 0, _DIVERSIFY_POOL, _step))[:24]
            else:
                combos = list(itertools.islice(combo_iter, 24))
        else:
            combos = [()]
        sample_envs = [dict(zip(names, combo)) for combo in combos]
    # CONSTRUCTIVE triangle-violation sampling (ADDITIVE): a `sumlt` hypothesis a + b < c is
    # otherwise honored only by rejection in _pairs_ok, so when no grid/curated env happens
    # to satisfy it the row starves into `undersampled` even though the hypothesis domain is
    # plainly non-empty — the curated _6J_TUPLES violate only the FIRST and FOURTH wigner6j
    # triads, so wigner6j_eq_zero_of_triangle₂ (j₁+l₂<l₃) and ₃ (l₁+j₂<l₃) never got a clean
    # sample. Supplement with envs built INSIDE the hypothesis: keep the other five entries
    # of a sampled env and set c := a + b + k for k ∈ {1..4} (when c is a free integer
    # binder; else symmetrically solve for a or b, dropping an ℕ binder that would go
    # negative). Supplements still pass through the FULL per-sample filter chain below
    # (_pairs_ok with every other hypothesis, junk-value deferrals, pole guard) — sampling
    # restricted to the stated hypothesis domain only; no tolerance or scoring change.
    _sumlt_extra = []
    for _q in (constraints or {}).get('_pairs', []):
        if _q[0] != 'sumlt':
            continue
        _sa, _sb, _sc = _q[1], _q[2], _q[3]
        for _e in sample_envs[:2]:
            for _k in (1, 2, 3, 4):
                if _sc in free and binders.get(_sc) in ('N', 'Z') \
                        and _sa in _e and _sb in _e:
                    _e2 = dict(_e); _e2[_sc] = _e[_sa] + _e[_sb] + _k
                elif _sa in free and binders.get(_sa) in ('N', 'Z') \
                        and _sb in _e and _sc in _e:
                    _va = _e[_sc] - _e[_sb] - _k
                    if binders.get(_sa) == 'N' and _va < 0:
                        continue
                    _e2 = dict(_e); _e2[_sa] = _va
                elif _sb in free and binders.get(_sb) in ('N', 'Z') \
                        and _sa in _e and _sc in _e:
                    _vb = _e[_sc] - _e[_sa] - _k
                    if binders.get(_sb) == 'N' and _vb < 0:
                        continue
                    _e2 = dict(_e); _e2[_sb] = _vb
                else:
                    continue
                _sumlt_extra.append(_e2)
        # REAL-binder companion (ADDITIVE): solve the sumlt hypothesis with small
        # FRACTIONAL slacks instead of integer ones — e.g. the DLMF 15.10.21 coefficient
        # identity's (a, b, c) window `0 < b < c < 1`, `a + b < c`, `c < a + 1`, where
        # the default real grid meets the hypotheses at a single point and the row
        # starves. Supplements pass the FULL per-sample filter chain like every other
        # env; sampling restricted to the stated hypothesis domain only.
        for _e in sample_envs[:2]:
            for _k in (mp.mpf("0.1"), mp.mpf("0.2"), mp.mpf("0.35"), mp.mpf("0.45")):
                if _sa in free and binders.get(_sa) == 'R' and _sb in _e and _sc in _e:
                    _e2 = dict(_e); _e2[_sa] = mp.re(_e[_sc]) - mp.re(_e[_sb]) - _k
                    _sumlt_extra.append(_e2)
                elif _sc in free and binders.get(_sc) == 'R' and _sa in _e and _sb in _e:
                    _e2 = dict(_e); _e2[_sc] = mp.re(_e[_sa]) + mp.re(_e[_sb]) + _k
                    _sumlt_extra.append(_e2)
    if _sumlt_extra:
        sample_envs = list(sample_envs) + _sumlt_extra
    # expand each env over BOTH indicial roots (see indroot_pins above): ρ := 0 and
    # ρ := 1 − c per sample. A missing root operand leaves ρ unset — the point then
    # drops honestly in evaluate, never scored.
    if indroot_pins:
        _ir_envs = []
        for _e in sample_envs:
            _outs = [_e]
            for _v, _w in indroot_pins:
                _nxt = []
                for _x in _outs:
                    if _w not in _x:
                        _nxt.append(_x)
                        continue
                    _x0 = dict(_x); _x0[_v] = mp.mpf(0)
                    _x1 = dict(_x); _x1[_v] = 1 - _x[_w]
                    _nxt += [_x0, _x1]
                _outs = _nxt
            _ir_envs += _outs
        sample_envs = _ir_envs
    # SHAPE-SCOPED nested-quadrature budget (see _nested_quad_shape): an ∫/deriv over a
    # quad-defined head needs a full inner adaptive quadrature per outer node, so the
    # default 8 s per-sample budget times out on CORRECT values (bickleyKi_succ_eq /
    # deriv_bickleyKi_succ / iRepErfc_succ_eq, DLMF 10.43 / 7.18.2). Raise the budget
    # to 60 s and thin the grid.
    #
    # The critical remedy for the SLOW-kernel case (bickleyKi's K₀ decays only like e^{−t},
    # not the Gaussian e^{−t²} of iRepErfc): at the base order n=0 the inner head is
    # UN-nested (bickleyKi 0 = K₀, iRepErfc 0 = erfc) so the row is a single outer quad
    # (~1 s), but at n≥1 the RHS `∫ f(n,·)` is a DOUBLY-nested semi-infinite quad — measured
    # >120 s for bickleyKi, far past any per-sample budget, and one such _EvalTimeout aborts
    # the WHOLE row. So for the nested-quad shape, pin every integer binder to the cheapest
    # order present (its grid minimum, n=0): the recursion's first step is still checked
    # against an independent single quad across several x-samples. Sample-set/budget only;
    # tolerances, gates and settle windows unchanged, no other row shape touched.
    eval_budget = EVAL_BUDGET
    _expensive = _expensive_integrand_shape(L) or _expensive_integrand_shape(R)
    if _nested_quad_shape(L) or _nested_quad_shape(R) or _expensive:
        _ivars = {v for v, t in binders.items() if t in ("Z", "N")}
        _imins = {v: min(e[v] for e in sample_envs if v in e)
                  for v in _ivars if any(v in e for e in sample_envs)}
        if _imins:
            _cheap = [e for e in sample_envs
                      if all(e.get(v) == _imins[v] for v in _imins if v in e)]
            if _cheap:
                sample_envs = _cheap
        # For the expensive-integrand shape, keep only envs where the Re c > Re d > 0 ordering
        # pin is FEASIBLE (Re c > 0) BEFORE thinning, so the ≤3 kept samples are in-domain
        # (an infeasible env would only drop in-loop, starving the thinned set → undersampled).
        _ro = (constraints or {}).get('_reorder', [])
        if _expensive and _ro:
            _feas = [e for e in sample_envs
                     if all(cv not in e or mp.re(e[cv]) > 0 for (_dd, cv) in _ro)]
            if _feas:
                sample_envs = _feas
        _step = max(1, len(sample_envs) // 3)
        sample_envs = sample_envs[::_step][:3]
        eval_budget = _NESTED_QUAD_BUDGET
    # §15.5 iterated-operator rows (DLMF 15.5.3/5/7/8): cap the sampled operator ORDER so the
    # n=5 point of the default ℕ grid — a 5-fold nested mp.diff measured at ~11.5 s — no longer
    # blows the per-sample budget and false-skips a TRUE identity as `eval-timeout` (see
    # _ITEROP_MAX_ORDER). Keeping n ∈ {0,1,2,3} still exercises the nested operator non-trivially
    # (residual ≤ 1e-31, probe_ops.py). Sample-set only — tolerances/gates/settle windows fixed.
    if _iterop_shape(L) or _iterop_shape(R):
        _ivars = {v for v, t in binders.items() if t in ("Z", "N")}
        if _ivars:
            _kept = [e for e in sample_envs
                     if all(v not in e or mp.re(e[v]) <= _ITEROP_MAX_ORDER for v in _ivars)]
            if _kept:
                sample_envs = _kept
    # §15.10 principal-Gauss connection rows: rescue from the coincident-parameter Γ-pole
    # starvation of the coarse grid with curated distinct-parameter, off-cut envs (see the
    # _PRINCIPAL_GAUSS_ENVS note above). Fires ONLY when a principalGauss/principalW head is
    # present AND a,b,c,z are ℂ binders — so no other row shape is perturbed. Additive.
    if {"a", "b", "c", "z"} <= set(binders) \
            and all(binders.get(v) == "C" for v in ("a", "b", "c", "z")) \
            and (_mentions_any_head(L, _PRINCIPAL_GAUSS_HEADS)
                 or _mentions_any_head(R, _PRINCIPAL_GAUSS_HEADS)):
        sample_envs = list(sample_envs) + [dict(e) for e in _PRINCIPAL_GAUSS_ENVS]
    # §15.6 principalOlver vertical-line Mellin–Barnes rows (DLMF 15.6.6/15.6.7): the coarse ℂ
    # grid samples σ below max(−Re a,−Re b) and z on the principal cut — OFF the contour's
    # convergence sector, where the vertical-line rep is a different branch — so its scored points
    # are spurious FAILs. The sector hypotheses (a `max(…)(…) < σ` lower bound, InPrincipalGaussDomain,
    # GammaFinite) do not lift into per-sample filters, so those off-sector points cannot be dropped
    # by _pairs_ok. RESTRICT sampling to the curated strictly-in-sector envs (see _PRINCIPAL_MB_ENVS)
    # — mirroring the nested-quad grid restriction (~6250) and the iterop order filter (~6260). Fires
    # ONLY on a principalOlver head + a doubly-infinite integral + a real σ binder + ℂ a,b,c,z; the
    # biinf evaluator's own convergence gate still refuses any non-converging u-quadrature. Additive:
    # a correctly-transcribed Barnes rep PASSes at these in-sector points (rel≈1e-41,
    # probe_g1_mb.py), only a mis-transcribed one FAILs.
    if {"a", "b", "c", "z"} <= set(binders) \
            and all(binders.get(v) == "C" for v in ("a", "b", "c", "z")) \
            and binders.get("σ") == "R" \
            and (_has_biinf_integral(L) or _has_biinf_integral(R)) \
            and (_mentions_any_head(L, _PRINCIPAL_MB_HEADS)
                 or _mentions_any_head(R, _PRINCIPAL_MB_HEADS)):
        sample_envs = [dict(e) for e in _PRINCIPAL_MB_ENVS]
    # §15.4 bilateral Gamma-ratio Dougall sum (DLMF 15.4.25): restrict to curated in-domain envs
    # (see _BILATERAL_GAMMA_ENVS). The a,b-off-ℤ and 1<Re(c+d−a−b) hypotheses never lift into
    # per-sample filters and the coarse grid's small-Re(c+d−a−b) points never let the acceleration-
    # free bilateral partial sum settle → every point drops (undersampled). Fires ONLY on ℂ a,b,c,d
    # + a bilateral ℤ-sum head — no other row shape perturbed. Additive; nothing loosened.
    if {"a", "b", "c", "d"} <= set(binders) \
            and all(binders.get(v) == "C" for v in ("a", "b", "c", "d")) \
            and (_has_bilateral_zsum(L) or _has_bilateral_zsum(R)):
        sample_envs = [dict(e) for e in _BILATERAL_GAMMA_ENVS]
    # §5.9.11 / §5.9.17 Barnes-ζ vertical-line reps of Ln Γ(z+1) / ψ(z+1): restrict to curated
    # in-domain envs (see _BARNES_ZETA_ENVS). The 1<c<2 and z∈slitPlane hyps never lift into
    # per-sample filters, and the oscillatory ζ integrand stalls the infinite-line quad past the
    # 8 s budget (eval-timeout). Fires ONLY on z:ℂ + c:ℝ binders + a doubly-infinite integral +
    # a riemannZeta head — no other row shape (the Γ-only 5.13.1 has NO ζ head; the ζ-value
    # rows have no biinf integral). Additive; nothing loosened.
    if binders.get("z") == "C" and binders.get("c") == "R" \
            and (_has_biinf_integral(L) or _has_biinf_integral(R)) \
            and (_contains_head(L, {"riemannZeta"}) or _contains_head(R, {"riemannZeta"})):
        sample_envs = [dict(e) for e in _BARNES_ZETA_ENVS]
    # §5.13.1 Barnes 2-Γ vertical-line rep (1/2π)∫ Γ(s+a)Γ(b-s)z^{-s} dt: restrict to curated
    # in-sector envs (see _BARNES_2GAMMA_ENVS). The -Re a<c<Re b, 0<Re(a+b), z∈slitPlane hyps
    # never lift into per-sample filters, so the coarse ℂ grid samples off the Barnes contour
    # window → spurious FAIL → contour-sector-unverified (worst≈1.114). Fires ONLY on a,b,z:ℂ +
    # c:ℝ binders + a doubly-infinite integral + a Gamma head and NO riemannZeta head (the ζ
    # rows above have no a,b binders anyway). Additive; nothing loosened.
    if {"a", "b", "z"} <= set(binders) \
            and all(binders.get(v) == "C" for v in ("a", "b", "z")) \
            and binders.get("c") == "R" \
            and (_has_biinf_integral(L) or _has_biinf_integral(R)) \
            and (_contains_head(L, {"Gamma"}) or _contains_head(R, {"Gamma"})) \
            and not (_contains_head(L, {"riemannZeta"}) or _contains_head(R, {"riemannZeta"})):
        sample_envs = [dict(e) for e in _BARNES_2GAMMA_ENVS]
    # §5.13.4 Ramanujan reciprocal-Γ real integral ∫_ℝ dt/(Γ(a+t)Γ(b+t)Γ(c-t)Γ(d-t)): restrict
    # to curated high-sum envs (see _RAMANUJAN_RECIP_ENVS). The a+b+c+d>3 hyp lifts (sumgt), but
    # the coarse grid samples sums just above 3 where the |t|^{2-Σ} tail never settles
    # (undersampled/domain). Fires ONLY on a,b,c,d:ℝ + a doubly-infinite integral + a Real.Gamma
    # head + the sumgt constraint on {a,b,c,d}. Additive; nothing loosened.
    if {"a", "b", "c", "d"} <= set(binders) \
            and all(binders.get(v) == "R" for v in ("a", "b", "c", "d")) \
            and (_has_biinf_integral(L) or _has_biinf_integral(R)) \
            and (_contains_head(L, {"Gamma"}) or _contains_head(R, {"Gamma"})) \
            and any(p and p[0] == "sumgt" and set(p[1]) == {"a", "b", "c", "d"}
                    for p in (constraints or {}).get("_pairs", [])):
        sample_envs = [dict(e) for e in _RAMANUJAN_RECIP_ENVS]
    # §15.14.1 Mellin transform of Olver's 𝐅 on the negative axis (DLMF 15.14.1): restrict to
    # curated in-STRIP envs (see _OLVER_MELLIN_ENVS). The strip hypotheses 0 < Re s < min(Re a,
    # Re b) never lift into per-sample filters, so the coarse ℂ grid samples s outside the strip
    # (ray integral diverges → point drops → undersampled). Fires ONLY on a principalOlver head +
    # a right-ray integral + ℂ a,b,c,s — the DLMF 15.6 vertical-line rows have a σ:R binder + a
    # DOUBLY-infinite integral and take the _PRINCIPAL_MB_ENVS branch above, never this one.
    # Additive; nothing loosened.
    if {"a", "b", "c", "s"} <= set(binders) \
            and all(binders.get(v) == "C" for v in ("a", "b", "c", "s")) \
            and (_has_ray_integral(L) or _has_ray_integral(R)) \
            and not (_has_biinf_integral(L) or _has_biinf_integral(R)) \
            and (_mentions_any_head(L, _PRINCIPAL_MB_HEADS)
                 or _mentions_any_head(R, _PRINCIPAL_MB_HEADS)):
        sample_envs = [dict(e) for e in _OLVER_MELLIN_ENVS]
    # §15.15.1 expansion of 𝐅(a,b;c;1/z) about 1/z₀ (DLMF 15.15.1): restrict to curated
    # LARGE-MARGIN in-convergence-domain envs (see _GAUSS_1515_ENVS). The convergence hypothesis
    # max(|z₀|,|z₀−1|) < |z−z₀| is an underscore binder that never lifts into a per-sample filter,
    # so the coarse ℂ grid samples z OUTSIDE the domain → divergent series → acceleration-hang
    # eval-timeout. Fires ONLY on ℂ a,b,c,z + a ℂ z₀ binder + BOTH the olverHypergeometric and
    # principalOlver heads (the §15.15.1 signature) — no ray/biinf integral, so it never overlaps
    # the §15.6/15.14 Barnes branches above. Additive; the series' own settle-window gate decides.
    if {"a", "b", "c", "z", "z₀"} <= set(binders) \
            and all(binders.get(v) == "C" for v in ("a", "b", "c", "z", "z₀")) \
            and (_mentions_any_head(L, {"olverHypergeometric"})
                 or _mentions_any_head(R, {"olverHypergeometric"})) \
            and (_mentions_any_head(L, {"principalOlver"})
                 or _mentions_any_head(R, {"principalOlver"})):
        sample_envs = [dict(e) for e in _GAUSS_1515_ENVS]
    # §5.9.5 analytic-continuation Γ integral (DLMF 5.9.5): restrict to curated in-window envs
    # (see _GAMMA595_ENVS). The −n−1<x<−n order hypotheses are not recorded as constraints, so the
    # default (n, x) grid almost never lands in the thin window → undersampled/domain. Fires ONLY
    # on the exact {n:N, x:R} binder shape with the Γ = ray-integral-of-(exp − Taylor) structure.
    # Additive; the ray evaluator's tail-exponent + quadrature-error gates still decide each point.
    if set(binders) == {"n", "x"} and binders.get("n") == "N" and binders.get("x") == "R" \
            and _is_gamma595_shape(L, R):
        sample_envs = [dict(e) for e in _GAMMA595_ENVS]
    # gate selection: inline `deriv`/formal `derivative` → mp.diff finite-difference error;
    # a weighted measure integral → tanh-sinh quadrature over an endpoint-singular weight
    # carries ~1e-17, far above the exact gate. Pick the loosest tolerance that applies.
    tol = _eq_tol(L, R)
    worst, ok_pts, maxmag, best = mp.mpf(0), 0, mp.mpf(0), None
    unbound_head = None                    # an "unbound head" raised by evaluate is the TRUE
    intvars = {v for v, t in binders.items() if t in ("Z", "N")}   # skip reason (head-only,
    periodvars = [v for v, t in binders.items() if t == "latticept"]   # sample-independent)
    for env in sample_envs:
        env = dict(env)                    # samples are already mpf/mpc
        env["_intvars"] = intvars
        env["_binders"] = binders
        env["_zmodmod"] = (constraints or {}).get('_zmodmod', {})   # a : ZMod k → its modulus k
        if "W" in env and "L" in env:      # W : WeierstrassZetaSigma L — same lattice
            env["W"] = env["L"]
        for pv in periodvars:              # l ∈ L.lattice — a genuine period (ω₁ of this L)
            if "L" in env:
                env[pv] = env["L"].w1
        # defining-equality constructive pin (DLMF 15.8.32 ζ = e^{2πi/3}(1−z)/(z−e^{4πi/3})):
        # compute ζ := f(z) from its stated value, so the identity is scored at the ζ the
        # hypothesis fixes — never an independently-sampled ζ. A missing operand or an
        # eval failure leaves the point to drop honestly below, never scored.
        _defeq_skip = False
        for _dv, _dast in defeq_pins:
            try:
                env[_dv] = evaluate(_dast, env)
            except Exception:
                _defeq_skip = True
                break
        if _defeq_skip:
            continue
        # scalar-Prop-CARRIER constructive pin ('_linpin'): solve the carrier's own
        # equation `L = R` for its pin variable at this env.  The equation is affine in
        # that variable in every admissible case, so two probe evaluations give the exact
        # root; the root is then SUBSTITUTED BACK and the residual re-checked against the
        # SAME parsed equation.  A degenerate slope, a non-affine equation, a complex root
        # for a real binder, or any evaluation failure drops the point honestly — never a
        # value that violates the stated hypothesis, and never a loosened gate.
        _lin_skip = False
        for _lv, _lL, _lR, _lbase, _ in linpins:
            try:
                _e0, _e1 = dict(env), dict(env)
                _e0[_lv], _e1[_lv] = mp.mpc(0), mp.mpc(1)
                _g0 = mp.mpc(evaluate(_lL, _e0)) - mp.mpc(evaluate(_lR, _e0))
                _g1 = mp.mpc(evaluate(_lL, _e1)) - mp.mpc(evaluate(_lR, _e1))
                _slope = _g1 - _g0
                if abs(_slope) < mp.mpf("1e-8"):
                    _lin_skip = True
                    break
                _root = -_g0 / _slope
                _ev = dict(env)
                _ev[_lv] = _root
                _res = mp.mpc(evaluate(_lL, _ev)) - mp.mpc(evaluate(_lR, _ev))
                _scale = 1 + abs(_root) + abs(_g0)
                if abs(_res) > mp.mpf("1e-20") * _scale:
                    _lin_skip = True
                    break
                if _lbase == "R":
                    if abs(_root.imag) > mp.mpf("1e-20") * _scale:
                        _lin_skip = True
                        break
                    _root = mp.mpf(_root.real)
                env[_lv] = _root
            except Exception:
                _lin_skip = True
                break
        if _lin_skip:
            continue
        # resolve finvecC vector binders (A/B : Fin q → ℂ, meijerG_eq_pFq) to concrete
        # `.q`-tagged callables, now that their cardinality q and any coupled binder
        # are sampled. Constructed to satisfy the row's OWN parsed hypotheses BY
        # CONSTRUCTION, never by search:
        #   '_finvecgt'[v] = lo  →  Re(v_i) = env[lo] + 1 + i/2 > env[lo]   (∀ i, σ < Re Aᵢ)
        #   v ∈ '_finvecavoidnat' →  Re(v_j) = 1.37 + 0.53j, never an integer, so
        #     (k:ℂ) ≠ -v_j for every k : ℕ (plus a nonzero imaginary part, belt-and-braces).
        # A vector with NEITHER parsed hypothesis (so no sound witness is derivable) or a
        # missing q/lower-bound binder leaves the point to drop honestly in evaluate —
        # never a fabricated callable.
        # BALANCED finvec pair (DLMF 5.8.4/5.8.5 equal-sum side condition ∑ⱼaⱼ = ∑ⱼbⱼ): build
        # the two equal-cardinality vectors DISTINCT and off the nonpositive integers (nonzero
        # imaginary parts ⇒ Γ finite and (k:ℂ)≠−vⱼ for every k:ℕ), then pin the LAST bⱼ so
        # ∑b=∑a EXACTLY. This is the exact convergence hypothesis of the ratio product
        # ∏ₖ∏ⱼ(aⱼ+k)/(bⱼ+k); a≠b whenever the dimension is ≥2 (a 1-vector balance forces a=b),
        # so the check is non-vacuous, and it is validated against the independent Γ-ratio RHS
        # (∏ⱼΓ(bⱼ)/Γ(aⱼ)) at rel ≤ 1e-28 (docs/verification/resolve-surfaces/probe_n5k.py) so a
        # misidentified pairing can only skip/FAIL, never fabricate a PASS.
        bal = (constraints or {}).get('_finvecbalance')
        bal_done = set()
        if bal and bal[0] in finvecdim and bal[1] in finvecdim \
                and finvecdim[bal[0]] in env and bal[0] in env and bal[1] in env:
            va, vb = bal
            qn = int(env[finvecdim[va]])
            avals = [mp.mpc(mp.mpf("1.37") + mp.mpf(idx) * mp.mpf("0.53"),
                            mp.mpf("0.29") + mp.mpf(idx) * mp.mpf("0.17")) for idx in range(qn)]
            bvals = [mp.mpc(mp.mpf("2.11") + mp.mpf(idx) * mp.mpf("0.61"),
                            mp.mpf("0.41") + mp.mpf(idx) * mp.mpf("0.13")) for idx in range(qn)]
            if qn >= 1:
                bvals[-1] = bvals[-1] + (sum(avals) - sum(bvals))    # close ∑b = ∑a exactly
            env[va] = _finvec_callable(avals)
            env[vb] = _finvec_callable(bvals)
            bal_done = {va, vb}
        # REAL Fin-vector construction ('_finvecRdim'): distinct arithmetic progressions,
        # one per vector (offset by the vector's rank in name order), so no two entries of
        # DIFFERENT vectors coincide — the DLMF 31.15.12 weight has |z_j − a_k| in a
        # negative-capable rpow exponent, and a coincidence would hit Mathlib's 0-power junk
        # branch on one side only. A negative sampled dimension (n = N − 1 at N = 0) raises
        # and drops the point honestly.
        _fvr_skip = False
        for _t, _nm in enumerate(sorted(_fvr)):
            try:
                _qn = int(evaluate(_fvr_dims[_nm][0], env))
            except Exception:
                _fvr_skip = True
                break
            if _qn < 0:
                _fvr_skip = True
                break
            env[_nm] = _finvec_callable(
                [mp.mpf("0.37") + mp.mpf(i) * mp.mpf("0.61") + mp.mpf(_t) * mp.mpf("1.13")
                 for i in range(_qn)])
        if _fvr_skip:
            continue
        finvec_skip = False
        for fv, dimv in finvecdim.items():
            if fv in bal_done:
                continue
            if fv not in env or dimv not in env:
                continue
            qn = int(env[dimv])
            lo = (constraints or {}).get('_finvecgt', {}).get(fv)
            if lo is not None and lo in env:
                base_re = env[lo]
                vals = [mp.mpc(base_re + 1 + mp.mpf(idx) / 2,
                               mp.mpf("0.3") + mp.mpf(idx) * mp.mpf("0.2"))
                        for idx in range(qn)]
            elif fv in (constraints or {}).get('_finvecavoidnat', ()):
                vals = [mp.mpc(mp.mpf("1.37") + mp.mpf(idx) * mp.mpf("0.53"),
                               mp.mpf("0.29") + mp.mpf(idx) * mp.mpf("0.17"))
                        for idx in range(qn)]
            elif not (constraints or {}).get('_finvecgt'):
                # UNCONSTRAINED ₚFᵩ parameter tuple (DLMF 16.2.1 `pFq_hasSum` in the p ≤ q
                # everywhere-convergent regime): the series/identity holds for ALL parameters,
                # so a generic pole-avoiding complex tuple (same non-integer real parts as the
                # avoid-nat construction) is a sound witness. SUPPRESSED whenever the row carries
                # a Mellin–Barnes abscissa hypothesis (`_finvecgt`, meijerG_eq_pFq) — there the
                # `σ < Re Aᵢ` contour constraint is mandatory and an unconstrained vector still
                # drops honestly below.
                # Each vector of a MULTI-vector row gets its own offset `t` (the row's finvec
                # binders in name order), so distinct vectors are genuinely DISTINCT: with one
                # shared construction `a = γ = q` and a row like DLMF 31.14.5
                # (γⱼγₖ/(aⱼ−aₖ) − qⱼ) could not tell its three vectors apart — a hollow PASS.
                # Real parts stay non-integer and imaginary parts nonzero (Γ finite, and
                # (k:ℂ) ≠ −vⱼ for every k : ℕ), so the witness is exactly as generic as before.
                _t = sorted(finvecdim).index(fv)
                vals = [mp.mpc(mp.mpf("1.37") + mp.mpf(idx) * mp.mpf("0.53")
                               + mp.mpf(_t) * mp.mpf("1.9"),
                               mp.mpf("0.29") + mp.mpf(idx) * mp.mpf("0.17")
                               - mp.mpf(_t) * mp.mpf("0.41"))
                        for idx in range(qn)]
            else:
                finvec_skip = True
                break
            env[fv] = _finvec_callable(vals)
        if finvec_skip:
            continue
        # ── hypothesis-CARRIER pin: build this sample INSIDE the stated carrier ──────────
        # The registry entry may first supply its own Fin-vector data ('vectors'): the
        # shared unconstrained construction is deliberately generic, and DLMF 31.14.2's two
        # relations (α+β+1 = Σγⱼ, αβ = Σaⱼqⱼ) need the three vectors to be genuinely
        # different to be told apart. Then 'pin' solves the display for the binders it
        # determines. Any failure (a degenerate sample outside the carrier's domain) drops
        # the point honestly — never a fabricated value, never a loosened gate.
        if _cspec is not None:
            try:
                _vecs = _cspec.get("vectors")
                if _vecs is not None:
                    _dimv = next(finvecdim[nm] for nm, kd in zip(_cargs, _cspec["kinds"])
                                 if kd == "finvecC" and nm in finvecdim)
                    _built = _vecs(int(env[_dimv]))
                    _vi = 0
                    for nm, kd in zip(_cargs, _cspec["kinds"]):
                        if kd == "finvecC":
                            env[nm] = _finvec_callable(_built[_vi])
                            _vi += 1
                _pinned = _cspec["pin"]([env.get(nm) for nm in _cargs])
                for _slot, _val in zip(_cspec["solves"], _pinned):
                    env[_cargs[_slot]] = _val
            except Exception:
                continue
        # magnetic selection rule m₁+m₂+m₃ = 0 ('sumzero'), solved constructively:
        # the dropped binder c is pinned to −(a+b), the unique value the stated
        # hypothesis allows. Never overrides a structured _angmom_envs assignment
        # (c already in env there); a missing operand leaves c unset — the point
        # then drops honestly in evaluate, never scored.
        for _c, _a, _b in sumzero_pins:
            if _c not in env and _a in env and _b in env:
                env[_c] = -(env[_a] + env[_b])
        # real-part ordering pin (DLMF 15.6.8/9): set Re d to a strict-interior fraction of
        # Re c so 0 < Re d < Re c holds by construction (keeping d's sampled imaginary part);
        # if Re c ≤ 0 the ordering is infeasible → drop the point, never fabricate an
        # out-of-domain (divergent-integral) sample.
        _reorder_skip = False
        for _dv, _cv in reorder_pins:
            if _cv in env and _dv in env:
                _rc = mp.re(env[_cv])
                if _rc <= 0:
                    _reorder_skip = True
                    break
                env[_dv] = mp.mpc(_rc * mp.mpf("0.4"), mp.im(env[_dv]))
        if _reorder_skip:
            continue
        # χ : DirichletCharacter ℂ k — resolve the sampled index t to the t-th CONCRETE
        # character mod the sampled k (ob._dirichlet_char_sample, self-anchored to the DLMF
        # 27.8.1–27.8.4 defining relations). Modulus missing or (ℤ/kℤ)* non-cyclic → the
        # sample drops honestly (never a fabricated character).
        dch_skip = False
        for dv, kv in (constraints or {}).get('_dirchmod', {}).items():
            if dv in env:
                chi = ob._dirichlet_char_sample(env.get(kv), env[dv])
                if chi is None:
                    dch_skip = True
                    break
                env[dv] = chi
        if dch_skip:
            continue
        # concrete `{χ : MulChar (ZMod p) ℂ}` / `{e : AddChar (ZMod p) ℂ}` binders
        # ('_zmodchar', the DLMF §27.8 Gauss-sum magnitude surface): resolve the sampled
        # character INDEX to a concrete character mod the SAME sampled p —
        # ob._mulchar_sample / ob._addchar_sample, self-anchored in oracle_bindings.verify()
        # to the DLMF 27.8.1–27.8.4 / 27.10.9 defining relations (χ(1)=1, complete
        # multiplicativity, period, vanishing off units; ψ(0)=1, additivity, ψ₁(1)=e^{2πi/p}).
        # Hypotheses honored per sample, never loosened, via the samplers' brute-force-
        # anchored tags: `hχ : χ ≠ 1` drops a `.principal` character sample; `he :
        # e.IsPrimitive` drops a non-`.primitive` kernel. Missing modulus or non-cyclic
        # (ℤ/pℤ)* → the sample drops honestly (never a fabricated character).
        zc_skip = False
        for cv, kv in (constraints or {}).get('_zmodchar', {}).items():
            if cv not in env or callable(env[cv]):
                continue
            kval = env.get(kv)
            if kval is None or int(kval) < 1:
                zc_skip = True
                break
            idx = int(env[cv])
            if binders.get(cv) == "addchar":
                psi = ob._addchar_sample(kval, idx)
                if cv in (constraints or {}).get('_primchar', ()) \
                        and not getattr(psi, "primitive", False):
                    zc_skip = True             # hypothesis e.IsPrimitive: a non-primitive
                    break                      # ψₙ is outside the stated domain — never scored
                env[cv] = psi
            else:
                chi = ob._mulchar_sample(kval, idx)
                if chi is None:
                    zc_skip = True
                    break
                if ['distinct', cv, '1'] in (constraints or {}).get('_pairs', []) \
                        and getattr(chi, "principal", False):
                    zc_skip = True             # hypothesis χ ≠ 1: the principal character
                    break                      # is outside the stated domain — never scored
                env[cv] = chi
        if zc_skip:
            continue
        # ψ : AddChar R R' — resolve the sampled kernel index n to the concrete additive
        # character ψₙ(x) = e^{2πinx/k} on the SAME ring as the sampled χ (k = the
        # .modulus tag of the mulchar sample, so `gaussSum χ ψ` is the genuine DLMF
        # 27.10.9 pairing). No mulchar modulus in scope → the sample drops honestly.
        ach_skip = False
        for av in (v for v, t in binders.items() if t == "addchar"):
            if av in env and not callable(env[av]):
                kmod = next((getattr(env[mv], "modulus") for mv, mt in binders.items()
                             if mt == "mulchar" and mv in env
                             and hasattr(env.get(mv), "modulus")), None)
                if kmod is None:
                    ach_skip = True
                    break
                env[av] = ob._addchar_sample(kmod, env[av])
        if ach_skip:
            continue
        if not _pairs_ok(env, constraints):
            continue
        if not _bool_nonzero_ok(env, constraints):
            continue                       # a hypothesized-nonzero expr vanishes here (0/0 point).
                                           # ZMod-AWARE (`_bool_nonzero_ok`, same filter as the
                                           # bool-iff path): `ha : (a : ZMod p) ≠ 0` vanishes
                                           # exactly when p ∣ a — the plain ℤ-lift gate cannot
                                           # see that (the lift 5 is nonzero while (5 : ZMod 5)
                                           # = 0), and scoring such an out-of-hypothesis point
                                           # compares Lean's junk-value branch (fabricated a
                                           # Gauss's-lemma FAIL at p = a ∈ {3,5}, DLMF 27.9).
                                           # Non-ZMod entries defer to `_nonzero_ok` unchanged.
        if _tonat_negative(L, env) or _tonat_negative(R, env):
            continue                       # defer the .toNat phase-clamp bug regime (ERRATA)
        if _natsub_negative(L, env) or _natsub_negative(R, env):
            continue                       # defer the Nat truncated-subtraction boundary point
                                           # (Lean `2*n−1 = 0` at n=0 vs the evaluator's −1)
        try:                               # series memory-safety is enforced in _bounded_nsum
            with _time_limit(eval_budget):   # = EVAL_BUDGET except the nested-quad shape
                a, b = evaluate(L, env), evaluate(R, env)
        except _EvalTimeout:               # row too costly (nested quad) → honest skip
            return (UNABLE, "eval-timeout")
        except Unparseable as e:
            unbound_head = unbound_head or _unbound_head_of(e)
            continue
        except (ZeroDivisionError, ValueError, OverflowError):
            continue
        except Exception:
            continue
        if zmod_tok is not None:
            # ZMod-n congruence scoring: reduce the two ℤ-lifts mod the sampled n. Both
            # sides must be exact integers and n ≥ 2 — else the point drops honestly
            # (n ∈ {0,1} is a degenerate/trivial ring; a non-integer lift means the ℤ-lift
            # model does not cover this operand, e.g. a ZMod inverse). gap ∈ {0, 1} keeps
            # the usual worst<tol PASS gate exact: one incongruent sample FAILs the row.
            nv = env.get(zmod_tok) if not zmod_tok.isdigit() else mp.mpf(int(zmod_tok))
            nn = _near_int(nv) if nv is not None else None
            ia, ib = _near_int(a), _near_int(b)
            if nn is None or nn < 2 or ia is None or ib is None:
                continue
            ok_pts += 1
            maxmag = max(maxmag, abs(a), abs(b))
            gap = mp.mpf(0) if (ia - ib) % nn == 0 else mp.mpf(1)
            worst = max(worst, gap)
            best = gap if best is None else min(best, gap)
            continue
        # POLE-DEGENERACY guard (ADDITIVE, no tolerance change): an operand magnitude beyond
        # POLE_MAG at dps=30 means the sample landed ON a pole — e.g. cs_neg_left on the
        # z = τ lattice-coincident diagonal, where sn(z,τ) is the dps-30 roundoff of an exact
        # zero (|sn| ≈ 6.6e-32) so cs = cn/sn ≈ 1.5e31 is cancellation noise with zero correct
        # digits (residual rel ≈ 1.8e-12 vs ≤ 1.8e-43 on the 11 clean grid points). Gating
        # noise can false-FAIL a true identity; dropping the point cannot fabricate a PASS —
        # the row must still clear TOL on ≥ 2 clean samples, else it skips as undersampled.
        if max(abs(a), abs(b)) > POLE_MAG:
            continue
        ok_pts += 1
        maxmag = max(maxmag, abs(a), abs(b))
        # residual RELATIVE to operand scale: Γ(19.2) ≈ 6e16 computed to 30 significant
        # digits carries an ABSOLUTE error ~1e-15 — gating absolutely would FAIL the (true)
        # Gauss multiplication formula on magnitude alone. max(1,·) keeps O(1) identities
        # gated exactly as before.
        rel_gap = abs(a - b) / max(mp.mpf(1), abs(a), abs(b))
        # CATASTROPHIC-CANCELLATION GUARD (additive — the tolerance is NOT loosened): a
        # series-backed operand can be the tiny difference of huge terms, so at the working
        # dps BOTH sides are pure roundoff and the residual is noise, not a refutation.
        # Concrete case (theta_20_2_12): the C-grid pair z=-0.7+2.1i, τ=1.4+0.3i satisfies
        # z = 1/2 − 11 + 7τ to ~1e-30 — an exact lattice zero of θ₂ — so the θ series'
        # largest term ~9e19 cancels to a true value ~5e-10 (≈30 digits of cancellation =
        # ALL of the 30-dps working precision), and the "FAIL" compared noise to noise.
        # Remedy: re-evaluate the offending sample at doubled precision. Strictly more
        # accurate, so a TRUE disagreement still fails (and a noise residual resolves);
        # any error here keeps the base-precision residual — the guard can never hide a
        # genuine FAIL behind an exception.
        if relation == "eq" and rel_gap >= tol:
            try:                           # 2× budget: doubled precision costs ~2–4× per eval,
                                           # and a budget expiry here would reinstate a noise FAIL
                with _time_limit(2 * EVAL_BUDGET), mp.workdps(2 * mp.mp.dps):
                    a2, b2 = evaluate(L, env), evaluate(R, env)
                    rel2 = abs(a2 - b2) / max(mp.mpf(1), abs(a2), abs(b2))
                if mp.isfinite(rel2):
                    rel_gap = rel2
            except Exception:
                pass
        worst = max(worst, rel_gap)
        best = rel_gap if best is None else min(best, rel_gap)
    if ok_pts < (2 if free else 1):
        return (UNABLE, f"unbound:{unbound_head}" if unbound_head else "undersampled/domain")
    if relation == "ne":
        # ≠ is refuted only by a sampled COINCIDENCE (L≈R); a clear gap everywhere is evidence.
        return (("FAIL" if best < TOL else "PASS"), f"min-gap={mp.nstr(best, 4)} over {ok_pts}pts")
    # SOUNDNESS-of-COVERAGE: a non-trivial identity (neither side a literal `0`) that
    # VANISHES at every sampled point was never substantively exercised — `0 = 0` holds for
    # any two functions that happen to vanish there (e.g. a Wigner relation on a grid where
    # the 3j symbol is identically zero). Report it as a skip, not a hollow PASS.
    if free and maxmag < mp.mpf("1e-15") and not (_is_zero_lit(L) or _is_zero_lit(R)):
        # …unless the vanishing is an artefact of WHICH 24 combos the cap selected. The cap
        # takes the lexicographic PREFIX of the cartesian product, so on a wide product every
        # leading variable is pinned at its FIRST grid value; if that one value happens to sit
        # where both sides are (junk-)zero, the row skips although its OWN grid contains points
        # that exercise it. Concretely heun_31_11_12 (DLMF 31.11.12, the Fuchs–Frobenius kernel
        # at ∞) has the Gauss factor ₂F₁(…;1/z), and Mathlib's `ordinaryHypergeometric` is the
        # SERIES — junk-0 off its disc — so the pinned z = 0.5+0.8i (‖1/z‖ = 1.06 > 1) zeroes
        # BOTH sides, while the same ℂ grid's z = 2−1.3i and −0.7+2.1i put 1/z inside the disc.
        # Retry ONCE with a STRIDED window over the SAME product, so every variable sweeps its
        # own grid. Reachable only from this skip (a row that already has a verdict is never
        # re-swept), invents no sample value, and changes no tolerance, gate or filter — the
        # retry runs the identical per-sample chain and may itself return PASS, FAIL or a skip.
        if not _diversify:
            return sweep_eq(L, R, binders, constraints, relation, _diversify=True)
        return (UNABLE, "trivial-zero/unexercised")
    return (("PASS" if worst < tol else "FAIL"), f"worst={mp.nstr(worst,4)} over {ok_pts}pts")


TOL_DERIV = mp.mpf("1e-7")     # numerical-differentiation gate (looser than exact)
TOL_QUAD = mp.mpf("1e-12")     # weighted-quadrature gate (singular-weight integrals)
TOL_TRANSFORM = mp.mpf("1e-6") # infinite-ray quadrature gate (Laplace/Mellin transforms)


def _has_ray_integral(node):
    """True if the tree contains a right-infinite integral ∫_lo^∞ — its exp-sinh
    evaluation over the ray is the loosest-accuracy quadrature in the kit. Also true for a
    `mellin f s` head, whose evaluation IS such a ray integral (∫₀^∞ t^{s−1}f(t) dt)."""
    if isinstance(node, tuple):
        if node[0] == "integral" and node[3] == ("inf",):
            return True
        if node[0] == "app" and node[1] in (("var", "mellin"), ("var", "laplace"),
                                             ("var", "laplaceTransform")):
            return True
        return any(_has_ray_integral(c) for c in node[1:])
    if isinstance(node, list):
        return any(_has_ray_integral(c) for c in node)
    return False


def _has_finite_integral(node):
    """True if the tree contains a DEFINITE integral over a FINITE interval (a `0..1`
    Euler integral, DLMF 15.6.8/15.6.9). Such a node is evaluated by adaptive mp.quad, so
    its residual carries tanh-sinh quadrature error — with the endpoint-singular weights
    `t^{d−1}(1−t)^{c−d−1}` and a large-argument ₂F₁ integrand this is ~1e-13, far above the
    exact 1e-18 gate but a TRUE identity — so the comparison belongs at the same TOL_QUAD as
    the weighted-measure integrals, NOT the exact gate. Matching the tolerance to the method
    actually used can never flip a genuine (O(1)) discrepancy to a pass. A doubly/right-
    infinite contour (handled by `_has_ray_integral`) is excluded."""
    if isinstance(node, tuple):
        if node[0] == "integral" and node[2] not in (("inf",), ("neginf",)) \
                and node[3] not in (("inf",), ("neginf",)):
            return True
        return any(_has_finite_integral(c) for c in node[1:])
    if isinstance(node, list):
        return any(_has_finite_integral(c) for c in node)
    return False


# Functions whose DEFINITION is a (ray-)quadrature, so a check referencing them carries
# quadrature precision even though the ∫ is hidden inside the def rather than visible in L/R.
# The §7.12 asymptotic remainders remF/remG (DLMF 7.12.6/7.12.7 ray integrals): `g = truncG +
# remG` is exact, but at extreme asymptotic params (large n, small x) it cancels a large
# divergent-tail truncation against the tiny remainder, leaving a ~1e-17 quadrature/cancellation
# residual — far above the exact 1e-18 gate, yet still a true identity.
_QUAD_BACKED_NAMES = {"remF", "remG"}

def _refs_name(node, names):
    """True if the tree applies (or bare-references) a function whose head var resolves to a
    key in `names`. Unlike `collect_free`, this DOES inspect function heads (`collect_free`
    drops the head of an `app` node, keeping only its arguments)."""
    if isinstance(node, tuple):
        if node[0] == "app" and isinstance(node[1], tuple) and node[1][0] == "var" \
           and _reg_resolve(node[1][1]) in names:
            return True
        if node[0] == "var" and _reg_resolve(node[1]) in names:
            return True
        return any(_refs_name(c, names) for c in node[1:])
    if isinstance(node, list):
        return any(_refs_name(c, names) for c in node)
    return False

def _eq_tol(L, R):
    if _has_deriv(L) or _has_deriv(R):
        return TOL_DERIV
    if _has_ray_integral(L) or _has_ray_integral(R):
        return TOL_TRANSFORM
    if _contains(L, {"mintegral"}) or _contains(R, {"mintegral"}):
        return TOL_QUAD
    if _refs_name(L, _QUAD_BACKED_NAMES) or _refs_name(R, _QUAD_BACKED_NAMES):
        return TOL_QUAD
    if _has_finite_integral(L) or _has_finite_integral(R):
        return TOL_QUAD
    return TOL


def sweep_ineq(op, L, R, binders, constraints=None):
    """Sample free vars; check the inequality at each in-domain point. Sound exactly as
    equality-sampling is: a clear sampled violation REFUTES; satisfying every sample is
    evidence (it cannot witness tightness — that blindness is Tier 0/2's to cover). A tiny
    relative slack absorbs roundoff so a boundary case (|J₀(0)| = 1) is not a false FAIL."""
    constraints = constraints or {}
    # TRANSITIVE-POSITIVITY grid inference — the EXACT block sweep_eq applies (see there):
    # `0 < q` ∧ `q < r` (ltpair/lepair) implies `0 < r`, but only q carries the `pos` flag,
    # so on an inequality row like qGamma monotonicity (DLMF 5.18.8/5.18.9: 0 < q < r < 1)
    # r's mixed-sign default grid never exceeds q's positive grid, every combo fails the
    # ltpair filter, and the row starves into `undersampled/domain` although the hypothesis
    # domain is plainly non-empty. Deriving the flag samples r on the positive grid —
    # strictly inside the stated hypothesis domain (the ltpair filter still applies per
    # sample); no tolerance or scoring change, nothing loosened. ADDITIVE port of
    # sweep_eq's proven block into the inequality sweep.
    for _q in constraints.get('_pairs', []):
        if _q[0] in ('ltpair', 'lepair') and constraints.get(_q[1]) == 'pos' \
                and constraints.get(_q[2]) is None:
            constraints = {**constraints, _q[2]: 'pos'}
    # ∀-quantified function variables → anchored witnesses (see _subst_fn_witness/sweep_eq).
    wmap = constraints.get('_fnwitness') or {}
    # tuple-valued witness family (IsMultiplicative) — check EVERY member, as in sweep_eq.
    for _wv, _ws in wmap.items():
        if isinstance(_ws, (tuple, list)):
            outs = [(w, sweep_ineq(op, L, R, binders,
                                   {**constraints, '_fnwitness': {**wmap, _wv: w}}))
                    for w in _ws]
            for w, o in outs:
                if o[0] == "FAIL":
                    return (o[0], f"{_wv}:={w} {o[1]}")
            if all(o[0] == "PASS" for _, o in outs):
                return ("PASS", "; ".join(f"{_wv}:={w} {o[1]}" for w, o in outs))
            return next(o for _, o in outs if o[0] != "PASS")
    if wmap:
        L, R = _subst_fn_witness(L, wmap), _subst_fn_witness(R, wmap)
    free = set(); collect_free(L, free); collect_free(R, free)
    binders = _lattice_binders(free, binders)
    # a registry name in `free` is a FUNCTION reference (a bare fn like `erfc` in `f = g`),
    # not a variable: neither flagged unbound nor sampled. Sampleables = binders + indeterminate.
    unbound = [v for v in free if v != IND and v not in binders and _reg_resolve(v) is None]
    if unbound:
        return (UNABLE, f"unbound:{unbound[0]}")
    free = {v for v in free if v == IND or v in binders}    # drop bare-fn refs from sampling
    grids = []
    for v in sorted(free):
        if v == IND:
            grids.append((v, SAMPLES[IND]))
        else:
            base = binders.get(v, "R")
            flag = constraints.get(v)
            if base == "lattice":
                grids.append((v, ob.SAMPLE_LATTICES))
            elif base == "latticept":
                grids.append((v, [mp.mpf(0)]))
            elif base == "H" or (base == "C" and flag in ("impos", "imnonneg")):
                # upper half-plane IS captured (τ : ℍ, or a `0 < τ.im` hypothesis): sampling stays
                # in-domain, so a real-valued ‖·‖/re comparison is sound. A genuinely complex
                # operand makes `a < b` raise → that point drops, never a spurious refutation.
                grids.append((v, SAMPLES["H"]))
            elif base == "C" and flag == "imneg":
                grids.append((v, SAMPLES_H_NEG))   # `z.im < 0` hypothesis — lower half-plane grid
            elif base == "C":
                # ≤/< has no order on ℂ and the domain hypothesis is uncaptured — sampling freely
                # would FALSE-FAIL a true theorem, so stay honest and skip.
                return (UNABLE, "complex-order")
            elif base in ("Z", "N"):
                grids.append((v, _int_grid(flag, base)))
            else:
                grids.append((v, _filter_lower(v, _filter_upper(v, _real_grid(flag), constraints), constraints)))
    if (constraints or {}).get('_flags'):      # multi-hypothesis variables (see _filter_extra_flags)
        grids = [(v, _filter_extra_flags(v, g, constraints)) for v, g in grids]
    import itertools
    combos = list(itertools.product(*[g[1] for g in grids])) if grids else [()]
    names = [g[0] for g in grids]
    worst, ok_pts, unbound_head, cplx_operand = mp.mpf("-inf"), 0, None, False
    intvars = {v for v, t in binders.items() if t in ("Z", "N")}   # for Lean floor `/`
    periodvars = [v for v, t in binders.items() if t == "latticept"]
    # a relational pair-filter (e.g. `1 ≤ b − a`) rejects many combos, so scan a wider
    # window when one is present — else the 24-combo cap can exhaust on invalid points and
    # report `undersampled` for a perfectly checkable claim. Stop once 24 points are evaluated.
    scan_cap = 256 if (constraints or {}).get('_pairs') else 24
    for combo in combos[:scan_cap]:
        if ok_pts >= 24:
            break
        env = dict(zip(names, combo))
        env["_intvars"] = intvars
        env["_binders"] = binders
        env["_zmodmod"] = (constraints or {}).get('_zmodmod', {})   # a : ZMod k → its modulus k
        if "W" in env and "L" in env:
            env["W"] = env["L"]
        for pv in periodvars:
            if "L" in env:
                env[pv] = env["L"].w1
        if not _pairs_ok(env, constraints):
            continue
        if _natsub_negative(L, env) or _natsub_negative(R, env):
            continue                       # defer the Nat truncated-subtraction boundary point
        try:
            a, b = evaluate(L, env), evaluate(R, env)
        except Unparseable as e:
            unbound_head = unbound_head or _unbound_head_of(e)
            continue
        except (ZeroDivisionError, ValueError, OverflowError):
            continue
        except Exception:
            continue
        # an order comparison needs REAL operands; a genuinely complex operand (≠ real up to
        # roundoff) is unorderable — note it and skip the point (a complex PARAMETER feeding a
        # real-valued ‖·‖/re/… is fine and falls through here).
        if abs(mp.im(a)) > mp.mpf("1e-12") * max(mp.mpf(1), abs(a)) or \
           abs(mp.im(b)) > mp.mpf("1e-12") * max(mp.mpf(1), abs(b)):
            cplx_operand = True
            continue
        a, b = mp.re(a), mp.re(b)
        ok_pts += 1
        # violation margin RELATIVE to the operand scale: positive ⇒ inequality broken here
        margin = (a - b) if op in ("≤", "<") else (b - a)
        worst = max(worst, margin / max(mp.mpf(1), abs(a), abs(b)))
    if ok_pts < (2 if free else 1):
        if cplx_operand:
            return (UNABLE, "complex-order")
        return (UNABLE, f"unbound:{unbound_head}" if unbound_head else "undersampled/domain")
    slack = TOL_DERIV if (_has_deriv(L) or _has_deriv(R)) else TOL
    return (("PASS" if worst <= slack else "FAIL"),
            f"margin={mp.nstr(worst,4)} over {ok_pts}pts")


def _finvec_callable(vals):
    """Wrap a concrete Python list of Fin-q sample values as a `.q`-tagged callable — the
    same carrier-tagging convention `_mulchar_sample`/`_addchar_sample` use for `.modulus`
    (oracle_bindings.py), so the shared `app`/bare-univ-`∏`/`∑` lookups in `evaluate` can
    recover q without threading it through every call site. Used to resolve a genuinely
    `Fin q`-parametrized vector binder `A/B : Fin q → ℂ` (meijerG_eq_pFq, DLMF 16.18.1)."""
    def f(idx):
        return vals[int(idx)]
    f.q = len(vals)
    return f


def _finvec_applied_q(body, var, env):
    """The cardinality `q` of the finvecC callable APPLIED to the bound index `var` inside a
    bare-univ `∏ var, …`/`∑ var, …` body (`∏ i, (A i + n)` → env['A'].q). Used to give each
    of two distinct-dimension parameter tuples (`A : Fin p → 𝕂`, `B : Fin q → 𝕂`,
    pFqCoefficient_succ_div) its OWN product range. Returns None if no `.q`-tagged callable is
    applied to `var` (the caller then falls back to any-carrier, the equal-dim meijerG case)."""
    found = []

    def walk(nd):
        if not isinstance(nd, tuple):
            return
        if nd[0] == "app" and nd[1][0] == "var":
            X = nd[1][1]
            vv = env.get(X)
            if callable(vv) and hasattr(vv, "q") and any(a == ("var", var) for a in nd[2]):
                found.append(int(vv.q))
        for e in nd[1:]:
            if isinstance(e, tuple):
                walk(e)
            elif isinstance(e, list):
                for x in e:
                    walk(x)
    walk(body)
    return found[0] if found else None


def _veclist(node, env):
    """A `![…]` vector-literal node (or empty `![]`) → list of evaluated entries (pFq params).
    Also accepts the `(fun _ : Fin 0 => 0)` / `(fun _ : Fin 0 => (0 : ℂ))` EMPTY-vector idiom
    (the `: Fin 0` annotation is discarded by the shared lambda parser, so only this exact
    size-0 shape — body is the literal numeral 0, independent of the bound var — is
    recognized), a genuinely `Fin q`-parametrized (q > 0) LAMBDA over a resolved finvecC
    vector — `fun i => 1 - A i` (meijerG_eq_pFq's `aNum`/`bDen` arguments) — evaluated
    elementwise over `0 .. q-1` with q read off any `.q`-tagged callable reachable in env
    (the same carrier lookup as the bare-univ `∏`/`∑` cases in `evaluate`), and a BARE
    finvecC variable applied directly (`pFq A B z`'s `A`, `B` — no wrapping lambda),
    expanded via its own `.q` tag. Used by `pFq A B z` (DLMF 16.2.1) and `meijerG`'s
    parameter-vector arguments (DLMF 16.17.1, e.g. the RHS `pFq (fun _ : Fin 0 => (0:ℂ))
    (fun _ : Fin 0 => (0:ℂ)) (-z)` of `meijerG_eq_pFq_zero`)."""
    if node[0] == "vec":
        return [evaluate(e[1] if e[0] == "expr" else e, env) for e in node[1]]
    if node[0] == "var" and callable(env.get(node[1])) and hasattr(env[node[1]], "q"):
        f = env[node[1]]
        return [f(mp.mpf(idx)) for idx in range(int(f.q))]
    if node[0] == "lam" and len(node) == 3:
        body = node[2]
        if body[0] == "real":            # (fun _ : Fin 0 => (0 : ℂ)) — transparent ℂ ascription
            body = body[1]
        if body == ("num", 0):
            return []
        qq = next((getattr(vv, "q", None) for vv in env.values()
                   if callable(vv) and hasattr(vv, "q")), None)
        if qq is not None:
            return [evaluate(body, {**env, node[1]: mp.mpf(idx)}) for idx in range(int(qq))]
    raise Unparseable("pFq parameter vector not a ![…] literal or the Fin-0/Fin-q idiom")



def _indicator_support(func, env):
    """If `func` is `indicator (Ioc/Icc/Ioo/Ico a b) f` over a bounded interval, return (a,b)
    — the Mellin/Laplace integration support; else None."""
    if (func[0] == "app" and func[1][0] == "var"
            and func[1][1] in ("indicator", "Set.indicator") and len(func[2]) == 2):
        setnode = func[2][0]
        if (setnode[0] == "app" and setnode[1][0] == "var"
                and setnode[1][1].split(".")[-1] in ("Ioc", "Icc", "Ioo", "Ico")
                and len(setnode[2]) == 2):
            return (evaluate(setnode[2][0], env), evaluate(setnode[2][1], env))
    return None


def _seq_callable(lam, base_env):
    """A `(fun k => …)` ℕ-indexed sequence node → a Python function of an integer `k`,
    closing over the outer sampled free vars in `base_env`. Used for the partial-numerator /
    -denominator sequences `a`, `b` of `FLMF.Error.cfConv` (DLMF §7.9 / §7.18.13), whose
    bodies are `if k = 0 then … else if k % 2 = 1 then …` forms the parser already tokenizes.
    Returns None for anything that isn't a lambda (an unbound/unsupported sequence → skip)."""
    if lam[0] != "lam":
        return None
    return lambda k: evaluate(lam[2], {**base_env, lam[1]: mp.mpf(int(k))})


def _cfconv_eval(a, b, N):
    """The `n`-th convergent `Aₙ/Bₙ` of `FLMF.Error.cfConv a b` (the classical Wallis
    fundamental recurrence, EXACTLY as the Lean `cfNum`/`cfDen` defs index it):
        A₀ = b₀,  A₁ = b₁·b₀ + a₁,  Aₙ = bₙ·Aₙ₋₁ + aₙ·Aₙ₋₂   (n ≥ 2)
        B₀ = 1,   B₁ = b₁,          Bₙ = bₙ·Bₙ₋₁ + aₙ·Bₙ₋₂
    `a`, `b` are Python callables of an integer index. Raises (→ honest point drop) on a
    vanishing denominator convergent (Bₙ = 0, the convergent is undefined there)."""
    N = int(N)
    if N == 0:
        return b(0)
    if N == 1:
        if b(1) == 0:
            raise ZeroDivisionError("cfConv B₁ = 0")
        return (b(1) * b(0) + a(1)) / b(1)
    Anm2, Anm1 = b(0), b(1) * b(0) + a(1)
    Bnm2, Bnm1 = mp.mpf(1), b(1)
    for n in range(2, N + 1):
        An = b(n) * Anm1 + a(n) * Anm2
        Bn = b(n) * Bnm1 + a(n) * Bnm2
        Anm2, Anm1 = Anm1, An
        Bnm2, Bnm1 = Bnm1, Bn
    if Bnm1 == 0:
        raise ZeroDivisionError("cfConv Bₙ = 0")
    return Anm1 / Bnm1


def _callable(func, base_env):
    """Turn a HasDerivAt/Tendsto function node into a one-argument Python callable, or
    None if unsupported (partial application of an unbound symbol, etc.)."""
    # `cfConv a b` (a 2-arg application of the continued-fraction convergent assembler, with
    # `a`, `b` SEQUENCE lambdas) → λN. cfConv(a,b,N): the Tendsto limit-gate then drives N up
    # the probe ladder and checks the convergents → the (bound) target (DLMF §7.9 / §7.18.13).
    # `cfConvC` = the complex analogue (ComplexErfExtra.lean) — same recurrence, same eval.
    if (func[0] == "app" and func[1][0] == "var"
            and func[1][1].split(".")[-1] in ("cfConv", "cfConvC") and len(func[2]) == 2):
        aseq = _seq_callable(func[2][0], base_env)
        bseq = _seq_callable(func[2][1], base_env)
        if aseq is None or bseq is None:
            return None
        return lambda N: _cfconv_eval(aseq, bseq, N)
    if func[0] == "lam":
        return lambda t: evaluate(func[2], {**base_env, func[1]: t})
    # `indicator (Ioc a b) f` — a function masked to the interval, 0 outside (Mellin/Laplace).
    if (func[0] == "app" and func[1][0] == "var"
            and func[1][1] in ("indicator", "Set.indicator") and len(func[2]) == 2):
        setnode, inner = func[2]
        if (setnode[0] == "app" and setnode[1][0] == "var"
                and setnode[1][1].split(".")[-1] in ("Ioc", "Icc", "Ioo", "Ico")):
            kind = setnode[1][1].split(".")[-1]
            a, b = evaluate(setnode[2][0], base_env), evaluate(setnode[2][1], base_env)
            g = _callable(inner, base_env)
            if g is None:
                return None
            lo_ok = (lambda t: a < t) if kind in ("Ioc", "Ioo") else (lambda t: a <= t)
            hi_ok = (lambda t: t <= b) if kind in ("Ioc", "Icc") else (lambda t: t < b)
            return lambda t: g(t) if (lo_ok(t) and hi_ok(t)) else mp.mpf(0)
        return None
    # 𝓕 f — Mathlib Fourier transform: (𝓕 f)(w) = ∫_ℝ e^{−2πi x w} f(x) dx.
    if (func[0] == "app" and func[1] == ("var", "𝓕") and len(func[2]) == 1):
        g = _callable(func[2][0], base_env)
        if g is None:
            return None
        return lambda w: mp.quad(lambda x: mp.e ** (-2 * mp.pi * mp.j * x * w) * g(x),
                                 [-mp.inf, mp.inf])
    if func[0] == "var" and (_reg_get(func[1]) or (None,))[0] == "fn":
        return _reg_get(func[1])[1]
    # `SlashAction.map k γ f` — the weight-k modular slash action, eta-expanded to a
    # τ-callable: (f ∣[k] γ)(τ) = (cτ+d)^{−k}·f((aτ+b)/(cτ+d)) for γ = ((a,b),(c,d))
    # (the ModularGroup.T/S registry consts; DLMF 23.15/23.17 automorphy — the math lives
    # in ob._slash_action, det γ = 1). Handled here (not generic partial application)
    # because the FUNCTION argument f needs _callable, not scalar `evaluate`.
    if func[0] == "app" and func[1] == ("var", "SlashAction.map") and len(func[2]) == 3:
        g = _callable(func[2][2], base_env)
        if g is None:
            return None
        try:
            kk = evaluate(func[2][0], base_env)
            gam = evaluate(func[2][1], base_env)
        except (Unparseable, ValueError, ZeroDivisionError, OverflowError, TypeError):
            return None
        return lambda t: ob._slash_action(kk, gam, g, t)
    # bare, unapplied `deriv f` / `logDeriv f` (a FUNCTION value, e.g. the LHS of the
    # extensionality equality `deriv dawson = fun x => 1 − 2x·dawson x`, DLMF §7.2 /
    # DawsonODE.lean — reached through _func_eq's eta-expansion): build the operand
    # callable with _fn_callable (the same builder inline `deriv f x` uses) and
    # differentiate at the eta point. ADDITIVE: mirrors the applied-form evaluate()
    # logic; an unsupported operand returns None → the honest unsupported skip.
    if func[0] == "app" and func[1] in (("var", "deriv"), ("var", "logDeriv")) \
            and len(func[2]) == 1:
        try:
            g = _fn_callable(func[2][0], base_env)
        except Unparseable:
            return None
        if func[1][1] == "logDeriv":
            return lambda t: mp.diff(g, t) / g(t)
        return lambda t: mp.diff(g, t)
    # PARTIAL application of a registry fn: `besselI_nat 0` ↦ λt. I(0,t) — mirror _fn_callable.
    if (func[0] == "app" and func[1][0] == "var"
            and (_reg_get(func[1][1]) or (None,))[0] == "fn"):
        fn = _reg_get(func[1][1])[1]
        try:
            pre = [evaluate(a, base_env) for a in func[2]]
        except (Unparseable, ValueError, ZeroDivisionError, OverflowError, TypeError):
            return None                       # an unevaluable partial arg → unsupported, skip
        return lambda t: fn(*pre, t)
    return None


# ── DLMF §31.3 Fuchs–Frobenius solutions: the `IsHeunSolution` predicate expander ──────
# Sampling margins. The displayed solutions are `P(z) · Hℓ(ã, …; u(z))` with `Hℓ(ã,…;·)`
# the SUM of a Maclaurin series convergent on `|·| < min(1,|ã|)` (Frameworks/Heun/
# Analytic.lean, heunCoeff_radius_ge) and `P` a principal-branch cpow. A numerically
# differentiated point must sit STRICTLY inside both stated domains — the stencil of
# mp.diff straddles the point — so candidates are kept only well inside the disc and off
# the principal cut. Both margins SHRINK the sampled set to a subset of the row's own
# stated hypotheses (`hz`, `hzs`); nothing is loosened.
_HEUN_DISC_MARGIN = mp.mpf("0.85")
_HEUN_CUT_MARGIN = mp.mpf("0.15")


def _heun_pow_bases(node, acc):
    """Collect the BASE node of every `^` occurring in a displayed Heun solution (the
    principal-branch prefactors z^{1−γ}, (1−z)^{1−δ}, ((a−z)/(a−1))^{1−ε}, z^{−α}, …)."""
    if isinstance(node, tuple):
        if len(node) == 4 and node[0] == "bin" and node[1] == "^":
            acc.append(node[2])
        for x in node:
            _heun_pow_bases(x, acc)
    elif isinstance(node, list):
        for x in node:
            _heun_pow_bases(x, acc)


def _heun_fn_apps(node, acc):
    """Collect every `heunFn ã q̃ α̃ β̃ γ̃ δ̃ u` application node as (ã-node, u-node)."""
    if isinstance(node, tuple):
        if (len(node) == 3 and node[0] == "app" and node[1][0] == "var"
                and node[1][1].split(".")[-1] == "heunFn" and len(node[2]) == 7):
            acc.append((node[2][0], node[2][6]))
        for x in node:
            _heun_fn_apps(x, acc)
    elif isinstance(node, list):
        for x in node:
            _heun_fn_apps(x, acc)


def _pair_vars(pair, binders):
    """The declared binder variables mentioned by one '_pairs' hypothesis entry (its string
    elements are variable names or expressions — parse each and collect its free vars)."""
    out = set()
    for el in pair[1:]:
        if not isinstance(el, str):
            continue
        try:
            fv = set()
            collect_free(P(tokenize(el)).expr(), fv)
            out |= {v for v in fv if v in binders}
        except Exception:
            if el in binders:
                out.add(el)
    return out


def _heun_z_candidates(a_val):
    """Candidate evaluation points for a Heun display, given the sampled singularity `a`:
    a coarse lattice plus rings around each finite singular point 0, 1, a (where the
    solutions at z = 0, 1, a live) and large-modulus points (where the z = ∞ solutions
    live). Candidates are only PROPOSED here — each is admitted solely by the in-disc /
    off-cut test against the row's own stated domain."""
    out = []
    for k in range(8):
        ph = mp.e ** (2 * mp.pi * mp.mpc(0, 1) * mp.mpf(k) / 8)
        for c in (mp.mpf(0), mp.mpf(1), a_val):
            for r in ("0.12", "0.3", "0.55"):
                out.append(c + mp.mpf(r) * ph)
        for R in ("1.8", "3.5", "7.0"):
            out.append(mp.mpf(R) * max(mp.mpf(1), abs(a_val)) * ph)
    return out


def handle_heun_solution(args, d):
    """An `IsHeunSolution a q α β γ δ w z` CONCLUSION (FLMF.Heun, Frameworks/Heun/Local.lean)
    whose `w` is a CONCRETE displayed function `fun ζ => …heunFn…` — the Fuchs–Frobenius
    solutions of DLMF 31.3.5–31.3.11. `IsHeunSolution` is a DEFINED predicate, not an opaque
    one: it unfolds to the cleared-denominator Heun equation 31.2.1

        z(z−1)(z−a)·w″(z) + (γ(z−1)(z−a) + δz(z−a) + (α+β+1−γ−δ)z(z−1))·w′(z)
                          + (αβz − q)·w(z) = 0,

    so the claim is a numeric equality in the displayed function and its first two
    derivatives at the sampled point. Expand it exactly that way (the precedent is the
    IsMultiplicative / IsCompletelyMultiplicative conclusion expanders, which likewise
    rewrite a predicate into its defining equalities) and score the residual against the
    scale of its own three terms — the equation is homogeneous, so an absolute residual is
    meaningless without that normalization.

    SAMPLING. Parameters come from the ordinary grids and must clear the row's own pairwise
    hypotheses (`a ≠ 1`, `1 ≤ ‖a‖`) and its defining-equality pins (`ε = α+β+1−γ−δ`); the
    point z is admitted only where the display is actually DEFINED — inside the Maclaurin
    disc `‖u(z)‖ < min(1,‖ã‖)` of the inner `heunFn` (with the margin above, since the
    derivative stencil must stay inside too) and off the principal-branch cut of every cpow
    prefactor. That is a subset of the stated hypotheses `hz` / `hzs`, never a superset.

    Returns None (→ the caller keeps its honest skip) for any shape this does not cover:
    a non-lambda solution, an abstract-function binder, a non-var point, no inner heunFn,
    or a sample set that never lands in the stated domain."""
    if len(args) != 8:
        return None
    W, Z = args[6], args[7]
    if not (isinstance(W, tuple) and W[0] == "lam" and len(W) == 3) or Z[0] != "var":
        return None
    binders, cons = d["binders"], d.get("constraints") or {}
    zname, zeta, body = Z[1], W[1], W[2]
    if binders.get(zname) not in ("C", "R"):
        return None
    happs = []
    _heun_fn_apps(body, happs)
    if not happs:
        return None
    bases = []
    _heun_pow_bases(body, bases)
    free = set()
    for nd in args:
        collect_free(nd, free)
    free = {v for v in free if v in binders}
    defeq = []
    for _dv, _dexpr in cons.get('_defeq', []):
        try:
            _da = parse(_dexpr)
            defeq.append((_dv, _da[1] if _da and _da[0] == "expr" else _da))
        except Exception:
            return None                       # an unparsable pin would leave ε unsampled
    params = sorted(free - {zname} - {v for v, _ in defeq})
    grids = [(v, list(_domain_reject_grid(v, cons, binders) or _grid(v, d))) for v in params]
    # De-coincidence + PRE-CAP hypothesis filtering, exactly as sweep_eq does: rotate each
    # complex grid by a distinct offset (a PERMUTATION — no new sample value) and admit an
    # env only after the defining-equality pins and the pairwise hypotheses (‖a‖ ≥ 1, a ≠ 1)
    # have been applied, so the parameter window is not exhausted by out-of-hypothesis
    # tuples (all-equal parameters, or ‖a‖ < 1, which is every one of the first 48 raw
    # tuples here).
    for j, (v, gr) in enumerate(grids):
        if len(gr) > 1:
            r = j % len(gr)
            grids[j] = (v, gr[r:] + gr[:r])
    # The PARAMETER pre-filter may only apply hypotheses that do not mention the point z
    # (which is not sampled yet): a `‖1 − z‖ < min 1 ‖1 − a‖` pair would otherwise reject
    # every parameter env for want of a z. The FULL pair set — including that hypothesis —
    # is re-applied per candidate point below, so nothing is dropped from the domain test.
    _cons_no_pt = {**cons, '_pairs': [p for p in cons.get('_pairs', [])
                                      if zname not in _pair_vars(p, binders)]}
    import itertools
    envs = []
    for combo in itertools.islice(itertools.product(*[g[1] for g in grids]), 4096):
        env = dict(zip(params, combo))
        try:
            for _dv, _dast in defeq:
                env[_dv] = evaluate(_dast, env)
        except Exception:
            continue
        if not _pairs_ok(env, _cons_no_pt):
            continue
        envs.append(env)
        if len(envs) >= 12:
            break
    worst, worst_at, ok, dropped = mp.mpf(0), None, 0, 0
    for env in envs:
        try:
            a_val = evaluate(args[0], env)
        except Exception:
            continue
        # in-domain z: strictly inside every inner Maclaurin disc, off every cpow cut
        pts = []
        for cand in _heun_z_candidates(a_val):
            env_z = {**env, zeta: cand}
            try:
                if not all(abs(evaluate(u, env_z))
                           < _HEUN_DISC_MARGIN * min(mp.mpf(1), abs(evaluate(at, env)))
                           for at, u in happs):
                    continue
                if not all((mp.re(bv := evaluate(b, env_z)) > 0
                            or abs(mp.im(bv)) > _HEUN_CUT_MARGIN) for b in bases):
                    continue
            except Exception:
                continue
            # and the row's OWN point hypotheses (‖1 − z‖ < min(1,‖1 − a‖), ‖a‖ < ‖z‖, …),
            # now that both the parameters and the point are in hand
            if not _pairs_ok({**env, zname: cand}, cons):
                continue
            pts.append(cand)
        if not pts:
            continue
        pts = pts[::max(1, len(pts) // 3)][:3]
        g = _callable(W, env)
        if g is None:
            return None
        for zv in pts:
            env2 = {**env, zname: zv}
            try:
                al, be, ga, de = (evaluate(args[i], env2) for i in (2, 3, 4, 5))
                qv, av = evaluate(args[1], env2), evaluate(args[0], env2)
                t1 = zv * (zv - 1) * (zv - av) * mp.diff(g, zv, 2)
                t2 = (ga * (zv - 1) * (zv - av) + de * zv * (zv - av)
                      + (al + be + 1 - ga - de) * zv * (zv - 1)) * mp.diff(g, zv)
                t3 = (al * be * zv - qv) * g(zv)
                gap = abs(t1 + t2 + t3) / max(mp.mpf(1), abs(t1), abs(t2), abs(t3))
            except Exception:
                dropped += 1
                continue
            ok += 1
            if gap > worst:
                worst, worst_at = gap, (dict(env2), mp.nstr(abs(t1 + t2 + t3), 6))
    if ok < 2:
        return (UNABLE, "is-heun-solution",
                f"undersampled: {ok} in-domain points ({dropped} dropped)")
    det = f"worst={mp.nstr(worst, 4)} over {ok}pts (31.2.1 residual / term scale)"
    if worst >= TOL_DERIV and worst_at is not None:
        det += (" @ " + ", ".join(f"{k}={mp.nstr(v, 6)}" for k, v in sorted(worst_at[0].items()))
                + f"; |residual|={worst_at[1]}")
    return (("PASS" if worst < TOL_DERIV else "FAIL"), "is-heun-solution", det)


def handle_deriv(args, d):
    """HasDerivAt f f' x  ⇒  numerically check  diff(f, x) == f'  over the sample."""
    if len(args) != 3:
        return (UNABLE, "deriv", "arity")
    func, deriv, pt = args
    if pt[0] != "var":
        return (UNABLE, "deriv", "non-var point")
    free = set(); collect_free(deriv, free); collect_free(func, free); free.add(pt[1])
    # binder status FIRST, registry second (sweep_eq's ordering): a declared binder whose
    # NAME happens to collide with a registry key (the Bessel order `μ` vs the Möbius
    # `mu`, besselJnu_hasDerivAt_general) must stay a sampled variable — dropping it here
    # left the env without μ, _callable's partial-application branch resolved `μ` to the
    # Möbius callable, raised, and the row skipped as 'unsupported func'.
    free = {v for v in free if v in d["binders"] or _reg_resolve(v) is None}
    unbound = [v for v in free if v != IND and v not in d["binders"]]
    if unbound:
        return (UNABLE, "deriv", f"unbound:{unbound[0]}")
    grids = [(v, _grid(v, d)) for v in sorted(free)]
    import itertools
    worst, ok, unbound_head = mp.mpf(0), 0, None
    for combo in list(itertools.product(*[g[1] for g in grids]))[:16]:
        env = dict(zip([g[0] for g in grids], combo))
        g = _callable(func, env)
        if g is None:
            return (UNABLE, "deriv", "unsupported func")
        try:
            num = mp.diff(g, env[pt[1]])
            want = evaluate(deriv, env)
            # Scale-normalized gap, same contract as sweep_eq's rel_gap: a raw absolute
            # gap false-FAILs any sample whose value is huge — theta_20_13_2_theta4
            # (DLMF 20.13.2, PROVED in Lean) hit |θ₄| ≈ 1e55 at z=−0.7+2.1i, τ=4iαt/π,
            # where 1e-31 relative roundoff reads as 1.35e+24 absolute.
            worst = max(worst, abs(num - want) / max(mp.mpf(1), abs(num), abs(want))); ok += 1
        except Unparseable as e:
            # an unbound head inside the derivative expression (`integrand a b x` of
            # hasDerivAt_incompleteBeta, DLMF 8.17) raises per-combo — remember it so the
            # skip is labelled `unbound:<fn>` honestly, exactly as sweep_eq does, instead
            # of the misleading generic `domain`.
            unbound_head = unbound_head or _unbound_head_of(e)
            continue
        except Exception:
            continue
    if ok < 1:
        return (UNABLE, "deriv",
                f"unbound:{unbound_head}" if unbound_head else "domain")
    return (("PASS" if worst < TOL_DERIV else "FAIL"), "deriv", f"worst={mp.nstr(worst,4)} over {ok}pts")


def _is_ray_integral_limit(func, env):
    """True when `func` is `fun R => ∫ t in lo..R, body` and `body` carries a genuine
    oscillatory cos(g(t))/sin(g(t)) factor in the integration variable (DLMF 5.9.6–9's
    improper-integral `Tendsto (fun R => ∫ t in 0..R, …) atTop (𝓝 L)` shape). For such a
    row, the deviation |value(R) − L| is NOT expected to shrink monotonically at arbitrary
    sample points R — only its oscillation ENVELOPE shrinks — so a non-monotone sequence of
    deviations is not evidence the limit is false, just that finite-R sampling caught an
    unfavorable phase. `env` supplies the row's OTHER free variables (e.g. the Fresnel `n`
    in cos(tⁿ)) so `_osc_phase`'s phase-varies-with-t probe can actually evaluate; only the
    bound `R` itself is excluded (irrelevant to the frozen-parameter phase check). Detection
    only; callers still require the envelope to be genuinely bounded/shrinking before
    treating a FAIL as an honest skip (never a blanket loosening)."""
    if not (func[0] == "lam" and len(func) == 3):
        return False
    Rvar, body = func[1], func[2]
    if not (body[0] == "integral" and body[3] == ("var", Rvar)):
        return False
    var = body[1]
    probe_env = {k: v for k, v in env.items() if k != Rvar}
    return _osc_phase(body[4], var, probe_env) is not None


def _tendsto_divergence(func, filt, d):
    """`Tendsto f F atTop` — divergence to +∞. PASS-only evidence: at every sampled
    parameter combo the probe values must be real, strictly increasing, large at the end
    (≥ 1e3) and grown by ≥ 50× across the ladder — the signature of a genuine pole/
    unbounded growth (1/|z| over three decades), which a bounded or slowly-growing
    sequence (Σ 1/p ~ log log N) can never fake. Anything short of that is an honest
    "divergence uncertified" skip; this branch NEVER returns FAIL (finite probes cannot
    refute divergence)."""
    if filt == ("var", "atTop"):
        probes = _f(10, 50, 200, 1000)
    elif filt[0] == "nhds":
        try:
            a = evaluate(filt[2], {})
        except Exception:
            return (UNABLE, "asymptotic", "filter base")
        sgn = -1 if filt[1] == "𝓝[<]" else 1
        probes = [a + sgn * s for s in _f("0.1", "0.01", "0.001", "0.0001")]
    else:
        return (UNABLE, "asymptotic", "filter unsupported")
    free = set(); collect_free(func, free)
    # binder status FIRST (see handle_deriv): a binder name colliding with a registry key
    # is still a sampled variable, never silently dropped from the grid.
    free = {v for v in free if v in d["binders"] or _reg_resolve(v) is None}
    unbound = [v for v in free if v != IND and v not in d["binders"]]
    if unbound:
        return (UNABLE, "asymptotic", f"unbound:{unbound[0]}")
    grids = [(v, _grid(v, d)) for v in sorted(free)] or [("_", [mp.mpf(0)])]
    import itertools
    combos = [c for c in itertools.product(*[g[1] for g in grids])
              if _pairs_ok(dict(zip([g[0] for g in grids], c)), d.get("constraints"))]
    ok, worst_end, unbound_seen = 0, mp.mpf("inf"), None
    for combo in combos[:8]:
        env = dict(zip([g[0] for g in grids], combo))
        g = _callable(func, env)
        if g is None:
            return (UNABLE, "asymptotic", "unsupported func")
        try:
            vals = [g(p) for p in probes]
        except Unparseable as e:           # an unbound head inside the lambda body —
            h = _unbound_head_of(e)        # surface it as unbound:<fn>, not `domain`
            if h and unbound_seen is None:
                unbound_seen = h
            continue
        except Exception:
            continue
        if any(abs(mp.im(v)) > mp.mpf("1e-9") * max(mp.mpf(1), abs(v)) for v in vals):
            continue
        vals = [mp.re(v) for v in vals]
        if not all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)):
            return (UNABLE, "asymptotic",
                    f"divergence uncertified (non-monotone, end={mp.nstr(vals[-1],4)})")
        if not (vals[-1] > mp.mpf(1000) and vals[-1] > 50 * max(vals[0], mp.mpf("1e-9"))):
            return (UNABLE, "asymptotic",
                    f"divergence uncertified (growth {mp.nstr(vals[0],4)}→{mp.nstr(vals[-1],4)})")
        ok += 1
        worst_end = min(worst_end, vals[-1])
    if ok < 1:
        return (UNABLE, "asymptotic",
                f"unbound:{unbound_seen}" if unbound_seen else "domain")
    return ("PASS", "asymptotic", f"diverges (end≥{mp.nstr(worst_end,4)} over {ok} combos)")


def _deep_limit_recheck(func, filt, lim, grids, d):
    """Certified DEEP near-limit re-scoring for a one-sided 𝓝[<]/𝓝[>] Tendsto whose standard
    4-decade ladder leaves the rate uncertified (worst rel ≥ 1e-2) even though the deviations
    are still SHRINKING toward the claimed limit. A genuinely slow one-sided tail — an algebraic
    (1−x)^p with small exponent p (Gauss's summation limit DLMF 15.4.20, ₂F₁→Γ-ratio, rate
    (1−x)^{c−a−b}), or a LOGARITHMIC O(1/log(1−x)) approach (DLMF 15.4.21, ₂F₁/(−log(1−x))→
    Γ-ratio) — is not refuted by the coarse grid: it is simply undersampled, the last default
    probe (1−x = 1e-4) sitting where the slow tail has not yet resolved. This resamples the SAME
    one-sided limit far closer to the base point (down to 1−x ≈ 1e-250), ESCALATING working
    precision per rung so the probe stays representable and the function evaluation stays
    accurate; each rung is cross-checked at 2× its dps and dropped if roundoff-dominated. The
    SAME 1e-2 relative gate is applied to the deepest surviving probe, and a PASS is issued only
    when the deviations are still shrinking there. No model, no extrapolation, no tolerance
    change — purely honest sampling of the one-sided limit closer than the default ladder
    reaches. Returns a verdict tuple on a decided PASS, else None (→ the honest uncertified
    skip). NEVER returns FAIL: a bounded/slow tail proves nothing against the limit, and a
    genuine mismatch (deviations not shrinking under deep sampling) simply declines to certify."""
    if not (filt[0] == "nhds" and filt[1] in ("𝓝[<]", "𝓝[>]")):
        return None
    try:
        base = evaluate(filt[2], {})
    except Exception:
        return None
    sgn = -1 if filt[1] == "𝓝[<]" else 1
    # (decades-from-base, working dps): dps sits comfortably past the decade so `base ∓ 10^-k`
    # is representable and the summand near the branch point keeps full accuracy. The ladder is
    # deep enough to resolve a 1/log(1−x) tail (whose relative deviation only falls like a
    # constant / |log(1−x)|), while the per-rung early-exit stops an algebraic tail at the first
    # rung that already clears the gate — so the fast (power-law) rows stay cheap.
    rungs = [(20, 70), (80, 130), (150, 200), (250, 300)]
    names = [g[0] for g in grids]
    import itertools
    combos = [c for c in itertools.product(*[g[1] for g in grids])
              if _pairs_ok(dict(zip(names, c)), d.get("constraints"))]
    ambient = mp.mp.dps
    worst, ok, improved = mp.mpf(0), 0, True
    try:
        for combo in combos[:8]:
            env = dict(zip(names, combo))
            g = _callable(func, env)
            if g is None:
                return None
            devs = []
            for k, dps in rungs:
                mp.mp.dps = max(dps, ambient)
                x = base + sgn * mp.mpf(10) ** (-k)
                try:
                    target = evaluate(lim[2], env)
                    v1 = g(x)
                    with mp.workdps(2 * mp.mp.dps):
                        v2 = g(x)
                except Exception:
                    continue
                if abs(v1 - v2) > mp.mpf("1e-6") * max(mp.mpf(1), abs(v2)):
                    continue                       # roundoff-dominated rung — drop it honestly
                devs.append(abs(v2 - target) / max(mp.mpf(1), abs(target)))
                if len(devs) >= 2 and devs[-1] < mp.mpf("1e-3"):
                    break                          # already well under the gate — stop deepening
            if len(devs) < 2:
                continue
            ok += 1
            worst = max(worst, devs[-1])
            improved = improved and (devs[-1] < devs[0] or devs[-1] < mp.mpf("1e-12"))
    finally:
        mp.mp.dps = ambient
    if ok < 1 or not improved:
        return None
    if worst < mp.mpf("1e-2"):
        return ("PASS", "asymptotic",
                f"deep near-limit ladder rel@end={mp.nstr(worst, 4)} over {ok}")
    return None


def _ray_integral_improper_check(func, lim, grids, d):
    """Certify (or refute) a `Tendsto (fun R => ∫ t in lo..R, body) atTop (𝓝 L)` improper
    ray-integral limit whose OSCILLATORY tail (DLMF 5.9.6–9's Cauchy–Saalschütz / Fresnel
    forms: ∫₀^R t^{x−1}cos t, …sin t, ∫₀^R cos(tⁿ), sin(tⁿ)) makes the default finite-R
    atTop ladder phase-noisy: |∫₀^R − L| shrinks only in ENVELOPE, so the 4 coarse probes
    (R = 10,50,200,1000) leave the rate uncertified even though the limit is exactly L.

    Rather than score the phase-noisy finite endpoints, this evaluates the CONVERGENT
    improper value ∫_lo^∞ body DIRECTLY via the pre-existing, self-validated oscillatory
    ray-integrator `_quad_ray_osc` (zero-split into constant-sign half-period panels →
    alternating-series acceleration by TWO independent accelerators that must agree to
    1e-6, plus a head-error gate that drops an under-resolved endpoint singularity) and
    compares it to the claimed limit L. The improper value carries no finite-R phase — it
    IS the limit — so the comparison certifies the rate the atTop ladder could not.

    SOUNDNESS. The scored value is `_quad_ray_osc`'s cross-validated improper integral
    (any sample it cannot certify — a divergent/growing tail, a non-alternating panel
    sequence, an under-resolved endpoint, or accelerator disagreement — RAISES and drops
    that combo, never a trusted-but-wrong value). Each surviving combo is additionally
    recomputed at DOUBLED working precision and dropped unless the two agree to 1e-6
    (the same roundoff gate the finite-R path applies per probe). A PASS is issued only
    when every surviving combo's improper value matches L to < 1e-4 relative (the method
    floor is ~1e-6; a true limit lands ~1e-9); a FAIL only on a gross, precision-stable
    contradiction (> 1e-2 relative) between the cross-validated improper value and L —
    the honest refutation of a wrong constant. Between the gates, or with no surviving
    combo, returns None so the caller keeps its prior uncertified skip. Sampling is
    narrowed to the row's stated hypothesis domain (the same order-bound filters the
    equality sweep uses) so an out-of-domain endpoint cannot influence the verdict.

    ADDITIVE: fires only where the ray-integral tail was already an uncertified skip; it
    can only DECIDE a row that was un-decided, never re-open or loosen any other verdict.
    Returns a verdict tuple on a decided PASS/FAIL, else None."""
    if not (func[0] == "lam" and len(func) == 3):
        return None
    Rvar, body = func[1], func[2]
    if not (body[0] == "integral" and body[3] == ("var", Rvar)):
        return None
    var, lo_ast, integrand = body[1], body[2], body[4]
    # narrow each grid to the row's stated hypothesis domain (int order bounds via
    # _filter_int_bounds; real bounds via _filter_lower/_filter_upper) — identical
    # discipline to the equality sweep's grid selection; a no-op when no bound is parsed.
    cons = d.get("constraints")
    fgrids = []
    for v, g in grids:
        base = d["binders"].get(v)
        if base in ("Z", "N"):
            g = _filter_int_bounds(v, g, cons)
        elif base in ("R", None):
            g = _filter_lower(v, _filter_upper(v, g, cons), cons)
        fgrids.append((v, g))
    import itertools
    names = [g[0] for g in fgrids]
    combos = [c for c in itertools.product(*[g[1] for g in fgrids])
              if _pairs_ok(dict(zip(names, c)), cons)]
    worst_rel, ok, unbound_seen = mp.mpf(0), 0, None
    for combo in combos[:8]:
        env = dict(zip(names, combo))
        try:
            target = evaluate(lim[2], env)
            lov = evaluate(lo_ast, env)
        except Unparseable as e:
            h = _unbound_head_of(e)
            if h and unbound_seen is None:
                unbound_seen = h
            continue
        except Exception:
            continue
        f = lambda t, env=env: evaluate(integrand, {**env, var: t})
        try:
            v1 = _quad_ray_osc(f, lov, integrand, var, env)
            with mp.workdps(2 * mp.mp.dps):
                v2 = _quad_ray_osc(f, lov, integrand, var, env)
        except Unparseable as e:
            h = _unbound_head_of(e)
            if h and unbound_seen is None:
                unbound_seen = h
            continue                           # value not certifiable → drop the combo
        except Exception:
            continue
        if abs(v1 - v2) > mp.mpf("1e-6") * max(mp.mpf(1), abs(v2)):
            continue                           # roundoff-dominated across precisions → drop
        ok += 1
        worst_rel = max(worst_rel, abs(v2 - target) / max(mp.mpf(1), abs(target)))
    if ok < 1:
        return None
    if worst_rel < mp.mpf("1e-4"):
        return ("PASS", "asymptotic",
                f"improper ray-integral limit rel={mp.nstr(worst_rel, 4)} over {ok}")
    if worst_rel > mp.mpf("1e-2"):
        return ("FAIL", "asymptotic",
                f"improper ray-integral rel={mp.nstr(worst_rel, 4)} over {ok}")
    return None


def handle_tendsto(args, d):
    """Tendsto f filter (𝓝 L)  ⇒  rate-gate: f→L along the filter, shrinking (§3.3)."""
    if len(args) != 3:
        return (UNABLE, "asymptotic", "arity")
    func, filt, lim = args
    # normalise fully-qualified aliases: `nhds L` ≡ `𝓝 L`, `Filter.atTop` ≡ `atTop`.
    if lim[0] == "app" and lim[1] == ("var", "nhds") and len(lim[2]) == 1:
        lim = ("nhds", "𝓝", lim[2][0])
    if filt[0] == "var" and filt[1] == "Filter.atTop":
        filt = ("var", "atTop")
    # explicit `nhdsWithin a (Set.Ioi b)` / `(Set.Iio b)` spelling of the one-sided filters
    # (erf_7_19_5, DLMF 7.19.5): when the base point equals the ray endpoint this IS the
    # `𝓝[>] a` / `𝓝[<] a` sugar the dispatch already handles — normalize it. Any other
    # nhdsWithin shape (a ≠ b, another set) keeps the honest "filter unsupported" skip.
    if (filt[0] == "app" and filt[1][0] == "var"
            and filt[1][1].split(".")[-1] == "nhdsWithin" and len(filt[2]) == 2):
        _base, _set = filt[2]
        if (_set[0] == "app" and _set[1][0] == "var"
                and _set[1][1].split(".")[-1] in ("Ioi", "Iio") and len(_set[2]) == 1):
            try:
                _same = abs(evaluate(_base, {}) - evaluate(_set[2][0], {})) < mp.mpf("1e-12")
            except Exception:
                _same = False
            if _same:
                filt = ("nhds",
                        "𝓝[>]" if _set[1][1].split(".")[-1] == "Ioi" else "𝓝[<]", _base)
    # a Tendsto TARGET of `atTop` (divergence to +∞, e.g. ns_pole_zero — DLMF 22.4.1's
    # simple pole of ns at z = 0): certified PASS only on strong monotone unbounded growth
    # along the filter ladder; anything else is an honest skip. NEVER FAIL — a bounded-
    # looking sample proves nothing about divergence (log log-slow growth).
    if lim[0] == "var" and lim[1] in ("atTop", "Filter.atTop"):
        return _tendsto_divergence(func, filt, d)
    if lim[0] != "nhds":
        return (UNABLE, "asymptotic", "limit not 𝓝")
    # probe sequence from the filter
    if filt == ("var", "atTop"):
        probes = _f(10, 50, 200, 1000)
    elif filt[0] == "nhds":
        try:
            a = evaluate(filt[2], {})
        except Exception:
            return (UNABLE, "asymptotic", "filter base")
        step = _f("0.1", "0.01", "0.001", "0.0001")
        sgn = -1 if filt[1] == "𝓝[<]" else 1
        probes = [a + sgn * s for s in step]
    else:
        return (UNABLE, "asymptotic", "filter unsupported")
    free = set(); collect_free(func, free); collect_free(lim[2], free)
    free = {v for v in free if _reg_resolve(v) is None}     # registry fns aren't variables
    unbound = [v for v in free if v != IND and v not in d["binders"]]
    if unbound:
        return (UNABLE, "asymptotic", f"unbound:{unbound[0]}")
    # SOUNDNESS: an abstract FUNCTION binder (a : ℕ → ℝ, base 'absfnR'/'absfnN') in a
    # Tendsto row is quantified together with functional HYPOTHESES this handler cannot
    # capture (erfc_watson_series, §7.12.1: `hsplit` pins `a k` to the Taylor coefficients
    # of e^{−u²} and `hhlim` pins aN to h's boundary limit — the stated limit is FALSE for
    # a generic (a, aN)). handle_tendsto has no callable-sampling kit (its _grid would
    # mis-sample the function as a bare real scalar, and the scored combos degenerate to
    # the N = 0 slice with aN free — a fabricated refutation of a proven theorem). Skip
    # honestly instead — never sample a function binder as a number. The binder sits in
    # application-HEAD position (`a k`), which collect_free never frees, so scan heads
    # with _absfn_heads (the sweep_eq mechanism) as well as the free set.
    _hd = set(); _absfn_heads(func, _hd); _absfn_heads(lim[2], _hd)
    absfns = [v for v in sorted(free | _hd)
              if d["binders"].get(v) in ("absfnR", "absfnN")]
    if absfns:
        return (UNABLE, "asymptotic",
                f"abstract-fn binder {absfns[0]} (functional hypotheses uncaptured)")
    grids = [(v, _grid(v, d)) for v in sorted(free)] or [("_", [mp.mpf(0)])]
    import itertools
    # honor the row's pair hypotheses (a < b, a + b < c, …) BEFORE the combo cap — exactly
    # as the equality sweep does: a sample outside the stated hypothesis domain proves
    # nothing about the limit (e.g. DLMF 15.4.20's `0 < c − a − b`: outside it the ₂F₁
    # boundary limit genuinely diverges, and scoring such a point fabricates a FAIL on a
    # true theorem). ADDITIVE: only drops out-of-hypothesis combos; cap and gates unchanged.
    _tnames = [g[0] for g in grids]
    _tcombos = [c for c in itertools.product(*[g[1] for g in grids])
                if _pairs_ok(dict(zip(_tnames, c)), d.get("constraints"))]
    # CONSTRUCTIVE real-part-vanishing pin `(Σ cᵥ·v).re = 0` (DLMF 15.4.22's Re(c−a−b) = 0
    # boundary regime): the discrete complex grid never lands on Re = 0 exactly, so a drop
    # filter would starve the row — instead set the +1-coefficient binder's real part to make
    # Re(Σ) = 0 by construction, keeping its imaginary part from the grid (so c ≠ a+b, the
    # companion `hne`, still holds generically and Γ(c−a−b) stays off its pole). Same sound
    # in-hypothesis construction as `_reorder`. ADDITIVE: only re-homes real parts onto the
    # stated Re = 0 slice; combos with no releq binder are untouched.
    _releq = (d.get("constraints") or {}).get('_releq')
    if _releq:
        _idx = {n: i for i, n in enumerate(_tnames)}
        _built, _seen = [], set()
        for _combo in _tcombos:
            _cl, _ok = list(_combo), True
            for _solve, _coeffs in _releq:
                if _solve not in _idx or any(v not in _idx for v in _coeffs):
                    _ok = False; break
                _rest = sum((_coeffs[v] * mp.re(_cl[_idx[v]])
                             for v in _coeffs if v != _solve), mp.mpf(0))
                _old = _cl[_idx[_solve]]
                _cl[_idx[_solve]] = mp.mpc(-_rest / _coeffs[_solve], mp.im(_old))
            if not _ok:
                continue
            _key = tuple(mp.nstr(x, 15) for x in _cl)
            if _key not in _seen:
                _seen.add(_key); _built.append(tuple(_cl))
        _tcombos = _built
    # A continued-fraction convergent `cfConv a b N` (DLMF §7.9 / §7.18.13): the Wallis
    # recurrence settles MONOTONELY in N, but to a value the row claims is the target. Drive a
    # long index ladder and certify on Cauchy-stabilization AT the target. A sequence that
    # stabilizes at a DIFFERENT value is not a slow tail — it is a genuine mismatch; but rather
    # than assert FAIL (the §7.9 conventions / index parity are exactly the kind of thing this
    # sweep surfaces for human audit, not auto-refutes), report it as an explicit uncertified
    # skip carrying the limit it actually converged to. Never a false FAIL on a true row.
    def _has_cfconv(nd):
        # `cfConvC` = the complex analogue (erf_7_9_3, ComplexErfExtra.lean) — routed to the
        # same extended CF probe ladder. bin/neg/inv traversal is needed because that row's
        # lam body is `(I/√π) * cfConvC a b N` — a ("bin", …) node the old walker never
        # descended into, so the row fell to the generic short 4-probe ladder.
        if nd[0] == "app" and nd[1][0] == "var" \
                and nd[1][1].split(".")[-1] in ("cfConv", "cfConvC"):
            return True
        if nd[0] == "lam":
            return _has_cfconv(nd[2])
        if nd[0] == "app":
            return _has_cfconv(nd[1]) or any(_has_cfconv(a) for a in nd[2])
        if nd[0] == "bin":
            return _has_cfconv(nd[2]) or _has_cfconv(nd[3])
        if nd[0] in ("neg", "inv", "real"):
            return _has_cfconv(nd[1])
        return False
    _is_cf = _has_cfconv(func)
    if _is_cf:
        cf_probes = _f(20, 60, 150, 400, 1200, 3000)
        worst_rel, ok, mismatched = mp.mpf(0), 0, None
        for combo in _tcombos[:8]:
            env = dict(zip([g[0] for g in grids], combo))
            g = _callable(func, env)
            if g is None:
                return (UNABLE, "asymptotic", "unsupported func")
            try:
                target = evaluate(lim[2], env)
                vals = [g(p) for p in cf_probes]
            except Exception:
                continue
            # require the convergents to have SETTLED (the last two agree to high precision) —
            # else the rate is uncertified (a sluggish small-argument CF tail) → honest skip.
            settle = abs(vals[-1] - vals[-2]) / max(mp.mpf(1), abs(vals[-1]))
            if settle > mp.mpf("1e-10"):
                continue                       # not yet stabilized at THIS sample — don't count it
            ok += 1
            rel = abs(vals[-1] - target) / max(mp.mpf(1), abs(target))
            worst_rel = max(worst_rel, rel)
            if rel > mp.mpf("1e-8") and mismatched is None:
                mismatched = (mp.nstr(vals[-1], 8), mp.nstr(target, 8))
        if ok < 1:
            return (UNABLE, "asymptotic", "cfConv unsettled (uncertified rate)")
        if mismatched is not None:
            # the convergents DO converge, but to a value ≠ the claimed limit — surface it
            return (UNABLE, "asymptotic",
                    f"cfConv converges to {mismatched[0]} ≠ target {mismatched[1]} (AUDIT)")
        if worst_rel < mp.mpf("1e-6"):
            return ("PASS", "asymptotic", f"cfConv rel@settle={mp.nstr(worst_rel,4)} over {ok}")
        return (UNABLE, "asymptotic", f"cfConv uncertified (rel={mp.nstr(worst_rel,4)})")
    worst_rel, improved_all, ok = mp.mpf(0), True, 0
    dropped_roundoff = False
    unbound_seen = None
    # supplementary NEAR-LIMIT ladder for a one-sided 𝓝[<]/𝓝[>] filter whose default
    # ladder steps into a regime the oracle binding genuinely cannot evaluate (mp.qp
    # raises NoConvergence for q ≥ 0.99 inside the qGamma binding — the documented q→1
    # numeric hazard; DLMF 5.18.10): when fewer than 2 default probes survive, retry with
    # steps further from the limit point but still directed along the filter. ADDITIVE:
    # fires only where the row previously starved (< 2 certified probes ⇒ guaranteed
    # skip); the shrink/pass gates are unchanged — the weaker ladder's deviations must
    # still shrink toward the claimed limit and clear the same rel@end gate.
    alt_probes = None
    if filt[0] == "nhds" and filt[1] in ("𝓝[<]", "𝓝[>]"):
        try:
            _a0 = evaluate(filt[2], {})
            _sg = -1 if filt[1] == "𝓝[<]" else 1
            alt_probes = [_a0 + _sg * s for s in _f("0.1", "0.07", "0.04", "0.02")]
        except Exception:
            alt_probes = None

    def _probe_devs(g, ps, target):
        # Per-probe SOUNDNESS gate: recompute each probe at doubled working precision
        # and keep the sample only if the two evaluations agree. An asymptotic-remainder
        # functional like DLMF 7.12.1, x^{2N+1}·(√π e^{x²} erfc x − Σ_{m<N}…), cancels
        # ~2N·log₁₀x digits before the x^{2N+1} rescale: at the largest probe the
        # base-precision value can be pure roundoff (erfc_7_12_1 at N=5, x=1000 gives
        # 5.5e4 instead of −29.53), and scoring that noise fabricates a FAIL on a true
        # statement. Cross-precision disagreement means the sample is roundoff-dominated
        # — it proves nothing in either direction, so it is dropped honestly; a genuine
        # statement/limit mismatch is precision-stable, reproduces at both precisions,
        # and still FAILs. A probe raising Unparseable with an unbound head is remembered
        # so the eventual skip is labelled `unbound:<fn>` (sweep_eq's discipline), never
        # the misleading `domain`. Per-PROBE failures drop the probe, not the whole combo.
        # ADDITIVE: gates which samples are scored; the shrink/pass tolerances unchanged.
        nonlocal dropped_roundoff, unbound_seen
        out = []
        for p in ps:
            try:
                v1 = g(p)
                with mp.workdps(2 * mp.mp.dps):
                    v2 = g(p)
            except Unparseable as e:
                h = _unbound_head_of(e)
                if h and unbound_seen is None:
                    unbound_seen = h
                continue
            except Exception:
                continue
            if abs(v1 - v2) > mp.mpf("1e-6") * max(mp.mpf(1), abs(v2)):
                dropped_roundoff = True
                continue
            out.append(abs(v2 - target))
        return out

    for combo in _tcombos[:8]:
        env = dict(zip([g[0] for g in grids], combo))
        g = _callable(func, env)
        if g is None:
            return (UNABLE, "asymptotic", "unsupported func")
        try:
            target = evaluate(lim[2], env)
        except Unparseable as e:
            h = _unbound_head_of(e)
            if h and unbound_seen is None:
                unbound_seen = h
            continue
        except Exception:
            continue
        devs = _probe_devs(g, probes, target)
        if len(devs) < 2 and alt_probes is not None:
            devs = _probe_devs(g, alt_probes, target)
        if len(devs) < 2:
            continue                       # too few certified samples — don't score
        ok += 1
        rel = devs[-1] / max(mp.mpf(1), abs(target))      # relative gate (slow O(1/n) ok)
        worst_rel = max(worst_rel, rel)
        # "improved" OR "already pinned to the limit": a function like erf saturates to 1 to
        # full precision by the first probe, so every dev is ~0 and a strict devs[-1]<devs[0]
        # would FAIL the strongest possible evidence for the limit. Converged ⇒ pass.
        converged = devs[-1] < mp.mpf("1e-12")
        improved_all = improved_all and (devs[-1] < devs[0] or converged)
    if ok < 1:
        if unbound_seen:
            return (UNABLE, "asymptotic", f"unbound:{unbound_seen}")
        if dropped_roundoff:
            return (UNABLE, "asymptotic", "roundoff-dominated samples (uncertified)")
        return (UNABLE, "asymptotic", "domain")
    # Refutation discipline: FAIL only a genuine CONTRADICTION (deviations not shrinking
    # toward the claimed limit). A limit that is converging but hasn't reached the gate
    # (a slow O(1/log x) tail, or an asymptotic-expansion remainder) is not refuted — it is
    # uncertified → honest skip, never a false FAIL on a true theorem.
    if not improved_all:
        # `fun R => ∫ t in lo..R, body` with an OSCILLATORY body (DLMF 5.9.6–9's improper
        # ray-integral limit, e.g. ∫₀^R t^{x−1}cos t): the deviation |value(R) − L| shrinks
        # only in ENVELOPE, not monotonically at arbitrary finite R — an unlucky sample phase
        # (e.g. R=200 landing worse than R=50) is expected, not a contradiction. The checker
        # cannot certify the rate from 4 coarse atTop probes here, so it is an honest skip
        # (never a fabricated PASS either) — same discipline as the cfConv-unsettled branch
        # above. Detection is by shape (an oscillatory factor genuinely present in the
        # integrand), never by row name, and does not touch the gate for any other Tendsto.
        if _is_ray_integral_limit(func, env):
            # the finite-R ladder cannot certify a phase-noisy oscillatory tail; certify (or
            # refute) the row instead by its CONVERGENT improper value ∫_lo^∞ body, evaluated
            # by the self-validated oscillatory ray-integrator (`_ray_integral_improper_check`).
            decided = _ray_integral_improper_check(func, lim, grids, d)
            if decided is not None:
                return decided
            return (UNABLE, "asymptotic",
                    f"uncertified rate (ray-integral oscillatory tail, rel@end={mp.nstr(worst_rel,4)})")
        return ("FAIL", "asymptotic", f"rel@end={mp.nstr(worst_rel,4)} over {ok}")
    if worst_rel < mp.mpf("1e-2"):
        return ("PASS", "asymptotic", f"rel@end={mp.nstr(worst_rel,4)} over {ok}")
    # The default 4-decade ladder left the rate uncertified, but the deviations ARE shrinking
    # toward the claimed limit (improved_all) — a genuinely slow one-sided tail (algebraic
    # (1−x)^p with small p, or logarithmic O(1/log(1−x))) that the coarse grid simply hasn't
    # resolved. Resample the SAME one-sided limit far closer to the base point at escalated
    # precision (no model, same 1e-2 gate); a decided PASS there certifies the row honestly.
    deep = _deep_limit_recheck(func, filt, lim, grids, d)
    if deep is not None:
        return deep
    return (UNABLE, "asymptotic", f"uncertified rate (rel@end={mp.nstr(worst_rel,4)})")


def _count_var(node, name):
    """Occurrences of the bare variable node ("var", name) anywhere in an AST
    (tuples/lists walked generically; dotted names and other atoms never match)."""
    if isinstance(node, tuple):
        if node[0] == "var":
            return 1 if node[1] == name else 0
        return sum(_count_var(x, name) for x in node[1:])
    if isinstance(node, list):
        return sum(_count_var(x, name) for x in node)
    return 0


def _solve_linear_var(eqnode, name):
    """`lhs = rhs` where `name` occurs EXACTLY ONCE, linearly with coefficient ±1 —
    i.e. only `+`, `-`, unary `neg`, and numeric-field casts on the path from the
    equality root down to the variable — solved symbolically for `name`. Returns the
    solved-for AST (free of `name`), or None on any other shape (a multiplicative,
    functional, or repeated occurrence is NOT solvable this way — never guess)."""
    L, R = eqnode[1], eqnode[2]
    cl, cr = _count_var(L, name), _count_var(R, name)
    if cl + cr != 1:
        return None
    node, target = (L, R) if cl else (R, L)
    while True:
        if node == ("var", name):
            return target
        if not isinstance(node, tuple):
            return None
        if node[0] == "real":                     # (e : ℚ/ℝ/ℂ) cast — numerically transparent
            node = node[1]
        elif node[0] == "neg":                    # −e = t  →  e = −t
            node, target = node[1], ("neg", target)
        elif node[0] == "bin" and node[1] in ("+", "-"):
            a, b = node[2], node[3]
            if _count_var(a, name) == 1:          # a ± b = t  →  a = t ∓ b
                node, target = a, ("bin", "-" if node[1] == "+" else "+", target, b)
            elif node[1] == "+":                  # a + b = t  →  b = t − a
                node, target = b, ("bin", "-", target, a)
            else:                                 # a − b = t  →  b = a − t
                node, target = b, ("bin", "-", a, target)
        else:                                     # ·, /, ^, app, … — not a ±1-linear path
            return None


def _isminmax_set_grid(snode):
    """Sample points of a Set node for the IsMinOn/IsMaxOn refutation check — a lower ray
    (Ioi/Ici), an upper ray (Iio/Iic), or a bounded interval (Ioo/Icc/Ioc/Ico). Returns a
    list of representative points or None if the set shape is unsupported. The rays are
    sampled log-like over ~2 decades on the open side; the bounded case is a uniform interior
    grid. Points are only ever used to look for a value that BEATS the witness extremum, so a
    coarse-but-straddling grid suffices (a genuine counterexample refutes; passing is evidence)."""
    if not (isinstance(snode, tuple) and snode[0] == "app" and snode[1][0] == "var"):
        return None
    kind = snode[1][1].split(".")[-1]
    args = snode[2]
    steps = (mp.mpf("1e-2"), mp.mpf("0.05"), mp.mpf("0.2"), mp.mpf("0.5"), mp.mpf(1),
             mp.mpf(2), mp.mpf(4), mp.mpf(8), mp.mpf(20), mp.mpf(50), mp.mpf(120))
    try:
        if kind in ("Ioi", "Ici") and len(args) == 1:
            a = mp.re(evaluate(args[0], {}))
            return [a + d for d in steps]
        if kind in ("Iio", "Iic") and len(args) == 1:
            b = mp.re(evaluate(args[0], {}))
            return [b - d for d in steps]
        if kind in ("Ioo", "Icc", "Ioc", "Ico") and len(args) == 2:
            a = mp.re(evaluate(args[0], {}))
            b = mp.re(evaluate(args[1], {}))
            if not (a < b):
                return None
            n = 24
            return [a + (b - a) * mp.mpf(i) / n for i in range(1, n)]
    except Exception:
        return None
    return None


def _check_isminmax_on(node, root, v):
    """Numeric refutation check for an `IsMinOn f s x` / `IsMaxOn f s x` witness conjunct
    (gamma_5_4_20_min: the positive minimiser x₀≈1.4616 of Γ on Ioi 0). Returns "PASS" when
    the witness value f(root) is the extremum over a grid of the set s, a `… (AUDIT)` string
    on a sampled counterexample, or None when the predicate/func/set shape is unsupported
    (→ the conjunct stays honestly `unchecked`). Sound as a refutation oracle: a grid point
    that beats the witness disproves the extremum claim; a clean grid is evidence, and — per
    existential discipline — a counterexample is reported as an AUDIT skip, never an auto-FAIL."""
    if not (isinstance(node, tuple) and node[0] == "app" and node[1][0] == "var"):
        return None
    head = node[1][1].split(".")[-1]
    if head not in ("IsMinOn", "IsMaxOn") or len(node[2]) != 3:
        return None
    fnode, snode, pnode = node[2]
    if pnode != ("var", v):                       # the extremum must be claimed AT the witness
        return None
    g = _callable(fnode, {})
    if g is None:
        return None
    grid = _isminmax_set_grid(snode)
    if grid is None or not grid:
        return None
    lo_g, hi_g = min(grid), max(grid)
    # densify around the witness (in-set points only) for a tight exercise of the extremum
    grid = list(grid) + [p for p in (root + d for d in
                (mp.mpf("-0.3"), mp.mpf("-0.1"), mp.mpf("0.1"), mp.mpf("0.3")))
                if lo_g <= p <= hi_g]
    try:
        fr = g(root)
        if not mp.isfinite(fr):
            return None
    except Exception:
        return None
    isminon = (head == "IsMinOn")
    for y in grid:
        try:
            fy = g(y)
        except Exception:
            continue
        if not mp.isfinite(fy):
            continue
        tol = mp.mpf("1e-9") * max(mp.mpf(1), abs(fr), abs(fy))
        if isminon and fy < fr - tol:
            return (f"{head}: f({mp.nstr(y, 8)})={mp.nstr(fy, 8)} < f(witness)="
                    f"{mp.nstr(fr, 8)} (AUDIT)")
        if (not isminon) and fy > fr + tol:
            return (f"{head}: f({mp.nstr(y, 8)})={mp.nstr(fy, 8)} > f(witness)="
                    f"{mp.nstr(fr, 8)} (AUDIT)")
    return "PASS"


def _exists_witness_root(v, parts, d):
    """`∃ x, C₁ ∧ … ∧ Cₙ` with a single SCALAR bound variable: numeric witness search.
    Exactly one conjunct must be an equation f(x) = g(x) in x — its root is located either
    from an approximation-pin conjunct `|x − c| < ε` (seed c, DLMF 6.13.1's Ei zero) or by
    bisection inside interval-bound conjuncts (`∃ x₀ ∈ Ioo 1 2`, gamma_5_4_20_min). Every
    other conjunct is then CHECKED at the root: inequalities numerically, anything else
    (IsMinOn, …) reported unchecked → an honest partial skip. PASS only when every conjunct
    verifies; a violated conjunct is surfaced as an explicit AUDIT skip with the numbers
    (existential discipline: never an auto-FAIL from a numeric witness search)."""
    free = set()
    for part in parts:
        collect_free(part[1] if part[0] == "expr" else part, free)
    free = {u for u in free if _reg_resolve(u) is None}
    others = sorted(u for u in free if u != v)
    if others:
        u = others[0]
        if u in d["binders"]:
            return (UNABLE, "exists", f"outer binder {u} in witness body (unsupported)")
        return (UNABLE, "exists", f"unbound:{u}")
    eqs = [q for q in parts if q[0] == "eq" and _count_var(q, v) > 0]
    if len(eqs) != 1:
        return (UNABLE, "exists", f"witness-root: {len(eqs)} equation conjuncts")
    eq = eqs[0]
    g = lambda t: evaluate(eq[1], {v: t}) - evaluate(eq[2], {v: t})
    seed = lo = hi = None
    for q in parts:
        if q[0] != "ineq":
            continue
        _, op, A, B = q
        # approximation pin `|x − c| < ε` → root seed c
        if (op == "<" and A[0] == "app" and A[1] == ("var", "abs") and len(A[2]) == 1
                and A[2][0][0] == "bin" and A[2][0][1] == "-" and A[2][0][2] == ("var", v)):
            try:
                seed = evaluate(A[2][0][3], {})
            except Exception:
                pass
            continue
        try:                                   # interval bounds lo < x / x < hi
            if B == ("var", v) and _count_var(A, v) == 0:
                bv = evaluate(A, {})
                lo = bv if lo is None else max(lo, bv)
            elif A == ("var", v) and _count_var(B, v) == 0:
                bv = evaluate(B, {})
                hi = bv if hi is None else min(hi, bv)
        except Exception:
            pass
    root = None
    try:
        if seed is not None:
            root = mp.findroot(g, seed)
        elif lo is not None and hi is not None and lo < hi:
            n = 64
            pts = [lo + (hi - lo) * mp.mpf(i) / n for i in range(1, n)]
            vals = [g(t) for t in pts]
            for i in range(len(pts) - 1):
                if mp.sign(vals[i]) * mp.sign(vals[i + 1]) < 0:
                    a, b = pts[i], pts[i + 1]
                    for _ in range(120):
                        m = (a + b) / 2
                        if mp.sign(g(a)) * mp.sign(g(m)) <= 0:
                            b = m
                        else:
                            a = m
                    root = (a + b) / 2
                    break
    except Unparseable as e:
        h = _unbound_head_of(e)
        return (UNABLE, "exists", f"unbound:{h}" if h else f"witness-root eval ({e})")
    except Exception:
        root = None
    if root is None or not mp.isfinite(root) or abs(mp.im(root)) > mp.mpf("1e-20"):
        return (UNABLE, "exists", "witness-root: no root located")
    root = mp.re(root)
    env = {v: root}
    checked, unchecked, violated = 0, [], None
    for q in parts:
        if q is eq:
            checked += 1                       # the defining equation — root located on it
            continue
        if q[0] == "eq":
            try:
                a2, b2 = evaluate(q[1], env), evaluate(q[2], env)
            except Exception:
                unchecked.append("eq"); continue
            if abs(a2 - b2) <= mp.mpf("1e-9") * max(mp.mpf(1), abs(a2), abs(b2)):
                checked += 1
            else:
                violated = f"eq: {mp.nstr(a2, 8)} ≠ {mp.nstr(b2, 8)}"
        elif q[0] == "ineq":
            try:
                a2, b2 = evaluate(q[2], env), evaluate(q[3], env)
            except Exception:
                unchecked.append(q[1]); continue
            if {"≤": a2 <= b2, "<": a2 < b2, "≥": a2 >= b2, ">": a2 > b2}[q[1]]:
                checked += 1
            else:
                violated = f"{mp.nstr(a2, 10)} {q[1]} {mp.nstr(b2, 10)} fails"
        else:
            t = q[1] if q[0] == "expr" else q
            mm = _check_isminmax_on(t, root, v)   # IsMinOn/IsMaxOn f s witness → numeric extremum check
            if mm == "PASS":
                checked += 1
            elif mm is not None:                  # a sampled point beats the witness
                violated = mm
            else:
                unchecked.append(t[1][1] if (t[0] == "app" and t[1][0] == "var") else t[0])
    rt = mp.nstr(root, 20)
    if violated is not None:
        return (UNABLE, "exists-witness",
                f"root {v} ≈ {rt}: conjunct violated — {violated} (AUDIT)")
    if unchecked:
        return (UNABLE, "exists-partial",
                f"root {v} ≈ {rt}; verified {checked}/{len(parts)} conjuncts, unchecked: {unchecked}")
    return ("PASS", "exists-witness", f"root {v} ≈ {rt}; all {len(parts)} conjuncts hold")


def _lm_witness(parts, names, base, start, iters=120):
    """ONE damped Gauss–Newton / Levenberg–Marquardt run on the complex residual vector
    F(x) = (lhsᵢ − rhsᵢ)(x) of a fixed-size scalar system, from the point `start`. The
    residuals are holomorphic in the unknowns, so the Jacobian is the complex derivative
    (central differences at h = 10^(−dps/2)) and each step solves the regularized normal
    equations (JᴴJ + λI) δ = −JᴴF, λ shrinking on an accepted step and growing on a rejected
    one; this also handles an OVERDETERMINED but consistent system (DLMF 31.10.7 pins two
    angles with three rows). Returns the converged iterate or None. A run that does not
    converge is NEVER evidence against the existential — only an absent witness."""
    k, n = len(names), len(parts)
    x = list(start)

    def F(xv):
        env = dict(base)
        env.update(zip(names, xv))
        return [mp.mpmathify(evaluate(q[1], env)) - mp.mpmathify(evaluate(q[2], env))
                for q in parts]

    lam = mp.mpf("1e-8")
    h = mp.mpf(10) ** (-(mp.mp.dps // 2))
    try:
        Fx = F(x)
    except Exception:
        return None
    for _ in range(iters):
        try:
            nrm = max(abs(t) for t in Fx)
        except Exception:
            return None
        if not mp.isfinite(nrm):
            return None
        if nrm < mp.mpf(10) ** (-(mp.mp.dps - 4)):
            return x
        J = [[mp.mpc(0)] * k for _ in range(n)]
        try:
            for j in range(k):
                xp, xm = list(x), list(x)
                xp[j] = x[j] + h
                xm[j] = x[j] - h
                Fp, Fm = F(xp), F(xm)
                for i in range(n):
                    J[i][j] = (Fp[i] - Fm[i]) / (2 * h)
        except Exception:
            return None
        A, b = mp.matrix(k, k), mp.matrix(k, 1)
        for p in range(k):
            for q in range(k):
                A[p, q] = mp.fsum([mp.conj(J[i][p]) * J[i][q] for i in range(n)])
            A[p, p] += lam
            b[p] = -mp.fsum([mp.conj(J[i][p]) * Fx[i] for i in range(n)])
        try:
            step = mp.lu_solve(A, b)
            xn = [x[j] + step[j] for j in range(k)]
            Fn = F(xn)
            nn = max(abs(t) for t in Fn)
        except Exception:
            return None
        if nn < nrm:
            x, Fx = xn, Fn
            lam = max(lam / 4, mp.mpf("1e-25"))
        else:
            lam = lam * 8
            if lam > mp.mpf("1e12"):
                return None
    return None


def _exists_system_witness(binders, parts, d):
    """`∃ x₁ … x_k : ℂ (ℝ), E₁ ∧ … ∧ Eₙ` — several SCALAR bound variables constrained by a
    fixed-size system of equations: the angular substitution DLMF 31.10.7 (θ, φ from three
    trigonometric rows), the spherical substitution 31.10.20 (r, θ, φ) and the seven exponent
    relations 31.10.23 (two quadratics + two sum/product pairs + one linear row). Each display
    *sets* its new variables, so the faithful reading is simultaneous solvability, and the
    honest numeric content is a CONSTRUCTED WITNESS: at each sampled value of the outer
    parameters the system is solved numerically (multi-start `_lm_witness`) and then EVERY
    conjunct is re-evaluated at the constructed point and required to hold to 1e-18 relative —
    the same "locate a witness, then verify all conjuncts" discipline as `_exists_witness_root`,
    lifted from one unknown/one equation to a fixed-size system, and applied to overdetermined
    systems too (31.10.7's third row is an independent check on the pair the other two pin).

    Existential discipline, unchanged: this path NEVER returns FAIL. A witness that verifies
    every conjunct is evidence FOR the claim (PASS); a search that finds none is only an absent
    witness — reported as an honest skip naming the sample point, never a refutation. Returns
    None when the body is not such a system, leaving the prior honest skip in place."""
    names = sorted(binders)
    if not (2 <= len(names) <= 8) or any(binders[v] not in ("C", "R") for v in names):
        return None
    if not parts or any(q[0] != "eq" for q in parts) or len(parts) > 12:
        return None
    free = set()
    for q in parts:
        collect_free(q, free)
    free = {u for u in free if u in d["binders"] or _reg_resolve(u) is None}
    outer = sorted(u for u in free if u not in binders)
    unbound = [u for u in outer if u != IND and u not in d["binders"]]
    if unbound:
        return (UNABLE, "exists-system", f"unbound:{unbound[0]}")
    cons = d.get("constraints") or {}
    grids = [(u, _grid(u, d)) for u in outer]
    # sample the outer parameters on ROTATED DIAGONALS of the per-variable grids (variable i
    # takes grid entry (i+j) mod len): the product-prefix used elsewhere would give every
    # parameter of a 7-binder row the SAME first grid value, i.e. α = β = γ = … , a degenerate
    # slice of the system. Diagonals stay inside each variable's own stated-domain grid.
    combos, L = [], max([len(g) for _, g in grids] or [1])
    for j in range(L):
        combos.append(tuple(g[(i + j) % len(g)] for i, (_, g) in enumerate(grids)))
    import itertools
    for c in itertools.islice(itertools.product(*[g[1] for g in grids]), 4):
        if c not in combos:
            combos.append(c)
    accepted, ok, worst, missing, wit = 0, 0, mp.mpf(0), None, ""
    for combo in combos:
        base = dict(zip([g[0] for g in grids], combo))
        if not _pairs_ok(base, cons) or not _nonzero_ok(base, cons):
            continue
        accepted += 1
        if accepted > 3:
            break
        best = None
        for s in range(24):
            start = []
            for j, _v in enumerate(names):
                ang = mp.mpf(2 * (7 * s + 3 * j + 1)) / 11
                rad = mp.mpf(1) + mp.mpf(s % 5) / 2
                start.append(mp.mpc(rad * mp.cos(ang), rad * mp.sin(ang)))
            sol = _lm_witness(parts, names, base, start)
            if sol is None:
                continue
            if any(not mp.isfinite(abs(t)) for t in sol):
                continue
            # an ℝ-typed unknown needs a REAL witness — a complex root is no witness at all
            if any(binders[names[j]] == "R"
                   and abs(mp.im(sol[j])) > mp.mpf("1e-18") * max(mp.mpf(1), abs(sol[j]))
                   for j in range(len(names))):
                continue
            env = dict(base)
            env.update(zip(names, sol))
            try:                                   # re-verify EVERY conjunct at the witness
                rel = mp.mpf(0)
                for q in parts:
                    a2 = mp.mpmathify(evaluate(q[1], env))
                    b2 = mp.mpmathify(evaluate(q[2], env))
                    rel = max(rel, abs(a2 - b2) / max(mp.mpf(1), abs(a2), abs(b2)))
            except Exception:
                continue
            if best is None or rel < best[0]:
                best = (rel, sol)
            if rel < mp.mpf("1e-18"):
                break
        if best is None or best[0] >= mp.mpf("1e-18"):
            if missing is None:
                missing = ("; ".join(f"{k2}={mp.nstr(v2, 4)}" for k2, v2 in base.items()),
                           "none" if best is None else mp.nstr(best[0], 4))
            continue
        ok += 1
        worst = max(worst, best[0])
        wit = ", ".join(f"{names[j]}≈{mp.nstr(best[1][j], 8)}" for j in range(len(names)))
    if accepted == 0:
        return (UNABLE, "exists-system", "no sample point inside the stated hypotheses")
    if missing is not None:
        return (UNABLE, "exists-system",
                f"no witness located at {missing[0]} (best residual {missing[1]})")
    return ("PASS", "exists-system",
            f"witness solves all {len(parts)} conjuncts over {ok} samples "
            f"(worst rel residual {mp.nstr(worst, 4)}; last {wit})")


def _exists_const(v, body, d):
    """`∃ c, ∀ x, E(x) = c` — constancy witness (the DLMF 9.2.7 Wronskian shape): sample x,
    require the values to coincide; the common value is the witness. PASS on clean constancy;
    a clearly non-constant sample is an AUDIT skip (never auto-FAIL); unbound/abstract
    operands keep the honest skip."""
    fb, rel = body[1], body[2]
    if rel[0] != "eq" or len(fb) != 1:
        return (UNABLE, "exists", "forall-body not a constancy equation")
    (x, xty), = fb.items()
    if rel[2] == ("var", v):
        E = rel[1]
    elif rel[1] == ("var", v):
        E = rel[2]
    else:
        return (UNABLE, "exists", "forall-body not pinned to the bound witness")
    free = set(); collect_free(E, free)
    free = {u for u in free if _reg_resolve(u) is None} - {x}
    for u in sorted(free):
        if u not in d["binders"]:
            return (UNABLE, "exists", f"unbound:{u}")
        if d["binders"].get(u) not in ("R", "N", "Z", "C", "H"):
            return (UNABLE, "exists", f"non-numeric binder {u} (unsupported)")
    grids = [(u, _grid(u, d)) for u in sorted(free)] or [("_", [mp.mpf(0)])]
    xgrid = SAMPLES["C"] if xty in ("C", "H") else SAMPLES["N"] if xty in ("N", "Z") \
        else SAMPLES["R"]
    import itertools
    ok = 0
    for combo in list(itertools.product(*[g[1] for g in grids]))[:4]:
        env = dict(zip([g[0] for g in grids], combo))
        vals = []
        for t in xgrid:
            try:
                vals.append(evaluate(E, {**env, x: t}))
            except Unparseable as e:
                h = _unbound_head_of(e)
                return (UNABLE, "exists", f"unbound:{h}" if h else "unsupported func")
            except Exception:
                continue
        if len(vals) < 3:
            continue
        scale = max([mp.mpf(1)] + [abs(w) for w in vals])
        spread = max(abs(w1 - w2) for w1 in vals for w2 in vals)
        if spread > mp.mpf("1e-9") * scale:
            return (UNABLE, "exists-const",
                    f"not constant: spread={mp.nstr(spread, 4)} over {len(vals)} pts (AUDIT)")
        ok += 1
    if ok < 1:
        return (UNABLE, "exists-const", "domain")
    return ("PASS", "exists-const", f"constant over {ok} combos × {len(xgrid)} pts")


def _exists_asymp(binders, body, d):
    """`∃ A : ℝ, (fun x => f x − A) =O[atTop] g` (Mertens' second theorem, DLMF 27.11.8):
    the bound constant must enter ONCE, LINEARLY (verified numerically: the A-slope of the
    lambda is constant in x and O(1)); the witness is then SOLVED from a deep sample,
    A := the value making f(x_big; A) ≈ 0, and the =O gate is run with that witness. PASS
    on a bounded ratio; anything else is an honest skip — never FAIL (a poor witness
    estimate must not refute an existential)."""
    if len(binders) != 1:
        return (UNABLE, "exists", "multi-binder asymp body")
    (v, vty), = binders.items()
    kind, L, filtname, R = body[1], body[2], body[3], body[4]
    if kind != "O" or filtname not in ("atTop", "Filter.atTop") or vty != "R":
        return (UNABLE, "exists", "asymp body (only ∃A, f−A =O[atTop] g)")
    free = set(); collect_free(L, free); collect_free(R, free)
    free = {u for u in free if _reg_resolve(u) is None} - {v}
    unb = sorted(u for u in free if u != IND and u not in d["binders"])
    if unb:
        return (UNABLE, "exists", f"unbound:{unb[0]}")
    if free:
        return (UNABLE, "exists", "asymp body with outer binders (unsupported)")
    try:
        fA = lambda t, Av: _fn_callable(L, {v: Av})(t)
        s0 = fA(mp.mpf(100), mp.mpf(1)) - fA(mp.mpf(100), mp.mpf(0))
        s1 = fA(mp.mpf(1000), mp.mpf(1)) - fA(mp.mpf(1000), mp.mpf(0))
    except Unparseable as e:
        h = _unbound_head_of(e)
        return (UNABLE, "exists", f"unbound:{h}" if h else "unsupported func")
    except Exception:
        return (UNABLE, "exists", "asymp witness eval failed")
    if abs(s0) < mp.mpf("1e-9") or abs(s0 - s1) > mp.mpf("1e-9") * max(mp.mpf(1), abs(s0)):
        return (UNABLE, "exists", "witness not once-linear in the bound constant")
    try:
        A_est = -fA(mp.mpf(300000), mp.mpf(0)) / s0
        gL = _fn_callable(L, {v: A_est})
        gR = _fn_callable(R, {})
        devs = []
        for p in _f(10, 100, 1000, 10000, 100000):
            b = gR(p)
            if abs(b) < mp.mpf("1e-300"):
                continue
            devs.append(abs(gL(p) / b))
    except Exception:
        return (UNABLE, "exists", "asymp witness eval failed")
    if len(devs) < 3:
        return (UNABLE, "exists", "domain")
    if devs[-1] < mp.mpf("1e6") and devs[-1] <= 4 * max(devs[0], mp.mpf(1)):
        return ("PASS", "exists-asymp",
                f"A≈{mp.nstr(A_est, 10)}; |f/g|@end={mp.nstr(devs[-1], 4)} over {len(devs)}")
    return (UNABLE, "exists-asymp",
            f"uncertified (A≈{mp.nstr(A_est, 10)}, |f/g|@end={mp.nstr(devs[-1], 4)})")


def _exists_fn_limits(P, parts, d):
    """`∃ P : ℤ → ℂ, (∀ n : ℤ, Tendsto inner_n atTop (𝓝 (P n))) ∧ Tendsto outer[P] atTop
    (𝓝 T)` — the DLMF 20.5.14–17 iterated-limit (Eisenstein) double products. The inner
    limits determine P uniquely (limits in ℂ are unique), so the profile is COMPUTED as the
    witness: P(n) := the inner sequence's Richardson-extrapolated limit (symmetric partial
    products carry a c/M + O(1/M²) tail — two Richardson levels on a doubling M-ladder,
    certified by level agreement, else the sample drops). The outer sequence is then driven
    up an N-ladder against the claimed limit. PASS on agreement; an outer sequence that
    SETTLES at a different value is surfaced as an explicit AUDIT skip with both numbers
    (existential discipline: never an auto-FAIL through a computed witness); anything else
    skips honestly. Returns None when the body is not this shape."""
    c1, c2 = parts
    if c1[0] == "expr" and isinstance(c1[1], tuple) and c1[1][0] == "forallq":
        c1 = c1[1]                         # a parenthesized `(∀ n : ℤ, …)` conjunct arrives
    if not (c1[0] == "forallq" and len(c1[1]) == 1):   # wrapped as ("expr", forallq)
        return None
    (nname, _nty), = c1[1].items()

    def _targs(t):
        if t[0] == "expr":
            t = t[1]
        if (t[0] == "app" and t[1] in (("var", "Tendsto"), ("var", "Filter.Tendsto"))
                and len(t[2]) == 3):
            return t[2]
        return None

    a1, a2 = _targs(c1[2]), _targs(c2)
    if a1 is None or a2 is None:
        return None
    innerlam, filt1, lim1 = a1
    outerlam, filt2, lim2 = a2
    if filt1 not in (("var", "atTop"), ("var", "Filter.atTop")) or \
            filt2 not in (("var", "atTop"), ("var", "Filter.atTop")):
        return None

    def _nhds_target(l):
        if l[0] == "app" and l[1] == ("var", "nhds") and len(l[2]) == 1:
            return l[2][0]
        if l[0] == "nhds" and l[1] == "𝓝":
            return l[2]
        return None

    t1, target = _nhds_target(lim1), _nhds_target(lim2)
    if t1 != ("app", ("var", P), [("var", nname)]) or target is None:
        return None
    free = set()
    collect_free(innerlam, free); collect_free(outerlam, free); collect_free(target, free)
    free -= {P, nname}
    free = {u for u in free if _reg_resolve(u) is None}
    unbound = [u for u in free if u != IND and u not in d["binders"]]
    if unbound:
        return (UNABLE, "exists-fn-limits", f"unbound:{unbound[0]}")
    cons = d.get("constraints") or {}
    grids = []
    for u in sorted(free):
        if d["binders"].get(u) == "C" and cons.get(u) in ("impos", "imnonneg"):
            grids.append((u, SAMPLES["H"]))    # 0 < τ.im (or 0 ≤ z.im) — upper half-plane grid
        elif d["binders"].get(u) == "C" and cons.get(u) == "imneg":
            grids.append((u, SAMPLES_H_NEG))   # z.im < 0 hypothesis — lower half-plane grid
        else:
            grids.append((u, _grid(u, d)))
    import itertools
    combos = [c for c in itertools.product(*[g[1] for g in grids])
              if _pairs_ok(dict(zip([g[0] for g in grids], c)), cons)]
    ok, mism = 0, None
    for combo in combos[:2]:
        env = dict(zip([g[0] for g in grids], combo))
        cache = {}

        def P_of(nv, _env=env, _cache=cache):
            key = int(nv)
            if key in _cache:
                return _cache[key]
            if abs(key) > 64:
                raise Unparseable("exists-fn inner index cap")
            gi = _callable(innerlam, {**_env, nname: mp.mpf(key)})
            if gi is None:
                raise Unparseable("exists-fn inner unsupported")
            # the symmetric-truncation tail is O(|n|/M) (paired factors sum a 2a·z/(a²−m²)
            # series with a = nτ), so the M-ladder must SCALE with the index for a uniform
            # extrapolation residual across n.
            s = max(2, abs(key))
            vs = [gi(mp.mpf(M * s)) for M in (48, 96, 192, 384)]
            A = [2 * vs[i + 1] - vs[i] for i in range(3)]        # kill the c/M term
            B = [(4 * A[i + 1] - A[i]) / 3 for i in range(2)]    # kill the c'/M² term
            if abs(B[1] - B[0]) > mp.mpf("3e-5") * max(mp.mpf(1), abs(B[1])):
                raise Unparseable("exists-fn inner limit unsettled")
            _cache[key] = B[1]
            return B[1]

        go = _callable(outerlam, {**env, P: P_of})
        if go is None:
            return (UNABLE, "exists-fn-limits", "unsupported outer func")
        try:
            tv = evaluate(target, env)
            ovals = [go(mp.mpf(N)) for N in (3, 6, 10)]
        except Exception:
            continue
        devs = [abs(o - tv) for o in ovals]
        rel = devs[-1] / max(mp.mpf(1), abs(tv))
        settled = abs(ovals[-1] - ovals[-2]) <= mp.mpf("1e-4") * max(mp.mpf(1), abs(ovals[-1]))
        # PASS gate: the whole outer ladder must sit on the target (≤1e-2 rel, an order
        # looser than the ≤1e-3 end gate) — the computed-witness error budget (25 factors
        # × ≤3e-5 certified inner residual) stays well inside it, so a true identity is
        # not starved, while a wrong target (off by any O(1) factor) can never sneak in.
        if rel < mp.mpf("1e-3") and max(devs) < mp.mpf("1e-2") * max(mp.mpf(1), abs(tv)):
            ok += 1
            continue
        if settled and mism is None:           # converged — but to a DIFFERENT value: audit
            mism = (mp.nstr(ovals[-1], 8), mp.nstr(tv, 8),
                    "; ".join(f"{kk}={mp.nstr(w, 4)}" for kk, w in env.items()))
    if mism is not None:
        return (UNABLE, "exists-fn-limits",
                f"outer limit settles to {mism[0]} ≠ claimed {mism[1]} at {mism[2]} (AUDIT)")
    if ok < 1:
        return (UNABLE, "exists-fn-limits", "domain/unsettled")
    return ("PASS", "exists-fn-limits",
            f"inner Richardson-settled; outer matches over {ok} samples")


def _handle_exists_compound(binders, body, d):
    """Dispatch the NEW compound existential bodies (conjunctions / quantified bodies) to
    their witness handlers. Everything unrecognized stays an honest skip; none of these
    paths can FAIL (see each handler's discipline)."""
    parts = list(body[1]) if body[0] == "and" else [body]
    fnb = [u for u, t in binders.items() if t == "fn"]
    if fnb:
        if len(binders) == 1 and len(parts) == 2:
            res = _exists_fn_limits(fnb[0], parts, d)
            if res is not None:
                return res
        return (UNABLE, "exists", "function-space witness (unsupported body shape)")
    if len(binders) == 1:
        (v, ty), = binders.items()
        if body[0] == "forallq":
            return _exists_const(v, body, d)
        if ty in ("R", "Z", "N"):
            return _exists_witness_root(v, parts, d)
    if body[0] == "and":                   # several scalar unknowns pinned by a fixed-size
        res = _exists_system_witness(binders, parts, d)   # system of equations (31.10.7/20/23)
        if res is not None:
            return res
    return (UNABLE, "exists", "unsupported compound body")


def handle_exists(binders, body, d):
    """`∃ L : ℝ, Tendsto f F (𝓝 L)` — an EXISTENCE claim. There is no DLMF number to refute:
    an existential over a CONTINUUM is not numerically falsifiable here, so the Tendsto
    branch NEVER returns FAIL. We PASS only on clear Cauchy stabilization of f along a
    ladder toward the filter point (strong evidence the limit exists); anything else (no
    stabilization within the ladder, unbound body, unsupported shape) is an honest skip.

    EXCEPTION (integer-equality branch, ADDITIVE): `∃ N : ℤ (or ℕ), lhs = rhs` with the
    bound variable occurring exactly once, linearly with coefficient ±1 (von Staudt–Clausen,
    DLMF 24.10) IS falsifiable — solving N = <residual> reduces the claim to '<residual>
    is an integer', decided by the SAME exact `nearint` gate as the
    `∈ Set.range ((↑) : ℤ → ℚ)` membership path (sweep_eq unchanged, no tolerance change):
    a clearly fractional residual at any sample refutes the existential (FAIL); unbound
    symbols / domain issues keep the usual honest skips."""
    # ── ∃ N : ℤ/ℕ, lhs = rhs — solve for N and check integrality of the residual ──
    if body[0] == "eq":
        used = [v for v in binders if _count_var(body, v) > 0]
        if len(used) != 1 or binders[used[0]] not in ("Z", "N") \
                or used[0] in d["binders"]:
            return (UNABLE, "exists", "eq body: not a single ℤ/ℕ-solvable bound variable")
        sol = _solve_linear_var(body, used[0])
        if sol is None:
            return (UNABLE, "exists", f"eq body: {used[0]} not once-linear ±1")
        # ty "N" clamps the nearest-integer projection at 0, so a solved value that is a
        # NEGATIVE integer correctly refutes an ℕ-existential (mirrors evaluate's nearint).
        v, det = sweep_eq(sol, ("nearint", sol, binders[used[0]]),
                          d["binders"], d.get("constraints"))
        return (v, "exists-int-eq", det)
    # compound bodies (∧-conjunctions, ∀-quantified bodies, =O with a bound constant) —
    # the NEW witness handlers; all skip-honest, none can FAIL (see each docstring).
    if body[0] in ("and", "forallq"):
        return _handle_exists_compound(binders, body, d)
    if body[0] == "asymp":
        return _exists_asymp(binders, body, d)
    # only the Tendsto-into-𝓝(boundvar) shape is supported; everything else skips honestly
    if body[0] != "expr" or body[1][0] != "app" or body[1][1] not in (
            ("var", "Tendsto"), ("var", "Filter.Tendsto")):
        return (UNABLE, "exists", "non-Tendsto body")
    args = body[1][2]
    if len(args) != 3:
        return (UNABLE, "exists", "arity")
    func, filt, lim = args
    if lim[0] == "app" and lim[1] == ("var", "nhds") and len(lim[2]) == 1:
        lim = ("nhds", "𝓝", lim[2][0])
    if filt[0] == "var" and filt[1] == "Filter.atTop":
        filt = ("var", "atTop")
    # the limit point must be exactly the existential-bound variable (𝓝 L with L : the binder)
    if lim[0] != "nhds" or lim[2][0] != "var" or lim[2][1] not in binders:
        return (UNABLE, "exists", "limit not 𝓝(bound var)")
    Lvar = lim[2][1]
    # probe ladder from the filter — long enough to see a slow oscillatory ~1/x Fresnel tail
    if filt == ("var", "atTop"):
        probes = _f(50, 200, 1000, 5000, 20000, 100000)
    elif filt[0] == "nhds":
        try:
            a = evaluate(filt[2], {})
        except Exception:
            return (UNABLE, "exists", "filter base")
        sgn = -1 if filt[1] == "𝓝[<]" else 1
        probes = [a + sgn * s for s in _f("0.1", "0.01", "0.001", "0.0001", "0.00001")]
    else:
        return (UNABLE, "exists", "filter unsupported")
    # f must be a registry-resolvable callable with no FREE vars other than the bound L
    free = set(); collect_free(func, free)
    free = {v for v in free if _reg_resolve(v) is None and v != Lvar}
    unbound = [v for v in free if v != IND and v not in d["binders"]]
    if unbound:
        return (UNABLE, "exists", f"unbound:{unbound[0]}")
    grids = [(v, _grid(v, d)) for v in sorted(free)] or [("_", [mp.mpf(0)])]
    import itertools
    worst_tail, ok = mp.mpf("inf"), 0
    for combo in list(itertools.product(*[g[1] for g in grids]))[:8]:
        env = dict(zip([g[0] for g in grids], combo))
        g = _callable(func, env)
        if g is None:
            return (UNABLE, "exists", "unsupported func")
        try:
            vals = [g(p) for p in probes]
        except Exception:
            continue
        if any(abs(mp.im(v)) > mp.mpf("1e-9") * max(mp.mpf(1), abs(v)) for v in vals):
            return (UNABLE, "exists", "complex sequence")
        ok += 1
        # Cauchy evidence: successive-probe gaps must be (a) shrinking monotonically and
        # (b) small at the tail. fresnelC/S converge as a slow oscillatory ~1/x tail, so the
        # gate tolerates slow monotone shrinkage rather than demanding a tiny absolute gap.
        gaps = [abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)]
        shrinking = all(gaps[i + 1] <= gaps[i] * mp.mpf("1.01") for i in range(len(gaps) - 1))
        if not shrinking:
            return (UNABLE, "exists", "no monotone stabilization")
        worst_tail = min(worst_tail, gaps[-1] / max(mp.mpf(1), abs(vals[-1])))
    if ok < 1:
        return (UNABLE, "exists", "domain")
    if worst_tail < mp.mpf("1e-3"):              # tail gap clearly collapsing ⇒ limit exists
        return ("PASS", "exists", f"tailgap={mp.nstr(worst_tail,4)} over {ok}")
    return (UNABLE, "exists", f"uncertified stabilization (tailgap={mp.nstr(worst_tail,4)})")


def handle_asymptotic(kind, L, filt, R, d):
    """f ~[filter] g (IsEquivalent, dev=|f/g−1|→0), =o[filter] (IsLittleO, dev=|f/g|→0),
    =O[filter] (IsBigO, |f/g| bounded). Rate-gated, refutation-disciplined: FAIL only on a
    clear contradiction (dev not shrinking for ~/o, or |f/g| blowing up for O); a converging-
    but-slow tail (e.g. Hₙ/log n → 1 at rate 1/log n) is uncertified → honest skip."""
    if filt.startswith("Filter."):          # `Filter.atTop` ≡ `atTop`
        filt = filt[len("Filter."):]
    if filt not in ("atTop", "atBot"):
        return (UNABLE, "asymptotic", f"filter {filt}")
    sgn = 1 if filt == "atTop" else -1
    probes = [sgn * p for p in _f(10, 100, 1000, 10000, 100000)]
    # free PARAMETERS (e.g. the k in partition n k ~ kⁿ/k!) are sampled, not just the probe var.
    free = set(); collect_free(L, free); collect_free(R, free)
    params = sorted(v for v in free if v in d["binders"])
    pgrids = [_grid(v, d) for v in params] or [[mp.mpf(0)]]
    import itertools
    # for the verdict use the WORST param combo: every sampled parameter must converge.
    first_dev, last_dev, n_combos = mp.mpf(0), mp.mpf(0), 0
    unbound_seen = None      # an unbound head raised per-probe (inside a lambda body) —
    for combo in list(itertools.product(*pgrids))[:6]:   # surfaced in the skip label below
        penv = dict(zip(params, combo))
        try:
            gL, gR = _fn_callable(L, penv), _fn_callable(R, penv)
        except Unparseable as e:
            h = _unbound_head_of(e)
            return (UNABLE, "asymptotic", f"unbound:{h}" if h else "unsupported func")
        def _probe_devs(ps):
            nonlocal unbound_seen
            dc_ = []
            for p in ps:
                try:
                    # GUARD DIGITS: an asymptotic REMAINDER (e.g. DLMF 6.12.4's g(x)−partial-sum,
                    # =O(x^{-(2n+2)})) is a subtraction of two quantities agreeing to many digits —
                    # the cancellation depth grows with the probe magnitude (empirically ~2·log10(p)
                    # per unit of the vanishing order, e.g. ~50 digits lost at p=1e5 for a 6th-order
                    # remainder). At the fixed base dps=30 this is pure roundoff noise blown up by
                    # dividing by the tiny denominator g(p) (e.g. reported |f/g|~6e27 for a PROVEN
                    # O-bound) — an oracle/harness artifact, not a statement failure. Evaluate at
                    # boosted working precision (same guard-digit idea as `_quad_ray_smooth`) so the
                    # subtraction in gL/gR is resolved before rounding back; this only ADDS precision,
                    # never loosens the comparison itself.
                    extra = int(4 * max(mp.mpf(0), mp.log10(max(abs(p), mp.mpf(1)))))
                    with mp.workdps(mp.mp.dps + extra):
                        a, b = mp.mpf(gL(p)), mp.mpf(gR(p))
                except Unparseable as e:         # an unbound head inside the lambda body only
                    h = _unbound_head_of(e)      # raises per-probe — remember it so the skip
                    if h and unbound_seen is None:   # is labelled `unbound:<fn>`, not `domain`
                        unbound_seen = h
                    continue
                except Exception:
                    continue
                if abs(b) < mp.mpf("1e-300"):    # g≈0 at this probe — ratio undefined, drop
                    continue
                dc_.append(abs(a / b - 1) if kind == "~" else abs(a / b))
            return dc_
        dc = _probe_devs(probes)
        if len(dc) < 2:
            # supplementary FINER ladder for fast-decaying comparisons (a Gaussian-tail
            # `~[atTop]` like iRepErfc ~ e^{−z²}/(2z)^{n+1}, DLMF 7.18.14, underflows the
            # 1e-300 ratio floor already at z = 100, so only the z = 10 probe of the
            # default decade ladder ever survives and the row starves at < 2 points):
            # retry with probes spaced BELOW the first decade, where both sides are still
            # representable. ADDITIVE: fires only when the default ladder left < 2
            # surviving probes (previously a guaranteed skip); the same shrink/boundedness
            # gates apply to the finer ladder's first/last deviations — nothing loosened.
            dc = _probe_devs([sgn * p for p in _f(3, 5, 7, 10, 14, 19, 25)])
        if len(dc) >= 2:
            first_dev = max(first_dev, dc[0]); last_dev = max(last_dev, dc[-1]); n_combos += 1
    if n_combos < 1:
        return (UNABLE, "asymptotic",
                f"unbound:{unbound_seen}" if unbound_seen else "domain")
    devs = [first_dev, last_dev]
    if kind == "O":                         # IsBigO: |f/g| must stay bounded (not blow up)
        # Two independent signals: an absolute 1e6 ceiling (catches genuine blow-up whose
        # `devs[0]` happens to start small/near-zero, where the ratio test alone is too
        # permissive) OR a stable RATIO between first/last (the real boundedness evidence —
        # |f/g| settling to a constant, however large that constant is). A high-ORDER
        # asymptotic remainder can have a legitimately huge but genuinely bounded O-constant
        # (e.g. (2n+1)! for large n, DLMF 6.12.4: devs[0]≈devs[-1]≈4e7 — flat, just big), so
        # the ceiling must not veto a case the ratio test already certifies as stable.
        ratio_stable = devs[-1] <= 4 * max(devs[0], mp.mpf(1))
        if ratio_stable and (devs[-1] < mp.mpf("1e6") or devs[-1] <= 4 * devs[0]):
            return ("PASS", "asymptotic", f"|f/g|@end={mp.nstr(devs[-1],4)} over {len(devs)}")
        return ("FAIL", "asymptotic", f"|f/g| unbounded: {mp.nstr(devs[-1],4)}")
    shrinking = devs[-1] < devs[0] or devs[-1] < mp.mpf("1e-12")
    if not shrinking:
        return ("FAIL", "asymptotic", f"dev@end={mp.nstr(devs[-1],4)} not shrinking")
    if devs[-1] < mp.mpf("1e-2"):
        return ("PASS", "asymptotic", f"dev@end={mp.nstr(devs[-1],4)} over {len(devs)}")
    return (UNABLE, "asymptotic", f"uncertified (dev@end={mp.nstr(devs[-1],4)})")


def _is_fourier(node):
    return isinstance(node, tuple) and node[0] == "app" and node[1] == ("var", "𝓕")


def handle_fourier(L, R, d):
    """(𝓕 f) = g, possibly with free parameters (e.g. b in e^{−πbx²}). Sample the params
    (complex ones restricted to Re>0, where the Gaussian integral converges) and a real eval
    point t, comparing (𝓕 f)(t) to g(t) via the mp.quad transform in `_callable`."""
    free = set(); collect_free(L, free); collect_free(R, free)
    binders = d["binders"]
    params = sorted(v for v in free if v in binders)
    cgrid = [mp.mpf(1), mp.mpf(2), mp.mpc("0.7", "0.4"), mp.mpc("1.5", "-0.8")]  # all Re>0
    rgrid = [mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf(2)]
    grids = [cgrid if binders[v] in ("C", "H") else rgrid for v in params]
    import itertools
    combos = list(itertools.product(*grids)) if grids else [()]
    pts = [mp.mpf("0.5"), mp.mpf(1), mp.mpf("1.7")]
    worst, ok = mp.mpf(0), 0
    for combo in combos[:6]:
        env = dict(zip(params, combo))
        gL, gR = _callable(L, env), _callable(R, env)
        if gL is None or gR is None:
            return (UNABLE, "fourier", "unsupported func")
        for t in pts:
            try:
                with _time_limit(EVAL_BUDGET):
                    a, b = gL(t), gR(t)
            except Exception:
                continue
            ok += 1
            worst = max(worst, abs(a - b) / max(mp.mpf(1), abs(a), abs(b)))
    if ok < 2:
        return (UNABLE, "fourier", "domain")
    return (("PASS" if worst < TOL_TRANSFORM else "FAIL"), "fourier",
            f"worst={mp.nstr(worst,4)} over {ok}")


def handle_hassum(args, d):
    """HasSum (fun n => body) S ⇒ check ∑ body == S over a ℕ-indexed series (reuse the
    `sum` AST node + sweep_eq, exactly as `∑'` does — inherits the trivial-zero guard)."""
    if len(args) != 2:
        return (UNABLE, "hassum", "arity")
    fn, S = args
    if fn[0] != "lam":
        return (UNABLE, "hassum", "non-lambda summand")
    sumnode = ("sum", fn[1], fn[2], "ℕ")
    v, det = sweep_eq(sumnode, S, d["binders"], d.get("constraints"))
    return (v, "hassum", det)


def handle_hasprod(args, d):
    """HasProd (fun k => body) P ⇒ check ∏ₖ body == P over a ℕ-indexed product (reuse the
    `prod` AST node + sweep_eq, exactly as `∏'` does). `HasProd f P ⇔ ∏ₖ f k = P`; the
    `prod` node truncates with `_bounded_nprod`, which RAISES (→ honest skip) unless the
    factors genuinely settle to 1, so a non-convergent product is dropped, never PASSed."""
    if len(args) != 2:
        return (UNABLE, "hasprod", "arity")
    fn, P = args
    if fn[0] != "lam":
        return (UNABLE, "hasprod", "non-lambda factor")
    prodnode = ("prod", fn[1], fn[2], "ℕ")
    v, det = sweep_eq(prodnode, P, d["binders"], d.get("constraints"))
    return (v, "hasprod", det)


def _series_tail_verdict(tf, nmax=600):
    """Convergence verdict for the |t_n| tail of a ℕ-indexed series — 'conv' / 'div' /
    'undecided'. Geometric ratio test (r̄ = mean tail ratio) with RAABE's refinement at
    the ratio → 1 boundary: n(1 − r_n) → ρ, converges if ρ > 1, diverges if ρ < 1 (the
    Gauss / p-series regime, e.g. ₂F₁ coefficients at x = 1 give ρ = Re(c−a−b)+1). A
    narrow undecided band around each threshold keeps borderline series (ρ → 1, the
    prime-reciprocal / harmonic case) an honest skip — never a fabricated verdict."""
    ts = []
    for n in range(nmax):
        try:
            ts.append(abs(mp.mpc(tf(n))))
        except Exception:
            ts.append(None)
    ratios = [(n, ts[n] / ts[n - 1]) for n in range(1, nmax)
              if ts[n] is not None and ts[n - 1] not in (None, 0)
              and mp.isfinite(ts[n]) and mp.isfinite(ts[n - 1]) and ts[n - 1] > 0]
    if len(ratios) < 20:
        return 'undecided'
    tail = ratios[-40:] if len(ratios) >= 60 else ratios[len(ratios) // 2:]
    rbar = sum(r for _, r in tail) / len(tail)
    if rbar < mp.mpf("0.98"):
        return 'conv'
    if rbar > mp.mpf("1.02"):
        return 'div'
    rho = sum(n * (1 - r) for n, r in tail) / len(tail)           # Raabe's test
    if rho > mp.mpf("1.05"):
        return 'conv'
    if rho < mp.mpf("0.95"):
        return 'div'
    return 'undecided'


def handle_summable(neg, arg, d, argstr):
    """Numerical convergence corroboration for `Summable (·)` / `¬ Summable (·)` — a
    Tier-1 strategy the blanket `Summable`-skip otherwise drops entirely. The summand's
    terms t_n are evaluated at successive ℕ indices and the |t_n| tail is ratio/Raabe
    tested (`_series_tail_verdict`).

    Positive `Summable`: corroborated PASS when ≥ 2 in-domain samples have a certifiably
    convergent tail. It NEVER FAILs from a divergent sample — an uncaptured convergence
    hypothesis (e.g. Re(c−a−b) > 0 for ₂F₁ at x = 1) lets the free parameter grid straddle
    the domain boundary, so a divergent point is treated as out-of-scope, not a refutation
    (cannot false-FAIL a true theorem). `¬ Summable`: symmetric, PASS on certified
    divergence at ≥ 2 samples. Undecidable tails stay honest skips. Corroboration, not
    proof (finite-N tail extrapolation). Scalar ℕ-indexed summands only — product-indexed
    (ℕ×ℕ) and prime-indexed series are skipped (string-guarded by the caller)."""
    if arg[0] == "lam":
        idx = arg[1]
        if not isinstance(idx, str) or (len(arg) > 3 and arg[3]):
            return (UNABLE, "summable", "multi/non-scalar index")
        body = arg[2]

        def mk_tf(env, _b=body, _i=idx):
            return lambda n: evaluate(_b, {**env, _i: mp.mpf(int(n))})
        free = set(); collect_free(body, free); free.discard(idx)
    elif arg[0] == "app":                          # point-free sequence (head args) : ℕ → scalar
        def mk_tf(env, _a=arg):
            return lambda n: evaluate(("app", _a[1], list(_a[2]) + [("num", int(n))]), env)
        free = set(); collect_free(arg, free)
    else:
        return (UNABLE, "summable", "unsupported summand shape")
    binders = d["binders"]; cons = d.get("constraints") or {}
    grids = []
    for v in sorted(free):
        base = binders.get(v, "R")
        if base in ("N", "Z"):
            grids.append((v, list(SAMPLES[base])[:3]))
        elif base in ("C", "H"):
            grids.append((v, list(SAMPLES["C"])[:3]))
        else:
            grids.append((v, list(_real_grid(cons.get(v)))[:4]))
    import itertools
    combos = list(itertools.product(*[g[1] for g in grids])) if grids else [()]
    envs = [dict(zip([g[0] for g in grids], combo)) for combo in combos][:12]
    conv = div = 0
    for env in envs:
        try:
            verd = _series_tail_verdict(mk_tf(env))
        except Exception:
            continue
        if verd == 'conv':
            conv += 1
        elif verd == 'div':
            div += 1
    if not neg:
        if conv >= 2:
            return ("PASS", "summable", f"convergent tail @ {conv}/{len(envs)} samples")
        return (UNABLE, "summable", f"tail undecided (conv={conv} div={div})")
    if div >= 2:
        return ("PASS", "not-summable", f"divergent tail @ {div}/{len(envs)} samples")
    return (UNABLE, "not-summable", f"tail undecided (conv={conv} div={div})")


# interval set-constructors: I<lo><hi>, lower char 'c'losed / 'o'pen, upper likewise; the
# ray forms (Ici/Ioi lower-only, Iic/Iio upper-only) handled in handle_mem.
_MEM_INTERVALS = {"Icc", "Ioo", "Ici", "Ioc", "Ico", "Iic", "Iio", "Ioi",
                  "Set.Icc", "Set.Ioo", "Set.Ici", "Set.Ioc", "Set.Ico",
                  "Set.Iic", "Set.Iio", "Set.Ioi"}


def handle_mem(elem, setnode, d):
    """`e ∈ Icc/Ioo/Ici/Iio/…` as a CONCLUSION → a one/two-sided inequality via sweep_ineq.
    Closed end → `≤`, open end → strict `<`. SOUNDNESS: a bare-VARIABLE element carries an
    uncapturable set-membership hypothesis on that variable (e.g. `x ∈ T.roots`), so sampling
    it freely would FAIL a true theorem — skip honestly; only computed expressions are run."""
    if elem[0] == "var":
        return (UNABLE, "membership", "free-variable element (uncapturable hypothesis)")
    if setnode[0] == "intrange":
        # `e ∈ Set.range ((↑) : ℤ → ℚ)` (or an ℕ-cast) — the 'e is an integer' predicate
        # (von Staudt–Clausen, DLMF 24.10): sweep e against its own nearest-integer
        # projection, so |e − nearint e| < tol must hold at EVERY sample. Reuses sweep_eq
        # unchanged — same exact gate, pole/cancellation guards, and honest skips (no
        # tolerance change); a genuinely fractional e (gap ≥ 1/2 somewhere) FAILs.
        v, det = sweep_eq(elem, ("nearint", elem, setnode[1]),
                          d["binders"], d.get("constraints"))
        return (v, "membership-int-range", det)
    if setnode[0] != "app" or setnode[1][0] != "var" or setnode[1][1] not in _MEM_INTERVALS:
        return (UNABLE, "membership", "non-interval set")
    bnd = setnode[1][1].split(".")[-1]
    args = setnode[2]
    lo = args[0] if len(args) >= 1 else None
    hi = args[1] if len(args) >= 2 else None
    lo_strict, hi_strict = (bnd[1] == "o"), (bnd[2] == "o" if len(bnd) == 3 else None)
    if bnd in ("Ici", "Ioi"):                 # lower ray only:  lo (≤|<) e
        hi = None
    elif bnd in ("Iic", "Iio"):               # upper ray only:  e (≤|<) hi
        hi, lo, hi_strict = lo, None, (bnd[1] == "o")
    dets = []
    for (op, a, b, tag) in ([("<" if lo_strict else "≤", lo, elem, "lo")] if lo is not None else []) + \
                           ([("<" if hi_strict else "≤", elem, hi, "hi")] if hi is not None else []):
        v, det = sweep_ineq(op, a, b, d["binders"], d.get("constraints"))
        dets.append(f"{tag}:{det}")
        if v != "PASS":
            return (v, "membership", "; ".join(dets))
    if not dets:
        return (UNABLE, "membership", "no bounds")
    return ("PASS", "membership", "; ".join(dets))


# ── '↔' between ∀-quantified equalities (DLMF 27.5 Möbius inversion) ─────────
# `(∀ n > 0, ∑ d ∈ n.divisors, f d = g n) ↔ ∀ n > 0, ∑ d ∈ n.divisors, μ(n/d)·g d = f n`
# is not a single sampleable equality — each direction of the '↔' is checked by WITNESS
# CONSTRUCTION instead: sample the assumed side's free arithmetic function at small random
# integers, CONSTRUCT the function that side defines pointwise from its defining equality
# (so the assumed side holds by construction), then verify the other side's equality at
# every n = 1..N_IFF. All arithmetic is exact-integer (small integer samples, μ ∈ {−1,0,1},
# divisor sums), so the standard TOL equality gate loses nothing. Only the exact shape
# `∀ v > 0, E = h v` on BOTH sides — each defining a DISTINCT function binder whose
# defining expression never references the function it defines — is run; any other shape,
# extra binder, uncaptured constraint, unbound symbol, or evaluation failure is an honest
# skip, never a fabricated verdict.
N_IFF = 50           # n-range 1..N_IFF per direction (divisor-closed: d ∣ n ⇒ d ≤ N_IFF)
IFF_TRIALS = 3       # independent random function witnesses per direction
_IFF_SEED = 2705     # fixed seed — deterministic across runs (DLMF §27.5)
_IFF_FORALL = re.compile(r"^∀\s+([^\s,:>()]+)\s*>\s*0\s*,\s*(.+)$", re.S)


def _split_top_iff(c):
    """(lhs, rhs) when `c` contains exactly ONE top-level '↔' (paren depth 0); else None."""
    depth, pos = 0, []
    for i, ch in enumerate(c):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "↔" and depth == 0:
            pos.append(i)
    if len(pos) != 1:
        return None
    return c[:pos[0]].strip(), c[pos[0] + 1:].strip()


def _split_top_and_text(c):
    """The members of a bracket-depth-0 '∧' conjunction, as raw text (a 1-element list
    when there is no top-level '∧'). Brackets `()`, `[]`, `{}` all count toward depth, so
    a '∧' inside a set-builder, a structure literal or a parenthesised group never splits.
    Text-level counterpart of the parsed ("and", …) node — needed for conclusions the
    tokenizer cannot reach at all (a '↔' member has no token)."""
    out, depth, cur = [], 0, ""
    for ch in c:
        if ch in "([{":
            depth += 1
            cur += ch
        elif ch in ")]}":
            depth -= 1
            cur += ch
        elif ch == "∧" and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [p.strip() for p in out]


_TOP_BINDER_HEADS = "∀∃∑∏⨆⨅⋃⋂λ"


def _opens_binder(s):
    """True when `s` opens a variable binder at bracket-depth 0 (`∀ j, …`, `∑ j, …`,
    `fun t => …`). Such a binder's body runs to the END of the enclosing expression, so a
    depth-0 '∧' AFTER it lies INSIDE the binder body: splitting there would cut a member
    out of the binder's scope (`∀ j, P j ∧ Q j` is one quantified conjunction, not two
    conjuncts). Used to refuse exactly those splits; a binder inside the LAST member
    swallows nothing, and a parenthesised `(∀ j, …)` is not at depth 0 at all."""
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0:
            if ch in _TOP_BINDER_HEADS:
                return True
            if s.startswith("fun", i) and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] == "_")) \
                    and not s[i + 3:i + 4].isalnum():
                return True
    return False


def _strip_outer_parens(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    return s           # the leading '(' does not wrap the whole string
        s = s[1:-1].strip()
    return s


def _iff_side(side):
    """One side of the '↔': `∀ v > 0, L = R` → (v, L, R); None on any other shape.
    May raise Unparseable (the caller reports it as the honest skip)."""
    m = _IFF_FORALL.match(_strip_outer_parens(side))
    if not m:
        return None
    ast = parse(m.group(2))
    if ast[0] != "eq":
        return None
    return (m.group(1), ast[1], ast[2])


def _refs_var(node, name):
    """True if the AST references `name` as a variable/application head anywhere."""
    if isinstance(node, tuple):
        if node[0] == "var" and node[1] == name:
            return True
        return any(_refs_var(c, name) for c in node[1:])
    if isinstance(node, list):
        return any(_refs_var(c, name) for c in node)
    return False


def _iff_defined(v, L, R, binders):
    """If one side of `L = R` is exactly the bare application `h v` of a function binder h
    and the OTHER side never references h, the equality DEFINES h pointwise at v:
    return (h, defining-expr). None otherwise."""
    for bare, expr in ((L, R), (R, L)):
        if (bare[0] == "app" and bare[1][0] == "var" and bare[1][1] in binders
                and bare[2] == [("var", v)] and not _refs_var(expr, bare[1][1])):
            return (bare[1][1], expr)
    return None


def _iff_table_fn(tab, what):
    """A ℕ-indexed integer table as a callable function binder; a lookup outside the
    constructed range drops honestly (never a fabricated value)."""
    def fn(x):
        key = int(mp.nint(x))
        if key not in tab:
            raise Unparseable(f"iff-witness range ({what} {key})")
        return mp.mpf(tab[key])
    return fn


def _iff_direction(rng, src, tgt, binders):
    """One implication of the '↔'. `src` = (v, h, E): the ASSUMED side `∀ v > 0, E = h v`,
    whose defining equality constructs h pointwise from the randomly sampled other
    function binder(s); `tgt` = (w, L, R): the side to VERIFY at every n = 1..N_IFF.
    Returns (verdict, detail)."""
    (v, h, E), (w, L, R) = src, tgt
    sampled = sorted(b for b in binders if b != h)
    for t in range(IFF_TRIALS):
        env = {"_binders": binders}
        for s in sampled:              # small random integers — sign changes and zeros included
            env[s] = _iff_table_fn({m: rng.randint(-9, 9) for m in range(1, N_IFF + 1)}, s)
        htab = {n: evaluate(E, {**env, v: mp.mpf(n)}) for n in range(1, N_IFF + 1)}
        env[h] = _iff_table_fn(htab, h)
        for n in range(1, N_IFF + 1):
            e = {**env, w: mp.mpf(n)}
            diff = abs(evaluate(L, e) - evaluate(R, e))
            if not diff <= TOL:
                return ("FAIL", f"witness {t + 1}, n={n}, |Δ|={mp.nstr(diff, 6)}")
    return ("PASS", f"{IFF_TRIALS} witnesses × n=1..{N_IFF}")


# ── '↔' between pointwise BOOLEAN-evaluable propositions (DLMF 27.9) ─────────
# `legendreSym p a = 1 ↔ IsSquare (a : ZMod p)` (the quadratic-residue criterion) is an
# equivalence of two DECIDABLE statements at each sample point — neither a numeric
# equality nor the ∀-quantified Möbius shape below. Check it by TRUTH-TABLE AGREEMENT:
# sample the binders on the standard hypothesis-honoring grids, evaluate each side to a
# bool, and PASS iff the sides agree at every decided sample (one disagreement is a
# genuine counterexample → FAIL). The two sides stay INDEPENDENT: `IsSquare` on ZMod n
# is a decorrelated brute-force residue search, never the Legendre-symbol binding, so
# agreement is genuine cross-validation. Honesty guards (never a guessed bool):
#   • a numerically ambiguous `=` (gap between the exact gate and the clear-≠ margin),
#     a non-integer value where exact ZMod arithmetic is required, or any evaluation
#     error drops the point;
#   • hypotheses are honored per point (`_pairs`, and a ZMod-AWARE `≠ 0` filter — the
#     ℤ-lift check in _nonzero_ok cannot see that (5 : ZMod 5) = 0);
#   • < 2 decided points → undersampled skip;
#   • decided points all sharing one truth value never exercised the equivalence
#     (`False ↔ False` holds for any two wrong statements) → honest skip, no hollow PASS.
_BOOL_FALSE_GAP = mp.mpf("1e-6")   # a relative gap this large is a CLEAR numeric ≠


def _bool_prop(ast):
    """The boolean-evaluable proposition of one '↔' side: an `=`/`≠` relation, or a
    supported decidable predicate application (IsSquare/Even/Odd/Nat.Prime — the last
    bound to sympy.isprime, ob._isprime). The dotted sugar `p.Prime` is one identifier
    token to the parser (('var', 'p.Prime')); normalize it to the applied form
    `Nat.Prime p` so the operand scan and eval see a single shape. None on any other
    shape — the caller then falls through to the witness-construction iff path."""
    a = ast[1] if ast[0] == "expr" else ast
    if a[0] in ("eq", "ne"):
        return a
    if (a[0] == "app" and a[1][0] == "var"
            and a[1][1] in ("IsSquare", "Even", "Odd", "Nat.Prime")
            and len(a[2]) == 1):
        return a
    if (a[0] == "var" and a[1].endswith(".Prime")
            and re.fullmatch(r"[A-Za-zα-ω]\w*", a[1][:-len(".Prime")])):
        return ("app", ("var", "Nat.Prime"), [("var", a[1][:-len(".Prime")])])
    return None


def _bool_prop_operands(a):
    """The numeric operand subtrees of a `_bool_prop` node (for the free-variable scan)."""
    return [a[1], a[2]] if a[0] in ("eq", "ne") else list(a[2])


def _bool_prop_eval(a, env):
    """Evaluate a `_bool_prop` node to True/False at the sampled env. Raises (→ the
    point drops honestly) on anything undecidable — see the honesty guards above."""
    if a[0] in ("eq", "ne"):
        L, R = a[1], a[2]
        zmods = set(); _zmod_moduli(L, zmods); _zmod_moduli(R, zmods)
        if zmods:                    # the `=` lives in ZMod n → congruence of the ℤ-lifts
            if len(zmods) > 1:
                raise Unparseable("iff-bool mixed ZMod moduli")
            tok = next(iter(zmods))
            nn = _near_int(mp.mpf(int(tok)) if tok.isdigit() else env.get(tok, mp.nan))
            ia, ib = _near_int(evaluate(L, env)), _near_int(evaluate(R, env))
            if nn is None or nn < 2 or ia is None or ib is None:
                raise Unparseable("iff-bool ZMod non-integer")
            val = (ia - ib) % nn == 0
        else:
            x, y = evaluate(L, env), evaluate(R, env)
            gap = abs(x - y) / max(mp.mpf(1), abs(x), abs(y))
            if gap < TOL:
                val = True
            elif gap > _BOOL_FALSE_GAP:
                val = False
            else:                    # numerically ambiguous — never guess a truth value
                raise Unparseable("iff-bool ambiguous =")
        return (not val) if a[0] == "ne" else val
    nm, arg = a[1][1], a[2][0]
    if nm == "IsSquare" and arg[0] == "zmodcast":
        # IsSquare on ZMod n — DECORRELATED brute force over every residue class
        # (deliberately NOT via the Legendre-symbol binding: the two '↔' sides must
        # stay independent for the agreement to be evidence).
        tok = arg[1]
        nn = _near_int(mp.mpf(int(tok)) if tok.isdigit() else env.get(tok, mp.nan))
        iv = _near_int(evaluate(arg[2], env))
        if nn is None or nn < 1 or iv is None:
            raise Unparseable("iff-bool ZMod non-integer")
        return any((x * x - iv) % nn == 0 for x in range(nn))
    v = _near_int(evaluate(arg, env))
    if v is None:
        raise Unparseable("iff-bool non-integer predicate arg")
    if nm == "IsSquare":             # ℤ: a perfect square (negatives never match r·r)
        r = _math.isqrt(abs(v))
        return r * r == v
    if nm == "Nat.Prime":            # primality — sympy.isprime (deterministic here);
        return ob._isprime(v)        # raises without sympy → the point drops honestly
    return v % 2 == 0 if nm == "Even" else v % 2 == 1


def _bool_nonzero_ok(env, constraints):
    """`h : e ≠ 0` filter for the bool-iff path, ZMod-AWARE: a hypothesized-nonzero
    `(a : ZMod p)` vanishes exactly when p ∣ a — the ℤ-lift numeric check in
    `_nonzero_ok` cannot see that (the lift 5 is nonzero while (5 : ZMod 5) = 0), and
    scoring such an out-of-domain point compares Lean's junk-value branch, fabricating
    a counterexample to a proven statement. Non-ZMod entries defer unchanged to the
    standard `_nonzero_ok` numeric gate; an unevaluable entry imposes no filter."""
    residual = []
    for s in (constraints or {}).get('_nonzero', []):
        try:
            ast = parse(s)
            node = ast[1] if ast and ast[0] == "expr" else ast
        except Exception:
            node = None
        if node is not None and node[0] == "zmodcast":
            tok = node[1]
            try:
                nn = _near_int(mp.mpf(int(tok)) if tok.isdigit() else env.get(tok, mp.nan))
                iv = _near_int(evaluate(node[2], env))
            except Exception:
                continue             # not evaluable here — no filter (mirrors _nonzero_ok)
            if nn is not None and nn >= 1 and iv is not None and iv % nn == 0:
                return False         # (e : ZMod n) = 0 here — outside the stated domain
            continue
        residual.append(s)
    return _nonzero_ok(env, {**(constraints or {}), '_nonzero': residual})


def _iff_bool(lhs, rhs, d):
    """Truth-table agreement check for a pointwise-boolean '↔' (block comment above).
    Returns None when either side is not a supported boolean proposition — the caller's
    witness-construction path then proceeds exactly as before (strictly additive)."""
    try:
        A = _bool_prop(parse(_strip_outer_parens(lhs)))
        B = _bool_prop(parse(_strip_outer_parens(rhs)))
    except Exception:
        return None
    if A is None or B is None:
        return None
    binders, constraints = d["binders"], d.get("constraints") or {}
    free = set()
    for node in _bool_prop_operands(A) + _bool_prop_operands(B):
        collect_free(node, free)
    # SOUNDNESS: every free symbol must be a declared binder (or the indeterminate) —
    # an unknown name is never sampled as a fresh real (same rule as sweep_eq).
    unbound = [v for v in sorted(free)
               if v != IND and v not in binders and _reg_resolve(v) is None]
    if unbound:
        return (UNABLE, "iff-bool", f"unbound:{unbound[0]}")
    free = {v for v in free if v == IND or v in binders}   # drop bare-fn registry refs
    if not free:
        return None                  # nothing to sample — not a pointwise check
    import itertools
    grids = [(v, _grid(v, d)) for v in sorted(free)]
    names = [g[0] for g in grids]
    combos = list(itertools.product(*[g[1] for g in grids]))[:36]
    intvars = {v for v, t in binders.items() if t in ("Z", "N")}
    decided, seen_true, seen_false, unbound_head = 0, False, False, None
    for combo in combos:
        env = dict(zip(names, combo))
        env["_intvars"] = intvars
        env["_binders"] = binders
        env["_zmodmod"] = constraints.get('_zmodmod', {})
        if not _pairs_ok(env, constraints):
            continue
        if not _bool_nonzero_ok(env, constraints):
            continue                 # a hypothesized-nonzero expr vanishes — out of domain
        try:
            with _time_limit(EVAL_BUDGET):
                va, vb = _bool_prop_eval(A, env), _bool_prop_eval(B, env)
        except _EvalTimeout:
            return (UNABLE, "iff-bool", "eval-timeout")
        except Unparseable as e:
            unbound_head = unbound_head or _unbound_head_of(e)
            continue
        except (ZeroDivisionError, ValueError, OverflowError, TypeError):
            continue
        decided += 1
        seen_true, seen_false = seen_true or va, seen_false or (not va)
        if va != vb:
            pt = ", ".join(f"{n}={mp.nstr(env[n], 6)}" for n in names)
            return ("FAIL", "iff-bool", f"sides disagree at {pt}: LHS={va} RHS={vb}")
    if decided < 2:
        return (UNABLE, "iff-bool",
                f"unbound:{unbound_head}" if unbound_head else "undersampled/domain")
    if not (seen_true and seen_false):
        return (UNABLE, "iff-bool", "single-valued/unexercised")
    return ("PASS", "iff-bool", f"agree at {decided}pts (both truth values exercised)")


# ── '↔' between an ODE-SOLUTION PREDICATE and a TRANSFORMED equation ──────────────
# DLMF 31.2.6 (trigonometric form) and 31.2.8 (Jacobi elliptic form) both read
#
#     IsHeunSolution a q α β γ δ w z(t)  ↔  <equation in t> = 0,
#
# with `w : ℂ → ℂ` a ∀-quantified ABSTRACT analytic function.  Neither side is a
# decidable boolean of the kind `_iff_bool` supports (the LHS is a defined predicate on a
# function binder; the RHS an exact equality `E = 0` in that same binder), so the row
# skipped.  It is nevertheless checkable, because BOTH branches of the truth table are
# reachable by instantiating the ∀ at concrete ANALYTIC witnesses:
#
#   TRUE  branch — `heunFn a q α β γ δ`, the local Heun function (DLMF 31.3.1), which
#                  solves 31.2.1 identically inside its Maclaurin disc |z| < min(1,|a|);
#   FALSE branch — the canonical entire witnesses of `_entire_wit_ast`, which do not.
#
# Every witness satisfies the row's own hypotheses on w (analyticity only — enforced at
# extraction time by `_solution_fn_witness`), so this is the ordinary refutation-oracle
# instantiation used throughout: a disagreement between the two sides at a witness
# DISPROVES the ∀-statement.  Measured separation between the branches is ~30 orders of
# magnitude (relative residual ~1e-31 at heunFn vs ~1e0 at an entire witness), so the
# boolean read-off needs no fine tolerance: a sample landing in the band between the two
# gates is DROPPED, never guessed.
_SOLIFF_TRUE_EPS = mp.mpf("1e-16")    # relative residual below this ⇒ that side HOLDS
_SOLIFF_FALSE_EPS = mp.mpf("1e-4")    # above this ⇒ that side FAILS; between ⇒ drop sample
_SOLIFF_MAX_ENVS = 6                  # parameter tuples per row
_SOLIFF_PT_LADDER = ("0.11", "0.19", "0.27", "0.36")   # small-modulus point candidates


def _subst_var_lam(node, name, lam):
    """Replace every `("var", name)` in an AST by the witness LAMBDA `lam` (instantiating
    the ∀-quantified function binder).  A pure structural substitution — `name` is a
    binder of the theorem, so no capture is possible with the witness's private bound
    variable."""
    if isinstance(node, tuple):
        if node[0] == "var" and node[1] == name:
            return lam
        return (node[0],) + tuple(_subst_var_lam(c, name, lam) for c in node[1:])
    if isinstance(node, list):
        return [_subst_var_lam(c, name, lam) for c in node]
    return node


def _add_terms(node, acc):
    """Top-level additive terms of an expression tree, for the homogeneity SCALE of a
    residual: `A + B - C` ↦ [A, B, C].  An equation `E = 0` is homogeneous in the unknown,
    so an ABSOLUTE residual is meaningless — it must be scored against the size of the
    terms that cancel (the same normalization `handle_heun_solution` uses)."""
    if isinstance(node, tuple) and node[0] == "bin" and node[1] in ("+", "-"):
        _add_terms(node[2], acc)
        _add_terms(node[3], acc)
        return acc
    acc.append(node)
    return acc


def _soliff_side_holds(residual, terms):
    """Read a side of the `↔` off its residual: True (holds), False (fails), or None —
    DROP the sample — when the relative residual lands between the two gates and the
    boolean cannot be decided without guessing."""
    scale = max([abs(t) for t in terms] + [mp.mpf("1e-300")])
    rel = abs(residual) / scale
    if rel < _SOLIFF_TRUE_EPS:
        return True, rel
    if rel > _SOLIFF_FALSE_EPS:
        return False, rel
    return None, rel


def _soliff_point_grids(free, ptvars, d):
    """Sampling grids: the ordinary per-binder grid, EXTENDED for the variables the
    solution point `z` depends on by a small-modulus ladder.  The TRUE witness `heunFn` is
    defined only inside its Maclaurin disc, so without such candidates every heunFn sample
    would drop and the TRUE branch would never be exercised.  These are CANDIDATES only —
    each is admitted solely by the row's own stated hypotheses (`_pairs_ok`/`_nonzero_ok`)
    plus evaluability, exactly as `_heun_z_candidates` proposes points for
    `handle_heun_solution`.  The FALSE witnesses are entire and are scored on the ordinary
    grid as well, so the point set is only ever ENLARGED, never restricted."""
    grids = []
    for v in sorted(free):
        g = list(_domain_reject_grid(v, d.get("constraints") or {}, d["binders"])
                 or _grid(v, d))
        if v in ptvars and d["binders"].get(v) in ("C", "R"):
            small = [mp.mpf(s) for s in _SOLIFF_PT_LADDER]
            if d["binders"].get(v) == "C":
                small += [mp.mpf(s) * mp.e ** (mp.mpc(0, 1) * mp.pi / 5) for s in _SOLIFF_PT_LADDER]
            g = small + g
        grids.append((v, g))
    # DE-COINCIDENCE (the rotation `handle_heun_solution` and sweep_eq already apply):
    # rotate each grid by a distinct offset — a PERMUTATION, introducing no new sample
    # value — so the first tuples do not set every parameter to the same number, where an
    # identity true only on the diagonal could pass by collapse.
    for j, (v, gr) in enumerate(grids):
        if len(gr) > 1:
            r = j % len(gr)
            grids[j] = (v, gr[r:] + gr[:r])
    return grids


def handle_solution_iff(lhs, rhs, d):
    """`IsHeunSolution a q α β γ δ w z ↔ <transformed equation> = 0` at an ABSTRACT
    analytic `w` (block comment above).  Returns None — the caller keeps its prior honest
    skip, byte for byte — for every shape this does not cover: a non-`IsHeunSolution`
    head, a wrong arity, a concrete (non-binder) solution slot, a binder carrying a
    hypothesis that is not pure analyticity (`_solfn` unset), or an RHS that is not an
    equation."""
    binders, cons = d["binders"], d.get("constraints") or {}
    solfn = cons.get('_solfn') or {}
    if not solfn:
        return None
    try:
        A = parse(_strip_outer_parens(lhs))
        B = parse(_strip_outer_parens(rhs))
    except Unparseable:
        return None
    if A[0] == "expr":
        A = A[1]
    if not (isinstance(A, tuple) and A[0] == "app" and A[1][0] == "var"
            and A[1][1].split(".")[-1] == "IsHeunSolution" and len(A[2]) == 8):
        return None
    if B[0] != "eq":
        return None
    args = A[2]
    fnode = args[6]
    if not (isinstance(fnode, tuple) and fnode[0] == "var" and solfn.get(fnode[1])):
        return None
    wname = fnode[1]
    # The analyticity hypothesis must be stated AT THE DISPLAY'S OWN SOLUTION POINT: the
    # local Heun witness is analytic in its Maclaurin disc, and only a hypothesis pinned to
    # the point actually sampled is one the witness demonstrably satisfies there.
    hyp_pt = solfn[wname]
    if isinstance(hyp_pt, str):
        try:
            hp = parse(hyp_pt)
        except Unparseable:
            return None
        if (hp[1] if hp[0] == "expr" else hp) != args[7]:
            return None
    # SOUNDNESS: every other free symbol must be a declared binder or registry-bound —
    # an unknown name is never sampled as a fresh value (the rule of sweep_eq/_iff_bool).
    free = set()
    for nd in list(args) + [B[1], B[2]]:
        collect_free(nd, free)
    unbound = [v for v in sorted(free)
               if v != wname and v not in binders and _reg_resolve(v) is None]
    if unbound:
        return (UNABLE, "solution-iff", f"unbound:{unbound[0]}")
    ptvars = set()
    collect_free(args[7], ptvars)
    defeq = []
    for _dv, _dexpr in cons.get('_defeq', []):
        try:
            _da = parse(_dexpr)
            defeq.append((_dv, _da[1] if _da and _da[0] == "expr" else _da))
        except Exception:
            return None                        # an unparsable pin would leave ε unsampled
    params = sorted((free & set(binders)) - {wname} - {v for v, _ in defeq})
    grids = _soliff_point_grids(params, ptvars, d)
    intvars = {v for v, t in binders.items() if t in ("Z", "N")}
    import itertools
    envs = []
    for combo in itertools.islice(itertools.product(*[g[1] for g in grids]), 4096):
        env = dict(zip([g[0] for g in grids], combo))
        env["_intvars"] = intvars
        env["_binders"] = binders
        try:
            for _dv, _dast in defeq:
                env[_dv] = evaluate(_dast, env)
        except Exception:
            continue
        if not _pairs_ok(env, cons) or not _nonzero_ok(env, cons):
            continue                           # outside the row's OWN stated hypotheses
        envs.append(env)
        if len(envs) >= _SOLIFF_MAX_ENVS:
            break
    # the TRUE witness: `fun ζ => heunFn a q α β γ δ ζ`, the parameter slots spliced from
    # the row's own LHS arguments (so it is the local solution OF THIS equation)
    true_wit = ("lam", "_soliffz",
                ("app", ("var", "heunFn"), list(args[:6]) + [("var", "_soliffz")]))
    wits = [("heunFn", true_wit)] + [(f"entire{i}", _entire_wit_ast(i)) for i in range(3)]
    lterms_n = [_add_terms(B[1], []), _add_terms(B[2], [])]
    decided, seen_true, seen_false, dropped = 0, False, False, 0
    for env in envs:
        for wnm, wit in wits:
            Bl = _subst_var_lam(B[1], wname, wit)
            Br = _subst_var_lam(B[2], wname, wit)
            g = _callable(wit, env)
            if g is None:
                return None
            try:
                with _time_limit(EVAL_BUDGET):
                    av, qv = evaluate(args[0], env), evaluate(args[1], env)
                    alv, bev = evaluate(args[2], env), evaluate(args[3], env)
                    gav, dev = evaluate(args[4], env), evaluate(args[5], env)
                    zv = evaluate(args[7], env)
                    # LHS = the DEFINED predicate `IsHeunSolution`, unfolded to its
                    # cleared-denominator Heun equation 31.2.1 (Frameworks/Heun/Local.lean)
                    t1 = zv * (zv - 1) * (zv - av) * mp.diff(g, zv, 2)
                    t2 = (gav * (zv - 1) * (zv - av) + dev * zv * (zv - av)
                          + (alv + bev + 1 - gav - dev) * zv * (zv - 1)) * mp.diff(g, zv, 1)
                    t3 = (alv * bev * zv - qv) * g(zv)
                    lh, lrel = _soliff_side_holds(t1 + t2 + t3, [t1, t2, t3])
                    # RHS = the transformed equation, evaluated verbatim from its own AST
                    rterms = [evaluate(_subst_var_lam(t, wname, wit), env)
                              for side in lterms_n for t in side]
                    rh, rrel = _soliff_side_holds(evaluate(Bl, env) - evaluate(Br, env), rterms)
            except _EvalTimeout:
                return (UNABLE, "solution-iff", "eval-timeout")
            except (Unparseable, ZeroDivisionError, ValueError, OverflowError,
                    TypeError, ArithmeticError):
                dropped += 1
                continue                       # out of the witness's domain — honest drop
            if lh is None or rh is None:
                dropped += 1
                continue                       # residual in the undecidable band — drop
            decided += 1
            seen_true, seen_false = seen_true or lh, seen_false or (not lh)
            if lh != rh:
                pt = ", ".join(f"{n}={mp.nstr(env[n], 6)}" for n in params)
                return ("FAIL", "solution-iff",
                        f"sides disagree at w={wnm}, {pt}: LHS={lh} (rel={mp.nstr(lrel, 4)}) "
                        f"RHS={rh} (rel={mp.nstr(rrel, 4)})")
    if decided < 2:
        return (UNABLE, "solution-iff", f"undersampled/domain (dropped {dropped})")
    if not (seen_true and seen_false):
        return (UNABLE, "solution-iff", "single-valued/unexercised")
    return ("PASS", "solution-iff",
            f"agree at {decided}pts (both truth values exercised, {dropped} dropped)")


# ── '↔' between a DEFINED ODE-solution PREDICATE and the printed differential equation ──
# DLMF §31.12 prints each confluent Heun equation in RATIONAL-coefficient form
# (31.12.1: `w'' + (γ/z + δ/(z−1) + ε) w' + (αz−q)/(z(z−1)) w = 0`), while the framework
# predicate `FLMF.Heun.IsConfluentHeunSolution` carries the CLEARED-denominator polynomial
# form; the surface theorems heun_31_12_1–4 (Ch31GeneralFuchsianEquation.lean) assert the two
# are equivalent off the finite singular points. Neither `_iff_bool` (a solution predicate is
# not a decidable arithmetic proposition) nor the `∀ n > 0` witness route applies, so these
# rows skipped as `uncaptured constraints` / `side not ∀ v > 0, L = R`.
#
# THE CHECK. δ-unfold the predicate from ITS OWN Lean `def`, read out of the FLMF source tree
# at check time (`_prop_defs`) — never a transcription and never a name-keyed numeric binding,
# so the comparison is literally "the definition FLMF gives the symbol" against "the equation
# DLMF prints", which is exactly the row's fidelity question. That yields a residual `F` (the
# predicate) beside the display's residual `E`; both involve the abstract solution `w` only
# through `w z`, `w' z`, `w'' z`.
#
# Each residual is a LINEAR FUNCTIONAL of that triple, and its coefficient vector is extracted
# by evaluating at the polynomial witnesses `1, t, t²` — whose (w, w′, w″)(z) are (1,0,0),
# (z,1,0), (z²,2z,2) — and solving the resulting triangular system. Linearity is then VERIFIED
# at two further independent witnesses (t³ and eᵗ); a residual that is not linear in the triple
# is outside this route and the handler returns None, leaving the caller's prior honest skip.
#
# Because the theorem quantifies over ALL `w : ℂ → ℂ` (hypothesis-free up to analyticity — the
# `_solfn` admissibility flag) and every triple (w, w′, w″)(z) is realised by an ENTIRE quadratic
# polynomial, the `↔` at a sample says exactly that the two functionals have the SAME KERNEL,
# i.e. a = m·b with m ≠ 0. Scoring per sample:
#   • proportional, and CONFIRMED by direct evaluation at two concrete entire witnesses — a
#     quadratic in ker(a) (both residuals ≈ 0: the True/True row of the truth table) and a
#     generic quadratic (both residuals ≉ 0: the False/False row) — the sample AGREES;
#   • not proportional — a counterexample witness is CONSTRUCTED (a quadratic in ker(a)∖ker(b)
#     or ker(b)∖ker(a)) and both residuals are evaluated directly at it; the row FAILs only when
#     that direct evaluation confirms one side holds while the other does not, and the witness
#     and both residuals are reported verbatim;
#   • anything numerically ambiguous (a residual between the agreement tolerance and the
#     clear-nonzero margin), non-linear, undersampled, or with only one truth value exercised
#     returns None — the caller's existing honest skip stands, never a guessed verdict.
# Nothing is loosened: hypotheses are honored per sample by the standard `_pairs_ok` /
# `_nonzero_ok` filters, the agreement gate is a fixed relative tolerance well inside the
# observed dps-30 accuracy, and no PASS is issued without both truth values exercised.
_ODE_AGREE = mp.mpf("1e-14")     # relative deviation counted as an exact zero
_ODE_CLEAR = mp.mpf("1e-6")      # relative magnitude counted as a clear non-zero
_ODE_COMBOS = 16                 # sampled parameter combinations (deterministic seed)
_ODE_SEED = 2705
# A `def … : Prop :=` body containing any BINDER is outside this route (the substitution below
# is capture-free only for binder-free bodies).
_ODE_NO_UNFOLD = ("λ", "fun ", "∑", "∏", "∫", "∀", "∃", "⨆", "⨅", "⋃", "⋂", "if ", "match ")
_PROP_DEFS = None                # lazily built {name: (head, body)}; ambiguous names dropped


def _prop_defs():
    """Index every `def <name> (explicit args) : Prop := <indented body>` in the FLMF source
    tree, once. A name defined more than once is dropped (an ambiguous unfold is never
    guessed). Definitions with implicit/instance argument groups do not match the explicit-`(`
    head pattern and are simply absent — such a row keeps its honest skip."""
    global _PROP_DEFS
    if _PROP_DEFS is None:
        pat = re.compile(r'^(?:noncomputable\s+)?def\s+([A-Za-zα-ω][\w\'′]*)\s+'
                         r'((?:\([^()]*\)\s*)+):\s*Prop\s*:=[ \t]*\n((?:[ \t]+\S.*\n)+)', re.M)
        hits = {}
        try:
            files = sorted(ROOT.parent.rglob("*.lean"))
        except OSError:
            files = []
        for f in files:
            try:
                text = f.read_text(encoding="utf-8")
            except OSError:
                continue
            for m in pat.finditer(text):
                hits.setdefault(m.group(1), []).append((m.group(2), m.group(3)))
        _PROP_DEFS = {k: v[0] for k, v in hits.items() if len(v) == 1}
    return _PROP_DEFS


def _subst_vars(node, mapping):
    """Simultaneous variable→AST substitution (capture-free: applied only to binder-free
    definition bodies, see `_ODE_NO_UNFOLD`)."""
    if isinstance(node, tuple):
        if node[0] == "var" and node[1] in mapping:
            return mapping[node[1]]
        return (node[0],) + tuple(_subst_vars(c, mapping) for c in node[1:])
    if isinstance(node, list):
        return [_subst_vars(c, mapping) for c in node]
    return node


def _prop_def_unfold(leaf, args):
    """δ-unfold `leaf args` from the Lean `def` of `leaf`, returning its body AST with the
    formal parameters replaced by the ACTUAL argument ASTs — or None (arity mismatch, a
    non-equation body, a binder in the body, an unparsed body, an unknown/ambiguous name)."""
    rec = _prop_defs().get(leaf)
    if rec is None:
        return None
    head, body_src = rec
    if any(tok in body_src for tok in _ODE_NO_UNFOLD):
        return None
    params = []
    for g in re.finditer(r'\(([^()]*)\)', head):
        inner = g.group(1)
        if ":" not in inner:
            return None
        nms = inner.split(":")[0].split()
        if not all(re.fullmatch(r'[A-Za-zα-ωΑ-Ω][\w′]*', n) for n in nms):
            return None
        params += nms
    if len(params) != len(args):
        return None
    try:
        ast = parse(" ".join(body_src.split()))
    except Exception:
        return None
    if not (isinstance(ast, tuple) and ast[0] == "eq"):
        return None
    return _subst_vars(ast, dict(zip(params, list(args))))


def _ode_w_points(node, wvar, pts):
    """True iff EVERY occurrence of `wvar` in `node` is `wvar pt`, `deriv wvar pt` or
    `deriv (deriv wvar) pt` — the only shapes this route models. Collects the evaluation
    points `pt` into `pts` (keyed by their printed form, so the AST need not be hashable)."""
    if isinstance(node, tuple):
        if node[0] == "var":
            return node[1] != wvar
        if node[0] == "app" and node[1] == ("var", wvar):
            if len(node[2]) != 1:
                return False
            pts[repr(node[2][0])] = node[2][0]
            return _ode_w_points(node[2][0], wvar, pts)
        if node[0] == "app" and node[1] == ("var", "deriv") and len(node[2]) == 2:
            base, depth = node[2][0], 0
            while (isinstance(base, tuple) and base[0] == "app"
                   and base[1] == ("var", "deriv") and len(base[2]) == 1):
                base, depth = base[2][0], depth + 1
            if base == ("var", wvar):
                if depth > 1:                # only w′ and w″ are modelled
                    return False
                pts[repr(node[2][1])] = node[2][1]
                return _ode_w_points(node[2][1], wvar, pts)
        return all(_ode_w_points(c, wvar, pts) for c in node[1:])
    if isinstance(node, list):
        return all(_ode_w_points(c, wvar, pts) for c in node)
    return True


_ODE_T = ("var", "_odet")                                   # private witness variable
_ODE_W1 = ("num", 1)                                        # w = 1        ↦ (w,w′,w″)=(1,0,0)
_ODE_WT = _ODE_T                                            # w = t        ↦ (z,1,0)
_ODE_WT2 = ("bin", "*", _ODE_T, _ODE_T)                     # w = t²       ↦ (z²,2z,2)
_ODE_WT3 = ("bin", "*", ("bin", "*", _ODE_T, _ODE_T), _ODE_T)          # linearity probe
_ODE_WEXP = ("app", ("var", "Complex.exp"), [_ODE_T])                  # linearity probe
_ODE_WQUAD = ("bin", "+", ("bin", "+", ("var", "_odec0"),
                           ("bin", "*", ("var", "_odec1"), _ODE_T)),
              ("bin", "*", ("var", "_odec2"), ("bin", "*", _ODE_T, _ODE_T)))


def _ode_eval(res, wvar, body, env):
    """Evaluate a residual with the solution binder instantiated at the entire witness
    `fun t => body` (spliced as a lambda, reaching the existing β-reduction / nested-`deriv`
    paths in `evaluate`), under the standard per-sample evaluation budget."""
    with _time_limit(EVAL_BUDGET):
        return evaluate(_subst_vars(res, {wvar: ("lam", "_odet", body)}), env)


def _ode_coeffs(res, wvar, env, z):
    """(coefficients of the residual as a linear functional of (w″,w′,w)(z), its scale, the
    relative linearity-check deviation at the independent witnesses t³ and eᵗ)."""
    r0 = _ode_eval(res, wvar, _ODE_W1, env)
    r1 = _ode_eval(res, wvar, _ODE_WT, env)
    r2 = _ode_eval(res, wvar, _ODE_WT2, env)
    a0 = r0
    a1 = r1 - a0 * z
    a2 = (r2 - 2 * z * a1 - z ** 2 * a0) / 2
    sc = max(abs(a2), abs(a1), abs(a0))
    r3, rE = _ode_eval(res, wvar, _ODE_WT3, env), _ode_eval(res, wvar, _ODE_WEXP, env)
    p3 = 6 * z * a2 + 3 * z ** 2 * a1 + z ** 3 * a0
    pE = (a2 + a1 + a0) * mp.e ** z
    lin = max(abs(r3 - p3) / max(abs(r3), sc * max(abs(z), mp.mpf(1)) ** 3, mp.mpf(1)),
              abs(rE - pE) / max(abs(rE), sc * abs(mp.e ** z), mp.mpf(1)))
    return (a2, a1, a0), sc, lin


def _ode_quad_env(t, z, env):
    """env extended with the coefficients of the entire quadratic `w` realising the prescribed
    triple `t = (w″(z), w′(z), w(z))` — every such triple is realised, which is what makes
    kernel comparison equivalent to the ∀-quantified `↔`."""
    c2 = t[0] / 2
    c1 = t[1] - t[0] * z
    c0 = t[2] - c1 * z - c2 * z ** 2
    return {**env, "_odec0": c0, "_odec1": c1, "_odec2": c2}


def _ode_kernel_basis(a):
    """Two vectors spanning ker(a) ⊂ ℂ³ for a nonzero coefficient vector a."""
    i = max(range(3), key=lambda k: abs(a[k]))
    out = []
    for j in range(3):
        if j == i:
            continue
        v = [mp.mpc(0)] * 3
        v[j], v[i] = mp.mpc(1), -a[j] / a[i]
        out.append(tuple(v))
    return out


def handle_ode_predicate_iff(lhs, rhs, d):
    """`<ODE-solution predicate> ↔ <printed differential equation>` (block comment above).
    Returns a PASS/FAIL verdict, or None whenever the shape is not this one or the numerics
    do not decide — in which case the caller's prior honest skip is kept unchanged."""
    binders, cons = d["binders"], d.get("constraints") or {}
    wcand = [v for v, ok in (cons.get("_solfn") or {}).items() if ok]
    if not wcand:
        return None                    # no admissible hypothesis-free solution binder
    try:
        parsed = [parse(_strip_outer_parens(s)) for s in (lhs, rhs)]
    except Exception:
        return None
    pred = disp = None
    for S in parsed:
        node = S[1] if S[0] == "expr" else S
        if S[0] == "eq" and disp is None:
            disp = S
        elif (S[0] == "expr" and isinstance(node, tuple) and node[0] == "app"
              and node[1][0] == "var" and pred is None):
            pred = node
        else:
            return None
    if pred is None or disp is None:
        return None
    if _reg_resolve(pred[1][1]) is not None:
        return None                    # a registry-bound head is not a Lean Prop definition
    unf = _prop_def_unfold(pred[1][1].split(".")[-1], pred[2])
    if unf is None:
        return None
    resA = ("bin", "-", unf[1], unf[2])          # predicate residual (Lean definition)
    resB = ("bin", "-", disp[1], disp[2])        # display residual (DLMF, as printed)
    wvar = ptv = None
    for wv in wcand:
        pts = {}
        if (_ode_w_points(resA, wv, pts) and _ode_w_points(resB, wv, pts)
                and len(pts) == 1):
            pt = next(iter(pts.values()))
            if pt[0] == "var" and binders.get(pt[1]) == "C":
                wvar, ptv = wv, pt[1]
    if wvar is None:
        return None
    free = set(); collect_free(resA, free); collect_free(resB, free)
    free.discard(wvar)
    if any(v != IND and v not in binders and _reg_resolve(v) is None for v in free):
        return None                    # an unbound head — never sampled as a fresh value
    free = {v for v in free if v in binders}
    if ptv not in free:
        return None
    import random
    names = sorted(free)
    grids = [_grid(v, d) for v in names]
    rng = random.Random(_ODE_SEED)
    combos, seen = [], set()
    while len(combos) < _ODE_COMBOS and len(seen) < _ODE_COMBOS * 12:
        c = tuple(rng.choice(g) for g in grids)
        if c not in seen:
            seen.add(c)
            combos.append(c)
    decided = 0
    sawT = sawF = False
    for combo in combos:
        env = dict(zip(names, combo))
        env["_binders"] = binders
        if not _pairs_ok(env, cons) or not _nonzero_ok(env, cons):
            continue                   # outside the theorem's stated domain
        z = env[ptv]
        try:
            a, sa, linA = _ode_coeffs(resA, wvar, env, z)
            b, sb, linB = _ode_coeffs(resB, wvar, env, z)
        except (_EvalTimeout, Unparseable, ZeroDivisionError, ValueError,
                OverflowError, TypeError, ArithmeticError):
            continue
        if max(linA, linB) > _ODE_AGREE:
            return None                # residual not linear in (w″,w′,w) — outside this route
        na, nb = max(abs(x) for x in a), max(abs(x) for x in b)
        if na + nb == 0:
            continue                   # both sides hold for every w here — nothing exercised
        azero, bzero = na <= _ODE_AGREE * (na + nb), nb <= _ODE_AGREE * (na + nb)
        if azero and bzero:
            continue
        if azero or bzero:
            dev, m = mp.mpf(1), mp.mpf(0)
        else:
            i = max(range(3), key=lambda k: abs(b[k]))
            m = a[i] / b[i]
            dev = max(abs(a[k] - m * b[k]) for k in range(3)) / na
        try:
            if dev <= _ODE_AGREE:      # same kernel ⇒ the '↔' holds at this sample; CONFIRM
                tsol = max(_ode_kernel_basis(a), key=lambda v: max(abs(x) for x in v))
                eT = _ode_quad_env(tsol, z, env)
                rA, rB = (_ode_eval(resA, wvar, _ODE_WQUAD, eT),
                          _ode_eval(resB, wvar, _ODE_WQUAD, eT))
                scT = max(abs(x) for x in tsol)
                if abs(rA) > _ODE_AGREE * sa * scT or abs(rB) > _ODE_AGREE * sb * scT:
                    continue           # ambiguous at the solving witness — drop the point
                sawT = True            # both sides TRUE at a concrete entire solution
                eF = _ode_quad_env((mp.mpc(1), mp.mpc(1), mp.mpc(1)), z, env)
                gA, gB = (_ode_eval(resA, wvar, _ODE_WQUAD, eF),
                          _ode_eval(resB, wvar, _ODE_WQUAD, eF))
                if abs(gA) > _ODE_CLEAR * sa and abs(gB) > _ODE_CLEAR * sb:
                    sawF = True        # both sides FALSE at a concrete entire non-solution
                decided += 1
                continue
            if dev >= _ODE_CLEAR:      # kernels differ — build and CHECK a counterexample
                cands = []
                for u, v in ((a, b), (b, a)):
                    if max(abs(x) for x in u) == 0:
                        continue
                    for t in _ode_kernel_basis(u):
                        cands.append((abs(sum(v[k] * t[k] for k in range(3))), t))
                if not cands:
                    continue
                t = max(cands, key=lambda c: c[0])[1]
                eX = _ode_quad_env(t, z, env)
                rA, rB = (_ode_eval(resA, wvar, _ODE_WQUAD, eX),
                          _ode_eval(resB, wvar, _ODE_WQUAD, eX))
                scT = max(abs(x) for x in t)
                zA, zB = abs(rA) <= _ODE_AGREE * sa * scT, abs(rB) <= _ODE_AGREE * sb * scT
                cA, cB = abs(rA) >= _ODE_CLEAR * sa * scT, abs(rB) >= _ODE_CLEAR * sb * scT
                if (zA and cB) or (zB and cA):
                    pt_s = ", ".join(f"{n}={mp.nstr(env[n], 6)}" for n in names)
                    return ("FAIL", "iff-ode",
                            f"w(t) = {mp.nstr(eX['_odec0'], 6)} + {mp.nstr(eX['_odec1'], 6)}·t"
                            f" + {mp.nstr(eX['_odec2'], 6)}·t² at {pt_s}: predicate residual"
                            f" = {mp.nstr(rA, 6)}, display residual = {mp.nstr(rB, 6)}")
        except (_EvalTimeout, Unparseable, ZeroDivisionError, ValueError,
                OverflowError, TypeError, ArithmeticError):
            continue
    if decided < 2 or not (sawT and sawF):
        return None                    # undecided — the caller's honest skip stands
    return ("PASS", "iff-ode",
            f"predicate and display define the same solution set at {decided} sampled "
            f"parameter points (both truth values exercised at entire quadratic witnesses)")


# ── the same '↔' for the §31.15 FUCHSIAN equation ────────────────────────────────
# DLMF 31.15.1 reads `IsFuchsianSolution γ a Φ w z ↔ <rational form> = 0` with THREE
# ∀-quantified infinite-dimensional binders: `w : ℂ → ℂ`, `Φ : Polynomial ℂ`, and the
# `Fin N → ℂ` data (γ, a).  Unlike Heun's equation there is no bound closed-form solution
# to realise the TRUE branch with — but none is needed, because `Φ` enters BOTH sides only
# through the single scalar `Φ.eval z`, linearly.  Instantiating `Φ` at the CONSTANT
# polynomial whose value is
#
#     c = −( ∏ⱼ(z−aⱼ)·w″(z) + ∑ⱼ γⱼ∏_{k≠j}(z−a_k)·w′(z) ) / w(z)
#
# makes the left side hold exactly, at an arbitrary entire `w`; any other value makes it
# fail.  Both are legitimate instantiations of the ∀ (a constant polynomial is a
# polynomial), so both branches of the truth table are exercised without ever solving the
# equation.  The value `c` is derived from the LEFT side's own definition, so what the
# check tests is precisely what the display asserts: that the RIGHT side holds exactly
# when the left one does.
def handle_fuchsian_iff(lhs, rhs, d):
    """`IsFuchsianSolution γ a Φ w z ↔ <rational form> = 0` (DLMF 31.15.1).  Returns None
    — the caller keeps its prior honest skip — for any other head, arity, non-binder slot,
    a `Φ` occurring anywhere but as `Φ.eval z`, or a `w` without a recorded `_solfn`."""
    binders, cons = d["binders"], d.get("constraints") or {}
    solfn = cons.get('_solfn') or {}
    try:
        A = parse(_strip_outer_parens(lhs))
        B = parse(_strip_outer_parens(rhs))
    except Unparseable:
        return None
    if A[0] == "expr":
        A = A[1]
    if not (isinstance(A, tuple) and A[0] == "app" and A[1][0] == "var"
            and A[1][1].split(".")[-1] == "IsFuchsianSolution" and len(A[2]) == 5):
        return None
    if B[0] != "eq":
        return None
    gam, aa, phi, wnode, znode = A[2]
    if not (wnode[0] == "var" and solfn.get(wnode[1])):
        return None
    if not (gam[0] == "var" and aa[0] == "var" and phi[0] == "var" and znode[0] == "var"):
        return None
    wname, gname, aname, pname, zname = wnode[1], gam[1], aa[1], phi[1], znode[1]
    if (binders.get(gname) != "finvecC" or binders.get(aname) != "finvecC"
            or binders.get(zname) != "C"):
        return None
    dims = cons.get('_finvecdim') or {}
    if dims.get(gname) != dims.get(aname) or dims.get(gname) is None:
        return None
    # `Φ` must occur ONLY as `Φ.eval z` — the single scalar the constant-polynomial witness
    # instantiates.  Any other occurrence (a coefficient, a degree, a second point) would
    # not be determined by that witness, so the row keeps its honest skip.
    evnode = ("app", ("var", f"{pname}.eval"), [znode])
    bad = []

    def _scan(nd):
        if isinstance(nd, tuple):
            if nd == evnode:
                return
            if nd[0] == "var" and (nd[1] == pname or nd[1].split(".")[0] == pname):
                bad.append(nd[1])
                return
            for c in nd[1:]:
                _scan(c)
        elif isinstance(nd, list):
            for c in nd:
                _scan(c)
    _scan(B[1]); _scan(B[2])
    if bad:
        return None
    free = set()
    for nd in (B[1], B[2]):
        collect_free(nd, free)
    unbound = [v for v in sorted(free)
               if v not in (wname, gname, aname, pname, zname) and v not in binders
               and _reg_resolve(v) is None and not v.startswith(f"{pname}.")]
    if unbound:
        return (UNABLE, "fuchsian-iff", f"unbound:{unbound[0]}")
    Bl = _subst_node(B[1], evnode, ("var", "_soliffphi"))
    Br = _subst_node(B[2], evnode, ("var", "_soliffphi"))
    lterms = _add_terms(Bl, []) + _add_terms(Br, [])
    decided, seen_true, seen_false, dropped = 0, False, False, 0
    for N in (3, 4):
        # γ and a: generic pole-avoiding tuples with DISTINCT singularities, the same
        # construction sweep_eq uses for an unconstrained `Fin q → ℂ` binder.
        avals = [mp.mpc(mp.mpf("0.41") + idx * mp.mpf("0.83"),
                        mp.mpf("-0.27") + idx * mp.mpf("0.31")) for idx in range(N)]
        gvals = [mp.mpc(mp.mpf("1.37") + idx * mp.mpf("0.53"),
                        mp.mpf("0.29") + idx * mp.mpf("0.17")) for idx in range(N)]
        for zv in list(_grid(zname, d))[:4]:
            # the row's OWN hypothesis `hz : ∀ j, z ≠ a j` (its textual capture is mangled,
            # so it is enforced here directly, with a margin for the derivative stencil)
            if any(abs(zv - av) < mp.mpf("0.05") for av in avals):
                continue
            P = mp.mpc(1)
            for av in avals:
                P *= (zv - av)
            S = mp.mpc(0)
            for j in range(N):
                pj = mp.mpc(1)
                for k in range(N):
                    if k != j:
                        pj *= (zv - avals[k])
                S += gvals[j] * pj
            for i in range(3):
                wit = _entire_wit_ast(i)
                env = {zname: zv, gname: _finvec_callable(gvals), aname: _finvec_callable(avals),
                       dims[gname]: mp.mpf(N), "_intvars": {v for v, t in binders.items()
                                                            if t in ("Z", "N")},
                       "_binders": binders}
                g = _callable(wit, env)
                if g is None:
                    return None
                try:
                    with _time_limit(EVAL_BUDGET):
                        w0, w1, w2 = g(zv), mp.diff(g, zv, 1), mp.diff(g, zv, 2)
                        if abs(w0) < mp.mpf("1e-8"):
                            dropped += 1
                            continue          # c would be ill-conditioned — honest drop
                        c_true = -(P * w2 + S * w1) / w0
                        c_false = c_true + max(mp.mpf(1), abs(c_true)) * mp.mpc("1", "0.5")
                        for cv in (c_true, c_false):
                            t1, t2, t3 = P * w2, S * w1, cv * w0
                            lh, lrel = _soliff_side_holds(t1 + t2 + t3, [t1, t2, t3])
                            env2 = {**env, "_soliffphi": cv}
                            rterms = [evaluate(_subst_var_lam(t, wname, wit), env2)
                                      for t in lterms]
                            rres = (evaluate(_subst_var_lam(Bl, wname, wit), env2)
                                    - evaluate(_subst_var_lam(Br, wname, wit), env2))
                            rh, rrel = _soliff_side_holds(rres, rterms)
                            if lh is None or rh is None:
                                dropped += 1
                                continue
                            decided += 1
                            seen_true, seen_false = seen_true or lh, seen_false or (not lh)
                            if lh != rh:
                                return ("FAIL", "fuchsian-iff",
                                        f"sides disagree at N={N}, z={mp.nstr(zv, 6)}, "
                                        f"witness {i}, Φ.eval z={mp.nstr(cv, 6)}: "
                                        f"LHS={lh} (rel={mp.nstr(lrel, 4)}) "
                                        f"RHS={rh} (rel={mp.nstr(rrel, 4)})")
                except _EvalTimeout:
                    return (UNABLE, "fuchsian-iff", "eval-timeout")
                except (Unparseable, ZeroDivisionError, ValueError, OverflowError,
                        TypeError, ArithmeticError):
                    dropped += 1
                    continue
    if decided < 2:
        return (UNABLE, "fuchsian-iff", f"undersampled/domain (dropped {dropped})")
    if not (seen_true and seen_false):
        return (UNABLE, "fuchsian-iff", "single-valued/unexercised")
    return ("PASS", "fuchsian-iff",
            f"agree at {decided}pts (both truth values exercised, {dropped} dropped)")


def _subst_node(node, target, repl):
    """Replace every occurrence of the exact subtree `target` by `repl`."""
    if node == target:
        return repl
    if isinstance(node, tuple):
        return (node[0],) + tuple(_subst_node(c, target, repl) for c in node[1:])
    if isinstance(node, list):
        return [_subst_node(c, target, repl) for c in node]
    return node


def handle_iff(lhs, rhs, d):
    """`(∀ n > 0, …) ↔ (∀ n > 0, …)` between two function-defining quantified equalities —
    both implications checked by witness construction (see the block comment above).
    A pointwise-boolean '↔' (both sides decidable at each sample) is instead checked by
    truth-table agreement first; any unsupported shape falls through unchanged."""
    r = _iff_bool(lhs, rhs, d)
    if r is not None:
        return r
    # an ODE-SOLUTION predicate `↔` transformed equation at an abstract analytic binder
    # (DLMF 31.2.6/31.2.8) — checked by instantiating the ∀ at concrete analytic witnesses
    # that realise BOTH branches of the truth table (see handle_solution_iff). None → the
    # honest skips below fire exactly as before.
    r = handle_solution_iff(lhs, rhs, d)
    if r is not None:
        return r
    # the §31.15 Fuchsian analogue (DLMF 31.15.1), whose TRUE branch is realised by the
    # CONSTANT-polynomial witness for `Φ` rather than by a closed-form solution.
    r = handle_fuchsian_iff(lhs, rhs, d)
    if r is not None:
        return r
    # `<ODE-solution predicate> ↔ <printed differential equation>` (DLMF 31.12.1–31.12.4):
    # decided by unfolding the predicate's own Lean `def` and comparing SOLUTION SETS; None on
    # any other shape and on an undecided sample set, so every other row's route is unchanged.
    r = handle_ode_predicate_iff(lhs, rhs, d)
    if r is not None:
        return r
    if d.get("constraints"):
        return (UNABLE, "iff", "uncaptured constraints")
    binders = d["binders"]
    try:
        A, B = _iff_side(lhs), _iff_side(rhs)
    except Unparseable as e:
        return (UNABLE, "iff", f"unparsed:{e}")
    if A is None or B is None:
        return (UNABLE, "iff", "side not `∀ v > 0, L = R`")
    dA = _iff_defined(A[0], A[1], A[2], binders)
    dB = _iff_defined(B[0], B[1], B[2], binders)
    if dA is None or dB is None or dA[0] == dB[0]:
        return (UNABLE, "iff", "sides do not each define a distinct function binder")
    if set(binders) != {dA[0], dB[0]}:
        return (UNABLE, "iff", "extra binders")
    # SOUNDNESS: every other free symbol must be a quantified index var or registry-bound.
    free = set()
    for node in (A[1], A[2], B[1], B[2]):
        collect_free(node, free)
    unbound = [x for x in sorted(free) if x not in binders and x not in (A[0], B[0])
               and _reg_resolve(x) is None]
    if unbound:
        return (UNABLE, "iff", f"unbound:{unbound[0]}")
    import random
    rng = random.Random(_IFF_SEED)
    dets = []
    try:
        for tag, src, tgt in (("→", (A[0], dA[0], dA[1]), B),
                              ("←", (B[0], dB[0], dB[1]), A)):
            v, det = _iff_direction(rng, src, tgt, binders)
            dets.append(f"{tag} {det}")
            if v != "PASS":
                return (v, "iff-witness", "; ".join(dets))
    except (Unparseable, ZeroDivisionError, ValueError, OverflowError) as e:
        return (UNABLE, "iff", f"eval:{e}")
    return ("PASS", "iff-witness", "; ".join(dets))


# ── '↔' between two BOOLEAN-valued sides (DLMF 27.9 Legendre-symbol dichotomies) ──
# `legendreSym p a = -1 ↔ ¬ IsSquare (a : ZMod p)` is not a numeric equality of two
# reals, but each side IS a per-sample decidable boolean: the LHS an exact-integer
# equality, the RHS a quadratic-residue test mod p. Model each side as a bool-spec
# wrapped in a `("bool", spec)` node (evaluate ↦ 1/0) and score bool(L) = bool(R)
# through the STANDARD sweep_eq sampler — grids, hypothesis constraints (the
# `[Fact p.Prime]` prime grid {2,3,5,7,11}), per-sample drops (sympy's
# legendre_symbol raises on p = 2 → honest drop), the exact tolerance gate
# (gap ∈ {0,1}: one mismatched sample FAILs the row), and the undersampled /
# trivial-zero guards all apply unchanged. Supported side shapes — anything else
# returns None and the caller keeps the prior honest skip, never a fabricated
# verdict:
#   [¬] L = R                 — exact-INTEGER equality of the evaluated sides (a
#                               non-integer value raises → the sample drops
#                               honestly). A ZMod-cast operand is NOT supported
#                               here: its Lean `=` is a congruence mod n, owned by
#                               sweep_eq's zmod mode — such a side yields None.
#   [¬] L ≠ R                 — negated integer equality
#   [¬] IsSquare (e : ZMod n) — squareness in ℤ/nℤ: ∃ x ∈ [0,n), x² ≡ e (mod n)
#                               (0 included — IsSquare 0 holds, 0 = 0²)
#   D₁ ∨ … ∨ Dₙ               — a top-level disjunction of supported shapes, True iff
#                               some disjunct is (`p % 8 = 1 ∨ p % 8 = 7`, the DLMF
#                               27.9 second supplement). Lean's '¬' binds tighter
#                               than '∨', so the split runs BEFORE negation stripping.
def _bool_spec_val(spec, env):
    """Evaluate a bool-spec (one side of a boolean '↔') to True/False. Raises
    Unparseable on any operand outside the exact-integer model — the sample then
    drops honestly in sweep_eq, never a fabricated boolean."""
    k = spec[0]
    if k == "not":
        return not _bool_spec_val(spec[1], env)
    if k == "or":            # D₁ ∨ … ∨ Dₙ — left-to-right, True short-circuits (sound:
        # True ∨ unknown = True); a raising disjunct BEFORE any True one still
        # propagates, so False ∨ unmodelled never fabricates a boolean (sample drops).
        return any(_bool_spec_val(sp, env) for sp in spec[1])
    if k == "inteq":
        ia, ib = _near_int(evaluate(spec[1], env)), _near_int(evaluate(spec[2], env))
        if ia is None or ib is None:
            raise Unparseable("bool-iff non-integer operand")
        return ia == ib
    if k == "sqmod":         # IsSquare (e : ZMod n) — quadratic residue (incl. 0) mod n
        nv = mp.mpf(int(spec[1])) if spec[1].isdigit() else env[spec[1]]
        n, e = _near_int(nv), _near_int(evaluate(spec[2], env))
        if n is None or n < 1 or e is None:
            raise Unparseable("bool-iff sqmod operand")
        return any((x * x - e) % n == 0 for x in range(n))
    raise Unparseable("bool-iff spec")


def _bool_spec_free(spec, acc, under_eval=False):
    """collect_free over a bool-spec: its numeric operand ASTs, plus the sqmod modulus
    (when a variable — it must be sampled for the residue test)."""
    k = spec[0]
    if k == "not":
        _bool_spec_free(spec[1], acc, under_eval)
    elif k == "or":
        for sp in spec[1]:
            _bool_spec_free(sp, acc, under_eval)
    elif k == "inteq":
        collect_free(spec[1], acc, under_eval)
        collect_free(spec[2], acc, under_eval)
    elif k == "sqmod":
        if not spec[1].isdigit():
            acc.add(spec[1])
        collect_free(spec[2], acc, under_eval)


def _split_top_or(s):
    """Split `s` on every top-level '∨' (paren depth 0) — the disjuncts of a boolean
    '↔' side (`p % 8 = 1 ∨ p % 8 = 7`, DLMF 27.9). A 1-element list when no '∨'."""
    depth, parts, last = 0, [], 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "∨" and depth == 0:
            parts.append(s[last:i])
            last = i + 1
    parts.append(s[last:])
    return [p.strip() for p in parts]


def _bool_side(side):
    """Parse ONE side of a boolean '↔' into a bool-spec; None on any unsupported
    shape (the caller keeps the honest iff skip)."""
    s = _strip_outer_parens(side)
    parts = _split_top_or(s)
    if len(parts) > 1:       # D₁ ∨ … ∨ Dₙ — each disjunct its own bool-spec ('¬' binds
        specs = [_bool_side(p) for p in parts]     # tighter than '∨': split FIRST)
        return None if any(sp is None for sp in specs) else ("or", specs)
    neg = False
    while s.startswith("¬"):
        neg = not neg
        s = _strip_outer_parens(s[1:].strip())
    try:
        ast = parse(s)
    except Exception:
        return None
    spec = None
    if ast[0] in ("eq", "ne"):
        zm = set()
        _zmod_moduli(ast[1], zm)
        _zmod_moduli(ast[2], zm)
        if zm:               # a ZMod-cast (dis)equality is a congruence — not modelled here
            return None
        spec = ("inteq", ast[1], ast[2])
        if ast[0] == "ne":
            spec = ("not", spec)
    elif (ast[0] == "expr" and ast[1][0] == "app" and ast[1][1] == ("var", "IsSquare")
          and len(ast[1][2]) == 1 and ast[1][2][0][0] == "zmodcast"):
        spec = ("sqmod", ast[1][2][0][1], ast[1][2][0][2])
    if spec is None:
        return None
    return ("not", spec) if neg else spec


def handle_bool_iff(lhs, rhs, d):
    """`P ↔ Q` with both sides per-sample decidable booleans — score bool(P) = bool(Q)
    through the standard sweep. None when either side is outside the supported shape
    set (the caller keeps the prior honest skip)."""
    A, B = _bool_side(lhs), _bool_side(rhs)
    if A is None or B is None:
        return None
    v, det = sweep_eq(("bool", A), ("bool", B), d["binders"], d.get("constraints"))
    return (v, "iff-bool", det)


def _grid(v, d):
    if v == IND:
        return SAMPLES[IND]
    base = d["binders"].get(v, "R")
    flag = (d.get("constraints") or {}).get(v)
    if base in ("Z", "N"):
        return _int_grid(flag, base)
    if base in ("C", "H"):
        # honour a `0 < v.im` hypothesis ('impos') exactly as sweep_eq's grid selection
        # already does: a point with Im v < 0 is OUTSIDE the row's stated domain, and
        # scoring it fabricates a mismatch — erf_7_9_3's Gautschi CF (DLMF 7.9.3, valid
        # Im z > 0 only) genuinely converges to the OTHER branch in the lower half-plane,
        # which surfaced as a spurious 'cfConv converges to … ≠ target (AUDIT)' skip.
        # ADDITIVE: restricts sampling to the stated hypothesis domain only.
        if base == "C" and flag == "imaxis":
            return SAMPLES_C_IMAXIS
        if base == "C" and flag in ("impos", "imnonneg"):
            return SAMPLES["H"]
        if base == "C" and flag == "imneg":
            return SAMPLES_H_NEG
        # honour a real-part abscissa hypothesis (`0 < re s` / `1 < s.re` …, recorded under
        # cons['s.re'] exactly as sweep_eq's grid selection consumes it): the default ℂ grid
        # includes Re s < 0 where e.g. a Dirichlet partial sum genuinely diverges — scoring
        # there fabricates a FAIL outside the stated domain (dirichletEta_tendsto_eq,
        # DLMF 25.2.3, rel@end=62.97 at s = −0.7+2.1i). ADDITIVE: in-half-plane grids only.
        rec = (d.get("constraints") or {}).get(v + ".re")
        if base == "C" and rec == "pos":
            return SAMPLES_C_REPOS
        if base == "C" and rec == "gt1":
            return SAMPLES_C_RE1
        if base == "C" and rec == "ge1":
            return SAMPLES_C_REGE1
        return _filter_extra_flags(v, SAMPLES[base], d.get("constraints"))
    return _filter_extra_flags(v, _real_grid(flag), d.get("constraints"))


def handle_parity(nm, expr_s, d):
    """A bare parity CONCLUSION `Even e` / `Odd e` whose `e` is a plain registry-evaluable
    integer-valued term (`Even (totient n)` — parity of φ, DLMF §27.2): the numeric check
    is e % 2 == 0 (resp. == 1), swept on the integer grid implied by the hypotheses (the
    `2 < n` of totient_even restricts to n ∈ {3, …} via the standard `_lower`/`_upper`
    filters, supplemented with CONSECUTIVE integers just above the bound — strictly inside
    the stated domain — so both residue classes and a prime/composite mix are exercised).
    Integer-valuedness is certified PER SAMPLE by the exact `_near_int` gate: a value that
    is not an exact integer drops the point honestly (deciding the parity of a truncated
    float could fabricate either verdict). Returns None whenever `e` is not such a term or
    a free var is not an ℕ/ℤ binder — the caller keeps the prior honest parity skip."""
    try:
        ast = parse(expr_s)
    except Exception:
        return None
    if ast[0] != "expr":
        return None
    node = ast[1]
    binders, constraints = d["binders"], d.get("constraints") or {}
    free = set(); collect_free(node, free)
    # binder status FIRST (see handle_deriv): a binder/registry name collision keeps the
    # declared binder sampled.
    free = {v for v in free if v in binders or _reg_resolve(v) is None}
    unbound = [v for v in free if v != IND and v not in binders]
    if unbound:
        return (UNABLE, "parity", f"unbound:{unbound[0]}")
    grids = []
    for v in sorted(free):
        base = binders.get(v)
        if base not in ("Z", "N"):          # a non-integer binder in a parity claim —
            return None                     # outside this carve-out; keep the honest skip
        g = _int_grid(constraints.get(v), base)
        g = _filter_lower(v, _filter_upper(v, g, constraints), constraints)
        g = [p for p in g if _near_int(p) is not None]   # bound-refill points can be fractional
        lb = constraints.get('_lower', {}).get(v)
        if lb is not None:                  # densify just above the lower bound (in-domain)
            bound, strict = lb
            start = int(mp.floor(bound)) + 1 if (strict or bound != mp.floor(bound)) \
                else int(mp.floor(bound))
            extra = [mp.mpf(start + k) for k in range(8)]
            ub = constraints.get('_upper', {}).get(v)
            if ub is not None:
                extra = [p for p in extra if (p < ub[0] if ub[1] else p <= ub[0])]
            g = sorted(set(g) | set(extra))
        if not g:
            return (UNABLE, "parity", f"empty grid for {v}")
        grids.append((v, g))
    import itertools
    combos = list(itertools.product(*[g[1] for g in grids]))[:24] if grids else [()]
    names = [g[0] for g in grids]
    want = 0 if nm == "Even" else 1
    ok_pts = 0
    for combo in combos:
        env = dict(zip(names, combo))
        if not _pairs_ok(env, constraints):
            continue                        # a pairwise hypothesis excludes this sample
        env["_intvars"] = {v for v, t in binders.items() if t in ("Z", "N")}
        env["_binders"] = binders
        env["_zmodmod"] = constraints.get('_zmodmod', {})
        try:
            with _time_limit(EVAL_BUDGET):
                val = evaluate(node, env)
        except _EvalTimeout:
            return (UNABLE, "parity", "eval-timeout")
        except Unparseable as e:
            head = _unbound_head_of(e)
            return (UNABLE, "parity", f"unbound:{head}" if head else f"unparsed:{e}")
        except Exception:
            continue
        vi = _near_int(val)
        if vi is None:
            continue                        # not an exact integer — parity undecidable here
        ok_pts += 1
        if vi % 2 != want:
            at = ", ".join(f"{n2}={mp.nstr(c2, 8)}" for n2, c2 in zip(names, combo))
            return ("FAIL", "parity", f"¬{nm} at {at}: value {vi}")
    if ok_pts < (2 if free else 1):
        return (UNABLE, "parity", "undersampled/domain")
    return ("PASS", "parity", f"{nm} holds over {ok_pts}pts")


# Definitional ODE-solution predicates, Δ-reduced for the sweep. A conclusion of the
# shape `IsMathieuSE a q y` / `IsMathieuCE a q y` is a def-application whose Lean body
# is a conjunction of ∀-quantified equalities (FLMF/Functions/Mathieu/Basic.lean):
#     IsMathieuSE a q y  :=  MathieuEquation a q y            -- ∀ x, mathieuOp a q y x = 0
#                            ∧ (∀ x, y (−x) = −y x)           -- oddness
#                            ∧ Function.Periodic y (2π)       -- ∀ x, y (x + 2π) = y x
#     IsMathieuCE a q y  :=  the same with (∀ x, y (−x) = y x) -- evenness (DLMF 28.2.23)
# with mathieuOp a q y x = deriv (deriv y) x + (a − 2·q·cos (2x))·y x (DLMF 28.2.1/28.2.24).
# The fresh sample variable 𝓍 is a synthetic name (like IND) that cannot collide with a
# Lean binder; `deriv` evaluates by finite-difference mp.diff and the applied lambda by
# β-reduction (see the app/"lam" case in `evaluate`). Only the exact 3-argument shape is
# unfolded; anything else returns the AST unchanged (honest skip downstream, never a
# fabricated verdict).
_ODE_X = "\U0001D4CD"          # 𝓍 — synthetic ∀-sample variable of an unfolded predicate


def _unfold_ode_pred(ast):
    """Δ-reduce a known definitional ODE-solution predicate in conclusion position to its
    `∀ x, eq ∧ eq ∧ eq` body, so classify_and_check's forall/and machinery can sweep each
    conjunct numerically. Currently: `IsMathieuSE a q y` (the DLMF 28.2.24 se surface)
    and `IsMathieuCE a q y` (the DLMF 28.2.23 ce surface — identical apart from the
    parity conjunct, y(−x) = +y(x))."""
    if ast[0] != "expr" or ast[1][0] != "app":
        return ast
    head, args = ast[1][1], ast[1][2]
    while head[0] == "app":                    # flatten a curried application
        args = head[2] + args
        head = head[1]
    if head not in (("var", "IsMathieuSE"), ("var", "IsMathieuCE")) or len(args) != 3:
        return ast
    A, Q, Y = args
    X = ("var", _ODE_X)
    yx = ("app", Y, [X])
    cos2x = ("app", ("var", "Real.cos"), [("bin", "*", ("num", 2), X)])
    ode = ("bin", "+",
           ("app", ("var", "deriv"), [("app", ("var", "deriv"), [Y]), X]),
           ("bin", "*",
            ("bin", "-", A, ("bin", "*", ("bin", "*", ("num", 2), Q), cos2x)),
            yx))
    conj = [("eq", ode, ("num", 0)),                                        # mathieuOp = 0
            # parity: se is odd (y(−x) = −y(x), 28.2.24), ce is even (y(−x) = y(x), 28.2.23)
            ("eq", ("app", Y, [("neg", X)]),
             ("neg", yx) if head == ("var", "IsMathieuSE") else yx),
            ("eq", ("app", Y, [("bin", "+", X, ("bin", "*", ("num", 2), ("var", "π")))]),
             yx)]                                                           # y(x+2π) = y(x)
    return ("forall", {_ODE_X: "R"}, ("and", conj))


# Synthetic ∀-sample index of the IsCDSystem unfolding (a natural, sampled on the ℕ grid).
_CD_K = "\U0001D4C0"           # 𝓀


def _unfold_cd_pred(ast):
    """Δ-reduce an `IsCDSystem p h a x y` conclusion (FLMF/Functions/OrthogonalPolynomials/
    ChristoffelDarboux.lean — the DLMF 18.2.12 telescoping system) to its two DEFINING
    equalities with `cdSummand`/`cdCross` unfolded per their Lean definitions
    (cdSummand k = pₖ(x)pₖ(y)/hₖ, cdCross k = aₖ·(p_{k+1}(x)pₖ(y) − pₖ(x)p_{k+1}(y))):

        base:    (x−y)·p₀(x)p₀(y)/h₀ = a₀·(p₁(x)p₀(y) − p₀(x)p₁(y))
        step k:  (x−y)·p_{k+1}(x)p_{k+1}(y)/h_{k+1}
                   = a_{k+1}·(p_{k+2}(x)p_{k+1}(y) − p_{k+1}(x)p_{k+2}(y))
                     − aₖ·(p_{k+1}(x)pₖ(y) − pₖ(x)p_{k+1}(y))

    hoisted as `∀ k : ℕ, base ∧ step k` for classify_and_check's forall/and machinery
    (base is k-free, so re-checking it at every k sample is redundant but harmless).
    Only the exact bare-name 5-argument shape is unfolded; anything else returns the
    AST unchanged (honest skip downstream, never a fabricated verdict)."""
    if ast[0] != "expr" or ast[1][0] != "app":
        return ast
    head, args = ast[1][1], ast[1][2]
    while head[0] == "app":                    # flatten a curried application
        args = head[2] + args
        head = head[1]
    if head != ("var", "IsCDSystem") or len(args) != 5:
        return ast
    P, H, A, X, Y = args

    def p(idx, at):                            # p idx at
        return ("app", P, [idx, at])

    def summand(idx):                          # cdSummand: p idx x · p idx y / h idx
        return ("bin", "/", ("bin", "*", p(idx, X), p(idx, Y)), ("app", H, [idx]))

    def cross(idx, idx1):                      # cdCross: a idx · (p idx1 x·p idx y − p idx x·p idx1 y)
        return ("bin", "*", ("app", A, [idx]),
                ("bin", "-", ("bin", "*", p(idx1, X), p(idx, Y)),
                 ("bin", "*", p(idx, X), p(idx1, Y))))

    K = ("var", _CD_K)
    n0, n1 = ("num", 0), ("num", 1)
    k1 = ("bin", "+", K, ("num", 1))
    k2 = ("bin", "+", K, ("num", 2))
    xmy = ("bin", "-", X, Y)
    base = ("eq", ("bin", "*", xmy, summand(n0)), cross(n0, n1))
    step = ("eq", ("bin", "*", xmy, summand(k1)),
            ("bin", "-", cross(k1, k2), cross(K, k1)))
    return ("forall", {_CD_K: "N"}, ("and", [base, step]))


# ── file-local `def` inlining (single-letter/file-scoped heads the registry must NOT bind) ──
# A theorem may state an identity in terms of helper `def`s that live in ITS OWN file —
# `dupl` (Bernoulli/Duplication.lean) uses `L`/`R`, `qbinomial_theorem`
# (QBinomialTheorem.lean) uses `f`/`c`. A GLOBAL registry binding of names like `L`/`f`
# would be unsound across files (the same letter means different things elsewhere), so these
# stayed `unbound:L`/`unbound:f`. The sound fix is δ-reduction: read the SAME source file,
# collect its single-line `def NAME (params) : T := BODY`, and unfold each such head in the
# conclusion by substituting the actual arguments into the (parsed) body. Fires ONLY on heads
# that are file-local defs AND are NOT registry-bound AND are NOT theorem binders — so it can
# never change a row whose heads already resolve (the control set is untouched by construction),
# and the collection is scoped to the decl's OWN file (no cross-file leakage). `local notation
# "X" => Y` aliases are expanded in the bodies first (e.g. `P` → `FLMF.qPochhammer`).
_LOCAL_DEF_CACHE = {}

# single-line: `(noncomputable |private )*def NAME (p:T)(q:T)… : RetT := BODY`  (BODY = rest of line)
_LOCALDEF_RE = re.compile(
    r'^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+)*def[ \t]+'
    r'([A-Za-zα-ω][\w\'′]*)[ \t]*((?:\([^()]*\)[ \t]*)*):[^:=]*:=[ \t]*(\S.*)$', re.M)
_LOCALNOTA_RE = re.compile(r'^[ \t]*local[ \t]+notation[ \t]+"([^"]+)"[ \t]*=>[ \t]*(\S.*?)[ \t]*$', re.M)
# MULTI-LINE def header: `def NAME (p:T)… : RetT :=` whose `:=` ENDS the line (body wraps below).
_LOCALDEF_MHEAD_RE = re.compile(
    r'^([ \t]*)(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+)*def[ \t]+'
    r'([A-Za-zα-ω][\w\'′]*)[ \t]*((?:\([^()]*\)[ \t]*)*):[^:=]*:=[ \t]*$')


def _multiline_localdefs(text):
    """Yield (name, params_s, body_s) for MULTI-LINE `def NAME (params) : T :=` whose body wraps
    to the following more-indented line(s) — e.g. `chapter15Arccosh` (Ch15AsymptoticApproximations),
    which the single-line `_LOCALDEF_RE` (body required on the `:=` line) misses. The body is the
    contiguous block of following non-blank lines indented STRICTLY MORE than the `def` keyword,
    stopping at the first blank line or dedent — the exact textual extent of a wrapped definition
    body. Same soundness scope as the single-line pass (the caller still drops any registry-bound
    head and any body that fails to parse; collection is scoped to the decl's OWN file)."""
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        m = _LOCALDEF_MHEAD_RE.match(lines[i])
        if not m:
            i += 1
            continue
        indent = len(m.group(1))
        body_lines, j = [], i + 1
        while j < len(lines):
            ln = lines[j]
            if ln.strip() == "" or (len(ln) - len(ln.lstrip())) <= indent:
                break
            body_lines.append(ln.strip())
            j += 1
        if body_lines:
            yield m.group(2), m.group(3), " ".join(body_lines)
        i = max(j, i + 1)


def _file_local_defs(d):
    """{name: (param_names, body_ast)} for the SINGLE-LINE, non-registry-bound `def`s of the
    decl's own file. Cached per file. A def whose body fails to parse is dropped (honest skip)."""
    rel = d.get("file")
    if not rel:
        return {}
    if rel in _LOCAL_DEF_CACHE:
        return _LOCAL_DEF_CACHE[rel]
    defs = {}
    try:
        text = (ROOT.parent.parent / rel).read_text()
    except Exception:
        _LOCAL_DEF_CACHE[rel] = defs
        return defs
    notas = {sym: rep for sym, rep in _LOCALNOTA_RE.findall(text)}
    triples = list(_LOCALDEF_RE.findall(text))
    _seen = {t[0] for t in triples}
    for nm, ps, bs in _multiline_localdefs(text):    # multi-line `def` bodies the 1-line regex missed
        if nm not in _seen:
            triples.append((nm, ps, bs))
            _seen.add(nm)
    for name, params_s, body_s in triples:
        if ob.REGISTRY.get(name) is not None:        # never shadow a registry-bound head
            continue
        params = []
        for grp in re.findall(r'\(([^():]+):[^()]*\)', params_s):
            params.extend(grp.split())
        body = body_s.strip()
        for sym, rep in notas.items():               # expand `local notation` aliases (whole-token)
            body = re.sub(r'(?<![\w\'′])' + re.escape(sym) + r'(?![\w\'′])', rep, body)
        try:
            p = P(tokenize(body))
            ast = p.expr()
        except Exception:
            continue
        defs[name] = (params, ast)
    _LOCAL_DEF_CACHE[rel] = defs
    return defs


def _ast_subst(node, mapping):
    """Replace every ('var', name) leaf with mapping[name] (arg-AST); structural recursion."""
    if isinstance(node, tuple):
        if len(node) == 2 and node[0] == "var" and node[1] in mapping:
            return mapping[node[1]]
        return tuple(_ast_subst(x, mapping) for x in node)
    if isinstance(node, list):
        return [_ast_subst(x, mapping) for x in node]
    return node


def _inline_local_defs(node, defs, depth=0):
    """δ-reduce applications of file-local defs, innermost-first, up to a small depth cap
    (nested helpers like f → c bottom out quickly; the cap guards a pathological self-cycle)."""
    if depth > 8 or not defs:
        return node
    if isinstance(node, tuple):
        node = tuple(_inline_local_defs(x, defs, depth) for x in node)
    elif isinstance(node, list):
        return [_inline_local_defs(x, defs, depth) for x in node]
    if (isinstance(node, tuple) and len(node) == 3 and node[0] == "app"
            and node[1][0] == "var" and node[1][1] in defs):
        params, body = defs[node[1][1]]
        args = node[2]
        if len(params) == len(args):
            reduced = _ast_subst(body, dict(zip(params, args)))
            return _inline_local_defs(reduced, defs, depth + 1)
    return node


# ════════════════════════ 4. DRIVE ══════════════════════════════════════════
def classify_and_check(d):
    """Verdict for one decl, with the namespace-resolution safety net: if the conclusion
    uses a name that resolves ONLY via FLMF-namespace stripping and the mechanical verdict is
    FAIL, downgrade to an honest `skip:ns-convention-unverified` (the FLMF↔mpmath convention /
    intended domain for that qualified name is not independently checked here). Exact-bound
    names are unaffected — they keep full FAIL authority."""
    global _CUR_NS
    _CUR_NS = d.get("ns") or ""      # per-decl namespace for blocked-pair head qualification
    verdict, kind, det = _classify_and_check(d)
    if verdict == "FAIL":
        try:
            ast = parse(d["concl"])
        except Exception:
            ast = None
        if ast is not None and _concl_uses_ns_resolved(ast):
            return (UNABLE, "ns-convention-unverified", f"({kind}) {det}")
        # A doubly-infinite contour integral with a free COMPLEX variable is sector-restricted
        # (Mellin–Barnes §7.7): the uncaptured z-sector means the ℂ grid samples off-domain, so
        # a FAIL there is not a sound refutation — downgrade to an honest skip, never a PASS.
        if (ast is not None and _has_biinf_integral(ast)
                and any(t == "C" for t in d.get("binders", {}).values())):
            return (UNABLE, "contour-sector-unverified", f"({kind}) {det}")
    return (verdict, kind, det)


def _split_top_ws(s):
    """Split `s` on whitespace runs occurring at bracket-depth 0 (parenthesised groups stay
    intact). Used to peel the space-separated arguments of a flat application."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{":
            depth += 1
            cur += ch
        elif ch in ")]}":
            depth -= 1
            cur += ch
        elif ch.isspace() and depth == 0:
            if cur:
                out.append(cur)
                cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def _struct_fields(body):
    """Field map of a Lean structure-literal BODY (the text inside the outer `{ … }`), splitting
    on each `IDENT :=` occurring at bracket-depth 0 — a nested `{ a := … , b := … }` value stays
    intact inside its parent's field. Whitespace-collapsed input (one line) is expected, as
    `_conclusion` emits."""
    marks = []
    for m in re.finditer(r"(?<![\w.])([A-Za-z_]\w*)\s*:=", body):
        pre = body[:m.start()]
        depth = sum(pre.count(o) - pre.count(cl) for o, cl in (("(", ")"), ("[", "]"), ("{", "}")))
        if depth == 0:
            marks.append((m.group(1), m.start(), m.end()))
    fields = {}
    for k, (name, _st, en) in enumerate(marks):
        end = marks[k + 1][1] if k + 1 < len(marks) else len(body)
        fields[name] = body[en:end].strip()
    return fields


# In-domain complex sample ladder for a generalized-continued-fraction convergence row
# (DLMF §15.7): small-modulus points (|z| ≤ 0.5, so the Gauss CF converges geometrically and
# the forward convergents settle to machine precision within a few hundred terms) with varied
# phase, all with Re z ≤ 0.35 < 1/2 so the DLMF 15.7.5 half-plane hypothesis is honoured too.
# Every point lies inside every §15.7 convergence domain (unit disc ∩ cut plane ∩ Re < 1/2); the
# `_pairs_ok` filter still applies the row's own recorded hypotheses on top. This is the same
# "build a probe ladder from the stated filter/domain" discipline handle_tendsto already uses —
# the STATEMENT is unchanged; only the numeric witness is sampled where the CF is well-conditioned.
_GCF_ZLADDER = [mp.mpf("0.3"), mp.mpf("-0.4"), mp.mpc("0.25", "0.25"), mp.mpc("-0.2", "0.35"),
                mp.mpc("0", "0.4"), mp.mpc("-0.35", "-0.15"), mp.mpc("0.35", "-0.2")]


_NAMED_CF_RE = re.compile(
    r'^(?:Filter\.)?Tendsto\s+\((\w[\w.\']*)((?:\s+[^\s()]+)+)\)\.convs\s+'
    r'(?:Filter\.)?atTop\s+\((?:𝓝|nhds)\s+(.*)\)$', re.S)
_NAMED_CF_ETA_RE = re.compile(
    r'^(?:Filter\.)?Tendsto\s+\(fun\s+(\w+)(?:\s*:\s*[^=]*?)?\s*=>\s*'
    r'\((\w[\w.\']*)((?:\s+[^\s()]+)+)\)\.convs\s+\1\)\s+'
    r'(?:Filter\.)?atTop\s+\((?:𝓝|nhds)\s+(.*)\)$', re.S)


def handle_named_cf_tendsto(c, d):
    """`Tendsto (F p₁ … p_k).convs atTop (𝓝 target)` — the convergence of a NAMED
    `GenContFract` object (DLMF 31.4.2's accessory-parameter fraction `heunEigenCF`),
    in either the direct or the η-expanded `fun n => (F …).convs n` spelling.

    `handle_gcf_tendsto` handles only a fraction written INLINE as a struct literal; a
    fraction packaged as a `def` reaches the generic Tendsto path, which cannot evaluate
    `.convs` at all (heun_31_4_2 skipped `arity`). This handler builds the convergents
    from the CF's registered stream (`ob.CF_REGISTRY[F]["build"]`, a field-for-field
    transcription of the Lean `def`, anchored in ob.verify() against the DLMF display
    entry-by-entry) through Mathlib's own continuant recursion (`ob.cf_convergent_limit`).

    SAMPLING SOUNDNESS — the point of the whole handler. Such a row is quantified under a
    hypothesis the free-variable grid cannot satisfy (31.4.2 holds only at the eigenvalues
    `q_m` of 31.4.1, a measure-zero set), so free sampling would fabricate a refutation of
    a true theorem. The handler therefore fires ONLY when the extractor recorded
    `_cfwitness` for this fraction — i.e. the row's own signature assumes the registered
    hypothesis carrier (`IsHeunEigenvalue`) on EXACTLY the arguments the fraction is
    applied to — and it samples ONLY the certified witnesses of that carrier
    (`ob.heun_eigen_witnesses`: `q` located as a root of the Wronskian of `Hℓ` against the
    `z = 1` analytic solution of DLMF 31.3.5, which never mentions the continued fraction;
    circularly solving `CF(q) = q` would be a vacuous check and is NOT done). Samples are
    additionally filtered by the row's recorded `_pairs_ok` hypotheses, and any sample whose
    continuants come near a vanishing denominator is DROPPED, honouring the statement's own
    `dens n ≠ 0` proviso rather than scoring a point the display excludes.

    PASS iff every scored witness's settled limit matches `target`; FAIL on a settled limit
    that contradicts it (a wrong sign, index shift or head in the Lean `def` — the rivals
    ob.verify() rejects); honest skip when fewer than two witnesses survive the gates.
    Returns None when the conclusion is not this shape or the fraction is unregistered."""
    c = c.strip()
    m = _NAMED_CF_RE.match(c)
    if m:
        cfname, argtext, target_text = m.group(1), m.group(2), m.group(3)
    else:
        m = _NAMED_CF_ETA_RE.match(c)
        if not m:
            return None
        cfname, argtext, target_text = m.group(2), m.group(3), m.group(4)
    spec = getattr(ob, "CF_REGISTRY", {}).get(cfname)
    if spec is None:
        return None                      # unregistered fraction — keep the caller's skip
    args = argtext.split()
    if len(args) != spec["arity"] or len(set(args)) != len(args):
        return (UNABLE, "gcf", f"{cfname}: arguments not a distinct binder list")
    recorded = (d.get("constraints") or {}).get('_cfwitness', {}).get(cfname)
    if recorded != args:
        # the row does not assume the carrier this witness ladder certifies (or assumes it
        # on other arguments): no sound sample ladder exists here.
        return (UNABLE, "gcf", f"{cfname}: no certified sample ladder ({spec['requires']})")
    try:
        tast = parse(target_text)
        tast = tast[1] if tast and tast[0] == "expr" else tast
    except Exception as e:
        return (UNABLE, "gcf", f"unparsed target:{e}")
    tfree = set()
    collect_free(tast, tfree)
    if any(v != IND and v not in args and _reg_resolve(v) is None for v in tfree):
        return (UNABLE, "gcf", "target outside the witnessed parameters")
    cons = d.get("constraints")
    scored, worst, mism, dropped = 0, mp.mpf(0), None, 0
    for w in spec["witnesses"]():
        env = dict(zip(args, w))
        if not _pairs_ok(env, cons):
            dropped += 1
            continue
        try:
            target = evaluate(tast, env)
            h, pair = spec["build"](*w)
            lim, k, dmin = ob.cf_convergent_limit(h, pair)
        except Exception:
            dropped += 1
            continue
        # `dens n ≠ 0` proviso of the statement: a near-vanishing continuant denominator
        # is outside the displayed fraction's own domain — drop, never score.
        if lim is None or not isinstance(dmin, mp.mpf) or dmin < mp.mpf("1e-12"):
            dropped += 1
            continue
        scored += 1
        rel = abs(lim - target) / max(mp.mpf(1), abs(target))
        worst = max(worst, rel)
        if rel > mp.mpf("1e-8") and mism is None:
            mism = (mp.nstr(lim, 12), mp.nstr(target, 12),
                    {k2: mp.nstr(v2, 8) for k2, v2 in env.items()})
    if mism is not None:
        return ("FAIL", "gcf",
                f"{cfname} convs settle to {mism[0]} ≠ target {mism[1]} @ {mism[2]}")
    if scored < 2:
        return (UNABLE, "gcf",
                f"{cfname}: only {scored} certified witness(es) settled ({dropped} dropped)")
    if worst < mp.mpf("1e-6"):
        return ("PASS", "gcf",
                f"{cfname} convs→target rel={mp.nstr(worst, 4)} over {scored} "
                f"certified {spec['requires']} witnesses")
    return (UNABLE, "gcf", f"uncertified rate (rel={mp.nstr(worst, 4)})")


def handle_gcf_tendsto(c, d):
    """`Tendsto ({ h := h₀ , s := Stream'.Seq.ofStream (fun n => { a := aₙ , b := bₙ }) }).convs
    atTop (𝓝 target)` — a Mathlib GenContFract convergence claim (DLMF §15.7 Gauss continued
    fractions). Build the forward convergents Aₖ/Bₖ from the EXACT stream of the statement
    (A₋₁=1, A₀=h₀, B₋₁=0, B₀=1; Aₖ₊₁ = bₖ·Aₖ + aₖ·Aₖ₋₁, likewise B — Mathlib's `convs`
    recurrence), certify they SETTLE (Cauchy) at each in-domain sample, and compare the settled
    limit to `target`. PASS iff every settled sample matches; FAIL if a sample settles to a value
    ≠ target (a genuine limit/sign/index mismatch — the check has teeth); honest skip if no
    sample settles. Returns None when the conclusion is not this shape (caller keeps its own path).
    The a/b-pair convention and the target ratio are self-validated in oracle_bindings.verify()
    (`gauss t/u | v/w | x/y CF → hyp2f1 ratio`), DECORRELATED from these coefficient forms."""
    c = c.strip()
    if not c.startswith("Tendsto"):
        return None
    idx = c.find(".convs")
    if idx < 0:
        return None
    func = c[len("Tendsto"):idx].strip()
    tail = c[idx + len(".convs"):].strip()
    if not tail.startswith("atTop"):
        return None
    limpart = tail[len("atTop"):].strip()
    if not (func.startswith("(") and func.endswith(")")):
        return None
    struct = func[1:-1].strip()
    if not (struct.startswith("{") and struct.endswith("}")):
        return None
    sbody = struct[1:-1].strip()
    if not (limpart.startswith("(") and _bracket_end(limpart, 0) == len(limpart)):
        return None
    inner = limpart[1:-1].strip()
    lm = re.match(r'^(?:𝓝|nhds)\s+(.*)$', inner, re.S)
    if not lm:
        return None
    target_text = lm.group(1).strip()
    fields = _struct_fields(sbody)
    if 'h' not in fields or 's' not in fields:
        return None
    fm = re.search(r'fun\s+(\w+)\s*=>', fields['s'])
    idxvar = fm.group(1) if fm else 'n'
    bi = fields['s'].find('{')
    if bi < 0:
        return None
    be = _bracket_end(fields['s'], bi)
    if be is None:
        return None
    ifields = _struct_fields(fields['s'][bi + 1:be - 1].strip())
    if 'a' not in ifields or 'b' not in ifields:
        return None

    def _node(text):
        ast = parse(text)
        return ast[1] if ast and ast[0] == "expr" else ast
    try:
        hN, aN, bN, tN = (_node(fields['h']), _node(ifields['a']),
                          _node(ifields['b']), _node(target_text))
    except Exception as e:
        return (UNABLE, "gcf", f"unparsed:{e}")
    free = set()
    for nd in (hN, aN, bN, tN):
        collect_free(nd, free)
    free = {v for v in free if v != idxvar and v != IND and _reg_resolve(v) is None}
    unbound = [v for v in free if v not in d["binders"]]
    if unbound:
        return (UNABLE, "gcf", f"unbound:{unbound[0]}")
    grids = [(v, _GCF_ZLADDER if v == 'z' else _grid(v, d)) for v in sorted(free)] \
        or [("_", [mp.mpf(0)])]
    import itertools
    names = [g[0] for g in grids]
    cons = d.get("constraints")
    combos = [co for co in itertools.product(*[g[1] for g in grids])
              if _pairs_ok(dict(zip(names, co)), cons)]
    scored, worst, mism = 0, mp.mpf(0), None
    for co in combos:
        env = dict(zip(names, co))
        z = env.get('z')
        if z is not None and abs(z) >= mp.mpf("0.95"):   # stay strictly inside the disc
            continue
        try:
            h = evaluate(hN, env)
            target = evaluate(tN, env)
        except Exception:
            continue
        try:
            Am1, A0, Bm1, B0 = mp.mpf(1), h, mp.mpf(0), mp.mpf(1)
            prev, settled = None, None
            for k in range(0, 300):
                e2 = dict(env); e2[idxvar] = mp.mpf(k)
                ak, bk = evaluate(aN, e2), evaluate(bN, e2)
                A1, B1 = bk * A0 + ak * Am1, bk * B0 + ak * Bm1
                Am1, A0, Bm1, B0 = A0, A1, B0, B1
                if B0 == 0:
                    break
                if abs(B0) > mp.mpf("1e8") or abs(B0) < mp.mpf("1e-8"):   # renormalise; ratio unchanged
                    Am1, A0, Bm1, B0 = Am1 / B0, A0 / B0, Bm1 / B0, B0 / B0
                conv = A0 / B0
                if prev is not None and k > 5:
                    if abs(conv - prev) / max(mp.mpf(1), abs(conv)) < mp.mpf("1e-24"):
                        settled = conv
                        break
                prev = conv
        except Exception:
            continue
        if settled is None:
            continue                     # this sample never Cauchy-settled — it proves nothing, drop it
        scored += 1
        rel = abs(settled - target) / max(mp.mpf(1), abs(target))
        worst = max(worst, rel)
        if rel > mp.mpf("1e-8") and mism is None:
            mism = (mp.nstr(settled, 10), mp.nstr(target, 10),
                    {k2: mp.nstr(v2, 6) for k2, v2 in env.items()})
    if scored < 1:
        return (UNABLE, "gcf", "no convergent settled at any in-domain sample")
    if mism is not None:
        return ("FAIL", "gcf",
                f"convs settle to {mism[0]} ≠ target {mism[1]} @ {mism[2]}")
    if worst < mp.mpf("1e-6"):
        return ("PASS", "gcf", f"convs→target rel={mp.nstr(worst, 4)} over {scored} samples")
    return (UNABLE, "gcf", f"uncertified rate (rel={mp.nstr(worst, 4)})")


def _classify_and_check(d):
    c = d["concl"]
    if not c:
        return (UNABLE, "no-conclusion", "")
    # the same convergence claim for a fraction packaged as a NAMED `def`
    # (`Tendsto (heunEigenCF a q α β γ δ).convs atTop (𝓝 q)`, DLMF 31.4.2): build the
    # convergents from the registered stream and score them at the certified witnesses of
    # the row's own hypothesis carrier. None ⇒ not this shape / unregistered, fall through.
    if ".convs" in c and "Tendsto" in c[:16]:
        nres = handle_named_cf_tendsto(c, d)
        if nres is not None:
            return nres
    # a GenContFract convergence claim `Tendsto (…).convs atTop (𝓝 target)` (DLMF §15.7): the
    # struct-let is δ-inlined by _inline_struct_lets, so the head is now the literal stream —
    # build the convergents and rate-gate to the target ratio. None ⇒ not this shape, fall through.
    if c.startswith("Tendsto") and ".convs" in c:
        gres = handle_gcf_tendsto(c, d)
        if gres is not None:
            return gres
    # `SolvesGaussODEOn a b c f puncturedUnitDisc` (Ch15LogarithmicSolutions.lean, DLMF §15.10)
    # is the DEFINING predicate `∀ z ∈ s, z(1−z)·f''(z) + (c−(a+b+1)z)·f'(z) − ab·f(z) = 0` —
    # the Gauss-ODE residual vanishing. Unfold it to that residual = 0 equality with z sampled
    # inside the punctured unit disc (the 'unit' complex grid: all points 0 < ‖z‖ < 1, off the
    # branch cut), so classify's numeric deriv path witnesses the residual pointwise. The three
    # logSolution heads are registry-bound. ADDITIVE: only the exact 4-arg-then-puncturedUnitDisc
    # shape fires; any other SolvesGaussODEOn spelling falls through to the honest skip below.
    mgo = re.match(r'^SolvesGaussODEOn\s+(.+?)\s+puncturedUnitDisc$', c)
    if mgo:
        parts = _split_top_ws(mgo.group(1))
        if len(parts) == 4:
            A, B, C, F = parts
            zv = next(z for z in ("z", "z₀", "w", "ζ", "ξ") if z not in d["binders"])
            resid = (f"{zv} * (1 - {zv}) * deriv (deriv {F}) {zv} "
                     f"+ ({C} - ({A} + {B} + 1) * {zv}) * deriv {F} {zv} "
                     f"- {A} * {B} * ({F} {zv})")
            d2 = {**d, "concl": f"{resid} = 0",
                  "binders": {**d["binders"], zv: "C"},
                  "constraints": {**(d.get("constraints") or {}), zv: "unit"}}
            v, k, det = _classify_and_check(d2)
            return (v, f"gauss-ode-residual/{k}", det)
    # ── DLMF §31.15(ii)/(iii): a display whose subject exists only through the row's own
    # hypotheses (a Stieltjes polynomial and its Van Vleck partner, their zeros, the
    # accessory parameters, the energy G, an equilibrium configuration).  `_stieltjes_witness`
    # has recorded those roles off the signature; build the witnesses from the §31.15(i)
    # DEFINING problem, re-verify every hypothesis on them, and score the conclusion (a
    # disjunctive one member by member — the tokenizer has no '∨' token, which is why these
    # rows never reached parse() at all).  None ⇒ not this shape / conclusion not covered by
    # the witness, fall through to the honest skip exactly as before.
    if (d.get("constraints") or {}).get("_stieltjes"):
        sres = handle_stieltjes(d)
        if sres is not None:
            return sres
    # non-numeric buckets, reported not forced (Tendsto/HasDerivAt are now HANDLED below)
    #   polynomial-roots: a conclusion over the root MULTISET of a polynomial
    #   (`P.roots` → `.toFinset.card` / `.Nodup` / `Multiset.card`, e.g. the DLMF §18.2(vi)
    #   zero-count theorems) is a symbolic root-extraction/count identity, not a sampleable
    #   real expression — the oracle has no root-finding, and the typical subject is an
    #   abstract `OrthogonalPoly` bundle with nothing to instantiate. Named here (instead of
    #   the misleading fall-through `unbound:….roots.toFinset.card`) so the worklist routes
    #   it to Tier-2 back-translation, never to a "bind it numerically" Tier-1 action.
    #   Scoped to `.roots` only: bare `Finset.card`/`card` stays bindable elsewhere.
    for pat, why in [(r'\bSummable\b', "summable"), (r'\bContinuous\b', "continuous"),
                     (r'\bOdd\b|\bEven\b', "parity"), (r'\bDifferentiable\b', "differentiable"),
                     (r'\.roots\b', "polynomial-roots"),
                     (r'Type\b|CommRing|Algebra', "abstract-type")]:
        if re.search(pat, c):
            # CARVE-OUT (additive): the OrthogonalPoly-bundle root-COUNT heads are now
            # numerically bound — registry kind 'envfn' instantiates the abstract bundle
            # at the anchored canonical Laguerre witness with genuine polyroots-based
            # root counting (ob._op_bundle_roots_card, DLMF §18.2(vi)). If EVERY
            # `.roots`-bearing atom in the conclusion is such a bound head, the row is
            # sampleable — fall through to the normal parse/sweep path. Any other
            # `.roots` spelling (`Multiset.card O.P.roots`, `.Nodup`, a bare root
            # multiset) keeps the honest polynomial-roots skip exactly as before.
            if why == "polynomial-roots":
                toks = re.findall(r"[\w.']*\.roots[\w.']*", c)
                if toks and all((ob.REGISTRY.get(t) or (None,))[0] == "envfn" for t in toks):
                    continue
            # CARVE-OUT (additive): a bare parity conclusion `Even e` / `Odd e` with `e`
            # a registry-evaluable integer-valued term (`Even (totient n)`, DLMF §27.2's
            # parity of φ) is numerically decidable — sweep e % 2 on the hypothesis-
            # restricted integer grid (handle_parity, exact-integer gated). Any other
            # Even/Odd-bearing shape keeps the honest parity skip exactly as before.
            if why == "parity":
                pm = re.match(r'^(Even|Odd)\s+(.+)$', c.strip())
                if pm:
                    pres = handle_parity(pm.group(1), pm.group(2).strip(), d)
                    if pres is not None:
                        return pres
            # CARVE-OUT (additive): a `Summable (·)` / `¬ Summable (·)` conclusion over a
            # SCALAR ℕ-indexed summand is numerically corroborated by the ratio/Raabe tail
            # test (handle_summable) — turning the blanket skip into a decided verdict where
            # the tail certifies. Product-indexed (ℕ×ℕ) and prime-indexed series (whose
            # `↦`/`¬` may not even tokenize) are string-guarded out and keep the honest skip.
            if why == "summable":
                neg = c.strip().startswith("¬")
                sbody = c.strip().lstrip("¬").strip()
                sm = re.match(r'^Summable\s+(.+)$', sbody)
                if sm and not any(t in sm.group(1) for t in
                                  ("Primes", "×", ".1", ".2", "indicator", "Set.indicator")):
                    try:
                        full = parse(sbody)
                    except Exception:
                        full = None
                    if (full and full[0] == "expr" and full[1][0] == "app"
                            and full[1][1] == ("var", "Summable") and len(full[1][2]) == 1):
                        return handle_summable(neg, full[1][2][0], d, sm.group(1))
            return (UNABLE, why, "")
    # ── `(A ↔ B) ∧ C` — a top-level conjunction ONE OF WHOSE MEMBERS is an equivalence
    # (DLMF 31.2.3 / 31.14.1 / 31.14.4: a normal-form equivalence printed together with the
    # display's own side condition, `A+B+C = 0` resp. `∑_j q̃_j = 0`). The tokenizer has no
    # '↔' token and `_split_top_iff` sees none at depth 0 (the '↔' is inside the member's
    # parentheses), so the whole row died as `unparsed:char '↔'` before ANY member could be
    # scored — including the purely algebraic side condition, which is an ordinary numeric
    # equality. Split at depth-0 '∧' and score each member INDEPENDENTLY through this same
    # dispatcher (the '↔' member then takes the iff path below; an equation member the
    # ordinary sweep), combining with the SAME rule the parsed ("and", …) path uses: FAIL if
    # any member FAILs, PASS only if EVERY member PASSes, otherwise the honest
    # `conjunction-partial` skip naming each member's verdict. A member the oracle cannot
    # check is therefore NEVER absorbed into a PASS — the conjunction is only as decided as
    # its weakest member.
    # ADDITIVE, guarded: fires only when the conclusion contains '↔', has NO depth-0 '↔' of
    # its own (that shape already has the handle_iff path), splits into ≥ 2 non-empty
    # members, and NO member other than the last opens a depth-0 binder — a `∀ j,` / `∑ j,`
    # / `fun t =>` there would mean the split cut a member out of that binder's scope
    # (`∀ j, P j ∧ Q j` is ONE quantified conjunction). A binder confined to the last member
    # (the `∑ j, q̃ j = 0` side conditions) swallows nothing and is admitted. Any conclusion
    # failing a guard reaches parse() exactly as before.
    if "↔" in c and _split_top_iff(c) is None:
        _members = _split_top_and_text(c)
        if (len(_members) >= 2 and all(_members)
                and not any(_opens_binder(m) for m in _members[:-1])):
            _verds, _kinds = [], []
            for _m in _members:
                _v, _k, _det = _classify_and_check({**d, "concl": _strip_outer_parens(_m)})
                _verds.append(_v)
                _kinds.append(f"{_k}({_det})" if _det else _k)
            if "FAIL" in _verds:
                return ("FAIL", "conjunction",
                        f"a conjunct FAILed: {_verds}; members={_kinds}")
            if all(_v == "PASS" for _v in _verds):
                return ("PASS", "conjunction", f"{len(_verds)} conjuncts")
            return (UNABLE, "conjunction-partial", f"{_verds}; members={_kinds}")
    # a top-level '↔' between ∀-quantified equalities (DLMF 27.5 Möbius inversion) —
    # witness-constructed implication check; any other iff shape skips honestly inside.
    if "↔" in c:
        sides = _split_top_iff(c)
        if sides is not None:
            res = handle_iff(sides[0], sides[1], d)
            if res[0] == UNABLE:
                # not the Möbius shape — try the BOOLEAN '↔' sweep (both sides
                # per-sample decidable booleans: `legendreSym p a = -1 ↔
                # ¬ IsSquare (a : ZMod p)`, DLMF 27.9). None keeps `res` honestly.
                bres = handle_bool_iff(sides[0], sides[1], d)
                if bres is not None:
                    return bres
            return res
    try:
        ast = parse(c)
    except Unparseable as e:
        return (UNABLE, f"unparsed:{e}", "")
    except Exception:
        return (UNABLE, "parse-error", "")
    ast = _unfold_ode_pred(ast)                # IsMathieuSE-style def-predicate → ∀ x, ∧-of-eqs
    ast = _unfold_cd_pred(ast)                 # IsCDSystem → ∀ k, base ∧ step (DLMF 18.2.12)
    ast = _inline_local_defs(ast, _file_local_defs(d))   # δ-reduce file-local helper defs (L/R, f/c)
    if ast[0] == "exists":                     # ∃ v : T, body — existence (never FAIL)
        return handle_exists(ast[1], ast[2], d)
    if ast[0] == "forall":                     # ∀ v : T, body — sample v as an extra binder
        # The ∀-quantifier's OWN parsed type wins on a name collision: inside its body the
        # locally-bound v has definitionally the quantifier's type, whereas a same-named
        # d["binders"] entry can be a mis-scrape — e.g. a `(k : ℝ)` COERCION inside a
        # nested hypothesis recorded as a fresh real binder k, which used to beat the
        # correct outer `∀ k : ℕ` and fed real k into ℕ-only heads
        # (expint_6_10_1_cCoeff_eq_laplaceCoeff_of_recurrence, DLMF 6.10.3). Binders for
        # names NOT bound by this ∀ are untouched.
        d = {**d, "binders": {**d["binders"], **ast[1]}}
        ast = ast[2]
    if ast[0] == "and":                       # A ∧ B ∧ … — true iff every conjunct holds
        def _conjunct_verdict(part, dd):
            """Verdict of ONE conjunct against decl-dict `dd` (binders/constraints)."""
            bn, cn = dd["binders"], dd.get("constraints")
            # Parenthesized first conjuncts parse as `expr(eq(...))` while
            # unparenthesized siblings parse as bare `eq`.  Parentheses carry
            # no logical content, so normalize the wrapper before dispatch.
            if part[0] == "expr" and isinstance(part[1], tuple) \
                    and part[1][0] in ("eq", "ineq"):
                part = part[1]
            if part[0] == "eq":
                return sweep_eq(part[1], part[2], bn, cn)[0]
            if part[0] == "ineq":
                return sweep_ineq(part[1], part[2], part[3], bn, cn)[0]
            if part[0] == "expr" and part[1][0] == "app" and \
                    part[1][1] in (("var", "Tendsto"), ("var", "Filter.Tendsto")):
                return handle_tendsto(part[1][2], dd)[0]     # a Tendsto conjunct → limit-gate it
            if part[0] == "expr" and part[1][0] == "app" and part[1][1] == ("var", "HasDerivAt"):
                return handle_deriv(part[1][2], dd)[0]
            if part[0] == "expr" and part[1][0] == "app" and part[1][1] == ("var", "HasSum"):
                return handle_hassum(part[1][2], dd)[0]
            return UNABLE                     # a conjunct of an unsupported shape → can't check this one

        verdicts = []
        for part in ast[1]:
            # ∀-QUANTIFIED conjunct `(∀ x, f x = g x) ∧ (∀ y, h y = k y)` (a multi-line
            # display whose rows carry their own binder). Sample the quantified variable
            # as an extra binder FOR THIS CONJUNCT ONLY — a sibling row's binder must not
            # leak into the next row's sample space — then dispatch the inner relation
            # exactly as an unquantified conjunct. The ∀-binder's own parsed type wins on
            # a name collision, matching the top-level ("forall", …) policy above.
            if part[0] == "expr" and isinstance(part[1], tuple) and part[1][0] == "forallq":
                part = part[1]                # relation() wraps a parenthesized (∀ …) as expr
            if part[0] == "forallq":
                verdicts.append(_conjunct_verdict(
                    part[2], {**d, "binders": {**d["binders"], **part[1]}}))
                continue
            verdicts.append(_conjunct_verdict(part, d))
        if "FAIL" in verdicts:
            return ("FAIL", "conjunction", f"a conjunct FAILed: {verdicts}")
        if all(v == "PASS" for v in verdicts):
            return ("PASS", "conjunction", f"{len(verdicts)} conjuncts")
        return (UNABLE, "conjunction-partial", str(verdicts))
    if ast[0] == "eq" and (_is_fourier(ast[1]) or _is_fourier(ast[2])):
        return handle_fourier(ast[1], ast[2], d)
    if ast[0] == "eq":
        v, det = sweep_eq(ast[1], ast[2], d["binders"], d.get("constraints"))
        return (v, "equality", det)
    if ast[0] == "ne":
        v, det = sweep_eq(ast[1], ast[2], d["binders"], d.get("constraints"), relation="ne")
        return (v, "disequality", det)
    if ast[0] == "asymp":                      # f ~[F] g / =O[F] / =o[F] — rate-gate
        return handle_asymptotic(ast[1], ast[2], ast[3], ast[4], d)
    if ast[0] == "ineq":
        v, det = sweep_ineq(ast[1], ast[2], ast[3], d["binders"], d.get("constraints"))
        return (v, "inequality", det)
    if ast[0] == "mem":                       # e ∈ Icc/Ioo/… interval membership
        return handle_mem(ast[1], ast[2], d)
    if ast[0] == "expr" and ast[1][0] == "app" and ast[1][1] == ("var", "HasDerivAt"):
        return handle_deriv(ast[1][2], d)
    if ast[0] == "expr" and ast[1][0] == "app" and ast[1][1] in (("var", "Tendsto"), ("var", "Filter.Tendsto")):
        return handle_tendsto(ast[1][2], d)
    if ast[0] == "expr" and ast[1][0] == "app" and ast[1][1] == ("var", "HasSum"):
        return handle_hassum(ast[1][2], d)
    if ast[0] == "expr" and ast[1][0] == "app" and ast[1][1] == ("var", "HasProd"):
        return handle_hasprod(ast[1][2], d)
    # an `IsHeunSolution a q α β γ δ (fun ζ => …) z` CONCLUSION (DLMF 31.3.5–31.3.11):
    # expand the DEFINED predicate into its cleared-denominator Heun equation 31.2.1 and
    # score the residual numerically (see handle_heun_solution). None → fall through to the
    # honest non-equality skip below, exactly as before.
    if (ast[0] == "expr" and ast[1][0] == "app" and ast[1][1][0] == "var"
            and ast[1][1][1].split(".")[-1] == "IsHeunSolution"):
        hs = handle_heun_solution(ast[1][2], d)
        if hs is not None:
            return hs
    # an `IsMultiplicative f` CONCLUSION with a concrete applied f (Mathlib
    # `ArithmeticFunction.IsMultiplicative`, prefix or dot form — e.g.
    # `(jordanTotientFn k).IsMultiplicative`, DLMF 27.3): expand into the two
    # DEFINING equality sweeps of 27.3.1 — (1) f 1 = 1, and (2) f (m·n) = f m · f n
    # over coprime pairs (m, n), reusing the same '_pairs' coprime sample filter the
    # `h : m.Coprime n` hypothesis path uses. FAIL if either sweep refutes; PASS only
    # if both pass. Additive and conservative: fires only when f is a plain applied
    # chain of simple tokens (a registry head + binder args) — anything else keeps
    # the honest non-equality skip below, and an unbound head still surfaces as the
    # sweep's own `unbound:<fn>` skip, never a fabricated verdict.
    mm = re.match(r'^(?:ArithmeticFunction\.)?IsMultiplicative\s+(.+)$', c) or \
         re.match(r'^\(([^()]+)\)\.IsMultiplicative$', c) or \
         re.match(r"^([\w.']+(?:\s+[\w.']+)*)\.IsMultiplicative$", c)
    if mm:
        f = mm.group(1).strip()
        if re.fullmatch(r"[\w.']+(?:\s+[\w.']+)*", f):
            vm = next(v for v in ("m", "m'", "m₁") if v not in d["binders"])
            vn = next(v for v in ("n", "n'", "n₁") if v not in d["binders"] and v != vm)
            cons = {k2: v2 for k2, v2 in (d.get("constraints") or {}).items()}
            cons["_pairs"] = list(cons.get("_pairs", [])) + [["coprime", vm, vn]]
            d1 = {**d, "concl": f"{f} 1 = 1"}
            d2 = {**d, "concl": f"{f} ({vm} * {vn}) = {f} {vm} * {f} {vn}",
                  "binders": {**d["binders"], vm: "N", vn: "N"},
                  "constraints": cons}
            v1, _, det1 = _classify_and_check(d1)
            v2, _, det2 = _classify_and_check(d2)
            if "FAIL" in (v1, v2):
                return ("FAIL", "is-multiplicative",
                        f"f(1)=1: {v1} ({det1}); f(mn)=f(m)f(n) coprime: {v2} ({det2})")
            if v1 == "PASS" and v2 == "PASS":
                return ("PASS", "is-multiplicative",
                        f"f(1)=1 {det1}; f(mn)=f(m)f(n) coprime {det2}")
            return (UNABLE, "is-multiplicative-partial",
                    f"f(1)=1: {v1} ({det1}); f(mn)=f(m)f(n): {v2} ({det2})")
    # an `IsCompletelyMultiplicative f` CONCLUSION (FLMF.NumberTheory, DLMF 27.3.9) with a
    # concrete applied f (e.g. `IsCompletelyMultiplicative liouville`): expand into the two
    # DEFINING equality sweeps of 27.3.9 — (1) f 1 = 1 exactly, and (2) the product rule
    # f (m·n) = f m · f n over ALL sampled pairs (m, n) from the ℕ grid. Unlike the 27.3.1
    # branch above there is deliberately NO coprimality filter: complete multiplicativity
    # demands the product rule unconditionally, so sampling unrestricted pairs is the
    # faithful (and strictly stronger) check. Same additive/conservative guard: fires only
    # when f is a plain applied chain of simple tokens; anything else keeps the honest
    # non-equality skip, and an unbound head surfaces as the sweep's own `unbound:<fn>`.
    mcm = re.match(r'^(?:FLMF\.)?(?:NumberTheory\.)?IsCompletelyMultiplicative\s+(.+)$', c) or \
          re.match(r'^\(([^()]+)\)\.IsCompletelyMultiplicative$', c) or \
          re.match(r"^([\w.']+(?:\s+[\w.']+)*)\.IsCompletelyMultiplicative$", c)
    if mcm:
        f = mcm.group(1).strip()
        if re.fullmatch(r"[\w.']+(?:\s+[\w.']+)*", f):
            vm = next(v for v in ("m", "m'", "m₁") if v not in d["binders"])
            vn = next(v for v in ("n", "n'", "n₁") if v not in d["binders"] and v != vm)
            d1 = {**d, "concl": f"{f} 1 = 1"}
            d2 = {**d, "concl": f"{f} ({vm} * {vn}) = {f} {vm} * {f} {vn}",
                  "binders": {**d["binders"], vm: "N", vn: "N"}}
            v1, _, det1 = _classify_and_check(d1)
            v2, _, det2 = _classify_and_check(d2)
            if "FAIL" in (v1, v2):
                return ("FAIL", "is-completely-multiplicative",
                        f"f(1)=1: {v1} ({det1}); f(mn)=f(m)f(n) all pairs: {v2} ({det2})")
            if v1 == "PASS" and v2 == "PASS":
                return ("PASS", "is-completely-multiplicative",
                        f"f(1)=1 {det1}; f(mn)=f(m)f(n) all pairs {det2}")
            return (UNABLE, "is-completely-multiplicative-partial",
                    f"f(1)=1: {v1} ({det1}); f(mn)=f(m)f(n): {v2} ({det2})")
    return (UNABLE, "non-equality", "")

import time


# ══════════════════════════════════════════════════════════════════════════════
# §31.15 Stieltjes / Van Vleck polynomials — hypothesis-pinned numeric witnesses
#
# The §31.15(ii)/(iii) displays talk about data that exists ONLY through the
# theorem's own hypotheses: a Stieltjes polynomial `S` (and its Van Vleck partner
# `V`) pinned by `IsStieltjes` / `IsStieltjesVanVleckPair`, its zeros `z` pinned by
# the factorization hypothesis, the zeros `zp` of `S'`, a zero `t` of `V`, the
# accessory parameters `q` pinned by the partial-fraction hypothesis, the energy
# function `G` pinned by its defining identity, and an equilibrium configuration
# `ζ`.  With none of that bound, the sweep skipped the rows as `unparsed:'∨'`,
# `unbound:G`, `unbound:q`, `unbound:stieltjesInner` — sampling the binders freely
# would have scored the displays OUTSIDE their hypotheses and fabricated FAILs.
#
# The witnesses below are built from the DEFINING condition of §31.15(i) ALONE,
#
#     A(z) S''(z) + B(z) S'(z) + V(z) S(z) = 0   identically,
#     A(z) = ∏_j (z − a_j),   B(z) = ∑_j γ_j ∏_{k≠j} (z − a_k),
#     deg V ≤ N − 2,   deg S = n
#
# (i.e. `IsStieltjesVanVleckPair` unfolded through `IsFuchsianSolution`, the two
# FLMF carriers of DLMF 31.15.1) — as the Heine–Stieltjes spectral problem, never
# from 31.15.2/31.15.4, the very displays under test.  Every hypothesis is then
# RE-VERIFIED numerically on the constructed witness (ODE residual, degrees, the
# factorization/partial-fraction/equilibrium identities parsed from the theorem's
# own signature) before the conclusion is scored, so a witness that drifts out of
# the hypotheses is dropped, never scored.
#
# ADDITIVE: nothing is loosened.  The path fires only when the signature exhibits
# the §31.15 defining hypotheses AND every free variable of the conclusion is
# covered by the witness; otherwise it returns None and the row keeps its prior
# honest skip.
# ══════════════════════════════════════════════════════════════════════════════

def _st_padd(p, q):
    m = max(len(p), len(q))
    return [(p[i] if i < len(p) else mp.mpf(0)) + (q[i] if i < len(q) else mp.mpf(0))
            for i in range(m)]


def _st_pmul(p, q):
    r = [mp.mpf(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


def _st_pscale(p, s):
    return [s * x for x in p]


def _st_pder(p):
    return [p[i] * i for i in range(1, len(p))] or [mp.mpf(0)]


def _st_pval(p, x):
    r = mp.mpf(0) * x
    for c in reversed(p):
        r = r * x + c
    return r


def _st_from_roots(rs):
    p = [mp.mpf(1)]
    for r in rs:
        p = _st_pmul(p, [-r, mp.mpf(1)])
    return p


def _st_AB(a, gam):
    """A(z) = ∏_j (z−a_j) and B(z) = ∑_j γ_j ∏_{k≠j} (z−a_k) — the two polynomial
    coefficients of `IsFuchsianSolution` (FLMF/Frameworks/Heun/Stieltjes.lean,
    DLMF 31.15.1)."""
    N = len(a)
    A = _st_from_roots(a)
    B = [mp.mpf(0)]
    for j in range(N):
        B = _st_padd(B, _st_pscale(_st_from_roots([a[k] for k in range(N) if k != j]), gam[j]))
    return A, B


def _st_residual(a, gam, V, S):
    """max |coefficient| of A S'' + B S' + V S — zero iff `IsFuchsianSolution γ a V S z`
    holds at EVERY z (a polynomial identity), which is the third field of
    `IsStieltjesVanVleckPair`."""
    A, B = _st_AB(a, gam)
    R = _st_padd(_st_padd(_st_pmul(A, _st_pder(_st_pder(S))), _st_pmul(B, _st_pder(S))),
                 _st_pmul(V, S))
    return max(abs(x) for x in R)


def _st_pairs(a, gam, n, want_real):
    """Every Van Vleck / Stieltjes pair (V, S) of §31.15(i) with deg S = n, for
    N = len(a) ∈ {2, 3}: S monic of degree n, deg V ≤ N−2.

    N = 2: V is the constant −n(n−1+∑γ) forced by the leading coefficient, and the
    remaining n coefficient equations are LINEAR in S — one pair, matching the
    §31.15(i) count C(n+N−2, N−2) = 1.
    N = 3: V(z) = v₁z + v₀ with v₁ = −n(n−1+∑γ) forced the same way; the operator
    T(S) = A S'' + B S' + v₁ z S then maps degree-≤n polynomials to themselves and
    the identity reads T(S) = −v₀ S — an (n+1)×(n+1) eigenproblem whose n+1
    eigenpairs are the C(n+1, 1) pairs of §31.15(i).
    """
    N = len(a)
    if n == 0:
        return [([mp.mpf(0)] * max(1, N - 1), [mp.mpf(1)])]
    A, B = _st_AB(a, gam)
    sg = sum(gam)
    vtop = -n * (n - 1 + sg)
    if N == 2:
        cols = []
        for m in range(n + 1):
            e = [mp.mpf(0)] * (m + 1)
            e[m] = mp.mpf(1)
            r = _st_padd(_st_padd(_st_pmul(A, _st_pder(_st_pder(e))), _st_pmul(B, _st_pder(e))),
                         _st_pscale(e, vtop))
            r = list(r) + [mp.mpf(0)] * (n + 2 - len(r))
            cols.append(r[:n + 1])
        M = mp.matrix(n, n)
        rhs = mp.matrix(n, 1)
        for i in range(n):
            for m in range(n):
                M[i, m] = cols[m][i]
            rhs[i] = -cols[n][i]
        c = mp.lu_solve(M, rhs)
        return [([vtop], [c[i] for i in range(n)] + [mp.mpf(1)])]
    if N == 3:
        M = mp.matrix(n + 1, n + 1)
        for m in range(n + 1):
            e = [mp.mpf(0)] * (m + 1)
            e[m] = mp.mpf(1)
            r = _st_padd(_st_padd(_st_pmul(A, _st_pder(_st_pder(e))), _st_pmul(B, _st_pder(e))),
                         _st_pscale(_st_pmul([mp.mpf(0), mp.mpf(1)], e), vtop))
            r = list(r) + [mp.mpf(0)] * (n + 3 - len(r))
            if abs(r[n + 1]) > mp.mpf("1e-20") * (1 + abs(vtop)):
                return []                       # leading cancellation lost — drop, never guess
            for i in range(n + 1):
                M[i, m] = r[i]
        E, ER = mp.eig(mp.matrix([[mp.mpc(M[i, j]) for j in range(n + 1)]
                                  for i in range(n + 1)]))
        out = []
        for idx in range(n + 1):
            lam = E[idx]
            vec = [ER[i, idx] for i in range(n + 1)]
            big = max(abs(v) for v in vec)
            if abs(vec[n]) < mp.mpf("1e-10") * big:
                continue                        # deg S < n — not a degree-n Stieltjes poly
            S = [v / vec[n] for v in vec]
            v0 = -lam
            if want_real:
                if abs(mp.im(lam)) > mp.mpf("1e-16") * max(1, abs(lam)):
                    continue
                if max(abs(mp.im(v)) for v in S) > mp.mpf("1e-14"):
                    continue
                S = [mp.re(v) for v in S]
                v0 = mp.re(v0)
            out.append(([v0, vtop], S))
        return out
    return []


def _st_roots(p):
    return list(mp.polyroots(list(reversed(p)), maxsteps=300, extraprec=300))


def _st_rho(gam, a, z):
    """`stieltjesWeight γ a z` (FLMF/Frameworks/Heun/Stieltjes.lean; its defining
    identity is DLMF 31.15.12, surfaced as `heun_31_15_12`)."""
    t = mp.mpf(1)
    for zj in z:
        for k in range(len(a)):
            t *= mp.power(abs(zj - a[k]), gam[k] - 1)
    for j in range(len(z)):
        for k in range(j + 1, len(z)):
            t *= (z[k] - z[j])
    return t


def _st_cell_inner(gam, a, f, g, maxdeg=4):
    """`stieltjesInner γ a f g` = ∫_Q f(z) conj(g(z)) ρ(z) dz over the cell
    Q = (a₁,a₂) × ⋯ × (a_{N−1},a_N) (DLMF 31.15.10/31.15.11)."""
    Nm1 = len(a) - 1
    ivals = [[a[j], a[j + 1]] for j in range(Nm1)]
    if Nm1 == 1:
        return mp.quad(lambda x: f([x]) * mp.conj(g([x])) * _st_rho(gam, a, [x]),
                       ivals[0], maxdegree=maxdeg)
    if Nm1 == 2:
        return mp.quad(lambda x, y: f([x, y]) * mp.conj(g([x, y])) * _st_rho(gam, a, [x, y]),
                       ivals[0], ivals[1], maxdegree=maxdeg)
    raise Unparseable("stieltjes-cell-dim")


# ── role scanner ─────────────────────────────────────────────────────────────
_ST_ID = r"[A-Za-zα-ωζξγΦ_][\w'′ₘₗ]*"


def _stieltjes_witness(sig, concl, binders, cons):
    """Record the §31.15 hypothesis roles of a theorem head into `cons['_stieltjes']`.

    Every pattern below is anchored on the LITERAL defining text of the FLMF carrier
    or of the DLMF display it transcribes (`IsStieltjes`/`IsStieltjesVanVleckPair`,
    the factorization `S = C c ∏(X − z k)`, `V.eval t = 0`, the partial-fraction
    identity of 31.14.1, the energy product of 31.15.4, the equilibrium system of
    31.15.2, the interval root counts of 31.15.8), never on a declaration name.  A
    head that does not exhibit them records nothing and the row is untouched."""
    colon = _colon_index(sig)
    if colon < 0:
        return
    head = sig[:colon]
    # cheap fast path: either a §31.15(i) carrier, or the `Σ_{k≠j}` erase-sum of the
    # 31.15.2 equilibrium system (the 31.15.4 head names no Stieltjes carrier at all).
    if "Stieltjes" not in head and "Finset.univ.erase" not in head:
        return
    st = {"vec": {}, "polys": {}, "roots": {}, "vzero": {}, "resid": {},
          "energy": {}, "equil": None, "multiidx": {}, "gpos": [], "aord": []}
    for grp in _head_groups(head):
        g = " ".join(grp.split())
        if ":" not in g:
            continue
        lhs, _, ty = g.partition(":")
        names = lhs.split()
        ty = ty.strip()
        # value tuples `γ a : Fin N → ℝ/ℂ`
        mv = re.match(r'^Fin\s+(.+?)\s*→\s*(ℝ|ℂ)$', ty)
        if mv and all(re.fullmatch(_ST_ID, x) for x in names):
            for nm in names:
                st["vec"][nm] = (mv.group(1).strip(), mv.group(2))
            continue
        if len(names) != 1:
            continue
        h = names[0]
        m = re.match(r'^IsStieltjes(VanVleckPair)?\s+(.+)$', ty)
        if m:
            args = _split_top_ws(m.group(2))
            if m.group(1) and len(args) == 5:
                st["polys"][args[4]] = {"gam": args[0], "a": args[1], "deg": args[2],
                                        "V": args[3]}
            elif not m.group(1) and len(args) == 4:
                st["polys"][args[3]] = {"gam": args[0], "a": args[1], "deg": args[2],
                                        "V": None}
            continue
        m = re.match(r'^(Polynomial\.derivative\s+)?(' + _ST_ID + r')\s*=\s*Polynomial\.C\s+('
                     + _ST_ID + r')\s*\*\s*∏\s*(' + _ST_ID + r'),\s*\(Polynomial\.X\s*-\s*'
                     r'Polynomial\.C\s*\((' + _ST_ID + r')\s+\4\)\)$', ty)
        if m:
            st["roots"][m.group(5)] = {"of": m.group(2), "lead": m.group(3),
                                       "deriv": bool(m.group(1))}
            continue
        m = re.match(r'^(' + _ST_ID + r')\.eval\s+(' + _ST_ID + r')\s*=\s*0$', ty)
        if m:
            st["vzero"][m.group(2)] = m.group(1)
            continue
        # partial-fraction pinning of the accessory parameters (DLMF 31.14.1 / 31.15.7)
        m = re.match(r'^∀\s+(' + _ST_ID + r')\s*:\s*ℝ,\s*\(∀\s+(' + _ST_ID + r'),\s*\1\s*≠\s*('
                     + _ST_ID + r')\s+\2\)\s*→\s*∑\s+(' + _ST_ID + r'),\s*(' + _ST_ID +
                     r')\s+\4\s*/\s*\(\1\s*-\s*\3\s+\4\)\s*=\s*(' + _ST_ID +
                     r')\.eval\s+\1\s*/\s*∏\s+(' + _ST_ID + r'),\s*\(\1\s*-\s*\3\s+\7\)$', ty)
        if m:
            st["resid"][m.group(5)] = {"a": m.group(3), "V": m.group(6), "x": m.group(1)}
            continue
        # the energy G of DLMF 31.15.4, pinned by its own defining identity
        m = re.match(r'^∀\s+(' + _ST_ID + r')\s*:\s*Fin\s+(.+?)\s*→\s*ℝ,\s*(' + _ST_ID +
                     r')\s+\1\s*=\s*(.+)$', ty)
        if m:
            st["energy"][m.group(3)] = {"var": m.group(1), "dim": m.group(2).strip(),
                                        "rhs": m.group(4).strip()}
            continue
        # the equilibrium system of DLMF 31.15.2, as a standing hypothesis
        m = re.match(r'^∀\s+(' + _ST_ID + r'),\s*∑\s+(' + _ST_ID + r'),\s*(' + _ST_ID +
                     r')\s+\2\s*/\s*\(2\s*\*\s*\((' + _ST_ID + r')\s+\1\s*-\s*(' + _ST_ID +
                     r')\s+\2\)\)\s*\+\s*∑\s+(' + _ST_ID + r')\s*∈\s*Finset\.univ\.erase\s+\1,'
                     r'\s*1\s*/\s*\(\4\s+\1\s*-\s*\4\s+\6\)\s*=\s*0$', ty)
        if m:
            st["equil"] = {"k": m.group(1), "gam": m.group(3), "zeta": m.group(4),
                           "a": m.group(5), "eq": ty}
            continue
        # the interval root counts of DLMF 31.15.8 (the multi-index label of S_m)
        m = re.match(r'^∀\s+(' + _ST_ID + r'),\s*Multiset\.card\s*\((' + _ST_ID +
                     r')\.roots\.filter\s*\(fun\s+(' + _ST_ID + r')\s*=>\s*\3\s*∈\s*Set\.Ioo\s*\(('
                     + _ST_ID + r')\s*\(cellLeft\s+\1\)\)\s*\(\4\s*\(cellRight\s+\1\)\)\)\)'
                     r'\s*=\s*(' + _ST_ID + r')\s+\1$', ty)
        if m:
            st["multiidx"][m.group(2)] = m.group(5)
            continue
        m = re.match(r'^StieltjesRealConditions\s+(' + _ST_ID + r')$', ty)
        if m:
            st["gpos"].append(m.group(1))
            continue
        m = re.match(r'^StieltjesOrderedNodes\s+(' + _ST_ID + r')$', ty)
        if m:
            st["aord"].append(m.group(1))
            continue
    if not (st["polys"] or st["equil"]):
        return
    # the (γ, a) pair every witness is built from: from a carrier hypothesis, else from
    # the equilibrium system.  Both must be `Fin N → 𝕜` tuples of the SAME dimension.
    if st["polys"]:
        any_p = next(iter(st["polys"].values()))
        gname, aname = any_p["gam"], any_p["a"]
    else:
        gname, aname = st["equil"]["gam"], st["equil"]["a"]
    if gname not in st["vec"] or aname not in st["vec"]:
        return
    if st["vec"][gname][0] != st["vec"][aname][0]:
        return
    st["gam"], st["a"] = gname, aname
    st["Ndim"] = st["vec"][gname][0]
    st["field"] = st["vec"][gname][1]
    cons["_stieltjes"] = st


# ── the sample families ──────────────────────────────────────────────────────
_ST_REAL_PARAMS = [                       # a strictly increasing, γ strictly positive
    ([mp.mpf("-1"), mp.mpf("0.4"), mp.mpf("2.1")],
     [mp.mpf("1.3"), mp.mpf("0.7"), mp.mpf("2.2")]),
    ([mp.mpf("0"), mp.mpf("1"), mp.mpf("3")],
     [mp.mpf("0.5"), mp.mpf("1.5"), mp.mpf("0.9")]),
    ([mp.mpf("-2"), mp.mpf("0.25"), mp.mpf("1")],
     [mp.mpf("2.0"), mp.mpf("1.1"), mp.mpf("0.6")]),
    ([mp.mpf("-1"), mp.mpf("1")], [mp.mpf("1.4"), mp.mpf("0.8")]),
    ([mp.mpf("0"), mp.mpf("2.5")], [mp.mpf("2.6"), mp.mpf("1.2")]),
]
_ST_CPLX_PARAMS = [
    ([mp.mpc("-1", "0.3"), mp.mpc("0.4", "-0.2"), mp.mpc("2.1", "0.5")],
     [mp.mpc("1.3", "0.4"), mp.mpc("0.7", "-0.6"), mp.mpc("2.2", "0.1")]),
    ([mp.mpc("0.2", "-0.7"), mp.mpc("1.1", "0.9")],
     [mp.mpc("0.9", "0.2"), mp.mpc("1.7", "-0.5")]),
]


def _st_holds(residual, terms, gate_true):
    scale = max([abs(t) for t in terms] + [mp.mpf("1e-300")])
    rel = abs(residual) / scale
    if rel < gate_true:
        return True, rel
    if rel > _SOLIFF_FALSE_EPS:
        return False, rel
    return None, rel


def _st_expr(ast):
    """Strip the parser's `('expr', …)` wrapper."""
    while isinstance(ast, tuple) and ast[0] == "expr":
        ast = ast[1]
    return ast


def _st_univ_q(node, var, env):
    """Cardinality of the `Finset.univ` a bare `∑ j, …` / `∑ j ∈ univ.erase k, …` ranges
    over: the `.q` tag of a vector the bound index is applied to (the same lookup
    `evaluate` itself uses for these nodes)."""
    q = [None]

    def scan(nd):
        if isinstance(nd, tuple):
            if nd[0] == "app" and nd[1][0] == "var" and nd[2] == [("var", var)]:
                f = env.get(nd[1][1])
                if callable(f) and hasattr(f, "q"):
                    q[0] = f.q
            for c in nd[1:]:
                scan(c)
        elif isinstance(nd, list):
            for c in nd:
                scan(c)
    scan(node)
    return q[0]


def _st_terms(node, env, acc):
    """Magnitudes of the ATOMIC cancelling terms of an expression — the homogeneity scale
    of a residual.  Unlike `_add_terms` this descends THROUGH a finite `∑` into its
    summands: the §31.15(ii) displays are sums of individually O(1) terms that cancel to
    zero, so scoring `Σ₁ + Σ₂ = 0` against max(|Σ₁|, |Σ₂|) would compare the residual with
    itself and read every true instance as rel = 1."""
    if isinstance(node, tuple) and node[0] == "bin" and node[1] in ("+", "-"):
        _st_terms(node[2], env, acc)
        _st_terms(node[3], env, acc)
        return acc
    if isinstance(node, tuple) and node[0] == "sum" and len(node) == 5 and node[3] == "ℕ":
        q = _st_univ_q(node[2], node[1], env)
        if q is not None:
            for i in range(int(q)):
                _st_terms(node[2], {**env, node[1]: mp.mpf(i)}, acc)
            return acc
    if isinstance(node, tuple) and node[0] == "funiverase" and node[1] == "fsum":
        q = _st_univ_q(node[4], node[2], env)
        if q is not None:
            skip = int(mp.re(evaluate(node[3], env)))
            for i in range(int(q)):
                if i != skip:
                    _st_terms(node[4], {**env, node[2]: mp.mpf(i)}, acc)
            return acc
    acc.append(abs(evaluate(node, env)))
    return acc


def _st_prop_holds(node, env, gate_true):
    """True / False / None (undecidable at this sample) for ONE disjunct."""
    if node[0] == "expr":
        node = node[1]
    if node[0] != "eq":
        raise Unparseable("stieltjes-disjunct")
    tv = _st_terms(node[1], env, []) + _st_terms(node[2], env, [])
    res = evaluate(node[1], env) - evaluate(node[2], env)
    return _st_holds(res, tv, gate_true)


def _st_exists_holds(var, body, env, gate_true):
    """`∃ j, L = R` over the Fin-index `var`: the index range is read off the `.q` tag
    of the vector the bound index is applied to."""
    ast = _st_expr(parse(body))
    if ast[0] != "eq":
        raise Unparseable("stieltjes-exists")
    q = None

    def scan(nd):
        nonlocal q
        if isinstance(nd, tuple):
            if nd[0] == "app" and nd[1][0] == "var" and nd[2] == [("var", var)]:
                f = env.get(nd[1][1])
                if callable(f) and hasattr(f, "q"):
                    q = f.q
            for c in nd[1:]:
                scan(c)
        elif isinstance(nd, list):
            for c in nd:
                scan(c)
    scan(ast)
    if q is None:
        raise Unparseable("stieltjes-exists-range")
    best = None
    for i in range(int(q)):
        e2 = {**env, var: mp.mpf(i)}
        tv = _st_terms(ast[1], e2, []) + _st_terms(ast[2], e2, [])
        h, rel = _st_holds(evaluate(ast[1], e2) - evaluate(ast[2], e2), tv, gate_true)
        if h:
            return True, rel
        best = rel if best is None else min(best, rel)
    return False, best


def _st_disjuncts(concl):
    """Depth-0 '∨' members of a conclusion, as raw text (1 element when there is none).
    The tokenizer has no '∨' token, so this is how a disjunctive conclusion is reached
    at all; each member is then parsed and scored on its own."""
    out, depth, cur = [], 0, ""
    for ch in concl:
        if ch in "([{":
            depth += 1
            cur += ch
        elif ch in ")]}":
            depth -= 1
            cur += ch
        elif ch == "∨" and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [p.strip() for p in out]


def _st_finvec(vals):
    return _finvec_callable(list(vals))


def _st_update(vec, idx, val):
    i0 = int(mp.re(idx))

    def g(i):
        return val if int(mp.re(i)) == i0 else vec(i)
    g.q = getattr(vec, "q", 0)
    return g


def _st_gamma_from_equilibrium(a, zeta):
    """Solve the DLMF 31.15.2 equilibrium system — LINEAR in γ — for the charges γ,
    giving an exact instance of the hypothesis `_hequil` at a freely chosen zero
    configuration.  n < N, so the system is underdetermined; the least-norm solution
    is taken.  The hypothesis is re-verified on the result before use."""
    n, N = len(zeta), len(a)
    if n >= N:
        return None
    A = mp.matrix(n, N)
    b = mp.matrix(n, 1)
    for k in range(n):
        for j in range(N):
            A[k, j] = 1 / (2 * (zeta[k] - a[j]))
        b[k] = -sum(1 / (zeta[k] - zeta[j]) for j in range(n) if j != k)
    try:
        y = mp.lu_solve(A * A.T, b)
    except Exception:
        return None
    g0 = A.T * y
    return [g0[j] for j in range(N)]


_ST_EQUIL_ZETA = [
    ([mp.mpf("-1"), mp.mpf("0.3"), mp.mpf("2")], [mp.mpf("-0.4"), mp.mpf("1.1")]),
    ([mp.mpf("0"), mp.mpf("1"), mp.mpf("2.5"), mp.mpf("4")],
     [mp.mpf("0.5"), mp.mpf("1.7"), mp.mpf("3.1")]),
    ([mp.mpf("-2"), mp.mpf("0.5"), mp.mpf("1.5")], [mp.mpf("-1.2")]),
    ([mp.mpf("-1"), mp.mpf("0.25"), mp.mpf("1"), mp.mpf("2.5")],
     [mp.mpf("-0.6"), mp.mpf("1.9")]),
]


def _st_base_env(d, extra):
    binders = d["binders"]
    env = {"_intvars": {v for v, t in binders.items() if t in ("Z", "N")},
           "_binders": binders}
    env.update(extra)
    return env


def _st_energy_env(st, d):
    """Witness environments for the DLMF 31.15.4 shape: a freely chosen zero
    configuration ζ with the charges γ SOLVED from the equilibrium hypothesis, the
    energy `G` instantiated by the RIGHT-HAND SIDE OF ITS OWN DEFINING HYPOTHESIS
    (parsed from the signature — never a re-transcription of the display), and
    `Function.update` bound so the conclusion's directional derivative is the one
    the statement writes."""
    eq = st["equil"]
    gname, aname, zname = eq["gam"], eq["a"], eq["zeta"]
    eqast = _st_expr(parse(eq["eq"].split(",", 1)[1].strip()))
    gnames = list(st["energy"])
    if len(gnames) != 1:
        return
    Gname = gnames[0]
    en = st["energy"][Gname]
    Grhs = _st_expr(parse(en["rhs"]))
    for avals, zvals in _ST_EQUIL_ZETA:
        gvals = _st_gamma_from_equilibrium(avals, zvals)
        if gvals is None:
            continue
        env = _st_base_env(d, {gname: _st_finvec(gvals), aname: _st_finvec(avals),
                               zname: _st_finvec(zvals), "Function.update": _st_update})
        env[st["Ndim"]] = mp.mpf(len(avals))
        env[en["dim"]] = mp.mpf(len(zvals))

        def _G(vec, _env=env, _rhs=Grhs, _v=en["var"]):
            return evaluate(_rhs, {**_env, _v: vec})
        env[Gname] = _G
        # `_hζa : ∀ k l, ζ k ≠ a l` and `_hζ : Function.Injective ζ`
        if any(abs(zk - al) < mp.mpf("1e-6") for zk in zvals for al in avals):
            continue
        if any(abs(zvals[i] - zvals[j]) < mp.mpf("1e-6")
               for i in range(len(zvals)) for j in range(i)):
            continue
        # `_hequil` re-verified on the constructed γ, as the theorem's own text
        ok = True
        for kk in range(len(zvals)):
            e2 = {**env, eq["k"]: mp.mpf(kk)}
            h, _ = _st_prop_holds(eqast, e2, _SOLIFF_TRUE_EPS)
            if h is not True:
                ok = False
                break
        if not ok:
            continue
        # the homogeneity scale of `deriv (fun t => G (update ζ k t)) (ζ k) = 0`: the
        # derivative is G(ζ) times the SUM of the 31.15.2 terms, which cancel.
        for kk in range(len(zvals)):
            sc = abs(_G(_st_finvec(zvals))) * (
                sum(abs(gvals[l] / 2 / (zvals[kk] - avals[l])) for l in range(len(avals)))
                + sum(abs(1 / (zvals[kk] - zvals[j])) for j in range(len(zvals)) if j != kk))
            yield ({**env}, {"k": kk, "scale": sc,
                             "at": f"N={len(avals)}, n={len(zvals)}, k={kk}"})


def _st_poly_env(st, d):
    """Witness environments for the §31.15(ii)/(iii) shapes carrying a Stieltjes (or
    Van Vleck / Stieltjes) polynomial: build EVERY pair of §31.15(i) at a handful of
    (a, γ), re-verify the carrier numerically, then derive the hypothesis-pinned
    zeros / accessory parameters and re-verify their own pinning identities."""
    gname, aname = st["gam"], st["a"]
    real_only = bool(st["gpos"] or st["aord"] or st["field"] == "ℝ")
    params = list(_ST_REAL_PARAMS) if real_only else list(_ST_REAL_PARAMS) + list(_ST_CPLX_PARAMS)
    needs_vzero = bool(st["vzero"])
    needs_zp = any(r["deriv"] for r in st["roots"].values())
    Sname = next(iter(st["polys"]))
    Vname = st["polys"][Sname]["V"]
    degvars = [p["deg"] for p in st["polys"].values() if re.fullmatch(_ST_ID, p["deg"])]
    for avals, gvals in params:
        N = len(avals)
        if needs_vzero and N != 3:
            continue                       # deg V ≤ N−2 = 0 for N = 2: `V.eval t = 0` unusable
        for n in (2, 3, 1):
            if needs_zp and n < 2:
                continue
            try:
                prs = _st_pairs(avals, gvals, n, real_only)
            except Exception:
                continue
            for V, S in prs:
                if _st_residual(avals, gvals, V, S) > mp.mpf("1e-18"):
                    continue               # `IsFuchsianSolution` not witnessed — drop
                if len(V) - 1 > N - 2 and any(abs(x) > mp.mpf("1e-20") for x in V[N - 1:]):
                    continue               # `vanVleck_degree_le` violated — drop
                if abs(S[n]) < mp.mpf("1e-12"):
                    continue               # `stieltjes_degree` violated — drop
                extra = {gname: _st_finvec(gvals), aname: _st_finvec(avals)}
                extra[st["Ndim"]] = mp.mpf(N)
                for dv in degvars:
                    extra[dv] = mp.mpf(n)
                extra[f"{Sname}.eval"] = lambda x, _p=S: _st_pval(_p, x)
                if Vname:
                    extra[f"{Vname}.eval"] = lambda x, _p=V: _st_pval(_p, x)
                zr = _st_roots(S)
                zpr = _st_roots(_st_pder(S)) if n >= 2 else []
                bad = False
                for rname, info in st["roots"].items():
                    vals = zpr if info["deriv"] else zr
                    extra[rname] = _st_finvec(vals)
                    lead = S[n] if not info["deriv"] else _st_pder(S)[n - 1]
                    extra[info["lead"]] = lead
                    # the factorization hypothesis itself, at three probe points
                    base = _st_pder(S) if info["deriv"] else S
                    for x in (mp.mpf("0.37"), mp.mpf("-1.9"), mp.mpf("2.4")):
                        lhsv = _st_pval(base, x)
                        rhsv = lead
                        for r in vals:
                            rhsv *= (x - r)
                        if abs(lhsv - rhsv) > mp.mpf("1e-16") * (1 + abs(lhsv)):
                            bad = True
                    if abs(lead) < mp.mpf("1e-14"):
                        bad = True
                if bad:
                    continue
                for tname, vn in st["vzero"].items():
                    vroots = _st_roots(V) if len(V) > 1 and abs(V[-1]) > mp.mpf("1e-20") else []
                    if not vroots:
                        bad = True
                        break
                    extra[tname] = vroots[0]
                if bad:
                    continue
                for qname, info in st["resid"].items():
                    qv = []
                    for j in range(N):
                        den = mp.mpf(1)
                        for k2 in range(N):
                            if k2 != j:
                                den *= (avals[j] - avals[k2])
                        qv.append(_st_pval(V, avals[j]) / den)
                    extra[qname] = _st_finvec(qv)
                env = _st_base_env(d, extra)
                # `_hq` re-verified: the partial-fraction identity of 31.14.1 the
                # accessory parameters are pinned by, at points off the singularities
                for qname, info in st["resid"].items():
                    lhsn = _st_expr(parse(f"∑ jj, {qname} jj / (xx - {info['a']} jj)"))
                    rhsn = _st_expr(parse(f"{info['V']}.eval xx / ∏ jj, (xx - {info['a']} jj)"))
                    for x in (mp.mpf("0.37"), mp.mpf("-3.1"), mp.mpf("4.4")):
                        if any(abs(x - av) < mp.mpf("0.05") for av in avals):
                            continue
                        e2 = {**env, "xx": x}
                        h, _ = _st_holds(evaluate(lhsn, e2) - evaluate(rhsn, e2),
                                         [evaluate(lhsn, e2), evaluate(rhsn, e2)],
                                         _SOLIFF_TRUE_EPS)
                        if h is not True:
                            bad = True
                if bad:
                    continue
                yield (env, {"at": f"N={N}, n={n}, "
                                   f"a={[mp.nstr(x, 5) for x in avals]}, "
                                   f"γ={[mp.nstr(x, 5) for x in gvals]}, "
                                   f"zeros={[mp.nstr(x, 6) for x in zr]}"})


def _st_multiindex(avals, S):
    """The multi-index of DLMF 31.15.8: mⱼ = #{zeros of S in (aⱼ, aⱼ₊₁)}."""
    z = _st_roots(S)
    out = []
    for j in range(len(avals) - 1):
        out.append(sum(1 for x in z if abs(mp.im(x)) < mp.mpf("1e-18")
                       and mp.re(avals[j]) < mp.re(x) < mp.re(avals[j + 1])))
    return tuple(out)


def _st_ortho(st, d, ast):
    """DLMF 31.15.9: `stieltjesInner γ a (fun z => ∏ⱼ Sm.eval (z j)) (…) = 0` for two
    Stieltjes polynomials with DISTINCT multi-indices (31.15.8).  The cell integral is
    the definition `stieltjesInner`/`stieltjesWeight` (31.15.10–31.15.12); the two
    polynomials come from the same §31.15(i) construction and are labelled by their
    interval root counts, which is exactly the hypothesis `_hSmz`/`_hSlz`."""
    head, args = ast[1][1], ast[1][2]
    if head != ("var", "stieltjesInner") or len(args) != 4:
        return None
    if ast[2] != ("num", 0):
        return None                    # only the VANISHING claim of 31.15.9 is handled here
    gnode, anode, f1, f2 = args
    if not (gnode == ("var", st["gam"]) and anode == ("var", st["a"])):
        return None
    if f1[0] != "lam" or f2[0] != "lam":
        return None
    polyvars = list(st["polys"])
    if len(polyvars) != 2 or set(st["multiidx"]) != set(polyvars):
        return None
    t0 = time.time()
    results = []
    for avals, gvals in _ST_REAL_PARAMS:
        if results and time.time() - t0 > 120:
            break            # cell-quadrature budget: decide on what is already integrated
        N = len(avals)
        cat = {}
        for n in (1, 2, 3) if N == 2 else (1, 2):
            try:
                prs = _st_pairs(avals, gvals, n, True)
            except Exception:
                continue
            for V, S in prs:
                if _st_residual(avals, gvals, V, S) > mp.mpf("1e-18"):
                    continue
                mi = _st_multiindex(avals, S)
                if sum(mi) == n:
                    cat[mi] = S
        keys = sorted(cat)
        if len(keys) < 2:
            continue
        norms = {}
        for k in keys:
            fk = _st_prod_direct(cat[k])
            norms[k] = _st_cell_inner(gvals, avals, fk, fk)
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                if results and time.time() - t0 > 120:
                    break
                km, kl = keys[i], keys[j]
                # the polynomial VARIABLES keep their own witnesses in BOTH lambdas, so a
                # conclusion naming the same polynomial twice is scored as the norm it is
                pmap = {polyvars[0]: cat[km], polyvars[1]: cat[kl]}
                fm = _st_prodfn(f1, pmap, d, st, gvals, avals)
                fl = _st_prodfn(f2, pmap, d, st, gvals, avals)
                val = _st_cell_inner(gvals, avals, fm, fl)
                sc = mp.sqrt(abs(norms[km] * norms[kl]))
                if sc == 0:
                    continue
                rel = abs(val) / sc
                results.append((rel, f"N={N}, m={km}, l={kl}, "
                                     f"(Sm,Sl)={mp.nstr(val, 6)}, "
                                     f"‖Sm‖‖Sl‖={mp.nstr(sc, 6)}, rel={mp.nstr(rel, 6)}"))
    if not results:
        return (UNABLE, "stieltjes", "no multi-index pair constructed")
    worst = max(results)
    if worst[0] > _SOLIFF_FALSE_EPS:
        return ("FAIL", "stieltjes", f"31.15.9 orthogonality fails: {worst[1]}")
    if worst[0] > TOL_QUAD:
        return (UNABLE, "stieltjes", f"quadrature undecided: {worst[1]}")
    return ("PASS", "stieltjes",
            f"{len(results)} multi-index pairs orthogonal, worst {worst[1]}")


def _st_prodfn(lam, pmap, d, st, gvals, avals):
    """The lambda `fun z => ∏ j, S.eval (z j)` of 31.15.8, with EACH polynomial variable
    instantiated by its own witness (`pmap`) — evaluated through the ordinary AST
    evaluator, so the product the display writes is the one that is integrated."""
    var, body = lam[1], lam[2]
    base = _st_base_env(d, {st["gam"]: _st_finvec(gvals), st["a"]: _st_finvec(avals)})
    for pv, poly in pmap.items():
        base[f"{pv}.eval"] = lambda x, _p=poly: _st_pval(_p, x)

    def f(pt):
        return evaluate(body, {**base, var: _st_finvec(pt)})
    return f


def _st_prod_direct(poly):
    """z ↦ ∏_j poly(z_j) — used ONLY for the homogeneity scale ‖·‖ of 31.15.9."""
    def f(pt):
        r = mp.mpf(1)
        for x in pt:
            r *= _st_pval(poly, x)
        return r
    return f


def handle_stieltjes(d):
    """Score a §31.15(ii)/(iii) display at hypothesis-pinned Stieltjes witnesses.
    Returns None when the row is not of this shape or the witness does not cover every
    free variable of the conclusion — the caller then keeps its prior honest skip."""
    st = (d.get("constraints") or {}).get("_stieltjes")
    if not st:
        return None
    c = d["concl"]
    parts = _st_disjuncts(c)
    parsed = []
    for p in parts:
        p = _strip_outer_parens(p)
        me = re.match(r'^∃\s+(' + _ST_ID + r'),\s*(.+)$', p)
        if me:
            parsed.append(("exists", me.group(1), me.group(2)))
            continue
        try:
            parsed.append(("prop", None, _st_expr(parse(p))))
        except Exception:
            return None
    # gate: numerically differentiated / quadrature shapes get their own TRUE gate
    gate = _SOLIFF_TRUE_EPS
    for kind, _v, node in parsed:
        if kind == "prop" and _has_deriv(node):
            gate = TOL_DERIV
    if st["equil"] and st["energy"]:
        gen = _st_energy_env(st, d)
    elif st["polys"]:
        # the 31.15.9 orthogonality shape is an integral over the cell, not a sample
        if len(parsed) == 1 and parsed[0][0] == "prop":
            node = parsed[0][2]
            if (node[0] == "eq" and node[1][0] == "app"
                    and node[1][1] == ("var", "stieltjesInner")):
                try:
                    return _st_ortho(st, d, node)
                except Unparseable as e:
                    return (UNABLE, "stieltjes", f"{e}")
                except Exception:
                    return None
        gen = _st_poly_env(st, d)
    else:
        return None
    idxvars = [(v, (d.get("constraints") or {}).get("_finidxdim", {}).get(v))
               for v, t in d["binders"].items() if t == "finidx"]
    decided, dropped, worst = 0, 0, None
    t0 = time.time()
    for env, meta in gen:
        if time.time() - t0 > 150:
            break
        # every free variable of every disjunct must be covered — else no verdict
        free = set()
        for kind, v, node in parsed:
            if kind == "prop":
                collect_free(node, free)
            else:
                try:
                    collect_free(parse(node), free)
                except Exception:
                    return None
                free.discard(v)
        for kind, v, node in parsed:
            if kind == "exists":
                free.discard(v)
        miss = [v for v in sorted(free)
                if v not in env and v not in {iv for iv, _dim in idxvars}
                and _reg_resolve(v) is None and v not in ("π",)]
        if miss:
            return None
        # index binders of the conclusion (`k : Fin n`, `j : Fin N`)
        combos = [{}]
        for iv, dim in idxvars:
            rng = env.get(dim)
            if iv in meta:
                combos = [{**cmb, iv: mp.mpf(meta[iv])} for cmb in combos]
            elif rng is not None:
                combos = [{**cmb, iv: mp.mpf(i)} for cmb in combos for i in range(int(rng))]
            else:
                return None
        for cmb in combos:
            e2 = {**env, **cmb}
            try:
                with _time_limit(EVAL_BUDGET):
                    vals = []
                    for kind, v, node in parsed:
                        if kind == "exists":
                            vals.append(_st_exists_holds(v, node, e2, gate))
                        else:
                            if "scale" in meta:
                                tv = (_st_terms(node[1], e2, []) + _st_terms(node[2], e2, [])
                                      + [meta["scale"]])
                                res = evaluate(node[1], e2) - evaluate(node[2], e2)
                                vals.append(_st_holds(res, tv, gate))
                            else:
                                vals.append(_st_prop_holds(node, e2, gate))
            except _EvalTimeout:
                dropped += 1
                continue
            except Unparseable:
                return None
            except (ZeroDivisionError, ValueError, OverflowError, TypeError,
                    ArithmeticError, IndexError, KeyError):
                dropped += 1
                continue
            if any(h is True for h, _r in vals):
                decided += 1
                continue
            if all(h is False for h, _r in vals):
                pt = ", ".join(f"{k}={mp.nstr(v, 6)}" for k, v in cmb.items())
                return ("FAIL", "stieltjes",
                        f"no disjunct holds at {meta.get('at', '')}{(', ' + pt) if pt else ''}: "
                        + "; ".join(f"rel={mp.nstr(r, 6)}" for _h, r in vals))
            dropped += 1
            worst = max([r for _h, r in vals if r is not None] + ([worst] if worst else []))
    if decided < 3:
        return (UNABLE, "stieltjes",
                f"undersampled ({decided} decided, {dropped} dropped"
                + (f", worst rel={mp.nstr(worst, 6)}" if worst else "") + ")")
    return ("PASS", "stieltjes",
            f"{decided} hypothesis-pinned Stieltjes witnesses ({dropped} dropped)")
