#!/usr/bin/env python3
"""oracle_bindings.py — the convention registry (docs/FIDELITY.md §5).

The auto-extractor must never bind "Lean symbol f" to "mpmath f" by *name* — conventions
proliferate (physicists' vs probabilists' Hermite, modulus-vs-parameter elliptic K, …).
Each entry here pins one Lean head symbol to a concrete mpmath callable, *anchored* by a
value/recurrence the two conventions disagree on, and self-tested at import (`verify()`).

A binding is a dict-like row:  lean head  ->  (callable, kind, anchor-check).
  kind 'const'  : a 0-ary constant (mp value)
  kind 'fn'     : an n-ary numeric function  args -> mp value
  kind 'poly'   : a family P_k evaluated at the indeterminate x:  (k, x) -> mp value
                  (Chebyshev/Hermite/… — the extractor passes the sampled x for the
                  polynomial indeterminate, and the `.eval a` form rebinds x := a.)
  kind 'envfn'  : an env-dependent ∀-witness ATOM  sample-env dict -> mp value
                  (a bundle-projection head with no explicit args whose witness value
                  reads sampled binders, e.g. `O.P.roots.toFinset.card` at the
                  canonical Laguerre witness — see _op_bundle_roots_card.)

Run standalone to self-test every anchor:  agent/.venv/bin/python3 agent/oracle_bindings.py
"""
import mpmath as mp

mp.mp.dps = 30

# sympy is an OPTIONAL dependency, used only as the independent implementation of the
# angular-momentum (Wigner/Racah/Clebsch–Gordan) symbols — mpmath has no builtin. If it
# is absent the oracle still imports; those heads simply stay unbound (honest skip).
try:
    from sympy.physics.wigner import wigner_3j as _sy_3j, wigner_6j as _sy_6j, \
        wigner_9j as _sy_9j, clebsch_gordan as _sy_cg, racah as _sy_racah
    import sympy as _sympy
    _HAVE_SYMPY = True
except Exception:
    _HAVE_SYMPY = False


def _sym(expr):
    """Evaluate a sympy exact expression to an mpf at the ambient precision (the symbols
    carry √ factors, so double-precision float() would undershoot the equality gate)."""
    return mp.mpf(str(_sympy.N(expr, mp.mp.dps + 5)))


# ── convention-pinned special-function bindings ──────────────────────────────
def _elliptic_junk(phi, k, kind):
    """FLMF `ellipticF φ k = ∫₀^φ dt/√(1−k²sin²t)` and `ellipticE` (Basic.lean /
    JacobiAmplitude.lean) are TOTALIZED real integrals: Mathlib's `Real.sqrt` junks a
    negative radicand to 0 (and `1/0 = 0`), so where `1 − k²sin²t ≤ 0` the F-integrand
    is 0 and the E-integrand is 0.  On the principal domain `k² < 1` this coincides
    with mpmath's ellipf/ellipe(φ, m=k²); OUTSIDE it mpmath continues ANALYTICALLY
    (complex values) while the Lean value stays the real junk-integral — binding the
    mpmath continuation there false-FAILed the unconditional totalized identity
    ellipticPi_characteristic_zero (worst=0.9004 at k=2.4).  Bind the junk-faithful
    value instead: piecewise quadrature with breakpoints at the radicand's zeros
    t* = arcsin(1/|k|) (+ reflections), odd in φ."""
    m = k * k
    if m < 1:
        return mp.ellipf(phi, m) if kind == "F" else mp.ellipe(phi, m)
    if phi < 0:                                     # both integrands are even in t →
        return -_elliptic_junk(-phi, k, kind)       # the 0-based integral is odd in φ
    def rad(t):
        return 1 - m * mp.sin(t) ** 2
    def f(t):
        d = rad(t)
        if d <= 0:
            return mp.mpf(0)
        return 1 / mp.sqrt(d) if kind == "F" else mp.sqrt(d)
    ts = mp.asin(1 / abs(k))                        # first zero of the radicand in (0, π/2]
    nodes = [mp.mpf(0)]
    j = 0
    while True:                                     # zeros: jπ + ts and (j+1)π − ts
        a, b = j * mp.pi + ts, (j + 1) * mp.pi - ts
        if a >= phi and j * mp.pi >= phi:
            break
        if a < phi:
            nodes.append(a)
        if b < phi:
            nodes.append(b)
        j += 1
    nodes = sorted(set(nodes)) + [phi]
    with mp.workdps(2 * mp.mp.dps):
        return mp.quad(f, nodes)


def _bernoulli_mathlib(n):
    """Mathlib `bernoulli` (the B⁻ convention): B₁ = −1/2; agrees with mpmath except
    n=1, where mpmath also uses −1/2 → identical.  (FLMF `bernoulli'` is the B⁺
    convention: B'₁ = +1/2, handled by the separate '_prime' binding.)"""
    return mp.bernoulli(n)


def _bernoulli_prime_mathlib(n):
    """Mathlib `bernoulli'` (B⁺): differs from `bernoulli` only at n=1 (+1/2)."""
    return mp.mpf(1) / 2 if n == 1 else mp.bernoulli(n)


def _tangent_number(n):
    """FLMF `tangentNumberQ n = n!·tanCoeff n` (EulerNumbers.lean) — the tangent numbers Tₙ
    of the DLMF §24.15(iii) generating function tan t = Σ Tₙ tⁿ/n!: T₀ = 0, T₁ = 1, T₃ = 2,
    T₅ = 16, T₇ = 272 (OEIS A000182 interleaved with zeros at even n). Computed exactly via
    the Bernoulli closed form (DLMF 24.15.4, reindexed to the GF index n = 2m+1):
    T_{2m+1} = (−1)^m·2^{2m+2}(2^{2m+2}−1)·B_{2m+2}/(2m+2), and Tₙ = 0 for even n.
    verify() anchors this against the DEFINING Taylor coefficient n!·[tⁿ] tan t, and pins
    T₂ = 0 to reject the compressed odd-only indexing (Tₙ ↦ coefficient of t^{2n−1}, which
    would give T₂ = 2)."""
    n = _nat(n, "tangentNumberQ")
    if n % 2 == 0:
        return mp.mpf(0)
    m = (n - 1) // 2
    return ((-1) ** m * mp.mpf(2) ** (2 * m + 2) * (mp.mpf(2) ** (2 * m + 2) - 1)
            * mp.bernoulli(2 * m + 2) / (2 * m + 2))


def _gamma_mathlib(z):
    """Γ with a pole-safe value at the non-positive integers, where mpmath's `mp.gamma` raises.

    Mathlib's `Real.Gamma` is `0` at those poles, and every DLMF row that lands on one uses Γ
    only as a DENOMINATOR factor whose reciprocal then vanishes (`1/Γ(pole) = 0`) — e.g. the
    repeated-erfc Maclaurin series DLMF 7.18.6, `∑ … / (… · Γ(1+(n−k)/2))`, which terminates for
    k > n precisely because those terms are 0. Returning `+∞` at the pole reproduces that
    reciprocal-zero EXACTLY in float (`x / ∞ = 0` in mpmath), with NO global division-junk
    convention and NO change to any non-pole point — so the pole terms simply drop out of the
    sum and the partial sums converge to `iⁿerfc`. Off the poles this is byte-identical to
    `mp.gamma`. (If a future row ever placed Γ(pole) in a NUMERATOR the `∞` would disagree with
    Mathlib's `0`, surfacing as an honest mismatch — never a silent wrong PASS.)"""
    try:
        return mp.gamma(z)
    except (ValueError, ZeroDivisionError):
        try:
            if mp.im(z) == 0 and mp.re(z) <= 0 and mp.re(z) == int(mp.re(z)):
                return mp.inf            # 1/Γ(pole) = 0 via x/∞ = 0 — the faithful reciprocal-zero
        except (TypeError, ValueError):
            pass
        raise


def _chebyt(k, x):
    return mp.chebyt(k, x)


def _chebyu(k, x):
    return mp.chebyu(k, x)


def _principal_complex_arcsin(z):
    # DLMF 15.4.4 file-local def `principalComplexArcsin`
    # (Ch15SpecialCases.lean:42): −i·log((1−z²)^{1/2} + i·z), principal branches
    # (`(1−z²)^(1/2:ℂ)` = principal cpow = `mp.sqrt`; `Complex.log` = principal log).
    # This IS the principal arcsin on the open unit disc: −i·log(iz+√(1−z²)) = asin z
    # (self-validated in verify() against mp.asin on the disc, and rejected the
    # non-principal −√ branch which would differ by sign there).
    j = mp.mpc(0, 1)
    return -j * mp.log(mp.sqrt(1 - z ** 2) + j * z)


# ── Christoffel–Darboux witness system (DLMF 18.2.9–18.2.12) ─────────────────
# The abstract FLMF surface `christoffel_darboux` (ChristoffelDarboux.lean) is
# ∀-quantified over a family (p, h, a) constrained only by the hypothesis
# `IsCDSystem p h a x y` — the base/step telescoping identities
#     (x−y)·p₀(x)p₀(y)/h₀ = W₀,   (x−y)·pₖ₊₁(x)pₖ₊₁(y)/hₖ₊₁ = Wₖ₊₁ − Wₖ,
#     Wₖ = aₖ·(pₖ₊₁(x)pₖ(y) − pₖ(x)pₖ₊₁(y)),
# which encode the three-term recurrence + orthogonality with aₖ = kₖ/(hₖ kₖ₊₁)
# (DLMF 18.2.12; kₖ = leading coefficient, hₖ = squared norm). The sweep
# instantiates the triple COHERENTLY at the canonical Chebyshev-T witness
# (DLMF Table 18.3.1): pₖ = Tₖ; h₀ = π, hₖ = π/2 (k ≥ 1) — the squared norms
# ∫₋₁¹ Tₖ(x)²(1−x²)^{−1/2} dx; leading coefficients k₀ = 1, kₙ = 2^{n−1}
# (n ≥ 1), so aₖ = kₖ/(hₖ kₖ₊₁) = 1/π for EVERY k. Anchored in verify()
# BEFORE the sweep trusts the witness: hₖ against the DEFINING orthogonality
# integrals, aₖ against kₖ/(hₖ kₖ₊₁) with the leading coefficients read off
# EXACT forward differences ΔⁿTₙ(0)/n! (decorrelated from the 2^{n−1} closed
# form), every IsCDSystem hypothesis clause numerically, and the 18.2.12
# identity itself at the witness — never by name.
def _cd_cheb_p(k, x):
    """CD witness pₖ(x) = Tₖ(x) — Chebyshev first kind (T₅(cos θ) = cos 5θ)."""
    return mp.chebyt(_nat(k, "cdChebP"), x)


def _cd_cheb_h(k):
    """CD witness hₖ = ∫₋₁¹ Tₖ(x)²(1−x²)^{−1/2} dx: π (k = 0), π/2 (k ≥ 1) —
    DLMF Table 18.3.1."""
    return mp.pi if _nat(k, "cdChebH") == 0 else mp.pi / 2


def _cd_cheb_a(k):
    """CD witness aₖ = kₖ/(hₖ kₖ₊₁) at the Chebyshev-T leading coefficients
    k₀ = 1, kₙ = 2^{n−1}: aₖ = 1/π for every k."""
    _nat(k, "cdChebA")
    return 1 / mp.pi


def _cd_cheb_d(k, x):
    """CONFLUENT CD witness Dₖ(x) = aₖ·(T′ₖ₊₁(x)Tₖ(x) − T′ₖ(x)Tₖ₊₁(x)) — the DLMF
    18.2.13 derivative cross term at the same Chebyshev-T witness (aₖ = 1/π), for the
    ∀-quantified `IsConfluentCDSystem p h D x` surface (the y → x diagonal of 18.2.12,
    where the FLMF statement abstracts the whole term as `D k`). The derivative is the
    EXACT T′ₙ = n·Uₙ₋₁ (DLMF 18.9.21) — no numeric differentiation. Unlike the (p, h, a)
    triple above, D depends on the row's own point x, so the sweep threads x as an extra
    trailing argument (fidelity_extract 'cdChebD@x' witness spec). verify() anchors the
    defining formula against an INDEPENDENT mp.diff derivative and every
    IsConfluentCDSystem hypothesis clause before the sweep trusts it."""
    k = _nat(k, "cdChebD")
    tk, tk1 = mp.chebyt(k, x), mp.chebyt(k + 1, x)
    dtk = k * mp.chebyu(k - 1, x) if k >= 1 else mp.mpf(0)
    dtk1 = (k + 1) * mp.chebyu(k, x)
    return (dtk1 * tk - dtk * tk1) / mp.pi


def _cd_summand(p, h, k, x, y):
    """FLMF `cdSummand p h k x y = p k x * p k y / h k` — the DLMF 18.2.12 LHS
    kernel summand pₖ(x)pₖ(y)/hₖ. Higher-order: p and h arrive as CALLABLES
    (fidelity_extract routes them through _fn_callable, never scalar eval)."""
    k = _nat(k, "cdSummand")
    return p(k, x) * p(k, y) / h(k)


def _cd_cross(p, a, k, x, y):
    """FLMF `cdCross p a k x y = a k * (p (k+1) x * p k y − p k x * p (k+1) y)`
    — the DLMF 18.2.12 cross term aₖ·(pₖ₊₁(x)pₖ(y) − pₖ(x)pₖ₊₁(y)). Higher-
    order: p and a arrive as callables."""
    k = _nat(k, "cdCross")
    return a(k) * (p(k + 1, x) * p(k, y) - p(k, x) * p(k + 1, y))


def _rlog(a):
    """Mathlib `Real.log`: log of the absolute value, with log 0 = 0."""
    return mp.mpf(0) if a == 0 else mp.log(abs(a))


def _log_auto(a):
    """Bare `log` token: `Complex.log` or `Real.log` depending on the file's `open`.
    The pretty-printer erases the namespace, so the two collapse to the same token.
    Disambiguate SOUNDLY by the argument's type: `Real.log : ℝ → ℝ` cannot accept a
    non-real argument, so an argument with a nonzero imaginary part unambiguously came
    from `Complex.log` and must use the PRINCIPAL complex log (Im ∈ (−π,π], = mp.log).
    A real-valued argument (mpf, or mpc with Im = 0) keeps the Mathlib `Real.log = log|·|`
    convention (`_rlog`) exactly as before — negative reals still avoid the fake 2πi
    branch mismatch on `log(xy)=logx+logy`. ADDITIVE: this only corrects genuinely
    complex arguments, which `_rlog` evaluated wrongly (log of the magnitude, phase
    discarded); it cannot fabricate a PASS since mp.log is the honest principal value."""
    if isinstance(a, mp.mpc) and a.imag != 0:
        return mp.log(a)
    return _rlog(a)


def _rsqrt(a):
    """Mathlib `Real.sqrt`: 0 on negatives (junk value), else the real root."""
    return mp.mpf(0) if a < 0 else mp.sqrt(a)


def _clamp(a):
    """Mathlib `Real.arcsin/arccos` clamp the argument to [−1, 1]."""
    return mp.mpf(-1) if a < -1 else mp.mpf(1) if a > 1 else a


# Spherical Bessel functions via the DLMF Rayleigh CLOSED FORM (10.49.3/.5/.8/.12) and the
# upward three-term recurrence (10.51.1/.4/.5). The Bessel-quotient form √(π/2x)·C_{n+½}(x)
# is REAL only for x>0; on the sample grid (which includes x=−0.8) that quotient goes complex
# (√ of a negative + a complex half-order J) and disagrees in SIGN with the FLMF def, whose
# base cases sin x/x, −cos x/x, sinh z/z, e^{−z}/z and recurrences are real entire-in-the-trig
# expressions valid for every x≠0. Encoding the Rayleigh closed form directly (sin/cos/sinh/
# /cosh/exp + the DLMF recurrence) matches the FLMF def on the WHOLE real grid.
def _sphericalj(n, x):
    """jₙ(x) — DLMF 10.47.3 closed form  jₙ(x) = √(π/(2x))·J_{n+½}(x).  Uses mpmath's
    order-robust `besselj` instead of the DLMF 10.51.1 FORWARD recurrence
    j_{k+1}=((2k+1)/x)·jₖ−j_{k−1}, which — evaluated at fixed precision — is numerically
    unstable and BLOWS UP for n≳60 (e.g. j_800(9.05) overflowed to ~1e1419), defeating
    the Fresnel-series convergence tests in erf_7_6_10/11.  For x<0 (the sample grid has
    x=−0.8) the naïve √-of-negative closed form goes complex/wrong-sign, so we evaluate at
    |x| and restore the sign by the parity jₙ(−x)=(−1)ⁿ jₙ(x) — matching the FLMF real
    trig-recurrence def on the WHOLE real grid.  Verified to agree with the old recurrence
    to full precision at small n where the recurrence is still stable (see this session's
    old-vs-new probe)."""
    n = _nat(n, "sphericalJ")
    if x == 0:
        return mp.mpf(1) if n == 0 else mp.mpf(0)
    xr, sign = x, 1
    neg = False
    try:
        neg = (x < 0)
    except TypeError:      # complex x: no real ordering — use the principal branch directly
        neg = False
    if neg:
        xr = -x
        if n % 2 == 1:
            sign = -1
    return sign * mp.sqrt(mp.pi / (2 * xr)) * mp.besselj(n + mp.mpf(1) / 2, xr)


def _sphericaly(n, x):
    """yₙ(x) — DLMF 10.49.5/10.51.1: y₀=−cos x/x, y₁=−cos x/x²−sin x/x,
    y_{k+1}=((2k+1)/x)·yₖ−y_{k−1}."""
    n = _nat(n, "sphericalY")
    a = -mp.cos(x) / x
    b = -mp.cos(x) / x ** 2 - mp.sin(x) / x
    if n == 0:
        return a
    for k in range(1, n):
        a, b = b, (2 * k + 1) / x * b - a
    return b


def _mod_spherical_i(n, z):
    """iₙ⁽¹⁾(z) — DLMF 10.47.7 closed form  iₙ⁽¹⁾(z) = √(π/(2z))·I_{n+½}(z).  Uses mpmath's
    order-robust `besseli` instead of the DLMF 10.51.4 FORWARD recurrence
    i_{k+1}=i_{k−1}−((2k+1)/z)·iₖ, which — evaluated at fixed precision — is numerically
    unstable for this MINIMAL (recessive) solution and BLOWS UP for n≳30 (e.g. i_800(0.09)
    overflowed to ~1e3021 instead of decaying to 0), defeating the convergence tests in
    erf_7_6_8/9.  For z<0 we evaluate at |z| and restore the sign by parity
    iₙ⁽¹⁾(−z)=(−1)ⁿ iₙ⁽¹⁾(z), matching the FLMF real recurrence def on the whole real grid.
    Verified to agree with the old recurrence to full precision at small n (old-vs-new
    probe, this session)."""
    n = _nat(n, "modSphericalI")
    if z == 0:
        return mp.mpf(1) if n == 0 else mp.mpf(0)
    zr, sign = z, 1
    neg = False
    try:
        neg = (z < 0)
    except TypeError:
        neg = False
    if neg:
        zr = -z
        if n % 2 == 1:
            sign = -1
    return sign * mp.sqrt(mp.pi / (2 * zr)) * mp.besseli(n + mp.mpf(1) / 2, zr)


def _mod_spherical_k(n, z):
    """kₙ(z) — DLMF 10.49.12/10.51.5 in the FLMF (no-π/2) normalization: k₀=e^{−z}/z,
    k₁=e^{−z}/z+e^{−z}/z², k_{k+1}=k_{k−1}+((2k+1)/z)·kₖ."""
    n = _nat(n, "modSphericalK")
    a = mp.exp(-z) / z
    b = mp.exp(-z) / z + mp.exp(-z) / z ** 2
    if n == 0:
        return a
    for k in range(1, n):
        a, b = b, a + (2 * k + 1) / z * b
    return b


def _jacobi(which):
    """FLMF `jacobiSn/Cn/Dn u k` — second arg is the MODULUS k (per the Lean naming
    `*_zero_modulus`), so bind to mpmath's PARAMETER form m = k²  (FIDELITY.md §5: the
    Jacobi/elliptic m-vs-k knob). sn(u,0)=sin u, sn²+cn²=1, dn²+k²sn²=1 anchor it."""
    return lambda u, k: mp.ellipfun(which, u, k ** 2)


def _voigt_w(z):
    """Faddeeva w(z) = e^{−z²}·erfc(−iz)  (the scaled complex error function)."""
    return mp.exp(-z ** 2) * mp.erfc(-mp.mpc(0, 1) * z)


def _voigt_uv(x, t):
    """FLMF Voigt U(x,t)+iV(x,t) (DLMF 7.19.1 integral; closed form 7.19.2/.3):
       U(x,t) = (1/√(4πt)) ∫_ℝ e^{−(x−y)²/(4t)}/(1+y²) dy,  V with an extra y in the numerator.
    Both equal (√π/(2√t))·w(z) split into Re/Im with z = (i+x)/(2√t) — verified against the
    defining integral. Requires t>0 (else the Gaussian kernel is non-normalizable). Returns the
    complex U+iV; the U/V bindings take real/imag parts."""
    if t <= 0:
        raise ValueError("voigt: t ≤ 0 (kernel non-normalizable)")
    z = (mp.mpc(0, 1) + x) / (2 * mp.sqrt(t))
    return mp.sqrt(mp.pi) / (2 * mp.sqrt(t)) * _voigt_w(z)


def _voigt_u(x, t):
    """DLMF 7.19.1 Voigt U(x,t) = Re[U+iV]."""
    return _voigt_uv(x, t).real


def _voigt_v(x, t):
    """DLMF 7.19.1 Voigt V(x,t) = Im[U+iV]."""
    return _voigt_uv(x, t).imag


def _phys_hermite(k, x):
    """GENUINE physicists' Hermite Hₙ(x) (DLMF 18.3 / 7.10): H₀=1, H₁=2x,
    Hₙ₊₁=2x·Hₙ−2n·Hₙ₋₁; mpmath's `hermite` (anchored H₂(x)=4x²−2).

    Bind this ONLY to `FLMF.Functions.Hermite.physicistsHermite` (the recurrence-
    defined true Hₙ).  It must NEVER be bound to the misnamed legacy
    `FLMF.Functions.Hermite.physHermite`, whose Lean body is
    `(hermite n).comp (C 2 * X)` = Heₙ(2x) ≠ Hₙ(x) for n ≥ 2 — binding by that
    name was exactly the false-PASS trap of ERRATA `physhermite-not-physicist`
    (Tier-1 validated DLMF's identity instead of the Lean statement)."""
    return mp.hermite(int(k), x)


def _hermite_prob(k, x):
    """FLMF Hermite = PROBABILISTS' Heₙ (Mathlib `Polynomial.hermite`):
    He₀=1, He₁=x, He₍ₙ₊₁₎ = x·Heₙ − n·He₍ₙ₋₁₎.  mpmath `hermite` is the PHYSICISTS'
    Hₙ, so bind through the exact map Heₙ(x) = 2^(−n/2)·Hₙ(x/√2) (FIDELITY.md §5.1)."""
    return mp.mpf(2) ** (-mp.mpf(k) / 2) * mp.hermite(k, x / mp.sqrt(2))


# ── exact-integer arithmetic helpers (M7 / Tier B1) ──────────────────────────
# Nat/arithmetic heads are EXACT-integer objects: compute them in Python ints
# (no rounding anywhere) and let the caller mix the result into mp arithmetic.
# Junk-value conventions follow Mathlib: divisors 0 = ∅, totient 0 = 0, …
def _nat(x, what):
    """Coerce a sampled value to an exact nonneg int; RAISE (→ honest point drop)
    if it isn't one — ℕ-truncated subtraction gone negative must never fabricate."""
    n = int(x)
    if n != x or n < 0:
        raise ValueError(f"{what}: {x} is not a natural number")
    return n


def _divisors(n):
    """Mathlib `Nat.divisors`: positive divisors of n, with divisors 0 = ∅."""
    n = _nat(n, "divisors")
    return [d for d in range(1, n + 1) if n % d == 0]


def _prime_factors(n):
    """Mathlib `Nat.primeFactors`: the distinct prime divisors (∅ for n ≤ 1)."""
    n, ps, p = _nat(n, "primeFactors"), [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ps.append(n)
    return ps


def _factorization(n):
    """Mathlib `Nat.factorization`: the finitely-supported exponent map of n, returned as
    the list of (p, k) pairs with p prime and p^k ∥ n (DLMF 27.2.1, n = ∏ p^{a_p}).
    Empty for n ≤ 1 (Mathlib: `Nat.factorization 0 = 0`, `Nat.factorization 1 = 0`), so a
    `Finsupp.prod` over it is the empty product 1 there. Exact trial division — anchored
    in verify() by reconstructing n = ∏ p^k."""
    n = _nat(n, "factorization")
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            k = 0
            while n % p == 0:
                n //= p
                k += 1
            out.append((p, k))
        p += 1
    if n > 1:
        out.append((n, 1))
    return out


def _totient(n):
    """Euler φ — exact, via the distinct prime factors; φ(0) = 0 (Mathlib)."""
    n = _nat(n, "totient")
    out = n
    for p in _prime_factors(n):
        out = out // p * (p - 1)
    return out


def _mobius(n):
    """Möbius μ — exact; μ(0) = 0 (ArithmeticFunction junk value)."""
    n = _nat(n, "mobius")
    if n == 0:
        return 0
    ps = _prime_factors(n)
    sq_free = all(n % (p * p) != 0 for p in ps)
    return 0 if not sq_free else (-1) ** len(ps)


def _jordan_totient(k, n):
    """Jordan Jₖ(n) = Σ_{d·e=n} μ(d)·eᵏ — exact, matching the Lean
    `jordanTotient k n = ∑ x ∈ n.divisorsAntidiagonal, μ x.1 · x.2 ^ k` (J₁ = φ)."""
    k, n = _nat(k, "jordanTotient k"), _nat(n, "jordanTotient n")
    return sum(_mobius(n // d) * d ** k for d in _divisors(n))


def _divisor_sigma(k, n):
    """σₖ(n) = Σ_{d∣n} dᵏ — exact (Mathlib `ArithmeticFunction.sigma`; σₖ(0) = 0)."""
    k, n = _nat(k, "divisorSigma k"), _nat(n, "divisorSigma n")
    return sum(d ** k for d in _divisors(n))


def _ramanujan_sum(q, n):
    """Ramanujan's sum c_q(n) = Σ_{d ∣ gcd(q,n)} d·μ(q/d) — the DLMF 27.10.1 Hölder/
    divisor form, exactly the FLMF def `ramanujanSum q n = ∑ d ∈ (Nat.gcd q n).divisors,
    d·μ(q/d)` (RamanujanSum.lean). Exact integer arithmetic throughout. Junk-value
    coherence: q = 0 gives μ(0/d) = μ(0) = 0 on every divisor d of gcd(0,n) = n, hence
    c_0(n) = 0 — the same value the Lean def produces. Anchored in verify() against the
    DECORRELATED exponential-sum form DLMF 27.10.2, c_k(n) = Σ_{h:(h,k)=1, 1≤h≤k}
    e^{2πihn/k} (unit-circle exponentials vs integer divisor sums — a genuinely
    independent evaluation), on a grid including gcd(k,n) > 1 samples, plus the special
    values c_1(n) = 1, c_q(1) = μ(q), and the prime dichotomy c_p(n) = p−1 (p ∣ n) /
    −1 (p ∤ n) — never by name."""
    from math import gcd
    q, n = _nat(q, "ramanujanSum q"), _nat(n, "ramanujanSum n")
    return sum(d * _mobius(q // d) for d in _divisors(gcd(q, n)))


def _choose(n, k):
    """Binomial C(n,k) — exact (Mathlib `Nat.choose`: 0 when k > n)."""
    import math
    n, k = _nat(n, "choose n"), _nat(k, "choose k")
    return math.comb(n, k)


def _catalan(n):
    """Catalan Cₙ = C(2n,n)/(n+1) — exact (Mathlib `catalan`)."""
    n = _nat(n, "catalan")
    return _choose(2 * n, n) // (n + 1)


def _harmonic(n):
    """Mathlib `harmonic n = Σ_{i=1..n} 1/i` (H₀ = 0)."""
    return mp.fsum(mp.mpf(1) / i for i in range(1, _nat(n, "harmonic") + 1))


_CCOEFF = {0: mp.mpf(1)}
def _ccoeff(k):
    """FLMF `cCoeff` (DLMF 6.10.3): c₀=1, cₖ = −Σ_{j<k} cⱼ/(k−j)."""
    k = _nat(k, "cCoeff")
    if k not in _CCOEFF:
        _CCOEFF[k] = -mp.fsum(_ccoeff(j) / (mp.mpf(k) - j) for j in range(k))
    return _CCOEFF[k]


def _dfo(m):  # (2m+1)!! = 1·3·5···(2m+1)
    r = mp.mpf(1)
    for i in range(1, 2 * m + 2, 2):
        r *= i
    return r

def _sph_j(n, z):   # FLMF sphBesselJ (DLMF 10.53.1): zⁿ Σ (−z²/2)ᵏ/(k!(2n+2k+1)!!) — real ∀z
    n = _nat(n, "sphBesselJ")
    return z ** n * mp.nsum(lambda k: (-z ** 2 / 2) ** k / (mp.factorial(k) * _dfo(n + int(k))), [0, mp.inf])

def _mod_sph_i(n, z):  # FLMF modSphBesselI (DLMF 10.53.3): zⁿ Σ (z²/2)ᵏ/(k!(2n+2k+1)!!) — real ∀z
    n = _nat(n, "modSphBesselI")
    return z ** n * mp.nsum(lambda k: (z ** 2 / 2) ** k / (mp.factorial(k) * _dfo(n + int(k))), [0, mp.inf])


def _bell(n):
    """Bell number Bₙ — exact (Mathlib `bell`), via the Bell triangle (B₀ = 1)."""
    n = _nat(n, "bell")
    row = [1]
    for _ in range(n):
        nxt = [row[-1]]
        for x in row:
            nxt.append(nxt[-1] + x)
        row = nxt
    return row[0]


def _von_mangoldt(n):
    """von Mangoldt Λ(n) = log p if n = pᵏ (k ≥ 1), else 0 (Λ(0)=Λ(1)=0)."""
    n = _nat(n, "vonMangoldt")
    if n < 2:
        return mp.mpf(0)
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return mp.log(p) if m == 1 else mp.mpf(0)   # pure power of p ⇒ log p, else 0
        p += 1
    return mp.log(n)                                     # n itself prime


def _chebyshev_psi(x):
    """Second Chebyshev function ψ(x) = Σ_{n ≤ x} Λ(n) — the DLMF 27.2.11 DEFINING sum
    (Mathlib `Chebyshev.psi`). Real x; the index set is 1 ≤ n ≤ ⌊x⌋₊ (Nat.floor — the
    sum is empty, i.e. ψ = 0, for x < 2, including all negative x)."""
    N = int(mp.floor(x))
    if N < 2:
        return mp.mpf(0)
    return mp.fsum(_von_mangoldt(n) for n in range(2, N + 1))


def _isprime(n):
    """Nat.Prime n for an exact integer — sympy.isprime (deterministic in this range).
    Used by the extractor's `with p.Prime` Finset-filter evaluation (DLMF 27.2.11 ϑ
    index set). Without sympy it raises → the sample point drops honestly."""
    if not _HAVE_SYMPY:
        raise ValueError("isprime requires sympy")
    return bool(_sympy.isprime(int(n)))


def _chebyshev_theta(x):
    """First Chebyshev function ϑ(x) = Σ_{p ≤ x, p prime} log p — DLMF 27.2.11 (Mathlib
    `Chebyshev.theta`, FLMF.Chebyshev.theta). Real x; index set is the primes p ≤ ⌊x⌋₊
    (Nat.floor — empty sum, ϑ = 0, for x < 2 including all negative x). Computed via
    sympy.primerange, INDEPENDENT of the extractor's isprime-filtered Finset-sum path.
    Anchored in verify(): ϑ(10) = log 210 (= log(2·3·5·7)), ϑ(2) = log 2, ϑ(1.9) = 0,
    floor step, Nat.floor clamp at negative x."""
    if not _HAVE_SYMPY:
        raise ValueError("chebyshev theta requires sympy")
    N = int(mp.floor(x)) if x > 0 else 0
    return mp.fsum(mp.log(p) for p in _sympy.primerange(2, N + 1))


def _lseries_term(f, s, n):
    """Mathlib `LSeries.term f s n` — the n-th Dirichlet-series term of the DLMF 25.11 /
    §27.4 defining form Σ_{n≥1} f(n)·n^{−s}:

        LSeries.term f s n = 0 if n = 0, else f(n) / n^s.

    `f` arrives as a one-argument callable (the extractor's `_fn_callable` of the Lean
    lambda argument, e.g. `fun n => (μ n : ℂ)`), never a scalar. The n = 0 branch mirrors
    Mathlib's `if n = 0 then 0 else f n / n ^ s` junk value exactly (the DLMF sums start
    at n = 1, so the Lean `∑'` over ℕ picks up only that extra zero term). For n ≥ 1 the
    base is a positive real, so n^s = exp(s·ln n) is the branch-unambiguous principal
    power. Anchored in verify() to the DLMF 25.2.1 defining series ζ(s) = Σ n^{−s}
    (real and complex s, THROUGH this binding), to the DLMF 27.4.5 Möbius series
    Σ μ(n) n^{−s} = 1/ζ(s), to an independent exp/log evaluation of a single term at
    complex s (pins the (f, s, n) argument order — a swap changes the value), and to
    the n = 0 junk value."""
    n = _nat(n, "LSeries.term")
    if n == 0:
        return mp.mpf(0)
    return f(n) / mp.power(n, s)


def _lseries(f, s):
    """Mathlib `LSeries f s = ∑'_{n:ℕ} LSeries.term f s n` — the scoped `L ↗f s` head of
    `LSeries.notation` — i.e. the DLMF 25.11 / §27.4 Dirichlet series Σ_{n≥1} f(n)·n^{−s},
    summed THROUGH the already-anchored `_lseries_term` (whose n = 0 Lean term is the junk 0,
    so the ℕ-sum starts honestly at n = 1).

    Plain partial sums with a settled-tail window and NO extrapolation: an arithmetic
    coefficient like μ(n) or Λ(n) is erratic in n, so convergence acceleration is unsound
    there; instead every partial sum over the trailing 48-term window must sit within
    1e-25·max(1,|total|) of the running total before the value is trusted (the same gate as
    fidelity_extract's _bounded_nsum). A tail that has not settled within the 4000-term cap
    RAISES → the sweep drops that sample point honestly (a blind truncation would carry the
    N^{1−Re s} tail of a half-summed Dirichlet series into the exact equality gate); in
    practice the large-σ half of the sweep's `Re s > 1` complex grid (σ = 8.5, 11.5)
    settles, mirroring the already-passing tsum-spelled twins. Anchored in verify() to the
    DLMF 25.2.1 defining series ζ(12) and ζ(12+3i) (real and complex s, THROUGH the
    binding), to the DLMF 27.4.5 Möbius series L μ s = 1/ζ(s) at s = 12 (the N = 400,
    s = 6 partial-sum anchor of `_lseries_term` restated through the full L head at a σ
    the settle window admits), and to the guard itself (s = 2 must raise, never return a
    half-converged partial sum)."""
    total, hist = mp.mpf(0), []
    for n in range(1, 4001):
        total += _lseries_term(f, s, n)
        hist.append(total)
        if len(hist) > 48:
            hist.pop(0)
        scale = mp.mpf("1e-25") * max(mp.mpf(1), abs(total))
        if n > 49 and all(abs(total - h) < scale for h in hist):
            return total
    raise ValueError("LSeries tail not settled within 4000 terms (truncation ~ N^{1-Re s})")


def _asy_coeff(a, n):
    """DLMF 8.11.2 coefficient Pₙ(a) = (a−1)(a−2)···(a−n), P₀ = 1 (falling factorial)."""
    n = _nat(n, "asyCoeff")
    r = mp.mpf(1)
    for j in range(n):
        r *= (a - 1 - j)
    return r


def _falling(x, k):
    """Falling factorial x^{(k)↓} = x(x−1)···(x−k+1) — `(descPochhammer ℝ k).eval x`, k ≥ 0."""
    k = _nat(k, "descPochhammer")
    r = mp.mpf(1)
    for j in range(k):
        r *= (x - j)
    return r


def _qbinom(q, n, k):
    """Gaussian binomial [n,k]_q = ∏_{i=1}^{k} (1−q^{n−k+i})/(1−q^i) (→ C(n,k) as q→1);
    decorrelated from the q-Pascal recurrence def. 0 for k>n."""
    import math
    n, k = _nat(n, "qbinom n"), _nat(k, "qbinom k")
    if k > n:
        return mp.mpf(0)
    if abs(q - 1) < mp.mpf("1e-12"):
        return mp.mpf(math.comb(n, k))
    num = den = mp.mpf(1)
    for i in range(1, k + 1):
        num *= (1 - q ** (n - k + i))
        den *= (1 - q ** i)
    return num / den


def _asc_factor(a, q, k, x):
    """FLMF `ascFactor a q k x = ∏_{m<k} (1 − 2a qᵐ x + a² q^{2m})` — the real form of
    the conjugate q-Pochhammer pair `(a e^{iθ}; q)_k (a e^{−iθ}; q)_k` at `x = cos θ`
    (the ₃φ₂ numerator of DLMF §18.28(ii) / KLS 14.8.1). Anchored in verify() against
    that DEFINING conjugate pair evaluated through mp.qp at COMPLEX argument (a
    decorrelated evaluation path) and the k = 1 closed form 1 − 2ax + a²."""
    k = _nat(k, "ascFactor")
    r = mp.mpf(1)
    for m in range(k):
        r *= 1 - 2 * a * q ** m * x + a ** 2 * q ** (2 * m)
    return r


def _al_salam_chihara(a, b, q, n, x):
    """Al-Salam–Chihara Qₙ(x; a, b | q) (DLMF §18.28 / KLS 14.8.1) — the terminating
    ₃φ₂ form with the conjugate e^{±iθ} pair folded into the real q-quadratic
    `ascFactor`:

        Qₙ = ((ab;q)ₙ / aⁿ) · Σ_{k=0}^{n} (q^{−n};q)_k · ascFactor(a,q,k,x)
               / ((ab;q)_k (q;q)_k) · qᵏ.

    Degenerate parameters (a = 0 with n ≥ 1, q ∈ {0, 1}, (ab;q)_k = 0) raise through
    mpmath's division/power errors → an honest point drop, never a fabricated value
    (the Lean theorems carry the matching a ≠ 0, q ≠ 0, q ≠ 1, ab ≠ 1 hypotheses).
    Anchored in verify() against the DEFINING three-term recurrence DLMF §18.28 /
    KLS 14.8.4, 2x·Qₙ = Q_{n+1} + (a+b)qⁿ·Qₙ + (1−qⁿ)(1−ab·q^{n−1})·Q_{n−1} with
    Q₀ = 1, built independently UPWARD from that initial data, plus the a↔b symmetry
    of the family (invisible in this asymmetric series form) — never by name."""
    n = _nat(n, "alSalamChihara")
    pref = mp.qp(a * b, q, n) / a ** n
    return pref * mp.fsum(
        mp.qp(q ** (-n), q, k) * _asc_factor(a, q, k, x)
        / (mp.qp(a * b, q, k) * mp.qp(q, q, k)) * q ** k
        for k in range(n + 1))


def _continuous_hahn(a, b, c, d, n, x):
    """Continuous Hahn pₙ(x; a, b, c, d) (DLMF §18.20, Table 18.19.1) — the DEFINING
    terminating ₃F₂ form

        pₙ = iⁿ · ((a+c)ₙ (a+d)ₙ / n!) · ₃F₂(−n, n+a+b+c+d−1, a+ix; a+c, a+d; 1)

    with real a, b, c, d, x and COMPLEX value (series argument a+ix, prefactor iⁿ).
    Argument order matches the FLMF def `continuousHahn a b c d n x`
    (Functions/OrthogonalPolynomials/ContinuousHahn.lean). Degenerate lower
    parameters ((a+c)ₖ or (a+d)ₖ = 0) raise through mpmath → an honest point drop
    (the Lean theorems carry the matching nonvanishing hypotheses). Anchored in
    verify() at the normalization p₀ = 1 and the DLMF degree-one value
    p₁ = (a+b+c+d)x + i(cd−ab) on asymmetric parameter points, plus the a↔b weight
    symmetry of the family (invisible in this asymmetric series form) — never by
    name."""
    n = _nat(n, "continuousHahn")
    return (mp.mpc(0, 1) ** n
            * mp.rf(a + c, n) * mp.rf(a + d, n) / mp.factorial(n)
            * mp.hyper([-n, n + a + b + c + d - 1, a + mp.mpc(0, 1) * x],
                       [a + c, a + d], 1))


def _dual_hahn(g, d, N, n, x):
    """Dual Hahn Rₙ(λ(x); γ, δ, N) (DLMF 18.20.5, Table 18.19.1) — the DEFINING
    terminating ₃F₂ at unit argument on the quadratic lattice λ(x) = x(x+γ+δ+1):

        Rₙ = ₃F₂(−n, −x, x+γ+δ+1; γ+1, −N; 1),   n = 0, 1, …, N,

    computed through mp.hyper (decorrelated from FLMF's explicit Pochhammer-sum
    def, Functions/OrthogonalPolynomials/DualHahn.lean). Argument order matches
    the FLMF def `dualHahn γ δ N n x`. Off-domain samples n > N hit the vanished
    (−N)ₖ denominator and raise through mpmath → an honest point drop, never a
    fabricated value (DLMF states 18.20.5 only for n ≤ N; the Lean def's junk-zero
    terms there are a division-by-zero artifact, not DLMF content). Anchored in
    verify() against the DEFINING three-term recurrence DLMF 18.22 / KLS 1.6.2,
    λ(x)·Rₙ = Aₙ·R_{n+1} − (Aₙ+Cₙ)·Rₙ + Cₙ·R_{n−1} with Aₙ = (n+γ+1)(n−N),
    Cₙ = n(n−δ−N−1), built independently UPWARD from R₀ = 1 (whence
    R₁ = 1 − λ(x)/((γ+1)N) at n = 0, C₀ = 0) on asymmetric γ ≠ δ parameter points
    (pinning the (γ,δ,N,n,x) argument order), plus the lattice-origin value
    Rₙ(λ(0)) = 1 and a hand-computed R₁ — never by name."""
    return mp.hyper([-int(_nat(n, "dualHahn")), -x, x + g + d + 1],
                    [g + 1, -int(_nat(N, "dualHahn"))], 1)


def _dh_A(g, N, n):
    """Dual Hahn recurrence coefficient dhA γ N n = A_{n+1} = (n+1+γ+1)(n+1−N)
    (FLMF DualHahn.lean, the DLMF 18.22 / KLS 1.6.2 coefficient
    Aₙ = (n+γ+1)(n−N) at index n+1; argument order matches the FLMF def
    `dhA γ N n`). Anchored in verify() by re-deriving the SAME shifted
    coefficient inside the independently anchored 18.22 upward recurrence and
    by checking the recurrence role λ(x)·R_{n+1} = A_{n+1}·R_{n+2}
    − (A_{n+1}+C_{n+1})·R_{n+1} + C_{n+1}·Rₙ against the decorrelated ₃F₂
    binding — never by name."""
    return (n + 1 + g + 1) * (n + 1 - N)


def _dh_CC(d, N, n):
    """Dual Hahn recurrence coefficient dhCC δ N n = C_{n+1} = (n+1)(n+1−δ−N−1)
    (FLMF DualHahn.lean, the DLMF 18.22 / KLS 1.6.2 coefficient
    Cₙ = n(n−δ−N−1) at index n+1; argument order matches the FLMF def
    `dhCC δ N n`). Anchored in verify() alongside _dh_A (same shifted-index and
    recurrence-role checks against the decorrelated ₃F₂ binding)."""
    return (n + 1) * (n + 1 - d - N - 1)


def _meixner_pollaczek(lam, phi, n, x):
    """Meixner–Pollaczek Pₙ^{(λ)}(x; φ) (DLMF §18.20, Table 18.19.1 / KLS 9.7.1) —
    the DEFINING terminating ₂F₁ form

        Pₙ = ((2λ)ₙ / n!) · e^{inφ} · ₂F₁(−n, λ+ix; 2λ; 1 − e^{−2iφ}),

    with real λ, φ, x, the series computed through mp.hyper (decorrelated from
    FLMF's explicit Pochhammer-sum def,
    Functions/OrthogonalPolynomials/MeixnerPollaczek.lean). Argument order matches
    the FLMF def `meixnerPollaczek lam phi n x`. The series runs through ℂ
    (argument λ+ix, prefactor e^{inφ}) but the value is real for real inputs.
    Degenerate parameters (the vanished (2λ)ₖ lower parameter at λ = 0, −1/2,
    −1, …) make mp.hyper return NaN, converted here to an explicit
    ZeroDivisionError → an honest point drop, never a fabricated value (the Lean
    theorems carry the matching λ ≠ 0 / (2λ)-Pochhammer ≠ 0 hypotheses).
    Anchored in verify() against the DEFINING three-term recurrence DLMF §18.9 /
    KLS 9.7.3, (n+1)·P_{n+1} = 2[x sinφ + (n+λ)cosφ]·Pₙ − (n+2λ−1)·P_{n−1}, built
    independently UPWARD from P₀ = 1 and the hand degree-one value
    P₁ = 2(λcosφ + x sinφ) on asymmetric parameter points (pinning the (λ,φ,n,x)
    argument order), plus the normalization P₀ = 1 and realness — never by name."""
    n = _nat(n, "meixnerPollaczek")
    val = (mp.rf(2 * lam, n) / mp.factorial(n)
           * mp.exp(mp.mpc(0, 1) * n * phi)
           * mp.hyper([-n, lam + mp.mpc(0, 1) * x], [2 * lam],
                      1 - mp.exp(mp.mpc(0, -2) * phi)))
    if mp.isnan(val):        # vanished (2λ)ₖ lower parameter (λ = 0, −1/2, −1, …)
        raise ZeroDivisionError("meixnerPollaczek: (2λ)ₖ lower parameter vanished")
    return val


def _stirling1u(n, k):
    """Unsigned Stirling number of the 1st kind c(n,k) (cycle count) — exact, via
    c(n+1,k) = n·c(n,k) + c(n,k−1); these are the rising-factorial coefficients
    x^{(n)↑} = Σₖ c(n,k) xᵏ (FLMF `cycle`)."""
    n, k = _nat(n, "cycle n"), _nat(k, "cycle k")
    if k > n:            # c(n,k) = 0 for k > n; also avoids the DP table (sized n+2)
        return mp.mpf(0)  # indexing out of range (previous code raised IndexError for k>n+1)
    C = [[0] * (n + 2) for _ in range(n + 2)]
    C[0][0] = 1
    for i in range(n + 1):
        for j in range(i + 2):
            C[i + 1][j] = i * C[i][j] + (C[i][j - 1] if j > 0 else 0)
    return mp.mpf(C[n][k])


def _dirichlet_chars(k):
    """The Dirichlet characters mod k as φ(k) callables χ(a)→ℂ (0 on non-units), for CYCLIC
    (ℤ/kℤ)* only (odd prime power, twice one, or k∈{1,2,4}) — built from a primitive root and
    discrete logs. Returns None when (ℤ/kℤ)* is not cyclic (the caller then skips that sample).
    Sound: the orthogonality theorems hold for every k; we verify on the cyclic subset we can
    enumerate exactly."""
    from math import gcd
    k = int(k)
    if k < 1:
        return None
    units = [a for a in range(1, k + 1) if gcd(a, k) == 1] if k > 1 else [0]
    phi = len(units)
    g = None                                   # find a primitive root (generator of the units)
    for cand in units:
        x, seen = 1, set()
        for _ in range(phi):
            x = (x * cand) % k; seen.add(x)
        if len(seen) == phi:
            g = cand; break
    if g is None:
        return None                            # (ℤ/kℤ)* not cyclic
    dlog, x = {}, 1                            # a = g^dlog[a]
    for j in range(phi):
        dlog[x] = j; x = (x * g) % k
    def mkchi(t):
        def chi(a):
            a = int(a) % k if k else 0
            if gcd(a, k) != 1:
                return mp.mpf(0)
            return mp.e ** (2 * mp.pi * mp.j * t * dlog[a] / phi)
        chi.modulus = k        # exposed so the sweep can couple a sampled χ to its modulus
        chi.index = t          # binder (χ : DirichletCharacter ℂ k  →  k := χ.modulus)
        return chi
    return [mkchi(t) for t in range(phi)]


# The FULL character group over small CYCLIC moduli, for sampling a ∀-bound Dirichlet-
# character binder `χ : DirichletCharacter ℂ k` (DLMF §27.8): φ(3)+φ(4)+φ(5)+φ(7)+φ(9)
# = 2+2+4+6+6 = 20 characters, covering the principal character of each modulus, the
# real quadratic characters (the non-principal χ mod 3 and χ₄ mod 4), and genuinely
# complex characters of order 4 (mod 5) and order 6 (mod 7, mod 9). Moduli with
# non-cyclic (ℤ/kℤ)* (8, 12, …) are outside `_dirichlet_chars`' primitive-root
# construction — omitted, never faked. Anchored in `verify()` against the DLMF 27.8
# DEFINING conditions (27.8.2 periodicity, 27.8.3 complete multiplicativity, 27.8.4
# vanishing exactly off the units, completeness/distinctness of the full character
# group) plus the independent χ₄ implementation — never by name.
SAMPLE_DIRICHLET_CHARS = [chi for _k in (3, 4, 5, 7, 9) for chi in _dirichlet_chars(_k)]


def _dirichlet_char_count(k):
    """`Nat.card (DirichletCharacter ℂ k)` — the number of distinct Dirichlet characters
    mod k, obtained by ENUMERATING the character group itself (`_dirichlet_chars` above:
    each character of a cyclic (ℤ/kℤ)* is pinned by χ(g) = a φ-th root of unity at a
    primitive root g) and taking the length of that enumeration — NOT by evaluating the
    totient formula, so the check of DLMF §27.8 ("there are exactly φ(k) different
    characters (mod k)", the text preceding 27.8.6) compares two decorrelated counts.
    Returns None for k = 0 or non-cyclic (ℤ/kℤ)* — the caller drops that sample (honest
    skip, never a fabricated value). Anchored in verify() against an exhaustive
    brute-force homomorphism count with no primitive-root input."""
    chars = _dirichlet_chars(k)
    return None if chars is None else mp.mpf(len(chars))


# Sample index grid for a ∀-quantified Dirichlet-character binder (χ : DirichletCharacter ℂ k):
# the extractor draws t from this grid and instantiates χ := _dirichlet_char_sample(k, t).
# Two NON-PRINCIPAL indices (t = 1, 2 of the generator-power enumeration) — the principal
# character is degenerate for most §27.8 rows (χ₀ ≡ 1 on units) and has its own dedicated
# theorems; two indices also keep the cartesian sample budget (24 combos) wide enough that
# the a : ZMod k grid {1,2,3} × moduli {5,7,9,11} is covered in full (3·4·2 = 24), so the
# non-unit residue (a=3, k=9) a `¬ IsUnit a` hypothesis demands is actually reached.
SAMPLE_DIRICHLET_TS = (1, 2)


def _dirichlet_char_sample(k, t):
    """A CONCRETE Dirichlet character mod k instantiating a universally quantified binder
    (χ : DirichletCharacter ℂ k) — the t-th member (index mod φ(k)) of the explicit
    cyclic-modulus enumeration `_dirichlet_chars` above. Anchored (verify()) to the DLMF
    §27.8 DEFINING relations, never by name: 27.8.1 χ(1)=1; 27.8.2 complete
    multiplicativity χ(mn)=χ(m)χ(n); 27.8.3 period k; 27.8.4 χ(n)=0 for gcd(n,k)>1; plus
    two DECORRELATED concrete characters — the nontrivial character mod 4 (= ZMod.χ₄:
    χ(3)=−1) and the quadratic character mod 5 (= the Legendre symbol (n|5): squares
    {1,4}→+1, non-residues {2,3}→−1) — and the non-principal orthogonality sum
    ∑_{n mod k} χ(n) = 0 (DLMF 27.8.6, the a≠1 column). Returns None when k is missing
    or (ℤ/kℤ)* is not cyclic — the caller drops that sample (honest skip, never a
    fabricated character)."""
    if k is None:
        return None
    chars = _dirichlet_chars(int(k))
    if not chars:
        return None
    return chars[int(t) % len(chars)]


# ∀-quantified MULTIPLICATIVE arithmetic-function binder — `(f : ArithmeticFunction R)`
# carrying an `hf : IsMultiplicative f` hypothesis (Mathlib
# `ArithmeticFunction.IsMultiplicative`; DLMF 27.3.1: f(1)=1 and f(mn)=f(m)f(n) whenever
# (m,n)=1). The sweep instantiates f at EVERY witness in this tuple via the `_fnwitness`
# substitution (fidelity_extract): each entry is a REGISTRY head, so evaluation goes
# through the already-anchored binding. Two structurally distinct members: φ = totient
# (DLMF 27.2.7 — multiplicative but NOT completely multiplicative, the distinguishing
# regime for 27.3.2 f(n)=∏f(p^{a_p}) vs the stronger 27.3.10 f(n)=∏f(p)^{a_p}) and
# μ = moebius (DLMF 27.2.12 — vanishes off squarefree n, exercising the zero regime).
# Self-validated in verify(): each witness's 27.3.1 hypothesis clauses (f(1)=1;
# f(mn)=f(m)f(n) on coprime pairs), its §27.2 anchor values, and the 27.3.2
# factorization product itself, BEFORE the sweep ever trusts the witness.
MULTIPLICATIVE_WITNESSES = ("totient", "μ")


# ∀-quantified CHARACTER binders over an ABSTRACT finite ring — `(χ : MulChar R R')`,
# `(ψ : AddChar R R')` with R a Type variable (the Gauss-sum defining surface
# `gaussSum_def`, DLMF 27.10.9): the sweep instantiates R := ZMod k on the cyclic-prime
# grid below. A `MulChar (ZMod k) ℂ` is exactly a Dirichlet character mod k, so χ draws
# from the anchored `_dirichlet_char_sample` enumeration; ψ draws x ↦ e^{2πinx/k}
# (every additive character of ℤ/kℤ has that form). t/n grids stay NON-principal /
# non-trivial (t ≢ 0 mod φ(k), gcd(n,k)=1) so the sampled Gauss sums are non-degenerate.
SAMPLE_MULCHAR_KTS = ((5, 1), (5, 2), (7, 1), (7, 2))
SAMPLE_ADDCHAR_NS = (1, 2)


def _mulchar_sample(k, t):
    """A concrete multiplicative character instantiating a ∀-quantified binder
    `(χ : MulChar R R')` at R := ZMod k, R' := ℂ — the t-th Dirichlet character mod k
    (`_dirichlet_char_sample` above, anchored to the DLMF 27.8.1–27.8.4 defining
    relations, never by name). Tagged with `.modulus = k` so the sweep can (a) pair the
    additive character's modulus to the SAME ring and (b) run a bare `∑ x, …`
    Finset.univ sum over the actual carrier {0,…,k−1}. None on a non-cyclic modulus —
    the caller drops that sample (honest skip, never a fabricated character)."""
    chi = _dirichlet_char_sample(k, t)
    if chi is None:
        return None
    chi.modulus = int(k)
    # `.principal` marks the PRINCIPAL character χ₀ (index 0 of the generator-power
    # enumeration) — Lean's `(1 : MulChar (ZMod k) ℂ)`. The sweep uses it to honor a
    # `χ ≠ 1` hypothesis per sample (a principal sample is OUTSIDE that hypothesis —
    # scoring it would fabricate a counterexample). Anchored in verify() against the
    # DEFINING property (χ ≡ 1 on every unit of ℤ/kℤ), never by index.
    chi.principal = (getattr(chi, "index", None) == 0)
    return chi


SAMPLE_MULCHARS = tuple(c for c in (_mulchar_sample(k, t) for (k, t) in SAMPLE_MULCHAR_KTS)
                        if c is not None)


def _addchar_sample(k, n):
    """A concrete additive character instantiating a ∀-quantified binder
    `(ψ : AddChar R R')` at R := ZMod k, R' := ℂ: ψₙ(x) = e^{2πi n x / k} — the DLMF
    27.10.9 kernel e^{2πimn/k} as a function of m. Anchored in verify() to the defining
    relations: ψ(0) = 1, additivity ψ(a+b) = ψ(a)ψ(b), period k, and the explicit value
    ψ₁(1) = e^{2πi/k}. `.modulus = k` tags the carrier for the univ-sum evaluator.
    `.primitive` tags whether ψₙ is a PRIMITIVE additive character of ℤ/kℤ — true iff
    gcd(n,k) = 1 — so the sweep can honor an `e.IsPrimitive` hypothesis per sample
    (DLMF 27.8.6 needs it: |G|² = k can fail for imprimitive ψ). Anchored in verify()
    against the DEFINING property ∀ a ≢ 0 ∃ x, ψ(ax) ≠ 1 (Mathlib `AddChar.IsPrimitive`:
    every nonzero shift a ↦ ψ(ax) is nontrivial), by brute force over the carrier —
    never by the gcd formula it is computed from."""
    from math import gcd
    k = int(k)

    def psi(x, _k=k, _n=int(n)):
        return mp.e ** (2 * mp.pi * mp.j * _n * (int(x) % _k) / _k)
    psi.modulus = k
    psi.primitive = (gcd(int(n), k) == 1) if k >= 1 else False
    return psi


def _gauss_sum_char(chi, psi):
    """Mathlib `gaussSum χ ψ = ∑ x, χ x * ψ x` on CHARACTER arguments — DLMF 27.10.9
    G(n,χ) = ∑_{m=1}^{k} χ(m) e^{2πimn/k} at ψ = ψₙ. NOT the same-named FLMF theta
    `gaussSum m n` (DLMF 20.11.1, `_gauss_sum` below), which keeps handling NUMERIC
    arguments — the extractor dispatches on the argument kind. Anchored in verify() to
    the classical evaluations G(1,(·|5)) = √5 and G(1,(·|7)) = i√7 (Gauss: +√p for
    p ≡ 1 mod 4, i√p for p ≡ 3 mod 4), the magnitude |G(1,χ)|² = k for primitive χ
    (27.10.11), and the separability G(n,χ) = χ̄(n)·G(1,χ) (27.10.10)."""
    k = getattr(chi, "modulus", None) or getattr(psi, "modulus", None)
    if k is None:
        raise ValueError("gaussSum: character argument without a modulus tag")
    return mp.fsum(chi(m) * psi(m) for m in range(1, int(k) + 1))


def _sawtooth_rat(p, q):
    """The sawtooth ((p/q)) = 0 if q ∣ p, else frac(p/q) − 1/2 — exact via integer residue
    (Python `%` gives a residue in [0,q), matching Int.fract for negative p too)."""
    m = int(p) % int(q)
    return mp.mpf(0) if m == 0 else mp.mpf(m) / int(q) - mp.mpf(1) / 2


def _sawtooth(x):
    """Dedekind's sawtooth ((x)) (DLMF 27.14 / DedekindSum.lean `sawtooth`):
    ((x)) = 0 for x ∈ ℤ, else Int.fract x − 1/2, with Int.fract x = x − ⌊x⌋ ∈ [0,1).
    Real-argument companion of the exact rational kernel `_sawtooth_rat` (anchored
    against it in verify()); an mpc argument raises and the sample drops honestly."""
    x = mp.mpf(x)
    fr = x - mp.floor(x)
    return mp.mpf(0) if fr == 0 else fr - mp.mpf(1) / 2


def _dedekind_sum(h, k):
    """Dedekind sum s(h,k) = Σ_{r=0}^{k-1} ((r/k))·((hr/k)) (DedekindSum.lean); s(h,0)=0 junk."""
    h, k = int(h), int(k)
    if k <= 0:
        return mp.mpf(0)
    return mp.fsum(_sawtooth_rat(r, k) * _sawtooth_rat(h * r, k) for r in range(k))


def _liouville(n):
    """Liouville λ(n) = (−1)^Ω(n), Ω = number of prime factors with multiplicity (λ(0)=0 junk)."""
    n = _nat(n, "liouville")
    if n == 0:
        return mp.mpf(0)
    omega, mm, d = 0, n, 2
    while d * d <= mm:
        while mm % d == 0:
            omega += 1; mm //= d
        d += 1
    if mm > 1:
        omega += 1
    return mp.mpf((-1) ** omega)


def _von_staudt_sum(k):
    """FLMF `vonStaudtSum k` = Σ_{p prime, p < 2k+2, (p−1) ∣ 2k} 1/p — the von
    Staudt–Clausen fractional correction of B_{2k} (DLMF 24.10; VonStaudtClausen.lean).
    The Lean Finset ranges over p ∈ range (2k+2), which already holds EVERY prime with
    (p−1) ∣ 2k once k ≥ 1 (such p satisfy p ≤ 2k+1), so the binding mirrors the def
    exactly; at k = 0 the range {0,1} has no prime and the sum is 0 (the divisibility
    (p−1) ∣ 0 is vacuously irrelevant there). Exact trial-division primality; anchored in
    verify() at the DLMF 24.10.1 values 5/6, 31/30, 41/42 and the theorem's own defining
    integrality B₁₂ + Σ = 1 (the 691 test)."""
    k = _nat(k, "vonStaudtSum")

    def _isp(p):
        if p < 2:
            return False
        d = 2
        while d * d <= p:
            if p % d == 0:
                return False
            d += 1
        return True

    return mp.fsum(mp.mpf(1) / p for p in range(2, 2 * k + 2)
                   if _isp(p) and (2 * k) % (p - 1) == 0)


def _eulerian(n, k):
    """Eulerian number ⟨n,k⟩ (FLMF `eulerian`, DLMF 26.14) via its recurrence:
    ⟨0,0⟩=1, ⟨n+1,0⟩=1, ⟨n+1,k+1⟩=(k+2)⟨n,k+1⟩+(n−k)⟨n,k⟩. Row n sums to n!."""
    n, k = _nat(n, "eulerian n"), _nat(k, "eulerian k")
    if k > n:
        return mp.mpf(0)
    row = [1] + [0] * n
    for nn in range(1, n + 1):
        new = [0] * (n + 1)
        new[0] = 1
        for kk in range(1, nn + 1):
            new[kk] = (kk + 1) * row[kk] + (nn - kk) * row[kk - 1]
        row = new
    return mp.mpf(row[k])


def _stirling2(n, k):
    """Stirling number of the 2nd kind S(n,k) (Mathlib `partition`/`stirlingSecond`) — exact,
    via the inclusion–exclusion formula S(n,k) = (1/k!) Σⱼ (−1)ʲ C(k,j)(k−j)ⁿ."""
    import math
    n, k = _nat(n, "stirling2 n"), _nat(k, "stirling2 k")
    if k == 0:
        return mp.mpf(1) if n == 0 else mp.mpf(0)
    tot = sum((-1) ** j * math.comb(k, j) * (k - j) ** n for j in range(k + 1))
    return mp.mpf(tot // math.factorial(k))


def _complete_k(k):
    """Complete elliptic K of MODULUS k = ellipticF(π/2,k) = mp.ellipk(k²). Real only for
    |k| ≤ 1 (mpmath returns a complex value for m = k² > 1); out-of-domain points drop."""
    if abs(k) > 1:
        raise ValueError("completeK: |k| > 1 outside the real domain")
    return mp.ellipk(k ** 2)


def _complete_e(k):
    """Complete elliptic E of MODULUS k = mp.ellipe(k²); real only for |k| ≤ 1."""
    if abs(k) > 1:
        raise ValueError("completeE: |k| > 1 outside the real domain")
    return mp.ellipe(k ** 2)


# ── theta nulls and the modular trio (M7 / Tier B2) ──────────────────────────
# FLMF θⱼ z τ are built on Mathlib jacobiTheta₂ z τ = Σ exp(2πi n z + πi n² τ):
# z is NOT pre-multiplied by π (period 1 in z), and the second argument is the
# lattice parameter τ (Im τ > 0), not the nome. mpmath's jtheta(j, w, q) uses
# w = πz and the NOME q = e^{iπτ} — both knobs anchored below and in CONVENTIONS.
def _theta_q(tau):
    """nome q = e^{iπτ}; requires Im τ > 0 (else |q| ≥ 1 and the series diverges —
    mpmath raises, the sample point is dropped, never half-trusted)."""
    return mp.exp(mp.mpc(0, 1) * mp.pi * tau)


def _theta_reduce(j, z, tau):
    """Quasi-period argument reduction, DLMF 20.2(iii) iterated n times, in the
    FLMF z-convention (period 1 in z, quasi-period τ):
        θⱼ(z + nτ, τ) = εⱼⁿ · e^{−iπn²τ − 2πinz} · θⱼ(z, τ),   ε₁ = ε₄ = −1, ε₂ = ε₃ = +1.
    Returns (z_red, prefactor) with θⱼ(z, τ) = prefactor · θⱼ(z_red, τ) EXACTLY,
    where n = nint(Im z / Im τ) pulls Im z_red into the fundamental strip
    |Im z_red| ≤ Im τ / 2.  WHY: for |Im z| ≫ Im τ the theta series has peak
    terms of size ~e^{π(Im z)²/Im τ} cancelling down to an O(prefactor·θ(z_red))
    value — e.g. the Tier-1 grid point z = −0.7+2.1i = 1/2 − 11 + 7τ at
    τ = 1.4+0.3i has θ₂ series terms ~9e19 cancelling ~30 digits (FALSE-FAILing
    the exact DLMF 22.4.3 parity row sc_neg_left at rel 1.6e-15, and the
    quasi-periodicity rows 20.2.6–20.2.9). After reduction the series terms are
    O(1) and the giant factor is carried by the single exact exponential
    prefactor — the |Im z|-driven cancellation is gone entirely. ADDITIVE:
    n = 0 (the whole classical sampling strip) is bit-for-bit the old path."""
    z, tau = mp.mpmathify(z), mp.mpmathify(tau)
    im_tau = mp.im(tau)
    if not (im_tau > 0 and mp.isfinite(z) and mp.isfinite(tau)):
        return z, mp.mpf(1)                    # let _theta_q raise downstream
    n = int(mp.nint(mp.im(z) / im_tau))
    if n == 0:
        return z, mp.mpf(1)
    z_red = z - n * tau
    pref = mp.exp(mp.mpc(0, -1) * mp.pi * (n * n * tau + 2 * n * z_red))
    if j in (1, 4) and n % 2:
        pref = -pref
    return z_red, pref


def _theta_core(j, z, tau):
    """Direct jtheta evaluation of FLMF θⱼ z τ (assumes the working precision
    is already raised by the caller): jtheta(j, πz_red, e^{iπτ}) · quasi-period
    prefactor (`_theta_reduce`, DLMF 20.2(iii)), with the θ₁/θ₂ BRANCH KNOB —
    mpmath resolves the q^{1/4} prefactor as the PRINCIPAL fourth root of the
    nome, while FLMF/Classical.lean carries the entire prefactor e^{iπτ/4}; the
    two differ by a power of i once Re τ ∉ (-1, 1] (e.g. lattice-parameter
    shifts τ+1, τ+1/2 in DLMF 20.7(viii)). Corrected by the exact ratio
    e^{iπτ/4}/q^{1/4} (≡ 1 on the principal strip)."""
    z_red, pref = _theta_reduce(j, z, tau)
    q = _theta_q(tau)
    # At very large Im τ the nome is below working precision.  Passing that
    # near-zero mpf to mpmath's fixed-point jtheta backend can raise
    # "outrageous shift count"; use the first exact q-series term instead.
    # The discarded tail is smaller than the ambient precision threshold.
    if q == 0 or abs(q) < mp.power(10, -(mp.mp.dps + 10)):
        if j in (3, 4):
            return pref
        lead = 2 * mp.exp(mp.mpc(0, 1) * mp.pi * tau / 4)
        return pref * lead * (mp.sin(mp.pi * z_red) if j == 1 else mp.cos(mp.pi * z_red))
    val = pref * mp.jtheta(j, mp.pi * z_red, q)
    if j in (1, 2):
        val *= mp.exp(mp.mpc(0, 1) * mp.pi * tau / 4) / q ** mp.mpf(0.25)
    return val


# Below this Im τ the nome |q| = e^{−π·Im τ} sits on jtheta's |q| → 1 wall
# (mpmath raises `abs(q) > THETA_Q_LIM` outright for Im τ ≲ 3e−8, and the term
# count blows up long before) — switch to the Jacobi imaginary transformation
# DLMF 20.7(viii). 0.05 keeps the whole Tier-1 τ = ix², x → 0⁺ Mellin sampling
# regime of 20.10.1–20.10.3 on the transformed branch.
_THETA_IM_TAU_MIN = mp.mpf("0.05")
# DLMF 20.7.30–20.7.33 pairing under τ ↦ −1/τ: θ₁↔θ₁, θ₂↔θ₄, θ₃↔θ₃, θ₄↔θ₂.
_THETA_IMAG_PAIR = {1: 1, 2: 4, 3: 3, 4: 2}


def _theta(j):
    """FLMF θⱼ z τ  →  `_theta_core` (jtheta + the DLMF 20.2(iii) quasi-period
    reduction + the θ₁/θ₂ e^{iπτ/4} branch knob; DLMF 20.2.1–20.2.4 numbering),
    routed through the Jacobi IMAGINARY TRANSFORMATION DLMF 20.7.30–20.7.33
    when Im τ < `_THETA_IM_TAU_MIN` — in FLMF variables (DLMF z = π·z_FLMF):
        θⱼ(z|τ) = εⱼ · (−iτ)^{−1/2} · e^{−iπz²/τ} · θ_{σ(j)}(−z/τ | −1/τ),
        σ = (1 2 3 4 ↦ 1 4 3 2),  ε₁ = −i,  ε₂ = ε₃ = ε₄ = 1,
    with the PRINCIPAL square root (Re(−iτ) = Im τ > 0, so no branch
    ambiguity). Im(−1/τ) = Im τ/|τ|², so the transformed nome e^{−iπ/τ} is
    TINY exactly where the direct nome e^{iπτ} hits jtheta's |q| → 1 wall (the
    Tier-1 τ = ix², x → 0⁺ Mellin grid of 20.10.1–20.10.3). Applied only when
    it strictly helps (Im(−1/τ) > Im τ, i.e. |τ| < 1); otherwise bit-for-bit
    the old direct path — ADDITIVE, and still-out-of-reach points raise as
    before (honest skip, never a half-trusted number).
    GUARD DIGITS: near a lattice zero of θⱼ (1/2 + ℤ + ℤτ for θ₂, etc.) the
    value is intrinsically tiny (the sweep grid can sample exactly ON a zero,
    up to representation error), so even the reduced O(1)-term series cancels
    to ~e^{-dps}; evaluating at DOUBLED working precision absorbs that before
    rounding back (same additive contract as the endpoint-singular quads,
    fidelity_extract.py `with mp.workdps(2*dps)`); the equality gate itself is
    NOT loosened."""
    def _f(z, tau, _j=j):
        with mp.workdps(2 * mp.mp.dps):
            z, tau = mp.mpmathify(z), mp.mpmathify(tau)
            im_tau = mp.im(tau)
            if (mp.isfinite(z) and mp.isfinite(tau) and 0 < im_tau
                    and im_tau < _THETA_IM_TAU_MIN
                    and mp.im(-1 / tau) > im_tau):
                pref = (mp.exp(-mp.mpc(0, 1) * mp.pi * z * z / tau)
                        / mp.sqrt(-mp.mpc(0, 1) * tau))
                if _j == 1:
                    pref *= -mp.mpc(0, 1)               # DLMF 20.7.30 extra −i
                return pref * _theta_core(_THETA_IMAG_PAIR[_j], -z / tau, -1 / tau)
            return _theta_core(_j, z, tau)
    return _f


# ── Termwise (heat-kernel) Laplace transform of a theta q-series ─────────────────
# General principle: an integral transform of a theta/heat-kernel q-series is the
# term-by-term transform of its series, so NO quadrature ever touches the τ → 0
# modular cusp — the regime where a naive `mp.quad` over t ∈ (0,∞) of
# θⱼ(z₀ | iπt/ℓ²) balloons (measured 5.7 GB / SIGKILL, targeted_check.py:16) because
# each near-cusp sample needs unbounded guard digits — the theta_20_10_4/5 skips. This
# turns those honest skips into exact, cheap, quadrature-free verifications.
_THETA_LAPLACE_TABLE = {          # DLMF 20.2 numbering →  (σⱼ, ε alternates?, cⱼ)
    3: (mp.mpf(1),  False, mp.mpf(0)),          # θ₃: σ=+1, ε=1,      c=0
    4: (mp.mpf(1),  False, -mp.mpf(1) / 2),     # θ₄: σ=+1, ε=1,      c=−1/2
    2: (mp.mpf(1),  True,  mp.mpf(0)),          # θ₂: σ=+1, ε=(−1)ᵏ,  c=0
    1: (-mp.mpf(1), True,  -mp.mpf(1) / 2),     # θ₁: σ=−1, ε=(−1)ᵏ,  c=−1/2
}


def _theta_lattice_laplace(j, z0, s, ell):
    """`∫₀^∞ e^{−s t} θⱼ(z₀ | iπ t/ℓ²) dt` — the Laplace transform of a theta
    function w.r.t. the lattice parameter (DLMF 20.10.4/20.10.5), evaluated by the
    TERMWISE (heat-kernel) transform instead of quadrature.

    Route.  The Jacobi imaginary transformation (DLMF 20.7.30–33) rewrites the
    integrand as a Gaussian heat kernel on the shifted lattice ℤ + cⱼ:
        θⱼ(z₀ | iπt/ℓ²) = σⱼ · (ℓ/√(πt)) · Σ_{k∈ℤ} εⱼ(k) · e^{−ℓ²(z₀−cⱼ−k)²/t},
    and each term's Laplace integral is EXACT,
        ∫₀^∞ t^{−1/2} e^{−st − A/t} dt = √(π/s) · e^{−2√(As)}   (Re s > 0),
    so
        = σⱼ · (ℓ/√s) · Σ_{k∈ℤ} εⱼ(k) · e^{−2 √(ℓ²(z₀−cⱼ−k)² · s)}   (principal √,
    branch Re ≥ 0).  The summand decays like e^{−2ℓ|k|√s}, so the lattice sum
    converges GEOMETRICALLY for every complex z₀ (hence every β) — it is the raw
    integral value computed from the theta series alone, INDEPENDENT of the DLMF
    right-hand side (a wrong sign / wrong argument in the printed formula is caught,
    not reproduced).  Table (DLMF 20.2.1–20.2.4):
        θ₃: σ=+1, ε=1,      c=0        θ₄: σ=+1, ε=1,      c=−1/2
        θ₂: σ=+1, ε=(−1)ᵏ, c=0        θ₁: σ=−1, ε=(−1)ᵏ, c=−1/2
    Verified by hand to reproduce the corrected 20.10.4/5 closed forms
    (θ₃ ↦ (ℓ/√s) cosh(β√s)/sinh(ℓ√s), θ₁ ↦ (ℓ/√s) sinh(β√s)/cosh(ℓ√s), …) and
    anchored in verify() against the INDEPENDENT direct q-series termwise Laplace
    Σ_{n∈ℤ} e^{2πinz₀}/(s+π²n²/ℓ²) (a different series representation of the same
    integral — a direct quadrature is unusable here, it is exactly what OOMs at the
    cusp).  Evaluated at doubled working precision (same additive contract as `_theta`)."""
    if j not in _THETA_LAPLACE_TABLE:
        raise ValueError(f"thetaLaplace: j={j} not in 1..4")
    sigma, alt, c = _THETA_LAPLACE_TABLE[j]
    s, z0, ell = mp.mpc(s), mp.mpc(z0), mp.mpf(ell)
    if not (mp.re(s) > 0 and ell > 0):
        raise ValueError("thetaLaplace: outside the Laplace domain (Re s > 0, ℓ > 0)")
    # DLMF constraint |Re β| + |Im β| ≤ ℓ (20.10.4/5), intrinsic form. Across all four
    # rows the FLMF z-argument satisfies β/(2ℓ) = z₀ − cⱼ − 1/2 (θ₁,θ₄: z₀ = β/2ℓ,
    # c = −1/2; θ₂,θ₃: z₀ = (ℓ+β)/2ℓ, c = 0 — both give z₀−c−1/2 = β/2ℓ), so the
    # constraint is |Re(z₀−cⱼ) − 1/2| + |Im z₀| ≤ 1/2. This is STRICTER than mere
    # convergence of the integral: θⱼ is quasi-periodic in z₀ (period 1), so the LHS
    # integral converges on a periodic z₀-domain, but the RHS closed form (sinh/cosh(β√s))
    # is NOT periodic — outside the constraint the (convergent) integral departs from the
    # printed formula and the THEOREM is simply out of scope. Raise there so the sweep
    # drops the sample honestly (the uncaptured `hβ` hypothesis lets the ℂ grid straddle
    # the constraint); a small margin excludes the marginal boundary.
    if abs(mp.re(z0 - c) - mp.mpf(1) / 2) + abs(mp.im(z0)) > mp.mpf(1) / 2 + mp.mpf("1e-12"):
        raise ValueError("thetaLaplace: outside the DLMF constraint "
                         "|Re β| + |Im β| ≤ ℓ (theorem out of scope)")
    outer = mp.mp.dps
    with mp.workdps(2 * outer):
        rs = mp.sqrt(s)                       # principal √s (Re > 0 since Re s > 0)
        eps = mp.mpf(10) ** (-(outer + 10))
        k0 = int(mp.nint(mp.re(z0 - c)))      # nearest lattice point (smallest |dₖ|)

        def term(k):
            dk = z0 - c - k
            r = mp.sqrt(ell * ell * dk * dk * s)
            if mp.re(r) < 0:                  # branch: Re √(As) ≥ 0 for decay
                r = -r
            e = mp.exp(-2 * r)
            return -e if (alt and k % 2) else e     # εⱼ(k) = (−1)ᵏ when `alt`

        tot = term(k0)
        for m in range(1, 4001):
            tp, tm = term(k0 + m), term(k0 - m)
            tot += tp + tm
            if m >= 4 and abs(tp) < eps * (1 + abs(tot)) and abs(tm) < eps * (1 + abs(tot)):
                return sigma * (ell / rs) * tot
    raise ValueError("thetaLaplace: lattice sum not stabilized by |k| = 4000 "
                     "(√s too small for the sweep precision)")


def _ramanujan_theta(a, b):
    """Ramanujan's theta function f(a,b) = Σ_{n=−∞}^{∞} a^{n(n+1)/2} b^{n(n−1)/2}
    — bound to the DLMF 20.11.3 DEFINING bilateral series (§5: by formula, never
    by name; there is no mpmath builtin).  Exponent convention: n(n+1) and n(n−1)
    are products of consecutive integers, hence even and ≥ 0 for every n ∈ ℤ, so
    integer `// 2` is exact and each exponent is a nonnegative integer — matching
    the Lean zpow spelling in Ch20Generalizations.lean term-for-term
    (n=−1 ↦ b, n=0 ↦ 1, n=1 ↦ a, n=2 ↦ a³b, n=−2 ↦ ab³).
    DOMAIN GUARD: DLMF states 20.11.3 for |ab| < 1 (the general term is
    (ab)^{n(n−1)/2}·aⁿ, so |ab| ≥ 1 diverges); the Lean tsum is junk-0 there and
    any truncation would be meaningless — raise, so the sample point is dropped
    (honest skip, never a silently wrong number).  TRUNCATION: symmetric partial
    sums n = 0, ±1, …, stopping only once BOTH wing terms fall below the target
    precision (the doubly-exponential |ab|^{~n²/2} tail then sits below it too);
    if that never happens by n = 400 (|ab| ≈ 1, or |a| so large the wing has not
    yet turned over), raise — again an honest skip, never a truncated lie.
    Evaluated at doubled working precision (same additive contract as `_theta`).
    Anchored in verify(): DLMF 20.11.4 θ₃ tie + the independent Jacobi triple
    product f(a,b) = (−a;ab)∞ (−b;ab)∞ (ab;ab)∞."""
    if abs(mp.mpc(a) * mp.mpc(b)) >= 1:
        raise ValueError("ramanujanTheta: |ab| >= 1 — outside the DLMF 20.11.3 "
                         "convergence domain (Lean tsum is junk-0 there)")
    outer_dps = mp.mp.dps
    with mp.workdps(2 * outer_dps):
        aa, bb = mp.mpc(a), mp.mpc(b)
        eps = mp.mpf(10) ** (-(outer_dps + 10))
        term = lambda n: aa ** ((n * (n + 1)) // 2) * bb ** ((n * (n - 1)) // 2)
        s = term(0)
        for n in range(1, 401):
            tp, tm = term(n), term(-n)
            s += tp + tm
            if n >= 8 and abs(tp) < eps * (1 + abs(s)) and abs(tm) < eps * (1 + abs(s)):
                return s
    raise ValueError("ramanujanTheta: bilateral series not stabilized by n = 400 "
                     "(|ab| too close to 1 for the sweep precision)")


def _jtp_factor_cleared(q, z, n):
    """FLMF `tripleProductFactorCleared q z n = (z² + q^(2n−1))·(1 + q^(2n−1)·z²)`
    (JacobiTripleProduct.lean) — the n-th symmetric DLMF 20.5.3 factor cleared of
    negative powers by an extra z²: for n ≥ 1, z ≠ 0 it equals
    z²·(1 + q^{2n−1} z²)(1 + q^{2n−1} z⁻²) (anchored so in verify()).  The Lean
    exponent `2*n − 1` is Nat TRUNCATED subtraction, so at n = 0 it is 0 (q⁰ = 1):
    the binding mirrors that with max(2n−1, 0), term-for-term with the Lean def."""
    q, z = mp.mpmathify(q), mp.mpmathify(z)
    e = max(2 * int(n) - 1, 0)
    return (z ** 2 + q ** e) * (1 + q ** e * z ** 2)


def _jtp_factor(q, z, n):
    """FLMF `tripleProductFactor q z n = (1 − q^{2n}) · tripleProductFactorCleared q z n`
    (JacobiTripleProduct.lean) — the full n-th DLMF 20.5.3 factor
    (1 − q^{2n})(1 + q^{2n−1} z²)(1 + q^{2n−1} z⁻²) in cleared (z²-multiplied) form."""
    q = mp.mpmathify(q)
    return (1 - q ** (2 * int(n))) * _jtp_factor_cleared(q, z, n)


def _jtp_prod(q, z, N):
    """FLMF `tripleProductProd q z N = ∏_{n ∈ range N} tripleProductFactor q z (n+1)`
    (JacobiTripleProduct.lean) — the truncated DLMF 20.5.3 product side; equals
    z^{2N}·∏_{n=1}^{N}(1−q^{2n})(1+q^{2n−1}z²)(1+q^{2n−1}z⁻²).  A finite polynomial
    (no domain guard needed).  Anchored in verify() against the INDEPENDENT
    mp.jtheta(3,·) via the Jacobi triple product identity (N large, |q| < 1)."""
    out = mp.mpmathify(1)
    for n in range(1, int(N) + 1):
        out *= _jtp_factor(q, z, n)
    return out


def _jtp_sum(q, z, N):
    """FLMF `tripleProductSum q z N = Σ_{n=−N}^{N} q^{(n²).toNat} · z^{(2n).toNat}`
    (JacobiTripleProduct.lean) — mirrors the Lean def term-for-term INCLUDING the
    Int.toNat clamp: (2n).toNat = max(2n, 0), so every n < 0 term carries z⁰ = 1
    (the def is a CommRing surface with no negative powers; whether it matches the
    DLMF 20.5.3 sum Σ q^{n²} z^{2n} is a theorem-level question the sweep must be
    able to probe — the binding must NOT silently symmetrize).  Anchored in
    verify() at z = 1, where the clamp is invisible, against jtheta(3, 0, q)."""
    q, z = mp.mpmathify(q), mp.mpmathify(z)
    return mp.fsum(q ** (n * n) * z ** max(2 * n, 0)
                   for n in range(-int(N), int(N) + 1))


def _combined_theta(m, n, z, tau):
    """FLMF `combinedTheta m n z τ` = the combined theta function φ_{m,n}(πz, q),
    q = e^{iπτ} (DLMF 20.11.6–20.11.8, Ch20Generalizations.lean), computed
    INDEPENDENTLY of `_theta` straight from the DLMF defining quotients in DLMF
    variables (w = πz, jtheta nome q):
        n = 1 (20.11.6):  φ_{m,1} = θ₁′(0,q) θₘ(w,q) / (θₘ(0,q) θ₁(w,q));
        m = 1 (20.11.7):  φ_{1,n} = θₙ(0,q) θ₁(w,q) / (θ₁′(0,q) θₙ(w,q));
        else  (20.11.8):  φ_{m,n} = θₙ(0,q) θₘ(w,q) / (θₘ(0,q) θₙ(w,q)).
    DLMF θ₁′(0,q) is the z-derivative in the DLMF argument, i.e. exactly
    jtheta(1, 0, q, derivative=1) — matching the Lean `π⁻¹ · deriv (θ₁ · τ) 0`
    (FLMF θ₁ z τ = θ₁^DLMF(πz, q), so the π⁻¹ undoes the chain rule).  Every
    branch pairs each θ-index j once in the numerator and once in the
    denominator, so the θ₁/θ₂ q^{1/4} branch knob (see `_theta`) cancels and no
    correction is needed.  Evaluated at DOUBLED working precision to absorb the
    |Im z| ≫ Im τ series cancellation the raw (unreduced) jtheta suffers on the
    Tier-1 ℂ grid (same additive contract as `_theta`).  Im τ ≤ 0 gives |q| ≥ 1
    and mpmath raises — honest domain drop.  Anchored in verify(): the 20.4.6
    derivative null θ₁′(0,q) = θ₂θ₃θ₄(0,q), a Lean-def replay through the
    independent `_theta` path (reduction + branch + finite-difference deriv) in
    all three (m,n) regimes, the z→0 normalization πz·φ_{2,1}(z) → 1, and the
    DLMF 22.2.4 Jacobi-sn tie θ₃²(0,q)·φ_{1,4}(z,τ) = sn(πz·θ₃²(0,q), k)."""
    m, n = int(m), int(n)
    with mp.workdps(2 * mp.mp.dps):
        q = _theta_q(tau)
        w = mp.pi * mp.mpmathify(z)
        th = lambda j, x: mp.jtheta(j, x, q)
        th1p = mp.jtheta(1, 0, q, derivative=1)
        if n == 1:
            return th1p * th(m, w) / (th(m, 0) * th(1, w))
        if m == 1:
            return th(n, 0) * th(1, w) / (th1p * th(n, w))
        return th(n, 0) * th(m, w) / (th(m, 0) * th(n, w))


def _elliptic_modulus(tau):
    """FLMF `ellipticModulus τ = θ₂(0,τ)²/θ₃(0,τ)²` (= k(τ), DLMF 22.2.2 via 20).
    Uses `_theta(2)` (the e^{iπτ/4}-anchored θ₂), so k² picks up the same ±1 as
    the Lean θ₂null² once Re τ ∉ (-1,1] — consistency with the `θ₂null` binding."""
    return _theta(2)(0, tau) ** 2 / _theta(3)(0, tau) ** 2


def _complementary_modulus(tau):
    """FLMF `complementaryModulus τ = θ₄(0,τ)²/θ₃(0,τ)²` (= k′(τ)).
    NOTE the same-name hazard: `FLMF/Functions/Theta/JacobiSpecialValues.lean`
    also defines a REAL `complementaryModulus (k : ℝ) = √(1−k²)`. No DLMF-tagged
    row uses that one today; if one appears, a real argument here gives |q| = 1
    and mpmath raises → honest skip, never a silently wrong number."""
    return _theta(4)(0, tau) ** 2 / _theta(3)(0, tau) ** 2


def _modular_lambda(tau):
    """FLMF `modularLambda τ = (θ₂/θ₃)⁴ = k(τ)²` — λ is the SQUARE of the modulus
    (the λ-vs-k trap is anchored at τ = i: λ(i) = 1/2, k(i) = 1/√2)."""
    return (_theta(2)(0, tau) / _theta(3)(0, tau)) ** 4


def _complementary_lambda(tau):
    """FLMF `complementaryLambda τ = (θ₄/θ₃)⁴ = 1 − λ(τ)`."""
    return (_theta(4)(0, tau) / _theta(3)(0, tau)) ** 4


def _gauss_sum(m, n):
    """FLMF `gaussSum m n = ∑_{k=0}^{n−1} exp(−πi k² m / n)` (DLMF 20.11.1,
    Ch20Generalizations.lean) — the quadratic Gauss sum in the DLMF `e^{−πik²m/n}`
    phase convention, NOT the number-theorists' `e^{2πik²m/n}` (the two disagree
    already at G(1,3): DLMF gives 1, the 2πi convention gives i√3). Direct
    transcription of the Lean finite sum: total in m ∈ ℤ (may be negative — the
    reciprocity RHS calls G(−n, m)) and n ∈ ℕ, empty sum 0 at n = 0.
    Anchors (from the defining sum): G(1,2) = 1 − i, G(−2,1) = 1,
    G(1,4) = 2e^{−πi/4} = √2·(1 − i)."""
    m, n = int(m), int(n)
    if n <= 0:
        return mp.mpc(0)
    return mp.fsum(mp.exp(-mp.pi * mp.j * k * k * m / n) for k in range(n))


# ── §20.6 lattice-sum coefficients δ/α/β/γ_{2j}(τ) (M7 tail; DLMF 20.6.6–20.6.9,
# Ch20PowerSeries.lean) ───────────────────────────────────────────────────────
# The Lean defs are honest ITERATED double sums Σ'_n Σ'_m (m + s + (n + t)τ)^{−2j}
# (inner m, outer n — exactly DLMF's order; DLMF warns the order matters only at
# j = 1, where the joint sum is merely conditionally convergent). Bound to the
# DEFINING formulas (§5) through the CLOSED-FORM inner sum: for a ∉ ℤ,
#     Σ_{m∈ℤ} (m+a)^{−2j} = ζ(2j, a) + ζ(2j, 1−a)
# (split at m = 0; ζ(s,a) = Σ_{m≥0}(m+a)^{−s} extends to all complex a by the
# exact recurrence ζ(s,a) = a^{−s} + ζ(s,a+1), and even integer exponents are
# branch-free, so the Hurwitz values ARE the reciprocal powers — anchored at
# j = 1 against the classical π²/sin²(πa) in verify()). The exact inner value
# makes the outer n-sum exponentially convergent (inner ~ e^{−4πj·n·Im τ}).
# WHY closed form: a doubly-truncated brute force carries the O(1/N) inner tail
# at j = 1 (rel ≈ 5e−2 at N = 200) and would FALSE-FAIL the correct 20.6.2–20.6.5;
# with the exact inner sum, end-to-end 20.6.2/20.6.3 reproduce to ~1e−30.
# HONEST DROPS: j = 0 and Im τ ≤ 0 (the Lean junk-tsum regimes flagged in the
# defs' docstrings) raise, as does an outer sum unstabilized by the n-cap —
# a sample point drops, never a fabricated number.
def _lattice_inner(j, a):
    """Exact inner m-sum Σ_{m∈ℤ}(m+a)^{−2j} = ζ(2j,a) + ζ(2j,1−a) (a ∉ ℤ).
    FAST PATH (every tail level has Im a ≠ 0): by evenness S(a) = S(−a), take
    Im a > 0 and use the equivalent exponentially convergent Lambert form
        S_j(a) = (−1)^j (2π)^{2j}/(2j−1)! · Σ_{k≥1} k^{2j−1} q^k,  q = e^{2πia}
    (the csc²-derivative ladder: Σ(m+a)^{−2} = π²/sin²(πa) = −4π²·Σ k qᵏ, and
    each ∂/∂a pulls down 2πi·k — both sides meromorphic in a, so the identity
    holds wherever |q| < 1; anchored against the ζ pair in verify()). The term
    k^{2j−1}|q|ᵏ peaks at k* = (2j−1)/(2π·Im a), so convergence is certified
    only PAST the peak. ~µs per call vs ~ms for two complex Hurwitz ζ's — the
    difference between an EVAL_BUDGET timeout and a decided verdict for the
    tsum rows 20.6.2–20.6.5; tolerances unchanged (nothing loosened)."""
    im = mp.im(mp.mpmathify(a))
    if im == 0:
        return mp.zeta(2 * j, a) + mp.zeta(2 * j, 1 - a)
    b = a if im > 0 else -a
    q = mp.exp(2 * mp.pi * mp.mpc(0, 1) * b)
    n = 2 * j - 1
    eps = mp.mpf(10) ** (-(mp.mp.dps + 6))
    kpeak = int(n / (2 * mp.pi * abs(im))) + 1
    s = mp.mpf(0)
    qk = mp.mpc(1)
    for k in range(1, 100001):
        qk = q ** k if k % 64 == 0 else qk * q   # periodic refresh vs drift
        term = mp.mpf(k) ** n * qk
        s += term
        if k > kpeak and abs(term) < eps * (1 + abs(s)):
            return (-1) ** j * (2 * mp.pi) ** (2 * j) / mp.factorial(n) * s
    raise ValueError("lattice inner sum: k-series not stabilized "
                     "(Im a too small for the sweep precision)")


def _lattice_args(j, tau, name):
    """Shared honest-drop guard: j must be a positive integer (j = 0 is the Lean
    junk-tsum divergent case), Im τ > 0 (else every inner sum diverges)."""
    n = int(j)
    if n != j or n < 1:
        raise ValueError(f"{name}: j = {j} outside the DLMF 20.6 index range j ≥ 1 "
                         "(the Lean tsum is junk there)")
    tau = mp.mpmathify(tau)
    if not (mp.isfinite(tau) and mp.im(tau) > 0):
        raise ValueError(f"{name}: Im τ ≤ 0 — the lattice sums diverge "
                         "(the Lean tsum is junk there)")
    return n, tau


# (name, j, τ, dps)-keyed memo: the Tier-1 tsum truncation of 20.6.2–20.6.5
# re-evaluates the SAME coefficient δ/α/β/γ_{2j}(τ) at every z-sample of a
# shared τ — cache the exact values so each (j, τ) is summed once per sweep
# precision (a pure memo: bit-identical values, nothing loosened).
_LATTICE_CACHE = {}


def _lattice_memo(name, fn):
    def _f(j, tau):
        j, tau = _lattice_args(j, tau, name)
        key = (name, j, tau, mp.mp.dps)
        if key not in _LATTICE_CACHE:
            _LATTICE_CACHE[key] = fn(j, tau)
        return _LATTICE_CACHE[key]
    return _f


def _lattice_tail(j, tau, shifts):
    """Outer sum over n ≥ 1 of the exact inner sums at `shifts(n)` (the ±n pair).
    Terms decay like e^{−4πj·n·Im τ}; stop on two consecutive negligible pairs
    (n-cap from Im τ, floor 12), inside the caller's raised working precision."""
    eps = mp.mpf(10) ** (-(mp.mp.dps + 6))
    nmax = int(mp.ceil((mp.mp.dps + 12) * mp.log(10) / (2 * mp.pi * mp.im(tau)))) + 8
    total = mp.mpf(0)
    small = 0
    for n in range(1, max(nmax, 12) + 1):
        t = mp.fsum(_lattice_inner(j, a) for a in shifts(n))
        total += t
        if abs(t) < eps * (1 + abs(total)):
            small += 1
            if small >= 2:
                return total
        else:
            small = 0
    raise ValueError("lattice sum: outer n-sum not stabilized "
                     "(Im τ too small for the sweep precision)")


def _lattice_delta(j, tau):
    """δ_{2j}(τ) (DLMF 20.6.6): (0,0) excluded — the n = 0 inner sum is
    Σ_{m≠0} m^{−2j} = 2ζ(2j)."""
    j, tau = _lattice_args(j, tau, "latticeDelta")
    with mp.workdps(mp.mp.dps + 10):
        r = 2 * mp.zeta(2 * j) + _lattice_tail(j, tau, lambda n: (n * tau, -n * tau))
    return +r


def _lattice_alpha(j, tau):
    """α_{2j}(τ) (DLMF 20.6.7), shift m − 1/2 + nτ: the n = 0 inner sum is
    Σ_{m∈ℤ}(m−1/2)^{−2j} = 2ζ(2j, 1/2)."""
    j, tau = _lattice_args(j, tau, "latticeAlpha")
    h = mp.mpf(1) / 2
    with mp.workdps(mp.mp.dps + 10):
        r = 2 * mp.zeta(2 * j, h) + _lattice_tail(
            j, tau, lambda n: (n * tau - h, -n * tau - h))
    return +r


def _lattice_beta(j, tau):
    """β_{2j}(τ) (DLMF 20.6.8), shift m − 1/2 + (n − 1/2)τ: the half-integer
    n-shifts pair up as ±(n − 1/2)τ − 1/2 over n ≥ 1 (no n = 0 special case)."""
    j, tau = _lattice_args(j, tau, "latticeBeta")
    h = mp.mpf(1) / 2
    with mp.workdps(mp.mp.dps + 10):
        r = _lattice_tail(j, tau, lambda n: ((n - h) * tau - h, -(n - h) * tau - h))
    return +r


def _lattice_gamma(j, tau):
    """γ_{2j}(τ) (DLMF 20.6.9), shift m + (n − 1/2)τ: pairs ±(n − 1/2)τ over n ≥ 1."""
    j, tau = _lattice_args(j, tau, "latticeGamma")
    h = mp.mpf(1) / 2
    with mp.workdps(mp.mp.dps + 10):
        r = _lattice_tail(j, tau, lambda n: ((n - h) * tau, -(n - h) * tau))
    return +r


_lattice_delta = _lattice_memo("latticeDelta", _lattice_delta)
_lattice_alpha = _lattice_memo("latticeAlpha", _lattice_alpha)
_lattice_beta = _lattice_memo("latticeBeta", _lattice_beta)
_lattice_gamma = _lattice_memo("latticeGamma", _lattice_gamma)


# ── Jacobi elliptic functions on ℂ via theta quotients (M10 / Tier C2) ───────
# FLMF defines the τ-parametrized (NOT modulus-k) Jacobi functions through the same
# theta nulls bound above (DLMF 22.2.4–6):
#   sn z τ = θ₃(0)θ₁(z)/(θ₂(0)θ₄(z)),  cn z τ = θ₄(0)θ₂(z)/(θ₂(0)θ₄(z)),
#   dn z τ = θ₄(0)θ₃(z)/(θ₃(0)θ₄(z)).
# Built from `_theta(j)` (which is anchored equal to the Lean θⱼ), so these are the
# Lean defs evaluated — the strongest §5 tie. Requires Im τ > 0 (else the theta nome
# |q| ≥ 1 and mpmath raises → the sample point drops, never a fabricated value).
def _sn(z, tau):
    return _theta(3)(0, tau) * _theta(1)(z, tau) / (_theta(2)(0, tau) * _theta(4)(z, tau))


def _cn(z, tau):
    return _theta(4)(0, tau) * _theta(2)(z, tau) / (_theta(2)(0, tau) * _theta(4)(z, tau))


def _dn(z, tau):
    return _theta(4)(0, tau) * _theta(3)(z, tau) / (_theta(3)(0, tau) * _theta(4)(z, tau))


# ── cancellation-noise pole guard for the Glaisher quotient denominators ─────
# A quotient denominator sn/cn/dn vanishes exactly where its NUMERATOR theta does
# (sn ↔ θ₁, cn ↔ θ₂, dn ↔ θ₃ — the θ₄(z) factor is shared and never zero with them).
# When a ℂ-grid sample lands ON that zero lattice (e.g. z = τ, a lattice zero of θ₁ —
# the sweep reuses one ℂ grid for both binders of a two-ℂ theta declaration), the
# computed theta is pure floating-point cancellation noise (~1e-60 against series
# terms of size 1…1e20), so the quotient is O(1e60) garbage instead of a true pole:
# both sides of a correct identity then disagree at ~1e-12 and FALSE-FAIL it.
# Guard: compare |θⱼ(z,τ)| against the largest MAGNITUDE of a term of its defining
# series (DLMF 20.2.1–20.2.4) and raise ValueError when it has collapsed below
# 1e-25 of that scale — the sample drops as an honest domain skip, exactly like a
# true pole (mpmath raise). ADDITIVE: values at every non-collapsed point are
# bit-identical to before; nothing is loosened.
_JACOBI_POLE_NOISE = mp.mpf("1e-25")


def _theta_term_scale(j, z, tau):
    """Largest term magnitude of the θⱼ series at (z, τ): 2|q|^{(n+1/2)²}e^{(2n+1)π|Im z|}
    for j = 1, 2 and max(1, 2|q|^{n²}e^{2nπ|Im z|}) for j = 3, 4 (|sin|, |cos| ≤ e^{|Im·|}).
    Unimodal in n (log-concave: |q| < 1), so a short scan with early exit suffices."""
    r = abs(_theta_q(tau))
    b = mp.pi * abs(mp.im(mp.mpmathify(z)))
    best = mp.mpf(0) if j in (1, 2) else mp.mpf(1)
    for n in range(64):
        t = (2 * r ** ((n + mp.mpf(1) / 2) ** 2) * mp.exp((2 * n + 1) * b) if j in (1, 2)
             else 2 * r ** ((n + 1) ** 2) * mp.exp(2 * (n + 1) * b))
        if t > best:
            best = t
        elif t < best * mp.mpf("1e-40"):
            break
    return best


def _pole_guarded(pq, pn, j, fn):
    """Denominator `pn` of the Glaisher quotient `pq`, raising ValueError when the
    theta θⱼ carrying pn's zeros has collapsed to cancellation noise (pole sample)."""
    def _f(z, t):
        if abs(_theta(j)(z, t)) < _JACOBI_POLE_NOISE * _theta_term_scale(j, z, t):
            raise ValueError(
                f"Glaisher {pq}: denominator {pn}(z,τ) at a lattice zero — θ{j} collapsed "
                "to theta-series cancellation noise (pole sample dropped)")
        return fn(z, t)
    return _f


_sn_den = _pole_guarded("·s", "sn", 1, _sn)
_cn_den = _pole_guarded("·c", "cn", 2, _cn)
_dn_den = _pole_guarded("·d", "dn", 3, _dn)


# the nine Glaisher quotients (DLMF 22.2 / FLMF `JacobiGlaisher`): first letter ÷ second,
# with leading `n` denoting the reciprocal (n = 1). Denominators are pole-guarded (above).
_GLAISHER = {
    "ns": lambda z, t: 1 / _sn_den(z, t),  "nc": lambda z, t: 1 / _cn_den(z, t),
    "nd": lambda z, t: 1 / _dn_den(z, t),
    "sc": lambda z, t: _sn(z, t) / _cn_den(z, t),  "sd": lambda z, t: _sn(z, t) / _dn_den(z, t),
    "cd": lambda z, t: _cn(z, t) / _dn_den(z, t),  "cs": lambda z, t: _cn(z, t) / _sn_den(z, t),
    "ds": lambda z, t: _dn(z, t) / _sn_den(z, t),  "dc": lambda z, t: _dn(z, t) / _cn_den(z, t),
}


# ── the MODULUS-parameterized Jacobi functions (JacobiModulusBridge.lean, DLMF §22.2) ──
# FLMF `tauOfModulus k = i·K(√(1−k²))/K(k)` (DLMF 22.2.12, `FLMF.JacobiElliptic.completeK`
# = `_complete_k`, the MODULUS-argument K) and `snk z k = sn z (tauOfModulus k)`,
# `cnk`/`dnk` likewise — the τ-parametrized theta quotients above, evaluated at that τ.
# Transcribed from the Lean defs, so this is again the Lean definition evaluated.
# DOMAIN: `Im τ > 0` needs `0 < |k| < 1` (k = 0 sends K′ → ∞, |k| ≥ 1 leaves completeK's
# real domain); outside it we raise and the sample point drops as an honest domain skip.
def _tau_of_modulus(k):
    """FLMF `FLMF.Theta.tauOfModulus k` = i·K(√(1−k²))/K(k) (DLMF 22.2.12)."""
    k = mp.mpmathify(k)
    if mp.im(k) != 0:
        raise ValueError("tauOfModulus: modulus is real (ℝ binder)")
    kr = mp.re(k)
    if not (0 < abs(kr) < 1):
        raise ValueError("tauOfModulus: |k| ∉ (0,1) — K′/K leaves the upper half-plane")
    return mp.mpc(0, 1) * (_complete_k(mp.sqrt(1 - kr ** 2)) / _complete_k(kr))


def _snk(z, k):
    """FLMF `snk z k = sn z (tauOfModulus k)` (DLMF 22.2.4, modulus form)."""
    return _sn(z, _tau_of_modulus(k))


def _cnk(z, k):
    """FLMF `cnk z k = cn z (tauOfModulus k)` (DLMF 22.2.5, modulus form)."""
    return _cn(z, _tau_of_modulus(k))


def _dnk(z, k):
    """FLMF `dnk z k = dn z (tauOfModulus k)` (DLMF 22.2.6, modulus form)."""
    return _dn(z, _tau_of_modulus(k))


def _gudermannian(x):
    """FLMF `gd x` — the Gudermannian (DLMF 4.23.39): gd x = 2·arctan(tanh(x/2)),
    pinned by sin(gd x) = tanh x and cos(gd x) = sech x."""
    return 2 * mp.atan(mp.tanh(x / 2))


# ── number-theory characters + Jacobi symbol (M14, DLMF 27.9) ────────────────
def _jacobi_sym(a, n):
    """FLMF/Mathlib `jacobiSym a n` = J(a | n) (DLMF 27.9): Legendre-symbol product over
    n's prime factors; defined for n a POSITIVE ODD integer. sympy.jacobi_symbol is the
    independent implementation and RAISES on even/nonpositive n → honest sample drop."""
    ai, ni = int(a), int(n)
    if ai != a or ni != n:
        raise ValueError(f"jacobiSym: non-integer args ({a}, {n})")
    return mp.mpf(int(_sympy.jacobi_symbol(ai, ni)))


def _legendre_sym(p, a):
    """FLMF/Mathlib `legendreSym p a` = (a | p) (DLMF 27.9): +1 if a is a nonzero
    quadratic residue mod the odd prime p, −1 if a nonresidue, 0 if p | a — i.e.
    ≡ a^((p−1)/2) (mod p) by Euler's criterion. NOTE the argument order: Mathlib puts
    the PRIME MODULUS first, sympy.legendre_symbol takes (a, p). sympy is the
    independent implementation and RAISES on non-odd-prime p → honest sample drop."""
    pi, ai = int(p), int(a)
    if pi != p or ai != a:
        raise ValueError(f"legendreSym: non-integer args ({p}, {a})")
    return mp.mpf(int(_sympy.legendre_symbol(ai, pi)))


def zmod_is_square(e, n):
    """Decidable `IsSquare (e : ZMod n)` (Mathlib: ∃ r, e = r * r in `ZMod n`) — decided
    by BRUTE FORCE straight from the definition: ∃ x ∈ [0, n), x·x ≡ e (mod n).
    Deliberately DECORRELATED from the Legendre/Euler-criterion machinery bound above
    (no sympy, no quadratic-reciprocity theory), so an '↔' surface pitting `IsSquare`
    against residue-class arithmetic (DLMF 27.9 first supplement) is a genuine
    two-implementation check; verify() anchors it against sympy.legendre_symbol on odd
    primes and against the exact square sets mod 7/8. Works for ANY modulus n ≥ 1
    (composite included); `ZMod 0 = ℤ` is not brute-forceable and non-integer args are
    ill-posed — both raise → honest sample drop, never a fabricated verdict."""
    ei, ni = int(e), int(n)
    if ei != e or ni != n:
        raise ValueError(f"zmod_is_square: non-integer args ({e}, {n})")
    if ni <= 0:
        raise ValueError(f"zmod_is_square: modulus must be a positive integer ({n})")
    r = ei % ni
    return any((x * x) % ni == r for x in range(ni))


def _chi4(n):
    """mod-4 real Dirichlet character χ₄ (Mathlib `ZMod.χ₄`): 0 if n even, +1 if n≡1,
    −1 if n≡3 (mod 4) — the J(−1|n) supplementary law."""
    r = int(n) % 4
    return mp.mpf(0) if r % 2 == 0 else (mp.mpf(1) if r == 1 else mp.mpf(-1))


def _chi8(n):
    """mod-8 real Dirichlet character χ₈ (Mathlib `ZMod.χ₈`): 0 if n even, +1 if n≡±1,
    −1 if n≡±3 (mod 8) — the J(2|n) supplementary law."""
    r = int(n) % 8
    if r % 2 == 0:
        return mp.mpf(0)
    return mp.mpf(1) if r in (1, 7) else mp.mpf(-1)


def _completed_riemann_zeta(s):
    """Mathlib `completedRiemannZeta s` = the SYMMETRIC completed zeta Λ(s) = π^(−s/2)·
    Γ(s/2)·ζ(s) satisfying Λ(1−s)=Λ(s). The 1/s+1/(1−s) pole terms live in the auxiliary
    `completedRiemannZeta₀`, NOT here (verified against Mathlib source).

    Mathlib totalizes the poles at 0 and 1 to the same finite placeholder.  Away
    from them, evaluate in the right half-plane via Λ(1-s)=Λ(s); this also preserves
    the Gamma-zeta cancellations at negative even integers instead of asking mpmath
    to multiply an infinity by a zero."""
    s = mp.mpmathify(s)
    if s == 0 or s == 1:
        return (mp.euler - mp.log(4 * mp.pi)) / 2
    if mp.re(s) < mp.mpf("0.5"):
        s = 1 - s
    return mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def _riemann_zeta_mathlib(s):
    """Mathlib's total `riemannZeta : ℂ → ℂ`.

    It is the standard meromorphic zeta away from 1, while at the mathematical
    pole Mathlib assigns `(γ - log(4π))/2`.  Mirroring that point is essential
    when a Lean statement literally includes s = 1."""
    s = mp.mpmathify(s)
    if s == 1:
        return (mp.euler - mp.log(4 * mp.pi)) / 2
    return mp.zeta(s)


def _theta4_mellin_continuation(s):
    """The split regularized Mellin transform used by `theta4MellinContinuation`.

    This evaluates the defining two integrals directly, independently of the
    completed-zeta closed form being checked.  For x < 1 the Jacobi imaginary
    transformation evaluates θ₄(0|ix²) as x⁻¹ θ₂(0|i/x²), avoiding the q→1 wall."""
    s = mp.mpmathify(s)

    def theta4_null(x):
        x = mp.mpf(x)
        if x <= 0:
            return mp.mpf(0)
        if x < 1:
            # θ₂(0|i/x²) = 2 Σ_{n≥0} exp(-π(n+1/2)²/x²).  Summing this
            # rapidly convergent transformed series directly also handles the
            # x→0 endpoint, where constructing its underflowed nome can make
            # mpmath's jtheta attempt an invalid giant fixed-point shift.
            a = mp.pi / (x * x)
            if a / 4 > (mp.mp.dps + 10) * mp.log(10):
                return mp.mpf(0)
            total = mp.mpf(0)
            for n in range(100):
                term = mp.exp(-a * (n + mp.mpf("0.5")) ** 2)
                total += term
                if term < mp.eps * max(mp.mpf(1), total):
                    break
            return 2 * total / x
        # θ₄(0|ix²) = 1 + 2 Σ_{n≥1} (-1)ⁿ exp(-πn²x²).
        # This direct large-x series avoids feeding an exactly underflowed nome
        # to jtheta at the infinite-ray quadrature nodes.
        a = mp.pi * x * x
        if a > (mp.mp.dps + 10) * mp.log(10):
            return mp.mpf(1)
        total = mp.mpf(1)
        for n in range(1, 100):
            term = 2 * (-1) ** n * mp.exp(-a * n * n)
            total += term
            if abs(term) < mp.eps * max(mp.mpf(1), abs(total)):
                break
        return total

    def low(x):
        if x == 0:
            return mp.mpc(0)
        return mp.power(x, s - 1) * (-theta4_null(x))

    def high(x):
        return mp.power(x, s - 1) * (1 - theta4_null(x))

    with mp.workdps(2 * mp.mp.dps):
        lo = mp.quad(low, [0, mp.mpf("0.2"), mp.mpf("0.5"), 1])
        hi = mp.quad(high, [1, 2, mp.inf])
        return +(1 / s + lo + hi)


# ── Dedekind η / modular forms (M14, τ-parametrized; DLMF 23) ─────────────────
def _eta(z):
    """Mathlib/FLMF `ModularForm.eta z = e^{πiz/12}·∏ₙ(1−e^{2πi(n+1)z})` (eta_eq_qpow_tprod);
    nome q=e^{2πiz}. Requires Im z>0 else |q|≥1 and the q-Pochhammer diverges → honest drop."""
    q = mp.exp(2 * mp.pi * mp.mpc(0, 1) * z)
    if abs(q) >= 1:
        raise ValueError("eta: Im z ≤ 0 (nome |q| ≥ 1, product diverges)")
    return mp.exp(mp.pi * mp.mpc(0, 1) * z / 12) * mp.qp(q)


def _eta_factor(tau):
    """FLMF `etaFactor τ = (Complex.sqrt I)⁻¹·Complex.sqrt τ` — the η S-transform prefactor
    √(−iτ), principal branch (DedekindEtaTransform.lean)."""
    return mp.sqrt(mp.mpc(0, 1)) ** (-1) * mp.sqrt(tau)


def _modform_discriminant(z):
    """Mathlib `ModularForm.discriminant z = (ModularForm.eta z)^24` (discriminant_eq_eta_pow)
    — Δ WITHOUT the (2π)^12 factor (leading q-coefficient 1)."""
    return _eta(z) ** 24


# SL(2,ℤ) generators (Mathlib `ModularGroup.T`/`ModularGroup.S`) as ((a,b),(c,d)) row
# tuples: T = [[1,1],[0,1]] (τ ↦ τ+1), S = [[0,-1],[1,0]] (τ ↦ −1/τ) — DLMF §23.15(i).
MODULAR_T = ((1, 1), (0, 1))
MODULAR_S = ((0, -1), (1, 0))


def _slash_action(k, gamma, f, tau):
    """Mathlib `SlashAction.map k γ f` for γ = ((a,b),(c,d)) ∈ SL(2,ℤ): the weight-k slash
    `(f ∣[k] γ)(τ) = (cτ+d)^{−k} · f((aτ+b)/(cτ+d))` — the DLMF 23.15 automorphy factor for
    the modular transformation τ ↦ (aτ+b)/(cτ+d). `f` is a callable on ℍ; `gamma` one of
    the MODULAR_T/MODULAR_S tuples (Mathlib's extra det^{k−1} factor is 1 on SL(2,ℤ))."""
    (a, b), (c, d) = gamma
    return (c * tau + d) ** (-int(k)) * f((a * tau + b) / (c * tau + d))


def _qparam(h, z):
    """Mathlib `Function.Periodic.qParam h z = exp(2πiz/h)` (the nome of period h)."""
    return mp.exp(2 * mp.pi * mp.mpc(0, 1) * z / h)


def _eisenstein_E2(z):
    """Eisenstein E₂(z) = 1 − 24·∑ σ₁(n)qⁿ (q=e^{2πiz}); the logarithmic derivative of η
    (logDeriv η = (πi/12)·E₂). Requires Im z > 0."""
    q = mp.exp(2 * mp.pi * mp.mpc(0, 1) * z)
    if abs(q) >= 1:
        raise ValueError("E2: Im z ≤ 0")
    s = mp.mpf(0)
    for n in range(1, 200):
        term = sum(d for d in range(1, n + 1) if n % d == 0) * q ** n
        s += term
        if abs(term) < mp.mpf("1e-30"):
            break
    return 1 - 24 * s


def _eisenstein_E4(z):
    """Normalized MODULAR Eisenstein E₄(τ) : ℍ → ℂ (Mathlib `EisensteinSeries.E (k:=4)`;
    FLMF.Eisenstein.E₄, EisensteinModular.lean). Defining lattice sum: E₄ = G₄/(2ζ(4)) with
    G₄(τ) = ∑'_{(m,n)≠(0,0)} (mτ+n)⁻⁴ (DLMF §23.9 invariant normalized to constant term 1).
    Computed via the theta-null g₂ (g₂ = 60·G₄ on ℤ+τℤ, 2ζ(4) = π⁴/45 ⇒ E₄ = 3g₂/(4π⁴)),
    so it stays DECORRELATED from the σ₃ q-expansion it is tested against. NOT the
    Weierstrass lattice-rescaled `E₄ L = g₂(L)/12` (`_wE4`) — that one takes a lattice
    argument and is dispatched through `_LARG` before this binding is reached."""
    if mp.im(z) <= 0:
        raise ValueError("E4: Im z ≤ 0")
    return 3 * _g2(_Lattice(1, z)) / (4 * mp.pi ** 4)


def _eisenstein_E6(z):
    """Normalized MODULAR Eisenstein E₆(τ) = G₆/(2ζ(6)), G₆(τ) = ∑'_{(m,n)≠(0,0)} (mτ+n)⁻⁶
    (Mathlib `EisensteinSeries.E (k:=6)`; FLMF.Eisenstein.E₆). Via the theta-null g₃
    (g₃ = 140·G₆, 2ζ(6) = 2π⁶/945 ⇒ E₆ = 27g₃/(8π⁶)) — decorrelated from the σ₅
    q-expansion. NOT the Weierstrass lattice-rescaled `E₆ L = g₃(L)/8` (`_wE6`)."""
    if mp.im(z) <= 0:
        raise ValueError("E6: Im z ≤ 0")
    return 27 * _g3(_Lattice(1, z)) / (8 * mp.pi ** 6)


# ── per-function specials (M14, Tier C2 tail) ────────────────────────────────
def _binet(z):
    """FLMF `binet z = logΓ z − ((z−1/2)log z − z + ½log 2π)` (the logΓ remainder, DLMF 5.11;
    Binet.lean). Real.log = log|·| (_rlog)."""
    return (_rlog(mp.gamma(z))
            - ((z - mp.mpf(1) / 2) * _rlog(z) - z + (mp.mpf(1) / 2) * _rlog(2 * mp.pi)))


# ── DLMF §5.10/5.11 Gamma asymptotic-coefficient tables (N1 group) ──────────
# Three abstract coefficient sequences pinned by a DEFINING recurrence / asymptotic
# relation, plus the Binet continued-fraction numerator table, each synthesized here
# from its DEFINING DLMF formula — DECORRELATED from the claimed Lean literals so a
# fidelity check is a genuine refutation oracle. Anchored in verify() before trusted.

def _stirling_seq_a(N):
    """The auxiliary sequence `aₖ` of the DLMF 5.11.5/5.11.6 Stirling recurrence
    (FLMF `SatisfiesStirlingRec`): a₀ = 1/√2, and for k ≥ 1
        Σ_{j=0}^{k} aⱼ a_{k−j}/(j+1) = a_{k−1}/k .
    aₖ occurs in that sum at j=0 (a₀aₖ/1) and j=k (aₖa₀/(k+1)), so its coefficient
    is a₀·(1 + 1/(k+1)); everything else is already known, giving a forward solve.
    This IS the defining recurrence of the hypothesis binder — no closed form used."""
    a = [None] * (N + 1)
    a[0] = 1 / mp.sqrt(2)
    for k in range(1, N + 1):
        known = mp.mpf(0)
        for j in range(1, k):
            known += a[j] * a[k - j] / (j + 1)
        coeff = a[0] * (1 + mp.mpf(1) / (k + 1))
        a[k] = (a[k - 1] / k - known) / coeff
    return a


def _asc_pochhammer_half(k):
    """(1/2)ₖ = ∏_{i=0}^{k−1}(1/2 + i) = (ascPochhammer ℝ k).eval (1/2)."""
    p = mp.mpf(1)
    for i in range(k):
        p *= mp.mpf(1) / 2 + i
    return p


def _stirling_g(k):
    """Stirling asymptotic coefficient `gₖ` (DLMF 5.11.4/5.11.6, FLMF
    `SatisfiesStirlingRec` conclusion): gₖ = √2 · (1/2)ₖ · a_{2k}, with aₖ from
    `_stirling_seq_a`. Independent of the claimed literals g₀=1, g₁=1/12, …:
    they are read back OUT of the recurrence, never fed in. Anchored in verify()."""
    k = _nat(k, "stirlingRecG")
    a = _stirling_seq_a(2 * k)
    return mp.sqrt(2) * _asc_pochhammer_half(k) * a[2 * k]


def _stirling_seq_a_witness(k):
    """The auxiliary aₖ itself, as the second `SatisfiesStirlingRec` witness head
    (the conclusion of 5.11.4 uses only `g`, but the hypothesis binds both a, g)."""
    k = _nat(k, "stirlingRecA")
    return _stirling_seq_a(k)[k]


def _ratio_coeff_G(n, a, b):
    """Coefficient `Gₙ(a,b)` of the unsymmetrized Gamma-ratio expansion
        Γ(x+a)/Γ(x+b) ∼ x^{a−b} Σ_k Gₖ(a,b) x^{−k}   (DLMF 5.11.13; FLMF `IsRatioCoeffs`).
    Derived from the DEFINING relation by exponentiating the log expansion:
        log[Γ(x+a)/Γ(x+b)] − (a−b)log x = Σ_{n≥1} cₙ x^{−n},
        cₙ = (−1)^{n+1} (B_{n+1}(a) − B_{n+1}(b)) / (n(n+1))   (ordinary Bernoulli poly),
    so G(t)=exp(Σ cₙ tⁿ) with G₀=1 and the exp recurrence k·Gₖ = Σ_{j≥1} j cⱼ G_{k−j}.
    Uses mp.bernpoly — no reference to the claimed 5.11.15 polynomials. Anchored in verify()."""
    n = _nat(n, "ratioCoeffG")
    if n == 0:
        return mp.mpf(1)
    c = [mp.mpf(0)] * (n + 1)
    for m in range(1, n + 1):
        c[m] = (-1) ** (m + 1) * (mp.bernpoly(m + 1, a) - mp.bernpoly(m + 1, b)) / (m * (m + 1))
    G = [mp.mpf(0)] * (n + 1)
    G[0] = mp.mpf(1)
    for k in range(1, n + 1):
        s = mp.mpf(0)
        for j in range(1, k + 1):
            s += j * c[j] * G[k - j]
        G[k] = s / k
    return G[n]


def _sym_ratio_coeff_H(k, a, b):
    """Coefficient `Hₖ(a,b)` of the SYMMETRIZED Gamma-ratio expansion
        Γ(x+a)/Γ(x+b) ∼ (x+½(a+b−1))^{a−b} Σ_k Hₖ(a,b) (x+½(a+b−1))^{−2k}
    (DLMF 5.11.14; FLMF `IsSymRatioCoeffs`). Recentring u = x+½(a+b−1) turns the
    ratio into Γ(u+α)/Γ(u+β) with α=(a−b+1)/2, β=(1−(a−b))/2 (so α+β=1); for such a
    balanced pair the odd unsymmetrized coefficients vanish, leaving Hₖ = G_{2k}(α,β).
    Independent of the claimed 5.11.16 polynomials. Anchored in verify()."""
    k = _nat(k, "symRatioCoeffH")
    d = a - b
    alpha = (d + 1) / 2
    beta = (1 - d) / 2
    return _ratio_coeff_G(2 * k, alpha, beta)


def _ps_reciprocal(a, K):
    """Coefficient list of 1/A to order K, for a power series A (list, A[0] ≠ 0)."""
    b = [mp.mpf(0)] * (K + 1)
    b[0] = 1 / a[0]
    for n in range(1, K + 1):
        s = mp.mpf(0)
        for k in range(1, n + 1):
            ak = a[k] if k < len(a) else mp.mpf(0)
            s += ak * b[n - k]
        b[n] = -s / a[0]
    return b


def _binet_cf_num(n):
    """Binet continued-fraction partial numerator `aₙ` (DLMF 5.10.2; FLMF
    `binetCFNum`).  DLMF 5.10.1 writes the Binet/Stirling function as the S-fraction
        μ(z) = a₀/(z + a₁/(z + a₂/(z + ⋯))),
    equivalently, with w = 1/z,  μ = a₀ w /(1 + a₁ w²/(1 + a₂ w²/(1 + ⋯))).
    μ has the DEFINING asymptotic series (DLMF 5.11.1) μ(z) ∼ Σ_{m≥1}
    B_{2m}/((2m−1)(2m)) z^{1−2m}, so the aₙ are extracted from that series by the
    reciprocal-difference recursion (T₀ = μ/w; aᵢ = Tᵢ(0); T_{i+1} = (aᵢ/Tᵢ − 1)/w²).
    Computed from the Bernoulli numbers alone — DECORRELATED from the claimed
    rational table. Anchored in verify() by rebuilding the CF and matching μ(z)."""
    n = _nat(n, "binetCFNum")
    K = 2 * n + 10
    T = [mp.mpf(0)] * (K + 1)          # T = μ/w as a series in w
    for m in range(1, (K + 4) // 2 + 1):
        idx = 2 * m - 2                # coeff of w^{2m-1} in μ → w^{2m-2} in μ/w
        if 0 <= idx <= K:
            T[idx] = mp.bernoulli(2 * m) / ((2 * m - 1) * (2 * m))
    aout = mp.mpf(0)
    for i in range(n + 1):
        ai = T[0]
        aout = ai
        rt = _ps_reciprocal(T, K)
        q = [ai * rt[j] for j in range(K + 1)]
        q[0] = q[0] - 1               # ≈ 0 (constant term of aᵢ/T)
        T = q[2:] + [mp.mpf(0), mp.mpf(0)]   # divide by w² (shift down 2)
        K -= 2
    return aout


def _binet_cf_eval(az, z):
    """Evaluate the DLMF 5.10.1 continued fraction a₀/(z+a₁/(z+a₂/(z+⋯))) from a
    finite numerator list — the verify() anchor tying `binetCFNum` back to μ(z)."""
    acc = mp.mpf(0)
    for a in reversed(az[1:]):
        acc = a / (z + acc)
    return az[0] / (z + acc)


def _besselK_amplitude(nu, t):
    """FLMF `besselKAmplitude ν t = (1 + t/2)^(ν − 1/2)` (rpow; Bessel/KSeries.lean)."""
    return (1 + t / 2) ** (nu - mp.mpf(1) / 2)


def _expint_n(n, x):
    """FLMF `Eₙ n x` = the GENERALIZED exponential integral Eₙ(x) = ∫₁^∞ e^{−xt}/tⁿ dt
    (EnLeading.lean) = mp.expint(n, x). NOT E₁ — the n index is honored."""
    return mp.expint(int(n), x)


def _upper_gamma_watson(a, x):
    """FLMF `upperGammaWatson a x` = upper incomplete Γ(a,x) = ∫ₓ^∞ e^{−t}t^{a−1}dt
    (UpperLeading.lean) = mp.gammainc(a, x, ∞)."""
    return mp.gammainc(a, x, mp.inf)


def _li_w(x):
    """FLMF `liW x = e^{log x}·∫₀^∞ e^{−(log x)u}/(1+u) du` (LiLeading.lean). Converges only
    for log x > 0 (x > 1); else mpmath raises → honest drop."""
    L = _rlog(x)
    return mp.e ** L * mp.quad(lambda u: mp.e ** (-L * u) * (1 / (1 + u)), [0, mp.inf])


def _ci_tail(x, b):
    """FLMF `ciTail x b = ∫ₓ^b cos t/t dt = Ci(b) − Ci(x)` (CiLeading.lean)."""
    return mp.ci(b) - mp.ci(x)


def _airy_g(z):
    """FLMF `airyG z` = the vertical-contour analytic continuation of Ai (airyG_ofReal:
    G(x)=Ai(x) on ℝ ⇒ G ≡ Ai entire; Airy/Connection.lean) = mp.airyai(z). NOT a Scorer fn."""
    return mp.airyai(z)


def _airy_bi(x):
    """FLMF `airyBi x = e^{iπ/6}·airyG(x·e^{2πi/3}) + e^{−iπ/6}·airyG(x·e^{−2πi/3})`
    (DLMF 9.2.10) — reproduces the standard real Bi."""
    i = mp.mpc(0, 1)
    return (mp.e ** (i * (mp.pi / 6)) * _airy_g(x * mp.e ** (i * (2 * mp.pi / 3)))
            + mp.e ** (-(i * (mp.pi / 6))) * _airy_g(x * mp.e ** (-(i * (2 * mp.pi / 3)))))


# ── Weierstrass elliptic functions on a lattice (M15, DLMF 23) ───────────────
# Lattice = Mathlib `PeriodPair` with full periods (ω₁, ω₂), `lattice = ℤω₁+ℤω₂`. FLMF:
# `g₂ = 60·G 4`, `g₃ = 140·G 6` (G n = ∑'_{l≠0} l⁻ⁿ); `℘` via θ₁; half-periods e₁=℘(ω₁/2),
# e₂=℘((ω₁+ω₂)/2), e₃=℘(ω₂/2); discriminant = g₂³−27g₃²; kleinJ = g₂³/Δ. mpmath has no ℘,
# so it is constructed from θ₁ and cross-checked against the lattice Eisenstein sums.
class _Lattice:
    __slots__ = ("w1", "w2")

    def __init__(self, w1, w2):
        self.w1 = mp.mpc(w1)
        self.w2 = mp.mpc(w2)

    def smul(self, lam):
        return _Lattice(lam * self.w1, lam * self.w2)

    def _q(self):
        return mp.exp(mp.mpc(0, 1) * mp.pi * (self.w2 / self.w1))


# τ=i (lemniscatic, g₃=0 — the distinguishing degeneracy) + two generic Im τ>0 lattices.
SAMPLE_LATTICES = [_Lattice(1, mp.mpc(0, 1)),
                   _Lattice(1, mp.mpc("0.3", "1.1")),
                   _Lattice(mp.mpc("1.0", "0.2"), mp.mpc("0.4", "1.3"))]


def _wp(L, z):
    """℘(z; L) via θ₁ (DLMF 23.6): ℘(z) = −(π/ω₁)²[(log θ₁)''(v) − θ₁'''(0)/(3θ₁'(0))],
    v = πz/ω₁. Anchored by the differential equation ℘'² = 4℘³ − g₂℘ − g₃."""
    q, v, fac = L._q(), mp.pi * z / L.w1, (mp.pi / L.w1) ** 2
    d2 = mp.diff(lambda t: mp.log(mp.jtheta(1, t, q)), v, 2)
    c = mp.jtheta(1, 0, q, 3) / (3 * mp.jtheta(1, 0, q, 1))
    return -fac * (d2 - c)


def _wp_deriv(L, z):
    return mp.diff(lambda t: _wp(L, t), z)


def _g2(L):
    q = L._q(); t2, t3, t4 = mp.jtheta(2, 0, q), mp.jtheta(3, 0, q), mp.jtheta(4, 0, q)
    return (mp.pi / L.w1) ** 4 * (mp.mpf(2) / 3) * (t2 ** 8 + t3 ** 8 + t4 ** 8)


def _g3(L):
    q = L._q(); t2, t3, t4 = mp.jtheta(2, 0, q), mp.jtheta(3, 0, q), mp.jtheta(4, 0, q)
    return (mp.pi / L.w1) ** 6 * (mp.mpf(4) / 27) * (t2 ** 4 + t3 ** 4) * (t3 ** 4 + t4 ** 4) * (t4 ** 4 - t2 ** 4)


def _G_eisenstein(L, n):
    """Lattice Eisenstein series G n = ∑'_{l≠0} l⁻ⁿ; g₂=60·G₄, g₃=140·G₆ give the fast path."""
    n = int(n)
    if n == 4:
        return _g2(L) / 60
    if n == 6:
        return _g3(L) / 140
    if n % 2 == 1:
        return mp.mpf(0)
    s, N = mp.mpf(0), 90
    for m in range(-N, N + 1):
        for k in range(-N, N + 1):
            if m == 0 and k == 0:
                continue
            s += (m * L.w1 + k * L.w2) ** (-n)
    return s


def _wdisc(L):
    return _g2(L) ** 3 - 27 * _g3(L) ** 2


def _e1(L): return _wp(L, L.w1 / 2)
def _e2(L): return _wp(L, (L.w1 + L.w2) / 2)
def _e3(L): return _wp(L, L.w2 / 2)
def _wE4(L): return _g2(L) / 12          # FLMF rescaled E₄ := g₂/12 (NOT modular E₄(τ))
def _wE6(L): return _g3(L) / 8           # FLMF rescaled E₆ := g₃/8
def _kleinJ(L): return _g2(L) ** 3 / _wdisc(L)
def _modular_invariant(L): return 1728 * _g2(L) ** 3 / _wdisc(L)


def _wsigma(L, z):
    """Weierstrass σ via θ₁, with η₁ fixed so that ℘ = −(log σ)''."""
    q = L._q(); t1p, t1ppp = mp.jtheta(1, 0, q, 1), mp.jtheta(1, 0, q, 3)
    eta1 = -(mp.pi / L.w1) ** 2 * (t1ppp / t1p) / 3
    v = mp.pi * z / L.w1
    return mp.exp(eta1 * z ** 2 / 2) * (L.w1 / mp.pi) * mp.jtheta(1, v, q) / t1p


def _wzeta(L, z):
    return mp.diff(lambda t: _wsigma(L, t), z) / _wsigma(L, z)


# ── angular-momentum helper coefficients (M12 / Tier C2, DLMF 34.2) ──────────
# FLMF `ifact n = n! for n ≥ 0, else 0` (the integer factorial with a junk-0 on negatives,
# so out-of-triangle terms vanish). triangleCoeffSq / magneticFactor are the elementary
# factorial products underneath the 3j symbol — exact integer/rational arithmetic.
def _ifact(n):
    import math
    n = int(n)
    return mp.mpf(math.factorial(n)) if n >= 0 else mp.mpf(0)


def _triangle_coeff_sq(j1, j2, j3):
    """Δ²(j₁j₂j₃) = (j₁+j₂−j₃)!(j₁−j₂+j₃)!(−j₁+j₂+j₃)! / (j₁+j₂+j₃+1)!  (DLMF 34.2.2)."""
    return (_ifact(j1 + j2 - j3) * _ifact(j1 - j2 + j3) * _ifact(-j1 + j2 + j3)
            / _ifact(j1 + j2 + j3 + 1))


def _magnetic_factor(j1, j2, j3, m1, m2, m3):
    """(j₁+m₁)!(j₁−m₁)!(j₂+m₂)!(j₂−m₂)!(j₃+m₃)!(j₃−m₃)! — the product under the 3j √."""
    return (_ifact(j1 + m1) * _ifact(j1 - m1) * _ifact(j2 + m2) * _ifact(j2 - m2)
            * _ifact(j3 + m3) * _ifact(j3 - m3))


def _triangle_coeff(j1, j2, j3):
    """Δ(j₁j₂j₃) = √(Δ²) — the triangle coefficient (DLMF 34.2.2)."""
    return mp.sqrt(_triangle_coeff_sq(j1, j2, j3))


def _racah_term(j1, j2, j3, m1, m2, k):
    """FLMF `racahTerm j₁ j₂ j₃ m₁ m₂ k` — a single Racah summand (DLMF 34.2.4):
    (−1)^k / [k!(j₁+j₂−j₃−k)!(j₁−m₁−k)!(j₂+m₂−k)!(j₃−j₂+m₁+k)!(j₃−j₁−m₂+k)!].
    NOTE the Lean phase is `(-1)^k.toNat`, which is faithful here since `k ≥ 0` on the
    summation range (unlike the buggy `wigner3j`/`clebschGordan` phases — see the
    `wigner3j-tonat-phase` ERRATA entry). `ifact` junk-0's any negative factorial
    argument, so terms outside the true support vanish automatically; mirrored here via
    `_ifact`."""
    k = int(k)
    denom = (_ifact(k) * _ifact(j1 + j2 - j3 - k) * _ifact(j1 - m1 - k)
             * _ifact(j2 + m2 - k) * _ifact(j3 - j2 + m1 + k) * _ifact(j3 - j1 - m2 + k))
    if denom == 0:
        return mp.mpf(0)
    return mp.mpf((-1) ** k) / denom


def _racah_sum(j1, j2, j3, m1, m2):
    """FLMF `racahSum j₁ j₂ j₃ m₁ m₂` — the Racah summation (DLMF 34.2.4), summed over
    `k ∈ [0, j₁+j₂−j₃]` (the Lean `Finset.Icc` range; terms outside it vanish via `ifact`
    junk-0, so this finite range captures the full sum, matching `racahSum` exactly)."""
    j1, j2, j3 = int(j1), int(j2), int(j3)
    s = mp.mpf(0)
    for k in range(0, j1 + j2 - j3 + 1):
        s += _racah_term(j1, j2, j3, m1, m2, k)
    return s


def _wigner6j_orth_sum(j1, j2, j4, j5, j6, j6p):
    """∑_x (2x+1)·{j₁ j₂ x; j₄ j₅ j₆}{j₁ j₂ x; j₄ j₅ j₆'} (DLMF 34.4.x orthogonality) =
    δ(j₆,j₆')/(2j₆+1). Built from the bound 6j; sympy only."""
    s = mp.mpf(0)
    for x in range(0, int(j1 + j2 + j4 + j5) + 1):
        s += (2 * x + 1) * _sym(_sy_6j(int(j1), int(j2), x, int(j4), int(j5), int(j6))) \
                         * _sym(_sy_6j(int(j1), int(j2), x, int(j4), int(j5), int(j6p)))
    return s


# ── M18 tail: 9j / triangle6j / Biedenharn–Elliott / 3j-orthogonality (Agent Y) ──
def _triangle6j(a, b, c):
    """FLMF `triangle6j a b c` = Δ²(a b c) (DLMF 34.2.2) = `triangleCoeffSq` (same ifact product);
    triangle6j 0 0 0 = 1."""
    return _triangle_coeff_sq(a, b, c)


def _wigner9j(j11, j12, j13, j21, j22, j23, j31, j32, j33):
    """FLMF `wigner9j` (DLMF 34.6) — verified equal to sympy's wigner_9j in identical row-major
    argument order; anchored at wigner_9j(1,1,2,1,1,2,2,2,2) = −1/150."""
    return _sym(_sy_9j(int(j11), int(j12), int(j13), int(j21), int(j22), int(j23),
                       int(j31), int(j32), int(j33)))


def _wigner9j_term(j11, j12, j13, j21, j22, j23, j31, j32, j33, x):
    """FLMF `wigner9jTerm … x` = (−1)^{2x}(2x+1)·(three 6j factors) in the DLMF 34.6.2 ordering."""
    x = int(x)
    return (mp.mpf((-1) ** (2 * x)) * (2 * x + 1)
            * _sym(_sy_6j(int(j11), int(j21), int(j31), int(j32), int(j33), x))
            * _sym(_sy_6j(int(j12), int(j22), int(j32), int(j21), x, int(j23)))
            * _sym(_sy_6j(int(j13), int(j23), int(j33), x, int(j11), int(j12))))


def _wigner9j_orth_sum(j11, j12, j21, j22, j33, j31, j32, j31p, j32p, N):
    """FLMF `wigner9jOrthSum` (DLMF 34.6.4) — double sum over the two third-column inner labels;
    symmetric under swapping the two outer third-column pairs."""
    N = int(N); s = mp.mpf(0)
    for j13 in range(0, N + 1):
        for j23 in range(0, N + 1):
            s += ((2 * j13 + 1) * (2 * j23 + 1)
                  * _wigner9j(j11, j12, j13, j21, j22, j23, j31, j32, j33)
                  * _wigner9j(j11, j12, j13, j21, j22, j23, j31p, j32p, j33))
    return s


def _biedenharn_elliott_sum(j1, j2, j3, j4, j5, j6, j7, j8, j9):
    """FLMF `biedenharnElliottSum` (DLMF 34.4.4) — ∑_x (−1)^{S+x}(2x+1)·(three 6j); Lean phase is
    `(S+x).toNat`, mirrored as a clamp (only the all-zero degenerate rows are bound, S+x = x ≥ 0)."""
    hi = int(j1 + j2 + j3 + j4 + j5 + j6 + j7 + j8 + j9); s = mp.mpf(0)
    for x in range(0, hi + 1):
        ph = max(0, int(j1 + j2 + j3 + j4 + j5 + j6 + j7 + j8 + j9 + x))
        s += (mp.mpf((-1) ** ph) * (2 * x + 1)
              * _sym(_sy_6j(int(j1), int(j2), x, int(j4), int(j5), int(j6)))
              * _sym(_sy_6j(int(j2), int(j3), x, int(j5), int(j6), int(j7)))
              * _sym(_sy_6j(int(j3), int(j1), x, int(j6), int(j4), int(j9))))
    return s


def _orth_sum(j1, j2, j3, j3p, m3, m3p):
    """FLMF `orthSum` (DLMF 34.3.18) — ∑_{m₁,m₂} (2j₃+1)·3j(…m₃)·3j(…m₃'); vanishes when m₃≠m₃'."""
    j1, j2 = int(j1), int(j2); s = mp.mpf(0)
    for m1 in range(-j1, j1 + 1):
        for m2 in range(-j2, j2 + 1):
            s += (2 * int(j3) + 1) * _sym(_sy_3j(j1, j2, int(j3), m1, m2, int(m3))) \
                                   * _sym(_sy_3j(j1, j2, int(j3p), m1, m2, int(m3p)))
    return s


# ── M16 tail: Tricomi U / confluent-hyp + Gamma helpers (Agent A) ────────────
def _tricomiU(a, b, z):
    """FLMF `tricomiU a b z` = U(a;b;z) (DLMF 13.4.4) = mp.hyperu. Junk 0 outside a>0 ∧ z>0
    (the Lean ∫₀^∞ e^{−zt}t^{a−1}(1+t)^{b−a−1}dt diverges → ∫=0), mirrored so the no-hypothesis
    bridge rows (besselK0_eq_tricomiU) hold via mutual junk-0."""
    if a <= 0 or z <= 0:
        return mp.mpf(0)
    return mp.hyperu(a, b, z)


def _En_ascii(n, x):
    """FLMF `En n x` (ASCII head) = generalized expint ∫₁^∞ e^{−xt}/tⁿ dt = mp.expint(n,x)."""
    return mp.expint(int(n), x)


def _cosGamma(t1, t2, phi):
    """FLMF `cosGamma θ₁ θ₂ φ` = cosθ₁cosθ₂ + sinθ₁sinθ₂cosφ (spherical separation angle)."""
    return mp.cos(t1) * mp.cos(t2) + mp.sin(t1) * mp.sin(t2) * mp.cos(phi)


def _multiplyingGamma(n, s):
    """FLMF `multiplyingGamma n s` = (2π)^((1−n)/2)·n^(s−1/2)·∏_{k<n} Γ(s/n+k/n) (the Gauss-
    multiplication product = Γ(s)). Bound to the LITERAL product so `=1` rows are real."""
    n = int(n)
    pref = (2 * mp.pi) ** ((mp.mpf(1) - n) / 2) * mp.mpf(n) ** (s - mp.mpf(1) / 2)
    return pref * mp.fprod([mp.gamma(s / n + mp.mpf(k) / n) for k in range(n)])


# ── M16 tail: Legendre/orthogonal-poly generating-function helpers (Agent B) ──
def _gen_sum(x, t, N):           # ∑_{n≤N} Pₙ(x)·tⁿ
    return mp.fsum(mp.legendre(n, x) * t ** n for n in range(int(N) + 1))


def _gen_sum_d(x, t, N):         # ∑_{n≤N} n·Pₙ(x)·tⁿ
    return mp.fsum(n * mp.legendre(n, x) * t ** n for n in range(int(N) + 1))


def _gen_quad(x, t):             # 1 − 2xt + t²
    return 1 - 2 * x * t + t ** 2


def _legendre_eigenvalue(n):
    """FLMF `legendreEigenvalue n` (Spheroidal/Eigenvalues.lean) — the degenerate
    spheroidal eigenvalue λₙ = λₙ⁰(0) = n(n+1) (DLMF 30.3.3 at γ = 0, order μ = 0),
    i.e. the eigenvalue of the Legendre differential equation
        (1−x²)·w″(x) − 2x·w′(x) + λ·w(x) = 0
    satisfied by Pₙ (the γ→0 collapse of the spheroidal equation, DLMF 30.3.1/30.2.1).
    verify() anchors this against that DEFINING ODE — λ recovered numerically as
    (2x·Pₙ′(x) − (1−x²)·Pₙ″(x))/Pₙ(x) — never against the n(n+1) closed form by name.
    The n=1 anchor (λ₁ = 2, not 1) rejects a trigonometric-eigenvalue n² mis-binding;
    Flammer-vs-Meixner–Schäfke normalizations differ only by γ²-shifts, which vanish
    at the γ = 0 point this binding covers."""
    n = _nat(n, "legendreEigenvalue")
    return mp.mpf(n) * (mp.mpf(n) + 1)


def _gen_closed(x, t):           # (1 − 2xt + t²)^(−1/2); raises off the convergence domain
    q = _gen_quad(x, t)
    if q <= 0:
        raise ValueError("genClosed: 1−2xt+t² ≤ 0 (outside the generating-function domain)")
    return q ** (-mp.mpf(1) / 2)


def _uval(x, n):                 # (U ℝ n).eval x — 2nd-kind Chebyshev, independent mpmath
    return mp.chebyu(int(n), x)


def _rodrigues_poly(l, x):       # (d/dx)^l (x²−1)^l — the Rodrigues numerator
    return mp.diff(lambda t: (t ** 2 - 1) ** int(l), x, int(l))


def _a0_approx(q):               # Mathieu a₀ small-q (DLMF 28.6.1): −½q² + (7/128)q⁴
    return -mp.mpf(1) / 2 * q ** 2 + mp.mpf(7) / 128 * q ** 4


def _a1_approx(q):               # Mathieu a₁ small-q (DLMF 28.6.2): 1 + q − ⅛q² − (1/64)q³
    return 1 + q - mp.mpf(1) / 8 * q ** 2 - mp.mpf(1) / 64 * q ** 3


def _b1_approx(q):               # Mathieu b₁ small-q (DLMF 28.6.3): 1 − q − ⅛q² + (1/64)q³
    return 1 - q - mp.mpf(1) / 8 * q ** 2 + mp.mpf(1) / 64 * q ** 3


def _a2_approx(q):               # Mathieu a₂ small-q (DLMF 28.6.4): 4 + (5/12)q² − (763/13824)q⁴
    return 4 + mp.mpf(5) / 12 * q ** 2 - mp.mpf(763) / 13824 * q ** 4


def _b2_approx(q):               # Mathieu b₂ small-q (DLMF 28.6.5): 4 − (1/12)q² + (5/13824)q⁴
    return 4 - mp.mpf(1) / 12 * q ** 2 + mp.mpf(5) / 13824 * q ** 4


def _mathieu_hill_eigs(kind, q, n=12):
    """Independent Mathieu characteristic values from the truncated Hill tridiagonal
    matrices (the DLMF 28.4 Fourier-coefficient recurrences for y'' + (a − 2q cos 2x)y = 0).
    Used only by `verify()` to anchor the §28.6 approximant bindings — NOT a binding.
      'ce_odd'  — basis cos((2m+1)x): diag (2m+1)², M₀₀ += q  → eigenvalues a₁,a₃,…
      'se_odd'  — basis sin((2m+1)x): diag (2m+1)², M₀₀ −= q  → eigenvalues b₁,b₃,…
      'ce_even' — basis cos(2mx):     diag (2m)², √2·q first link → eigenvalues a₀,a₂,…
      'se_even' — basis sin(2mx), m≥1: diag (2m)²                → eigenvalues b₂,b₄,…
    Returns the sorted real eigenvalue list; truncation error is O(q^n/((n−1)!)²)-tiny."""
    q = mp.mpf(q)
    A = mp.zeros(n, n)
    if kind in ("ce_odd", "se_odd"):
        for m in range(n):
            A[m, m] = mp.mpf((2 * m + 1) ** 2)
        A[0, 0] += q if kind == "ce_odd" else -q
        for m in range(n - 1):
            A[m, m + 1] = A[m + 1, m] = q
    elif kind == "ce_even":
        for m in range(n):
            A[m, m] = mp.mpf((2 * m) ** 2)
        A[0, 1] = A[1, 0] = mp.sqrt(2) * q
        for m in range(1, n - 1):
            A[m, m + 1] = A[m + 1, m] = q
    else:  # se_even
        for m in range(n):
            A[m, m] = mp.mpf((2 * (m + 1)) ** 2)
        for m in range(n - 1):
            A[m, m + 1] = A[m + 1, m] = q
    E, _ = mp.eig(A)
    return sorted(e.real for e in E)


def _mathieu_op(a, q, y, x):
    """FLMF `mathieuOp` (Mathieu/Basic.lean) — the Mathieu differential operator of
    DLMF 28.2.1 applied to a function:

        mathieuOp a q y x = y''(x) + (a − 2q·cos 2x)·y(x).

    `y` arrives as a one-argument callable (the extractor's `_fn_callable` of the Lean
    lambda / registry-fn argument); y'' is mp.diff's order-2 numerical derivative, which
    mpmath computes at raised working precision (near-exact for the analytic modes these
    surfaces apply the operator to). Anchored to the DLMF 28.2.1 defining formula, not to
    any FLMF recurrence theorem (see the harmonic-oscillator and e^{sin x} anchors)."""
    return mp.diff(y, x, 2) + (a - 2 * q * mp.cos(2 * x)) * y(x)


# ── M16 tail: Dedekind-η q-series factors (Agent C) ──────────────────────────
def _q_product_factor(j, w, n):
    """FLMF `qProductFactor` (QProduct.lean): at the first slot 0 the factor is 1."""
    return mp.mpf(1) if j == 0 else (1 - w * mp.mpf(0) ** n)


def _theta_series_term(j, w, n):
    """FLMF `thetaSeriesTerm` (QProduct.lean): at j=0 the term is the indicator [n=0]."""
    return mp.mpf(1) if (j == 0 and int(n) == 0) else mp.mpf(0)


# ── M17 tail: Clausen / Lobachevsky / Riemann ξ / Jacobi amplitude ───────────
def _clausen_cl2(theta):
    """FLMF `Cl_2 θ = Im Li₂(e^{iθ}) = ∑' sin(nθ)/n²` (DLMF 25.12; Clausen.lean) — the
    order-2 Clausen SINE → mp.clsin(2, θ)."""
    return mp.clsin(2, theta)


def _lobachevsky(theta):
    """FLMF `lobachevsky θ = (1/2)·Cl_2(2θ)` (Lobachevsky.lean)."""
    return mp.mpf(1) / 2 * mp.clsin(2, 2 * theta)


def _riemann_xi(s):
    """FLMF `riemannXi s = (1/2)·s·(s−1)·completedRiemannZeta s` (Hadamard.lean) — the FULL
    Riemann ξ (the ½s(s−1) prefactor cancels Λ's poles at s=0,1), NOT bare Λ. ξ(1−s)=ξ(s)."""
    return mp.mpf(1) / 2 * s * (s - 1) * _completed_riemann_zeta(s)


def _iRepErfc(n, x):
    """FLMF `iRepErfc n x` = iⁿerfc(x), the n-fold repeated integral of erfc (DLMF 7.18).
    Single-integral closed form (7.18.4, independent of the f(n+1)=∫ₓ^∞ f(n) recursion):
    iⁿerfc(x) = (2/√π)(1/n!)∫ₓ^∞ (t−x)ⁿ e^{−t²} dt. i⁰erfc = erfc; the recursion rows that
    integrate THIS are doubly-nested quadrature → the extractor's eval-timeout skips them."""
    n = int(n)
    return (2 / mp.sqrt(mp.pi)) / mp.factorial(n) * mp.quad(lambda t: (t - x) ** n * mp.e ** (-t ** 2),
                                                            [x, mp.inf])


def _goodwin_staton_trunc(z, b):
    """FLMF `GoodwinStaton.goodwinStatonTrunc z b = ∫₀ᵇ e^{−t²}/(t+z) dt` (GoodwinStaton.lean,
    truncated finite-interval Goodwin–Staton integral). As b→∞ it tends to the full DLMF 7.2.12
    integral ∫₀^∞ e^{−t²}/(t+z) dt (z>0 for the denominator to stay clear of 0 on [0,∞))."""
    return mp.quad(lambda t: mp.e ** (-t ** 2) / (t + z), [0, b])


def _bickleyKi(n, x):
    """FLMF `bickleyKi n x` = Kiₙ(x), the n-fold repeated integral of K₀ (DLMF 10.43(iii)).
    Single-integral form: Ki₀ = K₀; Kiₙ(x) = (1/(n−1)!)∫ₓ^∞ (t−x)^{n−1} K₀(t) dt (n≥1). x>0."""
    n = int(n)
    if x <= 0:
        raise ValueError("bickleyKi: x ≤ 0 (K₀ singular on the integration ray)")
    if n == 0:
        return mp.besselk(0, x)
    return (1 / mp.factorial(n - 1)) * mp.quad(lambda t: (t - x) ** (n - 1) * mp.besselk(0, t),
                                               [x, mp.inf])


def _besselK_real(nu, z):
    """FLMF `besselK_real ν z = (1/2)∫_{−∞}^∞ e^{−z cosh u − ν u} du` = real-order modified
    Bessel K_ν(z) (DLMF 10.32.9). z>0 for convergence (K is even in ν)."""
    if z <= 0:
        raise ValueError("besselK_real: z ≤ 0 (integral diverges)")
    return mp.besselk(nu, z)


def _tricomi_bridge_fun(nu, z):
    """FLMF `tricomiBridgeFun ν z = √π·(2z)^ν·e^{−z}·U(ν+½; 2ν+1; 2z)` (DLMF 13.6.10 RHS) —
    built from the independently-bound Tricomi U, so `besselK_real = tricomiBridgeFun` is a
    genuine cross-check of besselk against hyperu."""
    return mp.sqrt(mp.pi) * (2 * z) ** nu * mp.e ** (-z) * _tricomiU(nu + mp.mpf(1) / 2, 2 * nu + 1, 2 * z)


def _prob_hermite(n, c, x):
    """FLMF `(probHermite n c).eval x`: the variance-c probabilists' Hermite, H₀=1,
    H_{n+1}=x·Hₙ−c·Hₙ′. Equals c^{n/2}·Heₙ(x/√c) = (c/2)^{n/2}·hermite(n, x/√(2c)); at c=1 it
    is the standard Heₙ."""
    n = int(n)
    return (c / 2) ** (mp.mpf(n) / 2) * mp.hermite(n, x / mp.sqrt(2 * c))


def _jacobi_am(u, k):
    """FLMF `jacobiAm u k` (JacobiAmplitude.lean) = inverse of φ ↦ ellipticF φ k; equivalently
    am(u,k) = ∫₀^u dn(t, m=k²) dt (DLMF 22.13.1), so sin(am u k) = sn(u,k). 2nd arg = MODULUS k,
    defined only for |k|<1 → RAISE on |k|≥1 so the out-of-domain sample drops."""
    if abs(k) >= 1:
        raise ValueError("jacobiAm: |k| ≥ 1 (modulus out of domain)")
    return mp.quad(lambda t: mp.ellipfun("dn", t, k ** 2), [0, u])


# ── M18 tail: confluent hypergeometric ₁F₁/pFq + Rodrigues + double factorial (Agent Z) ──
def _kummerM(a, b, z):
    """FLMF `kummerM a b z` (notation `₁F₁ a b z`, DLMF 13.2.2) = M(a;b;z); arg order
    (numerator a, denominator b, argument z) = mp.hyp1f1. Entire in z. Anchored at M(1,2,z)=(eᶻ−1)/z."""
    return mp.hyp1f1(a, b, z)


def _hg_terminating(p):
    """True iff the Gauss-series numerator parameter `p` is a NONPOSITIVE INTEGER, i.e.
    `(p)ₙ = 0` for all `n > −p`. The series then has finite support (Mathlib:
    `ordinaryHypergeometric_radius_top_of_neg_nat₁/₂`, radius = ⊤) and its
    `FormalMultilinearSeries.sum` is that polynomial for EVERY z — never the junk 0."""
    try:
        return mp.im(p) == 0 and mp.re(p) <= 0 and mp.isint(mp.re(p))
    except (TypeError, ValueError):
        return False


def _gaussF(a, b, c, z):
    """FLMF `₂F₁ a b c z` / `ordinaryHypergeometric` (Mathlib
    `Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`, DLMF 15.2.1).

    The Lean object is NOT the analytic continuation: it is
    `(ordinaryHypergeometricSeries ℂ a b c).sum z = ∑' n, [(a)ₙ(b)ₙ/((c)ₙ n!)] • zⁿ`,
    a `tsum` over ℕ — which in ℂ is the series value when the family is SUMMABLE
    (= absolutely convergent) and the junk value 0 otherwise ("Note that this takes the
    junk value `0` outside the radius of convergence", Mathlib docstring). Binding it to
    mp.hyp2f1 (which CONTINUES past |z| = 1) therefore mis-modelled every off-disc sample:
    the kernel-proven `hypergeometric_15_1_2_a` (𝐅 = ₂F₁/Γ(c), where the olver binding
    already mirrors the junk-0) FAILed with rel = 1.0 at the default ℂ grid's off-disc
    points, 0 against a nonzero continuation. Mirror the Lean semantics exactly:

    • `a` or `b` a NONPOSITIVE INTEGER → the coefficients vanish beyond n = −a (resp. −b),
      the series is a POLYNOMIAL of radius ⊤, and `.sum` is that polynomial for all z.
      mp.hyp2f1 returns exactly the terminating polynomial there (same convention as the
      `olverHypergeometric` binding, validated in verify() against the finite Σ).
    • ‖z‖ < 1 → inside the radius the series converges absolutely; `.sum` is the analytic
      value, which is mp.hyp2f1.
    • ‖z‖ = 1 → the ONLY boundary points that are summable are those with
      Re(c − a − b) > 0: |(a)ₙ(b)ₙ/((c)ₙ n!)| ~ C·n^{Re(a+b−c)−1}, and Σ n^{s−1} converges
      iff s < 0. `tsum` needs UNCONDITIONAL summability, so the conditionally convergent
      boundary regime −1 < Re(c−a−b) ≤ 0 (z ≠ 1) is junk-0 as well. Above the threshold
      the sum is Gauss's value, again mp.hyp2f1 (this keeps rows evaluated AT z = 1 under
      a `0 < (c−a−b).re` hypothesis — ordinaryHypergeometric_one_dlmf_complex — scored).
    • ‖z‖ > 1 → junk 0.

    NOT modelled (deliberately): a NONPOSITIVE-INTEGER `c`, where Lean's `((c)ₙ)⁻¹ = 0⁻¹ = 0`
    junk makes the series a polynomial too. mp.hyp2f1 raises there, so such a sample point
    DROPS (an honest loss of coverage) rather than being scored against a wrong value.

    Anchored at ₂F₁(1,1,2,z)=−log(1−z)/z and the Legendre instance Pₙ=₂F₁(−n,n+1;1;(1−x)/2)."""
    if _hg_terminating(a) or _hg_terminating(b):
        return mp.hyp2f1(a, b, c, z)
    az = abs(z)
    if az < 1:
        return mp.hyp2f1(a, b, c, z)
    tol = mp.mpf(10) ** (-(mp.mp.dps - 6))       # ‖z‖ = 1 to working precision
    if abs(az - 1) <= tol and mp.re(c - a - b) > 0:
        return mp.hyp2f1(a, b, c, z)
    return mp.mpf(0)


def _gaussF_coeff(a, b, c, k):
    """kth series coefficient of ₂F₁: (a)ₖ(b)ₖ / ((c)ₖ·k!)  (rising factorials)."""
    k = int(k)
    return mp.rf(a, k) * mp.rf(b, k) / (mp.rf(c, k) * mp.factorial(k))


_GAUSSPRODCOEFF_CACHE = {}


def _gaussProductCoefficient(a, b, c, s):
    """FLMF `gaussProductCoefficient a b c s` (Ch15Products.lean:27) = the sth Maclaurin
    coefficient Aₛ (DLMF 15.16.2) of g(z) = (1−z)^(a+b−c)·₂F₁(2a,2b;2c−1;z), defined in Lean as
    the honest Taylor coefficient `iteratedDeriv s g 0 / s!`.

    Computed here EXACTLY as the CAUCHY PRODUCT of the two explicit Maclaurin series
       (1−z)^(a+b−c)     = Σₖ [(−(a+b−c))ₖ / k!] zᵏ            (binomial series)
       ₂F₁(2a,2b;2c−1;z) = Σₘ [(2a)ₘ(2b)ₘ / ((2c−1)ₘ m!)] zᵐ   (Gauss series)
    so Aₛ = Σ_{k=0}^{s} [(−(a+b−c))ₖ/k!]·[(2a)_{s−k}(2b)_{s−k}/((2c−1)_{s−k}(s−k)!)]. This is
    O(s) per coefficient and EXACT to working precision, where the per-order numerical
    differentiation of the defining relation (`mp.diff(g, 0, s)`) costs O(super-linear) in s —
    a growing-order coefficient series (the §15.16.1/2 HasSum rows need s up to ~280 at the disc
    boundary) false-skips as `hassum eval-timeout` under mp.diff. Coefficient list cached and
    grown geometrically per (a, b, c, dps) so all terms of one sample share it. SELF-VALIDATED in
    verify() against the numerical Taylor coefficient of g (mp.taylor / mp.diff·1/s!) — the DLMF
    15.16.2 defining relation, fully decorrelated from this convolution — never by name."""
    s = int(s)
    key = (repr(a), repr(b), repr(c), mp.mp.dps)
    coeffs = _GAUSSPRODCOEFF_CACHE.get(key)
    if coeffs is None or len(coeffs) <= s:
        N = 2 * s + 16
        alpha = a + b - c
        bco = [mp.rf(-alpha, k) / mp.factorial(k) for k in range(N + 1)]
        gco = [mp.rf(2 * a, m) * mp.rf(2 * b, m) / (mp.rf(2 * c - 1, m) * mp.factorial(m))
               for m in range(N + 1)]
        coeffs = [mp.fsum(bco[k] * gco[j - k] for k in range(j + 1)) for j in range(N + 1)]
        _GAUSSPRODCOEFF_CACHE[key] = coeffs
    return coeffs[s]


def _pfaffExtension(a, b, c, w):
    """FLMF `pfaffExtension a b c w` (Frameworks/Hypergeometric/PfaffFullDisc.lean) =
    (1−w)^(−a)·₂F₁(a, c−b; c; w/(w−1)) — the Pfaff analytic extension of ₂F₁(a,b;c;·) to the
    half-plane re w < 1/2 (the RHS of the full-disc DLMF 15.8.1). Mirrors the Lean definition
    LITERALLY: principal power (mp.power) times the inner Gauss series, whose argument satisfies
    |w/(w−1)| < 1 ⟺ re w < 1/2, so on the intended domain the series converges and mp.hyp2f1
    agrees with the series sum. The inner factor goes through `_gaussF` (Mathlib's `₂F₁`,
    which the Lean def names literally), so outside that domain the binding inherits the same
    junk-0 as the object it models instead of silently continuing."""
    return mp.power(1 - w, -a) * _gaussF(a, c - b, c, w / (w - 1))


def _principalGauss(a, b, c, z):
    """FLMF `principalGauss a b c z` (Frameworks/Hypergeometric/GaussPrincipalGlobal.lean):
    the selected PRINCIPAL analytic continuation of the ordinary Gauss function ₂F₁ to the
    slit plane ℂ∖[1,∞) = mp.hyp2f1 (principal branch, cut on [1,∞), the same branch as the
    defining series inside the unit disc). The FLMF def is guarded by `GaussRegular c` and
    returns a junk 0 at singular (nonpositive-integer) c, a value no sampled row reaches;
    every theorem using it carries GaussRegular c or approaches c through regular values.
    Anchored by the ₂F₁ defining series (DLMF 15.2.1), same kernel as `_gaussF`."""
    return mp.hyp2f1(a, b, c, z)


def _principalOlver(a, b, c, z):
    """FLMF `principalOlver a b c z` (GaussPrincipalGlobal.lean) = Olver's bold-F, the
    principal continuation of 𝐅(a,b;c;z) = ₂F₁(a,b;c;z)/Γ(c) (DLMF 15.2.2), which is entire
    in c (no singular-c guard needed). Anchored by the bold-F series
    Σₙ (a)ₙ(b)ₙ / (Γ(c+n)·n!) zⁿ = ₂F₁(a,b;c;z)/Γ(c) (Olver.lean olverHypergeometricCoefficient)."""
    return mp.hyp2f1(a, b, c, z) / mp.gamma(c)


def _olverHypergeometric(a, b, c, z):
    """FLMF `olverHypergeometric a b c z` (Olver.lean:51) = `(olverHypergeometricSeries a b c).sum z`,
    the SUM of Olver's bold-F power series Σₙ (a)ₙ(b)ₙ / (Γ(c+n)·n!) zⁿ (DLMF 15.2.2). Inside the
    series' radius of convergence (|z| < 1) this equals ₂F₁(a,b;c;z)/Γ(c) — the same value as the
    principal continuation `principalOlver` there. OUTSIDE the disc the Lean `FormalMultilinearSeries.sum`
    returns its junk 0 (the series diverges), so mirror that: 0 for |z| ≥ 1. Only the §15.7 rows with
    a |z| < 1 hypothesis consume this head. SELF-VALIDATED in verify() against the direct partial-sum
    of the DEFINING series (decorrelated from mp.hyp2f1), never by name.

    TERMINATING case: when `a` is a NONPOSITIVE INTEGER the coefficients (a)ₙ vanish for n > −a,
    so the series is a POLYNOMIAL — a finitely-supported FormalMultilinearSeries whose `.sum`
    converges to that polynomial for EVERY z (never the |z|≥1 junk-0 of a genuinely divergent
    series). mpmath's hyp2f1 with a nonpositive-integer first parameter returns exactly that
    terminating polynomial for all z (validated in verify() against the direct finite Σ). This is
    the §15.15.1 usage 𝐅(−s,b;c;1/z₀), where 1/z₀ may lie on or outside the unit circle.
    `b` terminates the series exactly as `a` does (the coefficients are symmetric in a, b —
    Mathlib `ordinaryHypergeometricSeries_symm`), so both are honored.

    BOUNDARY ‖z‖ = 1: the sum is a `tsum`, i.e. the value only when the family is SUMMABLE.
    |(a)ₙ(b)ₙ/(Γ(c+n)n!)| ~ C·n^{Re(a+b−c)−1}, so the circle is summable iff Re(c−a−b) > 0
    and junk-0 otherwise. Same rule, same threshold as `_gaussF` (₂F₁ = Γ(c)·𝐅 relates the
    two bindings pointwise — hypergeometric_15_1_2_a — so their domains must agree)."""
    if _hg_terminating(a) or _hg_terminating(b):
        return mp.hyp2f1(a, b, c, z) / mp.gamma(c)
    az = abs(z)
    if az < 1:
        return mp.hyp2f1(a, b, c, z) / mp.gamma(c)
    tol = mp.mpf(10) ** (-(mp.mp.dps - 6))
    if abs(az - 1) <= tol and mp.re(c - a - b) > 0:
        return mp.hyp2f1(a, b, c, z) / mp.gamma(c)
    return mp.mpf(0)


# ── §15.10 Kummer solutions w₁..w₆ as principal continuations (Ch15KummerPrincipal.lean:26-47).
# Each mirrors its Lean def LITERALLY: principalGauss → mp.hyp2f1 (principal ₂F₁, cut [1,∞)),
# and every `z ^ w` is the principal complex power `z**w`. Sound on the rows' domain hypotheses
# (InPrincipalGaussDomain guarantees the ₂F₁ arguments 1−z / 1−1/z avoid the cut). w₂,w₄,w₅,w₆
# are TWO-LINE defs the extractor's single-line δ-reducer cannot inline, hence bound here (w₁,w₃
# are one-liners over the already-bound principalGauss; bound too for uniformity). SELF-VALIDATED:
# these six exactly satisfy the Kummer Wronskian DLMF 15.10.7 to <1e-40 (docs/verification/ch15/
# probe_w5w6.py), which no wrong W-definition could — an independent anchor beyond the name.
# NOTE (2026-08-11): w₅/w₆ now carry the e^{aπi}/e^{bπi} phases of DLMF 15.10.15/16's third
# displayed forms, exactly as the Lean defs do (post kummerPhase-resolution); the Wronskian
# anchor above validated the phaseless pair — the phases rescale 𝒲{w₅,w₆} by the constant
# e^{(a+b)πi} and are independently pinned by the §15.10(ii) connection rows themselves
# (15.10.19–36 check to ≤ 1e-30 with the phases, ≈1 without).
def _principalW1(a, b, c, z):
    return mp.hyp2f1(a, b, c, z)


def _principalW2(a, b, c, z):
    return z ** (1 - c) * mp.hyp2f1(a - c + 1, b - c + 1, 2 - c, z)


def _principalW3(a, b, c, z):
    return mp.hyp2f1(a, b, a + b - c + 1, 1 - z)


def _principalW4(a, b, c, z):
    return (1 - z) ** (c - a - b) * mp.hyp2f1(c - a, c - b, c - a - b + 1, 1 - z)


def _principalW5(a, b, c, z):
    """FLMF `principalW5` (Ch15KummerPrincipal.lean:80) = e^{aπi}·z^{−a}·F(a,a−c+1;a−b+1;1/z),
    DLMF 15.10.15's THIRD displayed form — the Lean def CARRIES the e^{aπi} phase (the 2026-07
    kummerPhase resolution moved DLMF's w₅ phase INTO the def; see the module docstring there).
    The pre-resolution binding omitted it, false-FAILing every §15.10(ii) connection row
    (15.10.19–36 worst ≈ 1.0–1.9 = |1 − e^{aπi}| scale; with the phase the same rows check to
    ≤ 1e-30, docs/verification/ch15/probe_w5w6.py lineage)."""
    return mp.exp(a * mp.pi * 1j) * z ** (-a) * mp.hyp2f1(a, a - c + 1, a - b + 1, 1 / z)


def _principalW6(a, b, c, z):
    """FLMF `principalW6` (Ch15KummerPrincipal.lean:90) = e^{bπi}·z^{−b}·F(b,b−c+1;b−a+1;1/z),
    DLMF 15.10.16's THIRD displayed form — phase inside the def, mirroring `_principalW5`."""
    return mp.exp(b * mp.pi * 1j) * z ** (-b) * mp.hyp2f1(b, b - c + 1, b - a + 1, 1 / z)


def _kummerPhase(t, z):
    return z ** t * (-z) ** (-t)


def _principalOlverBoundary(sign):
    """Directional boundary value of `principalOlver` across the cut [1,∞), DLMF 15.2 (ii):
    lim_{ε→0⁺} 𝐅(a,b;c; x ± iε)  (sign = +1 above / −1 below), MIRRORING the FLMF defs
    principalOlverBoundaryAbove/Below = limUnder (𝓝[>] 0) (fun ε => principalOlver a b c
    (x ± εi)) LITERALLY. Off the cut 𝐅 is analytic in the (upper/lower) half-plane up to the
    boundary, so g(ε) := 𝐅(a,b;c;x±iε) admits an integer-power expansion L + c₁ε + c₂ε² + …;
    a step-halving Neville/Romberg extrapolation (ratio 2, successively removing ε¹,ε²,…)
    recovers L to ≈ε₀^N, well past the exact-equality gate.

    DEPTH/PRECISION (fixed-oracle; probe docs/verification/ch15/probe_olver_boundary.py):
    N=6 truncates the
    ε-expansion at O(ε₀^6), leaving a jump residual ≈2.2e-18 that just BREACHES the 1e-18 eq
    gate (docs/verification/ch15/probe_olver_boundary.py: 2.955e-15 worst on the harder
    x≈1.05/1.2 samples). This is a truncation artifact of the extrapolation, NOT a statement
    error (the identity holds exactly). N=9 removes ε¹…ε⁸ (residual ≈4e-26), and the whole
    Neville table runs at ≥100 dps so the deeper Richardson recombination stays roundoff-clean
    — strictly more accurate, no gate/tolerance touched."""
    def inner(a, b, c, x):
        with mp.workdps(max(mp.mp.dps, 100)):
            x = mp.mpf(x)
            eps0, N = mp.mpf("1e-3"), 9
            T = [_principalOlver(a, b, c, x + sign * 1j * (eps0 / (2 ** i))) for i in range(N)]
            for p in range(1, N):                 # remove the εᵖ term at each pass
                f = mp.mpf(2) ** p
                T = [(f * T[i + 1] - T[i]) / (f - 1) for i in range(len(T) - 1)]
            return T[0]
    return inner


def _gaussSingularIterated(m, l, b, z):
    """FLMF `gaussSingularIterated m l b z` (Ch15DefinitionsAnalytical.lean): the iterated
    singular limit  lim_{c→−m−ℓ} (lim_{a→−m} ₂F₁(a,b;c;z)).  The inner limit is ₂F₁(−m,b;c;z)
    (entire in a, so exact at a=−m: the degree-m terminating polynomial DLMF 15.2.4), which is
    analytic in c at c=−m−ℓ (each (c)ₙ, n≤m, is nonzero there for ℓ≥0), so the outer limit is
    its value at c=−m−ℓ:
        F(−m,b;−m−ℓ;z) = Σ_{n=0}^m (−m)ₙ(b)ₙ / ((−m−ℓ)ₙ·n!) zⁿ     (DLMF 15.2.4 / 15.2.5).
    This is the DEFINING closed form of the singular value. It is NOT the coupled limit
    lim_{a→−m} ₂F₁(a,b;a−ℓ;z) of DLMF 15.2.6, which the DLMF text states gives a DIFFERENT
    value ('the interpretation … and not …')."""
    m, l = int(m), int(l)
    c = -mp.mpf(m + l)
    s = mp.mpf(0)
    for n in range(m + 1):
        s += mp.rf(-mp.mpf(m), n) * mp.rf(b, n) / (mp.rf(c, n) * mp.factorial(n)) * (z ** n)
    return s


def _kummerCoefficient(a, b, n):
    """FLMF `kummerCoefficient a b n` = (a)ₙ/((b)ₙ·n!) (DLMF 13.2.2); junk-0 when (b)ₙ=0."""
    n = int(n)
    denom = mp.rf(b, n)
    return mp.mpf(0) if denom == 0 else mp.rf(a, n) / (mp.factorial(n) * denom)


def _pFqCoefficient(A, B, n):
    """FLMF `pFqCoefficient A B n` (DLMF 16.2.1) = (∏ᵢ (Aᵢ)ₙ) / ((∏ⱼ (Bⱼ)ₙ)·n!), the
    coefficient of the generalized hypergeometric series ₚFᵩ(A;B;z) = Σₙ pFqCoefficient·zⁿ.
    `A`, `B` are the parameter tuples (Python lists of the small-arity `Fin p`/`Fin q` values);
    (x)ₙ = mp.rf, matching the Lean `(ascPochhammer 𝕂 n).eval x`. Junk-0 when any (Bⱼ)ₙ = 0
    (the Lean `(∏ⱼ …)⁻¹` at 0 is Mathlib's 0⁻¹ = 0), mirroring `_kummerCoefficient`."""
    n = int(n)
    num = mp.mpf(1)
    for a in A:
        num *= mp.rf(a, n)
    den = mp.factorial(n)
    for b in B:
        den *= mp.rf(b, n)
    return mp.mpf(0) if den == 0 else num / den


# ── DLMF §15.10 resonant logarithmic local solutions (Ch15LogarithmicSolutions.lean) ──
# Each of `logSolution15_10_8/9/10` is transcribed TERM BY TERM from the Lean `def` (which in
# turn transcribes the DLMF 15.10.8/9/10 display): the ₂F₁·log z head, the finite negative-
# power correction Σ_{k=1}^{n-1}, and the digamma-weighted power part (a tsum for 8/9, finite
# for 10). (x)_k = mp.rf (ascending Pochhammer, matching `(ascPochhammer ℂ k).eval x`), ψ =
# mp.digamma (matching `Complex.digamma`), k! = mp.factorial, and `(-z)^(-k)` = mp.power(-z, -k)
# (principal branch; the intended domain is the punctured unit disc, off the cut). These are the
# EXPLICIT functions whose Gauss-ODE-residual the theorems assert vanishes; the fidelity check
# evaluates that residual numerically, so the binding must reproduce the Lean def, not the ODE.
# Self-validated in verify() by (a) matching a direct series recomputation and (b) confirming
# the DLMF-asserted residual z(1−z)f''+(c−(a+b+1)z)f'−ab·f vanishes at a sample point.
_LOGSOL_TSUM_CAP = 6000
_LOGSOL_TSUM_TOL = mp.mpf("1e-28")


def _logSolution15_10_8(n, a, b, z):
    """FLMF `logSolution15_10_8 n a b z` (DLMF 15.10.8), c = n ∈ ℕ_{≥1}."""
    n = int(round(float(mp.re(n))))
    z = mp.mpc(z)
    val = mp.hyp2f1(a, b, n, z) * mp.log(z)
    for k in range(1, n):                                  # Σ_{k=1}^{n-1}
        val -= (mp.factorial(n - 1) * mp.factorial(k - 1) /
                (mp.factorial(n - k - 1) * mp.rf(1 - a, k) * mp.rf(1 - b, k))) * mp.power(-z, -k)
    ser = mp.mpc(0)
    for k in range(0, _LOGSOL_TSUM_CAP):                   # Σ_{k=0}^∞
        t = (mp.rf(a, k) * mp.rf(b, k) / (mp.rf(n, k) * mp.factorial(k))) * z ** k * \
            (mp.digamma(a + k) + mp.digamma(b + k) - mp.digamma(1 + k) - mp.digamma(n + k))
        ser += t
        if k > 6 and abs(t) < _LOGSOL_TSUM_TOL * (abs(ser) + 1):
            break
    return val + ser


def _logSolution15_10_9(n, m, b, z):
    """FLMF `logSolution15_10_9 n m b z` (DLMF 15.10.9), a = −m ∈ ℤ_{≤0}, c = n."""
    n, m = int(round(float(mp.re(n)))), int(round(float(mp.re(m))))
    z = mp.mpc(z)
    val = mp.hyp2f1(-m, b, n, z) * mp.log(z)
    for k in range(1, n):                                  # Σ_{k=1}^{n-1}
        val -= (mp.factorial(n - 1) * mp.factorial(k - 1) /
                (mp.factorial(n - k - 1) * mp.rf(m + 1, k) * mp.rf(1 - b, k))) * mp.power(-z, -k)
    for k in range(0, m + 1):                              # Σ_{k=0}^{m}
        val += (mp.rf(-m, k) * mp.rf(b, k) / (mp.rf(n, k) * mp.factorial(k))) * z ** k * \
            (mp.digamma(1 + m - k) + mp.digamma(b + k) - mp.digamma(1 + k) - mp.digamma(n + k))
    tail = mp.mpc(0)                                        # (−1)^m m! Σ_{k≥m+1}
    for k in range(m + 1, _LOGSOL_TSUM_CAP):
        t = (mp.factorial(k - 1 - m) * mp.rf(b, k) /
             (mp.rf(n, k) * mp.factorial(k))) * z ** k
        tail += t
        if k > m + 6 and abs(t) < _LOGSOL_TSUM_TOL * (abs(tail) + 1):
            break
    return val + (-1) ** m * mp.factorial(m) * tail


def _logSolution15_10_10(n, m, l, z):
    """FLMF `logSolution15_10_10 n m l z` (DLMF 15.10.10), a = −m, b = −l, c = n, l ≤ m."""
    n, m, l = (int(round(float(mp.re(x)))) for x in (n, m, l))
    z = mp.mpc(z)
    val = mp.hyp2f1(-m, -l, n, z) * mp.log(z)
    for k in range(1, n):                                  # Σ_{k=1}^{n-1}
        val -= (mp.factorial(n - 1) * mp.factorial(k - 1) /
                (mp.factorial(n - k - 1) * mp.rf(m + 1, k) * mp.rf(l + 1, k))) * mp.power(-z, -k)
    for k in range(0, l + 1):                              # Σ_{k=0}^{l}
        val += (mp.rf(-m, k) * mp.rf(-l, k) / (mp.rf(n, k) * mp.factorial(k))) * z ** k * \
            (mp.digamma(1 + m - k) + mp.digamma(1 + l - k) -
             mp.digamma(1 + k) - mp.digamma(n + k))
    fin = mp.mpc(0)                                        # (−1)^l l! Σ_{k=l+1}^{m}  (finite)
    for k in range(l + 1, m + 1):
        fin += (mp.factorial(k - 1 - l) * mp.rf(-m, k) /
                (mp.rf(n, k) * mp.factorial(k))) * z ** k
    return val + (-1) ** l * mp.factorial(l) * fin


# ── Meijer-G (DLMF 16.17.1), Frameworks/MeijerG.lean + MeijerG/ResidueExpansion.lean ──
# FLMF `meijerG bNum aNum bDen aDen σ z` (4 explicit Fin-indexed ℂ parameter vectors —
# bNum = b₁..b_m, aNum = a₁..a_n, bDen = b_{m+1}..b_q, aDen = a_{n+1}..a_p — plus the
# contour abscissa σ and the real argument z) is DEFINED as
#   meijerG … σ z = mellinInv σ (fun s => meijerGIntegrand bNum aNum bDen aDen (-s)) z
# with meijerGIntegrand bNum aNum bDen aDen s
#   = (∏ⱼΓ(bNumⱼ−s)·∏ⱼΓ(1−aNumⱼ+s)) / (∏ⱼΓ(1−bDenⱼ+s)·∏ⱼΓ(aDenⱼ−s))   (DLMF 16.17.1 gamma quotient)
# and Mathlib's `mellinInv σ f x = (1/2π)∫ y, x^{-(σ+yi)} • f(σ+yi)` (Methods/Mellin.lean),
# i.e. mellinInv σ f x = 1/(2πi)∫_{(σ)} f(s) x^{-s} ds. Substituting f = (s ↦ g(-s)) with
# g = meijerGIntegrand bNum aNum bDen aDen gives, writing s' = -s inside g:
#   meijerG … σ z = 1/(2πi) ∫_{(σ)} g(-s) z^{-s} ds
#                 = 1/(2πi) ∫_{(σ)} [∏Γ(bNumⱼ+s)·∏Γ(1-aNumⱼ-s)] / [∏Γ(1-bDenⱼ-s)·∏Γ(aDenⱼ+s)] z^{-s} ds
# which is EXACTLY mpmath's defining contour integral for meijerg(a_s, b_s, z) with
#   a_s = (aNum, aDen)   [the n "upper-left" a's, then the p-n "upper-right" a's]
#   b_s = (bNum, bDen)   [the m "lower-left" b's, then the q-m "lower-right" b's]
# and the SAME argument z (no z ↦ -z flip, no z ↦ 1/z flip) — the contour convergence
# side-condition (which vertical line separates which poles) is not re-derived here;
# only the VALUE of the defined limit/integral is compared, exactly as for every other
# oracle binding.
#
# Self-validated (see agent/oracle_bindings.verify()) against:
#   (a) the meijerG_exp anchor  G^{1,0}_{0,1}(z;0) = e^{-z}  (bNum=[0], aNum=bDen=aDen=[]),
#   (b) the meijerG_eq_pFq_zero anchor (same LHS) = pFq(;;-z) = ₀F₀(;;-z) = e^{-z},
#   (c) a genuinely nontrivial q=1 instance of the GENERAL meijerG_eq_pFq shape
#       (bNum=[0], aNum=[1-a], bDen=[1-b], aDen=[]) against (Γ(a)/Γ(b))·₁F₁(a;b;-z),
#   (d) an independent direct mp.quad vertical-line quadrature of the mellinInv
#       contour integral above (decorrelated from mpmath's own meijerg series code),
#       reproduced to ~1e-30 against (a)-(c).
def _meijerG(bNum, aNum, bDen, aDen, z):
    """FLMF `meijerG bNum aNum bDen aDen σ z` (DLMF 16.17.1) via mpmath's Meijer G-function.
    σ (the contour abscissa) does not appear in the mpmath call — mpmath's meijerg picks
    an admissible contour internally, and the FLMF value is INDEPENDENT of σ on any line
    that keeps the two pole families separated (the defining Mellin–Barnes contour
    integral, DLMF §16.17(i)) — so σ is accepted (for call-signature parity with the Lean
    statement) but not otherwise used. bNum/aNum/bDen/aDen are Python lists (already
    evaluated from the Lean `![…]` / `fun _ : Fin 0 => …` vector arguments)."""
    a_s = [list(aNum), list(aDen)]
    b_s = [list(bNum), list(bDen)]
    return mp.meijerg(a_s, b_s, z)


def _double_factorial(n):
    """Mathlib `Nat.doubleFactorial` n‼: 0‼=(−1)‼=1; ℕ-typed ⇒ n ≤ 0 returns 1."""
    n = int(n)
    if n <= 0:
        return mp.mpf(1)
    r = mp.mpf(1)
    while n > 1:
        r *= n; n -= 2
    return r


def _laguerreRodrigues(n, x):
    """FLMF `laguerreRodrigues n x` = (eˣ/n!)·dⁿ/dxⁿ(xⁿ e⁻ˣ) (DLMF 18.5.5, α=0) = Lₙ(x)."""
    n = int(n)
    return mp.e ** x / mp.factorial(n) * mp.diff(lambda t: t ** n * mp.e ** (-t), x, n)


def _hermitePearson_rodrigues(n, x):
    """FLMF `hermitePearson.rodrigues (fun n => (-1)ⁿ) n x` = (−1)ⁿ·w⁻¹·dⁿ/dxⁿ w, w=e^{−x²/2} —
    the probabilists' Heₙ(x)."""
    n = int(n)
    w = lambda t: mp.e ** (-(t ** 2 / 2))
    return (-1) ** n / w(x) * mp.diff(w, x, n)


# ── Pearson-system witness (the abstract DLMF 18.5.5 Rodrigues surface) ──────
# `rodrigues_spec` (Rodrigues.lean) is ∀-quantified over an abstract Pearson system P
# and normalization κ : ℕ → ℝ — unsampleable as scalars, so the sweep skipped it as
# `unbound:k`. Like the IsCDSystem/IsMultiplicative witnesses, the extractor
# instantiates (P, κ) at the canonical Hermite-He row of DLMF Table 18.5.1 / §18.3:
#   w(x) = e^{−x²/2},  F(x) = 1,  κₙ = (−1)ⁿ,  pₙ = Heₙ
# — encoded here from the DLMF table data, NOT from the Lean `hermitePearson` def.
# Anchored in verify() to the 18.5.5 defining identity κₙ·w(x)·pₙ(x) = dⁿ/dxⁿ[w·Fⁿ](x)
# and to the Pearson equation (w·F)′ = w·τ (τ = −x) before the sweep trusts the row.
# Sound as a refutation oracle: a numeric counterexample at the witness disproves the
# ∀-statement; passing is evidence.
def _hermitePearson_w(x):
    """Hermite-He Pearson weight w(x) = e^{−x²/2} (DLMF Table 18.3.1, Heₙ row)."""
    return mp.e ** (-(x ** 2 / 2))


def _hermitePearson_kernel(n, x):
    """DLMF 18.5.5 Rodrigues kernel w(x)·F(x)ⁿ at the Hermite-He row (F = 1)."""
    return _hermitePearson_w(x) * mp.mpf(1) ** int(n)


def _hermitePearson_norm(n):
    """DLMF 18.5.5 normalization κₙ = (−1)ⁿ (Hermite row of Table 18.5.1; the same κₙ
    for the He row: Heₙ(x) = (−1)ⁿ e^{x²/2} dⁿ/dxⁿ e^{−x²/2})."""
    return mp.mpf((-1) ** int(n))


# ── Chapter-7 complex error-function family (cerf/cerfc/Faddeeva/complex Fresnel) ──
# These bind the COMPLEX extensions defined this session by their DLMF defining
# formulas (decorrelated from the Lean segment-integral defs). mpmath's erf/erfc/
# fresnelc/fresnels accept complex arguments; the extractor samples ℂ binders.
_CI = mp.mpc(0, 1)


def _faddeeva(z):
    """Faddeeva w(z) = e^{-z²} erfc(-iz) (DLMF 7.2.3)."""
    return mp.exp(-z ** 2) * mp.erfc(-_CI * z)


def _cfresnelAuxF(z):
    """Complex Fresnel auxiliary f(z) = (½-S)cos(πz²/2) - (½-C)sin(πz²/2) (DLMF 7.2.10)."""
    th = mp.pi * z ** 2 / 2
    return (mp.mpf(1) / 2 - mp.fresnels(z)) * mp.cos(th) - (mp.mpf(1) / 2 - mp.fresnelc(z)) * mp.sin(th)


def _cfresnelAuxG(z):
    """Complex Fresnel auxiliary g(z) = (½-C)cos(πz²/2) + (½-S)sin(πz²/2) (DLMF 7.2.11)."""
    th = mp.pi * z ** 2 / 2
    return (mp.mpf(1) / 2 - mp.fresnelc(z)) * mp.cos(th) + (mp.mpf(1) / 2 - mp.fresnels(z)) * mp.sin(th)


def _cfresnelScriptF(z):
    """Complex Fresnel integral 𝓕(z) = ½(1+i) - (C(z)+iS(z)) (DLMF 7.5.2)."""
    return mp.mpf(1) / 2 * (1 + _CI) - (mp.fresnelc(z) + _CI * mp.fresnels(z))


def _fresnelZeta(z):
    """ζ = ½√π(1-i)z (DLMF 7.5.7, upper sign)."""
    return mp.mpf(1) / 2 * mp.sqrt(mp.pi) * (1 - _CI) * z


def _cdawson(z):
    """Complex Dawson F(z) = (√π/2)e^{-z²}(-i)erf(iz) (= (√π/2)e^{-z²}erfi(z))."""
    return mp.sqrt(mp.pi) / 2 * mp.exp(-z ** 2) * (-_CI) * mp.erf(_CI * z)


def _expIntegralE(p, x):
    """Generalized exponential integral E_p(x) = x^{p-1} Γ(1-p, x) (DLMF 8.19.1)."""
    return x ** (p - 1) * mp.gammainc(1 - p, x, mp.inf)


def _Hh(n, x):
    """Probability function Hhₙ(x) = (1/n!) ∫ₓ^∞ (t-x)ⁿ e^{-t²/2} dt (DLMF §7.18)."""
    n = int(n)
    return (mp.mpf(1) / mp.factorial(n)) * mp.quad(lambda t: (t - x) ** n * mp.exp(-t ** 2 / 2), [x, mp.inf])


# ── Chapter-7 §7.12 asymptotics + §7.17 inverse-erf helpers ───────────────────
# Encoded from the DLMF DEFINING formulas (7.12.4/.5, 7.17.2_5, 7.17.6, 7.17.4),
# NOT copied from the Lean defs.
def _pochHalf(m):
    """FLMF `pochHalf m` = Pochhammer (½)_m = (½)(3/2)…((2m−1)/2) (= Γ(½+m)/Γ(½)).
    Independent rising product: (½)₀=1, (½)₁=½, (½)₂=3/4."""
    m = int(m)
    r, a = mp.mpf(1), mp.mpf(1) / 2
    for j in range(m):
        r *= (a + j)
    return r


def _truncF(n, x):
    """FLMF `truncF n x` = (1/(πx)) Σ_{m=0}^{n-1} (−1)ᵐ (½)_{2m}/(πx²/2)^{2m} (DLMF 7.12.4)."""
    n = int(n)
    return (1 / (mp.pi * x)) * mp.fsum(
        (-1) ** m * _pochHalf(2 * m) / (mp.pi * x ** 2 / 2) ** (2 * m) for m in range(n))


def _truncG(n, x):
    """FLMF `truncG n x` = (1/(πx)) Σ_{m=0}^{n-1} (−1)ᵐ (½)_{2m+1}/(πx²/2)^{2m+1} (DLMF 7.12.5)."""
    n = int(n)
    return (1 / (mp.pi * x)) * mp.fsum(
        (-1) ** m * _pochHalf(2 * m + 1) / (mp.pi * x ** 2 / 2) ** (2 * m + 1) for m in range(n))


def _remF(n, x):
    """FLMF `remF n x` = the f-remainder Rⁿᶠ, DEFINED by its integral (DLMF 7.12.6):
    (−1)ⁿ/(π√2) ∫₀^∞ e^{−πx²t/2} t^{2n−1/2}/(t²+1) dt.  Encoded by quadrature — decorrelated
    from auxF/truncF, so `erf_7_12_4` (f = truncF + remF) is a genuine numerical check."""
    n = int(n)
    # substitute t = u² (so t^{2n-1/2}·dt = 2 u^{4n} du): removes the t^{-1/2} singularity,
    # giving a smooth Gaussian-decay integrand that quadratures to full precision.
    integrand = lambda u: 2 * u ** (4 * n) * mp.exp(-mp.pi * x ** 2 * u ** 2 / 2) / (u ** 4 + 1)
    return ((-1) ** n / (mp.pi * mp.sqrt(2))) * mp.quad(integrand, [0, mp.inf])


def _remG(n, x):
    """FLMF `remG n x` = the g-remainder Rⁿᵍ, DEFINED by its integral (DLMF 7.12.7):
    (−1)ⁿ/(π√2) ∫₀^∞ e^{−πx²t/2} t^{2n+1/2}/(t²+1) dt.  Encoded by quadrature — decorrelated
    from auxG/truncG, so `erf_7_12_5` (g = truncG + remG) is a genuine numerical check."""
    n = int(n)
    # substitute t = u² (so t^{2n+1/2}·dt = 2 u^{4n+2} du): smooth Gaussian-decay integrand.
    integrand = lambda u: 2 * u ** (4 * n + 2) * mp.exp(-mp.pi * x ** 2 * u ** 2 / 2) / (u ** 4 + 1)
    return ((-1) ** n / (mp.pi * mp.sqrt(2))) * mp.quad(integrand, [0, mp.inf])


_INVERFC = {0: mp.mpf(1)}
def _inverf_coeff(k):
    """FLMF `inverfCoeff k` = inverf Maclaurin coefficient aₖ (DLMF 7.17.2_5):
    a₀=1, a_{m+1}=(1/(2m+3)) Σ_{n=0}^{m} ((2n+1)/(m−n+1)) aₙ a_{m−n}; a₀..a₃=1,⅓,7/30,127/630."""
    k = int(k)
    if k not in _INVERFC:
        m = k - 1
        s = mp.fsum(((2 * n + 1) / mp.mpf(m - n + 1))
                    * _inverf_coeff(n) * _inverf_coeff(m - n) for n in range(m + 1))
        _INVERFC[k] = (1 / mp.mpf(2 * m + 3)) * s
    return _INVERFC[k]


def _asymU(x):
    """FLMF `asymU x` = the §7.17 inverfc expansion variable u = −2/ln(π x² ln(1/x))
    (DLMF 7.17.5).  The DLMF leading term is inverfc x ∼ u^{−1/2} (7.17.3); verified
    numerically that THIS form (no extra √) reproduces inverfc — the Lean docstring's
    `√(…)` is a comment slip, the def itself has no √ and is correct.  Real for
    0 < x < 1 with ln(1/x) > 0 and the inner log negative (small x); else mpmath drops."""
    return -2 / mp.log(mp.pi * x ** 2 * mp.log(1 / x))


def _asymV(x):
    """FLMF `asymV x` = the §7.17 inverfc variable v = ln(ln(1/x)) − 2 + ln π (DLMF 7.17.6).
    Real for 0 < x < 1 (else ln(1/x) ≤ 0 → mpmath complex/raise, honest drop)."""
    return mp.log(mp.log(1 / x)) - 2 + mp.log(mp.pi)


def _asymA(x, k):
    """FLMF `asymA x k` = §7.17.4 LOCAL coeffs in v = asymV x: a₂=v/8,
    a₃=−(v²+6v−6)/32, a₄=(4v³+27v²+108v−300)/384, else 0 (DLMF 7.17.4)."""
    k = int(k)
    v = _asymV(x)
    if k == 2:
        return (mp.mpf(1) / 8) * v
    if k == 3:
        return -(mp.mpf(1) / 32) * (v ** 2 + 6 * v - 6)
    if k == 4:
        return (mp.mpf(1) / 384) * (4 * v ** 3 + 27 * v ** 2 + 108 * v - 300)
    return mp.mpf(0)


# 1/Γ Maclaurin coefficients cₖ (DLMF 5.7.1). Built via the DLMF 5.7.2 recurrence
# (c₀=0, c₁=1, c₂=γ; (k−1)cₖ = γc_{k−1} − Σ_{j=2}^{k−1} (−1)ʲζ(j)c_{k−j}), memoized and grown
# incrementally — O(k) per new term. (`mp.taylor(rgamma,0,k)` gives the same coeffs but is
# O(k²) per call → an O(N³) hang over a HasSum sweep; the recurrence builds to order 64 in
# ~0.05 s vs ~17 s.) The 5.7.1 identity Σ cₖ zᵏ = 1/Γ(z) stays an independent check: the RHS
# `1/Γ` is computed separately via `mp.rgamma`, so a mis-stated recurrence would not sum to it.
_RGC = {"prec": None, "vals": [mp.mpf(0)], "boost": 0}
def _recip_gamma_coeff(k):
    k = int(k)
    # The DLMF 5.7.2 recurrence loses ~1 digit/term to cancellation of the ζ(j) tail; at
    # AMBIENT precision the true super-exponential decay of cₖ (1/Γ is order-1 entire) is
    # swamped by rounding and the partial sums SPURIOUSLY BLOW UP (~1e1849 by k~5000),
    # defeating the HasSum convergence test (gamma_5_7_1). Build the whole prefix inside a
    # working precision boosted ∝ k so the decay survives; the returned mpf then rounds back
    # to the ambient prec used by the downstream sum. Rebuild (with headroom) only when the
    # requested k or the ambient precision outgrows the cached boost — a compute-budget
    # change, NOT a tolerance change; the 5.7.1 identity Σcₖzᵏ = 1/Γ(z) stays an independent
    # check (RHS via mp.rgamma).
    need = 30 + 2 * k
    if _RGC["prec"] != mp.mp.prec or _RGC["boost"] < need:
        _RGC["vals"] = [mp.mpf(0)]
        _RGC["prec"] = mp.mp.prec
        _RGC["boost"] = 30 + 4 * k + 200      # headroom so we don't rebuild every increment
    c = _RGC["vals"]
    if len(c) > k:
        return c[k]
    with mp.workdps(mp.mp.dps + _RGC["boost"]):
        while len(c) <= k:
            n = len(c)
            if n == 1:
                c.append(mp.mpf(1))
            elif n == 2:
                c.append(mp.euler)
            else:
                s = mp.fsum([(-1) ** j * mp.zeta(j) * c[n - j] for j in range(2, n)])
                c.append((mp.euler * c[n - 1] - s) / (n - 1))
    return c[k]


# ── OrthogonalPoly-bundle ∀-witness: distinct-real-root count (DLMF §18.2(vi)) ──
def _laguerre_coeffs(n):
    """Exact coefficients, HIGHEST degree first (the mp.polyroots order), of the classical
    Laguerre polynomial L_n(x) = Σ_{k=0}^n (−1)^k C(n,k)/k! · x^k — the DLMF 18.5.12
    explicit sum at α = 0, built from exact integer binomials/factorials (no cancellation;
    anchored in verify() against mpmath's independent mp.laguerre at a generic point)."""
    import math
    return [mp.mpf((-1) ** k * math.comb(int(n), k)) / mp.factorial(k)
            for k in range(int(n), -1, -1)]


def _distinct_real_root_count(coeffs):
    """Number of DISTINCT REAL roots of the polynomial with the given (highest-first)
    coefficients.  Roots via arbitrary-precision mp.polyroots; realness (|Im| below a
    scale-relative threshold) and distinctness (pairwise gap above it) are MEASURED,
    never assumed — a symmetric-Jacobi-matrix eigenvalue shortcut would build in the
    very reality that DLMF §18.2(vi) asserts, destroying refutation power.  The
    threshold 10^(−dps/2)·scale sits ≫ the polyroots residual at +30 dps / 250 extra
    bits and ≪ any true Laguerre root gap (≥ ~0.04 even at n = 24).  Anchored in
    verify() with negative controls (x²+1 → 0, (x−1)² → 1) so the counter cannot
    silently degrade into `degree`.  polyroots non-convergence raises → honest drop."""
    with mp.workdps(mp.mp.dps + 30):
        roots = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=250)
        scale = max([mp.mpf(1)] + [abs(r) for r in roots])
        thr = scale * mp.mpf(10) ** (-(mp.mp.dps // 2))
        real = sorted(mp.re(r) for r in roots if abs(mp.im(r)) <= thr)
        count, prev = 0, None
        for r in real:
            if prev is None or r - prev > thr:
                count += 1
            prev = r
    return count


def _op_bundle_roots_card(env):
    """Head `O.P.roots.toFinset.card` of the abstract OrthogonalPoly-bundle theorems
    (DLMF §18.2(vi): `laguerre_roots_card` / `laguerre_roots_card_eq_degree` in
    Functions/OrthogonalPolynomials/LaguerreZeros.lean and the second conjunct of
    `card_eq_of_nonneg_subset_roots` in Zeros.lean).  Like the Mathieu/Airy ∀-witnesses,
    the quantified bundle `O : OrthogonalPoly μ n` is instantiated at a CANONICAL
    witness: O.P = L_n (classical Laguerre, α = 0, DLMF 18.5.12) with μ = e^{−x}dx on
    (0,∞).  Every bundle field holds at the witness — deg/ne_zero by construction,
    integrable/ortho by Laguerre orthogonality (DLMF 18.3, ∫₀^∞ Lₘ Lₙ e^{−x} dx = δₘₙ),
    nondeg since μ has a density — and the sign-change data (S := the root set, hsign,
    hSroot) is satisfied after scaling P by ±n! (monic normalization); S and the root
    COUNT are invariant under nonzero scaling, so the returned value is
    normalization-independent.  Sound as a refutation oracle: the value is the
    numerically MEASURED number of distinct real roots of L_n, so a mismatch with the
    conclusion at the witness disproves the ∀-statement; PASS is evidence (the
    conclusion at this witness IS DLMF 18.2(vi) for the Laguerre family).  A missing
    degree binder or one outside the polyroots-validated range 1..24 raises →
    honest per-sample drop, never a half-trusted count."""
    nv = env.get("n")
    if nv is None:
        raise ValueError("OrthogonalPoly witness: degree binder `n` not in the sample env")
    n = int(nv)
    if n != nv or not (1 <= n <= 24):
        raise ValueError("OrthogonalPoly witness: n outside the validated range 1..24")
    return mp.mpf(_distinct_real_root_count(_laguerre_coeffs(n)))


# ── A2 Bessel/Struve/Kelvin/Lommel/Anger cluster (lane A2 unbound-head bindings) ─────
def _anger_integrand(nu, z, theta):
    """FLMF `angerIntegrand ν z θ = cos(νθ − z sin θ)` (Bessel/Anger.lean) — the DLMF
    11.10.1 Anger integrand, complex-capable in ν and z. Anchored in verify() by
    quadrature: (1/π)∫₀^π of THIS integrand reproduces mp.angerj at NON-integer ν,
    where Anger J_ν ≠ Bessel J_ν (a J-power-series-based rival is rejected there)."""
    return mp.cos(nu * theta - z * mp.sin(theta))


def _bessel_hankel1(nu, z):
    """FLMF `besselHankel1 ν z = J_ν(z) + i·Y_ν(z)` (BesselHankel.lean; DLMF 10.4.3
    H⁽¹⁾) — built from the SAME mp.besselj/mp.bessely the besselJnu/besselYnu bindings
    use, so definitional rows (10.4.4) stay convention-coherent; anchored against the
    independent mp.hankel1 (the +i sign is the distinguishing point vs H⁽²⁾)."""
    return mp.besselj(nu, z) + mp.mpc(0, 1) * mp.bessely(nu, z)


def _bessel_hankel2(nu, z):
    """FLMF `besselHankel2 ν z = J_ν(z) − i·Y_ν(z)` (DLMF 10.4.3 H⁽²⁾); see _bessel_hankel1."""
    return mp.besselj(nu, z) - mp.mpc(0, 1) * mp.bessely(nu, z)


def _besselI_int(n, z):
    """FLMF `besselI (n : ℤ) z := besselI_nat n.natAbs z` (BesselI.lean) — DLMF 10.25.2
    integer-order I_n. mp.besseli(n,z) at integer n already satisfies I_{−n} = I_n
    (DLMF 10.27.1), the same values the Lean natAbs packaging produces; anchored in
    verify() against the defining series partial sums and the ±n / ±z parities."""
    n = int(n)
    if n != int(mp.mpf(n)):
        raise ValueError("besselI: non-integer order")
    return mp.besseli(n, z)


def _natAbs_env(env):
    """The atom `n.natAbs` (Int.natAbs of the sampled ℤ-binder spelled `n`, e.g.
    `besselI_neg : besselI n (−z) = (−1)^n.natAbs · besselI n z`, DLMF 10.27.1) — an
    env-dependent ATOM via the existing 'envfn' kind (fidelity_extract's DOT0 table has
    no `natAbs`, and that file is parser-lane; this binding uses only the registry
    mechanism). Reads the sampled `n` and returns |n| exactly; a missing or non-integer
    `n` raises → honest per-sample drop."""
    nv = env.get("n")
    if nv is None:
        raise ValueError("natAbs: binder `n` not in the sample env")
    n = int(nv)
    if n != nv:
        raise ValueError("natAbs: sampled n is not an integer")
    return mp.mpf(abs(n))


def _besselJnu_term(nu, z, m):
    """FLMF `besselJnuTerm ν z m = (−1)^m/(Γ(m+1)Γ(m+ν+1))·(z/2)^ν·((z/2)²)^m`
    (BesselJnu.lean; the DLMF 10.2.2 series summand — a TERM, not J_ν itself). The
    `(z/2)^ν` slot is Real.rpow → mp.power (principal branch, same convention the
    evaluator uses for rpow, complex at z<0 → consistent junk, dropped points).
    Γ through _gamma_mathlib so the ν = negative-integer poles reproduce Mathlib's
    reciprocal-zero term drop. Anchored: Σ_m terms = mp.besselj, and the DLMF
    term ratio −(z²/4)/((m+1)(m+ν+1))."""
    m = _nat(m, "besselJnuTerm")
    return ((-1) ** m / (_gamma_mathlib(m + 1) * _gamma_mathlib(m + nu + 1))
            * mp.power(z / 2, nu) * ((z / 2) ** 2) ** m)


def _struve_term(sign, nu, z, m):
    """Shared body of FLMF `struveHTerm`/`struveLTerm ν z m` (Struve.lean; the DLMF
    11.2.1 / 11.2.2 series summands — TERMS, not H_ν/L_ν):
    sign^m/(Γ(m+3/2)Γ(m+ν+3/2))·(z/2)^{ν+1}·((z/2)²)^m, sign = −1 (H) / +1 (L).
    rpow slot via mp.power as in _besselJnu_term. Anchored: Σ_m = mp.struveh/struvel
    and the DLMF term ratio ∓(z²/4)/((m+3/2)(m+ν+3/2))."""
    m = _nat(m, "struveTerm")
    return (sign ** m / (_gamma_mathlib(m + mp.mpf(3) / 2) * _gamma_mathlib(m + nu + mp.mpf(3) / 2))
            * mp.power(z / 2, nu + 1) * ((z / 2) ** 2) ** m)


def _besselK_cosh(nu, x):
    """FLMF `besselK_cosh ν x = ∫₀^∞ e^{−x cosh t} cosh(νt) dt` (KMonotone.lean) —
    DLMF 10.32.9: equals K_ν(x) for x > 0. For x ≤ 0 the Lean Lebesgue integral is
    junk (divergent integrand) — raise → honest drop, same policy as _besselK_real.
    Anchored in verify() by direct quadrature of the DEFINING integral (rejects the
    one-sided e^{−x cosh t − νt} rival, which needs the full line ∫_{−∞}^∞/2)."""
    if mp.im(x) != 0 or mp.re(x) <= 0:
        raise ValueError("besselK_cosh: x ≤ 0 (integral diverges)")
    return mp.besselk(nu, x)


def _lommel_small_s(mu, nu, z):
    """FLMF `lommelS μ ν z = z^{μ+1}·Σ_k (−1)^k z^{2k}/∏_{j=0}^k((μ+2j+1)²−ν²)`
    (Lommel.lean) — the Lommel s_{μ,ν}(z) of DLMF 11.9.3. Since
    ∏_{j=0}^k((μ+2j+1)²−ν²) = 4^{k+1}·((μ−ν+1)/2)_{k+1}·((μ+ν+1)/2)_{k+1}, the sum is
    ₁F₂(1; (μ−ν+3)/2, (μ+ν+3)/2; −z²/4)/((μ+1)²−ν²) — evaluated through mp.hyper
    (independent of the Lean partial-product route). z^{μ+1} is Complex.cpow →
    mp.power principal branch. Degenerate μ±ν odd-negative-integer denominators raise
    → honest drop. Anchored: s_{ν,ν}(z) = 2^{ν−1}√π Γ(ν+½)·H_ν(z) against mp.struveh."""
    d0 = (mu + 1) ** 2 - nu ** 2
    if d0 == 0:
        raise ValueError("lommelS: (μ+1)² = ν² (degenerate leading denominator)")
    return (mp.power(z, mu + 1) / d0
            * mp.hyper([1], [(mu - nu + 3) / 2, (mu + nu + 3) / 2], -z ** 2 / 4))


def _lommel_big_gamma(mu, nu):
    """FLMF `lommelBigGamma μ ν = 2^{μ−1}Γ((μ+ν+1)/2)Γ((μ−ν+1)/2)` (LommelBig.lean) —
    the DLMF 11.9.5 prefactor. Γ poles → Mathlib junk handled by _gamma_mathlib."""
    return (mp.power(2, mu - 1) * _gamma_mathlib((mu + nu + 1) / 2)
            * _gamma_mathlib((mu - nu + 1) / 2))


def _lommel_big_homog(Jnu, Ynu, mu, nu):
    """FLMF `lommelBigHomog Jν Yν μ ν` — the homogeneous Bessel combination of DLMF
    11.9.5: lommelBigGamma·(sin((μ−ν)π/2)·Jν − cos((μ−ν)π/2)·Yν), with Jν/Yν the
    ∀-quantified Bessel DATA scalars of the Lean statement (sampled freely)."""
    return (_lommel_big_gamma(mu, nu)
            * (mp.sin((mu - nu) * mp.pi / 2) * Jnu - mp.cos((mu - nu) * mp.pi / 2) * Ynu))


def _lommel_big_S(Jnu, Ynu, mu, nu, z):
    """FLMF `lommelBigS Jν Yν μ ν z = lommelS μ ν z + lommelBigHomog Jν Yν μ ν` —
    the Lommel S_{μ,ν}(z) of DLMF 11.9.5 given Bessel data. Anchored in verify() with
    GENUINE Bessel data: S_{ν,ν}(z) = 2^{ν−1}√π Γ(ν+½)(H_ν−Y_ν)(z) (the Struve-K form,
    pinning the cos/Y placement and both Γ arguments), and the algebraic large-z decay
    S_{μ,ν}(z)·z^{1−μ} → 1 (DLMF 11.9.9 — the property that DISTINGUISHES S from s and
    pins the sin/J placement: any homogeneous-part error leaves an O(z^{−1/2})
    oscillating residual that bare s exhibits and S must not)."""
    return _lommel_small_s(mu, nu, z) + _lommel_big_homog(Jnu, Ynu, mu, nu)


def _lin_ord(x, what):
    """A sampled value as an element of a LINEAR order (ℕ/ℤ/ℚ/ℝ), or RAISE.  Lean's
    `max`/`min` are the lattice operations of a `LinearOrder`; ℂ carries none, so a
    complex operand can only come from a mis-typed sample — drop the point honestly
    instead of inventing an order.  An `mpc` with exactly zero imaginary part is the
    sweep's real value in complex clothing (ℕ→ℂ casts) and is accepted as its real
    part."""
    if isinstance(x, mp.mpc):
        if x.imag != 0:
            raise ValueError(f"{what}: complex operand has no linear order")
        return x.real
    return x


def _lin_max(x, y):
    """Lean/Mathlib `max` on a LinearOrder (`Nat.max`, `Rat.max`, `Real.max` — the
    same `⊔` in every case): the larger of the two operands."""
    x, y = _lin_ord(x, "max"), _lin_ord(y, "max")
    return x if x >= y else y


def _lin_min(x, y):
    """Lean/Mathlib `min` on a LinearOrder: the smaller of the two operands."""
    x, y = _lin_ord(x, "min"), _lin_ord(y, "min")
    return x if x <= y else y


def _heun_quadrature_genus(m):
    """FLMF `heunQuadratureGenus m` (Frameworks/Heun/Quadratures.lean) — the `λ`-degree
    (genus) of the Heun quadrature polynomial `Ψ_{g,N}`, **DLMF 31.8.3**:

        g = ½ max(2 max_{0≤k≤3} m_k,  1 + N − (1 + (−1)^N)(½ + min_{0≤k≤3} m_k)),
        N = m₀+m₁+m₂+m₃  (`heunQuadratureDegree`).

    `m : Fin 4 → ℕ` arrives as the sweep's pointwise-sampled `absfnN` callable, so the
    four entries are read at indices 0..3 (the arity is `Fin 4` in the Lean type, not a
    property of the callable).  Entries are coerced through `_nat`, so a non-natural
    sample drops the point rather than fabricating a value.  Arithmetic is EXACT
    `fractions.Fraction` (the Lean value lives in ℚ) and returned as an mp value.

    Anchored in `verify()` NOT by re-typing this display but by DLMF's own two worked
    members — 𝐦 = (1,1,0,0) must give the `Ψ_{1,2}` of 31.8.4 (g = 1) and 𝐦 = (1,−2,0,0)
    the `Ψ_{1,−1}` of 31.8.5 (g = 1), each independently confirmed to be the λ-degree of
    the symmetric-square solution — together with the structural integrality both
    arguments of the outer max are even, so g ∈ ℕ (docs/verification/ch31/
    probe_quadratures.py)."""
    from fractions import Fraction as _F
    ms = [_nat(m(k), "heunQuadratureGenus") for k in range(4)]
    N = sum(ms)
    lhs = _F(2 * max(ms))
    rhs = 1 + _F(N) - (1 + _F(-1) ** N) * (_F(1, 2) + _F(min(ms)))
    g = _F(1, 2) * (lhs if lhs >= rhs else rhs)
    return mp.mpf(g.numerator) / mp.mpf(g.denominator)


def _heun_psi_1_2(a, lam, z):
    """FLMF `heunPsi_1_2 a lam z` — the Heun quadrature polynomial for 𝐦 = (1,1,0,0),
    **DLMF 31.8.4**:  `Ψ_{1,2}(λ,z) = z² + λz + a`.  Anchored in `verify()` by the
    §31.8 DEFINING characterization (it solves the third-order symmetric-square equation
    of Heun's equation at q = −λ/4 with the 31.8.1 exponents of that 𝐦), never by name;
    see docs/verification/ch31/probe_quadratures.py."""
    return z ** 2 + lam * z + a


def _heun_nusq_1_2(a, lam):
    """FLMF `heunNuSq_1_2 a lam` — the squared spectral variable accompanying
    `Ψ_{1,2}`, **DLMF 31.8.4**:  `ν² = (λ + a + 1)(λ² − 4a)`.  Anchored in `verify()`
    by the Wronskian first integral of the 31.8.2 ansatz, which determines ν² from Ψ
    alone (`(Ψ′)² − 2ΨΨ″ − 2PΨΨ′ − 4QΨ² = W² = −ν² z^{2m₁−1}(z−1)^{2m₂−1}(z−a)^{2m₃−1}`),
    never by re-typing this display."""
    return (lam + a + 1) * (lam ** 2 - 4 * a)


def _heun_psi_1_neg1(a, lam, z):
    """FLMF `heunPsi_1_neg1 a lam z` — the quadrature FUNCTION for 𝐦 = (1,−2,0,0),
    **DLMF 31.8.5** (post-errata V1.0.7 numerator `z²`):

        Ψ_{1,−1}(λ,z) = (z² + (λ + 3a + 3)z + a)/z³        (N = −1, rational in z).

    Total via the Lean field convention `x/0 = 0`: the value at z = 0 is the junk 0,
    reproduced here rather than raising, so the shadow matches the Lean def exactly.
    Anchored in `verify()` by the §31.8 symmetric-square characterization at the 31.8.1
    exponents of 𝐦 = (1,−2,0,0) (γ = 5/2, δ = ε = 1/2, α = 1/2, β = 2)."""
    if z == 0:
        return mp.mpf(0)
    return (z ** 2 + (lam + 3 * a + 3) * z + a) / z ** 3


def _heun_nusq_1_neg1(a, lam):
    """FLMF `heunNuSq_1_neg1 a lam` — the squared spectral variable accompanying
    `Ψ_{1,−1}`, **DLMF 31.8.5**:  `ν² = (λ + 4a + 4)((λ + 3a + 3)² − 4a)`.  Anchored in
    `verify()` by the same Wronskian first integral as `_heun_nusq_1_2` (here with
    m₁ = −2, so W² = −ν² z^{−5}(z−1)^{−1}(z−a)^{−1})."""
    return (lam + 4 * a + 4) * ((lam + 3 * a + 3) ** 2 - 4 * a)


# head symbol (as it appears in a Lean conclusion)  ->  binding
REGISTRY = {
    # constants
    "π":          ("const", mp.pi),
    "Real.pi":    ("const", mp.pi),
    "Real.exp 1": ("const", mp.e),          # rarely needed; exp handled as fn below
    # elementary real functions (1-ary unless noted)
    "exp":     ("fn", lambda a: mp.e ** a),     "Real.exp":  ("fn", lambda a: mp.e ** a),
    # CONVENTION (FIDELITY.md §5): Mathlib `Real.log x = log|x|` (and log 0 = 0) — NOT the
    # principal complex log mpmath gives at x<0. Binding by name (→ mp.log) is wrong and
    # fabricates a 2π·i branch mismatch on `log(xy)=logx+logy` for negative reals.
    "log":     ("fn", lambda a: _log_auto(a)),  "Real.log":  ("fn", lambda a: _rlog(a)),
    # Mathlib `Real.sqrt x = 0` for x < 0 (junk value), not the complex root.
    "sqrt":    ("fn", lambda a: _rsqrt(a)),     "Real.sqrt": ("fn", lambda a: _rsqrt(a)),
    "cos":     ("fn", mp.cos),                  "Real.cos":  ("fn", mp.cos),
    "sin":     ("fn", mp.sin),                  "Real.sin":  ("fn", mp.sin),
    "tan":     ("fn", mp.tan),                  "Real.tan":  ("fn", mp.tan),
    "cot":     ("fn", mp.cot),                  "Real.cot":  ("fn", mp.cot),
    "cosh":    ("fn", mp.cosh),                 "Real.cosh": ("fn", mp.cosh),
    "sinh":    ("fn", mp.sinh),                 "Real.sinh": ("fn", mp.sinh),
    "tanh":    ("fn", mp.tanh),                 "Real.tanh": ("fn", mp.tanh),
    "arctan":  ("fn", mp.atan),                 "Real.arctan": ("fn", mp.atan),
    # Mathlib Real.artanh = ½ ln((1+x)/(1−x)) — junk outside (−1,1) via Real.log|·|;
    # mp.atanh matches on the principal interval (the 14.5.7/14.5.8 Q₀/Q₁ rows carry
    # |x| < 1 domains or sample inside it).
    "artanh":  ("fn", mp.atanh),                "Real.artanh": ("fn", mp.atanh),
    # CONVENTION (§5): Mathlib `Real.arcsin`/`Real.arccos` CLAMP the argument to [−1,1]
    # (arcsin 1.7 = π/2), so identities like cos(arcsin x)=√(1−x²) hold unconditionally —
    # mpmath's asin/acos go complex outside [−1,1]. Bind through a clamp.
    "arcsin":  ("fn", lambda a: mp.asin(_clamp(a))),  "Real.arcsin": ("fn", lambda a: mp.asin(_clamp(a))),
    "arccos":  ("fn", lambda a: mp.acos(_clamp(a))),  "Real.arccos": ("fn", lambda a: mp.acos(_clamp(a))),
    # DLMF 15.4.4 principal complex arcsin (file-local def, Ch15SpecialCases.lean:42),
    # bound to its literal defining formula −i·log((1−z²)^{1/2}+i·z) on the unit disc.
    "principalComplexArcsin": ("fn", _principal_complex_arcsin),
    "abs":     ("fn", abs),                     "|·|":       ("fn", abs),
    # Lattice `max`/`min` of a LinearOrder (ℕ/ℤ/ℚ/ℝ) — the same `⊔`/`⊓` in Lean for every
    # such carrier, so one binding is faithful for all of them.  A complex operand RAISES
    # (ℂ has no LinearOrder, so it can only be a mis-typed sample) → honest point drop.
    "max":     ("fn", _lin_max),                "min":       ("fn", _lin_min),
    # complex ENTIRE functions — same mpmath call (complex-native, no branch-cut subtlety).
    # NOTE: Complex.log is deliberately NOT aliased — it carries a principal-branch
    # convention distinct from the Real `log|·|` one, so binding it needs §5 care.
    # Mathlib `Complex.sqrt a = a ^ (2⁻¹ : ℂ)` (RCLike/Sqrt.lean) IS the principal square
    # root exp(Log a / 2) with sqrt 0 = 0 — exactly mpmath's mp.sqrt (same cut (−∞,0),
    # same arg = π convention on it, sqrt(−4) = 2i both sides).
    "Complex.sqrt": ("fn", lambda a: mp.sqrt(mp.mpc(a))),
    "Complex.exp":  ("fn", lambda a: mp.e ** a),  "cexp": ("fn", lambda a: mp.e ** a),
    "Complex.cos": ("fn", mp.cos),
    "Complex.sin":  ("fn", mp.sin),               "Complex.cosh": ("fn", mp.cosh),
    "Complex.sinh": ("fn", mp.sinh),              "Complex.Gamma": ("fn", mp.gamma),
    "Complex.tan":  ("fn", mp.tan),               "Complex.tanh": ("fn", mp.tanh),
    "Complex.cot":  ("fn", mp.cot),
    "Complex.I":    ("const", mp.mpc(0, 1)),  "I": ("const", mp.mpc(0, 1)),
    # Mathlib `Complex.normSq z = (re z)² + (im z)²` — the squared modulus |z|², a REAL
    # value (the DLMF §1.9(i) |z|² = x² + y²; e.g. the §27.8 Gauss-sum magnitude
    # `normSq (gaussSum χ e) = p`). Computed from the defining re/im form; anchored in
    # verify() against the independent |z|² = z·z̄ and through the full Gauss-sum path.
    "Complex.normSq": ("fn", lambda z: mp.re(z) ** 2 + mp.im(z) ** 2),
    "normSq": ("fn", lambda z: mp.re(z) ** 2 + mp.im(z) ** 2),
    # Mathlib's Complex.betaIntegral u v = ∫₀¹ t^(u-1)(1-t)^(v-1) dt = B(u,v) = Γu·Γv/Γ(u+v).
    # mpmath's mp.beta has exactly this normalization (anchored at B(1,1)=1, B(2,3)=1/12 below).
    "Complex.betaIntegral": ("fn", lambda u, v: mp.beta(u, v)),
    # special functions — convention-pinned
    # Mathlib Γ has the junk value 0 at its non-positive-integer poles (mpmath raises there);
    # _gamma_mathlib mirrors that so series terminating via 1/Γ = 0 (DLMF 7.18.6) sum faithfully.
    "Gamma":       ("fn", _gamma_mathlib),       "Real.Gamma": ("fn", _gamma_mathlib),
    # Mathlib riemannZeta is standard ζ away from 1 and carries a finite totalized
    # placeholder at 1; the wrapper mirrors both parts.
    "riemannZeta":  ("fn", _riemann_zeta_mathlib),
    "bernoulli":   ("fn", _bernoulli_mathlib),
    # picard-lefschetz `periodicBernoulli k x = Bₖ(Int.fract x)` (EulerMaclaurin.lean) —
    # the Bernoulli POLYNOMIAL at the fractional part {x} = x − ⌊x⌋ (matches Int.fract
    # for negative x too: {−0.3} = 0.7).
    "periodicBernoulli": ("fn", lambda k, x: mp.bernpoly(int(k), x - mp.floor(x))),
    "bernoulli'":  ("fn", _bernoulli_prime_mathlib),
    # FLMF eulerNumberQ n = n!·secCoeff n (EulerNumbers.lean) — the Euler numbers Eₙ of the
    # DLMF 24.2.6 generating function 2eᵗ/(e²ᵗ+1) = sech t = Σ Eₙ tⁿ/n!. mp.eulernum is that
    # SIGNED sech convention: anchored below at E₂=−1 (rejects the unsigned secant numbers,
    # |E₂|=1) and E₃=0 (rejects the zigzag/up-down numbers, A₃=2), cross-checked against the
    # defining sech Taylor coefficient at n=6 and the DLMF Table 24.2 value E₁₀=−50521.
    "eulerNumberQ": ("fn", lambda n: mp.eulernum(_nat(n, "eulerNumberQ"))),
    # FLMF tangentNumberQ n = n!·tanCoeff n (EulerNumbers.lean) — the tangent numbers Tₙ of
    # the DLMF §24.15(iii) generating function tan t = Σ Tₙ tⁿ/n! (T₀=0, T₁=1, T₃=2, T₅=16,
    # T₇=272; 0 at even n). Exact Bernoulli closed form DLMF 24.15.4; anchored below against
    # the defining Taylor coefficient n!·[tⁿ]tan t and T₂=0 (rejects the compressed
    # odd-only indexing, which would put T₂=2).
    "tangentNumberQ": ("fn", _tangent_number),
    # constants
    "eulerMascheroniConstant": ("const", mp.euler),
    "eulerMascheroni":         ("const", mp.euler),   # FLMF abbrev for the same constant
    "Real.eulerMascheroniConstant": ("const", mp.euler),
    "glaisherKinkelin":        ("const", mp.glaisher),
    # Bessel family (DLMF 10) — argument order f(order, x)
    # Anger/Weber — Lean defs are LITERALLY DLMF 11.10.1/11.10.4 ((1/π)∫₀^π cos/sin(νθ−z sinθ)dθ);
    # mpmath angerj/webere anchored against that defining integral below. Complex-capable.
    "angerJ": ("fn", mp.angerj),  "weberE": ("fn", mp.webere),
    # Barnes G — Lean barnesGNat: G(0)=0, G(n+1)=∏_{k<n} k!; mp.barnesg agrees incl. G(0)=0.
    "barnesGNat": ("fn", lambda n: mp.barnesg(int(n))),
    # Lean incompleteBeta a b x = ∫₀ˣ t^(a−1)(1−t)^(b−1) dt — UNregularized = betainc(a,b,0,x).
    "incompleteBeta": ("fn", lambda a, b, x: mp.betainc(a, b, 0, x)),
    # ── Chapter-5 (Gamma) surface helpers ──
    # Lean lahNumber n k (Ch5SpecialValues, DLMF §5.2.9): unsigned Lah L(n,k)=C(n-1,k-1)·n!/k!
    # for 1≤k≤n, L(0,0)=1, L(n,0)=0 (n≥1), and 0 for k>n. Anchored by that defining formula.
    "lahNumber": ("fn", lambda n, k: (mp.mpf(1) if int(n) == 0 else mp.mpf(0)) if int(k) == 0
                  else mp.binomial(int(n) - 1, int(k) - 1) * mp.factorial(int(n)) / mp.factorial(int(k))),
    # Lean qFactorial n q (Ch5QGamma, DLMF 5.18.2): n!_q = ∏_{k=1}^n [k]_q, [k]_q=(1-q^k)/(1-q).
    "qFactorial": ("fn", lambda n, q: mp.fprod([mp.fsum([mp.mpf(q) ** j for j in range(k + 1)])
                                                for k in range(int(n))])),
    # Lean qGamma z q (FLMF.QSeries, DLMF 5.18): Γ_q(z) = (q;q)_∞ / (q^z;q)_∞ · (1-q)^{1-z}, for
    # 0<q<1. Anchored by evaluating that very defining product ((a;q)_∞ = mp.qp(a,q)), the
    # strongest §5 tie; matches mp.qgamma to 1e-15 and gives Γ_q(1)=Γ_q(2)=1. Arg order (z,q).
    "qGamma": ("fn", lambda z, q: mp.qp(mp.mpf(q), q) / mp.qp(mp.mpf(q) ** z, q)
               * (1 - mp.mpf(q)) ** (1 - z)),
    # Lean qBeta x y q (FLMF.QSeries, DLMF 5.18.11): B_q(x,y) = Γ_q(x)Γ_q(y)/Γ_q(x+y), for 0<q<1
    # (decorrelated as the same Γ_q product at three points). Arg order (x,y,q).
    "qBeta": ("fn", lambda x, y, q: (mp.qp(mp.mpf(q), q) / mp.qp(mp.mpf(q) ** x, q) * (1 - mp.mpf(q)) ** (1 - x))
              * (mp.qp(mp.mpf(q), q) / mp.qp(mp.mpf(q) ** y, q) * (1 - mp.mpf(q)) ** (1 - y))
              / (mp.qp(mp.mpf(q), q) / mp.qp(mp.mpf(q) ** (x + y), q) * (1 - mp.mpf(q)) ** (1 - (x + y)))),
    # Lean recipGammaCoeff k (Ch5SeriesProducts, DLMF 5.7.1): the k-th Maclaurin coefficient of
    # 1/Γ(z) at z=0 (c₀=0, c₁=1, c₂=γ, …). Anchored by the DLMF defining property, not the recurrence.
    "recipGammaCoeff": ("fn", _recip_gamma_coeff),
    # Lean Bre a b (Ch5BetaCF, DLMF 5.12.1): the real Beta B(a,b) = Γ(a)Γ(b)/Γ(a+b). Arg order (a,b).
    "Bre": ("fn", lambda a, b: mp.gamma(a) * mp.gamma(b) / mp.gamma(a + b)),
    # Mathlib `Complex.digamma z = logDeriv Γ z = Γ'(z)/Γ(z)` (the complex digamma ψ). mpmath
    # mp.digamma accepts complex and is the same branch (anchored ψ(1)=−γ, ψ(1+i)=0.09465+1.07667i).
    "Complex.digamma": ("fn", mp.digamma),
    # Mathlib `Complex.log` — principal complex logarithm (Im ∈ (−π,π]); = mp.log on the same cut.
    "Complex.log": ("fn", mp.log),
    # Lean ellipticF φ k = ∫₀^φ dt/√(1−k²sin²t) uses MODULUS k; mp.ellipf takes PARAMETER m=k².
    # The k-vs-m trap is real: ellipf(1.1, 0.6) differs from the Lean def by 0.0666 (anchored).
    "ellipticF": ("fn", lambda phi, k: _elliptic_junk(phi, k, "F")),
    # Lean ellipticE φ k = ∫₀^φ √(1−k²sin²t) dt (FLMF.EllipticIntegrals, DLMF 19.2.5) — same
    # MODULUS-k convention; the two-arg mp.ellipe(φ, m) is the incomplete E of PARAMETER m=k²
    # (anchored against the defining quadrature; k-as-m would be off by 0.0485 at (1.1, 0.6)).
    "ellipticE": ("fn", lambda phi, k: _elliptic_junk(phi, k, "E")),
    # Lean modSpherical i/k use the no-π/2 convention (i₀=sinh z/z, k₀=e^{−z}/z). Bound via the
    # DLMF Rayleigh CLOSED FORM + recurrence (10.49.8/.12, 10.51.4/.5): the Bessel-quotient form
    # √(π/2z)·I_{n+½} / √(2/πz)·K_{n+½} is real only for z>0 and goes complex on the z<0 sample.
    "modSphericalI": ("fn", _mod_spherical_i),
    "modSphericalK": ("fn", _mod_spherical_k),
    # Lean assocLegendre n m x = (−1)^m (1−x²)^{m/2} dᵐPₙ/dxᵐ (Ferrers, Condon–Shortley IN);
    # mp.legenp carries the same phase on (−1,1) (anchored at P₁¹, P₂¹).
    "assocLegendre": ("fn", lambda n, m, x: mp.legenp(int(n), int(m), x)),
    # error-function family — Lean erf = (2/√π)∫₀ˣe^{−t²}dt (standard); Dawson F(x)=e^{−x²}∫₀ˣe^{t²}dt
    # has no mpmath builtin → composed via erfi: F = (√π/2)·e^{−x²}·erfi(x) (anchored vs the integral).
    "erf":  ("fn", mp.erf),   "erfc": ("fn", mp.erfc),
    "dawson": ("fn", lambda x: mp.sqrt(mp.pi) / 2 * mp.exp(-x ** 2) * mp.erfi(x)),
    "arsinh": ("fn", mp.asinh),  "Real.arsinh": ("fn", mp.asinh),
    "besselJ_nat": ("fn", lambda n, x: mp.besselj(int(n), x)),
    "besselJ_int": ("fn", lambda n, x: mp.besselj(int(n), x)),
    "besselI_nat": ("fn", lambda n, x: mp.besseli(int(n), x)),
    # complex-argument integer-order J/I (FLMF Kelvin module series defs besselJC/besselIC,
    # DLMF 10.2.2 / 10.25.2) — mpmath's complex-native besselj/besseli. Binding these breaks
    # the SELF-REFERENTIAL evaluation of the Kelvin rows (kelvinBer/Bei are re/im of
    # besselJC(x·e^{3πi/4}); with no external anchor Tier-1 was checking the defs against
    # themselves). kelvinBer/kelvinBei bind to mpmath's OWN independent ber/bei — verified
    # against the Lean convention (incl. x < 0) to ~1e-31 before adoption.
    "besselJC": ("fn", lambda n, z: mp.besselj(int(n), z)),
    "besselIC": ("fn", lambda n, z: mp.besseli(int(n), z)),
    "kelvinBer": ("fn", lambda n, x: mp.ber(int(n), x)),
    "kelvinBei": ("fn", lambda n, x: mp.bei(int(n), x)),
    # complex Y_n / K_n / Hankel (Kelvin module series defs, DLMF 10.8.1 / 10.31.1 /
    # 10.4.3) and the concrete ker/kei pair (DLMF 10.61.2) — all mpmath complex-native;
    # ker/kei convention verified against e^{−nπi/2}K_n(x·e^{πi/4}) to ~1e-29.
    "besselYC": ("fn", lambda n, z: mp.bessely(int(n), z)),
    "besselKC": ("fn", lambda n, z: mp.besselk(int(n), z)),
    "hankel1C": ("fn", lambda n, z: mp.hankel1(int(n), z)),
    "hankel2C": ("fn", lambda n, z: mp.hankel2(int(n), z)),
    "kelvinKer": ("fn", lambda n, x: mp.ker(int(n), x)),
    "kelvinKei": ("fn", lambda n, x: mp.kei(int(n), x)),
    "besselJ0": ("fn", lambda x: mp.besselj(0, x)),  "besselJ1": ("fn", lambda x: mp.besselj(1, x)),
    "besselI0": ("fn", lambda x: mp.besseli(0, x)),  "besselI1": ("fn", lambda x: mp.besseli(1, x)),
    # junk-0 at z≤0 mirrors FLMF's ∫₀^∞ e^{−z cosh t} dt (divergent → Lean ∫=0); the
    # no-hypothesis bridge row besselK0_eq_tricomiU holds via mutual junk-0, and every other
    # K₀/K₁ row carries z>0 so the gate never samples z≤0 there.
    "besselK0": ("fn", lambda z: mp.mpf(0) if z <= 0 else mp.besselk(0, z)),
    "besselK1": ("fn", lambda z: mp.mpf(0) if z <= 0 else mp.besselk(1, z)),
    # fully-qualified alias (the §6.7 K₀-integral surfaces print the qualified name in
    # their conclusions — same precedent as FLMF.ExpIntegrals.Def.Ei above).
    "FLMF.Functions.Bessel.besselK0": ("fn", lambda z: mp.mpf(0) if z <= 0 else mp.besselk(0, z)),
    # higher fixed orders (DLMF 10.6.1 / 10.29.1 recurrences) — mpmath's independent Jₙ/Kₙ,
    # anchored against the FLMF defining forms J₂ = 2J₁/z − J₀ and K₂ = K₀ + (2/z)K₁ below.
    # (The K recurrence carries a MINUS sign — see docs/ERRATA.md `besselk2-sign-error`,
    # fixed in FLMF/Functions/Bessel/Basic.lean.)
    "besselJ2": ("fn", lambda z: mp.besselj(2, z)),  "besselK2": ("fn", lambda z: mp.besselk(2, z)),
    # spherical Bessel jₙ/yₙ via the DLMF Rayleigh closed form + recurrence (10.49.3/.5, 10.51.1):
    # j₀=sin x/x, j₁=sin x/x²−cos x/x; y₀=−cos x/x, y₁=−cos x/x²−sin x/x. The √(π/2x)·C_{n+½} form
    # is real only for x>0 and disagrees in sign on the x<0 grid sample (so it false-FAILed).
    "sphericalJ": ("fn", _sphericalj),
    "sphericalY": ("fn", _sphericaly),
    # Voigt U(x,t), V(x,t) (DLMF 7.19.1 integral; 7.19.2/.3 closed form): U+iV = √(π/4t)·e^{z²}·
    # erfc(z) with z=(1−ix)/(2√t) — equivalently (√π/2√t)·w((i+x)/2√t). Real/imag parts. Heads
    # `Voigt`/`FLMF` strip to these. t>0 required (kernel non-normalizable otherwise).
    "voigtU": ("fn", _voigt_u),
    "voigtV": ("fn", _voigt_v),
    # FULLY-QUALIFIED spherical-Bessel heads: the chapter-7 (Error) rows cite them as
    # `FLMF.Bessel.sphericalJ`/`modSphericalI`, and `Bessel` is NOT a strippable namespace
    # segment, so they must bind exactly here (same closed-form helpers as the short keys).
    "FLMF.Bessel.sphericalJ": ("fn", _sphericalj),
    "FLMF.Bessel.sphericalY": ("fn", _sphericaly),
    "FLMF.Bessel.modSphericalI": ("fn", _mod_spherical_i),
    "FLMF.Bessel.modSphericalK": ("fn", _mod_spherical_k),
    # Parabolic cylinder U(a,x) (DLMF 12.2.6–7, 12.4.1) — the recessive solution of
    # w''−(¼x²+a)w=0 = mp.pcfu(a,x) (anchored: solves Weber's eqn, matches FLMF's even/odd
    # assembly + U(a,0)=√π 2^{−¼−a/2}/Γ(¾+a/2)). FULLY-QUALIFIED key so it never collides with
    # the Chebyshev second-kind poly `U` (the namespace stripper's guard would skip a `U` leaf).
    #
    # *** BINDING RE-ENABLED (2026-06-27). *** Previously withheld 2026-06-26 because its only
    # chapter-7 consumer `erf_7_18_11` carried the wrong power of two, `2^{n−1}` where DLMF 7.18.11
    # needs `2^{(n−1)/2}`. The Lean exponent has since been corrected to `2^{((n−1)/2)}`
    # (Ch7RepeatedErfc.lean:152) and ERRATA `repeated-erfc-pcf-pow2` is marked Fixed; the row now
    # PASSES (LHS/RHS rel-err ≤ 2.7e-17 over n=0..4, z∈{0.6,1.3,−0.8,2.0}). Binding self-validated:
    # mp.pcfu matches the DLMF 12.2.6 anchor U(a,0)=√π·2^{−¼−a/2}/Γ(¾+a/2) to ~1e-31 and solves
    # Weber's eqn w''−(¼x²+a)w=0.
    "FLMF.ParabolicCylinder.U": ("fn", lambda a, x: mp.pcfu(a, x)),
    # Legendre P/Q (DLMF 14)
    "legendre":  ("fn", lambda n, x: mp.legendre(int(n), x)),
    "legendreQ": ("fn", lambda l, x: mp.legenq(int(l), 0, x)),
    # bracket notations `P[l] x`/`Q[l] x`/`P[n,m] x` (Lean `notation "P[" l "]" => legendre`
    # etc.) — the parser emits these synthetic heads; they reuse the bindings above.
    "P[]":  ("fn", lambda l, x: mp.legendre(int(l), x)),
    "Q[]":  ("fn", lambda l, x: mp.legenq(int(l), 0, x)),
    "P[,]": ("fn", lambda n, m, x: mp.legenp(int(n), int(m), x)),     # associated Pₙᵐ
    # weighted-orthogonality normalization constants (exact closed forms)
    "normalizationConst": ("fn", lambda n: mp.pi if int(n) == 0 else mp.pi / 2),  # Chebyshev hₙ
    "legendreNormConst":  ("fn", lambda n: 2 / (2 * mp.mpf(n) + 1)),              # Legendre 2/(2n+1)
    # degenerate spheroidal eigenvalue λₙ = n(n+1) (DLMF 30.3.3 at γ=0, μ=0) — the
    # Legendre-ODE eigenvalue (Spheroidal/Eigenvalues.lean); ODE-anchored in verify()
    "legendreEigenvalue": ("fn", _legendre_eigenvalue),
    # incomplete Gamma (DLMF 8.2): lower γ(a,x) + upper Γ(a,x) = Γ(a)
    "upperGamma": ("fn", lambda a, x: mp.gammainc(a, x, mp.inf)),
    "lowerGamma": ("fn", lambda a, x: mp.gammainc(a, 0, x)),
    # Jacobi elliptic (DLMF 22) — 2nd arg = modulus k → mpmath parameter m = k²
    "jacobiSn": ("fn", _jacobi("sn")), "jacobiCn": ("fn", _jacobi("cn")),
    "jacobiDn": ("fn", _jacobi("dn")),
    # τ-parametrized Jacobi elliptic functions (DLMF 22.2.4–6) via theta quotients — the
    # bare `sn z τ`/`cn`/`dn` and the nine Glaisher quotients (M10). Argument order (z, τ).
    "sn": ("fn", _sn), "cn": ("fn", _cn), "dn": ("fn", _dn),
    "ns": ("fn", _GLAISHER["ns"]), "nc": ("fn", _GLAISHER["nc"]), "nd": ("fn", _GLAISHER["nd"]),
    "sc": ("fn", _GLAISHER["sc"]), "sd": ("fn", _GLAISHER["sd"]), "cd": ("fn", _GLAISHER["cd"]),
    "cs": ("fn", _GLAISHER["cs"]), "ds": ("fn", _GLAISHER["ds"]), "dc": ("fn", _GLAISHER["dc"]),
    # MODULUS-parametrized Jacobi elliptic functions (JacobiModulusBridge.lean, DLMF §22.2):
    # `snk z k = sn z (tauOfModulus k)`, argument order (z, k) with k REAL. Registered under
    # the qualified names too — Ch31's Jacobi-form rows spell them `FLMF.Theta.snk`. Anchored
    # against mpmath's independent AGM `ellipfun` and the nome relation k² = (θ₂/θ₃)⁴ in
    # verify() (and docs/verification/ch31/snk_selfcheck.py).
    "snk": ("fn", _snk), "cnk": ("fn", _cnk), "dnk": ("fn", _dnk),
    "FLMF.Theta.snk": ("fn", _snk), "FLMF.Theta.cnk": ("fn", _cnk),
    "FLMF.Theta.dnk": ("fn", _dnk),
    "tauOfModulus": ("fn", _tau_of_modulus),
    "FLMF.Theta.tauOfModulus": ("fn", _tau_of_modulus),
    # Gudermannian (DLMF 4.23.39)
    "gd": ("fn", _gudermannian),
    # ── M14: number theory (DLMF 27.9) ──
    # `ZMod.χ₄`/`ZMod.χ₈` are the fully-qualified Mathlib names as they appear in
    # statement dumps (`ZMod` is not an FLMF namespace segment, so _reg_resolve
    # never strips it) — same anchored implementations, DLMF 27.9 supplementary laws.
    "χ₄": ("fn", _chi4), "χ₈": ("fn", _chi8),
    "ZMod.χ₄": ("fn", _chi4), "ZMod.χ₈": ("fn", _chi8),
    "completedRiemannZeta": ("fn", _completed_riemann_zeta),
    "theta4MellinContinuation": ("fn", _theta4_mellin_continuation),
    # ── M14: Dedekind η / modular forms (τ-parametrized, DLMF 23) ──
    "eta": ("fn", _eta), "ModularForm.eta": ("fn", _eta), "etaFactor": ("fn", _eta_factor),
    "ModularForm.discriminant": ("fn", _modform_discriminant),
    # SL(2,ℤ) generators + the weight-k slash action `SlashAction.map k γ f` (DLMF 23.15;
    # the extract side eta-expands the 3-arg application into a τ-callable via _slash_action).
    "ModularGroup.T": ("const", MODULAR_T), "ModularGroup.S": ("const", MODULAR_S),
    "SlashAction.map": ("fn", _slash_action),
    "Function.Periodic.qParam": ("fn", _qparam), "Periodic.qParam": ("fn", _qparam),
    "EisensteinSeries.E2": ("fn", _eisenstein_E2),
    # FLMF bridge def FLMF.Eisenstein.E₂ := EisensteinSeries.E2 (EisensteinModular.lean);
    # pretty-prints as `E₂` in theorem conclusions (mirrors the eta/ModularForm.eta dual binding).
    "E₂": ("fn", _eisenstein_E2), "FLMF.Eisenstein.E₂": ("fn", _eisenstein_E2),
    # FLMF bridge defs FLMF.Eisenstein.E₄/E₆ := ⇑(EisensteinSeries.E k) (EisensteinModular.lean);
    # pretty-print as bare `E₄`/`E₆`. The Weierstrass lattice-rescaled `E₄ L = g₂/12`,
    # `E₆ L = g₃/8` share the bare names but take a LATTICE argument — the extractor's
    # `_LARG` dispatch fires first on a lattice value, so these τ-bindings are reached only
    # for a scalar (ℍ) argument or a bare function reference (e.g. inside `qExpansion 1 E₆`).
    "E₄": ("fn", _eisenstein_E4), "FLMF.Eisenstein.E₄": ("fn", _eisenstein_E4),
    "E₆": ("fn", _eisenstein_E6), "FLMF.Eisenstein.E₆": ("fn", _eisenstein_E6),
    "I": ("const", mp.mpc(0, 1)),          # bare Complex.I after `open Complex`
    # ── M14: per-function specials (Tier C2 tail) ──
    "binet": ("fn", _binet),
    # DLMF §5.10/5.11 asymptotic-coefficient tables (N1 group): the Stirling gₖ /
    # ratio Gₖ(a,b) / symmetrized Hₖ(a,b) sequences (instantiating the abstract
    # SatisfiesStirlingRec / IsRatioCoeffs / IsSymRatioCoeffs binders via
    # fidelity_extract's _fnwitness), and the Binet CF numerator table binetCFNum.
    "stirlingRecG": ("fn", _stirling_g),
    "stirlingRecA": ("fn", _stirling_seq_a_witness),
    "ratioCoeffG": ("fn", _ratio_coeff_G),
    "symRatioCoeffH": ("fn", _sym_ratio_coeff_H),
    "binetCFNum": ("fn", _binet_cf_num),
    "FLMF.Functions.Gamma.binetCFNum": ("fn", _binet_cf_num),
    "Eₙ": ("fn", _expint_n), "upperGammaWatson": ("fn", _upper_gamma_watson),
    "ciTail": ("fn", _ci_tail),
    "airyG": ("fn", _airy_g), "airyBi": ("fn", _airy_bi),
    "airyAi": ("fn", _airy_g),     # FLMF airyAi (steepest-descent integral) = Ai = airyG
    # ── M16 tail (Tricomi U, Legendre generating helpers, q-series, Mathieu, AM) ──
    "tricomiU": ("fn", _tricomiU),                                  # DLMF 13.4.4 U(a;b;z)
    "En": ("fn", _En_ascii),                                        # ASCII generalized Eₙ
    "E1": ("fn", lambda x: mp.e1(x)),                               # ∫₁^∞ e^{−xt}/t (x>0)
    "FLMF.ExpIntegrals.Def.E1": ("fn", lambda x: mp.e1(x)),         # fully-qualified alias
    "E₁": ("fn", lambda x: mp.e1(x)),                               # subscript alias (E1Leading)
    # eiSeries y = Σ_{n≥1} yⁿ/(n·n!) (Definitions.lean) — the entire series part of the E1
    # expansion (DLMF 6.6.2), summed directly so the E1_series check stays decorrelated from e1.
    "eiSeries": ("fn", lambda y: mp.nsum(lambda n: y ** n / (n * mp.factorial(n)), [1, mp.inf])),
    # liW(x) = e^{ln x}·∫₀^∞ e^{−(ln x)u}/(1+u) du = x²·E₁(ln x) (LiLeading; leading li factor).
    "liW": ("fn", lambda x: x ** 2 * mp.e1(mp.log(x))),
    "cosGamma": ("fn", _cosGamma), "multiplyingGamma": ("fn", _multiplyingGamma),
    "Nat.factorial": ("fn", lambda n: mp.mpf(__import__("math").factorial(int(n)))),
    "factorial": ("fn", lambda n: mp.mpf(__import__("math").factorial(int(n)))),
    "genSum": ("fn", _gen_sum), "genSumD": ("fn", _gen_sum_d),
    "genQuad": ("fn", _gen_quad), "genClosed": ("fn", _gen_closed),
    "Uval": ("fn", _uval), "rodriguesPoly": ("poly", _rodrigues_poly),
    "a0Approx": ("fn", _a0_approx),
    # Mathieu small-q characteristic-value approximants (DLMF 28.6.2–28.6.5), same
    # shape as a0Approx: explicit truncated polynomials from CharacteristicValues.lean.
    "a1Approx": ("fn", _a1_approx), "b1Approx": ("fn", _b1_approx),
    "a2Approx": ("fn", _a2_approx), "b2Approx": ("fn", _b2_approx),
    # ── mathieu_orthogonal ∀-function witness (DLMF 28.2.31 at q = 0) ────────────
    # The Sturm–Liouville surface `mathieu_orthogonal` (Mathieu/Orthogonality.lean)
    # universally quantifies over solutions `y₁, y₂` of Mathieu's equation together
    # with their SUPPLIED first/second derivatives `dyᵢ, ddyᵢ` — bound function
    # variables the oracle cannot sample as scalars (the sweep skipped it as
    # `unbound:y₁`).  Like the abstract Airy pair `P.Ai`/`P.Bi` below, we instantiate
    # the ∀ at a CANONICAL witness: the q = 0 Mathieu functions ce₁(x,0) = cos x
    # (a₁ = 1) and ce₂(x,0) = cos 2x (a₂ = 4) — DLMF 28.2(vi), with aₘ(0) = m²
    # (28.2.23; = the q→0 values of the a1Approx/a2Approx approximants above).  The
    # witness satisfies EVERY hypothesis of the theorem (the Mathieu ODE 28.2.1 with
    # q = 0, 2π-periodicity of values and first derivatives, a₁ ≠ a₂), and each
    # hypothesis is anchored numerically in verify() before the binding is trusted.
    # Sound as a refutation oracle: a numeric counterexample at the witness disproves
    # the ∀; passing is evidence (the conclusion at this witness IS DLMF 28.2.31 with
    # m = 1, n = 2, q = 0).  The whole solution package (yᵢ, dyᵢ, ddyᵢ) binds
    # coherently so any future surface mixing these heads stays self-consistent.
    "y₁": ("fn", lambda x: mp.cos(x)),
    "dy₁": ("fn", lambda x: -mp.sin(x)),
    "ddy₁": ("fn", lambda x: -mp.cos(x)),
    "y₂": ("fn", lambda x: mp.cos(2 * x)),
    "dy₂": ("fn", lambda x: -2 * mp.sin(2 * x)),
    "ddy₂": ("fn", lambda x: -4 * mp.cos(2 * x)),
    "qProductFactor": ("fn", _q_product_factor), "thetaSeriesTerm": ("fn", _theta_series_term),
    "triangleCoeff": ("fn", _triangle_coeff),
    "ifact": ("fn", _ifact), "triangle6j": ("fn", _triangle6j),   # exact factorials (M18)
    # ── M17 tail: Clausen/Lobachevsky (DLMF 25.12), Riemann ξ (25.4), Jacobi amplitude (22.13) ──
    "Cl_2": ("fn", _clausen_cl2), "lobachevsky": ("fn", _lobachevsky),
    "riemannXi": ("fn", _riemann_xi), "jacobiAm": ("fn", _jacobi_am),
    # ── M19 tail: real-order Bessel K + its Tricomi-U bridge (DLMF 10.32.9 / 13.6.10) ──
    "iRepErfc": ("fn", _iRepErfc), "bickleyKi": ("fn", _bickleyKi),   # repeated-integral families
    # truncated Goodwin–Staton ∫₀ᵇ e^{−t²}/(t+z) dt (GoodwinStaton.lean) — its b→∞ limit is the
    # full DLMF 7.2.12 integral (erf_7_2_12). Both the short and fully-qualified heads bind here.
    "goodwinStatonTrunc": ("fn", _goodwin_staton_trunc),
    "FLMF.GoodwinStaton.goodwinStatonTrunc": ("fn", _goodwin_staton_trunc),
    "GoodwinStaton.goodwinStatonTrunc": ("fn", _goodwin_staton_trunc),
    # Airy modulus/phase (DLMF 9.8): the theorems quantify over an abstract `RealAiryPair P`;
    # we instantiate P at the CANONICAL pair (airyAi/airyBi, Wronskian 1/π) and check the
    # formula at that witness — sound as a refutation oracle (a counterexample disproves the
    # ∀; passing is evidence). `P.field` are single dotted-id heads, so these are plain binds.
    "P.Ai": ("fn", lambda x: mp.airyai(x)),       "P.Bi": ("fn", lambda x: mp.airybi(x)),
    "P.Ai'": ("fn", lambda x: mp.airyai(x, 1)),   "P.Bi'": ("fn", lambda x: mp.airybi(x, 1)),
    "P.phase": ("fn", lambda x: mp.atan(mp.airyai(x) / mp.airybi(x))),
    "P.mod": ("fn", lambda x: mp.sqrt(mp.airyai(x) ** 2 + mp.airybi(x) ** 2)),
    # ── OrthogonalPoly-bundle ∀-witness heads (DLMF §18.2(vi); LaguerreZeros.lean /
    # Zeros.lean) — see _op_bundle_roots_card.  Kind `envfn`: an env-dependent ATOM —
    # the head takes no explicit arguments in the Lean conclusion
    # (`O.P.roots.toFinset.card = n`), but its witness value depends on the sampled
    # degree binder n, so the binding receives the whole sample env (the extractor's
    # bare-var envfn branch).  Keyed on the literal bundle-projection spelling, so it
    # can only fire on conclusions written over a bundle variable named `O` with a
    # polynomial field `P` — the OrthogonalPoly convention of Zeros.lean.
    "O.P.roots.toFinset.card": ("envfn", _op_bundle_roots_card),
    # bundle field `deg : P.natDegree = n` (OrthogonalPoly, Zeros.lean) — exact at ANY
    # witness by the bundle's own definition, so `laguerre_roots_card_eq_degree`
    # (roots.toFinset.card = natDegree) is scored as measured-root-count vs n,
    # never as the tautology n = n.
    "O.P.natDegree": ("envfn", lambda env: mp.mpf(int(env["n"]))),
    "besselK_real": ("fn", _besselK_real), "tricomiBridgeFun": ("fn", _tricomi_bridge_fun),
    # probHermite has DEGREE-then-param order (probHermite n c), opposite to laguerre's
    # (param α, degree n). lpoly calls fn(int(args[1]), args[0], x) = fn(int(c), n, x); the
    # wrapper swaps that back into _prob_hermite(degree=n, variance=c, x).
    "probHermite": ("lpoly", lambda cc, nn, x: _prob_hermite(nn, cc, x)),
    # ── M18: confluent-hyp + Rodrigues + Fresnel (Agent Z) ──
    "₁F₁": ("fn", _kummerM), "kummerM": ("fn", _kummerM),
    # ── M20: Gauss ₂F₁ + Legendre-as-₂F₁ (DLMF 15.2.1 / 14.3.1) ──
    "₂F₁": ("fn", _gaussF), "ordinaryHypergeometric": ("fn", _gaussF),
    "ordinaryHypergeometricCoefficient": ("fn", _gaussF_coeff),
    # ── §15.16 product identities: the Aₛ coefficient (DLMF 15.16.2) as an exact Cauchy product
    # (Ch15Products.lean gaussProductCoefficient), so the growing-order HasSum rows 15.16.1/2 no
    # longer false-skip as `hassum eval-timeout` under per-term numerical differentiation. ──
    "gaussProductCoefficient": ("fn", _gaussProductCoefficient),
    # ── C2 Phase 1: full-disc Pfaff (PfaffFullDisc.lean, DLMF 15.8.1) ──
    "pfaffExtension": ("fn", _pfaffExtension),
    # ── §15.2(ii): principal continuations + cut-jump / singular-limit surfaces ──
    # (GaussPrincipalGlobal.lean, Ch15DefinitionsAnalytical.lean; DLMF 15.2.1–15.2.6)
    "principalGauss": ("fn", _principalGauss),
    # §15.10 Kummer solutions w₁..w₆ (Ch15KummerPrincipal.lean; DLMF 15.10.2/15.10.4/15.10.6)
    "principalW1": ("fn", _principalW1), "principalW2": ("fn", _principalW2),
    "principalW3": ("fn", _principalW3), "principalW4": ("fn", _principalW4),
    "principalW5": ("fn", _principalW5), "principalW6": ("fn", _principalW6),
    # §15.10(ii) half-plane connection phase (Ch15KummerPrincipal.lean): z^t·(−z)^(−t) =
    # e^{tπi} for Im z>0 / z<0, e^{−tπi} for Im z<0 / z>0 — mirrors the Lean def LITERALLY
    # (both principal cpow; mpmath and Complex.log share arg ∈ (−π, π]).
    "kummerPhase": ("fn", _kummerPhase),
    "principalOlver": ("fn", _principalOlver),
    "olverHypergeometric": ("fn", _olverHypergeometric),
    "principalOlverBoundaryAbove": ("fn", _principalOlverBoundary(+1)),
    "principalOlverBoundaryBelow": ("fn", _principalOlverBoundary(-1)),
    "gaussSingularIterated": ("fn", _gaussSingularIterated),
    # ── C2 Phase 2: the z = 1 connection kit (GaussConnection.lean) ──
    # gaussValue a b c = Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))  (DLMF 15.4.20 RHS, GaussValues.lean)
    "gaussValue": ("fn", lambda a, b, c:
                   mp.gamma(c) * mp.gamma(c - a - b) / (mp.gamma(c - a) * mp.gamma(c - b))),
    # gaussW3 a b c z = ₂F₁(a,b;a+b−c+1;1−z)   (Kummer w₃, DLMF 15.10.13 first branch)
    # GaussConnection.lean defines w₃/w₄ through Mathlib's `₂F₁` ITSELF (hypergeometric_15_10_4
    # is proven by `rfl`), so both must go through `_gaussF` — its junk-0 outside the disc is
    # part of the object being defined; calling mp.hyp2f1 here instead would make the binding
    # of a definitional identity disagree with the binding of its own right-hand side.
    "gaussW3": ("fn", lambda a, b, c, z: _gaussF(a, b, a + b - c + 1, 1 - z)),
    # gaussW4 a b c z = (1−z)^{c−a−b}·₂F₁(c−a,c−b;c−a−b+1;1−z)  (w₄, DLMF 15.10.14)
    "gaussW4": ("fn", lambda a, b, c, z:
                (1 - z) ** (c - a - b) * _gaussF(c - a, c - b, c - a - b + 1, 1 - z)),
    "legendreHG": ("fn", lambda n, x: mp.legendre(int(n), x)),   # =₂F₁(−n,n+1;1;(1−x)/2)=Pₙ
    # §15.10 resonant logarithmic local solutions (DLMF 15.10.8/9/10)
    "logSolution15_10_8": ("fn", _logSolution15_10_8),
    "logSolution15_10_9": ("fn", _logSolution15_10_9),
    "logSolution15_10_10": ("fn", _logSolution15_10_10),
    "kummerCoefficient": ("fn", _kummerCoefficient),
    "laguerreRodrigues": ("fn", _laguerreRodrigues),
    # Pearson-system witness data (abstract DLMF 18.5.5 surface, rodrigues_spec):
    # the Hermite-He row of Table 18.5.1 / §18.3 — see the _hermitePearson_w block.
    "hermitePearsonW": ("fn", _hermitePearson_w),
    "hermitePearsonKernel": ("fn", _hermitePearson_kernel),
    "hermitePearsonNorm": ("fn", _hermitePearson_norm),
    "fresnelC": ("fn", mp.fresnelc), "fresnelS": ("fn", mp.fresnels),
    # Chapter-7 Fresnel auxiliary functions f, g (DLMF 7.2.10/7.2.11) — distinct from the
    # chapter-6 (Si/Ci) `auxF`/`auxG` below. C=fresnelc, S=fresnels, θ=πz²/2.
    "fresnelAuxF": ("fn", lambda z: (mp.mpf(1)/2 - mp.fresnels(z)) * mp.cos(mp.pi * z**2 / 2)
                                    - (mp.mpf(1)/2 - mp.fresnelc(z)) * mp.sin(mp.pi * z**2 / 2)),
    "fresnelAuxG": ("fn", lambda z: (mp.mpf(1)/2 - mp.fresnelc(z)) * mp.cos(mp.pi * z**2 / 2)
                                    + (mp.mpf(1)/2 - mp.fresnels(z)) * mp.sin(mp.pi * z**2 / 2)),
    # ── Chapter-7 complex error-function family (see helper defs above) ──
    "cerf": ("fn", mp.erf), "cerfc": ("fn", mp.erfc),         # complex erf/erfc (DLMF 7.2.1/7.2.2)
    "faddeeva": ("fn", _faddeeva),                            # Faddeeva w(z) (DLMF 7.2.3)
    "cfresnelC": ("fn", mp.fresnelc), "cfresnelS": ("fn", mp.fresnels),  # complex Fresnel C/S
    "cfresnelAuxF": ("fn", _cfresnelAuxF), "cfresnelAuxG": ("fn", _cfresnelAuxG),  # complex f, g
    "cfresnelScriptF": ("fn", _cfresnelScriptF),             # complex Fresnel 𝓕 (DLMF 7.5.2)
    "fresnelZeta": ("fn", _fresnelZeta),                     # ζ = ½√π(1-i)z (DLMF 7.5.7)
    "cdawson": ("fn", _cdawson),                             # complex Dawson F(z)
    "expIntegralE": ("fn", _expIntegralE),                   # E_p(x) (DLMF 8.19.1; used by 7.11.3)
    "Hh": ("fn", _Hh),                                       # probability fn Hhₙ (DLMF §7.18; 7.18.12)
    "inverf": ("fn", mp.erfinv),                             # inverse erf (DLMF 7.17.1)
    "inverfc": ("fn", lambda x: mp.erfinv(1 - x)),           # inverse erfc = erfinv(1-x)
    # §7.12 f/g asymptotic truncations + remainders (DLMF 7.12.4/.5) and the
    # Pochhammer (½)_m they use; §7.17 inverse-erf coefficients & local asymptotic vars.
    "pochHalf": ("fn", _pochHalf),                           # (½)_m (DLMF 5.2.5 form)
    "truncF": ("fn", _truncF), "truncG": ("fn", _truncG),    # n-term f/g sums (7.12.4/.5)
    "remF": ("fn", _remF), "remG": ("fn", _remG),            # structural f/g remainders
    "inverfCoeff": ("fn", _inverf_coeff),                    # inverf Maclaurin aₖ (7.17.2_5)
    "asymU": ("fn", _asymU),                                 # inverfc asymptotic var u (7.17.5)
    "asymV": ("fn", _asymV),                                 # inverfc asymptotic var v (7.17.6)
    "asymA": ("fn", _asymA),                                 # inverfc local coeffs a₂,a₃,a₄ (7.17.4)
    "Polynomial.hermite": ("poly", _hermite_prob),   # fully-qualified spelling
    # NOTE: liW is NOT bound. Its value/diff rows are reachable, but binding it turns the
    # O(1/log x) liW_asymptotic into a row the rate-gate can't certify — binding would only
    # convert a true theorem into an uncertifiable check. Left as a skip.
    # (besselKAmplitude, once on this list for the same reason via besselK_watson_*, IS now
    # bound below — checked 2026-07-21: the besselK_watson_* expansion theorems are not
    # extractor-reachable rows at all ("decl not found by extractor"), so binding cannot
    # convert them into anything; it only makes the value/limit rows checkable
    # (besselKAmplitude_zero g_ν(0)=1, DLMF 10.40.2 normalization — PASS;
    # besselKAmplitude_tendsto_one — PASS), and the M14 refutation-discipline Tendsto gate
    # would report any uncertified rate as a SKIP, never a false FAIL.)
    # angular-momentum factorial coefficients (DLMF 34.2.2) — exact, no sympy needed
    "triangleCoeffSq": ("fn", _triangle_coeff_sq),
    "magneticFactor":  ("fn", _magnetic_factor),
    # Racah summation (DLMF 34.2.4) — exact finite factorial sum, no sympy needed; closes
    # the previously-unbound `unbound:racahSum` gap that let the `wigner3j`/`clebschGordan`
    # `.toNat`-phase sign error (ERRATA `wigner3j-tonat-phase`) go undetected via this route.
    "racahTerm": ("fn", _racah_term),
    "racahSum":  ("fn", _racah_sum),
    # Laplace's integral for the Legendre polynomial (DLMF 14.7.19):
    #   laplaceIntegral n x = (1/π) ∫₀^π (x + √(x²−1)·cos θ)ⁿ dθ.
    # Uses the Mathlib `Real.sqrt` convention (0 on negatives) — so the identity with Pₙ
    # only holds for x² ≥ 1; below that the √-term is junk-0 (the laplaceIntegral_two
    # hypothesis `1 ≤ x²` is honored by the sampler's `absge1` grid).
    "laplaceIntegral": ("fn", lambda n, x: (1 / mp.pi) *
                        mp.quad(lambda th: (x + _rsqrt(x ** 2 - 1) * mp.cos(th)) ** int(n), [0, mp.pi])),
    # NOTE: Ei/E₁/li are deliberately NOT bound. FLMF defines Ei(x) := −E₁(−x) and
    # li(x) := Ei(log x) as `rfl`, so `Ei_eq_neg_E1_neg`/`li_eq_Ei_log` are definitional
    # tautologies (no numeric cross-check to add); and FLMF's `E1` is a real Lebesgue
    # integral that is junk-valued for x ≤ 0 (non-integrable 1/t singularity), where
    # mpmath's complex-branch `e1` would disagree. Left as honest skips.
    # constants — Lean spells the Glaisher–Kinkelin constant both ways
    "Real.glaisherKinkelin": ("const", mp.glaisher),
    # ── M7 / B1: exact Nat-arithmetic heads ──
    "totient":        ("fn", lambda n: _totient(n)),         # FLMF abbrev of Nat.totient
    "Nat.totient":    ("fn", lambda n: _totient(n)),
    "jordanTotient":  ("fn", lambda k, n: _jordan_totient(k, n)),
    # the underlying ArithmeticFunction `jordanTotientFn k = μ * pow k` (JordanTotient.lean):
    # applied as `jordanTotientFn k n` it IS `jordanTotient k n` (the Lean def unfolds to it),
    # so it shares the anchored _jordan_totient model (junk n = 0 ↦ 0 matches f(0) = 0).
    "jordanTotientFn": ("fn", lambda k, n: _jordan_totient(k, n)),
    "divisorSigma":   ("fn", lambda k, n: _divisor_sigma(k, n)),
    # Mathlib `ArithmeticFunction.sigma k n = ∑_{d∣n} dᵏ` — written fully qualified in
    # conclusions (the bare `σ` notation is scoped); same exact divisor sum as divisorSigma.
    "ArithmeticFunction.sigma": ("fn", lambda k, n: _divisor_sigma(k, n)),
    "Nat.choose":     ("fn", lambda n, k: _choose(n, k)),
    "catalan":        ("fn", lambda n: _catalan(n)),
    "harmonic":       ("fn", lambda n: _harmonic(n)),
    # `_root_.bernoulli` is how a conclusion disambiguates Mathlib's bernoulli NUMBER
    # from the local polynomial namespace — same B⁻ object as the `bernoulli` binding.
    "_root_.bernoulli": ("fn", _bernoulli_mathlib),
    "_root_.bernoulli'": ("fn", _bernoulli_prime_mathlib),       # B⁺ₙ (B₁=+½) = Bₙ(1)
    # Struve functions Hν, Lν (DLMF 11.2) — mpmath builtins (unlocks struveL_nonneg etc.)
    "struveH": ("fn", lambda nu, z: mp.struveh(nu, z)),
    "struveL": ("fn", lambda nu, z: mp.struvel(nu, z)),
    # general-order Bessel J_ν(z) (DLMF 10.2.2) = mp.besselj (besselJnu/besselJ: same series).
    "besselJnu": ("fn", lambda nu, z: mp.besselj(nu, z)),
    "besselJ": ("fn", lambda nu, z: mp.besselj(nu, z)),
    "besselY": ("fn", lambda nu, z: mp.bessely(nu, z)),     # Y_ν(z), Bessel 2nd kind
    # --- ExpIntegrals chapter-6 auxiliary functions (Cin, si, Shi, Chi, f, g) ---
    "Cin": ("fn", lambda z: mp.euler + mp.log(z) - mp.ci(z)),        # Cin, DLMF 6.2.12 = γ+ln z−Ci(z)
    "si":  ("fn", lambda z: mp.si(z) - mp.pi / 2),                   # si, DLMF 6.2.10 = Si(z)−π/2
    "Shi": ("fn", lambda z: mp.shi(z)),                             # Shi, DLMF 6.2.15 (hyperbolic sine integral)
    "Chi": ("fn", lambda z: mp.chi(z)),                             # Chi, DLMF 6.2.16 (hyperbolic cosine integral)
    "auxF": ("fn", lambda z: mp.ci(z) * mp.sin(z) + (mp.pi / 2 - mp.si(z)) * mp.cos(z)),  # f, DLMF 6.2.17 = Ci(z)sin z+(π/2−Si(z))cos z
    "auxG": ("fn", lambda z: (mp.pi / 2 - mp.si(z)) * mp.sin(z) - mp.ci(z) * mp.cos(z)),  # g, DLMF 6.2.18 = (π/2−Si(z))sin z−Ci(z)cos z
    # core sine/cosine/exponential/logarithmic integrals (ExpIntegrals §6) — were unbound,
    # so every Si/Ci/Ei/li-bearing statement silently skipped. Anchored to the DLMF functions.
    "Si":  ("fn", lambda z: mp.si(z)),                              # Si, DLMF 6.2.9
    "Ci":  ("fn", lambda z: mp.ci(z)),                             # Ci, DLMF 6.2.11/6.2.13
    "Ei":  ("fn", lambda x: mp.ei(x)),                             # Ei (unified series, DLMF 6.6.1), all x≠0
    "li":  ("fn", lambda x: mp.ei(_rlog(x))),                      # li := Ei(Real.log x), DLMF 6.2.8 (FLMF's defining anchor; Real.log = log|·|)
    "FLMF.ExpIntegrals.Def.Ei": ("fn", lambda x: mp.ei(x)),        # qualified alias (some concls print fully qualified)
    "FLMF.ExpIntegrals.Series.Ein": ("fn", lambda x: mp.euler + mp.log(x) + mp.e1(x)),  # Ein = γ+ln x+E1(x)
    # complex Ein / E1 helpers introduced by the §6.7 complex-argument integral-rep surfaces
    "EinC":      ("fn", lambda z: mp.euler + mp.log(z) + mp.e1(z)),  # entire Ein on ℂ
    "E1RepEinC": ("fn", lambda z: mp.euler + mp.log(z) + mp.e1(z)),
    "E1RepC":    ("fn", lambda z: mp.e1(z)),                         # principal complex E1
    # custom helper objects of §6.10/§6.12/§6.16/§6.18 — bound so their identities/recurrences
    # become Tier-1-checkable (each anchored to its exact FLMF def).
    "cCoeff": ("fn", lambda k: _ccoeff(k)),                          # 6.10.3 recurrence coeffs
    "aCoeff": ("fn", lambda n: (2 * _nat(n,'aCoeff') + 1) * (1 - (-1) ** _nat(n,'aCoeff') + _harmonic(n))),  # 6.10.7
    "sphBesselJ":   ("fn", lambda n, z: _sph_j(n, z)),              # DLMF 10.53.1
    "modSphBesselI":("fn", lambda n, z: _mod_sph_i(n, z)),          # DLMF 10.53.3
    "auxFPartialSum": ("fn", lambda n, x: (1 / x) * mp.fsum((-1) ** m * mp.factorial(2 * m) / x ** (2 * m) for m in range(_nat(n,'auxFPartialSum')))),
    "auxGPartialSum": ("fn", lambda n, x: (1 / x ** 2) * mp.fsum((-1) ** m * mp.factorial(2 * m + 1) / x ** (2 * m) for m in range(_nat(n,'auxGPartialSum')))),
    "auxFRemainder": ("fn", lambda n, x: (-1) ** _nat(n,'auxFRemainder') * mp.quad(lambda t: mp.exp(-x * t) * t ** (2 * _nat(n,'auxFRemainder')) / (t ** 2 + 1), [0, mp.inf])),
    "auxGRemainder": ("fn", lambda n, x: (-1) ** _nat(n,'auxGRemainder') * mp.quad(lambda t: mp.exp(-x * t) * t ** (2 * _nat(n,'auxGRemainder') + 1) / (t ** 2 + 1), [0, mp.inf])),
    "gibbsS": ("fn", lambda n, x: mp.fsum(mp.sin((2 * k + 1) * x) / (2 * k + 1) for k in range(_nat(n,'gibbsS')))),
    "gibbsR": ("fn", lambda n, x: (mp.mpf(1) / 2) * mp.quad(lambda t: (1 / mp.sin(t) - 1 / t) * mp.sin(2 * _nat(n,'gibbsR') * t), [0, x])),
    "auxAn": ("fn", lambda n, x: mp.quad(lambda t: (t * mp.exp(-x * t) / (1 + t ** 2)) * (t ** 2 / (1 + t ** 2)) ** _nat(n,'auxAn'), [0, mp.inf])),
    "auxBn": ("fn", lambda n, x: mp.quad(lambda t: (mp.exp(-x * t) / (1 + t ** 2)) * (t ** 2 / (1 + t ** 2)) ** _nat(n,'auxBn'), [0, mp.inf])),
    "auxCn": ("fn", lambda n, x: mp.quad(lambda t: mp.exp(-x * t) * (t ** 2 / (1 + t ** 2)) ** _nat(n,'auxCn'), [0, mp.inf])),
    # Struve K_ν(z) = H_ν(z) − Y_ν(z) (StruveBesselRel) — anchored K_{1/2}=√(2/πz), K_{−1/2}=0.
    "struveK": ("fn", lambda nu, z: mp.struveh(nu, z) - mp.bessely(nu, z)),
    # reduced Struve series Sν(w) = Σ(−1)ᵐwᵐ/(Γ(m+3/2)Γ(m+ν+3/2)) = ₁F₂(1;3/2,ν+3/2;−w)
    # /(Γ(3/2)Γ(ν+3/2)) — entire in w (decorrelated from the (z/2)^{ν+1}·Sν prefactor reln).
    "struveHReduced": ("fn", lambda nu, w: mp.hyper([1], [mp.mpf(3) / 2, nu + mp.mpf(3) / 2], -w)
                       / (mp.gamma(mp.mpf(3) / 2) * mp.gamma(nu + mp.mpf(3) / 2))),
    # struveInhom ν = 1/(√π·Γ(ν+3/2)) — the Struve recurrence inhomogeneity.
    "struveInhom": ("fn", lambda nu: 1 / (mp.sqrt(mp.pi) * mp.gamma(nu + mp.mpf(3) / 2))),
    # Weierstrass elementary factor of genus 2, E₂(w) = (1−w)·exp(w + w²/2)
    # (DLMF 23.2.7; WeierstrassSigmaProduct.lean). Anchored E₂(0)=1, E₂(1)=0.
    "weierstrassFactor": ("fn", lambda w: (1 - w) * mp.e ** (w + w ** 2 / 2)),
    # ── M7 / B2: digamma + theta nulls + the modular trio ──
    # Lean `realDigamma x = deriv (Real.log ∘ Real.Gamma) x` = Γ′/Γ = ψ(x) wherever
    # Γ ≠ 0 (Real.log = log|·| makes the composition ψ on each Γ-sign region too).
    "realDigamma":  ("fn", mp.digamma),  "Real.realDigamma": ("fn", mp.digamma),
    # `realTrigamma x = deriv realDigamma x` = ψ′(x) (DigammaTrigamma.lean) — trigamma
    # = mp.polygamma(1,·). Anchored at ψ′(1) = π²/6 (realTrigamma_one), which the
    # by-name ψ (= polygamma 0) fails.
    "realTrigamma": ("fn", lambda x: mp.polygamma(1, x)),
    "Real.realTrigamma": ("fn", lambda x: mp.polygamma(1, x)),
    # Airy leading amplitude (DLMF 9.7.5): e^{−⅔x^{3/2}}/(2√π·x^{1/4}).
    "airyAiAmp": ("fn", lambda x: mp.e ** (-(mp.mpf(2) / 3) * x ** (mp.mpf(3) / 2))
                  / (2 * mp.sqrt(mp.pi) * x ** (mp.mpf(1) / 4))),
    # nome q(τ) = exp(πiτ) (Nome.lean) — distinct from qParam's exp(2πiz/h).
    "nome": ("fn", lambda t: mp.exp(mp.pi * mp.j * t)),
    # ModularForm.eta_q n z = (𝕢 1 z)^(n+1) = e^{2πi(n+1)z} (DedekindEta) — the q^{n+1} factor.
    "ModularForm.eta_q": ("fn", lambda n, z: mp.exp(2 * mp.pi * mp.j * (int(n) + 1) * z)),
    "θ₁": ("fn", _theta(1)), "θ₂": ("fn", _theta(2)),
    "θ₃": ("fn", _theta(3)), "θ₄": ("fn", _theta(4)),
    # Mathlib `jacobiTheta₂ z τ = ∑' n, exp(2πinz + πin²τ)` = FLMF θ₃ (Classical.lean) — same head.
    "jacobiTheta₂": ("fn", _theta(3)),
    # z- and τ-derivatives of jacobiTheta₂ (heat equation θ_zz = 4πi·θ_τ, DLMF 20.4):
    "jacobiTheta₂'": ("fn", lambda z, t: mp.diff(lambda zz: _theta(3)(zz, t), z)),
    "jacobiTheta₂_snd": ("fn", lambda z, t: mp.diff(lambda tt: _theta(3)(z, tt), t)),
    "ellipticModulus":      ("fn", _elliptic_modulus),
    "complementaryModulus": ("fn", _complementary_modulus),
    "modularLambda":        ("fn", _modular_lambda),
    "complementaryLambda":  ("fn", _complementary_lambda),
    # quadratic Gauss sum G(m,n) = Σ_{k<n} e^{−πik²m/n} (DLMF 20.11.1, the theta-analog
    # discrete sum of Ch20Generalizations.lean) — anchored G(1,2)=1−i, G(1,4)=√2(1−i).
    "gaussSum": ("fn", _gauss_sum),
    # Ramanujan's theta f(a,b) = Σ_{n∈ℤ} a^{n(n+1)/2} b^{n(n−1)/2} (DLMF 20.11.3,
    # Ch20Generalizations.lean `ramanujanTheta`) — guarded truncated bilateral sum,
    # anchored to the 20.11.4 θ₃ tie + the Jacobi triple product in verify().
    "ramanujanTheta": ("fn", _ramanujan_theta),
    # combined theta functions φ_{m,n}(πz, q) (DLMF 20.11.6–20.11.8,
    # Ch20Generalizations.lean `combinedTheta m n z τ`) — independent raw-jtheta
    # quotients; anchored in verify() (20.4.6 null, Lean-def replay, z→0
    # normalization, 22.2.4 sn tie).
    "combinedTheta": ("fn", _combined_theta),
    # Jacobi triple product truncations (JacobiTripleProduct.lean; DLMF 20.5.3 in
    # cleared Laurent-free form) — finite-polynomial def mirrors, incl. the Nat
    # truncated-subtraction (2n−1 ↦ 0 at n=0) and Int.toNat ((2n).toNat = max(2n,0))
    # exponent clamps; anchored in verify() against mp.jtheta via the triple product.
    "tripleProductFactorCleared": ("fn", _jtp_factor_cleared),
    "tripleProductFactor":        ("fn", _jtp_factor),
    "tripleProductProd":          ("fn", _jtp_prod),
    "tripleProductSum":           ("fn", _jtp_sum),
    # theta nullwerte θⱼnull τ = θⱼ 0 τ (Nullwerte.lean; DLMF §20.4 values at z = 0)
    "θ₂null": ("fn", lambda t: _theta(2)(0, t)),
    "θ₃null": ("fn", lambda t: _theta(3)(0, t)),
    "θ₄null": ("fn", lambda t: _theta(4)(0, t)),
    # §20.6 lattice-sum coefficients δ/α/β/γ_{2j}(τ) (Ch20PowerSeries.lean; DLMF
    # 20.6.6–20.6.9) — the iterated double sums in DLMF's order (inner m, outer n),
    # via the exact Hurwitz closed-form inner sum (see `_lattice_inner` above);
    # anchored in verify() at π²/sin²(πa), G₂(i) = π, the literal defining double
    # sums, end-to-end 20.6.2, and the 20.6.10 inter-relations.
    "latticeDelta": ("fn", _lattice_delta),
    "latticeAlpha": ("fn", _lattice_alpha),
    "latticeBeta":  ("fn", _lattice_beta),
    "latticeGamma": ("fn", _lattice_gamma),
    # JacobiThetaQuotient.lean's duplicates of the modulus quotients (same DLMF 22.2 anchors)
    "kModulus":      ("fn", _elliptic_modulus),
    "kComplModulus": ("fn", _complementary_modulus),
    # Carlson symmetric R_F (DLMF 19.16.1) — mpmath `elliprf` IS R_F, anchored
    # R_F(x,x,x) = x^{-1/2}; FLMF `carlsonRF` (Ch20WatsonRelations.lean) is real
    "carlsonRF": ("fn", lambda x, y, z: mp.elliprf(x, y, z)),
    # real minor Jacobi functions (DLMF 22.2.10: pq = pr/qr with nn = 1), on the
    # amplitude-based real jacobiSn/Cn/Dn (u, MODULUS k) bound above
    "jacobiNs": ("fn", lambda u, k: 1 / _jacobi("sn")(u, k)),
    "jacobiNc": ("fn", lambda u, k: 1 / _jacobi("cn")(u, k)),
    "jacobiNd": ("fn", lambda u, k: 1 / _jacobi("dn")(u, k)),
    "jacobiSc": ("fn", lambda u, k: _jacobi("sn")(u, k) / _jacobi("cn")(u, k)),
    "jacobiSd": ("fn", lambda u, k: _jacobi("sn")(u, k) / _jacobi("dn")(u, k)),
    "jacobiCd": ("fn", lambda u, k: _jacobi("cn")(u, k) / _jacobi("dn")(u, k)),
    "jacobiCs": ("fn", lambda u, k: _jacobi("cn")(u, k) / _jacobi("sn")(u, k)),
    "jacobiDs": ("fn", lambda u, k: _jacobi("dn")(u, k) / _jacobi("sn")(u, k)),
    "jacobiDc": ("fn", lambda u, k: _jacobi("dn")(u, k) / _jacobi("cn")(u, k)),
    # Laguerre family (DLMF 18) — generalized Lₙ^(α) on (0,∞), weight x^α e^{−x}
    "laguerreWeight": ("fn", lambda a, x: x ** a * mp.e ** (-x)),
    "laguerreNormSq": ("fn", lambda a, n: mp.gamma(int(n) + a + 1) / mp.factorial(int(n))),
    # polynomial families (k, x)
    "T":  ("poly", _chebyt),     # Chebyshev first kind   (T ℝ k).eval x
    "U":  ("poly", _chebyu),     # Chebyshev second kind
    # FULLY-QUALIFIED Chebyshev Tₙ (DLMF 18.3): the head `Polynomial.Chebyshev.T` whose leading
    # `Polynomial`/`Chebyshev` segments are NOT in the namespace-strip list, so it must bind
    # here exactly. Same first-kind Tₙ as `T` above (anchored T₅(cos θ)=cos 5θ).
    "Polynomial.Chebyshev.T": ("poly", _chebyt),
    # FULLY-QUALIFIED Chebyshev Uₙ (DLMF 15.9.6 / 18.3): head `Polynomial.Chebyshev.U`,
    # whose `Polynomial`/`Chebyshev` segments are NOT stripped, so it must bind exactly
    # here. Same second-kind Uₙ as `U` above (anchored U₄(cos θ)·sin θ = sin 5θ).
    "Polynomial.Chebyshev.U": ("poly", _chebyu),
    "hermite": ("poly", _hermite_prob),   # probabilists' Heₙ (see §5.1)
    # MISNAMED legacy `physHermite` (Hermite/Normalization.lean): the Lean body is
    # `(hermite n).comp (C 2 * X)` = Heₙ(2x), NOT the physicists' Hₙ (He₂(2x)=4x²−1
    # vs H₂=4x²−2).  Bound to the def's TRUE semantics via the anchored probabilists'
    # map at 2x — matching the short-name registry entry, which was always correct.
    # (This FQ exact-key entry previously bound `_phys_hermite` = genuine Hₙ by NAME:
    # the false-PASS trap of ERRATA `physhermite-not-physicist`, fixed 2026-08-14.)
    # Bound under the FULLY-QUALIFIED head so the namespace stripper's poly-collision
    # guard is bypassed by the exact-key match; used via `Polynomial.aeval z (physHermite n)`.
    "FLMF.Functions.Hermite.physHermite":
        ("poly", lambda k, x: _hermite_prob(int(k), 2 * x)),
    # The GENUINE physicists' Hₙ (recurrence-defined, DLMF 7.10/18.3) — the correct
    # carrier for the 7.10.1 / 7.18.8 displays.
    "FLMF.Functions.Hermite.physicistsHermite": ("poly", _phys_hermite),
    # generalized Laguerre Lₙ^(α): (laguerre α n).eval x — TWO indices (param α, degree n)
    "laguerre": ("lpoly", lambda n, a, x: mp.laguerre(n, a, x)),
    # ascending (rising) Pochhammer (x)ₙ = x(x+1)…(x+n−1): (ascPochhammer ℝ n).eval x
    "ascPochhammer": ("poly", lambda n, x: mp.rf(x, n)),
    # Mathlib `Polynomial.bernoulli n` = Σ C(n,i)·B⁻ᵢ·X^{n−i} — the STANDARD Bₙ(x)
    # (B₁(0) = −1/2); mp.bernpoly is the same object (anchored; the Bₙ(x+1)/B⁺
    # variant differs at B₁(0) = +1/2). `bernoulliPoly n` is the FLMF abbrev for it.
    "Polynomial.bernoulli": ("poly", lambda n, x: mp.bernpoly(int(n), x)),
    "bernoulliPoly": ("poly", lambda n, x: mp.bernpoly(int(n), x)),
    "bernoulliPolyReal": ("fn", lambda n, x: mp.bernpoly(int(n), x)),   # = (bernoulliPoly n).eval x over ℝ
    # FLMF `bR n t = aeval t (Polynomial.bernoulli n)` (Bernoulli/Duplication.lean:42) — the
    # real Bernoulli polynomial Bₙ(t) (DLMF §24.2), the SAME object as `bernoulliPolyReal`
    # (aeval over ℝ = .eval); it is the `dupl` duplication-formula helper's atom. mp.bernpoly
    # is the STANDARD Bₙ (B₁(0) = −1/2, matching Mathlib `Polynomial.bernoulli`). This is the
    # only `bR` def in the corpus. Anchored in verify() at B₀=1, B₁(t)=t−½, B₂(t)=t²−t+⅙.
    "bR": ("fn", lambda n, t: mp.bernpoly(int(n), t)),
    # FLMF Euler polynomial `eulerPoly n : ℚ[X]` (EulerPolynomials.lean; DLMF §24.2),
    # DEFINED by the Bernoulli bridge Eₙ(x) = (2/(n+1))(B_{n+1}(x) − 2^{n+1}B_{n+1}(x/2))
    # (A&S 23.1.27) = the STANDARD Eₙ of the g.f. 2e^{xt}/(eᵗ+1) = Σ Eₙ(x)tⁿ/n!
    # = mp.eulerpoly. Anchored in verify() against BOTH the defining g.f. Taylor
    # coefficient AND the Lean bridge formula (via mp.bernpoly, independent of
    # mp.eulerpoly's internals); E₁(0) = −1/2 pins the convention (an Euler-number-style
    # normalization Ẽₙ(x) = 2ⁿEₙ(x/…) or a B⁺-based bridge would disagree there).
    "eulerPoly": ("poly", lambda n, x: mp.eulerpoly(int(n), x)),
    # Mathlib Bernoulli exponential generating functions (DLMF 24.2.1):
    # `bernoulliPowerSeries A = mk (n ↦ Bₙ/n!)`, `bernoulli'PowerSeries A = mk (n ↦ B'ₙ/n!)`
    # ∈ A⟦X⟧ — psfn1 rows: the one explicit argument is the TYPE A, dropped exactly as the
    # extractor drops it for `PowerSeries.exp A`, and the value is the analytic generating
    # function at the sampled indeterminate, x/(eˣ−1) resp. x·eˣ/(eˣ−1) (removable value 1
    # at x = 0; radius 2π ⊇ the indeterminate grid). Sound necessary condition (the psfn
    # argument, cf. catalanSeries): the coefficients are algebraMap-images of the ℚ values,
    # so the ∀-A formal identity implies the A = ℝ analytic identity near 0. Anchored in
    # verify() by Taylor-extracting [tⁿ] against the DEFINING mk-coefficients Bₙ/n! and
    # B'ₙ/n! — [t¹] = −1/2 vs +1/2 is exactly the point where the two conventions differ.
    "bernoulliPowerSeries": ("psfn1",
                             lambda _A, t: t / mp.expm1(t) if t != 0 else mp.mpf(1)),
    "bernoulli'PowerSeries": ("psfn1",
                              lambda _A, t: t * mp.e ** t / mp.expm1(t) if t != 0 else mp.mpf(1)),
    # `Polynomial.C c` — the constant-polynomial embedding; under indeterminate-sampling it
    # contributes its scalar value (so `bernoulliPoly 1 = X − C 2⁻¹` reads x − 1/2).
    "C": ("fn", lambda c: c),
    # ── Class-A coverage: heads that previously threw "unbound head …" INSIDE
    # evaluate and so skipped as the misleading "undersampled/domain". All anchored. ──
    # Complete elliptic integrals (DLMF 19.2): FLMF completeK/E take the MODULUS k
    # (completeK k = ellipticF(π/2,k)); mpmath ellipk/ellipe take the PARAMETER m = k².
    "completeK": ("fn", _complete_k),
    # Exact qualified heads in the real Jacobi-elliptic namespace.  The bare
    # `complementaryModulus` registry entry is the theta τ-function and must not
    # be reused here: this one is k ↦ √(1-k²).
    "FLMF.JacobiElliptic.completeK": ("fn", _complete_k),
    "FLMF.JacobiElliptic.complementaryModulus":
        ("fn", lambda k: _rsqrt(1 - k ** 2)),
    "completeE": ("fn", _complete_e),
    # Gegenbauer Cₙ^(λ)(x) / Jacobi Pₙ^(α,β)(x) (DLMF 18.5): mpmath arg order is
    # (degree, params…, x); FLMF order is (params…, degree, x).
    "gegenbauer": ("fn", lambda lam, n, x: mp.gegenbauer(int(n), lam, x)),
    "FLMF.Gegenbauer.gegenbauer": ("fn", lambda lam, n, x: mp.gegenbauer(int(n), lam, x)),
    "jacobiP": ("fn", lambda a, b, n, x: mp.jacobi(int(n), a, b, x)),
    "FLMF.Jacobi.jacobiP": ("fn", lambda a, b, n, x: mp.jacobi(int(n), a, b, x)),
    # probabilists' Hermite Heₙ(x) in FUNCTION form (He n x = aeval x (hermite n)) —
    # same object as the `hermite` poly row, here applied with explicit args.
    "He": ("fn", lambda n, x: _hermite_prob(int(n), x)),
    # Gaussian orthogonality weight for the probabilists' Hermite family
    # (FLMF.Functions.Hermite.gaussWeight x = exp(−x²/2); the DLMF §18.3 He weight).
    "gaussWeight": ("fn", lambda x: mp.e ** (-(x ** 2) / 2)),
    # Parabolic cylinder fundamental solutions (DLMF 12.4.1-2) via the bound ₁F₁:
    # w₁(a,x)=e^{−x²/4}·₁F₁(a/2+¼;½;x²/2), w₂(a,x)=x·e^{−x²/4}·₁F₁(a/2+¾;3/2;x²/2).
    "pcfEven": ("fn", lambda a, x: mp.e ** (-x ** 2 / 4)
                * _kummerM(a / 2 + mp.mpf(1) / 4, mp.mpf(1) / 2, x ** 2 / 2)),
    "pcfOdd": ("fn", lambda a, x: x * mp.e ** (-x ** 2 / 4)
               * _kummerM(a / 2 + mp.mpf(3) / 4, mp.mpf(3) / 2, x ** 2 / 2)),
    # Hurwitz zeta ζ(s,a) = Σ_{n≥0} (n+a)^{−s} (DLMF 25.11) = mp.zeta(s,a).
    "hurwitzZeta": ("fn", lambda s, a: mp.zeta(s, a)),
    # Mathlib `HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s` — arg order (a, s), a ∈ [0,1).
    "HurwitzZeta.hurwitzZeta": ("fn", lambda a, s: mp.zeta(s, a)),
    # Lerch transcendent Φ(z,s,a) = Σ_{n≥0} zⁿ/(n+a)^s (DLMF 25.14) = mp.lerchphi.
    "lerchPhi": ("fn", lambda z, s, a: mp.lerchphi(z, s, a)),
    # DLMF 8.11.2 asymptotic coefficient Pₙ(a) for the upper incomplete Γ expansion.
    "asyCoeff": ("fn", _asy_coeff),
    # q-Pochhammer (a;q)ₙ = ∏_{k<n}(1 − a qᵏ) (DLMF 17.2) = mp.qp.
    "qPochhammer": ("fn", lambda a, q, n: mp.qp(a, q, int(n))),
    # Bell numbers Bₙ and von Mangoldt Λ(n) — exact integer / prime-power routines.
    "bell": ("fn", lambda n: _bell(n)), "Nat.bell": ("fn", lambda n: _bell(n)),
    "vonMangoldt": ("fn", lambda n: _von_mangoldt(n)),
    "ArithmeticFunction.vonMangoldt": ("fn", lambda n: _von_mangoldt(n)),
    # Second Chebyshev function ψ(x) = Σ_{n ≤ x} Λ(n) (DLMF 27.2.11; Mathlib
    # `Chebyshev.psi`, FLMF.Chebyshev.psi). Anchored in verify() at hand-computable
    # values of the defining sum (ψ(2)=log 2, ψ(10)=3log2+2log3+log5+log7, …).
    "psi": ("fn", _chebyshev_psi),
    "Chebyshev.psi": ("fn", _chebyshev_psi),
    # First Chebyshev function ϑ(x) = Σ_{p ≤ x, p prime} log p (DLMF 27.2.11; Mathlib
    # `Chebyshev.theta`, FLMF.Chebyshev.theta — the lone bare-`theta` head in the FLMF
    # surface corpus, no collision with the §20 theta functions, which bind as
    # jacobiTheta/θ₁..θ₄). Anchored in verify() at hand-computable values of the
    # defining sum (ϑ(2)=log 2, ϑ(10)=log 210, ϑ(1.9)=0, floor step, negative clamp).
    "theta": ("fn", _chebyshev_theta),
    "Chebyshev.theta": ("fn", _chebyshev_theta),
    # Stirling 2nd kind S(n,k) (FLMF `partition`) and falling factorial (descPochhammer).
    # Catalan ordinary generating function C(x)=Σ Cₙxⁿ=(1−√(1−4x))/(2x); the formal identity
    # xC²−C+1=0 is algebraic (holds on the whole principal branch), so the analytic check is
    # a sound necessary condition for the ℤ⟦X⟧ relation. (psfn = power series via its g.f.)
    "catalanSeries": ("psfn", lambda x: (1 - mp.sqrt(1 - 4 * x)) / (2 * x)),
    # Hermite generating function `hermiteGF x = PowerSeries.mk (n ↦ Heₙ(x)/n!)` ∈ ℚ⟦t⟧
    # (GeneratingFunctions.lean): numerically its ENTIRE generating function, the DLMF
    # 18.12.16 DEFINING formula e^{xt − t²/2} = Σₙ Heₙ(x) tⁿ/n! (probabilists' Heₙ).
    # (psfn1 = one-parameter power-series family: called with the evaluated parameter x
    # and the indeterminate t; the psfn soundness argument applies — the g.f. is entire,
    # so its Taylor coefficients at 0 ARE the formal coefficients.)  Anchored in verify()
    # at the defining coefficient property [t³]@x=2 = He₃(2)/3! = 1/3, which REJECTS the
    # physicists' g.f. e^{2xt−t²} of DLMF 18.12.15 ([t³]@x=2 = H₃(2)/3! = 20/3).
    "hermiteGF": ("psfn1", lambda x, t: mp.e ** (x * t - t ** 2 / 2)),
    "dedekindSum": ("fn", _dedekind_sum),    # Dedekind sum s(h,k)
    "sawtooth": ("fn", _sawtooth),           # Dedekind sawtooth ((x)) (DLMF 27.14)
    "liouville": ("fn", _liouville),         # Liouville λ(n)=(−1)^Ω(n)
    "ArithmeticFunction.liouville": ("fn", _liouville),
    # von Staudt–Clausen correction Σ_{(p−1) ∣ 2k} 1/p (DLMF 24.10; VonStaudtClausen.lean)
    "vonStaudtSum": ("fn", _von_staudt_sum),
    "μ": ("fn", lambda n: _mobius(n)),       # Möbius (ArithmeticFunction.moebius)
    "ArithmeticFunction.moebius": ("fn", lambda n: _mobius(n)),
    # Ramanujan's sum c_q(n) (DLMF 27.10.1 Hölder form = the FLMF def; anchored in
    # verify() to the decorrelated 27.10.2 exponential sum).
    "ramanujanSum": ("fn", lambda q, n: _ramanujan_sum(q, n)),
    # ArithmeticFunction.pow k = (n ↦ nᵏ) with n^0=1 for n≥1; applied as `pow k m`.
    "ArithmeticFunction.pow": ("fn", lambda k, m: mp.mpf(int(m)) ** int(k)),
    "partition": ("fn", _stirling2),
    "cycle": ("fn", _stirling1u),       # unsigned Stirling 1st kind (rising-factorial coeffs)
    "descPochhammer": ("poly", lambda k, x: _falling(x, k)),
    # FLMF `fallingFactorial n x = (descPochhammer ℝ n).eval x` (FallingFactorial.lean;
    # DLMF §5.2/§26.8) — the SAME falling factorial x(x−1)⋯(x−n+1) as the poly row above,
    # in FUNCTION form with FLMF arg order (n, x). Anchored in verify() at a non-integer
    # point where falling vs rising disagree, plus the DLMF 5.2 reflection against mp.rf.
    "fallingFactorial": ("fn", lambda n, x: _falling(x, n)),
    # Eulerian numbers ⟨n,k⟩ + generalized binomial rbinom(y,n)=C(y,n)=ff_n(y)/n! (Eulerian.lean).
    "eulerian": ("fn", _eulerian),
    "rbinom": ("fn", lambda y, n: _falling(y, n) / mp.factorial(_nat(n, "rbinom"))),
    # Ein(x) = ∫₀ˣ (1−e^{−t})/t dt (E1Series.lean) — complementary exponential integral,
    # bound via its integral def (decorrelated from the series/E₁ relations it's tested against).
    "Ein": ("fn", lambda x: mp.quad(lambda t: (1 - mp.e ** (-t)) / t if t != 0 else mp.mpf(1),
                                    [0, x])),
    # Discrete orthogonal polynomials (DLMF 18.20) as their terminating hypergeometric forms,
    # decorrelated from the explicit Pochhammer-sum defs: Charlier ₂F₀(−n,−x;;−1/a),
    # Krawtchouk ₂F₁(−n,−x;−N;1/p), Meixner ₂F₁(−n,−x;β;1−1/c). Arg order matches FLMF.
    "qbinom":     ("fn", _qbinom),       # Gaussian binomial [n,k]_q (arg order q n k)
    "charlier":   ("fn", lambda a, n, x: mp.hyper([-int(n), -x], [], -1 / a)),
    "krawtchouk": ("fn", lambda p, N, n, x: mp.hyp2f1(-int(n), -x, -int(N), 1 / p)),
    "meixner":    ("fn", lambda b, c, n, x: mp.hyp2f1(-int(n), -x, b, 1 - 1 / c)),
    # fully-qualified aliases (the HypergeometricBridge rows print namespaced names).
    "FLMF.Krawtchouk.krawtchouk": ("fn", lambda p, N, n, x: mp.hyp2f1(-int(n), -x, -int(N), 1 / p)),
    "FLMF.Meixner.meixner": ("fn", lambda b, c, n, x: mp.hyp2f1(-int(n), -x, b, 1 - 1 / c)),
    # Continuous Hahn pₙ(x;a,b,c,d) (DLMF §18.20) — complex-valued terminating ₃F₂,
    # FLMF arg order (a,b,c,d,n,x); anchored in verify() (p₀, degree-one p₁, a↔b symmetry).
    "continuousHahn": ("fn", _continuous_hahn),
    "FLMF.ContinuousHahn.continuousHahn": ("fn", _continuous_hahn),
    # Dual Hahn Rₙ(λ(x);γ,δ,N) (DLMF 18.20.5) — terminating ₃F₂ at unit argument on the
    # quadratic lattice λ(x)=x(x+γ+δ+1); FLMF arg order (γ,δ,N,n,x); anchored in verify()
    # (DLMF 18.22 / KLS 1.6.2 recurrence built upward from R₀=1, Rₙ(λ(0))=1, hand R₁).
    "dualHahn": ("fn", _dual_hahn),
    "FLMF.DualHahn.dualHahn": ("fn", _dual_hahn),
    # Dual Hahn three-term-recurrence coefficients A_{n+1}, C_{n+1} (DLMF 18.22 /
    # KLS 1.6.2, the dhA/dhCC defs of DualHahn.lean); FLMF arg orders (γ,N,n) /
    # (δ,N,n); anchored in verify() (shifted-index match inside the anchored 18.22
    # upward recurrence + the recurrence role against the ₃F₂ binding).
    "dhA": ("fn", _dh_A),
    "FLMF.DualHahn.dhA": ("fn", _dh_A),
    "dhCC": ("fn", _dh_CC),
    "FLMF.DualHahn.dhCC": ("fn", _dh_CC),
    # Meixner–Pollaczek Pₙ^{(λ)}(x;φ) (DLMF §18.20, Table 18.19.1) — complex-prefactor
    # terminating ₂F₁ with real value; FLMF arg order (λ,φ,n,x); anchored in verify()
    # (DLMF §18.9 / KLS 9.7.3 recurrence built upward from P₀=1 and hand P₁, realness).
    "meixnerPollaczek": ("fn", _meixner_pollaczek),
    "FLMF.MeixnerPollaczek.meixnerPollaczek": ("fn", _meixner_pollaczek),
    # Al-Salam–Chihara Qₙ(x;a,b|q) (DLMF §18.28 / KLS 14.8) and its real q-quadratic
    # building block ascFactor = ∏_{m<k}(1−2aqᵐx+a²q^{2m}) — the conjugate-pair
    # (ae^{±iθ};q)_k product at x = cos θ. FLMF arg orders (a,b,q,n,x) / (a,q,k,x).
    "alSalamChihara": ("fn", _al_salam_chihara),
    "FLMF.AlSalamChihara.alSalamChihara": ("fn", _al_salam_chihara),
    "ascFactor": ("fn", _asc_factor),
    "FLMF.AlSalamChihara.ascFactor": ("fn", _asc_factor),
    # Christoffel–Darboux abstract surface (DLMF 18.2.12, ChristoffelDarboux.lean):
    # the Chebyshev-T witness triple instantiating the ∀-quantified (p, h, a) of an
    # `IsCDSystem p h a x y` hypothesis binder (fidelity_extract '_fnwitness'; the
    # hypothesis clauses are anchored in verify() before the sweep trusts it). The
    # companion heads cdSummand/cdCross are HIGHER-ORDER (function arguments) and are
    # special-cased in fidelity_extract's evaluate → ob._cd_summand/_cd_cross, not here.
    "cdChebP": ("fn", _cd_cheb_p),
    "cdChebH": ("fn", _cd_cheb_h),
    "cdChebA": ("fn", _cd_cheb_a),
    # confluent form (DLMF 18.2.13, `IsConfluentCDSystem p h D x`): Dₖ(x) reuses the
    # SAME Chebyshev-T witness, with the row's x threaded by the 'cdChebD@x' spec.
    "cdChebD": ("fn", _cd_cheb_d),
    # ── A2 Bessel/Struve/Kelvin/Lommel/Anger cluster (lane A2 unbound heads) ─────────
    # Anger integrand (DLMF 11.10.1 integrand; an INTEGRAND, not the Anger function):
    "angerIntegrand": ("fn", _anger_integrand),
    # Hankel H⁽¹⁾/H⁽²⁾ = J ± iY (DLMF 10.4.3; FLMF defs are literally these combinations
    # of real-order besselJnu/besselYnu — the ± i sign is the convention hazard, anchored
    # against the independent mp.hankel1/mp.hankel2):
    "besselHankel1": ("fn", _bessel_hankel1),
    "besselHankel2": ("fn", _bessel_hankel2),
    # real-order Y_ν (DLMF 10.2.3): FLMF besselYnu is the reflection formula
    # (J_ν cos νπ − J_{−ν})/sin νπ — mp.bessely IS that for non-integer ν (anchored).
    # CAUTION: at INTEGER ν the Lean def is junk (0/0 → 0) while mp.bessely takes the
    # DLMF ν→n limit; rows there compare DLMF-side objects consistently.
    "besselYnu": ("fn", lambda nu, z: mp.bessely(nu, z)),
    # integer-order modified I_n (DLMF 10.25.2 via natAbs symmetry 10.27.1):
    "besselI": ("fn", _besselI_int),
    # the `n.natAbs` ATOM (Int.natAbs of the ℤ-binder n; besselI_neg's (−1)^n.natAbs):
    "n.natAbs": ("envfn", _natAbs_env),
    # I₀ via its cosine integral (DLMF 10.32.1) — besselI0Int M = (1/π)∫₀^π e^{M cos θ}dθ
    # = I₀(M) for ALL real M (anchored by quadrature; pins the 1/π-on-[0,π] normalization
    # against the 1/(2π)-on-[0,π] rival):
    "besselI0Int": ("fn", lambda M: mp.besseli(0, M)),
    # series TERM functions (DLMF 10.2.2 / 11.2.1 / 11.2.2 summands, not the functions):
    "besselJnuTerm": ("fn", _besselJnu_term),
    "struveHTerm": ("fn", lambda nu, z, m: _struve_term(-1, nu, z, m)),
    "struveLTerm": ("fn", lambda nu, z, m: _struve_term(1, nu, z, m)),
    # K_ν cosh-integral representation (DLMF 10.32.9; = K_ν(x) for x > 0, junk-raise else):
    "besselK_cosh": ("fn", _besselK_cosh),
    # Watson amplitude for the K_ν Laplace representation (DLMF 10.32.8 rescaled;
    # an AMPLITUDE (1+t/2)^{ν−1/2}, not K_ν) — see the liW NOTE above for why this
    # is now safe to bind:
    "besselKAmplitude": ("fn", _besselK_amplitude),
    # Kelvin cluster (DLMF 10.61): rotation angles e^{3πi/4} (J-side) / e^{πi/4} (K-side),
    # prefactor e^{−nπi/2}, complex-argument J_n, and ber/bei = Re/Im J_n(x e^{3πi/4})
    # (mp.ber/mp.bei are the same DLMF convention — anchored against mp.besselj on the
    # rotated ray, which rejects the e^{πi/4}-angle rival for the J-side):
    "kelvinAngleJ": ("const", mp.expjpi(mp.mpf(3) / 4)),
    "kelvinAngleK": ("const", mp.expjpi(mp.mpf(1) / 4)),
    "kelvinKPrefactor": ("fn", lambda n: mp.expjpi(-_nat(n, "kelvinKPrefactor") / mp.mpf(2))),
    "besselJC": ("fn", lambda n, z: mp.besselj(_nat(n, "besselJC"), z)),
    "kelvinBer": ("fn", lambda n, x: mp.ber(_nat(n, "kelvinBer"), x)),
    "kelvinBei": ("fn", lambda n, x: mp.bei(_nat(n, "kelvinBei"), x)),
    # NOTE: kelvinKerOf/kelvinKeiOf are NOT bound — their first argument is a
    # ∀-quantified FUNCTION K : ℂ → ℂ (an abstract K_n stand-in; Mathlib has no complex
    # modified Bessel K), which the 'fn' kind cannot receive. Rows through them stay
    # honest structural skips (unbound:K).
    # Lommel functions (DLMF 11.9): small s_{μ,ν} (11.9.3, via ₁F₂), the 11.9.5
    # prefactor/homogeneous combination, and big S_{μ,ν} (11.9.5) over sampled Bessel data:
    "lommelS": ("fn", _lommel_small_s),
    "lommelBigGamma": ("fn", _lommel_big_gamma),
    "lommelBigHomog": ("fn", _lommel_big_homog),
    "lommelBigS": ("fn", _lommel_big_S),
}

# ── Wigner / Racah / Clebsch–Gordan symbols (M12) via sympy, the independent
# implementation (mpmath has none). Registered only when sympy is importable, so a
# stripped env degrades to honest skips. Argument conventions match the FLMF defs:
#   wigner3j j₁ j₂ j₃ m₁ m₂ m₃  = ⎛j₁ j₂ j₃; m₁ m₂ m₃⎞           (DLMF 34.2; sympy same order)
#   wigner6j j₁ j₂ j₃ l₁ l₂ l₃  = {j₁ j₂ j₃; l₁ l₂ l₃}            (DLMF 34.4.2; sympy same order)
#   clebschGordan j₁ m₁ j₂ m₂ j₃ m₃ = ⟨j₁m₁ j₂m₂|j₃m₃⟩            (sympy clebsch_gordan reorders to j,j,j,m,m,m)
#   racahW a b c d e f = W(abcd;ef)                              (DLMF 34.4.1; sympy racah same order)
if _HAVE_SYMPY:
    REGISTRY["wigner3j"] = ("fn", lambda j1, j2, j3, m1, m2, m3:
                            _sym(_sy_3j(int(j1), int(j2), int(j3), int(m1), int(m2), int(m3))))
    REGISTRY["wigner6j"] = ("fn", lambda j1, j2, j3, l1, l2, l3:
                            _sym(_sy_6j(int(j1), int(j2), int(j3), int(l1), int(l2), int(l3))))
    REGISTRY["clebschGordan"] = ("fn", lambda j1, m1, j2, m2, j3, m3:
                                 _sym(_sy_cg(int(j1), int(j2), int(j3), int(m1), int(m2), int(m3))))
    REGISTRY["racahW"] = ("fn", lambda a, b, c, d, e, f:
                          _sym(_sy_racah(int(a), int(b), int(c), int(d), int(e), int(f))))
    # Jacobi symbol (M14) — sympy.jacobi_symbol is the independent implementation
    REGISTRY["jacobiSym"] = ("fn", _jacobi_sym)
    # Legendre symbol (DLMF 27.9) — Mathlib `legendreSym p a` = (a|p), prime FIRST;
    # sympy.legendre_symbol(a, p) is the independent implementation (args swapped)
    REGISTRY["legendreSym"] = ("fn", _legendre_sym)
    REGISTRY["wigner6jOrthSum"] = ("fn", _wigner6j_orth_sum)   # 6j orthogonality sum (M16)
    REGISTRY["wigner9j"] = ("fn", _wigner9j)                   # DLMF 34.6.2 (= sympy wigner_9j)
    REGISTRY["wigner9jTerm"] = ("fn", _wigner9j_term)          # one summand of the 9j defining sum
    REGISTRY["wigner9jOrthSum"] = ("fn", _wigner9j_orth_sum)   # 9j orthogonality (DLMF 34.6.4)
    REGISTRY["biedenharnElliottSum"] = ("fn", _biedenharn_elliott_sum)  # DLMF 34.4.4
    REGISTRY["orthSum"] = ("fn", _orth_sum)                    # 3j magnetic orthogonality (34.3.18)


# ── A3 hypergeometric / special-values / misc cluster (Agent A3, 2026-07-21) ─────────
# Heads: Appell F₁/F₂, Frobenius-instance gaussP/Q/R + frobCoeff, Whittaker M/W +
# tricomiIntegrand, NormedSpace.exp, Heun (heunB/heunCoeff/heunSeries/heunOp +
# constantCoeff), Laplace transform + fC, physHermite, algCoeff, q-exponentials
# (qExp/qExpE/qPochhammerInf), Complex.cot, and the DLMF 7.13 zero-parameter defs.
class _FPS:
    """A formal power series as an exact coefficient callable (`.coeff n` = the n-th
    coefficient, mp-valued) — the Tier-1 shadow of a Lean `PowerSeries 𝕂` VALUE
    appearing as an argument of a registry head (`frobCoeff gaussP …`,
    `heunOp … (heunSeries …)`, `constantCoeff (heunSeries …)`). Var-position series
    bind as ('const', _FPS); applied constructors as ('fn', … → _FPS). Consumed only
    by `frobCoeff` / `heunOp` / `constantCoeff`; leaking one into scalar arithmetic
    raises (honest point drop), never a number."""

    def __init__(self, coeff_fn):
        self._c = coeff_fn

    def coeff(self, n):
        return self._c(int(n))


def _fps_of_list(cs):
    """Polynomial-tail series: coefficients `cs` then 0."""
    lst = [mp.mpmathify(c) for c in cs]
    return _FPS(lambda j: lst[j] if 0 <= j < len(lst) else mp.mpf(0))


def _constant_coeff(S):
    """Lean `PowerSeries.constantCoeff` (prefix `constantCoeff (R := 𝕂) S`, the type
    named-arg is dropped by the parser): the 0-th coefficient of an _FPS operand."""
    if isinstance(S, _FPS):
        return S.coeff(0)
    raise ValueError("constantCoeff: operand is not a power-series object")


def _frob_coeff(P, Q, R, rho, n):
    """FLMF `frobCoeff P Q R ρ n` (Methods/Frobenius.lean, DLMF §2.7(i)): a₀ = 1 and
    the full-history recurrence aₙ = −(Σ_{k<n} f_{n−k}(ρ+k)·aₖ)/f₀(ρ+n) with the
    symbol fⱼ(s) = Pⱼ·s(s−1) + Qⱼ·s + Rⱼ (frobSymbol). P, Q, R arrive as _FPS
    coefficient objects (gaussP/gaussQ/gaussR below). Junk (division by zero) exactly
    where the Lean def is junk — a degenerate ρ raises and the point drops."""
    for S in (P, Q, R):
        if not isinstance(S, _FPS):
            raise ValueError("frobCoeff: non-power-series argument")
    n = _nat(n, "frobCoeff")

    def sym(j, s):
        return P.coeff(j) * (s * (s - 1)) + Q.coeff(j) * s + R.coeff(j)

    a = [mp.mpf(1)]
    for m in range(1, n + 1):
        a.append(-mp.fsum(sym(m - k, rho + k) * a[k] for k in range(m)) / sym(0, rho + m))
    return a[n]


def _heunB(a, q, al, be, ga, de, n):
    """FLMF `heunB a q α β γ δ n` (Frameworks/Heun.lean, DLMF 31.3.4 bracket):
    B_n = (1+a)n(n−1) + (γ(1+a)+δa+ε)n + q with ε = α+β+1−γ−δ."""
    return ((1 + a) * n * (n - 1)
            + (ga * (1 + a) + de * a + (al + be + 1 - ga - de)) * n + q)


def _heun_coeff_list(a, q, al, be, ga, de, N):
    """First N+1 local Heun coefficients c₀=1, c₁=q/(aγ), and the DLMF 31.3.7
    three-term recurrence c_{n+2} = (B_{n+1}c_{n+1} − (n+α)(n+β)cₙ)/(a(n+2)(n+1+γ))."""
    c = [mp.mpf(1)]
    if N >= 1:
        c.append(q / (a * ga))
    for m in range(N - 1):
        c.append((_heunB(a, q, al, be, ga, de, m + 1) * c[m + 1]
                  - (m + al) * (m + be) * c[m]) / (a * (m + 2) * (m + 1 + ga)))
    return c


def _heun_coeff(a, q, al, be, ga, de, n):
    """FLMF `heunCoeff a q α β γ δ n` — the n-th local Heun Taylor coefficient
    (DLMF 31.3.1–31.3.7; junk division-by-zero mirrors the Lean def at aγ = 0 etc.)."""
    n = _nat(n, "heunCoeff")
    return _heun_coeff_list(a, q, al, be, ga, de, n)[n]


def _heun_series(a, q, al, be, ga, de):
    """FLMF `heunSeries a q α β γ δ = PowerSeries.mk (heunCoeff …)` as an _FPS."""
    cache = {}

    def cf(n):
        if n < 0:
            return mp.mpf(0)
        if n not in cache:
            cs = _heun_coeff_list(a, q, al, be, ga, de, n)
            for j, v in enumerate(cs):
                cache[j] = v
        return cache[n]

    return _FPS(cf)


_HEUN_FN_MAXTERMS = 6000
_HEUN_FN_CACHE = {}


def _heun_fn(a, q, al, be, ga, de, z):
    """FLMF `heunFn a q α β γ δ z` (Frameworks/Heun/Analytic.lean) — the **local Heun
    function** `Hℓ(a,q;α,β,γ,δ;z)` as the SUM of its Maclaurin series `∑ c_k z^k`,
    `c_k = heunCoeff a q α β γ δ k` (DLMF 31.3.1 with 31.3.2–31.3.7; normalization
    `Hℓ(…;0) = 1`).  This is literally the Lean definition
    `heunFn … = (ofScalars 𝕜 (heunCoeff …)).sum`, i.e. `∑' k, c_k z^k`, evaluated
    through the already-anchored `_heun_coeff_list` recurrence.

    Meaningful only where that series converges — the disc `|z| < min(1,|a|)`
    (`heunCoeff_radius_ge`).  Outside the disc, and whenever the truncation has not
    settled to working precision within the term cap, this RAISES: the Lean `tsum` is
    junk there, so the sample must drop honestly rather than take a fabricated value.
    Coefficients are cached per (precision, parameters) so the repeated evaluations of
    a numerical `mp.diff` do not re-run the recurrence."""
    rad = min(mp.mpf(1), abs(a))
    if not abs(z) < rad:
        raise ValueError("heunFn: |z| outside the Maclaurin disc min(1,|a|)")
    key = (mp.mp.prec, a, q, al, be, ga, de)
    cs = _HEUN_FN_CACHE.get(key)
    tol = mp.mpf(2) ** (-mp.mp.prec + 8)
    n, run, tot, tmax, zp = 0, 0, mp.mpf(0), mp.mpf(0), mp.mpf(1)
    while n <= _HEUN_FN_MAXTERMS:
        if cs is None or n >= len(cs):
            if len(_HEUN_FN_CACHE) > 64:
                _HEUN_FN_CACHE.clear()
            cs = _heun_coeff_list(a, q, al, be, ga, de,
                                  max(64, n + 1, 2 * len(cs) if cs else 0))
            _HEUN_FN_CACHE[key] = cs
        t = cs[n] * zp
        tot += t
        tmax = max(tmax, abs(t))
        zp *= z
        run = run + 1 if abs(t) <= tol * max(mp.mpf(1), tmax, abs(tot)) else 0
        if run >= 4:
            return tot
        n += 1
    raise ValueError("heunFn: Maclaurin series did not settle within the term cap")


def _heunF0(a, al, be, ga, de, q, z):
    """FLMF `heunF0 a α β γ δ q z` (Heun/Ch31Orthogonality.lean) — the coefficient
    `f₀(q,z)` of **DLMF 31.9.4**, transcribed from that display's DEFINING right-hand
    side `f₀(q,z) = Hℓ(a,q;α,β,γ,δ;z)` (not from the Lean body): the local Heun
    function itself, in the argument order of the Lean signature. Inherits the
    `_heun_fn` disc guard (an out-of-disc sample drops honestly)."""
    return _heun_fn(a, q, al, be, ga, de, z)


def _heunF1(a, al, be, ga, de, q, z):
    """FLMF `heunF1 a α β γ δ q z` — the coefficient `f₁(q,z)` of **DLMF 31.9.4**,
    transcribed from that display's DEFINING right-hand side
    `f₁(q,z) = Hℓ(1−a, αβ−q; α,β,δ,γ; 1−z)`: the local Heun function carried to the
    singularity `z = 1` by the homography `z ↦ 1−z` of §31.2(v), which swaps `γ ↔ δ`
    (note the swapped γ/δ SLOTS below) and sends `q ↦ αβ−q`, `a ↦ 1−a`. verify()
    checks INDEPENDENTLY that the result solves Heun's equation 31.2.1 in `z` with the
    ORIGINAL parameters `(a,q,α,β,γ,δ)` — the substantive content of the dictionary."""
    return _heun_fn(1 - a, al * be - q, al, be, de, ga, 1 - z)


def _heun_wronskian_q(a, al, be, ga, de, q, ze):
    """`(∂/∂q) 𝒲{f₀(q,ζ), f₁(q,ζ)}` — the accessory-parameter derivative of the
    z-Wronskian `𝒲{f,g}(ζ) = f(ζ)g′(ζ) − f′(ζ)g(ζ)` (§1.13(i), FLMF
    `Methods.Floquet.wronskianD`) of the DLMF 31.9.4 pair, as it enters 31.9.3.
    Both derivatives are mpmath finite differences of the anchored `_heun_fn` sum."""
    def wro(p):
        def f(t):
            return _heunF0(a, al, be, ga, de, p, t)

        def g(t):
            return _heunF1(a, al, be, ga, de, p, t)

        return f(ze) * mp.diff(g, ze) - mp.diff(f, ze) * g(ze)

    return mp.diff(wro, q)


def _heunTheta(a, al, be, ga, de, ep, q, ze):
    """FLMF `heunTheta a α β γ δ ε q ζ` — the normalization constant `θ_m` of
    **DLMF 31.9.3**, transcribed from that display itself:

      θ = (1 − e^{2πiγ})(1 − e^{2πiδ}) ζ^γ (1−ζ)^δ (ζ−a)^ε
            · (f₀(q,ζ)/f₁(q,ζ)) · (∂/∂q) 𝒲{f₀(q,ζ), f₁(q,ζ)},

    with `f₀,f₁` the DLMF 31.9.4 coefficients (`_heunF0`/`_heunF1`) and the powers
    PRINCIPAL (`mp.power` = `Complex.cpow`, DLMF's "principal values at the beginning
    of the contour"). Every ingredient is independently anchored: `_heun_fn` against
    mp.hyp2f1 and the defining ODE, `_heunF1` against Heun's equation under the
    §31.2(v) homography."""
    return ((1 - mp.e ** (2 * mp.pi * mp.mpc(0, 1) * ga))
            * (1 - mp.e ** (2 * mp.pi * mp.mpc(0, 1) * de))
            * mp.power(ze, ga) * mp.power(1 - ze, de) * mp.power(ze - a, ep)
            * (_heunF0(a, al, be, ga, de, q, ze) / _heunF1(a, al, be, ga, de, q, ze))
            * _heun_wronskian_q(a, al, be, ga, de, q, ze))


_HEUN_OP_ORDER = 12


def _heun_op(a, q, al, be, ga, de, g):
    """FLMF `heunOp a q α β γ δ g` (DLMF 31.2.1, monomial form on 𝕂⟦X⟧):
    L g = (X³−(1+a)X²+aX)g″ + ((α+β+1)X² − (γ(1+a)+δa+ε)X + γa)g′ + (αβX − q)g.
    Computed EXACTLY at the coefficient level from g's coefficients (D1ₘ = (m+1)c_{m+1},
    D2ₘ = (m+2)(m+1)c_{m+2}). The returned VALUE is sup_{n ≤ 12} |coeff n (L g)| — a
    faithful truncated measure of the power-series identity `L g = 0` (0 iff the first
    13 output coefficients vanish; any wrong operator/series leaves an O(1) residual,
    see the verify() discriminator). Sound ONLY for comparison against the literal 0
    series, which is its sole Tier-1 consumer (heunSeries_isFormalSolution)."""
    if not isinstance(g, _FPS):
        raise ValueError("heunOp: operand is not a power-series object")
    eps = al + be + 1 - ga - de
    kmax = _HEUN_OP_ORDER

    def c(m):
        return g.coeff(m) if m >= 0 else mp.mpf(0)

    def D1(m):
        return (m + 1) * c(m + 1) if m >= 0 else mp.mpf(0)

    def D2(m):
        return (m + 2) * (m + 1) * c(m + 2) if m >= 0 else mp.mpf(0)

    out = mp.mpf(0)
    for n in range(kmax + 1):
        v = (D2(n - 3) - (1 + a) * D2(n - 2) + a * D2(n - 1)
             + (al + be + 1) * D1(n - 2)
             - (ga * (1 + a) + de * a + eps) * D1(n - 1) + ga * a * D1(n)
             + al * be * c(n - 1) - q * c(n))
        out = max(out, abs(v))
    return out


# ── DLMF §31.3(i)/§31.4(ii): the recurrence coefficients and the accessory-parameter
# continued fraction (Frameworks/Heun/Eigenfunctions.lean, Ch31BasicSolutions.lean) ──
def _heunP(al, be, j):
    """FLMF `heunP α β j` (DLMF 31.3.4): `P_j = (j−1+α)(j−1+β)`."""
    return (j - 1 + al) * (j - 1 + be)


def _heunQ(a, al, be, ga, de, j):
    """FLMF `heunQ a α β γ δ j` (DLMF 31.3.4):
    `Q_j = j((j−1+γ)(1+a) + aδ + ε)` with `ε = α+β+1−γ−δ` (31.2.3)."""
    return j * ((j - 1 + ga) * (1 + a) + a * de + (al + be + 1 - ga - de))


def _heunR(a, ga, j):
    """FLMF `heunR a γ j` (DLMF 31.3.4): `R_j = a(j+1)(j+γ)`."""
    return a * (j + 1) * (j + ga)


def _heun_normal_gauge(a, ga, de, ep, z):
    """FLMF `heunNormalGauge a γ δ ε z` (Frameworks/Heun/Ch31DifferentialEquations.lean):
    the gauge factor of the **DLMF 31.2.2** normal-form substitution

        w(z) = z^{−γ/2} (z−1)^{−δ/2} (z−a)^{−ε/2} W(z),

    each power on the PRINCIPAL branch, i.e. Mathlib `Complex.cpow` = `exp (log · · e)`
    with `log` the principal logarithm (`ph ∈ (−π, π]`).  mpmath's `**` on mpc operands
    is that same principal branch, and the extractor's own `bin ^` path evaluates the
    display's right-hand side by exactly the same operator — so both sides of 31.2.2 use
    one convention and a mis-transcribed exponent can only FAIL, never cancel.

    Zero bases (z = 0, 1, a) are NOT junk-patched here: mpmath raises, the display's RHS
    raises identically, and the sample drops honestly — patching only this side would make
    the two sides asymmetric and could fabricate a verdict."""
    return z ** (-ga / 2) * (z - 1) ** (-de / 2) * (z - a) ** (-ep / 2)


def _fuchsian_normal_gauge(a, ga, z):
    """FLMF `fuchsianNormalGauge a γ z` (Frameworks/Heun/Fuchsian.lean): the gauge factor
    of the **DLMF 31.14.3** normal-form substitution for the general Fuchsian equation,

        w(z) = (∏_j (z − a_j)^{−γ_j/2}) W(z),      j ranging over `Fin N`,

    with `a γ : Fin N → ℂ` the singularity/exponent vectors.  Both arrive as the sweep's
    `.q`-tagged Fin-vector callables (`_finvec_callable`), so the product range is read
    off the vector's OWN cardinality — never guessed.  Principal branch and zero-base
    conventions exactly as in `_heun_normal_gauge`; `N = 0` gives the empty product 1,
    which is Lean's `∏ j : Fin 0` too."""
    q = getattr(a, "q", None)
    if q is None:
        q = getattr(ga, "q", None)
    if q is None:
        raise ValueError("fuchsianNormalGauge: operands are not Fin-vector callables")
    out = mp.mpc(1)
    for j in range(int(q)):
        out *= (z - a(j)) ** (-(ga(j)) / 2)
    return out


def _fin_card(*vecs):
    """The common `Fin N` cardinality of the sweep's `.q`-tagged Fin-vector callables."""
    for v in vecs:
        q = getattr(v, "q", None)
        if q is not None:
            return int(q)
    raise ValueError("Fin-vector cardinality unavailable (operands are not .q-tagged)")


def _fuchsian_normal_q(a, ga, q, j):
    """FLMF `fuchsianNormalQ a γ q j` (Frameworks/Heun/Fuchsian.lean) — the accessory
    coefficient of the normal form of the general Fuchsian equation, **DLMF 31.14.5**:

        q̃_j = ½ Σ_{k=1, k≠j}^{N} γ_j γ_k/(a_j − a_k) − q_j.

    `a γ q : Fin N → ℂ` arrive as the sweep's `.q`-tagged Fin-vector callables, so the
    erase-sum range is read off the vector's OWN cardinality; `j` is the sampled `Fin N`
    index.  Anchored in `verify()` NOT by this formula but by the DEFINING ROLE of the
    pair (q̃, γ̃): under the 31.14.3 gauge w = φ·W the equation 31.14.1 becomes
    W″ = Σ_j(γ̃_j/(z−a_j)² + q̃_j/(z−a_j))W (31.14.4), with φ″/φ obtained by NUMERICAL
    differentiation of the independently anchored `_fuchsian_normal_gauge`."""
    N = _fin_card(a, ga, q)
    jj = int(mp.re(j))
    if not 0 <= jj < N:
        raise ValueError("fuchsianNormalQ: index outside Fin N")
    s = mp.mpc(0)
    for k in range(N):
        if k != jj:
            s += ga(jj) * ga(k) / (a(jj) - a(k))
    return s / 2 - q(jj)


def _fuchsian_normal_gamma(ga, j):
    """FLMF `fuchsianNormalGamma γ j` (Frameworks/Heun/Fuchsian.lean) — the exponent
    coefficient of the normal form, **DLMF 31.14.5**:  γ̃_j = (γ_j/2)(γ_j/2 − 1).
    Anchored jointly with `_fuchsian_normal_q` by the 31.14.4 normal-form identity (the
    double pole at a_j sees γ̃_j alone, the simple pole q̃_j)."""
    jj = int(mp.re(j))
    if not 0 <= jj < _fin_card(ga):
        raise ValueError("fuchsianNormalGamma: index outside Fin N")
    g = ga(jj)
    return g / 2 * (g / 2 - 1)


def _stieltjes_weight(ga, a, z):
    """FLMF `stieltjesWeight γ a z` (Frameworks/Heun/Stieltjes.lean) — the weight of the
    Stieltjes inner product, **DLMF 31.15.12**:

        ρ(z) = (∏_{j=1}^{N−1} ∏_{k=1}^{N} |z_j − a_k|^{γ_k−1}) (∏_{j<k}^{N−1} (z_k − z_j)).

    `γ a : Fin N → ℝ` and `z : Fin (N−1) → ℝ` arrive as `.q`-tagged Fin-vector callables,
    so BOTH ranges come from the vectors themselves (the outer index runs over z's own
    `Fin (N−1)`, the inner over a's `Fin N`) — never guessed from one another.  The powers
    are `Real.rpow` powers of the nonnegative bases |z_j − a_k| (Mathlib junks 0^c to 0 for
    c ≠ 0, which mpmath reproduces); the second factor is the SIGNED difference (z_k − z_j),
    not its modulus, exactly as displayed."""
    N, n = _fin_card(a, ga), _fin_card(z)
    out = mp.mpf(1)
    for j in range(n):
        for k in range(N):
            out *= abs(z(j) - a(k)) ** (ga(k) - 1)
    for j in range(n):
        for k in range(n):
            if j < k:
                out *= z(k) - z(j)
    return out


# ── hypothesis-CARRIER witness ladders (`CARRIER_PINS`) ───────────────────────
# A theorem quantified under a named Prop carrier (`h : FuchsRelation a γ q α β`) is FALSE
# at a freely sampled point — the carrier is exactly what pins the sampled binders — so the
# sweep must construct its samples INSIDE the hypothesis.  Each entry below transcribes the
# DLMF display the carrier carries and SOLVES it for the binders the display determines,
# leaving the rest to the ordinary grid:
#   'params'  the carrier's argument list, positionally (matched against the row's own
#             hypothesis arguments — the pin fires only on the exact carrier and arity);
#   'kinds'   the extractor binder base each argument must have (a mismatch ⇒ no pin);
#   'solves'  the positions the ladder computes;
#   'pin'     env-dict → {name: value} for those positions, raising when the sample is
#             outside the carrier's own domain (the point then drops honestly).
# Anchored in verify() against an INDEPENDENT route to the same display, never by name.
def _pin_half_odd_integer_exponents(m, al):
    """DLMF 31.8.1 — the half-odd-integer exponent regime of §31.8:

        β − α = m₀ + ½,  γ = −m₁ + ½,  δ = −m₂ + ½,  ε = −m₃ + ½,   m₀..m₃ ∈ ℕ.

    Given the sampled `m : Fin 4 → ℕ` (a pointwise callable) and a free α, returns the
    (β, γ, δ, ε) the display determines.  Equivalently — the anchor used in verify() —
    the four Heun exponent DIFFERENCES are the half-odd integers m_k + ½: at ∞ it is
    β − α, and at z = 0, 1, a it is 1 − γ, 1 − δ, 1 − ε (DLMF 31.2.1's Riemann scheme)."""
    m0, m1, m2, m3 = (mp.mpf(int(mp.re(m(i)))) for i in range(4))
    if min(m0, m1, m2, m3) < 0:
        raise ValueError("HeunHalfOddIntegerExponents: m must be nonnegative")
    half = mp.mpf(1) / 2
    return (al + m0 + half, -m1 + half, -m2 + half, -m3 + half)


def _pin_fuchs_relation(a, ga, q):
    """DLMF 31.14.2 — the exponents {α, β} at ∞ of the general Fuchsian equation 31.14.1:

        α + β + 1 = Σ_j γ_j,      αβ = Σ_j a_j q_j.

    Solved as the two roots of ρ² − (Σγ − 1)ρ + Σ a q = 0 (the branch choice is
    immaterial: the carrier is symmetric in α, β).  Anchored in verify() by the
    INDEPENDENT indicial route — for the Heun data a = (0,1,a), γ = (γ,δ,ε) with the
    q_j the partial-fraction residues of Heun's (αβz − q)/(z(z−1)(z−a)) (DLMF 31.2.1),
    the ladder must return exactly Heun's own {α, β}."""
    N = _fin_card(a, ga, q)
    s1 = mp.fsum([ga(j) for j in range(N)])
    s2 = mp.fsum([a(j) * q(j) for j in range(N)])
    b = s1 - 1                                   # α + β
    disc = mp.sqrt(b * b - 4 * s2)
    return ((b + disc) / 2, (b - disc) / 2)


CARRIER_PINS = {
    # `h : HeunHalfOddIntegerExponents m α β γ δ ε` (Frameworks/Heun/Quadratures.lean)
    "HeunHalfOddIntegerExponents": {
        "params": ["m", "α", "β", "γ", "δ", "ε"],
        "kinds": ["absfnN", "C", "C", "C", "C", "C"],
        "solves": [2, 3, 4, 5],
        "pin": lambda vals: _pin_half_odd_integer_exponents(vals[0], vals[1]),
        "dlmf": "31.8.1",
    },
    # `h : FuchsRelation a γ q α β` (Frameworks/Heun/Fuchsian.lean)
    "FuchsRelation": {
        "params": ["a", "γ", "q", "α", "β"],
        "kinds": ["finvecC", "finvecC", "finvecC", "C", "C"],
        "solves": [3, 4],
        "pin": lambda vals: _pin_fuchs_relation(vals[0], vals[1], vals[2]),
        "dlmf": "31.14.2",
        # the unconstrained-vector construction gives a = γ = q, under which the two
        # relations of the display are indistinguishable; the sweep therefore rebuilds
        # the three vectors DISTINCTLY here (`vectors`), keeping them generic complex
        # tuples with distinct entries (so a_j ≠ a_k) and no other property.
        "vectors": lambda n: (
            [mp.mpc(mp.mpf("-0.6") + mp.mpf(i) * mp.mpf("0.9"),
                    mp.mpf("0.4") - mp.mpf(i) * mp.mpf("0.3")) for i in range(n)],
            [mp.mpc(mp.mpf("0.7") + mp.mpf(i) * mp.mpf("0.4"),
                    mp.mpf("-0.2") + mp.mpf(i) * mp.mpf("0.5")) for i in range(n)],
            [mp.mpc(mp.mpf("0.5") - mp.mpf(i) * mp.mpf("0.7"),
                    mp.mpf("0.1") + mp.mpf(i) * mp.mpf("0.6")) for i in range(n)]),
    },
}


def heun_eigen_cf(a, q, al, be, ga, de):
    """The Lean `heunEigenCF a q α β γ δ` (Ch31BasicSolutions.lean) as a
    `(head, pair)` pair for the generic convergent recursion: head `h = 0`, and the
    stream entry `n` is `(aₙ, bₙ)` with

        a₀ = R₀·P₁ = aγ·P₁,   aₙ = −(Rₙ·P_{n+1})  (n ≥ 1),   bₙ = Q_{n+1} + q,

    i.e. the fraction DISPLAYED in DLMF 31.4.2,
    `aγP₁/(Q₁+q − R₁P₂/(Q₂+q − R₂P₃/(Q₃+q − ⋯)))`.  Transcribed field-for-field from
    the Lean `def`; the transcription is anchored in verify() BOTH against the DLMF
    31.3.4 closed forms entry-by-entry AND, decorrelated from the fraction entirely, by
    convergence to the independently computed eigenvalues of `heun_eigen_witnesses`
    (with sign-flipped and index-shifted rivals rejected there)."""
    def pair(n):
        an = (_heunR(a, ga, 0) * _heunP(al, be, 1) if n == 0
              else -(_heunR(a, ga, n) * _heunP(al, be, n + 1)))
        return an, _heunQ(a, al, be, ga, de, n + 1) + q
    return mp.mpf(0), pair


def cf_convergent_limit(h, pair, maxn=400, tol=mp.mpf("1e-25")):
    """Limit of the convergents of a `GenContFract` given as `h` + the stream
    `n ↦ (aₙ, bₙ)`, by Mathlib's own `convs` continuant recursion
    (`A₋₁ = 1, A₀ = h, B₋₁ = 0, B₀ = 1`; `A_{k+1} = b_k·A_k + a_k·A_{k−1}`, likewise `B`).

    Returns `(limit, k, dmin)` where `k` is the index at which the convergents became
    Cauchy to `tol` (relative) and `dmin` is the smallest continuant denominator seen
    RELATIVE to the running `max(|A|,|B|)` scale — a scale-invariant proxy for DLMF's
    (and the Lean statements') nonvanishing-denominator proviso `dens n ≠ 0`.
    Returns `(None, k, reason)` when a denominator vanishes exactly or the convergents
    do not settle within `maxn` — never a fabricated limit."""
    Am1, A0, Bm1, B0 = mp.mpf(1), h, mp.mpf(0), mp.mpf(1)
    prev, dmin = None, None
    for k in range(maxn):
        ak, bk = pair(k)
        A1, B1 = bk * A0 + ak * Am1, bk * B0 + ak * Bm1
        Am1, A0, Bm1, B0 = A0, A1, B0, B1
        if B0 == 0:
            return None, k, "dens=0"
        sc = max(abs(A0), abs(B0))
        if sc == 0:
            return None, k, "degenerate continuants"
        Am1, A0, Bm1, B0 = Am1 / sc, A0 / sc, Bm1 / sc, B0 / sc
        dmin = abs(B0) if dmin is None else min(dmin, abs(B0))
        conv = A0 / B0
        if prev is not None and k > 5 and \
                abs(conv - prev) / max(mp.mpf(1), abs(conv)) < tol:
            return conv, k, dmin
        prev = conv
    return None, maxn, "unsettled"


_HEUN_VD_MAXTERMS = 900


def _heun_val_deriv(a, q, al, be, ga, de, z):
    """`(Hℓ(z), Hℓ′(z))` for the local Heun function of DLMF 31.3.1, summed from the
    SAME anchored coefficient recurrence as `_heun_fn` (`_heun_coeff_list`).  RAISES
    when `z` is outside the Maclaurin disc `|z| < min(1,|a|)` or the truncation has not
    settled to working precision within the term cap — never a fabricated value."""
    rad = min(mp.mpf(1), abs(a))
    if not abs(z) < rad:
        raise ValueError("heun_val_deriv: |z| outside the Maclaurin disc min(1,|a|)")
    cs = _heun_coeff_list(a, q, al, be, ga, de, _HEUN_VD_MAXTERMS)
    tol = mp.mpf(2) ** (-mp.mp.prec + 12)
    val, der, zp, tmax, run = mp.mpf(0), mp.mpf(0), mp.mpf(1), mp.mpf(0), 0
    for k, c in enumerate(cs):
        t = c * zp
        val += t
        if k >= 1:
            der += k * c * zp / z
        zp *= z
        tmax = max(tmax, abs(t))
        run = run + 1 if abs(t) <= tol * max(mp.mpf(1), tmax, abs(val)) else 0
        if run >= 6:
            return val, der
    raise ValueError("heun_val_deriv: Maclaurin series did not settle within the term cap")


def _heun_at_one(a, q, al, be, ga, de, z):
    """`(u₁(z), u₁′(z))` for the solution of Heun's equation ANALYTIC at `z = 1`:
    `u₁(z) = Hℓ(1−a, αβ−q; α, β, δ, γ; 1−z)` (DLMF 31.3.5, the `z ↦ 1−z` map that
    exchanges the singularities `0 ↔ 1` and sends `a ↦ 1−a`, `γ ↔ δ`, `q ↦ αβ−q`).
    verify() validates this map by substituting `u₁` into the ORIGINAL Heun ODE."""
    v, d = _heun_val_deriv(1 - a, al * be - q, al, be, de, ga, 1 - z)
    return v, -d


def _heun_analytic_at_one_wronskian(a, q, al, be, ga, de, z0):
    """`W(q) = Hℓ(z₀)·u₁′(z₀) − Hℓ′(z₀)·u₁(z₀)` — the Wronskian of the local Heun
    function at `0` against the solution analytic at `1`.  Since `Hℓ = A·u₁ + B·u₂`
    with `u₂` the second (exponent `1−δ`) branch at `z = 1`, `W = B·W(u₂,u₁)`, so
    `W(q) = 0` ⟺ `B = 0` ⟺ `Hℓ` continues analytically to `z = 1` — i.e. exactly
    DLMF 31.4.1's eigenvalue condition `IsHeunEigenvalue`.  No continued fraction
    enters this quantity."""
    hv, hd = _heun_val_deriv(a, q, al, be, ga, de, z0)
    uv, ud = _heun_at_one(a, q, al, be, ga, de, z0)
    return hv * ud - hd * uv


# Parameter families for the eigenvalue witnesses: `a` real with |a| > 1 and a ≠ 1
# (DLMF §31.1's own domain, and the theorem's ‖a‖ ≥ 1), γ and δ non-integral (so
# γ ≠ 0,−1,−2,… and the two exponents 0, 1−δ at z = 1 stay distinct), α NOT a
# nonpositive integer — the series does NOT terminate, so the convergence of the
# 31.4.2 fraction is genuinely at stake (not a finite truncation).
_HEUN_EIGEN_FAMILIES = (
    ("2", "0.3", "0.5", "0.7", "1.3"),
    ("3", "0.4", "-0.6", "1.1", "0.35"),
    ("1.7", "0.25", "0.8", "0.45", "1.15"),
)
_HEUN_EIGEN_CACHE = {}


def heun_eigen_witnesses(max_per_family=2):
    """Parameter tuples `(a, q, α, β, γ, δ)` at which `IsHeunEigenvalue a q α β γ δ`
    (DLMF 31.4.1: `Hℓ(a,q;α,β,γ,δ;·)` is analytic at `z = 1` as well as at `z = 0`)
    holds, computed INDEPENDENTLY of the 31.4.2 continued fraction: `q` is a root of
    the Wronskian `W(q) = 0` of `Hℓ` against the `z = 1` analytic solution
    (`_heun_analytic_at_one_wronskian`), located by sign-change bisection.

    At such a `q`, `Hℓ` is proportional to `u₁` near `z = 1`, hence extends
    analytically across `[0,1]` to an open connected `U ⊇ ball(0, min(1,‖a‖)) ∪ D(1,r)`
    with `a ∉ U` (each family has `a` real, `|a| > 1`), and solves Heun's equation on
    `U` by analytic continuation — the witness `w` that `IsHeunEigenvalue` requires.
    Every root returned is CERTIFIED here: `|W|` small at the root, and the ratio
    `Hℓ/u₁` equal at two separate interior points (proportionality — a scalar-multiple
    check that a mere small `|W|` at one point could not establish).  Roots that fail
    either gate are dropped, never returned as trusted witnesses."""
    key = (mp.mp.prec, max_per_family)
    if key in _HEUN_EIGEN_CACHE:
        return _HEUN_EIGEN_CACHE[key]
    out = []
    for fam in _HEUN_EIGEN_FAMILIES:
        a, al, be, ga, de = (mp.mpf(t) for t in fam)
        W = lambda qq: _heun_analytic_at_one_wronskian(a, qq, al, be, ga, de, mp.mpf("0.5"))
        grid = [mp.mpf(t) / 2 for t in range(-12, 13)]
        vals = []
        for x in grid:
            try:
                vals.append((x, W(x)))
            except Exception:
                vals.append((x, None))
        got = 0
        for (x0, v0), (x1, v1) in zip(vals, vals[1:]):
            if got >= max_per_family:
                break
            if v0 is None or v1 is None or v0 == 0 or mp.sign(v0) == mp.sign(v1):
                continue
            try:
                r = mp.findroot(W, (x0, x1), solver='bisect', tol=mp.mpf("1e-40"))
            except Exception:
                continue
            try:
                # certify: |W(r)| ≈ 0 against the scale of |W| on the bracket, and
                # Hℓ ∝ u₁ (equal ratios at two interior points) — genuine analyticity
                # at z = 1, not an accidental small Wronskian.
                scale = max(abs(v0), abs(v1), mp.mpf(1))
                if abs(W(r)) > mp.mpf("1e-18") * scale:
                    continue
                rats = []
                for z0 in (mp.mpf("0.35"), mp.mpf("0.65")):
                    hv, _ = _heun_val_deriv(a, r, al, be, ga, de, z0)
                    uv, _ = _heun_at_one(a, r, al, be, ga, de, z0)
                    if abs(uv) < mp.mpf("1e-8"):
                        raise ValueError("degenerate u₁ sample")
                    rats.append(hv / uv)
                if abs(rats[0] - rats[1]) > mp.mpf("1e-18") * max(mp.mpf(1), abs(rats[0])):
                    continue
            except Exception:
                continue
            out.append((a, r, al, be, ga, de))
            got += 1
    _HEUN_EIGEN_CACHE[key] = out
    return out


# Named `GenContFract` objects that FLMF statements apply `.convs` to, together with
# the hypothesis-carrier a Tier-1 sample ladder must satisfy before it may witness such
# a row, and the CERTIFIED witness generator for that carrier.  Consumed by
# fidelity_extract.handle_named_cf_tendsto; a CF absent from this table keeps its honest
# skip (no free-sampled verdict is ever issued for a fraction whose stated hypothesis
# the sampler cannot certify).
CF_REGISTRY = {
    "heunEigenCF": {
        "arity": 6,                              # a q α β γ δ
        "build": heun_eigen_cf,
        "requires": "IsHeunEigenvalue",          # DLMF 31.4.1 carrier (same 6 arguments)
        "witnesses": heun_eigen_witnesses,
    },
}


def _whittakerM(kap, mu, z):
    """FLMF `whittakerM κ μ z` (Whittaker.lean, DLMF 13.14.2): the DEFINING
    normalization e^{−z/2}·z^{μ+1/2}·M(½+μ−κ; 1+2μ; z), composed from the anchored
    ₁F₁ binding with the sweep's principal-branch power (= the Lean rpow on z > 0;
    both sides of the rfl rows share the z < 0 branch convention). Anchored in
    verify() against the INDEPENDENT mp.whitm on the clean domain — the κ-sign and
    argument-order rivals are rejected there."""
    return mp.e ** (-z / 2) * mp.power(z, mu + mp.mpf(1) / 2) \
        * _kummerM(mp.mpf(1) / 2 + mu - kap, 1 + 2 * mu, z)


def _whittakerW(kap, mu, z):
    """FLMF `whittakerW κ μ z` (DLMF 13.14.3): e^{−z/2}·z^{μ+1/2}·U(½+μ−κ; 1+2μ; z),
    composed from the anchored `tricomiU` binding — inheriting its junk-0 outside
    a > 0 ∧ z > 0 exactly as the Lean def does. Anchored against mp.whitw."""
    return mp.e ** (-z / 2) * mp.power(z, mu + mp.mpf(1) / 2) \
        * _tricomiU(mp.mpf(1) / 2 + mu - kap, 1 + 2 * mu, z)


def _tricomi_integrand(a, b, z, t):
    """FLMF `tricomiIntegrand a b z t` (Tricomi.lean, DLMF 13.4.4 integrand):
    e^{−zt}·t^{a−1}·(1+t)^{b−a−1} (evaluated at quadrature nodes t > 0)."""
    return mp.e ** (-z * t) * mp.power(t, a - 1) * mp.power(1 + t, b - a - 1)


def _appellF1(a, b1, b2, c, x, y):
    """FLMF `appellF1 a b₁ b₂ c x y` (Appell.lean, DLMF 16.13.1) = mpmath appellf1,
    same parameter order. GUARDED to the open bidisc ‖x‖<1 ∧ ‖y‖<1 — the Lean def is
    the double SERIES with junk 0 outside (mp.appellf1 would analytically continue
    there, a different value); off-disc points raise → honest drop."""
    if abs(x) >= 1 or abs(y) >= 1:
        raise ValueError("appellF1: outside the open bidisc (Lean junk-0 regime)")
    return mp.appellf1(a, b1, b2, c, x, y)


def _appellF2(a, b1, b2, c1, c2, x, y):
    """FLMF `appellF2 a b₁ b₂ c₁ c₂ x y` (AppellF2.lean, DLMF 16.13.2):
    Σ_{m,n} (a)_{m+n}(b₁)_m(b₂)_n / ((c₁)_m(c₂)_n m! n!) xᵐyⁿ — no mpmath builtin;
    truncated double sum (m+n ≤ 120, convergent for |x|+|y| < 1; guarded to
    |x|+|y| ≤ 0.95 so truncation ≪ tolerance, outside raises → honest drop)."""
    if abs(x) + abs(y) > mp.mpf("0.95"):
        raise ValueError("appellF2: outside the truncation-safe |x|+|y| region")
    # adaptive truncation to BELOW the working precision (the sweep gates at 1e-18
    # RELATIVE and retries FAILs at doubled dps, so a fixed row cap would surface as
    # a fake truncation-FAIL on the |x| ≈ 0.8 disc samples); a non-converged sum
    # RAISES (honest point drop), never returns a truncated value.
    eps = mp.mpf(10) ** (-(mp.mp.dps + 8))
    s = mp.mpf(0)
    converged = False
    for m in range(4001):
        rm = mp.rf(a, m) * mp.rf(b1, m) / (mp.rf(c1, m) * mp.factorial(m)) * x ** m
        row = mp.mpf(0)
        if rm != 0:
            for n in range(4001):
                t = (rm * mp.rf(a + m, n) * mp.rf(b2, n)
                     / (mp.rf(c2, n) * mp.factorial(n)) * y ** n)
                row += t
                if n > 8 and abs(t) < eps * max(1, abs(s + row)):
                    break
        s += row
        if m > 8 and abs(rm) < eps * max(1, abs(s)) and abs(row) < eps * max(1, abs(s)):
            converged = True
            break
    if not converged:
        raise ValueError("appellF2: series did not converge within the term cap")
    return s


def _qexp(z, q):
    """FLMF `qExp z q = Σ_n zⁿ/(q;q)ₙ` (QExponential.lean, DLMF 17.2 e_q) — the
    DEFINING series with an incremental (q;q)ₙ product, truncated when the term
    drops below 1e-32 (hard cap 800 terms); guarded to |q| < 1 ∧ |z| < 1 (the
    stated convergence regime; outside raises → honest drop)."""
    if abs(q) >= 1 or abs(z) >= 1:
        raise ValueError("qExp: outside |q|<1, |z|<1")
    s, zn, den = mp.mpf(0), mp.mpmathify(1), mp.mpmathify(1)
    for n in range(801):
        t = zn / den
        s += t
        if n > 20 and abs(t) < mp.mpf("1e-32") * max(1, abs(s)):
            break
        zn *= z
        den *= 1 - q ** (n + 1)
    return s


def _qpochhammer_inf(a, q):
    """FLMF `qPochhammerInf a q = ∏'_k (1 − a qᵏ)` (QBinomialTheorem.lean) =
    mp.qp(a, q); guarded to |q| < 1 (divergent/junk-tprod regime otherwise)."""
    if abs(q) >= 1:
        raise ValueError("qPochhammerInf: |q| ≥ 1")
    return mp.qp(a, q)


def _qexpE(z, q):
    """FLMF `qExpE z q = qPochhammerInf (−z) q` (DLMF 17.2 E_q = (−z;q)_∞)."""
    return _qpochhammer_inf(-z, q)


def _qhyper(r, s, a, b, q, z):
    """FLMF `qHyper r s a b q z = Σ_n qHyperTerm` (QHypergeometric.lean:42, DLMF 17.4.1) —
    the basic hypergeometric series ᵣφₛ(a;b;q,z). The term (QHypergeometric.lean:37) is
      [∏_i (aᵢ;q)_n] / ([∏_j (bⱼ;q)_n]·(q;q)_n) · ((−1)ⁿ q^{C(n,2)})^{s+1−r} · zⁿ,
    where (x;q)_n = mp.qp(x,q,n) and the exponent (s+1−r) uses Lean's ℕ-TRUNCATED
    subtraction (0 when r > s+1) — mirrored exactly. Reached via the extractor's `qHyper`
    leaf-match branch, which threads the `![…]` parameter vectors as Python lists a, b
    (lengths r, s). Summed with a hard term cap + a consecutive-settle guard (|q|<1,|z|<1 ⇒
    geometric-type convergence); an unsettled tail RAISES (honest drop, never a junk value).
    Anchored in verify() against the q-binomial theorem ₁φ₀(a;;q,z)=(az;q)_∞/(z;q)_∞ and the
    Euler identity ₀φ₀(;;q,z)=(z;q)_∞ (the latter exercises the s+1−r=1 exponent; a rival that
    drops the (−1)ⁿq^{C(n,2)} factor gives 1/(z;q)_∞ instead — rejected)."""
    r = _nat(r, "qHyper r")
    s = _nat(s, "qHyper s")
    a = list(a)
    b = list(b)
    if len(a) != r or len(b) != s:
        raise ValueError(f"qHyper: parameter-vector lengths {len(a)},{len(b)} ≠ (r,s)=({r},{s})")
    exp = s + 1 - r if s + 1 >= r else 0        # ℕ-truncated (s+1−r)
    total = mp.mpf(0)
    settled = 0
    tol = mp.mpf(10) ** (-(mp.mp.dps + 5))
    for n in range(4000):
        num = mp.mpf(1)
        for ai in a:
            num *= mp.qp(ai, q, n)
        den = mp.qp(q, q, n)
        for bj in b:
            den *= mp.qp(bj, q, n)
        binom2 = n * (n - 1) // 2                # Nat.choose n 2 (0 for n<2)
        term = num / den * ((-1) ** n * q ** binom2) ** exp * z ** n
        total += term
        if abs(term) < tol * (abs(total) + 1):
            settled += 1
            if settled >= 4:
                return total
        else:
            settled = 0
    raise ValueError("qHyper: series did not settle within the 4000-term cap")


def _laplace_transform(f, s):
    """FLMF `laplaceTransform f s = ∫_{(0,∞)} e^{−st} f(t) dt` (Methods/
    LaplaceTransform.lean, DLMF 1.14.17). f arrives as a CALLABLE (from a partial
    application like `fC b` below). Quadrature truncated at T = 60/Re s (tail
    ≤ sup|f|·e^{−60}/Re s ≈ 1e-26 for the bounded-f rows); Re s ≤ 0.05 raises —
    outside the convergence half-plane the Lean value is the junk 0 of a
    non-integrable Bochner integrand, which quadrature cannot witness."""
    if not callable(f):
        raise ValueError("laplaceTransform: operand is not a function")
    sr = mp.re(s)
    if sr <= mp.mpf("0.05"):
        raise ValueError("laplaceTransform: outside the sampled convergence half-plane")
    T = mp.mpf(60) / sr
    return mp.quad(lambda t: mp.e ** (-s * t) * f(t), [0, 1, T])


def _fC(b):
    """FLMF `fC b = fun t => (erf (Real.sqrt (b·t)) : ℂ)` (Ch7LaplaceBridge.lean) —
    returns the callable t ↦ erf(√(bt)) with the Mathlib junk √(x<0) = 0 (so
    fC b t = erf 0 = 0 there), for the higher-order `laplaceTransform` head."""
    return lambda t: mp.erf(_rsqrt(b * t))


def _alg_coeff(al, n):
    """FLMF `algCoeff α n = (∏_{k<n} (α+k))/n!` (Methods/Darboux.lean) — the RISING-
    factorial Darboux scale (α)ₙ/n! = [zⁿ](1−z)^{−α}. Anchored below at α = −1/2
    against the exact Catalan identity (DLMF 26.5.2) and a falling-factorial rival."""
    n = _nat(n, "algCoeff")
    return mp.rf(al, n) / mp.factorial(n)


# DLMF 7.13 zero-asymptotic parameters (ComplexZeros.lean) — closed-form defs with the
# Mathlib junk conventions √(x<0) = 0 and log 0 = 0 mirrored via _rsqrt/_rlog (so the
# n = 0 grid point matches the Lean value exactly). Anchored in verify() by the DEFINING
# property: the DLMF 7.13.1/.3/.5 approximants built from (λ, μ)/(λ, α) land near an
# actual zero of erf/erfc/C/S (|f| small), while the rival conventions (n+1/8 sign,
# un-doubled erfc μ, √(4n+1) Fresnel λ) miss by O(1).
def _erf_zero_lambda(n):
    return _rsqrt((_nat(n, "erfZeroLambda") - mp.mpf(1) / 8) * mp.pi)


def _erf_zero_mu(n):
    return _rlog(_erf_zero_lambda(n) * mp.sqrt(2 * mp.pi))


def _erfc_zero_mu(n):
    return _rlog(2 * _erf_zero_lambda(n) * mp.sqrt(2 * mp.pi))


def _fresnelC_zero_lambda(n):
    return _rsqrt(4 * mp.mpf(_nat(n, "fresnelCZeroLambda")) - 1)


def _fresnelC_zero_alpha(n):
    return (2 / mp.pi) * _rlog(mp.pi * _fresnelC_zero_lambda(n))


def _fresnelS_zero_lambda(n):
    return 2 * _rsqrt(mp.mpf(_nat(n, "fresnelSZeroLambda")))


def _fresnelS_zero_alpha(n):
    return (2 / mp.pi) * _rlog(mp.pi * _fresnelS_zero_lambda(n))


# ── DLMF §15.7 Gauss continued-fraction coefficients (Ch15ContinuedFractions.lean) ──
# The private abbrevs gaussTCoeff/…/gaussYCoeff ARE their DLMF closed forms; binding each
# to that closed form lets the coefficient-identity rows 15.7.2/4/6 (conjunctions of
# `coeff … = <closed form>`) evaluate instead of skipping `unbound:<coeff>`. Anchored in
# verify() DECORRELATED from these forms: the generalized continued fraction built from
# t/u (resp. v/w, x/y) — with the exact GenContFract h and (aₙ,bₙ) stream of the Lean
# statements — converges to the DLMF-stated ratio of Olver F = ₂F₁/Γ(c), computed via
# mpmath's independent hyp2f1. A wrong sign, index shift, or parity swap breaks that limit.
def _gauss_ucoeff(a, b, c, n):
    # DLMF 15.7.2: u_{2m} = (b+m)(c−a+m), u_{2m+1} = (a+m)(c−b+m) — the abbrev's Even split.
    m = int(mp.nint(mp.re(n)))
    if m % 2 == 0:
        h = m // 2
        return (b + h) * (c - a + h)
    h = (m - 1) // 2
    return (a + h) * (c - b + h)


REGISTRY.update({
    "gaussTCoeff": ("fn", lambda c, n: c + n),                             # DLMF 15.7.2 tₙ = c+n
    "gaussUCoeff": ("fn", _gauss_ucoeff),                                  # DLMF 15.7.2 uₙ
    "gaussVCoeff": ("fn", lambda a, b, c, z, n: c + n + (b - a + n + 1) * z),   # 15.7.4 vₙ
    "gaussWCoeff": ("fn", lambda a, b, c, z, n: (b + n) * (c - a + n) * z),     # 15.7.4 wₙ
    "gaussXCoeff": ("fn", lambda a, b, c, z, n: c + n - (a + b + 2 * n + 1) * z),  # 15.7.6 xₙ
    "gaussYCoeff": ("fn", lambda a, b, z, n: (a + n) * (b + n) * z * (1 - z)),     # 15.7.6 yₙ
    # Appell double series (DLMF 16.13.1 / 16.13.2), Lean junk-0 off the bidisc → guarded
    "appellF1": ("fn", _appellF1),
    "appellF2": ("fn", _appellF2),
    # Frobenius instance for the Gauss equation (FrobeniusInstance.lean, DLMF 15.10):
    # gaussP = 1 − X, gaussQ = c − (a+b+1)X, gaussR = −ab·X as _FPS objects; frobCoeff
    # is the DLMF §2.7(i) recurrence over them (anchored against the INDEPENDENT
    # ordinaryHypergeometricCoefficient at both indicial roots, with a generic-ρ
    # discriminator).
    "gaussP": ("const", _fps_of_list([1, -1])),
    "gaussQ": ("fn", lambda a, b, c: _fps_of_list([c, -(a + b + 1)])),
    "gaussR": ("fn", lambda a, b: _fps_of_list([0, -(a * b)])),
    "frobCoeff": ("fn", _frob_coeff),
    # Whittaker normalizations (DLMF 13.14.2/13.14.3) + the Tricomi integrand
    "whittakerM": ("fn", _whittakerM),
    "whittakerW": ("fn", _whittakerW),
    "tricomiIntegrand": ("fn", _tricomi_integrand),
    # Mathlib `NormedSpace.exp` — the exponential (the ℂ instance in FLMF statements)
    "NormedSpace.exp": ("fn", lambda a: mp.e ** a),
    # §31.2(iii)/(iv) changes of variable carrying Heun's equation into its
    # trigonometric and Jacobi-elliptic forms.  Each is anchored by the DLMF
    # DEFINING formula of its own display, never by name:
    #   heunTrigVariable θ       = sin²θ            (DLMF 31.2.5)
    #   heunJacobiSingularity k  = k⁻²              (DLMF 31.2.7, first half)
    #   heunJacobiVariable ζ k   = sn²(ζ,k)         (DLMF 31.2.7, second half)
    # `snk` is the already-anchored modulus-parameterized Jacobi sn.
    "heunTrigVariable": ("fn", lambda th: mp.sin(th) ** 2),
    "FLMF.Heun.heunTrigVariable": ("fn", lambda th: mp.sin(th) ** 2),
    "heunJacobiSingularity": ("fn", lambda k: k ** (-2)),
    "FLMF.Heun.heunJacobiSingularity": ("fn", lambda k: k ** (-2)),
    "heunJacobiVariable": ("fn", lambda ze, k: _snk(ze, k) ** 2),
    "FLMF.Heun.heunJacobiVariable": ("fn", lambda ze, k: _snk(ze, k) ** 2),
    # Heun local solution (Frameworks/Heun.lean, DLMF 31.2.1/31.3)
    "heunB": ("fn", _heunB),
    "heunCoeff": ("fn", _heun_coeff),
    "heunFn": ("fn", _heun_fn),
    # DLMF 31.3.4 recurrence coefficients (Eigenfunctions.lean) — the entries of both
    # the 31.5.1 tridiagonal matrix and the 31.4.2 continued fraction
    "heunP": ("fn", _heunP),
    "heunQ": ("fn", _heunQ),
    "heunR": ("fn", _heunR),
    # normal-form gauge factors of the substitution displays DLMF 31.2.2 / 31.14.3
    # (Ch31DifferentialEquations.lean, Fuchsian.lean) — principal-branch cpow products
    "heunNormalGauge": ("fn", _heun_normal_gauge),
    "fuchsianNormalGauge": ("fn", _fuchsian_normal_gauge),
    # normal-form coefficients of the general Fuchsian equation (DLMF 31.14.5) and the
    # Stieltjes inner-product weight (DLMF 31.15.12) — Fin-vector-carried definitions
    "fuchsianNormalQ": ("fn", _fuchsian_normal_q),
    "fuchsianNormalGamma": ("fn", _fuchsian_normal_gamma),
    "stieltjesWeight": ("fn", _stieltjes_weight),
    # DLMF §31.8 Hermite–Darboux quadrature data (Frameworks/Heun/Quadratures.lean):
    # the 31.8.3 genus formula and DLMF's two explicit members Ψ_{1,2} (31.8.4) and
    # Ψ_{1,−1} (31.8.5) with their spectral curves ν².  Each is anchored in verify()
    # by the §31.8 DEFINING data (symmetric-square equation + Wronskian first integral,
    # and for the genus by DLMF's own two worked 𝐦), never by name.
    "heunQuadratureGenus": ("fn", _heun_quadrature_genus),
    "heunPsi_1_2": ("fn", _heun_psi_1_2),
    "heunNuSq_1_2": ("fn", _heun_nusq_1_2),
    "heunPsi_1_neg1": ("fn", _heun_psi_1_neg1),
    "heunNuSq_1_neg1": ("fn", _heun_nusq_1_neg1),
    # DLMF 31.9.4 coefficients f₀,f₁ and the 31.9.3 normalization θ_m (Ch31Orthogonality)
    "heunF0": ("fn", _heunF0),
    "heunF1": ("fn", _heunF1),
    "heunTheta": ("fn", _heunTheta),
    "heunSeries": ("fn", _heun_series),
    "heunOp": ("fn", _heun_op),
    "constantCoeff": ("fn", _constant_coeff),
    # Laplace transform (DLMF 1.14.17) + the Ch7 bridge integrand fC
    "laplaceTransform": ("fn", _laplace_transform),
    "fC": ("fn", _fC),
    # physHermite (Hermite/Normalization.lean): the Lean def is (hermite n).comp (2X),
    # i.e. Heₙ(2x) — NOT the true physicists' Hₙ(x) (He₂(2x) = 4x²−1 vs H₂ = 4x²−2)!
    # Bound through the anchored probabilists' _hermite_prob at 2x; the verify()
    # anchor rejects the mp.hermite (genuine-physicists') rival.
    "physHermite": ("poly", lambda n, x: _hermite_prob(_nat(n, "physHermite"), 2 * x)),
    # the GENUINE physicists' Hₙ (new def, 2026-08-14): recurrence-defined true Hₙ
    "physicistsHermite":
        ("poly", lambda n, x: _phys_hermite(_nat(n, "physicistsHermite"), x)),
    # Darboux algebraic-singularity coefficient scale (Methods/Darboux.lean)
    "algCoeff": ("fn", _alg_coeff),
    # q-exponentials + the infinite q-Pochhammer (DLMF 17.2)
    "qPochhammerInf": ("fn", _qpochhammer_inf),
    "qExp": ("fn", _qexp),
    "qExpE": ("fn", _qexpE),
    # basic hypergeometric series ᵣφₛ(a;b;q,z) (DLMF 17.4.1) — consumed by the extractor's
    # `qHyper` leaf-match branch, which passes the ![…] vectors as the a,b list args:
    "qHyper": ("fn", _qhyper),
    # Complex cotangent — same principal function as mp.cot (cos/sin quotient; the
    # Real.cot binding above is the real restriction)
    "Complex.cot": ("fn", mp.cot),
    # DLMF 7.13 zero-asymptotic parameter families (ComplexZeros.lean)
    "erfZeroLambda": ("fn", _erf_zero_lambda),
    "erfZeroMu": ("fn", _erf_zero_mu),
    "erfcZeroLambda": ("fn", _erf_zero_lambda),   # same closed form as the erf λ (7.13.4)
    "erfcZeroMu": ("fn", _erfc_zero_mu),
    "fresnelCZeroLambda": ("fn", _fresnelC_zero_lambda),
    "fresnelCZeroAlpha": ("fn", _fresnelC_zero_alpha),
    "fresnelSZeroLambda": ("fn", _fresnelS_zero_lambda),
    "fresnelSZeroAlpha": ("fn", _fresnelS_zero_alpha),
})
# NOT bound (honest structural triage, extractor lane):
#  * `qHyper r s ![a] ![b] q z` (DLMF 17.4.1) — its `![…]` parameter vectors parse to
#    ('vec', …) nodes, which only leaf-matched extractor branches (`pFq`, `meijerG`)
#    can consume via _veclist; a registry 'fn' head cannot receive them.
#  * `kummerSeries 𝔸 a b n = 0` (13.2.7) — a FormalMultilinearSeries-level equality
#    whose DISJUNCTIVE hypothesis (k = −a ∨ k = −b) the extractor drops; sampling
#    a, b freely would fabricate a FAIL of a true theorem.
#  * file-local single-letter heads `L`/`R` (Bernoulli/Duplication.lean `dupl`) and
#    `f` (QBinomialTheorem.lean) — a global registry binding of these names would be
#    unsound across files (needs local-def unfolding on the extractor side).


# ── A4 final-batch cluster (Agent A4, 2026-07-21) ────────────────────────────────────
# Heads: Nat.primeCounting (π(n), DLMF §27.2 — the expint_6_16_5 li−π bound), the
# QUALIFIED real complementary modulus FLMF.JacobiElliptic.complementaryModulus
# (√(1−k²), DLMF 19.2.5 — theta_20_9_2's second conjunct), the incomplete-Beta
# integrand (DLMF 8.17.1 kernel — hasDerivAt_incompleteBeta), and Binet's function
# FLMF.Gamma.binet (DLMF §5.9/5.11.1 — tendsto_x_binet). Plus the anchored but
# deliberately UNREGISTERED AP prime-sum helper _ap_prime_sum (NOT-bound note below).

_PC_SIEVE_CAP = 2 * 10 ** 6            # mirror fidelity_extract._primes_upto's cap (OOM guard)
_PC_CACHE = {"limit": 0, "primes": []}  # own cache — the extractor's sieve is parser-lane


def _sieve_primes(n, what):
    """All primes ≤ n (exact, cached Eratosthenes), hard-capped at 2·10⁶ like the
    extractor's `_primes_upto` — a larger request RAISES (honest point drop, never an
    unbounded allocation; the Tier-1 probe ladders need only n ≤ 10⁵)."""
    n = _nat(n, what)
    if n > _PC_SIEVE_CAP:
        raise ValueError(f"{what}: n = {n} above the {_PC_SIEVE_CAP} sieve cap")
    if n < 2:
        return []
    if n > _PC_CACHE["limit"]:
        lim = max(n, 1000)
        sieve = bytearray([1]) * (lim + 1)
        sieve[0] = sieve[1] = 0
        for i in range(2, int(lim ** 0.5) + 1):
            if sieve[i]:
                sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        _PC_CACHE["limit"] = lim
        _PC_CACHE["primes"] = [i for i in range(lim + 1) if sieve[i]]
    import bisect
    ps = _PC_CACHE["primes"]
    return ps[:bisect.bisect_right(ps, n)]


def _prime_counting(n):
    """Mathlib `Nat.primeCounting n` = #{p prime : p ≤ n} — the INCLUSIVE π(n)
    (`Nat.primeCounting n = Nat.primeCounting' (n+1)`; Mathlib's primed variant is the
    STRICT count #{p < n}, differing at every prime argument — π(3) = 2 vs π′(3) = 1 is
    the verify() discriminating point). Exact sieve count, capped per _sieve_primes."""
    return mp.mpf(len(_sieve_primes(n, "Nat.primeCounting")))


def _complementary_modulus_real(k):
    """FLMF `FLMF.JacobiElliptic.complementaryModulus (k : ℝ) = Real.sqrt (1 − k²)`
    (JacobiSpecialValues.lean:34) — the DLMF 19.2.5 real-MODULUS k′, with the Mathlib
    junk √(negative) = 0 for |k| > 1 mirrored via _rsqrt. Registered ONLY under its
    QUALIFIED spellings: the BARE key `complementaryModulus` is the Theta τ-form
    θ₄(0,τ)²/θ₃(0,τ)² (_complementary_modulus above) — a DIFFERENT function of a
    DIFFERENT variable, and the extractor's `_NS_STRIP_BLOCK` deliberately refuses
    namespace-stripping for this leaf so ONLY exact qualified keys can resolve the
    JacobiElliptic head (aliasing hazard documented there). verify() anchors the two
    parametrizations' COHERENCE, √(1−k(τ)²) = (θ₄/θ₃)²(τ), and pins k′(0.6) = 0.8."""
    return _rsqrt(1 - k ** 2)


def _beta_integrand(a, b, t):
    """FLMF `integrand a b t = t^(a−1) · (1−t)^(b−1)` (IncompleteBeta.lean:39) — the
    DLMF 8.17.1 UNREGULARIZED incomplete-Beta kernel; its Tier-1 consumer is the FTC
    row hasDerivAt_incompleteBeta, hypothesis-fenced to 0 < a and 0 < x < 1 where both
    power bases are positive. The Real-rpow slots go through mp.power (principal
    branch — the sweep's rpow convention; a complex value off (0,1) is a dropped
    point, never a junk number). BARE-KEY COLLISION AUDIT (per the file-local-heads
    rule above): FLMF's two other `integrand` defs (Fresnel/HyperbolicUmbilic.lean:38,
    Fresnel/EllipticUmbilic.lean:45) both take FOUR arguments ((x y z : ℝ)(p : ℝ×ℝ)),
    so this 3-ary binding raises TypeError on them — an honest drop, never a wrong
    number. verify() pins the exponent convention against the t^a(1−t)^b shift rival
    and anchors d/dx B(x;a,b) = integrand (the row's own FTC content, DLMF 8.17)."""
    return mp.power(t, a - 1) * mp.power(1 - t, b - 1)


def _ap_prime_sum(a, q, M):
    """FLMF `apPrimeSum (a : ZMod q) (M : ℕ) = ∑_{p ≤ M prime, (p : ZMod q) = a}
    Real.log p / p` (NumberTheory/MertensAP.lean:52) — the DLMF 27.11.11
    Mertens-in-AP partial sum. NOT REGISTERED (see the NOT-bound note below): the
    congruence filter needs the MODULUS q, which is a separate sampled binder the
    registry 'fn' kind never receives. Kept here fully anchored so an extractor-side
    name-branch (the additionMatrix pattern — call ob._ap_prime_sum(a, q, M) with the
    sampled q threaded directly) needs no further bindings-side work. Exact integer
    filter arithmetic; sieve capped per _sieve_primes (probes need M ≤ 10⁵)."""
    q = _nat(q, "apPrimeSum modulus")
    if q == 0:
        raise ValueError("apPrimeSum: modulus 0 (ZMod 0 = ℤ not sampled)")
    a = int(a) % q
    return mp.fsum(mp.log(p) / p for p in _sieve_primes(M, "apPrimeSum") if p % q == a)


REGISTRY.update({
    # π(n) — Mathlib Nat.primeCounting, INCLUSIVE count of primes ≤ n (DLMF §27.2;
    # exact-name key, `Nat` is not an FLMF namespace segment):
    "Nat.primeCounting": ("fn", _prime_counting),
    # real-modulus complementary modulus k′ = √(1−k²) (DLMF 19.2.5) — QUALIFIED keys
    # only; the bare `complementaryModulus` key stays the Theta τ-form (see
    # _complementary_modulus_real's docstring and the extractor's _NS_STRIP_BLOCK):
    "FLMF.JacobiElliptic.complementaryModulus": ("fn", _complementary_modulus_real),
    "JacobiElliptic.complementaryModulus": ("fn", _complementary_modulus_real),
    # incomplete-Beta kernel t^{a−1}(1−t)^{b−1} (DLMF 8.17.1; collision audit in the
    # docstring — the same-named 4-ary umbilic integrands raise, never evaluate):
    "integrand": ("fn", _beta_integrand),
    # Binet's remainder J(z) (DLMF §5.9/5.11.1) — the QUALIFIED spellings of the
    # ALREADY-BOUND bare `binet` (the M14 _binet above; `Gamma` is not in
    # _FLMF_NS_SEGS, so `FLMF.Gamma.binet` — the tendsto_x_binet head — could never
    # strip down to the bare key). Same callable, no second implementation; the A4
    # verify() block adds the DLMF 5.9.9 quadrature + 5.11.1-tail anchors with the
    # missing-½log(2π) rival discriminator on top of the existing M14 anchors.
    "FLMF.Gamma.binet": ("fn", _binet),
    "Gamma.binet": ("fn", _binet),
})
# NOT bound (honest structural triage, extractor lane — A4):
#  * `apPrimeSum a M` (MertensAP.lean:52, DLMF 27.11.11 / mertens_first_ap) — the
#    p ≡ a (mod q) filter needs the modulus q, a SEPARATE sampled binder: the registry
#    'fn' kind receives only the explicit argument values (a, M), and 'envfn' fires
#    only on 0-ary atoms. Registering a 2-ary stub would merely demote the honest
#    `unbound:apPrimeSum` skip to an uninformative `domain`. The anchored
#    implementation is ready as ob._ap_prime_sum(a, q, M) for an extractor-side
#    name-branch that threads the sampled q (the additionMatrix/ob._wp pattern).
#  * `qHyper r s ![a] ![b] q z` (DLMF 17.4.1 / qHyper_one_zero) — still the
#    ('vec', …) leaf-match gap recorded in the A3 note above; no qHyper branch had
#    landed in fidelity_extract.py at this session's final composed-state check.


# ── A5 final-batch cluster (Agent A5, 2026-07-21) ────────────────────────────────────
# Heads: Mathlib's Complex/Real.GammaSeq (the Euler/Gauss limit sequence, DLMF 5.8.1 —
# GammaSeq_tendsto_Gamma_*), FLMF signedFirst (DLMF 26.8 — natAbs_signedFirst), and the
# 6.10.1 Laplace-representation coefficient expint_6_10_1_laplaceCoeff (DLMF 6.10.1 —
# expint_6_10_1_cCoeff_eq_laplaceCoeff_of_recurrence). Plus in-place robustness repairs to
# _sphericalj / _mod_spherical_i (unstable forward recurrences → DLMF 10.47.3/10.47.7 closed
# forms) and _recip_gamma_coeff (ambient-precision cancellation → boosted-precision build),
# and the _stirling1u k>n out-of-range fix — all edited at their def sites above.

def _gamma_seq_complex(s, n):
    """Mathlib `Complex.GammaSeq s n = n^s · n! / ∏_{j=0}^{n} (s+j)` (Analysis/…/Gamma/
    Beta.lean:230) — the Euler/Gauss finite approximant whose n→∞ limit IS Γ(s) (DLMF 5.8.1,
    the classical limit DEFINITION of Γ). The denominator ∏_{j=0}^{n}(s+j) is the rising
    factorial rf(s, n+1) of length n+1 (NOT rf(s,n) — the off-by-one Pochhammer rival diverges,
    ~200× off at n=200). NON-CIRCULAR: this is the SEQUENCE itself (mp.rf/factorial), never
    mp.gamma; the Tendsto check is the genuine numerical convergence GammaSeq(s,n)→Γ(s)."""
    return mp.mpc(n) ** s * mp.factorial(int(n)) / mp.rf(s, int(n) + 1)


def _gamma_seq_real(s, n):
    """Mathlib `Real.GammaSeq s n = n^s · n! / ∏_{j=0}^{n}(s+j)` (Beta.lean:231) — the
    real-argument twin of _gamma_seq_complex (DLMF 5.8.1)."""
    return mp.mpf(n) ** s * mp.factorial(int(n)) / mp.rf(s, int(n) + 1)


def _signed_first(n, k):
    """FLMF `signedFirst n k = (−1)^(n∸k) · cycle n k` (Combinatorics/Stirling.lean:63) — the
    signed Stirling number of the first kind s(n,k) (DLMF 26.8, falling-factorial coeffs). The
    exponent uses Lean's ℕ-TRUNCATED subtraction n∸k (0 when k>n), mirrored exactly here;
    immaterial to the value since cycle(n,k)=0 for k>n regardless, but kept faithful. Consumer
    natAbs_signedFirst asserts |s(n,k)| = cycle(n,k)."""
    n = _nat(n, "signedFirst n")
    k = _nat(k, "signedFirst k")
    exp = n - k if n >= k else 0        # ℕ-truncated subtraction (Lean `n - k`)
    return mp.mpf((-1) ** exp) * _stirling1u(n, k)


def _expint_6101_laplace_coeff(k):
    """FLMF `expint_6_10_1_laplaceCoeff k = ∫₀^∞ e^{−s}·laplacePoly(k,s) ds` (OtherExpansions
    .lean:1331), with `laplacePoly(k,s) = (−1)^k · Ring.choose s k = (−1)^k/k! · ∏_{i=0}^{k−1}
    (s−i)` (:1327, DLMF 6.10.1 Laplace representation). Since laplacePoly is a degree-k
    polynomial in s, the improper integral is computed EXACTLY by the Γ-moment rule
    ∫₀^∞ e^{−s} sᵐ ds = m! — no quadrature. Consumer
    expint_6_10_1_cCoeff_eq_laplaceCoeff_of_recurrence asserts cCoeff k = laplaceCoeff k."""
    k = int(k)
    coeffs = [mp.mpf(1)]                # ascending-power coeffs of ∏_{i=0}^{k−1}(s−i)
    for i in range(k):
        new = [mp.mpf(0)] * (len(coeffs) + 1)
        for m, c in enumerate(coeffs):
            new[m + 1] += c            # s · c
            new[m] += c * (-i)         # (−i) · c
        coeffs = new
    moment = mp.fsum(c * mp.factorial(m) for m, c in enumerate(coeffs))
    return mp.mpf((-1) ** k) / mp.factorial(k) * moment


REGISTRY.update({
    # Euler/Gauss limit sequences GammaSeq(s,n) = n^s·n!/rf(s,n+1) → Γ(s) (DLMF 5.8.1);
    # `Complex`/`Real` are not FLMF namespace segments, so exact-name keys (namespace
    # stripping cannot reach a bare `GammaSeq`, and there is no bare GammaSeq def anyway):
    "Complex.GammaSeq": ("fn", _gamma_seq_complex),
    "Real.GammaSeq": ("fn", _gamma_seq_real),
    # signed Stirling 1st kind s(n,k) = (−1)^(n∸k)·c(n,k) (DLMF 26.8):
    "signedFirst": ("fn", _signed_first),
    # 6.10.1 Laplace-representation coefficient ∫₀^∞ e^{−s}(−1)^k C(s,k) ds (DLMF 6.10.1):
    "expint_6_10_1_laplaceCoeff": ("fn", _expint_6101_laplace_coeff),
})


# ── convention table: the §5 "bind by anchoring, not by name" decisions ──────
# Each row records, for a function whose convention DIVERGES across the literature: the
# convention FLMF/DLMF uses, the mpmath binding, a DISTINGUISHING point (where conventions
# disagree), and the rejected alternative.  `ours`/`theirs` are callables evaluated at that
# point so the divergence is shown as two concrete numbers (and verify() asserts they
# actually differ — a genuine distinguishing point).  Source for docs/CONVENTIONS.md.
_q = mp.mpf("0.7")
CONVENTIONS = [
    dict(func="Hermite Heₙ", dlmf="18.3, 18.7.19",
         convention="probabilists' Heₙ (He₀=1, He₁=x, He₍ₙ₊₁₎=x·Heₙ−n·He₍ₙ₋₁₎) — Mathlib `Polynomial.hermite`",
         binding="2^(−n/2)·hermite(n, x/√2)", point="He₃(2)",
         ours=lambda: _hermite_prob(3, 2), theirs=lambda: mp.hermite(3, 2),
         rejected="mpmath/scipy `hermite` = physicists' Hₙ — off by ~2^(n/2)"),
    dict(func="Bernoulli Bₙ", dlmf="24.2.1",
         convention="B₁ = −1/2 (modern/NIST); FLMF also carries the B⁺ variant as `bernoulli'`",
         binding="mp.bernoulli(n)  (and bernoulli' = +1/2 only at n=1)", point="B₁",
         ours=lambda: _bernoulli_mathlib(1), theirs=lambda: _bernoulli_prime_mathlib(1),
         rejected="older B₁ = +1/2 convention (FLMF's `bernoulli'`) — sign flip at n=1"),
    dict(func="Real.log", dlmf="4.2",
         convention="Mathlib `Real.log x = log|x|`, log 0 = 0 (real-valued everywhere)",
         binding="log∘abs", point="log(−2)",
         ours=lambda: _rlog(-2), theirs=lambda: mp.log(-2),
         rejected="principal complex log `mp.log` — adds iπ at negatives (the product law fails)"),
    dict(func="Real.sqrt", dlmf="4.2",
         convention="Mathlib `Real.sqrt x = 0` for x < 0 (junk value), else the real root",
         binding="0 on negatives, else √", point="√(−3)  [|·| of rejected]",
         ours=lambda: _rsqrt(-3), theirs=lambda: abs(mp.sqrt(-3)),
         rejected="complex root `mp.sqrt(−3)=i√3` — non-real, breaks identities like cos(arcsin x)=√(1−x²)"),
    dict(func="arcsin / arccos", dlmf="4.23",
         convention="Mathlib `Real.arcsin/arccos` CLAMP the argument to [−1,1] (so identities are unconditional)",
         binding="asin/acos ∘ clamp[−1,1]", point="cos(arcsin 1.7)",
         ours=lambda: mp.cos(mp.asin(_clamp(mp.mpf("1.7")))), theirs=lambda: mp.cos(mp.asin(mp.mpf("1.7"))),
         rejected="unclamped `mp.asin` — complex outside [−1,1]; cos(arcsin x)=√(1−x²) would 'fail' for |x|>1"),
    dict(func="Jacobi sn/cn/dn", dlmf="22.2",
         convention="2nd argument is the MODULUS k (DLMF), bound to mpmath's PARAMETER m = k²",
         binding="ellipfun('sn', u, k²)", point="sn(0.8, k=0.6)",
         ours=lambda: mp.ellipfun("sn", mp.mpf("0.8"), mp.mpf("0.6") ** 2),
         theirs=lambda: mp.ellipfun("sn", mp.mpf("0.8"), mp.mpf("0.6")),
         rejected="passing k straight to mpmath's m-slot (k-as-parameter) — wrong unless k∈{0,1}"),
    dict(func="incomplete Γ (upper/lower)", dlmf="8.2.1, 8.2.2",
         convention="UNREGULARIZED γ(a,x)=∫₀ˣ, Γ(a,x)=∫ₓ^∞  (so γ+Γ=Γ(a))",
         binding="gammainc(a,0,x) / gammainc(a,x,∞)", point="γ(2.3,1.4)+Γ(2.3,1.4) − Γ(2.3)",
         ours=lambda: mp.gammainc(mp.mpf("2.3"), 0, mp.mpf("1.4")) + mp.gammainc(mp.mpf("2.3"), mp.mpf("1.4"), mp.inf) - mp.gamma(mp.mpf("2.3")),
         theirs=lambda: mp.gammainc(mp.mpf("2.3"), 0, mp.mpf("1.4")) / mp.gamma(mp.mpf("2.3")),
         rejected="REGULARIZED P(a,x)=γ/Γ, Q(a,x)=Γ/Γ — same name, divided by Γ(a)"),
    dict(func="Legendre Qₙ", dlmf="14.2.2",
         convention="degree n, order m=0, real branch on (−1,1)",
         binding="legenq(n, 0, x)", point="Q₀(0.7) − ½ln((1+x)/(1−x))",
         ours=lambda: mp.legenq(0, 0, _q) - mp.mpf("0.5") * mp.log((1 + _q) / (1 - _q)),
         theirs=None,
         rejected="the on-cut/off-cut (|x|>1) and order-m≠0 variants carry different normalizations"),
    dict(func="spherical Bessel jₙ", dlmf="10.47.3, 10.49.3",
         convention="jₙ(x) = √(π/2x)·J_{n+½}(x)", binding="√(π/2x)·besselj(n+½, x)",
         point="j₀(0.7) − sin(0.7)/0.7",
         ours=lambda: _sphericalj(0, _q) - mp.sin(_q) / _q, theirs=None,
         rejected="the second-kind yₙ, or the unnormalized J_{n+½}, share the 'spherical' label"),
    dict(func="Chebyshev Tₙ/Uₙ", dlmf="18.3",
         convention="Tₙ(cosθ)=cos nθ, Uₙ(cosθ)sinθ=sin((n+1)θ) on [−1,1]",
         binding="chebyt / chebyu", point="T₅(cos 0.7) − cos(3.5)",
         ours=lambda: _chebyt(5, mp.cos(_q)) - mp.cos(5 * _q), theirs=None,
         rejected="shifted Chebyshev T*ₙ(x)=Tₙ(2x−1) on [0,1] — a distinct, same-named family"),
    # ── M4 additions: every entry below is a genuine same-name convention TRAP ──
    dict(func="elliptic F(φ,k)", dlmf="19.2.4",
         convention="2nd arg is the MODULUS k (Lean ∫₀^φ dt/√(1−k²sin²t)), bound to mpmath's PARAMETER m=k²",
         binding="ellipf(φ, k²)", point="F(1.1, k=0.6)",
         ours=lambda: mp.ellipf(mp.mpf("1.1"), mp.mpf("0.6") ** 2),
         theirs=lambda: mp.ellipf(mp.mpf("1.1"), mp.mpf("0.6")),
         rejected="passing k straight into mpmath's m-slot — wrong by ~0.067 here (the k-vs-m trap, as for Jacobi sn)"),
    dict(func="incomplete Beta B(x;a,b)", dlmf="8.17.1",
         convention="UNREGULARIZED B(x;a,b)=∫₀ˣ t^(a−1)(1−t)^(b−1)dt (Lean `incompleteBeta`)",
         binding="betainc(a, b, 0, x)", point="B(0.4; 2.3, 1.7)",
         ours=lambda: mp.betainc(mp.mpf("2.3"), mp.mpf("1.7"), 0, mp.mpf("0.4")),
         theirs=lambda: mp.betainc(mp.mpf("2.3"), mp.mpf("1.7"), 0, mp.mpf("0.4"), regularized=True),
         rejected="REGULARIZED I_x(a,b)=B(x;a,b)/B(a,b) — same name, divided by the complete B(a,b)"),
    dict(func="associated Legendre Pₙᵐ", dlmf="14.7.10",
         convention="Ferrers form, Condon–Shortley phase (−1)^m INCLUDED (Lean (−1)^m(1−x²)^(m/2)dᵐPₙ)",
         binding="legenp(n, m, x)", point="P₁¹(0.5) = −√3/2",
         ours=lambda: mp.legenp(1, 1, mp.mpf("0.5")),
         theirs=lambda: -mp.legenp(1, 1, mp.mpf("0.5")),
         rejected="dropping the Condon–Shortley (−1)^m — a sign flip at every odd order m"),
    # ── M7 additions ──
    dict(func="theta θⱼ(z,τ)", dlmf="20.2.1–20.2.4",
         convention="FLMF θⱼ z τ on jacobiTheta₂ (period 1 in z, 2nd arg = lattice parameter τ)",
         binding="jtheta(j, πz, e^{iπτ})  — BOTH knobs: w = πz and nome q = e^{iπτ}", point="θ₃(0.3, 0.5+0.8i)",
         ours=lambda: mp.jtheta(3, mp.pi * mp.mpf("0.3"), _theta_q(mp.mpc("0.5", "0.8"))),
         theirs=lambda: mp.jtheta(3, mp.mpf("0.3"), mp.mpc("0.5", "0.8")),
         rejected="passing z unscaled and τ straight into mpmath's nome slot — wrong on both counts"),
    dict(func="modular λ(τ)", dlmf="22.2, 23.15.6",
         convention="λ = (θ₂/θ₃)⁴ = k² — the SQUARE of the elliptic modulus (λ(i) = 1/2)",
         binding="(jtheta(2,0,q)/jtheta(3,0,q))⁴", point="λ(i) vs k(i)",
         ours=lambda: _modular_lambda(mp.mpc(0, 1)),
         theirs=lambda: _elliptic_modulus(mp.mpc(0, 1)),
         rejected="conflating λ with the modulus k = θ₂²/θ₃² itself — off by a square root (k(i) = 1/√2)"),
    dict(func="Bernoulli polynomial Bₙ(x)", dlmf="24.2.3",
         convention="standard Bₙ(x) = Σ C(n,i)·B⁻ᵢ·x^{n−i} (Mathlib `Polynomial.bernoulli`; B₁(0) = −1/2)",
         binding="mp.bernpoly(n, x)", point="B₁(0)",
         ours=lambda: mp.bernpoly(1, 0), theirs=lambda: mp.bernpoly(1, 1),
         rejected="the shifted Bₙ(x+1) / B⁺ variant (B₁(0) = +1/2) — Faulhaber identities move by a boundary term"),
    dict(func="digamma ψ(x)", dlmf="5.2.2, 5.4.14",
         convention="ψ = Γ′/Γ (Lean realDigamma = deriv(log∘Γ)); ψ(1) = −γ",
         binding="mp.digamma", point="ψ(1) vs H₁ − γ = 1 − γ",
         ours=lambda: mp.digamma(1), theirs=lambda: 1 - mp.euler,
         rejected="the off-by-one ψ(n) ↔ harmonic confusion: ψ(n+1) = Hₙ − γ, NOT ψ(n)"),
    dict(func="modified spherical iₙ/kₙ", dlmf="10.49.8, 10.49.12",
         convention="no extra π/2: iₙ(z)=√(π/2z)·I_{n+½}(z), kₙ(z)=√(2/πz)·K_{n+½}(z) (Lean base i₀=sinh z/z, k₀=e^{−z}/z)",
         binding="√(π/2z)·besseli(n+½,z) / √(2/πz)·besselk(n+½,z)", point="k₀(1.7) vs the π/2-weighted variant",
         ours=lambda: mp.sqrt(2 / (mp.pi * mp.mpf("1.7"))) * mp.besselk(mp.mpf(1) / 2, mp.mpf("1.7")),
         theirs=lambda: mp.pi / 2 * mp.sqrt(2 / (mp.pi * mp.mpf("1.7"))) * mp.besselk(mp.mpf(1) / 2, mp.mpf("1.7")),
         rejected="the π/2-weighted spherical-K convention — an extra π/2 factor on kₙ"),
]

# Known convention hazards for functions NOT yet oracle-bound — to anchor when added.
FUTURE_HAZARDS = [
    ("Fourier transform", "2π placement (1/√2π symmetric vs e^{−2πi} vs e^{−i}) and exponent sign — 4 common variants"),
    ("Spherical harmonics Yₗᵐ", "the assocLegendre Pₙᵐ phase is now bound (CONVENTIONS); Yₗᵐ still adds the 4π / orthonormal normalization choice"),
    ("Bessel 2nd kind", "Yₙ (Weber) vs Nₙ (Neumann); Hankel H⁽¹⁾/H⁽²⁾ exponent sign"),
    ("Exponential integral", "Ei(x) vs E₁(x) — sign and branch differ"),
    ("Mathieu / spheroidal", "Ince vs Meixner–Schäfke vs Flammer normalizations; (a,q) parametrization"),
    ("Laguerre Lₙ^(α)", "with/without the 1/n! normalization; generalized vs simple"),
]


# ── anchored self-test: every binding verified at a DISTINGUISHING point ──────
def verify():
    fails = []

    def chk(name, got, want, tol=mp.mpf("1e-20")):
        # complex-aware: mp.mpf rejects mpc, so use mpmathify + |·| which handle both.
        if abs(mp.mpmathify(got) - mp.mpmathify(want)) >= tol:
            fails.append(f"{name}: got {mp.nstr(got,12)} want {mp.nstr(want,12)}")

    # bernoulli vs bernoulli' disagree exactly at n=1 — the distinguishing point
    chk("bernoulli(1)=-1/2", _bernoulli_mathlib(1), mp.mpf(-1) / 2)
    chk("bernoulli'(1)=+1/2", _bernoulli_prime_mathlib(1), mp.mpf(1) / 2)
    chk("bernoulli(2)=1/6", _bernoulli_mathlib(2), mp.mpf(1) / 6)
    # vonStaudtSum (DLMF 24.10.1): the defining prime-reciprocal values Σ_{(p−1)∣2k} 1/p,
    # plus the theorem's own integrality at 2k = 12 — B₁₂ + Σ = −691/2730 + 3421/2730 = 1
    # (the 691 test rejects any off-by-one in the (p−1) ∣ 2k filter or the range bound).
    chk("vonStaudtSum(0)=0 (empty Lean range)", _von_staudt_sum(0), mp.mpf(0))
    chk("vonStaudtSum(1)=1/2+1/3=5/6", _von_staudt_sum(1), mp.mpf(5) / 6)
    chk("vonStaudtSum(2)=1/2+1/3+1/5=31/30", _von_staudt_sum(2), mp.mpf(31) / 30)
    chk("vonStaudtSum(3)=1/2+1/3+1/7=41/42", _von_staudt_sum(3), mp.mpf(41) / 42)
    chk("B12+vonStaudtSum(6)=1 (DLMF 24.10.1, the 691 test)",
        _bernoulli_mathlib(12) + _von_staudt_sum(6), mp.mpf(1))
    # Euler numbers (eulerNumberQ): SIGNED sech convention, DLMF 24.2.6 / Table 24.2.
    # E₂=−1 is the distinguishing point vs the unsigned secant numbers (+1); E₃=0 vs the
    # zigzag/up-down numbers (A₃=2). GF anchor: Eₙ = n!·[tⁿ] sech t at n=6.
    chk("eulerNumber E2=-1", mp.eulernum(2), mp.mpf(-1))
    chk("eulerNumber E3=0 (not zigzag)", mp.eulernum(3), mp.mpf(0))
    chk("eulerNumber E10=-50521", mp.eulernum(10), mp.mpf(-50521))
    chk("eulerNumber GF anchor E6=6!·[t^6]sech t", mp.eulernum(6),
        mp.taylor(mp.sech, 0, 6)[6] * mp.factorial(6))
    # Tangent numbers (tangentNumberQ): GF-indexed tan t = Σ Tₙ tⁿ/n!, DLMF §24.15(iii).
    # T₂=0 is the distinguishing point vs the compressed odd-only indexing (T₂=2 there);
    # GF anchors: Tₙ = n!·[tⁿ] tan t at n=5 and n=7 (defining formula, decorrelated from
    # the Bernoulli closed form the binding computes with).
    chk("tangentNumber T0=0", _tangent_number(0), mp.mpf(0))
    chk("tangentNumber T1=1", _tangent_number(1), mp.mpf(1))
    chk("tangentNumber T2=0 (not compressed indexing)", _tangent_number(2), mp.mpf(0))
    chk("tangentNumber T3=2", _tangent_number(3), mp.mpf(2))
    chk("tangentNumber GF anchor T5=5!·[t^5]tan t", _tangent_number(5),
        mp.taylor(mp.tan, 0, 5)[5] * mp.factorial(5))
    chk("tangentNumber GF anchor T7=7!·[t^7]tan t", _tangent_number(7),
        mp.taylor(mp.tan, 0, 7)[7] * mp.factorial(7))
    # Euler polynomials (eulerPoly): anchored to the DLMF 24.2.6 DEFINING g.f. coefficient
    # n!·[tⁿ] 2e^{xt}/(eᵗ+1) (Taylor-extracted, decorrelated from mp.eulerpoly's internal
    # closed form) AND to the Lean Bernoulli-bridge definition (A&S 23.1.27, recomputed
    # independently with mp.bernpoly). E₁(0) = −1/2 is the convention pin: a B⁺-based
    # bridge or the Euler-number normalization 2ⁿEₙ(½)=Eₙ would give +1/2 resp. 0 there.
    _epb = REGISTRY["eulerPoly"][1]
    _epx = mp.mpf("0.7")
    chk("eulerPoly E0=1", _epb(0, _epx), 1)
    chk("eulerPoly E1(0)=−1/2 (convention pin)", _epb(1, 0), mp.mpf(-1) / 2)
    chk("eulerPoly GF anchor E3(0.7)=3!·[t³]2e^{xt}/(eᵗ+1)", _epb(3, _epx),
        mp.taylor(lambda t: 2 * mp.e ** (_epx * t) / (mp.e ** t + 1), 0, 3)[3]
        * mp.factorial(3))
    chk("eulerPoly bridge E4(0.7)=(2/5)(B₅(x)−2⁵B₅(x/2))", _epb(4, _epx),
        mp.mpf(2) / 5 * (mp.bernpoly(5, _epx) - 2 ** 5 * mp.bernpoly(5, _epx / 2)))
    # Bernoulli EGF psfn1 rows (DLMF 24.2.1): Taylor-extract [tⁿ] of the bound analytic
    # g.f.s and compare with the DEFINING mk-coefficients Bₙ/n! resp. B'ₙ/n! through n=4 —
    # n=1 (−1/2 vs +1/2) is the exact point where the B⁻/B⁺ conventions disagree, and the
    # shared [t⁴] = B₄/4! = −1/720 catches a wrong-function binding outright. Plus the
    # removable value 1 at t=0 (the sampled-indeterminate grid never hits 0, but the
    # guard must be the mathematically correct limit, not junk).
    _bps = REGISTRY["bernoulliPowerSeries"][1]
    _bpsp = REGISTRY["bernoulli'PowerSeries"][1]
    _btc = mp.taylor(lambda t: _bps(None, t), 0, 4)
    _btcp = mp.taylor(lambda t: _bpsp(None, t), 0, 4)
    for _bn in range(5):
        chk(f"bernoulliPowerSeries [t^{_bn}]=B{_bn}/{_bn}!", _btc[_bn],
            _bernoulli_mathlib(_bn) / mp.factorial(_bn))
        chk(f"bernoulli'PowerSeries [t^{_bn}]=B'{_bn}/{_bn}!", _btcp[_bn],
            _bernoulli_prime_mathlib(_bn) / mp.factorial(_bn))
    chk("bernoulliPowerSeries g.f.(0)=1", _bps(None, mp.mpf(0)), 1)
    chk("bernoulli'PowerSeries g.f.(0)=1", _bpsp(None, mp.mpf(0)), 1)
    # Chebyshev: T₅(cos.7)=cos 3.5 ; U defining identity
    chk("T defining", _chebyt(5, mp.cos(mp.mpf("0.7"))), mp.cos(5 * mp.mpf("0.7")))
    chk("U defining", _chebyu(4, mp.cos(mp.mpf("0.7"))) * mp.sin(mp.mpf("0.7")),
        mp.sin(5 * mp.mpf("0.7")))
    # Hermite probabilists' He₃(2) = 2³ − 3·2 = 2  (physicists' would give 40 — the trap)
    chk("hermite prob He3(2)=2", _hermite_prob(3, 2), mp.mpf(2))
    chk("hermite prob He0=1", _hermite_prob(0, mp.mpf("1.3")), mp.mpf(1))
    # hermiteGF (psfn1): the DEFINING coefficient property of DLMF 18.12.16,
    # [tⁿ] e^{xt−t²/2} = Heₙ(x)/n! — Taylor-extracted via mp.taylor, decorrelated from the
    # closed form. Distinguishing point [t³]@x=2 = He₃(2)/3! = 1/3: the physicists' g.f.
    # e^{2xt−t²} (DLMF 18.12.15) gives H₃(2)/3! = 40/6 = 20/3 there — rejected.
    _hgf = REGISTRY["hermiteGF"][1]
    chk("hermiteGF [t^0]@x=2 = He0(2)/0! = 1",
        mp.taylor(lambda t: _hgf(2, t), 0, 0)[0], mp.mpf(1))
    chk("hermiteGF [t^3]@x=2 = He3(2)/3! = 1/3 (not physicists' 20/3)",
        mp.taylor(lambda t: _hgf(2, t), 0, 3)[3], mp.mpf(1) / 3)
    chk("hermiteGF [t^4]@x=0.7 = He4(0.7)/4!",
        mp.taylor(lambda t: _hgf(mp.mpf("0.7"), t), 0, 4)[4],
        _hermite_prob(4, mp.mpf("0.7")) / mp.factorial(4))
    # Gauss continued-fraction coefficients (DLMF §15.7): DECORRELATED anchor — the
    # generalized continued fraction built from the BOUND coefficients (with the exact
    # GenContFract h and (aₙ,bₙ) stream of Ch15ContinuedFractions.lean) must converge to
    # the DLMF-stated limit, computed via mpmath's independent hyp2f1 (Olver F = ₂F₁/Γ(c)).
    def _cf(_h, _pair, _N=180):
        _acc = mp.mpf(0)
        for _k in range(_N, -1, -1):
            _an, _bn = _pair(_k)
            _acc = _an / (_bn + _acc)
        return _h + _acc

    _ga, _gb, _gc, _gz = mp.mpf("0.5"), mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf("0.2")
    _olv = lambda A, B, C, Z: mp.hyp2f1(A, B, C, Z) / mp.gamma(C)
    _tC, _uC = REGISTRY["gaussTCoeff"][1], REGISTRY["gaussUCoeff"][1]
    _vC, _wC = REGISTRY["gaussVCoeff"][1], REGISTRY["gaussWCoeff"][1]
    _xC, _yC = REGISTRY["gaussXCoeff"][1], REGISTRY["gaussYCoeff"][1]
    # 15.7.1/2  h=t₀ ; pair n = (−u_{n+1}·z, t_{n+1}) ;  F(a,b;c)/F(a,b+1;c+1)
    chk("gauss t/u CF → hyp2f1 ratio (15.7.2)",
        _cf(_tC(_gc, 0),
            lambda n: (-_uC(_ga, _gb, _gc, n + 1) * _gz, _tC(_gc, n + 1))),
        _olv(_ga, _gb, _gc, _gz) / _olv(_ga, _gb + 1, _gc + 1, _gz), mp.mpf("1e-30"))
    # 15.7.3/4  h=v₀ ; pair n = (−w_{n+1}, v_{n+1}) ;  same ratio
    chk("gauss v/w CF → hyp2f1 ratio (15.7.4)",
        _cf(_vC(_ga, _gb, _gc, _gz, 0),
            lambda n: (-_wC(_ga, _gb, _gc, _gz, n + 1), _vC(_ga, _gb, _gc, _gz, n + 1))),
        _olv(_ga, _gb, _gc, _gz) / _olv(_ga, _gb + 1, _gc + 1, _gz), mp.mpf("1e-30"))
    # olverHypergeometric (Olver.lean:51, the series SUM) = its own DEFINING partial sum
    # Σₙ (a)ₙ(b)ₙ/(Γ(c+n)·n!) zⁿ inside |z|<1 — decorrelated from mp.hyp2f1 (direct Pochhammer
    # accumulation), pinning the binding to the series it formalizes, not the name.
    def _olv_series(a, b, c, z, N=120):
        s, term = mp.mpf(0), mp.mpf(1)      # term_0 = (a)_0(b)_0/0! = 1
        for n in range(N):
            s += term / mp.gamma(c + n)
            term *= (a + n) * (b + n) / (n + 1) * z
        return s
    chk("olverHypergeometric = defining series Σ(a)ₙ(b)ₙ/(Γ(c+n)n!)zⁿ (15.2.2, |z|<1)",
        REGISTRY["olverHypergeometric"][1](_ga, _gb, _gc, _gz),
        _olv_series(_ga, _gb, _gc, _gz), mp.mpf("1e-30"))
    chk("olverHypergeometric junk-0 off the disc (|z|≥1, FMS.sum diverges)",
        REGISTRY["olverHypergeometric"][1](_ga, _gb, _gc, mp.mpf("1.4")), mp.mpf(0))
    # TERMINATING first parameter a = −s (nonpositive integer): the series is a POLYNOMIAL and its
    # FormalMultilinearSeries.sum converges for EVERY z — so olverHypergeometric(−s,b;c;z) must be
    # the terminating polynomial even off the disc (|z|≥1), NOT junk-0. Anchor at s=4, z=2.3 (|z|>1)
    # against the direct FINITE sum Σ_{n=0}^{s} (−s)ₙ(b)ₙ/(Γ(c+n)n!) zⁿ (decorrelated from hyp2f1).
    def _olv_terminating(s, b, c, z):
        return mp.fsum(mp.rf(-s, n) * mp.rf(b, n) / (mp.gamma(c + n) * mp.factorial(n)) * z ** n
                       for n in range(s + 1))
    chk("olverHypergeometric terminating poly off disc (a=−4, |z|>1; §15.15.1 𝐅(−s,b;c;1/z₀))",
        REGISTRY["olverHypergeometric"][1](mp.mpf(-4), _gb, _gc, mp.mpf("2.3")),
        _olv_terminating(4, _gb, _gc, mp.mpf("2.3")), mp.mpf("1e-28"))
    # gaussProductCoefficient Aₛ (DLMF 15.16.2) = sth Maclaurin coeff of g(z) =
    # (1−z)^(a+b−c)·₂F₁(2a,2b;2c−1;z). Anchor the Cauchy-product binding against the NUMERICAL
    # Taylor coefficient of g (mp.taylor — an independent high-precision differentiation scheme,
    # the exact defining relation `iteratedDeriv s g 0 / s!`) at several orders including one > 15.
    def _gpc_g(a, b, c, w):
        return (1 - w) ** (a + b - c) * mp.hyp2f1(2 * a, 2 * b, 2 * c - 1, w)
    _gpc_tay = mp.taylor(lambda w: _gpc_g(_ga, _gb, _gc, w), 0, 18)
    for _s in (0, 1, 2, 5, 12, 18):
        chk(f"gaussProductCoefficient A_{_s} = [z^{_s}] g (DLMF 15.16.2 defining Taylor coeff)",
            REGISTRY["gaussProductCoefficient"][1](_ga, _gb, _gc, _s), _gpc_tay[_s], mp.mpf("1e-24"))
    # 15.7.5/6  h=x₀ ; pair n = (+y_{n+1}, x_{n+1}) ;  F(a,b;c)/F(a+1,b+1;c+1)
    chk("gauss x/y CF → hyp2f1 ratio (15.7.6)",
        _cf(_xC(_ga, _gb, _gc, _gz, 0),
            lambda n: (_yC(_ga, _gb, _gz, n + 1), _xC(_ga, _gb, _gc, _gz, n + 1))),
        _olv(_ga, _gb, _gc, _gz) / _olv(_ga + 1, _gb + 1, _gc + 1, _gz), mp.mpf("1e-30"))
    # u-coefficient parity split (15.7.2): even/odd branches at the same index disagree
    chk("gauss u even u_4=(b+2)(c−a+2)", _uC(_ga, _gb, _gc, 4),
        (_gb + 2) * (_gc - _ga + 2))
    chk("gauss u odd u_5=(a+2)(c−b+2)", _uC(_ga, _gb, _gc, 5),
        (_ga + 2) * (_gc - _gb + 2))
    # Gamma(1/2)=√π
    chk("Gamma(1/2)=√π", mp.gamma(mp.mpf(1) / 2), mp.sqrt(mp.pi))
    # Mathlib real-log convention: log(-2) = log 2, and the product law holds at negatives
    chk("Real.log(-2)=log2", _rlog(-2), mp.log(2))
    chk("log(xy)=logx+logy @ x=-0.8,y=2.4", _rlog(mp.mpf("-0.8") * mp.mpf("2.4")),
        _rlog(mp.mpf("-0.8")) + _rlog(mp.mpf("2.4")))
    chk("Real.sqrt(-3)=0", _rsqrt(-3), 0)
    # special functions — anchored at distinguishing values / defining identities
    chk("J0(0)=1", mp.besselj(0, 0), 1)
    chk("besselj recurrence", mp.besselj(0, mp.mpf("0.7")) + mp.besselj(2, mp.mpf("0.7")),
        (2 / mp.mpf("0.7")) * mp.besselj(1, mp.mpf("0.7")))
    chk("I0(0)=1", mp.besseli(0, 0), 1)
    chk("spherical j0(x)=sin x/x", _sphericalj(0, mp.mpf("0.7")),
        mp.sin(mp.mpf("0.7")) / mp.mpf("0.7"))
    # spherical Bessel closed forms (DLMF 10.47.3/10.47.7) — defining trig/hyperbolic values
    # anchor the √(π/2·)·J_{n+½} / I_{n+½} rewrite; the negative-argument parity anchor pins
    # the jₙ(−x)=(−1)ⁿjₙ(x) sign fix (the naïve √-of-negative closed form goes complex there);
    # the large-n anchor certifies the recurrence-instability repair (old form → ~1e3021).
    chk("spherical j1(x)=sin x/x²−cos x/x", _sphericalj(1, mp.mpf("0.7")),
        mp.sin(mp.mpf("0.7")) / mp.mpf("0.7") ** 2 - mp.cos(mp.mpf("0.7")) / mp.mpf("0.7"))
    chk("mod spherical i0(z)=sinh z/z", _mod_spherical_i(0, mp.mpf("0.9")),
        mp.sinh(mp.mpf("0.9")) / mp.mpf("0.9"))
    chk("mod spherical i1(z)=cosh z/z−sinh z/z²", _mod_spherical_i(1, mp.mpf("0.9")),
        mp.cosh(mp.mpf("0.9")) / mp.mpf("0.9") - mp.sinh(mp.mpf("0.9")) / mp.mpf("0.9") ** 2)
    chk("spherical j3 parity: j3(−x)=−j3(x)", _sphericalj(3, mp.mpf("-0.8")),
        -_sphericalj(3, mp.mpf("0.8")))
    chk("mod spherical i2 parity: i2(−z)=i2(z)", _mod_spherical_i(2, mp.mpf("-0.8")),
        _mod_spherical_i(2, mp.mpf("0.8")))
    if not (abs(_sphericalj(200, mp.mpf("9.05"))) < 1 and abs(_mod_spherical_i(200, mp.mpf("0.09"))) < 1e-100):
        fails.append("spherical large-n closed form not bounded/decaying (recurrence-instability repair failed)")
    chk("P2(x)=(3x²−1)/2", mp.legendre(2, mp.mpf("0.7")), (3 * mp.mpf("0.7") ** 2 - 1) / 2)
    # ── pFqCoefficient (DLMF 16.2.1): the ₚFᵩ series coefficient, self-validated three ways
    # against mpmath's independent hypergeometric kernel — (a) the n=2 closed form from the
    # DEFINING product Πᵢ(Aᵢ)ₙ/(Πⱼ(Bⱼ)ₙ·n!); (b) the term-ratio recurrence cₙ₊₁/cₙ =
    # Πᵢ(Aᵢ+n)/(Πⱼ(Bⱼ+n)·(1+n)) (DLMF 16.2.1, exactly pFqCoefficient_succ_div's claim); and
    # (c) the resummation Σₙ cₙ zⁿ = mp.hyper(A,B,z) (exactly pFq_hasSum's claim), decorrelated
    # against mpmath's own series accelerator. ──
    _pfA, _pfB = [mp.mpf("1.3"), mp.mpc("0.7", "0.4")], [mp.mpf("2.1")]
    chk("pFqCoefficient n=2 defining product",
        _pFqCoefficient(_pfA, _pfB, 2),
        mp.rf(_pfA[0], 2) * mp.rf(_pfA[1], 2) / (mp.rf(_pfB[0], 2) * mp.factorial(2)))
    chk("pFqCoefficient succ ratio c3/c2 = Πᵢ(Aᵢ+2)/(Πⱼ(Bⱼ+2)·3)",
        _pFqCoefficient(_pfA, _pfB, 3) / _pFqCoefficient(_pfA, _pfB, 2),
        (_pfA[0] + 2) * (_pfA[1] + 2) / ((_pfB[0] + 2) * (1 + mp.mpf(2))))
    _pfz = mp.mpc("0.5", "0.3")
    chk("Σₙ pFqCoefficient·zⁿ = ₂F₁(A;B;z) (pFq_hasSum resummation)",
        mp.fsum(_pFqCoefficient(_pfA, _pfB, n) * _pfz ** n for n in range(60)),
        mp.hyper(_pfA, _pfB, _pfz))
    # ── Meijer-G (DLMF 16.17.1 / 16.18.1): _meijerG anchored against BOTH proven FLMF
    # facts (meijerG_exp, meijerG_eq_pFq_zero — same LHS, e^{-z}) and a genuinely
    # nontrivial q=1 instance of the general meijerG_eq_pFq shape, cross-checked against
    # an independent direct vertical-line mp.quad of the mellinInv contour integral.
    _mgz = mp.mpf("1.7")
    chk("meijerG_exp: G^{1,0}_{0,1}(z;0) = e^{-z}",
        _meijerG([0], [], [], [], _mgz), mp.e ** (-_mgz))
    chk("meijerG_eq_pFq_zero: same LHS = pFq(;;-z) = 0F0(;;-z)",
        _meijerG([0], [], [], [], _mgz), mp.hyper([], [], -_mgz))
    _mg_a1, _mg_b1, _mg_z1 = mp.mpf("0.8") + mp.mpc(0, "0.3"), mp.mpf("2.3"), mp.mpf("0.9")
    chk("meijerG_eq_pFq q=1: G^{1,1}_{1,2}(z;1-a;0,1-b) = (Γa/Γb)·1F1(a;b;-z)",
        _meijerG([0], [1 - _mg_a1], [1 - _mg_b1], [], _mg_z1),
        (mp.gamma(_mg_a1) / mp.gamma(_mg_b1)) * mp.hyp1f1(_mg_a1, _mg_b1, -_mg_z1))
    # decorrelated direct vertical-line quadrature of the FLMF mellinInv convention
    # (1/2πi)∫_{(σ)} g(-s) z^{-s} ds, g = meijerGIntegrand — independent of mpmath's
    # own meijerg series-expansion code path.
    def _mg_direct_quad(bNum, aNum, bDen, aDen, sigma, z):
        def g(s):
            num = mp.fprod(mp.gamma(b - s) for b in bNum) * mp.fprod(mp.gamma(1 - a + s) for a in aNum)
            den = mp.fprod(mp.gamma(1 - b + s) for b in bDen) * mp.fprod(mp.gamma(a - s) for a in aDen)
            return num / den
        return mp.quad(lambda t: g(-mp.mpc(sigma, t)) * z ** (-mp.mpc(sigma, t)),
                        [-mp.inf, mp.inf]) / (2 * mp.pi)
    chk("meijerG_exp direct vertical-line quad (σ=0.6) matches _meijerG",
        _mg_direct_quad([0], [], [], [], mp.mpf("0.6"), _mgz), _meijerG([0], [], [], [], _mgz))
    chk("meijerG_eq_pFq q=1 direct vertical-line quad (σ=0.4) matches _meijerG",
        _mg_direct_quad([0], [1 - _mg_a1], [1 - _mg_b1], [], mp.mpf("0.4"), _mg_z1),
        _meijerG([0], [1 - _mg_a1], [1 - _mg_b1], [], _mg_z1))
    chk("Q0(x)=½ln((1+x)/(1−x))", mp.legenq(0, 0, mp.mpf("0.7")),
        mp.mpf("0.5") * mp.log((1 + mp.mpf("0.7")) / (1 - mp.mpf("0.7"))))
    chk("lowerΓ+upperΓ=Γ", mp.gammainc(mp.mpf("2.3"), 0, mp.mpf("1.4")) +
        mp.gammainc(mp.mpf("2.3"), mp.mpf("1.4"), mp.inf), mp.gamma(mp.mpf("2.3")))
    sn = mp.ellipfun("sn", mp.mpf("0.8"), mp.mpf("0.6") ** 2)
    cn = mp.ellipfun("cn", mp.mpf("0.8"), mp.mpf("0.6") ** 2)
    chk("Jacobi sn²+cn²=1", sn ** 2 + cn ** 2, 1)
    chk("Jacobi sn(u,0)=sin u", mp.ellipfun("sn", mp.mpf("0.8"), 0), mp.sin(mp.mpf("0.8")))
    # complex bindings — anchored at points a real-axis test could not certify
    _i = mp.mpc(0, 1)
    chk("Complex.I²=−1", _i * _i, -1)
    chk("exp(iπ)=−1 (Euler)", mp.e ** (_i * mp.pi), -1)
    chk("Complex.cos(i)=cosh 1", mp.cos(_i), mp.cosh(1))            # links cos↔cosh off the real axis
    # betaIntegral normalization: B(1,1)=1, B(2,3)=1/12, and B=Γ·Γ/Γ at a complex point
    chk("betaIntegral B(1,1)=1", mp.beta(1, 1), 1)
    chk("betaIntegral B(2,3)=1/12", mp.beta(2, 3), mp.mpf(1) / 12)
    _u, _v = mp.mpc("1.4", "0.3"), mp.mpc("0.5", "-0.8")
    chk("B(u,v)=Γu·Γv/Γ(u+v) @ complex", mp.beta(_u, _v),
        mp.gamma(_u) * mp.gamma(_v) / mp.gamma(_u + _v))
    # Γ reflection off the real axis: Γ(z)Γ(1−z)=π/sin(πz) at z=0.5+0.8i (the airy/theta regime)
    _z = mp.mpc("0.5", "0.8")
    chk("Γ reflection @ 0.5+0.8i", mp.gamma(_z) * mp.gamma(1 - _z), mp.pi / mp.sin(mp.pi * _z))
    # Anger/Weber anchored against the LEAN DEFINING INTEGRAL (the strongest §5 binding —
    # tied to the exact object formalized, not a name)
    _nu, _zz = mp.mpf("0.7"), mp.mpf("1.3")
    chk("angerJ = (1/π)∫cos(νθ−z sinθ)", mp.angerj(_nu, _zz),
        mp.quad(lambda t: mp.cos(_nu * t - _zz * mp.sin(t)), [0, mp.pi]) / mp.pi, mp.mpf("1e-25"))
    chk("weberE = (1/π)∫sin(νθ−z sinθ)", mp.webere(_nu, _zz),
        mp.quad(lambda t: mp.sin(_nu * t - _zz * mp.sin(t)), [0, mp.pi]) / mp.pi, mp.mpf("1e-25"))
    # Barnes G: G(0)=0 (Lean's junk-value AND the standard zero), G(4)=1!·2!=2
    chk("barnesG(0)=0", mp.barnesg(0), 0)
    chk("barnesG(4)=2", mp.barnesg(4), 2)
    # incompleteBeta vs its defining integral; ellipticF vs ITS defining integral — and the
    # k-vs-m trap must genuinely distinguish (ellipf(φ,k) without squaring is WRONG by ~0.07)
    _a, _b, _x = mp.mpf("2.3"), mp.mpf("1.7"), mp.mpf("0.4")
    chk("incompleteBeta = ∫₀ˣt^{a−1}(1−t)^{b−1}", mp.betainc(_a, _b, 0, _x),
        mp.quad(lambda t: t ** (_a - 1) * (1 - t) ** (_b - 1), [0, _x]), mp.mpf("1e-25"))
    _phi, _k = mp.mpf("1.1"), mp.mpf("0.6")
    _Fdef = mp.quad(lambda t: 1 / mp.sqrt(1 - _k ** 2 * mp.sin(t) ** 2), [0, _phi])
    chk("ellipticF(φ,k)=ellipf(φ,k²)", mp.ellipf(_phi, _k ** 2), _Fdef, mp.mpf("1e-25"))
    if abs(mp.ellipf(_phi, _k) - _Fdef) < mp.mpf("1e-2"):
        fails.append("ellipticF k-vs-m trap: rejected convention does not distinguish")
    # incomplete E (DLMF 19.2.5) vs ITS defining integral, same k-vs-m trap (off by 0.0485 here)
    _Edef = mp.quad(lambda t: mp.sqrt(1 - _k ** 2 * mp.sin(t) ** 2), [0, _phi])
    chk("ellipticE(φ,k)=ellipe(φ,k²)", mp.ellipe(_phi, _k ** 2), _Edef, mp.mpf("1e-25"))
    if abs(mp.ellipe(_phi, _k) - _Edef) < mp.mpf("1e-2"):
        fails.append("ellipticE k-vs-m trap: rejected convention does not distinguish")
    # complete-integral bridges (DLMF 19.2.8): F(π/2,k)=K(k), E(π/2,k)=E(k)
    chk("ellipf(π/2,m)=ellipk(m)", mp.ellipf(mp.pi / 2, _k ** 2), mp.ellipk(_k ** 2))
    chk("ellipe(π/2,m)=ellipe(m)", mp.ellipe(mp.pi / 2, _k ** 2), mp.ellipe(_k ** 2))
    # Carlson R_F (DLMF 19.16.1) vs the Lean defining half-integral, and 19.20.1 diagonal
    _cx, _cy, _cz = mp.mpf("1.2"), mp.mpf("2.3"), mp.mpf("0.7")
    # (tol 1e-14: the t^{-3/2} tail limits mp.quad on [0,∞) to ~1e-17 — still 12 orders
    # below any convention-level discrepancy)
    chk("elliprf = ½∫dt/√((t+x)(t+y)(t+z))", mp.elliprf(_cx, _cy, _cz),
        mp.quad(lambda t: 1 / mp.sqrt((t + _cx) * (t + _cy) * (t + _cz)), [0, mp.inf]) / 2,
        mp.mpf("1e-14"))
    chk("elliprf R_F(x,x,x)=x^{−1/2}", mp.elliprf(_cz, _cz, _cz), _cz ** mp.mpf("-0.5"))
    chk("elliprf R_F(1,1,1)=1", mp.elliprf(1, 1, 1), 1)
    # modified spherical Bessel, no-π/2 convention — anchored at the Lean base cases i₀,k₀,k₁
    _z17 = mp.mpf("1.7")
    chk("modSphI i₀=sinh z/z", mp.sqrt(mp.pi / (2 * _z17)) * mp.besseli(mp.mpf(1) / 2, _z17),
        mp.sinh(_z17) / _z17, mp.mpf("1e-25"))
    chk("modSphK k₀=e^{−z}/z", mp.sqrt(2 / (mp.pi * _z17)) * mp.besselk(mp.mpf(1) / 2, _z17),
        mp.exp(-_z17) / _z17, mp.mpf("1e-25"))
    chk("modSphK k₁=e^{−z}(1/z+1/z²)", mp.sqrt(2 / (mp.pi * _z17)) * mp.besselk(mp.mpf(3) / 2, _z17),
        mp.exp(-_z17) / _z17 + mp.exp(-_z17) / _z17 ** 2, mp.mpf("1e-25"))
    # assocLegendre: Condon–Shortley phase IN, matching the Lean (−1)^m — P₁¹(½)=−√¾ distinguishes
    chk("legenp P₁¹(½)=−√(3)/2 (CS in)", mp.legenp(1, 1, mp.mpf("0.5")), -mp.sqrt(mp.mpf("0.75")))
    chk("legenp P₂¹(½)=−3x√(1−x²)", mp.legenp(2, 1, mp.mpf("0.5")),
        -3 * mp.mpf("0.5") * mp.sqrt(mp.mpf("0.75")))
    # Dawson composed via erfi, anchored against the Lean defining integral e^{−x²}∫₀ˣe^{t²}dt
    _x9 = mp.mpf("0.9")
    chk("dawson = e^{−x²}∫₀ˣe^{t²}", mp.sqrt(mp.pi) / 2 * mp.exp(-_x9 ** 2) * mp.erfi(_x9),
        mp.exp(-_x9 ** 2) * mp.quad(lambda t: mp.exp(t ** 2), [0, _x9]), mp.mpf("1e-25"))
    chk("erf(1)=2/√π·∫", mp.erf(1), 2 / mp.sqrt(mp.pi) * mp.quad(lambda t: mp.exp(-t ** 2), [0, 1]),
        mp.mpf("1e-25"))
    chk("arsinh 1 = ln(1+√2)", mp.asinh(1), mp.log(1 + mp.sqrt(2)))
    # riemannZeta: standard values plus Mathlib's explicitly totalized value at the pole.
    chk("ζ(2)=π²/6", _riemann_zeta_mathlib(2), mp.pi ** 2 / 6)
    chk("ζ(−1)=−B₂/2", _riemann_zeta_mathlib(-1), -_bernoulli_mathlib(2) / 2)
    chk("Mathlib ζ(1) totalization", _riemann_zeta_mathlib(1),
        (mp.euler - mp.log(4 * mp.pi)) / 2)
    # LSeries.term — the higher-order Dirichlet-series term (DLMF 25.11 / §27.4). Anchors:
    #  (1) the Mathlib n = 0 junk value (term f s 0 = 0, NOT f(0)/0^s);
    #  (2) the DLMF 25.2.1 DEFINING series ζ(s) = Σ_{n≥1} n^{−s}, summed THROUGH the
    #      binding at real s = 6 and complex s = 6+3i as pure partial sums to N = 400
    #      (|tail| ≤ Σ_{n>400} n^{−6} < 2·10⁻¹⁴ — gate 1e-12; no extrapolator, so the
    #      anchor exercises exactly the binding), tying it to the already-anchored ζ;
    #  (3) the DLMF 27.4.5 Möbius series Σ μ(n) n^{−s} = 1/ζ(s) at s = 6, partial sum to
    #      N = 400 (|μ| ≤ 1, so the same tail bound applies);
    #  (4) a single term at complex s via an INDEPENDENT exp/log evaluation,
    #      term(f, 2+3i, 5) = f(5)·e^{−(2+3i)·ln 5} — pins the (f, s, n) argument order
    #      (any permutation changes the value) and the principal-branch complex power.
    _one = lambda n: mp.mpf(1)
    chk("LSeries.term f s 0 = 0 (Mathlib junk)", _lseries_term(_one, mp.mpf(2), 0), 0)
    chk("Σ term(1,6,n) = ζ(6) (DLMF 25.2.1)",
        mp.fsum(_lseries_term(_one, mp.mpf(6), n) for n in range(1, 401)),
        mp.zeta(6), mp.mpf("1e-12"))
    chk("Σ term(1,6+3i,n) = ζ(6+3i)",
        mp.fsum(_lseries_term(_one, mp.mpc(6, 3), n) for n in range(1, 401)),
        mp.zeta(mp.mpc(6, 3)), mp.mpf("1e-12"))
    chk("Σ term(μ,6,n) = 1/ζ(6) (DLMF 27.4.5)",
        mp.fsum(_lseries_term(lambda m: mp.mpf(_mobius(m)), mp.mpf(6), n) for n in range(1, 401)),
        1 / mp.zeta(6), mp.mpf("1e-12"))
    chk("term arg order/branch: term(f,2+3i,5) = f(5)·e^{−(2+3i)ln5}",
        _lseries_term(lambda m: mp.mpf(3), mp.mpc(2, 3), 5),
        3 * mp.e ** (-mp.mpc(2, 3) * mp.log(5)))
    # L = LSeries (the scoped `L ↗f s` head) — the FULL Dirichlet sum through _lseries.
    # All anchors run THROUGH the binding, which must SETTLE or raise (no extrapolator):
    #  (1) the DLMF 25.2.1 defining series ζ(12) and ζ(12+3i), real and complex s (the
    #      settled-tail window admits σ = 12: partial sums settle by n ≈ 220);
    #  (2) the DLMF 27.4.5 Möbius series L μ s = 1/ζ(s) at s = 12 — the identity the
    #      MobiusMangoldt sweep surface states, mirroring the N = 400, s = 6 partial-sum
    #      anchor (3) of _lseries_term above at a σ the settle window admits;
    #  (3) the guard itself: at s = 2 the tail (~N^{1−σ}) cannot settle within the
    #      4000-term cap — _lseries must RAISE, never return a half-summed value.
    chk("L 1 12 = ζ(12) (DLMF 25.2.1)", _lseries(_one, mp.mpf(12)), mp.zeta(12))
    chk("L 1 (12+3i) = ζ(12+3i)", _lseries(_one, mp.mpc(12, 3)), mp.zeta(mp.mpc(12, 3)))
    chk("L μ 12 = 1/ζ(12) (DLMF 27.4.5)",
        _lseries(lambda m: mp.mpf(_mobius(m)), mp.mpf(12)), 1 / mp.zeta(12))
    try:
        _lseries(_one, mp.mpf(2))
        fails.append("L 1 2: expected the settled-tail guard to raise, got a value")
    except ValueError:
        pass
    # clamped inverse trig: cos(arcsin x)=√(1−x²) holds even at x=1.7 (both sides 0)
    chk("cos(arcsin 1.7)=0 (clamped)", mp.cos(mp.asin(_clamp(mp.mpf("1.7")))), 0)
    chk("arcsin(0.5) normal", mp.asin(_clamp(mp.mpf("0.5"))), mp.asin(mp.mpf("0.5")))
    # principalComplexArcsin (DLMF 15.4.4): −i·log(√(1−z²)+iz) = asin z on the unit disc
    chk("principalComplexArcsin = asin (0.4+0.3i)",
        _principal_complex_arcsin(mp.mpc("0.4", "0.3")), mp.asin(mp.mpc("0.4", "0.3")))
    chk("principalComplexArcsin = asin (−0.6+0.2i)",
        _principal_complex_arcsin(mp.mpc("-0.6", "0.2")), mp.asin(mp.mpc("-0.6", "0.2")))
    # ── M7 / B1: exact Nat-arithmetic helpers, anchored at distinguishing values ──
    chk("totient(0)=0 (Mathlib junk)", _totient(0), 0)
    chk("totient(1)=1", _totient(1), 1)
    chk("totient(12)=4", _totient(12), 4)
    chk("divisors(0)=∅ (Mathlib)", len(_divisors(0)), 0)
    chk("divisors(12) sum=28", sum(_divisors(12)), 28)
    chk("primeFactors(12)={2,3}", sum(_prime_factors(12)), 5)
    chk("mobius(1)=1", _mobius(1), 1)
    chk("mobius(6)=1", _mobius(6), 1)
    chk("mobius(12)=0 (not squarefree)", _mobius(12), 0)
    chk("jordan J₁=φ @ 12", _jordan_totient(1, 12), _totient(12))
    chk("jordan J₂(4)=12", _jordan_totient(2, 4), 12)
    # jordanTotientFn multiplicativity anchors (DLMF 27.3.1 defining relations for the
    # IsMultiplicative conclusion expansion): f(1) = 1 and f(mn) = f(m)·f(n), (m,n) coprime.
    chk("jordanFn J₂(1)=1", _jordan_totient(2, 1), 1)
    chk("jordanFn J₂(3·4)=J₂(3)·J₂(4)", _jordan_totient(2, 12),
        _jordan_totient(2, 3) * _jordan_totient(2, 4))
    chk("jordanFn J₂(3)·J₂(4)=8·12", _jordan_totient(2, 3) * _jordan_totient(2, 4), 96)
    # ── Nat.factorization model (DLMF 27.2.1 n = ∏ p^{a_p}): reconstruction + edge cases ──
    if _factorization(12) != [(2, 2), (3, 1)]:
        fails.append(f"factorization(12): got {_factorization(12)} want [(2,2),(3,1)]")
    if _factorization(1) != [] or _factorization(0) != []:
        fails.append("factorization(0/1): want the empty Finsupp (Mathlib junk/empty)")
    for _fn in (360, 97, 1024):
        _prod = 1
        for _p, _k in _factorization(_fn):
            _prod *= _p ** _k
        chk(f"factorization reconstructs {_fn}", _prod, _fn)
    # ── MULTIPLICATIVE_WITNESSES (the `hf : IsMultiplicative f` instantiation family,
    # φ = totient and μ = moebius): each witness satisfies the DLMF 27.3.1 DEFINING
    # hypothesis clauses (f(1)=1; f(mn)=f(m)f(n) on coprime pairs — including a
    # NON-coprime counter-anchor showing φ is not completely multiplicative, so the
    # family genuinely occupies the 27.3.2 regime), its §27.2 anchor values, and the
    # 27.3.2 factorization product f(n)=∏ f(p^{a_p}) at n=12 and n=30 — validated
    # BEFORE the sweep ever substitutes a ∀-quantified multiplicative binder. ──
    _mwits = {"totient": _totient, "μ": _mobius}
    for _wname in MULTIPLICATIVE_WITNESSES:
        if _wname not in _mwits:
            fails.append(f"multiplicative witness {_wname}: no verify() anchor — do not trust")
            continue
        _ff = _mwits[_wname]
        chk(f"multwit {_wname}(1)=1 (27.3.1 first clause)", _ff(1), 1)
        for _m, _n in ((4, 9), (5, 8), (3, 25), (6, 35)):
            chk(f"multwit {_wname} 27.3.1 f({_m}·{_n})=f({_m})f({_n})",
                _ff(_m * _n), _ff(_m) * _ff(_n))
        for _v in (12, 30):
            _prod = 1
            for _p, _k in _factorization(_v):
                _prod *= _ff(_p ** _k)
            chk(f"multwit {_wname} 27.3.2 product @ {_v}", _ff(_v), _prod)
    chk("multwit φ(12)=4", _totient(12), 4)
    chk("multwit μ(30)=−1", _mobius(30), -1)
    chk("multwit φ NOT completely mult: φ(4)≠φ(2)²", 1 if _totient(4) != _totient(2) ** 2 else 0, 1)
    chk("σ₀(12)=#divisors=6", _divisor_sigma(0, 12), 6)
    chk("σ₁(12)=28", _divisor_sigma(1, 12), 28)
    chk("choose(5,2)=10", _choose(5, 2), 10)
    chk("choose(2,5)=0 (k>n)", _choose(2, 5), 0)
    chk("catalan(0..4)=1,1,2,5,14", sum(_catalan(n) for n in range(5)), 23)
    chk("catalan(4)=14", _catalan(4), 14)
    chk("harmonic(0)=0", _harmonic(0), 0)
    chk("harmonic(4)=25/12", _harmonic(4), mp.mpf(25) / 12)
    # ── M7 / B2: digamma — ψ(1) = −γ and the harmonic ladder ψ(n+1) = Hₙ − γ ──
    chk("ψ(1)=−γ", mp.digamma(1), -mp.euler)
    chk("ψ(5)=H₄−γ", mp.digamma(5), _harmonic(4) - mp.euler)
    # realTrigamma = ψ′ — ψ′(1) = π²/6 (realTrigamma_one); the by-name ψ would give −γ.
    chk("ψ′(1)=π²/6", mp.polygamma(1, 1), mp.pi ** 2 / 6)
    # Weierstrass elementary factor E₂ — E₂(0)=1, E₂(1)=0 (the attached zero).
    chk("E₂(0)=1", (1 - 0) * mp.e ** (0 + 0), 1)
    chk("E₂(1)=0", (1 - 1) * mp.e ** (1 + mp.mpf(1) / 2), 0)
    # ── Class-A bindings ──
    # Complete elliptic K/E: modulus-vs-parameter knob — K(1/√2)=Γ(¼)²/(4√π).
    chk("K(0)=π/2", mp.ellipk(0), mp.pi / 2)
    chk("E(0)=π/2", mp.ellipe(0), mp.pi / 2)
    chk("K(1/√2)=Γ(¼)²/4√π", mp.ellipk(mp.mpf(1) / 2),
        mp.gamma(mp.mpf(1) / 4) ** 2 / (4 * mp.sqrt(mp.pi)))
    # Gegenbauer/Jacobi: pin the ARG ORDER (degree-vs-param) — C₁^(2)(½)=2λx=2,
    # P₁^(2,0)(0)=(α+1)+(α+β+2)(x−1)/2=1.
    chk("C₁^(2)(½)=2", mp.gegenbauer(1, 2, mp.mpf(1) / 2), 2)
    chk("P₁^(2,0)(0)=1", mp.jacobi(1, 2, 0, 0), 1)
    # Hermite He in fn form — He₃(2)=2 (physicists' 40 is the trap).
    chk("He₃(2)=2", _hermite_prob(3, 2), 2)
    # Parabolic cylinder: zero values + evenness/oddness of w₁/w₂.
    _pe = lambda a, x: mp.e ** (-x ** 2 / 4) * _kummerM(a / 2 + mp.mpf(1) / 4, mp.mpf(1) / 2, x ** 2 / 2)
    _po = lambda a, x: x * mp.e ** (-x ** 2 / 4) * _kummerM(a / 2 + mp.mpf(3) / 4, mp.mpf(3) / 2, x ** 2 / 2)
    chk("pcfEven(a,0)=1", _pe(mp.mpf("0.7"), 0), 1)
    chk("pcfOdd(a,0)=0", _po(mp.mpf("0.7"), 0), 0)
    chk("pcfEven even", _pe(mp.mpf("0.5"), mp.mpf("1.3")), _pe(mp.mpf("0.5"), mp.mpf("-1.3")))
    chk("pcfOdd odd", _po(mp.mpf("0.5"), mp.mpf("1.3")), -_po(mp.mpf("0.5"), mp.mpf("-1.3")))
    # Hurwitz ζ(s,a): ζ(2,2)=π²/6−1 distinguishes it from the plain ζ(s)=ζ(s,1).
    chk("ζ(2,1)=π²/6", mp.zeta(2, 1), mp.pi ** 2 / 6)
    chk("ζ(2,2)=π²/6−1", mp.zeta(2, 2), mp.pi ** 2 / 6 - 1)
    # cot — cot(π/4)=1.
    chk("cot(π/4)=1", mp.cot(mp.pi / 4), 1)
    # Lerch Φ: Φ(1,2,1)=ζ(2,1)=π²/6 ; Φ(½,1,1)=−log(½)/½.
    chk("Φ(1,2,1)=π²/6", mp.lerchphi(1, 2, 1), mp.pi ** 2 / 6)
    chk("Φ(½,1,1)=−2log½", mp.lerchphi(mp.mpf(1) / 2, 1, 1), -mp.log(mp.mpf(1) / 2) * 2)
    # asyCoeff Pₙ(a): P₁(a)=a−1 ; P₂(5)=4·3=12.
    chk("P₁(a)=a−1", _asy_coeff(mp.mpf("3.3"), 1), mp.mpf("3.3") - 1)
    chk("P₂(5)=12", _asy_coeff(5, 2), 12)
    # Stirling 2nd kind, falling factorial, and the discrete OPs (arg-order/normalization).
    chk("⟨3,1⟩=4", _eulerian(3, 1), 4)
    chk("⟨4,1⟩=11", _eulerian(4, 1), 11)
    chk("Σ⟨4,k⟩=4!", sum(_eulerian(4, k) for k in range(5)), 24)
    chk("rbinom(5,2)=10", _falling(5, 2) / mp.factorial(2), 10)
    chk("besselY_{1/2}(1.5)", mp.bessely(mp.mpf(1) / 2, mp.mpf("1.5")),
        -mp.sqrt(2 / (mp.pi * mp.mpf("1.5"))) * mp.cos(mp.mpf("1.5")))
    chk("struveK_{1/2}(2)=√(1/π)", mp.struveh(mp.mpf(1) / 2, 2) - mp.bessely(mp.mpf(1) / 2, 2),
        mp.sqrt(2 / (mp.pi * 2)))
    chk("S(4,2)=7", _stirling2(4, 2), 7)
    chk("S(5,3)=25", _stirling2(5, 3), 25)
    chk("J_{1/2}(1.5)", mp.besselj(mp.mpf(1) / 2, mp.mpf("1.5")),
        mp.sqrt(2 / (mp.pi * mp.mpf("1.5"))) * mp.sin(mp.mpf("1.5")))
    chk("struveHReduced(½,.7) vs struveh", mp.hyper([1], [mp.mpf(3) / 2, mp.mpf(2)], -mp.mpf("0.7"))
        / (mp.gamma(mp.mpf(3) / 2) * mp.gamma(mp.mpf(2))),
        mp.struveh(mp.mpf(1) / 2, 2 * mp.sqrt(mp.mpf("0.7"))) / mp.sqrt(mp.mpf("0.7")) ** mp.mpf("1.5"))
    chk("struveInhom(½)=1/√π", 1 / (mp.sqrt(mp.pi) * mp.gamma(mp.mpf(2))), 1 / mp.sqrt(mp.pi))
    chk("μ(6)=1", _mobius(6), 1)
    chk("μ(2)=−1", _mobius(2), -1)
    chk("λ(12)=−1", _liouville(12), -1)
    chk("λ(4)=1", _liouville(4), 1)
    # λ as the ∀-witness for `IsCompletelyMultiplicative f` surfaces (fidelity_extract
    # `_fnwitness`, DLMF 27.3.9/27.3.10): anchor EVERY hypothesis clause before the
    # witness is trusted — λ(1)=1 and full multiplicativity λ(mn)=λ(m)λ(n) on non-coprime
    # pairs too (6·4 shares the factor 2; 12·18 both composite), plus the junk-value
    # coherence λ(0)=0 matching Lean's `ArithmeticFunction` f(0)=0.
    chk("λ(1)=1 (27.3.9 first clause)", _liouville(1), 1)
    chk("λ(6·4)=λ(6)λ(4) (non-coprime)", _liouville(24), _liouville(6) * _liouville(4))
    chk("λ(12·18)=λ(12)λ(18)", _liouville(216), _liouville(12) * _liouville(18))
    chk("λ(0)=0 (ArithmeticFunction junk)", _liouville(0), 0)
    # and the DLMF 27.3.10 prime-power kernel at the witness: λ(2⁵)=λ(2)⁵, λ(9)=λ(3)².
    chk("λ(2⁵)=λ(2)⁵", _liouville(32), _liouville(2) ** 5)
    chk("λ(3²)=λ(3)²", _liouville(9), _liouville(3) ** 2)
    chk("s(1,5)=1/5", _dedekind_sum(1, 5), mp.mpf(1) / 5)        # s(1,k)=(k−1)(k−2)/(12k)
    chk("s(1,6)=5/18", _dedekind_sum(1, 6), mp.mpf(5) / 18)
    # Dedekind sawtooth ((x)) (DLMF 27.14 defining formula): value off ℤ, the zero on ℤ
    # (incl. a negative integer — the ⌊·⌋ branch that a truncation bug would break),
    # oddness ((−x)) = −((x)) at a non-integer, and consistency with the exact rational
    # kernel _sawtooth_rat that _dedekind_sum sums over.
    chk("((1/3))=-1/6", _sawtooth(mp.mpf(1) / 3), mp.mpf(-1) / 6)
    chk("((7))=0", _sawtooth(mp.mpf(7)), 0)
    chk("((-3))=0", _sawtooth(mp.mpf(-3)), 0)
    chk("((-1/4))=1/4 (oddness)", _sawtooth(mp.mpf(-1) / 4), -_sawtooth(mp.mpf(1) / 4))
    chk("((2/5))=_sawtooth_rat(2,5)", _sawtooth(mp.mpf(2) / 5), _sawtooth_rat(2, 5))
    # Ramanujan sum c_q(n) — the binding computes the DLMF 27.10.1 Hölder/divisor form;
    # anchor it against the DECORRELATED exponential-sum DEFINITION 27.10.2,
    # c_k(n) = Σ_{h:(h,k)=1, 1≤h≤k} e^{2πihn/k}, on a grid that includes gcd(k,n) > 1
    # samples (where the two forms could genuinely disagree if either were mis-coded),
    # plus the special values c_1(n)=1 (the theorem under test), c_q(1)=μ(q), the prime
    # dichotomy c_p(n)=p−1 (p∣n) / −1 (p∤n), and the q=0 junk value matching Lean.
    def _c_exp(k, n):
        from math import gcd
        return mp.fsum(mp.e ** (2 * mp.pi * mp.j * h * n / k)
                       for h in range(1, k + 1) if gcd(h, k) == 1)
    for _rsk, _rsn in ((1, 7), (2, 3), (4, 10), (6, 3), (9, 3), (10, 4), (12, 8), (7, 5)):
        chk(f"c_{_rsk}({_rsn}) 27.10.1 = 27.10.2 exp sum",
            mp.mpf(_ramanujan_sum(_rsk, _rsn)), _c_exp(_rsk, _rsn), mp.mpf("1e-20"))
    chk("c_1(997)=1", _ramanujan_sum(1, 997), 1)
    chk("c_12(1)=μ(12)", _ramanujan_sum(12, 1), _mobius(12))
    chk("c_5(10)=4 (p∣n: p−1)", _ramanujan_sum(5, 10), 4)
    chk("c_5(7)=−1 (p∤n: −1)", _ramanujan_sum(5, 7), -1)
    chk("c_0(6)=0 (μ(0)=0 junk, matches Lean)", _ramanujan_sum(0, 6), 0)
    chk("[3,1]_2=7", _qbinom(2, 3, 1), 7)
    chk("[4,2]_2=35", _qbinom(2, 4, 2), 35)
    chk("c(4,2)=11", _stirling1u(4, 2), 11)
    chk("c(5,2)=50", _stirling1u(5, 2), 50)
    chk("Ein(1)=γ+E₁(1)", mp.quad(lambda t: (1 - mp.e ** (-t)) / t if t != 0 else mp.mpf(1),
                                  [0, 1]), mp.euler + mp.e1(1))
    # eiSeries(−1) = Σ(−1)ⁿ/(n·n!) cross-checked against E1(1) = −γ − eiSeries(−1).
    chk("eiSeries(−1)=−γ−E1(1)", mp.nsum(lambda n: (-1) ** n / (n * mp.factorial(n)), [1, mp.inf]),
        -mp.euler - mp.e1(1))
    # liW(x)=x²·E₁(ln x) — cross-check against the literal integral def at x=3.
    chk("liW(3)=∫ def", mp.mpf(3) ** 2 * mp.e1(mp.log(3)),
        3 * mp.quad(lambda u: mp.e ** (-(mp.log(3)) * u) / (1 + u), [0, mp.inf]))
    chk("ff(5,3)=60", _falling(5, 3), 60)
    # fallingFactorial (FLMF function form, arg order (n, x)): the DLMF 5.2 product at a
    # NON-integer point — (0.7)₂ = 0.7·(−0.3) = −0.21, where the RISING factorial gives
    # 0.7·1.7 = +1.19 (the falling-vs-rising trap) — the reflection (x)ₙ = (−1)ⁿ(−x)⁽ⁿ⁾
    # against mp.rf (independent implementation), Nat.descFactorial agreement, and (x)₀=1.
    _ffb = REGISTRY["fallingFactorial"][1]
    chk("fallingFactorial(2,0.7)=−0.21 (falling, not rising +1.19)",
        _ffb(2, mp.mpf("0.7")), mp.mpf("-0.21"))
    chk("fallingFactorial reflection (1.3)₃=(−1)³·rf(−1.3,3)",
        _ffb(3, mp.mpf("1.3")), (-1) ** 3 * mp.rf(mp.mpf("-1.3"), 3))
    chk("fallingFactorial(3,5)=descFactorial=60", _ffb(3, 5), 60)
    chk("fallingFactorial(0,2.4)=1", _ffb(0, mp.mpf("2.4")), 1)
    chk("charlier C₁(2;3)=1/3", mp.hyper([-1, -2], [], -mp.mpf(1) / 3), mp.mpf(1) / 3)
    chk("krawtchouk K₁(1;½,4)=½", mp.hyp2f1(-1, -1, -4, 2), mp.mpf(1) / 2)
    chk("meixner M₁(2;3,2)=4/3", mp.hyp2f1(-1, -2, 3, mp.mpf(1) / 2), mp.mpf(4) / 3)
    # ── Continuous Hahn pₙ(x;a,b,c,d): anchored to the DLMF §18.20 normalization p₀ = 1
    # and the symbolic degree-one value p₁ = (a+b+c+d)x + i(cd−ab) at two ASYMMETRIC
    # parameter points (a,b,c,d pairwise distinct pins the {a,·}-Pochhammer grouping and
    # the x-slot), plus the a↔b symmetry of the family — the weight
    # Γ(a+ix)Γ(b+ix)Γ(c−ix)Γ(d−ix) and leading coefficient are a↔b symmetric, so
    # pₙ(x;a,b,c,d) = pₙ(x;b,a,c,d), an identity INVISIBLE in the asymmetric ₃F₂ series
    # the binding computes with. ──
    _chp1 = lambda a, b, c, d, x: (a + b + c + d) * x + mp.mpc(0, 1) * (c * d - a * b)
    _chpt1 = (mp.mpf('0.3'), mp.mpf('1.2'), mp.mpf('-0.4'), mp.mpf('2.1'), mp.mpf('0.7'))
    _chpt2 = (mp.mpf('1.5'), mp.mpf('0.2'), mp.mpf('0.9'), mp.mpf('-0.3'), mp.mpf('-1.8'))
    for _a, _b, _c, _d, _x in (_chpt1, _chpt2):
        chk("continuousHahn p₀=1", _continuous_hahn(_a, _b, _c, _d, 0, _x), 1, tol=mp.mpf("1e-25"))
        chk("continuousHahn p₁=(a+b+c+d)x+i(cd−ab)",
            _continuous_hahn(_a, _b, _c, _d, 1, _x), _chp1(_a, _b, _c, _d, _x),
            tol=mp.mpf("1e-25"))
    chk("continuousHahn a↔b symmetry n=3",
        _continuous_hahn(*_chpt1[:4], 3, _chpt1[4]),
        _continuous_hahn(_chpt1[1], _chpt1[0], _chpt1[2], _chpt1[3], 3, _chpt1[4]),
        tol=mp.mpf("1e-25"))
    # ── Dual Hahn Rₙ(λ(x);γ,δ,N): anchored to the DLMF 18.22 / KLS 1.6.2 DEFINING
    # three-term recurrence λ(x)·Rₙ = Aₙ·R_{n+1} − (Aₙ+Cₙ)·Rₙ + Cₙ·R_{n−1},
    # Aₙ = (n+γ+1)(n−N), Cₙ = n(n−δ−N−1), λ(x) = x(x+γ+δ+1), built independently
    # UPWARD from R₀ = 1 (whence R₁ = 1 − λ/((γ+1)N) at n = 0, C₀ = 0) and compared
    # against the ₃F₂ binding at n = 0..5 on two γ ≠ δ parameter points (asymmetry
    # pins the (γ,δ,N,n,x) argument order — swapping γ↔δ changes A₁ but not λ);
    # plus the lattice-origin normalization Rₙ(λ(0)) = 1 for every n and the
    # hand-computed degree-one value R₁(λ(2); ½, 3/10, 5) = 1 − 2·(19/5)/(15/2)
    # = −1/75. ──
    for _dhg, _dhd, _dhN, _dhx in ((mp.mpf("0.5"), mp.mpf("0.3"), 6, mp.mpf("1.7")),
                                   (mp.mpf("1.2"), mp.mpf("-0.4"), 7, mp.mpf("3.1"))):
        _dhlam = _dhx * (_dhx + _dhg + _dhd + 1)
        _dhrec = [mp.mpf(1), 1 - _dhlam / ((_dhg + 1) * _dhN)]  # the 1.6.2 initial data
        for _dhn in range(1, 5):                   # R_{n+1} from the defining recurrence
            _dhA = (_dhn + _dhg + 1) * (_dhn - _dhN)
            _dhC = _dhn * (_dhn - _dhd - _dhN - 1)
            _dhrec.append(((_dhlam + _dhA + _dhC) * _dhrec[_dhn]
                           - _dhC * _dhrec[_dhn - 1]) / _dhA)
        for _dhn in range(6):
            chk(f"dualHahn Rₙ = 18.22 recurrence @ n={_dhn}, γ={_dhg}",
                _dual_hahn(_dhg, _dhd, _dhN, _dhn, _dhx), _dhrec[_dhn], mp.mpf("1e-22"))
        # dhA/dhCC coefficient bindings (DualHahn.lean's A_{n+1}, C_{n+1}): (a) they
        # reproduce the SAME 18.22/KLS 1.6.2 coefficients the anchored upward
        # recurrence above was built with (index shift n ↦ n+1: dhA γ N n = A_{n+1});
        # (b) they play the DEFINING recurrence role λ(x)·R_{n+1} = A_{n+1}·R_{n+2}
        # − (A_{n+1}+C_{n+1})·R_{n+1} + C_{n+1}·Rₙ against the ₃F₂ binding values.
        for _dhn in range(1, 5):
            chk(f"dhA = 18.22 A_n @ n={_dhn}, γ={_dhg}",
                _dh_A(_dhg, _dhN, _dhn - 1), (_dhn + _dhg + 1) * (_dhn - _dhN))
            chk(f"dhCC = 18.22 C_n @ n={_dhn}, γ={_dhg}",
                _dh_CC(_dhd, _dhN, _dhn - 1), _dhn * (_dhn - _dhd - _dhN - 1))
        for _dhn in range(4):
            _dhAn, _dhCn = _dh_A(_dhg, _dhN, _dhn), _dh_CC(_dhd, _dhN, _dhn)
            chk(f"dhA/dhCC recurrence role @ n={_dhn}, γ={_dhg}",
                _dhlam * _dhrec[_dhn + 1],
                _dhAn * _dhrec[_dhn + 2] - (_dhAn + _dhCn) * _dhrec[_dhn + 1]
                + _dhCn * _dhrec[_dhn], mp.mpf("1e-20"))
    chk("dualHahn R₄(λ(0))=1", _dual_hahn(mp.mpf("0.5"), mp.mpf("0.3"), 5, 4, mp.mpf(0)), 1)
    chk("dualHahn R₁(λ(2);½,3/10,5)=−1/75",
        _dual_hahn(mp.mpf("0.5"), mp.mpf("0.3"), 5, 1, mp.mpf(2)), -mp.mpf(1) / 75)
    # ── Meixner–Pollaczek Pₙ^{(λ)}(x;φ): anchored to the DLMF §18.9 / KLS 9.7.3
    # DEFINING three-term recurrence
    # (n+1)·P_{n+1} = 2[x sinφ + (n+λ)cosφ]·Pₙ − (n+2λ−1)·P_{n−1},
    # built independently UPWARD from P₀ = 1 and the hand degree-one value
    # P₁ = 2(λcosφ + x sinφ), compared against the ₂F₁ binding at n = 0..5 on two
    # asymmetric parameter points (λ ≠ x and φ off the symmetry points pin the
    # (λ,φ,n,x) argument order: swapping λ↔x changes P₁ unless cosφ=sinφ), plus the
    # realness of the ℂ-routed value (Im P₃ = 0 for real λ,φ,x — a nontrivial
    # cancellation between e^{inφ} and the complex ₂F₁ argument λ+ix). ──
    for _mpl, _mpphi, _mpx in ((mp.mpf("0.7"), mp.mpf("0.9"), mp.mpf("1.3")),
                               (mp.mpf("2.5"), mp.mpf("-1.2"), mp.mpf("0.4"))):
        _mprec = [mp.mpf(1), 2 * (_mpl * mp.cos(_mpphi) + _mpx * mp.sin(_mpphi))]
        for _mpn in range(1, 5):               # P_{n+1} from the defining recurrence
            _mprec.append((2 * (_mpx * mp.sin(_mpphi) + (_mpn + _mpl) * mp.cos(_mpphi))
                           * _mprec[_mpn]
                           - (_mpn + 2 * _mpl - 1) * _mprec[_mpn - 1]) / (_mpn + 1))
        for _mpn in range(6):
            chk(f"meixnerPollaczek Pₙ = 18.9 recurrence @ n={_mpn}, λ={_mpl}",
                _meixner_pollaczek(_mpl, _mpphi, _mpn, _mpx), _mprec[_mpn],
                mp.mpf("1e-20"))
        chk(f"meixnerPollaczek Im P₃ = 0 @ λ={_mpl}",
            mp.im(_meixner_pollaczek(_mpl, _mpphi, 3, _mpx)), 0, mp.mpf("1e-20"))
    # q-Pochhammer (a;q)₂=(1−a)(1−aq).
    chk("(3/10;1/2)₂", mp.qp(mp.mpf(3) / 10, mp.mpf(1) / 2, 2),
        (1 - mp.mpf(3) / 10) * (1 - mp.mpf(3) / 10 * mp.mpf(1) / 2))
    # ── Al-Salam–Chihara Qₙ(x;a,b|q): anchored to the DLMF §18.28 / KLS 14.8.4 DEFINING
    # three-term recurrence 2x·Qₙ = Q_{n+1} + (a+b)qⁿ·Qₙ + (1−qⁿ)(1−ab·q^{n−1})·Q_{n−1}
    # with initial data Q₀ = 1 (whence Q₁ = 2x − (a+b) at n = 0), built independently
    # UPWARD from that data and compared against the ₃φ₂-series binding at n = 0..4 on
    # two asymmetric parameter points (a ≠ b pins the (a,b,q,n,x) argument order; the
    # second point has q < 0, off the classical 0<q<1 grid); plus the a↔b symmetry of
    # the family, which the asymmetric series form does not display. ──
    _ascQ = _al_salam_chihara
    for _pa, _pb, _pq, _px in ((mp.mpf("0.7"), mp.mpf("-0.4"), mp.mpf("0.5"), mp.mpf("1.3")),
                               (mp.mpf("-1.2"), mp.mpf("0.3"), mp.mpf("-0.6"), mp.mpf("0.2"))):
        _r0, _r1 = mp.mpf(1), 2 * _px - (_pa + _pb)   # the 14.8.4 initial data
        _rec = [_r0, _r1]
        for _pn in range(1, 4):                        # R_{n+1} from the defining recurrence
            _rec.append((2 * _px - (_pa + _pb) * _pq ** _pn) * _rec[_pn]
                        - (1 - _pq ** _pn) * (1 - _pa * _pb * _pq ** (_pn - 1)) * _rec[_pn - 1])
        for _pn in range(5):
            chk(f"ASC Qₙ = 14.8.4 recurrence @ n={_pn}, a={_pa}",
                _ascQ(_pa, _pb, _pq, _pn, _px), _rec[_pn], mp.mpf("1e-22"))
        chk(f"ASC a↔b symmetry @ n=3, a={_pa}",
            _ascQ(_pa, _pb, _pq, 3, _px), _ascQ(_pb, _pa, _pq, 3, _px), mp.mpf("1e-22"))
    # ascFactor: the conjugate q-Pochhammer pair (ae^{iθ};q)_k(ae^{−iθ};q)_k at x = cos θ,
    # through mp.qp at COMPLEX argument (decorrelated path), plus the k=1 closed form.
    _th = mp.mpf("0.9")
    chk("ascFactor = (ae^{iθ};q)₃(ae^{−iθ};q)₃ @ x=cosθ",
        _asc_factor(mp.mpf("0.7"), mp.mpf("0.5"), 3, mp.cos(_th)),
        mp.qp(mp.mpf("0.7") * mp.exp(mp.mpc(0, 1) * _th), mp.mpf("0.5"), 3)
        * mp.qp(mp.mpf("0.7") * mp.exp(-mp.mpc(0, 1) * _th), mp.mpf("0.5"), 3), mp.mpf("1e-22"))
    chk("ascFactor k=1 = 1−2ax+a²", _asc_factor(mp.mpf("0.7"), mp.mpf("0.5"), 1, mp.mpf("1.3")),
        1 - 2 * mp.mpf("0.7") * mp.mpf("1.3") + mp.mpf("0.7") ** 2)
    # Bell numbers and von Mangoldt.
    chk("B₅=52", _bell(5), 52)
    chk("B₆=203", _bell(6), 203)
    chk("Λ(8)=log2", _von_mangoldt(8), mp.log(2))
    chk("Λ(6)=0", _von_mangoldt(6), 0)
    chk("Λ(7)=log7", _von_mangoldt(7), mp.log(7))
    # Chebyshev ψ(x) = Σ_{n≤x} Λ(n) (DLMF 27.2.11): hand-computable prime-power sums,
    # the decorrelated lcm characterization e^{ψ(n)} = lcm(1..n) (ψ(10) = log 2520 with
    # 2520 = 2³·3²·5·7 = lcm(1..10)), and the Nat.floor step behaviour at non-integer x.
    chk("ψ(1.9)=0 (empty sum)", _chebyshev_psi(mp.mpf("1.9")), 0)
    chk("ψ(2)=log2", _chebyshev_psi(mp.mpf(2)), mp.log(2))
    chk("ψ(10)=3log2+2log3+log5+log7",
        _chebyshev_psi(mp.mpf(10)),
        3 * mp.log(2) + 2 * mp.log(3) + mp.log(5) + mp.log(7))
    chk("ψ(10)=log lcm(1..10)=log 2520", _chebyshev_psi(mp.mpf(10)), mp.log(2520))
    chk("ψ(10.7)=ψ(10) (floor step)", _chebyshev_psi(mp.mpf("10.7")),
        _chebyshev_psi(mp.mpf(10)))
    chk("ψ(−3)=0 (Nat.floor clamps)", _chebyshev_psi(mp.mpf(-3)), 0)
    # Chebyshev ϑ(x) = Σ_{p≤x} log p (DLMF 27.2.11): hand-computable prime-log sums —
    # ϑ(10) = log(2·3·5·7) = log 210 (primorial 10# = 210), ϑ distinguishes itself from
    # ψ at the first prime power (ϑ(4) = log 2 ≠ ψ(4) = 2 log 2) — plus the Nat.floor
    # step/clamp behaviour, and the isprime helper at the distinguishing points 1 (not
    # prime), 2 (the even prime), 9 (odd composite).
    chk("ϑ(1.9)=0 (empty sum)", _chebyshev_theta(mp.mpf("1.9")), 0)
    chk("ϑ(2)=log2", _chebyshev_theta(mp.mpf(2)), mp.log(2))
    chk("ϑ(10)=log 210 (primorial)", _chebyshev_theta(mp.mpf(10)), mp.log(210))
    chk("ϑ(4)=log6 (prime powers excluded: ≠ψ(4)=log12)",
        _chebyshev_theta(mp.mpf(4)), mp.log(6))
    chk("ϑ(10.7)=ϑ(10) (floor step)", _chebyshev_theta(mp.mpf("10.7")),
        _chebyshev_theta(mp.mpf(10)))
    chk("ϑ(−3)=0 (Nat.floor clamps)", _chebyshev_theta(mp.mpf(-3)), 0)
    chk("isprime: 1 no, 2 yes, 9 no",
        mp.mpf(1) if (not _isprime(1)) and _isprime(2) and not _isprime(9) else mp.mpf(0),
        1)
    # Gauss sum (DLMF 20.11.1) — hand-computable values of the DEFINING sum, in the DLMF
    # −πi phase (the 2πi convention fails all three), plus the 20.11.2 reciprocity identity
    # at an admissible point (m,n) = (3,4): coprime, mn even.
    chk("gaussSum G(1,2)=1−i", _gauss_sum(1, 2), mp.mpc(1, -1), mp.mpf("1e-25"))
    chk("gaussSum G(−2,1)=1", _gauss_sum(-2, 1), 1, mp.mpf("1e-25"))
    chk("gaussSum G(1,4)=√2(1−i)", _gauss_sum(1, 4), mp.sqrt(2) * mp.mpc(1, -1), mp.mpf("1e-25"))
    chk("gaussSum reciprocity @ (3,4)", _gauss_sum(3, 4) / mp.sqrt(4),
        mp.exp(-mp.pi * mp.j / 4) * _gauss_sum(-4, 3) / mp.sqrt(3), mp.mpf("1e-25"))
    # ── M7 / B2: theta nulls — anchored against the LEAN DEFINING FORMULAS, using
    # jacobiTheta₂ z τ = Σ e^{2πinz+iπn²τ} = jtheta(3, πz, q): the strongest §5 tie. ──
    _tz, _tt = mp.mpc("0.23", "0.11"), mp.mpc("0.5", "0.8")
    _tq = _theta_q(_tt)
    _jt2 = lambda z: mp.jtheta(3, mp.pi * z, _tq)          # ≡ Mathlib jacobiTheta₂ · τ
    chk("θ₃ = jacobiTheta₂", _theta(3)(_tz, _tt), _jt2(_tz), mp.mpf("1e-25"))
    chk("θ₄ z = jacobiTheta₂ (z+1/2)", _theta(4)(_tz, _tt), _jt2(_tz + mp.mpf(1) / 2), mp.mpf("1e-25"))
    chk("θ₂ z = e^{iπ(τ/4+z)}·jacobiTheta₂ (z+τ/2)", _theta(2)(_tz, _tt),
        mp.exp(mp.pi * mp.mpc(0, 1) * (_tt / 4 + _tz)) * _jt2(_tz + _tt / 2), mp.mpf("1e-25"))
    chk("θ₁ z = −i·e^{iπ(τ/4+z)}·jacobiTheta₂ (z+τ/2+1/2)", _theta(1)(_tz, _tt),
        -mp.mpc(0, 1) * mp.exp(mp.pi * mp.mpc(0, 1) * (_tt / 4 + _tz)) * _jt2(_tz + _tt / 2 + mp.mpf(1) / 2),
        mp.mpf("1e-25"))
    # ── Jacobi imaginary transformation DLMF 20.7.30–20.7.33 (the small-Im τ
    # branch of `_theta`): at Im τ = 0.03 < _THETA_IM_TAU_MIN the wrapper takes
    # the τ ↦ −1/τ route, while `_theta_core` still converges directly
    # (|q| = e^{−0.03π} ≈ 0.91) — the two must agree for all four θⱼ (Re τ ≠ 0
    # also exercises the θ₁/θ₂ q^{1/4} branch knob at the transformed −1/τ). ──
    _mz, _mt = mp.mpc("0.23", "0.011"), mp.mpc("0.13", "0.03")
    for _mj in (1, 2, 3, 4):
        with mp.workdps(2 * mp.mp.dps):
            _mdirect = _theta_core(_mj, _mz, _mt)
        chk(f"θ{_mj} imaginary transform 20.7(viii) @ τ=0.13+0.03i",
            _theta(_mj)(_mz, _mt), _mdirect, mp.mpf("1e-25"))
    # ── Theta lattice-Laplace transform `_theta_lattice_laplace` (DLMF 20.10.4/5):
    # two anchors that DO NOT quote the DLMF closed form. (i) INDEPENDENCE — the
    # heat-kernel lattice sum equals the DIRECT q-series termwise Laplace
    # Σ_{n∈ℤ} e^{2πinz₀}/(s+π²n²/ℓ²) (a different series representation of the same
    # integral; slowly ~1/n²-convergent, so a loose gate) at a REAL-β point; this
    # certifies the sum is the raw integral value, not the RHS. (ii) HIGH-PRECISION
    # binding correctness — the four θⱼ (with their σ/ε/c signs) reproduce the
    # numerically-validated corrected closed forms of 20.10.4/5, including the
    # docstring datum θ₁-integral = +0.217472200401278… at (s,ℓ,β)=(1.3,1.5,0.4), and
    # a COMPLEX-β point (the case the generic quad OOM-killed). ──
    _lls, _lll, _llb = mp.mpf("1.3"), mp.mpf("1.5"), mp.mpf("0.4")
    _llz3 = (_lll + _llb) / (2 * _lll)
    with mp.workdps(2 * mp.mp.dps):
        _lldirect = mp.fsum(mp.exp(2 * mp.pi * mp.mpc(0, 1) * _n * _llz3)
                            / (_lls + mp.pi ** 2 * _n * _n / _lll ** 2)
                            for _n in range(-12000, 12001))
    chk("θ₃ lattice-Laplace = direct q-series termwise Laplace (real β)",
        _theta_lattice_laplace(3, _llz3, _lls, _lll), _lldirect, mp.mpf("1e-8"))
    _llrs = mp.sqrt(_lls)
    _llsinh = _lll / _llrs * mp.sinh(_llb * _llrs) / mp.cosh(_lll * _llrs)   # 20.10.4 θ₁ RHS
    _llcosh = _lll / _llrs * mp.cosh(_llb * _llrs) / mp.sinh(_lll * _llrs)   # 20.10.5 θ₃/θ₄ RHS
    chk("θ₁ lattice-Laplace = +(ℓ/√s)sinh(β√s)sech(ℓ√s) (20.10.4, real β)",
        _theta_lattice_laplace(1, _llb / (2 * _lll), _lls, _lll), _llsinh, mp.mpf("1e-25"))
    chk("θ₂ lattice-Laplace = −(ℓ/√s)sinh(β√s)sech(ℓ√s) (20.10.4, real β)",
        _theta_lattice_laplace(2, _llz3, _lls, _lll), -_llsinh, mp.mpf("1e-25"))
    chk("θ₃ lattice-Laplace = (ℓ/√s)cosh(β√s)csch(ℓ√s) (20.10.5, real β)",
        _theta_lattice_laplace(3, _llz3, _lls, _lll), _llcosh, mp.mpf("1e-25"))
    chk("θ₄ lattice-Laplace = (ℓ/√s)cosh(β√s)csch(ℓ√s) (20.10.5, real β)",
        _theta_lattice_laplace(4, _llb / (2 * _lll), _lls, _lll), _llcosh, mp.mpf("1e-25"))
    _llbc, _llsc = mp.mpc("0.3", "0.2"), mp.mpc("1.1", "0.7")     # complex β, complex s
    _llrsc = mp.sqrt(_llsc)
    chk("θ₁ lattice-Laplace = +(ℓ/√s)sinh(β√s)sech(ℓ√s) (20.10.4, complex β)",
        _theta_lattice_laplace(1, _llbc / (2 * _lll), _llsc, _lll),
        _lll / _llrsc * mp.sinh(_llbc * _llrsc) / mp.cosh(_lll * _llrsc), mp.mpf("1e-25"))
    chk("θ₄ lattice-Laplace = (ℓ/√s)cosh(β√s)csch(ℓ√s) (20.10.5, complex β)",
        _theta_lattice_laplace(4, _llbc / (2 * _lll), _llsc, _lll),
        _lll / _llrsc * mp.cosh(_llbc * _llrsc) / mp.sinh(_lll * _llrsc), mp.mpf("1e-25"))
    # Mellin-grid regime τ = ix², x → 0⁺ (20.10.1–20.10.3 sampling; the direct
    # nome hits jtheta's |q| → 1 wall): θ₃(0|ix²) = x⁻¹θ₃(0|i/x²) = x⁻¹(1 + O(e^{−π/x²})),
    # so x·θ₃(0|ix²) = 1 to ~e^{−π·10¹²} — far below any working precision.
    chk("θ₃(0|ix²)·x = 1 @ x=1e-6", mp.mpf("1e-6") * _theta(3)(0, mp.mpc(0, 1) * mp.mpf("1e-12")),
        1, mp.mpf("1e-25"))
    chk("θ₂(0|ix²)·x = 1 @ x=1e-6", mp.mpf("1e-6") * _theta(2)(0, mp.mpc(0, 1) * mp.mpf("1e-12")),
        1, mp.mpf("1e-25"))
    # heat equation (DLMF 20.4):  ∂²_z θ₃ = 4πi · ∂_τ θ₃, with the bindings used by the oracle
    _dz, _dtau = REGISTRY["jacobiTheta₂'"][1], REGISTRY["jacobiTheta₂_snd"][1]
    chk("θ heat eq: θ_zz = 4πi·θ_τ", mp.diff(lambda z: _dz(z, _tt), _tz),
        4 * mp.pi * mp.mpc(0, 1) * _dtau(_tz, _tt), mp.mpf("1e-7"))
    # ── Ramanujan theta f(a,b) (DLMF 20.11.3) — two anchors: the 20.11.4 θ₃ tie
    # (FLMF normalization z_DLMF = πz: f(q·e^{2πiz}, q·e^{−2πiz}) = jacobiTheta₂ z τ)
    # and the INDEPENDENT Jacobi triple product f(a,b) = (−a;ab)∞(−b;ab)∞(ab;ab)∞
    # (incl. a point with |a| > 1, |ab| < 1 — exercises the asymmetric-wing regime). ──
    _rf = REGISTRY["ramanujanTheta"][1]
    _rq = _theta_q(_tt)
    chk("ramanujanTheta 20.11.4: f(qe^{2πiz},qe^{−2πiz}) = θ₃ z τ",
        _rf(_rq * mp.exp(2 * mp.pi * mp.mpc(0, 1) * _tz), _rq * mp.exp(-2 * mp.pi * mp.mpc(0, 1) * _tz)),
        _theta(3)(_tz, _tt), mp.mpf("1e-25"))
    chk("ramanujanTheta triple product @ (0.3, 0.2)",
        _rf(mp.mpf("0.3"), mp.mpf("0.2")),
        mp.qp(mp.mpf("-0.3"), mp.mpf("0.06")) * mp.qp(mp.mpf("-0.2"), mp.mpf("0.06"))
        * mp.qp(mp.mpf("0.06"), mp.mpf("0.06")), mp.mpf("1e-25"))
    _ra, _rb = mp.mpf("2.5"), mp.mpf("0.1")     # |a|>1, |ab|=0.25<1
    chk("ramanujanTheta triple product @ (2.5, 0.1)",
        _rf(_ra, _rb),
        mp.qp(-_ra, _ra * _rb) * mp.qp(-_rb, _ra * _rb) * mp.qp(_ra * _rb, _ra * _rb),
        mp.mpf("1e-25"))
    # ── combined theta functions φ_{m,n} (DLMF 20.11.6–20.11.8;
    # combinedTheta m n z τ = φ_{m,n}(πz, e^{iπτ})).  Four anchor layers: (i) the
    # derivative-convention knob via the 20.4.6 null θ₁′(0,q) = θ₂(0,q)θ₃(0,q)θ₄(0,q);
    # (ii) Lean-def replay through the INDEPENDENT `_theta` path (argument
    # reduction + q^{1/4} branch correction + π⁻¹·finite-difference deriv), one
    # chk per (m,n) regime of the def; (iii) the z→0 normalization
    # πz·φ_{2,1}(z,τ) → 1 (θ₁(w) ~ θ₁′(0,q)·w — pins the w = πz knob); (iv) the
    # DLMF 22.2.4 Jacobi tie θ₃²(0,q)·φ_{1,4}(z,τ) = sn(πz·θ₃²(0,q), k),
    # k² = (θ₂/θ₃)⁴(0,q), with sn from mpmath's ellipfun (a non-jtheta path). ──
    _cf = REGISTRY["combinedTheta"][1]
    _cq = _theta_q(_tt)
    chk("combinedTheta 20.4.6 null θ₁′(0,q)=θ₂θ₃θ₄(0,q)",
        mp.jtheta(1, 0, _cq, derivative=1),
        mp.jtheta(2, 0, _cq) * mp.jtheta(3, 0, _cq) * mp.jtheta(4, 0, _cq), mp.mpf("1e-25"))
    _c1p = mp.diff(lambda zz: _theta(1)(zz, _tt), 0) / mp.pi
    chk("φ_{2,1} = Lean-def replay via _theta (20.11.6)", _cf(2, 1, _tz, _tt),
        _c1p * _theta(2)(_tz, _tt) / (_theta(2)(0, _tt) * _theta(1)(_tz, _tt)),
        mp.mpf("1e-18"))
    chk("φ_{1,3} = Lean-def replay via _theta (20.11.7)", _cf(1, 3, _tz, _tt),
        _theta(3)(0, _tt) * _theta(1)(_tz, _tt) / (_c1p * _theta(3)(_tz, _tt)),
        mp.mpf("1e-18"))
    chk("φ_{4,2} = Lean-def replay via _theta (20.11.8)", _cf(4, 2, _tz, _tt),
        _theta(2)(0, _tt) * _theta(4)(_tz, _tt) / (_theta(4)(0, _tt) * _theta(2)(_tz, _tt)),
        mp.mpf("1e-18"))
    _ceps = mp.mpf("1e-9")
    chk("πz·φ_{2,1}(z,τ) → 1 as z → 0 (normalization)",
        mp.pi * _ceps * _cf(2, 1, _ceps, _tt), 1, mp.mpf("1e-15"))
    _ct3 = mp.jtheta(3, 0, _cq)
    chk("θ₃²(0,q)·φ_{1,4} = sn(πz·θ₃²(0,q), k) (22.2.4)",
        _ct3 ** 2 * _cf(1, 4, _tz, _tt),
        mp.ellipfun("sn", mp.pi * _tz * _ct3 ** 2, (mp.jtheta(2, 0, _cq) / _ct3) ** 4),
        mp.mpf("1e-18"))
    # ── Jacobi triple product truncations (JacobiTripleProduct.lean; DLMF 20.5.3
    # cleared form). Anchors: (i) cleared factor = z²(1+q^{2n−1}z²)(1+q^{2n−1}z⁻²)
    # at n ≥ 1; (ii) the n = 0 Nat-truncation clamp (exponent 2·0−1 ↦ 0 ⇒ cleared
    # factor (1+z²)², full factor (1−q⁰)·… = 0); (iii) product/z^{2N} at large N
    # vs the INDEPENDENT mp.jtheta(3, −i·log z, q) = Σ q^{n²} z^{2n} (the DLMF
    # 20.5.3 identity itself); (iv) sum at z = 1 (clamp-free) vs jtheta(3, 0, q). ──
    _jq, _jz, _jN = mp.mpc("0.3", "0.1"), mp.mpc("0.7", "-0.2"), 40
    chk("jtp cleared factor n=3 = z²(1+q⁵z²)(1+q⁵z⁻²)",
        _jtp_factor_cleared(_jq, _jz, 3),
        _jz ** 2 * (1 + _jq ** 5 * _jz ** 2) * (1 + _jq ** 5 / _jz ** 2), mp.mpf("1e-25"))
    chk("jtp cleared factor n=0 clamp = (1+z²)²",
        _jtp_factor_cleared(_jq, _jz, 0), (1 + _jz ** 2) ** 2, mp.mpf("1e-25"))
    chk("jtp full factor n=0 = (1−q⁰)·… = 0", _jtp_factor(_jq, _jz, 0), 0, mp.mpf("1e-25"))
    chk("jtp triple product: P(q,z,40)/z⁸⁰ = jtheta(3, −i·log z, q)",
        _jtp_prod(_jq, _jz, _jN) / _jz ** (2 * _jN),
        mp.jtheta(3, -mp.mpc(0, 1) * mp.log(_jz), _jq), mp.mpf("1e-25"))
    chk("jtp sum @ z=1: Σ_{|n|≤40} q^{n²} = jtheta(3, 0, q)",
        _jtp_sum(_jq, 1, _jN), mp.jtheta(3, 0, _jq), mp.mpf("1e-25"))
    chk("jtp recurrence P(5) = P(4)·factor(5) (jtpProd_succ surface)",
        _jtp_prod(_jq, _jz, 5),
        _jtp_prod(_jq, _jz, 4) * _jtp_factor(_jq, _jz, 5), mp.mpf("1e-25"))
    # ── §20.6 lattice sums δ/α/β/γ_{2j} (Ch20PowerSeries.lean) — five anchor layers:
    # (i) the closed-form inner sum vs the classical Σ(m+a)⁻² = π²/sin²(πa) at a
    # complex a; (ii) the order-sensitive j = 1 case vs the KNOWN Eisenstein value
    # G₂(i) = π and the independent E₂ q-series (G₂ = (π²/3)E₂, inner-m-first —
    # exactly DLMF's summation order); (iii) the LITERAL doubly-truncated defining
    # sums at j = 2 (absolutely convergent regime, truncation-limited tol);
    # (iv) end-to-end DLMF 20.6.2 against the already-anchored θ₁; (v) the 20.6.10
    # inter-relations cross-tie all four bindings. ──
    _la = mp.mpc("0.3", "0.7")
    chk("lattice inner Σ(m+a)⁻² = π²/sin²(πa)", _lattice_inner(1, _la),
        mp.pi ** 2 / mp.sin(mp.pi * _la) ** 2, mp.mpf("1e-25"))
    chk("δ₂(i) = G₂(i) = π (j=1 order)", _lattice_delta(1, mp.mpc(0, 1)), mp.pi,
        mp.mpf("1e-25"))
    _ltt = mp.mpc("0.3", "1.1")
    chk("δ₂ = (π²/3)·E₂ (q-series)", _lattice_delta(1, _ltt),
        mp.pi ** 2 / 3 * _eisenstein_E2(_ltt), mp.mpf("1e-25"))
    _ltc = complex(0.21, 0.93)
    _lit4 = lambda dm, dn, excl: sum(
        1 / (m + dm + (n + dn) * _ltc) ** 4
        for n in range(-12, 13) for m in range(-800, 801)
        if not (excl and m == 0 and n == 0))
    _ltm = mp.mpc("0.21", "0.93")
    chk("δ₄ literal double sum", _lattice_delta(2, _ltm), _lit4(0.0, 0.0, True), mp.mpf("1e-6"))
    chk("α₄ literal double sum", _lattice_alpha(2, _ltm), _lit4(-0.5, 0.0, False), mp.mpf("1e-6"))
    chk("β₄ literal double sum", _lattice_beta(2, _ltm), _lit4(-0.5, -0.5, False), mp.mpf("1e-6"))
    chk("γ₄ literal double sum", _lattice_gamma(2, _ltm), _lit4(0.0, -0.5, False), mp.mpf("1e-6"))
    _lz = mp.mpc("0.35", "0.1")
    chk("20.6.2 end-to-end: θ₁ = z·θ₁′(0)·exp(−Σ δ_{2j}z^{2j}/(2j))",
        _theta(1)(_lz, _ltt),
        _lz * mp.diff(lambda w: _theta(1)(w, _ltt), 0)
        * mp.exp(-mp.fsum(_lattice_delta(jj, _ltt) / (2 * jj) * _lz ** (2 * jj)
                          for jj in range(1, 41))), mp.mpf("1e-25"))
    chk("20.6.10 α₂ = 4δ₂(2τ) − δ₂(τ)", _lattice_alpha(1, _ltt),
        4 * _lattice_delta(1, 2 * _ltt) - _lattice_delta(1, _ltt), mp.mpf("1e-25"))
    chk("20.6.10 β₂ = 4γ₂(2τ) − γ₂(τ)", _lattice_beta(1, _ltt),
        4 * _lattice_gamma(1, 2 * _ltt) - _lattice_gamma(1, _ltt), mp.mpf("1e-25"))
    # Jacobi identity θ₂⁴+θ₄⁴=θ₃⁴ at the nulls ⇒ k²+k′²=1 and λ+λ′=1; λ(i)=1/2 exactly
    chk("k²+k′²=1 @ τ=0.5+0.8i", _elliptic_modulus(_tt) ** 2 + _complementary_modulus(_tt) ** 2, 1)
    chk("λ+λ′=1 @ τ=0.5+0.8i", _modular_lambda(_tt) + _complementary_lambda(_tt), 1)
    chk("λ(i)=1/2", _modular_lambda(mp.mpc(0, 1)), mp.mpf(1) / 2)
    chk("λ=k² @ τ", _modular_lambda(_tt), _elliptic_modulus(_tt) ** 2)
    # ── §20.6 lattice sums, extra KNOWN-VALUE layers (complementing the block above):
    # the j = 2 inner closed form vs (π²csc²)″/6 (d²/da² (m+a)⁻² = 6(m+a)⁻⁴), and the
    # lemniscatic square-lattice Eisenstein values G₄(i) = Γ(1/4)⁸/(960π²), G₆(i) = 0
    # (g₃(ℤ+ℤi) = 140·G₆ = 0 — the distinguishing degeneracy). ──
    chk("lattice inner j=2: ∑(m+a)^{−4}=(π²csc²)″/6", _lattice_inner(2, _la),
        mp.diff(lambda t: mp.pi ** 2 / mp.sin(mp.pi * t) ** 2, _la, 2) / 6, mp.mpf("1e-25"))
    chk("δ₄(i)=Γ(1/4)⁸/(960π²)", _lattice_delta(2, mp.mpc(0, 1)),
        mp.gamma(mp.mpf(1) / 4) ** 8 / (960 * mp.pi ** 2), mp.mpf("1e-25"))
    chk("δ₆(i)=0 (lemniscatic g₃=0)", _lattice_delta(3, mp.mpc(0, 1)), 0, mp.mpf("1e-25"))
    # ── M7: Bernoulli polynomial = standard Bₙ(x); Faulhaber 1²+2²=B₃(3)/3−B₃(0)/3 ──
    chk("bernpoly B₁(0)=−1/2", mp.bernpoly(1, 0), mp.mpf(-1) / 2)
    chk("Faulhaber p=2,n=3: 3·(0²+1²+2²)=B₃(3)−B₃", 3 * mp.mpf(5),
        mp.bernpoly(3, 3) - mp.bernpoly(3, 0))
    # ── M8 / B3: Legendre bracket bindings + weighted-orthogonality numbers ──
    # P₂(x)=(3x²−1)/2, P[n](−1)=(−1)ⁿ, Q₀(x)=½ln((1+x)/(1−x)) — same objects as the
    # non-bracket bindings, exercised through the synthetic bracket heads.
    chk("P[2](0.7)=(3x²−1)/2", mp.legendre(2, mp.mpf("0.7")), (3 * mp.mpf("0.7") ** 2 - 1) / 2)
    chk("P[3](−1)=−1", mp.legendre(3, -1), -1)
    chk("Q[0](0.7)=½ln((1+x)/(1−x))", mp.legenq(0, 0, mp.mpf("0.7")),
        mp.mpf("0.5") * mp.log((1 + mp.mpf("0.7")) / (1 - mp.mpf("0.7"))))
    chk("P[1,1](½)=−√3/2 (assoc, CS phase)", mp.legenp(1, 1, mp.mpf("0.5")), -mp.sqrt(mp.mpf("0.75")))
    # Chebyshev orthogonality under the weight 1/√(1−x²): ∫₋₁¹ Tₘ(x)Tₙ(x)/√(1−x²) dx
    # = 0 (m≠n), π (m=n=0), π/2 (m=n≠0) — anchors the measureT weight + endpoint handling.
    _w = lambda x: 1 / mp.sqrt(1 - x ** 2)
    chk("∫ T₂T₃ w = 0", mp.quad(lambda x: mp.chebyt(2, x) * mp.chebyt(3, x) * _w(x), [-1, 1]),
        0, mp.mpf("1e-12"))
    chk("∫ T₀² w = π", mp.quad(lambda x: _w(x), [-1, 1]), mp.pi, mp.mpf("1e-12"))
    chk("∫ T₃² w = π/2", mp.quad(lambda x: mp.chebyt(3, x) ** 2 * _w(x), [-1, 1]), mp.pi / 2,
        mp.mpf("1e-12"))
    chk("normalizationConst(0)=π", mp.pi if 0 == 0 else mp.pi / 2, mp.pi)
    chk("legendreNormConst(2)=2/5", 2 / (2 * mp.mpf(2) + 1), mp.mpf(2) / 5)
    # ── legendreEigenvalue λₙ = n(n+1) (DLMF 30.3.3, degenerate γ=0 spheroidal):
    # anchored against the DEFINING Legendre ODE (1−x²)Pₙ″ − 2x·Pₙ′ + λₙ·Pₙ = 0 —
    # λ recovered numerically from Pₙ at x=0.3, decorrelated from the closed form
    # the binding computes with. n=1 (λ₁=2, not 1) rejects an n² mis-binding. ──
    _xe = mp.mpf("0.3")
    for _ne in (0, 1, 2, 5):
        _lam_ode = ((2 * _xe * mp.diff(lambda t, _n=_ne: mp.legendre(_n, t), _xe)
                     - (1 - _xe ** 2) * mp.diff(lambda t, _n=_ne: mp.legendre(_n, t), _xe, 2))
                    / mp.legendre(_ne, _xe))
        chk(f"legendreEigenvalue λ_{_ne} from the Legendre ODE",
            _legendre_eigenvalue(_ne), _lam_ode, mp.mpf("1e-15"))
    # ── Christoffel–Darboux Chebyshev-T witness (DLMF 18.2.12, the ∀-quantified
    # IsCDSystem instantiation cdChebP/cdChebH/cdChebA): anchor the witness DATA and
    # every hypothesis clause BEFORE the sweep trusts it — never by name. ──
    # (i) hₖ against the DEFINING orthogonality integrals ∫₋₁¹ Tₖ²(1−x²)^{−1/2} dx.
    chk("CD witness h₀ = ∫T₀²w", mp.quad(lambda x: _w(x), [-1, 1]), _cd_cheb_h(0),
        mp.mpf("1e-12"))
    chk("CD witness h₃ = ∫T₃²w", mp.quad(lambda x: mp.chebyt(3, x) ** 2 * _w(x), [-1, 1]),
        _cd_cheb_h(3), mp.mpf("1e-12"))
    # (ii) aₖ = kₖ/(hₖ kₖ₊₁) with the leading coefficients kₙ read off the EXACT n-th
    # forward difference ΔⁿTₙ(0)/n! (exact for a degree-n polynomial — decorrelated
    # from the 2^{n−1} closed form baked into cdChebA).
    _cdlead = lambda n: mp.fsum((-1) ** (n - j) * _choose(n, j) * mp.chebyt(n, j)
                                for j in range(n + 1)) / mp.factorial(n)
    chk("CD witness a₀ = k₀/(h₀k₁)", _cd_cheb_a(0), _cdlead(0) / (_cd_cheb_h(0) * _cdlead(1)))
    chk("CD witness a₃ = k₃/(h₃k₄)", _cd_cheb_a(3), _cdlead(3) / (_cd_cheb_h(3) * _cdlead(4)))
    # (iii) the IsCDSystem hypothesis clauses at the witness (base + step, through the
    # SAME _cd_summand/_cd_cross the sweep evaluates — pins the (p,h/a,k,x,y) arg order).
    _cdx, _cdy = mp.mpf("0.4"), mp.mpf("-0.7")
    chk("CD witness IsCDSystem.base",
        (_cdx - _cdy) * _cd_summand(_cd_cheb_p, _cd_cheb_h, 0, _cdx, _cdy),
        _cd_cross(_cd_cheb_p, _cd_cheb_a, 0, _cdx, _cdy))
    for _cdk in range(5):
        chk(f"CD witness IsCDSystem.step k={_cdk}",
            (_cdx - _cdy) * _cd_summand(_cd_cheb_p, _cd_cheb_h, _cdk + 1, _cdx, _cdy),
            _cd_cross(_cd_cheb_p, _cd_cheb_a, _cdk + 1, _cdx, _cdy)
            - _cd_cross(_cd_cheb_p, _cd_cheb_a, _cdk, _cdx, _cdy))
    # (iv) DLMF 18.2.12 itself at the witness (n = 4): the telescoped sum equals the
    # cross term — the identity the abstract surface states.
    chk("CD witness 18.2.12 n=4",
        (_cdx - _cdy) * mp.fsum(_cd_summand(_cd_cheb_p, _cd_cheb_h, _cdk, _cdx, _cdy)
                                for _cdk in range(5)),
        _cd_cross(_cd_cheb_p, _cd_cheb_a, 4, _cdx, _cdy))
    # (v) the CONFLUENT system (DLMF 18.2.13, the y → x diagonal; witness cdChebD):
    # anchor Dₖ's DEFINING formula aₖ(T′ₖ₊₁Tₖ − T′ₖTₖ₊₁) against an INDEPENDENT
    # mp.diff derivative (decorrelated from the exact T′ₙ = n·Uₙ₋₁ baked into
    # cdChebD), then every IsConfluentCDSystem hypothesis clause (base + step),
    # then 18.2.13 itself at the witness — before the sweep trusts it.
    for _ccx in (mp.mpf("0.4"), mp.mpf("-0.7"), mp.mpf("1.6")):
        chk(f"confluent-CD witness D₃ defining formula @ x={_ccx}", _cd_cheb_d(3, _ccx),
            _cd_cheb_a(3) * (mp.diff(lambda t: mp.chebyt(4, t), _ccx) * mp.chebyt(3, _ccx)
                             - mp.diff(lambda t: mp.chebyt(3, t), _ccx) * mp.chebyt(4, _ccx)),
            mp.mpf("1e-15"))
        chk(f"confluent-CD witness IsConfluentCDSystem.base @ x={_ccx}",
            _cd_cheb_p(0, _ccx) ** 2 / _cd_cheb_h(0), _cd_cheb_d(0, _ccx))
        for _cck in range(5):
            chk(f"confluent-CD witness IsConfluentCDSystem.step k={_cck} @ x={_ccx}",
                _cd_cheb_p(_cck + 1, _ccx) ** 2 / _cd_cheb_h(_cck + 1),
                _cd_cheb_d(_cck + 1, _ccx) - _cd_cheb_d(_cck, _ccx))
        chk(f"confluent-CD witness 18.2.13 n=4 @ x={_ccx}",
            mp.fsum(_cd_cheb_p(_cck, _ccx) ** 2 / _cd_cheb_h(_cck) for _cck in range(5)),
            _cd_cheb_d(4, _ccx))
    # ── M9 / C1: Laplace/Mellin transforms over (0,∞) + Laguerre family ──
    # Bessel-J₀ Laplace transform ∫₀^∞ e^{−at}J₀(bt) dt = 1/√(a²+b²) (DLMF 10.22.49)
    _a, _b = mp.mpf("1.7"), mp.mpf("0.8")
    chk("∫ e^{−at}J₀(bt) = 1/√(a²+b²)",
        mp.quad(lambda t: mp.e ** (-_a * t) * mp.besselj(0, _b * t), [0, mp.inf]),
        1 / mp.sqrt(_a ** 2 + _b ** 2), mp.mpf("1e-20"))
    # generalized Laguerre weight moment ∫₀^∞ xᵏ·x^α e^{−x} dx = Γ(k+α+1) (DLMF 18.3 / 5.2.1)
    _al, _k = mp.mpf("0.3"), 2
    chk("∫ xᵏ·laguerreWeight = Γ(k+α+1)",
        mp.quad(lambda x: x ** _k * x ** _al * mp.e ** (-x), [0, mp.inf]),
        mp.gamma(_k + _al + 1), mp.mpf("1e-20"))
    # generalized Laguerre value + degree-1 form: L₀^(α)=1, L₁^(α)(x)=α+1−x (DLMF 18.5.12)
    chk("laguerre L₀^(α)=1", mp.laguerre(0, _al, mp.mpf("0.7")), 1)
    chk("laguerre L₁^(α)(x)=α+1−x", mp.laguerre(1, _al, mp.mpf("0.7")), _al + 1 - mp.mpf("0.7"))
    # orthogonality of distinct degrees under the weight: ∫₀^∞ L₀L₁ x^α e^{−x} = 0
    chk("∫ L₀^(α)L₁^(α) w = 0",
        mp.quad(lambda x: mp.laguerre(0, _al, x) * mp.laguerre(1, _al, x) * x ** _al * mp.e ** (-x),
                [0, mp.inf]), 0, mp.mpf("1e-15"))
    # laguerreNormSq α n = Γ(n+α+1)/n!  (squared L²-norm, DLMF 18.3 table)
    chk("laguerreNormSq(α,2)=Γ(α+3)/2!", mp.gamma(2 + _al + 1) / mp.factorial(2),
        mp.gamma(_al + 3) / 2)
    # ── M10 / C2: Jacobi elliptic via theta, Gudermannian, Ei/li, Pochhammer ──
    # τ-parametrized Jacobi: anchored at the Lean defining quotients AND the fundamental
    # identity cn²+sn²=1, at a point with Im τ > 0. sn is odd ⇒ sn(0,τ)=0.
    _jz, _jt = mp.mpc("0.3", "0.2"), mp.mpc("0.4", "0.9")
    chk("sn = θ₃(0)θ₁(z)/(θ₂(0)θ₄(z))", _sn(_jz, _jt),
        _theta(3)(0, _jt) * _theta(1)(_jz, _jt) / (_theta(2)(0, _jt) * _theta(4)(_jz, _jt)),
        mp.mpf("1e-25"))
    chk("Jacobi cn²+sn²=1", _cn(_jz, _jt) ** 2 + _sn(_jz, _jt) ** 2, 1, mp.mpf("1e-22"))
    chk("Jacobi sn(0,τ)=0", _sn(0, _jt), 0, mp.mpf("1e-25"))
    chk("Glaisher cd=cn/dn", _GLAISHER["cd"](_jz, _jt), _cn(_jz, _jt) / _dn(_jz, _jt), mp.mpf("1e-22"))
    chk("Glaisher nc·cn=1", _GLAISHER["nc"](_jz, _jt) * _cn(_jz, _jt), 1, mp.mpf("1e-22"))
    chk("Glaisher dc=1/cd", _GLAISHER["dc"](_jz, _jt), 1 / _GLAISHER["cd"](_jz, _jt), mp.mpf("1e-22"))
    # pole guard on the quotient denominators: (a) a NO-OP off the zero lattice — guarded ds
    # equals the raw quotient dn/sn and keeps the DLMF 22.4.3 parity ds(−z) = −ds(z);
    # (b) at z = τ (a lattice zero of θ₁, i.e. a pole of ds — the two-ℂ-binder grid diagonal)
    # it must RAISE, dropping the sample as a domain skip instead of comparing 1e60 noise.
    chk("Glaisher ds=dn/sn (guard no-op)", _GLAISHER["ds"](_jz, _jt),
        _dn(_jz, _jt) / _sn(_jz, _jt), mp.mpf("1e-22"))
    chk("Glaisher ds(−z)=−ds(z) (DLMF 22.4.3)", _GLAISHER["ds"](-_jz, _jt),
        -_GLAISHER["ds"](_jz, _jt), mp.mpf("1e-22"))
    # MODULUS-parametrized snk/cnk/dnk (JacobiModulusBridge.lean, DLMF §22.2), anchored on
    # values INDEPENDENT of the theta-quotient route: (a) tauOfModulus is pinned by the
    # classical nome relation k² = (θ₂(0,q)/θ₃(0,q))⁴ at q = e^{iπτ} — a round trip through
    # mpmath's AGM ellipk; (b) snk/cnk/dnk equal mpmath's AGM `ellipfun` at parameter m = k²
    # and argument u = πz·θ₃(0,q)² (FLMF's θⱼ have period 1 in z, mpmath's jtheta period π,
    # and the classical Jacobi argument is θ₃²-scaled). Domain guard: |k| ∉ (0,1) raises.
    _mk = mp.mpf("0.6")
    _mtau = _tau_of_modulus(_mk)
    _mq = mp.exp(mp.mpc(0, 1) * mp.pi * _mtau)
    chk("tauOfModulus: (θ₂/θ₃)⁴ = k²", (mp.jtheta(2, 0, _mq) / mp.jtheta(3, 0, _mq)) ** 4,
        _mk ** 2, mp.mpf("1e-22"))
    _mu = mp.pi * _jz * mp.jtheta(3, 0, _mq) ** 2
    chk("snk = AGM sn(u,m=k²)", _snk(_jz, _mk), mp.ellipfun("sn", _mu, _mk ** 2), mp.mpf("1e-20"))
    chk("cnk = AGM cn(u,m=k²)", _cnk(_jz, _mk), mp.ellipfun("cn", _mu, _mk ** 2), mp.mpf("1e-20"))
    chk("dnk = AGM dn(u,m=k²)", _dnk(_jz, _mk), mp.ellipfun("dn", _mu, _mk ** 2), mp.mpf("1e-20"))

    def chk_raises(name, fn):
        try:
            fn()
            fails.append(f"{name}: expected pole-guard ValueError, got a value")
        except ValueError:
            pass

    chk_raises("ds pole guard @ z=τ (sn lattice zero)", lambda: _GLAISHER["ds"](_jt, _jt))
    chk_raises("ns pole guard @ z=0 (sn(0,τ)=0)", lambda: _GLAISHER["ns"](0, _jt))
    chk_raises("cs pole guard @ z=1+τ (sn lattice zero)", lambda: _GLAISHER["cs"](1 + _jt, _jt))
    chk_raises("dc pole guard @ z=1/2 (cn zero)", lambda: _GLAISHER["dc"](mp.mpf("0.5"), _jt))
    # snk/cnk/dnk domain guard: k = 0 sends K′ → ∞ and |k| ≥ 1 leaves completeK's real
    # domain — both must raise so the sample drops rather than fabricating a value.
    chk_raises("snk domain guard @ k=0", lambda: _snk(_jz, mp.mpf(0)))
    chk_raises("snk domain guard @ k=1.7", lambda: _snk(_jz, mp.mpf("1.7")))
    chk_raises("dnk domain guard @ k=−2.4", lambda: _dnk(_jz, mp.mpf("-2.4")))
    # ramanujanTheta divergence guard: |ab| ≥ 1 is outside DLMF 20.11.3 — must raise
    chk_raises("ramanujanTheta guard @ |ab|=2 ≥ 1", lambda: _ramanujan_theta(2, 1))
    chk_raises("ramanujanTheta guard @ |ab|=1 (boundary)", lambda: _ramanujan_theta(mp.mpc(0, 1), 1))
    # §20.6 lattice sums: honest drops at the Lean junk-tsum regimes (defs' caveat)
    chk_raises("lattice guard @ j=0 (divergent)", lambda: _lattice_alpha(0, mp.mpc(0, 1)))
    chk_raises("lattice guard @ Im τ = 0", lambda: _lattice_delta(1, mp.mpf("0.5")))
    chk_raises("lattice guard @ Im τ < 0", lambda: _lattice_gamma(1, mp.mpc("0.3", "-1.1")))
    # small-but-genuine value must NOT trip the guard (ds(z)·sn(z) = dn(z) near 0)
    _jsmall = mp.mpf("0.05")
    chk("ds·sn=dn near 0 (guard not over-eager)",
        _GLAISHER["ds"](_jsmall, _jt) * _sn(_jsmall, _jt), _dn(_jsmall, _jt), mp.mpf("1e-22"))
    # ── OrthogonalPoly-bundle witness (DLMF §18.2(vi)): the distinct-real-root counter ──
    # NEGATIVE controls first — the counter must MEASURE realness/distinctness, never
    # echo the degree: x²+1 has 0 real roots, (x−1)² has 1 DISTINCT root, x²−1 has 2.
    chk("rootcount x^2+1 -> 0 (complex pair rejected)",
        mp.mpf(_distinct_real_root_count([1, 0, 1])), mp.mpf(0))
    chk("rootcount (x-1)^2 -> 1 (double root deduplicated)",
        mp.mpf(_distinct_real_root_count([1, -2, 1])), mp.mpf(1))
    chk("rootcount x^2-1 -> 2", mp.mpf(_distinct_real_root_count([1, 0, -1])), mp.mpf(2))
    # coefficient anchor: the DLMF 18.5.12 explicit sum at α = 0 against mpmath's
    # INDEPENDENT mp.laguerre implementation, at a generic point.
    chk("laguerre coeffs anchor L6(1.7)",
        mp.polyval(_laguerre_coeffs(6), mp.mpf("1.7")), mp.laguerre(6, 0, mp.mpf("1.7")))
    # root-VALUE anchors, decorrelated from the count: L₂ = 1 − 2x + x²/2 has the exact
    # roots 2 ± √2; the smallest zero of L₅ is the classical 5-point Gauss–Laguerre node.
    _l2r = sorted(mp.re(r) for r in mp.polyroots(_laguerre_coeffs(2)))
    chk("L2 root 2-sqrt2", _l2r[0], 2 - mp.sqrt(2))
    chk("L2 root 2+sqrt2", _l2r[1], 2 + mp.sqrt(2))
    chk("L5 smallest zero = Gauss-Laguerre node",
        min(mp.re(r) for r in mp.polyroots(_laguerre_coeffs(5), maxsteps=200, extraprec=250)),
        mp.mpf("0.2635603197181409102030619434"))
    # the witness head itself over (a superset of) the sweep's ge1 n-grid, including the
    # validated-range endpoint n = 24 — and the env plumbing (degree binder `n`) round-trips.
    for _nn in (1, 2, 3, 5, 12, 24):
        chk(f"O.P.roots.toFinset.card witness n={_nn}",
            _op_bundle_roots_card({"n": mp.mpf(_nn)}), mp.mpf(_nn))
    # out-of-range/absent degree must RAISE (honest sample drop), never return a count
    chk_raises("O.P witness n=25 out of validated range",
               lambda: _op_bundle_roots_card({"n": mp.mpf(25)}))
    chk_raises("O.P witness missing n", lambda: _op_bundle_roots_card({}))
    # Gudermannian: sin(gd u)=tanh u, cos(gd u)=sech u
    _u = mp.mpf("0.7")
    chk("sin(gd u)=tanh u", mp.sin(_gudermannian(_u)), mp.tanh(_u))
    chk("cos(gd u)=1/cosh u", mp.cos(_gudermannian(_u)), 1 / mp.cosh(_u))
    # ascending Pochhammer (rising factorial): (x)₂ = x(x+1), (x)₀ = 1
    chk("ascPochhammer (x)₂=x(x+1)", mp.rf(mp.mpf("1.3"), 2), mp.mpf("1.3") * mp.mpf("2.3"))
    chk("ascPochhammer (x)₀=1", mp.rf(mp.mpf("1.3"), 0), 1)
    # J₂/K₂ against their DLMF recurrences (the corrected FLMF defining forms): the J
    # recurrence has +, the modified-Bessel K recurrence has − (DLMF 10.29.1).
    _zb = mp.mpf("1.7")
    chk("J₂ = 2J₁/z − J₀", mp.besselj(2, _zb), 2 * mp.besselj(1, _zb) / _zb - mp.besselj(0, _zb),
        mp.mpf("1e-25"))
    chk("K₂ = K₀ + (2/z)K₁ (K-recurrence is −)", mp.besselk(2, _zb),
        mp.besselk(0, _zb) + (2 / _zb) * mp.besselk(1, _zb), mp.mpf("1e-25"))
    # spherical Bessel 2nd kind: y₀(x) = −cos x/x, y₁(x) = −cos x/x² − sin x/x
    _syf = lambda n, x: mp.sqrt(mp.pi / (2 * x)) * mp.bessely(n + mp.mpf(1) / 2, x)
    chk("sphericalY y₀=−cos x/x", _syf(0, _zb), -mp.cos(_zb) / _zb, mp.mpf("1e-25"))
    chk("sphericalY y₁=−cos/x²−sin/x", _syf(1, _zb), -mp.cos(_zb) / _zb ** 2 - mp.sin(_zb) / _zb,
        mp.mpf("1e-25"))
    # ── M12 / C2: angular-momentum symbols ──
    # triangleCoeffSq Δ²(2,1,1)=2!·2!·0!/5! = 4/120 = 1/30; symmetry under arg swap
    chk("triangleCoeffSq(2,1,1)=1/30", _triangle_coeff_sq(2, 1, 1), mp.mpf(1) / 30)
    chk("triangleCoeffSq swap-symmetric", _triangle_coeff_sq(2, 1, 3), _triangle_coeff_sq(1, 2, 3))
    chk("magneticFactor neg-symmetric", _magnetic_factor(3, 2, 1, -1, -2, -1),
        _magnetic_factor(3, 2, 1, 1, 2, 1))
    # Mellin transform of e^{−t} is Γ(s): ∫₀^∞ t^{s−1}e^{−t} dt (real and complex s, Re s > 0)
    chk("∫ t^{s−1}e^{−t} = Γ(s) @ s=2.3", mp.quad(lambda t: t ** (mp.mpf("2.3") - 1) * mp.e ** (-t),
        [0, mp.inf]), mp.gamma(mp.mpf("2.3")), mp.mpf("1e-18"))
    _sc = mp.mpc("1.4", "0.8")
    chk("Mellin Γ @ complex s", mp.quad(lambda t: t ** (_sc - 1) * mp.e ** (-t), [0, mp.inf]),
        mp.gamma(_sc), mp.mpf("1e-15"))
    # Laplace integral (DLMF 14.7.19) for P₂ at x=1.7 (x²≥1, so √ is real): = legendre(2,x)
    _xl = mp.mpf("1.7")
    chk("laplaceIntegral 2 = P₂ @ x=1.7",
        (1 / mp.pi) * mp.quad(lambda th: (_xl + _rsqrt(_xl ** 2 - 1) * mp.cos(th)) ** 2, [0, mp.pi]),
        mp.legendre(2, _xl), mp.mpf("1e-18"))
    if _HAVE_SYMPY:
        # Wigner/Racah/CG anchored against standard table values (DLMF 34 / Edmonds)
        chk("3j(1,1,0;0,0,0)=−1/√3", _sym(_sy_3j(1, 1, 0, 0, 0, 0)), -1 / mp.sqrt(3), mp.mpf("1e-25"))
        chk("6j{1,1,1;1,1,1}=1/6", _sym(_sy_6j(1, 1, 1, 1, 1, 1)), mp.mpf(1) / 6, mp.mpf("1e-25"))
        chk("CG⟨1 0 1 0|2 0⟩=√(2/3)", _sym(_sy_cg(1, 1, 2, 0, 0, 0)), mp.sqrt(mp.mpf(2) / 3),
            mp.mpf("1e-25"))
        # racahSum self-validation (DLMF 34.2.4 full assembly, correct zpow phase) against
        # independent sympy wigner_3j — includes the wigner3j-tonat-phase bug witness
        # (0,1,1;0,0,0). See ERRATA `wigner3j-tonat-phase`.
        def _wigner3j_via_racah(j1, j2, j3, m1, m2, m3):
            if m1 + m2 + m3 != 0:
                return mp.mpf(0)
            phase = mp.mpf((-1)) ** (j1 - j2 - m3)
            tri = mp.sqrt(_triangle_coeff_sq(j1, j2, j3))
            mag = mp.sqrt(_magnetic_factor(j1, j2, j3, m1, m2, m3))
            return phase * tri * mag * _racah_sum(j1, j2, j3, m1, m2)
        for (_j1, _j2, _j3, _m1, _m2, _m3) in [
            (0, 1, 1, 0, 0, 0), (1, 2, 1, 0, 0, 0), (1, 1, 0, 0, 0, 0),
            (2, 1, 1, 0, 0, 0), (2, 2, 2, 1, -1, 0), (3, 2, 2, 1, 0, -1),
        ]:
            chk(f"racahSum-assembly 3j({_j1},{_j2},{_j3};{_m1},{_m2},{_m3})",
                _wigner3j_via_racah(_j1, _j2, _j3, _m1, _m2, _m3),
                _sym(_sy_3j(_j1, _j2, _j3, _m1, _m2, _m3)), mp.mpf("1e-30"))
        # DLMF 34.4.1 relation, both sides independent: W(abcd;ef)=(−1)^{a+b+c+d}{a b e;d c f}
        _W = _sym(_sy_racah(1, 2, 3, 2, 2, 3))
        _6 = _sym(_sy_6j(1, 2, 2, 2, 3, 3))
        chk("racahW=(−1)^{a+b+c+d}·6j", _W, (-1) ** (1 + 2 + 3 + 2) * _6, mp.mpf("1e-25"))
        # Jacobi symbol + the χ₄/χ₈ supplementary laws (DLMF 27.9)
        chk("J(1001|9907)=−1", _jacobi_sym(1001, 9907), -1)
        for _n in (1, 3, 5, 7, 9, 11):
            chk(f"J(-1|{_n})=χ₄", _jacobi_sym(-1, _n), _chi4(_n))
            chk(f"J(2|{_n})=χ₈", _jacobi_sym(2, _n), _chi8(_n))
        # Legendre symbol (DLMF 27.9): anchored to the DEFINING quadratic-residue
        # criterion — (a|p) = +1 if a is a nonzero QR mod the odd prime p, −1 if a
        # nonresidue, 0 if p | a — with the residue sets {x² mod p} brute-forced
        # INDEPENDENTLY of sympy, plus Euler's criterion a^((p−1)/2) mod p (§27.9
        # text). Exhaustive over a ∈ [0, p) for p ∈ {3, 5, 7, 11, 13}.
        for _p in (3, 5, 7, 11, 13):
            _qrs = {(x * x) % _p for x in range(1, _p)}
            for _a in range(_p):
                _def = 0 if _a == 0 else (1 if _a in _qrs else -1)
                chk(f"({_a}|{_p}) QR-defining criterion", _legendre_sym(_p, _a), _def)
                _eul = pow(_a, (_p - 1) // 2, _p)
                chk(f"({_a}|{_p}) Euler criterion", _legendre_sym(_p, _a),
                    0 if _eul == 0 else (1 if _eul == 1 else -1))
        # asymmetry (3|7) = −1 ≠ (7|3) = +1 pins the Mathlib PRIME-FIRST argument
        # order (a swapped binding would flip both of these)
        chk("(3|7)=−1 (prime-first arg order)", _legendre_sym(7, 3), -1)
        chk("(7|3)=+1 (prime-first arg order)", _legendre_sym(3, 7), 1)
        chk("(-1|5)=+1 (negative a via mod p)", _legendre_sym(5, -1), 1)
        # non-odd-prime modulus is outside the DLMF 27.9 domain → honest sample drop
        chk_raises("legendreSym guard @ p=8 (non-prime)", lambda: _legendre_sym(8, 3))
        chk_raises("legendreSym guard @ p=2 (even prime)", lambda: _legendre_sym(2, 3))
        # zmod_is_square (Mathlib `IsSquare` on ZMod p) cross-checked against the
        # INDEPENDENT sympy.legendre_symbol: for an odd prime p, a ≢ 0 (mod p) is a
        # square in ZMod p iff (a|p) = +1, and a ≡ 0 is always the square of 0.
        # Exhaustive over a ∈ [−p, p] for every prime the iff-bool sweep grid samples.
        for _p in (3, 5, 7, 11, 13, 17, 19, 23, 29):
            for _a in range(-_p, _p + 1):
                _want = True if _a % _p == 0 else (int(_legendre_sym(_p, _a)) == 1)
                if zmod_is_square(_a, _p) != _want:
                    fails.append(f"zmod_is_square({_a}, {_p}) ≠ Legendre criterion")
    # ── M14 number theory: χ₄/χ₈ distinguish, completed zeta ──
    chk("χ₄(3)=−1", _chi4(3), -1)
    chk("χ₈(5)=−1 (≠χ₄(5)=+1)", _chi8(5), -1)
    # zmod_is_square defining anchors (sympy-free): the exact square set mod 7 is
    # {0,1,2,4}; mod 8 (a COMPOSITE modulus, beyond the Legendre cross-check) it is
    # {0,1,4}; and the DLMF 27.9 first supplement itself — −1 is a square mod p ≡ 1
    # (mod 4) and a nonresidue mod p ≡ 3 (mod 4); guards raise on n ≤ 0 / non-integers.
    for _a in range(7):
        if zmod_is_square(_a, 7) != (_a in (0, 1, 2, 4)):
            fails.append(f"zmod_is_square({_a}, 7): square set mod 7 is {{0,1,2,4}}")
    for _a in range(8):
        if zmod_is_square(_a, 8) != (_a in (0, 1, 4)):
            fails.append(f"zmod_is_square({_a}, 8): square set mod 8 is {{0,1,4}}")
    for _p in (5, 13, 17, 29):
        if not zmod_is_square(-1, _p):
            fails.append(f"zmod_is_square(-1, {_p}): −1 must be a QR (p ≡ 1 mod 4)")
    for _p in (3, 7, 11, 19, 23):
        if zmod_is_square(-1, _p):
            fails.append(f"zmod_is_square(-1, {_p}): −1 must be a nonresidue (p ≡ 3 mod 4)")
    for _bad in (lambda: zmod_is_square(3, 0), lambda: zmod_is_square(3, -5),
                 lambda: zmod_is_square(mp.mpf("2.5"), 7)):
        try:
            _bad()
            fails.append("zmod_is_square guard: expected ValueError, got a value")
        except ValueError:
            pass
    # ── SAMPLE_DIRICHLET_CHARS: each sampled χ satisfies the DLMF 27.8 DEFINING conditions,
    # and per modulus the sample is the COMPLETE character group (φ(k) pairwise-distinct
    # characters). Anchored to the defining formulas (27.8.2 periodicity χ(n+k)=χ(n);
    # 27.8.3 complete multiplicativity χ(mn)=χ(m)χ(n) — unrestricted m,n, including
    # non-units; 27.8.4 χ(n)=0 iff gcd(n,k)>1) and, at modulus 4, cross-checked against
    # the INDEPENDENT `_chi4` implementation — never by name.
    from math import gcd as _vgcd
    for _dk in (3, 4, 5, 7, 9):
        _grp = [c for c in SAMPLE_DIRICHLET_CHARS if c.modulus == _dk]
        chk(f"#chars mod {_dk} = φ({_dk}) (complete group)", len(_grp), _totient(_dk))
        _sigs = {tuple(mp.nstr(c(a), 12) for a in range(_dk)) for c in _grp}
        if len(_sigs) != len(_grp):
            fails.append(f"dirichlet chars mod {_dk}: not pairwise distinct")
        for _c in _grp:
            for _a in range(2 * _dk):
                chk(f"χ mod {_dk} (t={_c.index}) 27.8.2 periodicity @ {_a}",
                    _c(_a + _dk), _c(_a))
                if _vgcd(_a, _dk) > 1:
                    chk(f"χ mod {_dk} (t={_c.index}) 27.8.4 zero off units @ {_a}", _c(_a), 0)
                elif abs(_c(_a)) < mp.mpf("0.5"):
                    fails.append(f"dirichlet χ mod {_dk} (t={_c.index}): |χ({_a})| ≠ 1 on a unit")
            for _m in range(2, 5):
                for _n in range(2, 5):
                    chk(f"χ mod {_dk} (t={_c.index}) 27.8.3 mult @ ({_m},{_n})",
                        _c(_m * _n), _c(_m) * _c(_n))
    for _c in SAMPLE_DIRICHLET_CHARS:
        if _c.modulus == 4 and _c.index == 1:      # the non-principal χ mod 4 IS χ₄ —
            for _a in range(8):                    # independent-implementation cross-check
                chk(f"χ mod 4 non-principal = χ₄ @ {_a}", _c(_a), _chi4(_a))
    # the order-4 characters mod 5 exist: {χ(2)} over the group = the four 4th roots of
    # unity (2 is a primitive root mod 5) — pins the roots-of-unity value assignment.
    # Matched NUMERICALLY as a multiset (each expected root hit exactly once): the values
    # carry ~1e-33 roundoff from e^{2πi·t·dlog/φ}, so a printed-string comparison would
    # false-fail on pure noise.
    _v5 = [c(2) for c in SAMPLE_DIRICHLET_CHARS if c.modulus == 5]
    for _t in range(4):
        if sum(1 for _v in _v5 if abs(_v - mp.mpc(0, 1) ** _t) < mp.mpf("1e-20")) != 1:
            fails.append(f"dirichlet chars mod 5: χ(2) values ≠ 4th roots of unity "
                         f"({[mp.nstr(_v, 8) for _v in _v5]})")
            break
    _cs = mp.mpc("2.3", "1.1")
    chk("Λ(1−s)=Λ(s)", _completed_riemann_zeta(1 - _cs), _completed_riemann_zeta(_cs), mp.mpf("1e-18"))
    chk("Λ(2)=π^{−1}Γ(1)ζ(2)", _completed_riemann_zeta(2), mp.pi ** -1 * mp.gamma(1) * mp.zeta(2))
    chk("Mathlib Λ(0)=Λ(1) totalization", _completed_riemann_zeta(0),
        _completed_riemann_zeta(1))
    chk("theta4 regularized Mellin @ s=2", _theta4_mellin_continuation(2),
        mp.pi / 12, mp.mpf("1e-20"))
    # ── M14 Dedekind η / Δ (η(i)=Γ(1/4)/(2π^{3/4}); Δ=η^24; S-transform) ──
    _i = mp.mpc(0, 1)
    chk("η(i)=Γ(1/4)/(2π^{3/4})", _eta(_i), mp.gamma(mp.mpf(1) / 4) / (2 * mp.pi ** (mp.mpf(3) / 4)),
        mp.mpf("1e-25"))
    _t = mp.mpc("0.4", "0.9")
    chk("etaFactor²=−iτ", _eta_factor(_t) ** 2, -_i * _t, mp.mpf("1e-25"))
    chk("η(−1/τ)=etaFactor·η(τ)", _eta(-1 / _t), _eta_factor(_t) * _eta(_t), mp.mpf("1e-22"))
    chk("Δ=η^24", _modform_discriminant(_t), _eta(_t) ** 24, mp.mpf("1e-20"))
    # slash action `SlashAction.map k γ f` (DLMF 23.15): first the WIRING of ((a,b),(c,d))
    # and the (cτ+d)^{−k} exponent against the defining formula with generic f (T: exact
    # translation, c=0,d=1; S: τ^{−k}·f(−1/τ)), then the DLMF 23.17 CONTENT anchors —
    # (Δ∣₁₂T) = Δ (q-product periodicity) and (Δ∣₁₂S) = Δ (η S-transform to the 24th power,
    # independently anchored above via η(−1/τ)=√(−iτ)η(τ)).
    chk("slash wiring T: (exp∣₅T)(τ)=exp(τ+1)", _slash_action(5, MODULAR_T, lambda w: mp.exp(w), _t),
        mp.exp(_t + 1), mp.mpf("1e-25"))
    chk("slash wiring S: (sin∣₃S)(τ)=τ⁻³sin(−1/τ)", _slash_action(3, MODULAR_S, mp.sin, _t),
        _t ** -3 * mp.sin(-1 / _t), mp.mpf("1e-25"))
    chk("(Δ∣₁₂T)=Δ (DLMF 23.17)", _slash_action(12, MODULAR_T, _modform_discriminant, _t),
        _modform_discriminant(_t), mp.mpf("1e-22"))
    chk("(Δ∣₁₂S)=Δ (DLMF 23.17)", _slash_action(12, MODULAR_S, _modform_discriminant, _t),
        _modform_discriminant(_t), mp.mpf("1e-22"))
    chk("E₂(i)=3/π", _eisenstein_E2(_i), 3 / mp.pi, mp.mpf("1e-12"))
    # Modular E₄/E₆ (τ-bindings) — anchored on values INDEPENDENT of their σ q-expansions:
    # the lemniscatic G₄(i) = Γ(1/4)⁸/(960π²) ⇒ E₄(i) = 45/π⁴·G₄(i) = 3Γ(1/4)⁸/(64π⁶);
    # the CM zeros E₆(i) = 0 (g₃ = 0) and E₄(ρ) = 0 (ρ = e^{2πi/3}, g₂ = 0); and the
    # discriminant identity (E₄³−E₆²)/1728 = η(τ)²⁴ at a generic τ (via the η binding).
    chk("E₄(i)=3Γ(1/4)⁸/(64π⁶)", _eisenstein_E4(_i),
        3 * mp.gamma(mp.mpf(1) / 4) ** 8 / (64 * mp.pi ** 6), mp.mpf("1e-22"))
    chk("E₆(i)=0 (lemniscatic)", _eisenstein_E6(_i), 0, mp.mpf("1e-22"))
    chk("E₄(ρ)=0 (equianharmonic)", _eisenstein_E4(mp.mpc(-1, mp.sqrt(3)) / 2), 0, mp.mpf("1e-22"))
    chk("(E₄³−E₆²)/1728=η²⁴", (_eisenstein_E4(_t) ** 3 - _eisenstein_E6(_t) ** 2) / 1728,
        _eta(_t) ** 24, mp.mpf("1e-20"))
    chk("σ₅(4)=1+2⁵+4⁵=1057", _divisor_sigma(5, 4), 1057)
    chk("qParam 1 z=e^{2πiz}", _qparam(1, _t), mp.exp(2 * mp.pi * _i * _t), mp.mpf("1e-25"))
    chk("nome(i)=e^{−π}", mp.exp(mp.pi * mp.j * mp.j), mp.exp(-mp.pi))
    chk("airyAiAmp(1)=e^{−⅔}/2√π", mp.e ** (-mp.mpf(2) / 3) / (2 * mp.sqrt(mp.pi)),
        mp.e ** (-(mp.mpf(2) / 3) * mp.mpf(1) ** (mp.mpf(3) / 2))
        / (2 * mp.sqrt(mp.pi) * mp.mpf(1) ** (mp.mpf(1) / 4)))
    # ── M14 per-function specials ──
    _zb = mp.mpf("3.7")
    chk("binet(1)=1−½log2π", _binet(1), 1 - mp.mpf(1) / 2 * mp.log(2 * mp.pi))
    chk("binet diff eq", _binet(_zb + 1) - _binet(_zb), 1 - (_zb + mp.mpf(1) / 2) * mp.log(1 + 1 / _zb))
    # ── N1 §5.10/5.11 coefficient tables ──
    # binetCFNum: rebuild the DLMF 5.10.1 continued fraction from the numerators and
    # match the DEFINING Binet function μ(z) at two points (decorrelated: μ from logΓ,
    # the aₙ from the Bernoulli series). 7 numerators give ~1e-16 at z=8 (DLMF 5.10 CF).
    _cfnums = [_binet_cf_num(_k) for _k in range(7)]
    chk("binetCF→μ(8)", _binet_cf_eval(_cfnums, mp.mpf(8)), _binet(mp.mpf(8)), mp.mpf("1e-14"))
    chk("binetCF→μ(12)", _binet_cf_eval(_cfnums, mp.mpf(12)), _binet(mp.mpf(12)), mp.mpf("1e-18"))
    # stirlingRecG: independent forward solve of the DLMF 5.11.5/5.11.6 recurrence;
    # the recurrence's own defining identity Σⱼ aⱼa_{k−j}/(j+1)=a_{k−1}/k at k=4.
    _sa = _stirling_seq_a(8)
    chk("stirlingRec identity k=4",
        sum(_sa[j] * _sa[4 - j] / (j + 1) for j in range(5)), _sa[3] / 4)
    chk("stirlingRecG(0)=1", _stirling_g(0), 1)
    # ratioCoeffG / symRatioCoeffH: anchor the DEFINING asymptotic relation itself, not
    # the claimed polynomials — Γ(x+a)/Γ(x+b)/x^{a−b} ≈ Σ Gₖ x^{−k} at large x, and the
    # symmetrized centred form ≈ Σ Hₖ u^{−2k}, at an asymmetric (a,b) pinning arg order.
    _ga, _gb, _gx = mp.mpf("0.7"), mp.mpf("-0.3"), mp.mpf(40)
    _lhsG = mp.gamma(_gx + _ga) / mp.gamma(_gx + _gb) / _gx ** (_ga - _gb)
    chk("ratioCoeffG asymptotic @x=40",
        _lhsG, sum(_ratio_coeff_G(_k, _ga, _gb) / _gx ** _k for _k in range(6)), mp.mpf("1e-9"))
    _gu = _gx + (_ga + _gb - 1) / 2
    _lhsH = mp.gamma(_gx + _ga) / mp.gamma(_gx + _gb) / _gu ** (_ga - _gb)
    chk("symRatioCoeffH asymptotic @x=40",
        _lhsH, sum(_sym_ratio_coeff_H(_k, _ga, _gb) / _gu ** (2 * _k) for _k in range(4)), mp.mpf("1e-9"))
    chk("besselKAmplitude(ν,0)=1", _besselK_amplitude(mp.mpf("1.7"), 0), 1)
    chk("Eₙ index trap: E₁≠E₂", mp.mpf(1) if abs(_expint_n(1, 1) - _expint_n(2, 1)) > mp.mpf("1e-3") else mp.mpf(0), 1)
    chk("upperGammaWatson Γ(1,x)=e^{−x}", _upper_gamma_watson(1, mp.mpf("1.3")), mp.e ** mp.mpf("-1.3"))
    chk("liW=Lean integral form @ x=2.4", _li_w(mp.mpf("2.4")),
        mp.e ** _rlog(mp.mpf("2.4")) * mp.quad(lambda u: mp.e ** (-_rlog(mp.mpf("2.4")) * u) / (1 + u), [0, mp.inf]),
        mp.mpf("1e-18"))
    chk("ciTail=∫cos/t", _ci_tail(mp.mpf("1.7"), mp.mpf("4.2")), mp.quad(lambda t: mp.cos(t) / t, [mp.mpf("1.7"), mp.mpf("4.2")]), mp.mpf("1e-18"))
    chk("airyG=Ai", _airy_g(mp.mpf("1.3")), mp.airyai(mp.mpf("1.3")))
    chk("airyBi rotation=Bi (DLMF 9.2.10)", _airy_bi(mp.mpf("1.3")), mp.airybi(mp.mpf("1.3")), mp.mpf("1e-15"))
    # ── M15 Weierstrass ℘ / lattice (DLMF 23) ──
    _Lw = _Lattice(1, mp.mpc("0.3", "1.1")); _Li = _Lattice(1, mp.mpc(0, 1)); _wz = mp.mpc("0.3", "0.45")
    # master self-consistency anchor: ℘'² = 4℘³ − g₂℘ − g₃ (ties ℘, ℘', g₂, g₃)
    chk("℘'²=4℘³−g₂℘−g₃", _wp_deriv(_Lw, _wz) ** 2,
        4 * _wp(_Lw, _wz) ** 3 - _g2(_Lw) * _wp(_Lw, _wz) - _g3(_Lw), mp.mpf("1e-20"))
    chk("g₃(i)=0 (lemniscatic)", _g3(_Li), 0, mp.mpf("1e-20"))
    chk("g₂=60·G₄", _g2(_Lw), 60 * _G_eisenstein(_Lw, 4))
    chk("eᵢ root of 4t³−g₂t−g₃", 4 * _e1(_Lw) ** 3 - _g2(_Lw) * _e1(_Lw) - _g3(_Lw), 0, mp.mpf("1e-18"))
    chk("Δ=g₂³−27g₃²", _wdisc(_Lw), _g2(_Lw) ** 3 - 27 * _g3(_Lw) ** 2)
    chk("Δ=1728(E₄³−E₆²), E=g₂/12,g₃/8", _wdisc(_Lw), 1728 * (_wE4(_Lw) ** 3 - _wE6(_Lw) ** 2), mp.mpf("1e-18"))
    chk("j=1728·kleinJ", _modular_invariant(_Lw), 1728 * _kleinJ(_Lw))
    _lam = mp.mpc("1.3", "-0.4")
    chk("℘ homogeneity ℘(λz;λL)=λ⁻²℘", _wp(_Lw.smul(_lam), _lam * _wz), _lam ** -2 * _wp(_Lw, _wz), mp.mpf("1e-18"))
    chk("ζ'=−℘", mp.diff(lambda t: _wzeta(_Lw, t), _wz), -_wp(_Lw, _wz), mp.mpf("1e-18"))
    chk("℘=−(log σ)''", _wp(_Lw, _wz), -mp.diff(lambda t: mp.log(_wsigma(_Lw, t)), _wz, 2), mp.mpf("1e-18"))
    # ── M16 tail: Tricomi U, generating helpers, q-series, AM coefficients ──
    chk("U(½,1,2z)=K₀/(√π e^{−z}) @1.7", _tricomiU(mp.mpf(1)/2, 1, 2*mp.mpf("1.7")),
        mp.besselk(0, mp.mpf("1.7")) / (mp.sqrt(mp.pi) * mp.e**mp.mpf("-1.7")), mp.mpf("1e-25"))
    chk("U(1,1,x)=eˣE₁(x) @1.7", _tricomiU(1, 1, mp.mpf("1.7")), mp.e**mp.mpf("1.7")*mp.e1(mp.mpf("1.7")), mp.mpf("1e-25"))
    chk("tricomiU junk-0 @ z≤0", _tricomiU(mp.mpf(1)/2, 1, -mp.mpf("1.6")), 0)
    chk("En recurrence 2E₃=e^{−x}−xE₂ @1.3", 2*_En_ascii(3, mp.mpf("1.3")),
        mp.e**mp.mpf("-1.3") - mp.mpf("1.3")*_En_ascii(2, mp.mpf("1.3")), mp.mpf("1e-25"))
    chk("multiplyingGamma(3,s)=Γ(s) @2.4", _multiplyingGamma(3, mp.mpf("2.4")), mp.gamma(mp.mpf("2.4")), mp.mpf("1e-15"))
    chk("multiplyingGamma(3,1)=1", _multiplyingGamma(3, 1), 1, mp.mpf("1e-15"))
    chk("cosGamma=cc+ssc", _cosGamma(mp.mpf("0.3"), mp.mpf("1.7"), mp.mpf("0.4")),
        mp.cos(mp.mpf("0.3"))*mp.cos(mp.mpf("1.7")) + mp.sin(mp.mpf("0.3"))*mp.sin(mp.mpf("1.7"))*mp.cos(mp.mpf("0.4")))
    # Rodrigues vs independent mp.legendre (genuine cross-check), and generating telescopes
    chk("Rodrigues P₃=rodriguesPoly/(2³·3!)", _rodrigues_poly(3, mp.mpf("0.4")) / (2**3 * 6),
        mp.legendre(3, mp.mpf("0.4")))
    chk("Uval=chebyu", _uval(mp.mpf("0.4"), 3), mp.chebyu(3, mp.mpf("0.4")))
    chk("genClosed=(1−2xt+t²)^{−½}", _gen_closed(mp.mpf("0.3"), mp.mpf("0.2")),
        _gen_quad(mp.mpf("0.3"), mp.mpf("0.2")) ** (-mp.mpf(1)/2))
    chk("a0Approx(0)=0", _a0_approx(0), 0)
    # Mathieu small-q approximants (DLMF 28.6.2–28.6.5): q=0 anchors are the exact
    # characteristic base values aₙ(0)=bₙ(0)=n² (DLMF 28.2.23/28.2.24).
    chk("a1Approx(0)=1", _a1_approx(0), 1)
    chk("b1Approx(0)=1", _b1_approx(0), 1)
    chk("a2Approx(0)=4", _a2_approx(0), 4)
    chk("b2Approx(0)=4", _b2_approx(0), 4)
    # degenerate-pair splitting: a₁(q)−b₁(q) = 2q − (1/32)q³ exactly for the cubic
    # truncations (both DLMF series share the ±q, ±(1/64)q³ terms) — sign-convention anchor.
    chk("a1Approx−b1Approx=2q−q³/32 @0.3", _a1_approx(mp.mpf("0.3")) - _b1_approx(mp.mpf("0.3")),
        2 * mp.mpf("0.3") - mp.mpf(1) / 32 * mp.mpf("0.3") ** 3)
    # independent cross-check (when scipy is present): the truncated polynomials track
    # scipy's Mathieu characteristic values to the next DLMF term, ≲1e-7 at q=0.1 —
    # a convention slip (a↔b, q-scaling) would show up at O(1) or O(q²)≈1e-2.
    try:
        import scipy.special as _sp_mathieu
    except ImportError:
        _sp_mathieu = None
    if _sp_mathieu is not None:
        _qm = mp.mpf("0.1")
        chk("a0Approx≈scipy a₀ @0.1", _a0_approx(_qm), mp.mpf(repr(_sp_mathieu.mathieu_a(0, 0.1))), mp.mpf("1e-6"))
        chk("a1Approx≈scipy a₁ @0.1", _a1_approx(_qm), mp.mpf(repr(_sp_mathieu.mathieu_a(1, 0.1))), mp.mpf("1e-6"))
        chk("b1Approx≈scipy b₁ @0.1", _b1_approx(_qm), mp.mpf(repr(_sp_mathieu.mathieu_b(1, 0.1))), mp.mpf("1e-6"))
        chk("a2Approx≈scipy a₂ @0.1", _a2_approx(_qm), mp.mpf(repr(_sp_mathieu.mathieu_a(2, 0.1))), mp.mpf("1e-6"))
        chk("b2Approx≈scipy b₂ @0.1", _b2_approx(_qm), mp.mpf(repr(_sp_mathieu.mathieu_b(2, 0.1))), mp.mpf("1e-6"))
    # unconditional independent cross-check (mpmath-only, runs even without scipy):
    # Hill tridiagonal-matrix eigenvalues from the DLMF 28.4 defining recurrences.
    # At q=0.1 the truncated polynomials agree to the next DLMF series term (≲7e-8);
    # any convention slip (a↔b swap, q-scaling, coefficient sign) shows at ≥O(q³)≈3e-5.
    _qh = mp.mpf("0.1")
    chk("a0Approx≈Hill a₀ @0.1", _a0_approx(_qh), _mathieu_hill_eigs("ce_even", _qh)[0], mp.mpf("1e-6"))
    chk("a1Approx≈Hill a₁ @0.1", _a1_approx(_qh), _mathieu_hill_eigs("ce_odd", _qh)[0], mp.mpf("1e-6"))
    chk("b1Approx≈Hill b₁ @0.1", _b1_approx(_qh), _mathieu_hill_eigs("se_odd", _qh)[0], mp.mpf("1e-6"))
    chk("a2Approx≈Hill a₂ @0.1", _a2_approx(_qh), _mathieu_hill_eigs("ce_even", _qh)[1], mp.mpf("1e-6"))
    chk("b2Approx≈Hill b₂ @0.1", _b2_approx(_qh), _mathieu_hill_eigs("se_even", _qh)[0], mp.mpf("1e-6"))
    # Mathieu operator (DLMF 28.2.1): mathieuOp a q y x = y'' + (a − 2q cos 2x)·y.
    # Anchor 1 — harmonic-oscillator degeneration (DLMF 28.2.1 at q=0, y=cos 3x, a=9=3²):
    # the operator must annihilate cos(nx) exactly, validating the mp.diff y'' path + a·y.
    chk("mathieuOp(9,0,cos3x)=0 @0.7", _mathieu_op(9, 0, lambda t: mp.cos(3 * t), mp.mpf("0.7")),
        0, mp.mpf("1e-20"))
    # Anchor 2 — generic non-Fourier y=e^{sin x} against the hand-computed defining formula
    # y''=(cos²x−sin x)e^{sin x}: decorrelated from any FLMF cos/sin-mode theorem, and pins
    # the potential's sign/argument (a−2q·cos 2x, NOT a+…, NOT cos x).
    _mx, _ma, _mq = mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf("0.4")
    chk("mathieuOp(a,q,e^{sin x}) 28.2.1 @0.7",
        _mathieu_op(_ma, _mq, lambda t: mp.e ** mp.sin(t), _mx),
        mp.e ** mp.sin(_mx) * (mp.cos(_mx) ** 2 - mp.sin(_mx) + _ma - 2 * _mq * mp.cos(2 * _mx)),
        mp.mpf("1e-20"))
    # mathieu_orthogonal ∀-function witness: y₁ = ce₁(·,0) = cos x (a₁ = 1),
    # y₂ = ce₂(·,0) = cos 2x (a₂ = 4).  Anchor EVERY hypothesis of the Sturm–Liouville
    # surface at the witness — the supplied derivative data really are the derivatives,
    # the Mathieu ODE 28.2.1 holds with the DLMF characteristic values aₘ(0) = m²
    # (= a1Approx(0)/a2Approx(0), tying the witness to the 28.6 anchors above), and the
    # values/first derivatives are 2π-periodic.  a₁ = 1 ≠ 4 = a₂ holds by inspection.
    _wx = mp.mpf("0.7")
    _wit = {k: REGISTRY[k][1] for k in ("y₁", "dy₁", "ddy₁", "y₂", "dy₂", "ddy₂")}
    chk("witness dy₁ = y₁' @0.7", _wit["dy₁"](_wx), mp.diff(_wit["y₁"], _wx))
    chk("witness ddy₁ = y₁'' @0.7", _wit["ddy₁"](_wx), mp.diff(_wit["y₁"], _wx, 2))
    chk("witness dy₂ = y₂' @0.7", _wit["dy₂"](_wx), mp.diff(_wit["y₂"], _wx))
    chk("witness ddy₂ = y₂'' @0.7", _wit["ddy₂"](_wx), mp.diff(_wit["y₂"], _wx, 2))
    chk("witness ODE 28.2.1: ddy₁ = −(a₁−0)·y₁, a₁ = a1Approx(0)", _wit["ddy₁"](_wx),
        -(_a1_approx(0) - 0) * _wit["y₁"](_wx))
    chk("witness ODE 28.2.1: ddy₂ = −(a₂−0)·y₂, a₂ = a2Approx(0)", _wit["ddy₂"](_wx),
        -(_a2_approx(0) - 0) * _wit["y₂"](_wx))
    chk("mathieuOp(1,0,y₁)=0 @0.7 (independent operator route)",
        _mathieu_op(1, 0, _wit["y₁"], _wx), 0, mp.mpf("1e-20"))
    chk("mathieuOp(4,0,y₂)=0 @0.7 (independent operator route)",
        _mathieu_op(4, 0, _wit["y₂"], _wx), 0, mp.mpf("1e-20"))
    for _wnm in ("y₁", "dy₁", "y₂", "dy₂"):
        chk(f"witness {_wnm}(2π) = {_wnm}(0)", _wit[_wnm](2 * mp.pi), _wit[_wnm](0))
    # angular-momentum coefficients
    chk("triangleCoeff(2,1,1)=√(1/30)", _triangle_coeff(2, 1, 1), mp.sqrt(mp.mpf(1)/30))
    chk("triangleCoeff(1,1,3)=0 (triangle violated)", _triangle_coeff(1, 1, 3), 0)
    chk("ifact(4)=24", _ifact(4), 24)
    chk("ifact(-1)=0 (junk-0)", _ifact(-1), 0)
    chk("triangle6j(0,0,0)=1", _triangle6j(0, 0, 0), 1)
    chk("triangle6j(1,1,3)=0", _triangle6j(1, 1, 3), 0)
    if _HAVE_SYMPY:
        chk("6j orthogonality ∑(2x+1){}{} = 1/3 @(1,1,1,1,1,1)",
            _wigner6j_orth_sum(1, 1, 1, 1, 1, 1), mp.mpf(1)/3, mp.mpf("1e-20"))
        chk("6j orthogonality off-diag = 0 @(1,1,1,1,1,2)",
            _wigner6j_orth_sum(1, 1, 1, 1, 1, 2), 0, mp.mpf("1e-20"))
        chk("9j(1,1,2,1,1,2,2,2,2)=−1/150", _wigner9j(1, 1, 2, 1, 1, 2, 2, 2, 2),
            mp.mpf(-1)/150, mp.mpf("1e-25"))
        chk("9j_eq: symbol = ∑ wigner9jTerm",
            mp.fsum(_wigner9j_term(1, 1, 2, 1, 1, 2, 2, 2, 2, x) for x in range(13)),
            _wigner9j(1, 1, 2, 1, 1, 2, 2, 2, 2), mp.mpf("1e-25"))
        chk("biedenharnElliottSum(0…)=1", _biedenharn_elliott_sum(0, 0, 0, 0, 0, 0, 0, 0, 0), 1, mp.mpf("1e-25"))
        chk("orthSum diag=1", _orth_sum(1, 1, 1, 1, 0, 0), 1, mp.mpf("1e-25"))
        chk("orthSum off-diag (m₃≠m₃')=0", _orth_sum(1, 1, 1, 1, 0, 1), 0, mp.mpf("1e-25"))
    # ── M17 tail: Clausen / Lobachevsky / Riemann ξ / Jacobi amplitude ──
    _cth = mp.mpf("0.9")
    chk("Cl_2 = Im Li₂(e^{iθ})", _clausen_cl2(_cth),
        mp.polylog(2, mp.e ** (mp.mpc(0, 1) * _cth)).imag, mp.mpf("1e-25"))
    chk("lobachevsky = ½·Cl_2(2θ)", _lobachevsky(_cth), mp.mpf(1) / 2 * _clausen_cl2(2 * _cth))
    _xs = mp.mpc("2.3", "1.1")
    chk("ξ(1−s)=ξ(s)", _riemann_xi(1 - _xs), _riemann_xi(_xs), mp.mpf("1e-18"))
    chk("ξ(s)=½s(s−1)Λ(s)", _riemann_xi(_xs),
        mp.mpf(1) / 2 * _xs * (_xs - 1) * _completed_riemann_zeta(_xs))
    _au, _ak = mp.mpf("0.8"), mp.mpf("0.6")
    chk("sin(am u k)=sn(u,k)", mp.sin(_jacobi_am(_au, _ak)), mp.ellipfun("sn", _au, _ak ** 2), mp.mpf("1e-25"))
    chk("am'(u)=dn(u,k)", mp.diff(lambda uu: _jacobi_am(uu, _ak), _au),
        mp.ellipfun("dn", _au, _ak ** 2), mp.mpf("1e-15"))
    chk("am(u,0)=u", _jacobi_am(_au, 0), _au)
    # ── M18: ₁F₁ / Rodrigues / double factorial / Fresnel ──
    _zk = mp.mpf("1.3")
    chk("₁F₁(1,2,z)=(eᶻ−1)/z", _kummerM(1, 2, _zk), (mp.e ** _zk - 1) / _zk, mp.mpf("1e-25"))
    chk("₁F₁(1,1,z)=eᶻ", _kummerM(1, 1, _zk), mp.e ** _zk, mp.mpf("1e-25"))
    _zg = mp.mpf("0.4")
    chk("₂F₁(1,1,2,z)=−log(1−z)/z", _gaussF(1, 1, 2, _zg), -mp.log(1 - _zg) / _zg, mp.mpf("1e-25"))
    chk("legendreHG = Pₙ via ₂F₁(−n,n+1;1;(1−x)/2)", _gaussF(-3, 4, 1, (1 - mp.mpf("0.6")) / 2),
        mp.legendre(3, mp.mpf("0.6")), mp.mpf("1e-22"))
    chk("₂F₁ coeff (a)ₖ(b)ₖ/((c)ₖk!) @ (2,3,4,2)", _gaussF_coeff(2, 3, 4, 2),
        mp.rf(2, 2) * mp.rf(3, 2) / (mp.rf(4, 2) * 2), mp.mpf("1e-25"))
    # §15.2(ii) principal-continuation bindings (self-anchored to the DLMF DEFINING formulas)
    _pa, _pb, _pc = mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf("2.1")
    chk("principalOlver = ₂F₁/Γ(c) (bold-F, DLMF 15.2.2)",
        _principalOlver(_pa, _pb, _pc, _zg), mp.hyp2f1(_pa, _pb, _pc, _zg) / mp.gamma(_pc),
        mp.mpf("1e-25"))
    # DLMF 15.2.3 cut jump: 𝐅(x+i0)−𝐅(x−i0) = 2πi/(Γa Γb)·(x−1)^{c−a−b}·𝐅(c−a,c−b;c−a−b+1;1−x)
    _px = mp.mpf("1.8")
    chk("principalOlver boundary jump = DLMF 15.2.3 RHS",
        _principalOlverBoundary(+1)(_pa, _pb, _pc, _px)
        - _principalOlverBoundary(-1)(_pa, _pb, _pc, _px),
        2 * mp.pi * 1j / (mp.gamma(_pa) * mp.gamma(_pb)) * mp.power(_px - 1, _pc - _pa - _pb)
        * _principalOlver(_pc - _pa, _pc - _pb, _pc - _pa - _pb + 1, 1 - _px),
        mp.mpf("1e-9"))
    # gaussSingularIterated (DLMF 15.2.5 iterated limit) vs an INDEPENDENT small-ε evaluation
    # of that iterated limit: inner a=−m exact, outer c=−m−ℓ+ε.
    chk("gaussSingularIterated = iterated ε-limit of ₂F₁ (DLMF 15.2.4/5)",
        _gaussSingularIterated(2, 1, _pb, _zg),
        mp.hyp2f1(-mp.mpf(2), _pb, -mp.mpf(3) + mp.mpf("1e-15"), _zg), mp.mpf("1e-12"))
    # bernoulliPoly = Polynomial.bernoulli: B₁(x)=x−½, B₂(x)=x²−x+⅙, B₂(0)=B₂=1/6
    chk("bernoulliPoly₁(x)=x−½", mp.bernpoly(1, mp.mpf("0.7")), mp.mpf("0.7") - mp.mpf("0.5"))
    chk("bernoulliPoly₂(x)=x²−x+⅙", mp.bernpoly(2, mp.mpf("0.7")),
        mp.mpf("0.7") ** 2 - mp.mpf("0.7") + mp.mpf(1) / 6)
    chk("bernoulliPoly₂(0)=B₂=1/6", mp.bernpoly(2, 0), mp.mpf(1) / 6)
    # bR n t = Bₙ(t) (Duplication.lean) — exercise the REGISTRY callable itself, anchored to
    # the real Bernoulli polynomial (B₀=1, B₁(t)=t−½, B₂(t)=t²−t+⅙); also re-pin the DLMF
    # 24.4.13 duplication identity B₂(t/2)+B₂((t+1)/2)=2^{1−2}B₂(t) the `dupl` row asserts.
    _bR = REGISTRY["bR"][1]
    chk("bR 0 t = 1", _bR(0, mp.mpf("0.7")), mp.mpf(1))
    chk("bR 1 t = t−½", _bR(1, mp.mpf("0.7")), mp.mpf("0.7") - mp.mpf("0.5"))
    chk("bR 2 t = t²−t+⅙", _bR(2, mp.mpf("0.3")),
        mp.mpf("0.3") ** 2 - mp.mpf("0.3") + mp.mpf(1) / 6)
    chk("dupl 24.4.13 @ n=2", _bR(2, mp.mpf("0.3") / 2) + _bR(2, (mp.mpf("0.3") + 1) / 2),
        (mp.mpf(2) / 2 ** 2) * _bR(2, mp.mpf("0.3")))
    chk("kummerCoefficient(1,2,2)=1/6", _kummerCoefficient(1, 2, 2), mp.mpf(1) / 6)
    chk("5‼=15", _double_factorial(5), 15); chk("0‼=1", _double_factorial(0), 1)
    chk("laguerreRodrigues 3 = L₃", _laguerreRodrigues(3, mp.mpf("0.4")),
        mp.laguerre(3, 0, mp.mpf("0.4")), mp.mpf("1e-7"))
    chk("hermitePearson.rodrigues 3 = He₃", _hermitePearson_rodrigues(3, mp.mpf("0.6")),
        _hermite_prob(3, mp.mpf("0.6")), mp.mpf("1e-7"))
    # Pearson-system witness anchors (abstract DLMF 18.5.5 surface, rodrigues_spec):
    # the 18.5.5 defining identity κₙ·w(x)·pₙ(x) = dⁿ/dxⁿ[w·Fⁿ](x) at the Hermite-He
    # row (n=2, x=2: both sides = 3e⁻², the hand-checked anchor), the Pearson equation
    # (w·F)′ = w·τ with τ = −x, and the κ₃/κ₀ table values — validated BEFORE the sweep
    # trusts the witness instantiation.
    chk("Pearson 18.5.5 He-row LHS n=2 x=2 = 3e⁻²",
        _hermitePearson_norm(2) * _hermitePearson_w(mp.mpf(2)) * _hermite_prob(2, mp.mpf(2)),
        3 * mp.e ** -2)
    chk("Pearson 18.5.5 He-row RHS d²/dx²[w·F²](2) = 3e⁻²",
        mp.diff(lambda t: _hermitePearson_kernel(2, t), mp.mpf(2), 2),
        3 * mp.e ** -2, mp.mpf("1e-7"))
    chk("Pearson eq (w·F)′=−x·w @0.7", mp.diff(_hermitePearson_w, mp.mpf("0.7")),
        -mp.mpf("0.7") * _hermitePearson_w(mp.mpf("0.7")), mp.mpf("1e-12"))
    chk("Pearson κ₀ = 1", _hermitePearson_norm(0), 1)
    chk("Pearson κ₃ = −1", _hermitePearson_norm(3), -1)
    _xf = mp.mpf("1.7")
    chk("fresnelC = ∫₀ˣcos(πt²/2)", mp.fresnelc(_xf),
        mp.quad(lambda t: mp.cos(mp.pi * t ** 2 / 2), [0, _xf]), mp.mpf("1e-20"))
    chk("fresnelS = ∫₀ˣsin(πt²/2)", mp.fresnels(_xf),
        mp.quad(lambda t: mp.sin(mp.pi * t ** 2 / 2), [0, _xf]), mp.mpf("1e-20"))
    # §7.12/§7.17 helpers (decorrelated anchors):
    #   (½)_m matches Γ(½+m)/Γ(½);  truncF/truncG match their m=0 leading terms;
    #   f − truncF → 0 as x→∞ (the remainder shrinks);  inverfCoeff a₀..a₃ = 1,⅓,7/30,127/630;
    #   asymV/asymA against the closed forms in v.
    chk("(½)_4 = Γ(½+4)/Γ(½)", _pochHalf(4), mp.gamma(mp.mpf(1)/2 + 4) / mp.gamma(mp.mpf(1)/2))
    _xt = mp.mpf("2.5")
    chk("truncF 1 = 1/(πx)", _truncF(1, _xt), 1 / (mp.pi * _xt))
    chk("truncG 1 = 1/(π²x³)", _truncG(1, _xt), 1 / (mp.pi ** 2 * _xt ** 3))
    chk("remF integral = auxF − truncF (7.12.4/.6)", _remF(2, _xt), _cfresnelAuxF(_xt) - _truncF(2, _xt))
    chk("remG integral = auxG − truncG (7.12.5/.7)", _remG(2, _xt), _cfresnelAuxG(_xt) - _truncG(2, _xt))
    chk("inverfCoeff 1 = 1/3", _inverf_coeff(1), mp.mpf(1) / 3)
    chk("inverfCoeff 2 = 7/30", _inverf_coeff(2), mp.mpf(7) / 30)
    chk("inverfCoeff 3 = 127/630", _inverf_coeff(3), mp.mpf(127) / 630)
    _xv = mp.mpf("0.1")
    chk("asymU = −2/ln(π x² ln(1/x))", _asymU(_xv),
        -2 / mp.log(mp.pi * _xv ** 2 * mp.log(1 / _xv)))
    # asymptotic consistency (DLMF 7.17.3 leading term): inverfc x ≈ asymU^{−1/2} as x→0⁺
    chk("inverfc ≈ asymU^{−1/2} (7.17.3 lead)", mp.erfinv(1 - mp.mpf("1e-8")),
        _asymU(mp.mpf("1e-8")) ** (mp.mpf(-1) / 2), mp.mpf("2e-2"))
    chk("asymV = ln ln(1/x) − 2 + ln π", _asymV(_xv),
        mp.log(mp.log(1 / _xv)) - 2 + mp.log(mp.pi))
    chk("asymA 2 = v/8", _asymA(_xv, 2), _asymV(_xv) / 8)
    chk("asymA 3 = −(v²+6v−6)/32", _asymA(_xv, 3),
        -(_asymV(_xv) ** 2 + 6 * _asymV(_xv) - 6) / 32)
    # repeated-integral families: i⁰erfc=erfc, d/dx i¹erfc=−erfc; Ki₀=K₀, d/dx Ki₁=−K₀
    _xe = mp.mpf("0.7")
    chk("iRepErfc 0 = erfc", _iRepErfc(0, _xe), mp.erfc(_xe), mp.mpf("1e-20"))
    chk("d/dx iRepErfc 1 = −erfc", mp.diff(lambda t: _iRepErfc(1, t), _xe), -mp.erfc(_xe), mp.mpf("1e-12"))
    chk("bickleyKi 0 = K₀", _bickleyKi(0, _xe), mp.besselk(0, _xe))
    chk("d/dx bickleyKi 1 = −K₀", mp.diff(lambda t: _bickleyKi(1, t), _xe), -mp.besselk(0, _xe), mp.mpf("1e-12"))
    # Airy phase derivative (DLMF 9.8.13) at the canonical pair: θ'=(Ai'Bi−AiBi')/(Ai²+Bi²)=−1/(πM²)
    _xa = mp.mpf("0.7")
    _ai, _bi, _aip, _bip = mp.airyai(_xa), mp.airybi(_xa), mp.airyai(_xa, 1), mp.airybi(_xa, 1)
    chk("airy phase θ' = (Ai'Bi−AiBi')/(Ai²+Bi²)", mp.diff(lambda t: mp.atan(mp.airyai(t) / mp.airybi(t)), _xa),
        (_aip * _bi - _ai * _bip) / (_ai ** 2 + _bi ** 2), mp.mpf("1e-12"))
    chk("airy θ' = −1/(πM²) (Wronskian 1/π)", mp.diff(lambda t: mp.atan(mp.airyai(t) / mp.airybi(t)), _xa),
        -1 / (mp.pi * (_ai ** 2 + _bi ** 2)), mp.mpf("1e-12"))
    # ── M19: real-order Bessel K + Tricomi bridge + variance-c Hermite ──
    _bn, _bz = mp.mpf("1.3"), mp.mpf("1.7")
    chk("besselK_real(0,z)=K₀", _besselK_real(0, _bz), mp.besselk(0, _bz))
    chk("besselK_real=tricomiBridgeFun (DLMF 13.6.10)", _besselK_real(_bn, _bz),
        _tricomi_bridge_fun(_bn, _bz), mp.mpf("1e-22"))
    chk("probHermite(2,1,x)=x²−1 (=He₂)", _prob_hermite(2, 1, mp.mpf("0.7")), mp.mpf("0.7") ** 2 - 1)
    chk("probHermite(2,c,x)=x²−c", _prob_hermite(2, mp.mpf("1.3"), mp.mpf("0.7")),
        mp.mpf("0.7") ** 2 - mp.mpf("1.3"))
    # ── Dirichlet-character count (Nat.card (DirichletCharacter ℂ k), DLMF §27.8 text
    # preceding 27.8.6) — anchor _dirichlet_char_count against an EXHAUSTIVE brute-force
    # homomorphism count: enumerate ALL maps (ℤ/kℤ)* → μ_e (e = group exponent, values as
    # additive exponents mod e) and keep those with χ(ab) = χ(a)χ(b). No primitive root,
    # no discrete log, no totient formula enters this count — fully decorrelated from both
    # the binding's construction and the sweep's φ(k) side.
    def _brute_char_count(k):
        from math import gcd
        from itertools import product as _prod
        if k == 1:
            return 1                        # trivial group: exactly one character mod 1
        units = [a for a in range(1, k) if gcd(a, k) == 1]

        def _order(a):
            x, o = a, 1
            while x != 1:
                x = (x * a) % k; o += 1
            return o
        e = 1
        for a in units:
            o = _order(a)
            e = e * o // gcd(e, o)          # lcm (math.lcm needs ≥ 3.9)
        idx = {a: i for i, a in enumerate(units)}
        return sum(1 for f in _prod(range(e), repeat=len(units))
                   if all((f[idx[a]] + f[idx[b]] - f[idx[(a * b) % k]]) % e == 0
                          for a in units for b in units))
    for _kc in (1, 2, 3, 4, 5, 6, 10):      # cyclic (ℤ/kℤ)* — covers the sweep's N grid {1,2,3,5}
        chk(f"charCount({_kc}) = brute-force hom count", _dirichlet_char_count(_kc),
            _brute_char_count(_kc))
        chk(f"charCount({_kc}) = φ({_kc})", _dirichlet_char_count(_kc), _totient(_kc))
    for _kc in (0, 8, 12):                  # k=0 / non-cyclic (ℤ/kℤ)* → honest None skip
        if _dirichlet_char_count(_kc) is not None:
            fails.append(f"charCount({_kc}): expected None (honest skip), got a value")
    chk("brute hom count(8) = φ(8) = 4 (skip is conservative, not a disagreement)",
        _brute_char_count(8), 4)
    # the enumerated characters mod 5 really are φ(5)=4 DISTINCT multiplicative characters
    _ch5 = _dirichlet_chars(5)
    chk("chars(5): |list| = 4", len(_ch5), 4)
    for _i in range(len(_ch5)):
        chk(f"chars(5)[{_i}] multiplicative χ(2·3)=χ(2)χ(3)", _ch5[_i](2 * 3),
            _ch5[_i](2) * _ch5[_i](3))
        chk(f"chars(5)[{_i}] vanishes off units χ(0)=0", _ch5[_i](0), 0)
        for _j in range(_i + 1, len(_ch5)):
            if abs(_ch5[_i](2) - _ch5[_j](2)) < mp.mpf("1e-9"):
                fails.append(f"chars(5): characters {_i},{_j} coincide at the generator 2")
    # ── ∀-quantified Dirichlet-character instantiation (_dirichlet_char_sample, DLMF §27.8):
    # every sampled character over the sweep's moduli grid {5,7,9,11} (+ the χ₄ anchor
    # modulus 4) must satisfy the DEFINING relations 27.8.1–27.8.4 — anchored to the
    # formulas, never by name.
    from math import gcd as _vgcd
    for _kd in (4, 5, 7, 9, 11):
        for _td in SAMPLE_DIRICHLET_TS:
            _chi = _dirichlet_char_sample(_kd, _td)
            if _chi is None:
                fails.append(f"dirichletCharSample({_kd},{_td}): None on a cyclic modulus")
                continue
            chk(f"27.8.1 χ(1)=1 mod {_kd} t={_td}", _chi(1), 1)
            for _m in range(_kd):
                chk(f"27.8.3 χ(n+k)=χ(n) mod {_kd} t={_td} n={_m}", _chi(_m + _kd), _chi(_m))
                if _vgcd(_m, _kd) != 1:
                    chk(f"27.8.4 χ(n)=0, (n,k)>1 mod {_kd} t={_td} n={_m}", _chi(_m), 0)
                for _n in range(_kd):
                    chk(f"27.8.2 χ(mn)=χ(m)χ(n) mod {_kd} t={_td} ({_m},{_n})",
                        _chi(_m * _n), _chi(_m) * _chi(_n))
            # orthogonality column (DLMF 27.8.6, a≠1): ∑_{n mod k} χ(n) = 0 for χ ≠ χ₀,
            # = φ(k) for the principal character (t wraps mod φ(k): mod 4 has φ=2, so
            # t=2 IS χ₀ — a legitimate instance of the ∀χ binder, summed accordingly).
            _phi_kd = int(_dirichlet_char_count(_kd))
            chk(f"27.8.6 ∑ₙχ(n) mod {_kd} t={_td}",
                mp.fsum(_chi(_n) for _n in range(_kd)),
                _phi_kd if _td % _phi_kd == 0 else 0)
    # decorrelated concrete anchors: mod 4 the unique nontrivial character IS ZMod.χ₄
    # (independently implemented above from the residue table), and the ORDER-2 character
    # mod 5 is the Legendre symbol (n|5) — squares {1,4} → +1, non-residues {2,3} → −1.
    for _n4 in (0, 1, 2, 3):
        chk(f"dirichletCharSample(4,1) = χ₄ @ {_n4}", _dirichlet_char_sample(4, 1)(_n4), _chi4(_n4))
    _leg5 = _dirichlet_char_sample(5, 2)          # t=2 of φ=4: the quadratic character
    for _n5, _v5 in ((1, 1), (2, -1), (3, -1), (4, 1), (0, 0)):
        chk(f"dirichletCharSample(5,2) = Legendre(·|5) @ {_n5}", _leg5(_n5), _v5)
    # non-cyclic modulus → honest None skip, never a fabricated character
    if _dirichlet_char_sample(8, 1) is not None or _dirichlet_char_sample(None, 1) is not None:
        fails.append("dirichletCharSample: expected None on non-cyclic/missing modulus")
    # ── character Gauss sum (Mathlib `gaussSum χ ψ` on MulChar/AddChar binders;
    # DLMF 27.10.9–27.10.11). First the ADDITIVE-character defining relations for every
    # grid sample: ψ(0)=1, additivity ψ(a+b)=ψ(a)ψ(b) (exhaustive over the carrier),
    # period k, and the explicit 27.10.9 kernel value ψ₁(1) = e^{2πi/k}.
    for _ka in (5, 7):
        for _na in SAMPLE_ADDCHAR_NS:
            _psi = _addchar_sample(_ka, _na)
            chk(f"addChar ψ(0)=1 mod {_ka} n={_na}", _psi(0), 1)
            chk(f"addChar period ψ(3+k)=ψ(3) mod {_ka} n={_na}", _psi(3 + _ka), _psi(3))
            for _aa in range(_ka):
                for _ba in range(_ka):
                    chk(f"addChar ψ(a+b)=ψ(a)ψ(b) mod {_ka} n={_na} ({_aa},{_ba})",
                        _psi(_aa + _ba), _psi(_aa) * _psi(_ba))
        chk(f"addChar ψ₁(1)=e^(2πi/{_ka}) (27.10.9 kernel)", _addchar_sample(_ka, 1)(1),
            mp.e ** (2 * mp.pi * mp.j / _ka))
    # classical quadratic Gauss sums (Gauss's sign theorem — decorrelated closed values):
    # G(1,(·|5)) = +√5 (p ≡ 1 mod 4), G(1,(·|7)) = i√7 (p ≡ 3 mod 4). t=2 of φ(5)=4 and
    # t=3 of φ(7)=6 are the quadratic (Legendre) characters of the generator-power
    # enumeration (the mod-5 one is pinned to (·|5) value-by-value just above).
    chk("G(1,(·|5)) = √5 (27.10.9 @ Legendre mod 5)",
        _gauss_sum_char(_mulchar_sample(5, 2), _addchar_sample(5, 1)), mp.sqrt(5))
    chk("G(1,(·|7)) = i√7 (27.10.9 @ Legendre mod 7)",
        _gauss_sum_char(_mulchar_sample(7, 3), _addchar_sample(7, 1)), mp.j * mp.sqrt(7))
    # every sweep-grid pair: |G(1,χ)|² = k (27.10.11; χ nonprincipal mod a prime is
    # primitive) and separability G(n,χ) = χ̄(n)·G(1,χ) (27.10.10).
    for (_km, _tm) in SAMPLE_MULCHAR_KTS:
        _chim = _mulchar_sample(_km, _tm)
        _g1 = _gauss_sum_char(_chim, _addchar_sample(_km, 1))
        chk(f"|G(1,χ)|² = k (27.10.11) mod {_km} t={_tm}", abs(_g1) ** 2, _km)
        for _nn in SAMPLE_ADDCHAR_NS:
            chk(f"G(n,χ) = χ̄(n)G(1,χ) (27.10.10) mod {_km} t={_tm} n={_nn}",
                _gauss_sum_char(_chim, _addchar_sample(_km, _nn)), mp.conj(_chim(_nn)) * _g1)
    # ── concrete-binder hypothesis tags (`χ ≠ 1` / `e.IsPrimitive` of DLMF 27.8.6 rows,
    # GaussSumDirichlet.lean) — each tag anchored against its DEFINING property by brute
    # force over the carrier, never against the formula that computed it. ─────────────
    # `.principal` on _mulchar_sample ⟺ χ ≡ 1 on EVERY unit (Lean `(1 : MulChar …)`):
    from math import gcd as _vgcd2
    for _kp in (3, 5, 7):
        for _tp in range(int(_dirichlet_char_count(_kp))):
            _chp = _mulchar_sample(_kp, _tp)
            _brute_prin = all(abs(_chp(_a) - 1) < mp.mpf("1e-20")
                              for _a in range(1, _kp) if _vgcd2(_a, _kp) == 1)
            if bool(getattr(_chp, "principal", None)) != _brute_prin:
                fails.append(f"mulcharSample(.principal) mod {_kp} t={_tp}: tag "
                             f"{getattr(_chp, 'principal', None)} ≠ brute-force {_brute_prin}")
    # `.primitive` on _addchar_sample ⟺ every nonzero shift a ↦ ψ(ax) is nontrivial
    # (Mathlib `AddChar.IsPrimitive` over ZMod k):
    for _kp in (5, 6, 7, 9):
        for _np in (0, 1, 2, 3):
            _psp = _addchar_sample(_kp, _np)
            _brute_prim = all(any(abs(_psp(_a * _x) - 1) > mp.mpf("1e-9")
                                  for _x in range(_kp)) for _a in range(1, _kp))
            if bool(getattr(_psp, "primitive", None)) != _brute_prim:
                fails.append(f"addcharSample(.primitive) mod {_kp} n={_np}: tag "
                             f"{getattr(_psp, 'primitive', None)} ≠ brute-force {_brute_prim}")
    # the DLMF 27.8.6 magnitude in the exact Lean form of gaussSum_mul_conj_eq_card:
    # G·conj(G) = p for nontrivial χ mod PRIME p and primitive ψ (Fintype.card (ZMod p) = p).
    for _kp, _tp, _np in ((5, 1, 1), (5, 2, 2), (7, 1, 2), (11, 2, 1), (3, 1, 1)):
        _chp, _psp = _mulchar_sample(_kp, _tp), _addchar_sample(_kp, _np)
        _gp = _gauss_sum_char(_chp, _psp)
        chk(f"G·conj(G) = p (27.8.6) mod {_kp} t={_tp} n={_np}", _gp * mp.conj(_gp), _kp)
    # ── Complex.normSq: the DEFINING re² + im² against the independent z·z̄ (and the
    # closed |3+4i|² = 25), then the full §27.8 magnitude path normSq(G(χ, ψ₁)) = p at
    # the canonical prime instantiations p = 7, 11 (ψ₁ = x ↦ e^{2πix/p} primitive,
    # χ = the t-th nontrivial character mod p) — the exact shape of the swept Lean row
    # `normSq_gaussSum : Complex.normSq (gaussSum χ e) = p` (GaussSumDirichlet.lean). ──
    _nsq = REGISTRY["Complex.normSq"][1]
    chk("normSq(3+4i) = 25 (defining re²+im²)", _nsq(mp.mpc(3, 4)), 25)
    for _zq in (mp.mpc("1.7", "-0.4"), mp.mpc("-2.3", "0.9")):
        chk(f"normSq(z) = z·z̄ @ {_zq}", _nsq(_zq), _zq * mp.conj(_zq))
    for _kp in (7, 11):
        for _tp in (1, 2):
            chk(f"normSq(G(χ,ψ₁)) = p (27.8 magnitude) mod {_kp} t={_tp}",
                _nsq(_gauss_sum_char(_mulchar_sample(_kp, _tp), _addchar_sample(_kp, 1))), _kp)
    # ── A2 Bessel/Struve/Kelvin/Lommel/Anger cluster anchors ─────────────────────────
    # Anger integrand (DLMF 11.10.1): (1/π)∫₀^π of the BOUND integrand = mp.angerj at
    # NON-integer ν — where Anger ≠ Bessel J, so a J-based rival integrand is rejected.
    _av, _az = mp.mpf("0.4"), mp.mpf("1.1")
    chk("(1/π)∫₀^π angerIntegrand = angerJ (11.10.1)",
        mp.quad(lambda th: _anger_integrand(_av, _az, th), [0, mp.pi]) / mp.pi,
        mp.angerj(_av, _az), mp.mpf("1e-15"))
    if abs(mp.angerj(_av, _az) - mp.besselj(_av, _az)) < mp.mpf("1e-2"):
        fails.append("anger anchor point does not distinguish Anger J_ν from Bessel J_ν")
    # Hankel H⁽¹⁾/H⁽²⁾ (DLMF 10.4.3): our J ± iY vs the independent mp.hankel1/2 —
    # the imaginary-part SIGN is exactly where the two kinds differ.
    _hv, _hz = mp.mpf("0.3"), mp.mpf("1.7")
    chk("besselHankel1 = mp.hankel1 (10.4.3)", _bessel_hankel1(_hv, _hz), mp.hankel1(_hv, _hz), mp.mpf("1e-18"))
    chk("besselHankel2 = mp.hankel2 (10.4.3)", _bessel_hankel2(_hv, _hz), mp.hankel2(_hv, _hz), mp.mpf("1e-18"))
    chk("H⁽¹⁾−H⁽²⁾ = 2iY (10.4.4)", _bessel_hankel1(_hv, _hz) - _bessel_hankel2(_hv, _hz),
        2 * mp.mpc(0, 1) * mp.bessely(_hv, _hz), mp.mpf("1e-18"))
    if abs(_bessel_hankel1(_hv, _hz) - mp.hankel2(_hv, _hz)) < mp.mpf("1e-2"):
        fails.append("hankel anchor does not distinguish H⁽¹⁾ from H⁽²⁾")
    # besselYnu (DLMF 10.2.3): mp.bessely IS the Lean reflection formula at non-integer ν.
    chk("bessely = (Jν cos νπ − J₋ν)/sin νπ (10.2.3)",
        (mp.besselj(_hv, _hz) * mp.cos(mp.pi * _hv) - mp.besselj(-_hv, _hz)) / mp.sin(mp.pi * _hv),
        mp.bessely(_hv, _hz), mp.mpf("1e-18"))
    # besselI (DLMF 10.25.2/10.27.1): defining-series partial sum, ±n symmetry, z-parity.
    _iz = mp.mpf("1.3")
    chk("besselI series Σ(z/2)^{3+2k}/(k!(3+k)!) (10.25.2)",
        mp.nsum(lambda k: (_iz / 2) ** (3 + 2 * k) / (mp.factorial(k) * mp.factorial(3 + k)),
                [0, 25]), _besselI_int(3, _iz), mp.mpf("1e-20"))
    chk("I₋₃ = I₃ (10.27.1)", _besselI_int(-3, _iz), _besselI_int(3, _iz))
    chk("I₃(−z) = −I₃(z) (10.27.1 parity)", _besselI_int(3, -_iz), -_besselI_int(3, _iz))
    if abs(_besselI_int(2, _iz) - mp.besselj(2, _iz)) < mp.mpf("1e-2"):
        fails.append("besselI anchor does not distinguish I_n from J_n")
    chk("n.natAbs envfn atom |−3| = 3", _natAbs_env({"n": -3}), 3)
    # besselI0Int (DLMF 10.32.1): quadrature of the defining integral pins the 1/π-on-[0,π]
    # normalization (the 1/(2π)-on-[0,π] rival is off by 2).
    _m0 = mp.mpf("1.7")
    chk("(1/π)∫₀^π e^{M cos θ}dθ = I₀(M) (10.32.1)",
        mp.quad(lambda th: mp.e ** (_m0 * mp.cos(th)), [0, mp.pi]) / mp.pi,
        mp.besseli(0, _m0), mp.mpf("1e-15"))
    # series TERM bindings: partial sums rebuild the mpmath functions; term ratios are the
    # DLMF hypergeometric ratios (pins Γ-shifts and the (z/2)-powers at once).
    _tv, _tz = mp.mpf("0.6"), mp.mpf("1.3")
    chk("Σ besselJnuTerm = J_ν (10.2.2)",
        mp.nsum(lambda m: _besselJnu_term(_tv, _tz, m), [0, 30]), mp.besselj(_tv, _tz), mp.mpf("1e-20"))
    chk("besselJnuTerm ratio −(z²/4)/((m+1)(m+ν+1))",
        _besselJnu_term(_tv, _tz, 1) / _besselJnu_term(_tv, _tz, 0),
        -(_tz ** 2 / 4) / (1 * (_tv + 1)), mp.mpf("1e-20"))
    _sv, _sz = mp.mpf("0.4"), mp.mpf("1.7")
    chk("Σ struveHTerm = H_ν (11.2.1)",
        mp.nsum(lambda m: _struve_term(-1, _sv, _sz, m), [0, 30]), mp.struveh(_sv, _sz), mp.mpf("1e-20"))
    chk("Σ struveLTerm = L_ν (11.2.2)",
        mp.nsum(lambda m: _struve_term(1, _sv, _sz, m), [0, 30]), mp.struvel(_sv, _sz), mp.mpf("1e-20"))
    chk("struveHTerm ratio −(z²/4)/((m+3/2)(m+ν+3/2))",
        _struve_term(-1, _sv, _sz, 1) / _struve_term(-1, _sv, _sz, 0),
        -(_sz ** 2 / 4) / (mp.mpf(3) / 2 * (_sv + mp.mpf(3) / 2)), mp.mpf("1e-20"))
    # besselK_cosh (DLMF 10.32.9): quadrature of the DEFINING integral; the one-sided
    # e^{−x cosh t − νt} rival (correct only over the full line) is rejected.
    # (quad truncated at t = 40: the tail is < e^{−1.3·cosh 40} ≈ 10^{−6·10^16} ≡ 0 at any
    # dps, while the [0,∞) transform would evaluate cosh at huge t and feed exp an argument
    # of magnitude e^t — a bignum-exponent blowup, the documented mpmath OOM trap.)
    _kv, _kx = mp.mpf("0.7"), mp.mpf("1.3")
    chk("∫₀^∞ e^{−x cosh t}cosh(νt)dt = K_ν (10.32.9)",
        mp.quad(lambda t: mp.e ** (-_kx * mp.cosh(t)) * mp.cosh(_kv * t), [0, 40]),
        _besselK_cosh(_kv, _kx), mp.mpf("1e-15"))
    if abs(mp.quad(lambda t: mp.e ** (-_kx * mp.cosh(t) - _kv * t), [0, 40])
           - mp.besselk(_kv, _kx)) < mp.mpf("1e-3"):
        fails.append("besselK_cosh anchor does not distinguish the one-sided e^{−νt} rival")
    chk_raises("besselK_cosh(ν, −1) raises (divergent junk domain)", lambda: _besselK_cosh(_kv, -1))
    # besselKAmplitude (DLMF 10.32.8, rescaled t = 1+s): the amplitude reassembles K_ν —
    # √π (z/2)^ν 2^{ν−1/2} e^{−z}/Γ(ν+1/2) ∫₀^∞ e^{−zs} s^{ν−1/2} g_ν(s) ds = K_ν(z).
    _wv, _wz = mp.mpf("1.3"), mp.mpf("1.7")
    chk("Watson amplitude reassembles K_ν (10.32.8)",
        mp.sqrt(mp.pi) * (_wz / 2) ** _wv * mp.mpf(2) ** (_wv - mp.mpf(1) / 2)
        * mp.e ** (-_wz) / mp.gamma(_wv + mp.mpf(1) / 2)
        * mp.quad(lambda s: mp.e ** (-_wz * s) * s ** (_wv - mp.mpf(1) / 2)
                  * _besselK_amplitude(_wv, s), [0, mp.inf]),
        mp.besselk(_wv, _wz), mp.mpf("1e-15"))
    # Kelvin cluster (DLMF 10.61): angles pinned as values; ber/bei against mp.besselj on
    # the e^{3πi/4} ray (rejects the e^{πi/4} rival there); ker/kei relation for the K-side
    # prefactor/angle; besselJC against its defining series ON the Kelvin ray.
    chk("kelvinAngleJ = e^{3πi/4}", REGISTRY["kelvinAngleJ"][1], mp.mpc(-1, 1) / mp.sqrt(2))
    chk("kelvinAngleK = e^{πi/4}", REGISTRY["kelvinAngleK"][1], mp.mpc(1, 1) / mp.sqrt(2))
    _kbx = mp.mpf("1.3")
    _kray = _kbx * mp.expjpi(mp.mpf(3) / 4)
    chk("ber₂+i·bei₂ = J₂(x e^{3πi/4}) (10.61.1)",
        mp.ber(2, _kbx) + mp.mpc(0, 1) * mp.bei(2, _kbx), mp.besselj(2, _kray), mp.mpf("1e-18"))
    if abs(mp.besselj(2, _kbx * mp.expjpi(mp.mpf(1) / 4))
           - mp.besselj(2, _kray)) < mp.mpf("1e-3"):
        fails.append("kelvin J-angle anchor does not distinguish e^{3πi/4} from e^{πi/4}")
    chk("besselJC series on the Kelvin ray (10.2.2)",
        mp.nsum(lambda k: (-1) ** k * (_kray / 2) ** (2 + 2 * k)
                / (mp.factorial(k) * mp.factorial(2 + k)), [0, 30]),
        mp.besselj(2, _kray), mp.mpf("1e-18"))
    _kkx = mp.mpf("1.4")
    chk("ker₁+i·kei₁ = e^{−πi/2}K₁(x e^{πi/4}) (10.61.2)",
        mp.ker(1, _kkx) + mp.mpc(0, 1) * mp.kei(1, _kkx),
        mp.expjpi(-mp.mpf(1) / 2) * mp.besselk(1, _kkx * mp.expjpi(mp.mpf(1) / 4)), mp.mpf("1e-18"))
    chk("kelvinKPrefactor 1 = e^{−πi/2} = −i", REGISTRY["kelvinKPrefactor"][1](1), mp.mpc(0, -1))
    # Lommel s/S (DLMF 11.9.3/11.9.5): s_{ν,ν} = 2^{ν−1}√π Γ(ν+½) H_ν (pins the ₁F₂
    # normalization against mp.struveh); with GENUINE Bessel data S_{ν,ν} =
    # 2^{ν−1}√π Γ(ν+½)(H_ν − Y_ν) (pins the cos/Y placement + Γ arguments); and the
    # DLMF 11.9.9 algebraic decay S_{μ,ν}(z)·z^{1−μ} → 1 at z = 25 (pins the sin/J
    # placement — bare s, or any homogeneous-part error, leaves an O(1) residual there).
    _lv, _lz = mp.mpf("0.7"), mp.mpf("1.9")
    _lfac = mp.mpf(2) ** (_lv - 1) * mp.sqrt(mp.pi) * mp.gamma(_lv + mp.mpf(1) / 2)
    chk("lommel s_{ν,ν} = 2^{ν−1}√π Γ(ν+½)H_ν (11.9.3)",
        _lommel_small_s(_lv, _lv, _lz), _lfac * mp.struveh(_lv, _lz), mp.mpf("1e-18"))
    chk("lommel S_{ν,ν} = 2^{ν−1}√π Γ(ν+½)(H_ν−Y_ν) (11.9.5)",
        _lommel_big_S(mp.besselj(_lv, _lz), mp.bessely(_lv, _lz), _lv, _lv, _lz),
        _lfac * (mp.struveh(_lv, _lz) - mp.bessely(_lv, _lz)), mp.mpf("1e-18"))
    with mp.workdps(50):
        # Bessel data at ORDER ν (the theorem's J_ν/Y_ν slots — order μ there breaks
        # the 11.9.9 decay, which is itself a check that the data enters at order ν)
        _lm, _ln, _lZ = mp.mpf("0.4"), mp.mpf("0.3"), mp.mpf(25)
        _lS = _lommel_big_S(mp.besselj(_ln, _lZ), mp.bessely(_ln, _lZ), _lm, _ln, _lZ)
        _ls = _lommel_small_s(_lm, _ln, _lZ)
    if abs(_lS * _lZ ** (1 - _lm) - 1) > mp.mpf("2e-3"):
        fails.append(f"lommel S decay: S·z^(1−μ) = {mp.nstr(_lS * _lZ ** (1 - _lm), 12)} ≉ 1 (11.9.9)")
    if abs(_ls * _lZ ** (1 - _lm) - 1) < mp.mpf("5e-2"):
        fails.append("lommel decay anchor does not distinguish S from bare s")
    # ── A3 hypergeometric / special-values / misc cluster anchors ────────────────────
    # Frobenius Gauss instance (DLMF 15.10.2): frobCoeff over gaussP/Q/R against the
    # INDEPENDENT ₂F₁ coefficient (rising-factorial products) at BOTH indicial roots,
    # plus a generic-ρ discriminator (off an indicial root the identity must FAIL —
    # the recurrence carries real content, not a tautology).
    _fa, _fb, _fc = mp.mpf("0.4"), mp.mpf("0.6"), mp.mpf("0.9")
    _fP = REGISTRY["gaussP"][1]
    _fQ = REGISTRY["gaussQ"][1](_fa, _fb, _fc)
    _fR = REGISTRY["gaussR"][1](_fa, _fb)
    chk("gaussP: constantCoeff 1, coeff₁ −1", _fP.coeff(0) + _fP.coeff(1), 0)
    chk("gaussQ: (c, −(a+b+1))", _fQ.coeff(0) - _fc + (_fQ.coeff(1) + _fa + _fb + 1), 0)
    chk("gaussR: (0, −ab)", _fR.coeff(0) + (_fR.coeff(1) + _fa * _fb), 0)
    for _fn_ in (1, 3, 5):
        chk(f"frobCoeff ρ=0 n={_fn_} = ₂F₁ coeff (15.10.2)",
            _frob_coeff(_fP, _fQ, _fR, mp.mpf(0), _fn_), _gaussF_coeff(_fa, _fb, _fc, _fn_))
        chk(f"frobCoeff ρ=1−c n={_fn_} = shifted ₂F₁ coeff (15.10.2)",
            _frob_coeff(_fP, _fQ, _fR, 1 - _fc, _fn_),
            _gaussF_coeff(_fa - _fc + 1, _fb - _fc + 1, 2 - _fc, _fn_))
    if abs(_frob_coeff(_fP, _fQ, _fR, mp.mpf("0.3"), 1)
           - _gaussF_coeff(_fa + mp.mpf("0.3"), _fb + mp.mpf("0.3"), _fc + mp.mpf("0.6"), 1)) \
            < mp.mpf("1e-3"):
        fails.append("frobCoeff generic-ρ discriminator: identity did not break off-root")
    # Heun (DLMF 31.3): c₁ = q/(aγ); the 31.3.7 recurrence residual; the a = 1,
    # δ = α+β+1−γ, q = αβ hypergeometric REDUCTION Hℓ = ₂F₁(α,β;γ;·) (independent
    # cross-family anchor); formal annihilation heunOp(heunSeries) = 0 with a
    # perturbed-series discriminator; constantCoeff via the _FPS plumbing.
    _ha, _hq, _hal, _hbe, _hga, _hde = (mp.mpf(t) for t in ("1.3", "0.7", "0.4", "0.6", "0.9", "1.1"))
    chk("heunCoeff c₁ = q/(aγ) (31.3.2)", _heun_coeff(_ha, _hq, _hal, _hbe, _hga, _hde, 1),
        _hq / (_ha * _hga))
    for _hn in (0, 1, 3):
        chk(f"heunCoeff 31.3.7 recurrence n={_hn}",
            _ha * (_hn + 2) * (_hn + 1 + _hga) * _heun_coeff(_ha, _hq, _hal, _hbe, _hga, _hde, _hn + 2),
            _heunB(_ha, _hq, _hal, _hbe, _hga, _hde, _hn + 1)
            * _heun_coeff(_ha, _hq, _hal, _hbe, _hga, _hde, _hn + 1)
            - (_hn + _hal) * (_hn + _hbe) * _heun_coeff(_ha, _hq, _hal, _hbe, _hga, _hde, _hn))
    for _hn in (1, 2, 4):
        chk(f"heun a=1,q=αβ,δ=α+β+1−γ reduction → ₂F₁ coeff n={_hn}",
            _heun_coeff(mp.mpf(1), _hal * _hbe, _hal, _hbe, _hga,
                        _hal + _hbe + 1 - _hga, _hn),
            _gaussF_coeff(_hal, _hbe, _hga, _hn))
    _hs = _heun_series(_ha, _hq, _hal, _hbe, _hga, _hde)
    chk("heunSeries constantCoeff = 1 (31.3)", _constant_coeff(_hs), 1)
    chk("heunOp(heunSeries) = 0 formally (31.2.1/31.3)",
        _heun_op(_ha, _hq, _hal, _hbe, _hga, _hde, _hs), 0, mp.mpf("1e-24"))
    _hbad = _FPS(lambda j: _hs.coeff(j) + (mp.mpf(1) if j == 1 else 0))
    if _heun_op(_ha, _hq, _hal, _hbe, _hga, _hde, _hbad) < mp.mpf("0.1"):
        fails.append("heunOp discriminator: perturbed series not rejected")
    # ── normal-form gauge factors (DLMF 31.2.2 heunNormalGauge / 31.14.3
    # fuchsianNormalGauge) ──  Anchored to the DEFINING role of the gauge, not to its
    # closed form: under w = φ·W the first-derivative term of the Fuchsian/Heun equation
    # w″ + p(z)w′ + q(z)w = 0 disappears exactly when 2φ′/φ + p(z) = 0, with
    # p(z) = γ/z + δ/(z−1) + ε/(z−a) for Heun (DLMF 31.2.1) and p(z) = Σⱼ γⱼ/(z−aⱼ) for
    # the general Fuchsian equation (31.14.1).  φ′ is an mpmath numerical derivative —
    # decorrelated from the product formula the binding evaluates.  Plus: the principal
    # branch is pinned against exp(−γ/2·Log z) at a point with NEGATIVE real part on both
    # sides of the cut (a wrong-branch power fails this), the trivial-exponent
    # normalization φ ≡ 1, the empty Fin-0 product, the 31.14.3 → 31.2.2 specialization at
    # a = (0,1,a), γ = (γ,δ,ε), and an exponent-perturbation discriminator on each.
    _gz = mp.mpc("0.43", "0.61")
    chk("heunNormalGauge γ=δ=ε=0 → 1 (31.2.2 trivial gauge)",
        _heun_normal_gauge(_ha, mp.mpf(0), mp.mpf(0), mp.mpf(0), _gz), 1)
    for _gzz in (mp.mpc("-1.7", "0.35"), mp.mpc("-1.7", "-0.35"), mp.mpc("0.8", "1.2")):
        chk(f"heunNormalGauge single factor = exp(−γ/2·Log z) at z={mp.nstr(_gzz,6)}",
            _heun_normal_gauge(_ha, _hga, mp.mpf(0), mp.mpf(0), _gzz),
            mp.exp(-_hga / 2 * mp.log(_gzz)))
    _gp = (lambda t: _hga / t + _hde / (t - 1)
           + (_hal + _hbe + 1 - _hga - _hde) / (t - _ha))          # DLMF 31.2.1 p(z), ε by 31.2.3
    _gphi = (lambda t: _heun_normal_gauge(_ha, _hga, _hde,
                                          _hal + _hbe + 1 - _hga - _hde, t))
    chk("heunNormalGauge kills w′: 2φ′/φ + p = 0 (31.2.1→31.2.2)",
        2 * mp.diff(_gphi, _gz) / _gphi(_gz) + _gp(_gz), 0, mp.mpf("1e-15"))
    _gphibad = (lambda t: _heun_normal_gauge(_ha, _hga, _hde,
                                             _hal + _hbe + 1 - _hga - _hde + mp.mpf("0.3"), t))
    if abs(2 * mp.diff(_gphibad, _gz) / _gphibad(_gz) + _gp(_gz)) < mp.mpf("0.05"):
        fails.append("heunNormalGauge discriminator: perturbed ε still kills w′")

    def _gvec(vals):                       # the sweep's `.q`-tagged Fin-vector callable
        f = lambda i: vals[int(i)]         # noqa: E731
        f.q = len(vals)
        return f
    _fa3 = _gvec([mp.mpc("0.0", "0.0"), mp.mpc("1.0", "0.0"), _ha + 0j])
    _fg3 = _gvec([_hga + 0j, _hde + 0j, (_hal + _hbe + 1 - _hga - _hde) + 0j])
    chk("fuchsianNormalGauge Fin 0 = empty product 1 (31.14.3)",
        _fuchsian_normal_gauge(_gvec([]), _gvec([]), _gz), 1)
    chk("fuchsianNormalGauge at a=(0,1,a), γ=(γ,δ,ε) = heunNormalGauge (31.14.3→31.2.2)",
        _fuchsian_normal_gauge(_fa3, _fg3, _gz), _gphi(_gz))
    _fa4 = _gvec([mp.mpc("-0.6", "0.4"), mp.mpc("1.3", "-0.5"),
                  mp.mpc("0.2", "0.9"), mp.mpc("2.1", "0.3")])
    _fg4 = _gvec([mp.mpc("0.7", "-0.2"), mp.mpc("1.1", "0.3"),
                  mp.mpc("-0.4", "0.5"), mp.mpc("0.9", "0.1")])
    _fphi = lambda t: _fuchsian_normal_gauge(_fa4, _fg4, t)        # noqa: E731
    _fp = lambda t: mp.fsum(_fg4(j) / (t - _fa4(j)) for j in range(4))   # noqa: E731
    chk("fuchsianNormalGauge kills w′: 2φ′/φ + Σγⱼ/(z−aⱼ) = 0 (31.14.1→31.14.3)",
        2 * mp.diff(_fphi, _gz) / _fphi(_gz) + _fp(_gz), 0, mp.mpf("1e-15"))
    _fg4bad = _gvec([mp.mpc("0.7", "-0.2"), mp.mpc("1.1", "0.3"),
                     mp.mpc("-0.4", "0.5"), mp.mpc("1.4", "0.1")])
    _fphibad = lambda t: _fuchsian_normal_gauge(_fa4, _fg4bad, t)  # noqa: E731
    if abs(2 * mp.diff(_fphibad, _gz) / _fphibad(_gz) + _fp(_gz)) < mp.mpf("0.05"):
        fails.append("fuchsianNormalGauge discriminator: perturbed γ₄ still kills w′")
    # ── DLMF 31.14.5 normal-form coefficients (fuchsianNormalQ / fuchsianNormalGamma) ──
    # Anchored by their DEFINING ROLE, not by re-typing the display: with φ the (already
    # anchored) 31.14.3 gauge, w = φ·W turns 31.14.1 into W″ = −(φ″/φ + p φ′/φ + r)W, and
    # 31.14.4/31.14.5 assert that coefficient equals Σⱼ(γ̃ⱼ/(z−aⱼ)² + q̃ⱼ/(z−aⱼ)). φ″ and φ′
    # are mpmath numerical derivatives — decorrelated from the closed forms. The four qⱼ
    # carry the display's own Fuchsian side condition Σqⱼ = 0 (z = ∞ regular).
    # Verified independently at docs/verification/ch31/probe_fuchsian_normal.py.
    _fq4 = _gvec([mp.mpc("0.5", "0.1"), mp.mpc("-0.2", "0.7"), mp.mpc("0.4", "-0.3"),
                  -(mp.mpc("0.5", "0.1") + mp.mpc("-0.2", "0.7") + mp.mpc("0.4", "-0.3"))])
    _fr = lambda t: mp.fsum(_fq4(j) / (t - _fa4(j)) for j in range(4))    # noqa: E731
    _fW = lambda t: -(mp.diff(_fphi, t, 2) / _fphi(t)                     # noqa: E731
                      + _fp(t) * mp.diff(_fphi, t) / _fphi(t) + _fr(t))
    _fnorm = lambda t, qs, gs: mp.fsum(                                   # noqa: E731
        gs[j] / (t - _fa4(j)) ** 2 + qs[j] / (t - _fa4(j)) for j in range(4))
    _qt = [_fuchsian_normal_q(_fa4, _fg4, _fq4, j) for j in range(4)]
    _gt = [_fuchsian_normal_gamma(_fg4, j) for j in range(4)]
    for _nz in (mp.mpc("0.43", "0.61"), mp.mpc("-1.2", "0.8"), mp.mpc("3.0", "-1.1")):
        chk(f"31.14.5 (q̃,γ̃) give the 31.14.4 normal form at z={mp.nstr(_nz,6)}",
            _fW(_nz), _fnorm(_nz, _qt, _gt), mp.mpf("1e-15"))
    _qtbad = list(_qt); _qtbad[1] += mp.mpf("0.3")
    _gtbad = list(_gt); _gtbad[2] += mp.mpf("0.3")
    if abs(_fW(_gz) - _fnorm(_gz, _qtbad, _gt)) < mp.mpf("0.05"):
        fails.append("fuchsianNormalQ discriminator: perturbed q̃₂ still gives 31.14.4")
    if abs(_fW(_gz) - _fnorm(_gz, _qt, _gtbad)) < mp.mpf("0.05"):
        fails.append("fuchsianNormalGamma discriminator: perturbed γ̃₃ still gives 31.14.4")
    # the k ≠ j erase-sum ORIENTATION (aⱼ−aₖ, not aₖ−aⱼ) is what the normal form fixes
    _qtflip = [-(_qt[j] + _fq4(j)) - _fq4(j) for j in range(4)]     # ½Σ → −½Σ, −qⱼ kept
    if abs(_fW(_gz) - _fnorm(_gz, _qtflip, _gt)) < mp.mpf("0.05"):
        fails.append("fuchsianNormalQ discriminator: sign-flipped erase-sum still gives 31.14.4")
    # ── DLMF 31.14.2 carrier ladder (FuchsRelation) ──  INDEPENDENT anchor: for Heun's
    # own data — a = (0,1,a), γ = (γ,δ,ε) with ε = α+β+1−γ−δ (31.2.3), and the qⱼ the
    # partial-fraction residues of Heun's (αβz−q)/(z(z−1)(z−a)) (31.2.1) — the ladder must
    # return exactly Heun's {α, β}, which never entered the residues as a pair.
    _hres = _gvec([(-_hq) / ((0 - 1) * (0 - _ha)),
                   (_hal * _hbe - _hq) / (1 * (1 - _ha)),
                   (_hal * _hbe * _ha - _hq) / (_ha * (_ha - 1))])
    _hab = _pin_fuchs_relation(_fa3, _fg3, _hres)
    chk("FuchsRelation ladder recovers Heun's {α,β} (31.14.2 ← 31.2.1 residues)",
        min(abs(_hab[0] - _hal), abs(_hab[0] - _hbe))
        + min(abs(_hab[1] - _hal), abs(_hab[1] - _hbe)), 0, mp.mpf("1e-20"))
    chk("FuchsRelation ladder: Σq = 0 for the Heun residues (z=∞ regular, 31.14.1)",
        mp.fsum(_hres(j) for j in range(3)), 0, mp.mpf("1e-20"))
    # …and it genuinely solves the display it transcribes (both relations, at generic data)
    _fa5 = _gvec([mp.mpc("-0.6", "0.4"), mp.mpc("1.3", "-0.5"), mp.mpc("0.2", "0.9")])
    _fg5 = _gvec([mp.mpc("0.7", "-0.2"), mp.mpc("1.1", "0.3"), mp.mpc("-0.4", "0.5")])
    _fq5 = _gvec([mp.mpc("0.5", "0.1"), mp.mpc("-0.2", "0.7"), mp.mpc("0.4", "-0.3")])
    _al5, _be5 = _pin_fuchs_relation(_fa5, _fg5, _fq5)
    chk("FuchsRelation ladder: α+β+1 = Σγⱼ (31.14.2)", _al5 + _be5 + 1,
        mp.fsum(_fg5(j) for j in range(3)), mp.mpf("1e-20"))
    chk("FuchsRelation ladder: αβ = Σ aⱼqⱼ (31.14.2)", _al5 * _be5,
        mp.fsum(_fa5(j) * _fq5(j) for j in range(3)), mp.mpf("1e-20"))
    # ── DLMF 31.8.1 carrier ladder (HeunHalfOddIntegerExponents) ──  Anchored on the
    # EXPONENT DIFFERENCES of Heun's Riemann scheme (31.2.1): 1−γ, 1−δ, 1−ε at z = 0,1,a
    # and β−α at ∞ must be exactly the half-odd integers m₁+½, m₂+½, m₃+½, m₀+½. A rival
    # with the signs of m₁..m₃ unflipped (γ = m₁+½) sends 1−γ to ½−m₁ < 0 — not a §31.8
    # half-odd-integer index — and is rejected below.
    _hm = _gvec([mp.mpf(2), mp.mpf(0), mp.mpf(3), mp.mpf(1)])
    _hal0 = mp.mpc("0.37", "-0.82")
    _hbe0, _hga0, _hde0, _hep0 = _pin_half_odd_integer_exponents(_hm, _hal0)
    chk("31.8.1 ladder: β−α = m₀+½", _hbe0 - _hal0, mp.mpf(2) + mp.mpf(1) / 2)
    for _k, (_val, _mk) in enumerate([(_hga0, 0), (_hde0, 3), (_hep0, 1)]):
        chk(f"31.8.1 ladder: exponent difference at singularity {_k+1} = m+½",
            1 - _val, mp.mpf(_mk) + mp.mpf(1) / 2)
    if min(mp.re(1 - _hga0), mp.re(1 - _hde0), mp.re(1 - _hep0)) < mp.mpf("0.5"):
        fails.append("31.8.1 ladder discriminator: an exponent difference is not a "
                     "nonnegative half-odd integer (sign of m_k flipped?)")
    # ── DLMF §31.8 quadrature data (heunQuadratureGenus / heunPsi / heunNuSq) ──────
    # NONE of the four closed forms is re-typed here.  Ψ is anchored by the §31.8
    # DEFINING characterization — it solves the third-order symmetric-square equation of
    # Heun's equation at q = −λ/4 with the 31.8.1 exponents of its own 𝐦 — and ν² by the
    # Wronskian first integral of the 31.8.2 ansatz: for u = w₊w₋ = Ψ,
    #   (u′)² − 2u u″ − 2P u u′ − 4Q u² = W(w₊,w₋)²,
    # while differentiating 31.8.2 gives W = −iν z^{m₁}(z−1)^{m₂}(z−a)^{m₃}/√(z(z−1)(z−a)),
    # i.e. W² = −ν² z^{2m₁−1}(z−1)^{2m₂−1}(z−a)^{2m₃−1}.  Solving that for ν² recovers the
    # spectral curve from Ψ alone.  Both anchors are re-derived symbolically (sympy) in
    # docs/verification/ch31/probe_quadratures.py; here they run numerically via mp.diff.
    def _hq_params(m):                    # 31.8.1 + the Fuchsian relation 31.2.3
        _ga = -mp.mpf(m[1]) + mp.mpf(1) / 2
        _de = -mp.mpf(m[2]) + mp.mpf(1) / 2
        _ep = -mp.mpf(m[3]) + mp.mpf(1) / 2
        _s = _ga + _de + _ep - 1                       # α+β = γ+δ+ε−1
        _d = mp.mpf(m[0]) + mp.mpf(1) / 2              # β−α
        return (_s - _d) / 2, (_s + _d) / 2, _ga, _de, _ep

    def _hq_PQ(av, m, lamv):
        _al, _be, _ga, _de, _ep = _hq_params(m)
        _qq = -lamv / 4
        P = lambda t: _ga / t + _de / (t - 1) + _ep / (t - av)          # noqa: E731
        Q = lambda t: (_al * _be * t - _qq) / (t * (t - 1) * (t - av))  # noqa: E731
        return P, Q

    def _hq_symsq(u, P, Q, t):
        return (mp.diff(u, t, 3) + 3 * P(t) * mp.diff(u, t, 2)
                + (mp.diff(P, t) + 2 * P(t) ** 2 + 4 * Q(t)) * mp.diff(u, t)
                + (2 * mp.diff(Q, t) + 4 * P(t) * Q(t)) * u(t))

    def _hq_nusq(u, P, Q, m, t):
        w2 = (mp.diff(u, t) ** 2 - 2 * u(t) * mp.diff(u, t, 2)
              - 2 * P(t) * u(t) * mp.diff(u, t) - 4 * Q(t) * u(t) ** 2)
        return -w2 / (t ** (2 * m[1] - 1) * (t - 1) ** (2 * m[2] - 1)
                      * (t - av) ** (2 * m[3] - 1))

    av, lamv = mp.mpc("0.61", "-0.37"), mp.mpc("0.83", "0.29")
    for _mvec, _psi, _nusq in [((1, 1, 0, 0), _heun_psi_1_2, _heun_nusq_1_2),
                               ((1, -2, 0, 0), _heun_psi_1_neg1, _heun_nusq_1_neg1)]:
        _tag = "31.8.4" if _mvec[0:2] == (1, 1) else "31.8.5"
        _P, _Q = _hq_PQ(av, _mvec, lamv)
        _u = lambda t, _p=_psi: _p(av, lamv, t)                          # noqa: E731
        for _tz in (mp.mpc("0.41", "0.53"), mp.mpc("-0.72", "0.19"), mp.mpc("1.7", "-0.6")):
            chk(f"{_tag}: Ψ solves the §31.8 symmetric-square equation at "
                f"z={mp.nstr(_tz, 6)}", _hq_symsq(_u, _P, _Q, _tz), 0, mp.mpf("1e-14"))
            chk(f"{_tag}: ν² from the 31.8.2 Wronskian first integral at "
                f"z={mp.nstr(_tz, 6)}", _hq_nusq(_u, _P, _Q, _mvec, _tz),
                _nusq(av, lamv), mp.mpf("1e-12"))
        # z-independence of the recovered ν² — it is a first integral, not a local fit
        chk(f"{_tag}: recovered ν² is z-independent",
            _hq_nusq(_u, _P, _Q, _mvec, mp.mpc("0.41", "0.53"))
            - _hq_nusq(_u, _P, _Q, _mvec, mp.mpc("1.7", "-0.6")), 0, mp.mpf("1e-12"))
        # DISCRIMINATORS: a perturbed constant term must break the symmetric-square
        # equation, and a perturbed ν² must break the first integral.
        _ubad = lambda t, _p=_psi: _p(av, lamv, t) + mp.mpf("0.3")       # noqa: E731
        if abs(_hq_symsq(_ubad, _P, _Q, mp.mpc("0.41", "0.53"))) < mp.mpf("1e-3"):
            fails.append(f"{_tag} discriminator: a perturbed Ψ still solves the "
                         f"symmetric-square equation")
        if abs(_hq_nusq(_u, _P, _Q, _mvec, mp.mpc("0.41", "0.53"))
               - (_nusq(av, lamv) + mp.mpf("0.3"))) < mp.mpf("1e-3"):
            fails.append(f"{_tag} discriminator: a perturbed ν² still matches the "
                         f"Wronskian first integral")
    # 31.8.3 genus — anchored on DLMF's OWN two worked members (the λ-degrees of the
    # Ψ just verified: both are degree 1 in λ) and on the integrality that the (−1)^N
    # parity term is there to produce.
    chk("31.8.3: g(1,1,0,0) = 1 (the λ-degree of Ψ_{1,2}, 31.8.4)",
        _heun_quadrature_genus(lambda j: [1, 1, 0, 0][int(j)]), 1)
    chk("31.8.3: g(0,0,0,0) = 0 (Ψ ≡ const in λ)",
        _heun_quadrature_genus(lambda j: 0), 0)
    for _mg in [(0, 0, 0, 0), (1, 1, 0, 0), (2, 0, 3, 1), (1, 1, 1, 1), (4, 2, 0, 5),
                (3, 3, 2, 2), (6, 0, 0, 0), (0, 5, 2, 0), (7, 7, 7, 7)]:
        _gv = _heun_quadrature_genus(lambda j, _m=_mg: _m[int(j)])
        if _gv != int(_gv) or _gv < 0:
            fails.append(f"31.8.3 at m={_mg}: g = {mp.nstr(_gv, 12)} is not a "
                         f"nonnegative integer (both max arguments must be even)")
        if _gv < max(_mg):
            fails.append(f"31.8.3 at m={_mg}: g = {mp.nstr(_gv, 12)} < max m_k — the "
                         f"first max argument (2 max m_k) is not being taken")
    # DISCRIMINATOR: dropping the (1+(−1)^N) parity factor destroys the integrality of g
    # at an 𝐦 where the SECOND max argument wins and N is odd (the parity the factor
    # protects: N odd ⇒ 1+(−1)^N = 0, so the ½+min_k m_k term must not be subtracted).
    _mg = (1, 1, 1, 0)                       # N = 3 (odd), max = 1, min = 0 ⇒ g = 2
    _rival = mp.mpf(1) / 2 * max(mp.mpf(2 * max(_mg)),
                                 1 + mp.mpf(sum(_mg)) - (mp.mpf(1) / 2 + min(_mg)))
    if _rival == int(_rival):
        fails.append("31.8.3 discriminator: the parity-free rival is still integral at "
                     "m=(1,1,1,0) — the (−1)^N term is not being exercised")
    if abs(_heun_quadrature_genus(lambda j: _mg[int(j)]) - _rival) < mp.mpf("1e-20"):
        fails.append("31.8.3 discriminator: g agrees with the parity-free rival at "
                     "m=(1,1,1,0) — the (1+(−1)^N) factor is missing")
    # ── DLMF 31.15.12 Stieltjes weight ──  Transcription checked against a hand-expanded
    # N = 3 (n = 2) instance and the n = 1 empty-pair-product case, plus the defining-role
    # anchor at γ ≡ 1 (all exponents γ_k−1 vanish, so ρ collapses to the ordered-difference
    # product ∏_{j<k}(z_k−z_j)) — which rejects the γ_k-exponent rival — and an ORIENTATION
    # discriminator (z_k−z_j, not z_j−z_k).
    _sga = _gvec([mp.mpf("0.7"), mp.mpf("1.4"), mp.mpf("2.1")])
    _sa = _gvec([mp.mpf("-1.0"), mp.mpf("0.25"), mp.mpf("1.75")])
    _sz = _gvec([mp.mpf("-0.4"), mp.mpf("1.1")])
    chk("stieltjesWeight N=3 (n=2) = hand-expanded 31.15.12",
        _stieltjes_weight(_sga, _sa, _sz),
        abs(_sz(0) - _sa(0)) ** (_sga(0) - 1) * abs(_sz(0) - _sa(1)) ** (_sga(1) - 1)
        * abs(_sz(0) - _sa(2)) ** (_sga(2) - 1) * abs(_sz(1) - _sa(0)) ** (_sga(0) - 1)
        * abs(_sz(1) - _sa(1)) ** (_sga(1) - 1) * abs(_sz(1) - _sa(2)) ** (_sga(2) - 1)
        * (_sz(1) - _sz(0)), mp.mpf("1e-24"))
    _sga2 = _gvec([mp.mpf("0.7"), mp.mpf("1.4")])
    _sa2 = _gvec([mp.mpf("-1.0"), mp.mpf("0.25")])
    _sz1 = _gvec([mp.mpf("-0.4")])
    chk("stieltjesWeight n=1: empty pair product = 1 (31.15.12)",
        _stieltjes_weight(_sga2, _sa2, _sz1),
        abs(_sz1(0) - _sa2(0)) ** (_sga2(0) - 1) * abs(_sz1(0) - _sa2(1)) ** (_sga2(1) - 1),
        mp.mpf("1e-24"))
    _sg1 = _gvec([mp.mpf(1), mp.mpf(1), mp.mpf(1)])
    chk("stieltjesWeight γ≡1 collapses to ∏_{j<k}(z_k−z_j) (exponent is γ_k−1)",
        _stieltjes_weight(_sg1, _sa, _sz), _sz(1) - _sz(0), mp.mpf("1e-24"))
    if abs(_stieltjes_weight(_sga, _sa, _sz) + _stieltjes_weight(_sga, _sa,
                                                                 _gvec([_sz(1), _sz(0)]))) \
            > mp.mpf("1e-24"):
        fails.append("stieltjesWeight orientation: ρ is not antisymmetric in (z₁,z₂) — "
                     "the pair product must be the SIGNED (z_k−z_j)")
    # heunFn (DLMF 31.3.1, `(ofScalars (heunCoeff …)).sum`): the SUMMED Maclaurin series.
    # Anchors — (i) the normalization Hℓ(…;0) = 1; (ii) the truncated defining sum
    # ∑_{k≤K} c_k z^k at a point deep inside the disc; (iii) the INDEPENDENT cross-family
    # value: at a = 1, q = αβ, δ = α+β+1−γ the local Heun function reduces to
    # ₂F₁(α,β;γ;z), checked against mp.hyp2f1 (not against our own coefficients);
    # (iv) a q-perturbation discriminator, so the reduction is not vacuous; (v) the
    # out-of-disc guard must RAISE rather than return a value for the divergent tsum.
    chk("heunFn(0) = 1 (31.3 normalization)",
        _heun_fn(_ha, _hq, _hal, _hbe, _hga, _hde, mp.mpf(0)), 1)
    # §31.2(iii)/(iv) changes of variable, each against its own DEFINING formula and,
    # for the elliptic pair, against an INDEPENDENT mpmath evaluation (mp.ellipfun) of
    # sn — not against our own `snk`.
    _cvth = mp.mpc("0.61", "0.23")
    chk("heunTrigVariable θ = sin²θ (31.2.5)",
        REGISTRY["heunTrigVariable"][1](_cvth), mp.sin(_cvth) ** 2)
    _cvk = mp.mpf("0.62")
    chk("heunJacobiSingularity k = k⁻² (31.2.7)",
        REGISTRY["heunJacobiSingularity"][1](_cvk), 1 / _cvk ** 2)
    _cvze = mp.mpc("0.47", "0.13")
    chk("heunJacobiVariable ζ k = sn²(ζ,k) (31.2.7, independent mp.ellipfun)",
        REGISTRY["heunJacobiVariable"][1](_cvze, _cvk),
        mp.ellipfun('sn', u=_cvze, m=_cvk ** 2) ** 2, mp.mpf("1e-18"))
    _hz = mp.mpf("0.37")
    chk("heunFn = ∑_{k≤60} c_k z^k (31.3.1 defining sum)",
        _heun_fn(_ha, _hq, _hal, _hbe, _hga, _hde, _hz),
        mp.fsum(c * _hz ** k for k, c in
                enumerate(_heun_coeff_list(_ha, _hq, _hal, _hbe, _hga, _hde, 60))),
        mp.mpf("1e-18"))
    chk("heunFn a=1,q=αβ,δ=α+β+1−γ = ₂F₁(α,β;γ;z) (independent mp.hyp2f1)",
        _heun_fn(mp.mpf(1), _hal * _hbe, _hal, _hbe, _hga, _hal + _hbe + 1 - _hga, _hz),
        mp.hyp2f1(_hal, _hbe, _hga, _hz), mp.mpf("1e-18"))
    if abs(_heun_fn(mp.mpf(1), _hal * _hbe + 1, _hal, _hbe, _hga,
                    _hal + _hbe + 1 - _hga, _hz) - mp.hyp2f1(_hal, _hbe, _hga, _hz)) \
            < mp.mpf("1e-3"):
        fails.append("heunFn discriminator: q-perturbed reduction not rejected")
    try:
        _heun_fn(_ha, _hq, _hal, _hbe, _hga, _hde, mp.mpf("1.4"))
        fails.append("heunFn: out-of-disc |z| ≥ min(1,|a|) returned a value")
    except (ValueError, ZeroDivisionError, OverflowError):
        pass
    # DLMF 31.9.4 coefficients f₀,f₁ (heunF0/heunF1) — the substantive, INDEPENDENT
    # content of the pair is the §31.2(v) parameter dictionary: f₁(q,z) =
    # Hℓ(1−a,αβ−q;α,β,δ,γ;1−z) must solve Heun's equation 31.2.1 in z with the
    # ORIGINAL (a,q,α,β,γ,δ). Checked by finite differences of the summed series; the
    # γ↔δ-unswapped rival is rejected below.
    _t9a, _t9q, _t9z = mp.mpf(2), mp.mpf("0.83"), mp.mpf("0.4")
    _t9e = _hal + _hbe + 1 - _hga - _hde
    chk("heunF0 = Hℓ(a,q;α,β,γ,δ;z) (31.9.4)",
        _heunF0(_t9a, _hal, _hbe, _hga, _hde, _t9q, _t9z),
        _heun_fn(_t9a, _t9q, _hal, _hbe, _hga, _hde, _t9z))

    def _t9res(f, z0, ga_, de_):
        eps_ = _hal + _hbe + 1 - ga_ - de_
        return (mp.diff(f, z0, 2)
                + (ga_ / z0 + de_ / (z0 - 1) + eps_ / (z0 - _t9a)) * mp.diff(f, z0)
                + (_hal * _hbe * z0 - _t9q) / (z0 * (z0 - 1) * (z0 - _t9a)) * f(z0))

    def _t9f1(t):
        return _heunF1(_t9a, _hal, _hbe, _hga, _hde, _t9q, t)

    if abs(_t9res(_t9f1, mp.mpf("0.72"), _hga, _hde)) > mp.mpf("1e-16"):
        fails.append("heunF1: does not solve Heun's equation 31.2.1 (31.2(v) dictionary)")
    if abs(_t9res(lambda t: _heun_fn(1 - _t9a, _hal * _hbe - _t9q, _hal, _hbe,
                                     _hga, _hde, 1 - t), mp.mpf("0.72"), _hga, _hde)) \
            < mp.mpf("1e-8"):
        fails.append("heunF1 discriminator: γ↔δ-unswapped rival not rejected")
    # θ_m (31.9.3): the assembled display against its own factors, and a discriminator
    # showing the ∂/∂q Wronskian factor is not degenerate (a zero would make the row
    # vacuous).
    _t9w = _heun_wronskian_q(_t9a, _hal, _hbe, _hga, _hde, _t9q, _t9z)
    chk("heunTheta = 31.9.3 display",
        _heunTheta(_t9a, _hal, _hbe, _hga, _hde, _t9e, _t9q, _t9z),
        (1 - mp.e ** (2 * mp.pi * mp.mpc(0, 1) * _hga))
        * (1 - mp.e ** (2 * mp.pi * mp.mpc(0, 1) * _hde))
        * mp.power(_t9z, _hga) * mp.power(1 - _t9z, _hde) * mp.power(_t9z - _t9a, _t9e)
        * (_heunF0(_t9a, _hal, _hbe, _hga, _hde, _t9q, _t9z)
           / _heunF1(_t9a, _hal, _hbe, _hga, _hde, _t9q, _t9z)) * _t9w,
        mp.mpf("1e-18"))
    if abs(_t9w) < mp.mpf("1e-8"):
        fails.append("heunTheta: ∂_q Wronskian factor degenerate (vacuous θ)")
    # DLMF 31.3.4 recurrence coefficients P_j, Q_j, R_j and the §31.4(ii) accessory-
    # parameter continued fraction (heunEigenCF).
    #  (i) P/Q/R are anchored DECORRELATED from their own closed forms, through the
    #      three-term recurrence 31.3.3 they are the coefficients of, evaluated on the
    #      independently-anchored heunCoeff sequence: R_j c_{j+1} − (Q_j+q)c_j + P_j c_{j−1} = 0.
    for _pn in (1, 2, 5):
        _pc = _heun_coeff_list(_ha, _hq, _hal, _hbe, _hga, _hde, _pn + 2)
        chk(f"31.3.3 recurrence via P/Q/R at j={_pn}",
            _heunR(_ha, _hga, _pn) * _pc[_pn + 1]
            - (_heunQ(_ha, _hal, _hbe, _hga, _hde, _pn) + _hq) * _pc[_pn]
            + _heunP(_hal, _hbe, _pn) * _pc[_pn - 1], 0, mp.mpf("1e-20"))
    chk("31.3.2 base relation aγc₁ − qc₀ = 0 (R₀ = aγ)",
        _heunR(_ha, _hga, 0) * _heun_coeff(_ha, _hq, _hal, _hbe, _hga, _hde, 1)
        - _hq * _heun_coeff(_ha, _hq, _hal, _hbe, _hga, _hde, 0), 0)
    #  (ii) the u₁ = Hℓ(1−a, αβ−q; α,β,δ,γ; 1−z) map (DLMF 31.3.5) that the eigenvalue
    #      witnesses are built on must solve the ORIGINAL Heun equation; the γ↔δ-unswapped
    #      rival must not.
    _ea, _eq, _eal, _ebe, _ega, _ede = (mp.mpf(t) for t in ("2", "0.83", "0.4", "0.6", "0.9", "1.1"))

    def _eres(f, z0):
        _e = _eal + _ebe + 1 - _ega - _ede
        return (mp.diff(f, z0, 2)
                + (_ega / z0 + _ede / (z0 - 1) + _e / (z0 - _ea)) * mp.diff(f, z0)
                + (_eal * _ebe * z0 - _eq) / (z0 * (z0 - 1) * (z0 - _ea)) * f(z0))

    if abs(_eres(lambda t: _heun_at_one(_ea, _eq, _eal, _ebe, _ega, _ede, t)[0],
                 mp.mpf("0.62"))) > mp.mpf("1e-16"):
        fails.append("_heun_at_one: 31.3.5 map does not solve Heun's equation 31.2.1")
    if abs(_eres(lambda t: _heun_val_deriv(1 - _ea, _eal * _ebe - _eq, _eal, _ebe,
                                           _ega, _ede, 1 - t)[0], mp.mpf("0.62"))) \
            < mp.mpf("1e-8"):
        fails.append("_heun_at_one discriminator: γ↔δ-unswapped rival not rejected")
    chk("_heun_val_deriv value = _heun_fn (same 31.3.1 sum)",
        _heun_val_deriv(_ea, _eq, _eal, _ebe, _ega, _ede, mp.mpf("0.37"))[0],
        _heun_fn(_ea, _eq, _eal, _ebe, _ega, _ede, mp.mpf("0.37")), mp.mpf("1e-18"))
    chk("_heun_val_deriv derivative = numerical d/dz Hℓ",
        _heun_val_deriv(_ea, _eq, _eal, _ebe, _ega, _ede, mp.mpf("0.37"))[1],
        mp.diff(lambda t: _heun_fn(_ea, _eq, _eal, _ebe, _ega, _ede, t), mp.mpf("0.37")),
        mp.mpf("1e-16"))
    #  (iii) the eigenvalue witnesses: nonempty, each genuinely analytic at z = 1
    #      (Hℓ ∝ u₁ — checked at a THIRD point here), and NOT accidental (a shifted q
    #      breaks the proportionality).
    _ews = heun_eigen_witnesses()
    if len(_ews) < 3:
        fails.append(f"heun_eigen_witnesses: only {len(_ews)} certified eigenvalue witnesses")
    for _wa, _wq, _wal, _wbe, _wga, _wde in _ews:
        # both sample points must sit inside BOTH Maclaurin discs: |z| < min(1,|a|) for
        # Hℓ and |1−z| < min(1,|1−a|) for u₁ (family 3 has a = 1.7, so |1−z| < 0.7).
        _p1, _p2 = mp.mpf("0.45"), mp.mpf("0.6")
        _r5 = (_heun_val_deriv(_wa, _wq, _wal, _wbe, _wga, _wde, _p1)[0]
               / _heun_at_one(_wa, _wq, _wal, _wbe, _wga, _wde, _p1)[0])
        _r25 = (_heun_val_deriv(_wa, _wq, _wal, _wbe, _wga, _wde, _p2)[0]
                / _heun_at_one(_wa, _wq, _wal, _wbe, _wga, _wde, _p2)[0])
        chk(f"eigen witness q={mp.nstr(_wq, 8)}: Hℓ ∝ u₁ (analytic at z=1, 31.4.1)",
            _r5, _r25, mp.mpf("1e-16"))
        _bad = _wq + mp.mpf("0.05")
        _b5 = (_heun_val_deriv(_wa, _bad, _wal, _wbe, _wga, _wde, _p1)[0]
               / _heun_at_one(_wa, _bad, _wal, _wbe, _wga, _wde, _p1)[0])
        _b25 = (_heun_val_deriv(_wa, _bad, _wal, _wbe, _wga, _wde, _p2)[0]
                / _heun_at_one(_wa, _bad, _wal, _wbe, _wga, _wde, _p2)[0])
        if abs(_b5 - _b25) < mp.mpf("1e-4"):
            fails.append("eigen witness discriminator: q-shifted parameter still proportional")
    #  (iv) the heunEigenCF stream: its entries ARE the displayed 31.4.2 numerators and
    #      denominators, and — decorrelated from the fraction — its convergents converge
    #      to the independently computed eigenvalue q at every witness, while the
    #      sign-flipped and index-shifted rivals do not.
    _ch, _cpair = heun_eigen_cf(_ea, _eq, _eal, _ebe, _ega, _ede)
    chk("heunEigenCF h = 0 (31.4.2 has no head term)", _ch, 0)
    chk("heunEigenCF a₀ = aγP₁ (31.4.2 numerator)", _cpair(0)[0],
        _ea * _ega * _heunP(_eal, _ebe, 1))
    for _cfn in (1, 2, 4):
        chk(f"heunEigenCF a_{_cfn} = −R_{_cfn}P_{_cfn + 1}", _cpair(_cfn)[0],
            -(_heunR(_ea, _ega, _cfn) * _heunP(_eal, _ebe, _cfn + 1)))
        chk(f"heunEigenCF b_{_cfn} = Q_{_cfn + 1} + q", _cpair(_cfn)[1],
            _heunQ(_ea, _eal, _ebe, _ega, _ede, _cfn + 1) + _eq)
    for _wa, _wq, _wal, _wbe, _wga, _wde in _ews:
        _lim, _k, _dm = cf_convergent_limit(*heun_eigen_cf(_wa, _wq, _wal, _wbe, _wga, _wde))
        if _lim is None:
            fails.append(f"heunEigenCF at eigen witness q={mp.nstr(_wq, 8)}: {_dm}")
            continue
        chk(f"heunEigenCF convs → q at eigen witness q={mp.nstr(_wq, 8)} (31.4.2)",
            _lim, _wq, mp.mpf("1e-18"))
    _wa, _wq, _wal, _wbe, _wga, _wde = _ews[0]
    _fh, _fp = heun_eigen_cf(_wa, _wq, _wal, _wbe, _wga, _wde)
    _flip, _, _ = cf_convergent_limit(_fh, lambda n: (-_fp(n)[0], _fp(n)[1]))
    if _flip is not None and abs(_flip - _wq) < mp.mpf("1e-3"):
        fails.append("heunEigenCF discriminator: sign-flipped numerators still give q")
    _shift, _, _ = cf_convergent_limit(
        _fh, lambda n: (_fp(n)[0], _heunQ(_wa, _wal, _wbe, _wga, _wde, n) + _wq))
    if _shift is not None and abs(_shift - _wq) < mp.mpf("1e-3"):
        fails.append("heunEigenCF discriminator: index-shifted denominators still give q")
    _noneig, _, _ = cf_convergent_limit(*heun_eigen_cf(_wa, _wq + mp.mpf("0.3"),
                                                      _wal, _wbe, _wga, _wde))
    if _noneig is not None and abs(_noneig - (_wq + mp.mpf("0.3"))) < mp.mpf("1e-3"):
        fails.append("heunEigenCF discriminator: non-eigenvalue q still solves 31.4.2")
    # Whittaker (DLMF 13.14.2/13.14.3): the composed defining normalizations against
    # the INDEPENDENT mp.whitm/mp.whitw; κ-sign rival rejected.
    _wk, _wm, _wz = mp.mpf("0.4"), mp.mpf("0.7"), mp.mpf("1.3")
    chk("whittakerM = mp.whitm (13.14.2)", _whittakerM(_wk, _wm, _wz),
        mp.whitm(_wk, _wm, _wz), mp.mpf("1e-18"))
    chk("whittakerW = mp.whitw (13.14.3)", _whittakerW(_wk, _wm, _wz),
        mp.whitw(_wk, _wm, _wz), mp.mpf("1e-18"))
    if abs(mp.whitm(-_wk, _wm, _wz) - _whittakerM(_wk, _wm, _wz)) < mp.mpf("1e-2"):
        fails.append("whittakerM anchor does not distinguish the κ-sign rival")
    chk("tricomiIntegrand reassembles U(a;b;z) (13.4.4)",
        mp.quad(lambda t: _tricomi_integrand(mp.mpf("0.7"), mp.mpf("1.2"), mp.mpf("1.5"), t),
                [0, mp.inf]) / mp.gamma(mp.mpf("0.7")),
        mp.hyperu(mp.mpf("0.7"), mp.mpf("1.2"), mp.mpf("1.5")), mp.mpf("1e-15"))
    chk("NormedSpace.exp = exp", REGISTRY["NormedSpace.exp"][1](mp.mpf("1.3")), mp.e ** mp.mpf("1.3"))
    # Appell F₁/F₂ (DLMF 16.13.1/16.13.2): mp.appellf1 against the DEFINING truncated
    # double series at an ASYMMETRIC point (rejects the b₁↔b₂/x↔y-slot rival); F₂
    # against its independent ₂F₁-row expansion Σₙ (a)ₙ(b₂)ₙ/((c₂)ₙn!) yⁿ ₂F₁(a+n,b₁;c₁;x),
    # and the y = 0 reduction to ₂F₁ (the exact shape of the swept rows).
    _aa, _ab1, _ab2, _ac, _ax, _ay = (mp.mpf(t) for t in ("0.3", "0.4", "0.5", "0.9", "0.2", "0.3"))
    _f1_series = mp.fsum(mp.rf(_aa, m + n) * mp.rf(_ab1, m) * mp.rf(_ab2, n)
                         / (mp.rf(_ac, m + n) * mp.factorial(m) * mp.factorial(n))
                         * _ax ** m * _ay ** n
                         for m in range(45) for n in range(45 - m))
    chk("appellF1 = defining double series (16.13.1)", _appellF1(_aa, _ab1, _ab2, _ac, _ax, _ay),
        _f1_series, mp.mpf("1e-18"))
    if abs(_appellF1(_aa, _ab2, _ab1, _ac, _ax, _ay) - _f1_series) < mp.mpf("1e-6"):
        fails.append("appellF1 anchor does not distinguish the b₁↔b₂ slot rival")
    chk("appellF1(x, 0) = ₂F₁(a,b₁;c;x)", _appellF1(_aa, _ab1, _ab2, _ac, _ax, 0),
        mp.hyp2f1(_aa, _ab1, _ac, _ax), mp.mpf("1e-20"))
    _ac2 = mp.mpf("1.1")
    _f2_rows = mp.fsum(mp.rf(_aa, n) * mp.rf(_ab2, n) / (mp.rf(_ac2, n) * mp.factorial(n))
                       * _ay ** n * mp.hyp2f1(_aa + n, _ab1, _ac, _ax) for n in range(60))
    chk("appellF2 = ₂F₁-row expansion (16.13.2)", _appellF2(_aa, _ab1, _ab2, _ac, _ac2, _ax, _ay),
        _f2_rows, mp.mpf("1e-18"))
    chk("appellF2(x, 0) = ₂F₁(a,b₁;c₁;x)", _appellF2(_aa, _ab1, _ab2, _ac, _ac2, _ax, 0),
        mp.hyp2f1(_aa, _ab1, _ac, _ax), mp.mpf("1e-20"))
    if abs(_appellF2(_aa, _ab1, _ab2, _ac2, _ac, _ax, _ay) - _f2_rows) < mp.mpf("1e-6"):
        fails.append("appellF2 anchor does not distinguish the c₁↔c₂ slot rival")
    # physHermite (Normalization.lean): the Lean def is Heₙ(2x) — anchored to the
    # independent closed form 2^{−n/2}Hₙ(√2·x) at 2x… i.e. 2^{−n/2}·mp.hermite(n, √2 x),
    # top coefficient 2ⁿ, and the TRUE-physicists' rival mp.hermite(n, x) rejected.
    _px = mp.mpf("0.7")
    _pH = REGISTRY["physHermite"][1]
    for _pn in (2, 3):
        chk(f"physHermite {_pn} = 2^(−n/2)·H_n(√2·x) (Heₙ∘2X)", _pH(_pn, _px),
            mp.mpf(2) ** (-mp.mpf(_pn) / 2) * mp.hermite(_pn, mp.sqrt(2) * _px), mp.mpf("1e-20"))
    chk("physHermite 2 @0.7 = 4x²−1 = 0.96", _pH(2, _px), mp.mpf("0.96"))
    if abs(_pH(2, _px) - mp.hermite(2, _px)) < mp.mpf("1e-2"):
        fails.append("physHermite anchor does not distinguish the true-physicists' rival")
    chk("physHermite top Taylor coeff = 2ⁿ (n=3)",
        mp.taylor(lambda t: _pH(3, t), 0, 3)[3], 8, mp.mpf("1e-15"))
    # algCoeff (Darboux scale): rising-factorial content via the EXACT Catalan identity
    # Cₙ = −2·4ⁿ·algCoeff(−1/2)(n+1) (DLMF 26.5.2); falling-factorial rival rejected.
    for _catn in (3, 5):
        chk(f"algCoeff: catalan {_catn} = −2·4ⁿ·algCoeff(−½)({_catn}+1) (26.5.2)",
            -2 * mp.mpf(4) ** _catn * _alg_coeff(mp.mpf("-0.5"), _catn + 1), _catalan(_catn))
    if abs(_alg_coeff(mp.mpf("-0.5"), 2) - mp.ff(mp.mpf("-0.5"), 2) / 2) < mp.mpf("1e-6"):
        fails.append("algCoeff anchor does not distinguish rising from falling factorial")
    # q-exponentials (DLMF 17.2): the defining-series binding against the independent
    # infinite-product side 1/(z;q)_∞ (mp.qp) and the e_q(z)·E_q(−z) = 1 involution;
    # E_q ≠ e_q at the same point (rival rejected); (a;q)_∞ against a truncated product.
    _qz, _qq = mp.mpf("0.4"), mp.mpf("0.6")
    chk("qExp = 1/(z;q)_∞ (17.2)", _qexp(_qz, _qq), 1 / mp.qp(_qz, _qq), mp.mpf("1e-18"))
    chk("e_q(z)·E_q(−z) = 1 (17.2)", _qexp(_qz, _qq) * _qexpE(-_qz, _qq), 1, mp.mpf("1e-18"))
    chk("qExp term ratio n=2: z²/((1−q)(1−q²))",
        _qz ** 2 / ((1 - _qq) * (1 - _qq ** 2)),
        _qz ** 2 / mp.qp(_qq, _qq, 2), mp.mpf("1e-20"))
    if abs(_qexp(_qz, _qq) - _qexpE(_qz, _qq)) < mp.mpf("1e-2"):
        fails.append("qExp anchor does not distinguish e_q from E_q")
    chk("qPochhammerInf = truncated defining product",
        _qpochhammer_inf(_qz, _qq),
        mp.fprod(1 - _qz * _qq ** k for k in range(220)), mp.mpf("1e-20"))
    chk_raises("qExp raises at |q| ≥ 1 (junk regime)", lambda: _qexp(_qz, mp.mpf("1.1")))
    # Laplace transform (DLMF 1.14.17): decorrelated elementary anchors L[1](s) = 1/s,
    # L[e^{−t}](s) = 1/(s+1); the fC integrand against mp.erf, with the Mathlib
    # √(negative) = 0 junk mirrored (fC(b)(t) = 0 for bt < 0, not the imaginary erf).
    _ls = mp.mpf("1.1")
    chk("laplaceTransform 1 → 1/s", _laplace_transform(lambda t: mp.mpf(1), _ls),
        1 / _ls, mp.mpf("1e-18"))
    chk("laplaceTransform e^{−t} → 1/(s+1)", _laplace_transform(lambda t: mp.e ** (-t), _ls),
        1 / (_ls + 1), mp.mpf("1e-18"))
    chk("fC(0.8)(1.3) = erf(√1.04)", _fC(mp.mpf("0.8"))(mp.mpf("1.3")),
        mp.erf(mp.sqrt(mp.mpf("1.04"))), mp.mpf("1e-20"))
    chk("fC junk: √(x<0) = 0 ⇒ fC(0.8)(−1) = 0", _fC(mp.mpf("0.8"))(mp.mpf(-1)), 0)
    chk_raises("laplaceTransform raises off the half-plane",
               lambda: _laplace_transform(lambda t: mp.mpf(1), mp.mpf("-0.5")))
    # Complex.cot: quotient definition at a complex point (= mp.cot).
    _cz = mp.mpc("0.7", "0.4")
    chk("Complex.cot = cos/sin @ 0.7+0.4i", REGISTRY["Complex.cot"][1](_cz),
        mp.cos(_cz) / mp.sin(_cz), mp.mpf("1e-20"))
    # DLMF 7.13 zero parameters: the (λ, μ)/(λ, α) approximants land near an ACTUAL
    # first-quadrant zero of erf/erfc/C/S (small |f|), while the rival conventions
    # ((n+1/8)π sign, un-doubled erfc μ, √(4n+1) Fresnel λ) miss by O(1). Fresnel
    # zeros satisfy z² ≈ λ² + iα (DLMF 7.13.5–7.13.7). Junk values at n = 0 mirror
    # Mathlib (√(neg) = 0, log 0 = 0).
    for _zn in (2, 5):
        _el, _em = _erf_zero_lambda(_zn), _erf_zero_mu(_zn)
        if abs(mp.erf(mp.mpc(_el - _em / (4 * _el), _el + _em / (4 * _el)))) > mp.mpf("0.05"):
            fails.append(f"erf zero params (7.13.1/2) miss the zero at n={_zn}")
        _erl = mp.sqrt((_zn + mp.mpf(1) / 8) * mp.pi)
        _erm = mp.log(_erl * mp.sqrt(2 * mp.pi))
        if abs(mp.erf(mp.mpc(_erl - _erm / (4 * _erl), _erl + _erm / (4 * _erl)))) < mp.mpf("0.5"):
            fails.append("erf zero rival (n+1/8) not rejected")
        _cl, _cm = _erf_zero_lambda(_zn), _erfc_zero_mu(_zn)
        if abs(mp.erfc(mp.mpc(-_cl + _cm / (4 * _cl), _cl + _cm / (4 * _cl)))) > mp.mpf("0.2"):
            fails.append(f"erfc zero params (7.13.3/4) miss the zero at n={_zn}")
        _cmr = _erf_zero_mu(_zn)   # un-doubled rival μ
        if abs(mp.erfc(mp.mpc(-_cl + _cmr / (4 * _cl), _cl + _cmr / (4 * _cl)))) < mp.mpf("0.5"):
            fails.append("erfc zero rival (un-doubled μ) not rejected")
        _fl, _falp = _fresnelC_zero_lambda(_zn), _fresnelC_zero_alpha(_zn)
        if abs(mp.fresnelc(mp.sqrt(_fl ** 2 + mp.mpc(0, 1) * _falp))) > mp.mpf("0.05"):
            fails.append(f"fresnelC zero params (7.13.5/6) miss the zero at n={_zn}")
        _flr = mp.sqrt(4 * mp.mpf(_zn) + 1)
        _falr = (2 / mp.pi) * mp.log(mp.pi * _flr)
        if abs(mp.fresnelc(mp.sqrt(_flr ** 2 + mp.mpc(0, 1) * _falr))) < mp.mpf("0.5"):
            fails.append("fresnelC zero rival √(4n+1) not rejected")
        _sl, _salp = _fresnelS_zero_lambda(_zn), _fresnelS_zero_alpha(_zn)
        if abs(mp.fresnels(mp.sqrt(_sl ** 2 + mp.mpc(0, 1) * _salp))) > mp.mpf("0.05"):
            fails.append(f"fresnelS zero params (7.13.7) miss the zero at n={_zn}")
        _slr = _fresnelC_zero_lambda(_zn)
        _salr = (2 / mp.pi) * mp.log(mp.pi * _slr)
        if abs(mp.fresnels(mp.sqrt(_slr ** 2 + mp.mpc(0, 1) * _salr))) < mp.mpf("0.5"):
            fails.append("fresnelS zero rival (C-family λ) not rejected")
    chk("7.13 n=0 Mathlib junk: λ, μ, λC, αC, λS, αS all 0",
        abs(_erf_zero_lambda(0)) + abs(_erf_zero_mu(0)) + abs(_erfc_zero_mu(0))
        + abs(_fresnelC_zero_lambda(0)) + abs(_fresnelC_zero_alpha(0))
        + abs(_fresnelS_zero_lambda(0)) + abs(_fresnelS_zero_alpha(0)), 0)
    # ── A4 final-batch anchors ───────────────────────────────────────────────────────
    # Nat.primeCounting (DLMF §27.2.2): classical exact values, the INCLUSIVE-vs-strict
    # discriminator at a prime argument (π(3) = 2; Mathlib's strict π′(3) = 1), and the
    # sieve cap guard (never an unbounded allocation).
    chk("π(1)=0", _prime_counting(1), 0)
    chk("π(2)=1", _prime_counting(2), 1)
    chk("π(3)=2 (inclusive; strict-count rival π′(3)=1 rejected)", _prime_counting(3), 2)
    chk("π(10)=4", _prime_counting(10), 4)
    chk("π(100)=25", _prime_counting(100), 25)
    chk("π(1000)=168", _prime_counting(1000), 168)
    chk("π(10⁵)=9592", _prime_counting(100000), 9592)
    chk_raises("π raises above the 2e6 sieve cap", lambda: _prime_counting(3 * 10 ** 6))
    # real complementary modulus k′(k) = √(1−k²) (DLMF 19.2.5): the k = 0.6 → 0.8 pin,
    # the defining k² + k′² = 1, the Mathlib √(neg) = 0 junk point, COHERENCE with the
    # τ-parametrization (√(1 − k(τ)²) must equal the Theta-form (θ₄/θ₃)²(τ) — the same
    # k′ reached through the two conventions), and the ALIASING discriminator: at the
    # numerically identical input 0.6 the k-form and τ-form must NOT agree (a bare-key
    # alias would silently evaluate the wrong function; cf. _NS_STRIP_BLOCK).
    chk("k′(0.6)=0.8 (19.2.5)", _complementary_modulus_real(mp.mpf("0.6")), mp.mpf("0.8"))
    chk("k′²+k²=1 @ k=0.35", _complementary_modulus_real(mp.mpf("0.35")) ** 2
        + mp.mpf("0.35") ** 2, 1)
    chk("k′ Mathlib junk √(neg)=0 @ k=1.7", _complementary_modulus_real(mp.mpf("1.7")), 0)
    _a4t = mp.mpc(0, "0.8")
    chk("k′ coherence: √(1−k(τ)²) = (θ₄/θ₃)²(τ) @ τ=0.8i",
        _complementary_modulus_real(mp.re(_elliptic_modulus(_a4t))),
        _complementary_modulus(_a4t), mp.mpf("1e-18"))
    if abs(_complementary_modulus_real(mp.mpf("0.6"))
           - _complementary_modulus(mp.mpc(0, "0.6"))) < mp.mpf("1e-2"):
        fails.append("complementaryModulus k-form vs τ-form: aliasing point does not distinguish")
    # incomplete-Beta integrand (DLMF 8.17.1): the FTC anchor d/dx B(x;a,b) = integrand
    # (independent mp.betainc + numeric differentiation — the row's own content), the
    # literal exponent form, and the t^a(1−t)^b exponent-shift rival rejection.
    _ba, _bb, _bx = mp.mpf("2.3"), mp.mpf("1.7"), mp.mpf("0.4")
    chk("integrand = d/dx B(x;a,b) (8.17 FTC)", _beta_integrand(_ba, _bb, _bx),
        mp.diff(lambda y: mp.betainc(_ba, _bb, 0, y), _bx), mp.mpf("1e-15"))
    chk("integrand literal t^{a−1}(1−t)^{b−1}", _beta_integrand(_ba, _bb, _bx),
        _bx ** (_ba - 1) * (1 - _bx) ** (_bb - 1))
    if abs(_beta_integrand(_ba, _bb, _bx) - _bx ** _ba * (1 - _bx) ** _bb) < mp.mpf("1e-2"):
        fails.append("integrand: exponent-shift rival not distinguished at the anchor point")
    # Binet's function (the existing M14 _binet, now also under its qualified keys —
    # DLMF §5.9/5.11.1): Binet's SECOND formula by quadrature (5.9.9, decorrelated
    # from _binet's log|Γ| route), the 5.11.1 tail at z = 20 (tight enough to reject
    # the missing-½log(2π) rival by O(1) — also asserted explicitly), and the
    # tendsto_x_binet row's own x·binet(x) → 1/12 value at x = 200. (binet(1) and the
    # 5.9 difference equation are already anchored in the M14 block above.)
    _bz = mp.mpf("1.5")
    chk("binet = 2∫₀^∞ arctan(t/z)/(e^{2πt}−1)dt @ z=1.5 (5.9.9)", _binet(_bz),
        2 * mp.quad(lambda t: mp.atan(t / _bz) / mp.expm1(2 * mp.pi * t), [0, mp.inf]),
        mp.mpf("1e-18"))
    chk("binet(20) = 1/240 − 1/(360·20³) + 1/(1260·20⁵) + O(20⁻⁷) (5.11.1)", _binet(20),
        mp.mpf(1) / 240 - mp.mpf(1) / (360 * 20 ** 3) + mp.mpf(1) / (1260 * 20 ** 5),
        mp.mpf("1e-11"))
    if abs(_binet(20) + mp.log(2 * mp.pi) / 2 - mp.mpf(1) / 240) < mp.mpf("0.5"):
        fails.append("binet: missing-½log(2π) rival not rejected")
    chk("x·binet(x) @ x=200 ≈ 1/12 (5.11.1, the tendsto_x_binet target)",
        200 * _binet(200), mp.mpf(1) / 12, mp.mpf("1e-7"))
    # AP prime sum (helper, DLMF 27.11.11 — anchored though unregistered, see the
    # NOT-bound note): exact small-cutoff defining sums in both residue classes mod 4,
    # the residue partition Σ_a ap(a, 3, 50) = the full Mertens sum ∑_{p≤50} log p/p
    # (couples the filter to the unfiltered DLMF 27.11.10 object), and the cap guard.
    chk("apPrimeSum(1 mod 4, 20) = log5/5 + log13/13 + log17/17",
        _ap_prime_sum(1, 4, 20), mp.log(5) / 5 + mp.log(13) / 13 + mp.log(17) / 17)
    chk("apPrimeSum(3 mod 4, 20) = log3/3 + log7/7 + log11/11 + log19/19",
        _ap_prime_sum(3, 4, 20),
        mp.log(3) / 3 + mp.log(7) / 7 + mp.log(11) / 11 + mp.log(19) / 19)
    chk("residue partition: Σ_{a<3} ap(a,3,50) = ∑_{p≤50} log p/p",
        mp.fsum(_ap_prime_sum(r, 3, 50) for r in range(3)),
        mp.fsum(mp.log(p) / p
                for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)))
    chk_raises("apPrimeSum raises above the sieve cap",
               lambda: _ap_prime_sum(1, 4, 3 * 10 ** 6))

    # ── A5 final batch anchors ────────────────────────────────────────────────
    # GammaSeq (DLMF 5.8.1): the finite Euler/Gauss approximant converges to Γ, and the
    # denominator is rf(s,n+1) (length n+1) — the off-by-one rf(s,n) rival is ~200× off.
    _gsc, _gsr = REGISTRY["Complex.GammaSeq"][1], REGISTRY["Real.GammaSeq"][1]
    for _gs in (mp.mpf("1.5"), mp.mpf("2.5")):
        _err_hi = abs(_gsr(_gs, 50) - mp.gamma(_gs)) / abs(mp.gamma(_gs))
        _err_lo = abs(_gsr(_gs, 800) - mp.gamma(_gs)) / abs(mp.gamma(_gs))
        if not (_err_lo < _err_hi and _err_lo < mp.mpf("0.01")):
            fails.append(f"Real.GammaSeq({_gs}) not converging to Γ (errs {mp.nstr(_err_hi,3)}→{mp.nstr(_err_lo,3)})")
    _gsz = mp.mpc("0.3", "0.7")
    if not abs(_gsc(_gsz, 800) - mp.gamma(_gsz)) / abs(mp.gamma(_gsz)) < mp.mpf("0.01"):
        fails.append("Complex.GammaSeq not converging to Γ at 0.3+0.7i")
    _rival = mp.mpf("200") ** mp.mpf("1.5") * mp.factorial(200) / mp.rf(mp.mpf("1.5"), 200)  # rf(s,n)
    if abs(_rival - mp.gamma(mp.mpf("1.5"))) / abs(mp.gamma(mp.mpf("1.5"))) < mp.mpf("1"):
        fails.append("GammaSeq off-by-one rival rf(s,n) not distinguished from rf(s,n+1)")
    # signedFirst (DLMF 26.8): natAbs s(n,k)=c(n,k); sign is (−1)^(n−k); k>n → 0
    _sf = REGISTRY["signedFirst"][1]
    chk("signedFirst s(5,2)=−c(5,2)=−50", _sf(5, 2), mp.mpf(-50))
    chk("signedFirst s(4,2)=+c(4,2)=11", _sf(4, 2), mp.mpf(11))
    for _sfn, _sfk in ((6, 3), (7, 4), (5, 0), (3, 5)):
        if abs(_sf(_sfn, _sfk)) != _stirling1u(_sfn, _sfk):
            fails.append(f"natAbs_signedFirst: |s({_sfn},{_sfk})| ≠ c({_sfn},{_sfk})")
    chk("stirling1u c(3,5)=0 (k>n, was IndexError)", _stirling1u(3, 5), mp.mpf(0))
    # expint_6_10_1_laplaceCoeff (DLMF 6.10.1): equals cCoeff (6.10.3 recurrence); the
    # exact Γ-moment integral must match the independent cCoeff recurrence at every k.
    _lc = REGISTRY["expint_6_10_1_laplaceCoeff"][1]
    for _lk in range(0, 8):
        chk(f"laplaceCoeff({_lk}) = cCoeff({_lk})", _lc(_lk), _ccoeff(_lk))
    # qHyper (DLMF 17.4.1): q-binomial ₁φ₀(a;;q,z) = (az;q)_∞/(z;q)_∞ (the qHyper_one_zero
    # identity) and Euler's ₀φ₀(;;q,z) = (z;q)_∞ (exercises the s+1−r=1 exponent); the rival
    # dropping the (−1)ⁿq^{C(n,2)} factor sums to 1/(z;q)_∞ — a genuine distinguishing point.
    _qhy = REGISTRY["qHyper"][1]
    _qq, _qz, _qa = mp.mpf("0.3"), mp.mpf("0.4"), mp.mpf("0.7")
    chk("qHyper ₁φ₀(a;;q,z)=(az;q)∞/(z;q)∞", _qhy(1, 0, [_qa], [], _qq, _qz),
        mp.qp(_qa * _qz, _qq) / mp.qp(_qz, _qq))
    chk("qHyper ₀φ₀(;;q,z)=(z;q)∞ (exp s+1−r=1)", _qhy(0, 0, [], [], _qq, _qz), mp.qp(_qz, _qq))
    if abs(_qhy(0, 0, [], [], _qq, _qz) - 1 / mp.qp(_qz, _qq)) < mp.mpf("1e-3"):
        fails.append("qHyper exponent anchor: sign-factor-dropping rival 1/(z;q)∞ not distinguished")

    # every CONVENTIONS row with a rejected alternative must GENUINELY distinguish
    for c in CONVENTIONS:
        if c["theirs"] is not None and abs(c["ours"]() - c["theirs"]()) < mp.mpf("1e-9"):
            fails.append(f"convention {c['func']}: distinguishing point does not distinguish")
    return fails


if __name__ == "__main__":
    fails = verify()
    if fails:
        print("REGISTRY ANCHOR FAILURES:")
        for f in fails:
            print("  ✗", f)
        raise SystemExit(1)
    print(f"oracle_bindings: all {len(REGISTRY)} bindings present; every anchor verified ✓")
