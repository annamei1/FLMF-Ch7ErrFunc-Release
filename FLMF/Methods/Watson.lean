import PicardLefschetz.Watson

/-!
# Watson's lemma (method kit — DLMF §2.3)

Leading-order asymptotics of half-line Laplace integrals: for `s > 0` and `g`
measurable, bounded on `(0,∞)` with a limit `a₀` at `0⁺`,

`x^s · ∫_{(0,∞)} e^{−x t} t^{s−1} g(t) dt → a₀ · Γ(s)` as `x → ∞`.

Re-exported from the `picard-lefschetz` method spine so chapters import
`FLMF.Methods.Watson` rather than `PicardLefschetz.*` directly. Unlocks the leading
asymptotics of the exponential integral `E₁`, the error function, and the
incomplete Gamma function.

Surfaced (namespace `PicardLefschetz`):

* `watson_leading` — the leading-order Watson's lemma above.
* `watson_growth` — the same conclusion under an *exponential-growth* amplitude
  `|g t| ≤ C·e^{c t}` (the integral converges for `x > c`; the leading constant is
  unchanged). Unblocks the incomplete-Γ asymptotic for general order `a`.
* `watson_next_order` — the **second term**: for `g t = a₀ + t·h t`,
  `x·(x^s ∫ e^{−x t} t^{s−1} g − a₀ Γ(s)) → a₁ Γ(s+1)`.
* `watson_series` — the **full N-term asymptotic series**: for
  `g t = Σ_{k<N} aₖ tᵏ + tᴺ h t`,
  `xᴺ·(x^s ∫ e^{−x t} t^{s−1} g − Σ_{k<N} aₖ Γ(s+k) x^{−k}) → aₙ Γ(s+N)`.
  (Polynomial integrated exactly via the moment; remainder reduces to
  `watson_leading` at `s+N`. `watson_next_order` is the `N=1` case.)
* `integral_exp_neg_mul_rpow_Ioi` — the scaled Gamma moment
  `∫_{(0,∞)} e^{−x t} t^{s−1} dt = Γ(s)·x^{−s}`.

The Watson spine is complete: moment · leading · growth · next-order · N-term series.
-/
