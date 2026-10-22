module

public import Mathlib

/-!
# Ingham's theorem: zero-free half-planes of ζ ⟺ power-saving error in the PNT

Write `ψ(x) = ∑_{n ≤ x} Λ(n)` (Mathlib's `Chebyshev.psi`). For `1/2 ≤ θ < 1`:

  `ζ(s) ≠ 0` for all `Re s > θ`  ⟺  `ψ(x) - x = O(x^{θ+δ})` as `x → ∞`, for every `δ > 0`.

This is classical (Ingham, *The Distribution of Prime Numbers*, 1932, Ch. IV; the case `θ = 1/2`
is von Koch, 1901). Two consequences are stated separately:

* `riemannHypothesis_iff_psi_error` — the Riemann hypothesis (Mathlib's `RiemannHypothesis`) holds
  iff `ψ(x) - x = O(x^{1/2+δ})` for every `δ > 0`;
* `psi_error_of_zeta_ne_zero_seven_eighths` — the zero-free half-plane `Re s > 7/8` (proved by
  OpenAI in 2026 in a separate Lean formalisation; here it is a **hypothesis**, stated exactly as in
  OpenAI's comparator challenge `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`) gives
  `ψ(x) - x = O(x^{7/8+δ})` for every `δ > 0`.

No new definitions are introduced.
-/

@[expose] public section

open Filter Asymptotics

namespace PalomarIngham

/-- **Ingham's theorem.** For `1/2 ≤ θ < 1`, `ζ` has no zeros in `Re s > θ` if and only if
`ψ(x) = x + O(x^{θ+δ})` for every `δ > 0`. -/
theorem zeta_ne_zero_iff_psi_error {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    (∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) ↔
      ∀ δ : ℝ, 0 < δ → (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (θ + δ)) := by
  sorry

/-- **von Koch (ε-form).** RH holds iff `ψ(x) = x + O(x^{1/2+δ})` for every `δ > 0`. -/
theorem riemannHypothesis_iff_psi_error :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (1 / 2 + δ)) := by
  sorry

/-- **From a zero-free half-plane `Re s > 7/8` to the prime number theorem with error
`O(x^{7/8+δ})`.** The hypothesis is OpenAI's 2026 theorem, verbatim. -/
theorem psi_error_of_zeta_ne_zero_seven_eighths
    (h : ∀ {s : ℂ}, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) :
    ∀ δ : ℝ, 0 < δ → (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (7 / 8 + δ)) := by
  sorry

end PalomarIngham
