module

public import Mathlib
public import PalomarIngham

/-!
# Solution: proofs of the statements in `Challenge.lean`

Each theorem restates the corresponding Challenge declaration verbatim and proves it from the
library `PalomarIngham` (`PalomarIngham/Ingham/Equivalence.lean`).
-/

@[expose] public section

open Filter Asymptotics

namespace PalomarIngham

theorem zeta_ne_zero_iff_psi_error {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    (∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) ↔
      ∀ δ : ℝ, 0 < δ → (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (θ + δ)) := by
  simpa only [Ingham.PsiError, Ingham.ZeroFreeRight] using Ingham.zeroFreeRight_iff_psiError hθ hθ1

theorem riemannHypothesis_iff_psi_error :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (1 / 2 + δ)) := by
  simpa only [Ingham.PsiError] using Ingham.riemannHypothesis_iff_psiError

theorem psi_error_of_zeta_ne_zero_seven_eighths
    (h : ∀ {s : ℂ}, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0) :
    ∀ δ : ℝ, 0 < δ → (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (7 / 8 + δ)) := by
  simpa only [Ingham.PsiError] using Ingham.psiError_seven_eighths_of_openAI h

end PalomarIngham
