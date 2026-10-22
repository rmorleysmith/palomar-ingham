module

public import PalomarIngham.Ingham.LogDerivBound
public import PalomarIngham.Ingham.ContourBounds
public import PalomarIngham.Ingham.Assembly

/-!
# Ingham's theorem (hard direction), and the consequence of OpenAI's quasi-RH

* `Ingham.psiError_of_zeroFreeRight` — if `ζ(s) ≠ 0` for `Re s > θ` with `1/2 ≤ θ < 1`, then
  `ψ(x) = x + O(x^{θ+δ})` for every `δ > 0`.
* `Ingham.psiError_of_RH` — RH gives `ψ(x) = x + O(x^{1/2+δ})` (von Koch's theorem, ε-form).
* `Ingham.psiError_seven_eighths_of_openAI` — OpenAI's statement (copied verbatim from their
  comparator challenge) gives `ψ(x) = x + O(x^{7/8+δ})`.
-/

@[expose] public section


open Complex

namespace Ingham

theorem psiError_of_zeroFreeRight {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hz : ZeroFreeRight θ) : ∀ δ > 0, PsiError (θ + δ) := by
  refine psiError_of_bounds hθ hθ1 hz
    (fun σ₁ hσ _ => logDerivLogBound_of_zeroFreeRight hθ hσ hz) ?_
  intro ν σ₁ κ hν hσ hσ1 hκ hκ1 hA
  have hθ0 : 0 < θ := by linarith
  exact ⟨i37Bound hν hσ hσ1 hθ0 hz hA hκ hκ1, i2Bound hν hσ hσ1 hθ0 hz hA,
    i8Bound hν hσ hσ1 hθ0 hz hA⟩

/-- OpenAI's theorem, verbatim from `ComparatorChallenges/QuasiRiemannHypothesis.lean`. -/
def OpenAIStatement : Prop :=
  ∀ {s : ℂ}, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

/-- **The prime number theorem with error `O(x^{7/8+δ})`, from OpenAI's quasi-RH.** -/
theorem psiError_seven_eighths_of_openAI (h : OpenAIStatement) :
    ∀ δ > 0, PsiError (7 / 8 + δ) :=
  psiError_of_zeroFreeRight (by norm_num) (by norm_num) (fun _ hs => h hs)

/-- **von Koch (1901), ε-form.** RH implies `ψ(x) = x + O(x^{1/2+δ})`. -/
theorem psiError_of_RH (hRH : RiemannHypothesis) : ∀ δ > 0, PsiError (1 / 2 + δ) := by
  refine psiError_of_zeroFreeRight (by norm_num) (by norm_num) ?_
  intro s hs hzero
  have hs1 : s ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hzero
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : ((-2 * ((n : ℂ) + 1)) : ℂ).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s hzero htriv hs1
  linarith

end Ingham
