module

public import PalomarIngham.Dirichlet.Basic

/-!
# Ingham's theorem for Dirichlet `L`-functions: assembly of the contour-shift bounds

Twisted analogue of `PalomarIngham/Ingham/Assembly.lean`. Assuming the smoothing, contour-shift
and contour-piece bounds (as `Prop`s from `Dirichlet.Basic`), we deduce
`ψ(x, χ) = O(x^{θ+δ})`, with the choices `σ₁ = θ + δ/2`, `κ = δ/4`, `ε = X^{σ₁-1}`, `T = X`.
Since there is no pole, there is no main term.
-/

@[expose] public section

set_option autoImplicit false

open Set Function Filter Complex Real Asymptotics MeasureTheory

namespace InghamL

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- `‖ψ(x, χ)‖ ≤ ψ(x)`. -/
lemma norm_psiChi_le (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖psiChi χ x‖ ≤ Chebyshev.psi x := by
  unfold psiChi Chebyshev.psi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (DirichletCharacter.norm_le_one χ _)

omit [NeZero q] in
/-- The trivial case: exponent at least `1` (Chebyshev's bound). -/
lemma psiChiError_of_one_le (χ : DirichletCharacter ℂ q) {α : ℝ} (hα : 1 ≤ α) :
    PsiChiError χ α := by
  refine IsBigO.of_bound (Real.log 4 + 4) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h1 := Chebyshev.psi_le_const_mul_self (x := x) (by linarith)
  have h2 := norm_psiChi_le χ x
  have h3 : x ≤ x ^ α := by
    calc x = x ^ (1 : ℝ) := (rpow_one x).symm
    _ ≤ x ^ α := rpow_le_rpow_of_exponent_le hx hα
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith

lemma norm_six_le (a b c d e f : ℂ) :
    ‖-a + b - c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (-a + b - c + d + e) f
  have h2 := norm_add_le (-a + b - c + d) e
  have h3 := norm_add_le (-a + b - c) d
  have h4 := norm_sub_le (-a + b) c
  have h5 := norm_add_le (-a) b
  have h6 := norm_neg a
  linarith

/-- The decomposition of `ψ(X, χ)` coming from the contour shift. -/
lemma psiChi_le_pieces (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ} {σ₁ ε X T : ℝ}
    (hS : ShiftProp χ ν σ₁) (hε : 0 < ε) (hε1 : ε < 1) (hX : 3 < X) (hT : 3 < T) :
    ‖psiChi χ X‖ ≤ ‖SmoothedChebyshevL χ ν ε X - psiChi χ X‖ +
      ‖J₁ χ ν ε X T‖ + ‖J₂ χ ν ε T X σ₁‖ + ‖J₃₇ χ ν ε T X σ₁‖ + ‖J₈ χ ν ε T X σ₁‖ +
      ‖J₉ χ ν ε X T‖ := by
  have key : psiChi χ X =
      -(SmoothedChebyshevL χ ν ε X - psiChi χ X) + J₁ χ ν ε X T - J₂ χ ν ε T X σ₁ +
        J₃₇ χ ν ε T X σ₁ + J₈ χ ν ε T X σ₁ + J₉ χ ν ε X T := by
    rw [hS ε hε hε1 X hX T hT]; ring
  conv_lhs => rw [key]
  exact norm_six_le _ _ _ _ _ _

lemma div_le_of_sq {c X L P : ℝ} (hc : 0 ≤ c) (hP : 0 < P) (hL : 0 ≤ L) (hPP : X ≤ P * P) :
    c * X * L / P ≤ c * (P * L) := by
  rw [div_le_iff₀ hP]
  have := mul_le_mul_of_nonneg_left hPP (mul_nonneg hc hL)
  calc c * X * L = c * L * X := by ring
    _ ≤ c * L * (P * P) := this
    _ = c * (P * L) * P := by ring

lemma div_le_of_sq' {c X L P : ℝ} (hc : 0 ≤ c) (hP : 1 ≤ P) (hX : 0 < X) (hL : 0 ≤ L) :
    c * X * L / (P * X) ≤ c * (P * L) := by
  have hP0 : 0 < P := by linarith
  rw [div_le_iff₀ (mul_pos hP0 hX)]
  have h1 : 1 ≤ P * P := by nlinarith
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg hc hL) hX.le)
  calc c * X * L = c * L * X * 1 := by ring
    _ ≤ c * L * X * (P * P) := this
    _ = c * (P * L) * (P * X) := by ring

theorem psiChiError_of_bounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {θ : ℝ} (hθ : 1 / 2 ≤ θ) (_hθ1 : θ < 1)
    (hB : ∀ (ν : ℝ → ℝ) (σ₁ κ : ℝ), Ingham.SmoothingData ν → θ < σ₁ → σ₁ < 1 → 0 < κ → κ < 1 →
      CloseProp χ ν ∧ ShiftProp χ ν σ₁ ∧ J19BoundProp χ ν ∧
      J37BoundProp χ ν σ₁ κ ∧ J28BoundProp χ ν σ₁) :
    ∀ δ > 0, PsiChiError χ (θ + δ) := by
  intro δ hδ
  by_cases hα : 1 ≤ θ + δ
  · exact psiChiError_of_one_le χ hα
  replace hα : θ + δ < 1 := not_le.mp hα
  set σ₁ : ℝ := θ + δ / 2 with hσ₁def
  set κ : ℝ := δ / 4 with hκdef
  have hθσ : θ < σ₁ := by linarith
  have hσ₁1 : σ₁ < 1 := by linarith
  have hσ₁0 : 0 < σ₁ := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ < 1 := by linarith
  obtain ⟨ν, hνsmooth, hνnonneg, hνsupp, hνmass⟩ := SmoothExistence
  have hν : Ingham.SmoothingData ν := ⟨hνsmooth.of_le (by simp), fun x _ => hνnonneg x, hνsupp,
    by rwa [← integral_Ici_eq_integral_Ioi]⟩
  obtain ⟨⟨cc, ccpos, hclose⟩, hS, ⟨c19, c19pos, h19⟩, ⟨c37, c37pos, h37⟩,
    ⟨c28, c28pos, h28⟩⟩ := hB ν σ₁ κ hν hθσ hσ₁1 hκ0 hκ1
  have ev2 : ∀ᶠ X : ℝ in atTop, 2 < X ^ σ₁ := (tendsto_rpow_atTop hσ₁0).eventually_gt_atTop 2
  refine IsBigO.of_bound ((cc + 2 * c19 + 2 * c28) * (2 / δ) + c37) ?_
  filter_upwards [eventually_gt_atTop (3 : ℝ), ev2] with X hX hX2
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  set ε : ℝ := X ^ (σ₁ - 1) with hεdef
  set P : ℝ := X ^ σ₁ with hPdef
  set L : ℝ := Real.log X with hLdef
  have hεpos : 0 < ε := rpow_pos_of_pos hX0 _
  have hε1 : ε < 1 := rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hεP : ε = P / X := rpow_sub_one hX0.ne' σ₁
  have hεX : X * ε = P := by rw [hεP]; field_simp
  have hPpos : 0 < P := rpow_pos_of_pos hX0 _
  have hP1 : 1 ≤ P := one_le_rpow hX1 hσ₁0.le
  have hPP : X ≤ P * P := by
    rw [hPdef, ← rpow_add hX0]
    calc X = X ^ (1 : ℝ) := (rpow_one X).symm
      _ ≤ X ^ (σ₁ + σ₁) := rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hL0 : 0 ≤ L := Real.log_nonneg hX1
  have hXα0 : 0 ≤ X ^ (θ + δ) := (rpow_pos_of_pos hX0 _).le
  have hPL : P * L ≤ (2 / δ) * X ^ (θ + δ) := by
    have hlog := Real.log_le_rpow_div hX0.le (half_pos hδ)
    have hexp : σ₁ + δ / 2 = θ + δ := by rw [hσ₁def]; ring
    calc P * L ≤ P * (X ^ (δ / 2) / (δ / 2)) := by gcongr
      _ = (2 / δ) * (X ^ σ₁ * X ^ (δ / 2)) := by rw [hPdef]; field_simp
      _ = (2 / δ) * X ^ (θ + δ) := by rw [← rpow_add hX0, hexp]
  have hP37 : P * ε ^ (-κ) ≤ X ^ (θ + δ) := by
    rw [hεdef, hPdef, ← rpow_mul hX0.le, ← rpow_add hX0]
    apply rpow_le_rpow_of_exponent_le hX1
    nlinarith
  -- the individual bounds
  have bc : ‖SmoothedChebyshevL χ ν ε X - psiChi χ X‖ ≤ cc * (P * L) := by
    have := hclose X hX ε hεpos hε1 (by rw [hεX]; exact hX2)
    calc _ ≤ cc * ε * X * Real.log X := this
      _ = cc * (P * L) := by rw [← hεX]; ring
  obtain ⟨h1, h9⟩ := h19 ε hεpos hε1 X hX X hX
  rw [mul_comm ε X, hεX] at h1 h9
  have b1 : ‖J₁ χ ν ε X X‖ ≤ c19 * (P * L) := h1.trans (div_le_of_sq c19pos.le hPpos hL0 hPP)
  have b9 : ‖J₉ χ ν ε X X‖ ≤ c19 * (P * L) := h9.trans (div_le_of_sq c19pos.le hPpos hL0 hPP)
  have hεX2 : ε * X ^ 2 = P * X := by rw [← hεX]; ring
  obtain ⟨h2, h8⟩ := h28 ε hεpos hε1 X hX X hX
  rw [hεX2] at h2 h8
  have b2 : ‖J₂ χ ν ε X X σ₁‖ ≤ c28 * (P * L) :=
    h2.trans (div_le_of_sq' c28pos.le hP1 hX0 hL0)
  have b8 : ‖J₈ χ ν ε X X σ₁‖ ≤ c28 * (P * L) :=
    h8.trans (div_le_of_sq' c28pos.le hP1 hX0 hL0)
  have b37 : ‖J₃₇ χ ν ε X X σ₁‖ ≤ c37 * X ^ (θ + δ) := by
    have := h37 ε hεpos hε1 X hX X hX
    calc _ ≤ c37 * X ^ σ₁ * ε ^ (-κ) := this
      _ = c37 * (P * ε ^ (-κ)) := by rw [hPdef]; ring
      _ ≤ c37 * X ^ (θ + δ) := by gcongr
  have hdec := psiChi_le_pieces χ (T := X) hS hεpos hε1 hX hX
  rw [Real.norm_of_nonneg hXα0]
  have hsum : 0 ≤ cc + 2 * c19 + 2 * c28 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hPL hsum
  nlinarith

end InghamL
