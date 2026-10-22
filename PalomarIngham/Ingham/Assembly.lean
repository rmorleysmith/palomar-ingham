module

public import PalomarIngham.Ingham.Basic

set_option autoImplicit false

/-!
# Ingham's theorem: assembly of the contour-shift bounds

Assuming the bounds on the contour pieces `I₂`, `I₃₇`, `I₈` (as `Prop`s from `Ingham.Basic`),
we deduce `ψ(x) = x + O(x^{θ+δ})` following PNT+'s `GenStrengthPNT`, with the choices
`σ₁ = θ + δ/2`, `κ = δ/4`, `ε = X^{σ₁-1}`, `T = X`.
-/

@[expose] public section


open Set Function Filter Complex Real Asymptotics MeasureTheory

namespace Ingham

/-- `ζ'/ζ` is holomorphic on the rectangle (minus `1`) when there are no zeros to the right of
`θ < σ₁`. -/
lemma holo_logDeriv_of_zeroFree {θ σ₁ T : ℝ} (hz : ZeroFreeRight θ) (h : θ < σ₁) :
    HolomorphicOn (deriv riemannZeta / riemannZeta) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}) := by
  intro s hs
  have hs1 : s ≠ 1 := hs.2
  have hre : σ₁ ≤ s.re := (mem_reProdIm.mp hs.1).1.1
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_deriv_riemannZeta hs1).div (differentiableAt_riemannZeta hs1)
    (hz s (by linarith))

/-- The trivial case: exponent at least `1` (Chebyshev's bound). -/
lemma psiError_of_one_le {α : ℝ} (hα : 1 ≤ α) : PsiError α := by
  refine IsBigO.of_bound (Real.log 4 + 5) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h1 := Chebyshev.psi_le_const_mul_self (x := x) (by linarith)
  have h2 := Chebyshev.psi_nonneg x
  have h3 : x ≤ x ^ α := by
    calc x = x ^ (1 : ℝ) := (rpow_one x).symm
    _ ≤ x ^ α := rpow_le_rpow_of_exponent_le hx hα
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), abs_le]
  constructor <;> nlinarith

lemma norm_seven_le (a b c d e f g : ℂ) :
    ‖-a + b - c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (-a + b - c + d + e + f) g
  have h2 := norm_add_le (-a + b - c + d + e) f
  have h3 := norm_add_le (-a + b - c + d) e
  have h4 := norm_add_le (-a + b - c) d
  have h5 := norm_sub_le (-a + b) c
  have h6 := norm_add_le (-a) b
  have h7 := norm_neg a
  linarith

/-- The decomposition of `ψ(X) - X` coming from `SmoothedChebyshevPull1`. -/
lemma psi_sub_le_pieces {ν : ℝ → ℝ} (hν : SmoothingData ν) {θ σ₁ ε X T : ℝ}
    (hz : ZeroFreeRight θ) (hθσ : θ < σ₁) (hσ₁0 : 0 < σ₁) (hσ₁ : σ₁ < 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 3 < X) (hT : 0 < T) :
    |Chebyshev.psi X - X| ≤ ‖SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)‖ +
      ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ +
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
  obtain ⟨hdiff, hnonneg, hsupp, hmass⟩ := hν
  have hS := SmoothedChebyshevPull1 hε hε1 X hX hT hσ₁0 hσ₁
    (holo_logDeriv_of_zeroFree (T := T) hz hθσ) hsupp hnonneg hmass hdiff
  have key : ((Chebyshev.psi X : ℂ) - X) =
      -(SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)) + I₁ ν ε X T - I₂ ν ε T X σ₁ +
        I₃₇ ν ε T X σ₁ + I₈ ν ε T X σ₁ + I₉ ν ε X T +
        (mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X) := by
    rw [hS]; ring
  have habs : |Chebyshev.psi X - X| = ‖((Chebyshev.psi X : ℂ) - X)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, key]
  exact norm_seven_le _ _ _ _ _ _ _


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

theorem psiError_of_bounds {θ : ℝ} (hθ : 1 / 2 ≤ θ) (_hθ1 : θ < 1)
    (hz : Ingham.ZeroFreeRight θ)
    (hA : ∀ σ₁, θ < σ₁ → σ₁ < 1 → Ingham.LogDerivLogBound σ₁)
    (hB : ∀ (ν : ℝ → ℝ) (σ₁ κ : ℝ), Ingham.SmoothingData ν → θ < σ₁ → σ₁ < 1 → 0 < κ → κ < 1 →
      Ingham.LogDerivLogBound σ₁ →
      Ingham.I37BoundProp ν σ₁ κ ∧ Ingham.I2BoundProp ν σ₁ ∧ Ingham.I8BoundProp ν σ₁) :
    ∀ δ > 0, Ingham.PsiError (θ + δ) := by
  intro δ hδ
  by_cases hα : 1 ≤ θ + δ
  · exact psiError_of_one_le hα
  replace hα : θ + δ < 1 := not_le.mp hα
  set σ₁ : ℝ := θ + δ / 2 with hσ₁def
  set κ : ℝ := δ / 4 with hκdef
  have hθσ : θ < σ₁ := by linarith
  have hσ₁1 : σ₁ < 1 := by linarith
  have hσ₁0 : 0 < σ₁ := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ < 1 := by linarith
  obtain ⟨ν, hνsmooth, hνnonneg, hνsupp, hνmass⟩ := SmoothExistence
  have hν : SmoothingData ν := ⟨hνsmooth.of_le (by simp), fun x _ => hνnonneg x, hνsupp,
    by rwa [← integral_Ici_eq_integral_Ioi]⟩
  obtain ⟨⟨c37, c37pos, h37⟩, ⟨c2, c2pos, h2⟩, ⟨c8, c8pos, h8⟩⟩ :=
    hB ν σ₁ κ hν hθσ hσ₁1 hκ0 hκ1 (hA σ₁ hθσ hσ₁1)
  obtain ⟨cc, ccpos, hclose⟩ := SmoothedChebyshevClose hν.1 hν.2.2.1 hν.2.1 hν.2.2.2
  obtain ⟨ε₀, cm, ε₀pos, cmpos, hmain⟩ := MellinOfSmooth1cExplicit hν.1 hν.2.2.1 hν.2.2.2
  obtain ⟨c1, c1pos, h1⟩ := I1Bound hν.2.2.1 hν.1 hν.2.1 hν.2.2.2
  obtain ⟨c9, c9pos, h9⟩ := I9Bound hν.2.2.1 hν.1 hν.2.1 hν.2.2.2
  have ev2 : ∀ᶠ X : ℝ in atTop, 2 < X ^ σ₁ := (tendsto_rpow_atTop hσ₁0).eventually_gt_atTop 2
  have evε : ∀ᶠ X : ℝ in atTop, X ^ (σ₁ - 1) < ε₀ := by
    have := tendsto_rpow_neg_atTop (y := 1 - σ₁) (by linarith)
    rw [neg_sub] at this
    exact this.eventually_lt_const ε₀pos
  refine IsBigO.of_bound ((cc + c1 + c2 + c8 + c9) * (2 / δ) + c37 + cm) ?_
  filter_upwards [eventually_gt_atTop (3 : ℝ), ev2, evε] with X hX hX2 hXε
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
  have hPα : P ≤ X ^ (θ + δ) := rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hP37 : P * ε ^ (-κ) ≤ X ^ (θ + δ) := by
    rw [hεdef, hPdef, ← rpow_mul hX0.le, ← rpow_add hX0]
    apply rpow_le_rpow_of_exponent_le hX1
    nlinarith
  -- the individual bounds
  have bc : ‖SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)‖ ≤ cc * (P * L) := by
    have := hclose X hX ε hεpos hε1 (by rw [hεX]; exact hX2)
    calc _ ≤ cc * ε * X * Real.log X := this
      _ = cc * (P * L) := by rw [← hεX]; ring
  have bm : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ cm * P := by
    have := hmain ε ⟨hεpos, hXε⟩
    have heq : mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X =
        (mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) * (X : ℂ) := by ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0.le]
    calc _ ≤ cm * ε * X := by gcongr
      _ = cm * P := by rw [← hεX]; ring
  have b1 : ‖I₁ ν ε X X‖ ≤ c1 * (P * L) := by
    have := h1 ε hεpos hε1 X hX (T := X) hX
    rw [mul_comm ε X, hεX] at this
    exact this.trans (div_le_of_sq c1pos.le hPpos hL0 hPP)
  have b9 : ‖I₉ ν ε X X‖ ≤ c9 * (P * L) := by
    have := h9 hεpos hε1 X hX (T := X) hX
    rw [mul_comm ε X, hεX] at this
    exact this.trans (div_le_of_sq c9pos.le hPpos hL0 hPP)
  have hεX2 : ε * X ^ 2 = P * X := by rw [← hεX]; ring
  have b2 : ‖I₂ ν ε X X σ₁‖ ≤ c2 * (P * L) := by
    have := h2 ε hεpos hε1 X hX X hX
    rw [hεX2] at this
    exact this.trans (div_le_of_sq' c2pos.le hP1 hX0 hL0)
  have b8 : ‖I₈ ν ε X X σ₁‖ ≤ c8 * (P * L) := by
    have := h8 ε hεpos hε1 X hX X hX
    rw [hεX2] at this
    exact this.trans (div_le_of_sq' c8pos.le hP1 hX0 hL0)
  have b37 : ‖I₃₇ ν ε X X σ₁‖ ≤ c37 * X ^ (θ + δ) := by
    have := h37 ε hεpos hε1 X hX X hX
    calc _ ≤ c37 * X ^ σ₁ * ε ^ (-κ) := this
      _ = c37 * (P * ε ^ (-κ)) := by rw [hPdef]; ring
      _ ≤ c37 * X ^ (θ + δ) := by gcongr
  have hdec := psi_sub_le_pieces hν (T := X) hz hθσ hσ₁0 hσ₁1 hεpos hε1 hX hX0
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hXα0]
  have hsum : 0 ≤ cc + c1 + c2 + c8 + c9 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hPL hsum
  have k2 := mul_le_mul_of_nonneg_left hPα cmpos.le
  nlinarith

end Ingham
