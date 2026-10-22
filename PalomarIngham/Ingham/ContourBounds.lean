module

public import PalomarIngham.Ingham.Basic

set_option autoImplicit false

/-!
# Bounds for the contour pieces `I₂`, `I₈`, `I₃₇`
-/

@[expose] public section


open Set Function Filter Complex Real MeasureTheory

namespace Ingham

/-- For `x ∈ [1/2, 2]` and `-1 ≤ a ≤ 1`, `x ^ a ≤ 2`. -/
lemma rpow_le_two_of_mem_Icc {x a : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) (ha1 : -1 ≤ a)
    (ha2 : a ≤ 1) : x ^ a ≤ 2 := by
  obtain ⟨hx1, hx2⟩ := hx
  have xpos : 0 < x := by linarith
  rcases le_or_gt 1 x with h | h
  · calc x ^ a ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ha2
      _ = x := Real.rpow_one x
      _ ≤ 2 := hx2
  · calc x ^ a ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge xpos h.le ha1
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 2 := by
        rw [inv_le_comm₀ xpos (by norm_num)]; linarith

/-- The Mellin transform of `ν` is bounded on the strip `0 ≤ Re w ≤ 2`. -/
lemma mellin_nu_bounded {ν : ℝ → ℝ} (hν : SmoothingData ν) :
    ∃ B > 0, ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 2 → ‖mellin (fun x ↦ (ν x : ℂ)) w‖ ≤ B := by
  obtain ⟨diff, -, supp, -⟩ := hν
  have cont : Continuous ν := diff.continuous
  have hcs : HasCompactSupport ν :=
    HasCompactSupport.intro isCompact_Icc (fun x hx ↦ by
      by_contra h
      exact hx (supp h))
  have int : Integrable (fun x ↦ |ν x|) (volume.restrict (Ioi 0)) :=
    (cont.integrable_of_hasCompactSupport hcs).abs.restrict
  set J : ℝ := ∫ x in Ioi 0, |ν x| with hJ
  have Jnn : 0 ≤ J := integral_nonneg (fun _ ↦ abs_nonneg _)
  refine ⟨2 * J + 1, by linarith, ?_⟩
  intro w hw1 hw2
  have key : ‖mellin (fun x ↦ (ν x : ℂ)) w‖ ≤ ∫ x in Ioi 0, 2 * |ν x| := by
    unfold mellin
    refine norm_integral_le_of_norm_le (int.const_mul 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs]
    by_cases hνx : ν x = 0
    · simp [hνx]
    · have hxI : x ∈ Icc (1 / 2 : ℝ) 2 := supp hνx
      have : x ^ (w - 1).re ≤ 2 := by
        apply rpow_le_two_of_mem_Icc hxI <;> simp <;> linarith
      nlinarith [abs_nonneg (ν x)]
  calc _ ≤ ∫ x in Ioi 0, 2 * |ν x| := key
    _ = 2 * J := integral_const_mul _ _
    _ ≤ _ := by linarith

/-- `min a b ≤ a ^ (1 - κ) * b ^ κ` for `a, b ≥ 0`, `0 ≤ κ ≤ 1`. -/
lemma le_rpow_mul_rpow_of_le_of_le {m a b κ : ℝ} (hm : 0 ≤ m) (ha : m ≤ a) (hb : m ≤ b)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) : m ≤ a ^ (1 - κ) * b ^ κ := by
  calc m = m ^ (1 - κ) * m ^ κ := by
        rw [← Real.rpow_add' hm (by norm_num), sub_add_cancel, Real.rpow_one]
    _ ≤ a ^ (1 - κ) * b ^ κ := by
        gcongr
        exact Real.rpow_nonneg (hm.trans ha) _

/-- Interpolated Mellin bound: `‖𝓜(Smooth1 ν ε) s‖ ≤ M ε^{-κ} ‖s‖^{-1-κ}`. -/
lemma mellin_smooth1_interp {ν : ℝ → ℝ} (hν : SmoothingData ν) {κ : ℝ} (hκ : 0 < κ)
    (hκ1 : κ < 1) :
    ∃ M > 0, ∀ s : ℂ, 0 < s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ M * ε ^ (-κ) * ‖s‖ ^ (-1 - κ) := by
  obtain ⟨B, Bpos, hB⟩ := mellin_nu_bounded hν
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi hν.1 hν.2.2.1
  refine ⟨B ^ (1 - κ) * C ^ κ, by positivity, ?_⟩
  intro s hs1 hs2 ε εpos εlt
  have sne : s ≠ 0 := fun h ↦ by simp [h] at hs1
  have snorm : 0 < ‖s‖ := norm_pos_iff.mpr sne
  rw [MellinOfSmooth1a hν.1 hν.2.2.1 εpos hs1]
  have hre : (↑ε * s).re = ε * s.re := by simp
  have h1 : ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ ≤ B :=
    hB _ (by rw [hre]; positivity) (by rw [hre]; nlinarith)
  have h2 : ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ ≤ C * (ε * ‖s‖)⁻¹ := by
    have := hC (ε * s.re) (by positivity) (ε * s) (by rw [hre]) (by rw [hre]; nlinarith)
    simpa [abs_of_pos εpos] using this
  have h3 := le_rpow_mul_rpow_of_le_of_le (norm_nonneg _) h1 h2 hκ.le hκ1.le
  rw [norm_mul, norm_inv]
  calc ‖s‖⁻¹ * ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖
      ≤ ‖s‖⁻¹ * (B ^ (1 - κ) * (C * (ε * ‖s‖)⁻¹) ^ κ) := by gcongr
    _ = B ^ (1 - κ) * C ^ κ * ε ^ (-κ) * ‖s‖ ^ (-1 - κ) := by
      rw [Real.mul_rpow Cpos.le (by positivity), Real.inv_rpow (by positivity),
        Real.mul_rpow εpos.le snorm.le, Real.rpow_neg εpos.le,
        show (-1 - κ) = -1 + -κ by ring, Real.rpow_add snorm, Real.rpow_neg snorm.le,
        Real.rpow_neg snorm.le, Real.rpow_one]
      field_simp


/-! ### Horizontal pieces -/

lemma rpow_one_add_inv_log {X : ℝ} (hX : 1 < X) :
    X ^ (1 + (Real.log X)⁻¹) = X * Real.exp 1 := by
  have Xpos : 0 < X := by linarith
  have hl : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [Real.rpow_add Xpos, Real.rpow_one, Real.rpow_def_of_pos Xpos, mul_inv_cancel₀ hl]

lemma norm_cpow_le_of_re_le {X : ℝ} (hX : 1 < X) {s : ℂ} (hs : s.re ≤ 1 + (Real.log X)⁻¹) :
    ‖(X : ℂ) ^ s‖ ≤ X * Real.exp 1 := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith), ← rpow_one_add_inv_log hX]
  exact Real.rpow_le_rpow_of_exponent_le hX.le hs

/-- Norm of the integrand splits as a product. -/
lemma norm_integrand_eq (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) :
    ‖SmoothedChebyshevIntegrand ν ε X s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ *
        ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * ‖(X : ℂ) ^ s‖ := by
  simp only [SmoothedChebyshevIntegrand, norm_mul, neg_div, norm_neg]

/-- Pointwise bound on the horizontal segment at height `-T`. -/
lemma i2_pointwise {ν : ℝ → ℝ} (hν : SmoothingData ν) {σ₁ : ℝ} (hσ₁ : 0 < σ₁)
    (hA : LogDerivLogBound σ₁) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
      ∀ σ ∈ Icc σ₁ (1 + (Real.log X)⁻¹),
        ‖SmoothedChebyshevIntegrand ν ε X (σ - T * I)‖ ≤ C * X * Real.log T / (ε * T ^ 2) := by
  obtain ⟨K, Kpos, hK⟩ := hA
  obtain ⟨C₁, C₁pos, hC₁⟩ := MellinOfSmooth1b hν.1 hν.2.2.1
  refine ⟨K * C₁ * Real.exp 1, by positivity, ?_⟩
  intro ε εpos εlt X hX T hT σ hσ
  have Tpos : 0 < T := by linarith
  have hσ2 : σ ≤ 2 := hσ.2.trans (one_add_inv_log hX.le).le
  have eq1 : (σ : ℂ) - T * I = (σ : ℂ) + ((-T : ℝ) : ℂ) * I := by push_cast; ring
  have hre : ((σ : ℂ) - T * I).re = σ := by simp
  have hnorm : T ≤ ‖(σ : ℂ) - T * I‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) - T * I)
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_sub, abs_neg] at this
    rwa [abs_of_pos Tpos] at this
  have b1 : ‖deriv riemannZeta ((σ : ℂ) - T * I) / riemannZeta ((σ : ℂ) - T * I)‖ ≤
      K * Real.log T := by
    rw [eq1]
    have := hK σ (-T) hσ.1 hσ2 (by rw [abs_neg, abs_of_pos Tpos]; exact hT.le)
    rwa [abs_neg, abs_of_pos Tpos] at this
  have b2 : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) ((σ : ℂ) - T * I)‖ ≤ C₁ * (ε * T ^ 2)⁻¹ := by
    refine (hC₁ σ₁ hσ₁ _ (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ2) ε εpos εlt).trans ?_
    gcongr
  have b3 : ‖(X : ℂ) ^ ((σ : ℂ) - T * I)‖ ≤ X * Real.exp 1 :=
    norm_cpow_le_of_re_le (by linarith) (by rw [hre]; exact hσ.2)
  have logTpos : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  rw [norm_integrand_eq]
  calc _ ≤ (K * Real.log T) * (C₁ * (ε * T ^ 2)⁻¹) * (X * Real.exp 1) := by
        gcongr
    _ = _ := by field_simp

theorem i2Bound {ν : ℝ → ℝ} {θ σ₁ : ℝ} (hν : SmoothingData ν)
    (hθσ : θ < σ₁) (_hσ₁ : σ₁ < 1) (hθ : 0 < θ) (_hz : ZeroFreeRight θ)
    (hA : LogDerivLogBound σ₁) : I2BoundProp ν σ₁ := by
  obtain ⟨C, Cpos, hC⟩ := i2_pointwise hν (hθ.trans hθσ) hA
  refine ⟨‖1 / (2 * π * I)‖ * (2 * C), by
    have : ‖1 / (2 * π * I)‖ ≠ 0 := by simp [pi_ne_zero]
    positivity, ?_⟩
  intro ε εpos εlt X hX T hT
  have Tpos : 0 < T := by linarith
  have hlogX : 0 < (Real.log X)⁻¹ := inv_pos.mpr (Real.log_pos (by linarith))
  have hle : σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
  have hint : ‖∫ σ in σ₁..(1 + (Real.log X)⁻¹),
      SmoothedChebyshevIntegrand ν ε X (σ - T * I)‖ ≤
      C * X * Real.log T / (ε * T ^ 2) * 2 := by
    calc _ ≤ C * X * Real.log T / (ε * T ^ 2) * |1 + (Real.log X)⁻¹ - σ₁| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
          intro σ hσ
          rw [uIoc_of_le hle] at hσ
          exact hC ε εpos εlt X hX T hT σ ⟨hσ.1.le, hσ.2⟩
      _ ≤ C * X * Real.log T / (ε * T ^ 2) * 2 := by
          have : 0 ≤ C * X * Real.log T / (ε * T ^ 2) := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ T by linarith)
            have : 0 < X := by linarith
            positivity
          gcongr
          rw [abs_of_nonneg (by linarith)]
          linarith [one_add_inv_log hX.le, hθ.trans hθσ]
  unfold I₂
  rw [norm_mul]
  calc _ ≤ ‖1 / (2 * π * I)‖ * (C * X * Real.log T / (ε * T ^ 2) * 2) := by gcongr
    _ = _ := by ring

theorem i8Bound {ν : ℝ → ℝ} {θ σ₁ : ℝ} (hν : SmoothingData ν)
    (hθσ : θ < σ₁) (hσ₁ : σ₁ < 1) (hθ : 0 < θ) (hz : ZeroFreeRight θ)
    (hA : LogDerivLogBound σ₁) : I8BoundProp ν σ₁ := by
  obtain ⟨C, Cpos, hC⟩ := i2Bound hν hθσ hσ₁ hθ hz hA
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos εlt X hX T hT
  rw [I8I2 hX, norm_neg, Complex.norm_conj]
  exact hC ε εpos εlt X hX T hT


/-! ### The vertical piece -/

lemma continuous_logDeriv_line {θ σ₁ : ℝ} (hθσ : θ < σ₁) (hσ₁ : σ₁ < 1)
    (hz : ZeroFreeRight θ) :
    Continuous (fun t : ℝ ↦ deriv riemannZeta ((σ₁ : ℂ) + t * I) /
      riemannZeta ((σ₁ : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hl : Continuous (fun t : ℝ ↦ (σ₁ : ℂ) + t * I) := by fun_prop
  have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
  have hne : (σ₁ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre, one_re] at this
    linarith
  have hz' : riemannZeta ((σ₁ : ℂ) + t * I) ≠ 0 := hz _ (by rw [hre]; exact hθσ)
  refine ContinuousAt.div (f := fun t : ℝ ↦ deriv riemannZeta ((σ₁ : ℂ) + t * I))
    (g := fun t : ℝ ↦ riemannZeta ((σ₁ : ℂ) + t * I)) ?_ ?_ hz'
  · exact ContinuousAt.comp (f := fun t : ℝ ↦ (σ₁ : ℂ) + t * I)
      (differentiableAt_deriv_riemannZeta hne).continuousAt hl.continuousAt
  · exact ContinuousAt.comp (f := fun t : ℝ ↦ (σ₁ : ℂ) + t * I)
      (differentiableAt_riemannZeta hne).continuousAt hl.continuousAt

lemma logDeriv_line_bound {θ σ₁ κ : ℝ} (hθσ : θ < σ₁) (hσ₁ : σ₁ < 1)
    (hz : ZeroFreeRight θ) (hA : LogDerivLogBound σ₁) (hκ : 0 < κ) :
    ∃ D > 0, ∀ t : ℝ, ‖deriv riemannZeta ((σ₁ : ℂ) + t * I) /
      riemannZeta ((σ₁ : ℂ) + t * I)‖ ≤ D * (1 + |t|) ^ (κ / 2) := by
  obtain ⟨K, Kpos, hK⟩ := hA
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-3 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    (continuous_logDeriv_line hθσ hσ₁ hz).continuousOn
  refine ⟨max B 1 + K * (2 / κ), by positivity, ?_⟩
  intro t
  have h1 : 1 ≤ (1 + |t|) ^ (κ / 2) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have hpow : 0 ≤ (1 + |t|) ^ (κ / 2) := by positivity
  rcases le_or_gt |t| 3 with ht | ht
  · have := hB t (by rw [mem_Icc]; constructor <;> linarith [abs_le.mp ht])
    calc _ ≤ B := this
      _ ≤ max B 1 := le_max_left _ _
      _ ≤ max B 1 * (1 + |t|) ^ (κ / 2) := le_mul_of_one_le_right (by positivity) h1
      _ ≤ _ := by
        rw [add_mul]
        have : 0 ≤ K * (2 / κ) * (1 + |t|) ^ (κ / 2) := by positivity
        linarith
  · have hlog : Real.log |t| ≤ (2 / κ) * (1 + |t|) ^ (κ / 2) := by
      have := Real.log_le_rpow_div (abs_nonneg t) (show 0 < κ / 2 by positivity)
      calc Real.log |t| ≤ |t| ^ (κ / 2) / (κ / 2) := this
        _ = (2 / κ) * |t| ^ (κ / 2) := by field_simp
        _ ≤ (2 / κ) * (1 + |t|) ^ (κ / 2) := by
          gcongr
          linarith
    calc _ ≤ K * Real.log |t| := hK σ₁ t le_rfl (by linarith) ht.le
      _ ≤ K * ((2 / κ) * (1 + |t|) ^ (κ / 2)) := by gcongr
      _ ≤ _ := by
        rw [add_mul]
        have : 0 ≤ max B 1 * (1 + |t|) ^ (κ / 2) := by positivity
        linarith

lemma norm_line_ge {σ₁ : ℝ} (hσ₀ : 0 < σ₁) (hσ₁ : σ₁ < 1) (t : ℝ) :
    σ₁ / 2 * (1 + |t|) ≤ ‖(σ₁ : ℂ) + t * I‖ := by
  have h1 := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I)
  have h2 := Complex.abs_im_le_norm ((σ₁ : ℂ) + t * I)
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at h1 h2
  rw [abs_of_pos hσ₀] at h1
  nlinarith [abs_nonneg t]


/-- Pointwise bound on the vertical line `Re s = σ₁`. -/
lemma i37_pointwise {ν : ℝ → ℝ} {θ σ₁ κ : ℝ} (hν : SmoothingData ν)
    (hθσ : θ < σ₁) (hσ₁ : σ₁ < 1) (hθ : 0 < θ) (hz : ZeroFreeRight θ)
    (hA : LogDerivLogBound σ₁) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ Q > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 0 < X → ∀ t : ℝ,
      ‖SmoothedChebyshevIntegrand ν ε X ((σ₁ : ℂ) + t * I)‖ ≤
        Q * X ^ σ₁ * ε ^ (-κ) * (1 + ‖t‖) ^ (-(1 + κ / 2)) := by
  have hσ₀ : 0 < σ₁ := hθ.trans hθσ
  obtain ⟨D, Dpos, hD⟩ := logDeriv_line_bound hθσ hσ₁ hz hA hκ
  obtain ⟨M, Mpos, hM⟩ := mellin_smooth1_interp hν hκ hκ1
  refine ⟨D * M * (σ₁ / 2) ^ (-1 - κ), by positivity, ?_⟩
  intro ε εpos εlt X Xpos t
  have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
  have u0 : 0 < 1 + |t| := by linarith [abs_nonneg t]
  have b1 := hD t
  have b2 := hM ((σ₁ : ℂ) + t * I) (by rw [hre]; exact hσ₀) (by rw [hre]; linarith) ε εpos εlt
  have b2' : ‖(σ₁ : ℂ) + t * I‖ ^ (-1 - κ) ≤ (σ₁ / 2) ^ (-1 - κ) * (1 + |t|) ^ (-1 - κ) := by
    rw [← Real.mul_rpow (by positivity) u0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_line_ge hσ₀ hσ₁ t) (by linarith)
  have b3 : ‖(X : ℂ) ^ ((σ₁ : ℂ) + t * I)‖ = X ^ σ₁ := by
    rw [norm_cpow_eq_rpow_re_of_pos Xpos, hre]
  have hexp : (1 + |t|) ^ (κ / 2) * (1 + |t|) ^ (-1 - κ) = (1 + |t|) ^ (-(1 + κ / 2)) := by
    rw [← Real.rpow_add u0]; congr 1; ring
  rw [norm_integrand_eq, b3, Real.norm_eq_abs]
  calc _ ≤ (D * (1 + |t|) ^ (κ / 2)) *
        (M * ε ^ (-κ) * ((σ₁ / 2) ^ (-1 - κ) * (1 + |t|) ^ (-1 - κ))) * X ^ σ₁ := by
        gcongr
        exact b2.trans (by gcongr)
    _ = D * M * (σ₁ / 2) ^ (-1 - κ) * X ^ σ₁ * ε ^ (-κ) *
        ((1 + |t|) ^ (κ / 2) * (1 + |t|) ^ (-1 - κ)) := by ring
    _ = _ := by rw [hexp]

theorem i37Bound {ν : ℝ → ℝ} {θ σ₁ κ : ℝ} (hν : SmoothingData ν)
    (hθσ : θ < σ₁) (hσ₁ : σ₁ < 1) (hθ : 0 < θ) (hz : ZeroFreeRight θ)
    (hA : LogDerivLogBound σ₁) (hκ : 0 < κ) (hκ1 : κ < 1) : I37BoundProp ν σ₁ κ := by
  obtain ⟨Q, Qpos, hQ⟩ := i37_pointwise hν hθσ hσ₁ hθ hz hA hκ hκ1
  set g : ℝ → ℝ := fun t ↦ (1 + ‖t‖) ^ (-(1 + κ / 2)) with hg
  have gint : Integrable g := integrable_one_add_norm (by simp; linarith)
  have gnn : ∀ t, 0 ≤ g t := fun t ↦ by positivity
  set G : ℝ := ∫ t, g t with hG
  have Gnn : 0 ≤ G := integral_nonneg gnn
  refine ⟨‖1 / (2 * π * I)‖ * (Q * (G + 1)), by
    have : ‖1 / (2 * π * I)‖ ≠ 0 := by simp [pi_ne_zero]
    positivity, ?_⟩
  intro ε εpos εlt X hX T hT
  have Xpos : 0 < X := by linarith
  have hTle : -T ≤ T := by linarith
  have hint : ‖∫ t in (-T)..T, SmoothedChebyshevIntegrand ν ε X ((σ₁ : ℂ) + t * I)‖ ≤
      Q * X ^ σ₁ * ε ^ (-κ) * G := by
    rw [intervalIntegral.integral_of_le hTle]
    have hc : 0 ≤ Q * X ^ σ₁ * ε ^ (-κ) := by positivity
    calc _ ≤ ∫ t in Ioc (-T) T, Q * X ^ σ₁ * ε ^ (-κ) * g t := by
          refine norm_integral_le_of_norm_le ((gint.const_mul _).restrict) ?_
          exact Eventually.of_forall (fun t ↦ hQ ε εpos εlt X Xpos t)
      _ ≤ ∫ t, Q * X ^ σ₁ * ε ^ (-κ) * g t :=
          setIntegral_le_integral (gint.const_mul _)
            (Eventually.of_forall (fun t ↦ mul_nonneg hc (gnn t)))
      _ = _ := integral_const_mul _ _
  unfold I₃₇
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hXσ : 0 ≤ X ^ σ₁ := by positivity
  have hεκ : 0 ≤ ε ^ (-κ) := by positivity
  calc _ ≤ ‖1 / (2 * π * I)‖ * (Q * X ^ σ₁ * ε ^ (-κ) * G) := by gcongr
    _ ≤ ‖1 / (2 * π * I)‖ * (Q * X ^ σ₁ * ε ^ (-κ) * (G + 1)) := by gcongr; linarith
    _ = _ := by ring

end Ingham
