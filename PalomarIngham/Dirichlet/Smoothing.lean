module

public import PalomarIngham.Dirichlet.Basic

/-!
# Smoothing, contour shift and far vertical pieces for `-L'/L(s, χ)`

* `neg_logDeriv_eq_tsum`, `norm_neg_logDeriv_le`: `-L'/L(s, χ) = ∑ χ(n) Λ(n) n^{-s}` and
  `‖L'/L(σ + it, χ)‖ ≤ ‖ζ'/ζ(σ)‖` for `σ > 1`.
* `smoothedChebyshevL_eq_tsum`: `ψ_ε(X, χ) = ∑ χ(n) Λ(n) 1̃_ε(n/X)` (Mellin inversion).
* `closeProp`: `‖ψ_ε(X, χ) - ψ(X, χ)‖ ≤ C ε X log X`.
* `shiftProp`: for `χ ≠ 1` and `L` zero-free on `Re s > θ`, moving the line to `σ₁ ∈ (θ, 1)`
  (Cauchy on the rectangle; no residue since `L(s, χ)` is entire).
* `j19Bound`: `‖J₁‖, ‖J₉‖ ≤ C X log X / (ε T)`.
-/

@[expose] public section

set_option autoImplicit false

open Set Function Filter Complex Real Asymptotics MeasureTheory
open ArithmeticFunction (vonMangoldt)
open scoped ComplexOrder

namespace InghamL

variable {q : ℕ} [NeZero q]

/-- `-L'/L(s, χ) = L(χ Λ, s)` for `Re s > 1`. -/
theorem neg_logDeriv_eq_LSeries (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      LSeries ((fun n : ℕ ↦ χ n) * fun n ↦ (vonMangoldt n : ℂ)) s := by
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]

/-- `-L'/L(s, χ) = ∑ χ(n) Λ(n) n^{-s}` for `Re s > 1`. -/
theorem neg_logDeriv_eq_tsum (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      ∑' n : ℕ, χ n * (vonMangoldt n : ℂ) / (n : ℂ) ^ s := by
  rw [neg_logDeriv_eq_LSeries χ hs, LSeries]
  congr 1; ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]

/-- `‖L'/L(σ + it, χ)‖ ≤ ‖ζ'/ζ(σ)‖` for `σ > 1`. -/
theorem norm_neg_logDeriv_le (χ : DirichletCharacter ℂ q) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (t : ℝ) :
    ‖-deriv (DirichletCharacter.LFunction χ) (σ₀ + t * I) /
        DirichletCharacter.LFunction χ (σ₀ + t * I)‖ ≤
      ‖-deriv riemannZeta σ₀ / riemannZeta σ₀‖ := by
  have hs : 1 < ((σ₀ : ℂ) + t * I).re := by simpa using hσ₀
  have hs₀ : 1 < (σ₀ : ℂ).re := by simpa using hσ₀
  rw [neg_logDeriv_eq_LSeries χ hs,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs₀]
  unfold LSeries
  have hsumΛ : Summable (fun n ↦ LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) σ₀ n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs₀
  have hsum : Summable (fun n ↦ ‖LSeries.term ((fun n : ℕ ↦ χ n) *
      fun n ↦ (vonMangoldt n : ℂ)) (σ₀ + t * I) n‖) := by
    rw [summable_norm_iff]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hnn : ∀ n, 0 ≤ LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) σ₀ n := fun n ↦
    LSeries.term_nonneg (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) _
  apply (norm_tsum_le_tsum_norm hsum).trans
  rw [← re_eq_norm.mpr (tsum_nonneg hnn), re_tsum hsumΛ]
  apply Summable.tsum_mono hsum (Complex.reCLM.summable hsumΛ)
  intro n
  calc ‖LSeries.term ((fun n : ℕ ↦ χ n) * fun n ↦ (vonMangoldt n : ℂ)) (σ₀ + t * I) n‖
      ≤ ‖LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) (σ₀ + t * I) n‖ := by
        apply LSeries.norm_term_le
        simp only [Pi.mul_apply, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    _ ≤ ‖LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) σ₀ n‖ :=
        LSeries.norm_term_le_of_re_le_re _ (by simp) n
    _ = (LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) σ₀ n).re := (re_eq_norm.mpr (hnn n)).symm


/-! ### Far vertical pieces -/

lemma sigma0_facts {X : ℝ} (hX : 3 < X) :
    1 < Real.log X ∧ 1 < 1 + (Real.log X)⁻¹ ∧ 1 + (Real.log X)⁻¹ < 2 ∧
      ((1 + (Real.log X)⁻¹) - 1)⁻¹ = Real.log X ∧
      X ^ (1 + (Real.log X)⁻¹) = Real.exp 1 * X := by
  have hlog : 1 < Real.log X := logt_gt_one hX.le
  have hX0 : 0 < X := by linarith
  refine ⟨hlog, ?_, ?_, by simp, ?_⟩
  · have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  · have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlog
    linarith
  · rw [rpow_one_add' hX0.le (by positivity), rpow_inv_log hX0 (by linarith), mul_comm]

/-- Pointwise bound for the integrand on the line `Re s = 1 + 1/log X`. -/
theorem integrandL_vertical_bound (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (hν : Ingham.SmoothingData ν) :
    ∃ K > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ t : ℝ,
      ‖IntegrandL χ ν ε X ((1 + (Real.log X)⁻¹ : ℝ) + t * I)‖ ≤
        K * Real.log X * X / ε * (‖((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I‖ ^ 2)⁻¹ := by
  obtain ⟨hdiff, hnn, hsupp, hmass⟩ := hν
  obtain ⟨M, hMpos, hM⟩ := MellinOfSmooth1b hdiff hsupp
  obtain ⟨C₀, hC₀, hz⟩ := triv_bound_zeta
  refine ⟨(1 + C₀) * M * Real.exp 1, by positivity, ?_⟩
  intro ε hε hε1 X hX t
  obtain ⟨hlog, hσ1, hσ2, hinv, hXσ⟩ := sigma0_facts hX
  set σ₀ : ℝ := 1 + (Real.log X)⁻¹ with hσ₀
  set s : ℂ := (σ₀ : ℂ) + t * I with hs
  have hX0 : 0 < X := by linarith
  have hsre : s.re = σ₀ := by simp [hs]
  -- zeta bound
  have hζ : ‖-deriv riemannZeta σ₀ / riemannZeta σ₀‖ ≤ (1 + C₀) * Real.log X := by
    have := hz σ₀ 0 hσ1
    simp only [ofReal_zero, zero_mul, add_zero] at this
    rw [hinv] at this
    nlinarith
  have hL := (norm_neg_logDeriv_le χ hσ1 t).trans hζ
  have hmel : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹ :=
    hM 1 one_pos s (by rw [hsre]; linarith) (by rw [hsre]; linarith) ε hε hε1
  have hXs : ‖(X : ℂ) ^ s‖ = Real.exp 1 * X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0, hsre, hXσ]
  have hs0 : 0 < ‖s‖ := by
    rw [norm_pos_iff]; intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  unfold IntegrandL
  rw [norm_mul, norm_mul, hXs]
  calc ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ *
        ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * (Real.exp 1 * X)
      ≤ ((1 + C₀) * Real.log X) * (M * (ε * ‖s‖ ^ 2)⁻¹) * (Real.exp 1 * X) := by
        gcongr
    _ = (1 + C₀) * M * Real.exp 1 * Real.log X * X / ε * (‖s‖ ^ 2)⁻¹ := by
        field_simp

lemma integral_Ici_inv_normSq_le (x T : ℝ) (hT : 3 < T) :
    ∫ t : ℝ in Ici T, (‖(x : ℂ) + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  have h := integral_evaluation x T hT
  rw [← integral_comp_neg_Ioi] at h
  rw [integral_Ici_eq_integral_Ioi]
  convert h using 3 with t
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I,
    Complex.normSq_add_mul_I]
  ring

/-- Generic bound for `J₁`/`J₉`-type integrals over a half-line. -/
lemma norm_halfline_integral_le {S : Set ℝ} {f : ℝ → ℂ} {x B T : ℝ} (hx : x ≠ 0) (hB : 0 ≤ B)
    (hf : ∀ t, ‖f t‖ ≤ B * (‖(x : ℂ) + t * I‖ ^ 2)⁻¹)
    (hint : ∫ t : ℝ in S, (‖(x : ℂ) + t * I‖ ^ 2)⁻¹ ≤ T⁻¹) :
    ‖(1 / (2 * π * I)) * (I * ∫ t in S, f t)‖ ≤ B * T⁻¹ := by
  have h1 : ‖(1 / (2 * π * I)) * (I * ∫ t in S, f t)‖ ≤ ‖∫ t in S, f t‖ := by
    rw [norm_mul, norm_mul, norm_I, one_mul]
    have : ‖(1 / (2 * π * I) : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    exact mul_le_of_le_one_left (norm_nonneg _) this
  refine h1.trans ?_
  have hg : Integrable (fun t : ℝ ↦ B * (‖(x : ℂ) + t * I‖ ^ 2)⁻¹) (volume.restrict S) :=
    ((poisson_kernel_integrable x hx).const_mul B).restrict
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ hf)).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hint hB

theorem j19Bound (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (hν : Ingham.SmoothingData ν) : J19BoundProp χ ν := by
  obtain ⟨K, hK, hbound⟩ := integrandL_vertical_bound χ hν
  refine ⟨K, hK, ?_⟩
  intro ε hε hε1 X hX T hT
  obtain ⟨hlog, hσ1, -, -, -⟩ := sigma0_facts hX
  have hX0 : 0 < X := by linarith
  have hx : (1 + (Real.log X)⁻¹ : ℝ) ≠ 0 := by linarith
  have hB : 0 ≤ K * Real.log X * X / ε := by positivity
  have hf : ∀ t : ℝ, ‖IntegrandL χ ν ε X ((1 + (Real.log X)⁻¹ : ℂ) + t * I)‖ ≤
      K * Real.log X * X / ε * (‖((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I‖ ^ 2)⁻¹ := by
    intro t; have := hbound ε hε hε1 X hX t; push_cast at this ⊢; exact this
  have heq : K * Real.log X * X / ε * T⁻¹ = K * X * Real.log X / (ε * T) := by
    field_simp
  constructor
  · rw [← heq]
    exact norm_halfline_integral_le hx hB hf (integral_evaluation _ T hT)
  · rw [← heq]
    exact norm_halfline_integral_le hx hB hf (integral_Ici_inv_normSq_le _ T hT)


/-! ### Dirichlet series expansion of the smoothed twisted Chebyshev function -/

lemma ofReal_div_cpow_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-s) = (b : ℂ) ^ s / (a : ℂ) ^ s := by
  have hab : (0 : ℝ) < a / b := div_pos ha hb
  rw [cpow_def_of_ne_zero (by exact_mod_cast hab.ne'), cpow_def_of_ne_zero (by exact_mod_cast hb.ne'),
    cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), ← ofReal_log hab.le, ← ofReal_log hb.le,
    ← ofReal_log ha.le, Real.log_div ha.ne' hb.ne', ← Complex.exp_sub]
  congr 1; push_cast; ring

theorem smoothedChebyshevL_eq_tsum (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (hν : Ingham.SmoothingData ν) {X : ℝ} (hX : 3 < X) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    SmoothedChebyshevL χ ν ε X =
      ∑' n : ℕ, χ n * (vonMangoldt n : ℂ) * (Smooth1 ν ε (n / X) : ℂ) := by
  obtain ⟨hdiff, hnn, hsupp, hmass⟩ := hν
  obtain ⟨hlog, hσ1, hσ2, -, -⟩ := sigma0_facts hX
  set σ : ℝ := 1 + (Real.log X)⁻¹ with hσ
  have hX0 : 0 < X := by linarith
  set Mf : ℂ → ℂ := mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) with hMf
  let F : ℕ → ℝ → ℂ := fun n t ↦
    χ n * (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I) * Mf (σ + t * I) *
      (X : ℂ) ^ ((σ : ℂ) + t * I)
  have hmel : Integrable (fun t : ℝ ↦ Mf (σ + t * I)) :=
    SmoothedChebyshevDirichlet_aux_integrable hdiff hnn hsupp hmass hε hε1 hσ1 hσ2.le
  have hsre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t ↦ by simp
  have h1 : ∀ t : ℝ, IntegrandL χ ν ε X (σ + t * I) = ∑' n, F n t := by
    intro t
    rw [IntegrandL, neg_logDeriv_eq_tsum χ (by rw [hsre]; exact hσ1), ← tsum_mul_right,
      ← tsum_mul_right]
  have hFnorm : ∀ n t, ‖F n t‖ =
      ‖LSeries.term ((fun n : ℕ ↦ χ n) * fun n ↦ (vonMangoldt n : ℂ)) σ n‖ * X ^ σ *
        ‖Mf (σ + t * I)‖ := by
    intro n t
    have hXn : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = X ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0, hsre]
    have ht : ‖LSeries.term ((fun n : ℕ ↦ χ n) * fun n ↦ (vonMangoldt n : ℂ)) σ n‖ =
        ‖LSeries.term ((fun n : ℕ ↦ χ n) * fun n ↦ (vonMangoldt n : ℂ)) ((σ : ℂ) + t * I) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
    rw [ht]
    simp only [F, norm_mul, hXn]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]; simp only [Pi.mul_apply, norm_div, norm_mul]; ring
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have : F n = fun t : ℝ ↦ (χ n * (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I) *
        (X : ℂ) ^ ((σ : ℂ) + t * I)) * Mf (σ + t * I) := by
      ext t; simp only [F]; ring
    rw [this]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    refine hmel.bdd_mul (c := ‖χ n * (vonMangoldt n : ℂ)‖ / (n : ℝ) ^ σ * X ^ σ) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
      have c1 : Continuous fun t : ℝ ↦ (n : ℂ) ^ ((σ : ℂ) + t * I) :=
        Continuous.const_cpow (by fun_prop) (Or.inl hn')
      have c2 : Continuous fun t : ℝ ↦ (X : ℂ) ^ ((σ : ℂ) + t * I) :=
        Continuous.const_cpow (by fun_prop) (Or.inl hX')
      exact (continuous_const.div c1 fun t ↦ by rw [Ne, cpow_eq_zero_iff]; tauto).mul c2
    · refine ae_of_all _ fun t ↦ ?_
      rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hX0, hsre,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hsre]
  have hFsum : Summable (fun n ↦ ∫ t, ‖F n t‖) := by
    simp_rw [hFnorm, integral_const_mul]
    refine (Summable.mul_right _ ?_).mul_right _
    rw [summable_norm_iff]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simpa using hσ1)
  have h3 : ∀ n : ℕ, (1 / (2 * π * I)) * (I * ∫ t, F n t) =
      χ n * (vonMangoldt n : ℂ) * (Smooth1 ν ε (n / X) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hx : 0 < (n : ℝ) / X := div_pos hnpos hX0
    have key := mellinInv_mellin_eq σ (fun x ↦ (Smooth1 ν ε x : ℂ)) hx
      (Smooth1MellinConvergent hdiff hsupp ⟨hε, hε1⟩ hnn hmass (by simp; linarith)) hmel
      ((Smooth1ContinuousAt hdiff hnn hsupp hε hx).ofReal)
    have hF : ∀ t : ℝ, F n t = χ n * (vonMangoldt n : ℂ) *
        ((((n : ℝ) / X : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) • Mf (σ + t * I)) := by
      intro t
      rw [ofReal_div_cpow_neg hnpos hX0, smul_eq_mul]
      simp only [F, ofReal_natCast]
      ring
    simp_rw [hF, integral_const_mul]
    rw [← key, mellinInv, Complex.real_smul]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have alg : ∀ c J : ℂ, 1 / (2 * π * I) * (I * (c * J)) = c * (((1 / (2 * π) : ℝ) : ℂ) * J) := by
      intro c J; push_cast; field_simp
    exact alg _ _
  calc SmoothedChebyshevL χ ν ε X = (1 / (2 * π * I)) * (I * ∫ t : ℝ, ∑' n, F n t) := by
        simp only [SmoothedChebyshevL, VerticalIntegral', VerticalIntegral, smul_eq_mul]
        congr 2
        exact integral_congr_ae (ae_of_all _ h1)
    _ = (1 / (2 * π * I)) * (I * ∑' n, ∫ t, F n t) := by
        rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    _ = ∑' n, (1 / (2 * π * I)) * (I * ∫ t, F n t) := by
        rw [← tsum_mul_left, ← tsum_mul_left]
    _ = _ := tsum_congr h3


/-! ### Smoothing error -/

theorem closeProp (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ}
    (hν : Ingham.SmoothingData ν) : CloseProp χ ν := by
  obtain ⟨hdiff, hnn, hsupp, hmass⟩ := hν
  obtain ⟨c₁, hc₁pos, hc₁eq, hc₁⟩ := Smooth1Properties_below hsupp hmass
  obtain ⟨c₂, hc₂pos, hc₂eq, hc₂⟩ := Smooth1Properties_above hsupp
  have hl2 := Real.log_two_lt_d9
  have hc₁1 : c₁ < 1 := by rw [hc₁eq]; linarith
  have hc₂2 : c₂ < 2 := by rw [hc₂eq]; linarith
  refine ⟨2 * (c₁ + c₂ + 1), by positivity, ?_⟩
  intro X hX ε hε hε1 hXε
  have hX0 : 0 < X := by linarith
  rw [smoothedChebyshevL_eq_tsum χ ⟨hdiff, hnn, hsupp, hmass⟩ hX hε hε1]
  set a : ℝ := X * (1 - c₁ * ε) with ha
  set b : ℝ := X * (1 + c₂ * ε) with hb
  have hc₁ε : c₁ * ε < 1 := by nlinarith
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have haX : a ≤ X := by rw [ha]; nlinarith
  have hXb : X ≤ b := by rw [hb]; nlinarith
  have hb3 : b ≤ 3 * X := by rw [hb]; nlinarith
  set m : ℕ := ⌊a⌋₊ with hm
  set N : ℕ := ⌊b⌋₊ + 1 with hN
  have hmN : m + 1 ≤ N := by
    rw [hm, hN]; exact Nat.succ_le_succ (Nat.floor_le_floor (by linarith))
  have hXN : ⌊X⌋₊ < N := by rw [hN]; exact Nat.lt_succ_of_le (Nat.floor_le_floor hXb)
  let f : ℕ → ℂ := fun n ↦ χ n * (vonMangoldt n : ℂ) * (Smooth1 ν ε (n / X) : ℂ)
  let g : ℕ → ℂ := fun n ↦ χ n * (vonMangoldt n : ℂ)
  have hf0 : ∀ n ∉ Finset.range N, f n = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt, hN] at hn
    have hbn : b < n := by
      have := Nat.lt_floor_add_one b
      exact this.trans_le (by exact_mod_cast hn)
    have : Smooth1 ν ε (n / X) = 0 := by
      apply hc₂ ε _ ⟨hε, hε1⟩
      rw [le_div_iff₀ hX0]; rw [hb] at hbn; linarith
    simp [f, this]
  have hpsi : psiChi χ X = ∑ n ∈ Finset.range N,
      (if n ∈ Finset.Ioc 0 ⌊X⌋₊ then g n else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr]
    · rfl
    · intro n hn
      simp only [Finset.mem_Ioc] at hn
      simp only [Finset.mem_range]; omega
  rw [tsum_eq_sum hf0, hpsi, ← Finset.sum_sub_distrib,
    ← Finset.sum_range_add_sum_Ico _ hmN]
  -- the terms with `n ≤ m` vanish
  have hlow : ∑ n ∈ Finset.range (m + 1),
      (f n - if n ∈ Finset.Ioc 0 ⌊X⌋₊ then g n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp [f]
    have hnm : (n : ℝ) ≤ a := by
      have : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le ha0)
    have hS : Smooth1 ν ε (n / X) = 1 := by
      apply hc₁ ε _ hε (by positivity)
      rw [div_le_iff₀ hX0]; rw [ha] at hnm; linarith
    have hmem : n ∈ Finset.Ioc 0 ⌊X⌋₊ := by
      simp only [Finset.mem_Ioc]
      exact ⟨hnpos, Nat.le_floor (hnm.trans haX)⟩
    simp [f, g, hS, hmem]
  rw [hlow, zero_add]
  -- the remaining terms
  have hlogpos : 0 ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have hterm : ∀ n ∈ Finset.Ico (m + 1) N,
      ‖f n - if n ∈ Finset.Ioc 0 ⌊X⌋₊ then g n else 0‖ ≤ Real.log (3 * X) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp [f]; exact hlogpos
    have hnX : (0 : ℝ) < n / X := by positivity
    have hS0 := Smooth1Nonneg hnn hnX hε
    have hS1 := Smooth1LeOne hnn hmass hε hnX
    have hnN : (n : ℝ) ≤ 3 * X := by
      have : n ≤ ⌊b⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hn).2
      exact (Nat.cast_le.mpr this).trans ((Nat.floor_le (by linarith)).trans hb3)
    have hΛ : vonMangoldt n ≤ Real.log (3 * X) :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hnpos) hnN)
    have hdiff1 : ∀ e : ℝ, (e = 0 ∨ e = 1) →
        ‖χ n * (vonMangoldt n : ℂ) * ((Smooth1 ν ε (n / X) : ℂ) - e)‖ ≤ Real.log (3 * X) := by
      intro e he
      rw [norm_mul, norm_mul, ← ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.norm_eq_abs]
      have h1 : |Smooth1 ν ε (n / X) - e| ≤ 1 := by
        rw [abs_le]; rcases he with rfl | rfl <;> constructor <;> linarith
      calc ‖χ n‖ * vonMangoldt n * |Smooth1 ν ε (n / X) - e|
          ≤ 1 * Real.log (3 * X) * 1 := by
            have := DirichletCharacter.norm_le_one χ (n : ZMod q)
            have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
            gcongr
        _ = _ := by ring
    split_ifs
    · convert hdiff1 1 (Or.inr rfl) using 2; simp only [f, g]; push_cast; ring
    · convert hdiff1 0 (Or.inl rfl) using 2; simp only [f]; push_cast; ring
  refine (norm_sum_le_of_le _ hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((N - (m + 1) : ℕ) : ℝ) ≤ X * ε * (c₁ + c₂) + 1 := by
    rw [Nat.cast_sub hmN]
    have h1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by linarith)
    have h2 := Nat.lt_floor_add_one a
    simp only [hN, hm]; push_cast
    rw [ha] at h2; rw [hb] at h1
    nlinarith
  have hlog3 : Real.log (3 * X) ≤ 2 * Real.log X := by
    rw [← Real.log_rpow hX0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  calc ((N - (m + 1) : ℕ) : ℝ) * Real.log (3 * X)
      ≤ (X * ε * (c₁ + c₂) + 1) * (2 * Real.log X) := by
        gcongr
    _ ≤ (X * ε * (c₁ + c₂) + X * ε) * (2 * Real.log X) := by
        gcongr; linarith
    _ = 2 * (c₁ + c₂ + 1) * ε * X * Real.log X := by ring


/-! ### Contour shift -/

lemma differentiable_deriv_LFunction {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (deriv (DirichletCharacter.LFunction χ)) := fun z ↦
  ((DirichletCharacter.differentiable_LFunction hχ).analyticAt z).deriv.differentiableAt

/-- Integrability of the integrand on the line `Re s = 1 + 1/log X`. -/
theorem integrandL_integrable (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ν : ℝ → ℝ}
    (hν : Ingham.SmoothingData ν) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {X : ℝ} (hX : 3 < X) :
    Integrable (fun t : ℝ ↦
      IntegrandL χ ν ε X (((1 + (Real.log X)⁻¹ : ℝ) : ℂ) + t * I)) := by
  obtain ⟨hdiff, hnn, hsupp, hmass⟩ := hν
  obtain ⟨hlog, hσ1, hσ2, -, -⟩ := sigma0_facts hX
  set σ : ℝ := 1 + (Real.log X)⁻¹ with hσ
  have hX0 : 0 < X := by linarith
  have hsre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t ↦ by simp
  have hmel : Integrable (fun t : ℝ ↦ mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)) :=
    SmoothedChebyshevDirichlet_aux_integrable hdiff hnn hsupp hmass hε hε1 hσ1 hσ2.le
  have heq : (fun t : ℝ ↦ IntegrandL χ ν ε X ((σ : ℂ) + t * I)) = fun t : ℝ ↦
      ((-deriv (DirichletCharacter.LFunction χ) (σ + t * I)) /
        DirichletCharacter.LFunction χ (σ + t * I) * (X : ℂ) ^ ((σ : ℂ) + t * I)) *
        mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) := by
    ext t; simp only [IntegrandL]; ring
  rw [heq]
  refine hmel.bdd_mul (c := ‖-deriv riemannZeta σ / riemannZeta σ‖ * X ^ σ) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hline : Continuous fun t : ℝ ↦ (σ : ℂ) + t * I := by fun_prop
    have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
    refine Continuous.mul ?_ (Continuous.const_cpow hline (Or.inl hX'))
    refine Continuous.div ((differentiable_deriv_LFunction hχ).continuous.comp hline).neg
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp hline) ?_
    intro t
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hsre]; linarith)
  · refine ae_of_all _ fun t ↦ ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0, hsre]
    gcongr
    exact norm_neg_logDeriv_le χ hσ1 t

/-- Holomorphy of the integrand to the right of `θ`. -/
theorem integrandL_holomorphicOn (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {θ : ℝ} (hθ : 0 < θ)
    (hz : ZeroFreeRightL χ θ) {ν : ℝ → ℝ} (hν : Ingham.SmoothingData ν) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) {X : ℝ} (hX : 0 < X) :
    HolomorphicOn (IntegrandL χ ν ε X) {s : ℂ | θ < s.re} := by
  obtain ⟨hdiff, hnn, hsupp, hmass⟩ := hν
  intro s hs
  simp only [mem_ofPred_eq] at hs
  apply DifferentiableAt.differentiableWithinAt
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
  · exact ((differentiable_deriv_LFunction hχ) s).neg.div
      ((DirichletCharacter.differentiable_LFunction hχ) s) (hz s hs)
  · exact Smooth1MellinDifferentiable hdiff hsupp ⟨hε, hε1⟩ hnn hmass (by linarith)
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl hX')

theorem shiftProp (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {θ σ₁ : ℝ} (hθσ : θ < σ₁) (hσ₁ : σ₁ < 1) (hθ : 0 < θ) (hz : ZeroFreeRightL χ θ)
    {ν : ℝ → ℝ} (hν : Ingham.SmoothingData ν) : ShiftProp χ ν σ₁ := by
  intro ε hε hε1 X hX T hT
  obtain ⟨hlog, hσ1, hσ2, -, -⟩ := sigma0_facts hX
  have hX0 : 0 < X := by linarith
  set σ₀ : ℝ := 1 + (Real.log X)⁻¹ with hσ₀
  set f : ℂ → ℂ := IntegrandL χ ν ε X with hf
  have hint : Integrable (fun t : ℝ ↦ f ((σ₀ : ℂ) + t * I)) :=
    integrandL_integrable χ hχ hν hε hε1 hX
  have hR : RectangleIntegral f ((σ₁ : ℂ) - T * I) ((σ₀ : ℂ) + T * I) = 0 := by
    apply (integrandL_holomorphicOn χ hχ hθ hz hν hε hε1 hX0).vanishesOnRectangle
    intro s hs
    simp only [Rectangle, mem_reProdIm, sub_re, add_re, ofReal_re, mul_re, I_re, I_im,
      ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hs
    simp only [mem_ofPred_eq]
    rw [uIcc_of_le (by linarith)] at hs
    linarith [hs.1.1]
  simp only [RectangleIntegral, HIntegral, VIntegral, sub_re, add_re, ofReal_re, mul_re, I_re,
    I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero, zero_sub, sub_im, add_im, mul_im,
    zero_add, smul_eq_mul] at hR
  simp only [SmoothedChebyshevL, VerticalIntegral', smul_eq_mul]
  rw [verticalIntegral_split_three (-T) T hint]
  simp only [VIntegral, smul_eq_mul, J₁, J₂, J₃₇, J₈, J₉]
  rw [← hσ₀, show (1 : ℂ) + ((Real.log X)⁻¹ : ℝ) = (σ₀ : ℂ) by rw [hσ₀]; push_cast; ring]
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg] at hR
  rw [hf] at hR
  linear_combination (1 / (2 * (π : ℂ) * I)) * hR

end InghamL
