module

public import PalomarIngham.Ingham.Basic
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
set_option autoImplicit false

/-!
# `ζ'/ζ(σ + it) ≪ log |t|` to the right of a zero-free half-plane

We prove `Ingham.logDerivLogBound_of_zeroFreeRight`: if `ζ(s) ≠ 0` for `Re s > θ`
(`1/2 ≤ θ`), then for every `σ₁ > θ` there is `K` with
`‖ζ'/ζ(σ + it)‖ ≤ K log |t|` for `σ₁ ≤ σ ≤ 2`, `|t| ≥ 3`.

Proof (Titchmarsh §14.2): centre `s₀ = 2 + it`; on a disc around `s₀` avoiding the half-plane
`Re s ≤ θ`, `ζ` has a holomorphic logarithm `J` with `Re J = log|ζ(s)| - log|ζ(s₀)|`.
A polynomial upper bound for `ζ` and a lower bound for `|ζ(2 + it)|` bound `Re J ≪ log|t|`;
Borel–Carathéodory for the derivative then bounds `J' = ζ'/ζ`.

The general complex-analysis lemmas (Borel–Carathéodory for the derivative, holomorphic
logarithm of a non-vanishing function) are copied, with minor changes, from PNT+'s
`PrimeNumberTheoremAnd/StrongPNT.lean` (which is not imported by `MediumPNT`, hence not built
here); the lower bound for `ζ(2 + it)` is adapted from `ZetaFixedLowerBound` in the same file.
-/

@[expose] public section


open Complex Metric Set

namespace Ingham

namespace LogDerivBoundAux

/-- Borel–Carathéodory on an open ball (copied from PNT+ `borelCaratheodory'`). -/
theorem borelCaratheodory_ball {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn,
      fun z hz => by rw [Set.mem_ofPred_eq]; linarith [realPartBounded z hz],
      Rpos, by exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hyp_z) hyp_r),
      zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact Continuous.div_const
        ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const) _
    refine le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ?_
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

/-- Cauchy's formula for the derivative (copied from PNT+ `cauchy_formula_deriv`). -/
lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

/-- Copied from PNT+ `DerivativeBound`. -/
lemma derivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith)
    (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory_ball Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr

/-- Borel–Carathéodory for the derivative (copied from PNT+ `BorelCaratheodoryDeriv`). -/
theorem borelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by
    have hRr : R - r ≠ 0 := by linarith
    have h2 : R - (R + r) / 2 = (R - r) / 2 := by ring
    have h3 : (R + r) / 2 - r = (R - r) / 2 := by ring
    rw [h2, h3]; field_simp; ring
  calc ‖deriv f z‖
    _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
      derivativeBound Mpos rpos (by linarith) (by linarith)
        analytic_f zeroAtZero realPartBounded hyp_z
    _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
      have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
      rw [this]; bound

/-- Holomorphic logarithm of a non-vanishing analytic function on a disc
(copied from PNT+ `LogOfAnalyticFunction`). -/
theorem logOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R,
      (HasDerivAt J_B (deriv B z / B z) z)) ∧
      J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert! this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  refine ⟨J_B, fun z hz => ?_, hJB.2.1, fun z hz => ?_, hJB.2.2⟩
  · exact DifferentiableOn.analyticAt
      (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt)
      (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv


section
variable {α R : Type*} [SeminormedCommRing R] [NormMulClass R] [NormOneClass R]
 {f : α → R} {x : R}

lemma hasProd_nnnorm (hfx : HasProd f x) : HasProd (‖f ·‖₊) ‖x‖₊ := by
  simp only [HasProd, ← nnnorm_prod, SummationFilter.unconditional_filter] at ⊢ hfx
  exact hfx.nnnorm

theorem multipliable_nnnorm (hf : Multipliable f) : Multipliable (‖f ·‖₊) :=
  let ⟨x, hx⟩ := hf; ⟨‖x‖₊, hasProd_nnnorm hx⟩

lemma multipliable_nnnorm_tprod (hf : Multipliable f) : ‖∏' i, f i‖₊ = ∏' i, ‖f i‖₊ :=
  (hasProd_nnnorm hf.hasProd).tprod_eq.symm
end

lemma zetaTwoLowerBound (t : ℝ) :
    ‖riemannZeta (2 + I * t)‖₊ ≥ ‖riemannZeta 4 / riemannZeta 2‖₊ := by
  have mp : ∀ {s : ℂ}, 1 < s.re → Multipliable fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹ := by
    intro s hs
    exact ⟨riemannZeta s, riemannZeta_eulerProduct_hasProd hs⟩
  have h₁ : 1 < (2 : ℂ).re := by norm_num
  have h₂ : 1 < (4 : ℂ).re := by norm_num
  have h₃ : 1 < (2 + I * (t : ℂ)).re := by norm_num
  rw [nnnorm_div, ge_iff_le,
    div_le_iff₀ (nnnorm_pos.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))),
    ← riemannZeta_eulerProduct_tprod h₁, ← riemannZeta_eulerProduct_tprod h₂,
    ← riemannZeta_eulerProduct_tprod h₃, multipliable_nnnorm_tprod (mp h₁),
    multipliable_nnnorm_tprod (mp h₂),
    multipliable_nnnorm_tprod (mp h₃),
    ← (multipliable_nnnorm (mp h₃)).tprod_mul (multipliable_nnnorm (mp h₁))]
  refine (multipliable_nnnorm (mp h₂)).tprod_le_tprod (fun p ↦ ?_)
    ((multipliable_nnnorm (mp h₃)).mul (multipliable_nnnorm (mp h₁)))
  simp only [nnnorm_inv, ← mul_inv]
  have hfact : ‖1 - (p : ℂ) ^ (-4 : ℂ)‖₊ =
      ‖1 + (p : ℂ) ^ (-2 : ℂ)‖₊ * ‖1 - (p : ℂ) ^ (-(2 : ℂ))‖₊ := by
    rw [← nnnorm_mul]; congr 1
    have : (p : ℂ) ^ (-4 : ℂ) = ((p : ℂ) ^ (-2 : ℂ)) ^ 2 := by
      rw [← Complex.cpow_nat_mul]; norm_num
    rw [this]; ring
  have hne : ∀ {s : ℂ}, 1 < s.re → (1 - (p : ℂ) ^ (-s)) ≠ 0 :=
    fun hs ↦ Complex.one_sub_prime_cpow_ne_zero p.2 hs
  rw [inv_le_inv₀, hfact]
  · apply _root_.mul_le_mul_left
    rw [← norm_toNNReal, ← norm_toNNReal]
    apply Real.toNNReal_le_toNNReal
    calc ‖1 - (p : ℂ) ^ (-(2 + I * ↑t))‖
        ≤ 1 + ‖(p : ℂ) ^ (-(2 + I * ↑t))‖ := by
          rw [← Complex.norm_of_nonneg zero_le_one]; exact norm_sub_le _ _
      _ = ‖1 + (p : ℂ) ^ (-2 : ℂ)‖ := by
          have : 0 ≤ 1 + (p : ℝ) ^ (-(2 : ℝ)) :=
            by linarith [Real.rpow_nonneg (Nat.cast_nonneg' (p : ℕ)) (-2)]
          rw [Complex.norm_natCast_cpow_of_pos (Nat.Prime.pos p.2)]
          have e1 : (-(2 + I * (t : ℂ))).re = -(2 : ℝ) := by simp
          have e2 : ((p : ℕ) : ℂ) ^ (-2 : ℂ) = (((p : ℕ) : ℝ) ^ (-(2 : ℝ)) : ℝ) := by
            rw [Complex.ofReal_cpow (Nat.cast_nonneg' _)]; push_cast; rfl
          rw [e1, e2, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
            Real.norm_of_nonneg this]
  · exact norm_pos_iff.mpr (hne h₂)
  · exact mul_pos (norm_pos_iff.mpr (hne h₃)) (norm_pos_iff.mpr (hne h₁))

lemma zeta_norm_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 4) (hi : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 11 + 2 * |s.im| := by
  have hs1 : s ≠ 1 := by
    rintro rfl; simp at hi; norm_num at hi
  have hs0 : s ≠ 0 := by
    rintro rfl; simp at hi; norm_num at hi
  have hσ : 0 < s.re := by linarith
  have hint := ZetaBnd_aux1b 1 le_rfl (t := s.im) hσ
  rw [re_add_im s, Nat.cast_one, Real.one_rpow] at hint
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs1, riemannZeta0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_one, Nat.cast_zero,
    one_cpow, zero_cpow hs0, div_zero, zero_add, div_one] at hint ⊢
  set I1 := ∫ (x : ℝ) in Ioi 1, (↑⌊x⌋ + 1 / 2 - ↑x) / (x : ℂ) ^ (s + 1) with hI1
  have him : |s.im| ≤ ‖1 - s‖ := by
    have := abs_im_le_norm (1 - s); simpa using this
  have hA : ‖(-1 : ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_neg, norm_one, div_le_one (by linarith)]; linarith
  have hB : ‖(-1 : ℂ) / 2‖ = 1 / 2 := by simp
  have hs : ‖s‖ ≤ s.re + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ = s.re + |s.im| := by rw [abs_of_pos hσ]
  have hC : ‖s * I1‖ ≤ 8 + 2 * |s.im| := by
    rw [norm_mul]
    calc ‖s‖ * ‖I1‖ ≤ (s.re + |s.im|) * (1 / s.re) :=
          mul_le_mul hs hint (norm_nonneg _) (by positivity)
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / (1 / 2) := by gcongr
      _ ≤ 8 + 2 * |s.im| := by linarith [abs_nonneg s.im]
  calc _ ≤ ‖(1 : ℂ)‖ + ‖(-1 : ℂ) / (1 - s)‖ + ‖(-1 : ℂ) / 2‖ + ‖s * I1‖ := norm_add₄_le
    _ ≤ 11 + 2 * |s.im| := by rw [norm_one, hB]; linarith


/-- The main estimate for a fixed ordinate `t`. -/
lemma logDeriv_bound_fixed {θ σ₁ : ℝ} (hθ : 1 / 2 ≤ θ) (hθσ : θ < σ₁) (hσ₁ : σ₁ ≤ 2)
    (hz : ZeroFreeRight θ) {σ t : ℝ} (hσ1 : σ₁ ≤ σ) (hσ2 : σ ≤ 2) (ht : 3 ≤ |t|) :
    ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
      512 * (Real.log 7 + Real.log |t| - Real.log ‖riemannZeta 4 / riemannZeta 2‖ + 1) /
        ((σ₁ - θ) / 3) ^ 3 := by
  set δ := (σ₁ - θ) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδle : δ ≤ 1 / 2 := by rw [hδ]; linarith
  set R₀ := 2 - θ - δ with hR₀
  set R := 2 - σ₁ + δ with hR
  set r := 2 - σ₁ + δ / 2 with hr
  set c := ‖riemannZeta 4 / riemannZeta 2‖ with hc
  set M := Real.log 7 + Real.log |t| - Real.log c + 1 with hM
  set s₀ : ℂ := 2 + t * I with hs₀
  set B : ℂ → ℂ := fun w => riemannZeta (s₀ + w) with hB
  have hr_pos : 0 < r := by rw [hr]; linarith
  have hr_lt_R : r < R := by rw [hr, hR]; linarith
  have hR_lt_R₀ : R < R₀ := by rw [hR, hR₀, hδ]; linarith
  have hr_lt_R₀ : r < R₀ := hr_lt_R.trans hR_lt_R₀
  have hR₀_le : R₀ ≤ 3 / 2 := by rw [hR₀]; linarith
  -- geometry of the disc
  have hre : ∀ w : ℂ, ‖w‖ ≤ R₀ → θ + δ ≤ (s₀ + w).re ∧ (s₀ + w).re ≤ 4 := by
    intro w hw
    have h1 := abs_re_le_norm w
    have h2 := abs_le.mp (h1.trans hw)
    have : (s₀ + w).re = 2 + w.re := by simp [hs₀]
    rw [this]; constructor <;> linarith
  have him : ∀ w : ℂ, ‖w‖ ≤ R₀ →
      |t| - 3 / 2 ≤ |(s₀ + w).im| ∧ |(s₀ + w).im| ≤ |t| + 3 / 2 := by
    intro w hw
    have h1 := (abs_im_le_norm w).trans hw
    have : (s₀ + w).im = t + w.im := by simp [hs₀]
    rw [this]
    constructor
    · have := abs_sub_abs_le_abs_sub t (-w.im)
      rw [sub_neg_eq_add, abs_neg] at this; linarith
    · have := abs_add_le t w.im; linarith
  have hne1 : ∀ w : ℂ, ‖w‖ ≤ R₀ → s₀ + w ≠ 1 := by
    intro w hw h
    have := (him w hw).1
    rw [h] at this; simp at this; linarith
  have hBan : AnalyticOnNhd ℂ B (closedBall 0 R₀) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    exact (analyticAt_riemannZeta (hne1 w hw)).comp (analyticAt_const.add analyticAt_id)
  have hBne : ∀ w ∈ closedBall (0 : ℂ) R₀, B w ≠ 0 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    exact hz _ (by linarith [(hre w hw).1])
  obtain ⟨J, hJan, hJ0, hJd, hJre⟩ := logOfAnalyticFunction hr_pos hr_lt_R₀ hBan hBne
  -- upper bound for `B`
  have hBup : ∀ w : ℂ, ‖w‖ ≤ R₀ → ‖B w‖ ≤ 7 * |t| := by
    intro w hw
    have h := zeta_norm_le (s := s₀ + w) (by linarith [(hre w hw).1]) (hre w hw).2
      (by linarith [(him w hw).1])
    have := (him w hw).2
    show ‖riemannZeta (s₀ + w)‖ ≤ 7 * |t|
    linarith
  -- lower bound at the centre
  have hc_pos : 0 < c := by
    rw [hc, norm_div]
    exact div_pos (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
      (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hB0 : c ≤ ‖B 0‖ := by
    have h := zetaTwoLowerBound t
    have e : B 0 = riemannZeta (2 + I * t) := by
      simp only [hB, hs₀, add_zero]; congr 1; ring
    rw [e, hc]
    exact_mod_cast h
  have hB0pos : 0 < ‖B 0‖ := hc_pos.trans_le hB0
  have ht0 : 0 < |t| := by linarith
  have hlogB0 : Real.log c ≤ Real.log ‖B 0‖ := Real.log_le_log hc_pos hB0
  have hlogup : ∀ w : ℂ, ‖w‖ ≤ R₀ → Real.log ‖B w‖ ≤ Real.log 7 + Real.log |t| := by
    intro w hw
    rw [← Real.log_mul (by norm_num) ht0.ne']
    exact Real.log_le_log (norm_pos_iff.mpr (hBne w (by simpa using hw))) (hBup w hw)
  have hMpos : 0 < M := by
    have := hlogup 0 (by simp; linarith)
    rw [hM]; linarith
  have hreJ : ∀ z ∈ ball (0 : ℂ) R, (J z).re ≤ M := by
    intro z hz'
    have hzR : ‖z‖ < R := by simpa using hz'
    rw [← hJre z (by simpa using hzR.trans hR_lt_R₀)]
    have := hlogup z (by linarith)
    rw [hM]; linarith
  have hzmem : ((σ : ℂ) - 2) ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall, dist_zero_right]
    have : ((σ : ℂ) - 2) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    rw [hr]; linarith
  have key := borelCaratheodoryDeriv hMpos hr_pos hr_lt_R
    ((hJan.mono (ball_subset_ball hR_lt_R₀.le)).analyticOn) hJ0 hreJ hzmem
  rw [hJd _ hzmem] at key
  have hder : deriv B ((σ : ℂ) - 2) = deriv riemannZeta (σ + t * I) := by
    rw [hB, deriv_comp_const_add]; congr 1; rw [hs₀]; ring
  have hval : B ((σ : ℂ) - 2) = riemannZeta (σ + t * I) := by
    simp only [hB, hs₀]; congr 1; ring
  rw [hder, hval] at key
  have hRr : R - r = δ / 2 := by rw [hR, hr]; ring
  have hR_nonneg : 0 ≤ R := by linarith
  have hR_le : R ≤ 2 := by rw [hR]; linarith
  calc _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := key
    _ = 128 * M * R ^ 2 / δ ^ 3 := by rw [hRr]; field_simp; ring
    _ ≤ 128 * M * 2 ^ 2 / δ ^ 3 := by gcongr
    _ = 512 * M / δ ^ 3 := by ring

end LogDerivBoundAux

open LogDerivBoundAux in
/-- **`ζ'/ζ ≪ log |t|` to the right of a zero-free half-plane.** -/
theorem logDerivLogBound_of_zeroFreeRight {θ σ₁ : ℝ} (hθ : 1 / 2 ≤ θ) (hθσ : θ < σ₁)
    (hz : ZeroFreeRight θ) : LogDerivLogBound σ₁ := by
  by_cases hσ₁ : σ₁ ≤ 2
  · set δ := (σ₁ - θ) / 3 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    set c := ‖riemannZeta 4 / riemannZeta 2‖ with hc
    set L := Real.log 7 + |Real.log c| + 2 with hL
    have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
    have hLpos : 0 < L := by rw [hL]; positivity
    refine ⟨512 * L / δ ^ 3, by positivity, ?_⟩
    intro σ t h1 h2 ht
    have hlog : 1 ≤ Real.log |t| := (logt_gt_one ht).le
    have habs := neg_abs_le (Real.log c)
    calc _ ≤ 512 * (Real.log 7 + Real.log |t| - Real.log c + 1) / δ ^ 3 :=
          logDeriv_bound_fixed hθ hθσ hσ₁ hz h1 h2 ht
      _ ≤ 512 * (L * Real.log |t|) / δ ^ 3 := by
          gcongr
          rw [hL]
          nlinarith [abs_nonneg (Real.log c)]
      _ = 512 * L / δ ^ 3 * Real.log |t| := by ring
  · refine ⟨1, one_pos, ?_⟩
    intro σ t h1 h2 _
    exact absurd (h1.trans h2) hσ₁

end Ingham
