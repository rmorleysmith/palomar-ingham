module

public import PalomarIngham.Dirichlet.Basic
public import PalomarIngham.Ingham.LogDerivBound
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false

/-!
# `L'/L(σ + it, χ) ≪ log |t|` to the right of a zero-free half-plane (`χ ≠ 1`)

`InghamL.logDerivLBound_of_zeroFree`: the analogue of `Ingham.logDerivLogBound_of_zeroFreeRight`
for Dirichlet `L`-functions of nontrivial characters. The disc argument (holomorphic logarithm +
Borel–Carathéodory for the derivative) is the same, reusing the generic lemmas of
`PalomarIngham.Ingham.LogDerivBound`. New ingredients:

* `LogDerivLAux.LFunction_norm_le`: `‖L(s, χ)‖ ≤ A (1 + |Im s|)` for `1/2 ≤ Re s ≤ 4`. Proof:
  `Fχ s = ∑ (χ(n) n^{-s} - χ(n) b(n)^{-s})`, with `b(n) = q (⌊n/q⌋ + 1)`, converges locally
  uniformly on `Re s > 0` (mean value theorem: each term is `≪ |s| q n^{-Re s - 1}`); the
  subtracted series vanishes for `Re s > 1` (sum over residue classes, `∑ χ = 0`), so `Fχ = L` on
  `Re s > 1`, hence on `Re s > 0` by the identity theorem.
* `LogDerivLAux.LFunction_two_lower`: `‖L(2 + it, χ)‖ ≥ 1 - ∑_{n ≥ 2} n^{-2} = 2 - π²/6 > 0`.
-/

@[expose] public section

open Complex Metric Set

namespace InghamL

namespace LogDerivLAux

variable {q : ℕ} [NeZero q]

set_option linter.unusedSectionVars false

lemma norm_cpow_neg_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : -1 ≤ s.re) :
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  have hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s))
      ((-s) * (x : ℂ) ^ (-s - 1)) (Icc a b) x := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have h := (Complex.hasStrictDerivAt_cpow_const (c := -s) (x := (x : ℂ))
      (Complex.ofReal_mem_slitPlane.mpr hx0)).hasDerivAt
    exact h.comp_ofReal.hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a b, ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    gcongr
    have : (-s - 1).re = -s.re - 1 := by simp
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨hab, le_rfl⟩

/-- `blk q n = q * (n / q + 1)`, the least multiple of `q` exceeding `n`. -/
def blk (q n : ℕ) : ℕ := q * (n / q + 1)

lemma lt_blk (n : ℕ) : n < blk q n := Nat.lt_mul_div_succ n (Nat.pos_of_neZero q)

lemma blk_le (n : ℕ) : blk q n ≤ n + q := by
  unfold blk; rw [mul_add, mul_one]; have := Nat.mul_div_le n q; omega

/-- Correction terms `χ(n) · blk(n)^{-s}`, whose sum vanishes for `Re s > 1`. -/
noncomputable def gterm (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  χ n * ((blk q n : ℕ) : ℂ) ^ (-s)

lemma norm_gterm_le (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) (hs : 0 ≤ s.re) :
    ‖gterm χ s n‖ ≤ ((n : ℝ) + 1) ^ (-s.re) := by
  rw [gterm, norm_mul]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (n : ℝ) + 1 ≤ (blk q n : ℝ) := by exact_mod_cast lt_blk n
  rw [show ((blk q n : ℕ) : ℂ) = ((blk q n : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos (hpos.trans_le hb)]
  calc _ ≤ 1 * (blk q n : ℝ) ^ (-s).re := by
        gcongr; exact χ.norm_le_one _
    _ ≤ _ := by
        rw [one_mul, neg_re]; exact Real.rpow_le_rpow_of_nonpos hpos hb (by linarith)

lemma summable_gterm (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Summable (gterm χ s) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re)) ?_
    (fun n => norm_gterm_le χ s n (by linarith))
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
  simpa using this

lemma tsum_gterm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    ∑' n, gterm χ s n = 0 := by
  rw [Nat.sumByResidueClasses (summable_gterm χ hs) q]
  have key : ∀ j : ZMod q, ∑' m, gterm χ s (j.val + q * m) =
      χ j * ∑' m : ℕ, ((q * (m + 1) : ℕ) : ℂ) ^ (-s) := by
    intro j
    rw [← tsum_mul_left]
    congr 1; ext m
    have hdiv : (j.val + q * m) / q = m := by
      rw [Nat.add_mul_div_left _ _ (Nat.pos_of_neZero q), Nat.div_eq_of_lt (ZMod.val_lt j),
        zero_add]
    simp only [gterm, blk, hdiv]
    congr 1
    push_cast
    simp
  simp_rw [key, ← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]

/-- The summands of the continuation of `L(s, χ)` to `Re s > 0`. -/
noncomputable def hterm (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun n => χ n) s n - gterm χ s n

/-- The continuation of `L(s, χ)` to `Re s > 0`. -/
noncomputable def Fχ (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := ∑' n, hterm χ s n

lemma hterm_zero (χ : DirichletCharacter ℂ q) (s : ℂ) :
    hterm χ s 0 = -(χ 0 * (q : ℂ) ^ (-s)) := by
  simp [hterm, gterm, blk]

lemma hterm_of_ne_zero (χ : DirichletCharacter ℂ q) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    hterm χ s n = χ n * ((n : ℂ) ^ (-s) - ((blk q n : ℕ) : ℂ) ^ (-s)) := by
  rw [hterm, LSeries.term_of_ne_zero hn, gterm]; simp only [cpow_neg, div_eq_mul_inv, mul_sub]

/-- Dominating sequence. -/
noncomputable def vseq (q : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else (q : ℝ) * (n : ℝ) ^ (-ε - 1)

lemma vseq_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ vseq q ε n := by
  unfold vseq; split_ifs <;> positivity

lemma summable_vseq {ε : ℝ} (hε : 0 < ε) : Summable (vseq q ε) := by
  rw [← summable_nat_add_iff 1]
  have := ((summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith : -ε - 1 < -1))).mul_left (q : ℝ)
  refine this.congr (fun n => ?_)
  simp [vseq]

lemma norm_hterm_le (χ : DirichletCharacter ℂ q) {ε : ℝ} {s : ℂ} (hε : 0 ≤ ε) (hεs : ε ≤ s.re)
    (n : ℕ) : ‖hterm χ s n‖ ≤ (1 + ‖s‖) * vseq q ε n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [vseq, ↓reduceIte]
    rw [hterm_zero, norm_neg, norm_mul, mul_one]
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have := mul_le_mul (χ.norm_le_one 0)
      (Real.rpow_le_one_of_one_le_of_nonpos hq (by simp; linarith : (-s).re ≤ 0))
      (by positivity) zero_le_one
    linarith [norm_nonneg s]
  · simp only [vseq, hn, ↓reduceIte]
    rw [hterm_of_ne_zero χ s hn, norm_mul]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hb1 : (n : ℝ) ≤ (blk q n : ℝ) := by exact_mod_cast (lt_blk n).le
    have hb2 : (blk q n : ℝ) ≤ n + q := by exact_mod_cast blk_le n
    have h := norm_cpow_neg_sub_le (s := s) (by linarith) hb1 (by linarith)
    rw [norm_sub_rev] at h
    simp only [Complex.ofReal_natCast] at h
    calc _ ≤ 1 * (‖s‖ * (n : ℝ) ^ (-s.re - 1) * ((blk q n : ℝ) - n)) := by
          gcongr
          exact χ.norm_le_one _
      _ ≤ ‖s‖ * (n : ℝ) ^ (-ε - 1) * q := by
          rw [one_mul]
          gcongr; linarith
      _ ≤ _ := by
          have : 0 ≤ (q : ℝ) * (n : ℝ) ^ (-ε - 1) := by positivity
          nlinarith

lemma differentiable_hterm (χ : DirichletCharacter ℂ q) (n : ℕ) :
    Differentiable ℂ (fun s => hterm χ s n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : (fun s => hterm χ s 0) = fun s => -(χ 0 * (q : ℂ) ^ (-s)) :=
      funext fun s => hterm_zero χ s
    rw [this]
    exact ((differentiable_neg.const_cpow
      (Or.inl (by exact_mod_cast NeZero.ne q))).const_mul _).neg
  · have : (fun s => hterm χ s n) =
        fun s => χ n * ((n : ℂ) ^ (-s) - ((blk q n : ℕ) : ℂ) ^ (-s)) :=
      funext fun s => hterm_of_ne_zero χ s hn
    rw [this]
    have hb : ((blk q n : ℕ) : ℂ) ≠ 0 := by
      have := lt_blk (q := q) n; exact_mod_cast (show blk q n ≠ 0 by omega)
    exact ((differentiable_neg.const_cpow (Or.inl (by exact_mod_cast hn))).sub
      (differentiable_neg.const_cpow (Or.inl hb))).const_mul _

lemma differentiableAt_Fχ (χ : DirichletCharacter ℂ q) {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    DifferentiableAt ℂ (Fχ χ) s₀ := by
  set ε := s₀.re / 2 with hε
  set R := ‖s₀‖ + 1 with hR
  set U := {s : ℂ | ε < s.re} ∩ ball 0 R with hU
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter isOpen_ball
  have hmem : s₀ ∈ U := ⟨by show ε < s₀.re; rw [hε]; linarith, by simp [hR]⟩
  have hd : DifferentiableOn ℂ (Fχ χ) U := by
    refine differentiableOn_tsum_of_summable_norm ((summable_vseq (q := q) hεpos).mul_left (1 + R))
      (fun n => (differentiable_hterm χ n).differentiableOn) hUo ?_
    intro n w hw
    have hw1 : ε < w.re := hw.1
    have hw2 : ‖w‖ < R := by simpa using hw.2
    calc ‖hterm χ w n‖ ≤ (1 + ‖w‖) * vseq q ε n := norm_hterm_le χ hεpos.le hw1.le n
      _ ≤ (1 + R) * vseq q ε n := mul_le_mul_of_nonneg_right (by linarith) (vseq_nonneg _ _)
  exact hd.differentiableAt (hUo.mem_nhds hmem)

lemma Fχ_eq_of_one_lt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    Fχ χ s = DirichletCharacter.LFunction χ s := by
  rw [Fχ, DirichletCharacter.LFunction_eq_LSeries χ hs]
  unfold hterm
  rw [(DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).tsum_sub (summable_gterm χ hs),
    tsum_gterm χ hχ hs, sub_zero, LSeries]

lemma Fχ_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Fχ χ s = DirichletCharacter.LFunction χ s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (Fχ χ) {s : ℂ | 0 < s.re} :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_Fχ χ hs).differentiableWithinAt) hU
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have heq : Fχ χ =ᶠ[nhds 2] DirichletCharacter.LFunction χ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact Fχ_eq_of_one_lt χ hχ hz
  exact hF.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (0 : ℝ) < (2 : ℂ).re by norm_num) heq hs

/-- Polynomial upper bound for `L(s, χ)` in the strip `1/2 ≤ Re s ≤ 4`. -/
lemma LFunction_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ A > 0, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ A * (1 + |s.im|) := by
  set Z := ∑' n, vseq q (1 / 2) n with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun n => vseq_nonneg _ n)
  refine ⟨5 * Z + 1, by positivity, fun s h1 h2 => ?_⟩
  rw [← Fχ_eq χ hχ (by linarith)]
  have hsum := (summable_vseq (q := q) (by norm_num : (0 : ℝ) < 1 / 2)).mul_left (1 + ‖s‖)
  have hs : ‖s‖ ≤ 4 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ 4 + |s.im| := by rw [abs_of_pos (by linarith)]; linarith
  calc ‖Fχ χ s‖ ≤ ∑' n, (1 + ‖s‖) * vseq q (1 / 2) n :=
        tsum_of_norm_bounded hsum.hasSum (fun n => norm_hterm_le χ (by norm_num) h1 n)
    _ = (1 + ‖s‖) * Z := tsum_mul_left
    _ ≤ (5 * (1 + |s.im|)) * Z := by gcongr; linarith [abs_nonneg s.im]
    _ ≤ _ := by nlinarith [abs_nonneg s.im]

/-- Lower bound on the line `Re s = 2`: `‖L(2 + it, χ)‖ ≥ 2 - π²/6`. -/
lemma LFunction_two_lower (χ : DirichletCharacter ℂ q) (t : ℝ) :
    2 - Real.pi ^ 2 / 6 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
  have hs : 1 < (2 + t * I : ℂ).re := by simp
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  rw [← hsum.sum_add_tsum_nat_add 2]
  have hg : HasSum (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ] using this
  have hb : ‖∑' n, LSeries.term (fun n => χ n) (2 + t * I) (n + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    refine tsum_of_norm_bounded hg (fun n => ?_)
    rw [LSeries.norm_term_eq]
    simp only [show n + 2 ≠ 0 by omega, ↓reduceIte]
    have h2 : (2 + t * I : ℂ).re = 2 := by simp
    rw [h2, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    gcongr
    exact χ.norm_le_one _
  have h1 : ∑ i ∈ Finset.range 2, LSeries.term (fun n => χ n) (2 + t * I) i = 1 := by
    simp [Finset.sum_range_succ]
  rw [h1]
  have := norm_sub_norm_le (1 : ℂ) (-∑' n, LSeries.term (fun n => χ n) (2 + t * I) (n + 2))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

lemma two_sub_pi_sq_pos : 0 < 2 - Real.pi ^ 2 / 6 := by
  have h := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

open Ingham.LogDerivBoundAux in
/-- The main estimate for a fixed ordinate `t` (adapted from
`Ingham.LogDerivBoundAux.logDeriv_bound_fixed`). Here `K₀ |t|` bounds `‖L‖` near `2 + it` and
`c` bounds `‖L(2 + it)‖` from below. -/
lemma logDerivL_bound_fixed (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {θ σ₁ K₀ c : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθσ : θ < σ₁) (hσ₁ : σ₁ ≤ 2) (hz : ZeroFreeRightL χ θ) (hc_pos : 0 < c)
    (hlow : ∀ t : ℝ, c ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖)
    (hK₀ : 0 < K₀) (hup : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ K₀ / 2 * (1 + |s.im|))
    {σ t : ℝ} (hσ1 : σ₁ ≤ σ) (hσ2 : σ ≤ 2) (ht : 3 ≤ |t|) :
    ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
        DirichletCharacter.LFunction χ (σ + t * I)‖ ≤
      512 * (Real.log K₀ + Real.log |t| - Real.log c + 1) / ((σ₁ - θ) / 3) ^ 3 := by
  set δ := (σ₁ - θ) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set R₀ := 2 - θ - δ with hR₀
  set R := 2 - σ₁ + δ with hR
  set r := 2 - σ₁ + δ / 2 with hr
  set M := Real.log K₀ + Real.log |t| - Real.log c + 1 with hM
  set s₀ : ℂ := 2 + t * I with hs₀
  set B : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (s₀ + w) with hB
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
  have hBan : AnalyticOnNhd ℂ B (closedBall 0 R₀) := by
    intro w _
    exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt _).comp
      (analyticAt_const.add analyticAt_id)
  have hBne : ∀ w ∈ closedBall (0 : ℂ) R₀, B w ≠ 0 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    exact hz _ (by linarith [(hre w hw).1])
  obtain ⟨J, hJan, hJ0, hJd, hJre⟩ := logOfAnalyticFunction hr_pos hr_lt_R₀ hBan hBne
  -- upper bound for `B`
  have hBup : ∀ w : ℂ, ‖w‖ ≤ R₀ → ‖B w‖ ≤ K₀ * |t| := by
    intro w hw
    have h := hup (s₀ + w) (by linarith [(hre w hw).1]) (hre w hw).2
    have h2 := (him w hw).2
    show ‖DirichletCharacter.LFunction χ (s₀ + w)‖ ≤ K₀ * |t|
    calc _ ≤ K₀ / 2 * (1 + |(s₀ + w).im|) := h
      _ ≤ K₀ / 2 * (2 * |t|) := by gcongr; linarith
      _ = K₀ * |t| := by ring
  -- lower bound at the centre
  have hB0 : c ≤ ‖B 0‖ := by
    simpa [hB, hs₀] using hlow t
  have ht0 : 0 < |t| := by linarith
  have hlogB0 : Real.log c ≤ Real.log ‖B 0‖ := Real.log_le_log hc_pos hB0
  have hlogup : ∀ w : ℂ, ‖w‖ ≤ R₀ → Real.log ‖B w‖ ≤ Real.log K₀ + Real.log |t| := by
    intro w hw
    rw [← Real.log_mul hK₀.ne' ht0.ne']
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
  have hder : deriv B ((σ : ℂ) - 2) = deriv (DirichletCharacter.LFunction χ) (σ + t * I) := by
    rw [hB, deriv_comp_const_add]; congr 1; rw [hs₀]; ring
  have hval : B ((σ : ℂ) - 2) = DirichletCharacter.LFunction χ (σ + t * I) := by
    simp only [hB, hs₀]; congr 1; ring
  rw [hder, hval] at key
  have hRr : R - r = δ / 2 := by rw [hR, hr]; ring
  have hR_nonneg : 0 ≤ R := by linarith
  have hR_le : R ≤ 2 := by rw [hR]; linarith
  calc _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := key
    _ = 128 * M * R ^ 2 / δ ^ 3 := by rw [hRr]; field_simp; ring
    _ ≤ 128 * M * 2 ^ 2 / δ ^ 3 := by gcongr
    _ = 512 * M / δ ^ 3 := by ring

end LogDerivLAux

open LogDerivLAux in
/-- **`L'/L(s, χ) ≪ log |t|` to the right of a zero-free half-plane** (`χ ≠ 1`). -/
theorem logDerivLBound_of_zeroFree {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {θ σ₁ : ℝ} (hθ : 1 / 2 ≤ θ) (hθσ : θ < σ₁) (hz : ZeroFreeRightL χ θ) :
    LogDerivLBound χ σ₁ := by
  by_cases hσ₁ : σ₁ ≤ 2
  · obtain ⟨A, hA, hAb⟩ := LFunction_norm_le χ hχ
    set K₀ := 2 * A with hK₀
    have hK₀pos : 0 < K₀ := by rw [hK₀]; linarith
    have hup : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 4 →
        ‖DirichletCharacter.LFunction χ s‖ ≤ K₀ / 2 * (1 + |s.im|) := by
      intro s h1 h2; rw [hK₀, mul_div_cancel_left₀ _ two_ne_zero]; exact hAb s h1 h2
    set c := 2 - Real.pi ^ 2 / 6 with hc
    have hc_pos : 0 < c := two_sub_pi_sq_pos
    set δ := (σ₁ - θ) / 3 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    set L := |Real.log K₀| + |Real.log c| + 2 with hL
    have hLpos : 0 < L := by rw [hL]; positivity
    refine ⟨512 * L / δ ^ 3, by positivity, ?_⟩
    intro σ t h1 h2 ht
    have hlog : 1 ≤ Real.log |t| := (logt_gt_one ht).le
    calc _ ≤ 512 * (Real.log K₀ + Real.log |t| - Real.log c + 1) / δ ^ 3 :=
          logDerivL_bound_fixed χ hχ hθ hθσ hσ₁ hz hc_pos (LFunction_two_lower χ) hK₀pos
            hup h1 h2 ht
      _ ≤ 512 * (L * Real.log |t|) / δ ^ 3 := by
          gcongr
          rw [hL]
          nlinarith [abs_nonneg (Real.log c), abs_nonneg (Real.log K₀),
            le_abs_self (Real.log K₀), neg_abs_le (Real.log c)]
      _ = 512 * L / δ ^ 3 * Real.log |t| := by ring
  · refine ⟨1, one_pos, ?_⟩
    intro σ t h1 h2 _
    exact absurd (h1.trans h2) hσ₁

end InghamL
