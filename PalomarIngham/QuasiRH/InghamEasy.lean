module

public import PalomarIngham.QuasiRH.Continuation
public import PalomarIngham.QuasiRH.Reflection

/-!
# Regular primes force a zero-free region ("Ingham, easy direction")

Write `ψ(x) = ∑_{n ≤ x} Λ(n)` (Chebyshev's function; Mathlib's `Chebyshev.psi`). The prime
number theorem says `ψ(x) ~ x`. This file proves:

  if `ψ(x) - x = O(x^θ)`, then `ζ(s) ≠ 0` for `Re s > θ`.

So a power-saving error term in the prime number theorem *implies* a zero-free half-plane.
With `θ = 1/2 + ε` for every `ε > 0`, this gives the Riemann hypothesis
(`riemannHypothesis_of_psiError`, using the functional equation to reflect zeros).

## The proof in four lines

For `Re s > 1`, partial summation (Mathlib's `LSeries_eq_mul_integral`) gives

  `∑ Λ(n) n^{-s} = s ∫₁^∞ ψ(t) t^{-s-1} dt = s/(s-1) + s ∫₁^∞ (ψ(t) - t) t^{-s-1} dt`.

If `ψ(t) - t = O(t^θ)` the last integral is a Mellin transform which converges, and is
holomorphic, for `Re s > θ` (Mathlib's `mellin_differentiableAt_of_isBigO_rpow`). So the
right-hand side is a holomorphic `G` on `{θ < Re s, s ≠ 1}` agreeing with `-ζ'/ζ` on
`Re s > 1`; `QuasiRH.Continuation.zeroFreeRight_of_eqOn` finishes.

The converse (zero-free ⇒ error term `O(x^{θ+ε})`) is the hard direction and is *not* proved
here; see the roadmap in `README.md`.
-/

@[expose] public section


open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

namespace QuasiRH

/-- **The prime number theorem with error exponent `θ`:** `ψ(x) - x = O(x^θ)` as `x → ∞`. -/
def PsiError (θ : ℝ) : Prop :=
  (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ θ)

/-- **Chebyshev (1852): the trivial exponent.** `ψ(x) - x = O(x)`, from Mathlib's
`ψ(x) ≤ (log 4 + 4) x`. This shows `PsiError` is satisfiable; it yields only
`ZeroFreeRight 1`, which is weaker than what is known. -/
theorem psiError_one : PsiError 1 := by
  refine IsBigO.of_bound (Real.log 4 + 5) ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ x ^ (1 : ℝ)), Real.rpow_one,
    abs_le]
  have h1 := Chebyshev.psi_le_const_mul_self hx
  have h0 := Chebyshev.psi_nonneg x
  have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  constructor <;> nlinarith

/-- The error term `ψ(t) - t`, cut off to `t > 1` and viewed in `ℂ`. -/
noncomputable def psiErr : ℝ → ℂ :=
  indicator (Ioi 1) (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ))

theorem locallyIntegrableOn_psiErr : LocallyIntegrableOn psiErr (Ioi 0) := by
  have hloc : LocallyIntegrable (fun t : ℝ => Chebyshev.psi t - t) :=
    Chebyshev.psi_mono.locallyIntegrable.sub continuous_id.locallyIntegrable
  have hlocC : LocallyIntegrable (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ)) := by
    rw [locallyIntegrable_iff] at hloc ⊢
    exact fun K hK => (hloc K hK).ofReal
  exact (hlocC.indicator measurableSet_Ioi).locallyIntegrableOn _

theorem psiErr_isBigO_atTop {θ : ℝ} (h : PsiError θ) :
    psiErr =O[atTop] (fun x : ℝ => x ^ (-(-θ))) := by
  have hC : (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ)) =O[atTop] (fun x : ℝ => x ^ θ) := by
    refine isBigO_norm_left.mp ?_
    refine h.norm_left.congr_left fun t => ?_
    rw [Complex.norm_real]
  simp only [neg_neg]
  refine EventuallyEq.trans_isBigO ?_ hC
  filter_upwards [eventually_gt_atTop 1] with t ht
  simp [psiErr, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]

theorem psiErr_isBigO_nhdsGT (b : ℝ) : psiErr =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
  simp [psiErr, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => absurd ht.2 (not_lt.2 h.le))]

theorem mellinConvergent_psiErr {θ : ℝ} (h : PsiError θ) {s : ℂ} (hs : θ < s.re) :
    MellinConvergent psiErr (-s) :=
  mellinConvergent_of_isBigO_rpow (b := (-s).re - 1) locallyIntegrableOn_psiErr
    (psiErr_isBigO_atTop h) (by simp; linarith) (psiErr_isBigO_nhdsGT _) (by linarith)

theorem differentiableAt_mellin_psiErr {θ : ℝ} (h : PsiError θ) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ (fun z => mellin psiErr (-z)) s := by
  have hm : DifferentiableAt ℂ (mellin psiErr) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (b := (-s).re - 1) locallyIntegrableOn_psiErr
      (psiErr_isBigO_atTop h) (by simp; linarith) (psiErr_isBigO_nhdsGT _) (by linarith)
  exact hm.comp s differentiableAt_id.neg

/-- The Mellin transform of the error term, as an integral over `t > 1`. -/
theorem mellin_psiErr_eq (s : ℂ) :
    mellin psiErr (-s) =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(s + 1)) * ((Chebyshev.psi t - t : ℝ) : ℂ) := by
  have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • psiErr t) =
      indicator (Ioi 1) (fun t : ℝ => (t : ℂ) ^ (-(s + 1)) * ((Chebyshev.psi t - t : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [psiErr, indicator_of_mem ht, smul_eq_mul]
      ring_nf
    · simp [psiErr, indicator_of_notMem ht]
  rw [mellin, hfun, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- Partial sums of `Λ` are values of `ψ`. -/
theorem sum_Icc_vonMangoldt (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (↗Λ k : ℂ) = ((Chebyshev.psi x : ℝ) : ℂ) := by
  have hI : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by ext; simp; omega
  rw [Chebyshev.psi, hI]
  push_cast
  rfl

/-- If `ψ(x) - x = O(x^θ)` with `θ ≤ 1`, then `ψ(x) = O(x)`. -/
theorem psi_isBigO_self {θ : ℝ} (hθ : θ ≤ 1) (h : PsiError θ) :
    (fun x : ℝ => Chebyshev.psi x) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  have h1 : (fun x : ℝ => x ^ θ) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have h0 : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hx hθ
  have h2 : (fun x : ℝ => x) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
    simpa using isBigO_refl (fun x : ℝ => x) atTop
  simpa using (h.trans h1).add h2

/-- **Partial summation for `Λ`.** For `Re s > 1`, if `ψ(x) - x = O(x^θ)` with `θ < 1`,
`∑ Λ(n) n^{-s} = s/(s-1) + s · M(-s)`, where `M` is the Mellin transform of `ψ(t) - t` on
`t > 1`. -/
theorem LSeries_vonMangoldt_eq_mellin {θ : ℝ} (hθ : θ < 1) (h : PsiError θ) {s : ℂ}
    (hs : 1 < s.re) :
    L ↗Λ s = s / (s - 1) + s * mellin psiErr (-s) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (↗Λ k : ℂ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    have hψ := (psi_isBigO_self hθ.le h).comp_tendsto tendsto_natCast_atTop_atTop
    rw [← isBigO_norm_left] at hψ ⊢
    refine hψ.congr_left fun n => ?_
    simp only [Function.comp_apply]
    have hn := sum_Icc_vonMangoldt (n : ℝ)
    rw [Nat.floor_natCast] at hn
    rw [hn, Complex.norm_real]
  rw [LSeries_eq_mul_integral _ zero_le_one hs (ArithmeticFunction.LSeriesSummable_vonMangoldt hs) hO]
  simp_rw [sum_Icc_vonMangoldt]
  have hs0 : (-s).re < -1 := by simp; linarith
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hs0 one_pos
  have hI2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-(s + 1)) * ((Chebyshev.psi t - t : ℝ) : ℂ)) (Ioi 1) := by
    have hm := (mellinConvergent_psiErr h (show θ < s.re by linarith)).mono_set
      (Ioi_subset_Ioi zero_le_one)
    refine hm.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [psiErr, indicator_of_mem ht, smul_eq_mul]
    ring_nf
  have hsplit : EqOn (fun t : ℝ => ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ => (t : ℂ) ^ (-s) +
        (t : ℂ) ^ (-(s + 1)) * ((Chebyshev.psi t - t : ℝ) : ℂ)) (Ioi 1) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      have : (0 : ℝ) < t := lt_trans one_pos ht
      exact_mod_cast this.ne'
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = 1 + -(s + 1) by ring, cpow_add _ _ ht0, cpow_one]
    simp only
    rw [hpow]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hI1 hI2,
    integral_Ioi_cpow_of_lt hs0 one_pos, ← mellin_psiErr_eq]
  have hs1 : s - 1 ≠ 0 := by
    intro h0
    have : s = 1 := by linear_combination h0
    rw [this] at hs; simp at hs
  have hs1' : -s + 1 ≠ 0 := by
    intro h0; apply hs1; linear_combination -h0
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

/-- **Ingham (easy direction).** If `ψ(x) - x = O(x^θ)`, then `ζ` has no zeros with
`Re s > θ`. -/
theorem zeroFreeRight_of_psiError {θ : ℝ} (h : PsiError θ) : ZeroFreeRight θ := by
  by_cases hθ : 1 ≤ θ
  · exact zeroFreeRight_one.mono hθ
  push Not at hθ
  refine zeroFreeRight_of_eqOn (G := fun s => s / (s - 1) + s * mellin psiErr (-s)) ?_ ?_
  · intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => z / (z - 1)) s :=
      differentiableAt_id.div (differentiableAt_id.sub_const 1) hs1
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => z * mellin psiErr (-z)) s :=
      differentiableAt_id.mul (differentiableAt_mellin_psiErr h hs.1)
    exact (hd1.add hd2).differentiableWithinAt
  · intro s hs
    exact (LSeries_vonMangoldt_eq_mellin hθ h hs).symm.trans
      (LSeries_vonMangoldt_eq_negLogDerivZeta hs)

/-- The `ε`-version: an error term `O(x^{θ+ε})` for every `ε > 0` already gives
`ZeroFreeRight θ`. -/
theorem zeroFreeRight_of_forall_psiError {θ : ℝ} (h : ∀ ε > 0, PsiError (θ + ε)) :
    ZeroFreeRight θ := by
  intro s hs
  have hε : 0 < (s.re - θ) / 2 := by linarith
  exact zeroFreeRight_of_psiError (h _ hε) s (by linarith)

/-- **Square-root error in the prime number theorem implies RH.** If
`ψ(x) = x + O(x^{1/2 + ε})` for every `ε > 0`, the Riemann hypothesis holds. (The converse is
von Koch's theorem, 1901, which is the hard direction and is not formalised here.) -/
theorem riemannHypothesis_of_psiError (h : ∀ ε > 0, PsiError (1 / 2 + ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_zeroFreeRight_half (zeroFreeRight_of_forall_psiError h)

/-- Any power saving `θ < 1` in the prime number theorem gives a quasi-Riemann hypothesis. -/
theorem quasiRiemannHypothesis_of_psiError {θ : ℝ} (hθ : θ < 1) (h : PsiError θ) :
    QuasiRiemannHypothesis :=
  ⟨θ, hθ, zeroFreeRight_of_psiError h⟩

end QuasiRH
