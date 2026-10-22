module

public import Mathlib

/-!
# Zero-free half-planes for `ζ` and the von Mangoldt `L`-series

This file is the first brick of a formalisation that builds on OpenAI's claimed
*quasi-Riemann hypothesis* (October 2026): that `ζ s ≠ 0` whenever `7/8 < Re s`.

## The idea, in one paragraph

The primes enter analysis through the von Mangoldt function `Λ`, via the identity
`∑ Λ(n) n^{-s} = -ζ'(s)/ζ(s)` for `Re s > 1`. The left side is an arithmetic object (it
"counts primes"); the right side is analytic, and it is singular exactly where `ζ` has a
zero (or at the pole `s = 1`). So **where `ζ` has no zeros, the prime-counting series
`∑ Λ(n) n^{-s}` continues holomorphically.** A zero-free half-plane `Re s > θ` therefore
says: the prime series behaves well all the way down to `θ`. This is the bridge from
"where are the zeros of `ζ`" to "how regular are the primes".

## What is in this file

* `ZeroFreeRight θ` — `ζ` has no zeros with `θ < Re s`.
* `QuasiRiemannHypothesis` — the classical open problem: `ZeroFreeRight θ` for *some* `θ < 1`.
* `OpenAIStatement` — OpenAI's theorem, copied verbatim from their comparator challenge
  `ComparatorChallenges/QuasiRiemannHypothesis.lean` in `openai/math`. We take it as a
  *hypothesis*, so every result here is proved from it, not assumed true.
* Basic facts: monotonicity, `ZeroFreeRight 1` (from Mathlib, de la Vallée Poussin),
  `RH → ZeroFreeRight (1/2)`.
* **The von Mangoldt link:** `ZeroFreeRight θ` implies that `-ζ'/ζ` is holomorphic on
  `{θ < Re s, s ≠ 1}` and agrees with `∑ Λ(n) n^{-s}` on `Re s > 1`, i.e. the von Mangoldt
  `L`-series continues analytically to that region.

Everything is sorry-free. Nothing here proves a new zero-free region; it proves what such a
region *buys*.

## Correspondence with the HSLN corpus

The corpus' "the Lie derivative gives the primes" (`D(ζ)·μ = Λ`, i.e. `log * μ = Λ` in the
Dirichlet ring) is the arithmetic shadow of `-ζ'/ζ = L(Λ)`: under `L`, multiplying a
coefficient by `log n` becomes `-d/ds`, and Dirichlet-inverting `ζ` (which is `μ`) becomes
dividing by `ζ`. Mathlib's `ArithmeticFunction.log_mul_moebius_eq_vonMangoldt` is the
arithmetic side and `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` the
analytic side; this file is about what happens *beyond* `Re s > 1`, where only the analytic
side makes sense.
-/

@[expose] public section


open Complex ArithmeticFunction
open scoped LSeries.notation

namespace QuasiRH

/-! ## Zero-free half-planes -/

/-- `ζ` has no zeros in the open half-plane to the right of `θ`. -/
def ZeroFreeRight (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- The **quasi-Riemann hypothesis**: `ζ` is zero-free in *some* half-plane `Re s > θ` with
`θ < 1`. (The Riemann hypothesis is the case `θ = 1/2`; before October 2026 no `θ < 1` was
known.) -/
def QuasiRiemannHypothesis : Prop :=
  ∃ θ : ℝ, θ < 1 ∧ ZeroFreeRight θ

/-- A zero-free half-plane stays zero-free if you shrink it. -/
theorem ZeroFreeRight.mono {θ θ' : ℝ} (h : θ ≤ θ') (hz : ZeroFreeRight θ) :
    ZeroFreeRight θ' :=
  fun s hs => hz s (lt_of_le_of_lt h hs)

/-- The classical theorem (Hadamard, de la Vallée Poussin, 1896): `ζ` has no zeros with
`Re s ≥ 1`, so in particular none with `Re s > 1`. Supplied by Mathlib. -/
theorem zeroFreeRight_one : ZeroFreeRight 1 :=
  fun _ hs => riemannZeta_ne_zero_of_one_le_re hs.le

/-- The Riemann hypothesis gives the zero-free half-plane `Re s > 1/2`.

The only work is to check that a zero with `Re s > 1/2` is neither a trivial zero
(those have `Re s < 0`) nor the point `s = 1` (where Mathlib's `ζ 1` is a nonzero junk
value), so the hypothesis applies and forces `Re s = 1/2`, a contradiction. -/
theorem zeroFreeRight_half_of_RH (hRH : RiemannHypothesis) : ZeroFreeRight (1 / 2) := by
  intro s hs hzero
  have hnontriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    simp at hs
    linarith
  have hne : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hzero
  have := hRH s hzero hnontriv hne
  linarith

theorem quasiRiemannHypothesis_of_RH (hRH : RiemannHypothesis) : QuasiRiemannHypothesis :=
  ⟨1 / 2, by norm_num, zeroFreeRight_half_of_RH hRH⟩

/-! ## OpenAI's statement -/

/-- OpenAI's quasi-Riemann hypothesis, verbatim from the comparator challenge
`ComparatorChallenges/QuasiRiemannHypothesis.lean` in `github.com/openai/math`
(proof: `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, Lean v4.34.1, mathlib `d13f23b`). -/
def OpenAIStatement : Prop :=
  ∀ {s : ℂ}, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

theorem openAIStatement_iff : OpenAIStatement ↔ ZeroFreeRight (7 / 8) :=
  ⟨fun h _ hs => h hs, fun h _ hs => h _ hs⟩

/-- OpenAI's theorem is an instance of the quasi-Riemann hypothesis, with `θ = 7/8`. -/
theorem quasiRiemannHypothesis_of_openAI (h : OpenAIStatement) : QuasiRiemannHypothesis :=
  ⟨7 / 8, by norm_num, openAIStatement_iff.mp h⟩

/-! ## The von Mangoldt link -/

/-- The negative logarithmic derivative of `ζ`. For `Re s > 1` it is the von Mangoldt
`L`-series `∑ Λ(n) n^{-s}` (Mathlib: `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). -/
noncomputable def negLogDerivZeta (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- The region where a zero-free half-plane makes `-ζ'/ζ` holomorphic: right of `θ`, minus the
pole of `ζ` at `s = 1`. -/
def region (θ : ℝ) : Set ℂ := {s | θ < s.re ∧ s ≠ 1}

theorem isOpen_region (θ : ℝ) : IsOpen (region θ) :=
  (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton

/-- `ζ` is holomorphic away from its pole at `1`. -/
theorem differentiableOn_riemannZeta : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
  fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- …and therefore so is its derivative (a holomorphic function on an open set has a
holomorphic derivative). -/
theorem differentiableOn_deriv_riemannZeta : DifferentiableOn ℂ (deriv riemannZeta) {1}ᶜ :=
  differentiableOn_riemannZeta.deriv isOpen_compl_singleton

/-- **The von Mangoldt link.** If `ζ` has no zeros right of `θ`, then `-ζ'/ζ` is holomorphic on
`{θ < Re s, s ≠ 1}`. -/
theorem differentiableOn_negLogDerivZeta {θ : ℝ} (hz : ZeroFreeRight θ) :
    DifferentiableOn ℂ negLogDerivZeta (region θ) := by
  have hsub : region θ ⊆ {1}ᶜ := fun _ hs => hs.2
  exact (differentiableOn_deriv_riemannZeta.mono hsub).neg.div
    (differentiableOn_riemannZeta.mono hsub) (fun s hs => hz s hs.1)

/-- On `Re s > 1`, `-ζ'/ζ` *is* the von Mangoldt `L`-series. -/
theorem LSeries_vonMangoldt_eq_negLogDerivZeta {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = negLogDerivZeta s :=
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- **Analytic continuation of the prime-counting series.** If `ζ` has no zeros right of `θ`,
then `∑ Λ(n) n^{-s}` (defined by its Dirichlet series for `Re s > 1`) extends to a function
holomorphic on `{θ < Re s, s ≠ 1}`. -/
theorem vonMangoldt_LSeries_continuation {θ : ℝ} (hz : ZeroFreeRight θ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (region θ) ∧ ∀ s : ℂ, 1 < s.re → L ↗Λ s = F s :=
  ⟨negLogDerivZeta, differentiableOn_negLogDerivZeta hz,
    fun _ hs => LSeries_vonMangoldt_eq_negLogDerivZeta hs⟩

/-- **Building on OpenAI.** Granting OpenAI's theorem, the von Mangoldt `L`-series continues
holomorphically to `{7/8 < Re s, s ≠ 1}`. -/
theorem vonMangoldt_LSeries_continuation_of_openAI (h : OpenAIStatement) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (region (7 / 8)) ∧
      ∀ s : ℂ, 1 < s.re → L ↗Λ s = F s :=
  vonMangoldt_LSeries_continuation (openAIStatement_iff.mp h)

end QuasiRH
