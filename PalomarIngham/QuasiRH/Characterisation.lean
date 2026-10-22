module

public import PalomarIngham.QuasiRH.Basic

/-!
# Zero-free half-planes are *exactly* where `-ζ'/ζ` is holomorphic

`QuasiRH.Basic` proves one direction: no zeros right of `θ` ⇒ `-ζ'/ζ` (which is the von
Mangoldt series `∑ Λ(n) n^{-s}` on `Re s > 1`) is holomorphic on `{θ < Re s, s ≠ 1}`.

This file proves the converse, so the link is a characterisation:

  `ZeroFreeRight θ  ↔  DifferentiableOn ℂ (-ζ'/ζ) {θ < Re s, s ≠ 1}`.

## Why the converse holds, in one paragraph

Near a zero `ρ` of order `m ≥ 1`, write `ζ(s) = (s - ρ)^m g(s)` with `g(ρ) ≠ 0`. Then
`ζ'/ζ = m/(s - ρ) + g'/g`: a *simple pole with residue `m`*. A function with a pole is not
holomorphic, so `-ζ'/ζ` cannot be holomorphic at `ρ`. Two things make this rigorous:

* `ζ` has a zero of **finite** order at `ρ`, i.e. it is not identically zero near `ρ`. This is
  the identity theorem: `ζ` is analytic on the connected set `ℂ \ {1}` and `ζ(2) ≠ 0`.
* Mathlib's `meromorphicOrderAt_logDeriv_eq_neg_one`: the logarithmic derivative of a
  meromorphic function has order exactly `-1` at each of its zeros and poles.

Everything is sorry-free (checked by `#print axioms` in `Audit.lean`).
-/

@[expose] public section


open Complex Filter Topology

namespace QuasiRH

/-- `ζ` is analytic at every point other than its pole `s = 1`. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  differentiableOn_riemannZeta.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- `ℂ \ {1}` is connected (removing a point from the plane does not disconnect it). -/
theorem isPreconnected_compl_one : IsPreconnected ({1}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected

/-- `ζ` is not identically zero near any point `s ≠ 1`: otherwise, by the identity theorem on
the connected set `ℂ \ {1}`, it would vanish everywhere there, but `ζ(2) = π²/6 ≠ 0`. -/
theorem riemannZeta_not_eventually_zero {s : ℂ} (hs : s ≠ 1) :
    ¬ (riemannZeta =ᶠ[𝓝 s] 0) := by
  intro h
  have hzero := (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton
    ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_compl_one hs h
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  exact riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num) (by simpa using hzero h2)

/-- `-ζ'/ζ` is minus the logarithmic derivative of `ζ`. -/
theorem negLogDerivZeta_eq : negLogDerivZeta = -(logDeriv riemannZeta) := by
  funext s
  simp [negLogDerivZeta, logDeriv_apply, neg_div]

/-- **At a zero of `ζ`, `-ζ'/ζ` has a simple pole** (meromorphic order `-1`). -/
theorem meromorphicOrderAt_negLogDerivZeta {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : riemannZeta ρ = 0) :
    meromorphicOrderAt negLogDerivZeta ρ = -1 := by
  have han := analyticAt_riemannZeta hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han, hρ⟩
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := fun h =>
    riemannZeta_not_eventually_zero hρ1 (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne0 (by rw [← hn]; simp)
  have hord : meromorphicOrderAt riemannZeta ρ = (n : ℤ) := by
    rw [han.meromorphicOrderAt_eq, ← hn, ENat.map_natCast]
  rw [negLogDerivZeta_eq, ← meromorphicOrderAt_neg]
  refine meromorphicOrderAt_logDeriv_eq_neg_one han.meromorphicAt ?_ ?_ <;> rw [hord]
  · exact_mod_cast hn0
  · exact WithTop.coe_ne_top

/-- Consequently `-ζ'/ζ` is not holomorphic at any zero of `ζ`. -/
theorem not_analyticAt_negLogDerivZeta {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : riemannZeta ρ = 0) :
    ¬ AnalyticAt ℂ negLogDerivZeta ρ := by
  intro h
  have hnonneg := h.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_negLogDerivZeta hρ1 hρ] at hnonneg
  exact absurd hnonneg (by decide)

/-- **The converse of the von Mangoldt link.** If `-ζ'/ζ` is holomorphic on
`{θ < Re s, s ≠ 1}`, then `ζ` has no zeros right of `θ`. (At `s = 1` itself there is nothing to
prove: Mathlib's value `ζ(1) = (γ - log 4π)/2` is nonzero.) -/
theorem zeroFreeRight_of_differentiableOn {θ : ℝ}
    (h : DifferentiableOn ℂ negLogDerivZeta (region θ)) : ZeroFreeRight θ := by
  intro s hs hzero
  by_cases hs1 : s = 1
  · subst hs1
    exact riemannZeta_one_ne_zero hzero
  exact not_analyticAt_negLogDerivZeta hs1 hzero
    (h.analyticAt ((isOpen_region θ).mem_nhds ⟨hs, hs1⟩))

/-- **Characterisation.** `ζ` is zero-free right of `θ` if and only if `-ζ'/ζ` — the analytic
form of the prime-counting series `∑ Λ(n) n^{-s}` — is holomorphic on `{θ < Re s, s ≠ 1}`. -/
theorem zeroFreeRight_iff_differentiableOn (θ : ℝ) :
    ZeroFreeRight θ ↔ DifferentiableOn ℂ negLogDerivZeta (region θ) :=
  ⟨differentiableOn_negLogDerivZeta, zeroFreeRight_of_differentiableOn⟩

/-- **OpenAI's theorem, restated about primes.** OpenAI's statement is *equivalent* to the
holomorphy of `-ζ'/ζ` on `{7/8 < Re s, s ≠ 1}`. -/
theorem openAIStatement_iff_differentiableOn :
    OpenAIStatement ↔ DifferentiableOn ℂ negLogDerivZeta (region (7 / 8)) :=
  openAIStatement_iff.trans (zeroFreeRight_iff_differentiableOn _)

/-- **The quasi-Riemann hypothesis, restated about primes.** -/
theorem quasiRiemannHypothesis_iff :
    QuasiRiemannHypothesis ↔
      ∃ θ : ℝ, θ < 1 ∧ DifferentiableOn ℂ negLogDerivZeta (region θ) := by
  simp only [QuasiRiemannHypothesis, zeroFreeRight_iff_differentiableOn]

end QuasiRH
