module

public import PalomarIngham.QuasiRH.Basic

/-!
# The Riemann hypothesis is exactly `ZeroFreeRight (1/2)`

`QuasiRH.Basic` proved `RH ⇒ ZeroFreeRight (1/2)`. The converse uses the functional equation
`ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)` (Mathlib's `riemannZeta_one_sub`): a non-trivial
zero `ρ` with `Re ρ < 1/2` reflects to a zero `1 - ρ` with `Re (1 - ρ) > 1/2`. So a zero-free
half-plane `Re s > 1/2` automatically clears the mirror strip `Re s < 1/2` too, leaving only
the critical line.

The one subtlety is the factor `cos(π(1-ρ)/2)`: it vanishes exactly when `ρ` is an even
integer `≤ 0`, i.e. `ρ = 0` (but `ζ(0) = -1/2 ≠ 0`) or a trivial zero `-2, -4, …` (excluded by
the statement of `RiemannHypothesis`).
-/

@[expose] public section


open Complex
open scoped Real

namespace QuasiRH

/-- **Reflection.** `ZeroFreeRight (1/2)` implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_zeroFreeRight_half (h : ZeroFreeRight (1 / 2)) :
    RiemannHypothesis := by
  intro ρ hz htriv _h1
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hρ0 : ρ ≠ 0 := by
      rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
    have hre : (1 / 2 : ℝ) < (1 - ρ).re := by simp; linarith
    have hs : ∀ n : ℕ, 1 - ρ ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs' : 1 - ρ ≠ 1 := by
      intro h'; apply hρ0; linear_combination -h'
    have hfe := riemannZeta_one_sub hs hs'
    rw [sub_sub_cancel, hz] at hfe
    have hG : Gamma (1 - ρ) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hZ : riemannZeta (1 - ρ) ≠ 0 := h _ hre
    have hP : (2 * (π : ℂ)) ^ (-(1 - ρ)) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]
      exact fun h' => by
        have : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
        exact this h'.1
    have hC : cos (π * (1 - ρ) / 2) ≠ 0 := by
      intro hc
      obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
      have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have hρk : ρ = -2 * (k : ℂ) := by
        have h2 : (π : ℂ) * (1 - ρ) = (π : ℂ) * (2 * k + 1) := by linear_combination 2 * hk
        have h3 := mul_left_cancel₀ hpi h2
        linear_combination -h3
      have hkre : ρ.re = -2 * k := by rw [hρk]; simp
      have hk0 : 0 ≤ k := by
        by_contra hneg; push Not at hneg
        have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        linarith
      rcases eq_or_lt_of_le hk0 with hk0 | hk1
      · apply hρ0; rw [hρk, ← hk0]; simp
      · apply htriv
        refine ⟨(k - 1).toNat, ?_⟩
        have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
        have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
          have := congrArg (fun z : ℤ => (z : ℂ)) this
          push_cast at this
          exact this
        rw [hρk, hc]; ring
    have : (2 : ℂ) * (2 * π) ^ (-(1 - ρ)) * Gamma (1 - ρ) * cos (π * (1 - ρ) / 2) *
        riemannZeta (1 - ρ) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hP) hG) hC) hZ
    exact this hfe.symm
  · exact heq
  · exact absurd hz (h ρ hgt)

/-- **RH, as a zero-free half-plane.** -/
theorem riemannHypothesis_iff_zeroFreeRight_half :
    RiemannHypothesis ↔ ZeroFreeRight (1 / 2) :=
  ⟨zeroFreeRight_half_of_RH, riemannHypothesis_of_zeroFreeRight_half⟩

/-- **RH is the quasi-Riemann hypothesis with the optimal exponent.** No `θ < 1/2` is possible
(there are zeros on the critical line), so `θ = 1/2` is the best one can ask for. -/
theorem riemannHypothesis_iff_exists_le_half :
    RiemannHypothesis ↔ ∃ θ : ℝ, θ ≤ 1 / 2 ∧ ZeroFreeRight θ :=
  ⟨fun h => ⟨1 / 2, le_rfl, zeroFreeRight_half_of_RH h⟩,
   fun ⟨_, hθ, hz⟩ => riemannHypothesis_of_zeroFreeRight_half (hz.mono hθ)⟩

end QuasiRH
