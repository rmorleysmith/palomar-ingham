module

public import Mathlib

/-!
# Primes in arithmetic progressions with a power-saving error term, from zero-free half-planes

For a modulus `q ≥ 1` and a residue `a` coprime to `q`, write
`ψ(x; q, a) = ∑_{n ≤ x, n ≡ a mod q} Λ(n)`.

* `psi_ap_error_of_zero_free` — if `ζ(s)` and every `L(s, χ)` with `χ` a nontrivial Dirichlet
  character mod `q` have no zeros with `Re s > θ` (`1/2 ≤ θ < 1`), then
  `ψ(x; q, a) = x/φ(q) + O(x^{θ+δ})` for every `δ > 0`.
* `psi_ap_error_of_seven_eighths` — under OpenAI's 2026 theorem (stated **as a hypothesis**,
  verbatim as in their comparator challenge `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`),
  `ψ(x; q, a) = x/φ(q) + O(x^{7/8+δ})` for every fixed `q`, unit `a`, and `δ > 0`.

No new definitions are introduced.
-/

@[expose] public section

open Filter Asymptotics

namespace PalomarInghamAP

theorem psi_ap_error_of_zero_free {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (hζ : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0)
    (hL : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ∀ δ : ℝ, 0 < δ →
      (fun x : ℝ => (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = a),
          ArithmeticFunction.vonMangoldt n) - x / q.totient) =O[atTop]
        (fun x : ℝ => x ^ (θ + δ)) := by
  sorry

theorem psi_ap_error_of_seven_eighths
    (h : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}, (7 / 8 : ℝ) < s.re →
      ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∀ δ : ℝ, 0 < δ →
      (fun x : ℝ => (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = a),
          ArithmeticFunction.vonMangoldt n) - x / q.totient) =O[atTop]
        (fun x : ℝ => x ^ (7 / 8 + δ)) := by
  sorry

end PalomarInghamAP
