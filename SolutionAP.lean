module

public import Mathlib
public import PalomarIngham.Dirichlet.Main

/-!
# Solution: proofs of the statements in `ChallengeAP.lean`, from `PalomarIngham/Dirichlet/`.
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
        (fun x : ℝ => x ^ (θ + δ)) :=
  fun δ hδ => InghamL.psiAP_error_of_zeroFree ha hθ hθ1 hζ hL δ hδ

theorem psi_ap_error_of_seven_eighths
    (h : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}, (7 / 8 : ℝ) < s.re →
      ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∀ δ : ℝ, 0 < δ →
      (fun x : ℝ => (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = a),
          ArithmeticFunction.vonMangoldt n) - x / q.totient) =O[atTop]
        (fun x : ℝ => x ^ (7 / 8 + δ)) :=
  fun δ hδ => InghamL.psiAP_error_of_openAI h ha δ hδ

end PalomarInghamAP
