module

public import PalomarIngham.Dirichlet.LogDerivBound
public import PalomarIngham.Dirichlet.Smoothing
public import PalomarIngham.Dirichlet.ContourBounds
public import PalomarIngham.Dirichlet.Assembly
public import PalomarIngham.Dirichlet.Progressions
public import PalomarIngham.Ingham.Main

/-!
# Ingham's theorem for Dirichlet `L`-functions and primes in progressions

* `InghamL.psiChiError_of_zeroFree` — `χ ≠ 1`, `L(s, χ) ≠ 0` for `Re s > θ` (`1/2 ≤ θ < 1`) ⇒
  `ψ(x, χ) = O(x^{θ+δ})` for every `δ > 0`.
* `InghamL.psiAP_error_of_zeroFree` — if `ζ` and all `L(s, χ)` mod `q` are zero-free right of
  `θ`, then `ψ(x; q, a) = x/φ(q) + O(x^{θ+δ})` for every unit `a` mod `q`.
* `InghamL.psiAP_error_of_openAI` — OpenAI's Dirichlet theorem (verbatim) ⇒
  `ψ(x; q, a) = x/φ(q) + O(x^{7/8+δ})`: the prime number theorem in arithmetic progressions with
  a power saving, for every fixed modulus.
-/

@[expose] public section

set_option autoImplicit false

open Filter Asymptotics

namespace InghamL

theorem psiChiError_of_zeroFree {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hz : ZeroFreeRightL χ θ) :
    ∀ δ > 0, PsiChiError χ (θ + δ) := by
  have hθ0 : 0 < θ := by linarith
  refine psiChiError_of_bounds χ hθ hθ1 ?_
  intro ν σ₁ κ hν hσ hσ1 hκ hκ1
  have hA := logDerivLBound_of_zeroFree χ hχ hθ hσ hz
  exact ⟨closeProp χ hν, shiftProp χ hχ hσ hσ1 hθ0 hz hν, j19Bound χ hν,
    j37Bound χ hχ hν hσ hσ1 hθ0 hz hA hκ hκ1, j28Bound χ hχ hν hσ hσ1 hθ0 hz hA⟩

theorem psiAP_error_of_zeroFree {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {θ : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hζ : Ingham.ZeroFreeRight θ)
    (hL : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ZeroFreeRightL χ θ) :
    ∀ δ : ℝ, 0 < δ → (fun x : ℝ => psiAP q a x - x / q.totient) =O[atTop] (fun x : ℝ => x ^ (θ + δ)) :=
  fun δ hδ => psiAP_error ha (by linarith) (Ingham.psiError_of_zeroFreeRight hθ hθ1 hζ δ hδ)
    (fun χ hχ => psiChiError_of_zeroFree χ hχ hθ hθ1 (hL χ hχ) δ hδ)

/-- OpenAI's Dirichlet theorem, verbatim from their comparator challenge
`ComparatorChallenges/DirichletSevenEighths.lean` (a hypothesis here). -/
def OpenAIDirichletStatement : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}, (7 / 8 : ℝ) < s.re →
    ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- **Primes in arithmetic progressions with error `O(x^{7/8+δ})`, from OpenAI's theorem.** -/
theorem psiAP_error_of_openAI (h : OpenAIDirichletStatement) {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    ∀ δ : ℝ, 0 < δ → (fun x : ℝ => psiAP q a x - x / q.totient) =O[atTop]
      (fun x : ℝ => x ^ (7 / 8 + δ)) := by
  refine psiAP_error_of_zeroFree (θ := 7 / 8) ha (by norm_num) (by norm_num) ?_ ?_
  · intro s hs
    by_cases hs1 : s = 1
    · subst hs1; exact riemannZeta_one_ne_zero
    · have := h (q := 1) (1 : DirichletCharacter ℂ 1) hs (fun h' => hs1 h'.2)
      simpa [DirichletCharacter.LFunction_modOne_eq] using this
  · intro χ hχ s hs
    exact h χ hs (fun h' => hχ h'.1)

end InghamL
