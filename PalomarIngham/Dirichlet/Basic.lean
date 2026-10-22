module

public import PalomarIngham.Ingham.Basic

/-!
# Ingham's theorem for Dirichlet `L`-functions — interfaces

Target (`χ ≠ 1` a Dirichlet character mod `q`): if `L(s, χ) ≠ 0` for `Re s > θ` with
`1/2 ≤ θ < 1`, then `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n) = O(x^{θ+δ})` for every `δ > 0`.
With OpenAI's Dirichlet theorem (`θ = 7/8`) and orthogonality of characters this gives the prime
number theorem in arithmetic progressions with error `O(x^{7/8+δ})`.

The proof mirrors the `ζ` case (`PalomarIngham/Ingham/`), with `-L'/L` in place of `-ζ'/ζ`; since
`χ ≠ 1`, `L(s, χ)` is entire and there is no main term (no pole at `s = 1`).

This file fixes the definitions and the target `Prop`s so that the pieces can be proved
independently.
-/

@[expose] public section

open Set Function Filter Complex Real Asymptotics MeasureTheory

namespace InghamL

variable {q : ℕ} [NeZero q]

/-- No zeros of `L(s, χ)` with `Re s > θ`. -/
def ZeroFreeRightL (χ : DirichletCharacter ℂ q) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction χ s ≠ 0

/-- The twisted Chebyshev function `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
noncomputable def psiChi (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- `ψ(x, χ) = O(x^θ)`. -/
def PsiChiError (χ : DirichletCharacter ℂ q) (θ : ℝ) : Prop :=
  psiChi χ =O[atTop] (fun x : ℝ => x ^ θ)

/-- `|L'/L(σ + it, χ)| ≤ K log |t|` for `σ₁ ≤ σ ≤ 2`, `|t| ≥ 3`. -/
def LogDerivLBound (χ : DirichletCharacter ℂ q) (σ₁ : ℝ) : Prop :=
  ∃ K > 0, ∀ σ t : ℝ, σ₁ ≤ σ → σ ≤ 2 → 3 ≤ |t| →
    ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
      DirichletCharacter.LFunction χ (σ + t * I)‖ ≤ K * Real.log |t|

/-- The smoothed integrand `-L'/L(s, χ) · 𝓜(1̃_ε)(s) · X^s`. -/
noncomputable abbrev IntegrandL (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε X : ℝ) : ℂ → ℂ :=
  fun s ↦ (-deriv (DirichletCharacter.LFunction χ) s) / DirichletCharacter.LFunction χ s *
    mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

/-- The smoothed twisted Chebyshev function, as a vertical integral on `Re s = 1 + 1/log X`. -/
noncomputable def SmoothedChebyshevL (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε X : ℝ) : ℂ :=
  VerticalIntegral' (IntegrandL χ ν ε X) ((1 : ℝ) + (Real.log X)⁻¹)

/-- Contour pieces (same shapes as PNT+'s `I₁ … I₉`). -/
noncomputable def J₁ (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T), IntegrandL χ ν ε X ((1 + (Real.log X)⁻¹) + t * I)))
noncomputable def J₂ (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹), IntegrandL χ ν ε X (σ - T * I)))
noncomputable def J₃₇ (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T, IntegrandL χ ν ε X (σ₁ + t * I)))
noncomputable def J₈ (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹), IntegrandL χ ν ε X (σ + T * I)))
noncomputable def J₉ (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T, IntegrandL χ ν ε X ((1 + (Real.log X)⁻¹) + t * I)))

/-- **Smoothing error.** -/
def CloseProp (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) : Prop :=
  ∃ C > 0, ∀ X : ℝ, 3 < X → ∀ ε : ℝ, 0 < ε → ε < 1 → 2 < X * ε →
    ‖SmoothedChebyshevL χ ν ε X - psiChi χ X‖ ≤ C * ε * X * Real.log X

/-- **Contour shift** (no residue: `L(s, χ)` is entire for `χ ≠ 1`). -/
def ShiftProp (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (σ₁ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    SmoothedChebyshevL χ ν ε X =
      J₁ χ ν ε X T - J₂ χ ν ε T X σ₁ + J₃₇ χ ν ε T X σ₁ + J₈ χ ν ε T X σ₁ + J₉ χ ν ε X T

/-- **Far vertical pieces.** -/
def J19BoundProp (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) : Prop :=
  ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    ‖J₁ χ ν ε X T‖ ≤ C * X * Real.log X / (ε * T) ∧ ‖J₉ χ ν ε X T‖ ≤ C * X * Real.log X / (ε * T)

/-- **Shifted vertical piece.** -/
def J37BoundProp (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (σ₁ κ : ℝ) : Prop :=
  ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    ‖J₃₇ χ ν ε T X σ₁‖ ≤ C * X ^ σ₁ * ε ^ (-κ)

/-- **Horizontal pieces.** -/
def J28BoundProp (χ : DirichletCharacter ℂ q) (ν : ℝ → ℝ) (σ₁ : ℝ) : Prop :=
  ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    ‖J₂ χ ν ε T X σ₁‖ ≤ C * X * Real.log T / (ε * T ^ 2) ∧
    ‖J₈ χ ν ε T X σ₁‖ ≤ C * X * Real.log T / (ε * T ^ 2)

end InghamL
