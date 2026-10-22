module

public import PalomarIngham.Vendor.PNT.MediumPNT

/-!
# Ingham's theorem, hard direction — interfaces

Target: if `ζ(s) ≠ 0` for `Re s > θ` (with `1/2 ≤ θ < 1`), then `ψ(x) = x + O(x^{θ+δ})` for
every `δ > 0`.

Strategy (PrimeNumberTheoremAnd's `MediumPNT`, with the contour moved to a *straight* line):

1. `ψ_ε(X)` = smoothed Chebyshev function (PNT+ `SmoothedChebyshev`), with
   `|ψ(X) - ψ_ε(X)| ≪ ε X log X` (PNT+ `SmoothedChebyshevClose`).
2. `ψ_ε(X) = X·𝓜(1) + I₁ - I₂ + I₃₇ + I₈ + I₉` (PNT+ `SmoothedChebyshevPull1`), shifting the line
   of integration from `Re s = 1 + 1/log X` to `Re s = σ₁ ∈ (θ, 1)`.
3. Bounds: `I₁, I₉ ≪ X log X/(εT)` (PNT+); `I₂, I₈ ≪ X log T/(εT²)` and
   `I₃₇ ≪ X^{σ₁} ε^{-κ}` (this project), using `ζ'/ζ(σ + it) ≪ log |t|` for `σ ≥ σ₁`
   (this project, Borel–Carathéodory) — this is the only place the zero-free hypothesis is used
   quantitatively.
4. Choose `ε = X^{σ₁ - 1}`, `T = X²`.

This file fixes the interfaces (as `Prop`s) so the pieces can be proved independently.
-/

@[expose] public section


open Set Function Filter Complex Real Asymptotics MeasureTheory


namespace Ingham

/-- No zeros of `ζ` with `Re s > θ`. (Same as `QuasiRH.ZeroFreeRight` in `../Formal`.) -/
def ZeroFreeRight (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- `ψ(x) - x = O(x^θ)`. (Same as `QuasiRH.PsiError` in `../Formal`.) -/
def PsiError (θ : ℝ) : Prop :=
  (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ θ)

/-- The standard hypotheses on the smoothing bump `ν` used throughout PNT+'s `MediumPNT`. -/
def SmoothingData (ν : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 ν ∧ (∀ x > 0, 0 ≤ ν x) ∧ ν.support ⊆ Icc (1 / 2) 2 ∧
    ∫ x in Ioi 0, ν x / x = 1

/-- **Step A target.** `|ζ'/ζ(σ + it)| ≤ K log |t|` for `σ₁ ≤ σ ≤ 2`, `|t| ≥ 3`. -/
def LogDerivLogBound (σ₁ : ℝ) : Prop :=
  ∃ K > 0, ∀ σ t : ℝ, σ₁ ≤ σ → σ ≤ 2 → 3 ≤ |t| →
    ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ K * Real.log |t|

/-- **Step B target (vertical piece).** -/
def I37BoundProp (ν : ℝ → ℝ) (σ₁ κ : ℝ) : Prop :=
  ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    ‖I₃₇ ν ε T X σ₁‖ ≤ C * X ^ σ₁ * ε ^ (-κ)

/-- **Step B target (lower horizontal piece).** -/
def I2BoundProp (ν : ℝ → ℝ) (σ₁ : ℝ) : Prop :=
  ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    ‖I₂ ν ε T X σ₁‖ ≤ C * X * Real.log T / (ε * T ^ 2)

/-- **Step B target (upper horizontal piece).** -/
def I8BoundProp (ν : ℝ → ℝ) (σ₁ : ℝ) : Prop :=
  ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ X : ℝ, 3 < X → ∀ T : ℝ, 3 < T →
    ‖I₈ ν ε T X σ₁‖ ≤ C * X * Real.log T / (ε * T ^ 2)

end Ingham
