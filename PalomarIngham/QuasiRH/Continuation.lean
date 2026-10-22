module

public import PalomarIngham.QuasiRH.Characterisation

/-!
# Any holomorphic continuation of `∑ Λ(n) n^{-s}` forces a zero-free region

`QuasiRH.Characterisation` says: `ζ` is zero-free right of `θ` iff the *specific* function
`negLogDerivZeta = -ζ'/ζ` is holomorphic on `region θ = {θ < Re s, s ≠ 1}`.

In practice one never has `-ζ'/ζ` itself in hand on the left of `Re s = 1`. One has *some*
formula `G(s)` — an integral, a series — which is holomorphic on `region θ` and agrees with
the prime series `∑ Λ(n) n^{-s} = -ζ'/ζ` on `Re s > 1`. This file proves that this already
suffices:

  `G` holomorphic on `region θ`, `G = -ζ'/ζ` on `Re s > 1`  ⟹  `ZeroFreeRight θ`.

## Proof idea

1. `ζ · G` and `-ζ'` are holomorphic on `region θ` and agree on `Re s > 1`. The region is
   connected (a half-plane with one point removed), so by the identity theorem they agree on
   the whole region.
2. Near a putative zero `ρ`, the zeros of `ζ` are isolated, so on a punctured neighbourhood
   `G = -ζ'/ζ`. Hence `G` and `-ζ'/ζ` have the same meromorphic order at `ρ`.
3. `G` is holomorphic at `ρ` (order `≥ 0`), but `-ζ'/ζ` has a simple pole there (order `-1`,
   `Characterisation.meromorphicOrderAt_negLogDerivZeta`). Contradiction.
-/

@[expose] public section


open Complex Filter Topology Set

namespace QuasiRH

/-- `region θ = {θ < Re s} \ {1}` is (pre)connected. We cover it by four convex pieces:
upper half, lower half, the part right of `Re s = 1`, and the strip `θ < Re s < 1`. -/
theorem isPreconnected_region (θ : ℝ) : IsPreconnected (region θ) := by
  set A := {s : ℂ | θ < s.re} ∩ {s : ℂ | 0 < s.im}
  set B := {s : ℂ | θ < s.re} ∩ {s : ℂ | s.im < 0}
  set C := {s : ℂ | θ < s.re} ∩ {s : ℂ | 1 < s.re}
  set D := {s : ℂ | θ < s.re} ∩ {s : ℂ | s.re < 1}
  have cA : IsPreconnected A := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have cB : IsPreconnected B := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have cC : IsPreconnected C := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_gt 1)).isPreconnected
  have cD : IsPreconnected D := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_lt 1)).isPreconnected
  set a : ℝ := max θ 1 + 1
  have ha1 : θ < a := by simp only [a]; linarith [le_max_left θ 1]
  have ha2 : 1 < a := by simp only [a]; linarith [le_max_right θ 1]
  have hAC : IsPreconnected (A ∪ C) :=
    cA.union (⟨a, 1⟩ : ℂ) ⟨ha1, by norm_num⟩ ⟨ha1, ha2⟩ cC
  have hACB : IsPreconnected (A ∪ C ∪ B) :=
    hAC.union (⟨a, -1⟩ : ℂ) (Or.inr ⟨ha1, ha2⟩) ⟨ha1, by norm_num⟩ cB
  have hcover : region θ = A ∪ C ∪ B ∪ D := by
    ext s
    simp only [region, A, B, C, D, mem_ofPred_eq, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy s.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨h1, him⟩)
      · rcases lt_trichotomy s.re 1 with hre | hre | hre
        · exact Or.inr ⟨h1, hre⟩
        · exact absurd (Complex.ext (by simpa using hre) (by simpa using him)) h2
        · exact Or.inl (Or.inl (Or.inr ⟨h1, hre⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨h1, him⟩))
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> refine ⟨h1, ?_⟩ <;>
        rintro rfl <;> simp at h2
  rw [hcover]
  by_cases hθ : θ < 1
  · exact hACB.union (⟨(θ + 1) / 2, 1⟩ : ℂ)
      (Or.inl (Or.inl ⟨by simp; linarith, by norm_num⟩)) ⟨by simp; linarith, by simp; linarith⟩ cD
  · have hD : D = ∅ := by
      ext s; simp only [D, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩; exact hθ (h1.trans h2)
    rw [hD, union_empty]; exact hACB

/-- **Continuation forces a zero-free region.** If some `G` is holomorphic on
`{θ < Re s, s ≠ 1}` and agrees with `-ζ'/ζ = ∑ Λ(n) n^{-s}` on `Re s > 1`, then `ζ` has no
zeros with `Re s > θ`. -/
theorem zeroFreeRight_of_eqOn {θ : ℝ} {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (region θ))
    (hEq : EqOn G negLogDerivZeta {s | 1 < s.re}) : ZeroFreeRight θ := by
  intro ρ hρ hzero
  by_cases hρ1 : ρ = 1
  · subst hρ1; exact riemannZeta_one_ne_zero hzero
  have hρR : ρ ∈ region θ := ⟨hρ, hρ1⟩
  have hanG : AnalyticOnNhd ℂ G (region θ) := hG.analyticOnNhd (isOpen_region θ)
  have hζ : AnalyticOnNhd ℂ riemannZeta (region θ) := fun s hs => analyticAt_riemannZeta hs.2
  have hζ' : AnalyticOnNhd ℂ (deriv riemannZeta) (region θ) := fun s hs =>
    (analyticAt_riemannZeta hs.2).deriv
  -- a base point to the right of `Re s = 1`
  set a : ℂ := ((max θ 1 + 1 : ℝ) : ℂ)
  have hare : a.re = max θ 1 + 1 := by simp [a]
  have ha1 : 1 < a.re := by rw [hare]; linarith [le_max_right θ 1]
  have ha : a ∈ region θ := by
    refine ⟨by rw [hare]; linarith [le_max_left θ 1], ?_⟩
    intro h; rw [h] at ha1; simp at ha1
  -- step 1: `ζ · G = -ζ'` on the region (identity theorem)
  have hev : (fun s => riemannZeta s * G s) =ᶠ[𝓝 a] (fun s => -deriv riemannZeta s) := by
    have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 a :=
      (isOpen_lt continuous_const continuous_re).mem_nhds ha1
    filter_upwards [hopen] with s hs
    have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
    rw [hEq hs, negLogDerivZeta]
    field_simp
  have hid : EqOn (fun s => riemannZeta s * G s) (fun s => -deriv riemannZeta s) (region θ) :=
    (hζ.mul hanG).eqOn_of_preconnected_of_eventuallyEq hζ'.neg (isPreconnected_region θ) ha hev
  -- step 2: on a punctured neighbourhood of `ρ`, `G = -ζ'/ζ`
  have hne : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 := by
    refine (analyticAt_riemannZeta hρ1).eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
    intro h
    exact riemannZeta_not_eventually_zero hρ1 h
  have hreg : ∀ᶠ s in 𝓝[≠] ρ, s ∈ region θ :=
    nhdsWithin_le_nhds ((isOpen_region θ).mem_nhds hρR)
  have hpunct : G =ᶠ[𝓝[≠] ρ] negLogDerivZeta := by
    filter_upwards [hne, hreg] with s hs hsR
    have h := hid hsR
    simp only at h
    rw [negLogDerivZeta, ← h]
    field_simp
  -- step 3: orders disagree
  have hnonneg := (hanG ρ hρR).meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hpunct, meromorphicOrderAt_negLogDerivZeta hρ1 hzero] at hnonneg
  exact absurd hnonneg (by decide)

end QuasiRH
