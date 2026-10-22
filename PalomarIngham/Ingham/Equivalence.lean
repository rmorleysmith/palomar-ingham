module

public import PalomarIngham.Ingham.Main
public import PalomarIngham.QuasiRH.InghamEasy

/-!
# Ingham's theorem as an equivalence

Combining the easy direction (`../Formal`, `QuasiRH.zeroFreeRight_of_forall_psiError`: regular
primes ⇒ no zeros) with the hard direction (`Ingham.psiError_of_zeroFreeRight`: no zeros ⇒
regular primes):

  for `1/2 ≤ θ < 1`:  `ζ(s) ≠ 0 for Re s > θ`  ⟺  `ψ(x) = x + O(x^{θ+δ})` for every `δ > 0`.

At `θ = 1/2` this is the classical **RH ⟺ ψ(x) = x + O(x^{1/2+δ}) for all δ > 0**.
-/

@[expose] public section


namespace Ingham

theorem zeroFreeRight_iff_psiError {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    ZeroFreeRight θ ↔ ∀ δ > 0, PsiError (θ + δ) :=
  ⟨psiError_of_zeroFreeRight hθ hθ1, fun h => QuasiRH.zeroFreeRight_of_forall_psiError h⟩

/-- **RH ⟺ the prime number theorem with square-root error (ε-form).** -/
theorem riemannHypothesis_iff_psiError :
    RiemannHypothesis ↔ ∀ δ > 0, PsiError (1 / 2 + δ) :=
  ⟨psiError_of_RH, fun h => QuasiRH.riemannHypothesis_of_psiError h⟩

/-- OpenAI's statement is equivalent to `ψ(x) = x + O(x^{7/8+δ})` for every `δ > 0`. -/
theorem openAIStatement_iff_psiError :
    OpenAIStatement ↔ ∀ δ > 0, PsiError (7 / 8 + δ) := by
  rw [← zeroFreeRight_iff_psiError (by norm_num) (by norm_num)]
  exact ⟨fun h s hs => h hs, fun h _ hs => h _ hs⟩

end Ingham
