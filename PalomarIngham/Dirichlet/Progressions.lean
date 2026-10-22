module

public import PalomarIngham.Dirichlet.Basic
public import Mathlib

/-!
# From characters to arithmetic progressions

`ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (q)} Λ(n)`. For `a` a unit mod `q`, orthogonality of Dirichlet
characters gives `ψ(x; q, a) = φ(q)⁻¹ ∑_χ χ(a)⁻¹ ψ(x, χ)`. The trivial character contributes
`ψ(x) + O(log x)`; so error terms `O(x^α)` for `ψ(x) - x` and for every `ψ(x, χ)`, `χ ≠ 1`, give

  `ψ(x; q, a) = x/φ(q) + O(x^α)`.
-/

@[expose] public section

set_option autoImplicit false

open Set Function Filter Complex Real Asymptotics ArithmeticFunction

namespace InghamL

variable {q : ℕ} [NeZero q]

/-- `ψ(x; q, a)`. -/
noncomputable def psiAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), Λ n

/-! ### Orthogonality -/

open scoped Classical in
theorem psiAP_eq_sum_chars {a : ZMod q} (ha : IsUnit a) (x : ℝ) :
    ((psiAP q a x : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * psiChi χ x := by
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  rw [eq_inv_mul_iff_mul_eq₀ htot]
  simp only [psiChi, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ n * (Λ n : ℂ)) =
      if a = (n : ZMod q) then (q.totient : ℂ) * Λ n else 0 := by
    intro n
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
    split_ifs <;> simp
  simp_rw [hterm]
  rw [psiAP, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : (n : ZMod q) = a
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; simp

/-! ### The trivial character -/

omit [NeZero q] in
theorem psiChi_one (x : ℝ) :
    psiChi (1 : DirichletCharacter ℂ q) x =
      ((∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n.Coprime q), Λ n : ℝ) : ℂ) := by
  rw [psiChi, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n.Coprime q
  · rw [ite_eq_left h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr h), one_mul]
  · rw [ite_eq_right h, MulCharClass.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    simp

/-- Prime powers sharing a factor with `q` contribute at most `ω(q) log N`. -/
theorem sum_noncoprime_le (N : ℕ) :
    ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ n.Coprime q), Λ n ≤
      q.primeFactors.card * Real.log N := by
  classical
  set S := (Finset.Ioc 0 N).filter (fun n => ¬ n.Coprime q)
  set D : ℕ → Finset ℕ := fun p => (p ^ Nat.log p N).divisors
  have hpt : ∀ n ∈ S, Λ n ≤ ∑ p ∈ q.primeFactors, if n ∈ D p then Λ n else 0 := by
    intro n hn
    by_cases hΛ : Λ n = 0
    · rw [hΛ]; exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hS := Finset.mem_filter.mp hn
    have hN := (Finset.mem_Ioc.mp hS.1)
    have hpq : p ∣ q := by
      by_contra hpq
      exact hS.2 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq))
    have hpf : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩
    have hkN : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hN.2
    have hmem : p ^ k ∈ D p := by
      simp only [D, Nat.mem_divisors]
      exact ⟨pow_dvd_pow p hkN, pow_ne_zero _ hp.ne_zero⟩
    calc Λ (p ^ k) = if p ^ k ∈ D p then Λ (p ^ k) else 0 := by rw [ite_eq_left hmem]
      _ ≤ _ := Finset.single_le_sum (f := fun p' => if p ^ k ∈ D p' then Λ (p ^ k) else 0)
          (fun _ _ => by split_ifs <;> simp) hpf
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, ∑ p ∈ q.primeFactors, if n ∈ D p then Λ n else 0 :=
        Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ S, if n ∈ D p then Λ n else 0 := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := (Nat.mem_primeFactors.mp hp).1
        rw [← Finset.sum_filter]
        calc ∑ n ∈ S with n ∈ D p, Λ n ≤ ∑ n ∈ D p, Λ n :=
              Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (Finset.mem_filter.mp hn).2)
                (fun _ _ _ => vonMangoldt_nonneg)
          _ = Real.log ((p ^ Nat.log p N : ℕ) : ℝ) := vonMangoldt_sum
          _ ≤ Real.log N := by
              rcases Nat.eq_zero_or_pos N with h0 | h0
              · subst h0; simp
              · apply Real.log_le_log (by exact_mod_cast pow_pos hp'.pos _)
                exact_mod_cast Nat.pow_log_le_self p h0.ne'
    _ = q.primeFactors.card * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]

theorem psi_sub_psiChi_one_le (x : ℝ) (hx : 1 ≤ x) :
    ‖(Chebyshev.psi x : ℂ) - psiChi (1 : DirichletCharacter ℂ q) x‖ ≤
      q.primeFactors.card * Real.log x := by
  rw [psiChi_one, Chebyshev.psi, ← Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc 0 ⌊x⌋₊) (fun n => n.Coprime q)]
  push_cast
  rw [add_sub_cancel_left, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg)]
  refine (sum_noncoprime_le ⌊x⌋₊).trans ?_
  gcongr
  · exact_mod_cast Nat.floor_pos.mpr hx
  · exact Nat.floor_le (by linarith)

/-! ### The prime number theorem in progressions, from error terms for each character -/

open scoped Classical in
theorem psiAP_error {a : ZMod q} (ha : IsUnit a) {α : ℝ} (hα : 0 < α)
    (hζ : Ingham.PsiError α) (hχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → PsiChiError χ α) :
    (fun x : ℝ => psiAP q a x - x / q.totient) =O[atTop] (fun x : ℝ => x ^ α) := by
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  -- the trivial character: ψ(x,1) - x = (ψ(x,1) - ψ(x)) + (ψ(x) - x)
  have hlog : (fun x : ℝ => Real.log x) =O[atTop] (fun x : ℝ => x ^ α) :=
    (isLittleO_log_rpow_atTop hα).isBigO
  have h1 : (fun x : ℝ => psiChi (1 : DirichletCharacter ℂ q) x - x) =O[atTop]
      (fun x : ℝ => x ^ α) := by
    have hA : (fun x : ℝ => psiChi (1 : DirichletCharacter ℂ q) x - (Chebyshev.psi x : ℂ))
        =O[atTop] (fun x : ℝ => x ^ α) := by
      refine (IsBigO.of_bound (q.primeFactors.card) ?_).trans hlog
      filter_upwards [eventually_ge_atTop 1] with x hx
      rw [norm_sub_rev, Real.norm_of_nonneg (Real.log_nonneg hx)]
      exact psi_sub_psiChi_one_le x hx
    have hB : (fun x : ℝ => ((Chebyshev.psi x : ℂ) - x)) =O[atTop] (fun x : ℝ => x ^ α) := by
      refine IsBigO.of_norm_left ?_
      simpa [← Complex.ofReal_sub, Complex.norm_real] using hζ.norm_left
    simpa using hA.add hB
  -- the decomposition
  have hdec : ∀ x : ℝ, ((psiAP q a x - x / q.totient : ℝ) : ℂ) = (q.totient : ℂ)⁻¹ *
      ((psiChi (1 : DirichletCharacter ℂ q) x - x) +
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), χ a⁻¹ * psiChi χ x) := by
    intro x
    push_cast
    rw [psiAP_eq_sum_chars ha, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
    simp only [MulChar.one_apply (IsUnit.of_mul_eq_one a ((ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl)),
      one_mul]
    field_simp
    ring
  have hsum : (fun x : ℝ => ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      χ a⁻¹ * psiChi χ x) =O[atTop] (fun x : ℝ => x ^ α) := by
    have hfun : (fun x : ℝ => ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ a⁻¹ * psiChi χ x) = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (fun x : ℝ => χ a⁻¹ * psiChi χ x) := by
      funext x; simp [Finset.sum_apply]
    rw [hfun]
    refine IsBigO.sum fun χ hχ1 => ?_
    have hne : χ ≠ 1 := Finset.ne_of_mem_erase hχ1
    exact (hχ χ hne).const_mul_left _
  have hall := ((h1.add hsum).const_mul_left (q.totient : ℂ)⁻¹)
  refine IsBigO.of_norm_left ?_
  have : (fun x : ℝ => ‖psiAP q a x - x / q.totient‖) = (fun x : ℝ =>
      ‖(q.totient : ℂ)⁻¹ * ((psiChi (1 : DirichletCharacter ℂ q) x - x) +
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), χ a⁻¹ * psiChi χ x)‖) := by
    funext x; rw [← hdec, Complex.norm_real]
  rw [this]
  exact hall.norm_left

end InghamL
