/-
Copyright (c) 2026 lixiang90. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P3Group contributors
-/

import P3Group.Defs
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Classification of abelian groups of order p³

Every abelian group of order p³ is isomorphic to exactly one of:
  1. `ℤ/p³ℤ`
  2. `ℤ/p²ℤ × ℤ/pℤ`
  3. `(ℤ/pℤ)³`

This follows from the structure theorem for finite abelian groups applied
 to the partitions of 3: (3), (2,1), (1,1,1).
-/

set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
namespace P3Group

open Fintype Monoid

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Cardinalities of the three abelian types -/

theorem card_cyclicP3 : Nat.card (CyclicP3 p) = p ^ 3 := by
  simp [CyclicP3]

theorem card_abelianP2P : Nat.card (AbelianP2P p) = p ^ 3 := by
  simp [AbelianP2P]; ring

theorem card_elementaryP3 : Nat.card (ElementaryP3 p) = p ^ 3 := by
  simp [ElementaryP3]; ring

/-! ### The three types are pairwise non-isomorphic -/

theorem abelianP2P_not_cyclic :
    ¬ IsCyclic (Multiplicative (ZMod (p ^ 2)) ×
                Multiplicative (ZMod p)) := by
  intro h
  have hcop := coprime_card_of_isCyclic_prod
    (Multiplicative (ZMod (p ^ 2))) (Multiplicative (ZMod p))
  simp only [Nat.card_eq_fintype_card, card_multiplicative, ZMod.card, Order.lt_two_iff, zero_le,
  Nat.coprime_pow_left_iff, Nat.coprime_self] at hcop
  exact absurd hcop hp.out.one_lt.ne'

theorem elementaryP3_exponent :
    exponent (Multiplicative (ZMod p) ×
      Multiplicative (ZMod p) ×
      Multiplicative (ZMod p)) = p := by
  simp [exponent_prod, exponent_multiplicative, ZMod.exponent]

theorem abelianP2P_exponent :
    exponent (Multiplicative (ZMod (p ^ 2)) ×
              Multiplicative (ZMod p)) = p ^ 2 := by
  simp [exponent_prod, exponent_multiplicative, ZMod.exponent]
  exact Nat.lcm_eq_left (dvd_pow_self p (by omega))

/-! ### Classification of abelian groups of order p³ -/

/-- An abelian group of order p³ is isomorphic to one of the three
    abelian types.

    **Proof.** By the structure theorem for finite abelian groups
    (`CommGroup.equiv_prod_multiplicative_zmod_of_finite`),
    G ≅ ∏ᵢ ℤ/nᵢℤ where each nᵢ > 1 and ∏ nᵢ = p³.
    Since p is prime, each nᵢ is a power of p, and the
    possible multisets correspond to partitions of 3:
    (3) → ℤ/p³ℤ, (2,1) → ℤ/p² × ℤ/p, (1,1,1) → (ℤ/p)³. -/
private noncomputable def mulEquivPiFinTwo
    (M : Fin 2 → Type*) [∀ i, CommGroup (M i)] :
    (∀ i : Fin 2, M i) ≃* M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_mul' := fun _ _ => rfl }

private noncomputable def mulEquivPiReindex
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (M : ι → Type*) [∀ i, Mul (M i)]
    (e : ι ≃ ι') :
    (∀ i : ι, M i) ≃* (∀ j : ι', M (e.symm j)) :=
  { Equiv.piCongrLeft' M e with
    map_mul' := fun _ _ => rfl }

theorem abelian_p3_classification (G : Type*) [CommGroup G]
    [Fintype G] (hcard : Nat.card G = p ^ 3) :
    Nonempty (G ≃* Multiplicative (CyclicP3 p)) ∨
    Nonempty (G ≃* (Multiplicative (ZMod (p ^ 2)) ×
                     Multiplicative (ZMod p))) ∨
    Nonempty (G ≃* (Multiplicative (ZMod p) ×
                     Multiplicative (ZMod p) ×
                     Multiplicative (ZMod p))) := by
  -- Case split on whether G is cyclic
  by_cases hcyc : IsCyclic G
  · -- Cyclic case: G ≅ ℤ/p³ℤ
    left
    refine ⟨(zmodCyclicMulEquiv hcyc).symm.trans ?_⟩
    change Multiplicative (ZMod (Nat.card G)) ≃*
           Multiplicative (ZMod (p ^ 3))
    exact hcard ▸ MulEquiv.refl _
  · -- Non-cyclic: use structure theorem
    obtain ⟨ι, inst, n, hn_gt, ⟨e⟩⟩ :=
      CommGroup.equiv_prod_multiplicative_zmod_of_finite G
    have hne : ∀ i, NeZero (n i) := fun i => NeZero.of_gt (hn_gt i)
    have hprod : ∏ i : ι, n i = p ^ 3 := by
      have h1 : Nat.card G =
          Nat.card ((i : ι) → Multiplicative (ZMod (n i))) :=
        Nat.card_congr e.toEquiv
      rw [hcard] at h1
      rw [Nat.card_pi] at h1
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
                 ZMod.card] at h1
      exact h1.symm
    -- Each n i divides p³ and is a power of p
    have hn_dvd : ∀ i, n i ∣ p ^ 3 := by
      intro i; rw [← hprod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    -- |ι| ≥ 2 (since G is not cyclic)
    have hcard_ι : 2 ≤ Fintype.card ι := by
      by_contra h
      push Not at h
      have hle : Fintype.card ι ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h1
      · -- |ι| = 0: impossible since ∏ = 1 ≠ p³
        haveI : IsEmpty ι := by rwa [Fintype.card_eq_zero_iff] at h0
        simp [Finset.univ_eq_empty] at hprod
        have : 1 < p ^ 3 := Nat.one_lt_pow (by omega) hp.out.one_lt
        omega
      · -- |ι| = 1: G is cyclic, contradicts hcyc
        have h1eq : Fintype.card ι = 1 := by omega
        haveI : Unique ι :=
          (Fintype.card_eq_one_iff_nonempty_unique.mp h1eq).some
        have e' := e.trans (MulEquiv.piUnique _)
        exact hcyc (isCyclic_of_surjective e'.symm e'.symm.surjective)
    -- Each n i is a power of p with exponent ≥ 1
    have hn_ppow : ∀ i, ∃ k, 1 ≤ k ∧ k ≤ 3 ∧ n i = p ^ k := by
      intro i
      obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (hn_dvd i)
      refine ⟨k, ?_, hk3, hk⟩
      by_contra h; push Not at h
      interval_cases k
      simp at hk; linarith [hn_gt i]
    -- Each n i ≥ p
    have hn_ge_p : ∀ i, p ≤ n i := by
      intro i
      obtain ⟨k, hk1, _, hk⟩ := hn_ppow i
      rw [hk]
      exact le_self_pow₀ hp.out.one_le (by omega)
    -- |ι| ≤ 3 (since p^|ι| ≤ ∏ n i = p³)
    have hcard_ι_le : Fintype.card ι ≤ 3 := by
      have hple : p ^ Fintype.card ι ≤ p ^ 3 := by
        calc p ^ Fintype.card ι
            = ∏ _i : ι, p := by simp
          _ ≤ ∏ i : ι, n i :=
            Finset.prod_le_prod (fun _ _ => by omega)
              (fun i _ => hn_ge_p i)
          _ = p ^ 3 := hprod
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hple
    -- Case split: |ι| = 2 or |ι| = 3
    have hcard_ι_cases : Fintype.card ι = 2 ∨ Fintype.card ι = 3 := by
      omega
    rcases hcard_ι_cases with h2 | h3
    · -- |ι| = 2: two factors, must be (p², p)
      right; left
      have eι : ι ≃ Fin 2 := Fintype.equivFinOfCardEq h2
      set n' : Fin 2 → ℕ := fun j => n (eι.symm j) with hn'_def
      have hn'_ppow : ∀ j : Fin 2, ∃ k, 1 ≤ k ∧ k ≤ 3 ∧ n' j = p ^ k :=
        fun j => hn_ppow (eι.symm j)
      obtain ⟨k₀, hk0_ge, hk0_le, hk0⟩ := hn'_ppow 0
      obtain ⟨k₁, hk1_ge, hk1_le, hk1⟩ := hn'_ppow 1
      have hsum : k₀ + k₁ = 3 := by
        have hprod' : n' 0 * n' 1 = p ^ 3 := by
          have := hprod
          rw [show ∏ i : ι, n i = ∏ j : Fin 2, n' j from
            Finset.prod_equiv eι (by simp)
              (by intro i _; simp [n'])] at this
          simpa [Fin.prod_univ_two] using this
        have : p ^ k₀ * p ^ k₁ = p ^ 3 := by rw [← hk0, ← hk1]; exact hprod'
        rw [← pow_add] at this
        exact Nat.pow_right_injective hp.out.two_le this
      -- Build MulEquiv via reindex + piFinTwo + cast
      have ereindex := mulEquivPiReindex
        (fun i => Multiplicative (ZMod (n i))) eι
      have eprod := mulEquivPiFinTwo
        (fun j => Multiplicative (ZMod (n' j)))
      have hcases : (k₀ = 2 ∧ k₁ = 1) ∨ (k₀ = 1 ∧ k₁ = 2) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- n' 0 = p², n' 1 = p
        rw [hk0, hk1, pow_one] at eprod
        exact ⟨e.trans (ereindex.trans eprod)⟩
      · -- n' 0 = p, n' 1 = p²: need to swap
        rw [hk0, hk1, pow_one] at eprod
        exact ⟨e.trans (ereindex.trans (eprod.trans
          MulEquiv.prodComm))⟩
    · -- |ι| = 3: three factors, all equal to p
      right; right
      have eι : ι ≃ Fin 3 := Fintype.equivFinOfCardEq h3
      -- Each n (eι.symm j) is a power of p with exponent ≥ 1
      have hprod' : ∏ j : Fin 3, n (eι.symm j) = p ^ 3 := by
        rw [← hprod]
        exact (Finset.prod_equiv eι (by simp) (by simp)).symm
      -- All n (eι.symm j) = p
      have hall_p : ∀ j : Fin 3, n (eι.symm j) = p := by
        have hexps : ∀ j : Fin 3, ∃ k, 1 ≤ k ∧ n (eι.symm j) = p ^ k :=
          fun j => let ⟨k, h1, _, h3⟩ := hn_ppow (eι.symm j); ⟨k, h1, h3⟩
        choose ex hex_ge hex using hexps
        have hsum : ex 0 + ex 1 + ex 2 = 3 := by
          have h1 : ∏ j : Fin 3, p ^ ex j = p ^ 3 := by
            convert hprod' using 1; congr 1; ext j; exact (hex j).symm
          rw [Fin.prod_univ_three, ← pow_add, ← pow_add] at h1
          exact Nat.pow_right_injective hp.out.two_le h1
        have : ex 0 = 1 ∧ ex 1 = 1 ∧ ex 2 = 1 := by
          have := hex_ge 0; have := hex_ge 1; have := hex_ge 2; omega
        intro j; rw [hex j]; fin_cases j <;> simp [this.1, this.2.1, this.2.2]
      -- n factors through eι to constant p
      have hn_eq : n = fun i => p := by
        ext i; have := hall_p (eι i); simp at this; exact this
      subst hn_eq
      have etriple : (∀ j : Fin 3, Multiplicative (ZMod p)) ≃*
                     (Multiplicative (ZMod p) ×
                      Multiplicative (ZMod p) ×
                      Multiplicative (ZMod p)) :=
        { toFun := fun f => (f 0, f 1, f 2)
          invFun := fun ⟨a, b, c⟩ => ![a, b, c]
          left_inv := by intro f; ext j; fin_cases j <;> rfl
          right_inv := by intro ⟨a, b, c⟩; simp [Matrix.cons_val_zero, Matrix.cons_val_one]
          map_mul' := by intro f g; rfl }
      exact ⟨e.trans ((mulEquivPiReindex _ eι).trans etriple)⟩

end P3Group
