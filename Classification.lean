/-
Copyright (c) 2026 lixiang90. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P3Group contributors
-/

import P3Group.AbelianCase
import P3Group.NonAbelianCase
import P3Group.Structural

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.header false

namespace P3Group

open Fintype Subgroup

variable (p : ℕ) [hp : Fact (Nat.Prime p)]



/-! ### The five concrete groups -/

/-- Predicate: G is isomorphic to one of the five groups of order p³.
    For p odd, the non-abelian groups are Heisenberg and ℤ/p² ⋊ ℤ/p.
    For p = 2, the non-abelian groups are D₄ and Q₈. -/
def IsP3Group (G : Type*) [Group G] [Fintype G] : Prop :=
  Nonempty (G ≃* Multiplicative (CyclicP3 p)) ∨
  Nonempty (G ≃* (Multiplicative (ZMod (p ^ 2)) ×
                   Multiplicative (ZMod p))) ∨
  Nonempty (G ≃* (Multiplicative (ZMod p) ×
                   Multiplicative (ZMod p) ×
                   Multiplicative (ZMod p))) ∨
  (p ≠ 2 ∧ Nonempty (G ≃* HeisenbergGroup p)) ∨
  (p ≠ 2 ∧ Nonempty (G ≃* SemidirectP2P p)) ∨
  (p = 2 ∧ Nonempty (G ≃* DihedralGroup 4)) ∨
  (p = 2 ∧ Nonempty (G ≃* QuaternionGroup 2))

/-! ### Main Classification Theorem -/

/-- **Classification Theorem for Groups of Order p³.**
    Every group of order p³ is isomorphic to one of the five
    standard groups.

    **Proof.** Split into abelian vs non-abelian.
    - Abelian: apply structure theorem → partitions of 3.
    - Non-abelian: |Z(G)| = p, G/Z(G) ≅ (ℤ/pℤ)²,
      exponent is p or p²; each determines the iso type. -/
theorem classification (G : Type*) [Group G] [Fintype G]
    (hcard : Nat.card G = p ^ 3) :
    IsP3Group p G := by
  by_cases hab : ∀ a b : G, a * b = b * a
  · -- Abelian case: use structure theorem
    letI : CommGroup G :=
      { mul_comm := hab }
    rcases abelian_p3_classification p G hcard with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · -- Non-abelian case: split on p = 2
    by_cases hp2 : p = 2
    · subst hp2
      rcases nonabelian_8_classification G hcard hab with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, h⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨rfl, h⟩)))))
    · rcases nonabelian_p3_classification_odd p hp2 G hcard
        hab with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hp2, h⟩))))

/-! ### Uniqueness: the five types are pairwise non-isomorphic -/

omit hp in
/-- ℤ/p³ℤ is cyclic. -/
theorem cyclicP3_is_cyclic :
    IsCyclic (Multiplicative (CyclicP3 p)) :=
  inferInstance

/-- The three abelian types are pairwise non-isomorphic. -/
theorem abelian_types_distinct :
    IsEmpty (Multiplicative (CyclicP3 p) ≃*
      (Multiplicative (ZMod (p ^ 2)) ×
       Multiplicative (ZMod p))) ∧
    IsEmpty (Multiplicative (CyclicP3 p) ≃*
      (Multiplicative (ZMod p) ×
       Multiplicative (ZMod p) ×
       Multiplicative (ZMod p))) ∧
    IsEmpty ((Multiplicative (ZMod (p ^ 2)) ×
              Multiplicative (ZMod p)) ≃*
      (Multiplicative (ZMod p) ×
       Multiplicative (ZMod p) ×
       Multiplicative (ZMod p))) := by
  refine ⟨⟨fun f => ?_⟩, ⟨fun f => ?_⟩, ⟨fun f => ?_⟩⟩
  · exact abelianP2P_not_cyclic p
      ((MulEquiv.isCyclic f).mp inferInstance)
  · have hcyc : IsCyclic (Multiplicative (ZMod p) ×
        Multiplicative (ZMod p) ×
        Multiplicative (ZMod p)) :=
      (MulEquiv.isCyclic f).mp inferInstance
    have hexp := IsCyclic.exponent_eq_card (α :=
      Multiplicative (ZMod p) × Multiplicative (ZMod p) ×
      Multiplicative (ZMod p))
    rw [elementaryP3_exponent] at hexp
    simp at hexp
    have := hp.out.one_lt
    nlinarith
  · have hexp1 := abelianP2P_exponent p
    have hexp2 := elementaryP3_exponent p
    have : Monoid.exponent (Multiplicative (ZMod (p ^ 2)) ×
      Multiplicative (ZMod p)) =
      Monoid.exponent (Multiplicative (ZMod p) ×
        Multiplicative (ZMod p) ×
        Multiplicative (ZMod p)) :=
      Monoid.exponent_eq_of_mulEquiv f
    rw [hexp1, hexp2] at this
    have := hp.out.one_lt
    nlinarith [sq_nonneg p]

/-- No abelian group of order p³ is isomorphic to a non-abelian one
    (the Heisenberg group is non-abelian). -/
theorem abelian_not_iso_nonabelian_heisenberg (_ : p ≠ 2) :
    IsEmpty (Multiplicative (CyclicP3 p) ≃*
             HeisenbergGroup p) ∧
    IsEmpty ((Multiplicative (ZMod (p ^ 2)) ×
              Multiplicative (ZMod p)) ≃*
             HeisenbergGroup p) ∧
    IsEmpty ((Multiplicative (ZMod p) ×
              Multiplicative (ZMod p) ×
              Multiplicative (ZMod p)) ≃*
             HeisenbergGroup p) := by
  have hnonab := HeisenbergGroup.heisenberg_nonabelian p
  refine ⟨⟨fun f => ?_⟩, ⟨fun f => ?_⟩, ⟨fun f => ?_⟩⟩
  all_goals {
    apply hnonab; intro a b
    have heq : f.symm a * f.symm b =
               f.symm b * f.symm a := mul_comm _ _
    calc a * b = f (f.symm a * f.symm b) := by simp
      _ = f (f.symm b * f.symm a) := by rw [heq]
      _ = b * a := by simp }

/-- The two non-abelian types (odd p) are non-isomorphic
    (distinguished by exponent: p vs p²). -/
theorem heisenberg_not_iso_semidirect (hodd : p ≠ 2) :
    IsEmpty (HeisenbergGroup p ≃* SemidirectP2P p) := by
  constructor
  intro f
  have hexp_h := HeisenbergGroup.heisenberg_exponent p hodd
  have hexp_s := SemidirectP2P.semidirectP2P_exponent p
  have : Monoid.exponent (HeisenbergGroup p) =
         Monoid.exponent (SemidirectP2P p) :=
    Monoid.exponent_eq_of_mulEquiv f
  rw [hexp_h, hexp_s] at this
  have := hp.out.one_lt
  nlinarith [sq_nonneg p]

/-! ### Counting: there are exactly 5 isomorphism classes -/

/-- For any prime p, every group of order p³ belongs to one of the
    five classes. -/
theorem exactly_five_classes :
    ∀ (G : Type*) [Group G] [Fintype G],
      Nat.card G = p ^ 3 → IsP3Group p G := by
  intro G _ _ hcard
  exact classification p G hcard

end P3Group
