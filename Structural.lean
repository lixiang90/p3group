/-
Copyright (c) 2026 lixiang90. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P3Group contributors
-/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.ClassEquation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Structural lemmas for p-groups of order p³

This file collects basic structural facts used in the classification:
* A group of order p³ is a p-group and is nilpotent.
* The center of a non-abelian group of order p³ has order p.
* The quotient G / Z(G) has order p² and is isomorphic to `(ℤ/pℤ)²`.
* The commutator subgroup of a non-abelian p³-group equals its center.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace P3Group

open Subgroup

/-! ### Local helpers for finite products of multiplicative groups -/

private noncomputable def mulEquivPiReindex
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (M : ι → Type*) [∀ i, Mul (M i)] (e : ι ≃ ι') :
    (∀ i : ι, M i) ≃* (∀ j : ι', M (e.symm j)) where
  toEquiv := Equiv.piCongrLeft' M e
  map_mul' := fun _ _ => rfl

private noncomputable def mulEquivPiFinTwo
    (M : Fin 2 → Type*) [∀ i, Mul (M i)] :
    (∀ i : Fin 2, M i) ≃* M 0 × M 1 where
  toEquiv := piFinTwoEquiv M
  map_mul' := fun _ _ => rfl

variable {G : Type*} [Group G] [Fintype G]
variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Basic facts about p³-groups -/

/-- A group of order p³ is a p-group. -/
theorem isPGroup_of_card_eq_p3 (hcard : Nat.card G = p ^ 3) :
    IsPGroup p G := by
  rw [IsPGroup.iff_card]
  exact ⟨3, hcard⟩

/-- If G/Z(G) is cyclic, then G is abelian. -/
theorem comm_of_cyclic_center_quotient
    (hcyc : IsCyclic (G ⧸ center G)) :
    ∀ a b : G, a * b = b * a := by
  letI : CommGroup G := commGroupOfCyclicCenterQuotient
    (QuotientGroup.mk' (center G))
    (by rw [QuotientGroup.ker_mk'])
  exact fun a b => mul_comm a b

/-- Every group of order p³ is nilpotent. -/
theorem isNilpotent_of_card_p3 (hcard : Nat.card G = p ^ 3) :
    Group.IsNilpotent G :=
  (isPGroup_of_card_eq_p3 hcard).isNilpotent

/-! ### Center structure of non-abelian p³-groups -/

/-- In a non-abelian group of order p³, the center has order exactly p. -/
theorem center_card_eq_p_of_nonabelian (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    Nat.card (center G) = p := by
  have hprime := hp.out
  have hG : IsPGroup p G := isPGroup_of_card_eq_p3 hcard
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hG.to_subgroup (center G))
  have hdvd : Nat.card (center G) ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card _
  rw [hk, hcard] at hdvd
  have hk3 : k ≤ 3 := by
    rwa [Nat.pow_dvd_pow_iff_le_right hprime.one_lt] at hdvd
  have hnt : Nontrivial G := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card,
        hcard]
    exact Nat.one_lt_pow (by omega) hprime.one_lt
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd ((Nat.card_eq_one_iff_unique.mp hk).1)
        (not_subsingleton_iff_nontrivial.mpr hG.center_nontrivial)
    · omega
  have hk_ne_3 : k ≠ 3 := by
    intro hk3'; subst hk3'
    have htop := Subgroup.eq_top_of_card_eq (center G) (by rw [hk, hcard])
    apply hnonab; intro a b
    have ha : a ∈ center G := htop ▸ Subgroup.mem_top a
    rw [Subgroup.mem_center_iff] at ha; exact (ha b).symm
  have hk_ne_2 : k ≠ 2 := by
    intro hk2'; subst hk2'
    have hquot_card : Nat.card (G ⧸ center G) = p := by
      have hlag := Subgroup.card_mul_index (center G)
      rw [Subgroup.index_eq_card, hk, hcard] at hlag
      have : p ^ 2 * Nat.card (G ⧸ center G) = p ^ 2 * p := by
        rw [hlag]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hprime.ne_zero) this
    haveI : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hquot_card
    exact hnonab (comm_of_cyclic_center_quotient inferInstance)
  have : k = 1 := by omega
  rw [this] at hk; simpa using hk

/-- In a non-abelian group of order p³, G/Z(G) has order p². -/
theorem quotient_center_card_eq_p2 (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    Nat.card (G ⧸ center G) = p ^ 2 := by
  have hcenter := center_card_eq_p_of_nonabelian hcard hnonab
  have hlag := Subgroup.card_mul_index (center G)
  rw [Subgroup.index_eq_card, hcenter, hcard] at hlag
  have hpne : p ≠ 0 := hp.out.ne_zero
  have : p * Nat.card (G ⧸ center G) = p * p ^ 2 := by
    rw [hlag]; ring
  exact mul_left_cancel₀ hpne this

/-- A group of order p² is abelian. -/
theorem comm_of_card_p2 (hcard : Nat.card G = p ^ 2) :
    ∀ a b : G, a * b = b * a := by
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hcard
  exact this.is_comm.comm

/-- In a non-abelian group of order p³, G/Z(G) ≅ (ℤ/pℤ)². -/
theorem quotient_center_iso_p2 (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    Nonempty ((G ⧸ center G) ≃*
      (Multiplicative (ZMod p) × Multiplicative (ZMod p))) := by
  have hq := quotient_center_card_eq_p2 hcard hnonab
  haveI : IsMulCommutative (G ⧸ center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  letI : CommGroup (G ⧸ center G) :=
    { mul_comm := IsMulCommutative.is_comm.comm }
  have hncyc : ¬ IsCyclic (G ⧸ center G) := by
    intro h
    exact hnonab (comm_of_cyclic_center_quotient h)
  have hne2 : ¬ IsCyclic (G ⧸ center G) := hncyc
  have hexpeq : Monoid.exponent (G ⧸ center G) = p := by
    exact (not_isCyclic_iff_exponent_eq_prime hp.out hq).mp hncyc
  have hcard2 : Nat.card (G ⧸ center G) = p ^ 2 := hq
  obtain ⟨ι, inst, n, hn_gt, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite (G ⧸ center G)
  haveI : Fintype ι := inst
  have hprod : ∏ i : ι, n i = p ^ 2 := by
    have h1 : Nat.card (G ⧸ center G) =
        Nat.card ((i : ι) → Multiplicative (ZMod (n i))) :=
      Nat.card_congr e.toEquiv
    rw [hcard2, Nat.card_pi] at h1
    have hcard_each : ∀ i, Nat.card (Multiplicative (ZMod (n i))) = n i := by
      intro i
      haveI : Fact (0 < n i) := ⟨by have := hn_gt i; omega⟩
      haveI : NeZero (n i) := NeZero.of_gt (by have := hn_gt i; omega)
      haveI : Fintype (ZMod (n i)) := ZMod.fintype (n i)
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hprod_eq : (∏ i : ι, Nat.card (Multiplicative (ZMod (n i)))) =
        (∏ i : ι, n i) :=
      Finset.prod_congr rfl fun i _ => by rw [hcard_each i]
    rw [hprod_eq] at h1
    exact h1.symm
  have hexp_dvd : ∀ i, n i ∣ Monoid.exponent (G ⧸ center G) := by
    intro i
    let π : G ⧸ center G →* Multiplicative (ZMod (n i)) :=
      (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i).comp
        e.toMonoidHom
    have hsurj : Function.Surjective π := by
      intro z
      classical
      let f : (j : ι) → Multiplicative (ZMod (n j)) := fun j =>
        if h : j = i then by subst h; exact z else 1
      use e.symm f
      simp [π, f]
    have hexp_temp : Monoid.exponent (Multiplicative (ZMod (n i))) ∣
        Monoid.exponent (G ⧸ center G) :=
      MonoidHom.exponent_dvd (f := π) hsurj
    have hexp_mul : Monoid.exponent (Multiplicative (ZMod (n i))) = n i := by
      simp
    rwa [hexp_mul] at hexp_temp
  rw [hexpeq] at hexp_dvd
  have hn_eq_p : ∀ i, n i = p := by
    intro i
    have hdvd : n i ∣ p := hexp_dvd i
    have hgt : 1 < n i := hn_gt i
    have : n i = 1 ∨ n i = p := hp.out.eq_one_or_self_of_dvd _ hdvd
    omega
  have hcard_ι : Fintype.card ι = 2 := by
    have hprod_p : ∏ i : ι, n i = p ^ Fintype.card ι := by
      simp [hn_eq_p]
    rw [hprod_p] at hprod
    exact (Nat.pow_right_injective hp.out.two_le) hprod
  have eι : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard_ι
  set n' : Fin 2 → ℕ := fun j => n (eι.symm j) with hn'_def
  have hn'_eq_p : ∀ j : Fin 2, n' j = p := fun j => hn_eq_p (eι.symm j)
  have ereindex := mulEquivPiReindex
    (fun i => Multiplicative (ZMod (n i))) eι
  have eprod := mulEquivPiFinTwo
    (fun j => Multiplicative (ZMod (n' j)))
  rw [show n' 0 = p by exact hn'_eq_p 0,
      show n' 1 = p by exact hn'_eq_p 1] at eprod
  exact ⟨e.trans (ereindex.trans eprod)⟩

/-- A non-abelian group of order p³ has nilpotency class exactly 2. -/
theorem nilpotencyClass_eq_two (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    Group.nilpotencyClass G = 2 := by
  classical
  haveI hnil : Group.IsNilpotent G := isNilpotent_of_card_p3 hcard
  haveI : Fintype (G ⧸ center G) := QuotientGroup.fintype _
  have hqcard : Nat.card (G ⧸ center G) = p ^ 2 :=
    quotient_center_card_eq_p2 hcard hnonab
  have hq_ab : ∀ a b : G ⧸ center G, a * b = b * a := comm_of_card_p2 hqcard
  have hq_comm : IsMulCommutative (G ⧸ center G) :=
    IsMulCommutative.of_comm hq_ab
  have hxy_comm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ center G := by
    intro x y
    let Q := QuotientGroup.mk' (center G)
    have hQ : Q (x * y * x⁻¹ * y⁻¹) = (Q x * Q y) * (Q x)⁻¹ * (Q y)⁻¹ := by
      simp [map_mul, map_inv]
    have h_one : Q (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [hQ]
      calc
        (Q x * Q y) * (Q x)⁻¹ * (Q y)⁻¹ =
          (Q x * Q y) * ((Q x)⁻¹ * (Q y)⁻¹) := by group
        _ = (Q y * Q x) * ((Q x)⁻¹ * (Q y)⁻¹) := by rw [hq_ab (Q x) (Q y)]
        _ = 1 := by group
    exact (QuotientGroup.eq_one_iff _).mp h_one
  have hucs2 : Subgroup.upperCentralSeries G 2 = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x _
    apply (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact hxy_comm x y
  have hclass_le : Group.nilpotencyClass G ≤ 2 :=
    (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp hucs2)
  have hclass_ge : 2 ≤ Group.nilpotencyClass G := by
    by_contra h
    push Not at h
    have hle1 : Group.nilpotencyClass G ≤ 1 := by omega
    have hmc : IsMulCommutative G :=
      Group.IsNilpotent.nilpotencyClass_le_one_iff.mp hle1
    exact hnonab hmc.is_comm.comm
  omega

/-- The commutator subgroup of a non-abelian p³-group equals the center. -/
theorem commutator_eq_center (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    commutator G = center G := by
  classical
  have hcenter_card : Nat.card (center G) = p :=
    center_card_eq_p_of_nonabelian hcard hnonab
  haveI : Fintype (G ⧸ center G) := QuotientGroup.fintype _
  have hqcard : Nat.card (G ⧸ center G) = p ^ 2 :=
    quotient_center_card_eq_p2 hcard hnonab
  have hq_ab : ∀ a b : G ⧸ center G, a * b = b * a := comm_of_card_p2 hqcard
  have hq_comm : IsMulCommutative (G ⧸ center G) :=
    IsMulCommutative.of_comm hq_ab
  have hcomm_le : commutator G ≤ center G := by
    have hq_comm_bot : commutator (G ⧸ center G) = ⊥ :=
      (commutator_eq_bot_iff _).mpr hq_comm
    have hmap : (commutator G).map (QuotientGroup.mk' (center G)) =
        commutator (G ⧸ center G) := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      have hsurj : Function.Surjective (QuotientGroup.mk' (center G)) :=
        QuotientGroup.mk'_surjective _
      have htop_map := Subgroup.map_top_of_surjective
        (QuotientGroup.mk' (center G)) hsurj
      simp [htop_map, _root_.commutator_def]
    rw [hq_comm_bot] at hmap
    have hle : commutator G ≤ (QuotientGroup.mk' (center G)).ker :=
      (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (center G))
        (commutator G)).mp hmap
    rw [QuotientGroup.ker_mk'] at hle
    exact hle
  have hcomm_ne_bot : commutator G ≠ ⊥ := by
    intro h_eq
    have hmc : IsMulCommutative G := (commutator_eq_bot_iff G).mp h_eq
    exact hnonab hmc.is_comm.comm
  classical
  haveI : Fintype (commutator G) := Subtype.fintype (· ∈ commutator G)
  haveI : Fintype (center G) := Subtype.fintype (· ∈ Subgroup.center G)
  have hcard_comm : Nat.card (commutator G) = p := by
    have hdvd : Nat.card (commutator G) ∣ Nat.card (center G) :=
      Subgroup.card_dvd_of_le hcomm_le
    rw [hcenter_card] at hdvd
    have hcard_ne_one : Nat.card (commutator G) ≠ 1 := by
      have h_one_lt : 1 < Nat.card (commutator G) :=
        (Subgroup.one_lt_card_iff_ne_bot (commutator G)).mpr hcomm_ne_bot
      omega
    rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hcard_ne_one
    · exact h
  have hcard_fin : Fintype.card (commutator G) = Fintype.card (center G) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_comm, hcenter_card]
  have hinj : Function.Injective (Subgroup.inclusion hcomm_le) :=
    Subgroup.inclusion_injective hcomm_le
  have hsurj : Function.Surjective (Subgroup.inclusion hcomm_le) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard_fin⟩).surjective
  apply le_antisymm hcomm_le
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hyx : (y : G) = x := by
    have := congrArg Subtype.val hy
    simpa [Subgroup.inclusion] using this
  rw [← hyx]
  exact y.2

end P3Group
