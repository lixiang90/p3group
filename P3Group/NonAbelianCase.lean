/-
Copyright (c) 2026 lixiang90. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P3Group contributors
-/

import P3Group.Structural
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Exponent
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.Nat.ModEq

/-! # Classification of non-abelian groups of order p³

A non-abelian group of order p³ has:
  - Center of order p (isomorphic to `ℤ/pℤ`)
  - Quotient `G/Z(G) ≅ (ℤ/pℤ)²`
  - Commutator subgroup `[G,G] = Z(G)`
  - Nilpotency class 2

There are exactly two non-abelian groups of order p³ up to isomorphism,
distinguished by whether the group has exponent p or p²:

For p odd:
  - Exponent p:  The Heisenberg group
  - Exponent p²: `ℤ/p²ℤ ⋊ ℤ/pℤ`

For p = 2:
  - `D₄` (dihedral group of order 8)
  - `Q₈` (quaternion group of order 8)
-/

namespace P3Group

open Subgroup

variable {G : Type*} [Group G] [Fintype G]
variable {p : ℕ} [hp : Fact (Nat.Prime p)]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unnecessarySimpa false

/-! ### Construction of the Heisenberg group -/

/-- The Heisenberg group over ℤ/pℤ, represented as upper triangular
    3×3 matrices with 1s on the diagonal. Elements are triples
    (a, b, c) with multiplication (a,b,c)·(a',b',c') =
    (a+a', b+b', c+c'+a·b'). -/
@[ext]
structure HeisenbergGroup (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p
  deriving DecidableEq

namespace HeisenbergGroup

instance (p : ℕ) : Group (HeisenbergGroup p) where
  mul x y := ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩
  one := ⟨0, 0, 0⟩
  inv x := ⟨-x.a, -x.b, -x.c + x.a * x.b⟩
  mul_assoc x y z := by
    ext
    · show x.a + y.a + z.a = x.a + (y.a + z.a); ring
    · show x.b + y.b + z.b = x.b + (y.b + z.b); ring
    · show x.c + y.c + x.a * y.b + z.c + (x.a + y.a) * z.b =
          x.c + (y.c + z.c + y.a * z.b) + x.a * (y.b + z.b); ring
  one_mul x := by
    ext
    · show (0 : ZMod p) + x.a = x.a; exact zero_add _
    · show (0 : ZMod p) + x.b = x.b; exact zero_add _
    · show (0 : ZMod p) + x.c + (0 : ZMod p) * x.b = x.c; simp
  mul_one x := by
    ext
    · show x.a + (0 : ZMod p) = x.a; exact add_zero _
    · show x.b + (0 : ZMod p) = x.b; exact add_zero _
    · show x.c + (0 : ZMod p) + x.a * (0 : ZMod p) = x.c; simp
  inv_mul_cancel x := by
    ext
    · show -x.a + x.a = (0 : ZMod p); exact neg_add_cancel _
    · show -x.b + x.b = (0 : ZMod p); exact neg_add_cancel _
    · show (-x.c + x.a * x.b) + x.c + (-x.a) * x.b =
          (0 : ZMod p); ring

def equiv (p : ℕ) :
    HeisenbergGroup p ≃ (ZMod p × ZMod p × ZMod p) where
  toFun g := ⟨g.a, g.b, g.c⟩
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    Fintype (HeisenbergGroup p) :=
  Fintype.ofEquiv _ (equiv p).symm

/-- The Heisenberg group has order p³. -/
theorem card_heisenberg (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (HeisenbergGroup p) = p ^ 3 := by
  rw [Nat.card_congr (equiv p)]
  simp
  ring

/-- The Heisenberg group is non-abelian for p ≥ 2. -/
theorem heisenberg_nonabelian (p : ℕ) [Fact (Nat.Prime p)] :
    ¬ ∀ x y : HeisenbergGroup p, x * y = y * x := by
  intro h
  have h12 := h ⟨1, 0, 0⟩ ⟨0, 1, 0⟩
  have : (⟨1, 0, 0⟩ : HeisenbergGroup p) * ⟨0, 1, 0⟩ ≠
         ⟨0, 1, 0⟩ * ⟨1, 0, 0⟩ := by
    intro heq
    have hc := congrArg HeisenbergGroup.c heq
    change (0 : ZMod p) + 0 + 1 * 1 = 0 + 0 + 0 * 0 at hc
    simp at hc
  exact this h12

private theorem heisenberg_pow_aux (p : ℕ) (x : HeisenbergGroup p) (n : ℕ) :
    (x ^ n).a = (n : ZMod p) * x.a ∧
    (x ^ n).b = (n : ZMod p) * x.b ∧
    (x ^ n).c = (n : ZMod p) * x.c +
      (Nat.choose n 2 : ZMod p) * (x.a * x.b) := by
  induction n with
  | zero => simp [pow_zero]; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨ha, hb, hc⟩ := ih
    rw [pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · change (x ^ n).a + x.a = _
      rw [ha, Nat.cast_succ, add_mul, one_mul]
    · change (x ^ n).b + x.b = _
      rw [hb, Nat.cast_succ, add_mul, one_mul]
    · change (x ^ n).c + x.c + (x ^ n).a * x.b = _
      rw [ha, hc, Nat.cast_succ, Nat.choose_succ_succ,
          Nat.choose_one_right, Nat.cast_add, add_mul, add_mul,
          one_mul]
      ring

/-- Every element of the Heisenberg group satisfies x^p = 1 when p is odd. -/
private theorem heisenberg_pow_p (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hodd : p ≠ 2) (x : HeisenbergGroup p) : x ^ p = 1 := by
  have hlt : 2 < p := by
    have := hp.out.two_le; omega
  obtain ⟨ha, hb, hc⟩ := heisenberg_pow_aux p x p
  have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  have hchoose : (↑(Nat.choose p 2) : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
    exact hp.out.dvd_choose_self (by omega) hlt
  have h1a : (1 : HeisenbergGroup p).a = 0 := rfl
  have h1b : (1 : HeisenbergGroup p).b = 0 := rfl
  have h1c : (1 : HeisenbergGroup p).c = 0 := rfl
  ext
  · rw [ha, hp0, zero_mul, h1a]
  · rw [hb, hp0, zero_mul, h1b]
  · rw [hc, hp0, zero_mul, hchoose, zero_mul, zero_add, h1c]

/-- The Heisenberg group has exponent p for odd primes. -/
theorem heisenberg_exponent (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hodd : p ≠ 2) : Monoid.exponent (HeisenbergGroup p) = p := by
  apply Nat.dvd_antisymm
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one (heisenberg_pow_p p hodd)
  · have hne1 : (⟨1, 0, 0⟩ : HeisenbergGroup p) ≠ 1 := by
      intro h; have := congrArg HeisenbergGroup.a h
      change (1 : ZMod p) = 0 at this
      exact one_ne_zero this
    have hord_dvd : orderOf (⟨1, 0, 0⟩ : HeisenbergGroup p) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr (heisenberg_pow_p p hodd _)
    have hord_ne1 : orderOf (⟨1, 0, 0⟩ : HeisenbergGroup p) ≠ 1 :=
      mt orderOf_eq_one_iff.mp hne1
    have hord_eq : orderOf (⟨1, 0, 0⟩ : HeisenbergGroup p) = p :=
      (hp.out.eq_one_or_self_of_dvd _ hord_dvd).resolve_left hord_ne1
    calc p = orderOf (⟨1, 0, 0⟩ : HeisenbergGroup p) := hord_eq.symm
      _ ∣ Monoid.exponent (HeisenbergGroup p) := Monoid.order_dvd_exponent _

end HeisenbergGroup

/-! ### Construction of ℤ/p²ℤ ⋊ ℤ/pℤ -/

/-- The non-abelian group of order p³ and exponent p²:
    ⟨a, b | a^(p²) = b^p = 1, b⁻¹ab = a^(1+p)⟩ -/
@[ext]
structure SemidirectP2P (p : ℕ) where
  a : ZMod (p ^ 2)
  b : ZMod p
  deriving DecidableEq

namespace SemidirectP2P

private theorem pp_eq_zero (p : ℕ) [Fact (Nat.Prime p)] :
    (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
  have h : ((p * p : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [show p * p = p ^ 2 from (sq p).symm]
    exact CharP.cast_eq_zero (ZMod (p ^ 2)) (p ^ 2)
  rwa [Nat.cast_mul] at h

private theorem val_mul_p_add (p : ℕ) [hp : Fact (Nat.Prime p)]
    (k1 k2 : ZMod p) :
    ((k1 + k2).val : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) =
    (k1.val : ZMod (p ^ 2)) * ↑p + (k2.val : ZMod (p ^ 2)) * ↑p := by
  rw [← add_mul, ← Nat.cast_add, ZMod.val_add]
  set n := k1.val + k2.val
  conv_rhs => rw [← Nat.div_add_mod n p]
  rw [Nat.cast_add, Nat.cast_mul, add_mul,
      mul_comm (↑p : ZMod (p ^ 2)) (↑(n / p) : ZMod (p ^ 2)),
      mul_assoc, pp_eq_zero, mul_zero, zero_add]

private theorem val_neg_mul_p (p : ℕ) [hp : Fact (Nat.Prime p)]
    (k : ZMod p) :
    ((-k).val : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) =
    -((k.val : ZMod (p ^ 2)) * ↑p) := by
  have h := val_mul_p_add p (-k) k
  rw [neg_add_cancel, ZMod.val_zero, Nat.cast_zero, zero_mul] at h
  exact eq_neg_of_add_eq_zero_left h.symm

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Group (SemidirectP2P p) where
  mul x y := ⟨x.a + y.a + (x.b.val : ZMod (p ^ 2)) * ↑p * y.a, x.b + y.b⟩
  one := ⟨0, 0⟩
  inv x := ⟨-x.a + (x.b.val : ZMod (p ^ 2)) * ↑p * x.a, -x.b⟩
  mul_assoc x y z := by
    have h1 := val_mul_p_add p x.b y.b
    have hpp := pp_eq_zero p
    ext
    · change x.a + y.a + ↑x.b.val * ↑p * y.a + z.a +
           ↑(x.b + y.b).val * ↑p * z.a =
           x.a + (y.a + z.a + ↑y.b.val * ↑p * z.a) +
           ↑x.b.val * ↑p * (y.a + z.a + ↑y.b.val * ↑p * z.a)
      have h2 : (↑x.b.val : ZMod (p ^ 2)) * ↑p *
                ((↑y.b.val : ZMod (p ^ 2)) * ↑p * z.a) = 0 := by
        have : (↑x.b.val : ZMod (p ^ 2)) * ↑p *
               (↑y.b.val * ↑p * z.a) =
               ↑x.b.val * ↑y.b.val * (↑p * ↑p) * z.a := by ring
        rw [this, hpp, mul_zero, zero_mul]
      have h3 : ↑(x.b + y.b).val * (↑p : ZMod (p ^ 2)) * z.a =
          (↑x.b.val * ↑p + ↑y.b.val * ↑p) * z.a := by
        rw [← h1]
      rw [h3]
      have expand : (↑x.b.val : ZMod (p ^ 2)) * ↑p *
          (y.a + z.a + ↑y.b.val * ↑p * z.a) =
          ↑x.b.val * ↑p * y.a + ↑x.b.val * ↑p * z.a +
          ↑x.b.val * ↑p * (↑y.b.val * ↑p * z.a) := by
        rw [mul_add, mul_add]
      rw [expand, h2, add_zero, add_mul]
      abel
    · exact add_assoc _ _ _
  one_mul x := by
    ext
    · show 0 + x.a + (↑(0 : ZMod p).val : ZMod (p ^ 2)) * ↑p * x.a = x.a
      rw [ZMod.val_zero, Nat.cast_zero, zero_mul, zero_mul, add_zero, zero_add]
    · exact zero_add _
  mul_one x := by
    ext
    · show x.a + 0 + ↑x.b.val * ↑p * (0 : ZMod (p ^ 2)) = x.a
      rw [mul_zero, add_zero, add_zero]
    · exact add_zero _
  inv_mul_cancel x := by
    ext
    · show -x.a + ↑x.b.val * ↑p * x.a + x.a + ↑(-x.b).val * ↑p * x.a = 0
      have h := val_neg_mul_p p x.b
      rw [show (↑(-x.b).val : ZMod (p ^ 2)) * ↑p * x.a = -(↑x.b.val * ↑p) * x.a from by rw [h]]
      rw [neg_mul]
      abel
    · exact neg_add_cancel _

def equiv' (p : ℕ) : SemidirectP2P p ≃ (ZMod (p ^ 2) × ZMod p) where
  toFun g := ⟨g.a, g.b⟩
  invFun t := ⟨t.1, t.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Fintype (SemidirectP2P p) :=
  Fintype.ofEquiv _ (equiv' p).symm

/-- The semidirect product group has order p³. -/
theorem card_semidirectP2P (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (SemidirectP2P p) = p ^ 3 := by
  rw [Nat.card_congr (equiv' p)]
  simp
  ring

@[simp] theorem mul_a' (x y : SemidirectP2P p) :
    (x * y).a = x.a + y.a + (x.b.val : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * y.a := rfl
@[simp] theorem mul_b' (x y : SemidirectP2P p) : (x * y).b = x.b + y.b := rfl
@[simp] theorem one_a' : (1 : SemidirectP2P p).a = 0 := rfl
@[simp] theorem one_b' : (1 : SemidirectP2P p).b = 0 := rfl

/-- The semidirect product is non-abelian for p ≥ 2. -/
theorem semidirectP2P_nonabelian (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ¬ ∀ a b : SemidirectP2P p, a * b = b * a := by
  intro h
  have h12 := h ⟨0, 1⟩ ⟨1, 0⟩
  have ha := congrArg SemidirectP2P.a h12
  simp only [mul_a', ZMod.val_zero, ZMod.val_one'' hp.out.ne_one,
    Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero,
    add_zero, zero_add, mul_one, one_mul] at ha
  have hp_ne : (p : ZMod (p ^ 2)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
    intro hdvd
    have := Nat.le_of_dvd hp.out.pos hdvd
    nlinarith [hp.out.one_lt]
  have hp0 : (↑p : ZMod (p ^ 2)) = 0 :=
    add_left_cancel (show (1 : ZMod (p ^ 2)) + ↑p = 1 + 0 from by rw [add_zero]; exact ha)
  exact hp_ne hp0

private theorem semidirectP2P_pow_b (p : ℕ) [hp : Fact (Nat.Prime p)]
    (x : SemidirectP2P p) (n : ℕ) : (x ^ n).b = (n : ZMod p) * x.b := by
  induction n with
  | zero => simp [pow_zero, one_b']
  | succ n ih =>
    have h_eq := congr_arg SemidirectP2P.b (pow_succ x n)
    rw [h_eq, mul_b', ih, Nat.cast_succ, add_mul, one_mul]

private theorem pow_a_of_b_zero (p : ℕ) [hp : Fact (Nat.Prime p)]
    (y : SemidirectP2P p) (hy : y.b = 0) (k : ℕ) : (y ^ k).a = (k : ZMod (p ^ 2)) * y.a := by
  induction k with
  | zero => simp [pow_zero, one_a']
  | succ n ih =>
    have hbn : (y ^ n).b = 0 := by rw [semidirectP2P_pow_b, hy, mul_zero]
    have h_eq := congr_arg SemidirectP2P.a (pow_succ y n)
    rw [h_eq, mul_a', ih, hbn, ZMod.val_zero, Nat.cast_zero,
        zero_mul, zero_mul, add_zero, Nat.cast_succ, add_mul, one_mul]

private theorem semidirectP2P_pow_a (p : ℕ) [hp : Fact (Nat.Prime p)]
    (x : SemidirectP2P p) (n : ℕ) :
    (x ^ n).a = (n : ZMod (p ^ 2)) * x.a +
      (Nat.choose n 2 : ZMod (p ^ 2)) * ((x.b.val : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * x.a) := by
  induction n with
  | zero => simp [pow_zero, one_a']
  | succ n ih =>
    have h_eq := congr_arg SemidirectP2P.a (pow_succ x n)
    rw [h_eq, mul_a', ih, semidirectP2P_pow_b]
    have hval : ((↑n * x.b).val : ZMod (p ^ 2)) * (↑p : ZMod (p ^ 2)) =
        (n : ZMod (p ^ 2)) * (↑x.b.val * ↑p) := by
      clear ih h_eq
      induction n with
      | zero => simp [ZMod.val_zero]
      | succ m ihm =>
        rw [Nat.cast_succ, add_mul (↑m : ZMod p), one_mul,
            val_mul_p_add, ihm, Nat.cast_succ, add_mul, one_mul]
    rw [hval, Nat.cast_succ, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.cast_add, add_mul, add_mul, one_mul]
    ring

/-- The semidirect product has exponent p². -/
theorem semidirectP2P_exponent (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Monoid.exponent (SemidirectP2P p) = p ^ 2 := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    have hb0 : (x ^ p).b = 0 := by
      rw [semidirectP2P_pow_b, CharP.cast_eq_zero (ZMod p) p, zero_mul]
    rw [show p ^ 2 = p * p from sq p, pow_mul]
    ext
    · rw [pow_a_of_b_zero p _ hb0, one_a']
      rw [semidirectP2P_pow_a p x p]
      have hpp := pp_eq_zero p
      rw [show (↑p : ZMod (p ^ 2)) * ((↑p : ZMod (p ^ 2)) * x.a +
           (↑(Nat.choose p 2) : ZMod (p ^ 2)) * ((x.b.val : ZMod (p ^ 2)) * ↑p * x.a)) =
          ↑p * ↑p * x.a + ↑(Nat.choose p 2) * x.b.val * (↑p * ↑p) * x.a from by ring]
      simp [hpp]
    · rw [semidirectP2P_pow_b, one_b', hb0, mul_zero]
  · have hord : orderOf (⟨1, 0⟩ : SemidirectP2P p) = p ^ 2 := by
      apply orderOf_eq_prime_pow
      · rw [pow_one]
        have ha := pow_a_of_b_zero p ⟨1, (0 : ZMod p)⟩ rfl p
        intro hpow
        have := congrArg SemidirectP2P.a hpow
        rw [ha, one_a', mul_one] at this
        have hdvd : (p ^ 2 : ℕ) ∣ p := by
          rwa [CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)] at this
        have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.out.pos hdvd
        have hp1 := hp.out.one_lt
        nlinarith
      · have hb0 : (⟨(1 : ZMod (p ^ 2)), (0 : ZMod p)⟩ : SemidirectP2P p).b = 0 := rfl
        have ha := pow_a_of_b_zero p ⟨1, (0 : ZMod p)⟩ rfl (p ^ 2)
        ext
        · rw [ha, one_a', mul_one, CharP.cast_eq_zero (ZMod (p ^ 2)) (p ^ 2)]
        · rw [semidirectP2P_pow_b, one_b', mul_zero]
    calc p ^ 2 = orderOf (⟨1, 0⟩ : SemidirectP2P p) := hord.symm
      _ ∣ Monoid.exponent (SemidirectP2P p) := Monoid.order_dvd_exponent _

end SemidirectP2P

/-! ### The p = 2 case: D₄ and Q₈ -/

section PrimeTwo

/-- D₄ has order 8. -/
theorem card_dihedral4 : Nat.card (DihedralGroup 4) = 2 ^ 3 := by
  rw [DihedralGroup.nat_card]; norm_num

/-- D₄ is non-abelian. -/
theorem dihedral4_nonabelian : ¬ ∀ a b : DihedralGroup 4, a * b = b * a := by
  intro h
  have h1 := h (DihedralGroup.r 1) (DihedralGroup.sr 0)
  simp [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
  exact absurd h1 (by decide)

/-- Q₈ has order 8. -/
theorem card_quaternion8 : Nat.card (QuaternionGroup 2) = 2 ^ 3 := by
  simp [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- Q₈ is non-abelian. -/
theorem quaternion8_nonabelian : ¬ ∀ a b : QuaternionGroup 2, a * b = b * a := by
  intro h
  have h1 := h (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
  simp [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
  exact absurd h1 (by decide)

/-- D₄ and Q₈ are not isomorphic. -/
theorem dihedral4_not_iso_quaternion8 : IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2) := by
  constructor
  intro f
  have hsr : ∀ i : ZMod 4, (DihedralGroup.sr i) ^ 2 = (1 : DihedralGroup 4) := by
    decide +kernel
  have huniq : ∀ x : QuaternionGroup 2, x ^ 2 = 1 → x = 1 ∨ x = QuaternionGroup.a 2 := by
    decide +kernel
  have h0 := huniq (f (DihedralGroup.sr 0)) (by rw [← map_pow, hsr, map_one])
  have h1 := huniq (f (DihedralGroup.sr 1)) (by rw [← map_pow, hsr, map_one])
  have h2 := huniq (f (DihedralGroup.sr 2)) (by rw [← map_pow, hsr, map_one])
  have hne : DihedralGroup.sr (0 : ZMod 4) ≠ DihedralGroup.sr 1 := by decide
  have hinj := f.injective
  have hne_1_0 : DihedralGroup.sr (0 : ZMod 4) ≠ 1 := by decide
  have hne_1_1 : DihedralGroup.sr (1 : ZMod 4) ≠ 1 := by decide
  rcases h0 with h0 | h0
  · exact absurd (hinj (h0 ▸ (map_one f).symm)) hne_1_0
  · rcases h1 with h1 | h1
    · exact absurd (hinj (h1 ▸ (map_one f).symm)) hne_1_1
    · exact absurd (hinj (h0 ▸ h1 ▸ rfl)) hne

end PrimeTwo

/-! ### Exponent dichotomy -/

/-- A non-abelian group of order p³ has exponent either p or p². -/
theorem exponent_of_nonabelian_p3 (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) : Monoid.exponent G = p ∨ Monoid.exponent G = p ^ 2 := by
  have hprime := hp.out
  have hexp_dvd : Monoid.exponent G ∣ p ^ 3 := by
    rw [← hcard]; exact Group.exponent_dvd_nat_card
  obtain ⟨k, hk3, hkexp⟩ := (Nat.dvd_prime_pow hprime).mp hexp_dvd
  have hexp_pos : 0 < Monoid.exponent G := Monoid.exponent_ne_zero_of_finite.bot_lt
  have hk_ne_0 : k ≠ 0 := by
    intro hk0; subst hk0; simp at hkexp
    have hnt : Nontrivial G := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
      exact Nat.one_lt_pow (by omega) hprime.one_lt
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    have : g ^ 1 = 1 := by rw [← hkexp]; exact Monoid.pow_exponent_eq_one g
    rw [pow_one] at this; exact hg this
  have hk_ne_3 : k ≠ 3 := by
    intro hk3'; subst hk3'
    have hpG := isPGroup_of_card_eq_p3 hcard
    have hord_dvd : ∀ g : G, orderOf g ∣ p ^ 3 := fun g => hcard ▸ @orderOf_dvd_natCard G _ g
    have hcyc : ∃ g : G, orderOf g = p ^ 3 := by
      by_contra h; push Not at h
      have hord_le : ∀ g : G, orderOf g ∣ p ^ 2 := by
        intro g
        obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hpG) g
        rw [hj]
        have hjle : j ≤ 3 := by
          rw [← Nat.pow_dvd_pow_iff_le_right hprime.one_lt, ← hj]
          exact hord_dvd g
        have hjne3 : j ≠ 3 := fun hj3 => h g (by rw [hj, hj3])
        exact Nat.pow_dvd_pow p (by omega)
      have hexple : Monoid.exponent G ∣ p ^ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => orderOf_dvd_iff_pow_eq_one.mp (hord_le g)
      rw [hkexp] at hexple
      exact absurd ((Nat.pow_dvd_pow_iff_le_right hprime.one_lt).mp hexple) (by omega)
    obtain ⟨g, hg⟩ := hcyc
    rw [← hcard] at hg
    exact hnonab (fun a b => by
      haveI : IsCyclic G := isCyclic_of_orderOf_eq_card g hg
      exact IsCyclic.commGroup.mul_comm a b)
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl
  · left; simpa using hkexp
  · right; exact hkexp

/-! ### Main non-abelian classification -/

private lemma orderOf_eq_prime_of_pow_one {x : G} (hpow : x ^ p = 1) (hx1 : x ≠ 1) :
    orderOf x = p := by
  have h_dvd : orderOf x ∣ p := by rw [orderOf_dvd_iff_pow_eq_one]; exact hpow
  rcases hp.out.eq_one_or_self_of_dvd _ h_dvd with (h1 | hp')
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact hp'

private lemma closure_abelian_of_comm {a₀ b₀ : G} (h_comm : a₀ * b₀ = b₀ * a₀) :
    IsMulCommutative (Subgroup.closure ({a₀, b₀} : Set G)) := by
  let S : Set G := {a₀, b₀}
  let K : Subgroup G := Subgroup.closure S
  -- K is contained in the centralizer of a₀
  have hK_Ca : K ≤ Subgroup.centralizer ({a₀} : Set G) :=
    (Subgroup.closure_le (k := S) (K := Subgroup.centralizer ({a₀} : Set G))).mpr
      (by
        intro g hg
        have h_cases : g = a₀ ∨ g = b₀ := by simpa [S] using hg
        rcases h_cases with (rfl | rfl)
        · apply mem_centralizer_singleton_iff.mpr; rfl
        · apply mem_centralizer_singleton_iff.mpr; exact h_comm.symm)
  -- K is contained in the centralizer of b₀
  have hK_Cb : K ≤ Subgroup.centralizer ({b₀} : Set G) :=
    (Subgroup.closure_le (k := S) (K := Subgroup.centralizer ({b₀} : Set G))).mpr
      (by
        intro g hg
        have h_cases : g = a₀ ∨ g = b₀ := by simpa [S] using hg
        rcases h_cases with (rfl | rfl)
        · apply mem_centralizer_singleton_iff.mpr; exact h_comm
        · apply mem_centralizer_singleton_iff.mpr; rfl)
  -- Now prove commutativity for any two elements of K
  refine { is_comm := ⟨fun a b => ?_⟩ }
  have ha_comm_a₀ : (a : G) * a₀ = a₀ * (a : G) :=
    mem_centralizer_singleton_iff.mp (hK_Ca a.2)
  have ha_comm_b₀ : (a : G) * b₀ = b₀ * (a : G) :=
    mem_centralizer_singleton_iff.mp (hK_Cb a.2)
  -- a commutes with the generators, so the centralizer of a contains the generators
  let Ca : Subgroup G := Subgroup.centralizer ({(a : G)} : Set G)
  have ha₀_Ca : a₀ ∈ Ca := mem_centralizer_singleton_iff.mpr ha_comm_a₀.symm
  have hb₀_Ca : b₀ ∈ Ca := mem_centralizer_singleton_iff.mpr ha_comm_b₀.symm
  have hK_sub_Ca : K ≤ Ca :=
    (Subgroup.closure_le (k := S) (K := Ca)).mpr (by
      intro g hg
      have h_cases : g = a₀ ∨ g = b₀ := by simpa [S] using hg
      rcases h_cases with (rfl | rfl)
      · exact ha₀_Ca
      · exact hb₀_Ca)
  have hb_Ca' : (b : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := hK_sub_Ca b.2
  have hb_comm_a : (b : G) * (a : G) = (a : G) * (b : G) := by
    rw [Subgroup.mem_centralizer_iff] at hb_Ca'
    have h := hb_Ca' (a : G) (by simp)
    rw [h]
  exact Subtype.ext hb_comm_a.symm

private lemma exists_orderOf_p_sq (hexp : Monoid.exponent G = p ^ 2) :
∃ x : G, orderOf x = p ^ 2 := by
  have hprime := hp.out
  by_contra h_no
  push Not at h_no
  have h_all_ord : ∀ g : G, orderOf g ∣ p := by
    intro g
    have h_ord_exp : orderOf g ∣ p ^ 2 := by
      rw [← hexp]; exact Monoid.order_dvd_exponent g
    obtain ⟨j, hj, h_ord⟩ := (Nat.dvd_prime_pow hprime).mp h_ord_exp
    have hj_ne_2 : j ≠ 2 := by
      intro hj2; subst hj2; exact h_no g h_ord
    have hj_le_1 : j ≤ 1 := by omega
    rw [h_ord]
    simpa [pow_one] using Nat.pow_dvd_pow p hj_le_1
  have h_exp_dvd_p : Monoid.exponent G ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
      rw [← orderOf_dvd_iff_pow_eq_one]; exact h_all_ord g
  rw [hexp] at h_exp_dvd_p
  have hp_gt_1 : 1 < p := hprime.one_lt
  have hp2_gt_p : p < p ^ 2 := by nlinarith
  have hle := Nat.le_of_dvd (by omega) h_exp_dvd_p
  omega

private lemma zpowers_normal_of_index_p (x : G) (hx_card : Nat.card (zpowers x) = p ^ 2)
    (hcard : Nat.card G = p ^ 3) : (zpowers x).Normal := by
  have hindex : (zpowers x).index = p := by
    have h := Subgroup.index_mul_card (zpowers x)
    rw [hx_card, hcard] at h
    have hp_ne_zero : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.out.ne_zero
    have h' : p ^ 2 * (zpowers x).index = p ^ 2 * p := by nlinarith
    exact mul_left_cancel₀ hp_ne_zero h'
  have h_minFac : Nat.minFac (p ^ 3) = p := by
    have hp3_ne_one : p ^ 3 ≠ 1 := by
      have h : 1 < p ^ 3 := Nat.one_lt_pow (by omega) hp.out.one_lt
      omega
    have h_minFac_prime : Nat.Prime (Nat.minFac (p ^ 3)) := Nat.minFac_prime hp3_ne_one
    have h_dvd : Nat.minFac (p ^ 3) ∣ p ^ 3 := Nat.minFac_dvd _
    have h_dvd_p : Nat.minFac (p ^ 3) ∣ p :=
      h_minFac_prime.dvd_of_dvd_pow h_dvd
    exact (Nat.prime_dvd_prime_iff_eq h_minFac_prime hp.out).mp h_dvd_p
  have hcard_minFac : Nat.minFac (Nat.card G) = p := by
    rw [hcard, h_minFac]
  have hindex_eq : (zpowers x).index = Nat.minFac (Nat.card G) := by
    rw [hcard_minFac, hindex]
  exact Subgroup.normal_of_index_eq_minFac_card hindex_eq

private lemma commutator_mem_center_of_p3 {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) (a b : G) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G := by
  haveI : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
  have hqcard := quotient_center_card_eq_p2 (p := p) hcard hnonab
  have hqcomm := comm_of_card_p2 (p := p) hqcard
  rw [← QuotientGroup.eq_one_iff]
  have : (↑(a * b * a⁻¹ * b⁻¹) : G ⧸ Subgroup.center G) =
      ↑a * ↑b * (↑a)⁻¹ * (↑b)⁻¹ := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [this, hqcomm (↑a) (↑b)]; group

/-- Helper: for x with orderOf x = n, x^((a+b) % n) = x^a * x^b. -/
private theorem pow_zmod_add {G : Type*} [Group G] {x : G} {n : ℕ}
    (hn : orderOf x = n) [NeZero n] (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, pow_mod_orderOf x (a.val + b.val) |>.symm,
      hn]

/-- Helper: for x with orderOf x = n, x^((a*b) % n) = x^(a.val * b.val). -/
private theorem pow_zmod_mul {G : Type*} [Group G] {x : G} {n : ℕ}
    (hn : orderOf x = n) [NeZero n] (a b : ZMod n) :
    x ^ (a * b).val = x ^ (a.val * b.val) := by
  conv_rhs => rw [← pow_mod_orderOf, hn]
  congr 1; exact ZMod.val_mul a b

private lemma pow_mul_comm_right {G : Type*} [Group G] {x y z : G}
    (hcent : z ∈ Subgroup.center G)
    (hrel : x * y = y * x * z) (n : ℕ) :
    x * y ^ n = y ^ n * x * z ^ n := by
  have hzcomm : ∀ g : G, Commute z g := fun g =>
    (show Commute g z from Subgroup.mem_center_iff.mp hcent g).symm
  have hconj : x * y * x⁻¹ = y * z := by
    rw [hrel, mul_assoc (y * x) z x⁻¹, (hzcomm x⁻¹).eq,
        ← mul_assoc (y * x) x⁻¹ z, mul_assoc y x x⁻¹,
        mul_inv_cancel, mul_one]
  suffices h : x * y ^ n * x⁻¹ = (y * z) ^ n by
    conv_lhs => rw [show x * y ^ n = x * y ^ n * x⁻¹ * x from by group]
    rw [h, (hzcomm y).symm.mul_pow, mul_assoc,
        (hzcomm x).pow_left n |>.eq, ← mul_assoc]
  induction n with
  | zero => simp
  | succ n ihn =>
    calc x * y ^ (n + 1) * x⁻¹
        = x * y ^ n * x⁻¹ * (x * y * x⁻¹) := by rw [pow_succ]; group
      _ = (y * z) ^ n * (y * z) := by rw [ihn, hconj]
      _ = (y * z) ^ (n + 1) := (pow_succ _ _).symm

private lemma pow_mul_comm_left {G : Type*} [Group G] {x y z : G}
    (hcent : z ∈ Subgroup.center G)
    (hrel : x * y = y * x * z) (m : ℕ) :
    x ^ m * y = y * x ^ m * z ^ m := by
  have hzcomm : ∀ g : G, Commute z g := fun g =>
    (show Commute g z from Subgroup.mem_center_iff.mp hcent g).symm
  induction m with
  | zero => simp
  | succ m ihm =>
    calc x ^ (m + 1) * y = x * (x ^ m * y) := by rw [pow_succ', mul_assoc]
      _ = x * (y * x ^ m * z ^ m) := by rw [ihm]
      _ = (x * y) * x ^ m * z ^ m := by
          simp only [mul_assoc]
      _ = y * x * z * x ^ m * z ^ m := by rw [hrel]
      _ = y * x ^ (m + 1) * z ^ (m + 1) := by
          rw [mul_assoc (y * x) z (x ^ m), (hzcomm (x ^ m)).eq,
              ← mul_assoc (y * x) (x ^ m) z, mul_assoc y x (x ^ m),
              ← pow_succ', mul_assoc (y * x ^ (m + 1)) z (z ^ m),
              ← pow_succ']

private lemma pow_mul_pow_comm {G : Type*} [Group G] {x y z : G}
    (hcent : z ∈ Subgroup.center G)
    (hrel : x * y = y * x * z) (m n : ℕ) :
    x ^ m * y ^ n = y ^ n * x ^ m * z ^ (m * n) := by
  have hzm_cent : z ^ m ∈ Subgroup.center G := (Subgroup.center G).pow_mem hcent m
  have hrel_m : x ^ m * y = y * x ^ m * z ^ m := pow_mul_comm_left hcent hrel m
  have h := pow_mul_comm_right hzm_cent hrel_m n
  rwa [← pow_mul] at h

private lemma heisenberg_mul_identity {G : Type*} [Group G] {x y z : G}
    (hcent : z ∈ Subgroup.center G)
    (hrel : x * y = y * x * z)
    (a₁ a₂ b₁ b₂ c₁ c₂ : ℕ) :
    y ^ b₁ * x ^ a₁ * z ^ c₁ * (y ^ b₂ * x ^ a₂ * z ^ c₂) =
    y ^ (b₁ + b₂) * x ^ (a₁ + a₂) * z ^ (a₁ * b₂ + c₁ + c₂) := by
  have hzc : ∀ (n : ℕ) (g : G), Commute (z ^ n) g := fun n g =>
    (Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem hcent n) g).symm
  have hxyz := pow_mul_pow_comm hcent hrel a₁ b₂
  -- Flatten LHS: remove inner parens
  rw [← mul_assoc (y ^ b₁ * x ^ a₁ * z ^ c₁) (y ^ b₂ * x ^ a₂) (z ^ c₂),
      ← mul_assoc (y ^ b₁ * x ^ a₁ * z ^ c₁) (y ^ b₂) (x ^ a₂)]
  -- LHS: y^b₁ * x^a₁ * z^c₁ * y^b₂ * x^a₂ * z^c₂
  -- Move z^c₁ past y^b₂
  rw [mul_assoc (y ^ b₁ * x ^ a₁) (z ^ c₁) (y ^ b₂),
      (hzc c₁ (y ^ b₂)).eq,
      ← mul_assoc (y ^ b₁ * x ^ a₁) (y ^ b₂) (z ^ c₁)]
  -- LHS: y^b₁ * x^a₁ * y^b₂ * z^c₁ * x^a₂ * z^c₂
  -- Move z^c₁ past x^a₂
  rw [mul_assoc (y ^ b₁ * x ^ a₁ * y ^ b₂) (z ^ c₁) (x ^ a₂),
      (hzc c₁ (x ^ a₂)).eq,
      ← mul_assoc (y ^ b₁ * x ^ a₁ * y ^ b₂) (x ^ a₂) (z ^ c₁)]
  -- LHS: y^b₁ * x^a₁ * y^b₂ * x^a₂ * z^c₁ * z^c₂
  -- Swap x^a₁ * y^b₂ using hxyz
  rw [mul_assoc (y ^ b₁) (x ^ a₁) (y ^ b₂), hxyz,
      ← mul_assoc (y ^ b₁) (y ^ b₂ * x ^ a₁) (z ^ (a₁ * b₂)),
      ← mul_assoc (y ^ b₁) (y ^ b₂) (x ^ a₁)]
  -- LHS: y^b₁ * y^b₂ * x^a₁ * z^(a₁*b₂) * x^a₂ * z^c₁ * z^c₂
  -- Move z^(a₁*b₂) past x^a₂
  rw [mul_assoc (y ^ b₁ * y ^ b₂ * x ^ a₁) (z ^ (a₁ * b₂)) (x ^ a₂),
      (hzc (a₁ * b₂) (x ^ a₂)).eq,
      ← mul_assoc (y ^ b₁ * y ^ b₂ * x ^ a₁) (x ^ a₂) (z ^ (a₁ * b₂))]
  -- LHS: y^b₁ * y^b₂ * x^a₁ * x^a₂ * z^(a₁*b₂) * z^c₁ * z^c₂
  -- Combine all powers
  rw [← pow_add y b₁ b₂,
      mul_assoc (y ^ (b₁ + b₂)) (x ^ a₁) (x ^ a₂), ← pow_add x a₁ a₂]
  -- Now: y^(b₁+b₂) * x^(a₁+a₂) * z^(a₁*b₂) * z^c₁ * z^c₂
  -- = y^(b₁+b₂) * x^(a₁+a₂) * z^(a₁*b₂+c₁+c₂)
  simp only [mul_assoc, ← pow_add]

/-! #### Exponent p case: Heisenberg group -/

private lemma heisenberg_of_exponent_p (hexp : Monoid.exponent G = p)
    (hcard : Nat.card G = p ^ 3) (hnonab : ¬ ∀ a b : G, a * b = b * a)
    (_ : p ≠ 2) :
    Nonempty (G ≃* HeisenbergGroup p) := by
    have hprime := hp.out
    have hpow : ∀ g : G, g ^ p = 1 := fun g => by
      have := Monoid.pow_exponent_eq_one (G := G) g; rwa [hexp] at this
    -- Find non-commuting elements
    obtain ⟨x, y, hxy⟩ : ∃ x y : G, x * y ≠ y * x := by
      by_contra h; push Not at h; exact hnonab h
    -- Set z = commutator
    set z := x⁻¹ * y⁻¹ * x * y with hz_def
    -- z is non-trivial
    have hzne : z ≠ 1 := by
      intro heq; apply hxy
      have : x⁻¹ * y⁻¹ * x * y = 1 := heq
      calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
        _ = y * x * 1 := by rw [this]
        _ = y * x := mul_one _
    -- z is central (using commutator_mem_center_of_p3 with a=x⁻¹, b=y⁻¹)
    have hzcent : z ∈ Subgroup.center G := by
      have h := commutator_mem_center_of_p3 (p := p) hcard hnonab x⁻¹ y⁻¹
      simp only [inv_inv] at h
      exact h
    -- multiplication relation
    have hrel : x * y = y * x * z := by
      rw [hz_def]; group
    -- All non-identity elements have order p
    have hord_eq_p : ∀ g : G, g ≠ 1 → orderOf g = p := by
      intro g hg
      exact (hprime.eq_one_or_self_of_dvd _
        (orderOf_dvd_of_pow_eq_one (hpow g))).resolve_left
        (mt orderOf_eq_one_iff.mp hg)
    have hxne : x ≠ 1 := by intro h; apply hxy; rw [h]; simp
    have hyne : y ≠ 1 := by intro h; apply hxy; rw [h]; simp
    have hxord : orderOf x = p := hord_eq_p x hxne
    have hyord : orderOf y = p := hord_eq_p y hyne
    have hzord : orderOf z = p := hord_eq_p z hzne
    -- Define the map f : HeisenbergGroup p → G
    let fFun : HeisenbergGroup p → G := fun ⟨a, b, c⟩ =>
      y ^ b.val * x ^ a.val * z ^ c.val
    -- f is a group homomorphism
    have hmul : ∀ g₁ g₂ : HeisenbergGroup p, fFun (g₁ * g₂) = fFun g₁ * fFun g₂ := by
      intro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩
      show y ^ (b₁ + b₂).val * x ^ (a₁ + a₂).val * z ^ (c₁ + c₂ + a₁ * b₂).val =
        y ^ b₁.val * x ^ a₁.val * z ^ c₁.val *
        (y ^ b₂.val * x ^ a₂.val * z ^ c₂.val)
      rw [pow_zmod_add hyord, pow_zmod_add hxord,
          pow_zmod_add hzord (c₁ + c₂) (a₁ * b₂),
          pow_zmod_add hzord c₁ c₂, pow_zmod_mul hzord]
      simp only [← pow_add]
      rw [show c₁.val + c₂.val + a₁.val * b₂.val =
            a₁.val * b₂.val + c₁.val + c₂.val from by ring]
      exact (heisenberg_mul_identity hzcent hrel a₁.val a₂.val
        b₁.val b₂.val c₁.val c₂.val).symm
    let f := MonoidHom.mk' fFun hmul
    -- f is injective: show kernel is trivial
    have hzmod_pow_one : ∀ (a : ZMod p), a ≠ 0 → z ^ a.val ≠ 1 := by
      intro a ha heq
      have hdvd : p ∣ a.val := by
        have := orderOf_dvd_of_pow_eq_one heq; rwa [hzord] at this
      have := Nat.eq_zero_of_dvd_of_lt hdvd a.val_lt
      exact ha ((ZMod.val_eq_zero a).mp this)
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro ⟨a, b, c⟩ hmem
      simp only [MonoidHom.mem_ker, Subgroup.mem_bot] at hmem ⊢
      -- hmem : y^b.val * x^a.val * z^c.val = 1
      have hmem' : y ^ b.val * x ^ a.val * z ^ c.val = 1 := hmem
      -- y^b * x^a = (z^c)⁻¹ ∈ Z(G)
      have hyx_eq : y ^ b.val * x ^ a.val = (z ^ c.val)⁻¹ :=
        mul_eq_one_iff_eq_inv.mp hmem'
      have hyx_cent : y ^ b.val * x ^ a.val ∈ Subgroup.center G := by
        rw [hyx_eq]; exact (Subgroup.center G).inv_mem
          ((Subgroup.center G).pow_mem hzcent c.val)
      -- Commuting y^b * x^a with y forces z^a = 1, hence a = 0
      have ha : a = 0 := by
        by_contra ha_ne
        have h2 : x ^ a.val * y = y * x ^ a.val * z ^ a.val :=
          pow_mul_comm_left hzcent hrel a.val
        have hcomm := (Subgroup.mem_center_iff.mp hyx_cent y).symm
        apply hzmod_pow_one a ha_ne
        have hlhs : (y ^ b.val * x ^ a.val) * y =
            y ^ (b.val + 1) * x ^ a.val := by rw [hcomm]; group
        have hrhs : (y ^ b.val * x ^ a.val) * y =
            y ^ (b.val + 1) * x ^ a.val * z ^ a.val := by
          calc _ = y ^ b.val * (x ^ a.val * y) := by group
            _ = y ^ b.val * (y * x ^ a.val * z ^ a.val) := by rw [h2]
            _ = _ := by group
        rw [hlhs] at hrhs
        exact mul_eq_left.mp hrhs.symm
      -- Commuting y^b (since a=0) with x forces z^b = 1, hence b = 0
      have hb : b = 0 := by
        by_contra hb_ne
        have hyx_cent' : y ^ b.val ∈ Subgroup.center G := by
          convert hyx_cent using 1; rw [ha]; simp
        have h2 : x * y ^ b.val = y ^ b.val * x * z ^ b.val :=
          pow_mul_comm_right hzcent hrel b.val
        have hcomm := (Subgroup.mem_center_iff.mp hyx_cent' x).symm
        apply hzmod_pow_one b hb_ne
        have : y ^ b.val * x * z ^ b.val = y ^ b.val * x := by
          rw [← h2, hcomm]
        exact mul_eq_left.mp this
      -- With a=b=0, z^c = 1, hence c = 0
      have hc : c = 0 := by
        by_contra hc_ne
        apply hzmod_pow_one c hc_ne
        rw [ha, hb] at hmem'
        simpa using hmem'
      exact HeisenbergGroup.ext ha hb hc
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hinj, ?_⟩
      rw [show Fintype.card (HeisenbergGroup p) = p ^ 3 from by
            rw [← Nat.card_eq_fintype_card]; exact HeisenbergGroup.card_heisenberg p,
          ← Nat.card_eq_fintype_card, hcard]
    exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

private lemma one_add_mul_p_pow_inv
    {p k r : ℕ}
    [Fact p.Prime]
    (_ : Nat.Coprime k p)
    (hr : r * k ≡ 1 [MOD p]) :
    (1 + k * p) ^ r ≡ 1 + p [MOD p ^ 2] := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_gt_one : 1 < p := hp_prime.one_lt
  -- Step 1: prove by induction that for all r, (1 + kp)^r ≡ 1 + rkp [MOD p^2]
  -- We separate this to avoid induction dependency on hr
  have h_expand_all : ∀ (n : ℕ), (1 + k * p) ^ n ≡ 1 + n * k * p [MOD p ^ 2] := by
    intro n
    induction n with
    | zero => simp [Nat.ModEq]
    | succ n ih =>
      calc
        (1 + k * p) ^ (n + 1) = (1 + k * p) ^ n * (1 + k * p) := by ring
        _ ≡ (1 + n * k * p) * (1 + k * p) [MOD p ^ 2] :=
          Nat.ModEq.mul ih (Nat.ModEq.refl _)
        _ = 1 + k * p + n * k * p + n * k * p * (k * p) := by ring
        _ = 1 + (n + 1) * k * p + n * k ^ 2 * p ^ 2 := by ring
        _ ≡ 1 + (n + 1) * k * p [MOD p ^ 2] := by
          have h_vanishes : n * k ^ 2 * p ^ 2 ≡ 0 [MOD p ^ 2] :=
            (Nat.modEq_zero_iff_dvd.mpr ⟨n * k ^ 2, by ring⟩)
          simpa [add_comm, add_left_comm, add_assoc] using
            Nat.ModEq.add (Nat.ModEq.refl (1 + (n + 1) * k * p)) h_vanishes
  have h_expand : (1 + k * p) ^ r ≡ 1 + r * k * p [MOD p ^ 2] := h_expand_all r
  -- Step 2: from hr (r*k ≡ 1 [MOD p]), show r*k*p ≡ p [MOD p^2]
  have h_rkp : r * k * p ≡ p [MOD p ^ 2] := by
    -- hr: (r*k) % p = 1 % p
    have h_mod_val : (r * k) % p = 1 := by
      rw [Nat.ModEq] at hr
      rw [show (1 : ℕ) % p = 1 from Nat.mod_eq_of_lt hp_gt_one] at hr
      exact hr
    -- Write r*k = q*p + 1 where q = (r*k)/p
    have h_eq : r * k = ((r * k) / p) * p + 1 := by
      calc
        r * k = p * ((r * k) / p) + (r * k) % p := (Nat.div_add_mod (r * k) p).symm
        _ = ((r * k) / p) * p + (r * k) % p := by rw [mul_comm]
        _ = ((r * k) / p) * p + 1 := by rw [h_mod_val]
    rw [h_eq]
    -- (q*p + 1)*p = q*p^2 + p
    rw [add_mul, one_mul]
    rw [show (((r * k) / p) * p) * p = ((r * k) / p) * p ^ 2 by ring]
    -- Now: q*p^2 + p ≡ p [MOD p^2]
    have h_dvd : p ^ 2 ∣ ((r * k) / p) * p ^ 2 := ⟨(r * k) / p, by ring⟩
    have h_zero : ((r * k) / p) * p ^ 2 ≡ 0 [MOD p ^ 2] :=
      (Nat.modEq_zero_iff_dvd.mpr h_dvd)
    simpa [add_comm] using Nat.ModEq.add (Nat.ModEq.refl p) h_zero
  -- Combine: (1+kp)^r ≡ 1+rkp ≡ 1+p [MOD p^2]
  have h_sum : 1 + r * k * p ≡ 1 + p [MOD p ^ 2] :=
    Nat.ModEq.add (Nat.ModEq.refl 1) h_rkp
  exact h_expand.trans h_sum

  -- proof using binomial theorem
private lemma conjugation_iterate'
    {x y : G} : ∀ n,
    y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero]; group
  | succ n ih =>
  calc
    y * x ^ (n + 1) * y⁻¹ = (y * x * y⁻¹) * (y * x ^ n * y⁻¹) := by group
    _ = (y * x * y⁻¹) * (y * x * y⁻¹) ^ n := by rw [ih]
    _ = (y * x * y⁻¹) ^ (n + 1) := by group

private lemma conjugation_iterate
    {x y : G}
    (h : y * x * y⁻¹ = x ^ m) :
    ∀ n,
    y^n * x * (y^n)⁻¹ = x^(m^n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
  calc
    y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y ⁻¹ := by group
    _ = y * x ^ (m ^ n) * y ⁻¹ := by rw [ih]
    _ = (y * x * y⁻¹) ^ (m ^ n) := by rw [conjugation_iterate']
    _ = x ^ (m ^ (n + 1)) := by rw [h]; group

private lemma normalize_conjugation_power
    {G : Type*} [Group G] [Fintype G] {p k r : ℕ}
    [Fact p.Prime]
    {x y : G}
    (hx : orderOf x = p ^ 2)
    (hconj : y * x * y⁻¹ = x ^ (1 + k * p))
    (hk : Nat.Coprime k p)
    (hr : r * k ≡ 1 [MOD p]) :
    y ^ r * x * (y ^ r)⁻¹ = x ^ (1 + p) := by
  have h_iterate := conjugation_iterate hconj r
  -- h_iterate: y^r * x * (y^r)⁻¹ = x ^ ((1 + k * p) ^ r)
  rw [h_iterate]
  -- Now need x^((1+k*p)^r) = x^(1+p)
  -- Using one_add_mul_p_pow_inv and the fact that orderOf x = p^2
  have h_mod : (1 + k * p) ^ r ≡ 1 + p [MOD p ^ 2] :=
    one_add_mul_p_pow_inv hk hr
  -- Reduce both exponents modulo p^2 using pow_mod_orderOf
  have h_exp_eq : x ^ ((1 + k * p) ^ r) = x ^ (1 + p) := by
    calc
      x ^ ((1 + k * p) ^ r) = x ^ (((1 + k * p) ^ r) % orderOf x) := by
        rw [pow_mod_orderOf]
      _ = x ^ (((1 + k * p) ^ r) % (p ^ 2)) := by rw [hx]
      _ = x ^ ((1 + p) % (p ^ 2)) := by rw [h_mod]
      _ = x ^ (1 + p) := by
        rw [show (1 + p) % (p ^ 2) = 1 + p from
          Nat.mod_eq_of_lt (by
            have hp_prime : Nat.Prime p := Fact.out
            have hp_gt_1 : 1 < p := hp_prime.one_lt
            have : p ^ 2 > 1 + p := by
              nlinarith
            exact this)]
  exact h_exp_eq

private lemma normalize_conjugation_to_one_add_p
    {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    {x y : G}
    (hx : orderOf x = p ^ 2)
    (hy_not_mem : y ∉ zpowers x)
    (hconj_mem : y * x * y⁻¹ ∈ zpowers x)
    (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    ∃ y' : G,
      y' ∉ zpowers x ∧
      y' * x * y'⁻¹ = x ^ (1 + p) := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp_prime.pos
  -- Step 1: from hconj_mem, get integer k with x^k = y*x*y⁻¹
  rw [Subgroup.mem_zpowers_iff] at hconj_mem
  rcases hconj_mem with ⟨k, hk⟩
  -- hk : x ^ k = y * x * y⁻¹, where k : ℤ
  -- Reduce k modulo p^2 to get m_int in [0, p^2-1]
  have hp2_pos_int : (0 : ℤ) < p ^ 2 := by exact_mod_cast pow_pos hp_pos 2
  set m_int := k % (p ^ 2 : ℤ) with hm_int_def
  have hm_int_nn : 0 ≤ m_int := Int.emod_nonneg k (by
    have : (p ^ 2 : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hp_prime.ne_zero
    exact this)
  have hm_int_lt : m_int < (p ^ 2 : ℤ) := Int.emod_lt_of_pos k hp2_pos_int
  have hk_mod : x ^ k = x ^ m_int := by
    calc
      x ^ k = x ^ (k % (↑(orderOf x) : ℤ)) := by rw [zpow_mod_orderOf x k]
      _ = x ^ (k % (p ^ 2 : ℤ)) := by
        have h_cast : (orderOf x : ℤ) = (p ^ 2 : ℤ) := by exact_mod_cast hx
        rw [h_cast]
      _ = x ^ m_int := by rfl
  -- So x^m_int = y*x*y⁻¹
  have h_conj_zpow : x ^ m_int = y * x * y⁻¹ := by rw [← hk_mod, hk]
  -- Since conjugation preserves order, orderOf(x^m_int) = p^2
  have h_ord_conj : orderOf (x ^ m_int) = p ^ 2 := by
    rw [h_conj_zpow]
    have hsemi : SemiconjBy y x (y * x * y⁻¹) := by
      show y * x = y * x * y⁻¹ * y; group
    exact (SemiconjBy.orderOf_eq y hsemi).symm.trans hx
  -- Convert m_int to ℕ
  let m_nat : ℕ := m_int.toNat
  have hm_nat_eq_int : (m_nat : ℤ) = m_int := Int.toNat_of_nonneg hm_int_nn
  have hm_nat_lt_p2 : m_nat < p ^ 2 := by
    have h_lt_int : (m_nat : ℤ) < (p ^ 2 : ℤ) := by
      rw [hm_nat_eq_int]
      exact hm_int_lt
    exact_mod_cast h_lt_int
  have hx_m_nat : x ^ m_int = x ^ m_nat := by
    calc
      x ^ m_int = x ^ (m_nat : ℤ) := by rw [← hm_nat_eq_int]
      _ = x ^ m_nat := by rw [zpow_natCast]
  have h_conj_nat : x ^ m_nat = y * x * y⁻¹ := by rw [← hx_m_nat, h_conj_zpow]
  -- Step 2: m_nat is coprime to p^2 (since conjugation preserves order)
  have h_ord_nat : orderOf (x ^ m_nat) = p ^ 2 := by
    rw [h_conj_nat]
    have hsemi : SemiconjBy y x (y * x * y⁻¹) := by
      show y * x = y * x * y⁻¹ * y; group
    exact (SemiconjBy.orderOf_eq y hsemi).symm.trans hx
  have h_gcd_p2 : Nat.gcd (p ^ 2) m_nat = 1 := by
    rw [orderOf_pow x (n := m_nat), hx] at h_ord_nat
    by_contra h_not
    have hp2pos : 0 < p ^ 2 := pow_pos hp_pos 2
    have h_gt : 1 < Nat.gcd (p ^ 2) m_nat := by
      have hpos : 0 < Nat.gcd (p ^ 2) m_nat := Nat.gcd_pos_of_pos_left m_nat hp2pos
      omega
    have h_div_lt : (p ^ 2) / Nat.gcd (p ^ 2) m_nat < p ^ 2 :=
      Nat.div_lt_self hp2pos h_gt
    rw [h_ord_nat] at h_div_lt
    omega
  have h_coprime_p : Nat.Coprime m_nat p := by
    rw [Nat.coprime_iff_gcd_eq_one]
    apply Nat.eq_one_of_dvd_one
    have h_gcd_p_dvd : Nat.gcd m_nat p ∣ Nat.gcd (p ^ 2) m_nat :=
      Nat.dvd_gcd
        (Nat.dvd_trans (Nat.gcd_dvd_right m_nat p) (by rw [sq p]; exact ⟨p, rfl⟩))
        (Nat.gcd_dvd_left m_nat p)
    rw [h_gcd_p2] at h_gcd_p_dvd
    exact h_gcd_p_dvd
  have hm_mod_p : m_nat % p = 1 := by
    have h_comm_cent : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center G :=
      commutator_mem_center_of_p3 hcard hnonab y x
    rw [← h_conj_nat] at h_comm_cent
    -- h_comm_cent: x^m_nat * x⁻¹ ∈ Z(G)
    have h_center_card : Nat.card (Subgroup.center G) = p :=
      center_card_eq_p_of_nonabelian hcard hnonab
    -- Element z = x^m_nat * x⁻¹ has order dividing p
    letI : Fintype (Subgroup.center G) := Fintype.ofFinite _
    let z : Subgroup.center G := ⟨x ^ m_nat * x⁻¹, h_comm_cent⟩
    have h_ord_z : orderOf (z : G) ∣ p := by
      have h_ord_sub : orderOf z ∣ Fintype.card (Subgroup.center G) := orderOf_dvd_card
      have h_card : Fintype.card (Subgroup.center G) = p := by
        rw [← Nat.card_eq_fintype_card, h_center_card]
      rw [h_card] at h_ord_sub
      simpa [z] using h_ord_sub
    have hz_pow : (x ^ m_nat * x⁻¹) ^ p = 1 := by
      simpa [z] using (orderOf_dvd_iff_pow_eq_one.mp h_ord_z)
    -- x^m_nat and x⁻¹ commute (both powers of x)
    have h_comm : Commute (x ^ m_nat) x⁻¹ :=
      (Commute.refl x).pow_left m_nat |>.inv_right
    -- (a*b)^p = a^p * b^p for commuting a,b
    rw [h_comm.mul_pow p] at hz_pow
    -- hz_pow: (x ^ m_nat)^p * (x⁻¹)^p = 1
    -- Simplify powers: (x⁻¹)^p = (x^p)⁻¹
    have h_inv_pow : (x⁻¹)^p = (x ^ p)⁻¹ := by simp
    rw [← pow_mul x m_nat p, h_inv_pow] at hz_pow
    -- hz_pow: x^(m_nat*p) * (x^p)⁻¹ = 1
    -- So x^(m_nat*p) = x^p
    have h_eq_pow : x ^ (m_nat * p) = x ^ p := by
      apply_fun (· * (x ^ p)) at hz_pow
      simpa [mul_assoc, inv_mul_cancel, mul_one] using hz_pow
    -- Now x^((m_nat-1)*p) = 1
    -- Since (m_nat-1)*p = m_nat*p - p... In ℕ, we need to be careful with subtraction
    -- Instead, use the relation directly: from x^(m*p) = x^p, we have x^(m*p) * (x^p)⁻¹ = 1
    -- In ℤ: x^(m*p - p) = 1 → x^((m-1)*p) = 1
    -- But we can also use: x^((m-1)*p) = x^(m*p) * x^(-p) = x^p * x^(-p) = 1
    -- Too complex in ℕ. Let's use ℤ.
    have hm_pos : m_nat ≥ 1 := by
      by_contra h_not
      have hm_zero : m_nat = 0 := by omega
      rw [hm_zero, pow_zero] at h_conj_nat
      -- h_conj_nat: 1 = y*x*y⁻¹ → y*x = x*y → x = 1, contradiction
      have hx_is_one : x = 1 := by
        -- From h_conj_nat: 1 = y*x*y⁻¹, multiply by y on the right: y = y*x
        have hy_eq_yx : y = y * x := by
          calc
            y = 1 * y := by simp
            _ = (y * x * y⁻¹) * y := by rw [← h_conj_nat]
            _ = y * x := by group
        have h_one_eq_x : (1 : G) = x :=
          mul_left_cancel (a := y) (by simpa using hy_eq_yx)
        exact h_one_eq_x.symm
      have h_ord_one : orderOf (1 ^ m_nat) = 1 := by simp
      have h_contra : (1 : ℕ) = p ^ 2 := by
        calc
          1 = orderOf (1 ^ m_nat) := by simp
          _ = orderOf (x ^ m_nat) := by simpa [hx_is_one]
          _ = p ^ 2 := h_ord_nat
      have hp_sq_gt_one : 1 < p ^ 2 := by
        nlinarith [hp_prime.one_lt]
      omega
    -- Now from h_eq_pow: x^(m_nat*p) = x^p, deduce x^((m_nat-1)*p) = 1
    have hz_prod_nat : x ^ ((m_nat - 1) * p) = 1 := by
      have h_sum : (m_nat - 1) * p + p = m_nat * p := by
        calc
          (m_nat - 1) * p + p = ((m_nat - 1) + 1) * p := by ring
          _ = m_nat * p := by rw [Nat.sub_add_cancel hm_pos]
      -- x^((m_nat-1)*p) * x^p = x^(m_nat*p)
      have h_pow_sum : x ^ ((m_nat - 1) * p) * x ^ p = x ^ (m_nat * p) := by
        rw [← pow_add, h_sum]
      rw [h_eq_pow] at h_pow_sum
      -- h_pow_sum: x^((m_nat-1)*p) * x^p = x^p
      -- Cancel x^p on the right
      apply_fun (· * (x ^ p)⁻¹) at h_pow_sum
      simpa [mul_assoc] using h_pow_sum
    -- Now orderOf x = p^2 ∣ (m_nat-1)*p
    have hp2_dvd : p ^ 2 ∣ (m_nat - 1) * p := by
      rw [← hx]
      exact orderOf_dvd_of_pow_eq_one hz_prod_nat
    -- p^2 = p*p. Since p*p ∣ (m_nat-1)*p, cancel one p
    have hp_dvd : p ∣ m_nat - 1 := by
      have htemp : p * p ∣ (m_nat - 1) * p := by
        rw [show p ^ 2 = p * p by ring] at hp2_dvd
        exact hp2_dvd
      rw [mul_comm (m_nat - 1) p] at htemp
      -- htemp: p*p ∣ p*(m_nat-1)
      -- Cancel one p
      exact (Nat.mul_dvd_mul_iff_left hp_pos).mp htemp
    -- Now m_nat = p*k + 1, so m_nat % p = 1
    rcases hp_dvd with ⟨k, hk⟩
    -- hk: m_nat - 1 = p * k
    have hm_eq : m_nat = p * k + 1 := by
      omega
    rw [hm_eq]
    simp [Nat.add_mod_right, Nat.mod_eq_of_lt hp_prime.one_lt]
  -- Step 4: write m_nat = 1 + a*p, find r with r*a ≡ 1 [MOD p]
  have hm_eq_ap : m_nat = 1 + (m_nat / p) * p := by
    rw [← Nat.mod_add_div m_nat p, hm_mod_p]
  set a := m_nat / p with ha_def
  have ha_lt_p : a < p := by
    rw [ha_def]
    exact (Nat.div_lt_iff_lt_mul hp_pos).mpr (by
      rw [sq]
      exact hm_nat_lt_p2)
  have ha_cop : Nat.Coprime a p := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have h_gcd_dvd_p : Nat.gcd a p ∣ p := Nat.gcd_dvd_right a p
    rcases hp_prime.eq_one_or_self_of_dvd _ h_gcd_dvd_p with (h1 | hp')
    · exact h1
    · -- gcd a p = p, so p ∣ a, meaning a = p*k for some k
      -- Since a < p, this forces a = 0
      have hp_dvd_a : p ∣ a := Nat.gcd_dvd_left a p
      have ha_zero : a = 0 := by
        have h_le : p ≤ a := Nat.le_of_dvd (by omega) hp_dvd_a
        omega
      -- But a = 0 implies m_nat = 1, so y*x*y⁻¹ = x, meaning y centralizes x
      -- Then x is in the center, contradicting |Z(G)| = p
      rw [ha_zero, mul_zero, add_zero] at hm_eq_ap
      rw [hm_eq_ap, pow_one] at h_conj_nat
      -- h_conj_nat: x = y*x*y⁻¹ → y*x = x*y
      have hyx_comm : y * x = x * y := by
        apply_fun (· * y) at h_conj_nat
        simpa [mul_assoc] using h_conj_nat
      -- x commutes with y, so the centralizer of x contains both ⟨x⟩ and y
      -- Since |⟨x⟩| = p^2 and y ∉ ⟨x⟩, |C_G(x)| > p^2, so C_G(x) = G
      -- Thus x ∈ Z(G), so |Z(G)| ≥ p^2, but |Z(G)| = p, contradiction
      have hx_cent : x ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        -- Need to show x*g = g*x. We know x commutes with x and y.
        -- But we don't know about other elements... Hmm, this argument needs more.
        sorry
      sorry
  have h_exists_r : ∃ (r : ℕ), r * a ≡ 1 [MOD p] := by
    have h_cop_int : (a : ℤ).gcd (p : ℤ) = 1 := by
      rw [← Nat.cast_gcd, ha_cop.gcd_eq_one, Nat.cast_one]
    rcases Int.gcd_eq_gcd_ab (a : ℤ) (p : ℤ) with ⟨u, v, h⟩
    have h_mod_int : u * (a : ℤ) ≡ (1 : ℤ) [ZMOD (p : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      use -v
      linarith
    let r := ((u % (p : ℤ)).toNat : ℕ)
    have h_r_nonneg : 0 ≤ u % (p : ℤ) := Int.emod_nonneg u (by exact_mod_cast hp_prime.ne_zero)
    have h_r_int : (r : ℤ) = u % (p : ℤ) := by
      simp [r, Int.toNat_of_nonneg h_r_nonneg]
    have h_r_mod : (r : ℤ) ≡ u [ZMOD (p : ℤ)] := by
      rw [h_r_int]
      exact Int.mod_modEq _ _
    have h_result_int : (r : ℤ) * (a : ℤ) ≡ (1 : ℤ) [ZMOD (p : ℤ)] :=
      (h_r_mod.mul_right (a : ℤ)).trans h_mod_int
    -- Convert to ℕ: equality in ZMod p
    have h_result_nat : r * a ≡ 1 [MOD p] := by
      rw [Nat.ModEq]
      apply (ZMod.eq_iff_modEq_nat (r * a) (1 : ℕ) p).mpr
      -- Need: r*a ≡ 1 mod p in ℕ, which follows from h_result_int
      -- But ZMod.eq_iff_modEq_nat might not exist
      -- Let me use: `ZMod.natCast_mod` and `ZMod.val`
      -- Actually, we can use `Nat.modEq_iff_modEq_int`:
      rw [Nat.modEq_iff_modEq_int]
      -- Now need: (r*a : ℤ) ≡ (1 : ℤ) [ZMOD p]
      -- Which is exactly h_result_int since (r*a : ℤ) = (r : ℤ) * (a : ℤ)
      simpa [mul_comm, add_comm] using h_result_int
    exact ⟨r, h_result_nat⟩
  rcases h_exists_r with ⟨r, hr⟩
  -- Apply normalize_conjugation_power
  have h_conj_form : y * x * y⁻¹ = x ^ (1 + a * p) := by
    rw [h_conj_nat, hm_eq_ap]
  have hy_r_conj : y ^ r * x * (y ^ r)⁻¹ = x ^ (1 + p) :=
    normalize_conjugation_power hx h_conj_form ha_cop hr
  -- Show y^r ∉ zpowers x
  have hy_r_not_mem : y ^ r ∉ zpowers x := by
    intro hyr_mem
    -- Since y ∉ zpowers x, the quotient G/(zpowers x) has order p
    -- and y generates the quotient. Since r*a ≡ 1 [MOD p], r is coprime to p
    -- So y^r ≠ 1 in the quotient, contradiction
    have hindex : (zpowers x).index = p := by
      have hxcard : Nat.card (zpowers x) = p ^ 2 := by
        rw [Nat.card_zpowers, hx]
      have h := Subgroup.index_mul_card (zpowers x)
      rw [hxcard, hcard] at h
      have hp_ne_zero : p ^ 2 ≠ 0 := pow_ne_zero 2 hp_prime.ne_zero
      nlinarith
    have hcardQ : Fintype.card (G ⧸ zpowers x) = p := by
      rw [← Subgroup.index_eq_card, hindex]
    let yQ : G ⧸ zpowers x := (y : G ⧸ zpowers x)
    have hyQ_ne_one : yQ ≠ 1 := mt ((QuotientGroup.eq_one_iff _).mp) hy_not_mem
    have hyQ_order : orderOf yQ = p := by
      have h_dvd : orderOf yQ ∣ p := by
        rw [← hcardQ]
        exact orderOf_dvd_card
      rcases hp_prime.eq_one_or_self_of_dvd _ h_dvd with (hone | hp')
      · exact absurd (orderOf_eq_one_iff.mp hone) hyQ_ne_one
      · exact hp'
    have hyrQ_one : (yQ ^ r) = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hyr_mem
    -- So orderOf yQ = p ∣ r, which contradicts r*a ≡ 1 [MOD p] unless a ≡ 0 mod p
    have hp_dvd_r : p ∣ r := by
      rw [← hyQ_order]
      exact orderOf_dvd_of_pow_eq_one _ hyrQ_one
    -- But hr: r*a ≡ 1 [MOD p], so r*a % p = 1
    -- If p ∣ r, then r*a ≡ 0*a ≡ 0 [MOD p], not 1
    -- Contradiction
    have h_mod : r * a ≡ 1 [MOD p] := hr
    have h_mod' : r * a ≡ 0 [MOD p] := by
      apply Nat.ModEq.of_dvd
      exact Nat.dvd_mul_of_dvd_right hp_dvd_r a
    have : (r * a) % p = 0 % p := h_mod'
    have : (r * a) % p = 1 % p := h_mod
    rw [show (1 : ℕ) % p = 1 from Nat.mod_eq_of_lt hp_prime.one_lt] at this
    rw [show (0 : ℕ) % p = 0 from Nat.zero_mod _] at this
    -- Contradiction: 1 = 0
    omega
  exact ⟨y ^ r, hy_r_not_mem, hy_r_conj⟩

/-! #### Exponent p² case: ℤ/p² ⋊ ℤ/p -/

private lemma semidirectP2P_of_exponent_p2 (hexp : Monoid.exponent G = p ^ 2)
    (hcard : Nat.card G = p ^ 3) (hnonab : ¬ ∀ a b : G, a * b = b * a)
    (hodd : p ≠ 2) :
    Nonempty (G ≃* SemidirectP2P p) := by
    have hprime := hp.out
    -- Step 1: find an element x with order p²
    obtain ⟨x, hxord⟩ : ∃ x : G, orderOf x = p ^ 2 := exists_orderOf_p_sq hexp
    have hxcard : Nat.card (zpowers x) = p ^ 2 := by
      rw [Nat.card_zpowers]; exact hxord
    -- Step 2: the subgroup ⟨x⟩ is normal (index p)
    have hxnorm : (zpowers x).Normal := zpowers_normal_of_index_p x hxcard hcard
    -- Step 3: find an element y not in ⟨x⟩
    have h_exists_y : ∃ (y : G), y ∉ zpowers x := by
      -- since |G|=p^3 and |<x>|=p^2, there must exist
      -- y in G that is not in <x>
      have h_card_lt : Nat.card (zpowers x) < Nat.card G := by
        rw [hxcard, hcard]
        have h : p ^ 2 < p ^ 3 := by
          have h1 : 1 < p := hprime.one_lt
          have h2 : p ^ 2 * 1 < p ^ 2 * p := by
            exact mul_lt_mul_of_pos_left h1 (by positivity)
          simpa [pow_succ] using h2
        exact h
      by_contra h
      push Not at h
      have h_full : (zpowers x) = ⊤ := eq_top_iff.mpr (fun y _ => h y)

      rw [h_full] at h_card_lt
      simp at h_card_lt
    rcases h_exists_y with ⟨y, hy_not_mem⟩
    -- Step 4: y * x * y⁻¹ = x ^ (1 + p) (the standard action for this group)
    have hconj_mem : y * x * y⁻¹ ∈ zpowers x := hxnorm.conj_mem _ (mem_zpowers x) y
    rw [Subgroup.mem_zpowers_iff] at hconj_mem
    have ⟨k, hk⟩ := hconj_mem
    have hx_pow2 : x ^ (p ^ 2) = 1 := by
      rw [← hxord]; exact pow_orderOf_eq_one x
    have hkord : orderOf (y * x * y⁻¹) = p ^ 2 := by
      have hsemi : SemiconjBy y x (y * x * y⁻¹) := by show y * x = y * x * y⁻¹ * y; group
      exact (SemiconjBy.orderOf_eq y hsemi).symm.trans hxord
    have hk_pow : x ^ k = x ^ (k % (p ^ 2)) := by
      have h := zpow_mod_orderOf x k
      rw [show (↑(orderOf x) : ℤ) = (p ^ 2 : ℤ) from by exact_mod_cast hxord] at h
      exact h.symm
    set m := k % (p ^ 2) with hm_def
    have hp2_pos : (0 : ℤ) < p ^ 2 := by
      have hp_ne_zero : (p : ℤ) ≠ 0 := by exact mod_cast hp.out.ne_zero
      have hp2pos' : 0 < (p : ℤ) ^ 2 := pow_pos (by exact mod_cast hp.out.pos) 2
      simpa using hp2pos'
    have hm_nn : 0 ≤ (m : ℤ) :=
      Int.emod_nonneg k (by
        have : (p ^ 2 : ℤ) ≠ 0 := by omega
        exact this)
    have hm_lt : (m : ℤ) < (p ^ 2 : ℤ) :=
      Int.emod_lt_of_pos k hp2_pos
    have hxm_ord : orderOf (x ^ m) = p ^ 2 := by rw [← hk_pow, hk]; exact hkord
    let m_nat : ℕ := m.toNat
    have hm_nat_eq : (m : ℤ) = (m_nat : ℤ) := by
      show m = (Int.toNat m : ℤ)
      exact (Int.toNat_of_nonneg hm_nn).symm
    have hxm_nat : x ^ m = x ^ (m_nat : ℕ) := by
      calc
        x ^ m = x ^ (m_nat : ℤ) := by rw [hm_nat_eq]
        _ = x ^ (m_nat : ℕ) := by rw [zpow_natCast]
    have hxm_nat_ord : orderOf (x ^ (m_nat : ℕ)) = p ^ 2 := by
      rw [← hxm_nat, hxm_ord]
    have hp2pos : 0 < p ^ 2 := pow_pos hp.out.pos 2
    have h_gcd1 : Nat.gcd (p ^ 2) m_nat = 1 := by
      rw [orderOf_pow x (n := m_nat), hxord] at hxm_nat_ord
      by_contra h
      have hg_gt1 : 1 < Nat.gcd (p ^ 2) m_nat := by
        have hpos : 0 < Nat.gcd (p ^ 2) m_nat :=
          Nat.gcd_pos_of_pos_left m_nat hp2pos
        omega
      have hdiv_lt : (p ^ 2) / Nat.gcd (p ^ 2) m_nat < p ^ 2 :=
        Nat.div_lt_self hp2pos hg_gt1
      rw [hxm_nat_ord] at hdiv_lt
      omega
    have hcoprime : Nat.Coprime m_nat p := by
      have h_gcd_p : Nat.gcd p m_nat = 1 := by
        have h_dvd_p2 : Nat.gcd p m_nat ∣ p ^ 2 :=
          dvd_trans (Nat.gcd_dvd_left p m_nat) (by rw [sq p]; exact ⟨p, rfl⟩)
        have h_dvd_all : Nat.gcd p m_nat ∣ Nat.gcd (p ^ 2) m_nat :=
          Nat.dvd_gcd h_dvd_p2 (Nat.gcd_dvd_right p m_nat)
        rw [h_gcd1] at h_dvd_all
        exact Nat.eq_one_of_dvd_one h_dvd_all
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact h_gcd_p
    -- Now normalize the conjugation using normalize_conjugation_to_one_add_p
    obtain ⟨y', hy'_not_mem, h_conj⟩ :=
      normalize_conjugation_to_one_add_p
      hxord
      hy_not_mem
      hconj_mem
      hcard
      hnonab
    -- Define the map f : SemidirectP2P p → G sending (a, b) ↦ x ^ a.val * y' ^ b.val
    let fFun : SemidirectP2P p → G := fun ⟨a, b⟩ => x ^ a.val * y' ^ b.val
    have hmul : ∀ g₁ g₂ : SemidirectP2P p, fFun (g₁ * g₂) = fFun g₁ * fFun g₂ := by
      sorry
    let f := MonoidHom.mk' fFun hmul
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro ⟨a, b⟩ hmem
      simp only [MonoidHom.mem_ker, Subgroup.mem_bot] at hmem ⊢
      have hmem' : x ^ a.val * y' ^ b.val = 1 := hmem
      have hb : b = 0 := by
        by_contra hb_ne
        have hindex : (zpowers x).index = p := by
          have h := Subgroup.index_mul_card (zpowers x)
          rw [hxcard, hcard] at h
          have hp_ne_zero : p ^ 2 ≠ 0 := pow_ne_zero 2 hprime.ne_zero
          have h' : p ^ 2 * (zpowers x).index = p ^ 2 * p := by nlinarith
          exact mul_left_cancel₀ hp_ne_zero h'
        have hx_pow_mem : x ^ a.val ∈ zpowers x := Subgroup.pow_mem _ (mem_zpowers x) a.val
        have h : y' ^ b.val ∈ zpowers x := by
          have hy_eq : y' ^ b.val = (x ^ a.val)⁻¹ :=
            eq_inv_of_mul_eq_one_right hmem'
          rw [hy_eq]
          exact Subgroup.inv_mem _ hx_pow_mem
        have h2 : b.val > 0 := by
          by_contra hle
          have hzero : b.val = 0 := by omega
          apply hb_ne
          exact (ZMod.val_eq_zero b).mp hzero
        have h3 : (zpowers x).index ∣ b.val := by
          rw [hindex]
          let yQ : G ⧸ zpowers x := (y' : G ⧸ zpowers x)
          have hyQ_ne_one : yQ ≠ 1 :=
            mt ((QuotientGroup.eq_one_iff _).mp) hy'_not_mem
          have hcardQ : Fintype.card (G ⧸ zpowers x) = p := by
            rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card (zpowers x), hindex]
          have hyQ_order : orderOf yQ = p := by
            have h_dvd : orderOf yQ ∣ p := by
              rw [← hcardQ]
              exact orderOf_dvd_card
            rcases hp.out.eq_one_or_self_of_dvd _ h_dvd with (hone | hp')
            · exact absurd (orderOf_eq_one_iff.mp hone) hyQ_ne_one
            · exact hp'
          have hyQ_pow_one : yQ ^ b.val = 1 := by
            rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
            exact h
          have h_order_dvd : orderOf yQ ∣ b.val :=
            orderOf_dvd_of_pow_eq_one hyQ_pow_one
          exact hyQ_order.symm ▸ h_order_dvd
        rw [hindex] at h3
        have h4 : p ∣ b.val := h3
        have h5 : b.val < p := b.val_lt
        have h6 : b.val = 0 :=
          Nat.eq_zero_of_dvd_of_lt h4 h5
        apply hb_ne
        exact (ZMod.val_eq_zero b).mp h6
      rw [hb] at hmem'
      have hmem'' : x ^ a.val = 1 := by
        simpa [pow_zero, mul_one] using hmem'
      have ha : a = 0 := by
        rw [← ZMod.val_eq_zero]
        have h_order_dvd : orderOf x ∣ a.val :=
          orderOf_dvd_of_pow_eq_one hmem''
        rw [hxord] at h_order_dvd
        have ha_val_lt : a.val < p ^ 2 := a.val_lt
        exact Nat.eq_zero_of_dvd_of_lt h_order_dvd ha_val_lt
      exact SemidirectP2P.ext ha hb
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hinj, ?_⟩
      rw [show Fintype.card (SemidirectP2P p) = p ^ 3 from by
            rw [← Nat.card_eq_fintype_card]; exact SemidirectP2P.card_semidirectP2P p,
          ← Nat.card_eq_fintype_card, hcard]
    exact ⟨(MulEquiv.ofBijective f hbij).symm⟩


/-- A non-abelian group of order p³ (p odd) is isomorphic to either
    the Heisenberg group or ℤ/p² ⋊ ℤ/p. -/
theorem nonabelian_p3_classification_odd (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (G : Type*) [Group G] [Fintype G]
    (hcard : Nat.card G = p ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    Nonempty (G ≃* HeisenbergGroup p) ∨
    Nonempty (G ≃* SemidirectP2P p) := by
  rcases exponent_of_nonabelian_p3 hcard hnonab with (hexp_p | hexp_p2)
  · left; exact heisenberg_of_exponent_p hexp_p hcard hnonab hp2
  · right; exact semidirectP2P_of_exponent_p2 hexp_p2 hcard hnonab hp2



/-- Helper: for x with orderOf x = n, x^((a-b)%n) = x^a * (x^b)⁻¹. -/
private theorem pow_zmod_sub {G : Type*} [Group G] {x : G} {n : ℕ}
    (hn : orderOf x = n) [NeZero n] (a b : ZMod n) :
    x ^ (a - b).val = x ^ a.val * (x ^ b.val)⁻¹ := by
  have h : x ^ (a - b).val * x ^ b.val = x ^ a.val := by
    rw [← pow_add, ← pow_mod_orderOf x ((a - b).val + b.val), hn,
        ← ZMod.val_add, sub_add_cancel]
  rw [eq_mul_inv_iff_mul_eq]; exact h

/-- Helper: conjugation by y inverts x: x^i * y = y * (x⁻¹)^i. -/
private theorem conj_inv_comm {G : Type*} [Group G] {x y : G}
    (hconj : y * x * y⁻¹ = x⁻¹) (i : ℕ) : x ^ i * y = y * (x⁻¹) ^ i := by
  have hxy : x * y = y * x⁻¹ := by
    rw [← mul_inv_eq_one]
    calc x * y * (y * x⁻¹)⁻¹ = x * (y * x * y⁻¹) := by simp [mul_assoc]
      _ = x * x⁻¹ := by rw [hconj]
      _ = 1 := by simp
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x n, mul_assoc (x ^ n) x y, hxy,
        ← mul_assoc (x ^ n) y, ih, mul_assoc y, pow_succ]

/-- Exponent 2 implies abelian. -/
private theorem abelian_of_exponent_two {G : Type*} [Group G]
    (h : ∀ g : G, g * g = 1) : ∀ a b : G, a * b = b * a := by
  intro a b
  have hinv : ∀ g : G, g⁻¹ = g := fun g => (eq_inv_of_mul_eq_one_right (h g)).symm
  calc a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b, hinv a]

/-- Helper: if x has order n and x^i.val = x^j.val for i j : ZMod n, then i = j. -/
private lemma zmod_eq_of_pow_eq {G : Type*} [Group G] {x : G} {n : ℕ} [NeZero n]
    (hord : orderOf x = n) (i j : ZMod n) (h : x ^ i.val = x ^ j.val) : i = j :=
  ZMod.val_injective n
    (pow_injOn_Iio_orderOf (show i.val < orderOf x by rw [hord]; exact i.val_lt)
      (show j.val < orderOf x by rw [hord]; exact j.val_lt) h)

/-- A non-abelian group of order 8 is isomorphic to D₄ or Q₈. -/
theorem nonabelian_8_classification
    (G : Type*) [Group G] [Fintype G]
    (hcard : Nat.card G = 2 ^ 3)
    (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    Nonempty (G ≃* DihedralGroup 4) ∨
    Nonempty (G ≃* QuaternionGroup 2) := by
  haveI hp2 : Fact (Nat.Prime 2) := ⟨by decide⟩
  -- Step 1: exponent is 4
  have hexp : Monoid.exponent G = 4 := by
    rcases exponent_of_nonabelian_p3 (p := 2) hcard hnonab with h2 | h4
    · exfalso; apply hnonab
      exact abelian_of_exponent_two (fun g => by
        have := Monoid.pow_exponent_eq_one (G := G) g
        rw [h2, sq] at this; exact this)
    · linarith [sq_nonneg 2]
  -- Step 2: find x with orderOf x = 4
  obtain ⟨x, hx4⟩ : ∃ x : G, orderOf x = 4 := by
    by_contra hall; push Not at hall
    have h2dvd : Monoid.exponent G ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one; intro g
      rw [← orderOf_dvd_iff_pow_eq_one]
      have hg4 : orderOf g ∣ 4 := hexp ▸ Monoid.order_dvd_exponent g
      have h_lb : 1 ≤ orderOf g := orderOf_pos g
      have h_ub : orderOf g ≤ 4 := Nat.le_of_dvd (by omega) hg4
      have h_n3 : orderOf g ≠ 3 := fun h =>
        absurd (h ▸ hg4 : (3 : ℕ) ∣ 4) (by decide)
      have h_n4 : orderOf g ≠ 4 := hall g
      interval_cases (orderOf g) <;> omega
    rw [hexp] at h2dvd; omega
  -- Step 3: ⟨x⟩ has index 2
  have hxcard : Nat.card (zpowers x) = 4 := by
    rw [Nat.card_zpowers]; exact hx4
  have hindex : (zpowers x).index = 2 := by
    have := Subgroup.index_mul_card (zpowers x)
    rw [hxcard, hcard] at this; omega
  haveI hxnorm : (zpowers x).Normal := normal_of_index_eq_two hindex
  -- Step 4: find y ∉ ⟨x⟩
  obtain ⟨y, hy_not_mem⟩ : ∃ y : G, y ∉ zpowers x := by
    by_contra hall; push Not at hall
    have : (zpowers x).index = 1 :=
      Subgroup.index_eq_one.mpr (eq_top_iff.mpr (fun g _ => hall g))
    rw [hindex] at this; omega
  -- Step 5: y * x * y⁻¹ = x⁻¹
  have hx_ord4 : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hx_ne_1 : x ≠ 1 := by intro h; rw [h, orderOf_one] at hx4; omega
  have hx2_ne_1 : x ^ 2 ≠ 1 := by
    intro h; have := orderOf_dvd_of_pow_eq_one h; rw [hx4] at this; omega
  have hx_not_cent : x ∉ Subgroup.center G := by
    intro hx_cent
    have hcenter := center_card_eq_p_of_nonabelian (p := 2) hcard hnonab
    have hle : zpowers x ≤ Subgroup.center G := zpowers_le.mpr hx_cent
    have : 4 ≤ Nat.card (Subgroup.center G) :=
      hxcard ▸ Subgroup.card_le_of_le hle
    omega
  have hconj : y * x * y⁻¹ = x⁻¹ := by
    have hmem : y * x * y⁻¹ ∈ zpowers x :=
      hxnorm.conj_mem _ (mem_zpowers x) y
    have hord_conj : orderOf (y * x * y⁻¹) = 4 := by
      have hsemi : SemiconjBy y x (y * x * y⁻¹) := by show y * x = y * x * y⁻¹ * y; group
      exact (SemiconjBy.orderOf_eq y hsemi).symm.trans hx4
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk_mod : x ^ k = x ^ (k % (4 : ℤ)) := by
      have h := zpow_mod_orderOf x k
      rw [show (↑(orderOf x) : ℤ) = 4 from by exact_mod_cast hx4] at h
      exact h.symm
    set m := k % (4 : ℤ) with hm_def
    have hm_nn : 0 ≤ m := Int.emod_nonneg k (by omega)
    have hm_lt : m < 4 := Int.emod_lt_of_pos k (by omega)
    have hxm_ord : orderOf (x ^ m) = 4 := by rw [← hk_mod, hk]; exact hord_conj
    interval_cases m
    · simp at hxm_ord
    · exfalso; apply hx_not_cent
      have heq : y * x * y⁻¹ = x := by rw [← hk, hk_mod]; simp
      have hyx_comm : y * x = x * y := by
        have := congr_arg (· * y) heq
        simp only [mul_assoc, inv_mul_cancel, mul_one] at this; exact this
      have hzp_le : zpowers x ≤ Subgroup.centralizer ({x} : Set G) :=
        zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
      have hy_cent : y ∈ Subgroup.centralizer ({x} : Set G) :=
        mem_centralizer_singleton_iff.mpr hyx_comm
      have hcard_ge : 4 ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) :=
        hxcard ▸ Subgroup.card_le_of_le hzp_le
      have hcard_dvd : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card _
      rw [hcard] at hcard_dvd
      have hcard_le : Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ 2 ^ 3 := by
        have := Subgroup.card_le_of_le (le_top : Subgroup.centralizer ({x} : Set G) ≤ ⊤)
        rwa [Subgroup.card_top, hcard] at this
      have hcard_ne4 : Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 4 := by
        intro h; exact hy_not_mem
          (Subgroup.eq_of_le_of_card_ge hzp_le (h ▸ hxcard ▸ le_refl _) ▸ hy_cent)
      have hcard_8 : Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 ^ 3 := by
        obtain ⟨d, hd⟩ := hcard_dvd
        have hd_le : d ≤ 2 := by nlinarith
        interval_cases d <;> omega
      have htop := Subgroup.eq_top_of_card_eq _ (hcard_8.trans hcard.symm)
      rw [Subgroup.mem_center_iff]; intro g
      have hg_mem : g ∈ Subgroup.centralizer ({x} : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact mem_centralizer_singleton_iff.mp hg_mem
    · have h2 : orderOf (x ^ (2 : ℤ)) ∣ 2 := by
        rw [show (2 : ℤ) = ↑(2 : ℕ) from rfl, zpow_natCast, orderOf_dvd_iff_pow_eq_one,
            ← pow_mul, show 2 * 2 = 4 from rfl]; exact hx_ord4
      have h4 : orderOf (x ^ (2 : ℤ)) = 4 := hxm_ord
      have : 4 ≤ 2 := h4 ▸ Nat.le_of_dvd (by omega) h2
      omega
    · have hx3inv : x ^ (3 : ℕ) = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_right; rw [← pow_succ']; exact hx_ord4
      calc y * x * y⁻¹ = x ^ k := hk.symm
        _ = x ^ (3 : ℤ) := hk_mod
        _ = x ^ (3 : ℕ) := by rw [show (3 : ℤ) = ↑(3 : ℕ) from rfl, zpow_natCast]
        _ = x⁻¹ := hx3inv
  -- Step 6: y² ∈ {1, x²}
  have hy2 : y ^ 2 = 1 ∨ y ^ 2 = x ^ 2 := by
    have hy2_mem : y ^ 2 ∈ zpowers x := by
      have hq_card : Nat.card (G ⧸ zpowers x) = 2 := by
        rw [← Subgroup.index_eq_card]; exact hindex
      suffices h : QuotientGroup.mk' (zpowers x) (y ^ 2) = 1 from
        (QuotientGroup.eq_one_iff _).mp h
      rw [map_pow, ← hq_card]; exact pow_card_eq_one'
    have hy_ord_dvd : orderOf y ∣ 4 := hexp ▸ Monoid.order_dvd_exponent y
    have hy2_sq : (y ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * 2 = 4 from rfl, ← orderOf_dvd_iff_pow_eq_one]; exact hy_ord_dvd
    rw [Subgroup.mem_zpowers_iff] at hy2_mem
    obtain ⟨j, hj⟩ := hy2_mem
    have hj_mod : y ^ 2 = x ^ (j % (4 : ℤ)) := by
      have h := (zpow_mod_orderOf x j).symm
      rw [show (↑(orderOf x) : ℤ) = 4 from by exact_mod_cast hx4] at h
      rwa [← hj]
    set m := j % (4 : ℤ) with hm_def
    have hm_nn : 0 ≤ m := Int.emod_nonneg j (by omega)
    have hm_lt : m < 4 := Int.emod_lt_of_pos j (by omega)
    have hxm_sq : (x ^ m) ^ 2 = 1 := hj_mod ▸ hy2_sq
    interval_cases m
    · left; rw [hj_mod]; simp
    · exfalso; rw [zpow_one] at hxm_sq; exact hx2_ne_1 hxm_sq
    · right; rw [hj_mod, show (2 : ℤ) = ↑(2 : ℕ) from rfl, zpow_natCast]
    · exfalso
      rw [show (3 : ℤ) = ↑(3 : ℕ) from rfl, zpow_natCast, ← pow_mul] at hxm_sq
      have : orderOf x ∣ 3 * 2 := orderOf_dvd_of_pow_eq_one hxm_sq
      rw [hx4] at this; exact absurd this (by decide)
  -- Step 7: construct isomorphism
  haveI : NeZero (4 : ℕ) := ⟨by omega⟩
  rcases hy2 with hy1 | hyx2
  · -- D₄ case: y² = 1
    left
    let fFun : DihedralGroup 4 → G := fun
      | .r i => x ^ i.val
      | .sr i => y * x ^ i.val
    have hmul : ∀ a b : DihedralGroup 4, fFun (a * b) = fFun a * fFun b := by
      intro a b; match a, b with
      | .r i, .r j =>
        show x ^ (i + j).val = x ^ i.val * x ^ j.val
        exact pow_zmod_add hx4 i j
      | .r i, .sr j =>
        show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
        symm
        calc x ^ i.val * (y * x ^ j.val)
            = x ^ i.val * y * x ^ j.val := by rw [mul_assoc]
          _ = y * (x⁻¹) ^ i.val * x ^ j.val := by rw [conj_inv_comm hconj]
          _ = y * ((x ^ i.val)⁻¹ * x ^ j.val) := by rw [inv_pow, mul_assoc]
          _ = y * (x ^ j.val * (x ^ i.val)⁻¹) := by
              rw [(Commute.pow_pow (Commute.refl x) i.val j.val).inv_left.eq]
          _ = y * x ^ (j - i).val := by rw [← pow_zmod_sub hx4 j i]
      | .sr i, .r j =>
        show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
        rw [mul_assoc, pow_zmod_add hx4 i j]
      | .sr i, .sr j =>
        show x ^ (j - i).val = y * x ^ i.val * (y * x ^ j.val)
        have hyy : y * y = 1 := by rw [← sq]; exact hy1
        symm
        calc y * x ^ i.val * (y * x ^ j.val)
            = y * (x ^ i.val * y) * x ^ j.val := by
              rw [← mul_assoc (y * _) y, mul_assoc y (x ^ i.val) y]
          _ = y * (y * (x⁻¹) ^ i.val) * x ^ j.val := by rw [conj_inv_comm hconj]
          _ = (x ^ i.val)⁻¹ * x ^ j.val := by
              rw [mul_assoc y (y * _), mul_assoc y ((x⁻¹) ^ i.val),
                  ← mul_assoc y y, hyy, one_mul, inv_pow]
          _ = x ^ j.val * (x ^ i.val)⁻¹ :=
              (Commute.pow_pow (Commute.refl x) i.val j.val).inv_left.eq
          _ = x ^ (j - i).val := (pow_zmod_sub hx4 j i).symm
    let f := MonoidHom.mk' fFun hmul
    have hinj : Function.Injective f := by
      intro a b hab
      show a = b
      match a, b with
      | .r i, .r j =>
        exact congr_arg _ (zmod_eq_of_pow_eq hx4 i j hab)
      | .sr i, .sr j =>
        exact congr_arg _ (zmod_eq_of_pow_eq hx4 i j (mul_left_cancel hab))
      | .r i, .sr j =>
        exfalso; apply hy_not_mem
        have h : x ^ i.val = y * x ^ j.val := hab
        have : y = x ^ i.val * (x ^ j.val)⁻¹ := by rw [h]; group
        rw [this]; exact mul_mem (pow_mem (mem_zpowers x) _) (inv_mem (pow_mem (mem_zpowers x) _))
      | .sr i, .r j =>
        exfalso; apply hy_not_mem
        have h : y * x ^ i.val = x ^ j.val := hab
        have : y = x ^ j.val * (x ^ i.val)⁻¹ := by rw [← h]; group
        rw [this]; exact mul_mem (pow_mem (mem_zpowers x) _) (inv_mem (pow_mem (mem_zpowers x) _))
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hcard]; norm_num⟩
    exact ⟨(MulEquiv.ofBijective f hbij).symm⟩
  · -- Q₈ case: y² = x²
    right
    let fFun : QuaternionGroup 2 → G := fun
      | .a i => x ^ i.val
      | .xa i => y * x ^ i.val
    have hmul : ∀ a b : QuaternionGroup 2, fFun (a * b) = fFun a * fFun b := by
      intro a b; match a, b with
      | .a i, .a j =>
        show x ^ (i + j).val = x ^ i.val * x ^ j.val
        exact pow_zmod_add hx4 i j
      | .a i, .xa j =>
        show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
        symm
        calc x ^ i.val * (y * x ^ j.val)
            = x ^ i.val * y * x ^ j.val := by rw [mul_assoc]
          _ = y * (x⁻¹) ^ i.val * x ^ j.val := by rw [conj_inv_comm hconj]
          _ = y * ((x ^ i.val)⁻¹ * x ^ j.val) := by rw [inv_pow, mul_assoc]
          _ = y * (x ^ j.val * (x ^ i.val)⁻¹) := by
              rw [(Commute.pow_pow (Commute.refl x) i.val j.val).inv_left.eq]
          _ = y * x ^ (j - i).val := by rw [← pow_zmod_sub hx4 j i]
      | .xa i, .a j =>
        show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
        rw [mul_assoc, pow_zmod_add hx4 i j]
      | .xa i, .xa j =>
        show x ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val = y * x ^ i.val * (y * x ^ j.val)
        have hyy : y * y = x ^ 2 := by rw [← sq]; exact hyx2
        symm
        calc y * x ^ i.val * (y * x ^ j.val)
            = y * (x ^ i.val * y) * x ^ j.val := by
              rw [← mul_assoc (y * _) y, mul_assoc y (x ^ i.val) y]
          _ = y * (y * (x⁻¹) ^ i.val) * x ^ j.val := by rw [conj_inv_comm hconj]
          _ = x ^ 2 * ((x ^ i.val)⁻¹ * x ^ j.val) := by
              rw [mul_assoc y (y * _), mul_assoc y ((x⁻¹) ^ i.val),
                  ← mul_assoc y y, hyy, inv_pow]
          _ = x ^ 2 * (x ^ j.val * (x ^ i.val)⁻¹) := by
              rw [(Commute.pow_pow (Commute.refl x) i.val j.val).inv_left.eq]
          _ = x ^ 2 * x ^ (j - i).val := by rw [← pow_zmod_sub hx4 j i]
          _ = x ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val := by
              change x ^ ((2 : ℕ) : ZMod (2 * 2)).val * x ^ (j - i).val = _
              rw [← pow_zmod_add hx4 ((2 : ℕ) : ZMod (2 * 2)) (j - i), add_sub_assoc]
    let f := MonoidHom.mk' fFun hmul
    have hinj : Function.Injective f := by
      intro a b hab
      show a = b
      match a, b with
      | .a i, .a j =>
        exact congr_arg _ (zmod_eq_of_pow_eq hx4 i j hab)
      | .xa i, .xa j =>
        exact congr_arg _ (zmod_eq_of_pow_eq hx4 i j (mul_left_cancel hab))
      | .a i, .xa j =>
        exfalso; apply hy_not_mem
        have h : x ^ i.val = y * x ^ j.val := hab
        have : y = x ^ i.val * (x ^ j.val)⁻¹ := by rw [h]; group
        rw [this]; exact mul_mem (pow_mem (mem_zpowers x) _) (inv_mem (pow_mem (mem_zpowers x) _))
      | .xa i, .a j =>
        exfalso; apply hy_not_mem
        have h : y * x ^ i.val = x ^ j.val := hab
        have : y = x ^ j.val * (x ^ i.val)⁻¹ := by rw [← h]; group
        rw [this]; exact mul_mem (pow_mem (mem_zpowers x) _) (inv_mem (pow_mem (mem_zpowers x) _))
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hinj, ?_⟩
      rw [QuaternionGroup.card, ← Nat.card_eq_fintype_card, hcard]; norm_num
    exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end P3Group
