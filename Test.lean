import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

open scoped commutatorElement

variable {G : Type*} [Group G]

lemma central_conj_cancel {x y : G} (hc : x ∈ Subgroup.center G) : y * x * y⁻¹ = x := by
  rw [Subgroup.mem_center_iff] at hc
  simp [mul_assoc, hc]

lemma commutator_pow_right_aux (a b : G) (hc : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℕ) :
    ⁅a, b^n⁆ = ⁅a, b⁆^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutatorElement_mul_right_eq_mul_conj, ih]
    have hcb : ⁅a, b⁆ ∈ Subgroup.center G := hc
    rw [Subgroup.mem_center_iff] at hcb
    have h1 : ⁅a, b⁆^n * b^n * ⁅a, b⁆ * (b^n)⁻¹ = b^n * ⁅a, b⁆^n * ⁅a, b⁆ * (b^n)⁻¹ := by
      simp [mul_assoc, hcb]
      sorry
    rw [h1]
    have h2 : b^n * ⁅a, b⁆^n * ⁅a, b⁆ * (b^n)⁻¹ = b^n * ⁅a, b⁆^(n+1) * (b^n)⁻¹ := by
      simp [mul_assoc, pow_succ]
    rw [h2]
    rw [central_conj_cancel (Subgroup.pow_mem _ hc (n+1))]
