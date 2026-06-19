/-
Copyright (c) 2026 lixiang90. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P3Group contributors
-/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.ClassEquation
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index

/-! # Definitions for the classification of groups of order p³

For a prime p, every group of order p³ is isomorphic to exactly one of:
  1. `ℤ/p³ℤ` (cyclic)
  2. `ℤ/p²ℤ × ℤ/pℤ` (abelian, non-cyclic)
  3. `(ℤ/pℤ)³` (elementary abelian)
  4. `(ℤ/pℤ × ℤ/pℤ) ⋊ ℤ/pℤ` (non-abelian, exponent p for p odd; `D₄` for p = 2)
  5. `ℤ/p²ℤ ⋊ ℤ/pℤ` (non-abelian, exponent p² for p odd; `Q₈` for p = 2)
-/

namespace P3Group

open Fintype Subgroup MulOpposite

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The five isomorphism classes for groups of order p³. -/
inductive P3Classification where
  | cyclic           -- ℤ/p³ℤ
  | abelianP2P       -- ℤ/p²ℤ × ℤ/pℤ
  | elementary       -- (ℤ/pℤ)³
  | nonabelianExpP   -- exponent p non-abelian (Heisenberg for odd p, D₄ for p=2)
  | nonabelianExpP2  -- exponent p² non-abelian (ℤ/p² ⋊ ℤ/p for odd p, Q₈ for p=2)
  deriving DecidableEq

/-- The abelian group ℤ/p³ℤ -/
abbrev CyclicP3 := ZMod (p ^ 3)

/-- The abelian group ℤ/p²ℤ × ℤ/pℤ -/
abbrev AbelianP2P := ZMod (p ^ 2) × ZMod p

/-- The elementary abelian group (ℤ/pℤ)³ -/
abbrev ElementaryP3 := ZMod p × ZMod p × ZMod p

end P3Group
