module

public import BrauerGroup.Algebra.BrauerGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# The Brauer group of an algebraically closed field is trivial

Over an algebraically closed field every finite-dimensional central simple algebra is a
matrix algebra, so the Brauer group is trivial.
-/

@[expose] public section

namespace BrauerGroup

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem eq_one_of_isAlgClosed (x : BrauerGroup k) : x = 1 := by
  induction x using BrauerGroup.induction with | h A =>
  obtain ⟨n, hn, ⟨iso⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (F := k) (R := A)
  rw [mk_congr iso, mk_matrix_eq_one]

instance instUniqueOfIsAlgClosed : Unique (BrauerGroup k) where
  default := 1
  uniq := eq_one_of_isAlgClosed k

end BrauerGroup
