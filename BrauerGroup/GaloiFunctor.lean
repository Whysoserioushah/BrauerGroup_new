import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Category.AlgebraCat.Basic

universe u

open CategoryTheory

variable (K : Type u) [Field K]

class GroupScheme where
  toFunctor : AlgebraCat K ⥤ Grp
