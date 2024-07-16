import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

variable (K : Type*) [Field K]
open Matrix
abbrev Aut (n : ℕ) := ((GeneralLinearGroup (Fin n) K) ≃* (GeneralLinearGroup (Fin n) K))

abbrev PGL (n : ℕ) :=
  (GeneralLinearGroup (Fin n) K)⧸(Subgroup.center (GeneralLinearGroup (Fin n) K))

def Aut_GLn (n : ℕ) : Aut K n ≃* PGL K n where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
