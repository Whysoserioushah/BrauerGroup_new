import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

suppress_compilation

variable (K : Type*) [Field K]
open Matrix

/-- Automorphism group of Mₙ(K)-/
abbrev Aut (n : ℕ) := ((Matrix (Fin n) (Fin n) K) ≃* (Matrix (Fin n) (Fin n) K))

abbrev PGL (n : ℕ) :=
  (GeneralLinearGroup (Fin n) K)⧸(Subgroup.center (GeneralLinearGroup (Fin n) K))

/-- Any automorphism of Mₙ(K) is inner -/
lemma Is_inner (n : ℕ) (A : Matrix (Fin n) (Fin n) K):
    ∀(σ : Aut K n), ∃(C : GeneralLinearGroup (Fin n) K), σ A = (C * A * C⁻¹) := by

  sorry

abbrev toAut (n : ℕ): GeneralLinearGroup (Fin n) K →* Aut K n where
  toFun C := {
    toFun := fun A => C * A * C⁻¹
    invFun := fun A => C⁻¹ * A * C
    left_inv := fun A => by
      simp only [← mul_assoc]
      rw [← GeneralLinearGroup.coe_mul, mul_left_inv, GeneralLinearGroup.coe_one, one_mul,
        mul_assoc, ← GeneralLinearGroup.coe_mul, mul_left_inv, GeneralLinearGroup.coe_one, mul_one]
    right_inv := fun A => by
      simp only [← mul_assoc]
      rw [← GeneralLinearGroup.coe_mul, mul_right_inv, GeneralLinearGroup.coe_one, one_mul,
        mul_assoc, ← GeneralLinearGroup.coe_mul, mul_right_inv, GeneralLinearGroup.coe_one, mul_one]
    map_mul' := fun A B => by
      simp only [← mul_assoc]
      rw [mul_assoc (C * A) _ C, ← GeneralLinearGroup.coe_mul, mul_left_inv,
        GeneralLinearGroup.coe_one, mul_one]
  }
  map_one' := by simp only [Units.val_one, one_mul, inv_one, mul_one]; rfl
  map_mul' A B := by
    ext M i j
    simp only [Units.val_mul, _root_.mul_inv_rev, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.mul_apply, _root_.map_mul, ← mul_assoc]
    rw [mul_assoc ((A : Matrix (Fin n) (Fin n) K) * B) _ A, ← GeneralLinearGroup.coe_mul A⁻¹ A,
      mul_left_inv, GeneralLinearGroup.coe_one, mul_one]; nth_rw 2 [mul_assoc (A * B * M)]
    rw [← GeneralLinearGroup.coe_mul A⁻¹ A, mul_left_inv, GeneralLinearGroup.coe_one, mul_one]

lemma toAut_is_surj (n : ℕ) : Function.Surjective (toAut K n) := by sorry

lemma toAut_ker (n : ℕ) :
    (toAut K n).ker = Subgroup.center (GL (Fin n) K) := by

  sorry

def Aut_GLn (n : ℕ) : PGL K n ≃* Aut K n := by
  let e1 := QuotientGroup.quotientKerEquivOfSurjective (toAut K n) (toAut_is_surj K n)
  have : GL (Fin n) K ⧸ (toAut K n).ker ≃* GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K) := sorry
  exact this.symm.trans e1
