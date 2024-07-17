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
lemma Is_inner (n : ℕ) :
    ∀(σ : Aut K n), ∃(C : GeneralLinearGroup (Fin n) K), ∀ A : Matrix (Fin n) (Fin n) K,
    σ A = (C * A * C⁻¹) := by
  intro σ
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

lemma toAut_is_surj (n : ℕ) : Function.Surjective (toAut K n) := by
  intro σ
  simp only [MonoidHom.coe_mk, coe_units_inv, OneHom.coe_mk]
  obtain ⟨C, hC⟩ := Is_inner _ _ σ
  use C; ext A
  simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, (hC A), coe_units_inv]

lemma GL_center_commute_all (n : ℕ) (G : GL (Fin n) K) (hG : G ∈ Subgroup.center (GL (Fin n) K)) :
    ∀ g : Matrix (Fin n) (Fin n) K, g * G = G * g := by
  intro g
  sorry

lemma toAut_ker (n : ℕ) :
    (toAut K n).ker = Subgroup.center (GL (Fin n) K) := by
  ext G
  constructor
  · rw [Subgroup.mem_center_iff, MonoidHom.mem_ker]
    intro hσ C
    simp only [MonoidHom.coe_mk, coe_units_inv, OneHom.coe_mk] at hσ
    rw [DFunLike.ext_iff] at hσ
    specialize hσ C
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.one_apply] at hσ
    norm_cast at hσ
    have :  G * C * G⁻¹ * G = C * G := by
      rwa [mul_right_cancel_iff]
    simp only [inv_mul_cancel_right] at this
    exact this.symm
  · intro h
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.coe_mk, coe_units_inv, OneHom.coe_mk]
    rw [DFunLike.ext_iff]
    intro A
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.one_apply]
    have : (G : Matrix (Fin n) (Fin n) K) * A * (G)⁻¹ * G = A * G := by
      rw [Matrix.GeneralLinearGroup.coe_inv, mul_assoc,
        show (G : Matrix (Fin n) (Fin n) K)⁻¹ * G = 1 by norm_cast; simp, mul_one]
      exact GL_center_commute_all _ _ _ h A |>.symm
    simp only [coe_units_inv, Units.mul_left_inj] at this
    exact this

def Aut_GLn (n : ℕ) : PGL K n ≃* Aut K n := by
  let e1 := QuotientGroup.quotientKerEquivOfSurjective (toAut K n) (toAut_is_surj K n)
  have : GL (Fin n) K ⧸ (toAut K n).ker ≃* GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K) := by
    exact QuotientGroup.quotientMulEquivOfEq (toAut_ker _ n)
  exact this.symm.trans e1
