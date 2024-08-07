/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
import Mathlib.Data.Matrix.Basic

/-! 
# Composition of matrices 
This file shows that Mₙ(Mₘ(R)) ≃ Mₙₘ(R), Mₙ(Mₘ(R)) ≃ Mₘ(Mₙ(R)), Mn(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ 
and also different levels of equivalence when R is an AddCommMonoid,
Semiring, and Algebra over a CommSemiring K.
-/
namespace Matrix

open BigOperators

variable  (I J K L R : Type*)

/-- Mₙ(Mₘ(R)) ≃ Mₙₘ(R) -/
def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
  toFun m ik jl := m ik.1 jl.1 ik.2 jl.2
  invFun n i j k l := n (i, k) (j, l)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Mₙ(Mₘ(R)) ≃ Mₘ(Mₙ(R)) -/
def swap : Matrix (I × J) (K × L) R ≃ Matrix (J × I) (L × K) R where
  toFun m ji kl := m (ji.2, ji.1) (kl.2, kl.1)
  invFun n ij kl := n (ij.2, ij.1) (kl.2, kl.1)
  left_inv _ := rfl
  right_inv _ := rfl

section AddCommMonoid
variable [AddCommMonoid R]

/-- Mₙ(Mₘ(R)) ≃+ Mₙₘ(R) -/
def comp_addHom : Matrix I J (Matrix K L R) ≃+ Matrix (I × K) (J × L) R :=
{ Matrix.comp I J K L R with
  map_add' := fun _ _ ↦ rfl
}

/-- Mₙ(Mₘ(R)) ≃+ Mₘ(Mₙ(R)) -/
def swap_addHom : Matrix (I × J) (K × L) R ≃+ Matrix (J × I) (L × K) R :=
{ Matrix.swap I J K L R with
  map_add' := fun _ _ ↦ rfl
}

end AddCommMonoid

section Semiring
variable [Semiring R][Fintype I][Fintype J] [DecidableEq I] [DecidableEq J]

/-- Mₙ(Mₘ(R)) ≃+* Mₙₘ(R) -/
def comp_ringHom : Matrix I I (Matrix J J R) ≃+* Matrix (I × J) (I × J) R :=
{ Matrix.comp_addHom I I J J R with
  map_mul' := fun _ _ ↦ by
    ext _ _
    refine (Matrix.sum_apply _ _ _ _).trans $ Eq.symm Fintype.sum_prod_type
}

/-- Mₙ(Mₘ(R)) ≃+* Mₘ(Mₙ(R)) -/
def swap_ringHom : Matrix (I × J) (I × J) R ≃+* Matrix (J × I) (J × I) R :=
{ Matrix.swap_addHom I J I J R with
  map_mul' := fun _ _ ↦ by
    ext _ _
    simp only [swap_addHom, swap, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, mul_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
}

end Semiring

section Algebra

variable (K : Type*) [CommSemiring K] [Semiring R] [Fintype I] [Fintype J] [Algebra K R]
variable [DecidableEq I] [DecidableEq J]

/-- Mₙ(Mₘ(R)) ≃ₐ[K] Mₙₘ(R) -/
def comp_algHom : Matrix I I (Matrix J J R) ≃ₐ[K] Matrix (I × J) (I × J) R :=
{ Matrix.comp_ringHom I J R with
  commutes' := fun c ↦ by
    ext ⟨i1, j1⟩ ⟨i2, j2⟩
    simp only [comp_ringHom, comp_addHom, comp, AddEquiv.toEquiv_eq_coe, RingEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk]
    simp only [algebraMap_eq_diagonal]; rw [Pi.algebraMap_def, Pi.algebraMap_def]
    rw [@Algebra.algebraMap_eq_smul_one', @Algebra.algebraMap_eq_smul_one']
    rw [← @diagonal_one, @diagonal_apply, @diagonal_apply]
    if hii: i1 = i2 then
      simp only [hii, ↓reduceIte, diagonal_one, smul_apply, Prod.mk.injEq, true_and]
      if hjj : j1 = j2 then subst hjj ; simp  else
        simp only [ne_eq, hjj, not_false_eq_true, one_apply_ne, smul_zero, ↓reduceIte]
    else simp only [hii, ↓reduceIte, zero_apply, Prod.mk.injEq]; tauto
}

/-- Mₙ(Mₘ(R)) ≃ₐ[K] Mₘ(Mₙ(R)) -/
def swap_algHom : Matrix (I × J) (I × J) R ≃ₐ[K] Matrix (J × I) (J × I) R :=
{ Matrix.swap_ringHom I J R with
  commutes' := fun c ↦ by
    ext ⟨i1, j1⟩ ⟨i2, j2⟩
    simp only [swap_ringHom, swap_addHom, swap, AddEquiv.toEquiv_eq_coe, RingEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      algebraMap_eq_diagonal]; rw [Pi.algebraMap_def, Pi.algebraMap_def,
      @Algebra.algebraMap_eq_smul_one', @diagonal_apply, @diagonal_apply]
    if hii: i1 = i2 then
      simp only [hii, ↓reduceIte, diagonal_one, smul_apply, Prod.mk.injEq, true_and]
      if hjj : j1 = j2 then simp only [hjj, and_self, ↓reduceIte] else
        simp only [ne_eq, hjj, not_false_eq_true, one_apply_ne, smul_zero, ↓reduceIte]; tauto
    else simp only [Prod.mk.injEq, hii, and_false, ↓reduceIte, false_and]
}


open BigOperators Matrix MulOpposite in
/-- Mn(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ -/
def matrixEquivMatrixMop_algebra (n : ℕ):
    Matrix (Fin n) (Fin n) Rᵐᵒᵖ ≃ₐ[K] (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ where
  toFun := fun M => MulOpposite.op (M.transpose.map (fun d => MulOpposite.unop d))
  invFun := fun M => (MulOpposite.unop M).transpose.map (fun d => MulOpposite.op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective $ by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop
  commutes' k := by
    simp only [algebraMap_apply, op_inj]; ext i j
    simp only [map_apply, transpose_apply, algebraMap_matrix_apply]
    if h : i = j then simp only [h, ↓reduceIte, algebraMap_apply, unop_op]
    else simp only [algebraMap_apply, h, ↓reduceIte, unop_eq_zero_iff, ite_eq_right_iff,
      op_eq_zero_iff]; tauto

end Algebra

end Matrix