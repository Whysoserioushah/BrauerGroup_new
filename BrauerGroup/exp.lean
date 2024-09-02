import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

section mod

variable (K A B M : Type*) [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module Bᵐᵒᵖ M]
variable [IsScalarTower K A M] [IsScalarTower K Bᵐᵒᵖ M]

noncomputable def test : A ⊗[K] B →ₗ[K] M →ₗ[K] M :=
  TensorProduct.lift
  { toFun := fun a =>
    { toFun := fun b =>
      { toFun := fun m => a • (MulOpposite.op b • m)
        map_add' := by aesop
        map_smul' := by
          intro k m
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul Bᵐᵒᵖ, ← smul_assoc (MulOpposite.op b), smul_eq_mul,
            ← (Algebra.commutes k (MulOpposite.op b)), mul_smul, algebraMap_smul,
            algebra_compatible_smul A, ← smul_assoc, smul_eq_mul, ← Algebra.commutes k a,
            mul_smul, algebraMap_smul] }
      map_add' := by
        intros b b'
        ext m
        simp only [MulOpposite.op_add, add_smul, smul_add, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.add_apply]
      map_smul' := by
        intros k b
        ext m
        simp only [MulOpposite.op_smul, smul_assoc, LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, LinearMap.smul_apply]
        rw [algebra_compatible_smul A, ← smul_assoc a, smul_eq_mul,
            ← (Algebra.commutes k a), mul_smul, algebraMap_smul] }
    map_add' := by
      intros a a'
      ext b m
      simp only [add_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    map_smul' := by
      intros k a
      ext b m
      simp only [smul_assoc, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
        LinearMap.smul_apply] }


instance : Module (A ⊗[K] B) M := sorry

-- instance  : Module (A ⊗[K] Bᵐᵒᵖ) M :=
  -- instModuleTensorProduct_brauerGroup K A B M

end mod
