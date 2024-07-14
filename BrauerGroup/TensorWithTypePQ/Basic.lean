import Mathlib.LinearAlgebra.TensorPower
import BrauerGroup.Dual

variable (k K V W : Type*) [CommSemiring k] [CommSemiring k]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]

open TensorProduct PiTensorProduct

abbrev TensorWithType (p q : ℕ) := (⨂[k]^p V) ⊗[k] (⨂[k]^q $ Module.Dual k V)

namespace TensorWithTypePQ

variable {k V W p q}

set_option maxHeartbeats 500000 in
noncomputable def toHom : TensorWithType k V p q →ₗ[k] ⨂[k]^q V →ₗ[k] ⨂[k]^p V :=
TensorProduct.lift
{ toFun := fun v =>
  { toFun := fun f =>
    { toFun := fun v' => dualTensorPower k V q f v' • v
      map_add' := by
        intros v₁ v₂
        simp only [map_add, add_smul]
      map_smul' := by
        intros a v
        simp only [LinearMapClass.map_smul, smul_eq_mul, mul_smul, RingHom.id_apply] }
    map_add' := by
      intros f₁ f₂
      ext v'
      simp only [map_add, LinearMap.add_apply, LinearMap.compMultilinearMap_apply, LinearMap.coe_mk,
        AddHom.coe_mk, add_smul]
    map_smul' := by
      intros a f
      ext v'
      simp only [LinearMapClass.map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul,
        LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] }
  map_add' := by
    intros v₁ v₂
    ext f w
    simp only [smul_add, LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
      dualTensorPower_tprod, LinearMap.add_apply]
  map_smul' := by
    intros a v
    ext f w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
      dualTensorPower_tprod, RingHom.id_apply, LinearMap.smul_apply]
    rw [smul_comm] }

lemma toHom_tprod_tmul_tprod_apply
    (v : Fin p → V) (f : Fin q → Module.Dual k V) (x : Fin q → V) :
    toHom (tprod k v ⊗ₜ[k] tprod k f) (tprod k x) =
    (∏ i : Fin q, f i (x i)) • tprod k v := by
  simp only [toHom, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, dualTensorPower_tprod]

noncomputable def induced (e : V ≃ₗ[k] W) : TensorWithType k V p q →ₗ[k] TensorWithType k W p q :=
TensorProduct.map
  (PiTensorProduct.map fun _ => e)
  (PiTensorProduct.map fun _ => Module.Dual.transpose e.symm)

@[simp]
lemma induced_tprod_tmul_tprod (e : V ≃ₗ[k] W) (v : Fin p → V) (f : Fin q → Module.Dual k V) :
    induced e (tprod k v ⊗ₜ[k] tprod k f) =
    tprod k (fun i => e (v i)) ⊗ₜ[k] tprod k (fun i => Module.Dual.transpose e.symm (f i)) := by
  simp only [induced, map_tmul, map_tprod, LinearEquiv.coe_coe]

noncomputable def congr (e : V ≃ₗ[k] W) : TensorWithType k V p q ≃ₗ[k] TensorWithType k W p q :=
LinearEquiv.ofLinear
  (induced e) (induced e.symm) (by
    ext w fw
    simp only [LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      induced_tprod_tmul_tprod, Module.Dual.transpose, LinearEquiv.symm_symm, LinearMap.flip_apply,
      LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
    congr 2
    ext i x
    simp only [LinearMap.llcomp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]) (by
    ext w fw
    simp only [LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      induced_tprod_tmul_tprod, Module.Dual.transpose, LinearMap.flip_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, LinearMap.id_coe, id_eq]
    congr 2
    ext i x
    simp only [LinearMap.llcomp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

@[simp]
lemma congr_apply (e : V ≃ₗ[k] W) (v : TensorWithType k V p q) :
    congr e v = induced e v := rfl

@[simp]
lemma congr_symm_apply (e : V ≃ₗ[k] W) (w : TensorWithType k W p q) :
    (congr e).symm w = induced e.symm w := rfl

end TensorWithTypePQ
