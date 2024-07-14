import Mathlib.LinearAlgebra.TensorPower
import BrauerGroup.Dual

universe u v

variable (k : Type u) (V : Type v) [CommSemiring k] [AddCommMonoid V] [Module k V]

open TensorProduct PiTensorProduct

abbrev TensorWithType (p q : ℕ) := (⨂[k]^p V) ⊗[k] (⨂[k]^q $ Module.Dual k V)

namespace TensorWithTypePQ


variable {k V p q}
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

def toHom_tmul_tprod_tprod_apply
    (v : Fin p → V) (f : Fin q → Module.Dual k V) (x : Fin q → V) :
    toHom (tprod k v ⊗ₜ[k] tprod k f) (tprod k x) =
    (∏ i : Fin q, f i (x i)) • tprod k v := by
  simp only [toHom, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, dualTensorPower_tprod]

end TensorWithTypePQ
