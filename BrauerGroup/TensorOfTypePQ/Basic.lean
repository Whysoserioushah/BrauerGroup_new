import Mathlib.LinearAlgebra.TensorPower
import BrauerGroup.Dual
import BrauerGroup.PiTensorProduct
import BrauerGroup.LinearMap

suppress_compilation


open TensorProduct PiTensorProduct

abbrev TensorOfType (k V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V] (p q : ℕ) :=
   (⨂[k]^q V) →ₗ[k] (⨂[k]^p V)

namespace TensorOfType

section extendScalars

variable (k K V W W' : Type*)
variable {p q : ℕ}
variable [CommSemiring k] [Nontrivial k] [NoZeroDivisors k]
variable [CommSemiring K] [Nontrivial K] [NoZeroDivisors K] [Algebra k K]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]
variable [AddCommMonoid W'] [Module k W']

variable {k V} in
def extendScalarsLinearMapToFun {ι : Type*} (b : Basis ι k V) (f : TensorOfType k V p q) :
    TensorOfType K (K ⊗[k] V) p q :=
  (b.extendScalarsTensorPowerEquiv K p).toLinearMap ∘ₗ f.extendScalars K ∘ₗ
    (b.extendScalarsTensorPowerEquiv K q).symm.toLinearMap

variable {k V} in
lemma extendScalarsLinearMapToFun_add {ι : Type*} (b : Basis ι k V) (f g : TensorOfType k V p q) :
    extendScalarsLinearMapToFun K b (f + g) =
    extendScalarsLinearMapToFun K b f + extendScalarsLinearMapToFun K b g := by
  simp only [extendScalarsLinearMapToFun, LinearMap.lTensor_add]
  ext
  simp only [LinearMap.extendScalars, LinearMap.lTensor_add, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, LinearMap.add_apply, map_add]

variable {k V} in
lemma extendScalarsLinearMapToFun_smul {ι : Type*} (b : Basis ι k V)
    (a : k) (f : TensorOfType k V p q) :
    extendScalarsLinearMapToFun K b (a • f) = a • extendScalarsLinearMapToFun K b f := by
  simp only [extendScalarsLinearMapToFun, LinearMap.lTensor_smul, RingHom.id_apply]
  fapply Basis.ext (b := b.tensorPowerExtendScalars K q)
  intro i
  simp only [Basis.tensorPowerExtendScalars_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearMap.coe_mk, LinearMap.coe_toAddHom, Function.comp_apply, LinearMap.smul_apply,
    Basis.extendScalarsTensorPowerEquiv, Basis.equiv_symm]
  have := (b.tensorPowerExtendScalars K q).equiv_apply (b' := b.extendScalarsTensorPower K q)
    (i := i) (Equiv.refl _)
  simp only [Basis.tensorPowerExtendScalars_apply, Equiv.refl_apply,
    Basis.extendScalarsTensorPower_apply] at this
  erw [this]
  simp only [LinearMap.extendScalars_apply, LinearMap.smul_apply, tmul_smul]
  rw [algebra_compatible_smul K a, map_smul, algebraMap_smul]

variable {k V} in
@[simps]
def extendScalarsLinearMap {ι : Type*} (b : Basis ι k V) :
    TensorOfType k V p q →ₗ[k] TensorOfType K (K ⊗[k] V) p q where
  toFun f := extendScalarsLinearMapToFun K b f
  map_add' := extendScalarsLinearMapToFun_add K b
  map_smul' := extendScalarsLinearMapToFun_smul K b

variable {k V}
variable{ι : Type*} (b : Basis ι k V)

def extendScalars (v : TensorOfType k V p q) : TensorOfType K (K ⊗[k] V) p q :=
  extendScalarsLinearMap K b v

@[simp]
lemma extendScalars_zero : (0 : TensorOfType k V p q).extendScalars K b = 0 :=
  (extendScalarsLinearMap K b).map_zero

lemma extendScalars_smul (v : TensorOfType k V p q) (a : k) :
    (a • v).extendScalars K b = a • v.extendScalars K b :=
  (extendScalarsLinearMap K b).map_smul a v

lemma extendScalars_add (v₁ v₂ : TensorOfType k V p q) :
    (v₁ + v₂).extendScalars K b = v₁.extendScalars K b + v₂.extendScalars K b:=
  (extendScalarsLinearMap K b).map_add v₁ v₂

end extendScalars

end TensorOfType
