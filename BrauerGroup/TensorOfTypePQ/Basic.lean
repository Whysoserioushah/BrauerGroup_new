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

lemma extendScalarsLinearMapToFun_apply_tmul
    {ι : Type*} (b : Basis ι k V) (f : TensorOfType k V p q)
    (a : Fin q → K) (v : Fin q → ι) :
    extendScalarsLinearMapToFun K b f (tprod K fun i => a i ⊗ₜ b (v i)) =
    (b.extendScalarsTensorPowerEquiv K p).toLinearMap
      ((∏ i : Fin q, a i) ⊗ₜ f (tprod k fun i => b (v i))) := by
  simp only [extendScalarsLinearMapToFun, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  have eq₁ (i : Fin q) : a i ⊗ₜ[k] b (v i) = a i • (1 ⊗ₜ[k] b (v i)) := by simp [smul_tmul']
  simp_rw [eq₁]
  rw [MultilinearMap.map_smul_univ, map_smul, map_smul]
  simp only [Basis.extendScalarsTensorPowerEquiv_symm_apply, LinearMap.extendScalars_apply,
    smul_tmul', smul_eq_mul, mul_one]

lemma extendScalarsLinearMapToFun_apply_one_tmul
    {ι : Type*} (b : Basis ι k V) (f : TensorOfType k V p q)
    (v : Fin q → ι) :
    extendScalarsLinearMapToFun K b f (tprod K fun i => 1 ⊗ₜ b (v i)) =
    (b.extendScalarsTensorPowerEquiv K p).toLinearMap
      (1 ⊗ₜ f (tprod k fun i => b (v i))) := by
  have := extendScalarsLinearMapToFun_apply_tmul k K V b f (fun _ : Fin q => 1) v
  simpa using this


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

lemma extendScalars_apply_tmul
    {ι : Type*} (b : Basis ι k V) (f : TensorOfType k V p q)
    (a : Fin q → K) (v : Fin q → ι) :
    f.extendScalars K b (tprod K fun i => a i ⊗ₜ b (v i)) =
    (b.extendScalarsTensorPowerEquiv K p).toLinearMap
      ((∏ i : Fin q, a i) ⊗ₜ f (tprod k fun i => b (v i))) := by
  apply extendScalarsLinearMapToFun_apply_tmul

lemma extendScalars_apply_one_tmul
    {ι : Type*} (b : Basis ι k V) (f : TensorOfType k V p q)
    (v : Fin q → ι) :
    f.extendScalars K b (tprod K fun i => 1 ⊗ₜ b (v i)) =
    (b.extendScalarsTensorPowerEquiv K p).toLinearMap
      (1 ⊗ₜ f (tprod k fun i => b (v i))) := by
  apply extendScalarsLinearMapToFun_apply_one_tmul

lemma extendScalarsTensorPowerEquiv_comp {ιV : Type*} (bV : Basis ιV k V)
    (f : TensorOfType k V p q) :
    ((Basis.extendScalarsTensorPowerEquiv K p bV).toLinearMap ∘ₗ LinearMap.extendScalars K f) =
    ((f.extendScalars K bV) ∘ₗ (Basis.extendScalarsTensorPowerEquiv K q bV).toLinearMap) := by
  fapply Basis.ext (b := Basis.extendScalarsTensorPower K q bV)
  intro v
  simp only [Basis.extendScalarsTensorPower_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.extendScalars_apply, Basis.extendScalarsTensorPowerEquiv_apply]
  set B := piTensorBasis (Fin p) k (fun _ => ιV) (fun _ => V) (fun _ => bV) with B_eq
  have eq₁ := B.total_repr (f ((tprod k) fun j ↦ bV (v j)))
  rw [← eq₁]
  dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
    Finsupp.sum]
  rw [tmul_sum, map_sum]
  set lhs := _; change lhs = _
  rw [show lhs =
    ∑ x ∈ (B.repr (f ((tprod k) fun j ↦ bV (v j)))).support,
    (B.repr (f ((tprod k) fun j ↦ bV (v j)))) x • (Basis.extendScalarsTensorPowerEquiv K p bV)
      (1 ⊗ₜ[k] B x) by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [tmul_smul, algebra_compatible_smul K, map_smul, algebraMap_smul]]
  clear lhs
  simp only [piTensorBasis_apply, Basis.extendScalarsTensorPowerEquiv_apply, B]
  simp only [← B_eq]
  rw [extendScalars_apply_one_tmul]
  conv_rhs => rw [← eq₁]
  dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
    Finsupp.sum]
  rw [tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [piTensorBasis_apply, tmul_smul, LinearMap.map_smul_of_tower, LinearEquiv.coe_coe,
    Basis.extendScalarsTensorPowerEquiv_apply, B]

lemma extendScalarsTensorPowerEquiv_comp_elementwise {ιV : Type*} (bV : Basis ιV k V)
    (f : TensorOfType k V p q) (x) :
    (Basis.extendScalarsTensorPowerEquiv K p bV).toLinearMap (LinearMap.extendScalars K f x) =
    (f.extendScalars K bV) (Basis.extendScalarsTensorPowerEquiv K q bV x) := by
  rw [← LinearMap.comp_apply, extendScalarsTensorPowerEquiv_comp, LinearMap.comp_apply]
  simp

end extendScalars

end TensorOfType
