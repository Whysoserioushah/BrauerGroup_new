import BrauerGroup.TensorOfTypePQ.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

suppress_compilation

open TensorProduct PiTensorProduct CategoryTheory

structure VectorSpaceWithTensorOfType (k : Type*) (p q : ℕ) [Field k] where
(carrier : Type*)
[ab : AddCommGroup carrier]
[mod : Module k carrier]
(tensor : TensorOfType k carrier p q)

namespace VectorSpaceWithTensorOfType

section basic

variable {p q : ℕ}
variable {k : Type*} [Field k] (V V₁ V₂ V₃ W : VectorSpaceWithTensorOfType k p q)

instance : CoeSort (VectorSpaceWithTensorOfType k p q) Type* := ⟨carrier⟩
instance : AddCommGroup V := V.ab
instance : Module k V := V.mod

structure Hom extends V →ₗ[k] W where
  /--
  ⨂[k]^q V → ⨂[k]^q W
    |              |
    v              v
  ⨂[k]^p V → ⨂[k]^p W
  -/
  comm :
    W.tensor ∘ₗ (PiTensorProduct.map fun _ => toLinearMap) =
    (PiTensorProduct.map fun _ => toLinearMap) ∘ₗ V.tensor

instance : FunLike (Hom V W) V W where
  coe f := f.toLinearMap
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    aesop

instance : LinearMapClass (Hom V W) k V W where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

def Hom.id : Hom V V where
  __ := LinearMap.id
  comm := by ext; simp

variable {V₁ V₂ V₃} in
def Hom.comp (f : Hom V₁ V₂) (g : Hom V₂ V₃) : Hom V₁ V₃ where
  __ := g.toLinearMap ∘ₗ f.toLinearMap
  comm := by
    simp only
    rw [PiTensorProduct.map_comp, ← LinearMap.comp_assoc, g.comm, LinearMap.comp_assoc, f.comm,
      PiTensorProduct.map_comp]
    fapply Basis.ext (b := piTensorBasis _ _ _ _ fun _ => Basis.ofVectorSpace k V₁)
    intro v
    simp only [piTensorBasis_apply, Basis.coe_ofVectorSpace, LinearMap.coe_comp,
      Function.comp_apply, map_tprod]

instance : Category (VectorSpaceWithTensorOfType k p q) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance : FunLike (V ⟶ W) V W :=
  inferInstanceAs (FunLike (Hom V W) V W)

lemma Hom.toLinearMap_injective : Function.Injective (Hom.toLinearMap : (V ⟶ W) → V →ₗ[k] W) := by
  intro f g h
  refine DFunLike.ext _ _ ?_
  exact fun x => congr($h x)

@[simp]
lemma id_toLinearMap : (𝟙 V : Hom V V).toLinearMap = LinearMap.id := rfl

@[simp]
lemma comp_toLinearMap (f : V ⟶ V₁) (g : V₁ ⟶ V₂) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

instance : LinearMapClass (V ⟶ W) k V W :=
  inferInstanceAs (LinearMapClass (Hom V W) k V W)

end basic

section extendScalars

variable {p q : ℕ}
variable {k K : Type*}
variable [Field k] [Field K] [Algebra k K]

variable (K) in
@[simps tensor carrier]
def extendScalars (V : VectorSpaceWithTensorOfType k p q) :
    VectorSpaceWithTensorOfType K p q where
  carrier := K ⊗[k] V
  ab := inferInstance
  mod := inferInstance
  tensor := V.tensor.extendScalars K (Basis.ofVectorSpace k V)

instance (V : VectorSpaceWithTensorOfType k p q) : Module k (V.extendScalars K) :=
  inferInstanceAs $ Module k (K ⊗[k] V)

instance (V : VectorSpaceWithTensorOfType k p q) : IsScalarTower k K (V.extendScalars K) where
  smul_assoc a b x := by
    simp only [algebra_compatible_smul K, smul_eq_mul, Algebra.id.map_eq_id, _root_.map_mul,
      RingHomCompTriple.comp_apply, RingHom.id_apply, mul_smul]
    simp only [Algebra.id.map_eq_id, RingHomCompTriple.comp_apply, smul_eq_mul, _root_.map_mul,
      RingHom.id_apply, mul_smul]
    induction x using TensorProduct.induction_on
    · simp
    · rw [smul_tmul', smul_tmul', smul_tmul']
      congr
      simp only [smul_eq_mul]
      rw [algebra_compatible_smul K, smul_eq_mul]
    · aesop

variable (K) in
lemma extendScalars_map_comm {V W : VectorSpaceWithTensorOfType k p q} (f : V ⟶ W) :
    (W.tensor.extendScalars K (Basis.ofVectorSpace k W.carrier) ∘ₗ
    PiTensorProduct.map fun _ ↦ f.toLinearMap.extendScalars K) =
    (PiTensorProduct.map fun _ ↦ f.toLinearMap.extendScalars K) ∘ₗ
    V.tensor.extendScalars K (Basis.ofVectorSpace k V.carrier) := by
  have comm' :=
    congr(((Basis.ofVectorSpace k W).extendScalarsTensorPowerEquiv K p).toLinearMap ∘ₗ
      $(f.comm).extendScalars K ∘ₗ
      ((Basis.ofVectorSpace k V).extendScalarsTensorPowerEquiv K q).symm.toLinearMap)
  set lhs := _; set rhs := _; change lhs = rhs
  set lhs' := _; set rhs' := _; change lhs' = rhs' at comm'
  have eql : lhs = lhs' := by
    simp only [lhs, lhs']
    fapply Basis.ext (b := Basis.tensorPowerExtendScalars K q (Basis.ofVectorSpace k V))
    intro v
    simp only [Basis.tensorPowerExtendScalars_apply, LinearMap.coe_comp,
      Function.comp_apply, map_tprod, LinearMap.extendScalars_apply, LinearEquiv.coe_coe]
    have eq1 := (Basis.ofVectorSpace k V).extendScalarsTensorPowerEquiv_symm_apply K (p := q) v
    rw [eq1]
    simp only [LinearMap.extendScalars_apply, LinearMap.coe_comp, Function.comp_apply, map_tprod]
    change Basis.extendScalarsTensorPowerEquiv K p (Basis.ofVectorSpace k W.carrier) _ = _
    congr 1
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    conv_rhs => rw [← LinearMap.extendScalars_apply]
    refine DFunLike.congr_arg _ ?_
    simp only [Basis.extendScalarsTensorPowerEquiv_symm_apply']
  have eqr : rhs = rhs' := by
    simp only [rhs, rhs']
    fapply Basis.ext (b := Basis.tensorPowerExtendScalars K q (Basis.ofVectorSpace k V))
    intro v
    simp only [Basis.tensorPowerExtendScalars_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    have eq1 := (Basis.ofVectorSpace k V).extendScalarsTensorPowerEquiv_symm_apply K (p := q) v
    rw [eq1]
    simp only [LinearMap.extendScalars_apply, LinearMap.coe_comp,
      Function.comp_apply]
    delta TensorOfType.extendScalars TensorOfType.extendScalarsLinearMap
      TensorOfType.extendScalarsLinearMapToFun
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Basis.extendScalarsTensorPowerEquiv_symm_apply, LinearMap.extendScalars_apply]
    conv_rhs => rw [← LinearMap.comp_apply, ← LinearMap.extendScalars_apply]
    change _ =
      ((Basis.extendScalarsTensorPowerEquiv K p (Basis.ofVectorSpace k W.carrier)).toLinearMap ∘ₗ
      (LinearMap.extendScalars K ((PiTensorProduct.map fun _ ↦ f.toLinearMap) ∘ₗ V.tensor)))
      (1 ⊗ₜ[k] (tprod k) fun j ↦ (Basis.ofVectorSpace k V.carrier) (v j))
    rw [LinearMap.extendScalars_comp, ← LinearMap.comp_assoc,
      Basis.extendScalarsTensorPowerEquiv_comp_extendScalars (K := K) (bV := Basis.ofVectorSpace k V)
        (bW := Basis.ofVectorSpace k W.carrier) (f := f.toLinearMap)]
    rfl
  rw [eql, eqr, comm']

@[simps toLinearMap]
def extendScalarsMap {V W : VectorSpaceWithTensorOfType k p q} (f : V ⟶ W) :
    V.extendScalars K ⟶ W.extendScalars K where
  __ := f.extendScalars K
  comm := by
    simp only [extendScalars_carrier, extendScalars_tensor]
    apply extendScalars_map_comm

variable (k K p q) in
def extendScalarsFunctor : VectorSpaceWithTensorOfType k p q ⥤ VectorSpaceWithTensorOfType K p q where
  obj V := V.extendScalars K
  map := extendScalarsMap
  map_id V := Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, extendScalarsMap_toLinearMap, id_toLinearMap,
      LinearMap.extendScalars_id]
  map_comp f g := Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, extendScalarsMap_toLinearMap, comp_toLinearMap,
      LinearMap.extendScalars_comp]

end extendScalars

section twisedForm

variable (p q : ℕ)
variable {k : Type*} (K : Type*) [Field k] [Field K] [Algebra k K]
variable (V W : VectorSpaceWithTensorOfType k p q)

structure twisedForm extends
  VectorSpaceWithTensorOfType k p q,
  (V.extendScalars K) ≅ (toVectorSpaceWithTensorOfType.extendScalars K)

end twisedForm

end VectorSpaceWithTensorOfType
