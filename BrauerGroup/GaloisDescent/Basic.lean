import BrauerGroup.TensorOfTypePQ.VectorSpaceWithTensorOfTypePQ

import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.FieldTheory.Galois

suppress_compilation

universe u v w

open TensorProduct PiTensorProduct CategoryTheory

variable {k K : Type u} {p q : ℕ} [Field k] [Field K] [Algebra k K]
variable {V W W' : VectorSpaceWithTensorOfType.{u, u} k p q}
variable {ιV ιW ιW' : Type*} (bV : Basis ιV k V) (bW : Basis ιW k W) (bW' : Basis ιW' k W')

open VectorSpaceWithTensorOfType

set_option maxHeartbeats 500000 in

lemma indeucedByGalAux_comm (σ : K ≃ₐ[k] K)
    (f : V.extendScalars K bV ⟶ W.extendScalars K bW) :
    (TensorOfType.extendScalars K bW W.tensor ∘ₗ
      PiTensorProduct.map fun _ ↦ LinearMap.galAct σ f.toLinearMap) =
    (PiTensorProduct.map fun _ ↦ LinearMap.galAct σ f.toLinearMap) ∘ₗ
      TensorOfType.extendScalars K bV V.tensor := by
  apply_fun LinearMap.restrictScalars k using LinearMap.restrictScalars_injective k
  rw [LinearMap.restrictScalars_comp, LinearMap.restrictScalars_comp,
    VectorSpaceWithTensorOfType.galAct_tensor_power_eq, ← LinearMap.comp_assoc,
    VectorSpaceWithTensorOfType.galAct_tensor_power_eq]
  have := VectorSpaceWithTensorOfType.oneTMulPow_comm_sq bW σ.toAlgHom
  simp only [extendScalars_carrier, extendScalars_tensor, AlgEquiv.toAlgHom_eq_coe] at this
  set lhs := _; change lhs = _
  rw [show lhs = (AlgHom.oneTMulPow p bW ↑σ ∘ₗ LinearMap.restrictScalars k (TensorOfType.extendScalars K bW W.tensor)) ∘ₗ
      LinearMap.restrictScalars k (PiTensorProduct.map fun _ ↦ f.toLinearMap) ∘ₗ
      AlgHom.oneTMulPow q bV σ.symm.toAlgHom by
    simp only [AlgEquiv.toAlgHom_eq_coe, extendScalars_carrier, lhs]
    rw [this]]
  clear lhs
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (f := AlgHom.oneTMulPow q bV _)]
  have eq := congr(LinearMap.restrictScalars k $f.comm)
  simp only [extendScalars_carrier, extendScalars_tensor, LinearMap.restrictScalars_comp] at eq
  rw [eq]
  rw [LinearMap.comp_assoc]
  have := VectorSpaceWithTensorOfType.oneTMulPow_comm_sq bV σ.symm.toAlgHom
  simp only [extendScalars_carrier, extendScalars_tensor, AlgEquiv.toAlgHom_eq_coe] at this
  set lhs := _; change lhs = _
  rw [show lhs = AlgHom.oneTMulPow p bW ↑σ ∘ₗ
      LinearMap.restrictScalars k (PiTensorProduct.map fun _ ↦ f.toLinearMap) ∘ₗ
      AlgHom.oneTMulPow p bV ↑σ.symm ∘ₗ
      LinearMap.restrictScalars k (TensorOfType.extendScalars K bV V.tensor) by
    simp only [AlgEquiv.toAlgHom_eq_coe, extendScalars_carrier, lhs]
    rw [this]]
  clear lhs
  simp only [extendScalars_carrier, ← LinearMap.comp_assoc]
  rfl

variable {bV bW} in
def homInducedByGal (σ : K ≃ₐ[k] K) (f : V.extendScalars K bV ⟶ W.extendScalars K bW) :
    V.extendScalars K bV ⟶ W.extendScalars K bW where
  __ := LinearMap.galAct σ f.toLinearMap
  comm := by
    simp only [extendScalars_carrier, extendScalars_tensor]
    apply indeucedByGalAux_comm

instance : SMul (K ≃ₐ[k] K) (V.extendScalars K bV ⟶ W.extendScalars K bW) where
  smul σ f := homInducedByGal σ f

@[simp]
lemma homInducedByGal_toLinearMap
    (σ : K ≃ₐ[k] K) (f : V.extendScalars K bV ⟶ W.extendScalars K bW) :
    (homInducedByGal σ f).toLinearMap = LinearMap.galAct σ f.toLinearMap := rfl

lemma homInducedByGal_comp (σ : K ≃ₐ[k] K)
    (f : V.extendScalars K bV ⟶ W.extendScalars K bW)
    (g : W.extendScalars K bW ⟶ W'.extendScalars K bW') :
    homInducedByGal σ (f ≫ g) =
    homInducedByGal σ f ≫ homInducedByGal σ g :=
  Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, homInducedByGal_toLinearMap, comp_toLinearMap]
    rw [LinearMap.galAct_comp]

@[simp]
lemma homInducedByGal_one (σ : K ≃ₐ[k] K) : homInducedByGal σ (𝟙 (V.extendScalars K bV)) = 𝟙 _ :=
  Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, homInducedByGal_toLinearMap, id_toLinearMap]
    rw [LinearMap.galAct_id]

variable {bV bW} in
@[simps]
def isoInducedByGal (σ : K ≃ₐ[k] K) (f : V.extendScalars K bV ≅ W.extendScalars K bW) :
    V.extendScalars K bV ≅ W.extendScalars K bW where
  hom := homInducedByGal σ f.hom
  inv := homInducedByGal σ f.inv
  hom_inv_id := Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, comp_toLinearMap, homInducedByGal_toLinearMap, id_toLinearMap]
    rw [← LinearMap.galAct_comp, ← comp_toLinearMap, f.hom_inv_id, id_toLinearMap,
      LinearMap.galAct_id]
  inv_hom_id := Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, comp_toLinearMap, homInducedByGal_toLinearMap, id_toLinearMap]
    rw [← LinearMap.galAct_comp, ← comp_toLinearMap, f.inv_hom_id, id_toLinearMap,
      LinearMap.galAct_id]

variable {bV} in
abbrev autInducedByGal (σ : K ≃ₐ[k] K) (f : V.extendScalars K bV ≅ V.extendScalars K bV) :
    V.extendScalars K bV ≅ V.extendScalars K bV :=
  isoInducedByGal σ f

lemma autoInducedByGal_id (σ : K ≃ₐ[k] K) :
    autInducedByGal σ (Iso.refl $ V.extendScalars K bV) = Iso.refl _ := by
  ext
  simp only [autInducedByGal, isoInducedByGal_hom, Iso.refl_hom, homInducedByGal_one]

lemma autInducedByGal_trans (σ : K ≃ₐ[k] K) (f g : V.extendScalars K bV ≅ V.extendScalars K bV) :
    autInducedByGal σ (f ≪≫ g) =
    autInducedByGal σ f ≪≫ autInducedByGal σ g := by
  ext
  simp only [autInducedByGal, isoInducedByGal_hom, Iso.trans_hom, homInducedByGal_comp]

variable (K) in
@[simps]
def act : Action (Type u) (MonCat.of $ K ≃ₐ[k] K) where
  V := Aut (V.extendScalars K bV)
  ρ :=
  { toFun := fun σ => autInducedByGal σ
    map_one' := funext fun i => Iso.ext $ Hom.toLinearMap_injective _ _ $
      AlgebraTensorModule.curry_injective $ LinearMap.ext_ring $ LinearMap.ext fun x ↦ by
        simp [show (1 : K →ₗ[k] K) = LinearMap.id by rfl]
    map_mul' := fun σ τ => funext fun i => Iso.ext $ Hom.toLinearMap_injective _ _ $
      AlgebraTensorModule.curry_injective $ LinearMap.ext_ring $ LinearMap.ext fun x ↦ by
        change _ = (autInducedByGal _ _).hom.toLinearMap (1 ⊗ₜ x)
        simp only [extendScalars_carrier, autInducedByGal, MonCat.mul_of, isoInducedByGal_hom,
          homInducedByGal_toLinearMap, AlgebraTensorModule.curry_apply, curry_apply,
          LinearMap.coe_restrictScalars, LinearMap.galAct_extendScalars_apply,
          show (AlgEquiv.toLinearMap (σ * τ)) = σ.toLinearMap ∘ₗ τ.toLinearMap by rfl,
          LinearMap.rTensor_comp, _root_.map_one, LinearMap.coe_comp, Function.comp_apply] }

variable (K) in
def rep : Rep (ULift ℤ) (K ≃ₐ[k] K) := Rep.linearization _ _ |>.obj $ act K bV

section

variable [IsGalois k K] (g : V.extendScalars K bV ⟶ W.extendScalars K bW)

lemma homInducedByGal_extendScalarsMap_eq (f : V ⟶ W) (σ : K ≃ₐ[k] K) :
    homInducedByGal σ (extendScalarsMap f bV bW) = extendScalarsMap f bV bW := by
  apply Hom.toLinearMap_injective
  simp only [extendScalars_carrier, homInducedByGal_toLinearMap, extendScalarsMap_toLinearMap]
  ext v
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.galAct_extendScalars_apply, _root_.map_one, LinearMap.extendScalars_apply,
    LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply]

-- this is weird, we need non-abelian group cohomology
example (n : ℤ) (e : Aut V) :
    Finsupp.single (autExtendScalars (K := K) e bV) ⟨n⟩  ∈ groupCohomology.H0 (rep K bV) := by
  classical
  simp only [rep, Representation.mem_invariants]
  intro σ
  erw [Rep.linearization_obj_ρ]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  simp only [act_V, act_ρ_apply]
  ext f
  have eq : autInducedByGal σ (autExtendScalars e bV) = autExtendScalars e bV := by
    ext
    simp only [isoInducedByGal_hom, autExtendScalars_hom]
    apply homInducedByGal_extendScalarsMap_eq
  rw [eq]



end
