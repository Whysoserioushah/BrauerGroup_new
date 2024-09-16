-- Jujian Zhang

import BrauerGroup.FieldCatOver
import InfiniteGaloisTheory.Basic

universe u

open CategoryTheory BigOperators

variable {k : Type u} [Field k]

variable (G : FieldCatOver k ⥤ Grp)

section smul

variable (FF : FieldCatOver k ⥤ Grp)
variable (K : FieldCatOver k) (Ω : FieldCatOver K) [IsGalois K Ω]

example
    (σ : Ω ≃ₐ[K] Ω) (x : FF.obj (FieldCatOver.extend K Ω)) :
    FF.obj (FieldCatOver.extend K Ω) :=
FF.map
  ({ __ := σ.toAlgHom
     commutes' := fun r => σ.commutes (algebraMap k K r) }) x

instance : MulDistribMulAction (Ω ≃ₐ[K] Ω) (FF.obj (FieldCatOver.extend K Ω)) where
  smul σ x :=
    FF.map
    ({ __ := σ.toAlgHom
       commutes' := fun r => σ.commutes (algebraMap k K r) }) x
  one_smul x := by
    change FF.map _ _ = _
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom]
    exact congr($(FF.map_id _) x)
  mul_smul σ σ' x := by
    change FF.map _ _ = FF.map _ (FF.map _ _)
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom]
    erw [← CategoryTheory.comp_apply]
    rw [← FF.map_comp]
    rfl
  smul_mul σ x y := by
    change FF.map _ _ = FF.map _ _ * FF.map _ _
    rw [← map_mul]
  smul_one σ := by
    change FF.map _ _ = 1
    rw [map_one]

def FieldCatOver.galois_action_def (σ : Ω ≃ₐ[K] Ω) (x : FF.obj (FieldCatOver.extend K Ω)) :
  σ • x =
    FF.map ({ __ := σ.toAlgHom, commutes' := fun r => σ.commutes (algebraMap k K r) }) x := rfl

@[simps]
def FieldCatOver.toFixedPoint :
    (FF.obj K) →*
    FixedPoints.submonoid (Ω ≃ₐ[K] Ω) (FF.obj (FieldCatOver.extend K Ω)) where
  toFun x := ⟨FF.map (FieldCatOver.toExtend K Ω) x, fun σ => by
    rw [FieldCatOver.galois_action_def]
    erw [← CategoryTheory.comp_apply]
    rw [← FF.map_comp]
    congr
    ext x
    exact σ.commutes x⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp


end smul

class GaloisFunctor  : Prop where
  inj (K : FieldCatOver k) (Ω : FieldCatOver K) [IsGalois K Ω] :
    Function.Injective <| G.map (FieldCatOver.toExtend K Ω)
  induced_iso (K : FieldCatOver k) (Ω : FieldCatOver K) [IsGalois K Ω] :
    Function.Bijective <| FieldCatOver.toFixedPoint G K Ω
  union_eq_top (K : FieldCatOver k) (Ω : FieldCatOver K) [IsGalois K Ω] :
    (⨆ (L : FiniteGaloisIntermediateField K Ω),
      (MonoidHom.range
        (G.map
        ({
          __ := algebraMap L Ω
          commutes' := by intros; rfl
        }) : G.obj (FieldCatOver.extend K (.of K L)) →* G.obj (FieldCatOver.extend K Ω))) :
          Subgroup <| G.obj <| FieldCatOver.extend K Ω) = ⊤
