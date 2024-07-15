import Mathlib.LinearAlgebra.TensorPower
import BrauerGroup.Dual
import BrauerGroup.PiTensorProduct

suppress_compilation

variable (k K V V₁ V₂ V₃ W : Type*)
variable [CommSemiring k] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid V₁] [Module k V₁]
variable [AddCommMonoid V₂] [Module k V₂]
variable [AddCommMonoid V₃] [Module k V₃]
variable [AddCommMonoid W] [Module k W]

open TensorProduct PiTensorProduct

abbrev TensorOfType (p q : ℕ) := (⨂[k]^p V) ⊗[k] (⨂[k]^q $ Module.Dual k V)

namespace TensorOfType

variable {k V W p q}

@[simps]
noncomputable def toHomAux (v : ⨂[k]^p V) (f : ⨂[k]^q (Module.Dual k V)) :
    ⨂[k]^q V →ₗ[k] ⨂[k]^p V where
  toFun v' := dualTensorPower k V q f v' • v
  map_add' v₁ v₂ := by simp only [map_add, add_smul]
  map_smul' a v' := by simp only [LinearMapClass.map_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

noncomputable def toHom : TensorOfType k V p q →ₗ[k] ⨂[k]^q V →ₗ[k] ⨂[k]^p V :=
TensorProduct.lift
{ toFun := fun v =>
  { toFun := fun f => toHomAux v f
    map_add' := by
      intros f₁ f₂
      ext v'
      simp only [LinearMap.compMultilinearMap_apply, toHomAux_apply, map_add, LinearMap.add_apply,
        add_smul]
    map_smul' := by
      intros a f
      ext v'
      simp only [LinearMap.compMultilinearMap_apply, toHomAux_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, mul_smul, RingHom.id_apply] }
  map_add' := by
    intros v₁ v₂
    ext f w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk, toHomAux_apply,
      dualTensorPower_tprod, smul_add, LinearMap.add_apply]
  map_smul' := by
    intros a v
    ext f w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk, toHomAux_apply,
      dualTensorPower_tprod, RingHom.id_apply, LinearMap.smul_apply]
    rw [smul_comm] }

@[simp]
lemma toHom_tprod_tmul_tprod_apply
    (v : Fin p → V) (f : Fin q → Module.Dual k V) (x : Fin q → V) :
    toHom (tprod k v ⊗ₜ[k] tprod k f) (tprod k x) =
    (∏ i : Fin q, f i (x i)) • tprod k v := by
  simp only [toHom, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, toHomAux_apply,
    dualTensorPower_tprod]

noncomputable def induced (e : V ≃ₗ[k] W) : TensorOfType k V p q →ₗ[k] TensorOfType k W p q :=
  TensorProduct.map
    (PiTensorProduct.map fun _ => e)
    (PiTensorProduct.map fun _ => Module.Dual.transpose e.symm)

@[simp]
lemma induced_tprod_tmul_tprod (e : V ≃ₗ[k] W) (v : Fin p → V) (f : Fin q → Module.Dual k V) :
    induced e (tprod k v ⊗ₜ[k] tprod k f) =
    tprod k (fun i => e (v i)) ⊗ₜ[k] tprod k (fun i => Module.Dual.transpose e.symm (f i)) := by
  simp only [induced, map_tmul, map_tprod, LinearEquiv.coe_coe]

@[simp]
lemma induced_refl :
    induced (p := p) (q := q) (LinearEquiv.refl k V) = LinearMap.id := by
  ext v f
  simp only [induced, LinearEquiv.refl_toLinearMap, PiTensorProduct.map_id, Module.Dual.transpose,
    LinearEquiv.refl_symm, LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply,
    curry_apply, LinearMap.coe_restrictScalars, map_tmul, LinearMap.id_coe, id_eq, map_tprod,
    LinearMap.flip_apply]
  congr 2

lemma induced_trans (e : V₁ ≃ₗ[k] V₂) (f : V₂ ≃ₗ[k] V₃) :
    induced (p := p) (q := q) (e ≪≫ₗ f) =
    induced (p := p) (q := q) f ∘ₗ induced (p := p) (q := q) e := by
  ext v g
  simp only [LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, induced_tprod_tmul_tprod, LinearEquiv.trans_apply,
    Module.Dual.transpose, LinearEquiv.trans_symm, LinearMap.flip_apply, LinearMap.coe_comp,
    Function.comp_apply]
  congr 2

noncomputable def congr (e : V ≃ₗ[k] W) : TensorOfType k V p q ≃ₗ[k] TensorOfType k W p q :=
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
lemma congr_apply (e : V ≃ₗ[k] W) (v : TensorOfType k V p q) :
    congr e v = induced e v := rfl

@[simp]
lemma congr_symm_apply (e : V ≃ₗ[k] W) (w : TensorOfType k W p q) :
    (congr e).symm w = induced e.symm w := rfl

section extendScalars

variable (k K V : Type*) [CommRing k] [CommRing K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

def extendScalars : TensorOfType k V p q →ₗ[k] TensorOfType K (K ⊗[k] V) p q :=
  let f1 : (⨂[k]^p V) →ₗ[k] ⨂[K]^p (K ⊗[k] V) := PiTensorProduct.extendScalars k K _
  let f2 : (⨂[k]^q (Module.Dual k V)) →ₗ[k] ⨂[K]^q (Module.Dual K (K ⊗[k] V)) :=
    { PiTensorProduct.map fun i => Module.Dual.extendScalars k K V with
      map_smul' := fun k hk => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.map_smul_of_tower,
          RingHom.id_apply] } ∘ₗ
    PiTensorProduct.extendScalars k K _
  TensorProduct.lift $
    { toFun := fun vp =>
      { toFun := fun fq => vp ⊗ₜ[K] f2 fq
        map_add' := fun fq₁ fq₂ => by
          simp only [map_add, tmul_add]
        map_smul' := fun a fq => by
          simp only [LinearMapClass.map_smul, tmul_smul, RingHom.id_apply] }
      map_add' := fun vp₁ vp₂ => by
        simp only
        ext fq
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.add_apply, add_tmul]
      map_smul' := fun a vp => by
        simp only [RingHom.id_apply]
        ext fq
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.smul_apply]
        rw [smul_tmul'] } ∘ₗ f1

@[simp]
lemma extendScalars_tprod_tmul_tprod (v : Fin p → V) (f : Fin q → Module.Dual k V) :
    extendScalars k K V ((tprod k v) ⊗ₜ (tprod k f)) =
    (tprod K ((1 : K) ⊗ₜ v ·)) ⊗ₜ
    (tprod K $ fun i => Module.Dual.extendScalars k K V (1 ⊗ₜ f i)) := by
  simp only [extendScalars, LinearMap.coe_comp, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, lift.tmul, AddHom.coe_mk, extendScalars_tprod, map_tprod]

lemma extendScalars_tprod_tmul_tprod_toHom_apply
    (v : Fin p → V) (f : Fin q → Module.Dual k V) (w : Fin q → V) :
    toHom (extendScalars k K V ((tprod k v) ⊗ₜ (tprod k f))) (tprod K (1 ⊗ₜ w ·)) =
    (∏ x : Fin q, (f x) (w x)) • (tprod K) (1 ⊗ₜ v ·) := by
  simp only [extendScalars_tprod_tmul_tprod, toHom_tprod_tmul_tprod_apply,
    Module.Dual.extendScalars_tmul_apply_tmul, mul_one]
  simp_rw [← Algebra.algebraMap_eq_smul_one]
  rw [← map_prod]
  rw [algebraMap_smul]

end extendScalars

end TensorOfType

structure VectorSpaceWithTensorOfType (p q : ℕ) where
(carrier : Type*)
[ab : AddCommMonoid carrier]
[mod : Module k carrier]
(tensor : TensorOfType k carrier p q)

namespace VectorSpaceWithTensorOfType

variable {k p q}
variable (V V₁ V₂ V₃ W : VectorSpaceWithTensorOfType k p q)

instance : AddCommMonoid V.carrier := V.ab
instance : Module k V.carrier := V.mod

instance : CoeSort (VectorSpaceWithTensorOfType k p q) Type* := ⟨carrier⟩

noncomputable def hom := TensorOfType.toHom V.tensor

structure Equiv extends V ≃ₗ[k] W where
  map_tensor : TensorOfType.induced toLinearEquiv V.tensor = W.tensor

instance : EquivLike (Equiv V W) V W where
  coe e x := e.toLinearEquiv x
  inv e x := e.toLinearEquiv.symm x
  left_inv e x := by simp
  right_inv e x := by simp
  coe_injective' := by
    rintro ⟨e, he⟩ ⟨f, hf⟩ h _
    simp only [DFunLike.coe_fn_eq, Equiv.mk.injEq]
    simpa using h

instance : LinearEquivClass (Equiv V W) k V W where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

@[refl, simps toLinearEquiv]
def Equiv.refl : Equiv V V where
  __ := LinearEquiv.refl k V
  map_tensor := by simp only [TensorOfType.induced_refl, LinearMap.id_coe, id_eq]

@[symm, simps toLinearEquiv]
def Equiv.symm (e : Equiv V W) : Equiv W V where
  __ := e.toLinearEquiv.symm
  map_tensor := by
    simp only
    have eq1 := e.map_tensor
    apply_fun (TensorOfType.induced e.toLinearEquiv.symm) at eq1
    rw [← LinearMap.comp_apply, ← TensorOfType.induced_trans, e.toLinearEquiv.self_trans_symm,
      TensorOfType.induced_refl, LinearMap.id_apply] at eq1
    rw [eq1]

@[trans, simps toLinearEquiv]
def Equiv.trans (e : Equiv V₁ V₂) (f : Equiv V₂ V₃) : Equiv V₁ V₃ where
  __ := (e.toLinearEquiv.trans f.toLinearEquiv)
  map_tensor := by
    simp only
    rw [TensorOfType.induced_trans, LinearMap.comp_apply, e.map_tensor, f.map_tensor]

end VectorSpaceWithTensorOfType
