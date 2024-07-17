import Mathlib.LinearAlgebra.TensorPower
import BrauerGroup.Dual
import BrauerGroup.PiTensorProduct

suppress_compilation


open TensorProduct PiTensorProduct

abbrev TensorOfType (k V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V] (p q : ℕ) :=
  (⨂[k]^p V) ⊗[k] (⨂[k]^q $ Module.Dual k V)

namespace TensorOfType

section basic

variable {k K V W V₁ V₂ V₃} {p q : ℕ}

variable [CommSemiring k] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid V₁] [Module k V₁]
variable [AddCommMonoid V₂] [Module k V₂]
variable [AddCommMonoid V₃] [Module k V₃]
variable [AddCommMonoid W] [Module k W]

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

noncomputable def inducedLinearMap (e : V ≃ₗ[k] W) : TensorOfType k V p q →ₗ[k] TensorOfType k W p q :=
  TensorProduct.map
    (PiTensorProduct.map fun _ => e)
    (PiTensorProduct.map fun _ => Module.Dual.transpose e.symm)

def induced (v : TensorOfType k V p q) (e : V ≃ₗ[k] W) : TensorOfType k W p q :=
  inducedLinearMap e v

@[simp]
lemma induced_zero (e : V ≃ₗ[k] W)  : (0 : TensorOfType k V p q).induced e = 0 :=
  (inducedLinearMap e).map_zero

@[simp]
lemma induced_smul (v : TensorOfType k V p q) (e : V ≃ₗ[k] W) (a : k) :
    (a • v).induced e = a • v.induced e :=
  (inducedLinearMap e).map_smul a v

lemma induced_add (v₁ v₂ : TensorOfType k V p q) (e : V ≃ₗ[k] W) :
    (v₁ + v₂).induced e = v₁.induced e + v₂.induced e :=
  (inducedLinearMap e).map_add v₁ v₂

@[simp]
lemma inducedLinearMap_tprod_tmul_tprod
    (e : V ≃ₗ[k] W) (v : Fin p → V) (f : Fin q → Module.Dual k V) :
    inducedLinearMap e (tprod k v ⊗ₜ[k] tprod k f) =
    tprod k (fun i => e (v i)) ⊗ₜ[k] tprod k (fun i => Module.Dual.transpose e.symm (f i)) := by
  simp only [inducedLinearMap, map_tmul, map_tprod, LinearEquiv.coe_coe]

@[simp]
lemma induced_tprod_tmul_tprod (v : Fin p → V) (f : Fin q → Module.Dual k V) (e : V ≃ₗ[k] W)  :
    induced (tprod k v ⊗ₜ[k] tprod k f : TensorOfType k V p q) e =
    tprod k (fun i => e (v i)) ⊗ₜ[k] tprod k (fun i => Module.Dual.transpose e.symm (f i)) :=
  inducedLinearMap_tprod_tmul_tprod e v f

@[simp]
lemma inducedLinearMap_refl :
    inducedLinearMap (p := p) (q := q) (LinearEquiv.refl k V) = LinearMap.id := by
  ext v f
  simp only [inducedLinearMap, LinearEquiv.refl_toLinearMap, PiTensorProduct.map_id, Module.Dual.transpose,
    LinearEquiv.refl_symm, LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply,
    curry_apply, LinearMap.coe_restrictScalars, map_tmul, LinearMap.id_coe, id_eq, map_tprod,
    LinearMap.flip_apply]
  congr 2

@[simp] lemma induced_refl (v : TensorOfType k V p q) : v.induced (LinearEquiv.refl k V) = v :=
  congr($inducedLinearMap_refl v)

lemma inducedLinearMap_trans (e : V₁ ≃ₗ[k] V₂) (f : V₂ ≃ₗ[k] V₃) :
    inducedLinearMap (p := p) (q := q) (e ≪≫ₗ f) =
    inducedLinearMap (p := p) (q := q) f ∘ₗ inducedLinearMap (p := p) (q := q) e := by
  ext v g
  simp only [LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, inducedLinearMap_tprod_tmul_tprod, LinearEquiv.trans_apply,
    Module.Dual.transpose, LinearEquiv.trans_symm, LinearMap.flip_apply, LinearMap.coe_comp,
    Function.comp_apply]
  congr 2

lemma induced_trans (v : TensorOfType k V₁ p q) (e : V₁ ≃ₗ[k] V₂) (f : V₂ ≃ₗ[k] V₃) :
    v.induced (e ≪≫ₗ f) = (v.induced e).induced f :=
  congr($(inducedLinearMap_trans e f) v)

noncomputable def congr (e : V ≃ₗ[k] W) : TensorOfType k V p q ≃ₗ[k] TensorOfType k W p q :=
LinearEquiv.ofLinear
  (inducedLinearMap e) (inducedLinearMap e.symm) (by
    ext w fw
    simp only [LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      inducedLinearMap_tprod_tmul_tprod, Module.Dual.transpose, LinearEquiv.symm_symm, LinearMap.flip_apply,
      LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
    congr 2
    ext i x
    simp only [LinearMap.llcomp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]) (by
    ext w fw
    simp only [LinearMap.compMultilinearMap_apply, AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      inducedLinearMap_tprod_tmul_tprod, Module.Dual.transpose, LinearMap.flip_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, LinearMap.id_coe, id_eq]
    congr 2
    ext i x
    simp only [LinearMap.llcomp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

@[simp]
lemma congr_apply (e : V ≃ₗ[k] W) (v : TensorOfType k V p q) :
    congr e v = inducedLinearMap e v := rfl

@[simp]
lemma congr_symm_apply (e : V ≃ₗ[k] W) (w : TensorOfType k W p q) :
    (congr e).symm w = inducedLinearMap e.symm w := rfl

end basic

section extendScalars

variable (k K V W : Type*)
variable {p q : ℕ}
variable [CommRing k] [CommRing K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

def extendScalarsLinearMap : TensorOfType k V p q →ₗ[k] TensorOfType K (K ⊗[k] V) p q :=
  let f1 : (⨂[k]^p V) →ₗ[k] ⨂[K]^p (K ⊗[k] V) := PiTensorProduct.extendScalars k K _
  let f2 : (⨂[k]^q (Module.Dual k V)) →ₗ[k] ⨂[K]^q (Module.Dual K (K ⊗[k] V)) :=
    { PiTensorProduct.map fun _ => Module.Dual.extendScalars k K V with
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

variable {k V}
def extendScalars (v : TensorOfType k V p q) : TensorOfType K (K ⊗[k] V) p q :=
  extendScalarsLinearMap k K V v

@[simp]
lemma extendScalars_zero : (0 : TensorOfType k V p q).extendScalars K = 0 :=
  (extendScalarsLinearMap k K V).map_zero

lemma extendScalars_smul (v : TensorOfType k V p q) (a : k) :
    (a • v).extendScalars K = a • v.extendScalars K :=
  (extendScalarsLinearMap k K V).map_smul a v

lemma extendScalars_add (v₁ v₂ : TensorOfType k V p q) :
    (v₁ + v₂).extendScalars K = v₁.extendScalars K + v₂.extendScalars K :=
  (extendScalarsLinearMap k K V).map_add v₁ v₂

@[simp]
lemma extendScalarsLinearMap_tprod_tmul_tprod (v : Fin p → V) (f : Fin q → Module.Dual k V) :
    extendScalarsLinearMap k K V ((tprod k v) ⊗ₜ (tprod k f)) =
    (tprod K ((1 : K) ⊗ₜ v ·)) ⊗ₜ
    (tprod K $ fun i => Module.Dual.extendScalars k K V (1 ⊗ₜ f i)) := by
  simp only [extendScalarsLinearMap, LinearMap.coe_comp, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, lift.tmul, AddHom.coe_mk, extendScalars_tprod, map_tprod]

@[simp]
lemma extendScalars_tprod_tmul_tprod (v : Fin p → V) (f : Fin q → Module.Dual k V) :
    extendScalars K ((tprod k v) ⊗ₜ[k] (tprod k f) : TensorOfType k V p q) =
    (tprod K ((1 : K) ⊗ₜ v ·)) ⊗ₜ
    (tprod K $ fun i => Module.Dual.extendScalars k K V (1 ⊗ₜ f i)) :=
  extendScalarsLinearMap_tprod_tmul_tprod _ _ _

lemma extendScalarsLinearMap_tprod_tmul_tprod_toHom_apply
    (v : Fin p → V) (f : Fin q → Module.Dual k V) (w : Fin q → V) :
    toHom (extendScalarsLinearMap k K V ((tprod k v) ⊗ₜ (tprod k f))) (tprod K (1 ⊗ₜ w ·)) =
    (∏ x : Fin q, (f x) (w x)) • (tprod K) (1 ⊗ₜ v ·) := by
  simp only [extendScalarsLinearMap_tprod_tmul_tprod, toHom_tprod_tmul_tprod_apply,
    Module.Dual.extendScalars_tmul_apply_tmul, mul_one]
  simp_rw [← Algebra.algebraMap_eq_smul_one]
  rw [← map_prod]
  rw [algebraMap_smul]

end extendScalars

end TensorOfType

structure VectorSpaceWithTensorOfType (k : Type*) (p q : ℕ) [CommRing k] where
(carrier : Type*)
[ab : AddCommGroup carrier]
[mod : Module k carrier]
(tensor : TensorOfType k carrier p q)

namespace VectorSpaceWithTensorOfType

section basic

variable {p q : ℕ}
variable {k : Type*} [CommRing k] (V V₁ V₂ V₃ W : VectorSpaceWithTensorOfType k p q)

instance : CoeSort (VectorSpaceWithTensorOfType k p q) Type* := ⟨carrier⟩
instance : AddCommGroup V := V.ab
instance : Module k V := V.mod

noncomputable def hom := TensorOfType.toHom V.tensor


structure Equiv extends V ≃ₗ[k] W where
  map_tensor : V.tensor.induced toLinearEquiv = W.tensor

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
  map_tensor := by
    simp only [TensorOfType.induced_refl]

@[simp]
lemma Equiv.refl_apply (v : V) : (Equiv.refl V) v = v := rfl

variable {V W}
@[symm, simps toLinearEquiv]
def Equiv.symm (e : Equiv V W) : Equiv W V where
  __ := e.toLinearEquiv.symm
  map_tensor := by
    simp only
    rw [← congr(($e.map_tensor).induced e.toLinearEquiv.symm)]
    rw [← TensorOfType.induced_trans]
    simp only [LinearEquiv.self_trans_symm, TensorOfType.induced_refl]

variable {V₁ V₂ V₃} in
@[trans, simps toLinearEquiv]
def Equiv.trans (e : Equiv V₁ V₂) (f : Equiv V₂ V₃) : Equiv V₁ V₃ where
  __ := (e.toLinearEquiv.trans f.toLinearEquiv)
  map_tensor := by
    simp only [TensorOfType.induced_trans, e.map_tensor, f.map_tensor]

lemma Equiv.trans_apply (e : Equiv V₁ V₂) (f : Equiv V₂ V₃) (v : V₁) :
    (e.trans f) v = f (e v) := by rfl

end basic

section extendScalars

variable {p q : ℕ}
variable {k : Type*} (K : Type*)
variable [CommRing k] [CommRing K] [Algebra k K]

@[simps tensor]
def extendScalars (V : VectorSpaceWithTensorOfType k p q) :
    VectorSpaceWithTensorOfType K p q where
  carrier := K ⊗[k] V
  ab := inferInstance
  mod := inferInstance
  tensor := V.tensor.extendScalars K

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

def Equiv.extendScalarsAux {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W) :
    (V.extendScalars K) ≃ₗ[K] (W.extendScalars K) :=
  LinearEquiv.ofLinear
    { LinearMap.lTensor K e.toLinearEquiv.toLinearMap with
      map_smul' := fun a x =>
        show LinearMap.lTensor K e.toLinearEquiv.toLinearMap _ =
          a • LinearMap.lTensor K e.toLinearEquiv.toLinearMap _ by
        induction x using TensorProduct.induction_on with
        | zero =>
          simp only [smul_zero, map_zero]
        | tmul x y =>
          rw [smul_tmul']
          simp only [smul_eq_mul, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, smul_tmul']
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add, smul_add]
          }
    { LinearMap.lTensor K e.symm.toLinearEquiv.toLinearMap with
      map_smul' := fun a x =>
        show LinearMap.lTensor K e.symm.toLinearEquiv.toLinearMap _ =
          a • LinearMap.lTensor K e.symm.toLinearEquiv.toLinearMap _ by
        induction x using TensorProduct.induction_on with
        | zero =>
          simp only [smul_zero, map_zero]
        | tmul x y =>
          rw [smul_tmul']
          simp only [smul_eq_mul, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, smul_tmul']
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add, smul_add] }
    (by
      ext x
      change (LinearMap.lTensor _ _) (LinearMap.lTensor _ _ _) = _
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      simp only [symm_toLinearEquiv, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, LinearMap.lTensor_id, LinearMap.id_coe, id_eq])
    (by
      ext x
      change (LinearMap.lTensor _ _) (LinearMap.lTensor _ _ _) = _
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      simp only [symm_toLinearEquiv, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, LinearMap.lTensor_id, LinearMap.id_coe, id_eq])

@[simp]
lemma Equiv.extendScalarsAux_apply_tmul
    {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W)
    (a : K) (v : V) :
    e.extendScalarsAux K (a ⊗ₜ v) = a ⊗ₜ e v := by rfl

@[simp]
lemma Equiv.extendScalarsAux_refl
    (V : VectorSpaceWithTensorOfType k p q) :
    (Equiv.refl V).extendScalarsAux K = Equiv.refl (V.extendScalars K) := by
  ext x
  induction x using TensorProduct.induction_on
  · simp
  · rfl
  · aesop

lemma Equiv.extendScalarsAux_symm
    {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W) :
    e.symm.extendScalarsAux K =
    (e.extendScalarsAux K).symm := by
  ext x
  induction x using TensorProduct.induction_on
  · simp
  · rfl
  · aesop

lemma Equiv.extendScalarsAux_trans
    {V₁ V₂ V₃ : VectorSpaceWithTensorOfType k p q} (e : Equiv V₁ V₂) (f : Equiv V₂ V₃) :
    (e.trans f).extendScalarsAux K =
    (e.extendScalarsAux K).trans (f.extendScalarsAux K) := by
  ext x
  induction x using TensorProduct.induction_on
  · simp
  · rfl
  · aesop

lemma Equiv.extendScalarsAux_map_tensor_aux
    {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W)
    (x : TensorOfType k V p q) :
    (x.extendScalars K).induced (e.extendScalarsAux K) =
    (x.induced e.toLinearEquiv).extendScalars K := by
  induction x using TensorProduct.induction_on with
    | zero =>
      simp only [TensorOfType.extendScalars_zero, TensorOfType.induced_zero]
    | tmul v f =>
      induction v using PiTensorProduct.induction_on with
      | smul_tprod a v =>
        induction f using PiTensorProduct.induction_on with
        | smul_tprod b f =>
          simp only [tmul_smul, ← smul_tmul', TensorOfType.extendScalars_smul,
            TensorOfType.induced_smul, TensorOfType.induced_tprod_tmul_tprod, ← mul_smul,
            TensorOfType.extendScalars_tprod_tmul_tprod]
          rw [algebra_compatible_smul (A := K), TensorOfType.induced_smul,
            TensorOfType.induced_tprod_tmul_tprod, algebraMap_smul]
          congr
          ext i w
          induction w using TensorProduct.induction_on with
          | zero => simp only [map_zero]
          | tmul a w =>
            simp only [Module.Dual.transpose, LinearMap.flip_apply, LinearMap.llcomp_apply,
              LinearEquiv.coe_coe]
            rw [← Equiv.extendScalarsAux_symm]
            erw [extendScalarsAux_apply_tmul (e := e.symm) K a w]
            simp only [Module.Dual.extendScalars_tmul_apply_tmul, one_mul, LinearMap.llcomp,
              LinearMap.flip, LinearMap.mk₂'ₛₗ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.lcomp,
              LinearMap.id_coe, id_eq, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
            erw [Module.Dual.extendScalars_tmul_apply_tmul]
            simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
            rfl
          | add w₁ w₂ h₁ h₂ =>
            simp only [map_add, h₁, h₂]
        | add x y hx hy =>
          simp only [tmul_add, TensorOfType.extendScalars_add, TensorOfType.induced_add, hx, hy]
      | add x y hx hy =>
        simp only [add_tmul, TensorOfType.extendScalars_add, TensorOfType.induced_add, hx, hy]
    | add x y hx hy =>
      simp only [TensorOfType.extendScalars_add, TensorOfType.induced_add, hx, hy]

def Equiv.extendScalars {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W) :
    Equiv (V.extendScalars K) (W.extendScalars K) where
  toLinearEquiv := e.extendScalarsAux K
  map_tensor := by
    simp only [symm_toLinearEquiv, extendScalars_tensor]
    rw [extendScalarsAux_map_tensor_aux, e.map_tensor]

lemma Equiv.extendScalars_apply_tmul
    {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W) (a : K) (v : V) :
    e.extendScalars K (a ⊗ₜ v) = a ⊗ₜ e v := by rfl

lemma Equiv.induced_extendScalars
    {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W)
    (x : TensorOfType k V p q) :
    (x.extendScalars K).induced (e.extendScalars K).toLinearEquiv =
    (x.induced e.toLinearEquiv).extendScalars K :=
  Equiv.extendScalarsAux_map_tensor_aux _ _ _

lemma Equiv.extendScalars_refl
    (V : VectorSpaceWithTensorOfType k p q) :
    (Equiv.refl V).extendScalars K = Equiv.refl (V.extendScalars K) :=
  DFunLike.ext _ _ fun x => congr($(Equiv.extendScalarsAux_refl K V) x)

lemma Equiv.extendScalars_symm
    {V W : VectorSpaceWithTensorOfType k p q} (e : Equiv V W) :
    e.symm.extendScalars K = (e.extendScalars K).symm :=
  DFunLike.ext _ _ fun x => congr($(Equiv.extendScalarsAux_symm K e) x)

lemma Equiv.extendScalars_trans
    {V₁ V₂ V₃ : VectorSpaceWithTensorOfType k p q} (e : Equiv V₁ V₂) (f : Equiv V₂ V₃) :
    (e.trans f).extendScalars K = (e.extendScalars K).trans (f.extendScalars K) :=
  DFunLike.ext _ _ fun x => congr($(Equiv.extendScalarsAux_trans K e f) x)

variable {K} in
def auxExtendAlgEquiv (V : VectorSpaceWithTensorOfType k p q) (σ : K ≃ₐ[k] K) :
    V.extendScalars K ≃ₗ[k] V.extendScalars K :=
  LinearEquiv.ofLinear
    (LinearMap.rTensor V σ.toLinearMap)
    (LinearMap.rTensor V σ.symm.toLinearMap)
    (by
      apply TensorProduct.ext
      ext a v
      simp only [LinearMap.compr₂_apply, mk_apply, LinearMap.coe_comp, Function.comp_apply]
      erw [LinearMap.rTensor_tmul]
      aesop)
    (by
      apply TensorProduct.ext
      ext a v
      simp only [LinearMap.compr₂_apply, mk_apply, LinearMap.coe_comp, Function.comp_apply]
      erw [LinearMap.rTensor_tmul]
      aesop)


@[simp]
lemma auxExtendAlgEquiv_tmul (V : VectorSpaceWithTensorOfType k p q) (σ : K ≃ₐ[k] K)
    (a : K) (v : V) :
    auxExtendAlgEquiv V σ (a ⊗ₜ v) = σ a ⊗ₜ v := rfl


-- def auxExtendAlgEquiv' (V : VectorSpaceWithTensorOfType k p q) (σ : K ≃ₐ[k] K) :
--     V.extendScalars K ≃ₗ[K] V.extendScalars K where
--   toFun := auxExtendAlgEquiv V σ
--   map_add' := (auxExtendAlgEquiv V σ).map_add
--   map_smul' a x := by
--     simp only [RingHom.id_apply]
--     induction x using TensorProduct.induction_on with
--     | zero => simp
--     | tmul b x =>
--       rw [smul_tmul']
--       simp only [smul_eq_mul, auxExtendAlgEquiv_tmul, _root_.map_mul]
--       rw [smul_tmul']
--       sorry
--     | add x y hx hy => aesop
--   invFun := (auxExtendAlgEquiv V σ).symm
--   left_inv := (auxExtendAlgEquiv V σ).left_inv
--   right_inv := (auxExtendAlgEquiv V σ).right_inv

variable {K} in
def auxRestrict {V W : VectorSpaceWithTensorOfType k p q}
    (f : Equiv (V.extendScalars K) (W.extendScalars K)) :
    V.extendScalars K ≃ₗ[k] W.extendScalars K where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [algebra_compatible_smul K, map_smul, algebraMap_smul]
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

@[simp]
lemma auxRestrict_apply {V W : VectorSpaceWithTensorOfType k p q}
    (f : Equiv (V.extendScalars K) (W.extendScalars K)) (x : V.extendScalars K) :
    auxRestrict f x = f x := rfl

variable {K} in
def Equiv.algEquivActAux
    {V W : VectorSpaceWithTensorOfType k p q}
    (σ : K ≃ₐ[k] K) (f : Equiv (V.extendScalars K) (W.extendScalars K)) :
    (V.extendScalars K) ≃ₗ[k] (W.extendScalars K) :=
  auxExtendAlgEquiv V σ ≪≫ₗ auxRestrict f ≪≫ₗ
  auxExtendAlgEquiv W σ.symm

lemma Equiv.algEquivActAux_tmul
    {V W : VectorSpaceWithTensorOfType k p q}
    (σ : K ≃ₐ[k] K) (f : Equiv (V.extendScalars K) (W.extendScalars K))
    (a : K) (v : V) :
    Equiv.algEquivActAux σ f (a ⊗ₜ v) =
    (W.auxExtendAlgEquiv σ.symm) (f (σ a ⊗ₜ[k] v)) := by
  simp only [algEquivActAux, LinearEquiv.trans_apply, auxExtendAlgEquiv_tmul, auxRestrict_apply]

def Equiv.algEquivAct
    {V W : VectorSpaceWithTensorOfType k p q}
    (σ : K ≃ₐ[k] K) (f : Equiv (V.extendScalars K) (W.extendScalars K)) :
    (V.extendScalars K) ≃ₗ[K] (W.extendScalars K) where
  toFun := Equiv.algEquivActAux σ f
  map_add' := map_add _
  map_smul' a x := by
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, RingHom.id_apply]
    | tmul b x =>
      rw [smul_tmul']
      simp only [algEquivActAux, smul_eq_mul, LinearEquiv.trans_apply, auxExtendAlgEquiv_tmul,
        auxRestrict_apply, RingHom.id_apply]
      simp only [_root_.map_mul, LinearEquiv.ofLinear_apply]
      rw [show (σ a * σ b) ⊗ₜ[k] x = (σ a * σ b) • (1 ⊗ₜ x) by simp only [smul_tmul',
        smul_eq_mul, mul_one], map_smul]
      have mem : f (1 ⊗ₜ[k] x) ∈ (⊤ : Submodule k _):= ⟨⟩
      rw [← span_tmul_eq_top k K W, mem_span_set] at mem
      obtain ⟨c, hc, (eq1 : (∑ i in c.support, _ • _) = _)⟩ := mem
      choose xᵢ yᵢ hxy using hc
      have eq1 : f (1 ⊗ₜ[k] x) = ∑ i in c.support.attach, (c i.1 • xᵢ i.2) ⊗ₜ[k] yᵢ i.2 := by
        rw [← eq1, ← Finset.sum_attach]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← smul_tmul', hxy i.2]
      rw [eq1, Finset.smul_sum, map_sum]
      rw [show ∑ i ∈ c.support.attach, (W.auxExtendAlgEquiv σ.symm)
        ((σ a * σ b) • (c i.1 • xᵢ i.2) ⊗ₜ[k] yᵢ i.2) =
        ∑ i ∈ c.support.attach, (W.auxExtendAlgEquiv σ.symm)
        (((σ a * σ b) • c i.1 • xᵢ i.2) ⊗ₜ[k] yᵢ i.2) from Finset.sum_congr rfl fun i _ => by
          rw [smul_tmul']]
      simp_rw [auxExtendAlgEquiv_tmul]
      rw [show ∑ i in c.support.attach, σ.symm ((σ a * σ b) • c i.1 • xᵢ i.2) ⊗ₜ[k] yᵢ i.2 =
        ∑ i in c.support.attach, (a * b) • ((c i.1 • σ.symm (xᵢ i.2)) ⊗ₜ[k] yᵢ i.2) from
          Finset.sum_congr rfl fun i _ => by
            congr 1
            simp only [smul_eq_mul, Algebra.mul_smul_comm, LinearMapClass.map_smul, _root_.map_mul,
              AlgEquiv.symm_apply_apply]]
      rw [← Finset.smul_sum]
      rw [show σ b ⊗ₜ[k] x = σ b • (1 ⊗ₜ x) by simp only [smul_tmul', smul_eq_mul,
        mul_one], map_smul, eq1]
      conv_rhs =>
        rw [Finset.smul_sum, map_sum,
        show ∑  i in c.support.attach, (W.auxExtendAlgEquiv σ.symm)
          (σ b • ((c i.1 • (xᵢ i.2)) ⊗ₜ[k] yᵢ i.2)) =
          ∑ i in c.support.attach, (W.auxExtendAlgEquiv σ.symm)
            ((σ b • (c i.1 • xᵢ i.2)) ⊗ₜ[k] yᵢ i.2) from Finset.sum_congr rfl fun i _ => by
            rw [smul_tmul']]
      simp_rw [auxExtendAlgEquiv_tmul]
      rw [show ∑ i in c.support.attach, σ.symm (σ b • c i.1 • xᵢ i.2) ⊗ₜ[k] yᵢ i.2 =
        ∑ i in c.support.attach, b • (c i.1 • σ.symm (xᵢ i.2) ⊗ₜ[k] yᵢ i.2) from
          Finset.sum_congr rfl fun i _ => by
            congr 1
            simp only [smul_eq_mul, Algebra.mul_smul_comm, LinearMapClass.map_smul, _root_.map_mul,
              AlgEquiv.symm_apply_apply]]
      rw [← Finset.smul_sum, ← mul_smul]
      congr
    | add x y hx hy => aesop
  invFun := (Equiv.algEquivActAux σ f).symm
  left_inv := (Equiv.algEquivActAux σ f).left_inv
  right_inv := (Equiv.algEquivActAux σ f).right_inv

end extendScalars

section twisedForm

variable (p q : ℕ)
variable {k : Type*} (K : Type*) [CommRing k] [CommRing K] [Algebra k K]
variable (V W : VectorSpaceWithTensorOfType k p q)

structure twisedForm extends
  VectorSpaceWithTensorOfType k p q,
  Equiv (V.extendScalars K) (toVectorSpaceWithTensorOfType.extendScalars K)

end twisedForm

end VectorSpaceWithTensorOfType
