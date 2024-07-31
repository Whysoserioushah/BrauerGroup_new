import Mathlib.LinearAlgebra.TensorPower
import BrauerGroup.Dual
import BrauerGroup.PiTensorProduct

import Mathlib.Algebra.Category.ModuleCat.Abelian

suppress_compilation


open TensorProduct PiTensorProduct CategoryTheory

abbrev TensorOfType (k V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V] (p q : ℕ) :=
   (⨂[k]^q V) →ₗ[k] (⨂[k]^p V)

namespace TensorOfType

section extendScalars

variable (k K V W W' : Type*)
variable {p q : ℕ}
variable [Field k] [Field K] [Algebra k K]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable [AddCommGroup W'] [Module k W']

variable {k V W} in
def _root_.LinearMap.extendScalars (f : V →ₗ[k] W) : K ⊗[k] V →ₗ[K] K ⊗[k] W :=
  { f.lTensor K with
    map_smul' := fun a x => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
        simp only [smul_tmul', smul_eq_mul, LinearMap.lTensor_tmul]
      | add => aesop }

variable {k V W} in
@[simp]
lemma _root_.LinearMap.extendScalars_apply (f : V →ₗ[k] W) (a : K) (v : V) :
    LinearMap.extendScalars K f (a ⊗ₜ v) = a ⊗ₜ f v := by
  simp only [LinearMap.extendScalars, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    LinearMap.lTensor_tmul]

@[simp]
lemma _root_.LinearMap.extendScalars_id :
    LinearMap.extendScalars K (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  ext
  simp

lemma _root_.LinearMap.extendScalars_comp (f : V →ₗ[k] W) (g : W →ₗ[k] W') :
    (g ∘ₗ f).extendScalars K = g.extendScalars K ∘ₗ f.extendScalars K := by
  ext v
  simp

variable {k V} (p) in
def _root_.Basis.extendScalarsTensorPower {ι : Type*} (b : Basis ι k V) :
  Basis (Fin p → ι) K (K ⊗[k] (⨂[k]^p V)) :=
Algebra.TensorProduct.basis K (piTensorBasis _ _ _ _ (fun _ => b))

@[simp]
lemma _root_.Basis.extendScalarsTensorPower_apply {ι : Type*} (b : Basis ι k V) (i : Fin p → ι) :
    Basis.extendScalarsTensorPower K p b i = 1 ⊗ₜ tprod k fun j => b (i j) := by
  simp only [Basis.extendScalarsTensorPower, Algebra.TensorProduct.basis_apply, piTensorBasis_apply]

variable {k V} (p) in
def _root_.Basis.tensorPowerExtendScalars {ι : Type*} (b : Basis ι k V) :
    Basis (Fin p → ι) K (⨂[K]^p $ K ⊗[k] V) :=
  piTensorBasis _ _ _ _ fun _ => Algebra.TensorProduct.basis K b

@[simp]
lemma _root_.Basis.tensorPowerExtendScalars_apply {ι : Type*} (b : Basis ι k V) (i : Fin p → ι) :
    Basis.tensorPowerExtendScalars K p b i = tprod K fun j => 1 ⊗ₜ[k] b (i j) := by
  simp only [Basis.tensorPowerExtendScalars, piTensorBasis_apply, Algebra.TensorProduct.basis_apply]

variable {k V} (p) in
def _root_.Basis.extendScalarsTensorPowerEquiv {ι : Type*} (b : Basis ι k V) :
    K ⊗[k] (⨂[k]^p V) ≃ₗ[K] (⨂[K]^p $ K ⊗[k] V) :=
  (b.extendScalarsTensorPower K p).equiv (b.tensorPowerExtendScalars K p) (Equiv.refl _)

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_apply {ι : Type*} (b : Basis ι k V)
    (i : Fin p → ι) :
    b.extendScalarsTensorPowerEquiv K p (1 ⊗ₜ tprod k fun j => b (i j)) =
    tprod K fun j => 1 ⊗ₜ[k] b (i j) := by
  simp only [Basis.extendScalarsTensorPowerEquiv]
  have := (b.extendScalarsTensorPower K p).equiv_apply (b' := b.tensorPowerExtendScalars K p) i
    (Equiv.refl _)
  simp only [Basis.extendScalarsTensorPower_apply, Equiv.refl_apply,
    Basis.tensorPowerExtendScalars_apply] at this
  exact this

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_symm_apply {ι : Type*} (b : Basis ι k V)
    (i : Fin p → ι) :
    (b.extendScalarsTensorPowerEquiv K p).symm (tprod K fun j => 1 ⊗ₜ[k] b (i j)) =
    1 ⊗ₜ[k] tprod k fun j => b (i j) := by
  simp only [Basis.extendScalarsTensorPowerEquiv, Basis.equiv_symm, Equiv.refl_symm]
  have := (b.tensorPowerExtendScalars K p).equiv_apply (b' := b.extendScalarsTensorPower K p) i
    (Equiv.refl _)
  simp only [Basis.tensorPowerExtendScalars_apply, Equiv.refl_apply,
    Basis.extendScalarsTensorPower_apply] at this
  exact this

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_apply' {ιV ιW : Type*}
    (bV : Basis ιV k V) (bW : Basis ιW k W)
    (iV : Fin p → ιV) (f : V →ₗ[k] W) :
    bW.extendScalarsTensorPowerEquiv K p (1 ⊗ₜ tprod k fun j => f $ bV (iV j)) =
    tprod K fun j => (1 : K) ⊗ₜ[k] (f $ bV (iV j)) := by
  have eq (j : Fin p) := bW.total_repr (f $ bV (iV j))
  dsimp only [Finsupp.total, Finsupp.lsum, Finsupp.sum, LinearEquiv.coe_mk, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, LinearMap.coe_mk, AddHom.coe_mk] at eq
  have eq' : (tprod k fun j ↦ f (bV $ iV j)) = tprod k fun j =>
    ∑ a ∈ (bW.repr (f (bV $ iV j))).support, (bW.repr (f (bV (iV j)))) a • bW a := by
    congr
    simp_rw [eq]
  rw [eq', MultilinearMap.map_sum_finset, tmul_sum, map_sum]
  simp_rw [MultilinearMap.map_smul_univ (tprod k), tmul_smul]
  have eq'' : ((tprod K) fun j ↦ (1 : K) ⊗ₜ[k] f (bV (iV j))) = tprod K fun j =>
    1 ⊗ₜ ∑ a ∈ (bW.repr (f (bV $ iV j))).support, (bW.repr (f (bV (iV j)))) a • bW a := by
    congr
    simp_rw [eq]
  rw [eq'']
  simp_rw [tmul_sum]
  rw [MultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [algebra_compatible_smul K, map_smul, map_prod]
  simp only [Basis.extendScalarsTensorPowerEquiv_apply, tmul_smul]
  rw [← MultilinearMap.map_smul_univ (tprod K)]
  congr 1
  ext i
  simp

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_symm_apply' {ιV ιW : Type*}
    (bV : Basis ιV k V) (bW : Basis ιW k W)
    (iV : Fin p → ιV) (f : V →ₗ[k] W) :
    (bW.extendScalarsTensorPowerEquiv K p).symm (tprod K fun j => (1 : K) ⊗ₜ[k] (f $ bV (iV j))) =
     (1 ⊗ₜ tprod k fun j => f $ bV (iV j)) := by
  apply_fun (bW.extendScalarsTensorPowerEquiv K p) using
    (bW.extendScalarsTensorPowerEquiv K p).injective
  simp only [LinearEquiv.apply_symm_apply, Basis.extendScalarsTensorPowerEquiv_apply']

set_option maxHeartbeats 500000 in
lemma _root_.Basis.extendScalarsTensorPowerEquiv_comp_extendScalars
    {ιV ιW : Type*}
    (bV : Basis ιV k V) (bW : Basis ιW k W)
    (f : V →ₗ[k] W) :
    (bW.extendScalarsTensorPowerEquiv K p).toLinearMap ∘ₗ
      (LinearMap.extendScalars K (PiTensorProduct.map fun _ => f)) =
    (PiTensorProduct.map fun _ => f.extendScalars K) ∘ₗ
      (bV.extendScalarsTensorPowerEquiv K p).toLinearMap := by
  ext v
  simp only [AlgebraTensorModule.curry_apply, LinearMap.compMultilinearMap_apply, curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.extendScalars_apply, map_tprod]
  have eq (j : Fin p) := bW.total_repr (f $ v j)
  dsimp only [Finsupp.total, Finsupp.lsum, Finsupp.sum, LinearEquiv.coe_mk, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, LinearMap.coe_mk, AddHom.coe_mk] at eq
  have eq' : (tprod k fun j ↦ f (v j)) = tprod k fun j =>
    ∑ a ∈ (bW.repr (f (v j))).support, (bW.repr (f (v j))) a • bW a := by
    congr
    simp_rw [eq]
  rw [eq']
  rw [MultilinearMap.map_sum_finset, tmul_sum, map_sum]
  simp_rw [MultilinearMap.map_smul_univ (tprod k), tmul_smul]
  rw [show ∑ x ∈ Fintype.piFinset fun j ↦ (bW.repr (f (v j))).support,
    (Basis.extendScalarsTensorPowerEquiv K p bW)
      ((∏ i : Fin p, (bW.repr (f (v i))) (x i)) • 1 ⊗ₜ[k] (tprod k) fun i ↦ bW (x i)) =
    ∑ x ∈ Fintype.piFinset fun j ↦ (bW.repr (f (v j))).support,
    (Basis.extendScalarsTensorPowerEquiv K p bW)
      (algebraMap k K (∏ i : Fin p, (bW.repr (f (v i))) (x i)) •
        1 ⊗ₜ[k] (tprod k) fun i ↦ bW (x i)) from Finset.sum_congr rfl fun _ _ => by
        rw [algebra_compatible_smul K, map_smul, map_prod]]
  simp_rw [map_smul]
  have eq''' (x : Fin p → ιW) :
      Basis.extendScalarsTensorPowerEquiv K p bW (1 ⊗ₜ[k] (tprod k) fun i ↦ bW (x i)) =
      tprod K fun i => 1 ⊗ₜ[k] bW (x i) := by
    rw [Basis.extendScalarsTensorPowerEquiv_apply]
  simp_rw [eq''']
  have eq₄ : (tprod k) v =
    tprod k fun i => ∑ a ∈ (bV.repr (v i)).support, bV.repr (v i) a • bV a := by
    congr
    ext j
    have := bV.total_repr (v j)
    simpa [Eq.comm, Finsupp.total] using this
  conv_rhs => rw [eq₄, MultilinearMap.map_sum_finset, tmul_sum, map_sum, map_sum]
  simp_rw [MultilinearMap.map_smul_univ (tprod k), tmul_smul]
  have eq₅ (x : Fin p → ιV) :
      Basis.extendScalarsTensorPowerEquiv K p bV
        ((∏ i : Fin p, (bV.repr (v i)) (x i)) • 1 ⊗ₜ[k] (tprod k) fun i ↦ bV (x i)) =
      algebraMap k K (∏ i : Fin p, (bV.repr (v i)) (x i)) • tprod K fun i => 1 ⊗ₜ[k] bV (x i) := by
    rw [algebra_compatible_smul K, map_smul, Basis.extendScalarsTensorPowerEquiv_apply]
  simp_rw [eq₅, map_smul, PiTensorProduct.map_tprod]
  simp only [LinearMap.extendScalars_apply, algebraMap_smul]
  have eq₆ (x : Fin p → ιW) :
      (∏ i : Fin p, (bW.repr (f (v i))) (x i)) • ((tprod K) fun i ↦ (1 : K) ⊗ₜ[k] bW (x i)) =
      tprod K fun i => (1 : K) ⊗ₜ[k] ((bW.repr (f (v i))) (x i) • bW (x i)) := by
    rw [algebra_compatible_smul K, map_prod, ← (tprod K).map_smul_univ]
    congr
    ext j
    simp
  simp_rw [eq₆]
  have eq₇ (x : Fin p → ιV) :
      (∏ i : Fin p, (bV.repr (v i)) (x i)) • ((tprod K) fun i ↦ (1 : K) ⊗ₜ[k] f (bV (x i))) =
      tprod K fun i => 1 ⊗ₜ[k] ((bV.repr (v i)) (x i) • f (bV (x i))):= by
    rw [algebra_compatible_smul K, map_prod, ← (tprod K).map_smul_univ]
    congr
    ext j
    simp
  simp_rw [eq₇]
  have eq₈ : (tprod K fun j ↦ (1 : K) ⊗ₜ[k] f (v j)) = tprod K fun j =>
    ∑ a ∈ (bW.repr (f (v j))).support, 1 ⊗ₜ ((bW.repr (f (v j))) a • bW a) := by
    simp_rw [← tmul_sum]
    congr
    ext j
    simp_rw [eq]
  rw [MultilinearMap.map_sum_finset] at eq₈
  rw [← eq₈]
  have eq₉ : (tprod K fun j ↦ (1 : K) ⊗ₜ[k] f (v j)) = tprod K fun j =>
    ∑ a ∈ (bV.repr (v j)).support, 1 ⊗ₜ (bV.repr (v j) a • f (bV a)) := by
    simp_rw [← tmul_sum]
    congr
    ext j
    have := bV.total_repr (v j)
    conv_lhs => erw [← this]
    erw [map_sum]
    congr
    ext i
    simp
  rw [MultilinearMap.map_sum_finset] at eq₉
  rw [← eq₉]

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

set_option maxHeartbeats 500000 in
@[simps toLinearMap]
def extendScalarsMap {V W : VectorSpaceWithTensorOfType k p q} (f : V ⟶ W) :
    V.extendScalars K ⟶ W.extendScalars K where
  __ := f.extendScalars K
  comm := by
    simp only [extendScalars_carrier, extendScalars_tensor]
    have := f.comm
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
