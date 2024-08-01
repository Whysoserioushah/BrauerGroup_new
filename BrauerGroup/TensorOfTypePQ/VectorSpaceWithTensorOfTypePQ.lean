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

variable {V W} in
lemma Hom.comm_elementwise (f : Hom V W) (v : ⨂[k]^q V) :
    W.tensor ((PiTensorProduct.map fun _ => f.toLinearMap) v) =
    (PiTensorProduct.map fun _ => f.toLinearMap) (V.tensor v):=
  congr($f.comm v)

variable {V W} in
@[simp]
lemma Hom.comm_basis {ιV : Type*} (bV : Basis ιV k V) (f : Hom V W) (v : Fin q → ιV) :
    (PiTensorProduct.map fun _ => f.toLinearMap) (V.tensor $ tprod k fun i => bV (v i)) =
    W.tensor ((tprod k) fun i ↦ f.toLinearMap (bV (v i))) := by
  rw [← f.comm_elementwise, PiTensorProduct.map_tprod]

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
def extendScalars (V : VectorSpaceWithTensorOfType k p q) {ι : Type*} (b : Basis ι k V) :
    VectorSpaceWithTensorOfType K p q where
  carrier := K ⊗[k] V
  ab := inferInstance
  mod := inferInstance
  tensor := V.tensor.extendScalars K b

instance (V : VectorSpaceWithTensorOfType k p q) {ι : Type*} (b : Basis ι k V) :
    Module k (V.extendScalars K b):=
  inferInstanceAs $ Module k (K ⊗[k] V)

instance (V : VectorSpaceWithTensorOfType k p q) {ι : Type*} (b : Basis ι k V) :
    IsScalarTower k K (V.extendScalars K b) where
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
lemma extendScalars_map_comm
    {V W : VectorSpaceWithTensorOfType k p q} (f : V ⟶ W)
    {ιV ιW : Type*} (bV : Basis ιV k V) (bW : Basis ιW k W) :
    (W.tensor.extendScalars K bW ∘ₗ
      PiTensorProduct.map fun _ ↦ f.toLinearMap.extendScalars K) =
    (PiTensorProduct.map fun _ ↦ f.toLinearMap.extendScalars K) ∘ₗ
      V.tensor.extendScalars K bV := by
  have comm' :=
    congr((bW.extendScalarsTensorPowerEquiv K p).toLinearMap ∘ₗ
      $(f.comm).extendScalars K ∘ₗ
      (bV.extendScalarsTensorPowerEquiv K q).symm.toLinearMap)
  set lhs := _; set rhs := _; change lhs = rhs
  set lhs' := _; set rhs' := _; change lhs' = rhs' at comm'
  have eql : lhs = lhs' := by
    simp only [lhs, lhs']
    fapply Basis.ext (b := Basis.tensorPowerExtendScalars K q bV)
    intro v
    simp only [Basis.tensorPowerExtendScalars_apply, LinearMap.coe_comp,
      Function.comp_apply, map_tprod, LinearMap.extendScalars_apply, LinearEquiv.coe_coe]
    have eq1 := bV.extendScalarsTensorPowerEquiv_symm_apply K (p := q) v
    rw [eq1]
    simp only [LinearMap.extendScalars_apply, LinearMap.coe_comp, Function.comp_apply, map_tprod]
    change Basis.extendScalarsTensorPowerEquiv K p bW _ = _
    congr 1
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    conv_rhs => rw [← LinearMap.extendScalars_apply]
    refine DFunLike.congr_arg _ ?_
    simp only [Basis.extendScalarsTensorPowerEquiv_symm_apply']
  have eqr : rhs = rhs' := by
    simp only [rhs, rhs']
    fapply Basis.ext (b := Basis.tensorPowerExtendScalars K q bV)
    intro v
    simp only [Basis.tensorPowerExtendScalars_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    have eq1 := bV.extendScalarsTensorPowerEquiv_symm_apply K (p := q) v
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
      ((Basis.extendScalarsTensorPowerEquiv K p bW).toLinearMap ∘ₗ
      (LinearMap.extendScalars K ((PiTensorProduct.map fun _ ↦ f.toLinearMap) ∘ₗ V.tensor)))
      (1 ⊗ₜ[k] (tprod k) fun j ↦ bV (v j))
    rw [LinearMap.extendScalars_comp, ← LinearMap.comp_assoc,
      Basis.extendScalarsTensorPowerEquiv_comp_extendScalars (K := K) (bV := bV)
        (bW := bW) (f := f.toLinearMap)]
    rfl
  rw [eql, eqr, comm']

@[simps toLinearMap]
def extendScalarsMap {V W : VectorSpaceWithTensorOfType k p q} (f : V ⟶ W)
    {ιV ιW : Type*} (bV : Basis ιV k V) (bW : Basis ιW k W) :
    V.extendScalars K bV ⟶ W.extendScalars K bW where
  __ := f.extendScalars K
  comm := by
    simp only [extendScalars_carrier, extendScalars_tensor]
    apply extendScalars_map_comm

variable (k K p q) in
def extendScalarsFunctor : VectorSpaceWithTensorOfType k p q ⥤ VectorSpaceWithTensorOfType K p q where
  obj V := V.extendScalars K (Basis.ofVectorSpace k V)
  map f := extendScalarsMap f (Basis.ofVectorSpace k _) (Basis.ofVectorSpace k _)
  map_id V := Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, extendScalarsMap_toLinearMap, id_toLinearMap,
      LinearMap.extendScalars_id]
  map_comp f g := Hom.toLinearMap_injective _ _ $ by
    simp only [extendScalars_carrier, extendScalarsMap_toLinearMap, comp_toLinearMap,
      LinearMap.extendScalars_comp]

end extendScalars

section gal

variable {p q : ℕ} {ι k K : Type*} [Field k] [Field K] [Algebra k K]
variable {V : VectorSpaceWithTensorOfType k p q} (b : Basis ι k V)
variable (σ : K →ₐ[k] K)

set_option maxHeartbeats 500000 in
/--
(1 ⊗ σ) in general is not `K`-linear, but we have a commutative diagram nevertheless:
```
⨂[K]^q V_K -(1 ⊗ σ)^q-> ⨂[K]^q V_K
 |V_K.tensor                      |V_K.tensor
 v                                v
⨂[K]^p V_K -(1 ⊗ σ)^p-> ⨂[K]^p V_K
```
-/
lemma oneTMulPow_comm_sq_neZero_neZero [NeZero p] [NeZero q] :
    (V.extendScalars K b).tensor.restrictScalars k ∘ₗ σ.oneTMulPow q b =
    σ.oneTMulPow p b ∘ₗ
    (V.extendScalars K b).tensor.restrictScalars k := by
  set Bq := b.tensorPowerExtendScalars K q with Bq_eq
  set Bp := piTensorBasis (Fin p) k (fun _ => ι) (fun _ => V) (fun _ => b) with Bp_eq
  ext v
  rw [← Bq.total_repr v, Finsupp.total]
  dsimp only [extendScalars_carrier, extendScalars_tensor, Finsupp.coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Finsupp.sum, LinearMap.coe_comp,
    LinearMap.coe_restrictScalars, Function.comp_apply]
  simp only [Basis.tensorPowerExtendScalars_apply, map_sum, LinearMapClass.map_smul, Bq]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Bq_eq, TensorOfType.extendScalars_apply_one_tmul]
  simp only [Basis.coe_ofVectorSpace, LinearEquiv.coe_coe]
  rw [← (Basis.extendScalarsTensorPowerEquiv K p b).map_smul, smul_tmul', smul_eq_mul, mul_one]

  have eq₁ := (Bp.total_repr $ V.tensor ((tprod k) fun i ↦ b (x i)))
  dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
    Finsupp.sum] at eq₁
  simp only [piTensorBasis_apply, Bp] at eq₁
  simp only [← Bp_eq] at eq₁
  rw [← eq₁, tmul_sum, map_sum, map_sum]
  change _ = ∑ z ∈ _, _
  rw [show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (AlgHom.oneTMulPow p b σ)
    ((Basis.extendScalarsTensorPowerEquiv K p b)
    ((Bq.repr v) x ⊗ₜ[k]
      ((Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))) z • (tprod k) fun i ↦ b (z i)))) =
    ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    AlgHom.oneTMulPow p b σ
      (Basis.extendScalarsTensorPowerEquiv K p b $
        (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z • Bq.repr v x) • 1 ⊗ₜ[k]
        tprod k fun i => b (z i)) from Finset.sum_congr rfl fun z _ => by
          simp only [tmul_smul, smul_tmul', smul_eq_mul, mul_one],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    AlgHom.oneTMulPow p b σ
      (Basis.extendScalarsTensorPowerEquiv K p b $
        (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z • Bq.repr v x) • 1 ⊗ₜ[k]
        tprod k fun i => b (z i)) =
      ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    AlgHom.oneTMulPow p b σ
      ((Bp.repr (V.tensor $ tprod k fun i => b (x i)) z • Bq.repr v x) •
        Basis.extendScalarsTensorPowerEquiv K p b (1 ⊗ₜ[k] tprod k fun i => b (z i))) from
      Finset.sum_congr rfl fun z _ => by rw [map_smul],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    AlgHom.oneTMulPow p b σ
      ((Bp.repr (V.tensor $ tprod k fun i => b (x i)) z • Bq.repr v x) •
        Basis.extendScalarsTensorPowerEquiv K p b (1 ⊗ₜ[k] tprod k fun i => b (z i))) =
    ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    AlgHom.oneTMulPow p b σ
      ((Bp.repr (V.tensor $ tprod k fun i => b (x i)) z • Bq.repr v x) •
      tprod K fun i => 1 ⊗ₜ[k] b (z i)) from Finset.sum_congr rfl fun z _ => by
      rw [Basis.extendScalarsTensorPowerEquiv_apply],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    AlgHom.oneTMulPow p b σ
      ((Bp.repr (V.tensor $ tprod k fun i => b (x i)) z • Bq.repr v x) •
      tprod K fun i => 1 ⊗ₜ[k] b (z i)) =
    ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    AlgHom.oneTMulPow p b σ (Bq.repr v x • tprod K fun i => 1 ⊗ₜ[k] b (z i))) from
    Finset.sum_congr rfl fun z _ => by rw [← (AlgHom.oneTMulPow p b σ).map_smul, smul_assoc],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    AlgHom.oneTMulPow p b σ (Bq.repr v x • tprod K fun i => 1 ⊗ₜ[k] b (z i))) =
    ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    AlgHom.oneTMulPow p b σ ((∏ i : Fin p, if i = 0 then Bq.repr v x else 1) •
      tprod K fun i => 1 ⊗ₜ[k] b (z i))) from Finset.sum_congr rfl fun z _ => by
      simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    AlgHom.oneTMulPow p b σ ((∏ i : Fin p, if i = 0 then Bq.repr v x else 1) •
      tprod K fun i => 1 ⊗ₜ[k] b (z i))) =
      ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    AlgHom.oneTMulPow p b σ
      (tprod K fun i => (if i = 0 then Bq.repr v x else 1) ⊗ₜ[k] b (z i))) from
    Finset.sum_congr rfl fun z _ => by
      rw [← MultilinearMap.map_smul_univ]
      simp_rw [smul_tmul', smul_eq_mul, mul_one],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    AlgHom.oneTMulPow p b σ (tprod K fun i => (if i = 0 then Bq.repr v x else 1) ⊗ₜ[k] b (z i))) =
    ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    (σ $ Bq.repr v x) • (tprod K fun i => 1 ⊗ₜ[k] b (z i))) from Finset.sum_congr rfl fun z _ => by
        simp only [AlgHom.oneTMulPow_apply,
          show
            (∏ i : Fin p, σ (if i = 0 then Bq.repr v x else 1)) =
              (∏ i : Fin p, if i = 0 then (σ $ Bq.repr v x) else 1)
            from Finset.prod_congr rfl fun _ _ => by split_ifs <;> simp,
          Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte],
    show ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
    (σ $ Bq.repr v x) • (tprod K fun i => (1 : K) ⊗ₜ[k] b (z i))) =
    ∑ z ∈ (Bp.repr (V.tensor ((tprod k) fun i ↦ b (x i)))).support,
    (σ $ Bq.repr v x) • ((Bp.repr (V.tensor $ tprod k fun i => b (x i)) z •
      (tprod K fun i => (1 : K) ⊗ₜ[k] b (z i)))) from Finset.sum_congr rfl fun z _ => by
      rw [smul_comm], ← Finset.smul_sum]
  rw [show ((Bq.repr v) x • (tprod K) fun j ↦ (1 : K) ⊗ₜ[k] b (x j)) =
    tprod K fun j ↦  ((if j = 0 then (Bq.repr v) x else 1) ⊗ₜ[k] b (x j)) by
    rw [show (Bq.repr v) x = ∏ i : Fin q, if i = 0 then (Bq.repr v) x else 1 by simp,
      ← MultilinearMap.map_smul_univ]
    congr 2
    ext j
    split_ifs with h
    · subst h; simp only [smul_tmul', smul_eq_mul, mul_one, Finset.prod_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    · simp only [one_smul]]
  rw [AlgHom.oneTMulPow_apply, map_smul, TensorOfType.extendScalars_apply_tmul]
  simp only [Finset.prod_const_one, LinearEquiv.coe_coe]
  rw [show (∏ i : Fin q, σ (if i = 0 then (Bq.repr v) x else 1)) =
    (∏ i : Fin q, if i = 0 then σ (Bq.repr v x) else 1) from
    Finset.prod_congr rfl fun _ _ => by split_ifs <;> simp]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
  conv_lhs => rw [← eq₁]
  rw [tmul_sum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [tmul_smul, algebra_compatible_smul K, map_smul, algebraMap_smul]
  congr 1
  simp only [Basis.extendScalarsTensorPowerEquiv_apply]

set_option maxHeartbeats 500000 in
lemma oneTMulPow_comm_sq_p_zero
    {V : VectorSpaceWithTensorOfType k 0 q} (b : Basis ι k V) [NeZero q] :
    (V.extendScalars K b).tensor.restrictScalars k ∘ₗ σ.oneTMulPow q b =
    σ.oneTMulPow 0 b ∘ₗ
    (V.extendScalars K b).tensor.restrictScalars k := by
  have eq₁ := AlgHom.oneTMulPow_apply_q_zero (σ := σ) (K := K) (b := b)
  rw [eq₁]
  simp only [extendScalars_carrier, extendScalars_tensor]
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, isEmptyEquiv_symm_apply]
  set B := b.tensorPowerExtendScalars K q with B_eq
  have eq₁ := B.total_repr x |>.symm
  conv_lhs => rw [eq₁]
  dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
    Finsupp.sum]
  simp only [Basis.tensorPowerExtendScalars_apply, map_sum, B]
  simp only [← B_eq, AlgHom.oneTMulPow_apply', LinearMapClass.map_smul]
  rw [show (∑ z ∈ (B.repr x).support,
    σ ((B.repr x) z) • (TensorOfType.extendScalars K b V.tensor)
      ((tprod K) fun i ↦ 1 ⊗ₜ[k] b (z i))) =
    ∑ z ∈ (B.repr x).support,
    σ ((B.repr x) z) • (b.extendScalarsTensorPowerEquiv K 0)
      ((1 : K) ⊗ₜ[k] (V.tensor $ tprod k fun i => b (z i))) from
    Finset.sum_congr rfl fun z _ => by
      rw [TensorOfType.extendScalars_apply_one_tmul (f := V.tensor) (K := K) (b := b)]
      simp]
  simp_rw [Basis.extendScalarsTensorPowerEquiv_zero_apply]
  simp only [isEmptyEquiv_symm_apply, smul_assoc, one_smul]
  change ∑ z ∈ _, _ = _
  rw [show ∑ z ∈ (B.repr x).support,
    σ ((B.repr x) z) • (isEmptyEquiv (Fin 0)) (V.tensor ((tprod k) fun i ↦ b (z i))) • (tprod K) isEmptyElim =
    ∑ z ∈ (B.repr x).support,
    ((isEmptyEquiv (Fin 0)) (V.tensor ((tprod k) fun i ↦ b (z i))) • σ ((B.repr x) z) ) • (tprod K) isEmptyElim from
    Finset.sum_congr rfl fun z _ => by
    simp only [smul_assoc]
    rw [smul_comm]]
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  conv_rhs => rw [eq₁]
  dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
    Finsupp.sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Basis.tensorPowerExtendScalars_apply, B]
  simp only [← B_eq]
  rw [algebra_compatible_smul K, smul_eq_mul, mul_comm]
  congr 1
  rw [TensorOfType.extendScalars_apply_one_tmul]
  simp only [LinearEquiv.coe_coe, EmbeddingLike.apply_eq_iff_eq]
  rw [Basis.extendScalarsTensorPowerEquiv_zero_apply]
  simp only [isEmptyEquiv_symm_apply, smul_assoc, one_smul]
  rw [algebra_compatible_smul K, map_smul]
  simp only [isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one]

lemma oneTMulPow_comm_sq_q_zero
    {V : VectorSpaceWithTensorOfType k p 0} (b : Basis ι k V) [NeZero p] :
    (V.extendScalars K b).tensor.restrictScalars k ∘ₗ σ.oneTMulPow 0 b =
    σ.oneTMulPow p b ∘ₗ
    (V.extendScalars K b).tensor.restrictScalars k := by
  have eq₁ := AlgHom.oneTMulPow_apply_q_zero (σ := σ) (K := K) (b := b)
  rw [eq₁]
  simp only [extendScalars_carrier, extendScalars_tensor]
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Function.comp_apply, AlgHom.toLinearMap_apply, isEmptyEquiv_symm_apply, LinearMapClass.map_smul]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [LinearMapClass.map_smul, isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one]
    have eqx : x = isEmptyElim := List.ofFn_inj.mp rfl
    subst eqx
    unfold TensorOfType.extendScalars TensorOfType.extendScalarsLinearMap
      TensorOfType.extendScalarsLinearMapToFun
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Basis.extendScalarsTensorPowerEquiv_zero_symm_apply',
      LinearMap.extendScalars_apply]
    set X := V.tensor ((tprod k) fun a ↦ isEmptyElim a)
    set B : Basis _ k (⨂[k]^p V.carrier) := piTensorBasis _ _ _ _ (fun _ => b)  with B_eq
    have eq₁ := B.total_repr X |>.symm
    rw [eq₁]
    dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
      Finsupp.sum]
    simp only [piTensorBasis_apply, tmul_sum, tmul_smul, map_sum, Finset.smul_sum, B]
    simp only [← B_eq]
    refine Finset.sum_congr rfl fun z _ => ?_
    conv_lhs => rw [algebra_compatible_smul K (B.repr X z),
      (Basis.extendScalarsTensorPowerEquiv K p b).map_smul, algebraMap_smul, smul_comm]
    conv_rhs => rw [algebra_compatible_smul K (B.repr X z),
      (Basis.extendScalarsTensorPowerEquiv K p b).map_smul, algebraMap_smul,
      smul_comm, (AlgHom.oneTMulPow p b σ).map_smul]
    refine congr_arg ((B.repr X) z • ·) ?_
    simp only [Basis.extendScalarsTensorPowerEquiv_apply, AlgHom.oneTMulPow_apply']
  | add x y hx hy =>
    simp only [map_add, add_smul, hx, hy]

lemma oneTMulPow_comm_sq_p_zero_q_zero
    {V : VectorSpaceWithTensorOfType k 0 0} (b : Basis ι k V) :
    (V.extendScalars K b).tensor.restrictScalars k ∘ₗ σ.oneTMulPow 0 b =
    σ.oneTMulPow 0 b ∘ₗ
    (V.extendScalars K b).tensor.restrictScalars k := by
  have eq₁ := AlgHom.oneTMulPow_apply_q_zero (σ := σ) (K := K) (b := b)
  rw [eq₁]
  simp only [extendScalars_carrier, extendScalars_tensor]
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Function.comp_apply, AlgHom.toLinearMap_apply, isEmptyEquiv_symm_apply, LinearMapClass.map_smul]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    have eqv : v = isEmptyElim := List.ofFn_inj.mp rfl
    subst eqv
    simp only [LinearMapClass.map_smul, isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one,
      _root_.map_mul]
    unfold TensorOfType.extendScalars TensorOfType.extendScalarsLinearMap
      TensorOfType.extendScalarsLinearMapToFun
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Basis.extendScalarsTensorPowerEquiv_zero_symm_apply',
      LinearMap.extendScalars_apply]
    simp only [Basis.extendScalarsTensorPowerEquiv_zero_apply, isEmptyEquiv_symm_apply, smul_assoc,
      one_smul]
    rw [algebra_compatible_smul K ((isEmptyEquiv (Fin 0)) _), ← smul_assoc]
    congr 1
    rw [smul_eq_mul]
    congr 1
    rw [map_smul]
    simp only [isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, add_smul, hx, hy]

lemma oneTMulPow_comm_sq :
    (V.extendScalars K b).tensor.restrictScalars k ∘ₗ σ.oneTMulPow q b =
    σ.oneTMulPow p b ∘ₗ
    (V.extendScalars K b).tensor.restrictScalars k := by
  by_cases hp : p = 0
  · subst hp
    by_cases hq : q = 0
    · subst hq
      apply oneTMulPow_comm_sq_p_zero_q_zero
    · haveI : NeZero q := ⟨hq⟩
      apply oneTMulPow_comm_sq_p_zero
  · haveI : NeZero p := ⟨hp⟩
    by_cases hq : q = 0
    · subst hq
      apply oneTMulPow_comm_sq_q_zero
    · haveI : NeZero q := ⟨hq⟩
      apply oneTMulPow_comm_sq_neZero_neZero

end gal

section twisedForm

variable (p q : ℕ)
variable {k : Type*} (K : Type*) [Field k] [Field K] [Algebra k K]
variable (V W : VectorSpaceWithTensorOfType k p q)

structure twisedForm extends
  VectorSpaceWithTensorOfType k p q,
  (V.extendScalars K (Basis.ofVectorSpace k V)) ≅
  (toVectorSpaceWithTensorOfType.extendScalars K
    (Basis.ofVectorSpace k toVectorSpaceWithTensorOfType))

end twisedForm

end VectorSpaceWithTensorOfType
