import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.FieldTheory.IsSepclosed
import BrauerGroup.BrauerGroup
import BrauerGroup.ExtendScalar

suppress_compilation

open TensorProduct

universe u

section
variable (k K: Type u) [Field k] [Field K] [Algebra k K]

variable (A : Type u) [AddCommGroup A] [Module k A]

instance module_over_over (A : CSA k) (I : RingCon A):
    Module k I := Module.compHom I (algebraMap k A)

open scoped IntermediateField

/- midfield L ⊗ A is a k-submodule of K ⊗ A -/
def intermediateTensor (L : IntermediateField k K) : Submodule k (K ⊗[k] A) :=
  LinearMap.range (LinearMap.rTensor _ (L.val.toLinearMap) : L ⊗[k] A →ₗ[k] K ⊗[k] A)

/- midfield L ⊗ A is a L-submodule of K ⊗ A -/
set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 400000 in
def intermediateTensor' (L : IntermediateField k K) : Submodule L (K ⊗[k] A) :=
  LinearMap.range ({LinearMap.rTensor _ (L.val.toLinearMap) with
    map_smul' := fun l x => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x a =>
        simp only [smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          _root_.map_mul, IntermediateField.coe_val]
        rfl
      | add x y hx hy => aesop } : L ⊗[k] A →ₗ[L] K ⊗[k] A)

/- Submodule k (K ⊗[k] A) ≃ₗ[k] L ⊗[k] A -/
def intermediateTensorEquiv (L : IntermediateField k K) :
    intermediateTensor k K A L ≃ₗ[k] L ⊗[k] A :=
  LinearEquiv.symm $ LinearEquiv.ofBijective
    (LinearMap.rangeRestrict _)
    ⟨by
      intro x y hxy
      simp only [LinearMap.rangeRestrict, Subtype.ext_iff, LinearMap.codRestrict_apply] at hxy
      refine Module.Flat.rTensor_preserves_injective_linearMap _
        (fun x y h => by simpa using h) hxy, LinearMap.surjective_rangeRestrict _⟩

@[simp]
lemma intermediateTensorEquiv_apply_tmul (L : IntermediateField k K)
      (x : L) (a : A) (h : x.1 ⊗ₜ[k] a ∈ intermediateTensor k K A L) :
    intermediateTensorEquiv k K A L ⟨_, h⟩ =
    x ⊗ₜ a := by
  simp only [intermediateTensorEquiv]
  convert LinearEquiv.ofBijective_symm_apply_apply _ _
  rfl

set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 400000 in
def intermediateTensorEquiv' (L : IntermediateField k K) :
    intermediateTensor' k K A L ≃ₗ[L] L ⊗[k] A where
  toFun := intermediateTensorEquiv k K A L
  map_add' := map_add _
  map_smul' := by
    rintro x ⟨-, ⟨y, rfl⟩⟩
    simp only [RingHom.id_apply]
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, SetLike.mk_smul_mk, smul_zero]
      erw [map_zero]
      rw [smul_zero]
    | tmul y a =>
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, IntermediateField.coe_val, SetLike.mk_smul_mk, smul_tmul',
        intermediateTensorEquiv_apply_tmul, smul_eq_mul]
      exact intermediateTensorEquiv_apply_tmul k K A L (x • y) a _
    | add y z hy hz =>
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, SetLike.mk_smul_mk, map_add,
        smul_add] at hy hz ⊢
      convert congr($hy + $hz) using 1
      · rw [← (intermediateTensorEquiv k K A L).map_add]; rfl
      · rw [← smul_add, ← (intermediateTensorEquiv k K A L).map_add]; rfl
  invFun := (intermediateTensorEquiv k K A L).symm
  left_inv := (intermediateTensorEquiv k K A L).left_inv
  right_inv := (intermediateTensorEquiv k K A L).right_inv

/- midfield leq then tensor leq -/
lemma intermediateTensor_mono {L1 L2 : IntermediateField k K} (h : L1 ≤ L2) :
    intermediateTensor k K A L1 ≤ intermediateTensor k K A L2 := by
  have e1 : (LinearMap.rTensor _ (L1.val.toLinearMap) : L1 ⊗[k] A →ₗ[k] K ⊗[k] A) =
    (LinearMap.rTensor _ (L2.val.toLinearMap) : L2 ⊗[k] A →ₗ[k] K ⊗[k] A) ∘ₗ
    (LinearMap.rTensor A (L1.inclusion h) : L1 ⊗[k] A →ₗ[k] L2 ⊗[k] A) := by
    rw [← LinearMap.rTensor_comp]; rfl
  delta intermediateTensor
  rw [e1, LinearMap.range_comp, Submodule.map_le_iff_le_comap]
  rintro _ ⟨x, rfl⟩
  simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    Submodule.mem_comap, LinearMap.mem_range, exists_apply_eq_apply]

private abbrev SetOfFinite : Set (IntermediateField k K) :=
  {M | FiniteDimensional k M}

lemma is_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1)
    (Set.range fun (L : SetOfFinite k K) ↦ intermediateTensor k K A L) := by
  rintro _ ⟨⟨L1, (hL1 : FiniteDimensional _ _)⟩, rfl⟩ _ ⟨⟨L2, (hL2 : FiniteDimensional _ _)⟩, rfl⟩
  refine ⟨intermediateTensor k K A (L1 ⊔ L2), ⟨⟨L1 ⊔ L2, show FiniteDimensional _ _ from
    ?_⟩, rfl⟩, ⟨intermediateTensor_mono k K A le_sup_left,
      intermediateTensor_mono k K A le_sup_right⟩⟩
  · apply (config := { allowSynthFailures := true }) IntermediateField.finiteDimensional_sup <;>
    assumption

lemma SetOfFinite_nonempty : (Set.range fun (L : SetOfFinite k K) ↦
    intermediateTensor k K A L).Nonempty := by
  refine ⟨intermediateTensor k K A ⊥, ⟨⟨⊥, ?_⟩, rfl⟩⟩
  simp only [SetOfFinite, Set.mem_setOf_eq, IntermediateField.bot_toSubalgebra]
  infer_instance

variable (k K L A B: Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
  [Algebra k L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [IsScalarTower k K L]

def releaseAddHom' (h : A ≃ₐ[K] B) : L ⊗[K] A →+ L ⊗[K] B :=
  TensorProduct.liftAddHom
  {
    toFun := fun l ↦
    {
      toFun := fun a ↦ l ⊗ₜ[K] h a
      map_zero' := by simp only [map_zero, tmul_zero]
      map_add' := by intro x y; simp only [map_add, TensorProduct.tmul_add]
    }
    map_zero' := by ext ; simp only [zero_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.zero_apply]
    map_add' := by
      intro x y; ext
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply,
        TensorProduct.add_tmul]
  }
  (fun r l a ↦ by
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.tmul_smul]
    rw [TensorProduct.smul_tmul]
    simp)

set_option synthInstance.maxHeartbeats 40000 in
def release' (h : A ≃ₐ[K] B) : L ⊗[K] A →ₐ[L] L ⊗[K] B where
  __ := releaseAddHom' K L A B h
  map_one' := by
    simp only [releaseAddHom', Algebra.TensorProduct.one_def, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, _root_.map_one]
  map_mul' := fun x y ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, ZeroHom.toFun_eq_coe, map_zero, AddMonoidHom.toZeroHom_coe]
    | tmul l a =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, ZeroHom.toFun_eq_coe, map_zero, AddMonoidHom.toZeroHom_coe]
      | tmul l a => simp [releaseAddHom']
      | add x y hx hy =>
        simp only [mul_add, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
        simp_all only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    | add z w hz hw =>
      simp only [add_mul, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
      simp_all only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
  commutes' := fun l ↦ by
    simp only [releaseAddHom', Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id,
      RingHom.id_apply, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, liftAddHom_tmul,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, _root_.map_one]

def absorbAddHom' (h : A ≃ₐ[K] B) : L ⊗[K] B →+ L ⊗[K] A :=
  TensorProduct.liftAddHom
  {
    toFun := fun l ↦
    {
      toFun := fun a ↦ l ⊗ₜ[K] h.symm a
      map_zero' := by simp only [map_zero, tmul_zero]
      map_add' := fun _ _ ↦ by simp only [map_add, tmul_add]
    }
    map_zero' := by simp only [zero_tmul]; rfl
    map_add' := fun x y ↦ by simp only [add_tmul]; rfl
  }
  fun r l a ↦ by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMapClass.map_smul,
    tmul_smul, smul_tmul']

def absorb' (h : A ≃ₐ[K] B) : L ⊗[K] B →ₐ[L] L ⊗[K] A where
  __ := absorbAddHom' K L A B h
  map_one' := by simp only [absorbAddHom', Algebra.TensorProduct.one_def, ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    _root_.map_one]
  map_mul' := fun x y ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, ZeroHom.toFun_eq_coe, map_zero, AddMonoidHom.toZeroHom_coe]
    | tmul l a =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, ZeroHom.toFun_eq_coe, map_zero, AddMonoidHom.toZeroHom_coe]
      | tmul l a => simp [absorbAddHom']
      | add x y hx hy =>
        simp only [mul_add, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
        simp_all only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    | add z w hz hw =>
      simp only [add_mul, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add]
      simp_all only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
  commutes' := fun l ↦ by simp [absorbAddHom']

def eqv_eqv (h : A ≃ₐ[K] B) : L ⊗[K] A ≃ₐ[L] L ⊗[K] B where
  toFun := release' K L A B h
  invFun := absorb' K L A B h
  left_inv := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul l a =>
      change (l ⊗ₜ[K] h.symm (h a)) = _
      congr; exact h.symm_apply_apply a
    | add x y hx hy => simp only [map_add, hx, hy]
  right_inv := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul l a =>
      change (l ⊗ₜ[K] h (h.symm a)) = _
      congr; exact h.apply_symm_apply a
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' := release' _ _ _ _ _|>.map_mul
  map_add' := release' _ _ _ _ _|>.map_add
  commutes' := release' _ _ _ _ _|>.commutes

def Matrix_eqv_eqv (n : ℕ) : L ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[L] Matrix (Fin n) (Fin n) L where
  toFun := matrixEquivTensor k L (Fin n)|>.symm
  invFun := matrixEquivTensor k L (Fin n)
  left_inv := (matrixEquivTensor k L (Fin n)).apply_symm_apply
  right_inv := (matrixEquivTensor k L (Fin n)).symm_apply_apply
  map_mul' := _root_.map_mul (matrixEquivTensor _ _ _).symm
  map_add' := _root_.map_add (matrixEquivTensor _ _ _).symm
  commutes' _ := by
    ext i j
    if hij : i = j then simp [hij, Matrix.algebraMap_matrix_apply]
    else simp [hij, Matrix.algebraMap_matrix_apply]

variable [Ring A] [Algebra k A] [Algebra k K]

structure split (A : CSA k) (K : Type*) [Field K] [Algebra k K] :=
  (n : ℕ) (hn : n ≠ 0)
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

def isSplit (L : Type u) [Field L] [Algebra k L] : Prop :=
  ∃(n : ℕ)(_ : n ≠ 0),
  Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

lemma spilt_iff_left (A : CSA k) (ℒ : Set (IntermediateField k K))
    (l_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1) ℒ)
    (h : ⨆ (L ∈ ℒ), (intermediateTensor k K A L) = K) :
    isSplit k A K → (∃ L ∈ ℒ, isSplit k A L) := by
  sorry

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 800000 in
lemma spilt_iff_right (A : CSA k) (ℒ : Set (IntermediateField k K)):
    (∃ L ∈ ℒ, isSplit k A L) → isSplit k A K := fun ⟨L, ⟨_, ⟨n, ⟨hn, hnL⟩⟩⟩⟩ ↦
    ⟨n ,⟨hn, ⟨absorb_eqv k L K A|>.trans $ eqv_eqv _ _ _ _ hnL.some|>.trans $
      eqv_eqv _ _ _ _ (Matrix_eqv_eqv k L n).symm|>.trans $
      absorb_eqv k L K (Matrix (Fin n) (Fin n) k)|>.symm.trans $ Matrix_eqv_eqv k K n⟩⟩⟩

theorem spilt_iff (A : CSA k) (ℒ : Set (IntermediateField k K))
    (l_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1) ℒ)
    (h : ⨆ (L ∈ ℒ), (intermediateTensor k K A L) = K) :
    isSplit k A K ↔ (∃ L ∈ ℒ, isSplit k A L) := by
  exact ⟨spilt_iff_left _ _ _ _ l_direct h, spilt_iff_right _ _ _ _⟩
