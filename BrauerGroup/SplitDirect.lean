import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.FieldTheory.IsSepclosed
import BrauerGroup.BrauerGroup
import BrauerGroup.ExtendScalar
import BrauerGroup.Quaternion

namespace split_direct

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

lemma mem_intermediateTensor_iff_mem_intermediateTensor'
    {L : IntermediateField k K} {x : K ⊗[k] A} :
    x ∈ intermediateTensor k K A L ↔ x ∈ intermediateTensor' k K A L := by
  simp only [intermediateTensor, LinearMap.mem_range, intermediateTensor', LinearMap.coe_mk,
    LinearMap.coe_toAddHom]

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

variable (n : ℕ) [NeZero n] (k K A : Type u) [Field k] [Field K] [Algebra k K]
  [Ring A] [Algebra k A]
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)
  (ℒ : Set (IntermediateField k K))
  (l_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1) ℒ)
  (h : ⨆ (L ∈ ℒ), L = ⊤) (h1 : Nonempty ℒ)

lemma is_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1)
    (Set.range fun (L : ℒ) ↦ intermediateTensor k K A L) := by
  rintro _ ⟨⟨L1, hL1⟩, rfl⟩ _ ⟨⟨L2, hL2⟩, rfl⟩
  obtain ⟨L3, hL3⟩ := l_direct L1 hL1 L2 hL2
  refine ⟨intermediateTensor k K A L3, ⟨⟨L3, hL3.1⟩, rfl⟩,
      ⟨intermediateTensor_mono k K A hL3.2.1, intermediateTensor_mono k K A hL3.2.2⟩⟩

lemma SetOfInterField_nonempty : (Set.range fun (L : IntermediateField k K) ↦
    intermediateTensor k K A L).Nonempty := by
  rw [← Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty]
  simp only [ne_eq, Set.range_eq_empty_iff, not_isEmpty_of_nonempty, not_false_eq_true]

theorem tensor_union_eq :
    ⨆ (L : ℒ), (intermediateTensor k K A L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  |zero => simp only [Submodule.zero_mem]
  |tmul x a =>
    obtain h₀ := IntermediateField.mem_top (F := k) (E := K) (x := x)
    rw [← h] at h₀
    replace h₀ : x ∈ (⨆ (L : ℒ), L.1) := by
      convert h₀
      rw [iSup_subtype]
    change x ∈ ((iSup (fun i : ℒ => i.1) : IntermediateField k K): Set K) at h₀
    rw [IntermediateField.coe_iSup_of_directed (directedOn_iff_directed.1 l_direct)] at h₀
    · simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at h₀
      rcases h₀ with ⟨L, ⟨hL1, hL2⟩⟩
      have h1 : (x ⊗ₜ[k] a) ∈ intermediateTensor k K A L := by
        rw [intermediateTensor]
        simp only [LinearMap.mem_range]
        use (⟨x, hL2⟩ : ↥L) ⊗ₜ[k] a
        simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IntermediateField.val_mk]
      have h2 : (Set.range fun (L : ℒ) ↦ intermediateTensor k K A L).Nonempty := by
        refine Set.nonempty_def.mpr ?_
        tauto
      refine Submodule.mem_sSup_of_directed h2 (is_direct k K A ℒ l_direct) |>.2 ?_
      tauto
  |add x y hx hy =>
    exact AddMemClass.add_mem hx hy

theorem extension_element_in (x : K ⊗[k] A):
    ∃ (F : ℒ), x ∈ intermediateTensor k K A F := by
  have mem : x ∈ (⊤ : Submodule k _) := ⟨⟩
  rw [← tensor_union_eq k K A ℒ l_direct h h1] at mem
  rw [Set.nonempty_iff_ne_empty', Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty] at h1
  have h2 : (Set.range fun (L : ℒ) ↦ intermediateTensor k K A L).Nonempty := by
    refine Set.nonempty_def.mpr ?_
    use intermediateTensor k K A h1.choose
    simp only [Set.mem_range, Subtype.exists, exists_prop]
    use h1.choose
    simp only [and_true]
    exact h1.choose_spec
  obtain ⟨_, ⟨⟨⟨L, hL1⟩, rfl⟩, hL⟩⟩ := Submodule.mem_sSup_of_directed h2
    (is_direct k K A ℒ l_direct) (z := x) |>.1 mem
  simp only [Subtype.exists, exists_prop]
  tauto

def subfieldOf (x : K ⊗[k] A) : IntermediateField k K :=
  extension_element_in k K A ℒ l_direct h h1 x|>.choose

lemma subfieldOf_in (x : K ⊗[k] A) : (subfieldOf k K A ℒ l_direct h h1 x) ∈ ℒ := by
  rw [subfieldOf]
  simp only [Subtype.coe_prop]

theorem mem_subfieldOf (x : K ⊗[k] A) : x ∈ intermediateTensor k K A
    (subfieldOf k K A ℒ l_direct h h1 x) := (extension_element_in k K A ℒ l_direct h h1 x).choose_spec

theorem mem_subfieldOf' (x : K ⊗[k] A) : x ∈ intermediateTensor' k K A
    (subfieldOf k K A ℒ l_direct h h1 x) := by
  rw [← mem_intermediateTensor_iff_mem_intermediateTensor']
  exact mem_subfieldOf k K A ℒ l_direct h h1 x

def ee : Basis (Fin n × Fin n) K (K ⊗[k] A) :=
  Basis.map (Matrix.stdBasis K _ _) iso.symm

local notation "e" => ee n k K A iso

@[simp]
lemma ee_apply (i : Fin n × Fin n) : iso (e i) = Matrix.stdBasis K (Fin n) (Fin n) i := by
  apply_fun iso.symm
  simp only [AlgEquiv.symm_apply_apply]
  have := Basis.map_apply (Matrix.stdBasis K (Fin n) (Fin n)) iso.symm.toLinearEquiv i
  erw [← this]

lemma L_sup :
    ∃ L, L ∈ ℒ ∧ (∀ (i : Fin n × Fin n), subfieldOf k K A ℒ l_direct h h1 (e i) ≤ L) := by
  use ⨆ (i : Fin n × Fin n), subfieldOf k K A ℒ l_direct h h1 (e i)
  constructor
  · suffices ∀ i, subfieldOf k K A ℒ l_direct h h1 (e i) ∈ ℒ by
      sorry
    intro i
    exact subfieldOf_in k K A ℒ l_direct h h1 (e i)
  · let f := fun i => subfieldOf k K A ℒ l_direct h h1 (e i)
    exact le_iSup f

def ℒℒ : IntermediateField k K := (L_sup n k K A iso ℒ l_direct h h1).choose

local notation "ℒ₁" => ℒℒ n k K A iso ℒ l_direct h h1

def f (i : Fin n × Fin n) : subfieldOf k K A ℒ l_direct h h1 (e i) →ₐ[k] ℒ₁ :=
  subfieldOf k K A ℒ l_direct h h1 (e i)|>.inclusion
  (by exact (L_sup n k K A iso ℒ l_direct h h1).choose_spec.2 i)

def e_hat' (i : Fin n × Fin n) : intermediateTensor' k K A ℒ₁ :=
  ⟨e i, by
    rw [← mem_intermediateTensor_iff_mem_intermediateTensor', ℒℒ]
    exact intermediateTensor_mono k K A ((L_sup n k K A iso ℒ l_direct h h1).choose_spec.2 i)
      $ mem_subfieldOf k K A ℒ l_direct h h1 (e i)⟩

local notation "e^'" => e_hat' n k K A iso ℒ l_direct h h1

theorem e_hat_linear_independent : LinearIndependent ℒ₁ e^' := by
  rw [linearIndependent_iff']
  intro s g h
  have h' : ∑ i ∈ s, algebraMap ℒ₁ K (g i) • e i = 0 := by
    apply_fun Submodule.subtype _ at h
    simpa only [IntermediateField.algebraMap_apply, map_sum, map_smul, Submodule.coeSubtype,
      map_zero] using h

  have H := (linearIndependent_iff'.1 $ e |>.linearIndependent) s (algebraMap ℒ₁ K ∘ g) h'
  intro i hi
  simpa using H i hi

-- shortcut instance search
set_option synthInstance.maxHeartbeats 40000 in
instance : Module ℒ₁ (ℒ₁ ⊗[k] A) := TensorProduct.leftModule

theorem dim_ℒ_eq : FiniteDimensional.finrank ℒ₁ (intermediateTensor' k K A ℒ₁) = n^2 := by
    -- have eq1 := dim_eq k K A |>.trans iso.toLinearEquiv.finrank_eq
    -- simp only [FiniteDimensional.finrank_matrix, Fintype.card_fin] at eq1
    -- rw [pow_two, ← eq1, dim_eq k ℒ A]
    -- exact LinearEquiv.finrank_eq (intermediateTensorEquiv' k k_bar A ℒ)
    sorry

def e_hat : Basis (Fin n × Fin n) ℒ₁ (intermediateTensor' k K A ℒ₁) :=
  basisOfLinearIndependentOfCardEqFinrank (e_hat_linear_independent n k K A iso ℒ l_direct h h1) $ by
    simp only [Fintype.card_prod, Fintype.card_fin, dim_ℒ_eq, pow_two]


local notation "e^" => e_hat n k K A iso ℒ l_direct h h1

def isoRestrict0 : ℒ₁ ⊗[k] A ≃ₗ[ℒ₁] Matrix (Fin n) (Fin n) ℒ₁ :=
  (intermediateTensorEquiv' k K A ℒ₁).symm ≪≫ₗ
  Basis.equiv (e^) (Matrix.stdBasis ℒ₁ (Fin n) (Fin n)) (Equiv.refl _)

set_option synthInstance.maxHeartbeats 50000 in
instance : SMulCommClass k ℒ₁ ℒ₁ := inferInstance
-- instance : Algebra ℒ (ℒ ⊗[k] A) := Algebra.TensorProduct.leftAlgebra

def inclusion : ℒ₁ ⊗[k] A →ₐ[ℒ₁] K ⊗[k] A :=
  Algebra.TensorProduct.map (Algebra.ofId ℒ₁ K) (AlgHom.id k A)

def inclusion' : Matrix (Fin n) (Fin n) ℒ₁ →ₐ[ℒ₁] Matrix (Fin n) (Fin n) K :=
  AlgHom.mapMatrix (Algebra.ofId ℒ₁ _)

lemma inclusion'_injective : Function.Injective (inclusion' n k K A iso ℒ l_direct h h1) := by
  intro x y h
  ext i j
  rw [← Matrix.ext_iff] at h
  specialize h i j
  simp only [inclusion', Algebra.ofId, AlgHom.mapMatrix_apply, AlgHom.coe_mk, Matrix.map_apply,
    IntermediateField.algebraMap_apply, SetLike.coe_eq_coe] at h
  rw [h]

/--
ℒ₁ ⊗_k A ------>  intermidateTensor
  |              /
  | inclusion  /
  v          /
K ⊗_k A  <-
-/
lemma comm_triangle :
    (intermediateTensor' k K A ℒ₁).subtype ∘ₗ
    (intermediateTensorEquiv' k K A ℒ₁).symm.toLinearMap =
    (inclusion n k K A iso ℒ l_direct h h1).toLinearMap := by
  ext a
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, Submodule.coeSubtype, LinearEquiv.coe_coe, Function.comp_apply, inclusion,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.coe_id, id_eq]
  simp only [intermediateTensorEquiv', intermediateTensorEquiv, LinearEquiv.symm_symm,
    LinearEquiv.coe_symm_mk]
  rfl

/--
intermidateTensor ----> M_n(ℒ)
  | val                 | inclusion'
  v                     v
k⁻ ⊗_k A ----------> M_n(k⁻)
          iso
-/
lemma comm_square' :
    iso.toLinearEquiv.toLinearMap.restrictScalars ℒ₁ ∘ₗ
    (intermediateTensor' k K A ℒ₁).subtype =
    (inclusion' n k K A iso ℒ l_direct h h1).toLinearMap ∘ₗ
    Basis.equiv (e^) (Matrix.stdBasis ℒ₁ (Fin n) (Fin n)) (Equiv.refl _) := by
  apply Basis.ext (e^)
  intro i
  conv_lhs => simp only [AlgEquiv.toLinearEquiv_toLinearMap, e_hat,
    basisOfLinearIndependentOfCardEqFinrank,
    Basis.coe_mk, e_hat', LinearMap.coe_comp, LinearMap.coe_restrictScalars, Submodule.coeSubtype,
    Function.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  simp only [ee_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
  ext a b
  simp only [inclusion', AlgHom.mapMatrix_apply, Matrix.map_apply]
  simp only [Algebra.ofId, AlgHom.coe_mk, IntermediateField.algebraMap_apply]
  rw [Matrix.stdBasis_eq_stdBasisMatrix]
  erw [Matrix.stdBasis_eq_stdBasisMatrix]
  simp only [Matrix.stdBasisMatrix]
  aesop

/--
     isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso
-/
lemma comm_square :
    (inclusion' n k K A iso ℒ l_direct h h1).toLinearMap ∘ₗ
    (isoRestrict0 n k K A iso ℒ l_direct h h1).toLinearMap  =
    iso.toLinearEquiv.toLinearMap.restrictScalars ℒ₁ ∘ₗ
    (inclusion n k K A iso ℒ l_direct h h1).toLinearMap := by
  rw [← comm_triangle n k K A iso ℒ l_direct h h1, ← LinearMap.comp_assoc,
    comm_square' n k K A iso ℒ l_direct h h1]
  rfl

lemma isoRestrict_map_one : isoRestrict0 n k K A iso ℒ l_direct h h1 1 = 1 := by
  /-
        isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso

  Want to show isoRestrict 1 = 1
  inclusion' ∘ isoRestrict = iso ∘ inclusion
  inclusion' (isoRestrict 1) = iso (inclusion 1) = 1 = inclusion' 1
  since inclusion' is injective, isoRestrict 1 = 1
  -/
  have eq := congr($(comm_square n k K A iso ℒ l_direct h h1) 1)
  conv_rhs at eq =>
    rw [LinearMap.comp_apply]
    erw [(inclusion n k K A iso ℒ l_direct h h1).map_one, map_one iso]
  refine inclusion'_injective n k K A iso ℒ l_direct h h1 (eq.trans ?_)
  rw [_root_.map_one]

lemma isoRestrict_map_mul (x y : ℒ₁ ⊗[k] A) :
    isoRestrict0 n k K A iso ℒ l_direct h h1 (x * y) =
    isoRestrict0 n k K A iso ℒ l_direct h h1 x * isoRestrict0 n k K A iso ℒ l_direct h h1 y := by
  /-
        isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso

  Want to show isoRestrict (x * y) = isoRestrict x * isoRestrict y
  inclusion' ∘ isoRestrict = iso ∘ inclusion
  inclusion' (isoRestrict (x * y)) = iso (inclusion (x * y)) = iso (inclusion x) * iso (inclusion y)
    = inclusion' (isoRestrict x) * inclusion' (isoRestrict y)
    = inclusion' (isoRestrict x * isoRestrict y)
  since inclusion' is injective, isoRestrict (x * y) = isoRestrict x * isoRestrict y

  -/
  have eq := congr($(comm_square n k K A iso ℒ l_direct h h1) (x * y))
  conv_rhs at eq =>
    rw [LinearMap.comp_apply]
    erw [(inclusion n k K A iso ℒ l_direct h h1).map_mul, _root_.map_mul (f := iso)]
  have eq₁ := congr($(comm_square n k K A iso ℒ l_direct h h1) x)
  have eq₂ := congr($(comm_square n k K A iso ℒ l_direct h h1) y)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.coe_restrictScalars,
    AlgEquiv.toLinearMap_apply] at eq₁ eq₂
  rw [← eq₁, ← eq₂, ← _root_.map_mul] at eq
  refine inclusion'_injective n k K A iso ℒ l_direct h h1 (eq.trans ?_)
  rw [_root_.map_mul]


def isoRestrict' : ℒ₁ ⊗[k] A ≃ₐ[ℒ₁] Matrix (Fin n) (Fin n) ℒ₁ :=
  AlgEquiv.ofLinearEquiv (isoRestrict0 n k K A iso ℒ l_direct h h1)
    (isoRestrict_map_one n k K A iso ℒ l_direct h h1) (isoRestrict_map_mul n k K A iso ℒ l_direct h h1)

variable [Ring A] [Algebra k A] [Algebra k K]

structure split (A : CSA k) (K : Type*) [Field K] [Algebra k K] :=
  (n : ℕ) (hn : n ≠ 0)
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

def isSplit (L : Type u) [Field L] [Algebra k L] : Prop :=
  ∃(n : ℕ)(_ : n ≠ 0),
  Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

lemma spilt_iff_left (A : CSA k) (𝓁 : Set (IntermediateField k K))
    (l_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1) 𝓁)
    (h : ⨆ (L ∈ 𝓁), L = ⊤) (h₀ : Nonempty 𝓁) :
    isSplit k A K → (∃ L ∈ 𝓁, isSplit k A L) := by
  rintro ⟨n, ⟨hn, hnL⟩⟩
  obtain hnL' := hnL.some; clear hnL
  use (L_sup n k K A hnL' 𝓁 l_direct h h₀).choose
  constructor
  · exact (L_sup n k K A hnL' 𝓁 l_direct h h₀).choose_spec.1
  · use n; use hn
    rw [← neZero_iff] at hn
    obtain h1 := isoRestrict' n k K A hnL' 𝓁
    simp [ℒℒ] at h1
    tauto

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 800000 in
lemma spilt_iff_right (A : CSA k) (𝓁 : Set (IntermediateField k K)):
    (∃ L ∈ 𝓁, isSplit k A L) → isSplit k A K := fun ⟨L, ⟨_, ⟨n, ⟨hn, hnL⟩⟩⟩⟩ ↦
    ⟨n ,⟨hn, ⟨absorb_eqv k L K A|>.trans $ eqv_eqv _ _ _ _ hnL.some|>.trans $
      eqv_eqv _ _ _ _ (Matrix_eqv_eqv k L n).symm|>.trans $
      absorb_eqv k L K (Matrix (Fin n) (Fin n) k)|>.symm.trans $ Matrix_eqv_eqv k K n⟩⟩⟩

theorem spilt_iff (A : CSA k) (𝓁 : Set (IntermediateField k K))
    (l_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1) 𝓁)
    (h : ⨆ (L ∈ 𝓁), L = ⊤) (h₀ : Nonempty 𝓁) :
    isSplit k A K ↔ (∃ L ∈ 𝓁, isSplit k A L) := by
  exact ⟨spilt_iff_left _ _ _ _ l_direct h h₀, spilt_iff_right _ _ _ _⟩

end

end split_direct
