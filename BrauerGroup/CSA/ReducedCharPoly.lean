import Mathlib
import BrauerGroup.BrauerGroup
import BrauerGroup.DoubleCentralizer
import BrauerGroup.SplittingOfCSA

universe u v w

open scoped TensorProduct

variable (K F E K_bar F_bar: Type u) [Field K] [Field F] [Field E] [Field F_bar] [Algebra K F]
  [Algebra K E] [Field K_bar] [Algebra K K_bar] [Algebra F F_bar] [hK_bar : IsAlgClosure K K_bar]
  [hF_bar : IsAlgClosure F F_bar] (A : CSA.{u, u} K)
  (n m : ℕ) [NeZero n] (e : F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F)

suppress_compilation

-- instance (R R' A B C : Type) [CommSemiring R]
--     [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
--     [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
--     [IsScalarTower R R' A] [IsScalarTower R R' B]
--     : NonUnitalSemiring ((A ⊗[R'] B) ⊗[R] C) := inferInstance


set_option maxSynthPendingDepth 2 in
def Algebra.TensorProduct.assoc' (R S R' A B C : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
    [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
    [IsScalarTower R R' A] [IsScalarTower R R' B] [Algebra S A] [Algebra R S] [Algebra R' S]
    [IsScalarTower R' S A] [IsScalarTower R S A]:
    (A ⊗[R'] B) ⊗[R] C ≃ₐ[S] A ⊗[R'] B ⊗[R] C :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.assoc _ _ _ _ _ _)
    rfl (LinearMap.map_mul_iff _|>.2 <| by ext; simp)

@[simp]
lemma Algebra.TensorProduct.assoc'_apply (R S R' A B C : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
    [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
    [IsScalarTower R R' A] [IsScalarTower R R' B] [Algebra S A] [Algebra R S] [Algebra R' S]
    [IsScalarTower R' S A] [IsScalarTower R S A] (a : A) (b : B) (c : C):
    (Algebra.TensorProduct.assoc' R S R' A B C) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl
  -- [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : AddCommMonoid M] [inst_6 : Module R M] [inst_7 : Module A M]
  -- [inst_8 : Module B M] [inst_9 : IsScalarTower R A M] [inst_10 : IsScalarTower R B M] [inst_11 : SMulCommClass A B M]
  -- [inst_12 : AddCommMonoid P] [inst_13 : Module A P] [inst_14 : AddCommMonoid Q] [inst_15 : Module R Q]
  -- [inst_16 : Module R P] [inst_17 : IsScalarTower R A P] [inst_18 : Algebra A B] [inst_19 : IsScalarTower A B M] :
  -- (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] P ⊗[R] Q := sorry

-- instance [Algebra F E] [IsScalarTower K F E]: IsScalarTower K (Algebra.ofId F E).range E where
--   smul_assoc k := fun ⟨f, hf⟩ x ↦ by
--     change (k • f) • _ = k • f • x
--     exact smul_assoc _ _ _

-- instance [Algebra F E] : Algebra (Algebra.ofId F E).range F :=
--   RingHom.toAlgebra (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm

-- instance [Algebra F E] [IsScalarTower K F E]: IsScalarTower K (Algebra.ofId F E).range F where
--   smul_assoc k := fun ⟨e, he⟩ x ↦ by
--     simp only [RingHom.smul_toAlgebra, RingHom.coe_coe]
--     change (AlgEquiv.restrictScalars K (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm) _ * _ = _
--     rw [map_smul]
--     simp

def matrixEquivTensor'.{u_1, u_2, u_3} (n : Type u_1) (R : Type u_2) (A : Type u_3) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Fintype n] [DecidableEq n] :
    Matrix n n A ≃ₐ[A] A ⊗[R] Matrix n n R :=
  (AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R A).symm) <| fun a ↦ by
    ext i j
    simp [matrixEquivTensor, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.one_apply] ).symm

@[simp] lemma matrixEquivTensor'_symm_apply.{u_1, u_2, u_3} (n : Type u_1) (R : Type u_2) (A : Type u_3) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Fintype n] [DecidableEq n] (a : A) (m : Matrix n n R):
    (matrixEquivTensor' n R A).symm (a ⊗ₜ m) = a • (m.map (algebraMap R A)) := rfl

section defs

lemma injective_φ (φ : F →ₐ[K] E) : Function.Injective φ := RingHom.injective _

variable {K F E } in
@[simps]
def φ_m (φ : F →ₐ[K] E) : Matrix (Fin n) (Fin n) F →ₐ[K] Matrix (Fin n) (Fin n) E where
  toFun := fun M ↦ (fun i j ↦ φ (M i j))
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_mul' M1 M2 := by ext i j; simp [Matrix.mul_apply]
  map_zero' := by ext; simp
  map_add' M1 M2 := by ext; simp
  commutes' k := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply]
    split_ifs with h <;>  simp

omit [NeZero n] in
lemma φ_m_inj (φ : F →ₐ[K] E): Function.Injective (φ_m n φ) := fun M N h ↦ funext fun i ↦
  funext fun j ↦ by simp [← Matrix.ext_iff] at h; exact (injective_φ _ _ _ φ) (h i j)

abbrev e1 (φ : F →ₐ[K] E) : Matrix (Fin n) (Fin n) F ≃ₐ[K] Matrix (Fin n) (Fin n) φ.range :=
  AlgEquiv.ofInjective φ (injective_φ K F E _)|>.mapMatrix

abbrev e1' (φ : F →ₐ[K] E) : φ.range ⊗[K] A ≃ₐ[K] Matrix (Fin n) (Fin n) φ.range :=
  Algebra.TensorProduct.congr (AlgEquiv.ofInjective _ (injective_φ _ _ _ _)).symm AlgEquiv.refl|>.trans <|
  ({__ := e, commutes' r := by simpa using (e.commutes (algebraMap K F r))} : _ ≃ₐ[K] Matrix (Fin n) (Fin n) F).trans
  <| e1 _ _ _ _ φ



#exit
variable {F E} in
abbrev e1 : (Algebra.ofId F E).range ≃ₐ[F] F := (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm

abbrev e1' : (Algebra.ofId F E).range ≃ₐ[(Algebra.ofId F E).range] F :=
  AlgEquiv.ofRingEquiv (f := e1 (F := F) (E := E)) (fun ⟨x, hx⟩ ↦ by
    simp [e1, AlgEquiv.ofInjectiveField, Algebra.algebraMap_eq_smul_one, RingHom.smul_toAlgebra]
    rfl)

variable [IsScalarTower K F E]

abbrev e' : F ⊗[K] A ≃ₐ[(Algebra.ofId F E).range] Matrix (Fin n) (Fin n) F :=
  AlgEquiv.ofRingEquiv (f := e) <| fun ⟨x, hx⟩ ↦ by
    simp [Algebra.TensorProduct.one_def]
    simp [Algebra.algebraMap_eq_smul_one, RingHom.smul_toAlgebra]
    conv_lhs => erw [← mul_one ((AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm ⟨x, hx⟩),
      ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_one]
    rfl

abbrev e2 : E ≃ₐ[E] E ⊗[(Algebra.ofId F E).range] (Algebra.ofId F E).range :=
  Algebra.TensorProduct.rid (Algebra.ofId F E).range E E|>.symm

abbrev e3 : (Algebra.ofId F E).range ⊗[K] A ≃ₐ[(Algebra.ofId F E).range]
    Matrix (Fin n) (Fin n) (Algebra.ofId F E).range :=
  Algebra.TensorProduct.congr (e1' F E) AlgEquiv.refl |>.trans <|
  (e' K F E A n e).trans (e1' F E).mapMatrix.symm

set_option maxSynthPendingDepth 2 in
variable {K F E A n} in
abbrev g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E :=
  Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (Algebra.ofId F E).range E E|>.symm)
    AlgEquiv.refl |>.trans <|
  (Algebra.TensorProduct.assoc' K E (Algebra.ofId F E).range
    E (Algebra.ofId F E).range A).trans <|
  Algebra.TensorProduct.congr AlgEquiv.refl (e3 K F E A n e) |>.trans <|
  (matrixEquivTensor' _ _ _).symm

end defs

omit [NeZero n] in
lemma mat_over_extension [Algebra F E] [IsScalarTower K F E] (φ : F →ₐ[F] E) (a : A):
    ∃ g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E, g (1 ⊗ₜ a) =
    φ.mapMatrix (e (1 ⊗ₜ a)) := by
  use g e
  simp
  -- rw [Algebra.TensorProduct.one_def]
  sorry
  -- use g e
  -- simp only [Algebra.range_ofId, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
  --   AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_coe, map_one, AlgHom.coe_id,
  --   id_eq, AlgHom.mapMatrix_apply]
  -- rw [Algebra.TensorProduct.one_def]
  -- erw [Algebra.TensorProduct.assoc'_apply]
  -- simp only [Algebra.range_ofId, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
  --   AlgHom.coe_coe, matrixEquivTensor'_symm_apply, one_smul]
  -- ext i j
  -- simp only [Matrix.map_apply]
  -- unfold e3
  -- simp only [Algebra.range_ofId, AlgEquiv.mapMatrix_symm, AlgEquiv.trans_apply,
  --   Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul,
  --   AlgHom.coe_coe, map_one, AlgHom.coe_id, id_eq, AlgEquiv.mapMatrix_apply, Matrix.map_apply]
  -- change algebraMap _ _ (e1.symm (e (_) i j)) = _
  -- change algebraMap _ _ ((AlgEquiv.ofInjective _ (FaithfulSMul.algebraMap_injective F E )) (e _ i j)) = _
  -- change algebraMap _ _ ((algebraMap F E) (e _ i j)) = _
  -- conv_lhs => rw [← RingHom.comp_apply]
  -- change ((RingHom.id _).comp _) _ = _
  -- simp [Algebra.ofId]

variable {K F n} in
def ReducedCharPoly (a : A): Polynomial F := Matrix.charpoly (e (1 ⊗ₜ a))

namespace ReducedCharPoly
omit [NeZero n] in
lemma over_extension [Algebra F E] [IsScalarTower K F E] (a : A):
    ∃ g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E, ReducedCharPoly A
    g a = Polynomial.mapAlgHom (Algebra.ofId F E) (ReducedCharPoly A e a) := by
  obtain ⟨g, hg⟩ := mat_over_extension K F E A n e a
  use g
  simp only [ReducedCharPoly, hg, AlgHom.mapMatrix_apply, Polynomial.coe_mapAlgHom]
  change (Matrix.charmatrix _).det = Polynomial.map _ (Matrix.charmatrix _).det
  erw [Matrix.charmatrix_map]
  rw [AlgHom.toRingHom_eq_coe, ← Polynomial.coe_mapRingHom, RingHom.map_det,
    RingHom.mapMatrix_apply]

#exit
lemma _root_.Matrix.charpoly.similar_eq (n : ℕ) (u : (Matrix (Fin n) (Fin n) F)ˣ)
    (A B : Matrix (Fin n) (Fin n) F) (h : A = u * B * u⁻¹):
    A.charpoly = B.charpoly := sorry

-- lemma _root_.Matrix.charmatrix_commute_blockdiag (n m F : Type*) [Fintype n] [Fintype m]
--     [DecidableEq n] [DecidableEq m] [Field F] (A : Matrix n n F):
--     (Matrix.blockDiagonal (fun (_ : m) ↦ A)).charmatrix =
--     Matrix.blockDiagonal (fun _ ↦ A.charmatrix) := sorry

/-- A subtype of a `Prod` that depends only on the second component is equivalent to the
first type times a corresponding subtype of the second type. -/
@[simps]
def Equiv.prodSubtypeSndEquivProdSubtype {α β} {p : β → Prop} :
    {s : α × β // p s.2} ≃ α × {b // p b} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simps!]
def thing' {α β : Type*} (b : β) : {i : α × β // i.2 = b} ≃ α :=
  Equiv.prodSubtypeSndEquivProdSubtype.trans (Equiv.prodUnique α {i : β // i = b})

open Matrix in
theorem Matrix.blockDiagonal_toSquareBlock {r} {n : Type*} [DecidableEq n] [Fintype n]
    (A : Fin r → Matrix n n F) {i} :
    (blockDiagonal A).toSquareBlock Prod.snd i = (A i).reindex (thing' _).symm (thing' _).symm := by
  aesop (add simp toSquareBlock_def)

theorem Matrix.blockDiagonal_charpoly_aux {r} {n : Type*} [DecidableEq n] [Fintype n]
    (A : Fin r → Matrix n n F) {i} :
    ((Matrix.blockDiagonal A).toSquareBlock Prod.snd i).charpoly = (A i).charpoly := by
  rw [blockDiagonal_toSquareBlock, Matrix.charpoly_reindex]

theorem Matrix.blockDiagonal_charpoly {r} {n : Type*}  [DecidableEq n] [Fintype n]
    (A : Fin r → Matrix n n F) :
    (Matrix.blockDiagonal A).charpoly = ∏ i : Fin r, (A i).charpoly := by
  have hM := Matrix.blockTriangular_blockDiagonal A
  simp only [Matrix.charpoly, hM.charmatrix.det_fintype, ← Matrix.charmatrix_toSquareBlock]
  -- TODO: make det_fintype for charpoly
  -- ie BlockTriangular.charpoly for Fintype α
  congr! with i hi
  exact blockDiagonal_charpoly_aux _ _

theorem Matrix.blockDiagonal_const_charpoly (r n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) :
    (Matrix.blockDiagonal fun _ : Fin r => A).charpoly = A.charpoly ^ r := by
  rw [blockDiagonal_charpoly]
  simp

lemma Matrix.reindex_diagonal_charpoly (r n m : ℕ) (eq : m = r * n)
    (A : Matrix (Fin n) (Fin n) F) :
    (Matrix.reindexAlgEquiv F F
      (finProdFinEquiv.trans (finCongr (by rw [eq, mul_comm])) : Fin n × Fin r ≃ Fin m)
    ((Matrix.blockDiagonalRingHom (Fin n) (Fin r) F) fun _ ↦ A)).charpoly =
    A.charpoly ^ r := by
  rw [Matrix.blockDiagonalRingHom_apply, Matrix.reindexAlgEquiv_apply,
    Matrix.charpoly_reindex, blockDiagonal_charpoly]
  simp

-- set_option trace.profiler true in
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 600000 in
include F_bar e in
omit [NeZero n] in
lemma eq_pow_reducedCharpoly (g : F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F) [NeZero m] (a : A):
    ∃ (r : ℕ), NeZero r ∧ m = r * n ∧ Matrix.charpoly (g (1 ⊗ₜ a)) = (ReducedCharPoly A e a)^r :=
  -- if h : m ≠ 0 then
  -- haveI : NeZero m := ⟨h⟩
  have iso : F ⊗[K] A ≃ₐ[F] g.range := AlgEquiv.ofInjective _ <|
    IsSimpleRing.iff_eq_zero_or_injective' (F ⊗[K] A) F |>.1
    (IsCentralSimple.TensorProduct.simple K F A) g|>.resolve_left <| fun hg ↦ by
      simpa [one_ne_zero] using (TwoSidedIdeal.mem_ker g|>.1 <| SetLike.ext_iff.1 hg 1|>.2 (by trivial))
  haveI : Algebra.IsCentral F g.range := .of_algEquiv F _ _ iso
  haveI : IsSimpleRing g.range := .of_ringEquiv iso.toRingEquiv inferInstance
  have ee := writeAsTensorProduct (F := F) (A := Matrix (Fin m) (Fin m) F) g.range
  haveI : IsSimpleRing (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range) :=
    centralizer_isSimple (A := Matrix (Fin m) (Fin m) F) g.range
    (Module.finBasis _ _)
  haveI : Algebra.IsCentral F (g.range ⊗[F] ↥(Subalgebra.centralizer F (SetLike.coe g.range))) :=
    .of_algEquiv F _ (g.range ⊗[F] (Subalgebra.centralizer F (SetLike.coe g.range))) ee
  haveI : Algebra.IsCentral F (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range) :=
    .right_of_tensor_of_field F g.range _
  let r : ℕ := deg F F_bar ⟨.of F (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range)⟩
  have eq : r * n = m := by
    apply_fun fun x ↦ x^2 using (Nat.pow_left_injective (by omega))
    have eq1 : Module.finrank F g.range = n^2 := by
      rw [← iso.toLinearEquiv.finrank_eq, e.toLinearEquiv.finrank_eq]
      simp [pow_two, Module.finrank_matrix]
    simp only [mul_comm, mul_pow, r, deg_sq_eq_dim, ← eq1, ← Module.finrank_tensorProduct,
      ee.symm.toLinearEquiv.finrank_eq]
    rw [pow_two, Module.finrank_matrix]
    simp
  let h: F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F := {
    toFun ta :=
      Matrix.reindexAlgEquiv F _ (finProdFinEquiv.trans ((finCongr (by rw [mul_comm, eq]))))
      (Matrix.blockDiagonalRingHom (Fin n) (Fin r) _ (fun i ↦ e ta))
    map_one' := by
      simp only [eq_mpr_eq_cast, cast_cast, map_one, Matrix.blockDiagonalRingHom_apply]
      erw [Matrix.blockDiagonal_one (m := Fin n) (o := Fin _) (α := F)]
      exact map_one _
    map_mul' := by simp
    map_zero' := by
        simp only [Matrix.blockDiagonalRingHom_apply, map_zero]
        change Matrix.reindexAlgEquiv _ _ _ (Matrix.blockDiagonal 0) = _
        simp
    map_add' fa1 fa2 := by
      simp only [map_add, Matrix.blockDiagonalRingHom_apply]
      change Matrix.reindexAlgEquiv _ _ _
        (Matrix.blockDiagonal ((fun i ↦ e fa1) + (fun i ↦ e fa2))) = _
      rw [Matrix.blockDiagonal_add, map_add]
    commutes' k := by
      simp only [eq_mpr_eq_cast, cast_cast, Algebra.TensorProduct.algebraMap_apply,
        Algebra.id.map_eq_id, RingHom.id_apply, Matrix.blockDiagonalRingHom_apply]
      rw [← mul_one k, ← smul_eq_mul k 1, ← TensorProduct.smul_tmul', map_smul]
      change Matrix.reindexAlgEquiv _ _ _ (Matrix.blockDiagonal (k • _)) = _
      rw [Matrix.blockDiagonal_smul, map_smul, ← Algebra.TensorProduct.one_def, map_one]
      change k • (Matrix.reindexAlgEquiv _ _ _ (Matrix.blockDiagonal 1)) = _
      simp [Algebra.algebraMap_eq_smul_one] }
  ⟨r, deg_pos _ _ _, eq.symm,
  by
    obtain ⟨u, hu⟩ := SkolemNoether' F _ _ h g
    specialize hu (1 ⊗ₜ a)
    delta ReducedCharPoly
    rw [Matrix.charpoly.similar_eq _ m u _ _ hu]
    simp only [h, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    exact Matrix.reindex_diagonal_charpoly F _ _ _ eq.symm (e (1 ⊗ₜ[K] a))⟩
  -- else ⟨0, by omega⟩

-- variable {K F A n m} in
-- abbrev deg_div (g : F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F) [NeZero m] : ℕ :=
--   AlgHom.toMatrix_of_split K F F_bar A n m e g|>.choose

-- set_option synthInstance.maxHeartbeats 60000 in
-- lemma deg_div_eq (g : F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F) [NeZero m]:
--   deg_div F_bar e g =
--   -- if h : m ≠ 0 then
--   --   haveI : NeZero m := ⟨h⟩
--   have iso : F ⊗[K] A ≃ₐ[F] g.range := AlgEquiv.ofInjective _ <|
--     IsSimpleRing.iff_eq_zero_or_injective' (F ⊗[K] A) F |>.1
--     (IsCentralSimple.TensorProduct.simple K F A) g|>.resolve_left <| fun hg ↦ by
--       simpa [one_ne_zero] using (TwoSidedIdeal.mem_ker g|>.1 <| SetLike.ext_iff.1 hg 1|>.2 (by trivial))
--   haveI : Algebra.IsCentral F g.range := .of_algEquiv F _ _ iso
--   haveI : IsSimpleRing g.range := .of_ringEquiv iso.toRingEquiv inferInstance
--   have ee := writeAsTensorProduct (F := F) (A := Matrix (Fin m) (Fin m) F) g.range
--   haveI : IsSimpleRing (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range) :=
--     centralizer_isSimple (A := Matrix (Fin m) (Fin m) F) g.range
--     (Module.finBasis _ _)
--   haveI : Algebra.IsCentral F (g.range ⊗[F] ↥(Subalgebra.centralizer F (SetLike.coe g.range))) :=
--     .of_algEquiv F _ (g.range ⊗[F] (Subalgebra.centralizer F (SetLike.coe g.range))) ee
--   haveI : Algebra.IsCentral F (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range) :=
--     .right_of_tensor_of_field F g.range _
--   deg F F_bar ⟨.of F (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range)⟩ := by
--     simp; rfl
-- WHY IS THE PROOF NOT RFL???

-- include F_bar in
-- omit [NeZero n] in
-- theorem eq_pow_reducedPoly (g : F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F) [NeZero m] (a : A):
--     ∃(r : ℕ), Matrix.charpoly (g (1 ⊗ₜ a)) = (ReducedCharPoly A e a)^r := ⟨
--   AlgHom.toMatrix_of_split K F F_bar A n m e g|>.choose, by
--   set r := AlgHom.toMatrix_of_split K F F_bar A n m e g|>.choose with r_eq
--   have mul_eq := AlgHom.toMatrix_of_split K F F_bar A n m e g|>.choose_spec
--   obtain ⟨u, hu⟩ := SkolemNoether' F _ _ (h K F F_bar A _ _ e g) g
--   specialize hu (1 ⊗ₜ a)
--   delta ReducedCharPoly
--   rw [Matrix.charpoly.similar_eq _ m u _ _ hu]
--   simp only [h, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
--   exact Matrix.reindex_diagonal_charpoly F _ _ _ mul_eq (e (1 ⊗ₜ[K] a))⟩

include F_bar in
lemma eq_polys (f1 f2 : F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F) (a : A):
    ReducedCharPoly A f1 a = ReducedCharPoly A f2 a := by
  obtain ⟨r, _, hr1, hr2⟩ := eq_pow_reducedCharpoly K F F_bar A n n f1 f2 a
  have : r = 1 := by simpa [mul_left_eq_self₀, NeZero.ne n] using hr1.symm
  subst this
  simp at hr2
  rw [← hr2]
  rfl

lemma _root_.Matrix.charpoly_eq_reduced (K : Type*) [Field K] (n : ℕ) [NeZero n]
    (M : Matrix (Fin n) (Fin n) K):
    M.charpoly = ReducedCharPoly (F := K) ⟨.of K (Matrix (Fin n) (Fin n) K)⟩ (n := n)
      (Algebra.TensorProduct.lid _ _) M := by
  simp [ReducedCharPoly]

variable [IsGalois K F]

open Polynomial

lemma mem_Kx (a : A): ∃ f : K[X], ReducedCharPoly A e a = f.mapAlgHom (Algebra.ofId K F) := by
  haveI : Nonempty (F ≃ₐ[K] F) := inferInstance
  have := over_extension K F F A n e a
  sorry

lemma cayleyHamilton (a : A) : (ReducedCharPoly.mem_Kx K F A n e a).choose.aeval a = 0 := by

  sorry

end ReducedCharPoly
