import BrauerGroup.SplittingOfCSA
import BrauerGroup.DoubleCentralizer
import BrauerGroup.Mathlib.RingTheory.TensorProduct.Basic
import BrauerGroup.Mathlib.RingTheory.MatrixAlgebra
import BrauerGroup.Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import BrauerGroup.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.RingTheory.SimpleRing.Congr

universe u v w

open scoped TensorProduct

section poly

suppress_compilation

-- instance (R R' A B C : Type) [CommSemiring R]
--     [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
--     [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
--     [IsScalarTower R R' A] [IsScalarTower R R' B]
--     : NonUnitalSemiring ((A ⊗[R'] B) ⊗[R] C) := inferInstance

  -- [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : AddCommMonoid M] [inst_6 : Module R M] [inst_7 : Module A M]
  -- [inst_8 : Module B M] [inst_9 : IsScalarTower R A M] [inst_10 : IsScalarTower R B M] [inst_11 : SMulCommClass A B M]
  -- [inst_12 : AddCommMonoid P] [inst_13 : Module A P] [inst_14 : AddCommMonoid Q] [inst_15 : Module R Q]
  -- [inst_16 : Module R P] [inst_17 : IsScalarTower R A P] [inst_18 : Algebra A B] [inst_19 : IsScalarTower A B M] :
  -- (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] P ⊗[R] Q := sorry

-- instance [Algebra F E] [IsScalarTower K F E] : IsScalarTower K (Algebra.ofId F E).range E where
--   smul_assoc k := fun ⟨f, hf⟩ x ↦ by
--     change (k • f) • _ = k • f • x
--     exact smul_assoc _ _ _

-- instance [Algebra F E] : Algebra (Algebra.ofId F E).range F :=
--   RingHom.toAlgebra (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm

-- instance [Algebra F E] [IsScalarTower K F E] : IsScalarTower K (Algebra.ofId F E).range F where
--   smul_assoc k := fun ⟨e, he⟩ x ↦ by
--     simp only [RingHom.smul_toAlgebra, RingHom.coe_coe]
--     change (AlgEquiv.restrictScalars K (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm) _ * _ = _
--     rw [map_smul]
--     simp

variable (K F E K_bar F_bar A: Type*) [Field K] [Field F] [Field E] [Field F_bar] [Algebra K F]
  [Algebra K E] [Field K_bar] [Algebra K K_bar] [Algebra F F_bar] [hK_bar : IsAlgClosure K K_bar]
  [hF_bar : IsAlgClosure F F_bar] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  (n m : ℕ) [NeZero n] (e : F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F)

section defs

variable {K F E} in
@[simps]
def φ_m (φ : F →ₐ[K] E) : Matrix (Fin n) (Fin n) F →ₐ[K] Matrix (Fin n) (Fin n) E where
  toFun M := fun i j ↦ φ (M i j)
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_mul' M1 M2 := by ext i j; simp [Matrix.mul_apply]
  map_zero' := by ext; simp
  map_add' M1 M2 := by ext; simp
  commutes' k := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply]
    split_ifs with h <;>  simp

omit [NeZero n] in
variable {K F E} in
lemma φ_m_inj (φ : F →ₐ[K] E) : Function.Injective (φ_m n φ) := fun M N h ↦ funext fun i ↦
  funext fun j ↦ by simp [← Matrix.ext_iff] at h; exact φ.injective (h i j)

variable {K F E} in
abbrev e1Aux (φ : F →ₐ[K] E) : Matrix (Fin n) (Fin n) φ.range ≃ₐ[K] (φ_m n φ).range where
  toFun M := ⟨fun i j ↦ M i j|>.1, ⟨fun i j ↦ M i j|>.2.choose, funext fun i ↦ funext fun j ↦ M i j|>.2.choose_spec⟩⟩
  invFun := fun ⟨M, (h : ∃ _, _ = _)⟩ ↦ fun i j ↦ ⟨M i j, ⟨h.choose i j, Matrix.ext_iff.2 h.choose_spec i j ⟩⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by ext; simp [Matrix.mul_apply]
  map_add' _ _ := rfl
  commutes' k := by
    ext
    simp only [Matrix.algebraMap_matrix_apply, SubalgebraClass.coe_algebraMap]
    exact apply_ite Subtype.val _ ((algebraMap K ↥φ.range) k) 0

abbrev e1 (φ : F →ₐ[K] E) : Matrix (Fin n) (Fin n) F ≃ₐ[K] φ_m n φ|>.range :=
  AlgEquiv.ofBijective (φ_m n φ).rangeRestrict ⟨AlgHom.injective_codRestrict _ _
    (φ_m n φ).mem_range_self|>.2 <| φ_m_inj n φ, AlgHom.rangeRestrict_surjective _⟩

abbrev e1' (φ : F →ₐ[K] E) : φ.range ⊗[K] A ≃ₐ[K] Matrix (Fin n) (Fin n) φ.range :=
  Algebra.TensorProduct.congr (AlgEquiv.ofInjectiveField φ).symm AlgEquiv.refl|>.trans <|
  ({__ := e, commutes' r := by simpa using (e.commutes (algebraMap K F r))} : _ ≃ₐ[K] Matrix (Fin n) (Fin n) F).trans
  <| e1 _ _ _ _ φ|>.trans (e1Aux n φ).symm

variable {K F E} in
abbrev e1'' (φ : F →ₐ[K] E) : φ.range ⊗[K] A ≃ₐ[φ.range] Matrix (Fin n) (Fin n) φ.range where
  __ := e1' K F E A n e φ
  commutes' := fun ⟨x, ⟨y, eq⟩⟩ ↦ Matrix.ext_iff.1 <| fun i j ↦ by
    simp [AlgEquiv.ofInjectiveField]
    rw [← mul_one ((AlgEquiv.ofInjective φ _).symm ⟨x, _⟩), ← smul_eq_mul, ← TensorProduct.smul_tmul',
      map_smul, ← Algebra.TensorProduct.one_def, map_one]
    simp [Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · subst h
      simp only [AlgEquiv.ofInjective, AlgEquiv.ofLeftInverse_symm_apply, Matrix.one_apply_eq,
        map_one, mul_one, Subtype.mk.injEq]
      set ψ := Classical.choose _ with ψ_eq
      let hψ := Classical.choose_spec φ.injective.hasLeftInverse
      simp only [Function.LeftInverse, ← ψ_eq] at hψ
      rw [← eq, hψ y]
      rfl
    · simp [h]
      exact Subtype.ext rfl

set_option maxSynthPendingDepth 2 in
variable {K F E A n} in
abbrev g (φ : F →ₐ[K] E) : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E :=
  Algebra.TensorProduct.congr (Algebra.TensorProduct.rid φ.range E E|>.symm) AlgEquiv.refl |>.trans
  <| Algebra.TensorProduct.assoc' K E φ.range E φ.range A|>.trans <|
  Algebra.TensorProduct.congr AlgEquiv.refl (e1'' A n e φ) |>.trans <|
  (matrixEquivTensor' _ _ _ ).symm

end defs

variable {K E F} in
omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma mat_over_extension (φ : F →ₐ[K] E) (a : A) :
    ∃ g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E, g (1 ⊗ₜ a) =
    φ.mapMatrix (e (1 ⊗ₜ a)) := by
  use g e φ
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_coe, AlgHom.coe_id, id_eq,
    Algebra.TensorProduct.assoc'_apply, AlgEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    AlgEquiv.symm_mk, map_one, AlgEquiv.coe_ofBijective, Equiv.coe_fn_mk, AlgHom.coe_codRestrict,
    φ_m_apply, matrixEquivTensor'_symm_apply, one_smul, AlgHom.mapMatrix_apply,
    Algebra.TensorProduct.one_def]
  ext i j
  simp [Matrix.map_apply]
  rfl

variable {K F n A} in
def ReducedCharPoly (a : A) : Polynomial F := Matrix.charpoly (e (1 ⊗ₜ a)) -- elements in F[X]

namespace ReducedCharPoly

omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma over_extension (φ : F →ₐ[K] E) (a : A) :
    ∃ g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E, ReducedCharPoly g a =
    Polynomial.mapAlgHom φ (ReducedCharPoly e a) := by
  obtain ⟨g, hg⟩ := mat_over_extension A n e φ a
  use g
  simp only [ReducedCharPoly, hg, AlgHom.mapMatrix_apply, Polynomial.coe_mapAlgHom]
  change (Matrix.charmatrix _).det = Polynomial.map _ (Matrix.charmatrix _).det
  erw [Matrix.charmatrix_map]
  rw [AlgHom.toRingHom_eq_coe, ← Polynomial.coe_mapRingHom, RingHom.map_det,
    RingHom.mapMatrix_apply]

end ReducedCharPoly

end poly

section mono

variable (K F E K_bar F_bar A: Type u) [Field K] [Field F] [Field E] [Field F_bar] [Algebra K F]
  [Algebra K E] [Field K_bar] [Algebra K K_bar] [Algebra F F_bar] [hK_bar : IsAlgClosure K K_bar]
  [hF_bar : IsAlgClosure F F_bar] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  (n m : ℕ) [NeZero n] (e : F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F)

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 600000 in
include F_bar in
omit [NeZero n] in
lemma eq_pow_reducedCharpoly (g : F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F) [NeZero m] (a : A) :
    ∃(r : ℕ), NeZero r ∧ m = r * n ∧ Matrix.charpoly (g (1 ⊗ₜ a)) = (ReducedCharPoly e a)^r :=
  have iso: F ⊗[K] A ≃ₐ[F] g.range := AlgEquiv.ofInjective _ <| RingHom.injective _
  haveI : Algebra.IsCentral F g.range := .of_algEquiv F _ _ iso
  haveI : IsSimpleRing g.range := .of_ringEquiv iso.toRingEquiv inferInstance
  have ee := writeAsTensorProduct (F := F) (A := Matrix (Fin m) (Fin m) F) g.range
  haveI : IsSimpleRing (Subalgebra.centralizer (A := Matrix (Fin m) (Fin m) F) F g.range) :=
    centralizer_isSimple (A := Matrix (Fin m) (Fin m) F) g.range
    (Module.finBasis F (Module.End F g.range))
  haveI : Algebra.IsCentral F (g.range ⊗[F] (Subalgebra.centralizer F (SetLike.coe g.range))) :=
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
  let h : F ⊗[K] A →ₐ[F] Matrix (Fin m) (Fin m) F := {
    toFun ta :=
      Matrix.reindexAlgEquiv F _ (finProdFinEquiv.trans ((finCongr (by rw [mul_comm, eq]))))
      (Matrix.blockDiagonalRingHom (Fin n) (Fin r) _ (fun i ↦ e ta))
    map_one' := by
      simp only [map_one, Matrix.blockDiagonalRingHom_apply]
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
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Matrix.blockDiagonalRingHom_apply]
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
    rw [Matrix.charpoly.similar_eq m u _ _ hu]
    simp only [h, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    exact Matrix.reindex_diagonal_charpoly _ _ _ eq.symm (e (1 ⊗ₜ[K] a))⟩

include F_bar in
lemma eq_polys (f1 f2 : F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F) (a : A) :
    ReducedCharPoly f1 a = ReducedCharPoly f2 a := by
  obtain ⟨r, _, hr1, hr2⟩ := eq_pow_reducedCharpoly K F F_bar A n n f1 f2 a
  have : r = 1 := by simpa [mul_left_eq_self₀, NeZero.ne n] using hr1.symm
  subst this
  simp at hr2
  rw [← hr2]
  rfl

open Polynomial

section
variable [IsGalois K F] [FiniteDimensional K F]

lemma fixedpoints (x : F) : (∀ φ : F ≃ₐ[K] F, φ x = x) → x ∈ (Algebra.ofId K F).range := by
  intro h
  have eq1 := IntermediateField.mem_fixedField_iff (F := K) ⊤ x|>.2 (by aesop)
  have := OrderIso.map_bot (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := F)).symm
  change IntermediateField.fixedField ⊤ = _ at this
  rwa [this] at eq1

-- lemma 3
include F_bar in
lemma mem_Kx (a : A) : ∃ f : K[X], ReducedCharPoly e a = f.mapAlgHom (Algebra.ofId K F) := by
  have fixed : ∀ φ : F ≃ₐ[K] F, (e (1 ⊗ₜ[K] a)).charpoly = map φ (e (1 ⊗ₜ[K] a)).charpoly := fun φ ↦ by
    obtain ⟨g, hg⟩ := mat_over_extension (E := F) A n e φ a
    obtain ⟨r, _, hr1, hr⟩ := eq_pow_reducedCharpoly K F F_bar A n n e g a
    rw [eq_comm, Nat.mul_eq_right (NeZero.ne n)] at hr1
    subst hr1
    simp only [AlgHom.coe_coe, pow_one] at hr
    rw [ReducedCharPoly] at *
    apply_fun Matrix.charpoly at hg
    change _ = ((e (1 ⊗ₜ a)).map φ.toRingHom).charpoly at hg
    rw [Matrix.charpoly_map] at hg
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom] at hg
    exact hr.symm.trans hg
  simp only [ext_iff, coeff_map, RingHom.coe_coe] at fixed
  have fixed2 : ∀ m : ℕ, (e (1 ⊗ₜ a)).charpoly.coeff m ∈ (Algebra.ofId K F).range := fun m ↦
    fixedpoints K F _ <| fun φ ↦ fixed φ m |>.symm
  rw [ReducedCharPoly]
  use ⟨(⟨(e (1 ⊗ₜ[K] a)).charpoly.support, fun m ↦ fixed2 m|>.choose, ?_⟩ : ℕ →₀ K)⟩
  pick_goal 2
  · simp
    intro k
    constructor
    · by_contra! h
      obtain ⟨h1, h2⟩ := h
      have := fixed2 k|>.choose_spec
      apply_fun (Algebra.ofId K F) at h2
      rw [map_zero] at h2
      rw [← this] at h1
      tauto
    · by_contra! h
      obtain ⟨h1, h2⟩ := h
      have := fixed2 k|>.choose_spec
      simp only [h2] at this
      change algebraMap _ _ _ = 0 at this
      rw [FaithfulSMul.algebraMap_eq_zero_iff] at this
      exact h1 <| by convert this
  ext k
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_mapAlgHom, coeff_map, coeff_ofFinsupp,
    Finsupp.coe_mk]
  exact fixed2 k|>.choose_spec.symm

section field_ext

noncomputable def algClosure_ext (L F F_bar: Type*) [Field F] [Field L] [Field F_bar] [Algebra F L]
    [Algebra F F_bar] [FiniteDimensional F L] [IsAlgClosure F F_bar] : Algebra L F_bar :=
  haveI : IsAlgClosed F_bar := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F L := by exact Algebra.IsAlgebraic.of_finite F L
  RingHom.toAlgebra <| IsAlgClosed.lift (R := F) (S := L) (M := F_bar)

end field_ext


-- `A` is a central simple algebra over `K`, `F/K` is splitting field with iso `e : F ⊗[K] A ≃ₐ[F] Mₙ(F)`,
-- `L/K` is another splitting field with iso `e' : L ⊗[K] A ≃ₐ[L] Mₙ(L)`.
-- ∀ a : A, reduced charpoly of `a` using `e` is the same as using `e'`.
include F_bar in
set_option maxSynthPendingDepth 3 in
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 1600000 in
lemma unique_onver_split (L L_bar : Type u) [Field L] [Field L_bar] [Algebra K L] [Algebra L L_bar]
    [FiniteDimensional K L] [IsGalois K L] [hL : IsAlgClosure L L_bar]
    (e' : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) (a : A) :
      ∃ f g : K[X], ReducedCharPoly e a = f.mapAlgHom (Algebra.ofId K F) ∧
      ReducedCharPoly e' a = g.mapAlgHom (Algebra.ofId K L) ∧ f = g := by
  obtain ⟨f, hf⟩ := mem_Kx K F F_bar A n e a
  obtain ⟨g, hg⟩ := mem_Kx K L L_bar A n e' a
  refine ⟨f, g, hf, hg, ?_⟩
  let E := (F ⊗[K] L) ⧸ (Ideal.exists_maximal (F ⊗[K] L)).choose
  have : IsField E := Ideal.Quotient.maximal_ideal_iff_isField_quotient _|>.1 (Ideal.exists_maximal _).choose_spec
  letI alg : Algebra K E := Ideal.Quotient.algebra K
  let φ : F →ₐ[K] E := {
    toFun m := Ideal.Quotient.mk _ (m ⊗ₜ 1)
    map_one' := by simp [← Algebra.TensorProduct.one_def]
    map_mul' x y := by rw [← mul_one 1, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, mul_one]
    map_zero' := by simp
    map_add' := by simp [TensorProduct.add_tmul]
    commutes' := by simpa [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', ←
      Algebra.TensorProduct.one_def] using fun _ ↦ by rfl }
  let ψ : L →ₐ[K] E := {
    toFun m := Ideal.Quotient.mk _ (1 ⊗ₜ m)
    map_one' := by simp [← Algebra.TensorProduct.one_def]
    map_mul' x y := by rw [← mul_one 1, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, mul_one]
    map_zero' := by simp
    map_add' := by simp [TensorProduct.tmul_add]
    commutes' := by simpa [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', ←
      Algebra.TensorProduct.one_def] using fun _ ↦ by rfl }
  obtain ⟨g1, hg1⟩ := @ReducedCharPoly.over_extension K F E A _ _ (IsField.toField this) _
    (Ideal.Quotient.algebra K) _ _ _ e φ a
  obtain ⟨g2, hg2⟩ := @ReducedCharPoly.over_extension K L E A _ _ (IsField.toField this) _
    (Ideal.Quotient.algebra K) _ _ _ e' ψ a
  -- haveI alge : Algebra F E := RingHom.toAlgebra φ.toRingHom
  -- have findim' : FiniteDimensional F E := Module.Finite.quotient F (Ideal.exists_maximal (F ⊗[K] L)).choose
  have alg' : Algebra E F_bar := @algClosure_ext E F F_bar _ (IsField.toField this) _ (RingHom.toAlgebra φ.toRingHom) _
    (by
      convert Module.Finite.quotient F (Ideal.exists_maximal (F ⊗[K] L)).choose
      ext r m
      change φ r * m = r • m
      simp [φ]
      induction m using Submodule.Quotient.induction_on with
      | H m =>
      induction m using TensorProduct.induction_on with
      | tmul x y =>
        simp only [Ideal.Quotient.mk_eq_mk]
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← smul_eq_mul,
          ← TensorProduct.smul_tmul']
        rfl
      | add x y hx hy =>
        change _ * Ideal.Quotient.mk _ _ = r • Ideal.Quotient.mk _ _ at hx hy
        simp [map_add, mul_add, hx, hy]
      | zero => simp) _
  have algclo : IsAlgClosed F_bar := IsAlgClosure.isAlgClosed F
  have tow : IsScalarTower F E F_bar := {
    smul_assoc f e f0 := by
      induction e using Submodule.Quotient.induction_on with
      | H z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        -- change _ = f • (IsAlgClosed.lift (S := E) (M := F_bar) _)
        sorry
      | add x y _ _ => sorry
  }
  -- have hg12 := @eq_polys K E F_bar _ (IsField.toField this) _ (Ideal.Quotient.algebra K)
  --   alg' (@isAlgClosure_iff E (IsField.toField this) F_bar _ alg' |>.2
  --   ⟨IsAlgClosure.isAlgClosed F, @Algebra.IsAlgebraic.tower_top F E F_bar _ this.toField _ _ _ _ tow _⟩)
  --   A n _ g1 g2 a

  sorry

set_option maxSynthPendingDepth 3 in
omit [IsGalois K F] [FiniteDimensional K F] in
theorem invariant_extend_scalars (L L_bar : Type u) [Field L] [Field L_bar] [Algebra F L] [Algebra K L]
    [Algebra L L_bar] [IsAlgClosure L L_bar] (e0 : L ⊗[F] (F ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) [IsScalarTower K F L] (a : A) :
    (ReducedCharPoly e a).mapAlgHom (Algebra.ofId F L) = ReducedCharPoly e0 (1 ⊗ₜ a) := by
  let e0' : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L := Algebra.TensorProduct.congr
    (Algebra.TensorProduct.rid F L L).symm AlgEquiv.refl|>.trans <|
    Algebra.TensorProduct.assoc' _ _ _ _ _ _ |>.trans e0
  obtain ⟨g, hg⟩ := ReducedCharPoly.over_extension K F L A n e ((Algebra.ofId F L).restrictScalars K) a
  have : ReducedCharPoly e0' a = ReducedCharPoly e0 (1 ⊗ₜ a) := by simp [ReducedCharPoly, e0']
  rw [← this, eq_polys K L L_bar A n e0' g a, hg]
  simp

omit [NeZero n] [IsGalois K F] [FiniteDimensional K F] in
theorem invariant_algEquiv (A1 A2 L : Type u) [Field L] [Algebra K L] [Ring A1] [Ring A2]
    [Algebra K A1] [Algebra K A2] [Algebra.IsCentral K A1] [Algebra.IsCentral K A2]
    [IsSimpleRing A1] [IsSimpleRing A2] (e1 : F ⊗[K] A1 ≃ₐ[F] Matrix (Fin n) (Fin n) F)
    (f : A1 ≃ₐ[K] A2) (a : A1) :
    ReducedCharPoly e1 a = ReducedCharPoly (Algebra.TensorProduct.congr
      AlgEquiv.refl f.symm|>.trans e1) (f a) := by
  simp [ReducedCharPoly]

end

variable {K F A n} in
def reducedNorm (a : A) := Matrix.det (e (1 ⊗ₜ a))

variable {K F A n} in
def reducedTrace (a : A) := Matrix.trace (e (1 ⊗ₜ a))

omit [NeZero n] in
theorem equalMatrixCharpoly (M : Matrix (Fin n) (Fin n) K) :
    @ReducedCharPoly K K (Matrix (Fin n) (Fin n) K) _ _ _ _ _ n
    (Algebra.TensorProduct.lid _ _) M = M.charpoly := by simp [ReducedCharPoly]

open Algebra.TensorProduct in
omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma reducedNorm_mul (a b : A) : reducedNorm e (a * b) = reducedNorm e a * reducedNorm e b :=
  show Matrix.det _ = _ from (mul_one (M := F) 1).symm ▸ tmul_mul_tmul (R := K) (1 : F) 1 a b ▸
    map_mul e _ _ ▸ Matrix.det_mul _ _

open Algebra.TensorProduct in
omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma reducedTrace_smul (a : A) (r : K) : reducedTrace e (r • a) = r • reducedTrace e a := by
  simpa only [reducedTrace, ← Matrix.trace_smul, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul'] using congr_arg _ <| LinearMapClass.map_smul_of_tower e r (1 ⊗ₜ a)

open Algebra.TensorProduct in
omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma reducedTrace_mul_comm (a b : A) : reducedTrace e (a * b) = reducedTrace e (b * a) := by
  simp only [reducedTrace]
  rw [← mul_one 1, ← tmul_mul_tmul, map_mul, Matrix.trace_mul_comm, ← map_mul, tmul_mul_tmul]

omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma reducedNorm_algebraMap (k : K) : reducedNorm e (algebraMap K A k) = (algebraMap K F k) ^ n := by
  simp [reducedNorm, Algebra.algebraMap_eq_smul_one, LinearMapClass.map_smul_of_tower e,
    ← Algebra.TensorProduct.one_def, _root_.smul_pow]

omit [NeZero n] [Algebra.IsCentral K A] [IsSimpleRing A] in
lemma reducedTrace_algebraMap (k : K) : reducedTrace e (algebraMap K A k) = n • (algebraMap K F k) := by
  simp [reducedTrace, Algebra.algebraMap_eq_smul_one, LinearMapClass.map_smul_of_tower e,
    ← Algebra.TensorProduct.one_def]

@[simps]
def reducedNormHom : A →*₀ F where
  toFun := reducedNorm e
  map_zero' := by simp [reducedNorm]
  map_one' := by simp [reducedNorm, ← Algebra.TensorProduct.one_def]
  map_mul' := by simp [reducedNorm_mul]

@[simps]
def reducedTraceLinearMap : A →ₗ[K] F where
  toFun := reducedTrace e
  map_add' := by simp [reducedTrace, TensorProduct.tmul_add]
  map_smul' := by simp [reducedTrace_smul]

lemma reducedNorm_ne_zero_iff (a : A) : reducedNorm e a ≠ 0 ↔ IsUnit a :=
  ⟨sorry, fun ha1 ha2 ↦ sorry⟩

theorem inv_under_extend (L L_bar : Type u) [Field L] [Field L_bar] [Algebra F L] [Algebra K L]
    [Algebra L L_bar] [IsAlgClosure L L_bar] (e0 : L ⊗[F] (F ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    [IsScalarTower K F L] (a : A) : reducedNorm e0 (1 ⊗ₜ a) = algebraMap F L (reducedNorm e a) := by
  -- use det is coeffiecient of charpoly
  sorry

-- mimic what I did above, write a verision for reduced trace

theorem inv_under_algEquiv (A1 A2 L : Type u) [Field L] [Algebra K L] [Ring A1] [Ring A2]
    [Algebra K A1] [Algebra K A2] [Algebra.IsCentral K A1] [Algebra.IsCentral K A2]
    [IsSimpleRing A1] [IsSimpleRing A2] (e1 : F ⊗[K] A1 ≃ₐ[F] Matrix (Fin n) (Fin n) F)
    (f : A1 ≃ₐ[K] A2) (a : A1) :
    reducedNorm e1 a = reducedNorm
    (Algebra.TensorProduct.congr AlgEquiv.refl f.symm|>.trans e1) (f a) := by
  sorry

-- mimic what I did above, write a verision for reduced trace

end mono
