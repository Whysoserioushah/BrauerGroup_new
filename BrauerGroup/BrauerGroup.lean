import BrauerGroup.CentralSimple
import BrauerGroup.FieldCat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

suppress_compilation
universe u v v₁ v₂ w

variable (K : Type u) [Field K]
variable (A B : Type u) [Ring A] [Ring B] [Algebra K A] [Algebra K B]

open scoped TensorProduct BigOperators

lemma bijective_of_dim_eq_of_isCentralSimple
    [csa_source : IsSimpleRing A]
    [fin_source : FiniteDimensional K A]
    [fin_target : FiniteDimensional K B]
    (f : A →ₐ[K] B) (h : Module.finrank K A = Module.finrank K B) :
    Function.Bijective f := by
  obtain hA|hA := subsingleton_or_nontrivial A
  · have eq1 : Module.finrank K A = 0 := by
      rw [finrank_zero_iff_forall_zero]
      intro x
      apply Subsingleton.elim
    rw [eq1] at h
    replace h : Subsingleton B := by
      constructor
      symm at h
      rw [finrank_zero_iff_forall_zero] at h
      intro a b
      rw [h a, h b]
    rw [Function.bijective_iff_existsUnique]
    intro b
    refine ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  · have := IsSimpleRing.iff_injective_ringHom_or_subsingleton_codomain A |>.1 csa_source
      f.toRingHom
    rcases this with (H|H)
    · refine ⟨H, ?_⟩
      change Function.Surjective f.toLinearMap
      have := f.toLinearMap.finrank_range_add_finrank_ker
      rw [show Module.finrank K (LinearMap.ker f.toLinearMap) = 0 by
        rw [finrank_zero_iff_forall_zero]
        rintro ⟨x, hx⟩
        rw [LinearMap.ker_eq_bot (f := f.toLinearMap) |>.2 H] at hx
        ext
        exact hx, add_zero, h] at this
      rw [← LinearMap.range_eq_top]

      apply Submodule.eq_top_of_finrank_eq
      exact this
    · have : (1 : A) ∈ TwoSidedIdeal.ker f.toRingHom := by
        simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, RingHom.coe_coe, map_one]
        exact Subsingleton.elim _ _
      simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, map_one] at this
      have hmm : Nontrivial B := by
        let e := LinearEquiv.ofFinrankEq _ _ h
        exact Equiv.nontrivial e.symm.toEquiv

      exact one_ne_zero this |>.elim


lemma bijective_of_surj_of_isCentralSimple
    [csa_source : IsSimpleRing A]
    (f : A →ₐ[K] B) [Nontrivial B] (h : Function.Surjective f) :
    Function.Bijective f :=
  ⟨IsSimpleRing.iff_injective_ringHom A |>.1 inferInstance f.toRingHom, h⟩
-- instance tensor_CSA_is_CSA
--     [Algebra.IsCentral K A] [hA: IsSimpleRing A]
--     [Algebra.IsCentral K B] [hB: IsSimpleRing B] :
--     IsSimpleRing (A ⊗[K] B) := inferInstance
  --  is_central := IsCentralSimple.TensorProduct.isCentral K A B hA.is_central hB.is_central
  --  simple := IsCentralSimple.TensorProduct.simple K A B

instance CSA_op_is_CSA [hA: Algebra.IsCentral K A] :
    Algebra.IsCentral K Aᵐᵒᵖ where
  out z hz:= by
    let z': A := z.unop
    have hz' : ∀ (x : A), x * z' = z' * x := by
      rw [Subalgebra.mem_center_iff] at hz
      intro x; specialize hz (MulOpposite.op x)
      have z'_eq : MulOpposite.op z'= z := rfl
      rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
      have : (MulOpposite.op (z' * x)).unop = z' * x := rfl
      simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
          MulOpposite.unop_op, z']
    obtain ⟨k, hk⟩ := hA.out $ Subalgebra.mem_center_iff.mpr hz'
    exact ⟨k, MulOpposite.unop_inj.mp hk⟩
  -- is_simple := @op_simple A _ hA.is_simple

-- instance [IsSimpleRing A] : IsSimpleRing Aᵐᵒᵖ := @op_simple A _ _

namespace tensor_self_op

variable [Algebra.IsCentral K A] [hA: IsSimpleRing A] [FiniteDimensional K A]

instance st : IsScalarTower K K (Module.End K A) where
  smul_assoc k₁ k₂ f := DFunLike.ext _ _ fun a => by
    change (k₁ * k₂) • f a = k₁ • (k₂ • f a)
    rw [mul_smul]

def toEnd : A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  Algebra.TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun x => a * x
          map_add' := mul_add _
          map_smul' := by simp }
      map_one' := by aesop
      map_mul' := by intros; ext; simp [mul_assoc]
      map_zero' := by aesop
      map_add' := by intros; ext; simp [add_mul]
      commutes' := fun k => DFunLike.ext _ _ fun a => show (algebraMap K A) k * a = k • _ from
        (Algebra.smul_def _ _).symm }
    { toFun := fun a =>
        { toFun := fun x => x * a.unop
          map_add' := fun x y => by simp [add_mul]
          map_smul' := by simp }
      map_one' := by aesop
      map_mul' := by intros; ext; simp [mul_assoc]
      map_zero' := by aesop
      map_add' := by intros; ext; simp [mul_add]
      commutes' := fun k => DFunLike.ext _ _ fun a =>
        show a * (algebraMap K A) k = k • _ by
          rw [Algebra.smul_def, Algebra.commutes]
          rfl }
    fun a a' => show _ = _ from DFunLike.ext _ _ fun x => show a * (x * a'.unop) = a * x * a'.unop
      from mul_assoc _ _ _ |>.symm

-- instance : Algebra.IsCentral K Aᵐᵒᵖ := inferInstance -- CSA_op_is_CSA K A inferInstance
instance : FiniteDimensional K Aᵐᵒᵖ := LinearEquiv.finiteDimensional
  (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ)

instance fin_end : FiniteDimensional K (Module.End K A) :=
  LinearMap.finiteDimensional

omit [Algebra.IsCentral K A] hA in
lemma dim_eq :
    Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
  rw [Module.finrank_tensorProduct]
  rw [show Module.finrank K (Module.End K A) =
    Module.finrank K (Matrix (Fin $ Module.finrank K A) (Fin $ Module.finrank K A) K) from
    (algEquivMatrix $ Module.finBasis _ _).toLinearEquiv.finrank_eq]
  rw [Module.finrank_matrix, Fintype.card_fin]
  rw [show Module.finrank K Aᵐᵒᵖ = Module.finrank K A from
    (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.finrank_eq]
  simp only [Module.finrank_self, mul_one]

def equivEnd : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (toEnd K A) <| bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <|
    dim_eq K A

end tensor_self_op

open tensor_self_op in
def tensor_self_op
    [Algebra.IsCentral K A] [hA: IsSimpleRing A] [FiniteDimensional K A] :
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K]
    (Matrix (Fin $ Module.finrank K A) (Fin $ Module.finrank K A) K) :=
  equivEnd K A |>.trans $ algEquivMatrix $ Module.finBasis _ _

def tensor_op_self
    [Algebra.IsCentral K A] [hA: IsSimpleRing A] [FiniteDimensional K A] :
    Aᵐᵒᵖ ⊗[K] A ≃ₐ[K]
    (Matrix (Fin $ Module.finrank K A) (Fin $ Module.finrank K A) K) :=
  (Algebra.TensorProduct.comm _ _ _).trans $ tensor_self_op _ _

/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/


structure CSA (K : Type u) [Field K] where
  (carrier : Type v)
  [ring : Ring carrier]
  [algebra : Algebra K carrier]
  [isCentral : Algebra.IsCentral K carrier]
  [isSimple : IsSimpleRing carrier]
  [fin_dim : FiniteDimensional K carrier]

instance : CoeSort (CSA.{u, v} K) (Type v) where
  coe A := A.carrier

instance (A : CSA K) : Ring A := A.ring

instance (A : CSA K) : Algebra K A := A.algebra

instance (A : CSA K) : Algebra.IsCentral K A := A.isCentral

instance (A : CSA K) : IsSimpleRing A := A.isSimple

instance (A : CSA K) : FiniteDimensional K A := A.fin_dim

variable {K : Type u} [Field K]

structure BrauerEquivalence (A B : CSA K) where
(n m : ℕ) [hn: NeZero n] [hm : NeZero m]
(iso: Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

instance (A B : CSA K) (h : BrauerEquivalence A B) : NeZero h.n := h.hn
instance (A B : CSA K) (h : BrauerEquivalence A B) : NeZero h.m := h.hm

abbrev IsBrauerEquivalent (A B : CSA K) := Nonempty (BrauerEquivalence A B)

namespace IsBrauerEquivalent

def refl (A : CSA K) : IsBrauerEquivalent A A := ⟨⟨1, 1, AlgEquiv.refl⟩⟩

def symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
  obtain ⟨n, m, iso⟩ := h
  exact ⟨⟨m, n, iso.symm⟩⟩

def matrix_eqv' (n m : ℕ) (A : Type*) [Ring A] [Algebra K A] :
    (Matrix (Fin n × Fin m) (Fin n × Fin m) A) ≃ₐ[K] Matrix (Fin (n * m)) (Fin (n * m)) A :=
{ Matrix.reindexLinearEquiv K A finProdFinEquiv finProdFinEquiv with
  toFun := Matrix.reindex finProdFinEquiv finProdFinEquiv
  map_mul' := fun m n ↦ by simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  commutes' := fun k ↦ by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finProdFinEquiv_symm_apply,
      Matrix.algebraMap_matrix_apply, Prod.mk.injEq]
    if h : i = j then aesop
    else
    simp only [h, ↓reduceIte, ite_eq_right_iff, and_imp]
    intro h1 h2
    have : i = j := by
      have : (⟨i.divNat, i.modNat⟩ : Fin n × Fin m) = ⟨j.divNat, j.modNat⟩ := Prod.ext h1 h2
      apply_fun finProdFinEquiv at this
      rw [show ⟨i.divNat, i.modNat⟩ = finProdFinEquiv.symm i by rfl,
        show ⟨j.divNat, _⟩ = finProdFinEquiv.symm j by rfl,
        finProdFinEquiv.apply_symm_apply, finProdFinEquiv.apply_symm_apply] at this
      exact this
    tauto
}

def trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, iso1⟩ := hAB
  obtain ⟨p, q, iso2⟩ := hBC
  refine ⟨⟨p * n, m * q,
    matrix_eqv' _ _ _ |>.symm.trans $ Matrix.compAlgEquiv _ _ _ _|>.symm.trans $
      iso1.mapMatrix (m := Fin p)|>.trans $ Matrix.compAlgEquiv _ _ _ _|>.trans $ ?_⟩⟩
  exact Matrix.reindexAlgEquiv K B (.prodComm (Fin p) (Fin m))|>.trans $
    Matrix.compAlgEquiv _ _ _ _|>.symm.trans $ iso2.mapMatrix.trans $
    Matrix.compAlgEquiv _ _ _ _|>.trans $ matrix_eqv' _ _ _

lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B := by
  exact ⟨⟨1, 1, h.mapMatrix (m := (Fin 1))⟩⟩

theorem Braur_is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

namespace BrauerGroup

def CSA_Setoid : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.Braur_is_eqv

def mul (A B : CSA K) : CSA K where
  carrier := A ⊗[K] B
  fin_dim := Module.Finite.tensorProduct K A B

def is_fin_dim_of_mop (A : Type*) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    FiniteDimensional K Aᵐᵒᵖ := by
  have f:= MulOpposite.opLinearEquiv K (M:= A)
  exact Module.Finite.of_surjective (M:= A) (N:= Aᵐᵒᵖ) f (LinearEquiv.surjective _)

instance inv (A : CSA K) : CSA K where
  carrier := Aᵐᵒᵖ
  fin_dim := is_fin_dim_of_mop A

def one_in (n : ℕ) [hn : NeZero n] : CSA K := ⟨Matrix (Fin n) (Fin n) K⟩

def one_in' : CSA K := ⟨K⟩

def one_mul_in (n : ℕ) [hn : NeZero n] (A : CSA K) : CSA K :=
  ⟨A ⊗[K] (Matrix (Fin n) (Fin n) K)⟩

def mul_one_in (n : ℕ) [hn : NeZero n] (A : CSA K) : CSA K :=
  ⟨(Matrix (Fin n) (Fin n) K) ⊗[K] A⟩

def eqv_in (A : CSA K) (A' : Type*) [Ring A'] [Algebra K A'] (e : A ≃ₐ[K] A'): CSA K where
  carrier := A'
  isCentral := AlgEquiv.isCentral e
  isSimple := ⟨TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv.symm |>.isSimpleOrder⟩
  fin_dim := LinearEquiv.finiteDimensional e.toLinearEquiv

def matrix_A (n : ℕ) [hn : NeZero n] (A : CSA K) : CSA K :=
  eqv_in (one_mul_in n A) (Matrix (Fin n) (Fin n) A) $
    by unfold one_mul_in ; exact matrixEquivTensor (Fin n) K A|>.symm

def dim_1 (R : Type*) [Ring R] [Algebra K R]: Algebra K (Matrix (Fin 1) (Fin 1) R) where
  algebraMap := {
    toFun k := Matrix.diagonal (λ _ => (Algebra.ofId K R) k)
    map_one' := by simp only [map_one, Matrix.diagonal_one]
    map_mul' := by simp only [map_mul, Matrix.diagonal_mul_diagonal, implies_true]
    map_zero' := by simp only [map_zero, Matrix.diagonal_zero]
    map_add' := by simp only [map_add, Matrix.diagonal_add, implies_true]
  }
  commutes' r m := by ext i j; fin_cases i; fin_cases j; simp only [RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Fin.zero_eta, Fin.isValue, Matrix.diagonal_mul,
    Matrix.mul_diagonal]; exact Algebra.commutes r (m 0 0)
  smul_def' r m := by ext i j; fin_cases i; fin_cases j; simp only [Fin.zero_eta, Fin.isValue,
    Matrix.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_mul,
    Algebra.smul_def]; rfl

def dim_one_iso (R : Type*) [Ring R] [Algebra K R]: (Matrix (Fin 1) (Fin 1) R) ≃ₐ[K] R where
  toFun m := m 0 0
  invFun r := Matrix.diagonal (λ _ => r)
  left_inv m := by ext i j; fin_cases i; fin_cases j; simp only [Fin.isValue, Fin.zero_eta,
    Matrix.diagonal_apply_eq]
  right_inv r := by simp only [Fin.isValue, Matrix.diagonal_apply_eq]
  map_mul' m n := by
    simp only [Fin.isValue, Matrix.mul_apply]
    exact Fin.sum_univ_one fun i ↦ m 0 i * n i 0
  map_add' m n := by simp only [Fin.isValue, Matrix.add_apply]
  commutes' r := by
    simp only [Fin.isValue, Algebra.algebraMap_eq_smul_one']
    rw [Matrix.smul_apply]; rfl

open IsBrauerEquivalent
-- def Matrix.swapAlgEquiv (n m : ℕ) (A : Type*) [Ring A] [Algebra K A]:
--     Matrix (Fin n × Fin m) (Fin n × Fin m) A ≃ₐ[K] Matrix (Fin m × Fin n) (Fin m × Fin n) A := by
--   exact Matrix.reindexAlgEquiv K (.prodComm (Fin n) (Fin m))

def matrix_comp (n m : ℕ) (A : Type*) [Ring A] [Algebra K A]:
    Matrix (Fin n) (Fin n) (Matrix (Fin m) (Fin m) A) ≃ₐ[K]
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) :=
  Matrix.compAlgEquiv _ _ _ _|>.trans $ Matrix.reindexAlgEquiv _ _ (.prodComm _ _) |>.trans $
    Matrix.compAlgEquiv _ _ _ _|>.symm

theorem eqv_mat (A : CSA K) (n : ℕ) [hn : NeZero n]: IsBrauerEquivalent A (matrix_A n A) := by
  refine ⟨⟨n, 1, ?_⟩⟩
  unfold matrix_A one_mul_in eqv_in
  exact dim_one_iso _ |>.symm

def matrixEquivForward (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m K ⊗[K] Matrix n n K →ₐ[K] Matrix (m × n) (m × n) K :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.lift Matrix.kroneckerBilinear)
    (fun _ _ _ _ => Matrix.mul_kronecker_mul _ _ _ _)
    (Matrix.one_kronecker_one (α := K))

open scoped Kronecker in
theorem matrixEquivForward_tmul (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m m K) (N : Matrix n n K) : matrixEquivForward m n (M ⊗ₜ N) = M ⊗ₖ N := rfl

lemma matrixEquivForward_surjective
    (n m : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Function.Surjective $ matrixEquivForward (K := K) m n := by
  intro x
  rw [Matrix.matrix_eq_sum_stdBasisMatrix x]
  suffices H :
      ∀ (i j : m × n), ∃ a, (matrixEquivForward m n) a = Matrix.stdBasisMatrix i j (x i j) by
    choose a ha using H
    use ∑ i : m × n, ∑ j : m × n, a i j
    rw [map_sum]
    simp_rw [map_sum]
    simp_rw [ha]

  intro i j
  rw [show Matrix.stdBasisMatrix i j (x i j) = (x i j) • Matrix.stdBasisMatrix i j 1 by
    rw [Matrix.smul_stdBasisMatrix, Algebra.smul_def,  mul_one]
    rfl]
  use (x i j) • ((Matrix.stdBasisMatrix i.1 j.1 1) ⊗ₜ (Matrix.stdBasisMatrix i.2 j.2 1))
  rw [_root_.map_smul (f := (matrixEquivForward (K := K) m n)) (x i j)]
  congr 1
  simp only [matrixEquivForward, Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply,
    TensorProduct.lift.tmul]
  ext a b
  erw [Matrix.kroneckerMapBilinear_apply_apply]
  erw [Matrix.kroneckerMap_apply]
  erw [Algebra.coe_lmul_eq_mul]
  rw [LinearMap.mul]
  simp only [LinearMap.mk₂_apply]
  simp only [Matrix.stdBasisMatrix, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · simp only [not_and, ne_eq] at h3
    refine h3 ?_ ?_ |>.elim <;> ext <;> aesop
  · simp only [not_and, ne_eq] at h2
    refine h2 ?_ ?_ |>.elim <;> aesop
  · rfl
  · simp only [not_and, ne_eq] at h1
    refine h1 ?_ ?_ |>.elim <;> aesop
  · rfl


def matrix_eqv (m n : ℕ): (Matrix (Fin m) (Fin m) K) ⊗[K] (Matrix (Fin n) (Fin n) K) ≃ₐ[K]
    Matrix (Fin m × Fin n) (Fin m × Fin n) K :=
  AlgEquiv.ofBijective
    (matrixEquivForward (Fin m) (Fin n)) $ by
    if h : n = 0 ∨ m = 0
    then
      rcases h with h|h <;>
      subst h <;>
      refine ⟨?_, matrixEquivForward_surjective _ _⟩ <;>
      intro x y _ <;>
      apply Subsingleton.elim

    else
    have : Nonempty (Fin n) := ⟨0, by omega⟩
    have : Nonempty (Fin m) := ⟨0, by omega⟩
    apply bijective_of_surj_of_isCentralSimple
    apply matrixEquivForward_surjective


lemma one_mul (n : ℕ) [hn : NeZero n] (A : CSA K) :
    IsBrauerEquivalent A (one_mul_in n A) :=
  ⟨⟨n, 1, AlgEquiv.symm $ (dim_one_iso _).trans $ matrixEquivTensor _ _ _ |>.symm⟩⟩

lemma mul_one (n : ℕ) [hn : NeZero n] (A : CSA K) :
    IsBrauerEquivalent A (mul_one_in n A) :=
  ⟨⟨n, 1, AlgEquiv.symm $ (dim_one_iso _).trans $ AlgEquiv.symm $
    matrixEquivTensor _ _ _ |>.trans $ Algebra.TensorProduct.comm _ _ _⟩⟩


lemma mul_assoc (A B C : CSA K) :
    IsBrauerEquivalent (mul (mul A B) C) (mul A (mul B C)) :=
  IsBrauerEquivalent.iso_to_eqv (K := K) _ _ $ Algebra.TensorProduct.assoc _ _ _ _

def huarongdao (A B C D : Type*) [Ring A] [Ring B] [Ring C] [Ring D] [Algebra K A]
    [Algebra K B] [Algebra K C] [Algebra K D]:
    (A ⊗[K] B) ⊗[K] C ⊗[K] D ≃ₐ[K] (A ⊗[K] C) ⊗[K] B ⊗[K] D := by
  let eq1 := Algebra.TensorProduct.congr (R := K)
    (Algebra.TensorProduct.comm K A B) $ AlgEquiv.refl (A₁ := C ⊗[K] D)
  let eq2 := Algebra.TensorProduct.assoc K B A (C ⊗[K] D)
  let eq3 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := B))
    $ Algebra.TensorProduct.assoc K A C D|>.symm
  let eq4 := Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := B))
    $ Algebra.TensorProduct.comm K (A ⊗[K] C) D
  let eq5 := Algebra.TensorProduct.assoc K B D (A ⊗[K] C)|>.symm
  let eq6 := Algebra.TensorProduct.comm K (B ⊗[K] D) (A ⊗[K] C)
  exact eq1.trans $ eq2.trans $ eq3.trans $ eq4.trans $ eq5.trans eq6

def kroneckerMatrixTensor' (A B: Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (n m : ℕ) :
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K]
      (Matrix (Fin (n*m)) (Fin (n*m)) (A ⊗[K] B)) := by
    have := matrixEquivTensor (Fin n) K A
    refine AlgEquiv.trans (Algebra.TensorProduct.congr (matrixEquivTensor (Fin n) K A)
      $ matrixEquivTensor (Fin m) K B) <| AlgEquiv.trans (huarongdao ..) <| AlgEquiv.trans
      (Algebra.TensorProduct.congr AlgEquiv.refl $ (matrix_eqv ..).trans $ matrix_eqv' ..) ?_
    exact (matrixEquivTensor ..).symm

theorem eqv_tensor_eqv
    (A B C D : CSA K) (hAB : IsBrauerEquivalent A B) (hCD : IsBrauerEquivalent C D) :
    IsBrauerEquivalent (mul A C) (mul B D) := by
  obtain ⟨n, m, e1⟩ := hAB
  obtain ⟨p, q, e2⟩ := hCD
  exact ⟨⟨n * p, m * q, kroneckerMatrixTensor' .. |>.symm.trans <|
    Algebra.TensorProduct.congr e1 e2|>.trans <| kroneckerMatrixTensor' ..⟩⟩

abbrev BrGroup := Quotient $ CSA_Setoid (K := K)

instance Mul: Mul $ BrGroup (K := K) :=
  ⟨Quotient.lift₂ (fun A B ↦ Quotient.mk (CSA_Setoid) $ BrauerGroup.mul A B)
  (by
    simp only [Quotient.eq]
    intro A B C D hAB hCD
    exact eqv_tensor_eqv A C B D hAB hCD)⟩

instance One: One (BrGroup (K := K)) := ⟨Quotient.mk (CSA_Setoid) one_in'⟩

theorem mul_assoc' (A B C : BrGroup (K := K)) : A * B * C = A * (B * C) := by
  induction' A using Quotient.inductionOn' with A
  induction' B using Quotient.inductionOn' with B
  induction' C using Quotient.inductionOn' with C
  apply Quotient.sound; exact mul_assoc _ _ _

lemma mul_inv (A : CSA.{u, u} K) : IsBrauerEquivalent (mul A (inv (K := K) A)) one_in' := by
  unfold mul inv one_in'
  let n := Module.finrank K A
  have hn : NeZero n := by
    constructor
    by_contra! hn
    simp only [n] at hn
    have := Module.finrank_pos_iff (R := K) (M := A) |>.2 inferInstance
    omega
  have := tensor_self_op K A
  exact ⟨⟨1, n, dim_one_iso _|>.trans this⟩⟩

lemma inv_mul (A : CSA.{u, u} K) : IsBrauerEquivalent (mul (inv (K := K) A) A) one_in' := by
  unfold mul inv one_in'
  let n := Module.finrank K A
  have hn : NeZero n := by
    constructor
    by_contra! hn
    simp only [n] at hn
    have := Module.finrank_pos_iff (R := K) (M := A) |>.2 $ inferInstance
    omega
  have := tensor_op_self K A
  exact ⟨⟨1, n, dim_one_iso _|>.trans this⟩⟩

variable (K R : Type*) [CommSemiring K] [Semiring R] [Algebra K R] in
open BigOperators Matrix MulOpposite in
/-- Mn(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ -/
def matrixEquivMatrixMop_algebra (n : ℕ):
    Matrix (Fin n) (Fin n) Rᵐᵒᵖ ≃ₐ[K] (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ where
  toFun := fun M => op (M.transpose.map (fun d => d.unop))
  invFun := fun M => M.unop.transpose.map (fun d => op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective $ by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop
  commutes' k := by
    simp only [MulOpposite.algebraMap_apply, op_inj]; ext i j
    simp only [map_apply, transpose_apply, algebraMap_matrix_apply]
    if h : i = j then simp only [h, ↓reduceIte, MulOpposite.algebraMap_apply, unop_op]
    else simp only [MulOpposite.algebraMap_apply, h, ↓reduceIte, unop_eq_zero_iff, ite_eq_right_iff,
      op_eq_zero_iff]; tauto

lemma inv_eqv (A B: CSA K) (hAB : IsBrauerEquivalent A B):
    IsBrauerEquivalent (inv (K := K) A) (inv (K := K) B) := by
  unfold inv
  obtain ⟨n, m, iso⟩ := hAB
  refine ⟨⟨n, m, (matrixEquivMatrixMop_algebra _ _ _).trans $
    (AlgEquiv.op iso).trans (matrixEquivMatrixMop_algebra _ _ _).symm⟩⟩

instance Inv: Inv (BrGroup (K := K)) := ⟨Quotient.lift (fun A ↦ Quotient.mk (CSA_Setoid) $ inv A)
(by
  intro A B hAB
  change IsBrauerEquivalent _ _ at hAB
  simp only [Quotient.eq]; change IsBrauerEquivalent _ _
  exact inv_eqv (K := K) A B hAB)⟩

theorem mul_left_inv' (A : BrGroup (K := K)) : A⁻¹ * A = 1 := by
  induction' A using Quotient.inductionOn' with A
  change _ = Quotient.mk'' one_in'
  apply Quotient.sound ; exact inv_mul A

theorem one_mul' (A : BrGroup (K := K)) : 1 * A = A := by
  induction' A using Quotient.inductionOn' with A
  change Quotient.mk'' one_in' * _ = _ ; apply Quotient.sound
  exact (mul_one 1 A).trans (iso_to_eqv _ _ (Algebra.TensorProduct.congr
    (dim_one_iso _) AlgEquiv.refl))|>.symm

theorem mul_one' (A : BrGroup (K := K)) : A * 1 = A := by
  induction' A using Quotient.inductionOn' with A
  change _ * Quotient.mk'' one_in' = _ ; apply Quotient.sound
  exact (one_mul 1 A).trans (iso_to_eqv _ _ (Algebra.TensorProduct.congr
    AlgEquiv.refl (dim_one_iso _)))|>.symm

instance Bruaer_Group : Group (BrGroup (K := K)) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := mul_left_inv'

lemma Alg_closed_equiv_one [IsAlgClosed K]: ∀(A : CSA K), IsBrauerEquivalent A one_in' := by
  intro A
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed K A
  exact ⟨⟨1, n, dim_one_iso A|>.trans iso⟩⟩

lemma Alg_closed_eq_one [IsAlgClosed K]: ∀(A : BrGroup (K := K)), A = 1 := by
  intro A ; induction' A using Quotient.inductionOn' with A
  change _ = Quotient.mk'' one_in' ; apply Quotient.sound
  change IsBrauerEquivalent _ _; exact Alg_closed_equiv_one A

instance [IsAlgClosed K]: Unique (BrGroup (K := K)) where
  default := 1
  uniq := Alg_closed_eq_one

theorem Alg_closed_Brauer_trivial [IsAlgClosed K]: (⊤ : Subgroup BrGroup) =
    (⊥ : Subgroup $ BrGroup (K := K)) :=
  Subgroup.ext fun _ => ⟨fun _ ↦ Alg_closed_eq_one _, fun _ ↦ ⟨⟩⟩

end BrauerGroup

namespace BrauerGroupHom

open BrauerGroup
variable {E : Type u} [Field E] [Algebra K E]

namespace someEquivs

variable (A B : Type u) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
variable (m : ℕ)

def e1 :
    Matrix (Fin m) (Fin m) (E ⊗[K] A) ≃ₐ[E]
    (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E :=
  matrixEquivTensor (Fin m) E (E ⊗[K] A)

def e2 :
    (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E ≃ₐ[E]
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) :=
  Algebra.TensorProduct.congr AlgEquiv.refl $
    { __ := matrixEquivTensor (Fin m) K E
      commutes' := fun e => by
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          matrixEquivTensor_apply, Fintype.sum_prod_type,
          Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
        simp_rw [Matrix.algebraMap_eq_diagonal]
        simp_rw [Matrix.diagonal_apply]
        simp only [Pi.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
        rw [show
          ∑ x : Fin m, ∑ y : Fin m,
            (if x = y then e else 0) ⊗ₜ[K] Matrix.stdBasisMatrix x y (1 : K) =
          ∑ x : Fin m, e ⊗ₜ[K] Matrix.stdBasisMatrix x x 1 by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [show e ⊗ₜ[K] Matrix.stdBasisMatrix x x (1 : K) =
              (if x = x then e else 0) ⊗ₜ Matrix.stdBasisMatrix x x (1 : K) by aesop]
            apply Finset.sum_eq_single
            · aesop
            · aesop]
        rw [← TensorProduct.tmul_sum]
        congr 1
        ext i j
        rw [Matrix.sum_apply]
        by_cases h : i = j
        · subst h; simp [Matrix.stdBasisMatrix]
        · rw [Matrix.one_apply_ne h]
          apply Finset.sum_eq_zero
          intros k
          simp only [Finset.mem_univ, Matrix.stdBasisMatrix, Matrix.of_apply, ite_eq_right_iff,
            one_ne_zero, imp_false, not_and, forall_const]
          rintro rfl
          exact h }

def e3Aux0 : E ⊗[K] A →ₐ[E] E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K :=
  AlgHom.comp
    { (Algebra.TensorProduct.assoc K E A (Matrix (Fin m) (Fin m) K)).toAlgHom  with
      commutes' := fun e => by
        simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom,
          RingHom.toMonoidHom_eq_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id,
          RingHom.id_apply, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          RingHom.coe_coe, Algebra.TensorProduct.assoc_tmul]
        rfl }
    (Algebra.TensorProduct.includeLeft : E ⊗[K] A →ₐ[E] (E ⊗[K] A) ⊗[K] Matrix (Fin m) (Fin m) K)

def e3Aux10 : (E ⊗[K] Matrix (Fin m) (Fin m) K) ⊗[K] A ≃ₐ[K]
    E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K :=
  (Algebra.TensorProduct.assoc K E (Matrix (Fin m) (Fin m) K) A).trans $
    Algebra.TensorProduct.congr AlgEquiv.refl $ Algebra.TensorProduct.comm _ _ _

def e3Aux1 : E ⊗[K] Matrix (Fin m) (Fin m) K →ₐ[E] E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K :=
  AlgHom.comp
    { (e3Aux10 (K := K) (E := E) A m).toAlgHom with
      commutes' := fun e => by
        simp only [AlgEquiv.toAlgHom_eq_coe, e3Aux10, AlgHom.toRingHom_eq_coe,
          AlgEquiv.toAlgHom_toRingHom, RingHom.toMonoidHom_eq_coe,
          Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
          OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
          AlgEquiv.trans_apply, Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.congr_apply,
          AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          AlgHom.coe_coe, Algebra.TensorProduct.comm_tmul]
        rfl }
    (Algebra.TensorProduct.includeLeft : E ⊗[K] Matrix (Fin m) (Fin m) K →ₐ[E]
      (E ⊗[K] Matrix (Fin m) (Fin m) K) ⊗[K] A)

-- instance e3Aux2 [hm : NeZero m] [Algebra.IsCentral K A] [IsSimpleRing A] :
--     Algebra.IsCentral E ((E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K)) :=
--   inferInstance

-- instance e3Aux2' [hm : NeZero m] [Algebra.IsCentral K A] [IsSimpleRing A] :
--     IsSimpleRing ((E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K)) :=
--   inferInstance

-- instance e3Aux2''  [hm : NeZero m] [Algebra.IsCentral K A] [IsSimpleRing A] :
--     Algebra.IsCentral E (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) :=
--   inferInstance

-- instance e3Aux2'''  [hm : NeZero m] [Algebra.IsCentral K A] [IsSimpleRing A] :
--     IsSimpleRing (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) :=
--   inferInstance

lemma e3Aux3 (hm : m = 0) : Subsingleton ((E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K)) := by
  suffices ∀ a : (E ⊗[K] A) ⊗[E] E ⊗[K] Matrix (Fin m) (Fin m) K, a = 0 by
    refine ⟨fun a b => ?_⟩
    rw [this a, this b]
  subst hm
  intro x
  induction' x using TensorProduct.induction_on with e a e a he ha
  · rfl
  · induction' a using TensorProduct.induction_on with e' mat _ _ hx hy
    · simp
    · rw [show mat = 0 from Subsingleton.elim _ _]
      simp
    · rw [TensorProduct.tmul_add, hx, hy, add_zero]
  · rw [he, ha, zero_add]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 160000 in
def e3Aux4 : (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) →ₐ[E]
      E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
    (Algebra.TensorProduct.lift
        (e3Aux0 (K := K) (E := E) A m)
        (e3Aux1 (K := K) (E := E) A m) fun x y => by
      show _ = _
      simp only [e3Aux0, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
        AlgEquiv.toAlgHom_toRingHom, AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_coe,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, e3Aux1, e3Aux10,
        AlgEquiv.coe_trans, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom]
      induction' x using TensorProduct.induction_on with e a e a he ha
      · simp only [TensorProduct.zero_tmul, map_zero] ; rw [zero_mul
          (M₀ := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K), mul_zero
          (M₀ := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)]
      · simp only [Algebra.TensorProduct.assoc_tmul]
        induction' y using TensorProduct.induction_on with x y x y hx hy
        · simp only [TensorProduct.zero_tmul]
          trans 0
          · convert mul_zero (M₀ := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K) _
          · symm ; convert zero_mul (M₀ := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K) _
        · simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, AlgHom.coe_coe, Algebra.TensorProduct.comm_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
          rw [mul_comm]
        · haveI := Distrib.leftDistribClass (E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)
          haveI := Distrib.rightDistribClass (E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)
          convert congr($hx + $hy) using 1
          · rw [← mul_add (R := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)]
            congr
            rw [TensorProduct.add_tmul]
            exact map_add _ _ _
          · rw [← add_mul (R := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)]
            congr
            rw [TensorProduct.add_tmul]
            exact map_add _ _ _
      · haveI := Distrib.leftDistribClass (E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)
        haveI := Distrib.rightDistribClass (E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)
        simp only [TensorProduct.add_tmul, map_add,
          add_mul (R := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K), he, ha,
          mul_add (R := E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)]
      )

-- instance : AddHomClass ((E ⊗[K] A) ⊗[E] E ⊗[K] Matrix (Fin m) (Fin m) K →ₐ[E]
--     E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)
--     ((E ⊗[K] A) ⊗[E] E ⊗[K] Matrix (Fin m) (Fin m) K) (E ⊗[K] A ⊗[K] Matrix (Fin m) (Fin m) K)
--     where
--       map_add f := fun x y ↦ by
--         change f.toRingHom _ = f.toRingHom _ + f.toRingHom _
--         exact RingHom.map_add f.toRingHom x y

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
lemma e3Aux5 : Function.Surjective (e3Aux4 (K := K) (E := E) A m) := by
  intro x
  induction' x using TensorProduct.induction_on with e a e a he ha
  · refine ⟨0, ?_⟩
    rfl
  · induction' a using TensorProduct.induction_on with a m a m h₁ h₂
    · refine ⟨0, ?_⟩
      simp only [TensorProduct.tmul_zero]; rfl
    · refine ⟨(e ⊗ₜ[K] a) ⊗ₜ[E] (1 : E) ⊗ₜ[K] m, ?_⟩
      delta e3Aux4
      rw [Algebra.TensorProduct.lift_tmul]
      simp only [e3Aux0, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
        AlgEquiv.toAlgHom_toRingHom, AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_coe,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.assoc_tmul, e3Aux1, e3Aux10, AlgEquiv.coe_trans,
        Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_coe, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    · rcases h₂ with ⟨m, h₂⟩
      rcases h₁ with ⟨a, h₁⟩
      refine ⟨a + m, ?_⟩
      convert congr($h₁+ $h₂) using 1
      · exact map_add (f := e3Aux4 (K := K) (E := E) A _) _ _
      · rw [TensorProduct.tmul_add]
  · rcases he with ⟨e, rfl⟩
    rcases ha with ⟨a, rfl⟩
    refine ⟨e + a, ?_⟩
    exact map_add (f := e3Aux4 (K := K) (E := E) A _) _ _

def e3 [Algebra.IsCentral K A] [csa_A : IsSimpleRing A] :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  AlgEquiv.ofBijective (e3Aux4 (K := K) (E := E) A m) $ by
      if hm : m = 0
      then
        haveI := e3Aux3 (K := K) (E := E) A m hm
        refine ⟨fun _ _ _ => Subsingleton.elim _ _, e3Aux5 (K := K) (E := E) A m⟩
      else
        have : NeZero m := ⟨hm⟩
        letI r1 : Ring ((E ⊗[K] A) ⊗[E] E ⊗[K] Matrix (Fin m) (Fin m) K) := inferInstance
        letI r2 : Ring (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) := inferInstance

        apply bijective_of_surj_of_isCentralSimple E _ _ _ $ e3Aux5 (K := K) (E := E) A m

def e4 :
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (Matrix (Fin m) (Fin m) A) :=
  Algebra.TensorProduct.congr AlgEquiv.refl $ (matrixEquivTensor (Fin m) K A).symm

def e5 (e : A ≃ₐ[K] B) : (E ⊗[K] A) ≃ₐ[E] (E ⊗[K] B) :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

set_option maxHeartbeats 800000 in
def e6Aux0 :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) →ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift
      { toFun := fun e => e ⊗ₜ[K] 1 ⊗ₜ 1
        map_one' := rfl
        map_mul' := fun e e' => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun e e' => by simp [TensorProduct.add_tmul]
        commutes' := fun e => rfl }
      { toFun := fun a => 1 ⊗ₜ[K] a ⊗ₜ 1
        map_one' := rfl
        map_mul' := fun _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun _ _ => by simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
        commutes' := fun k => by
          simp only [Algebra.TensorProduct.algebraMap_apply]
          rw [show (algebraMap K A) k ⊗ₜ[K] (1 : B) = k • (1 : A ⊗[K] B) by
            rw [Algebra.algebraMap_eq_smul_one]
            rw [← TensorProduct.smul_tmul']
            rfl]
          rw [TensorProduct.tmul_smul]
          rw [Algebra.smul_def (A := E ⊗[K] A ⊗[K] B)]
          convert _root_.mul_one _ } fun e a =>
            show (_ ⊗ₜ[K] _) * (_ ⊗ₜ[K] _) = (_ ⊗ₜ[K] _) * (_ ⊗ₜ[K] _) by simp)
    (Algebra.TensorProduct.lift
      { toFun := fun e => e ⊗ₜ[K] 1 ⊗ₜ 1
        map_one' := rfl
        map_mul' := fun e e' => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun e e' => by simp [TensorProduct.add_tmul]
        commutes' := fun e => rfl }
      { toFun := fun b => 1 ⊗ₜ[K] 1 ⊗ₜ b
        map_one' := rfl
        map_mul' := fun _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun _ _ => by simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
        commutes' := fun k => by
          simp only [Algebra.TensorProduct.algebraMap_apply]
          rw [show (1 : A) ⊗ₜ[K] (algebraMap K B) k = k • (1 : A ⊗[K] B) by
            rw [Algebra.algebraMap_eq_smul_one]
            rw [TensorProduct.tmul_smul]
            rfl]
          rw [TensorProduct.tmul_smul]
          rw [Algebra.smul_def (A := E ⊗[K] A ⊗[K] B)]
          convert _root_.mul_one _ } fun e b => show (_ ⊗ₜ _) * (_ ⊗ₜ _) = (_ ⊗ₜ _) * (_ ⊗ₜ _) by simp)
            fun x y => show _ = _ by
            induction' x using TensorProduct.induction_on with e a x x' hx hx'
            · simp only [map_zero, zero_mul, mul_zero]
            · simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk,
              MonoidHom.coe_mk, OneHom.coe_mk, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
              _root_.one_mul]
              induction' y using TensorProduct.induction_on with e' b y y' hy hy'
              · simp only [map_zero, mul_zero, zero_mul]
              · simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk]
                change (_ ⊗ₜ _) * (_ ⊗ₜ _) * ((_ ⊗ₜ _) * (_ ⊗ₜ _)) = (_ ⊗ₜ _) * (_ ⊗ₜ _) * ((_ ⊗ₜ _) * (_ ⊗ₜ _))
                simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
                rw [mul_comm]
              · simp only [map_add, mul_add, hy, hy', add_mul]
            · simp only [map_add, mul_add, hx, hx', add_mul]

set_option synthInstance.maxHeartbeats 40000 in
def e6 [Algebra.IsCentral K A] [csa_A : IsSimpleRing A]
    [Algebra.IsCentral K B] [csa_B : IsSimpleRing B] :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  AlgEquiv.ofBijective (e6Aux0 (K := K) (E := E) A B) $ by
    apply bijective_of_surj_of_isCentralSimple E _ _ _
    intro x
    induction' x using TensorProduct.induction_on with e a x y hx hy
    · refine ⟨0, ?_⟩
      rfl
    · induction' a using TensorProduct.induction_on with a b a a' ha ha'
      · refine ⟨0, ?_⟩
        rw [TensorProduct.tmul_zero]
        rfl
      · refine ⟨(e ⊗ₜ a) ⊗ₜ[E] (1 ⊗ₜ b), ?_⟩
        simp only [e6Aux0, Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
          _root_.one_mul, map_one];
        change e ⊗ₜ[K] 1 ⊗ₜ[K] 1 * 1 ⊗ₜ[K] a ⊗ₜ[K] 1 * 1 ⊗ₜ[K] 1 ⊗ₜ[K] b = _
        simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
      · rcases ha with ⟨aa, haa⟩
        rcases ha' with ⟨aa', haa'⟩
        refine ⟨aa + aa', ?_⟩
        rw [_root_.map_add (f := (e6Aux0 (K := K) (E := E) A B)), haa, haa', TensorProduct.tmul_add]
    · rcases hx with ⟨x, rfl⟩
      rcases hy with ⟨y, rfl⟩
      refine ⟨x + y, ?_⟩
      exact map_add (f := (e6Aux0 (K := K) (E := E) A B)) _ _

def e7 : E ≃ₐ[E] (E ⊗[K] K) := AlgEquiv.symm $ Algebra.TensorProduct.rid _ _ _

end someEquivs

section Q_to_C

abbrev BaseChange : BrGroup (K := K) →* BrGroup (K := E) where
  toFun :=
    Quotient.map'
    (fun A =>
    { carrier := E ⊗[K] A
      ring := inferInstance
      algebra := inferInstance
      fin_dim := inferInstance }) $ fun A B => Nonempty.map $ by
          rintro ⟨m, n, e⟩
          exact ⟨m, n, (someEquivs.e1 A m).trans $ (someEquivs.e2 A m).trans $
            (someEquivs.e3 A m).trans $ (someEquivs.e4 A m).trans $ AlgEquiv.symm $
            (someEquivs.e1 B n).trans $ (someEquivs.e2 B n).trans $
            (someEquivs.e3 B n).trans $ (someEquivs.e4 B n).trans $ someEquivs.e5 _ _ e.symm⟩
  map_one' := by
    erw [Quotient.eq'']
    letI : Field one_in'.carrier := inferInstanceAs <| Field K
    letI : Algebra one_in'.carrier E := inferInstanceAs <| Algebra K E
    exact ⟨1, 1, (dim_one_iso _).trans $ AlgEquiv.symm $ (dim_one_iso _).trans <| someEquivs.e7⟩
  map_mul' := by
    intro x y
    induction' x using Quotient.inductionOn' with A
    induction' y using Quotient.inductionOn' with B
    simp only [Quotient.map'_mk'']
    erw [Quotient.map'_mk'']
    erw [Quotient.eq'']
    exact ⟨1, 1, (dim_one_iso _).trans $ AlgEquiv.symm $ (dim_one_iso _).trans <|
      someEquivs.e6 A B⟩

abbrev BaseChange_Q_to_C := BaseChange (K := ℚ) (E := ℂ)

lemma BaseChange_Q_to_C_eq_one : BaseChange_Q_to_C = 1 := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  ext A ; simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply]
  induction' A using Quotient.inductionOn' with A ;
  simp only [Quotient.map'_mk'']; apply Quotient.sound
  exact BrauerGroup.Alg_closed_equiv_one _

end Q_to_C

instance IsAbelBrauer : CommGroup (BrGroup (K := K)) := {
  __ := BrauerGroup.Bruaer_Group
  mul_comm := fun A B ↦ by
    induction' A using Quotient.inductionOn' with A
    induction' B using Quotient.inductionOn' with B
    apply Quotient.sound'
    change IsBrauerEquivalent _ _
    unfold mul
    exact ⟨⟨1, 1, AlgEquiv.mapMatrix $ Algebra.TensorProduct.comm ..⟩⟩
}

open CategoryTheory

def baseChange_idem.Aux (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] (A : CSA F) :
    E ⊗[K] K ⊗[F] A ≃ₗ[E] (E ⊗[F] A.carrier) :=
  have : SMulCommClass F K E :=
    { smul_comm := fun a b c => by
        rw [Algebra.smul_def, Algebra.smul_def, ← _root_.mul_assoc, mul_comm (algebraMap _ _ a),
          Algebra.smul_def, Algebra.smul_def, _root_.mul_assoc] }
  (TensorProduct.AlgebraTensorModule.assoc F K E E K A).symm ≪≫ₗ
  TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.AlgebraTensorModule.rid _ _ _) (LinearEquiv.refl _ _)

set_option maxHeartbeats 400000 in
def baseChange_idem.Aux' (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] (A : CSA F) :
    E ⊗[K] K ⊗[F] A ≃ₐ[E] (E ⊗[F] A.carrier) :=
  have : SMulCommClass F K E :=
    { smul_comm := fun a b c => by
        rw [Algebra.smul_def, Algebra.smul_def, ← _root_.mul_assoc, mul_comm (algebraMap _ _ a),
          Algebra.smul_def, Algebra.smul_def, _root_.mul_assoc] }
  AlgEquiv.ofLinearEquiv (baseChange_idem.Aux F K E A)
    (by simp [baseChange_idem.Aux,Algebra.TensorProduct.one_def])
    (by
      intro x y
      induction x using TensorProduct.induction_on -- with e a e a he ha

      · rw [zero_mul, (baseChange_idem.Aux F K E A).map_zero, zero_mul]
      · induction y using TensorProduct.induction_on -- with f b e a he ha
        · rw [mul_zero, (baseChange_idem.Aux F K E A).map_zero, mul_zero]
        · rename_i x1 y1 x2 y2
          simp only [Aux, Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.trans_apply]
          set f := (TensorProduct.AlgebraTensorModule.congr
            (TensorProduct.AlgebraTensorModule.rid K E E) (LinearEquiv.refl F A))
          set g := (TensorProduct.AlgebraTensorModule.assoc F K E E K A.carrier).symm
          change f (g _) = _
          induction y1 using TensorProduct.induction_on -- with f b e a he ha
          · rw [zero_mul, TensorProduct.tmul_zero, g.map_zero,
              f.map_zero, TensorProduct.tmul_zero,
              g.map_zero, f.map_zero, zero_mul]
          · induction y2 using TensorProduct.induction_on -- with f b e a he ha
            · rw [mul_zero, TensorProduct.tmul_zero, TensorProduct.tmul_zero,
                g.map_zero, f.map_zero, mul_zero]
            · simp only [Algebra.TensorProduct.tmul_mul_tmul,
              TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
              TensorProduct.AlgebraTensorModule.congr_tmul,
              TensorProduct.AlgebraTensorModule.rid_tmul, LinearEquiv.refl_apply,
              Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, f, g]
              rw [mul_comm]
            · rename_i a b c d h
              simp only [mul_add, TensorProduct.tmul_add, g.map_add, f.map_add, d, h]
          · rename_i a b c
            simp only [add_mul, TensorProduct.tmul_add, g.map_add, f.map_add, b, c]
        · rename_i a b
          rw [mul_add, (Aux F K E A).map_add, a, b,
            (Aux F K E A).map_add, mul_add]
      · rename_i a b c d
        simp only [add_mul, (Aux F K E A).map_add, c, d])

lemma baseChange_idem (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] :
    BrauerGroupHom.BaseChange (K := F) (E := E) =
    (BrauerGroupHom.BaseChange (K := K) (E := E)).comp
    BrauerGroupHom.BaseChange := by
  ext A
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply]
  induction' A using Quotient.inductionOn' with A
  simp only [Quotient.map'_mk'', Quotient.eq'']
  exact ⟨⟨1, 1, AlgEquiv.mapMatrix <| AlgEquiv.symm <| baseChange_idem.Aux' ..⟩⟩

def Br : FieldCat ⥤ CommGrp where
  obj F := .of $ BrGroup (K := F)
  map {F K} f := ConcreteCategory.ofHom <|
    @BrauerGroupHom.BaseChange F _ K _ (RingHom.toAlgebra f.hom)
  map_id F := by
    ext A
    simp only [CommGrp.coe_of, FieldCat.hom_id, CommGrp.hom_ofHom, MonoidHom.coe_mk, OneHom.coe_mk,
      CommGrp.hom_id, MonoidHom.id_apply]
    simp only [CommGrp.coe_of] at A
    induction' A using Quotient.inductionOn' with A
    simp only [Quotient.map'_mk'', Quotient.eq'']
    change IsBrauerEquivalent _ _
    exact ⟨1, 1, AlgEquiv.mapMatrix $ Algebra.TensorProduct.lid _ _⟩
  map_comp {F K E} f g := by
    simp only [FieldCat.hom_comp]
    ext : 1
    simp only [CommGrp.hom_ofHom, CommGrp.hom_comp]
    apply (config := { allowSynthFailures := true }) baseChange_idem
    letI : Algebra F E := RingHom.toAlgebra (f ≫ g).hom
    letI : Algebra F K := RingHom.toAlgebra f.hom
    letI : Algebra K E := RingHom.toAlgebra g.hom
    exact IsScalarTower.of_algebraMap_smul (R := F) (A := K) (M := E) fun r ↦ congrFun rfl

end BrauerGroupHom
