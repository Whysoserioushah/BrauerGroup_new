import BrauerGroup.CentralSimple
import BrauerGroup.Composition
import Mathlib.LinearAlgebra.Matrix.ToLin


suppress_compilation
universe u v v₁ v₂ w

variable (K : Type u) [Field K]
variable (A B : Type v) [Ring A] [Ring B] [Algebra K A] [Algebra K B]

open scoped TensorProduct BigOperators

lemma bijective_of_dim_eq_of_isCentralSimple
    [csa_source : IsCentralSimple K A]
    [fin_source : FiniteDimensional K A]
    [fin_target : FiniteDimensional K B]
    (f : A →ₐ[K] B) (h : FiniteDimensional.finrank K A = FiniteDimensional.finrank K B) :
    Function.Bijective f := by
  obtain hA|hA := subsingleton_or_nontrivial A
  · have eq1 : FiniteDimensional.finrank K A = 0 := by
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
  · have := RingCon.IsSimpleOrder.iff_eq_zero_or_injective A |>.1 csa_source.2 f.toRingHom
    rcases this with (H|H)
    · have : (1 : A) ∈ RingCon.ker f.toRingHom := H ▸ ⟨⟩
      simp only [AlgHom.toRingHom_eq_coe, RingCon.mem_ker, map_one] at this
      have hmm : Nontrivial B := by
        let e := LinearEquiv.ofFinrankEq _ _ h
        exact Equiv.nontrivial e.symm.toEquiv

      exact one_ne_zero this |>.elim
    · refine ⟨H, ?_⟩
      change Function.Surjective f.toLinearMap
      have := f.toLinearMap.finrank_range_add_finrank_ker
      rw [show FiniteDimensional.finrank K ↥(LinearMap.ker f.toLinearMap) = 0 by
        rw [finrank_zero_iff_forall_zero]
        rintro ⟨x, hx⟩
        rw [LinearMap.ker_eq_bot (f := f.toLinearMap) |>.2 H] at hx
        ext
        exact hx, add_zero, h] at this
      rw [← LinearMap.range_eq_top]

      apply Submodule.eq_top_of_finrank_eq
      exact this

lemma bijective_of_surj_of_isCentralSimple
    [csa_source : IsCentralSimple K A]
    (f : A →ₐ[K] B) [Nontrivial B] (h : Function.Surjective f) :
    Function.Bijective f :=
  ⟨by
    letI : IsSimpleOrder (RingCon A) := csa_source.2
    haveI : Nontrivial A := inferInstance
    have := RingCon.IsSimpleOrder.iff_eq_zero_or_injective A |>.1 inferInstance f.toRingHom
    refine this.resolve_left ?_
    intro H
    have : (1 : A) ∈ (⊤ : RingCon A) := ⟨⟩
    rw [← H] at this
    simp only [AlgHom.toRingHom_eq_coe, RingCon.mem_ker, map_one] at this
    have eq1 : (1 : B) ≠ 0 := one_ne_zero
    exact eq1 this |>.elim, h⟩

instance tensor_CSA_is_CSA [Small.{v, u} K ] [hA: IsCentralSimple K A] [hB: IsCentralSimple K B] :
    IsCentralSimple K (A ⊗[K] B) where
   is_central := IsCentralSimple.TensorProduct.isCentral K A B hA.is_central hB.is_central
   is_simple := by haveI := hA.is_simple; exact IsCentralSimple.TensorProduct.simple K A B

lemma CSA_op_is_CSA (hA: IsCentralSimple K A):
    IsCentralSimple K Aᵐᵒᵖ where
  is_central z hz:= by
    let z': A := z.unop
    have hz' : ∀ (x : A), x * z' = z' * x := by
      rw [Subalgebra.mem_center_iff] at hz
      intro x; specialize hz (MulOpposite.op x)
      have z'_eq : MulOpposite.op z'= z := rfl
      rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
      have : (MulOpposite.op (z' * x)).unop = z' * x := rfl
      simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
          MulOpposite.unop_op, z']
    obtain ⟨k, hk⟩ := hA.is_central $ Subalgebra.mem_center_iff.mpr hz'
    exact ⟨k, MulOpposite.unop_inj.mp hk⟩
  is_simple := @op_simple A _ hA.is_simple

namespace tensor_self_op

variable [hA: IsCentralSimple K A] [FiniteDimensional K A]

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

instance : IsCentralSimple K Aᵐᵒᵖ := CSA_op_is_CSA K A inferInstance
instance : FiniteDimensional K Aᵐᵒᵖ := LinearEquiv.finiteDimensional
  (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ)

instance fin_end : FiniteDimensional K (Module.End K A) :=
  LinearMap.finiteDimensional

-- #find Basis ?_
lemma dim_eq :
    FiniteDimensional.finrank K (A ⊗[K] Aᵐᵒᵖ) = FiniteDimensional.finrank K (Module.End K A) := by
  rw [FiniteDimensional.finrank_tensorProduct]
  rw [show FiniteDimensional.finrank K (Module.End K A) =
    FiniteDimensional.finrank K
      (Matrix (Fin $ FiniteDimensional.finrank K A) (Fin $ FiniteDimensional.finrank K A) K) from
    (algEquivMatrix $ FiniteDimensional.finBasis _ _).toLinearEquiv.finrank_eq]
  rw [FiniteDimensional.finrank_matrix, Fintype.card_fin]
  rw [show FiniteDimensional.finrank K Aᵐᵒᵖ = FiniteDimensional.finrank K A from
    (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.finrank_eq]

def equivEnd [Small.{v, u} K] : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (toEnd K A) $
    bijective_of_dim_eq_of_isCentralSimple _ _ _ _ $ dim_eq K A

end tensor_self_op

open tensor_self_op in
def tensor_self_op [Small.{v} K] [IsCentralSimple K A] [FiniteDimensional K A] :
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K]
    (Matrix (Fin $ FiniteDimensional.finrank K A) (Fin $ FiniteDimensional.finrank K A) K) :=
  equivEnd K A |>.trans $ algEquivMatrix $ FiniteDimensional.finBasis _ _

def tensor_op_self [Small.{v} K] [IsCentralSimple K A] [FiniteDimensional K A] :
    Aᵐᵒᵖ ⊗[K] A ≃ₐ[K]
    (Matrix (Fin $ FiniteDimensional.finrank K A) (Fin $ FiniteDimensional.finrank K A) K) :=
  (Algebra.TensorProduct.comm _ _ _).trans $ tensor_self_op _ _

/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/


structure CSA (K : Type u) [Field K] :=
  (carrier : Type v)
  [ring : Ring carrier]
  [algebra : Algebra K carrier]
  [is_central_simple : IsCentralSimple K carrier]
  [fin_dim : FiniteDimensional K carrier]

instance : CoeSort (CSA.{u, v} K) (Type v) where
  coe A := A.carrier

instance (A : CSA K) : Ring A := A.ring

instance (A : CSA K) : Algebra K A := A.algebra

instance (A : CSA K) : IsCentralSimple K A := A.is_central_simple

instance (A : CSA K) : IsSimpleOrder (RingCon A) := A.is_central_simple.is_simple

instance (A : CSA K) : FiniteDimensional K A := A.fin_dim

variable {K : Type u} [Field K]

structure BrauerEquivalence (A B : CSA.{u, v} K) :=
(n m : ℕ) (hn: n ≠ 0) (hm : m ≠ 0)
(iso: Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)


abbrev IsBrauerEquivalent (A B : CSA K) := Nonempty (BrauerEquivalence A B)

namespace IsBrauerEquivalent

def refl (A : CSA K) : IsBrauerEquivalent A A := ⟨⟨1, 1, one_ne_zero, one_ne_zero, AlgEquiv.refl⟩⟩

def symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
  obtain ⟨n, m, hn, hm, iso⟩ := h
  exact ⟨⟨m, n, hm, hn, iso.symm⟩⟩

def matrix_eqv' (n m : ℕ) (A : Type*) [Ring A] [Algebra K A] :
    (Matrix (Fin n × Fin m) (Fin n × Fin m) A) ≃ₐ[K] Matrix (Fin (n * m)) (Fin (n * m)) A :=
{ Matrix.reindexLinearEquiv K A finProdFinEquiv finProdFinEquiv with
  toFun := Matrix.reindex finProdFinEquiv finProdFinEquiv
  map_mul' := fun m n ↦ by simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  commutes' := fun k ↦ by simp only [algebraMap, Algebra.toRingHom, RingHom.coe_comp,
    Function.comp_apply, Matrix.scalar_apply, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv,
    Matrix.diagonal_eq_diagonal_iff, implies_true]
}

def trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, hn, hm, iso1⟩ := hAB
  obtain ⟨p, q, hp, hq, iso2⟩ := hBC
  refine ⟨⟨_, _, Nat.mul_ne_zero hp hn, Nat.mul_ne_zero hm hq,
    matrix_eqv' _ _ _ |>.symm.trans $ Matrix.comp_algHom _ _ _ _|>.symm.trans $
      iso1.mapMatrix (m := Fin p)|>.trans $ Matrix.comp_algHom _ _ _ _|>.trans $ ?_⟩⟩
  haveI : Algebra K (Matrix (Fin m × Fin p) (Fin m × Fin p) B) := inferInstance
  haveI : Algebra K (Matrix (Fin p × Fin m) (Fin p × Fin m) B) := inferInstance
  -- let eqv := Matrix.reindexAlgEquiv B (.prodComm (Fin p) (Fin m))
  -- refine eqv.trans ?_
  sorry
      -- Matrix.reindexAlgEquiv K (.prodComm _ _) |>.trans $ Matrix.comp_algHom _ _ _ _|>.symm.trans $
      -- iso2.mapMatrix.trans $ Matrix.comp_algHom _ _ _ _|>.trans $ matrix_eqv' _ _ _⟩⟩


lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B := by
  exact ⟨⟨_, _, one_ne_zero, one_ne_zero, h.mapMatrix (m := (Fin 1))⟩⟩

theorem Braur_is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

namespace BrauerGroup

def CSA_Setoid : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.Braur_is_eqv

def mul (A B : CSA.{u, u} K) : CSA K where
  carrier := A ⊗[K] B
  is_central_simple := @tensor_CSA_is_CSA K _ A B _ _ _ _ _ A.is_central_simple B.is_central_simple
  fin_dim := Module.Finite.tensorProduct K A B

def is_fin_dim_of_mop (A : Type*) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    FiniteDimensional K Aᵐᵒᵖ := by
  have f:= MulOpposite.opLinearEquiv K (M:= A)
  exact Module.Finite.of_surjective (M:= A) (N:= Aᵐᵒᵖ) f (LinearEquiv.surjective _)

instance inv (A : CSA K) : CSA K where
  carrier := Aᵐᵒᵖ
  is_central_simple := CSA_op_is_CSA K A A.is_central_simple
  fin_dim := is_fin_dim_of_mop A

instance one_in (n : ℕ) (hn : n ≠ 0): CSA K where
  carrier := Matrix (Fin n) (Fin n) K
  is_central_simple := by
   haveI: Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
   exact MatrixRing.isCentralSimple K (Fin n)

instance one_in' : CSA K where
  carrier := K
  is_central_simple :=
  { is_central := Subsingleton.le (Subalgebra.center _ _) ⊥
    is_simple := inferInstance }

instance one_mul_in (n : ℕ) (hn : n ≠ 0) (A : CSA K) : CSA K where
  carrier := A ⊗[K] (Matrix (Fin n) (Fin n) K)
  is_central_simple := by
    haveI: Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    exact tensor_CSA_is_CSA K A (Matrix (Fin n) (Fin n) K)
      -- (MatrixRing.isCentralSimple K (Fin n))

instance mul_one_in (n : ℕ) (hn : n ≠ 0) (A : CSA K) : CSA K where
  carrier := (Matrix (Fin n) (Fin n) K) ⊗[K] A
  is_central_simple := by
    haveI: Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    exact tensor_CSA_is_CSA K (Matrix (Fin n) (Fin n) K) A

def eqv_in (A : CSA K) (A' : Type*) [Ring A'] [Algebra K A'] (e : A ≃ₐ[K] A'): CSA K where
  carrier := A'
  is_central_simple := AlgEquiv.isCentralSimple e
  fin_dim := LinearEquiv.finiteDimensional e.toLinearEquiv

instance matrix_A (n : ℕ) (hn : n ≠ 0) (A : CSA K) : CSA K :=
  eqv_in (one_mul_in n hn A) (Matrix (Fin n) (Fin n) A) $
    by unfold one_mul_in ; exact matrixEquivTensor K A (Fin n)|>.symm

instance dim_1 (R : Type*) [Ring R] [Algebra K R]: Algebra K (Matrix (Fin 1) (Fin 1) R) where
  toFun k := Matrix.diagonal (λ _ => (Algebra.ofId K R) k)
  map_one' := by simp only [map_one, Matrix.diagonal_one]
  map_mul' := by simp only [map_mul, Matrix.diagonal_mul_diagonal, implies_true]
  map_zero' := by simp only [map_zero, Matrix.diagonal_zero]
  map_add' := by simp only [map_add, Matrix.diagonal_add, implies_true]
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
  (Matrix.comp_algHom _ _ _ _).trans $ (Matrix.swap_algHom _ _ _ _).trans
    (Matrix.comp_algHom _ _ _ _).symm


theorem eqv_mat (A : CSA K) (n : ℕ) (hn : n ≠ 0): IsBrauerEquivalent A (matrix_A _ hn A) := by
  refine ⟨⟨n, 1, hn, one_ne_zero, ?_⟩⟩
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
  rw [Matrix.matrix_eq_sum_std_basis x]
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
  rw [(matrixEquivForward (K := K) m n).map_smul (x i j)]
  congr 1
  simp only [matrixEquivForward, Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply,
    TensorProduct.lift.tmul]
  ext a b
  erw [Matrix.kroneckerMapBilinear_apply_apply]
  erw [Matrix.kroneckerMap_apply]
  erw [Algebra.coe_lmul_eq_mul]
  rw [LinearMap.mul]
  simp only [LinearMap.mk₂_apply]
  simp only [Matrix.stdBasisMatrix, mul_ite, mul_one, mul_zero]
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


lemma one_mul (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (one_mul_in n hn A) :=
  ⟨⟨n, 1, hn, by omega, AlgEquiv.symm $ (dim_one_iso _).trans $ matrixEquivTensor _ _ _ |>.symm⟩⟩

lemma mul_one (n : ℕ) (hn : n ≠ 0) (A : CSA K) :
    IsBrauerEquivalent A (mul_one_in n hn A) :=
  ⟨⟨n, 1, hn, by omega, AlgEquiv.symm $ (dim_one_iso _).trans $ AlgEquiv.symm $
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
    have := matrixEquivTensor K A (Fin n)
    refine AlgEquiv.trans (Algebra.TensorProduct.congr (matrixEquivTensor K A (Fin n))
      $ matrixEquivTensor K B (Fin m)) ?_
    refine AlgEquiv.trans (huarongdao _ _ _ _) ?_
    refine AlgEquiv.trans
      (Algebra.TensorProduct.congr AlgEquiv.refl $ (matrix_eqv _ _).trans $ matrix_eqv' _ _ _) ?_
    exact (matrixEquivTensor _ _ _).symm

theorem eqv_tensor_eqv (A B C D : CSA K) (hAB : IsBrauerEquivalent A B) (hCD : IsBrauerEquivalent C D) :
    IsBrauerEquivalent (mul A C) (mul B D) := by
  unfold mul
  obtain ⟨n, m, hn, hm, e1⟩ := hAB; obtain ⟨p, q, hp, hq, e2⟩ := hCD
  let e01 := kroneckerMatrixTensor' _ _ _ _|>.symm.trans $ Algebra.TensorProduct.congr e1 e2|>.trans
    $ kroneckerMatrixTensor' _ _ _ _
  exact ⟨⟨_, _, Nat.mul_ne_zero hn hp, Nat.mul_ne_zero hm hq, e01⟩⟩

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
  let n := FiniteDimensional.finrank K A
  have hn : n ≠ 0 := by
    by_contra! hn
    simp only [n] at hn
    have := FiniteDimensional.finrank_pos_iff (R := K) (M := A) |>.2 inferInstance
    omega
  have := tensor_self_op K A
  exact ⟨⟨1, n, one_ne_zero, hn, dim_one_iso _|>.trans this⟩⟩

lemma inv_mul (A : CSA.{u, u} K) : IsBrauerEquivalent (mul (inv (K := K) A) A) one_in' := by
  unfold mul inv one_in'
  let n := FiniteDimensional.finrank K A
  have hn : n ≠ 0 := by
    by_contra! hn
    simp only [n] at hn
    have := FiniteDimensional.finrank_pos_iff (R := K) (M := A) |>.2 $ inferInstance
    omega
  have := tensor_op_self K A
  exact ⟨⟨1, n, one_ne_zero, hn, dim_one_iso _|>.trans this⟩⟩


lemma inv_eqv (A B: CSA K) (hAB : IsBrauerEquivalent A B):
    IsBrauerEquivalent (inv (K := K) A) (inv (K := K) B) := by
  unfold inv
  obtain ⟨n, m, hn, hm, iso⟩ := hAB
  exact ⟨⟨n, m, hn, hm, (Matrix.matrixEquivMatrixMop_algebra _ _ _).trans
    $ (AlgEquiv.op iso).trans (Matrix.matrixEquivMatrixMop_algebra _ _ _).symm⟩⟩

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
  exact (mul_one 1 one_ne_zero A).trans (iso_to_eqv _ _ (Algebra.TensorProduct.congr
    (dim_one_iso _) AlgEquiv.refl))|>.symm

theorem mul_one' (A : BrGroup (K := K)) : A * 1 = A := by
  induction' A using Quotient.inductionOn' with A
  change _ * Quotient.mk'' one_in' = _ ; apply Quotient.sound
  exact (one_mul 1 one_ne_zero A).trans (iso_to_eqv _ _ (Algebra.TensorProduct.congr
    AlgEquiv.refl (dim_one_iso _)))|>.symm

instance Bruaer_Group : Group (BrGroup (K := K)) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  mul_left_inv := mul_left_inv'

lemma Alg_closed_equiv_one [IsAlgClosed K]: ∀(A : CSA K), IsBrauerEquivalent A one_in' := by
  intro A
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed K A
  exact ⟨⟨1, n, one_ne_zero, hn, dim_one_iso A|>.trans iso⟩⟩

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
  matrixEquivTensor E (E ⊗[K] A) (Fin m)

def e2 :
    (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E ≃ₐ[E]
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) :=
  Algebra.TensorProduct.congr AlgEquiv.refl $
    { __ := matrixEquivTensor K E (Fin m)
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
          simp only [Finset.mem_univ, Matrix.stdBasisMatrix, ite_eq_right_iff, one_ne_zero,
            imp_false, not_and, true_implies]
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


lemma e3Aux2 (hm : m ≠ 0) [IsCentralSimple K A] :
    IsCentralSimple E ((E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K)) :=
  haveI : Nonempty (Fin m) := ⟨0, by omega⟩
  tensor_CSA_is_CSA.{u, u} E (E ⊗[K] A) (E ⊗[K] Matrix (Fin m) (Fin m) K)

lemma e3Aux2' (hm : m ≠ 0) [IsCentralSimple K A] :
    IsCentralSimple E (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) := by
  haveI : Nonempty (Fin m) := ⟨0, by omega⟩
  apply IsCentralSimple.baseChange

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

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
lemma e3Aux5 : Function.Surjective (e3Aux4 (K := K) (E := E) A m) := by
  intro x
  induction' x using TensorProduct.induction_on with e a e a he ha
  · refine ⟨0, ?_⟩
    simp only [TensorProduct.zero_tmul, AlgHom.map_zero]
  · induction' a using TensorProduct.induction_on with a m a m h₁ h₂
    · refine ⟨0, ?_⟩
      simp only [TensorProduct.tmul_zero]; exact AlgHom.map_zero (e3Aux4 A m)
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
      · exact (e3Aux4 (K := K) (E := E) A _).map_add _ _
      · rw [TensorProduct.tmul_add]
  · rcases he with ⟨e, rfl⟩
    rcases ha with ⟨a, rfl⟩
    refine ⟨e + a, ?_⟩
    exact (e3Aux4 (K := K) (E := E) A _).map_add _ _

def e3 [csa_A : IsCentralSimple K A] :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  AlgEquiv.ofBijective (e3Aux4 (K := K) (E := E) A m) $ by
      if hm : m = 0
      then
        haveI := e3Aux3 (K := K) (E := E) A m hm
        refine ⟨fun _ _ _ => Subsingleton.elim _ _, e3Aux5 (K := K) (E := E) A m⟩
      else
        letI csa := e3Aux2 (K := K) (E := E) A m hm
        letI r1 : Ring ((E ⊗[K] A) ⊗[E] E ⊗[K] Matrix (Fin m) (Fin m) K) := inferInstance
        letI r2 : Ring (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) := inferInstance
        letI : Nontrivial (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) := by
            have := e3Aux2' (K := K) (E := E) A m hm |>.2
            exact RingCon.instNontrivialOfIsSimpleOrder_brauerGroup _
        apply bijective_of_surj_of_isCentralSimple E _ _ _ $ e3Aux5 (K := K) (E := E) A m

def e4 :
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (Matrix (Fin m) (Fin m) A) :=
  Algebra.TensorProduct.congr AlgEquiv.refl $ (matrixEquivTensor K A (Fin m)).symm

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


def e6 [csa_A : IsCentralSimple K A] [csa_B : IsCentralSimple K B] :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  AlgEquiv.ofBijective (e6Aux0 (K := K) (E := E) A B) $ by
    apply bijective_of_surj_of_isCentralSimple E _ _ _
    intro x
    induction' x using TensorProduct.induction_on with e a x y hx hy
    · refine ⟨0, ?_⟩
      exact (e6Aux0 (K := K) (E := E) A B).map_zero
    · induction' a using TensorProduct.induction_on with a b a a' ha ha'
      · refine ⟨0, ?_⟩
        rw [TensorProduct.tmul_zero]
        exact (e6Aux0 (K := K) (E := E) A B).map_zero
      · refine ⟨(e ⊗ₜ a) ⊗ₜ[E] (1 ⊗ₜ b), ?_⟩
        simp only [e6Aux0, Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
          _root_.one_mul, map_one];
        change e ⊗ₜ[K] 1 ⊗ₜ[K] 1 * 1 ⊗ₜ[K] a ⊗ₜ[K] 1 * 1 ⊗ₜ[K] 1 ⊗ₜ[K] b = _
        simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
      · rcases ha with ⟨aa, haa⟩
        rcases ha' with ⟨aa', haa'⟩
        refine ⟨aa + aa', ?_⟩
        rw [(e6Aux0 (K := K) (E := E) A B).map_add, haa, haa', TensorProduct.tmul_add]
    · rcases hx with ⟨x, rfl⟩
      rcases hy with ⟨y, rfl⟩
      refine ⟨x + y, ?_⟩
      rw [(e6Aux0 (K := K) (E := E) A B).map_add]

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
      is_central_simple := inferInstance
      fin_dim := inferInstance }) $ fun A B => Nonempty.map $ fun ⟨m, n, hm, hn, e⟩ =>
          ⟨m, n, hm, hn, (someEquivs.e1 A m).trans $ (someEquivs.e2 A m).trans $
            (someEquivs.e3 A m).trans $ (someEquivs.e4 A m).trans $ AlgEquiv.symm $
            (someEquivs.e1 B n).trans $ (someEquivs.e2 B n).trans $
            (someEquivs.e3 B n).trans $ (someEquivs.e4 B n).trans $ someEquivs.e5 _ _ e.symm⟩
  map_one' := by
    change Quotient.map' _ _ (Quotient.mk'' _) = Quotient.mk'' _
    erw [Quotient.eq'']
    change IsBrauerEquivalent _ _
    simp only
    refine ⟨1, 1, by omega, by omega, ?_⟩
    refine (dim_one_iso _).trans $ AlgEquiv.symm $ (dim_one_iso _).trans ?_
    change E ≃ₐ[E] (E ⊗[K] K)
    exact someEquivs.e7
  map_mul' := by
    intro x y
    induction' x using Quotient.inductionOn' with A
    induction' y using Quotient.inductionOn' with B
    simp only [Quotient.map'_mk'']
    erw [Quotient.map'_mk'']
    erw [Quotient.eq'']
    change IsBrauerEquivalent _ _
    refine ⟨1, 1, by omega, by omega, ?_⟩
    refine (dim_one_iso _).trans $ AlgEquiv.symm $ (dim_one_iso _).trans ?_
    change (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B)
    exact someEquivs.e6 A B

abbrev BaseChange_Q_to_C := BaseChange (K := ℚ) (E := ℂ)

lemma BaseChange_Q_to_C_eq_one : BaseChange_Q_to_C = 1 := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  ext A ; simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply]
  induction' A using Quotient.inductionOn' with A ;
  simp only [Quotient.map'_mk'']; apply Quotient.sound
  exact BrauerGroup.Alg_closed_equiv_one _

end Q_to_C

end BrauerGroupHom

namespace Brauer'



end Brauer'
