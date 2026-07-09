module

public import BrauerGroup.Algebra.BrauerGroup.Basic
public import BrauerGroup.CentralSimple
public import BrauerGroup.FieldCat
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section

suppress_compilation
universe u v v₁ v₂ w

variable (K : Type u) [Field K]
variable (A B : Type u) [Ring A] [Ring B] [Algebra K A] [Algebra K B]

open scoped TensorProduct

lemma bijective_of_dim_eq_of_simple
    [csa_source : IsSimpleRing A]
    [fin_source : FiniteDimensional K A]
    [fin_target : FiniteDimensional K B]
    (f : A →ₐ[K] B) (h : Module.finrank K A = Module.finrank K B) :
    Function.Bijective f := by
  have : Nontrivial B := Module.finrank_pos_iff.1 <| h ▸
    (Module.finrank_pos_iff (R := K) (M := A)|>.2 inferInstance)
  exact ⟨RingHom.injective f.toRingHom, f.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank
    h|>.1 <| RingHom.injective f.toRingHom⟩

lemma bijective_of_surj_of_isCentralSimple
    [csa_source : IsSimpleRing A]
    (f : A →ₐ[K] B) [Nontrivial B] (h : Function.Surjective f) :
    Function.Bijective f :=
  ⟨IsSimpleRing.iff_injective_ringHom A |>.1 inferInstance f.toRingHom, h⟩

-- instance CSA_op_is_CSA [hA : Algebra.IsCentral K A] : Algebra.IsCentral K Aᵐᵒᵖ where
--   out z hz:= by
--     let z': A := z.unop
--     have hz' : ∀ (x : A), x * z' = z' * x := by
--       rw [Subalgebra.mem_center_iff] at hz
--       intro x; specialize hz (MulOpposite.op x)
--       have z'_eq : MulOpposite.op z'= z := rfl
--       rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
--       have : (MulOpposite.op (z' * x)).unop = z' * x := rfl
--       simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
--           MulOpposite.unop_op, z']
--     obtain ⟨k, hk⟩ := hA.out <| Subalgebra.mem_center_iff.mpr hz'
--     exact ⟨k, MulOpposite.unop_inj.mp hk⟩

namespace tensor_self_op

variable [Algebra.IsCentral K A] [hA : IsSimpleRing A] [FiniteDimensional K A]

instance st : IsScalarTower K K (Module.End K A) where
  smul_assoc k₁ k₂ f := DFunLike.ext _ _ fun a ↦ by
    change (k₁ * k₂) • f a = k₁ • (k₂ • f a)
    rw [mul_smul]

-- instance : Algebra.IsCentral K Aᵐᵒᵖ := inferInstance -- CSA_op_is_CSA K A inferInstance
-- instance : FiniteDimensional K Aᵐᵒᵖ := LinearEquiv.finiteDimensional
--   (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ)

-- instance fin_end : FiniteDimensional K (Module.End K A) :=
--   LinearMap.finiteDimensional

omit [Algebra.IsCentral K A] hA in
lemma dim_eq :
    Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
  rw [Module.finrank_tensorProduct]
  rw [show Module.finrank K (Module.End K A) =
    Module.finrank K (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) from
    (algEquivMatrix <| Module.finBasis _ _).toLinearEquiv.finrank_eq]
  rw [Module.finrank_matrix, Fintype.card_fin]
  rw [(MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.finrank_eq]
  simp only [Module.finrank_self, mul_one]

def equivEnd : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (AlgHom.mulLeftRight K A) <| bijective_of_dim_eq_of_simple _ _ _ _ <|
    dim_eq K A

end tensor_self_op

open tensor_self_op in
def tensor_self_op
    [Algebra.IsCentral K A] [hA : IsSimpleRing A] [FiniteDimensional K A] :
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K]
    (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) :=
  equivEnd K A |>.trans <| algEquivMatrix <| Module.finBasis _ _

def tensor_op_self
    [Algebra.IsCentral K A] [hA : IsSimpleRing A] [FiniteDimensional K A] :
    Aᵐᵒᵖ ⊗[K] A ≃ₐ[K]
    (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) :=
  (Algebra.TensorProduct.comm _ _ _).trans <| tensor_self_op _ _

/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/

variable {K : Type u} [Field K]

namespace IsBrauerEquivalent

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

lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B :=
    ⟨1, 1, one_ne_zero, one_ne_zero, ⟨h.mapMatrix (m := (Fin 1))⟩⟩

end IsBrauerEquivalent

namespace BrauerGroup

def mul (A B : CSA.{u, v} K) : CSA.{u, v} K where
  toAlgCat := .of K (A ⊗[K] B)
  fin_dim := Module.Finite.tensorProduct K A B

def one_in' : CSA K := ⟨.of K K⟩

def dim_one_iso (R : Type*) [Ring R] [Algebra K R] : (Matrix (Fin 1) (Fin 1) R) ≃ₐ[K] R where
  toFun m := m 0 0
  invFun r := Matrix.diagonal fun _ => r
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

def kroneckerMatrixTensor' (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ) :
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K]
      (Matrix (Fin (n*m)) (Fin (n*m)) (A ⊗[K] B)) :=
  .trans (Algebra.TensorProduct.congr (matrixEquivTensor (Fin n) K A) <|
    matrixEquivTensor (Fin m) K B) <| (Algebra.TensorProduct.tensorTensorTensorComm ..).trans <|
      .trans
    (Algebra.TensorProduct.congr .refl <| (Matrix.kroneckerAlgEquiv _ _ K).trans <| matrix_eqv' ..)
    (matrixEquivTensor ..).symm

theorem eqv_tensor_eqv
    (A B C D : CSA K) (hAB : IsBrauerEquivalent A B) (hCD : IsBrauerEquivalent C D) :
    IsBrauerEquivalent (mul A C) (mul B D) := by
  obtain ⟨n, m, hn, hm, ⟨e1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨e2⟩⟩ := hCD
  exact ⟨n * p, m * q, by simp_all, by simp_all, ⟨ (kroneckerMatrixTensor' A C n p).symm.trans <|
    (Algebra.TensorProduct.congr e1 e2).trans <| kroneckerMatrixTensor' B D m q⟩⟩

lemma Alg_closed_equiv_one [IsAlgClosed K] : ∀(A : CSA K), IsBrauerEquivalent A one_in' := by
  intro A
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed K A
  exact ⟨1, n, one_ne_zero, hn, ⟨dim_one_iso A|>.trans iso⟩⟩

lemma Alg_closed_eq_one [IsAlgClosed K] : ∀(A : BrauerGroup (K := K)), A = 1 := by
  intro A; induction A using Quotient.inductionOn' with | h A
  change _ = Quotient.mk'' one_in'; apply Quotient.sound
  change IsBrauerEquivalent _ _; exact Alg_closed_equiv_one A

instance [IsAlgClosed K] : Unique (BrauerGroup (K := K)) where
  default := 1
  uniq := Alg_closed_eq_one

theorem Alg_closed_Brauer_trivial [IsAlgClosed K] : (⊤ : Subgroup (BrauerGroup K)) =
    (⊥ : Subgroup <| BrauerGroup (K := K)) :=
  Subgroup.ext fun _ ↦ ⟨fun _ ↦ Alg_closed_eq_one _, fun _ ↦ ⟨⟩⟩

end BrauerGroup

namespace BrauerGroupHom

open BrauerGroup
variable {E : Type u} [Field E] [Algebra K E]

namespace someEquivs

variable (A B : Type u) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
variable (m : ℕ)

def e1 : Matrix (Fin m) (Fin m) (E ⊗[K] A) ≃ₐ[E] (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E :=
  matrixEquivTensor (Fin m) E (E ⊗[K] A)

def e2 :
    (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E ≃ₐ[E]
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) :=
  Algebra.TensorProduct.congr .refl <|
    { __ := matrixEquivTensor (Fin m) K E
      commutes' e := by
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          matrixEquivTensor_apply, Fintype.sum_prod_type,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        simp_rw [Matrix.algebraMap_eq_diagonal]
        simp_rw [Matrix.diagonal_apply]
        simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [show
          ∑ x : Fin m, ∑ y : Fin m,
            (if x = y then e else 0) ⊗ₜ[K] Matrix.single x y (1 : K) =
          ∑ x : Fin m, e ⊗ₜ[K] Matrix.single x x 1 by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [show e ⊗ₜ[K] Matrix.single x x (1 : K) =
              (if x = x then e else 0) ⊗ₜ Matrix.single x x (1 : K) by aesop]
            apply Finset.sum_eq_single
            · aesop
            · aesop]
        rw [← TensorProduct.tmul_sum]
        congr 1
        ext i j
        rw [Matrix.sum_apply]
        by_cases h : i = j
        · subst h; simp [Matrix.single]
        · rw [Matrix.one_apply_ne h]
          apply Finset.sum_eq_zero
          intros k
          simp only [Finset.mem_univ, Matrix.single, Matrix.of_apply, ite_eq_right_iff,
            one_ne_zero, imp_false, not_and, forall_const]
          rintro rfl
          exact h }

def e3Aux0 : E ⊗[K] A →ₐ[E] E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  AlgHom.comp
    { (Algebra.TensorProduct.assoc K K K E A (Matrix (Fin m) (Fin m) K)).toAlgHom with
      commutes' e := by
        simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, RingHom.toMonoidHom_eq_coe,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
          Algebra.TensorProduct.assoc_tmul]
        rfl }
    (Algebra.TensorProduct.includeLeft : E ⊗[K] A →ₐ[E] (E ⊗[K] A) ⊗[K] Matrix (Fin m) (Fin m) K)

def e3Aux10 : (E ⊗[K] Matrix (Fin m) (Fin m) K) ⊗[K] A ≃ₐ[K]
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  (Algebra.TensorProduct.assoc K K K E (Matrix (Fin m) (Fin m) K) A).trans <|
    Algebra.TensorProduct.congr AlgEquiv.refl <| Algebra.TensorProduct.comm _ _ _

def e3Aux1 : E ⊗[K] Matrix (Fin m) (Fin m) K →ₐ[E] E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  AlgHom.comp
    { (e3Aux10 (K := K) (E := E) A m).toAlgHom with
      commutes' e := by
        simp only [e3Aux10, AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom,
          RingHom.toMonoidHom_eq_coe, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, RingHom.coe_coe, AlgEquiv.trans_apply,
          Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.congr_apply,
          AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
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
  suffices ∀ a : (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K), a = 0 by
    refine ⟨fun a b => ?_⟩
    rw [this a, this b]
  subst hm
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | add e a he ha => rw [he, ha, zero_add]
  | tmul e a =>
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
  | tmul e' mat =>
  rw [show mat = 0 from Subsingleton.elim _ _]
  simp

set_option maxHeartbeats 800000 in
-- FIXME: Get rid of the raised heartbeats
def e3Aux4 :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) →ₐ[E]
      E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) := by
  refine Algebra.TensorProduct.lift (e3Aux0 A m) (e3Aux1 A m) fun x y ↦ ?_
  change _ = _
  simp only [e3Aux0, AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, AlgHom.coe_comp,
    AlgHom.coe_mk, RingHom.coe_coe, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    e3Aux1, e3Aux10, AlgEquiv.coe_trans, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom]
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [TensorProduct.zero_tmul, map_zero]; rw [zero_mul
      (M₀ := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)), mul_zero
      (M₀ := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))]
  | add e a he ha =>
    haveI := Distrib.leftDistribClass (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))
    haveI := Distrib.rightDistribClass (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))
    simp only [TensorProduct.add_tmul, map_add,
      add_mul (R := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)), he, ha,
      mul_add (R := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))]
  | tmul e a =>
  simp only [Algebra.TensorProduct.assoc_tmul]
  induction y using TensorProduct.induction_on with
  | zero =>
    simp only [TensorProduct.zero_tmul]
    trans 0
    · exact mul_zero (M₀ := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) _
    · symm
      exact zero_mul (M₀ := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) _
  | add x y hx hy =>
    haveI := Distrib.leftDistribClass (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))
    haveI := Distrib.rightDistribClass (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))
    convert congr($hx + $hy) using 1
    · rw [← mul_add (R := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))]
      congr
      rw [TensorProduct.add_tmul]
      exact map_add _ _ _
    · rw [← add_mul (R := E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K))]
      congr
      rw [TensorProduct.add_tmul]
      exact map_add _ _ _
  | tmul x y =>
    simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq, Algebra.TensorProduct.tmul_mul_tmul]
    erw [Algebra.TensorProduct.comm_tmul]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      _root_.mul_one, _root_.one_mul, _root_.mul_one, _root_.one_mul, mul_comm e x]

set_option maxHeartbeats 800000 in
-- FIXME: Get rid of the raised heartbeats
set_option synthInstance.maxHeartbeats 100000 in
-- FIXME: Get rid of the raised heartbeats
lemma e3Aux5 : Function.Surjective (e3Aux4 (K := K) (E := E) A m) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, rfl⟩
  | add e a he ha =>
    rcases he with ⟨e, rfl⟩
    rcases ha with ⟨a, rfl⟩
    refine ⟨e + a, ?_⟩
    exact map_add (f := e3Aux4 (K := K) (E := E) A _) _ _
  | tmul e a =>
  induction a using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [TensorProduct.tmul_zero]; rfl
  | add a m h₁ h₂ =>
    rcases h₂ with ⟨m, h₂⟩
    rcases h₁ with ⟨a, h₁⟩
    refine ⟨a + m, ?_⟩
    convert congr($h₁+ $h₂) using 1
    · exact map_add (f := e3Aux4 (K := K) (E := E) A _) _ _
    · rw [TensorProduct.tmul_add]
  | tmul a m =>
    refine ⟨(e ⊗ₜ[K] a) ⊗ₜ[E] ((1 : E) ⊗ₜ[K] m), ?_⟩
    simp [Algebra.TensorProduct.lift_tmul, e3Aux0, e3Aux1, e3Aux4, e3Aux10]

def e3 [Algebra.IsCentral K A] [csa_A : IsSimpleRing A] :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  AlgEquiv.ofBijective (e3Aux4 (K := K) (E := E) A m) <| by
      if hm : m = 0
      then
        haveI := e3Aux3 (K := K) (E := E) A m hm
        refine ⟨fun _ _ _ => Subsingleton.elim _ _, e3Aux5 (K := K) (E := E) A m⟩
      else
        have : NeZero m := ⟨hm⟩
        letI r1 : Ring ((E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K)) := inferInstance
        letI r2 : Ring (E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K)) := inferInstance
        apply bijective_of_surj_of_isCentralSimple E _ _ _ <| e3Aux5 (K := K) (E := E) A m

def e4 :
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (Matrix (Fin m) (Fin m) A) :=
  Algebra.TensorProduct.congr AlgEquiv.refl <| (matrixEquivTensor (Fin m) K A).symm

def e5 (e : A ≃ₐ[K] B) : (E ⊗[K] A) ≃ₐ[E] (E ⊗[K] B) :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

set_option maxHeartbeats 800000 in
-- FIXME: Get rid of the raised heartbeats
def e6Aux0 : (E ⊗[K] A) ⊗[E] (E ⊗[K] B) →ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift
      { toFun e := e ⊗ₜ[K] (1 ⊗ₜ 1)
        map_one' := rfl
        map_mul' := fun e e' => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun e e' => by simp [TensorProduct.add_tmul]
        commutes' e := rfl }
      { toFun a := 1 ⊗ₜ[K] (a ⊗ₜ 1)
        map_one' := rfl
        map_mul' := fun _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun _ _ => by simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
        commutes' k := by
          simp only [Algebra.TensorProduct.algebraMap_apply]
          rw [show (algebraMap K A) k ⊗ₜ[K] (1 : B) = k • (1 : A ⊗[K] B) by
            rw [Algebra.algebraMap_eq_smul_one]
            rw [← TensorProduct.smul_tmul']
            rfl]
          simp [TensorProduct.tmul_smul, Algebra.smul_def (A := E ⊗[K] (A ⊗[K] B))]
      } fun e a =>
            show (_ ⊗ₜ[K] _) * (_ ⊗ₜ[K] _) = (_ ⊗ₜ[K] _) * (_ ⊗ₜ[K] _) by simp)
    (Algebra.TensorProduct.lift
      { toFun e := e ⊗ₜ[K] (1 ⊗ₜ 1)
        map_one' := rfl
        map_mul' := fun e e' => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun e e' => by simp [TensorProduct.add_tmul]
        commutes' e := rfl }
      { toFun b := 1 ⊗ₜ[K] (1 ⊗ₜ b)
        map_one' := rfl
        map_mul' := fun _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun _ _ => by simp [TensorProduct.tmul_add]
        commutes' k := by
          simp only [Algebra.TensorProduct.algebraMap_apply]
          rw [show (1 : A) ⊗ₜ[K] (algebraMap K B) k = k • (1 : A ⊗[K] B) by
            rw [Algebra.algebraMap_eq_smul_one]
            rw [TensorProduct.tmul_smul]
            rfl]
          simp [TensorProduct.tmul_smul, Algebra.smul_def (A := E ⊗[K] (A ⊗[K] B))]
      }
    fun e b => show (_ ⊗ₜ _) * (_ ⊗ₜ _) = (_ ⊗ₜ _) * (_ ⊗ₜ _) by simp)
      fun x y => show _ = _ by
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero, zero_mul, mul_zero]
        | add x x' hx hx' => simp only [map_add, mul_add, hx, hx', add_mul]
        | tmul e a =>
        simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk]
        induction y using TensorProduct.induction_on with
        | zero => simp only [map_zero, mul_zero, zero_mul]
        | add y y' hy hy' => simp only [map_add, mul_add, hy, hy', add_mul]
        | tmul e' b =>
        simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk]
        change (_ ⊗ₜ _) * (_ ⊗ₜ _) * ((_ ⊗ₜ _) * (_ ⊗ₜ _))
          = (_ ⊗ₜ _) * (_ ⊗ₜ _) * ((_ ⊗ₜ _) * (_ ⊗ₜ _))
        simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [mul_comm]

-- e6: equivalence (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B)
def e6 [Algebra.IsCentral K A] [csa_A : IsSimpleRing A]
    [Algebra.IsCentral K B] [csa_B : IsSimpleRing B] :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  AlgEquiv.ofBijective (e6Aux0 (K := K) (E := E) A B) <| by
    apply bijective_of_surj_of_isCentralSimple E _ _ _
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, rfl⟩
    | add x y hx hy =>
      rcases hx with ⟨x, rfl⟩
      rcases hy with ⟨y, rfl⟩
      refine ⟨x + y, ?_⟩
      exact map_add (f := (e6Aux0 (K := K) (E := E) A B)) _ _
    | tmul e a =>
    induction a using TensorProduct.induction_on with
    | zero =>
      refine ⟨0, ?_⟩
      rw [TensorProduct.tmul_zero]
      rfl
    | add a a' ha ha' =>
      rcases ha with ⟨aa, haa⟩
      rcases ha' with ⟨aa', haa'⟩
      refine ⟨aa + aa', ?_⟩
      rw [_root_.map_add (f := (e6Aux0 (K := K) (E := E) A B)), haa, haa', TensorProduct.tmul_add]
    | tmul a b =>
    refine ⟨(e ⊗ₜ a) ⊗ₜ[E] (1 ⊗ₜ b), ?_⟩
    simp only [e6Aux0, Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk,
      _root_.one_mul, map_one];
    change e ⊗ₜ[K] (1 ⊗ₜ[K] 1) * 1 ⊗ₜ[K] (a ⊗ₜ[K] 1) * 1 ⊗ₜ[K] (1 ⊗ₜ[K] b) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]

def e7 : E ≃ₐ[E] (E ⊗[K] K) := .symm <| Algebra.TensorProduct.rid _ _ _

end someEquivs

section Q_to_C

set_option backward.isDefEq.respectTransparency false in
abbrev BaseChange : BrauerGroup (K := K) →* BrauerGroup (K := E) where
  toFun :=
    Quotient.map'
    (fun A =>
    { __ := AlgCat.of E (E ⊗[K] A)
      fin_dim := inferInstance }) fun A B ⟨m, n, hm, hn, ⟨e⟩⟩ =>
          ⟨m, n, hm, hn, ⟨(someEquivs.e1 A m).trans <| (someEquivs.e2 A m).trans <|
            (someEquivs.e3 A m).trans <| (someEquivs.e4 A m).trans <| AlgEquiv.symm <|
            (someEquivs.e1 B n).trans <| (someEquivs.e2 B n).trans <|
            (someEquivs.e3 B n).trans <| (someEquivs.e4 B n).trans <| someEquivs.e5 _ _ e.symm⟩⟩
  map_one' := by
    erw [Quotient.eq'']
    exact ⟨1, 1, one_ne_zero, one_ne_zero,
      ⟨(dim_one_iso (K := E) (E ⊗[K] K)).trans <| (someEquivs.e7 (K := K) (E := E)).symm.trans <|
        (dim_one_iso (K := E) E).symm⟩⟩
  map_mul' := by
    intro x y
    induction x using Quotient.inductionOn' with | h A
    induction y using Quotient.inductionOn' with | h B
    simp only [Quotient.map'_mk'']
    erw [Quotient.map'_mk'']
    erw [Quotient.eq'']
    change IsBrauerEquivalent ⟨.of E (E ⊗[K] (A ⊗[K] B))⟩ _
    exact ⟨1, 1, one_ne_zero, one_ne_zero,
      ⟨(dim_one_iso _).trans <| .symm <| (dim_one_iso _).trans <| someEquivs.e6 A B⟩⟩

abbrev BaseChange_Q_to_C := BaseChange (K := ℚ) (E := ℂ)

lemma BaseChange_Q_to_C_eq_one : BaseChange_Q_to_C = 1 := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  ext A; simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply]
  induction A using Quotient.inductionOn' with | h A;
  simp only [Quotient.map'_mk'']; apply Quotient.sound
  exact BrauerGroup.Alg_closed_equiv_one _

end Q_to_C

open CategoryTheory

@[simps!]
def baseChange_idem.Aux (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] (A : CSA F) :
    E ⊗[K] (K ⊗[F] A) ≃ₗ[E] (E ⊗[F] A.carrier) :=
  have : SMulCommClass F K E :=
    { smul_comm := fun a b c => by
        rw [Algebra.smul_def, Algebra.smul_def, ← _root_.mul_assoc, mul_comm (algebraMap _ _ a),
          Algebra.smul_def, Algebra.smul_def, _root_.mul_assoc] }
  (TensorProduct.AlgebraTensorModule.assoc F K E E K A).symm ≪≫ₗ
  TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.AlgebraTensorModule.rid _ _ _) (LinearEquiv.refl _ _)

set_option maxHeartbeats 600000 in
-- FIXME: Get rid of the raised heartbeats
def baseChange_idem.Aux' (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] (A : CSA F) :
    E ⊗[K] (K ⊗[F] A) ≃ₐ[E] (E ⊗[F] A.carrier) := by
  have : SMulCommClass F K E :=
    { smul_comm := fun a b c => by
        rw [Algebra.smul_def, Algebra.smul_def, ← _root_.mul_assoc, mul_comm (algebraMap _ _ a),
          Algebra.smul_def, Algebra.smul_def, _root_.mul_assoc] }
  refine .ofLinearEquiv (baseChange_idem.Aux F K E A) ?_ fun x y ↦ ?_
  · simp [Algebra.TensorProduct.one_def]
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, (baseChange_idem.Aux F K E A).map_zero, zero_mul]
  | add => simp only [add_mul, (Aux F K E A).map_add, *]
  | tmul =>
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, (baseChange_idem.Aux F K E A).map_zero, mul_zero]
  | add => simp only [mul_add, (Aux F K E A).map_add, *]
  | tmul =>
  rename_i x1 y1 x2 y2
  simp only [Aux, Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.trans_apply]
  set f := (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.AlgebraTensorModule.rid K E E) (LinearEquiv.refl F A))
  set g := (TensorProduct.AlgebraTensorModule.assoc F K E E K A.carrier).symm
  change f (g _) = _
  induction y1 using TensorProduct.induction_on with
  | zero =>
    rw [zero_mul, TensorProduct.tmul_zero, g.map_zero, f.map_zero, TensorProduct.tmul_zero,
      g.map_zero, f.map_zero, zero_mul]
  | add => simp only [add_mul, TensorProduct.tmul_add, g.map_add, f.map_add, *]
  | tmul k1 a1 =>
  induction y2 using TensorProduct.induction_on with
  | zero =>
    rw [mul_zero, TensorProduct.tmul_zero, TensorProduct.tmul_zero, g.map_zero, f.map_zero,
      mul_zero]
  | add => simp only [mul_add, TensorProduct.tmul_add, g.map_add, f.map_add, *]
  | tmul k2 a2 =>
  simp only [Algebra.TensorProduct.tmul_mul_tmul, *]
  simp only [TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    LinearEquiv.refl_apply, Algebra.TensorProduct.tmul_mul_tmul, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, f, g]
  congr 1
  rw [mul_comm k1 k2]
  exact mul_smul k2 k1 (x1 * x2)

lemma baseChange_idem (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] :
    BrauerGroupHom.BaseChange (K := F) (E := E) =
    (BrauerGroupHom.BaseChange (K := K) (E := E)).comp
    BrauerGroupHom.BaseChange := by
  ext A
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply]
  induction A using Quotient.inductionOn' with | h A
  simp only [Quotient.map'_mk'', Quotient.eq'']
  exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨.mapMatrix <| .symm <| baseChange_idem.Aux' ..⟩⟩

def Br : FieldCat ⥤ CommGrpCat where
  obj F := .of <| BrauerGroup F
  map {F K} f := CommGrpCat.ofHom <| @BrauerGroupHom.BaseChange F _ K _ (RingHom.toAlgebra f.hom)
  map_id F := by
    ext A
    simp only [CommGrpCat.coe_of]
    induction A using Quotient.inductionOn' with | h A
    simp only [CommGrpCat.hom_ofHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Quotient.map'_mk'', CommGrpCat.hom_id, MonoidHom.id_apply, Quotient.eq]
    change IsBrauerEquivalent _ _
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.mapMatrix <| Algebra.TensorProduct.lid _ _⟩⟩
  map_comp {F K E} f g := by
    simp only [← CommGrpCat.ofHom_comp]
    congr 1
    apply +allowSynthFailures baseChange_idem
    letI : Algebra F E := RingHom.toAlgebra (f ≫ g).hom
    letI : Algebra F K := RingHom.toAlgebra f.hom
    letI : Algebra K E := RingHom.toAlgebra g.hom
    exact IsScalarTower.of_algebraMap_smul (R := F) (A := K) (M := E) fun r ↦ congrFun rfl

end BrauerGroupHom
