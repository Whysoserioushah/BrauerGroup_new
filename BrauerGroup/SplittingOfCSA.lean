import BrauerGroup.BrauerGroup
import BrauerGroup.Quaternion
import BrauerGroup.AlgClosedUnion
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

suppress_compilation

universe u v w
variable (k A K: Type u) [Field k] [Field K] [Algebra k K] [Ring A]
  [Algebra k A]

variable (k_bar : Type u) [Field k_bar] [Algebra k k_bar] [hk_bar : IsAlgClosure k k_bar]

open scoped TensorProduct
open RingCon

instance module_over_over (A : CSA k) (I : RingCon A):
    Module k I := Module.compHom I (algebraMap k A)

lemma one_tensor_bot_RingCon [FiniteDimensional k K] {x : A} (Is_CSA : IsCentralSimple K (K ⊗[k] A))
  (h : 1 ⊗ₜ[k] x ∈ (⊥ : RingCon (K ⊗[k] A))) :
    x ∈ (⊥ : RingCon A) := by
  sorry

lemma one_tensor_bot_Algebra [FiniteDimensional k K] {x : A} (Is_CSA : IsCentralSimple K (K ⊗[k] A))
  (h : 1 ⊗ₜ[k] x ∈ (⊥ : Subalgebra K (K ⊗[k] A))) :
    x ∈ (⊥ : Subalgebra k A) := by
  sorry

theorem centralsimple_over_extension_iff [FiniteDimensional k K]:
    IsCentralSimple k A ↔ IsCentralSimple K (K ⊗[k] A) where
  mp := fun hA ↦ IsCentralSimple.baseChange k A K
  mpr := fun hAt ↦ {
    is_central := by
      obtain h := hAt.is_central
      intro x hx
      rw [Subalgebra.mem_center_iff] at hx
      have h1 : ((1 : K) ⊗ₜ[k] x) ∈ Subalgebra.center K (K ⊗[k] A) := by
        rw [Subalgebra.mem_center_iff]
        intro b
        induction b using TensorProduct.induction_on with
        | zero => simp only [zero_mul, mul_zero]
        | tmul b c =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
            one_mul, hx c]
        | add b c hb hc => rw [add_mul, mul_add]; simp only [hb, hc]
      specialize h h1
      exact one_tensor_bot_Algebra _ _ _ hAt h
    is_simple :=
    {
      exists_pair_ne := ⟨⊥, ⊤, by
        suffices Nontrivial (RingCon A) by simp only [ne_eq, bot_ne_top, not_false_eq_true]
        have : Nontrivial A := by
          by_contra! h
          have h0 : (⊥ : RingCon (K ⊗[k] A)) ≠ ⊤ := by
            rcases hAt.is_simple.exists_pair_ne with ⟨x, ⟨y, hxy⟩⟩
            obtain h := hAt.is_simple.eq_bot_or_eq_top y
            rcases hAt.is_simple.eq_bot_or_eq_top x with (x1 | x2) <;> aesop
          suffices (⊥ : RingCon (K ⊗[k] A)) = ⊤ by exact h0 this
          rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at h
          suffices (⊥ : RingCon (K ⊗[k] A)) = (⊤ : Set (K ⊗[k] A)) by
            rw [eq_top_iff, le_iff, this]
            simp only [Set.top_eq_univ, Set.subset_univ]
          apply Set.eq_of_subset_of_subset (by simp)
          intro x hx
          suffices x = 0 by tauto
          induction x using TensorProduct.induction_on with
          | zero => rfl
          | tmul b c => rw [← h 0 c, TensorProduct.tmul_zero]
          | add b c hb hc =>
            simp only [Set.top_eq_univ, Set.mem_univ, true_implies] at hb hc hx
            rw [hb, hc, add_zero]
        exact RingCon.instNontrivial
        ⟩
      eq_bot_or_eq_top := fun I => by
        by_contra! hI
        let tensor_is_ideal : RingCon (K ⊗[k] A) :=
          RingCon.span {x| ∃(a : K)(i : I), x = a ⊗ₜ i.1}
        have ne_bot : tensor_is_ideal ≠ ⊥ := by
          by_contra! h
          suffices I = ({0} : Set A) by
            apply hI.1
            rw [← le_bot_iff, le_iff]
            simp only [this, Set.singleton_subset_iff, SetLike.mem_coe]
            tauto
          apply Set.eq_of_subset_of_subset
          · intro x hx
            simp only [SetLike.mem_coe] at hx
            have : 1 ⊗ₜ x ∈ (tensor_is_ideal : Set (K ⊗[k] A)) := by
              simp only [Subtype.exists, exists_prop, SetLike.mem_coe, tensor_is_ideal]
              suffices 1 ⊗ₜ x ∈ {x| ∃ (a : K) , ∃ b ∈ I, x = a ⊗ₜ[k] b} by tauto
              use 1; use x
            simp only [SetLike.mem_coe, Set.mem_singleton_iff, h] at this ⊢
            suffices x ∈ (⊥ : RingCon A) by tauto
            exact one_tensor_bot_RingCon _ _ _ hAt this
          · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
            exact RingCon.zero_mem I
        have ne_top : tensor_is_ideal ≠ ⊤ := by
          by_contra! h
          suffices I = (⊤ : Set A) by
            apply hI.2
            rw [eq_top_iff, le_iff]
            simp only [this, Set.top_eq_univ, Set.subset_univ]
          apply Set.eq_of_subset_of_subset (by simp)
          intro x _
          by_contra! hx
          rw [eq_top_iff, le_iff] at h
          have : ∃ (a : K), a ⊗ₜ[k] x ∉ tensor_is_ideal := by
            sorry
          tauto
        haveI := hAt.is_simple.2 tensor_is_ideal
        tauto
    }
  }

def extension_CSA (A : CSA k) [FiniteDimensional k K]: CSA K where
  carrier := K ⊗[k] A
  is_central_simple := centralsimple_over_extension_iff k A K|>.1 A.is_central_simple
  fin_dim := Module.Finite.base_change k K A.carrier

def extension_inv (hT : IsCentralSimple K (K ⊗[k] A)) [FiniteDimensional K (K ⊗[k] A)]
    [FiniteDimensional k K]: CSA k where
  carrier := A
  is_central_simple := centralsimple_over_extension_iff k A K|>.2 hT
  fin_dim := by
    have := centralsimple_over_extension_iff k A K|>.2 hT
    let to_ten: A →ₐ[k] K ⊗[k] A :=
    {
      toFun := fun a ↦ 1 ⊗ₜ a
      map_one' := rfl
      map_mul' := by simp
      map_zero' := TensorProduct.tmul_zero A 1
      map_add' := TensorProduct.tmul_add 1
      commutes' := fun _ ↦ Algebra.TensorProduct.algebraMap_apply' _|>.symm
    }
    have Isinj : Function.Injective to_ten := by
      haveI := this.is_simple
      haveI : Nontrivial A := inferInstance
      exact RingCon.IsSimpleOrder.iff_eq_zero_or_injective A|>.1 inferInstance
        to_ten.toRingHom|>.resolve_left (by
        intro h
        rw [SetLike.ext_iff] at h
        specialize h 1
        simp only [RingCon.mem_ker, map_one, one_ne_zero, false_iff] at h
        exact h ⟨⟩)
    haveI : FiniteDimensional k (K ⊗[k] A) := Module.Finite.trans (R := k) K (K ⊗[k] A)
    exact FiniteDimensional.of_injective (K := k) to_ten.toLinearMap Isinj

theorem CSA_iff_exist_split [hA : FiniteDimensional k A]:
    IsCentralSimple k A ↔ (∃(n : ℕ)(_ : n ≠ 0)(L : Type u)(_ : Field L)(_ : Algebra k L)
    (fin_dim : FiniteDimensional k L), Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)) := by
  constructor
  · intro hA
    haveI := hk_bar.1
    obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    refine ⟨n, hn, ?_⟩
    haveI : FiniteDimensional k_bar (k_bar ⊗[k] A) := inferInstance
    let b := FiniteDimensional.finBasis k_bar (k_bar ⊗[k] A)
    have := inter_tensor_union k k_bar A
    -- let S1 : Set k_bar := (i : (Fin (FiniteDimensional.finrank k_bar (k_bar ⊗[k] A)))), {b i}
    have (i : Fin (FiniteDimensional.finrank k_bar (k_bar ⊗[k] A))) :
        ∃ (L : IntermediateField k k_bar), FiniteDimensional k L ∧
          b i ∈ intermediateTensor k k_bar A L := by
      apply algclosure_element_in k k_bar A
    choose L finL hL using this

    -- refine ⟨(⨆ (i : Fin (FiniteDimensional.finrank k_bar (k_bar ⊗[k] A))), L i :
    --   IntermediateField k k_bar), inferInstance, inferInstance,
    --   IntermediateField.finiteDimensional_iSup_of_finite, ⟨?_⟩⟩
    sorry
  · rintro ⟨n, hn, L, _, _, _, ⟨iso⟩⟩
    haveI : Nonempty (Fin n) := ⟨0, by omega⟩
    exact (centralsimple_over_extension_iff k A L).mpr $ AlgEquiv.isCentralSimple iso.symm

lemma dim_is_sq (h : IsCentralSimple k A) [FiniteDimensional k A]:
    IsSquare (FiniteDimensional.finrank k A) := by
  haveI := hk_bar.1
  obtain ⟨n, _, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
  refine ⟨n, ?_⟩
  have := FiniteDimensional.finrank_matrix k_bar (Fin n) (Fin n)
  simp only [Fintype.card_fin] at this
  exact dim_eq k k_bar A|>.trans $ LinearEquiv.finrank_eq iso.toLinearEquiv|>.trans this

def deg (A : CSA k): ℕ := dim_is_sq k A k_bar A.is_central_simple|>.choose

lemma deg_sq_eq_dim (A : CSA k): (deg k k_bar A) ^ 2 = FiniteDimensional.finrank k A :=
  by rw [pow_two]; exact dim_is_sq k A k_bar A.is_central_simple|>.choose_spec.symm

lemma deg_pos (A : CSA k): 0 < deg k k_bar A := by
  by_contra! h
  have eq_zero : deg k k_bar A = 0 := by omega
  apply_fun (λ x => x^2) at eq_zero
  rw [deg_sq_eq_dim k k_bar A, pow_two, mul_zero] at eq_zero
  haveI := A.is_central_simple.is_simple.1
  have Nontriv : Nontrivial A := inferInstance
  have := FiniteDimensional.finrank_pos_iff (R := k) (M := A)|>.2 Nontriv
  linarith

structure split (A : CSA k) (K : Type*) [Field K] [Algebra k K] :=
  (n : ℕ) (hn : n ≠ 0)
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

def split_by_alg_closure (A : CSA k): split k A k_bar where
  n := deg k k_bar A
  hn := by haveI := deg_pos k k_bar A; omega
  iso := by
    haveI := hk_bar.1
    choose n _ iso using simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    have iso' := iso.some ; clear iso
    have e : Matrix (Fin n) (Fin n) k_bar ≃ₐ[k_bar] Matrix (Fin (deg k k_bar A))
      (Fin (deg k k_bar A)) k_bar := by
      suffices n = deg k k_bar A from Matrix.reindexAlgEquiv k_bar (finCongr this)
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e1 := LinearEquiv.finrank_eq iso'.toLinearEquiv|>.trans $
        FiniteDimensional.finrank_matrix k_bar (Fin n) (Fin n)
      simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self, one_mul,
        Fintype.card_fin] at e1
      have := this.trans e1
      exact Nat.mul_self_inj.mp (id this.symm)
    exact iso'.trans e

def extension_over_split (A : CSA k) (L L': Type u) [Field L] [Field L'] [Algebra k L]
    (hA : split k A L) [Algebra L L'] [Algebra k L'] [IsScalarTower k L L'] : split k A L' where
  n := deg k k_bar A
  hn := by haveI := deg_pos k k_bar A; omega
  iso := sorry
