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

instance module_over_over (A : CSA k) (I : RingCon A):
    Module k I := Module.compHom I (algebraMap k A)

theorem centralsimple_over_extension_iff [FiniteDimensional k K]:
    IsCentralSimple k A ↔ IsCentralSimple K (K ⊗[k] A) where
  mp := fun hA ↦ IsCentralSimple.baseChange k A K
  mpr := fun hAt ↦ {
    is_central := sorry
    is_simple :=
    {
      exists_pair_ne := ⟨⊥, ⊤, by sorry⟩
      eq_bot_or_eq_top := fun I => by
        by_contra! hI
        have tensor_is_ideal: RingCon (K ⊗[k] A) :=
          RingCon.span {x| ∃(a : K)(i : I), x = a ⊗ₜ i.1}
        have ne_bot : tensor_is_ideal ≠ ⊥ := sorry
        have ne_top : tensor_is_ideal ≠ ⊤ := sorry
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
    have : FiniteDimensional k (K ⊗[k] A) := Module.Finite.trans (R := k) K (K ⊗[k] A)

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
  obtain ⟨n, -, L, _, _, _, ⟨iso⟩⟩ := CSA_iff_exist_split k A k_bar|>.1 h
  refine ⟨n, ?_⟩
  have := FiniteDimensional.finrank_matrix L (Fin n) (Fin n)
  simp only [Fintype.card_fin] at this
  exact dim_eq k L A|>.trans $ LinearEquiv.finrank_eq iso.toLinearEquiv|>.trans this

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

structure split (A : CSA k) :=
  (n : ℕ) (hn : n ≠ 0) (K : Type*) (hK1 : Field K) (hK2 : Algebra k K)
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

def split_by_alg_closure (A : CSA k): split k A where
  n := deg k k_bar A
  hn := by haveI := deg_pos k k_bar A; omega
  K := k_bar
  hK1 := inferInstance
  hK2 := inferInstance
  iso := sorry
