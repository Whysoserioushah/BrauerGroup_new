import BrauerGroup.BrauerGroup
import BrauerGroup.Con

suppress_compilation

universe u v w
variable (k A K: Type u) [Field k] [Field K] [Algebra k K] [Ring A]
  [Algebra k A]
open scoped TensorProduct Classical

-- variable (L : Type u) [Field L] [Algebra K L]
--   (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V]

-- lemma dim_eq : FiniteDimensional.finrank K V = FiniteDimensional.finrank L (L ⊗[K] V) := by
--   let b := FiniteDimensional.finBasis K V
--   let b' := Algebra.TensorProduct.basis L b
--   rw [FiniteDimensional.finrank_eq_card_basis b, FiniteDimensional.finrank_eq_card_basis b']

section more_on_CSA
namespace CentralSimple

instance module_over_over (A : CSA k) (I : RingCon A):
    Module k I := Module.compHom I (algebraMap k A)

theorem cantralsimple_over_extension_iff [FiniteDimensional k K]:
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
  is_central_simple := cantralsimple_over_extension_iff k A K|>.1 A.is_central_simple
  fin_dim := Module.Finite.base_change k K A.carrier

def extension_inv (hT : IsCentralSimple K (K ⊗[k] A)) [FiniteDimensional K (K ⊗[k] A)]
    [FiniteDimensional k K]: CSA k where
  carrier := A
  is_central_simple := cantralsimple_over_extension_iff k A K|>.2 hT
  fin_dim := sorry

lemma dim_is_sq (A : CSA k): IsSquare (FiniteDimensional.finrank k A) := ⟨sorry, sorry⟩

def deg (A : CSA k): ℕ := dim_is_sq k A|>.choose

lemma deg_sq_eq_dim (A : CSA k): (deg k A) ^ 2 = FiniteDimensional.finrank k A :=
  by rw [pow_two]; exact dim_is_sq k A|>.choose_spec.symm

lemma deg_pos (A : CSA k): 0 < deg k A := by
  by_contra! h
  have eq_zero : deg k A = 0 := by omega
  apply_fun (λ x => x^2) at eq_zero
  rw [deg_sq_eq_dim k A, pow_two, mul_zero] at eq_zero
  haveI := A.is_central_simple.is_simple.1
  have Nontriv : Nontrivial A := inferInstance
  have := FiniteDimensional.finrank_pos_iff (R := k) (M := A)|>.2 Nontriv
  linarith

end CentralSimple
end more_on_CSA

structure split (A : CSA k) :=
  (n : ℕ) (hn : n ≠ 0) (K : Type*) (hK1 : Field K) (hK2 : Algebra k K)
  (iso : K ⊗[k] A ≃ₐ[k] Matrix (Fin n) (Fin n) K)

def split_by_alg_closure (A : CSA k): split k A where
  n := CentralSimple.deg k A
  hn := by haveI := CentralSimple.deg_pos k A; omega
  K := AlgebraicClosure k
  hK1 := inferInstance
  hK2 := inferInstance
  iso := sorry
