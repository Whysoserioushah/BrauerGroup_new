import BrauerGroup.BrauerGroup
import BrauerGroup.Con 

suppress_compilation 

universe u v w
variable (k A K: Type u) [Field k] [Field K] [Algebra k K] [Ring A] 
  [Algebra k A]
open scoped TensorProduct

section more_on_CSA
namespace CentralSimple 

instance module_over_over (A : CSA k) (I : RingCon A): 
    Module k I := Module.compHom I (algebraMap k A)

theorem cantralsimple_over_extension_iff (A : CSA.{u, u} k) [FiniteDimensional k K]: 
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

end CentralSimple
end more_on_CSA



structure split (A : CSA k) := 
  (n : ℕ) (hn : n ≠ 0) (K : Type*) (hK1 : Field K) (hK2 : Algebra k K)
  (iso : K ⊗[k] A ≃ₐ[k] Matrix (Fin n) (Fin n) K)

def split_by_alg_closure (A : CSA k): split k A where
  n := sorry
  hn := sorry
  K := AlgebraicClosure k
  hK1 := inferInstance
  hK2 := inferInstance
  iso := sorry
