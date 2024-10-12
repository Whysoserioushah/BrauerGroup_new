import BrauerGroup.SplittingOfCSA

suppress_compilation

universe u

open TensorProduct

section Defs

variable (K F F_bar: Type u) [Field K] [Field F] [Algebra F K] [Field F_bar] [Algebra F F_bar] [hk_bar : IsAlgClosure F F_bar]

abbrev RelativeBrGroup := MonoidHom.ker $ BrauerGroupHom.BaseChange (K := F) (E := K)

include F_bar in
lemma ele_of_relBrGroup : ∀(A : RelativeBrGroup K F),
    isSplit F (@Quotient.out (CSA F) (BrauerGroup.CSA_Setoid) A) K := fun A ↦ by
  use (deg F F_bar (@Quotient.out _ (BrauerGroup.CSA_Setoid) A))
  use (deg_pos F F_bar _)
  obtain ⟨A, hA⟩ := A
  induction A using Quotient.inductionOn
  refine ⟨?_⟩
  -- have : BrauerGroupHom.BaseChange (K := F) (E := K) A = 1 := by
  --   unfold RelativeBrGroup at A
  --   rw [← MonoidHom.mem_ker] ; exact SetLike.coe_mem A
  -- simp only [MonoidHom.coe_mk, OneHom.coe_mk] at this
  -- change _ = Quotient.mk'' _ at this
  -- have : IsBrauerEquivalent (K ⊗[K] (@Quotient.out _ (BrauerGroup.CSA_Setoid) A.1)) (CSA.mk K) := sorry
  -- simp? [BrauerGroup.one_in'] at this
  sorry

end Defs
