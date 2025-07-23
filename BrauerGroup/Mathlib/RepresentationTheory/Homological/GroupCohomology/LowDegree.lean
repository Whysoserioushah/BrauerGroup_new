import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

namespace groupCohomology
variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] {f g : G × G → M}

-- TODO: Rename in mathlib
alias IsMulCocycle₂.of_mem_cocycles₂ := isMulCocycle₂_of_mem_cocycles₂

lemma IsMulCocycle₂.mul (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) :
    IsMulCocycle₂ (f * g) :=
  fun a b c ↦ by simp [hf a, hg a, smul_mul', mul_mul_mul_comm]

instance [Fact <| IsMulCocycle₂ f] [Fact <| IsMulCocycle₂ g] :
    Fact <| IsMulCocycle₂ (f * g) := ⟨.mul Fact.out Fact.out⟩

end groupCohomology
