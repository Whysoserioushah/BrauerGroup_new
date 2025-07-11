import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology
variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] {f g : G × G → M}

lemma IsMulTwoCocycle.mul (hf : IsMulTwoCocycle f) (hg : IsMulTwoCocycle g) :
    IsMulTwoCocycle (f * g) :=
  fun a b c ↦ by simp [hf a, hg a, smul_mul', mul_mul_mul_comm]

instance [Fact <| IsMulTwoCocycle f] [Fact <| IsMulTwoCocycle g] :
    Fact <| IsMulTwoCocycle (f * g) := ⟨.mul Fact.out Fact.out⟩

end groupCohomology
