import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

-- TODO: Rename in mathlib
alias IsMulTwoCocycle.of_mem_twoCocycles := isMulTwoCocycle_of_mem_twoCocycles

variable {K F : Type} [Field K] [Field F] [Algebra F K] {α β : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ}

lemma IsMulTwoCocycle.mul (hα : IsMulTwoCocycle α) (hβ : IsMulTwoCocycle β) :
    IsMulTwoCocycle (α * β) :=
  .of_mem_twoCocycles _ (twoCocyclesOfIsMulTwoCocycle hα + twoCocyclesOfIsMulTwoCocycle hβ).2

end groupCohomology
