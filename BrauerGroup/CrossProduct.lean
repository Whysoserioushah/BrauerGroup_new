import BrauerGroup.Mathlib.GroupTheory.GroupExtension.Abelian
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

variable {G K : Type*} [Group G] [Field K] {a : G × G → Kˣ}

abbrev CrossProduct (a : G × G → Kˣ) :=
  MonoidAlgebra K (TwistedProduct a)

namespace CrossProduct

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ)

lemma dim_eq_square [Fact (IsMulTwoCocycle a)] :
    Module.finrank F (CrossProduct a) = (Module.finrank F K)^2 := by
  have eq1 : Module.finrank F (CrossProduct a) = Module.finrank F K *
      Module.finrank K (CrossProduct a) := by
    rw [Module.finrank_mul_finrank]
  -- rw [Module.finrank_eq_card_basis (x_AsBasis a), IsGalois.card_aut_eq_finrank] at eq1
  -- rw [eq1, pow_two]
  sorry

end CrossProduct
end groupCohomology
