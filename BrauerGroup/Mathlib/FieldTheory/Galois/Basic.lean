import Mathlib.FieldTheory.Galois.Basic

namespace IsGalois
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

-- This is already in future mathlib
lemma mem_bot_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x ∈ (⊥ : IntermediateField F E) ↔ ∀ f : E ≃ₐ[F] E, f x = x := sorry

end IsGalois
