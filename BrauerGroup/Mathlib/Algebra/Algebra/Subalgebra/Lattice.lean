import Mathlib.Algebra.Algebra.Subalgebra.Basic

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

lemma Subalgebra.map_centralizer_le_centralizer_image (s : Set A) (f : A →ₐ[R] B) :
    (centralizer _ s).map f ≤ centralizer _ (f '' s) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  dsimp only [RingHom.coe_coe]
  rw [← map_mul, ← map_mul, hg h hh]
