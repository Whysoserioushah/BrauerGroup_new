module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

@[expose] public section

variable {R₀ R S A B : Type*} [CommSemiring R₀] [CommSemiring R] [CommSemiring S] [Semiring A]
  [Semiring B] [Algebra R₀ R] [Algebra R₀ S] [Algebra R A] [Algebra S B] [Algebra R₀ A]
  [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ S B]

/-- The center of an algebra is preserved under algebra isomorphisms. -/
@[simps!]
def Subalgebra.centerCongr (e : A ≃ₐ[R₀] B) : Subalgebra.center R A ≃ₐ[R₀]
    Subalgebra.center S B where
  __ := Subsemiring.centerCongr e.toRingEquiv
  commutes' r := by ext; exact e.commutes r
