import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace Subalgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {L : Subalgebra R A}

lemma le_centralizer_self : L ≤ centralizer R L ↔ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := forall₂_swap

end Subalgebra
