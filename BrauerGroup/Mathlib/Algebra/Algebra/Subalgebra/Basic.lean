import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace Subalgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {L S T U : Subalgebra R A}

lemma le_centralizer_self : L ≤ centralizer R L ↔ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := forall₂_swap
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {S T U : Subalgebra R A}

@[simp] lemma inclusion_comp_inclusion (hST : S ≤ T) (hTU : T ≤ U) :
    (inclusion hTU).comp (inclusion hST) = inclusion (hST.trans hTU) := rfl

end Subalgebra
