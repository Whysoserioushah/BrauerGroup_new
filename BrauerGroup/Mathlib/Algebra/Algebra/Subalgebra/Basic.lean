import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace Subalgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {S T U : Subalgebra R A}

@[simp] lemma inclusion_comp_inclusion (hST : S ≤ T) (hTU : T ≤ U) :
    (inclusion hTU).comp (inclusion hST) = inclusion (hST.trans hTU) := rfl

end Subalgebra
