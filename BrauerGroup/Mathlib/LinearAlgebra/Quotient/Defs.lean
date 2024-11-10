import Mathlib.LinearAlgebra.Quotient.Defs

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)

@[elab_as_elim]
theorem Quotient.induction_on {C : M ⧸ p → Prop} (x : M ⧸ p) (H : ∀ z, C (Submodule.Quotient.mk z)) :
    C x := Quotient.inductionOn' x H

end Submodule
