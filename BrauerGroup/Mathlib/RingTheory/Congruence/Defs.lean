import Mathlib.RingTheory.Congruence.Defs

variable {R : Type*} [Ring R]

namespace RingCon

@[elab_as_elim]
lemma quot_ind (r : RingCon R) {motive : r.Quotient → Prop}
  (basic : ∀ (x : R), motive (r.mk' x)) : ∀ (x : r.Quotient), motive x := by
  intro x
  induction x using Quotient.inductionOn' with | h x =>
  exact basic x

end RingCon
