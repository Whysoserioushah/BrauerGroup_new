import Mathlib

namespace RingCon
variable {α R : Type*}

instance [Semiring α] [NonAssocSemiring R] [Module α R] [IsScalarTower α R R]
    (c : RingCon R) : Module α c.Quotient where
  zero_smul x := by
    induction x using Quotient.inductionOn' with | h a =>
    change Quotient.mk'' _ = Quotient.mk'' _
    simp [zero_smul α a]
  add_smul r1 r2 x := by
    induction x using Quotient.inductionOn' with | h a =>
    change Quotient.mk'' _ = Quotient.mk'' _
    simp [add_smul]

end RingCon
