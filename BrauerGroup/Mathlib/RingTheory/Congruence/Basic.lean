import Mathlib.Algebra.Module.Defs
import Mathlib.RingTheory.Congruence.Basic

namespace RingCon
variable {α R : Type*}

instance [Semiring α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : Module α c.Quotient where
  zero_smul x := by
    induction x using Quotient.ind
    simp
    sorry
  add_smul := sorry

end RingCon
