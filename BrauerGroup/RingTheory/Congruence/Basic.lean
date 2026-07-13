module

public import Mathlib.RingTheory.Congruence.Basic

@[expose] public section

open Function

namespace RingCon
variable {α R : Type*} [Semiring α] [NonAssocSemiring R] [Module α R] [IsScalarTower α R R]
  {c d : RingCon R}

instance : Module α c.Quotient where
  zero_smul x := by induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp
  add_smul r s x := by induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp [add_smul]

variable (α) in
/-- The quotient map as a linear map. -/
def mkL (c : RingCon R) : R →ₗ[α] c.Quotient where
  __ := c.mk'
  map_smul' _ _ := rfl

end RingCon
