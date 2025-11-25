import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Congruence.Basic

open Function

namespace RingCon
variable {α R : Type*}

section Semiring
variable [Semiring α] [NonAssocSemiring R] [Module α R] [IsScalarTower α R R] {c d : RingCon R}

instance : Module α c.Quotient where
  zero_smul x := by induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp
  add_smul r s x := by induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp [add_smul]

variable (α) in
/-- The quotient map as a linear map. -/
def mkL (c : RingCon R) : R →ₗ[α] c.Quotient where
  __ := c.mk'
  map_smul' _ _ := rfl

end Semiring

section CommSemiring
variable [CommSemiring α] [Semiring R] [Algebra α R] [IsScalarTower α R R] {c : RingCon R}

instance : Algebra α c.Quotient where
  algebraMap := c.mk'.comp <| algebraMap α R
  smul_def' r x := by induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp [← Algebra.smul_def]
  commutes' r x := by
    induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp [Algebra.commutes]

lemma algebraMap_def : algebraMap α c.Quotient = c.mk'.comp (algebraMap α R) := rfl

variable (α) in
/-- The quotient map as a linear map. -/
def mkA (c : RingCon R) : R →ₐ[α] c.Quotient where
  __ := c.mk'
  __ := c.mkL α
  commutes' := by simp [algebraMap_def]

end CommSemiring
end RingCon
