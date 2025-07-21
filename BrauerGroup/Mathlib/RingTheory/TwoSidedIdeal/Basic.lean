import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.TwoSidedIdeal.Basic

namespace TwoSidedIdeal
variable {R : Type*}

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] {I : TwoSidedIdeal R} {x : R}

lemma smul_mem (r : R) (hx : x ∈ I) : r • x ∈ I := by
  simpa using I.ringCon.mul (I.ringCon.refl r) hx

end NonUnitalNonAssocRing

section Ring
variable [Ring R] {I : TwoSidedIdeal R}

instance : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; simp
  mul_smul x y z := by ext; simp [mul_assoc]
  smul_zero x := by ext; simp
  zero_smul x := by ext; simp
  add_smul x y z := by ext; simp [left_distrib]
  smul_add x y z := by ext; simp [right_distrib]

end Ring
end TwoSidedIdeal
