import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

variable {R : Type*} [NonUnitalSemiring R]

@[simp] lemma NonUnitalSubsemiring.carrier_eq (S : NonUnitalSubsemiring R) : S.carrier = S := rfl
