import Mathlib.RingTheory.NonUnitalSubring.Defs

variable {R : Type*} [NonUnitalRing R]

@[simp] lemma NonUnitalSubring.carrier_eq (S : NonUnitalSubring R) : S.carrier = S := rfl
