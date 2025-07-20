import Mathlib.RingTheory.TwoSidedIdeal.Lattice

namespace TwoSidedIdeal
variable {R : Type*} [NonUnitalNonAssocRing R] {I J : TwoSidedIdeal R} {x : R}

@[simp] lemma ringCon_inj : I.ringCon = J.ringCon ↔ I = J := ringCon_injective.eq_iff

@[simp] lemma ringCon_eq_top : I.ringCon = ⊤ ↔ I = ⊤ := by rw [← top_ringCon, ringCon_inj]

end TwoSidedIdeal
