import Mathlib.GroupTheory.Congruence.Defs

open Function

namespace Con
variable {M : Type*} [Mul M] {c d : Con M}

@[to_additive] lemma toSetoid_injective : Injective (toSetoid (M := M)) :=
  fun c d ↦ by cases c; congr!

-- TODO: Replace `toSetoid_inj`
@[to_additive (attr := simp)] lemma toSetoid_inj' : c.toSetoid = d.toSetoid ↔ c = d :=
  toSetoid_injective.eq_iff

@[to_additive (attr := simp)] lemma toSetoid_top : (⊤ : Con M).toSetoid = ⊤ := rfl

@[to_additive (attr := simp)] lemma toSetoid_eq_top : c.toSetoid = ⊤ ↔ c = ⊤ := by
  rw [← toSetoid_top, toSetoid_inj']

end Con
