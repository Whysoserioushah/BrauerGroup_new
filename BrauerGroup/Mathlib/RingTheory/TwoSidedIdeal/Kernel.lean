import Mathlib.RingTheory.TwoSidedIdeal.Kernel

variable {R S : Type*} [Ring R] [Ring S]

namespace TwoSidedIdeal

lemma injective_iff_ker_eq_bot {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) :
    Function.Injective f ↔ TwoSidedIdeal.ker f = ⊥ := by
  rw [Function.Injective, eq_bot_iff, le_iff]
  change _ ↔ ∀ _, _
  simp only [SetLike.mem_coe, mem_ker]
  constructor
  · intro h x hx
    specialize @h x 0 (by simpa using hx)
    rw [h]; rfl
  · intro h a b hab
    specialize h (a - b) (by rwa [map_sub, sub_eq_zero])
    rw [← sub_eq_zero]
    exact h

end TwoSidedIdeal
