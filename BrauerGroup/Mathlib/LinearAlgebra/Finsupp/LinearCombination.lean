import Mathlib.LinearAlgebra.Finsupp.LinearCombination

variable {α R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {v : α → M} {x : M}

lemma Submodule.mem_span_image_finset_iff_exists_fun {s : Finset α} :
    x ∈ span R (v '' s) ↔ ∃ c : α → R, ∑ i ∈ s, c i • v i = x := sorry
