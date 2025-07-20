import Mathlib.LinearAlgebra.LinearIndependent.Defs

variable {ι R M : Type*} {v : ι → M} [Semiring R] [AddCommMonoid M] [Module R M]

-- TODO: Replace `linearIndependent_iff_finset_linearIndependent`
lemma linearIndependent_iff_linearIndepOn_finset :
    LinearIndependent R v ↔ ∀ s : Finset ι, LinearIndepOn R v s :=
  linearIndependent_iff_finset_linearIndependent

-- This already exists in future mathlib
lemma linearIndepOn_finset_iffₛ {s : Finset ι} :
    LinearIndepOn R v s ↔
      ∀ (f g : ι → R), ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i ∈ s, f i = g i := sorry
