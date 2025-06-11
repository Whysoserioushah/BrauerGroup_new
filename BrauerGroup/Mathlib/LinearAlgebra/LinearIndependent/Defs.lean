import Mathlib.LinearAlgebra.LinearIndependent.Defs

variable {ι R M : Type*} {v : ι → M} [Semiring R] [AddCommMonoid M] [Module R M]

-- TODO: Replace `linearIndependent_iff_finset_linearIndependent`
lemma linearIndependent_iff_linearIndepOn_finset :
    LinearIndependent R v ↔ ∀ s : Finset ι, LinearIndepOn R v s :=
  linearIndependent_iff_finset_linearIndependent
