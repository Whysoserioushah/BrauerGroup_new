module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
## rank of the endomorphism ring
-/

@[expose] public section

lemma Module.End.finrank_eq {R M : Type*} [CommSemiring R] [StrongRankCondition R] [AddCommMonoid M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (n : ℕ) (hn : Module.finrank R M = n) :
    Module.finrank R (Module.End R M) = n ^ 2 := by
  simp [(algEquivMatrix (Module.finBasisOfFinrankEq R M hn)).toLinearEquiv.finrank_eq,
    finrank_matrix, pow_two]
