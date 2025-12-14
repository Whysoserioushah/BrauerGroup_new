import Mathlib.RingTheory.MatrixAlgebra

open scoped TensorProduct

def matrixEquivTensor' (n R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Fintype n] [DecidableEq n] :
    Matrix n n A ≃ₐ[A] A ⊗[R] Matrix n n R :=
  .symm <| .ofRingEquiv (f := (matrixEquivTensor n R A).symm) fun a ↦ by
    ext i j
    simp [matrixEquivTensor, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.one_apply]

@[simp] lemma matrixEquivTensor'_symm_apply (n R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [Fintype n] [DecidableEq n] (a : A) (m : Matrix n n R) :
    (matrixEquivTensor' n R A).symm (a ⊗ₜ m) = a • (m.map (algebraMap R A)) := rfl
