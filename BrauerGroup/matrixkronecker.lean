import Mathlib.Data.Matrix.Composition
import Mathlib.RingTheory.MatrixAlgebra

open scoped TensorProduct

noncomputable def MatrixAlgebra.TensorEquiv (K A B : Type*) [CommSemiring K] [Semiring A] [Algebra K A] [Semiring B] [Algebra K B] (m n)
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m A ⊗[K] Matrix n n B ≃ₐ[K] Matrix (m × n) (m × n) (A ⊗[K] B) :=
  Algebra.TensorProduct.congr (matrixEquivTensor _ _ _) (matrixEquivTensor _ _ _)
    |>.trans <| (Algebra.TensorProduct.tensorTensorTensorComm K _ _ _ _)
    |>.trans <|
      .trans (Algebra.TensorProduct.congr .refl <|
        Algebra.TensorProduct.comm K _ _
          |>.trans <| (matrixEquivTensor _ _ _).symm
          |>.trans <| Matrix.compAlgEquiv _ _ K K
      ) <| (matrixEquivTensor ..).symm
