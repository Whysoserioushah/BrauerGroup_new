module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
## rank of the endomorphism ring

Also `Module.Basis.endRingEquivMatrixOpposite`, the `RingEquiv` version of `algEquivMatrix`
over a not necessarily commutative semiring.
-/

@[expose] public section

variable {ι A M : Type*} [Fintype ι] [DecidableEq ι] [Semiring A] [AddCommMonoid M] [Module A M]

/-- The `RingEquiv` version of `algEquivMatrix` over a not necessarily commutative semiring:
a finite basis of `M` over `A` identifies the endomorphism ring of `M` with the matrix ring
over the *opposite* of `A`. The opposite is forced already for `M = A`, where an endomorphism
commutes with all left multiplications and hence is a right multiplication
(`AlgEquiv.moduleEndSelf`). -/
noncomputable def Module.Basis.endRingEquivMatrixOpposite (b : Module.Basis ι A M) :
    Module.End A M ≃+* Matrix ι ι Aᵐᵒᵖ :=
  b.equivFun.conjRingEquiv.trans <| (endVecRingEquivMatrixEnd ι A A).trans
    (AlgEquiv.moduleEndSelf ℕ).symm.toRingEquiv.mapMatrix
