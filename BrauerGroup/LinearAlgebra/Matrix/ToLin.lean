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

variable (R : Type*) [CommSemiring R] [Algebra R A] [Module R M] [IsScalarTower R A M]

/-- The `AlgEquiv` version of `Module.Basis.endRingEquivMatrixOpposite`, for a commutative
base `R` acting on `M` through `A`. -/
noncomputable def Module.Basis.endAlgEquivMatrixOpposite (b : Module.Basis ι A M) :
    Module.End A M ≃ₐ[R] Matrix ι ι Aᵐᵒᵖ :=
  ((AlgEquiv.ofRingEquiv (f := b.equivFun.conjRingEquiv) fun r ↦ LinearMap.ext fun v ↦ by
      simp only [Module.algebraMap_end_eq_smul_id]
      ext i
      have h : ∀ x, b.repr (r • b x) = r • Finsupp.single x 1 := fun x ↦ by
        rw [← algebraMap_smul A r (b x), map_smul, b.repr_self, algebraMap_smul]
      simp [h, Finsupp.single_apply, Algebra.smul_def, Algebra.commutes, mul_ite]).trans
    (endVecAlgEquivMatrixEnd (ι := ι) (R := R) (A := A) (M := A))).trans
    (AlgEquiv.mapMatrix (AlgEquiv.moduleEndSelf R).symm)
