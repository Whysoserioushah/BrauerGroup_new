import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Basic

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

open TensorProduct MulOpposite

/-- `A` as a `A ⊗[R] Aᵐᵒᵖ`-module (or equivalently, an `A`-`A` bimodule). -/
noncomputable abbrev instModuleTensorProductMop :
  Module (A ⊗[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module

/-- The canonical map from `A ⊗[R] Aᵐᵒᵖ` to `Module.End R A` where
  `a ⊗ b` maps to `f : x ↦ a * x * b`. -/
noncomputable abbrev AlgHom.mulLeftRight : (A ⊗[R] Aᵐᵒᵖ) →ₐ[R] Module.End R A :=
  letI : Module (A ⊗[R] Aᵐᵒᵖ) A := TensorProduct.Algebra.module
  letI : IsScalarTower R (A ⊗[R] Aᵐᵒᵖ) A := {
    smul_assoc := fun r ab a ↦ by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  Algebra.lsmul R (A := A ⊗[R] Aᵐᵒᵖ) R A

lemma AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) (x : A) :
    AlgHom.mulLeftRight R A (a ⊗ₜ b) x = a * x * b.unop := by
  simp only [Algebra.lsmul_coe]
  change TensorProduct.Algebra.moduleAux _ _ = _
  simp [TensorProduct.Algebra.moduleAux, ← mul_assoc]

/-- An Azumaya algebra is a finitely generated, projective and faithful R-algebra where
  `AlgHom.mulLeftRight` is an isomorphism. -/
class IsAzumaya extends Module.Projective R A, FaithfulSMul R A, Module.Finite R A : Prop where
    bij : Function.Bijective <| AlgHom.mulLeftRight R A
