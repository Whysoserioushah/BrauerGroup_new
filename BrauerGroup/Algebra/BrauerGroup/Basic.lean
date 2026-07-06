module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import BrauerGroup.LinearAlgebra.Matrix.toLin
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct

/-!
## Multiplication in Brauer group
-/

@[expose] public section

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

open scoped TensorProduct

section mul_inv

lemma mulLeftRight_bijective_of_simple (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let e := algEquivMatrix (Module.finBasisOfFinrankEq k A hn)
  refine ⟨RingHom.injective _, LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight k A).toLinearMap) ?_|>.1 <| RingHom.injective _⟩
  simp [Module.End.finrank_eq, MulOpposite.finrank, pow_two]

@[stacks 074I]
noncomputable def centralSimpleTensorOp (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) : A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  (AlgEquiv.ofBijective _ (mulLeftRight_bijective_of_simple n hn)).trans <|
    algEquivMatrix (Module.finBasisOfFinrankEq k A hn)

end mul_inv
