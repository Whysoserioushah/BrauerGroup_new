module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.RingTheory.Morita.Matrix
public import Mathlib.RingTheory.SimpleRing.DivisionRing

/-!
## The transfer of simple modules along the wedderburn isomorphism
-/

@[expose] public section

universe u v w

instance {n : ℕ} [NeZero n] (D : Type v) [DivisionRing D] :
    IsSimpleModule (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  IsSimpleModule.obj_of_isEquivalence
    (ModuleCat.matrixEquivalence D (ι := Fin n) 0).functor (ModuleCat.of D D)

@[stacks 074E "(4) first part"]
lemma simple_mod_of_wedderburn (k A : Type*) [Field k] [Ring A] [Algebra k A] {n : ℕ} [NeZero n]
    (D : Type w) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    letI : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
    IsSimpleModule A (Fin n → D) :=
  IsSimpleModule.obj_of_isEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv wdb.toRingEquiv).functor
    (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → D))
