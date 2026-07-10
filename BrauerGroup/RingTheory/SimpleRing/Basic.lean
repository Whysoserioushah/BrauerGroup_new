module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Algebra homomorphisms out of simple rings

An algebra homomorphism out of a simple ring is injective, and hence bijective when source
and target are finite-dimensional of the same dimension.
-/

@[expose] public section

variable {F A B : Type*} [Field F] [Ring A] [Algebra F A] [Ring B] [Algebra F B]

/-- An algebra homomorphism from a simple ring to a nontrivial ring is injective. -/
theorem AlgHom.injective_of_isSimpleRing [IsSimpleRing A] [Nontrivial B] (f : A →ₐ[F] B) :
    Function.Injective f :=
  (IsSimpleRing.injective_ringHom_or_subsingleton_codomain f.toRingHom).resolve_right
    (not_subsingleton B)

/-- An algebra homomorphism from a simple ring to a nontrivial algebra of the same finite
dimension is bijective. -/
theorem AlgHom.bijective_of_finrank_eq [IsSimpleRing A] [Nontrivial B]
    [FiniteDimensional F A] (f : A →ₐ[F] B)
    (h : Module.finrank F A = Module.finrank F B) : Function.Bijective f :=
  have : Module.Finite F B := Module.finite_of_finrank_pos (h ▸ Module.finrank_pos)
  ⟨f.injective_of_isSimpleRing,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) h).1
      f.injective_of_isSimpleRing⟩
