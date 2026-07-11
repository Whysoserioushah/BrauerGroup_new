module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Field

/-!
# Algebra homomorphisms out of simple rings

An algebra homomorphism out of a simple ring is injective, and hence bijective when source
and target are finite-dimensional of the same dimension.

We also provide `IsSimpleRing.toField`, the `Field` structure on a commutative simple ring,
built over the canonical `CommRing` instance so that no instance diamonds arise.
-/

@[expose] public section

/-- A commutative simple ring is a field: every nonzero element generates the unit ideal.
Built over the canonical `CommRing` instance, so no instance diamonds arise; use as
`letI : Field R := IsSimpleRing.toField R` at use sites. -/
noncomputable abbrev IsSimpleRing.toField (R : Type*) [CommRing R] [IsSimpleRing R] :
    Field R :=
  Field.ofIsUnitOrEqZero fun a ↦ by
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inr rfl
    · obtain ⟨b, hb⟩ := ((isSimpleRing_iff_isField R).mp ‹_›).mul_inv_cancel ha
      exact Or.inl ⟨⟨a, b, hb, by rwa [mul_comm] at hb⟩, rfl⟩

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
