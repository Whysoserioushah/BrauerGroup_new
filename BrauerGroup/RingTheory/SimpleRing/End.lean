module

public import BrauerGroup.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Simplicity of endomorphism rings

The endomorphism ring of a nontrivial finite free module over a simple ring satisfying the
strong rank condition is simple: a basis identifies it with a matrix ring over the opposite
ring (`Module.Basis.endRingEquivMatrixOpposite`), and matrix rings over simple rings are
simple.
-/

@[expose] public section

/-- The endomorphism ring of a nontrivial finite free module over a simple ring satisfying
the strong rank condition is simple. -/
instance Module.End.instIsSimpleRing (R M : Type*) [Ring R] [StrongRankCondition R]
    [IsSimpleRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] [Nontrivial M] :
    IsSimpleRing (Module.End R M) :=
  have : NeZero (Module.finrank R M) := ⟨fun h ↦ not_subsingleton M
    ((Module.finrank_eq_zero_iff_of_free R M).1 h)⟩
  .of_ringEquiv (Module.finBasis R M).endRingEquivMatrixOpposite.symm inferInstance
