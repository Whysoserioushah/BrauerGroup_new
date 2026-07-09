module

public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Composition of `Fin`-indexed matrix algebras

`Matrix.compFinAlgEquiv`: nested matrix algebras collapse to a single matrix algebra,
`Mₘ(Mₙ(R)) ≃ₐ[K] M_{m·n}(R)`. This is `Matrix.compAlgEquiv` composed with reindexing along
`finProdFinEquiv`, a combination that otherwise gets inlined at every use site (including
mathlib's `IsBrauerEquivalent.trans`).
-/

@[expose] public section

/-- Nested `Fin`-indexed matrix algebras collapse to a single matrix algebra:
`Mₘ(Mₙ(R)) ≃ₐ[K] M_{m·n}(R)`. -/
def Matrix.compFinAlgEquiv (m n : ℕ) (R K : Type*) [CommSemiring K] [Semiring R]
    [Algebra K R] :
    Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R) ≃ₐ[K]
      Matrix (Fin (m * n)) (Fin (m * n)) R :=
  (Matrix.compAlgEquiv (Fin m) (Fin n) R K).trans (Matrix.reindexAlgEquiv K R finProdFinEquiv)
