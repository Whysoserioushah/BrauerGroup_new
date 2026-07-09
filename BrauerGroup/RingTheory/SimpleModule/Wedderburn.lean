module

public import BrauerGroup.Data.Matrix.Composition
public import BrauerGroup.RingTheory.Finiteness.Basic
public import BrauerGroup.RingTheory.Morita.End

/-!
# Uniqueness in the Wedderburn–Artin theorem

Mathlib's `IsSimpleRing.exists_algEquiv_matrix_divisionRing` provides the existence half of
the Wedderburn–Artin theorem. This file provides the uniqueness half: in a decomposition
`A ≃ₐ[k] Matrix (Fin n) (Fin n) D` of a finite-dimensional algebra with `D` a division
algebra, both `D` (up to `k`-algebra isomorphism, `Matrix.divisionRing_unique`) and `n`
(`Matrix.size_unique`) are determined by `A`.
-/

@[expose] public section

namespace IsSimpleRing

universe u v w

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Uniqueness of the division algebra in the Wedderburn–Artin theorem: two matrix-algebra
presentations of the same finite-dimensional algebra have isomorphic underlying division
algebras. -/
@[stacks 074E "uniqueness of the division algebra"]
theorem wedderburn_artin_divisionring_unique {n n' : ℕ} [NeZero n] [NeZero n']
    {D : Type w} [DivisionRing D] [Algebra k D] {D' : Type w} [DivisionRing D'] [Algebra k D']
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    Nonempty (D ≃ₐ[k] D') := by
  have : IsSimpleRing A := .of_ringEquiv wdb.symm.toRingEquiv inferInstance
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k A (Fin n → D) :=
    IsSimpleRing.isScalarTower_compHom_pi k A D wdb
  haveI : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A D wdb
  obtain ⟨iso⟩ := end_simple_mod_of_wedderburn' k A n D wdb (Fin n → D)
  obtain ⟨iso'⟩ := end_simple_mod_of_wedderburn' k A n' D' wdb' (Fin n → D)
  exact ⟨AlgEquiv.op.symm (iso.symm.trans iso')⟩

/-- Uniqueness of the matrix size in the Wedderburn–Artin theorem. -/
@[stacks 074E "uniqueness of the matrix size"]
theorem wedderburn_artin_size_unique {n n' : ℕ} [NeZero n] [NeZero n']
    {D : Type w} [DivisionRing D] [Algebra k D] {D' : Type w} [DivisionRing D'] [Algebra k D']
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    n = n' := by
  obtain ⟨iso⟩ := wedderburn_artin_divisionring_unique k A wdb wdb'
  haveI inst1 : Module.Finite k (Matrix (Fin n) (Fin n) D) := wdb.toLinearEquiv.finiteDimensional
  let e : Matrix (Fin n) (Fin n) D ≃ₐ[k] Matrix (Fin n') (Fin n') D :=
    wdb.symm.trans (wdb'.trans iso.symm.mapMatrix)
  have : Module.Finite k D := Module.finite_of_matrix (Fin n) (Fin n)
  have : 0 ≠ Module.finrank k D := ne_of_lt <| Module.finrank_pos
  have eq3 : n * n * Module.finrank k D = n' * n' * Module.finrank k D := by
    convert e.toLinearEquiv.finrank_eq <;> simp [Module.finrank_matrix]
  simpa [this.symm,  Nat.mul_self_inj] using eq3

/-- Two finite-dimensional simple algebras whose matrix algebras are isomorphic are matrix
algebras over a common division algebra. Note that finite-dimensionality of `B` follows
from the isomorphism, and no centrality is assumed. -/
theorem wedderburn_artin_common_divisionring {n m : ℕ} [NeZero n] [NeZero m]
    {B : Type v} [Ring B] [Algebra k B] [IsSimpleRing A] [IsSimpleRing B]
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) :
    ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D) (p q : ℕ) (_ : NeZero p) (_ : NeZero q),
      Nonempty (A ≃ₐ[k] Matrix (Fin p) (Fin p) D) ∧
        Nonempty (B ≃ₐ[k] Matrix (Fin q) (Fin q) D) := by
  have : IsArtinianRing A := .of_finite k A
  have : Module.Finite k (Matrix (Fin m) (Fin m) B) := .equiv e.toLinearEquiv
  have : Module.Finite k B := Module.finite_of_matrix (Fin m) (Fin m)
  have : IsArtinianRing B := .of_finite k B
  obtain ⟨p, hp, D, _, _, ⟨wdbA⟩⟩ := exists_algEquiv_matrix_divisionRing k (R := A)
  obtain ⟨q, hq, D', _, _, ⟨wdbB⟩⟩ := exists_algEquiv_matrix_divisionRing k (R := B)
  obtain ⟨isoD⟩ := wedderburn_artin_divisionring_unique k (Matrix (Fin n) (Fin n) A)
    (wdbA.mapMatrix.trans <| Matrix.compFinAlgEquiv n p D k)
    (e.trans <| wdbB.mapMatrix.trans <| Matrix.compFinAlgEquiv m q D' k)
  exact ⟨D, _, _, p, q, hp, hq, ⟨wdbA⟩, ⟨wdbB.trans isoD.symm.mapMatrix⟩⟩

end IsSimpleRing
