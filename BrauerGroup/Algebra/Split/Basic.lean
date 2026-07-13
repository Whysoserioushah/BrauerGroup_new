module

public import BrauerGroup.Algebra.BrauerGroup.BaseChange
public import BrauerGroup.RingTheory.SimpleModule.Wedderburn
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Splitting fields of algebras

`Algebra.IsSplit K A L` says that the field extension `L` of `K` *splits* the
`K`-algebra `A`, i.e. `L ⊗[K] A` is isomorphic to a matrix algebra over `L`.

This replaces both the old Prop-valued `isSplit` and the data-valued `split`
structure from `BrauerGroup/SplittingOfCSA.lean`.
-/

@[expose] public section

universe u v w w'

open scoped TensorProduct

namespace Algebra

section General

variable (K : Type u) (A : Type v) (L : Type w)
variable [Field K] [Ring A] [Algebra K A] [Field L] [Algebra K L]

/-- A field extension `L` of `K` *splits* a `K`-algebra `A` if `L ⊗[K] A` is isomorphic
to a (nontrivial) matrix algebra over `L`. -/
def IsSplit (L : Type w) [CommRing L] [Algebra K L] : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

variable {K A L}

theorem IsSplit.of_algEquiv (L : Type w) [CommRing L] [Algebra K L]
    {B : Type v} [Ring B] [Algebra K B]
    (h : IsSplit K A L) (e : A ≃ₐ[K] B) : IsSplit K B L := by
  obtain ⟨n, hn, ⟨iso⟩⟩ := h
  exact ⟨n, hn, ⟨(TensorProduct.congr AlgEquiv.refl e.symm).trans iso⟩⟩

/-- Splitting fields are upward closed: if `L` splits `A` then so does any
extension `L'` of `L`. -/
theorem IsSplit.of_isScalarTower {L : Type w} [CommRing L] [Algebra K L] (L' : Type w')
    [CommRing L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (h : IsSplit K A L) : IsSplit K A L' := by
  obtain ⟨n, hn, ⟨iso⟩⟩ := h
  refine ⟨n, hn, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L L' L').symm AlgEquiv.refl).trans
    <| (Algebra.TensorProduct.assoc K L L' L' L A).trans
    <| (Algebra.TensorProduct.congr AlgEquiv.refl iso).trans
    <| (BrauerGroup.matrixEquivTensorL L L' (Fin n) L').symm

/-- Splitting is invariant under isomorphism of the splitting field, across universes:
transport the `L`-algebra structure of `L'` along `e` and ascend the (trivial) tower. -/
lemma IsSplit.of_algEquiv' (L : Type w) (L' : Type w') [CommRing L] [CommRing L'] [Algebra K L]
    [Algebra K L'] (h : IsSplit K A L) (e : L ≃ₐ[K] L') : IsSplit K A L' := by
  letI : Algebra L L' := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K L L' := .of_algebraMap_eq fun c ↦ (e.commutes c).symm
  exact h.of_isScalarTower L'

/-- Any algebraically closed extension splits a finite-dimensional central simple algebra. -/
theorem IsSplit.of_isAlgClosed [IsAlgClosed L] [IsSimpleRing A] [Algebra.IsCentral K A]
    [FiniteDimensional K A] : IsSplit K A L := by
  obtain ⟨n, hn, ⟨iso⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (F := L) (R := L ⊗[K] A)
  exact ⟨n, hn.out, ⟨iso⟩⟩

end General

section CentralSimple

open BrauerGroup

variable (K : Type u) (A : Type u) (L : Type (max u v))
variable [Field K] [Ring A] [Algebra K A] [IsSimpleRing A] [Algebra.IsCentral K A]
  [FiniteDimensional K A] [Field L] [Algebra K L]

/-- A field extension `L/K` splits a central simple algebra `A` if and only if the Brauer
class of `A` is killed by base change to `L`. -/
theorem isSplit_iff_baseChange_eq_one :
    IsSplit K A L ↔ baseChange K L (BrauerGroup.mk K A) = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨n, hn, ⟨iso⟩⟩ := h
    have : NeZero n := ⟨hn⟩
    rw [baseChange_mk, mk_congr iso, mk_matrix_eq_one]
  · rw [baseChange_mk, ← mk_self_eq_one, mk_eq_mk] at h
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
    have : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite L _
    obtain ⟨p, hp, D, _, _, ⟨wdb⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing L (R := L ⊗[K] A)
    have : NeZero (n * p) := ⟨Nat.mul_ne_zero hn hp.out⟩
    have : NeZero m := ⟨hm⟩
    have e' : Matrix (Fin (n * p)) (Fin (n * p)) D ≃ₐ[L] Matrix (Fin m) (Fin m) L :=
      (Matrix.compFinAlgEquiv n p D L).symm.trans <| wdb.symm.mapMatrix.trans e
    obtain ⟨isoD⟩ := IsSimpleRing.wedderburn_artin_divisionring_unique L
      (Matrix (Fin m) (Fin m) L) e'.symm (ULift.algEquiv (R := L) (A := L)).symm.mapMatrix
    exact ⟨p, hp.out, ⟨wdb.trans (isoD.trans ULift.algEquiv).mapMatrix⟩⟩

/-- If `L` splits `A` then `L` splits the opposite algebra: inversion in the Brauer group
preserves the relative Brauer group. -/
theorem IsSplit.op (h : IsSplit K A L) : IsSplit K Aᵐᵒᵖ L := by
  rw [isSplit_iff_baseChange_eq_one] at h ⊢
  rw [← BrauerGroup.mk_inv, map_inv, h, inv_one]

/-- A field splits a central simple algebra if and only if it splits any matrix algebra
over it. -/
theorem isSplit_matrix_iff (K : Type u) (A : Type v) [Field K] [Ring A] [Algebra K A]
    [Module.Finite K A] [IsSimpleRing A] [Algebra.IsCentral K A]
    (L : Type w) [Field L] [Algebra K L] (n : ℕ) (hn : n ≠ 0) :
    IsSplit K (Matrix (Fin n) (Fin n) A) L ↔ IsSplit K A L := by
  constructor
  · rintro ⟨m, hm, ⟨iso⟩⟩
    haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite L _
    obtain ⟨p, hp, D, _, _, ⟨wdb⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing L (R := L ⊗[K] A)
    have : NeZero (n * p) := ⟨Nat.mul_ne_zero hn hp.out⟩
    have : NeZero m := ⟨hm⟩
    have e' : Matrix (Fin (n * p)) (Fin (n * p)) D ≃ₐ[L] Matrix (Fin m) (Fin m) L :=
      (Matrix.compFinAlgEquiv n p D L).symm.trans <| wdb.symm.mapMatrix.trans <|
        (matrixBaseChange K L (Fin n) A).trans iso
    obtain ⟨isoD⟩ := IsSimpleRing.wedderburn_artin_divisionring_unique L
      (Matrix (Fin m) (Fin m) L) e'.symm (ULift.algEquiv (R := L) (A := L)).symm.mapMatrix
    exact ⟨p, hp.out, ⟨wdb.trans (isoD.trans ULift.algEquiv).mapMatrix⟩⟩
  · rintro ⟨m, hm, ⟨iso⟩⟩
    exact ⟨n * m, Nat.mul_ne_zero hn hm,
      ⟨(matrixBaseChange K L (Fin n) A).symm.trans <| iso.mapMatrix.trans <|
        Matrix.compFinAlgEquiv n m L L⟩⟩

/-- Splitting only depends on the Brauer class: two central simple algebras in the same
class have exactly the same splitting fields. -/
theorem isSplit_congr (K : Type u) (A B : Type v) [Field K] [Ring A] [Algebra K A]
    [Module.Finite K A] [IsSimpleRing A] [Algebra.IsCentral K A] [Ring B] [Algebra K B]
    [IsSimpleRing B] [Algebra.IsCentral K B] [FiniteDimensional K B]
    (L : Type w) [Field L] [Algebra K L]
    (h : BrauerGroup.mk K A = BrauerGroup.mk K B) :
    IsSplit K A L ↔ IsSplit K B L := by
  rw [mk_eq_mk] at h
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  rw [← isSplit_matrix_iff K A L n hn, ← isSplit_matrix_iff K B L m hm]
  exact ⟨fun hs ↦ hs.of_algEquiv _ e, fun hs ↦ hs.of_algEquiv _ e.symm⟩

end CentralSimple

namespace IsCentralSimple

/-! Numerical invariants of central simple algebras. Note that mathlib deliberately has no
`Algebra.IsCentralSimple` class (see the implementation notes in
`Mathlib/Algebra/Central/Defs.lean`); we use the namespace for the invariants of algebras
that are central simple. -/

variable (K : Type u) (A : Type v) [Field K] [Ring A] [Algebra K A]

/-- The degree of a central simple algebra `A` over `K`, i.e. the square root of its
dimension. For central simple `A` the dimension is a perfect square
(`Algebra.IsCentralSimple.isSquare_finrank`), so the square root is exact
(`Algebra.IsCentralSimple.degree_sq_eq_finrank`). -/
noncomputable def degree : ℕ := Nat.sqrt (Module.finrank K A)

/-- The dimension of a central simple algebra is a perfect square. -/
theorem isSquare_finrank [IsSimpleRing A] [Algebra.IsCentral K A] [FiniteDimensional K A] :
    IsSquare (Module.finrank K A) := by
  obtain ⟨n, hn, ⟨iso⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    (F := AlgebraicClosure K) (R := AlgebraicClosure K ⊗[K] A)
  refine ⟨n, ?_⟩
  rw [← Module.finrank_baseChange (R := AlgebraicClosure K) (S := K) (M' := A),
    iso.toLinearEquiv.finrank_eq]
  simp [Module.finrank_matrix]

theorem degree_sq_eq_finrank [IsSimpleRing A] [Algebra.IsCentral K A] [FiniteDimensional K A] :
    degree K A ^ 2 = Module.finrank K A := by
  obtain ⟨n, hn⟩ := isSquare_finrank K A
  rw [degree, hn, ← pow_two, Nat.sqrt_eq']

theorem degree_pos [Nontrivial A] [Module.Finite K A] : 0 < degree K A :=
  Nat.sqrt_pos.mpr Module.finrank_pos

instance instNeZeroDegree [Nontrivial A] [Module.Finite K A] : NeZero (degree K A) :=
  ⟨(degree_pos K A).ne'⟩

end IsCentralSimple

end Algebra
