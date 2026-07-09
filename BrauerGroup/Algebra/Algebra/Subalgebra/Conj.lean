module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Conjugates of a subalgebra

For a unit `x` of an algebra `A`, conjugation `b ↦ x * b * x⁻¹` is an algebra automorphism
of `A` (`MulSemiringAction.toAlgEquiv` for the conjugation action of `ConjAct Aˣ`), so the
image `Subalgebra.conj B x` of a subalgebra `B` is again a subalgebra, isomorphic to `B` via
`Subalgebra.conjEquiv`. We record the transfer lemmas: dimension, simplicity, and
compatibility with centralizers.
-/

@[expose] public section

namespace Subalgebra

section Semiring

variable {R A A' : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring A']
  [Algebra R A']

/-- The image of a centralizer under an algebra isomorphism is the centralizer of the
image. -/
lemma map_centralizer (e : A ≃ₐ[R] A') (S : Subalgebra R A) :
    (Subalgebra.centralizer R (S : Set A)).map (e : A →ₐ[R] A') =
      Subalgebra.centralizer R (S.map (e : A →ₐ[R] A') : Set A') := by
  ext y
  simp only [mem_map, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc b hb]
  · intro h
    refine ⟨e.symm y, fun b hb ↦ e.injective ?_, e.apply_symm_apply y⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h (e b) ⟨b, hb, rfl⟩

variable (B : Subalgebra R A) (x : Aˣ)

/-- The conjugate of a subalgebra by a unit: `B.conj x` consists of `x * b * x⁻¹` for
`b ∈ B`. -/
def conj : Subalgebra R A :=
  B.map (MulSemiringAction.toAlgEquiv R A (ConjAct.toConjAct x) : A →ₐ[R] A)

lemma mem_conj {y : A} : y ∈ B.conj x ↔ ∃ b ∈ B, y = ↑x * b * ↑x⁻¹ := by
  simp [conj, ConjAct.units_smul_def, eq_comm]

/-- A subalgebra is isomorphic to its conjugates. -/
def conjEquiv : B ≃ₐ[R] B.conj x :=
  AlgEquiv.subalgebraMap (MulSemiringAction.toAlgEquiv R A (ConjAct.toConjAct x)) B

lemma finrank_conj : Module.finrank R (B.conj x) = Module.finrank R B :=
  (B.conjEquiv x).symm.toLinearEquiv.finrank_eq

/-- Conjugation commutes with taking centralizers. -/
lemma conj_centralizer :
    Subalgebra.centralizer R (B.conj x : Set A) =
      (Subalgebra.centralizer R (B : Set A)).conj x :=
  (map_centralizer _ B).symm

end Semiring

lemma isSimpleRing_conj_iff {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (B : Subalgebra R A) (x : Aˣ) : IsSimpleRing (B.conj x) ↔ IsSimpleRing B :=
  ⟨fun h ↦ by exact .of_ringEquiv (B.conjEquiv x).symm.toRingEquiv h,
    fun h ↦ by exact .of_ringEquiv (B.conjEquiv x).toRingEquiv h⟩

end Subalgebra
