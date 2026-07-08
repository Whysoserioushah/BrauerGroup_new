module

public import Mathlib
public import BrauerGroup.Algebra.BrauerGroup.Basic
public import BrauerGroup.Algebra.Central.Matrix
public import BrauerGroup.RingTheory.Finiteness.Basic

/-!
# The Brauer group of a finite field is trivial

By Wedderburn–Artin, every central simple algebra over a finite field `K` is a matrix
algebra over a finite central division algebra `D`; Wedderburn's little theorem makes `D`
a field, and centrality forces `D = K`.
-/

@[expose] public section

namespace BrauerGroup

universe u

variable (K : Type u) [Field K] [Finite K]

theorem eq_one_of_finite (x : BrauerGroup K) : x = 1 := by
  induction x using BrauerGroup.induction with | h A =>
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, _, _, ⟨iso⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing K (R := A)
  have : Module.Finite K (Matrix (Fin n) (Fin n) D) := Module.Finite.equiv iso.toLinearEquiv
  have : Module.Finite K D := Module.finite_of_matrix (Fin n) (Fin n)
  have : Finite D := Module.finite_iff_finite.1 ‹_›
  have : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) := .of_algEquiv K A _ iso
  have hD : Algebra.IsCentral K D := .of_matrix (Fin n)
  -- Wedderburn's little theorem makes `D` a (commutative) field, so its center is
  -- everything; centrality then identifies `D` with `K`.
  have htop : Subalgebra.center K D = ⊤ := SetLike.ext fun x ↦
    ⟨fun _ ↦ trivial, fun _ ↦ Subalgebra.mem_center_iff.mpr fun b => mul_comm b x⟩
  have e : D ≃ₐ[K] K := Subalgebra.topEquiv.symm.trans <|
    (Subalgebra.equivOfEq ⊤ ⊥ (htop.symm.trans hD.center_eq_bot)).trans <| Algebra.botEquiv K D
  rw [mk_congr iso, mk_congr (e.mapMatrix (m := Fin n)), mk_matrix_eq_one]

instance instUniqueOfFinite : Unique (BrauerGroup K) where
  default := 1
  uniq := eq_one_of_finite K

end BrauerGroup
