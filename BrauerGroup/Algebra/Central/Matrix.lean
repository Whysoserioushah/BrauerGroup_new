module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Data.Matrix.Basic

/-!
# Centrality descends from matrix algebras

Mathlib's `Algebra.IsCentral.matrix` shows that matrix algebras over central algebras are
central. This file provides the reverse direction: if `Matrix n n D` is central then so is
`D` (`Algebra.IsCentral.of_matrix`) — the entries of a central scalar matrix are central.
-/

@[expose] public section

namespace Algebra.IsCentral

theorem of_matrix {K D : Type*} [CommSemiring K] [Semiring D] [Algebra K D]
    (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
    [h : Algebra.IsCentral K (Matrix n n D)] : Algebra.IsCentral K D where
  out d hd := by
    obtain ⟨i⟩ := ‹Nonempty n›
    have hscalar : Matrix.scalar n d ∈ Subalgebra.center K (Matrix n n D) :=
      Subalgebra.mem_center_iff.mpr fun M =>
        (Matrix.scalar_commute d
          (fun r => (Subalgebra.mem_center_iff.mp hd r).symm) M).symm
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (h.out hscalar)
    exact Algebra.mem_bot.mpr ⟨c, by
      simpa [Matrix.algebraMap_matrix_apply] using congrFun (congrFun hc i) i⟩

end Algebra.IsCentral
