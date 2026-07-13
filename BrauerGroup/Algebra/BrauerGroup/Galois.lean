module

public import BrauerGroup.Algebra.BrauerGroup.Relative.Basic
public import BrauerGroup.Algebra.Split.DivisionRing

/-!
# The Brauer group is covered by relative Brauer groups of finite Galois extensions

Every Brauer class of a field `k` is split by a finite Galois subextension of a fixed
algebraic closure, hence lies in the corresponding relative Brauer group
(`BrauerGroup.exists_finite_galois_mem`). Consequently the relative Brauer groups of the
finite Galois subextensions of `AlgebraicClosure k` cover all of `Br k`
(`BrauerGroup.iSup_relativeBrGroup_eq_top`).

This is the colimit-free description of `Br k` as a directed union of relative Brauer
groups, the source-side input to the invariant map.
-/

@[expose] public section

namespace BrauerGroup

variable (k : Type*) [Field k]

/-- Every Brauer class lies in the relative Brauer group of some finite Galois
subextension of the algebraic closure. -/
theorem exists_finite_galois_mem (x : BrauerGroup k) :
    ∃ N : IntermediateField k (AlgebraicClosure k), FiniteDimensional k N ∧ IsGalois k N ∧
      x ∈ relativeBrGroup k N := by
  induction x using BrauerGroup.induction with | h A =>
  obtain ⟨N, hfin, hgal, hsplit⟩ :=
    Algebra.IsCentralSimple.exists_finite_galois_split (k := k) (A := A)
      (k_bar := AlgebraicClosure k)
  exact ⟨N, hfin, hgal, (mk_mem_relativeBrGroup_iff_isSplit k N A).2 hsplit⟩

/-- `Br k` is the union of the relative Brauer groups of the finite Galois subextensions
of the algebraic closure. -/
theorem iSup_relativeBrGroup_eq_top :
    ⨆ N : {N : IntermediateField k (AlgebraicClosure k) //
      FiniteDimensional k N ∧ IsGalois k N}, relativeBrGroup k N.1 = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨N, hfin, hgal, hmem⟩ := exists_finite_galois_mem k x
  exact le_iSup (fun N : {N : IntermediateField k (AlgebraicClosure k) //
    FiniteDimensional k N ∧ IsGalois k N} ↦ relativeBrGroup k N.1) ⟨N, hfin, hgal⟩ hmem

end BrauerGroup
