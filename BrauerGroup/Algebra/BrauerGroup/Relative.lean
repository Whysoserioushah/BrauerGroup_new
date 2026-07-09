module

public import Mathlib
public import BrauerGroup.Algebra.BrauerGroup.BaseChange
public import BrauerGroup.Algebra.Split

/-!
# Relative Brauer group

The relative Brauer group `Br(L/K)` is the kernel of the base-change map
`Br K →* Br L`, i.e. the classes of central simple `K`-algebras that become
trivial (split) after base change to `L`.
-/

@[expose] public section

namespace BrauerGroup

universe u u₂

variable (K : Type u) (L : Type (max u u₂)) [Field K] [Field L] [Algebra K L]

/-- The relative Brauer group `Br(L/K)`: the subgroup of `BrauerGroup K` consisting of
the classes that become trivial after base change to `L`. -/
abbrev relativeBrGroup : Subgroup (BrauerGroup K) := (baseChange K L).ker

lemma mem_relativeBrGroup_iff {x : BrauerGroup K} :
    x ∈ relativeBrGroup K L ↔ baseChange K L x = 1 :=
  Iff.rfl

/-- A Brauer class lies in the relative Brauer group `Br(L/K)` if and only if `L` splits
(any representative of) the class. -/
lemma mk_mem_relativeBrGroup_iff_isSplit (A : Type u) [Ring A] [Algebra K A]
    [IsSimpleRing A] [Algebra.IsCentral K A] [FiniteDimensional K A] :
    BrauerGroup.mk K A ∈ relativeBrGroup K L ↔ Algebra.IsSplit K A L :=
  (mem_relativeBrGroup_iff K L).trans (Algebra.isSplit_iff_baseChange_eq_one K A L).symm

end BrauerGroup
