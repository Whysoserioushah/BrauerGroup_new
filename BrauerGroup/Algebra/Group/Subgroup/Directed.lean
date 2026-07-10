module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.UnionLift

/-!
# Subgroups and directed unions of sets

Mirrors `Mathlib.Algebra.Algebra.Subalgebra.Directed` for subgroups:

* `Subgroup.iSupLift` (and `AddSubgroup.iSupLift`): define a monoid homomorphism on a
  directed supremum of subgroups by defining it on each subgroup, and proving that the
  definitions agree on smaller subgroups.

This is the gluing gadget for assembling a homomorphism out of a group presented as a
directed union — e.g. the invariant map on a Brauer group presented as the union of the
relative Brauer groups of a tower of extensions.
-/

@[expose] public section

namespace Subgroup

variable {G H : Type*} [Group G] [Group H]
variable {ι : Type*} [Nonempty ι] (K : ι → Subgroup G)

/-- Auxiliary definition for `Subgroup.iSupLift`: the homomorphism on the supremum itself. -/
@[to_additive /-- Auxiliary definition for `AddSubgroup.iSupLift`: the homomorphism on the
supremum itself. -/]
noncomputable def iSupLiftAux (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →* H)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)) :
    (iSup K : Subgroup G) →* H where
  toFun := Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
    (fun i j x hxi hxj => by
      rcases dir i j with ⟨k, hik, hjk⟩
      rw [hf i k hik, hf j k hjk]
      rfl)
    ((iSup K : Subgroup G) : Set G) (le_of_eq <| coe_iSup_of_directed dir)
  map_one' := Set.iUnionLift_const _ (fun i : ι => (1 : K i)) (fun _ => rfl) _ (by simp)
  map_mul' := by
    apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
    all_goals simp

/-- Define a monoid homomorphism on a directed supremum of subgroups by defining it on each
subgroup, and proving that the definitions agree on smaller subgroups. -/
@[to_additive /-- Define an additive monoid homomorphism on a directed supremum of additive
subgroups by defining it on each subgroup, and proving that the definitions agree on smaller
subgroups. -/]
noncomputable def iSupLift (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →* H)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : Subgroup G) (hT : T ≤ iSup K) : ↥T →* H :=
  (iSupLiftAux K dir f hf).comp (inclusion hT)

variable {K}

@[to_additive]
theorem iSupLift_of_mem {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →* H}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subgroup G} {hT : T ≤ iSup K} {i : ι} (x : T) (hx : (x : G) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  unfold iSupLift iSupLiftAux
  simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  exact Set.iUnionLift_of_mem (S := fun i => ((K i : Subgroup G) : Set G))
    (f := fun i x => f i x) (T := ((iSup K : Subgroup G) : Set G)) (inclusion hT x) hx

@[to_additive (attr := simp)]
theorem iSupLift_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →* H}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subgroup G} {hT : T ≤ iSup K} {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  exact iSupLift_of_mem (K := K) (dir := dir) (f := f) (hf := hf) (T := T) (hT := hT)
    (i := i) (inclusion h x) x.2

@[to_additive (attr := simp)]
theorem iSupLift_comp_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →* H}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subgroup G} {hT : T ≤ iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

@[to_additive (attr := simp)]
theorem iSupLift_mk {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →* H}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subgroup G} {hT : T ≤ iSup K} {i : ι} (x : K i) (hx : (x : G) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  exact iSupLift_of_mem (K := K) (dir := dir) (f := f) (hf := hf) (T := T) (hT := hT)
    (i := i) ⟨x, hx⟩ x.2

end Subgroup
