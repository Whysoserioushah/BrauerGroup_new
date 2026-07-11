module

public import BrauerGroup.RingTheory.SimpleRing.Centralizer
public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.FieldTheory.JacobsonNoether
public import Mathlib.FieldTheory.SeparableDegree

/-!
# Subalgebras of finite-dimensional division algebras, and Koethe's theorem

Every subalgebra of a finite-dimensional division algebra `D` over a field `k` is closed
under the ambient inverse (`Subalgebra.inv_mem_of_finite`), hence is a division ring
(`Subalgebra.divisionRingOfFinite`), and a field when it is commutative
(`Subalgebra.fieldOfIsMulCommutative`). These structures are built over the canonical
`Ring`/`CommRing` instances on the subtype, so they do not create instance diamonds.

The main result is **Koethe's theorem** (`DivisionRing.exists_separable_maxSubfield`):
a finite-dimensional central division algebra contains a self-centralizing — equivalently,
by `Subalgebra.maximal_comm_iff_self_centralizer`, maximal — commutative subalgebra that is
separable over the base field: a separable maximal subfield.

We also prove that a directed supremum of separable subalgebras is separable
(`Subalgebra.isSeparable_iSup_of_directed`), the input to the Zorn argument.
-/

@[expose] public section

open scoped IsMulCommutative Subalgebra

variable {k D : Type*} [Field k] [DivisionRing D] [Algebra k D]

/-! ### Subalgebras of a finite-dimensional division algebra are division rings -/

/-- Every subalgebra of a finite-dimensional division algebra is closed under the ambient
inverse: the inverse of an integral element `x` is a polynomial in `x`. -/
theorem Subalgebra.inv_mem_of_finite [FiniteDimensional k D] {L : Subalgebra k D} {x : D}
    (hx : x ∈ L) : x⁻¹ ∈ L :=
  (Algebra.IsIntegral.isIntegral (R := k) x).inv_mem hx

/-- Every nonzero element of a subalgebra of a finite-dimensional division algebra is a unit
of the subalgebra, its inverse being the ambient one. -/
theorem Subalgebra.isUnit_or_eq_zero_of_finite [FiniteDimensional k D] (L : Subalgebra k D)
    (x : ↥L) : IsUnit x ∨ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inr rfl
  · exact Or.inl ⟨⟨x, ⟨(x : D)⁻¹, Subalgebra.inv_mem_of_finite x.2⟩,
      Subtype.ext (mul_inv_cancel₀ fun h ↦ hx (Subtype.ext h)),
      Subtype.ext (inv_mul_cancel₀ fun h ↦ hx (Subtype.ext h))⟩, rfl⟩

/-- A subalgebra of a finite-dimensional division algebra is a division ring. Built over the
canonical `Ring` instance, so no instance diamonds arise. -/
noncomputable abbrev Subalgebra.divisionRingOfFinite [FiniteDimensional k D]
    (L : Subalgebra k D) : DivisionRing ↥L :=
  haveI : Nontrivial ↥L := ⟨1, 0, fun h ↦ one_ne_zero (α := D) (congrArg Subtype.val h)⟩
  DivisionRing.ofIsUnitOrEqZero L.isUnit_or_eq_zero_of_finite

/-- A commutative subalgebra of a finite-dimensional division algebra is a field. Built over
the canonical `CommRing` instance, so no instance diamonds arise. -/
noncomputable abbrev Subalgebra.fieldOfIsMulCommutative [FiniteDimensional k D]
    (L : Subalgebra k D) [IsMulCommutative L] : Field ↥L :=
  haveI : Nontrivial ↥L := ⟨1, 0, fun h ↦ one_ne_zero (α := D) (congrArg Subtype.val h)⟩
  Field.ofIsUnitOrEqZero L.isUnit_or_eq_zero_of_finite

/-! ### Directed suprema of separable subalgebras -/

/-- A directed supremum of separable subalgebras is separable: every element of the
supremum already lies in one of the subalgebras. -/
theorem Subalgebra.isSeparable_iSup_of_directed {ι : Type*} [Nonempty ι]
    {K : ι → Subalgebra k D} (dir : Directed (· ≤ ·) K)
    [hK : ∀ i, Algebra.IsSeparable k (K i)] :
    Algebra.IsSeparable k (⨆ i, K i : Subalgebra k D) := by
  rw [Subalgebra.isSeparable_iff]
  intro x hx
  rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed dir] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact Subalgebra.isSeparable_iff.1 (hK i) x hi

/-! ### Koethe's theorem -/

namespace JacobsonNoether

variable (k D) in
/-- The Zorn family for Koethe's theorem: commutative subalgebras of `D` that are separable
over `k`. -/
private abbrev S := {L : Subalgebra k D | IsMulCommutative ↥L ∧ Algebra.IsSeparable k L}

variable (k D) in
/-- Chains in the family `S` are bounded by their supremum: directed suprema preserve both
commutativity and separability. -/
private lemma exists_ub_S : ∀ c ⊆ S k D, IsChain (fun x1 x2 ↦ x1 ≤ x2) c →
    ∀ y ∈ c, ∃ ub ∈ S k D, ∀ z ∈ c, z ≤ ub := fun c hc hc' L hL ↦ by
  have : Nonempty c := ⟨⟨L, hL⟩⟩
  have : ∀ i : c, IsMulCommutative (i : Subalgebra k D) := fun i ↦ (hc i.2).1
  have : ∀ i : c, Algebra.IsSeparable k (i : Subalgebra k D) := fun i ↦ (hc i.2).2
  have dir : Directed (· ≤ ·) (Subtype.val : c → Subalgebra k D) := hc'.directedOn.directed_val
  exact ⟨⨆ i : c, (i : Subalgebra k D),
    ⟨Subalgebra.isMulCommutative_iSup dir, Subalgebra.isSeparable_iSup_of_directed dir⟩,
    fun z hz ↦ le_iSup (fun i : c ↦ (i : Subalgebra k D)) ⟨z, hz⟩⟩

/-- The base field, as the bottom subalgebra, is commutative and separable. -/
private lemma bot_mem_S : ⊥ ∈ S k D := by
  simp [S, Subalgebra.isSeparable_iff, isMulCommutative_iff, ← Algebra.range_ofId,
    ← map_mul, mul_comm, isSeparable_algebraMap]

variable {L : Subalgebra k D}

private instance [IsMulCommutative L] :
    IsScalarTower k ↥L ↥(Subalgebra.centralizer k (L : Set D)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ Subtype.ext rfl

private instance [FiniteDimensional k D] [IsMulCommutative L] :
    Module.Finite ↥L ↥(Subalgebra.centralizer k (L : Set D)) :=
  Module.Finite.of_restrictScalars_finite k ↥L ↥(Subalgebra.centralizer k (L : Set D))

/-- If the centralizer of `L` is strictly larger than `L`, then `L` is a proper subfield of
its centralizer, i.e. `⊥ ≠ ⊤` for the centralizer as an `L`-algebra. -/
private lemma bot_ne_top [IsMulCommutative L]
    (h : Subalgebra.centralizer k (L : Set D) ≠ L) :
    (⊥ : Subalgebra ↥L ↥(Subalgebra.centralizer k (L : Set D))) ≠ ⊤ := fun hbot ↦ by
  refine h (le_antisymm (fun c hc ↦ ?_)
    ((Subalgebra.le_centralizer_iff_isMulCommutative L).2 inferInstance))
  have hmem : (⟨c, hc⟩ : ↥(Subalgebra.centralizer k (L : Set D))) ∈
      (⊥ : Subalgebra ↥L ↥(Subalgebra.centralizer k (L : Set D))) := by
    rw [hbot]; exact Algebra.mem_top
  obtain ⟨l, hl⟩ := Algebra.mem_bot.1 hmem
  have hval : (l : D) = c := congrArg Subtype.val hl
  exact hval ▸ l.2

/-- The enlargement step of Koethe's theorem: adjoining to `L` an element of its centralizer
that is separable over `L` produces a strictly larger member of the Zorn family. The key
point is separability over the *base field*, by transitivity in the tower
`k ⊆ L ⊆ L' = k[L, x]`, where `L'/L` is separable because it is generated by the single
separable element `x`. -/
private lemma adjoin_insert_mem_S [FiniteDimensional k D] [IsMulCommutative L]
    [Algebra.IsSeparable k L] {x : ↥(Subalgebra.centralizer k (L : Set D))}
    (hxsep : IsSeparable ↥L x) :
    Algebra.adjoin k (insert (x : D) (L : Set D)) ∈ S k D := by
  haveI hcomm' : IsMulCommutative (Algebra.adjoin k (insert (x : D) (L : Set D))) :=
    Subalgebra.isMulCommutative_adjoin_insert_of_mem_centralizer x.2
  refine ⟨hcomm', ?_⟩
  have hLL' : L ≤ Algebra.adjoin k (insert (x : D) (L : Set D)) :=
    fun y hy ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)
  have hL'C : Algebra.adjoin k (insert (x : D) (L : Set D)) ≤
      Subalgebra.centralizer k (L : Set D) :=
    Algebra.adjoin_le (Set.insert_subset x.2
      ((Subalgebra.le_centralizer_iff_isMulCommutative L).2 inferInstance))
  set L' := Algebra.adjoin k (insert (x : D) (L : Set D))
  -- the tower of fields `k ⊆ L ⊆ L'`, with all algebra maps given by inclusions
  letI : Field ↥L := L.fieldOfIsMulCommutative
  letI : Field ↥L' := L'.fieldOfIsMulCommutative
  letI : Algebra ↥L ↥L' := (Subalgebra.inclusion hLL').toRingHom.toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq fun _ ↦ Subtype.ext rfl
  haveI : Module.Finite ↥L ↥L' := Module.Finite.of_restrictScalars_finite k ↥L ↥L'
  set x' : ↥L' := ⟨(x : D), Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  -- `x'` is separable over `L`: transport `hxsep` along the inclusion `L' → C_D(L)`
  have hx' : IsSeparable ↥L x' := by
    let ι : ↥L' →ₐ[↥L] ↥(Subalgebra.centralizer k (L : Set D)) :=
      { toRingHom := (Subalgebra.inclusion hL'C).toRingHom
        commutes' := fun l ↦ Subtype.ext rfl }
    have hι : Function.Injective ι := fun a b hab ↦ by
      have h1 := congrArg (Subtype.val (α := D)) hab
      exact Subtype.ext h1
    have h0 : ι x' = x := Subtype.ext rfl
    exact (isSeparable_map_iff ι hι).1 (h0 ▸ hxsep)
  -- as an `L`-algebra, `L'` is generated by the single element `x'`
  have hadj : Algebra.adjoin ↥L {x'} = ⊤ := by
    rw [eq_top_iff]
    have hmemL : ∀ (d : D) (hdL : d ∈ L) (hdL' : d ∈ L'),
        (⟨d, hdL'⟩ : ↥L') ∈ Algebra.adjoin ↥L {x'} := fun d hdL hdL' ↦ by
      rw [show (⟨d, hdL'⟩ : ↥L') = algebraMap ↥L ↥L' ⟨d, hdL⟩ from Subtype.ext rfl]
      exact Subalgebra.algebraMap_mem _ _
    rintro ⟨y, hy⟩ -
    induction hy using Algebra.adjoin_induction with
    | mem d hd =>
      rcases hd with rfl | hd
      · exact Algebra.subset_adjoin rfl
      · exact hmemL d hd _
    | algebraMap r =>
      rw [show (⟨algebraMap k D r, _⟩ : ↥L') = algebraMap ↥L ↥L' (algebraMap k ↥L r) from
        Subtype.ext rfl]
      exact Subalgebra.algebraMap_mem _ _
    | add d e hd he ihd ihe => exact add_mem ihd ihe
    | mul d e hd he ihd ihe => exact mul_mem ihd ihe
  -- hence `L'/L` is a separable field extension, generated by one separable element
  haveI : Algebra.IsSeparable ↥L ↥(IntermediateField.adjoin ↥L {x'}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable ↥L ↥L').2 hx'
  haveI : Algebra.IsSeparable ↥L ↥L' := by
    refine (Algebra.isSeparable_def _ _).2 fun y ↦ ?_
    have hy' : y ∈ Algebra.adjoin ↥L {x'} := by rw [hadj]; exact Algebra.mem_top
    exact IntermediateField.isSeparable_of_mem_isSeparable ↥L ↥L'
      (IntermediateField.algebra_adjoin_le_adjoin ↥L {x'} hy')
  -- transitivity of separability in the tower `k ⊆ L ⊆ L'`
  exact Algebra.IsSeparable.trans k ↥L ↥L'

end JacobsonNoether

open JacobsonNoether in
/-- **Koethe's theorem**: a finite-dimensional central division algebra `D` over a field `k`
contains a *separable maximal subfield*, stated here as: there is a commutative subalgebra
`L` that is self-centralizing — equivalently maximal commutative, by
`Subalgebra.maximal_comm_iff_self_centralizer` — and separable over `k`. Commutativity of
`L` follows from self-centralizing-ness via `Subalgebra.le_centralizer_iff_isMulCommutative`.

Proof strategy:

1. By Zorn's lemma, pick `L` maximal among commutative separable subalgebras of `D`
   (directed suprema preserve both properties).
2. Suppose `L` is not self-centralizing and let `C ≠ L` be its centralizer. Then `C` is a
   division ring (`Subalgebra.divisionRingOfFinite`), finite-dimensional over the field `L`
   (`Subalgebra.fieldOfIsMulCommutative`), and *central* over `L`: by the double centralizer
   theorem, `Z(C) = C ∩ C_D(C) = C ∩ L = L` (the scoped instance
   `Subalgebra.isCentral_centralizer`).
3. By the Jacobson–Noether theorem (`exists_separable_and_not_isCentral'`) applied to the
   noncommutative division algebra `C` over `L`, there is `x ∈ C \ L` separable over `L`.
4. `L' := k[L, x]` is commutative (since `x` centralizes `L`) and separable over `k` — it is
   generated over `L` by the single separable element `x`, and separability is transitive in
   the tower `k ⊆ L ⊆ L'` (`JacobsonNoether.adjoin_insert_mem_S`).
5. So `L'` is a member of the Zorn family strictly containing `L`, contradicting maximality.
-/
theorem DivisionRing.exists_separable_maxSubfield [FiniteDimensional k D]
    [Algebra.IsCentral k D] :
    ∃ L : Subalgebra k D, Subalgebra.centralizer k (L : Set D) = L ∧
      Algebra.IsSeparable k L := by
  -- step 1: a maximal commutative separable subalgebra, by Zorn
  obtain ⟨L, _, hL⟩ := zorn_le_nonempty₀ (s := S k D) (exists_ub_S k D) _ bot_mem_S
  refine ⟨L, ?_, hL.1.2⟩
  by_contra! h
  haveI := hL.1.1
  haveI := hL.1.2
  -- step 2: the centralizer is a central division algebra over the field `L`
  letI : Field ↥L := L.fieldOfIsMulCommutative
  letI : DivisionRing ↥(Subalgebra.centralizer k (L : Set D)) :=
    (Subalgebra.centralizer k (L : Set D)).divisionRingOfFinite
  haveI : Algebra.IsAlgebraic ↥L ↥(Subalgebra.centralizer k (L : Set D)) :=
    Algebra.IsAlgebraic.of_finite ↥L ↥(Subalgebra.centralizer k (L : Set D))
  -- step 3: Jacobson–Noether provides a separable element outside `L`
  obtain ⟨x, hx1, hx2⟩ := exists_separable_and_not_isCentral'
    (L := ↥L) (D := ↥(Subalgebra.centralizer k (L : Set D))) (bot_ne_top h)
  have hxL : (x : D) ∉ L := fun hxL ↦ hx1 (Algebra.mem_bot.2 ⟨⟨(x : D), hxL⟩, Subtype.ext rfl⟩)
  -- steps 4–5: adjoining `x` contradicts the maximality of `L`
  exact hxL (hL.2 (adjoin_insert_mem_S hx2)
    (fun y hy ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy))
    (Algebra.subset_adjoin (Set.mem_insert _ _)))
