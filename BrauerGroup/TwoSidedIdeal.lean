import BrauerGroup.Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Operations

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι)
variable {R : Type*} [Ring R] (t : TwoSidedIdeal R)

open MulOpposite

namespace TwoSidedIdeal

variable {s}

variable (I : TwoSidedIdeal R)

variable {R' : Type*} [Ring R']

-- def span (s : Set R) : TwoSidedIdeal R :=
-- .mk $ ringConGen (fun a b ↦ a - b ∈ s)


-- lemma subset_span (s : Set R) : s ⊆ span s := by
--   intro x hx
--   rw [SetLike.mem_coe]
--   change ringConGen _ x 0
--   exact RingConGen.Rel.of _ _ (by simpa using hx)

def span' (s : Set R) : TwoSidedIdeal R := .mk'
  {x | ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * y i * xR i}
  ⟨Empty, Fintype.instEmpty, Empty.elim, Empty.elim, Empty.elim, by simp⟩
  (by
    rintro _ _ ⟨na, fina, xLa, xRa, ya, rfl⟩ ⟨nb, finb, xLb, xRb, yb, rfl⟩
    refine ⟨na ⊕ nb, inferInstance, Sum.elim xLa xLb, Sum.elim xRa xRb, Sum.elim ya yb, by
      simp⟩)
  (by
    rintro _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, -xL, xR, y, by simp⟩)
  (by
    rintro a _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, a • xL, xR, y, by
      rw [Finset.mul_sum]; simp only [mul_assoc, Pi.smul_apply, smul_eq_mul]⟩)
  (by
    rintro _ b ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, xL, fun x ↦ xR x * b, y, by simp [Finset.sum_mul, mul_assoc]⟩)

lemma mem_span'_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span' s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  simp only [span', mem_mk', Set.mem_setOf_eq]

lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  suffices eq1 : span s = span' s by
    rw [eq1]
    simp only [span', Set.mem_setOf_eq]
    generalize_proofs h1 h2 h3 h4 h5
    simp_all only [mem_mk', Set.mem_setOf_eq]

  rw [span, RingCon.ringConGen_eq]
  apply ringCon_injective
  refine sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · rintro I (hI : ∀ a b, _ → _)
    suffices span' s ≤ .mk I by
      rw [ringCon_le_iff] at this
      exact this
    intro x h
    rw [mem_span'_iff_exists_fin] at h
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := h
    rw [mem_iff]
    refine TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ ↦ TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ <| hI (y i) 0 (by simp))
  · rintro I hI
    exact ⟨(span' s).ringCon, fun a b H ↦ ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ ⟨a - b, by simp [H]⟩, by simp⟩, hI⟩

lemma mem_span_ideal_iff_exists_fin (s : Ideal R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, (y i : R) * xR i := by
  rw [mem_span_iff_exists_fin]
  fconstructor
  · rintro ⟨n, fin, xL, xR, y, rfl⟩
    exact ⟨n, fin, xR, fun i ↦ ⟨xL i * y i, s.mul_mem_left _ (y i).2⟩, by simp⟩
  · rintro ⟨n, fin, xR, y, rfl⟩
    exact ⟨n, fin, 1, xR, y, by simp⟩

lemma span_le {s : Set R} {I : TwoSidedIdeal R} : s ⊆ I ↔ span s ≤ I := by
  rw [le_iff]
  constructor
  · intro h x hx
    rw [SetLike.mem_coe, mem_span_iff_exists_fin] at hx
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := hx
    exact I.finsetSum_mem _ _ fun i _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ <| h (y i).2)
  · intro h x hx
    exact h <| subset_span hx

lemma coe_bot_set : ((⊥ : TwoSidedIdeal R) : Set R) = {0} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_singleton_iff]
  rfl

lemma coe_top_set : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_univ]
  rfl

section IsSimpleOrder

universe u

variable (A : Type u) [Ring A]

instance [Nontrivial A] : Nontrivial (TwoSidedIdeal A) :=
⟨⊥, ⊤, by
      apply_fun (fun I => I.ringCon 0 1)
      convert false_ne_true
      -- Change after https://github.com/leanprover-community/mathlib4/pull/12860
      simp only [iff_false]
      exact zero_ne_one⟩

lemma _root_.IsSimpleRing.iff_eq_zero_or_injective'
    (k : Type*) [CommRing k] [Algebra k A] [Nontrivial A] :
    IsSimpleRing A ↔
    ∀ ⦃B : Type u⦄ [Ring B] [Algebra k B] (f : A →ₐ[k] B),
      TwoSidedIdeal.ker f = ⊤ ∨ Function.Injective f := by
  classical
  constructor
  · intro so B _ _ f
    if hker : TwoSidedIdeal.ker f.toRingHom = ⊤
    then exact Or.inl hker
    else
      replace hker := so.1.2 (TwoSidedIdeal.ker f) |>.resolve_right hker
      rw [injective_iff_ker_eq_bot]
      exact Or.inr hker
  · intro h
    refine ⟨⟨fun I => ?_⟩⟩
    letI : Algebra k I.ringCon.Quotient :=
    { algebraMap := I.ringCon.mk'.comp (algebraMap k A)
      smul a := Quotient.map' (fun b => a • b) fun x y (h : I.ringCon x y) =>
        show I.ringCon _ _ by
        simp only
        rw [Algebra.smul_def, Algebra.smul_def]
        exact I.ringCon.mul (I.ringCon.refl (algebraMap k A a)) h
      commutes' := by
        simp only [RingHom.coe_comp, Function.comp_apply]
        intro a b
        induction b using Quotient.inductionOn' with
        | h b =>
          change _ * I.ringCon.mk' b = I.ringCon.mk' b * _
          simp only [← map_mul, Algebra.commutes a b]

      smul_def' := fun a b => by
        simp only [RingHom.coe_comp, Function.comp_apply]
        change Quotient.map' _ _ _ = _
        induction b using Quotient.inductionOn' with
        | h b =>
          change _ = _ * I.ringCon.mk' _
          simp only [Quotient.map'_mk'', ← map_mul, Algebra.smul_def]
          rfl }
    rcases @h I.ringCon.Quotient _ _ {I.ringCon.mk' with commutes' a := rfl } with h|h
    · right
      rw [eq_top_iff, le_iff]
      rintro x -
      simp only at h
      have mem : x ∈ TwoSidedIdeal.ker I.ringCon.mk' := by erw [h]; trivial
      rw [mem_ker] at mem
      change _ = I.ringCon.mk' 0 at mem
      exact I.ringCon.eq.mp mem
    · left
      rw [injective_iff_ker_eq_bot] at h
      rw [eq_bot_iff, le_iff]
      intro x hx
      have mem : x ∈ TwoSidedIdeal.ker I.ringCon.mk' := by
        rw [mem_ker]
        exact I.ringCon.eq.mpr hx
      erw [h] at mem
      exact mem

end IsSimpleOrder

end TwoSidedIdeal
