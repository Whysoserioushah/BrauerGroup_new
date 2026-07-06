module

public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Span as a Sum

In this file, we show that any element in the two-sided ideal span of a set `s` in `R` is a
finite sum of the form `∑ i, rᵢ * sᵢ * tᵢ` where `rᵢ, tᵢ ∈ R, sᵢ ∈ s` .

## Main Results

* `TwoSidedIdeal.mem_span_iff_exists_fin`: `x ∈ span s` iff there exists a linear combination
  `∑ i, rᵢ * sᵢ * rᵢ' = x` where only finite terms are non-zero.
* `TwoSidedIdeal.mem_span_ideal_iff_exists_fin`: elements in the two-sided ideal closure of an
  (left) ideal `I` is in the form of `∑ i, xᵢ * rᵢ`(`rᵢ ∈ R` and `xᵢ ∈ I`) where only
  finite terms are non-zero.
* `IsSimpleRing.exists_sum_mul_mul_eq_one`: in a simple ring, every nonzero element admits a
  finite family of left and right multipliers whose sum of conjugates is `1`.

-/

@[expose] public section

open scoped Pointwise

private lemma Set.univ_mul_mul_univ_eq_range {α : Type*} [Mul α] (s : Set α) :
    univ * s * univ = range fun t : α × s × α ↦ t.1 * t.2.1 * t.2.2 := by
  ext; simp [mem_mul]

namespace TwoSidedIdeal

universe u v

variable {R : Type u} [Ring R]

lemma mem_span_iff_exists_fin' (s : Set R) (x : R) :
    x ∈ span s ↔ ∃ (ι : Type u) (t : Finset ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
      x = ∑ i ∈ t, xL i * (y i : R) * xR i := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := AddSubgroup.mem_closure_range_iff.1
      (s.univ_mul_mul_univ_eq_range ▸ mem_span_iff_mem_addSubgroup_closure.1 hx)
    simp_rw [← smul_mul_assoc, Finsupp.sum] at ha
    exact ⟨_, a.support, _, _, _, ha⟩
  · rintro ⟨_, _, _, _, _, rfl⟩
    exact sum_mem fun _ _ ↦ mul_mem_right _ _ _ <| mul_mem_left _ _ _ <|
      subset_span <| Subtype.coe_prop _

lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔ ∃ (n : ℕ) (xL : Fin n → R) (xR : Fin n → R) (y : Fin n → s),
      x = ∑ i : Fin n, xL i * (y i : R) * xR i := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨ι, t, xL, xR, y, hy⟩ := (mem_span_iff_exists_fin' s x).1 hx
    let f := Subtype.val ∘ (Finset.equivFin t).symm
    refine ⟨t.card, xL ∘ f, xR ∘ f, y ∘ f, hy ▸ (Finset.sum_bij'
      (fun x hx ↦ Finset.equivFin t ⟨x, hx⟩) (fun i _ ↦ f i) ?_ ?_ ?_ ?_ ?_)⟩
    all_goals simp [f]
  · rintro ⟨_, _, _, _, rfl⟩
    exact sum_mem fun _ _ ↦ mul_mem_right _ _ _ <| mul_mem_left _ _ _ <|
      subset_span <| Subtype.coe_prop _

lemma mem_span_ideal_iff_exists_fin (s : Ideal R) (x : R) :
    x ∈ span s ↔ ∃ (n : ℕ) (xR : Fin n → R) (y : Fin n → s),
      x = ∑ i : Fin n, (y i : R) * xR i := by
  rw [mem_span_iff_exists_fin]
  exact ⟨fun ⟨n, xL, xR, y, _⟩ ↦ ⟨n, xR, fun i ↦ ⟨xL i * y i, s.mul_mem_left _ (y i).2⟩,
    by simp_all⟩, fun ⟨n, xL, xR, hy⟩ ↦ ⟨n, 1, xL, xR, by simpa⟩⟩

end TwoSidedIdeal

/-- In a simple ring, every nonzero element `a` admits finite families `x y` of left and right
multipliers such that `∑ i, x i * a * y i = 1`. -/
lemma IsSimpleRing.exists_sum_mul_mul_eq_one {R : Type*} [Ring R] [IsSimpleRing R] {a : R}
    (ha : a ≠ 0) : ∃ (n : ℕ) (x y : Fin n → R), ∑ i, x i * a * y i = 1 := by
  obtain ⟨n, x, y, z, eq⟩ := (TwoSidedIdeal.mem_span_iff_exists_fin {a} 1).1 <|
    one_mem_of_ne_zero_mem _ ha (TwoSidedIdeal.subset_span rfl)
  simp_rw [show ∀ i, (z i : R) = a from fun i ↦ (z i).2] at eq
  exact ⟨n, x, y, eq.symm⟩
