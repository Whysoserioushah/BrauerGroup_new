import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Tactic
import Mathlib.Data.Finsupp.Notation

universe u

suppress_compilation

variable (R : Type u) [Ring R] (e : R) {I : Type*} [DecidableEq I]

structure PrimitiveIdempotents: Prop where
  idem : IsIdempotentElem e
  ne_sum_ortho : ∀(e' : I → R)(_ : OrthogonalIdempotents e')(i j : I), e ≠ e' i + e' j

section

variable {ι M σ : Type*}
variable [DecidableEq ι] [AddCommGroup M] [Module R M]
open DirectSum
variable (ℳ : ι → Submodule R M) [Decomposition ℳ]
variable [(i : ι) → (x : (ℳ i)) → Decidable (x ≠ 0)]


-- example (n : ℕ) : n * 2 = n + n := by
--   induction (2 : ℝ)

lemma decompose_unique  (rep₁ rep₂ : ⨁ i, ℳ i)
    (h₁ : (∑ i ∈ rep₂.support, rep₂ i : M) = (∑ i ∈ rep₁.support, rep₁ i)) :

    rep₁ = rep₂ := by
  classical
  apply_fun (decompose ℳ).symm
  rw [← sum_support_decompose ℳ (r := (decompose ℳ).symm rep₁),
    ← sum_support_decompose ℳ (r := (decompose ℳ).symm rep₂)]
  simp only [Equiv.apply_symm_apply]
  exact h₁.symm


def decomp_ring_ortho_idem (I M : Type u) [Fintype I] [DecidableEq I]
    (V : I → Submodule R R) [Decomposition V] (e : ⨁ (i : I), (V i))
    [(i : I) → (x : ↥(V i)) → Decidable (x ≠ 0)]
    (he : (1 : R) = ∑ j ∈ e.support, e j):
    OrthogonalIdempotents (R := R) (I := DFinsupp.support e) fun i ↦ e i where
  idem i := by
    change _ = _
    let x : (⨁ i, V i) := DFinsupp.single i (e i) -- 0,0,0,...,eᵢ,0,0,0,...
    let y : (⨁ i, V i) := DFinsupp.mapRange (x := e) (fun j (z : V j) => ⟨e i * (z : R), by
      rw [← smul_eq_mul] ; obtain ⟨z, hz⟩ := z
      exact Submodule.smul_mem (V j) (↑(e ↑i)) hz ⟩)
      fun i' ↦ by simp only [ZeroMemClass.coe_zero, mul_zero, AddSubmonoid.mk_eq_zero]
    have hx1 : x i = e i := by simp [x]
    have hx2 (j) (h : j ≠ i) : (x j : R) = 0 := by
      simp [x, Finsupp.single_apply]
      intro hij ; exfalso
      exact h.symm $ Subtype.coe_inj.1 hij
    have hy (j) : (y j : R) = e i * e j := by
      simp only [DFinsupp.mapRange_apply, y]
    have hx3 : ∑ i ∈ DFinsupp.support x, (x i : R) = x i := by
      apply Finset.sum_eq_single
      · intro j hj hj'
        specialize hx2 ⟨j, by
          simp_all [↓reduceDIte, x, y]
          obtain ⟨val, property⟩ := i
          obtain ⟨w, h⟩ := hj
          subst w
          simp_all only [Subtype.mk.injEq, not_true_eq_false]⟩ $ Subtype.coe_ne_coe.1 hj'
        exact hx2
      · simp
    have hy3 : ∑ i ∈ DFinsupp.support y, (y i : R) = e i * 1 := by
      rw [he, Finset.mul_sum]
      simp_rw [hy]
      apply Finset.sum_subset
      · intro j hj
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, y] at hj ⊢
        contrapose! hj
        simp [hj, mul_zero]
      · intro x hx hy
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, not_not, y] at hx hy ⊢
        exact hy
    have : x = y := by
      apply decompose_unique
      rw [hx3, hy3, mul_one]
      simp only [DFinsupp.single_apply, ↓reduceDIte, x]
    have := congr($this i)
    simp [hx1, hy, y, Subtype.ext_iff] at this
    exact this.symm
  ortho := fun i j hij ↦ by
    simp only
    let x : (⨁ i, V i) := DFinsupp.single i (e i) -- 0,0,0,...,eᵢ,0,0,0,...
    let y : (⨁ i, V i) := DFinsupp.mapRange (x := e) (fun j (z : V j) => ⟨e i * (z : R), by
      rw [← smul_eq_mul] ; obtain ⟨z, hz⟩ := z
      exact Submodule.smul_mem (V j) (↑(e ↑i)) hz ⟩)
      fun i' ↦ by simp only [ZeroMemClass.coe_zero, mul_zero, AddSubmonoid.mk_eq_zero]
    have hx1 : x i = e i := by simp [x]
    have hx2 (j) (h : j ≠ i) : (x j : R) = 0 := by
      simp [x, Finsupp.single_apply]
      intro hij ; exfalso
      exact h.symm $ Subtype.coe_inj.1 hij
    have hy (j) : (y j : R) = e i * e j := by
      simp only [DFinsupp.mapRange_apply, y]
    have hx3 : ∑ i ∈ DFinsupp.support x, (x i : R) = x i := by
      apply Finset.sum_eq_single
      · intro j hj hj'
        specialize hx2 ⟨j, by
          simp_all [↓reduceDIte, x, y]
          obtain ⟨val, property⟩ := i
          obtain ⟨w, h⟩ := hj
          subst w
          simp_all only [Subtype.mk.injEq, not_true_eq_false]⟩ $ Subtype.coe_ne_coe.1 hj'
        exact hx2
      · simp
    have hy3 : ∑ i ∈ DFinsupp.support y, (y i : R) = e i * 1 := by
      rw [he, Finset.mul_sum]
      simp_rw [hy]
      apply Finset.sum_subset
      · intro j hj
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, y] at hj ⊢
        contrapose! hj
        simp [hj, mul_zero]
      · intro x hx hy
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, not_not, y] at hx hy ⊢
        exact hy
    have : x = y := by
      apply decompose_unique
      rw [hx3, hy3, mul_one]
      simp only [DFinsupp.single_apply, ↓reduceDIte, x]
    have := congr($this j)
    simp [hx1, hy, y, Subtype.ext_iff, (hx2 j hij.symm)] at this
    exact this.symm

def ortho_idem_directsum (I M : Type u) [Fintype I] [DecidableEq I]
    (e : I → R) (he' : OrthogonalIdempotents e) :
    (⨁ i : I, (Submodule.span R {e i})) = Submodule.span R {∑ i : I, e i} := by
  simp only [Ideal.submodule_span_eq]
  sorry


def ortho_idem_decomp_ring (I M : Type u) [Fintype I] [DecidableEq I]
    (e : I → R) (he : ∑ i : I, e i  = 1) (he' : OrthogonalIdempotents e) :
    (⨁ i : I, (Submodule.span R {e i})) ≃ₗ[R] R := by
  have h : ⊤ = Submodule.span R {(1 : R)} := by
    simp_all only [Ideal.submodule_span_eq, Ideal.span_singleton_one]
  refine ?_ ≪≫ₗ (LinearEquiv.ofEq _ _ h.symm ≪≫ₗ Submodule.topEquiv (R := R) (M := R))
  rw [← he]
  symm

  sorry

end
