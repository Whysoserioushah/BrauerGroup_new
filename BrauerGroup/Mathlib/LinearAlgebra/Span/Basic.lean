import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Defs

variable {α R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {v : α → M} {x : M}

lemma Submodule.mem_span_image_finset_iff_exists_fun {s : Finset α} :
    x ∈ span R (v '' s) ↔ ∃ c : α → R, ∑ i ∈ s, c i • v i = x := by
  refine ⟨?_, ?_⟩
  · intro hx
    simp at hx
    refine Submodule.span_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro c ⟨c', hc1, hc2⟩
      classical
      exact ⟨Function.update (0 : α → R) c' 1 , by
        simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, ite_smul, one_smul,
          zero_smul, Finset.sum_ite_eq']; aesop⟩
    · exact ⟨0, by simp⟩
    · rintro x y hx hy ⟨c1, hc1⟩ ⟨c2, hc2⟩
      exact ⟨c1 + c2, by simp_all [add_smul, Finset.sum_add_distrib]⟩
    · exact fun r x hx ⟨c, hc⟩ ↦ ⟨r • c, by simp_all [mul_smul, ← Finset.smul_sum]⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun i hi ↦ smul_mem _ _ <| subset_span ⟨i, hi, by simp⟩
