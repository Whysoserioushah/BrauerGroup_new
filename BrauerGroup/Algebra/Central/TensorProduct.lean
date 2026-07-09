module

public import Mathlib.Algebra.Central.TensorProduct
public import BrauerGroup.Algebra.Algebra.Subalgebra.Centralizer

/-!
## Tensor product of centers
This file shows the tensor product of centers of two algebras over a field is
the center of the tensor product.
-/

@[expose] public section

variable {k A A' : Type*} [Field k] [Ring A] [Ring A'] [Algebra k A] [Algebra k A']

open scoped TensorProduct

lemma Subtype.val_surjective {α : Type*} {p : α → Prop} (hp : ∀ a, p a) :
    Function.Surjective (Subtype.val : Subtype p → α) :=
  fun a ↦ ⟨⟨a, hp a⟩, rfl⟩

lemma Subalgebra.top_subtype_surj {R : Type*} (A : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] : Function.Surjective (⊤ : Subalgebra R A).val :=
  Subtype.val_surjective fun _ ↦ Algebra.mem_top

lemma center_tensor_center : Subalgebra.center k (A ⊗[k] A') =
    (Algebra.TensorProduct.map (Subalgebra.center k A).val (Subalgebra.center k A').val).range := by
  have h := centralizer_tensor_centralizer (F := k) (A := A) (A' := A') ⊤ ⊤
  rw [(AlgHom.range_eq_top _).2 (Algebra.TensorProduct.map_surjective _ _
    (Subalgebra.top_subtype_surj A) (Subalgebra.top_subtype_surj A')),
    Algebra.TensorProduct.map_range, Subalgebra.range_comp_val, Subalgebra.range_comp_val] at h
  simpa [Algebra.TensorProduct.map_range, Subalgebra.range_comp_val] using h

@[stacks 074G "part 2"]
instance [Algebra.IsCentral k A] [Algebra.IsCentral k A'] : Algebra.IsCentral k (A ⊗[k] A') where
  out := by simp [center_tensor_center, Algebra.TensorProduct.map_range, Subalgebra.range_comp_val]

@[stacks 074H "part 2"]
instance Algebra.IsCentral.baseChange (L : Type*) [Field L] [Algebra k L] [Algebra.IsCentral k A] :
    Algebra.IsCentral L (L ⊗[k] A) where
  out x h := by
    obtain ⟨x, rfl⟩ := le_of_eq center_tensor_center h
    clear h
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul x y =>
      obtain ⟨r, hr⟩ := (Algebra.IsCentral.center_eq_bot k A).le y.2
      use r • x.1
      simp only [AlgHom.toRingHom_eq_coe, toRingHom_ofId] at hr
      simp [-TensorProduct.tmul_smul, TensorProduct.smul_tmul, ← algebraMap_eq_smul_one, hr]
    | add x y h1 h2 => rw [map_add]; exact add_mem h1 h2

/-- Centrality descends along a field base change: if `L ⊗[k] A` is a central `L`-algebra
then `A` is a central `k`-algebra. Note the change of base field — this is not
`Algebra.IsCentral.right_of_tensor`, which keeps the base field fixed (and cannot apply
here, since the ring-center of `L ⊗[k] A` is `L·1`, not `k·1`). Neither nontriviality nor
finite-dimensionality of `A` is needed. -/
theorem Algebra.IsCentral.of_baseChange (L : Type*) [Field L] [Algebra k L]
    [h : Algebra.IsCentral L (L ⊗[k] A)] : Algebra.IsCentral k A where
  out z hz := by
    -- `1 ⊗ z` is central in `L ⊗[k] A`, hence of the form `c ⊗ 1`
    have h1 : (1 : L) ⊗ₜ[k] z ∈ Subalgebra.center L (L ⊗[k] A) := by
      rw [Subalgebra.mem_center_iff]
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [zero_mul, mul_zero]
      | tmul c a => rw [Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
          Subalgebra.mem_center_iff.mp hz a]
      | add u v hu hv => rw [add_mul, mul_add, hu, hv]
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (h.out h1)
    -- retract `L` onto `k` linearly and apply the retraction to the first tensor factor
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k L)
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective k L))
    have hg1 : g 1 = 1 := by simpa using LinearMap.congr_fun hg 1
    refine Algebra.mem_bot.mpr ⟨g c, ?_⟩
    have h2 := congrArg (fun x => TensorProduct.lid k A (LinearMap.rTensor A g x)) hc
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hg1, one_smul] at h2
    rw [Algebra.algebraMap_eq_smul_one]
    exact h2
