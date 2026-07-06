module

public import Mathlib.RingTheory.Flat.TorsionFree
public import BrauerGroup.LinearAlgebra.Quotient.Basic

/-!
## Tensor product of submodules
This file shows the intersection of `b ⊗ C` and `B ⊗ c` is `b ⊗ c` in `B ⊗ C` for submodules
`b` of `B` and `c` of `C`.

# Main results
* `TensorProduct.submodule_tensor_inf_tensor_submodule` : `(b ⊗ C) ⊓ (B ⊗ c) = b ⊗ c`.

## Tags
Tensor product, Submodule, Flatness

-/

@[expose] public section

universe u

variable {K : Type u} [Field K]

open TensorProduct

/-- Any element in `B ⊗ C` that's in the image of `b ⊗ C` and `B ⊗ c` can be pulled back to an
element in `B ⊗ c`, but since it is also in the image of `b ⊗ C`, it got sent to zero in
`(B/b) ⊗ C` in bottom right, then by the commSq on right and the fact that
`c.subtype.lTensor (B ⧸ b)` is injective (by flatness) we have the element is in kernel of
`b.mkQ.rTensor c` hence by exactness it's in image of `b ⊗ c` in top left.
This is the analogue of `ShortComplex.Exact.lift` in concrete modules.
  0 ---> b ⊗ c ---> B ⊗ c ---> (B/b) ⊗ c ---> 0
           |          |             |
           |          |             |
           v          v             v
  0 ---> b ⊗ C ---> B ⊗ C ---> (B/b) ⊗ C ---> 0
-/
lemma TensorProduct.submodule_tensor_inf_tensor_submodule
    {B C : Type*} [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (b : Submodule K B) (c : Submodule K C) :
    (b.subtype.rTensor C).range ⊓ (c.subtype.lTensor B).range =
    (map b.subtype c.subtype).range := by
  refine le_antisymm ?_ ?_
  · rintro z (hz : z ∈ (b.subtype.rTensor C).range ⊓ (c.subtype.lTensor B).range)
    obtain ⟨z, rfl⟩ := hz.2
    have hsq2 : c.subtype.lTensor (B ⧸ b) ∘ₗ (Submodule.mkQ b).rTensor c =
      (Submodule.mkQ b).rTensor C ∘ₗ c.subtype.lTensor B := by simp
    have he := rTensor_exact c (LinearMap.exact_subtype_mkQ b) (Submodule.mkQ_surjective _)
    have : (Submodule.mkQ b).rTensor C (c.subtype.lTensor B z) = 0 := by
      obtain ⟨x, hx⟩ := hz.1
      simp [← hx, ← LinearMap.rTensor_comp_apply, b.subtype_mkQ]
    rw [← LinearMap.comp_apply, ← hsq2, LinearMap.comp_apply,
      (map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap
      _ c.subtype_injective)), ← LinearMap.mem_ker, he.linearMap_ker_eq] at this
    obtain ⟨x, rfl⟩ := this
    use x
    simp [← LinearMap.lTensor_comp_rTensor]
  · rintro _ ⟨x, rfl⟩
    exact ⟨⟨c.subtype.lTensor _ x, by simp [← LinearMap.rTensor_comp_lTensor]⟩,
      ⟨b.subtype.rTensor _ x, by simp [← LinearMap.lTensor_comp_rTensor]⟩⟩
