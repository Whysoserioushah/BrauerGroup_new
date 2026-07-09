module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import BrauerGroup.Algebra.Algebra.Opposite
public import BrauerGroup.RingTheory.Flat.TorsionFree

/-!

## Centralizer of tensor products
This file shows that the centralizer of tensor product of two subalgebras is equal to tensor product
of the centralizers of the two subalgebras.

# Main results
* `Subalgebra.centralizer_range_lmul` : inside `Module.End R B`, the centralizer of the left
  regular representation is the right regular representation.
* `centralizer_tensor_centralizer` : For subalgebras `B` of `A` and `B'` of `A'`,
  `C_A(B) ⊗ C_{A'}(B') = C_{A ⊗ A'}(B ⊗ B')`.

## Tags
Noncommutative algebra, centralizer, tensor product

-/

@[expose] public section

universe u v

open scoped TensorProduct

open Algebra.TensorProduct Subalgebra

section RegularRepresentation

variable (R B : Type*) [CommSemiring R] [Semiring B] [Algebra R B]

/-- Inside `Module.End R B`, the centralizer of the left regular representation of `B` is the
right regular representation: an endomorphism `φ` commuting with all left multiplications
satisfies `φ z = z * φ 1`. -/
theorem Subalgebra.centralizer_range_lmul :
    Subalgebra.centralizer R (Algebra.lmul R B).range = (Algebra.rmul R B).range := by
  ext φ
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨.op (φ 1), LinearMap.ext fun z ↦ by
      simpa using DFunLike.congr_fun (h (Algebra.lmul R B z) ⟨z, rfl⟩) (1 : B)⟩
  · rintro ⟨c, rfl⟩ _ ⟨b, rfl⟩
    exact LinearMap.ext fun z ↦ (mul_assoc b z c.unop).symm

end RegularRepresentation

variable {F A A' : Type*} [Field F] [Ring A] [Algebra F A] [Ring A']
  [Algebra F A'] (B : Subalgebra F A) (B' : Subalgebra F A')

lemma centralizer_tensor_le_inf_centralizer :
    centralizer F (A := A ⊗[F] A') (map B.val B'.val).range =
    centralizer F (A := A ⊗[F] A') ((includeLeft (R := F) (S := F) (A := A) (B := A')).comp
      B.val).range ⊓ centralizer F (A := A ⊗[F] A')
      ((includeRight (R := F) (A := A)).comp B'.val).range := by
  rw [← Subalgebra.centralizer_coe_sup, Algebra.TensorProduct.map_range]

open Algebra.TensorProduct

lemma Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct' :
     centralizer F (A := A ⊗[F] A') ((includeLeft (R := F) (B := A')).comp B.val).range =
      (Algebra.TensorProduct.map (centralizer F B).val (AlgHom.id F A')).range := by
  rw [range_comp_val, ← centralizer_coe_image_includeLeft_eq_center_tensorProduct, coe_map]

lemma Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct' :
     centralizer F (A := A ⊗[F] A') ((includeRight (R := F) (A := A)).comp B'.val).range =
      (Algebra.TensorProduct.map (AlgHom.id F A) (Subalgebra.centralizer F B').val).range := by
  rw [range_comp_val, ← centralizer_coe_image_includeRight_eq_center_tensorProduct, coe_map]

@[stacks 0749]
lemma centralizer_tensor_centralizer :
    Subalgebra.centralizer F (A := A ⊗[F] A') (Algebra.TensorProduct.map B.val B'.val).range =
    (Algebra.TensorProduct.map (centralizer F B).val (centralizer F B').val).range := by
  rw [centralizer_tensor_le_inf_centralizer,
    centralizer_coe_image_includeLeft_eq_center_tensorProduct',
    centralizer_coe_image_includeRight_eq_center_tensorProduct']
  apply toSubmodule.injective
  exact (TensorProduct.submodule_tensor_inf_tensor_submodule
    (centralizer F (B : Set A)).toSubmodule (centralizer F (B' : Set A')).toSubmodule)
