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
