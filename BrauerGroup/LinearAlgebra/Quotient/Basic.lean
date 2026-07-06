module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
## Composition of quotient map and submodule inclusion
-/

@[expose] public section

@[simp]
lemma Submodule.subtype_mkQ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) : (Submodule.mkQ p) ∘ₗ p.subtype = 0 := by
  ext; simp only [LinearMap.coe_comp, coe_subtype, Function.comp_apply, mkQ_apply,
    LinearMap.zero_apply, Quotient.mk_eq_zero, SetLike.coe_mem]
