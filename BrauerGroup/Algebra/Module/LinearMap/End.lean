module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.LinearMap.End

/-!
## Conjugation of endomorphisms by a linear equivalence on noncommutative rings
This is the analogue of `LinearEquiv.conj` for non-commutative rings, note that
without commutativity it is not a `LinearEquiv` anymore!

TODO: refactor `LinearEquiv.conj` in mathlib to use them directly.
-/

@[expose] public section

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (l : M ≃ₗ[R] N)

/-- conjugation of endomorphisms by a linear equivalence -/
@[simps]
def LinearEquiv.conj' (f : Module.End (Module.End R M) M) :
    Module.End (Module.End R N) N where
  toFun x := l (f (l.symm x))
  map_smul' g x := by
    simp only [Module.End.smul_def, RingHom.id_apply]
    let L := l.symm.toLinearMap ∘ₗ g ∘ₗ l.toLinearMap
    have := f.map_smul L (l.symm x)
    simp only [Module.End.smul_def, LinearMap.coe_comp, coe_coe, Function.comp_apply,
      apply_symm_apply, L] at this
    simp [this]
  map_add' := by simp

/-- A LinearEquiv from `M` to `N` induces an AddEquiv from `End (End R M) M` to `End (End R N)` -/
@[simps]
def LinearEquiv.conjAddEquiv (l : M ≃ₗ[R] N) :
    Module.End (Module.End R M) M ≃+ Module.End (Module.End R N) N where
  toFun := l.conj'
  map_add' _ _ := by ext; simp
  invFun g := l.symm.conj' g
  left_inv f := by ext; simp
  right_inv g := by ext; simp
