module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Opposite

/-!
# The right regular representation

`Algebra.lmul` realizes an algebra `B` inside `Module.End F B` by left multiplication. This
file provides the right-handed companion `Algebra.rmul`, realizing the opposite algebra
`Bᵐᵒᵖ` inside `Module.End F B` by right multiplication.
-/

@[expose] public section

variable (F B : Type*) [CommSemiring F] [Semiring B] [Algebra F B]

/-- Right multiplication as an algebra homomorphism `Bᵐᵒᵖ →ₐ[F] Module.End F B`; the
right-handed companion of `Algebra.lmul`. -/
def Algebra.rmul : Bᵐᵒᵖ →ₐ[F] Module.End F B where
  toFun b := LinearMap.mulRight F b.unop
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [mul_add]
  commutes' c := by ext; simp [Algebra.smul_def, Algebra.commutes]

@[simp]
lemma Algebra.rmul_apply (b : Bᵐᵒᵖ) (z : B) : Algebra.rmul F B b z = z * b.unop := rfl

lemma Algebra.rmul_injective : Function.Injective (Algebra.rmul F B) := fun b c h ↦
  MulOpposite.unop_injective <| by simpa using DFunLike.congr_fun h 1
