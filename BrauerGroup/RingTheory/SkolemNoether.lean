module

public import BrauerGroup.RingTheory.Morita.SimpleRing
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct
public import Mathlib.Algebra.Azumaya.Defs

/-!
# The Skolem–Noether theorem

`skolemNoether`: any two `K`-algebra homomorphisms `f g : B →ₐ[K] A` from a simple `K`-algebra
`B` to a finite-dimensional central simple `K`-algebra `A` are conjugate by a unit of `A`.

The proof is by the regular representation. `A` becomes a `B ⊗[K] Aᵐᵒᵖ`-module in two ways:
`(b ⊗ aᵒᵖ) • x = f b * x * a`, and its `g`-twin (`SkolemNoether.Twist`). The algebra
`B ⊗[K] Aᵐᵒᵖ` is simple (`B` is simple and `Aᵐᵒᵖ` is central simple), and the two module
structures live on the same carrier, so they have equal dimension over `K` and are therefore
isomorphic as `B ⊗[K] Aᵐᵒᵖ`-modules (stacks 074E(3)). An isomorphism `φ` commutes with right
multiplication (the `1 ⊗ Aᵐᵒᵖ` part of linearity), hence is left multiplication by the unit
`φ 1`; the `B ⊗ 1` part of linearity is then exactly the conjugacy `g b = φ 1 * f b * (φ 1)⁻¹`.
-/

universe u v

open scoped TensorProduct

namespace SkolemNoether

variable (K : Type u) (A B : Type v) [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- The algebra map `B ⊗[K] Aᵐᵒᵖ →ₐ[K] End K A` sending `b ⊗ aᵒᵖ` to `x ↦ f b * x * a`,
twisting the left-multiplication part of `AlgHom.mulLeftRight` by `f`. -/
public def toEnd (f : B →ₐ[K] A) : B ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

public lemma toEnd_tmul (f : B →ₐ[K] A) (b : B) (a : Aᵐᵒᵖ) (x : A) :
    toEnd K A B f (b ⊗ₜ[K] a) x = f b * x * a.unop := by
  simp [toEnd, AlgHom.mulLeftRight_apply]

/-- `A`, regarded as a `B ⊗[K] Aᵐᵒᵖ`-module through `f : B →ₐ[K] A`:
`(b ⊗ aᵒᵖ) • x = f b * x * a`. -/
@[no_expose, nolint unusedArguments]
def Twist (_ : B →ₐ[K] A) : Type v := A
  deriving AddCommGroup, Module K

namespace Twist

variable (f : B →ₐ[K] A)

instance : Module (B ⊗[K] Aᵐᵒᵖ) (Twist K A B f) :=
  Module.compHom A (toEnd K A B f).toRingHom

/-- The identity map `A → Twist K A B f`. -/
def mk (x : A) : Twist K A B f := x

/-- The identity map `Twist K A B f → A`. -/
def val (x : Twist K A B f) : A := x

lemma val_injective : Function.Injective (val K A B f) := fun _ _ h ↦ h

variable {K A B f}

@[simp] lemma val_mk (x : A) : val K A B f (mk K A B f x) = x := rfl

@[simp] lemma mk_val (x : Twist K A B f) : mk K A B f (val K A B f x) = x := rfl

lemma val_smul (r : B ⊗[K] Aᵐᵒᵖ) (x : Twist K A B f) :
    val K A B f (r • x) = toEnd K A B f r (val K A B f x) := rfl

@[simp] lemma val_one_op_smul (a : A) (x : Twist K A B f) :
    val K A B f (((1 : B) ⊗ₜ[K] MulOpposite.op a) • x) = val K A B f x * a := by
  rw [val_smul, toEnd_tmul, map_one, one_mul, MulOpposite.unop_op]

@[simp] lemma val_tmul_one_smul (b : B) (x : Twist K A B f) :
    val K A B f ((b ⊗ₜ[K] (1 : Aᵐᵒᵖ)) • x) = f b * val K A B f x := by
  rw [val_smul, toEnd_tmul, MulOpposite.unop_one, mul_one]

@[simp] lemma one_op_smul_mk (a x : A) :
    ((1 : B) ⊗ₜ[K] MulOpposite.op a) • mk K A B f x = mk K A B f (x * a) :=
  val_injective K A B f (by rw [val_one_op_smul, val_mk, val_mk])

@[simp] lemma tmul_one_smul_mk (b : B) (x : A) :
    (b ⊗ₜ[K] (1 : Aᵐᵒᵖ)) • mk K A B f x = mk K A B f (f b * x) :=
  val_injective K A B f (by rw [val_tmul_one_smul, val_mk, val_mk])

variable (K A B f)

instance : IsScalarTower K (B ⊗[K] Aᵐᵒᵖ) (Twist K A B f) :=
  .of_algebraMap_smul fun k x ↦ by
    have h : val K A B f (algebraMap K (B ⊗[K] Aᵐᵒᵖ) k • x) = k • val K A B f x := by
      rw [val_smul, AlgHom.commutes]
      exact Module.algebraMap_end_apply K K A k (val K A B f x)
    exact h

instance [FiniteDimensional K A] : Module.Finite K (Twist K A B f) :=
  inferInstanceAs (Module.Finite K A)

instance [FiniteDimensional K A] : Module.Finite (B ⊗[K] Aᵐᵒᵖ) (Twist K A B f) :=
  Module.Finite.of_restrictScalars_finite K _ _

end Twist

variable {K A B}

/-- A `B ⊗[K] Aᵐᵒᵖ`-linear map between twisted regular representations commutes with right
multiplication, hence is left multiplication by its value at `1`. -/
private lemma val_apply_mk {f g : B →ₐ[K] A}
    (φ : Twist K A B f ≃ₗ[B ⊗[K] Aᵐᵒᵖ] Twist K A B g) (x : A) :
    Twist.val K A B g (φ (Twist.mk K A B f x))
      = Twist.val K A B g (φ (Twist.mk K A B f 1)) * x := by
  simpa using congrArg (Twist.val K A B g)
    (φ.map_smul ((1 : B) ⊗ₜ[K] MulOpposite.op x) (Twist.mk K A B f 1))

private lemma mul_val_symm_eq_one {f g : B →ₐ[K] A}
    (φ : Twist K A B f ≃ₗ[B ⊗[K] Aᵐᵒᵖ] Twist K A B g) :
    Twist.val K A B g (φ (Twist.mk K A B f 1))
      * Twist.val K A B f (φ.symm (Twist.mk K A B g 1)) = 1 := by
  rw [← val_apply_mk φ, Twist.mk_val, LinearEquiv.apply_symm_apply, Twist.val_mk]

end SkolemNoether

open SkolemNoether in
/-- **Skolem–Noether**: two algebra homomorphisms from a simple algebra to a
finite-dimensional central simple algebra are conjugate by a unit. -/
public theorem skolemNoether (K : Type u) (A B : Type v) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [Ring B] [Algebra K B] [IsSimpleRing B] (f g : B →ₐ[K] A) :
    ∃ x : Aˣ, ∀ b : B, g b = x * f b * x⁻¹ := by
  have hf : Function.Injective f :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain f.toRingHom).resolve_right
      (not_subsingleton A)
  have : FiniteDimensional K B := .of_injective f.toLinearMap hf
  obtain ⟨φ⟩ := (linearEquiv_iff_finrank_eq_over_simple_ring K (B ⊗[K] Aᵐᵒᵖ)
    (Twist K A B f) (Twist K A B g)).2 rfl
  refine ⟨⟨_, _, mul_val_symm_eq_one φ, mul_val_symm_eq_one φ.symm⟩, fun b ↦ ?_⟩
  rw [Units.eq_mul_inv_iff_mul_eq, ← val_apply_mk φ (f b), ← mul_one (f b),
    ← Twist.tmul_one_smul_mk, map_smul]
  simp
