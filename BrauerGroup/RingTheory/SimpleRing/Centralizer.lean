module

public import BrauerGroup.Algebra.Algebra.Subalgebra.Centralizer
public import BrauerGroup.Algebra.Central.TensorProduct
public import BrauerGroup.RingTheory.SimpleRing.End
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct
public import BrauerGroup.RingTheory.SkolemNoether
public import Mathlib.Algebra.Central.End

/-!
# Simplicity of centralizers in central simple algebras

Let `A` be a finite-dimensional central simple algebra over a field `F` and let `B` be a simple
subalgebra of `A`. This file proves that the centralizer of `B` in `A` is again a simple ring.

The proof embeds `B` into `T := A ⊗[F] Module.End F B` twice: once as `b ↦ b ⊗ 1` and once as
`b ↦ 1 ⊗ (left multiplication by b)`. By Skolem–Noether the two embeddings are conjugate by a
unit of `T`, hence so are the centralizers of their ranges. The first centralizer is
`C_A(B) ⊗ End F B`, the second is `A ⊗ Bᵐᵒᵖ` (by `Subalgebra.centralizer_range_lmul`), which is
simple; simplicity then descends to the tensor factor `C_A(B)`.

## Main results

* `Subalgebra.centralizer_isSimple`: the centralizer of a simple subalgebra of a
  finite-dimensional central simple algebra is simple.
-/

@[expose] public section

universe u v

open scoped TensorProduct

section CentralSimple

variable {F : Type u} {A : Type v} [Field F] [Ring A] [Algebra F A]

private lemma conj_mem_centralizer_range {B : Type*} [Ring B] [Algebra F B]
    {f g : B →ₐ[F] A} {x : Aˣ} (hx : ∀ b, g b = x * f b * x⁻¹) {t : A}
    (ht : t ∈ Subalgebra.centralizer F (g.range : Set A)) :
    ↑x⁻¹ * t * ↑x ∈ Subalgebra.centralizer F (f.range : Set A) := by
  rw [Subalgebra.mem_centralizer_iff] at ht ⊢
  rintro _ ⟨b, rfl⟩
  have h1 : (f b : A) = ↑x⁻¹ * g b * ↑x := by rw [hx b]; simp [mul_assoc]
  have h2 := ht (g b) ⟨b, rfl⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h1]
  simp only [mul_assoc, Units.mul_inv_cancel_left]
  rw [← mul_assoc (g b) t, h2, mul_assoc]

/-- Simplicity of the centralizer transfers between the ranges of two conjugate algebra
homomorphisms, by conjugating with the unit. -/
private lemma isSimpleRing_centralizer_of_conj {B : Type*} [Ring B] [Algebra F B]
    {f g : B →ₐ[F] A} {x : Aˣ} (hx : ∀ b, g b = x * f b * x⁻¹)
    (hg : IsSimpleRing (Subalgebra.centralizer F (g.range : Set A))) :
    IsSimpleRing (Subalgebra.centralizer F (f.range : Set A)) :=
  .of_ringEquiv (R := Subalgebra.centralizer F (g.range : Set A))
    { toFun t := ⟨↑x⁻¹ * t * ↑x, conj_mem_centralizer_range hx t.2⟩
      invFun t := ⟨↑x * t * ↑x⁻¹, by
        simpa using conj_mem_centralizer_range (f := g) (g := f) (x := x⁻¹)
          (fun b ↦ by rw [hx b]; simp [mul_assoc]) t.2⟩
      left_inv t := Subtype.ext <| by simp [mul_assoc]
      right_inv t := Subtype.ext <| by simp [mul_assoc]
      map_mul' s t := Subtype.ext <| by simp [mul_assoc]
      map_add' s t := Subtype.ext <| by simp [mul_add, add_mul, mul_assoc] }
    hg

/-- If the centralizer of `B ⊗ 1` in `A ⊗[F] C` is simple, then so is the centralizer of `B`
in `A`: the former is isomorphic to `C_A(B) ⊗[F] C`, and simplicity descends to the left
tensor factor. -/
private lemma isSimpleRing_of_centralizer_includeLeft (B : Subalgebra F A) (C : Type*)
    [Ring C] [Algebra F C]
    (h : IsSimpleRing (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := C)).comp B.val).range :
        Set (A ⊗[F] C)))) :
    IsSimpleRing (Subalgebra.centralizer F (B : Set A)) := by
  rw [AlgHom.range_comp, Subalgebra.range_val,
    Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct] at h
  have vinj : Function.Injective (Algebra.TensorProduct.map
      (Subalgebra.centralizer F (B : Set A)).val (AlgHom.id F C)) := by
    change Function.Injective (LinearMap.rTensor _ _)
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  haveI : IsSimpleRing ((Subalgebra.centralizer F (B : Set A)) ⊗[F] C) := by
    exact .of_ringEquiv (AlgEquiv.ofInjective _ vinj).symm.toRingEquiv h
  exact IsSimpleRing.left_of_tensor (K := F)
    (A := Subalgebra.centralizer F (B : Set A)) (B := C)

variable [Algebra.IsCentral F A] [IsSimpleRing A]

/-- The centralizer in `A ⊗[F] Module.End F B` of `B` embedded as
`b ↦ 1 ⊗ (left multiplication by b)` is simple: it is isomorphic to `A ⊗[F] Bᵐᵒᵖ` by
`Subalgebra.centralizer_range_lmul`. -/
private lemma isSimpleRing_centralizer_includeRight_lmul (B : Type*) [Ring B] [Algebra F B]
    [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
        (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B))) := by
  rw [AlgHom.range_comp,
    Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct]
  have e : A ⊗[F] Bᵐᵒᵖ ≃ₐ[F]
      A ⊗[F] (Subalgebra.centralizer F ((Algebra.lmul F B).range : Set (Module.End F B))) :=
    Algebra.TensorProduct.congr .refl <|
      (AlgEquiv.ofInjective _ (Algebra.rmul_injective F B)).trans <|
        Subalgebra.equivOfEq _ _ (Subalgebra.centralizer_range_lmul F B).symm
  have einj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F A)
      (Subalgebra.centralizer F
        ((Algebra.lmul F B).range : Set (Module.End F B))).val) := by
    change Function.Injective (LinearMap.lTensor _ _)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  exact .of_ringEquiv (e.trans (AlgEquiv.ofInjective _ einj)).toRingEquiv inferInstance

/-- The centralizer of a simple subalgebra of a finite-dimensional central simple algebra is
simple. -/
@[stacks 074S "second part"]
theorem Subalgebra.centralizer_isSimple [FiniteDimensional F A] (B : Subalgebra F A)
    [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer F (B : Set A)) := by
  haveI : Nontrivial B := ⟨1, 0, fun h ↦ one_ne_zero (α := A) (congrArg Subtype.val h)⟩
  haveI : FiniteDimensional F B := .of_injective B.val.toLinearMap Subtype.val_injective
  obtain ⟨x, hx⟩ := skolemNoether F (A ⊗[F] Module.End F B) B
    (Algebra.TensorProduct.includeLeft.comp B.val)
    (Algebra.TensorProduct.includeRight.comp (Algebra.lmul F B))
  have h1 := isSimpleRing_centralizer_includeRight_lmul (F := F) (A := A) B
  have h2 := isSimpleRing_centralizer_of_conj (F := F) hx h1
  exact isSimpleRing_of_centralizer_includeLeft B (Module.End F B) h2

end CentralSimple
