module

public import BrauerGroup.Algebra.Algebra.Subalgebra.Centralizer
public import BrauerGroup.Algebra.Algebra.Subalgebra.Conj
public import BrauerGroup.Algebra.Central.TensorProduct
public import BrauerGroup.RingTheory.SimpleRing.Basic
public import BrauerGroup.RingTheory.SimpleRing.End
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct
public import BrauerGroup.RingTheory.SkolemNoether
public import Mathlib.Algebra.Central.End
public import Mathlib.LinearAlgebra.Basis.MulOpposite

/-!
# Centralizers in central simple algebras

Let `A` be a finite-dimensional central simple algebra over a field `F` and let `B` be a simple
subalgebra of `A`. This file proves that the centralizer of `B` in `A` is again a simple ring,
and that its dimension satisfies `dim C_A(B) * dim B = dim A`.

Both proofs embed `B` into `T := A ⊗[F] Module.End F B` twice: once as `b ↦ b ⊗ 1` and once as
`b ↦ 1 ⊗ (left multiplication by b)`. By Skolem–Noether the two embeddings are conjugate by a
unit of `T`, hence so are the centralizers of their ranges (`AlgHom.range_conj` and
`Subalgebra.conj_centralizer`). The first centralizer is `C_A(B) ⊗ End F B`, the second is
`A ⊗ Bᵐᵒᵖ` (by `Subalgebra.centralizer_range_lmul`); comparing simplicity and dimensions of
the two sides yields the results.

## Main results

* `Subalgebra.centralizer_isSimple`: the centralizer of a simple subalgebra of a
  finite-dimensional central simple algebra is simple.
* `Subalgebra.finrank_centralizer_mul_finrank`: `dim C_A(B) * dim B = dim A`.
-/

@[expose] public section

universe u v

open scoped TensorProduct

section CentralSimple

variable {F : Type u} {A : Type v} [Field F] [Ring A] [Algebra F A]

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

/-- In `A ⊗[F] C`, the centralizer of `B ⊗ 1` is `C_A(B) ⊗ C`; in particular its dimension
is `dim C_A(B) * dim C`. -/
private lemma finrank_centralizer_includeLeft (B : Subalgebra F A) (C : Type*)
    [Ring C] [Algebra F C] :
    Module.finrank F (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F) (B := C)).comp B.val).range :
        Set (A ⊗[F] C))) =
      Module.finrank F (Subalgebra.centralizer F (B : Set A)) * Module.finrank F C := by
  haveI : Module.Free F C := Module.Free.of_divisionRing F C
  haveI : Module.Free F (Subalgebra.centralizer F (B : Set A)) := by
    exact Module.Free.of_divisionRing F ↥(Subalgebra.centralizer F (B : Set A))
  rw [AlgHom.range_comp, Subalgebra.range_val,
    Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct]
  have vinj : Function.Injective (Algebra.TensorProduct.map
      (Subalgebra.centralizer F (B : Set A)).val (AlgHom.id F C)) := by
    change Function.Injective (LinearMap.rTensor _ _)
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [← (AlgEquiv.ofInjective _ vinj).toLinearEquiv.finrank_eq, Module.finrank_tensorProduct]

/-- In `A ⊗[F] Module.End F B`, the centralizer of `B` embedded as
`b ↦ 1 ⊗ (left multiplication by b)` is `A ⊗ Bᵐᵒᵖ`; in particular its dimension is
`dim A * dim B`. -/
private lemma finrank_centralizer_includeRight_lmul (B : Type*) [Ring B] [Algebra F B] :
    Module.finrank F (Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
        (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B))) =
      Module.finrank F A * Module.finrank F B := by
  haveI : Module.Free F A := Module.Free.of_divisionRing F A
  rw [AlgHom.range_comp,
    Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct]
  have einj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F A)
      (Subalgebra.centralizer F
        ((Algebra.lmul F B).range : Set (Module.End F B))).val) := by
    change Function.Injective (LinearMap.lTensor _ _)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  haveI : Module.Free F (Subalgebra.centralizer F
      ((Algebra.lmul F B).range : Set (Module.End F B))) := by
    exact Module.Free.of_divisionRing F ↥(Subalgebra.centralizer F
      ((Algebra.lmul F B).range : Set (Module.End F B)))
  rw [← (AlgEquiv.ofInjective _ einj).toLinearEquiv.finrank_eq,
    Module.finrank_tensorProduct]
  congr 1
  rw [← (AlgEquiv.ofInjective _ (Algebra.rmul_injective F B)).trans
      (Subalgebra.equivOfEq _ _ (Subalgebra.centralizer_range_lmul F B).symm)
    |>.toLinearEquiv.finrank_eq]
  exact MulOpposite.finrank

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
  have e : Bᵐᵒᵖ ≃ₐ[F] (Subalgebra.centralizer F
      ((Algebra.lmul F B).range : Set (Module.End F B))) :=
    (AlgEquiv.ofInjective _ (Algebra.rmul_injective F B)).trans <|
        Subalgebra.equivOfEq _ _ (Subalgebra.centralizer_range_lmul F B).symm
  have einj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F A)
      (Subalgebra.centralizer F
        ((Algebra.lmul F B).range : Set (Module.End F B))).val) := by
    change Function.Injective (LinearMap.lTensor _ _)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have e2 : (A ⊗[F] Bᵐᵒᵖ) ≃+* (Algebra.TensorProduct.map (AlgHom.id F A)
      (Subalgebra.centralizer F
        ((Algebra.lmul F B).range : Set (Module.End F B))).val).range :=
    ((Algebra.TensorProduct.congr .refl e).trans (AlgEquiv.ofInjective _ einj)).toRingEquiv
  exact .of_ringEquiv e2
    (Algebra.TensorProduct.isSimpleRing (K := F) (A := A) (B := Bᵐᵒᵖ))

/-- By Skolem–Noether, the centralizers of the two embeddings of `B` into
`A ⊗[F] Module.End F B` are conjugate. -/
private lemma exists_centralizer_includeRight_eq_conj [FiniteDimensional F A]
    (B : Subalgebra F A) [IsSimpleRing B] :
    ∃ x : (A ⊗[F] Module.End F B)ˣ,
      Subalgebra.centralizer F
        (((Algebra.TensorProduct.includeRight (R := F) (A := A)).comp
          (Algebra.lmul F B)).range : Set (A ⊗[F] Module.End F B)) =
      (Subalgebra.centralizer F
        (((Algebra.TensorProduct.includeLeft (R := F) (S := F)
          (B := Module.End F B)).comp B.val).range :
          Set (A ⊗[F] Module.End F B))).conj x := by
  obtain ⟨x, hx⟩ := skolemNoether F (A ⊗[F] Module.End F B) B
    (Algebra.TensorProduct.includeLeft.comp B.val)
    (Algebra.TensorProduct.includeRight.comp (Algebra.lmul F B))
  exact ⟨x, by rw [AlgHom.range_conj hx, Subalgebra.conj_centralizer]⟩

/-- The centralizer of a simple subalgebra of a finite-dimensional central simple algebra is
simple. -/
@[stacks 074S "second part"]
theorem Subalgebra.centralizer_isSimple [FiniteDimensional F A] (B : Subalgebra F A)
    [IsSimpleRing B] :
    IsSimpleRing (Subalgebra.centralizer F (B : Set A)) := by
  obtain ⟨x, hE⟩ := exists_centralizer_includeRight_eq_conj B
  have h1 : IsSimpleRing ((Subalgebra.centralizer F
      (((Algebra.TensorProduct.includeLeft (R := F) (S := F)
        (B := Module.End F B)).comp B.val).range :
        Set (A ⊗[F] Module.End F B))).conj x) :=
    .of_ringEquiv (Subalgebra.equivOfEq _ _ hE).toRingEquiv
      (isSimpleRing_centralizer_includeRight_lmul (F := F) (A := A) B)
  exact isSimpleRing_of_centralizer_includeLeft _ _
    ((Subalgebra.isSimpleRing_conj_iff _ x).1 h1)

/-- The dimension of the centralizer of a simple subalgebra `B` of a finite-dimensional
central simple algebra `A` satisfies `dim C_A(B) * dim B = dim A`. -/
@[stacks 074S "first part"]
theorem Subalgebra.finrank_centralizer_mul_finrank [FiniteDimensional F A]
    (B : Subalgebra F A) [IsSimpleRing B] :
    Module.finrank F (Subalgebra.centralizer F (B : Set A)) * Module.finrank F B =
      Module.finrank F A := by
  haveI : Nontrivial B := ⟨1, 0, fun h ↦ one_ne_zero (α := A) (congrArg Subtype.val h)⟩
  obtain ⟨x, hE⟩ := exists_centralizer_includeRight_eq_conj B
  have key := (finrank_centralizer_includeLeft B (Module.End F B)).symm.trans <|
    ((congrArg (fun S : Subalgebra F (A ⊗[F] Module.End F B) ↦ Module.finrank F ↥S) hE).trans
      (Subalgebra.finrank_conj _ x)).symm.trans <|
    finrank_centralizer_includeRight_lmul (F := F) (A := A) B
  rw [Module.End.finrank_eq (Module.finrank F B) rfl, pow_two, ← mul_assoc] at key
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Module.finrank_pos.ne') key

/-- The double centralizer theorem: in a finite-dimensional central simple algebra `A`, the
centralizer of the centralizer of a simple subalgebra `B` is `B` itself. -/
@[stacks 074S "third part"]
theorem Subalgebra.centralizer_centralizer [FiniteDimensional F A] (B : Subalgebra F A)
    [IsSimpleRing B] :
    Subalgebra.centralizer F (Subalgebra.centralizer F (B : Set A) : Set A) = B := by
  haveI := B.centralizer_isSimple
  haveI : Nontrivial (Subalgebra.centralizer F (B : Set A)) :=
    ⟨1, 0, fun h ↦ one_ne_zero (α := A) (congrArg Subtype.val h)⟩
  refine (Subalgebra.eq_of_le_of_finrank_eq (Subalgebra.le_centralizer_centralizer F) ?_).symm
  have h3 := B.finrank_centralizer_mul_finrank.trans
    (Subalgebra.centralizer F (B : Set A)).finrank_centralizer_mul_finrank.symm
  rw [mul_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Module.finrank_pos.ne') h3

/-- A finite-dimensional central simple algebra decomposes as the tensor product of any
central simple subalgebra and its centralizer. -/
@[stacks 074U]
noncomputable def Subalgebra.tensorCentralizerEquiv [FiniteDimensional F A]
    (B : Subalgebra F A) [IsSimpleRing B] [Algebra.IsCentral F B] :
    A ≃ₐ[F] B ⊗[F] Subalgebra.centralizer F (B : Set A) :=
  haveI := B.centralizer_isSimple
  (AlgEquiv.ofBijective
    (Algebra.TensorProduct.lift B.val (Subalgebra.centralizer F (B : Set A)).val
      fun b c ↦ show _ = _ by simpa using c.2 b b.2)
    (AlgHom.bijective_of_finrank_eq _ (by
      rw [Module.finrank_tensorProduct, ← B.finrank_centralizer_mul_finrank, mul_comm]))).symm

end CentralSimple
