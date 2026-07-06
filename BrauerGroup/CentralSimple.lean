/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/
module

public import BrauerGroup.Algebra.Central.TensorProduct
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct
public import BrauerGroup.Wedderburn
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.RingTheory.Flat.Basic

/-!
# Characteristic predicate for central simple algebras

In this file we define the predicate `IsCentralSimple K D` where `K` is a field
and `D` is a (noncommutative) `K`-algebra.

Note that the predicate makes sense just for `K` a `CommRing` but it doesn't give the
right definition; for a commutative ring base one should use the theory of Azumaya algebras.
This adds an extra layer of complication which we don't need. In fact ideals of `K`
immediately give rise to nontrivial quotients of `D` so there are no central simple
algebras in this case according to our definition.

-/

@[expose] public section

universe u v w

open Module

-- class IsCentralSimple
--     (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] : Prop where
--   is_central : Subalgebra.center K D ≤ ⊥
--   [is_simple : IsSimpleRing D]

-- lemma IsCentralSimple.center_eq
--     (K D : Type*) [Field K] [Ring D] [Algebra K D] [IsCentralSimple K D] :
--     Subalgebra.center K D = ⊥ :=
--   le_antisymm IsCentralSimple.is_central <| by
--     rintro _ ⟨x, rfl⟩
--     rw [Subalgebra.mem_center_iff]
--     exact (Algebra.commutes' x · |>.symm)

variable (K : Type u) [Field K]

namespace IsCentralSimple

variable (D : Type v) [Ring D] [Algebra K D]

/-
\begin{lemma}
    \label{IsCentralSimple.baseChange}
    If DD is a central simple algebra over~KK and L/KL/K is a field extension, then L⊗KDL\otimes_KD
    is a central simple algebra over~LL.
\end{lemma}
\begin{proof}
    This is not too hard: it's lemma b of section 12.4 in Peirce's "Associative algebras".
    Will maybe write more on Saturday.
\end{proof}
-/
open scoped TensorProduct

section should_be_elsewhere

instance (B : Type*) [Ring B] [Algebra K B] : Algebra K (Subring.center B) :=
  RingHom.toAlgebra <| (algebraMap K B).codRestrict _ fun x ↦ by
    rw [Subring.mem_center_iff]
    exact fun y ↦ Algebra.commutes x y |>.symm

lemma TensorProduct.sum_tmul_basis_right_eq_zero'
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιC : Type*} (𝒞 : Basis ιC K C)
    (s : Finset ιC) (b : ιC → B)
    (h : ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = 0) :
    ∀ i ∈ s, b i = 0 := by
  classical
  intro i
  have := TensorProduct.sum_tmul_basis_right_eq_zero (κ := ιC) 𝒞 (M := B)
    { support := s.filter fun i ↦ b i ≠ 0
      toFun x := if x ∈ s then b x else 0
      mem_support_toFun := by simp }
    (by
      simp only [Finsupp.sum, ne_eq, Finsupp.coe_mk, Finset.sum_filter, ite_not]
      convert h using 1
      congr!
      aesop)
  simpa using Finsupp.ext_iff.mp this i

end should_be_elsewhere

noncomputable def centerTensorCenter (B C : Type v) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    (Subalgebra.center K B ⊗[K] Subalgebra.center K C) →ₗ[K] (B ⊗[K] C) :=
  TensorProduct.map (Subalgebra.val _).toLinearMap (Subalgebra.val _).toLinearMap

lemma centerTensorCenter_injective (B C : Type v) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Function.Injective (centerTensorCenter K B C) := by
  have : centerTensorCenter K B C =
    ((Subalgebra.center K B).val.toLinearMap.rTensor _) ∘ₗ
    ((Subalgebra.center K C).val.toLinearMap.lTensor _) := by
    ext; simp [centerTensorCenter]
  rw [this]
  apply Function.Injective.comp (g := (Subalgebra.center K B).val.toLinearMap.rTensor _)
  · apply Module.Flat.rTensor_preserves_injective_linearMap
    exact Subtype.val_injective
  · apply Module.Flat.lTensor_preserves_injective_linearMap
    exact Subtype.val_injective

noncomputable def centerTensor
    (B C : Type u) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K B ⊗[K] Subalgebra.center K C ≃ₗ[K]
    Subalgebra.center K (B ⊗[K] C) :=
    LinearEquiv.ofInjective (centerTensorCenter K B C) (centerTensorCenter_injective K B C) ≪≫ₗ
    (show _ ≃ₗ[K] Subalgebra.toSubmodule (Subalgebra.center K (B ⊗[K] C)) from LinearEquiv.ofLinear
      (Submodule.inclusion (by
        rw [center_tensor_center]
        intro x hx
        simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, AlgHom.mem_range] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        refine ⟨y, rfl⟩))
      (Submodule.inclusion (by
        intro x hx
        simp only [Subalgebra.mem_toSubmodule, LinearMap.mem_range] at hx ⊢
        rw [center_tensor_center] at hx
        simp only [AlgHom.mem_range] at hx
        obtain ⟨y, rfl⟩ := hx
        refine ⟨y, rfl⟩)) rfl rfl)

instance TensorProduct.nontrivial
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[K] B) :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K A B
    (algebraMap K B).injective

end IsCentralSimple

section CSA_implies_CSA
variable (K : Type u) [Field K]
variable (B : Type*) [Ring B]

lemma top_eq_ring (R : Type*) [Ring R] : (⊤ : TwoSidedIdeal R) = (⊤ : Set R) := by
  aesop

theorem CSA_implies_CSA (K : Type*) (B : Type v) [Field K] [Ring B] [Algebra K B]
    (n : ℕ) (D : Type v) [NeZero n] (h : DivisionRing D) [Algebra K D]
    (Wdb : B ≃ₐ[K] (Matrix (Fin n) (Fin n) D)) [Algebra.IsCentral K B] [IsSimpleRing B] :
    Algebra.IsCentral K D := by
  refine ⟨fun d hd => ?_⟩
  obtain ⟨k, hk⟩ := (Algebra.IsCentral.of_algEquiv K B (Matrix (Fin n) (Fin n) D) Wdb).1
    (show (Matrix.diagonal fun _ ↦ d) ∈ _ by
      rw [Matrix.mem_center_iff']
      refine ⟨⟨d, hd⟩, ?_⟩
      ext i j
      simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero]
      split_ifs
      · change _ = d • (1 : D)
        simp only [smul_eq_mul, mul_one]
      · rfl)
  exact ⟨k, by simpa [Matrix.algebraMap_eq_diagonal] using congr($hk 0 0)⟩

end CSA_implies_CSA
