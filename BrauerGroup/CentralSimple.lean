/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Kevin Buzzard
-/
import BrauerGroup.Centralizer
import BrauerGroup.Wedderburn
import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.Flat.Basic

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

open Matrix in
instance MatrixRing.isCentral (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    Algebra.IsCentral K (Matrix ι ι K) where
  out _ h := mem_range_scalar_of_commute_single fun _ _ _ =>
    Subalgebra.mem_center_iff.mp h _

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

lemma TensorProduct.sum_tmul_basis_left_eq_zero'
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιB : Type*} (ℬ : Basis ιB K B)
    (s : Finset ιB) (c : ιB → C)
    (h : ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = 0) :
    ∀ i ∈ s, c i = 0 := by
  apply TensorProduct.sum_tmul_basis_right_eq_zero' K C B ℬ s c
  apply_fun TensorProduct.comm K B C at h
  simpa using h

lemma TensorProduct.left_tensor_base_sup_base_tensor_right
    (K B C : Type*) [CommRing K] [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    (Algebra.TensorProduct.map (AlgHom.id K B) (Algebra.ofId K C)).range ⊔
    (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C)).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | tmul b c =>
    rw [show b ⊗ₜ[K] c = b ⊗ₜ[K] 1 * 1 ⊗ₜ[K] c by simp]
    exact Algebra.mul_mem_sup ⟨b ⊗ₜ 1, by simp⟩ ⟨1 ⊗ₜ c, by simp⟩
  | add x y hx hy =>
    exact Subalgebra.add_mem _ hx hy

-- We need to restrict the universe, because we used properties of flatness.
lemma TensorProduct.submodule_tensor_inf_tensor_submodule
    (B C : Type u) [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (b : Submodule K B) (c : Submodule K C) :
    LinearMap.range (TensorProduct.map b.subtype .id) ⊓
    LinearMap.range (TensorProduct.map .id c.subtype) =
    LinearMap.range (TensorProduct.map b.subtype c.subtype) := by
  refine le_antisymm ?_ ?_
  · letI : Module.Flat K (B ⧸ b) := Module.Flat.of_free
    let u : b ⊗[K] c →ₗ[K] B ⊗[K] c := TensorProduct.map b.subtype LinearMap.id
    let v : B ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] c :=
      TensorProduct.map (Submodule.mkQ _) LinearMap.id
    have exactuv : Function.Exact u v := by
      apply rTensor_exact _ _ (Submodule.mkQ_surjective _)
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
    let u' : b ⊗[K] C →ₗ[K] B ⊗[K] C := TensorProduct.map b.subtype LinearMap.id
    let v' : B ⊗[K] C →ₗ[K] (B ⧸ b) ⊗[K] C := TensorProduct.map (Submodule.mkQ _) LinearMap.id
    have exactu'v' : Function.Exact u' v' := by
      apply rTensor_exact _ _ (Submodule.mkQ_surjective _)
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
    let α : b ⊗[K] c →ₗ[K] b ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    let β : B ⊗[K] c →ₗ[K] B ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    let γ : (B ⧸ b) ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    have γ_inj : Function.Injective γ :=
      Module.Flat.iff_lTensor_preserves_injective_linearMap (R := K) (M := B ⧸ b)|>.1 inferInstance
        c.subtype c.injective_subtype
    rintro z (hz : z ∈ LinearMap.range u' ⊓ LinearMap.range β)
    obtain ⟨z, rfl⟩ := hz.2
    have comm0 : v' ∘ₗ β = γ ∘ₗ v := by
      ext
      simp [v', β, γ, v]
    have hz1 : v' (β z) = γ (v z) := congr($comm0 z)
    have hz2 : v' (β z) = 0 := by
      rw [← LinearMap.mem_ker]
      rw [LinearMap.exact_iff] at exactu'v'
      rw [exactu'v']
      exact hz.1
    rw [hz2] at hz1
    have hz3 : v z ∈ LinearMap.ker γ := by rw [LinearMap.mem_ker]; exact hz1.symm
    replace hz3 : v z = 0 := by
      rw [← LinearMap.ker_eq_bot] at γ_inj; rw [γ_inj] at hz3; exact hz3
    replace hz3 : z ∈ LinearMap.ker v := hz3
    replace hz3 : z ∈ LinearMap.range u := by
      rw [LinearMap.exact_iff] at exactuv
      rwa [← exactuv]
    obtain ⟨z, rfl⟩ := hz3
    change (β ∘ₗ u) z ∈ _
    have comm1 : β ∘ₗ u = u' ∘ₗ α := by
      ext
      simp [β, u, u', α]
    rw [comm1, LinearMap.comp_apply]
    refine ⟨z, ?_⟩
    simp only [u', α]
    change _ = (TensorProduct.map b.subtype .id ∘ₗ TensorProduct.map .id c.subtype) z
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨TensorProduct.map LinearMap.id c.subtype x, ?_⟩,
      ⟨TensorProduct.map b.subtype LinearMap.id x, ?_⟩⟩
    · change (TensorProduct.map b.subtype LinearMap.id ∘ₗ
        TensorProduct.map LinearMap.id c.subtype) x = _
      rw [← TensorProduct.map_comp]
      rfl
    · change (TensorProduct.map LinearMap.id c.subtype ∘ₗ
        TensorProduct.map b.subtype LinearMap.id) x = _
      rw [← TensorProduct.map_comp]
      rfl

end should_be_elsewhere

-- We need to restrict the universe, because we used properties of flatness.
lemma center_tensorProduct
    (B C : Type u) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K (B ⊗[K] C) =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range := by
  rw [show Subalgebra.center K (B ⊗[K] C) = Subalgebra.centralizer K (⊤ : Subalgebra K (B ⊗[K] C))
    by simp, ← TensorProduct.left_tensor_base_sup_base_tensor_right K B C,
    Subalgebra.centralizer_sup, Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_left,
    Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_right]
  suffices eq :
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (.id K C)).range ⊓
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (.id K B) (Subalgebra.center K C).val).range =
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val
      (Subalgebra.center K C).val).range by
    apply_fun Subalgebra.toSubmodule using Subalgebra.toSubmodule_injective
    rw [← eq]
    ext x
    simp only [Algebra.inf_toSubmodule, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
      AlgHom.mem_range]
  have eq1 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (.id K C)).range
        = LinearMap.range (TensorProduct.map (Subalgebra.center K B).val.toLinearMap .id) := rfl
  rw [eq1]
  have eq2 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (.id K B) (Subalgebra.center K C).val).range
        = LinearMap.range (TensorProduct.map .id (Subalgebra.center K C).val.toLinearMap) := rfl
  rw [eq2]
  have eq3 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range =
      LinearMap.range (TensorProduct.map (Subalgebra.center K B).val.toLinearMap
        (Subalgebra.center K C).val.toLinearMap) := by
    rfl
  rw [eq3]
  have := TensorProduct.submodule_tensor_inf_tensor_submodule K B C
    (Subalgebra.toSubmodule <| .center K B)
    (Subalgebra.toSubmodule <| .center K C)
  have eq4 : (Subalgebra.toSubmodule (Subalgebra.center K B)).subtype =
    (Subalgebra.center K B).val.toLinearMap := by rfl
  rw [eq4] at this
  have eq5 : (Subalgebra.toSubmodule (Subalgebra.center K C)).subtype =
    (Subalgebra.center K C).val.toLinearMap := by rfl
  rw [eq5] at this
  rw [this]

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
        rw [center_tensorProduct]
        intro x hx
        simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, AlgHom.mem_range] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        refine ⟨y, rfl⟩))
      (Submodule.inclusion (by
        intro x hx
        simp only [Subalgebra.mem_toSubmodule, LinearMap.mem_range] at hx ⊢
        rw [center_tensorProduct] at hx
        simp only [AlgHom.mem_range] at hx
        obtain ⟨y, rfl⟩ := hx
        refine ⟨y, rfl⟩)) rfl rfl)

instance TensorProduct.isCentral
    (A B : Type u) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isCentral_A : Algebra.IsCentral K A] [isCentral_B : Algebra.IsCentral K B] :
    Algebra.IsCentral K (A ⊗[K] B) := by
  constructor
  intro _ H
  obtain ⟨x, rfl⟩ := le_of_eq (center_tensorProduct K A B) H; clear H
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨a', ha⟩ := isCentral_A.1 a.2
    obtain ⟨b', hb⟩ := isCentral_B.1 b.2
    refine ⟨b' * a', ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, map_mul, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, ← ha, ← hb]
    rw [Algebra.ofId_apply, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_mul, mul_one]
    rw [← Algebra.ofId_apply, ← Algebra.ofId_apply]
  | add x y hx hy =>
    obtain ⟨kx, hx⟩ := hx
    obtain ⟨ky, hy⟩ := hy
    refine ⟨kx + ky, ?_⟩
    rw [map_add, hx, hy, map_add]

instance TensorProduct.nontrivial
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[K] B) := by
  refine ⟨0, 1, fun r ↦ ?_⟩
  let f : K ⊗[K] B →ₐ[K] A ⊗[K] B :=
    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
  have hf : Function.Injective f := Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap K A).injective
  have r' : f 0 = f 1 := by convert r; simp [f]
  specialize hf r'
  apply_fun Algebra.TensorProduct.lid K B at hf
  simp only [map_zero, map_one] at hf
  exact zero_ne_one hf

variable {K} in
/--
a non-zero element in an ideal that can be represented as a sum of tensor products of `n`-terms.
-/
structure is_obtainable_by_sum_tmul
    {ιA A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (x : A ⊗[K] B) (𝒜 : Basis ιA K A) (I : TwoSidedIdeal <| A ⊗[K] B) (n : ℕ) : Prop where
  mem : x ∈ I
  ne_zero : x ≠ 0
  rep : ∃ (s : Finset ιA) (_ : s.card = n) (f : ιA → B),
    x = ∑ i ∈ s, 𝒜 i ⊗ₜ[K] f i

variable {K} in
lemma is_obtainable_by_sum_tmul.exists_minimal_element
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (ιA : Type*) (𝒜 : Basis ιA K A)
    (I : TwoSidedIdeal (A ⊗[K] B)) (hI : I ≠ ⊥) :
    ∃ (n : ℕ) (x : A ⊗[K] B), is_obtainable_by_sum_tmul x 𝒜 I n ∧
      ∀ (m : ℕ) (y : A ⊗[K] B) , is_obtainable_by_sum_tmul y 𝒜 I m → n ≤ m := by
  classical
  have := SetLike.ext_iff.not.mp hI
  push_neg at this
  obtain ⟨x, ⟨hx0, hx1⟩|⟨hx0, hx1⟩⟩ := this
  pick_goal 2
  · change x = 0 at hx1
    subst hx1
    exact hx0 I.zero_mem |>.elim
  obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_left 𝒜 x
  let n := @Nat.find (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
    ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩
  obtain ⟨x, hx⟩ : ∃ x, is_obtainable_by_sum_tmul x 𝒜 I n :=
    @Nat.find_spec (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩
  refine ⟨n, x, hx, fun m y hy => ?_⟩
  by_contra r
  simp only [not_le] at r
  have := @Nat.find_min (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩ m r
  simp only [not_exists] at this
  exact this y hy

lemma TensorProduct.map_comap_eq_of_isSimple_isCentralSimple
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleOrder <| TwoSidedIdeal A]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B)) :
    I = TwoSidedIdeal.span
      (Set.image (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) <|
        I.comap (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B)) := by
  classical
  refine le_antisymm ?_ ?_
  · if I_ne_bot : I = ⊥
    then subst I_ne_bot; exact bot_le
    else
    let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
    change I ≤ TwoSidedIdeal.span (Set.image f <| I.comap f)
    let 𝒜 := Basis.ofVectorSpace K A
    obtain ⟨n, x, ⟨x_mem, x_ne_zero, ⟨s, card_s, b, rfl⟩⟩, H⟩ :=
      is_obtainable_by_sum_tmul.exists_minimal_element _ 𝒜 I I_ne_bot
    have b_ne_zero : ∀ i ∈ s, b i ≠ 0 := by
      by_contra! h
      rcases h with ⟨i, h1, h2⟩
      specialize H (n - 1) (∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i) ⟨x_mem, x_ne_zero, ⟨s.erase i,
        by rw [Finset.card_erase_of_mem, card_s]; exact h1, b, by
        symm
        fapply Finset.sum_subset
        · exact Finset.erase_subset i s
        · intro x hx1 hx2
          simp only [Finset.mem_erase, ne_eq, not_and] at hx2
          rw [show x = i by tauto, h2, TensorProduct.tmul_zero]⟩⟩
      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i, h1⟩
      omega
    if s_ne_empty : s = ∅
    then
      subst s_ne_empty
      simp only [Finset.card_empty, Finset.sum_empty, ne_eq, not_true_eq_false] at *
    else
      obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr s_ne_empty
      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i₀, hi₀⟩
      have x_eq' :
          ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i =
          𝒜 i₀ ⊗ₜ[K] b i₀ +
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] b i := by
        rw [show 𝒜 i₀ ⊗ₜ[K] b i₀ = ∑ i ∈ {i₀}, 𝒜 i ⊗ₜ[K] b i by rw [Finset.sum_singleton],
          ← Finset.sum_disjUnion]
        pick_goal 2
        · rw [← Finset.disjoint_erase_comm]
          simp only [Finset.erase_singleton, Finset.disjoint_empty_left]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext x
        simp only [Finset.disjUnion_eq_union, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase, ne_eq]
        constructor
        · intro hx
          if hx' : x = i₀ then left; exact hx'
          else right; exact ⟨hx', hx⟩
        · rintro (rfl|⟨_, hx2⟩) <;> assumption
      have span_bi₀ : TwoSidedIdeal.span {b i₀} = ⊤ := isSimple_B.1.2 _ |>.resolve_left fun r ↦ by
        have mem : b i₀ ∈ (⊥ : TwoSidedIdeal B) := by
          rw [← r]
          apply TwoSidedIdeal.subset_span
          simp only [Set.mem_singleton_iff]
        exact b_ne_zero i₀ hi₀ mem
      have one_mem : (1 : B) ∈ TwoSidedIdeal.span {b i₀} := by rw [span_bi₀]; trivial
      rw [TwoSidedIdeal.mem_span_iff_exists_fin] at one_mem
      obtain ⟨ℐ, inst1, xL, xR, y, one_eq⟩ := one_mem
      replace one_eq : 1 = ∑ i : ℐ, xL i * b i₀ * xR i := by
        rw [one_eq]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr
        simpa only [Set.mem_singleton_iff] using (y i).2
      let ω := ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i
      let Ω := ∑ i : ℐ, (1 ⊗ₜ[K] xL i) * ω * (1 ⊗ₜ[K] xR i)
      have Ω_in_I : Ω ∈ I := TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ => I.mul_mem_right _ _ <|
        I.mul_mem_left _ _ x_mem
      have Ω_eq :
          Ω =
          𝒜 i₀ ⊗ₜ[K] (∑ i : ℐ, xL i * b i₀ * xR i) +
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] (∑ j : ℐ, xL j * b i * xR j) := by
        dsimp only [Ω, ω]
        simp only [x_eq', mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
          add_mul, mul_one, Finset.sum_mul, Finset.sum_add_distrib, TensorProduct.tmul_sum,
          add_right_inj]
        rw [Finset.sum_comm]
      rw [← one_eq] at Ω_eq
      have Ω_prop_1 (b : B) : (1 ⊗ₜ b) * Ω - Ω * (1 ⊗ₜ b) ∈ I :=
        I.sub_mem (I.mul_mem_left _ _ Ω_in_I) (I.mul_mem_right _ _ Ω_in_I)
      have Ω_prop_2 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) =
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K]
            (∑ j : ℐ, (x * (xL j * b i * xR j) - (xL j * b i * xR j) * x)) := by
        rw [Ω_eq]
        simp only [TensorProduct.tmul_sum, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, Finset.mul_sum, add_mul, Finset.sum_mul, add_sub_add_left_eq_sub,
          Finset.sum_sub_distrib, TensorProduct.tmul_sub]
      have Ω_prop_3 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) = 0 := by
        by_contra rid
        specialize H (n - 1) (((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x))
          ⟨Ω_prop_1 x, rid, ⟨s.erase i₀, by rw [Finset.card_erase_of_mem, card_s]; exact hi₀, _,
            Ω_prop_2 x⟩⟩
        omega
      simp_rw [Ω_prop_2] at Ω_prop_3
      have Ω_prop_4 : ∀ i ∈ s.erase i₀,
          ∑ j : ℐ, (xL j * b i * xR j) ∈ Subalgebra.center K B := by
        intro i hi
        rw [Subalgebra.mem_center_iff]
        intro x
        specialize Ω_prop_3 x
        simp only [Finset.mul_sum, Finset.sum_mul, ← sub_eq_zero, sub_zero]
        rw [← Finset.sum_sub_distrib, sub_zero]
        simpa using TensorProduct.sum_tmul_basis_left_eq_zero' _ _ _ 𝒜 (s.erase i₀) _ Ω_prop_3 i hi
      simp_rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot, Set.mem_range] at Ω_prop_4
      choose k hk using Ω_prop_4
      have Ω_eq2 := calc Ω
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := Ω_eq
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := by
            congr 1
            exact Finset.sum_attach _ _ |>.symm
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] algebraMap _ _ (k i.1 i.2) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hk i.1 i.2]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 +  ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] (k i.1 i.2 • (1 : B) : B) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Algebra.algebraMap_eq_smul_one]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i) ⊗ₜ[K] (1 : B) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.smul_tmul]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ⊗ₜ[K] (1 : B) := by
            rw [TensorProduct.sum_tmul]
        _ = (𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i))) ⊗ₜ[K] 1 := by
            rw [TensorProduct.add_tmul]
      rw [Ω_eq2] at Ω_in_I
      have hI : I.comap f = ⊤ := isSimple_A.2 _ |>.resolve_left fun r ↦ by
        have mem : 𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ∈ I.comap f := by
          rw [TwoSidedIdeal.mem_comap]
          exact Ω_in_I
        rw [r] at mem
        change _ = 0 at mem
        rw [mem, TensorProduct.zero_tmul] at Ω_eq2
        have LI := 𝒜.linearIndependent
        rw [linearIndependent_iff'] at LI
        specialize LI s (fun i =>
          if i = i₀ then 1
          else if h : i ∈ s.erase i₀ then k i h else 0) (by
          dsimp only
          simp_rw [ite_smul, one_smul, dite_smul, zero_smul]
          rw [Finset.sum_ite,
            show ∑ x ∈ Finset.filter (fun x ↦ x = i₀) s, 𝒜 x = ∑ x ∈ {i₀}, 𝒜 x by
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext
            simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
            rintro rfl
            exact hi₀, Finset.sum_singleton,
            show Finset.filter (fun x ↦ ¬x = i₀) s = s.erase i₀ by
            ext
            simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
            rw [and_comm], ← Finset.sum_attach]
          conv_rhs => rw [← mem]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dif_pos i.2]) i₀ hi₀
        rw [if_pos rfl] at LI
        exact zero_ne_one LI.symm
      rw [hI, TwoSidedIdeal.coe_top_set, TwoSidedIdeal.le_iff]
      rintro x -
      rw [SetLike.mem_coe]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
        exact TwoSidedIdeal.mul_mem_right _ _ _ <| TwoSidedIdeal.subset_span ⟨a, ⟨⟩, rfl⟩
      | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] at hx
    exact hx

instance TensorProduct.simple
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleRing A]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
  suffices eq1 : ∀ (I : TwoSidedIdeal (A ⊗[K] B)),
      I = TwoSidedIdeal.span (Set.image f <| I.comap f) by
    refine ⟨⟨fun I => ?_⟩⟩
    specialize eq1 I
    rcases isSimple_A.1.2 (I.comap f) with h|h
    · left
      rw [h, TwoSidedIdeal.coe_bot_set, Set.image_singleton, map_zero] at eq1
      rw [eq1, eq_bot_iff, TwoSidedIdeal.le_iff]
      rintro x hx
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_span_iff_exists_fin] at hx
      obtain ⟨ι, inst, xL, xR, y, rfl⟩ := hx
      rw [SetLike.mem_coe]
      refine TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ => ?_
      have := (y i).2
      simp only [Set.mem_singleton_iff] at this
      rw [this, mul_zero, zero_mul]
      rfl
    · right
      rw [h, TwoSidedIdeal.coe_top_set] at eq1
      rw [eq1, eq_top_iff, TwoSidedIdeal.le_iff]
      rintro x -
      rw [SetLike.mem_coe]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
        exact TwoSidedIdeal.mul_mem_right _ _ _ <| TwoSidedIdeal.subset_span ⟨a, ⟨⟩, rfl⟩
      | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy
  apply TensorProduct.map_comap_eq_of_isSimple_isCentralSimple

-- We can't have `L` to have different universe level of `D` in this proof, again due that we used
-- `flatness`
set_option synthInstance.maxHeartbeats 40000 in
-- FIXME: Get rid of the raised heartbeats
instance baseChange
    (D L : Type u) [Ring D] [Algebra K D]
    [Field L] [Algebra K L]
    [h : Algebra.IsCentral K D] [IsSimpleRing D] :
    Algebra.IsCentral L (L ⊗[K] D) where
  out:= by
    intro _ H
    obtain ⟨x, rfl⟩ := le_of_eq (center_tensorProduct K L D) H; clear H
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l d =>
      obtain ⟨k, hk⟩ := h.out d.2
      refine ⟨k • l, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        Subalgebra.coe_val, ← hk]
      simp only [Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨kx, (hkx : kx ⊗ₜ 1 = _)⟩ := hx
      obtain ⟨ky, (hky : ky ⊗ₜ 1 = _)⟩ := hy
      exact ⟨kx + ky, by simp only [AlgHom.toRingHom_eq_coe, map_add, RingHom.coe_coe,
        Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, hkx, hky]⟩

end IsCentralSimple

section CSA_implies_CSA
variable (K : Type u) [Field K]
variable (B : Type*) [Ring B]

lemma top_eq_ring (R : Type*) [Ring R] : (⊤ : TwoSidedIdeal R) = (⊤ : Set R) := by
  aesop

lemma _root_.AlgEquiv.isCentral {K B C : Type*}
    [Field K] [Ring B] [Algebra K B]
    [hc : Algebra.IsCentral K B]
    [Ring C] [Algebra K C] (e : B ≃ₐ[K] C) :
    Algebra.IsCentral K C where
  out z hz := by
    obtain ⟨k, hk⟩ := hc.out (show e.symm z ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hz ⊢
      exact fun x ↦ by simpa using congr(e.symm $(hz (e x))))
    exact ⟨k, by simpa [Algebra.ofId_apply] using congr(e $hk)⟩

theorem CSA_implies_CSA (K : Type*) (B : Type*) [Field K] [Ring B] [Algebra K B]
    (n : ℕ) (D : Type*) [NeZero n] (h : DivisionRing D) [Algebra K D]
    (Wdb : B ≃ₐ[K] (Matrix (Fin n) (Fin n) D)) [Algebra.IsCentral K B] [IsSimpleRing B] :
    Algebra.IsCentral K D := by
  refine ⟨fun d hd => ?_⟩
  obtain ⟨k, hk⟩ := Wdb.isCentral.1
    (show (Matrix.diagonal fun _ ↦ d) ∈ _ by
      rw [Matrix.mem_center_iff']
      refine ⟨⟨d, hd⟩, ?_⟩
      ext i j
      simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero]
      split_ifs
      · change _ = d • (1 : D)
        simp only [smul_eq_mul, mul_one]
      · rfl)
  refine ⟨k, ?_⟩
  apply_fun (· 0 0) at hk
  simpa using hk

end CSA_implies_CSA
