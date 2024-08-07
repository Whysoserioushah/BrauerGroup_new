import BrauerGroup.BrauerGroup
import BrauerGroup.Quaternion
import BrauerGroup.AlgClosedUnion
import BrauerGroup.ExtendScalar
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsSepclosed

suppress_compilation

universe u v w
variable (k A K: Type u) [Field k] [Field K] [Algebra k K] [Ring A]
  [Algebra k A]

variable (k_bar : Type u) [Field k_bar] [Algebra k k_bar] [hk_bar : IsAlgClosure k k_bar]
  (k_s : Type u) [Field k_s] [Algebra k k_s] [IsSepClosure k k_s]

open scoped TensorProduct
open RingCon

instance module_over_over (A : CSA k) (I : RingCon A):
    Module k I := Module.compHom I (algebraMap k A)

lemma one_tensor_bot_RingCon [FiniteDimensional k K] {x : A} (_ : IsCentralSimple K (K ⊗[k] A))
  (h : 1 ⊗ₜ[k] x ∈ (⊥ : RingCon (K ⊗[k] A))) :
    x ∈ (⊥ : RingCon A) := by
  let h1 : k ⊗[k] A ≃ₐ[k] A := Algebra.TensorProduct.lid _ _
  let h2 : k →ₗ[k] K := {
    toFun := algebraMap k K
    map_add' := by simp only [map_add, implies_true]
    map_smul' := by intro x y; simp only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
  }
  have h4 : Function.Injective (LinearMap.rTensor A h2) := by
    apply Module.Flat.rTensor_preserves_injective_linearMap
    simp only [LinearMap.coe_mk, AddHom.coe_mk, h2]
    exact Basis.algebraMap_injective (FiniteDimensional.finBasis k K)
  suffices x = 0 by tauto
  suffices (1 : k) ⊗ₜ[k] x = 0 by
    obtain h := map_zero h1
    rw [← this, Algebra.TensorProduct.lid_tmul, Algebra.smul_def] at h
    simp_all
  suffices (algebraMap k K) 1 ⊗ₜ[k] x = 0 by
    have h : (LinearMap.rTensor A h2) (1 ⊗ₜ[k] x) = (algebraMap k K) 1 ⊗ₜ[k] x := by tauto
    rw [this, show 0 = (LinearMap.rTensor A h2) 0 by simp ] at h
    tauto
  simp; tauto

lemma RingCon_Injective_top [FiniteDimensional k K] {I : RingCon A}
    (Is_CSA : IsCentralSimple K (K ⊗[k] A))
    (h : (RingCon.span {x| ∃(a : K), ∃ i ∈ I, x = a ⊗ₜ i} : RingCon (K ⊗[k] A)) = ⊤) :
    I = ⊤ := by
  let f : RingCon A → RingCon (K ⊗[k] A) :=
    fun I => RingCon.span {x| ∃(a : K), ∃ i ∈ I, x = a ⊗ₜ i}
  let g : RingCon (K ⊗[k] A) → RingCon A :=
    fun J => RingCon.span {x| 1 ⊗ₜ x ∈ J}
  have hf : Function.Injective f := by
    apply Function.LeftInverse.injective (g := g)
    intro J
    apply LE.le.antisymm'
    · simp [f, g]
      rw [le_iff]
      intro a ha
      simp only [SetLike.mem_coe]
      suffices a ∈ {x | (1 : K) ⊗ₜ[k] x ∈ span {x | ∃ a, ∃ i ∈ J, x = a ⊗ₜ[k] i}} by
        have := subset_span {x | (1 : K) ⊗ₜ[k] x ∈ span {x | ∃ a, ∃ i ∈ J, x = a ⊗ₜ[k] i}}
        apply this
        tauto
      simp only [Set.mem_setOf_eq]
      suffices (1 : K) ⊗ₜ[k] a ∈ {x | ∃ a, ∃ i ∈ J, x = a ⊗ₜ[k] i} by
        have := subset_span {x | ∃ a : K, ∃ i ∈ J, x = a ⊗ₜ[k] i}
        apply this
        tauto
      simp only [Set.mem_setOf_eq]
      tauto
    · simp only [g, f]
      rw [← span_le]
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [SetLike.mem_coe]
      -- rw [le_iff]
      -- intro a ha
      -- obtain ⟨ι, m, xA, yA, hι, ha'⟩ := RingCon.mem_span_iff_exists_fin
      --   {x | (1 : K) ⊗ₜ[k] x ∈ span {x | ∃ a, ∃ i ∈ J, x = a ⊗ₜ[k] i}} a|>.1 ha
      sorry
  suffices f ⊤ = ⊤ by rw [← this] at h; tauto
  rw [← top_le_iff, le_iff]
  intro x _
  simp only [SetLike.mem_coe, f]
  induction x using TensorProduct.induction_on with
  | zero =>
    exact RingCon.zero_mem _
  | tmul b c =>
    suffices b ⊗ₜ[k] c ∈ ({x | ∃ a, ∃ i ∈ (⊤ : RingCon A), x = a ⊗ₜ[k] i} : Set (K ⊗[k] A)) by
      have := subset_span ({x | ∃ a, ∃ i ∈ (⊤ : RingCon A), x = a ⊗ₜ[k] i} : Set (K ⊗[k] A))
      apply this; tauto
    use b; use c; tauto
  | add b c hb hc =>
    simp only [SetLike.mem_coe] at hb hc
    exact add_mem _ (hb (show b ∈ ⊤ by tauto)) (hc (show c ∈ ⊤ by tauto))

theorem is_simple_A [FiniteDimensional k K] (hAt : IsCentralSimple K (K ⊗[k] A)):
    IsSimpleOrder (RingCon A) := {
  exists_pair_ne := ⟨⊥, ⊤, by
    suffices Nontrivial (RingCon A) by simp only [ne_eq, bot_ne_top, not_false_eq_true]
    have : Nontrivial A := by
      by_contra! h
      have h0 : (⊥ : RingCon (K ⊗[k] A)) ≠ ⊤ := by
        rcases hAt.is_simple.exists_pair_ne with ⟨x, ⟨y, hxy⟩⟩
        obtain h := hAt.is_simple.eq_bot_or_eq_top y
        rcases hAt.is_simple.eq_bot_or_eq_top x with (x1 | x2) <;> aesop
      suffices (⊥ : RingCon (K ⊗[k] A)) = ⊤ by exact h0 this
      rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at h
      suffices (⊥ : RingCon (K ⊗[k] A)) = (⊤ : Set (K ⊗[k] A)) by
        rw [eq_top_iff, le_iff, this]
        simp only [Set.top_eq_univ, Set.subset_univ]
      apply Set.eq_of_subset_of_subset (by simp)
      intro x hx
      suffices x = 0 by tauto
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul b c => rw [← h 0 c, TensorProduct.tmul_zero]
      | add b c hb hc =>
        simp only [Set.top_eq_univ, Set.mem_univ, true_implies] at hb hc hx
        rw [hb, hc, add_zero]
    exact RingCon.instNontrivial ⟩
  eq_bot_or_eq_top := fun I => by
    by_contra! hI
    let tensor_is_ideal : RingCon (K ⊗[k] A) :=
      RingCon.span {x| ∃(a : K)(i : I), x = a ⊗ₜ i.1}
    have ne_bot : tensor_is_ideal ≠ ⊥ := by
      by_contra! h
      suffices I = ({0} : Set A) by
        apply hI.1
        rw [← le_bot_iff, le_iff]
        simp only [this, Set.singleton_subset_iff, SetLike.mem_coe]
        tauto
      apply Set.eq_of_subset_of_subset
      · intro x hx
        simp only [SetLike.mem_coe] at hx
        have : 1 ⊗ₜ x ∈ (tensor_is_ideal : Set (K ⊗[k] A)) := by
          simp only [Subtype.exists, exists_prop, SetLike.mem_coe, tensor_is_ideal]
          suffices 1 ⊗ₜ x ∈ {x| ∃ (a : K) , ∃ b ∈ I, x = a ⊗ₜ[k] b} by tauto
          use 1; use x
        simp only [SetLike.mem_coe, Set.mem_singleton_iff, h] at this ⊢
        suffices x ∈ (⊥ : RingCon A) by tauto
        exact one_tensor_bot_RingCon _ _ _ hAt this
      · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
        exact RingCon.zero_mem I
    have ne_top : tensor_is_ideal ≠ ⊤ := by
      by_contra! h
      apply hI.2
      simp [tensor_is_ideal] at h
      exact RingCon_Injective_top k A K hAt h
    haveI := hAt.is_simple.2 tensor_is_ideal
    tauto}

lemma one_tensor_bot_Algebra [FiniteDimensional k K] {x : A} (Is_CSA : IsCentralSimple K (K ⊗[k] A))
    (sim : IsSimpleOrder (RingCon A))
    (h : 1 ⊗ₜ[k] x ∈ (⊥ : Subalgebra K (K ⊗[k] A))) : x ∈ (⊥ : Subalgebra k A) := by
  --rw [Algebra.mem_bot] at h ⊢
  --simp only [Set.mem_range, Algebra.id.map_eq_id, RingHom.id_apply] at h ⊢
  -- obtain ⟨y, hy⟩ := h
  -- rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
  --   TensorProduct.smul_tmul'] at hy
  -- simp_rw [Algebra.algebraMap_eq_smul_one]
  -- sorry
  have h' : 1 ⊗ₜ[k] x ∈ Subalgebra.center K (K ⊗[k] A) := by
    simp only [IsCentralSimple.center_eq K (K ⊗[k] A), h]
  simp only [Subalgebra.mem_center_iff] at h'
  have h'' := fun a ↦ h' (1 ⊗ₜ[k] a)
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h''
  have hx : ∀(a : A), a * x = x * a := fun a ↦ by
    have inj: Function.Injective
      (Algebra.TensorProduct.includeRight (R := k) (B := A) (A := K)) := by
      have H := RingCon.IsSimpleOrder.iff_eq_zero_or_injective A|>.1 sim
      specialize @H (K ⊗[k]A) _ (Algebra.TensorProduct.includeRight (R := k) (B := A) (A := K))
      refine H.resolve_left fun rid => ?_
      rw [eq_top_iff, RingCon.le_iff] at rid
      specialize @rid 1 ⟨⟩
      simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, RingCon.mem_ker, _root_.map_one,
        one_ne_zero] at rid
    exact inj (h'' a)
  rw [← Subalgebra.mem_center_iff (R := k)] at hx
  sorry

theorem centralsimple_over_extension_iff [FiniteDimensional k K]:
    IsCentralSimple k A ↔ IsCentralSimple K (K ⊗[k] A) where
  mp := fun hA ↦ IsCentralSimple.baseChange k A K
  mpr := fun hAt ↦ {
    is_central := by
      obtain h := hAt.is_central
      intro x hx
      rw [Subalgebra.mem_center_iff] at hx
      have h1 : ((1 : K) ⊗ₜ[k] x) ∈ Subalgebra.center K (K ⊗[k] A) := by
        rw [Subalgebra.mem_center_iff]
        intro b
        induction b using TensorProduct.induction_on with
        | zero => simp only [zero_mul, mul_zero]
        | tmul b c =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
            one_mul, hx c]
        | add b c hb hc => rw [add_mul, mul_add]; simp only [hb, hc]
      exact one_tensor_bot_Algebra _ _ _ hAt (is_simple_A k A K hAt) (h h1)
    is_simple := is_simple_A k A K hAt}

def extension_CSA (A : CSA k) [FiniteDimensional k K]: CSA K where
  carrier := K ⊗[k] A
  is_central_simple := centralsimple_over_extension_iff k A K|>.1 A.is_central_simple
  fin_dim := Module.Finite.base_change k K A.carrier

def extension_inv (hT : IsCentralSimple K (K ⊗[k] A)) [FiniteDimensional K (K ⊗[k] A)]
    [FiniteDimensional k K]: CSA k where
  carrier := A
  is_central_simple := centralsimple_over_extension_iff k A K|>.2 hT
  fin_dim := by
    have := centralsimple_over_extension_iff k A K|>.2 hT
    let to_ten: A →ₐ[k] K ⊗[k] A :=
    {
      toFun := fun a ↦ 1 ⊗ₜ a
      map_one' := rfl
      map_mul' := by simp
      map_zero' := TensorProduct.tmul_zero A 1
      map_add' := TensorProduct.tmul_add 1
      commutes' := fun _ ↦ Algebra.TensorProduct.algebraMap_apply' _|>.symm
    }
    have Isinj : Function.Injective to_ten := by
      haveI := this.is_simple
      haveI : Nontrivial A := inferInstance
      exact RingCon.IsSimpleOrder.iff_eq_zero_or_injective A|>.1 inferInstance
        to_ten.toRingHom|>.resolve_left (by
        intro h
        rw [SetLike.ext_iff] at h
        specialize h 1
        simp only [RingCon.mem_ker, map_one, one_ne_zero, false_iff] at h
        exact h ⟨⟩)
    haveI : FiniteDimensional k (K ⊗[k] A) := Module.Finite.trans (R := k) K (K ⊗[k] A)
    exact FiniteDimensional.of_injective (K := k) to_ten.toLinearMap Isinj

theorem CSA_iff_exist_split [hA : FiniteDimensional k A]:
    IsCentralSimple k A ↔ (∃(n : ℕ)(_ : n ≠ 0)(L : Type u)(_ : Field L)(_ : Algebra k L)
    (_ : FiniteDimensional k L), Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)) := by
  constructor
  · intro hA
    haveI := hk_bar.1
    obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    refine ⟨n, hn, ?_⟩
    have := @lemma_tto.isoRestrict n ({out := hn}) k k_bar A _ _ _ _ _ _ _ iso
    use lemma_tto.ℒℒ n k k_bar A iso
    refine ⟨_, _, inferInstance, ⟨this⟩⟩
  · rintro ⟨n, hn, L, _, _, _, ⟨iso⟩⟩
    haveI : Nonempty (Fin n) := ⟨0, by omega⟩
    exact (centralsimple_over_extension_iff k A L).mpr $ AlgEquiv.isCentralSimple iso.symm

lemma dim_is_sq (h : IsCentralSimple k A) [FiniteDimensional k A]:
    IsSquare (FiniteDimensional.finrank k A) := by
  haveI := hk_bar.1
  obtain ⟨n, _, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
  refine ⟨n, ?_⟩
  have := FiniteDimensional.finrank_matrix k_bar (Fin n) (Fin n)
  simp only [Fintype.card_fin] at this
  exact dim_eq k k_bar A|>.trans $ LinearEquiv.finrank_eq iso.toLinearEquiv|>.trans this

def deg (A : CSA k): ℕ := dim_is_sq k A k_bar A.is_central_simple|>.choose

lemma deg_sq_eq_dim (A : CSA k): (deg k k_bar A) ^ 2 = FiniteDimensional.finrank k A :=
  by rw [pow_two]; exact dim_is_sq k A k_bar A.is_central_simple|>.choose_spec.symm

lemma deg_pos (A : CSA k): deg k k_bar A ≠ 0 := by
  by_contra! h
  apply_fun (λ x => x^2) at h
  rw [deg_sq_eq_dim k k_bar A, pow_two, mul_zero] at h
  haveI := A.is_central_simple.is_simple.1
  have Nontriv : Nontrivial A := inferInstance
  have := FiniteDimensional.finrank_pos_iff (R := k) (M := A)|>.2 Nontriv
  linarith

structure split (A : CSA k) (K : Type*) [Field K] [Algebra k K] :=
  (n : ℕ) (hn : n ≠ 0)
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

def isSplit (L : Type u) [Field L] [Algebra k L]: Prop :=
  ∃(n : ℕ)(_ : n ≠ 0),
  Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

def split_by_alg_closure (A : CSA k): split k A k_bar where
  n := deg k k_bar A
  hn := by haveI := deg_pos k k_bar A; omega
  iso := by
    haveI := hk_bar.1
    choose n _ iso using simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    have iso' := iso.some ; clear iso
    have e : Matrix (Fin n) (Fin n) k_bar ≃ₐ[k_bar] Matrix (Fin (deg k k_bar A))
      (Fin (deg k k_bar A)) k_bar := by
      suffices n = deg k k_bar A from Matrix.reindexAlgEquiv k_bar (finCongr this)
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e1 := LinearEquiv.finrank_eq iso'.toLinearEquiv|>.trans $
        FiniteDimensional.finrank_matrix k_bar (Fin n) (Fin n)
      simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self, one_mul,
        Fintype.card_fin] at e1
      have := this.trans e1
      exact Nat.mul_self_inj.mp (id this.symm)
    exact iso'.trans e

def extension_over_split (A : CSA k) (L L': Type u) [Field L] [Field L'] [Algebra k L]
    (hA : split k A L) [Algebra L L'] [Algebra k L'] [IsScalarTower k L L'] : split k A L' where
  n := deg k k_bar A
  hn := by haveI := deg_pos k k_bar A; omega
  iso := by
    obtain ⟨n, _, iso⟩ := hA
    let e1 : L' ⊗[k] A ≃ₐ[L] L' ⊗[L] L ⊗[k] A := {
      __ := absorb_eqv k L L' A
      commutes' := fun _ => rfl
    }
    let e2 := e1.trans $ Algebra.TensorProduct.congr (AlgEquiv.refl) iso
    let e3 : L' ⊗[k] A ≃ₐ[L'] L' ⊗[L] Matrix (Fin n) (Fin n) L := {
      __ := e2
      commutes' := fun l' => by
        simp only [AlgEquiv.toEquiv_eq_coe, Algebra.TensorProduct.algebraMap_apply,
          Algebra.id.map_eq_id, RingHom.id_apply, Equiv.toFun_as_coe, EquivLike.coe_coe]
        simp only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
          AlgEquiv.refl_toAlgHom, e2, e1]
        erw [absorb_eqv_apply, Algebra.TensorProduct.map_tmul]
        simp only [AlgHom.coe_id, id_eq, Algebra.TensorProduct.one_def.symm, map_one]
    }
    let e4 : L' ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[L'] Matrix (Fin n) (Fin n) L' := {
      __ := matrixEquivTensor _ _ _|>.symm
      commutes' := fun l' ↦ by
        simp only [AlgEquiv.toEquiv_eq_coe, Algebra.TensorProduct.algebraMap_apply,
          Algebra.id.map_eq_id, RingHom.id_apply, Equiv.toFun_as_coe, EquivLike.coe_coe,
          matrixEquivTensor_apply_symm, Matrix.map]
        ext i j
        simp only [Matrix.of_apply]
        if hij : i = j then
        subst hij
        simp only [Matrix.one_apply_eq, map_one, mul_one, Algebra.algebraMap_eq_smul_one,
          Matrix.smul_apply, smul_eq_mul, mul_one]
        else
        simp only [ne_eq, hij, not_false_eq_true, Matrix.one_apply_ne, map_zero, mul_zero,
          Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, smul_eq_mul, zero_mul]
    }
    let e5 : n = deg k k_bar A := by
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e6 := LinearEquiv.finrank_eq (e3.trans e4).toLinearEquiv|>.trans $
        FiniteDimensional.finrank_matrix L' (Fin n) (Fin n)
      simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self, one_mul,
        Fintype.card_fin] at e6
      exact Nat.mul_self_inj.mp (id (this.trans e6).symm)
    exact (e3.trans e4).trans $ Matrix.reindexAlgEquiv L' (finCongr e5)

variable [FiniteDimensional k A]

def Basis_of_k : Basis (Fin (FiniteDimensional.finrank k A)) k_bar (k_bar ⊗[k] A):=
  Algebra.TensorProduct.basis k_bar (FiniteDimensional.finBasis k A)

theorem Basis_apply (i : Fin (FiniteDimensional.finrank k A)) :
    Basis_of_k k A k_bar i = 1 ⊗ₜ (FiniteDimensional.finBasis k A i) :=
  Algebra.TensorProduct.basis_apply (FiniteDimensional.finBasis k A) i

example (x : k_bar ⊗[k] A) : 1 = 2 := by
  have := Basis.mem_span (Basis_of_k k A k_bar) x

  sorry
theorem sepclosure_split (A : CSA k):
    isSplit k A k_s := by
  obtain ⟨n, hn, D, _, _, ⟨iso⟩⟩ := Wedderburn_Artin_algebra_version k_s (k_s ⊗[k] A)
  refine ⟨deg k k_bar A, deg_pos k k_bar A, ⟨?_⟩⟩
  haveI := is_fin_dim_of_wdb k_s (k_s ⊗[k] A) n D (by omega) iso
  set d : ℕ := FiniteDimensional.finrank k_s D with d_eq
  if hd' : d = 1 then
    haveI : Nontrivial D := GroupWithZero.toNontrivial
    haveI := FiniteDimensional.finrank_pos_iff (R := k_s) (M := D)|>.2 this
    have k_s_sim: IsSimpleOrder (RingCon k_s) := instIsSimpleOrderRingCon_brauerGroup k_s
    have inj : Function.Injective (Algebra.ofId k_s D) := by
      have H := RingCon.IsSimpleOrder.iff_eq_zero_or_injective k_s|>.1 k_s_sim
      specialize @H D _ (Algebra.ofId k_s D)
      refine H.resolve_left fun rid => ?_
      rw [eq_top_iff, RingCon.le_iff] at rid
      specialize @rid 1 ⟨⟩
      simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, RingCon.mem_ker, _root_.map_one,
        one_ne_zero] at rid
    have e : k_s ≃ₐ[k_s] D :=
      AlgEquiv.ofBijective (Algebra.ofId k_s D) ⟨inj, by
        change Function.Surjective (Algebra.ofId k_s D).toLinearMap
        rw [← LinearMap.range_eq_top]
        have eq := (Algebra.ofId k_s D).toLinearMap.finrank_range_add_finrank_ker
        rw [FiniteDimensional.finrank_self, LinearMap.ker_eq_bot.2 inj, finrank_bot, add_zero] at eq
        apply Submodule.eq_top_of_finrank_eq
        rw [eq, ← d_eq, hd']⟩
    have e1 := iso.trans $ e.mapMatrix (m := Fin n)|>.symm
    have e2 : n = deg k k_bar A := by
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e3 := LinearEquiv.finrank_eq e1.toLinearEquiv|>.trans $
        FiniteDimensional.finrank_matrix k_s (Fin n) (Fin n)
      simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self, one_mul,
        Fintype.card_fin] at e3
      exact Nat.mul_self_inj.mp (id (this.trans e3).symm)
    exact e1.trans $ Matrix.reindexAlgEquiv k_s $ finCongr e2
  else
  have hd : 1 < d := by
    suffices d ≠ 0 by omega
    by_contra! h
    obtain d_eq := d_eq.symm
    rw [h, FiniteDimensional.finrank_zero_iff (R := k_s) (M := D),
      ← not_nontrivial_iff_subsingleton] at d_eq
    tauto
  -- suffices Matrix (Fin n) (Fin n) D ≃ₐ[k_s] Matrix (Fin (deg k k_bar A)) (Fin (deg k k_bar A)) k_s by
  --   exact ((id this.symm).trans (id iso.symm)).symm
  -- have e1 := deg_sq_eq_dim k k_bar A
  -- have e2 := matrixEquivTensor (A := D) (R := k_s) (n := Fin n)
  -- have e3 := LinearEquiv.finrank_eq e2.toLinearEquiv
  -- have e4 := LinearEquiv.finrank_eq iso.toLinearEquiv
  -- rw [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_matrix k_s (Fin n) (Fin n),
  --   ← e4, FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self, one_mul,
  --   Fintype.card_fin, ← e1] at e3; clear e4 e1
  sorry

theorem finite_sep_split (A : CSA k): ∃(L : Type u)(_ : Field L)(_ : Algebra k L)
    (fin_dim : FiniteDimensional k L)(_ : Algebra.IsSeparable k L), isSplit k A L := sorry
