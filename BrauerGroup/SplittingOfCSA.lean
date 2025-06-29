import BrauerGroup.BrauerGroup
import BrauerGroup.AlgClosedUnion
import BrauerGroup.ExtendScalar
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import BrauerGroup.LemmasAboutSimpleRing

suppress_compilation

universe u v w
variable (k A K : Type u) [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

variable (k_bar : Type u) [Field k_bar] [Algebra k k_bar]
  [hk_bar : IsAlgClosure k k_bar] (k_s : Type u) [Field k_s] [Algebra k k_s]

open scoped TensorProduct
open RingCon

instance module_over_over (A : CSA k) (I : TwoSidedIdeal A) :
    Module k I := Module.compHom I (algebraMap k A)

set_option synthInstance.maxHeartbeats 50000 in
theorem is_simple_A [IsSimpleRing (K ⊗[k] A)] :
    IsSimpleRing A := IsSimpleRing.right_of_tensor k K A

theorem central_over_extension_iff_subsingleton
    [Subsingleton A] [FiniteDimensional k A] [FiniteDimensional k K] :
    Algebra.IsCentral k A ↔ Algebra.IsCentral K (K ⊗[k] A) := by
  have : Subsingleton (K ⊗[k] A) := by
    rw [← subsingleton_iff_zero_eq_one, show (0 : K ⊗[k] A) = 0 ⊗ₜ 0 by simp,
        show (1 : K ⊗[k] A) = 1 ⊗ₜ 1 by rfl, show (1 : A) = 0 from Subsingleton.elim _ _]
    simp
  constructor <;>
  · intro h
    refine ⟨fun x hx => ?_⟩
    rw [show x = 0 from Subsingleton.elim _ _]
    exact Subalgebra.zero_mem ⊥

theorem isSimple_over_extension_iff_subsingleton
    [Subsingleton A] [FiniteDimensional k A] [FiniteDimensional k K] :
    IsSimpleRing A ↔ IsSimpleRing (K ⊗[k] A) := by
  have : Subsingleton (K ⊗[k] A) := by
    rw [← subsingleton_iff_zero_eq_one, show (0 : K ⊗[k] A) = 0 ⊗ₜ 0 by simp,
        show (1 : K ⊗[k] A) = 1 ⊗ₜ 1 by rfl, show (1 : A) = 0 from Subsingleton.elim _ _]
    simp
  constructor <;>
  · intro h
    have : Nontrivial (K ⊗[k] A) := inferInstance
    rw [← not_subsingleton_iff_nontrivial] at this
    contradiction

set_option synthInstance.maxHeartbeats 60000 in
set_option maxHeartbeats 400000 in
theorem centralSimple_over_extension_iff_nontrivial
    [Nontrivial A] [FiniteDimensional k A] [FiniteDimensional k K] :
    (Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
    (Algebra.IsCentral K (K ⊗[k] A) ∧ IsSimpleRing (K ⊗[k] A)) where
  mp := fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩
  mpr := fun ⟨hAt, _⟩ ↦ ⟨by
    constructor
    by_contra h
    simp only [le_bot_iff, ne_eq] at h
    have : 1 < Module.finrank k (Subalgebra.center k A) := by
      have eq1 := Subalgebra.finrank_bot (F := k) (E := A)
      have ineq1 := Submodule.finrank_lt_finrank_of_lt
        (s := Subalgebra.toSubmodule (⊥ : Subalgebra k A))
        (t := Subalgebra.toSubmodule (Subalgebra.center k A)) (by
        simp only [OrderEmbedding.lt_iff_lt]
        rw [bot_lt_iff_ne_bot]
        exact h)
      erw [eq1] at ineq1
      exact ineq1
    let e : K ⊗[k] Subalgebra.center k A ≃ₗ[k] Subalgebra.center k (K ⊗[k] A) :=
      (TensorProduct.congr (Submodule.topEquiv.symm ≪≫ₗ
        show _ ≃ₗ[k] Subalgebra.toSubmodule (Subalgebra.center k K) from LinearEquiv.ofLinear
        (Submodule.inclusion (by simp)) (Submodule.inclusion (by simp)) rfl rfl)
        (LinearEquiv.refl _ _)) ≪≫ₗ
      (IsCentralSimple.centerTensor k K A)
    have eq1 : Module.finrank k (Subalgebra.center k (K ⊗[k] A)) =
              Module.finrank k K *
              Module.finrank k (Subalgebra.center k A) := by
      rw [LinearEquiv.finrank_eq e.symm, Module.finrank_tensorProduct]
    have eq2 : Module.finrank k (Subalgebra.center K (K ⊗[k] A)) =
              Module.finrank k K *
              Module.finrank k (Subalgebra.center k A) := by
      rw [← eq1]; congr
    have eq3 : Module.finrank k (Subalgebra.center K (K ⊗[k] A)) =
              Module.finrank k K *
              Module.finrank K (Subalgebra.center K (K ⊗[k] A)) := by
      rw [Module.finrank_mul_finrank]

    have eq4 : Module.finrank K (Subalgebra.center K (K ⊗[k] A)) = 1 := by
      rw [← Subalgebra.finrank_bot (F := K) (E := K ⊗[k] A)]
      have := hAt.center_eq_bot
      rw [this.symm]

    rw [eq4, mul_one] at eq3
    rw [eq3] at eq2
    have ineq0 : 0 < Module.finrank k K := Module.finrank_pos
    have ineq1 :
      Module.finrank k K <
      Module.finrank k K * Module.finrank k (Subalgebra.center k A) := by
      apply lt_mul_right <;> assumption
    conv_lhs at ineq1 => rw [eq2]
    exact Nat.lt_irrefl _ ineq1, is_simple_A k A K⟩

theorem centralsimple_over_extension_iff
    [FiniteDimensional k A] [FiniteDimensional k K] :
    (Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
    (Algebra.IsCentral K (K ⊗[k] A) ∧ IsSimpleRing (K ⊗[k] A)) := by
  obtain h|h := subsingleton_or_nontrivial A
  · refine ⟨fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩⟩
    · rwa [← central_over_extension_iff_subsingleton]
    · rwa [← isSimple_over_extension_iff_subsingleton]
    · rwa [central_over_extension_iff_subsingleton k A K]
    · rwa [isSimple_over_extension_iff_subsingleton k A K]
  · apply centralSimple_over_extension_iff_nontrivial

def extension_CSA (A : CSA k) [FiniteDimensional k K] : CSA K := {
  __ := AlgebraCat.of K (K ⊗[k] A)
  fin_dim := Module.Finite.base_change k K A.carrier }

def extension_inv [FiniteDimensional k A]
    [Algebra.IsCentral K (K ⊗[k] A)] [IsSimpleRing (K ⊗[k] A)]
    [FiniteDimensional K (K ⊗[k] A)]
    [FiniteDimensional k K] : CSA k := {
  __ := AlgebraCat.of k A
  isCentral := centralsimple_over_extension_iff k A K |>.2 ⟨inferInstance, inferInstance⟩ |>.1
  isSimple := centralsimple_over_extension_iff k A K |>.2 ⟨inferInstance, inferInstance⟩ |>.2
  fin_dim := by
    have := centralsimple_over_extension_iff k A K |>.2 ⟨inferInstance, inferInstance⟩ |>.2
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
      have := IsSimpleRing.iff_eq_zero_or_injective' A k|>.1 inferInstance (B := K ⊗[k] A) to_ten
      have nezero : TwoSidedIdeal.ker to_ten ≠ ⊤ := by
        intro h
        have : (1 : A) ∈ (⊤ : TwoSidedIdeal A) := by simp
        rw [h.symm, TwoSidedIdeal.mem_ker] at this
        simp only [map_one, one_ne_zero] at this
      simp only [nezero, false_or] at this
      exact this
    haveI : FiniteDimensional k (K ⊗[k] A) := Module.Finite.trans (R := k) K (K ⊗[k] A)
    exact FiniteDimensional.of_injective (K := k) to_ten.toLinearMap Isinj }

theorem CSA_iff_exist_split (k_bar : Type u) [Field k_bar] [Algebra k k_bar]
    [hk_bar : IsAlgClosure k k_bar] [hA : FiniteDimensional k A] :
    (Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
      (∃ (n : ℕ) (_ : NeZero n) (L : Type u) (_ : Field L) (_ : Algebra k L)
        (_ : FiniteDimensional k L), Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)) := by
  constructor
  · rintro ⟨_, _⟩
    haveI := hk_bar.1
    obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    refine ⟨n, hn, ?_⟩
    use lemma_tto.ℒℒ n k k_bar A iso
    refine ⟨_, _, inferInstance, ⟨lemma_tto.isoRestrict n k k_bar A iso⟩⟩
  · rintro ⟨n, hn, L, _, _, _, ⟨iso⟩⟩
    refine (centralsimple_over_extension_iff k A L).mpr <| ⟨iso.symm.isCentral, ⟨?_⟩⟩
    rw [← TwoSidedIdeal.orderIsoOfRingEquiv iso.symm.toRingEquiv |>.isSimpleOrder_iff]
    exact IsSimpleRing.simple

lemma dim_is_sq (k_bar : Type u) [Field k_bar] [Algebra k k_bar] [hk_bar : IsAlgClosure k k_bar]
    [Algebra.IsCentral k A] [IsSimpleRing A] [FiniteDimensional k A] :
    IsSquare (Module.finrank k A) := by
  haveI := hk_bar.1
  obtain ⟨n, _, ⟨iso⟩⟩ := simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
  refine ⟨n, ?_⟩
  have := Module.finrank_matrix k_bar k_bar (Fin n) (Fin n)
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at this
  exact dim_eq k k_bar A|>.trans $ LinearEquiv.finrank_eq iso.toLinearEquiv|>.trans this

def deg (A : CSA k) : ℕ := dim_is_sq k A k_bar |>.choose

lemma deg_sq_eq_dim (A : CSA k) : (deg k k_bar A) ^ 2 = Module.finrank k A :=
  by rw [pow_two]; exact dim_is_sq k A k_bar |>.choose_spec.symm

instance deg_pos (A : CSA k) : NeZero (deg k k_bar A) := by
  constructor
  by_contra! h
  apply_fun (λ x => x^2) at h
  rw [deg_sq_eq_dim k k_bar A, pow_two, mul_zero] at h
  have := Module.finrank_pos_iff (R := k) (M := A)|>.2 inferInstance
  linarith

structure split (A : CSA k) (K : Type*) [Field K] [Algebra k K] where
  (n : ℕ) [hn : NeZero n]
  (iso : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

def isSplit (L : Type u) [Field L] [Algebra k L] : Prop :=
  ∃ (n : ℕ) (_ : NeZero n),
  Nonempty (L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

def split_by_alg_closure (A : CSA k) : split k A k_bar where
  n := deg k k_bar A
  iso := by
    haveI := hk_bar.1
    choose n _ iso using simple_eq_matrix_algClosed k_bar (k_bar ⊗[k] A)
    have iso' := iso.some; clear iso
    have e : Matrix (Fin n) (Fin n) k_bar ≃ₐ[k_bar] Matrix (Fin (deg k k_bar A))
      (Fin (deg k k_bar A)) k_bar := by
      suffices n = deg k k_bar A from Matrix.reindexAlgEquiv k_bar _ (finCongr this)
      have := deg_sq_eq_dim k k_bar A
      rw [pow_two] at this
      have e1 := LinearEquiv.finrank_eq iso'.toLinearEquiv|>.trans $
        Module.finrank_matrix k_bar _ (Fin n) (Fin n)
      simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul, Fintype.card_fin,
        mul_one] at e1
      have := this.trans e1
      exact Nat.mul_self_inj.mp (id this.symm)
    exact iso'.trans e

def extension_over_split (A : CSA k) (L L': Type u) [Field L] [Field L'] [Algebra k L]
    (hA : split k A L) [Algebra L L'] [Algebra k L'] [IsScalarTower k L L'] : split k A L' where
  n := deg k k_bar A
  iso := by
    obtain ⟨n, iso⟩ := hA
    let e1 : L' ⊗[k] A ≃ₐ[L] L' ⊗[L] L ⊗[k] A := {
      __ := absorb_eqv k L L' A
      commutes' _ := rfl
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
        Module.finrank_matrix L' _ (Fin n) (Fin n)
      simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul, Fintype.card_fin,
        mul_one] at e6
      exact Nat.mul_self_inj.mp (id (this.trans e6).symm)
    exact (e3.trans e4).trans $ Matrix.reindexAlgEquiv L' _ (finCongr e5)
