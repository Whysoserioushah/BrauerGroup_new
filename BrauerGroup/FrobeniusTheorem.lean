import BrauerGroup.Subfield.Subfield
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Complex.FiniteDimensional

suppress_compilation

open TensorProduct Classical FiniteDimensional

variable {D : Type} [DivisionRing D]

section prerequisites

set_option synthInstance.maxHeartbeats 80000 in
theorem rank_1_D_iso_R [Algebra ℝ D] : Module.finrank ℝ D = 1 →
    Nonempty (D ≃ₐ[ℝ] ℝ) := fun h ↦ by
  have h' := Subalgebra.finrank_eq_one_iff (F := ℝ) (S := (⊤ : Subalgebra ℝ D))
  have : Module.finrank ℝ (⊤ : Subalgebra ℝ D) = 1 := by
    simp_all only [Subalgebra.finrank_eq_one_iff, Subalgebra.bot_eq_top_of_finrank_eq_one]
  exact ⟨Subalgebra.topEquiv.symm.trans $ Subalgebra.equivOfEq _ _
    (h'.1 this)|>.trans $ Algebra.botEquiv ℝ D⟩

lemma RealExtension_is_RorC (K : Type) [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K] :
    Nonempty (K ≃ₐ[ℝ] ℝ) ∨ Nonempty (K ≃ₐ[ℝ] ℂ) := by
  let CC := AlgebraicClosure K
  letI : Algebra ℝ CC := AlgebraicClosure.instAlgebra K
  haveI : IsAlgClosure ℝ CC := ⟨inferInstance, Algebra.IsAlgebraic.trans ℝ K CC⟩
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  let e : ℂ ≃ₐ[ℝ] CC := IsAlgClosure.equiv ℝ _ _
  have dim_eq1 : Module.finrank ℝ CC = 2 := by
    rw [← Complex.finrank_real_complex, e.toLinearEquiv.finrank_eq]
  have dim_eq2 : Module.finrank ℝ K * Module.finrank K CC = 2 := by
    rw [Module.finrank_mul_finrank, dim_eq1]
  haveI : Module.Finite ℝ CC := by
    have := e.toLinearEquiv.finrank_eq
    simp only [Complex.finrank_real_complex] at this
    exact FiniteDimensional.of_finrank_eq_succ this.symm
  haveI : Module.Finite K CC := Module.Finite.right ℝ K CC
  have dim_eq3 : Module.finrank ℝ K = 1 ∨ Module.finrank ℝ K = 2 := by
    have ineq1 : 0 < Module.finrank ℝ K := Module.finrank_pos
    have ineq2 : 0 < Module.finrank K CC := Module.finrank_pos
    have : Module.finrank ℝ K ∈ Nat.divisors 2 := by
      simpa using ⟨Module.finrank K CC, dim_eq2.symm⟩
    rw [show Nat.divisors 2 = {1, 2} from rfl] at this
    simpa using this
  rcases dim_eq3 with ⟨h1⟩ | ⟨h2⟩
  · left
    exact Nonempty.intro <| AlgEquiv.symm <| AlgEquiv.ofBijective (Algebra.ofId _ _)
      (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by simp [h1])
  · right
    exact Nonempty.intro <| AlgEquiv.ofBijective
      (e.symm.toAlgHom.comp <| Algebra.ofId K CC |>.restrictScalars ℝ)
      (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by simp [h2])

end prerequisites

variable [Algebra ℝ D] [hD : Algebra.IsCentral ℝ D] [hD' : IsSimpleRing D]
  (k : SubField ℝ D) (hk : IsMaximalSubfield ℝ D k)
  (e : k ≃ₐ[ℝ] ℂ) [FiniteDimensional ℝ D]

open ComplexConjugate

set_option synthInstance.maxHeartbeats 50000 in
abbrev f : k →ₐ[ℝ] k where
  toFun := fun kk ↦ e.symm $ conj (e kk)
  map_one' := by simp only [map_one, OneMemClass.coe_one]
  map_mul' := by simp only [map_mul, MulMemClass.coe_mul, implies_true]
  map_zero' := by simp only [map_zero, ZeroMemClass.coe_zero]
  map_add' := fun x y ↦ by
    simp only [map_add, AddMemClass.coe_add]
  commutes' := fun r ↦ by
    simp only [AlgEquiv.commutes, Complex.coe_algebraMap, Complex.conj_ofReal]
    rw [← mul_one (algebraMap _ _ r), ← Algebra.smul_def]
    nth_rw 1 [← mul_one r]
    unfold Complex.ofReal
    rw [← smul_eq_mul, show (⟨r • 1, 0⟩ : ℂ) = r • ⟨1, 0⟩ by
      apply Complex.ext
      · simp only [smul_eq_mul, mul_one, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, mul_zero,
        Complex.ofReal_im, mul_one, add_zero]]
    rw [_root_.map_smul, show ⟨1, 0⟩ = (1 : ℂ) by rfl, _root_.map_one]

omit hD [FiniteDimensional ℝ D] in
lemma f_injective : Function.Injective (f k e) := by
  intro x y h
  simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    EmbeddingLike.apply_eq_iff_eq] at h
  have : Function.Injective $ starRingEnd ℂ := by exact RingHom.injective (starRingEnd ℂ)
  apply this at h
  apply e.injective
  exact h

omit hD [FiniteDimensional ℝ D] in
@[simp]
lemma f_apply (x : k) : f k e x = e.symm (conj (e x)) := rfl

omit hD [FiniteDimensional ℝ D] in
lemma f_apply_apply (z : ℂ) : f k e (e.symm z) = e.symm (conj z) := by
  rw [f_apply]
  congr
  exact AlgEquiv.apply_symm_apply e z

set_option maxHeartbeats 500000 in
lemma f_is_conjugation : ∃ (x : Dˣ), ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z := by
  obtain ⟨x, hx⟩ := SkolemNoether' ℝ D k k.val (k.val.comp (f k e))
  use x
  intro z
  have hx2 := hx
  specialize hx z
  apply_fun fun y ↦ ↑x⁻¹ * y * ↑x at hx
  nth_rw 2 [mul_assoc, mul_assoc] at hx
  simp only [Units.val_inv_eq_inv_val, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
    IsUnit.inv_mul_cancel, mul_one, IsUnit.inv_mul_cancel_left] at hx
  exact hx

omit hD in
lemma linindep_one_xsq (x : Dˣ)
    (hxx : ¬x.1 ^ 2 ∈ Subalgebra.center ℝ D) :
    LinearIndependent ℝ ![(1 : D), x.1^2] := by
  rw [LinearIndependent.pair_iff]
  by_contra! hh
  obtain ⟨s, t, ⟨hst1, hst2⟩⟩ := hh
  if hs : s = 0 then
    rw [hs, zero_smul, zero_add] at hst1
    simp only [smul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      Units.ne_zero, or_false] at hst1
    apply hst2 at hs
    exact hs hst1
  else
    if ht : t = 0 then
      rw [ht, zero_smul, add_zero, smul_eq_zero] at hst1
      simp only [one_ne_zero, or_false] at hst1
      exact hst2 hst1 ht
    else
      rw [add_eq_zero_iff_eq_neg, ← neg_smul] at hst1
      apply_fun ((-t)⁻¹ • ·) at hst1
      rw [← smul_assoc, ← smul_assoc, smul_eq_mul,
        smul_eq_mul, inv_mul_cancel₀ (by simp_all only [AlgHom.coe_comp, Subalgebra.coe_val,
          Function.comp_apply, Units.val_inv_eq_inv_val, Subtype.forall, Subtype.coe_eta,
          ne_eq, not_true_eq_false, false_implies, mul_neg, neg_smul, neg_eq_zero,
          not_false_eq_true]), one_smul] at hst1
      have : x.1^2 ∈ Subalgebra.center ℝ D := by
        rw [Subalgebra.mem_center_iff]
        intro d
        rw [← hst1]
        simp only [Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc, one_mul]
      exact hxx this

omit hD [FiniteDimensional ℝ D] in
lemma x2_comm_k (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z) :
    ∀ (y : k), x.1^2 * k.val y = k.val y * x.1^2 := by
  have hx2 := hx
  intro y
  specialize hx y
  simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
    Units.val_inv_eq_inv_val] at hx
  erw [Subtype.ext_iff.1 (f_apply k e y)] at hx
  apply_fun (x.1 * · * x.1⁻¹) at hx
  erw [← mul_assoc, ← mul_assoc] at hx
  have : k.val y = (x.1⁻¹ * x.1⁻¹) * k.val y * (x.1 * x.1) := by
    nth_rw 1 [← hx2 y, show ((f k e y) : D) = k.val (f k e y) from rfl,
      ← hx2, show (f k e (f k e y)) = y by simp, show (y : D) = k.val y from rfl]
    simp [← mul_assoc]
  apply_fun (x.1 * x.1 * · ) at this
  erw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_assoc x.1 x.1 x.1⁻¹,
    mul_inv_cancel₀ (by simp only [ne_eq, Units.ne_zero, not_false_eq_true]), mul_one,
    mul_inv_cancel₀ (by simp only [ne_eq, Units.ne_zero, not_false_eq_true]), one_mul,
    ← pow_two, mul_assoc, ← pow_two] at this
  exact this

lemma xsq_ink (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) : x.1^2 ∈ k := by
  have := cor_two_1to2 ℝ D k|>.2 (by simp [hDD, e.toLinearEquiv.finrank_eq])
  change x.1^2 ∈ k.1
  rw [← this, Subalgebra.mem_centralizer_iff]
  simp only [SubField.coe_toSubalgebra, SetLike.mem_coe]
  intro z hz
  have := (x2_comm_k _ _ _ hx ⟨z, hz⟩).symm
  simp only [Subalgebra.coe_val] at this
  exact this

set_option synthInstance.maxHeartbeats 40000 in
lemma indep' (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) (hxx : ¬x.1 ^ 2 ∈ Subalgebra.center ℝ D) :
    LinearIndependent ℝ (M := k) ![1, ⟨x.1^2, (xsq_ink _ _ _ hx hDD)⟩] := by
  have indep := linindep_one_xsq _ hxx
  rw [LinearIndependent.pair_iff] at *
  intro s t hst'
  specialize indep s t
  apply_fun k.val at hst'
  rw [_root_.map_add, map_smul, map_smul] at hst'
  simp only [Subalgebra.coe_val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at hst'
  exact indep hst'

abbrev IsBasis (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) (hxx : ¬x.1 ^ 2 ∈ Subalgebra.center ℝ D) :
    Basis (Fin (Nat.succ 0).succ) ℝ k :=
  .mk (M := k) (v := ![1, ⟨x.1^2, xsq_ink _ _ _ hx hDD⟩]) (indep' _ _ _ hx hDD hxx) $ by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.union_singleton, top_le_iff]
  have : Module.finrank ℝ (Submodule.span ℝ
    {⟨x.1^2, xsq_ink _ _ _ hx hDD⟩, (1 : k)})= 2 := by
    have indep' := indep' _ _ _ hx hDD hxx
    apply LinearIndependent.span_eq_top_of_card_eq_finrank' at indep'
    simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin,
      Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton] at indep'
    have : 2 = Module.finrank ℝ k := by
      rw [LinearEquiv.finrank_eq e.toLinearEquiv]
      symm
      exact Complex.finrank_real_complex
    apply indep' at this
    rw [this, finrank_top]
    exact (show Module.finrank ℝ k = 2 by
        rw [LinearEquiv.finrank_eq e.toLinearEquiv]
        exact Complex.finrank_real_complex
    )
  have eq := Submodule.topEquiv.finrank_eq.trans $
    e.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex
  have le : Submodule.span _ {⟨x.1 ^ 2, xsq_ink _ _ _ hx hDD⟩, (1 : k)} ≤
    (⊤ : Submodule ℝ k) := fun _ _ ↦ ⟨⟩
  exact Submodule.eq_of_le_of_finrank_eq le $ this.trans eq.symm

@[simp]
lemma IsBasis0 (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) (hxx : ¬x.1 ^ 2 ∈ Subalgebra.center ℝ D) :
    IsBasis _ _ _ hx hDD hxx 0 = 1 := by simp [IsBasis]

@[simp]
lemma IsBasis1 (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) (hxx : ¬x.1 ^ 2 ∈ Subalgebra.center ℝ D) :
    IsBasis _ _ _ hx hDD hxx 1 = ⟨x.1^2, xsq_ink _ _ _ hx hDD⟩ := by simp [IsBasis]

set_option synthInstance.maxHeartbeats 40000 in
lemma x2_is_real (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) : x.1^2 ∈ (algebraMap ℝ D).range := by
  let hx2 := hx
  have x2_is_central : x.1^2 ∈ Subalgebra.center ℝ D := by
      have x2_commutes_K := x2_comm_k _ _ _ hx
      by_contra! hxx
      have xink := xsq_ink _ _ _ hx hDD
      have indep' := indep' _ _ _ hx hDD hxx
      let IsBasis := IsBasis _ _ _ hx hDD hxx
      have x_commutes_k : ∀ (y : k), x.1 * k.val y = k.val y * x.1 := by
        intro y
        have := Basis.linearCombination_repr IsBasis y|>.symm
        rw [this, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Basis.mk_repr, Basis.coe_mk,
          Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [IsBasis0, IsBasis1]
        · erw [mul_add, add_mul]
          rw [Subalgebra.coe_smul, mul_smul_comm, smul_mul_assoc, Subalgebra.coe_one,
            one_mul, mul_one, add_right_inj, Subalgebra.coe_smul, mul_smul_comm,
            show ((⟨x.1^2, xink⟩ : k) : D) = x.1^2 by rfl, pow_two, ← mul_assoc, smul_mul_assoc]
        · exact fun _ ↦ Subtype.ext_iff.2 <| zero_smul _ _

      specialize x_commutes_k $ e.symm ⟨0,1⟩
      specialize hx $ e.symm ⟨0,1⟩
      -- apply_fun (x.1⁻¹ * ·) at x_commutes_k
      simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, Units.val_inv_eq_inv_val,
        isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel_right] at hx
      simp only [Subalgebra.coe_val, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_left] at x_commutes_k
      apply_fun (· * x.1⁻¹) at x_commutes_k
      simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.mul_inv_cancel_right] at x_commutes_k
      erw [← hx, f_apply] at x_commutes_k
      simp only [AlgEquiv.apply_symm_apply, Subalgebra.coe_val, SetLike.coe_eq_coe,
        EmbeddingLike.apply_eq_iff_eq] at x_commutes_k
      have : starRingEnd ℂ ⟨0, 1⟩ = ⟨0, -1⟩:= rfl
      simp only [this, mul_assoc, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.mul_inv_cancel, mul_one, IsUnit.mul_inv_cancel_left] at x_commutes_k
      unfold f at hx2
      specialize hx2 $ e.symm ⟨0,1⟩
      simp only [this, f_apply, AlgEquiv.apply_symm_apply, Subalgebra.coe_val] at hx2
      erw [← mul_assoc, hx2] at x_commutes_k
      simp only [SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq, Complex.mk.injEq, true_and] at x_commutes_k
      norm_num at x_commutes_k

  change _ ∈ (⊥ : Subalgebra ℝ D)
  rw [← Algebra.IsCentral.center_eq_bot ℝ D]
  exact x2_is_central

open scoped algebraMap in
abbrev V : Set D := {x | ∃ r : ℝ, r < 0 ∧ x^2 = (r : D)}

set_option linter.unusedSectionVars false in
lemma V_def (x : D) : x ∈ V ↔ ∃ r : ℝ, r < 0 ∧ x^2 = (algebraMap ℝ D) r := by
    exact Set.mem_def

lemma real_sq_in_R_or_V (x : D) : x^2 ∈ (algebraMap ℝ D).range → x ∈ (algebraMap ℝ D).range ∨ x ∈ V := by
  rintro ⟨r, hr⟩
  if h'' : x ∈ V then
    exact Or.inr h''
  else
    left
    simp only [V_def, not_exists, not_and] at h''
    have : r ≥ 0 := by
      specialize h'' r
      by_contra!
      exact h'' this (id (Eq.symm hr))
    have eq1 : (x - algebraMap ℝ D (Real.sqrt r)) * ( x + algebraMap ℝ D (Real.sqrt r)) = 0 := by
      simp only [mul_add, sub_mul]
      rw [← pow_two, ← hr, ← map_mul, show algebraMap ℝ D √r * x = x * algebraMap ℝ D √r from Algebra.commutes' _ _]
      simp only [sub_add_sub_cancel, ← map_sub, map_eq_zero]
      rw [sub_eq_zero, ← pow_two]
      symm
      apply Real.sq_sqrt
      positivity
    simp only [mul_eq_zero] at eq1
    rcases eq1 with eq1|eq1
    · use Real.sqrt r
      rw [sub_eq_zero] at eq1
      rw [eq1]
    · use - Real.sqrt r
      rwa [map_neg, eq_comm, eq_neg_iff_add_eq_zero]

lemma x_is_in_V (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x.1 = k.val z)
    (hDD : Module.finrank ℝ D = 4) : x.1 ∈ V := by
  let hx3 := hx
  apply x2_is_real _ at hx
  let hx' := hx hDD
  have hx := real_sq_in_R_or_V _ hx'
  have : x.1 ∉ (algebraMap ℝ D).range := by
    by_contra! hxx
    obtain ⟨r, hr⟩ := hxx
    have xcomm : ∀ (y : k), x.1⁻¹ * k.val y * x.1 = k.val y := by
      intro y
      rw [← hr, mul_assoc]
      simp only [Subalgebra.coe_val, ← Algebra.commutes, ← mul_assoc]
      rw [mul_inv_cancel₀ (by simp [hr, Units.ne_zero]), one_mul]
    specialize xcomm (e.symm Complex.I)
    specialize hx3 (e.symm Complex.I)
    rw [← xcomm] at hx3
    symm at hx3
    simp only [f_apply, AlgEquiv.apply_symm_apply, Complex.conj_I, map_neg, NegMemClass.coe_neg,
      mul_neg, neg_mul, Subalgebra.coe_val, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at hx3
    cases' hx3 with hx31 hx32
    · rw [show (2 : D) = (1 : D) + (1 : D) by norm_num, ← two_smul ℝ,
        smul_eq_zero] at hx31; aesop
    · simp only [inv_eq_zero, Units.ne_zero, ZeroMemClass.coe_eq_zero,
      EmbeddingLike.map_eq_zero_iff, Complex.I_ne_zero, or_self] at hx32
  simp_all only [Set.mem_setOf_eq, false_or, RingHom.mem_range, not_exists]

-- instance : NoZeroSMulDivisors ℝ D := inferInstance

lemma x_corre_R (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x.1 = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    ∃(r : ℝ), algebraMap ℝ D r = - x.1^2 := by
  have := x_is_in_V _ _ _ hx
  rw [V_def] at this
  obtain ⟨r, hr1, hr2⟩ := this hDD
  use -r
  simp only [map_neg, hr2]

lemma r_pos (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x.1 = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    0 < (x_corre_R _ _ _ hx hDD).choose := by
  have eq1 := x_is_in_V _ _ _ hx
  rw [V_def] at eq1
  obtain ⟨r, hr1, hr2⟩ := eq1 hDD
  have eq2 := x_corre_R _ _ _ hx hDD|>.choose_spec
  have : -r = (x_corre_R _ _ _ hx hDD).choose := by
    apply_fun -(·) at hr2
    simp only [Pi.neg_apply] at hr2
    have := eq2.trans hr2
    simp only [← map_neg] at this
    exact FaithfulSMul.algebraMap_injective _ _ this|>.symm
  rw [← this]
  simp only [Left.neg_pos_iff, hr1]

lemma j_mul_j (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    (algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * ↑x *
    ((algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * ↑x) = (-1 : ℝ) • 1 := by
  rw [← mul_assoc, show algebraMap ℝ D _ = (algebraMap ℝ k _ : D) from rfl]
  have hx1 := hx
  specialize hx $ (algebraMap ℝ k (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹)
  simp only [AlgHom.commutes, Subalgebra.coe_val] at hx
  apply_fun (x.1 * · ) at hx
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero x), one_mul] at hx
  rw [mul_assoc _ x.1, ← hx, ← mul_assoc, ← Subalgebra.coe_mul, ← map_mul (algebraMap ℝ k),
    ← mul_inv, ← pow_two, Real.sq_sqrt, show (algebraMap ℝ k _ : D) =
    algebraMap ℝ D _ from rfl, map_inv₀ (algebraMap ℝ D) (x_corre_R _ _ _ hx1 hDD).choose,
    (x_corre_R _ _ _ hx1 hDD).choose_spec, mul_assoc, ← pow_two, ← neg_inv, neg_mul,
    inv_mul_cancel₀ (by simp_all only [f_apply, Subalgebra.coe_val, Subtype.forall, map_inv₀,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Units.ne_zero])]
  simp only [f_apply, Subalgebra.coe_val, Subtype.forall, neg_smul, one_smul]
  exact le_of_lt $ r_pos _ _ _ hx1 hDD

lemma jij_eq_negi (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    ((algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * x.1) * e.symm ⟨0, 1⟩ *
    ((algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * x.1)⁻¹ = - e.symm ⟨0, 1⟩ := by
  rw [show algebraMap ℝ D _ = (algebraMap ℝ k _ : D) from rfl, mul_inv_rev, ← mul_assoc]
  have hx1 := hx
  specialize hx $ e.symm ⟨0, 1⟩
  apply_fun (x.1 * · * x.1⁻¹) at hx
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero x), one_mul, mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero x), mul_one] at hx
  simp only [f_apply, AlgEquiv.apply_symm_apply, Subalgebra.coe_val] at hx
  rw [mul_assoc, mul_assoc, mul_assoc]; nth_rw 2 [← mul_assoc, ← mul_assoc]
  rw [← hx, ← Complex.I, Complex.conj_I, ← mul_assoc, ← Subalgebra.coe_mul, mul_comm,
    Subalgebra.coe_mul, mul_assoc, mul_inv_cancel₀ (by
      simp only [map_inv₀, ne_eq, ZeroMemClass.coe_eq_zero, inv_eq_zero, map_eq_zero]
      by_contra! zero
      apply_fun (·)^2 at zero
      rw [Pi.pow_apply, Real.sq_sqrt (le_of_lt (r_pos _ _ _ hx1 hDD)), Pi.pow_apply,
        pow_two 0, zero_mul] at zero
      haveI := r_pos _ _ _ hx1
      simp_all only [f_apply, Subalgebra.coe_val, Subtype.forall, lt_self_iff_false]), mul_one, map_neg,
    Subalgebra.coe_neg]

lemma k_sq_eq_negone (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    (e.symm ⟨0, 1⟩ * ((algebraMap ℝ D (Real.sqrt
    (x_corre_R k e x hx hDD).choose)⁻¹) * x.1))^2 = -1 := by
  rw [pow_two]
  set j := (algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1 with j_eq
  nth_rw 2 [← mul_one (e.symm { re := 0, im := 1 })]
  rw [Subalgebra.coe_mul, Subalgebra.coe_one]
  nth_rw 1 [← @inv_mul_cancel₀ _ _ j (by
    simp only [j_eq, map_inv₀, ne_eq, mul_eq_zero, inv_eq_zero, map_eq_zero,
      Units.ne_zero, or_false]
    by_contra! heq
    apply_fun (·)^2 at heq
    rw [Pi.pow_apply, Real.sq_sqrt (le_of_lt (r_pos _ _ _ hx hDD)), Pi.pow_apply,
      pow_two 0, zero_mul] at heq
    haveI := r_pos _ _ _ hx
    simp_all only [Real.sqrt_zero, inv_zero, map_zero, zero_mul, lt_self_iff_false]), mul_assoc]
  nth_rw 2 [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  rw [jij_eq_negi _ _ _ hx, ← Subalgebra.coe_neg, ← map_neg e.symm, ← mul_assoc,
    ← mul_assoc, ← mul_assoc, ← Subalgebra.coe_mul, ← map_mul e.symm, ← Complex.I, mul_neg,
    Complex.I_mul_I, neg_neg, map_one, Subalgebra.coe_one, one_mul, mul_assoc, j_mul_j _ _ _ hx]
  simp only [neg_smul, one_smul]
  · exact hDD
  · exact hDD

omit hD [FiniteDimensional ℝ D] in
lemma i_mul_i : (e.symm ⟨0, 1⟩ : D) * e.symm ⟨0, 1⟩ = (-1 : ℝ) • 1 := by
  rw [← Subalgebra.coe_mul, ← _root_.map_mul e.symm, ← Complex.I, Complex.I_mul_I, map_neg,
    map_one, Subalgebra.coe_neg, Subalgebra.coe_one]; simp

omit hD [FiniteDimensional ℝ D] in
lemma i_ne_zero : (e.symm ⟨0, 1⟩ : D) ≠ 0 := by
  intro h
  change _ = ((0 : k) : D) at h
  simp only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, EmbeddingLike.map_eq_zero_iff] at h
  rw [Complex.ext_iff] at h
  obtain ⟨_, h⟩ := h
  simp only [Complex.zero_im, one_ne_zero] at h

lemma j_ne_zero (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    ((algebraMap ℝ D (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹) * x.1) ≠ 0 := by
  intro h
  simp only [mul_eq_zero, Units.ne_zero, or_false, i_ne_zero, false_or] at h
  simp only [map_inv₀, inv_eq_zero, map_eq_zero] at h
  apply_fun (·)^2 at h
  rw [Pi.pow_apply, Real.sq_sqrt (le_of_lt (r_pos _ _ _ hx _)), Pi.pow_apply,
    pow_two 0, zero_mul] at h
  · exact (r_pos _ _ _ hx hDD).ne' h
  · exact hDD

lemma k_ne_zero (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    e.symm ⟨0, 1⟩ * ((algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1) ≠ 0 := by
  intro h
  rw [mul_eq_zero] at h
  cases' h with h1 h2
  · exact (i_ne_zero k e) h1
  · exact (j_ne_zero _ _ _ hx hDD) h2

lemma j_mul_i_eq_neg_i_mul_j (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    (algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * ↑x *
    ↑(e.symm { re := 0, im := 1 }) = -(↑(e.symm { re := 0, im := 1 }) *
    ((algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * ↑x)) := by
  have := k_sq_eq_negone _ _ _ hx hDD
  rw [pow_two] at this
  set j := (algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1 with j_eq
  apply_fun (· * ((↑(e.symm { re := 0, im := 1 }) * j)⁻¹)) at this
  rw [mul_assoc, mul_inv_cancel₀ (k_ne_zero _ _ _ hx hDD), mul_one, mul_inv_rev] at this
  have jinv : j⁻¹ = -j := by
    rw [← mul_eq_one_iff_inv_eq₀ (j_ne_zero _ _ _ hx _), mul_neg, j_mul_j _ _ _ hx]
    simp only [neg_smul, one_smul, neg_neg]
    exact hDD; exact hDD
  have iinv : ((e.symm { re := 0, im := 1 })).1⁻¹ = - (e.symm { re := 0, im := 1 }).1 := by
    rw [← mul_eq_one_iff_inv_eq₀ (i_ne_zero _ _), mul_neg, ← Subalgebra.coe_mul,
      ← map_mul e.symm, ← Complex.I, Complex.I_mul_I, map_neg, map_one, Subalgebra.coe_neg,
      neg_neg]; rfl
  rw [jinv, iinv] at this
  simp only [mul_neg, neg_mul, neg_neg, one_mul] at this
  apply_fun fun x ↦ -x at this
  simp only [Pi.neg_apply, neg_neg] at this
  exact this.symm

open Quaternion

set_option synthInstance.maxHeartbeats 40000 in
abbrev toFun (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    ℍ[ℝ] →ₐ[ℝ] D := QuaternionAlgebra.lift (R := ℝ) (A := D) {
  i := e.symm ⟨0, 1⟩
  j := (algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1
  k := e.symm ⟨0, 1⟩ * ((algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1)
  i_mul_i := by rw [i_mul_i _ e, zero_smul, add_zero]
  j_mul_j := j_mul_j _ _ _ hx hDD
  i_mul_j := by rfl
  j_mul_i := by
    rw [j_mul_i_eq_neg_i_mul_j _ _ _ hx hDD, zero_smul, zero_sub]
}

abbrev basisijk (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
  (hDD : Module.finrank ℝ D = 4) : Fin 4 → D :=
  Fin.cons (e.symm ⟨0, 1⟩ * ((algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1))
  (Fin.cons ((algebraMap ℝ D (Real.sqrt (x_corre_R k e x hx hDD).choose)⁻¹) * x.1)
    ![(1 : D), e.symm ⟨0, 1⟩])

-- instance : NoZeroSMulDivisors ℝ k := inferInstance

set_option synthInstance.maxHeartbeats 60000 in
omit hD [FiniteDimensional ℝ D] in
lemma linindep1i :
    LinearIndependent ℝ ![(1 : D), ↑(e.symm { re := 0, im := 1 })] := by
  rw [LinearIndependent.pair_iff']
  · intro r
    rw [show (1 : D) = (1 : k) from rfl, ← Subalgebra.coe_smul,
      ← _root_.map_one e.symm, ← map_smul e.symm]
    -- suffices e.symm (r • 1) ≠ e.symm ⟨0, 1⟩ by aesop
    suffices r • 1 ≠ (⟨0, 1⟩ : ℂ) by
      simp_all only [f_apply, Subalgebra.coe_val, Subtype.forall, Complex.real_smul,
        mul_one, ne_eq, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true]
    rw [show (1 : ℂ) = ⟨1, 0⟩ from rfl, show r • ⟨1, 0⟩ = (⟨r, 0⟩ : ℂ) by
      apply Complex.ext <;> simp]
    by_contra! h
    rw [Complex.ext_iff] at h
    simp_all only [f_apply, Subalgebra.coe_val, Subtype.forall, zero_ne_one, and_false]
  · exact one_ne_zero

set_option synthInstance.maxHeartbeats 60000 in
set_option maxHeartbeats 400000 in
lemma linindep1ij (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    LinearIndependent ℝ (Fin.cons ((algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹ * ↑x)
      ![1, ↑(e.symm { re := 0, im := 1 })]) := by
  rw [linearIndependent_fin_cons]
  constructor
  · exact linindep1i _ _
  · simp only [Nat.reduceAdd, map_inv₀, Fin.init_snoc, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, Fin.snoc_last]
    rw [Submodule.mem_span_pair]
    by_contra! h
    obtain ⟨a, b, hab⟩ := h
    rw [show (1 : D) = (1 : k) from rfl, ← Subalgebra.coe_smul, ← Subalgebra.coe_smul,
        ← _root_.map_one e.symm, ← map_smul e.symm, ← map_smul e.symm, ← Subalgebra.coe_add,
        ← map_add e.symm, show (1 : ℂ) = ⟨1, 0⟩ from rfl, show b • ⟨1, 0⟩ = (⟨b, 0⟩ : ℂ) by
        apply Complex.ext <;> simp, show a • ⟨0, 1⟩ = (⟨0, a⟩ : ℂ) by
        apply Complex.ext <;> simp, show ⟨0, a⟩ + ⟨b, 0⟩ = (⟨b, a⟩ : ℂ) by
        apply Complex.ext <;> simp] at hab
    apply_fun ((algebraMap ℝ D) (Real.sqrt (x_corre_R _ _ _ hx hDD).choose) * · ) at hab
    rw [← mul_assoc, mul_inv_cancel₀ (by
      simp_all only [ne_eq, map_eq_zero]
      by_contra! eqzero
      rw [Real.sqrt_eq_zero (le_of_lt (r_pos _ _ _ hx hDD))] at eqzero
      have := r_pos _ _ _ hx
      simp_all only [Real.sqrt_zero, map_zero, zero_mul, inv_zero, mul_zero, lt_self_iff_false]),
      one_mul] at hab
    rw [show algebraMap ℝ D _ = (algebraMap ℝ k _ : D) from rfl, ← Subalgebra.coe_mul] at hab
    have : ∃(y : k), y = x.1 := ⟨_, hab⟩
    obtain ⟨y, hy⟩ := this
    have hyy : x.1 ≠ 0 := Units.ne_zero x
    rw [← hy] at hx hyy
    rw [show y.1⁻¹ = (y⁻¹ : k) by
      apply_fun (· * (y : D)) using (mul_left_injective₀ hyy)
      simp only
      rw [inv_mul_cancel₀ hyy, ← Subalgebra.coe_mul, inv_mul_cancel₀ (Subtype.coe_ne_coe.1 hyy)]
      rfl] at hx
    simp_rw [← Subalgebra.coe_mul] at hx
    change ∀(z : k), _ = (z : D) at hx
    simp_rw [Subtype.coe_inj, mul_comm, ← mul_assoc,
      mul_inv_cancel₀ (Subtype.coe_ne_coe.1 hyy), one_mul] at hx
    specialize hx $ e.symm Complex.I
    simp only [f_apply, AlgEquiv.apply_symm_apply, Complex.conj_I, map_neg] at hx
    symm at hx
    rw [eq_neg_iff_add_eq_zero] at hx
    ring_nf at hx
    simp only [mul_eq_zero] at hx
    cases' hx with hx1 hx2
    · apply_fun e at hx1
      simp only [map_zero, e.apply_symm_apply] at hx1
      rw [Complex.ext_iff] at hx1
      obtain ⟨hx11, hx12⟩ := hx1
      simp only [Complex.I_im, Complex.zero_im, one_ne_zero] at hx12
    · rw [show (2 : k) = (1 : k) + (1 : k) by norm_num, ← two_smul ℝ,
        smul_eq_zero] at hx2
      simp_all only [OfNat.ofNat_ne_zero, one_ne_zero, or_self]

set_option synthInstance.maxHeartbeats 40000 in
-- set_option maxHeartbeats 600000 in
lemma linindepijk (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (hDD : Module.finrank ℝ D = 4) :
    LinearIndependent ℝ (basisijk k e x hx hDD) := by
  rw [linearIndependent_fin_cons]
  constructor
  · exact linindep1ij _ _ _ hx hDD
  · by_contra! h
    simp only [Fin.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, Submodule.mem_span_insert, Submodule.mem_span_pair,
      exists_exists_exists_and_eq] at h
    simp_rw [Submodule.mem_span_singleton] at h
    obtain ⟨c, d, ⟨b, d', ⟨a, hc⟩, had⟩, heq⟩ := h
    rw [← hc] at had; rw [had] at heq
    rw [add_comm] at heq; nth_rw 2 [add_comm] at heq
    clear hc had
    set k := ↑(e.symm { re := 0, im := 1 }) * (((algebraMap ℝ D)
      (Real.sqrt (x_corre_R _ _ _ hx hDD).choose)⁻¹) * ↑x) with k_eq
    have := k_sq_eq_negone _ _ _ hx hDD
    set j := (algebraMap ℝ D (Real.sqrt (x_corre_R _ e x hx hDD).choose)⁻¹) * x.1 with j_eq
    set i := e.symm ⟨0, 1⟩ with i_eq
    rw [← k_eq, heq, pow_two, mul_add, mul_add, add_mul, add_mul, add_mul, add_mul, add_mul,
      add_mul] at this
    simp only [Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc, one_mul] at this
    rw [j_mul_j _ _ _ hx hDD, j_mul_i_eq_neg_i_mul_j _ _ _ hx hDD, i_mul_i _ _, ← j_eq,
      ← i_eq, ← k_eq] at this
    replace this : (a * a - b * b - c * c + (1 : ℝ)) • (1 : D) + (2 * a * b) • i +
      (2 * a * c) • j = 0 := by linear_combination (norm := module) this
    have ijindep := linindep1ij _ _ _ hx hDD
    rw [← i_eq, ← j_eq, Fintype.linearIndependent_iff] at ijindep
    specialize ijindep ![(2 * a * c), (a * a - b * b - c * c + (1 : ℝ)), (2 * a * b)]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at ijindep
    specialize ijindep (by
      simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Fin.cons_zero,
        Matrix.cons_val_one, Matrix.head_cons, Fin.cons_one, Matrix.cons_val_two,
        Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons]
      rw [← Fin.succ_one_eq_two, Fin.cons_succ]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      rw [add_assoc, add_comm]; exact this)
    have h1 := ijindep ⟨0, by omega⟩
    have h2 := ijindep ⟨1, by omega⟩
    have h3 := ijindep ⟨2, by omega⟩
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Fin.reduceFinMk,
      Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons] at h1 h2 h3
    have ha : a = 0 := by
      by_contra! h
      simp only [h, false_or] at h1 h3
      simp only [h3, mul_zero, sub_zero, h1, add_eq_zero_iff_eq_neg] at h2
      rw [← pow_two] at h2
      have haa := h2
      apply_fun Real.sqrt at h2
      if ha1 : a < 0 then
      have e1: 0 < a^2 := sq_pos_of_ne_zero h
      have e2: a^2 < 0 := by rw [haa]; simp
      linarith
      else
      simp only [not_lt] at ha1
      rw [Real.sqrt_sq ha1, Real.sqrt_eq_zero_of_nonpos (by linarith)] at h2
      rw [h2, pow_two, mul_zero] at haa
      norm_num at haa
    simp only [ha, mul_zero, zero_sub, zero_smul, zero_add] at h2 heq
    have hbc : b ≠ 0 ∨ c ≠ 0 := by
      by_contra! hbc
      obtain ⟨⟩ := hbc
      simp_all
    have hb : b = 0 := by
      have heq' := heq
      apply_fun (i.1 * ·) at heq
      nth_rw 1 [k_eq, ← mul_assoc, i_mul_i] at heq
      simp only [neg_smul, one_smul, neg_mul, one_mul, mul_add, Algebra.mul_smul_comm, i_mul_i _ _,
        smul_neg] at heq
      rw [← k_eq, heq'] at heq
      simp only [smul_add, smul_smul, ← add_assoc] at heq
      symm at heq
      rw [eq_neg_iff_add_eq_zero, add_assoc _ _ j] at heq
      nth_rw 2 [← one_smul ℝ j] at heq; rw [← add_smul, i_mul_i _ _] at heq
      have h1 := linindep1ij _ _ _ hx hDD
      rw [Fintype.linearIndependent_iff] at h1
      specialize h1 ![(c * c + 1), -b, (c * b)]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_three, Fin.isValue,
        Matrix.cons_val_zero, Fin.cons_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.cons_one,
        Matrix.cons_val_two, Matrix.tail_cons, ← j_eq, ← i_eq] at h1
      rw [← Fin.succ_one_eq_two, Fin.cons_succ] at h1
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons] at h1
      rw [add_comm, ← add_assoc, neg_smul, one_smul, smul_neg, ← neg_smul] at heq
      specialize h1 heq ⟨1, by omega⟩
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, neg_eq_zero] at h1
      exact h1
    have hc : c = 0 := by
      simp only [hb, zero_smul, zero_add] at heq
      rw [Algebra.smul_def, k_eq, mul_eq_mul_right_iff] at heq
      have : j ≠ 0 := j_ne_zero _ _ _ hx hDD
      simp only [this, or_false] at heq
      rename_i _ _ k' _ _
      change _ = ((algebraMap ℝ k' _) : D) at heq
      simp only [SetLike.coe_eq_coe, i_eq] at heq
      apply_fun e at heq
      rw [e.apply_symm_apply] at heq
      simp only [AlgEquiv.commutes, Complex.coe_algebraMap] at heq
      change ⟨0, 1⟩ = (⟨c, 0⟩ : ℂ) at heq
      rw [Complex.ext_iff] at heq
      obtain ⟨hc, _⟩ := heq
      simp only at hc
      exact hc.symm
    tauto

abbrev isBasisijk (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (h : Module.finrank ℝ D = 4) : Basis (Fin 4) ℝ D := .mk
    (v := basisijk _ _ _ hx h) (linindepijk _ _ _ hx h)
    (by
      suffices (⊤ : Submodule ℝ D) = Submodule.span ℝ (Set.range (basisijk _ _ _ hx h))
        from le_of_eq this
      exact LinearIndependent.span_eq_top_of_card_eq_finrank (K := ℝ) (b := basisijk _ _ _ hx h)
        (linindepijk _ _ _ hx h) (by simp only [Fintype.card_fin, h])|>.symm )

abbrev linEquivH (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (h : Module.finrank ℝ D = 4) : ℍ[ℝ] ≃ₗ[ℝ] D :=
  Basis.equiv (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1 : ℝ)) (isBasisijk _ _ _ hx h)
    $ {
      toFun := ![2, 3, 1, 0]
      invFun := ![3, 2, 0, 1]
      left_inv := fun i ↦ by fin_cases i <;> simp
      right_inv := fun i ↦ by fin_cases i <;> simp
    }

lemma toFun_i_eq (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (h : Module.finrank ℝ D = 4) :
    toFun _ _ _ hx h ((QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1 : ℝ)) 1) = e.symm ⟨0, 1⟩ := by
  simp only [QuaternionAlgebra.lift_apply, QuaternionAlgebra.Basis.liftHom, map_inv₀,
    QuaternionAlgebra.basisOneIJK, Fin.isValue, Basis.coe_ofEquivFun,
    QuaternionAlgebra.coe_linearEquivTuple_symm, QuaternionAlgebra.equivTuple_symm_apply, ne_eq,
    zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_eq_same, Fin.reduceEq,
    AlgHom.coe_mk', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, QuaternionAlgebra.Basis.lift,
    map_zero, one_smul, zero_add, zero_smul, add_zero]

@[simp] theorem succ_two_eq_three (n : ℕ) : Fin.succ (2 : Fin (n + 3)) = 3 := rfl

lemma linEquivH_eq_toFun (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (h : Module.finrank ℝ D = 4) : (linEquivH _ _ _ hx h).toLinearMap = toFun _ _ _ hx h := by
  apply Basis.ext (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1 : ℝ))
  intro i
  change (linEquivH _ _ _ hx h) _ = (toFun _ _ _ hx h) _
  fin_cases i
  · erw [Basis.equiv_apply]
    simp only [Fin.isValue, Fin.zero_eta, Equiv.coe_fn_mk, Matrix.cons_val_zero, Basis.coe_mk,
      basisijk, map_inv₀, QuaternionAlgebra.lift_apply, QuaternionAlgebra.Basis.liftHom,
      QuaternionAlgebra.basisOneIJK, Basis.coe_ofEquivFun,
      QuaternionAlgebra.coe_linearEquivTuple_symm, QuaternionAlgebra.equivTuple_symm_apply,
      Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, Fin.reduceEq,
      AlgHom.coe_mk', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, QuaternionAlgebra.Basis.lift,
      map_one, zero_smul, add_zero]
    rw [← Fin.succ_one_eq_two, Fin.cons_succ, ← Fin.succ_zero_eq_one, Fin.cons_succ]; simp
  · erw [Basis.equiv_apply]
    simp only [Fin.isValue, Fin.mk_one, Equiv.coe_fn_mk, Matrix.cons_val_one, Matrix.head_cons,
      Basis.coe_mk, basisijk, map_inv₀, QuaternionAlgebra.lift_apply,
      QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.basisOneIJK, Basis.coe_ofEquivFun,
      QuaternionAlgebra.coe_linearEquivTuple_symm, QuaternionAlgebra.equivTuple_symm_apply, ne_eq,
      zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_eq_same, Fin.reduceEq,
      AlgHom.coe_mk', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, QuaternionAlgebra.Basis.lift,
      map_zero, one_smul, zero_add, zero_smul, add_zero]
    rw [← succ_two_eq_three, Fin.cons_succ, ← Fin.succ_one_eq_two, Fin.cons_succ]; simp
  · erw [Basis.equiv_apply]
    simp [QuaternionAlgebra.basisOneIJK, QuaternionAlgebra.Basis.liftHom,
      QuaternionAlgebra.Basis.lift]
  · erw [Basis.equiv_apply]
    simp [QuaternionAlgebra.basisOneIJK, QuaternionAlgebra.Basis.liftHom,
      QuaternionAlgebra.Basis.lift]

-- set_option maxHeartbeats 600000 in
lemma bij_tofun (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (h : Module.finrank ℝ D = 4) : Function.Bijective (toFun _ _ _ hx h) := by
  have eq1 := linEquivH_eq_toFun _ _ _ hx h
  haveI := LinearEquiv.bijective (linEquivH _ _ _ hx h)
  have eq2 : @DFunLike.coe (ℍ[ℝ] ≃ₗ[ℝ] D) ℍ[ℝ] (fun x ↦ D) EquivLike.toFunLike
      (linEquivH k e x hx h) = @DFunLike.coe (ℍ[ℝ] →ₐ[ℝ] D) ℍ[ℝ] (fun x ↦ D)
      AlgHom.funLike (toFun k e x hx h) := by
    ext x
    change (linEquivH _ _ _ hx h) x = (toFun _ _ _ hx h).toLinearMap x
    exact DFunLike.congr eq1.symm rfl|>.symm
  rw [← eq2]; exact this

theorem rank4_iso_H (x : Dˣ) (hx : ∀ (z : k), (x.1⁻¹) * (f k e z) * x = k.val z)
    (h : Module.finrank ℝ D = 4) : Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) :=
  ⟨AlgEquiv.ofBijective (toFun _ _ _ hx h) (bij_tofun _ _ _ hx h)⟩

set_option synthInstance.maxHeartbeats 40000 in
abbrev SmulCA (A : Type) [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    (e : ℂ ≃ₐ[ℝ] (Subalgebra.center ℝ A)) : ℂ →+* A where
  toFun z := e z
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' z1 z2 := by simp

instance AlgCA (A : Type) [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    (e : ℂ ≃ₐ[ℝ] (Subalgebra.center ℝ A)) : Algebra ℂ A where
  __ := SmulCA A e
  smul z a := (SmulCA A e z) * a
  commutes' z _ := by
    simp [Subalgebra.mem_center_iff.1 (e z).2]
  smul_def' _ _ := rfl

set_option synthInstance.maxHeartbeats 40000 in
lemma smulCRassoc (A : Type) [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    (e : ℂ ≃ₐ[ℝ] (Subalgebra.center ℝ A)) (r : ℝ) (z : ℂ) (a : A) : e (r • z) * a =
    r • (e z * a) := by
  rw [map_smul e, Subalgebra.coe_smul]
  exact smul_mul_assoc r (↑(e z)) a

set_option synthInstance.maxHeartbeats 40000 in
theorem centereqvCisoC (A : Type) [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    (hA : Nonempty ((Subalgebra.center ℝ A) ≃ₐ[ℝ] ℂ)) : Nonempty (A ≃ₐ[ℝ] ℂ) := by
  have e := hA.some.symm
  letI : Algebra ℂ A := AlgCA A e
  have : IsScalarTower ℝ ℂ A := { smul_assoc := smulCRassoc A e }
  rename_i _ _ fin _
  unfold FiniteDimensional at fin
  have : Algebra.toModule (R := ℝ) (A := A) = Module.complexToReal A := by
    ext r a
    change r • a = (e (algebraMap ℝ ℂ r)) * a
    rw [Algebra.algebraMap_eq_smul_one, _root_.map_smul e, map_one, Subalgebra.coe_smul,
      Subalgebra.coe_one, smul_mul_assoc, one_mul]
  haveI : IsNoetherian ℝ A := IsNoetherian.iff_fg.2 $ fin
  haveI : FiniteDimensional ℂ A := Module.Finite.right ℝ ℂ A
  have bij := bijective_algebraMap_of_finiteDimensional_divisionRing_over_algClosed ℂ A
  exact ⟨(AlgEquiv.ofBijective {
    toFun := algebraMap ℂ A
    map_one' := _
    map_mul' := _
    map_zero' := _
    map_add' := _
    commutes' r := by
      simp; change (algebraMap ℂ A) (algebraMap ℝ ℂ r) = _;
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]} bij).symm ⟩

abbrev iSup_chain_subfield (D : Type) [DivisionRing D] [Algebra ℝ D] (α : Set (SubField ℝ D))
    [Nonempty α] (hα : IsChain (· ≤ ·) α) : SubField ℝ D :=
  {
  __ := (⨆ (L : α), L.1.1 : Subalgebra ℝ D)
  mul_comm := by
    rintro x y hx hy
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      SetLike.mem_coe] at hx hy
    have := Subalgebra.coe_iSup_of_directed hα.directed
    dsimp at this
    change x ∈ (_ : Set _) at hx; change _ ∈ ( _ : Set _) at hy
    rw [this] at hx hy
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx hy
    obtain ⟨L1, hL1, hx⟩ := hx
    obtain ⟨L2, hL2, hy⟩ := hy
    obtain ⟨L3, _, hL31, hL32⟩ := hα.directedOn L1 hL1 L2 hL2
    exact L3.mul_comm x y (hL31 hx) (hL32 hy)
  inverse := by
    rintro x hx hx0
    simp only [Subalgebra.coe_toSubsemiring,
      Subsemiring.coe_carrier_toSubmonoid, SetLike.mem_coe] at *
    letI : Nonempty α := Set.Nonempty.to_subtype (Set.Nonempty.of_subtype)
    have := Subalgebra.coe_iSup_of_directed hα.directed
    dsimp at this
    change x ∈ (_ : Set _) at hx
    rw [this] at hx
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
    obtain ⟨L1, hL1, hx⟩ := hx
    use L1.inverse x hx hx0|>.choose
    constructor
    · have : L1.1 ≤ ⨆ (L : α), (L.1).toSubalgebra := by
        exact le_iSup_of_le (ι := α) (f := fun x ↦ x.1.1) (a := L1.1) ⟨L1, hL1⟩ (by rfl)
      exact this (L1.inverse x hx hx0).choose_spec.1
    · exact L1.inverse x hx hx0|>.choose_spec.2
  }

-- set_option maxHeartbeats 1600000 in
lemma exitsmaxsub (D : Type) [DivisionRing D] [Algebra ℝ D] : ∃(L : SubField ℝ D),
    IsMaximalSubfield ℝ D L := by
  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := SubField ℝ D) (fun α hα hα' ↦ by
    letI : Nonempty α := by exact Set.Nonempty.to_subtype hα'
    use iSup_chain_subfield D α hα
    change (iSup_chain_subfield D α hα) ∈ {L | _}
    simp only [Set.mem_setOf_eq]
    intro L hL
    change L.1 ≤ (⨆ (L : α), L.1.1 : Subalgebra ℝ D)
    exact le_iSup_of_le (ι := α) (f := fun x ↦ x.1.1) (a := L.1) ⟨L, hL⟩ (by rfl) |>.trans <|
      by trivial)
  exact ⟨m, isMax_iff_isMaxSubfield _ _ _ |>.1 hm⟩

set_option synthInstance.maxHeartbeats 40000 in
theorem FrobeniusTheorem (A : Type) [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A] :
    Nonempty (A ≃ₐ[ℝ] ℂ) ∨ Nonempty (A ≃ₐ[ℝ] ℝ) ∨ Nonempty (A ≃ₐ[ℝ] ℍ[ℝ]) := by
  have hh := RealExtension_is_RorC (Subalgebra.center ℝ A)
  cases' hh with hR hC
  · right
    obtain hR := hR.some
    have : Subalgebra.center ℝ A = ⊥ := by
      have := LinearEquiv.finrank_eq hR.toLinearEquiv
      simp only [Module.finrank_self, Subalgebra.finrank_eq_one_iff] at this
      exact this
    have hAA : Algebra.IsCentral ℝ A := ⟨le_of_eq this⟩
    have hhA' (L : SubField ℝ A) (hL : IsMaximalSubfield ℝ A L) :
      Module.finrank ℝ L = 1 ∨ Module.finrank ℝ L = 2 := by
      have := RealExtension_is_RorC L
      cases' this with hR hH
      · have := LinearEquiv.finrank_eq hR.some.toLinearEquiv
        simp only [Module.finrank_self, Subalgebra.finrank_eq_one_iff] at this
        exact Or.inl this
      · have := LinearEquiv.finrank_eq hH.some.toLinearEquiv
        simp only [Complex.finrank_real_complex] at this
        exact Or.inr this
    specialize hhA'
    obtain ⟨L, hL⟩ := exitsmaxsub A
    specialize hhA' L hL
    have dimeq := dim_max_subfield ℝ A L hL
    cases' hhA' with h1 h2
    · left
      simp only [h1, mul_one] at dimeq
      exact rank_1_D_iso_R dimeq
    · right
      simp only [h2, Nat.reduceMul] at dimeq
      have e := RealExtension_is_RorC L
      cases' e with e1 e2
      · exfalso
        have := LinearEquiv.finrank_eq e1.some.toLinearEquiv
        rw [Module.finrank_self] at this
        linarith
      · exact ⟨(rank4_iso_H L e2.some (f_is_conjugation L e2.some).choose
          (f_is_conjugation L e2.some).choose_spec dimeq).some.symm⟩
  · left; exact centereqvCisoC A hC
