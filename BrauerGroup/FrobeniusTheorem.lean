import BrauerGroup.QuatBasic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import BrauerGroup.Subfield.Subfield
import Mathlib.Algebra.Star.Basic
import BrauerGroup.SkolemNoether

suppress_compilation

open Quaternion TensorProduct BigOperators Classical FiniteDimensional

variable {D : Type} [DivisionRing D]

section prerequisites

set_option synthInstance.maxHeartbeats 40000 in
theorem rank_1_D_iso_R [Algebra ℝ D] : FiniteDimensional.finrank ℝ D = 1 →
    Nonempty (D≃ₐ[ℝ] ℝ) := fun h => by
  have h' := Subalgebra.finrank_eq_one_iff (F := ℝ) (S := (⊤ : Subalgebra ℝ D))
  have : FiniteDimensional.finrank ℝ (⊤ : Subalgebra ℝ D) = 1 := by
    simp_all only [Subalgebra.finrank_eq_one_iff, Subalgebra.bot_eq_top_of_finrank_eq_one]
  exact ⟨Subalgebra.topEquiv.symm.trans $ Subalgebra.equivOfEq _ _
    (h'.1 this)|>.trans $ Algebra.botEquiv ℝ D⟩

lemma RealExtension_is_RorC (K : Type) [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]:
    Nonempty (K ≃ₐ[ℝ] ℝ) ∨ Nonempty (K ≃ₐ[ℝ] ℂ) := by
  --Zulip
  sorry

lemma field_over_R_iso_C (K : Type) [Field K] [Algebra ℝ K] (h : finrank ℝ K = 2) :
    Nonempty (K ≃ₐ[ℝ] ℂ) := by
    haveI : FiniteDimensional ℝ K := .of_finrank_eq_succ h
    haveI : Algebra.IsAlgebraic ℝ K := Algebra.IsAlgebraic.of_finite _ _
    haveI : Algebra.IsAlgebraic ℝ (AlgebraicClosure K) :=
      Algebra.IsAlgebraic.trans (K := ℝ) (L := K)
    let ι₀ : (AlgebraicClosure K) →ₐ[ℝ] ℂ :=
        IsAlgClosed.lift (R := ℝ) (M := ℂ) (S := AlgebraicClosure K)
    let ι₁ : K →ₐ[ℝ] AlgebraicClosure K :=
        IsScalarTower.toAlgHom ℝ K (AlgebraicClosure K)
    exact .intro <| AlgEquiv.ofBijective (ι₀.comp ι₁) <|
        LinearMap.linearEquivOfInjective (ι₀.comp ι₁).toLinearMap (RingHom.injective _)
            (h.trans Complex.finrank_real_complex.symm) |>.bijective

lemma D_equiv_C [Algebra ℂ D] [FiniteDimensional ℂ D]:
    Nonempty (D ≃ₐ[ℂ] ℂ) := by
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed ℂ D
  haveI : NeZero n := ⟨hn⟩
  exact Wedderburn_Artin_uniqueness₀ ℂ D 1 n D (BrauerGroup.dim_one_iso D).symm ℂ iso

end prerequisites

section isoC

variable [Algebra ℝ D] (e : Subring.center D ≃ₐ[ℝ] ℂ)

variable (D) in
set_option linter.unusedVariables false in
def DD (e : Subring.center D ≃ₐ[ℝ] ℂ):= D

instance : DivisionRing (DD D e) := inferInstanceAs (DivisionRing D)

instance : Algebra ℝ (DD D e) := inferInstanceAs (Algebra ℝ D)

set_option synthInstance.maxHeartbeats 30000 in
instance CAlg : Algebra ℂ (DD D e) where
  smul z (d : D) := (e.symm z).1 * d
  toFun z := e.symm z|>.1
  map_one' := by simp only [map_one, OneMemClass.coe_one]
  map_mul' := by simp only [map_mul, Subring.coe_mul, implies_true]
  map_zero' := by simp only [map_zero, ZeroMemClass.coe_zero]
  map_add' := fun x y => by simp only [map_add, Subring.coe_add]
  commutes' z d := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    exact Subring.mem_center_iff.1 (e.symm z).2 d |>.symm
  smul_def' := by
    intro z d
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rfl

-- -- instance (e : Subring.center D ≃+* ℂ) : Module (Subring.center D) ℂ where
-- --   smul d z := e d * z
-- --   one_smul :=
-- --   mul_smul := _
-- --   smul_zero := _
-- --   smul_add := _
-- --   add_smul := _
-- --   zero_smul := _

-- -- set_option synthInstance.maxHeartbeats 80000 in
-- lemma complex_centre_equiv_complex (e : Subring.center (DD D) ≃ₐ[ℝ] ℂ) [FiniteDimensional ℝ (DD D)]:
--     Nonempty ((DD D) ≃ₐ[ℝ] ℂ) := by
--   haveI := FiniteDimensional.right ℝ ℂ (DD D)
--   exact DequivC

end isoC
variable [Algebra ℝ D] [hD : IsCentralSimple ℝ D] (k : SubField ℝ D) (hk : IsMaximalSubfield ℝ D k)
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
    unfold Complex.ofReal'
    rw [← smul_eq_mul, show (⟨r • 1, 0⟩ : ℂ) = r • ⟨1, 0⟩ by
      apply Complex.ext
      · simp only [smul_eq_mul, mul_one, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, mul_zero,
        Complex.ofReal_im, mul_one, add_zero]]
    rw [_root_.map_smul, show ⟨1, 0⟩ = (1 : ℂ) by rfl, _root_.map_one]

omit hD [FiniteDimensional ℝ D] in
@[simp]
lemma f_apply (x : k) : f k e x = e.symm (conj (e x)) := rfl

omit hD [FiniteDimensional ℝ D] in
lemma f_apply_apply (z : ℂ): f k e (e.symm z) = e.symm (conj z) := by
  rw [f_apply]
  congr
  exact AlgEquiv.apply_symm_apply e z

open Finsupp in
lemma f_is_conjugation : ∃ (x : D), ∀ (z : k), (x⁻¹) * (f k e z) * x = k.val z
    ∧ x^2 ∈ (algebraMap ℝ D).range := by
  obtain ⟨x, hx⟩ := SkolemNoether' ℝ D k k.val (k.val.comp (f k e))
  use x
  intro z
  have hx2 := hx
  specialize hx z
  constructor
  · apply_fun fun y => ↑x⁻¹ * y * ↑x at hx
    nth_rw 2 [mul_assoc, mul_assoc] at hx
    simp only [Units.val_inv_eq_inv_val, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, mul_one, IsUnit.inv_mul_cancel_left] at hx
    exact hx
  · have x2_is_central : x.1^2 ∈ Subalgebra.center ℝ D := by
      have x2_commutes_K : ∀ (y : k), x.1^2 * k.val y = k.val y * x.1^2 := by
        intro y
        specialize hx2 y
        simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
          Units.val_inv_eq_inv_val] at hx2
        erw [Subtype.ext_iff.1 (f_apply k e y)] at hx2
        apply_fun (x.1 * · * x.1⁻¹) at hx2
        erw [← mul_assoc, ← mul_assoc, mul_assoc (x.1 * x.1 * k.val y) x.1⁻¹ x.1⁻¹] at hx2
        have : k.val y = (x.1 * x.1) * k.val y * (x.1⁻¹ * x.1⁻¹) := by
          sorry
        rw [← pow_two] at this
        apply_fun (· * x.1 * x.1) at this
        erw [← mul_assoc, mul_assoc (x.1^2 * k.val y * x.1⁻¹),
          inv_mul_cancel₀ (by simp_all only [AlgHom.coe_comp,
            Subalgebra.coe_val, Function.comp_apply,
            Units.val_inv_eq_inv_val, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
            IsUnit.inv_mul_cancel, mul_one, IsUnit.inv_mul_cancel_right]), mul_one, mul_assoc,
          mul_assoc (x.1^2 * _) _ _, inv_mul_cancel₀ (by simp_all only [AlgHom.coe_comp,
            Subalgebra.coe_val, Function.comp_apply, Units.val_inv_eq_inv_val, isUnit_iff_ne_zero,
            ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel, mul_one]),
          ← pow_two, mul_one] at this
        exact this.symm
      by_contra! hxx
      have indep : LinearIndependent ℝ ![(1 : D), x.1^2] := by
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

      have xink : x.1^2 ∈ k := by
        sorry

      have indep' : LinearIndependent ℝ (M := k) ![1, ⟨x.1^2, xink⟩] := by

        sorry

      have IsBasis : Basis (Fin (Nat.succ 0).succ) ℝ k :=
        .mk (M := k) (v := ![1, ⟨x.1^2, xink⟩]) indep' $ by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons,
          Matrix.range_empty, Set.union_empty, Set.union_singleton, top_le_iff]
        have : FiniteDimensional.finrank ℝ (Submodule.span ℝ
          {⟨x.1^2, xink⟩, (1 : k)})= 2 := by
          apply LinearIndependent.span_eq_top_of_card_eq_finrank' at indep'
          simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Fintype.card_fin,
            Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton] at indep'
          have : 2 = FiniteDimensional.finrank ℝ k := by
            rw [LinearEquiv.finrank_eq e.toLinearEquiv]
            symm
            exact Complex.finrank_real_complex
          apply indep' at this
          rw [this, finrank_top]
          exact (show FiniteDimensional.finrank ℝ k = 2 by
              rw [LinearEquiv.finrank_eq e.toLinearEquiv]
              exact Complex.finrank_real_complex
          )
        have eq := Submodule.topEquiv.finrank_eq.trans $
          e.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex
        have le : Submodule.span _ {⟨x.1 ^ 2, xink⟩, (1 : k)} ≤
          (⊤ : Submodule ℝ k) := by exact fun ⦃x_1⦄ a ↦ trivial
        exact FiniteDimensional.eq_of_le_of_finrank_eq le $ this.trans eq.symm

      have xink' : x.1 ∈ k := sorry
      sorry
    change _ ∈ (⊥ : Subalgebra ℝ D)
    rw [← IsCentralSimple.center_eq ℝ D]; exact x2_is_central

open scoped algebraMap in
abbrev V : Set D := {x | ∃ r : ℝ, r ≤ 0 ∧ x^2 = (r : D)}

set_option linter.unusedSectionVars false in
lemma V_def (x : D) : x ∈ V ↔ ∃ r : ℝ, r ≤ 0 ∧ x^2 = (algebraMap ℝ D) r := by
    exact Set.mem_def

lemma real_sq_in_R_or_V (x : D) : x^2 ∈ (algebraMap ℝ D).range → x ∈ (algebraMap ℝ D).range ∨ x ∈ V := by
  rintro ⟨r, hr⟩
  if h'' : x ∈ V then
    exact Or.inr h''
  else
    left
    simp only [V_def, not_exists, not_and] at h''
    have : r > 0 := by
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

theorem rank_4_iso_H : FiniteDimensional.finrank ℝ D = 4 → Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  intro h'
  sorry

theorem rank_2_D_iso_C : FiniteDimensional.finrank ℝ D = 2 → Nonempty (D≃ₐ[ℝ] ℂ) := sorry
