import BrauerGroup.QuatBasic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import BrauerGroup.Subfield.Subfield

suppress_compilation

open Quaternion TensorProduct BigOperators Classical FiniteDimensional

variable {D : Type} [DivisionRing D] [Algebra ℝ D]

section prerequisites

set_option synthInstance.maxHeartbeats 40000 in
theorem rank_1_D_iso_R [Algebra ℝ D] : FiniteDimensional.finrank ℝ D = 1 → Nonempty (D≃ₐ[ℝ] ℝ) := fun h => by
  have h' := Subalgebra.finrank_eq_one_iff (F := ℝ) (S := (⊤ : Subalgebra ℝ D))
  have : FiniteDimensional.finrank ℝ (⊤ : Subalgebra ℝ D) = 1 := by
    simp_all only [Subalgebra.finrank_eq_one_iff, Subalgebra.bot_eq_top_of_finrank_eq_one]
  exact ⟨Subalgebra.topEquiv.symm.trans $ Subalgebra.equivOfEq _ _
    (h'.1 this)|>.trans $ Algebra.botEquiv ℝ D⟩

lemma RealExtension_is_RorC (K : Type) [Field K] [Algebra ℝ K] [FiniteDimensional ℝ K]: Nonempty (K ≃ₐ[ℝ] ℝ) ∨ Nonempty (K ≃ₐ[ℝ] ℂ) := by
  sorry

lemma field_over_R_iso_C (K : Type) [Field K] [Algebra ℝ K] (h : finrank ℝ K = 2) : Nonempty (K ≃ₐ[ℝ] ℂ) := by
    haveI : FiniteDimensional ℝ K := .of_finrank_eq_succ h
    haveI : Algebra.IsAlgebraic ℝ K := Algebra.IsAlgebraic.of_finite _ _
    haveI : Algebra.IsAlgebraic ℝ (AlgebraicClosure K) := Algebra.IsAlgebraic.trans (K := ℝ) (L := K)
    let ι₀ : (AlgebraicClosure K) →ₐ[ℝ] ℂ :=
        IsAlgClosed.lift (R := ℝ) (M := ℂ) (S := AlgebraicClosure K)
    let ι₁ : K →ₐ[ℝ] AlgebraicClosure K :=
        IsScalarTower.toAlgHom ℝ K (AlgebraicClosure K)
    exact .intro <| AlgEquiv.ofBijective (ι₀.comp ι₁) <|
        LinearMap.linearEquivOfInjective (ι₀.comp ι₁).toLinearMap (RingHom.injective _)
            (h.trans Complex.finrank_real_complex.symm) |>.bijective

lemma DequivC [Algebra ℂ D] [FiniteDimensional ℂ D]:
    Nonempty (D ≃ₐ[ℂ] ℂ) := by
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed ℂ D
  haveI : NeZero n := ⟨hn⟩
  exact Wedderburn_Artin_uniqueness₀ ℂ D 1 n D (BrauerGroup.dim_one_iso D).symm ℂ iso

variable (D) in
def DD := D

instance : DivisionRing (DD D) := inferInstanceAs (DivisionRing D)

instance : Algebra ℝ (DD D) := inferInstanceAs (Algebra ℝ D)

instance CAlg (e : Subring.center (DD D) ≃ₐ[ℝ] ℂ) : Algebra ℂ (DD D) where
  smul z d := e.symm z • d
  toFun z := e.symm z|>.1
  map_one' := by simp only [map_one, OneMemClass.coe_one]
  map_mul' := by simp only [map_mul, Subring.coe_mul, implies_true]
  map_zero' := by simp only [map_zero, ZeroMemClass.coe_zero]
  map_add' := fun x y => by sorry
  commutes' z d := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    -- obtain ⟨x, hx⟩ := e.symm z
    exact Subring.mem_center_iff.1 (e.symm z).2 d |>.symm
  smul_def' := by
    intro z d
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rfl

-- instance (e : Subring.center D ≃+* ℂ) : Module (Subring.center D) ℂ where
--   smul d z := e d * z
--   one_smul :=
--   mul_smul := _
--   smul_zero := _
--   smul_add := _
--   add_smul := _
--   zero_smul := _

-- set_option synthInstance.maxHeartbeats 80000 in
lemma complex_centre_equiv_complex (e : Subring.center (DD D) ≃ₐ[ℝ] ℂ) [FiniteDimensional ℝ (DD D)]:
    Nonempty ((DD D) ≃ₐ[ℝ] ℂ) := by
  haveI := FiniteDimensional.right ℝ ℂ (DD D)
  exact DequivC

end prerequisites

variable [Algebra ℝ D]

open scoped algebraMap in
abbrev V : Set D := {x | ∃ r : ℝ, r ≤ 0 ∧ x^2 = (r : D)}

lemma V_def (x : D) : x ∈ V ↔ ∃ r : ℝ, r ≤ 0 ∧ x^2 = (algebraMap ℝ D) r := by
    exact Set.mem_def



-- lemma complex_centre_equiv_complex (D)
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
