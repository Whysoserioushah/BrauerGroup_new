import BrauerGroup.QuatBasic
import BrauerGroup.CentralSimple
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Real.Sqrt

suppress_compilation

variable (n : ℕ)
variable {D : Type} [DivisionRing D] [Algebra ℝ D]
variable (x y : D)

open Quaternion TensorProduct BigOperators Classical FiniteDimensional

local notation x " ∘ " y => x * y + y * x

open scoped algebraMap in
def V : Set D := {x | ∃ r : ℝ, r ≤ 0 ∧ x^2 = (r : D)}

lemma V_def (x : D) : x ∈ V ↔ ∃ r : ℝ, r ≤ 0 ∧ x^2 = (algebraMap ℝ D) r := by
    exact Set.mem_def

lemma field_over_R_iso_C (F : Type) [Field F] [Algebra ℝ F] (h : finrank ℝ F = 2) : Nonempty (F ≃ₐ[ℝ] ℂ) := by
    haveI : FiniteDimensional ℝ F := .of_finrank_eq_succ h
    haveI : Algebra.IsAlgebraic ℝ F := Algebra.IsAlgebraic.of_finite _ _
    haveI : Algebra.IsAlgebraic ℝ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans (K := ℝ) (L := F)
    let ι₀ : (AlgebraicClosure F) →ₐ[ℝ] ℂ :=
        IsAlgClosed.lift (R := ℝ) (M := ℂ) (S := AlgebraicClosure F)
    let ι₁ : F →ₐ[ℝ] AlgebraicClosure F :=
        IsScalarTower.toAlgHom ℝ F (AlgebraicClosure F)
    exact .intro <| AlgEquiv.ofBijective (ι₀.comp ι₁) <|
        LinearMap.linearEquivOfInjective (ι₀.comp ι₁).toLinearMap (RingHom.injective _)
            (h.trans Complex.finrank_real_complex.symm) |>.bijective

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

lemma lemma1 (x : D) : ∃ (α : ℝ), x^2 + α • x ∈ (algebraMap ℝ D).range ∧ x + (α/2) • 1 ∈ V := by sorry

lemma inner_prod_is_real (u v : D) : u ∈ V ∧ v ∈ V → (u ∘ v) ∈ (algebraMap ℝ D).range := sorry

theorem rank_4_iso_H : FiniteDimensional.finrank ℝ D = 4 → Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
    intro h'
    sorry

theorem rank_2_D_iso_C : FiniteDimensional.finrank ℝ D = 2 → Nonempty (D≃ₐ[ℝ] ℂ) := sorry

set_option synthInstance.maxHeartbeats 100000 in
theorem rank_1_D_iso_R : FiniteDimensional.finrank ℝ D = 1 → Nonempty (D≃ₐ[ℝ] ℝ) := fun h => by
    have h' := Subalgebra.finrank_eq_one_iff (F := ℝ) (S := (⊤ : Subalgebra ℝ D))
    have : FiniteDimensional.finrank ℝ (⊤ : Subalgebra ℝ D) = 1 := by
        simp_all only [Subalgebra.finrank_eq_one_iff, Subalgebra.bot_eq_top_of_finrank_eq_one]
    exact ⟨Subalgebra.topEquiv.symm.trans $ Subalgebra.equivOfEq _ _
        (h'.1 this)|>.trans $ Algebra.botEquiv ℝ D⟩
