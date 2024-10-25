import BrauerGroup.QuatBasic
import BrauerGroup.CentralSimple
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

suppress_compilation

variable (n : ℕ)
variable (D : Type) [DivisionRing D] [Algebra ℝ D]
variable (x y : D)

open Quaternion TensorProduct BigOperators Classical

local notation x " ∘ " y => x * y + y * x

#check (⊥ : Subalgebra ℝ D)
-- ⊥ = algebraMap ℝ D|>.range
def V : Set D := {x | x^2 ∈ (algebraMap ℝ D).range ∧ x ≤ 0}

lemma real_sq_in_R_or_V (x : D) : x^2 ∈ ⊥ → x ∈ ⊥ ∨ x ∈ V := by sorry

lemma inner_prod_is_real (u v : D) : u ∈ V ∧ v ∈ V → (u ∘ v) ∈ (algebraMap ℝ D).range := sorry

theorem rank_4_D_iso_H : FiniteDimensional.finrank ℝ D = 4 → Nonempty (D≃ₐ[ℝ] ℍ[ℝ]) := sorry

theorem rank_2_D_iso_C : FiniteDimensional.finrank ℝ D = 2 → Nonempty (D≃ₐ[ℝ] ℂ) := sorry


theorem rank_1_D_iso_R : FiniteDimensional.finrank ℝ D = 1 → Nonempty (D≃ₐ[ℝ] ℝ) := fun h => by
    have hh := Subalgebra.finrank_eq_one_iff (F := ℝ) (S := (⊤ : Subalgebra ℝ D))
    have : FiniteDimensional.finrank ℝ (⊤ : Subalgebra ℝ D) = 1 := by
        simp_all only [Subalgebra.finrank_eq_one_iff, Subalgebra.bot_eq_top_of_finrank_eq_one]
    exact ⟨Subalgebra.topEquiv.symm.trans $ Subalgebra.equivOfEq _ _
        (hh.1 this)|>.trans $ Algebra.botEquiv ℝ D⟩
universe u
