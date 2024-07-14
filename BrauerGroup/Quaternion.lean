import Mathlib.Algebra.QuaternionBasis
import BrauerGroup.CentralSimple
import BrauerGroup.QuatBasic
import BrauerGroup.CentralSimple

variable (D : Type) [Ring D] [Algebra ℚ D] [h : IsCentralSimple ℚ D]
    [FiniteDimensional ℚ D] (hD : FiniteDimensional.finrank ℚ D = 4)
open Quaternion TensorProduct BigOperators Classical
--instance isoisoiso (h1: Module.rank ℚ D = 4): Nonempty (D ≃ₐ[ℚ] QuaternionAlgebra ℚ a b):= by sorry

variable (a b : ℚ)

theorem Quat_is_CSA: IsCentralSimple ℚ (ℍ[ℚ]) where
  is_central z hz := by
    rw [@Subalgebra.mem_center_iff] at hz
    let eq2 := congrArg Quaternion.imI (hz ⟨0,0,1,0⟩)
    let eq3 := congrArg Quaternion.imJ (hz ⟨0,0,0,1⟩)
    let eq4 := congrArg Quaternion.imK (hz ⟨0,1,0,0⟩)
    simp only [mul_imI, zero_mul, add_zero, one_mul, zero_add, sub_zero, mul_zero, mul_one,
      zero_sub, eq_neg_self_iff, mul_imJ, sub_self, mul_imK] at eq2 eq3 eq4
    refine ⟨_, id (ext z (↑z.re) rfl eq3 eq4 eq2).symm⟩

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (V : Type) [AddCommGroup V] [Module K V] [Module.Finite K V]

lemma dim_eq : FiniteDimensional.finrank K V = FiniteDimensional.finrank L (L ⊗[K] V) := by
  let b := FiniteDimensional.finBasis K V
  let b' := Algebra.TensorProduct.basis L b
  rw [FiniteDimensional.finrank_eq_card_basis b, FiniteDimensional.finrank_eq_card_basis b']

theorem tensor_C_is_CSA : IsCentralSimple ℂ (ℂ ⊗[ℚ] D) := IsCentralSimple.baseChange ℚ D ℂ

instance : FiniteDimensional ℂ (ℂ ⊗[ℚ] D) := Module.Finite.base_change ℚ ℂ D

lemma finrank_four : FiniteDimensional.finrank ℂ (ℂ ⊗[ℚ] D) = 4 :=
  (dim_eq ℚ ℂ D).symm.trans hD

-- strictly speaking, this is wrong, because ℍ[ℚ, 0, 0] is not simple.
theorem Gen_Quat_is_CSA: IsCentralSimple ℚ (ℍ[ℚ, a, b]) where
  is_central := sorry
  is_simple := sorry
    -- if hH : ∀(x : ℍ[ℚ, a, b]), x = 0 ∨ (∃(y : _), y * x = 1 ∧ x * y = 1) then
    --   haveI : DivisionRing ℍ[ℚ, a, b] :=
    --   { inv := fun x ↦ if hx : x = 0 then 0
    --       else (by change _ ≠ _ at hx; have h1 := hH x ; simp only [hx, false_or] at h1 ;
    --                 choose y hy using h1 ; exact y)
    --     mul_inv_cancel := fun x hx ↦ by simp only [hx, ↓reduceDIte, ne_eq, id_eq] ;sorry
    --     inv_zero := by simp only [↓reduceDIte]
    --     nnqsmul := _
    --     qsmul := _
    --   }
    --   --exact @instIsSimpleOrderRingCon_fLTJujian02 ℍ[ℚ, a, b] this
    --   sorry
    -- else
    -- simp only [not_forall, not_or, not_exists] at hH
    -- obtain ⟨x, hx1, hx2⟩ := hH
    -- change x ≠ 0 at hx1
    -- have hy : ∀(y : _), y * x ≠ 1 ∨ x * y ≠ 1 := by tauto
    -- obtain ⟨iso⟩ := Quat.not_div_iff_iso_matrix a b|>.2 ⟨x, ⟨hx1, hy⟩⟩
    -- exact (_root_.AlgEquiv.isCentralSimple iso.symm).2

theorem isoisoisoisoisoiso:
    Nonempty (ℂ ⊗[ℚ] D  ≃ₐ[ℂ] ℍ[ℂ]) := by

  sorry

variable (K E : Type) [Field K] [Ring E] [Algebra K E] [h : IsCentralSimple K E]
    [FiniteDimensional K E] (hD : FiniteDimensional.finrank K E = 4)

theorem CSA_is_quat : ∃(a b : K), Nonempty (E ≃ₐ[K] ℍ[K, a, b]) := sorry
