import BrauerGroup.QuatBasic
import BrauerGroup.BrauerGroup

suppress_compilation

variable (D : Type) [Ring D] [Algebra ℚ D] [h : IsCentralSimple ℚ D]
    [FiniteDimensional ℚ D] (hD : FiniteDimensional.finrank ℚ D = 4)

open Quaternion TensorProduct BigOperators Classical

variable (a b : ℚ)

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

instance Gen_Quat_is_CSA [NeZero a] [NeZero b] : IsCentralSimple ℚ (ℍ[ℚ, a, b]) where
  is_central := by
    intro z hz
    rw [Algebra.mem_bot]
    rw [Subalgebra.mem_center_iff] at hz
    induction z with
    | mk α β γ δ =>
    have eq1 := hz ⟨0,1,0,0⟩
    simp only [QuaternionAlgebra.mk_mul_mk, zero_mul, mul_one, zero_add, mul_zero, add_zero,
      sub_zero, one_mul, zero_sub, QuaternionAlgebra.mk.injEq, eq_neg_self_iff, mul_eq_zero,
      true_and] at eq1
    rw [eq1.2, eq1.1.resolve_left (NeZero.ne' a).symm]
    have eq2 := hz ⟨0,0,1,0⟩
    simp only [QuaternionAlgebra.mk_mul_mk, zero_mul, mul_zero, add_zero, mul_one, zero_add,
      sub_zero, zero_sub, one_mul, sub_self, QuaternionAlgebra.mk.injEq, neg_eq_self_iff,
      mul_eq_zero, true_and] at eq2
    rw [eq2.2]
    have eq3 := hz ⟨0,0,0,1⟩
    simp only [QuaternionAlgebra.mk_mul_mk, zero_mul, mul_zero, add_zero, mul_one, zero_sub,
      sub_self, zero_add, one_mul, sub_zero, QuaternionAlgebra.mk.injEq, eq_neg_self_iff,
      mul_eq_zero, neg_eq_self_iff, and_true, true_and] at eq3
    exact ⟨α, rfl⟩
  is_simple := Quat.quat_isSimple a b (NeZero.ne' a).symm (NeZero.ne' b).symm

/-- prove 1 ⊗ 1, 1 ⊗ i, 1 ⊗ j, 1 ⊗ k is a basis of ℂ ⊗ ℍ. -/
theorem complex_tensor_eqv [NeZero a] [NeZero b] :
    Nonempty (ℂ ⊗[ℚ] ℍ[ℚ, a, b] ≃ₐ[ℂ] ℍ[ℂ, a, b]) := by
  sorry

/-- use exist non-trvial but norm-zero element 1 + (1/√a) i -/
def complex_quat_eqv (c d : ℂ) [NeZero c] [NeZero d]: ℍ[ℂ, c, d] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Quat.not_div_iff_iso_matrix c d (NeZero.ne' c).symm (NeZero.ne' d).symm).2
  (by sorry)|>.some

variable (E : Type) [Ring E] [Algebra ℂ E] [h : IsCentralSimple ℂ E]
    [FiniteDimensional ℂ E] (hD : FiniteDimensional.finrank ℂ E = 4)

/-- by prove {1, i, j, k} in E is indeed a basis of E read FiniteDimensional.finBasis -/
theorem CSA_is_quat : ∃(a b : ℂ) (_ : NeZero a) (_ : NeZero b),
    Nonempty (E ≃ₐ[ℂ] ℍ[ℂ, a, b]) := sorry
