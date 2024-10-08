import BrauerGroup.QuatBasic
import BrauerGroup.CentralSimple
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

suppress_compilation

variable (D : Type) [Ring D] [Algebra ℚ D] [h : IsCentralSimple ℚ D]

open Quaternion TensorProduct BigOperators Classical

variable (a b : ℚ)
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V]

lemma dim_eq : FiniteDimensional.finrank K V = FiniteDimensional.finrank L (L ⊗[K] V) := by
  let b := FiniteDimensional.finBasis K V
  let b' := Algebra.TensorProduct.basis L b
  rw [FiniteDimensional.finrank_eq_card_basis b, FiniteDimensional.finrank_eq_card_basis b']

theorem tensor_C_is_CSA : IsCentralSimple ℂ (ℂ ⊗[ℚ] D) := IsCentralSimple.baseChange ℚ D ℂ

variable [FiniteDimensional ℚ D]
instance : FiniteDimensional ℂ (ℂ ⊗[ℚ] D) := Module.Finite.base_change ℚ ℂ D

omit h in
lemma finrank_four (hD : FiniteDimensional.finrank ℚ D = 4):
    FiniteDimensional.finrank ℂ (ℂ ⊗[ℚ] D) = 4 := (dim_eq ℚ ℂ D).symm.trans hD

instance Gen_Quat_is_CSA [NeZero a] [NeZero b] : IsCentralSimple ℚ (ℍ[ℚ, a, b]) where
  is_central := by
    intro z hz
    rw [Algebra.mem_bot]
    rw [Subalgebra.mem_center_iff] at hz
    induction z with
    | mk α β γ δ =>
    have eq1 := hz ⟨0,1,0,0⟩
    simp only [QuaternionAlgebra.mk_mul_mk, zero_mul, mul_one, zero_add, mul_zero, add_zero,
      sub_zero, one_mul, zero_sub, QuaternionAlgebra.mk.injEq, true_and] at eq1
    have eq2 := hz ⟨0,0,1,0⟩
    simp only [QuaternionAlgebra.mk_mul_mk, zero_mul, mul_zero, add_zero, mul_one, zero_add,
      sub_zero, zero_sub, one_mul, sub_self, QuaternionAlgebra.mk.injEq, true_and] at eq2
    -- rw [eq2.2]
    have eq3 := hz ⟨0,0,0,1⟩
    simp only [QuaternionAlgebra.mk_mul_mk, zero_mul, mul_zero, add_zero, mul_one, zero_sub,
      sub_self, zero_add, one_mul, sub_zero, QuaternionAlgebra.mk.injEq, and_true, true_and] at eq3
    refine ⟨α, ?_⟩
    simp only [QuaternionAlgebra.coe_algebraMap]
    ext
    · rfl
    · exact CharZero.eq_neg_self_iff.1 eq2.2.symm|>.symm
    · exact CharZero.eq_neg_self_iff.1 eq1.2 |>.symm
    · have : a = 0 ∨ δ = 0 := eq_zero_or_eq_zero_of_mul_eq_zero $ CharZero.eq_neg_self_iff.1 eq1.1
      simp only [NeZero.ne a, false_or] at this ⊢
      exact this.symm
  is_simple := Quat.quat_isSimple a b (NeZero.ne' a).symm (NeZero.ne' b).symm

def Quat_to_tensor [NeZero a] [NeZero b] : ℍ[ℂ, a, b] →ₐ[ℂ] ℂ ⊗[ℚ] ℍ[ℚ, a, b] :=
  QuaternionAlgebra.lift
  {
    i := (1 : ℂ) ⊗ₜ ⟨0,1,0,0⟩,
    j := (1 : ℂ) ⊗ₜ ⟨0,0,1,0⟩,
    k := (1 : ℂ) ⊗ₜ ⟨0,0,0,1⟩,
    i_mul_i := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        QuaternionAlgebra.mk_mul_mk, mul_zero, zero_add, add_zero, sub_zero, sub_self,
        Algebra.TensorProduct.one_def]
      rw [show ⟨a, 0, 0, 0⟩ = a • (1 : ℍ[ℚ, a, b]) by ext <;> simp]
      rw [tmul_smul]; congr
    j_mul_j := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        QuaternionAlgebra.mk_mul_mk, mul_zero, zero_add, add_zero, sub_zero, sub_self,
        Algebra.TensorProduct.one_def]
      rw [show ⟨b, 0, 0, 0⟩ = b • (1 : ℍ[ℚ, a, b]) by ext <;> simp]
      rw [tmul_smul]; congr
    i_mul_j := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        QuaternionAlgebra.mk_mul_mk, mul_zero, zero_add, add_zero, sub_zero, sub_self,
        Algebra.TensorProduct.one_def]
    j_mul_i := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, QuaternionAlgebra.mk_mul_mk,
        mul_zero, add_zero, sub_self, zero_sub]
      rw[show (⟨0, 0, 0, -1⟩:ℍ[ℚ, a, b]) = -1 • ⟨0, 0, 0, 1⟩ by ext <;> simp]
      rw [tmul_smul, neg_one_zsmul]
  }
/-- prove 1 ⊗ 1, 1 ⊗ i, 1 ⊗ j, 1 ⊗ k is a basis of ℂ ⊗ ℍ. -/
lemma Injective_Quat_to_tensor [NeZero a] [NeZero b]: Function.Injective (Quat_to_tensor a b) := by
  change Function.Injective (Quat_to_tensor a b).toRingHom
  have H := TwoSidedIdeal.IsSimpleOrder.iff_eq_zero_or_injective ℍ[ℂ , a, b] |>.1 $
    Quat.quat_isSimple (a:ℂ) (b:ℂ) (by aesop) (by aesop)
  specialize H (Quat_to_tensor a b).toRingHom
  refine H.resolve_left fun rid => ?_
  rw [eq_top_iff, TwoSidedIdeal.le_iff] at rid
  specialize @rid 1 ⟨⟩
  simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, TwoSidedIdeal.mem_ker, _root_.map_one,
    one_ne_zero] at rid

lemma Surjective_Quat_to_tensor [NeZero a] [NeZero b]:
    Function.Surjective (Quat_to_tensor a b) := by
  change Function.Surjective (Quat_to_tensor a b).toLinearMap
  rw [← LinearMap.range_eq_top]
  have eq := (Quat_to_tensor a b).toLinearMap.finrank_range_add_finrank_ker
  rw [QuaternionAlgebra.finrank_eq_four, LinearMap.ker_eq_bot.2 (Injective_Quat_to_tensor a b),
    finrank_bot, add_zero] at eq
  apply Submodule.eq_top_of_finrank_eq
  · rw [eq]; symm; exact (finrank_four ℍ[ℚ,a,b] (QuaternionAlgebra.finrank_eq_four a b))

theorem complex_tensor_eqv [NeZero a] [NeZero b] :
    Nonempty (ℍ[ℂ, a, b] ≃ₐ[ℂ] ℂ ⊗[ℚ] ℍ[ℚ, a, b]) :=
  ⟨AlgEquiv.ofBijective (Quat_to_tensor a b)
  ⟨Injective_Quat_to_tensor _ _, Surjective_Quat_to_tensor _ _⟩ ⟩

/-- use exist non-trvial but norm-zero element 1 + (1/√a) i -/
def complex_quat_eqv (c d : ℂ) [NeZero c] [NeZero d]: ℍ[ℂ, c, d] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Quat.not_div_iff_iso_matrix c d (NeZero.ne' c).symm (NeZero.ne' d).symm).2
  (by sorry)|>.some

variable (E : Type) [Ring E] [Algebra ℂ E] [h : IsCentralSimple ℂ E]
    [FiniteDimensional ℂ E] (hD : FiniteDimensional.finrank ℂ E = 4)

/-- by prove {1, i, j, k} in E is indeed a basis of E read FiniteDimensional.finBasis -/
theorem CSA_is_quat : ∃(a b : ℂ) (_ : NeZero a) (_ : NeZero b),
    Nonempty (E ≃ₐ[ℂ] ℍ[ℂ, a, b]) := sorry
