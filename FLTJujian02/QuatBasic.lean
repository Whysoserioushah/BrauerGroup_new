import Mathlib.Algebra.QuaternionBasis
import Mathlib.Tactic

suppress_compilation

namespace Quat

variable (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)

open Quaternion Classical Matrix

def normQuat : ℍ[ℚ, a, b] →*₀ ℚ where
  toFun a := a * star a|>.re
  map_zero' := by simp only [star_zero, mul_zero, QuaternionAlgebra.zero_re]
  map_one' := by simp only [star_one, mul_one, QuaternionAlgebra.one_re]
  map_mul' x y := by
    simp only [StarMul.star_mul]; nth_rw 1 [← mul_assoc, (mul_assoc _ _ (star y)),
      QuaternionAlgebra.mul_star_eq_coe, mul_assoc, QuaternionAlgebra.coe_mul_eq_smul,
      mul_smul_comm, QuaternionAlgebra.smul_re, smul_eq_mul, mul_comm]

theorem invertible_iff (x : ℍ[ℚ, a, b]) : (∃ y : ℍ[ℚ, a, b], x * y = 1 ∧ y * x = 1) ↔
    normQuat a b x ≠ 0 := by
  constructor
  · intro ⟨y, h1, _⟩
    by_contra hx
    have hxy1 : normQuat a b (x * y) = 0 := by simp only [map_mul _, hx, zero_mul]
    have : normQuat a b (x * y) = 1 := by rw [h1]; simp only [(normQuat a b).map_one]
    exact one_ne_zero $ this.symm.trans hxy1
  · intro hx
    use (normQuat a b x)⁻¹ • star x ; constructor
    · rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel hx]; rfl
    · rw [Algebra.smul_mul_assoc, star_comm_self', QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel hx]; rfl

theorem non_zero_norm_iff_div :
    (∀(x : ℍ[ℚ, a, b]), x ≠ 0 → (∃(y : ℍ[ℚ, a, b]), y * x = 1 ∧ x * y = 1)) ↔
    ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0 := by
  constructor
  · intro hD x ;constructor
    · intro hx
      by_contra! hx'
      obtain ⟨y, ⟨hy, hyy⟩⟩ := hD x hx'
      have := invertible_iff a b x |>.1 ⟨y, ⟨hyy, hy⟩⟩
      exact this hx
    · intro hx; simp only [hx]; exact map_zero _
  · intro hD' x hx
    use (normQuat a b x)⁻¹ • star x
    constructor
    · rw [Algebra.smul_mul_assoc, star_comm_self', QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel (by by_contra! hxx ; exact hx ((hD' x).1 hxx))]; rfl
    · rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe]
      rw [show (x * star x).re = normQuat a b x from rfl, QuaternionAlgebra.smul_coe,
        inv_mul_cancel (by by_contra! hxx ; exact hx ((hD' x).1 hxx))]; rfl

-- instance IsDivisionRing (hx : ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0) :
--     DivisionRing (ℍ[ℚ, a, b]) where
--       one_mul := one_mul
--       mul_one := mul_one
--       natCast_succ n := Nat.cast_add_one n
--       sub_eq_add_neg a b := sub_eq_add_neg a b
--       zsmul := fun z x ↦ z • x
--       add_left_neg x := neg_add_self x
--       inv x := (normQuat a b x)⁻¹ • star x
--       div := fun x y => x * ((normQuat a b y)⁻¹ • star y)
--       mul_inv_cancel x := by
--         intro hxx; simp only [Algebra.mul_smul_comm]
--         rw [QuaternionAlgebra.mul_star_eq_coe, show (x * star x).re = normQuat a b x from rfl,
--           QuaternionAlgebra.smul_coe,
--           inv_mul_cancel (by by_contra! hx' ; exact hxx $ (hx x).1 hx')]; rfl
--       inv_zero := by simp only [map_zero, inv_zero, star_zero, smul_zero]
--       nnqsmul := _
--       qsmul := _

--- !!Might be wrong don't try to write this
def equiv_to_square (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0):
    ℍ[ℚ, a, b] →ₐ[ℚ] ℍ[ℚ, u^2 * a, v^2 * b] :=
  QuaternionAlgebra.lift $
    { i := ⟨0, u⁻¹, 0, 0⟩
      j := ⟨0, 0, v⁻¹, 0⟩
      k := ⟨0, 0, 0, u⁻¹ * v⁻¹⟩
      i_mul_i := by
        ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, pow_two, zero_add,
        add_zero, sub_zero, zero_mul, sub_self, QuaternionAlgebra.smul_re, QuaternionAlgebra.one_re,
        smul_eq_mul, mul_one, QuaternionAlgebra.smul_imI, QuaternionAlgebra.one_imI,
        QuaternionAlgebra.smul_imJ, QuaternionAlgebra.one_imJ, QuaternionAlgebra.smul_imK,
        QuaternionAlgebra.one_imK] ; field_simp
      j_mul_j := by
        ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero,
        sub_self, zero_mul, QuaternionAlgebra.smul_re, QuaternionAlgebra.one_re, smul_eq_mul,
        mul_one, QuaternionAlgebra.smul_imI, QuaternionAlgebra.one_imI, QuaternionAlgebra.smul_imJ,
        QuaternionAlgebra.one_imJ, QuaternionAlgebra.smul_imK, QuaternionAlgebra.one_imK, pow_two]
        field_simp
      i_mul_j := by
        ext <;>
        simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, pow_two, add_zero, zero_mul,
          sub_self, zero_add, sub_zero]
      j_mul_i := by
        ext <;>
        simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, pow_two, zero_mul, add_zero,
          sub_self, zero_sub, QuaternionAlgebra.neg_mk, neg_zero, mul_comm] }

def square_to_equiv (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0):
    ℍ[ℚ, u^2 * a, v^2 * b] →ₐ[ℚ] ℍ[ℚ, a, b] :=
  QuaternionAlgebra.lift $
    { i := ⟨0, u, 0, 0⟩
      j := ⟨0, 0, v, 0⟩
      k := ⟨0, 0, 0, u * v⟩
      i_mul_i := by
        ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, pow_two, zero_add,
        add_zero, sub_zero, zero_mul, sub_self, QuaternionAlgebra.smul_re, QuaternionAlgebra.one_re,
        smul_eq_mul, mul_one, QuaternionAlgebra.smul_imI, QuaternionAlgebra.one_imI,
        QuaternionAlgebra.smul_imJ, QuaternionAlgebra.one_imJ, QuaternionAlgebra.smul_imK,
        QuaternionAlgebra.one_imK, mul_comm]; exact mul_rotate' u a u
      j_mul_j := by
        ext <;> simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero,
        sub_self, zero_mul, QuaternionAlgebra.smul_re, QuaternionAlgebra.one_re, smul_eq_mul,
        mul_one, QuaternionAlgebra.smul_imI, QuaternionAlgebra.one_imI, QuaternionAlgebra.smul_imJ,
        QuaternionAlgebra.one_imJ, QuaternionAlgebra.smul_imK, QuaternionAlgebra.one_imK, pow_two]
        exact mul_rotate b v v
      i_mul_j := by
        ext <;>
        simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, pow_two, add_zero, zero_mul,
          sub_self, zero_add, sub_zero]
      j_mul_i := by
        ext <;>
        simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, pow_two, zero_mul, add_zero,
          sub_self, zero_sub, QuaternionAlgebra.neg_mk, neg_zero, mul_comm] }

lemma to_square_one (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0):
    (equiv_to_square a b u v hu hv) ⟨1, 0, 0, 0⟩ = ⟨1, 0, 0, 0⟩ := by
  simp only [equiv_to_square, QuaternionAlgebra.lift_apply, QuaternionAlgebra.Basis.liftHom_apply]
  rw [show ⟨1, 0, 0, 0⟩ = (1 : ℍ[ℚ, a, b]) by rfl, QuaternionAlgebra.Basis.lift_one]; rfl

lemma to_square_re (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0) (x : ℍ[ℚ, a, b]):
    ((equiv_to_square a b u v hu hv) x).re = x.re := by
  simp only [equiv_to_square, QuaternionAlgebra.lift_apply, QuaternionAlgebra.Basis.liftHom_apply]
  sorry
theorem Bij_to_square (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0):
    Function.Bijective (equiv_to_square a b u v hu hv) := by
  refine ⟨?_, ?_⟩
  · intro x y; sorry
  · intro y; sorry
-- def equiv_mul_square (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0):
--     ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, u^2 * a, v^2 * b] where
--   toFun := equiv_to_square a b u v hu hv
--   invFun := square_to_equiv a b u v hu hv
--   left_inv x := by
--     have := equiv_to_square a b u v hu hv|>.left_inv x
--   right_inv x := by sorry
--   map_mul' := equiv_to_square a b u v hu hv|>.map_mul
--   map_add' := equiv_to_square a b u v hu hv|>.map_add
--   commutes' := equiv_to_square a b u v hu hv|>.commutes

def one_iso_matrix : ℍ[ℚ, 1, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ where
  toFun x := x.1 • 1 + x.2 • (1 - stdBasisMatrix 1 1 2) +
    x.3 • (stdBasisMatrix 0 1 b + stdBasisMatrix 1 0 1) +
    x.4 • (stdBasisMatrix 0 1 b - stdBasisMatrix 1 0 1)
  invFun M := ⟨(M 0 0 + M 1 1)/2, (M 0 0 - M 1 1)/2, ((M 0 1)/b + M 1 0)/2, ((M 0 1)/b - M 1 0)/2⟩
  left_inv x := by
    ext <;> simp only [Fin.isValue, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one, add_apply,
      smul_apply, ne_eq, zero_ne_one, not_false_eq_true, one_apply_ne, mul_zero, sub_apply,
      one_ne_zero, and_true, StdBasisMatrix.apply_of_ne, sub_self, add_zero,
      StdBasisMatrix.apply_same, and_self, zero_add, sub_zero, and_false, zero_sub, mul_neg,
      sub_self, mul_zero, StdBasisMatrix.apply_same, zero_ne_one]
    · simp only [Fin.isValue, one_apply_eq, mul_one]
      rw [show x.imI * (1 - 2) = -x.imI by ring, ← add_assoc]; ring
    · simp only [Fin.isValue, one_apply_eq, mul_one, add_sub_add_left_eq_sub]; ring
    · ring_nf; rw [mul_assoc x.imJ b b⁻¹, mul_inv_cancel hb, mul_one, mul_comm b, mul_assoc x.imK,
      mul_inv_cancel hb]; ring
    · ring_nf; rw [mul_assoc x.imJ b b⁻¹, mul_inv_cancel hb, mul_one, mul_comm b, mul_assoc x.imK,
      mul_inv_cancel hb]; ring

  right_inv x := by
    ext i j
    fin_cases i
    · fin_cases j
      · simp only [Fin.isValue, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one, Fin.zero_eta,
        add_apply, smul_apply, one_apply_eq, sub_apply, one_ne_zero, and_self, not_false_eq_true,
        StdBasisMatrix.apply_of_ne, sub_zero, and_false, and_true, add_zero, sub_self, mul_zero]
        ring
      · simp only [Fin.isValue, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one, Fin.zero_eta,
        Fin.mk_one, add_apply, smul_apply, ne_eq, zero_ne_one, not_false_eq_true, one_apply_ne,
        mul_zero, sub_apply, one_ne_zero, and_true, StdBasisMatrix.apply_of_ne, sub_self, add_zero,
        StdBasisMatrix.apply_same, and_self, zero_add, sub_zero]; ring_nf;
        exact (fun hc ↦ (eq_mul_inv_iff_mul_eq₀ hc).mpr) hb rfl |>.symm
    · fin_cases j
      · simp only [Fin.isValue, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one, Fin.mk_one,
        Fin.zero_eta, add_apply, smul_apply, ne_eq, one_ne_zero, not_false_eq_true, one_apply_ne,
        mul_zero, sub_apply, and_false, StdBasisMatrix.apply_of_ne, sub_self, add_zero, zero_ne_one,
        and_self, StdBasisMatrix.apply_same, zero_add, zero_sub, mul_neg]; ring
      · simp only [Fin.isValue, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one, Fin.mk_one,
        add_apply, smul_apply, one_apply_eq, sub_apply, StdBasisMatrix.apply_same, zero_ne_one,
        and_true, not_false_eq_true, StdBasisMatrix.apply_of_ne, and_false, add_zero, sub_self,
        mul_zero]; ring

  map_mul' x y := by
    simp only [QuaternionAlgebra.mul_re, one_mul, QuaternionAlgebra.mul_imI, Fin.isValue,
      QuaternionAlgebra.mul_imJ, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one,
      QuaternionAlgebra.mul_imK]; ext i j;
    fin_cases i; fin_cases j
    · simp only [Fin.isValue, Fin.zero_eta, add_apply, smul_apply, one_apply_eq, smul_eq_mul,
      mul_one, sub_apply, one_ne_zero, and_self, not_false_eq_true, StdBasisMatrix.apply_of_ne,
      sub_zero, and_false, and_true, add_zero, sub_self, mul_zero]
      repeat rw [Matrix.mul_add]; repeat rw [Matrix.add_mul]
      simp only [Algebra.mul_smul_comm, mul_one, Fin.isValue, smul_stdBasisMatrix, smul_eq_mul,
        Algebra.smul_mul_assoc, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
        StdBasisMatrix.mul_of_ne, StdBasisMatrix.mul_same, zero_add, zero_ne_one, add_zero,
        add_apply, smul_apply, one_apply_eq, sub_apply, and_self, StdBasisMatrix.apply_of_ne,
        sub_zero, and_false, and_true, sub_self, mul_zero, StdBasisMatrix.mul_left_apply_same,
        one_apply_ne, StdBasisMatrix.mul_left_apply_of_ne, StdBasisMatrix.mul_right_apply_of_ne,
        StdBasisMatrix.mul_right_apply_same, zero_mul, StdBasisMatrix.apply_same, zero_sub, mul_neg]
      repeat rw [Matrix.mul_sub]; repeat rw [Matrix.sub_mul]
      simp only [mul_one, Fin.isValue, one_mul, StdBasisMatrix.mul_same, sub_apply, one_apply_eq,
        one_ne_zero, and_self, not_false_eq_true, StdBasisMatrix.apply_of_ne, sub_zero, sub_self,
        ne_eq, zero_ne_one, StdBasisMatrix.mul_of_ne, and_false, and_true, mul_zero, add_zero,
        zero_add, zero_sub, neg_apply, neg_zero, StdBasisMatrix.apply_same, mul_neg]; ring
    · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, add_apply, smul_apply, ne_eq, zero_ne_one,
      not_false_eq_true, one_apply_ne, smul_eq_mul, mul_zero, sub_apply, one_ne_zero, and_true,
      StdBasisMatrix.apply_of_ne, sub_self, add_zero, StdBasisMatrix.apply_same, and_self, zero_add,
      sub_zero]
      repeat rw [Matrix.mul_add]; repeat rw [Matrix.add_mul]
      simp only [Algebra.mul_smul_comm, mul_one, Fin.isValue, smul_stdBasisMatrix, smul_eq_mul,
        Algebra.smul_mul_assoc, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
        StdBasisMatrix.mul_of_ne, StdBasisMatrix.mul_same, zero_add, zero_ne_one, add_zero,
        add_apply, smul_apply, one_apply_ne, mul_zero, sub_apply, and_true,
        StdBasisMatrix.apply_of_ne, sub_self, StdBasisMatrix.apply_same, and_self, sub_zero,
        StdBasisMatrix.mul_left_apply_same, one_apply_eq, StdBasisMatrix.mul_left_apply_of_ne,
        StdBasisMatrix.mul_right_apply_same, and_false, zero_mul,
        StdBasisMatrix.mul_right_apply_of_ne]
      repeat rw [Matrix.mul_sub]; repeat rw [Matrix.sub_mul]
      simp only [mul_one, Fin.isValue, one_mul, StdBasisMatrix.mul_same, sub_apply, ne_eq,
        zero_ne_one, not_false_eq_true, one_apply_ne, one_ne_zero, and_true,
        StdBasisMatrix.apply_of_ne, sub_self, mul_zero, zero_add, StdBasisMatrix.mul_of_ne,
        sub_zero, StdBasisMatrix.apply_same, and_self, zero_sub, neg_apply, neg_zero, and_false,
        add_zero]; ring
    · fin_cases j
      · simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, add_apply, smul_apply, ne_eq,
        one_ne_zero, not_false_eq_true, one_apply_ne, smul_eq_mul, mul_zero, sub_apply, and_false,
        StdBasisMatrix.apply_of_ne, sub_self, add_zero, zero_ne_one, and_self,
        StdBasisMatrix.apply_same, zero_add, zero_sub, mul_neg, mul_one, neg_add_rev, neg_sub]
        repeat rw [Matrix.mul_add]; repeat rw [Matrix.add_mul]
        simp only [Algebra.mul_smul_comm, mul_one, Fin.isValue, smul_stdBasisMatrix, smul_eq_mul,
          Algebra.smul_mul_assoc, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
          StdBasisMatrix.mul_of_ne, StdBasisMatrix.mul_same, zero_add, zero_ne_one, add_zero,
          add_apply, smul_apply, one_apply_ne, mul_zero, sub_apply, and_false,
          StdBasisMatrix.apply_of_ne, sub_self, and_self, StdBasisMatrix.apply_same, zero_sub,
          mul_neg, StdBasisMatrix.mul_left_apply_of_ne, StdBasisMatrix.mul_left_apply_same,
          one_apply_eq, sub_zero, StdBasisMatrix.mul_right_apply_of_ne,
          StdBasisMatrix.mul_right_apply_same, and_true, zero_mul]
        repeat rw [Matrix.mul_sub]; repeat rw [Matrix.sub_mul]
        simp only [mul_one, Fin.isValue, one_mul, StdBasisMatrix.mul_same, sub_apply, ne_eq,
          one_ne_zero, not_false_eq_true, one_apply_ne, and_false, StdBasisMatrix.apply_of_ne,
          sub_self, mul_zero, zero_add, zero_ne_one, StdBasisMatrix.mul_of_ne, sub_zero, and_self,
          StdBasisMatrix.apply_same, zero_sub, mul_neg, neg_sub, neg_apply, neg_zero, and_true,
          add_zero]; ring
      · simp only [Fin.isValue, Fin.mk_one, add_apply, smul_apply, one_apply_eq, smul_eq_mul,
        mul_one, sub_apply, StdBasisMatrix.apply_same, zero_ne_one, and_true, not_false_eq_true,
        StdBasisMatrix.apply_of_ne, and_false, add_zero, sub_self, mul_zero]
        repeat rw [Matrix.mul_add]; repeat rw [Matrix.add_mul]
        simp only [Algebra.mul_smul_comm, mul_one, Fin.isValue, smul_stdBasisMatrix, smul_eq_mul,
          Algebra.smul_mul_assoc, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
          StdBasisMatrix.mul_of_ne, StdBasisMatrix.mul_same, zero_add, zero_ne_one, add_zero,
          add_apply, smul_apply, one_apply_eq, sub_apply, StdBasisMatrix.apply_same, and_true,
          StdBasisMatrix.apply_of_ne, and_false, sub_self, mul_zero,
          StdBasisMatrix.mul_left_apply_of_ne, StdBasisMatrix.mul_left_apply_same, one_apply_ne,
          StdBasisMatrix.mul_right_apply_same, zero_mul, and_self, zero_sub, neg_mul, mul_neg,
          StdBasisMatrix.mul_right_apply_of_ne, sub_zero]
        repeat rw [Matrix.mul_sub]; repeat rw [Matrix.sub_mul]
        simp only [mul_one, Fin.isValue, one_mul, StdBasisMatrix.mul_same, sub_apply, one_apply_eq,
          StdBasisMatrix.apply_same, ne_eq, zero_ne_one, not_false_eq_true,
          StdBasisMatrix.mul_of_ne, sub_zero, and_true, StdBasisMatrix.apply_of_ne, and_false,
          sub_self, mul_zero, add_zero, one_ne_zero, zero_add, zero_sub, neg_apply, and_self,
          mul_neg]; ring


  map_add' x y := by
    ext i j; fin_cases i
    · fin_cases j
      · simp only [QuaternionAlgebra.add_re, QuaternionAlgebra.add_imI, Fin.isValue,
        QuaternionAlgebra.add_imJ, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one,
        QuaternionAlgebra.add_imK, Fin.zero_eta, add_apply, smul_apply, one_apply_eq, sub_apply,
        one_ne_zero, and_self, not_false_eq_true, StdBasisMatrix.apply_of_ne, sub_zero, and_false,
        and_true, add_zero, sub_self, mul_zero]; ring
      · simp only [QuaternionAlgebra.add_re, QuaternionAlgebra.add_imI, Fin.isValue,
        QuaternionAlgebra.add_imJ, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one,
        QuaternionAlgebra.add_imK, Fin.zero_eta, Fin.mk_one, add_apply, smul_apply, ne_eq,
        zero_ne_one, not_false_eq_true, one_apply_ne, mul_zero, sub_apply, one_ne_zero, and_true,
        StdBasisMatrix.apply_of_ne, sub_self, add_zero, StdBasisMatrix.apply_same, and_self,
        zero_add, sub_zero]; ring
    · fin_cases j
      · simp only [QuaternionAlgebra.add_re, QuaternionAlgebra.add_imI, Fin.isValue,
        QuaternionAlgebra.add_imJ, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one,
        QuaternionAlgebra.add_imK, Fin.mk_one, Fin.zero_eta, add_apply, smul_apply, ne_eq,
        one_ne_zero, not_false_eq_true, one_apply_ne, mul_zero, sub_apply, and_false,
        StdBasisMatrix.apply_of_ne, sub_self, add_zero, zero_ne_one, and_self,
        StdBasisMatrix.apply_same, zero_add, zero_sub, mul_neg, neg_add_rev]; ring
      · simp only [QuaternionAlgebra.add_re, QuaternionAlgebra.add_imI, Fin.isValue,
        QuaternionAlgebra.add_imJ, smul_add, smul_stdBasisMatrix, smul_eq_mul, mul_one,
        QuaternionAlgebra.add_imK, Fin.mk_one, add_apply, smul_apply, one_apply_eq, sub_apply,
        StdBasisMatrix.apply_same, zero_ne_one, and_true, not_false_eq_true,
        StdBasisMatrix.apply_of_ne, and_false, add_zero, sub_self, mul_zero]; ring

  commutes' q := by
    simp only [QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.coe_re,
      QuaternionAlgebra.coe_imI, Fin.isValue, zero_smul, add_zero, QuaternionAlgebra.coe_imJ,
      smul_add, QuaternionAlgebra.coe_imK]
    exact Algebra.algebraMap_eq_smul_one q|>.symm

lemma iso_to_not_div : Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) →
    ∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1)) := by
  intro ⟨hH⟩
  let x := hH.invFun $ stdBasisMatrix 1 1 1
  use x ; by_contra! hx ;
  have : x ≠ 0 := by
    suffices stdBasisMatrix 1 1 1 ≠ 0 by
      by_contra! hhx;
      have hHx : hH x = stdBasisMatrix 1 1 1 := by
        simp only [Equiv.invFun_as_coe, AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm,
          Fin.isValue, EquivLike.coe_coe, AlgEquiv.apply_symm_apply, x]
      apply_fun hH at hhx; rw [hHx,map_zero] at hhx; tauto
    intro h; rw [← Matrix.ext_iff] at h; specialize h 1 1
    simp only [StdBasisMatrix.apply_same, zero_apply, one_ne_zero] at h
  obtain ⟨y, hy1, hy2⟩ := hx this
  have : y = hH.invFun (hH.toFun y) := by simp [x]
  simp only [x] at hy1; rw [this] at hy1
  apply_fun hH at hy1
  simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
    AlgEquiv.symm_toEquiv_eq_symm, AlgEquiv.symm_apply_apply, Fin.isValue, _root_.map_mul,
    AlgEquiv.apply_symm_apply, _root_.map_one] at hy1
  suffices ∀(M : Matrix (Fin 2) (Fin 2) ℚ), M * stdBasisMatrix 1 1 1 ≠ 1 by tauto
  intro M ; by_contra! hM
  rw [← Matrix.ext_iff] at hM; specialize hM 2 2
  simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true,
    StdBasisMatrix.mul_right_apply_of_ne, one_apply_eq, zero_ne_one] at hM

lemma not_div_to_norm_zero :
    (∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1))) →
    (∃(x : ℍ[ℚ, a, b]), (x ≠ 0) ∧  (normQuat a b) x = 0) := by
  intro ⟨x, ⟨hx, hy⟩⟩
  by_contra! hx'
  have iff_1 : ∀ (x : ℍ[ℚ, a, b]), (normQuat a b) x = 0 ↔ x = 0 := by
    intro x; constructor
    · by_contra!; exact (hx' x this.2) this.1
    · intro hxx; simp only [hxx, map_zero]
  obtain ⟨y, hy1, hy2⟩ := non_zero_norm_iff_div a b |>.2 iff_1 x hx
  specialize hy y ; tauto

open Polynomial
abbrev f_a : Polynomial ℚ := X^2 - a • 1

instance f_a_irr (ha : ¬ ∃ y, a = y ^ 2): Irreducible (f_a a) := by
  unfold f_a; rw [irreducible_iff]
  constructor
  · by_contra! h
    rw [Polynomial.isUnit_iff_degree_eq_zero, sub_eq_neg_add] at h
    have h1 :=  Polynomial.eq_C_of_degree_eq_zero h
    simp only [coeff_add, coeff_neg, coeff_smul, coeff_one_zero, smul_eq_mul, mul_one, coeff_X_pow,
      OfNat.zero_ne_ofNat, ↓reduceIte, add_zero, map_neg] at h1
    rw [Algebra.smul_def, algebraMap_eq, mul_one] at h1
    simp at h1
  · intro h g h1
    by_contra! hhg
    rw [Algebra.smul_def, algebraMap_eq, mul_one] at h1
    have h_ne_zero : h ≠ 0 := by
      by_contra!
      simp only [this, zero_mul] at h1
      exact (Polynomial.X_pow_sub_C_ne_zero (by omega) a) h1
    have g_ne_zero : g ≠ 0 := by
      by_contra!
      simp only [this, mul_zero] at h1
      exact (Polynomial.X_pow_sub_C_ne_zero (by omega) a) h1
    obtain ⟨hh, hg⟩ := hhg
    have hh := Polynomial.degree_pos_of_ne_zero_of_nonunit h_ne_zero hh
    have hg := Polynomial.degree_pos_of_ne_zero_of_nonunit g_ne_zero hg
    have h2 : h.degree + g.degree = 2 := by
      rw [← degree_mul, ← h1, Polynomial.degree_X_pow_sub_C (by omega), Nat.cast_ofNat]
    rw [Polynomial.degree_eq_natDegree h_ne_zero, Polynomial.degree_eq_natDegree g_ne_zero] at *
    norm_cast at hh hg h2
    have hh : h.natDegree = 1 := by omega
    have hg : g.natDegree = 1 := by omega
    obtain ⟨m, ⟨hm, ⟨n, hn⟩⟩⟩ := Polynomial.natDegree_eq_one.1 hh
    obtain ⟨p, ⟨gp, ⟨q, gq⟩⟩⟩ := Polynomial.natDegree_eq_one.1 hg
    rw [← hn, ← gq] at h1
    ring_nf at h1
    rw [Polynomial.ext_iff] at h1
    obtain l0 := h1 0
    obtain l1 := (h1 1).symm
    obtain l2 := h1 2
    simp only [coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, coeff_C_zero, zero_sub,
      X_mul_C, X_pow_mul_C, X_pow_mul_assoc_C, coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero,
      zero_mul, add_zero, zero_add, OfNat.one_ne_ofNat, coeff_C_succ, sub_self, coeff_mul_C,
      coeff_mul_X, sub_zero] at l0 l1 l2
    rw [mul_assoc, mul_comm, coeff_mul_C] at l2
    nth_rewrite 2 [mul_comm] at l2
    rw [coeff_mul_C, coeff_X_pow] at l2
    simp only [↓reduceIte, one_mul] at l2
    rw [mul_assoc] at l1
    nth_rewrite 3 [mul_comm] at l1
    rw [coeff_mul_C] at l1
    nth_rewrite 4 [mul_comm] at l1
    rw [coeff_mul_C, coeff_X_pow] at l1
    simp only [OfNat.one_ne_ofNat, ↓reduceIte, zero_mul, add_zero] at l1
    apply ha
    use q / p
    rw [div_pow, neg_eq_iff_eq_neg.1 l0, pow_two, neg_mul_eq_neg_mul, mul_comm, ← mul_div_assoc']
    congr
    rw [neg_eq_iff_eq_neg, ← neg_div, eq_div_iff_mul_eq, pow_two]
    · rw [← neg_eq_iff_add_eq_zero] at l1
      rw [← mul_assoc, ← l1, neg_mul, neg_inj]
      nth_rewrite 2 [mul_comm]
      rw [mul_comm] at l2
      rw [mul_assoc, ← l2, mul_one]
    · rw [pow_ne_zero_iff]
      exact gp
      norm_num

instance (ha : ¬ ∃ y, a = y ^ 2) : Field (AdjoinRoot (f_a a)) := by
  exact @AdjoinRoot.instField (f := f_a a) (fact_iff.2 (f_a_irr a ha))

local notation "ℚ(√"a")" => Algebra.adjoin ℚ {√a}

def square_a_iso_to_Q (ha : ∃(y : ℚ), a = y ^ 2) :
    ℍ[ℚ, a, b] ≃ₐ[ℚ] ℚ := sorry

lemma norm_in_quadratic (x : ℚ(√a)): Algebra.norm ℚ x = (x:ℂ) * star (x: ℂ)  := sorry

-- Prop 1.1.7 3 -> 4
lemma norm_zero_to_norm_in :
    (∃(x : ℍ[ℚ, a, b]), (x ≠ 0) ∧  (normQuat a b) x = 0) →
    (∃(y : ℚ(√a)), b = Algebra.norm ℚ y) := by
  if ha : ∃(y : ℚ), a = y ^ 2 then
    intro ⟨x, hx⟩
    have e1 := square_a_iso_to_Q a b ha
    have pp1: (normQuat a b) x = 0 → ∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1) := by
      intro h; by_contra!
      have ne2 := invertible_iff a b x |>.1 $ Set.inter_nonempty_iff_exists_right.mp this
      exact ne2 h
    have con1 : ∃(y : ℍ[ℚ, a, b]), y * x = 1 ∧ x * y = 1 := by
      have ex : x = e1.invFun (e1 x) := by simp
      refine ⟨e1.invFun ((e1 x)⁻¹), ?_, ?_⟩
      · nth_rw 2 [ex]; apply_fun e1
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
          EquivLike.coe_coe, AlgEquiv.symm_apply_apply, _root_.map_mul, AlgEquiv.apply_symm_apply,
          _root_.map_one]; refine Rat.inv_mul_cancel _ ?_
        suffices x ≠ 0 by
          by_contra! hx1
          apply_fun e1.invFun at hx1
          simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
            EquivLike.coe_coe, AlgEquiv.symm_apply_apply, map_zero] at hx1; exact this hx1
        exact hx.1
      · rw [ex]; apply_fun e1
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
          EquivLike.coe_coe, AlgEquiv.symm_apply_apply, _root_.map_mul, AlgEquiv.apply_symm_apply,
          _root_.map_one]; refine Rat.mul_inv_cancel _ ?_
        suffices x ≠ 0 by
          by_contra! hx1
          apply_fun e1.invFun at hx1
          simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
            EquivLike.coe_coe, AlgEquiv.symm_apply_apply, map_zero] at hx1; exact this hx1
        exact hx.1
    obtain ⟨y, ⟨hy1, hy2⟩⟩ := con1 ; haveI:= pp1 hx.2 y ; tauto
  else
  intro ⟨x, ⟨hx, hnx⟩⟩
  simp only [normQuat, QuaternionAlgebra.mul_re, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, mul_neg, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star,
    sub_neg_eq_add, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] at hnx
  have eq1 : x.re * x.re + -(a * x.imI * x.imI) = b * (x.imJ * x.imJ - a * x.imK * x.imK) := by
    apply_fun fun y ↦ y - a * b * x.imK *x.imK + b * x.imJ * x.imJ  at hnx
    simp only [zero_sub] at hnx
    rw [← add_sub _ (a * b * x.imK * x.imK) (a * b * x.imK * x.imK), sub_self, add_zero,
      add_assoc, add_comm (- (b * x.imJ * x.imJ)), add_neg_self (b * x.imJ * x.imJ), add_zero,
      add_comm (-(a * b * x.imK * x.imK))] at hnx
    refine hnx.trans ?_
    simp only [mul_sub, ← mul_assoc]; ring

  sorry

-- Prop 1.1.7 4 -> 1
lemma norm_in_to_iso_matrix :
    (∃(y : ℚ(√a)), b = Algebra.norm ℚ y) →
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) := by sorry

theorem not_div_iff_iso_matrix :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) ↔
    ∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1)) := by
  constructor
  · exact iso_to_not_div a b
  · intro not_div
    refine norm_in_to_iso_matrix a b $ norm_zero_to_norm_in a b $ not_div_to_norm_zero a b not_div

end Quat
