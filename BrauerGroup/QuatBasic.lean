import Mathlib.Algebra.QuaternionBasis
import BrauerGroup.QuadraticExtension
import BrauerGroup.Con
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

def square_to_equiv (u v : ℚ) (_ : u ≠ 0) (_ : v ≠ 0):
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

lemma to_square_re (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0) (x : ℍ[ℚ, a, b]):
    ((equiv_to_square a b u v hu hv) x).re = x.re := by
  simp only [equiv_to_square, QuaternionAlgebra.lift_apply, QuaternionAlgebra.Basis.liftHom_apply]
  induction x with
  | mk x y z w =>
    simp only [QuaternionAlgebra.Basis.lift, QuaternionAlgebra.coe_algebraMap,
      QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, QuaternionAlgebra.add_re,
      QuaternionAlgebra.coe_re, add_zero]

def equiv_mul_square (u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0):
    ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, u^2 * a, v^2 * b] where
  toFun := equiv_to_square a b u v hu hv
  invFun := square_to_equiv a b u v hu hv
  left_inv x := by
    induction x with
    | mk x y z w =>
      ext
      · simp only [square_to_equiv, QuaternionAlgebra.lift_apply, equiv_to_square,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_re]
      · simp only [square_to_equiv, QuaternionAlgebra.lift_apply, equiv_to_square,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_imI]
        rwa [mul_assoc, inv_mul_cancel, mul_one]
      · simp only [square_to_equiv, QuaternionAlgebra.lift_apply, equiv_to_square,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_imJ]
        rwa [mul_assoc, inv_mul_cancel, mul_one]
      · simp only [square_to_equiv, QuaternionAlgebra.lift_apply, equiv_to_square,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_imK]
        field_simp
  right_inv x := by
    induction x with
    | mk x y z w =>
      ext
      · simp only [equiv_to_square, QuaternionAlgebra.lift_apply, square_to_equiv,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_re]
      · simp only [equiv_to_square, QuaternionAlgebra.lift_apply, square_to_equiv,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_imI]
        rwa [mul_assoc, mul_inv_cancel, mul_one]
      · simp only [equiv_to_square, QuaternionAlgebra.lift_apply, square_to_equiv,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_imJ]
        rwa [mul_assoc, mul_inv_cancel, mul_one]
      · simp only [equiv_to_square, QuaternionAlgebra.lift_apply, square_to_equiv,
        QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
        QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, map_add,
        QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, zero_smul, add_zero,
        QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, map_zero, zero_add,
        QuaternionAlgebra.add_imK]
        field_simp
  map_mul' := equiv_to_square a b u v hu hv|>.map_mul
  map_add' := equiv_to_square a b u v hu hv|>.map_add
  commutes' := equiv_to_square a b u v hu hv|>.commutes

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

-- open Polynomial
-- abbrev f_a : Polynomial ℚ := X^2 - a • 1

-- instance f_a_irr (ha : ¬ ∃ y, a = y ^ 2): Irreducible (f_a a) := by
--   unfold f_a; rw [irreducible_iff]
--   constructor
--   · by_contra! h
--     rw [Polynomial.isUnit_iff_degree_eq_zero, sub_eq_neg_add] at h
--     have h1 :=  Polynomial.eq_C_of_degree_eq_zero h
--     simp only [coeff_add, coeff_neg, coeff_smul, coeff_one_zero, smul_eq_mul, mul_one, coeff_X_pow,
--       OfNat.zero_ne_ofNat, ↓reduceIte, add_zero, map_neg] at h1
--     rw [Algebra.smul_def, algebraMap_eq, mul_one] at h1
--     simp at h1
--   · intro h g h1
--     by_contra! hhg
--     rw [Algebra.smul_def, algebraMap_eq, mul_one] at h1
--     have h_ne_zero : h ≠ 0 := by
--       by_contra!
--       simp only [this, zero_mul] at h1
--       exact (Polynomial.X_pow_sub_C_ne_zero (by omega) a) h1
--     have g_ne_zero : g ≠ 0 := by
--       by_contra!
--       simp only [this, mul_zero] at h1
--       exact (Polynomial.X_pow_sub_C_ne_zero (by omega) a) h1
--     obtain ⟨hh, hg⟩ := hhg
--     have hh := Polynomial.degree_pos_of_ne_zero_of_nonunit h_ne_zero hh
--     have hg := Polynomial.degree_pos_of_ne_zero_of_nonunit g_ne_zero hg
--     have h2 : h.degree + g.degree = 2 := by
--       rw [← degree_mul, ← h1, Polynomial.degree_X_pow_sub_C (by omega), Nat.cast_ofNat]
--     rw [Polynomial.degree_eq_natDegree h_ne_zero, Polynomial.degree_eq_natDegree g_ne_zero] at *
--     norm_cast at hh hg h2
--     have hh : h.natDegree = 1 := by omega
--     have hg : g.natDegree = 1 := by omega
--     obtain ⟨m, ⟨_, ⟨n, hn⟩⟩⟩ := Polynomial.natDegree_eq_one.1 hh
--     obtain ⟨p, ⟨gp, ⟨q, gq⟩⟩⟩ := Polynomial.natDegree_eq_one.1 hg
--     rw [← hn, ← gq] at h1
--     ring_nf at h1
--     rw [Polynomial.ext_iff] at h1
--     obtain l0 := h1 0
--     obtain l1 := (h1 1).symm
--     obtain l2 := h1 2
--     simp only [coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, coeff_C_zero, zero_sub,
--       X_mul_C, X_pow_mul_C, X_pow_mul_assoc_C, coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero,
--       zero_mul, add_zero, zero_add, OfNat.one_ne_ofNat, coeff_C_succ, sub_self, coeff_mul_C,
--       coeff_mul_X, sub_zero] at l0 l1 l2
--     rw [mul_assoc, mul_comm, coeff_mul_C] at l2
--     nth_rewrite 2 [mul_comm] at l2
--     rw [coeff_mul_C, coeff_X_pow] at l2
--     simp only [↓reduceIte, one_mul] at l2
--     rw [mul_assoc] at l1
--     nth_rewrite 3 [mul_comm] at l1
--     rw [coeff_mul_C] at l1
--     nth_rewrite 4 [mul_comm] at l1
--     rw [coeff_mul_C, coeff_X_pow] at l1
--     simp only [OfNat.one_ne_ofNat, ↓reduceIte, zero_mul, add_zero] at l1
--     apply ha
--     use q / p
--     rw [div_pow, neg_eq_iff_eq_neg.1 l0, pow_two, neg_mul_eq_neg_mul, mul_comm, ← mul_div_assoc']
--     congr
--     rw [neg_eq_iff_eq_neg, ← neg_div, eq_div_iff_mul_eq, pow_two]
--     · rw [← neg_eq_iff_add_eq_zero] at l1
--       rw [← mul_assoc, ← l1, neg_mul, neg_inj]
--       nth_rewrite 2 [mul_comm]
--       rw [mul_comm] at l2
--       rw [mul_assoc, ← l2, mul_one]
--     · rw [pow_ne_zero_iff]
--       exact gp
--       norm_num

-- instance (ha : ¬ ∃ y, a = y ^ 2) : Field (AdjoinRoot (f_a a)) := by
--   exact @AdjoinRoot.instField (f := f_a a) (fact_iff.2 (f_a_irr a ha))

-- local notation "ℚ(√"a")" => Algebra.adjoin ℚ {√a}

-- Prop 1.1.7 3 -> 4
open Ksqrtd
lemma norm_zero_to_norm_in :
    (∃(x : ℍ[ℚ, a, b]), (x ≠ 0) ∧  (normQuat a b) x = 0) →
    (∃(y : Ksqrtd a), b = Ksqrtd.norm y) ∨
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) := by
  intro ⟨x, ⟨hx1, hx2⟩⟩
  if h : IsSquare a then
  obtain ⟨k, h⟩ := h
  right
  have k_neq' : k ≠ 0 := by
    simp_all only [ne_eq, mul_eq_zero, or_self, not_false_eq_true]
  have k_neq : k⁻¹ ≠ 0 := by
    simp_all only [ne_eq, mul_eq_zero, or_self, inv_eq_zero, not_false_eq_true]
  have eqv : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, 1, b] := by
    have := Quat.equiv_mul_square a b k⁻¹ 1 k_neq one_ne_zero
    rw [h, pow_two, mul_assoc, ← mul_assoc k⁻¹ k k, inv_mul_cancel k_neq', one_mul,
      inv_mul_cancel k_neq', pow_two, one_mul, one_mul, ← h] at this
    exact this
  exact ⟨eqv.trans $ one_iso_matrix b hb⟩
  else
  left
  simp only [normQuat, QuaternionAlgebra.mul_re, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, mul_neg, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star,
    sub_neg_eq_add, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] at hx2
  have eq1 : x.re * x.re + -(a * x.imI * x.imI) = b * (x.imJ * x.imJ - a * x.imK * x.imK) := by
    apply_fun fun y ↦ y - a * b * x.imK *x.imK + b * x.imJ * x.imJ at hx2
    simp only [zero_sub] at hx2
    rw [← add_sub _ (a * b * x.imK * x.imK) (a * b * x.imK * x.imK), sub_self, add_zero,
      add_assoc, add_comm (- (b * x.imJ * x.imJ)), add_neg_self (b * x.imJ * x.imJ), add_zero,
      add_comm (-(a * b * x.imK * x.imK))] at hx2
    refine hx2.trans ?_
    simp only [mul_sub, ← mul_assoc]; ring
  have eq2 : (⟨x.imJ, x.imK⟩ : Ksqrtd a).norm = (x.imJ * x.imJ - a * x.imK * x.imK) := rfl
  have eq3 : (⟨x.re, x.imI⟩ : Ksqrtd a).norm = x.re * x.re + -(a * x.imI * x.imI) := by
    simp only [Ksqrtd.norm_def] ; ring
  simp only [← eq3, ← eq2] at eq1
  apply_fun fun y ↦ y * (⟨x.imJ, x.imK⟩ : Ksqrtd a).norm⁻¹ at eq1
  if hK : x.imK = 0 then
  simp only [hK, mul_zero, add_zero] at hx2
  if hJ : x.imJ = 0 then
  simp [hJ, hK] at hx2
  apply_fun (· + a * x.imI * x.imI) at hx2
  rw [zero_add, add_assoc, neg_add_self, add_zero] at hx2
  have hI : x.imI ≠ 0 := by
    by_contra!
    simp only [this, mul_zero, mul_eq_zero, or_self] at hx2
    have : x = 0 := by ext <;> simpa
    tauto
  apply_fun (· * (x.imI * x.imI)⁻¹) at hx2
  rw [mul_inv, ← mul_assoc] at hx2; nth_rw 3 [mul_assoc] at hx2
  rw [← mul_assoc x.imI, mul_inv_cancel hI, one_mul, mul_assoc a, mul_inv_cancel hI, mul_one,
    mul_assoc x.re, mul_comm x.re, mul_assoc] at hx2
  have : IsSquare a := ⟨x.re * x.imI⁻¹, hx2.symm⟩; tauto
  else
  have norm_neq_zero : norm (d := a) ⟨x.imJ, x.imK⟩ ≠ 0 := by
    by_contra!
    rw [norm_eq_zero_iff h] at this
    apply_fun fun (y : K√a) ↦ y.re at this
    rw [show (⟨x.imJ, x.imK⟩ : K√a).re = x.imJ from rfl, Ksqrtd.zero_re] at this
    exact hJ this
  rw [mul_assoc, mul_inv_cancel norm_neq_zero, mul_one] at eq1
  rw [inv_norm_inv h ⟨x.imJ, x.imK⟩, ← Ksqrtd.norm_mul] at eq1
  exact ⟨_, eq1.symm⟩
  else
  have norm_neq_zero : norm (d := a) ⟨x.imJ, x.imK⟩ ≠ 0 := by
    by_contra!
    rw [norm_eq_zero_iff h] at this
    apply_fun fun (y : K√a) ↦ y.im at this
    rw [show (⟨x.imJ, x.imK⟩ : K√a).im = x.imK from rfl, Ksqrtd.zero_im] at this
    exact hK this
  rw [mul_assoc, mul_inv_cancel norm_neq_zero, mul_one] at eq1
  rw [inv_norm_inv h ⟨x.imJ, x.imK⟩, ← Ksqrtd.norm_mul] at eq1
  exact ⟨_, eq1.symm⟩

lemma quat_isSimple : IsSimpleOrder (RingCon $ ℍ[ℚ, a, b]) := by
  refine ⟨fun I => ?_⟩
  if h : I = ⊥ then exact Or.inl h else

  refine Or.inr ?_

  suffices ∃ (x : ℍ[ℚ, a, b]), IsUnit x ∧ x ∈ I by
    rcases this with ⟨_, ⟨⟨⟨x, y, hxy1, hxy2⟩, rfl⟩, h⟩⟩
    rw [eq_top_iff, RingCon.le_iff]
    rintro z -
    have : z * y * x ∈ I := by
      apply I.mul_mem_left
      exact h
    rw [mul_assoc, hxy2, mul_one] at this
    exact this

  rw [eq_bot_iff, RingCon.le_iff, Set.not_subset_iff_exists_mem_not_mem] at h
  obtain ⟨⟨x₁, x₂, x₃, x₄⟩, (hx1 : _ ∈ I), (hx2 : _ ≠ 0)⟩ := h
  simp only [ne_eq, QuaternionAlgebra.ext_iff, QuaternionAlgebra.zero_re,
    QuaternionAlgebra.zero_imI, QuaternionAlgebra.zero_imJ, QuaternionAlgebra.zero_imK,
    not_and] at hx2
  let q : ℍ[ℚ, a, b] := ⟨x₁, x₂, x₃, x₄⟩
  let i : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
  let j : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
  have eq1 : (2⁻¹ : ℚ) • (i * q - q * i) = ⟨0, 0, a * x₄, x₃⟩ := by
    ext
    · simp
    · simp
    · simp only [QuaternionAlgebra.smul_imJ, QuaternionAlgebra.sub_imJ, QuaternionAlgebra.mul_imJ,
      zero_mul, mul_one, zero_add, add_zero, mul_zero, sub_zero, zero_sub, sub_neg_eq_add,
      smul_eq_mul]
      field_simp
    · simp only [QuaternionAlgebra.smul_imK, QuaternionAlgebra.sub_imK, QuaternionAlgebra.mul_imK,
      zero_mul, one_mul, zero_add, sub_zero, add_zero, mul_zero, mul_one, zero_sub, sub_neg_eq_add,
      smul_eq_mul]
      field_simp
  have eq2 : (2⁻¹ : ℚ) • (i * q + q * i) = ⟨a * x₂, x₁, 0, 0⟩ := by
    ext
    · simp only [smul_add, QuaternionAlgebra.add_re, QuaternionAlgebra.smul_re,
      QuaternionAlgebra.mul_re, zero_mul, mul_one, zero_add, mul_zero, add_zero, sub_zero,
      smul_eq_mul]
      field_simp
    · simp only [smul_add, QuaternionAlgebra.add_imI, QuaternionAlgebra.smul_imI,
      QuaternionAlgebra.mul_imI, zero_mul, one_mul, zero_add, mul_zero, sub_zero, add_zero,
      smul_eq_mul, mul_one]
      field_simp
    · simp
    · simp
  observe ha : a ≠ 0
  observe hb : b ≠ 0
  replace hx2 : x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 ∨ x₄ ≠ 0 := by tauto
  have aux1 : (⟨0, 0, a * x₄, x₃⟩ : ℍ[ℚ, a, b]) ≠ 0 ∨ (⟨a * x₂, x₁, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
    by_contra! rid
    rcases rid with ⟨h1, h2⟩
    rw [QuaternionAlgebra.ext_iff] at h1 h2
    simp only [QuaternionAlgebra.zero_re, QuaternionAlgebra.zero_imI, QuaternionAlgebra.zero_imJ,
      mul_eq_zero, QuaternionAlgebra.zero_imK, true_and, and_self, and_true] at h1 h2
    tauto
  have aux2 : ∃ (y₀ y₁ : ℚ), (y₀ ≠ 0 ∨ y₁ ≠ 0) ∧ (⟨y₀, y₁, 0, 0⟩ : ℍ[ℚ, a, b]) ∈ I := by
    rcases aux1 with h|h
    · have : (⟨0, 0, a * x₄, x₃⟩ : ℍ[ℚ, a, b]) * j ≠ 0 := by
        simp only [ne_eq, QuaternionAlgebra.ext_iff, QuaternionAlgebra.zero_re,
          QuaternionAlgebra.zero_imI, QuaternionAlgebra.zero_imJ, mul_eq_zero,
          QuaternionAlgebra.zero_imK, true_and, not_and, QuaternionAlgebra.mul_re, mul_zero,
          add_zero, mul_one, zero_add, sub_zero, QuaternionAlgebra.mul_imI, sub_self,
          QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK, and_self, and_true, not_or] at h ⊢
        tauto
      have eq : (⟨0, 0, a * x₄, x₃⟩ : ℍ[ℚ, a, b]) * j = ⟨b * a * x₄, b * x₃, 0, 0⟩ := by
        ext
        · simp only [QuaternionAlgebra.mul_re, mul_zero, add_zero, mul_one, zero_add, mul_assoc,
          sub_zero]
        · simp only [QuaternionAlgebra.mul_imI, mul_zero, add_zero, sub_self, mul_one, zero_add]
        · simp
        · simp
      refine ⟨b * a * x₄, b * x₃, ?_, ?_⟩
      · contrapose! h
        simp only [mul_eq_zero] at h
        ext
        · simp only [QuaternionAlgebra.zero_re]
        · simp only [QuaternionAlgebra.zero_imI]
        · simp only [QuaternionAlgebra.zero_imJ, mul_eq_zero]; tauto
        · simp only [QuaternionAlgebra.zero_imK]; tauto
      rw [← eq]
      apply RingCon.mul_mem_right
      rw [← eq1]
      rw [Algebra.smul_def]
      apply RingCon.smul_mem
      apply RingCon.sub_mem
      · apply RingCon.mul_mem_left
        assumption
      · apply RingCon.mul_mem_right
        assumption
    · refine ⟨a * x₂, x₁, ?_, ?_⟩
      · contrapose! h
        simp only [mul_eq_zero] at h
        ext
        · simp only [QuaternionAlgebra.zero_re, mul_eq_zero]
          tauto
        · simp only [QuaternionAlgebra.zero_imI]
          tauto
        · simp only [QuaternionAlgebra.zero_imJ]
        · simp only [QuaternionAlgebra.zero_imK]
      · rw [← eq2, Algebra.smul_def]
        apply RingCon.smul_mem
        apply RingCon.add_mem
        · apply RingCon.smul_mem
          assumption
        · apply RingCon.mul_mem_right
          assumption
  obtain ⟨y₀, y₁, h, mem⟩ := aux2
  let z : ℍ[ℚ, a, b] := ⟨y₀, y₁, 0, 0⟩
  have eq3 : (2⁻¹ : ℚ) • (j * z + z * j) = ⟨0, 0, y₀, 0⟩ := by
    ext
    · simp
    · simp
    · simp only [smul_add, QuaternionAlgebra.add_imJ, QuaternionAlgebra.smul_imJ,
      QuaternionAlgebra.mul_imJ, mul_zero, add_zero, one_mul, zero_add, zero_mul, sub_zero,
      smul_eq_mul, mul_one]
      field_simp
    · simp
  have eq4 : (2⁻¹ : ℚ) • (j * z - z * j) = ⟨0, 0, 0, - y₁⟩ := by
    ext
    · simp
    · simp
    · simp
    · simp only [QuaternionAlgebra.smul_imK, QuaternionAlgebra.sub_imK, QuaternionAlgebra.mul_imK,
      mul_zero, add_zero, one_mul, zero_sub, zero_mul, mul_one, zero_add, sub_zero, smul_eq_mul]
      rw [sub_eq_add_neg, ← two_mul, ← mul_assoc, inv_mul_cancel, one_mul]
      exact two_ne_zero
  rcases h with h|h
  · refine ⟨⟨0, 0, y₀, 0⟩, isUnit_iff_exists_and_exists.2 ⟨?_, ?_⟩, ?_⟩
    · refine ⟨⟨0, 0, b⁻¹ * y₀⁻¹, 0⟩, ?_⟩
      ext
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_re]
        field_simp
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imI]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imJ]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imK]
    · refine ⟨⟨0, 0, b⁻¹ * y₀⁻¹, 0⟩, ?_⟩
      ext
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_re]
        field_simp
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imI]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imJ]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imK]
    · rw [← eq3, Algebra.smul_def]
      apply RingCon.smul_mem
      apply RingCon.add_mem
      · apply RingCon.mul_mem_left
        assumption
      · apply RingCon.mul_mem_right
        assumption

  · refine ⟨⟨0, 0, 0, - y₁⟩, isUnit_iff_exists_and_exists.2 ⟨?_, ?_⟩, ?_⟩
    · refine ⟨⟨0, 0, 0, a⁻¹ * b⁻¹ * y₁⁻¹⟩, ?_⟩
      ext
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_re]
        field_simp
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imI]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imJ]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imK]
    · refine ⟨⟨0, 0, 0, a⁻¹ * b⁻¹ * y₁⁻¹⟩, ?_⟩
      ext
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_re]
        field_simp
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imI]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imJ]
      · simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, sub_zero, sub_self,
        zero_mul, QuaternionAlgebra.one_imK]
    rw [← eq4, Algebra.smul_def]
    apply RingCon.smul_mem
    apply RingCon.sub_mem
    · apply RingCon.mul_mem_left
      assumption
    · apply RingCon.mul_mem_right
      assumption

-- Prop 1.1.7 4 -> 1
lemma norm_in_to_iso_matrix :
    (∃(y : Ksqrtd a), b = Ksqrtd.norm y) ∨ Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) →
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) := by
  intro h
  rcases h with h|h
  · if haa : IsSquare a then
    obtain ⟨k, h⟩ := haa
    have k_neq' : k ≠ 0 := by
      simp_all only [ne_eq, mul_eq_zero, or_self, not_false_eq_true]
    have k_neq : k⁻¹ ≠ 0 := by
      simp_all only [ne_eq, mul_eq_zero, or_self, inv_eq_zero, not_false_eq_true]
    have eqv : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, 1, b] := by
      have := Quat.equiv_mul_square a b k⁻¹ 1 k_neq one_ne_zero
      rw [h, pow_two, mul_assoc, ← mul_assoc k⁻¹ k k, inv_mul_cancel k_neq', one_mul,
        inv_mul_cancel k_neq', pow_two, one_mul, one_mul, ← h] at this
      exact this
    exact ⟨eqv.trans $ one_iso_matrix b hb⟩
    else

    obtain ⟨y, hy⟩ := h
    have hbinv : b⁻¹ = y⁻¹.norm := by
      apply_fun fun x ↦ x⁻¹ at hy
      exact hy.trans $ inv_norm_inv haa y
    rw [norm_def] at hbinv
    let u := (⟨0, 0, y⁻¹.re, y⁻¹.im⟩ : ℍ[ℚ, a, b])
    have u_sq : u * u = 1 := by
      simp only [QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero, zero_add, zero_sub, zero_mul,
        sub_self, u]
      ext <;> simp only [QuaternionAlgebra.one_re, QuaternionAlgebra.one_imI,
        QuaternionAlgebra.one_imJ, QuaternionAlgebra.one_imK]
      · rw [mul_comm a b, mul_assoc, mul_assoc b, mul_assoc b, ← mul_sub, hbinv.symm]
        exact mul_inv_cancel hb
      · ring
    let v := ⟨0, 1 + a, 0, 0⟩ + (1 - a) * u * ⟨0, 1, 0, 0⟩
    have eq1 : u * ⟨0, 1, 0, 0⟩ = - (⟨0, 1, 0, 0⟩ * u) := by simp [u]
    have eq2 : u * v = - (v * u) := by
      simp only [u, v]
      ext <;> simp <;> ring
    have v_sq : v * v = 4 * a * a := by
      simp only [v]
      ext
      · simp only [QuaternionAlgebra.mul_re, QuaternionAlgebra.add_re, QuaternionAlgebra.sub_re,
        QuaternionAlgebra.one_re, QuaternionAlgebra.coe_re, mul_zero, QuaternionAlgebra.sub_imI,
        QuaternionAlgebra.one_imI, QuaternionAlgebra.coe_imI, sub_self, add_zero,
        QuaternionAlgebra.sub_imJ, QuaternionAlgebra.one_imJ, QuaternionAlgebra.coe_imJ, zero_mul,
        QuaternionAlgebra.sub_imK, QuaternionAlgebra.one_imK, QuaternionAlgebra.coe_imK,
        QuaternionAlgebra.mul_imI, mul_one, QuaternionAlgebra.mul_imJ, sub_zero,
        QuaternionAlgebra.mul_imK, QuaternionAlgebra.add_imI, zero_add, QuaternionAlgebra.add_imJ,
        zero_sub, mul_neg, neg_mul, neg_neg, QuaternionAlgebra.add_imK]
        rw [mul_comm a b, mul_assoc b a, mul_assoc b, mul_assoc b, ← add_sub, ← mul_sub,
          ← mul_assoc a, mul_assoc (a * (1 - a)), mul_comm y⁻¹.im, ← mul_assoc a,
          mul_assoc (a * (1 - a)), mul_assoc (a * (1 - a)), ← mul_sub]
        nth_rw 2 [mul_comm a (1 - a)]; rw [mul_assoc (1 - a) a (y⁻¹.im * y⁻¹.im),
          ← mul_assoc y⁻¹.re, mul_comm y⁻¹.re, mul_assoc (1 - a), ← mul_sub, ← mul_assoc a,
          show a * y⁻¹.im * y⁻¹.im - y⁻¹.re * y⁻¹.re = - b⁻¹ by aesop,
          mul_comm b, ← mul_assoc, mul_assoc (a * (1 - a) * (1 - a)), neg_mul, inv_mul_cancel hb,
          mul_neg, mul_one]
        ring_nf; rfl
      · simp only [QuaternionAlgebra.mul_imI, QuaternionAlgebra.add_re, QuaternionAlgebra.mul_re,
        QuaternionAlgebra.sub_re, QuaternionAlgebra.one_re, QuaternionAlgebra.coe_re, mul_zero,
        QuaternionAlgebra.sub_imI, QuaternionAlgebra.one_imI, QuaternionAlgebra.coe_imI, sub_self,
        add_zero, QuaternionAlgebra.sub_imJ, QuaternionAlgebra.one_imJ, QuaternionAlgebra.coe_imJ,
        zero_mul, QuaternionAlgebra.sub_imK, QuaternionAlgebra.one_imK, QuaternionAlgebra.coe_imK,
        mul_one, QuaternionAlgebra.mul_imJ, sub_zero, QuaternionAlgebra.mul_imK,
        QuaternionAlgebra.add_imI, QuaternionAlgebra.add_imJ, zero_sub, zero_add, mul_neg,
        QuaternionAlgebra.add_imK, neg_mul, neg_neg]
        rw [show @imI ℚ a b 4 = 0 from rfl, zero_mul, zero_mul]; ring
      · simp only [QuaternionAlgebra.mul_imJ, QuaternionAlgebra.add_re, QuaternionAlgebra.mul_re,
        QuaternionAlgebra.sub_re, QuaternionAlgebra.one_re, QuaternionAlgebra.coe_re, mul_zero,
        QuaternionAlgebra.sub_imI, QuaternionAlgebra.one_imI, QuaternionAlgebra.coe_imI, sub_self,
        add_zero, QuaternionAlgebra.sub_imJ, QuaternionAlgebra.one_imJ, QuaternionAlgebra.coe_imJ,
        zero_mul, QuaternionAlgebra.sub_imK, QuaternionAlgebra.one_imK, QuaternionAlgebra.coe_imK,
        QuaternionAlgebra.mul_imI, mul_one, sub_zero, QuaternionAlgebra.mul_imK,
        QuaternionAlgebra.add_imJ, zero_sub, zero_add, mul_neg, neg_zero, QuaternionAlgebra.add_imI,
        QuaternionAlgebra.add_imK, neg_mul, sub_neg_eq_add]
        rw [show @imJ ℚ a b 4 = 0 from rfl, zero_mul, zero_mul]; ring
      · simp only [QuaternionAlgebra.mul_imK, QuaternionAlgebra.add_re, QuaternionAlgebra.mul_re,
        QuaternionAlgebra.sub_re, QuaternionAlgebra.one_re, QuaternionAlgebra.coe_re, mul_zero,
        QuaternionAlgebra.sub_imI, QuaternionAlgebra.one_imI, QuaternionAlgebra.coe_imI, sub_self,
        add_zero, QuaternionAlgebra.sub_imJ, QuaternionAlgebra.one_imJ, QuaternionAlgebra.coe_imJ,
        zero_mul, QuaternionAlgebra.sub_imK, QuaternionAlgebra.one_imK, QuaternionAlgebra.coe_imK,
        QuaternionAlgebra.mul_imI, mul_one, QuaternionAlgebra.mul_imJ, sub_zero,
        QuaternionAlgebra.add_imK, zero_sub, zero_add, mul_neg, neg_zero, QuaternionAlgebra.add_imI,
        QuaternionAlgebra.add_imJ, neg_mul, sub_neg_eq_add]
        rw [show @imK ℚ a b 4 = 0 from rfl, zero_mul, zero_mul]; ring
    have := equiv_mul_square 1 (4 * a * a)
    let one_iso_to : ℍ[ℚ, 1, 4 * a * a] →ₐ[ℚ] ℍ[ℚ, a, b] :=
      QuaternionAlgebra.lift $
      { i := u
        j := v
        k := u * v
        i_mul_i := by simp only [one_smul] ; exact u_sq
        j_mul_j := by
          simp only [v_sq];
          simp_all only [ne_eq, QuaternionAlgebra.mk_mul_mk, mul_zero, add_zero,
            zero_add, zero_sub, zero_mul, sub_self, mul_one, sub_zero, one_mul,
            QuaternionAlgebra.neg_mk, neg_zero, u, v]
          ext
          · simp only [QuaternionAlgebra.mul_re, QuaternionAlgebra.coe_re,
            QuaternionAlgebra.coe_imI, mul_zero, add_zero, QuaternionAlgebra.coe_imJ,
            QuaternionAlgebra.coe_imK, sub_zero, QuaternionAlgebra.mul_imI, zero_add,
            QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK, sub_self,
            QuaternionAlgebra.smul_re, QuaternionAlgebra.one_re, smul_eq_mul, mul_one,
            mul_eq_mul_right_iff, or_self_right]; left; rfl
          · simp only [QuaternionAlgebra.mul_imI, QuaternionAlgebra.mul_re,
              QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, mul_zero, add_zero,
              QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, sub_zero, zero_add,
              QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK, sub_self,
              QuaternionAlgebra.smul_imI, QuaternionAlgebra.one_imI, smul_eq_mul, mul_eq_zero,
              or_self_right]; left; rfl
          · simp only [QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_re,
              QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, mul_zero, add_zero,
              QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, sub_zero,
              QuaternionAlgebra.mul_imI, zero_add, QuaternionAlgebra.mul_imK, sub_self,
              QuaternionAlgebra.smul_imJ, QuaternionAlgebra.one_imJ, smul_eq_mul, mul_eq_zero,
              or_self_right]; left; rfl
          · simp only [QuaternionAlgebra.mul_imK, QuaternionAlgebra.mul_re,
            QuaternionAlgebra.coe_re, QuaternionAlgebra.coe_imI, mul_zero, add_zero,
            QuaternionAlgebra.coe_imJ, QuaternionAlgebra.coe_imK, sub_zero,
            QuaternionAlgebra.mul_imI, zero_add, QuaternionAlgebra.mul_imJ, sub_self,
            QuaternionAlgebra.smul_imK, QuaternionAlgebra.one_imK, smul_eq_mul, mul_eq_zero,
            or_self_right]; left; rfl
        i_mul_j := rfl
        j_mul_i := by simp only [eq2, neg_neg] }
    have inj : Function.Injective one_iso_to := by
      change Function.Injective one_iso_to.toRingHom
      have H := RingCon.IsSimpleOrder.iff_eq_zero_or_injective ℍ[ℚ,1,4 * a * a] |>.1 $
        quat_isSimple 1 (4 * a * a) (by simp) (by simpa)
      specialize H one_iso_to.toRingHom
      refine H.resolve_left fun rid => ?_
      rw [eq_top_iff, RingCon.le_iff] at rid
      specialize @rid 1 ⟨⟩
      simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, RingCon.mem_ker, _root_.map_one,
        one_ne_zero] at rid

    have bij : Function.Bijective one_iso_to :=
    ⟨inj,
    by
      change Function.Surjective one_iso_to.toLinearMap
      rw [← LinearMap.range_eq_top]
      have eq := one_iso_to.toLinearMap.finrank_range_add_finrank_ker
      rw [QuaternionAlgebra.finrank_eq_four, LinearMap.ker_eq_bot.2 inj, finrank_bot, add_zero] at eq
      apply Submodule.eq_top_of_finrank_eq
      rw [eq, QuaternionAlgebra.finrank_eq_four]⟩
    have eqv : ℍ[ℚ, 1, 4 * a * a] ≃ₐ[ℚ] ℍ[ℚ, a, b] :=
      AlgEquiv.ofBijective one_iso_to bij
    exact ⟨eqv.symm.trans $ one_iso_matrix (4 * a * a) (by simpa)⟩
  · exact h

theorem not_div_iff_iso_matrix :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) ↔
    ∃(x : ℍ[ℚ, a, b]), x ≠ 0 ∧ (∀(y : ℍ[ℚ, a, b]), (y * x ≠ 1 ∨ x * y ≠ 1)) := by
  constructor
  · exact iso_to_not_div a b
  · intro not_div
    refine norm_in_to_iso_matrix a b ha hb $ norm_zero_to_norm_in a b ha hb $
      not_div_to_norm_zero a b not_div

end Quat
