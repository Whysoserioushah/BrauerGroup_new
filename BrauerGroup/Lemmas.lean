import Mathlib.RingTheory.TensorProduct.Basic
import BrauerGroup.CentralSimple

universe u

open TensorProduct BigOperators

variable (A k : Type u) [Field k] [Ring A] [Algebra k A]

theorem center_of_divring (D : Type u) [DivisionRing D] [Algebra k D] :
    IsField (Subalgebra.center k D) := {
  exists_pair_ne := exists_pair_ne _
  mul_comm := CommMonoid.mul_comm
  mul_inv_cancel := fun hd ↦ by
    rename_i d
    refine ⟨⟨d⁻¹, ?_⟩, ?_⟩
    · rw [Subalgebra.mem_center_iff]
      intro a
      if ha : a = 0 then simp only [ha, zero_mul, mul_zero]
      else
      apply_fun fun x ↦ x⁻¹
      · simp only [mul_inv_rev, inv_inv]
        have mem_center := d.2
        rw [Subalgebra.mem_center_iff] at mem_center
        exact mem_center a⁻¹|>.symm
      · exact inv_injective
    · simp [Subtype.ext_iff, hd] }

def center_ofA_eqv (n : ℕ) (_ : n ≠ 0) (D : Type u) [DivisionRing D] [Algebra k D]
    [FiniteDimensional k A] (iso : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    Subalgebra.center k A ≃ₐ[k] Subalgebra.center k (Matrix (Fin n) (Fin n) D) := {
    toFun := fun a ↦ ⟨iso a, by
      rw [Subalgebra.mem_center_iff]
      intro M
      rw [(AlgEquiv.apply_symm_apply iso M).symm, ← _root_.map_mul, ← _root_.map_mul]
      exact congrArg _ $ Subalgebra.mem_center_iff.1 a.2 $ iso.symm M ⟩
    invFun := fun M ↦ ⟨iso.symm M, by
      rw [Subalgebra.mem_center_iff]
      intro a
      rw [iso.symm_apply_apply a|>.symm, ← _root_.map_mul, ← _root_.map_mul]
      refine congrArg _ $ Subalgebra.mem_center_iff.1 M.2 $ iso a⟩
    left_inv := fun _ ↦ by simp only [AlgEquiv.symm_apply_apply, Subtype.coe_eta]
    right_inv := fun _ ↦ by simp only [AlgEquiv.apply_symm_apply, Subtype.coe_eta]
    map_mul' := fun _ _ ↦ by simp only [Submonoid.coe_mul, Subalgebra.center_toSubsemiring,
      Subsemiring.center_toSubmonoid, _root_.map_mul, Submonoid.mk_mul_mk]
    map_add' := fun _ _ ↦ by simp only [AddSubmonoid.coe_add,
      NonUnitalSubsemiring.coe_toAddSubmonoid, map_add, AddSubmonoid.mk_add_mk]
    commutes' := fun _ ↦ by simp only [Subalgebra.coe_algebraMap, AlgEquiv.commutes]; rfl }

def CenterEquiv.ofAlgEquiv (A B R : Type u) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
  Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B where
  toFun := fun ⟨a, ha⟩ ↦ ⟨e a, by
    rw [Subalgebra.mem_center_iff] at *
    exact fun b ↦ by rw [← e.apply_symm_apply b, ← _root_.map_mul, ← _root_.map_mul, ha]⟩
  invFun := fun ⟨b, hb⟩ ↦ ⟨e.symm b, by
    rw [Subalgebra.mem_center_iff] at *
    exact fun a ↦ by rw [← e.symm_apply_apply a, ← _root_.map_mul, ← _root_.map_mul, hb]⟩
  left_inv x := by simp only [AlgEquiv.symm_apply_apply, Subtype.coe_eta]
  right_inv y := by simp only [AlgEquiv.apply_symm_apply, Subtype.coe_eta]
  map_mul' := by simp
  map_add' := by simp
  commutes' := fun r ↦ by simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, Subalgebra.coe_algebraMap, AlgEquiv.commutes]; congr

def centerMatrixAlgEquiv (n : ℕ) (_ : n ≠ 0) :
    Subalgebra.center k (Matrix (Fin n) (Fin n) A) ≃ₐ[k] Subalgebra.center k A := {
      __ := Matrix.centerEquivBase n (by omega) A
      commutes' := fun _ ↦ rfl }

theorem IsField.ofRingEquiv (A1 A2 : Type u) [Ring A1] [Ring A2] (e : A1 ≃+* A2) :
    IsField A1 → IsField A2 := fun hA1 ↦ {
  exists_pair_ne := by
    obtain ⟨a, b, ha⟩ := hA1.1
    refine ⟨e a, e b, ?_⟩
    apply_fun e.symm
    simp only [RingEquiv.symm_apply_apply]
    exact ha
  mul_comm := fun a' b' ↦ by
    rw [(RingEquiv.apply_symm_apply e a').symm, (RingEquiv.apply_symm_apply e b').symm,
      ← e.map_mul, ← e.map_mul]
    exact congrArg _ $ hA1.2 _ _
  mul_inv_cancel := fun ha' ↦ by
    rename_i a'
    obtain ⟨b, hb⟩ := hA1.3 (a := (e.symm a')) (by simp_all)
    exact ⟨_, by rw [(RingEquiv.apply_symm_apply e a').symm, ← e.map_mul, hb, e.map_one]⟩
  }

theorem center_is_ext (hA : IsCentralSimple k A) [FiniteDimensional k A] :
    IsField (Subalgebra.center k A) := by
  obtain ⟨n, hn, D, hD1, hD2, ⟨iso⟩⟩ := @Wedderburn_Artin_algebra_version k A _ _ _ _ hA.2
  have := center_of_divring k D
  have e := center_ofA_eqv _ _ _ hn _ iso
  have e1 := e.trans $ centerMatrixAlgEquiv D k n hn
  exact IsField.ofRingEquiv _ _ e1.symm this

-- variable (D : Type u) [DivisionRing D] [Algebra k D]



-- theorem SkolemNoethoer
