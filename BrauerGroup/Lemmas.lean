import Mathlib.RingTheory.TensorProduct.Basic
import BrauerGroup.CentralSimple

universe u

open TensorProduct BigOperators

variable (A k : Type u) [Field k] [Ring A] [Algebra k A]

set_option maxHeartbeats 400000 in
theorem center_is_ext (hA : IsCentralSimple k A) [FiniteDimensional k A] :
    IsField (Subalgebra.center k A) := by
  obtain ⟨n, hn, D, hD1, hD2, ⟨iso⟩⟩ := @Wedderburn_Artin_algebra_version k A _ _ _ _ hA.2
  have : IsField (Subalgebra.center k D) := {
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
      · simp [Subtype.ext_iff, hd]
  }
  have e : Subalgebra.center k A ≃ₐ[k] Subalgebra.center k (Matrix (Fin n) (Fin n) D) :={
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
    commutes' := fun _ ↦ by simp only [Subalgebra.coe_algebraMap, AlgEquiv.commutes]; rfl
  }

  sorry