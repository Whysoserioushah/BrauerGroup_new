import BrauerGroup.ToSecond

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

section mul_inv

variable (a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) (ha : IsMulTwoCocycle a)

include ha in
lemma inv_in : IsMulTwoCocycle (a⁻¹) := fun σ1 σ2 σ3 ↦ by
  have := ha σ1 σ2 σ3
  simp only [Pi.inv_apply, smul_inv']
  apply_fun ((a (σ1 * σ2, σ3)) * · * (a (σ1, σ2 * σ3)))
  simp only [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  apply_fun ((a (σ1, σ2)) * · * (σ1 • a (σ2, σ3)))
  simp only [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one, mul_comm]
  nth_rw 2 [mul_comm]
  exact this.symm
  · intro k1 k2
    simp only [AlgEquiv.smul_units_def, mul_left_inj, mul_right_inj, imp_self]
  · intro k1 k2
    simp only [mul_left_inj, mul_right_inj, imp_self]

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

abbrev invCross : Type := CrossProduct (inv_in K F a ha)

instance : FiniteDimensional K (invCross K F a ha) := FiniteDimensional.right F K _

instance : FiniteDimensional K (CrossProduct ha)ᵐᵒᵖ := FiniteDimensional.right F K _

open MulOpposite CrossProduct in
def Basis_ofmop : Basis (K ≃ₐ[F] K) K (CrossProduct ha)ᵐᵒᵖ := .mk
  (v := fun σ => op (x_ ha σ).1) (by
    rw [linearIndependent_iff']
    intro J f hf σ hσ
    replace hf : ∑ i ∈ J, ι ha (f i) • (op (x_ ha i).1) = (0 : (CrossProduct ha)ᵐᵒᵖ) := hf
    replace hf : ∑ i ∈ J, op ⟨Pi.single i (f i)⟩ = (0 : (CrossProduct ha)ᵐᵒᵖ) := by
      rw [← hf]
      exact Finset.sum_congr rfl fun i _ => congrArg op $ identity_double_cross ha i (f i) |>.symm
    apply_fun AddMonoidHom.mulOp (valAddMonoidHom ha) at hf
    simp only [map_sum, AddMonoidHom.mulOp_apply_apply, Function.comp_apply, unop_op, unop_zero,
      map_zero, op_zero] at hf
    apply_fun unop at hf
    simp only [Finset.unop_sum, unop_op, unop_zero] at hf
    replace hf := congr_fun hf σ
    simp only [Finset.sum_apply, valAddMonoidHom_apply, Finset.sum_pi_single, Pi.zero_apply,
      ite_eq_else] at hf
    exact hf hσ) (by
    rintro ⟨x⟩ -
    induction x using single_induction ha with
    | single x cx =>
      have eq : (⟨Pi.single x cx⟩ : CrossProduct ha) = cx • ⟨Pi.single x 1⟩ := by
        change _ = ι ha _ * _
        rw [identity_double_cross]
      rw [eq]
      exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨x, rfl⟩
    | add x x' hx hx' => exact Submodule.add_mem _ hx hx'
    | zero => exact Submodule.zero_mem _)

@[simps! symm_apply apply]
abbrev KlinearEquiv : invCross K F a ha ≃ₗ[K] (CrossProduct ha)ᵐᵒᵖ :=
  Basis.equiv (CrossProduct.x_AsBasis (inv_in K F a ha)) (Basis_ofmop _ _ _ _) $ Equiv.refl _

def iso_op : invCross K F a ha ≃ₐ[F] (CrossProduct ha)ᵐᵒᵖ where
  __ := KlinearEquiv K F a ha
  map_mul' := fun (x y: CrossProduct (inv_in _ _ _ ha)) ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    -- have := Basis.repr (CrossProduct.x_AsBasis (inv_in _ _ _ ha)) x
    sorry
  commutes' := sorry

end mul_inv

-- instance : Mul (H2 (galAct F K)) := sorry

-- def IsoSecond : H2 (galAct F K) ≃* RelativeBrGroup K F := {
--   __ := RelativeBrGroup.equivSnd (F := F)|>.symm
--   map_mul' := sorry
-- }
