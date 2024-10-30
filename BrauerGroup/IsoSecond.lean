import BrauerGroup.ToSecond

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

open scoped TensorProduct

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

omit [IsGalois F K] in
@[simp]
lemma Basis_ofmop_apply (σ : K ≃ₐ[F] K):
    Basis_ofmop K F a ha σ = MulOpposite.op ⟨Pi.single σ 1⟩ := by
  simp only [Basis_ofmop, CrossProduct.x_, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    CrossProduct.Units.val_ofLeftRightInverse, Basis.coe_mk]


@[simps! symm_apply apply]
abbrev KlinearEquiv : invCross K F a ha ≃ₗ[K] (CrossProduct ha)ᵐᵒᵖ :=
  Basis.equiv (CrossProduct.x_AsBasis (inv_in K F a ha)) (Basis_ofmop _ _ _ _) $ Equiv.refl _

omit [IsGalois F K] in
lemma KlinearEquiv_apply' (σ : K ≃ₐ[F] K): KlinearEquiv K F a ha
    ((CrossProduct.x_AsBasis (inv_in K F a ha)) σ) = MulOpposite.op ⟨Pi.single σ 1⟩ := by
  rw [Basis.equiv_apply]
  simp only [Equiv.refl_apply, Basis_ofmop_apply]

-- variable [DecidableEq (K ≃ₐ[F] K)] in
open CrossProduct MulOpposite in
def iso_op : invCross K F a ha ≃ₐ[F] (CrossProduct ha)ᵐᵒᵖ where
  __ := KlinearEquiv K F a ha
  map_mul' := fun (x y: CrossProduct (inv_in _ _ _ ha)) ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    have := Basis.linearCombination_repr (CrossProduct.x_AsBasis (inv_in _ _ _ ha))
    -- have eq2 := Basis.linearCombination_repr (Basis_ofmop K F a ha)
    rw [← this x, ← this y]
    simp only [Finsupp.linearCombination_apply, x_AsBasis_apply, KlinearEquiv_apply,
      Basis_ofmop_apply]
    change ∑ _ ∈ _, _ = (∑ _ ∈ _, _) * (∑ _ ∈ _, _)
    apply_fun MulOpposite.unop using (fun a b hab ↦ MulOpposite.unop_inj.1 hab)
    simp only [map_sum, LinearMap.coe_mk, AddHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op,
      MulOpposite.unop_mul, Finset.unop_sum]
    -- calc _
    --   _ = ∑ σ ∈ Finset.univ, if σ ∈ ((x_AsBasis _).repr
    --       ((((x_AsBasis (inv_in K F a ha)).repr x).sum fun τ k ↦ k • ⟨Pi.single τ 1⟩) *
    --         ((x_AsBasis _).repr y).sum fun τ k ↦ k • ⟨Pi.single τ 1⟩)).support then
    --         ((x_AsBasis _).repr ((((x_AsBasis _).repr x).sum fun i a_1 ↦ a_1 • { val := Pi.single i 1 }) *
    --         ((x_AsBasis _).repr y).sum fun i a_1 ↦ a_1 • { val := Pi.single i 1 }))
    --         σ • { val := Pi.single x_1 1 } else 0 := by sorry
      -- _ = _ := sorry
    sorry
    -- rw [← Finsupp.linearCombination_apply, ← Finsupp.linearCombination_apply,
    --   ← Finsupp.linearCombination_apply, ← Finsupp.linearCombination_apply,
    --   ← Finsupp.linearCombination_apply, this x, this y]

    -- induction x using single_induction (inv_in K F a ha) with
    -- | single x k1 =>
    --   induction y using single_induction (inv_in K F a ha) with
    --   | single y k2 =>
    --     simp only [mul_def, crossProductMul_single_single, Pi.inv_apply, Units.val_inv_eq_inv_val]
    --     rw [KlinearEquiv_apply, KlinearEquiv_apply, KlinearEquiv_apply]
    --     simp only [Finsupp.linearCombination_apply]
    --     change ∑ _ ∈ _, _ = (∑ _ ∈ _, _) * (∑ _ ∈ _, _)
    --     simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_product']
    --     -- refine Finset.sum_congr ?_ ?_
    --     sorry
    --   | add y y' hy hy' => sorry
    --   | zero => sorry
    -- | add x x' hx hx' => sorry
    -- | zero => sorry

  commutes' := fun α ↦ by
    simp only [algebraMap_val, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearMap.map_smul_of_tower, LinearEquiv.coe_coe, MulOpposite.algebraMap_apply,
      MulOpposite.op_smul, op_one]
    change _ • (KlinearEquiv _ _ _ _) ⟨_⟩ = _
    simp only [Prod.mk_one_one, Pi.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
    rw [single_in_xAsBasis (inv_in K F a ha) (a 1).1 1, map_smul, KlinearEquiv_apply']
    apply_fun unop using fun _ _ h ↦ unop_inj.1 h
    simp only [unop_smul, unop_op, unop_one]
    congr
    apply val_injective ha
    simp only [CrossProduct.smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
      Units.val_inv_eq_inv_val, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
      IsUnit.mul_inv_cancel, crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
      _root_.one_mul, one_val, Pi.single_inj]
    have : a 1 = 1 := by sorry
    simp only [this, Units.val_one, inv_one]

end mul_inv

section map_mul

variable (a b: (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) (ha : IsMulTwoCocycle a) (hb : IsMulTwoCocycle b)
  [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

open CrossProduct


abbrev S : Set (CrossProduct ha ⊗[F] CrossProduct hb) :=
  {x : (CrossProduct ha ⊗[F] CrossProduct hb)|
    ∃(a : CrossProduct ha)(b : CrossProduct hb)(k : K), x = (k • a) ⊗ₜ b - a ⊗ₜ (k • b)}

omit [IsGalois F K] in
@[simp]
lemma mem_S (x : CrossProduct ha ⊗[F] CrossProduct hb) : x ∈ S K F a b ha hb ↔
  ∃(a : CrossProduct ha)(b : CrossProduct hb)(k : K), x = (k • a) ⊗ₜ b - a ⊗ₜ (k • b) := Iff.rfl

abbrev M := (CrossProduct ha ⊗[F] CrossProduct hb) ⧸ Submodule.span
  (CrossProduct ha ⊗[F] CrossProduct hb) (S K F a b ha hb)

instance : Module F (M K F a b ha hb) := inferInstance

def TensorSmul (aa : CrossProduct ha) (bb : CrossProduct hb) :
  (CrossProduct ha) ⊗[F] (CrossProduct hb) →ₗ[F] M K F a b ha hb :=
  let m := Submodule.Quotient.mk (R := CrossProduct ha ⊗[F] CrossProduct hb)
    (p := Submodule.span (CrossProduct ha ⊗[F] CrossProduct hb) (S K F a b ha hb)) (aa ⊗ₜ bb)
  TensorProduct.lift {
    toFun := fun a' ↦ {
      toFun := fun b' ↦ Submodule.Quotient.mk ((a' * aa) ⊗ₜ (b' * bb))
      map_add' := fun b1 b2 ↦ by simp only [Ideal.submodule_span_eq, add_mul,
        TensorProduct.tmul_add, Submodule.Quotient.mk_add]
      map_smul' := fun α bbb ↦ by simp only [Ideal.submodule_span_eq, Algebra.smul_mul_assoc,
        TensorProduct.tmul_smul, Submodule.Quotient.mk_smul, RingHom.id_apply]
    }
    map_add' := fun a1 a2 ↦ by
      ext bbb
      simp only [Ideal.submodule_span_eq, add_mul, TensorProduct.add_tmul,
        Submodule.Quotient.mk_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    map_smul' := fun α aaa ↦ by
      ext bbb
      simp only [Ideal.submodule_span_eq, Algebra.smul_mul_assoc, LinearMap.coe_mk, AddHom.coe_mk,
        RingHom.id_apply, LinearMap.smul_apply]
      rfl
  }


instance : Module (CrossProduct ha ⊗[F] CrossProduct hb) (M K F a b ha hb) where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

end map_mul