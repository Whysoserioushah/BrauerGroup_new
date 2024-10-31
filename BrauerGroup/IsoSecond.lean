import BrauerGroup.ToSecond

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

open scoped TensorProduct

section map_one

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

def φ0 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₗ[K]
    Module.End F K :=
  (CrossProduct.x_AsBasis (F := F) (K := K) (a := 1) (isMulTwoCocycle_of_twoCocycles 0)).constr F
    fun σ => σ.toLinearMap

def φ1 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₗ[F]
    Module.End F K :=
  φ0 K F |>.restrictScalars F

def φ2 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₐ[F]
    Module.End F K :=
  AlgHom.ofLinearMap (φ1 K F)
    (by
      generalize_proofs h
      rw [show (1 : CrossProduct h) = .x_AsBasis h 1 by
        ext1
        simp]
      delta φ1 φ0
      rw [LinearMap.restrictScalars_apply, Basis.constr_basis]
      rfl)
    (by
      rintro x y
      change φ0 K F _ = φ0 K F _ * φ0 K F _
      generalize_proofs h
      induction x using CrossProduct.single_induction h with
      | single x c =>
        rw [show (⟨Pi.single x c⟩ : CrossProduct h) =
          c • .x_AsBasis h x by
          ext : 1
          simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
            CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
            crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
        rw [map_smul]
        induction y using CrossProduct.single_induction h with
        | single y d =>
          rw [show (⟨Pi.single y d⟩ : CrossProduct h) =
            d • .x_AsBasis h y by
            ext : 1
            simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
              CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
              crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
          rw [show (c • CrossProduct.x_AsBasis h x) * (d • .x_AsBasis h y) =
            (c * x d) • .x_AsBasis h (x * y) by
            ext : 1
            simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
              CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
              crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply, map_mul]]
          rw [map_smul, map_smul]
          delta φ0
          rw [Basis.constr_basis, Basis.constr_basis, Basis.constr_basis]
          ext α
          simp only [LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.mul_apply,
            smul_eq_mul, _root_.mul_assoc, LinearMap.mul_apply, map_mul]
        | add y y' hy hy' =>
          erw [mul_add]
          rw [map_add, hy, hy']
          erw [map_add]
          rw [mul_add]
        | zero =>
          erw [mul_zero]
          rw [map_zero]
          erw [map_zero]
          rw [mul_zero]
      | add x x' hx hx' =>
        erw [add_mul]
        rw [map_add, hx, hx']
        erw [map_add]
        rw [add_mul]
      | zero =>
        erw [zero_mul]
        rw [map_zero]
        erw [map_zero]
        rw [zero_mul])

def φ3 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
    Module.End F K :=
  AlgEquiv.ofBijective (φ2 K F) (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by
    rw [CrossProduct.dim_eq_square]
    rw [finrank_linearMap, pow_two])

def φ4 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
    Matrix (Fin <| finrank F K) (Fin <| finrank F K) F :=
  φ3 K F |>.trans <| LinearMap.toMatrixAlgEquiv <| finBasis F K

lemma map_one' : RelativeBrGroup.fromTwoCocycles (F := F) (K := K) (a := 0) = 1 := by
  ext1
  change Quotient.mk'' _ = Quotient.mk'' _
  erw [Quotient.eq'']
  have : 0 < finrank F K := finrank_pos
  change IsBrauerEquivalent _ _
  refine ⟨1, finrank F K, by positivity, by positivity, AlgEquiv.trans ?_ <| φ4 K F⟩
  exact dim_one_iso (CSA.mk (CrossProduct.asCSA ⋯).carrier).carrier

lemma fromSnd_zero : RelativeBrGroup.fromSnd (F := F) (K := K) 0 = 1 := map_one' K F

end map_one

-- section mul_inv

-- variable (a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) (ha : IsMulTwoCocycle a)

-- include ha in
-- lemma inv_in : IsMulTwoCocycle (a⁻¹) := fun σ1 σ2 σ3 ↦ by
--   have := ha σ1 σ2 σ3
--   simp only [Pi.inv_apply, smul_inv']
--   apply_fun ((a (σ1 * σ2, σ3)) * · * (a (σ1, σ2 * σ3)))
--   simp only [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
--   rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
--   apply_fun ((a (σ1, σ2)) * · * (σ1 • a (σ2, σ3)))
--   simp only [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
--   rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one, mul_comm]
--   nth_rw 2 [mul_comm]
--   exact this.symm
--   · intro k1 k2
--     simp only [AlgEquiv.smul_units_def, mul_left_inj, mul_right_inj, imp_self]
--   · intro k1 k2
--     simp only [mul_left_inj, mul_right_inj, imp_self]

-- variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

-- abbrev invCross : Type := CrossProduct (inv_in K F a ha)

-- instance : FiniteDimensional K (invCross K F a ha) := FiniteDimensional.right F K _

-- instance : FiniteDimensional K (CrossProduct ha)ᵐᵒᵖ := FiniteDimensional.right F K _

-- open MulOpposite CrossProduct in
-- def Basis_ofmop : Basis (K ≃ₐ[F] K) K (CrossProduct ha)ᵐᵒᵖ := .mk
--   (v := fun σ => op (x_ ha σ).1) (by
--     rw [linearIndependent_iff']
--     intro J f hf σ hσ
--     replace hf : ∑ i ∈ J, ι ha (f i) • (op (x_ ha i).1) = (0 : (CrossProduct ha)ᵐᵒᵖ) := hf
--     replace hf : ∑ i ∈ J, op ⟨Pi.single i (f i)⟩ = (0 : (CrossProduct ha)ᵐᵒᵖ) := by
--       rw [← hf]
--       exact Finset.sum_congr rfl fun i _ => congrArg op $ identity_double_cross ha i (f i) |>.symm
--     apply_fun AddMonoidHom.mulOp (valAddMonoidHom ha) at hf
--     simp only [map_sum, AddMonoidHom.mulOp_apply_apply, Function.comp_apply, unop_op, unop_zero,
--       map_zero, op_zero] at hf
--     apply_fun unop at hf
--     simp only [Finset.unop_sum, unop_op, unop_zero] at hf
--     replace hf := congr_fun hf σ
--     simp only [Finset.sum_apply, valAddMonoidHom_apply, Finset.sum_pi_single, Pi.zero_apply,
--       ite_eq_else] at hf
--     exact hf hσ) (by
--     rintro ⟨x⟩ -
--     induction x using single_induction ha with
--     | single x cx =>
--       have eq : (⟨Pi.single x cx⟩ : CrossProduct ha) = cx • ⟨Pi.single x 1⟩ := by
--         change _ = ι ha _ * _
--         rw [identity_double_cross]
--       rw [eq]
--       exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨x, rfl⟩
--     | add x x' hx hx' => exact Submodule.add_mem _ hx hx'
--     | zero => exact Submodule.zero_mem _)

-- omit [IsGalois F K] in
-- @[simp]
-- lemma Basis_ofmop_apply (σ : K ≃ₐ[F] K):
--     Basis_ofmop K F a ha σ = MulOpposite.op ⟨Pi.single σ 1⟩ := by
--   simp only [Basis_ofmop, CrossProduct.x_, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
--     CrossProduct.Units.val_ofLeftRightInverse, Basis.coe_mk]


-- @[simps! symm_apply apply]
-- abbrev KlinearEquiv : invCross K F a ha ≃ₗ[K] (CrossProduct ha)ᵐᵒᵖ :=
--   Basis.equiv (CrossProduct.x_AsBasis (inv_in K F a ha)) (Basis_ofmop _ _ _ _) $ Equiv.refl _

-- omit [IsGalois F K] in
-- lemma KlinearEquiv_apply' (σ : K ≃ₐ[F] K): KlinearEquiv K F a ha
--     ((CrossProduct.x_AsBasis (inv_in K F a ha)) σ) = MulOpposite.op ⟨Pi.single σ 1⟩ := by
--   rw [Basis.equiv_apply]
--   simp only [Equiv.refl_apply, Basis_ofmop_apply]

-- -- variable [DecidableEq (K ≃ₐ[F] K)] in
-- open CrossProduct MulOpposite in
-- def iso_op : invCross K F a ha ≃ₐ[F] (CrossProduct ha)ᵐᵒᵖ where
--   __ := KlinearEquiv K F a ha
--   map_mul' := fun (x y: CrossProduct (inv_in _ _ _ ha)) ↦ by
--     simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
--     have := Basis.linearCombination_repr (CrossProduct.x_AsBasis (inv_in _ _ _ ha))
--     -- have eq2 := Basis.linearCombination_repr (Basis_ofmop K F a ha)
--     rw [← this x, ← this y]
--     simp only [Finsupp.linearCombination_apply, x_AsBasis_apply, KlinearEquiv_apply,
--       Basis_ofmop_apply]
--     change ∑ _ ∈ _, _ = (∑ _ ∈ _, _) * (∑ _ ∈ _, _)
--     apply_fun MulOpposite.unop using (fun a b hab ↦ MulOpposite.unop_inj.1 hab)
--     simp only [map_sum, LinearMap.coe_mk, AddHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op,
--       MulOpposite.unop_mul, Finset.unop_sum]
--     -- calc _
--     --   _ = ∑ σ ∈ Finset.univ, if σ ∈ ((x_AsBasis _).repr
--     --       ((((x_AsBasis (inv_in K F a ha)).repr x).sum fun τ k ↦ k • ⟨Pi.single τ 1⟩) *
--     --         ((x_AsBasis _).repr y).sum fun τ k ↦ k • ⟨Pi.single τ 1⟩)).support then
--     --         ((x_AsBasis _).repr ((((x_AsBasis _).repr x).sum fun i a_1 ↦ a_1 • { val := Pi.single i 1 }) *
--     --         ((x_AsBasis _).repr y).sum fun i a_1 ↦ a_1 • { val := Pi.single i 1 }))
--     --         σ • { val := Pi.single x_1 1 } else 0 := by sorry
--       -- _ = _ := sorry
--     sorry
--     -- rw [← Finsupp.linearCombination_apply, ← Finsupp.linearCombination_apply,
--     --   ← Finsupp.linearCombination_apply, ← Finsupp.linearCombination_apply,
--     --   ← Finsupp.linearCombination_apply, this x, this y]

--     -- induction x using single_induction (inv_in K F a ha) with
--     -- | single x k1 =>
--     --   induction y using single_induction (inv_in K F a ha) with
--     --   | single y k2 =>
--     --     simp only [mul_def, crossProductMul_single_single, Pi.inv_apply, Units.val_inv_eq_inv_val]
--     --     rw [KlinearEquiv_apply, KlinearEquiv_apply, KlinearEquiv_apply]
--     --     simp only [Finsupp.linearCombination_apply]
--     --     change ∑ _ ∈ _, _ = (∑ _ ∈ _, _) * (∑ _ ∈ _, _)
--     --     simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_product']
--     --     -- refine Finset.sum_congr ?_ ?_
--     --     sorry
--     --   | add y y' hy hy' => sorry
--     --   | zero => sorry
--     -- | add x x' hx hx' => sorry
--     -- | zero => sorry

--   commutes' := fun α ↦ by
--     simp only [algebraMap_val, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
--       LinearMap.map_smul_of_tower, LinearEquiv.coe_coe, MulOpposite.algebraMap_apply,
--       MulOpposite.op_smul, op_one]
--     change _ • (KlinearEquiv _ _ _ _) ⟨_⟩ = _
--     simp only [Prod.mk_one_one, Pi.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
--     rw [single_in_xAsBasis (inv_in K F a ha) (a 1).1 1, map_smul, KlinearEquiv_apply']
--     apply_fun unop using fun _ _ h ↦ unop_inj.1 h
--     simp only [unop_smul, unop_op, unop_one]
--     congr
--     apply val_injective ha
--     simp only [CrossProduct.smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
--       Units.val_inv_eq_inv_val, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
--       IsUnit.mul_inv_cancel, crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
--       _root_.one_mul, one_val, Pi.single_inj]
--     have : a 1 = 1 := by sorry
--     simp only [this, Units.val_one, inv_one]

-- -- def TensorK : GoodRep (F := F) K 1 where
-- --   carrier := {
-- --     carrier := K ⊗[F] K
-- --     is_central_simple := {
-- --       is_central := _
-- --       is_simple :=
-- --     }
-- --     fin_dim := _
-- --   }
-- --   quot_eq := _
-- --   ι := _
-- --   dim_eq_square := _

-- end mul_inv

section map_mul

variable (a b: (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) (ha : IsMulTwoCocycle a) (hb : IsMulTwoCocycle b)
  [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

open CrossProduct TensorProduct


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

include ha hb in
omit [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)] in
lemma mulab : IsMulTwoCocycle (a * b) := by
  unfold IsMulTwoCocycle
  intro σ1 σ2 σ3
  simp only [Pi.mul_apply]
  replace ha := (ha σ1 σ2 σ3)
  replace hb := (hb σ1 σ2 σ3)
  rw [_root_.mul_assoc, ← _root_.mul_assoc (b (σ1 * σ2, _)), mul_comm (b _),
    ← _root_.mul_assoc, ← _root_.mul_assoc, ha, _root_.mul_assoc, hb]
  simp only [AlgEquiv.smul_units_def, smul_mul']
  apply_fun (((Units.map ↑σ1) (a (σ2, σ3)))⁻¹ * · ) using
    fun k1 k2 h12 ↦ mul_right_inj ((Units.map ↑σ1) (a (σ2, σ3)))⁻¹ |>.1 h12
  simp only
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← _root_.mul_assoc,
    inv_mul_cancel, _root_.one_mul, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]
  congr 1
  exact mul_comm _ _

-- def TensorSmul (aa : CrossProduct ha) (bb : CrossProduct hb) :
--   (CrossProduct ha) ⊗[F] (CrossProduct hb) →ₗ[F] M K F a b ha hb :=
--   -- let m := Submodule.Quotient.mk (R := CrossProduct ha ⊗[F] CrossProduct hb)
--   --   (p := Submodule.span (CrossProduct ha ⊗[F] CrossProduct hb) (S K F a b ha hb)) (aa ⊗ₜ bb)
--   TensorProduct.lift {
--     toFun := fun a' ↦ {
--       toFun := fun b' ↦ Submodule.Quotient.mk ((a' * aa) ⊗ₜ (b' * bb))
--       map_add' := fun b1 b2 ↦ by simp only [Ideal.submodule_span_eq, add_mul,
--         TensorProduct.tmul_add, Submodule.Quotient.mk_add]
--       map_smul' := fun α bbb ↦ by simp only [Ideal.submodule_span_eq, Algebra.smul_mul_assoc,
--         TensorProduct.tmul_smul, Submodule.Quotient.mk_smul, RingHom.id_apply]
--     }
--     map_add' := fun a1 a2 ↦ by
--       ext bbb
--       simp only [Ideal.submodule_span_eq, add_mul, TensorProduct.add_tmul,
--         Submodule.Quotient.mk_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
--     map_smul' := fun α aaa ↦ by
--       ext bbb
--       simp only [Ideal.submodule_span_eq, Algebra.smul_mul_assoc, LinearMap.coe_mk, AddHom.coe_mk,
--         RingHom.id_apply, LinearMap.smul_apply]
--       rfl
--   }

instance : Module (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ
  (CrossProduct ha ⊗[F] CrossProduct hb) := inferInstance

set_option synthInstance.maxHeartbeats 40000 in
instance : Module (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ
    (Submodule.span (CrossProduct ha ⊗[F] CrossProduct hb) (S K F a b ha hb)) :=
  -- inferInstance
  sorry

instance : IsScalarTower (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ (CrossProduct ha ⊗[F] CrossProduct hb)
    (CrossProduct ha ⊗[F] CrossProduct hb) where
  smul_assoc xop x y := by
    simp only [MulOpposite.smul_eq_mul_unop, smul_eq_mul]
    sorry

instance : Module (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ (M K F a b ha hb) :=
  Submodule.Quotient.module' _

local notation "u" => x_AsBasis ha

local notation "v" => x_AsBasis hb

local notation "w" => x_AsBasis (mulab K F a b ha hb)

-- abbrev smulTensor (σ : (K ≃ₐ[F] K)) (k : K) : (CrossProduct ha) ⊗[F] (CrossProduct hb)
--     →ₗ[F] (CrossProduct ha) ⊗[F] (CrossProduct hb) := TensorProduct.lift {
--   toFun := fun a ↦ {
--     toFun := fun b ↦ (k • u σ * a) ⊗ₜ (v σ * b)
--     map_add' := fun x y ↦ by simp only [x_AsBasis_apply, mul_add, tmul_add]
--     map_smul' := fun α x ↦ by
--       simp only [RingHom.id_apply, smul_tmul', smul_tmul]
--       congr 1
--       exact mul_smul_comm α (v σ) x }
--   map_add' := fun a1 a2 ↦ by
--     ext b
--     simp only [x_AsBasis_apply, mul_add, add_tmul, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.add_apply]
--   map_smul' := fun α a ↦ by
--     ext b
--     simp only [x_AsBasis_apply, Algebra.mul_smul_comm, LinearMap.coe_mk,
--       AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
--     congr 1  }
-- #check Basis.constr

abbrev smulsmul (aa : CrossProduct ha) (bb : CrossProduct hb) :
    CrossProduct (mulab K F a b ha hb) →ₗ[K]
    (CrossProduct ha) ⊗[F] (CrossProduct hb) :=
  Basis.constr (ι := (K ≃ₐ[F] K)) (S := F) (R := K) w $ fun σ =>
    (u σ * aa) ⊗ₜ (v σ * bb)

abbrev smulLinear : (CrossProduct ha) ⊗[F] (CrossProduct hb) →ₗ[F]
    CrossProduct (mulab K F a b ha hb) →ₗ[K]
    (CrossProduct ha) ⊗[F] (CrossProduct hb) := TensorProduct.lift {
    toFun := fun aa ↦ {
      toFun := fun bb ↦ smulsmul K F a b ha hb aa bb
      map_add' := fun b1 b2 ↦ by
        simp only
        ext aabb
        simp only [Basis.constr_apply_fintype, Basis.equivFun_apply,
          x_AsBasis_apply, mul_add, tmul_add, smul_add,
          Finset.sum_add_distrib, LinearMap.add_apply]
      map_smul' := sorry
    }
    map_add' := sorry
    map_smul' := sorry
  }

instance : Module (CrossProduct (mulab K F a b ha hb))
    (CrossProduct ha ⊗[F] CrossProduct hb) := sorry

instance : Module (CrossProduct (mulab K F a b ha hb)) (M K F a b ha hb) := sorry

end map_mul
