import BrauerGroup.TensorOfTypePQ.VectorSpaceWithTensorOfTypePQ

suppress_compilation

open TensorProduct PiTensorProduct

universe u v

variable {k K : Type u} {p q : ℕ} [Field k] [Field K] [Algebra k K]
variable {V W : VectorSpaceWithTensorOfType.{u, u} k p q}

open VectorSpaceWithTensorOfType

#exit
-- attribute [-simp] Basis.coe_ofVectorSpace in
lemma indeucedByGalAux_comm (σ : K ≃ₐ[k] K)
    (f : V.extendScalars K ⟶ W.extendScalars K) :
    (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor ∘ₗ
      PiTensorProduct.map fun x ↦ LinearMap.galAct σ f.toLinearMap) =
    (PiTensorProduct.map fun x ↦ LinearMap.galAct σ f.toLinearMap) ∘ₗ
      TensorOfType.extendScalars K (Basis.ofVectorSpace k V.carrier) V.tensor := by
  set bW := Algebra.TensorProduct.basis K (Basis.ofVectorSpace k W.carrier) with bW_eq
  fapply Basis.ext (b := Basis.tensorPowerExtendScalars K q (Basis.ofVectorSpace k V))
  intro v
  simp only [Basis.tensorPowerExtendScalars_apply, Basis.coe_ofVectorSpace, LinearMap.coe_comp,
    Function.comp_apply, map_tprod, LinearMap.galAct_extendScalars_apply, _root_.map_one]
  have eq₁ (i : Fin q) : f.toLinearMap (1 ⊗ₜ[k] (v i)) = _ :=
    (bW.total_repr (f.toLinearMap (1 ⊗ₜ[k] (v i)))).symm
  dsimp only [extendScalars_carrier, Finsupp.total, Finsupp.lsum, Finsupp.sum, LinearEquiv.coe_mk,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, LinearMap.coe_mk, AddHom.coe_mk] at eq₁
  have eq₂: (tprod K fun i ↦ LinearMap.rTensor W σ.toLinearMap (f.toLinearMap (1 ⊗ₜ[k] (v i)))) =
      tprod K fun i ↦ LinearMap.rTensor W σ.toLinearMap $
        ∑ a ∈ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] (v i)))).support,
          (bW.repr (f.toLinearMap (1 ⊗ₜ[k] (v i)))) a • bW a := by
    congr; ext x;
    conv_lhs => erw [eq₁ x]
    rfl
  erw [eq₂]
  simp only [extendScalars_carrier, Algebra.TensorProduct.basis_apply, Basis.coe_ofVectorSpace,
    map_sum, bW]
  simp only [← bW_eq]
  simp only [smul_tmul', smul_eq_mul, mul_one, LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply]
  rw [MultilinearMap.map_sum_finset, map_sum]
  have := TensorOfType.extendScalars_apply_tmul (K := K) (b := Basis.ofVectorSpace k W)
    (f := W.tensor)
  simp only [Basis.coe_ofVectorSpace, LinearEquiv.coe_coe] at this
  simp_rw [this]
  -- have eq₃ (x : Fin q → Basis.ofVectorSpaceIndex k W.carrier) :
  --   (∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] (v i)))) (x i))) ⊗ₜ[k]
  --     W.tensor ((tprod k) fun i ↦ ↑(x i)) =
  --   (∏ i : Fin q, σ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] v i)) (x i))) •
  --   (1 ⊗ₜ[k] W.tensor (tprod k fun i ↦ x i)) := by simp only [extendScalars_carrier,
  --     smul_tmul', smul_eq_mul, mul_one]
  have eq₃ : ∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
    (Basis.extendScalarsTensorPowerEquiv K p (Basis.ofVectorSpace k W.carrier))
      ((∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) ⊗ₜ[k]
        W.tensor ((tprod k) fun i ↦ ↑(x i))) =
    ∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
    (Basis.extendScalarsTensorPowerEquiv K p (Basis.ofVectorSpace k W.carrier))
      ((∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) •
      1 ⊗ₜ[k] W.tensor ((tprod k) fun i ↦ ↑(x i))) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    congr 1
    simp only [extendScalars_carrier, smul_tmul', smul_eq_mul, mul_one]
  erw [eq₃]
  simp_rw [map_smul]
  /-
  ∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
    (∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) •
      (Basis.extendScalarsTensorPowerEquiv K p (Basis.ofVectorSpace k W.carrier))
        ((LinearMap.extendScalars K W.tensor) (1 ⊗ₜ[k] (tprod k) fun i ↦ ↑(x i)))
  -/
  simp_rw [← LinearMap.extendScalars_apply]
  have := TensorOfType.extendScalarsTensorPowerEquiv_comp_elementwise
    (K := K) (bV := Basis.ofVectorSpace k W) (f := W.tensor)
  simp only [LinearEquiv.coe_coe] at this
  simp_rw [this]
  clear this
  set lhs := _; change lhs = _
  rw [show lhs =
  ∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,

    (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor)
      ((Basis.extendScalarsTensorPowerEquiv K q (Basis.ofVectorSpace k W.carrier))
      ((∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) ⊗ₜ[k]
        ((tprod k) fun i ↦ (x i)))) from sorry,
    ← map_sum, ← map_sum]
  set X : K ⊗[k] ⨂[k]^q W.carrier :=
    (∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
        (∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) ⊗ₜ[k]
        (tprod k) fun i ↦ (x i))
  have := LinearMap.rTensor (⨂[k]^q W.carrier) σ.toLinearMap
  have eqX : (LinearMap.rTensor (⨂[k]^q W.carrier) σ.symm.toLinearMap) X =
      (Basis.extendScalarsTensorPowerEquiv K q (Basis.ofVectorSpace k W.carrier)).symm
      ((PiTensorProduct.map fun x ↦ f.toLinearMap) (tprod _ fun i => 1 ⊗ₜ[k] ↑(v i))) := by
    simp only [extendScalars_carrier, map_sum, LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply,
      map_prod, AlgEquiv.symm_apply_apply, map_tprod, X]
    erw [show ((tprod K) fun i ↦ f.toLinearMap ((1 : K) ⊗ₜ[k] ↑(v i))) =
      tprod K fun i => ∑ a ∈ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
        (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) a • bW a by
      congr
      ext j
      conv_lhs => erw [eq₁]
      rfl]
    rw [MultilinearMap.map_sum_finset, map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [MultilinearMap.map_smul_univ]
    simp only [extendScalars_carrier, Algebra.TensorProduct.basis_apply, Basis.coe_ofVectorSpace,
      LinearMapClass.map_smul, bW]
    have := Basis.extendScalarsTensorPowerEquiv_symm_apply (p := q) (b := Basis.ofVectorSpace k W)
      (K := K)
    simp only [Basis.coe_ofVectorSpace] at this
    rw [this]
    simp [← bW_eq, smul_tmul']

  apply_fun  (LinearMap.rTensor (⨂[k]^q W.carrier) σ.toLinearMap) at eqX
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp] at eqX
  simp only [extendScalars_carrier] at eqX
  rw [show σ.toLinearMap ∘ₗ σ.symm.toLinearMap = LinearMap.id by
    ext; simp, LinearMap.rTensor_id, LinearMap.id_apply] at eqX
  rw [eqX, ← LinearMap.comp_apply]
  change (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor ∘ₗ _) _ = _
  sorry

  #exit
  change (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor)
    ((Basis.extendScalarsTensorPowerEquiv K q (Basis.ofVectorSpace k W.carrier)) X) = _
  have f_comm :
    (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor ∘ₗ
      PiTensorProduct.map fun x ↦ f.toLinearMap) =
    (PiTensorProduct.map fun x ↦ f.toLinearMap) ∘ₗ
      TensorOfType.extendScalars K (Basis.ofVectorSpace k V.carrier) V.tensor := f.comm
  have eq₄ := DFunLike.congr_fun f_comm
  simp only [extendScalars_carrier, LinearMap.coe_comp, Function.comp_apply] at eq₄
  sorry

  #exit
  have := Basis.extendScalarsTensorPowerEquiv_apply (p := q) (b := Basis.ofVectorSpace k W) (K := K)
  simp only [Basis.coe_ofVectorSpace] at this
  set lhs := _; change lhs = _
  rw [show lhs =
    ∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
    (∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) •
      (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor)
        ((tprod K) fun j ↦ 1 ⊗ₜ[k] ↑(x j)) from Finset.sum_congr rfl fun x hx => by rw [this]]
  clear lhs
  have := TensorOfType.extendScalars_apply_one_tmul (f := W.tensor) (K := K)
    (b := Basis.ofVectorSpace k W)
  simp only [Basis.coe_ofVectorSpace, LinearEquiv.coe_coe] at this
  set lhs := _; change lhs = _
  rw [show lhs =
    ∑ x ∈ Fintype.piFinset fun i ↦ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))).support,
  (∏ i : Fin q, σ ((bW.repr (f.toLinearMap (1 ⊗ₜ[k] ↑(v i)))) (x i))) •
    (Basis.extendScalarsTensorPowerEquiv K p (Basis.ofVectorSpace k W.carrier))
      (1 ⊗ₜ[k] W.tensor ((tprod k) fun i ↦ ↑(x i))) from Finset.sum_congr rfl fun x hx => by
      rw [this]]
  simp_rw [← LinearMap.extendScalars_apply]

  sorry

  #exit


  -- unfold TensorOfType.extendScalars TensorOfType.extendScalarsLinearMap
  -- simp only [LinearMap.coe_mk, AddHom.coe_mk, ← bW_eq]
  -- simp_rw [TensorOfType.extendScalarsLinearMapToFun_apply_tmul]
  -- simp only [LinearEquiv.coe_coe, Finset.prod_const_one]
  have f_comm :
    (TensorOfType.extendScalars K (Basis.ofVectorSpace k W.carrier) W.tensor ∘ₗ
      PiTensorProduct.map fun x ↦ f.toLinearMap) =
    (PiTensorProduct.map fun x ↦ f.toLinearMap) ∘ₗ
      TensorOfType.extendScalars K (Basis.ofVectorSpace k V.carrier) V.tensor := f.comm

  have eq₃ (x : Fin q → Basis.ofVectorSpaceIndex k W.carrier) :=
    DFunLike.congr_fun f_comm
      (tprod K fun i =>
        σ (bW.repr (f.toLinearMap (1 ⊗ₜ[k] (Basis.ofVectorSpace k V.carrier) (v i))) (x i)) ⊗ₜ[k]
        _)
  -- simp_rw [LinearMap.rTensor_tmul]
  -- have := f.comm
  -- have := LinearMap.galAct_extendScalars_apply'
  sorry


def inducedByGal (σ : K ≃ₐ[k] K) (f : V.extendScalars K ⟶ W.extendScalars K) :
    V.extendScalars K ⟶ W.extendScalars K where
  __ :=   LinearMap.galAct σ f.toLinearMap
  comm := by
    simp only [extendScalars_carrier, extendScalars_tensor]
    apply indeucedByGalAux_comm


#exit

lemma indeucedByGalAux_comm_lemma1 (ι : Type*) (b : Basis ι k V) (σ : K ≃ₐ[k] K) (f : V ⟶ W)
    (v : Fin q → ι) :
    (PiTensorProduct.map fun _ ↦ LinearMap.galAct σ (f.toLinearMap.extendScalars K) :
      (⨂[K]^q (K ⊗[k] V)) →ₗ[K] ⨂[K]^q (K ⊗[k] W))
      (tprod K fun j => 1 ⊗ₜ b (v j)) =
    tprod K fun j => 1 ⊗ₜ f (b (v j)) := by
  simp only [map_tprod, LinearMap.galAct_extendScalars_apply]
  rfl

lemma indeucedByGalAux_comm_lemma2 (ι : Type*) (b : Basis ι k V)  (f : V ⟶ W) (v : Fin q → ι) :
    (PiTensorProduct.map fun _ ↦ (f.toLinearMap.extendScalars K) :
      (⨂[K]^q (K ⊗[k] V)) →ₗ[K] ⨂[K]^q (K ⊗[k] W))
      (tprod K fun j => 1 ⊗ₜ b (v j)) =
    tprod K fun j => 1 ⊗ₜ f (b (v j)) := by
  simp only [map_tprod, LinearMap.extendScalars_apply]
  rfl


attribute [-simp] Basis.coe_ofVectorSpace in
lemma indeucedByGalAux_comm (σ : K ≃ₐ[k] K) (f : V ⟶ W) :
    (TensorOfType.extendScalars K (Basis.ofVectorSpace k W) W.tensor ∘ₗ
      PiTensorProduct.map fun _ ↦ LinearMap.galAct σ (f.toLinearMap.extendScalars K)) =
    (PiTensorProduct.map fun _ ↦ LinearMap.galAct σ (f.toLinearMap.extendScalars K)) ∘ₗ
      TensorOfType.extendScalars K (Basis.ofVectorSpace k V) V.tensor := by
  fapply Basis.ext (b := Basis.tensorPowerExtendScalars K q (Basis.ofVectorSpace k V))
  intro v
  conv_lhs => rw [Basis.tensorPowerExtendScalars_apply, LinearMap.comp_apply,
    indeucedByGalAux_comm_lemma1, ← indeucedByGalAux_comm_lemma2, ← LinearMap.comp_apply,
    VectorSpaceWithTensorOfType.extendScalars_map_comm]
  conv_rhs => rw [Basis.tensorPowerExtendScalars_apply]
  set G := TensorOfType.extendScalars K (Basis.ofVectorSpace k V.carrier) V.tensor
  set F := (PiTensorProduct.map fun _ ↦ LinearMap.extendScalars K f.toLinearMap)
  set F' := (PiTensorProduct.map fun _ ↦ LinearMap.galAct σ
    (LinearMap.extendScalars K f.toLinearMap))
  set x := (tprod K) fun j ↦ (1 : K) ⊗ₜ[k] (Basis.ofVectorSpace k V.carrier) (v j)
  set B := Basis.tensorPowerExtendScalars K p (Basis.ofVectorSpace k V)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [← B.total_repr (G x)]
  simp only [Finsupp.total, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, map_sum, map_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  simp only [Basis.tensorPowerExtendScalars_apply, map_tprod, LinearMap.extendScalars_apply,
    LinearMap.galAct_extendScalars_apply, F, B, F']

def inducedByGal (σ : K ≃ₐ[k] K) (f : V ⟶ W) : V.extendScalars K ⟶ W.extendScalars K where
  __ :=   LinearMap.galAct σ (f.toLinearMap.extendScalars K)
  comm := by
    simp only [VectorSpaceWithTensorOfType.extendScalars_carrier,
      VectorSpaceWithTensorOfType.extendScalars_tensor]
    apply indeucedByGalAux_comm
