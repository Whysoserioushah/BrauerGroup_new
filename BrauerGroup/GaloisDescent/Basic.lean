import BrauerGroup.TensorOfTypePQ.VectorSpaceWithTensorOfTypePQ

suppress_compilation

open TensorProduct PiTensorProduct

universe u v

variable {k K : Type u} {p q : ℕ} [Field k] [Field K] [Algebra k K]
variable {V W : VectorSpaceWithTensorOfType.{u, u} k p q}

open VectorSpaceWithTensorOfType

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
