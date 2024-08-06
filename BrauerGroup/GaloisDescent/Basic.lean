import BrauerGroup.TensorOfTypePQ.VectorSpaceWithTensorOfTypePQ

suppress_compilation

open TensorProduct PiTensorProduct

variable {k K : Type*} {p q : ℕ} [Field k] [Field K] [Algebra k K]
variable {V W : VectorSpaceWithTensorOfType k p q}
variable {ιV ιW : Type*} (bV : Basis ιV k V) (bW : Basis ιW k W)

open VectorSpaceWithTensorOfType

set_option maxHeartbeats 500000 in

lemma indeucedByGalAux_comm (σ : K ≃ₐ[k] K)
    (f : V.extendScalars K bV ⟶ W.extendScalars K bW) :
    (TensorOfType.extendScalars K bW W.tensor ∘ₗ
      PiTensorProduct.map fun _ ↦ LinearMap.galAct σ f.toLinearMap) =
    (PiTensorProduct.map fun _ ↦ LinearMap.galAct σ f.toLinearMap) ∘ₗ
      TensorOfType.extendScalars K bV V.tensor := by
  apply_fun LinearMap.restrictScalars k using LinearMap.restrictScalars_injective k
  rw [LinearMap.restrictScalars_comp, LinearMap.restrictScalars_comp,
    VectorSpaceWithTensorOfType.galAct_tensor_power_eq, ← LinearMap.comp_assoc,
    VectorSpaceWithTensorOfType.galAct_tensor_power_eq]
  have := VectorSpaceWithTensorOfType.oneTMulPow_comm_sq bW σ.toAlgHom
  simp only [extendScalars_carrier, extendScalars_tensor, AlgEquiv.toAlgHom_eq_coe] at this
  set lhs := _; change lhs = _
  rw [show lhs = (AlgHom.oneTMulPow p bW ↑σ ∘ₗ LinearMap.restrictScalars k (TensorOfType.extendScalars K bW W.tensor)) ∘ₗ
      LinearMap.restrictScalars k (PiTensorProduct.map fun _ ↦ f.toLinearMap) ∘ₗ
      AlgHom.oneTMulPow q bV σ.symm.toAlgHom by
    simp only [AlgEquiv.toAlgHom_eq_coe, extendScalars_carrier, lhs]
    rw [this]]
  clear lhs
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (f := AlgHom.oneTMulPow q bV _)]
  have eq := congr(LinearMap.restrictScalars k $f.comm)
  simp only [extendScalars_carrier, extendScalars_tensor, LinearMap.restrictScalars_comp] at eq
  rw [eq]
  rw [LinearMap.comp_assoc]
  have := VectorSpaceWithTensorOfType.oneTMulPow_comm_sq bV σ.symm.toAlgHom
  simp only [extendScalars_carrier, extendScalars_tensor, AlgEquiv.toAlgHom_eq_coe] at this
  set lhs := _; change lhs = _
  rw [show lhs = AlgHom.oneTMulPow p bW ↑σ ∘ₗ
      LinearMap.restrictScalars k (PiTensorProduct.map fun _ ↦ f.toLinearMap) ∘ₗ
      AlgHom.oneTMulPow p bV ↑σ.symm ∘ₗ
      LinearMap.restrictScalars k (TensorOfType.extendScalars K bV V.tensor) by
    simp only [AlgEquiv.toAlgHom_eq_coe, extendScalars_carrier, lhs]
    rw [this]]
  clear lhs
  simp only [extendScalars_carrier, ← LinearMap.comp_assoc]
  rfl

def inducedByGal (σ : K ≃ₐ[k] K) (f : V.extendScalars K bV ⟶ W.extendScalars K bW) :
    V.extendScalars K bV ⟶ W.extendScalars K bW where
  __ :=   LinearMap.galAct σ f.toLinearMap
  comm := by
    simp only [extendScalars_carrier, extendScalars_tensor]
    apply indeucedByGalAux_comm
