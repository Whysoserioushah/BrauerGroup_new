import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.TensorPower

universe u v

section

variable (k : Type u) (V : Type v) [CommSemiring k] [AddCommMonoid V] [Module k V]

open TensorProduct PiTensorProduct

noncomputable def dualTensorPower (p : ℕ) :
    (⨂[k]^p $ Module.Dual k V) →ₗ[k] Module.Dual k (⨂[k]^p V) :=
  PiTensorProduct.lift
  { toFun := fun f => PiTensorProduct.lift
      { toFun := fun v => ∏ i : Fin p, f i (v i)
        map_add' := by
          intros _ v i x₁ x₂
          simp only
          have (j : Fin p) : f j (Function.update v i (x₁ + x₂) j) =
              Function.update (fun i => f i (v i)) i (f j x₁ + f j x₂) j := by
            simp only [Function.update, eq_rec_constant, dite_eq_ite]
            aesop
          simp_rw [this]; clear this
          have (j : Fin p) : f j (Function.update v i x₁ j) =
              Function.update (fun i => f i (v i)) i (f j x₁) j := by
            simp only [Function.update, eq_rec_constant, dite_eq_ite]
            aesop
          simp_rw [this]; clear this
          have (j : Fin p) : f j (Function.update v i x₂ j) =
              Function.update (fun i => f i (v i)) i (f j x₂) j := by
            simp only [Function.update, eq_rec_constant, dite_eq_ite]
            aesop
          simp_rw [this, Finset.update_eq_piecewise]; clear this
          erw [Finset.prod_piecewise, Finset.prod_piecewise, Finset.prod_piecewise]
          simp only [Finset.mem_univ, Finset.inter_singleton_of_mem, Finset.prod_singleton, add_mul]
        map_smul' := by
          intro _ v i a x
          simp only [smul_eq_mul]
          have (j : Fin p) : f j (Function.update v i (a • x) j) =
              Function.update (fun i => f i (v i)) i (a • f j x) j := by
            simp only [Function.update, eq_rec_constant, dite_eq_ite]
            aesop
          simp_rw [this]; clear this
          have (j : Fin p) : f j (Function.update v i x j) =
              Function.update (fun i => f i (v i)) i (f j x) j := by
            simp only [Function.update, eq_rec_constant, dite_eq_ite]
            aesop
          simp_rw [this, Finset.update_eq_piecewise]; clear this
          erw [Finset.prod_piecewise, Finset.prod_piecewise]
          simp only [Finset.mem_univ, Finset.inter_singleton_of_mem, smul_eq_mul,
            Finset.prod_singleton, mul_assoc] }
    map_add' := by
      intro _ f i g₁ g₂
      ext y
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod,
        MultilinearMap.coe_mk, LinearMap.add_apply]
      have (j : Fin p) :
          Function.update f i (g₁ + g₂) j (y j) =
          Function.update (fun i => f i (y i)) i (g₁ (y i) + g₂ (y i)) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]
        aesop
      simp_rw [this]; clear this
      have (j : Fin p) :
          Function.update f i g₁ j (y j) =
          Function.update (fun i => f i (y i)) i (g₁ (y i)) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]
        aesop
      simp_rw [this]; clear this
      have (j : Fin p) :
          Function.update f i g₂ j (y j) =
          Function.update (fun i => f i (y i)) i (g₂ (y i)) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]
        aesop
      simp_rw [this, Finset.update_eq_piecewise]; clear this
      erw [Finset.prod_piecewise, Finset.prod_piecewise, Finset.prod_piecewise]
      simp only [Finset.mem_univ, Finset.inter_singleton_of_mem, Finset.prod_const,
        Finset.card_singleton, pow_one, add_mul]
    map_smul' := by
      intro _ f i a g
      ext y
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod,
        MultilinearMap.coe_mk, LinearMap.smul_apply, smul_eq_mul]
      have (j : Fin p) :
          Function.update f i (a • g) j (y j) =
          Function.update (fun i => f i (y i)) i (a • g (y i)) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]
        aesop
      simp_rw [this]; clear this
      have (j : Fin p) :
          Function.update f i g j (y j) =
          Function.update (fun i => f i (y i)) i (g (y i)) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]
        aesop
      simp_rw [this, Finset.update_eq_piecewise]; clear this
      erw [Finset.prod_piecewise, Finset.prod_piecewise]
      simp only [Finset.mem_univ, Finset.inter_singleton_of_mem, smul_eq_mul,
        Finset.prod_const, Finset.card_singleton, pow_one, mul_assoc] }

@[simp]
lemma dualTensorPower_tprod (p : ℕ) (f : Fin p → Module.Dual k V) (v : Fin p → V) :
    dualTensorPower k V p (tprod k f) (tprod k v) = ∏ i : Fin p, f i (v i) := by
  simp only [dualTensorPower, lift.tprod, MultilinearMap.coe_mk]

end
