import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.TensorPower

section

variable (k V : Type*) [CommSemiring k] [AddCommMonoid V] [Module k V]

open TensorProduct PiTensorProduct

noncomputable def dualTensorPower (p : ℕ) :
    (⨂[k]^p $ Module.Dual k V) →ₗ[k] Module.Dual k (⨂[k]^p V) :=
  PiTensorProduct.lift
  { toFun := fun f => PiTensorProduct.lift
      { toFun := fun v => ∏ i : Fin p, f i (v i)
        map_update_add' := by
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
        map_update_smul' := by
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
    map_update_add' := by
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
    map_update_smul' := by
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

section

variable (k K V : Type*) [CommRing k] [CommRing K] [Algebra k K]
variable [AddCommGroup V] [Module k V]

open TensorProduct PiTensorProduct

noncomputable def Module.Dual.basis
    {ι : Type*} [DecidableEq ι] [_root_.Finite ι] (b : Basis ι k V) :
    Basis ι k (Module.Dual k V) :=
  b.map $ LinearEquiv.ofBijective b.toDual ⟨b.toDual_injective,
    LinearMap.range_eq_top.1 b.toDual_range⟩

set_option maxHeartbeats 500000 in
noncomputable def Module.Dual.extendScalarsAux (x : K) (f : Module.Dual k V) : Module.Dual K (K ⊗[k] V) :=
{ TensorProduct.liftAddHom
  { toFun := fun a =>
    { toFun := fun v => f v • (x * a)
      map_zero' := by simp
      map_add' := by intros; simp only [map_add, add_smul] }
    map_zero' := by ext; simp only [mul_zero, smul_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.zero_apply]
    map_add' := by intros; ext; simp only [mul_add, smul_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.add_apply] } fun a b x => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Algebra.mul_smul_comm, map_smul, smul_eq_mul,
        mul_smul]
      rw [smul_comm] with
  map_smul' := fun a x => by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply,
      smul_eq_mul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp only [smul_tmul', smul_eq_mul, liftAddHom_tmul, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Algebra.mul_smul_comm]; congr 1; ring
    | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, mul_add] }

@[simp]
lemma Module.Dual.extendScalarsAux_apply_tmul
    (x : K) (f : Module.Dual k V) (b : K) (v : V) :
    Module.Dual.extendScalarsAux k K V x f (b ⊗ₜ v) =
    f v • x * b := by
  simp only [extendScalarsAux, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk,
    AddHom.coe_mk, liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Algebra.smul_mul_assoc]

noncomputable def Module.Dual.extendScalarsAux2 :
    K ⊗[k] Module.Dual k V →ₗ[k] Module.Dual K (K ⊗[k] V) :=
  TensorProduct.lift
    { toFun := fun x =>
      { toFun := fun f => Module.Dual.extendScalarsAux k K V x f
        map_add' := fun f g => by
          ext v
          simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
            extendScalarsAux_apply_tmul, LinearMap.add_apply, add_smul, mul_one]

        map_smul' := fun a f => by
          ext v
          simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
            extendScalarsAux_apply_tmul, LinearMap.smul_apply, smul_eq_mul, mul_smul, mul_one,
            RingHom.id_apply] }
      map_add' := fun a b => by
        ext f v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, AlgebraTensorModule.curry_apply, curry_apply,
          LinearMap.coe_restrictScalars, extendScalarsAux_apply_tmul, smul_add, mul_one,
          LinearMap.add_apply]
      map_smul' := fun a b => by
        ext f v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, AlgebraTensorModule.curry_apply, curry_apply,
          LinearMap.coe_restrictScalars, extendScalarsAux_apply_tmul, mul_one, RingHom.id_apply,
          LinearMap.smul_apply]
        rw [smul_comm] }

noncomputable def Module.Dual.extendScalars :
    K ⊗[k] Module.Dual k V →ₗ[K] Module.Dual K (K ⊗[k] V) :=
  { Module.Dual.extendScalarsAux2 k K V with
    map_smul' := fun a x => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero =>
        rw [smul_zero, (extendScalarsAux2 k K V).map_zero, smul_zero]
      | tmul x f =>
        ext v
        simp only [extendScalarsAux2, smul_tmul', smul_eq_mul, lift.tmul, LinearMap.coe_mk,
          AddHom.coe_mk, AlgebraTensorModule.curry_apply, curry_apply,
          LinearMap.coe_restrictScalars, extendScalarsAux_apply_tmul, mul_one, LinearMap.smul_apply,
          Algebra.mul_smul_comm]
      | add x y hx hy =>
        rw [smul_add, map_add, hx, hy, map_add, smul_add] }

@[simp]
lemma Module.Dual.extendScalars_tmul_apply_tmul
    (x : K) (f : Module.Dual k V) (b : K) (v : V) :
    Module.Dual.extendScalars k K V (x ⊗ₜ f) (b ⊗ₜ v) =
    f v • (x * b) := by
  simp only [extendScalars, extendScalarsAux2, LinearMap.coe_mk, lift.tmul', AddHom.coe_mk,
    extendScalarsAux_apply_tmul, Algebra.smul_mul_assoc]

end
