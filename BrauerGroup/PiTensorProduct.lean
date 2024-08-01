import Mathlib.LinearAlgebra.PiTensorProduct
import BrauerGroup.LinearMap
import BrauerGroup.Dual
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Notation

suppress_compilation

open TensorProduct PiTensorProduct


namespace PiTensorProduct

variable {ι : Type*} (k K : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (V : ι → Type*) [Π i : ι, AddCommMonoid (V i)] [Π i : ι, Module k (V i)]
variable (W : ι → Type*) [Π i : ι, AddCommMonoid (W i)] [Π i : ι, Module k (W i)]

def extendScalars : (⨂[k] i, V i) →ₗ[k] ⨂[K] i, (K ⊗[k] V i) :=
  PiTensorProduct.lift
  { toFun := fun v => tprod _ fun i => 1 ⊗ₜ v i
    map_add' := by
      intro _ v i x y
      simp only
      have eq (j : ι) : (1 : K) ⊗ₜ Function.update v i x j =
        Function.update (fun i : ι => 1 ⊗ₜ v i) i (1 ⊗ₜ[k] x) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]; aesop
      simp_rw [eq]; clear eq
      have eq (j : ι) : (1 : K) ⊗ₜ Function.update v i y j =
        Function.update (fun i : ι => 1 ⊗ₜ v i) i (1 ⊗ₜ[k] y) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]; aesop
      simp_rw [eq]; clear eq
      rw [← MultilinearMap.map_add]
      congr
      ext
      simp only [Function.update]
      split_ifs with h
      · subst h
        simp only [tmul_add]
      · rfl
    map_smul' := by
      intro _ v i a x
      simp only
      have eq (j : ι) : (1 : K) ⊗ₜ Function.update v i (a • x) j =
        Function.update (fun i : ι => 1 ⊗ₜ v i) i (algebraMap k K a • 1 ⊗ₜ[k] x) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite, smul_ite]
        split_ifs with h
        · subst h; simp only [tmul_smul, algebraMap_smul]
        · rfl
      simp_rw [eq]; clear eq
      rw [MultilinearMap.map_smul]
      rw [algebraMap_smul]
      congr 2
      ext
      simp only [Function.update, eq_rec_constant, dite_eq_ite]
      aesop }

@[simp]
lemma extendScalars_tprod (x : Π i : ι, V i) :
    extendScalars k K V (tprod k x) =
    tprod K (1 ⊗ₜ x ·) := by
  simp only [extendScalars, lift.tprod, MultilinearMap.coe_mk]

/--
pure tensor of pure tensor
-/
lemma span_simple_tensor_eq_top [Fintype ι] :
    Submodule.span k { x | ∃ (v : Π i : ι,  V i) (w : Π i : ι, W i),
      x = tprod k (fun i => v i ⊗ₜ[k] w i) } = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    have H (i : ι) : v i ∈ (⊤ : Submodule k _) := ⟨⟩
    simp_rw [← span_tmul_eq_top, mem_span_set] at H
    choose cᵢ hcᵢ eqᵢ using H
    choose vij wij hij using hcᵢ
    have eq : v = fun i => ∑ j ∈ (cᵢ i).support.attach, (cᵢ i j) • (vij i j.2 ⊗ₜ[k] wij i j.2) := by
      ext i
      -- rw [← eqᵢ]
      simp only [← eqᵢ, Finsupp.sum]
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hij]
    rw [eq, (tprod k).map_sum_finset]
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ $ Submodule.subset_span
      ⟨fun i => cᵢ i (s i) • vij i (s i).2, fun i => wij i (s i).2, rfl⟩
  | add => aesop

end PiTensorProduct

section PiTensorProduct.Basis

variable (n k : Type*) [CommSemiring k] [Nontrivial k] [NoZeroDivisors k]
variable [Fintype n] [DecidableEq n]
variable (ι : n → Type*)
variable (V : n → Type*) [Π i, AddCommMonoid (V i)] [Π i, Module k (V i)]
variable (B : (i : n) → Basis (ι i) k (V i))

lemma prod_mul_tprod (x : n → k) (v : (i : n) → V i) :
    (∏ i, x i) • tprod k v = tprod k fun i => x i • v i := by
  exact Eq.symm (MultilinearMap.map_smul_univ (tprod k) x v)

open Finsupp in
def finsuppPiTensorFinsupp :
    (⨂[k] (i : n), ι i →₀ k) ≃ₗ[k] ((i : n) → ι i) →₀ k :=
  LinearEquiv.ofLinear
    (PiTensorProduct.lift
      { toFun := fun f =>
          { support := Fintype.piFinset fun i => (f i).support
            toFun := fun x => ∏ i : n, f i (x i)
            mem_support_toFun := fun x => by
              simp only [Fintype.mem_piFinset, mem_support_iff, ne_eq]
              rw [Finset.prod_eq_zero_iff]
              simp only [Finset.mem_univ, true_and, not_exists] }
        map_add' := by
          intro _ f i a b
          ext v
          simp only [Finsupp.coe_mk, Finsupp.coe_add, Pi.add_apply]
          calc ∏ j : n, (Function.update f i (a + b) j) (v j)
            _ = ∏ j : n, if j = i then a (v i) + b (v i) else f j (v j) := by
              refine Finset.prod_congr rfl fun j _ => ?_
              simp only [Function.update]
              aesop
          simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_eq']
          rw [if_pos (by simp)]
          simp only [Finset.card_singleton, pow_one, add_mul]
          rw [calc ∏ j : n, (Function.update f i a j) (v j)
              _ = ∏ j : n, if j = i then a (v i) else f j (v j) := by
                refine Finset.prod_congr rfl fun j _ => ?_
                simp only [Function.update]
                aesop,
              calc ∏ j : n, (Function.update f i b j) (v j)
              _ = ∏ j : n, if j = i then b (v i) else f j (v j) := by
                refine Finset.prod_congr rfl fun j _ => ?_
                simp only [Function.update]
                aesop]
          simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_eq']
          rw [if_pos (by simp)]
          simp only [Finset.card_singleton, pow_one, add_mul]
        map_smul' := by
          intro _ f i a x
          ext v
          simp only [Finsupp.coe_mk, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
          calc ∏ j : n, (Function.update f i (a • x) j) (v j)
            _ = ∏ j : n, if j = i then a * x (v i) else f j (v j) := by
              refine Finset.prod_congr rfl fun j _ => ?_
              simp only [Function.update]
              aesop
          simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_eq']
          rw [if_pos (by simp)]
          simp only [Finset.card_singleton, pow_one, mul_pow]
          rw [calc ∏ j : n, (Function.update f i x j) (v j)
              _ = ∏ j : n, if j = i then x (v i) else f j (v j) := by
                refine Finset.prod_congr rfl fun j _ => ?_
                simp only [Function.update]
                aesop]
          simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_eq']
          rw [if_pos (by simp)]
          simp only [Finset.card_singleton, pow_one, mul_pow, mul_assoc] })
    (Finsupp.llift (⨂[k] (i : n), ι i →₀ k) k k ((i : n) → ι i) fun x =>
      tprod k $ fun i => fun₀ | x i => 1)
    (by
      ext v₁ v₂
      simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, llift_apply, lift_apply,
        zero_smul, sum_single_index, one_smul, lift.tprod, MultilinearMap.coe_mk, coe_mk,
        LinearMap.id_comp]
      if h : v₁ = v₂ then subst h; aesop
      else
        rw [Finsupp.single_eq_of_ne h]
        replace h := Function.funext_iff.not.1 h
        push_neg at h
        obtain ⟨j, hj⟩ := h
        rw [Finset.prod_eq_zero (i := j) (hi := by simp)]
        rwa [Finsupp.single_eq_of_ne])
    (by
      ext x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        lift.tprod, MultilinearMap.coe_mk, llift_apply, lift_apply, LinearMap.id_coe, id_eq]
      simp only [sum, coe_mk, Finset.sum_map, Function.Embedding.coeFn_mk]
      change ∑ z ∈ _, (∏ i : n, _) • (⨂ₜ[k] _, _) = _
      have (z : (a : n) → ι a) :
          (∏ i : n, (x i) (z i)) •
          (tprod k fun j ↦ fun₀ | z j => (1 : k)) =
          tprod k fun j ↦ fun₀ | z j => (x j) (z j) := by
        rw [← (tprod k).map_smul_univ]
        congr! with j
        simp only [smul_single, smul_eq_mul, mul_one]
      simp_rw [this]
      rw [← (tprod k : MultilinearMap k _ (⨂[k] (i : n), ι i →₀ k)).map_sum_finset
        (A := fun i ↦ (x i).support) (g := fun j z ↦ fun₀ | z => x j z)]
      congr! with j
      conv_rhs => rw [← Finsupp.sum_single (x j)]
      rw [Finsupp.sum])

def piTensorBasis : Basis (Π i, ι i) k (⨂[k] i, V i) :=
  Finsupp.basisSingleOne.map $
    LinearEquiv.symm $ PiTensorProduct.congr (fun i => (B i).repr) ≪≫ₗ finsuppPiTensorFinsupp n k ι

@[simp]
lemma piTensorBasis_apply (x : Π i, ι i) :
    piTensorBasis n k ι V B x = tprod k fun i => (B i) (x i) := by
  simp only [piTensorBasis, PiTensorProduct.congr, Basis.coe_repr_symm, finsuppPiTensorFinsupp,
    LinearEquiv.trans_symm, Basis.map_apply, Finsupp.coe_basisSingleOne, LinearEquiv.trans_apply,
    LinearEquiv.ofLinear_symm_apply, Finsupp.llift_apply, Finsupp.lift_apply, zero_smul,
    Finsupp.sum_single_index, one_smul, map_tprod, Finsupp.total_single]

end PiTensorProduct.Basis

section extendScalars

variable (k K V W W' : Type*)
variable {p q : ℕ}
variable [CommSemiring k] [Nontrivial k] [NoZeroDivisors k]
variable [CommSemiring K] [Nontrivial K] [NoZeroDivisors K] [Algebra k K]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]
variable [AddCommMonoid W'] [Module k W']

variable {k V} (p) in
def _root_.Basis.extendScalarsTensorPower {ι : Type*} (b : Basis ι k V) :
  Basis (Fin p → ι) K (K ⊗[k] (⨂[k]^p V)) :=
Algebra.TensorProduct.basis K (piTensorBasis _ _ _ _ (fun _ => b))

@[simp]
lemma _root_.Basis.extendScalarsTensorPower_apply {ι : Type*} (b : Basis ι k V) (i : Fin p → ι) :
    Basis.extendScalarsTensorPower K p b i = 1 ⊗ₜ tprod k fun j => b (i j) := by
  simp only [Basis.extendScalarsTensorPower, Algebra.TensorProduct.basis_apply, piTensorBasis_apply]

variable {k V} (p) in
def _root_.Basis.tensorPowerExtendScalars {ι : Type*} (b : Basis ι k V) :
    Basis (Fin p → ι) K (⨂[K]^p $ K ⊗[k] V) :=
  piTensorBasis _ _ _ _ fun _ => Algebra.TensorProduct.basis K b

@[simp]
lemma _root_.Basis.tensorPowerExtendScalars_apply {ι : Type*} (b : Basis ι k V) (i : Fin p → ι) :
    Basis.tensorPowerExtendScalars K p b i = tprod K fun j => 1 ⊗ₜ[k] b (i j) := by
  simp only [Basis.tensorPowerExtendScalars, piTensorBasis_apply, Algebra.TensorProduct.basis_apply]

variable {k V} (p) in
def _root_.Basis.extendScalarsTensorPowerEquiv {ι : Type*} (b : Basis ι k V) :
    K ⊗[k] (⨂[k]^p V) ≃ₗ[K] (⨂[K]^p $ K ⊗[k] V) :=
  (b.extendScalarsTensorPower K p).equiv (b.tensorPowerExtendScalars K p) (Equiv.refl _)

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_apply {ι : Type*} (b : Basis ι k V)
    (i : Fin p → ι) :
    b.extendScalarsTensorPowerEquiv K p (1 ⊗ₜ tprod k fun j => b (i j)) =
    tprod K fun j => 1 ⊗ₜ[k] b (i j) := by
  simp only [Basis.extendScalarsTensorPowerEquiv]
  have := (b.extendScalarsTensorPower K p).equiv_apply (b' := b.tensorPowerExtendScalars K p) i
    (Equiv.refl _)
  simp only [Basis.extendScalarsTensorPower_apply, Equiv.refl_apply,
    Basis.tensorPowerExtendScalars_apply] at this
  exact this

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_symm_apply {ι : Type*} (b : Basis ι k V)
    (i : Fin p → ι) :
    (b.extendScalarsTensorPowerEquiv K p).symm (tprod K fun j => 1 ⊗ₜ[k] b (i j)) =
    1 ⊗ₜ[k] tprod k fun j => b (i j) := by
  simp only [Basis.extendScalarsTensorPowerEquiv, Basis.equiv_symm, Equiv.refl_symm]
  have := (b.tensorPowerExtendScalars K p).equiv_apply (b' := b.extendScalarsTensorPower K p) i
    (Equiv.refl _)
  simp only [Basis.tensorPowerExtendScalars_apply, Equiv.refl_apply,
    Basis.extendScalarsTensorPower_apply] at this
  exact this

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_apply' {ιV ιW : Type*}
    (bV : Basis ιV k V) (bW : Basis ιW k W)
    (iV : Fin p → ιV) (f : V →ₗ[k] W) :
    bW.extendScalarsTensorPowerEquiv K p (1 ⊗ₜ tprod k fun j => f $ bV (iV j)) =
    tprod K fun j => (1 : K) ⊗ₜ[k] (f $ bV (iV j)) := by
  have eq (j : Fin p) := bW.total_repr (f $ bV (iV j))
  dsimp only [Finsupp.total, Finsupp.lsum, Finsupp.sum, LinearEquiv.coe_mk, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, LinearMap.coe_mk, AddHom.coe_mk] at eq
  have eq' : (tprod k fun j ↦ f (bV $ iV j)) = tprod k fun j =>
    ∑ a ∈ (bW.repr (f (bV $ iV j))).support, (bW.repr (f (bV (iV j)))) a • bW a := by
    congr
    simp_rw [eq]
  rw [eq', MultilinearMap.map_sum_finset, tmul_sum, map_sum]
  simp_rw [MultilinearMap.map_smul_univ (tprod k), tmul_smul]
  have eq'' : ((tprod K) fun j ↦ (1 : K) ⊗ₜ[k] f (bV (iV j))) = tprod K fun j =>
    1 ⊗ₜ ∑ a ∈ (bW.repr (f (bV $ iV j))).support, (bW.repr (f (bV (iV j)))) a • bW a := by
    congr
    simp_rw [eq]
  rw [eq'']
  simp_rw [tmul_sum]
  rw [MultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [algebra_compatible_smul K, map_smul, map_prod]
  simp only [Basis.extendScalarsTensorPowerEquiv_apply, tmul_smul]
  rw [← MultilinearMap.map_smul_univ (tprod K)]
  congr 1
  ext i
  simp

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_symm_apply' {ιV ιW : Type*}
    (bV : Basis ιV k V) (bW : Basis ιW k W)
    (iV : Fin p → ιV) (f : V →ₗ[k] W) :
    (bW.extendScalarsTensorPowerEquiv K p).symm (tprod K fun j => (1 : K) ⊗ₜ[k] (f $ bV (iV j))) =
     (1 ⊗ₜ tprod k fun j => f $ bV (iV j)) := by
  apply_fun (bW.extendScalarsTensorPowerEquiv K p) using
    (bW.extendScalarsTensorPowerEquiv K p).injective
  simp only [LinearEquiv.apply_symm_apply, Basis.extendScalarsTensorPowerEquiv_apply']

lemma _root_.Basis.extendScalarsTensorPowerEquiv_zero {ι : Type*} (b : Basis ι k V) :
    b.extendScalarsTensorPowerEquiv K 0 =
    ({ TensorProduct.congr (LinearEquiv.refl k K) (PiTensorProduct.isEmptyEquiv (ι := Fin 0) (s := fun _ => V)) with
        map_smul' := fun a x => by
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
            RingHom.id_apply]
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul x y => simp [smul_tmul']
          | add x y hx hy =>
            simp only [smul_add, map_add, hx, hy, mul_add] } : (K ⊗[k] ⨂[k]^0 V) ≃ₗ[K] K ⊗[k] k) ≪≫ₗ
    { TensorProduct.rid k K with
      map_smul' := fun a x => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply, smul_eq_mul]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => simp [smul_tmul']
        | add x y hx hy =>
          simp only [smul_add, map_add, hx, hy, mul_add] } ≪≫ₗ
    (PiTensorProduct.isEmptyEquiv _).symm := by
  apply_fun LinearEquiv.toLinearMap using LinearEquiv.toLinearMap_injective
  fapply Basis.ext (b := b.extendScalarsTensorPower K 0)
  intro v
  simp only [Basis.extendScalarsTensorPower_apply, LinearEquiv.coe_coe,
    Basis.extendScalarsTensorPowerEquiv_apply, LinearEquiv.invFun_eq_symm, LinearEquiv.trans_apply,
    isEmptyEquiv_symm_apply]
  erw [LinearMap.coe_mk]
  simp only [LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  erw [TensorProduct.rid_tmul]
  simp only [LinearEquiv.coe_coe, isEmptyEquiv_apply_tprod, LinearEquiv.refl_toLinearMap,
    LinearMap.id_coe, id_eq, one_smul]
  congr 1
  ext i
  exact i.elim0

lemma _root_.Basis.extendScalarsTensorPowerEquiv_zero_apply {ι : Type*} (b : Basis ι k V)
    (a : K) (x : ⨂[k]^0 V) :
    b.extendScalarsTensorPowerEquiv K 0 (a ⊗ₜ x) =
    (PiTensorProduct.isEmptyEquiv _).symm (PiTensorProduct.isEmptyEquiv _ x • a) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod x v =>
    simp only [Basis.extendScalarsTensorPowerEquiv_zero, LinearEquiv.invFun_eq_symm, tmul_smul,
      smul_tmul', LinearEquiv.trans_apply, isEmptyEquiv_symm_apply, map_smul,
      isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one, smul_assoc]
    erw [LinearMap.coe_mk]
    simp only [LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    erw [TensorProduct.rid_tmul]
    simp only [LinearEquiv.coe_coe, isEmptyEquiv_apply_tprod, LinearEquiv.refl_toLinearMap,
      LinearMapClass.map_smul, LinearMap.id_coe, id_eq, one_smul, smul_assoc]
  | add x y hx hy =>
    simp only [tmul_add, map_add, hx, isEmptyEquiv_symm_apply, smul_assoc, hy, add_smul]

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_zero_symm_apply {ι : Type*} (b : Basis ι k V)
    (a : K)  :
    (b.extendScalarsTensorPowerEquiv K 0).symm (a • tprod K isEmptyElim) =
    a ⊗ₜ tprod k isEmptyElim := by
  apply_fun b.extendScalarsTensorPowerEquiv K 0 using LinearEquiv.injective
    (Basis.extendScalarsTensorPowerEquiv K 0 b)
  simp only [LinearMapClass.map_smul, LinearEquiv.apply_symm_apply,
    Basis.extendScalarsTensorPowerEquiv_zero_apply, isEmptyEquiv_apply_tprod, one_smul,
    isEmptyEquiv_symm_apply]

@[simp]
lemma _root_.Basis.extendScalarsTensorPowerEquiv_zero_symm_apply' {ι : Type*} (b : Basis ι k V) :
    (b.extendScalarsTensorPowerEquiv K 0).symm (tprod K isEmptyElim) =
    1 ⊗ₜ tprod k isEmptyElim := by
  apply_fun b.extendScalarsTensorPowerEquiv K 0 using LinearEquiv.injective
    (Basis.extendScalarsTensorPowerEquiv K 0 b)
  simp only [LinearMapClass.map_smul, LinearEquiv.apply_symm_apply,
    Basis.extendScalarsTensorPowerEquiv_zero_apply, isEmptyEquiv_apply_tprod, one_smul,
    isEmptyEquiv_symm_apply]


set_option maxHeartbeats 500000 in
lemma _root_.Basis.extendScalarsTensorPowerEquiv_comp_extendScalars
    {ιV ιW : Type*}
    (bV : Basis ιV k V) (bW : Basis ιW k W)
    (f : V →ₗ[k] W) :
    (bW.extendScalarsTensorPowerEquiv K p).toLinearMap ∘ₗ
      (LinearMap.extendScalars K (PiTensorProduct.map fun _ => f)) =
    (PiTensorProduct.map fun _ => f.extendScalars K) ∘ₗ
      (bV.extendScalarsTensorPowerEquiv K p).toLinearMap := by
  ext v
  simp only [AlgebraTensorModule.curry_apply, LinearMap.compMultilinearMap_apply, curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.extendScalars_apply, map_tprod]
  have eq (j : Fin p) := bW.total_repr (f $ v j)
  dsimp only [Finsupp.total, Finsupp.lsum, Finsupp.sum, LinearEquiv.coe_mk, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, LinearMap.coe_mk, AddHom.coe_mk] at eq
  have eq' : (tprod k fun j ↦ f (v j)) = tprod k fun j =>
    ∑ a ∈ (bW.repr (f (v j))).support, (bW.repr (f (v j))) a • bW a := by
    congr
    simp_rw [eq]
  rw [eq']
  rw [MultilinearMap.map_sum_finset, tmul_sum, map_sum]
  simp_rw [MultilinearMap.map_smul_univ (tprod k), tmul_smul]
  rw [show ∑ x ∈ Fintype.piFinset fun j ↦ (bW.repr (f (v j))).support,
    (Basis.extendScalarsTensorPowerEquiv K p bW)
      ((∏ i : Fin p, (bW.repr (f (v i))) (x i)) • 1 ⊗ₜ[k] (tprod k) fun i ↦ bW (x i)) =
    ∑ x ∈ Fintype.piFinset fun j ↦ (bW.repr (f (v j))).support,
    (Basis.extendScalarsTensorPowerEquiv K p bW)
      (algebraMap k K (∏ i : Fin p, (bW.repr (f (v i))) (x i)) •
        1 ⊗ₜ[k] (tprod k) fun i ↦ bW (x i)) from Finset.sum_congr rfl fun _ _ => by
        rw [algebra_compatible_smul K, map_smul, map_prod]]
  simp_rw [map_smul]
  have eq''' (x : Fin p → ιW) :
      Basis.extendScalarsTensorPowerEquiv K p bW (1 ⊗ₜ[k] (tprod k) fun i ↦ bW (x i)) =
      tprod K fun i => 1 ⊗ₜ[k] bW (x i) := by
    rw [Basis.extendScalarsTensorPowerEquiv_apply]
  simp_rw [eq''']
  have eq₄ : (tprod k) v =
    tprod k fun i => ∑ a ∈ (bV.repr (v i)).support, bV.repr (v i) a • bV a := by
    congr
    ext j
    have := bV.total_repr (v j)
    simpa [Eq.comm, Finsupp.total] using this
  conv_rhs => rw [eq₄, MultilinearMap.map_sum_finset, tmul_sum, map_sum, map_sum]
  simp_rw [MultilinearMap.map_smul_univ (tprod k), tmul_smul]
  have eq₅ (x : Fin p → ιV) :
      Basis.extendScalarsTensorPowerEquiv K p bV
        ((∏ i : Fin p, (bV.repr (v i)) (x i)) • 1 ⊗ₜ[k] (tprod k) fun i ↦ bV (x i)) =
      algebraMap k K (∏ i : Fin p, (bV.repr (v i)) (x i)) • tprod K fun i => 1 ⊗ₜ[k] bV (x i) := by
    rw [algebra_compatible_smul K, map_smul, Basis.extendScalarsTensorPowerEquiv_apply]
  simp_rw [eq₅, map_smul, PiTensorProduct.map_tprod]
  simp only [LinearMap.extendScalars_apply, algebraMap_smul]
  have eq₆ (x : Fin p → ιW) :
      (∏ i : Fin p, (bW.repr (f (v i))) (x i)) • ((tprod K) fun i ↦ (1 : K) ⊗ₜ[k] bW (x i)) =
      tprod K fun i => (1 : K) ⊗ₜ[k] ((bW.repr (f (v i))) (x i) • bW (x i)) := by
    rw [algebra_compatible_smul K, map_prod, ← (tprod K).map_smul_univ]
    congr
    ext j
    simp
  simp_rw [eq₆]
  have eq₇ (x : Fin p → ιV) :
      (∏ i : Fin p, (bV.repr (v i)) (x i)) • ((tprod K) fun i ↦ (1 : K) ⊗ₜ[k] f (bV (x i))) =
      tprod K fun i => 1 ⊗ₜ[k] ((bV.repr (v i)) (x i) • f (bV (x i))):= by
    rw [algebra_compatible_smul K, map_prod, ← (tprod K).map_smul_univ]
    congr
    ext j
    simp
  simp_rw [eq₇]
  have eq₈ : (tprod K fun j ↦ (1 : K) ⊗ₜ[k] f (v j)) = tprod K fun j =>
    ∑ a ∈ (bW.repr (f (v j))).support, 1 ⊗ₜ ((bW.repr (f (v j))) a • bW a) := by
    simp_rw [← tmul_sum]
    congr
    ext j
    simp_rw [eq]
  rw [MultilinearMap.map_sum_finset] at eq₈
  rw [← eq₈]
  have eq₉ : (tprod K fun j ↦ (1 : K) ⊗ₜ[k] f (v j)) = tprod K fun j =>
    ∑ a ∈ (bV.repr (v j)).support, 1 ⊗ₜ (bV.repr (v j) a • f (bV a)) := by
    simp_rw [← tmul_sum]
    congr
    ext j
    have := bV.total_repr (v j)
    conv_lhs => erw [← this]
    erw [map_sum]
    congr
    ext i
    simp
  rw [MultilinearMap.map_sum_finset] at eq₉
  rw [← eq₉]

end extendScalars

section


lemma PiTensorProduct.isEmptyEquiv_comp_algebraMap
    {k K : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K] (ι : Type*) [emp : IsEmpty ι]
  (V : ι → Type*) [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] :
  (Algebra.ofId k K).toLinearMap ∘ₗ
  (PiTensorProduct.isEmptyEquiv ι : (⨂[k] i : ι, V i) ≃ₗ[k] k).toLinearMap =
  (PiTensorProduct.isEmptyEquiv ι :
    (⨂[K] i : ι, K ⊗[k] V i) ≃ₗ[K] K).toLinearMap.restrictScalars k ∘ₗ
  PiTensorProduct.lift
    { toFun := fun v => tprod K fun i => 1 ⊗ₜ v i
      map_add' := fun v i => emp.elim i
      map_smul' := fun v i => emp.elim i } := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, isEmptyEquiv_apply_tprod, AlgHom.toLinearMap_apply, _root_.map_one,
    LinearMap.coe_restrictScalars, lift.tprod, MultilinearMap.coe_mk]

lemma PiTensorProduct.isEmptyEquiv_comp_algebraMap_elementwise
    {k K : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K] (ι : Type*) [emp : IsEmpty ι]
    (V : ι → Type*) [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]  :
    algebraMap k K (PiTensorProduct.isEmptyEquiv ι
      (tprod k isEmptyElim : ⨂[k] i : ι, V i)) = 1 := by
  have := congr($(PiTensorProduct.isEmptyEquiv_comp_algebraMap ι V (k := k) (K := K))
    (tprod k isEmptyElim))
  dsimp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars] at this
  erw [this]
  simp

end

section gal
variable {ι k K V : Type*}
variable {q : ℕ}
variable [CommSemiring k] [Nontrivial k] [NoZeroDivisors k]
variable [CommSemiring K] [Nontrivial K] [NoZeroDivisors K] [Algebra k K]
variable [AddCommMonoid V] [Module k V] (b : Basis ι k V)

variable (q) in
def _root_.AlgHom.oneTMulPow (σ : K →ₐ[k] K) :
    (⨂[K]^q (K ⊗[k] V)) →ₗ[k] ⨂[K]^q (K ⊗[k] V) :=
  (Basis.extendScalarsTensorPowerEquiv K q b).toLinearMap.restrictScalars k ∘ₗ
  σ.toLinearMap.rTensor _ ∘ₗ
  (Basis.extendScalarsTensorPowerEquiv K q b).symm.toLinearMap.restrictScalars k

@[simp]
lemma _root_.AlgHom.oneTMulPow_apply (σ : K →ₐ[k] K) (a : Fin q → K) (v : Fin q → ι) :
    σ.oneTMulPow q b (tprod K fun i => a i ⊗ₜ b (v i)) =
    (∏ i : Fin q, σ (a i)) • tprod K fun i => 1 ⊗ₜ b (v i) := by
  simp only [AlgHom.oneTMulPow, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [show (tprod K fun i => a i ⊗ₜ b (v i)) =
    (tprod K fun i => a i • 1 ⊗ₜ b (v i)) by simp_rw [smul_tmul', smul_eq_mul, mul_one],
    MultilinearMap.map_smul_univ, map_smul]
  simp only [Basis.extendScalarsTensorPowerEquiv_symm_apply]
  rw [smul_tmul', smul_eq_mul, mul_one, LinearMap.rTensor_tmul,
    show (σ.toLinearMap (∏ i : Fin q, a i) ⊗ₜ[k] (tprod k) fun j ↦ b (v j)) =
    (σ.toLinearMap (∏ i : Fin q, a i) • 1 ⊗ₜ[k] (tprod k) fun j ↦ b (v j)) by
    rw [smul_tmul', smul_eq_mul, mul_one], map_smul]
  simp

@[simp]
lemma _root_.AlgHom.oneTMulPow_apply' (σ : K →ₐ[k] K) (a : K) (v : Fin q → ι) [NeZero q] :
    σ.oneTMulPow q b (a • tprod K fun i => 1 ⊗ₜ b (v i)) =
    σ a • tprod K fun i => 1 ⊗ₜ b (v i) := by
  rw [show (a • tprod K fun i => (1 : K) ⊗ₜ b (v i)) =
    (∏ i : Fin q, if i = 0 then a else 1) • tprod K fun i => 1 ⊗ₜ b (v i) by simp,
    ← MultilinearMap.map_smul_univ]
  simp_rw [smul_tmul']
  rw [AlgHom.oneTMulPow_apply]
  simp only [smul_eq_mul, mul_one]
  congr
  rw [show ∏ x : Fin q, σ (if x = 0 then a else 1) = ∏ x : Fin q, if x = 0 then σ a else 1 from
    Finset.prod_congr rfl fun i _ => by split_ifs <;> simp]
  simp

lemma _root_.AlgHom.oneTMulPow_apply_q_zero (σ : K →ₐ[k] K) :
    σ.oneTMulPow 0 b =
    (PiTensorProduct.isEmptyEquiv _).symm.toLinearMap.restrictScalars k ∘ₗ
    σ.toLinearMap ∘ₗ
    (PiTensorProduct.isEmptyEquiv _).toLinearMap.restrictScalars k := by
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Function.comp_apply, AlgHom.toLinearMap_apply, isEmptyEquiv_symm_apply]
  have mem : x ∈ (⊤ : Submodule K _) := ⟨⟩
  rw [← PiTensorProduct.span_tprod_eq_top, mem_span_set] at mem
  obtain ⟨a, ha, rfl⟩ := mem
  choose x hx using ha
  simp only [Finsupp.sum, map_sum, LinearMapClass.map_smul, smul_eq_mul, _root_.map_mul]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hz => ?_
  specialize hx hz
  have hz' : z = tprod K isEmptyElim := by
    rw [← hx]; congr; ext i; simpa using i.2
  rw [hz']
  simp only [isEmptyEquiv_apply_tprod, _root_.map_one, mul_one]
  simp only [AlgHom.oneTMulPow, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, Function.comp_apply, LinearMapClass.map_smul]
  have eq : ((tprod K) isEmptyElim : ⨂[K] (_ : Fin 0), K ⊗[k] V) =
      tprod K fun a => 1 ⊗ₜ b a.elim0 := by
    congr; ext i; exact i.elim0
  rw [eq]
  simp only [Basis.extendScalarsTensorPowerEquiv_symm_apply, smul_tmul', smul_eq_mul, mul_one,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  rw [show (σ (a ((tprod K) fun a ↦ 1 ⊗ₜ[k] b a.elim0)) ⊗ₜ[k]
      (tprod k) fun j : Fin 0 ↦ b j.elim0) =
    σ (a ((tprod K) fun a ↦ 1 ⊗ₜ[k] b a.elim0)) • ((1 : K) ⊗ₜ (tprod k) fun j ↦ b j.elim0) by
    rw [smul_tmul', smul_eq_mul, mul_one], map_smul]
  simp

end gal

section PiTensorProduct.fin

variable {k K : Type*} [CommSemiring k] [Semiring K] [Algebra k K]

variable (k) in
def PiTensorProduct.emptyEquivBaseRing (ι : Type*) (V : ι → Type*) [hι: IsEmpty ι]
  [∀ i, AddCommGroup $ V i]  [∀ i, Module k $ V i]: (⨂[k] i : ι, V i) ≃ₗ[k] k :=
  LinearEquiv.ofLinear
    (PiTensorProduct.lift
      { toFun := fun _ ↦ 1
        map_add' := by
          intros; exact hι.elim (by assumption)
        map_smul' := by
          intros; exact hι.elim (by assumption) })
    { toFun := fun a ↦ a • tprod k fun x ↦ hι.elim x
      map_add' := by
        intro x y
        simp only [self_eq_add_right, add_smul]
      map_smul' := by
        intro m x
        simp [mul_smul]
      }
    (by
      refine LinearMap.ext_ring ?h
      simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, one_smul,
        lift.tprod, MultilinearMap.coe_mk, LinearMap.id_coe, id_eq])
    (by
      ext x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply, lift.tprod, MultilinearMap.coe_mk, one_smul,
        LinearMap.id_coe, id_eq]
      refine MultilinearMap.congr_arg (tprod k) ?_
      ext y
      exact hι.elim y)

end PiTensorProduct.fin
