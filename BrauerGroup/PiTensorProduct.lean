import Mathlib.LinearAlgebra.PiTensorProduct
import BrauerGroup.Dual
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Notation

suppress_compilation

open TensorProduct PiTensorProduct

variable {ι : Type*} (k K : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (V : ι → Type*) [Π i : ι, AddCommMonoid (V i)] [Π i : ι, Module k (V i)]
variable (W : ι → Type*) [Π i : ι, AddCommMonoid (W i)] [Π i : ι, Module k (W i)]

namespace PiTensorProduct

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

-- def PiTensorProduct.tensorProductAux (w : (i : ι) → W i) :
--     (⨂[k] i, V i)  →ₗ[k] ⨂[k] i, (V i ⊗[k] W i) :=
--   PiTensorProduct.map fun i =>
--     { toFun := fun v => v ⊗ₜ[k] w i
--       map_add' := by simp [add_tmul]
--       map_smul' := by simp [smul_tmul] }

-- @[simp]
-- lemma PiTensorProduct.tensorProductAux_tprod (w : (i : ι) → W i) (x : Π i : ι, V i) :
--     PiTensorProduct.tensorProductAux k V W w (tprod k x) =
--     tprod k fun i => x i ⊗ₜ[k] w i := by
--   simp only [tensorProductAux, map_tprod, LinearMap.coe_mk, AddHom.coe_mk]

-- def PiTensorProduct.tensorProduct :
--     (⨂[k] i, V i) ⊗[k] (⨂[k] i, W i) →ₗ[k] ⨂[k] i, (V i ⊗[k] W i) :=
--   TensorProduct.lift
--     { toFun := fun v =>
--         PiTensorProduct.lift
--         { toFun := fun w => PiTensorProduct.tensorProductAux k V W w v
--           map_add' := by
--             intro _ w i x y
--             simp only
--             induction v using PiTensorProduct.induction_on with
--             | smul_tprod a v =>
--               simp only [LinearMapClass.map_smul, tensorProductAux_tprod]
--               rw [← smul_add]
--               rw [show (fun j ↦ v j ⊗ₜ[k] Function.update w i x j) =
--                 Function.update (fun i => v i ⊗ₜ[k] w i) i (v i ⊗ₜ[k] x) by
--                 ext <;> simp only [Function.update] <;> aesop,
--                 show (fun j ↦ v j ⊗ₜ[k] Function.update w i y j) =
--                 Function.update (fun i => v i ⊗ₜ[k] w i) i (v i ⊗ₜ[k] y) by
--                 ext <;> simp only [Function.update] <;> aesop]
--               rw [← (tprod k).map_add]
--               congr
--               ext
--               simp only [Function.update]
--               split_ifs with h
--               · subst h
--                 simp only [tmul_add]
--               · rfl
--             | add x y hx hy =>
--               rw [map_add, hx, hy, map_add, map_add]
--               abel
--           map_smul' := by
--             intro _ w i a x
--             simp only
--             induction v using PiTensorProduct.induction_on with
--             | smul_tprod b v =>
--               simp only [map_smul, tensorProductAux_tprod]
--               -- rw [← smul_tmul]
--               rw [show (fun j ↦ v j ⊗ₜ[k] Function.update w i x j) =
--                 Function.update (fun i => v i ⊗ₜ[k] w i) i (v i ⊗ₜ[k] x) by
--                 ext; simp only [Function.update]; aesop,
--                 show (fun j ↦ v j ⊗ₜ[k] Function.update w i (a • x) j) =
--                 Function.update (fun i => v i ⊗ₜ[k] w i) i (a • (v i ⊗ₜ[k] x)) by
--                 ext; simp only [Function.update]; aesop]
--               rw [(tprod k).map_smul, smul_comm]
--             | add x y hx hy =>
--               rw [map_add, hx, hy, map_add, smul_add] }
--       map_add' := fun x y => by
--         simp only [map_add]
--         rw [← map_add]
--         rfl
--       map_smul' := fun a x => by
--         simp only [LinearMapClass.map_smul, RingHom.id_apply]
--         rw [← map_smul]
--         rfl }
-- /-
-- (∑ᵢ₁, xᵢ₁ ⊗ yᵢ₁) ⊗ₜ (∑ᵢ₂, xᵢ₂ ⊗ yᵢ₂) ...
-- -/
-- def PiTensorProduct.tensorProductSymm :
--     (⨂[k] i, V i ⊗[k] W i) →ₗ[k] (⨂[k] i, W i) ⊗[k] (⨂[k] i, V i) :=
--   lift $ by
--     have := (tprod k (s := V))
--     have := MultilinearMap.domCoprod (R := k) (N := ⨂[k] i, V i ⊗[k] W i) (ι₁ := ι) (ι₂ := ι) (N₁ := (⨂[k] i, V i)) (N₂ := (⨂[k] i, W i))
--   -- { toFun := fun x => tprod _ fun i => x.1 i ⊗ₜ x.2 i
--   --   map_add' := by
--   --     intro _ x i x y
--   --     simp only
--   --     rw [← tmul_add]
--   --     congr
--   --     ext
--   --     simp only [Function.update]
--   --     split_ifs with h
--   --     · subst h
--   --       simp only [tmul_add]
--   --     · rfl
--   --   map_smul' := by
--   --     intro _ x i a y
--   --     simp only
--   --     rw [← tmul_smul]
--   --     congr
--   --     ext
--   --     simp only [Function.update]
--   --     split_ifs with h
--   --     · subst h
--   --       simp only [tmul_smul]
--   --     · rfl }


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

variable (n k : Type*) [Field k] [Fintype n] [DecidableEq n]
variable (ι : n → Type*) --[Π i, Fintype (ι i)]
variable (V : n → Type*) [Π i, AddCommGroup (V i)] [Π i, Module k (V i)]
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
              refine Finset.prod_congr rfl fun j hj => ?_
              simp only [Function.update]
              aesop
          simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_eq']
          rw [if_pos (by simp)]
          simp only [Finset.card_singleton, pow_one, add_mul]
          rw [calc ∏ j : n, (Function.update f i a j) (v j)
              _ = ∏ j : n, if j = i then a (v i) else f j (v j) := by
                refine Finset.prod_congr rfl fun j hj => ?_
                simp only [Function.update]
                aesop,
              calc ∏ j : n, (Function.update f i b j) (v j)
              _ = ∏ j : n, if j = i then b (v i) else f j (v j) := by
                refine Finset.prod_congr rfl fun j hj => ?_
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
              refine Finset.prod_congr rfl fun j hj => ?_
              simp only [Function.update]
              aesop
          simp only [Finset.prod_ite, Finset.prod_const, Finset.filter_eq']
          rw [if_pos (by simp)]
          simp only [Finset.card_singleton, pow_one, mul_pow]
          rw [calc ∏ j : n, (Function.update f i x j) (v j)
              _ = ∏ j : n, if j = i then x (v i) else f j (v j) := by
                refine Finset.prod_congr rfl fun j hj => ?_
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

lemma piTensorBasis_apply (x : Π i, ι i) :
    piTensorBasis n k ι V B x = tprod k fun i => (B i) (x i) := by
  simp only [piTensorBasis, PiTensorProduct.congr, Basis.coe_repr_symm, finsuppPiTensorFinsupp,
    LinearEquiv.trans_symm, Basis.map_apply, Finsupp.coe_basisSingleOne, LinearEquiv.trans_apply,
    LinearEquiv.ofLinear_symm_apply, Finsupp.llift_apply, Finsupp.lift_apply, zero_smul,
    Finsupp.sum_single_index, one_smul, map_tprod, Finsupp.total_single]

end PiTensorProduct.Basis

#exit
section PiTensorProduct.fin

variable {n : ℕ} (k K : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (V : Fin (n + 1) → Type*) [Π i, AddCommMonoid (V i)] [Π i, Module k (V i)]
variable (W : Fin (n + 1) → Type*) [Π i, AddCommMonoid (W i)] [Π i, Module k (W i)]

def PiTensorProduct.succ : (⨂[k] i, V i) ≃ₗ[k] V 0 ⊗[k] (⨂[k] i : Fin n, V i.succ) :=
LinearEquiv.ofLinear
  (PiTensorProduct.lift
    { toFun := fun v => v 0 ⊗ₜ[k] tprod k fun i => v i.succ
      map_add' := by
        intro _ v i x y
        simp only
        by_cases h : i = 0
        · subst h
          simp only [Function.update_same]
          rw [add_tmul]
          congr 3 <;>
          · ext i
            rw [Function.update_noteq (h := Fin.succ_ne_zero i),
              Function.update_noteq (h :=  Fin.succ_ne_zero i)]

        rw [Function.update_noteq (Ne.symm h), Function.update_noteq (Ne.symm h),
          Function.update_noteq (Ne.symm h), ← tmul_add]
        congr 1
        have eq1 : (fun j : Fin n ↦ Function.update v i (x + y) j.succ) =
          Function.update (fun i : Fin n ↦ v i.succ) (i.pred h)
            (cast (by simp) x + cast (by simp) y):= by
          ext j
          simp only [Function.update, eq_mpr_eq_cast]
          aesop
        rw [eq1, (tprod k).map_add]
        congr 2 <;>
        ext j <;>
        simp only [Function.update] <;>
        have eq : (j = i.pred h) = (j.succ = i) := by
          rw [← iff_eq_eq]
          constructor
          · rintro rfl
            exact Fin.succ_pred i h
          · rintro rfl
            simp only [Fin.pred_succ]
        · simp_rw [eq] <;> aesop
        · simp_rw [eq] <;> aesop
      map_smul' := by
        intro _ v i a x
        simp only
        rw [smul_tmul', smul_tmul]
        by_cases h : i = 0
        · subst h
          simp only [Function.update_same, tmul_smul]
          rw [smul_tmul']
          congr 2
          ext j
          rw [Function.update_noteq (Fin.succ_ne_zero j),
            Function.update_noteq (Fin.succ_ne_zero j)]
        · rw [Function.update_noteq (Ne.symm h), Function.update_noteq (Ne.symm h)]
          congr 1
          have eq1 : (fun j : Fin n ↦ Function.update v i (a • x) j.succ) =
            Function.update (fun i : Fin n ↦ v i.succ) (i.pred h)
              (a • cast (by simp) x):= by
            ext j
            simp only [Function.update, eq_mpr_eq_cast]
            aesop
          rw [eq1, (tprod k).map_smul]
          congr
          ext j
          simp only [Function.update]
          have eq : (j = i.pred h) = (j.succ = i) := by
            rw [← iff_eq_eq]
            constructor
            · rintro rfl
              exact Fin.succ_pred i h
            · rintro rfl
              simp only [Fin.pred_succ]
          simp_rw [eq] <;> aesop })
  (TensorProduct.lift
    { toFun := fun v₀ => PiTensorProduct.lift
        { toFun := fun v => tprod k $ Fin.cases v₀ v
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }) sorry sorry

end PiTensorProduct.fin


section PiTensorProduct.fin

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]

variable (k) in
def zeroPower (ι : Type*) (V : ι → Type*) [hι: IsEmpty ι]
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

variable (k) in
def PiTensorProduct.tensorCommutes (n : ℕ) :
    ∀ (V W : Fin n → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)],
    (⨂[k] i : Fin n, V i) ⊗[k] (⨂[k] i : Fin n, W i) ≃ₗ[k]
    ⨂[k] i : Fin n, (V i ⊗[k] W i) :=
  n.recOn
  (fun V W _ _ _ _ ↦ LinearEquiv.symm $ zeroPower k (Fin 0) (fun i : (Fin 0) ↦ V i ⊗[k] W i) ≪≫ₗ
      (TensorProduct.lid k k).symm ≪≫ₗ TensorProduct.congr (zeroPower k (Fin 0) _).symm
      (zeroPower k (Fin 0) _).symm)
  (fun m em V W _ _ _ _ ↦
      (TensorProduct.congr (PiTensorProduct.succ k (fun i : Fin (m+1) ↦ V i))
      (PiTensorProduct.succ k (fun i : Fin (m+1) ↦ W i))) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm k k _ _ _ _) ≪≫ₗ
      LinearEquiv.symm
        ((PiTensorProduct.succ (n := m) k (V := fun i : Fin (m.succ) ↦ (V i ⊗[k] W i))) ≪≫ₗ
          TensorProduct.congr (LinearEquiv.refl _ _)
            (em (fun i => V i.succ) (fun i => W i.succ)).symm))

theorem PiTensorProduct.tensorCommutes_apply (n : ℕ) (V W : Fin n → Type*)
    [hi1 : ∀ i, AddCommGroup (V i)] [hi2 : ∀ i, Module k (V i)]
    [hi1' : ∀ i, AddCommGroup (W i)] [hi2' : ∀ i, Module k (W i)]
    (v : Π i : Fin n, V i) (w : Π i : Fin n, W i) :
    PiTensorProduct.tensorCommutes k n V W ((tprod k v) ⊗ₜ (tprod k w)) =
    tprod k (fun i ↦ v i ⊗ₜ w i) := by
    sorry

end PiTensorProduct.fin
