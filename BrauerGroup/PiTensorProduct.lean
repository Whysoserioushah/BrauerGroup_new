import Mathlib.LinearAlgebra.PiTensorProduct
import BrauerGroup.Dual

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
