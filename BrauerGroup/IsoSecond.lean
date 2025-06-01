import BrauerGroup.ToSecond
import Mathlib.LinearAlgebra.Dimension.Constructions

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

open scoped TensorProduct

-- namespace map_one_proof
-- section map_one

-- variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

-- set_option maxHeartbeats 1000000 in
-- def φ0 :
--     CrossProduct (F := F) (K := K) (a := 1)
--       (ha := isMulTwoCocycle_of_mem_twoCocycles 0 <| Submodule.zero_mem _) →ₗ[K]
--     Module.End F K :=
--   (CrossProduct.x_AsBasis (F := F) (K := K) (a := 1)
--     (ha := isMulTwoCocycle_of_mem_twoCocycles 0 <| Submodule.zero_mem _)).constr F
--     fun σ => σ.toLinearMap

-- def φ1 :
--     CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₗ[F]
--     Module.End F K :=
--   φ0 K F |>.restrictScalars F

-- def φ2 :
--     CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₐ[F]
--     Module.End F K :=
--   AlgHom.ofLinearMap (φ1 K F)
--     (by
--       generalize_proofs h
--       rw [show (1 : CrossProduct h) = .x_AsBasis h 1 by
--         ext1
--         simp]
--       delta φ1 φ0
--       rw [LinearMap.restrictScalars_apply, Basis.constr_basis]
--       rfl)
--     (by
--       rintro x y
--       change φ0 K F _ = φ0 K F _ * φ0 K F _
--       generalize_proofs h
--       induction x using CrossProduct.single_induction h with
--       | single x c =>
--         rw [show (⟨Pi.single x c⟩ : CrossProduct h) =
--           c • .x_AsBasis h x by
--           ext : 1
--           simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
--             CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
--             crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
--         rw [map_smul]
--         induction y using CrossProduct.single_induction h with
--         | single y d =>
--           rw [show (⟨Pi.single y d⟩ : CrossProduct h) =
--             d • .x_AsBasis h y by
--             ext : 1
--             simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
--               CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
--               crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
--           rw [show (c • CrossProduct.x_AsBasis h x) * (d • .x_AsBasis h y) =
--             (c * x d) • .x_AsBasis h (x * y) by
--             ext : 1
--             simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
--               CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
--               crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply, map_mul]]
--           rw [map_smul, map_smul]
--           delta φ0
--           rw [Basis.constr_basis, Basis.constr_basis, Basis.constr_basis]
--           ext α
--           simp only [LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.mul_apply,
--             smul_eq_mul, _root_.mul_assoc, LinearMap.mul_apply, map_mul]
--         | add y y' hy hy' =>
--           erw [mul_add]
--           rw [map_add, hy, hy']
--           erw [map_add]
--           rw [mul_add]
--         | zero =>
--           erw [mul_zero]
--           rw [map_zero]
--           erw [map_zero]
--           rw [mul_zero]
--       | add x x' hx hx' =>
--         erw [add_mul]
--         rw [map_add, hx, hx']
--         erw [map_add]
--         rw [add_mul]
--       | zero =>
--         erw [zero_mul]
--         rw [map_zero]
--         erw [map_zero]
--         rw [zero_mul])

-- def φ3 :
--     CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
--     Module.End F K :=
--   AlgEquiv.ofBijective (φ2 K F) (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by
--     rw [CrossProduct.dim_eq_square]
--     rw [Module.finrank_linearMap, pow_two])

-- def φ4 :
--     CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
--     Matrix (Fin <| Module.finrank F K) (Fin <| Module.finrank F K) F :=
--   φ3 K F |>.trans <| LinearMap.toMatrixAlgEquiv <| Module.finBasis F K

-- lemma map_one' : RelativeBrGroup.fromTwoCocycles (F := F) (K := K) (a := 0) = 1 := by
--   ext1
--   change Quotient.mk'' _ = Quotient.mk'' _
--   erw [Quotient.eq'']
--   have : 0 < Module.finrank F K := Module.finrank_pos
--   haveI : NeZero (Module.finrank F K) := ⟨by omega⟩
--   change IsBrauerEquivalent _ _
--   refine ⟨1, Module.finrank F K, AlgEquiv.trans ?_ <| φ4 K F⟩
--   exact dim_one_iso (CSA.mk (CrossProduct.asCSA _).carrier).carrier

-- lemma fromSnd_zero : RelativeBrGroup.fromSnd (F := F) (K := K) 0 = 1 := map_one' K F

-- end map_one

-- end map_one_proof

namespace map_mul_proof
section map_mul

variable (𝔞 𝔟 : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ)
variable (h𝔞 : IsMulTwoCocycle 𝔞) (h𝔟 : IsMulTwoCocycle 𝔟)

variable {K F 𝔞 𝔟}

include h𝔞 h𝔟 in
lemma h𝔞𝔟 : IsMulTwoCocycle (𝔞 * 𝔟) := isMulTwoCocycle_of_mem_twoCocycles _ <|
  ((twoCocyclesOfIsMulTwoCocycle h𝔞) + (twoCocyclesOfIsMulTwoCocycle h𝔟)).2

local notation "A" => CrossProduct h𝔞
local notation "B" => CrossProduct h𝔟
local notation "C" => CrossProduct (h𝔞𝔟 h𝔞 h𝔟)

open CrossProduct TensorProduct

variable [FiniteDimensional F K]  [DecidableEq (K ≃ₐ[F] K)]


abbrev S : Set (A ⊗[F] B) :=
  Set.range (fun (cba : K × A × B) =>
    (cba.1 • cba.2.1) ⊗ₜ[F] cba.2.2 - cba.2.1 ⊗ₜ[F] (cba.1 • cba.2.2))

@[simp]
lemma mem_S (x : A ⊗[F] B) : x ∈ S h𝔞 h𝔟 ↔
    ∃ (k : K) (a : A) (b : B), x = (k • a) ⊗ₜ b - a ⊗ₜ (k • b) := by
  simp only [S, Set.mem_range, Prod.exists]
  aesop

abbrev M := (A ⊗[F] B) ⧸ Submodule.span F (S h𝔞 h𝔟)

open MulOpposite

instance : IsScalarTower K A A where
  smul_assoc k a a' := by
    induction a using single_induction with
    | single σ a =>
      induction a' using single_induction with
      | single τ a' =>
        ext : 1
        simp only [CrossProduct.smul_def, smul_eq_mul, mul_val, ι_apply_val, Prod.mk_one_one,
          Units.val_inv_eq_inv_val, crossProductMul_single_single, _root_.one_mul,
          AlgEquiv.one_apply, Pi.single_inj]
        field_simp
        ring
      | add x y hx hy =>
        erw [smul_add, smul_add, hx, hy, smul_add]
      | zero =>
        erw [smul_zero, smul_zero, smul_zero]
    | add x y hx hy =>
      erw [smul_add, add_smul, hx, hy, add_smul, smul_add]
    | zero =>
      erw [smul_zero, zero_smul, smul_zero]

section Aox_FB_mod

def Aox_FB_smul_M_aux (a' : A) (b' : B) : M h𝔞 h𝔟 →ₗ[F] M h𝔞 h𝔟 :=
  Submodule.mapQ (Submodule.span F (S h𝔞 h𝔟)) (Submodule.span F (S h𝔞 h𝔟))
    (TensorProduct.lift
      { toFun := fun a =>
        { toFun := fun b => (a * a') ⊗ₜ (b * b')
          map_add' := by
            intro b1 b2
            simp [add_mul, tmul_add]
          map_smul' := by
            intro f b; simp }
        map_add' := by
          intro a1 a2
          ext b : 1
          simp [add_mul, add_tmul]
        map_smul' := by
          intro f a
          ext b : 1
          simp [smul_tmul] })
    (by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, a, b⟩, rfl⟩
      simp only [Submodule.comap_coe, Set.mem_preimage, map_sub, lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, SetLike.mem_coe]
      refine Submodule.subset_span ⟨⟨k, a * a', b * b'⟩, by simp [smul_mul_assoc]⟩)

def Aox_FB_smul_M : A ⊗[F] B →ₗ[F] M h𝔞 h𝔟 →ₗ[F] M h𝔞 h𝔟 :=
  TensorProduct.lift
  { toFun := fun a' =>
    { toFun := fun b' => Aox_FB_smul_M_aux _ _ a' b'
      map_add' := by
        intro b1' b2'
        ext a b
        simp only [Aox_FB_smul_M_aux, AlgebraTensorModule.curry_apply, curry_apply,
          LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.mapQ_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.add_apply]
        rw [mul_add, tmul_add]
        rfl
      map_smul' := by
        intro f b'
        ext a b
        simp only [Aox_FB_smul_M_aux, Algebra.mul_smul_comm, tmul_smul,
          AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
          LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
          lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.mk_smul, RingHom.id_apply,
          LinearMap.smul_apply] }
    map_add' := by
      intro a1' a2'
      ext b' a b
      simp only [Aox_FB_smul_M_aux, mul_add, add_tmul, LinearMap.coe_mk, AddHom.coe_mk,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        lift.tmul, Submodule.Quotient.mk_add, LinearMap.add_apply]
    map_smul' := by
      intro f a'
      ext b' a b
      simp only [Aox_FB_smul_M_aux, Algebra.mul_smul_comm, LinearMap.coe_mk, AddHom.coe_mk,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        lift.tmul, RingHom.id_apply, LinearMap.smul_apply]
      rw [← smul_tmul']
      simp only [Submodule.Quotient.mk_smul] }

@[simp]
lemma Aox_FB_smul_M_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    Aox_FB_smul_M h𝔞 h𝔟 (a' ⊗ₜ[F] b') (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M h𝔞 h𝔟) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl


instance : SMul (A ⊗[F] B)ᵐᵒᵖ (M h𝔞 h𝔟) where
  smul x y := Aox_FB_smul_M _ _ x.unop y

@[simp]
lemma Aox_FB_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    op (a' ⊗ₜ[F] b') • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M h𝔞 h𝔟) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl

instance : MulAction (A ⊗[F] B)ᵐᵒᵖ (M h𝔞 h𝔟) where
  one_smul := by
    intro x
    rw [show (1 : (A ⊗[F] B)ᵐᵒᵖ) = op 1 from rfl,
      Algebra.TensorProduct.one_def]
    change Aox_FB_smul_M h𝔞 h𝔟 (1 ⊗ₜ[F] 1) x = LinearMap.id (R := F) x
    refine LinearMap.ext_iff |>.1 ?_ x
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Aox_FB_smul_M_op_tmul_smul_mk_tmul, _root_.mul_one, LinearMap.id_comp]
  mul_smul := by
    rintro ⟨x⟩ ⟨y⟩ b
    change Aox_FB_smul_M h𝔞 h𝔟 (y * x) _ = Aox_FB_smul_M h𝔞 h𝔟 x (Aox_FB_smul_M h𝔞 h𝔟 y b)
    rw [← LinearMap.comp_apply]
    refine LinearMap.ext_iff |>.1 ?_ b
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    induction x using TensorProduct.induction_on with
    | tmul xl rl =>
      induction y using TensorProduct.induction_on with
      | tmul yl yr =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, Aox_FB_smul_M_op_tmul_smul_mk_tmul,
          _root_.mul_assoc]
      | add y y' hy hy' =>
        simp only [add_mul, map_add, LinearMap.add_apply, hy, hy']
      | zero =>
        simp only [zero_mul, map_zero, LinearMap.zero_apply]
    | add x x' hx hx' =>
      simp only [mul_add, map_add, LinearMap.add_apply, hx, hx']
    | zero =>
      simp only [mul_zero, map_zero, LinearMap.zero_apply]

instance : DistribMulAction (A ⊗[F] B)ᵐᵒᵖ (M h𝔞 h𝔟) where
  smul_zero := by
    intro x
    change Aox_FB_smul_M h𝔞 h𝔟 _ _ = _
    simp
  smul_add := by
    intro x a b
    change Aox_FB_smul_M h𝔞 h𝔟 _ _ = Aox_FB_smul_M h𝔞 h𝔟 _ _ + Aox_FB_smul_M h𝔞 h𝔟 _ _
    simp

instance : Module (A ⊗[F] B)ᵐᵒᵖ (M h𝔞 h𝔟) where
  add_smul := by
    intro x y a
    change Aox_FB_smul_M h𝔞 h𝔟 _ _ = Aox_FB_smul_M h𝔞 h𝔟 _ _ + Aox_FB_smul_M h𝔞 h𝔟 _ _
    simp
  zero_smul := by
    intro x
    change Aox_FB_smul_M h𝔞 h𝔟 _ _ = _
    simp

end Aox_FB_mod

section C_mod

def F_smul_mul_compatible (f : F) (a a' : A) :
    (f • a) * a' = a * (f • a') := by
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

def C_smul_aux (c : C) : M h𝔞 h𝔟 →ₗ[F] M h𝔞 h𝔟 :=
  Submodule.mapQ (Submodule.span F (S h𝔞 h𝔟)) (Submodule.span F (S h𝔞 h𝔟))
    (TensorProduct.lift
      { toFun := fun a =>
        { toFun := fun b =>
            ∑ σ : K ≃ₐ[F] K, ((c.1 σ • x_AsBasis h𝔞 σ) * a) ⊗ₜ (x_AsBasis h𝔟 σ * b)
          map_add' := by
            intro b b'
            dsimp only
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [mul_add, tmul_add]
          map_smul' := by
            intro f b
            dsimp only [RingHom.id_apply]
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [smul_tmul', smul_tmul, ← F_smul_mul_compatible]
            simp only [Algebra.smul_mul_assoc, tmul_smul] }
        map_add' := by
          intro a a'
          ext b : 1
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp [mul_add, add_tmul]
        map_smul' := by
          intro f a
          ext b : 1
          simp only [Algebra.mul_smul_comm, LinearMap.coe_mk, AddHom.coe_mk,
            RingHom.id_apply, LinearMap.smul_apply]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [smul_tmul'] })
  (by
    rw [Submodule.span_le]
    rintro _ ⟨⟨k, a, b⟩, rfl⟩
    simp only [Submodule.comap_coe, Set.mem_preimage, map_sub, lift.tmul,
      LinearMap.coe_mk, AddHom.coe_mk, SetLike.mem_coe]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun σ _ =>
      Submodule.subset_span ⟨⟨σ k, c.1 σ • (x_AsBasis h𝔞 σ * a), x_AsBasis h𝔟 σ * b⟩, ?_⟩
    simp only [← smul_mul_assoc, CrossProduct.smul_def, _root_.mul_assoc, ← map_mul]
    congr 2 <;>
    simp only [← _root_.mul_assoc ((x_AsBasis h𝔞) σ), ← _root_.mul_assoc ((x_AsBasis h𝔟) σ),
      x_AsBasis_conj''] <;>
    simp only [← _root_.mul_assoc, ← map_mul, mul_comm (σ k)])


lemma C_smul_aux_calc (k : K) (σ : K ≃ₐ[F] K) (a : A) (b : B) :
    C_smul_aux _ _ (k • x_AsBasis (h𝔞𝔟 h𝔞 h𝔟) σ) (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M h𝔞 h𝔟) =
    Submodule.Quotient.mk (((k • x_AsBasis h𝔞 σ) * a) ⊗ₜ (x_AsBasis h𝔟 σ * b)) := by
  delta C_smul_aux
  rw [Submodule.mapQ_apply, lift.tmul]
  congr 1
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem σ (Finset.mem_univ _)]
  swap
  · rintro τ - h
    erw [show (k • (x_AsBasis (h𝔞𝔟 h𝔞 h𝔟)) σ).val τ = 0 by
      simp only [x_AsBasis_apply, CrossProduct.smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
        Pi.mul_apply, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val,
        crossProductMul_single_single, AlgEquiv.one_apply, _root_.mul_one]
      rw [_root_.one_mul, Pi.single_apply, if_neg h], zero_smul, zero_mul, zero_tmul]
  congr 2
  simp only [x_AsBasis_apply, CrossProduct.smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
    Pi.mul_apply, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val,
    crossProductMul_single_single, AlgEquiv.one_apply, _root_.mul_one]
  rw [_root_.one_mul, Pi.single_eq_same, a_one_left h𝔞, a_one_left h𝔟]
  congr 2
  field_simp
  left
  rw [mul_comm]


set_option maxHeartbeats 400000 in
def C_smul : C →ₗ[F] M h𝔞 h𝔟 →ₗ[F] M h𝔞 h𝔟 where
  toFun c := C_smul_aux h𝔞 h𝔟 c
  map_add' := by
    intro c c'
    dsimp only
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.add_apply]
    delta C_smul_aux
    rw [Submodule.mapQ_apply, lift.tmul, Submodule.mapQ_apply, lift.tmul,
        Submodule.mapQ_apply, lift.tmul]
    change Submodule.Quotient.mk (∑ _, _) = Submodule.Quotient.mk ((∑ _, _) + (∑ _, _))
    change Submodule.mkQ _ _ = Submodule.mkQ _ _
    rw [map_sum, map_add, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← map_add, ← add_tmul]
    congr 2
    simp only [add_val, Pi.add_apply, x_AsBasis_apply, add_smul, add_mul]
  map_smul' := by
    intro f c
    dsimp only
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, RingHom.id_apply,
      LinearMap.smul_apply]
    delta C_smul_aux
    rw [Submodule.mapQ_apply, lift.tmul, Submodule.mapQ_apply, lift.tmul]
    change Submodule.mkQ _ (∑ _, _) = f • Submodule.mkQ _ (∑ _, _)
    rw [← map_smul, Finset.smul_sum]
    simp_rw [smul_tmul']
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    simp only [smul_val, crossProductSMul, LinearMap.lsum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
      Function.comp_apply, Function.eval, Function.update_apply, Pi.zero_apply, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, x_AsBasis_apply, smul_assoc, Algebra.smul_mul_assoc,
      smul_mul_assoc]


instance : SMul C (M h𝔞 h𝔟) where
  smul c x := C_smul h𝔞 h𝔟 c x

lemma C_smul_calc (k : K) (σ : K ≃ₐ[F] K) (a : A) (b : B) :
    (k • x_AsBasis (h𝔞𝔟 h𝔞 h𝔟) σ) • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M h𝔞 h𝔟) =
    Submodule.Quotient.mk (((k • x_AsBasis h𝔞 σ) * a) ⊗ₜ (x_AsBasis h𝔟 σ * b)) :=
  C_smul_aux_calc h𝔞 h𝔟 k σ a b

instance : MulAction C (M h𝔞 h𝔟) where
  one_smul := by
    intro x
    induction x using Quotient.inductionOn' with | h x =>
    change (1 : C) • Submodule.Quotient.mk x = Submodule.Quotient.mk x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      rw [show (1 : C) = ((𝔟 1).1⁻¹ * (𝔞 1).1⁻¹) • x_AsBasis (h𝔞𝔟 h𝔞 h𝔟) 1 by
        simp only [CrossProduct.one_def, Pi.mul_apply, Units.val_mul, mul_inv_rev, x_AsBasis_apply,
          mul_smul], C_smul_calc, mul_smul, ← CrossProduct.one_def, smul_mul_assoc, _root_.one_mul,
          Submodule.Quotient.eq]
      refine Submodule.subset_span ⟨⟨(𝔟 1).1⁻¹, a, x_AsBasis h𝔟 1 * b⟩, ?_⟩
      simp only [← smul_mul_assoc, ← CrossProduct.one_def, _root_.one_mul]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add]
      conv_rhs => rw [← hx, ← hy]
      change C_smul_aux h𝔞 h𝔟 _ _ =  C_smul_aux h𝔞 h𝔟 _ _ +  C_smul_aux h𝔞 h𝔟 _ _
      simp only [map_add]
    | zero =>
      simp only [Submodule.Quotient.mk_zero]
      change C_smul_aux h𝔞 h𝔟 _ _ = _
      simp only [map_zero]
  mul_smul := by
    intro x y ab
    induction x using single_induction with
    | single σ x =>
      induction y using single_induction with
      | single τ y =>
        induction ab using Quotient.inductionOn' with | h ab =>
        induction ab using TensorProduct.induction_on with
        | tmul a b =>
          change _ • Submodule.Quotient.mk _ = _ • _ • Submodule.Quotient.mk _
          rw [single_in_xAsBasis, single_in_xAsBasis, smul_mul_assoc,
            CrossProduct.smul_def _ y, ← _root_.mul_assoc, x__conj'',
            smul_mul_assoc, x_AsBasis_mul, Pi.mul_apply, mul_comm _ (𝔟 _),
            Units.val_mul, ← mul_smul, ← mul_smul, C_smul_calc, ← CrossProduct.smul_def,
            C_smul_calc, C_smul_calc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
            CrossProduct.smul_def _ y, ← _root_.mul_assoc _ (ι h𝔞 y), x__conj'',
            smul_mul_assoc, ← _root_.mul_assoc _ _ a, x_AsBasis_mul, ← _root_.mul_assoc _ _ b,
            x_AsBasis_mul, Submodule.Quotient.eq, ← mul_smul]
          refine Submodule.subset_span ⟨⟨𝔟 (σ, τ), (x * σ y * 𝔞 (σ, τ)) •
            ((x_AsBasis h𝔞) (σ * τ) * a), (x_AsBasis h𝔟) (σ * τ) * b⟩, ?_⟩
          dsimp only
          rw [← smul_assoc, smul_mul_assoc, ← smul_assoc, smul_mul_assoc]
          congr 3
          simp only [smul_eq_mul]
          ring
        | add z z' hz hz' =>
          change C_smul_aux h𝔞 h𝔟 _ _ = C_smul_aux h𝔞 h𝔟 _ _ at hz hz' ⊢
          rw [Submodule.Quotient.mk''_eq_mk] at hz hz'
          rw [Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.mk_add, map_add,
            hz, hz']
          change C_smul_aux h𝔞 h𝔟 _ (C_smul_aux _ _ _ _) +
            C_smul_aux h𝔞 h𝔟 _ (C_smul_aux _ _ _ _) = C_smul_aux h𝔞 h𝔟 _ (C_smul_aux h𝔞 h𝔟 _ _)
          rw [← map_add, ← map_add]
        | zero =>
          change C_smul_aux h𝔞 h𝔟 _ _ = C_smul_aux h𝔞 h𝔟 _ (C_smul_aux h𝔞 h𝔟 _ _)
          rw [show Quotient.mk'' 0 = (0 : M _ _) from rfl, map_zero, map_zero, map_zero]
      | add y y' hy hy' =>
        change C_smul h𝔞 h𝔟 _ _ = C_smul h𝔞 h𝔟 _ _ at hy hy' ⊢
        change _ = C_smul h𝔞 h𝔟 _ (C_smul h𝔞 h𝔟 _ _)
        erw [mul_add, map_add, map_add, map_add]
        simp only [LinearMap.add_apply, hy, hy']
        rfl
      | zero =>
        erw [mul_zero]
        change C_smul h𝔞 h𝔟 _ _ = C_smul h𝔞 h𝔟 _ (C_smul h𝔞 h𝔟 _ _)
        simp only [map_zero, LinearMap.zero_apply]
        erw [map_zero, map_zero]
    | add x x' hx hx' =>
      erw [add_mul]
      change C_smul h𝔞 h𝔟 _ _ = C_smul h𝔞 h𝔟 _ _ at hx hx' ⊢
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hx']
      erw [map_add]
      rfl
    | zero =>
      erw [zero_mul]
      change C_smul h𝔞 h𝔟 _ _ = C_smul h𝔞 h𝔟 0 (C_smul h𝔞 h𝔟 _ _)
      simp only [map_zero, LinearMap.zero_apply]

example : True := ⟨⟩
-- #check QuotientAddGroup.mk_add
instance : DistribMulAction C (M h𝔞 h𝔟) where
  smul_zero := by
    intro c
    change C_smul h𝔞 h𝔟 _ _ = 0
    simp
  smul_add := by
    intro c x y
    change C_smul h𝔞 h𝔟 _ _ = C_smul h𝔞 h𝔟 _ _ + C_smul h𝔞 h𝔟 _ _
    simp

instance : Module C (M h𝔞 h𝔟) where
  add_smul := by
    intro c c' x
    change C_smul h𝔞 h𝔟 _ _ = C_smul h𝔞 h𝔟 _ _ + C_smul h𝔞 h𝔟 _ _
    simp only [map_add, LinearMap.add_apply]
  zero_smul := by
    intro x
    change C_smul h𝔞 h𝔟 _ _ = _
    simp

end C_mod

section bimodule

instance : SMulCommClass (A ⊗[F] B)ᵐᵒᵖ C (M h𝔞 h𝔟) where
  smul_comm := by
    rintro ⟨x⟩ c m
    induction m using Quotient.inductionOn' with | h m =>
    change (op x) • c • Submodule.Quotient.mk _ = c • op x • Submodule.Quotient.mk _
    induction x using TensorProduct.induction_on with
    | tmul a' b' =>
      induction m using TensorProduct.induction_on with
      | tmul a b =>
        induction c using single_induction with
        | single σ c =>
          rw [single_in_xAsBasis, C_smul_calc, Aox_FB_op_tmul_smul_mk_tmul,
            Aox_FB_op_tmul_smul_mk_tmul, C_smul_calc, _root_.mul_assoc, _root_.mul_assoc]
        | add c c' hc hc' =>
          simp only [show (⟨c.1 + c'.1⟩ : C) = (⟨c.1⟩ + ⟨c'.1⟩ : C) by rfl, add_smul, smul_add, hc,
            Aox_FB_op_tmul_smul_mk_tmul, hc']
        | zero =>
          erw [zero_smul, zero_smul]
          rw [smul_zero]
      | add x y hx hy =>
        simp only [Submodule.Quotient.mk_add, smul_add] at hx hy ⊢
        simp only [hx, hy]
      | zero => erw [smul_zero]
    | add x y hx hy =>
      simp only [op_add, add_smul, hx, hy, smul_add]
    | zero =>
      erw [zero_smul]

end bimodule

section iso

set_option maxHeartbeats 400000 in
instance : IsScalarTower F C (M h𝔞 h𝔟) where
  smul_assoc f c m := by
    induction m using Quotient.inductionOn' with | h m =>
    change _ • Submodule.Quotient.mk _ = _ • _ • Submodule.Quotient.mk _
    induction m using TensorProduct.induction_on with
    | tmul a b =>
      induction c using single_induction with
      | single σ c =>
        rw [single_in_xAsBasis, C_smul_calc]
        rw [show f • c • (x_AsBasis (h𝔞𝔟 h𝔞 h𝔟)) σ = algebraMap F K f • c • (x_AsBasis (h𝔞𝔟 h𝔞 h𝔟)) σ by
          simp only [Algebra.smul_def]
          rw [GoodRep.CrossProduct.smul_def]
          congr 1
          delta CrossProduct.ι
          simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, AlgHom.commutes, algebraMap_val]]
        rw [← smul_assoc, C_smul_calc, ← Submodule.Quotient.mk_smul]
        congr 2
        simp only [smul_eq_mul, x_AsBasis_apply]
        ext τ
        simp only [CrossProduct.smul_def, map_mul, AlgHom.commutes, algebraMap_val,
          Algebra.smul_mul_assoc, _root_.one_mul, smul_val, crossProductSMul, LinearMap.lsum_apply,
          LinearMap.coe_mk, AddHom.coe_mk, mul_val, ι_apply_val, Prod.mk_one_one,
          Units.val_inv_eq_inv_val, crossProductMul_single_single, AlgEquiv.one_apply,
          _root_.mul_one, LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj,
          Finset.sum_apply, Function.comp_apply, Function.eval, Function.update_apply,
          Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      | add c c' hc hc' =>
        erw [add_smul, smul_add, add_smul, hc, hc', smul_add]
      | zero =>
        erw [smul_zero, zero_smul, smul_zero]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add, smul_add, hx, hy]
    | zero =>
      erw [smul_zero]

example : True := ⟨⟩

instance : Module F (M h𝔞 h𝔟) := inferInstance

noncomputable def φ0 :
    (A ⊗[F] B)ᵐᵒᵖ →ₐ[F] Module.End C (M h𝔞 h𝔟) where
  toFun x :=
  { toFun := fun m => x • m
    map_add' := by intros; dsimp only; rw [smul_add]
    map_smul' := by
      intro c y
      simp only [RingHom.id_apply]
      rw [smul_comm] }
  map_one' := by
    refine LinearMap.ext fun _ => ?_
    simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply, implies_true]
  map_mul' := by
    intro x y
    refine LinearMap.ext fun _ => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply]
    rw [mul_smul]
  map_zero' := by
    refine LinearMap.ext fun _ => ?_
    simp only [zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  map_add' := by
    intro x y
    refine LinearMap.ext fun _ => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_smul]
  commutes' := by
    intro f
    refine LinearMap.ext fun m => ?_
    simp only [MulOpposite.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, algebraMap_val,
      LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply]
    induction m using Quotient.inductionOn' with | h m =>
    induction m using TensorProduct.induction_on with
    | tmul a b =>
      erw [Aox_FB_op_tmul_smul_mk_tmul]
      rw [Algebra.smul_def, _root_.mul_one, _root_.mul_one, ← Algebra.commutes f,
        ← Algebra.smul_def, ← smul_tmul']
      rfl
    | add x y hx hy =>
      simp only at hx hy ⊢
      have := congr($hx + $hy)
      rw [← smul_add, ← smul_add] at this
      exact this
    | zero =>
      erw [smul_zero]

set_option synthInstance.maxHeartbeats 40000 in
def MtoAox_KB : M h𝔞 h𝔟 →ₗ[F] A ⊗[K] B :=
  Submodule.liftQ _
    (TensorProduct.lift
      { toFun := fun a =>
        { toFun := fun b => a ⊗ₜ b
          map_add' := by simp [tmul_add]
          map_smul' := by simp }
        map_add' := by intros; ext; simp [add_tmul]
        map_smul' := by intros; ext; simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply, smul_tmul'] })
    (by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, a, b⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, tmul_smul, smul_tmul', sub_self])

def Aox_KBToM_aux : A ⊗[K] B →+ M h𝔞 h𝔟 :=
TensorProduct.liftAddHom
  { toFun := fun a =>
    { toFun := fun b => Submodule.Quotient.mk <| a ⊗ₜ b
      map_zero' := by simp
      map_add' := by simp [tmul_add] }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp [add_tmul] } <| fun k a b => by
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span <| ⟨⟨k, a, b⟩, rfl⟩

set_option synthInstance.maxHeartbeats 80000 in
def Aox_KBToM : A ⊗[K] B →ₗ[F] M h𝔞 h𝔟 where
  __ := Aox_KBToM_aux h𝔞 h𝔟
  map_smul' := by
    intro f x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      simp only [Aox_KBToM_aux, smul_tmul', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, RingHom.id_apply]
      rw [← Submodule.Quotient.mk_smul, smul_tmul']
    | add x y hx hy =>
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply, smul_add,
        map_add] at hx hy ⊢
      simp only [hx, hy]
    | zero =>
      simp only [smul_zero, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_zero,
        RingHom.id_apply]

set_option synthInstance.maxHeartbeats 80000 in
def Aox_KBEquivM : M h𝔞 h𝔟 ≃ₗ[F] A ⊗[K] B :=
LinearEquiv.ofLinear
  (MtoAox_KB _ _)
  (Aox_KBToM _ _)
  (by
    ext x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      simp only [MtoAox_KB, Aox_KBToM, Aox_KBToM_aux, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        Function.comp_apply, liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Submodule.liftQ_apply, lift.tmul, LinearMap.id_coe, id_eq]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hx hy
      simp only [LinearMap.coe_comp, Function.comp_apply, map_add, hx, hy, LinearMap.id_coe, id_eq]
    | zero => simp)
  (by
    ext a b
    simp only [Aox_KBToM, Aox_KBToM_aux, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      MtoAox_KB, AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.liftQ_apply, lift.tmul, liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      LinearMap.id_comp])

open Module
lemma M_F_dim [IsGalois F K] : finrank F (M h𝔞 h𝔟) = (finrank F K)^3 := by
  rw [LinearEquiv.finrank_eq (Aox_KBEquivM h𝔞 h𝔟),
    show finrank F (A ⊗[K] B) = finrank F K * finrank K (A ⊗[K] B) from
      Eq.symm (finrank_mul_finrank F K (A ⊗[K] B)),
    finrank_tensorProduct, finrank_eq_card_basis (x_AsBasis h𝔞),
    finrank_eq_card_basis (x_AsBasis h𝔟), IsGalois.card_aut_eq_finrank,
    pow_three]

instance [IsGalois F K] : FiniteDimensional F C :=
  .of_finrank_eq_succ (n := (finrank F K)^2 - 1) <| by
    rw [CrossProduct.dim_eq_square (h𝔞𝔟 h𝔞 h𝔟)]
    refine Nat.succ_pred_eq_of_pos (pow_two_pos_of_ne_zero ?_) |>.symm
    have : 0 < finrank F K := finrank_pos
    omega

instance [IsGalois F K] : Module.Finite C (M h𝔞 h𝔟) :=
  Module.Finite.right F C (M h𝔞 h𝔟)

lemma exists_simple_module_directSum [IsGalois F K] :
  ∃ (S : Type) (_ : AddCommGroup S) (_ : Module C S) (_ : IsSimpleModule C S)
    (ι : Type) (_ : Fintype ι),
    Nonempty (C ≃ₗ[C] ι →₀ S) := by
  obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring F C C
  refine ⟨S, inferInstance, inferInstance, inferInstance, ι, ?_, ⟨iso⟩⟩
  haveI infinite : Module.Finite C (ι →₀ S) := Module.Finite.equiv iso
  letI : Module F S := Module.compHom S (algebraMap F C)

  haveI : LinearMap.CompatibleSMul C (ι →₀ S) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    simp only [algebraMap_val, smul_assoc, one_smul]
  let iso' : C ≃ₗ[F] (ι →₀ S) := iso.restrictScalars F
  haveI : IsScalarTower F C (ι →₀ S) := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]
  haveI : Module.Finite F (ι →₀ S) := Module.Finite.trans C (ι →₀ S)
  have eq := LinearEquiv.finrank_eq iso'
  -- rw [M_F_dim, pow_three] at eq
  refine (@Cardinal.lt_aleph0_iff_fintype ι).1 ?_ |>.some
  apply_fun ((↑) : ℕ → Cardinal) at eq
  rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp F S ι] at eq
  have ineq : Module.rank F C < Cardinal.aleph0 := by
    rw [rank_lt_aleph0_iff]; infer_instance
  rw [eq] at ineq
  simp only [Cardinal.lift_id] at ineq
  haveI : Nontrivial S := IsSimpleModule.nontrivial C S

  have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι) (Module.rank F S)
    (by
      suffices 0 < Module.rank F S by exact Ne.symm (ne_of_lt this)
      apply rank_pos)
  rw [mul_comm] at ineq2
  exact lt_of_le_of_lt ineq2 ineq

variable [IsGalois F K]

def simpleMod : Type := exists_simple_module_directSum h𝔞 h𝔟 |>.choose

local notation "SM" => simpleMod h𝔞 h𝔟

instance : AddCommGroup SM := exists_simple_module_directSum h𝔞 h𝔟 |>.choose_spec.choose

instance : Module C SM := exists_simple_module_directSum h𝔞 h𝔟 |>.choose_spec.choose_spec.choose

instance : Module F SM := Module.compHom SM (algebraMap F C)

instance : IsSimpleModule C SM := exists_simple_module_directSum h𝔞 h𝔟
  |>.choose_spec.choose_spec.choose_spec.choose

def indexingSet : Type := exists_simple_module_directSum h𝔞 h𝔟
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose

local notation "ι" => indexingSet h𝔞 h𝔟

instance : Fintype ι := exists_simple_module_directSum h𝔞 h𝔟
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

def isoιSM : C ≃ₗ[C] ι →₀ SM := exists_simple_module_directSum h𝔞 h𝔟
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

instance : Nonempty ι := by
  by_contra!
  simp only [not_nonempty_iff] at this
  haveI : Subsingleton (ι →₀ SM) := inferInstance
  haveI : Subsingleton C := isoιSM h𝔞 h𝔟 |>.toEquiv.subsingleton
  haveI : Nontrivial C := inferInstance
  rw [← not_subsingleton_iff_nontrivial] at this
  contradiction

instance : NeZero (Fintype.card ι) := by
  constructor
  simp

def isoιSMPow : C ≃ₗ[C] ι → SM :=
  isoιSM h𝔞 h𝔟 ≪≫ₗ Finsupp.linearEquivFunOnFinite C SM ι

def isoιSMPow' : C ≃ₗ[C] Fin (Fintype.card ι) → SM :=
  isoιSMPow h𝔞 h𝔟 ≪≫ₗ
  { __ := Equiv.arrowCongr (Fintype.equivFinOfCardEq (α := ι) rfl : ι ≃ Fin (Fintype.card ι))
      (Equiv.refl _)
    map_add' := by
      intros v w
      rfl
    map_smul' := by
      intros; rfl }


instance : LinearMap.CompatibleSMul (M h𝔞 h𝔟) (ι →₀ SM) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    simp only [algebraMap_val, smul_assoc, one_smul]

instance : IsScalarTower F C SM := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]

instance : Module.Finite C (ι →₀ SM) := Module.Finite.equiv (isoιSM h𝔞 h𝔟)

instance : Module.Finite F (ι →₀ SM) := Module.Finite.trans C (ι →₀ SM)

instance : SMulCommClass C F SM where
  smul_comm c f a := by
    show c • algebraMap F C f • a = algebraMap F C f • _
    rw [← mul_smul, ← Algebra.commutes, mul_smul]

section C_iso

instance [DecidableEq (Module.End C SM)] : DivisionRing (Module.End C SM) :=
  Module.End.divisionRing

variable [DecidableEq (Module.End C SM)]

instance : Algebra F (Module.End C SM) := Module.End.instAlgebra F C SM

def isoDagger (m : ℕ) [NeZero m] :
    (Module.End C (Fin m → SM)) ≃ₐ[F]
    Matrix (Fin m) (Fin m) (Module.End C SM) where
  __ := endPowEquivMatrix C SM m
  commutes' := by
    intro f
    ext i j x
    simp only [endPowEquivMatrix, endVecAlgEquivMatrixEnd, endVecRingEquivMatrixEnd,
      RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, AlgEquiv.coe_ringEquiv,
      AlgEquiv.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, Pi.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · simp only [h, algebraMap_end_apply, Pi.smul_apply, Pi.single_eq_same]
    · simp only [algebraMap_end_apply, Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero,
      LinearMap.zero_apply]

def mopEquivEnd' : Cᵐᵒᵖ ≃ₐ[F] Module.End C C :=
AlgEquiv.ofRingEquiv (f := mopEquivEnd C) <| by
  intro f
  ext x
  simp only [mopEquivEnd, mopToEnd, MulOpposite.algebraMap_apply, algebraMap_val, op_smul, op_one,
    RingEquiv.coe_ofBijective, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, unop_smul, unop_one,
    Algebra.mul_smul_comm, _root_.mul_one, LinearMap.coe_mk, AddHom.coe_mk, smul_val, one_val,
    Prod.mk_one_one, Pi.mul_apply, Units.val_mul, mul_inv_rev, crossProductSMul_single,
    Module.algebraMap_end_apply]


set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 600000 in
def C_iso_aux : Cᵐᵒᵖ ≃ₐ[F] Module.End C (Fin (Fintype.card ι) → SM) :=
  let iso1 : Module.End C (Fin (Fintype.card ι) → SM) ≃ₐ[F] Module.End C C :=
  { toFun := fun x => (isoιSMPow' h𝔞 h𝔟).symm ∘ₗ x ∘ₗ (isoιSMPow' h𝔞 h𝔟)
    invFun := fun x => (isoιSMPow' h𝔞 h𝔟) ∘ₗ x ∘ₗ (isoιSMPow' h𝔞 h𝔟).symm
    left_inv := by
      intro x; ext; simp
    right_inv := by
      intro x; ext; simp
    map_mul' := by
      intro x y; ext; simp
    map_add' := by
      intro x y; ext; simp
    commutes' := by
      intro f
      ext σ
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Module.algebraMap_end_apply, smul_val, one_val, Prod.mk_one_one, Pi.mul_apply, Units.val_mul,
        mul_inv_rev, crossProductSMul_single]
      rw [show f • (isoιSMPow' h𝔞 h𝔟) 1 = algebraMap F C f • (isoιSMPow' h𝔞 h𝔟) 1 by rfl]
      rw [map_smul]
      simp only [algebraMap_val, LinearEquiv.symm_apply_apply, smul_eq_mul, _root_.mul_one, smul_val,
        one_val, Prod.mk_one_one, Pi.mul_apply, Units.val_mul, mul_inv_rev, crossProductSMul_single] }
  mopEquivEnd' h𝔞 h𝔟 |>.trans iso1.symm

example : True := ⟨⟩

def C_iso_aux' : Cᵐᵒᵖ ≃ₐ[F] Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM) :=
  C_iso_aux h𝔞 h𝔟 |>.trans <| isoDagger h𝔞 h𝔟 _

omit [DecidableEq (Module.End C SM)] in
lemma dim_endCSM : (finrank F K)^2 =
  (Fintype.card ι) ^ 2 * finrank F (Module.End C SM) := by
  have eq1 := (C_iso_aux' h𝔞 h𝔟).toLinearEquiv.finrank_eq
  rw [show finrank F Cᵐᵒᵖ = finrank F C by
    refine LinearEquiv.finrank_eq
      { toFun := unop
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := op
        left_inv := unop_op
        right_inv := fun _ => rfl }, CrossProduct.dim_eq_square] at eq1
  rw [eq1, matrixEquivTensor (Fin (Fintype.card ι)) F (Module.End C SM)  |>.toLinearEquiv.finrank_eq,
    finrank_tensorProduct, finrank_matrix]
  simp only [Fintype.card_fin, finrank_self, _root_.mul_one, pow_two]
  group

def C_iso_aux'' : C ≃ₐ[F] (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM))ᵐᵒᵖ where
  toFun c := op <| C_iso_aux' _ _ (op c)
  invFun m := (C_iso_aux' _ _ |>.symm m.unop).unop
  left_inv := by
    intro c
    simp only [unop_op, AlgEquiv.symm_apply_apply]
  right_inv := by
    intro m
    simp only [op_unop, AlgEquiv.apply_symm_apply]
  map_mul' := by
    intro c c'
    simp only [op_mul, map_mul]
  map_add' := by
    intro c c'
    simp only [op_add, map_add]
  commutes' := by
    intro f
    simp only [algebraMap_val, op_smul, op_one, map_smul, map_one, MulOpposite.algebraMap_apply]
    rw [Algebra.smul_def]
    simp only [MulOpposite.algebraMap_apply, _root_.mul_one]

def C_iso : C ≃ₐ[F] (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM)ᵐᵒᵖ) :=
  C_iso_aux'' h𝔞 h𝔟 |>.trans ((matrixEquivMatrixMop_algebra F _ _).symm)

end C_iso

lemma M_directSum : ∃ (ιM : Type) (_ : Fintype ιM), Nonempty (M h𝔞 h𝔟 ≃ₗ[C] ιM →₀ SM) := by
  obtain ⟨ιM, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring' F C (M h𝔞 h𝔟) SM
  refine ⟨ιM, ?_, ⟨iso⟩⟩

  haveI : LinearMap.CompatibleSMul C (ιM →₀ SM) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    simp only [algebraMap_val, smul_assoc, one_smul]
  let iso' : M h𝔞 h𝔟 ≃ₗ[F] (ιM →₀ SM) := iso.restrictScalars F
  haveI : IsScalarTower F C (ιM →₀ SM) := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]
  haveI : Module.Finite C (M h𝔞 h𝔟) := Module.Finite.right F C (M h𝔞 h𝔟)
  haveI : Module.Finite C (ιM →₀ SM) := Module.Finite.equiv iso
  haveI : Module.Finite F (ιM →₀ SM) := Module.Finite.trans C (ιM →₀ SM)
  have eq := LinearEquiv.finrank_eq iso'
  rw [M_F_dim, pow_three] at eq
  refine (@Cardinal.lt_aleph0_iff_fintype ιM).1 ?_ |>.some
  apply_fun ((↑) : ℕ → Cardinal) at eq
  simp only [Nat.cast_mul] at eq
  rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp F SM ιM] at eq
  have ineq : Module.rank F K < Cardinal.aleph0 := by
    rw [Module.rank_lt_aleph0_iff]; infer_instance
  replace ineq : Module.rank F K * (Module.rank F K * Module.rank F K) < Cardinal.aleph0 := by
    apply Cardinal.mul_lt_aleph0
    · assumption
    apply Cardinal.mul_lt_aleph0 <;>
    assumption

  rw [eq] at ineq
  simp only [Cardinal.lift_id] at ineq
  haveI : Nontrivial SM := IsSimpleModule.nontrivial C SM

  have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ιM) (Module.rank F SM)
    (by
      suffices 0 < Module.rank F SM by exact Ne.symm (ne_of_lt this)
      apply rank_pos)
  rw [mul_comm] at ineq2
  exact lt_of_le_of_lt ineq2 ineq

def indexingSetM : Type := (M_directSum h𝔞 h𝔟).choose

local notation "ιM" => indexingSetM h𝔞 h𝔟

instance : Fintype ιM := (M_directSum h𝔞 h𝔟).choose_spec.choose

def M_iso_directSum : M h𝔞 h𝔟 ≃ₗ[C] ιM →₀ SM :=
  (M_directSum h𝔞 h𝔟).choose_spec.choose_spec.some

instance : Module.Finite C SM := by
  rw [Module.finite_def, Submodule.fg_def]
  obtain ⟨a, ha⟩ := IsSimpleModule.instIsPrincipal C (M := SM) ⊤
  exact ⟨{a}, Set.finite_singleton a, ha.symm⟩

instance : Module.Finite F SM := Module.Finite.trans C SM

lemma SM_F_dim : Fintype.card ι * finrank F SM = finrank F K ^ 2 := by
  have eq1 := LinearEquiv.finrank_eq (isoιSMPow' h𝔞 h𝔟 |>.restrictScalars F)
  rw [CrossProduct.dim_eq_square] at eq1
  have eq2 := rank_fun (η := (Fin (Fintype.card ι))) (M := SM) (R := F)
  rw [Fintype.card_fin, ← finrank_eq_rank F SM,
    show (Fintype.card ι : Cardinal) * (finrank F SM : Cardinal) =
      ((Fintype.card ι * finrank F SM : ℕ) : Cardinal) by simp] at eq2

  have := finrank_eq_of_rank_eq (n := Fintype.card ι * finrank F SM) eq2
  rw [this] at eq1
  exact eq1.symm

instance : Module.Finite C ((Fin (Fintype.card ι * finrank F K) →₀ SM)) := by
  infer_instance

instance : Module.Finite C (Fin (Fintype.card ι * finrank F K) → SM) := by
  have := Finsupp.linearEquivFunOnFinite C SM (Fin (Fintype.card ι * finrank F K))
  refine Module.Finite.equiv this

lemma M_iso_powAux : Nonempty (M h𝔞 h𝔟 ≃ₗ[C] Fin (finrank F K * Fintype.card ι) → SM) := by
  rw [linearEquiv_iff_finrank_eq_over_simple_ring F C]
  have eq2 := rank_fun (η := (Fin (finrank F K * Fintype.card ι))) (M := SM) (R := F)
  rw [Fintype.card_fin, ← finrank_eq_rank F SM,
    show ((finrank F K * Fintype.card ι : ℕ) : Cardinal) * (finrank F SM : Cardinal) =
      ((finrank F K * Fintype.card ι * finrank F SM : ℕ) : Cardinal) by simp] at eq2

  have := finrank_eq_of_rank_eq eq2
  rw [this, M_F_dim, _root_.mul_assoc, SM_F_dim, pow_three, pow_two]

def M_iso_pow : M h𝔞 h𝔟 ≃ₗ[C] Fin (finrank F K * Fintype.card ι) → SM :=
  M_iso_powAux _ _ |>.some

def M_iso_pow' : M h𝔞 h𝔟 ≃ₗ[F] Fin (finrank F K * Fintype.card ι) → SM :=
M_iso_pow _ _ |>.restrictScalars F

-- set_option maxHeartbeats 600000 in
def endCMIso :
    Module.End C (M h𝔞 h𝔟) ≃ₐ[F] Module.End C (Fin (finrank F K * Fintype.card ι) → SM) where
  toFun x := (M_iso_pow h𝔞 h𝔟) ∘ₗ x ∘ₗ (M_iso_pow h𝔞 h𝔟).symm
  invFun x := (M_iso_pow h𝔞 h𝔟).symm ∘ₗ x ∘ₗ (M_iso_pow h𝔞 h𝔟)
  left_inv := by
    intro x
    simp only [← LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  right_inv := by
    intro x
    simp only [← LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  map_mul' := by
    intro x y
    refine DFunLike.ext _ _ fun z => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.mul_apply,
      LinearEquiv.symm_apply_apply]
  map_add' := by
    intro x y
    refine DFunLike.ext _ _ fun z => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.add_apply,
      map_add]
  commutes' := by
    intro f
    refine DFunLike.ext _ _ fun z => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.algebraMap_end_apply]
    change  (M_iso_pow' h𝔞 h𝔟) (f • (M_iso_pow' h𝔞 h𝔟).symm z) = f • z
    rw [map_smul]
    simp only [algebraMap_val, LinearEquiv.apply_symm_apply, smul_assoc, one_smul]

example : True := ⟨⟩

instance : NeZero (finrank F K * Fintype.card ι) := by
  constructor
  simp only [ne_eq, mul_eq_zero, Fintype.card_ne_zero, or_false]
  have : 0 < finrank F K := finrank_pos
  omega

def endCMIso' :
    Module.End C (M h𝔞 h𝔟) ≃ₐ[F]
    Matrix (Fin (finrank F K * Fintype.card ι))
      (Fin (finrank F K * Fintype.card ι)) (Module.End C SM) :=
  endCMIso h𝔞 h𝔟  |>.trans <| isoDagger _ _ _

lemma dim_endCM :
    finrank F (Module.End C (M h𝔞 h𝔟)) = (finrank F K)^4 := by
  have := LinearEquiv.finrank_eq (endCMIso' h𝔞 h𝔟).toLinearEquiv
  rw [this]
  have := matrixEquivTensor (Fin (finrank F K * Fintype.card ι)) F (Module.End C SM)
    |>.toLinearEquiv.finrank_eq
  rw [this, finrank_tensorProduct, finrank_matrix]
  simp only [Fintype.card_fin]
  rw [show finrank F K * Fintype.card ι * (finrank F K * Fintype.card ι) =
    (Fintype.card ι)^2 * (finrank F K)^2 by group]
  rw [finrank_self, _root_.mul_one, ← _root_.mul_assoc, mul_comm _ ((Fintype.card ι)^2),
    ← dim_endCSM, pow_two, pow_succ, pow_three]
  group

def φ1 :
    (A ⊗[F] B)ᵐᵒᵖ ≃ₐ[F] Module.End C (M h𝔞 h𝔟) :=
  AlgEquiv.ofBijective (φ0 h𝔞 h𝔟) (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by
    rw [dim_endCM, show finrank F (A ⊗[F] B)ᵐᵒᵖ = finrank F (A ⊗[F] B) by
      refine LinearEquiv.finrank_eq
        { toFun := unop
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := op
          left_inv := unop_op
          right_inv := fun _ => rfl }, finrank_tensorProduct, CrossProduct.dim_eq_square,
      CrossProduct.dim_eq_square, pow_two, pow_succ]
    group)

def φ2 :
    (A ⊗[F] B) ≃ₐ[F] (Module.End C (M h𝔞 h𝔟))ᵐᵒᵖ where
  toFun a := op <| φ1 _ _ (op a)
  invFun g := (φ1 _ _ |>.symm g.unop).unop
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  map_mul' := by intros; simp
  map_add' := by intros; simp
  commutes' := by
    intro f
    simp only [Algebra.TensorProduct.algebraMap_apply, algebraMap_val, MulOpposite.algebraMap_apply,
      op_inj]
    rw [← smul_tmul', op_smul]
    have := (φ0 h𝔞 h𝔟).commutes f
    rw [← this]
    rw [Algebra.algebraMap_eq_smul_one]
    rfl

def φ3 :
    (A ⊗[F] B) ≃ₐ[F]
    (Matrix (Fin (finrank F K * Fintype.card ι)) (Fin (finrank F K * Fintype.card ι))
      (Module.End C SM))ᵐᵒᵖ :=
  φ2 _ _ |>.trans (AlgEquiv.op <| endCMIso' _ _)

def φ4 :
    (A ⊗[F] B) ≃ₐ[F]
    (Matrix (Fin (finrank F K * Fintype.card ι)) (Fin (finrank F K * Fintype.card ι))
      (Module.End C SM)ᵐᵒᵖ) :=
  φ3 _ _ |>.trans ((matrixEquivMatrixMop_algebra F _ _).symm)

instance [DecidableEq (Module.End C SM)] : DivisionRing ((Module.End C SM)ᵐᵒᵖ) := by
  letI : DivisionRing (Module.End C SM) := Module.End.divisionRing
  infer_instance

lemma isBrauerEquivalent : IsBrauerEquivalent (⟨A ⊗[F] B⟩ : CSA F) ⟨C⟩ := by
  let iso1 := C_iso h𝔞 h𝔟 |>.mapMatrix (m := Fin (finrank F K))
  let iso11 := iso1.trans (Matrix.compAlgEquiv _ _ _ _) |>.trans
    (Matrix.reindexAlgEquiv _ _ finProdFinEquiv)
  let iso2 := φ4 h𝔞 h𝔟
  let iso3 := iso11.trans iso2.symm
  haveI : NeZero (finrank F K) := ⟨by have : 0 < finrank F K := finrank_pos; omega⟩
  exact ⟨1, finrank F K, (dim_one_iso (CSA.mk (A ⊗[F] B))).trans iso3.symm⟩

end iso

end map_mul

end map_mul_proof

namespace RelativeBrGroup

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

-- @[simps]
-- def fromSndAddMonoidHom :
--     H2 (galAct F K) →+ Additive (RelativeBrGroup K F) where
--   toFun := Additive.ofMul ∘ RelativeBrGroup.fromSnd _ _
--   map_zero' := by
--     simpa only [Function.comp_apply, ofMul_eq_zero] using map_one_proof.fromSnd_zero K F
--   map_add' := by
--     intro x y
--     induction x using Quotient.inductionOn' with | h x =>
--     induction y using Quotient.inductionOn' with | h y =>
--     simp only [Function.comp_apply]
--     rcases x with ⟨x, hx'⟩
--     have hx := isMulTwoCocycle_of_twoCocycles ⟨x, hx'⟩
--     rcases y with ⟨y, hy'⟩
--     have hy := isMulTwoCocycle_of_twoCocycles ⟨y, hy'⟩
--     rw [fromSnd_wd, fromSnd_wd]
--     erw [fromSnd_wd]
--     apply_fun Additive.toMul
--     simp only [AddMemClass.mk_add_mk, toMul_ofMul, toMul_add, MulMemClass.mk_mul_mk,
--       Subtype.mk.injEq]
--     change _ = Quotient.mk'' _
--     rw [Quotient.eq'']
--     exact map_mul_proof.isBrauerEquivalent hx hy |>.symm

-- def toSndAddMonoidHom : Additive (RelativeBrGroup K F) →+ H2 (galAct F K) where
--   toFun := RelativeBrGroup.toSnd ∘ Additive.toMul
--   map_zero' := by
--     simp only [Function.comp_apply, toMul_zero]
--     apply_fun fromSnd F K using equivSnd.symm.injective
--     rw [map_one_proof.fromSnd_zero]
--     exact congr_fun fromSnd_toSnd 1
--   map_add' := by
--     intro x y
--     dsimp only
--     apply_fun fromSndAddMonoidHom K F using equivSnd.symm.injective
--     rw [map_add]
--     simp only [Function.comp_apply, toMul_add, fromSndAddMonoidHom_apply,
--       show ∀ x, fromSnd F K (toSnd x) = x by intro x; exact congr_fun fromSnd_toSnd x, ofMul_mul,
--       ofMul_toMul]

def sndIso : H2 (galAct F K) ≃+ Additive (RelativeBrGroup K F) :=
  AddEquiv.mk' (equivSnd (F := F) (K := K)).symm <| by
    intro x y
    induction x using Quotient.inductionOn' with | h x =>
    induction y using Quotient.inductionOn' with | h y =>
    change fromSnd F K (Quotient.mk'' _) =
      fromSnd F K (Quotient.mk'' _) * fromSnd F K (Quotient.mk'' _)
    rw [fromSnd_wd, fromSnd_wd, fromSnd_wd]
    exact Subtype.ext <| Quotient.sound <| map_mul_proof.isBrauerEquivalent _ _ |>.symm

def isoSnd :
    Additive (RelativeBrGroup K F) ≃+ H2 (galAct F K) := sndIso K F |>.symm

#print axioms isoSnd


class MyMonoid (M : Type u) where
  e : M
  op : M → M → M
  op_assoc : ∀ a b c : M, op a (op b c) = op (op a b) c
  e_op : ∀ a : M, op e a = a
  op_e : ∀ a : M, op a e = a

instance : MyMonoid ℤ where
  e := 0
  op := (· + ·)
  op_assoc := by simp [add_assoc]
  e_op := by simp
  op_e := by simp

instance : MyMonoid ℤ where
  e := 1
  op := (· * ·)
  op_assoc := by simp [_root_.mul_assoc]
  e_op := by simp
  op_e := by simp

end RelativeBrGroup
