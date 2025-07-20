import BrauerGroup.ToSecond
import Mathlib.Algebra.Module.LinearMap.Basic

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

open scoped TensorProduct

-- namespace map_one_proof
-- section map_one

-- variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq Gal(K, F)]

-- set_option maxHeartbeats 1000000 in
-- def φ0 :
--     CrossProductAlgebra (F := F) (K := K) (a := 1)
--       (ha := isMulTwoCocycle_of_mem_twoCocycles 0 <| Submodule.zero_mem _) →ₗ[K]
--     Module.End F K :=
--   (CrossProductAlgebra.x_AsBasis (F := F) (K := K) (a := 1)
--     (ha := isMulTwoCocycle_of_mem_twoCocycles 0 <| Submodule.zero_mem _)).constr F
--     fun σ => σ.toLinearMap

-- def φ1 :
--     CrossProductAlgebra (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₗ[F]
--     Module.End F K :=
--   φ0 K F |>.restrictScalars F

-- def φ2 :
--     CrossProductAlgebra (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₐ[F]
--     Module.End F K :=
--   AlgHom.ofLinearMap (φ1 K F)
--     (by
--       generalize_proofs h
--       rw [show (1 : CrossProductAlgebra h) = .x_AsBasis h 1 by
--         ext1
--         simp]
--       delta φ1 φ0
--       rw [LinearMap.restrictScalars_apply, Basis.constr_basis]
--       rfl)
--     (by
--       rintro x y
--       change φ0 K F _ = φ0 K F _ * φ0 K F _
--       generalize_proofs h
--       induction x using CrossProductAlgebra.single_induction h with
--       | single x c =>
--         rw [show (⟨Pi.single x c⟩ : CrossProductAlgebra h) =
--           c • .x_AsBasis h x by
--           ext : 1
--           simp only [CrossProductAlgebra.x_AsBasis_apply, CrossProductAlgebra.smul_def, CrossProductAlgebra.mul_val,
--             CrossProductAlgebra.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
--             crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
--         rw [map_smul]
--         induction y using CrossProductAlgebra.single_induction h with
--         | single y d =>
--           rw [show (⟨Pi.single y d⟩ : CrossProductAlgebra h) =
--             d • .x_AsBasis h y by
--             ext : 1
--             simp only [CrossProductAlgebra.x_AsBasis_apply, CrossProductAlgebra.smul_def, CrossProductAlgebra.mul_val,
--               CrossProductAlgebra.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
--               crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
--           rw [show (c • CrossProductAlgebra.x_AsBasis h x) * (d • .x_AsBasis h y) =
--             (c * x d) • .x_AsBasis h (x * y) by
--             ext : 1
--             simp only [CrossProductAlgebra.x_AsBasis_apply, CrossProductAlgebra.smul_def, CrossProductAlgebra.mul_val,
--               CrossProductAlgebra.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
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
--     CrossProductAlgebra (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
--     Module.End F K :=
--   AlgEquiv.ofBijective (φ2 K F) (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by
--     rw [CrossProductAlgebra.dim_eq_sq]
--     rw [Module.finrank_linearMap, pow_two])

-- def φ4 :
--     CrossProductAlgebra (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
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
--   exact dim_one_iso (CSA.mk (CrossProductAlgebra.asCSA _).carrier).carrier

-- lemma fromSnd_zero : RelativeBrGroup.fromSnd (F := F) (K := K) 0 = 1 := map_one' K F

-- end map_one

-- end map_one_proof

namespace map_mul_proof
section map_mul

variable (α β : Gal(K, F) × Gal(K, F) → Kˣ)
variable [Fact <| IsMulTwoCocycle α] [Fact <| IsMulTwoCocycle β]

variable {K F α β}

local notation "A" => CrossProductAlgebra α
local notation "B" => CrossProductAlgebra β
local notation "C" => CrossProductAlgebra (α * β)

open CrossProductAlgebra TensorProduct

variable [FiniteDimensional F K]  [DecidableEq Gal(K, F)]

abbrev S : Set (A ⊗[F] B) :=
  Set.range (fun (cba : K × A × B) =>
    (cba.1 • cba.2.1) ⊗ₜ[F] cba.2.2 - cba.2.1 ⊗ₜ[F] (cba.1 • cba.2.2))

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp]
lemma mem_S (x : A ⊗[F] B) : x ∈ S ↔
    ∃ (k : K) (a : A) (b : B), x = (k • a) ⊗ₜ b - a ⊗ₜ (k • b) := by
  simp only [S, Set.mem_range, Prod.exists]
  aesop

variable (α β) in
@[reducible] def M := (A ⊗[F] B) ⧸ Submodule.span F S

instance : Fact (IsMulTwoCocycle (α * β)) := ⟨isMulTwoCocycle_of_mem_twoCocycles _ <|
  (twoCocyclesOfIsMulTwoCocycle Fact.out) + (twoCocyclesOfIsMulTwoCocycle Fact.out)|>.2⟩

-- instance : AddCommGroup (M α β) := inferInstance

-- instance : Module F (M α β) := inferInstance

open MulOpposite

section Aox_FB_mod

variable (α β) in
def Aox_FB_smul_M_aux (a' : A) (b' : B) : (M α β) →ₗ[F] (M α β) :=
  Submodule.mapQ (Submodule.span F S) (Submodule.span F S)
    (TensorProduct.lift
      { toFun a :=
        { toFun b := (a * a') ⊗ₜ (b * b')
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

def Aox_FB_smul_M_aux_aux (a' : A) : B →ₗ[F] M α β →ₗ[F] M α β where
  toFun b' := Aox_FB_smul_M_aux α β a' b'
  map_add' b1' b2' := by
    ext a b
    simp only [Aox_FB_smul_M_aux, AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.mapQ_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply]
    rw [mul_add, tmul_add]
    rfl
  map_smul' f b' := by
    ext a b
    simp only [Aox_FB_smul_M_aux, Algebra.mul_smul_comm, tmul_smul,
      AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.mk_smul, RingHom.id_apply,
      LinearMap.smul_apply]

def Aox_FB_smul_M : A ⊗[F] B →ₗ[F] M α β →ₗ[F] M α β :=
  TensorProduct.lift
  { toFun := Aox_FB_smul_M_aux_aux
    map_add' a1' a2' := by
      ext b' a b
      simp only [Aox_FB_smul_M_aux, mul_add, add_tmul, LinearMap.coe_mk, AddHom.coe_mk,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        lift.tmul, Submodule.Quotient.mk_add, LinearMap.add_apply, Aox_FB_smul_M_aux_aux]
    map_smul' f a' := by
      ext b' a b
      simp only [Aox_FB_smul_M_aux, Algebra.mul_smul_comm, LinearMap.coe_mk, AddHom.coe_mk,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        lift.tmul, RingHom.id_apply, LinearMap.smul_apply, Aox_FB_smul_M_aux_aux]
      rw [← smul_tmul']
      simp only [Submodule.Quotient.mk_smul] }

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp]
lemma Aox_FB_smul_M_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    Aox_FB_smul_M (a' ⊗ₜ[F] b') (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl

instance : SMul (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  smul x y := Aox_FB_smul_M x.unop y

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp]
lemma Aox_FB_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    op (a' ⊗ₜ[F] b') • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl

set_option maxSynthPendingDepth 3 in
instance : MulAction (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  one_smul := by
    intro x
    rw [show (1 : (A ⊗[F] B)ᵐᵒᵖ) = op 1 from rfl,
      Algebra.TensorProduct.one_def]
    change Aox_FB_smul_M (1 ⊗ₜ[F] 1) x = LinearMap.id (R := F) x
    refine LinearMap.ext_iff |>.1 ?_ x
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Aox_FB_smul_M_op_tmul_smul_mk_tmul, _root_.mul_one, LinearMap.id_comp]
  mul_smul := by
    rintro ⟨x⟩ ⟨y⟩ b
    change Aox_FB_smul_M (y * x) _ = Aox_FB_smul_M x (Aox_FB_smul_M y b)
    rw [← LinearMap.comp_apply]
    refine LinearMap.ext_iff |>.1 ?_ b
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    induction x using TensorProduct.induction_on with
    | tmul xl rl =>
      induction y using TensorProduct.induction_on with
      | tmul yl yr => simp [Aox_FB_smul_M_op_tmul_smul_mk_tmul, _root_.mul_assoc]
      | add y y' hy hy' => simp_all [add_mul]
      | zero => simp
    | add x x' hx hx' => simp_all [mul_add]
    | zero => simp

instance : DistribMulAction (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  smul_zero x := show Aox_FB_smul_M _ _ = _ by simp
  smul_add x a b := show Aox_FB_smul_M _ _ =
    Aox_FB_smul_M _ _ + Aox_FB_smul_M _ _ by simp

instance : Module (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  add_smul x y a := show Aox_FB_smul_M _ _ =
    Aox_FB_smul_M _ _ + Aox_FB_smul_M _ _ by simp
  zero_smul x := show Aox_FB_smul_M _ _ = _ by simp

end Aox_FB_mod

section C_mod

def F_smul_mul_compatible (f : F) (a a' : A) :
    (f • a) * a' = a * (f • a') := by
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

open CrossProductAlgebra in
def C_smul_aux (c : C) : M α β →ₗ[F] M α β :=
  Submodule.mapQ (Submodule.span F S) (Submodule.span F S)
    (TensorProduct.lift
      { toFun a := {
          toFun b := ∑ σ : Gal(K, F), ((c.1 σ • basis σ) * a) ⊗ₜ (basis σ * b)
          map_add' b b' := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [mul_add, tmul_add]
          map_smul' f b := by
            dsimp only [RingHom.id_apply]
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [smul_tmul', smul_tmul, ← F_smul_mul_compatible]
            simp only [Algebra.smul_mul_assoc, tmul_smul] }
        map_add' a a' := by
          ext b : 1
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp [mul_add, add_tmul]
        map_smul' f a := by
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
      Submodule.subset_span ⟨⟨σ k, c.1 σ • (basis σ * a), basis σ * b⟩, ?_⟩
    simp only [← smul_mul_assoc, _root_.mul_assoc, ← map_mul, basis_smul_comm]
    congr 2
    apply val_injective
    simp [CrossProductAlgebra.basis]
    induction b.val using Finsupp.induction_linear with
    | h0 => simp
    | hadd f g _ _ => simp_all
    | hsingle a b =>
      simp only [mulLinearMap_single_single, Finsupp.smul_single, smul_eq_mul, map_mul]
      congr 1
      field_simp [← _root_.mul_assoc])

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma C_smul_aux_calc (k : K) (σ : Gal(K, F)) (a : A) (b : B) :
    C_smul_aux (k • CrossProductAlgebra.basis σ) (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk (((k • CrossProductAlgebra.basis σ) * a) ⊗ₜ (CrossProductAlgebra.basis σ * b)) := by
  delta C_smul_aux
  rw [Submodule.mapQ_apply, lift.tmul]
  congr 1
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem σ (Finset.mem_univ _)]
  swap
  · rintro τ - h
    erw [show (k • CrossProductAlgebra.basis σ).val τ = 0 by
      simp [CrossProductAlgebra.basis, Finsupp.single_apply, Ne.symm h]]
    simp
  congr 2
  simp [CrossProductAlgebra.basis]

set_option maxHeartbeats 400000 in
def C_smul : C →ₗ[F] M α β →ₗ[F] M α β where
  toFun := C_smul_aux
  map_add' c c' := by
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
    simp [add_smul, add_mul]
  map_smul' f c := by
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
    simp

instance : SMul C (M α β) where
  smul c x := C_smul c x

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma C_smul_def (c : C) (x : M α β) : c • x = C_smul c x := rfl

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma C_smul_calc (k : K) (σ : Gal(K, F)) (a : A) (b : B) :
    (k • (CrossProductAlgebra.basis σ : C)) • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk (((k • CrossProductAlgebra.basis σ) * a) ⊗ₜ (CrossProductAlgebra.basis σ * b)) :=
  C_smul_aux_calc k σ a b

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
lemma CrossProductAlgebra.basis_mul_basis {f : Gal(K, F) × Gal(K, F) → Kˣ} (σ τ : Gal(K, F)) :
    basis (f := f) σ * basis τ = (f (σ, τ)).1 • basis (σ * τ) := by
  apply val_injective
  simp [basis]

omit [DecidableEq (K ≃ₐ[F] K)] in
set_option maxHeartbeats 1200000 in
theorem C_mul_smul' (x y : C) (ab : M α β) : (x * y) • ab = x • y • ab := by
  change ((⟨x.val⟩ : C) * ⟨y.val⟩) • ab = (⟨x.val⟩ : C) • (⟨y.val⟩ : C) • ab
  induction x.val using Finsupp.induction_linear with
  | h0 => change (0 * _) • _ = 0 • _; change C_smul _ _ = C_smul _ (C_smul _ _); simp
  | hadd f g h1 h2 =>
    change ((⟨f⟩ + ⟨g⟩ : C) * _) • ab = (⟨f⟩ + ⟨g⟩ : C) • _ • _
    simp only [add_mul]
    change C_smul _ _ = C_smul _ (C_smul _ _) at h1 h2 ⊢
    rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, h1, h2]
  | hsingle σ k1 =>
    induction y.val using Finsupp.induction_linear with
    | h0 =>
      change (_ * 0) • _ = _ • 0 • _ ;
      change C_smul _ _ = C_smul _ (C_smul _ _)
      simp
    | hadd f g h1 h2 =>
      change C_smul (⟨.single σ k1⟩ * (_ + _) : C) _ = C_smul _ (C_smul (⟨f⟩ + ⟨g⟩ : C) _)
      change C_smul _ _ = C_smul _ (C_smul _ _) at h1 h2
      rw [mul_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, h1, h2, map_add]
    | hsingle τ k2 =>
      induction ab using Submodule.Quotient.induction_on with | H ab =>
      induction ab using TensorProduct.induction_on with
      | zero =>
        change C_smul _ _ = C_smul _ (C_smul _ _)
        simp
      | tmul a b =>
        change C_smul (⟨mulLinearMap _ (.single σ k1) (.single τ k2)⟩ : C) _ = C_smul _ (C_smul _ _)
        simp only [mulLinearMap_single_single, Pi.mul_apply, Units.val_mul]
        rw [← mul_one (k1 * σ k2 * ((α (σ, τ)).1 * (β (σ, τ)).1)), ← smul_eq_mul _ 1,
          ← Finsupp.smul_single, ← CrossProductAlgebra.smul_mk, mk_single_one, ← mul_one k1,
          ← mul_one k2, ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one,
          ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one, ← C_smul_def,
          ← C_smul_def, ← C_smul_def, C_smul_calc, C_smul_calc, C_smul_calc, Submodule.Quotient.eq]
        simp only [smul_eq_mul, _root_.mul_one]
        rw [← _root_.mul_assoc (basis σ) _ b, CrossProductAlgebra.basis_mul_basis σ τ,
          smul_mul_assoc (β (σ, τ)).1, ← mul_assoc (k1 • basis σ), basis_smul_comm,
          ← mul_smul (σ k2), mul_comm k1, smul_mul_assoc (σ k2 * k1),
          CrossProductAlgebra.basis_mul_basis σ τ, ← mul_smul (σ k2 * k1),
          mul_comm (α (_, _)).1, ← _root_.mul_assoc, mul_comm (σ k2 * k1) (β (_, _)).1,
          _root_.mul_assoc, mul_smul, smul_mul_assoc]
        refine Submodule.subset_span ⟨⟨(β (σ, τ)).1, (σ k2 * k1 * ↑(α (σ, τ))) • basis (σ * τ) * a,
          basis (σ * τ) * b⟩, rfl⟩
      | add x y h1 h2 =>
        simp only [C_smul_def, Submodule.Quotient.mk_add, map_add] at h1 h2 ⊢
        rw [h1, h2]

set_option maxHeartbeats 1200000 in
set_option maxSynthPendingDepth 3 in
instance : MulAction C (M α β) where
  one_smul x := by
    induction x using Quotient.inductionOn' with | h x =>
    change (1 : C) • Submodule.Quotient.mk x = Submodule.Quotient.mk x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      rw [show (1 : C) = ((β 1).1⁻¹ * (α 1).1⁻¹) • CrossProductAlgebra.basis 1 by
        apply val_injective; simp [CrossProductAlgebra.basis], C_smul_calc, mul_smul,
        show basis 1 = (⟨.single 1 1⟩ : CrossProductAlgebra α) from rfl,
        show ((α 1).1)⁻¹ • (⟨.single 1 1⟩ : A) = ⟨(↑(α 1))⁻¹ • .single 1 1⟩ by
          apply val_injective; simp; congr; change _ = (α 1)⁻¹.1 * 1; simp,
        Finsupp.smul_single, show (α 1)⁻¹ • 1 = (α 1).1⁻¹ by change (α 1)⁻¹.1 * 1 = _; simp,
        show (⟨.single 1 (α 1).1⁻¹⟩ : A) = 1 by rfl,
        smul_mul_assoc, _root_.one_mul, Submodule.Quotient.eq]
      refine Submodule.subset_span ⟨⟨(β 1).1⁻¹, a, basis 1 * b⟩, ?_⟩
      simp [← smul_mul_assoc, show ((β 1).1)⁻¹ • basis 1 = (1 : B) by
        apply val_injective; simp [CrossProductAlgebra.basis]]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add]
      conv_rhs => rw [← hx, ← hy]
      change C_smul_aux _ _ =  C_smul_aux _ _ +  C_smul_aux _ _
      simp only [map_add]
    | zero =>
      simp only [Submodule.Quotient.mk_zero]
      change C_smul_aux _ _ = _
      simp only [map_zero]
  mul_smul := C_mul_smul'

instance : DistribMulAction C (M α β) where
  smul_zero c := show C_smul _ _ = 0 by simp
  smul_add c x y := show C_smul _ _ = C_smul _ _ + C_smul _ _ by simp

instance : Module C (M α β) where
  add_smul c c' x :=
    show C_smul _ _ = C_smul _ _ + C_smul _ _ by
      simp only [map_add, LinearMap.add_apply]
  zero_smul x := show C_smul _ _ = _ by simp

instance : SMulWithZero (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  zero_smul ab := show Aox_FB_smul_M 0 _ = 0 by simp

end C_mod

section bimodule

instance : SMulCommClass (A ⊗[F] B)ᵐᵒᵖ C (M α β) where
  smul_comm := by
    rintro ⟨x⟩ c m
    induction m using Quotient.inductionOn' with | h m =>
    change (op x) • c • Submodule.Quotient.mk _ = c • op x • Submodule.Quotient.mk _
    induction x using TensorProduct.induction_on with
    | tmul a' b' =>
      induction m using TensorProduct.induction_on with
      | tmul a b =>
        change _ • (⟨c.val⟩ : C) • _ = (⟨c.val⟩ : C) • _ • Submodule.Quotient.mk _
        induction c.val using Finsupp.induction_linear with
        | h0 => simp
        | hadd f g h1 h2 =>
          rw [← mk_add_mk, add_smul, @smul_add (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _, add_smul, h1, h2]
        | hsingle σ c =>
          rw [← mul_one c, ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one,
            C_smul_calc, Aox_FB_op_tmul_smul_mk_tmul, Aox_FB_op_tmul_smul_mk_tmul, C_smul_calc,
            _root_.mul_assoc, _root_.mul_assoc]
      | zero => simp
      | add x y hx hy =>
        simp [Submodule.Quotient.mk_add, @smul_add (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _,
          @smul_add C (M α β) _ _, hx, hy]
    | add x y hx hy =>
      simp only [op_add, @add_smul (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _, hx, hy, smul_add]
    | zero =>
      simp [op_zero, zero_smul]

end bimodule

section iso

set_option maxHeartbeats 400000 in
instance : IsScalarTower F C (M α β) where
  smul_assoc f c m := by
    -- rw [Algebra.smul_def]
    induction m using Submodule.Quotient.induction_on with | H m =>
    induction m using TensorProduct.induction_on with
    | tmul a b =>
      change (f • (⟨c.val⟩ : C)) • _ = f • (⟨c.val⟩ : C) • _
      induction c.val using Finsupp.induction_linear with
      | h0 => simp
      | hadd _ _ h1 h2 =>
        simp [smul_add, ← mk_add_mk, add_smul, h1, h2, -smul_mk]
      | hsingle σ c =>
        rw [← mul_one c, ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one,
          C_smul_calc, show f • c • basis σ = algebraMap F K f • c • basis σ by
            simp only [Algebra.smul_def]
            rw [smul_eq_incl_mul, ← _root_.mul_assoc, ← smul_mul_assoc, smul_eq_incl_mul]; simp]
        rw [← smul_assoc, C_smul_calc, ← Submodule.Quotient.mk_smul]
        congr 2
        apply val_injective
        simp only [smul_eq_mul, basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply,
          AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, val_mul,
          val_smul, valAddEquiv_symm_apply_val, Finsupp.smul_single, _root_.mul_one]
        induction a.val using Finsupp.induction_linear with
        | h0 => simp
        | hadd f1 g1 h1 h2 => simp [map_add, h1, h2]
        | hsingle a b => simp [_root_.mul_assoc, Algebra.smul_def]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add, smul_add, hx, hy]
    | zero =>
      erw [smul_zero]

instance : Module F (M α β) := inferInstance

set_option maxSynthPendingDepth 3 in
noncomputable def φ0 :
    (A ⊗[F] B)ᵐᵒᵖ →ₐ[F] Module.End C (M α β) where
  toFun x := {
    toFun m := x • m
    map_add' _ _ := by simp [@smul_add (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _]
    map_smul' c y := by
      simp only [RingHom.id_apply]
      rw [smul_comm]
    }
  map_one' := by
    refine LinearMap.ext fun _ ↦ ?_
    simp [@one_smul (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _]
  map_mul' x y := by
    refine LinearMap.ext fun m ↦ ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply]
    exact @mul_smul (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _ x y m
  map_zero' := by
    refine LinearMap.ext fun _ ↦ ?_
    simp only [zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  map_add' x y := by
    refine LinearMap.ext fun _ ↦ ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_smul]
  commutes' f := by
    refine LinearMap.ext fun m ↦ ?_
    simp only [MulOpposite.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, algebraMap_val,
      LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply]
    induction m using Submodule.Quotient.induction_on with | H m =>
    induction m using TensorProduct.induction_on with
    | tmul a b =>
      erw [Aox_FB_op_tmul_smul_mk_tmul]
      rw [_root_.mul_one, ← Algebra.commutes, ← Algebra.smul_def, ← smul_tmul', Submodule.Quotient.mk_smul]
    | add x y hx hy =>
      simp only at hx hy ⊢
      have := congr($hx + $hy)
      rw [← smul_add, ← smul_add] at this
      exact this
    | zero =>
      erw [smul_zero]

set_option synthInstance.maxHeartbeats 40000 in
def MtoAox_KB : M α β →ₗ[F] A ⊗[K] B :=
  Submodule.liftQ _
    (TensorProduct.lift
      { toFun a :=
        { toFun b := a ⊗ₜ b
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

def Aox_KBToM_aux : A ⊗[K] B →+ M α β :=
TensorProduct.liftAddHom
  { toFun a :=
    { toFun b := Submodule.Quotient.mk <| a ⊗ₜ b
      map_zero' := by simp
      map_add' := by simp [tmul_add] }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp [add_tmul] } <| fun k a b => by
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span <| ⟨⟨k, a, b⟩, rfl⟩

set_option synthInstance.maxHeartbeats 80000 in
def Aox_KBToM : A ⊗[K] B →ₗ[F] M α β where
  __ := Aox_KBToM_aux
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
def Aox_KBEquivM : M α β ≃ₗ[F] A ⊗[K] B :=
  LinearEquiv.ofLinear MtoAox_KB Aox_KBToM
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

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma M_F_dim [IsGalois F K] : finrank F (M α β) = (finrank F K)^3 := by
  rw [LinearEquiv.finrank_eq Aox_KBEquivM,
    show finrank F (A ⊗[K] B) = finrank F K * finrank K (A ⊗[K] B) from
      Eq.symm (finrank_mul_finrank F K (A ⊗[K] B)),
    finrank_tensorProduct, finrank_eq_card_basis basis,
    finrank_eq_card_basis basis, IsGalois.card_aut_eq_finrank, pow_three]

instance [IsGalois F K] : FiniteDimensional F C :=
  .of_finrank_eq_succ (n := (finrank F K)^2 - 1) <| by
    rw [CrossProductAlgebra.dim_eq_sq]
    refine Nat.succ_pred_eq_of_pos (pow_two_pos_of_ne_zero ?_) |>.symm
    have : 0 < finrank F K := finrank_pos
    omega

instance [IsGalois F K] : Module.Finite C (M α β) :=
  Module.Finite.right F C (M α β)

omit [DecidableEq (K ≃ₐ[F] K)] in
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
    congr 1
    apply val_injective
    simp only [val_smul, smul_eq_mul, val_mul]
    induction x.val using Finsupp.induction_linear with
    | h0 => simp
    | hadd f g _ _ => simp_all [smul_add]
    | hsingle σ c =>
      simp [Algebra.algebraMap_eq_smul_one, map_one_fst_of_isMulTwoCocycle Fact.out]
      rw [mul_comm _ c, mul_assoc c, ← smul_mul_assoc, ← mul_assoc ((β 1).1⁻¹ * _),
        mul_assoc (β 1).1⁻¹, inv_mul_cancel₀ (by simp), _root_.mul_one]
      field_simp
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

variable (α β) in
def simpleMod : Type := exists_simple_module_directSum (α := α) (β := β) |>.choose

local notation "SM" => simpleMod α β

instance : AddCommGroup SM := exists_simple_module_directSum |>.choose_spec.choose

instance : Module C SM := exists_simple_module_directSum |>.choose_spec.choose_spec.choose

instance : Module F SM := Module.compHom SM (algebraMap F C)

instance : IsSimpleModule C SM :=
  exists_simple_module_directSum |>.choose_spec.choose_spec.choose_spec.choose

variable (α β) in
def indexingSet : Type := exists_simple_module_directSum (α := α) (β := β)
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose

local notation "ι" => indexingSet α β

instance : Fintype ι := exists_simple_module_directSum
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

def isoιSM : C ≃ₗ[C] ι →₀ SM := exists_simple_module_directSum
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

instance : Nonempty ι := by
  by_contra!
  simp only [not_nonempty_iff] at this
  haveI : Subsingleton (ι →₀ SM) := inferInstance
  haveI : Subsingleton C := isoιSM.toEquiv.subsingleton
  haveI : Nontrivial C := inferInstance
  rw [← not_subsingleton_iff_nontrivial] at this
  contradiction

instance : NeZero (Fintype.card ι) := by
  constructor
  simp

def isoιSMPow : C ≃ₗ[C] ι → SM :=
  isoιSM ≪≫ₗ Finsupp.linearEquivFunOnFinite C SM ι

def isoιSMPow' : C ≃ₗ[C] Fin (Fintype.card ι) → SM :=
  isoιSMPow ≪≫ₗ
  { __ := Equiv.arrowCongr (Fintype.equivFinOfCardEq (α := ι) rfl : ι ≃ Fin (Fintype.card ι))
      (Equiv.refl _)
    map_add' := by
      intros v w
      rfl
    map_smul' := by
      intros; rfl }

instance : LinearMap.CompatibleSMul (M α β) (ι →₀ SM) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    congr 1
    simp

instance : IsScalarTower F C SM := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]

instance : Module.Finite C (ι →₀ SM) := .equiv (isoιSM hα hβ)
instance : Module.Finite F (ι →₀ SM) := .trans C (ι →₀ SM)

instance : SMulCommClass C F SM where
  smul_comm c f a := by
    show c • algebraMap F C f • a = algebraMap F C f • _
    rw [← mul_smul, ← Algebra.commutes, mul_smul]

section C_iso

def isoDagger (m : ℕ) [NeZero m] :
    Module.End C (Fin m → SM) ≃ₐ[F] Matrix (Fin m) (Fin m) (Module.End C SM) where
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
  simp [mopEquivEnd, Algebra.algebraMap_eq_smul_one]

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 600000 in
def C_iso_aux : Cᵐᵒᵖ ≃ₐ[F] Module.End C (Fin (Fintype.card ι) → SM) :=
  let iso1 : Module.End C (Fin (Fintype.card ι) → SM) ≃ₐ[F] Module.End C C :=
  { toFun x := (isoιSMPow' (α := α) (β := β)).symm ∘ₗ x ∘ₗ (isoιSMPow' (α := α) (β := β))
    invFun x := (isoιSMPow' (α := α) (β := β)) ∘ₗ x ∘ₗ (isoιSMPow' (α := α) (β := β)).symm
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
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, algebraMap_end_apply,
        val_smul, val_one, Pi.mul_apply, Units.val_mul, mul_inv_rev, Finsupp.smul_single]
      rw [show f • (isoιSMPow' (α := α) (β := β)) 1 = algebraMap F C f • (isoιSMPow') 1 by rfl, map_smul]
      simp [Algebra.algebraMap_eq_smul_one]}
  mopEquivEnd'.trans iso1.symm

example : True := ⟨⟩

def C_iso_aux' : Cᵐᵒᵖ ≃ₐ[F] Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM) :=
  C_iso_aux.trans <| isoDagger _

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma dim_endCSM : (finrank F K)^2 =
  (Fintype.card ι) ^ 2 * finrank F (Module.End C SM) := by
  have eq1 := (C_iso_aux' (α := α) (β := β)).toLinearEquiv.finrank_eq
  rw [show finrank F Cᵐᵒᵖ = finrank F C by
    refine LinearEquiv.finrank_eq
      { toFun := unop
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        invFun := op
        left_inv := unop_op
        right_inv _ := rfl }, CrossProductAlgebra.dim_eq_sq] at eq1
  rw [eq1, matrixEquivTensor (Fin (Fintype.card ι)) F (Module.End C SM)  |>.toLinearEquiv.finrank_eq,
    finrank_tensorProduct, finrank_matrix]
  simp only [Fintype.card_fin, finrank_self, _root_.mul_one, pow_two]
  group

set_option maxHeartbeats 1200000 in
def C_iso_aux'' : C ≃ₐ[F] (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM))ᵐᵒᵖ where
  toFun c := op <| C_iso_aux' (op c)
  invFun m := (C_iso_aux'.symm m.unop).unop
  left_inv := by
    intro c
    simp only [unop_op, AlgEquiv.symm_apply_apply]
  right_inv := by
    intro m
    simp only [op_unop, AlgEquiv.apply_symm_apply]
  map_mul' := by
    intro c c'
    simp [op_mul, map_mul]
  map_add' := by
    intro c c'
    simp [op_add, map_add]
  commutes' := by
    intro f
    simp [MulOpposite.algebraMap_apply, op_inj, Algebra.algebraMap_eq_smul_one]

def C_iso : C ≃ₐ[F] (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM)ᵐᵒᵖ) :=
  C_iso_aux''.trans ((matrixEquivMatrixMop_algebra F _ _).symm)

end C_iso

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma M_directSum : ∃ (ιM : Type) (_ : Fintype ιM), Nonempty (M α β ≃ₗ[C] ιM →₀ SM) := by
  obtain ⟨ιM, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring' F C (M α β) SM
  refine ⟨ιM, ?_, ⟨iso⟩⟩

  haveI : LinearMap.CompatibleSMul C (ιM →₀ SM) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    congr 1
    apply val_injective
    simp [Algebra.algebraMap_eq_smul_one]

  let iso' : M α β ≃ₗ[F] (ιM →₀ SM) := iso.restrictScalars F
  haveI : IsScalarTower F C (ιM →₀ SM) := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]
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

variable (α β) in
def indexingSetM : Type := (M_directSum (α := α) (β := β)).choose

local notation "ιM" => indexingSetM α β

instance : Fintype ιM := M_directSum.choose_spec.choose

def M_iso_directSum : M α β ≃ₗ[C] ιM →₀ SM := M_directSum.choose_spec.choose_spec.some

instance : Module.Finite C SM := by
  rw [Module.finite_def, Submodule.fg_def]
  obtain ⟨a, ha⟩ := IsSimpleModule.instIsPrincipal C (M := SM) ⊤
  exact ⟨{a}, Set.finite_singleton a, ha.symm⟩

instance : Module.Finite F SM := Module.Finite.trans C SM

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma SM_F_dim : Fintype.card ι * finrank F SM = finrank F K ^ 2 := by
  have eq1 := LinearEquiv.finrank_eq (isoιSMPow' hα hβ |>.restrictScalars F)
  rw [CrossProductAlgebra.dim_eq_sq] at eq1
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

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma M_iso_powAux : Nonempty (M α β ≃ₗ[C] Fin (finrank F K * Fintype.card ι) → SM) := by
  rw [linearEquiv_iff_finrank_eq_over_simple_ring F C]
  have eq2 := rank_fun (η := (Fin (finrank F K * Fintype.card ι))) (M := SM) (R := F)
  rw [Fintype.card_fin, ← finrank_eq_rank F SM,
    show ((finrank F K * Fintype.card ι : ℕ) : Cardinal) * (finrank F SM : Cardinal) =
      ((finrank F K * Fintype.card ι * finrank F SM : ℕ) : Cardinal) by simp] at eq2

  have := finrank_eq_of_rank_eq eq2
  rw [this, M_F_dim, _root_.mul_assoc, SM_F_dim, pow_three, pow_two]

variable (α β) in
def M_iso_pow : M α β ≃ₗ[C] Fin (finrank F K * Fintype.card ι) → SM := M_iso_powAux.some

def M_iso_pow' : M α β ≃ₗ[F] Fin (finrank F K * Fintype.card ι) → SM :=
  M_iso_pow α β|>.restrictScalars F

-- set_option maxHeartbeats 600000 in
def endCMIso :
    Module.End C (M α β) ≃ₐ[F] Module.End C (Fin (finrank F K * Fintype.card ι) → SM) where
  toFun x := (M_iso_pow α β) ∘ₗ x ∘ₗ (M_iso_pow α β).symm
  invFun x := (M_iso_pow α β).symm ∘ₗ x ∘ₗ (M_iso_pow α β)
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
  map_mul' x y := by
    refine DFunLike.ext _ _ fun z ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.mul_apply,
      LinearEquiv.symm_apply_apply]
  map_add' x y := by
    refine DFunLike.ext _ _ fun z ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.add_apply,
      map_add]
  commutes' := by
    intro f
    refine DFunLike.ext _ _ fun z ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.algebraMap_end_apply]
    change  (M_iso_pow') (f • (M_iso_pow').symm z) = f • z
    rw [map_smul]
    simp only [algebraMap_val, LinearEquiv.apply_symm_apply, smul_assoc, one_smul]

example : True := ⟨⟩

instance : NeZero (finrank F K * Fintype.card ι) := by
  constructor
  simp only [ne_eq, mul_eq_zero, Fintype.card_ne_zero, or_false]
  have : 0 < finrank F K := finrank_pos
  omega

def endCMIso' :
    Module.End C (M α β) ≃ₐ[F]
    Matrix (Fin (finrank F K * Fintype.card ι))
      (Fin (finrank F K * Fintype.card ι)) (Module.End C SM) :=
  endCMIso.trans <| isoDagger _

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma dim_endCM :
    finrank F (Module.End C (M α β)) = (finrank F K)^4 := by
  have := LinearEquiv.finrank_eq (endCMIso' (α := α) (β := β)).toLinearEquiv
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

-- set_option maxHeartbeats 600000 in
set_option maxSynthPendingDepth 3 in
def φ1 :
    (A ⊗[F] B)ᵐᵒᵖ ≃ₐ[F] Module.End C (M α β) :=
  AlgEquiv.ofBijective (φ0 (α := α) (β := β)) <|
  bijective_of_dim_eq_of_isCentralSimple F (A ⊗[F] B)ᵐᵒᵖ (Module.End C (M α β)) φ0 <| by
    rw [dim_endCM, show finrank F (A ⊗[F] B)ᵐᵒᵖ = finrank F (A ⊗[F] B) by
      refine LinearEquiv.finrank_eq
        { toFun := unop
          map_add' _ _ := rfl
          map_smul' _ _ := rfl
          invFun := op
          left_inv := unop_op
          right_inv _ := rfl }, finrank_tensorProduct, CrossProductAlgebra.dim_eq_sq,
      CrossProductAlgebra.dim_eq_sq, pow_two, pow_succ]
    group)

def φ2 :
    (A ⊗[F] B) ≃ₐ[F] (Module.End C (M α β))ᵐᵒᵖ where
  toFun a := op <| φ1 (op a)
  invFun g := (φ1.symm g.unop).unop
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  map_mul' := by intros; simp
  map_add' := by intros; simp
  commutes' := fun f ↦ by
    simp only [Algebra.TensorProduct.algebraMap_apply, MulOpposite.algebraMap_apply, op_inj]
    rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul', op_smul, ← (φ0 (α := α) (β := β)).commutes f,
      Algebra.algebraMap_eq_smul_one]
    rfl

def φ3 :
    (A ⊗[F] B) ≃ₐ[F]
    (Matrix (Fin (finrank F K * Fintype.card ι)) (Fin (finrank F K * Fintype.card ι))
      (Module.End C SM))ᵐᵒᵖ := φ2.trans endCMIso'.op

def φ4 :
    (A ⊗[F] B) ≃ₐ[F]
    (Matrix (Fin (finrank F K * Fintype.card ι)) (Fin (finrank F K * Fintype.card ι))
      (Module.End C SM)ᵐᵒᵖ) :=
  φ3.trans ((matrixEquivMatrixMop_algebra F _ _).symm)

instance [DecidableEq (Module.End C SM)] : DivisionRing ((Module.End C SM)ᵐᵒᵖ) := by
  letI : DivisionRing (Module.End C SM) := Module.End.divisionRing
  infer_instance

omit [DecidableEq (K ≃ₐ[F] K)] in
lemma isBrauerEquivalent : IsBrauerEquivalent (⟨.of F (A ⊗[F] B)⟩ : CSA F) ⟨.of F C⟩ := by
  let iso1 := C_iso (α := α) (β := β) |>.mapMatrix (m := Fin (finrank F K))
  let iso11 := iso1.trans (Matrix.compAlgEquiv _ _ _ _) |>.trans
    (Matrix.reindexAlgEquiv _ _ finProdFinEquiv)
  let iso2 := φ4 (α := α) (β := β)
  let iso3 := iso11.trans iso2.symm
  haveI : NeZero (finrank F K) := ⟨by have : 0 < finrank F K := finrank_pos; omega⟩
  exact ⟨1, finrank F K, one_ne_zero, (NeZero.ne' (finrank F K)).symm,
    ⟨(dim_one_iso (⟨.of F (A ⊗[F] B)⟩ : CSA F)).trans iso3.symm⟩⟩

end iso

end map_mul

end map_mul_proof

namespace RelativeBrGroup

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq Gal(K, F)]

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

def isoSnd :
    Additive (RelativeBrGroup K F) ≃+ H2 (galAct F K) :=
  AddEquiv.symm <|
  AddEquiv.mk' (equivSnd (F := F) (K := K)).symm <| by
    intro x y
    induction x using Quotient.inductionOn' with | h x =>
    induction y using Quotient.inductionOn' with | h y =>
    simp only [Function.comp_apply]
    rcases x with ⟨x, hx'⟩
    have hx := isMulTwoCocycle_of_mem_twoCocycles _ hx'
    rcases y with ⟨y, hy'⟩
    have hy := isMulTwoCocycle_of_mem_twoCocycles _ hy'
    change fromSnd F K (Quotient.mk'' _) =
      fromSnd F K (Quotient.mk'' _) * fromSnd F K (Quotient.mk'' _)
    erw [fromSnd_wd, fromSnd_wd]
    erw [fromSnd_wd]
    apply_fun Additive.toMul
    simp only [AddMemClass.mk_add_mk, twoCocycles.val_eq_coe, MulMemClass.mk_mul_mk,
      EmbeddingLike.apply_eq_iff_eq]
    refine Subtype.ext ?_
    change _ = Quotient.mk'' _
    rw [Quotient.eq'']
    change IsBrauerEquivalent _ _
    exact @map_mul_proof.isBrauerEquivalent _ _ _ _ _ _ _ ⟨hx⟩ ⟨hy⟩ _ _ |>.symm

#print axioms isoSnd

end RelativeBrGroup
