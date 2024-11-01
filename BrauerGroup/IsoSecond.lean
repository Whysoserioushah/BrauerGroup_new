import BrauerGroup.ToSecond

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

open scoped TensorProduct

namespace map_one_proof
section map_one

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

def φ0 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₗ[K]
    Module.End F K :=
  (CrossProduct.x_AsBasis (F := F) (K := K) (a := 1) (isMulTwoCocycle_of_twoCocycles 0)).constr F
    fun σ => σ.toLinearMap

def φ1 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₗ[F]
    Module.End F K :=
  φ0 K F |>.restrictScalars F

def φ2 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) →ₐ[F]
    Module.End F K :=
  AlgHom.ofLinearMap (φ1 K F)
    (by
      generalize_proofs h
      rw [show (1 : CrossProduct h) = .x_AsBasis h 1 by
        ext1
        simp]
      delta φ1 φ0
      rw [LinearMap.restrictScalars_apply, Basis.constr_basis]
      rfl)
    (by
      rintro x y
      change φ0 K F _ = φ0 K F _ * φ0 K F _
      generalize_proofs h
      induction x using CrossProduct.single_induction h with
      | single x c =>
        rw [show (⟨Pi.single x c⟩ : CrossProduct h) =
          c • .x_AsBasis h x by
          ext : 1
          simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
            CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
            crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
        rw [map_smul]
        induction y using CrossProduct.single_induction h with
        | single y d =>
          rw [show (⟨Pi.single y d⟩ : CrossProduct h) =
            d • .x_AsBasis h y by
            ext : 1
            simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
              CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
              crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply]]
          rw [show (c • CrossProduct.x_AsBasis h x) * (d • .x_AsBasis h y) =
            (c * x d) • .x_AsBasis h (x * y) by
            ext : 1
            simp only [CrossProduct.x_AsBasis_apply, CrossProduct.smul_def, CrossProduct.mul_val,
              CrossProduct.ι_apply_val, Pi.one_apply, inv_one, Units.val_one, _root_.mul_one,
              crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply, map_mul]]
          rw [map_smul, map_smul]
          delta φ0
          rw [Basis.constr_basis, Basis.constr_basis, Basis.constr_basis]
          ext α
          simp only [LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.mul_apply,
            smul_eq_mul, _root_.mul_assoc, LinearMap.mul_apply, map_mul]
        | add y y' hy hy' =>
          erw [mul_add]
          rw [map_add, hy, hy']
          erw [map_add]
          rw [mul_add]
        | zero =>
          erw [mul_zero]
          rw [map_zero]
          erw [map_zero]
          rw [mul_zero]
      | add x x' hx hx' =>
        erw [add_mul]
        rw [map_add, hx, hx']
        erw [map_add]
        rw [add_mul]
      | zero =>
        erw [zero_mul]
        rw [map_zero]
        erw [map_zero]
        rw [zero_mul])

def φ3 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
    Module.End F K :=
  AlgEquiv.ofBijective (φ2 K F) (bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by
    rw [CrossProduct.dim_eq_square]
    rw [finrank_linearMap, pow_two])

def φ4 :
    CrossProduct (F := F) (K := K) (a := 1) (ha := isMulTwoCocycle_of_twoCocycles 0) ≃ₐ[F]
    Matrix (Fin <| finrank F K) (Fin <| finrank F K) F :=
  φ3 K F |>.trans <| LinearMap.toMatrixAlgEquiv <| finBasis F K

lemma map_one' : RelativeBrGroup.fromTwoCocycles (F := F) (K := K) (a := 0) = 1 := by
  ext1
  change Quotient.mk'' _ = Quotient.mk'' _
  erw [Quotient.eq'']
  have : 0 < finrank F K := finrank_pos
  change IsBrauerEquivalent _ _
  refine ⟨1, finrank F K, by positivity, by positivity, AlgEquiv.trans ?_ <| φ4 K F⟩
  exact dim_one_iso (CSA.mk (CrossProduct.asCSA _).carrier).carrier

lemma fromSnd_zero : RelativeBrGroup.fromSnd (F := F) (K := K) 0 = 1 := map_one' K F

end map_one

end map_one_proof

namespace map_mul_proof
section map_mul

variable (α β : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ)
variable (hα : IsMulTwoCocycle α) (hβ : IsMulTwoCocycle β)

variable {K F α β}

include hα hβ in
lemma hαβ : IsMulTwoCocycle (α * β) := isMulTwoCocycle_of_twoCocycles <|
  (twoCocyclesOfIsMulTwoCocycle hα) + (twoCocyclesOfIsMulTwoCocycle hβ)

local notation "A" => CrossProduct hα
local notation "B" => CrossProduct hβ
local notation "C" => CrossProduct (hαβ hα hβ)

open CrossProduct TensorProduct

variable [FiniteDimensional F K]  [DecidableEq (K ≃ₐ[F] K)]


abbrev S : Set (A ⊗[F] B) :=
  Set.range (fun (cba : K × A × B) =>
    (cba.1 • cba.2.1) ⊗ₜ[F] cba.2.2 - cba.2.1 ⊗ₜ[F] (cba.1 • cba.2.2))

@[simp]
lemma mem_S (x : A ⊗[F] B) : x ∈ S hα hβ ↔
    ∃ (k : K) (a : A) (b : B), x = (k • a) ⊗ₜ b - a ⊗ₜ (k • b) := by
  simp only [S, Set.mem_range, Prod.exists]
  aesop

abbrev M := (A ⊗[F] B) ⧸ Submodule.span F (S hα hβ)

open MulOpposite

-- def SAsIdeal : Ideal (A ⊗[F] B)ᵐᵒᵖ where
--   carrier := op '' Submodule.span F (S hα hβ)
--   add_mem' := by
--     rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
--     refine ⟨x + y, Submodule.add_mem _ hx hy, rfl⟩
--   zero_mem' := by
--     refine ⟨0, Submodule.zero_mem _, rfl⟩
--   smul_mem' := by
--     rintro ⟨x⟩ _ ⟨y, hy, rfl⟩
--     refine ⟨y • x, Submodule.span_induction hy ?_ ?_ ?_ ?_, unop_injective rfl⟩
--     · rintro _ ⟨⟨k, a, b⟩, rfl⟩
--       simp only [smul_eq_mul, SetLike.mem_coe]
--       induction x using TensorProduct.induction_on
--       sorry

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

def Aox_FB_smul_M_aux (a' : A) (b' : B) : M hα hβ →ₗ[F] M hα hβ :=
  Submodule.mapQ (Submodule.span F (S hα hβ)) (Submodule.span F (S hα hβ))
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

def Aox_FB_smul_M : A ⊗[F] B →ₗ[F] M hα hβ →ₗ[F] M hα hβ :=
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
    Aox_FB_smul_M hα hβ (a' ⊗ₜ[F] b') (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M hα hβ) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl


instance : SMul (A ⊗[F] B)ᵐᵒᵖ (M hα hβ) where
  smul x y := Aox_FB_smul_M _ _ x.unop y

@[simp]
lemma Aox_FB_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    op (a' ⊗ₜ[F] b') • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M hα hβ) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl

instance : MulAction (A ⊗[F] B)ᵐᵒᵖ (M hα hβ) where
  one_smul := by
    intro x
    rw [show (1 : (A ⊗[F] B)ᵐᵒᵖ) = op 1 from rfl,
      Algebra.TensorProduct.one_def]
    change Aox_FB_smul_M hα hβ (1 ⊗ₜ[F] 1) x = LinearMap.id (R := F) x
    refine LinearMap.ext_iff |>.1 ?_ x
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Aox_FB_smul_M_op_tmul_smul_mk_tmul, _root_.mul_one, LinearMap.id_comp]
  mul_smul := by
    rintro ⟨x⟩ ⟨y⟩ b
    change Aox_FB_smul_M hα hβ (y * x) _ = Aox_FB_smul_M hα hβ x (Aox_FB_smul_M hα hβ y b)
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

instance : DistribMulAction (A ⊗[F] B)ᵐᵒᵖ (M hα hβ) where
  smul_zero := by
    intro x
    change Aox_FB_smul_M hα hβ _ _ = _
    simp
  smul_add := by
    intro x a b
    change Aox_FB_smul_M hα hβ _ _ = Aox_FB_smul_M hα hβ _ _ + Aox_FB_smul_M hα hβ _ _
    simp

instance : Module (A ⊗[F] B)ᵐᵒᵖ (M hα hβ) where
  add_smul := by
    intro x y a
    change Aox_FB_smul_M hα hβ _ _ = Aox_FB_smul_M hα hβ _ _ + Aox_FB_smul_M hα hβ _ _
    simp
  zero_smul := by
    intro x
    change Aox_FB_smul_M hα hβ _ _ = _
    simp

end Aox_FB_mod

section C_mod

def F_smul_mul_compatible (f : F) (a a' : A) :
    (f • a) * a' = a * (f • a') := by
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

def C_smul_aux (c : C) : M hα hβ →ₗ[F] M hα hβ :=
  Submodule.mapQ (Submodule.span F (S hα hβ)) (Submodule.span F (S hα hβ))
    (TensorProduct.lift
      { toFun := fun a =>
        { toFun := fun b =>
            ∑ σ : K ≃ₐ[F] K, ((c.1 σ • x_AsBasis hα σ) * a) ⊗ₜ (x_AsBasis hβ σ * b)
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
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [show c.val σ • (x_AsBasis hα) σ * k • a = (c.val σ • (x_AsBasis hα) σ * ι hα k) * a by
      conv_lhs => rw [CrossProduct.smul_def hα k a]
      simp only [_root_.mul_assoc],
      show (c.val σ • (x_AsBasis hα) σ * ι hα k) * a = ((c.val σ * σ k) • x_AsBasis hα σ * a) by
      rw [smul_mul_assoc, x__conj'' hα, mul_smul],
      mul_comm (c.val σ), smul_mul_assoc, mul_smul,
      show (x_AsBasis hβ) σ * k • b = σ k • ((x_AsBasis hβ) σ * b) by
      rw [← smul_mul_assoc (σ k) (x_AsBasis hβ σ) b, ← x__conj'' hβ, _root_.mul_assoc]
      rfl]
    refine Submodule.subset_span ⟨⟨σ k, c.1 σ • (x_AsBasis hα σ * a), x_AsBasis hβ σ * b⟩, ?_⟩
    simp only [smul_mul_assoc])


lemma C_smul_aux_calc (k : K) (σ : K ≃ₐ[F] K) (a : A) (b : B) :
    C_smul_aux _ _ (k • x_AsBasis (hαβ hα hβ) σ) (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M hα hβ) =
    Submodule.Quotient.mk (((k • x_AsBasis hα σ) * a) ⊗ₜ (x_AsBasis hβ σ * b)) := by
  delta C_smul_aux
  rw [Submodule.mapQ_apply, lift.tmul]
  congr 1
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem σ (Finset.mem_univ _)]
  swap
  · rintro τ - h
    erw [show (k • (x_AsBasis (hαβ hα hβ)) σ).val τ = 0 by
      simp only [x_AsBasis_apply, CrossProduct.smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
        Pi.mul_apply, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val,
        crossProductMul_single_single, AlgEquiv.one_apply, _root_.mul_one]
      rw [_root_.one_mul, Pi.single_apply, if_neg h], zero_smul, zero_mul, zero_tmul]
  congr 2
  simp only [x_AsBasis_apply, CrossProduct.smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
    Pi.mul_apply, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val,
    crossProductMul_single_single, AlgEquiv.one_apply, _root_.mul_one]
  rw [_root_.one_mul, Pi.single_eq_same, a_one_left hα, a_one_left hβ]
  congr 2
  field_simp
  left
  rw [mul_comm]


set_option maxHeartbeats 400000 in
def C_smul : C →ₗ[F] M hα hβ →ₗ[F] M hα hβ where
  toFun c := C_smul_aux hα hβ c
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


instance : SMul C (M hα hβ) where
  smul c x := C_smul hα hβ c x

lemma C_smul_calc (k : K) (σ : K ≃ₐ[F] K) (a : A) (b : B) :
    (k • x_AsBasis (hαβ hα hβ) σ) • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M hα hβ) =
    Submodule.Quotient.mk (((k • x_AsBasis hα σ) * a) ⊗ₜ (x_AsBasis hβ σ * b)) :=
  C_smul_aux_calc hα hβ k σ a b

instance : MulAction C (M hα hβ) where
  one_smul := by
    intro x
    induction x using Quotient.inductionOn' with | h x =>
    change (1 : C) • Submodule.Quotient.mk x = Submodule.Quotient.mk x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      rw [show (1 : C) = ((β 1).1⁻¹ * (α 1).1⁻¹) • x_AsBasis (hαβ hα hβ) 1 by
        simp only [CrossProduct.one_def, Pi.mul_apply, Units.val_mul, mul_inv_rev, x_AsBasis_apply,
          mul_smul], C_smul_calc, mul_smul, ← CrossProduct.one_def, smul_mul_assoc, _root_.one_mul]
      trans (Submodule.Quotient.mk (a ⊗ₜ[F] ((β 1).1⁻¹ • x_AsBasis hβ 1 * b)) : M hα hβ)
      · rw [Submodule.Quotient.eq]
        refine Submodule.subset_span ⟨⟨(β 1).1⁻¹, a, x_AsBasis hβ 1 * b⟩, ?_⟩
        simp only [sub_right_inj, smul_mul_assoc]
      rw [← CrossProduct.one_def, _root_.one_mul]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add]
      conv_rhs => rw [← hx, ← hy]
      change C_smul_aux hα hβ _ _ =  C_smul_aux hα hβ _ _ +  C_smul_aux hα hβ _ _
      simp only [map_add]
    | zero =>
      simp only [Submodule.Quotient.mk_zero]
      change C_smul_aux hα hβ _ _ = _
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
            smul_mul_assoc, x_AsBasis_mul, Pi.mul_apply, mul_comm _ (β _),
            Units.val_mul, ← mul_smul, ← mul_smul, C_smul_calc, ← CrossProduct.smul_def,
            C_smul_calc, C_smul_calc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
            CrossProduct.smul_def _ y, ← _root_.mul_assoc _ (ι hα y), x__conj'',
            smul_mul_assoc, ← _root_.mul_assoc _ _ a, x_AsBasis_mul, ← _root_.mul_assoc _ _ b,
            x_AsBasis_mul, Submodule.Quotient.eq, ← mul_smul]
          refine Submodule.subset_span ⟨⟨β (σ, τ), (x * σ y * α (σ, τ)) •
            ((x_AsBasis hα) (σ * τ) * a), (x_AsBasis hβ) (σ * τ) * b⟩, ?_⟩
          dsimp only
          rw [← smul_assoc, smul_mul_assoc, ← smul_assoc, smul_mul_assoc]
          congr 3
          simp only [smul_eq_mul]
          ring
        | add z z' hz hz' =>
          change C_smul_aux hα hβ _ _ = C_smul_aux hα hβ _ _ at hz hz' ⊢
          simp only [QuotientAddGroup.mk_add, map_add] at hz hz' ⊢
          rw [hz, hz']
          change _ = C_smul_aux hα hβ _ (C_smul_aux hα hβ _ _)
          simp only [map_add]
          rfl
        | zero =>
          change C_smul_aux hα hβ _ _ = C_smul_aux hα hβ _ (C_smul_aux hα hβ _ _)
          simp only [QuotientAddGroup.mk_zero, map_zero]
      | add y y' hy hy' =>
        change C_smul hα hβ _ _ = C_smul hα hβ _ _ at hy hy' ⊢
        change _ = C_smul hα hβ _ (C_smul hα hβ _ _)
        erw [mul_add, map_add, map_add, map_add]
        simp only [LinearMap.add_apply, hy, hy']
        rfl
      | zero =>
        erw [mul_zero]
        change C_smul hα hβ _ _ = C_smul hα hβ _ (C_smul hα hβ _ _)
        simp only [map_zero, LinearMap.zero_apply]
        erw [map_zero, map_zero]
    | add x x' hx hx' =>
      erw [add_mul]
      change C_smul hα hβ _ _ = C_smul hα hβ _ _ at hx hx' ⊢
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hx']
      erw [map_add]
      rfl
    | zero =>
      erw [zero_mul]
      change C_smul hα hβ _ _ = C_smul hα hβ 0 (C_smul hα hβ _ _)
      simp only [map_zero, LinearMap.zero_apply]

example : True := ⟨⟩

instance : DistribMulAction C (M hα hβ) where
  smul_zero := by
    intro c
    change C_smul hα hβ _ _ = 0
    simp
  smul_add := by
    intro c x y
    change C_smul hα hβ _ _ = C_smul hα hβ _ _ + C_smul hα hβ _ _
    simp

instance : Module C (M hα hβ) where
  add_smul := by
    intro c c' x
    change C_smul hα hβ _ _ = C_smul hα hβ _ _ + C_smul hα hβ _ _
    simp only [map_add, LinearMap.add_apply]
  zero_smul := by
    intro x
    change C_smul hα hβ _ _ = _
    simp

end C_mod

section bimodule

instance : SMulCommClass (A ⊗[F] B)ᵐᵒᵖ C (M hα hβ) where
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
instance : IsScalarTower F C (M hα hβ) where
  smul_assoc f c m := by
    -- rw [Algebra.smul_def]
    induction m using Quotient.inductionOn' with | h m =>
    change _ • Submodule.Quotient.mk _ = _ • _ • Submodule.Quotient.mk _
    induction m using TensorProduct.induction_on with
    | tmul a b =>
      induction c using single_induction with
      | single σ c =>
        rw [single_in_xAsBasis, C_smul_calc]
        rw [show f • c • (x_AsBasis (hαβ hα hβ)) σ = algebraMap F K f • c • (x_AsBasis (hαβ hα hβ)) σ by
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

-- instance : Algebra F (Module.End C (M hα hβ)) := Module.End.instAlgebra _ _ _

-- set_option maxHeartbeats 400000 in
noncomputable def φ0 :
    (A ⊗[F] B)ᵐᵒᵖ →ₐ[F] Module.End C (M hα hβ) where
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
      simp only [QuotientAddGroup.mk_add, smul_add] at hx hy ⊢
      erw [hx, hy]
    | zero =>
      erw [smul_zero]

example : True := ⟨⟩

set_option synthInstance.maxHeartbeats 40000 in
def MtoAox_KB : M hα hβ →ₗ[F] A ⊗[K] B :=
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

end iso

end map_mul

end map_mul_proof

#exit

instance : Module (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ
  (CrossProduct ha ⊗[F] CrossProduct hb) := inferInstance

set_option synthInstance.maxHeartbeats 40000 in
instance : Module (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ
    (Submodule.span (CrossProduct ha ⊗[F] CrossProduct hb) (S K F a b ha hb)) :=
  -- inferInstance
  sorry

instance : IsScalarTower (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ (CrossProduct ha ⊗[F] CrossProduct hb)
    (CrossProduct ha ⊗[F] CrossProduct hb) where
  smul_assoc xop x y := by
    simp only [MulOpposite.smul_eq_mul_unop, smul_eq_mul]
    sorry

instance : Module (CrossProduct ha ⊗[F] CrossProduct hb)ᵐᵒᵖ (M K F a b ha hb) :=
  Submodule.Quotient.module' _

local notation "u" => x_AsBasis ha

local notation "v" => x_AsBasis hb

local notation "w" => x_AsBasis (mulab K F a b ha hb)

-- abbrev smulTensor (σ : (K ≃ₐ[F] K)) (k : K) : (CrossProduct ha) ⊗[F] (CrossProduct hb)
--     →ₗ[F] (CrossProduct ha) ⊗[F] (CrossProduct hb) := TensorProduct.lift {
--   toFun := fun a ↦ {
--     toFun := fun b ↦ (k • u σ * a) ⊗ₜ (v σ * b)
--     map_add' := fun x y ↦ by simp only [x_AsBasis_apply, mul_add, tmul_add]
--     map_smul' := fun α x ↦ by
--       simp only [RingHom.id_apply, smul_tmul', smul_tmul]
--       congr 1
--       exact mul_smul_comm α (v σ) x }
--   map_add' := fun a1 a2 ↦ by
--     ext b
--     simp only [x_AsBasis_apply, mul_add, add_tmul, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.add_apply]
--   map_smul' := fun α a ↦ by
--     ext b
--     simp only [x_AsBasis_apply, Algebra.mul_smul_comm, LinearMap.coe_mk,
--       AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
--     congr 1  }
-- #check Basis.constr

abbrev smulsmul (aa : CrossProduct ha) (bb : CrossProduct hb) :
    CrossProduct (mulab K F a b ha hb) →ₗ[K]
    (CrossProduct ha) ⊗[F] (CrossProduct hb) :=
  Basis.constr (ι := (K ≃ₐ[F] K)) (S := F) (R := K) w $ fun σ =>
    (u σ * aa) ⊗ₜ (v σ * bb)

abbrev smulLinear : (CrossProduct ha) ⊗[F] (CrossProduct hb) →ₗ[F]
    CrossProduct (mulab K F a b ha hb) →ₗ[K]
    (CrossProduct ha) ⊗[F] (CrossProduct hb) := TensorProduct.lift {
    toFun := fun aa ↦ {
      toFun := fun bb ↦ smulsmul K F a b ha hb aa bb
      map_add' := fun b1 b2 ↦ by
        simp only
        ext aabb
        simp only [Basis.constr_apply_fintype, Basis.equivFun_apply,
          x_AsBasis_apply, mul_add, tmul_add, smul_add,
          Finset.sum_add_distrib, LinearMap.add_apply]
      map_smul' := fun α bb ↦ by
        ext aabb
        simp only [Basis.constr_apply_fintype, Basis.equivFun_apply, x_AsBasis_apply,
          Algebra.mul_smul_comm, tmul_smul, RingHom.id_apply,
          LinearMap.smul_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ smul_comm _ _ _ }
    map_add' := fun a1 a2 ↦ by
      ext bb x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Basis.constr_apply_fintype, Basis.equivFun_apply,
        LinearMap.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ by
        simp only [x_AsBasis_apply, mul_add, add_tmul, smul_add]
    map_smul' := fun α aa ↦ by
      ext bb x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Basis.constr_apply_fintype, Basis.equivFun_apply,
        Algebra.mul_smul_comm, RingHom.id_apply, LinearMap.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ by
        rw [smul_tmul', smul_tmul', smul_tmul', smul_comm]
  }

instance : IsScalarTower K (CrossProduct ha) (CrossProduct ha) where
  smul_assoc k a1 a2 := by
    change (ι ha k * a1) • _ = ι ha k * _
    rw [smul_eq_mul, smul_eq_mul, _root_.mul_assoc]

instance : CompatibleSMul F K (CrossProduct ha) (CrossProduct hb) where
  smul_tmul k aa bb := by
    -- change (CrossProduct.ι ha k * aa) ⊗ₜ _ = _ ⊗ₜ (CrossProduct.ι hb k * bb)
    induction aa using single_induction ha with
    | zero => simp only [show ⟨0⟩ = (0 : CrossProduct ha) from rfl, smul_zero, zero_tmul]
    | single σ k1 =>
      simp only [smul_single]
      induction bb using single_induction hb with
      | zero => simp only [show ⟨0⟩ = (0 : CrossProduct hb) from rfl, tmul_zero, smul_zero]
      | single σ' k2 =>
        simp only [smul_single]

        sorry
      | add _ _ h11 h22 =>
        sorry
    | add _ _ h1 h2 => sorry

instance : Module (CrossProduct (mulab K F a b ha hb))
    (CrossProduct ha ⊗[F] CrossProduct hb) where
  smul x ab := smulLinear K F a b ha hb ab x
  one_smul ab := by
    change smulLinear _ _ _ _ _ _ _ ⟨_⟩ = _
    rw [single_in_xAsBasis, map_smul]
    induction ab using TensorProduct.induction_on with
    | zero => simp only [Prod.mk_one_one, Pi.mul_apply, Units.val_mul, mul_inv_rev, map_zero,
        x_AsBasis_apply, LinearMap.zero_apply, smul_zero]
    | tmul aa bb =>
        simp only [lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, smulsmul,
          Basis.constr_basis]
        change ((((a (1, 1)) * (b (1, 1))) : Kˣ).1)⁻¹ • _ = _
        rw [Units.val_mul, _root_.mul_inv, ← one_smul K (u 1),
          ← single_in_xAsBasis ha 1 1, ← one_smul K (v 1),
          ← single_in_xAsBasis hb 1 1, mul_comm, mul_smul, smul_tmul', ← smul_mul_assoc,
          smul_single, _root_.mul_one, show ⟨Pi.single _ _⟩ = (1 : CrossProduct ha) from rfl,
          _root_.one_mul, ← tmul_smul, ← smul_mul_assoc, smul_single, _root_.mul_one,
          show ⟨Pi.single _ _⟩ = (1 : CrossProduct hb) from rfl, _root_.one_mul]
    | add _ _ h1 h2 => rw [map_add, LinearMap.add_apply, smul_add, h1, h2]
  mul_smul aabb1 aabb2 ab := by
    change smulLinear _ _ _ _ _ _ _ _ = smulLinear _ _ _ _ _ _ (smulLinear _ _ _ _ _ _ _ _) _
    induction aabb1 using single_induction with
    | zero => sorry
    | single σ k =>
    induction aabb2 using single_induction with
      | zero => sorry
      | single σ' k' =>
        simp only [mul_single_in_xAsBasis, Pi.mul_apply, Units.val_mul, x_AsBasis_apply, map_smul]
        induction ab using TensorProduct.induction_on with
        | zero => sorry
        | tmul aa bb =>
          simp only [lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, smulsmul, single_in_xAsBasis,
            one_smul, Basis.constr_basis, map_smul, smul_tmul']
          sorry
        | add _ _ h11 h12 => sorry
      | add _ _ h1' h2' => sorry
    | add _ _ h1 h2 => sorry

  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

example (a b : K) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by exact _root_.mul_inv a b
instance : Module (CrossProduct (mulab K F a b ha hb)) (M K F a b ha hb) := sorry

end map_mul
