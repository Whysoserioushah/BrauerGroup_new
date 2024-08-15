import BrauerGroup.BrauerGroup
import BrauerGroup.«074E»

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Opposites
import Mathlib.RingTheory.SimpleModule
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import BrauerGroup.«074E»
import BrauerGroup.MatrixCenterEquiv
import BrauerGroup.Lemmas

suppress_compilation

universe u v w

open Classical MulOpposite
open scoped TensorProduct

variable (K : Type u) [Field K]

-- variable {A B M: Type u} [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
--         [csA : IsCentralSimple K A] [hSimple : IsSimpleOrder (RingCon B)]
--         [AddCommGroup M][Module A M][IsSimpleModule A M]
-- variable (L: Module.End A M)
-- -- lemma first
-- -- def L:= Module.End A M
-- -- instance (L: Module.End A M): DivisionRing L := sorry

set_option linter.unusedVariables false in
def module_inst (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] (f : B →ₐ[K] A) := M

instance (K A B M : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] (f: B →ₐ[K] A) [AddCommGroup M]:
    AddCommGroup (module_inst K A B M f) :=
  inferInstanceAs $ AddCommGroup M

instance inst_K_mod (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : Module K (module_inst K A B M f) :=
  Module.compHom M (algebraMap K A)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : Module A (module_inst K A B M f) :=
  inferInstanceAs (Module A M)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : IsScalarTower K A (module_inst K A B M f) :=
  IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl

def smul1AddHom'  (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → B →+ (Module.End A M) →+ (module_inst K A B M f) :=
  fun m ↦ {
    toFun := fun b ↦ {
      toFun := fun l ↦ (f b) • (l m)
      map_zero' := by simp only [LinearMap.zero_apply, smul_zero]
      map_add' := fun l1 l2 ↦ by simp only [LinearMapClass.map_smul, ← smul_add]; rfl
    }
    map_zero' := by ext; simp
    map_add' := fun b1 b2 ↦ by
      ext l; simp only [map_add, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_coe,
      opAddEquiv_apply, Function.comp_apply, unop_op, AddMonoidHom.add_apply];
      exact Module.add_smul (f b1) (f b2) (l m)
  }

def smul1AddHom (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → (B ⊗[K] (Module.End A M)) →+ (module_inst K A B M f) := fun m ↦
  TensorProduct.liftAddHom (smul1AddHom' K A B M f m) fun k b l ↦ by
    simp only [smul1AddHom', AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMapClass.map_smul,
      smul_assoc, unop_smul, LinearMap.smul_apply]
    rw [smul_comm]

def smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → (B ⊗[K] (Module.End A M)) →ₗ[K] (module_inst K A B M f) :=
  fun m ↦ {
    __ := smul1AddHom K A B M f m
    map_smul' := fun k b ↦ by
      simp only [smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        RingHom.id_apply]
      induction b using TensorProduct.induction_on
      · simp only [smul_zero, map_zero]
      · rename_i b l
        simp only [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk, LinearMapClass.map_smul, smul_assoc]
        congr
        ext k m
        change k • m = algebraMap _ _ k • m
        simp only [algebraMap_smul]
      · rename_i bl1 bl2 hbl1 hbl2
        simp only [smul_add, map_add, hbl1, hbl2]
  }

lemma one_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    ∀(m : module_inst K A B M f), smul1 K A B M f m 1 = m := fun m ↦ by
  simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    Algebra.TensorProduct.one_def, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul, unop_one, LinearMap.one_apply]

lemma mul_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):  ∀ (x y : (B ⊗[K] (Module.End A M)))
    (m : module_inst K A B M f),
    smul1 K A B M f m (x * y) = smul1 K A B M f (smul1 K A B M f m y) x := fun x y m ↦ by
  dsimp [smul1, smul1AddHom, smul1AddHom']
  induction x using TensorProduct.induction_on
  · simp only [zero_mul, map_zero]
  · rename_i b1 l1
    induction y using TensorProduct.induction_on
    · simp only [mul_zero, map_zero, smul_zero, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    · rename_i b2 l2
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, unop_mul, LinearMap.mul_apply,
        LinearMapClass.map_smul]
      simp only [smul_smul]
    · simp_all [mul_add]
  · simp_all [add_mul]

lemma smul1_add (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):  ∀ (r : (B ⊗[K] (Module.End A M)))
    (m1 m2 : module_inst K A B M f),
    smul1 K A B M f (m1 + m2) r = smul1 K A B M f m1 r + smul1 K A B M f m2 r := fun r m1 m2 ↦ by
  induction r using TensorProduct.induction_on
  · simp only [map_zero, smul_zero, add_zero]
  · simp only [smul1, smul1AddHom, smul1AddHom', map_add, smul_add, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  · rename_i a b ha hb
    simp_all only [smul1, smul1AddHom, smul1AddHom', map_add, smul_add, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, ← add_assoc, add_left_inj]
    nth_rw 2 [add_assoc]; nth_rw 4 [add_comm]
    rw [← add_assoc]

lemma add_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A): ∀ (r s : B ⊗[K] Module.End A M)
    (x : module_inst K A B M f), smul1 K A B M f x (r + s) =
    smul1 K A B M f x r + smul1 K A B M f x s := fun r s x ↦ by
  simp only [smul1, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add, LinearMap.coe_mk,
    AddHom.coe_mk]

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    Module (B ⊗[K] (Module.End A M)) (module_inst K A B M f) where
  smul := fun r m => smul1 K A B M f m r
  one_smul := one_smul1 K A B M f
  mul_smul := mul_smul1 K A B M f
  smul_zero a := by
    change smul1 K A B M f 0 a = 0
    rw [smul1]
    simp only [map_zero, smul_zero]
    induction a using TensorProduct.induction_on
    · simp only [map_zero]
    · rename_i b l
      simp only [smul1AddHom, smul1AddHom', map_zero, smul_zero, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    · simp_all [map_add]
  smul_add := smul1_add K A B M f
  add_smul := add_smul1 K A B M f
  zero_smul m := by
    change smul1 K A B M f m 0 = 0
    simp only [smul1, map_zero, smul_zero]

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    IsScalarTower K (B ⊗[K] Module.End A M) (module_inst K A B M f) where
  smul_assoc a x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b z =>
      change (smul1 K A B M f _ _) = _ • smul1 K A B M f _ _
      simp
    | add x y hx hy =>
      rw [smul_add, add_smul, hx, hy, add_smul, smul_add]

-- Is this even true?
instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    Module.Finite (B ⊗[K] Module.End A M) (module_inst K A B M f) := by
  sorry

instance tensor_is_simple (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [IsSimpleOrder (RingCon B)][AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] [csa_A : IsCentralSimple K A]: IsSimpleOrder
    (RingCon (B ⊗[K] (Module.End A M))) := by
  haveI : IsCentralSimple K (Module.End A M) := by
    have := csa_A.2
    obtain ⟨n, hn, D, inst1, inst2, ⟨wdb⟩⟩ := Wedderburn_Artin_algebra_version K A
    have : NeZero n := ⟨hn⟩
    obtain ⟨h⟩ := end_simple_mod_of_wedderburn' K A n D wdb M
    haveI : IsCentralSimple K D := by
      apply CSA_implies_CSA _ _ _ _ _ _ wdb inferInstance
      omega
    exact h.symm.isCentralSimple
  haveI := csa_A.2
  obtain ⟨n, hn, D, hD1, hD2, ⟨iso⟩⟩ := Wedderburn_Artin_algebra_version K A
  have : NeZero n := { out := hn }
  obtain ⟨e1⟩ := end_simple_mod_of_wedderburn' K A n D iso M
  haveI : IsCentralSimple K (Module.End A M) :=
    AlgEquiv.isCentralSimple (hcs := CSA_op_is_CSA K D $
      CSA_implies_CSA K A n D (by omega) _ iso csa_A) e1.symm
  exact @IsCentralSimple.TensorProduct.simple K _ B (Module.End A M) _ _ _ _ _ this

section modules_over_simple_ring

variable (N N' R : Type u) [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsSimpleOrder (RingCon R)] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

end modules_over_simple_ring

variable (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] [Ring B]
    [Algebra K B] [hB : IsSimpleOrder (RingCon B)] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f g : B →ₐ[K] A)

lemma findimB : FiniteDimensional K B := FiniteDimensional.of_injective (K := K) (V₂ := A) f (by
    haveI := hA.2
    haveI : Nontrivial A := RingCon.instNontrivialOfIsSimpleOrder_brauerGroup A
    change Function.Injective f
    have H := RingCon.IsSimpleOrder.iff_eq_zero_or_injective B|>.1 hB (B := A) f
    refine H.resolve_left fun rid => ?_
    rw [eq_top_iff, RingCon.le_iff] at rid
    specialize @rid 1 ⟨⟩
    simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, RingCon.mem_ker, _root_.map_one,
        one_ne_zero] at rid )

lemma iso_fg : Nonempty $ module_inst K A B M f ≃ₗ[B ⊗[K] (Module.End A M)] module_inst K A B M g := by
  haveI := findimB K A B f
  haveI := hA.2
  rw [linearEquiv_iff_finrank_eq_over_simple_ring K]
  rfl
-- -- lemma SkolemNoether_aux (A : Type u) [Ring A] [Algebra K A]
-- --   (M : Type u) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
-- --   (B : Type u) [Ring B] [Algebra K B] [Module B M] [IsScalarTower K B M]
-- --   [IsSimpleModule A M] [IsSimpleModule (B ⊗[K] (Aᵐᵒᵖ )) M] :
-- --   ∃ (φ : M →ₗ[A] M), function.surjective φ := sorry
-- -- variable (A: Type u ) [Ring A] [Algebra K A] [FiniteDimensional K A]:
theorem SkolemNoether : ∃(x : Aˣ), ∀(b : B), f b = x * g b * x⁻¹ := by
  obtain ⟨φ⟩ := iso_fg K A B M f g

    -- let L:= Module.End A M
    -- let _: DivisionRing L := by sorry
    -- -- have module_f:= M
    -- -- have module_g:= M
    -- -- let _: Module K Lᵐᵒᵖ := by infer_instance
    -- -- let _: Semiring (B ⊗[K] Lᵐᵒᵖ) := inferInstance
    -- let _: Module (B ⊗[K] Lᵐᵒᵖ) (module_inst K A B M f) := sorry
    -- have : Module (B ⊗[K] Lᵐᵒᵖ) (module_inst K A B M g) := sorry
    -- have : IsSimpleOrder (RingCon (B ⊗[K] Lᵐᵒᵖ))  := sorry
    -- have : FiniteDimensional K B := sorry
    -- have : FiniteDimensional K (B ⊗[K] Lᵐᵒᵖ) := sorry
    -- have : (module_inst K A B M f) ≃ₗ[B ⊗[K] Lᵐᵒᵖ] (module_inst K A B M g) := sorry
    -- have :
  sorry
