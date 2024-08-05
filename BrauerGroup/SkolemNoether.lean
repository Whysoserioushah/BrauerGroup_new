import BrauerGroup.BrauerGroup
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Opposites
import Mathlib.RingTheory.SimpleModule
import Mathlib.LinearAlgebra.TensorProduct.Opposite

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
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

instance tensor_is_simple (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [IsSimpleOrder (RingCon B)][AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] [csa_A : IsCentralSimple K A]: IsSimpleOrder
    (RingCon (B ⊗[K] (Module.End A M))) := by
  haveI : IsCentralSimple K (Module.End A M) := {
    is_central := by
      intro l hl
      rw [Subalgebra.mem_center_iff] at hl
      obtain ⟨m, hm⟩ := IsSimpleModule.instIsPrincipal A (⊤ : Submodule A M)
      let a : A := Submodule.mem_span_singleton.1 (hm ▸ ⟨⟩ : l m ∈ Submodule.span A {m}) |>.choose
      have ha : l m = a • m := Submodule.mem_span_singleton.1
        (hm ▸ ⟨⟩ : l m ∈ Submodule.span A {m}) |>.choose_spec.symm
      have hm' : ∀(m' : M), ∃(a' : A), a' • m = m' := fun m' ↦
        Submodule.mem_span_singleton.1 (hm ▸ ⟨⟩ : m' ∈ Submodule.span A {m})
      have l_eq : l = ⟨⟨(a • ·), smul_add a⟩, fun a' mm ↦ by
        simp only [RingHom.id_apply]
        obtain ⟨aa, haa⟩ := hm' mm
        rw [← haa]
        sorry⟩ := sorry
      have hl'' : ∀(l' : Module.End A M), ∃(b : A), b • m = l' m := fun l' ↦
        Submodule.mem_span_singleton.1 (hm ▸ ⟨⟩ : l' m ∈ Submodule.span A {m})
      have mem_a : a ∈ Subalgebra.center K A := by
        rw [Subalgebra.mem_center_iff]
        intro b
        let 𝒷 : Module.End A M := ⟨⟨(b • ·), sorry⟩, sorry⟩
        specialize hl 𝒷
        have hl : b • l m = l (b • m) := congr($hl m)
        simp only [l_eq, LinearMap.coe_mk, AddHom.coe_mk] at hl
        rw [smul_smul, smul_smul] at hl
        have hl' : ∀(l' : Module.End A M),(a * b) • (l' m) = (b * a) • (l' m) := by
          intro l'
          apply_fun l' at hl
          simp only [LinearMapClass.map_smul] at hl
          exact hl.symm
        have hM : ∀(m' : M), ∃(l : Module.End A M), l m = m' := fun m' ↦ by
          obtain ⟨a', ha⟩ := hm' m'
          use ⟨⟨(a' • ·), sorry⟩, sorry⟩
          exact ha
        let ann : RingCon A := RingCon.fromIdeal {r | ∀(m : M), r • m = 0} (by simp)
          (fun _ _ _ _ ↦ by simp_all [add_smul])
          (by sorry) (fun x y hxy ↦ by
            intro m
            rw [← smul_smul, hxy, smul_zero]) (fun x y hxy ↦ by
            intro m
            change ∀(m : M), _ • _ = 0 at hxy
            rw [← smul_smul, hxy (y • m)])
        have isann : b * a - a * b ∈ ann := fun n ↦ by
          simp only [sub_zero]
          rw [← sub_eq_zero, ← sub_smul] at hl
          obtain ⟨f', hf'⟩ := hM n
          rw [← hf', ← map_smul, hl, map_zero]
        have : ann = ⊥ := by
          haveI := csa_A.2.2 ann
          cases' this with h1 h2
          exact h1
          have nontriv : Nontrivial (Module.End A M) := GroupWithZero.toNontrivial
          obtain ⟨φ, hφ⟩ := exists_ne (0 : Module.End A M)
          obtain ⟨b, hb⟩:= hl'' φ
          have φ_0 : φ = 0 := by
            ext m'
            obtain ⟨x, hx⟩ := hm' m'
            rw [← hx, map_smul, map_smul]
            have x_mem : x ∈ (⊤ : RingCon A) := ⟨⟩
            rw [← h2] at x_mem
            change ∀(m : _), _ = _ at x_mem
            rw [sub_zero] at x_mem
            rw [x_mem (φ m), LinearMap.zero_apply, smul_zero]
          tauto
        rw [this] at isann
        change _ - _ = _ at isann
        apply_fun (· + a * b) at isann
        rw [zero_add] at isann
        simp only [sub_add_cancel] at isann
        exact isann
      have := csa_A.1 mem_a
      rw [Algebra.mem_bot] at *
      rcases this with ⟨k, hk⟩
      use k
      rw [l_eq]
      ext m
      simp only [Module.algebraMap_end_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← hk, algebraMap_smul]
  }
  exact @IsCentralSimple.TensorProduct.simple K _ B (Module.End A M) _ _ _ _ _ this

section modules_over_simple_ring

variable (N N' R : Type u) [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsSimpleOrder (RingCon R)] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

theorem iso_iff_dim_eq (h : FiniteDimensional.finrank R N = FiniteDimensional.finrank R N'):
    Nonempty (N ≃ₗ[R] N') := by
  sorry

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

def iso_fg : module_inst K A B M f ≃ₗ[B ⊗[K] (Module.End A M)] module_inst K A B M g := sorry
-- -- lemma SkolemNoether_aux (A : Type u) [Ring A] [Algebra K A]
-- --   (M : Type u) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
-- --   (B : Type u) [Ring B] [Algebra K B] [Module B M] [IsScalarTower K B M]
-- --   [IsSimpleModule A M] [IsSimpleModule (B ⊗[K] (Aᵐᵒᵖ )) M] :
-- --   ∃ (φ : M →ₗ[A] M), function.surjective φ := sorry
-- -- variable (A: Type u ) [Ring A] [Algebra K A] [FiniteDimensional K A]:
theorem SkolemNoether : ∃(x : Aˣ), ∀(b : B), f b = x * g b * x⁻¹ := by
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
