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

attribute [-instance] MulOpposite.instAddCommMonoid MulOpposite.instModule in
instance (K A B M : Type u)
    [Field K] [Ring A] [Ring B] [Algebra K B] [Algebra K A]
    [AddCommGroup M] [Module K M]  [Module A M] [IsScalarTower K A M] [IsSimpleModule A M] :
    Semiring (B ⊗[K] (Module.End A M)ᵐᵒᵖ) :=
  Algebra.TensorProduct.instSemiring -- Module.End.divisionRing

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

attribute [-instance] MulOpposite.instAddCommMonoid MulOpposite.instModule in
instance(K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : Ring (B ⊗[K] (Module.End A M)ᵐᵒᵖ)ᵐᵒᵖ := inferInstance

attribute [-instance] MulOpposite.instAddCommMonoid MulOpposite.instModule in
def smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → (B ⊗[K] (Module.End A M)ᵐᵒᵖ) →ₗ[K] (module_inst K A B M f) :=
  fun m ↦ TensorProduct.lift {
    toFun := fun b ↦ {
      toFun := fun l ↦ (f b) • (l.unop m)
      map_add' := fun l1 l2 ↦ by simp only [LinearMapClass.map_smul, ← smul_add]; rfl
      map_smul' := fun k l ↦ by
        simp only [LinearMapClass.map_smul, RingHom.id_apply]
        rw [smul_comm]; simp only [unop_smul, LinearMap.smul_apply]
    }
    map_add' := fun _ _ ↦ by
      ext _ ; simp [add_smul]
    map_smul' := fun k b ↦ by
      ext l
      simp only [LinearMapClass.map_smul, smul_assoc, LinearMap.map_smul_of_tower, LinearMap.coe_mk,
        AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
      congr; rw [inst_K_mod];
      ext k m
      change k • m = algebraMap _ _ k • m
      simp only [algebraMap_smul]
  }

attribute [-instance] MulOpposite.instAddCommMonoid MulOpposite.instModule in
instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    Module (B ⊗[K] (Module.End A M)ᵐᵒᵖ)ᵐᵒᵖ (module_inst K A B M f) where
  smul := fun r m => smul1 K A B M f m r.unop
  one_smul m := by
    change smul1 K A B M f m 1 = m
    rw [smul1, Algebra.TensorProduct.one_def]
    simp only [TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, map_one, one_smul,
      unop_one, LinearMap.one_apply]
  mul_smul x y m := sorry
  smul_zero a := by
    change smul1 K A B M f 0 a.unop = 0
    rw [smul1]
    cases' a with a
    simp only [map_zero, smul_zero, unop_op]
    induction a using TensorProduct.induction_on
    · sorry
    · sorry
    · sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

attribute [-instance] MulOpposite.instAddCommMonoid MulOpposite.instModule in
set_option synthInstance.maxHeartbeats 40000 in
instance tensor_is_simple (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [IsSimpleOrder (RingCon B)][AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] [csa_A : IsCentralSimple K A]: IsSimpleOrder (RingCon (B ⊗[K] (Module.End A M)ᵐᵒᵖ)) := by
  haveI : IsCentralSimple K (Module.End A M)ᵐᵒᵖ := CSA_op_is_CSA K (Module.End A M) ({
    is_central := by
      intro l hl
      rw [Subalgebra.mem_center_iff] at hl
      obtain ⟨m, hm⟩ := IsSimpleModule.instIsPrincipal A (⊤ : Submodule A M)
      let a : A := Submodule.mem_span_singleton.1 (hm ▸ ⟨⟩ : l m ∈ Submodule.span A {m}) |>.choose
      have ha : l m = a • m := Submodule.mem_span_singleton.1
        (hm ▸ ⟨⟩ : l m ∈ Submodule.span A {m}) |>.choose_spec.symm
      have l_eq : l = ⟨⟨(a • ·), sorry⟩, sorry⟩ := sorry
      have mem_a : a ∈ Subalgebra.center K A := by
        rw [Subalgebra.mem_center_iff]
        intro b
        let 𝒷 : Module.End A M := ⟨⟨(b • ·), sorry⟩, sorry⟩
        specialize hl 𝒷
        have hl : b • l m = l (b • m) := congr($hl m)
        simp only [l_eq, LinearMap.coe_mk, AddHom.coe_mk] at hl
        rw [smul_smul, smul_smul] at hl
        -- let ann : RingCon A := RingCon.fromIdeal {r | r • m = 0} (by sorry) (by sorry)
        --   (by sorry) (fun x y hxy ↦ by
        --     change _ • m = 0 at *
        --     rw [← smul_smul, hxy, smul_zero]) (fun x y hxy ↦ by
        --     change _ • m = 0 at *
        --     sorry)
        sorry
      have := csa_A.1 mem_a
      rw [Algebra.mem_bot] at *
      rcases this with ⟨k, hk⟩
      use k
      rw [l_eq]
      ext m
      simp only [Module.algebraMap_end_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← hk, algebraMap_smul]; congr
      ext k m
      change algebraMap _ _ k • m = k • m
      simp only [algebraMap_smul]
    is_simple := inferInstance
  })
  exact @IsCentralSimple.TensorProduct.simple K _ B (Module.End A M)ᵐᵒᵖ _ _ _ _ _ this

variable (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f g : B →ₐ[K] A)

-- -- lemma SkolemNoether_aux (A : Type u) [Ring A] [Algebra K A]
-- --   (M : Type u) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
-- --   (B : Type u) [Ring B] [Algebra K B] [Module B M] [IsScalarTower K B M]
-- --   [IsSimpleModule A M] [IsSimpleModule (B ⊗[K] (Aᵐᵒᵖ )) M] :
-- --   ∃ (φ : M →ₗ[A] M), function.surjective φ := sorry
-- -- variable (A: Type u ) [Ring A] [Algebra K A] [FiniteDimensional K A]:
theorem SkolemNoether
        (A B M: Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
        [csA : IsCentralSimple K A] [hSimple : IsSimpleOrder (RingCon B)]
        (f g: B →ₐ[K] A)[AddCommGroup M][Module A M][IsSimpleModule A M]: ∃(x : Aˣ), ∀(b : B), f b = x * g b * x⁻¹ := by
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
