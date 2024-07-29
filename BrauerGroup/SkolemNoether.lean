import BrauerGroup.CentralSimple
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
  one_smul := sorry
  mul_smul x y m := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

theorem tensor_is_simple (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [IsSimpleOrder (RingCon B)][AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A): IsSimpleOrder (RingCon (B ⊗[K] (Module.End A M)ᵐᵒᵖ)) := by

  sorry

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
