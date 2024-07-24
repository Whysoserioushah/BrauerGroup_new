import BrauerGroup.CentralSimple
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Opposites
import Mathlib.RingTheory.SimpleModule

suppress_compilation

universe u v w

open Classical
open scoped TensorProduct
variable (K : Type u) [Field K]
-- variable {A B M: Type u} [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
--         [csA : IsCentralSimple K A] [hSimple : IsSimpleOrder (RingCon B)]
--         [AddCommGroup M][Module A M][IsSimpleModule A M]
-- variable (L: Module.End A M)
-- -- lemma first
-- -- def L:= Module.End A M
-- -- instance (L: Module.End A M): DivisionRing L := sorry

def module_inst (K A B : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B] (M: Type u) (f: B →ₐ[K] A):= M

instance (K A B : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B](M: Type u) (f: B →ₐ[K] A) [AddCommGroup M]:
    AddCommGroup (module_inst K A B M f) :=
  inferInstanceAs $ AddCommGroup M
instance (K A B M : Type u) [Field K] [Ring A] [Ring B] [Algebra K B] [Algebra K A] [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [IsSimpleModule A M] :
    Semiring (B ⊗[K] (Module.End A M)ᵐᵒᵖ) := Algebra.TensorProduct.instSemiring -- Module.End.divisionRing
instance(K A B : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    (M : Type u) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A)
    : Module (B ⊗[K] (Module.End A M)ᵐᵒᵖ) (module_inst K A B M f) where
--   smul := sorry
--   one_smul := sorry
--   mul_smul := sorry
--   smul_zero := sorry
--   smul_add := sorry
--   add_smul := sorry
--   zero_smul := sorry

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
    let L:= Module.End A M
    let _: DivisionRing L := by sorry
    -- have module_f:= M
    -- have module_g:= M
    -- let _: Module K Lᵐᵒᵖ := by infer_instance
    -- let _: Semiring (B ⊗[K] Lᵐᵒᵖ) := inferInstance
    let _: Module (B ⊗[K] Lᵐᵒᵖ) (module_inst K A B M f) := sorry
    have : Module (B ⊗[K] Lᵐᵒᵖ) (module_inst K A B M g) := sorry
    have : IsSimpleOrder (RingCon (B ⊗[K] Lᵐᵒᵖ))  := sorry
    have : FiniteDimensional K B := sorry
    have : FiniteDimensional K (B ⊗[K] Lᵐᵒᵖ) := sorry
    have : (module_inst K A B M f) ≃ₗ[B ⊗[K] Lᵐᵒᵖ] (module_inst K A B M g) := sorry
    have :
    sorry
