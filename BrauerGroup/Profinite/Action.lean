import BrauerGroup.Profinite.Basic

import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Action.Continuous

open CategoryTheory

universe u

variable (V : Type (u + 1)) [LargeCategory V] [ConcreteCategory V] [HasForget₂ V TopCat]

instance : HasForget₂ (Type u) TopCat where
  forget₂ :=
  { obj := fun X => @TopCat.of X ⊥
    map := fun f => { toFun := f } }
  forget_comp := rfl

variable (Γ : ProfiniteGrp.{u})

instance : TopologicalSpace (MonCat.of Γ) := inferInstanceAs $ TopologicalSpace Γ

variable (A : DiscreteContAction (Type u) $ MonCat.of Γ)

attribute [local instance] ConcreteCategory.hasCoeToSort

def C (n : ℕ) : Type u := ContinuousMap (Fin n → Γ) ((forget₂ _ TopCat).obj A)
