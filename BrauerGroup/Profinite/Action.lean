import BrauerGroup.Profinite.Basic

import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Action.Continuous
import Mathlib.Topology.Algebra.ContinuousMonoidHom

open CategoryTheory

universe u v

instance : HasForget₂ (Type u) TopCat where
  forget₂ :=
  { obj := fun X => @TopCat.of X ⊥
    map := fun f => { toFun := f } }
  forget_comp := rfl

variable (Γ : ProfiniteGrp.{u})

attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

instance Action.mulAction (G : MonCat.{u}) (V : Type (u + 1)) [LargeCategory V] [ConcreteCategory V]
    (A : Action V G) : MulAction G A where
  smul σ a := (CategoryTheory.forget V).map (A.ρ σ) a
  one_smul a := show (CategoryTheory.forget V).map (A.ρ 1) a = a by simp
  mul_smul σ τ a := show (CategoryTheory.forget V).map (A.ρ _) _ =
      (CategoryTheory.forget V).map (A.ρ _) ((CategoryTheory.forget V).map (A.ρ _) _) by
    simp only [map_mul, MonCat.mul_of]
    conv_lhs => erw [(CategoryTheory.forget V).map_comp]
    simp only [types_comp_apply]

namespace Action

variable (G : MonCat.{u}) (G : MonCat.{u}) (V : Type (u + 1)) [LargeCategory V] [ConcreteCategory V]
variable (A : Action V G)

lemma smul_def (σ : G) (a : A) : σ • a = (CategoryTheory.forget V).map (A.ρ σ) a := rfl

end Action

structure ΓGroup where
  carrier : Type v
  [group : Group carrier]
  ρ : Γ →* (carrier ≃* carrier)

namespace ΓGroup

instance : CoeSort (ΓGroup Γ) (Type v) where
  coe A := A.carrier

instance (A : ΓGroup Γ) : Group A := A.group

variable {Γ}

@[simps]
def toAction (A : ΓGroup.{u, u} Γ) : Action (Type u) (MonCat.of Γ) where
  V := A
  ρ :=
  { toFun := fun σ x => A.ρ σ x
    map_one' := by aesop
    map_mul' := by aesop }

instance (A : ΓGroup Γ) : MulAction Γ A := A.toAction.mulAction

lemma smul_def (A : ΓGroup Γ) (σ : Γ) (a : A) : σ • a = A.ρ σ a := rfl

instance (A : ΓGroup Γ) : MulDistribMulAction Γ A where
  smul_mul σ a b := by simp [smul_def]
  smul_one σ := by simp [smul_def]

lemma smul_inv {A : ΓGroup Γ} (σ : Γ) (a : A) : (σ • a)⁻¹ = σ • a⁻¹ := by
  simp only [smul_def, smul_inv']

end ΓGroup

structure ContinuousΓGroup extends ΓGroup Γ where
  [topologicalSpace : TopologicalSpace toΓGroup]
  [topologicalGroup : TopologicalGroup toΓGroup]
  [continuousSMul : ContinuousSMul Γ toΓGroup]

namespace ContinuousΓGroup

instance : CoeSort (ContinuousΓGroup Γ) (Type u) where
  coe A := A.toΓGroup

instance (A : ContinuousΓGroup Γ) : Group A := inferInstance
instance (A : ContinuousΓGroup Γ) : TopologicalSpace A := A.topologicalSpace
instance (A : ContinuousΓGroup Γ) : TopologicalGroup A := A.topologicalGroup

end ContinuousΓGroup

structure DiscreteContinuousΓGroup extends ContinuousΓGroup Γ where
  [discrete : DiscreteTopology toΓGroup]

namespace DiscreteContinuousΓGroup

instance : CoeSort (DiscreteContinuousΓGroup Γ) (Type u) where
  coe A := A.toΓGroup

instance (A : DiscreteContinuousΓGroup Γ) : Group A := A.group
instance (A : DiscreteContinuousΓGroup Γ) : TopologicalSpace A := A.topologicalSpace
instance (A : DiscreteContinuousΓGroup Γ) : TopologicalGroup A := A.topologicalGroup
instance (A : DiscreteContinuousΓGroup Γ) : DiscreteTopology A := A.discrete

end DiscreteContinuousΓGroup

variable (A : DiscreteContinuousΓGroup Γ)

structure ContinuousH₀ : Type u where
  elem : A
  invariant : ∀ σ : Γ, σ • elem = elem

namespace ContinuousH₀

instance : Inhabited (ContinuousH₀ Γ A) where
  default := ⟨1, by simp⟩

end ContinuousH₀

structure ContinuousOneCocycle extends ContinuousMap Γ A where
  cocyle : ∀ σ τ : Γ,
    toContinuousMap (σ * τ) =
    toContinuousMap σ * (σ • toContinuousMap τ)

instance : FunLike (ContinuousOneCocycle Γ A) Γ A where
  coe f := f.toContinuousMap
  coe_injective' f g h := by cases f; cases g; aesop

instance : ContinuousMapClass (ContinuousOneCocycle Γ A) Γ A where
  map_continuous f := f.toContinuousMap.continuous

variable {Γ A} in
def ContinuousOneCocycle.cohomologous (f g : ContinuousOneCocycle Γ A) : Prop :=
  ∃ a : A, ∀ σ : Γ, f σ = a⁻¹ * g σ * (σ • a)

variable {Γ A} in
lemma ContinuousOneCocycle.cohomologous.refl (f : ContinuousOneCocycle Γ A) :
    f.cohomologous f :=
  ⟨1, fun σ => by simp⟩

variable {Γ A} in
lemma ContinuousOneCocycle.cohomologous.symm {f g : ContinuousOneCocycle Γ A}
    (h : f.cohomologous g) : g.cohomologous f := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a⁻¹, fun σ => ?_⟩
  simp only [inv_inv, ha, mul_assoc, mul_inv_cancel_left, smul_inv', mul_right_inv, mul_one]

variable {Γ A} in
lemma ContinuousOneCocycle.cohomologous.trans {f g h : ContinuousOneCocycle Γ A}
    (hfg : f.cohomologous g) (hgh : g.cohomologous h) : f.cohomologous h := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgh
  refine ⟨b * a, fun σ => ?_⟩
  simp only [ha, hb, ← mul_assoc, mul_inv_rev, smul_mul']

def ContinuousOneCocycle.setoid : Setoid (ContinuousOneCocycle Γ A) where
  r := ContinuousOneCocycle.cohomologous
  iseqv :=
  { refl := ContinuousOneCocycle.cohomologous.refl
    symm := ContinuousOneCocycle.cohomologous.symm
    trans := ContinuousOneCocycle.cohomologous.trans }

abbrev ContinuousH₁ : Type u := Quotient (ContinuousOneCocycle.setoid Γ A)

namespace ContinuousH₁

instance : Inhabited (ContinuousH₁ Γ A) where
  default := Quotient.mk _
    { toFun := fun _ => 1
      continuous_toFun := by continuity
      cocyle := fun σ _ => show 1 = 1 * σ • 1 by simp }

end ContinuousH₁
