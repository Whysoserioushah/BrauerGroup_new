import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Topology.Category.Profinite.Basic

/-!

# Category of Profinite Groups

We say `G` is a profinite group if it is a topological group which is compact and totally
disconnected.

## Main definitions and results

* `ProfiniteGrp` is the type of profinite groups.
* `FiniteGrp` is the type of finite groups.
* `limitOfFiniteGrp`: direct limit of finite groups is a profinite group

-/

suppress_compilation

universe u v

open CategoryTheory Topology

structure ProfiniteGrp extends Profinite where
[group : Group toProfinite]
[topologicalGroup : TopologicalGroup toProfinite]

structure FiniteGrp where
  carrier : Grp
  isFinite : Fintype carrier

namespace FiniteGrp

instance : CoeSort FiniteGrp.{u} (Type u) where
  coe (G : FiniteGrp) : Type u := G.carrier

instance (G : FiniteGrp) : Group G := inferInstanceAs $ Group G.carrier

instance (G : FiniteGrp) : Fintype G := G.isFinite

instance : Category FiniteGrp := InducedCategory.category FiniteGrp.carrier

instance : ConcreteCategory FiniteGrp := InducedCategory.concreteCategory FiniteGrp.carrier

def of (G : Type u) [Group G] [Fintype G] : FiniteGrp where
  carrier := Grp.of G
  isFinite := inferInstanceAs $ Fintype G

instance (G H : FiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs $ FunLike (G →* H) G H

instance (G H : FiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs $ MonoidHomClass (G →* H) G H

end FiniteGrp

namespace ProfiniteGroup

instance : CoeSort ProfiniteGrp (Type u) where
  coe (G : ProfiniteGrp) : Type u := G.toProfinite

instance (G : ProfiniteGrp) : Group G := G.group

instance (G : ProfiniteGrp) : TopologicalGroup G := G.topologicalGroup

def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toCompHaus :=
    { toTop := .of G
      is_compact := inferInstanceAs $ CompactSpace G
      is_hausdorff := inferInstanceAs $ T2Space G }
  isTotallyDisconnected := inferInstanceAs $ TotallyDisconnectedSpace G
  group := inferInstanceAs $ Group G
  topologicalGroup := inferInstanceAs $ TopologicalGroup G


structure Hom (G H : ProfiniteGrp) extends G →* H, ContinuousMap G H

def Hom.id (G : ProfiniteGrp) : Hom G G where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by continuity

instance (G H) : FunLike (Hom G H) G H where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; aesop

instance (G H) : MonoidHomClass (Hom G H) G H where
  map_mul f := f.toMonoidHom.map_mul
  map_one f := f.toMonoidHom.map_one

instance (G H) : ContinuousMapClass (Hom G H) G H where
  map_continuous f := f.toContinuousMap.continuous

lemma Hom.continuous {G H : ProfiniteGrp} (f : Hom G H) : Continuous f := by continuity

@[continuity]
lemma Hom.continuous' {G H : ProfiniteGrp} (f : Hom G H) : Continuous f.toMonoidHom :=
  show Continuous f by continuity

def Hom.comp {G H K : ProfiniteGrp} (g : Hom G H) (f : Hom H K)  : Hom G K where
  toFun := f.toFun ∘ g.toFun
  map_one' := by simp
  map_mul' := by simp

instance : Category ProfiniteGrp where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance (G H : ProfiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs $ FunLike (Hom G H) G H

instance (G H : ProfiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs $ MonoidHomClass (Hom G H) G H

instance (G H : ProfiniteGrp) : ContinuousMapClass (G ⟶ H) G H :=
  inferInstanceAs $ ContinuousMapClass (Hom G H) G H

instance : ConcreteCategory ProfiniteGrp where
  forget :=
  { obj := fun G => G
    map := fun f => f.toFun }
  forget_faithful :=
    { map_injective := by
        intro G H f g h
        simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, id_eq] at h ⊢
        exact DFunLike.ext _ _ $ fun x => congr_fun h x }

def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G

def ofClosedSubgroup {G : ProfiniteGrp}
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : ProfiniteGrp :=
  letI : CompactSpace H := ClosedEmbedding.compactSpace (f := H.subtype)
    { induced := rfl
      inj := H.subtype_injective
      isClosed_range := by simpa }
  of H

section

variable {J : Type v} [Category J] (F : J ⥤ FiniteGrp)

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

instance (j : J) : TopologicalSpace (F.obj j) := ⊥

instance (j : J) : DiscreteTopology (F.obj j) := ⟨rfl⟩

instance (j : J) : TopologicalGroup (F.obj j) where
  continuous_mul := by continuity
  continuous_inv := by continuity

instance : TopologicalSpace (Π j : J, F.obj j) :=
  Pi.topologicalSpace

def G_ : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp
  inv_mem' h _ _ π := by simp [h π]

@[simp]
lemma mem_G_ (x : Π j : J, F.obj j) : x ∈ G_ F ↔ ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j :=
  Iff.rfl

instance : CompactSpace (G_ F) := ClosedEmbedding.compactSpace (f := (G_ F).subtype)
  { induced := rfl
    inj := Subgroup.subtype_injective _
    isClosed_range := by
      classical
      let S ⦃i j : J⦄ (π : i ⟶ j) : Set (Π j : J, F.obj j) := {x | F.map π (x i) = x j}
      have hS ⦃i j : J⦄ (π : i ⟶ j) : IsClosed (S π) := by
        simp only [S]
        rw [← isOpen_compl_iff, isOpen_pi_iff]
        rintro x (hx : ¬ _)
        simp only [Set.mem_setOf_eq] at hx
        refine ⟨{i, j}, fun i => {x i}, ?_⟩
        simp only [Finset.mem_singleton, isOpen_discrete, Set.mem_singleton_iff, and_self,
          implies_true, Finset.coe_singleton, Set.singleton_pi, true_and]
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.insert_pi, Set.singleton_pi,
          Set.mem_inter_iff, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
          Set.mem_compl_iff, Set.mem_setOf_eq] at hy ⊢
        rwa [hy.1, hy.2]
      have eq : Set.range (G_ F).subtype = ⋂ (i : J) (j : J) (π : i ⟶ j), S π := by
        ext x
        simp only [Subgroup.coeSubtype, Subtype.range_coe_subtype, SetLike.mem_coe, mem_G_,
          Set.mem_setOf_eq, Set.mem_iInter]
        tauto
      rw [eq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun π => hS π }

def limitOfFiniteGrp : ProfiniteGrp := of (G_ F)

end


end ProfiniteGroup
