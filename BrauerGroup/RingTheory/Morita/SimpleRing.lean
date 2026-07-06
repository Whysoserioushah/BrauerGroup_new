module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Morita.Matrix
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import BrauerGroup.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.SimpleRing.DivisionRing

/-!
## Simple modules over simple rings

## Main results

* `linearEquiv_of_isSimpleModule_over_simple_ring`: any two simple modules over an Artinian
  simple ring are isomorphic.
* `directSum_simple_module_over_simple_ring`: any module over an Artinian simple ring is
  isomorphic to a direct sum of copies of a simple module.
* `linearEquiv_iff_finrank_eq_over_simple_ring`: two finite modules over a finite simple algebra
  `A` over a field `k` are isomorphic as `A`-modules if and only if they have the same dimension
  over `k`.
-/

@[expose] public section

open CategoryTheory DirectSum

universe w u v

section simple

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [Module.Finite k A]

@[stacks 074E "(1)"]
lemma linearEquiv_of_isSimpleModule_over_simple_ring [IsArtinianRing A] (M N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N] [IsSimpleModule A M]
    [IsSimpleModule A N] : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨n, hn, D, _, ⟨iso₁⟩⟩ := IsSimpleRing.exists_ringEquiv_matrix_divisionRing A
  let e₂ : ModuleCat A ≌ ModuleCat D :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm).trans <|
    ModuleCat.matrixEquivalence D 0|>.symm
  have := IsSimpleModule.obj_of_isEquivalence e₂.functor (ModuleCat.of A M)
  have := IsSimpleModule.obj_of_isEquivalence e₂.functor (ModuleCat.of A N)
  have iso₂ := DivisionRing.nonempty_linearEquiv_of_isSimpleModule D
    (e₂.functor.obj (ModuleCat.of A M))|>.some.trans
    (DivisionRing.nonempty_linearEquiv_of_isSimpleModule D
      (e₂.functor.obj (ModuleCat.of A N))|>.some.symm)
  exact ⟨e₂.unitIso.app _ ≪≫ (e₂.inverse.mapIso <| iso₂.toModuleIso) ≪≫
    (e₂.unitIso.app _).symm|>.toLinearEquiv⟩

@[stacks 074E "(2)"]
lemma directSum_simple_module_over_simple_ring [IsArtinianRing A] (M : Type v) [AddCommGroup M]
    [Module A M] : ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module A S) (_ : IsSimpleModule A S)
    (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  classical
  obtain ⟨n, hn, D, inst1, ⟨iso₁⟩⟩ := IsSimpleRing.exists_ringEquiv_matrix_divisionRing A
  let e₁ := ModuleCat.matrixEquivalence D (ι := Fin n) 0
  let e₂ : ModuleCat A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm
  let e := e₂.trans e₁.symm
  let S := e.inverse.obj (ModuleCat.of D D)
  have : IsSimpleModule A S := IsSimpleModule.obj_of_isEquivalence e.inverse (ModuleCat.of D D)
  obtain ⟨b, hb⟩ : Module.Free D (e.functor.obj (ModuleCat.of A M)) := inferInstance
  refine ⟨S, inferInstance, inferInstance, inferInstance, b, ⟨?_⟩⟩
  let iso₄ : ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    (finsuppLequivDFinsupp _).toModuleIso ≪≫ (ModuleCat.coprodIsoDirectSum _).symm ≪≫
    (Limits.PreservesCoproduct.iso _ _).symm ≪≫ e.inverse.mapIso
    ((ModuleCat.coprodIsoDirectSum _) ≪≫ (finsuppLequivDFinsupp _).symm.toModuleIso)
  exact e.unitIso.app (ModuleCat.of A M) ≪≫ (e.inverse.mapIso hb.repr.toModuleIso)
    ≪≫ iso₄.symm |>.toLinearEquiv

@[stacks 074E "(2)"]
lemma directSum_simple_module_over_simple_algebra (M : Type v) [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] : ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module k S)
    (_ : Module A S) (_ : IsScalarTower k A S) (_ : IsSimpleModule A S) (ι : Type v),
    Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring A M
  let : Module k S := Module.compHom S (algebraMap k A)
  have : IsScalarTower k A S := .of_algebraMap_smul fun _ _ ↦ rfl
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ι, ⟨iso⟩⟩

lemma directSum_simple_module_over_simple_algebra' (A : Type v) [Ring A] [IsArtinianRing A]
    [IsSimpleRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (S : Type v) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    ∃ (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  obtain ⟨T, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring A M
  obtain ⟨iso'⟩ := linearEquiv_of_isSimpleModule_over_simple_ring A S T
  exact ⟨ι, ⟨iso ≪≫ₗ Finsupp.mapRange.linearEquiv iso'.symm⟩⟩

attribute [local instance] Fintype.ofFinite in
@[stacks 074E "(3)"]
lemma linearEquiv_iff_finrank_eq_over_simple_ring
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module k M]
    [Module k N] [IsScalarTower k A M] [IsScalarTower k A N] [Module.Finite A M]
    [Module.Finite A N] : Nonempty (M ≃ₗ[A] N) ↔ Module.finrank k M = Module.finrank k N := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : Module.Finite k M := Module.Finite.trans A M
  have : Module.Finite k N := Module.Finite.trans A N
  refine ⟨fun ⟨e⟩ ↦ (e.restrictScalars k).finrank_eq, fun h ↦ ?_⟩
  obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring A M
  obtain ⟨ι', ⟨iso'⟩⟩ := directSum_simple_module_over_simple_algebra' A N S
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨Module.equivOfSingleton h iso.injective.subsingleton⟩
  obtain hι' | hι' := isEmpty_or_nonempty ι'
  · exact ⟨Module.equivOfSingleton h.symm iso'.injective.subsingleton|>.symm⟩
  letI : Module k S := Module.compHom S (algebraMap k A)
  haveI : IsScalarTower k A S := .of_algebraMap_smul fun _ _ ↦ rfl
  haveI : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨hS, hfι⟩ := (Module.finite_finsupp_iff.1 <| Module.Finite.equiv
    (iso.restrictScalars k)).resolve_left (not_isEmpty_of_nonempty ι) |>.resolve_left
    (not_subsingleton S)
  obtain ⟨-, hfι'⟩ := (Module.finite_finsupp_iff.1 <| Module.Finite.equiv
    (iso'.restrictScalars k)).resolve_left (not_isEmpty_of_nonempty ι') |>.resolve_left
    (not_subsingleton S)
  have EQ := (iso.restrictScalars k).finrank_eq.symm.trans <|
    h.trans (iso'.restrictScalars k).finrank_eq
  simp only [Module.finrank_finsupp, mul_eq_mul_right_iff] at EQ
  replace EQ := Fintype.card_eq.1 <| EQ.resolve_right <| ne_of_gt Module.finrank_pos
  exact ⟨iso ≪≫ₗ Finsupp.lcongr EQ.some (LinearEquiv.refl A S) ≪≫ₗ iso'.symm⟩

namespace IsSimpleRing

open Matrix.Module

scoped instance {n : ℕ} (D : Type w) [DivisionRing D] [Algebra k D] :
    IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) where
  smul_assoc a b x := by ext; simp [Finset.smul_sum]

scoped instance {n : ℕ} (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    letI := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
    IsScalarTower k A (Fin n → D) :=
  let := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
  ⟨fun a b x ↦ show wdb (a • b) • x = _ by
    rw [map_smul, Algebra.smul_def, mul_smul, algebraMap_smul]; rfl⟩

scoped instance {n : ℕ} (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    letI := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
    SMulCommClass A k (Fin n → D) :=
  let := Module.compHom (Fin n → D) wdb.toRingEquiv.toRingHom
  ⟨fun a b x ↦ show wdb a • b • x = b • wdb a • x by ext; simp [Finset.smul_sum]⟩

end IsSimpleRing
