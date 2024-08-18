import BrauerGroup.Wedderburn

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Algebra.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

open CategoryTheory

universe u v w

section simple

variable (k : Type u) [Field k] (A : Type v)
variable [Ring A] [Algebra k A] [IsSimpleOrder (RingCon A)] [FiniteDimensional k A]

/--
Stack 074E (1)
-/
lemma linearEquiv_of_isSimpleModule_over_simple_ring
    (M N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [IsSimpleModule A M] [IsSimpleModule A N] : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨n, hn, D, inst1, inst2, ⟨iso₁⟩⟩ := Wedderburn_Artin_algebra_version k A
  letI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  let e₁ := moritaEquivalentToMatrix.{_, _, w} D (Fin n)
  let e₂ : ModuleCat.{w} A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm.toRingEquiv
  let e₃ := e₂.trans e₁.symm
  haveI : IsSimpleModule A (ModuleCat.of A M) := inferInstanceAs $ IsSimpleModule A M
  haveI : IsSimpleModule A (ModuleCat.of A N) := inferInstanceAs $ IsSimpleModule A N
  haveI := IsMoritaEquivalent.division_ring.IsSimpleModule.functor A D e₃ (ModuleCat.of A M)
  haveI := IsMoritaEquivalent.division_ring.IsSimpleModule.functor A D e₃ (ModuleCat.of A N)
  obtain ⟨iso₂⟩ := IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule D
    (e₃.functor.obj (ModuleCat.of A M))
  obtain ⟨iso₃⟩ := IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule D
    (e₃.functor.obj (ModuleCat.of A N))
  let iso₄ : e₃.functor.obj (ModuleCat.of A M) ≅ e₃.functor.obj (ModuleCat.of A N) :=
    LinearEquiv.toModuleIso $ iso₂ ≪≫ₗ iso₃.symm
  let iso₅ : ModuleCat.of A M ≅ ModuleCat.of A N :=
    e₃.unitIso.app (ModuleCat.of A M) ≪≫ e₃.inverse.mapIso iso₄ ≪≫
      (e₃.unitIso.app (ModuleCat.of A N)).symm
  exact ⟨iso₅.toLinearEquiv⟩

noncomputable abbrev iso₄_toFun (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D):
  ↑(ModuleCat.of A (b →₀ ↑((ModuleCat.restrictScalars iso₁.toRingEquiv.toRingHom).obj
  (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D)))))) → Fin n → b →₀ D :=
  fun x i ↦ Finsupp.ofSupportFinite (fun y => x.toFun y i) $
    Set.Finite.subset (Finsupp.finite_support x) fun y hy => by
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
        Function.mem_support, ne_eq, Finsupp.fun_support_eq, Finset.mem_coe,
        Finsupp.mem_support_iff] at hy ⊢
      contrapose! hy
      change x.toFun y = 0 at hy
      rw [hy]; rfl

noncomputable abbrev iso₄iso₄ (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D):
  ModuleCat.of A (b →₀ ((ModuleCat.restrictScalars iso₁.symm.toRingEquiv.symm.toRingHom).obj
  (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D))))) ⟶
  (ModuleCat.restrictScalars ↑iso₁.symm.toRingEquiv.symm).obj
    (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D (b →₀ D)))) :=
  ModuleCat.semilinearMapAddEquiv _ _ _ $
  { toFun := iso₄_toFun k A b M D n iso₁
    map_add' := fun x x' => funext fun i => Finsupp.ext fun y => rfl
    map_smul' := fun a x => funext fun i => Finsupp.ext fun y => show ∑ j : Fin n, _ = _ by
      erw [matrix_smul_vec_apply]
      erw [Finsupp.coe_finset_sum]
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
        RingEquiv.symm_symm, AlgEquiv.toRingEquiv_toRingHom, RingHom.toMonoidHom_eq_coe,
        OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
        ZeroHom.coe_mk, smul_eq_mul, Finsupp.ofSupportFinite, Finset.sum_apply]
      rfl }

noncomputable abbrev iso₄_invFun (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (v : ↑(ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D (b →₀ D))))):
  ↑((ModuleCat.restrictScalars iso₁.toRingEquiv.toRingHom).obj
  (ModuleCat.mk (R := (Matrix (Fin n) (Fin n) D)) (Matrix (Fin n) (Fin n) D))) → b →₀
  ↑((ModuleCat.restrictScalars iso₁.toRingEquiv.toRingHom).obj
  (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D)))) := fun x =>
  Finsupp.ofSupportFinite (fun y i =>  ∑ j : Fin n,  x i j * (v j).toFun y) $
  Set.Finite.subset (s := ⋃ j : Fin n, (v j).support) (Set.toFinite _)
    fun y hy => by
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv, smul_eq_mul,
        Function.mem_support, ne_eq, Set.mem_iUnion, Finset.mem_coe,
        Finsupp.mem_support_iff] at hy ⊢
      contrapose! hy
      refine funext fun i => ?_
      simp_rw [show ∀ i, (v i).toFun y = 0 from hy, mul_zero]
      simp only [Finset.sum_const_zero]
      rfl

noncomputable abbrev iso₄inv' (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D):
  (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D (b →₀ D)))) →
  ((ModuleCat.restrictScalars ↑iso₁.symm.toRingEquiv.symm.toRingHom).obj (ModuleCat.mk (Matrix (Fin n) (Fin n) D))) →ₗ[A]
  (ModuleCat.of A (b →₀ ((ModuleCat.restrictScalars iso₁.toRingEquiv.toRingHom).obj
  (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D)))))) := fun v => {
    toFun := iso₄_invFun k A b M D n iso₁ v
    map_add' := fun x y => Finsupp.ext fun z => funext fun i => by
      erw [Finsupp.add_apply]
      rw [Pi.add_apply]
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
        Finsupp.ofSupportFinite, Finsupp.coe_mk, iso₄_invFun]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      erw [Matrix.add_apply, add_mul]
    map_smul' := by
      rintro a (x : (ModuleCat.restrictScalars _).obj $ ModuleCat.of _ _)
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
        ModuleCat.restrictScalars.smul_def, RingEquiv.symm_symm,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, smul_eq_mul,
        RingHom.id_apply, iso₄_invFun]
      refine Finsupp.ext fun y => ?_
      erw [Finsupp.smul_apply]
      simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
      refine funext fun i => ?_
      erw [matrix_smul_vec_apply]
      simp only [RingEquiv.symm_symm, AlgEquiv.toRingEquiv_toRingHom,
        RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_coe, ZeroHom.coe_mk, smul_eq_mul]
      simp_rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl $ fun j _ ↦ Finset.sum_congr rfl $ fun k _ ↦ by rw [mul_assoc] }

noncomputable abbrev iso₄inv (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D):
  (ModuleCat.restrictScalars ↑iso₁.symm.toRingEquiv.symm).obj (ModuleCat.of
  (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D (b →₀ D)))) ⟶
  ModuleCat.of A (b →₀ ↑((ModuleCat.restrictScalars iso₁.toRingEquiv.toRingHom).obj
  (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D))))) :=
  ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction _
  { toFun := iso₄inv' k A b M D n iso₁
    map_add' := fun x x' => by
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv, iso₄_invFun]
      refine LinearMap.ext fun y => ?_
      erw [LinearMap.add_apply]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine Finsupp.ext fun z => ?_
      erw [Finsupp.add_apply]
      simp only [iso₄_invFun, Finsupp.ofSupportFinite, Finsupp.coe_mk]
      refine funext fun i => ?_
      erw [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      erw [Pi.add_apply]
      rw [show (x j + x' j).toFun z = (x j).toFun z + (x' j).toFun z from rfl, mul_add]
    map_smul' := fun m x => by
      dsimp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
        ModuleCat.restrictScalars.smul_def, RingHom.coe_coe, smul_eq_mul,
        AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, iso₄inv', iso₄_invFun]
      refine LinearMap.ext fun y => ?_
      change _ = (_ : _ →ₗ[_] _).toFun _
      erw [ModuleCat.CoextendScalars.smul_apply]
      simp only [iso₄_invFun, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finsupp.ext fun z => ?_
      simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
      refine funext fun i => ?_
      simp_rw [Matrix.mul_apply]
      change ∑ j : Fin n, y i j * ((∑ k : Fin n, m j k • x k : b →₀ _) z) = _
      simp_rw [Finsupp.coe_finset_sum]
      simp only [Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [smul_eq_mul, mul_assoc]; rfl }

lemma hom_inv_id_iso₄ (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D):
  iso₄iso₄ k A b M D n iso₁ ≫ iso₄inv k A b M D n iso₁ =
  𝟙 (ModuleCat.of A (b →₀ ((ModuleCat.restrictScalars iso₁.symm.toRingEquiv.symm.toRingHom).obj
    (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D)))))) := by
  ext x
  unfold iso₄iso₄ iso₄inv iso₄inv' iso₄_toFun iso₄_invFun
  simp only [ModuleCat.coe_comp, Function.comp_apply]
  rw [ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_apply]
  erw [ModuleCat.id_apply (M := (ModuleCat.of A (b →₀
    ((ModuleCat.restrictScalars iso₁.symm.toRingEquiv.symm.toRingHom).obj
    (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D D))))))) (m := x)]
  rw [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finsupp.ext fun y => ?_
  simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
  refine funext fun i => ?_
  simp_rw [Matrix.one_apply, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  erw [ModuleCat.semilinearMapAddEquiv_apply_apply]
  rfl

lemma inv_hom_id_iso₄ (b M D: Type v) (n : ℕ) [Inhabited (Fin n)] [DivisionRing D]
    [Algebra k D] [AddCommGroup M] [Module A M] (iso₁ : A ≃ₐ[k] Matrix (Fin n) (Fin n) D):
  iso₄inv k A b M D n iso₁ ≫ iso₄iso₄ k A b M D n iso₁ =
  𝟙 ((ModuleCat.restrictScalars iso₁.symm.toRingEquiv.symm.toRingHom).obj
    (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → ↑(ModuleCat.of D (b →₀ D))))) := by
  ext x
  unfold iso₄iso₄ iso₄inv iso₄inv' iso₄_toFun iso₄_invFun
  rw [ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_apply]
  erw [ModuleCat.id_apply (m := x)]
  rw [LinearMap.coe_mk, AddHom.coe_mk]
  refine funext fun y => ?_
  erw [ModuleCat.semilinearMapAddEquiv_apply_apply]
  rw [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finsupp.ext fun z => ?_
  simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
  simp_rw [Matrix.one_apply, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rfl

lemma directSum_simple_module_over_simple_ring
    (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module A S) (_ : IsSimpleModule A S)
      (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  obtain ⟨n, hn, D, inst1, inst2, ⟨iso₁⟩⟩ := Wedderburn_Artin_algebra_version k A
  letI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  let e₁ := moritaEquivalentToMatrix D (Fin n)
  let e₂ : ModuleCat A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm.toRingEquiv
  let e := e₂.trans e₁.symm
  let S := e.inverse.obj (ModuleCat.of D D)
  haveI : IsSimpleModule D (ModuleCat.of D D) := inferInstanceAs $ IsSimpleModule D D
  haveI : IsSimpleModule A S :=
    IsMoritaEquivalent.division_ring.IsSimpleModule.functor _ _ e.symm (ModuleCat.of D D)
  let M' := e.functor.obj (ModuleCat.of A M)
  obtain ⟨b, hb⟩ : Module.Free D M' := inferInstance
  refine ⟨S, inferInstance, inferInstance, inferInstance, b, ⟨?_⟩⟩
  let iso₂ : M' ≅ ModuleCat.of D (b →₀ D) := LinearEquiv.toModuleIso hb.repr
  let iso₃ : ModuleCat.of A M ≅ e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    e.unitIso.app (ModuleCat.of A M) ≪≫ (e.inverse.mapIso iso₂)
  let iso₄ :
      ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
      show ModuleCat.of A (b →₀ (ModuleCat.restrictScalars _).obj (ModuleCat.of _ _)) ≅
        (ModuleCat.restrictScalars _).obj (ModuleCat.of _ _) from
        { hom := iso₄iso₄ k A b M D n iso₁
          inv := iso₄inv k A b M D n iso₁
          hom_inv_id := hom_inv_id_iso₄ k A b M D n iso₁
          inv_hom_id := inv_hom_id_iso₄ k A b M D n iso₁ }
  exact iso₃ ≪≫ iso₄.symm |>.toLinearEquiv

lemma directSum_simple_module_over_simple_ring'
    (M : Type v) [AddCommGroup M] [Module A M]
    (S : Type v) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    ∃ (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  obtain ⟨T, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring k A M
  obtain ⟨iso'⟩ := linearEquiv_of_isSimpleModule_over_simple_ring k A S T
  exact ⟨ι, ⟨iso ≪≫ₗ Finsupp.mapRange.linearEquiv iso'.symm⟩⟩

lemma linearEquiv_iff_finrank_eq_over_simple_ring
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module k M] [Module k N]
    [IsScalarTower k A M] [IsScalarTower k A N]
    [Module.Finite A M] [Module.Finite A N] :

    Nonempty (M ≃ₗ[A] N) ↔
    FiniteDimensional.finrank k M = FiniteDimensional.finrank k N := by

  haveI : FiniteDimensional k M := Module.Finite.trans A M
  haveI : FiniteDimensional k N := Module.Finite.trans A N

  fconstructor
  · rintro ⟨iso⟩
    refine LinearEquiv.finrank_eq { iso with map_smul' := ?_ }
    intros a m
    simp only [AlgHom.toRingHom_eq_coe, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearMap.map_smul_of_tower, LinearEquiv.coe_coe, RingHom.id_apply]
  · intro h
    obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring k A M
    obtain ⟨ι', ⟨iso'⟩⟩ := directSum_simple_module_over_simple_ring' k A N S

    by_cases HS : Subsingleton S
    · letI : Unique S := ⟨⟨0⟩, fun x => Subsingleton.elim _ _⟩
      letI : Unique (ι →₀ S) := inferInstance
      letI : Unique (ι' →₀ S) := inferInstance
      let e : (ι →₀ S) ≃ₗ[A] (ι' →₀ S) :=
        { toFun := 0
          map_add' := by simp
          map_smul' := by simp
          invFun := 0
          left_inv := by
            intro x
            apply Subsingleton.elim
          right_inv := by
            intro x
            apply Subsingleton.elim }
      refine ⟨iso ≪≫ₗ e ≪≫ₗ iso'.symm⟩

    replace HS : Nontrivial S := not_subsingleton_iff_nontrivial.mp HS

    by_cases Hιι' : IsEmpty ι ∨ IsEmpty ι'
    · rcases Hιι' with (Hι|Hι')
      · letI : Unique (ι →₀ S) := inferInstance
        letI : Unique M := ⟨⟨0⟩, by
          intros a
          apply_fun iso using LinearEquiv.injective _
          apply Subsingleton.elim⟩
        have eq : FiniteDimensional.finrank k M = 0 := by
          rw [FiniteDimensional.finrank_eq_zero_iff]
          exact fun m => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
        have eq' : FiniteDimensional.finrank k N = 0 := by
          rw [← h, eq]
        haveI : Unique N := ⟨⟨0⟩, by
          rw [FiniteDimensional.finrank_zero_iff] at eq'
          intro n
          exact Subsingleton.elim _ _⟩
        refine ⟨⟨0, 0, fun x => Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩⟩
      · letI : Unique (ι' →₀ S) := inferInstance
        letI : Unique N := ⟨⟨0⟩, by
          intros a
          apply_fun iso' using LinearEquiv.injective _
          apply Subsingleton.elim⟩
        have eq : FiniteDimensional.finrank k N = 0 := by
          rw [FiniteDimensional.finrank_eq_zero_iff]
          exact fun m => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
        have eq' : FiniteDimensional.finrank k M = 0 := by
          rw [h, eq]
        haveI : Unique M := ⟨⟨0⟩, by
          rw [FiniteDimensional.finrank_zero_iff] at eq'
          intro n
          exact Subsingleton.elim _ _⟩
        refine ⟨⟨0, 0, fun x => Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩⟩

    push_neg at Hιι'
    rw [not_isEmpty_iff, not_isEmpty_iff] at Hιι'
    obtain ⟨Hι, -⟩ := Hιι'

    letI := Module.compHom S (Algebra.ofId k A).toRingHom
    let ISO : M ≃ₗ[k] ι →₀ S :=
    { iso with
      map_smul' := by
        intros a m
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply]
        rw [algebra_compatible_smul A]
        change iso (algebraMap k A a • _) = algebraMap k A a • _
        rw [map_smul] }
    have eq := LinearEquiv.finrank_eq ISO

    let ISO' : N ≃ₗ[k] ι' →₀ S :=
    { iso' with
      map_smul' := by
        intros a m
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply]
        rw [algebra_compatible_smul A]
        change iso' (algebraMap k A a • _) = algebraMap k A a • _
        rw [map_smul] }
    have eq' := LinearEquiv.finrank_eq ISO'
    have EQ : FiniteDimensional.finrank k (ι →₀ S) = FiniteDimensional.finrank k (ι' →₀ S) := by
      rw [← eq, h, eq']

    haveI : Module.Finite k (ι →₀ S) := Module.Finite.equiv ISO
    haveI : Module.Finite k (ι' →₀ S) := Module.Finite.equiv ISO'
    haveI : Module.Finite k S := by
      suffices : IsNoetherian k S
      · infer_instance
      rw [IsNoetherian.iff_rank_lt_aleph0]
      apply_fun ((↑) : ℕ → Cardinal) at eq
      rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp] at eq
      have ineq : Module.rank k M < Cardinal.aleph0 := by
        rw [Module.rank_lt_alpeh0_iff]; infer_instance
      rw [eq] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_right (Module.rank k S) (Cardinal.mk ι)
        (by rw [Cardinal.mk_ne_zero_iff]; infer_instance)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq

    haveI : Fintype ι := by
      refine (@Cardinal.lt_aleph0_iff_fintype ι).1 ?_ |>.some
      apply_fun ((↑) : ℕ → Cardinal) at eq
      rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp] at eq
      have ineq : Module.rank k M < Cardinal.aleph0 := by
        rw [Module.rank_lt_alpeh0_iff]; infer_instance
      rw [eq] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι) (Module.rank k S)
        (by
          suffices : 0 < Module.rank k S
          · exact Ne.symm (ne_of_lt this)
          apply rank_pos)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq

    haveI : Fintype ι' := by
      refine (@Cardinal.lt_aleph0_iff_fintype ι').1 ?_ |>.some
      apply_fun ((↑) : ℕ → Cardinal) at eq'
      rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp] at eq'
      have ineq : Module.rank k N < Cardinal.aleph0 := by
        rw [Module.rank_lt_alpeh0_iff]; infer_instance
      rw [eq'] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι') (Module.rank k S)
        (by
          suffices : 0 < Module.rank k S
          · exact Ne.symm (ne_of_lt this)
          apply rank_pos)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq

    rw [FiniteDimensional.finrank_finsupp,  FiniteDimensional.finrank_finsupp] at EQ
    simp only [Cardinal.lift_id] at EQ
    simp only [mul_eq_mul_right_iff] at EQ
    replace EQ := EQ.resolve_right
      (by have := FiniteDimensional.finrank_pos (R := k) (M := S); omega)
    rw [Fintype.card_eq] at EQ
    obtain ⟨e⟩ := EQ
    let E : (ι →₀ S) ≃ₗ[A] (ι' →₀ S) :=
      { Finsupp.equivCongrLeft e with
        map_add' := by intros a b; ext; simp
        map_smul' := by intros a b; ext; simp }
    refine ⟨iso ≪≫ₗ E ≪≫ₗ iso'.symm⟩

/--
074E (3) first part
-/
lemma simple_mod_of_wedderburn (n : ℕ) [NeZero n]
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
    IsSimpleModule A (Fin n → D) := by
  letI : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom

  let e : ModuleCat.{v} A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv wdb.toRingEquiv.symm

  have inst1 : IsSimpleModule (Matrix (Fin n) (Fin n) D) (Fin n → D) := by
    haveI : IsSimpleModule D (ModuleCat.of D D) := inferInstanceAs $ IsSimpleModule D D
    exact IsMoritaEquivalent.division_ring.IsSimpleModule.functor D (Matrix (Fin n) (Fin n) D)
      (moritaEquivalentToMatrix D (Fin n)) (ModuleCat.of D D)

  have : IsSimpleModule (Matrix (Fin n) (Fin n) D)
    (ModuleCat.of (Matrix (Fin n) (Fin n) D) $ Fin n → D) := inst1

  exact IsMoritaEquivalent.division_ring.IsSimpleModule.functor (Matrix (Fin n) (Fin n) D) A
    e.symm (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → D))

noncomputable section wedderburn

abbrev endCatEquiv (n : ℕ) [NeZero n]
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    [Module A (Fin n → D)] (smul_def : ∀ (a : A) (v : Fin n → D), a • v = wdb a • v)
    [IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D)] [IsScalarTower k A (Fin n → D)]
    [SMulCommClass A k (Fin n → D)]  :
  Module.End A (Fin n → D) ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  AlgEquiv.ofAlgHom {
    toFun := fun f ↦ {
      toFun := f
      map_add' := f.map_add
      map_smul' := fun a v => by
        simp only [RingHom.id_apply]
        rw [show a • v = wdb.symm a • v by simp [smul_def], map_smul, smul_def]
        simp
    }
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    commutes' := by intros; ext; simp }
  { toFun := fun f => {
      toFun := f
      map_add' := f.map_add
      map_smul' := fun a b => by
        simp only [smul_def, LinearMapClass.map_smul, RingHom.id_apply]
    }
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    commutes' := by intros; ext; simp }
  (AlgHom.ext $ fun _ => LinearMap.ext $ fun _ => by rfl)
  (AlgHom.ext $ fun _ => LinearMap.ext $ fun _ => by rfl)
    -- AlgEquiv.ofAlgHom
    --   { toFun := fun f =>
    --     { f with
    --       map_smul' := fun a v => by
    --         simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
    --         rw [show a • v = wdb.symm a • v by change a • v = wdb (wdb.symm a) • v; simp, map_smul]
    --         change wdb (wdb.symm a) • f v = _
    --         simp }
    --     map_one' := by rfl
    --     map_mul' := by intros; ext; rfl
    --     map_zero' := by rfl
    --     map_add' := by intros; ext; rfl
    --     commutes' := by intros; ext; simp }
    --   { toFun := fun f =>
    --     { f with
    --       map_smul' := fun a b => by
    --         simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
    --         change f (wdb a • b) = wdb a • f b
    --         rw [map_smul] }
    --     map_one' := by rfl
    --     map_mul' := by intros; ext; rfl
    --     map_zero' := by rfl
    --     map_add' := by intros; ext; rfl
    --     commutes' := by intros; ext; simp }
    --   (AlgHom.ext $ fun _ => LinearMap.ext $ fun _ => by rfl)
    --   (AlgHom.ext $ fun _ => LinearMap.ext $ fun _ => by rfl)

#exit
set_option maxHeartbeats 500000 in
/--
074E (3) first part
-/
def end_simple_mod_of_wedderburn (n : ℕ) [NeZero n]
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
    -- these should be in Morita file
    have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
    { smul_assoc := fun a b x => by
        ext i
        simp only [matrix_smul_vec_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_mul_assoc,
          Pi.smul_apply, Finset.smul_sum] }
    letI _ : IsScalarTower k A (Fin n → D) :=
    { smul_assoc := fun a b x => by
        change wdb (a • b) • x = _
        rw [map_smul, Algebra.smul_def, mul_smul]
        rw [algebraMap_smul]
        rfl }
    letI _ : SMulCommClass A k (Fin n → D) :=
      { smul_comm := fun a b x => by
          change wdb a • b • x = b • wdb a • x
          ext i
          simp only [matrix_smul_vec_apply, Pi.smul_apply, smul_eq_mul, Algebra.mul_smul_comm,
            Finset.smul_sum] }
    Module.End A (Fin n → D) ≃ₐ[k] Dᵐᵒᵖ := by

  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc := fun a b x => by
      ext i
      simp only [matrix_smul_vec_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_mul_assoc,
        Pi.smul_apply, Finset.smul_sum] }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc := fun a b x => by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm := fun a b x => by
        change wdb a • b • x = b • wdb a • x
        ext i
        simp only [matrix_smul_vec_apply, Pi.smul_apply, smul_eq_mul, Algebra.mul_smul_comm,
          Finset.smul_sum] }

  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom]

  let E := moritaEquivalentToMatrix D (Fin n)

  haveI :  E.functor.Additive := {}
  haveI :  E.inverse.Additive := CategoryTheory.Equivalence.inverse_additive E

  let e₁ : Module.End A (Fin n → D) ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
    endCatEquiv k A n D wdb

  let e₂ : Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) ≃ₐ[k] Module.End D D :=
    AlgEquiv.ofAlgHom
    { toFun := fun (f : End (ModuleCat.of _ _)) => show End (ModuleCat.of D D) from
        E.unit.app (ModuleCat.of D D) ≫ E.inverse.map f ≫ E.unitInv.app ((ModuleCat.of D D))
      map_one' := by
        simp only [Functor.comp_obj, smul_eq_mul]
        rw [show (1 : Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D)) =
          𝟙 (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → D)) by rfl]
        erw [E.inverse.map_id]
        rw [Category.id_comp]
        simp only [Iso.hom_inv_id_app, Functor.id_obj]
        rfl
      map_mul' := fun (f g : End (ModuleCat.of _ _)) => by
        simp only [Functor.comp_obj, smul_eq_mul]
        rw [show f * g = g ≫ f by rfl, E.inverse.map_comp]
        simp only [smul_eq_mul, Category.assoc]
        change _ = _ ≫ _
        aesop_cat
      map_zero' := by
        simp only [Functor.comp_obj, smul_eq_mul, Functor.map_zero, Limits.zero_comp,
          Limits.comp_zero]
      map_add' := fun (f g : End (ModuleCat.of _ _)) => by
        simp only [Functor.comp_obj, smul_eq_mul]
        rw [E.inverse.map_add]
        simp only [Preadditive.add_comp, Preadditive.comp_add]
      commutes' := fun a => by
        simp only [Functor.comp_obj, smul_eq_mul]
        ext
        rw [Module.algebraMap_end_eq_smul_id, Module.algebraMap_end_eq_smul_id]
        erw [LinearMap.smul_apply]
        rw [LinearMap.id_apply]
        rw [Algebra.smul_def]
        erw [mul_one]
        erw [comp_apply, comp_apply]
        simp only [moritaEquivalentToMatrix, fromModuleCatOverMatrix_obj,
          Equivalence.Equivalence_mk'_unitInv, Iso.symm_inv, matrix.unitIso_hom,
          toModuleCatOverMatrix_obj, Equivalence.Equivalence_mk'_unit, Iso.symm_hom,
          matrix.unitIso_inv, E]
        erw [matrix.unitIsoHom_app_apply]
        simp only [toModuleCatOverMatrix_obj, fromModuleCatOverMatrix, Functor.id_obj]
        set lhs := _; change lhs = _
        rw [show lhs = ∑ j : Fin n,
          algebraMap k (Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D)) a
            (((matrix.unitIsoInv D (Fin n)).app (ModuleCat.of D D)) (1 : D)).1 j by rfl]
        simp only [toModuleCatOverMatrix_obj, Functor.id_obj, Functor.comp_obj,
          fromModuleCatOverMatrix_obj, Module.algebraMap_end_apply, Pi.smul_apply]
        rw [← Finset.smul_sum]
        congr 1
        set lhs := _; change lhs = _
        rw [show lhs = ∑ j : Fin n, Function.update (0 : Fin n → D) default 1 j by
          refine Finset.sum_congr rfl fun j _ => ?_
          erw [matrix.unitIsoInv_app_apply_coe]]
        simp only [Fin.default_eq_zero]
        rw [Finset.sum_eq_single_of_mem (a := 0) (h := Finset.mem_univ _)]
        · simp only [Function.update_same]
        · intro i _ h
          rw [Function.update_noteq (h := h)]
          rfl
          }
    { toFun := fun (f : End (ModuleCat.of _ _)) =>
        show End (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → D)) from E.functor.map f
      map_one' := by
        simp only [Functor.comp_obj, smul_eq_mul]
        rw [show (1 : Module.End D D) =
          𝟙 (ModuleCat.of D D) by rfl]
        erw [E.functor.map_id]
        rfl
      map_mul' := fun (f g : End (ModuleCat.of _ _)) => by
        simp only [Functor.comp_obj, smul_eq_mul]
        rw [show f * g = g ≫ f by rfl, E.functor.map_comp]
        rfl
      map_zero' := by
        simp only [Functor.comp_obj, smul_eq_mul, Functor.map_zero, Limits.zero_comp,
          Limits.comp_zero]
      map_add' := fun (f g : End (ModuleCat.of _ _)) => by
        simp only [Functor.comp_obj, smul_eq_mul]
        rw [E.functor.map_add]
      commutes' := fun a => by
        simp only [moritaEquivalentToMatrix_functor, toModuleCatOverMatrix, E]
        ext x
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine funext fun j => ?_
        rfl }
    (by
      simp only [smul_eq_mul, Functor.comp_obj]
      ext d
      simp only [AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Function.comp_apply, Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
        Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc,
        AlgHom.coe_id, id_eq])
    (by
      simp only [smul_eq_mul, Functor.comp_obj]
      ext f v i
      simp only [AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Function.comp_apply, Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj,
        Functor.id_obj, Category.assoc, Equivalence.functor_unit_comp_assoc, AlgHom.coe_id, id_eq]
      erw [E.counitInv_functor_comp (X := ModuleCat.of D D)]
      rfl)
  refine e₁.trans $ e₂.trans $ AlgEquiv.symm $ AlgEquiv.ofRingEquiv (f := mopEquivEnd _) ?_
  intro a
  simp only [mopEquivEnd, mopToEnd, MulOpposite.algebraMap_apply, RingEquiv.coe_ofBijective,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
  ext
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Module.algebraMap_end_apply]
  rw [Algebra.smul_def, mul_one]

end wedderburn

lemma end_simple_mod_of_wedderburn' (n : ℕ) [NeZero n]
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    Nonempty $ Module.End A M ≃ₐ[k] Dᵐᵒᵖ := by
  let e := end_simple_mod_of_wedderburn k A n D wdb
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc := fun a b x => by
      ext i
      simp only [matrix_smul_vec_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_mul_assoc,
        Pi.smul_apply, Finset.smul_sum] }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc := fun a b x => by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm := fun a b x => by
        change wdb a • b • x = b • wdb a • x
        ext i
        simp only [matrix_smul_vec_apply, Pi.smul_apply, smul_eq_mul, Algebra.mul_smul_comm,
          Finset.smul_sum] }
  haveI : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A n D wdb
  obtain ⟨iso⟩ := linearEquiv_of_isSimpleModule_over_simple_ring k A M (Fin n → D)
  refine Nonempty.intro $ AlgEquiv.trans (AlgEquiv.ofLinearEquiv ?_ ?_ ?_) e
  · exact LinearEquiv.ofLinear
      { toFun := fun f => iso.toLinearMap ∘ₗ f ∘ₗ iso.symm.toLinearMap
        map_add' := fun f g => by ext; simp
        map_smul' := fun a f => by
          ext v i
          simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
            AlgEquiv.toRingEquiv_toRingHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
            Function.comp_apply, LinearMap.smul_apply, RingHom.id_apply, Pi.smul_apply]
          rw [algebra_compatible_smul A, iso.map_smul]
          rw [algebraMap_smul]
          rfl }
      { toFun := fun f => iso.symm.toLinearMap ∘ₗ f ∘ₗ iso.toLinearMap
        map_add' := fun f g => by ext; simp
        map_smul' := fun a f => by
          ext m
          simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
            AlgEquiv.toRingEquiv_toRingHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
            Function.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
          rw [algebra_compatible_smul A, iso.symm.map_smul]
          rw [algebraMap_smul] }
      (by ext; simp) (by ext; simp)
  · ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, Pi.smul_apply, smul_eq_mul, id_eq, Matrix.smul_apply,
      eq_mpr_eq_cast, LinearEquiv.ofLinear_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.one_apply,
      LinearEquiv.apply_symm_apply]
  · intros f g
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, Pi.smul_apply, smul_eq_mul, id_eq, Matrix.smul_apply,
      eq_mpr_eq_cast, LinearEquiv.ofLinear_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.mul_apply,
      LinearEquiv.symm_apply_apply]

instance end_simple_mod_finite
    (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    FiniteDimensional k (Module.End A M) := by
  obtain ⟨n, hn, D, _, _, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version k A
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨iso⟩ := end_simple_mod_of_wedderburn' k A n D e M
  let E : Dᵐᵒᵖ ≃ₗ[k] D := LinearEquiv.ofLinear
    { toFun := MulOpposite.unop
      map_add' := by simp
      map_smul' := by simp }
    { toFun := MulOpposite.op
      map_add' := by simp
      map_smul' := by simp }
    (by ext; simp) (by ext; simp)
  have : Module.Finite k D := by
    haveI inst1 : Module.Finite k (Matrix (Fin n) (Fin n) D) := e.toLinearEquiv.finiteDimensional
    rw [← Module.rank_lt_alpeh0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1

  have : FiniteDimensional k Dᵐᵒᵖ := E.symm.finiteDimensional
  refine iso.symm.toLinearEquiv.finiteDimensional


lemma Wedderburn_Artin_uniqueness₀
    (n n' : ℕ) [NeZero n] [NeZero n']
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (D' : Type v) [DivisionRing D'] [Algebra k D'] (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    Nonempty $ D ≃ₐ[k] D' := by
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc := fun a b x => by
      ext i
      simp only [matrix_smul_vec_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_mul_assoc,
        Pi.smul_apply, Finset.smul_sum] }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc := fun a b x => by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm := fun a b x => by
        change wdb a • b • x = b • wdb a • x
        ext i
        simp only [matrix_smul_vec_apply, Pi.smul_apply, smul_eq_mul, Algebra.mul_smul_comm,
          Finset.smul_sum] }
  haveI : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A n D wdb
  have ⟨iso⟩ := end_simple_mod_of_wedderburn' k A n D wdb (Fin n → D)
  have ⟨iso'⟩ := end_simple_mod_of_wedderburn' k A n' D' wdb' (Fin n → D)
  let e := iso.symm.trans iso'
  exact Nonempty.intro {
    toFun := fun x => e (MulOpposite.op x) |>.unop
    invFun := fun x => e.symm (MulOpposite.op x) |>.unop
    left_inv := fun x => by simp
    right_inv := fun x => by simp
    map_mul' := fun x y => by simp
    map_add' := fun x y => by simp
    commutes' := fun x => by
      simp only
      have := e.commutes x
      simp only [MulOpposite.algebraMap_apply] at this
      rw [this]
      simp
  }

lemma Wedderburn_Artin_uniqueness₁
    (n n' : ℕ) [NeZero n] [NeZero n']
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (D' : Type v) [DivisionRing D'] [Algebra k D'] (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    n = n' := by
  have ⟨iso⟩ := Wedderburn_Artin_uniqueness₀ k A n n' D wdb D' wdb'
  let e : Matrix (Fin n) (Fin n) D ≃ₐ[k] Matrix (Fin n') (Fin n') D :=
    wdb.symm.trans (wdb'.trans $ AlgEquiv.mapMatrix iso.symm)

  haveI : Module.Finite k D := by
    haveI inst1 : Module.Finite k (Matrix (Fin n) (Fin n) D) := wdb.toLinearEquiv.finiteDimensional
    rw [← Module.rank_lt_alpeh0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1

  have eq1 := FiniteDimensional.finrank_matrix D (Fin n) (Fin n)
  have eq2 := FiniteDimensional.finrank_matrix D (Fin n') (Fin n')
  simp only [Fintype.card_fin] at eq1 eq2
  have eq11 :
      FiniteDimensional.finrank k (Matrix (Fin n) (Fin n) D) =
      n * n * FiniteDimensional.finrank k D := by
    rw [← FiniteDimensional.finrank_mul_finrank k D (Matrix (Fin n) (Fin n) D), eq1]
    ring
  have eq21 : FiniteDimensional.finrank k (Matrix (Fin n') (Fin n') D) =
      n' * n' * FiniteDimensional.finrank k D := by
    rw [← FiniteDimensional.finrank_mul_finrank k D (Matrix (Fin n') (Fin n') D), eq2]
    ring
  have eq3 : n * n * FiniteDimensional.finrank k D = n' * n' * FiniteDimensional.finrank k D := by
    rw [← eq11, ← eq21]
    exact LinearEquiv.finrank_eq e
  simp only [mul_eq_mul_right_iff] at eq3
  replace eq3 := eq3.resolve_right (fun rid => by
    rw [FiniteDimensional.finrank_zero_iff] at rid
    simpa using rid.elim 0 1)
  simpa [← pow_two] using eq3

end simple
