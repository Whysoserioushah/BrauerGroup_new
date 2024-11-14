import BrauerGroup.Wedderburn
import BrauerGroup.CoproductModuleCat

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Algebra.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Dimension.Free

open CategoryTheory DirectSum

universe u v w

section simple

/--
Stack 074E (1)
-/
lemma linearEquiv_of_isSimpleModule_over_simple_ring
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]
    [FiniteDimensional k A] (M N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [IsSimpleModule A M] [IsSimpleModule A N] : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨n, hn, D, _, _, ⟨iso₁⟩⟩ := Wedderburn_Artin_algebra_version k A
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

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [FiniteDimensional k A]

lemma directSum_simple_module_over_simple_ring
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]
    [FiniteDimensional k A] (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module A S) (_ : IsSimpleModule A S)
      (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  classical
  obtain ⟨n, hn, D, inst1, inst2, ⟨iso₁⟩⟩ := Wedderburn_Artin_algebra_version k A
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
  let iso₄₀ :
      ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      ModuleCat.of A (⨁ (i : b), e.inverse.obj (ModuleCat.of D D)) :=
    LinearEquiv.toModuleIso (finsuppLequivDFinsupp _)
  let iso₄₁ :
    ModuleCat.of A (⨁ (i : b), e.inverse.obj (ModuleCat.of D D)) ≅
    ∐ fun i : b ↦ ModuleCat.of A (e.inverse.obj (ModuleCat.of D D)) :=
        Iso.symm (ModuleCat.coprodIsoDirectSum _)
  let iso₄₂ :
    (∐ fun i : b ↦ ModuleCat.of A (e.inverse.obj (ModuleCat.of D D))) ≅
    e.inverse.obj (∐ fun i : b ↦ ModuleCat.of D D) :=
      { hom := Limits.Sigma.desc fun i ↦ e.inverse.map <|
          Limits.Sigma.ι (fun i : b ↦ ModuleCat.of D D) i
        inv := -- e.inverse.map (Limits.Sigma.desc fun i ↦ _) ≫ e.unitInv.app _
          e.symm.toAdjunction.homEquiv _ _ |>.symm
            (Limits.Sigma.desc fun i ↦
              e.symm.toAdjunction.homEquiv _ _ <| Limits.Sigma.ι
                (fun i : b ↦ e.inverse.obj <| ModuleCat.of D D) i)
        hom_inv_id := by
          ext i : 1
          simp only [ModuleCat.of_coe, Equivalence.symm_inverse, Equivalence.symm_functor,
            Adjunction.homEquiv, Functor.comp_obj, Equivalence.toAdjunction,
            show e.symm.unit = e.counitInv by aesop_cat,
            show e.symm.counit = e.unitInv by aesop_cat, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, ←
            Category.assoc, Limits.colimit.ι_desc, Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app, ←
            Functor.map_comp, Category.comp_id]
          simp only [Functor.map_comp, Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
            Equivalence.inverse_counitInv_comp_assoc, Category.assoc, Iso.hom_inv_id_app,
            Category.comp_id]
        inv_hom_id := by
          apply_fun (e.symm.toAdjunction.homEquiv _ _)
          apply Limits.Sigma.hom_ext
          intro i
          simp only [Equivalence.symm_inverse, Equivalence.symm_functor, Adjunction.homEquiv,
            Functor.comp_obj, Equivalence.toAdjunction_unit,
            show e.symm.unit = e.counitInv by aesop_cat, Equivalence.toAdjunction_counit,
            show e.symm.counit = e.unitInv by aesop_cat, ModuleCat.of_coe, Equiv.coe_fn_mk,
            Equiv.coe_fn_symm_mk, Category.assoc, Functor.map_comp, Equivalence.fun_inv_map,
            Functor.id_obj, Equivalence.counitInv_functor_comp_assoc, Iso.inv_hom_id_app_assoc,
            Limits.colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Limits.Cofan.mk_pt,
            Limits.Cofan.mk_ι_app, CategoryTheory.Functor.map_id, Category.comp_id]
          simp only [← Functor.map_comp, Limits.colimit.ι_desc, Limits.Cofan.mk_pt,
            Limits.Cofan.mk_ι_app, Equivalence.fun_inv_map, Functor.comp_obj, Functor.id_obj,
            Iso.inv_hom_id_app_assoc]  }
  let iso₄₃ : e.inverse.obj (∐ fun i : b ↦ ModuleCat.of D D) ≅
    e.inverse.obj (ModuleCat.of D (⨁ i : b, D)) :=
    e.inverse.mapIso (ModuleCat.coprodIsoDirectSum _)
  let iso₄₄ : e.inverse.obj (ModuleCat.of D (⨁ i : b, D)) ≅
    e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    e.inverse.mapIso (LinearEquiv.toModuleIso (finsuppLequivDFinsupp _).symm)

  let iso₄ :
      ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    iso₄₀ ≪≫ iso₄₁ ≪≫ iso₄₂ ≪≫ iso₄₃ ≪≫ iso₄₄
  exact iso₃ ≪≫ iso₄.symm |>.toLinearEquiv

lemma directSum_simple_module_over_simple_ring'
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]
    [FiniteDimensional k A] (M : Type v) [AddCommGroup M] [Module A M]
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
    Module.finrank k M = Module.finrank k N := by

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
        have eq : Module.finrank k M = 0 := by
          rw [Module.finrank_eq_zero_iff]
          exact fun m => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
        have eq' : Module.finrank k N = 0 := by
          rw [← h, eq]
        haveI : Unique N := ⟨⟨0⟩, by
          rw [Module.finrank_zero_iff] at eq'
          intro n
          exact Subsingleton.elim _ _⟩
        refine ⟨⟨0, 0, fun x => Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩⟩
      · letI : Unique (ι' →₀ S) := inferInstance
        letI : Unique N := ⟨⟨0⟩, by
          intros a
          apply_fun iso' using LinearEquiv.injective _
          apply Subsingleton.elim⟩
        have eq : Module.finrank k N = 0 := by
          rw [Module.finrank_eq_zero_iff]
          exact fun m => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
        have eq' : Module.finrank k M = 0 := by
          rw [h, eq]
        haveI : Unique M := ⟨⟨0⟩, by
          rw [Module.finrank_zero_iff] at eq'
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
    have EQ : Module.finrank k (ι →₀ S) = Module.finrank k (ι' →₀ S) := by
      rw [← eq, h, eq']

    haveI : Module.Finite k (ι →₀ S) := Module.Finite.equiv ISO
    haveI : Module.Finite k (ι' →₀ S) := Module.Finite.equiv ISO'
    haveI : Module.Finite k S := by
      suffices IsNoetherian k S from inferInstance
      rw [IsNoetherian.iff_rank_lt_aleph0]
      apply_fun ((↑) : ℕ → Cardinal) at eq
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank, rank_finsupp] at eq
      have ineq : Module.rank k M < Cardinal.aleph0 := by
        rw [Module.rank_lt_aleph0_iff]; infer_instance
      rw [eq] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_right (Module.rank k S) (Cardinal.mk ι)
        (by rw [Cardinal.mk_ne_zero_iff]; infer_instance)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq

    haveI : Fintype ι := by
      refine (@Cardinal.lt_aleph0_iff_fintype ι).1 ?_ |>.some
      apply_fun ((↑) : ℕ → Cardinal) at eq
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank, rank_finsupp] at eq
      have ineq : Module.rank k M < Cardinal.aleph0 := by
        rw [Module.rank_lt_aleph0_iff]; infer_instance
      rw [eq] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι) (Module.rank k S)
        (by
          suffices 0 < Module.rank k S by exact Ne.symm (ne_of_lt this)
          apply rank_pos)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq

    haveI : Fintype ι' := by
      refine (@Cardinal.lt_aleph0_iff_fintype ι').1 ?_ |>.some
      apply_fun ((↑) : ℕ → Cardinal) at eq'
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank, rank_finsupp] at eq'
      have ineq : Module.rank k N < Cardinal.aleph0 := by
        rw [Module.rank_lt_aleph0_iff]; infer_instance
      rw [eq'] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι') (Module.rank k S)
        (by
          suffices 0 < Module.rank k S from
            Ne.symm (ne_of_lt this)
          apply rank_pos)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq

    rw [Module.finrank_finsupp,  Module.finrank_finsupp] at EQ
    simp only [Cardinal.lift_id] at EQ
    simp only [mul_eq_mul_right_iff] at EQ
    replace EQ := EQ.resolve_right
      (by have := Module.finrank_pos (R := k) (M := S); omega)
    rw [Fintype.card_eq] at EQ
    obtain ⟨e⟩ := EQ
    let E : (ι →₀ S) ≃ₗ[A] (ι' →₀ S) :=
      { Finsupp.equivCongrLeft e with
        map_add' := by intros a b; ext; simp
        map_smul' := by intros a b; ext; simp }
    refine ⟨iso ≪≫ₗ E ≪≫ₗ iso'.symm⟩

omit [IsSimpleRing A] [FiniteDimensional k A] in
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
    endCatEquiv k A n D wdb $ fun _ _ => rfl

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
    rw [← Module.rank_lt_aleph0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1

  have : FiniteDimensional k Dᵐᵒᵖ := E.symm.finiteDimensional
  refine iso.symm.toLinearEquiv.finiteDimensional

instance (D : Type v) [DivisionRing D] : Module.Finite Dᵐᵒᵖ D := by
  rw [Module.finite_def]
  refine ⟨{1}, eq_top_iff.2 fun x _ => ?_⟩
  simp only [Finset.coe_singleton]
  rw [show x = (MulOpposite.op x : Dᵐᵒᵖ) • 1 by simp]
  exact Submodule.smul_mem _ _ $ Submodule.subset_span rfl

noncomputable def pow_basis  (n : ℕ) [NeZero n] (D : Type v) [DivisionRing D] :
    Basis (Fin n) Dᵐᵒᵖ (Fin n → D) :=
  .mk (v := fun i => Pi.single i 1)
    (by
      rw [linearIndependent_iff]
      intro c hc
      ext i
      replace hc := congr_fun hc i
      simpa only [Finsupp.linearCombination, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
        LinearMap.id_coe, id_eq, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
        MulOpposite.smul_eq_mul_unop, one_mul, smul_zero, Finset.sum_ite_eq,
        Finsupp.mem_support_iff, ne_eq, Pi.zero_apply, ite_eq_right_iff,
        MulOpposite.unop_eq_zero_iff, _root_.not_imp_self, Finsupp.coe_zero] using hc )
    (by
      rintro v -
      have eq1 : v = ∑ i : Fin n, (MulOpposite.op $ v i) • Pi.single i 1 := by
        ext i
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul, smul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ↓reduceIte]
      rw [eq1]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ $ Submodule.subset_span ?_
      simp)

instance (M : Type v) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    Algebra k (Module.End (Module.End A M) M) where
  toFun a :=
    { toFun := fun m => a • m
      map_add' := by simp only [smul_add, implies_true]
      map_smul' := by
        simp only [LinearMap.smul_def, RingHom.id_apply, LinearMap.map_smul_of_tower,
          implies_true] }
  map_one' := by ext; simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply]
  map_mul' := by
    intros; ext
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, LinearMap.map_smul_of_tower]
    rw [mul_comm, mul_smul]
  map_zero' := by ext; simp only [zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  map_add' := by
    intros; ext
    simp only [add_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  commutes' := by
    intros r f
    ext m
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    let s : Module.End A M :=
    { toFun := fun x => r • x
      map_add' := by simp
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
        congr 1
        exact Algebra.commutes r a }
    rw [show r • m = s • m by rfl, f.map_smul]
    rfl
  smul r f :=
  { toFun := fun m => f $ r • m
    map_add' := by simp
    map_smul' := by
      intro g m
      simp only [LinearMap.smul_def, RingHom.id_apply]
      let s : Module.End A M :=
      { toFun := fun x => r • x
        map_add' := by simp
        map_smul' := fun a x => by
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
          congr 1
          exact Algebra.commutes r a }
      change f (s • g m) = g (f $ s • m)
      rw [f.map_smul, f.map_smul]
      simp only [LinearMap.smul_def, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul_of_tower,
        s]
      change r • f (g • m) = _
      rw [f.map_smul]
      simp }
  smul_def' := by
    intro r f
    ext m
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    let s : Module.End A M :=
      { toFun := fun x => r • x
        map_add' := by simp
        map_smul' := fun a x => by
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
          congr 1
          exact Algebra.commutes r a }
    change _ = s • f m
    rw [← f.map_smul]
    rfl

omit [IsSimpleRing A] in
lemma exists_gen (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] :
    ∃ m : M, m ≠ 0 ∧ ∀ m', ∃ a : A, m' = a • m := by
    have i : Submodule.IsPrincipal (⊤ : Submodule A M) := inferInstance

    refine ⟨i.1.choose, ?_, fun m => by
      classical
      have : m ∈ Submodule.span A {i.1.choose} := by
        rw [← i.1.choose_spec]; trivial
      rw [Submodule.mem_span_singleton] at this
      simpa [Eq.comm]⟩
    intro h
    have := i.1.choose_spec
    rw [h] at this
    simp only [Submodule.span_zero_singleton, top_ne_bot] at this

noncomputable def gen (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M]: M :=
    (exists_gen A M).choose

omit [IsSimpleRing A] in
lemma gen_ne_zero (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    gen A M ≠ 0 := (exists_gen A M).choose_spec.1

omit [IsSimpleRing A] in
lemma gen_spec (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] (m' : M) :
    ∃ a : A, m' = a • gen A M := (exists_gen A M).choose_spec.2 m'

@[simps]
def toEndEnd (M : Type v) [AddCommGroup M] [Module A M] : A →ₗ[A] Module.End (Module.End A M) M where
  toFun a := DistribMulAction.toLinearMap _ _ a
  map_add' := by intros; ext; simp [add_smul]
  map_smul' := by intros; ext; simp [mul_smul]


def toEndEndAlgHom (M : Type v) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    A →ₐ[k] Module.End (Module.End A M) M where
  __ := toEndEnd A M
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_smul]
  map_zero' := by ext; simp
  commutes' a := by ext; simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, toEndEnd_apply,
    DistribMulAction.toLinearMap_apply, algebraMap_smul]; rfl

omit [FiniteDimensional k A] in
lemma toEndEnd_injective
    (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Function.Injective (toEndEnd A M) := by
  apply IsSimpleRing.injective_ringHom_or_subsingleton_codomain
    (toEndEndAlgHom k A M).toRingHom |>.resolve_right ?_
  intro h
  have eq : 1 ∈ TwoSidedIdeal.ker (toEndEndAlgHom k A M) := by
    simp only [TwoSidedIdeal.mem_ker, map_one]
    exact Subsingleton.elim _ _
  simp only [TwoSidedIdeal.mem_ker, map_one] at eq
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  have eq' := congr($eq (gen A M))
  simp only [LinearMap.one_apply, LinearMap.zero_apply] at eq'
  exact gen_ne_zero A M eq'

class IsBalanced (M : Type v) [AddCommGroup M] [Module A M] : Prop where
  surj : Function.Surjective (toEndEnd A M)

instance : IsBalanced A A where
  surj f := ⟨f 1, by
    ext x
    simp only [toEndEnd_apply, DistribMulAction.toLinearMap_apply, smul_eq_mul]
    let X : Module.End A A :=
      { toFun := fun y => y * x
        map_add' := by simp [add_mul]
        map_smul' := by simp [mul_assoc] }
    have eq1 := f.map_smul X 1
    simp only [LinearMap.smul_def, LinearMap.coe_mk, AddHom.coe_mk, one_mul, X] at eq1
    exact eq1.symm⟩

omit [IsSimpleRing A] in
lemma IsBalanced.congr_aux (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (l : M ≃ₗ[A] N) (h : IsBalanced A M) : IsBalanced A N := by
  refine ⟨fun a => ?_⟩
  let a' : Module.End (Module.End A M) M :=
  { toFun := fun m => l.symm $ a $ l m
    map_add' := by simp
    map_smul' := fun x y => by
      simp only [LinearMap.smul_def, RingHom.id_apply]
      let L := l.toLinearMap ∘ₗ x ∘ₗ l.symm.toLinearMap
      have := a.map_smul L (l $ y)
      simp only [LinearMap.smul_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply, L] at this
      simp [this] }
  obtain ⟨b, hb⟩ := h.1 a'
  refine ⟨b, ?_⟩
  ext n
  simp only [toEndEnd_apply, DistribMulAction.toLinearMap_apply]
  have := congr($hb $ l.symm n)
  simp only [toEndEnd_apply, DistribMulAction.toLinearMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply, a'] at this
  apply_fun l at this
  simpa using this

omit [IsSimpleRing A] in
lemma IsBalanced.congr {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (l : M ≃ₗ[A] N) : IsBalanced A M ↔ IsBalanced A N := by
  constructor
  · apply IsBalanced.congr_aux; exact l
  · apply IsBalanced.congr_aux; exact l.symm


lemma isBalanced_of_simpleMod (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] : IsBalanced A M := by
  classical
  obtain ⟨ι, ⟨e⟩⟩ := directSum_simple_module_over_simple_ring' k A A M
  haveI : IsBalanced A A := inferInstance
  haveI b : IsBalanced A (ι →₀ M) := by
    rw [← IsBalanced.congr A e]
    infer_instance
  refine ⟨fun g => ?_⟩
  let G : Module.End (Module.End A (ι →₀ M)) (ι →₀ M) :=
  { toFun := fun v => Finsupp.mapRange g (by simp) v
    map_add' := by intros; ext; simp
    map_smul' := by
      intro f v
      ext i
      simp only [LinearMap.smul_def, Finsupp.mapRange_apply, RingHom.id_apply]
      let x (i j : ι) : Module.End A M :=
      { toFun := fun m => f (Finsupp.single i m) j
        map_add' := by simp
        map_smul' := by
          intro a m
          simp only [RingHom.id_apply]
          rw [← Finsupp.smul_single, map_smul]
          rfl }
      have eq (i j k : ι) := g.map_smul (x i j) (v k)
      simp only [LinearMap.smul_def, LinearMap.coe_mk, AddHom.coe_mk, x] at eq
      conv_lhs => rw [show v = ∑ i ∈ v.support, Finsupp.single i (v i) by
        ext j
        simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
          Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
        aesop]
      simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
      change ∑ j ∈ _, _ = _
      simp_rw [eq]
      rw [show ∑ x ∈ v.support, (f (Finsupp.single x (g (v x)))) i =
        (∑ x ∈ v.support, f (Finsupp.single x (g (v x)))) i by simp [Finsupp.coe_finset_sum],
        ← map_sum]
      congr
      ext j
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
        Finsupp.mem_support_iff, ne_eq, ite_not, Finsupp.mapRange_apply, ite_eq_right_iff]
      aesop }
  obtain ⟨a, ha⟩ := b.1 G
  refine ⟨a, ?_⟩
  ext m
  haveI : Nonempty ι := by
    refine isEmpty_or_nonempty ι |>.resolve_left ?_
    intro H
    haveI : Subsingleton (ι →₀ M) := inferInstance
    haveI : Subsingleton A := Equiv.subsingleton e.toEquiv
    have eq1 : (1 : A) = 0 := Subsingleton.elim _ _
    have : Nontrivial A := inferInstance
    exact one_ne_zero eq1
  obtain ⟨j⟩ := this
  have := congr($ha (Finsupp.single j m))
  simp only [toEndEnd_apply, DistribMulAction.toLinearMap_apply, Finsupp.smul_single,
    LinearMap.coe_mk, AddHom.coe_mk, Finsupp.mapRange_single, G] at this ⊢
  have := congr($this j)
  simp only [Finsupp.single_eq_same] at this
  exact this

noncomputable def end_end_iso
    (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    A ≃ₐ[k] Module.End (Module.End A M) M :=
  AlgEquiv.ofBijective
    { toFun := fun a =>
      { toFun := fun m => a • m
        map_add' := by simp
        map_smul' := by simp }
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp [mul_smul]
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_smul]
      commutes' := by
        intro r
        ext m
        simp only [algebraMap_smul, LinearMap.coe_mk, AddHom.coe_mk]
        rfl }
    ⟨toEndEnd_injective k A M, isBalanced_of_simpleMod k A M |>.1⟩


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
    rw [← Module.rank_lt_aleph0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1

  have eq1 := Module.finrank_matrix k D (Fin n) (Fin n)
  have eq2 := Module.finrank_matrix k D (Fin n') (Fin n')
  simp only [Fintype.card_fin] at eq1 eq2
  have eq3 : n * n * Module.finrank k D = n' * n' * Module.finrank k D := by
    rw [← eq1, ← eq2]
    exact LinearEquiv.finrank_eq e
  simp only [mul_eq_mul_right_iff] at eq3
  replace eq3 := eq3.resolve_right (fun rid => by
    rw [Module.finrank_zero_iff] at rid
    simpa using rid.elim 0 1)
  simpa [← pow_two] using eq3

end simple
