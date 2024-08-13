import BrauerGroup.Wedderburn

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.FieldTheory.Finiteness

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
  -- each individual goal will type check, together they can't be compiled with maxHeartbeats
  -- 8000000. Somebody should do something about this.
  let iso₄ :
      ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
      show ModuleCat.of A (b →₀ (ModuleCat.restrictScalars _).obj (ModuleCat.of _ _)) ≅
        (ModuleCat.restrictScalars _).obj (ModuleCat.of _ _) from
        { hom := ModuleCat.semilinearMapAddEquiv _ _ _ $
          { toFun := fun x i => Finsupp.ofSupportFinite (fun y => x.toFun y i) $ sorry
              -- Set.Finite.subset (Finsupp.finite_support x) fun y hy => by
              --   simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
              --     Function.mem_support, ne_eq, Finsupp.fun_support_eq, Finset.mem_coe,
              --     Finsupp.mem_support_iff] at hy ⊢
              --   contrapose! hy
              --   change x.toFun y = 0 at hy
              --   rw [hy]
              --   rfl
            map_add' := fun x x' => funext fun i => Finsupp.ext fun y => rfl
            map_smul' := fun a x => funext fun i => Finsupp.ext fun y => show ∑ j : Fin n, _ = _ by
              sorry
              -- erw [matrix_smul_vec_apply]
              -- erw [Finsupp.coe_finset_sum]
              -- simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
              --   RingEquiv.symm_symm, AlgEquiv.toRingEquiv_toRingHom, RingHom.toMonoidHom_eq_coe,
              --   OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
              --   ZeroHom.coe_mk, smul_eq_mul, Finsupp.ofSupportFinite, Finset.sum_apply]
              -- rfl
              }
          inv :=
            ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction _
            { toFun := fun v =>
                { toFun := fun x => Finsupp.ofSupportFinite
                    (fun y i =>  ∑ j : Fin n,  x i j * (v j).toFun y) $ sorry
                      -- Set.Finite.subset (s := ⋃ j : Fin n, (v j).support) (Set.toFinite _)
                      -- fun y hy => by
                      -- simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv, smul_eq_mul,
                      --   Function.mem_support, ne_eq, Set.mem_iUnion, Finset.mem_coe,
                      --   Finsupp.mem_support_iff] at hy ⊢
                      -- contrapose! hy
                      -- refine funext fun i => ?_
                      -- simp_rw [show ∀ i, (v i).toFun y = 0 from hy, mul_zero]
                      -- simp only [Finset.sum_const_zero]
                      -- rfl
                  map_add' := fun x y => Finsupp.ext fun z => funext fun i => by sorry
                    -- erw [Finsupp.add_apply]
                    -- rw [Pi.add_apply]
                    -- simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
                    --   Finsupp.ofSupportFinite, Finsupp.coe_mk]
                    -- rw [← Finset.sum_add_distrib]
                    -- refine Finset.sum_congr rfl fun j _ => ?_
                    -- erw [Matrix.add_apply, add_mul]
                  map_smul' := by sorry
                    -- rintro a (x : (ModuleCat.restrictScalars _).obj $ ModuleCat.of _ _)
                    -- simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
                    --   ModuleCat.restrictScalars.smul_def, RingEquiv.symm_symm,
                    --   AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, smul_eq_mul,
                    --   RingHom.id_apply]
                    -- refine Finsupp.ext fun y => ?_
                    -- erw [Finsupp.smul_apply]
                    -- simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
                    -- refine funext fun i => ?_
                    -- erw [matrix_smul_vec_apply]
                    -- simp only [RingEquiv.symm_symm, AlgEquiv.toRingEquiv_toRingHom,
                    --   RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
                    --   MonoidHom.coe_coe, RingHom.coe_coe, ZeroHom.coe_mk, smul_eq_mul]
                    -- simp_rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
                    -- conv_lhs => rw [Finset.sum_comm]

                    -- refine Finset.sum_congr rfl ?_
                    -- rintro j -
                    -- refine Finset.sum_congr rfl ?_
                    -- rintro k -
                    -- rw [mul_assoc]
                     }
              map_add' := by sorry
                -- intro x x'
                -- simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv]
                -- refine LinearMap.ext fun y => ?_
                -- erw [LinearMap.add_apply]
                -- simp only [LinearMap.coe_mk, AddHom.coe_mk]
                -- refine Finsupp.ext fun z => ?_
                -- erw [Finsupp.add_apply]
                -- simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
                -- refine funext fun i => ?_
                -- erw [Pi.add_apply]
                -- rw [← Finset.sum_add_distrib]
                -- refine Finset.sum_congr rfl fun j _ => ?_
                -- erw [Pi.add_apply]
                -- rw [show (x j + x' j).toFun z = (x j).toFun z + (x' j).toFun z from rfl, mul_add]
              map_smul' := by sorry
                -- intro m x
                -- dsimp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.symm_toRingEquiv,
                --   ModuleCat.restrictScalars.smul_def, RingHom.coe_coe, smul_eq_mul,
                --   AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
                -- refine LinearMap.ext fun y => ?_
                -- change _ = (_ : _ →ₗ[_] _).toFun _
                -- erw [ModuleCat.CoextendScalars.smul_apply]
                -- simp only [LinearMap.coe_mk, AddHom.coe_mk]
                -- refine Finsupp.ext fun z => ?_
                -- simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
                -- refine funext fun i => ?_
                -- simp_rw [Matrix.mul_apply]
                -- change ∑ j : Fin n, y i j * ((∑ k : Fin n, m j k • x k : b →₀ _) z) = _
                -- simp_rw [Finsupp.coe_finset_sum]
                -- simp only [Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
                -- conv_lhs => rw [Finset.sum_comm]
                -- refine Finset.sum_congr rfl fun k _ => ?_
                -- simp only [smul_eq_mul, mul_assoc]
                -- rfl
                 }
          hom_inv_id := by sorry
            -- ext x
            -- rw [ModuleCat.coe_comp, Function.comp_apply,
            --   ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_apply, ModuleCat.id_apply,
            --   LinearMap.coe_mk, AddHom.coe_mk]
            -- dsimp only
            -- refine Finsupp.ext fun y => ?_
            -- simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
            -- refine funext fun i => ?_
            -- simp_rw [Matrix.one_apply, ite_mul, zero_mul, one_mul]
            -- rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
            -- erw [ModuleCat.semilinearMapAddEquiv_apply_apply]
            -- rfl
          inv_hom_id := by sorry
            -- ext x
            -- rw [ModuleCat.coe_comp, Function.comp_apply,
            --   ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_apply, ModuleCat.id_apply,
            --   LinearMap.coe_mk, AddHom.coe_mk]
            -- refine funext fun y => ?_
            -- erw [ModuleCat.semilinearMapAddEquiv_apply_apply]
            -- rw [LinearMap.coe_mk, AddHom.coe_mk]
            -- refine Finsupp.ext fun z => ?_
            -- simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk]
            -- simp_rw [Matrix.one_apply, ite_mul, zero_mul, one_mul]
            -- rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
            -- rfl
            }

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

end simple
