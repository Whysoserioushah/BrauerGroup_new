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
    [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.rank A M = Module.rank A N := by
  fconstructor
  · rintro ⟨iso⟩
    exact iso.rank_eq
  · intro h
    obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring k A M
    obtain ⟨ι', ⟨iso'⟩⟩ := directSum_simple_module_over_simple_ring' k A N S
    have eq := iso.rank_eq
    have eq' := iso'.rank_eq
    have EQ : Module.rank A (ι →₀ S) = Module.rank A (ι' →₀ S) := by
      rw [← eq, h, eq']

    -- I am stuck because I don't have **StrongRankCondition**
    sorry

end simple
