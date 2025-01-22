-- import Mathlib.Algebra.Category.ModuleCat.Products
-- import Mathlib.Algebra.DirectSum.Module

-- open CategoryTheory

-- open CategoryTheory.Limits

-- universe u v w

-- namespace ModuleCat

-- variable {R : Type u} [Ring R]
-- variable {ι : Type v} (Z : ι → ModuleCatMax.{v, w} R)


-- section coproduct

-- open DirectSum

-- variable [DecidableEq ι]

-- /-- The coproduct cone induced by the concrete product. -/
-- def coproductCocone : Cofan Z :=
--   Cofan.mk (ModuleCat.of R (⨁ i : ι, Z i)) fun i => (DirectSum.lof R ι (fun i ↦ Z i) i)

-- /-- The concrete coproduct cone is limiting. -/
-- def coproductCoconeIsColimit : IsColimit (coproductCocone Z) where
--   desc s := DirectSum.toModule R ι _ fun i ↦ s.ι.app ⟨i⟩
--   fac := by
--     rintro s ⟨i⟩
--     ext (x : Z i)
--     simpa only [Discrete.functor_obj_eq_as, coproductCocone, Cofan.mk_pt, Functor.const_obj_obj,
--       Cofan.mk_ι_app, coe_comp, Function.comp_apply] using
--       DirectSum.toModule_lof (ι := ι) R (M := fun i ↦ Z i) i x
--   uniq := by
--     rintro s f h
--     refine DirectSum.linearMap_ext _ fun i ↦ ?_
--     ext x
--     simpa only [LinearMap.coe_comp, Function.comp_apply, toModule_lof] using
--       congr($(h ⟨i⟩) x)

-- variable [HasCoproduct Z]

-- /-- The categorical coproduct of a family of objects in `ModuleCat`
-- agrees with direct sum.
-- -/
-- noncomputable def coprodIsoDirectSum : ∐ Z ≅ ModuleCat.of R (⨁ i, Z i) :=
--   colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩

-- @[simp, elementwise]
-- theorem ι_coprodIsoDirectSum_hom (i : ι) :
--     Sigma.ι Z i ≫ (coprodIsoDirectSum Z).hom = DirectSum.lof R ι (fun i ↦ Z i) i :=
--   colimit.isoColimitCocone_ι_hom _ _

-- @[simp, elementwise]
-- theorem lof_coprodIsoDirectSum_inv (i : ι) :
--     DirectSum.lof R ι (fun i ↦ Z i) i ≫ (coprodIsoDirectSum Z).inv = Sigma.ι Z i :=
--   (coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

-- end coproduct

-- end ModuleCat
