/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Category instances for `Field`.
-/

universe u v

open CategoryTheory

/-- The category of fields. -/
structure FieldCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [field : Field carrier]

attribute [instance] FieldCat.field

initialize_simps_projections FieldCat (-field)

namespace FieldCat

instance : CoeSort (FieldCat) (Type u) :=
  ⟨FieldCat.carrier⟩

attribute [coe] FieldCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `FieldCat`. -/
abbrev of (R : Type u) [Field R] : FieldCat := ⟨R⟩

lemma coe_of (R : Type u) [Field R] : (of R : Type u) = R := rfl

lemma of_carrier (R : FieldCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `FieldCat`. -/
@[ext]
structure Hom (R S : FieldCat) where
  private mk ::
  /-- The underlying ring hom. -/
  hom : R →+* S

instance : Category FieldCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom.comp f.hom⟩


instance {R S : FieldCat.{u}} : CoeFun (R ⟶ S) (fun _ ↦ R → S) where
  coe f := f.hom

@[simp]
lemma hom_id {R : FieldCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
lemma id_apply (R : FieldCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
lemma hom_comp {R S T : FieldCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {R S T : FieldCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
lemma hom_ext {R S : FieldCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/-- Typecheck a `RingHom` as a morphism in `FieldCat`. -/
abbrev ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : of R ⟶ of S :=
  ⟨f⟩

lemma hom_ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {R S : FieldCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {R : Type u} [Field R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
lemma ofHom_comp {R S T : Type u} [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R S : Type u} [Field R] [Field S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl


@[simp]
lemma inv_hom_apply {R S : FieldCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply {R S : FieldCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

-- instance : Inhabited FieldCat :=
--   ⟨of PUnit⟩

instance : HasForget.{u} FieldCat where
  forget :=
    { obj := fun R => R
      map := fun f => f.hom }
  forget_faithful := ⟨fun h => by ext x; simpa using congrFun h x⟩


/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forget_obj_eq_coe (R R' : FieldCat) where
  R ≟ R' ⊢
  (forget FieldCat).obj R ≟ FieldCat.carrier R'

lemma forget_obj {R : FieldCat} : (forget FieldCat).obj R = R := rfl

lemma forget_map {R S : FieldCat} (f : R ⟶ S) :
    (forget FieldCat).map f = f :=
  rfl

instance {R : FieldCat} : Field ((forget FieldCat).obj R) :=
  (inferInstance : Field R.carrier)

instance hasForgetToSemiRingCat : HasForget₂ FieldCat CommRingCat where
  forget₂ :=
    { obj := fun R ↦ CommRingCat.of R
      map := fun f ↦ CommRingCat.ofHom f.hom }

instance hasForgetToAddCommGrp : HasForget₂ FieldCat RingCat where
  forget₂ :=
    { obj := fun R ↦ RingCat.of R
      map := fun f ↦ RingCat.ofHom f.hom }

/-- Field equivalence are isomorphisms in category of semirings -/
@[simps]
def RingEquiv.toRingCatIso {R S : Type u} [Field R] [Field S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩

instance forgetReflectIsos : (forget FieldCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget FieldCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact FieldCat.RingEquiv.toRingCatIso e|>.isIso_hom


-- instance : BundledHom.ParentProjection @Field.toCommRing :=
--   ⟨⟩

-- instance (X : FieldCat) : Field X.1 := X.field

-- instance : Category FieldCat := inferInstance

-- instance : HasForget FieldCat where
--   forget := {
--     obj X := X
--     map f := f.1
--     map_id X := by simp [RingHom.id_apply]; rfl
--     map_comp := _
--   }
--   forget_faithful := _

-- -- Porting note: Hinting to Lean that `forget R` and `R` are the same
-- unif_hint forget_obj_eq_coe (R : FieldCat) where ⊢
--   (forget FieldCat).obj R ≟ R

-- instance instField (X : FieldCat) : Field X := X.str

-- instance instFunLike {X Y : FieldCat} : FunLike (X ⟶ Y) X Y :=
--   -- Note: this is apparently _not_ defeq to FieldHom.instFunLike with reducible transparency
--   ConcreteCategory.instFunLike

-- -- Porting note (#10754): added instance
-- instance instFieldHomClass {X Y : FieldCat} : RingHomClass (X ⟶ Y) X Y :=
--   RingHom.instRingHomClass

-- lemma coe_id {X : FieldCat} : (𝟙 X : X → X) = id := rfl

-- lemma coe_comp {X Y Z : FieldCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

-- @[simp] lemma forget_map {X Y : FieldCat} (f : X ⟶ Y) : (forget FieldCat).map f = (f : X → Y) := rfl

-- lemma ext {X Y : FieldCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
--   RingHom.ext w

-- /-- Construct a bundled `FieldCat` from the underlying type and typeclass. -/
-- def of (R : Type u) [Field R] : FieldCat :=
--   Bundled.of R

-- /-- Typecheck a `RingHom` as a morphism in `FieldCat`. -/
-- def ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : of R ⟶ of S :=
--   f

-- -- Porting note: I think this is now redundant.
-- -- @[simp]
-- -- theorem ofHom_apply {R S : Type u} [Field R] [Field S] (f : R →+* S) (x : R) : ofHom f x = f x :=
-- --   rfl

-- instance : Inhabited FieldCat :=
--   ⟨of ℚ⟩

-- instance (R : FieldCat) : Field R :=
--   R.str

-- @[simp]
-- theorem coe_of (R : Type u) [Field R] : (FieldCat.of R : Type u) = R :=
--   rfl

-- -- Coercing the identity morphism, as a Field homomorphism, gives the identity function.
-- @[simp] theorem coe_FieldHom_id {X : FieldCat} :
--     @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (𝟙 X) = id :=
--   rfl

-- -- Coercing `𝟙 (of X)` to a function should be expressed as the coercion of `RingHom.id X`.
-- @[simp] theorem coe_id_of {X : Type u} [Field X] :
--     @DFunLike.coe no_index (FieldCat.of X ⟶ FieldCat.of X) X
--       (fun _ ↦ X) _
--       (𝟙 (of X)) =
--     @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (RingHom.id X) :=
--   rfl

-- -- Coercing `f ≫ g`, where `f : of X ⟶ of Y` and `g : of Y ⟶ of Z`, to a function should be
-- -- expressed in terms of the coercion of `g.comp f`.
-- @[simp] theorem coe_comp_of {X Y Z : Type u} [Field X] [Field Y] [Field Z]
--     (f : X →+* Y) (g : Y →+* Z) :
--     @DFunLike.coe no_index (FieldCat.of X ⟶ FieldCat.of Z) X
--       (fun _ ↦ Z) _
--       (CategoryStruct.comp (X := FieldCat.of X) (Y := FieldCat.of Y) (Z := FieldCat.of Z)
--         f g) =
--     @DFunLike.coe (X →+* Z) X (fun _ ↦ Z) _ (RingHom.comp g f) :=
--   rfl

-- -- Sometimes neither the `ext` lemma for `FieldCat` nor for `RingHom` is applicable,
-- -- because of incomplete unfolding of `FieldCat.of X ⟶ FieldCat.of Y := X →+* Y`,
-- -- but this one will fire.
-- @[ext] theorem ext_of {X Y : Type u} [Field X] [Field Y] (f g : X →+* Y)
--     (h : ∀ x, f x = g x) :
--     @Eq (FieldCat.of X ⟶ FieldCat.of Y) f g :=
--   RingHom.ext h

-- @[simp]
-- lemma FieldEquiv_coe_eq {X Y : Type _} [Field X] [Field Y] (e : X ≃+* Y) :
--     (@DFunLike.coe (FieldCat.of X ⟶ FieldCat.of Y) _ (fun _ => (forget FieldCat).obj _)
--       ConcreteCategory.instFunLike (e : X →+* Y) : X → Y) = ↑e :=
--   rfl

-- instance hasForgetToCommFieldCat : HasForget₂ FieldCat CommFieldCat :=
--   BundledHom.forget₂ _ _

-- -- instance hasForgetToFieldCat : HasForget₂ FieldCat FieldCat :=
-- --   BundledHom.forget₂ _ Field.toCommRing |>.tran _

-- instance hasForgetToAddCommGrp : HasForget₂ FieldCat AddCommGrp where
--   -- can't use BundledHom.mkHasForget₂, since AddCommGroup is an induced category
--   forget₂ :=
--     { obj := fun R => AddCommGrp.of R
--       -- Porting note: use `(_ := _)` similar to above.
--       map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }

-- end FieldCat

-- namespace FieldEquiv

-- variable {X Y : Type u}

-- /-- Build an isomorphism in the category `FieldCat` from a `FieldEquiv` between `FieldCat`s. -/
-- @[simps]
-- def toFieldCatIso [Field X] [Field Y] (e : X ≃+* Y) : FieldCat.of X ≅ FieldCat.of Y where
--   hom := e.toRingHom
--   inv := e.symm.toRingHom

-- end FieldEquiv

-- namespace CategoryTheory.Iso

-- /-- Build a `FieldEquiv` from an isomorphism in the category `FieldCat`. -/
-- def FieldCatIsoToRingEquiv {X Y : FieldCat} (i : X ≅ Y) : X ≃+* Y :=
--   RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id


-- end CategoryTheory.Iso

-- /-- Field equivalences between `FieldCat`s are the same as (isomorphic to) isomorphisms in
-- `FieldCat`. -/
-- def fieldEquivIsoRingIso {X Y : Type u} [Field X] [Field Y] :
--     X ≃+* Y ≅ FieldCat.of X ≅ FieldCat.of Y where
--   hom e := FieldEquiv.toFieldCatIso e
--   inv i := i.FieldCatIsoToRingEquiv

-- instance FieldCat.forget_reflects_isos : (forget FieldCat.{u}).ReflectsIsomorphisms where
--   reflects {X Y} f _ := by
--     let i := asIso ((forget FieldCat).map f)
--     let ff : X →+* Y := f
--     let e : X ≃+* Y := { ff, i.toEquiv with }
--     exact (FieldEquiv.toFieldCatIso e).isIso_hom


-- -- It would be nice if we could have the following,
-- -- but it requires making `reflectsIsomorphisms_forget₂` an instance,
-- -- which can cause typeclass loops:
-- -- Porting note: This was the case in mathlib3, perhaps it is different now?
-- attribute [local instance] reflectsIsomorphisms_forget₂

-- example : (forget₂ FieldCat AddCommGrp).ReflectsIsomorphisms := by infer_instance
