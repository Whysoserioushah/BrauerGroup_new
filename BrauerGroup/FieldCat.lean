/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.FieldTheory.PurelyInseparable

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`
along with the relevant forgetful functors between them.
-/

universe u v

open CategoryTheory

/-- The category of rings. -/
abbrev FieldCat : Type (u + 1) :=
  Bundled Field

namespace FieldCat

instance : BundledHom.ParentProjection @Field.toCommRing :=
  ⟨⟩

instance (X : FieldCat) : Field X := X.str

-- Porting note: Hinting to Lean that `forget R` and `R` are the same
unif_hint forget_obj_eq_coe (R : FieldCat) where ⊢
  (forget FieldCat).obj R ≟ R

instance instField (X : FieldCat) : Field X := X.str

instance instFunLike {X Y : FieldCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to FieldHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

-- Porting note (#10754): added instance
instance instFieldHomClass {X Y : FieldCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

lemma coe_id {X : FieldCat} : (𝟙 X : X → X) = id := rfl

lemma coe_comp {X Y Z : FieldCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp] lemma forget_map {X Y : FieldCat} (f : X ⟶ Y) : (forget FieldCat).map f = (f : X → Y) := rfl

lemma ext {X Y : FieldCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

/-- Construct a bundled `FieldCat` from the underlying type and typeclass. -/
def of (R : Type u) [Field R] : FieldCat :=
  Bundled.of R

/-- Typecheck a `RingHom` as a morphism in `FieldCat`. -/
def ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : of R ⟶ of S :=
  f

-- Porting note: I think this is now redundant.
-- @[simp]
-- theorem ofHom_apply {R S : Type u} [Field R] [Field S] (f : R →+* S) (x : R) : ofHom f x = f x :=
--   rfl

instance : Inhabited FieldCat :=
  ⟨of ℚ⟩

instance (R : FieldCat) : Field R :=
  R.str

@[simp]
theorem coe_of (R : Type u) [Field R] : (FieldCat.of R : Type u) = R :=
  rfl

-- Coercing the identity morphism, as a Field homomorphism, gives the identity function.
@[simp] theorem coe_FieldHom_id {X : FieldCat} :
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (𝟙 X) = id :=
  rfl

-- Coercing `𝟙 (of X)` to a function should be expressed as the coercion of `RingHom.id X`.
@[simp] theorem coe_id_of {X : Type u} [Field X] :
    @DFunLike.coe no_index (FieldCat.of X ⟶ FieldCat.of X) X
      (fun _ ↦ X) _
      (𝟙 (of X)) =
    @DFunLike.coe (X →+* X) X (fun _ ↦ X) _ (RingHom.id X) :=
  rfl

-- Coercing `f ≫ g`, where `f : of X ⟶ of Y` and `g : of Y ⟶ of Z`, to a function should be
-- expressed in terms of the coercion of `g.comp f`.
@[simp] theorem coe_comp_of {X Y Z : Type u} [Field X] [Field Y] [Field Z]
    (f : X →+* Y) (g : Y →+* Z) :
    @DFunLike.coe no_index (FieldCat.of X ⟶ FieldCat.of Z) X
      (fun _ ↦ Z) _
      (CategoryStruct.comp (X := FieldCat.of X) (Y := FieldCat.of Y) (Z := FieldCat.of Z)
        f g) =
    @DFunLike.coe (X →+* Z) X (fun _ ↦ Z) _ (RingHom.comp g f) :=
  rfl

-- Sometimes neither the `ext` lemma for `FieldCat` nor for `RingHom` is applicable,
-- because of incomplete unfolding of `FieldCat.of X ⟶ FieldCat.of Y := X →+* Y`,
-- but this one will fire.
@[ext] theorem ext_of {X Y : Type u} [Field X] [Field Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (FieldCat.of X ⟶ FieldCat.of Y) f g :=
  RingHom.ext h

@[simp]
lemma FieldEquiv_coe_eq {X Y : Type _} [Field X] [Field Y] (e : X ≃+* Y) :
    (@DFunLike.coe (FieldCat.of X ⟶ FieldCat.of Y) _ (fun _ => (forget FieldCat).obj _)
      ConcreteCategory.instFunLike (e : X →+* Y) : X → Y) = ↑e :=
  rfl

instance hasForgetToCommRingCat : HasForget₂ FieldCat CommRingCat :=
  BundledHom.forget₂ _ _

instance hasForgetToRingCat : HasForget₂ FieldCat RingCat :=
  BundledHom.forget₂ _ _ |>.trans _

instance hasForgetToAddCommGrp : HasForget₂ FieldCat AddCommGrp where
  -- can't use BundledHom.mkHasForget₂, since AddCommGroup is an induced category
  forget₂ :=
    { obj := fun R => AddCommGrp.of R
      -- Porting note: use `(_ := _)` similar to above.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }

end FieldCat

namespace FieldEquiv

variable {X Y : Type u}

/-- Build an isomorphism in the category `FieldCat` from a `FieldEquiv` between `FieldCat`s. -/
@[simps]
def toFieldCatIso [Field X] [Field Y] (e : X ≃+* Y) : FieldCat.of X ≅ FieldCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

end FieldEquiv

namespace CategoryTheory.Iso

/-- Build a `FieldEquiv` from an isomorphism in the category `FieldCat`. -/
def FieldCatIsoToRingEquiv {X Y : FieldCat} (i : X ≅ Y) : X ≃+* Y :=
  RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id

-- /-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
-- def commRingCatIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y :=
--   RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id

-- -- Porting note: make this high priority to short circuit simplifier
-- @[simp (high)]
-- theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
--     i.commRingCatIsoToRingEquiv.toRingHom = i.hom := by
--   ext
--   rfl

-- -- Porting note: make this high priority to short circuit simplifier
-- @[simp (high)]
-- theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
--     i.commRingCatIsoToRingEquiv.symm.toRingHom = i.inv := by
--   ext
--   rfl

end CategoryTheory.Iso

/-- Ring equivalences between `RingCat`s are the same as (isomorphic to) isomorphisms in
`RingCat`. -/
def fieldEquivIsoRingIso {X Y : Type u} [Field X] [Field Y] :
    X ≃+* Y ≅ FieldCat.of X ≅ FieldCat.of Y where
  hom e := FieldEquiv.toFieldCatIso e
  inv i := i.FieldCatIsoToRingEquiv

-- /-- Ring equivalences between `CommRingCat`s are the same as (isomorphic to) isomorphisms
-- in `CommRingCat`. -/
-- def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
--     X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y where
--   hom e := e.toCommRingCatIso
--   inv i := i.commRingCatIsoToRingEquiv

instance FieldCat.forget_reflects_isos : (forget FieldCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget FieldCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact (FieldEquiv.toFieldCatIso e).isIso_hom

-- instance CommRingCat.forget_reflects_isos : (forget CommRingCat.{u}).ReflectsIsomorphisms where
--   reflects {X Y} f _ := by
--     let i := asIso ((forget CommRingCat).map f)
--     let ff : X →+* Y := f
--     let e : X ≃+* Y := { ff, i.toEquiv with }
--     exact e.toCommRingCatIso.isIso_hom

-- theorem CommRingCat.comp_eq_ring_hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
--     f ≫ g = g.comp f :=
--   rfl

-- theorem CommRingCat.ringHom_comp_eq_comp {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
--     (f : R →+* S) (g : S →+* T) : g.comp f = CommRingCat.ofHom f ≫ CommRingCat.ofHom g :=
--   rfl

-- It would be nice if we could have the following,
-- but it requires making `reflectsIsomorphisms_forget₂` an instance,
-- which can cause typeclass loops:
-- Porting note: This was the case in mathlib3, perhaps it is different now?
attribute [local instance] reflectsIsomorphisms_forget₂

example : (forget₂ FieldCat AddCommGrp).ReflectsIsomorphisms := by infer_instance

/-!
`@[simp]` lemmas for `RingHom.comp` and categorical identities.
-/

-- @[simp] theorem RingHom.comp_id_semiringCat
--     {G : SemiRingCat.{u}} {H : Type u} [Semiring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
--   Category.id_comp (SemiRingCat.ofHom f)
-- @[simp] theorem RingHom.id_semiringCat_comp
--     {G : Type u} [Semiring G] {H : SemiRingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
--   Category.comp_id (SemiRingCat.ofHom f)

-- @[simp] theorem RingHom.comp_id_commSemiringCat
--     {G : CommSemiRingCat.{u}} {H : Type u} [CommSemiring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
--   Category.id_comp (CommSemiRingCat.ofHom f)
-- @[simp] theorem RingHom.id_commSemiringCat_comp
--     {G : Type u} [CommSemiring G] {H : CommSemiRingCat.{u}} (f : G →+* H) :
--     RingHom.comp (𝟙 H) f = f :=
--   Category.comp_id (CommSemiRingCat.ofHom f)

-- @[simp] theorem RingHom.comp_id_ringCat
--     {G : RingCat.{u}} {H : Type u} [Ring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
--   Category.id_comp (RingCat.ofHom f)
-- @[simp] theorem RingHom.id_ringCat_comp
--     {G : Type u} [Ring G] {H : RingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
--   Category.comp_id (RingCat.ofHom f)

-- @[simp] theorem RingHom.comp_id_commRingCat
--     {G : CommRingCat.{u}} {H : Type u} [CommRing H] (f : G →+* H) : f.comp (𝟙 G) = f :=
--   Category.id_comp (CommRingCat.ofHom f)
-- @[simp] theorem RingHom.id_commRingCat_comp
--     {G : Type u} [CommRing G] {H : CommRingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
--   Category.comp_id (CommRingCat.ofHom f)
