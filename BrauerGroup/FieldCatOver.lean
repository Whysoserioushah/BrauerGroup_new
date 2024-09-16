import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Category.AlgebraCat.Basic
import BrauerGroup.FieldCat

universe u

open CategoryTheory

variable (K : Type u) [Field K]

-- class GaloisFunctor extends AlgebraCat K ⥤ Grp where
--   val := ∀(E G: Type u) [Field E] [Algebra K E] [Field G] [Algebra E G] [IsGalois E G],
--     Function.Injective (toFunctor.map _ )
structure FieldCatOver (K : Type u) [Field K] where
  carrier : Type u
  [isField : Field carrier]
  [isAlgebra : Algebra K carrier]

attribute [instance] FieldCatOver.isField FieldCatOver.isAlgebra

namespace FieldCatOver
instance : CoeSort (FieldCatOver K) (Type u) :=
  ⟨FieldCatOver.carrier⟩

attribute [coe] FieldCatOver.carrier

instance : Category (FieldCatOver K) where
  Hom A B := A →ₐ[K] B
  id A := AlgHom.id K A
  comp f g := g.comp f

instance {M N : FieldCatOver K} : FunLike (M ⟶ N) M N :=
  AlgHom.funLike

instance {M N : FieldCatOver K} : AlgHomClass (M ⟶ N) K M N :=
  AlgHom.algHomClass

instance : ConcreteCategory (FieldCatOver K) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => AlgHom.ext (by intros x; dsimp at h; rw [h])⟩

instance {S : FieldCatOver K} : Field ((forget (FieldCatOver K)).obj S) :=
  (inferInstance : Field S.carrier)

instance {S : FieldCatOver K} : Algebra K ((forget (FieldCatOver K)).obj S) :=
  (inferInstance : Algebra K S.carrier)

instance hasForgetToField : HasForget₂ (FieldCatOver K) FieldCat where
  forget₂ :=
    { obj := fun A => FieldCat.of A
      map := fun f => FieldCat.ofHom f.toRingHom }

instance hasForgetToRing : HasForget₂ (FieldCatOver K) RingCat where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.toRingHom }

instance hasForgetToModule : HasForget₂ (FieldCatOver K) (ModuleCat K) where
  forget₂ :=
    { obj := fun M => ModuleCat.of K M
      map := fun f => ModuleCat.ofHom f.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : FieldCatOver K) :
    (forget₂ (FieldCatOver K) (ModuleCat K)).obj X = ModuleCat.of K X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : FieldCatOver K} (f : X ⟶ Y) :
    (forget₂ (FieldCatOver K) (ModuleCat K)).map f = ModuleCat.ofHom f.toLinearMap :=
  rfl

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type u) [Field X] [Algebra K X] : FieldCatOver K :=
  ⟨X⟩

/-- Typecheck a `AlgHom` as a morphism in `AlgebraCat R`. -/
def ofHom {K} [Field K] {X Y : Type u} [Field X] [Algebra K X] [Field Y] [Algebra K Y]
    (f : X →ₐ[K] Y) : of K X ⟶ of K Y :=
  f

@[simp]
theorem ofHom_apply {X Y : Type u} [Field X] [Algebra K X] [Field Y]
    [Algebra K Y] (f : X →ₐ[K] Y) (x : X) : ofHom f x = f x :=
  rfl

instance : Inhabited (FieldCatOver K) :=
  ⟨of K K⟩

@[simp]
theorem coe_of (X : Type u) [Field X] [Algebra K X] : (of K X : Type u) = X :=
  rfl


variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : FieldCatOver K) : FieldCatOver.of K M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

-- variable {M N U : ModuleCat K}

-- @[simp]
-- theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
--   rfl

-- @[simp]
-- theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
--   rfl

-- variable (R)

-- /-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
-- @[simps!]
-- def free : Type u ⥤ AlgebraCat.{u} R where
--   obj S :=
--     { carrier := FreeAlgebra R S
--       isRing := Algebra.semiringToRing R }
--   map f := FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f
--   -- Porting note (#11041): `apply FreeAlgebra.hom_ext` was `ext1`.
--   map_id := by intro X; apply FreeAlgebra.hom_ext; simp only [FreeAlgebra.ι_comp_lift]; rfl
--   map_comp := by
--   -- Porting note (#11041): `apply FreeAlgebra.hom_ext` was `ext1`.
--     intros; apply FreeAlgebra.hom_ext; simp only [FreeAlgebra.ι_comp_lift]; ext1
--     -- Porting node: this ↓ `erw` used to be handled by the `simp` below it
--     erw [CategoryTheory.coe_comp]
--     simp only [CategoryTheory.coe_comp, Function.comp_apply, types_comp_apply]
--     -- Porting node: this ↓ `erw` and `rfl` used to be handled by the `simp` above
--     erw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
--     rfl

-- /-- The free/forget adjunction for `R`-algebras. -/
-- def adj : free.{u} R ⊣ forget (AlgebraCat.{u} R) :=
--   Adjunction.mkOfHomEquiv
--     { homEquiv := fun X A => (FreeAlgebra.lift _).symm
--       -- Relying on `obviously` to fill out these proofs is very slow :(
--       homEquiv_naturality_left_symm := by
--         -- Porting note (#11041): `apply FreeAlgebra.hom_ext` was `ext1`.
--         intros; apply FreeAlgebra.hom_ext; simp only [FreeAlgebra.ι_comp_lift]; ext1
--         simp only [free_map, Equiv.symm_symm, FreeAlgebra.lift_ι_apply, CategoryTheory.coe_comp,
--           Function.comp_apply, types_comp_apply]
--         -- Porting node: this ↓ `erw` and `rfl` used to be handled by the `simp` above
--         erw [FreeAlgebra.lift_ι_apply, CategoryTheory.comp_apply, FreeAlgebra.lift_ι_apply,
--           Function.comp_apply, FreeAlgebra.lift_ι_apply]
--         rfl
--       homEquiv_naturality_right := by
--         intros; ext
--         simp only [CategoryTheory.coe_comp, Function.comp_apply,
--           FreeAlgebra.lift_symm_apply, types_comp_apply]
--         -- Porting note: proof used to be done after this ↑ `simp`; added ↓ two lines
--         erw [FreeAlgebra.lift_symm_apply, FreeAlgebra.lift_symm_apply]
--         rfl }

-- instance : (forget (AlgebraCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end FieldCatOver

variable {K}
variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `AlgebraCat R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def FieldEquiv.toAlgebraIso {g₁ : Field X₁} {g₂ : Field X₂} {m₁ : Algebra K X₁} {m₂ : Algebra K X₂}
    (e : X₁ ≃ₐ[K] X₂) : FieldCatOver.of K X₁ ≅ FieldCatOver.of K X₂ where
  hom := (e : X₁ →ₐ[K] X₂)
  inv := (e.symm : X₂ →ₐ[K] X₁)
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x


namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `AlgebraCat R`. -/
@[simps]
def FieldCatOver.toAlgEquiv {X Y : FieldCatOver K} (i : X ≅ Y) : X ≃ₐ[K] Y :=
  { i.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x => by
      -- Porting note: was `by tidy`
      change (i.hom ≫ i.inv) x = x
      simp only [hom_inv_id]
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [id_apply]
    right_inv := fun x => by
      -- Porting note: was `by tidy`
      change (i.inv ≫ i.hom) x = x
      simp only [inv_hom_id]
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [id_apply] }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgebraCat`. -/
@[simps!]
def algEquivIsoFieldIso {X Y : Type u} [Field X] [Field Y] [Algebra K X] [Algebra K Y] :
    (X ≃ₐ[K] Y) ≅ FieldCatOver.of K X ≅ FieldCatOver.of K Y where
  hom e := FieldEquiv.toAlgebraIso e
  inv i := CategoryTheory.Iso.FieldCatOver.toAlgEquiv i

instance FieldCatOver.forget_reflects_isos : (forget (FieldCatOver K)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (FieldCatOver K)).map f)
    let e : X ≃ₐ[K] Y := { f, i.toEquiv with }
    exact (FieldEquiv.toAlgebraIso e).isIso_hom

/-!
`@[simp]` lemmas for `AlgHom.comp` and categorical identities.
-/

@[simp] theorem AlgHom.comp_id_fieldCatOver
    {K} [Field K] {G : FieldCatOver K} {H : Type u} [Field H] [Algebra K H] (f : G →ₐ[K] H) :
    f.comp (𝟙 G) = f := rfl

@[simp] theorem AlgHom.id_fieldCatOver_comp
    {G : Type u} [Field G] [Algebra K G] {H : FieldCatOver K} (f : G →ₐ[K] H) :
    AlgHom.comp (𝟙 H) f = f :=
  Category.comp_id (AlgebraCat.ofHom f)
