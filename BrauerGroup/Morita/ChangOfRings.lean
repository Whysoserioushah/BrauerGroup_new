/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
-- import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor
import BrauerGroup.Morita.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.Matrix.Basic
import BrauerGroup.MoritaEquivalence
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

open CategoryTheory Limits

namespace ModuleCat

universe v u₁ u₂ u₃ w

instance {R₀ S} [CommRing R₀] [Ring S] [Algebra R₀ S]:
    Linear R₀ (ModuleCat S) := Algebra.instLinear

instance restrictScalarsEquivalenceOfRingEquiv_additive {R S} [Ring R] [Ring S] (e : R ≃+* S) :
    (restrictScalarsEquivalenceOfRingEquiv e).functor.Additive where

scoped instance restrictScalarsEquivalenceOfRingEquiv_linear
      {R₀ R S} [CommRing R₀] [Ring R] [Ring S] [Algebra R₀ R] [Algebra R₀ S]
      (e : R ≃ₐ[R₀] S) :
    (restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor.Linear R₀ where
  map_smul {M N} f r₀ := by
    ext m
    simp only [AlgEquiv.toRingEquiv_eq_coe, restrictScalarsEquivalenceOfRingEquiv,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, AddEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      AddEquiv.coe_refl, AddEquiv.refl_symm, restrictScalars.map_apply, hom_smul,
      LinearMap.smul_apply]
    letI : Module R₀ N := Algebra.instModuleCarrier_brauerGroup
    show (algebraMap R₀ R₀) r₀ • _ = e (algebraMap _ _ r₀) • f.hom m
    rw [AlgEquiv.commutes]
    rfl


universe u₀ u u' u''  v'

variable (R : Type u₀) [CommRing R]

instance (priority := low) {R₀ S} [CommRing R₀] [Ring S] [Algebra R₀ S]:
    Linear R₀ (ModuleCat S) := Algebra.instLinear
/--
Let `A` and `B` be `R`-algebras. We say that `A` and `B` are Morita equivalent if the categories of
`A`-modules and `B`-modules are equivalent as `R`-linear categories.
-/
@[ext]
structure MoritaEquivalence
    (R : Type u) [CommRing R]
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] where
  /--the underlying equivalence of categories-/
  eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
  additive : eqv.functor.Additive := by infer_instance
  linear : eqv.functor.Linear R := by infer_instance

namespace MoritaEquivalence

attribute [instance] MoritaEquivalence.additive MoritaEquivalence.linear

/--
For any `R`-algebra `A`, `A` is Morita equivalent to itself.
-/
def refl (A : Type u₁) [Ring A] [Algebra R A] : MoritaEquivalence R A A where
  eqv := CategoryTheory.Equivalence.refl
  additive := CategoryTheory.Functor.instAdditiveId
  linear := CategoryTheory.Functor.instLinearId

/--
For any `R`-algebras `A` and `B`, if `A` is Morita equivalent to `B`, then `B` is Morita equivalent
to `A`.
-/
def symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : MoritaEquivalence R B A where
  eqv := e.eqv.symm
  additive := e.eqv.inverse_additive
  linear := e.eqv.inverseLinear R

-- TODO: We have restricted all the rings to the same universe here because of the complication
-- `max u₁ u₂`, `max u₂ u₃` vs `max u₁ u₃`. But once we proved the definition of Morita
-- equivalence is equivalent to the existence of a full idempotent element, we can remove this
-- restriction in the universe.
-- Or alternatively, @alreadydone has sketched an argument on how the universe restriction can be
-- removed via a categorical argument,
-- see [here](https://github.com/leanprover-community/mathlib4/pull/20640#discussion_r1912189931)
/--
For any `R`-algebras `A`, `B`, and `C`, if `A` is Morita equivalent to `B` and `B` is Morita
equivalent to `C`, then `A` is Morita equivalent to `C`.
-/
def trans {A B C : Type u₁}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (e : MoritaEquivalence R A B) (e' : MoritaEquivalence R B C) :
    MoritaEquivalence R A C where
  eqv := e.eqv.trans e'.eqv
  additive := Functor.instAdditiveComp e.eqv.functor e'.eqv.functor
  linear := Functor.instLinearComp e.eqv.functor e'.eqv.functor

variable {R} in
/--
Isomorphic `R`-algebras are Morita equivalent.
-/
noncomputable def ofAlgEquiv {A : Type u₁} {B : Type u₂}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] (f : A ≃ₐ[R] B) :
    MoritaEquivalence R A B where
  eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := restrictScalarsEquivalenceOfRingEquiv_linear f.symm

end MoritaEquivalence

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure _root_.IsMoritaEquivalent
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] : Prop where
  cond : Nonempty <| MoritaEquivalence R A B

namespace IsMoritaEquivalent

lemma refl {A : Type u₁} [Ring A] [Algebra R A] : IsMoritaEquivalent R A A where
  cond := ⟨.refl R A⟩

lemma symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (h : IsMoritaEquivalent R A B) : IsMoritaEquivalent R B A where
  cond := h.cond.map <| .symm R

lemma trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (h : IsMoritaEquivalent R A B) (h' : IsMoritaEquivalent R B C) :
    IsMoritaEquivalent R A C where
  cond := Nonempty.map2 (.trans R) h.cond h'.cond

lemma of_algEquiv {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (f : A ≃ₐ[R] B) : IsMoritaEquivalent R A B where
  cond := ⟨.ofAlgEquiv f⟩

end IsMoritaEquivalent
-- class IsMoritaEquivalent
--   (R : Type u) (S : Type u') [Ring R] [Ring S] : Prop where
-- out : Nonempty $ ModuleCat.{v} R ≌ ModuleCat.{v'} S

-- namespace IsMoritaEquivalent

-- variable (R : Type u) (S : Type u') (T : Type u'') [Ring R] [Ring S] [Ring T]

-- noncomputable def equiv [IsMoritaEquivalent R S] : ModuleCat R ≌ ModuleCat S :=
--   (inferInstance : IsMoritaEquivalent R S) |>.out.some


-- instance [IsMoritaEquivalent R S] : (equiv R S).functor.Additive := inferInstance

-- instance [IsMoritaEquivalent R S] : (equiv R S).inverse.Additive :=
-- inferInstance

-- @[refl]
-- lemma refl : IsMoritaEquivalent R R :=
-- ⟨⟨CategoryTheory.Equivalence.refl (C := ModuleCat.{v} R)⟩⟩

-- instance : IsMoritaEquivalent.{u, u, v, v} R R := refl R

-- @[symm]
-- lemma symm [IsMoritaEquivalent.{u, u', v, v'} R S] : IsMoritaEquivalent.{u', u, v', v} S R where
--   out := ⟨equiv R S |>.symm⟩

-- @[trans]
-- lemma trans [IsMoritaEquivalent.{u, u', v, v'} R S] [IsMoritaEquivalent.{u', u'', v', v''} S T] :
--     IsMoritaEquivalent.{u, u'', v, v''} R T where
--   out := ⟨(equiv R S).trans $ equiv S T⟩

suppress_compilation

namespace MoritaEquivalence

variable (A B : Type u) [Ring A] [Ring B] [Algebra R A] [Algebra R B]

-- def equiv (h : MoritaEquivalence R A B) : ModuleCat A ≌ ModuleCat B :=
--   h.eqv

-- instance (h : IsMoritaEquivalent ℤ R S) : (equiv R S h).functor.Additive :=
--     Functor.additive_of_preserves_binary_products _

-- instance (h : IsMoritaEquivalent ℤ R S) : (equiv R S h).inverse.Additive :=
--     inferInstance

instance (n : ℕ) [NeZero n]: Functor.Additive (moritaEquivalentToMatrix A (Fin n)).functor :=
  Functor.additive_of_preserves_binary_products _

instance (n : ℕ) [NeZero n] : Functor.Linear R (moritaEquivalentToMatrix A (Fin n)).functor where
  map_smul {M N} f r := by
    ext m
    simp [toModuleCatOverMatrix]
    ext i
    -- rw [LinearMap.smul_apply]
    -- simp only [moritaEquivalentToMatrix] at m
    -- erw [toModuleCatOverMatrix_obj_carrier] at m
    change (algebraMap R A r) • (f.hom _) = ((algebraMap R (Matrix (Fin (n)) (Fin (n)) A) r) • (fun i ↦  _)) i
    -- erw [Matrix.matrix_smul_vec_apply]
    change _ = ∑ _, _
    simp only [Matrix.algebraMap_matrix_apply, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]

-- attribute [-instance] Linear.preadditiveIntLinear Linear.preadditiveNatLinear in
def matrix (n : ℕ) : MoritaEquivalence R A (Matrix (Fin (n+1)) (Fin (n + 1)) A) :=
  letI : NeZero (n + 1) := ⟨by omega⟩
  { eqv :=
      moritaEquivalentToMatrix A _
    additive := inferInstance
    linear := inferInstance}
  -- additive := inferIns
  -- linear := _
  -- out := ⟨⟩

def matrix' (n : ℕ) [hn : NeZero n] : MoritaEquivalence R A (Matrix (Fin n) (Fin n) A) where
  eqv := moritaEquivalentToMatrix A _
end  MoritaEquivalence
-- abbrev ofIsoApp1 (e : R ≃+* S) (X : ModuleCat R): X ⟶
--     (ModuleCat.restrictScalars e.symm.toRingHom ⋙ ModuleCat.restrictScalars e.toRingHom).obj X :=
--   ModuleCat.ofHom (Y := (ModuleCat.restrictScalars e.symm.toRingHom ⋙
--     ModuleCat.restrictScalars e.toRingHom).obj X)
--     { toFun := LinearMap.id (R := R)
--       map_add' := fun _ _ ↦ rfl
--       map_smul' := fun r x ↦ by
--         change _ = X.isModule.smul _ x
--         simp; rfl }

-- abbrev ofIsoApp2 (e : R ≃+* S) (X : ModuleCat R): (ModuleCat.restrictScalars e.symm.toRingHom ⋙
--     ModuleCat.restrictScalars e.toRingHom).obj X ⟶ X :=
--   ModuleCat.ofHom (X := (ModuleCat.restrictScalars e.symm.toRingHom ⋙
--     ModuleCat.restrictScalars e.toRingHom).obj X)
--   { toFun := LinearMap.id (R := R)
--     map_add' := fun _ _ ↦ rfl
--     map_smul' := fun r x ↦ by
--       change X.isModule.smul _ x = _
--       simp; rfl }

-- lemma ofIso (e : R ≃+* S) : IsMoritaEquivalent.{u, u', v, v} R S where
--   out := .intro
--     { functor := ModuleCat.restrictScalars e.symm.toRingHom
--       inverse := ModuleCat.restrictScalars e.toRingHom
--       unitIso :=
--       { hom :=
--         { app := fun X => ofIsoApp1 R S e X
--           naturality := fun _ _ f => rfl }
--         inv :=
--         { app := fun X => ofIsoApp2 _ _ e X
--           naturality := fun _ _ f => rfl }
--         hom_inv_id := by ext; rfl
--         inv_hom_id := by ext; rfl }
--       counitIso :=
--       { hom :=
--         { app := fun X => ofIsoApp2 _ _ e.symm X
--           naturality := fun _ _ f => rfl }
--         inv :=
--         { app := fun X => ofIsoApp1 _ _ e.symm X
--           naturality := fun _ _ f => rfl }
--         hom_inv_id := by ext; rfl
--         inv_hom_id := by ext; rfl }
--       functor_unitIso_comp := by intros; ext; rfl }

namespace MoritaEquivalence

variable (A B : Type u) [DivisionRing A] [DivisionRing B] [Algebra R A] [Algebra R B]

instance : Algebra R (End (ModuleCat.of A A)) := inferInstance

@[simps]
def mopToEnd : Aᵐᵒᵖ →ₐ[R] End (ModuleCat.of A A) where
  toFun a := ModuleCat.ofHom <|
    { toFun := fun (x : A) ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by simp; rfl
  map_one' := by aesop
  map_add' := fun x y => by simp [mul_add]; rfl
  map_mul' := fun (x y) => by
    simp only [MulOpposite.unop_mul, End.mul_def]
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]; ext; simp
  commutes' := fun r ↦ by
    apply hom_ext
    simp
    ext
    simp
    change _ = (ModuleCat.ofHom _).hom 1
    rw [ModuleCat.hom_ofHom]
    simp
    change _ = algebraMap R A r * 1
    rw [mul_one]

-- variable [Algebra K R]

-- instance : Algebra K (End (ModuleCat.of R R)) where
--   smul k f := ModuleCat.ofHom <| k • f.hom
--   algebraMap := {
--     toFun := fun k ↦ ModuleCat.ofHom (algebraMap K (R →ₗ[R] R) k)
--     map_one' := by simp; rfl
--     map_mul' := fun k1 k2 ↦ by simp; rfl
--     map_zero' := by simp; rfl
--     map_add' := fun k1 k2 ↦ by simp; rfl
--   }
--   commutes' := fun k f ↦ by apply ModuleCat.hom_ext; simp; ext; simp
--   smul_def' := fun k f ↦ by apply ModuleCat.hom_ext; simp; ext; simp; rfl


-- @[simp]
-- def mopToEndAlgHom [Algebra K R]: Rᵐᵒᵖ →ₐ[K] End (ModuleCat.of R R) where
--   __ := mopToEnd R
--   commutes' := fun k ↦ by
--     apply ModuleCat.hom_ext
--     ext
--     simp
--     change _ = (ModuleCat.ofHom (algebraMap K (R →ₗ[R] R) k)).hom 1
--     rw [ModuleCat.hom_ofHom]
--     simp [Module.algebraMap_end_apply, Algebra.algebraMap_eq_smul_one]

lemma moptoend_bij : Function.Bijective (mopToEnd R A) :=
  ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr $
    SetLike.ext fun (α : Aᵐᵒᵖ) => ⟨fun (h : _ = _) => by
      rw [ModuleCat.hom_ext_iff] at h
      simp only [mopToEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ModuleCat.hom_zero,
        LinearMap.ext_iff, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, mul_eq_zero,
        MulOpposite.unop_eq_zero_iff] at h
      specialize h (1 : A)
      simp_all [one_ne_zero, false_or, Ideal.mem_bot],
      by rintro rfl; simp⟩, fun φ => ⟨MulOpposite.op (φ.hom.toFun (1 : A)), ModuleCat.hom_ext <|
      LinearMap.ext fun r => by
      simp only [AlgHom.toRingHom_eq_coe, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        RingHom.coe_coe, mopToEnd_apply_hom_apply, MulOpposite.unop_op]
      rw [← smul_eq_mul, ← φ.hom.map_smul, smul_eq_mul, mul_one]⟩⟩

-- noncomputable def mopEquivEnd : Rᵐᵒᵖ ≃+* End (ModuleCat.of R R) :=
--   RingEquiv.ofBijective (mopToEnd R) ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr $
--     SetLike.ext fun (α : Rᵐᵒᵖ) => ⟨fun (h : _ = _) => by
--       rw [ModuleCat.hom_ext_iff] at h
--       simp only [mopToEnd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ModuleCat.hom_zero,
--         LinearMap.ext_iff, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, mul_eq_zero,
--         MulOpposite.unop_eq_zero_iff] at h
--       specialize h (1 : R)
--       simp_all only [one_ne_zero, false_or, Ideal.mem_bot],
--       by rintro rfl; simp⟩, fun φ => ⟨MulOpposite.op (φ.hom.toFun (1 : R)), ModuleCat.hom_ext <|
--       LinearMap.ext fun r => by
--       simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, MulOpposite.unop_op,
--         mopToEnd_apply_hom_apply, MulOpposite.unop_op]
--       rw [← smul_eq_mul, ← φ.hom.map_smul, smul_eq_mul, mul_one]⟩⟩

noncomputable def mopAlgEquivEnd : Aᵐᵒᵖ ≃ₐ[R] End (ModuleCat.of A A) :=
  AlgEquiv.ofBijective (mopToEnd R A) <| moptoend_bij R A

variable (e : MoritaEquivalence R A B)

variable {R S} in
def aux1 : End (ModuleCat.of A A) ≃ₐ[R] End (e.eqv.functor.obj $ ModuleCat.of A A) where
  toFun f := e.eqv.functor.map f
  invFun g := e.eqv.unit.app _ ≫ e.eqv.inverse.map g ≫ e.eqv.unitInv.app _
  left_inv := by
    intro f
    simp only [Functor.comp_obj, Equivalence.inv_fun_map, Functor.id_obj, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    rw [← Category.assoc]
    change (e.eqv.unit ≫ e.eqv.unitInv).app _ ≫ _ = _
    simp
  right_inv := by
    intro g
    simp only [Functor.comp_obj, Functor.map_comp, Equivalence.fun_inv_map, Functor.id_obj,
      Category.assoc, Equivalence.counitInv_functor_comp, Category.comp_id]
    exact e.eqv.functor_unit_comp_assoc (ModuleCat.of A A) g
  map_mul' x y := by simp
  map_add' x y := by simp only; rw [e.eqv.functor.map_add]
  commutes' r := by
    simp only
    rw [Algebra.algebraMap_eq_smul_one, e.linear.map_smul, Algebra.algebraMap_eq_smul_one]
    simp only [End.one_def, CategoryTheory.Functor.map_id]
-- variable [Algebra K S]

-- instance (M : ModuleCat S): Module K M := Module.compHom M (algebraMap K S)

-- -- instance : Algebra K (End (e.functor.obj (ModuleCat.of R R))) :=
-- --     {__ := IsMoritaEquivalent.division_ring.instModuleCarrier
-- --     }

-- -- variable {R S} in
-- def aux1' : End (ModuleCat.of A A) ≃ₐ[R] End (e.functor.obj $ ModuleCat.of A A) := sorry



noncomputable def aux20 : (e.eqv.functor.obj (ModuleCat.of A A)) ≅ ModuleCat.of B B := by
  haveI : IsSimpleModule A A := by
    rw [@isSimpleModule_iff_finrank_eq_one, Module.finrank_self]
  have :  IsSimpleModule A (ModuleCat.of A A) := inferInstanceAs $ IsSimpleModule A A
  have : IsSimpleModule B (e.eqv.functor.obj (ModuleCat.of A A)) :=
    IsMoritaEquivalent.division_ring.IsSimpleModule.functor A B e.eqv (ModuleCat.of A A)
  -- haveI : Module B (e.eqv.functor.obj (ModuleCat.of A A)) := e.eqv.functor.obj (ModuleCat.of A A) |>.isModule
  have := IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule B
    (e.eqv.functor.obj $ ModuleCat.of A A)
  exact this.some.toModuleIso

def aux2 (M N : ModuleCat B) (f : M ≅ N) : End M ≃ₐ[R] End N where
  toFun x := f.inv ≫ x ≫ f.hom
  invFun x := f.hom ≫ x ≫ f.inv
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp
  map_add' x y := by simp only; rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    apply hom_ext
    ext n
    simp
    change f.hom.hom ((ModuleCat.ofHom _).hom (f.inv.hom n)) = (ModuleCat.ofHom _).hom n
    simp [ModuleCat.hom_ofHom]
    erw [map_smul f.hom.hom]
    simp
    rfl
    -- simp
    -- chan

noncomputable def toRingMopEquiv : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ :=
  mopAlgEquivEnd R A |>.trans $
    aux1 A B e |>.trans $
    aux2 _ _ _ _ (aux20 R A B e ) |>.trans $
    mopAlgEquivEnd R B |>.symm

noncomputable def toRingEquiv : A ≃ₐ[R] B where
  toFun r := toRingMopEquiv R A B e (.op r) |>.unop
  invFun s := toRingMopEquiv R A B e |>.symm (.op s) |>.unop
  left_inv r := by simp [MulOpposite.op_unop, RingEquiv.symm_apply_apply, MulOpposite.unop_op]
  right_inv s := by simp [MulOpposite.op_unop, RingEquiv.apply_symm_apply, MulOpposite.unop_op]
  map_mul' a b := by simp only [MulOpposite.op_mul, _root_.map_mul, MulOpposite.unop_mul]
  map_add' a b := by simp only [MulOpposite.op_add, map_add, MulOpposite.unop_add]
  commutes' r := by
    dsimp
    rw [show (MulOpposite.op <| algebraMap R A r) = algebraMap R Aᵐᵒᵖ r by rfl]
    rw [AlgEquiv.commutes, ]
    rfl

-- end division_ring

-- noncomputable def ringEquivOfDivisionRing
--     (R S : Type u) [DivisionRing R] [DivisionRing S] [IsMoritaEquivalent R S] :
--     R ≃+* S := division_ring.toRingEquiv R S (equiv R S)

noncomputable def algEquivOfDivisionRing (R : Type u) [CommRing R]
    (D₁ D₂: Type v) [DivisionRing D₁] [DivisionRing D₂] [Algebra R D₁] [Algebra R D₂]
    (e : MoritaEquivalence R D₁ D₂) : D₁ ≃ₐ[R] D₂ :=
    ModuleCat.MoritaEquivalence.toRingEquiv R D₁ D₂ e

end MoritaEquivalence
