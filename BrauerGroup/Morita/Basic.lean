/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe u v u₀

variable (R : Type u) [Ring R]

section

namespace Algebra

variable {S₀ : Type u₀} [CommRing S₀] {S : Type u} [Ring S] [Algebra S₀ S]

variable {M N : ModuleCat.{v} S}

/--
Let `S` be an `S₀`-algebra. Then `S`-modules are modules over `S₀`.
-/
scoped instance : Module S₀ M := Module.compHom _ (algebraMap S₀ S)

scoped instance : SMulCommClass S S₀ M :=
    { smul_comm s s₀ n :=
        show s • algebraMap S₀ S s₀ • n = algebraMap S₀ S s₀ • s • n by
        rw [← smul_assoc, smul_eq_mul, ← Algebra.commutes, mul_smul] }

/--
Let `S` be an `S₀`-algebra. Then the category of `S`-modules is `S₀`-linear.
-/
scoped instance instLinear : Linear S₀ (ModuleCat.{v} S) where
  smul_comp _ M N s₀ f g := by
    ext
    simp [show ∀ (m : M), s₀ • m = algebraMap S₀ S s₀ • m by intros; rfl,
      show ∀ (n : N), s₀ • n = algebraMap S₀ S s₀ • n by intros; rfl]

end Algebra

section

variable {S : Type u} [CommRing S]

instance : Linear S (ModuleCat.{v} S) := Algebra.instLinear

variable {X Y X' Y' : ModuleCat.{v} S}

theorem Iso.homCongr_eq_arrowCongr (i : X ≅ X') (j : Y ≅ Y') (f : X ⟶ Y) :
    Iso.homCongr i j f = (ModuleCat.ofHom <|
      LinearEquiv.arrowCongr (R := S) i.toLinearEquiv j.toLinearEquiv f.hom ):=
  rfl

theorem Iso.conj_eq_conj (i : X ≅ X') (f : End X) :
    Iso.conj i f = (ModuleCat.ofHom <| LinearEquiv.conj i.toLinearEquiv f.hom) :=
  rfl

end

end

variable {R} (M N : ModuleCat.{v} R)

/-- `ModuleCat.Hom.hom` as an isomorphism of monoids. -/
@[simps]
def endMulEquiv : End M ≃* (M →ₗ[R] M) where
  toFun := ModuleCat.Hom.hom
  invFun := ModuleCat.ofHom
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The scalar multiplication on an object of `ModuleCat R` considered as
a morphism of rings from `R` to the endomorphisms of the underlying abelian group. -/
def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGrp).obj M) where
  toFun r :=
    { toFun := fun (m : M) => r • m
      map_zero' := by dsimp; rw [smul_zero]
      map_add' := fun x y => by dsimp; rw [smul_add] }
  map_one' := AddMonoidHom.ext (fun x => by dsimp; rw [one_smul])
  map_zero' := AddMonoidHom.ext (fun x => by dsimp; rw [zero_smul]; rfl)
  map_mul' r s := AddMonoidHom.ext (fun (x : M) => (smul_smul r s x).symm)
  map_add' r s := AddMonoidHom.ext (fun (x : M) => add_smul r s x)

lemma smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGrp).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGrp).map f := by
  ext x
  exact (f.hom.map_smul r x).symm

variable (R)

/-- The scalar multiplication on `ModuleCat R` considered as a morphism of rings
to the endomorphisms of the forgetful functor to `AddCommGrp)`. -/
@[simps]
def smulNatTrans : R →+* End (forget₂ (ModuleCat R) AddCommGrp) where
  toFun r :=
    { app := fun M => M.smul r
      naturality := fun _ _ _ => smul_naturality _ r }
  map_one' := NatTrans.ext (by aesop_cat)
  map_zero' := NatTrans.ext (by aesop_cat)
  map_mul' _ _ := NatTrans.ext (by aesop_cat)
  map_add' _ _ := NatTrans.ext (by aesop_cat)

variable {R}

/-- Given `A : AddCommGrp` and a ring morphism `R →+* End A`, this is a type synonym
for `A`, on which we shall define a structure of `R`-module. -/
@[nolint unusedArguments]
def mkOfSMul' {A : AddCommGrp} (_ : R →+* End A) := A

section

variable {A : AddCommGrp} (φ : R →+* End A)

instance : AddCommGroup (mkOfSMul' φ) := by
  dsimp only [mkOfSMul']
  infer_instance

instance : SMul R (mkOfSMul' φ) := ⟨fun r (x : A) => (show A ⟶ A from φ r) x⟩

@[simp]
lemma mkOfSMul'_smul (r : R) (x : mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl

instance : Module R (mkOfSMul' φ) where
  smul_zero _ := map_zero (N := A) _
  smul_add _ _ _ := map_add (N := A) _ _ _
  one_smul := by simp
  mul_smul := by simp
  add_smul _ _ _ := by simp; rfl
  zero_smul := by simp

/-- Given `A : AddCommGrp` and a ring morphism `R →+* End A`, this is an object in
`ModuleCat R`, whose underlying abelian group is `A` and whose scalar multiplication is
given by `R`. -/
abbrev mkOfSMul := ModuleCat.of R (mkOfSMul' φ)

-- This lemma has always been bad, but https://github.com/leanprover/lean4/pull/2644 made `simp` start noticing
@[simp, nolint simpNF]
lemma mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl

end

section

variable {M N}
  (φ : (forget₂ (ModuleCat R) AddCommGrp).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrp).obj N)
  (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)

/-- Constructor for morphisms in `ModuleCat R` which takes as inputs
a morphism between the underlying objects in `AddCommGrp` and the compatibility
with the scalar multiplication. -/
@[simps]
def homMk : M ⟶ N := ModuleCat.ofHom <| {
  toFun := φ
  map_add' _ _ := φ.map_add _ _
  map_smul' r x := (congr_hom (hφ r) x).symm }

lemma forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGrp).map (homMk φ hφ) = φ := rfl

end

instance : (forget (ModuleCat.{v} R)).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso ((LinearEquiv.mk f.hom
      (asIso ((forget (ModuleCat R)).map f)).toEquiv.invFun
      (Equiv.left_inv _) (Equiv.right_inv _)).toModuleIso).hom)

instance : (forget₂ (ModuleCat.{v} R) AddCommGrp.{v}).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso ((forget _).map f) := by
      change IsIso ((forget _).map ((forget₂ _ AddCommGrp).map f))
      infer_instance
    apply isIso_of_reflects_iso _ (forget _)
