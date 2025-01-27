import BrauerGroup.Azumaya.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite

suppress_compilation

universe u v

variable (R : Type u) [CommRing R]

open TensorProduct MulOpposite

structure Azumaya (R : Type u) [CommRing R] extends AlgebraCat R where
  isAzumaya : IsAzumaya R carrier

@[coe]
instance : CoeSort (Azumaya R) (Type v) where
  coe s := s.carrier

attribute [instance] Azumaya.isAzumaya

def Azumaya.IsMoritaEquivalent : Azumaya R → Azumaya R → Prop :=
    fun A B ↦ _root_.IsMoritaEquivalent R A.carrier B.carrier

lemma Azumaya.IsMoritaEquivalent.iff {A B : Azumaya R} :
  Azumaya.IsMoritaEquivalent R A B ↔ _root_.IsMoritaEquivalent R A.carrier B.carrier :=
  Iff.rfl

abbrev AzuMorita.equiv : Equivalence (Azumaya.IsMoritaEquivalent R) where
  refl _ := Azumaya.IsMoritaEquivalent.iff R|>.2 <| ModuleCat.IsMoritaEquivalent.refl R
  symm h := Azumaya.IsMoritaEquivalent.iff R|>.2 <| ModuleCat.IsMoritaEquivalent.symm R
    <| Azumaya.IsMoritaEquivalent.iff R|>.1 h
  trans h1 h2 := Azumaya.IsMoritaEquivalent.iff R|>.2 <| ModuleCat.IsMoritaEquivalent.trans R
    (Azumaya.IsMoritaEquivalent.iff R|>.2 h1) <| Azumaya.IsMoritaEquivalent.iff R|>.2 h2

abbrev AzumayaSetoid : Setoid (Azumaya R) where
  r := Azumaya.IsMoritaEquivalent R
  iseqv := AzuMorita.equiv R

namespace Azumaya

variable (A B : Type v) [Ring A] [Ring B] [Algebra R A] [Algebra R B]
instance [Module.Finite R A] [Module.Finite R B] :
    Module.Finite R (A ⊗[R] B) := by exact Module.Finite.tensorProduct R A B

variable {R A B} in
instance FathfulSMul.tensor [Module.Projective R A] [Module.Projective R B]
    [FaithfulSMul R A] [FaithfulSMul R B] :
    FaithfulSMul R (A ⊗[R] B) where
  eq_of_smul_eq_smul {r1 r2} eq := by
    specialize eq 1
    rw [Algebra.TensorProduct.one_def, smul_tmul', smul_tmul'] at eq
    have := Algebra.TensorProduct.includeLeft_injective (R := R) (S := R)
      (fun r1 r2 h ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
        exact eq_of_smul_eq_smul (M := R) (α := B) (m₁ := r1) (m₂ := r2) (by
          intro b
          rw [← one_mul b, ← smul_mul_assoc, h, smul_mul_assoc, one_mul])) eq
    exact eq_of_smul_eq_smul (M := R) (α := A) (m₁ := r1) (m₂ := r2) <|
      fun a ↦ by rw [← one_mul a, ← smul_mul_assoc, this, smul_mul_assoc, one_mul]

def Endtensor_aux : Module.End R A →ₗ[R] Module.End R B →ₗ[R] Module.End R (A ⊗[R] B) where
  toFun f := {
    toFun := fun g ↦ TensorProduct.map f g
    map_add' := fun _ _ ↦ by ext; simp [tmul_add]
    map_smul' := fun r g ↦ by ext; simp
  }
  map_add' f1 f2 := by ext; simp [add_tmul]
  map_smul' r f := by ext; simp [smul_tmul']

@[simp]
lemma Endtensor_aux_apply (f : Module.End R A) (g : Module.End R B) :
  Endtensor_aux R A B f g  = TensorProduct.map f g := rfl

@[simp]
lemma Endtensor_aux_apply' (f : Module.End R A) (g : Module.End R B) (a : A) (b : B) :
  (Endtensor_aux R A B f g) (a ⊗ₜ b) = f a ⊗ₜ g b := rfl

abbrev Endtensor_algHom : Module.End R A ⊗[R] Module.End R B →ₐ[R] Module.End R (A ⊗[R] B) where
  toFun := TensorProduct.lift <| Endtensor_aux R A B
  map_one' := by simp [Algebra.TensorProduct.one_def]
  map_mul' := fun x y ↦ by
    ext a b
    simp
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f1 g1 =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f2 g2 => simp
      | add _ _ _ _ => simp_all [mul_add]
    | add _ _ _ _ => simp_all [add_mul]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by ext; simp [smul_tmul']

abbrev Endtensor_equiv [Module.Finite R A] [Module.Finite R B] [Module.Projective R A]
  [Module.Projective R B]: Module.End R A ⊗[R] Module.End R B ≃ₐ[R] Module.End R (A ⊗[R] B) := sorry

-- lemma tensor_bij (A B : Azumaya R): Function.Bijective (AlgHom.mulLeftRight R (A ⊗[R] B)) :=
--   ⟨fun abab1 abab2 h ↦ by
--   induction abab1 using TensorProduct.induction_on with
--   | zero =>
--     induction abab2 using TensorProduct.induction_on with
--     | zero => rfl
--     | tmul ab2 ab2' =>
--       rw [DFunLike.ext_iff] at h
--       specialize h 1
--       simp only [map_zero, Algebra.TensorProduct.one_def, LinearMap.zero_apply,
--         AlgHom.mulLeftRight_apply] at h
--       induction ab2 using TensorProduct.induction_on with
--       | zero => exact zero_tmul _ _ |>.symm
--       | tmul a1 b1 =>
--         -- set ab22 := unop ab2'
--         -- change 0 = _ ⊗ₜ op ab22
--         -- induction ab2' using TensorProduct.induction_on with
--         -- | zero => rw [op_zero, tmul_zero]
--         -- | tmul a' b' =>
--         --   rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one] at h
--         --   -- change 0 = (a1 ⊗ₜ b1) * (a' ⊗ₜ b') at h


--         --   sorry
--         -- | add _ _ _ _ =>
--         sorry
--       | add _ _ _ _ => sorry
--     | add _ _ _ _ => sorry
--   | tmul ab ab' => sorry
--   | add _ _ _ _ => sorry
--   , sorry⟩

def mul (A B : Azumaya R) : Azumaya R := {
  __ := AlgebraCat.of R (A.carrier ⊗[R] B.carrier)
  isAzumaya := {
    out := Module.Projective.tensorProduct|>.out
    eq_of_smul_eq_smul := Azumaya.FathfulSMul.tensor|>.eq_of_smul_eq_smul
    fg_top := Module.Finite.tensorProduct R A B|>.fg_top
    bij := by
      sorry
  }}

end Azumaya
