import BrauerGroup.Azumaya.Mul
import BrauerGroup.Morita.TensorProduct

universe u v

variable (R : Type u) [CommRing R]

open scoped TensorProduct
abbrev Azumaya.BrauerGroup := Quotient <| AzumayaSetoid R

noncomputable section

section Inv

open MulOpposite

abbrev Endmop (A : Type*) [Ring A] [Algebra R A] : Module.End R A →ₐ[R] Module.End R Aᵐᵒᵖ where
  toFun f := (opLinearEquiv R).toLinearMap ∘ₗ f ∘ₗ (opLinearEquiv R).symm.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

abbrev EndmopEquiv (A : Type*) [Ring A] [Algebra R A] : Module.End R A ≃ₐ[R] Module.End R Aᵐᵒᵖ :=
  AlgEquiv.ofBijective (Endmop R A) ⟨
  fun f1 f2 h ↦ by simpa using h, fun f ↦ ⟨(opLinearEquiv R).symm.toLinearMap ∘ₗ f ∘ₗ
    (opLinearEquiv R).toLinearMap, rfl⟩⟩


example (A : Type*) [Ring A] [Algebra R A] : Aᵐᵒᵖᵐᵒᵖ ≃ₐ[R] A := by
  exact (AlgEquiv.opOp R A).symm

    --  <| (AlgHom.mulLeftRight R A).comp <|
    -- ((Algebra.TensorProduct.congr (AlgEquiv.refl (A₁ := Aᵐᵒᵖ)) (AlgEquiv.opOp R A).symm).trans
    -- (Algebra.TensorProduct.comm _ _ _)).toAlgHom

/--
```
  A ⊗ Aᵐᵒᵖ -----------------> End R A
    ^                          |
    |                          |
Aᵐᵒᵖ ⊗ A                       |
    |                          |
    |                          V
Aᵐᵒᵖ⊗ Aᵐᵒᵖᵐᵒᵖ -------------> End R Aᵐᵒᵖ
```
-/
lemma Mopcomm_square (A : Type*) [Ring A] [Algebra R A] :
    AlgHom.mulLeftRight R Aᵐᵒᵖ = (EndmopEquiv R A|>.toAlgHom.comp <|
    (AlgHom.mulLeftRight R A).comp <|
    (Algebra.TensorProduct.comm R Aᵐᵒᵖ A).toAlgHom.comp <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl) (AlgEquiv.opOp R A).symm).toAlgHom) := by
  ext a a'
  · simp [-Algebra.lsmul_coe, AlgHom.mulLeftRight_apply]
  · simp [-Algebra.lsmul_coe, AlgHom.mulLeftRight_apply]

lemma mop_bij (A : Azumaya R) : Function.Bijective (AlgHom.mulLeftRight R Aᵐᵒᵖ) := by
  rw [Mopcomm_square R A]
  erw [Function.Bijective.of_comp_iff]
  · simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, AlgEquiv.coe_ofBijective,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Function.Bijective.of_comp_iff]
    · exact EndmopEquiv R A|>.bijective
    · rw [Function.Bijective.of_comp_iff]
      · exact IsAzumaya.bij
      · rw [Function.Bijective.of_comp_iff]
        · exact AlgEquiv.bijective _
        · exact AlgEquiv.bijective _
  · exact Function.Involutive.bijective (congrFun rfl)

abbrev Azumaya.Inv (A : Azumaya R) : Azumaya R :=
  {
    __ := AlgCat.of R Aᵐᵒᵖ
    isAzumaya := {
      out := Module.Projective.of_equiv (opLinearEquiv R)|>.out
      eq_of_smul_eq_smul := FaithfulSMul.of_injective _
          (opLinearEquiv R).injective|>.eq_of_smul_eq_smul
      fg_top := Module.Finite.of_surjective _ (opLinearEquiv R).surjective|>.fg_top
      bij := mop_bij R A
    }
  }

private abbrev ee : Module.End R R ≃ₐ[R] R where
  toFun f := f 1
  invFun r := Algebra.lsmul R R R r
  left_inv r := by ext; simp
  right_inv r := by simp
  map_mul' _ _ := by simp
  map_add' _ _ := rfl
  commutes' _ := by simp

lemma Azumaya.inv_mul (A : Azumaya R) :
    IsMoritaEquivalent R (Azumaya.mul R (Azumaya.Inv R A) A) 1 := by
  sorry

/--
A-Mod ≃ B-Mod => Mod-A ≃ Mod-B?

The proof of this is by:
(1) On a commutative ring, `M` is progenerator iff `M` is fg faithful projective.
(2) Let `S = End R (P)`, this makes `P` an `S`-mod
(3) `tr(P) := ⊔ f : Module.Dual R P, imf` is equal to `R` if `P` is generator which
    induces the equation `(1 : R) = ∑ qᵢ (pⱼ)` for some `qᵢ ∈ Module.Dual R P , pⱼ ∈ P`.
-/
lemma inv_eqv (A B : Azumaya R) (e : IsMoritaEquivalent R A B) :
    IsMoritaEquivalent R (Azumaya.Inv R A) (Azumaya.Inv R B) := by
  sorry

end Inv

instance : Mul (Azumaya.BrauerGroup R) where
  mul := Quotient.lift₂ (fun A B ↦ Quotient.mk _ (Azumaya.mul R A B))
    (fun A1 A2 B1 B2 h1 h2 ↦ by
      simp only [Quotient.eq]
      exact MoritaTensor _ _ _ _ _ h1 h2)

instance : One (Azumaya.BrauerGroup R) where
  one := Quotient.mk _ 1

instance : Monoid (Azumaya.BrauerGroup R) where
  mul_assoc A B C := by
    induction A using Quotient.inductionOn' with | h A
    induction B using Quotient.inductionOn' with | h B
    induction C using Quotient.inductionOn' with | h C
    apply Quotient.sound
    exact .of_algEquiv R (Algebra.TensorProduct.assoc ..)
  one_mul A := by
    induction A using Quotient.inductionOn' with | h A
    apply Quotient.sound
    exact .of_algEquiv R (Algebra.TensorProduct.lid _ _)
  mul_one A := by
    induction A using Quotient.inductionOn' with | h A
    apply Quotient.sound
    exact .of_algEquiv R (Algebra.TensorProduct.rid _ _ _)

instance : Inv (Azumaya.BrauerGroup R) where
  inv := Quotient.lift (fun A ↦ Quotient.mk'' (Azumaya.Inv R A)) fun A B h ↦ by
    simp only [Quotient.eq]
    change IsMoritaEquivalent R A B at h
    exact inv_eqv R _ _ h

instance : Group (Azumaya.BrauerGroup R) where
  inv_mul_cancel A := by
    induction A using Quotient.inductionOn' with | h A
    apply Quotient.sound
    exact Azumaya.inv_mul R A

end
