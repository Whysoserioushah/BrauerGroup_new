module

public import BrauerGroup.LinearAlgebra.Matrix.toLin
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct
public import Mathlib

/-!
## Multiplication in Brauer group
-/

@[expose] public section

universe w u v

variable {k : Type u} {A B : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Ring B] [Algebra k B] [FiniteDimensional k B]

open scoped TensorProduct

section mul_inv

lemma mulLeftRight_bijective_of_simple (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let e := algEquivMatrix (Module.finBasisOfFinrankEq k A hn)
  refine ⟨RingHom.injective _, LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight k A).toLinearMap) ?_|>.1 <| RingHom.injective _⟩
  simp [Module.End.finrank_eq, MulOpposite.finrank, pow_two]

@[stacks 074I]
noncomputable def centralSimpleTensorOp (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) : A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  (AlgEquiv.ofBijective _ (mulLeftRight_bijective_of_simple n hn)).trans <|
    algEquivMatrix (Module.finBasisOfFinrankEq k A hn)

end mul_inv

variable (k A) in
def BrauerGroup.mk [IsSimpleRing A] [Algebra.IsCentral k A] : BrauerGroup k :=
  Quotient.mk _ ⟨(.of k A)⟩

noncomputable def BrauerGroup.carrier (x : BrauerGroup k) := x.out

namespace BrauerGroup

lemma mk_eq_mk [IsSimpleRing B] [Algebra.IsCentral k B] [IsSimpleRing A]
    [Algebra.IsCentral k A] :
    BrauerGroup.mk k A = BrauerGroup.mk k B ↔ ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧ (Nonempty <|
      Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) := by
  rw [BrauerGroup.mk, BrauerGroup.mk, Quotient.eq]
  rfl

instance : One (BrauerGroup k) := ⟨BrauerGroup.mk k k⟩

lemma mk_self_eq_one : BrauerGroup.mk k k = 1 := rfl

lemma mk_matrix_eq_one (n : Type u) [Nonempty n] [Fintype n] [DecidableEq n] :
    mk k (Matrix n n k) = 1 := by
  rw [← mk_self_eq_one, mk_eq_mk]
  use 1, Fintype.card n, one_ne_zero, ne_of_gt Fintype.card_pos
  refine ⟨?_⟩
  have e1 := Matrix.uniqueAlgEquiv (m := Fin 1) (R := k) (A := Matrix n n k)
  refine AlgEquiv.trans ?_ <| Matrix.reindexAlgEquiv k k (Fintype.equivFin n)
  convert e1
  · with_reducible_and_instances rfl -- needs investigating
  · with_reducible_and_instances rfl

lemma induction (x : BrauerGroup k) (P : BrauerGroup k → Prop) (h : ∀ (A : Type v)
    [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A], P (mk k A)) : P x := by
  refine Quotient.inductionOn x fun C => ?_
  exact h C

variable {β : Sort w}

/-- Lift a function on central simple algebras that is invariant under Brauer equivalence
to a function out of the Brauer group. -/
def lift (f : CSA.{u, v} k → β)
    (hf : ∀ X Y : CSA.{u, v} k, IsBrauerEquivalent X Y → f X = f Y) :
    BrauerGroup k → β :=
  Quotient.lift f hf

@[simp]
lemma lift_mk (f : CSA.{u, v} k → β)
    (hf : ∀ X Y : CSA.{u, v} k, IsBrauerEquivalent X Y → f X = f Y)
    (A : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] :
    lift f hf (mk k A) = f ⟨.of k A⟩ :=
  rfl

/-- Lift a binary function on central simple algebras that is invariant under Brauer
equivalence in each argument to the Brauer group. Useful for defining multiplication via
`fun A B => mk k (A ⊗[k] B)`. -/
def lift_2 (f : CSA.{u, v} k → CSA.{u, v} k → β)
    (hf : ∀ X Y Z W : CSA.{u, v} k, IsBrauerEquivalent X Z → IsBrauerEquivalent Y W →
      f X Y = f Z W) :
    BrauerGroup k → BrauerGroup k → β :=
  Quotient.lift₂ f hf

@[simp]
lemma lift_2_mk (f : CSA.{u, v} k → CSA.{u, v} k → β)
    (hf : ∀ X Y Z W : CSA.{u, v} k, IsBrauerEquivalent X Z → IsBrauerEquivalent Y W →
      f X Y = f Z W)
    (A B : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] [Ring B] [Algebra k B] [FiniteDimensional k B] [IsSimpleRing B]
    [Algebra.IsCentral k B] :
    lift_2 f hf (mk k A) (mk k B) = f ⟨.of k A⟩ ⟨.of k B⟩ :=
  rfl

abbrev IsBrauerEquivalent' (A B : Type v) [Ring A] [Algebra k A]
    [Ring B] [Algebra k B] :=
  ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
      Nonempty (Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B)

lemma isBrauerEquivalent_tensor {A B C D : Type v}
    [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C] [Algebra k C] [Ring D] [Algebra k D]
    (hAC : IsBrauerEquivalent' (k := k) A C) (hBD : IsBrauerEquivalent' (k := k) B D) :
    IsBrauerEquivalent' (k := k) (A ⊗[k] B) (C ⊗[k] D) := by
  obtain ⟨n₁, m₁, hn₁, hm₁, ⟨e₁⟩⟩ := hAC
  obtain ⟨n₂, m₂, hn₂, hm₂, ⟨e₂⟩⟩ := hBD
  refine ⟨n₁ * n₂, m₁ * m₂, Nat.mul_ne_zero hn₁ hn₂, Nat.mul_ne_zero hm₁ hm₂, ⟨?_⟩⟩
  exact (Matrix.reindexAlgEquiv k _ (finProdFinEquiv (m := n₁) (n := n₂))).symm.trans <|
    (Matrix.kroneckerTMulAlgEquiv (m := Fin n₁) (n := Fin n₂) (R := k) (S := k)
      (A := A) (B := B)).symm.trans <|
    (Algebra.TensorProduct.congr e₁ e₂).trans <|
    (Matrix.kroneckerTMulAlgEquiv (m := Fin m₁) (n := Fin m₂) (R := k) (S := k)
      (A := C) (B := D)).trans <|
    Matrix.reindexAlgEquiv k _ (finProdFinEquiv (m := m₁) (n := m₂))

instance : Mul (BrauerGroup k) where
  mul x y := sorry

section group

end group

end BrauerGroup
