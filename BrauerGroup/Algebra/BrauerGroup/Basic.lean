module

public import BrauerGroup.Algebra.Central.TensorProduct
public import BrauerGroup.LinearAlgebra.Matrix.ToLin
public import BrauerGroup.RingTheory.SimpleRing.TensorProduct
public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.SimpleRing.Matrix

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
  simp [Module.finrank_linearMap, MulOpposite.finrank]

@[stacks 074I]
noncomputable def centralSimpleTensorOp (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) : A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  (AlgEquiv.ofBijective _ (mulLeftRight_bijective_of_simple n hn)).trans <|
    algEquivMatrix (Module.finBasisOfFinrankEq k A hn)

noncomputable def opTensorCentralSimple (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) : Aᵐᵒᵖ ⊗[k] A ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  Algebra.TensorProduct.comm k Aᵐᵒᵖ A |>.trans <| centralSimpleTensorOp n hn

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

lemma mk_congr [IsSimpleRing B] [Algebra.IsCentral k B] [IsSimpleRing A]
    [Algebra.IsCentral k A] (e : A ≃ₐ[k] B) :
    BrauerGroup.mk k A = BrauerGroup.mk k B := by
  rw [mk_eq_mk]
  use 1, 1, one_ne_zero, one_ne_zero
  exact ⟨AlgEquiv.mapMatrix e⟩

instance : One (BrauerGroup k) := ⟨BrauerGroup.mk k k⟩

lemma mk_self_eq_one : BrauerGroup.mk k k = 1 := rfl

lemma mk_matrix_eq_one (n : Type) [Nonempty n] [Fintype n] [DecidableEq n] :
    mk k (Matrix n n k) = 1 := by
  rw [← mk_self_eq_one, mk_eq_mk]
  use 1, Fintype.card n, one_ne_zero, ne_of_gt Fintype.card_pos
  refine ⟨?_⟩
  have e1 := Matrix.uniqueAlgEquiv (m := Fin 1) (R := k) (A := Matrix n n k)
  refine AlgEquiv.trans ?_ <| Matrix.reindexAlgEquiv k k (Fintype.equivFin n)
  convert e1
  · with_reducible_and_instances rfl -- decidableEq_of_subsingleton should not be an instance
  · with_reducible_and_instances rfl

@[elab_as_elim]
protected theorem induction (x : BrauerGroup k) (P : BrauerGroup k → Prop) (h : ∀ (A : Type v)
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
def lift₂ (f : CSA.{u, v} k → CSA.{u, v} k → β)
    (hf : ∀ X Y Z W : CSA.{u, v} k, IsBrauerEquivalent X Z → IsBrauerEquivalent Y W →
      f X Y = f Z W) :
    BrauerGroup k → BrauerGroup k → β :=
  Quotient.lift₂ f hf

@[simp]
lemma lift₂_mk (f : CSA.{u, v} k → CSA.{u, v} k → β)
    (hf : ∀ X Y Z W : CSA.{u, v} k, IsBrauerEquivalent X Z → IsBrauerEquivalent Y W →
      f X Y = f Z W)
    (A B : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] [Ring B] [Algebra k B] [FiniteDimensional k B] [IsSimpleRing B]
    [Algebra.IsCentral k B] :
    lift₂ f hf (mk k A) (mk k B) = f ⟨.of k A⟩ ⟨.of k B⟩ :=
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
  mul := BrauerGroup.lift₂ (fun A ↦ fun B ↦ BrauerGroup.mk k (A ⊗[k] B)) fun A B C D h1 h2 ↦ by
    rw [mk_eq_mk]
    exact isBrauerEquivalent_tensor h1 h2

lemma mk_mul_mk (A B : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] [Ring B] [Algebra k B] [FiniteDimensional k B] [IsSimpleRing B]
    [Algebra.IsCentral k B] :
    BrauerGroup.mk k A * BrauerGroup.mk k B = BrauerGroup.mk k (A ⊗[k] B) := rfl

lemma mul_one' (x : BrauerGroup k) : x * 1 = x := by
  induction x using BrauerGroup.induction with | h A =>
  rw [← mk_self_eq_one, mk_mul_mk]
  exact mk_congr (Algebra.TensorProduct.rid _ _ _)

lemma one_mul' (x : BrauerGroup k) : 1 * x = x := by
  induction x using BrauerGroup.induction with | h A =>
  rw [← mk_self_eq_one, mk_mul_mk]
  exact mk_congr (Algebra.TensorProduct.lid _ _)

lemma mul_assoc' (x y z : BrauerGroup k) : x * y * z = x * (y * z) := by
  induction x using BrauerGroup.induction with | h A =>
  induction y using BrauerGroup.induction with | h B =>
  induction z using BrauerGroup.induction with | h C =>
  rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk]
  exact mk_congr (Algebra.TensorProduct.assoc ..)

instance : Inv (BrauerGroup k) where
  inv := BrauerGroup.lift (fun A ↦ BrauerGroup.mk k Aᵐᵒᵖ) fun A B h ↦ by
    rw [mk_eq_mk]
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
    refine ⟨n, m, hn, hm, ⟨?_⟩⟩
    exact AlgEquiv.mopMatrix.trans <| e.op.trans AlgEquiv.mopMatrix.symm

lemma mk_inv (A : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSimpleRing A] [Algebra.IsCentral k A] :
    (BrauerGroup.mk k A)⁻¹ = BrauerGroup.mk k Aᵐᵒᵖ := rfl

lemma inv_mul_cancel' (x : BrauerGroup k) : x⁻¹ * x = 1 := by
  induction x using BrauerGroup.induction with | h A =>
  have : NeZero (Module.finrank k A) := ⟨ne_of_gt Module.finrank_pos⟩
  rw [mk_inv, mk_mul_mk, ← mk_matrix_eq_one (k := k) (Fin (Module.finrank k A))]
  exact mk_congr <| opTensorCentralSimple _ rfl

lemma mul_comm' (x y : BrauerGroup k) : x * y = y * x := by
  induction x using BrauerGroup.induction with | h A =>
  induction y using BrauerGroup.induction with | h B =>
  rw [mk_mul_mk, mk_mul_mk]
  exact mk_congr (Algebra.TensorProduct.comm _ _ _)

instance : CommGroup (BrauerGroup k) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'
  mul_comm := mul_comm'

set_option pp.universes true in
protected def map (L : Type*) [Field L] [Algebra k L] (h : ∀ (A B : CSA k),
    IsBrauerEquivalent A B → IsBrauerEquivalent (K := L) (.mk (.of L (L ⊗[k] A)))
    (.mk (.of L (L ⊗[k] B)))) :
    BrauerGroup k → BrauerGroup L := Quotient.map _ h

lemma map_mk (L : Type*) [Field L] [Algebra k L] (h : ∀ (A B : CSA k),
    IsBrauerEquivalent A B → IsBrauerEquivalent (K := L) (.mk (.of L (L ⊗[k] A)))
    (.mk (.of L (L ⊗[k] B)))) (A : Type v) [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSimpleRing A] [Algebra.IsCentral k A] :
    BrauerGroup.map L h (BrauerGroup.mk k A) = BrauerGroup.mk L (L ⊗[k] A) := rfl

end BrauerGroup
