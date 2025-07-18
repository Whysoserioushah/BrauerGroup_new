import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.TwoSidedIdeal.Basic

namespace TwoSidedIdeal
variable {R : Type*}

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] {I : TwoSidedIdeal R} {x : R}

lemma smul_mem (r : R) (hx : x ∈ I) : r • x ∈ I := by
  simpa using I.ringCon.mul (I.ringCon.refl r) hx

/-- Any two-sided-ideal in `A` corresponds to a two-sided-ideal in `Aᵒᵖ`. -/
@[simps]
def op (rel : TwoSidedIdeal R) : TwoSidedIdeal Rᵐᵒᵖ where
  ringCon.r a b := rel.ringCon b.unop a.unop
  ringCon.iseqv.refl a := rel.ringCon.refl a.unop
  ringCon.iseqv.symm := rel.ringCon.symm
  ringCon.iseqv.trans h1 h2 := rel.ringCon.trans h2 h1
  ringCon.mul' h1 h2 := rel.ringCon.mul h2 h1
  ringCon.add' := rel.ringCon.add

/-- Any two-sided-ideal in `Aᵒᵖ` corresponds to a two-sided-ideal in `A`. -/
@[simps]
def unop (rel : TwoSidedIdeal Rᵐᵒᵖ) : TwoSidedIdeal R where
  ringCon.r a b := rel.ringCon (.op b) (.op a)
  ringCon.iseqv.refl a := rel.ringCon.refl (.op a)
  ringCon.iseqv.symm := rel.ringCon.symm
  ringCon.iseqv.trans h1 h2 := rel.ringCon.trans h2 h1
  ringCon.mul' h1 h2 := rel.ringCon.mul h2 h1
  ringCon.add' := rel.ringCon.add

/-- Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other. -/
@[simps]
def opOrderIso : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {a b} := by
    constructor
    · intro h x H
      have := @h (.op x) (by simp only [op, mem_iff] at H ⊢; exact a.ringCon.symm H)
      simp [Equiv.coe_fn_mk, op, mem_iff, RingCon.rel_mk, Con.rel_mk] at this ⊢
      exact b.ringCon.symm this
    · intro h x H
      have := @h (x.unop) (by simp only [op, mem_iff] at H ⊢; exact a.ringCon.symm H)
      simp only [Equiv.coe_fn_mk, op, mem_iff, RingCon.rel_mk, Con.rel_mk] at this ⊢
      exact b.ringCon.symm this

end NonUnitalNonAssocRing

section Ring
variable [Ring R] {I : TwoSidedIdeal R}

instance : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; simp
  mul_smul x y z := by ext; simp [mul_assoc]
  smul_zero x := by ext; simp
  zero_smul x := by ext; simp
  add_smul x y z := by ext; simp [left_distrib]
  smul_add x y z := by ext; simp [right_distrib]

end Ring
end TwoSidedIdeal
