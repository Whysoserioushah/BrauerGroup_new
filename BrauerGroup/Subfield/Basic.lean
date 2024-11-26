import BrauerGroup.DoubleCentralizer
import Mathlib.Tactic
import Mathlib.RingTheory.Adjoin.Basic

universe u

suppress_compilation

open BigOperators TensorProduct MulOpposite

section def_and_lemmas

@[ext]
structure SubField (K A : Type u) [CommSemiring K] [Semiring A] [Algebra K A] extends Subalgebra K A where
  mul_comm : ∀ (x y : A), x ∈ carrier → y ∈ carrier → x * y = y * x
  inverse : ∀ (x : A), x ∈ carrier → x ≠ 0 → ∃(y : A), (y ∈ carrier ∧ x * y = 1)

/-- Reinterpret SubFields as `Subalgebras` -/
add_decl_doc SubField.toSubalgebra

instance (K A : Type u) [CommSemiring K] [Semiring A] [Algebra K A] : LE (SubField K A) where
  le := fun L1 L2 ↦ L1.1 ≤ L2.1

def IsMaximalSubfield (K A : Type u) [CommSemiring K] [Semiring A] [Algebra K A] (L : SubField K A) : Prop
  := ∀ (B : SubField K A), L ≤ B → B = L

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] [Nontrivial A]: Nonempty (SubField K A) :=
  have e : K ≃ₐ[K] (Algebra.ofId K A).range := AlgEquiv.ofBijective
    (Algebra.ofId K A).rangeRestrict ⟨by
      suffices Function.Injective (Algebra.ofId K A) from
        (AlgHom.injective_codRestrict (Algebra.ofId K A) (Algebra.ofId K A).range
          (AlgHom.mem_range_self (Algebra.ofId K A))).2 this
      exact NoZeroSMulDivisors.algebraMap_injective K A,
      AlgHom.rangeRestrict_surjective (Algebra.ofId K A)⟩
  ⟨⟨⊥, fun x y hx hy ↦ by
    change x ∈ (Algebra.ofId K A).range at hx
    change y ∈ (Algebra.ofId K A).range at hy
    suffices (⟨x, hx⟩ : (Algebra.ofId K A).range) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ from
      Subtype.ext_iff.1 this
    rw [← e.apply_symm_apply ⟨x, hx⟩, ← e.apply_symm_apply ⟨y, hy⟩, ← _root_.map_mul, mul_comm,
      _root_.map_mul], fun x hx hx0 ↦ ⟨e ((e.symm ⟨x, hx⟩)⁻¹), by
        change _ ∈ (Algebra.ofId K A).range; simp only [SetLike.coe_mem], by
    suffices (⟨x, hx⟩ : (Algebra.ofId K A).range) * ⟨e ((e.symm ⟨x, hx⟩)⁻¹), _⟩ = 1 from
      Subtype.ext_iff.1 this
    nth_rw 1 [← e.apply_symm_apply ⟨x, hx⟩, ← _root_.map_mul, mul_inv_cancel₀ _, map_one]
    simp only [ne_eq, EmbeddingLike.map_eq_zero_iff]
    exact Subtype.coe_ne_coe.1 hx0 ⟩⟩⟩

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] : PartialOrder (SubField K A) where
  le L1 L2:= L1 ≤ L2
  le_refl L := by change L.1 ≤ L.1 ; exact fun _ a ↦ a
  le_trans L1 L2 L3 hL12 hL23 := by
    change L1.1 ≤ L3.1 ; exact fun _ a ↦ hL23 (hL12 a)
  le_antisymm L1 L2 hL12 hL21 := by
    suffices L1.1 = L2.1 by
      ext a; exact ⟨fun a_1 ↦ hL12 (hL21 (hL12 a_1)), fun a_1 ↦ hL21 (hL12 (hL21 a_1))⟩
    exact (LE.le.le_iff_eq hL12).1 hL21|>.symm

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] : SetLike (SubField K A) A where
  coe L := L.1
  coe_injective' := fun L1 L2 hL12 ↦ by
    simp only [SetLike.coe_set_eq] at hL12
    have le : L1 ≤ L2 := by
      change L1.1 ≤ L2.1
      exact le_of_eq_of_le hL12 fun _ a ↦ a
    have ge : L2 ≤ L1 := by
      change L2.1 ≤ L1.1
      exact le_of_eq_of_le hL12.symm fun _ a ↦ a
    exact (LE.le.le_iff_eq le).1 ge|>.symm

end def_and_lemmas

section instances

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]

instance : SubringClass (SubField K A) A where
  mul_mem {s} := mul_mem (s := s.1)
  one_mem {s} := one_mem (s := s.1)
  add_mem {s} := add_mem (s := s.1)
  zero_mem {s} := zero_mem (s := s.1)
  neg_mem {s} := neg_mem (s := s.1)

namespace SubField
@[simp]
theorem mem_toSubring {L : SubField K A} {a : A} : a ∈ L.toSubring ↔ a ∈ L := Iff.rfl

theorem mem_carrier {L : SubField K A} {a : A} : a ∈ L.carrier ↔ a ∈ L := Iff.rfl

variable {K A} in
@[ext]
theorem ext' {L1 L2 : SubField K A} (h : ∀ x : A, x ∈ L1 ↔ x ∈ L2) :
    L1 = L2 := SetLike.ext h

@[simp]
theorem coe_toSubalgebra (L : SubField K A) : (L.toSubalgebra : Set A) = L := rfl

variable {K A} in
theorem toSubalgebra_injective :
    Function.Injective (SubField.toSubalgebra : SubField K A → Subalgebra K A) :=
  fun S T h => ext' fun x => by rw [← mem_toSubring, ← mem_toSubring, h]

theorem toSubalgebra_inj {S U : SubField K A} : S.toSubalgebra = U.toSubalgebra ↔ S = U :=
  toSubalgebra_injective.eq_iff

def toSubalgebra' : SubField K A ↪o Subalgebra K A where
  toEmbedding := {
    toFun := fun S => {S with}
    inj' := fun _ _ h => ext' fun x => SetLike.ext_iff.1 h x
  }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

variable {K A} in
instance (priority := low) algebra' {K' : Type u} [CommRing K'] [SMul K' K] [Algebra K' A]
    [IsScalarTower K' K A] (S : SubField K A): Algebra K' S :=
  S.toSubalgebra.algebra'

instance (S : SubField K A) : Algebra K S := S.algebra'

open scoped Classical in
instance (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A] (L : SubField K A) : Field L.1 := {
  __ := L
  mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext_iff.2 $ L.2 a b ha hb
  inv := fun ⟨x, hx⟩ ↦ if h0 : x = 0 then 0 else ⟨L.3 x hx h0|>.choose,
    L.3 x hx h0|>.choose_spec.1⟩
  exists_pair_ne := ⟨⟨0, Subalgebra.zero_mem L.1⟩, ⟨1, Subalgebra.one_mem L.1⟩, by
    refine Subtype.coe_ne_coe.1 $ by simp only [ne_eq, zero_ne_one, not_false_eq_true]⟩
  mul_inv_cancel := fun ⟨a, ha⟩ ha0 ↦ by
    unfold Inv.inv
    simp only [ZeroMemClass.coe_eq_zero, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SetLike.mem_coe, ha0, ↓reduceDIte, MulMemClass.mk_mul_mk]
    suffices a * (L.3 a ha (Subtype.coe_ne_coe.2 ha0)).choose = (1 : A) from
      Subtype.ext_iff.2 (by simp only [this, OneMemClass.coe_one])
    exact L.3 a ha (Subtype.coe_ne_coe.2 ha0)|>.choose_spec.2
  inv_zero := by
    simp only [ZeroMemClass.coe_eq_zero, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SetLike.mem_coe, ↓reduceDIte]
  nnqsmul := _
  qsmul := _
}

instance (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A] (L : SubField K A) : Field L :=
  inferInstanceAs (Field L.1)

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (L : SubField K A): FiniteDimensional K L :=
  FiniteDimensional.finiteDimensional_subalgebra L.1

end SubField

end instances
