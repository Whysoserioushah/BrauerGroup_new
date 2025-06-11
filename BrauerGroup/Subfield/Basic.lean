import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.CompletePartialOrder

universe u

suppress_compilation

open TensorProduct MulOpposite

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

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] [Nontrivial A] : Nonempty (SubField K A) :=
  have e : K ≃ₐ[K] (Algebra.ofId K A).range := AlgEquiv.ofBijective
    (Algebra.ofId K A).rangeRestrict ⟨by
      suffices Function.Injective (Algebra.ofId K A) from
        (AlgHom.injective_codRestrict (Algebra.ofId K A) (Algebra.ofId K A).range
          (AlgHom.mem_range_self (Algebra.ofId K A))).2 this
      exact FaithfulSMul.algebraMap_injective K A,
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

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] : Bot (SubField K A) where
  bot := ⟨⊥, by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩;
    simp [← map_mul];
    congr 1; exact CommMonoid.mul_comm x y,
    fun _ ↦ by
    rintro ⟨x, rfl⟩ hx
    use algebraMap K A x⁻¹
    simp [Algebra.ofId, ← map_mul]
    rw [mul_inv_cancel₀ (by aesop), map_one]⟩

lemma isMax_iff_isMaxSubfield (K A : Type u) [Field K] [Ring A] [Algebra K A] (L : SubField K A):
    IsMax L ↔ IsMaximalSubfield K A L :=
  ⟨fun hL _ hB ↦ (IsMax.eq_of_le hL hB).symm, fun hL B hB ↦ le_of_eq $ hL B hB⟩

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
instance (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A] (L : SubField K A) :
    Field L.1 where
  __ := L
  mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext_iff.2 $ L.2 a b ha hb
  inv := fun ⟨x, hx⟩ ↦ if h0 : x = 0 then 0 else ⟨L.3 x hx h0|>.choose,
    L.3 x hx h0|>.choose_spec.1⟩
  exists_pair_ne := ⟨⟨0, Subalgebra.zero_mem L.1⟩, ⟨1, Subalgebra.one_mem L.1⟩, by
    refine Subtype.coe_ne_coe.1 $ by simp only [ne_eq, zero_ne_one, not_false_eq_true]⟩
  mul_inv_cancel a ha := by ext; simpa [ha] using (L.3 a a.2 <| mod_cast ha).choose_spec.2
  inv_zero := by
    simp only [ZeroMemClass.coe_eq_zero, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SetLike.mem_coe, ↓reduceDIte]
  nnqsmul := _
  qsmul := _

instance (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A] (L : SubField K A) : Field L :=
  inferInstanceAs (Field L.1)

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (L : SubField K A): FiniteDimensional K L :=
  FiniteDimensional.finiteDimensional_subalgebra L.1

abbrev iSup_chain_subfield (D : Type u) [DivisionRing D] [Algebra K D] (α : Set (SubField K D))
    [Nonempty α] (hα : IsChain (· ≤ ·) α) : SubField K D where
  __ := (⨆ (L : α), L.1.1 : Subalgebra K D)
  mul_comm x y hx hy := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
      SetLike.mem_coe] at hx hy
    have := Subalgebra.coe_iSup_of_directed hα.directed
    dsimp at this
    change x ∈ (_ : Set _) at hx ; change _ ∈ ( _ : Set _) at hy
    rw [this] at hx hy
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx hy
    obtain ⟨L1, hL1, hx⟩ := hx
    obtain ⟨L2, hL2, hy⟩ := hy
    obtain ⟨L3, _, hL31, hL32⟩ := hα.directedOn L1 hL1 L2 hL2
    exact L3.mul_comm x y (hL31 hx) (hL32 hy)
  inverse x hx hx0 := by
    simp only [Subalgebra.coe_toSubsemiring,
      Subsemiring.coe_carrier_toSubmonoid, SetLike.mem_coe] at *
    letI : Nonempty α := Set.Nonempty.to_subtype (Set.Nonempty.of_subtype)
    have := Subalgebra.coe_iSup_of_directed hα.directed
    dsimp at this
    change x ∈ (_ : Set _) at hx
    rw [this] at hx
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
    obtain ⟨L1, hL1, hx⟩ := hx
    use L1.inverse x hx hx0|>.choose
    constructor
    · have : L1.1 ≤ ⨆ (L : α), (L.1).toSubalgebra := by
        exact le_iSup_of_le (ι := α) (f := fun x ↦ x.1.1) (a := L1.1) ⟨L1, hL1⟩ (by rfl)
      exact this (L1.inverse x hx hx0).choose_spec.1
    · exact L1.inverse x hx hx0|>.choose_spec.2

lemma exitsmaxsub (D : Type u) [DivisionRing D] [Algebra K D] :
    ∃ L : SubField K D, IsMaximalSubfield K D L := by
  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := SubField K D) fun α hα hα' ↦ by
    letI : Nonempty α := by exact Set.Nonempty.to_subtype hα'
    use iSup_chain_subfield K D α hα
    change iSup_chain_subfield K D α hα ∈ {L | _}
    simp only [Set.mem_setOf_eq]
    intro L hL
    change L.1 ≤ (⨆ (L : α), L.1.1 : Subalgebra K D)
    exact le_iSup_of_le ⟨L, hL⟩ le_rfl
  exact ⟨m, isMax_iff_isMaxSubfield _ _ _ |>.1 hm⟩

end SubField

end instances
