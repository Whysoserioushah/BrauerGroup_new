import Mathlib.Algebra.Algebra.Subalgebra.Basic

open Function TensorProduct MulOpposite

section def_and_lemmas

structure SubField (K A : Type*) [CommSemiring K] [Semiring A] [Algebra K A]
    extends Subalgebra K A where
  mul_comm ⦃x : A⦄ (hx : x ∈ carrier) ⦃y : A⦄ (hy : y ∈ carrier) : x * y = y * x
  exists_inverse ⦃x : A⦄ : x ∈ carrier → x ≠ 0 → ∃ y ∈ carrier, x * y = 1

/-- Reinterpret SubFields as `Subalgebras` -/
add_decl_doc SubField.toSubalgebra

namespace SubField
variable {K A : Type*}

section CommSemiring
variable [CommSemiring K] [Semiring A] [Algebra K A] {L L₁ L₂ : SubField K A} {a : A}

lemma toSubalgebra_injective : Injective (toSubalgebra : SubField K A → Subalgebra K A) := by
  rintro ⟨L⟩; congr!

@[simp] lemma toSubalgebra_inj : L₁.toSubalgebra = L₂.toSubalgebra ↔ L₁ = L₂ :=
  toSubalgebra_injective.eq_iff

instance : SetLike (SubField K A) A where
  coe L := L.1
  coe_injective' := SetLike.coe_injective.comp toSubalgebra_injective

@[simp] lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := .rfl
@[simp] lemma mem_toSubalgebra : a ∈ L.toSubalgebra ↔ a ∈ L := .rfl

@[simp] lemma coe_toSubalgebra (L : SubField K A) : (L.toSubalgebra : Set A) = L := rfl

@[ext] lemma ext (h : ∀ x, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ := SetLike.ext h

instance : SubsemiringClass (SubField K A) A where
  mul_mem {s} := mul_mem (s := s.1)
  one_mem {s} := one_mem (s := s.1)
  add_mem {s} := add_mem (s := s.1)
  zero_mem {s} := zero_mem (s := s.1)

instance (priority := low) algebra' {K' : Type*} [CommSemiring K'] [SMul K' K] [Algebra K' A]
    [IsScalarTower K' K A] (S : SubField K A) : Algebra K' S := S.toSubalgebra.algebra'

open scoped Classical in
noncomputable instance carrier.instSemifield [Nontrivial A] : Semifield L.1 where
  __ := L
  mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext_iff.2 $ L.2 ha hb
  inv := fun ⟨x, hx⟩ ↦ if h0 : x = 0 then 0 else ⟨L.3 hx h0|>.choose,
    L.3 hx h0|>.choose_spec.1⟩
  exists_pair_ne := ⟨⟨0, Subalgebra.zero_mem L.1⟩, ⟨1, Subalgebra.one_mem L.1⟩, by
    refine Subtype.coe_ne_coe.1 $ by simp only [ne_eq, zero_ne_one, not_false_eq_true]⟩
  mul_inv_cancel a ha := by ext; simpa [ha] using (L.3 a.2 <| mod_cast ha).choose_spec.2
  inv_zero := by
    simp only [ZeroMemClass.coe_eq_zero, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SetLike.mem_coe, ↓reduceDIte]
  nnqsmul := _

end CommSemiring

section CommRing
variable [CommRing K] [Ring A] [Algebra K A] {L : SubField K A} {a : A}

instance : SubringClass (SubField K A) A where
  mul_mem {s} := mul_mem (s := s.1)
  one_mem {s} := one_mem (s := s.1)
  add_mem {s} := add_mem (s := s.1)
  zero_mem {s} := zero_mem (s := s.1)
  neg_mem {s} := neg_mem (s := s.1)

@[simp] lemma mem_toSubring : a ∈ L.toSubring ↔ a ∈ L := .rfl
@[simp] lemma coe_toSubring (L : SubField K A) : (L.toSubring : Set A) = L := rfl

noncomputable instance carrier.instField [Nontrivial A] : Field L where
  __ : Ring L := inferInstance
  __ := carrier.instSemifield
  qsmul := _

end CommRing

section Semifield
variable [Semifield K] [Semiring A] [Algebra K A]

instance : Bot (SubField K A) where
  bot.toSubalgebra := ⊥
  bot.mul_comm := by simp [← map_mul, _root_.mul_comm]
  bot.exists_inverse := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, Algebra.coe_bot,
      Set.mem_range, ne_eq, exists_exists_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun x hx ↦ ⟨x⁻¹, by rw [← map_mul, mul_inv_cancel₀ (by aesop), map_one]⟩

instance : Nonempty (SubField K A) := ⟨⊥⟩

end Semifield
end SubField

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

lemma exists_subfield_isMax (D : Type*) [DivisionRing D] [Algebra ℝ D] :
    ∃ L : SubField ℝ D, IsMax L := by
  refine zorn_le_nonempty (α := SubField ℝ D) fun α hα hα' ↦ ?_
  letI : Nonempty α := by exact Set.Nonempty.to_subtype hα'
  use iSup_chain_subfield D α hα
  change (iSup_chain_subfield D α hα) ∈ {L | _}
  simp only [Set.mem_setOf_eq]
  intro L hL
  change L.1 ≤ (⨆ (L : α), L.1.1 : Subalgebra ℝ D)
  exact le_iSup_of_le (ι := α) (f := fun x ↦ x.1.1) (a := L.1) ⟨L, hL⟩ (by rfl) |>.trans <|
    by trivial
