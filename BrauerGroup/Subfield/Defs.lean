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
