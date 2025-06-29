import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Instances
import Mathlib.RingTheory.TwoSidedIdeal.Operations

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι)
variable {R : Type*} [Ring R] (t : TwoSidedIdeal R)

open MulOpposite

namespace RingCon

@[elab_as_elim]
lemma quot_ind (r : RingCon R) {motive : r.Quotient → Prop}
  (basic : ∀ (x : R), motive (r.mk' x)) : ∀ (x : r.Quotient), motive x := by
  intro x
  induction x using Quotient.inductionOn' with | h x =>
  exact basic x

end RingCon

namespace TwoSidedIdeal

variable {t s}

variable (t)

variable (I : TwoSidedIdeal R)

lemma smul_mem (r : R) {x} (hx : x ∈ I) : r • x ∈ I := by
  simpa using I.ringCon.mul (I.ringCon.refl r) hx

/--
Any two-sided-ideal in `A` corresponds to a two-sided-ideal in `Aᵒᵖ`.
-/
@[simps]
def toMop (rel : TwoSidedIdeal R) : TwoSidedIdeal Rᵐᵒᵖ := .mk {
  r a b := rel.ringCon b.unop a.unop
  iseqv.refl a := rel.ringCon.refl a.unop
  iseqv.symm := rel.ringCon.symm
  iseqv.trans h1 h2 := rel.ringCon.trans h2 h1
  mul' h1 h2 := rel.ringCon.mul h2 h1
  add' := rel.ringCon.add
}

/--
Any two-sided-ideal in `Aᵒᵖ` corresponds to a two-sided-ideal in `A`.
-/
@[simps]
def fromMop (rel : TwoSidedIdeal Rᵐᵒᵖ) : TwoSidedIdeal R := .mk {
  r a b := rel.ringCon (.op b) (.op a)
  iseqv.refl a := rel.ringCon.refl (.op a)
  iseqv.symm := rel.ringCon.symm
  iseqv.trans h1 h2 := rel.ringCon.trans h2 h1
  mul' h1 h2 := rel.ringCon.mul h2 h1
  add' := rel.ringCon.add
}

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
def toMopOrderIso : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where
  toFun := toMop
  invFun := fromMop
  left_inv := unop_op
  right_inv := unop_op
  map_rel_iff' {a b} := by
    constructor
    · intro h x H
      have := @h (.op x) (by simp only [toMop, mem_iff] at H ⊢; exact a.ringCon.symm H)
      simp only [Equiv.coe_fn_mk, toMop, mem_iff, RingCon.rel_mk, Con.rel_mk, unop_zero,
        unop_op] at this ⊢
      exact b.ringCon.symm this
    · intro h x H
      have := @h (x.unop) (by simp only [toMop, mem_iff] at H ⊢; exact a.ringCon.symm H)
      simp only [Equiv.coe_fn_mk, toMop, mem_iff, RingCon.rel_mk, Con.rel_mk, unop_zero,
        unop_op] at this ⊢
      exact b.ringCon.symm this

variable {R' : Type*} [Ring R']

lemma comap_injective {F : Type*} [FunLike F R R'] [RingHomClass F R R']
    (f : F) (hf : Function.Surjective f) :
    Function.Injective (fun J : TwoSidedIdeal _ ↦ J.comap f) := by
  intro I J h
  refine SetLike.ext fun x ↦ ?_
  simp only [mem_comap] at h
  obtain ⟨x, rfl⟩ := hf x
  rw [← mem_comap, ← mem_comap, h]

instance : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; show x.1 * 1 = x.1; simp
  mul_smul x y z := by
    ext; show z.1 * (y.unop * x.unop) = (z.1 * y.unop) * x.unop; simp only [mul_assoc]
  smul_zero x := by
    ext ; show 0 * _ = 0; simp only [zero_mul]
  smul_add x y z := by
    ext ; show (y.1 + z.1) * _ = (y * _) + (z * _); simp only [right_distrib]
  add_smul x y z := by
    ext; show _ * (_ + _) = _ * _ + _ * _; simp only [left_distrib]
  zero_smul x := by
    ext ; show _ * 0 = 0; simp only [mul_zero]

-- lemma comap_comap
--     {S T : Type*} [Ring S] [Ring T]
--     (f : R →+* S) (g : S →+* T) (I : TwoSidedIdeal T) :
--   TwoSidedIdeal.comap f (TwoSidedIdeal.comap g I) = TwoSidedIdeal.comap (g.comp f) I := rfl

@[simp]
def orderIsoOfRingEquiv {F : Type*} [EquivLike F R R'] [RingEquivClass F R R'] (f : F) :
    TwoSidedIdeal R ≃o TwoSidedIdeal R' where
  toFun := comap (RingEquivClass.toRingEquiv f).symm
  invFun := comap (RingEquivClass.toRingEquiv f)
  left_inv I := by
    have :=
      TwoSidedIdeal.comap_comap (R := R) (S := R') I
        (RingEquivClass.toRingEquiv f) (RingEquivClass.toRingEquiv f).symm

    simp at this
    erw [TwoSidedIdeal.comap_comap _ (RingEquivClass.toRingEquiv f).toRingHom
      (RingEquivClass.toRingEquiv f).symm.toRingHom]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    rfl
  right_inv I := SetLike.ext $ fun x ↦ by
    simp only [mem_comap, RingEquiv.apply_symm_apply]
  map_rel_iff' := by
    intro I J
    rw [le_iff, le_iff]
    constructor
    · rintro h x hx

      specialize @h (RingEquivClass.toRingEquiv f x) (by simpa [TwoSidedIdeal.mem_comap])
      simpa [TwoSidedIdeal.mem_comap] using h
    · intro h x hx
      simp only [Equiv.coe_fn_mk, SetLike.mem_coe, mem_comap] at hx ⊢
      exact h hx

lemma injective_iff_ker_eq_bot {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (f : F) :
    Function.Injective f ↔ TwoSidedIdeal.ker f = ⊥ := by
  rw [Function.Injective, eq_bot_iff, le_iff]
  change _ ↔ ∀ _, _
  simp only [SetLike.mem_coe, mem_ker]
  constructor
  · intro h x hx
    specialize @h x 0 (by simpa using hx)
    rw [h]; rfl
  · intro h a b hab
    specialize h (a - b) (by rwa [map_sub, sub_eq_zero])
    rw [← sub_eq_zero]
    exact h

-- def span (s : Set R) : TwoSidedIdeal R :=
-- .mk $ ringConGen (fun a b ↦ a - b ∈ s)

-- lemma subset_span (s : Set R) : s ⊆ span s := by
--   intro x hx
--   rw [SetLike.mem_coe]
--   change ringConGen _ x 0
--   exact RingConGen.Rel.of _ _ (by simpa using hx)

def span' (s : Set R) : TwoSidedIdeal R := .mk'
  {x | ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * y i * xR i}
  ⟨Empty, Fintype.instEmpty, Empty.elim, Empty.elim, Empty.elim, by simp⟩
  (by
    rintro _ _ ⟨na, fina, xLa, xRa, ya, rfl⟩ ⟨nb, finb, xLb, xRb, yb, rfl⟩
    refine ⟨na ⊕ nb, inferInstance, Sum.elim xLa xLb, Sum.elim xRa xRb, Sum.elim ya yb, by
      simp⟩)
  (by
    rintro _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, -xL, xR, y, by simp⟩)
  (by
    rintro a _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, a • xL, xR, y, by
      rw [Finset.mul_sum]; simp only [mul_assoc, Pi.smul_apply, smul_eq_mul]⟩)
  (by
    rintro _ b ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, xL, fun x ↦ xR x * b, y, by simp [Finset.sum_mul, mul_assoc]⟩)

lemma mem_span'_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span' s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  simp only [span', mem_mk', Set.mem_setOf_eq]

lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  suffices eq1 : span s = span' s by
    rw [eq1]
    simp only [span', Set.mem_setOf_eq]
    generalize_proofs h1 h2 h3 h4 h5
    simp_all only [mem_mk', Set.mem_setOf_eq]

  rw [span, RingCon.ringConGen_eq]
  apply ringCon_injective
  refine sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · rintro I (hI : ∀ a b, _ → _)
    suffices span' s ≤ .mk I by
      rw [ringCon_le_iff] at this
      exact this
    intro x h
    rw [mem_span'_iff_exists_fin] at h
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := h
    rw [mem_iff]
    refine TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ ↦ TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ <| hI (y i) 0 (by simp))
  · rintro I hI
    exact ⟨(span' s).ringCon, fun a b H ↦ ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ ⟨a - b, by simp [H]⟩, by simp⟩, hI⟩

lemma mem_span_ideal_iff_exists_fin (s : Ideal R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, (y i : R) * xR i := by
  rw [mem_span_iff_exists_fin]
  fconstructor
  · rintro ⟨n, fin, xL, xR, y, rfl⟩
    exact ⟨n, fin, xR, fun i ↦ ⟨xL i * y i, s.mul_mem_left _ (y i).2⟩, by simp⟩
  · rintro ⟨n, fin, xR, y, rfl⟩
    exact ⟨n, fin, 1, xR, y, by simp⟩

lemma span_le {s : Set R} {I : TwoSidedIdeal R} : s ⊆ I ↔ span s ≤ I := by
  rw [le_iff]
  constructor
  · intro h x hx
    rw [SetLike.mem_coe, mem_span_iff_exists_fin] at hx
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := hx
    exact I.finsetSum_mem _ _ fun i _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ <| h (y i).2)
  · intro h x hx
    exact h <| subset_span hx

lemma coe_bot_set : ((⊥ : TwoSidedIdeal R) : Set R) = {0} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_singleton_iff]
  rfl

lemma coe_top_set : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_univ]
  rfl

section IsSimpleOrder

universe u

variable (A : Type u) [Ring A]

instance [Nontrivial A] : Nontrivial (TwoSidedIdeal A) :=
⟨⊥, ⊤, by
      apply_fun (fun I => I.ringCon 0 1)
      convert false_ne_true
      -- Change after https://github.com/leanprover-community/mathlib4/pull/12860
      simp only [iff_false]
      exact zero_ne_one⟩

lemma _root_.IsSimpleRing.iff_eq_zero_or_injective'
    (k : Type*) [CommRing k] [Algebra k A] [Nontrivial A] :
    IsSimpleRing A ↔
    ∀ ⦃B : Type u⦄ [Ring B] [Algebra k B] (f : A →ₐ[k] B),
      TwoSidedIdeal.ker f = ⊤ ∨ Function.Injective f := by
  classical
  constructor
  · intro so B _ _ f
    if hker : TwoSidedIdeal.ker f.toRingHom = ⊤
    then exact Or.inl hker
    else
      replace hker := so.1.2 (TwoSidedIdeal.ker f) |>.resolve_right hker
      rw [injective_iff_ker_eq_bot]
      exact Or.inr hker
  · intro h
    refine ⟨⟨fun I => ?_⟩⟩
    letI : Algebra k I.ringCon.Quotient :=
    { algebraMap := I.ringCon.mk'.comp (algebraMap k A)
      smul a := Quotient.map' (fun b => a • b) fun x y (h : I.ringCon x y) =>
        show I.ringCon _ _ by
        simp only
        rw [Algebra.smul_def, Algebra.smul_def]
        exact I.ringCon.mul (I.ringCon.refl (algebraMap k A a)) h
      commutes' := by
        simp only [RingHom.coe_comp, Function.comp_apply]
        intro a b
        induction b using Quotient.inductionOn' with
        | h b =>
          change _ * I.ringCon.mk' b = I.ringCon.mk' b * _
          simp only [← map_mul, Algebra.commutes a b]

      smul_def' := fun a b => by
        simp only [RingHom.coe_comp, Function.comp_apply]
        change Quotient.map' _ _ _ = _
        induction b using Quotient.inductionOn' with
        | h b =>
          change _ = _ * I.ringCon.mk' _
          simp only [Quotient.map'_mk'', ← map_mul, Algebra.smul_def]
          rfl }
    rcases @h I.ringCon.Quotient _ _ {I.ringCon.mk' with commutes' a := rfl } with h|h
    · right
      rw [eq_top_iff, le_iff]
      rintro x -
      simp only at h
      have mem : x ∈ TwoSidedIdeal.ker I.ringCon.mk' := by erw [h]; trivial
      rw [mem_ker] at mem
      change _ = I.ringCon.mk' 0 at mem
      exact I.ringCon.eq.mp mem
    · left
      rw [injective_iff_ker_eq_bot] at h
      rw [eq_bot_iff, le_iff]
      intro x hx
      have mem : x ∈ TwoSidedIdeal.ker I.ringCon.mk' := by
        rw [mem_ker]
        exact I.ringCon.eq.mpr hx
      erw [h] at mem
      exact mem

end IsSimpleOrder

end TwoSidedIdeal
