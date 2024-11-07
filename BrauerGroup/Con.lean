import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Algebra.Hom

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι)
variable {R : Type*} [Ring R] (t : TwoSidedIdeal R)

open BigOperators MulOpposite

namespace AddCon

variable {r s}

lemma sum {f g : ι → M} (h : ∀ i ∈ s, r (f i) (g i)) :
    r (∑ i in s, f i) (∑ i in s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r.refl 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact r.add (h _ (by simp)) <| ih fun i hi ↦ h _ (by aesop)

end AddCon

namespace TwoSidedIdeal

variable {t s}

lemma sum {f g : ι → R} (h : ∀ i ∈ s, t.ringCon (f i) (g i)) :
    t.ringCon (∑ i in s, f i) (∑ i in s, g i) :=
  t.ringCon.toAddCon.sum h

variable (t)

-- /--
-- An alternative constructor for `RingCon`, making it obvious that we are view it as a
-- two-sided-ideal.
-- -/
-- @[simps]
-- def fromIdeal
--     (carrier : Set R)
--     (zero : 0 ∈ carrier)
--     (add : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
--     (neg : ∀ a, a ∈ carrier → -a ∈ carrier)
--     (left_absorb : ∀ a b, b ∈ carrier → a * b ∈ carrier)
--     (right_absorb : ∀ a b, a ∈ carrier → a * b ∈ carrier) : RingCon R where
--   r a b := a - b ∈ carrier
--   iseqv :=
--   { refl := fun a ↦ by simpa
--     symm := fun {x y} h ↦ by
--       simpa only [show y - x = -(x - y) by abel] using neg _ h
--     trans := fun {a b c } h1 h2 ↦ by
--       simpa only [show a - c = (a - b) + (b - c) by abel] using add _ _ h1 h2 }
--   mul' {a b c d} h1 h2 := show _ - _ ∈ _ by
--     change a * c - b * d ∈ carrier
--     rw [show a * c - b * d = (a - b) * c + b * (c - d) by
--       rw [sub_mul, mul_sub]; aesop]
--     exact add _ _ (right_absorb _ _ h1) (left_absorb _ _ h2)
--   add' {a b c d} h1 h2 := by
--     change (a + c) - (b + d) ∈ carrier
--     rw [show (a + c) - (b + d) = (a - b) + (c - d) by abel]
--     exact add _ _ h1 h2

-- @[simp] lemma mem_fromIdeal
--     (carrier : Set R)
--     (zero : 0 ∈ carrier)
--     (add : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
--     (neg : ∀ a, a ∈ carrier → -a ∈ carrier)
--     (left_absorb : ∀ a b, b ∈ carrier → a * b ∈ carrier)
--     (right_absorb : ∀ a b, a ∈ carrier → a * b ∈ carrier)
--     (x) :
--     x ∈ fromIdeal carrier zero add neg left_absorb right_absorb ↔ x ∈ carrier := by
--   simp only [fromIdeal]
--   change _ ∈ carrier ↔ _
--   rw [sub_zero]

variable (I : TwoSidedIdeal R)

lemma smul_mem (r : R) {x} (hx : x ∈ I) : r • x ∈ I := by
  simpa using I.ringCon.mul (I.ringCon.refl r) hx

lemma sum_mem (f : ι → R) (h : ∀ i ∈ s, f i ∈ I) : ∑ i in s, f i ∈ I := by
  simpa using I.sum h

/--
Any two-sided-ideal in `A` corresponds to a two-sided-ideal in `Aᵒᵖ`.
-/
@[simps]
def toMop (rel : TwoSidedIdeal R) : (TwoSidedIdeal Rᵐᵒᵖ) :=
.mk
{ r := fun a b ↦ rel.ringCon b.unop a.unop
  iseqv :=
  { refl := fun a ↦ rel.ringCon.refl a.unop
    symm := rel.ringCon.symm
    trans := fun h1 h2 ↦ rel.ringCon.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.ringCon.mul h2 h1
  add' := rel.ringCon.add }

/--
Any two-sided-ideal in `Aᵒᵖ` corresponds to a two-sided-ideal in `A`.
-/
@[simps]
def fromMop (rel : TwoSidedIdeal Rᵐᵒᵖ) : (TwoSidedIdeal R) :=
.mk
{ r := fun a b ↦ rel.ringCon (op b) (op a)
  iseqv :=
  { refl := fun a ↦ rel.ringCon.refl (op a)
    symm := rel.ringCon.symm
    trans := fun h1 h2 ↦ rel.ringCon.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.ringCon.mul h2 h1
  add' := rel.ringCon.add }

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
def toMopOrderIso : (TwoSidedIdeal R) ≃o (TwoSidedIdeal Rᵐᵒᵖ) where
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

-- /--
-- Pulling back a RingCon across a ring hom.
-- -/
-- @[simps!]
-- def comap {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (J : TwoSidedIdeal R') (f : F) :
--     TwoSidedIdeal R :=
--   .mk {
--     __ := J.ringCon.toCon.comap f (map_mul f)
--     __ := J.ringCon.toAddCon.comap f (map_add f)
--     }

-- @[simp] lemma mem_comap {F : Type*} [FunLike F R R'] [RingHomClass F R R']
--     (J : TwoSidedIdeal R') (f : F) (x) :
--     x ∈ J.comap f ↔ f x ∈ J := by
--   change J.ringCon (f x) (f 0) ↔ J.ringCon (f x) 0
--   simp

lemma comap_injective {F : Type*} [FunLike F R R'] [RingHomClass F R R']
    (f : F) (hf : Function.Surjective f) :
    Function.Injective (fun J : TwoSidedIdeal _ ↦ J.comap f) := by
  intro I J h
  refine SetLike.ext fun x => ?_
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

@[simp]
def orderIsoOfRingEquiv {F : Type*} [EquivLike F R R'] [RingEquivClass F R R'] (f : F) :
    TwoSidedIdeal R ≃o TwoSidedIdeal R' := sorry
  -- toFun := (comap · (RingEquivClass.toRingEquiv f).symm)
  -- invFun := (comap · (RingEquivClass.toRingEquiv f))
  -- left_inv := fun I => SetLike.ext $ fun x => by simp
  -- right_inv := fun I => SetLike.ext $ fun x => by simp
  -- map_rel_iff' := by
  --   intro I J
  --   rw [le_iff, le_iff]
  --   constructor
  --   · rintro h x hx
  --     specialize @h (RingEquivClass.toRingEquiv f x) (by simpa using hx)
  --     simpa using h
  --   · intro h x hx
  --     simp only [Equiv.coe_fn_mk, SetLike.mem_coe, mem_comap] at hx ⊢
  --     exact h hx

-- protected def ker {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (f : F) :
--     TwoSidedIdeal R :=
--   .mk' {x | f x = 0} (map_zero f)
--     (fun {a b} ha hb => show f (a + b) = 0 by rw [map_add f, ha, hb, zero_add])
--     (fun {a} ha => show f (-a) = 0 by rw [map_neg f, ha, neg_zero])
--     (fun {a b} hb => show f (a * b) = 0 by rw [map_mul f, hb, mul_zero])
--     (fun {a b} ha => show f (a * b) = 0 by rw [map_mul f, ha, zero_mul])

-- @[simp]
-- lemma mem_ker {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (f : F) (x) :
--     x ∈ TwoSidedIdeal.ker f ↔ f x = 0 := by
--       simp only [TwoSidedIdeal.ker, mem_mk']
--       generalize_proofs h1 h2 h3 h4 h5
--       aesop

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
    -- rw [le_iff]
    suffices span' s ≤ .mk I by
      rw [ringCon_le_iff] at this
      exact this
    intro x h
    rw [mem_span'_iff_exists_fin] at h
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := h
    rw [mem_iff]
    refine TwoSidedIdeal.sum_mem _ _ fun i _ ↦ TwoSidedIdeal.mul_mem_right _ _ _
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
    exact I.sum_mem _ fun i _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ <| h (y i).2)
  · intro h x hx
    exact h $ subset_span hx

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

instance [so : IsSimpleOrder (TwoSidedIdeal A)] : Nontrivial A := by
  refine subsingleton_or_nontrivial A |>.resolve_left fun r => ?_
  obtain ⟨x, y, hxy⟩ := so.1
  exact hxy $ SetLike.ext fun a => (show a = 0 from Subsingleton.elim _ _) ▸
    by simp [TwoSidedIdeal.zero_mem]

instance [Nontrivial A] : Nontrivial (TwoSidedIdeal A) :=
⟨⊥, ⊤, by
      apply_fun (fun I => I.ringCon 0 1)
      convert false_ne_true
      -- Change after https://github.com/leanprover-community/mathlib4/pull/12860
      simp only [iff_false]
      exact zero_ne_one⟩

lemma eq_bot_or_eq_top [so : IsSimpleOrder (TwoSidedIdeal A)] (I : TwoSidedIdeal A) :
    I = ⊥ ∨ I = ⊤ := so.2 I

lemma IsSimpleOrder.iff_eq_zero_or_injective [Nontrivial A] :
    IsSimpleOrder (TwoSidedIdeal A) ↔
    ∀ ⦃B : Type u⦄ [Ring B] (f : A →+* B), TwoSidedIdeal.ker f = ⊤ ∨ Function.Injective f := by
  classical
  constructor
  · intro so B _ f
    if hker : TwoSidedIdeal.ker f = ⊤
    then exact Or.inl hker
    else
      replace hker := so.2 (TwoSidedIdeal.ker f) |>.resolve_right hker
      rw [injective_iff_ker_eq_bot]
      exact Or.inr hker
  · intro h
    refine ⟨fun I => ?_⟩
    rcases h I.ringCon.mk' with h|h
    · right
      rw [eq_top_iff, le_iff]
      rintro x -
      have mem : x ∈ TwoSidedIdeal.ker I.ringCon.mk' := by rw [h]; trivial
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
      rw [h] at mem
      exact mem

lemma IsSimpleOrder.iff_eq_zero_or_injective'
    (k : Type*) [CommRing k] [Algebra k A] [Nontrivial A] :
    IsSimpleOrder (TwoSidedIdeal A) ↔
    ∀ ⦃B : Type u⦄ [Ring B] [Algebra k B] (f : A →ₐ[k] B),
      TwoSidedIdeal.ker f = ⊤ ∨ Function.Injective f := by
  classical
  constructor
  · intro so B _ _ f
    if hker : TwoSidedIdeal.ker f.toRingHom = ⊤
    then exact Or.inl hker
    else
      replace hker := so.2 (TwoSidedIdeal.ker f) |>.resolve_right hker
      rw [injective_iff_ker_eq_bot]
      exact Or.inr hker
  · intro h
    refine ⟨fun I => ?_⟩
    letI : Algebra k I.ringCon.Quotient :=
    { __ := I.ringCon.mk'.comp (algebraMap k A)
      smul := fun a => Quotient.map' (fun b => a • b) fun x y (h : I.ringCon x y) =>
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
    rcases @h I.ringCon.Quotient _ _ {I.ringCon.mk' with commutes' := fun a => rfl } with h|h
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
