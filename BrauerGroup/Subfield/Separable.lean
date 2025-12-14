import BrauerGroup.Mathlib.Algebra.Algebra.Subalgebra.Lattice
import BrauerGroup.Subfield.Splitting
import Mathlib.FieldTheory.JacobsonNoether

-- section
-- variable {ι R A : Type*} (B : ι → Type*) [Preorder ι] [CommRing R]
--   [Ring A] [Algebra R A] [∀ i, Ring (B i)] [∀ i, Algebra R (B i)]

-- lemma Algebra.IsSeparable.of_directedSystem [IsDirected ι (· ≤ ·)] [∀ i, Algebra.IsSeparable R (B i)]
--     (map : ∀ i j, i ≤ j → B i →ₐ[R] B j)
--     (directedSystem_map : DirectedSystem B fun i j hij ↦ map i j hij)
--     (cone : ∀ i, B i →ₐ[R] A)
--     (hcone : ∀ i j (hij : i ≤ j), cone i = (cone j).comp (map i j hij))
--     (hlimit : ∀ a , ∃ i, a ∈ Set.range (cone i)) :
--     Algebra.IsSeparable R A where
--   isSeparable' a := by
--     obtain ⟨i, b, rfl⟩ := hlimit a
--     sorry
--     -- exact IsSeparable.map _ (f := (cone i).toRingHom)

-- end

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D]

open Polynomial

-- se_option maxHeartbeats 3200000 in
omit [Algebra.IsCentral K D] [FiniteDimensional K D] in
lemma SubField.adjoin_centralizer_mul_comm (L : SubField K D) (a : D)
    (ha : a ∈ Subalgebra.centralizer K L) : ∀ (x y : D), x ∈ Algebra.adjoin K (L ∪ {a}) →
    y ∈ Algebra.adjoin K (L ∪ {a}) → x * y = y * x :=
  fun x y hx hy ↦ by
    simp [Algebra.mem_adjoin_iff, Subalgebra.mem_centralizer_iff] at hx hy ha
    refine Subring.closure_induction₂ (R := D) (fun x1 y1 hx1 hy1 ↦ by
      simp at hx1 hy1
      obtain hx11 | hx12 | hx13 := hx1
      all_goals obtain hy11 | hy12 | hy13 := hy1
      · simp_all
      · obtain ⟨b, rfl⟩ := hy12
        exact Algebra.commutes _ _ |>.symm
      · subst hx11
        exact ha _ hy13|>.symm
      · obtain ⟨b, rfl⟩ := hx12
        exact Algebra.commutes _ _
      · obtain ⟨b, rfl⟩ := hx12
        exact Algebra.commutes _ _
      · obtain ⟨b, rfl⟩ := hx12
        exact Algebra.commutes _ _
      · subst hy11
        exact ha _ hx13
      · obtain ⟨b, rfl⟩ := hy12
        exact Algebra.commutes _ _ |>.symm
      · exact L.2 hx13 hy13) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    all_goals try simp_all [add_mul, mul_add]
    · rintro x y z - - - hxz hyz
      rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc]
    · rintro x y z - - - hxy hxz
      rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]

instance SubField.adjoin_commRing (L : SubField K D) (a : D) (ha : a ∈ Subalgebra.centralizer K L) :
    CommRing (Algebra.adjoin K (L ∪ {a})) where
  mul_comm := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
    ext
    simp [SubField.adjoin_centralizer_mul_comm K D L a ha x y hx hy]

instance SubField.adjoin_isDomain (L : SubField K D) (a : D) :
    IsDomain (Algebra.adjoin K (L ∪ {a})) where
  mul_left_cancel_of_ne_zero {x} hx y z eq := by
    have eq' := Subtype.ext_iff.1 eq
    simp at eq'
    exact eq'.resolve_right hx
  mul_right_cancel_of_ne_zero {x} hx y z eq := by
    have eq' := Subtype.ext_iff.1 eq
    simp at eq'
    exact eq'.resolve_right hx

def SubField.adjoin (L : SubField K D) (a : D) (ha : a ∈ Subalgebra.centralizer K L) :
    SubField K D where
  __ := Algebra.adjoin K (L ∪ {a})
  algebraMap_mem' k := by
    have : ⊥ ≤ Algebra.adjoin K (L ∪ {a}) := bot_le
    change (Algebra.ofId _ _).range ≤ _ at this
    exact this (by change _ ∈ (algebraMap K D).range; exact
      RingHom.mem_range_self (algebraMap K D) k)
  mul_comm x y hx hy := by
    exact SubField.adjoin_centralizer_mul_comm K D L a ha x hx y hy
  exists_inverse x hx hx0 := by
    letI := SubField.adjoin_commRing K D L a ha
    haveI := isField_of_isIntegral_of_isField' (R := K) (S := Algebra.adjoin K (L ∪ {a}))
      (Semifield.toIsField K)
    exact ⟨(this.3 (Subtype.coe_ne_coe.mp hx0 : (⟨x, hx⟩ : Algebra.adjoin K _) ≠ 0)).choose.1,
    ⟨(this.3 (Subtype.coe_ne_coe.mp hx0 : (⟨x, hx⟩ : Algebra.adjoin _ _) ≠ 0)).choose.2,
      haveI := (this.3 (Subtype.coe_ne_coe.mp hx0 : (⟨x, hx⟩ : Algebra.adjoin _ _) ≠ 0)).choose_spec
      (Submonoid.mk_eq_one (Algebra.adjoin _ _).toSubring.toSubmonoid).mp this⟩⟩

noncomputable local instance IsLAlg (L : SubField K D) (a : D) (ha : a ∈ Subalgebra.centralizer K L) :
  Algebra L (SubField.adjoin K D L a ha) := RingHom.toAlgebra' (Subalgebra.inclusion <|
    Set.subset_union_left |>.trans Algebra.subset_adjoin).toRingHom fun ⟨x, hx⟩ ⟨y, hy⟩ ↦
    Subtype.ext_iff|>.2 <| SubField.adjoin_centralizer_mul_comm K D L a ha _ y
      (Subalgebra.inclusion _ (⟨x, hx⟩ : L)).2 hy

local instance SubField.adjoin_scalarTower (L : SubField K D) (a : D)
    (ha : a ∈ Subalgebra.centralizer K L) :
    IsScalarTower K L (SubField.adjoin K D L a ha) where
  smul_assoc k l x := Subtype.ext_iff.2 <| by simp

omit [Algebra.IsCentral K D] [FiniteDimensional K D] in
lemma SubField.le_centralizer (L : SubField K D) : L.toSubalgebra ≤ Subalgebra.centralizer _ L :=
  fun _ hx _ hy ↦ L.mul_comm hy hx

omit [Algebra.IsCentral K D] in
lemma SubField.adjoin_le_centralizer (L : SubField K D) (a : D)
    (ha : a ∈ Subalgebra.centralizer K L) :
    (SubField.adjoin K D L a ha).1 ≤ Subalgebra.centralizer K (A := D) L := by
  change Algebra.adjoin _ _ ≤ _
  rw [Algebra.adjoin_le_iff, Set.union_subset_iff, Set.singleton_subset_iff]
  exact ⟨SubField.le_centralizer _ _ _, ha⟩

abbrev AllSepSubfield : Set (SubField K D) :=
  { L : SubField K D | Algebra.IsSeparable K L }

instance : Nonempty (AllSepSubfield K D) :=
  ⟨⊥, by simpa using Algebra.IsSeparable.of_algHom K K <| Algebra.botEquiv K D⟩

instance : PartialOrder (AllSepSubfield K D) where
  le L1 L2 := L1.1 ≤ L2.1
  le_refl _ := by simp
  le_trans _ _ _ _ _ _ _ := by aesop
  le_antisymm _ _ _ _ := by aesop

set_option maxHeartbeats 500000 in
noncomputable abbrev iSup_chain_sepsubfield (c : Set (AllSepSubfield K D)) [Nonempty c]
    (hc1 : IsChain (· ≤ ·) c) : AllSepSubfield K D where
  val := {
    __ := (⨆ (L : c), L.1.1.1 : Subalgebra K D)
    mul_comm x hx y hy := by
      simp only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring,
        SetLike.mem_coe] at hx hy
      have := Subalgebra.coe_iSup_of_directed hc1.directed
      dsimp at this
      change x ∈ (_ : Set _) at hx ; change _ ∈ ( _ : Set _) at hy
      erw [this] at hx hy

      -- rw [this] at hx hy
      simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx hy
      obtain ⟨L1, hL1, hx⟩ := hx
      obtain ⟨L2, hL2, hy⟩ := hy
      obtain ⟨L3, _, hL31, hL32⟩ := hc1.directedOn L1 hL1 L2 hL2
      exact L3.1.mul_comm (hL31 hx) (hL32 hy)
    exists_inverse x hx hx0 := by
      simp only [Subalgebra.coe_toSubsemiring,
        Subsemiring.coe_carrier_toSubmonoid, SetLike.mem_coe] at *
      letI : Nonempty c := Set.Nonempty.to_subtype (Set.Nonempty.of_subtype)
      have := Subalgebra.coe_iSup_of_directed hc1.directed
      dsimp at this
      change x ∈ (_ : Set _) at hx
      erw [this] at hx
      simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
      obtain ⟨L1, hL1, hx⟩ := hx
      use L1.1.3 hx hx0|>.choose
      constructor
      · have : L1.1.1 ≤ ⨆ (L : c), (L.1.1).toSubalgebra := by
          exact le_iSup_of_le (ι := c) (f := fun x ↦ x.1.1.1) (a := L1.1.1) ⟨L1, hL1⟩ (by rfl)
        exact this (L1.1.3 hx hx0).choose_spec.1
      · exact L1.1.3 hx hx0|>.choose_spec.2
  }
  property := by
    simp only [Set.coe_setOf, Set.mem_setOf_eq]
    rw [Algebra.isSeparable_def]
    simp
    intro a ha
    have := Subalgebra.coe_iSup_of_directed hc1.directed
    simp at this
    change a ∈ (_ : Set _) at ha
    erw [this] at ha
    simp at ha
    obtain ⟨L, ⟨ha', h⟩, hL2⟩ := ha
    exact IsSeparable.map (F := K) (L := ((⨆ (L : c), L.1.1.1) : Subalgebra K D)) (x := (⟨a, hL2⟩ : L))
      (Subalgebra.inclusion (le_iSup_of_le ⟨⟨L, ha'⟩, h⟩ le_rfl))
      (Subalgebra.inclusion_injective _) <| Algebra.isSeparable_def _ _|>.1 ha' ⟨a, hL2⟩

omit [Algebra.IsCentral K D] [FiniteDimensional K D] in
lemma exists_max_sepSub : ∃ L : AllSepSubfield K D, IsMax L :=
  zorn_le_nonempty (α := AllSepSubfield K D) fun c hc1 hc2 ↦ by
    haveI : Nonempty c := Set.Nonempty.to_subtype hc2
    use iSup_chain_sepsubfield K D c hc1
    change _ ∈ {L | _}
    simp only [Set.mem_setOf_eq]
    intro L hL
    change L.1.1 ≤ (⨆ (L : c), L.1.1.1 : Subalgebra K D)
    exact le_iSup_of_le ⟨L, hL⟩ (by rfl)

theorem Set.centralizer.qsmul_mem (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
    (L : Set D) (q : ℚ) (a : D) (ha : a ∈ Set.centralizer L) :
    q • a ∈ Set.centralizer L := by
  rw [Rat.smul_def]
  intro m hm
  simp_all [mem_centralizer_iff]
  have (m : D) := Commute.left_comm <| Rat.cast_commute q m|>.symm
  rw [this, ha _ hm, mul_assoc]

@[simps!]
instance (L : SubField K D) : DivInvMonoid (Subalgebra.centralizer K (A := D) L) where
  __ := inferInstanceAs (Ring (Subalgebra.centralizer K (A := D) L))
  inv a := ⟨a⁻¹, Set.inv_mem_centralizer₀ a.2⟩
  div x y := ⟨(x / y : D), Set.div_mem_centralizer₀ x.2 y.2⟩
  div_eq_mul_inv x y := by ext; simp [← div_eq_mul_inv]; rfl

instance (L : SubField K D) : RatCast (Subalgebra.centralizer K (A := D) L) where
  ratCast q := ⟨q, Subalgebra.mem_centralizer_iff _|>.2 fun _ _↦ Rat.cast_commute _ _|>.symm⟩

omit [Algebra.IsCentral K D] [FiniteDimensional K D] in
@[simp]
lemma SubField.centralizer.coe_ratCast (L : SubField K D) (q : ℚ) :
    ((q : Subalgebra.centralizer K (A := D) L) : D) = q := rfl

instance (L : SubField K D) : NNRatCast (Subalgebra.centralizer K (A := D) L) where
  nnratCast q := ⟨q, Subalgebra.mem_centralizer_iff _|>.2 fun _ _ ↦ NNRat.cast_commute _ _|>.symm⟩

omit [Algebra.IsCentral K D] [FiniteDimensional K D] in
@[simp]
lemma SubField.centralizer.nnratCast_eq (L : SubField K D) (q : NNRat) :
    ((q : Subalgebra.centralizer K (A := D) L) : D) = q := rfl

instance centralizerSubfieldDiv (L : SubField K D) :
    DivisionRing (Subalgebra.centralizer K (A := D) L) where
  mul_inv_cancel a ha := by ext; simp; rw [mul_inv_cancel₀ (by aesop)]
  inv_zero := by ext; simp
  ratCast_def q := by ext; simp [Rat.cast_def]
  nnratCast q := ⟨q, Subalgebra.mem_centralizer_iff _|>.2 fun x _ ↦ NNRat.cast_commute _ _|>.symm⟩
  nnratCast_def q := by ext; simp only [NNRat.cast_def]; rfl
  qsmul q a := ⟨q • a.1, Set.centralizer.qsmul_mem K D (L.1.1) q a.1 a.2⟩
  qsmul_def q x := by ext; simp [Rat.smul_def q x.1]
  nnqsmul q a := ⟨q.1 • a.1, Set.centralizer.qsmul_mem K D L.1.1 q a.1 a.2⟩
  nnqsmul_def q a := by ext; simp [Rat.smul_def]

noncomputable instance (L : SubField K D) : Algebra L (Subalgebra.centralizer K (A := D) L) where
  smul l1 x := ⟨l1 * x, Set.mul_mem_centralizer
    (Subalgebra.mem_centralizer_iff K|>.2 fun _ hy ↦ L.2 l1.2 hy |>.symm) x.2⟩
  algebraMap := Subalgebra.inclusion (fun _ hx ↦ Subalgebra.mem_centralizer_iff K|>.2
    fun _ hy ↦ L.2 hx hy|>.symm : L.1 ≤ Subalgebra.centralizer K (A := D) L)
  commutes' l x := Subtype.ext_iff.2 <| Subalgebra.mem_centralizer_iff K|>.1 x.2 l.1 l.2
  smul_def' _ _ := rfl

instance (L : SubField K D) : IsScalarTower K L (Subalgebra.centralizer K (A := D) L) where
  smul_assoc k l x := Subtype.ext_iff.2 <| by
    simp [show ↑((k • l) • x) = (k • l.1) * _ from rfl, show k • ↑(l • x) = k • (l.1 * x.1) from rfl]

instance (L : SubField K D) : FiniteDimensional L (Subalgebra.centralizer K (A := D) L) :=
  haveI : FiniteDimensional K (Subalgebra.centralizer K (A := D) L) := inferInstance
  -- haveI : FiniteDimensional K L := sorry
  Module.Finite.of_restrictScalars_finite K _ _

noncomputable abbrev ZCL_equiv_ZCL_map (L : SubField K D) :
    (Subalgebra.center K (Subalgebra.centralizer K (A := D) L)) ≃ₐ[K] Subalgebra.map
      (Subalgebra.centralizer K (A := D) L).val
      (Subalgebra.center K (Subalgebra.centralizer K (A := D) L)) :=
  AlgEquiv.ofBijective {
    toFun x := ⟨x.1, ⟨⟨x.1, by simp⟩, by simp⟩⟩
    map_one' := by ext; rfl
    map_mul' _ _ := by ext; simp
    map_zero' := by ext; rfl
    map_add' _ _ := by ext; simp
    commutes' _ := by ext; simp }
  ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ eq ↦ by simp_all, fun ⟨y, ⟨y', hy1, hy2⟩⟩ ↦ ⟨⟨y', hy1⟩, by simpa using hy2⟩⟩

abbrev SubField.bot_adjoin (a : D) : SubField K D :=
  SubField.adjoin K D ⊥ a (by
    rw [Subalgebra.mem_centralizer_iff];
    intro y (hy : y ∈ (Algebra.ofId _ _).range);
    obtain ⟨y, rfl⟩ := hy
    exact Algebra.commutes _ _)

omit [Algebra.IsCentral K D] in
@[simp]
lemma SubField.self_mem_bot_adjoin (a : D) :
    a ∈ (SubField.bot_adjoin K D a) := by
  apply Algebra.subset_adjoin
  simp

omit [Algebra.IsCentral K D] in
lemma SubField.bot_adjoin_coe (a : D) :
    (SubField.bot_adjoin K D a).1 = Algebra.adjoin K {a} := by
  apply le_antisymm
  · change Algebra.adjoin _ _ ≤ _
    rw [Algebra.adjoin_le_iff, Set.union_subset_iff]
    exact ⟨bot_le (α := Subalgebra K D), by simp⟩
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    simp
  -- change x ∈ Algebra.adjoin K ((Algebra.ofId _ _).range ∪ {a}) ↔ _
  -- simp [Algebra.adjoin_algebraMap]
-- lemma extend_sep_sep (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
--     [FiniteDimensional K D] (L : Subalgebra K D) [Algebra.IsSeparable K L] [CommRing L] [Algebra L D] (a : D)
--     (ha : a ∈ Subalgebra.centralizer K L) (ha' : IsSeparable L a) :
--     Algebra.IsSeparable K (Algebra.adjoin K (L ∪ {a})) := by
--   rw [Algebra.isSeparable_def]
--   intro ⟨x, hx⟩
--   refine Algebra.adjoin_induction _ _ _ _ hx
--   sorry
  --   Algebra.IsSeparable K (SubField.adjoin K D L a ha) := by
  -- rw [Algebra.isSeparable_def]
  -- intro x hx
  -- change x ∈ Algebra.adjoin _ _ at hx
  -- obtain ⟨y, hy⟩ := hx
  -- have := SubField.adjoin_centralizer_mul_comm K D L a ha y x hy hx
  -- simp at this
  -- exact H y hy this

-- todo: replace mathlib version with this one
theorem IsSeparable.of_algHom'.{u_1, u_2, u_3}
    {F : Type u_1} [Field F] {K : Type u_2} {E : Type u_3} [Field K] [Ring E]
  [Algebra F K] [Algebra F E] [Nontrivial E] (f : K →ₐ[F] E) {x : K}
  (h : IsSeparable F (f x)) : IsSeparable F x :=
  have ⟨_q, hq⟩ := minpoly.dvd F x (p := minpoly F (f x)) (by
    apply f.injective
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_zero, ← aeval_algHom_apply, minpoly.aeval])
  (Eq.mp (congrArg Separable hq) h).of_mul_left

set_option synthInstance.maxHeartbeats 500000 in
set_option maxHeartbeats 1000000 in
open Subalgebra in
theorem exists_sep_masSubfield' : ∃ (a : D), IsMax (SubField.bot_adjoin K D a) ∧
    Algebra.IsSeparable K (SubField.bot_adjoin K D a) := by
  obtain ⟨L, hL⟩ := exists_max_sepSub K D
  let CL := Subalgebra.centralizer K (A := D) L
  -- have := comm_of_centralizer K D L.1.1 (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by simpa using L.1.2 x y hx hy)
  suffices h : CL = L.1.1 by
    have Lmax := maxsubfield_of_div_iff K D L.1 |>.1 <| cor_two_2to3 K D L.1 (cor_two_1to2 K D L.1 |>.1 h)
    haveI : Algebra.IsSeparable _ _  := L.2
    obtain ⟨a, ha⟩ := Field.exists_primitive_element K L.1
    use a
    constructor
    · convert Lmax
      apply SubField.toSubalgebra_injective
      simp [SubField.bot_adjoin_coe]
      convert congr(($ha).toSubalgebra.map L.1.toSubalgebra.val)
      · rw [IntermediateField.adjoin_simple_toSubalgebra_of_integral,
          AlgHom.map_adjoin, Set.image_singleton]
        · rfl
        · exact Algebra.IsIntegral.isIntegral _
      · simp [Subalgebra.range_val] --TODO: Add to simp lemma
    · exact Algebra.IsSeparable.of_algHom K (E := (SubField.bot_adjoin K D a.1)) L.1 <|
        Subalgebra.inclusion (by
          rw [SubField.bot_adjoin_coe K D a.1, Algebra.adjoin_le_iff]
          simp)
  by_contra! h
  let ZCL := Subalgebra.center K CL
  let CCL := Subalgebra.centralizer K (A := D) CL
  letI : Field L.1 := inferInstance
  haveI sim : IsSimpleRing L.1.1 := inferInstance
  have eq1 := double_centralizer (F := K) (A := D) L.1.1
  change CCL = L.1.1 at eq1
  have eq2 : CCL = ZCL.map (Subalgebra.val _) := by
    dsimp [CCL, ZCL, CL] at *
    clear CCL ZCL CL
    refine le_antisymm ?_ ?_
    · rw [eq1]
      intro x hx
      simp
      constructor
      · simp [Subalgebra.mem_center_iff]
        intro y hy
        simp [Subalgebra.mem_centralizer_iff] at hy
        exact hy x hx|>.symm
      · simp [Subalgebra.mem_centralizer_iff]
        exact fun y hy ↦ L.1.2 hy hx
    · convert le_trans ?_ (Subalgebra.map_centralizer_le_centralizer_image ⊤ (centralizer K (L.1.1: Set D)).val)
      · simp
      apply Subalgebra.map_mono
      exact Subalgebra.center_le_centralizer _ _
    -- rw [eq1]
  rw [eq1] at eq2
  haveI inst1 : Algebra.IsAlgebraic L CL := Algebra.IsAlgebraic.of_finite L CL
  haveI inst2 : FiniteDimensional ZCL CL := inferInstance
  haveI inst3: Algebra.IsAlgebraic ZCL CL := Algebra.IsAlgebraic.of_finite ZCL CL
  have ass : Subring.center ↥CL ≠ ⊤ := by
    rw [eq2] at h
    symm
    contrapose! h
    apply Subalgebra.toSubring_injective
    convert congr(Subring.map CL.val.toRingHom $h)
    ext
    simp
  obtain ⟨a, ha1, ha2⟩ := @JacobsonNoether.exists_separable_and_not_isCentral
    (Subalgebra.centralizer K (A := D) L) _ inst3 ass
  obtain ⟨L, hLsep⟩ := L
  have ha1_aux : a.1 ∉ L := by
    by_contra! haa
    have : a ∈ Subring.center (centralizer K L) := by
      rw [Subring.mem_center_iff]
      intro ⟨b, hb⟩
      rw [Subalgebra.mem_centralizer_iff] at hb
      ext
      simp [hb a.1 haa]
    tauto
  have cond3 : L ≠ SubField.adjoin K D L a.1 a.2 := by
    by_contra! eq
    obtain eq' := (SetLike.ext_iff.1 eq) a.1 |>.2 (Algebra.subset_adjoin <| by simp)
    tauto
  simp_all only
  let e1 := Subalgebra.equivOfEq L.1 _ eq2
  let e2 := ZCL_equiv_ZCL_map K D L
  have asep := IsSeparable.of_equiv_equiv (A₁ := Subalgebra.center K (Subalgebra.centralizer K (A := D) L))
    (A₂ := L) (e2.trans e1.symm).toRingEquiv (RingEquiv.refl _) (by
    ext x
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, RingEquiv.coe_ringHom_refl, RingHomCompTriple.comp_eq,
      SetLike.coe_eq_coe]
    unfold e1 e2
    simp only [equivOfEq_symm]
    erw [AlgEquiv.trans_apply]
    simp only [AlgEquiv.coe_ofBijective, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    change algebraMap _ _ x = _
    rfl) ha2
  simp at asep
  have cond1 : Algebra.IsSeparable K (SubField.adjoin K D L a.1 a.2) := by
    rw [Algebra.isSeparable_def]
    rintro ⟨x, hx⟩
    change x ∈ Algebra.adjoin _ _  at hx
    refine Algebra.adjoin_induction (by
      intro x1 hx1
      simp at hx1
      obtain hx11 | hx12 := hx1
      · subst hx11
        letI : Algebra.IsSeparable K L := hLsep
        letI := IsLAlg K D L a.1 a.2
        letI := SubField.adjoin_scalarTower K D L a.1 a.2
        exact IsSeparable.of_algebra_isSeparable_of_isSeparable K (E := L)
          (K := SubField.adjoin K D L a.1 a.2) (x := ⟨a.1, Algebra.subset_adjoin hx1⟩) <| by
            let f : SubField.adjoin K D L a.1 a.2 →ₐ[L] centralizer K (L : Set D) :=
              ⟨(Subalgebra.inclusion (SubField.adjoin_le_centralizer K D L a.1 a.2)).toRingHom, fun r ↦ rfl⟩
            refine IsSeparable.of_algHom' f asep
      · simp [Algebra.isSeparable_def] at hLsep
        have := IsSeparable.map (F := K) (K := L) (L := SubField.adjoin K D L a.1 a.2)
          (x := (⟨x1, hx12⟩ : L)) (Subalgebra.inclusion (Set.subset_union_left |>.trans
          Algebra.subset_adjoin)) (Subalgebra.inclusion_injective _ ) <| hLsep x1 hx12
        exact this)
      (fun k ↦ IsSeparable.map (Algebra.ofId K _) (FaithfulSMul.algebraMap_injective _ _)
        (Algebra.IsSeparable.isSeparable' k))
      (fun _ _ _ _ ↦ Field.isSeparable_add) (fun _ _ _ _ ↦ Field.isSeparable_mul)  hx
  have : (SubField.adjoin K D L a.1 a.2) ∈ AllSepSubfield K D := by
    simp [cond1]
  have cond2 : L ≤ SubField.adjoin K D L a.1 a.2 :=
    Set.subset_union_left (s := L.1) (t := {a.1}) |>.trans <| Algebra.subset_adjoin (R := K)
  simp [IsMax] at hL
  specialize hL (SubField.adjoin K D L a.1 a.2) cond1 cond2
  have : L = SubField.adjoin K D L a.1 a.2 := le_antisymm cond2 hL
  tauto

theorem exists_sep_masSubfield : ∃ L : SubField K D, IsMax L ∧ Algebra.IsSeparable K L := by
  obtain ⟨a, hL1, hL2⟩ := exists_sep_masSubfield' K D
  exact ⟨SubField.bot_adjoin K D a, hL1, hL2⟩

theorem exists_sep_splitting : ∃ (L : Type u)(_ : Field L)(_ : Algebra K L)(_ : FiniteDimensional K L),
    Algebra.IsSeparable K L ∧ isSplit K D L := by
  obtain ⟨L, hL1, hL2⟩ := exists_sep_masSubfield K D
  exact ⟨L, inferInstance, inferInstance, inferInstance, hL2, isSplit_of_isMax K D L hL1⟩

set_option synthInstance.maxHeartbeats 40000 in
theorem exists_finite_galois_split : ∃ (L : Type u)(_ : Field L)(_ : Algebra K L)(_ : FiniteDimensional K L),
    IsGalois K L ∧ isSplit K D L := by
  obtain ⟨L, _, _, _, hL1, hL2⟩ := exists_sep_splitting K D
  haveI : FiniteDimensional K L := inferInstance
  let K_bar := AlgebraicClosure K
  haveI : IsAlgClosed K_bar := inferInstance
  haveI : Algebra.IsAlgebraic K L := inferInstance
  let L' := IntermediateField.normalClosure K L K_bar
  let f := normalClosure.algHomEquiv K L K_bar |>.symm IsAlgClosed.lift
  letI : Algebra.IsSeparable K L := hL1
  letI : Algebra L L' := RingHom.toAlgebra f
  haveI : IsScalarTower K L L' := {
    smul_assoc k l x := by
      simp only [Algebra.smul_def, map_mul]
      rw [mul_assoc]
      congr 1
      change (normalClosure.algHomEquiv K L K_bar |>.symm IsAlgClosed.lift) _ = _
      simp only [AlgHom.commutes]
      rfl }
  have : L' ≤ separableClosure K K_bar := by
    change IntermediateField.normalClosure K L K_bar ≤ _
    rw [normalClosure_def, iSup_le_iff]
    intro f
    intro x hx
    have : Algebra.IsSeparable K f.fieldRange := Algebra.IsSeparable.of_equiv_equiv (B₁ := L)
      (B₂ := f.fieldRange) (RingEquiv.refl K) (AlgEquiv.ofInjectiveField f).toRingEquiv <| by
      ext; erw [AlgEquiv.ofInjective_apply _ f.injective]; simp
    simp [mem_separableClosure_iff]
    exact IsSeparable.map f.fieldRange.val Subtype.val_injective <|
      Algebra.isSeparable_def _ _ |>.1 this ⟨x, hx⟩
  exact ⟨L', inferInstance, inferInstance, inferInstance,
    {to_isSeparable := le_separableClosure_iff _ _ _|>.1 this,
      to_normal := inferInstance},
    extension_over_split' K K_bar D L L' hL2⟩
