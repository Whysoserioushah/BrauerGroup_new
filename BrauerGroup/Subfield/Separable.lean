import Mathlib
import BrauerGroup.Subfield.Splitting
import BrauerGroup.Mathlib.Algebra.Algebra.Subalgebra.Basic

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

abbrev SubField.adjoin (a : D) : SubField K D where
  __ := Algebra.adjoin K {a}
  mul_comm x y hx hy := congr($(_root_.mul_comm (⟨x, hx⟩ : Algebra.adjoin K {a}) (⟨y, hy⟩ : Algebra.adjoin K {a})))
  inverse x hx hx0 := by
    haveI := isField_of_isIntegral_of_isField' (R := K) (S := (Algebra.adjoin K {a} : Subalgebra K D))
      (Semifield.toIsField K)
    exact ⟨(this.3 (Subtype.coe_ne_coe.mp hx0 : (⟨x, hx⟩ : Algebra.adjoin K {a}) ≠ 0)).choose.1,
    ⟨(this.3 (Subtype.coe_ne_coe.mp hx0 : (⟨x, hx⟩ : Algebra.adjoin K {a}) ≠ 0)).choose.2,
      haveI := (this.3 (Subtype.coe_ne_coe.mp hx0 : (⟨x, hx⟩ : Algebra.adjoin K {a}) ≠ 0)).choose_spec
      (Submonoid.mk_eq_one (Algebra.adjoin K {a}).toSubring.toSubmonoid).mp this⟩⟩


abbrev AllSepSubfield : Set (SubField K D) :=
  { L : SubField K D | Algebra.IsSeparable K L }

instance : Nonempty (AllSepSubfield K D) :=
  ⟨⊥, by simpa using Algebra.IsSeparable.of_algHom K K <| Algebra.botEquiv K D⟩

instance : PartialOrder (AllSepSubfield K D) where
  le L1 L2 := L1.1 ≤ L2.1
  le_refl _ := by simp
  le_trans _ _ _ _ _ _ _ := by aesop
  lt_iff_le_not_le _ _ := by aesop
  le_antisymm _ _ _ _ := by aesop

lemma IsSeparable.map {L} {F} {K} [CommRing F] [Ring K] [Algebra F K] [Ring L] [Algebra F L]
    {x : K} (f : K →ₐ[F] L) (hf : Function.Injective f)
    (H : IsSeparable F x) : IsSeparable F (f x) := by
  rwa [IsSeparable, minpoly.algHom_eq _ hf]

set_option maxHeartbeats 500000 in
noncomputable abbrev iSup_chain_sepsubfield (c : Set (AllSepSubfield K D)) [Nonempty c]
    (hc1 : IsChain (· ≤ ·) c): AllSepSubfield K D where
  val := {
    __ := (⨆ (L : c), L.1.1.1 : Subalgebra K D)
    mul_comm x y hx hy := by
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
      exact L3.1.mul_comm x y (hL31 hx) (hL32 hy)
    inverse x hx hx0 := by
      simp only [Subalgebra.coe_toSubsemiring,
        Subsemiring.coe_carrier_toSubmonoid, SetLike.mem_coe] at *
      letI : Nonempty c := Set.Nonempty.to_subtype (Set.Nonempty.of_subtype)
      have := Subalgebra.coe_iSup_of_directed hc1.directed
      dsimp at this
      change x ∈ (_ : Set _) at hx
      erw [this] at hx
      simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
      obtain ⟨L1, hL1, hx⟩ := hx
      use L1.1.inverse x hx hx0|>.choose
      constructor
      · have : L1.1.1 ≤ ⨆ (L : c), (L.1.1).toSubalgebra := by
          exact le_iSup_of_le (ι := c) (f := fun x ↦ x.1.1.1) (a := L1.1.1) ⟨L1, hL1⟩ (by rfl)
        exact this (L1.1.inverse x hx hx0).choose_spec.1
      · exact L1.1.inverse x hx hx0|>.choose_spec.2
  }
  property := by
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SubField.coe_toSubalgebra, eq_mp_eq_cast, cast_eq, id_eq, ne_eq,
      eq_mpr_eq_cast]
    -- have : IsDirected c fun x1 x2 ↦ x1 ≤ x2 := sorry
    -- have : ∀ L : c, Algebra.IsSeparable K L := sorry
    -- exact .of_directedSystem (fun L : c ↦ L)
    --   (fun L M hLM ↦ Subalgebra.inclusion hLM)
    --   sorry
    --   (fun L ↦ Subalgebra.inclusion <| le_iSup_of_le L le_rfl) (by sorry) sorry
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
  zorn_le_nonempty (α := AllSepSubfield K D) <| fun c hc1 hc2 ↦ by
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
  nnratCast q := ⟨q, Subalgebra.mem_centralizer_iff _|>.2 <| fun x _ ↦ NNRat.cast_commute _ _|>.symm⟩
  nnratCast_def q := by ext; simp only [NNRat.cast_def]; rfl
  qsmul q a := ⟨q • a.1, Set.centralizer.qsmul_mem K D (L.1.1) q a.1 a.2⟩
  qsmul_def q x := by ext; simp [Rat.smul_def q x.1]
  nnqsmul q a := ⟨q.1 • a.1, Set.centralizer.qsmul_mem K D L.1.1 q a.1 a.2⟩
  nnqsmul_def q a := by ext; simp [Rat.smul_def]

theorem exists_sep_masSubfield: ∃ a : D, IsMaximalSubfield K D (SubField.adjoin K D a) ∧
    Algebra.IsSeparable K (SubField.adjoin K D a) := by
  obtain ⟨L, hL⟩ := exists_max_sepSub K D
  let CL := Subalgebra.centralizer K (A := D) L
  have := comm_of_centralizer K D L.1.1 (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by simpa using L.1.2 x y hx hy)
  wlog h : CL ≠ L.1.1
  · simp at h

    sorry
  · sorry
