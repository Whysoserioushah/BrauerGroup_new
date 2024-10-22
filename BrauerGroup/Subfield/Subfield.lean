import BrauerGroup.Subfield.Basic

universe u

instance comm_of_centralizer (K A : Type u) [Field K] [Ring A] [Algebra K A] (L : Subalgebra K A)
  (hL : ∀(x y : L), x * y = y * x) :
    L ≤ Subalgebra.centralizer K (A := A) L := by
  intro l hl
  simp only [Subalgebra.mem_centralizer_iff, SetLike.mem_coe]
  exact fun l' hl' => by
    have := hL ⟨l, hl⟩ ⟨l', hl'⟩|>.symm
    have eqeq : (⟨l', hl'⟩ : L) * ⟨l, hl⟩ = ⟨l' * l, Subalgebra.mul_mem L hl' hl⟩ := by
      have eq : ((⟨l', hl'⟩ : L) * (⟨l, hl⟩ : L)).1 = l' * l := by
        calc
        _ = ((⟨l', hl'⟩ : L) : A) * ((⟨l, hl⟩ : L) : A) := rfl
        _ = _ := by push_cast ; rfl
      rw [Subtype.ext_iff, eq]
    have eqeq' : (⟨l, hl⟩ : L) * ⟨l', hl'⟩ = ⟨l * l', Subalgebra.mul_mem L hl hl'⟩ := rfl
    rw [eqeq, eqeq'] at this
    exact Subtype.ext_iff.1 this


section cors_of_DC

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    [IsCentralSimple K D]

theorem dim_max_subfield (k : SubField K D) (hk: IsMaximalSubfield K D k) :
    FiniteDimensional.finrank K D = FiniteDimensional.finrank K k *
    FiniteDimensional.finrank K k := by
  have dimdim := dim_centralizer K (A := D) k.1 |>.symm
  have := comm_of_centralizer K D k.1 $ fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ Subtype.ext_iff.2 $ k.2 x y hx hy
  have eq : k.1 = Subalgebra.centralizer K (A := D) k.1 := by
    by_contra! hneq
    have lt := LE.le.lt_iff_ne this|>.2 hneq
    have exist_ele : ∃ a ∈ Subalgebra.centralizer K (A := D) k.1, a ∉ k.1 :=
      Set.ssubset_iff_of_subset this|>.1 $ Set.lt_iff_ssubset.1 lt
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := exist_ele

    letI : CommRing (Algebra.adjoin K (insert a k.1) : Subalgebra K D) :=
    { mul_comm := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
        refine Algebra.adjoin_induction₂ (ha := hx) (hb := hy) ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_
        · intro α hα β hβ
          simp only [Set.mem_insert_iff, SetLike.mem_coe] at hα hβ
          rcases hα with rfl|hα <;> rcases hβ with rfl|hβ
          · rfl
          · rw [Subalgebra.mem_centralizer_iff] at ha1
            refine ha1 _ hβ |>.symm
          · rw [Subalgebra.mem_centralizer_iff] at ha1
            apply ha1; exact hα
          · apply k.mul_comm _ _ hα hβ
        · intros; rw [Algebra.commutes]

        · intros; rw [Algebra.commutes]

        · intros; rw [Algebra.commutes]
        · intro _ _  _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro _ _  _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro x y z h1 h2
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
        · intro x y z h1 h2
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc] }

    have : IsField (Algebra.adjoin K (insert a k) : Subalgebra K D) := by
      rw [ ← Algebra.IsIntegral.isField_iff_isField (R := K)]
      · exact Semifield.toIsField K
      · exact NoZeroSMulDivisors.algebraMap_injective K _

    let L : SubField K D := {
      __ := Algebra.adjoin K (insert a k.1)
      mul_comm := fun x y hx hy ↦ by
        have := this.2 ⟨x, hx⟩ ⟨y, hy⟩
        change (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ :
          (Algebra.adjoin K (insert a k.1) : Subalgebra K D)) = ⟨_, _⟩ at this
        simp only [Subtype.mk.injEq] at this ⊢ ; exact this
      inverse := fun x hx hx0 ↦ by
         have := this.3 (Subtype.coe_ne_coe.1 hx0 : (⟨x, hx⟩ :
          (Algebra.adjoin K (insert a k.1) : Subalgebra K D)) ≠ 0)
         use this.choose.1
         exact ⟨this.choose.2, by
          have eq := this.choose_spec
          change ⟨x * this.choose.1, _⟩ = (1 : Algebra.adjoin K (insert a k.1)) at eq
          exact Subtype.ext_iff.1 eq⟩
    }

    have : a ∈ L := by
      change _ ∈ Algebra.adjoin K _
      have adjoin_le : Algebra.adjoin K {a} ≤ Algebra.adjoin K (insert a k.1) :=
        Algebra.adjoin_mono (s := {a}) (Set.singleton_subset_iff.mpr (Set.mem_insert a k.1))
      have := Algebra.adjoin_le_iff |>.1 adjoin_le
      exact this rfl

    have hL : k < L := ne_iff_lt_iff_le.2 (by
      change k.1 ≤ Algebra.adjoin K (insert a k.1)
      nth_rw 1 [← Algebra.adjoin_eq k.1]
      refine Algebra.adjoin_mono ?_
      exact Set.subset_insert _ _ )|>.1 $ by
      symm
      exact ne_of_mem_of_not_mem' this ha2

    have := hk L (le_of_lt hL)
    have : k ≠ L := ne_of_lt hL
    tauto
  rw [← eq] at dimdim
  exact dimdim

lemma cor_two_1to2 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [hA : IsCentralSimple K A] (L : SubField K A) :
    Subalgebra.centralizer K L.1 = L.1 ↔ FiniteDimensional.finrank K A =
    FiniteDimensional.finrank K L * FiniteDimensional.finrank K L :=
  haveI := hA.2
  ⟨fun h ↦ by
  have := dim_centralizer K (A := A) L.1 ; rw [h] at this ; exact this.symm, fun h ↦ by
  have := dim_centralizer K (A := A) L.1 ; rw [h] at this
  erw [mul_eq_mul_right_iff] at this
  cases' this with h1 h2
  · exact Subalgebra.eq_of_le_of_finrank_eq (comm_of_centralizer K A L.1 fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
      simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq, L.2 x y hx hy]) h1.symm|>.symm
  · have := FiniteDimensional.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]⟩

lemma cor_two_2to3 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [hA : IsCentralSimple K A] (L : SubField K A) :
    FiniteDimensional.finrank K A = FiniteDimensional.finrank K L * FiniteDimensional.finrank K L →
    (∀ (L' : Subalgebra K A) (_ : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' → L.1 = L') :=
  fun hrank L' hL' hLL ↦ by
  haveI := hA.2
  have := dim_centralizer K (A := A) L.1 |>.symm
  simp only [this, SubField.coe_toSubalgebra] at hrank
  erw [mul_eq_mul_right_iff] at hrank
  cases' hrank with h1 h2
  · have := Subalgebra.eq_of_le_of_finrank_eq (comm_of_centralizer K A L.1 fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
      simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq, L.2 x y hx hy]) h1.symm
    exact le_antisymm hLL fun x hx => this.symm ▸ Subalgebra.mem_centralizer_iff _ |>.2
      fun y hy => hL' _ hx _ (hLL hy) |>.symm

  · have := FiniteDimensional.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]

lemma cor_two_3to1 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [IsCentralSimple K A] (L : SubField K A) :
    (∀ (L' : Subalgebra K A)  (_ : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' → L.1 = L') →
    Subalgebra.centralizer K L = L.1 := by
  intro H
  refine le_antisymm ?_ ?_
  · by_contra! hL'
    have := comm_of_centralizer K A L.1 (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ Subtype.ext_iff.2 $ L.2 x y hx hy)
    have Llt := lt_of_le_not_le this hL'
    have exist_ele : ∃ a ∈ Subalgebra.centralizer K L.1, a ∉ L.1 :=
      Set.ssubset_iff_of_subset this|>.1 $ Set.lt_iff_ssubset.1 Llt
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := exist_ele
    specialize H (Algebra.adjoin K (insert a L.1)) (fun x hx y hy ↦ by
      refine Algebra.adjoin_induction₂ (ha := hx) (hb := hy) (fun x hx y hy ↦ by
        simp only [Set.mem_insert_iff, SetLike.mem_coe] at hx hy
        rcases hx with rfl|hx <;> rcases hy with rfl|hy
        · rfl
        · rw [Subalgebra.mem_centralizer_iff] at ha1
          exact ha1 _ hy|>.symm
        · rw [Subalgebra.mem_centralizer_iff] at ha1
          rename_i hxx
          exact ha1 _ hxx
        · exact L.2 _ _ hx hy)
        (fun k1 k2 ↦ Algebra.commutes _ _) (fun k x _ ↦ Algebra.commutes _ _)
        (fun k x _ ↦ Algebra.commutes _ _|>.symm)
        (fun x y z hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
        (fun x y z hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
        (fun x y z hxz hyz ↦ by rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
        (fun x y z hxy hxz ↦ by rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]))
      (by nth_rw 1 [← Algebra.adjoin_eq L.1] ; exact Algebra.adjoin_mono (Set.subset_insert _ _))
    have : L.1 ≠ Algebra.adjoin K (insert a L.1) := ne_of_mem_of_not_mem' (a := a)
      (by exact (Algebra.adjoin_le_iff |>.1 (Algebra.adjoin_mono (R := K) (s := {a})
        (Set.singleton_subset_iff.mpr (Set.mem_insert a L.1)))) rfl) ha2|>.symm
    tauto
  · apply comm_of_centralizer
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    exact L.mul_comm _ _ hx hy

end cors_of_DC

section statement_of_jacobson_noether

variable (D : Type u) [DivisionRing D]

instance {R : Type*} [Ring R]: Algebra (Subring.center R) R where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r x := Subring.mem_center_iff.1 r.2 x|>.symm
  smul_def' _ _ := rfl

variable [Algebra.IsAlgebraic (Subring.center D) D]

theorem Jacobson_Noether (H : (Subring.center D) ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ (Subring.center D) ∧ IsSeparable (Subring.center D) x := by sorry

end statement_of_jacobson_noether

section subfield_of_division

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [IsCentralSimple K D]

instance (a : D) : CommRing (Algebra.adjoin K (insert a (Subalgebra.center K D))) where
  mul_comm := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    exact Algebra.adjoin_induction₂ (ha := hx) (hb := hy)
      (fun α hα β hβ ↦ by
        simp only [Set.mem_insert_iff, SetLike.mem_coe] at hα hβ
        rcases hα with rfl|hα <;> rcases hβ with rfl|hβ
        · rfl
        · rw [Subalgebra.mem_center_iff] at hβ
          exact hβ α
        · rw [Subalgebra.mem_center_iff] at hα
          exact (SemiconjBy.eq (hα β)).symm
        · rw [Subalgebra.mem_center_iff] at hα hβ
          exact hα β |>.symm)
      (fun k1 k2 ↦ Algebra.commutes _ _)
      (fun k x _ ↦ Algebra.commutes _ _)
      (fun k x _ ↦ Algebra.commutes _ _|>.symm)
      (fun x y z hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
      (fun x y z hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
      (fun x y z hxz hyz ↦ by rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
      (fun x y z hxy hxz ↦ by rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc])

abbrev maxSubfieldOfDiv (a : D): SubField K D := {
  __ := (Algebra.adjoin K (insert a (Subalgebra.center K D)))
  mul_comm := fun x y hx hy ↦ by
    have := mul_comm (G := Algebra.adjoin K (insert a (Subalgebra.center K D)))
    simp only [Subtype.forall, MulMemClass.mk_mul_mk, Subtype.mk.injEq] at this
    exact this x hx y hy
  inverse := fun x hx hx0 ↦ by
    have : IsField (Algebra.adjoin K (insert a (Subalgebra.center K D)) : Subalgebra K D) := by
      rw [ ← Algebra.IsIntegral.isField_iff_isField (R := K)]
      · exact Semifield.toIsField K
      · exact NoZeroSMulDivisors.algebraMap_injective K _
    have := this.3 (Subtype.coe_ne_coe.1 hx0 : (⟨x, hx⟩ :
          (Algebra.adjoin K (insert a (Subalgebra.center K D)) : Subalgebra K D)) ≠ 0)
    use this.choose.1
    exact ⟨this.choose.2, by
      have eq := this.choose_spec
      change ⟨x * this.choose.1, _⟩ = (1 : Algebra.adjoin K (insert a _)) at eq
      exact Subtype.ext_iff.1 eq⟩ }

theorem centralizer_eq_iff_max (D : Type u) [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    [IsCentralSimple K D] (L : SubField K D) :
    Subalgebra.centralizer K L = L.1 ↔ IsMaximalSubfield K D L :=
  ⟨fun h L' hL' ↦ by
    change L.1 ≤ L'.1 at hL'
    have hL : ∀ x ∈ L', ∀ y ∈ L', x * y = y * x := fun x hx y hy ↦ L'.2 x y hx hy
    have := cor_two_2to3 K D L $ cor_two_1to2 K D L|>.1 h
    apply SubField.ext
    exact congrArg _ (congrArg _ (congrArg _ (congrArg _ $ this L'.1 hL hL' |>.symm))),
  fun h ↦ cor_two_1to2 K D L|>.2 $ dim_max_subfield K D L h⟩

instance (KK : SubField K D) [h : Fact <| (Subalgebra.center K D) ≤ KK.1] :
    Algebra (Subalgebra.center K D) KK where
      smul := _
      toFun x := ⟨x.1, h.out x.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' r x := by sorry
      smul_def' _  _ := rfl

abbrev A := {KK : SubField K D | ∃ (_ : Fact <| Subalgebra.center K D ≤ KK.1),
  Algebra.IsSeparable (Subalgebra.center K D) KK}
abbrev centerSubfield : SubField K D := ⟨Subalgebra.center K D, sorry, sorry⟩

-- lemma meme_centerSubfield (a : D) : a ∈ centerSubfield K D ↔ a ∈ Subalgebra.center K D := by
--   simp only [centerSubfield]

instance : Fact <| Subalgebra.center K D ≤ (centerSubfield K D).1 := ⟨sorry⟩
open Polynomial in
instance : Nonempty (A K D) := ⟨centerSubfield K D, inferInstance,
{ isSeparable' := by
    rintro ⟨x, (hx : x ∈ Subalgebra.center K D)⟩
    delta IsSeparable
    set P := _; change Polynomial.Separable P
    have eq : P = Polynomial.X - Polynomial.C ⟨x, hx⟩ := by
      simp only [P]
      symm
      apply minpoly.unique
      · exact monic_X_sub_C _
      · simp only [map_sub, aeval_X, aeval_C]
        erw [sub_self]
      intro q hq hq'
      simp only [degree_X_sub_C]
      suffices h : 0 < q.degree by exact Nat.WithBot.one_le_iff_zero_lt.mpr h
      rw [← Polynomial.natDegree_pos_iff_degree_pos]
      by_contra! h
      simp only [nonpos_iff_eq_zero] at h
      rw [natDegree_eq_zero] at h
      obtain ⟨c, rfl ⟩ := h
      simp only [aeval_C, _root_.map_eq_zero] at hq'
      subst hq'
      simp only [map_zero, not_monic_zero] at hq
    rw [eq]
    exact separable_X_sub_C }⟩

lemma A_has_maximal : ∃ (M : SubField K D), M ∈ A K D ∧ ∀ N ∈ A K D, M ≤ N → M = N := by
  classical
  obtain ⟨_, ⟨⟨M, hM1, rfl⟩, hM2⟩⟩ := set_has_maximal_iff_noetherian (R := K) (M := D) |>.2 inferInstance (Subalgebra.toSubmodule ∘ SubField.toSubalgebra '' A K D)
    (by simpa only [Function.comp_apply, Set.image_nonempty] using Set.nonempty_of_nonempty_subtype)

  refine ⟨M, hM1, fun N hN  hMN => ?_⟩
  specialize hM2 (Subalgebra.toSubmodule N.1) ⟨N, hN, rfl⟩
  rw [le_iff_lt_or_eq] at hMN
  refine hMN.resolve_left fun r => hM2 r

theorem maxsubfield_is_sep : ∃ a : D, Algebra.IsSeparable K (maxSubfieldOfDiv K D a)
    ∧ IsMaximalSubfield K D (maxSubfieldOfDiv K D a) := by
  obtain ⟨M, ⟨LE, hM1⟩, hM2⟩ := A_has_maximal K D
  let CM := Subalgebra.centralizer K (M : Set D)
  letI : DivisionRing CM :=
  { inv := fun x => ⟨x.1⁻¹, sorry⟩
    mul_inv_cancel := sorry
    inv_zero := by ext; simp
    nnqsmul := _
    qsmul := _ }
  have eq : CM = M.1 := sorry
  letI : Module M D := Module.compHom D M.val.toRingHom
  haveI : IsScalarTower K M D := by
    constructor
    intro x y z
    change (x • y.1) • z = x • y.1 • z
    rw [smul_assoc]
    -- rfl
  have := centralizer_eq_iff_max K D M |>.1 eq
  haveI : FiniteDimensional K D := inferInstance
  haveI : FiniteDimensional K M := FiniteDimensional.of_injective M.toSubalgebra.val.toLinearMap (Subtype.val_injective)
  haveI : FiniteDimensional M D := FiniteDimensional.right K M D
  haveI : IsScalarTower K (Subalgebra.center K D) M := by
    constructor
    intro x y z
    ext
    change (x • y.1) • z.1 = x • y.1 • z.1
    rw [smul_assoc]
  haveI : FiniteDimensional (Subalgebra.center K D) M :=
    FiniteDimensional.right K (Subalgebra.center K D) M
  obtain ⟨a, ha⟩ := Field.exists_primitive_element (Subalgebra.center K D) M


  sorry

end subfield_of_division
