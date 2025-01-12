import BrauerGroup.Subfield.Basic
import BrauerGroup.DoubleCentralizer

universe u

instance comm_of_centralizer (K A : Type u) [Field K] [Ring A] [Algebra K A] (L : Subalgebra K A)
  (hL : ∀ (x y : L), x * y = y * x) :
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
    [Algebra.IsCentral K D] [IsSimpleRing D]

theorem dim_max_subfield (k : SubField K D) (hk: IsMaximalSubfield K D k) :
    Module.finrank K D = Module.finrank K k *
    Module.finrank K k := by
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
        refine Algebra.adjoin_induction₂  ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_ hx hy
        · intro α β hα hβ
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
        · intro _ _  _ _ _ _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro _ _ _ _ _ _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro _ _ _ _ _ _ h1 h2
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
        · intro _ _ _ _ _ _ h1 h2
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
    [Algebra.IsCentral K A] [IsSimpleRing A] (L : SubField K A) :
    Subalgebra.centralizer K L.1 = L.1 ↔ Module.finrank K A =
    Module.finrank K L * Module.finrank K L :=
  ⟨fun h ↦ by
  have := dim_centralizer K (A := A) L.1 ; rw [h] at this ; exact this.symm, fun h ↦ by
  have := dim_centralizer K (A := A) L.1 ; rw [h] at this
  erw [mul_eq_mul_right_iff] at this
  cases' this with h1 h2
  · exact Subalgebra.eq_of_le_of_finrank_eq (comm_of_centralizer K A L.1 fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
      simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq, L.2 x y hx hy]) h1.symm|>.symm
  · have := Module.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]⟩

lemma cor_two_2to3 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] (L : SubField K A) :
    Module.finrank K A = Module.finrank K L * Module.finrank K L →
    (∀ (L' : Subalgebra K A) (_ : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' → L.1 = L') :=
  fun hrank L' hL' hLL ↦ by
  have := dim_centralizer K (A := A) L.1 |>.symm
  simp only [this, SubField.coe_toSubalgebra] at hrank
  erw [mul_eq_mul_right_iff] at hrank
  cases' hrank with h1 h2
  · have := Subalgebra.eq_of_le_of_finrank_eq (comm_of_centralizer K A L.1 fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
      simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq, L.2 x y hx hy]) h1.symm
    exact le_antisymm hLL fun x hx => this.symm ▸ Subalgebra.mem_centralizer_iff _ |>.2
      fun y hy => hL' _ hx _ (hLL hy) |>.symm

  · have := Module.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]

lemma cor_two_3to1 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] (L : SubField K A) :
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
      refine Algebra.adjoin_induction₂ (fun x y hx hy ↦ by
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
        (fun x y z _ _ _ hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
        (fun x y z _ _ _ hxz hyz ↦ by rw [mul_add, add_mul, hxz, hyz])
        (fun x y z _ _ _ hxz hyz ↦ by rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
        (fun x y z _ _ _ hxy hxz ↦ by rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]) hx hy)
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
#min_imports
