import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Tactic
import Mathlib.Data.Finsupp.Notation

universe u

suppress_compilation

variable (R : Type u) [Ring R] (e : R)

structure PrimitiveIdempotents: Prop where
  idem : IsIdempotentElem e
  ne_sum_ortho : ∀ (I : Type u) [DecidableEq I] [Fintype I]
    (e' : I → R) [(i : I) → (x : ↥(Submodule.span R {e' i})) → Decidable (x ≠ 0)]
    (_ : OrthogonalIdempotents (R := R) e') (i j : I), e ≠ e' i + e' j

section

variable {ι M σ : Type*}
variable [DecidableEq ι] [AddCommGroup M] [Module R M]
open DirectSum
variable (ℳ : ι → Submodule R M) [Decomposition ℳ]
variable [(i : ι) → (x : (ℳ i)) → Decidable (x ≠ 0)]


-- example (n : ℕ) : n * 2 = n + n := by
--   induction (2 : ℝ)

lemma decompose_unique  (rep₁ rep₂ : ⨁ i, ℳ i)
    (h₁ : (∑ i ∈ rep₂.support, rep₂ i : M) = (∑ i ∈ rep₁.support, rep₁ i)) :

    rep₁ = rep₂ := by
  apply_fun (decompose ℳ).symm
  rw [← sum_support_decompose ℳ (r := (decompose ℳ).symm rep₁),
    ← sum_support_decompose ℳ (r := (decompose ℳ).symm rep₂)]
  simp only [Equiv.apply_symm_apply]
  exact h₁.symm


def decomp_ring_ortho_idem (I : Type u) [Fintype I] [DecidableEq I]
    (V : I → Submodule R R) [Decomposition V] (e : ⨁ (i : I), (V i))
    [(i : I) → (x : ↥(V i)) → Decidable (x ≠ 0)]
    (he : (1 : R) = ∑ j ∈ e.support, e j):
    OrthogonalIdempotents (R := R) (I := DFinsupp.support e) fun i ↦ e i where
  idem i := by
    change _ = _
    let x : (⨁ i, V i) := DFinsupp.single i (e i) -- 0,0,0,...,eᵢ,0,0,0,...
    let y : (⨁ i, V i) := DFinsupp.mapRange (x := e) (fun j (z : V j) => ⟨e i * (z : R), by
      rw [← smul_eq_mul] ; obtain ⟨z, hz⟩ := z
      exact Submodule.smul_mem (V j) (↑(e ↑i)) hz ⟩)
      fun i' ↦ by simp only [ZeroMemClass.coe_zero, mul_zero, Submodule.mk_eq_zero]
    have hx1 : x i = e i := by simp [x]
    have hx2 (j) (h : j ≠ i) : (x j : R) = 0 := by
      simp [x, Finsupp.single_apply]
      intro hij ; exfalso
      exact h.symm $ Subtype.coe_inj.1 hij
    have hy (j) : (y j : R) = e i * e j := by
      simp only [DFinsupp.mapRange_apply, y]
    have hx3 : ∑ i ∈ DFinsupp.support x, (x i : R) = x i := by
      apply Finset.sum_eq_single
      · intro j hj hj'
        specialize hx2 ⟨j, by
          simp_all [↓reduceDIte, x, y]
          obtain ⟨val, property⟩ := i
          obtain ⟨w, h⟩ := hj
          subst w
          simp_all only [Subtype.mk.injEq, not_true_eq_false]⟩ $ Subtype.coe_ne_coe.1 hj'
        exact hx2
      · simp
    have hy3 : ∑ i ∈ DFinsupp.support y, (y i : R) = e i * 1 := by
      rw [he, Finset.mul_sum]
      simp_rw [hy]
      apply Finset.sum_subset
      · intro j hj
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, y] at hj ⊢
        contrapose! hj
        simp [hj, mul_zero]
      · intro x hx hy
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, not_not, y] at hx hy ⊢
        exact (AddSubmonoid.mk_eq_zero (V x).toAddSubmonoid).mp hy
    have : x = y := by
      apply decompose_unique
      rw [hx3, hy3, mul_one]
      simp only [DFinsupp.single_apply, ↓reduceDIte, x]
    have := congr($this i)
    simp [hx1, hy, y, Subtype.ext_iff] at this
    exact this.symm
  ortho := fun i j hij ↦ by
    simp only
    let x : (⨁ i, V i) := DFinsupp.single i (e i) -- 0,0,0,...,eᵢ,0,0,0,...
    let y : (⨁ i, V i) := DFinsupp.mapRange (x := e) (fun j (z : V j) => ⟨e i * (z : R), by
      rw [← smul_eq_mul] ; obtain ⟨z, hz⟩ := z
      exact Submodule.smul_mem (V j) (↑(e ↑i)) hz ⟩)
      fun i' ↦ by simp only [ZeroMemClass.coe_zero, mul_zero, Submodule.mk_eq_zero]
    have hx1 : x i = e i := by simp [x]
    have hx2 (j) (h : j ≠ i) : (x j : R) = 0 := by
      simp [x, Finsupp.single_apply]
      intro hij ; exfalso
      exact h.symm $ Subtype.coe_inj.1 hij
    have hy (j) : (y j : R) = e i * e j := by
      simp only [DFinsupp.mapRange_apply, y]
    have hx3 : ∑ i ∈ DFinsupp.support x, (x i : R) = x i := by
      apply Finset.sum_eq_single
      · intro j hj hj'
        specialize hx2 ⟨j, by
          simp_all [↓reduceDIte, x, y]
          obtain ⟨val, property⟩ := i
          obtain ⟨w, h⟩ := hj
          subst w
          simp_all only [Subtype.mk.injEq, not_true_eq_false]⟩ $ Subtype.coe_ne_coe.1 hj'
        exact hx2
      · simp
    have hy3 : ∑ i ∈ DFinsupp.support y, (y i : R) = e i * 1 := by
      rw [he, Finset.mul_sum]
      simp_rw [hy]
      apply Finset.sum_subset
      · intro j hj
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, y] at hj ⊢
        contrapose! hj
        simp [hj, mul_zero]
      · intro x hx hy
        simp only [DFinsupp.mem_support_toFun, ne_eq, DFinsupp.mapRange_apply,
          AddSubmonoid.mk_eq_zero, not_not, y] at hx hy ⊢
        exact (AddSubmonoid.mk_eq_zero (V x).toAddSubmonoid).mp hy
    have : x = y := by
      apply decompose_unique
      rw [hx3, hy3, mul_one]
      simp only [DFinsupp.single_apply, ↓reduceDIte, x]
    have := congr($this j)
    simp [hx1, hy, y, Subtype.ext_iff, (hx2 j hij.symm)] at this
    exact this.symm


def ortho_idem_component (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) (i : s) :
    (Submodule.span R {∑ i : s, e i}) →ₗ[R] Submodule.span R {e i} where
  toFun := fun x ↦ ⟨x * e i, by
    obtain ⟨r, hx⟩ := Submodule.mem_span_singleton.1 x.2
    rw [← hx, smul_eq_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    apply Ideal.mul_mem_left
    apply Ideal.mul_mem_left
    exact Submodule.mem_span_singleton_self (e i)
    ⟩
  map_add' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    ext
    simp only [Finset.univ_eq_attach, Ideal.submodule_span_eq, AddMemClass.mk_add_mk, add_mul]

  map_smul' := by
    rintro r ⟨x, hx⟩
    simp only [Ideal.submodule_span_eq, SetLike.mk_smul_mk, smul_eq_mul, RingHom.id_apply,
      Subtype.mk.injEq, mul_assoc]

def ortho_idem_directsum (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) (i : s) :
    (Submodule.span R {∑ i : s, e i}) →ₗ[R] ⨁ i : s, Submodule.span R {e i} :=
  DirectSum.lof _ _ _ _ ∘ₗ ortho_idem_component R I s e i

lemma OrthogonalIdempotents.sum_mul_of_mem (I : Type u) [Fintype I]  [DecidableEq I]
    (e : I → R) {i : I} (he : OrthogonalIdempotents e) {s : Finset I} (h : i ∈ s) :
    (∑ j ∈ s, e j) * e i = e i := by
  simp only [Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', h, ↓reduceIte]

lemma orth_idem_directSum_apply_spec (I : Type u) [Fintype I]  [DecidableEq I] (s : Finset I)
    (e : I → R) (i : s) (a : R) (he : OrthogonalIdempotents e) :
    ortho_idem_directsum (e := e) s i ⟨a * ∑ i : s, e i, Submodule.smul_mem _ _ $
      Submodule.mem_span_singleton_self _ ⟩ =
      DirectSum.of _ i ⟨a • e i, Submodule.smul_mem _ _ $ Submodule.mem_span_singleton_self _⟩ := by
    -- DirectSum.mk _ Finset.univ fun ⟨i, _⟩ ↦
    --   ⟨a • e i, Submodule.smul_mem _ _ $ Submodule.mem_span_singleton_self (e i)⟩ := by
  simp only [Ideal.submodule_span_eq, ortho_idem_directsum, ortho_idem_component, smul_eq_mul,
    LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Finset.coe_sort_coe]
  apply DFinsupp.ext
  intro j
  simp only [lof]
  erw [DFinsupp.single_apply]
  split_ifs with h
  · subst h
    ext
    erw [of_apply]
    simp only [↓reduceDIte]
    rw [mul_assoc, Finset.sum_coe_sort s e, OrthogonalIdempotents.sum_mul_of_mem R I e he i.2]
  · ext
    simp only [ZeroMemClass.coe_zero]
    erw [of_apply, dif_neg h]
    rfl

def ortho_idem_directsum_inv_component
    (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) [(i : I) → (x : ↥(Submodule.span R {e i})) → Decidable (x ≠ 0)]
    (j : s) :
    Submodule.span R {e j}  →ₗ[R] Submodule.span R {∑ i : s, e i}  where
  toFun x := ⟨x.1 * (∑ i : s, e i), by
    apply Ideal.mul_mem_left; exact Submodule.mem_span_singleton_self _⟩
  map_add' := fun x y ↦ by
    simp only [Finset.univ_eq_attach, Ideal.submodule_span_eq, Submodule.coe_add, add_mul,
      AddMemClass.mk_add_mk]
  map_smul' := fun r x ↦ by
    simp only [Ideal.submodule_span_eq, SetLike.val_smul, smul_eq_mul, mul_assoc, RingHom.id_apply,
      SetLike.mk_smul_mk]

def ortho_idem_directsum_inv
    (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) [(i : I) → (x : ↥(Submodule.span R {e i})) → Decidable (x ≠ 0)] :
    (⨁ i : s, Submodule.span R {e i}) →ₗ[R] Submodule.span R {∑ i : s, e i} :=
  DirectSum.toModule _ _ _ fun j => ortho_idem_directsum_inv_component R I s e j

lemma ortho_idem_directsum_inv_apply (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) [(i : I) → (x : ↥(Submodule.span R {e i})) → Decidable (x ≠ 0)] (j : s) :
    ortho_idem_directsum_inv R I s e ∘ₗ lof R s (fun i ↦ ↥(Submodule.span R {e i})) j =
    ortho_idem_directsum_inv_component R I s e j  := by
  ext x
  simp only [Ideal.submodule_span_eq, ortho_idem_directsum_inv, ortho_idem_directsum_inv_component,
    LinearMap.comp_apply, toModule_lof, LinearMap.coe_mk, AddHom.coe_mk]

set_option maxHeartbeats 400000 in
lemma aux00 (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) (he : OrthogonalIdempotents e)
    [(i : I) → (x : ↥(Submodule.span R {e i})) → Decidable (x ≠ 0)] (i j : s) :
    (ortho_idem_directsum R I s e j ∘ₗ ortho_idem_directsum_inv_component R I s e i) =
    if i = j then DirectSum.lof R s (fun i => Submodule.span R {e i}) i else 0 := by
  split_ifs with h
  · subst h
    ext x
    simp only [Ideal.submodule_span_eq, ortho_idem_directsum, ortho_idem_component,
      ortho_idem_directsum_inv_component, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp_apply]
    apply DFinsupp.ext
    intro j
    ext
    simp only [lof, SetLike.coe_eq_coe]
    erw [DFinsupp.lsingle_apply, DFinsupp.lsingle_apply, DFinsupp.single_apply,
      DFinsupp.single_apply]
    split_ifs with h
    · subst h
      simp only
      ext
      simp only
      rw [mul_assoc, Finset.sum_coe_sort s e, OrthogonalIdempotents.sum_mul_of_mem R I e he i.2,
        ← (Submodule.mem_span_singleton.1 x.2).choose_spec, smul_mul_assoc, he.1 i]
    · rfl
  · ext x
    simp only [Ideal.submodule_span_eq, ortho_idem_directsum, ortho_idem_component,
      ortho_idem_directsum_inv_component, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp_apply]
    apply DFinsupp.ext
    intro k
    change _ = 0
    ext
    simp only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero]
    simp only [lof]
    erw [DFinsupp.lsingle_apply, DFinsupp.single_apply]
    split_ifs with H
    · subst H
      simp only [Submodule.mk_eq_zero]
      rw [mul_assoc, Finset.sum_coe_sort s e, OrthogonalIdempotents.sum_mul_of_mem (he := he) j.2,
        ← (Submodule.mem_span_singleton.1 x.2).choose_spec, smul_mul_assoc, he.2, smul_zero]
      exact Subtype.coe_ne_coe.mpr h
    · rfl

def ortho_idem_directsum_equiv
    (I : Type u) [Fintype I] [DecidableEq I] (s : Finset I)
    (e : I → R) (he : OrthogonalIdempotents e)
    [(i : I) → (x : ↥(Submodule.span R {e i})) → Decidable (x ≠ 0)] :
    Submodule.span R {∑ i : s, e i}  ≃ₗ[R] (⨁ i : s, Submodule.span R {e i}) :=
  LinearEquiv.ofLinear (∑ i : s, ortho_idem_directsum R I s e i) (ortho_idem_directsum_inv R I s e)
  (by
    classical
    ext i : 1
    simp only [ LinearMap.id_comp]
    rw [LinearMap.comp_assoc, ortho_idem_directsum_inv_apply]
    rw [show (∑ j : s, ortho_idem_directsum R I s e j) ∘ₗ ortho_idem_directsum_inv_component R I s e i =
      (∑ j : s, ortho_idem_directsum R I s e j ∘ₗ ortho_idem_directsum_inv_component R I s e i) by
      ext x
      erw [LinearMap.sum_apply]
      simp]
    rw [show ∑ j : s, ortho_idem_directsum R I s e j ∘ₗ ortho_idem_directsum_inv_component R I s e i =
      ∑ j : s, if i = j then DirectSum.lof R s (fun i => Submodule.span R {e i}) i else 0 by
      refine Finset.sum_congr rfl ?_
      intros j _
      rw [aux00]
      assumption]
    simp) (by
  ext x
  rw [LinearMap.comp_apply]
  simp only [Ideal.submodule_span_eq, LinearMap.id_coe, id_eq, SetLike.coe_eq_coe]
  erw [LinearMap.sum_apply]
  rw [map_sum]
  rcases x with ⟨x, hx⟩
  ext : 1
  simp only [Ideal.submodule_span_eq]
  change Submodule.subtype _ _ = _
  rw [map_sum]
  simp only [Finset.univ_eq_attach, Submodule.coeSubtype]
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  simp only [Finset.coe_sort_coe, smul_eq_mul]

  calc ∑ j : s, (_ : R)
    _ = ∑ j : s, (ortho_idem_directsum_inv R I s e) (DirectSum.of _ j ⟨a • e j,
      Submodule.smul_mem _ _ $ Submodule.mem_span_singleton_self _⟩) := by
      simp only [Ideal.submodule_span_eq, smul_eq_mul, AddSubmonoid.coe_finset_sum,
        Submodule.coe_toAddSubmonoid]
      change _ = Submodule.subtype _ _
      rw [map_sum]

      refine Finset.sum_congr rfl ?_
      intro i _
      erw [orth_idem_directSum_apply_spec (he := he)]
      rfl

  simp only [Finset.univ_eq_attach, Ideal.submodule_span_eq, ortho_idem_directsum_inv, smul_eq_mul]
  rw [← smul_eq_mul, Finset.smul_sum]
  change Submodule.subtype _ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ by
    unfold of --DFinsupp.singleAddHom
    simp only [toModule, DFinsupp.singleAddHom, smul_eq_mul]
    change (((DFinsupp.lsum ℕ) fun j ↦ ortho_idem_directsum_inv_component R I s e j)
      (DFinsupp.single j _)).1 = _
    rw [DFinsupp.lsum_single, ortho_idem_directsum_inv_component]
    simp only [Ideal.submodule_span_eq, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc,
      Finset.sum_coe_sort s e, OrthogonalIdempotents.mul_sum_of_mem he j.2] )

abbrev toDirectsum1 (I : Type u) [Fintype I] [DecidableEq I]
    (e : I → R)
    [(i : I) → (x : (Submodule.span R {e i})) → Decidable (x ≠ 0)] :
  (i : I) →
  { x // x ∈ Submodule.span R {e i} } →ₗ[R]
    ⨁ (i : { x // x ∈ Finset.univ }), { x // x ∈ Submodule.span R {e i.1}} := fun i => {
    toFun := fun x => DFinsupp.lsingle (R := R) ⟨i, Finset.mem_univ _⟩ ⟨x.1, by
      change x.1 ∈ Submodule.span R {e i} ; exact x.2⟩
    map_add' := fun x y => by
      simp only [Ideal.submodule_span_eq, Submodule.coe_add, Subtype.coe_eta]
      apply DFinsupp.ext
      intro j
      simp only [DFinsupp.lsingle_apply, DFinsupp.single_apply, add_apply]
      split_ifs with h1
      · subst h1
        simp only [AddMemClass.mk_add_mk] ; rfl
      · exact AddZeroClass.zero_add _|>.symm
    map_smul' := fun r x => by
      simp only [SetLike.val_smul, RingHom.id_apply, Subtype.coe_eta]
      apply DFinsupp.ext
      intro j
      simp only [Ideal.submodule_span_eq, DFinsupp.lsingle_apply, DFinsupp.single_apply, smul_apply,
        smul_dite, smul_zero]
      split_ifs with h1
      · subst h1
        simp only; rfl
      · rfl
  }

abbrev toDirectsum2 (I : Type u) [Fintype I] [DecidableEq I]
    (e : I → R)
    [(i : I) → (x : (Submodule.span R {e i})) → Decidable (x ≠ 0)] :
    (i : { x // x ∈ Finset.univ }) →
    { x // x ∈ Submodule.span R {e i.1} } →ₗ[R] ⨁ (i : I), { x // x ∈ Submodule.span R {e i} } :=
  fun i => {
    toFun := fun x => DFinsupp.lsingle (R := R) i.1 ⟨x.1, by
      change x.1 ∈ Submodule.span R {e i.1} ; exact x.2⟩
    map_add' := fun x y => by
      simp only [Submodule.coe_add, DFinsupp.lsingle_apply, Subtype.coe_eta]
      apply DFinsupp.ext
      intro j
      simp only [DFinsupp.single_apply, add_apply]
      split_ifs with h1
      · subst h1
        rfl
      · exact AddZeroClass.zero_add _|>.symm
    map_smul' := fun r x => by
      simp only [SetLike.val_smul, DFinsupp.lsingle_apply, RingHom.id_apply, Subtype.coe_eta]
      apply DFinsupp.ext
      intro j
      simp only [DFinsupp.single_apply, smul_apply, smul_dite, smul_zero]
      split_ifs with h1
      · subst h1
        rfl
      · rfl
  }

set_option maxHeartbeats 400000 in
def ortho_idem_decomp_ring (I : Type u) [Fintype I] [DecidableEq I]
    (e : I → R) (he : ∑ i : I, e i  = 1) (he' : OrthogonalIdempotents e)
    [(i : I) → (x : (Submodule.span R {e i})) → Decidable (x ≠ 0)] :
    (⨁ i : I, (Submodule.span R {e i})) ≃ₗ[R] R :=
  (LinearEquiv.ofLinear
  (DirectSum.toModule _ _ _ <|toDirectsum1 R I e)
  (DirectSum.toModule _ _ _ <|toDirectsum2 R I e) (by
  ext j y
  simp only [Subtype.coe_eta, LinearMap.coe_comp, Function.comp_apply,
    toModule_lof, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_comp]
  simp only [toModule]
  erw [DFinsupp.lsum_single]
  simp only [toDirectsum1, subset_refl, Set.coe_inclusion, Subtype.coe_eta,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply DFinsupp.ext
  intro j'
  simp only [DFinsupp.lsingle_apply, DFinsupp.single_apply, Subtype.coe_eta, lof_eq_of, of_apply])
  (by
    ext j y
    simp only [LinearMap.coe_comp, Function.comp_apply, toModule_lof,
      toDirectsum1, Subtype.coe_eta, DFinsupp.lsingle_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.id_comp]
    simp only [toModule]
    erw [DFinsupp.lsum_single]
    apply DFinsupp.ext
    intro i'
    simp only [Ideal.submodule_span_eq, toDirectsum2, Subtype.coe_eta, DFinsupp.lsingle_apply,
      LinearMap.coe_mk, AddHom.coe_mk, DFinsupp.single_apply, lof_eq_of, of_apply] ) :
  (⨁ (i : I), { x // x ∈ Submodule.span R {e i} }) ≃ₗ[R]
  ⨁ (i : { x // x ∈ Finset.univ }), { x // x ∈ Submodule.span R {e i.1} }) ≪≫ₗ
  (ortho_idem_directsum_equiv (he := he') Finset.univ).symm ≪≫ₗ
    LinearEquiv.ofLinear (Submodule.subtype _)
      { toFun := fun r =>
        ⟨r, by
          rw [show r = r • ∑ i, e i by simp [he]]
          apply Submodule.smul_mem;
          rw [show ∑ i : I, e i = ∑ i : {x | x ∈ Finset.univ}, e i.1 from
            (Finset.sum_coe_sort Finset.univ e).symm]
          exact Submodule.mem_span_singleton_self (∑ i : {x | x ∈ Finset.univ}, e i.1)⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl } rfl rfl

end

section indecomp

def Module.Indecomposable (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀(N N' : Submodule R M), ((N × N' ≃ₗ[R] M) → (N = ⊥ ∨ N' = ⊥))

variable (e : R) (he : IsIdempotentElem e)

include he in
lemma indecomp_of_idem (he' : e ≠ (1 : R)) : Module.Indecomposable R (Submodule.span R {e}) ↔
    PrimitiveIdempotents R e := sorry
    -- ⟨fun hI ↦ {
--       idem := he
--       ne_sum_ortho := by
--         classical
--         by_contra! he
--         obtain ⟨I, _, _, e', _, hee', ii, jj, hij⟩ := he
--         obtain ⟨Nontriv, hM⟩ := hI
--         have iso1 := ortho_idem_directsum_equiv R I {ii, jj} e' hee'
--         if hijj : ii = jj then sorry
--         else
--         have heq : ∑ i : { x // x ∈ ({ii, jj} : Finset I) }, e' i.1 = e' ii + e' jj := sorry
--         have singleton_eq : {(∑ i : { x // x ∈ ({ii, jj} : Finset I) }, e' i.1)} =
--           ({e' ii + e' jj} : Set R) := Set.singleton_eq_singleton_iff.2
--             (by
--               rw [Finset.sum_coe_sort {ii, jj} e', Finset.sum_eq_add_of_mem];
--               exact Finset.mem_insert_self ii {jj}
--               exact Finset.mem_insert.2 (by right; exact Finset.mem_singleton_self jj)
--               exact hijj
--               sorry
--               )
--         have eq := LinearEquiv.ofEq _ _ $ Submodule.span_eq_span (R := R) (M := R)
--             (s := {(∑ i : { x // x ∈ ({ii, jj} : Finset I)}, e' i.1)}) (t := {e' ii + e' jj})
--             (Set.singleton_subset_iff.2 (Submodule.mem_span_singleton.2
--               ⟨1, by rw [one_smul]; exact heq.symm⟩)) (Set.singleton_subset_iff.2 $
--               Submodule.mem_span_singleton.2 ⟨1, by rw [one_smul]; exact heq⟩)|>.symm
--         rw [hij] at hM
--         sorry
--     }, fun he => by
--       unfold Module.Indecomposable
--       constructor
--       · refine ⟨⟨e, Submodule.mem_span_singleton_self _⟩, ⟨0, by
--           by_contra! he0
--           -- obtain ⟨_, hno⟩ := he
--           -- have := hno ∅
--           sorry ⟩⟩
--       · sorry⟩
#check JordanHolderModule.instJordanHolderLattice
end indecomp
