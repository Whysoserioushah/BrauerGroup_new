import Mathlib.LinearAlgebra.Matrix.IsDiag

local notation "M[" ι "," R "]" => Matrix ι ι R

universe u v w

section RingEquiv

lemma Matrix.mem_center_iff (R : Type*) [Ring R] (n : ℕ) (M) :
    M ∈ Subring.center M[Fin n, R] ↔ ∃ α : (Subring.center R), M = α • 1 := by
  constructor
  · if h : n = 0 then subst h; exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
    else
      intro h
      rw [Subring.mem_center_iff] at h
      have diag : Matrix.IsDiag M := fun i j hij => by
        simpa only [single_mul_apply_same, one_mul,
          mul_single_apply_of_ne (hbj := hij.symm)] using
          Matrix.ext_iff.2 (h (single i i 1)) i j
      have (i j : Fin n) : M i i = M j j := by
        simpa [Eq.comm] using Matrix.ext_iff.2 (h (single i j 1)) i j
      obtain ⟨b, hb⟩ : ∃ (b : R), M = b • 1 := by
        refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, Matrix.ext fun i j => ?_⟩
        if heq : i = j then subst heq; rw [this i ⟨0, by omega⟩]; simp
        else simp [diag heq, Matrix.one_apply_ne heq]
      suffices b ∈ Subring.center R by aesop
      refine Subring.mem_center_iff.mpr fun g ↦ ?_
      simpa [hb] using Matrix.ext_iff.2 (h (Matrix.diagonal fun _ ↦ g)) ⟨0, by omega⟩ ⟨0, by omega⟩
  · rintro ⟨α, ha⟩; rw [Subring.mem_center_iff]; aesop

def Matrix.centerEquivBase (n : ℕ) (hn : 0 < n) (R : Type*) [Ring R] :
    Subring.center (M[Fin n, R]) ≃+* (Subring.center R) where
  toFun A := ⟨(A.1 ⟨0, by omega⟩ ⟨0, by omega⟩), by
    obtain ⟨a, ha⟩ := (Matrix.mem_center_iff R n A.1).1 A.2
    simpa only [ha, smul_apply, one_apply_eq] using Subring.mul_mem _ a.2 $ Subring.one_mem _⟩
  invFun a := ⟨a • 1, Subring.mem_center_iff.2 fun A ↦ Matrix.ext fun i j => by simp [mul_comm]⟩
  left_inv := by
    if hn : n = 0
    then subst hn; exact fun _ ↦ Subsingleton.elim _ _
    else
    rintro ⟨A, hA⟩; obtain ⟨⟨α, hα⟩, rfl⟩ := Matrix.mem_center_iff _ _ _ |>.1 hA
    simp only [smul_apply, one_apply_eq, Subtype.mk.injEq]
    change (α • (1 : R)) • (1 : Matrix (Fin n) (Fin n) R) = α • (1 : _)
    simp only [smul_eq_mul, mul_one]
  right_inv := by
    intro ⟨r, hr⟩; simp only [smul_apply, one_apply_eq, Subtype.mk.injEq]

    change r • (1 : R) = _
    simp only [smul_eq_mul, mul_one]
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    rw [Matrix.mem_center_iff] at hA hB
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨b, rfl⟩ := hB
    simp only [MulMemClass.mk_mul_mk, mul_smul_one, smul_apply, one_apply_eq]
  map_add' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    rw [Matrix.mem_center_iff] at hA hB
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨b, rfl⟩ := hB
    simp only [AddMemClass.mk_add_mk, add_apply, smul_apply, one_apply_eq]

end RingEquiv

section AlgEquiv

variable (R A: Type u) [CommSemiring R] [Ring A] [Algebra R A]

def Matrix.centerAlgEquiv (n : ℕ) (hn : 0 < n) :
    Subalgebra.center R M[Fin n, A] ≃ₐ[R] Subalgebra.center R A := {
  __ := Matrix.centerEquivBase n hn A
  commutes' := fun _ ↦ rfl }

end AlgEquiv
