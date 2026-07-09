module

public import BrauerGroup.BrauerGroup
public import BrauerGroup.Data.Matrix.Composition
public import BrauerGroup.CentralSimple
public import BrauerGroup.Morita.ChangeOfRings
public import Mathlib.RingTheory.SimpleRing.Congr

@[expose] public section

universe u v

open Module TensorProduct

section Field
variable (K : Type u) [Field K]

lemma TensorProduct.flip_mk_injective {R M N : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] [IsTorsionFree R N] [Flat R M] (a : N) (ha : a ≠ 0) :
    Function.Injective ((TensorProduct.mk R M N).flip a) := by
  intro x y e
  -- simp only [LinearMap.flip_apply, mk_apply] at e
  apply (TensorProduct.rid R M).symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M) (LinearMap.toSpanSingleton R N a)
    (smul_left_injective R ha)
  simpa using e

variable (A : Type u) [Ring A] [Algebra K A]

theorem IsAzumaya_iff_CentralSimple [Nontrivial A] : IsAzumaya K A ↔ FiniteDimensional K A ∧
    Algebra.IsCentral K A ∧ IsSimpleRing A :=
  ⟨fun ⟨bij⟩ ↦
    letI e := AlgEquiv.ofBijective _ bij|>.trans <| algEquivMatrix <| Module.finBasis _ _
    letI : Nonempty (Fin (Module.finrank K A)) := ⟨⟨_, Module.finrank_pos⟩⟩
    ⟨IsAzumaya.toFinite, ⟨by
    have : Algebra.IsCentral K (A ⊗[K] Aᵐᵒᵖ) := Algebra.IsCentral.of_algEquiv K _ _ e.symm
    exact Algebra.IsCentral.left_of_tensor_of_field K A Aᵐᵒᵖ, by
    haveI := IsSimpleRing.matrix (Fin (Module.finrank K A)) K
    have sim : IsSimpleRing (A ⊗[K] Aᵐᵒᵖ) := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv this
    exact IsSimpleRing.left_of_tensor K A Aᵐᵒᵖ⟩⟩,
    fun ⟨fin, cen, sim⟩ ↦ {
      out := Module.Projective.out
      eq_of_smul_eq_smul {k1} {k2} ha := by
        specialize ha (1 : A)
        rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at ha
        exact FaithfulSMul.algebraMap_injective _ _ ha
      fg_top := fin.1
      bij := bijective_of_dim_eq_of_simple K _ _
        (AlgHom.mulLeftRight K A) <| tensor_self_op.dim_eq _ _
    }⟩

def finswap {n m : ℕ} : Fin (n * m) ≃ Fin (m * n) where
  toFun i := ⟨i.1, by rw [mul_comm m n]; exact i.2⟩
  invFun i := ⟨i.1, by rw [mul_comm n m]; exact i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open ModuleCat in
lemma IsMorita_iff_IsBrauer' (R : Type u) [CommRing R] (A B : Type v) [Ring A] [Ring B]
    [IsSimpleRing A] [IsSimpleRing B] [IsArtinianRing A] [IsArtinianRing B] [Algebra R A]
    [Algebra R B] :
    IsMoritaEquivalent R A B ↔ ∃(n m : ℕ), n ≠ 0 ∧ m ≠ 0 ∧ (Nonempty <|
    Matrix (Fin n) (Fin n) A ≃ₐ[R] Matrix (Fin m) (Fin m) B) := ⟨fun hAB ↦
  by
    obtain ⟨n, hn, D, _, _, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version' R A
    obtain ⟨m, hm, E, _, _, ⟨e'⟩⟩ := Wedderburn_Artin_algebra_version' R B
    letI e1 := MoritaEquivalence.ofAlgEquiv e
    letI e2 := MoritaEquivalence.ofAlgEquiv e'
    have : NeZero m := ⟨hm⟩
    have : NeZero n := ⟨hn⟩
    haveI := moritaEquivalenceMatrix D R (0 : Fin n) |>.symm
    have ww := MoritaEquivalence.trans R e1 this |>.symm
    haveI := moritaEquivalenceMatrix E R (0 : Fin m) |>.symm
    have ww' := MoritaEquivalence.trans R e2 this
    haveI h := MoritaEquivalence.trans R ww hAB.cond.some
    haveI h' := MoritaEquivalence.trans R h ww'
    have := MoritaEquivalence.algEquivOfDivisionRing R D E h'
    refine ⟨m, n, hm, hn, ⟨e.mapMatrix.trans <| Matrix.compFinAlgEquiv _ _ _ _ |>.trans <|
      this.mapMatrix.trans <| Matrix.reindexAlgEquiv _ _ finswap|>.trans <|
      (Matrix.compFinAlgEquiv _ _ _ _).symm.trans e'.symm.mapMatrix⟩⟩,
  fun ⟨n, m, hn, hm, ⟨e⟩⟩ ↦
  letI : NeZero n := ⟨hn⟩
  letI : NeZero m := ⟨hm⟩
  ⟨⟨MoritaEquivalence.trans R (MoritaEquivalence.trans R
    (moritaEquivalenceMatrix A R (0 : Fin n)) (MoritaEquivalence.ofAlgEquiv e))
      (moritaEquivalenceMatrix B R (0 : Fin m)).symm⟩⟩⟩

open ModuleCat in
theorem IsMorita_iff_IsBrauer (A B : CSA.{u, v} K) :
    IsMoritaEquivalent K A B ↔ IsBrauerEquivalent (K := K) A B :=
  haveI : IsArtinianRing A := .of_finite K A
  haveI : IsArtinianRing B := .of_finite K B
  IsMorita_iff_IsBrauer' K A B

end Field

section Matrix

open scoped TensorProduct

variable (R : Type u) [CommRing R]

instance (n : ℕ) [NeZero n] : FaithfulSMul R (Matrix (Fin n) (Fin n) R) where
  eq_of_smul_eq_smul {r1 r2} h12 := by
    specialize h12 (1 : Matrix _ _ _)
    rw [← Matrix.ext_iff] at h12
    specialize h12 ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero _⟩
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h12
    exact h12

open MulOpposite in
abbrev matrixAlgEquivMatrixMop (n : ℕ) :
  Matrix (Fin n) (Fin n) R ≃ₐ[R] (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
  (AlgEquiv.toOpposite R R).mapMatrix.trans <| AlgEquiv.ofRingEquiv
  (f := RingEquiv.mopMatrix) <|
  fun r ↦ by
    simp only [RingEquiv.mopMatrix_apply, MulOpposite.algebraMap_apply, op_inj]
    ext i j
    simp [Matrix.algebraMap_matrix_apply]
    split_ifs with h1 h2 h3 <;> tauto

noncomputable abbrev mopAlgEquivEnd : Rᵐᵒᵖ ≃ₐ[R] Module.End R R := AlgEquiv.moduleEndSelf R

instance (n : ℕ) [NeZero n] : FaithfulSMul R (Matrix (Fin n) (Fin n) R) where
  eq_of_smul_eq_smul {r1 r2} h := by
    specialize h 1
    rw [← Matrix.ext_iff] at h
    specialize h ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    exact h

end Matrix
