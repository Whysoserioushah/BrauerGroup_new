import BrauerGroup.Morita.ChangOfRings
import BrauerGroup.BrauerGroup
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import BrauerGroup.Azumaya.Defs
import Mathlib.Algebra.Central.Matrix
import BrauerGroup.LemmasAboutSimpleRing

universe u v

open TensorProduct

section Morita

end Morita

variable (K : Type u) [Field K]

lemma TensorProduct.flip_mk_injective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [NoZeroSMulDivisors R N] [Module.Flat R M] (a : N) (ha : a ≠ 0) :
    Function.Injective ((TensorProduct.mk R M N).flip a) := by
  intro x y e
  -- simp only [LinearMap.flip_apply, mk_apply] at e
  apply (TensorProduct.rid R M).symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M) (LinearMap.toSpanSingleton R N a)
    (smul_left_injective R ha)
  simpa using e

lemma IsCentral.left_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Nontrivial B] [Nontrivial C] [Algebra K C] [Algebra K B]
    [FiniteDimensional K B] [hbc : Algebra.IsCentral K (B ⊗[K] C)] :
    Algebra.IsCentral K B := by
  letI : Nontrivial (B ⊗[K] C) := Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  have h := (Subalgebra.equivOfEq (R := K) (A := B ⊗[K] C) _ _ <|
    hbc.center_eq_bot K (B ⊗[K] C)) |>.trans <| Algebra.botEquiv K (B ⊗[K] C)
  have : (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range ≤
    Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
    simp only [AlgHom.mem_range, AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Subtype.exists, exists_prop] at hx
    obtain ⟨b, hb0, hb⟩ := hx
    rw [Subalgebra.mem_center_iff] at hb0 ⊢
    intro bc
    induction bc using TensorProduct.induction_on with
    | zero => simp
    | tmul b' c =>
      subst hb
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      congr 1
      exact hb0 b'
    | add _ _ _ _ => simp_all [add_mul, mul_add]
  have eq: (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range =
      (⊥ : Subalgebra K (B ⊗[K] C)) := by
    refine le_antisymm ?_ <| OrderBot.bot_le _
    rw [← hbc.center_eq_bot]; exact this
  let f : Subalgebra.center K B →ₐ[K] ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range := {
      toFun := fun ⟨b, hb⟩ ↦ ⟨b ⊗ₜ 1, ⟨⟨b, hb⟩, rfl⟩⟩
      map_one' := by simp; rfl
      map_mul' := fun _ _ ↦ by ext : 1; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [add_tmul]
      commutes' := fun _ ↦ rfl}
  have f_surj : Function.Surjective f := fun ⟨bc, ⟨⟨b, hb⟩, h⟩⟩ ↦ ⟨⟨b, hb⟩, by
    simp [f]
    change _ ⊗ₜ _ = _ at h
    simp only [RingHom.coe_coe, Subalgebra.coe_val] at h⊢
    exact h⟩

  have e : ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range ≃ₐ[K] (Subalgebra.center K B) :=
    (AlgEquiv.ofBijective f
    ⟨fun ⟨b1, hb1⟩ ⟨b2, hb2⟩ h12 ↦ by
      simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Subtype.mk.injEq, f] at h12
      ext ; simp only [f]
      exact TensorProduct.flip_mk_injective _ one_ne_zero h12,
    f_surj⟩).symm
  have e2 := Subalgebra.equivOfEq _ _ eq |>.trans <| Algebra.botEquiv K _
  have ee: Subalgebra.center K B ≃ₐ[K] K := e.symm.trans e2
  exact ⟨le_of_eq <| Subalgebra.eq_of_le_of_finrank_eq (OrderBot.bot_le _)
    (by rw [ee.toLinearEquiv.finrank_eq, Subalgebra.finrank_bot, Module.finrank_self])|>.symm⟩

variable (A : Type u) [Ring A] [Algebra K A]

lemma Algebra.IsCentral_ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (hA : Algebra.IsCentral K A):  Algebra.IsCentral K B where
  out x hx := by
    obtain ⟨k, hk⟩ := hA.1 (show e.symm x ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hx ⊢
      exact fun x => by simpa using congr(e.symm $(hx (e x))))
    exact ⟨k, by apply_fun e.symm; rw [← hk]; simp [ofId_apply]⟩

lemma IsSimpleRing.ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (hA : IsSimpleRing A) : IsSimpleRing B :=
  ⟨OrderIso.isSimpleOrder_iff (TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv)|>.1 hA.1⟩

theorem IsAzumaya_iff_CentralSimple [Nontrivial A]: IsAzumaya K A ↔ FiniteDimensional K A ∧
    Algebra.IsCentral K A ∧ IsSimpleRing A :=
  ⟨fun ⟨bij⟩ ↦
    letI e := AlgEquiv.ofBijective _ bij|>.trans <| algEquivMatrix <| Module.finBasis _ _
    letI : Nonempty (Fin (Module.finrank K A)) := ⟨⟨_, Module.finrank_pos⟩⟩
    ⟨IsAzumaya.toFinite, ⟨by
    have : Algebra.IsCentral K (A ⊗[K] Aᵐᵒᵖ) :=
      Algebra.IsCentral_ofAlgEquiv K _ _ e.symm <| Algebra.IsCentral.matrix K K
        (Fin (Module.finrank K A))
    exact IsCentral.left_of_tensor K A Aᵐᵒᵖ, by
    haveI := IsSimpleRing.matrix (Fin (Module.finrank K A)) K
    have sim : IsSimpleRing (A ⊗[K] Aᵐᵒᵖ) := IsSimpleRing.ofAlgEquiv K _ _ e.symm this
    exact IsSimpleRing.left_of_tensor K A Aᵐᵒᵖ⟩⟩,
    fun ⟨fin, cen, sim⟩ ↦ {
      out := Module.Projective.out
      eq_of_smul_eq_smul {k1} {k2} ha := by
        specialize ha (1 : A)
        rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at ha
        exact NoZeroSMulDivisors.algebraMap_injective _ _ ha
      fg_top := fin.1
      bij := bijective_of_dim_eq_of_isCentralSimple K _ _
        (AlgHom.mulLeftRight K A) <| tensor_self_op.dim_eq _ _
    }⟩

def finswap {n m : ℕ}: Fin (n * m) ≃ Fin (m * n) where
  toFun i := ⟨i.1, by rw [mul_comm m n]; exact i.2⟩
  invFun i := ⟨i.1, by rw [mul_comm n m]; exact i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open ModuleCat in
lemma IsMorita_iff_IsBrauer' (R : Type u) [CommRing R] (A B : Type v) [Ring A] [Ring B]
    [IsSimpleRing A] [IsSimpleRing B] [IsArtinianRing A] [IsArtinianRing B] [Algebra R A]
    [Algebra R B]:
    IsMoritaEquivalent R A B ↔ ∃(n m : ℕ), n ≠ 0 ∧ m ≠ 0 ∧ (Nonempty <|
    Matrix (Fin n) (Fin n) A ≃ₐ[R] Matrix (Fin m) (Fin m) B) := ⟨fun hAB ↦
  by
    obtain ⟨n, hn, D, _, _, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version' R A
    obtain ⟨m, hm, E, _, _, ⟨e'⟩⟩ := Wedderburn_Artin_algebra_version' R B
    letI e1 := MoritaEquivalence.ofAlgEquiv e
    letI e2 := MoritaEquivalence.ofAlgEquiv e'
    haveI := MoritaEquivalence.matrix' R D n |>.symm
    have ww := MoritaEquivalence.trans R e1 this |>.symm
    haveI := MoritaEquivalence.matrix' R E m |>.symm
    have ww' := MoritaEquivalence.trans R e2 this
    haveI h := MoritaEquivalence.trans R ww hAB.cond.some
    haveI h' := MoritaEquivalence.trans R h ww'
    have := MoritaEquivalence.algEquivOfDivisionRing R D E h'
    refine ⟨m, n, hm.1, hn.1, ⟨e.mapMatrix.trans <| Matrix.compAlgEquiv _ _ _ _ |>.trans <|
      Matrix.reindexAlgEquiv _ _ finProdFinEquiv |>.trans <| this.mapMatrix.trans <|
      Matrix.reindexAlgEquiv _ _ finswap|>.trans <| Matrix.reindexAlgEquiv _ _
      finProdFinEquiv.symm |>.trans <| Matrix.compAlgEquiv _ _ _ _|>.symm.trans
      e'.symm.mapMatrix⟩⟩,
  fun ⟨n, m, hn, hm, ⟨e⟩⟩ ↦
  letI : NeZero n := ⟨hn⟩
  letI : NeZero m := ⟨hm⟩
  ⟨⟨MoritaEquivalence.trans R (MoritaEquivalence.trans R
    (MoritaEquivalence.matrix' R A n) (MoritaEquivalence.ofAlgEquiv e))
      (MoritaEquivalence.matrix' R B m).symm⟩⟩⟩

open ModuleCat in
theorem IsMorita_iff_IsBrauer (A B : CSA.{u, v} K):
    IsMoritaEquivalent K A B ↔ IsBrauerEquivalent (K := K) A B :=
  haveI : IsArtinianRing A := .of_finite K A
  haveI : IsArtinianRing B := .of_finite K B
  IsMorita_iff_IsBrauer' K A B

#print axioms IsMorita_iff_IsBrauer
