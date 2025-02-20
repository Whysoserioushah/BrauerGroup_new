import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import BrauerGroup.FrobeniusTheorem

suppress_compilation

open Quaternion BrauerGroup TensorProduct

set_option synthInstance.maxHeartbeats 40000 in
instance : Module ℝ (Module.End ℝ ℍ[ℝ]) := inferInstance

set_option synthInstance.maxHeartbeats 40000 in
instance : Algebra ℝ (Module.End ℝ ℍ[ℝ]) := inferInstance

abbrev toEnd_map_aux (q1 q2 : ℍ[ℝ]): Module.End ℝ ℍ[ℝ] where
    toFun x := q1 * x * (star q2)
    map_add' x1 x2 := by simp [mul_add, add_mul]
    map_smul' r x := by simp

abbrev toEnd_map_aux' (q1 : ℍ[ℝ]): ℍ[ℝ] →ₗ[ℝ] Module.End ℝ ℍ[ℝ] where
  toFun q2 := toEnd_map_aux q1 q2
  map_add' x1 x2 := by ext : 1; simp [mul_add]
  map_smul' r x := by ext : 1; simp [Algebra.mul_smul_comm _ _ (star x)]

abbrev toEnd_map : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] →ₗ[ℝ] Module.End ℝ (ℍ[ℝ]) := TensorProduct.lift {
  toFun := fun q1 ↦ toEnd_map_aux' q1
  map_add' := fun x1 x3 ↦ by ext : 2 ; simp [add_mul]
  map_smul' := fun r x ↦ by ext : 2 ; simp
}

lemma toEnd_map.map_mul (x1 x2 : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]): toEnd_map (x1 * x2) =
    toEnd_map x1 * toEnd_map x2 := by
  induction x1 using TensorProduct.induction_on with
  | zero => simp
  | tmul q1 q2 =>
    induction x2 using TensorProduct.induction_on with
    | zero => simp
    | tmul q3 q4 => ext : 1; simp [← _root_.mul_assoc]
    | add x y h1 h2 =>
      rw [mul_add, map_add, map_add, mul_add, h1, h2]
  | add x y h1 h2 => rw [add_mul, map_add, map_add, add_mul, h1, h2]

abbrev toEnd : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] →ₐ[ℝ] Module.End ℝ (ℍ[ℝ]) where
  toFun := toEnd_map
  map_one' := by ext : 1; simp [Algebra.TensorProduct.one_def]
  map_mul' := toEnd_map.map_mul
  map_zero' := rfl
  map_add' := toEnd_map.map_add
  commutes' r := by ext : 1; simp only [Algebra.TensorProduct.algebraMap_apply,
    algebraMap_def, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, star_one, _root_.mul_one,
    Module.algebraMap_end_apply]; exact coe_mul_eq_smul r _

instance : Algebra.IsCentral ℝ ℍ[ℝ] := ⟨fun q hq ↦ by
  rw [Subalgebra.mem_center_iff] at hq
  change ∃(_ : _), _ = _
  use q.1
  let eq1 := hq ⟨0, 1, 0, 0⟩
  let eq2 := hq ⟨0, 0, 1, 0⟩
  let eq3 := hq ⟨0, 0, 0, 1⟩
  rw [Quaternion.ext_iff] at eq1 eq2 eq3
  obtain ⟨_, _, eq13, eq14⟩ := eq1
  obtain ⟨_, eq22, _, eq24⟩ := eq2
  obtain ⟨_, eq32, eq33, _⟩ := eq3
  simp only [mul_re, zero_mul, _root_.one_mul, zero_sub, sub_zero, mul_zero, _root_.mul_one,
    mul_imI, zero_add, add_zero, mul_imJ, sub_self, mul_imK, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at *
  simp [self_eq_neg ℝ ℝ, neg_eq_self ℝ ℝ] at *
  change (⟨q.1, 0, 0, 0⟩ : ℍ[ℝ]) = ⟨q.1, q.2,q.3,q.4⟩
  ext <;> simp_all⟩

instance : IsSimpleRing (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) := IsCentralSimple.TensorProduct.simple _ _ _

lemma toEnd_bij : Function.Bijective toEnd :=
  bijective_of_dim_eq_of_isCentralSimple ℝ (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) (Module.End ℝ ℍ[ℝ]) toEnd <| by
    rw [show Module.finrank ℝ (Module.End ℝ _) =
      Module.finrank ℝ (Matrix (Fin $ Module.finrank ℝ ℍ[ℝ]) (Fin $ Module.finrank ℝ ℍ[ℝ]) ℝ) from
      (algEquivMatrix $ Module.finBasis _ _).toLinearEquiv.finrank_eq]
    simp [Quaternion.finrank_eq_four, Fintype.card_fin, Module.finrank_matrix]

def QuaternionTensorEquivMatrix : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (AlgEquiv.ofBijective toEnd toEnd_bij).trans <| algEquivMatrix
    (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1 : ℝ))

lemma QuaternionTensorEquivOne : IsBrauerEquivalent (K := ℝ) ⟨ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]⟩ ⟨ℝ⟩ :=
  ⟨⟨1, 4, dim_one_iso _ |>.trans QuaternionTensorEquivMatrix⟩⟩

lemma QuaternionNotEquivR : ¬ IsBrauerEquivalent (K := ℝ) ⟨ℍ[ℝ]⟩ ⟨ℝ⟩ := by
  intro h
  obtain ⟨⟨n, m, e⟩⟩ := h
  obtain ⟨e'⟩ := Wedderburn_Artin_uniqueness₀ ℝ (Matrix (Fin n) (Fin n) ℍ[ℝ])
    n m ℍ[ℝ] AlgEquiv.refl ℝ e
  have eq2 := e'.toLinearEquiv.finrank_eq
  simp only [Module.finrank_self] at eq2
  haveI := eq2.symm.trans <| Quaternion.finrank_eq_four (R := ℝ)
  norm_num at this

lemma BrauerOverR (A : CSA.{0, 0} ℝ) : IsBrauerEquivalent A ⟨ℝ⟩ ∨ IsBrauerEquivalent A ⟨ℍ[ℝ]⟩ := by
  if h : IsBrauerEquivalent A ⟨ℝ⟩ then left; assumption
  else
  right
  obtain ⟨n, ⟨hn, D, _, _, ⟨e⟩⟩⟩ := Wedderburn_Artin_algebra_version.{0, 0} ℝ A
  letI := A.6
  letI : FiniteDimensional ℝ D := is_fin_dim_of_wdb ℝ A n D e
  have hD := FrobeniusTheorem D
  cases' hD with hD1 hD2
  · obtain ⟨e'⟩ := hD1
    have := is_central_of_wdb ℝ A n D e|>.center_eq_bot
    have e2 : Subalgebra.center ℝ D ≠ ⊥ := by
      refine ne_of_gt ?_
      letI : Algebra ℂ D := RingHom.toAlgebra' e'.symm <| fun z d ↦ by
        simp only [RingHom.coe_coe]
        rw [← e'.symm_apply_apply d, ← map_mul, mul_comm, map_mul]
      letI : IsScalarTower ℝ ℂ D := {
        smul_assoc := fun r z d ↦ by
          change e'.symm _  * _ = _ • (e'.symm z * d)
          rw [map_smul, Algebra.smul_mul_assoc]
      }
      have : Subalgebra.center ℝ D = ⊤ := by
        apply le_antisymm (fun _ _ ↦ trivial) <| by
          rintro d -
          rw [Subalgebra.mem_center_iff]
          intro d'
          rw [← e'.symm_apply_apply d, ← e'.symm_apply_apply d']
          conv_lhs => rw [← _root_.map_mul e'.symm, mul_comm, map_mul]
      rw [this]
      exact SetLike.lt_iff_le_and_exists.2 ⟨fun _ _ ↦ ⟨⟩, ⟨e'.symm Complex.I, ⟨⟨⟩, by
        by_contra! mem
        change ∃(_ : _), _ = _ at mem
        obtain ⟨r, eq⟩ := mem
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at eq
        apply_fun e' at eq
        rw [e'.apply_symm_apply] at eq
        rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, map_smul, map_one] at eq
        simp only [Complex.real_smul, _root_.mul_one] at eq
        rw [Complex.ext_iff] at eq
        obtain ⟨_, fal⟩ := eq
        simp only [Complex.ofReal_im, Complex.I_im, zero_ne_one] at fal⟩⟩⟩
    tauto
  · cases' hD2 with hD2 hD3
    · have : IsBrauerEquivalent A ⟨ℝ⟩ :=
        ⟨⟨1, n, dim_one_iso A|>.trans <| e.trans hD2.some.mapMatrix⟩⟩
      tauto
    · exact ⟨⟨1, n, dim_one_iso A |>.trans <| e.trans hD3.some.mapMatrix⟩⟩

open scoped Classical in
abbrev toC2 : Additive (BrauerGroup.BrGroup (K := ℝ)) →+ ZMod 2 where
  toFun := Quotient.lift (fun A ↦ if h1 : IsBrauerEquivalent A (one_in')
    then 0 else 1) <|
    fun A B hAB ↦ by
      change IsBrauerEquivalent _ _ at hAB
      if h : IsBrauerEquivalent A (BrauerGroup.one_in') then
        simp [h, hAB.symm.trans h]
      else
        simp [h]
        have : ¬ IsBrauerEquivalent B (BrauerGroup.one_in') := by
          by_contra!
          haveI := hAB.trans this
          tauto
        simp [this]
  map_zero' := by
    change Quotient.lift _ _ (Quotient.mk'' (BrauerGroup.one_in')) = 0
    simp only [dite_eq_ite, Quotient.lift_mk, ite_eq_left_iff, not_nonempty_iff, one_ne_zero,
      imp_false, not_isEmpty_iff]
    exact IsBrauerEquivalent.refl _
  map_add' A B := by
    induction' A using Quotient.inductionOn' with A
    induction' B using Quotient.inductionOn' with B
    have hab' : @HAdd.hAdd (Additive BrGroup) (Additive BrGroup)
      (Additive BrGroup) instHAdd (Quotient.mk'' A) (Quotient.mk'' B)=
      (Quotient.mk'' (mul A B) : Additive _) := rfl
    rw [hab']
    simp
    if hA : IsBrauerEquivalent A one_in' then
      if hB : IsBrauerEquivalent B one_in' then
        simp only [hA, ↓reduceIte, hB, add_zero, ite_eq_left_iff, not_nonempty_iff, one_ne_zero,
          imp_false, not_isEmpty_iff]
        have := eqv_tensor_eqv _ _ _ _ hA hB
        refine this.trans ?_
        change IsBrauerEquivalent ⟨ℝ ⊗[ℝ] ℝ⟩ ⟨ℝ⟩
        exact IsBrauerEquivalent.iso_to_eqv _ _ (BrauerGroupHom.someEquivs.e7.symm)
      else
      simp only [hA, ↓reduceIte, hB, zero_add, ite_eq_right_iff, zero_ne_one, imp_false]
      have : IsBrauerEquivalent (mul A B) B := by
        obtain ⟨⟨n, m, e⟩⟩ := hA
        exact ⟨⟨n * 1, m * 1, ((kroneckerMatrixTensor' A B n 1).symm.trans
          <| (Algebra.TensorProduct.congr e AlgEquiv.refl).trans
          <| (kroneckerMatrixTensor' ℝ B m 1).trans <| AlgEquiv.mapMatrix (
            Algebra.TensorProduct.lid _ _) : Matrix _ _ (A ⊗[ℝ] B) ≃ₐ[ℝ] Matrix _ _ B)⟩⟩
      -- rw [this]
      by_contra! hBB
      haveI := this.symm.trans hBB
      tauto
    else
    if hB : IsBrauerEquivalent B one_in' then
      simp only [hA, ↓reduceIte, hB, add_zero, ite_eq_right_iff, zero_ne_one, imp_false]
      have : IsBrauerEquivalent (mul A B) A := by
        obtain ⟨⟨n, m, e⟩⟩ := hB
        exact ⟨⟨1 * n, 1 * m, ((kroneckerMatrixTensor' A B 1 n).symm.trans
          <| (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
          <| (kroneckerMatrixTensor' A ℝ 1 m).trans <| AlgEquiv.mapMatrix (
            Algebra.TensorProduct.rid _ _ _) : Matrix _ _ (A ⊗[ℝ] B) ≃ₐ[ℝ] Matrix _ _ A)⟩⟩
      by_contra! hAA
      haveI := this.symm.trans hAA
      tauto
    else
    simp only [hA, ↓reduceIte, hB]
    change _ = 0
    change ¬ IsBrauerEquivalent _ ⟨ℝ⟩ at hA hB
    have hA1 := BrauerOverR A
    have hB1 := BrauerOverR B
    simp only [hA, false_or] at hA1
    simp only [hB, false_or] at hB1
    obtain ⟨⟨n1, m1, e1⟩⟩ := hA1
    obtain ⟨⟨n2, m2, e2⟩⟩ := hB1
    have : IsBrauerEquivalent (mul A B) one_in' :=
      ⟨⟨n1 * n2, m1 * m2 * 4, (kroneckerMatrixTensor' _ _ _ _ |>.symm.trans <|
        Algebra.TensorProduct.congr e1 e2 |>.trans <| kroneckerMatrixTensor' _ _ _ _ |>.trans <|
        QuaternionTensorEquivMatrix.mapMatrix.trans <| Matrix.compAlgEquiv _ _ _ _ |>.trans <|
        IsBrauerEquivalent.matrix_eqv' _ _ _ : Matrix _ _ (A ⊗[ℝ] B) ≃ₐ[ℝ] Matrix _ _ ℝ)⟩⟩
    simp [this]

-- lemma toC2_surjective : Function.Surjective toC2 := fun x ↦ by
--     fin_cases x
--     · use Quotient.mk'' one_in'
--       simp [IsBrauerEquivalent.refl]
--     · use Quotient.mk'' ⟨ℍ[ℝ]⟩
--       simp only [AddMonoidHom.coe_mk, dite_eq_ite, ZeroHom.coe_mk, Quotient.lift_mk, Nat.reduceAdd,
--         Fin.mk_one, Fin.isValue, ite_eq_right_iff, zero_ne_one, imp_false]
--       exact QuaternionNotEquivR

abbrev C2toBrauerOverR : ZMod 2 →+ Additive (BrauerGroup.BrGroup (K := ℝ)) where
  toFun x := if hx : x = 0 then Quotient.mk'' one_in' else Quotient.mk'' ⟨ℍ[ℝ]⟩
  map_zero' := by simp only [↓reduceDIte]; rfl
  map_add' x y := by
    fin_cases x <;> fin_cases y <;> simp <;> try rfl
    erw [show 1 + 1 = (0 : ZMod 2) from rfl]
    simp only [↓reduceIte]
    change _ = Quotient.mk'' _
    rw [Quotient.sound']
    change IsBrauerEquivalent _ ⟨ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]⟩
    exact QuaternionTensorEquivOne.symm

lemma toC2.left_inv : Function.LeftInverse C2toBrauerOverR toC2 := fun A ↦ by
  induction' A using Quotient.inductionOn' with A
  cases' (BrauerOverR A) with h1 h2
  · change IsBrauerEquivalent A one_in' at h1
    simp only [AddMonoidHom.coe_mk, dite_eq_ite, ZeroHom.coe_mk, Quotient.lift_mk, h1, ↓reduceIte]
    rw [Quotient.sound']; exact h1.symm
  · have : ¬ (IsBrauerEquivalent A one_in') := fun h ↦ QuaternionNotEquivR <| h2.symm.trans h
    simp [this]
    exact Quotient.sound' h2.symm

lemma toC2.right_inv : Function.RightInverse C2toBrauerOverR toC2 := fun x ↦ by
  fin_cases x
  · simp [IsBrauerEquivalent.refl]
  · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, AddMonoidHom.coe_mk, dite_eq_ite,
    ZeroHom.coe_mk, one_ne_zero, ↓reduceIte, Quotient.lift_mk, ite_eq_right_iff, zero_ne_one,
    imp_false]; exact QuaternionNotEquivR

def BrauerGroupOverR : Additive (BrauerGroup.BrGroup (K := ℝ)) ≃+ ZMod 2 where
  toFun := toC2
  invFun := C2toBrauerOverR
  left_inv := toC2.left_inv
  right_inv := toC2.right_inv
  map_add' := toC2.map_add
