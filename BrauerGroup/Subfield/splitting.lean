import BrauerGroup.Subfield.Subfield
import BrauerGroup.«074E»
import BrauerGroup.faithfullyflat
import BrauerGroup.RelativeBrauer
import Mathlib.RingTheory.MatrixAlgebra
import BrauerGroup.SplittingOfCSA

universe u

variable (K F : Type u) [Field K] [Field F] [Algebra F K]

open FiniteDimensional MulOpposite BrauerGroup BigOperators TensorProduct

section CSA

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 40000 in
set_option maxSynthPendingDepth 2 in
lemma exists_embedding_of_isSplit [FiniteDimensional F K] (A : CSA F) (split : isSplit F A K) :
    ∃ (B : CSA F), (Quotient.mk'' A : BrGroup) * (Quotient.mk'' B) = 1 ∧
      ∃ (ι : K →ₐ[F] B), (finrank F K)^2 = finrank F B := by
  obtain ⟨n, hn, ⟨iso⟩⟩ := split
  let iso' := iso.trans (algEquivMatrix' (R := K) (n := Fin n)).symm
  let emb : A →ₐ[F] Module.End F (Fin n → K) :=
    AlgHom.comp (AlgHom.comp
      { toFun := fun f => f.restrictScalars F
        map_one' := by ext; rfl
        map_mul' := by intros; ext; rfl
        map_zero' := by ext; rfl
        map_add' := by intros; ext; rfl
        commutes' := by intros; ext; rfl } <| iso'.toAlgHom.restrictScalars F) <|
      Algebra.TensorProduct.includeRight (R := F) (A := K) (B := A)
  let B := Subalgebra.centralizer F (AlgHom.range emb : Set (Module.End F (Fin n → K)))
  let e : A ≃ₐ[F] (AlgHom.range emb) :=
    AlgEquiv.ofInjective _ (by
      refine TwoSidedIdeal.IsSimpleOrder.iff_eq_zero_or_injective A |>.1 inferInstance
        emb.toRingHom |>.resolve_left fun rid => ?_
      have mem : (1 : A ) ∈ (⊤ : TwoSidedIdeal A) := ⟨⟩
      rw [← rid, TwoSidedIdeal.mem_ker, map_one] at mem
      replace mem : (1 : K) = 0 := congr_fun congr($mem 1) ⟨0, by omega⟩
      exact one_ne_zero mem)
  haveI csa1 : IsCentralSimple F (AlgHom.range emb) := e |>.isCentralSimple
  haveI := csa1.2
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (finrank F (Fin n → K)) := by
    constructor
    have : 0 < finrank F (Fin n → K) := finrank_pos
    omega
  haveI : IsCentralSimple F (Matrix (Fin (finrank F (Fin n → K))) (Fin (finrank F (Fin n → K))) F) := by
    apply MatrixRing.isCentralSimple

  haveI : IsCentralSimple F (Module.End F (Fin n → K)) := by
    have f := algEquivMatrix (R := F) (M := Fin n → K) (finBasis _ _)
    refine f.symm.isCentralSimple
  haveI : IsCentralSimple F F :=
  { is_central := Subsingleton.le (Subalgebra.center _ _) ⊥
    is_simple := inferInstance }
  haveI : IsCentralSimple F B :=
  { is_central := by
      intro x hx
      rw [Algebra.mem_bot]
      rw [Subalgebra.mem_center_iff] at hx
      have hx' : ⟨x, by
          rw [← double_centralizer (B := emb.range)]
          intro y hy
          specialize hx ⟨y, hy⟩
          simpa [Subtype.ext_iff] using hx⟩ ∈ Subalgebra.center F emb.range := by
        rw [Subalgebra.mem_center_iff]
        rintro ⟨_, ⟨y, rfl⟩⟩
        rw [Subtype.ext_iff]
        exact x.2 (emb y) ⟨y, rfl⟩
      rw [IsCentralSimple.center_eq, Algebra.mem_bot] at hx'
      obtain ⟨r, hr⟩ := hx'
      simp only [Subtype.ext_iff, SubalgebraClass.coe_algebraMap] at hr
      use r
      rw [Subtype.ext_iff, ← hr]
      rfl
    is_simple := centralizer_isSimple _ (Module.Free.chooseBasis _ _) }
  refine ⟨⟨B⟩, ?_,
    { toFun := fun r =>
        ⟨{
          toFun := fun a => r • a
          map_add' := by simp
          map_smul' := by
            intro r v
            ext i
            simp only [Pi.smul_apply, smul_eq_mul, Algebra.mul_smul_comm, RingHom.id_apply]
        }, by
        rintro _ ⟨x, rfl⟩
        refine LinearMap.ext fun v => ?_
        simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          AlgHom.coe_restrictScalars', AlgHom.coe_coe, Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, LinearMap.mul_apply, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.coe_restrictScalars, map_smul, emb]⟩
      map_one' := by ext; simp only [one_smul, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_single, Function.comp_apply, OneMemClass.coe_one, LinearMap.one_apply]
      map_mul' := by intros; ext; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_single, Function.comp_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc,
        MulMemClass.coe_mul, LinearMap.mul_apply]
      map_zero' := by ext; simp only [zero_smul, LinearMap.coe_comp, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.coe_single, Function.comp_apply, Pi.zero_apply,
        ZeroMemClass.coe_zero, LinearMap.zero_comp, LinearMap.zero_apply]
      map_add' := by intros; ext; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_single, Function.comp_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        AddMemClass.coe_add, LinearMap.add_apply, Pi.add_apply]
      commutes' := by intros; ext; simp only [algebraMap_smul, LinearMap.coe_comp, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.coe_single, Function.comp_apply, Pi.smul_apply,
        SubalgebraClass.coe_algebraMap, Module.algebraMap_end_apply] }, ?_⟩
  · change Quotient.mk'' _ = Quotient.mk'' (CSA.mk F)
    have := writeAsTensorProduct (B := emb.range)
    have iso : A ⊗[F] B ≃ₐ[F] Matrix (Fin (finrank F (Fin n → K))) (Fin (finrank F (Fin n → K))) F :=
      AlgEquiv.symm <|
        AlgEquiv.trans (algEquivMatrix (R := F) (M := Fin n → K) (finBasis _ _)).symm
        (writeAsTensorProduct (B := emb.range) |>.trans <|
          Algebra.TensorProduct.congr e.symm AlgEquiv.refl)
    apply Quotient.sound'
    exact ⟨1, (finrank F (Fin n → K)), by omega,
      by have : 0 < finrank F (Fin n → K) := finrank_pos; omega, AlgEquiv.trans (dim_one_iso _) iso⟩
  · show finrank F K ^ 2 = finrank F B
    have dim_eq1 : finrank F B * _ = _ := dim_centralizer F emb.range
    rw [finrank_linearMap, show finrank F (Fin n → K) = finrank F K * finrank K (Fin n → K) from
      (finrank_mul_finrank F K (Fin n → K)).symm, finrank_fin_fun,
      show finrank F emb.range = finrank F A from e.symm.toLinearEquiv.finrank_eq,
      show finrank F K * n * (finrank F K * n) = (finrank F K)^2 * n ^ 2 by
        simp only [pow_two]; group] at dim_eq1
    have dim_eq2 := iso.toLinearEquiv.finrank_eq
    simp only [finrank_tensorProduct, finrank_self, _root_.one_mul, finrank_matrix,
      Fintype.card_fin] at dim_eq2
    rw [dim_eq2, ← pow_two] at dim_eq1
    let m := finrank F B
    let M := finrank F K
    haveI : Nontrivial B := ⟨0, 1, fun r => by
      simp only [zero_ne_one] at r⟩
    change m * n ^ 2 = M^2 * _ at dim_eq1
    change M^2 = m
    clear_value m M
    clear dim_eq2

    simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff] at dim_eq1
    exact dim_eq1 |>.resolve_right hn |>.symm

example : True := ⟨⟩

/--
theorem 3.3
-/
theorem isSplit_iff_dimension [FiniteDimensional F K] (A : CSA F) :
    isSplit F A K ↔
    ∃ (B : CSA F), (Quotient.mk'' A : BrGroup) = (Quotient.mk'' B) ∧
      ∃ (ι : K →ₐ[F] B), (finrank F K)^2 = finrank F B := by
  constructor
  · intro split
    obtain ⟨B, eq1, ι, eq2⟩ := exists_embedding_of_isSplit K F A split
    refine ⟨⟨B.1ᵐᵒᵖ⟩, ?_, {
      toFun := fun k => op <| ι k
      map_one' := by simp
      map_mul' := by intros; simp [← op_mul, ← map_mul, mul_comm]
      map_zero' := by simp
      map_add' := by intros; simp
      commutes' := by intros; simp
    }, eq2.trans ?_⟩
    · rw [show (Quotient.mk'' A : BrGroup) = (Quotient.mk'' B)⁻¹ by
        rwa [eq_inv_iff_mul_eq_one]]
      rfl
    · refine LinearEquiv.finrank_eq (opLinearEquiv F)
  · rintro ⟨B, eq, ⟨ι, dim_eq⟩⟩
    let n := finrank F K
    have n_pos : 0 < n := finrank_pos
    replace dim_eq : finrank F B = n^2 := dim_eq.symm
    letI : Module K B :=
    { smul := fun c a => a * ι c
      one_smul := by intros; show _ * _ = _; simp
      mul_smul := by intros; show _ * _ = (_ * _) * _; simp [_root_.mul_assoc, ← map_mul, mul_comm]
      smul_zero := by intros; show _ * _ = _; simp
      smul_add := by intros; show _ * _ = _ * _ + _ * _; simp [add_mul]
      add_smul := by intros; show _ * _ = _ * _ + _ * _; simp [mul_add]
      zero_smul := by intros; show _ * _ = _; simp }
    have smul_def (r : K) (a : B) : r • a = a * (ι r) := rfl
    haveI : SMulCommClass K F B :=
    { smul_comm := by
        intro a b c
        simp only [smul_def, Algebra.smul_mul_assoc] }
    haveI : IsScalarTower F K B :=
    { smul_assoc := by
        intro a b c
        simp only [smul_def, map_smul, Algebra.mul_smul_comm] }
    let μ : K →ₗ[F] B →ₗ[F] Module.End K B :=
    { toFun := fun c =>
      { toFun := fun a =>
        { toFun := fun a' => c • a • a'
          map_add' := by
            intro x y
            simp only [smul_eq_mul, mul_add, smul_def, add_mul]
          map_smul' := by
            intro r x
            simp only [smul_def, smul_eq_mul, _root_.mul_assoc, ← map_mul, mul_comm,
              RingHom.id_apply] }
        map_add' := by
          intros x y
          ext a'
          simp only [smul_eq_mul, add_mul, smul_def, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.add_apply]
        map_smul' := by
          intros r x
          ext a'
          simp only [smul_eq_mul, Algebra.smul_mul_assoc, smul_def, LinearMap.coe_mk, AddHom.coe_mk,
            RingHom.id_apply, LinearMap.smul_apply] }
      map_add' := by
        intros a a'
        ext
        simp only [op_add, smul_eq_mul, add_smul, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.add_apply]
      map_smul' := by
        intros a x
        ext r a'
        simp only [op_smul, smul_eq_mul, smul_assoc, LinearMap.coe_mk, AddHom.coe_mk,
          RingHom.id_apply, LinearMap.smul_apply] }

    let μ' : K ⊗[F] B →ₗ[F] Module.End K B := TensorProduct.lift μ
    let μ'' : K ⊗[F] B →ₗ[K] Module.End K B :=
    { __ := μ'
      map_smul' := by
        intro r a
        induction a using TensorProduct.induction_on with
        | zero => simp
        | tmul c a =>
          ext a'
          simp only [smul_eq_mul, smul_def, smul_tmul', AddHom.toFun_eq_coe, lift.tmul',
            LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply, μ', μ]
          rw [mul_comm r c, map_mul]
          simp only [_root_.mul_assoc]
        | add x y hx hy =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply] at hx hy
          simp only [smul_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add, hx, hy,
            RingHom.id_apply] }
    let μAlg : K ⊗[F] B →ₐ[K] Module.End K B := AlgHom.ofLinearMap μ''
      (by
        ext
        simp only [smul_eq_mul, Algebra.TensorProduct.one_def, LinearMap.coe_mk, lift.tmul',
          AddHom.coe_mk, one_smul, _root_.one_mul, LinearMap.one_apply, μ'', μ', μ])
      (by
        intro x y
        ext a''
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul c a =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | tmul c' a' =>
            simp only [smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm c c',
              LinearMap.coe_mk, lift.tmul', AddHom.coe_mk, mul_smul, _root_.mul_assoc,
              LinearMap.mul_apply, map_smul, μ'', μ', μ]
          | add m n hm hn =>
            simp only [mul_add, map_add, LinearMap.add_apply, hm, LinearMap.mul_apply, hn]
        | add m n hm hn =>
          simp only [add_mul, map_add, LinearMap.add_apply, hm, LinearMap.mul_apply, hn])
    haveI : FiniteDimensional K B := FiniteDimensional.right F K B
    let e : Module.End K B ≃ₐ[K] Matrix _ _ _ := algEquivMatrix (finBasis _ _)
    rw [split_sound' K F A B (Quotient.eq''.1 eq).some]
    refine ⟨finrank K B, fun r => by have := finrank_pos (R := K) (M := B); omega,
      ⟨AlgEquiv.trans (AlgEquiv.ofBijective μAlg ?_) e⟩⟩
    apply bijective_of_dim_eq_of_isCentralSimple
    rw [show finrank K (K ⊗[F] B) = n^2 by simp [dim_eq]]
    rw [show finrank K (Module.End K B) = n^2 by
      rw [finrank_linearMap]
      have eq : finrank F B = finrank F K * finrank K B := (finrank_mul_finrank F K B).symm
      change finrank F B = n * finrank K B at eq
      rw [dim_eq, pow_two] at eq
      replace eq : n = finrank K B := by
        set m := finrank K B
        have m_pos : 0 < m := finrank_pos
        clear_value n m
        simp only [mul_eq_mul_left_iff] at eq
        refine eq.resolve_right (by omega)
      simp only [← eq, pow_two]]

end CSA

section CSA2

@[simps!]
noncomputable abbrev toTensorMatrix_toFun_Flinear (A : Type u) (n : Type*) [Ring A] [Algebra F A]
    [DecidableEq n] [Fintype n] : K ⊗[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) :=
  TensorProduct.lift {
    toFun := fun k ↦ {
      toFun := fun M ↦ k • Algebra.TensorProduct.includeRight.mapMatrix M
      map_add' := fun M1 M2 ↦ by
        simp only ; rw [map_add, smul_add]
      map_smul' := fun a M ↦ by
        simp only [map_smul, AlgHom.mapMatrix_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
    map_add' := fun k1 k2 ↦ by
      ext : 1
      simp only [AlgHom.mapMatrix_apply, add_smul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.add_apply]
    map_smul' := fun a k ↦ by
      ext : 1
      simp only [AlgHom.mapMatrix_apply, smul_assoc, LinearMap.coe_mk, AddHom.coe_mk,
        RingHom.id_apply, LinearMap.smul_apply] }

noncomputable abbrev toTensorMatrix_toFun_Kliniear (A : Type u) (n : Type*) [Ring A] [Algebra F A]
    [DecidableEq n] [Fintype n] : K ⊗[F] Matrix n n A →ₗ[K] Matrix n n (K ⊗[F] A) where
  __ := toTensorMatrix_toFun_Flinear K F A n
  map_smul' := fun k1 koxM ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
    induction koxM using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul k M =>
      simp only [toTensorMatrix_toFun_Flinear, AlgHom.mapMatrix_apply, smul_tmul',
      smul_eq_mul, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← smul_eq_mul, smul_assoc]
    | add koxM1 koxM2 h1 h2 => simp only [smul_add, map_add, h1, h2]

noncomputable abbrev toTensorMatrix (A : Type u) (n : Type*) [Ring A] [Algebra F A]
    [DecidableEq n] [Fintype n] : K ⊗[F] Matrix n n A →ₐ[K] Matrix n n (K ⊗[F] A) where
  __ := toTensorMatrix_toFun_Kliniear K F A n
  map_one' := by
    simp only [Algebra.TensorProduct.one_def, AddHom.toFun_eq_coe, lift.tmul',
      AlgHom.mapMatrix_apply, LinearMap.coe_mk, AddHom.coe_mk, one_smul,
      Algebra.TensorProduct.includeRight_apply, tmul_zero, Matrix.map_one]
  map_mul' := fun koxM1 koxM2 ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction koxM1 using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero]
    | tmul k1 M1 =>
      induction koxM2 using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, lift.tmul, AlgHom.mapMatrix_apply,
        LinearMap.coe_mk,AddHom.coe_mk]
      | tmul k2 M2 =>
        simp only [toTensorMatrix_toFun_Flinear, Algebra.TensorProduct.tmul_mul_tmul]
        simp only [lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
          Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [_root_.map_mul, mul_comm, ← smul_eq_mul, smul_assoc]
      | add koxM1 koxM2 h1 h2 =>
        rw [mul_add, map_add, h1, h2, ← mul_add, ← map_add]
    | add koxM1 koxM2 h1 h2 =>
      rw [add_mul, map_add, h1, h2, ← add_mul, ← map_add]
  map_zero' := by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_zero]
  commutes' := fun k ↦ by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
      AddHom.toFun_eq_coe, lift.tmul', AlgHom.mapMatrix_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Algebra.TensorProduct.includeRight_apply, tmul_zero]
    ext i j
    simp only [Algebra.TensorProduct.includeRight_apply, tmul_zero, Matrix.smul_apply,
      Matrix.map_apply, Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.id.map_eq_id, RingHom.id_apply, TensorProduct.smul_tmul']
    simp_all only [smul_eq_mul, _root_.mul_one]
    split_ifs with h
    · subst h
      simp_all only [Matrix.one_apply_eq]
    · simp_all only [ne_eq, not_false_eq_true, Matrix.one_apply_ne, tmul_zero]

noncomputable abbrev invFun_toFun (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]
    (i : n) (j : n): K ⊗[F] A →ₗ[F] K ⊗[F] Matrix n n A :=
  TensorProduct.lift {
    toFun := fun k ↦ {
      toFun := fun a ↦ k ⊗ₜ Matrix.stdBasisMatrix i j a
      map_add' := fun a1 a2 ↦ by simp only [← TensorProduct.tmul_add, Matrix.stdBasisMatrix_add]
      map_smul' := fun r a ↦ by
        simp only [RingHom.id_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
          Matrix.smul_stdBasisMatrix]
    }
    map_add' := fun k1 k2 ↦ by
      ext a
      simp only [add_tmul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    map_smul' := fun r k ↦ by
      ext a
      simp only [← smul_tmul', LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
        LinearMap.smul_apply]
  }

noncomputable abbrev invFun_Klinear (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]
    (i : n) (j : n): K ⊗[F] A →ₗ[K] K ⊗[F] Matrix n n A where
  __ := invFun_toFun K F A n i j
  map_smul' := fun k koxa ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
    induction koxa using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul k a => simp only [smul_tmul', smul_eq_mul, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
    | add koxa1 koxa2 h1 h2 => simp only [smul_add, map_add, h1, h2]

noncomputable abbrev invFun_linearMap (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]:
    Matrix n n (K ⊗[F] A) →ₗ[K] K ⊗[F] Matrix n n A where
  toFun M := ∑ p : n × n, invFun_Klinear K F A n p.1 p.2 (M p.1 p.2)
  map_add' M1 M2 := by
    simp only [Matrix.add_apply, LinearMap.coe_mk, LinearMap.coe_toAddHom, map_add,
      Fintype.sum_prod_type, Finset.sum_add_distrib]
  map_smul' k M := by
    simp only [Matrix.smul_apply, map_smul, LinearMap.coe_mk, LinearMap.coe_toAddHom,
      Fintype.sum_prod_type, RingHom.id_apply, Finset.smul_sum]

lemma Martrix.one_eq_sum (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]:
    (1 : Matrix n n A) = ∑ i : n, ∑ j : n, Matrix.stdBasisMatrix i j (if i = j then 1 else 0) := by
  rw [Matrix.matrix_eq_sum_stdBasisMatrix (m := n) (n := n) 1]
  refine Finset.sum_congr rfl $ fun i _ => Finset.sum_congr rfl $ fun j _ => rfl

-- noncomputable abbrev invFun_algHom (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]:
--     Matrix n n (K ⊗[F] A) →ₐ[K] K ⊗[F] Matrix n n A :=
--   AlgHom.ofLinearMap (invFun_linearMap K F A n)
--   (by
--     simp only [LinearMap.coe_mk, invFun_toFun, LinearMap.coe_toAddHom, Fintype.sum_prod_type,
--       AddHom.coe_mk, Matrix.one_apply, Algebra.TensorProduct.one_def]
--     rw [Martrix.one_eq_sum F A n, TensorProduct.tmul_sum]
--     simp_rw [TensorProduct.tmul_sum]
--     refine Finset.sum_congr rfl $ fun i hi => Finset.sum_congr rfl $ fun j hj ↦ by
--       split_ifs with hij
--       · simp only [lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
--       · simp only [map_zero, Matrix.stdBasisMatrix_zero, tmul_zero]) sorry

lemma left_inv (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]
    (M : K ⊗[F] Matrix n n A) : invFun_linearMap K F A n (toTensorMatrix K F A n M) = M := by
  induction M using TensorProduct.induction_on with
  | zero => simp only [AlgHom.coe_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, map_zero, LinearMap.coe_mk, Fintype.sum_prod_type,
      AddHom.coe_mk, Matrix.zero_apply, Finset.sum_const_zero]
  | tmul k M =>
    simp only [AlgHom.coe_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, lift.tmul, AlgHom.mapMatrix_apply,
    LinearMap.coe_mk, AddHom.coe_mk, map_smul, Fintype.sum_prod_type, Matrix.map_apply,
    Algebra.TensorProduct.includeRight_apply, ← tmul_sum, smul_tmul', smul_eq_mul, _root_.mul_one]
    nth_rw 2 [Matrix.matrix_eq_sum_stdBasisMatrix M]
  | add koxa1 koxa2 h1 h2 =>
    rw [map_add, map_add, h1, h2]

lemma right_inv (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]
    (M : Matrix n n (K ⊗[F] A)) : toTensorMatrix K F A n (invFun_linearMap K F A n M) = M := by
  simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Fintype.sum_prod_type, AddHom.coe_mk,
    map_sum, AlgHom.coe_mk, AddHom.toFun_eq_coe, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [Matrix.matrix_eq_sum_stdBasisMatrix M]
  refine Finset.sum_congr rfl $ fun i _ => Finset.sum_congr rfl $ fun j _ => by
    induction M i j using TensorProduct.induction_on with
    | zero => simp only [map_zero, Matrix.stdBasisMatrix_zero]
    | tmul k a =>
      simp only [lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, AlgHom.mapMatrix_apply]
      ext i' j'
      simp only [Matrix.smul_apply, Matrix.map_apply, Algebra.TensorProduct.includeRight_apply,
        Matrix.stdBasisMatrix]
      split_ifs with hij
      · simp only [smul_tmul', smul_eq_mul, _root_.mul_one]
      · simp only [tmul_zero, smul_zero]
    | add koxa1 koxa2 h1 h2 =>
      rw [Matrix.stdBasisMatrix_add, map_add, map_add, h1, h2]

noncomputable def equivTensor' (A : Type u) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]:
    K ⊗[F] Matrix n n A ≃ Matrix n n (K ⊗[F] A) where
  toFun := toTensorMatrix K F A n
  invFun := invFun_linearMap K F A n
  left_inv := left_inv K F A n
  right_inv := right_inv K F A n

noncomputable def matrixTensorEquivTensor (A : Type u) (n : Type*) [Ring A] [Algebra F A]
    [DecidableEq n] [Fintype n] : K ⊗[F] Matrix n n A ≃ₐ[K] Matrix n n (K ⊗[F] A) :=
  {toTensorMatrix K F A n, equivTensor' K F A n with}

theorem isSplit_if_equiv (A B : CSA F) (hAB : IsBrauerEquivalent A B) (hA : isSplit F A K) :
    isSplit F B K := by
  obtain ⟨⟨n, m, hn, hm, iso⟩⟩ := hAB
  obtain ⟨p, ⟨hp, ⟨e⟩⟩⟩ := hA
  have ee := Algebra.TensorProduct.congr (A := K) (S := K) AlgEquiv.refl iso|>.symm.trans $
    matrixTensorEquivTensor K F A (Fin n)|>.trans $ e.mapMatrix (m := (Fin n))

  sorry

end CSA2

section DivisionRing

variable (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [IsCentralSimple F D]

theorem maxOfDivision (L : SubField F D): IsMaximalSubfield F D L ↔ isSplit F D L :=
  ⟨fun hL ↦ by
    rw [isSplit_iff_dimension L F ⟨D⟩]
    refine ⟨⟨D⟩, ⟨rfl, ⟨L.val, by rw [pow_two]; exact dim_max_subfield F D L hL|>.symm ⟩⟩⟩,
  fun hL ↦ by
    obtain ⟨B, ⟨hB1, ⟨(ι : L →ₐ[F] B), eq⟩⟩⟩ := isSplit_iff_dimension L F ⟨D⟩|>.1 hL
    simp only [Quotient.eq''] at hB1
    obtain ⟨⟨n, m, _, _, iso⟩⟩ := hB1
    simp only at iso

    sorry
  ⟩

end  DivisionRing
