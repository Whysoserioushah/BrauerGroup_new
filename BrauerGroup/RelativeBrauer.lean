import BrauerGroup.SplittingOfCSA
import BrauerGroup.«074E»
import Mathlib.RingTheory.MatrixAlgebra
import BrauerGroup.Subfield.Subfield

suppress_compilation

universe u

open TensorProduct BrauerGroup

section Defs

variable (K F : Type u) [Field K] [Field F] [Algebra F K] -- [FiniteDimensional F K]

abbrev RelativeBrGroup := MonoidHom.ker $ BrauerGroupHom.BaseChange (K := F) (E := K)

lemma BrauerGroup.split_iff (A : CSA F) : isSplit F A K ↔
    BrauerGroupHom.BaseChange (K := F) (Quotient.mk'' A) = (1 : BrGroup (K := K)) :=
  ⟨fun hA ↦ by
    let F_bar := AlgebraicClosure F
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk'']
    change _ = Quotient.mk'' _
    simp only [Quotient.eq'', one_in']
    change IsBrauerEquivalent _ _
    refine ⟨⟨1, deg F F_bar A, one_ne_zero, deg_pos F F_bar A, by
      simp only
      refine dim_one_iso (K ⊗[F] A) |>.trans ?_
      set n : ℕ := hA.choose with n_eq
      have iso' := hA.choose_spec.2.some
      rw [n_eq.symm] at iso'
      have e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin (deg F F_bar A))
          (Fin (deg F F_bar A)) K := by
        suffices n = deg F F_bar A from Matrix.reindexAlgEquiv K _ (finCongr this)
        have := deg_sq_eq_dim F F_bar A
        rw [pow_two] at this
        have e1 := LinearEquiv.finrank_eq iso'.toLinearEquiv|>.trans $
          FiniteDimensional.finrank_matrix _ (Fin n) (Fin n)
        simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self,
          _root_.one_mul, Fintype.card_fin] at e1
        have := this.trans e1
        exact Nat.mul_self_inj.mp (id this.symm)
      exact iso'.trans e⟩⟩,
    fun hA ↦ by
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk''] at hA
      change _ = Quotient.mk'' _ at hA
      simp only [Quotient.eq'', one_in'] at hA
      change IsBrauerEquivalent _ _ at hA
      obtain ⟨⟨n, m, hn, hm, iso⟩⟩ := hA
      simp only at iso
      let p : ℕ := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose
      let hp := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.1
      let D := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.2.choose
      letI := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.2.choose_spec.choose
      letI := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.2.choose_spec
        |>.choose_spec.choose
      let iso' := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec
        |>.2.choose_spec.choose_spec.choose_spec.some
      change K ⊗[F] A ≃ₐ[K] Matrix (Fin p) (Fin p) D at iso'
      have e := Matrix.reindexAlgEquiv K _ (finProdFinEquiv.symm) |>.trans $
        Matrix.compAlgEquiv _ _ _ _|>.symm.trans $
        iso.mapMatrix (m := (Fin p))|>.symm.trans $
        (Matrix.compAlgEquiv (Fin p) (Fin n) D K |>.trans $ Matrix.reindexAlgEquiv K D
        (Equiv.prodComm (Fin p) (Fin n))|>.trans $ Matrix.compAlgEquiv (Fin n) (Fin p) D K
        |>.symm.trans $ iso'.mapMatrix.symm).symm.mapMatrix |>.trans $
        Matrix.compAlgEquiv (Fin p) (Fin p) _ K |>.trans $ Matrix.reindexAlgEquiv K _
        (finProdFinEquiv)|>.trans $ Matrix.compAlgEquiv _ _  D K|>.trans $
        Matrix.reindexAlgEquiv K _ (finProdFinEquiv)
      have D_findim := is_fin_dim_of_wdb K (K ⊗[F] A) p D (Nat.zero_lt_of_ne_zero hp) iso'
      letI : NeZero (p * p * n) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp hp) hn⟩
      have := @Wedderburn_Artin_uniqueness₀ K (Matrix (Fin (p * p * n)) (Fin (p * p * n)) D) _ _
        _ _ (by
          suffices FiniteDimensional K (D ⊗[K] Matrix (Fin (p * p * n)) (Fin (p * p * n)) K) from
            LinearEquiv.finiteDimensional $ matrixEquivTensor K D (Fin (p * p * n))|>.symm.toLinearEquiv
          exact Module.Finite.tensorProduct _ _ _) (p * p * n) (p * m) _
        ⟨Nat.mul_ne_zero hp hm⟩ D _ _ AlgEquiv.refl K
        _ _ e.symm |>.some.mapMatrix (m := (Fin p))
      exact ⟨p, hp, ⟨iso'.trans this⟩⟩⟩

lemma mem_relativeBrGroup (A : CSA F) :
    Quotient.mk'' A ∈ RelativeBrGroup K F ↔
    isSplit F A K :=
  BrauerGroup.split_iff K F A |>.symm
-- lemma ele_of_relBrGroup : ∀ A ∈ RelativeBrGroup K F,
--     isSplit F (@Quotient.out (CSA F) (BrauerGroup.CSA_Setoid) A) K := fun A hA ↦ by
--   let F_bar := AlgebraicClosure F
--   rw [BrauerGroup.split_iff K F F_bar]
--   change _ = 1 at hA
--   rw [← hA]
--   simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk'']
--   have := Quotient.out_eq' A
--   conv_rhs => rw [← this]
--   erw [Quotient.map'_mk'']
--   rfl
lemma split_sound (A B : CSA F) (h0 : BrauerEquivalence A B) (h : isSplit F A K) :
    isSplit F B K := sorry

lemma split_sound' (A B : CSA F) (h0 : BrauerEquivalence A B) :
    isSplit F A K ↔ isSplit F B K :=
  ⟨split_sound K F A B h0, split_sound K F B A
    ⟨h0.m, h0.n, h0.hm, h0.hn, h0.iso.symm⟩⟩

open FiniteDimensional MulOpposite

-- set_option synthInstance.maxHeartbeats 128 in
-- set_option trace.Meta.synthPending true in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 40000 in
set_option maxSynthPendingDepth 2 in
lemma exists_embedding_of_isSplit [FiniteDimensional F K] (A : CSA F) (split : isSplit F A K) :
    ∃ (B : CSA F), (Quotient.mk'' A : BrGroup) * (Quotient.mk'' B) = 1 ∧
      ∃ (ι : K →ₐ[F] B), (finrank F K)^2 = finrank F B := by
  have mem : Quotient.mk'' A ∈ RelativeBrGroup K F := by
    rw [BrauerGroup.split_iff] at split
    exact split
  obtain ⟨n, hn, ⟨iso⟩⟩ := split
  let iso' := iso.trans (algEquivMatrix' (R := K) (n := Fin n)).symm
  have := algEquivMatrix' (R := K) (n := Fin n)
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
  haveI : IsSimpleOrder (TwoSidedIdeal <| AlgHom.range emb) := csa1.2
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (finrank F (Fin n → K)) := by
    constructor
    have : 0 < finrank F (Fin n → K) := finrank_pos
    omega
  haveI : IsCentralSimple F (Matrix (Fin (finrank F (Fin n → K))) (Fin (finrank F (Fin n → K))) F) := by
    apply MatrixRing.isCentralSimple

  haveI : IsCentralSimple F (Module.End F (Fin n → K)) := by
    have := algEquivMatrix (R := F) (M := Fin n → K) (finBasis _ _)
    refine this.symm.isCentralSimple
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
  · change Quotient.mk'' (CSA.mk <| A ⊗[F] B) = Quotient.mk'' (CSA.mk F)
    have iso1 : _ ≃ₐ[F] _ ⊗[F] B := writeAsTensorProduct emb.range
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
    haveI : Nontrivial B := sorry
    have : 0 < m := finrank_pos
    have : 0 < M := finrank_pos
    have : 0 < M^2 := by positivity
    have : 0 < n := by positivity
    change m * n ^ 2 = M^2 * _ at dim_eq1
    change M^2 = m
    clear_value m M
    clear dim_eq2

    simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff] at dim_eq1
    exact dim_eq1 |>.resolve_right hn |>.symm

example : true := ⟨⟩

example [FiniteDimensional F K] (A : CSA F) :
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
        | add x y hx hy => sorry }
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
          | add m n hm hn => sorry
        | add m n hm hn => sorry)
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


end Defs
