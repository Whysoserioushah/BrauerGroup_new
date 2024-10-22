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

open FiniteDimensional MulOpposite
example [FiniteDimensional F K] (A : CSA F) :
    isSplit F A K ↔
    ∃ (B : CSA F), (Quotient.mk'' A : BrGroup) = (Quotient.mk'' B) ∧
      ∃ (ι : K →ₐ[F] A), (finrank F K)^2 = finrank F A := by
  constructor
  · sorry
  · rintro ⟨B, eq, ⟨ι, dim_eq⟩⟩
    let n := finrank F K
    have n_pos : 0 < n := finrank_pos
    replace dim_eq : finrank F A = n^2 := dim_eq.symm
    letI : Module K A :=
    { smul := fun c a => a * ι c
      one_smul := by intros; show _ * _ = _; simp
      mul_smul := by intros; show _ * _ = (_ * _) * _; simp [_root_.mul_assoc, ← map_mul, mul_comm]
      smul_zero := by intros; show _ * _ = _; simp
      smul_add := by intros; show _ * _ = _ * _ + _ * _; simp [add_mul]
      add_smul := by intros; show _ * _ = _ * _ + _ * _; simp [mul_add]
      zero_smul := by intros; show _ * _ = _; simp }
    have smul_def (r : K) (a : A) : r • a = a * (ι r) := rfl
    haveI : SMulCommClass K F A :=
    { smul_comm := by
        intro a b c
        simp only [smul_def, Algebra.smul_mul_assoc] }
    haveI : IsScalarTower F K A :=
    { smul_assoc := by
        intro a b c
        simp only [smul_def, map_smul, Algebra.mul_smul_comm] }
    let μ : K →ₗ[F] A →ₗ[F] Module.End K A :=
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

    let μ' : K ⊗[F] A →ₗ[F] Module.End K A := TensorProduct.lift μ
    let μ'' : K ⊗[F] A →ₗ[K] Module.End K A :=
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
    let μAlg : K ⊗[F] A →ₐ[K] Module.End K A := AlgHom.ofLinearMap μ''
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
    haveI : FiniteDimensional K A := FiniteDimensional.right F K A
    let B := finBasis K A
    let e : Module.End K A ≃ₐ[K] Matrix _ _ _ := algEquivMatrix B
    refine ⟨finrank K A, fun r => by have := finrank_pos (R := K) (M := A); omega,
      ⟨AlgEquiv.trans (AlgEquiv.ofBijective μAlg ?_) e⟩⟩
    apply bijective_of_dim_eq_of_isCentralSimple
    rw [show finrank K (K ⊗[F] A) = n^2 by simp [dim_eq]]
    rw [show finrank K (Module.End K A.carrier) = n^2 by
      rw [finrank_linearMap]
      have eq : finrank F A = finrank F K * finrank K A := (finrank_mul_finrank F K A).symm
      change finrank F A = n * finrank K A at eq
      rw [dim_eq, pow_two] at eq
      replace eq : n = finrank K A := by
        set m := finrank K A
        have m_pos : 0 < m := finrank_pos
        clear_value n m
        simp only [mul_eq_mul_left_iff] at eq
        refine eq.resolve_right (by omega)
      simp only [← eq, pow_two]]


end Defs
