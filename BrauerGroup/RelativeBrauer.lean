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

lemma ele_of_relBrGroup : ∀ A ∈ RelativeBrGroup K F,
    isSplit F (@Quotient.out (CSA F) (BrauerGroup.CSA_Setoid) A) K := fun A hA ↦ by
  rw [BrauerGroup.split_iff K F _]
  change _ = 1 at hA
  rw [← hA]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk'']
  have := Quotient.out_eq' A
  conv_rhs => rw [← this]
  erw [Quotient.map'_mk'']
  rfl

open FiniteDimensional MulOpposite
example (A : CSA F) :
    isSplit F A K ↔
    ∃ (B : CSA F), (Quotient.mk'' A : BrGroup) = (Quotient.mk'' B) ∧
      ∃ (ι : K →ₐ[F] A), (finrank F K)^2 = finrank F A := by
  constructor
  · sorry
  · rintro ⟨B, eq, ⟨ι, dim_eq⟩⟩
    letI : Module Kᵐᵒᵖ A := Module.compHom A (ι.toRingHom.fromOpposite fun x y => by
      change _ = _
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← map_mul, mul_comm])

    haveI : SMulCommClass Kᵐᵒᵖ F A :=
    { smul_comm := by
        intro a b c
        change ι a.unop • b • c = b • ι a.unop • c
        simp only [smul_eq_mul, Algebra.mul_smul_comm] }
    haveI : IsScalarTower F Kᵐᵒᵖ A :=
    { smul_assoc := by
        intro a b c
        change ι (a • b).unop • c = a • ι b.unop • c
        simp only [MulOpposite.unop_smul, map_smul, smul_eq_mul, Algebra.smul_mul_assoc] }
    let μ : K →ₗ[F] A →ₗ[F] Module.End Kᵐᵒᵖ A :=
    { toFun := fun c =>
      { toFun := fun a =>
        { toFun := fun a' => (op c) • a' • a
          map_add' := by
            intro x y
            simp only [smul_eq_mul, add_mul, smul_add]
          map_smul' := by
            intro r x
            simp only [smul_eq_mul, RingHom.id_apply]
            change ι c * (ι r.unop • x * _) = ι r.unop * (ι c * _)
            simp only [smul_eq_mul, ← _root_.mul_assoc, ← map_mul, mul_comm] }
        map_add' := by
          intros x y
          ext a'
          simp only [smul_eq_mul, mul_add, smul_add, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.add_apply]
        map_smul' := by
          intros r x
          ext a'
          simp only [smul_eq_mul, Algebra.mul_smul_comm, LinearMap.coe_mk, AddHom.coe_mk,
            RingHom.id_apply, LinearMap.smul_apply]
          change ι c * _ = r • (ι c * _)
          simp only [Algebra.mul_smul_comm] }
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

    let μ' : K ⊗[F] A →ₗ[F] Module.End Kᵐᵒᵖ A := TensorProduct.lift μ
    let μ'' : K ⊗[F] A →ₗ[Kᵐᵒᵖ] Module.End Kᵐᵒᵖ A :=
    { __ := μ'
      map_smul' := by
        intro r a

        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply, Algebra.smul_def]
        rw [show r • a = r.unop • a by
          rw [Algebra.smul_def]
          simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
          induction a using TensorProduct.induction_on with
          | zero => simp only [smul_zero, mul_zero]
          | tmul c a =>
            simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
            rw [smul_tmul']
            congr 1
            simp only [smul_eq_mul_unop, mul_comm]
          | add x y hx hy =>
            simp only [smul_add, hx, hy, mul_add]
            ]
        induction a using TensorProduct.induction_on with
        | zero => simp
        | tmul c a =>
          ext a'
          simp only [smul_eq_mul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
            Algebra.id.map_eq_id, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul,
            _root_.one_mul, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, op_mul, op_unop,
            LinearMap.mul_apply, map_smul, Module.algebraMap_end_apply, μ', μ]
          change ι (op c * r).unop • _ = ι c • (ι r.unop * _)
          simp only [unop_mul, unop_op, map_mul, smul_eq_mul, ← _root_.mul_assoc, ← map_mul]
          rw [_root_.mul_comm r.unop c]
        | add x y hx hy =>
        simp only [smul_add, map_add, hx, hy, mul_add]
         }
    haveI : FiniteDimensional Kᵐᵒᵖ A := sorry
    let B := finBasis Kᵐᵒᵖ A
    let e : Module.End Kᵐᵒᵖ A ≃ₐ[Kᵐᵒᵖ] Matrix _ _ _ := algEquivMatrix B
    use finrank Kᵐᵒᵖ A
    sorry

end Defs
