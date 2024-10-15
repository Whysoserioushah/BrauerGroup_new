import BrauerGroup.SplittingOfCSA
import BrauerGroup.«074E»

suppress_compilation

universe u

open TensorProduct BrauerGroup

section Defs

variable (K F F_bar: Type u) [Field K] [Field F] [Algebra F K] [Field F_bar] [Algebra F F_bar] [hk_bar : IsAlgClosure F F_bar]

abbrev RelativeBrGroup := MonoidHom.ker $ BrauerGroupHom.BaseChange (K := F) (E := K)

include F_bar in
lemma ele_of_relBrGroup : ∀(A : RelativeBrGroup K F),
    isSplit F (@Quotient.out (CSA F) (BrauerGroup.CSA_Setoid) A) K := fun A ↦ by
  use (deg F F_bar (@Quotient.out _ (BrauerGroup.CSA_Setoid) A))
  use (deg_pos F F_bar _)
  obtain ⟨A, hA⟩ := A
  induction A using Quotient.inductionOn
  refine ⟨?_⟩
  -- have : BrauerGroupHom.BaseChange (K := F) (E := K) A = 1 := by
  --   unfold RelativeBrGroup at A
  --   rw [← MonoidHom.mem_ker] ; exact SetLike.coe_mem A
  -- simp only [MonoidHom.coe_mk, OneHom.coe_mk] at this
  -- change _ = Quotient.mk'' _ at this
  -- have : IsBrauerEquivalent (K ⊗[K] (@Quotient.out _ (BrauerGroup.CSA_Setoid) A.1)) (CSA.mk K) := sorry
  -- simp? [BrauerGroup.one_in'] at this
  sorry

include F_bar in
lemma BrauerGroup.split_iff (A : CSA F) : isSplit F A K ↔
    BrauerGroupHom.BaseChange (K := F) (Quotient.mk'' A) = (1 : BrGroup (K := K)) :=
  ⟨fun hA ↦ by
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
      have := @Wedderburn_Artin_uniqueness₀ K (Matrix (Fin (p * p * n)) (Fin (p * p * n)) D) _ _
        _ (by sorry) (by sorry) (p * p * n) (p * m) ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp hp) hn⟩
        ⟨Nat.mul_ne_zero hp hm⟩ D _ _ AlgEquiv.refl K
        _ _ e.symm |>.some.mapMatrix (m := (Fin p))
      exact ⟨p, hp, ⟨iso'.trans this⟩⟩⟩

-- example (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] : FiniteDimensional K (Matrix (Fin 10) (Fin 10) A) :=
--   Module.Finite.of_basis (Matrix.stdBasis)

end Defs
