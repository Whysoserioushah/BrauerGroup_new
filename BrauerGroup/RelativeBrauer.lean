/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/

import BrauerGroup.SplittingOfCSA
import BrauerGroup.«074E»
import Mathlib.RingTheory.MatrixAlgebra
import BrauerGroup.Subfield.Subfield

/-!
# Relative Brauer Group

# Main results

* `BrauerGroup.split_iff`: Let `A` be a CSA over F, then `⟦A⟧ ∈ Br(K/F)` if and only if K splits A
* `isSplit_iff_dimension`: Let `A` be a CSA over F, then `⟦A⟧ ∈ Br(K/F)` if and only if there exists
  another `F`-CSA `B` such that `⟦A⟧ = ⟦B⟧` (i.e. `A` and `B` are Brauer-equivalent) and `K ⊆ B` and
  `dim_F B = (dim_F K)²`
-/

suppress_compilation

universe u

open TensorProduct BrauerGroup

section Defs

variable (K F : Type u) [Field K] [Field F] [Algebra F K] -- [FiniteDimensional F K]

/--
The relative Brauer group `Br(K/F)` is the kernel of the map `Br F -> Br K`
-/
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
    isSplit F B K := by
  rw [split_iff] at h ⊢
  rw [show (Quotient.mk'' B : BrGroup) = Quotient.mk'' A from Eq.symm <| Quotient.sound ⟨h0⟩, h]

lemma split_sound' (A B : CSA F) (h0 : BrauerEquivalence A B) :
    isSplit F A K ↔ isSplit F B K :=
  ⟨split_sound K F A B h0, split_sound K F B A
    ⟨h0.m, h0.n, h0.hm, h0.hn, h0.iso.symm⟩⟩

end Defs
