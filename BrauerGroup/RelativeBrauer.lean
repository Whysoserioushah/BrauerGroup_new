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
    refine ⟨⟨1, deg F F_bar A, by
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
          Module.finrank_matrix _ _ (Fin n) (Fin n)
        simp only [Module.finrank_tensorProduct, Module.finrank_self, _root_.one_mul,
          Fintype.card_fin, _root_.mul_one] at e1
        have := this.trans e1
        exact Nat.mul_self_inj.mp (id this.symm)
      exact iso'.trans e⟩⟩,
    fun hA ↦ by
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk''] at hA
      change _ = Quotient.mk'' _ at hA
      simp only [Quotient.eq'', one_in'] at hA
      change IsBrauerEquivalent _ _ at hA
      obtain ⟨⟨n, m, iso⟩⟩ := hA
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
      have D_findim := is_fin_dim_of_wdb K (K ⊗[F] A) p D iso'
      have := Wedderburn_Artin_uniqueness₀ K (Matrix (Fin (p * p * n)) (Fin (p * p * n)) D)
        (p * p * n) (p * m) D AlgEquiv.refl K e.symm
      exact ⟨p, hp, ⟨iso'.trans <| Wedderburn_Artin_uniqueness₀ K
        (Matrix (Fin (p * p * n)) (Fin (p * p * n)) D)
        (p * p * n) (p * m) D AlgEquiv.refl K e.symm |>.some.mapMatrix⟩⟩⟩

lemma mem_relativeBrGroup (A : CSA F) :
    Quotient.mk'' A ∈ RelativeBrGroup K F ↔
    isSplit F A K :=
  BrauerGroup.split_iff K F A |>.symm

lemma split_sound (A B : CSA F) (h0 : BrauerEquivalence A B) (h : isSplit F A K) :
    isSplit F B K := by
  rw [split_iff] at h ⊢
  rw [show (Quotient.mk'' B : BrGroup) = Quotient.mk'' A from Eq.symm <| Quotient.sound ⟨h0⟩, h]

lemma split_sound' (A B : CSA F) (h0 : BrauerEquivalence A B) :
    isSplit F A K ↔ isSplit F B K :=
  ⟨split_sound K F A B h0, split_sound K F B A
    ⟨h0.m, h0.n, h0.iso.symm⟩⟩

end Defs

namespace IsBrauerEquivalent

open BrauerGroup

variable (K : Type u) [Field K]

lemma exists_common_division_algebra (A B : CSA.{u, u} K) (h : IsBrauerEquivalent A B) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (m n : ℕ) (_ : NeZero m) (_ : NeZero n),
      Nonempty (A ≃ₐ[K] Matrix (Fin m) (Fin m) D) ∧
      Nonempty (B ≃ₐ[K] Matrix (Fin n) (Fin n) D) := by
  obtain ⟨n, hn, SA, _, _, ⟨isoA⟩⟩ := Wedderburn_Artin_algebra_version K A
  haveI : Algebra.IsCentral K (Matrix (Fin n) (Fin n) SA) := isoA.isCentral
  haveI : Algebra.IsCentral K SA := is_central_of_wdb _ _ _ _ isoA
  have : FiniteDimensional K (Matrix (Fin n) (Fin n) SA) :=
    Module.Finite.of_injective isoA.symm.toLinearMap isoA.symm.injective
  have : FiniteDimensional K SA :=  is_fin_dim_of_wdb _ _ _ _ isoA
  have eq1 : IsBrauerEquivalent ⟨SA⟩ A :=
    ⟨n, 1, AlgEquiv.symm <| AlgEquiv.trans (dim_one_iso A) isoA⟩
  obtain ⟨m, hm, SB, _, _, ⟨isoB⟩⟩ := Wedderburn_Artin_algebra_version K B
  haveI : Algebra.IsCentral K (Matrix (Fin m) (Fin m) SB) := isoB.isCentral
  haveI : Algebra.IsCentral K SB := is_central_of_wdb _ _ _ _ isoB
  have : FiniteDimensional K (Matrix (Fin m) (Fin m) SB) :=
    Module.Finite.of_injective isoB.symm.toLinearMap isoB.symm.injective
  have : FiniteDimensional K SB := is_fin_dim_of_wdb _ _ _ _ isoB

  have eq2 : IsBrauerEquivalent ⟨SA⟩ B :=
    .trans eq1 h

  obtain ⟨a, a', e⟩ := eq2
  haveI : FiniteDimensional K (Matrix (Fin a') (Fin a') B) :=
    LinearEquiv.finiteDimensional (matrixEquivTensor K B (Fin a')).toLinearEquiv.symm
  obtain ⟨isoAB⟩ := Wedderburn_Artin_uniqueness₀ K (Matrix (Fin a') (Fin a') B) a (a' * m)
    SA e.symm SB (by
    refine AlgEquiv.trans (AlgEquiv.trans ?_ (Matrix.compAlgEquiv _ _ _ _)) <|
      IsBrauerEquivalent.matrix_eqv' _ _ _
    refine AlgEquiv.mapMatrix ?_
    assumption)
  refine ⟨SA, inferInstance, inferInstance, n, m, inferInstance, inferInstance,
    ⟨⟨isoA⟩, ⟨isoB.trans <| AlgEquiv.mapMatrix isoAB.symm⟩⟩⟩

end IsBrauerEquivalent
