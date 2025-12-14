/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import BrauerGroup.BrauerGroup
import BrauerGroup.SplittingOfCSA
import BrauerGroup.ZeroSevenFourE

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
abbrev RelativeBrGroup := (BrauerGroupHom.BaseChange (K := F) (E := K)).ker

lemma BrauerGroup.split_iff (A : CSA F) : isSplit F A K ↔
    BrauerGroupHom.BaseChange (K := F) (Quotient.mk'' A) = (1 : BrauerGroup K) :=
  ⟨by
    rintro ⟨n, hn, ⟨iso⟩⟩
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk'']
    change _ = Quotient.mk'' _
    simp only [Quotient.eq'', one_in']
    exact ⟨1, n, one_ne_zero, hn.1, ⟨dim_one_iso (K ⊗[F] A) |>.trans iso⟩⟩,
    fun hA ↦ by
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.map'_mk''] at hA
      change _ = Quotient.mk'' _ at hA
      simp only [Quotient.eq'', one_in'] at hA
      change IsBrauerEquivalent _ _ at hA
      obtain ⟨n, m, hn, hm, ⟨iso⟩⟩ := hA
      let p : ℕ := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose
      let hp := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.1
      let D := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.2.choose
      letI := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.2.choose_spec.choose
      letI := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec.2.choose_spec
        |>.choose_spec.choose
      let iso' := Wedderburn_Artin_algebra_version K (K ⊗[F] A)|>.choose_spec
        |>.2.choose_spec.choose_spec.choose_spec.some
      change K ⊗[F] A ≃ₐ[K] Matrix (Fin p) (Fin p) D at iso'
      have e := Matrix.reindexAlgEquiv K _ (finProdFinEquiv.symm) |>.trans <|
        Matrix.compAlgEquiv _ _ _ _|>.symm.trans <|
        iso.mapMatrix (m := (Fin p))|>.symm.trans <|
        (Matrix.compAlgEquiv (Fin p) (Fin n) D K |>.trans <| Matrix.reindexAlgEquiv K D
        (Equiv.prodComm (Fin p) (Fin n))|>.trans <| Matrix.compAlgEquiv (Fin n) (Fin p) D K
        |>.symm.trans <| iso'.mapMatrix.symm).symm.mapMatrix |>.trans <|
        Matrix.compAlgEquiv (Fin p) (Fin p) _ K |>.trans <| Matrix.reindexAlgEquiv K _
        (finProdFinEquiv)|>.trans <| Matrix.compAlgEquiv _ _  D K|>.trans <|
        Matrix.reindexAlgEquiv K _ (finProdFinEquiv)
      have D_findim := is_fin_dim_of_wdb K (K ⊗[F] A) hp D iso'
      haveI : NeZero (p * p * n) := ⟨by simpa [hn]⟩
      haveI : NeZero (p * m) := ⟨by simpa [hm]⟩
      have := Wedderburn_Artin_uniqueness₀ K (Matrix (Fin (p * p * n)) (Fin (p * p * n)) D)
        (p * p * n) (p * m) D AlgEquiv.refl K e.symm
      exact ⟨p, ⟨hp⟩, ⟨iso'.trans <| Wedderburn_Artin_uniqueness₀ K
        (Matrix (Fin (p * p * n)) (Fin (p * p * n)) D)
        (p * p * n) (p * m) D .refl K e.symm |>.some.mapMatrix⟩⟩⟩

lemma mem_relativeBrGroup (A : CSA F) :
    Quotient.mk'' A ∈ RelativeBrGroup K F ↔
    isSplit F A K :=
  BrauerGroup.split_iff K F A |>.symm

lemma split_sound (A B : CSA F) (h0 : IsBrauerEquivalent A B) (h : isSplit F A K) :
    isSplit F B K := by
  rw [split_iff] at h ⊢
  rw [show (Quotient.mk'' B : BrauerGroup F) = Quotient.mk'' A from Eq.symm <| Quotient.sound h0, h]

lemma split_sound' (A B : CSA F) (h0 : IsBrauerEquivalent A B) :
    isSplit F A K ↔ isSplit F B K :=
  ⟨split_sound K F A B h0, split_sound K F B A <| h0.symm⟩

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
  haveI : Algebra.IsCentral K SA := is_central_of_wdb _ _ _ _ hn isoA
  have : FiniteDimensional K (Matrix (Fin n) (Fin n) SA) :=
    Module.Finite.of_injective isoA.symm.toLinearMap isoA.symm.injective
  have : FiniteDimensional K SA := is_fin_dim_of_wdb _ _ hn _ isoA
  have eq1 : IsBrauerEquivalent ⟨.of K SA⟩ A :=
    ⟨n, 1, hn, one_ne_zero, ⟨AlgEquiv.symm <| AlgEquiv.trans (dim_one_iso A) isoA⟩⟩
  obtain ⟨m, hm, SB, _, _, ⟨isoB⟩⟩ := Wedderburn_Artin_algebra_version K B
  haveI : Algebra.IsCentral K (Matrix (Fin m) (Fin m) SB) := isoB.isCentral
  haveI : Algebra.IsCentral K SB := is_central_of_wdb _ _ _ _ hm isoB
  have : FiniteDimensional K (Matrix (Fin m) (Fin m) SB) :=
    .of_injective isoB.symm.toLinearMap isoB.symm.injective
  have : FiniteDimensional K SB := is_fin_dim_of_wdb _ _ hm _ isoB

  have eq2 : IsBrauerEquivalent ⟨.of K SA⟩ B := .trans eq1 h

  obtain ⟨a, a', ha, ha', ⟨e⟩⟩ := eq2
  haveI : FiniteDimensional K (Matrix (Fin a') (Fin a') B) :=
    LinearEquiv.finiteDimensional (matrixEquivTensor (Fin a') K B).toLinearEquiv.symm
  haveI : NeZero a' := ⟨ha'⟩
  haveI : NeZero a := ⟨ha⟩
  have : NeZero m := ⟨hm⟩
  obtain ⟨isoAB⟩ := Wedderburn_Artin_uniqueness₀ K (Matrix (Fin a') (Fin a') B) a (a' * m)
    SA e.symm SB <|
      (AlgEquiv.mapMatrix ‹_›).trans <| (Matrix.compAlgEquiv _ _ _ _).trans <|
        IsBrauerEquivalent.matrix_eqv' _ _ _
  exact ⟨SA, inferInstance, inferInstance, n, m, ⟨hn⟩, ⟨hm⟩, ⟨isoA⟩,
    ⟨isoB.trans isoAB.symm.mapMatrix⟩⟩

end IsBrauerEquivalent
