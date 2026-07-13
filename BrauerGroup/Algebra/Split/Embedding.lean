module

public import BrauerGroup.Algebra.Central.Matrix
public import BrauerGroup.Algebra.Split.Basic
public import BrauerGroup.LinearAlgebra.Matrix.Module
public import BrauerGroup.LinearAlgebra.Matrix.ToLin

/-!
# Splitting fields embed into a representative of the Brauer class

Scaffolding for `Algebra.IsSplit.exists_embedding`: given a division `K`-algebra `E` and a
splitting `e : L ⊗[K] E ≃ₐ[L] M_d(L)`, the column module `W := Fin d → L` carries commuting
actions of `L` (coordinatewise) and of `E` (through `e`), and counting `dim_K W` along the
two towers `K ⊆ L ⊆ End` and `K ⊆ E` gives `[L : K] = d · dim_E W`.

The `E`-module structure depends on the choice of `e`, so it is installed with `letI` at
each use site (never as an instance), following the `rightMod` pattern in
`BrauerGroup.Algebra.Split.Finrank`.
-/

@[expose] public section

universe u

open scoped TensorProduct
open Matrix.Module

namespace Algebra.IsSplit

variable {K L E : Type u} [Field K] [Field L] [Algebra K L] [DivisionRing E] [Algebra K E]
  {d : ℕ} (e : L ⊗[K] E ≃ₐ[L] Matrix (Fin d) (Fin d) L)

/-- The action of `E` on the column module `Fin d → L` through the splitting `e` and the
matrix action on columns. -/
private abbrev colMod : Module E (Fin d → L) :=
  Module.compHom _ (e.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := E)).toRingHom)

private lemma colMod_smul_def (x : E) (v : Fin d → L) :
    letI := colMod e; (x • v : Fin d → L) = e (1 ⊗ₜ[K] x) • v := rfl

private lemma colMod_isScalarTower :
    letI := colMod e; IsScalarTower K E (Fin d → L) := by
  letI := colMod e
  refine .of_algebraMap_smul fun k v ↦ ?_
  rw [colMod_smul_def, show (1 : L) ⊗ₜ[K] algebraMap K E k
      = algebraMap L (L ⊗[K] E) (algebraMap K L k) by
    rw [← Algebra.TensorProduct.includeRight_apply, AlgHom.commutes,
      IsScalarTower.algebraMap_apply K L (L ⊗[K] E)], e.commutes]
  ext i
  simp [Matrix.algebraMap_matrix_apply, Algebra.smul_def]

private lemma colMod_smulCommClass :
    letI := colMod e; SMulCommClass L E (Fin d → L) := by
  letI := colMod e
  refine ⟨fun l x v ↦ ?_⟩
  rw [colMod_smul_def, colMod_smul_def]
  ext i
  simp [Finset.mul_sum, mul_left_comm]

private lemma colMod_smulCommClass' :
    letI := colMod e; SMulCommClass E K (Fin d → L) := by
  letI := colMod e
  haveI := colMod_smulCommClass e
  refine ⟨fun x k v ↦ ?_⟩
  rw [← algebraMap_smul L k v, ← algebraMap_smul L k (x • v)]
  exact (smul_comm _ _ _).symm

include e in
private lemma finrank_of_split [FiniteDimensional K E] : Module.finrank K E = d * d := by
  rw [← Module.finrank_baseChange (S := K) (R := L) (M' := E), e.toLinearEquiv.finrank_eq]
  simp [Module.finrank_matrix]

/-- The dimension count: `[L : K] = d · dim_E W` for the column module `W`. In particular
the degree `d` of `E` divides `[L : K]`. -/
private lemma finrank_eq_mul [FiniteDimensional K L] [FiniteDimensional K E] (hd : d ≠ 0) :
    letI := colMod e
    Module.finrank K L = d * Module.finrank E (Fin d → L) := by
  letI := colMod e
  haveI := colMod_isScalarTower e
  have h1 : Module.finrank K L * d = Module.finrank K (Fin d → L) := by
    rw [← Module.finrank_mul_finrank K L (Fin d → L)]
    congr 1
    simp
  have h2 : Module.finrank K (Fin d → L)
      = d * d * Module.finrank E (Fin d → L) := by
    rw [← finrank_of_split e, Module.finrank_mul_finrank K E (Fin d → L)]
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) ?_
  rw [h1, h2]
  ring

include e in
/-- Steps 5–6: the endomorphism algebra `B := End_E W` of the column module is a central
simple `K`-algebra in the class of `Eᵐᵒᵖ`, of dimension `[L : K]²`, receiving `L` by
scalar multiplication. -/
private lemma exists_embedding_aux [FiniteDimensional K L] [FiniteDimensional K E]
    [Algebra.IsCentral K E] (hd : d ≠ 0) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra K B) (_ : FiniteDimensional K B)
      (_ : IsSimpleRing B) (_ : Algebra.IsCentral K B) (_ : L →ₐ[K] B),
      BrauerGroup.mk K B = (BrauerGroup.mk K E)⁻¹ ∧
      Module.finrank K B = Module.finrank K L ^ 2 := by
  letI := colMod e
  haveI := colMod_isScalarTower e
  haveI := colMod_smulCommClass e
  haveI := colMod_smulCommClass' e
  haveI : Module.Finite E (Fin d → L) := Module.Finite.right K E (Fin d → L)
  haveI : Module.Finite K Eᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv K)
  have hm : Module.finrank E (Fin d → L) ≠ 0 := fun h ↦ by
    have hn := finrank_eq_mul e hd
    rw [h, mul_zero] at hn
    exact (Module.finrank_pos (R := K) (M := L)).ne' hn
  haveI : Nonempty (Fin (Module.finrank E (Fin d → L))) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  let φ := (Module.finBasis E (Fin d → L)).endAlgEquivMatrixOpposite K
  haveI : IsSimpleRing (Module.End E (Fin d → L)) :=
    .of_ringEquiv φ.symm.toRingEquiv inferInstance
  haveI : Algebra.IsCentral K (Module.End E (Fin d → L)) :=
    .of_algEquiv K _ _ φ.symm
  haveI : Module.Finite K (Module.End E (Fin d → L)) :=
    Module.Finite.equiv φ.symm.toLinearEquiv
  refine ⟨Module.End E (Fin d → L), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance,
    { toFun l :=
        { toFun v := l • v
          map_add' v w := smul_add l v w
          map_smul' x v := smul_comm l x v }
      map_one' := LinearMap.ext fun v ↦ one_smul L v
      map_mul' l l' := LinearMap.ext fun v ↦ mul_smul l l' v
      map_zero' := LinearMap.ext fun v ↦ zero_smul L v
      map_add' l l' := LinearMap.ext fun v ↦ add_smul l l' v
      commutes' k := LinearMap.ext fun v ↦ algebraMap_smul L k v }, ?_, ?_⟩
  · rw [BrauerGroup.mk_inv, BrauerGroup.mk_congr φ, BrauerGroup.mk_eq_mk]
    exact ⟨1, Module.finrank E (Fin d → L), one_ne_zero, hm,
      ⟨by convert! Matrix.uniqueAlgEquiv (m := Fin 1) (R := K)⟩⟩
  · rw [φ.toLinearEquiv.finrank_eq, finrank_eq_mul e hd]
    have hE : Module.finrank K Eᵐᵒᵖ = d * d :=
      (MulOpposite.opLinearEquiv (R := K) (M := E)).symm.finrank_eq.trans (finrank_of_split e)
    simp only [Module.finrank_matrix, Fintype.card_fin, hE]
    ring

/-- **Every finite splitting field embeds into a representative of the Brauer class**: if a
finite extension `L/K` splits the central simple algebra `A`, then the class of `A` has a
representative `B` of dimension `[L : K]²` receiving a `K`-algebra embedding of `L`. This is
the converse of `Algebra.IsCentralSimple.split_of_finrank`. -/
theorem exists_embedding {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
    [IsSimpleRing A] [Algebra.IsCentral K A] [FiniteDimensional K L]
    (hs : Algebra.IsSplit K A L) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra K B) (_ : FiniteDimensional K B)
      (_ : IsSimpleRing B) (_ : Algebra.IsCentral K B) (_ : L →ₐ[K] B),
      BrauerGroup.mk K B = BrauerGroup.mk K A ∧
      Module.finrank K B = Module.finrank K L ^ 2 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, _, _, _, ⟨eD⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  haveI : Algebra.IsCentral K D := .of_matrix (h := .of_algEquiv K _ _ eD)
  have hAD : BrauerGroup.mk K A = BrauerGroup.mk K D := by
    rw [BrauerGroup.mk_congr eD, BrauerGroup.mk_eq_mk]
    exact ⟨1, n, one_ne_zero, hn.out, ⟨by convert! Matrix.uniqueAlgEquiv (m := Fin 1) (R := K)⟩⟩
  haveI : Module.Finite K Dᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv K)
  obtain ⟨d, hd, ⟨iso⟩⟩ := ((isSplit_congr K A D L hAD).1 hs).op
  obtain ⟨B, _, _, _, _, _, ιB, hB1, hB2⟩ := exists_embedding_aux iso hd
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ιB, ?_, hB2⟩
  rw [hB1, ← BrauerGroup.mk_inv, inv_inv]
  exact hAD.symm

end Algebra.IsSplit
