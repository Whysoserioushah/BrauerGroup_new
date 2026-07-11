module

public import Mathlib
public import BrauerGroup.Algebra.BrauerGroup.Basic

@[expose] public section

namespace BrauerGroup

universe u u₂ u₃

open scoped TensorProduct

section MatrixBaseChange

/- The matrix/base-change helpers do not involve the Brauer group, so their two field
universes are fully independent (no `max u u₂` tower needed). -/
variable (K : Type u) (L : Type u₂) [Field K] [Field L] [Algebra K L]

/-- `matrixEquivTensor` upgraded to be linear over an intermediate field `L`: for a ring `C`
that is both a `K`-algebra and an `L`-algebra compatibly, the isomorphism
`Matrix n n C ≃ C ⊗[K] Matrix n n K` is in fact `L`-linear. -/
def matrixEquivTensorL (K : Type u) (L : Type u₂) [CommRing K] [CommRing L] [Algebra K L]
    (n : Type*) [Fintype n] [DecidableEq n]
    (C : Type*) [Ring C] [Algebra K C] [Algebra L C] [IsScalarTower K L C] :
    Matrix n n C ≃ₐ[L] C ⊗[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n K C).toRingEquiv) fun l => by
    change matrixEquivTensor n K C (algebraMap L (Matrix n n C) l)
       = algebraMap L (C ⊗[K] Matrix n n K) l
    have key : (matrixEquivTensor n K C).symm (algebraMap L C l ⊗ₜ[K] (1 : Matrix n n K))
        = algebraMap L (Matrix n n C) l := by
      rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
        Algebra.algebraMap_eq_smul_one (R := L) (A := Matrix n n C) l,
        IsScalarTower.algebraMap_smul C l (1 : Matrix n n C)]
    rw [Algebra.TensorProduct.algebraMap_apply, ← key, AlgEquiv.apply_symm_apply]

/-- Base change commutes with matrix algebras: `Matrix n n (L ⊗[K] A) ≃ₐ[L] L ⊗[K] Matrix n n A`. -/
def matrixBaseChange (K : Type u) (L : Type u₂) [CommRing K] [CommRing L] [Algebra K L]
    (n : Type*) [Fintype n] [DecidableEq n] (A : Type*) [Ring A] [Algebra K A] :
    Matrix n n (L ⊗[K] A) ≃ₐ[L] L ⊗[K] Matrix n n A :=
  (matrixEquivTensorL K L n (L ⊗[K] A)).trans <|
    (Algebra.TensorProduct.assoc K K L L A (Matrix n n K)).trans <|
      Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor n K A).symm

end MatrixBaseChange

variable (K : Type u) (L : Type (max u u₂)) [Field K] [Field L] [Algebra K L]

open Algebra.TensorProduct in
def baseChange : BrauerGroup K →* BrauerGroup L where
  toFun := BrauerGroup.map (k := K) L fun A B h ↦ by
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
    simp only [IsBrauerEquivalent]
    refine ⟨n, m, hn, hm, ⟨?_⟩⟩
    exact (matrixBaseChange K L (Fin n) A).trans <|
      (congr AlgEquiv.refl e).trans <| (matrixBaseChange K L (Fin m) B).symm
  map_one' := by
    rw [← mk_self_eq_one, ← mk_self_eq_one, map_mk]
    exact mk_congr (Algebra.TensorProduct.rid _ _ _)
  map_mul' x y := by
    induction x using BrauerGroup.induction with | h A =>
    induction y using BrauerGroup.induction with | h B =>
    rw [map_mk, map_mk, mk_mul_mk, mk_mul_mk, map_mk]
    refine mk_congr <| ((Algebra.TensorProduct.assoc K K L L A B).symm.trans
      (congr (Algebra.TensorProduct.rid L L (L ⊗[K] A)).symm AlgEquiv.refl)).trans
      (Algebra.TensorProduct.assoc K L L (L ⊗[K] A) L B)

@[simp]
lemma baseChange_mk (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A]
    [IsSimpleRing A] [Algebra.IsCentral K A] :
    baseChange K L (BrauerGroup.mk K A) = BrauerGroup.mk L (L ⊗[K] A) := rfl

lemma baseChange_self : baseChange K K = .id (BrauerGroup K) := by
  ext x
  induction x using BrauerGroup.induction with | h A =>
  simp only [baseChange_mk, MonoidHom.id_apply]
  exact mk_congr <| (Algebra.TensorProduct.lid ..)

@[simp]
lemma baseChange_self_apply (x : BrauerGroup K) :
    baseChange K K x = x := by
  simp [baseChange_self]

lemma baseChange_comp (M : Type (max u u₂ u₃)) [Field M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (baseChange L M).comp (baseChange K L) = baseChange.{u, max u₂ u₃} K M := by
  ext x
  induction x using BrauerGroup.induction with | h A =>
  simp only [MonoidHom.comp_apply, baseChange_mk]
  exact mk_congr <| (Algebra.TensorProduct.assoc K L M M L A).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M) AlgEquiv.refl)

end BrauerGroup
