import Mathlib.LinearAlgebra.PiTensorProduct
import BrauerGroup.Dual

suppress_compilation

open TensorProduct PiTensorProduct

variable {ι : Type*} (k K : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (V : ι → Type*) [Π i : ι, AddCommMonoid (V i)] [Π i : ι, Module k (V i)]

namespace PiTensorProduct

def extendScalars : (⨂[k] i, V i) →ₗ[k] ⨂[K] i, (K ⊗[k] V i) :=
  PiTensorProduct.lift
  { toFun := fun v => tprod _ fun i => 1 ⊗ₜ v i
    map_add' := by
      intro _ v i x y
      simp only
      have eq (j : ι) : (1 : K) ⊗ₜ Function.update v i x j =
        Function.update (fun i : ι => 1 ⊗ₜ v i) i (1 ⊗ₜ[k] x) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]; aesop
      simp_rw [eq]; clear eq
      have eq (j : ι) : (1 : K) ⊗ₜ Function.update v i y j =
        Function.update (fun i : ι => 1 ⊗ₜ v i) i (1 ⊗ₜ[k] y) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite]; aesop
      simp_rw [eq]; clear eq
      rw [← MultilinearMap.map_add]
      congr
      ext
      simp only [Function.update]
      split_ifs with h
      · subst h
        simp only [tmul_add]
      · rfl
    map_smul' := by
      intro _ v i a x
      simp only
      have eq (j : ι) : (1 : K) ⊗ₜ Function.update v i (a • x) j =
        Function.update (fun i : ι => 1 ⊗ₜ v i) i (algebraMap k K a • 1 ⊗ₜ[k] x) j := by
        simp only [Function.update, eq_rec_constant, dite_eq_ite, smul_ite]
        split_ifs with h
        · subst h; simp only [tmul_smul, algebraMap_smul]
        · rfl
      simp_rw [eq]; clear eq
      rw [MultilinearMap.map_smul]
      rw [algebraMap_smul]
      congr 2
      ext
      simp only [Function.update, eq_rec_constant, dite_eq_ite]
      aesop }

@[simp]
lemma extendScalars_tprod (x : Π i : ι, V i) :
    extendScalars k K V (tprod k x) =
    tprod K (1 ⊗ₜ x ·) := by
  simp only [extendScalars, lift.tprod, MultilinearMap.coe_mk]

end PiTensorProduct
