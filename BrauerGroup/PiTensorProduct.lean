import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.Algebra.Algebra.Basic

suppress_compilation

open TensorProduct PiTensorProduct

variable {ι : Type*} (k K : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (V : ι → Type*) [Π i : ι, AddCommMonoid (V i)] [Π i : ι, Module k (V i)]
variable (W : ι → Type*) [Π i : ι, AddCommMonoid (W i)] [Π i : ι, Module k (W i)]

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

/--
pure tensor of pure tensor
-/
lemma span_simple_tensor_eq_top [Fintype ι] :
    Submodule.span k { x | ∃ (v : Π i : ι,  V i) (w : Π i : ι, W i),
      x = tprod k (fun i => v i ⊗ₜ[k] w i) } = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    have H (i : ι) : v i ∈ (⊤ : Submodule k _) := ⟨⟩
    simp_rw [← span_tmul_eq_top, mem_span_set] at H
    choose cᵢ hcᵢ eqᵢ using H
    choose vij wij hij using hcᵢ
    have eq : v = fun i => ∑ j ∈ (cᵢ i).support.attach, (cᵢ i j) • (vij i j.2 ⊗ₜ[k] wij i j.2) := by
      ext i
      -- rw [← eqᵢ]
      simp only [← eqᵢ, Finsupp.sum]
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hij]
    rw [eq, (tprod k).map_sum_finset]
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ $ Submodule.subset_span
      ⟨fun i => cᵢ i (s i) • vij i (s i).2, fun i => wij i (s i).2, rfl⟩
  | add => aesop

end PiTensorProduct
