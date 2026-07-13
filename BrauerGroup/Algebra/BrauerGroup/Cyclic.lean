module

public import BrauerGroup.Algebra.BrauerGroup.Basic
public import BrauerGroup.Algebra.CrossProduct.CentralSimple
public import BrauerGroup.RingTheory.SimpleRing.Basic
public import BrauerGroup.RingTheory.SimpleRing.End
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

universe u v w

open groupCohomology CategoryTheory CrossProductAlgebra

section one

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

instance : Fact (IsMulCocycle₂ (1 : Gal(L/K) × Gal(L/K) → Lˣ)) :=
  ⟨fun g h j ↦ by simp⟩

variable (K L) in
noncomputable def oneToEnd :
    CrossProductAlgebra (1 : Gal(L/K) × Gal(L/K) → Lˣ) →ₐ[K] Module.End K L :=
  .ofLinearMap ((Finsupp.lsum K fun σ ↦
        (LinearMap.toSpanSingleton L (Module.End K L) σ.toLinearMap).restrictScalars K)
      ∘ₗ (valLinearEquiv (R := K)).toLinearMap)
    (by simp) <| fun σ τ ↦ by
  simp only [LinearMap.coe_comp, Finsupp.coe_lsum, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, Function.comp_apply, valLinearEquiv_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.toFun_as_coe, EquivLike.coe_coe, valAddEquiv_apply, val_mul]
  induction σ.val using Finsupp.induction_linear with
  | zero => simp
  | add f g h1 h2 =>
    classical rw [map_add, LinearMap.add_apply, Finsupp.sum_add_index (by simp)
      (by simp [add_smul]), h1, h2, ← add_mul, ← Finsupp.sum_add_index
      (by simp) (by simp [add_smul])]
  | single σ r1 =>
    induction τ.val using Finsupp.induction_linear with
    | zero => simp
    | add f g h1 h2 =>
      classical rw [map_add, Finsupp.sum_add_index (by simp)
        (by simp [add_smul]), h1, h2, ← mul_add, ← Finsupp.sum_add_index
        (by simp) (by simp [add_smul])]
    | single τ r2 => ext; simp [-Finsupp.single_mul, mul_assoc]

@[simp]
lemma oneToEnd_mk_single (σ : Gal(L/K)) (c : L) :
    oneToEnd K L ⟨.single σ c⟩ = c • σ.toLinearMap := by
  simp [oneToEnd]

@[simp]
lemma oneToEnd_of (σ : Gal(L/K)) :
    oneToEnd K L (of (1 : Gal(L/K) × Gal(L/K) → Lˣ) σ : CrossProductAlgebra _)
      = σ.toLinearMap :=
  (oneToEnd_mk_single σ 1).trans (one_smul L σ.toLinearMap)

@[simp]
lemma oneToEnd_incl (c : L) :
    oneToEnd K L (incl (1 : Gal(L/K) × Gal(L/K) → Lˣ) c) = c • (1 : Module.End K L) := by
  have h : incl (1 : Gal(L/K) × Gal(L/K) → Lˣ) c = ⟨.single 1 c⟩ := by
    ext : 1
    simp [incl_apply]
  rw [h, oneToEnd_mk_single]
  rfl

variable (K L) in
noncomputable def oneEquivEnd [IsGalois K L] [Module.Finite K L] :
    CrossProductAlgebra (1 : Gal(L/K) × Gal(L/K) → Lˣ) ≃ₐ[K] Module.End K L :=
  .ofBijective (oneToEnd K L) <| (oneToEnd K L).bijective_of_finrank_eq <| by
    rw [dim_eq_sq, Module.finrank_linearMap, sq]

variable [IsGalois K L] [Module.Finite K L]

@[simp]
lemma oneEquivEnd_apply (x : CrossProductAlgebra (1 : Gal(L/K) × Gal(L/K) → Lˣ)) :
    oneEquivEnd K L x = oneToEnd K L x := rfl

@[simp]
lemma oneEquivEnd_symm_toLinearMap (σ : Gal(L/K)) :
    (oneEquivEnd K L).symm σ.toLinearMap
      = (of (1 : Gal(L/K) × Gal(L/K) → Lˣ) σ : CrossProductAlgebra _) := by
  rw [AlgEquiv.symm_apply_eq]
  simp

@[simp]
lemma oneEquivEnd_symm_smul_one (c : L) :
    (oneEquivEnd K L).symm (c • (1 : Module.End K L))
      = incl (1 : Gal(L/K) × Gal(L/K) → Lˣ) c := by
  rw [AlgEquiv.symm_apply_eq]
  simp

end one

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem BrauerGroup.mk_one_eq_one [IsGalois K L] [Module.Finite K L] :
    BrauerGroup.mk K (CrossProductAlgebra (1 : Gal(L/K) × Gal(L/K) → Lˣ)) = 1 := by
  haveI : Nonempty (Fin (Module.finrank K L)) := ⟨⟨0, Module.finrank_pos⟩⟩
  rw [BrauerGroup.mk_congr (oneEquivEnd K L),
    BrauerGroup.mk_congr (algEquivMatrix (Module.finBasis K L)),
    BrauerGroup.mk_matrix_eq_one]

