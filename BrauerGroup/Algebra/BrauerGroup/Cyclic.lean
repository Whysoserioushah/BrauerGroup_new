module

public import BrauerGroup.Algebra.BrauerGroup.Relative.Cohomology.FactorSet
public import BrauerGroup.Algebra.BrauerGroup.Relative.Cohomology.Maps
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
    (by simp) <| fun x y ↦ by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂]
  | single σ c =>
    induction y using induction_linear with
    | zero => simp
    | add y₁ y₂ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂]
    | single τ d => ext; simp [-Finsupp.single_mul, mul_assoc]

@[simp]
lemma oneToEnd_single (σ : Gal(L/K)) (c : L) :
    oneToEnd K L (single (1 : Gal(L/K) × Gal(L/K) → Lˣ) σ c) = c • σ.toLinearMap := by
  simp [oneToEnd]

@[simp]
lemma oneToEnd_of (σ : Gal(L/K)) :
    oneToEnd K L (of (1 : Gal(L/K) × Gal(L/K) → Lˣ) σ : CrossProductAlgebra _)
      = σ.toLinearMap :=
  (oneToEnd_single σ 1).trans (one_smul L σ.toLinearMap)

@[simp]
lemma oneToEnd_incl (c : L) :
    oneToEnd K L (incl (1 : Gal(L/K) × Gal(L/K) → Lˣ) c) = c • (1 : Module.End K L) := by
  have h : incl (1 : Gal(L/K) × Gal(L/K) → Lˣ) c = single 1 1 c := by
    ext : 1
    simp [incl_apply]
  rw [h, oneToEnd_single]
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

open groupCohomology BrauerGroup CrossProductAlgebra

/-- A cyclic algebra is split iff its parameter is a norm:
`[(L/K, σ, a)] = 1 ↔ a ∈ N(Lˣ)`. -/
theorem CyclicAlgebra.mk_eq_one_iff [IsGalois K L] [Module.Finite K L]
    (σ : Gal(L/K)) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (a : Kˣ) :
    BrauerGroup.mk K (CyclicAlgebra σ hσ a) = 1 ↔
      ∃ c : Lˣ, Units.map (Algebra.norm K (S := L)) c = a := by
  rw [← isMulCoboundary₂_cyclicCocycle_iff σ hσ a]
  constructor
  · intro hsplit
    have h1 : BrauerGroup.mk K (CrossProductAlgebra (1 : Gal(L/K) × Gal(L/K) → Lˣ))
        = BrauerGroup.mk K (CyclicAlgebra σ hσ a) :=
      BrauerGroup.mk_one_eq_one.trans hsplit.symm
    have hcob := isMulCoboundary₂_factorSet_div'
      (GoodRep.ofCrossProduct 1 h1) (GoodRep.ofCrossProduct (cyclicCocycle σ hσ a) rfl)
      (ofFamily 1 h1) (ofFamily (cyclicCocycle σ hσ a) rfl)
    simpa [factorSet_ofFamily] using hcob
  · rintro ⟨β, hβ⟩
    refine (BrauerGroup.mk_congr (equivOfCoboundary β fun g h ↦ ?_)).trans
      BrauerGroup.mk_one_eq_one
    simpa using hβ g h

