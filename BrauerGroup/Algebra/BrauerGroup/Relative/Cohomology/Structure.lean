module

public import BrauerGroup.Algebra.BrauerGroup.Relative.Cohomology.FactorSet

@[expose] public section

universe u v w

namespace BrauerGroup

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  {x : BrauerGroup K} (A : GoodRep L x)

/-- The left `L`-module structure on a `GoodRep` through `ι`: `c • a = ι c * a`.
Deliberately NOT an instance — for concrete carriers (e.g. a crossed product) it
disagrees with their native `L`-action. Attach with `attribute [local instance]`. -/
@[instance_reducible]
noncomputable def GoodRep.lmodule : Module L A.carrier :=
  Module.compHom A.carrier A.ι.toRingHom

attribute [local instance] GoodRep.lmodule

lemma GoodRep.lsmul_def (c : L) (a : A.carrier) : c • a = A.ι c * a := rfl

/-- `K` acts through `L`. Local-instance companion to `lmodule`. -/
theorem GoodRep.lmoduleTower : IsScalarTower K L A.carrier :=
  ⟨fun k c a ↦ by simp only [lsmul_def, Algebra.smul_def, map_mul, AlgHom.commutes, mul_assoc]⟩

attribute [local instance] GoodRep.lmoduleTower

/-- Finiteness over `L`, descended from finiteness over `K`. -/
theorem GoodRep.lmoduleFinite : Module.Finite L A.carrier :=
  Module.Finite.of_restrictScalars_finite K L A.carrier

attribute [local instance] GoodRep.lmoduleFinite

lemma GoodRep.finrank_ι [Module.Finite K L] :
    Module.finrank L A.carrier = Module.finrank K L := by
  have h := Module.finrank_mul_finrank K L A.carrier
  rw [A.dim_eq_sq, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

/-- Dedekind coefficient lemma: if a conjugation factor at `σ` is an `L`-combination of
conjugation factors at other automorphisms with independent values, the coefficients
intertwine the automorphisms: `σ d * c τ = c τ * τ d`. -/
lemma GoodRep.conjFactor_coeff (b : (τ : Gal(L/K)) → conjFactor A τ) {σ : Gal(L/K)}
    {J : Set Gal(L/K)} (hJ : LinearIndepOn L (fun τ ↦ (b τ : A.carrier)) J)
    {c : Gal(L/K) →₀ L} (hc : c ∈ Finsupp.supported L L J)
    (hu : Finsupp.linearCombination L (fun τ ↦ (b τ : A.carrier)) c = (b σ : A.carrier))
    (τ : Gal(L/K)) (d : L) : σ d * c τ = c τ * τ d := by
  set c₂ : Gal(L/K) →₀ L := Finsupp.onFinset c.support (fun τ ↦ c τ * τ d)
    (fun τ h ↦ Finsupp.mem_support_iff.2 fun h0 ↦ h (by simp [h0]))
  have h1 : Finsupp.linearCombination L (fun τ ↦ (b τ : A.carrier)) (σ d • c)
    = A.ι (σ d) * (b σ : A.carrier) := by
    rw [map_smul, hu, lsmul_def]     -- linearity, then the 4.7a spec
  have h2 : Finsupp.linearCombination L (fun τ ↦ (b τ : A.carrier)) c₂
    = (b σ : A.carrier) * A.ι d := by
    rw [← hu, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.onFinset_sum _ (by simp), Finsupp.sum_mul, Finsupp.sum]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    rw [lsmul_def, map_mul, mul_assoc, ← mem_conjFactor _ _ (b ρ) d, ← mul_assoc, ← lsmul_def]
  have h0 : σ d • c - c₂ ∈ Finsupp.supported L L J :=
    sub_mem (Submodule.smul_mem _ _ hc) (fun ρ hρ ↦ hc (by simp_all [c₂]))
  have := linearIndepOn_iff.1 hJ _ h0 (by rw [map_sub, h1, h2, mem_conjFactor, sub_self])
  simpa [c₂, sub_eq_zero] using congr($this τ)

theorem GoodRep.linearIndependent_conjFactor (b : (σ : Gal(L/K)) → conjFactor A σ) :
    LinearIndependent L fun σ ↦ (b σ : A.carrier) := by
  obtain ⟨J, hJ, hmax⟩ := exists_maximal_linearIndepOn L (fun σ ↦ (b σ : A.carrier))
  rw [← linearIndepOn_univ_iff]
  suffices h : J = Set.univ from h ▸ hJ
  rw [Set.eq_univ_iff_forall]
  intro σ
  by_contra hσ
  -- maximality: a • u_σ ∈ span, a ≠ 0; scale by a⁻¹ (L is a field)
  obtain ⟨a, ha, hmem⟩ := hmax σ hσ
  have hmem' : (b σ : A.carrier) ∈ Submodule.span L ((fun τ ↦ (b τ : A.carrier)) '' J) := by
    simpa [smul_smul, inv_mul_cancel₀ ha] using Submodule.smul_mem _ a⁻¹ hmem
  -- Finsupp representation
  obtain ⟨c, hc, hu⟩ := (Finsupp.mem_span_image_iff_linearCombination L).1 hmem'
  -- some coefficient is nonzero: u_σ is a unit in a nontrivial ring
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (b σ).1.ne_zero (by simpa using hu.symm)
  obtain ⟨τ, hτ⟩ := Finsupp.support_nonempty_iff.2 hc0
  -- Dedekind identity + cancellation ⟹ σ = τ
  have hστ : σ = τ := AlgEquiv.ext fun d ↦ mul_right_cancel₀ (Finsupp.mem_support_iff.1 hτ)
    ((A.conjFactor_coeff b hJ hc hu τ d).trans (mul_comm _ _))
  exact hσ (hστ ▸ hc hτ)

/-- The conjugation factors of a family `b` form an `L`-basis of a `GoodRep`:
`A = ⊕_σ L·u_σ`. -/
noncomputable def GoodRep.conjFactorBasis [Module.Finite K L] [IsGalois K L]
    (b : (σ : Gal(L/K)) → conjFactor A σ) : Module.Basis Gal(L/K) L A.carrier :=
  basisOfLinearIndependentOfCardEqFinrank (A.linearIndependent_conjFactor b)
    (by rw [A.finrank_ι, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card])

@[simp] lemma GoodRep.conjFactorBasis_apply [Module.Finite K L] [IsGalois K L]
    (b : (σ : Gal(L/K)) → conjFactor A σ) (σ : Gal(L/K)) :
    conjFactorBasis A b σ = (b σ : A.carrier) :=
  congr($(coe_basisOfLinearIndependentOfCardEqFinrank (A.linearIndependent_conjFactor b) _) σ)

variable [Module.Finite K L] [IsGalois K L]

/-- The `L`-linear comparison between the crossed product of the factor set of `b` and the
`GoodRep` itself, matching the canonical basis to the conjugation factors. -/
noncomputable def GoodRep.compareEquiv (b : (σ : Gal(L/K)) → conjFactor A σ) :
    CrossProductAlgebra (factorSet A b) ≃ₗ[L] A.carrier :=
  CrossProductAlgebra.basis.equiv (A.conjFactorBasis b) (Equiv.refl _)

@[simp] lemma GoodRep.compareEquiv_basis (b : (σ : Gal(L/K)) → conjFactor A σ)
    (σ : Gal(L/K)) :
    A.compareEquiv b (CrossProductAlgebra.basis σ) = (b σ : A.carrier) := by
  simp [compareEquiv, Module.Basis.equiv_apply]

@[simp] lemma GoodRep.compareEquiv_single (b : (σ : Gal(L/K)) → conjFactor A σ)
    (σ : Gal(L/K)) (c : L) :
    A.compareEquiv b (CrossProductAlgebra.single (factorSet A b) σ c)
      = A.ι c * (b σ : A.carrier) := by
  rw [CrossProductAlgebra.single_eq_smul_basis, map_smul, compareEquiv_basis, lsmul_def]

open groupCohomology

instance (b : (σ : Gal(L/K)) → conjFactor A σ) : Fact (IsMulCocycle₂ (factorSet A b)) :=
  ⟨isMulCocycle₂_factorSet A b⟩

omit [Module.Finite K L] [IsGalois K L] in
lemma GoodRep.conjFactor_one_val (b : (σ : Gal(L/K)) → conjFactor A σ) :
    (b 1 : A.carrier) = A.ι (factorSet A b (1, 1)) := by
  have h := factorSet_spec A b 1 1
  rw [mul_one] at h        -- fixes the index: b (1 * 1) → b 1
  exact ((Units.mul_left_inj _).1 h.symm).symm  -- cancel the right unit; adjust symm's to taste

open CrossProductAlgebra
/-- The structure theorem: a `GoodRep` is the crossed product of its factor set. -/
noncomputable def GoodRep.compareAlgEquiv (b : (σ : Gal(L/K)) → conjFactor A σ) :
    CrossProductAlgebra (factorSet A b) ≃ₐ[K] A.carrier :=
  .ofLinearEquiv ((A.compareEquiv b).restrictScalars K) (by
    simp [CrossProductAlgebra.one_eq_single, conjFactor_one_val, ← map_mul]) (fun x y ↦ by
    induction x using induction_linear with
    | zero => simp
    | add x' y' h1 h2 => rw [add_mul, map_add, h1, h2, ← add_mul, ← map_add]
    | single σ c =>
    induction y using induction_linear with
    | zero => simp
    | add x y h1 h2 => rw [mul_add, map_add, h1, h2, ← mul_add, ← map_add]
    | single τ d =>
      simp only [single_mul_single, LinearEquiv.restrictScalars_apply, compareEquiv_single, map_mul,
        AlgEquiv.mul_apply]
      rw [← mul_assoc, mul_assoc (A.ι c) (b σ : A.carrier), mem_conjFactor _ _  (b σ) d,
        mul_assoc, ← factorSet_spec]
      simp [mul_assoc])

theorem GoodRep.mk_crossProduct_factorSet (b : (σ : Gal(L/K)) → conjFactor A σ) :
    BrauerGroup.mk K (CrossProductAlgebra (factorSet A b)) = x :=
  (BrauerGroup.mk_congr (A.compareAlgEquiv b)).trans A.quot_eq

lemma _root_.CrossProductAlgebra.mk_congr_cocycle {f g : Gal(L/K) × Gal(L/K) → Lˣ}
    [Fact <| IsMulCocycle₂ f] [Fact <| IsMulCocycle₂ g] (h : f = g) :
    BrauerGroup.mk K (CrossProductAlgebra f) = BrauerGroup.mk K (CrossProductAlgebra g) := by
  subst h; rfl

theorem exists_mk_cyclicAlgebra_eq {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsGalois K L]
    (σ : Gal(L/K)) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    {x : BrauerGroup K} (hx : x ∈ relativeBrGroup K L) :
    ∃ a : Kˣ, BrauerGroup.mk K (CyclicAlgebra σ hσ a) = x := by
  obtain ⟨A⟩ := GoodRep.nonempty x hx
  obtain ⟨u⟩ := (inferInstance : Nonempty (conjFactor A σ))
  exact ⟨powScalar σ hσ A u,
    (CrossProductAlgebra.mk_congr_cocycle (factorSet_powFamily σ hσ A u)).symm.trans
      (A.mk_crossProduct_factorSet (powFamily σ hσ A u))⟩

end BrauerGroup
