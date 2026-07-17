module

public import BrauerGroup.Algebra.BrauerGroup.Relative.Basic
public import BrauerGroup.Algebra.CrossProduct.CentralSimple
public import BrauerGroup.Algebra.Split.Finrank

open groupCohomology BrauerGroup

universe w u v

namespace groupCohomology.IsMulCocycle₂

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (f : Gal(L/K) × Gal(L/K) → Lˣ) [hf : Fact <| IsMulCocycle₂ f]
  [Module.Finite K L] [IsGalois K L]

@[expose] public noncomputable def toRelBr :
    relativeBrGroup K L where
  val := .mk K <| CrossProductAlgebra f
  property := by
    rw [mk_mem_relativeBrGroup_iff_isSplit]
    exact Algebra.IsCentralSimple.split_of_finrank (CrossProductAlgebra.incl f)
      (by rw [CrossProductAlgebra.dim_eq_sq, pow_two])

@[simp] public lemma coe_toRelBr : (toRelBr K L f : BrauerGroup K) =
    BrauerGroup.mk K (CrossProductAlgebra f) := rfl

end groupCohomology.IsMulCocycle₂

namespace CrossProductAlgebra

open Module

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {f₁ f₂ : Gal(L/K) × Gal(L/K) → Lˣ} (β : Gal(L/K) → Lˣ)

/-- Rescaling the canonical basis by a family of units `β`, as an `L`-linear equivalence
between cross product algebras. This is an algebra isomorphism when the two cocycles differ
by the coboundary of `β`, see `CrossProductAlgebra.equivOfCoboundary`. -/
public noncomputable def unitsSMulEquiv : CrossProductAlgebra f₂ ≃ₗ[L] CrossProductAlgebra f₁ :=
  (basis (f := f₂)).equiv ((basis (f := f₁)).unitsSMul β) (Equiv.refl _)

@[simp]
public lemma unitsSMulEquiv_single (σ : Gal(L/K)) (c : L) :
    unitsSMulEquiv (f₁ := f₁) (f₂ := f₂) β (single f₂ σ c) = single f₁ σ (c * β σ) := by
  rw [single_eq_smul_basis, map_smul]
  simp only [unitsSMulEquiv, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply]
  ext : 1
  simp only [val_smul, Units.smul_def, basis_val, val_single, Finsupp.smul_single,
    smul_eq_mul, mul_one]

public lemma unitsSMulEquiv_map_one
    (hβ : ∀ σ τ, σ • β τ / β (σ * τ) * β σ = f₂ (σ, τ) / f₁ (σ, τ)) :
    unitsSMulEquiv (f₁ := f₁) β (1 : CrossProductAlgebra f₂) = 1 := by
  have h := hβ 1 1
  rw [one_smul, mul_one, div_self', one_mul] at h
  have h11 : f₂ (1, 1) = β 1 * f₁ (1, 1) := div_eq_iff_eq_mul.1 h.symm
  have hcoef : ((f₂ (1, 1))⁻¹ : Lˣ) * β 1 = (f₁ (1, 1))⁻¹ := by
    rw [h11, mul_inv_rev, inv_mul_cancel_right]
  have hc := congrArg Units.val hcoef
  simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hc
  rw [one_eq_single, unitsSMulEquiv_single]
  ext : 1
  rw [val_one]
  exact congrArg (Finsupp.single 1) hc

public lemma unitsSMulEquiv_map_mul [Fact <| IsMulCocycle₂ f₁] [Fact <| IsMulCocycle₂ f₂]
    (hβ : ∀ σ τ, σ • β τ / β (σ * τ) * β σ = f₂ (σ, τ) / f₁ (σ, τ))
    (x y : CrossProductAlgebra f₂) :
    unitsSMulEquiv (f₁ := f₁) β (x * y) = unitsSMulEquiv β x * unitsSMulEquiv β y := by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂]
  | single σ a =>
    induction y using induction_linear with
    | zero => simp
    | add y₁ y₂ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂]
    | single τ b =>
      have key : (f₂ (σ, τ) : L) * β (σ * τ) = σ (β τ) * β σ * f₁ (σ, τ) := by
        have h := congrArg Units.val (hβ σ τ)
        simp only [Units.val_mul, Units.val_div_eq_div_val, AlgEquiv.smul_units_def,
          Units.coe_map, MonoidHom.coe_coe] at h
        rw [div_mul_eq_mul_div, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _)] at h
        exact h.symm
      simp only [single_mul_single, unitsSMulEquiv_single]
      refine congrArg (single f₁ (σ * τ)) ?_
      rw [map_mul]
      linear_combination (a * σ b) * key

/-- Cocycles that differ by a coboundary have isomorphic cross product algebras: rescale
the canonical basis by the coboundary datum `β`. -/
public noncomputable def equivOfCoboundary [Fact <| IsMulCocycle₂ f₁] [Fact <| IsMulCocycle₂ f₂]
    (hβ : ∀ σ τ, σ • β τ / β (σ * τ) * β σ = f₂ (σ, τ) / f₁ (σ, τ)) :
    CrossProductAlgebra f₂ ≃ₐ[K] CrossProductAlgebra f₁ :=
  AlgEquiv.ofLinearEquiv ((unitsSMulEquiv β).restrictScalars K)
    (unitsSMulEquiv_map_one β hβ) (unitsSMulEquiv_map_mul β hβ)

end CrossProductAlgebra

namespace groupCohomology.IsMulCocycle₂

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {f₁ f₂ : Gal(L/K) × Gal(L/K) → Lˣ} [Fact <| IsMulCocycle₂ f₁] [Fact <| IsMulCocycle₂ f₂]
  [Module.Finite K L] [IsGalois K L]

/-- Cohomologous cocycles have the same class in the relative Brauer group: `toRelBr`
descends to `H²`. -/
public lemma toRelBr_eq_of_isMulCoboundary₂ (h : IsMulCoboundary₂ (f₂ / f₁)) :
    toRelBr K L f₁ = toRelBr K L f₂ := by
  obtain ⟨β, hβ⟩ := h
  exact Subtype.ext
    (BrauerGroup.mk_congr (CrossProductAlgebra.equivOfCoboundary β fun σ τ ↦ hβ σ τ)).symm

end groupCohomology.IsMulCocycle₂

/-- `H2π` is surjective: mathlib registers it as an epimorphism in `ModuleCat`. -/
public lemma groupCohomology.H2π_surjective {k G : Type w} [CommRing k] [Group G]
    (A : Rep k G) : Function.Surjective (H2π A) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

namespace BrauerGroup.relativeBrGroup

/- `Rep (k : Type u) (G : Type v)` is universe-polymorphic, but mathlib's group cohomology
is not yet: `GroupCohomology/LowDegree.lean` works under `variable {k G : Type u}` (one
universe for coefficients and group), so for `ℤ`-linear representations `cocycles₂`/`H2π`
only exist for groups in `Type 0`, and its `ofMulDistribMulAction` bridge section is stated
for `{G M : Type}` outright. Hence `K L : Type` below, exactly as in the `H¹` section of
mathlib's `Hilbert90.lean`.
TODO(mathlib): generalize the `groupCohomology` universes; the new `Rep` signature allows it. -/
variable (K L : Type) [Field K] [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

-- ## TODO : PR to mathlib to make this definition obselete
/-- A 2-cocycle of `Rep.ofAlgebraAutOnUnits K L`, viewed as a multiplicative cocycle datum
`Gal(L/K) × Gal(L/K) → Lˣ`. The type ascription resolves the defeq
`↥(Rep.ofAlgebraAutOnUnits K L) = Additive Lˣ` once and for all, so that typeclass search
downstream sees `Lˣ` syntactically. -/
public def cocycleFun (a : cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    Gal(L/K) × Gal(L/K) → Lˣ :=
  Additive.toMul ∘ (a.1 : Gal(L/K) × Gal(L/K) → Additive Lˣ)

/-- The Brauer class of the cross product algebra, at the level of mathlib's cocycle module
`cocycles₂ (Rep.ofAlgebraAutOnUnits K L)`. -/
public noncomputable def fromCocycles₂ (a : cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    relativeBrGroup K L :=
  haveI : Fact (IsMulCocycle₂ (cocycleFun K L a)) :=
    ⟨isMulCocycle₂_of_mem_cocycles₂ (G := Gal(L/K)) (M := Lˣ) a.1 a.2⟩
  IsMulCocycle₂.toRelBr K L (cocycleFun K L a)

/-- `fromCocycles₂` only depends on the cohomology class: the descent input for `fromH2`. -/
public lemma fromCocycles₂_eq_of_H2π_eq {a b : cocycles₂ (Rep.ofAlgebraAutOnUnits K L)}
    (h : H2π (Rep.ofAlgebraAutOnUnits K L) a = H2π (Rep.ofAlgebraAutOnUnits K L) b) :
    fromCocycles₂ K L a = fromCocycles₂ K L b := by
  haveI : Fact (IsMulCocycle₂ (cocycleFun K L a)) :=
    ⟨isMulCocycle₂_of_mem_cocycles₂ (G := Gal(L/K)) (M := Lˣ) a.1 a.2⟩
  haveI : Fact (IsMulCocycle₂ (cocycleFun K L b)) :=
    ⟨isMulCocycle₂_of_mem_cocycles₂ (G := Gal(L/K)) (M := Lˣ) b.1 b.2⟩
  rw [eq_comm, H2π_eq_iff] at h
  exact IsMulCocycle₂.toRelBr_eq_of_isMulCoboundary₂
    (isMulCoboundary₂_of_mem_coboundaries₂ (G := Gal(L/K)) (M := Lˣ) (b.1 - a.1) h)

/-- The crossed-product construction `H²(Gal(L/K), Lˣ) → Br(L/K)`, defined on `H2` itself.
It is characterized by `fromH2_H2π`; downstream proofs should only use that equation and
never unfold this definition. -/
public noncomputable def fromH2 (x : H2 (Rep.ofAlgebraAutOnUnits K L)) :
    relativeBrGroup K L :=
  fromCocycles₂ K L (Function.surjInv (groupCohomology.H2π_surjective _) x)

@[simp]
public lemma fromH2_H2π (a : cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    fromH2 K L (H2π (Rep.ofAlgebraAutOnUnits K L) a) = fromCocycles₂ K L a :=
  fromCocycles₂_eq_of_H2π_eq K L (Function.surjInv_eq (groupCohomology.H2π_surjective _) _)

end BrauerGroup.relativeBrGroup
