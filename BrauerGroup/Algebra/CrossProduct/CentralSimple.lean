module

public import BrauerGroup.Algebra.CrossProduct.Basic
public import BrauerGroup.RingTheory.Congruence.Basic
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# The cross product algebra of a 2-cocycle is central simple

For a 2-cocycle `f` of a finite Galois field extension `K / F`, this file endows the cross
product algebra `CrossProductAlgebra f` with its `F`-algebra structure and shows that it is a
central simple `F`-algebra of dimension `dim(K / F) ^ 2`.

## References

* [*Advanced Algebra*]
-/

@[expose] public section

open groupCohomology Function Module

suppress_compilation

variable {R F K : Type*} [Field F] [Field K] [Algebra F K] {f : Gal(K/F) × Gal(K/F) → Kˣ}

namespace CrossProductAlgebra

variable [Fact <| IsMulCocycle₂ f]

instance monoid : Monoid (CrossProductAlgebra f) where
  one_mul := by
    rintro ⟨x⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a => simp [map_one_fst_of_isMulCocycle₂ Fact.out σ, mul_right_comm _ a]
  mul_one := by
    rintro ⟨x⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a => simp [map_one_snd_of_isMulCocycle₂ Fact.out σ]
  mul_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single σ a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single τ b =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add => simp [-mulLinearMap_single_single, *]
    | single ν c =>
    simp only [mulLinearMap_single_single, mul_assoc, AlgEquiv.mul_apply, map_mul,
      mul_left_comm _ (σ (τ c))]
    congr 4
    simpa [mul_comm] using congr(($((Fact.out : IsMulCocycle₂ f) σ τ ν)).val)

instance : Ring (CrossProductAlgebra f) where
  __ := addCommGroup
  __ := monoid
  left_distrib := by intros; ext; simp
  right_distrib := by intros; ext; simp
  zero_mul := by intros; ext; simp
  mul_zero := by intros; ext; simp
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp

instance algebra [CommSemiring R] [Algebra R F] [Module R K] [IsScalarTower R F K] :
    Algebra R (CrossProductAlgebra f) := by
  refine .ofModule ?_ ?_ <;> intros <;> ext <;> simp

lemma algebraMap_val [CommSemiring R] [Algebra R F] [Algebra R K] [IsScalarTower R F K] (r : R) :
    (algebraMap R (CrossProductAlgebra f) r).val = .single 1 (algebraMap R K r * (f (1, 1))⁻¹) := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [val_smul, val_one, Finsupp.smul_single,
    Units.val_inv_eq_inv_val, ← Algebra.smul_def]

variable (f) in
/-- The inclusion from `K` into `CrossProductAlgebra f`.

Note that this does *not* make `CrossProductAlgebra f` into a `K`-algebra, because that would
require `incl k * x = x * incl k`. -/
@[simps -isSimp]
def incl : K →ₐ[F] CrossProductAlgebra f where
  toFun k := k • 1
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_mul]
  map_one' := by ext; simp
  map_mul' _ _ := by
    ext
    simp only [val_smul, val_one, Finsupp.smul_single, smul_eq_mul, mul_assoc,
      val_mul, mulLinearMap_single_single, mul_one, AlgEquiv.one_apply, mul_left_comm]
    simp
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

lemma smul_eq_incl_mul (k : K) (x : CrossProductAlgebra f) : k • x = incl f k * x := by
  obtain ⟨x⟩ := x
  ext : 1
  dsimp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add => simp [*]
  | single σ b => simp only [Finsupp.smul_single, smul_eq_mul, incl_apply, val_smul, val_one,
    mulLinearMap_single_single, one_mul, AlgEquiv.one_apply, mul_right_comm _ _ b,
    map_one_fst_of_isMulCocycle₂ Fact.out σ, ne_eq, Units.ne_zero, not_false_eq_true,
    inv_mul_cancel_right₀]

instance [CommSemiring R] [Algebra R K] :
    IsScalarTower R (CrossProductAlgebra f) (CrossProductAlgebra f) where
  smul_assoc r x y := by
    simp only [← algebraMap_smul K r, smul_eq_mul, smul_eq_incl_mul, mul_assoc]

variable (f) in
@[simps]
def of (σ : Gal(K/F)) : (CrossProductAlgebra f)ˣ where
  val.val := .single σ 1
  inv.val := .single σ⁻¹ <| (f (σ⁻¹, σ))⁻¹ * (f (1, 1))⁻¹
  val_inv := by
    ext : 1
    simp only [Units.val_inv_eq_inv_val, mk_mul_mk, mulLinearMap_single_single, mul_inv_cancel,
      map_mul, map_inv₀, one_mul, val_one]
    congr
    convert congr((σ (f (σ⁻¹, σ)))⁻¹ * (σ (f (1, 1)))⁻¹ * (f (1, 1))⁻¹ *
      $((Fact.out : IsMulCocycle₂ f) σ σ⁻¹ σ)) using 1
    · simp [map_one_fst_of_isMulCocycle₂ Fact.out σ, mul_assoc]
    · calc
          (f (1, 1) : K)⁻¹
      _ = σ (f (1, 1)) * (σ (f (1, 1)))⁻¹ * σ (f (σ⁻¹, σ)) * (σ (f (σ⁻¹, σ)))⁻¹ * (f (1, 1))⁻¹ := by
        simp [← map_inv₀, ← map_mul]
      _ = (σ (f (σ⁻¹, σ)))⁻¹ * (σ (f (1, 1)))⁻¹ * (f (1, 1))⁻¹ *
            (σ (f (σ⁻¹, σ)) * σ (f (1, 1))) := by group
      _ = _ := by simp [map_one_snd_of_isMulCocycle₂ Fact.out σ]
  inv_val := by ext : 1; simp only [Units.val_inv_eq_inv_val, mk_mul_mk, mulLinearMap_single_single,
    inv_mul_cancel, map_one, mul_right_comm _ (f _ : K)⁻¹, mul_one, ne_eq, Units.ne_zero,
    not_false_eq_true, inv_mul_cancel₀, one_mul, val_one]

lemma basis_eq_of (σ : Gal(K/F)) : basis σ = (of f σ).val := rfl

variable (f) in
@[simp] lemma of_one : of f 1 = incl f (f (1, 1)) := by ext; simp [incl_apply]

variable (f) in
@[simp] lemma of_mul_of (σ τ : Gal(K/F)) : of f σ * of f τ = incl f (f (σ, τ)) * of f (σ * τ) := by
  ext; simp [incl_apply]

@[simp]
lemma basis_mul_basis (σ τ : Gal(K/F)) :
    basis (f := f) σ * basis τ = incl f (f (σ, τ)) * basis (σ * τ) := of_mul_of ..

lemma of_mul_incl (σ : Gal(K/F)) (c : K) : of f σ * incl f c = incl f (σ c) * of f σ := by
  ext : 1;
  simp only [incl_apply, val_mul, val_of_val, val_smul, val_one, Finsupp.smul_single, smul_eq_mul,
    mulLinearMap_single_single, mul_one, map_mul, map_inv₀, one_mul,
    map_one_snd_of_isMulCocycle₂ Fact.out σ, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe, ne_eq, EmbeddingLike.map_eq_zero_iff, Units.ne_zero, not_false_eq_true,
    inv_mul_cancel_right₀, smul_one_mul]

lemma sum_of (x : CrossProductAlgebra f) : x.val.sum (fun σ c ↦ c • (of f σ).val) = x := by
  ext; simp

lemma of_conj (σ : Gal(K/F)) (k : K) : of f σ * incl f k * (of f σ)⁻¹ = incl f (σ k) := by
  simp [of_mul_incl]

variable [Module.Finite F K] [IsGalois F K]

/-! ### Finite dimensionality -/

@[simp] lemma dim_eq_sq : Module.finrank F (CrossProductAlgebra f) = Module.finrank F K ^ 2 := by
  rw [← Module.finrank_mul_finrank _ K, Module.finrank_eq_card_basis basis,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, sq]

instance : Module.Finite F (CrossProductAlgebra f) :=
  Module.finite_of_finrank_pos <| by simp [pow_pos_iff two_ne_zero, Module.finrank_pos]

/-! ### Centrality -/

instance : Algebra.IsCentral F (CrossProductAlgebra f) := by
  classical
  constructor
  -- Assume `c` is central.
  rintro c hc
  rw [Subalgebra.mem_center_iff] at hc
  -- By comparing the `σ * τ` coefficient of `c * d x_τ = d x_τ * c`,
  -- we get `d τ(c_{τ⁻¹στ}) f(τ, τ⁻¹στ) = c_σ σ(d) f(σ, τ)`.
  have key (d : K) (σ τ : Gal(K/F)) :
      d * τ (c.val (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) = c.val σ * σ d * f (σ, τ) := by
    simpa [incl_apply, mul_assoc] using congr(($(hc <| incl f d * (of f τ).val)).val (σ * τ))
  -- By substituting `d = 1` in the previous equality,
  -- we get `τ(c_{τ⁻¹στ}) f(τ, τ⁻¹στ) = c_σ f(σ, τ)`.
  have key₁ (σ τ : Gal(K/F)) :
      τ (c.val (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) = c.val σ * f (σ, τ) := by
    simpa using key 1 σ τ
  -- By substituting `σ = 1` in the previous equality, we get `τ(c_1 f(1, 1)) = c_1 f(1, 1)`.
  have key₁₁ (τ : Gal(K/F)) : τ (c.val 1 * f (1, 1)) = c.val 1 * f (1, 1) := by
    simpa [map_one_fst_of_isMulCocycle₂ Fact.out τ, map_one_snd_of_isMulCocycle₂ Fact.out τ]
      using key₁ 1 τ
  -- Since `τ` is arbitrary, this says `c_1 f(1, 1) ∈ F`.
  rw [← IsGalois.mem_bot_iff_fixed] at key₁₁
  -- If `c_σ ≠ 0`, we can substitute `key₁` in `key₁₁` and cancel `c_σ` on both sides to get
  -- `σ(d) = d`, ie `σ = 1`.
  have hc₁ {σ} (hσ : c.val σ ≠ 0) : σ = 1 := by
    ext d
    simpa [mul_assoc d, mul_assoc (σ d), mul_comm (c.val _), key₁, hσ] using (key d σ default).symm
  -- Therefore `c = c_1 x_1 = (c_1 f(1, 1)) * 1` is a `F`-multiple of the identity.
  rw [← c.sum_of]
  obtain ⟨a, ha⟩ := key₁₁
  refine AddSubmonoidClass.finsuppSum_mem _ _ _ fun σ hσ ↦ ?_
  simpa [incl_apply, hc₁ hσ, of_one, ← mul_smul, ← ha, Algebra.ofId]
    using Subalgebra.smul_mem _ (one_mem _) _

/-! ### Simplicity -/


variable {I : TwoSidedIdeal (CrossProductAlgebra f)}

open TwoSidedIdeal in
set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-- The standard basis for `CrossProductAlgebra f` descends to a basis for any of its non-trivial
quotients. -/
private def quotientBasis (hI : I ≠ ⊤) : Basis Gal(K/F) K (I.ringCon.Quotient) := by
  -- Let `ϕ` be the quotient map.
  let ϕ := I.ringCon.mkL K
  refine .mk (v := ϕ ∘ basis) ?_ ?_; swap
  · rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top_of_surjective]
    exact Quotient.mk_surjective
  classical
  -- We show that `ϕ(x_τ)` is linearly independent over `τ ∈ J` for any finset `J`.
  rw [← linearIndepOn_univ_iff, linearIndepOn_iff_linearIndepOn_finset]
  rintro J -
  -- For this, we do induction on `J`.
  induction J using Finset.cons_induction with
  -- The case `J = ∅` is trivial.
  | empty => simp
  -- Let's deal with the `J ∪ {σ}` case.
  | cons σ J hσ ih =>
  -- Assume that there is some `a : Gal(K/F) → K` such that `∑ τ ∈ J, a_τ • ϕ(x_τ) = ϕ(x_σ)`.
  -- We want to prove `∀ τ ∈ J, a_τ = 0`.
  rw [Finset.coe_cons, linearIndepOn_insert <| Finset.mem_coe.not.2 hσ,
    Submodule.mem_span_image_finset_iff_exists_fun']
  simp only [ih, comp_apply, not_exists, true_and, basis_eq_of]
  rintro a ha
  have key (c : K) : ∀ τ ∈ J, a τ * τ c = σ c * a τ := by
    refine linearIndepOn_finset_iffₛ.1 ih _ _ ?_
    have ϕ_map_mul (x y) : ϕ (x * y) = ϕ x * ϕ y := rfl
    have aux τ : ϕ (of f τ) * ϕ (incl f c) = ϕ (incl f (τ c)) * ϕ (of f τ) :=
      congr(ϕ $(of_mul_incl (f := f) τ c))
    have aux' (d : K) (x : I.ringCon.Quotient) : d • x = ϕ (incl f d) * x := by
      induction x using Quotient.ind; change ⟦_⟧ = ⟦_⟧; simp [smul_eq_incl_mul]
    calc
          ∑ τ ∈ J, (a τ * τ c) • ϕ (of f τ)
      _ = ∑ τ ∈ J, ϕ (incl f <| a τ) * (ϕ (incl f <| τ c) * ϕ (of f τ)) := by
        simp [mul_assoc, aux', ϕ_map_mul]
      _ = ∑ τ ∈ J, ϕ (incl f <| a τ) * (ϕ (of f τ) * ϕ (incl f c)) := by simp [aux]
      _ = ∑ τ ∈ J, ϕ (incl f <| σ c) * ϕ (incl f <| a τ) * ϕ (of f τ) := by
        simpa [← ha, Finset.mul_sum, Finset.sum_mul, mul_smul, mul_assoc, aux'] using aux σ
      _ = ∑ τ ∈ J, (σ c * a τ) • ϕ (of f τ) := by simp [mul_assoc, aux', ϕ_map_mul]
  have : Nontrivial I.ringCon.Quotient := by simpa [← top_ringCon, ringCon_injective.eq_iff]
  have aux τ : ϕ (of f τ) ≠ 0 := ((of f τ).isUnit.map I.ringCon.mk').ne_zero
  obtain ⟨τ, hτ, haτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero <| ha.trans_ne <| aux _
  apply left_ne_zero_of_smul at haτ
  exact ne_of_mem_of_not_mem hτ hσ <| by simpa [DFunLike.ext_iff, mul_comm, haτ] using (key · τ hτ)

variable (I) in
/-- `CrossProductAlgebra f` is isomorphic to any of its non-trivial quotients. -/
private def equivQuotient (hI : I ≠ ⊤) : CrossProductAlgebra f ≃ₗ[K] I.ringCon.Quotient :=
  basis.repr ≪≫ₗ (quotientBasis I hI).repr.symm

omit [Module.Finite F K] [IsGalois F K] in
variable (I) in
/-- `CrossProductAlgebra f` is isomorphic to any of its non-trivial quotients along the quotient
map. -/
private lemma coe_equivQuotient (hI) : (equivQuotient I hI).toLinearMap = I.ringCon.mkL K := by
  refine basis.ext fun σ ↦ ?_
  simp [equivQuotient, basis, CrossProductAlgebra.basis, RingCon.mkL, quotientBasis]

instance : IsSimpleRing (CrossProductAlgebra f) := by
  refine ⟨⟨fun I ↦ Classical.or_iff_not_imp_right.2 fun hI ↦ ?_⟩⟩
  rw [← I.ker_ringCon_mk', TwoSidedIdeal.ker_eq_bot]
  convert (equivQuotient I hI).injective
  exact congr(⇑$((coe_equivQuotient I hI).symm))

/-! ### The cross product algebra as a central simple algebra -/

variable (f) in
/-- The cross product algebra as a central simple algebra. -/
def asCSA : CSA F := ⟨.of F (CrossProductAlgebra f)⟩

end CrossProductAlgebra
