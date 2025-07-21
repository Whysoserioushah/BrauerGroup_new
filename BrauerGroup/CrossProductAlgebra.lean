import BrauerGroup.Mathlib.Algebra.Algebra.Equiv
import BrauerGroup.Mathlib.Data.DFinsupp.Submonoid
import BrauerGroup.Mathlib.FieldTheory.Galois.Basic
import BrauerGroup.Mathlib.LinearAlgebra.Finsupp.LinearCombination
import BrauerGroup.Mathlib.LinearAlgebra.LinearIndependent.Defs
import BrauerGroup.Mathlib.RingTheory.Congruence.Basic
import BrauerGroup.Mathlib.RingTheory.TwoSidedIdeal.Lattice
import BrauerGroup.Subfield.Splitting
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

/-!
# Cross product algebra

This file constructs the cross product algebra associated to a 2-cocycle of a field extension
`K / F` and shows that it is a central simple `F`-algebra of dimension `dim(K / F) ^ 2`.

## References

* [*Advanced Algebra*]
-/

open groupCohomology Function

suppress_compilation

variable {R S F K : Type*} [Field F] [Field K] [Algebra F K] {f : Gal(K, F) × Gal(K, F) → Kˣ}

@[ext]
structure CrossProductAlgebra (f : Gal(K, F) × Gal(K, F) → Kˣ) where
  val : Gal(K, F) →₀ K

namespace CrossProductAlgebra
variable {x y : CrossProductAlgebra f}

lemma val_injective : Injective (val (f := f)) := fun _ _ ↦ CrossProductAlgebra.ext
lemma val_surjective : Surjective (val (f := f)) := fun x ↦ ⟨⟨x⟩, rfl⟩
lemma val_bijective : Bijective (val (f := f)) := ⟨val_injective, val_surjective⟩

@[simp] lemma val_inj : x.val = y.val ↔ x = y := val_injective.eq_iff

lemma «forall» {P : CrossProductAlgebra f → Prop} : (∀ x, P x) ↔ ∀ x, P (mk x) := by
  rw [val_surjective.forall]

instance : Nontrivial (CrossProductAlgebra f) := val_surjective.nontrivial

instance : Zero (CrossProductAlgebra f) where
  zero := ⟨0⟩

instance : Add (CrossProductAlgebra f) where
  add x y := ⟨x.val + y.val⟩

instance : Neg (CrossProductAlgebra f) where
  neg x := ⟨-x.val⟩

instance : Sub (CrossProductAlgebra f) where
  sub x y := ⟨x.val - y.val⟩

instance [Semiring R] [Module R K] : SMul R (CrossProductAlgebra f) where
  smul r x := ⟨r • x.val⟩

@[simp] lemma val_zero : (0 : CrossProductAlgebra f).val = 0 := rfl
@[simp] lemma val_add (x y : CrossProductAlgebra f) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_smul [Semiring R] [Module R K] (r : R) (x : CrossProductAlgebra f) :
    (r • x).val = r • x.val := rfl
@[simp] lemma val_neg (x : CrossProductAlgebra f) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : CrossProductAlgebra f) : (x - y).val = x.val - y.val := rfl

@[simp] lemma mk_zero : (mk 0 : CrossProductAlgebra f) = 0 := rfl
@[simp] lemma mk_add_mk (x y : Gal(K, F) →₀ K) :
    (mk x + mk y : CrossProductAlgebra f) = mk (x + y) := rfl
@[simp] lemma smul_mk [Semiring R] [Module R K] (r : R) (x : Gal(K, F) →₀ K) :
    (r • mk x : CrossProductAlgebra f) = mk (r • x) := rfl
@[simp] lemma neg_mk (x : Gal(K, F) →₀ K) : (- mk x : CrossProductAlgebra f) = mk (-x) := rfl
@[simp] lemma mk_sub_mk (x y : Gal(K, F) →₀ K) :
    (mk x - mk y : CrossProductAlgebra f) = mk (x - y) := rfl

instance addCommGroup : AddCommGroup (CrossProductAlgebra f) :=
  val_injective.addCommGroup val val_zero val_add val_neg val_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simps]
def valAddEquiv : CrossProductAlgebra f ≃+ (Gal(K, F) →₀ K) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := val_add

@[simp]
lemma val_finsuppSum {α M : Type*} [AddCommMonoid M] (g : α →₀ M)
    (h : α → M → CrossProductAlgebra f) :
    (g.sum h).val = g.sum (fun a m ↦ (h a m).val) := map_finsupp_sum valAddEquiv ..

instance [Semiring R] [Module R K] : Module R (CrossProductAlgebra f) :=
  val_injective.module _ valAddEquiv.toAddMonoidHom val_smul

instance [Semiring R] [Semiring S] [Module R K] [Module S K] [Module R S] [IsScalarTower R S K] :
    IsScalarTower R S (CrossProductAlgebra f) where
  smul_assoc r s x := by ext; simp [smul_assoc]

@[simps]
def valLinearEquiv [Semiring R] [Module R K] : CrossProductAlgebra f ≃ₗ[R] (Gal(K, F) →₀ K) where
  __ := valAddEquiv
  map_smul' := val_smul

@[simps]
def basis : Basis Gal(K, F) K (CrossProductAlgebra f) where
  repr := valLinearEquiv

lemma basis_val (σ : Gal(K, F)) : (basis (f := f) σ).val = .single σ 1 := rfl
lemma mk_single_one (σ : Gal(K, F)) : mk (.single σ 1) = basis (f := f) σ := rfl

variable (f) in
def mulLinearMap : (Gal(K, F) →₀ K) →ₗ[F] (Gal(K, F) →₀ K) →ₗ[F] (Gal(K, F) →₀ K) :=
  Finsupp.lsum F fun σ =>
  { toFun c := Finsupp.lsum F fun τ =>
      { toFun d := .single (σ * τ) (c * σ d * f (σ, τ))
        map_add' := by simp [mul_add, add_mul]
        map_smul' := by simp }
    map_add' _ _ := by ext; simp [mul_add, add_mul]
    map_smul' _ _ := by ext; simp }

variable (f) in
@[simp]
lemma mulLinearMap_single_single (c d : K) (σ τ : Gal(K, F)) :
    mulLinearMap f (.single σ c) (.single τ d) = .single (σ * τ) (c * σ d * f (σ, τ)) := by
  simp [mulLinearMap]

variable (f) in
@[simp]
lemma mulLinearMap_single_left_apply (c : K) (σ : Gal(K, F)) (x : Gal(K, F) →₀ K) (τ : Gal(K, F)) :
    mulLinearMap f (.single σ c) x τ = c * σ (x (σ⁻¹ * τ)) * f (σ, σ⁻¹ * τ) := by
  classical simp +contextual [mulLinearMap, Finsupp.single_apply, ← eq_inv_mul_iff_mul_eq]

variable (f) in
@[simp]
lemma mulLinearMap_single_right_apply (c : K) (σ : Gal(K, F)) (x : Gal(K, F) →₀ K) (τ : Gal(K, F)) :
    mulLinearMap f x (.single σ c) τ = x (τ * σ⁻¹) * τ (σ⁻¹ c) * f (τ * σ⁻¹, σ) := by
  classical simp +contextual [mulLinearMap, Finsupp.single_apply, ← eq_mul_inv_iff_mul_eq]

instance : One (CrossProductAlgebra f) where
  one := ⟨.single 1 (f 1)⁻¹⟩

instance : Mul (CrossProductAlgebra f) where
  mul x y := ⟨mulLinearMap f x.val y.val⟩

lemma one_def : (1 : CrossProductAlgebra f) = ⟨.single 1 (f 1)⁻¹⟩ := rfl

@[simp] lemma val_one : (1 : CrossProductAlgebra f).val = .single 1 (f 1)⁻¹ := rfl
@[simp] lemma val_mul (x y : CrossProductAlgebra f) : (x * y).val = mulLinearMap f x.val y.val := rfl

@[simp] lemma mk_mul_mk (x y : Gal(K, F) →₀ K) :
    (mk x * mk y : CrossProductAlgebra f) = mk (mulLinearMap f x y) := rfl

variable [Fact <| IsMulTwoCocycle f]

instance monoid : Monoid (CrossProductAlgebra f) where
  one_mul := by
    rintro ⟨x⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [*]
    | hsingle σ a => simp [map_one_fst_of_isMulTwoCocycle Fact.out, mul_right_comm _ a]
  mul_one := by
    rintro ⟨x⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [*]
    | hsingle σ a => simp [map_one_snd_of_isMulTwoCocycle Fact.out]
  mul_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    ext : 1
    dsimp
    induction x using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [*]
    | hsingle σ a =>
    induction y using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [*]
    | hsingle τ b =>
    induction z using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [-mulLinearMap_single_single, *]
    | hsingle ν c =>
    simp only [mulLinearMap_single_single, mul_assoc, AlgEquiv.mul_apply, map_mul,
      mul_left_comm _ (σ (τ c))]
    congr 4
    simpa [mul_comm] using congr(($((Fact.out : IsMulTwoCocycle f) σ τ ν)).val)

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
  refine .ofModule ?_ ?_ <;> intros <;> ext <;> simp [map_smul]

lemma algebraMap_val [CommSemiring R] [Algebra R F] [Algebra R K] [IsScalarTower R F K] (r : R) :
    (algebraMap R (CrossProductAlgebra f) r).val = .single 1 (algebraMap R K r * (f 1)⁻¹) := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [val_smul, val_one, Prod.mk_one_one, Finsupp.smul_single,
    Units.val_inv_eq_inv_val, ← Algebra.smul_def]

omit [Fact <| IsMulTwoCocycle f] in
lemma basis_smul_comm (σ : Gal(K, F)) (k1 k2 : K) (x : CrossProductAlgebra f) :
    (k1 • basis (f := f) σ) * (k2 • x) = σ k2 • k1 • basis σ * x := by
  apply val_injective
  simp only [basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, val_mul, val_smul, valAddEquiv_symm_apply_val,
    Finsupp.smul_single, smul_eq_mul, _root_.mul_one]
  induction x.val using Finsupp.induction_linear with
  | h0 => simp
  | hadd _ _ _ _ => simp_all[smul_add]
  | hsingle a b =>
    simp [← _root_.mul_assoc, mul_comm k1 (σ k2)]

variable (f) in
/-- The inclusion from `K` into `CrossProductAlgebra f`.

Note that this does *not* make `CrossProductAlgebra f` into a `K`-algebra, because that would require
`incl k * x = x * incl k`. -/
@[simps -isSimp]
def incl : K →ₐ[F] CrossProductAlgebra f where
  toFun k := k • 1
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_mul]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc, mul_left_comm]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

lemma smul_eq_incl_mul (k : K) (x : CrossProductAlgebra f) : k • x = incl f k * x := by
  obtain ⟨x⟩ := x
  ext : 1
  dsimp
  induction x using Finsupp.induction_linear with
  | h0 => simp
  | hadd => simp [*]
  | hsingle σ b => simp [incl_apply, map_one_fst_of_isMulTwoCocycle Fact.out, mul_right_comm _ _ b]

instance [CommSemiring R] [Algebra R K] :
    IsScalarTower R (CrossProductAlgebra f) (CrossProductAlgebra f) where
  smul_assoc r x y := by
    simp only [← algebraMap_smul K r, smul_eq_mul, smul_eq_incl_mul, mul_smul, mul_assoc]

variable (f) in
@[simps]
def of (σ : Gal(K, F)) : (CrossProductAlgebra f)ˣ where
  val.val := .single σ 1
  inv.val := .single σ⁻¹ <| (f (σ⁻¹, σ))⁻¹ * (f 1)⁻¹
  val_inv := by
    ext : 1
    simp
    congr
    convert congr((σ (f (σ⁻¹, σ)))⁻¹ * (σ (f 1))⁻¹ * (f 1)⁻¹ *
      $((Fact.out : IsMulTwoCocycle f) σ σ⁻¹ σ)) using 1
    · simp [map_one_fst_of_isMulTwoCocycle Fact.out, map_one_snd_of_isMulTwoCocycle Fact.out,
        mul_assoc]
    · calc
            (f 1 : K)⁻¹
        _ = σ (f 1) * (σ (f 1))⁻¹ * σ (f (σ⁻¹, σ)) * (σ (f (σ⁻¹, σ)))⁻¹ * (f 1)⁻¹ := by
          simp [← map_inv₀, ← map_mul]
        _ = (σ (f (σ⁻¹, σ)))⁻¹ * (σ (f 1))⁻¹ * (f 1)⁻¹ * (σ (f (σ⁻¹, σ)) * σ (f 1)) := by group
        _ = _ := by
          simp [map_one_fst_of_isMulTwoCocycle Fact.out, map_one_snd_of_isMulTwoCocycle Fact.out]
  inv_val := by ext : 1; simp [mul_right_comm _ (f _ : K)⁻¹]

lemma basis_eq_of (σ : Gal(K, F)) : basis σ = (of f σ).val := rfl

variable (f) in
@[simp] lemma of_one : of f 1 = incl f (f 1) := by ext; simp [incl_apply]

variable (f) in
@[simp] lemma of_mul_of (σ τ : Gal(K, F)) : of f σ * of f τ = incl f (f (σ, τ)) * of f (σ * τ) := by
  ext; simp [incl_apply]

@[simp]
lemma basis_mul_basis (σ τ : Gal(K, F)) :
    basis (f := f) σ * basis τ = incl f (f (σ, τ)) * basis (σ * τ) := of_mul_of ..

lemma of_mul_incl (σ : Gal(K, F)) (c : K) : of f σ * incl f c = incl f (σ c) * of f σ := by
  ext : 1; simp [map_one_snd_of_isMulTwoCocycle Fact.out, incl_apply]

lemma sum_of (x : CrossProductAlgebra f) : x.val.sum (fun σ c ↦ c • (of f σ).val) = x := by
  ext; simp

lemma of_conj (σ : Gal(K, F)) (k : K) : of f σ * incl f k * (of f σ)⁻¹ = incl f (σ k) := by
  rw [of_mul_incl]; field_simp

variable [Module.Finite F K] [IsGalois F K]

/-! ### Finite dimensionality -/

@[simp] lemma dim_eq_sq : Module.finrank F (CrossProductAlgebra f) = Module.finrank F K ^ 2 := by
  rw [← Module.finrank_mul_finrank _ K, Module.finrank_eq_card_basis basis,
    IsGalois.card_aut_eq_finrank, sq]

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
  have key (d : K) (σ τ : Gal(K, F)) :
      d * τ (c.val (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) = c.val σ * σ d * f (σ, τ) := by
    simpa [incl_apply, mul_assoc] using congr(($(hc <| incl f d * (of f τ).val)).val (σ * τ))
  -- By substituting `d = 1` in the previous equality,
  -- we get `τ(c_{τ⁻¹στ}) f(τ, τ⁻¹στ) = c_σ f(σ, τ)`.
  have key₁ (σ τ : Gal(K, F)) :
      τ (c.val (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) = c.val σ * f (σ, τ) := by
    simpa using key 1 σ τ
  -- By substituting `σ = 1` in the previous equality, we get `τ(c_1 f(1, 1)) = c_1 f(1, 1)`.
  have key₁₁ (τ : Gal(K, F)) : τ (c.val 1 * f 1) = c.val 1 * f 1 := by
    simpa [map_one_fst_of_isMulTwoCocycle Fact.out, map_one_snd_of_isMulTwoCocycle Fact.out]
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
  refine finsuppSum_mem fun σ hσ ↦ ?_
  simpa [incl_apply, hc₁ hσ, of_one, ← mul_smul, ← ha, Algebra.ofId]
    using Subalgebra.smul_mem _ (one_mem _) _

/-! ### Simplicity -/

variable {I : TwoSidedIdeal (CrossProductAlgebra f)}

variable (I) in
/-- The standard basis for `CrossProductAlgebra f` descends to a basis for any of its non-trivial
quotients. -/
private def quotientBasis (hI : I ≠ ⊤) : Basis Gal(K, F) K I.ringCon.Quotient := by
  -- Let `ϕ` be the quotient map.
  let ϕ := I.ringCon.mkL K
  refine .mk (v := ϕ ∘ basis) ?_ ?_; swap
  · rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top_of_surjective]
    exact Quotient.mk_surjective
  classical
  -- We show that `ϕ(x_τ)` is linearly independent over `τ ∈ J` for any finset `J`.
  rw [linearIndependent_iff_linearIndepOn_finset]
  rintro J
  -- For this, we do induction on `J`.
  induction J using Finset.cons_induction with
  -- The case `J = ∅` is trivial.
  | empty => simp
  -- Let's deal with the `J ∪ {σ}` case.
  | cons σ J hσ ih =>
  -- Assume that there is some `a : Gal(K, F) → K` such that `∑ τ ∈ J, a_τ • ϕ(x_τ) = ϕ(x_σ)`.
  -- We want to prove `∀ τ ∈ J, a_τ = 0`.
  rw [Finset.coe_cons, linearIndepOn_insert <| Finset.mem_coe.not.2 hσ,
    Submodule.mem_span_image_finset_iff_exists_fun]
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
  have : Nontrivial I.ringCon.Quotient := by simpa
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
  rw [← I.ker_ringCon_mk', ← TwoSidedIdeal.injective_iff_ker_eq_bot]
  convert (equivQuotient I hI).injective
  exact congr(⇑$((coe_equivQuotient I hI).symm))

/-! ### The cross product algebra as a central simple algebra -/

variable (f) in
/-- The cross product algebra as a central simple algebra. -/
def asCSA [IsGalois F K] : CSA F := ⟨.of F (CrossProductAlgebra f)⟩

end CrossProductAlgebra
