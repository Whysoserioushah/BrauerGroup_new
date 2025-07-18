import BrauerGroup.Mathlib.Algebra.Algebra.Equiv
import BrauerGroup.Mathlib.Data.DFinsupp.Submonoid
import BrauerGroup.Mathlib.FieldTheory.Galois.Basic
import BrauerGroup.Subfield.Splitting
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

/-!
# Cross product algebra

This file constructs the cross product algebra associated to a 2-cocycle of a field extension
`K / F` and shows that it is a central simple `F`-algebra of dimension `dim(K / F) ^ 2`.
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

variable (f) in
/-- The inclusion from `K` into `CrossProductAlgebra f`.

Note that this does *not* make `CrossProductAlgebra f` into a `K`-algebra, because that would require
`incl k * x = x * incl k`. -/
@[simps]
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
  | hsingle σ b => simp [map_one_fst_of_isMulTwoCocycle Fact.out, mul_right_comm _ _ b]

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

variable (f) in
@[simp] lemma of_one : of f 1 = incl f (f 1) := by ext; simp

variable (f) in
@[simp] lemma of_mul_of (σ τ : Gal(K, F)) : of f σ * of f τ = incl f (f (σ, τ)) * of f (σ * τ) := by
  ext; simp

lemma of_mul_incl (σ : Gal(K, F)) (c : K) : of f σ * incl f c = incl f (σ c) * of f σ := by
  ext; simp [map_one_snd_of_isMulTwoCocycle Fact.out]

lemma sum_of (x : CrossProductAlgebra f) : x.val.sum (fun σ c ↦ c • (of f σ).val) = x := by
  ext; simp

variable [Module.Finite F K] [IsGalois F K]

/-! ### Finite dimensionality -/

@[simp] lemma finrank_eq_sq : Module.finrank F (CrossProductAlgebra f) = Module.finrank F K ^ 2 := by
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
    simpa [mul_assoc] using congr(($(hc <| incl f d * (of f τ).val)).val (σ * τ))
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
  simpa [hc₁ hσ, of_one, ← mul_smul, ← ha, Algebra.ofId] using Subalgebra.smul_mem _ (one_mem _) _

/-! ### Simplicity -/

instance {I : TwoSidedIdeal (CrossProductAlgebra f)} : Module K I.ringCon.Quotient where
  one_smul x := by simp
  mul_smul k1 k2 x := by
    induction x using Quot.induction_on with
    | h g =>
      simp only [Con.rel_eq_coe, RingCon.toCon_coe_eq_coe, RingCon.quot_mk_eq_coe]
      change ((_ : CrossProductAlgebra f) : I.ringCon.Quotient) = _ ;
      simp [mul_smul]
  smul_zero k := by simp
  smul_add k x y := by simp
  add_smul k1 k2 x := by
    induction x using Quot.induction_on with
    | h g =>
      change ((_ : CrossProductAlgebra f) : I.ringCon.Quotient) = _
      simp [add_smul]
  zero_smul x := by
    induction x using Quot.induction_on with
    | h g =>
      change ((_ : CrossProductAlgebra f) : I.ringCon.Quotient) = _
      simp [zero_smul]

section smul_def

variable (I : TwoSidedIdeal (CrossProductAlgebra f))

def π : CrossProductAlgebra f →+* I.ringCon.Quotient := I.ringCon.mk'

def πRes : (incl f).range →+* I.ringCon.Quotient := RingHom.domRestrict (π I) _

variable {I} in
def xx : (πRes I).range → K := fun x ↦ x.2.choose.2.choose

omit [FiniteDimensional F K] [IsGalois F K] in
lemma hx (k : πRes I |>.range) : πRes I ⟨incl f (xx k), by simp⟩ = k := by
  rw [← k.2.choose_spec]
  congr 1
  ext : 1
  exact k.2.choose.2.choose_spec

omit [FiniteDimensional F K] [IsGalois F K] in
lemma hx' (k : K) : πRes I ⟨incl f k, by simp⟩ = I.ringCon.mk' (incl f k) := by
  simp only [RingHom.restrict_apply, πRes, π]

omit [FiniteDimensional F K] [IsGalois F K] in
lemma x_wd (c c' : K) (eq : πRes I ⟨incl f c, by simp⟩ = πRes I ⟨incl f c', by simp⟩) (y : CrossProductAlgebra f) :
    (c - c') • y ∈ I := by
  simp only [πRes, π, RingHom.restrict_apply, RingCon.mk', RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, RingCon.eq] at eq
  rw [TwoSidedIdeal.rel_iff, ← map_sub] at eq
  simpa using I.mul_mem_right _ _ eq

instance (priority := high) : SMul (RingHom.range <| πRes I) I.ringCon.Quotient where
  smul a := Quotient.map'
    (fun y => xx a • y) (by
      rintro y y' (hy : I.ringCon _ _)
      show I.ringCon _ _
      simp only
      rw [TwoSidedIdeal.rel_iff] at hy ⊢
      rw [← smul_sub, smul_eq_incl_mul]
      exact I.mul_mem_left _ _ hy)

omit [FiniteDimensional F K] [IsGalois F K] in
lemma smul_def_quot (a : (πRes I).range) (y : CrossProductAlgebra f) :
    (a • (I.ringCon.mk' y : I.ringCon.Quotient) : I.ringCon.Quotient) =
    (Quotient.mk'' (xx a • y)) := rfl

omit [FiniteDimensional F K] [IsGalois F K] in
lemma smul_def_quot' (a : K) (y : CrossProductAlgebra f) :
    ((⟨π I (incl f a), ⟨_, a, rfl⟩, rfl⟩ : RingHom.range <| πRes I) •
      (I.ringCon.mk' y : I.ringCon.Quotient) : I.ringCon.Quotient) =
    (I.ringCon.mk' (a • y)) := by
  erw [smul_def_quot, Quotient.eq'']
  change I.ringCon _ _
  rw [I.rel_iff, ← sub_smul]
  apply x_wd
  rw [hx, hx']
  rfl

omit [FiniteDimensional F K] [IsGalois F K] in
lemma smul_def_quot'' (a : K) (y : CrossProductAlgebra f) :
  (((⟨π I (incl f a), ⟨_, a, rfl⟩, rfl⟩ : RingHom.range <| πRes I) •
      (by exact Quotient.mk'' y : I.ringCon.Quotient) : I.ringCon.Quotient)) =
    (Quotient.mk'' (a • y) :  I.ringCon.Quotient) :=
  smul_def_quot' I a y

omit [FiniteDimensional F K] [IsGalois F K] in
lemma K_smul_quot (k : K) (x : I.ringCon.Quotient) :
    k • x = (⟨π I (incl f k), by simpa using ⟨incl f k, ⟨k, rfl⟩, rfl⟩⟩ : (πRes I).range) • x := by
  induction x using Quotient.inductionOn' with
  | h g =>
    rw [smul_def_quot'' I k g]
    rfl



end smul_def

set_option maxHeartbeats 1000000 in
def quotientBasis {I : TwoSidedIdeal (CrossProductAlgebra f)} (hI : I ≠ ⊤) :
    Basis Gal(K, F) K I.ringCon.Quotient :=
  Basis.mk (v := fun σ => I.ringCon.mk' (CrossProductAlgebra.basis σ)) (by
  classical
  by_contra rid
  obtain ⟨J, LI, maximal⟩ := exists_maximal_linearIndepOn K (fun (i : Gal(K, F)) =>
      I.ringCon.mk' (CrossProductAlgebra.basis i))
  have ne : J ≠ Set.univ := by
        rintro rfl
        refine rid ?_
        let e : (Set.univ : Set Gal(K, F)) ≃ Gal(K, F) := Equiv.Set.univ Gal(K, F)
        have := linearIndependent_equiv e.symm |>.2 LI
        exact this
  rw [Set.ne_univ_iff_exists_not_mem] at ne
  obtain ⟨σ, hσ⟩ := ne
  obtain ⟨c, c_ne_zero, hc⟩ := maximal σ hσ
  let B := Basis.span LI
  replace hc := Submodule.smul_mem _ c⁻¹ hc
  rw [smul_smul] at hc
  rw [inv_mul_cancel₀ c_ne_zero, one_smul] at hc
  clear c c_ne_zero
  have mem1 : I.ringCon.mk' (CrossProductAlgebra.basis σ) ∈ Submodule.span K
      (Set.range fun (σ : J) ↦ I.ringCon.mk' (CrossProductAlgebra.basis σ)) := by
    convert hc; aesop
  have eq0 : (⟨I.ringCon.mk' (CrossProductAlgebra.basis σ), mem1⟩ : Submodule.span K
      (Set.range fun (σ : J) ↦ I.ringCon.mk' (CrossProductAlgebra.basis σ))) =
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support, B.repr ⟨_, mem1⟩ τ • I.ringCon.mk' (CrossProductAlgebra.basis τ) := by
    conv_lhs => rw [← B.linearCombination_repr ⟨I.ringCon.mk' (CrossProductAlgebra.basis σ), mem1⟩,
      Finsupp.linearCombination_apply, Finsupp.sum]
    rw [AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SetLike.val_smul]
    congr 1
    simp [B, Basis.span_apply]

  simp only at eq0

  have eq1 (c : K) := calc I.ringCon.mk' (incl f (σ c)) * I.ringCon.mk' (CrossProductAlgebra.basis σ)
      _ = I.ringCon.mk' (CrossProductAlgebra.basis σ) * I.ringCon.mk' (incl f c) := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply val_injective
        simp [CrossProductAlgebra.basis, map_one_snd_of_isMulTwoCocycle (f := f) Fact.out σ,
          map_one_fst_of_isMulTwoCocycle (f := f) Fact.out σ]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            I.ringCon.mk' (incl f (B.repr ⟨_, mem1⟩ τ)) * I.ringCon.mk' (CrossProductAlgebra.basis τ) *
              I.ringCon.mk' (incl f c) := by
        conv_lhs => rw [eq0, Finset.sum_mul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [K_smul_quot, smul_def_quot' I, ← map_mul]
        congr 1
        simp [incl_apply, B, smul_one_mul]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            I.ringCon.mk' (incl f (B.repr ⟨_, mem1⟩ τ)) *
            I.ringCon.mk' (incl f (τ.1 c)) * I.ringCon.mk' (CrossProductAlgebra.basis τ) :=
        Finset.sum_congr rfl fun i _ => by
        simp only [_root_.mul_assoc]
        congr 1
        rw [← map_mul, ← map_mul]
        congr 1
        apply val_injective
        simp [CrossProductAlgebra.basis]
        congr 1
        rw [_root_.mul_assoc]
        rw [map_one_snd_of_isMulTwoCocycle (f := f) Fact.out i.1]
        simp
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            I.ringCon.mk' (incl f (B.repr ⟨_, mem1⟩ τ * τ.1 c)) *
            I.ringCon.mk' (CrossProductAlgebra.basis τ) :=
        Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul]

  have eq2 (c : K) := calc I.ringCon.mk' (incl f (σ c)) * I.ringCon.mk' (CrossProductAlgebra.basis σ)
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          I.ringCon.mk' (incl f (σ c * (B.repr ⟨_, mem1⟩) τ)) *
          I.ringCon.mk' (CrossProductAlgebra.basis τ) := by
        conv_lhs => rw [eq0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [K_smul_quot, smul_def_quot' I, ← map_mul, ← _root_.mul_assoc]
        congr 1
        simp only [incl_apply, smul_one_mul, B]
        rw [mul_smul]

  have eq3 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            I.ringCon.mk' (incl f (B.repr ⟨_, mem1⟩ τ * τ.1 c)) *
            I.ringCon.mk' (CrossProductAlgebra.basis τ) =
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          I.ringCon.mk' (incl f (σ c * (B.repr ⟨_, mem1⟩) τ)) *
          I.ringCon.mk' (CrossProductAlgebra.basis τ) :=
    eq1 c |>.symm.trans <| eq2 c

  have eq4 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          I.ringCon.mk' (incl f (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ)) *
          I.ringCon.mk' (CrossProductAlgebra.basis τ) = 0 := by
    simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    convert eq3 c
    · simp only [← map_mul]
    · simp only [← map_mul]

  have eq5 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ) •
          I.ringCon.mk' (CrossProductAlgebra.basis τ) = 0 := by
    rw [← eq4 c]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [K_smul_quot, smul_def_quot' I,  ← map_mul]
    congr 1
    simp
  have eq6 (c : K) := linearIndependent_iff'' |>.1 LI (B.repr ⟨_, mem1⟩).support
    (fun τ => B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ)
    (by
      intro i hi
      simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hi
      simp only [hi, zero_mul, mul_zero, sub_self]) (eq5 c)
  simp only [sub_eq_zero, Subtype.forall] at eq6
  have : (B.repr ⟨_, mem1⟩).support ≠ ∅ := by
    intro rid
    simp only [rid, Finset.sum_empty] at eq0
    change _ = I.ringCon.mk' 0 at eq0
    erw [Quotient.eq''] at eq0
    change I.ringCon _ _ at eq0
    rw [I.rel_iff, sub_zero] at eq0
    have mem' := I.mul_mem_left (CrossProductAlgebra.of f σ)⁻¹.1 _ eq0
    simp only [Units.inv_mul] at mem'
    refine hI <| eq_top_iff.2 fun x _ => ?_
    have : ((of (f := f) σ)⁻¹.1 * CrossProductAlgebra.basis σ) = 1 := by
      apply val_injective
      simp only [CrossProductAlgebra.basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply,
        AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, val_mul,
        val_inv_of_val, Units.val_inv_eq_inv_val, valAddEquiv_symm_apply_val,
        mulLinearMap_single_single, inv_mul_cancel, map_one, _root_.mul_one, val_one, B]
      congr 1; field_simp
    simpa [this] using I.mul_mem_left x _ mem'

  obtain ⟨τ, τ_mem⟩ := Finset.nonempty_of_ne_empty this
  have eq7 : σ = τ := by
    ext c
    specialize eq6 c τ τ.2
    rw [mul_comm] at eq6
    simp only [Subtype.coe_eta, mul_eq_mul_right_iff] at eq6
    refine eq6.recOn Eq.symm fun rid ↦ ?_
    simp only [Finsupp.mem_support_iff, ne_eq] at τ_mem
    contradiction
  subst eq7
  exact hσ τ.2) <| by
  rintro z -
  induction z using Quotient.inductionOn' with | h z =>
  have eq1 := CrossProductAlgebra.basis |>.linearCombination_repr z
  rw [← eq1]
  change I.ringCon.mk' _ ∈ _
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [show I.ringCon.mk' ((CrossProductAlgebra.basis.repr z) σ • CrossProductAlgebra.basis σ) =
    (⟨π I (incl f (CrossProductAlgebra.basis.repr z σ)), by
      simp only [πRes, π, RingHom.mem_range,
        RingHom.restrict_apply, Subtype.exists, AlgHom.mem_range, exists_prop', nonempty_prop,
        exists_exists_eq_and]
      refine ⟨(CrossProductAlgebra.basis.repr z σ), rfl⟩⟩ : (πRes I).range) •
      I.ringCon.mk' (CrossProductAlgebra.basis σ) by
      rw [smul_def_quot']]
  rw [← K_smul_quot]
  refine Submodule.smul_mem _ _ <| Submodule.subset_span ⟨σ, ?_⟩
  simp

def π₁ (I : TwoSidedIdeal <| CrossProductAlgebra f) (ne_top : I ≠ ⊤) :
    CrossProductAlgebra f ≃ₗ[K] I.ringCon.Quotient :=
  CrossProductAlgebra.basis.equiv (quotientBasis ne_top) (Equiv.refl _)

def π₂ (I : TwoSidedIdeal <| CrossProductAlgebra f) :
    CrossProductAlgebra f →ₗ[K] I.ringCon.Quotient where
  __ := π I
  map_smul' c x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, RingHom.id_apply]
    simp only [K_smul_quot]
    erw [smul_def_quot' I]
    rfl

omit [FiniteDimensional F K] [IsGalois F K] in
lemma equal (I : TwoSidedIdeal <| CrossProductAlgebra f) (ne_top : I ≠ ⊤) : π₁ I ne_top = π₂ I := by
  apply Basis.ext (b := CrossProductAlgebra.basis)
  intro σ
  delta π₁
  erw [Basis.equiv_apply]
  simp [basis, CrossProductAlgebra.basis, map_mul, map_inv₀, π₂, π, quotientBasis]

omit [FiniteDimensional F K] [IsGalois F K] in
lemma π_inj (I : TwoSidedIdeal <| CrossProductAlgebra f) (ne_top : I ≠ ⊤) :
    Function.Injective (π I) := by
  change Function.Injective (π₂ I)
  rw [← equal (ne_top := ne_top)]
  exact LinearEquiv.injective _

instance : IsSimpleRing (CrossProductAlgebra f) := ⟨⟨fun I ↦ by
  by_contra! h
  have inj : Function.Injective (π I) := π_inj I h.2
  rw [TwoSidedIdeal.injective_iff_ker_eq_bot] at inj
  refine h.1 <| inj ▸ ?_
  ext x
  simp only [π, TwoSidedIdeal.mem_ker]
  change _ ↔ _ = I.ringCon.mk' 0
  erw [Quotient.eq'']
  change _ ↔ I.ringCon _ _
  rw [I.rel_iff, sub_zero] ⟩⟩

/-! ### The cross product algebra as a central simple algebra -/

variable (f) in
def asCSA [IsGalois F K] : CSA F :=
  ⟨.of F (CrossProductAlgebra f)⟩

end CrossProductAlgebra
