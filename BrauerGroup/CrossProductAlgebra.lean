import BrauerGroup.Mathlib.Algebra.Algebra.Equiv
import BrauerGroup.Mathlib.Data.DFinsupp.Submonoid
import BrauerGroup.Mathlib.FieldTheory.Galois.Basic
import BrauerGroup.Subfield.Splitting
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

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
`ι k * x = x * ι k`. -/
@[simps]
def ι : K →ₐ[F] CrossProductAlgebra f where
  toFun k := k • 1
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_mul]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc, mul_left_comm]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

lemma smul_eq_ι_mul (k : K) (x : CrossProductAlgebra f) : k • x = ι f k * x := by
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
    simp only [← algebraMap_smul K r, smul_eq_mul, smul_eq_ι_mul, mul_smul, mul_assoc]

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
@[simp] lemma of_one : of f 1 = ι f (f 1) := by ext; simp

variable (f) in
@[simp] lemma of_mul_of (σ τ : Gal(K, F)) : of f σ * of f τ = ι f (f (σ, τ)) * of f (σ * τ) := by
  ext; simp

lemma of_mul_ι (σ : Gal(K, F)) (c : K) : of f σ * ι f c = ι f (σ c) * of f σ := by
  ext; simp [map_one_snd_of_isMulTwoCocycle Fact.out]

lemma sum_of (x : CrossProductAlgebra f) : x.val.sum (fun σ c ↦ c • (of f σ).val) = x := by
  ext; simp

variable [Module.Finite F K] [IsGalois F K]

@[simp] lemma finrank_eq_sq : Module.finrank F (CrossProductAlgebra f) = Module.finrank F K ^ 2 := by
  rw [← Module.finrank_mul_finrank _ K, Module.finrank_eq_card_basis basis,
    IsGalois.card_aut_eq_finrank, sq]

instance : Module.Finite F (CrossProductAlgebra f) :=
  Module.finite_of_finrank_pos <| by simp [pow_pos_iff two_ne_zero, Module.finrank_pos]

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
    simpa [mul_assoc] using congr(($(hc <| ι f d * (of f τ).val)).val (σ * τ))
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

end CrossProductAlgebra
