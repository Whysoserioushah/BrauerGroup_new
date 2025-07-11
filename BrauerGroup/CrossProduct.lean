import BrauerGroup.Subfield.Splitting
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

open groupCohomology Function

suppress_compilation

notation "Gal("K ", "F")" => K ≃ₐ[F] K

variable {R S F K : Type*} [Field F] [Field K] [Algebra F K] {f : Gal(K, F) × Gal(K, F) → Kˣ}

@[ext]
structure CrossProduct (f : Gal(K, F) × Gal(K, F) → Kˣ) where
  val : Gal(K, F) →₀ K

namespace CrossProduct
variable {x y : CrossProduct f}

lemma val_injective : Injective (val (f := f)) := fun _ _ ↦ CrossProduct.ext
lemma val_surjective : Surjective (val (f := f)) := fun x ↦ ⟨⟨x⟩, rfl⟩
lemma val_bijective : Bijective (val (f := f)) := ⟨val_injective, val_surjective⟩

@[simp] lemma val_inj : x.val = y.val ↔ x = y := val_injective.eq_iff

instance : Nontrivial (CrossProduct f) := val_surjective.nontrivial

instance : Zero (CrossProduct f) where
  zero := ⟨0⟩

instance : Add (CrossProduct f) where
  add x y := ⟨x.val + y.val⟩

instance : Neg (CrossProduct f) where
  neg x := ⟨-x.val⟩

instance : Sub (CrossProduct f) where
  sub x y := ⟨x.val - y.val⟩

instance [Semiring R] [Module R K] : SMul R (CrossProduct f) where
  smul r x := ⟨r • x.val⟩

@[simp] lemma val_zero : (0 : CrossProduct f).val = 0 := rfl
@[simp] lemma val_add (x y : CrossProduct f) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_smul [Semiring R] [Module R K] (r : R) (x : CrossProduct f) :
    (r • x).val = r • x.val := rfl
lemma smul_val [Semiring R] [Module R K] (r : R) (x : CrossProduct f) :
    r • x = ⟨r • x.val⟩ := rfl
@[simp] lemma val_neg (x : CrossProduct f) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : CrossProduct f) : (x - y).val = x.val - y.val := rfl

instance addCommGroup : AddCommGroup (CrossProduct f) :=
  val_injective.addCommGroup val val_zero val_add val_neg val_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simps]
def valAddEquiv : CrossProduct f ≃+ (Gal(K, F) →₀ K) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := val_add

instance [Semiring R] [Module R K] : Module R (CrossProduct f) :=
  val_injective.module _ valAddEquiv.toAddMonoidHom val_smul

instance [Semiring R] [Semiring S] [Module R K] [Module S K] [Module R S] [IsScalarTower R S K] :
    IsScalarTower R S (CrossProduct f) where
  smul_assoc r s x := by ext; simp [smul_assoc]

@[simps]
def valLinearEquiv [Semiring R] [Module R K] : CrossProduct f ≃ₗ[R] (Gal(K, F) →₀ K) where
  __ := valAddEquiv
  map_smul' := val_smul

def basis : Basis Gal(K, F) K (CrossProduct f) where
  repr := valLinearEquiv

lemma basis_val {σ : Gal(K, F)} :
    (basis (f := f) σ).val = Finsupp.single σ 1 := by
  simp [basis]

variable (f) in
def mulLinearMap : (Gal(K, F) →₀ K) →ₗ[F] (Gal(K, F) →₀ K) →ₗ[F] (Gal(K, F) →₀ K) :=
  Finsupp.lsum F fun σ =>
  { toFun c := Finsupp.lsum F fun τ =>
      { toFun d := .single (σ * τ) (c * σ d * f (σ, τ))
        map_add' := by simp [mul_add, add_mul]
        map_smul' := by simp }
    map_add' _ _ := by ext; simp [mul_add, add_mul]
    map_smul' _ _ := by ext; simp }

@[simp]
lemma mulLinearMap_single_single (c d : K) (σ τ : Gal(K, F)):
    mulLinearMap f (.single σ c) (.single τ d) = .single (σ * τ) (c * σ d * f (σ, τ)) := by
  simp [mulLinearMap]

instance : One (CrossProduct f) where
  one := ⟨.single 1 (f 1)⁻¹⟩

instance : Mul (CrossProduct f) where
  mul x y := ⟨mulLinearMap f x.val y.val⟩

@[simp] lemma val_one : (1 : CrossProduct f).val = .single 1 (f 1)⁻¹ := rfl
@[simp] lemma val_mul (x y : CrossProduct f) : (x * y).val = mulLinearMap f x.val y.val := rfl

variable [Fact <| IsMulTwoCocycle f]

instance monoid : Monoid (CrossProduct f) where
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

instance : Ring (CrossProduct f) where
  __ := addCommGroup
  __ := monoid
  left_distrib := by intros; ext; simp
  right_distrib := by intros; ext; simp
  zero_mul := by intros; ext; simp
  mul_zero := by intros; ext; simp
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]
  neg_add_cancel := by intros; ext; simp

instance algebra [CommSemiring R] [Algebra R F] [Module R K] [IsScalarTower R F K] :
    Algebra R (CrossProduct f) := by
  refine .ofModule ?_ ?_ <;> intros <;> ext <;> simp [map_smul]

lemma algebraMap_val [CommSemiring R] [Algebra R F] [Algebra R K] [IsScalarTower R F K] (r : R) :
    (algebraMap R (CrossProduct f) r).val = .single 1 (algebraMap R K r * (f 1)⁻¹) := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [val_smul, val_one, Prod.mk_one_one, Finsupp.smul_single,
    Units.val_inv_eq_inv_val, ← Algebra.smul_def]

omit [Fact (IsMulTwoCocycle f)] in
lemma basis_coe_eq (σ : K ≃ₐ[F] K): (⟨.single σ 1⟩ : CrossProduct f) = basis σ := rfl

omit [Fact (IsMulTwoCocycle f)] in
theorem single_induction {p : CrossProduct f → Prop} (x : CrossProduct f) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y))
    (hsingle : ∀ σ : Gal(K, F), ∀ k : K, p (k • basis σ)) : p x := show p (⟨x.val⟩) by
  induction x.val using Finsupp.induction_linear with
  | h0 => show p 0; assumption
  | hadd f g hf hg => show p (⟨f⟩ + ⟨g⟩); exact hadd _ _ hf hg
  | hsingle σ k =>
    simpa [← basis_coe_eq, smul_val] using hsingle σ k

-- p (x + y) => p ⟨x + y⟩ => p ⟨x⟩ + ⟨y⟩

variable (f) in
/-- The inclusion from `K` into `CrossProduct f`.

Note that this does *not* make `CrossProduct f` into a `K`-algebra, because that would require
`ι k * x = x * ι k`. -/
@[simps]
def ι : K →ₐ[F] CrossProduct f where
  toFun k := k • 1
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_mul]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc, mul_left_comm]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

lemma smul_eq_ι_mul (k : K) (x : CrossProduct f) : k • x = ι f k * x := by
  obtain ⟨x⟩ := x
  ext : 1
  dsimp
  induction x using Finsupp.induction_linear with
  | h0 => simp
  | hadd => simp [*]
  | hsingle σ b => simp [map_one_fst_of_isMulTwoCocycle Fact.out, mul_right_comm _ _ b]

-- scoped instance : IsScalarTower K (CrossProduct f) (CrossProduct f) where
--   smul_assoc k x y := by simp only [smul_eq_mul, smul_eq_ι_mul, mul_smul, mul_assoc]

@[simps]
def singleUnit (σ : K ≃ₐ[F] K) : (CrossProduct f)ˣ where
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

lemma singleUnit_mul_singleUnit (σ τ : K ≃ₐ[F] K) :
    (singleUnit σ).val * (singleUnit τ).val = ι f (f (σ, τ)) * (singleUnit (σ * τ)).val := by
  haveI : IsScalarTower K (CrossProduct f) (CrossProduct f) := {
    smul_assoc k x y := by simp only [smul_eq_mul, smul_eq_ι_mul, mul_smul, mul_assoc]}
  ext : 1
  simp

variable [Module.Finite F K] [IsGalois F K]

@[simp] lemma finrank_eq_sq : Module.finrank F (CrossProduct f) = Module.finrank F K ^ 2 := by
  rw [← Module.finrank_mul_finrank _ K, Module.finrank_eq_card_basis basis,
    IsGalois.card_aut_eq_finrank, sq]

instance : Module.Finite F (CrossProduct f) :=
  Module.finite_of_finrank_pos <| by simp [pow_pos_iff two_ne_zero, Module.finrank_pos]

instance : Algebra.IsCentral F (CrossProduct f) := by
  classical
  constructor
  rintro z hz
  rw [Subalgebra.mem_center_iff] at hz
  set s : (K ≃ₐ[F] K) → K :=
    fun σ => if σ ∈ (basis.repr z).support then basis.repr z σ else 0

  have eq1 : z = ∑ σ : K ≃ₐ[F] K, s σ • ⟨Finsupp.single σ 1⟩ := by
    conv_lhs => rw [← basis.linearCombination_repr z, Finsupp.linearCombination_apply,
      Finsupp.sum]
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finsupp.mem_support_iff, ne_eq,
        Decidable.not_not, true_and, ite_not, ite_smul, zero_smul, ite_eq_left_iff, smul_eq_zero,
        s] at hx ⊢
      simp [hx]
    intro x _
    simp only [basis, valLinearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
      EquivLike.coe_coe, valAddEquiv_apply, Basis.coe_ofRepr, valLinearEquiv_symm_apply,
      Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Finsupp.mem_support_iff, ne_eq, ite_not,
      ite_smul, zero_smul, s]
    if hz' : z.val x = 0 then simp [hz'] else apply val_injective; simp [hz']
  have eq1' (τ : K ≃ₐ[F] K) : z = ∑ σ, s (τ⁻¹ * σ * τ) • ⟨Finsupp.single (τ⁻¹ * σ * τ) 1⟩ := by
    rw [eq1]
    fapply Finset.sum_bij
    · refine fun σ _ => τ * σ * τ⁻¹
    · intros; exact Finset.mem_univ _
    · rintro σ - σ' - h
      simpa using h
    · rintro σ -
      refine ⟨τ⁻¹ * σ * τ, Finset.mem_univ _, ?_⟩
      simp [← _root_.mul_assoc]
    · rintro σ -
      simp [← _root_.mul_assoc]

  have eq2 (d : K) (τ : K ≃ₐ[F] K) :
      z * ⟨.single τ d⟩ = ⟨.single τ d⟩ * z := hz ⟨.single τ d⟩ |>.symm
  have eq3 (d : K) (τ : K ≃ₐ[F] K) : z * ⟨.single τ d⟩ =
      ∑ σ, (s σ * (σ d) * f (σ, τ)) • ⟨.single (σ * τ) 1⟩ := by
    rw [eq1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [mul_assoc, s]
    apply val_injective
    simp only [val_mul, val_smul, Finsupp.smul_single, smul_eq_mul, mul_one,
      mulLinearMap_single_single, s, ← mul_assoc]

  have eq4 (d : K) (τ : K ≃ₐ[F] K) : ⟨.single τ d⟩ * z =
      ∑ σ, (d * τ (s (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ)) • ⟨.single (σ * τ) 1⟩ := by
    rw [eq1' τ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    apply val_injective
    simp [← mul_assoc, Prod.mk_one_one, Units.val_inv_eq_inv_val, mul_one,
      map_mul, map_inv₀, isUnit_iff_ne_zero, ne_eq, EmbeddingLike.map_eq_zero_iff,
      Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right, mul_inv_cancel, one_mul,
      map_one, AlgEquiv.one_apply]

  have eq5 (d : K) (τ : K ≃ₐ[F] K) :
      ∑ σ, (s σ * (σ d) * (f (σ, τ))) • (basis (f := f) (σ * τ)) =
      ∑ σ, (d * τ (s (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ)) • (basis (σ * τ)) := by
    conv_lhs => enter [2]; intro σ; rw [show basis (σ * τ) = ⟨.single (σ * τ) 1⟩ by rfl]
    conv_rhs => enter [2]; intro σ; rw [show basis (σ * τ) = ⟨.single (σ * τ) 1⟩ by rfl]
    rw [← eq3, ← eq4, ← eq2]

  let e (τ : K ≃ₐ[F] K) : (K ≃ₐ[F] K) ≃ (K ≃ₐ[F] K) :=
  { toFun σ := σ * τ⁻¹
    invFun σ := σ * τ
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

  let basis' (τ : K ≃ₐ[F] K) := basis (f := f).reindex (e τ)
  have eq5' (d : K) (τ : K ≃ₐ[F] K) :
      ∑ σ, (s σ * (σ d) * (f (σ, τ))) • (basis' τ σ) =
      ∑ σ, (d * τ (s (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ)) • (basis' τ σ) := by
    simp only [Basis.coe_reindex, Equiv.coe_fn_symm_mk, Function.comp_apply, basis,
      basis', e]
    simp_rw [basis] at eq5
    rw [eq5 d τ]

  have eq5'' (d : K) (τ : K ≃ₐ[F] K) :
      ∑ σ, (s σ * (σ d) * (f (σ, τ)) - d * τ (s (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ)) •
        (basis' τ σ) = 0:= by
    simp_rw [sub_smul, Finset.sum_sub_distrib]
    rw [eq5', sub_self]

  have EQ0 (d : K) (σ τ : K ≃ₐ[F] K) :
      s σ * (σ d) * (f (σ, τ)) = d * τ (s (τ⁻¹ * σ * τ)) * f (τ, τ⁻¹ * σ * τ) := by
    specialize eq5 d τ
    have EQ := (basis' τ).linearIndependent
    rw [Fintype.linearIndependent_iff] at EQ
    have EQ := EQ _ (eq5'' d _) σ
    rw [sub_eq_zero] at EQ
    rw [EQ]

  have EQ1 := EQ0 1
  simp only [map_one, _root_.mul_one, _root_.one_mul] at EQ1

  have EQ2 (d : K) (σ τ : K ≃ₐ[F] K) :
      s σ * (σ d) * (f (σ, τ)) = d * s σ * (f (σ, τ)) := by
    rw [EQ0, _root_.mul_assoc, ← EQ1, ← _root_.mul_assoc]

  have EQ3 (d : K) (σ : K ≃ₐ[F] K) (h : s σ ≠ 0) : σ d = d := by
    specialize EQ2 d σ 1
    rw [mul_comm (s σ) (σ d)] at EQ2
    simp only [mul_eq_mul_right_iff, Units.ne_zero, or_false] at EQ2
    exact EQ2.resolve_right h

  have conclusion1 (σ : K ≃ₐ[F] K) (h : σ ≠ 1) : s σ = 0 := by
    contrapose! h
    ext d
    exact EQ3 d σ h

  have conclusion2 (τ : K ≃ₐ[F] K) : τ (s 1 * f 1) = s 1 * f 1 := by
    rw [map_mul]
    specialize EQ0 1 1 τ
    simp only [AlgEquiv.one_apply, _root_.mul_one, inv_mul_cancel, _root_.one_mul,
      map_one_fst_of_isMulTwoCocycle Fact.out, map_one_snd_of_isMulTwoCocycle Fact.out,
      show ((1, 1) : Gal(K, F) × Gal(K, F)) = 1 by rfl, AlgEquiv.smul_units_def, Units.coe_map] at EQ0
    exact EQ0.symm

  have eq_bot := IsGalois.tfae (F := F) (E := K) |>.out 0 1 |>.1
    (inferInstance : IsGalois F K)

  apply_fun IntermediateField.toSubalgebra at eq_bot
  simp only [IntermediateField.bot_toSubalgebra] at eq_bot
  have conclusion3 : (s 1 * f 1) ∈ (⊥ : Subalgebra F K) := by
    rw [← eq_bot,IntermediateField.mem_toSubalgebra, IntermediateField.fixedField]
    rintro ⟨σ, -⟩
    exact conclusion2 σ
  rw [Algebra.mem_bot] at conclusion3

  rw [eq1]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  by_cases h : σ = 1
  · subst h

    rw [show (s 1 • { val := Finsupp.single 1 1 } : CrossProduct f) = ⟨s 1 • .single 1 1⟩ by rfl,
      Finsupp.smul_single, smul_eq_mul, mul_one,
      show (⟨.single 1 (s 1)⟩ : CrossProduct f) = ι f (s 1 * (f 1).1) by apply val_injective; simp,
      show ι f (s 1 * f 1) = (s 1 * f 1) • (1 : CrossProduct f) by apply val_injective; simp]
    obtain ⟨g, hg⟩ := conclusion3
    rw [← hg, show algebraMap F K g • (1 : CrossProduct f) = g • 1 by
      rw [Algebra.smul_def, algebraMap_smul, mul_one]
      apply val_injective;
      simp only [val_smul, val_one, Prod.mk_one_one, Finsupp.smul_single, algebraMap_val,
        Units.val_inv_eq_inv_val, basis', e, s]
      rw [← smul_eq_mul, algebraMap_smul]]
    apply Subalgebra.smul_mem _ (Subalgebra.one_mem ⊥)
  · specialize conclusion1 σ h
    rw [conclusion1]
    rw [zero_smul]
    exact Subalgebra.zero_mem _


-- instance : SMulCommClass K (CrossProduct f) (CrossProduct f) where
--   smul_comm k x y := by
--     apply val_injective
--     simp only [smul_eq_mul, val_smul, val_mul]
--     induction x.val using Finsupp.induction_linear with
--     | h0 => simp
--     | hadd f g _ _ => simp_all
--     | hsingle σ k1 =>
--       induction y.val using Finsupp.induction_linear with
--       | h0 => simp
--       | hadd f g _ _ => simp_all
--       | hsingle τ k2 =>
--         simp [Finsupp.smul_single]
--         congr 1
--         simp [← mul_assoc]
--         sorry
omit [Fact (IsMulTwoCocycle f)] [Module.Finite F K] [IsGalois F K] in
lemma unit_smul (u : Kˣ) (x : CrossProduct f) : u • x = u.1 • x := by rfl

omit [Module.Finite F K] [IsGalois F K] in
lemma identity_double_cross (σ : K ≃ₐ[F] K) (b : K) :
    ι f b * ⟨Finsupp.single σ 1⟩ = ⟨Finsupp.single σ b⟩ := by
  ext α
  simp [ι_apply, val_mul, val_smul, val_one, Finsupp.smul_single, smul_eq_mul,
    mulLinearMap_single_single, one_mul, AlgEquiv.one_apply, mul_one,
    map_one_fst_of_isMulTwoCocycle Fact.out]

omit [Module.Finite F K] [IsGalois F K] in
lemma singleUnit_conj (σ : K ≃ₐ[F] K) (c : K) : (singleUnit σ).1 * ι f c * (singleUnit σ)⁻¹.1 = ι f (σ c) := by
  have eq1 :=
    calc (singleUnit σ).1 * ι f c
    _ = ⟨Finsupp.single σ ((σ (c * (f (1, 1))⁻¹.1)) * (f (σ, 1)).1)⟩ := val_injective <| by simp
    _ = ⟨Finsupp.single σ (σ c)⟩ := val_injective <| by
      simp [Prod.mk_one_one, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
        map_one_snd_of_isMulTwoCocycle Fact.out]
  rw [eq1, ← identity_double_cross, mul_assoc]
  haveI : IsScalarTower K (CrossProduct f) (CrossProduct f) := {
    smul_assoc k x y := by simp only [smul_eq_mul, smul_eq_ι_mul, mul_smul, mul_assoc]}
  simp only [ι_apply, smul_one_mul]
  congr
  change (singleUnit σ).1 * _ = _
  simp

omit [Fact (IsMulTwoCocycle f)] [Module.Finite F K] [IsGalois F K] in
theorem basis_smul_comm (k : K) (b : CrossProduct f) (σ : K ≃ₐ[F] K):
    σ k • basis σ * b = basis σ * k • b := by
  apply val_injective
  simp [CrossProduct.basis]
  induction b.val using Finsupp.induction_linear with
  | h0 => simp
  | hadd f g _ _ => simp_all
  | hsingle τ a => simp

end CrossProduct
