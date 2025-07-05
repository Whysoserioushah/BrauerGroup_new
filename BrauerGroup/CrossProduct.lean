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
  one := ⟨.single 1 (f (1, 1))⁻¹⟩

instance : Mul (CrossProduct f) where
  mul x y := ⟨mulLinearMap f x.val y.val⟩

@[simp] lemma val_one : (1 : CrossProduct f).val = .single 1 (f (1, 1))⁻¹ := rfl
@[simp] lemma val_mul (x y : CrossProduct f) : (x * y).val = mulLinearMap f x.val y.val := rfl

variable [Fact <| IsMulTwoCocycle f]

instance monoid : Monoid (CrossProduct f) where
  one_mul := by
    rintro ⟨x⟩
    ext σ
    simp
    induction x using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [*]
    | hsingle x cx => simp [map_one_fst_of_isMulTwoCocycle Fact.out, mul_right_comm _ cx]
  mul_one := by
    rintro ⟨x⟩
    ext σ
    simp
    induction x using Finsupp.induction_linear with
    | h0 => simp
    | hadd => simp [*]
    | hsingle x cx => simp [map_one_snd_of_isMulTwoCocycle Fact.out]
  mul_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    ext σ
    simp
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
    congr 5
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

variable (f) in
@[simps]
def ι : K →ₐ[F] CrossProduct f where
  toFun a := ⟨.single 1 <| a * (f 1)⁻¹⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [add_mul]
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc, mul_left_comm]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

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
  ext : 1
  simp
  congr
  convert congr($((Fact.out : IsMulTwoCocycle f) 1 σ τ) * (f 1 : K)⁻¹) using 1
  · simp [map_one_fst_of_isMulTwoCocycle Fact.out]
  · simp [mul_right_comm]

variable [Module.Finite F K] [IsGalois F K]

@[simp] lemma finrank_eq_sq : Module.finrank F (CrossProduct f) = Module.finrank F K ^ 2 := by
  rw [← Module.finrank_mul_finrank _ K, Module.finrank_eq_card_basis basis,
    IsGalois.card_aut_eq_finrank, sq]

instance : Module.Finite F (CrossProduct f) :=
  Module.finite_of_finrank_pos <| by simp [pow_pos_iff two_ne_zero, Module.finrank_pos]

lemma center_eq_bot [IsGalois F K] : Subalgebra.center F (CrossProduct f) = ⊥ := by
  rw [← le_bot_iff]
  rintro z hz
  rw [Subalgebra.mem_center_iff] at hz
  set s : (K ≃ₐ[F] K) → K :=
    fun σ => if σ ∈ ((x_AsBasis ha).repr z).support then (x_AsBasis ha).repr z σ else 0

  have eq1 : z = ∑ σ : K ≃ₐ[F] K, s σ • ⟨Pi.single σ 1⟩ := by
    conv_lhs => rw [← (x_AsBasis ha).linearCombination_repr z, Finsupp.linearCombination_apply,
      Finsupp.sum]
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finsupp.mem_support_iff, ne_eq, not_not,
        true_and, Finsupp.if_mem_support, smul_eq_zero, s] at hx ⊢
      exact Or.inl hx
    intro x _
    simp only [x_AsBasis_apply, Finsupp.mem_support_iff, ne_eq, Finsupp.if_mem_support, s]
  have eq1' (τ : K ≃ₐ[F] K) : z = ∑ σ, s (τ⁻¹ * σ * τ) • ⟨Pi.single (τ⁻¹ * σ * τ) 1⟩ := by
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
      z * ⟨Pi.single τ d⟩ = ⟨Pi.single τ d⟩ * z := hz ⟨Pi.single τ d⟩ |>.symm
  have eq3 (d : K) (τ : K ≃ₐ[F] K) : z * ⟨Pi.single τ d⟩ =
      ∑ σ, (s σ * (σ d) * a (σ, τ)) • ⟨Pi.single (σ * τ) 1⟩ := by
    rw [eq1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [x_AsBasis_apply, smul_def, _root_.mul_assoc]
    apply val_injective ha
    simp only [mul_val, crossProductMul_single_single, _root_.one_mul, ι_apply_val, Prod.mk_one_one,
      Units.val_inv_eq_inv_val, AlgEquiv.one_apply, _root_.mul_one, Pi.single_inj]
    rw [a_one_left ha]
    field_simp

  have eq4 (d : K) (τ : K ≃ₐ[F] K) : ⟨Pi.single τ d⟩ * z =
      ∑ σ, (d * τ (s (τ⁻¹ * σ * τ)) * a (τ, τ⁻¹ * σ * τ)) • ⟨Pi.single (σ * τ) 1⟩ := by
    rw [eq1' τ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_def, smul_def]
    apply val_injective
    simp only [← _root_.mul_assoc, mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
      crossProductMul_single_single, _root_.mul_one, map_mul, map_inv₀, a_one_right' ha,
      isUnit_iff_ne_zero, ne_eq, EmbeddingLike.map_eq_zero_iff, Units.ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel_right, mul_inv_cancel, _root_.one_mul, map_one, AlgEquiv.one_apply,
      a_one_left ha, Pi.single_inj]
    field_simp
  have eq5 (d : K) (τ : K ≃ₐ[F] K) :
      ∑ σ, (s σ * (σ d) * (a (σ, τ))) • (x_AsBasis ha (σ * τ)) =
      ∑ σ, (d * τ (s (τ⁻¹ * σ * τ)) * a (τ, τ⁻¹ * σ * τ)) • (x_AsBasis ha (σ * τ)) := by
    simp_rw [x_AsBasis_apply]
    rw [← eq3, ← eq4, eq2]

  let e (τ : K ≃ₐ[F] K) : (K ≃ₐ[F] K) ≃ (K ≃ₐ[F] K) :=
  { toFun σ := σ * τ⁻¹
    invFun σ := σ * τ
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

  let basis' (τ : K ≃ₐ[F] K) := x_AsBasis ha |>.reindex (e τ)
  have eq5' (d : K) (τ : K ≃ₐ[F] K) :
      ∑ σ, (s σ * (σ d) * (a (σ, τ))) • (basis' τ σ) =
      ∑ σ, (d * τ (s (τ⁻¹ * σ * τ)) * a (τ, τ⁻¹ * σ * τ)) • (basis' τ σ) := by
    simp only [Basis.coe_reindex, Equiv.coe_fn_symm_mk, Function.comp_apply, x_AsBasis_apply,
      basis', e]
    simp_rw [x_AsBasis_apply] at eq5
    rw [eq5 d τ]

  have eq5'' (d : K) (τ : K ≃ₐ[F] K) :
      ∑ σ, (s σ * (σ d) * (a (σ, τ)) - d * τ (s (τ⁻¹ * σ * τ)) * a (τ, τ⁻¹ * σ * τ)) •
        (basis' τ σ) = 0:= by
    simp_rw [sub_smul, Finset.sum_sub_distrib]
    rw [eq5', sub_self]

  have EQ0 (d : K) (σ τ : K ≃ₐ[F] K) :
      s σ * (σ d) * (a (σ, τ)) = d * τ (s (τ⁻¹ * σ * τ)) * a (τ, τ⁻¹ * σ * τ) := by
    specialize eq5 d τ
    have EQ := (basis' τ).linearIndependent
    rw [Fintype.linearIndependent_iff] at EQ
    have EQ := EQ _ (eq5'' d _) σ
    rw [sub_eq_zero] at EQ
    rw [EQ]

  have EQ1 := EQ0 1
  simp only [map_one, _root_.mul_one, _root_.one_mul] at EQ1

  have EQ2 (d : K) (σ τ : K ≃ₐ[F] K) :
      s σ * (σ d) * (a (σ, τ)) = d * s σ * (a (σ, τ)) := by
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

  have conclusion2 (τ : K ≃ₐ[F] K) : τ (s 1 * a 1) = s 1 * a 1 := by
    rw [map_mul]
    specialize EQ0 1 1 τ
    simp only [AlgEquiv.one_apply, _root_.mul_one, a_one_left ha, inv_mul_cancel, _root_.one_mul,
      a_one_right' ha] at EQ0
    exact EQ0.symm

  have eq_bot := IsGalois.tfae (F := F) (E := K) |>.out 0 1 |>.1
    (inferInstance : IsGalois F K)

  apply_fun IntermediateField.toSubalgebra at eq_bot
  simp only [IntermediateField.bot_toSubalgebra] at eq_bot
  have conclusion3 : (s 1 * a 1) ∈ (⊥ : Subalgebra F K) := by
    rw [← eq_bot,IntermediateField.mem_toSubalgebra, IntermediateField.fixedField]
    rintro ⟨σ, -⟩
    exact conclusion2 σ
  rw [Algebra.mem_bot] at conclusion3

  rw [eq1]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  by_cases h : σ = 1
  · subst h

    rw [smul_single, _root_.mul_one, show (⟨Pi.single 1 (s 1)⟩ : CrossProduct a) =
      ι ha (s 1 * a 1) by apply val_injective ha; simp,
      show ι ha (s 1 * a 1) = (s 1 * a 1) • (1 : CrossProduct a) by
        rw [smul_def];  apply val_injective ha; simp]
    obtain ⟨f, hf⟩ := conclusion3
    rw [← hf, show algebraMap F K f • (1 : CrossProduct a) = f • 1 by
      rw [Algebra.smul_def]
      simp only [algebraMap_smul, algebraMap_val, _root_.mul_one]]
    apply Subalgebra.smul_mem _ (Subalgebra.one_mem ⊥)
  · specialize conclusion1 σ h
    rw [conclusion1]
    rw [zero_smul]
    exact Subalgebra.zero_mem _

end CrossProduct
