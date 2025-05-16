import BrauerGroup.GoodRep

suppress_compilation

open FiniteDimensional BrauerGroup groupCohomology

variable {F K : Type} [Field K] [Field F] [Algebra F K] (X : BrauerGroup (K := F))
variable {a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ} (σ τ : K ≃ₐ[F] K)

instance : DecidableEq (K ≃ₐ[F] K) := Classical.decEq _

@[ext]
structure CrossProduct (a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) where
  /-- The underlying element of the Galois group. -/
  val : (K ≃ₐ[F] K) → K

namespace CrossProduct

/-- `CrossProduct.val` as an `Equiv`. -/
@[simps!] def valEquiv : CrossProduct a ≃ ((K ≃ₐ[F] K) → K) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

lemma val_injective : Function.Injective (val (a := a)) := valEquiv.injective

instance : AddCommGroup (CrossProduct a) := valEquiv.addCommGroup

@[nolint unusedArguments] -- We assume `IsScalarTower R F K` to avoid a diamond when `R := K`.
instance {R : Type*} [Semiring R] [Module R F] [Module R K] [IsScalarTower R F K] :
    Module R (CrossProduct a) := valEquiv.module R

@[simp] lemma zero_val : (0 : CrossProduct a).val = 0 := rfl
@[simp] lemma neg_val (x : CrossProduct a) : (-x).val = -x.val := rfl
@[simp] lemma add_val (x y : CrossProduct a) : (x + y).val = x.val + y.val := rfl
@[simp] lemma sub_val (x y : CrossProduct a) : (x - y).val = x.val - y.val := rfl

@[simp] lemma smul_val {R : Type*} [Semiring R] [Module R F] [Module R K] [IsScalarTower R F K]
    (r : R) (x : CrossProduct a) : (r • x).val = r • x.val := rfl

@[simps!] def valLinearEquiv : CrossProduct a ≃ₗ[F] ((K ≃ₐ[F] K) → K) := valEquiv.linearEquiv F

instance : One (CrossProduct a) where one.val := Pi.single 1 (a (1, 1))⁻¹

@[simp] lemma one_val : (1 : CrossProduct a).val = Pi.single (1 : K ≃ₐ[F] K) (a (1, 1))⁻¹ := rfl

variable [FiniteDimensional F K]

@[elab_as_elim]
lemma single_induction (x : CrossProduct a) {motive : CrossProduct a → Prop}
    (single : ∀ (σ : K ≃ₐ[F] K) (c : K), motive ⟨Pi.single σ c⟩)
    (add : ∀ x y, motive x → motive y → motive ⟨x.val + y.val⟩)
    (zero : motive ⟨0⟩) : motive x := by
  have : x = ∑ σ : K ≃ₐ[F] K, ⟨Pi.single σ (x.val σ)⟩ := by
    ext σ
    change valLinearEquiv _ _ = valLinearEquiv _ _
    rw [map_sum]
    simp only [valLinearEquiv_apply, Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ,
      ↓reduceIte]
  rw [this]
  apply Finset.sum_induction
  · apply add
  · apply zero
  · intros σ _
    apply single

variable (a) in
def mulLinearMap : ((K ≃ₐ[F] K) → K) →ₗ[F] ((K ≃ₐ[F] K) → K) →ₗ[F] ((K ≃ₐ[F] K) → K) :=
  .flip <| .lsum F _ F fun σ ↦ .flip <| .lsum F _ F fun τ ↦ (LinearMap.toSpanSingleton _ _
    (.single F _ (τ * σ) ∘ₗ (a (τ, σ) • τ.toLinearMap))).restrictScalars _

@[simp]
lemma mulLinearMap_single_single (c d : K) :
    mulLinearMap a (Pi.single σ c) (Pi.single τ d) = Pi.single (σ * τ) (c * σ d * a (σ, τ)) := by
  classical
  ext γ
  have : c * a (σ, τ) • σ d = c * σ d * ↑(a (σ, τ)) := by simp [Units.smul_def]; ring
  simp [mulLinearMap, Pi.single_apply, apply_ite (_ : K ≃ₐ[F] K),
    ite_ite_distrib_right (p := _ = _ * _), this]

-- @[simp]
-- lemma crossProductSMul_single (r : F) (c : K) [DecidableEq (K ≃ₐ[F] K)] :
--     crossProductSMul r (Pi.single σ c) = Pi.single σ (r • c) := by
--   simp only [crossProductSMul, LinearMap.lsum_apply, LinearMap.coe_mk, AddHom.coe_mk,
--     LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
--     Function.comp_apply, Function.eval]

--   rw [show (Pi.single σ (r • c) : (K ≃ₐ[F] K) → K) =
--     Function.update (0 : (K ≃ₐ[F] K) → K) σ (r • (Pi.single σ c : (K ≃ₐ[F] K) → K) σ) by
--     aesop]
--   apply Finset.sum_eq_single_of_mem (h := by simp)
--   intros
--   aesop

instance : _root_.Mul (CrossProduct a) where mul x y := ⟨mulLinearMap a x.val y.val⟩

@[simp] lemma mul_val (x y : CrossProduct a) : (x * y).val = mulLinearMap a x.val y.val := rfl

lemma mul_def (x y : CrossProduct a) : x * y = ⟨mulLinearMap a x.val y.val⟩ := rfl

section galois

variable {X : BrauerGroup (K := F)} (A : GoodRep K X)

lemma conjFactor_linearIndependent (x_ : Π σ, A.conjFactor σ) :
    LinearIndependent K fun i : K ≃ₐ[F] K ↦ (x_ i).1.1 := by
  classical
  by_contra! rid
  obtain ⟨J, LI, maximal⟩ := exists_maximal_linearIndepOn K (fun (i : K ≃ₐ[F] K) => (x_ i).1.1)
  have ne : J ≠ Set.univ := by
    rintro rfl
    refine rid ?_
    let e : (Set.univ : Set (K ≃ₐ[F] K)) ≃ (K ≃ₐ[F] K) := Equiv.Set.univ (K ≃ₐ[F] K)
    have := linearIndependent_equiv e.symm |>.2 LI
    exact this
  rw [Set.ne_univ_iff_exists_not_mem] at ne
  obtain ⟨σ, hσ⟩ := ne

  obtain ⟨c, c_ne_zero, hc⟩ := maximal σ hσ
  let B := Basis.span LI
  replace hc := Submodule.smul_mem _ c⁻¹ hc
  rw [← mul_smul, inv_mul_cancel₀ c_ne_zero, one_smul] at hc
  clear c c_ne_zero
  have mem1 : (x_ σ).1.1 ∈ Submodule.span K (Set.range fun (σ : J) ↦ (x_ σ.1).1.1) := by
    convert hc; aesop
  have eq0 : (⟨(x_ σ).1.1, mem1⟩ : Submodule.span K (Set.range fun (σ : J) ↦ (x_ σ.1).1.1)) =
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support, B.repr ⟨_, mem1⟩ τ • (x_ τ).1.1 := by
    conv_lhs => rw [← B.linearCombination_repr ⟨(x_ σ).1.1, mem1⟩, Finsupp.linearCombination_apply,
      Finsupp.sum]
    rw [AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SetLike.val_smul]
    congr 1
    simp only [B, Basis.span_apply]

  simp only [Submodule.coe_subtype, map_sum, map_smul] at eq0
  have eq1 (c : K) := calc A.ι (σ c) * (x_ σ).1.1
      _ = (x_ σ).1.1 * A.ι c := by
        rw [(x_ σ).2 c]; simp [_root_.mul_assoc]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ) * (x_ τ).1.1 * A.ι c := by
        conv_lhs => rw [eq0, Finset.sum_mul]

      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ) * A.ι (τ.1 c) * (x_ τ).1.1 :=
        Finset.sum_congr rfl fun i _ => by
        simp only [_root_.mul_assoc]
        congr 1
        rw [(x_ i).2 c]
        simp [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ * τ.1 c) * (x_ τ).1.1 :=
        Finset.sum_congr rfl fun i _ => by rw [map_mul]
  have eq2 (c : K) := calc A.ι (σ c) * (x_ σ).1.1
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          A.ι (σ c * (B.repr ⟨_, mem1⟩) τ) * (x_ τ).1.1 := by
        conv_lhs => rw [eq0, Finset.mul_sum]
        simp_rw [map_mul, _root_.mul_assoc, GoodRep.smul_def]
  have eq3 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ * τ.1 c) * (x_ τ).1.1 =
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          A.ι (σ c * (B.repr ⟨_, mem1⟩) τ) * (x_ τ).1.1 :=
    eq1 c |>.symm.trans <| eq2 c
  have eq4 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          A.ι (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ) * (x_ τ).1.1 = 0 := by
    simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
    simp only [← map_mul, eq3, sub_self]

  have eq5 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ) • (x_ τ).1.1 = 0 := by
    rw [← eq4]
    rfl


  have eq6 (c : K) := linearIndependent_iff'' |>.1 LI (B.repr ⟨_, mem1⟩).support
    (fun τ => B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ)
    (by
      intro i hi
      simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hi
      simp only [hi, zero_mul, mul_zero, sub_self]) (eq5 c)
  simp only [sub_eq_zero, Subtype.forall] at eq6
  have : (B.repr ⟨_, mem1⟩).support ≠ ∅ := by
    intro rid
    simp only [rid, Finset.sum_empty, Units.ne_zero] at eq0
  obtain ⟨τ, τ_mem⟩ := Finset.nonempty_of_ne_empty this
  have eq7 : σ = τ := by
    ext c
    specialize eq6 c τ τ.2
    rw [mul_comm] at eq6
    simp only [Subtype.coe_eta, mul_eq_mul_right_iff] at eq6
    refine eq6.recOn Eq.symm fun rid => ?_
    simp only [Finsupp.mem_support_iff, ne_eq] at τ_mem
    contradiction

  subst eq7
  exact hσ τ.2

variable [FiniteDimensional F K]

variable [IsGalois F K] in

def conjFactorBasis (x_ : Π σ, A.conjFactor σ) : Basis (K ≃ₐ[F] K) K A :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun (i : K ≃ₐ[F] K) => (x_ i).1.1)
    (A.conjFactor_linearIndependent x_)
    (by rw [A.dim_eq', IsGalois.card_aut_eq_finrank])

open DirectSum

attribute [local simp] mul_def in
instance monoid : Monoid (CrossProduct a) where
  mul_assoc x y z := by
    ext α
    induction x using single_induction ha with
    | single x cx =>
      induction y using single_induction ha with
      | single y cy =>
        induction z using single_induction ha with
        | single z cz =>
          simp only [mul_def, mulLinearMap_single_single, AlgEquiv.mul_apply, ← _root_.mul_assoc,
            map_mul]
          congr 1
          simp only [_root_.mul_assoc]
          congr 2
          rw [← _root_.mul_assoc, mul_comm _ (x _), _root_.mul_assoc]
          congr 1
          have := congr($(ha x y z).1)
          simp only [Units.val_mul, AlgEquiv.smul_units_def, Units.coe_map,
            MonoidHom.coe_coe] at this
          rw [mul_comm] at this
          exact this
        | add z z' hz hz' =>
          simp only [mul_def, mulLinearMap_single_single, map_add, Pi.add_apply] at hz hz' ⊢
          simp only [hz, hz']
        | zero => simp
      | add y y' hy hy' =>
        simp only [mul_def, map_add, LinearMap.add_apply, Pi.add_apply] at hy hy' ⊢
        simp only [hy, hy']
      | zero => simp
    | add x x' hx hx' =>
      simp only [mul_def, map_add, LinearMap.add_apply, Pi.add_apply] at hx hx' ⊢
      simp only [hx, hx']
    | zero => simp
  one_mul x := by
    ext α
    induction x using single_induction ha with
    | single x cx =>
      simp only [mul_def, one_val, Prod.mk_one_one, mulLinearMap_single_single, _root_.one_mul,
        AlgEquiv.one_apply]
      congr 1
      have eq1 := ha 1 1 x
      simp only [_root_.mul_one, Prod.mk_one_one, one_smul, _root_.one_mul, mul_right_inj] at eq1
      replace eq1 := congr($eq1.1)
      rw [eq1, mul_comm _ cx]
      simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_right]
    | add x x' hx hx' =>
      simp only [mul_def, map_add, LinearMap.add_apply, Pi.add_apply] at hx hx' ⊢
      simp only [hx, hx']
    | zero => simp
  mul_one x := by
    ext α
    induction x using single_induction ha with
    | single x cx =>
      simp only [mul_def, one_val, Prod.mk_one_one, mulLinearMap_single_single, _root_.mul_one,
        map_inv₀]
      congr 1
      have eq1 := ha x 1 1
      simp only [_root_.mul_one, Prod.mk_one_one, AlgEquiv.smul_units_def, mul_left_inj] at eq1
      replace eq1 := congr($eq1.1)
      simp only [Units.coe_map, MonoidHom.coe_coe] at eq1
      rw [← eq1,_root_.mul_assoc]
      simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
        _root_.mul_one]
    | add x x' hx hx' =>
      simp only [mul_def, map_add, LinearMap.add_apply, Pi.add_apply] at hx hx' ⊢
      simp only [hx, hx']
    | zero => simp

instance : Ring (CrossProduct a) where
  __ := addCommGroup ha
  __ := monoid ha
  left_distrib := by intros; ext; simp
  right_distrib := by intros; ext; simp
  zero_mul := by intros; ext; simp
  mul_zero := by intros; ext; simp
  sub_eq_add_neg := by intros; ext; simp only [sub_val, Pi.sub_apply, add_val, neg_val,
    Pi.add_apply, Pi.neg_apply]; group
  neg_add_cancel := by intros; ext; simp

instance : SMul F (CrossProduct a) where
  smul r x := ⟨crossProductSMul r x.1⟩

@[simp]
lemma smul_val (r : F) (x : CrossProduct a) :
    (r • x).val = crossProductSMul r x.val := rfl

instance algebra : Algebra F (CrossProduct a) where
  algebraMap := {
    toFun r := r • 1
    map_one' := by
      ext α
      simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single, one_smul]
    map_mul' := by
      intro r r'
      ext α
      simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single, mul_smul, mul_val,
        mulLinearMap_single_single, map_smul, map_inv₀, AlgEquiv.one_apply, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_right]
      congr 1
      rw [smul_comm]
    map_zero' := by
      ext; simp
    map_add' := by
      intro r r'
      ext α
      simp only [smul_val, map_add, one_val, Prod.mk_one_one, LinearMap.add_apply,
        crossProductSMul_single, Pi.add_apply, add_val]
  }
  commutes' := by
    intro r x
    ext α
    simp only [one_val, Prod.mk_one_one, crossProductSMul_single, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, mul_val]
    induction x using single_induction ha with
    | single x cx =>
      simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single,
        mulLinearMap_single_single, AlgEquiv.one_apply, Algebra.smul_mul_assoc, map_smul,
        map_inv₀, Algebra.mul_smul_comm]
      rw [_root_.one_mul, _root_.mul_one]
      congr 2
      have eq1 := ha x 1 1
      simp only [_root_.mul_one, Prod.mk_one_one, AlgEquiv.smul_units_def, mul_left_inj] at eq1
      replace eq1 := congr($eq1.1)
      simp only [Units.coe_map, MonoidHom.coe_coe] at eq1
      rw [← eq1]
      simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_right]
      have eq2 := ha 1 1 x
      simp only [_root_.mul_one, Prod.mk_one_one, one_smul, _root_.one_mul, mul_right_inj] at eq2
      rw [congr($eq2.1), mul_comm _ cx]
      simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_right]
    | add x x' hx hx' =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply] at hx hx' ⊢
      simp only [hx, hx']
    | zero => simp
  smul_def' := by
    intro r x
    ext α
    simp only [one_val, Prod.mk_one_one, crossProductSMul_single, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, mul_val]
    induction x using single_induction ha with
    | single x cx =>
      simp only [smul_val, crossProductSMul_single, one_val, Prod.mk_one_one,
        mulLinearMap_single_single, AlgEquiv.one_apply, Algebra.smul_mul_assoc]
      rw [_root_.one_mul]
      congr 2
      have eq2 := ha 1 1 x
      simp only [_root_.mul_one, Prod.mk_one_one, one_smul, _root_.one_mul, mul_right_inj] at eq2
      rw [congr($eq2.1), mul_comm _ cx]
      simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_right]
    | add x x' hx hx' =>
      simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single, map_add,
        Pi.add_apply] at hx hx' ⊢
      simp only [hx, hx']
    | zero => simp

@[simp]
lemma algebraMap_val (r : F) :
    algebraMap F (CrossProduct a) r = r • 1 := rfl

def ι : K →ₐ[F] CrossProduct a where
  toFun b := ⟨Pi.single 1 (b * (a (1, 1))⁻¹)⟩
  map_one' := by
    ext α
    simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, _root_.one_mul, one_val]
  map_mul' := by
    intro b b'
    ext α
    simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, mul_val, mulLinearMap_single_single,
      AlgEquiv.one_apply]
    rw [_root_.mul_one]
    congr 1
    simp only [_root_.mul_assoc]
    congr 1
    rw [mul_comm b']
    congr 1
    simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
      _root_.mul_one]
  map_zero' := by
    ext α; simp
  map_add' := by
    intro b b'
    ext α
    simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, add_mul, Pi.single_apply, add_val,
      Pi.add_apply]
    split_ifs with h <;> aesop
  commutes' := by
    intro r
    ext α
    simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, algebraMap_val, smul_val, one_val,
      crossProductSMul_single]
    congr 1
    rw [Algebra.smul_def]

@[simp]
lemma ι_apply_val (b : K) :
    (ι ha b).val = Pi.single 1 (b * (a (1, 1))⁻¹) := rfl

include ha in
 (K ≃ₐ[F] K)] in
@[simp] lemma a_one_left : a (1, σ) = a 1 := by
  have := ha 1 1 σ
  simp only [_root_.mul_one, Prod.mk_one_one, one_smul, _root_.one_mul, mul_right_inj] at this
  exact this.symm

include ha in
 (K ≃ₐ[F] K)] in
lemma a_one_right : a (σ, 1) = Units.map σ (a 1) := by
  have := ha σ 1 1
  simp only [_root_.mul_one, Prod.mk_one_one, AlgEquiv.smul_units_def, mul_left_inj] at this
  exact this

include ha in
 (K ≃ₐ[F] K)] in
lemma a_one_right' : (a (σ, 1)).1 = σ (a 1) := congr($(a_one_right ha σ).1)

lemma identity_double_cross (b : K) :
    ι ha b * ⟨Pi.single σ 1⟩ = ⟨Pi.single σ b⟩ := by
  ext α
  simp only [mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    mulLinearMap_single_single, AlgEquiv.one_apply, _root_.mul_one]
  rw [_root_.one_mul]
  congr 1
  rw [a_one_left ha]
  simp

lemma identity_double_cross' (b c : K) :
    ι ha b * ⟨Pi.single σ c⟩ = ⟨Pi.single σ (b*c)⟩ := by
  ext α
  simp only [mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    mulLinearMap_single_single, AlgEquiv.one_apply]
  rw [_root_.one_mul]
  congr 1
  rw [a_one_left ha]
  field_simp

@[simps]
def Units.ofLeftRightInverse (G : Type*) [Monoid G] (a b c : G) (h : a * b = 1) (h' : c * a = 1) : Gˣ where
  val := a
  inv := b
  val_inv := h
  inv_val := by simpa [left_inv_eq_right_inv h' h] using h'

lemma Units.ofLeftRightInverse_inv_eq1 (G : Type*) [Monoid G] (a b c : G) (h : a * b = 1) (h' : c * a = 1) :
    (Units.ofLeftRightInverse G a b c h h').inv = b := rfl

lemma Units.ofLeftRightInverse_inv_eq2 (G : Type*) [Monoid G] (a b c : G) (h : a * b = 1) (h' : c * a = 1) :
    (Units.ofLeftRightInverse G a b c h h').inv = c := by simp [left_inv_eq_right_inv h' h]

def x_ (σ : K ≃ₐ[F] K) : (CrossProduct a)ˣ :=
  Units.ofLeftRightInverse (CrossProduct a) ⟨Pi.single σ 1⟩
    ⟨Pi.single σ⁻¹ ((σ⁻¹ ((a (σ, σ⁻¹))⁻¹ * (a 1)⁻¹)))⟩
    ⟨Pi.single σ⁻¹ ((a (σ⁻¹, σ))⁻¹ * (a 1)⁻¹)⟩
    (by
      let x_σ : (CrossProduct a) := ⟨Pi.single σ 1⟩
      have eq1 (b : K) := calc x_σ * ⟨Pi.single σ⁻¹ b⟩
          _ = ⟨Pi.single σ 1⟩ * ⟨Pi.single σ⁻¹ b⟩ := rfl
          _ = ⟨Pi.single 1 (σ b * a (σ, σ⁻¹))⟩ := by
              ext α
              simp only [mul_val, mulLinearMap_single_single, _root_.one_mul]
              rw [mul_inv_cancel]
      specialize eq1 (σ⁻¹ ((a (σ, σ⁻¹))⁻¹ * (a 1)⁻¹))
      conv_rhs at eq1 => erw [Equiv.apply_symm_apply]
      conv_rhs at eq1 => rw [mul_comm _ (a 1)⁻¹.1, _root_.mul_assoc]

      convert eq1 using 1
      ext α
      simp only [mul_val, mulLinearMap_single_single, map_one, _root_.mul_one, _root_.one_mul,
        map_mul, map_inv₀]
      simp)
    (by
      let x_σ : (CrossProduct a) := ⟨Pi.single σ 1⟩
      have eq2 (b : K) := calc  ⟨Pi.single σ⁻¹ b⟩ * x_σ
          _ = ⟨Pi.single 1 (b * a (σ⁻¹, σ))⟩ := by
              ext α
              rw [mul_val, mulLinearMap_single_single, map_one,
                _root_.mul_one]
              rw [inv_mul_cancel]
      specialize eq2  ((a 1)⁻¹ * (a (σ⁻¹, σ))⁻¹)
      simp only [Units.val_inv_eq_inv_val, isUnit_iff_ne_zero, ne_eq, Units.ne_zero,
        not_false_eq_true, IsUnit.inv_mul_cancel_right] at eq2
      change _ = 1 at eq2
      rw [← eq2]
      congr! 3
      rw [mul_comm]
      simp only [Units.val_inv_eq_inv_val])

set_option linter.style.nameCheck false in
@[simp]
lemma x__val (σ : K ≃ₐ[F] K) :
    (x_ ha σ).val.val = Pi.single σ 1 := rfl

set_option linter.style.nameCheck false in
lemma x__inv (σ : K ≃ₐ[F] K) :
    (x_ ha σ).inv.val = Pi.single σ⁻¹ ((σ⁻¹ ((a (σ, σ⁻¹))⁻¹ * (a 1)⁻¹)) : K) := rfl

set_option linter.style.nameCheck false in
lemma x__inv' (σ : K ≃ₐ[F] K) :
    (x_ ha σ).inv.1 = Pi.single σ⁻¹ ((a (σ⁻¹, σ))⁻¹ * (a 1)⁻¹) := by
  delta x_
  rw [Units.ofLeftRightInverse_inv_eq2]
  simp

set_option linter.style.nameCheck false in
lemma x__mul : x_ ha σ * x_ ha τ = ι ha (a (σ, τ)) * x_ ha (σ * τ) := by
  ext α
  simp only [mul_val, x__val, mulLinearMap_single_single, ι_apply_val, Prod.mk_one_one,
    Units.val_inv_eq_inv_val, AlgEquiv.one_apply]
  rw [_root_.one_mul]
  congr 1
  simp only [map_one, _root_.one_mul, _root_.mul_one]
  rw [a_one_left ha]
  simp

set_option linter.style.nameCheck false in
lemma x__conj (c : K) : x_ ha σ * ι ha c * (x_ ha σ)⁻¹ = ι ha (σ c) := by
  have eq1 :=
    calc (x_ ha σ) * (ι ha) c
    _ = ⟨Pi.single σ (σ (c * (a (1, 1))⁻¹) * (a (σ, 1)))⟩ := val_injective ha <| by
        simp
    _ = ⟨Pi.single σ (σ c)⟩ := val_injective ha <| by
        simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Pi.single_inj]
        rw [a_one_right' ha σ]
        simp
  rw [eq1]
  rw [← identity_double_cross ha σ (σ c)]
  rw [_root_.mul_assoc]
  change _ * ((x_ ha σ).1 * _) = _
  simp

set_option linter.style.nameCheck false in
lemma x__conj' (c : K) : x_ ha σ * ι ha c = ι ha (σ c) * (x_ ha σ) := by
  rw [← x__conj]
  simp only [Units.inv_mul_cancel_right]

instance module : Module K (CrossProduct a) where
  smul c x := ι ha c * x
  one_smul := by intros; show _ * _ = _; simp
  mul_smul := by intros; show _ * _ = _ * (_ * _); simp [_root_.mul_assoc]
  smul_zero := by intros; show _ * _ = _; simp
  smul_add := by intros; show _ * _ = _ * _ + _ * _; simp [mul_add]
  add_smul := by intros; show _ * _ = _ * _ + _ * _; simp [add_mul]
  zero_smul := by intros; show _ * _ = _; simp

lemma smul_def (c : K) (x : CrossProduct a) :
    c • x = ι ha c * x := rfl

lemma smul_single (c d : K) (σ : K ≃ₐ[F] K) :
    c • (⟨Pi.single σ d⟩ : CrossProduct a) = ⟨Pi.single σ (c * d)⟩ := by
  apply val_injective ha
  simp only [smul_def, mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    mulLinearMap_single_single, _root_.one_mul, AlgEquiv.one_apply, a_one_left ha, Pi.single_inj]
  rw [show ∀ (a b c d : K), a * b * c * d = (a * c) * (b * d) by intros; ring]
  simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
    _root_.mul_one]

def x_AsBasis : Basis (K ≃ₐ[F] K) K (CrossProduct a) :=
.mk (v σ := (x_ ha σ).1)
  (by
    rw [linearIndependent_iff']
    intro J f hf σ hσ
    replace hf : ∑ i ∈ J, ι ha (f i) * (x_ ha i).val = (0 : CrossProduct a) := hf
    replace hf : ∑ i ∈ J, ⟨Pi.single i (f i)⟩ = (0 : CrossProduct a) := by
      rw [← hf]
      exact Finset.sum_congr rfl fun i _ => identity_double_cross ha i (f i) |>.symm
    apply_fun valLinearEquiv at hf
    replace hf := congr_fun hf σ
    simp only [map_sum, Finset.sum_apply, map_zero, Pi.zero_apply] at hf
    simp only [valLinearEquiv_apply, Finset.sum_pi_single, ite_eq_right_iff] at hf
    exact hf hσ)
  (by
    rintro x -
    induction x using single_induction ha with
    | single x cx =>
      have eq : (⟨Pi.single x cx⟩ : CrossProduct a) = cx • ⟨Pi.single x 1⟩ := by
        change _ = ι ha _ * _
        rw [identity_double_cross]
      rw [eq]
      refine Submodule.smul_mem _ _ <| Submodule.subset_span ⟨x, rfl⟩
    | add x x' hx hx' =>
      exact Submodule.add_mem _ hx hx'
    | zero =>
      exact Submodule.zero_mem _)

instance : IsScalarTower F K (CrossProduct a) where
  smul_assoc := by
    intros x y z
    change ι ha (x • y) * z = x • (_ * _)
    ext α
    simp only [map_smul, Algebra.smul_mul_assoc, smul_val, mul_val, ι_apply_val, Prod.mk_one_one,
      Units.val_inv_eq_inv_val]

@[simp]
lemma x_AsBasis_apply (σ : K ≃ₐ[F] K) :
    x_AsBasis ha σ = ⟨Pi.single σ 1⟩ := by simp [x_AsBasis, x_]

lemma one_in_x_AsBasis :
    (1 : CrossProduct a) = (a (1, 1))⁻¹ • x_AsBasis ha 1 := by
  apply val_injective ha
  erw [smul_def]
  simp only [one_val, Prod.mk_one_one, Units.val_inv_eq_inv_val, x_AsBasis_apply, mul_val,
    ι_apply_val, mulLinearMap_single_single, _root_.mul_one, AlgEquiv.one_apply,
    isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right]

lemma single_in_xAsBasis (c : K) (σ : K ≃ₐ[F] K) :
    ⟨Pi.single σ c⟩ = c • x_AsBasis ha σ := by
  apply val_injective ha
  simp only [x_AsBasis_apply, smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
    Units.val_inv_eq_inv_val, mulLinearMap_single_single, _root_.one_mul, AlgEquiv.one_apply,
    _root_.mul_one, a_one_left ha, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
    IsUnit.inv_mul_cancel_right]

lemma mul_single_in_xAsBasis (c d : K) (σ τ : K ≃ₐ[F] K) :
    ⟨Pi.single σ c⟩ * ⟨Pi.single τ d⟩ = (c * σ d * a (σ, τ)) • x_AsBasis ha (σ * τ) := by
  apply val_injective ha
  simp only [mul_val, mulLinearMap_single_single, x_AsBasis_apply, smul_def, map_mul,
    ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val, _root_.mul_one, AlgEquiv.one_apply,
    map_inv₀, _root_.one_mul, a_one_left ha, Pi.single_inj]

  simp only [_root_.mul_assoc]
  congr 1
  simp only [← _root_.mul_assoc]
  simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
    IsUnit.inv_mul_cancel_right]
  field_simp

lemma x_AsBasis_conj' (c : K) : x_AsBasis ha σ * ι ha c = (σ c) • (x_AsBasis ha σ) := by
  have := x__conj' ha σ c
  convert this using 1 <;>
  simp [x_, smul_def]

lemma x_AsBasis_conj'' (c : K) : x_AsBasis ha σ * ι ha c = (ι ha <| σ c) * (x_AsBasis ha σ) :=
  x_AsBasis_conj' ha σ c


lemma dim_eq_square [IsGalois F K] : Module.finrank F (CrossProduct a) =
    (Module.finrank F K)^2 := by
  have eq1 : Module.finrank F (CrossProduct a) = Module.finrank F K *
      Module.finrank K (CrossProduct a) := by
    rw [Module.finrank_mul_finrank]
  rw [Module.finrank_eq_card_basis (x_AsBasis ha), IsGalois.card_aut_eq_finrank] at eq1
  rw [eq1, pow_two]

lemma one_def : (1 : CrossProduct a) = (a 1).1⁻¹ • x_AsBasis ha 1 := by
  ext1
  simp only [one_val, Prod.mk_one_one, x_AsBasis_apply, smul_def, mul_val, ι_apply_val,
    Units.val_inv_eq_inv_val, mulLinearMap_single_single, _root_.mul_one, AlgEquiv.one_apply,
    isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right]

set_option linter.style.nameCheck false in
lemma x__conj'' (c : K) : x_AsBasis ha σ * ι ha c = (σ c) • (x_AsBasis ha σ) := by
  simpa using x__conj' ha σ c

lemma x_AsBasis_mul : x_AsBasis ha σ * x_AsBasis ha τ = (a (σ, τ)).1 • x_AsBasis ha (σ * τ) := by
  have := x__mul ha σ τ
  simp only [x_, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Units.val_ofLeftRightInverse,
    mul_inv_rev, AlgEquiv.mul_apply, x_AsBasis_apply] at this ⊢
  rw [this, smul_def]

lemma is_central [IsGalois F K] : Subalgebra.center F (CrossProduct a) ≤ ⊥ := by
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
    simp only [mul_val, mulLinearMap_single_single, _root_.one_mul, ι_apply_val, Prod.mk_one_one,
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
      mulLinearMap_single_single, _root_.mul_one, map_mul, map_inv₀, a_one_right' ha,
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
  { toFun σ :==> σ * τ⁻¹
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

instance : Nontrivial (CrossProduct a) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have := congr($(h).val 1)
    simp only [zero_val, Pi.zero_apply, one_val, Prod.mk_one_one, Pi.single_eq_same,
      zero_eq_inv] at this
    exact Units.ne_zero _ this.symm⟩

namespace is_simple_proofs

variable (I : TwoSidedIdeal (CrossProduct a))
variable {ha}

def π : (CrossProduct a) →+* RingCon.Quotient I.ringCon := I.ringCon.mk'

def πRes : (ι ha).range →+* I.ringCon.Quotient :=
  RingHom.domRestrict (π I) (ι ha).range

variable {I} in
def x : (πRes I).range → K x := x.2.choose.2.choose

lemma hx (a : πRes I |>.range) : πRes I ⟨ι ha (x a), by simp⟩ = a := by
  rw [← a.2.choose_spec]
  congr 1
  ext : 1
  exact a.2.choose.2.choose_spec

lemma hx' (a : K) : πRes I ⟨ι ha a, by simp⟩ = I.ringCon.mk' (ι ha a) := by
  simp only [RingHom.restrict_apply, πRes, π]

lemma x_wd (c c' : K) (eq : πRes I ⟨ι ha c, by simp⟩ = πRes I ⟨ι ha c', by simp⟩)
    (y : CrossProduct a) :
    (c - c') • y ∈ I := by
  simp only [RingHom.restrict_apply, πRes, π] at eq
  erw [Quotient.eq''] at eq
  change I.ringCon _ _ at eq
  rw [TwoSidedIdeal.rel_iff, ← map_sub] at eq
  exact I.mul_mem_right _ _ eq

instance (priority := high) : SMul (RingHom.range <| πRes I) I.ringCon.Quotient where
  smul a := Quotient.map'
    (fun y => x a • y) (by
      rintro y y' (hy : I.ringCon _ _)
      show I.ringCon _ _
      simp only
      rw [TwoSidedIdeal.rel_iff] at hy ⊢
      rw [← smul_sub]
      apply I.mul_mem_left _ _ hy)

lemma smul_def_quot (a : RingHom.range <| πRes I) (y : CrossProduct a) :
    (a • (I.ringCon.mk' y : I.ringCon.Quotient) : I.ringCon.Quotient) =
    (Quotient.mk'' (x a • y)) := rfl

lemma smul_def_quot' (a : K) (y : CrossProduct a) :
    ((⟨π I (ι ha a), ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩ : RingHom.range <| πRes I) •
      (I.ringCon.mk' y : I.ringCon.Quotient) : I.ringCon.Quotient) =
    (I.ringCon.mk' (a • y)) := by
  erw [smul_def_quot, Quotient.eq'']
  change I.ringCon _ _
  rw [I.rel_iff, ← sub_smul]
  apply x_wd
  rw [hx, hx']
  rfl

lemma smul_def_quot'' (a : K) (y : CrossProduct a) :
  (((⟨π I (ι ha a), ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩ : RingHom.range <| πRes I) •
      (by exact Quotient.mk'' y : I.ringCon.Quotient) : I.ringCon.Quotient)) =
    (Quotient.mk'' (a • y) : I.ringCon.Quotient) :=
  smul_def_quot' I a y


set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 50000 in
instance : Module (RingHom.range <| πRes I) I.ringCon.Quotient where
  one_smul := by
    intro y
    induction y using RingCon.quot_ind with | basic y =>
    rw [show (1 : (πRes I).range) = ⟨π I (ι ha 1), ⟨⟨_, ⟨1, rfl⟩⟩, rfl⟩⟩
      by ext; simp only [map_one, OneMemClass.coe_one]]
    rw [smul_def_quot' I 1 y, one_smul]
  mul_smul := by
    intro c c' y
    induction y using RingCon.quot_ind with | basic y =>
    rcases c with ⟨-, ⟨⟨_, ⟨c, rfl⟩⟩, rfl⟩⟩
    rcases c' with ⟨-, ⟨⟨_, ⟨c', rfl⟩⟩, rfl⟩⟩
    simp only [πRes, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.restrict_apply,
      MulMemClass.mk_mul_mk, ← map_mul, smul_def_quot' I, mul_smul]
  smul_zero := by
    rintro ⟨-, ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩
    simp only [πRes, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.restrict_apply,
      show (0 : I.ringCon.Quotient) = I.ringCon.mk' 0 by rfl, smul_def_quot' I, smul_zero]
  smul_add := by
    rintro ⟨-, ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩ x y
    induction x using RingCon.quot_ind with | basic x =>
    induction y using RingCon.quot_ind with | basic y =>
    simp only [πRes, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.restrict_apply, ← map_add,
      smul_def_quot' I, smul_add]
  add_smul := by
    rintro ⟨-, ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩ ⟨-, ⟨⟨_, ⟨a', rfl⟩⟩, rfl⟩⟩ x
    induction x using RingCon.quot_ind with | basic y =>
    simp only [πRes, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.restrict_apply,
      AddMemClass.mk_add_mk, ← map_add, smul_def_quot' I, ← add_smul]
  zero_smul := by
    intro y
    induction y using RingCon.quot_ind with | basic y =>
    rw [show (0 : (πRes I).range) = ⟨π I (ι ha 0), ⟨⟨_, ⟨0, rfl⟩⟩, rfl⟩⟩
      by ext; simp only [ZeroMemClass.coe_zero, map_zero]]
    rw [smul_def_quot' I 0 y, zero_smul, map_zero]

example : True := ⟨⟩

instance : Module K (I.ringCon.Quotient) :=
  Module.compHom _ (f := show K →+* (πRes I).range from
  { toFun a := ⟨π I (ι ha a), by simpa using ⟨ι ha a, ⟨a, rfl⟩, rfl⟩⟩
    map_one' := by
      simp only [map_one, RingCon.coe_one]
      rfl
    map_mul' := by
      intros
      simp only [map_mul, RingCon.coe_mul, MulMemClass.mk_mul_mk]
    map_zero' := by
      simp only [map_zero, RingCon.coe_zero]
      rfl
    map_add' := by
      intros
      simp only [map_add, RingCon.coe_add, AddMemClass.mk_add_mk] })

lemma K_smul_quot (c : K) (x : I.ringCon.Quotient) : c • x =
  (⟨π I (ι ha c), by simpa using ⟨ι ha c, ⟨c, rfl⟩, rfl⟩⟩ : (πRes I).range) • x := rfl

set_option maxHeartbeats 400000 in
def basis (ne_top : I ≠ ⊤) : Basis (K ≃ₐ[F] K) K I.ringCon.Quotient :=
  .mk (v σ := I.ringCon.mk' (x_ ha σ))
    (by
      classical
      by_contra rid
      obtain ⟨J, LI, maximal⟩ := exists_maximal_linearIndepOn K (fun (i : K ≃ₐ[F] K) =>
        I.ringCon.mk' (x_ ha i))
      have ne : J ≠ Set.univ := by
        rintro rfl
        refine rid ?_
        let e : (Set.univ : Set (K ≃ₐ[F] K)) ≃ (K ≃ₐ[F] K) := Equiv.Set.univ (K ≃ₐ[F] K)
        have := linearIndependent_equiv e.symm |>.2 LI
        exact this
      rw [Set.ne_univ_iff_exists_not_mem] at ne
      obtain ⟨σ, hσ⟩ := ne
      obtain ⟨c, c_ne_zero, hc⟩ := maximal σ hσ
      let B := Basis.span LI
      replace hc := Submodule.smul_mem _ c⁻¹ hc
      rw [← mul_smul, inv_mul_cancel₀ c_ne_zero, one_smul] at hc
      clear c c_ne_zero
      have mem1 : I.ringCon.mk' (x_ ha σ) ∈ Submodule.span K
          (Set.range fun (σ : J) ↦ I.ringCon.mk' (x_ ha σ)) := by
        convert hc; aesop
      have eq0 : (⟨I.ringCon.mk' (x_ ha σ), mem1⟩ : Submodule.span K
          (Set.range fun (σ : J) ↦ I.ringCon.mk' (x_ ha σ))) =
          ∑ τ ∈ (B.repr ⟨_, mem1⟩).support, B.repr ⟨_, mem1⟩ τ • I.ringCon.mk' (x_ ha τ) := by
        conv_lhs => rw [← B.linearCombination_repr ⟨I.ringCon.mk' (x_ ha σ), mem1⟩,
          Finsupp.linearCombination_apply, Finsupp.sum]
        rw [AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [SetLike.val_smul, smul_def]
        congr 1
        simp only [B, Basis.span_apply]
      simp only at eq0


      have eq1 (c : K) := calc I.ringCon.mk' (ι ha (σ c)) * I.ringCon.mk' (x_ ha σ)
          _ = I.ringCon.mk' (x_ ha σ) * I.ringCon.mk' (ι ha c) := by
            rw [← map_mul, ← x__conj' ha, map_mul]
          _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
                I.ringCon.mk' (ι ha (B.repr ⟨_, mem1⟩ τ)) * I.ringCon.mk' (x_ ha τ) *
                  I.ringCon.mk' (ι ha c) := by
            conv_lhs => rw [eq0, Finset.sum_mul]
            refine Finset.sum_congr rfl fun τ _ => ?_
            simp only [K_smul_quot, smul_def_quot' I, smul_def, ← map_mul]
          _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
                I.ringCon.mk' (ι ha (B.repr ⟨_, mem1⟩ τ)) *
                I.ringCon.mk' (ι ha (τ.1 c)) * I.ringCon.mk' (x_ ha τ) :=
            Finset.sum_congr rfl fun i _ => by
            simp only [_root_.mul_assoc]
            congr 1
            rw [← map_mul, x__conj', ← map_mul]
          _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
                I.ringCon.mk' (ι ha (B.repr ⟨_, mem1⟩ τ * τ.1 c)) *
                I.ringCon.mk' (x_ ha τ) :=
            Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul]

      have eq2 (c : K) := calc I.ringCon.mk' (ι ha (σ c)) * I.ringCon.mk' (x_ ha σ)
          _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
              I.ringCon.mk' (ι ha (σ c * (B.repr ⟨_, mem1⟩) τ)) *
              I.ringCon.mk' (x_ ha τ) := by
            conv_lhs => rw [eq0, Finset.mul_sum]
            refine Finset.sum_congr rfl fun τ _ => ?_
            simp only [K_smul_quot, smul_def_quot' I, smul_def, ← map_mul, ← _root_.mul_assoc]

      have eq3 (c : K) :
          ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
                I.ringCon.mk' (ι ha (B.repr ⟨_, mem1⟩ τ * τ.1 c)) *
                I.ringCon.mk' (x_ ha τ) =
          ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
              I.ringCon.mk' (ι ha (σ c * (B.repr ⟨_, mem1⟩) τ)) *
              I.ringCon.mk' (x_ ha τ) :=
        eq1 c |>.symm.trans <| eq2 c

      have eq4 (c : K) :
          ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
              I.ringCon.mk' (ι ha (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ)) *
              I.ringCon.mk' (x_ ha τ) = 0 := by
        simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert eq3 c
        · simp only [← map_mul]
        · simp only [← map_mul]

      have eq5 (c : K) :
          ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
              (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ) •
              I.ringCon.mk' (x_ ha τ) = 0 := by
        rw [← eq4 c]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [K_smul_quot, smul_def_quot' I, smul_def, ← map_mul]
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
        have mem' := I.mul_mem_left (x_ ha σ)⁻¹.1 _ eq0
        simp only [Units.inv_mul] at mem'
        refine ne_top <| eq_top_iff.2 fun x _ => ?_
        simpa using I.mul_mem_left x _ mem'

      obtain ⟨τ, τ_mem⟩ := Finset.nonempty_of_ne_empty this
      have eq7 : σ = τ := by
        ext c
        specialize eq6 c τ τ.2
        rw [mul_comm] at eq6
        simp only [Subtype.coe_eta, mul_eq_mul_right_iff] at eq6
        refine eq6.recOn Eq.symm fun rid => ?_
        simp only [Finsupp.mem_support_iff, ne_eq] at τ_mem
        contradiction
      subst eq7
      exact hσ τ.2)
    (by
      rintro z -
      induction z using Quotient.inductionOn' with | h z =>
      have eq1 := x_AsBasis ha |>.linearCombination_repr z
      rw [← eq1]
      change I.ringCon.mk' _ ∈ _
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      refine Submodule.sum_mem _ fun σ _ => ?_
      rw [show I.ringCon.mk' (((x_AsBasis ha).repr z) σ • (x_AsBasis ha) σ) =
        (⟨π I (ι ha ((x_AsBasis ha).repr z σ)), by
          simp only [πRes, π, RingHom.mem_range,
            RingHom.restrict_apply, Subtype.exists, AlgHom.mem_range, exists_prop', nonempty_prop,
            exists_exists_eq_and]
          refine ⟨((x_AsBasis ha).repr z σ), rfl⟩⟩ : (πRes I).range) •
          I.ringCon.mk' (x_AsBasis ha σ) by
          rw [smul_def_quot']]
      refine Submodule.smul_mem _ _ <| Submodule.subset_span ⟨σ, ?_⟩
      simp only [x_, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Units.val_ofLeftRightInverse,
        x_AsBasis_apply])

def π₁ (ne_top : I ≠ ⊤) : CrossProduct a ≃ₗ[K] (I.ringCon.Quotient) :=
  Basis.equiv (x_AsBasis ha) (basis I ne_top) (Equiv.refl _)

def π₂ : CrossProduct a →ₗ[K] (I.ringCon.Quotient) where
  __ := π I
  map_smul' c := => by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, RingHom.id_apply]
    simp only [smul_def, K_smul_quot]
    erw [smul_def_quot' I]
    rfl

lemma equal (ne_top : I ≠ ⊤) : π₁ I ne_top = π₂ I := by
  apply Basis.ext (b := x_AsBasis ha)
  intro σ
  delta π₁
  erw [Basis.equiv_apply]
  simp only [basis, x_, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Units.val_ofLeftRightInverse,
    Equiv.refl_apply, Basis.coe_mk, π₂, π, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, x_AsBasis_apply, LinearMap.coe_mk, AddHom.coe_mk]

lemma π_inj (ne_top : I ≠ ⊤): Function.Injective (π I) := by
  change Function.Injective (π₂ I)
  rw [← equal (ne_top := ne_top)]
  exact LinearEquiv.injective _

end is_simple_proofs

open is_simple_proofs in
instance is_simple : IsSimpleRing (CrossProduct a) :=
⟨⟨by
    intro I
    by_contra! h

    have inj : Function.Injective (π I) := π_inj I h.2
    rw [TwoSidedIdeal.injective_iff_ker_eq_bot] at inj
    refine h.1 <| inj ▸ ?_
    ext x
    simp only [π, TwoSidedIdeal.mem_ker]
    change _ ↔ _ = I.ringCon.mk' 0
    erw [Quotient.eq'']
    change _ ↔ I.ringCon _ _
    rw [I.rel_iff, sub_zero]⟩⟩

instance [IsGalois F K] : Algebra.IsCentral F (CrossProduct a) where
  out := is_central ha

instance [IsGalois F K] : FiniteDimensional F (CrossProduct a) :=
  .of_finrank_eq_succ (n := (Module.finrank F K)^2 - 1) (by
    rw [dim_eq_square]
    rw [← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos]
    apply pow_two_pos_of_ne_zero
    have : 0 < Module.finrank F K := Module.finrank_pos
    omega)

def asCSA [IsGalois F K] : CSA F :=
  ⟨.of F (CrossProduct a)⟩

end CrossProduct

end galois

end GoodRep

namespace RelativeBrGroup

section from_two

open GoodRep.CrossProduct

variable [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

def fromTwoCocycles (a : twoCocycles (galAct F K)) : RelativeBrGroup K F :=
⟨Quotient.mk'' (asCSA (isMulTwoCocycle_of_mem_twoCocycles _ a.2)), by
  rw [mem_relativeBrGroup_iff_exists_goodRep]
  exact ⟨⟨(asCSA (isMulTwoCocycle_of_mem_twoCocycles _ a.2)), rfl,
    ι (isMulTwoCocycle_of_mem_twoCocycles _ a.2),
    dim_eq_square (isMulTwoCocycle_of_mem_twoCocycles _ a.2)⟩⟩⟩

variable (F K) in
set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 40000 in
def fromSnd : H2 (galAct F K) → RelativeBrGroup K F :=
  Quotient.lift fromTwoCocycles <| by
    rintro ⟨(a : _ → Kˣ), ha⟩ ⟨(b : _ → Kˣ), hb⟩ (hab : Submodule.quotientRel _ _ _)

    have H' : H2π (galAct F K) ⟨a, ha⟩ - H2π (galAct F K) ⟨b, hb⟩ = 0 := by
      rw [← map_sub, H2π_eq_zero_iff]
      simp only [Submodule.quotientRel_def, LinearMap.mem_range] at hab
      obtain ⟨y, hy⟩ := hab
      use y
      rw [← hy]
      rfl

    rw [← map_sub, H2π_eq_zero_iff] at H'
    have ha : IsMulTwoCocycle (G := K ≃ₐ[F] K) (M := Kˣ) a := isMulTwoCocycle_of_mem_twoCocycles a ha
    have hb : IsMulTwoCocycle (G := K ≃ₐ[F] K) (M := Kˣ) b := isMulTwoCocycle_of_mem_twoCocycles b hb
    have hc : IsMulTwoCoboundary (G := K ≃ₐ[F] K) (M := Kˣ) (a / b) := by
      exact isMulTwoCoboundary_of_mem_twoCoboundaries (G := K ≃ₐ[F] K) (M := Kˣ)
        _ H'

    obtain ⟨c, hc⟩ := hc
    simp only [fromTwoCocycles, Subtype.mk.injEq, Quotient.eq'']
    let A := asCSA ha
    let B := asCSA hb
    change IsBrauerEquivalent A B
    letI : Module K A := inferInstanceAs <| Module K (GoodRep.CrossProduct a)
    letI : Module K B := inferInstanceAs <| Module K (GoodRep.CrossProduct hb)

    let basis : Basis (K ≃ₐ[F] K) K B :=
      Basis.unitsSMul (x_AsBasis hb) c
    let φ0 : A ≃ₗ[K] B :=
      Basis.equiv (x_AsBasis ha) basis (Equiv.refl _)
    haveI : LinearMap.CompatibleSMul A B F K := by
      constructor
      have eq (c : F) (a : A) : c • a = algebraMap F K c • a := by
        induction a using GoodRep.CrossProduct.single_induction with
        | single σ a =>
          simp only [Algebra.smul_def]
          rw [GoodRep.CrossProduct.smul_def]
          congr 1
          delta ι
          simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, AlgHom.commutes, algebraMap_val]
          rw [Algebra.algebraMap_eq_smul_one]
        | add x y hx hy =>
          change c • (x + y) = _ • (x + y)
          rw [smul_add, smul_add, hx, hy]
        | zero =>
          change c • 0 = _ • 0
          simp
      have eq' (c : F) (a : B) : c • a = algebraMap F K c • a := by
        induction a using GoodRep.CrossProduct.single_induction with
        | single σ a =>
          simp only [Algebra.smul_def]
          rw [GoodRep.CrossProduct.smul_def]
          congr 1
          delta ι
          simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, AlgHom.commutes, algebraMap_val]
          rw [Algebra.algebraMap_eq_smul_one]
        | add x y hx hy =>
          change c • (x + y) = _ • (x + y)
          rw [smul_add, smul_add, hx, hy]
        | zero =>
          change c • 0 = _ • 0
          simp

      intro l c a
      rw [eq, eq', map_smul]
    let φ1 : A ≃ₗ[F] B := φ0.restrictScalars F
    let φ2 : A ≃ₐ[F] B := AlgEquiv.ofLinearEquiv φ1
      (by
        change φ0 1 = 1
        rw [show (1 : A) = (a 1)⁻¹.1 • (x_AsBasis ha 1 : A) by
          apply val_injective ha
          erw [GoodRep.CrossProduct.smul_def]
          simp only [one_val, Prod.mk_one_one, Units.val_inv_eq_inv_val, x_AsBasis_apply, mul_val,
            ι_apply_val, GoodRep.mulLinearMap_single_single, _root_.mul_one, AlgEquiv.one_apply,
            isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
            IsUnit.inv_mul_cancel_right], map_smul]
        erw [Basis.equiv_apply]
        simp only [Units.val_inv_eq_inv_val, Equiv.refl_apply, Basis.unitsSMul_apply, basis]
        apply val_injective hb
        erw [GoodRep.CrossProduct.smul_def, GoodRep.CrossProduct.smul_def]
        erw [mul_val, mul_val]
        erw [x_AsBasis_apply]
        simp only [ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
          GoodRep.mulLinearMap_single_single, _root_.mul_one, AlgEquiv.one_apply,
          isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right,
          map_inv₀, one_val, Pi.single_inj]
        specialize hc 1 1
        simp only [one_smul, _root_.mul_one, div_self', _root_.one_mul, Prod.mk_one_one,
          Pi.div_apply] at hc
        simp only [hc, Units.val_div_eq_div_val]
        field_simp)
      (by
        intro α β
        change φ0 _ = φ0 _ * φ0 _
        induction α using GoodRep.CrossProduct.single_induction with
        | single σ α =>
          induction β using GoodRep.CrossProduct.single_induction with
          | single τ β =>
            rw [show (⟨Pi.single σ α⟩ : GoodRep.CrossProduct a) * ⟨Pi.single τ β⟩ =
              ⟨Pi.single (σ * τ) (α * σ β * a (σ, τ))⟩ by
              apply val_injective
              simp only [mul_val, GoodRep.mulLinearMap_single_single],
              show (⟨Pi.single (σ * τ) (α * σ β * a (σ, τ))⟩ : GoodRep.CrossProduct a) =
                (α * σ β * a (σ, τ)) • ((x_AsBasis ha (σ * τ)) : GoodRep.CrossProduct a) by
              apply val_injective
              simp only [x_AsBasis_apply, smul_def, map_mul, mul_val, ι_apply_val, Prod.mk_one_one,
                Units.val_inv_eq_inv_val, GoodRep.mulLinearMap_single_single, _root_.mul_one,
                AlgEquiv.one_apply, map_inv₀, _root_.one_mul, Pi.single_inj]
              rw [a_one_left ha]
              simp only [_root_.mul_assoc]
              congr 1
              simp only [← _root_.mul_assoc]
              simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
                IsUnit.inv_mul_cancel_right]
              field_simp, map_smul,
              show (⟨Pi.single σ α⟩ : GoodRep.CrossProduct a) = α • (x_AsBasis ha σ) by
              apply val_injective
              simp only [x_AsBasis_apply, smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
                Units.val_inv_eq_inv_val, GoodRep.mulLinearMap_single_single, _root_.one_mul,
                AlgEquiv.one_apply, _root_.mul_one, a_one_left ha, isUnit_iff_ne_zero, ne_eq,
                Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right], map_smul,
              show (⟨Pi.single τ β⟩ : GoodRep.CrossProduct a) = β • (x_AsBasis ha τ) by
              apply val_injective
              simp only [x_AsBasis_apply, smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
                Units.val_inv_eq_inv_val, GoodRep.mulLinearMap_single_single, _root_.one_mul,
                AlgEquiv.one_apply, _root_.mul_one, a_one_left ha, isUnit_iff_ne_zero, ne_eq,
                Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right], map_smul]
            erw [Basis.equiv_apply, Basis.equiv_apply, Basis.equiv_apply]
            simp only [Equiv.refl_apply, Basis.unitsSMul_apply, basis]
            erw [x_AsBasis_apply, x_AsBasis_apply, x_AsBasis_apply]
            erw [GoodRep.CrossProduct.smul_def, GoodRep.CrossProduct.smul_def,
              GoodRep.CrossProduct.smul_def, GoodRep.CrossProduct.smul_def,
              GoodRep.CrossProduct.smul_def, GoodRep.CrossProduct.smul_def]
            apply val_injective
            simp only [map_mul, mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
              GoodRep.mulLinearMap_single_single, _root_.mul_one, AlgEquiv.one_apply,
              _root_.one_mul]
            repeat erw [mul_val]
            simp only [ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
              GoodRep.mulLinearMap_single_single, _root_.one_mul, AlgEquiv.one_apply,
              _root_.mul_one, map_mul, map_inv₀, Pi.single_inj]
            simp only [a_one_left hb, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
              IsUnit.inv_mul_cancel_right, EmbeddingLike.map_eq_zero_iff]
            specialize hc σ τ
            rw [Units.ext_iff] at hc
            field_simp at hc
            simp only [_root_.mul_assoc]
            congr 2
            simp only [← _root_.mul_assoc]
            rw [_root_.mul_assoc (σ β)]
            simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
              IsUnit.inv_mul_cancel, _root_.mul_one, IsUnit.inv_mul_cancel_right]
            rw [_root_.mul_assoc (σ β), ← hc]
            field_simp
            ring
          | add x y hx hy =>
            change φ0 ((⟨Pi.single σ α⟩ : A) * (x + y)) = φ0 ⟨Pi.single σ α⟩ * (φ0 (x + y))
            simp only [mul_add, map_add, hx, hy]
          | zero =>
            erw [mul_zero, map_zero, mul_zero]
        | add α α' hα hα' =>
          erw [add_mul, map_add, hα, hα', map_add, add_mul]
        | zero =>
          erw [zero_mul, map_zero, zero_mul])

    apply IsBrauerEquivalent.iso_to_eqv (h := φ2)

lemma fromSnd_wd (a : twoCocycles (galAct F K)) :
    (fromSnd F K <| Quotient.mk'' a) =
    ⟨Quotient.mk'' (asCSA (isMulTwoCocycle_of_mem_twoCocycles _ a.2)),
      mem_relativeBrGroup_iff_exists_goodRep _ |>.2 ⟨_, rfl, ι _, dim_eq_square _⟩⟩ := by
  rfl

open GoodRep in
lemma toSnd_fromSnd :
    toSnd ∘ fromSnd F K = id := by
  ext a
  induction a using Quotient.inductionOn' with | h a =>
  rcases a with ⟨(a : _ → Kˣ), ha'⟩
  have ha : IsMulTwoCocycle a := isMulTwoCocycle_of_mem_twoCocycles a ha'
  simp only [Function.comp_apply, fromSnd_wd, id_eq]
  let A : GoodRep K (Quotient.mk'' <| asCSA ha) :=
    ⟨asCSA ha, rfl, ι ha, dim_eq_square ha⟩

  let y_ : Π σ, A.conjFactor σ σ := ⟨x_ ha σ, fun c => by erw [x__conj ha σ]; rfl⟩
  rw [toSnd_wd (A := A) (x_ := y_)]
  let b : ((K ≃ₐ[F] K) × (K ≃ₐ[F] K)) → Kˣ := A.toTwoCocycles y_

  rw [show A.toH2 y_ = Quotient.mk'' ⟨b, _⟩ by rfl]
  -- rw [Quotient.eq'']
  -- change (twoCoboundaries (galAct F K)).quotientRel.r _ _
  change H2π _ _ = H2π _ _
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  -- rw [Submodule.quotientRel_def]
  suffices H : IsMulTwoCoboundary _ from
    (twoCoboundariesOfIsMulTwoCoboundary H).2
  refine ⟨fun _ => 1, ?_⟩
  intro σ τ
  simp only [smul_one, div_self', _root_.mul_one, Pi.sub_apply]
  change _ = (Additive.toMul b (σ, τ)) / (Additive.toMul _)
  erw [Equiv.symm_apply_apply]
  simp only [GoodRep.toTwoCocycles, GoodRep.conjFactorCompCoeffAsUnit, AlgEquiv.mul_apply]
  change _ = _ / a (σ, τ)
  ext : 1
  simp only [AlgEquiv.smul_units_def, div_mul_cancel, Units.coe_map, MonoidHom.coe_coe,
    Units.val_div_eq_div_val]
  field_simp
  simp only [AlgEquiv.mul_apply, y_]
  change _ = A.conjFactorCompCoeff (y_ σ) (y_ τ) (y_ (σ * τ))
  apply_fun A.ι using RingHom.injective _
  rw [conjFactorCompCoeff_spec'', x__mul ha σ τ, Units.mul_inv_cancel_right]
  rfl

set_option maxHeartbeats 500000 in
lemma fromSnd_toSnd :
    fromSnd F K ∘ toSnd = id := by
  ext X
  obtain ⟨A⟩ := mem_relativeBrGroup_iff_exists_goodRep X.1 |>.1 X.2
  simp only [Function.comp_apply, id_eq, SetLike.coe_eq_coe]
  rw [toSnd_wd (A := A) (x_ := A.aribitaryConjFactor)]
  ext : 1
  conv_rhs => rw [← A.quot_eq]
  simp only [GoodRep.toH2, fromSnd_wd]
  rw [Quotient.eq'']
  apply IsBrauerEquivalent.iso_to_eqv
  set lhs := _
  change lhs ≃ₐ[F] A
  letI : Module K lhs := inferInstanceAs <| Module K (GoodRep.CrossProduct _)
  let φ0 : lhs ≃ₗ[K] A :=
    Basis.equiv (x_AsBasis _) (A.conjFactorBasis (A.aribitaryConjFactor)) (Equiv.refl _)
  haveI : LinearMap.CompatibleSMul lhs A.carrier.carrier F K := by
    constructor
    have eq (c : F) (a : A) : c • a = algebraMap F K c • a := by
      simp only [algebraMap_smul]
    have eq' (c : F) (a : lhs) : c • a = algebraMap F K c • a := by
      induction a using GoodRep.CrossProduct.single_induction with
      | single σ a =>
        simp only [Algebra.smul_def]
        rw [GoodRep.CrossProduct.smul_def]
        congr 1
        delta ι
        simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, AlgHom.commutes, algebraMap_val]
        rw [Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        change c • (x + y) = _ • (x + y)
        rw [smul_add, smul_add, hx, hy]
      | zero =>
        change c • 0 = _ • 0
        simp

    intro l c a
    rw [eq, eq', map_smul]
  let φ1 : lhs ≃ₗ[F] A := φ0.restrictScalars F
  refine AlgEquiv.ofLinearEquiv φ1 ?_ ?_
  · change φ0 1 = 1
    rw [one_in_x_AsBasis]
    change φ0 ((_ : K) • _) = _
    rw [map_smul]
    simp only [LinearEquiv.restrictScalars_apply, φ1, φ0]
    erw [Basis.equiv_apply]
    simp only [Prod.mk_one_one, Function.comp_apply, Units.val_inv_eq_inv_val,
      GoodRep.conjFactorBasis, Equiv.refl_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
      AlgEquiv.one_apply, GoodRep.smul_def]
    change A.ι (A.toTwoCocycles _ (1, 1))⁻¹ * _ = 1
    simp only [GoodRep.toTwoCocycles, GoodRep.conjFactorCompCoeffAsUnit, Prod.mk_one_one,
      Prod.fst_one, Prod.snd_one, AlgEquiv.one_apply]
    have := A.conjFactorCompCoeff_spec' (A.aribitaryConjFactor 1)
      (A.aribitaryConjFactor 1)
      (A.aribitaryConjFactor (1 * 1))
    simp only [AlgEquiv.one_apply, AlgEquiv.mul_apply] at this
    rw [GoodRep.conjFactorCompCoeff_inv]
    erw [_root_.one_mul]
    simp only [AlgEquiv.one_apply, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul, Units.inv_mul]
  · intro x y
    change φ0 _ = φ0 _ * φ0 _
    induction x using GoodRep.CrossProduct.single_induction with
    | single x c =>
      induction y using GoodRep.CrossProduct.single_induction with
      | single y d =>
        rw [mul_single_in_xAsBasis]
        rw [single_in_xAsBasis, single_in_xAsBasis]
        rw [map_smul, map_smul, map_smul]
        simp only [Function.comp_apply, GoodRep.smul_def, map_mul, φ0]
        erw [Basis.equiv_apply, Basis.equiv_apply, Basis.equiv_apply]
        simp only [GoodRep.conjFactorBasis, Equiv.refl_apply,
          coe_basisOfLinearIndependentOfCardEqFinrank, AlgEquiv.mul_apply]
        change A.ι c * A.ι (x d) * A.ι (A.toTwoCocycles _ _) * _ = _
        simp only [GoodRep.toTwoCocycles, GoodRep.conjFactorCompCoeffAsUnit]
        simp only [_root_.mul_assoc]
        erw [A.conjFactorCompCoeff_spec'']
        simp only [_root_.mul_assoc]
        simp only [AlgEquiv.mul_apply, Units.inv_mul, _root_.mul_one]
        simp only [← _root_.mul_assoc]
        congr 1
        simp only [_root_.mul_assoc]
        congr 1
        rw [(A.aribitaryConjFactor x).2 d]
        field_simp
      | add y y' hy hy' =>
        erw [mul_add, map_add, hy, hy', map_add, mul_add]
      | zero =>
        erw [mul_zero, map_zero, mul_zero]
    | add x x' hx hx' =>
      erw [add_mul, map_add, hx, hx', map_add, add_mul]
    | zero =>
      erw [zero_mul, map_zero, zero_mul]

@[simp]
def equivSnd : RelativeBrGroup K F ≃ H2 (galAct F K) where
  toFun := toSnd
  invFun := fromSnd F K
  left_inv := congr_fun fromSnd_toSnd
  right_inv := congr_fun toSnd_fromSnd

end from_two

end RelativeBrGroup
