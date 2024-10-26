import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.Algebra.DirectSum.Ring

import BrauerGroup.Subfield.splitting

import BrauerGroup.Subfield.Subfield

suppress_compilation

open FiniteDimensional BrauerGroup

variable {F K : Type} [Field K] [Field F] [Algebra F K]
variable (X : BrGroup (K := F))

variable (K) in
structure GoodRep where
carrier : CSA.{0, 0} F
quot_eq : (Quotient.mk'' carrier) = X
ι : K →ₐ[F] carrier
dim_eq_square : finrank F carrier = (finrank F K) ^ 2

namespace GoodRep

variable {X : BrGroup (K := F)} (A B : GoodRep K X)

section basic

instance : CoeSort (GoodRep K X) Type where
  coe A := A.carrier

def ιRange : K ≃ₐ[F] A.ι.range :=
AlgEquiv.ofInjective _ (RingHom.injective _)

instance : Algebra F A := inferInstanceAs <| Algebra F A.carrier

instance : IsSimpleOrder (TwoSidedIdeal A.ι.range) :=
  TwoSidedIdeal.orderIsoOfRingEquiv A.ιRange.symm |>.isSimpleOrder

lemma centralizerιRange : Subalgebra.centralizer F A.ι.range = A.ι.range := by
  let L : SubField F A :=
  { __ := A.ι.range
    mul_comm := by
      rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← map_mul, mul_comm]
    inverse := by
      rintro _ ⟨x, rfl⟩ hx
      refine ⟨A.ι x⁻¹, ?_, ?_⟩
      · simp
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← map_mul]
        rw [mul_inv_cancel₀, map_one]
        rintro rfl
        simp at hx }
  change Subalgebra.centralizer F (L.toSubalgebra : Set A) = L.toSubalgebra
  apply cor_two_3to1
  apply cor_two_2to3
  change finrank F A = finrank F A.ι.range * finrank F A.ι.range
  rw [A.dim_eq_square, pow_two, LinearEquiv.finrank_eq (f := A.ιRange.toLinearEquiv.symm)]

instance : Module K A where
  smul c a := A.ι c * a
  one_smul a := show A.ι 1 * a = a by simp
  mul_smul c c' x := show A.ι (c * c') * x = _ * (_ * _) by simp [_root_.mul_assoc]
  smul_zero c := show A.ι c * 0 = 0 by simp
  smul_add c x y := show A.ι c * (x + y) = _ * _ + _ * _ by simp [_root_.mul_add]
  add_smul c c' x := show A.ι (c + c') * x = _ * _ + _ * _ by simp [_root_.add_mul]
  zero_smul x := show A.ι 0 * x = 0 by simp

@[simp]
lemma smul_def (c : K) (a : A) : c • a = A.ι c * a := rfl

instance : FiniteDimensional F A := A.carrier.fin_dim

instance : IsScalarTower F K A where
  smul_assoc a b c := by simp

instance : FiniteDimensional K A := FiniteDimensional.right F K A

lemma dim_eq' [FiniteDimensional F K] : finrank K A = finrank F K := by
  have : finrank F A = finrank F K * finrank K A :=
    Eq.symm (finrank_mul_finrank F K A.carrier.carrier)
  rw [A.dim_eq_square, pow_two] at this
  simp only [mul_eq_mul_left_iff] at this
  refine this.recOn Eq.symm fun rid => ?_
  have : 0 < finrank F K := finrank_pos
  omega

end basic

section single

variable (ρ σ τ : K ≃ₐ[F] K)

def conjFactor : (σ : K ≃ₐ[F] K) → Type :=
  fun σ => { a : Aˣ //  ∀ x : K, A.ι (σ x) = a * A.ι x * a⁻¹ }

def aribitaryConjFactor : A.conjFactor σ :=
⟨SkolemNoether' F A K A.ι (A.ι.comp σ) |>.choose, fun x =>
  SkolemNoether' F A K A.ι (A.ι.comp σ) |>.choose_spec x⟩

variable {A ρ σ τ}

@[simp] lemma conjFactor_prop (x : A.conjFactor σ) (c : K) :
    x.1 * A.ι c * x.1⁻¹ = A.ι (σ c) := x.2 c |>.symm

def mul' (x : A.conjFactor σ) (y : A.conjFactor τ) : A.conjFactor (σ * τ) :=
⟨x.1 * y.1, fun c => by
  simp only [AlgEquiv.mul_apply, Units.val_mul, _root_.mul_assoc, mul_inv_rev]
  rw [← _root_.mul_assoc (A.ι c), ← mul_assoc (y.1 : A), ← mul_assoc (y.1 : A),
    conjFactor_prop, ← _root_.mul_assoc, conjFactor_prop]⟩

@[simp]
lemma mul'_coe (x : A.conjFactor σ) (y : A.conjFactor τ) : (mul' x y).1.1 = x.1 * y.1 := rfl

lemma conjFactor_rel_aux (x y : A.conjFactor σ) :
    ∃ (c : K), x.1 = y.1 * A.ι c := by
  have mem1 : (y.1⁻¹ * x.1 : A) ∈ Subalgebra.centralizer F A.ι.range := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    have := x.2 z |>.symm.trans (y.2 z)
    apply_fun (x.1⁻¹.1 * ·) at this
    simp only [← _root_.mul_assoc, Units.inv_mul, _root_.one_mul] at this
    apply_fun (· * x.1.1) at this
    simp only [Units.inv_mul_cancel_right] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    conv_rhs => rw [this]
    simp only [_root_.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left]

  rw [A.centralizerιRange, AlgHom.mem_range] at mem1
  obtain ⟨c, hc⟩ := mem1
  use c
  simp only [hc, Units.mul_inv_cancel_left]

lemma conjFactor_rel (x y : A.conjFactor σ) :
    ∃! (c : K), x.1 = y.1 * A.ι c := by
  obtain ⟨c, hc⟩ := conjFactor_rel_aux x y
  refine ⟨c, hc, fun c' (hc' : _ = _) => ?_⟩
  rw [hc] at hc'
  simp only [Units.mul_right_inj] at hc'
  exact RingHom.injective _ hc' |>.symm

def conjFactorTwistCoeff (x y : A.conjFactor σ) : K := conjFactor_rel x y |>.choose

lemma conjFactorTwistCoeff_spec (x y : A.conjFactor σ) : x.1 = y.1 * A.ι (conjFactorTwistCoeff x y) :=
  conjFactor_rel x y |>.choose_spec.1

lemma conjFactorTwistCoeff_unique (x y : A.conjFactor σ) (c : K) (h : x.1 = y.1 * A.ι c) :
    c = conjFactorTwistCoeff x y :=
  conjFactor_rel x y |>.choose_spec.2 _ h

@[simp]
lemma conjFactorTwistCoeff_self (x : A.conjFactor σ) : conjFactorTwistCoeff x x = 1 :=
  Eq.symm <| conjFactorTwistCoeff_unique _ _ _ <| by simp

@[simps]
def conjFactorTwistCoeffAsUnit (x y : A.conjFactor σ) : Kˣ where
  val := conjFactorTwistCoeff x y
  inv := conjFactorTwistCoeff y x
  val_inv := by
    simpa using conjFactorTwistCoeff_unique y y
      (conjFactorTwistCoeff x y * conjFactorTwistCoeff y x)
      (by simp only [map_mul, ← _root_.mul_assoc, ← conjFactorTwistCoeff_spec])
  inv_val := by
    simpa using conjFactorTwistCoeff_unique x x
      (conjFactorTwistCoeff y x * conjFactorTwistCoeff x y)
      (by simp only [map_mul, ← _root_.mul_assoc, ← conjFactorTwistCoeff_spec])

@[simp]
lemma conjFactorTwistCoeff_swap (x y : A.conjFactor σ) :
    conjFactorTwistCoeff x y * conjFactorTwistCoeff y x = 1 :=
    conjFactorTwistCoeffAsUnit x y |>.val_inv

@[simp]
lemma conjFactorTwistCoeff_swap' (x y : A.conjFactor σ) :
    conjFactorTwistCoeff y x * conjFactorTwistCoeff x y = 1 :=
    conjFactorTwistCoeffAsUnit y x |>.val_inv

@[simp]
lemma conjFactorTwistCoeff_swap'' (x y : A.conjFactor σ) :
    A.ι (conjFactorTwistCoeff x y) * A.ι (conjFactorTwistCoeff y x) = 1 := by
  simp [← map_mul]

@[simp]
lemma conjFactorTwistCoeff_swap''' (x y : A.conjFactor σ) :
    A.ι (conjFactorTwistCoeff y x) * A.ι (conjFactorTwistCoeff x y) = 1 := by
  simp [← map_mul]

lemma conjFactorTwistCoeff_spec' (x y : A.conjFactor σ) :
    x.1 = A.ι (σ <| conjFactorTwistCoeff x y) * y.1 := by
  calc x.1.1
    _ = (x.1 * A.ι (conjFactorTwistCoeff x y) * x.1⁻¹) * (x.1 * A.ι (conjFactorTwistCoeff y x)) := by
        simp only [_root_.mul_assoc, Units.inv_mul_cancel_left, conjFactorTwistCoeff_swap'',
          _root_.mul_one]
    _ = A.ι (σ <| conjFactorTwistCoeff x y) * (x.1 * A.ι (conjFactorTwistCoeff y x)) := by
        simp only [conjFactor_prop]
    _ = A.ι (σ <| conjFactorTwistCoeff x y) * y.1 := by
        simp [← conjFactorTwistCoeff_spec]

def conjFactorCompCoeff (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) : K :=
    σ <| τ <| conjFactorTwistCoeff (mul' x y) z

@[simp]
def conjFactorCompCoeffAsUnit
    (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) : Kˣ where
  val := conjFactorCompCoeff x y z
  inv := σ <| τ <| conjFactorTwistCoeff z (mul' x y)
  val_inv := by
    simp only [conjFactorCompCoeff, ← map_mul, conjFactorTwistCoeff_swap, map_one]
  inv_val := by
    simp only [conjFactorCompCoeff, ← map_mul, conjFactorTwistCoeff_swap, map_one]

lemma conjFactorCompCoeff_spec
    (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    (x.1 * y.1 : A) = A.ι (conjFactorCompCoeff x y z) * z.1 :=
  conjFactorTwistCoeff_spec' (mul' x y) z

lemma conjFactorCompCoeff_spec' (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι (σ <| τ <| conjFactorTwistCoeff z (mul' x y)) * (x.1 * y.1 : A) = z.1 := by
  rw [conjFactorCompCoeff_spec (z := z), ← _root_.mul_assoc, ← map_mul]
  have := conjFactorCompCoeffAsUnit x y z |>.inv_val
  erw [this]
  simp

lemma conjFactorCompCoeff_comp_comp₁
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xρσ : A.conjFactor (ρ * σ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    xρ.1.1 * xσ.1 * xτ.1 =
    A.ι (conjFactorCompCoeff xρ xσ xρσ) *
    A.ι (conjFactorCompCoeff xρσ xτ xρστ) *
    xρστ.1 := by
  rw [conjFactorCompCoeff_spec (z := xρσ), _root_.mul_assoc,
    conjFactorCompCoeff_spec (z := xρστ), ← _root_.mul_assoc]

lemma conjFactorCompCoeff_eq (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι (conjFactorCompCoeff x y z) = (x.1 * y.1) * z.1⁻¹ := by
  have := conjFactorTwistCoeff_spec' (mul' x y) z
  simp only [AlgEquiv.mul_apply, mul'_coe] at this
  rw [this]
  simp only [AlgEquiv.mul_apply, Units.mul_inv_cancel_right]
  rfl

lemma conjFactorCompCoeff_comp_comp₂
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xστ : A.conjFactor (σ * τ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    xρ.1.1 * (xσ.1 * xτ.1) =
    A.ι (ρ <| conjFactorCompCoeff xσ xτ xστ) *
    A.ι (conjFactorCompCoeff xρ xστ xρστ) *
    xρστ.1 := by
  have eq1 :
      xρ.1 * A.ι (conjFactorCompCoeff xσ xτ xστ) =
      A.ι (ρ <| conjFactorCompCoeff xσ xτ xστ) * xρ.1 := by
    have := xρ.2 (conjFactorCompCoeff xσ xτ xστ)
    conv_rhs => rw [this, _root_.mul_assoc]
    simp
  conv_lhs => rw [conjFactorCompCoeff_spec (z := xστ), ← _root_.mul_assoc, eq1]
  conv_rhs => rw [_root_.mul_assoc, ← conjFactorCompCoeff_spec, ← _root_.mul_assoc]

lemma conjFactorCompCoeff_comp_comp₃
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xρσ : A.conjFactor (ρ * σ)) (xστ : A.conjFactor (σ * τ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    A.ι (conjFactorCompCoeff xρ xσ xρσ) *
    A.ι (conjFactorCompCoeff xρσ xτ xρστ) *
    xρστ.1 =
    A.ι (ρ <| conjFactorCompCoeff xσ xτ xστ) *
    A.ι (conjFactorCompCoeff xρ xστ xρστ) *
    xρστ.1 := by
  rw [← conjFactorCompCoeff_comp_comp₁, ← conjFactorCompCoeff_comp_comp₂, _root_.mul_assoc]

lemma conjFactorCompCoeff_comp_comp
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xρσ : A.conjFactor (ρ * σ)) (xστ : A.conjFactor (σ * τ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    conjFactorCompCoeff xρ xσ xρσ *
    conjFactorCompCoeff xρσ xτ xρστ =
    (ρ <| conjFactorCompCoeff xσ xτ xστ) *
    conjFactorCompCoeff xρ xστ xρστ := by
  apply_fun A.ι using RingHom.injective _
  simpa using conjFactorCompCoeff_comp_comp₃ xρ xσ xτ xρσ xστ xρστ

variable (A) in
def toTwoCocycles (x_ : Π σ, A.conjFactor σ) : ((K ≃ₐ[F] K) × (K ≃ₐ[F] K)) → Kˣ :=
fun p =>
  conjFactorCompCoeffAsUnit
    (x_ p.1)
    (x_ p.2)
    (x_ <| p.1 * p.2)

variable (ρ σ τ) in
lemma toTwoCocycles_cond (x_ : Π σ, A.conjFactor σ) :
    ρ (A.toTwoCocycles x_ (σ, τ)).1 * A.toTwoCocycles x_ (ρ, σ * τ) =
    A.toTwoCocycles x_ (ρ, σ) * A.toTwoCocycles x_ (ρ * σ, τ) := by
  delta toTwoCocycles
  dsimp only [conjFactorCompCoeffAsUnit, AlgEquiv.mul_apply]
  rw [conjFactorCompCoeff_comp_comp]
  rfl

lemma isTwoCocyles (x_ : Π σ, A.conjFactor σ) :
    groupCohomology.IsMulTwoCocycle (A.toTwoCocycles x_) := by
  intro ρ σ τ
  ext : 1
  simp only [Units.val_mul]
  erw [A.toTwoCocycles_cond ρ σ τ]
  rw [mul_comm]

end single

section double

variable {σ τ : K ≃ₐ[F] K}

lemma exists_iso :
    Nonempty (A ≃ₐ[F] B) := by
  obtain ⟨D, _, _, m, n, hm, hn, ⟨isoA⟩, ⟨isoB⟩⟩ :=
    IsBrauerEquivalent.exists_common_division_algebra F A.carrier B.carrier
      (Quotient.eq''.1 (A.quot_eq.trans B.quot_eq.symm))
  have eq1 := isoA.toLinearEquiv.finrank_eq
  have eq2 := isoB.toLinearEquiv.finrank_eq
  simp only [A.dim_eq_square, LinearEquiv.finrank_eq (matrixEquivTensor F D (Fin m)).toLinearEquiv,
    finrank_tensorProduct, finrank_matrix, Fintype.card_fin] at eq1
  simp only [B.dim_eq_square, LinearEquiv.finrank_eq (matrixEquivTensor F D (Fin n)).toLinearEquiv,
    finrank_tensorProduct, finrank_matrix, Fintype.card_fin] at eq2
  have eq3 := eq1.symm.trans eq2
  haveI : FiniteDimensional F (Matrix (Fin m) (Fin m) D) :=
    LinearEquiv.finiteDimensional isoA.toLinearEquiv
  haveI : FiniteDimensional F D := by
    refine FiniteDimensional.of_injective
      ({
        toFun := fun x => Matrix.diagonal fun _ => x
        map_add' := by intros; ext i j; by_cases i = j <;> aesop
        map_smul' := by intros; ext i j; by_cases i = j <;> aesop
      } : D →ₗ[F] Matrix (Fin m) (Fin m) D) fun _ _ H => Matrix.ext_iff.2 H 0 0
  have : 0 < finrank F D := finrank_pos
  rw [Nat.mul_right_inj, ← pow_two, ← pow_two] at eq3; swap; omega
  simp only [zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj] at eq3
  subst eq3
  exact ⟨isoA.trans isoB.symm⟩

def iso : A.carrier ≃ₐ[F] B.carrier := exists_iso A B |>.some

def isoConjCoeff : Bˣ :=
  SkolemNoether' F B K (AlgHom.comp (A.iso B).toAlgHom A.ι) B.ι |>.choose

lemma isoConjCoeff_spec :
    ∀ r : K, B.ι r = (A.isoConjCoeff B) * (A.iso B <| A.ι r) * (A.isoConjCoeff B)⁻¹ :=
  SkolemNoether' F B K (AlgHom.comp (A.iso B).toAlgHom A.ι) B.ι |>.choose_spec

lemma isoConjCoeff_spec' :
    ∀ r : K, (A.isoConjCoeff B)⁻¹ * B.ι r * (A.isoConjCoeff B) = (A.iso B <| A.ι r) := by
  intro c
  rw [A.isoConjCoeff_spec B c]
  simp [_root_.mul_assoc]

lemma isoConjCoeff_spec'' (c : K) (x : A.conjFactor σ):
    B.ι (σ c) =
    (A.isoConjCoeff B * (A.iso B <| x.1) * (A.isoConjCoeff B)⁻¹) *
      B.ι c *
    (A.isoConjCoeff B * (A.iso B <| x.1⁻¹.1) * (A.isoConjCoeff B)⁻¹) := by
  have eq1 := congr(A.iso B $(x.2 c))
  have eq2 := A.isoConjCoeff_spec B (σ c)
  simp only [eq1, map_mul] at eq2
  simp only [eq2, _root_.mul_assoc, Units.mul_right_inj]
  congr 1
  simp only [← _root_.mul_assoc, Units.mul_left_inj]
  congr 1
  rw [isoConjCoeff_spec']

def pushConjFactor (x : A.conjFactor σ) : B.conjFactor σ where
  val :=
  { val := A.isoConjCoeff B * (A.iso B <| x.1) * (A.isoConjCoeff B)⁻¹
    inv := A.isoConjCoeff B * (A.iso B <| x.1⁻¹.1) * (A.isoConjCoeff B)⁻¹
    val_inv := by
      simp only [← _root_.mul_assoc, Units.inv_mul_cancel_right, Units.mul_inv_eq_one]
      simp only [_root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.mul_one]
    inv_val := by
      simp only [← _root_.mul_assoc, Units.inv_mul_cancel_right, Units.mul_inv_eq_one]
      simp only [_root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.mul_one] }
  property c := by
    simp only [Units.inv_mk]
    rw [isoConjCoeff_spec'']

@[simp] lemma pushConjFactor_coe (x : A.conjFactor σ) :
    (A.pushConjFactor B x).1.1 = A.isoConjCoeff B * (A.iso B <| x.1) * (A.isoConjCoeff B)⁻¹ :=
    rfl

def pushConjFactorCoeff (x : A.conjFactor σ) (y : B.conjFactor σ) : K :=
σ (conjFactorTwistCoeff y (A.pushConjFactor B x))

lemma pushConjFactorCoeff_spec (x : A.conjFactor σ) (y : B.conjFactor σ)  :
    y.1 = B.ι (A.pushConjFactorCoeff B x y) * (A.pushConjFactor B x).1 := by
  simpa using conjFactorTwistCoeff_spec' y (A.pushConjFactor B x)

lemma pushConjFactorCoeff_spec' (x : A.conjFactor σ) (y : B.conjFactor σ) :
    B.ι (A.pushConjFactorCoeff B x y) =
    A.isoConjCoeff B *
    A.iso B (A.ι <| A.pushConjFactorCoeff B x y) *
    (A.isoConjCoeff B)⁻¹:= by
  rw [isoConjCoeff_spec]

@[simps]
abbrev pushConjFactorCoeffAsUnit (x : A.conjFactor σ) (y : B.conjFactor σ) : Kˣ where
  val := A.pushConjFactorCoeff B x y
  inv := σ (conjFactorTwistCoeff (A.pushConjFactor B x) y)
  val_inv := by simp [pushConjFactorCoeff, ← map_mul]
  inv_val := by simp [pushConjFactorCoeff, ← map_mul]

lemma compare_conjFactorCompCoeff
    (xσ : A.conjFactor σ) (yσ : B.conjFactor σ) (xτ : A.conjFactor τ) (yτ : B.conjFactor τ)
    (xστ : A.conjFactor (σ * τ)) (yστ : B.conjFactor (σ * τ)):
    B.conjFactorCompCoeff yσ yτ yστ *
    A.pushConjFactorCoeff B xστ yστ =
    A.pushConjFactorCoeff B xσ yσ *
    σ (A.pushConjFactorCoeff B xτ yτ) *
    A.conjFactorCompCoeff xσ xτ xστ := by
  have eq1 := B.conjFactorCompCoeff_spec yσ yτ yστ
  have eq2 : yσ.1.1 * yτ.1.1 =
      (A.isoConjCoeff B) *
      A.iso B
        (A.ι (A.pushConjFactorCoeff B xσ yσ) *
          xσ.1 *
          A.ι (A.pushConjFactorCoeff B xτ yτ) *
          xτ.1) *
      (A.isoConjCoeff B)⁻¹ := by
    rw [A.pushConjFactorCoeff_spec B xσ yσ, A.pushConjFactorCoeff_spec B xτ yτ,
    pushConjFactorCoeff_spec', pushConjFactorCoeff_spec',
    pushConjFactor_coe, pushConjFactor_coe]
    simp only [_root_.mul_assoc, Units.inv_mul_cancel_left, map_mul, Units.mul_right_inj]
  rw [eq2] at eq1; clear eq2
  have eq2 : yστ.1.1 =
    A.isoConjCoeff B *
      (A.iso B <| A.ι (A.pushConjFactorCoeff B xστ yστ) * xστ.1) *
    (A.isoConjCoeff B)⁻¹ := by
    rw [A.pushConjFactorCoeff_spec B xστ yστ, pushConjFactorCoeff_spec']
    simp only [_root_.mul_assoc, AlgEquiv.mul_apply, pushConjFactor_coe, mul'_coe, map_mul,
      Units.inv_mul_cancel_left]
  rw [eq2] at eq1; clear eq2
  rw [A.isoConjCoeff_spec B] at eq1
  simp only [← _root_.mul_assoc] at eq1
  conv_rhs at eq1 =>
    rw [_root_.mul_assoc _ _ (A.isoConjCoeff B).1, Units.inv_mul, _root_.mul_one,
      _root_.mul_assoc _ _ (A.iso B _), ← map_mul]
  rw [Units.mul_left_inj, Units.mul_right_inj] at eq1
  replace eq1 := (A.iso B).injective eq1
  have eq2 : xσ.1.1 * A.ι (A.pushConjFactorCoeff B xτ yτ) * xτ.1.1 =
      A.ι (σ <| A.pushConjFactorCoeff B xτ yτ) * xσ.1.1 * xτ.1.1 := by
    have := xσ.2 (A.pushConjFactorCoeff B xτ yτ)
    rw [this]
    simp [_root_.mul_assoc]
  apply_fun (A.ι (A.pushConjFactorCoeff B xσ yσ) * ·) at eq2
  simp only [← _root_.mul_assoc] at eq2
  rw [eq2] at eq1; clear eq2
  simp only [_root_.mul_assoc] at eq1
  rw [A.conjFactorCompCoeff_spec xσ xτ xστ] at eq1
  simp only [← _root_.mul_assoc] at eq1
  rw [Units.mul_left_inj] at eq1
  apply_fun A.ι using RingHom.injective _
  simp only [map_mul, eq1]

def trivialFactorSet (c : (K ≃ₐ[F] K) → Kˣ) : ((K ≃ₐ[F] K) × (K ≃ₐ[F] K)) → Kˣ :=
fun p => c p.1 * Units.map p.1.toRingEquiv.toRingHom.toMonoidHom (c p.2) * (c (p.1 * p.2))⁻¹

lemma compare_toTwoCocycles (x_ : Π σ, A.conjFactor σ) (y_ : Π σ, B.conjFactor σ) :
    B.toTwoCocycles y_ (σ, τ) *
    A.pushConjFactorCoeffAsUnit B (x_ (σ * τ)) (y_ (σ * τ)) =
    A.pushConjFactorCoeffAsUnit B (x_ σ) (y_ σ) *
    Units.map σ (A.pushConjFactorCoeffAsUnit B (x_ τ) (y_ τ)) *
    A.toTwoCocycles x_ (σ, τ) := by
  delta toTwoCocycles
  dsimp only
  have := A.compare_conjFactorCompCoeff B
    (x_ σ) (y_ σ)
    (x_ τ) (y_ τ)
    (x_ _) (y_ _)
  simp only [← _root_.mul_assoc] at this
  ext : 1
  dsimp
  rw [this]

lemma compare_toTwoCocycles' (x_ : Π σ, A.conjFactor σ) (y_ : Π σ, B.conjFactor σ) :
    groupCohomology.IsMulTwoCoboundary (B.toTwoCocycles y_ / A.toTwoCocycles x_) := by
  fconstructor
  · refine fun σ =>
      A.pushConjFactorCoeffAsUnit B (x_ σ) (y_ σ)
  intro σ τ
  dsimp
  symm
  rw [div_eq_iff_eq_mul, div_eq_mul_inv, mul_comm (Units.map _ _)]
  simp only [_root_.mul_assoc]
  symm
  rw [inv_mul_eq_iff_eq_mul, mul_comm _ (B.toTwoCocycles y_ _)]
  symm
  erw [compare_toTwoCocycles]
  simp only [← _root_.mul_assoc]
  congr 1
  rw [mul_comm]

end double

end GoodRep

variable (F K) in
noncomputable def galAct : Rep ℤ (K ≃ₐ[F] K) :=
  Rep.ofMulDistribMulAction (K ≃ₐ[F] K) Kˣ

@[simp] lemma galAct_ρ_apply (σ : K ≃ₐ[F] K) (x : Kˣ) :
    (galAct F K).ρ σ (.ofMul x) = .ofMul (Units.map σ x) := rfl

variable [FiniteDimensional F K]

lemma mem_relativeBrGroup_iff_exists_goodRep (X : BrGroup (K := F)) :
    X ∈ RelativeBrGroup K F ↔
    Nonempty (GoodRep K X) := by
  induction X using Quotient.inductionOn' with | h X =>
  simp only [RelativeBrGroup, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk,
    Quotient.map'_mk'']
  erw [← split_iff]
  rw [isSplit_iff_dimension]
  constructor
  · rintro ⟨A, eq, i, dim⟩
    exact ⟨⟨A, eq.symm, i, dim.symm⟩⟩
  · rintro ⟨⟨A, eq, i, dim⟩⟩
    exact ⟨A, eq.symm, i, dim.symm⟩

def RelativeBrGroup.goodRep (X : RelativeBrGroup K F) : GoodRep K X.1 :=
mem_relativeBrGroup_iff_exists_goodRep X.1 |>.1 X.2 |>.some

open groupCohomology

namespace GoodRep

variable {X : BrGroup (K := F)} (A : GoodRep K X)

def toH2 (x_ : Π σ, A.conjFactor σ) : groupCohomology.H2 (galAct F K) :=
Quotient.mk'' <| twoCocyclesOfIsMulTwoCocycle (f := A.toTwoCocycles x_)
  (A.isTwoCocyles x_)

end GoodRep

def RelativeBrGroup.toSnd :  RelativeBrGroup K F → groupCohomology.H2 (galAct F K) :=
  fun X => (goodRep X).toH2 (goodRep X).aribitaryConjFactor

lemma RelativeBrGroup.toSnd_wd (X : RelativeBrGroup K F)
    (A : GoodRep K X.1) (x_ : Π σ, A.conjFactor σ) :
    toSnd X = A.toH2 x_ := by
  erw [Submodule.Quotient.eq]
  set lhs := _; change lhs ∈ _
  have : IsMulTwoCoboundary (G := K ≃ₐ[F] K) (M := Kˣ) (lhs.1) := by
    apply GoodRep.compare_toTwoCocycles'

  exact twoCoboundariesOfIsMulTwoCoboundary this |>.2

namespace GoodRep

section galois

variable {X : BrGroup (K := F)} (A : GoodRep K X)

omit [FiniteDimensional F K] in
lemma conjFactor_linearIndependent (x_ : Π σ, A.conjFactor σ) :
    LinearIndependent K (v := fun (i : K ≃ₐ[F] K) => (x_ i).1.1) := by
  classical
  by_contra! rid
  obtain ⟨J, LI, maximal⟩ := exists_maximal_independent K (fun (i : K ≃ₐ[F] K) => (x_ i).1.1)
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
    simp only [SetLike.val_smul, smul_def]
    congr 1
    simp only [B, Basis.span_apply]

  simp only [Submodule.coeSubtype, map_sum, map_smul, smul_def] at eq0
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
        simp_rw [map_mul, _root_.mul_assoc]
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


variable [IsGalois F K] in

def conjFactorBasis (x_ : Π σ, A.conjFactor σ) : Basis (K ≃ₐ[F] K) K A :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun (i : K ≃ₐ[F] K) => (x_ i).1.1)
    (A.conjFactor_linearIndependent x_)
    (by rw [A.dim_eq', IsGalois.card_aut_eq_finrank])

open DirectSum

variable [DecidableEq (K ≃ₐ[F] K)]

variable {a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ} (ha : IsMulTwoCocycle a)

variable (σ τ : K ≃ₐ[F] K)

variable (a) in
def crossProductMul :
    ((K ≃ₐ[F] K) → K) →ₗ[F] ((K ≃ₐ[F] K) → K) →ₗ[F] ((K ≃ₐ[F] K) → K) :=
  LinearMap.lsum F _ F fun σ =>
  { toFun := fun c => LinearMap.lsum F _ F fun τ =>
      { toFun := fun d => Function.update 0 (σ * τ) (c * σ d * a (σ, τ))
        map_add' := by
          intros d d'
          conv_rhs => rw [← Function.update_add]
          ext στ
          simp only [map_add, mul_add, add_mul, add_zero]
        map_smul' := by
          intros r d
          rw [← Function.update_smul]
          simp only [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply,
            smul_zero] }
    map_add' := by
      intros
      ext
      simp only [LinearMap.lsum_apply, LinearMap.coe_comp, LinearMap.coeFn_sum, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.coe_proj, LinearMap.coe_single, Function.comp_apply,
        Finset.sum_apply, Function.eval, LinearMap.add_apply, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ' _ => ?_
      simp only [Function.update_apply, Pi.zero_apply]
      split_ifs
      · simp [mul_add, add_mul]
      · simp
    map_smul' := by
      intro r c
      ext
      simp only [Algebra.smul_mul_assoc, LinearMap.lsum_apply, LinearMap.coe_comp,
        LinearMap.coeFn_sum, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_proj,
        LinearMap.coe_single, Function.comp_apply, Finset.sum_apply, Function.eval,
        RingHom.id_apply, LinearMap.smul_apply, Pi.smul_apply]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun τ' _ => ?_
      simp only [Function.update_apply, Pi.zero_apply, smul_ite, smul_zero] }

@[simp]
lemma crossProductMul_single_single (c d : K) :
    crossProductMul a (Pi.single σ c) (Pi.single τ d) =
    Pi.single (σ * τ) (c * σ d * a (σ, τ)) := by
  simp only [crossProductMul, LinearMap.lsum_apply, LinearMap.coeFn_sum, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_proj, Finset.sum_apply, Function.comp_apply,
    Function.eval]
  rw [← Finset.sum_product']
  rw [show (Pi.single (σ * τ) (c * σ d * a (σ, τ)) : (K ≃ₐ[F] K) → K) =
    Function.update (0 : (K ≃ₐ[F] K) → K) ((σ, τ).1 * (σ, τ).2)
      ((Pi.single σ c : (K ≃ₐ[F] K) → K) (σ, τ).1 *
      (σ, τ).1 ((Pi.single τ d : (K ≃ₐ[F] K) → K) τ) * a ((σ, τ).1, (σ, τ).2)) by
    simp only [Pi.single_eq_same]; rfl]
  apply Finset.sum_eq_single_of_mem (h := by simp)
  rintro ⟨σ', τ'⟩ - neq
  simp only [ne_eq, Prod.mk.injEq, not_and] at neq
  simp only [Function.update_eq_self_iff, Pi.zero_apply, mul_eq_zero, AddEquivClass.map_eq_zero_iff,
    Units.ne_zero, or_false, Pi.single_apply]
  split_ifs <;> aesop

def crossProductSMul : F →ₗ[F] ((K ≃ₐ[F] K) → K) →ₗ[F] ((K ≃ₐ[F] K) → K) where
  toFun r := LinearMap.lsum F _ F fun σ =>
    { toFun := fun c => Function.update 0 σ (r • c)
      map_add' := by
        intros
        rw [← Function.update_add]
        simp
      map_smul' := by
        intros
        rw [← Function.update_smul]
        simp only [RingHom.id_apply, smul_zero]
        rw [smul_comm] }
  map_add' := by
    intros
    ext
    simp only [LinearMap.lsum_apply, LinearMap.coe_comp, LinearMap.coeFn_sum, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.coe_proj, LinearMap.coe_single, Function.comp_apply,
      Finset.sum_apply, Function.eval, ← Finset.sum_add_distrib, LinearMap.add_apply, Pi.add_apply]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    simp only [Function.update_apply, Pi.zero_apply, Pi.single_apply]
    split_ifs <;> simp [smul_add, add_smul]
  map_smul' := by
    intros
    ext
    simp only [smul_eq_mul, LinearMap.lsum_apply, LinearMap.coe_comp, LinearMap.coeFn_sum,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_proj, LinearMap.coe_single,
      Function.comp_apply, Finset.sum_apply, Function.eval, RingHom.id_apply, LinearMap.smul_apply,
      Pi.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    simp only [Function.update_apply, Pi.zero_apply, smul_ite, smul_zero]
    split_ifs <;> simp [mul_smul]

@[simp]
lemma crossProductSMul_single (r : F) (c : K) :
    crossProductSMul r (Pi.single σ c) = Pi.single σ (r • c) := by
  simp only [crossProductSMul, LinearMap.lsum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval]

  rw [show (Pi.single σ (r • c) : (K ≃ₐ[F] K) → K) =
    Function.update (0 : (K ≃ₐ[F] K) → K) σ (r • (Pi.single σ c : (K ≃ₐ[F] K) → K) σ) by
    aesop]
  apply Finset.sum_eq_single_of_mem (h := by simp)
  intros
  aesop

structure CrossProduct {a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ} (ha : IsMulTwoCocycle a) where
  (val : (K ≃ₐ[F] K) → K)

namespace CrossProduct

instance : Add (CrossProduct ha) where
  add x y := ⟨x.val + y.val⟩

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma add_val (x y : CrossProduct ha) :
    (x + y).val = x.val + y.val := rfl

instance : Zero (CrossProduct ha) where
  zero := ⟨0⟩

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma zero_val : (0 : CrossProduct ha).val = 0 := rfl

instance : SMul ℕ (CrossProduct ha) where
  smul n x := ⟨n • x.val⟩

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma nsmul_val (n : ℕ) (x : CrossProduct ha) :
    (n • x).val = n • x.val := rfl

instance : Neg (CrossProduct ha) where
  neg x := ⟨-x.val⟩

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma neg_val (x : CrossProduct ha) :
    (-x).val = -x.val := rfl

instance : Sub (CrossProduct ha) where
  sub x y := ⟨x.val - y.val⟩

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma sub_val (x y : CrossProduct ha) :
    (x - y).val = x.val - y.val := rfl

instance : SMul ℤ (CrossProduct ha) where
  smul n x := ⟨n • x.val⟩

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma zsmul_val (n : ℤ) (x : CrossProduct ha) :
    (n • x).val = n • x.val := rfl

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
lemma val_injective : Function.Injective (CrossProduct.val (ha := ha)) := by
  rintro ⟨x⟩ ⟨y⟩ rfl
  rfl

omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[ext]
lemma ext (x y : CrossProduct ha) : x.val = y.val → x = y := by
  cases x; cases y
  simp

instance addCommGroup : AddCommGroup (CrossProduct ha) :=
  Function.Injective.addCommGroup
    (CrossProduct.val (ha := ha))
    (val_injective ha) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

@[simps]
def valAddMonoidHom : (CrossProduct ha) →+ ((K ≃ₐ[F] K) → K) :=
  { toFun := fun x => x.val,
    map_zero' := rfl,
    map_add' := fun _ _ => rfl }

@[elab_as_elim]
lemma single_induction (x : CrossProduct ha) {motive : CrossProduct ha → Prop}
    (single : ∀ (σ : K ≃ₐ[F] K) (c : K), motive ⟨Pi.single σ c⟩)
    (add : ∀ x y, motive x → motive y → motive ⟨x.val + y.val⟩)
    (zero : motive ⟨0⟩) : motive x := by
  have : x = ∑ σ : K ≃ₐ[F] K, ⟨Pi.single σ (x.val σ)⟩ := by
    ext σ
    change valAddMonoidHom ha _ _ = valAddMonoidHom ha _ _
    rw [map_sum]
    simp only [valAddMonoidHom_apply, Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ,
      ↓reduceIte]
  rw [this]
  apply Finset.sum_induction
  · apply add
  · apply zero
  · intros σ _
    apply single

instance : _root_.Mul (CrossProduct ha) where
  mul x y := ⟨crossProductMul a x.val y.val⟩

lemma mul_def (x y : CrossProduct ha) :
    x * y = ⟨crossProductMul a x.val y.val⟩ := rfl

@[simp]
lemma mul_val (x y : CrossProduct ha) :
    (x * y).val = crossProductMul a x.val y.val := rfl

instance : One (CrossProduct ha) where
  one := ⟨Pi.single 1 (a (1, 1))⁻¹⟩

omit  [FiniteDimensional F K] in
@[simp] lemma one_val : (1 : CrossProduct ha).val =
    Pi.single (1 : K ≃ₐ[F] K) (a (1, 1))⁻¹ := rfl

attribute [local simp] mul_def in
instance monoid : Monoid (CrossProduct ha) where
  mul_assoc x y z := by
    ext α
    induction x using single_induction ha with
    | single x cx =>
      induction y using single_induction ha with
      | single y cy =>
        induction z using single_induction ha with
        | single z cz =>
          simp only [mul_def, crossProductMul_single_single, AlgEquiv.mul_apply, ← _root_.mul_assoc,
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
          simp only [mul_def, crossProductMul_single_single, map_add, Pi.add_apply] at hz hz' ⊢
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
      simp only [mul_def, one_val, Prod.mk_one_one, crossProductMul_single_single, _root_.one_mul,
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
      simp only [mul_def, one_val, Prod.mk_one_one, crossProductMul_single_single, _root_.mul_one,
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

instance : Ring (CrossProduct ha) where
  __ := addCommGroup ha
  __ := monoid ha
  left_distrib := by intros; ext; simp
  right_distrib := by intros; ext; simp
  zero_mul := by intros; ext; simp
  mul_zero := by intros; ext; simp
  sub_eq_add_neg := by intros; ext; simp only [sub_val, Pi.sub_apply, add_val, neg_val,
    Pi.add_apply, Pi.neg_apply]; group
  neg_add_cancel := by intros; ext; simp

instance : SMul F (CrossProduct ha) where
  smul r x := ⟨crossProductSMul r x.1⟩

@[simp]
lemma smul_val (r : F) (x : CrossProduct ha) :
    (r • x).val = crossProductSMul r x.val := rfl

instance algebra : Algebra F (CrossProduct ha) where
  toFun r := r • 1
  map_one' := by
    ext α
    simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single, one_smul]
  map_mul' := by
    intro r r'
    ext α
    simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single, mul_smul, mul_val,
      crossProductMul_single_single, map_smul, map_inv₀, AlgEquiv.one_apply, Algebra.mul_smul_comm,
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
  commutes' := by
    intro r x
    ext α
    simp only [one_val, Prod.mk_one_one, crossProductSMul_single, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, mul_val]
    induction x using single_induction ha with
    | single x cx =>
      simp only [smul_val, one_val, Prod.mk_one_one, crossProductSMul_single,
        crossProductMul_single_single, AlgEquiv.one_apply, Algebra.smul_mul_assoc, map_smul,
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
        crossProductMul_single_single, AlgEquiv.one_apply, Algebra.smul_mul_assoc]
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
    algebraMap F (CrossProduct ha) r = r • 1 := rfl

def ι : K →ₐ[F] CrossProduct ha where
  toFun b := ⟨Pi.single 1 (b * (a (1, 1))⁻¹)⟩
  map_one' := by
    ext α
    simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, _root_.one_mul, one_val]
  map_mul' := by
    intro b b'
    ext α
    simp only [Prod.mk_one_one, Units.val_inv_eq_inv_val, mul_val, crossProductMul_single_single,
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
omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
@[simp] lemma a_one_left : a (1, σ) = a 1 := by
  have := ha 1 1 σ
  simp only [_root_.mul_one, Prod.mk_one_one, one_smul, _root_.one_mul, mul_right_inj] at this
  exact this.symm

include ha in
omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
lemma a_one_right : a (σ, 1) = Units.map σ (a 1) := by
  have := ha σ 1 1
  simp only [_root_.mul_one, Prod.mk_one_one, AlgEquiv.smul_units_def, mul_left_inj] at this
  exact this

include ha in
omit [FiniteDimensional F K] [DecidableEq (K ≃ₐ[F] K)] in
lemma a_one_right' : (a (σ, 1)).1 = σ (a 1) := congr($(a_one_right ha σ).1)

lemma identity_double_dagger (b : K) :
    ι ha b * ⟨Pi.single σ 1⟩ = ⟨Pi.single σ b⟩ := by
  ext α
  simp only [mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    crossProductMul_single_single, AlgEquiv.one_apply, _root_.mul_one]
  rw [_root_.one_mul]
  congr 1
  rw [a_one_left ha]
  simp


@[simps]
def Units.ofLeftRightInverse (G : Type*) [Monoid G] (a b c : G) (h : a * b = 1) (h' : c * a = 1) : Gˣ where
  val := a
  inv := b
  val_inv := h
  inv_val := by
    suffices b = c by
      subst this
      exact h'
    calc b
      _ = 1 * b := by rw [_root_.one_mul]
      _ = (c * a) * b := by rw [← h']
      _ = c * (a * b) := by rw [_root_.mul_assoc]
      _ = c * 1 := by rw [h]
      _ = c := by rw [_root_.mul_one]

lemma Units.ofLeftRightInverse_inv_eq1 (G : Type*) [Monoid G] (a b c : G) (h : a * b = 1) (h' : c * a = 1) :
    (Units.ofLeftRightInverse G a b c h h').inv = b := rfl

lemma Units.ofLeftRightInverse_inv_eq2 (G : Type*) [Monoid G] (a b c : G) (h : a * b = 1) (h' : c * a = 1) :
    (Units.ofLeftRightInverse G a b c h h').inv = c := by
  suffices b = c by
    subst this
    rw [ofLeftRightInverse_inv_eq1]
  calc b
      _ = 1 * b := by rw [_root_.one_mul]
      _ = (c * a) * b := by rw [← h']
      _ = c * (a * b) := by rw [_root_.mul_assoc]
      _ = c * 1 := by rw [h]
      _ = c := by rw [_root_.mul_one]

def x_ (σ : K ≃ₐ[F] K) : (CrossProduct ha)ˣ :=
  Units.ofLeftRightInverse (CrossProduct ha) ⟨Pi.single σ 1⟩
    ⟨Pi.single σ⁻¹ ((σ⁻¹ ((a (σ, σ⁻¹))⁻¹ * (a 1)⁻¹)))⟩
    ⟨Pi.single σ⁻¹ ((a (σ⁻¹, σ))⁻¹ * (a 1)⁻¹)⟩
    (by
      let x_σ : (CrossProduct ha) := ⟨Pi.single σ 1⟩
      have eq1 (b : K) := calc x_σ * ⟨Pi.single σ⁻¹ b⟩
          _ = ⟨Pi.single σ 1⟩ * ⟨Pi.single σ⁻¹ b⟩ := rfl
          _ = ⟨Pi.single 1 (σ b * a (σ, σ⁻¹))⟩ := by
              ext α
              simp only [mul_val, crossProductMul_single_single, _root_.one_mul]
              rw [mul_inv_cancel]
      specialize eq1 (σ⁻¹ ((a (σ, σ⁻¹))⁻¹ * (a 1)⁻¹))
      conv_rhs at eq1 => erw [Equiv.apply_symm_apply]
      conv_rhs at eq1 => rw [mul_comm _ (a 1)⁻¹.1, _root_.mul_assoc]

      convert eq1 using 1
      ext α
      simp only [mul_val, crossProductMul_single_single, map_one, _root_.mul_one, _root_.one_mul,
        map_mul, map_inv₀]
      simp)
    (by
      let x_σ : (CrossProduct ha) := ⟨Pi.single σ 1⟩
      have eq2 (b : K) := calc  ⟨Pi.single σ⁻¹ b⟩ * x_σ
          _ = ⟨Pi.single 1 (b * a (σ⁻¹, σ))⟩ := by
              ext α
              simp only [mul_val, crossProductMul_single_single, _root_.one_mul, map_one,
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

@[simp]
lemma x__val (σ : K ≃ₐ[F] K) :
    (x_ ha σ).val.val = Pi.single σ 1 := rfl

lemma x__inv (σ : K ≃ₐ[F] K) :
    (x_ ha σ).inv.val = Pi.single σ⁻¹ ((σ⁻¹ ((a (σ, σ⁻¹))⁻¹ * (a 1)⁻¹)) : K) := rfl

lemma x__inv' (σ : K ≃ₐ[F] K) :
    (x_ ha σ).inv.1 = Pi.single σ⁻¹ ((a (σ⁻¹, σ))⁻¹ * (a 1)⁻¹) := by
  delta x_
  rw [Units.ofLeftRightInverse_inv_eq2]
  simp

lemma x__mul : x_ ha σ * x_ ha τ = ι ha (a (σ, τ)) * x_ ha (σ * τ) := by
  ext α
  simp only [mul_val, x__val, crossProductMul_single_single, ι_apply_val, Prod.mk_one_one,
    Units.val_inv_eq_inv_val, AlgEquiv.one_apply]
  rw [_root_.one_mul]
  congr 1
  simp only [map_one, _root_.one_mul, _root_.mul_one]
  rw [a_one_left ha]
  simp

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
  rw [← identity_double_dagger ha σ (σ c)]
  rw [_root_.mul_assoc]
  change _ * ((x_ ha σ).1 * _) = _
  simp

instance : Module K (CrossProduct ha) where
  smul c x := ι ha c * x
  one_smul := by intros; show _ * _ = _; simp
  mul_smul := by intros; show _ * _ = _ * (_ * _); simp [_root_.mul_assoc]
  smul_zero := by intros; show _ * _ = _; simp
  smul_add := by intros; show _ * _ = _ * _ + _ * _; simp [mul_add]
  add_smul := by intros; show _ * _ = _ * _ + _ * _; simp [add_mul]
  zero_smul := by intros; show _ * _ = _; simp

lemma smul_def (c : K) (x : CrossProduct ha) :
    c • x = ι ha c * x := rfl

def x_AsBasis : Basis (K ≃ₐ[F] K) K (CrossProduct ha) :=
.mk (v := fun σ => (x_ ha σ).1)
  (by
    rw [linearIndependent_iff']
    intro J f hf σ hσ
    replace hf : ∑ i ∈ J, ι ha (f i) * (x_ ha i).val = (0 : CrossProduct ha) := hf
    replace hf : ∑ i ∈ J, ⟨Pi.single i (f i)⟩ = (0 : CrossProduct ha) := by
      rw [← hf]
      exact Finset.sum_congr rfl fun i hi => identity_double_dagger ha i (f i) |>.symm
    apply_fun valAddMonoidHom ha at hf
    replace hf := congr_fun hf σ
    simp only [map_sum, Finset.sum_apply, map_zero, Pi.zero_apply] at hf
    simp only [valAddMonoidHom_apply, Finset.sum_pi_single, ite_eq_else] at hf
    exact hf hσ)
  (by
    rintro x -
    induction x using single_induction ha with
    | single x cx =>
      have eq : (⟨Pi.single x cx⟩ : CrossProduct ha) = cx • ⟨Pi.single x 1⟩ := by
        change _ = ι ha _ * _
        rw [identity_double_dagger]
      rw [eq]
      refine Submodule.smul_mem _ _ <| Submodule.subset_span ⟨x, rfl⟩
    | add x x' hx hx' =>
      exact Submodule.add_mem _ hx hx'
    | zero =>
      exact Submodule.zero_mem _)

instance : IsScalarTower F K (CrossProduct ha) where
  smul_assoc := by
    intros x y z
    change ι ha (x • y) * z = x • (_ * _)
    ext α
    simp only [map_smul, Algebra.smul_mul_assoc, smul_val, mul_val, ι_apply_val, Prod.mk_one_one,
      Units.val_inv_eq_inv_val]

lemma dim_eq_square [IsGalois F K] : finrank F (CrossProduct ha) = (finrank F K)^2 := by
  have eq1 : finrank F (CrossProduct ha) = finrank F K * finrank K (CrossProduct ha) := by
    rw [finrank_mul_finrank]
  rw [finrank_eq_card_basis (x_AsBasis ha), IsGalois.card_aut_eq_finrank] at eq1
  rw [eq1, pow_two]

end CrossProduct

end galois

end GoodRep
