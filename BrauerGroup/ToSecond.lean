import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.Algebra.DirectSum.Ring

import BrauerGroup.Subfield.Splitting
import Mathlib.Algebra.BigOperators.Finsupp
import BrauerGroup.Subfield.Subfield

suppress_compilation

open FiniteDimensional BrauerGroup

variable {F K : Type} [Field K] [Field F] [Algebra F K]
variable (X : BrGroup (K := F))

variable (K) in
structure GoodRep where
carrier : CSA.{0} F
quot_eq : (Quotient.mk'' carrier) = X
ι : K →ₐ[F] carrier
dim_eq_square : Module.finrank F carrier = (Module.finrank F K) ^ 2

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
  change Module.finrank F A = Module.finrank F A.ι.range * Module.finrank F A.ι.range
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

lemma dim_eq' [FiniteDimensional F K] : Module.finrank K A = Module.finrank F K := by
  have : Module.finrank F A = Module.finrank F K * Module.finrank K A :=
    Eq.symm (Module.finrank_mul_finrank F K A.carrier.carrier)
  rw [A.dim_eq_square, pow_two] at this
  simp only [mul_eq_mul_left_iff] at this
  refine this.recOn Eq.symm fun rid => ?_
  have : 0 < Module.finrank F K := Module.finrank_pos
  omega

end basic

section single

variable (ρ σ τ : K ≃ₐ[F] K)

def conjFactor : (σ : K ≃ₐ[F] K) → Type :=
  fun σ => { a : Aˣ //  ∀ x : K, A.ι (σ x) = a * A.ι x * a⁻¹ }

def arbitraryConjFactor : A.conjFactor σ :=
⟨SkolemNoether' F A K A.ι (A.ι.comp σ) |>.choose,
  SkolemNoether' F A K A.ι (A.ι.comp σ) |>.choose_spec⟩

variable {A ρ σ τ}

@[simp] lemma conjFactor_prop (x : A.conjFactor σ) (c : K) :
    x.1 * A.ι c * x.1⁻¹ = A.ι (σ c) := x.2 c |>.symm

def mul' (x : A.conjFactor σ) (y : A.conjFactor τ) : A.conjFactor (σ * τ) :=
⟨x.1 * y.1, fun c => by
  simp only [AlgEquiv.mul_apply, Units.val_mul, _root_.mul_assoc, mul_inv_rev]
  rw [← _root_.mul_assoc (A.ι c), ← mul_assoc (y.1 : A), ← mul_assoc (y.1 : A),
    conjFactor_prop, ← _root_.mul_assoc, conjFactor_prop]⟩

instance : HMul (A.conjFactor σ) (A.conjFactor τ) (A.conjFactor (σ * τ)) where
  hMul := mul'

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

lemma conjFactorTwistCoeff_inv (x y : A.conjFactor σ) :
    conjFactorTwistCoeff x y = (conjFactorTwistCoeff y x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp

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

@[simps]
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

lemma conjFactorCompCoeff_spec'_ (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι (conjFactorCompCoeffAsUnit x y z)⁻¹ * (x.1 * y.1 : A) = z.1 := by
  rw [conjFactorCompCoeff_spec (z := z), ← _root_.mul_assoc, ← map_mul]
  simp only [conjFactorCompCoeffAsUnit, AlgEquiv.mul_apply]
  rw [inv_mul_cancel₀, map_one, _root_.one_mul]
  exact Units.ne_zero (conjFactorCompCoeffAsUnit x y z)

lemma conjFactorCompCoeff_spec' (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι (σ <| τ <| conjFactorTwistCoeff z (mul' x y)) * (x.1 * y.1 : A) = z.1 := by
  convert conjFactorCompCoeff_spec'_ x y z using 3
  norm_cast

lemma conjFactorCompCoeff_spec'' (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι (conjFactorCompCoeff x y z) = x.1 * y.1 * z.1⁻¹ := by
  field_simp
  rw [← A.conjFactorCompCoeff_spec' x y z]
  simp only [conjFactorCompCoeff, ← _root_.mul_assoc, ← map_mul, conjFactorTwistCoeff_swap, map_one,
    _root_.one_mul]

lemma conjFactorCompCoeff_inv (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι ((conjFactorCompCoeff x y z)⁻¹) = z.1 * (y.1⁻¹ * x.1⁻¹) := by
  suffices eq : Units.map A.ι (conjFactorCompCoeffAsUnit x y z)⁻¹ = z.1 * (y.1⁻¹ * x.1⁻¹) by
    rw [Units.ext_iff] at eq
    simp only [conjFactorCompCoeffAsUnit, Units.inv_mk, Units.coe_map, MonoidHom.coe_coe,
      AlgEquiv.mul_apply, Units.val_mul] at eq
    rw [← eq]
    congr 1
    symm
    apply eq_inv_of_mul_eq_one_left
    simp only [conjFactorCompCoeff, ← map_mul, conjFactorTwistCoeff_swap, map_one]
  rw [map_inv]
  rw [inv_eq_iff_mul_eq_one]
  ext
  simp only [conjFactorCompCoeffAsUnit, AlgEquiv.mul_apply, Units.val_mul, Units.coe_map,
    MonoidHom.coe_coe, Units.val_one]
  rw [conjFactorCompCoeff_spec'']
  field_simp


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
  simp only [A.dim_eq_square, LinearEquiv.finrank_eq (matrixEquivTensor (Fin m) F D).toLinearEquiv,
    Module.finrank_tensorProduct, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
    _root_.mul_one] at eq1
  simp only [B.dim_eq_square, LinearEquiv.finrank_eq (matrixEquivTensor (Fin n) F D).toLinearEquiv,
    Module.finrank_tensorProduct, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
    _root_.mul_one] at eq2
  have eq3 := eq1.symm.trans eq2
  haveI : FiniteDimensional F D := is_fin_dim_of_wdb _ _ _ _ isoB
  have : 0 < Module.finrank F D := Module.finrank_pos
  rw [Nat.mul_right_inj, ← pow_two, ← pow_two] at eq3; swap; omega
  simp only [zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀] at eq3
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
    y.1 = B.ι (A.pushConjFactorCoeff B x y) * (A.pushConjFactor B x).1 :=
  conjFactorTwistCoeff_spec' y (A.pushConjFactor B x)

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
  dsimp only [AlgEquiv.smul_units_def, Pi.div_apply]
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
  fun X => (goodRep X).toH2 (goodRep X).arbitraryConjFactor

lemma RelativeBrGroup.toSnd_wd (X : RelativeBrGroup K F)
    (A : GoodRep K X.1) (x_ : Π σ, A.conjFactor σ) :
    toSnd X = A.toH2 x_ := by
  simp only [toSnd, GoodRep.toH2]
  change H2π _ _ = H2π _ _
  rw [← sub_eq_zero, ← map_sub]
  rw [H2π_eq_zero_iff]
  set lhs := _; change lhs ∈ _
  have : IsMulTwoCoboundary (G := K ≃ₐ[F] K) (M := Kˣ) (lhs) := by
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

  simp only [Submodule.coe_subtype, map_sum, map_smul, smul_def] at eq0
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
  simp only [Function.update_eq_self_iff, Pi.zero_apply, mul_eq_zero, EmbeddingLike.map_eq_zero_iff,
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
  algebraMap := {
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
  }
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

lemma identity_double_cross (b : K) :
    ι ha b * ⟨Pi.single σ 1⟩ = ⟨Pi.single σ b⟩ := by
  ext α
  simp only [mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    crossProductMul_single_single, AlgEquiv.one_apply, _root_.mul_one]
  rw [_root_.one_mul]
  congr 1
  rw [a_one_left ha]
  simp

lemma identity_double_cross' (b c : K) :
    ι ha b * ⟨Pi.single σ c⟩ = ⟨Pi.single σ (b*c)⟩ := by
  ext α
  simp only [mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    crossProductMul_single_single, AlgEquiv.one_apply]
  rw [_root_.one_mul]
  congr 1
  rw [a_one_left ha]
  field_simp

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
              rw [mul_val, crossProductMul_single_single, map_one,
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
  rw [← identity_double_cross ha σ (σ c)]
  rw [_root_.mul_assoc]
  change _ * ((x_ ha σ).1 * _) = _
  simp

lemma x__conj' (c : K) : x_ ha σ * ι ha c = ι ha (σ c) * (x_ ha σ) := by
  rw [← x__conj]
  simp only [Units.inv_mul_cancel_right]

instance module : Module K (CrossProduct ha) where
  smul c x := ι ha c * x
  one_smul := by intros; show _ * _ = _; simp
  mul_smul := by intros; show _ * _ = _ * (_ * _); simp [_root_.mul_assoc]
  smul_zero := by intros; show _ * _ = _; simp
  smul_add := by intros; show _ * _ = _ * _ + _ * _; simp [mul_add]
  add_smul := by intros; show _ * _ = _ * _ + _ * _; simp [add_mul]
  zero_smul := by intros; show _ * _ = _; simp

lemma smul_def (c : K) (x : CrossProduct ha) :
    c • x = ι ha c * x := rfl

lemma smul_single (c d : K) (σ : K ≃ₐ[F] K) :
    c • (⟨Pi.single σ d⟩ : CrossProduct ha) = ⟨Pi.single σ (c * d)⟩ := by
  apply val_injective ha
  simp only [smul_def, mul_val, ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
    crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply, a_one_left ha, Pi.single_inj]
  rw [show ∀ (a b c d : K), a * b * c * d = (a * c) * (b * d) by intros; ring]
  simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
    _root_.mul_one]

def x_AsBasis : Basis (K ≃ₐ[F] K) K (CrossProduct ha) :=
.mk (v := fun σ => (x_ ha σ).1)
  (by
    rw [linearIndependent_iff']
    intro J f hf σ hσ
    replace hf : ∑ i ∈ J, ι ha (f i) * (x_ ha i).val = (0 : CrossProduct ha) := hf
    replace hf : ∑ i ∈ J, ⟨Pi.single i (f i)⟩ = (0 : CrossProduct ha) := by
      rw [← hf]
      exact Finset.sum_congr rfl fun i _ => identity_double_cross ha i (f i) |>.symm
    apply_fun valAddMonoidHom ha at hf
    replace hf := congr_fun hf σ
    simp only [map_sum, Finset.sum_apply, map_zero, Pi.zero_apply] at hf
    simp only [valAddMonoidHom_apply, Finset.sum_pi_single, ite_eq_right_iff] at hf
    exact hf hσ)
  (by
    rintro x -
    induction x using single_induction ha with
    | single x cx =>
      have eq : (⟨Pi.single x cx⟩ : CrossProduct ha) = cx • ⟨Pi.single x 1⟩ := by
        change _ = ι ha _ * _
        rw [identity_double_cross]
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

@[simp]
lemma x_AsBasis_apply (σ : K ≃ₐ[F] K) :
    x_AsBasis ha σ = ⟨Pi.single σ 1⟩ := by simp [x_AsBasis, x_]

lemma one_in_x_AsBasis :
    (1 : CrossProduct ha) = (a (1, 1))⁻¹ • x_AsBasis ha 1 := by
  apply val_injective ha
  erw [smul_def]
  simp only [one_val, Prod.mk_one_one, Units.val_inv_eq_inv_val, x_AsBasis_apply, mul_val,
    ι_apply_val, crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
    isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right]

lemma single_in_xAsBasis (c : K) (σ : K ≃ₐ[F] K) :
    ⟨Pi.single σ c⟩ = c • x_AsBasis ha σ := by
  apply val_injective ha
  simp only [x_AsBasis_apply, smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
    Units.val_inv_eq_inv_val, crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply,
    _root_.mul_one, a_one_left ha, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
    IsUnit.inv_mul_cancel_right]

lemma mul_single_in_xAsBasis (c d : K) (σ τ : K ≃ₐ[F] K) :
    ⟨Pi.single σ c⟩ * ⟨Pi.single τ d⟩ = (c * σ d * a (σ, τ)) • x_AsBasis ha (σ * τ) := by
  apply val_injective ha
  simp only [mul_val, crossProductMul_single_single, x_AsBasis_apply, smul_def, map_mul,
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


lemma dim_eq_square [IsGalois F K] : Module.finrank F (CrossProduct ha) =
    (Module.finrank F K)^2 := by
  have eq1 : Module.finrank F (CrossProduct ha) = Module.finrank F K *
      Module.finrank K (CrossProduct ha) := by
    rw [Module.finrank_mul_finrank]
  rw [Module.finrank_eq_card_basis (x_AsBasis ha), IsGalois.card_aut_eq_finrank] at eq1
  rw [eq1, pow_two]

lemma one_def : (1 : CrossProduct ha) = (a 1).1⁻¹ • x_AsBasis ha 1 := by
  ext1
  simp only [one_val, Prod.mk_one_one, x_AsBasis_apply, smul_def, mul_val, ι_apply_val,
    Units.val_inv_eq_inv_val, crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
    isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right]

lemma x__conj'' (c : K) : x_AsBasis ha σ * ι ha c = (σ c) • (x_AsBasis ha σ) := by
  simpa using x__conj' ha σ c

lemma x_AsBasis_mul : x_AsBasis ha σ * x_AsBasis ha τ = (a (σ, τ)).1 • x_AsBasis ha (σ * τ) := by
  have := x__mul ha σ τ
  simp only [x_, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Units.val_ofLeftRightInverse,
    mul_inv_rev, AlgEquiv.mul_apply, x_AsBasis_apply] at this ⊢
  rw [this, smul_def]

lemma is_central [IsGalois F K] : Subalgebra.center F (CrossProduct ha) ≤ ⊥ := by
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
  { toFun := fun σ  => σ * τ⁻¹
    invFun := fun σ => σ * τ
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

    rw [smul_single, _root_.mul_one, show (⟨Pi.single 1 (s 1)⟩ : CrossProduct ha) =
      ι ha (s 1 * a 1) by apply val_injective ha; simp,
      show ι ha (s 1 * a 1) = (s 1 * a 1) • (1 : CrossProduct ha) by
        rw [smul_def];  apply val_injective ha; simp]
    obtain ⟨f, hf⟩ := conclusion3
    rw [← hf, show algebraMap F K f • (1 : CrossProduct ha) = f • 1 by
      rw [Algebra.smul_def]
      simp only [algebraMap_smul, algebraMap_val, _root_.mul_one]]
    apply Subalgebra.smul_mem _ (Subalgebra.one_mem ⊥)
  · specialize conclusion1 σ h
    rw [conclusion1]
    rw [zero_smul]
    exact Subalgebra.zero_mem _

instance : Nontrivial (CrossProduct ha) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have := congr($(h).val 1)
    simp only [zero_val, Pi.zero_apply, one_val, Prod.mk_one_one, Pi.single_eq_same,
      zero_eq_inv] at this
    exact Units.ne_zero _ this.symm⟩

namespace is_simple_proofs

variable (I : TwoSidedIdeal (CrossProduct ha))
variable {ha}

def π : (CrossProduct ha) →+* I.ringCon.Quotient := I.ringCon.mk'

def πRes : (ι ha).range →+* I.ringCon.Quotient :=
  RingHom.domRestrict (π I) (ι ha).range

variable {I} in
def x : (πRes I).range → K := fun x => x.2.choose.2.choose

lemma hx (a : πRes I |>.range) : πRes I ⟨ι ha (x a), by simp⟩ = a := by
  rw [← a.2.choose_spec]
  congr 1
  ext : 1
  exact a.2.choose.2.choose_spec

lemma hx' (a : K) : πRes I ⟨ι ha a, by simp⟩ = I.ringCon.mk' (ι ha a) := by
  simp only [RingHom.restrict_apply, πRes, π]

lemma x_wd (c c' : K) (eq : πRes I ⟨ι ha c, by simp⟩ = πRes I ⟨ι ha c', by simp⟩)
    (y : CrossProduct ha) :
    (c - c') • y ∈ I := by
  simp only [RingHom.restrict_apply, πRes, π] at eq
  erw [Quotient.eq''] at eq
  change I.ringCon _ _ at eq
  rw [TwoSidedIdeal.rel_iff, ← map_sub] at eq
  exact I.mul_mem_right _ _ eq

instance (priority := high) : SMul (RingHom.range <| πRes I) I.ringCon.Quotient where
  smul := fun a => Quotient.map'
    (fun y => x a • y) (by
      rintro y y' (hy : I.ringCon _ _)
      show I.ringCon _ _
      simp only
      rw [TwoSidedIdeal.rel_iff] at hy ⊢
      rw [← smul_sub]
      apply I.mul_mem_left _ _ hy)

lemma smul_def_quot (a : RingHom.range <| πRes I) (y : CrossProduct ha) :
    (a • (I.ringCon.mk' y : I.ringCon.Quotient) : I.ringCon.Quotient) =
    (Quotient.mk'' (x a • y)) := rfl

lemma smul_def_quot' (a : K) (y : CrossProduct ha) :
    ((⟨π I (ι ha a), ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩ : RingHom.range <| πRes I) •
      (I.ringCon.mk' y : I.ringCon.Quotient) : I.ringCon.Quotient) =
    (I.ringCon.mk' (a • y)) := by
  erw [smul_def_quot, Quotient.eq'']
  change I.ringCon _ _
  rw [I.rel_iff, ← sub_smul]
  apply x_wd
  rw [hx, hx']
  rfl

lemma smul_def_quot'' (a : K) (y : CrossProduct ha) :
  (((⟨π I (ι ha a), ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩⟩ : RingHom.range <| πRes I) •
      (by exact Quotient.mk'' y : I.ringCon.Quotient) : I.ringCon.Quotient)) =
    (Quotient.mk'' (a • y) :  I.ringCon.Quotient) :=
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
  { toFun := fun a => ⟨π I (ι ha a), by simpa using ⟨ι ha a, ⟨a, rfl⟩, rfl⟩⟩
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

def basis (ne_top : I ≠ ⊤) : Basis (K ≃ₐ[F] K) K I.ringCon.Quotient :=
  .mk (v := fun σ => I.ringCon.mk' (x_ ha σ))
    (by
      classical
      by_contra rid
      obtain ⟨J, LI, maximal⟩ := exists_maximal_independent K (fun (i : K ≃ₐ[F] K) =>
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

def π₁ (ne_top : I ≠ ⊤) : CrossProduct ha ≃ₗ[K] (I.ringCon.Quotient) :=
  Basis.equiv (x_AsBasis ha) (basis I ne_top) (Equiv.refl _)

def π₂ : CrossProduct ha →ₗ[K] (I.ringCon.Quotient) where
  __ := π I
  map_smul' := fun c x => by
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
instance is_simple : IsSimpleRing (CrossProduct ha) :=
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

instance [IsGalois F K] : Algebra.IsCentral F (CrossProduct ha) where
  out := is_central ha

instance [IsGalois F K] : FiniteDimensional F (CrossProduct ha) :=
  .of_finrank_eq_succ (n := (Module.finrank F K)^2 - 1) (by
    rw [dim_eq_square]
    rw [← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos]
    apply pow_two_pos_of_ne_zero
    have : 0 < Module.finrank F K := Module.finrank_pos
    omega)

def asCSA [IsGalois F K] : CSA F :=
⟨CrossProduct ha⟩

end CrossProduct

end galois

end GoodRep

namespace RelativeBrGroup

section from_two

open GoodRep.CrossProduct

variable [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

def fromTwoCocycles (a : twoCocycles (galAct F K)) : RelativeBrGroup K F :=
⟨Quotient.mk'' ⟨asCSA (isMulTwoCocycle_of_mem_twoCocycles _ a.2)⟩, by
  rw [mem_relativeBrGroup_iff_exists_goodRep]
  exact ⟨⟨⟨asCSA (isMulTwoCocycle_of_mem_twoCocycles _ a.2)⟩, rfl,
    ι (isMulTwoCocycle_of_mem_twoCocycles _ a.2),
    dim_eq_square (isMulTwoCocycle_of_mem_twoCocycles _ a.2)⟩⟩⟩

variable (F K) in
set_option maxHeartbeats 500000 in
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
    letI : Module K A := inferInstanceAs <| Module K (GoodRep.CrossProduct ha)
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
            ι_apply_val, GoodRep.crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
            isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
            IsUnit.inv_mul_cancel_right], map_smul]
        erw [Basis.equiv_apply]
        simp only [Units.val_inv_eq_inv_val, Equiv.refl_apply, Basis.unitsSMul_apply, basis]
        apply val_injective hb
        erw [GoodRep.CrossProduct.smul_def, GoodRep.CrossProduct.smul_def]
        erw [mul_val, mul_val]
        erw [x_AsBasis_apply]
        simp only [ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
          GoodRep.crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
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
            rw [show (⟨Pi.single σ α⟩ : GoodRep.CrossProduct ha) * ⟨Pi.single τ β⟩ =
              ⟨Pi.single (σ * τ) (α * σ β * a (σ, τ))⟩ by
              apply val_injective
              simp only [mul_val, GoodRep.crossProductMul_single_single],
              show (⟨Pi.single (σ * τ) (α * σ β * a (σ, τ))⟩ : GoodRep.CrossProduct ha) =
                (α * σ β * a (σ, τ)) • ((x_AsBasis ha (σ * τ)) : GoodRep.CrossProduct ha) by
              apply val_injective
              simp only [x_AsBasis_apply, smul_def, map_mul, mul_val, ι_apply_val, Prod.mk_one_one,
                Units.val_inv_eq_inv_val, GoodRep.crossProductMul_single_single, _root_.mul_one,
                AlgEquiv.one_apply, map_inv₀, _root_.one_mul, Pi.single_inj]
              rw [a_one_left ha]
              simp only [_root_.mul_assoc]
              congr 1
              simp only [← _root_.mul_assoc]
              simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
                IsUnit.inv_mul_cancel_right]
              field_simp, map_smul,
              show (⟨Pi.single σ α⟩ : GoodRep.CrossProduct ha) = α • (x_AsBasis ha σ) by
              apply val_injective
              simp only [x_AsBasis_apply, smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
                Units.val_inv_eq_inv_val, GoodRep.crossProductMul_single_single, _root_.one_mul,
                AlgEquiv.one_apply, _root_.mul_one, a_one_left ha, isUnit_iff_ne_zero, ne_eq,
                Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right], map_smul,
              show (⟨Pi.single τ β⟩ : GoodRep.CrossProduct ha) = β • (x_AsBasis ha τ) by
              apply val_injective
              simp only [x_AsBasis_apply, smul_def, mul_val, ι_apply_val, Prod.mk_one_one,
                Units.val_inv_eq_inv_val, GoodRep.crossProductMul_single_single, _root_.one_mul,
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
              GoodRep.crossProductMul_single_single, _root_.mul_one, AlgEquiv.one_apply,
              _root_.one_mul]
            repeat erw [mul_val]
            simp only [ι_apply_val, Prod.mk_one_one, Units.val_inv_eq_inv_val,
              GoodRep.crossProductMul_single_single, _root_.one_mul, AlgEquiv.one_apply,
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
  have ha : IsMulTwoCocycle a := isMulTwoCocycle_of_mem_twoCocycles _ ha'
  simp only [Function.comp_apply, fromSnd_wd, id_eq]
  let A : GoodRep K (Quotient.mk'' <| asCSA ha) :=
    ⟨asCSA ha, rfl, ι ha, dim_eq_square ha⟩

  let y_ : Π σ, A.conjFactor σ := fun σ => ⟨x_ ha σ, fun c => by erw [x__conj ha σ]; rfl⟩
  rw [toSnd_wd (A := A) (x_ := y_)]
  let b : ((K ≃ₐ[F] K) × (K ≃ₐ[F] K)) → Kˣ := A.toTwoCocycles y_

  rw [show A.toH2 y_ = Quotient.mk'' ⟨b, _⟩ by rfl]
  change H2π _ _ = H2π _ _
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]

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
  rw [toSnd_wd (A := A) (x_ := A.arbitraryConjFactor)]
  ext : 1
  conv_rhs => rw [← A.quot_eq]
  simp only [GoodRep.toH2, fromSnd_wd]
  rw [Quotient.eq'']
  apply IsBrauerEquivalent.iso_to_eqv
  set lhs := _
  change lhs ≃ₐ[F] A
  letI : Module K lhs := inferInstanceAs <| Module K (GoodRep.CrossProduct _)
  let φ0 : lhs ≃ₗ[K] A :=
    Basis.equiv (x_AsBasis _) (A.conjFactorBasis (A.arbitraryConjFactor)) (Equiv.refl _)
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
    have := A.conjFactorCompCoeff_spec' (A.arbitraryConjFactor 1)
      (A.arbitraryConjFactor 1)
      (A.arbitraryConjFactor (1 * 1))
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
        rw [(A.arbitraryConjFactor x).2 d]
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
