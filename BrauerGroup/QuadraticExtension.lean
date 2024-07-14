import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

suppress_compilation

variable {K: Type*} [Field K] [CharZero K]

@[ext]
structure Ksqrtd (d : K) where
  re : K
  im : K
  deriving DecidableEq

prefix:100 "K√" => Ksqrtd

namespace Ksqrtd

variable {d : K}
-- variable (K: Type*) [Field K] [CharZero K]
-- theorem ext : ∀ {z w : K√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
--   | ⟨x, y⟩, ⟨x', y'⟩ =>
--     ⟨fun h => by injection h; constructor <;> assumption,
--      fun ⟨h₁, h₂⟩ => by congr⟩

def ofField (n : K) : K√d := ⟨n, 0⟩

theorem ofField_re (n : K) : (ofField n : K√d).re = n := rfl


theorem ofField_im (n : K) : (ofField n : K√d).im = 0 := rfl

instance : Zero (K√d) :=
  ⟨ofField 0⟩

@[simp]
theorem zero_re : (0 : K√d).re = 0 := rfl

@[simp]
theorem zero_im : (0 : K√d).im = 0 := rfl

instance : Inhabited (K√d) :=
  ⟨0⟩

instance : One (K√d) :=
  ⟨ofField 1⟩

@[simp]
theorem one_re : (1 : K√d).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : K√d).im = 0 :=
  rfl

def sqrtd : K√d :=
  ⟨0, 1⟩

@[simp]
theorem sqrtd_re : (sqrtd : K√d).re = 0 :=
  rfl

@[simp]
theorem sqrtd_im : (sqrtd : K√d).im = 1 :=
  rfl

instance : Add (K√d) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem add_def (x y x' y' : K) : (⟨x, y⟩ + ⟨x', y'⟩ : K√d) = ⟨x + x', y + y'⟩ := rfl

@[simp]
theorem add_re (z w : K√d) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : K√d) : (z + w).im = z.im + w.im :=
  rfl

section bit
set_option linter.deprecated false

@[simp]
theorem bit0_re (z) : (bit0 z : K√d).re = bit0 z.re :=
  rfl

@[simp]
theorem bit0_im (z) : (bit0 z : K√d).im = bit0 z.im :=
  rfl

@[simp]
theorem bit1_re (z) : (bit1 z : K√d).re = bit1 z.re :=
  rfl

@[simp]
theorem bit1_im (z) : (bit1 z : K√d).im = bit0 z.im := by simp [bit1]

end bit

/-- Negation in `K√d` -/
instance : Neg (K√d) :=
  ⟨fun z => ⟨-z.1, -z.2⟩⟩

@[simp]
theorem neg_re (z : K√d) : (-z).re = -z.re :=
  rfl

@[simp]
theorem neg_im (z : K√d) : (-z).im = -z.im :=
  rfl

/-- Multiplication in `K√d` -/
instance : Mul (K√d) :=
  ⟨fun z w => ⟨z.1 * w.1 + d * z.2 * w.2, z.1 * w.2 + z.2 * w.1⟩⟩

@[simp]
theorem mul_re (z w : K√d) : (z * w).re = z.re * w.re + d * z.im * w.im :=
  rfl

@[simp]
theorem mul_im (z w : K√d) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
-- example (x:K): K := x

-- -- x 也是 Ksqrtd K 的元素
-- example (x:K): Ksqrtd K := (x : Ksqrtd K)

-- -- 使用 simp 自动处理转换
-- example (x : K) : (x : Ksqrtd K).re = x :=
-- by simp
@[simp]
instance : CoeTC K (Ksqrtd d) :=
⟨fun x => ⟨x, 0⟩⟩
-- theorem coe_Kd_to_K : (x : K) = ↑(x : K√d) := by rfl
instance addCommGroup : AddCommGroup (K√d) := by
  refine
  { add := (· + ·)
    zero := (0 : K√d)
    sub := fun a b => a + -b
    neg := Neg.neg
    nsmul := @nsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec (K√d) ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_left_neg := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp]
theorem sub_re (z w : K√d) : (z - w).re = z.re - w.re := by
  exact Eq.symm (Mathlib.Tactic.Abel.unfold_sub z.re w.re (z - w).re rfl)

@[simp]
theorem sub_im (z w : K√d) : (z - w).im = z.im - w.im := by
  exact Eq.symm (Mathlib.Tactic.Abel.unfold_sub z.im w.im (z - w).im rfl)

instance addGroupWithOne : AddGroupWithOne (K√d) :=
{ Ksqrtd.addCommGroup with
  intCast := fun z => ⟨z, 0⟩
  natCast := fun n => ⟨n, 0⟩
  natCast_zero := by simp only [CharP.cast_eq_zero]; rfl
  natCast_succ := fun _ => by ext <;> simp
  intCast_negSucc := fun _ => by
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev]
    ext <;> ring_nf
    · rw [neg_sub_left, add_comm, Nat.one_add, ← Nat.cast_one, ← Nat.cast_add, Nat.one_add]; congr
    · simp only [neg_im, zero_eq_neg]; rfl
  intCast_ofNat := fun _ => by simp only [Int.cast_natCast]; rfl
  }


instance commRing : CommRing (K√d) := by
  refine
  { Ksqrtd.addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec (K√d) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

instance : AddMonoid (K√d) := by infer_instance

instance : Monoid (K√d) := by infer_instance

instance : CommMonoid (K√d) := by infer_instance

instance : CommSemigroup (K√d) := by infer_instance

instance : Semigroup (K√d) := by infer_instance

instance : AddCommSemigroup (K√d) := by infer_instance

instance : AddSemigroup (K√d) := by infer_instance

instance : CommSemiring (K√d) := by infer_instance

instance : Semiring (K√d) := by infer_instance

instance : Ring (K√d) := by infer_instance

instance : Distrib (K√d) := by infer_instance

instance : Star (K√d) where
  star z := ⟨z.1, -z.2⟩

instance : Algebra K (K√d) :=
{
  toFun := fun r => ⟨r, 0⟩,
  smul := fun r z => ⟨r * z.1, r * z.2⟩
  map_one' := rfl
  map_zero' := by simp_all only; apply Eq.refl
  map_add' := by intro x y; simp
  map_mul' := by intro x y; simp_all only; ext <;> simp
  commutes' := fun _ _ ↦ mul_comm _ _
  smul_def' := fun _ _ ↦ by ext <;> simp <;> rfl
}


@[simp]
theorem star_mk (x y : K) : star (⟨x, y⟩ : K√d) = ⟨x, -y⟩ :=
  rfl

@[simp]
theorem star_re (z : K√d) : (star z).re = z.re :=
  rfl

@[simp]
theorem star_im (z : K√d) : (star z).im = -z.im :=
  rfl

instance : StarRing (K√d) where
  star_involutive x := Ksqrtd.ext _ _ rfl (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add a b := Ksqrtd.ext _ _ rfl (neg_add _ _)

instance nontrivial : Nontrivial (K√d) :=
  ⟨⟨0, 1, (Ksqrtd.ext_iff 0 1).not.mpr (by simp)⟩⟩

@[simp]
theorem natCast_re (n : ℕ) : (n : K√d).re = n :=
  rfl

@[simp]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : K√d).re = n :=
  rfl

@[simp]
theorem natCast_im (n : ℕ) : (n : K√d).im = 0 :=
  rfl

@[simp]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : K√d).im = 0 :=
  rfl

theorem natCast_val (n : ℕ) : (n : K√d) = ⟨n, 0⟩ :=
  rfl

@[simp]
theorem intCast_re (n : ℤ) : (n : K√d).re = n := rfl

@[simp]
theorem intCast_im (n : ℤ ) : (n : K√d).im = 0 := rfl

theorem intCast_val (n : ℤ) : (n : K√d) = ⟨n, 0⟩ := by ext <;> simp

instance : CharZero (K√d) where cast_injective m n := by simp [Ksqrtd.ext_iff]

@[simp]
theorem ratCast_re (q : ℚ) : ((q : K) : K√d).re = q := rfl

@[simp]
theorem ratCast_im (q : ℚ) : ((q : K) : K√d).im = 0 := rfl

@[simp]
theorem ofInt_eq_intCast (n : ℤ) : (ofField n : K√d) = n := rfl

@[simp]
theorem smul_val (n x y : K) : (n : K√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by ext <;> simp

theorem smul_re (a : K) (b : K√d) : (↑a * b).re = a * b.re := by simp
-- #align zsqrtd.smul_re Zsqrtd.smul_re

theorem smul_im (a : K) (b : K√d) : (↑a * b).im = a * b.im := by simp
-- #align zsqrtd.smul_im Zsqrtd.smul_im

@[simp]
theorem muld_val (x y : K) : sqrtd (d := d) * ⟨x, y⟩ = ⟨d * y, x⟩ := by ext <;> simp
-- #align zsqrtd.muld_val Zsqrtd.muld_val

@[simp]
theorem dmuld : sqrtd (d := d) * sqrtd (d := d) = d := by ext <;> simp
-- #align zsqrtd.dmuld Zsqrtd.dmuld

@[simp]
theorem smuld_val (n x y : K) : sqrtd * (n : K√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ := by ext <;> simp
-- #align zsqrtd.smuld_val Zsqrtd.smuld_val

theorem decompose {x y : K} : (⟨x, y⟩ : K√d) = x + sqrtd (d := d) * y := by ext <;> simp
-- #align zsqrtd.decompose Zsqrtd.decompose

theorem mul_star {x y : K} : (⟨x, y⟩ * star ⟨x, y⟩ : K√d) = x * x - d * y * y := by
  ext <;> simp [sub_eq_add_neg, mul_comm]
-- #align zsqrtd.mul_star Zsqrtd.mul_star

-- protected theorem coe_int_add (m n : K) : (↑(m + n) : K√d) = ↑m + ↑n := by aesop
  -- Int.cast_add m n
-- #align zsqrtd.coe_int_add Zsqrtd.coe_int_add

-- protected theorem coe_int_sub (m n : K) : (↑(m - n) : K√d) = ↑m - ↑n := by aesop
  -- Int.cast_sub m n
-- #align zsqrtd.coe_int_sub Zsqrtd.coe_int_sub

-- protected theorem coe_int_mul (m n : K) : (↑(m * n) : K√d) = ↑m * ↑n := by aesop
  -- Int.cast_mul m n
-- #align zsqrtd.coe_int_mul Zsqrtd.coe_int_mul

-- protected theorem coe_int_inj {m n : K} (h : (↑m : K√d) = ↑n) : m = n := by
  -- simpa using congr_arg re h
-- #align zsqrtd.coe_int_inj Zsqrtd.coe_int_inj

theorem intCast_dvd (z : K) (a : K√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp only [add_zero, intCast_re, zero_mul, mul_im, dvd_mul_right, and_self_iff,
      mul_re, mul_zero, intCast_im]
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    rw [smul_val, Ksqrtd.ext_iff]
    exact ⟨hr, hi⟩

@[simp]
theorem intCast_dvd_intCast (a b : K) : (a : K√d) ∣ b ↔ a ∣ b := by
  rw [intCast_dvd]
  constructor
  · rintro ⟨hre, -⟩
    simp only at hre ; exact hre
  · simp only [dvd_zero, and_true, imp_self]

section Norm

def norm (n : K√d) : K :=
  n.re * n.re - d * n.im * n.im

theorem norm_def (n : K√d) : n.norm = n.re * n.re - d * n.im * n.im :=
  rfl

@[simp]
theorem norm_zero : norm (0 : K√d) = 0 := by simp [norm]

@[simp]
theorem norm_one : norm (1 : K√d) = 1 := by simp [norm]

@[simp]
theorem norm_mul (n m : K√d) : norm (n * m) = norm n * norm m := by
  simp only [norm, mul_im, mul_re]
  ring

def normMonoidHom : K√d →* K where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one

theorem norm_eq_mul_conj (n : K√d) : (norm n : K) = n * star n := by
  ext <;> simp [norm, star, mul_comm, sub_eq_add_neg]

@[simp]
theorem norm_neg (x : K√d) : (-x).norm = x.norm := by simp [norm_def]

@[simp]
theorem norm_conj (x : K√d) : (star x).norm = x.norm := by
  simp only [norm_def, star_re, star_im, mul_neg, neg_mul, neg_neg]

-- set_option maxHeartbeats 400000 in
-- theorem norm_nonneg (d : ℚ) (hd : d ≤ 0) (n : (Ksqrtd (K := ℚ) d)) : 0 ≤ n.norm := by
--   if hn : n = 0 then subst hn; simp only [norm_zero, le_refl]
--   else
--   have h : 0 ≤ n.re * n.re := mul_self_nonneg n.re
--   have h' : 0 ≤ n.im * n.im := mul_self_nonneg n.im
--   have h'' : d * n.im * n.im ≤ 0 := by
--     rw [mul_assoc];
--     exact mul_nonpos_of_nonpos_of_nonneg hd h'
--   simp only [norm_def]
--   refine le_add_of_nonneg_of_le


def inv_of_this: K√d → K√d := fun z =>
  ⟨z.re / (z.re ^ 2 - d * z.im ^ 2), -z.im / (z.re ^ 2 - d * z.im ^ 2)⟩

instance : Inv (K√d) where
  inv := inv_of_this

instance : Div (K√d) where
  div x y := x * y⁻¹

lemma not_square_to_norm_not_zero (hd : ¬(IsSquare d)) : ∀(x : K√d), x ≠ 0 → x.norm ≠ 0 := by
  intro x hx hnx
  unfold norm at hnx
  if hxi : x.im = 0 then
    simp only [hxi, mul_zero, sub_zero, mul_eq_zero, or_self] at hnx
    apply hx ; exact Ksqrtd.ext _ _ hnx hxi
  else
    rw [← pow_two, mul_assoc, ← pow_two, sub_eq_zero] at hnx
    apply_fun fun m => m/(x.im ^ 2) at hnx
    rw [← mul_div, div_self (pow_ne_zero 2 hxi), mul_one] at hnx
    have sq_eq : x.re ^ 2 / x.im ^ 2 = (x.re / x.im) ^ 2 := by ring
    rw [sq_eq] at hnx; symm at hnx; rw [pow_two] at hnx
    have : IsSquare d := ⟨(x.re /x.im), hnx⟩ ; tauto

instance GroupWithZero (hd : ¬(IsSquare d)) : GroupWithZero (K√d) where
  inv := _
  inv_zero := by
    change inv_of_this 0 = 0; simp only [inv_of_this, zero_re, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_im, mul_zero, sub_self, div_zero, neg_zero]; rfl
  mul_inv_cancel := fun a ha ↦ by
    simp only [nsmul_eq_mul, inv_of_this]; ext
    · simp only [show a⁻¹ = inv_of_this a from rfl, inv_of_this, mul_re, one_re];
      ring_nf; rw [← sub_mul, mul_inv_cancel]
      rw [pow_two, pow_two, ← mul_assoc, ← norm_def];
      exact not_square_to_norm_not_zero hd a ha
    · simp only [show a⁻¹ = inv_of_this a from rfl, inv_of_this, mul_im, one_im]; ring


instance DivisionRing (hd : ¬(IsSquare d)): DivisionRing (K√d) :=
{ Ksqrtd.commRing with
  mul_inv_cancel := Ksqrtd.GroupWithZero hd|>.mul_inv_cancel
  inv_zero := Ksqrtd.GroupWithZero hd|>.inv_zero
  nnqsmul := _
  qsmul := _
}

instance sqrt_field (hd : ¬(IsSquare d)) : Field (K√d) :=
{ Ksqrtd.DivisionRing hd with
  mul_comm := _
}

theorem inv_norm_inv (hd : ¬(IsSquare d)) (x : K√d) : (norm x)⁻¹ = norm (x⁻¹) := by
  letI : Field (K√d) := sqrt_field hd
  if h : x = 0 then
    subst h
    simp only [norm_def, zero_re, mul_zero, zero_im, sub_self, inv_zero]
  else
  have eq1 : (norm x⁻¹) * norm x = norm (x * x⁻¹) := by rw [mul_comm]; exact norm_mul x x⁻¹ |>.symm
  rw [mul_inv_cancel h, norm_one] at eq1
  exact Eq.symm (eq_inv_of_mul_eq_one_left eq1)

theorem norm_eq_zero_iff (hd : ¬(IsSquare d)) (x : K√d) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra!
    exact (not_square_to_norm_not_zero hd x this) hx
  · intro hx
    simp [hx]

@[ext]
theorem hom_ext (q : ℚ) (f g : Ksqrtd q →ₐ[ℚ] ℝ) (h : f (sqrtd (K := ℚ)) = g (sqrtd (K := ℚ))) :
    f = g := by
  ext ⟨x, y⟩
  rw [decompose, decompose, map_add, map_add, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
    h]; change _ + _ * f 0 + _ = _ + _ * g 0 + _; simp only [map_zero, mul_zero, add_zero]
  change f (algebraMap _ _ x) + _ * f (algebraMap _ _ y) = g (algebraMap _ _ x) +
    _ * g (algebraMap _ _ y)
  simp only [AlgHom.commutes, eq_ratCast]

@[simps]
def lift (q : ℚ): { r : ℝ // r * r = ↑q } ≃ (Ksqrtd q →ₐ[ℚ] ℝ) where
  toFun r :=
    { toFun := fun a => a.1 + a.2 * (r : ℝ)
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [add_re, Rat.cast_add, add_im]
        ring
      map_one' := by simp
      map_mul' := fun a b => by
        have :
          (a.re + a.im * r : ℝ) * (b.re + b.im * r) =
            a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) := by
          ring
        simp only [mul_re, Rat.cast_add, Rat.cast_mul, mul_im, this, r.prop]
        ring
      commutes' := fun k => by
        simp only [Algebra.id.map_eq_id, RingHom.id_apply]
        rw [show algebraMap _ _ k = (k : Ksqrtd q) from rfl]
        simp only [Rat.cast_zero, zero_mul, add_zero, eq_ratCast]
      }
  invFun f := ⟨f sqrtd, by
    rw [← f.map_mul, dmuld, show ⟨q, 0⟩ = q • (1 : Ksqrtd q) by
      ext; change q = _ ; rw [← Algebra.algebraMap_eq_smul_one]; change q = (q : Ksqrtd q).re; rfl;
      change 0 = _ ; rw [← Algebra.algebraMap_eq_smul_one]; change 0 = (q : Ksqrtd q).im; rfl]; simp⟩
  left_inv r := by
    ext
    simp
  right_inv f := by
    refine hom_ext q _ _ ?_
    simp

/-- `lift r` is injective if `d` is non-square, and R has characteristic zero (that is, the map from
`ℤ` into `R` is injective). -/
theorem lift_injective (q : ℚ) (r : { r : ℝ // r * r = ↑q })
    (hd : ¬(IsSquare q)) : Function.Injective (lift q r) :=
  (injective_iff_map_eq_zero (lift q r)).mpr fun a ha => by
    suffices lift q r a.norm = 0 by
      simp only [ratCast_re, add_zero, lift_apply_apply, ratCast_im, Rat.cast_zero,
        zero_mul, Rat.cast_eq_zero] at this
      rw [(norm_eq_zero_iff hd a).1]; exact this
    rw [norm_eq_mul_conj, map_mul, ha, zero_mul]

@[simps!]
def toReal (q : ℚ) (h : 0 ≤ q) : Ksqrtd q →ₐ[ℚ] ℝ :=
  lift q ⟨_, Real.mul_self_sqrt (Rat.cast_nonneg.mpr h)⟩

theorem toReal_injective {q : ℚ} (h0d : 0 ≤ q) (hd : ¬(IsSquare q)) :
    Function.Injective (toReal q h0d) := lift_injective q _ hd

end Norm

end Ksqrtd
