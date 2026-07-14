module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

/-!
# Indexing a cyclic group by `ZMod`, and the carry function

For a generator `σ` of a finite group (`hσ : ∀ x, x ∈ Subgroup.zpowers σ`) we define the
exponent map `genExp σ hσ : G → ZMod (orderOf σ)`, inverse to `i ↦ σ ^ i.val`, together with
its arithmetic (`genExp_pow`, `pow_genExp_val`, `genExp_mul`).

We also define the integer-valued *carry* of adding two residues in `ZMod n`. Its 2-cocycle
identity `carry_add_carry_add_left/right` is the combinatorial heart of cyclic crossed
products: the factor set of the cyclic algebra `(K/F, σ, a)` is `a ^ carry i j`.

The `carry` definitions and lemmas are adapted from the ClassFieldTheory project
(https://github.com/kbuzzard/ClassFieldTheory, Apache 2.0 — authors Yaël Dillies, Aaron Liu).
-/

@[expose] public section

namespace ZMod

variable {n : ℕ}

/-- The carry of adding two residues: `0` or `1` according to whether `val i + val j`
overflows `n`. Integer-valued so that it can be used as a `zpow` exponent. -/
def carry (i j : ZMod n) : ℤ := ((i.cast : ℤ) + j.cast - (i + j).cast) / n

lemma carry_eq_ite [NeZero n] (i j : ZMod n) :
    carry i j = if n ≤ i.val + j.val then 1 else 0 := by
  zify
  simp only [carry, ZMod.cast_add_eq_ite, ZMod.natCast_val]
  split_ifs
  · rw [sub_sub_cancel, Int.ediv_self (by exact_mod_cast NeZero.ne n)]
  · rw [sub_self, Int.zero_ediv]

lemma carry_comm (i j : ZMod n) : carry i j = carry j i := by simp [carry, add_comm]

@[simp] lemma carry_zero_left (j : ZMod n) : carry 0 j = 0 := by
  simp [carry]

@[simp] lemma carry_zero_right (i : ZMod n) : carry i 0 = 0 := by
  rw [carry_comm, carry_zero_left]

lemma carry_add_carry_add_left (i j k : ZMod n) :
    carry i j + carry (i + j) k = ((i.cast : ℤ) + j.cast + k.cast - (i + j + k).cast) / n := by
  obtain rfl | h := eq_zero_or_neZero n
  · simp [carry]
  rw [carry, carry,
    ← Int.add_ediv_of_dvd_left <| by simp [← ZMod.intCast_zmod_eq_zero_iff_dvd]]
  congr 1
  ring

lemma carry_add_carry_add_right (i j k : ZMod n) :
    carry j k + carry i (j + k) = ((i.cast : ℤ) + j.cast + k.cast - (i + j + k).cast) / n := by
  rw [carry_comm i, carry_add_carry_add_left, ← add_rotate, ← add_rotate i]

/-- The 2-cocycle identity for `carry`. -/
lemma carry_cocycle (i j k : ZMod n) :
    carry (i + j) k + carry i j = carry j k + carry i (j + k) := by
  rw [add_comm (carry (i + j) k), carry_add_carry_add_left, carry_add_carry_add_right]

end ZMod

section GenExp

variable {G : Type*} [Group G] [Finite G] (σ : G) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

open Subgroup

/-- In a finite group, every element has nonzero order. -/
instance : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩

omit [Finite G] in
include hσ in
lemma natCard_eq_orderOf : Nat.card G = orderOf σ :=
  (Nat.card_congr (Equiv.subtypeUnivEquiv hσ)).symm.trans (Nat.card_zpowers σ)

/-- The exponent of `x` with respect to a generator `σ` of `G`: the unique `i : ZMod (orderOf σ)`
with `σ ^ i.val = x`. A thin (reducible) layer over mathlib's `zmodMulEquivOfGenerator`;
downstream proofs should use the spec lemmas `genExp_pow`, `pow_genExp_val`, `genExp_mul`. -/
noncomputable abbrev genExp (x : G) : ZMod (orderOf σ) :=
  ((zmodMulEquivOfGenerator hσ (natCard_eq_orderOf σ hσ)).symm x).toAdd

omit [Finite G] in
@[simp] lemma genExp_pow (i : ℕ) : genExp σ hσ (σ ^ i) = (i : ZMod (orderOf σ)) := by
  rw [genExp, show σ ^ i = σ ^ (i : ℤ) from (zpow_natCast σ i).symm,
    zmodMulEquivOfGenerator_symm_apply_zpow, toAdd_ofAdd, Int.cast_natCast]

omit [Finite G] in
@[simp] lemma genExp_one : genExp σ hσ 1 = 0 := by
  simp

lemma pow_genExp_val (x : G) : σ ^ (genExp σ hσ x).val = x := by
  have h : (((genExp σ hσ x).val : ℤ) : ZMod (orderOf σ)) = genExp σ hσ x := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [← zpow_natCast, ← zmodMulEquivOfGenerator_apply_ofAdd_intCast hσ
    (natCard_eq_orderOf σ hσ), h, genExp, ofAdd_toAdd, MulEquiv.apply_symm_apply]

omit [Finite G] in
lemma genExp_mul (x y : G) : genExp σ hσ (x * y) = genExp σ hσ x + genExp σ hσ y := by
  simp [genExp, map_mul]

include hσ in
attribute [local instance] Fintype.ofFinite in
lemma prod_univ_eq_prod_range_pow [Fintype G] {M} [CommMonoid M] (φ : G → M) :
    ∏ g : G, φ g = ∏ k ∈ Finset.range (orderOf σ), φ (σ ^ k) := by
  have eq1 : Finset.univ (α := G) = (zpowers σ : Set G).toFinset := by
    simp [Finset.ext_iff, hσ]
  let e : Fin (orderOf σ) ≃ (zpowers σ : Set G).toFinset := {
    toFun i := ⟨finEquivZPowers (orderOf_pos_iff.1 (orderOf_pos σ)) i, by simp⟩
    invFun t := (finEquivZPowers (orderOf_pos_iff.1 (orderOf_pos σ))).symm ⟨t.1, by simp_all⟩
    left_inv _ := by simp
    right_inv _ := by simp}
  rw [eq1, ← Finset.prod_finset_coe]
  convert Finset.prod_equiv (s := (Finset.univ : Finset (zpowers σ : Set G).toFinset))
      (t := Finset.univ (α := Fin (orderOf σ))) (f := fun x ↦ φ x.1) (g := fun x ↦ φ (σ ^ x.val))
      e.symm (by simp) (by
        simp only [Finset.univ_eq_attach, Finset.mem_attach, forall_const, Subtype.forall,
          Set.mem_toFinset, SetLike.mem_coe]
        intro g hg
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg;
        simp [e, pow_finEquivZPowers_symm_apply])
  exact Fin.prod_univ_eq_prod_range _ _|>.symm

end GenExp
