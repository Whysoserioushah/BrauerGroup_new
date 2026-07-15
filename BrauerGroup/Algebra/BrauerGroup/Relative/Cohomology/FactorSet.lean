module

public import BrauerGroup.Algebra.BrauerGroup.Relative.Basic
public import BrauerGroup.Algebra.CrossProduct.Cyclic
public import BrauerGroup.Algebra.Split.Embedding
public import BrauerGroup.RingTheory.SimpleRing.Centralizer
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

universe w u v

namespace BrauerGroup

section Rep

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

variable (L) in
set_option backward.privateInPublic true in
structure GoodRep (x : BrauerGroup K) where
  private mk' ::
  carrier : Type w
  [ring : Ring carrier]
  [algebra : Algebra K carrier]
  [finite : Module.Finite K carrier]
  [central : Algebra.IsCentral K carrier]
  [simple : IsSimpleRing carrier]
  quot_eq : BrauerGroup.mk K carrier = x
  ι : L →ₐ[K] carrier
  dim_eq_sq : Module.finrank K carrier = (Module.finrank K L) ^ 2

namespace GoodRep

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
abbrev mk (A : Type w) [Ring A] [Algebra K A] [Module.Finite K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] {x : BrauerGroup K} (ι : L →ₐ[K] A)
    (hA : BrauerGroup.mk K A = x) (hA' : Module.finrank K A = (Module.finrank K L) ^ 2) :
    GoodRep L x where
  carrier := A
  quot_eq := hA
  ι := ι
  dim_eq_sq := hA'

attribute [instance] GoodRep.ring GoodRep.algebra GoodRep.finite
  GoodRep.central GoodRep.simple

initialize_simps_projections GoodRep (-ring, -algebra, -finite, -central, -simple)

instance (x : BrauerGroup K) : CoeSort (GoodRep L x) (Type w) where
  coe := GoodRep.carrier

attribute [coe] GoodRep.carrier

lemma mk_ι (x : BrauerGroup K) (A : Type w) [Ring A] [Algebra K A]
    [Module.Finite K A] [Algebra.IsCentral K A] [IsSimpleRing A] (ι : L →ₐ[K] A)
    (hA : BrauerGroup.mk K A = x) (hA' : Module.finrank K A = (Module.finrank K L) ^ 2) :
    (GoodRep.mk A ι hA hA').ι = ι := rfl

@[simp]
lemma mk_ι_apply (x : BrauerGroup K) (A : Type w) [Ring A] [Algebra K A]
    [Module.Finite K A] [Algebra.IsCentral K A] [IsSimpleRing A] (ι : L →ₐ[K] A)
    (hA : BrauerGroup.mk K A = x) (hA' : Module.finrank K A = (Module.finrank K L) ^ 2)
    (c : L) : (GoodRep.mk A ι hA hA').ι c = ι c := rfl

scoped instance (x : BrauerGroup K) (A : GoodRep L x) :
    IsSimpleRing A.ι.range := .of_ringEquiv (AlgEquiv.ofInjective A.ι
  A.ι.toRingHom.injective).toRingEquiv inferInstance

scoped instance (x : BrauerGroup K) (A : GoodRep L x) :
    IsMulCommutative A.ι.range := by
  refine ⟨⟨fun a b ↦ Subtype.ext ?_⟩⟩
  obtain ⟨a', ha'⟩ := (AlgHom.mem_range _).1 a.2
  obtain ⟨b', hb'⟩ := (AlgHom.mem_range _).1 b.2
  simp [← ha', ← hb', ← map_mul, mul_comm a' b']

lemma self_centralize (x : BrauerGroup K) (A : GoodRep L x) :
    Subalgebra.centralizer K A.ι.range = A.ι.range := by
  rw [Subalgebra.isMaximal_comm_iff_finrank, A.dim_eq_sq, pow_two,
    (AlgEquiv.ofInjective A.ι A.ι.toRingHom.injective).toLinearEquiv.finrank_eq]

theorem nonempty {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : BrauerGroup K) (hx : x ∈ relativeBrGroup K L) :
    Nonempty (GoodRep L x) := by
  induction x using BrauerGroup.induction with | h A =>
  obtain ⟨B, _, _, _, _, _, ι, hB1, hB2⟩ :=
    Algebra.IsSplit.exists_embedding ((mk_mem_relativeBrGroup_iff_isSplit K L A).1 hx)
  exact ⟨GoodRep.mk B ι hB1 hB2⟩

end GoodRep

end Rep

section conjFactor

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {x : BrauerGroup K}
  (A : GoodRep L x) (σ : Gal(L/K))

def conjFactor : Type _ :=
  {u : A.carrierˣ // ∀ c : L, u * A.ι c * u⁻¹ = A.ι (σ c)}

instance : CoeSort (conjFactor A σ) A where
  coe x := x.val.val

lemma mem_conjFactor (u : conjFactor A σ) (l : L) : u * A.ι l = A.ι (σ l) * u := by
  rw [← u.2, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

lemma inv_conjFactor (u : conjFactor A σ) (l : L) : A.ι l * u.1⁻¹ = u.1⁻¹ * A.ι (σ l) := by
  rw [← u.2, ← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

instance (x : BrauerGroup K) (A : GoodRep.{v} L x) (σ : Gal(L/K)) :
    Nonempty (conjFactor A σ) := by
  obtain ⟨u, hu⟩ := skolemNoether K A.carrier L A.ι (A.ι.comp σ.toAlgHom)
  exact ⟨u, fun c ↦ (hu c).symm⟩

lemma conjFactor_mul_inv_mem_self (u v : conjFactor A σ) :
    (u.1 * v.1⁻¹).1 ∈ A.ι.range := by
  rw [← A.self_centralize, Subalgebra.mem_centralizer_iff]
  intro g hg
  obtain ⟨d, rfl⟩ := (AlgHom.mem_range _).1 hg
  rw [Units.val_mul, ← mul_assoc, ← σ.apply_symm_apply d, ← AlgEquiv.aut_inv,
    ← mem_conjFactor _ _ u (σ⁻¹ d), mul_assoc, inv_conjFactor, mul_assoc]

lemma conjFactor_rel (u v : conjFactor A σ) : ∃! b : Lˣ, u = A.ι b * v := by
  obtain ⟨b, hb⟩ := (AlgHom.mem_range _).1 (conjFactor_mul_inv_mem_self _ _ u v)
  have key : (↑u.1 : A.carrier) = A.ι b * ↑v.1 := by
    rw [hb, Units.val_mul, Units.inv_mul_cancel_right]
  refine ⟨Units.mk0 b fun h ↦ (u.1 * v.1⁻¹).ne_zero (by simpa [h] using hb.symm), key,
    fun c hc ↦ Units.ext <| A.ι.toRingHom.injective ?_⟩
  simp [hb, hc]

abbrev conjFactor.mul (τ : Gal(L/K)) (u : conjFactor A σ)
    (v : conjFactor A τ) : conjFactor A (σ * τ) where
  val := u.1 * v.1
  property c := by
    rw [AlgEquiv.mul_apply, ← u.2 (τ c), ← v.2 c, mul_inv_rev, Units.val_mul, Units.val_mul]
    simp [mul_assoc]

noncomputable abbrev conjFactor.diff (u v : conjFactor A σ) : Lˣ :=
  (conjFactor_rel A σ u v).choose

lemma conjFactor.diff_spec (u v : conjFactor A σ) :
    u = A.ι (conjFactor.diff A σ u v) * v :=
  (conjFactor_rel A σ u v).choose_spec.1

lemma conjFactor.diff_unique {u v : conjFactor A σ} {b : Lˣ} (h : u = A.ι b * v) :
    b = conjFactor.diff A σ u v :=
  (conjFactor_rel A σ u v).choose_spec.2 b h

@[simp]
lemma conjFactor.diff_self (u : conjFactor A σ) : conjFactor.diff A σ u u = 1 :=
  (conjFactor.diff_unique A σ (by simp)).symm

/-- Given a function from `b : G → conjFactor`, this function measures the difference
between two products of `b i` and `b j` and `b (i * j)` -/
noncomputable abbrev factorSet (b : (σ : Gal(L/K)) → conjFactor A σ) :
    Gal(L/K) × Gal(L/K) → Lˣ := fun p ↦
  conjFactor.diff A _ (conjFactor.mul A _ _ (b p.1) (b p.2)) (b (p.1 * p.2))

/-- The master equation of the factor set: `bₛ · bₜ = ι c(s, t) · bₛₜ`. Downstream proofs
should only ever use this and `factorSet_unique`, never the definition. -/
lemma factorSet_spec (b : (σ : Gal(L/K)) → conjFactor A σ) (σ τ : Gal(L/K)) :
    (b σ : A.carrier) * b τ = A.ι (factorSet A b (σ, τ)) * b (σ * τ) :=
  conjFactor.diff_spec A _ (conjFactor.mul A _ _ (b σ) (b τ)) (b (σ * τ))

lemma factorSet_unique (b : (σ : Gal(L/K)) → conjFactor A σ) (σ τ : Gal(L/K)) {c : Lˣ}
    (h : (b σ : A.carrier) * b τ = A.ι c * b (σ * τ)) :
    c = factorSet A b (σ, τ) := conjFactor.diff_unique A _ h

private lemma GoodRep.ι_mul_cancel {ρ : Gal(L/K)} (w : conjFactor A ρ) {l l' : L}
    (h : A.ι l * w = A.ι l' * w) : l = l' :=
  A.ι.toRingHom.injective ((Units.mul_left_inj w.1).1 h)

private lemma mul_expand_left (b : (σ : Gal(L/K)) → conjFactor A σ) (σ τ ν : Gal(L/K)) :
    (b σ : A.carrier) * b τ * b ν
      = A.ι (factorSet A b (σ * τ, ν) * factorSet A b (σ, τ)) * b (σ * τ * ν) := by
  rw [mul_comm (factorSet A b (σ * τ, ν) : L), map_mul,
    factorSet_spec A b σ τ, mul_assoc, factorSet_spec A b (σ * τ) ν, ← mul_assoc]

private lemma mul_expand_right (b : (σ : Gal(L/K)) → conjFactor A σ) (σ τ ν : Gal(L/K)) :
    (b σ : A.carrier) * b τ * b ν
      = A.ι (σ • factorSet A b (τ, ν) * factorSet A b (σ, τ * ν)) * b (σ * τ * ν) := by
  rw [mul_assoc, factorSet_spec A b τ ν, ← mul_assoc, mem_conjFactor, mul_assoc,
    factorSet_spec A b σ (τ * ν), ← mul_assoc, ← mul_assoc σ τ ν]
  simp

open groupCohomology in
/-- The factor set of any family of conjugation factors is a multiplicative 2-cocycle:
expand `bₛ · bₜ · bᵥ` along both associations using the master equation and compare. -/
lemma isMulCocycle₂_factorSet (b : (σ : Gal(L/K)) → conjFactor A σ) :
    IsMulCocycle₂ (factorSet A b) := fun σ τ ν ↦
  Units.ext <| A.ι_mul_cancel (b (σ * τ * ν)) <|
    (mul_expand_left A b σ τ ν).symm.trans (mul_expand_right A b σ τ ν)

private lemma mul_expand_diff_left (b₁ b₂ : (σ : Gal(L/K)) → conjFactor A σ)
    (σ τ : Gal(L/K)) : (b₂ σ : A.carrier) * b₂ τ
      = A.ι (factorSet A b₂ (σ, τ) * conjFactor.diff A (σ * τ) (b₂ (σ * τ)) (b₁ (σ * τ)))
        * b₁ (σ * τ) := by
  rw [map_mul, factorSet_spec A b₂ σ τ,
    conjFactor.diff_spec A (σ * τ) (b₂ (σ * τ)) (b₁ (σ * τ)), ← mul_assoc]

private lemma mul_expand_diff_right (b₁ b₂ : (σ : Gal(L/K)) → conjFactor A σ)
    (σ τ : Gal(L/K)) : (b₂ σ : A.carrier) * b₂ τ
      = A.ι (conjFactor.diff A σ (b₂ σ) (b₁ σ) * σ • conjFactor.diff A τ (b₂ τ) (b₁ τ)
          * factorSet A b₁ (σ, τ)) * b₁ (σ * τ) := by
  rw [conjFactor.diff_spec A σ (b₂ σ) (b₁ σ), conjFactor.diff_spec A τ (b₂ τ) (b₁ τ),
    mul_assoc, ← mul_assoc (b₁ σ : A.carrier), mem_conjFactor, mul_assoc,
    factorSet_spec A b₁ σ τ, ← mul_assoc, ← mul_assoc]
  simp [mul_assoc]

open groupCohomology in
/-- The factor sets attached to two families of conjugation factors differ by the
coboundary of the family of their differences: the H²-class of the factor set does not
depend on the choice of conjugation factors. -/
lemma isMulCoboundary₂_factorSet_div (b₁ b₂ : (σ : Gal(L/K)) → conjFactor A σ) :
    IsMulCoboundary₂ (factorSet A b₂ / factorSet A b₁) := by
  refine ⟨fun σ ↦ conjFactor.diff A σ (b₂ σ) (b₁ σ), fun σ τ ↦ ?_⟩
  have key : factorSet A b₂ (σ, τ) * conjFactor.diff A (σ * τ) (b₂ (σ * τ)) (b₁ (σ * τ))
      = conjFactor.diff A σ (b₂ σ) (b₁ σ) * σ • conjFactor.diff A τ (b₂ τ) (b₁ τ)
        * factorSet A b₁ (σ, τ) :=
    Units.ext <| A.ι_mul_cancel (b₁ (σ * τ)) <|
      (mul_expand_diff_left A b₁ b₂ σ τ).symm.trans (mul_expand_diff_right A b₁ b₂ σ τ)
  rw [Pi.div_apply, div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul,
    mul_comm (σ • conjFactor.diff A τ (b₂ τ) (b₁ τ))]
  exact key.symm

def conjFactor.one (A : GoodRep L x) : conjFactor A 1 := ⟨1, by simp⟩

@[simp]
lemma conjFactor.one_val (A : GoodRep L x) : (conjFactor.one A).1 = 1 := rfl

@[no_expose]
def conjFactor.cast {σ τ : Gal(L/K)} (h : σ = τ) (u : conjFactor A σ) :
    conjFactor A τ := ⟨u.1, h ▸ u.2⟩

@[simp] lemma conjFactor.cast_val {σ τ : Gal(L/K)} (h : σ = τ)
    (u : conjFactor A σ) : (cast A h u).1 = u.1 := by rfl

def conjFactor.pow (u : conjFactor A σ) : (i : ℕ) → conjFactor A (σ ^ i)
  | 0     => cast A (pow_zero σ).symm (one A)
  | i + 1 => cast A (pow_succ σ i).symm (mul A _ _ (pow u i) u)

@[simp] lemma conjFactor.pow_val (u) : ∀ i, (pow A σ u i).1 = u.1 ^ i
  | 0 => by unfold pow; rw [cast_val, one_val, pow_zero]
  | i + 1 => by
    conv_rhs => rw [pow_succ, ← pow_val u i]
    exact cast_val ..

end conjFactor

section cyclic

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  (σ : Gal(L/K)) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
  {x : BrauerGroup K} (A : GoodRep L x)

/-- The conjugation-factor family generated by the powers of a single `u : conjFactor A σ` at
a generator `σ` of `Gal(L/K)`: at `τ = σ ^ i` it is `u ^ i`, the exponent reduced modulo
`orderOf σ`. Downstream proofs should only use `powFamily_val`, never unfold this. -/
noncomputable def powFamily [Module.Finite K L] (u : conjFactor A σ) :
    (τ : Gal(L/K)) → conjFactor A τ :=
  fun τ ↦ conjFactor.cast A (pow_genExp_val σ hσ τ) (conjFactor.pow A σ u (genExp σ hσ τ).val)

@[simp]
lemma powFamily_val [Module.Finite K L] (u : conjFactor A σ) (τ : Gal(L/K)) :
    (powFamily σ hσ A u τ).1 = u.1 ^ (genExp σ hσ τ).val := by
  simp [powFamily]

/-- The unit `b : Lˣ` with `u ^ orderOf σ = ι b`. Internal to the descent; downstream
uses `powScalar` and its spec lemmas. -/
noncomputable abbrev powUnitL (u : conjFactor A σ) : Lˣ :=
    conjFactor.diff A 1 (conjFactor.cast A (pow_orderOf_eq_one σ)
      (conjFactor.pow A σ u (orderOf σ))) (conjFactor.one A)

lemma ι_powUnitL (u : conjFactor A σ) :
    A.ι (powUnitL σ A u) = ↑(u.1 ^ orderOf σ) := by
  have h := conjFactor.diff_spec A 1 (conjFactor.cast A (pow_orderOf_eq_one σ)
    (conjFactor.pow A σ u (orderOf σ))) (conjFactor.one A)
  simpa [-Units.val_pow_eq_pow_val] using h.symm

/-- The scalar of `u ^ orderOf σ` is `σ`-fixed: `u` commutes with its own power, so
conjugation by `u` fixes it. -/
lemma smul_powUnitL (u : conjFactor A σ) :
    σ (powUnitL σ A u : L) = powUnitL σ A u := GoodRep.ι_mul_cancel A u <| by
  rw [← mem_conjFactor A σ u, ι_powUnitL, ← Units.val_mul, ← Units.val_mul, ← pow_succ', pow_succ]

include hσ in
/-- Since `σ` generates `Gal(L/K)`, the scalar of `u ^ orderOf σ` is fixed by the whole
Galois group. -/
lemma smul_powUnitL' (u : conjFactor A σ) (τ : Gal(L/K)) :
    τ (powUnitL σ A u : L) = powUnitL σ A u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ τ)
  induction k with
  | zero => simp
  | succ i ih => rw [← Nat.cast_succ, zpow_natCast, pow_succ, AlgEquiv.mul_apply,
      smul_powUnitL, ← zpow_natCast, ih]
  | pred i ih => rw [← neg_sub, sub_neg_eq_add, zpow_neg, add_comm, ← Nat.cast_succ,
      zpow_natCast, pow_succ, mul_inv_rev, AlgEquiv.mul_apply, ← zpow_natCast, ← zpow_neg, ih,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, smul_powUnitL]

variable [IsGalois K L]

include hσ in
/-- Galois descent: the Galois-fixed unit `powUnitL` comes from `Kˣ`. -/
lemma exists_powScalar (u : conjFactor A σ) :
    ∃ c : Kˣ, algebraMap K L (c : K) = (powUnitL σ A u : L) := by
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2
    (smul_powUnitL' σ hσ A u)
  refine ⟨Units.mk0 c ?_, hc⟩
  rintro rfl
  exact (powUnitL σ A u).ne_zero (by simpa using hc.symm)

/-- The scalar `a : Kˣ` with `u ^ orderOf σ = ι (algebraMap K L a)` — the `uⁿ = a` datum of
the cyclic-algebra presentation. The power family of `u` will have factor set
`cyclicCocycle σ hσ (powScalar σ hσ A u)`. Use only through the spec lemmas below. -/
noncomputable def powScalar (u : conjFactor A σ) : Kˣ :=
    (exists_powScalar σ hσ A u).choose

/-- Defining property of `powScalar`, at the level of `L`. -/
lemma algebraMap_powScalar (u : conjFactor A σ) :
    algebraMap K L (powScalar σ hσ A u : K) = powUnitL σ A u :=
  (exists_powScalar σ hσ A u).choose_spec

/-- Defining property of `powScalar`, at the level of units — the bridge to the values of
`cyclicCocycle`. -/
lemma map_powScalar (u : conjFactor A σ) :
    Units.map (algebraMap K L) (powScalar σ hσ A u) = powUnitL σ A u :=
  Units.ext (algebraMap_powScalar σ hσ A u)

/-- The presentation relation inside `A`: `ι a = u ^ orderOf σ`. -/
lemma ι_powScalar (u : conjFactor A σ) :
    A.ι (algebraMap K L (powScalar σ hσ A u : K)) = ↑(u.1 ^ orderOf σ) := by
  rw [algebraMap_powScalar, ι_powUnitL]

include hσ in
/-- The factor set of the power family of `u` is the carry cocycle at `powScalar u`:
a `GoodRep` with a conjugation factor at a generator is presented by a cyclic algebra. -/
theorem factorSet_powFamily [Module.Finite K L] (u : conjFactor A σ) :
    factorSet A (powFamily σ hσ A u) = cyclicCocycle σ hσ (powScalar σ hσ A u) := by
  ext ⟨τ₁, τ₂⟩ : 1
  refine (factorSet_unique A _ τ₁ τ₂ ?_).symm
  have hval : (genExp σ hσ (τ₁ * τ₂)).val
      = ((genExp σ hσ τ₁).val + (genExp σ hσ τ₂).val) % orderOf σ := by
    rw [genExp_mul, ZMod.val_add]
  rw [cyclicCocycle_apply, ZMod.carry_eq_ite]
  by_cases hc : orderOf σ ≤ (genExp σ hσ τ₁).val + (genExp σ hσ τ₂).val
  · -- carry: v₁ + v₂ = n + v₁₂
    have hmod : ((genExp σ hσ τ₁).val + (genExp σ hσ τ₂).val) % orderOf σ
        = (genExp σ hσ τ₁).val + (genExp σ hσ τ₂).val - orderOf σ := by
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by grind)]
    have h12 : (genExp σ hσ τ₁).val + (genExp σ hσ τ₂).val
        = orderOf σ + (genExp σ hσ (τ₁ * τ₂)).val := by lia
    rw [if_pos hc, zpow_one]
    simp only [powFamily_val, ← Units.val_mul, ← pow_add, h12]
    simp only [pow_add, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
      AlgHom.commutes]
    rw [← Units.val_pow_eq_pow_val, ← ι_powScalar σ hσ A u, AlgHom.commutes]
  · -- no carry: v₁₂ = v₁ + v₂
    have h12 : (genExp σ hσ (τ₁ * τ₂)).val
        = (genExp σ hσ τ₁).val + (genExp σ hσ τ₂).val := by
      rw [hval, Nat.mod_eq_of_lt (by lia)]
    simp [hc, powFamily_val, ← pow_add, h12]

end cyclic

section comparison
variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  (σ : Gal(L/K)) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
  {x : BrauerGroup K} (A : GoodRep L x)

/-- Any two `GoodRep`s of the same Brauer class are isomorphic by an isomorphism
intertwining the two embeddings of `L`: Wedderburn–Artin uniqueness matches up the
carriers, and Skolem–Noether corrects the isomorphism by an inner automorphism. -/
theorem GoodRep.exists_algEquiv_ι (A₁ A₂ : GoodRep.{v} L x) :
    ∃ e : A₁.carrier ≃ₐ[K] A₂.carrier, ∀ c : L, e (A₁.ι c) = A₂.ι c := by
  obtain ⟨e₀⟩ := nonempty_algEquiv_of_mk_eq_of_finrank_eq
    (A₁.quot_eq.trans A₂.quot_eq.symm) (A₁.dim_eq_sq.trans A₂.dim_eq_sq.symm)
  obtain ⟨u, hu⟩ := skolemNoether K A₂.carrier L (e₀.toAlgHom.comp A₁.ι) A₂.ι
  exact ⟨e₀.trans (MulSemiringAction.toAlgEquiv K A₂.carrier (ConjAct.toConjAct u)),
    fun c ↦ by simp [hu c, ConjAct.units_smul_def]⟩

/-- Transport a conjugation factor along an isomorphism intertwining the `L`-embeddings. -/
def conjFactor.map {A₁ A₂ : GoodRep L x} (e : A₁.carrier ≃ₐ[K] A₂.carrier)
    (he : ∀ c : L, e (A₁.ι c) = A₂.ι c) {σ : Gal(L/K)} (u : conjFactor A₁ σ) :
    conjFactor A₂ σ :=
  ⟨Units.map (e : A₁.carrier →* A₂.carrier) u.1, fun c ↦ by
    rw [← map_inv, Units.coe_map, Units.coe_map, MonoidHom.coe_coe, ← he c, ← he (σ c),
      ← map_mul, ← map_mul, u.2 c]⟩

@[simp] lemma conjFactor.map_val {A₁ A₂ : GoodRep L x} (e : A₁.carrier ≃ₐ[K] A₂.carrier)
    (he : ∀ c : L, e (A₁.ι c) = A₂.ι c) {σ : Gal(L/K)} (u : conjFactor A₁ σ) :
    (conjFactor.map e he u).1 = Units.map (e : A₁.carrier →* A₂.carrier) u.1 := rfl

theorem factorSet_map {A₁ A₂ : GoodRep L x} (e : A₁.carrier ≃ₐ[K] A₂.carrier)
    (he : ∀ c : L, e (A₁.ι c) = A₂.ι c) (b : (σ : Gal(L/K)) → conjFactor A₁ σ) :
    factorSet A₂ (fun σ ↦ (b σ).map e he) = factorSet A₁ b := by
  funext ⟨σ, τ⟩
  refine (factorSet_unique A₂ _ σ τ ?_).symm
  simpa [map_mul, he] using congrArg e (factorSet_spec A₁ b σ τ)

open groupCohomology in
/-- The factor sets attached to any two `GoodRep`s of the same Brauer class differ by a
coboundary: the H²-class of the factor set depends only on `x`. -/
theorem isMulCoboundary₂_factorSet_div' (A₁ A₂ : GoodRep.{v} L x)
    (b₁ : (σ : Gal(L/K)) → conjFactor A₁ σ) (b₂ : (σ : Gal(L/K)) → conjFactor A₂ σ) :
    IsMulCoboundary₂ (factorSet A₂ b₂ / factorSet A₁ b₁) := by
  obtain ⟨e, he⟩ := A₁.exists_algEquiv_ι A₂
  rw [← factorSet_map e he b₁]
  exact isMulCoboundary₂_factorSet_div A₂ _ b₂

end comparison

section canonical

open groupCohomology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  (f : Gal(L/K) × Gal(L/K) → Lˣ) [Fact <| IsMulCocycle₂ f]
  [Module.Finite K L] [IsGalois K L] {x : BrauerGroup K}

/-- The crossed product of a cocycle, as a `GoodRep` of any class it represents. -/
noncomputable def GoodRep.ofCrossProduct (h : BrauerGroup.mk K (CrossProductAlgebra f) = x) :
    GoodRep L x :=
  .mk (CrossProductAlgebra f) (CrossProductAlgebra.incl f) h CrossProductAlgebra.dim_eq_sq

/-- The canonical conjugation factors of the crossed product: the units `of f σ`. -/
noncomputable def ofFamily (h : BrauerGroup.mk K (CrossProductAlgebra f) = x) (σ : Gal(L/K)) :
    conjFactor (GoodRep.ofCrossProduct f h) σ :=
  ⟨CrossProductAlgebra.of f σ, fun c ↦ CrossProductAlgebra.of_conj σ c⟩

@[simp] lemma ofFamily_val (h : BrauerGroup.mk K (CrossProductAlgebra f) = x) (σ : Gal(L/K)) :
    (ofFamily f h σ).1 = CrossProductAlgebra.of f σ := rfl

/-- The factor set of the canonical conjugation factors is `f` itself. -/
theorem factorSet_ofFamily (h : BrauerGroup.mk K (CrossProductAlgebra f) = x) :
    factorSet (GoodRep.ofCrossProduct f h) (ofFamily f h) = f := by
  funext ⟨σ, τ⟩
  exact (factorSet_unique _ _ σ τ (CrossProductAlgebra.of_mul_of _ σ τ)).symm

end canonical

end BrauerGroup
