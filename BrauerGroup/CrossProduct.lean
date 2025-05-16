import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

namespace groupCohomology

variable {G K : Type*} [Group G] [Field K] {a : G × G → Kˣ}

@[ext]
structure TwistedProduct (a : G × G → Kˣ) where
  fst : G
  snd : Kˣ

namespace TwistedProduct

instance : One (TwistedProduct a) where
  one := ⟨1, (a 1)⁻¹⟩

lemma one_def : (1 : TwistedProduct a) = ⟨1, (a 1)⁻¹⟩ := rfl

@[simp] lemma fst_one : (1 : TwistedProduct a).fst = 1 := rfl
@[simp] lemma snd_one : (1 : TwistedProduct a).snd = (a 1)⁻¹ := rfl

variable [MulAction G Kˣ]

instance : Mul (TwistedProduct a) where
  mul := fun ⟨σ, c⟩ ⟨τ, d⟩ ↦ ⟨σ * τ, c * σ • d * a (σ, τ)⟩

instance : Inv (TwistedProduct a) where
  inv := fun ⟨σ, c⟩ ↦ ⟨σ⁻¹, σ⁻¹ • c⁻¹ / a 1 / a (σ⁻¹, σ)⟩

lemma mul_def (x y : TwistedProduct a) :
    x * y = ⟨x.fst * y.fst, x.snd * x.fst • y.snd * a (x.fst, y.fst)⟩ := rfl

lemma inv_def (x : TwistedProduct a) :
    x⁻¹ = ⟨x.fst⁻¹, x.fst⁻¹ • x.snd⁻¹ / a 1 / a (x.fst⁻¹, x.fst)⟩ := rfl

@[simp] lemma fst_mul (x y : TwistedProduct a) : (x * y).fst = x.fst * y.fst := rfl

@[simp] lemma snd_mul (x y : TwistedProduct a) :
    (x * y).snd = x.snd * x.fst • y.snd * a (x.fst, y.fst) := rfl

@[simp] lemma fst_inv (x : TwistedProduct a) : x⁻¹.fst = x.fst⁻¹ := rfl

@[simp] lemma snd_inv (x : TwistedProduct a) :
    x⁻¹.snd = x.fst⁻¹ • x.snd⁻¹ / a 1 / a (x.fst⁻¹, x.fst) := rfl

instance [Fact (IsMulTwoCocycle a)] : Monoid (TwistedProduct a) where
  mul_assoc := by
    rintro ⟨σ, c⟩ ⟨τ, d⟩ ⟨ν, e⟩
    ext
    · simp [mul_assoc]
    have := congr(($((Fact.out : IsMulTwoCocycle a) σ τ ν)).val)
    rw [Units.val_mul, mul_comm] at this
    simp [mul_assoc, mul_left_comm _ (σ • τ • e), this, mul_smul]
    sorry
  one_mul := by
    rintro ⟨σ, c⟩; ext <;> simp [map_one_fst_of_isMulTwoCocycle Fact.out, mul_right_comm _ c.val]
  mul_one := by
    rintro ⟨σ, c⟩; ext <;> simp [map_one_snd_of_isMulTwoCocycle Fact.out]
    sorry

instance [Fact (IsMulTwoCocycle a)] : Group (TwistedProduct a) where
  inv_mul_cancel := by
    rintro ⟨σ, c⟩; ext : 1 <;> simp [div_eq_mul_inv, mul_assoc, mul_left_comm]
    sorry

end TwistedProduct

abbrev CrossProduct (a : G × G → Kˣ) :=
  MonoidAlgebra K (TwistedProduct a)

namespace CrossProduct

lemma dim_eq_square [Fact (IsMulTwoCocycle a)] :
    Module.finrank F (CrossProduct a) = (Module.finrank F K)^2 := by
  have eq1 : Module.finrank F (CrossProduct a) = Module.finrank F K *
      Module.finrank K (CrossProduct a) := by
    rw [Module.finrank_mul_finrank]
  rw [Module.finrank_eq_card_basis (x_AsBasis a), IsGalois.card_aut_eq_finrank] at eq1
  rw [eq1, pow_two]

end CrossProduct
end groupCohomology
