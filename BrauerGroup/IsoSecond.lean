import BrauerGroup.ToSecond

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

section mul_inv

variable (a : (K ≃ₐ[F] K) × (K ≃ₐ[F] K) → Kˣ) (ha : IsMulTwoCocycle a)

include ha in
lemma neg_in : IsMulTwoCocycle (-a) := fun a b c ↦ by
  simp only [Pi.neg_apply, mul_neg, neg_mul, ha a b c,
    AlgEquiv.smul_units_def, neg_neg, Units.map_neg]

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq (K ≃ₐ[F] K)]

abbrev invCross := CrossProduct (neg_in K F a ha)

def KlinearEquiv : invCross K F a ha ≃ₗ[K] (CrossProduct ha)ᵐᵒᵖ := sorry

def iso_op : invCross K F a ha ≃ₐ[F] (CrossProduct ha)ᵐᵒᵖ := sorry

end mul_inv

-- instance : Mul (H2 (galAct F K)) := sorry

-- def IsoSecond : H2 (galAct F K) ≃* RelativeBrGroup K F := {
--   __ := RelativeBrGroup.equivSnd (F := F)|>.symm
--   map_mul' := sorry
-- }
