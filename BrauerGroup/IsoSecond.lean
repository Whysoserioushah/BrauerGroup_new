import BrauerGroup.ToSecond

suppress_compilation

universe u

variable (K F : Type) [Field K] [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

open groupCohomology FiniteDimensional BrauerGroup DirectSum GoodRep

instance : Group (H2 (galAct F K)) := sorry

open Classical in
def IsoSecond : H2 (galAct F K) ≃* RelativeBrGroup K F := {
  __ := RelativeBrGroup.equivSnd (F := F)|>.symm
  map_mul' := sorry
}
