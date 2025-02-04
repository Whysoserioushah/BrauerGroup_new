import BrauerGroup.Azumaya.Mul

universe u v

variable (R : Type u) [CommRing R]

abbrev Azumaya.BrauerGroup := Quotient <| AzumayaSetoid R

noncomputable instance: Mul (Azumaya.BrauerGroup R) where
  mul := Quotient.lift₂ (fun A B ↦ Quotient.mk _ (Azumaya.mul R A B))
    (fun A1 A2 B1 B2 h1 h2 ↦ by
      simp only [Quotient.eq]

      sorry)
