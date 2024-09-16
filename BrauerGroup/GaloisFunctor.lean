import BrauerGroup.FieldCatOver

universe u

open CategoryTheory BigOperators

variable (K : Type u) [Field K]
 --need fxing
class GaloisFunctor (F : FieldCatOver K ⥤ Grp) : Prop where
  inj : ∀(E G : Type u) [Field E] [Algebra K E] [Field G] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G] [IsGalois E G],
    Function.Injective (F.map (FieldCatOver.ofHom (X := E) (Y := G)
    { __ := Algebra.ofId E G
      commutes' := AlgHom.map_algebraMap _}))
  iso : ∀(E G : Type u) [Field E] [Algebra K E] [Field G] [Algebra E G] [Algebra K G]
    [IsScalarTower K E G] [IsGalois E G], Nonempty $
      F.obj (FieldCatOver.of K K) ≃*
      MulAction.stabilizer (F.obj (FieldCatOver.of K G)) (α := (G ≃ₐ[K] G)) _
