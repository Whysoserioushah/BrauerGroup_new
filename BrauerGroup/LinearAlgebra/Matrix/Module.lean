module

public import Mathlib.LinearAlgebra.Matrix.Module

/-!
## Some lemmas about `ι → M` as a module over the matrix ring
-/

@[expose] public section

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

open Matrix.Module

lemma LinearMap.add_mapMatrixModule (f g : M →ₗ[R] N) :
    (f + g).mapMatrixModule _ = f.mapMatrixModule ι + g.mapMatrixModule _ := by
  ext; simp

lemma LinearMap.smul_mapMatrixModule {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ N]
    (r : R₀) (f : M →ₗ[R] N) [IsScalarTower R₀ R N] :
    (r • f).mapMatrixModule ι = r • (f.mapMatrixModule ι) := by
  ext; simp
