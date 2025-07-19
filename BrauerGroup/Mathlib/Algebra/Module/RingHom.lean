import Mathlib.Algebra.Module.RingHom

lemma Module.compHom_apply {R S : Type*} (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
  [Semiring S] (f : S →+* R) (s : S) (m : M) :
  letI : Module S M := Module.compHom _ f
  s • m = f s • m := by rfl
