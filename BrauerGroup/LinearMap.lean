import Mathlib.RingTheory.TensorProduct.Basic

suppress_compilation

open TensorProduct

variable (k K V W W' : Type*)
variable {p q : ℕ}
variable [CommSemiring k] [Semiring K] [Algebra k K]
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]
variable [AddCommMonoid W'] [Module k W']

variable {k V W} in
def _root_.LinearMap.extendScalars (f : V →ₗ[k] W) : K ⊗[k] V →ₗ[K] K ⊗[k] W :=
  { f.lTensor K with
    map_smul' := fun a x => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b v =>
        simp only [smul_tmul', smul_eq_mul, LinearMap.lTensor_tmul]
      | add => aesop }

variable {k V W} in
@[simp]
lemma _root_.LinearMap.extendScalars_apply (f : V →ₗ[k] W) (a : K) (v : V) :
    LinearMap.extendScalars K f (a ⊗ₜ v) = a ⊗ₜ f v := by
  simp only [LinearMap.extendScalars, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    LinearMap.lTensor_tmul]

@[simp]
lemma _root_.LinearMap.extendScalars_id :
    LinearMap.extendScalars K (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  ext
  simp

lemma _root_.LinearMap.extendScalars_comp (f : V →ₗ[k] W) (g : W →ₗ[k] W') :
    (g ∘ₗ f).extendScalars K = g.extendScalars K ∘ₗ f.extendScalars K := by
  ext v
  simp
