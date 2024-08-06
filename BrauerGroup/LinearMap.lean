import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorPower

suppress_compilation

open TensorProduct

section

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

variable {k K V W} in
def _root_.LinearMap.galAct (σ : K ≃ₐ[k] K) (f : K ⊗[k] V →ₗ[K] K ⊗[k] W) :
    K ⊗[k] V →ₗ[K] K ⊗[k] W where
  toFun := LinearMap.rTensor W σ.toLinearMap ∘ f ∘ LinearMap.rTensor V σ.symm.toLinearMap
  map_add' := by aesop
  map_smul' a x := by
    simp only [Function.comp_apply, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      simp only [smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply,
        _root_.map_mul]
      rw [show (σ.symm a * σ.symm b) ⊗ₜ[k] x = σ.symm (a * b) • ((1 : K) ⊗ₜ x) by
        simp [smul_tmul'], map_smul]
      have mem : f (1 ⊗ₜ[k] x) ∈ (⊤ : Submodule k _):= ⟨⟩
      rw [← span_tmul_eq_top k K W, mem_span_set] at mem
      obtain ⟨c, hc, (eq1 : (∑ i in c.support, _ • _) = _)⟩ := mem
      choose xᵢ yᵢ hxy using hc
      have eq1 : f (1 ⊗ₜ[k] x) = ∑ i in c.support.attach, (c i.1 • xᵢ i.2) ⊗ₜ[k] yᵢ i.2 := by
        rw [← eq1, ← Finset.sum_attach]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← smul_tmul', hxy i.2]
      rw [eq1, Finset.smul_sum, map_sum]
      simp_rw [smul_tmul', LinearMap.rTensor_tmul, smul_eq_mul, AlgEquiv.toLinearMap_apply,
        _root_.map_mul, AlgEquiv.apply_symm_apply]
      rw [show σ.symm b ⊗ₜ[k] x = σ.symm b • (1 ⊗ₜ x) by simp [smul_tmul'], map_smul, eq1,
        Finset.smul_sum, map_sum]
      simp_rw [smul_tmul', LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply, smul_eq_mul,
        _root_.map_mul, AlgEquiv.apply_symm_apply]
      rw [Finset.smul_sum]
      simp_rw [smul_tmul', smul_eq_mul, mul_assoc]
    | add => aesop

@[simp]
lemma _root_.LinearMap.galAct_extendScalars_apply
    (σ : K ≃ₐ[k] K) (f : K ⊗[k] V →ₗ[K] K ⊗[k] W) (a : K) (v : V) :
    LinearMap.galAct σ f (a ⊗ₜ v) =
    LinearMap.rTensor W σ.toLinearMap (f $ σ.symm a ⊗ₜ v) := by
  simp only [LinearMap.galAct, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply]

@[simp]
lemma _root_.LinearMap.galAct_extendScalars_apply'
    (σ : K ≃ₐ[k] K) (f : V →ₗ[k] W) (a : K) (v : V) :
    LinearMap.galAct σ (f.extendScalars K) (a ⊗ₜ v) = a ⊗ₜ f v := by
  simp only [LinearMap.galAct, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply, LinearMap.extendScalars_apply,
    AlgEquiv.apply_symm_apply]

lemma _root_.LinearMap.restrictScalars_comp
    {k K : Type*} [Semiring k] [Semiring K]
    {V W W' : Type*} [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid W']
    [Module k V] [Module k W] [Module k W']
    [Module K V] [Module K W] [Module K W']
    [LinearMap.CompatibleSMul V W k K] [LinearMap.CompatibleSMul W W' k K]
    [LinearMap.CompatibleSMul V W' k K]
    (f : V →ₗ[K] W) (g : W →ₗ[K] W') :
    (LinearMap.restrictScalars k (g ∘ₗ f)) =
    LinearMap.restrictScalars k g ∘ₗ LinearMap.restrictScalars k f := by
  ext; rfl

end
