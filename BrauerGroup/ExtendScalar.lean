module

public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct

universe u
variable (k K L A : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L]
  [Algebra k L] [Ring A] [Algebra k A] [IsScalarTower k K L]

def releaseAddHom : L ⊗[k] A →+ L ⊗[K] (K ⊗[k] A) :=
  TensorProduct.liftAddHom
  {
    toFun l := {
      toFun a := l ⊗ₜ[K] (1 ⊗ₜ[k] a)
      map_zero' := by simp only [TensorProduct.tmul_zero]
      map_add' _ _ := by simp_rw [TensorProduct.tmul_add]
    }
    map_zero' := by simp only [TensorProduct.zero_tmul]; rfl
    map_add' x y := by
      ext a'
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
      repeat rw [TensorProduct.add_tmul]
  } fun r l a ↦ by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.tmul_smul]; rfl

def release : L ⊗[k] A →ₐ[L] L ⊗[K] (K ⊗[k] A) where
  __ := releaseAddHom k K L A
  map_one' := rfl
  map_mul' x y := by
    change (releaseAddHom k K L A) (x * y) = (releaseAddHom k K L A) x * (releaseAddHom k K L A) y
    induction x with
    | add z w hz hw =>
      rw [add_mul]
      rw [map_add (releaseAddHom k K L A), map_add (releaseAddHom k K L A)]
      rw [add_mul]
      rw [hz, hw]
    | tmul l a =>
    induction y with
    | add x y hx hy =>
      rw [mul_add]
      rw [map_add (releaseAddHom k K L A), map_add (releaseAddHom k K L A)]
      rw [mul_add]
      rw [hx, hy]
    | tmul l' a' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    change (l * l') ⊗ₜ[K] (1 ⊗ₜ[k] (a * a')) = (l ⊗ₜ[K] (1 ⊗ₜ[k] a)) * (l' ⊗ₜ[K] (1 ⊗ₜ[k] a'))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  commutes' l := rfl

def absorbMap (l : L) : K ⊗[k] A →ₗ[k] L ⊗[k] A :=
  TensorProduct.lift {
    toFun := fun m ↦ {
      toFun := fun a ↦ (m • l) ⊗ₜ[k] a
      map_add' := fun _ _ ↦ by simp only [TensorProduct.tmul_add]
      map_smul' := fun _ _ ↦ by simp [TensorProduct.tmul_smul, RingHom.id_apply]
    }
    map_add' := fun _ _ ↦ by ext; simp only [add_smul, TensorProduct.add_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    map_smul' := fun _ _ ↦ by ext; simp only [smul_assoc, ← TensorProduct.smul_tmul',
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
  }

def absorbAddHom : L ⊗[K] (K ⊗[k] A) →+ L ⊗[k] A :=
  TensorProduct.liftAddHom
  {
    toFun l := absorbMap k K L A l
    map_zero' := by
      ext x
      induction x with
      | tmul x a =>
        change (x • 0) ⊗ₜ a = 0
        simp only [smul_zero, TensorProduct.zero_tmul]
      | add x y hx hy =>
        simp_all only [AddMonoidHom.zero_apply, map_add, add_zero]
    map_add' := fun x y ↦ by
      ext z
      induction z with
      | tmul m a =>
        change (m • (x + y)) ⊗ₜ a = (m • x) ⊗ₜ a + (m • y) ⊗ₜ a
        simp only [smul_add, TensorProduct.add_tmul]
      | add z w hz hw =>
        simp only [AddMonoidHom.add_apply] at hz hw
        simp only [map_add, AddMonoidHom.add_apply, hz, hw]
  } (fun r l a ↦ by
    induction a with
    | tmul m a =>
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, TensorProduct.smul_tmul']
      change (m • (r • l)) ⊗ₜ a = ((r • m) • l) ⊗ₜ a
      rw [← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul]
    | add x y hx hy =>
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hx hy
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, hx, hy, smul_add]
    )

def absorb : L ⊗[K] (K ⊗[k] A) →ₐ[L] L ⊗[k] A where
  __ := absorbAddHom k K L A
  map_one' := by
    simp only [Algebra.TensorProduct.one_def, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    change (1 • 1) ⊗ₜ (1 : A) = _
    rw [one_smul]
  map_mul' := fun x y ↦ by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    induction x with
    | add x' y' hx hy => simp only [add_mul, map_add, hx, hy]
    | tmul l ka =>
    induction y with
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | tmul l' ka' =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
    induction ka' with
    | add x y hx hy => simp only [mul_add, TensorProduct.tmul_add, map_add, hx, hy]
    | tmul k' a =>
    induction ka with
    | add x y hx hy => simp only [add_mul, TensorProduct.tmul_add, map_add, hx, hy]
    | tmul k1 a1 =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul]
    change ((k1 * k') • (l * l')) ⊗ₜ (a1 * a) = (k1 • l) ⊗ₜ a1 * (k' • l') ⊗ₜ a
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc]
    rw [← smul_assoc, smul_eq_mul, mul_comm]
  commutes' := fun l ↦ by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def]
    change (1 • l) ⊗ₜ (1 : A) = l ⊗ₜ 1
    rw [one_smul]

def absorb_eqv : L ⊗[k] A ≃ₐ[L] L ⊗[K] (K ⊗[k] A) where
  toFun := release k K L A
  invFun := absorb k K L A
  left_inv := fun x ↦ by
    induction x with
    | tmul l a =>
      change (absorb k K L A) (l ⊗ₜ[K] (1 ⊗ₜ a)) = _
      change (1 • l) ⊗ₜ _ = _
      rw [one_smul]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  right_inv := fun x ↦ by
    induction x with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l ka =>
    induction ka with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul k' a =>
    change (release k K L A) ((k' • l) ⊗ₜ a) = _
    change (k' • l) ⊗ₜ[K] (1 ⊗ₜ a) = _
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := release k K L A|>.commutes

theorem absorb_eqv_apply (l : L) (a : A) : absorb_eqv k K L A (l ⊗ₜ a) = l ⊗ₜ[K] (1 ⊗ₜ a) :=
  rfl
