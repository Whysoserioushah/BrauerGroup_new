import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

import BrauerGroup.Subfield.splitting


#check groupCohomology.H2

variable (K F : Type) [Field K] [Field F] [Algebra F K]

noncomputable example : Rep ℤ (K ≃ₐ[F] K) :=
  Rep.of (V := Additive Kˣ)
    { toFun := fun σ =>
      { toFun := fun x => ⟨σ x.1, σ x.2, by simp, by simp⟩
        map_add' := fun (x : Kˣ) (y : Kˣ) => by
          refine Units.ext ?_
          change σ (x.1 * y.1) = σ _ * σ _
          simp only [map_mul]
        map_smul' := by
          rintro m x
          dsimp
          apply_fun Additive.toMul
          rw [toMul_zsmul]
          simp only [Units.val_inv_eq_inv_val, map_inv₀]
          refine Units.ext ?_
          dsimp
          change σ (_ ^ m : Kˣ).1 = _ -- r • σ x.1
          simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
          rfl }
      map_one' := rfl
      map_mul' := by intros; rfl }
