import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

suppress_compilation

open TensorProduct

universe u

variable (K K_bar: Type u) [Field K] [Field K_bar] [Algebra K K_bar] [IsAlgClosure K K_bar]

variable (A : Type u) [AddCommGroup A] [Module K A]

open scoped IntermediateField

def intermediateTensor (L : IntermediateField K K_bar) : Submodule K (K_bar ⊗[K] A) :=
  LinearMap.range (LinearMap.rTensor _ (L.val.toLinearMap) : L ⊗[K] A →ₗ[K] K_bar ⊗[K] A)

lemma intermediateTensor_mono {L1 L2 : IntermediateField K K_bar} (h : L1 ≤ L2) :
    intermediateTensor K K_bar A L1 ≤ intermediateTensor K K_bar A L2 := by
  have e1 : (LinearMap.rTensor _ (L1.val.toLinearMap) : L1 ⊗[K] A →ₗ[K] K_bar ⊗[K] A) =
    (LinearMap.rTensor _ (L2.val.toLinearMap) : L2 ⊗[K] A →ₗ[K] K_bar ⊗[K] A) ∘ₗ
    (LinearMap.rTensor A (L1.inclusion h) : L1 ⊗[K] A →ₗ[K] L2 ⊗[K] A) := by
    rw [← LinearMap.rTensor_comp]; rfl
  delta intermediateTensor
  rw [e1, LinearMap.range_comp, Submodule.map_le_iff_le_comap]
  rintro _ ⟨x, rfl⟩
  simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    Submodule.mem_comap, LinearMap.mem_range, exists_apply_eq_apply]

abbrev S : Set (IntermediateField K K_bar) :=
  {M | FiniteDimensional K M}

lemma is_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1)
    (Set.range fun (L : S K K_bar) ↦ intermediateTensor K K_bar A L):= by
  rintro _ ⟨⟨L1, (hL1 : FiniteDimensional _ _)⟩, rfl⟩ _ ⟨⟨L2, (hL2 : FiniteDimensional _ _)⟩, rfl⟩
  refine ⟨intermediateTensor K K_bar A (L1 ⊔ L2), ⟨⟨L1 ⊔ L2, show FiniteDimensional _ _ from
    ?_⟩, rfl⟩, ⟨intermediateTensor_mono K K_bar A le_sup_left,
      intermediateTensor_mono K K_bar A le_sup_right⟩⟩
  · apply (config := { allowSynthFailures := true }) IntermediateField.finiteDimensional_sup <;>
    assumption

/-- K_bar ⊗[K] A = union of all finite subextension of K ⊗ A -/
theorem inter_tensor_union :
    ⨆ (L : S K K_bar),
    (intermediateTensor K K_bar A L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  |zero => simp
  |tmul x a =>
    have fin0: FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional (by
      observe : IsAlgebraic K x
      exact Algebra.IsIntegral.isIntegral x)
    refine Submodule.mem_sSup_of_directed ?_ (is_direct K K_bar A) |>.2
      ⟨intermediateTensor K K_bar A K⟮x⟯, ⟨⟨⟨K⟮x⟯, fin0⟩, rfl⟩,
        ⟨(⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ ⊗ₜ a), by simp⟩⟩⟩
    refine ⟨intermediateTensor K K_bar A ⊥, ⟨⟨⊥, ?_⟩, rfl⟩⟩
    simp only [S, Set.mem_setOf_eq, IntermediateField.bot_toSubalgebra]
    infer_instance

  |add x y hx hy =>
  apply AddMemClass.add_mem <;> assumption
