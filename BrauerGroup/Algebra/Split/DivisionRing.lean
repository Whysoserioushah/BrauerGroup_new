module

public import BrauerGroup.Algebra.Split.Finrank
public import BrauerGroup.Algebra.Central.Matrix
public import BrauerGroup.Algebra.Algebra.Subalgebra.DivisionRing

@[expose] public section

variable {k A k_bar : Type*} [Field k] [Ring A] [Algebra k A] [Module.Finite k A] [IsSimpleRing A]
  [Algebra.IsCentral k A] [Field k_bar] [Algebra k k_bar] [IsAlgClosed k_bar]

/-- Every central simple algebra over a field has a finite separable splitting field. -/
theorem Algebra.IsCentralSimple.exists_finite_sep_split :
    ∃ K : IntermediateField k k_bar, Module.Finite k K ∧
      Algebra.IsSeparable k K ∧ Algebra.IsSplit k A K := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  have : Algebra.IsCentral k D := .of_matrix (h := .of_algEquiv k _ _ e)
  obtain ⟨L, hL1, hL2⟩ := DivisionRing.exists_separable_maxSubfield (k := k) (D := D)
  have : IsMulCommutative L := (Subalgebra.le_centralizer_iff_isMulCommutative L).1 hL1.ge
  let : Field L := L.fieldOfIsMulCommutative
  have hL3 : IsSplit k A L := by
    rw [isSplit_congr k A D L (by
      rw [BrauerGroup.mk_congr e, BrauerGroup.mk_eq_mk]
      exact ⟨1, n, one_ne_zero, hn.out, ⟨by convert! Matrix.uniqueAlgEquiv (m := Fin 1)⟩⟩)]
    rwa [DivisionRing.split_iff_finrank L.val, ← Subalgebra.isMaximal_comm_iff_finrank]
  have hL4 : Function.Injective (IsAlgClosed.lift (M := k_bar) (R := k) (S := L)) := by
    change Function.Injective IsAlgClosed.lift.toRingHom
    exact RingHom.injective _
  use (IsAlgClosed.lift (S := L)).fieldRange, Module.Finite.of_injective _
    (AlgEquiv.ofInjective _ hL4).symm.toLinearEquiv.injective,
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjective _ hL4)
  change IsSplit k A (IsAlgClosed.lift (S := L)).range
  exact IsSplit.of_algEquiv' _ _ hL3 (AlgEquiv.ofInjective _ hL4)

/-- Every central simple algebra over a field has a finite Galois splitting field. -/
theorem Algebra.IsCentralSimple.exists_finite_galois_split [Algebra.IsAlgebraic k k_bar] :
    ∃ K : IntermediateField k k_bar, Module.Finite k K ∧ IsGalois k K ∧ Algebra.IsSplit k A K := by
  obtain ⟨K, _, _, hK⟩ := exists_finite_sep_split (k := k) (A := A) (k_bar := k_bar)
  have hk : IsAlgClosure k k_bar := ⟨inferInstance, inferInstance⟩
  set N := IntermediateField.normalClosure k K k_bar with N_def
  use N, inferInstance, ?_
  · exact IsSplit.of_isScalarTower N hK
  haveI : ∀ f : K →ₐ[k] k_bar, Algebra.IsSeparable k f.fieldRange := fun f ↦
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjective f f.toRingHom.injective)
  exact IsGalois.mk (to_isSeparable := IntermediateField.isSeparable_iSup k k_bar)
