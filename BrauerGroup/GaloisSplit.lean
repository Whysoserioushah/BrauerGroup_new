import Mathlib.Tactic
import BrauerGroup.SplittingOfCSA

universe u

open BigOperators TensorProduct

noncomputable section one

variable (K K_bar : Type u) [Field K] (A : CSA K)[Field K_bar] [Algebra K K_bar]
  [IsAlgClosure K K_bar]

def Basis_of_K : Basis (Fin (FiniteDimensional.finrank K A)) K_bar (K_bar ⊗[K] A):=
  Algebra.TensorProduct.basis K_bar (FiniteDimensional.finBasis K A)

theorem Basis_apply (i : Fin (FiniteDimensional.finrank K A)) :
    Basis_of_K K K_bar A i = 1 ⊗ₜ (FiniteDimensional.finBasis K A i) :=
  Algebra.TensorProduct.basis_apply (FiniteDimensional.finBasis K A) i

variable {K K_bar A} in
abbrev b (e : split K A K_bar := split_by_alg_closure K K_bar A)
    (i j : Fin e.n) (x : Fin (FiniteDimensional.finrank K A.carrier)) : K_bar :=
  ((Basis_of_K K K_bar A).repr
    (e.iso.symm (Matrix.stdBasisMatrix i j 1))) x

lemma b_spec (e : split K A K_bar := split_by_alg_closure K K_bar A)
    (i j : Fin e.n) :
    Matrix.stdBasisMatrix i j (1 : K_bar) =
    e.iso (∑ k : Fin (FiniteDimensional.finrank K A.carrier),
      b e i j k ⊗ₜ FiniteDimensional.finBasis K A k) := by
  let x (i j : Fin e.n):= e.iso.symm $ Matrix.stdBasisMatrix i j (1 : K_bar)
  have (i j : Fin e.n) := (Basis_of_K K K_bar A).total_repr (x i j)
  simp only [Finsupp.total, Basis_apply, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, smul_tmul', smul_eq_mul, mul_one, x] at this
  specialize this i j
  apply_fun e.iso.symm
  simp only [map_sum, AlgEquiv.symm_apply_apply]
  rw [← this]
  apply Finset.sum_subset (h := Finset.subset_univ _)
  rintro x - hx
  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx ⊢
  simp only [hx, zero_tmul]

variable [DecidableEq K_bar]

abbrev K' (e : split K A K_bar := split_by_alg_closure K K_bar A) : IntermediateField K K_bar :=
  IntermediateField.adjoin K (Finset.image (Function.uncurry $ Function.uncurry $ b e) Finset.univ)

def b_as_K' (e : split K A K_bar := split_by_alg_closure K K_bar A) (i j : Fin e.n)
    (k : Fin (FiniteDimensional.finrank K A)) :
    K' K K_bar A e :=
  ⟨b e i j k,  by
    simp only [K', Finset.coe_image, Finset.coe_univ, Set.image_univ]
    apply IntermediateField.subset_adjoin
    simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair, exists_apply_eq_apply3]⟩

lemma coe_b_as_K' (e : split K A K_bar := split_by_alg_closure K K_bar A) (i j : Fin e.n)
    (k : Fin (FiniteDimensional.finrank K A)) :
    (b_as_K' (e := e) i j k : K_bar) = b e i j k := rfl

open IntermediateField in
instance (e : split K A K_bar := split_by_alg_closure K K_bar A) :
    FiniteDimensional K (K' K K_bar A e) := by
  delta K'
  rw [← IntermediateField.biSup_adjoin_simple]
  have (i : K_bar) : Module.Finite K K⟮i⟯ := by
    apply IntermediateField.adjoin.finiteDimensional
    exact Algebra.IsIntegral.isIntegral i
  apply finiteDimensional_iSup_of_finset

set_option synthInstance.maxHeartbeats 60000 in
instance (e : split K A K_bar) :
  Algebra ((K' K K_bar A e)) ((K' K K_bar A e) ⊗[K] A.carrier) := inferInstance

set_option synthInstance.maxHeartbeats 60000 in
instance (e : split K A K_bar) :
  Module ((K' K K_bar A e)) ((K' K K_bar A e) ⊗[K] A.carrier) := inferInstance

set_option synthInstance.maxHeartbeats 60000 in
instance (e : split K A K_bar) :
  DistribSMul ((K' K K_bar A e)) ((K' K K_bar A e) ⊗[K] A.carrier) := inferInstance

private def emb (e : split K A K_bar := split_by_alg_closure K K_bar A) :
    K' K K_bar A e ⊗[K] A →ₐ[K' K K_bar A e] K_bar ⊗[K] A :=
  Algebra.TensorProduct.map (Algebra.ofId (K' (e := e)) _) (AlgHom.id _ _)

private lemma emb_tmul (e : split K A K_bar := split_by_alg_closure K K_bar A) :
  ∀ (x : K' K K_bar A e) (y : A), emb (e := e) (x ⊗ₜ y) =
    (x.1 ⊗ₜ y) := by
  intros
  simp only [emb, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  rfl

lemma basis'_li (e) : LinearIndependent ↥(K' K K_bar A e) fun i : Fin e.n × Fin e.n ↦
  ∑ j : Fin (FiniteDimensional.finrank K A.carrier),
    b_as_K' K K_bar A e i.1 i.2 j ⊗ₜ[K] (FiniteDimensional.finBasis K A.carrier) j := by
        rw [linearIndependent_iff]
        intro c hc
        apply_fun (emb (e := e)) at hc
        dsimp only [Finsupp.total, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
          id_eq, Finsupp.sum] at hc
        rw [(emb (e := e)).map_sum] at hc
        simp_rw [Finset.smul_sum, smul_tmul', (emb (e := e)).map_sum, emb_tmul, smul_eq_mul] at  hc
        push_cast at hc
        simp_rw [coe_b_as_K', ← smul_eq_mul, ← smul_tmul', ← Finset.smul_sum] at hc
        apply_fun e.iso at hc
        rw [map_sum] at hc
        simp_rw [map_smul, ← b_spec] at hc
        rw [(emb (e := e)).map_zero, map_zero] at hc
        ext ⟨i, j⟩
        have := Matrix.ext_iff.2 hc i j
        simp only [Matrix.smul_stdBasisMatrix, smul_eq_mul, mul_one, Matrix.zero_apply] at this
        simp only [Matrix.sum_apply, Matrix.stdBasisMatrix] at this
        have p_eq (x : Fin e.n × Fin e.n) : (x.1 = i ∧ x.2 = j) = (x = ⟨i, j⟩) := by
          aesop
        simp_rw [p_eq] at this
        simp only [Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_left_iff,
          ZeroMemClass.coe_eq_zero, Decidable.not_imp_self] at this
        rw [this]
        rfl

def basis' (e : split K A K_bar := split_by_alg_closure K K_bar A) :
      Basis (Fin e.n × Fin e.n) (K' K K_bar A e) (K' K K_bar A e ⊗[K] A) :=
    haveI : NeZero e.n := ⟨e.hn⟩
    haveI :  Nonempty (Fin e.n × Fin e.n) := inferInstance
    basisOfLinearIndependentOfCardEqFinrank (lin_ind := basis'_li (e := e)) $ by
      simp only [Fintype.card_prod, Fintype.card_fin, FiniteDimensional.finrank_tensorProduct,
        FiniteDimensional.finrank_self, one_mul]
      have := LinearEquiv.finrank_eq (R := K_bar) e.iso.toLinearEquiv
      simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self, one_mul,
        FiniteDimensional.finrank_matrix, Fintype.card_fin] at this ⊢
      exact this.symm

@[simp]
lemma basis'_apply (e : split K A K_bar := split_by_alg_closure K K_bar A)
    (i j : Fin e.n) :
    basis' (e := e) (i, j) = ∑ k : (Fin $ FiniteDimensional.finrank K A),
      b_as_K' (e := e) i j k ⊗ₜ FiniteDimensional.finBasis K A k := by
  simp only [basis', coe_basisOfLinearIndependentOfCardEqFinrank]

def e'Aux (e : split K A K_bar := split_by_alg_closure K K_bar A) :
    (K' K K_bar A e) ⊗[K] A ≃ₗ[K' K K_bar A e]
    Matrix (Fin e.n) (Fin e.n) (K' K K_bar A e) :=
  Basis.equiv (b := basis' (e := e)) (b' := Matrix.stdBasis (K' K K_bar A e) (Fin e.n) (Fin e.n)) $
    Equiv.refl _

lemma e'Aux_apply_basis (e : split K A K_bar := split_by_alg_closure K K_bar A)
    (i j : Fin e.n) :
    (e'Aux (e := e) (∑ k, b_as_K' (e := e) i j k ⊗ₜ FiniteDimensional.finBasis K A k)) =
    Matrix.stdBasisMatrix i j 1 := by
  simp only [e'Aux]
  have := (basis' (e := e)).equiv_apply (b' := Matrix.stdBasis (K' K K_bar A e) (Fin e.n) (Fin e.n))
    ⟨i, j⟩ (Equiv.refl _)
  rw [basis'_apply (e := e)] at this
  rw [this]
  ext
  simp only [Equiv.refl_apply, Matrix.stdBasis_eq_stdBasisMatrix, Matrix.stdBasisMatrix]

def emb' (e : split K A K_bar := split_by_alg_closure K K_bar A):
    Matrix (Fin e.n) (Fin e.n) (K' K K_bar A e) →ₐ[K' K K_bar A e]
    Matrix (Fin e.n) (Fin e.n) K_bar :=
  AlgHom.mapMatrix (Algebra.ofId (K' K K_bar A e) _)

lemma emb'_inj (e : split K A K_bar := split_by_alg_closure K K_bar A):
    Function.Injective (emb' (e := e)) := by
  intros x y h
  ext i j
  rw [← Matrix.ext_iff] at h
  specialize h i j
  simp only [emb', Algebra.ofId, AlgHom.mapMatrix_apply, AlgHom.coe_mk, Matrix.map_apply,
    IntermediateField.algebraMap_apply, SetLike.coe_eq_coe] at h ⊢
  exact h

set_option synthInstance.maxHeartbeats 60000 in
instance (e) : NonUnitalNonAssocSemiring (↥(K' K K_bar A e) ⊗[K] A.carrier) := inferInstance

lemma emb_comm_square (e : split K A K_bar := split_by_alg_closure K K_bar A):
    e.iso.toLinearMap.restrictScalars (K' (e := e)) ∘ₗ (emb (e := e)).toLinearMap =
    (emb' (e := e)).toLinearMap ∘ₗ (e'Aux (e := e)).toLinearMap := by
  apply Basis.ext (b := basis' (e := e))
  rintro ⟨i, j⟩
  rw [basis'_apply (e := e)]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  erw [e'Aux_apply_basis (e := e)]
  simp only [map_sum, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, emb',
    AlgHom.mapMatrix_apply]
  simp only [emb, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  simp only [Algebra.ofId, AlgHom.coe_mk, IntermediateField.algebraMap_apply]
  rw [← map_sum]
  simp_rw [coe_b_as_K']
  rw [← b_spec (e := e)]
  ext
  simp only [Matrix.stdBasisMatrix, Matrix.map_apply, RingHom.map_ite_one_zero]

set_option synthInstance.maxHeartbeats 60000 in
instance (e : split K A K_bar := split_by_alg_closure K K_bar A):
  HMul (↥(K' K K_bar A e) ⊗[K] A.carrier) (↥(K' K K_bar A e) ⊗[K] A.carrier)
  (↥(K' K K_bar A e) ⊗[K] A.carrier) := inferInstance

lemma e'_map_mul (e : split K A K_bar := split_by_alg_closure K K_bar A)
    (x y : (K' K K_bar A e) ⊗[K] A) :
    (e'Aux K K_bar A e) (x * y) =
    (e'Aux K K_bar A e) x * (e'Aux K K_bar A e) y := by
  have eq := congr($(emb_comm_square (e := e)) (x * y))
  have eqx := congr($(emb_comm_square (e := e)) x)
  have eqy := congr($(emb_comm_square (e := e)) y)
  apply_fun emb' (e := e) using emb'_inj (e := e)
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe] at eq eqx eqy
  rw [← eq, (emb (e := e)).map_mul, _root_.map_mul (f := e.iso), (emb' (e := e)).map_mul,
    ← eqx, ← eqy]

lemma e'_map_one (e : split K A K_bar := split_by_alg_closure K K_bar A) :
    (e'Aux K K_bar A e) 1 = 1 := by
  have eq := congr($(emb_comm_square (e := e)) 1)
  apply_fun emb' (e := e) using emb'_inj (e := e)
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe] at eq
  rw [← eq, (emb (e := e)).map_one, _root_.map_one (f := e.iso), (emb' (e := e)).map_one]

def e' (e : split K A K_bar := split_by_alg_closure K K_bar A) :
    (K' K K_bar A e) ⊗[K] A ≃ₐ[K' K K_bar A e]
    Matrix (Fin e.n) (Fin e.n) (K' K K_bar A e) :=
  AlgEquiv.ofLinearEquiv (e'Aux (e := e)) (e'_map_one (e := e)) (e'_map_mul (e := e))

end one
