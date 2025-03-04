import BrauerGroup
import Mathlib

universe u v w

open scoped TensorProduct

variable (K F E K_bar: Type u) [Field K] [Field F] [Field E] [Algebra K F]
  [Algebra K E] [Field K_bar] [Algebra K K_bar] [hK_bar : IsAlgClosure K K_bar] (A : CSA K)
  (n : ℕ) [NeZero n] (e : F ⊗[K] A ≃ₐ[F] Matrix (Fin n) (Fin n) F)

suppress_compilation
#check TensorProduct.AlgebraTensorModule.assoc

set_option maxSynthPendingDepth 2 in
def Algebra.TensorProduct.assoc' (R S R' A B C : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [Semiring A] [Semiring B] [Semiring C] [Algebra R R'] [Algebra R A]
    [Algebra R' A] [Algebra R B] [Algebra R' B] [Algebra R C]
    [IsScalarTower R R' A] [IsScalarTower R R' B] [Algebra S A] [Algebra R S] [Algebra R' S]
    [IsScalarTower R' S A] [IsScalarTower R S A]:
    (A ⊗[R'] B) ⊗[R] C ≃ₐ[S] A ⊗[R'] B ⊗[R] C :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.assoc _ _ _ _ _ _)
    rfl (LinearMap.map_mul_iff _|>.2 <| by ext; simp)
  -- [inst_3 : Algebra R A] [inst_4 : Algebra R B] [inst_5 : AddCommMonoid M] [inst_6 : Module R M] [inst_7 : Module A M]
  -- [inst_8 : Module B M] [inst_9 : IsScalarTower R A M] [inst_10 : IsScalarTower R B M] [inst_11 : SMulCommClass A B M]
  -- [inst_12 : AddCommMonoid P] [inst_13 : Module A P] [inst_14 : AddCommMonoid Q] [inst_15 : Module R Q]
  -- [inst_16 : Module R P] [inst_17 : IsScalarTower R A P] [inst_18 : Algebra A B] [inst_19 : IsScalarTower A B M] :
  -- (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] P ⊗[R] Q := sorry

instance [Algebra F E] [IsScalarTower K F E]: IsScalarTower K (Algebra.ofId F E).range E where
  smul_assoc k := fun ⟨f, hf⟩ x ↦ by
    change (k • f) • _ = k • f • x
    exact smul_assoc _ _ _

instance [Algebra F E] : Algebra (Algebra.ofId F E).range F :=
  RingHom.toAlgebra (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm

instance [Algebra F E] [IsScalarTower K F E]: IsScalarTower K (Algebra.ofId F E).range F where
  smul_assoc k := fun ⟨e, he⟩ x ↦ by
    simp only [RingHom.smul_toAlgebra, RingHom.coe_coe]
    change (AlgEquiv.restrictScalars K (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm) _ * _ = _
    rw [map_smul]
    simp

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 400000 in
lemma mat_over_extension [Algebra F E] [IsScalarTower K F E] (a : A):
    ∃ g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E, g (1 ⊗ₜ a) =
    (Algebra.ofId F E).mapMatrix (e (1 ⊗ₜ a)) := by
  let e1 : (Algebra.ofId F E).range ≃ₐ[F] F := (AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm
  let e1' : (Algebra.ofId F E).range ≃ₐ[(Algebra.ofId F E).range] F :=
    AlgEquiv.ofRingEquiv (f := e1) (fun ⟨x, hx⟩ ↦ by
      simp [e1, AlgEquiv.ofInjectiveField, Algebra.algebraMap_eq_smul_one, RingHom.smul_toAlgebra]
      rfl)
  let e' : F ⊗[K] A ≃ₐ[(Algebra.ofId F E).range] Matrix (Fin n) (Fin n) F :=
    AlgEquiv.ofRingEquiv (f := e) <| fun ⟨x, hx⟩ ↦ by
      simp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, RingHom.smul_toAlgebra]
      conv_lhs => erw [← mul_one ((AlgEquiv.ofInjectiveField (Algebra.ofId F E)).symm ⟨x, hx⟩),
        ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_one]
      rfl
  let e2 : E ≃ₐ[E] E ⊗[(Algebra.ofId F E).range] (Algebra.ofId F E).range :=
    Algebra.TensorProduct.rid _ _ _|>.symm
  have assoc := Algebra.TensorProduct.assoc' K E (Algebra.ofId F E).range
    E (Algebra.ofId F E).range A
  -- haveI : Algebra (Algebra.ofId F E).range (F ⊗[F] A)
  let e3 : (Algebra.ofId F E).range ⊗[K] A ≃ₐ[(Algebra.ofId F E).range]
      Matrix (Fin n) (Fin n) (Algebra.ofId F E).range :=
    Algebra.TensorProduct.congr e1' AlgEquiv.refl |>.trans <| e'.trans e1'.mapMatrix.symm
  let g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E :=
    Algebra.TensorProduct.congr e2 AlgEquiv.refl |>.trans <| assoc.trans <|
    Algebra.TensorProduct.congr AlgEquiv.refl e3 |>.trans <|
    (AlgEquiv.ofRingEquiv (f := matrixEquivTensor (Fin n) (Algebra.ofId F E).range E) <|
    fun x ↦ by
      simp only [Algebra.range_ofId, AlgEquiv.coe_ringEquiv,
        Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
      simp [Matrix.algebraMap_eq_diagonal, -matrixEquivTensor_apply]
      sorry ).symm

  sorry

variable {K F n} in
def ReducedCharPoly (a : A): Polynomial F := Matrix.charpoly (e (1 ⊗ₜ a))

namespace ReducedCharPoly
lemma over_extension [Algebra F E] [IsScalarTower K F E] (a : A):
    ∃ g : E ⊗[K] A ≃ₐ[E] Matrix (Fin n) (Fin n) E, ReducedCharPoly A
    (extension_over_split K K_bar A F E ⟨n, e⟩).3 a =
    Polynomial.mapAlgHom (Algebra.ofId F E) (ReducedCharPoly A e a) := sorry



#check AlgHom.mapMatrix

end ReducedCharPoly
