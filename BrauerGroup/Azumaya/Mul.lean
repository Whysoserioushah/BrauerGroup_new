import BrauerGroup.Azumaya.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import BrauerGroup.matrixkronecker
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Finiteness.Projective

suppress_compilation

universe u v

variable (R : Type u) [CommRing R]

open scoped TensorProduct

open MulOpposite

structure Azumaya (R : Type u) [CommRing R] extends AlgebraCat R where
  isAzumaya : IsAzumaya R carrier

@[coe]
instance : CoeSort (Azumaya R) (Type v) where
  coe s := s.carrier

attribute [instance] Azumaya.isAzumaya

def Azumaya.IsMoritaEquivalent : Azumaya R → Azumaya R → Prop :=
    fun A B ↦ _root_.IsMoritaEquivalent R A.carrier B.carrier

lemma Azumaya.IsMoritaEquivalent.iff {A B : Azumaya R} :
  Azumaya.IsMoritaEquivalent R A B ↔ _root_.IsMoritaEquivalent R A.carrier B.carrier :=
  Iff.rfl

abbrev AzuMorita.equiv : Equivalence (Azumaya.IsMoritaEquivalent R) where
  refl _ := Azumaya.IsMoritaEquivalent.iff R|>.2 <| ModuleCat.IsMoritaEquivalent.refl R
  symm h := Azumaya.IsMoritaEquivalent.iff R|>.2 <| ModuleCat.IsMoritaEquivalent.symm R
    <| Azumaya.IsMoritaEquivalent.iff R|>.1 h
  trans h1 h2 := Azumaya.IsMoritaEquivalent.iff R|>.2 <| ModuleCat.IsMoritaEquivalent.trans R
    (Azumaya.IsMoritaEquivalent.iff R|>.2 h1) <| Azumaya.IsMoritaEquivalent.iff R|>.2 h2

abbrev AzumayaSetoid : Setoid (Azumaya R) where
  r := Azumaya.IsMoritaEquivalent R
  iseqv := AzuMorita.equiv R

namespace Azumaya

variable (A B : Type v) [Ring A] [Ring B] [Algebra R A] [Algebra R B]
instance [Module.Finite R A] [Module.Finite R B] :
    Module.Finite R (A ⊗[R] B) := by exact Module.Finite.tensorProduct R A B

variable {R A B} in
instance FathfulSMul.tensor [Module.Projective R A] [Module.Projective R B]
    [FaithfulSMul R A] [FaithfulSMul R B] :
    FaithfulSMul R (A ⊗[R] B) where
  eq_of_smul_eq_smul {r1 r2} eq := by
    specialize eq 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul'] at eq
    have := Algebra.TensorProduct.includeLeft_injective (R := R) (S := R)
      (fun r1 r2 h ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
        exact eq_of_smul_eq_smul (M := R) (α := B) (m₁ := r1) (m₂ := r2) (by
          intro b
          rw [← one_mul b, ← smul_mul_assoc, h, smul_mul_assoc, one_mul])) eq
    exact eq_of_smul_eq_smul (M := R) (α := A) (m₁ := r1) (m₂ := r2) <|
      fun a ↦ by rw [← one_mul a, ← smul_mul_assoc, this, smul_mul_assoc, one_mul]

abbrev u (n : ℕ) : Fin n → (Fin n → R) := fun i ↦ Function.update (0 : Fin n → R) i 1

abbrev v (n : ℕ): Basis (Fin n) R (Fin n → R) := Basis.mk (v := u R n) (by
  rw [Fintype.linearIndependent_iff]
  refine fun f hf j ↦ ?_
  apply congrFun at hf
  specialize hf j
  change (∑ _, _ • Function.update _ _ _) _ = _ at hf
  simp only [Finset.sum_apply, Pi.smul_apply, Function.update_apply, Pi.zero_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at hf
  exact hf) <| fun x _ ↦ by
  refine mem_span_range_iff_exists_fun R|>.2 ⟨x, ?_⟩
  change ∑ i : Fin n, _ • Function.update _ _ _ = x
  ext j
  simp [Function.update_apply]

abbrev End_basis' (n : ℕ) : Fin n × Fin n → (Module.End R (Fin n → R)) := fun ⟨i, r⟩ ↦
  Basis.constr (v R n) R <| fun j ↦ if i = r then v R n j else 0

-- lemma End_basis'_apply (n : ℕ) (i r : Fin n) :
--   (End_basis' R n) (i, r) =
--     Basis.constr (v R n) R (fun j ↦ if i = r then v R n j else 0) := rfl

-- abbrev _root_.Module.End_basis (n : ℕ): Basis (Fin n × Fin n) R (Module.End R (Fin n → R)) :=
--   Basis.mk (v := End_basis' R n) (by
--   rw [Fintype.linearIndependent_iff]
--   intro f hf ⟨i0, r0⟩
--   rw [Fintype.sum_prod_type] at hf
--   simp [End_basis'_apply R n] at hf
--   rw [LinearMap.ext_iff] at hf
--   specialize hf (v R n i0)
--   simp only [Basis.coe_mk, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
--     Basis.constr_apply_fintype, Basis.equivFun_apply, Basis.mk_repr, smul_ite, smul_zero,
--     Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
--     LinearMap.zero_apply] at hf
--   -- rw [LinearMap.pi_ext_iff] at hf
--   -- simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
--   --   Basis.constr_apply_fintype, Basis.equivFun_apply, Basis.mk_repr, smul_ite, smul_zero,
--   --   Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
--   --   LinearMap.zero_apply] at hf


--   sorry
--   ) sorry

-- def eqqq (n : ℕ): Module.End R (Fin n → R) ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
--   algEquivMatrix'

abbrev Endtensor_algHom : Module.End R A ⊗[R] Module.End R B →ₐ[R] Module.End R (A ⊗[R] B) :=
    Module.endTensorEndAlgHom

open Algebra.TensorProduct in
variable {R A B} in
abbrev e : (A ⊗[R] Aᵐᵒᵖ) ⊗[R] B ⊗[R] Bᵐᵒᵖ ≃ₐ[R] (A ⊗[R] B) ⊗[R] (A ⊗[R] B)ᵐᵒᵖ :=
  (Algebra.TensorProduct.assoc R A B (Aᵐᵒᵖ ⊗[R] Bᵐᵒᵖ)|>.trans <|
  (congr (AlgEquiv.refl) (Algebra.TensorProduct.assoc R B Aᵐᵒᵖ Bᵐᵒᵖ)).symm.trans <|
  Algebra.TensorProduct.congr AlgEquiv.refl (congr (Algebra.TensorProduct.comm R _ _) AlgEquiv.refl) |>.trans
  <| Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.assoc R Aᵐᵒᵖ B Bᵐᵒᵖ) |>.trans
  <| Algebra.TensorProduct.assoc R A Aᵐᵒᵖ (B ⊗[R] Bᵐᵒᵖ)|>.symm).symm.trans
  <| congr AlgEquiv.refl <| opAlgEquiv R R A B

lemma e_apply (a : A) (b : B) (a' : Aᵐᵒᵖ) (b' : Bᵐᵒᵖ) :
  e ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) = (a ⊗ₜ b) ⊗ₜ op (a'.unop ⊗ₜ[R] b'.unop) := rfl

lemma top_sqaure_comm' (A B : Azumaya R) (a : A) (a' : Aᵐᵒᵖ) (b : B) (b' : Bᵐᵒᵖ) :
    ((TensorProduct.homTensorHomMap R A B A B) ∘ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))) ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) =
    ((AlgHom.mulLeftRight R (A ⊗[R] B)) ∘ e) ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) := by
  ext a0 b0
  simp [e_apply, AlgHom.mulLeftRight_apply, Module.endTensorEndAlgHom_apply]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 1000000 in
lemma top_sqaure_comm (A B : Azumaya R) :
    (TensorProduct.homTensorHomMap R A B A B) ∘ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))
    = (AlgHom.mulLeftRight R (A ⊗[R] B)) ∘ e := by
  ext aabb : 1
  induction aabb using TensorProduct.induction_on with
  | zero => rfl
  | tmul aa bb =>
    induction aa using TensorProduct.induction_on with
    | zero => simp [TensorProduct.zero_tmul]
    | tmul a1 a2 =>
      induction bb using TensorProduct.induction_on with
      | zero => simp [TensorProduct.zero_tmul]
      | tmul b1 b2 => rw [top_sqaure_comm']
      | add _ _ _ _ => simp_all [TensorProduct.tmul_add]
    | add _ _ _ _ => simp_all [TensorProduct.add_tmul]
  | add _ _ _ _ => simp_all [map_add]


/--
A ⊗ Aᵐᵒᵖ ⊗ B ⊗ B ᵐᵒᵖ --------> (A ⊗ B) ⊗ (A ⊗ B)ᵐᵒᵖ
        |                              |
        |                              |
        |                              |
        |                              |
      f ⊗ g            ---->         f ⊗ g
End R A ⊗ End R B ---------------> End R (A ⊗ B)
    |     |                           |   |
  i |     | j                     i'  |   |  j'
    |     |                           |   |
    |     |   `homTensorHomEquiv`     |   |
End R Rⁿ ⊗ End R Rᵐ -------------> End R (Rⁿ ⊗ Rᵐ)
-/
abbrev Endtensor_equiv [Module.Finite R A] [Module.Finite R B] [Module.Projective R A]
  [Module.Projective R B]: Module.End R A ⊗[R] Module.End R B ≃ₐ[R] Module.End R (A ⊗[R] B) := sorry

def EndRn_tensorequiv (n m : Type*) [Fintype m] [Fintype n]:
  Module.End R (n → R) ⊗[R] Module.End R (m → R) ≃ₐ[R] Module.End R ((n → R) ⊗[R] (m → R)) :=
  AlgEquiv.ofLinearEquiv (homTensorHomEquiv R (n → R) (m → R) (n → R) (m → R))
  (by simp [Algebra.TensorProduct.one_def]) <| fun fg1 fg2 ↦ by
  induction fg1 using TensorProduct.induction_on with
  | zero => simp
  | tmul f1 g1 =>
    induction fg2 using TensorProduct.induction_on with
    | zero => simp
    | tmul f2 g2 => ext; simp
    | add _ _ _ _ => simp_all [mul_add]
  | add _ _ _ _ => simp_all [add_mul]

lemma EndRn_tensorequiv_apply (n m : Type*) [Fintype m] [Fintype n] (f : Module.End R (n → R))
    (g : Module.End R (m → R)): EndRn_tensorequiv R n m (f ⊗ₜ[R] g) = TensorProduct.map f g := by
  simp [EndRn_tensorequiv]

-- open Module in
-- theorem Projective.exists_fin_free (P : Type v) [AddCommGroup P] [Module R P]
--     [Module.Projective R P] [fin : Module.Finite R P]: ∃(S : Finset P)
--     (i : P →ₗ[R] (S → R)) (s : (S → R) →ₗ[R] P) (_ : Function.Surjective s)
--     (_ : Function.Injective i), s.comp i = LinearMap.id := by
--   obtain ⟨S, hS⟩ := fin.fg_top
--   use S
--   have e1 := LinearEquiv.ofEq _ _ hS
--   have e2 := (Submodule.topEquiv (R := R) (M := P)).symm
--   use {
--     toFun := fun ⟨m, hm⟩ ↦ (fun ⟨i, hi⟩ ↦ mem_span_finset.1 hm|>.choose i)
--     map_add' := sorry
--     map_smul' := sorry
--   } ∘ₗ (e2.trans e1.symm).toLinearMap

theorem exists_comp_eq_id_of_projective (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M) (g : M →ₗ[R] Fin n → R),
      Function.Surjective f ∧ Function.Injective g ∧ f ∘ₗ g = .id :=
  have ⟨n, f, surj⟩ := Module.Finite.exists_fin' R M
  have ⟨g, hfg⟩ := Module.projective_lifting_property f .id surj
  ⟨n, f, g, surj, LinearMap.injective_of_comp_eq_id _ _ hfg, hfg⟩

abbrev nn [Module.Finite R A] [Module.Projective R A]: ℕ :=
  (Module.Finite.exists_comp_eq_id_of_projective R A).choose

abbrev f0 [Module.Finite R A] [Module.Projective R A]: (Fin (nn R A) → R) →ₗ[R] A :=
  (Module.Finite.exists_comp_eq_id_of_projective R A).choose_spec.choose

abbrev g0 [Module.Finite R A] [Module.Projective R A]: A →ₗ[R] Fin (nn R A) → R :=
  (Module.Finite.exists_comp_eq_id_of_projective R A).choose_spec.choose_spec.choose

lemma f0_inj [Module.Finite R A] [Module.Projective R A]: Function.Surjective (f0 R A) :=
  (Module.Finite.exists_comp_eq_id_of_projective R A).choose_spec.choose_spec.choose_spec|>.1

lemma g0_inj [Module.Finite R A] [Module.Projective R A]: Function.Injective (g0 R A) :=
  (Module.Finite.exists_comp_eq_id_of_projective R A).choose_spec.choose_spec.choose_spec|>.2.1

lemma fg [Module.Finite R A] [Module.Projective R A]: (f0 R A) ∘ₗ (g0 R A) = LinearMap.id :=
  (Module.Finite.exists_comp_eq_id_of_projective R A).choose_spec.choose_spec.choose_spec|>.2.2

abbrev inclusion1 [Module.Finite R A] [Module.Projective R A]:
  Module.End R A →ₗ[R] Module.End R ((Fin (nn R A)) → R) where
    toFun := fun f ↦ (g0 R A) ∘ₗ f ∘ₗ (f0 R A)
    map_add' := by simp [LinearMap.add_comp, LinearMap.comp_add]
    map_smul' := by simp [LinearMap.smul_comp, LinearMap.comp_smul]

abbrev projection1 [Module.Finite R A] [Module.Projective R A]:
  Module.End R ((Fin (nn R A)) → R) →ₗ[R] Module.End R A where
    toFun := fun f ↦ (f0 R A) ∘ₗ f ∘ₗ (g0 R A)
    map_add' := by simp [LinearMap.add_comp, LinearMap.comp_add]
    map_smul' := by simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma inclusion1_projection1 [Module.Finite R A] [Module.Projective R A]:
    (projection1 R A).comp (inclusion1 R A) = LinearMap.id := by
  ext f : 1
  simp [LinearMap.comp_assoc, fg]
  rw [← LinearMap.comp_assoc, fg, LinearMap.id_comp]

lemma Tensor_include_project [Module.Finite R A] [Module.Projective R A] [Module.Finite R B]
    [Module.Projective R B]:
    (TensorProduct.map (projection1 R A) (projection1 R B)).comp (TensorProduct.map (inclusion1 R A)
      (inclusion1 R B)) = LinearMap.id := by
    simp [← TensorProduct.map_comp, inclusion1_projection1]

-- lemma TensorAB_is_directsummand [Module.Finite R A] [Module.Projective R A] [Module.Finite R B]
--     [Module.Projective R B]:
--     ∃(s1 : Module.End R (A ⊗[R] B) →ₗ[R] Module.End R ((nn R A → R) ⊗[R] (nn R B → R)))
--       (s2 : Module.End R ((nn R A → R) ⊗[R] (nn R B → R)) →ₗ[R] Module.End R (A ⊗[R] B)),

abbrev inclusiononLeft [Module.Finite R A] [Module.Projective R A] [Module.Finite R B]
    [Module.Projective R B]: Module.End R A ⊗[R] Module.End R B →ₗ[R]
    Module.End R (Fin (nn R A) → R) ⊗[R] Module.End R (Fin (nn R B) → R):=
  TensorProduct.map (inclusion1 R A) (inclusion1 R B)


-- lemma tensor_bij (A B : Azumaya R): Function.Bijective (AlgHom.mulLeftRight R (A ⊗[R] B)) :=
--   ⟨fun abab1 abab2 h ↦ by
--   induction abab1 using TensorProduct.induction_on with
--   | zero =>
--     induction abab2 using TensorProduct.induction_on with
--     | zero => rfl
--     | tmul ab2 ab2' =>
--       rw [DFunLike.ext_iff] at h
--       specialize h 1
--       simp only [map_zero, Algebra.TensorProduct.one_def, LinearMap.zero_apply,
--         AlgHom.mulLeftRight_apply] at h
--       induction ab2 using TensorProduct.induction_on with
--       | zero => exact zero_tmul _ _ |>.symm
--       | tmul a1 b1 =>
--         -- set ab22 := unop ab2'
--         -- change 0 = _ ⊗ₜ op ab22
--         -- induction ab2' using TensorProduct.induction_on with
--         -- | zero => rw [op_zero, tmul_zero]
--         -- | tmul a' b' =>
--         --   rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one] at h
--         --   -- change 0 = (a1 ⊗ₜ b1) * (a' ⊗ₜ b') at h


--         --   sorry
--         -- | add _ _ _ _ =>
--         sorry
--       | add _ _ _ _ => sorry
--     | add _ _ _ _ => sorry
--   | tmul ab ab' => sorry
--   | add _ _ _ _ => sorry
--   , sorry⟩

def mul (A B : Azumaya R) : Azumaya R := {
  __ := AlgebraCat.of R (A.carrier ⊗[R] B.carrier)
  isAzumaya := {
    out := Module.Projective.tensorProduct|>.out
    eq_of_smul_eq_smul := Azumaya.FathfulSMul.tensor|>.eq_of_smul_eq_smul
    fg_top := Module.Finite.tensorProduct R A B|>.fg_top
    bij := by
      sorry
  }}






end Azumaya

section formathlib

variable (R : Type u) [CommRing R] (M N P Q: Type v) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Projective R M]
  [Module.Projective R N] [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]

abbrev nn : ℕ := (Module.Finite.exists_comp_eq_id_of_projective R M).choose

abbrev f0 : (Fin (nn R M) → R) →ₗ[R] M := (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose

abbrev g0 : M →ₗ[R] Fin (nn R M) → R := (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose

lemma f0_surj : Function.Surjective (f0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.1

lemma g0_inj : Function.Injective (g0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.1

lemma fg : (f0 R M) ∘ₗ (g0 R M) = LinearMap.id :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.2

abbrev inclusion1 : (M →ₗ[R] P) →ₗ[R] ((Fin (nn R M) → R) →ₗ[R] P) where
  toFun := fun f ↦ f.comp (f0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

abbrev projection1 : ((Fin (nn R M) → R) →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) where
  toFun := fun f ↦ f.comp (g0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

/-- Hom(M, P) ⊗ Hom(N, Q) →ₗ[R] Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -/
abbrev tensor_inclusion1 : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R] ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q) :=
  TensorProduct.map (inclusion1 R M P) (inclusion1 R N Q)

abbrev tensor_projection1 := TensorProduct.map (projection1 R M P) (projection1 R N Q)

lemma projection_inlusion1 : (projection1 R M P).comp (inclusion1 R M P) = LinearMap.id := by
  ext f : 1
  simp [LinearMap.comp_assoc, fg]

lemma tensor_inclusion1_projection1 : (tensor_projection1 R M N P Q).comp
    (tensor_inclusion1 R M N P Q) = LinearMap.id := by
  simp [← TensorProduct.map_comp, projection_inlusion1]

lemma tensor_inclusion1_projection1_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)): (tensor_projection1 R M N P Q)
    ((tensor_inclusion1 R M N P Q) x) = x :=
  DFunLike.congr_fun (tensor_inclusion1_projection1 R M N P Q) x

lemma tensor_inclusion1_inj: Function.Injective (tensor_inclusion1 R M N P Q) := by
  exact Function.LeftInverse.injective (g := tensor_projection1 R M N P Q)
    <| DFunLike.congr_fun <| tensor_inclusion1_projection1 R M N P Q

open TensorProduct in
lemma Tensor_isDirectSummand : ∃(s0 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R))
    (s1 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N), s1.comp s0 = .id :=
  ⟨map (g0 R M) (g0 R N), map (f0 R M) (f0 R N), by simp [← map_comp, fg]⟩

variable {R M N} in
abbrev inclusion2 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) :=
  TensorProduct.map (g0 R M) (g0 R N)

variable {R M N} in
abbrev projection2 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (f0 R M) (f0 R N)

variable {M N} in
abbrev tensor_inclusion2 : (M ⊗[R] N →ₗ[R] P ⊗[R] Q) →ₗ[R]
    ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp projection2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

variable {M N} in
abbrev tensor_projection2 : ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R]
    P ⊗[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp inclusion2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

lemma projection2_inclusion2 : (projection2).comp (inclusion2) =
    LinearMap.id (R := R) (M := M ⊗[R] N) :=
  by simp [← TensorProduct.map_comp, fg]

lemma projection2_inclusion2_apply (x : M ⊗[R] N): (projection2) ((inclusion2) x) = x :=
  DFunLike.congr_fun (projection2_inclusion2 R M N) x

lemma tensor_projection2_inclusion2 : (tensor_projection2 R P Q).comp (tensor_inclusion2 R P Q) =
    LinearMap.id (R := R) (M := M ⊗[R] N →ₗ[R] P ⊗[R] Q) := by
  ext f : 1
  simp [LinearMap.comp_assoc, projection2_inclusion2]

lemma tensor_inclusion2_inj : Function.Injective (tensor_inclusion2 R (M := M) (N := N) P Q) := by
  exact Function.LeftInverse.injective (g := tensor_projection2 R P Q)
    <| DFunLike.congr_fun <| tensor_projection2_inclusion2 R M N P Q

lemma comm_square2: (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap ∘ₗ
    tensor_inclusion1 R M N P Q =
    tensor_inclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap R M N P Q := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

lemma comm_square2_apply (f : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):
  (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap
    (tensor_inclusion1 R M N P Q f) = tensor_inclusion2 R P Q (TensorProduct.homTensorHomMap R M N P Q f) :=
  DFunLike.congr_fun (comm_square2 R M N P Q) f

lemma homTensorHomMap_inj : Function.Injective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Injective.of_comp (f := tensor_inclusion2 R P Q)
  rw [← LinearMap.coe_comp, ← comm_square2]
  exact Function.Injective.comp (f := tensor_inclusion1 R M N P Q)
    (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).injective <|
    tensor_inclusion1_inj R M N P Q

lemma comm_sqaure3: (homTensorHomEquiv R _ _ _ _).toLinearMap ∘ₗ
    tensor_inclusion1 R M N P Q ∘ₗ tensor_projection1 R M N P Q = tensor_inclusion2 R P Q ∘ₗ
    tensor_projection2 R P Q ∘ₗ (homTensorHomEquiv R _ _ _ _).toLinearMap := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

lemma comm_square3_apply (f : ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q)):
    (homTensorHomEquiv R _ _ _ _) (tensor_inclusion1 R M N P Q (tensor_projection1 R M N P Q f)) =
    tensor_inclusion2 R P Q (tensor_projection2 R P Q (homTensorHomEquiv R _ _ _ _ f)) :=
  DFunLike.congr_fun (comm_sqaure3 R M N P Q) f

lemma comm_square1: tensor_projection1 R M N P Q ∘ₗ (homTensorHomEquiv R _ _ P Q).symm.toLinearMap ∘ₗ
    tensor_inclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap R M N P Q =
    LinearMap.id (R := R) (M := (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):= by
  rw [← comm_square2]
  apply LinearMap.ext
  simp [-homTensorHomEquiv_toLinearMap, -homTensorHomEquiv_apply, tensor_inclusion1_projection1_apply]


lemma comm_square4: TensorProduct.homTensorHomMap R M N P Q ∘ₗ tensor_projection1 R M N P Q ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensor_inclusion2 R P Q =
    LinearMap.id (R := R) (M := (M ⊗[R] N) →ₗ[R] P ⊗[R] Q) := by
  apply LinearMap.ext
  intro fgfg
  simp only [LinearMap.comp_apply]
  apply tensor_inclusion2_inj
  rw [← comm_square2_apply, LinearEquiv.coe_toLinearMap, comm_square3_apply]
  simp [LinearMap.comp_assoc]
  apply LinearMap.ext
  simp [projection2_inclusion2_apply]

lemma homTensorHomMap_surj: Function.Surjective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Surjective.of_comp (g := (tensor_projection1 R M N P Q ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensor_inclusion2 R P Q))
  rw [← LinearMap.coe_comp, comm_square4]
  exact CharacterModule.surjective_of_dual_injective LinearMap.id fun ⦃a₁ a₂⦄ a ↦ a


/--          `TensorProduct.homTensorHomMap`
Hom(M, P) ⊗ Hom(N, Q) ---------------> Hom(M ⊗ N, P ⊗ Q)
    |       |                             |      |
 i  |       |  j                       i' |      |  j'
    |       |                             |      |
    |       |                             |      |
Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -------------> Hom(Rⁿ ⊗ Rᵐ, P ⊗ Q)
-/
theorem todo : 1 = 1 := rfl

end formathlib
