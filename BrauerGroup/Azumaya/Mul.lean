import BrauerGroup.Azumaya.Basic
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import BrauerGroup.matrixkronecker
import Mathlib.LinearAlgebra.Contraction

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
    ((Endtensor_algHom R A B) ∘ (Algebra.TensorProduct.congr
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R A) A.isAzumaya.bij)
    (AlgEquiv.ofBijective (AlgHom.mulLeftRight R B) B.isAzumaya.bij))) ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) =
    ((AlgHom.mulLeftRight R (A ⊗[R] B)) ∘ e) ((a ⊗ₜ a') ⊗ₜ (b ⊗ₜ b')) := by
  ext a0 b0
  simp [e_apply, AlgHom.mulLeftRight_apply, Module.endTensorEndAlgHom_apply]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 1000000 in
lemma top_sqaure_comm (A B : Azumaya R) :
    (Endtensor_algHom R A B) ∘ (Algebra.TensorProduct.congr
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
    |     | `homTensorHomEquiv`       |   |
End R Rⁿ ⊗ End R Rᵐ -------------> End R (Rⁿ ⊗ Rᵐ)
  --     |                                |
  --     |                                |   not needed now that there is `homTensorHomEquiv`
  --     |                                |
  --     |                                |
  -- MₙR ⊗ MₘR   --------------->        MₙₘR
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

open Module in
theorem Projective.exists_fin_free (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Projective R P] [fin : Module.Finite R P]: ∃(S : Finset P)
    (i : P →ₗ[R] (S → R)) (s : (S → R) →ₗ[R] P) (_ : Function.Surjective s)
    (_ : Function.Injective i), s.comp i = LinearMap.id := by
  obtain ⟨S, hS⟩ := fin.fg_top
  use S
  have e1 := LinearEquiv.ofEq _ _ hS
  have e2 := (Submodule.topEquiv (R := R) (M := P)).symm
  use {
    toFun := fun ⟨m, hm⟩ ↦ (fun ⟨i, hi⟩ ↦ mem_span_finset.1 hm|>.choose i)
    map_add' := sorry
    map_smul' := sorry
  } ∘ₗ (e2.trans e1.symm).toLinearMap

  sorry


#check Submodule.span
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
