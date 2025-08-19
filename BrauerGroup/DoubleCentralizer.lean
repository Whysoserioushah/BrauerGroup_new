/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import BrauerGroup.LemmasAboutSimpleRing
import BrauerGroup.SkolemNoether
import Mathlib.RingTheory.SimpleRing.Field

universe u v

variable {F A : Type u}
variable [Field F] [Ring A] [Algebra F A]
variable [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A]
variable (B : Subalgebra F A) [IsSimpleRing B]

open Module TensorProduct

section lemma1

variable {F A A' : Type u}
variable [Field F] [Ring A] [Algebra F A] [Ring A'] [Algebra F A']
variable (B : Subalgebra F A) (B' : Subalgebra F A')
variable {ι ι' : Type*} (𝒜 : Basis ι F A) (𝒜' : Basis ι' F A')

set_option synthInstance.maxHeartbeats 40000 in
include 𝒜' in
lemma centralizer_inclusionLeft :
    Subalgebra.centralizer F (A := A ⊗[F] A')
      (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := A') |>.comp
        B.val).range =
      (Algebra.TensorProduct.map (Subalgebra.centralizer F B).val (AlgHom.id F A')).range := by
  classical
  refine le_antisymm ?_ ?_
  · rintro x hx
    obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_right 𝒜' x
    refine Subalgebra.sum_mem _ fun i hi => ?_
    simp only [AlgHom.mem_range]
    refine ⟨⟨s i, fun b hb => ?_⟩ ⊗ₜ 𝒜' i, by simp⟩
    have eq := hx (b ⊗ₜ 1) (by simpa using ⟨b, hb, rfl⟩)
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at eq
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at eq
    simp_rw [← sub_tmul] at eq
    have := IsCentralSimple.TensorProduct.sum_tmul_basis_right_eq_zero' (h := eq)
    specialize this i hi
    rw [sub_eq_zero] at this
    exact this
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Subalgebra.coe_val,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      congr 1
      exact a.2 _ y.2
    | add x y hx hy =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Subalgebra.coe_val,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, map_add] at hx hy ⊢
      simp [mul_add, hx, hy, add_mul]

set_option synthInstance.maxHeartbeats 40000 in
include 𝒜 in
lemma centralizer_inclusionRight :
    Subalgebra.centralizer F (A := A ⊗[F] A')
      (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := A') |>.comp
        B'.val).range =
      (Algebra.TensorProduct.map (AlgHom.id F A) (Subalgebra.centralizer F B').val).range := by
  classical
  refine le_antisymm ?_ ?_
  · rintro x hx
    obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_left 𝒜 x
    refine Subalgebra.sum_mem _ fun i hi => ?_
    simp only [AlgHom.mem_range]
    refine ⟨𝒜 i ⊗ₜ ⟨s i, fun b hb => ?_⟩, by simp⟩
    have eq := hx (1 ⊗ₜ b) (by simpa using ⟨b, hb, rfl⟩)
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at eq
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at eq
    simp_rw [← tmul_sub] at eq
    have := IsCentralSimple.TensorProduct.sum_tmul_basis_left_eq_zero' (h := eq)
    specialize this i hi
    rw [sub_eq_zero] at this
    exact this

  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Subalgebra.coe_val,
        Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      congr 1
      exact b.2 _ y.2
    | add x y hx hy =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Subalgebra.coe_val,
        Function.comp_apply, Algebra.TensorProduct.includeRight_apply, map_add] at hx hy ⊢
      simp [mul_add, hx, hy, add_mul]

lemma centralizer_tensor_le_inf_centralizer :
    Subalgebra.centralizer F (A := A ⊗[F] A')
      ((Algebra.TensorProduct.map B.val B'.val).range :
        Subalgebra F (A ⊗[F] A')) ≤
    Subalgebra.centralizer F (A := A ⊗[F] A')
      (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := A') |>.comp
        B.val).range ⊓
    Subalgebra.centralizer F (A := A ⊗[F] A')
      (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := A') |>.comp
        B'.val).range := by
  intro x hx
  rw [← Subalgebra.centralizer_sup]
  intro y hy
  apply hx
  rw [Algebra.TensorProduct.map_range]
  exact hy

set_option synthInstance.maxHeartbeats 40000 in
include 𝒜 𝒜' in
lemma centralizer_tensor_centralizer :
    Subalgebra.centralizer F (A := A ⊗[F] A')
      ((Algebra.TensorProduct.map B.val B'.val).range :
          Subalgebra F (A ⊗[F] A')) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer F B).val
      (Subalgebra.centralizer F B').val).range := by
  refine le_antisymm ?_ ?_
  ·
    have := Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := B') |>.comp B.val
    have ineq1 :
        Subalgebra.centralizer F (A := A ⊗[F] A')
          ((Algebra.TensorProduct.map B.val B'.val).range :
            Subalgebra F (A ⊗[F] A')) ≤
        Subalgebra.centralizer F (A := A ⊗[F] A')
          (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := A') |>.comp
            B.val).range ⊓
        Subalgebra.centralizer F (A := A ⊗[F] A')
          (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := A') |>.comp
            B'.val).range := by
      apply centralizer_tensor_le_inf_centralizer

    have eq1 : Subalgebra.centralizer F (A := A ⊗[F] A')
          (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := A') |>.comp
            B.val).range =
          (Algebra.TensorProduct.map (Subalgebra.centralizer F B).val (AlgHom.id F A')).range := by
      apply centralizer_inclusionLeft (𝒜' := 𝒜')

    have eq2 : Subalgebra.centralizer F (A := A ⊗[F] A')
          (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := A') |>.comp
            B'.val).range =
          (Algebra.TensorProduct.map (AlgHom.id F A) (Subalgebra.centralizer F B').val).range := by
      apply centralizer_inclusionRight (𝒜 := 𝒜)

    refine ineq1.trans ?_

    rw [eq1, eq2]
    have := IsCentralSimple.TensorProduct.submodule_tensor_inf_tensor_submodule F A A'
      (Subalgebra.toSubmodule <| Subalgebra.centralizer F (B : Set A))
      (Subalgebra.toSubmodule <| Subalgebra.centralizer F (B' : Set A'))

    intro x (hx : x ∈ Subalgebra.toSubmodule (_ ⊓ _))
    suffices x ∈
      (LinearMap.range <| TensorProduct.map
        (Subalgebra.toSubmodule <| Subalgebra.centralizer F (B : Set A)).subtype
        (Subalgebra.toSubmodule <| Subalgebra.centralizer F (B' : Set A')).subtype) by
      exact this
    rw [← this]
    exact hx

  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul a b =>
      simp only [AlgHom.coe_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, Subalgebra.coe_val, Subalgebra.mem_centralizer_iff,
        Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp only [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val,
          Algebra.TensorProduct.tmul_mul_tmul]
        congr 1
        · exact a.2 x x.2
        · exact b.2 y y.2
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy, mul_add]
    | add x y hx hy =>
      rw [RingHom.map_add]
      exact Subalgebra.add_mem _ hx hy

end lemma1

section lemma2

section central_simple_case

variable (F B : Type u)
variable [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]

lemma centralizer_mulLeft_le_of_isCentralSimple :
    (Subalgebra.centralizer F (Set.range <| LinearMap.mulLeft F : Set  <| Module.End F B) : Set _) ≤
    Set.range (LinearMap.mulRight F (A := B)) := by
  intro (x : Module.End F B) hx
  let eqv := tensor_self_op.equivEnd F B
  have hx' : eqv.symm x ∈ Subalgebra.centralizer F
    ((Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := B) (B := Bᵐᵒᵖ)).range :
      Set (B ⊗[F] Bᵐᵒᵖ)) := by
    rintro _ ⟨y, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
      eqv]
    apply_fun eqv
    simp only [map_mul]
    rw [show eqv (y ⊗ₜ[F] 1) = LinearMap.mulLeft F y by
      ext x
      simp only [LinearMap.mulLeft_apply]
      simp only [tensor_self_op.equivEnd, tensor_self_op.toEnd, AlgEquiv.coe_ofBijective,
        Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, MulOpposite.unop_one, mul_one, Module.End.mul_apply, LinearMap.coe_mk,
        AddHom.coe_mk, eqv] ]
    ext b
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
    -- change y * (eqv (eqv.symm x)) b = (eqv (eqv.symm x)) (y * b)
    rw [eqv.apply_symm_apply]
    exact congr($(hx (LinearMap.mulLeft F y) (by simp)) b)

  have eq : Subalgebra.centralizer F
    ((Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := B) (B := Bᵐᵒᵖ)).range :
      Set (B ⊗[F] Bᵐᵒᵖ)) =
    (Algebra.TensorProduct.includeRight (R := F) (A := B) (B := Bᵐᵒᵖ)).range := by
    refine le_antisymm ?_ ?_
    · set ℬ := Module.finBasis F Bᵐᵒᵖ
      intro z hz
      obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ z
      refine Subalgebra.sum_mem _ fun i hi => ?_
      have : (s i) ∈ Subalgebra.center F B := by
        rw [Subalgebra.mem_center_iff]
        intro b'
        have eq := hz (b' ⊗ₜ 1) (by simp)
        simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          Finset.sum_mul, mul_one] at eq
        rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at eq
        simp_rw [← TensorProduct.sub_tmul] at eq
        replace eq := IsCentralSimple.TensorProduct.sum_tmul_basis_right_eq_zero' (h := eq)
        specialize eq i hi
        rw [sub_eq_zero] at eq
        exact eq
      rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at this
      obtain ⟨x, hx⟩ := this
      dsimp only
      rw [← hx, Algebra.algebraMap_eq_smul_one, ← smul_tmul']
      exact Subalgebra.smul_mem _ (by simp) _
    · set ℬ := Module.finBasis F B
      rintro _ ⟨z, rfl⟩ _ ⟨y, rfl⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]

  rw [eq] at hx'
  obtain ⟨y, hy⟩ := hx'
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] at hy
  apply_fun eqv at hy
  simp only [AlgEquiv.apply_symm_apply] at hy
  rw [← hy]
  refine ⟨y.unop, ?_⟩
  ext c
  simp only [LinearMap.mulRight_apply, tensor_self_op.equivEnd, tensor_self_op.toEnd,
    AlgEquiv.coe_ofBijective, Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, one_mul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk,
    eqv]

end central_simple_case

variable {F B : Type u}
variable [Field F] [Ring B] [Algebra F B] [IsSimpleRing B] [FiniteDimensional F B]

variable (F B) in
set_option synthInstance.maxHeartbeats 40000 in
def centralizerMulLeftCopy :
    (Subalgebra.centralizer F (Set.range (LinearMap.mulLeft F) : Set <| Module.End F B)) →ₗ[F]
    (B →ₗ[Subalgebra.center F B] B) where
  toFun a :=
  { toFun := a
    map_add' := a.1.map_add
    map_smul' := by
      intro c x
      simp only [RingHom.id_apply]
      rw [show c • x = c.1 * x by rfl]
      have eq : c.1 * a.1 x = a.1 (c.1 * x) :=
        congr($(a.2 (LinearMap.mulLeft F c.1) (by simp)) x)
      rw [← eq]; rfl }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : SMulCommClass (Subalgebra.center F B) B B where
  smul_comm x y z := by
    change x.1 * (y * z) = y * (x.1 * z)
    rw [← mul_assoc, ← Subalgebra.mem_center_iff.1 x.2 y, mul_assoc]

noncomputable instance center_field : Field (Subalgebra.center F B) :=
  IsField.toField <| IsSimpleRing.isField_center _

instance center_algebra : Algebra (Subalgebra.center F B) B where
  smul a b := a.1 • b
  algebraMap := {
    toFun a := a.1
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
  }
  commutes' x y := by
    simpa using Subalgebra.mem_center_iff.1 x.2 y |>.symm
  smul_def' _ _ := rfl

instance : FiniteDimensional (Subalgebra.center F B) B :=
  FiniteDimensional.right F (Subalgebra.center F B) B

variable (F B) in
@[simps]
def Module.End.leftMul : Subalgebra F (Module.End F B) where
  carrier := Set.range <| LinearMap.mulLeft F
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x * y, ?_⟩
    ext z
    simp
  one_mem' := by
    refine ⟨1, ?_⟩
    simp only [LinearMap.mulLeft_one]
    rfl
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    ext z
    simp [add_mul]
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext z
    simp
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap _ _ c, ?_⟩
    ext z
    simp [Algebra.smul_def]

variable (F B) in
def Module.End.rightMul : Subalgebra F (Module.End F B) where
  carrier := Set.range <| LinearMap.mulRight F
  one_mem' := ⟨1, by ext; simp⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    ext z
    simp [mul_add]
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext z
    simp
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨y * x, ?_⟩
    ext z
    simp
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap _ _ c, ?_⟩
    ext z
    simp only [LinearMap.mulRight_apply, algebraMap_end_apply]
    rw [Algebra.smul_def, Algebra.commutes c z]

noncomputable def Module.End.rightMulEquiv : Module.End.rightMul F B ≃ₐ[F] Bᵐᵒᵖ :=
AlgEquiv.symm <| AlgEquiv.ofBijective
  { toFun x := ⟨LinearMap.mulRight F x.unop, Set.mem_range_self _⟩
    map_one' := by ext; simp
    map_mul' := by intros; ext; simp
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp [mul_add]
    commutes' := by intros; ext; simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      LinearMap.mulRight_apply, SubalgebraClass.coe_algebraMap, algebraMap_end_apply,
      Algebra.smul_def, Algebra.commutes] } <| by
  constructor
  · intro x y hxy
    have := congr($hxy.1 1)
    simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.mulRight_apply, one_mul, MulOpposite.unop_inj] at this
    exact this
  · rintro ⟨_, ⟨x, rfl⟩⟩
    use (MulOpposite.op x)
    ext
    simp

lemma centralizer_mulLeft :
    Subalgebra.centralizer F (Module.End.leftMul F B : Set <| Module.End F B) =
    (Module.End.rightMul F B) := by
  refine le_antisymm ?_ ?_
  · suffices eq :
        (Subalgebra.centralizer (Subalgebra.center F B)
          (Set.range <| LinearMap.mulLeft (Subalgebra.center F B) :
            Set  <| Module.End (Subalgebra.center F B) B) : Set _) ≤
        Set.range (LinearMap.mulRight (Subalgebra.center F B) (A := B)) by
      intro a ha
      set a' : B →ₗ[Subalgebra.center F B] B :=
      { __ := a
        map_smul' := by
          intro c x
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
          rw [show c • x = c.1 * x by rfl]
          have eq : c.1 * a x = a (c.1 * x) :=
            congr($(ha (LinearMap.mulLeft F c.1) (by simp)) x)
          rw [← eq]; rfl }
      obtain ⟨b, hb⟩ := @eq a' (by
        rintro _ ⟨y, rfl⟩
        ext b
        simp only [Module.End.mul_apply, LinearMap.coe_mk, LinearMap.coe_toAddHom,
          LinearMap.mulLeft_apply, a']
        exact congr($(ha (LinearMap.mulLeft F y) (by simp)) b))
      refine ⟨b, ?_⟩
      ext c
      exact congr($hb c)

    haveI : Algebra.IsCentral (Subalgebra.center F B) B :=
    { out := by
        intro x hx
        rw [Algebra.mem_bot]
        exact ⟨⟨x, hx⟩, rfl⟩ }
    apply centralizer_mulLeft_le_of_isCentralSimple

  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    ext z
    simp only [Module.End.mul_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]

end lemma2

@[simps]
def Subalgebra.conj (B : Subalgebra F A) (x : Aˣ) : Subalgebra F A where
  carrier := {y | ∃ b ∈ B, y = x * b * x⁻¹}
  mul_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨b * c, B.mul_mem hb hc, by simp [mul_assoc]⟩
  one_mem' := by
    exact ⟨1, B.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨b + c, B.add_mem hb hc, by simp [mul_add, add_mul]⟩
  zero_mem' := by
    exact ⟨0, B.zero_mem, by simp⟩
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap _ _ c, B.algebraMap_mem c, ?_⟩
    rw [mul_assoc, Algebra.commutes c (x⁻¹).1, ← mul_assoc]
    simp

omit [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] in
lemma Subalgebra.mem_conj {B : Subalgebra F A} {x : Aˣ} {y : A} :
    y ∈ B.conj x ↔ ∃ b ∈ B, y = x * b * x⁻¹ := by
  simp only [conj]
  rfl

@[simps]
def Subalgebra.toConj (B : Subalgebra F A) (x : Aˣ) : B →ₐ[F] B.conj x where
  toFun b := ⟨x * b * x⁻¹, by simp [Subalgebra.mem_conj]⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intros y z
    ext
    simp only [MulMemClass.coe_mul, MulMemClass.mk_mul_mk, mul_assoc]
    rw [← mul_assoc x⁻¹.1, Units.inv_mul, one_mul]
  map_zero' := by ext; simp
  map_add' := by
    intros y z
    ext
    simp only [AddMemClass.coe_add, mul_add, add_mul, AddMemClass.mk_add_mk]
  commutes' := by
    intros r
    ext
    simp only [SubalgebraClass.coe_algebraMap, mul_assoc]
    rw [Algebra.commutes r, ← mul_assoc]
    simp only [Units.mul_inv, one_mul]

@[simps]
def Subalgebra.fromConj (B : Subalgebra F A) (x : Aˣ) : B.conj x →ₐ[F] B where
  toFun b := ⟨x⁻¹ * b * x, by
    rcases b with ⟨_, ⟨b, hb, rfl⟩⟩
    simpa [mul_assoc]⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intros; ext; simp only [MulMemClass.coe_mul, ← mul_assoc, MulMemClass.mk_mul_mk,
      Units.mul_inv_cancel_right]
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp [mul_add, add_mul]
  commutes' := by intros; ext; simp [← Algebra.commutes]

def Subalgebra.conjEquiv (B : Subalgebra F A) (x : Aˣ) : B ≃ₐ[F] B.conj x :=
  AlgEquiv.ofAlgHom (B.toConj x) (B.fromConj x)
    (by ext; simp [mul_assoc]) (by ext; simp [mul_assoc])

omit [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] in
lemma Subalgebra.finrank_conj (B : Subalgebra F A) (x : Aˣ) :
    Module.finrank F (B.conj x) = Module.finrank F B := by
  rw [LinearEquiv.finrank_eq (Subalgebra.conjEquiv B x).toLinearEquiv]

omit [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] in
lemma Subalgebra.conj_simple_iff {B : Subalgebra F A} {x : Aˣ} :
    IsSimpleOrder (TwoSidedIdeal <| B.conj x) ↔
    IsSimpleOrder (TwoSidedIdeal B) := by
  let e : TwoSidedIdeal (B.conj x) ≃o TwoSidedIdeal B :=
  { toFun J := J.comap (B.toConj x)
    invFun J := .mk'
      (Set.image (B.toConj x) J)
      (⟨0, TwoSidedIdeal.zero_mem _, by simp⟩)
      (by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        rw [← map_add]
        refine ⟨a + b, J.add_mem ha hb, rfl⟩)
      (by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_neg]
        refine ⟨-a, J.neg_mem ha, rfl⟩)
      (by
        rintro ⟨_, ⟨a, ha, rfl⟩⟩ _ ⟨b, hb, rfl⟩

        refine ⟨⟨a, ha⟩ * b, J.mul_mem_left _ _ hb, ?_⟩
        ext
        simp only [toConj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          MulMemClass.coe_mul, mul_assoc]
        rw [← mul_assoc x⁻¹.1, Units.inv_mul, one_mul])
      (by
        rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩ ⟨c, hc1, hc2⟩
        simp only [toConj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          Subtype.mk.injEq, Units.mul_left_inj, Units.mul_right_inj] at hc2
        refine ⟨⟨a, ha⟩ * ⟨b, hb⟩, J.mul_mem_right _ _ <| by
          simp_rw [← hc2]; exact hc1, ?_⟩
        ext
        simp only [toConj, MulMemClass.mk_mul_mk, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk, mul_assoc]
        rw [← mul_assoc x⁻¹.1, Units.inv_mul, one_mul])
    left_inv := by
      intro J
      ext ⟨_, ⟨a, ha, rfl⟩⟩
      simp only [toConj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      generalize_proofs
      rw [TwoSidedIdeal.mem_mk']
      try assumption
      simp only [Set.mem_image, SetLike.mem_coe, TwoSidedIdeal.mem_comap, AlgHom.coe_mk,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq, Units.mul_left_inj,
        Units.mul_right_inj, Subtype.exists, exists_and_right, exists_eq_right, ha,
        exists_true_left]
    right_inv := by
      intro J
      ext ⟨a, ha⟩
      simp only [TwoSidedIdeal.mem_comap]
      generalize_proofs
      rw [TwoSidedIdeal.mem_mk']
      try assumption
      simp only [toConj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Set.mem_image, SetLike.mem_coe, Subtype.mk.injEq, Units.mul_left_inj, Units.mul_right_inj,
        Subtype.exists, exists_and_right, exists_eq_right, ha, exists_true_left]
    map_rel_iff' := by
      intro J K
      simp only [Equiv.coe_fn_mk]
      constructor
      · rintro H ⟨_, ⟨a, ha1, rfl⟩⟩ ha2
        have := @H ⟨a, ha1⟩ (by
          simp only [toConj, TwoSidedIdeal.mem_comap, AlgHom.coe_mk, RingHom.coe_mk,
            MonoidHom.coe_mk, OneHom.coe_mk, ha2])
        simp only [toConj, TwoSidedIdeal.mem_comap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk] at this
        exact this
      · intro H ⟨a, ha1⟩ ha2
        simp only [toConj, TwoSidedIdeal.mem_comap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk] at ha2
        simp only [toConj, TwoSidedIdeal.mem_comap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk]
        exact H ha2 }
  rw [OrderIso.isSimpleOrder_iff e]

omit [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] in
lemma Subalgebra.conj_centralizer (B : Subalgebra F A) {x : Aˣ} :
    Subalgebra.centralizer F (B.conj x : Set A) =
    (Subalgebra.centralizer F B).conj x := by
  ext a
  simp only [coe_conj, mem_centralizer_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    mem_conj, SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨x⁻¹ * a * x, ?_, by simp [mul_assoc]⟩
    intro b hb
    have := h (x * b * x⁻¹) b hb rfl
    apply_fun (x⁻¹.1 * ·) at this
    apply_fun (· * x.1) at this
    simp only [← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right] at this ⊢
    exact this
  · rintro ⟨b, hb, rfl⟩
    rintro _ a ha rfl
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_right_inj]
    simp only [← mul_assoc, Units.mul_left_inj]
    apply hb
    exact ha

omit [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] in
lemma Subalgebra.conj_centralizer' (B : Subalgebra F A) {x : Aˣ} :
    Subalgebra.centralizer F (B.conj x).carrier =
    (Subalgebra.centralizer F B).conj x :=
  Subalgebra.conj_centralizer _

namespace centralizer_isSimple.aux

open FiniteDimensional

instance :
    Algebra.IsCentral F (Matrix (Fin (Module.finrank F B)) (Fin (Module.finrank F B)) F) := by
  haveI : NeZero (Module.finrank F B) := by
    have : 0 < Module.finrank F B := Module.finrank_pos
    constructor
    omega
  infer_instance

instance : Algebra.IsCentral F (Module.End F B) :=
  algEquivMatrix (Module.finBasis F B) |>.symm.isCentral

instance : IsSimpleRing (Module.End F B) := by
  haveI : NeZero (Module.finrank F B) := by
    have : 0 < Module.finrank F B := Module.finrank_pos
    constructor
    omega
  constructor
  rw [TwoSidedIdeal.orderIsoOfRingEquiv
    (algEquivMatrix (Module.finBasis F B) |>.toRingEquiv) |>.isSimpleOrder_iff]
  exact IsSimpleRing.simple

noncomputable def auxLeft (B : Subalgebra F A) (C : Type u) [Ring C] [Algebra F C] :
    B ⊗[F] C ≃ₐ[F] (Algebra.TensorProduct.map B.val (AlgHom.id F C)).range :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInjective _ <| by
      change Function.Injective <| LinearMap.rTensor _ _
      apply Module.Flat.rTensor_preserves_injective_linearMap
      exact Subtype.val_injective)
    (by
      ext
      erw [LinearEquiv.ofInjective_apply])
    (by
      intro x y
      ext
      erw [LinearEquiv.ofInjective_apply]
      change Algebra.TensorProduct.map _ _ _ = _
      rw [map_mul]
      rfl)

noncomputable def auxRight (B : Subalgebra F A) (C : Type u) [Ring C] [Algebra F C] :
    C ⊗[F] B ≃ₐ[F] (Algebra.TensorProduct.map (AlgHom.id F C) B.val).range :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInjective _ <| by
      change Function.Injective <| LinearMap.lTensor _ _
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact Subtype.val_injective)
    (by
      ext
      erw [LinearEquiv.ofInjective_apply])
    (by
      intro x y
      ext
      erw [LinearEquiv.ofInjective_apply]
      change Algebra.TensorProduct.map _ _ _ = _
      rw [map_mul]
      rfl)

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
instance : IsSimpleRing (A ⊗[F] Module.End.rightMul F B) := by
  constructor
  let eqv : (A ⊗[F] Module.End.rightMul F B) ≃ₐ[F] (Bᵐᵒᵖ  ⊗[F] A) :=
    AlgEquiv.trans (Algebra.TensorProduct.congr AlgEquiv.refl Module.End.rightMulEquiv)
      (Algebra.TensorProduct.comm F A Bᵐᵒᵖ)
  have := TwoSidedIdeal.orderIsoOfRingEquiv eqv.toRingEquiv
  rw [OrderIso.isSimpleOrder_iff this]
  haveI : IsSimpleRing Bᵐᵒᵖ := by
    constructor
    rw [← TwoSidedIdeal.opOrderIso.isSimpleOrder_iff]
    exact IsSimpleRing.simple
  apply (IsCentralSimple.TensorProduct.simple F _ _).simple

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
lemma step1 {ι : Type*} (ℬ : Basis ι F <| Module.End F B) :
    ∃ (x : (A ⊗[F] Module.End F B)ˣ),
    Nonempty <|
      ((Subalgebra.centralizer F (B : Set A)) ⊗[F] (Module.End F B)) ≃ₐ[F]
      Subalgebra.conj
        (Algebra.TensorProduct.map (AlgHom.id F A)
          (Module.End.rightMul F B).val).range x:= by
  haveI : Algebra.IsCentral F (A ⊗[F] Module.End F B) := inferInstance

  let f : B →ₐ[F] A ⊗[F] Module.End F B :=
    { toFun b := b.1 ⊗ₜ LinearMap.id
      map_one' := by rfl
      map_mul' := by
        intro b₁ b₂
        simp only [MulMemClass.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, Module.End.mul_eq_comp,
          LinearMap.comp_id]
      map_zero' := by simp only [ZeroMemClass.coe_zero, zero_tmul]
      map_add' := by
        intro a b
        simp only [AddMemClass.coe_add, add_tmul]
      commutes' := by
        intro a
        simp only [SubalgebraClass.coe_algebraMap, Algebra.TensorProduct.algebraMap_apply]
        rfl }
  let g : B →ₐ[F] A ⊗[F] Module.End F B :=
  { toFun :=fun b => 1 ⊗ₜ LinearMap.mulLeft F b
    map_one' := by
      simp only [LinearMap.mulLeft_one]
      rfl
    map_mul' x y := by
      simp only [LinearMap.mulLeft_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        Module.End.mul_eq_comp]
    map_zero' := by
      simp only [LinearMap.mulLeft_zero_eq_zero, tmul_zero]
    map_add' b₁ b₂ := by
      rw [← tmul_add]
      congr
      ext
      simp only [LinearMap.mulLeft_apply, add_mul, AddMemClass.coe_add, MulMemClass.coe_mul,
        LinearMap.add_apply]
    commutes' := by
      intro a
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [Algebra.TensorProduct.one_def, smul_tmul', smul_tmul]
      congr
      ext
      simp only [LinearMap.mulLeft_apply, Algebra.smul_mul_assoc, one_mul, SetLike.val_smul,
        LinearMap.smul_apply, Module.End.one_apply] }

  obtain ⟨x, hx⟩ := SkolemNoether' F (A ⊗[F] Module.End F B) B g f
  use x
  have eq1 :
      ((Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := Module.End F B)).comp
        B.val).range =
      Subalgebra.conj
        (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := Module.End F B) |>.comp
          (Module.End.leftMul F B).val).range x := by
    ext z
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Subalgebra.coe_val,
        Function.comp_apply, Algebra.TensorProduct.includeLeft_apply]
      specialize hx ⟨z, hz⟩
      rw [Subalgebra.mem_conj]
      refine ⟨g ⟨z, hz⟩, ?_⟩
      simp only [AlgHom.mem_range, AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, Subtype.exists, exists_prop', nonempty_prop]
      rw [← hx]
      simp only [AlgHom.coe_mk, RingHom.coe_mk, f]
      refine ⟨⟨LinearMap.mulLeft F ⟨z, hz⟩, Set.mem_range_self _, rfl⟩, rfl⟩
    · rw [Subalgebra.mem_conj]
      simp only [AlgHom.mem_range, AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, Subtype.exists, exists_prop', nonempty_prop,
        exists_exists_and_eq_and, Algebra.TensorProduct.includeLeft_apply, forall_exists_index,
        and_imp]
      rintro _ ⟨⟨z, hz⟩, _, rfl⟩ rfl
      refine ⟨z, hz, ?_⟩
      exact hx ⟨z, hz⟩

  have eq2 := congr(Subalgebra.centralizer F $(eq1).carrier)
  erw [centralizer_inclusionLeft (𝒜' := ℬ)] at eq2
  have temp := Subalgebra.conj_centralizer' (F := F) (A := A ⊗[F] Module.End F B)
    (B := (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := Module.End F B) |>.comp
          (Module.End.leftMul F B).val).range) (x := x)
  rw [temp] at eq2; clear temp
  rw [centralizer_inclusionRight (𝒜 := Module.finBasis F A)] at eq2
  rw [centralizer_mulLeft] at eq2

  rw [← eq2]
  refine ⟨?_⟩
  apply auxLeft

lemma finrank_mop (B : Type*) [Ring B] [Algebra F B] : Module.finrank F Bᵐᵒᵖ =
    Module.finrank F B := by
  refine LinearEquiv.finrank_eq
    { toFun := MulOpposite.unop
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      invFun := MulOpposite.op
      left_inv := by intros x; simp
      right_inv := by intros x; simp }

end centralizer_isSimple.aux

open centralizer_isSimple.aux in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
lemma centralizer_isSimple {ι : Type*} (ℬ : Basis ι F <| Module.End F B) :
    IsSimpleRing (Subalgebra.centralizer F (B : Set A)) := by
  letI (X : Subalgebra F (A ⊗[F] Module.End F B)) : Ring X :=
      Subalgebra.toRing (R := F) (A := A ⊗[F] Module.End F B) X

  obtain ⟨x, ⟨eqv⟩⟩ := step1 B ℬ

  have : IsSimpleRing (Subalgebra.centralizer F (B : Set A) ⊗[F] Module.End F B) := by
    have := TwoSidedIdeal.orderIsoOfRingEquiv eqv
    constructor
    rw [OrderIso.isSimpleOrder_iff this]
    rw [Subalgebra.conj_simple_iff]

    let eqv'' := auxRight (Module.End.rightMul F B) A
    have := TwoSidedIdeal.orderIsoOfRingEquiv eqv''.toRingEquiv
    rw [← OrderIso.isSimpleOrder_iff this]
    infer_instance
  exact IsSimpleRing.left_of_tensor (K := F)
    (B := Subalgebra.centralizer F (B : Set A))
    (C := Module.End F B)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
open centralizer_isSimple.aux in
variable (F) in
lemma dim_centralizer  :
    Module.finrank F (Subalgebra.centralizer F (B : Set A)) *
    Module.finrank F B = Module.finrank F A := by

  letI (X : Subalgebra F (A ⊗[F] Module.End F B)) : Ring X :=
      Subalgebra.toRing (R := F) (A := A ⊗[F] Module.End F B) X

  haveI : Module.Free F (Module.End.rightMul F B) := Module.Free.of_divisionRing F
    ↥(Module.End.rightMul F ↥B)

  obtain ⟨x, ⟨eqv⟩⟩ := step1 B (Module.finBasis _ _)
  let leqv := eqv.toLinearEquiv
  have : Module.finrank F (Subalgebra.centralizer F (B : Set A) ⊗[F] Module.End F B) =
    Module.finrank F _ := LinearEquiv.finrank_eq leqv
  simp only [Module.finrank_tensorProduct] at this
  rw [Module.finrank_linearMap, Subalgebra.finrank_conj] at this
  have eq' := auxRight (Module.End.rightMul F B) A |>.toLinearEquiv.finrank_eq
  rw [← eq'] at this
  have eq' := Module.finrank_tensorProduct (R := F) (S := F) (M := A) (M' := Module.End.rightMul F B)
  rw [eq'] at this
  have eq' : Module.finrank F (Module.End.rightMul F B) = Module.finrank F Bᵐᵒᵖ :=
    Module.End.rightMulEquiv (F := F) (B := B) |>.toLinearEquiv.finrank_eq
  rw [eq'] at this
  rw [show Module.finrank F Bᵐᵒᵖ = Module.finrank F B by rw [finrank_mop], ← mul_assoc] at this
  rw [Nat.mul_left_inj] at this
  · exact this

  rw [← pos_iff_ne_zero]
  exact Module.finrank_pos

lemma double_centralizer :
    Subalgebra.centralizer F (Subalgebra.centralizer F (B : Set A) : Set A) = B := by
  symm
  apply Subalgebra.eq_of_le_of_finrank_eq
  · intro x hx y hy
    exact hy x hx |>.symm
  · haveI := centralizer_isSimple B (Module.finBasis F _)
    have eq1 := dim_centralizer F B
    have eq2 := dim_centralizer F (A := A) (Subalgebra.centralizer F B)
    have eq3 := eq1.trans eq2.symm
    rw [mul_comm] at eq3
    have eq4 := Nat.mul_left_inj (by
      suffices 0 < Module.finrank F (Subalgebra.centralizer F (B : Set A)) by omega
      apply Module.finrank_pos) |>.1 eq3

    exact eq4

/-
074U
-/
set_option maxHeartbeats 400000 in
noncomputable def writeAsTensorProduct
    [Algebra.IsCentral F B] [IsSimpleRing B] :
    A ≃ₐ[F] B ⊗[F] Subalgebra.centralizer F (B : Set A) :=
  haveI s1 : IsSimpleRing (Subalgebra.centralizer F (B : Set A)) :=
    centralizer_isSimple B (Module.Free.chooseBasis _ _)
  haveI s2 : IsSimpleRing (B ⊗[F] Subalgebra.centralizer F (B : Set A)) :=
    ⟨TwoSidedIdeal.orderIsoOfRingEquiv
      (Algebra.TensorProduct.comm F B (Subalgebra.centralizer F (B : Set A))).toRingEquiv
      |>.isSimpleOrder⟩

  AlgEquiv.symm <| AlgEquiv.ofBijective (Algebra.TensorProduct.lift B.val (Subalgebra.val _)
    fun x y => show _ = _ by simpa using y.2 x x.2) <|
      bijective_of_dim_eq_of_isCentralSimple F (B ⊗[F] Subalgebra.centralizer F (B : Set A)) A
        _ <| by
        rw [Module.finrank_tensorProduct]
        rw [← dim_centralizer (B := B), mul_comm]
