import BrauerGroup.SkolemNoether
import BrauerGroup.Lemmas

import BrauerGroup.faithfullyflat

universe u v

variable {F A : Type u}
variable [Field F] [Ring A] [Algebra F A]
variable [FiniteDimensional F A] [IsCentralSimple F A]
variable (B : Subalgebra F A) [IsSimpleOrder (TwoSidedIdeal B)]

open TensorProduct

section lemma1

variable {F A A' : Type u}
variable [Field F] [Ring A] [Algebra F A] [Ring A'] [Algebra F A']
variable (B : Subalgebra F A) (B' : Subalgebra F A')
variable {ι ι' : Type*} (𝒜 : Basis ι F A) (𝒜' : Basis ι' F A')

include 𝒜' in
lemma centralizer_inclusionLeft :
    Subalgebra.centralizer F (A := A ⊗[F] A')
      (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := A') |>.comp
        B.val).range =
      (Algebra.TensorProduct.map (Subalgebra.centralizer F B).val (AlgHom.id F A')).range := by
  refine le_antisymm ?_ ?_
  · rintro x hx
    obtain ⟨s, a, rfl⟩ := IsCentralSimple.TensorProduct.eq_repr_basis_right F A A' 𝒜' x
    refine Subalgebra.sum_mem _ fun i hi => ?_
    simp only [AlgHom.mem_range]
    refine ⟨⟨a i, fun b hb => ?_⟩ ⊗ₜ 𝒜' i, by simp⟩
    have eq := hx (b ⊗ₜ 1) (by simpa using ⟨b, hb, rfl⟩)
    simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.sum_mul,
      mul_one] at eq
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at eq
    simp_rw [← sub_tmul] at eq
    have := IsCentralSimple.TensorProduct.sum_tmul_basis_right_eq_zero (h := eq)
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

include 𝒜 in
lemma centralizer_inclusionRight :
    Subalgebra.centralizer F (A := A ⊗[F] A')
      (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := A') |>.comp
        B'.val).range =
      (Algebra.TensorProduct.map (AlgHom.id F A) (Subalgebra.centralizer F B').val).range := by
  refine le_antisymm ?_ ?_
  · rintro x hx
    obtain ⟨s, a, rfl⟩ := IsCentralSimple.TensorProduct.eq_repr_basis_left F A A' 𝒜 x
    refine Subalgebra.sum_mem _ fun i hi => ?_
    simp only [AlgHom.mem_range]
    refine ⟨𝒜 i ⊗ₜ ⟨a i, fun b hb => ?_⟩, by simp⟩
    have eq := hx (1 ⊗ₜ b) (by simpa using ⟨b, hb, rfl⟩)
    simp only [Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
      mul_one] at eq
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at eq
    simp_rw [← tmul_sub] at eq
    have := IsCentralSimple.TensorProduct.sum_tmul_basis_left_eq_zero (h := eq)
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
  rw [← IsCentralSimple.Subalgebra.centralizer_sup]
  intro y hy
  apply hx
  rw [Algebra.TensorProduct.map_range]
  exact hy

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
variable [Field F] [Ring B] [Algebra F B] [IsCentralSimple F B] [FiniteDimensional F B]

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
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    rw [show eqv (y ⊗ₜ[F] 1) = LinearMap.mulLeft F y by
      ext x
      simp only [LinearMap.mulLeft_apply]
      simp only [tensor_self_op.equivEnd, tensor_self_op.toEnd, AlgEquiv.coe_ofBijective,
        Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, MulOpposite.unop_one, mul_one, LinearMap.mul_apply, LinearMap.coe_mk,
        AddHom.coe_mk, eqv] ]
    ext b
    simp only [LinearMap.mul_apply, LinearMap.mulLeft_apply]
    exact congr($(hx (LinearMap.mulLeft F y) (by simp)) b)

  have eq : Subalgebra.centralizer F
    ((Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := B) (B := Bᵐᵒᵖ)).range :
      Set (B ⊗[F] Bᵐᵒᵖ)) =
    (Algebra.TensorProduct.includeRight (R := F) (A := B) (B := Bᵐᵒᵖ)).range := by
    refine le_antisymm ?_ ?_
    · set ℬ := FiniteDimensional.finBasis F Bᵐᵒᵖ
      intro z hz
      obtain ⟨s, b, rfl⟩ := IsCentralSimple.TensorProduct.eq_repr_basis_right F B Bᵐᵒᵖ ℬ z
      refine Subalgebra.sum_mem _ fun i hi => ?_
      have : (b i) ∈ Subalgebra.center F B := by
        rw [Subalgebra.mem_center_iff]
        intro b'
        have eq := hz (b' ⊗ₜ 1) (by simp)
        simp only [Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
          mul_one] at eq
        rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at eq
        simp_rw [← TensorProduct.sub_tmul] at eq
        replace eq := IsCentralSimple.TensorProduct.sum_tmul_basis_right_eq_zero (h := eq)
        specialize eq i hi
        rw [sub_eq_zero] at eq
        exact eq
      rw [IsCentralSimple.center_eq, Algebra.mem_bot] at this
      obtain ⟨x, hx⟩ := this
      rw [← hx, Algebra.algebraMap_eq_smul_one, smul_tmul]
      simp only [AlgHom.mem_range, Algebra.TensorProduct.includeRight_apply]
      exact ⟨_, rfl⟩
    · set ℬ := FiniteDimensional.finBasis F B
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
    MonoidHom.coe_mk, OneHom.coe_mk, one_mul, LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk,
    eqv]

end central_simple_case

variable {F B : Type u}
variable [Field F] [Ring B] [Algebra F B] [IsSimpleOrder <| TwoSidedIdeal B] [FiniteDimensional F B]

variable (F B) in
private def centralizerMulLeftCopy :
    (Subalgebra.centralizer F (Set.range (LinearMap.mulLeft F) : Set <| Module.End F B)) →ₗ[F]
    (B →ₗ[Subalgebra.center F B] B) where
  toFun a :=
  { toFun := a
    map_add' := a.1.map_add
    map_smul' := by
      intro c x
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
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
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
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
    simp [mul_add, add_mul]
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
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    ext z
    simp [mul_add, add_mul]
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

lemma centralizer_mulLeft :
    Subalgebra.centralizer F (Module.End.leftMul F B : Set <| Module.End F B) =
    (Module.End.rightMul F B : Set (Module.End F B)) := by
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
        simp only [LinearMap.mul_apply, LinearMap.coe_mk, LinearMap.coe_toAddHom,
          LinearMap.mulLeft_apply, a']
        exact congr($(ha (LinearMap.mulLeft F y) (by simp)) b))
      refine ⟨b, ?_⟩
      ext c
      exact congr($hb c)

    exact @centralizer_mulLeft_le_of_isCentralSimple (Subalgebra.center F B) B _ _ _
      { is_central := by
          intro x hx
          rw [Algebra.mem_bot]
          exact ⟨⟨x, hx⟩, rfl⟩
        is_simple := by assumption } _
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    ext z
    simp only [LinearMap.mul_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]

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

omit [FiniteDimensional F A] [IsCentralSimple F A] in
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

omit [FiniteDimensional F A] [IsCentralSimple F A] in
lemma Subalgebra.conj_simple_iff {B : Subalgebra F A} {x : Aˣ} :
    IsSimpleOrder (TwoSidedIdeal <| B.conj x) ↔
    IsSimpleOrder (TwoSidedIdeal B) := by
  let e : TwoSidedIdeal (B.conj x) ≃o TwoSidedIdeal B :=
  { toFun := fun J => J.comap (B.toConj x)
    invFun := fun J => .mk'
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
          OneHom.coe_mk, MulMemClass.coe_mul, mul_assoc]
        rw [← mul_assoc x⁻¹.1, Units.inv_mul, one_mul])
    left_inv := by
      intro J
      ext ⟨_, ⟨a, ha, rfl⟩⟩
      simp only [toConj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      generalize_proofs
      rw [TwoSidedIdeal.mem_mk'] <;> try assumption
      simp only [Set.mem_image, SetLike.mem_coe, TwoSidedIdeal.mem_comap, AlgHom.coe_mk,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq, Units.mul_left_inj,
        Units.mul_right_inj, Subtype.exists, exists_and_right, exists_eq_right, ha,
        exists_true_left]
    right_inv := by
      intro J
      ext ⟨a, ha⟩
      simp only [TwoSidedIdeal.mem_comap]
      generalize_proofs
      rw [TwoSidedIdeal.mem_mk'] <;> try assumption
      simp only [toConj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Set.mem_image, SetLike.mem_coe, Subtype.mk.injEq, Units.mul_left_inj, Units.mul_right_inj,
        Subtype.exists, exists_and_right, exists_eq_right, ha, exists_true_left]
    map_rel_iff' := by
      intro J K
      simp only [Equiv.coe_fn_mk]
      constructor
      · rintro H ⟨_, ⟨a, ha1, rfl⟩⟩ ha2
        have := @H ⟨a, ha1⟩ (by simpa using ha2)
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

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
lemma centralizer_isSimple {ι : Type*} (ℬ : Basis ι F <| Module.End F B) :
    IsSimpleOrder <| TwoSidedIdeal (Subalgebra.centralizer F (B : Set A)) := by
  haveI : IsSimpleOrder <| TwoSidedIdeal A := (inferInstanceAs <| IsCentralSimple F A).2
  haveI : IsCentralSimple F (A ⊗[F] Module.End F B) := sorry

  let f : B →ₐ[F] A ⊗[F] Module.End F B :=
    { toFun := fun b => b.1 ⊗ₜ LinearMap.id
      map_one' := by rfl
      map_mul' := by
        intro b₁ b₂
        simp only [MulMemClass.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul_eq_comp,
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
    map_mul' := by
      intro x y
      simp only [LinearMap.mulLeft_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        LinearMap.mul_eq_comp]
    map_zero' := by
      simp only [LinearMap.mulLeft_zero_eq_zero, tmul_zero]
    map_add' := by
      intro b₁ b₂
      simp only
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
        LinearMap.smul_apply, LinearMap.one_apply] }

  obtain ⟨x, hx⟩ := SkolemNoether' F (A ⊗[F] Module.End F B) B g f

  letI (X : Subalgebra F (A ⊗[F] Module.End F B)) : Ring X :=
      Subalgebra.toRing (R := F) (A := A ⊗[F] Module.End F B) X

  let eqv :
    (Subalgebra.centralizer F (B : Set A) ⊗[F] Module.End F B) ≃ₐ[F]
    Subalgebra.conj (Algebra.TensorProduct.map (AlgHom.id F A)
      (Module.End.rightMul F B).val).range x := sorry


  let eqv' :
    (Subalgebra.centralizer F (B : Set A) ⊗[F] Module.End F B) ≃+*
    Subalgebra.conj (Algebra.TensorProduct.map (AlgHom.id F A)
      (Module.End.rightMul F B).val).range x := eqv.toRingEquiv


  have : IsSimpleOrder <|
      TwoSidedIdeal (Subalgebra.centralizer F (B : Set A) ⊗[F] Module.End F B) := by
    have := TwoSidedIdeal.orderIsoOfRingEquiv eqv
    rw [OrderIso.isSimpleOrder_iff this]
    rw [Subalgebra.conj_simple_iff]
    sorry
  exact IsSimpleRing.left_of_tensor (K := F)
    (B := Subalgebra.centralizer F (B : Set A))
    (C := Module.End F B)

variable (F) in
lemma dim_centralizer  :
    FiniteDimensional.finrank F (Subalgebra.centralizer F (B : Set A)) *
    FiniteDimensional.finrank F B = FiniteDimensional.finrank F A := by
  sorry

lemma double_centralizer :
    Subalgebra.centralizer F (Subalgebra.centralizer F (B : Set A) : Set A) = B := by
  symm
  apply Subalgebra.eq_of_le_of_finrank_eq
  · intro x hx y hy
    exact hy x hx |>.symm
  · haveI := centralizer_isSimple B (FiniteDimensional.finBasis F _)
    have eq1 := dim_centralizer F B
    have eq2 := dim_centralizer F (A := A) (Subalgebra.centralizer F B)
    have eq3 := eq1.trans eq2.symm
    rw [mul_comm] at eq3
    have eq4 := Nat.mul_left_inj (by
      suffices 0 < FiniteDimensional.finrank F (Subalgebra.centralizer F (B : Set A)) by omega
      apply FiniteDimensional.finrank_pos) |>.1 eq3

    exact eq4
