import BrauerGroup.SkolemNoether

universe u v

variable {F A : Type*}
variable [Field F] [Ring A] [Algebra F A]
variable [FiniteDimensional F A] [IsCentralSimple F A]
variable (B : Subalgebra F A) [IsSimpleOrder (RingCon B)]

open TensorProduct

section lemma1

variable {F A A' : Type u}
variable [Field F] [Ring A] [Algebra F A] [Ring A'] [Algebra F A']
variable (B : Subalgebra F A) (B' : Subalgebra F A')

#check Subalgebra.mem_centralizer_iff
lemma centralizer_tensor_centralizer
    {ι ι' : Type*} (𝒜 : Basis ι F A) (𝒜' : Basis ι' F A') :
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
      sorry

    have eq1 : Subalgebra.centralizer F (A := A ⊗[F] A')
          (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := A) (B := A') |>.comp
            B.val).range =
          (Algebra.TensorProduct.map (Subalgebra.centralizer F B).val (AlgHom.id F A')).range := by
      refine le_antisymm ?_ ?_
      · sorry

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

    have eq2 : Subalgebra.centralizer F (A := A ⊗[F] A')
          (Algebra.TensorProduct.includeRight (R := F) (A := A) (B := A') |>.comp
            B'.val).range =
          (Algebra.TensorProduct.map (AlgHom.id F A) (Subalgebra.centralizer F B').val).range := by
      refine le_antisymm ?_ ?_
      · sorry
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

variable {F B : Type*}
variable [Field F] [Ring B] [Algebra F B] [IsSimpleOrder (RingCon B)]

lemma centralizer_mulLeft :
    (Subalgebra.centralizer F (Set.range <| LinearMap.mulLeft F : Set  <| Module.End F B) : Set _) =
    Set.range (LinearMap.mulRight F (A := B)) := sorry

end lemma2

lemma centralizer_isSimple : IsSimpleOrder <| RingCon (Subalgebra.centralizer F (B : Set A)) := sorry
