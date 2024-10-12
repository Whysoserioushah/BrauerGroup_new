import BrauerGroup.DoubleCentralizer
import BrauerGroup.Lemmas

import Mathlib.RingTheory.Adjoin.Basic

universe u

suppress_compilation

open BigOperators TensorProduct MulOpposite

section def_and_lemmas

@[ext]
structure SubField (K A : Type u) [Field K] [Semiring A] [Algebra K A] extends Subalgebra K A where
  mul_comm : ∀(x y : A), x ∈ carrier → y ∈ carrier → x * y = y * x
  inverse : ∀(x : A), x ∈ carrier → x ≠ 0 → ∃(y : A), (y ∈ carrier ∧ x * y = 1)

instance (K A : Type u) [Field K] [Semiring A] [Algebra K A] : LE (SubField K A) where
  le := fun L1 L2 ↦ L1.1 ≤ L2.1

def IsMaximalSubfield (K A : Type u) [Field K] [Semiring A] [Algebra K A] (L : SubField K A) : Prop
  := ∀ (B : SubField K A), L ≤ B → B = L

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] [Nontrivial A]: Nonempty (SubField K A) :=
  have e : K ≃ₐ[K] (Algebra.ofId K A).range := AlgEquiv.ofBijective
    (Algebra.ofId K A).rangeRestrict ⟨by
      suffices Function.Injective (Algebra.ofId K A) from
        (AlgHom.injective_codRestrict (Algebra.ofId K A) (Algebra.ofId K A).range
          (AlgHom.mem_range_self (Algebra.ofId K A))).2 this
      exact NoZeroSMulDivisors.algebraMap_injective K A,
      AlgHom.rangeRestrict_surjective (Algebra.ofId K A)⟩
  ⟨⟨⊥, fun x y hx hy ↦ by
    change x ∈ (Algebra.ofId K A).range at hx
    change y ∈ (Algebra.ofId K A).range at hy
    suffices (⟨x, hx⟩ : (Algebra.ofId K A).range) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ from
      Subtype.ext_iff.1 this
    rw [← e.apply_symm_apply ⟨x, hx⟩, ← e.apply_symm_apply ⟨y, hy⟩, ← _root_.map_mul, mul_comm,
      _root_.map_mul], fun x hx hx0 ↦ ⟨e ((e.symm ⟨x, hx⟩)⁻¹), by
        change _ ∈ (Algebra.ofId K A).range; simp only [SetLike.coe_mem], by
    suffices (⟨x, hx⟩ : (Algebra.ofId K A).range) * ⟨e ((e.symm ⟨x, hx⟩)⁻¹), _⟩ = 1 from
      Subtype.ext_iff.1 this
    nth_rw 1 [← e.apply_symm_apply ⟨x, hx⟩, ← _root_.map_mul, mul_inv_cancel₀ _, map_one]
    simp only [ne_eq, AddEquivClass.map_eq_zero_iff]
    exact Subtype.coe_ne_coe.1 hx0 ⟩⟩⟩

-- instance (K A : Type u) [Field K] [Ring A] [Algebra K A] (L : SubField K A) : Nontrivial L.1 := sorry

open scoped Classical in
instance (K A : Type u) [Field K] [Ring A] [Nontrivial A] [Algebra K A] (L : SubField K A) : Field L.1 := {
  __ := L.1
  mul_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext_iff.2 $ L.2 a b ha hb
  inv := fun ⟨x, hx⟩ ↦ if h0 : x = 0 then 0 else ⟨L.3 x hx h0|>.choose,
    L.3 x hx h0|>.choose_spec.1⟩
  exists_pair_ne := ⟨⟨0, Subalgebra.zero_mem L.1⟩, ⟨1, Subalgebra.one_mem L.1⟩, by
    refine Subtype.coe_ne_coe.1 $ by simp only [ne_eq, zero_ne_one, not_false_eq_true]⟩
  mul_inv_cancel := fun ⟨a, ha⟩ ha0 ↦ by
    unfold Inv.inv
    simp only [ZeroMemClass.coe_eq_zero, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SetLike.mem_coe, ha0, ↓reduceDIte, MulMemClass.mk_mul_mk]
    suffices a * (L.3 a ha (Subtype.coe_ne_coe.2 ha0)).choose = (1 : A) from
      Subtype.ext_iff.2 (by simp only [this, OneMemClass.coe_one])
    exact L.3 a ha (Subtype.coe_ne_coe.2 ha0)|>.choose_spec.2
  inv_zero := by
    simp only [ZeroMemClass.coe_eq_zero, Subsemiring.coe_carrier_toSubmonoid,
      Subalgebra.coe_toSubsemiring, SetLike.mem_coe, ↓reduceDIte]
  nnqsmul := _
  qsmul := _
}

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] : PartialOrder (SubField K A) where
  le L1 L2:= L1 ≤ L2
  le_refl L := by change L.1 ≤ L.1 ; exact fun _ a ↦ a
  le_trans L1 L2 L3 hL12 hL23 := by
    change L1.1 ≤ L3.1 ; exact fun _ a ↦ hL23 (hL12 a)
  le_antisymm L1 L2 hL12 hL21 := by
    suffices L1.1 = L2.1 by
      ext a; exact ⟨fun a_1 ↦ hL12 (hL21 (hL12 a_1)), fun a_1 ↦ hL21 (hL12 (hL21 a_1))⟩
    exact (LE.le.le_iff_eq hL12).1 hL21|>.symm

instance (K A : Type u) [Field K] [Ring A] [Algebra K A] : SetLike (SubField K A) A where
  coe L := L.1
  coe_injective' := fun L1 L2 hL12 ↦ by
    simp only [SetLike.coe_set_eq] at hL12
    have le : L1 ≤ L2 := by
      change L1.1 ≤ L2.1
      exact le_of_eq_of_le hL12 fun _ a ↦ a
    have ge : L2 ≤ L1 := by
      change L2.1 ≤ L1.1
      exact le_of_eq_of_le hL12.symm fun _ a ↦ a
    exact (LE.le.le_iff_eq le).1 ge|>.symm

instance comm_of_centralizer (K A : Type u) [Field K] [Ring A] [Algebra K A] (L : Subalgebra K A)
  (hL : ∀(x y : L), x * y = y * x) :
    L ≤ Subalgebra.centralizer K (A := A) L := by
  intro l hl
  simp only [Subalgebra.mem_centralizer_iff, SetLike.mem_coe]
  exact fun l' hl' => by
    have := hL ⟨l, hl⟩ ⟨l', hl'⟩|>.symm
    have eqeq : (⟨l', hl'⟩ : L) * ⟨l, hl⟩ = ⟨l' * l, Subalgebra.mul_mem L hl' hl⟩ := by
      have eq : ((⟨l', hl'⟩ : L) * (⟨l, hl⟩ : L)).1 = l' * l := by
        calc
        _ = ((⟨l', hl'⟩ : L) : A) * ((⟨l, hl⟩ : L) : A) := by rfl
        _ = _ := by push_cast ; rfl
      rw [Subtype.ext_iff, eq]
    have eqeq' : (⟨l, hl⟩ : L) * ⟨l', hl'⟩ = ⟨l * l', Subalgebra.mul_mem L hl hl'⟩ := rfl
    rw [eqeq, eqeq'] at this
    exact Subtype.ext_iff.1 this

end def_and_lemmas

section cors_of_DC

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [IsCentralSimple K D]

example (A : SubField K D) (a : D) (ha : a ∉ A) : ∃ (B : SubField K D), a ∈ B ∧ A < B := sorry


theorem dim_max_subfield (k : SubField K D) (hk: IsMaximalSubfield K D k) :
    FiniteDimensional.finrank K D = FiniteDimensional.finrank K k.1 * FiniteDimensional.finrank K k.1 := by
  have dimdim := dim_centralizer K (A := D) k.1 |>.symm
  have := comm_of_centralizer K D k.1 $ fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ Subtype.ext_iff.2 $ k.2 x y hx hy
  have eq : k.1 = Subalgebra.centralizer K (A := D) k.1 := by
    by_contra! hneq
    have lt := LE.le.lt_iff_ne this|>.2 hneq
    have exist_ele : ∃ a ∈ Subalgebra.centralizer K (A := D) k.1, a ∉ k.1 :=
      Set.ssubset_iff_of_subset this|>.1 $ Set.lt_iff_ssubset.1 lt
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := exist_ele
    have ha : a ≠ 0 := by
      by_contra! haa
      have : a ∈ k.1 := by rw [haa]; exact Subalgebra.zero_mem _
      tauto

    letI : CommRing (Algebra.adjoin K (insert a k.1) : Subalgebra K D) :=
    { mul_comm := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
        refine Algebra.adjoin_induction₂ (ha := hx) (hb := hy) ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_
        · intro α hα β hβ
          simp only [Set.mem_insert_iff, SetLike.mem_coe] at hα hβ
          rcases hα with rfl|hα <;> rcases hβ with rfl|hβ
          · rfl
          · rw [Subalgebra.mem_centralizer_iff] at ha1
            refine ha1 _ hβ |>.symm
          · rw [Subalgebra.mem_centralizer_iff] at ha1
            apply ha1; exact hα
          · apply k.mul_comm _ _ hα hβ
        · intros; rw [Algebra.commutes]

        · intros; rw [Algebra.commutes]

        · intros; rw [Algebra.commutes]
        · intro _ _  _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro _ _  _ h1 h2
          simp only [add_mul, h1, h2, mul_add]
        · intro x y z h1 h2
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
        · intro x y z h1 h2
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc] }

    have : IsField (Algebra.adjoin K (insert a k.1) : Subalgebra K D) := by
      rw [ ← Algebra.IsIntegral.isField_iff_isField (R := K)]
      · exact Semifield.toIsField K
      · exact NoZeroSMulDivisors.algebraMap_injective K _

    let L : SubField K D := {
      __ := Algebra.adjoin K (insert a k.1)
      mul_comm := fun x y hx hy ↦ by
        have := this.2 ⟨x, hx⟩ ⟨y, hy⟩
        -- simp? at hx hy
        change (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ :
          (Algebra.adjoin K (insert a k.1) : Subalgebra K D)) = ⟨_, _⟩ at this
        simp only [Subtype.mk.injEq] at this ⊢ ; exact this
      inverse := fun x hx hx0 ↦ by
         have := this.3 (Subtype.coe_ne_coe.1 hx0 : (⟨x, hx⟩ :
          (Algebra.adjoin K (insert a k.1) : Subalgebra K D)) ≠ 0)
         use this.choose.1
         exact ⟨this.choose.2, by
          have eq := this.choose_spec
          change ⟨x * this.choose.1, _⟩ = (1 : Algebra.adjoin K (insert a k.1)) at eq
          exact Subtype.ext_iff.1 eq⟩
    }

    have : a ∈ L := sorry

    have hL : k < L := ne_iff_lt_iff_le.2 (by
      change k.1 ≤ Algebra.adjoin K (insert a k.1)
      nth_rw 1 [← Algebra.adjoin_eq k.1]
      refine Algebra.adjoin_mono ?_
      exact Set.subset_insert _ _ )|>.1 $ by
      symm
      exact ne_of_mem_of_not_mem' this ha2

    have := hk L (le_of_lt hL)
    have : k ≠ L := ne_of_lt hL
    tauto
  rw [← eq] at dimdim
  exact dimdim

lemma cor_two_1to2 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] (L : SubField K A) :
    Subalgebra.centralizer K L.1 = L.1 ↔ FiniteDimensional.finrank K A =
    FiniteDimensional.finrank K L.1 * FiniteDimensional.finrank K L.1 :=
  haveI := hA.2
  ⟨fun h ↦ by
  have := dim_centralizer K (A := A) L.1 ; rw [h] at this ; exact this.symm, fun h ↦ by
  have := dim_centralizer K (A := A) L.1 ; rw [h] at this
  simp only [mul_eq_mul_right_iff] at this
  cases' this with h1 h2
  · exact Subalgebra.eq_of_le_of_finrank_eq (comm_of_centralizer K A L.1 fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
      simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq, L.2 x y hx hy]) h1.symm|>.symm
  · have := FiniteDimensional.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]⟩

lemma cor_two_2to3 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] (L : SubField K A) :
    FiniteDimensional.finrank K A = FiniteDimensional.finrank K L.1 * FiniteDimensional.finrank K L.1 →
    (∀ (L' : Subalgebra K A) (hL : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' → L.1 = L') := fun hrank L' hL' hLL ↦ by
  haveI := hA.2
  have := dim_centralizer K (A := A) L.1 |>.symm
  rw [this, mul_eq_mul_right_iff] at hrank
  cases' hrank with h1 h2
  · have := Subalgebra.eq_of_le_of_finrank_eq (comm_of_centralizer K A L.1 fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
      simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq, L.2 x y hx hy]) h1.symm
    exact le_antisymm hLL fun x hx => this.symm ▸ Subalgebra.mem_centralizer_iff _ |>.2
      fun y hy => hL' _ hx _ (hLL hy) |>.symm

  · have := FiniteDimensional.finrank_pos (R := K) (M := L.1)
    simp_all only [mul_zero, lt_self_iff_false]

lemma cor_two_3to1 (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] [IsCentralSimple K A] (L : SubField K A) :
    (∀ (L' : Subalgebra K A)  (hL : ∀ x ∈ L', ∀ y ∈ L',  x * y = y * x), L.1 ≤ L' → L.1 = L') →
    Subalgebra.centralizer K L.1 = L.1 := by
  intro H
  refine le_antisymm ?_ ?_
  ·
    sorry
  · apply comm_of_centralizer
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    exact L.mul_comm _ _ hx hy

end cors_of_DC


-- variable (K A M: Type u) [Field K] [Ring A] [Algebra K A] [hA : IsCentralSimple K A]
--   [FiniteDimensional K A] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
--   [IsSimpleModule A M]

-- variable (K A: Type u) [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)

-- set_option linter.unusedVariables false in
-- def A_inst (K A: Type u) [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A) := A

-- instance: AddCommGroup $ A_inst K A B := inferInstanceAs $ AddCommGroup A

-- instance: Module K $ A_inst K A B := inferInstanceAs $ Module K A

-- instance: Ring $ A_inst K A B := inferInstanceAs $ Ring A

-- instance: Algebra K $ A_inst K A B := inferInstanceAs $ Algebra K A

-- instance : HMul A (A_inst K A B) A where
--   hMul := fun a a' ↦ by
--     unfold A_inst at a'
--     exact a * a'

-- instance : HMul (A_inst K A B) A A where
--   hMul := fun a a' ↦ by
--     unfold A_inst at a
--     exact a * a'

-- instance : Module A (A_inst K A B) := inferInstanceAs $ Module A A

-- instance : IsScalarTower K A (A_inst K A B) := inferInstanceAs $ IsScalarTower K A A

-- -- def smulAAddHom'  (K A: Type u) [Field K] [Ring A] [Algebra K A]
-- --     (B : Subalgebra K A): (A_inst K A B) → A →+ Bᵐᵒᵖ →+ A :=
-- --   fun a ↦ {
-- --     toFun := fun x ↦ {
-- --       toFun := fun b ↦ b.unop * a * x
-- --       map_zero' := by simp only [MulOpposite.unop_zero, ZeroMemClass.coe_zero, zero_mul]
-- --       map_add' := fun b1 b2 ↦ by
-- --         change (b1 + b2).unop * _ * x = _ * _ * _ + _ * _ * _
-- --         simp only [MulOpposite.unop_add, Subsemiring.coe_add, Subalgebra.coe_toSubsemiring, add_mul]
-- --     }
-- --     map_zero' := by
-- --       ext; simp only [zero_mul, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp,
-- --         AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_coe, MulOpposite.opAddEquiv_apply,
-- --         Function.comp_apply, AddMonoidHom.zero_comp, AddMonoidHom.zero_apply, mul_zero]
-- --     map_add' := fun _ _ ↦ by
-- --       ext; simp only [add_mul, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp,
-- --         AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_coe, MulOpposite.opAddEquiv_apply,
-- --         Function.comp_apply, MulOpposite.unop_op, AddMonoidHom.add_apply, mul_add]}

-- -- def smulAAddHom  (K A: Type u)
-- --     [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A):
-- --     (A_inst K A B) → A ⊗[K] Bᵐᵒᵖ →+ A_inst K A B := fun a ↦
-- --   TensorProduct.liftAddHom (smulAAddHom' K A B a) $ fun k a' bop ↦ by
-- --   unfold A_inst at a
-- --   simp only [smulAAddHom']
-- --   change _ * a *_ = (k • bop).unop  * _ * _
-- --   simp only [Algebra.smul_mul_assoc, MulOpposite.unop_smul, SetLike.val_smul, Algebra.mul_smul_comm]

-- -- def smulA (K A: Type u)
-- --     [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A):
-- --     (A_inst K A B) → A ⊗[K] Bᵐᵒᵖ →ₗ[K] A_inst K A B := fun a ↦ {
-- --   __ := smulAAddHom K A B a
-- --   map_smul' := fun k ab ↦ by
-- --     simp only [smulAAddHom, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
-- --     induction ab using TensorProduct.induction_on
-- --     · simp only [smul_zero, map_zero]
-- --     · rename_i a' b
-- --       obtain ⟨b, hb⟩ := b
-- --       simp only [smulAAddHom', liftAddHom_tmul, TensorProduct.smul_tmul',
-- --         SetLike.mk_smul_mk, liftAddHom_tmul]
-- --       change _ * a * _ = k • (_ * a * _)
-- --       simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
-- --     · rename_i x y hx hy
-- --       simp only [smul_add, map_add, hx, add_right_inj, hy]
-- --   }

-- -- set_option synthInstance.maxHeartbeats 40000 in
-- -- instance : ZeroHomClass (A ⊗[K] Bᵐᵒᵖ →ₗ[K] A_inst K A B) _ _ := inferInstance

-- -- lemma smulA_add (a b : A_inst K A B) (x : A ⊗[K] Bᵐᵒᵖ):
-- --     smulA K A B (a + b) x = smulA K A B a x + smulA K A B b x := by
-- --   induction x using TensorProduct.induction_on
-- --   · simp only [map_zero, add_zero]
-- --   · rename_i a' bop
-- --     simp only [smulA, smulAAddHom, smulAAddHom', mul_add, add_mul, ZeroHom.toFun_eq_coe,
-- --       AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, liftAddHom_tmul]
-- --     change bop.unop * _ * a' + bop.unop * _ * a' = _ * _ * _ + _ * _ * _
-- --     rfl
-- --   · rename_i x y hx hy
-- --     simp only [map_add]
-- --     rw [hx, hy]
-- --     abel

-- -- lemma smulA_mul_smul : ∀ (x y : A ⊗[K] Bᵐᵒᵖ) (b : A_inst K A B), smulA K A B b (x * y) =
-- --     smulA K A B (smulA K A B b y) x := fun x y a ↦ by
-- --   induction x using TensorProduct.induction_on
-- --   · simp only [zero_mul, map_zero, mul_zero]
-- --   · rename_i a' b
-- --     induction y using TensorProduct.induction_on
-- --     · dsimp only [smulA, smulAAddHom, smulAAddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
-- --          LinearMap.coe_mk, AddHom.coe_mk]
-- --       simp only [mul_zero, map_zero, liftAddHom_tmul, zero_mul]; rfl
-- --     · dsimp only [smulA, smulAAddHom, smulAAddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
-- --          LinearMap.coe_mk, AddHom.coe_mk]
-- --       rename_i a1 b1
-- --       obtain ⟨b1, hb1⟩ := b1; obtain ⟨b, hb⟩ := b
-- --       unfold A_inst at *
-- --       simp only [Algebra.TensorProduct.tmul_mul_tmul, Submonoid.mk_mul_mk, liftAddHom_tmul,
-- --         AddMonoidHom.coe_mk, ZeroHom.coe_mk]
-- --       rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
-- --     · rename_i x y hx hy
-- --       simp only [mul_add, map_add, hx, liftAddHom_tmul, hy, smulA_add]
-- --   · rename_i x y' hx hy
-- --     simp only [add_mul, map_add, hx, hy]

-- -- lemma smulA_zero : ∀ (x : A ⊗[K] (↥B)ᵐᵒᵖ), smulA K A B 0 x = 0 := fun x ↦ by
-- --   simp only [smulA, smulAAddHom, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
-- --       LinearMap.coe_mk, AddHom.coe_mk]
-- --   induction x using TensorProduct.induction_on
-- --   · simp only [map_zero]
-- --   · simp only [smulAAddHom', mul_zero, zero_mul, liftAddHom_tmul]; rfl
-- --   · simp_all only [map_add, zero_add]

-- -- instance : Module (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) where
-- --   smul := fun x a ↦ smulA K A B a x
-- --   one_smul := fun a ↦ by
-- --     change smulA K A B _ _ = _
-- --     simp only [smulA, smulAAddHom, smulAAddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
-- --       Algebra.TensorProduct.one_def, LinearMap.coe_mk, AddHom.coe_mk, liftAddHom_tmul]
-- --     change _ * _ * _ = a
-- --     simp only [one_mul, MulOpposite.unop_one, OneMemClass.coe_one, mul_one]
-- --   mul_smul := smulA_mul_smul K A B
-- --   smul_zero := smulA_zero K A B
-- --   smul_add := fun _ _ _ ↦ smulA_add K A B _ _ _
-- --   add_smul := fun x y a ↦ by
-- --     change smulA K A B _ _  = smulA K A B _ _ + smulA K A B _ _
-- --     simp only [map_add]
-- --   zero_smul := fun a ↦ by
-- --     change smulA K A B _ 0 = 0
-- --     simp only [map_zero]

-- -- lemma smulA_apply (a : A) (bop : Bᵐᵒᵖ) : ∀(a' : A_inst K A B), smulA K A B a' (a ⊗ₜ bop)
-- --     = a * a' * bop.unop.1 := fun a' ↦ by
-- --   simp only [smulA, smulAAddHom, smulAAddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
-- --     LinearMap.coe_mk, AddHom.coe_mk, liftAddHom_tmul]; rfl

-- -- def C_iso_toFun_toFun (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]
-- --     (c : (Subalgebra.centralizer (A := A) K B)):
-- --     Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) where
-- --   toFun := fun a ↦ c.1 * a
-- --   map_add' := fun a1 a2 ↦ by simp only [mul_add]
-- --   map_smul' := fun x a ↦ by
-- --     simp only [RingHom.id_apply]
-- --     induction x using TensorProduct.induction_on with
-- --     | zero => simp only [zero_smul, mul_zero]
-- --     | tmul a' bop =>
-- --         obtain ⟨c, hc⟩ := c
-- --         change c * smulA K A B _ _  = smulA K A B (c * a) _
-- --         simp only [smulA_apply]
-- --         rw [Subalgebra.mem_centralizer_iff] at hc
-- --         simp only [← mul_assoc]
-- --         sorry
-- --     | add x y hx hy => sorry

-- abbrev inclusion1 : A ⊗[K] Bᵐᵒᵖ →ₐ[K] Module.End K A :=
--   tensor_self_op.toEnd K A|>.comp $ (Algebra.TensorProduct.map (AlgHom.id _ _) $ AlgHom.op B.val)

-- /--this takes ten seconds someone should fix this -/
-- instance IsModA : Module (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) where
--   smul := fun x a1 ↦ inclusion1 K A B x a1
--   one_smul := fun a ↦ by
--     change inclusion1 K A B _ _ = _
--     simp only [_root_.map_one, LinearMap.one_apply]
--   mul_smul := fun x y a ↦ by
--     change inclusion1 K A B _ _ = inclusion1 K A B _ (inclusion1 K A B _ _)
--     simp only [_root_.map_mul, AlgHom.coe_comp, Function.comp_apply, LinearMap.mul_apply]
--   smul_zero := fun x ↦ by
--     change inclusion1 K A B _ _ = 0
--     simp only [AlgHom.coe_comp, Function.comp_apply, map_zero]
--   smul_add := fun x a1 a2 ↦ by
--     change inclusion1 K A B _ _ = inclusion1 K A B _ _ + inclusion1 K A B _ _
--     simp only [AlgHom.coe_comp, Function.comp_apply, map_add]
--   add_smul := fun x y a ↦ by
--     change inclusion1 K A B _ _ = _ + _
--     simp only [map_add, AlgHom.coe_comp, Function.comp_apply, LinearMap.add_apply]; rfl
--   zero_smul := fun a ↦ by
--     change inclusion1 K A B _ _ = 0
--     simp only [map_zero, LinearMap.zero_apply]

-- lemma inclusion1_apply (a : A) (bop : Bᵐᵒᵖ) (x : A_inst K A B):
--     inclusion1 K A B (a ⊗ₜ bop) x = a * x * bop.unop := by
--   simp only [AlgHom.coe_comp, tensor_self_op.toEnd, Function.comp_apply,
--     Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgHom.op_apply_apply, Subalgebra.coe_val,
--     Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
--     unop_op, LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
--   exact mul_assoc a x bop.unop|>.symm

-- instance : IsScalarTower K (A ⊗[K] (↥B)ᵐᵒᵖ) (A_inst K A B) where
--   smul_assoc := fun k x a ↦ by
--     change inclusion1 K A B _ _ = k • inclusion1 K A B _ _
--     simp only [LinearMapClass.map_smul, AlgHom.coe_comp, Function.comp_apply, LinearMap.smul_apply]

-- def C_iso_toFun_toFun (B : Subalgebra K A)
--     (c : (Subalgebra.centralizer (A := A) K B)):
--     Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) where
--   toFun := fun a ↦ a * c.1
--   map_add' := fun a1 a2 ↦ by simp only [add_mul]
--   map_smul' := fun x a ↦ by
--     simp only [RingHom.id_apply]
--     induction x using TensorProduct.induction_on with
--     | zero => simp only [zero_smul, zero_mul]
--     | tmul a' bop =>
--         obtain ⟨c, hc⟩ := c
--         change inclusion1 K A B _ _ * c = inclusion1 K A B _ (a * c)
--         rw [inclusion1_apply, inclusion1_apply, mul_assoc (a' * a) _ _, hc, ← mul_assoc,
--           ← mul_assoc]
--         obtain ⟨_, hb⟩ := bop.unop
--         exact hb
--     | add x y hx hy =>
--         simp only [add_smul, add_mul, hx, hy]

-- lemma C_iso_mapmul (B : Subalgebra K A) :
--     ∀(x y : Subalgebra.centralizer (A := A) K B), C_iso_toFun_toFun K A B (x * y) =
--     C_iso_toFun_toFun K A B x * C_iso_toFun_toFun K A B y := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
--   ext a
--   simp only [C_iso_toFun_toFun, Submonoid.mk_mul_mk, Submonoid.mk_smul, LinearMap.coe_mk,
--     AddHom.coe_mk, LinearMap.mul_apply, mul_smul]
--   sorry

-- abbrev ksmul : K → Module.End (A ⊗[K] (↥B)ᵐᵒᵖ) (A_inst K A B) → A_inst K A B →ₗ[A ⊗[K] (↥B)ᵐᵒᵖ]
--     A_inst K A B := fun k l ↦ {
--   toFun := fun a ↦ k • l a
--   map_add' := fun a1 a2 ↦ by simp only [map_add, smul_add]
--   map_smul' := fun k' a ↦ by
--     simp only [LinearMapClass.map_smul, RingHom.id_apply]
--     exact smul_comm _ _ _
-- }

-- -- set_option synthInstance.maxHeartbeats 60000 in
-- instance : Algebra K (Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B)) where
--   smul := ksmul K A B
--   toFun := fun k ↦ ⟨⟨(k • ·), smul_add _⟩, smul_comm _ ⟩
--   map_one' := by ext; simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply]
--   map_mul' := fun k1 k2 ↦ by
--     ext a
--     simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, LinearMap.map_smul_of_tower]
--     rw [mul_comm, mul_smul]
--   map_zero' := by simp only [zero_smul]; rfl
--   map_add' := fun k1 k2 ↦ by ext; simp only [add_smul, LinearMap.coe_mk, AddHom.coe_mk,
--     LinearMap.add_apply]
--   smul_def' := fun k l ↦ by
--     ext a
--     change _ = k • (l a)
--     rfl
--   commutes' := fun k l ↦ by
--     ext a
--     simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.mul_apply,
--       LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul_of_tower]

-- /-- C →ₐ[K] End (B ⊗ L) M -/
-- def C_iso_toFun (B : Subalgebra K A):
--     (Subalgebra.centralizer (A := A) K B) →ₐ[K]
--     Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) where
--   toFun c := C_iso_toFun_toFun K A B c
--   map_one' := by
--     ext a
--     simp only [C_iso_toFun_toFun, OneMemClass.coe_one, mul_one, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.one_apply]
--   map_mul' := C_iso_mapmul K A B
--   map_zero' := by
--     ext
--     simp only [C_iso_toFun_toFun, ZeroMemClass.coe_zero, mul_zero, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.zero_apply]
--   map_add' := fun x y ↦ by
--     ext m
--     simp only [C_iso_toFun_toFun, AddMemClass.coe_add, mul_add, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.add_apply]
--   commutes' := fun k ↦ by
--     ext m
--     simp only [C_iso_toFun_toFun]
--     change m * _ = k • m
--     simp only [Subalgebra.coe_algebraMap]
--     unfold A_inst at *
--     rw [← Algebra.commutes (R := K) k m, Algebra.smul_def]

-- lemma C_iso_inj (B : Subalgebra K A): Function.Injective
--     (C_iso_toFun K A B) := RingHom.injective_iff_ker_eq_bot (C_iso_toFun K A B)|>.2 $ by
--   ext ⟨c, hc⟩
--   constructor
--   · intro hhc
--     -- change c = 0
--     change C_iso_toFun K A B ⟨c, hc⟩ = (0 : Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B)) at hhc
--     simp only [C_iso_toFun, C_iso_toFun_toFun, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
--       OneHom.coe_mk, Submonoid.mk_smul] at hhc
--     have : c = 0 := by
--       have := DFunLike.ext_iff.1 hhc (1 : A)
--       change 1 * c = 0 at this
--       simp only [one_mul] at this ⊢
--       exact this
--     change ⟨c, hc⟩ = (0 : Subalgebra.centralizer K B)
--     exact Eq.symm $ SetCoe.ext (id this.symm)
--   · intro hhc
--     simp only [Ideal.mem_bot] at hhc ⊢
--     simp only [hhc, Submodule.zero_mem]

-- lemma C_iso_surj: Function.Surjective (C_iso_toFun K A B) := by
--   intro l
--   let c := l 1
--   have eq1 : ∀(b : B), l (((1 : A) ⊗ₜ[K] (op b)) • 1) = l b.1 := fun b ↦ by
--     change l (inclusion1 K A B _ _) = _
--     rw [inclusion1_apply]
--     simp only [mul_one, unop_op, one_mul]
--   have eq2 : ∀(b : B), b.1 * c = b.1 ⊗ₜ[K] (1 : Bᵐᵒᵖ) • c := fun b ↦ by
--     change  _ = inclusion1 K A B _ _
--     rw [inclusion1_apply]
--     simp only [unop_one, OneMemClass.coe_one, mul_one]
--   have eq3 : ∀(b : B), l (b.1 ⊗ₜ[K] (1 : Bᵐᵒᵖ) • 1) = l b.1 := fun b ↦ by
--     change l (inclusion1 K A B _ _) = _
--     rw [inclusion1_apply]
--     simp only [mul_one, unop_one, OneMemClass.coe_one]
--   have eq4 : ∀(b : B), c * b.1 = (1 : A) ⊗ₜ[K] (op b) • c := fun b ↦ by
--     change _ = inclusion1 K A B _ _
--     rw [inclusion1_apply]
--     simp only [one_mul, unop_op]
--   have abel1: ∀(b : B), b.1 * c = l b.1 := fun b ↦ by
--     rw [eq2]
--     change _ • l 1 = _
--     rw [← LinearMap.map_smul, eq3]
--   have abelll: ∀(b : B), b.1 * c = c * b.1 := fun b ↦ by
--     rw [abel1, eq4, show c = l 1 from rfl, ← LinearMap.map_smul, eq1]
--   have hc : c ∈ Subalgebra.centralizer (A := A) K B := by
--     rw [Subalgebra.mem_centralizer_iff]
--     unfold A_inst at *
--     convert abelll using 1
--     simp_all only [LinearMapClass.map_smul, Subtype.forall, SetLike.coe_mem, Subtype.coe_eta, SetLike.mem_coe,
--       implies_true, c]
--   use ⟨c, hc⟩
--   ext (a : A)
--   simp only [C_iso_toFun, C_iso_toFun_toFun, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
--     OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
--   rw [show a * c = (a : A) ⊗ₜ[K] (1 : Bᵐᵒᵖ) • c by
--     change _ = inclusion1 K A B _ _
--     rw [inclusion1_apply]; simp only [unop_one, OneMemClass.coe_one, mul_one],
--     show c = l 1 from rfl, ← LinearMap.map_smul]
--   change l (inclusion1 K A B _ _) = _
--   rw [inclusion1_apply]
--   simp only [mul_one, unop_one, OneMemClass.coe_one]

-- def C_iso (B : Subalgebra K A) [IsSimpleOrder (TwoSidedIdeal B)]:
--     (Subalgebra.centralizer (A := A) K B) ≃ₐ[K]
--     Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) :=
--   AlgEquiv.ofBijective (C_iso_toFun K A B) ⟨C_iso_inj K A B, C_iso_surj K A B⟩

-- section centralsimple

-- variable [hA : IsCentralSimple K A] [FiniteDimensional K A] [IsSimpleOrder (TwoSidedIdeal B)]

-- instance : IsSimpleOrder (TwoSidedIdeal (A ⊗[K] Bᵐᵒᵖ)) :=
--   (OrderIso.isSimpleOrder_iff (TwoSidedIdeal.orderIsoOfRingEquiv
--     (Algebra.TensorProduct.comm K A Bᵐᵒᵖ))).2 $
--     @IsCentralSimple.TensorProduct.simple K _ Bᵐᵒᵖ A _ _ _ _ _ hA

-- instance : FiniteDimensional K (A ⊗[K] Bᵐᵒᵖ) := inferInstance

-- set_option synthInstance.maxHeartbeats 40000 in
-- instance : Module K (Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B)) := inferInstance

-- -- set_option synthInstance.maxHeartbeats 80000 in
-- set_option maxHeartbeats 500000 in
-- variable (ι M : Type u) [AddCommGroup M] [Module K M]
--     [Module (A ⊗[K] Bᵐᵒᵖ) M] [DecidableEq M]
--     [IsScalarTower K (A ⊗[K] Bᵐᵒᵖ) M] in
-- instance : HSMul (A ⊗[K] (↥B)ᵐᵒᵖ) (Module.End (A ⊗[K] Bᵐᵒᵖ) (ι →₀ M))
--     (Module.End (A ⊗[K] Bᵐᵒᵖ) (ι →₀ M)) where
--   hSMul := fun x mn ↦ {
--     toFun := fun im ↦ {
--       support := im.support.filter fun j => (x • im j) ≠ 0
--       toFun := fun i ↦ x • im i
--       mem_support_toFun := fun j ↦ ⟨fun hj ↦ by
--         simp only [ne_eq, Finset.mem_filter, Finsupp.mem_support_iff] at hj
--         exact hj.2, fun hj ↦ by
--           simp only [ne_eq, Finset.mem_filter, Finsupp.mem_support_iff]
--           simp only [ne_eq] at hj
--           constructor
--           · by_contra! hj'
--             simp only [hj', smul_zero, not_true_eq_false] at hj
--           · exact hj  ⟩}
--     map_add' := fun nm1 nm2 ↦ by
--       simp only [Finsupp.coe_add, Pi.add_apply, smul_add, ne_eq]
--       ext
--       simp only [Finsupp.coe_mk, Finsupp.coe_add, Pi.add_apply]
--     map_smul' := fun k nm ↦ by
--       ext i
--       simp only [Finsupp.coe_smul, Pi.smul_apply, ne_eq, Finsupp.coe_mk, RingHom.id_apply]
--       -- conv_lhs => sorry
--       sorry
--       -- rw [smul_comm]

--   }

-- variable (ι M : Type u) [AddCommGroup M] [Module (A ⊗[K] Bᵐᵒᵖ) M] [DecidableEq M] in
-- instance modK: Module K (Module.End (A ⊗[K] Bᵐᵒᵖ) (ι →₀ M)) where
--   smul k := fun x ↦ algebraMap K (A ⊗[K] Bᵐᵒᵖ) k • x
--   one_smul := sorry
--   mul_smul := sorry
--   smul_zero := sorry
--   smul_add := sorry
--   add_smul := sorry
--   zero_smul := sorry

-- variable (ι M : Type u) [AddCommGroup M] [Module (A ⊗[K] Bᵐᵒᵖ) M] in
-- instance isring : Ring (Module.End (A ⊗[K] Bᵐᵒᵖ) (ι →₀ M)) := inferInstance

-- variable (ι M : Type u) [AddCommGroup M] [Module (A ⊗[K] Bᵐᵒᵖ) M] in
-- instance : Algebra K (Module.End (A ⊗[K] Bᵐᵒᵖ) (ι →₀ M)) := sorry
-- -- {
-- --   modK K A B ι M, isring K A B ι M with
-- --   <;> sorry
-- -- }

-- lemma centralizer_is_simple : IsSimpleOrder (TwoSidedIdeal (Subalgebra.centralizer (A := A) K B)) := by
--   haveI := hA.2
--   obtain ⟨M, _, _, _, ι, ⟨iso⟩⟩:= directSum_simple_module_over_simple_ring K (A ⊗[K] Bᵐᵒᵖ) $
--     A_inst K A B
--   let D := Module.End (A ⊗[K] Bᵐᵒᵖ) M
--   have := C_iso K A B
--   have e1 : Module.End (A ⊗[K] Bᵐᵒᵖ) (A_inst K A B) ≃ₐ[K] Module.End (A ⊗[K] Bᵐᵒᵖ) (ι →₀ M) := sorry

--   sorry

-- -- def endEquivMat (R M ι: Type u) [Ring R] [AddCommGroup M] [Module R M] [DecidableEq ι] [Fintype ι]:
-- --     Module.End R (ι → M) ≃ₗ[R] Matrix ι ι (Module.End R M) := sorry
-- end centralsimple

-- variable (K A : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
--     [hA : IsCentralSimple K A] (B : Subalgebra K A)
-- theorem doubleCentralizer: Subalgebra.centralizer (A := A) K
--     (Subalgebra.centralizer (A := A) K B) = B := by
--   sorry
-- --GIVE UPPPPPPPPP
-- -- lemma finiteM: Module.Finite A M := by
-- --   have i : Submodule.IsPrincipal (⊤ : Submodule A M) := inferInstance
-- --   refine ⟨⟨{i.1.choose}, ?_⟩⟩
-- --   symm
-- --   have := i.1.choose_spec
-- --   refine this.trans ?_
-- --   congr
-- --   simp only [Set.mem_singleton_iff, Finset.coe_singleton]

-- -- set_option synthInstance.maxHeartbeats 60000 in
-- -- instance (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
-- --   Module K $ Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) := inferInstance

-- -- set_option synthInstance.maxHeartbeats 60000 in
-- -- instance (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
-- --   Algebra K $ Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) := inferInstance

-- -- def C_iso_toFun_toFun (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]
-- --     (c : (Subalgebra.centralizer (A := A) K B)):
-- --     Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) where
-- --   toFun := fun m ↦ c • m
-- --   map_add' := smul_add _
-- --   map_smul' := fun x m ↦ by
-- --     simp only [Subalgebra.coe_centralizer, RingHom.id_apply]
-- --     induction x using TensorProduct.induction_on
-- --     · simp only [zero_smul, smul_zero]
-- --     · rename_i b l
-- --       change c • (smul1 _ _ _ _ _ _ _) = smul1 _ _ _ _ _ _ _
-- --       simp only [smul1, smul1AddHom, smul1AddHom', Subalgebra.coe_val, ZeroHom.toFun_eq_coe,
-- --         AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, liftAddHom_tmul,
-- --         AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.map_smul_of_tower]
-- --       obtain ⟨c, hc⟩ := c
-- --       rw [Subalgebra.mem_centralizer_iff] at hc
-- --       obtain ⟨b, hb⟩ := b
-- --       have hb' : b ∈ (B : Set A) := hb
-- --       specialize hc b hb'
-- --       simp only [Submonoid.mk_smul, ← mul_smul, hc]
-- --     · simp_all only [add_smul, smul_add]


-- -- lemma C_iso_mapmul (B : Subalgebra K A) [IsSimpleOrder (RingCon B)] :
-- --     ∀(x y : Subalgebra.centralizer (A := A) K B), C_iso_toFun_toFun K A M B (x * y) =
-- --     C_iso_toFun_toFun K A M B x * C_iso_toFun_toFun K A M B y := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
-- --   ext m
-- --   simp only [C_iso_toFun_toFun, Submonoid.mk_mul_mk, Submonoid.mk_smul, LinearMap.coe_mk,
-- --     AddHom.coe_mk, LinearMap.mul_apply, mul_smul]

-- -- /-- C →ₐ[K] End (B ⊗ L) M -/
-- -- def C_iso_toFun (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
-- --     (Subalgebra.centralizer (A := A) K B) →ₐ[K]
-- --     Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) where
-- --   toFun c := C_iso_toFun_toFun K A M B c
-- --   map_one' := by
-- --     ext
-- --     simp only [C_iso_toFun_toFun, one_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply]
-- --   map_mul' := C_iso_mapmul K A M B
-- --   map_zero' := by
-- --     ext
-- --     simp only [C_iso_toFun_toFun, zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
-- --   map_add' := fun x y ↦ by
-- --     ext m
-- --     simp only [C_iso_toFun_toFun, add_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
-- --   commutes' := fun k ↦ by
-- --     ext m
-- --     simp only [C_iso_toFun_toFun, algebraMap_smul, LinearMap.coe_mk, AddHom.coe_mk,
-- --       Module.algebraMap_end_apply]

-- -- instance findimM (B : Subalgebra K A) : Module.Finite (B ⊗[K] (Module.End A M))
-- --     (module_inst K A B M B.val) := inferInstance
-- -- -- f(c) = 0 → c • M = 0 → c ∈ Ann(M) →(A simple) c = 0

-- -- abbrev Annilator_TwoSidedIdeal (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]: RingCon B :=
-- --   RingCon.fromIdeal {x | x.1 ∈ (Subalgebra.centralizer (A := A) K B) ∧ ∀(m : M), x • m = 0} sorry _ _ _
-- --   $ fun ⟨b11, b12⟩ ⟨b21, b22⟩ ⟨hb11, hb12⟩ ↦ by
-- --     rw [Subalgebra.mem_centralizer_iff] at hb11
-- --     simp only [Submonoid.mk_mul_mk, Set.mem_setOf_eq, Submonoid.mk_smul]
-- --     constructor
-- --     · sorry
-- --     · sorry

-- -- lemma C_iso_inj (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]: Function.Injective
-- --     (C_iso_toFun K A M B) := RingHom.injective_iff_ker_eq_bot (C_iso_toFun K A M B)|>.2 $ by
-- --   ext ⟨c, hc⟩
-- --   constructor
-- --   · intro hhc
-- --     -- change c = 0
-- --     change C_iso_toFun K A M B ⟨c, hc⟩ = (0 : Module.End
-- --       (↥B ⊗[K] Module.End A M) (module_inst K A (↥B) M B.val)) at hhc
-- --     simp only [C_iso_toFun, C_iso_toFun_toFun, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
-- --       OneHom.coe_mk, Submonoid.mk_smul] at hhc
-- --     obtain ⟨ℬ, hℬ⟩ := findimM K A M B
-- --     -- apply DFunLike.ext_iff at hhc
-- --     sorry
-- --   · intro hhc
-- --     simp only [Ideal.mem_bot] at hhc ⊢
-- --     simp only [hhc, Submodule.zero_mem]

-- -- def C_iso (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
-- --     (Subalgebra.centralizer (A := A) K B) ≃ₐ[K]
-- --     Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) :=
-- --   AlgEquiv.ofBijective (C_iso_toFun K A M B) ⟨C_iso_inj K A M B, sorry⟩

-- -- lemma double_centralizer1 (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
-- --     IsSimpleOrder (RingCon (Subalgebra.centralizer (A := A) K B)) := by
-- --   let C := Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val)
-- --   have simple_C: IsSimpleOrder (RingCon C) := sorry  -- need 074E (6)
-- --   -- haveI : FiniteDimensional K M := @Module.Finite.trans K A M _ _ _ _ _ _ _ _ (finiteM A M)
-- --   -- obtain ⟨m, hm, D, hD1, hD2, ⟨iso⟩⟩ := Wedderburn_Artin_algebra_version K (B ⊗[K] (Module.End A M))
-- --   exact OrderIso.isSimpleOrder_iff (RingCon.orderIsoOfRingEquiv (C_iso K A M B))|>.2 simple_C

-- -- lemma double_centralizer2 (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
-- --     FiniteDimensional.finrank K A = (FiniteDimensional.finrank K B) * (FiniteDimensional.finrank K
-- --     (Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val))) := sorry

-- -- -- R = A ⊗ B, unique R simple mod M, A is R-mod → A ≃ Mⁿ
-- -- -- Cₐ(B) ≃ End R A ≃ End R (Mⁿ) ≃ Mₙ(End R M) ≃ Mₙ(D)

-- -- def EndtoMat : Module.End R ((Fin n) → M) ≃ Mₙ(End R M)
