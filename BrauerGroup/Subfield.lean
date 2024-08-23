import BrauerGroup.SkolemNoether

universe u

suppress_compilation

open BigOperators TensorProduct

section def_and_lemmas

structure SubField (K A : Type u) [Field K] [Semiring A] [Algebra K A] extends Subalgebra K A where
  is_field : IsField carrier

def IsMaximalSubfield (K A : Type u) [Field K] [Semiring A] [Algebra K A] (L : SubField K A) : Prop
  := ∀ (B : SubField K A), L.1 ≤ B.1 → B = L

-- variable (K A N: Type u) [Field K] [Ring A] [Algebra K A] [AddCommGroup N] [Module A N]
--     [Module K N]

-- instance : Ring (Module.End A N) := inferInstance

-- instance : IsScalarTower K A N :=
--   IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun $ by
--     ext n; rename_i k ; sorry

-- instance (priorty := 500): Algebra K (Module.End A N) := inferInstance

-- lemma six074E (K A N M: Type u) (n : ℕ) (_ : n ≠ 0) [Field K] [Ring A] [Algebra K A]
--     [FiniteDimensional K A] (hA : IsSimpleOrder (RingCon A)) [AddCommGroup N] [Module A N]
--     [AddCommGroup M] [Module A M] (hM : M = (Fin n → A)) :
--     ∃(n : ℕ)(_ : n ≠ 0), Nonempty (Module.End A N ≃ₐ[K] Matrix (Fin n) (Fin n) (Module.End A M)):= sorry

end def_and_lemmas

-- variable (K A M: Type u) [Field K] [Ring A] [Algebra K A] [hA : IsCentralSimple K A]
--   [FiniteDimensional K A] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
--   [IsSimpleModule A M]

variable (K A: Type u) [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)

def A_inst (K A: Type u) [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A) := A

instance: AddCommGroup $ A_inst K A B := inferInstanceAs $ AddCommGroup A

instance: Module K $ A_inst K A B := inferInstanceAs $ Module K A

instance: Ring $ A_inst K A B := inferInstanceAs $ Ring A

instance: Algebra K $ A_inst K A B := inferInstanceAs $ Algebra K A

instance : HMul A (A_inst K A B) A where
  hMul := fun a a' ↦ by
    unfold A_inst at a'
    exact a * a'

def smulAAddHom'  (K A: Type u) [Field K] [Ring A] [Algebra K A]
    (B : Subalgebra K A): (A_inst K A B) → A →+ B →+ A :=
  fun a ↦ {
    toFun := fun x ↦ {
      toFun := fun ⟨b, _⟩ ↦ b * x * a
      map_zero' := by simp only [zero_mul]
      map_add' := fun a1 a2 ↦ by simp only [add_mul]
    }
    map_zero' := by ext; simp only [mul_zero, zero_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.zero_apply]
    map_add' := fun b1 b2 ↦ by ext; simp only [mul_add, add_mul, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AddMonoidHom.add_apply] }

def smulAAddHom  (K A: Type u)
    [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A):
    (A_inst K A B) → A ⊗[K] B →+ A_inst K A B := fun a ↦
  TensorProduct.liftAddHom (smulAAddHom' K A B a) $ fun k a' ⟨b, _⟩ ↦ by
  unfold A_inst at a
  simp only [smulAAddHom', SetLike.mk_smul_mk]
  change _ * (k • a') * _ = _ * a' * _
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

def smulA (K A: Type u)
    [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A):
    (A_inst K A B) → A ⊗[K] B →ₗ[K] A_inst K A B := fun a ↦ {
  __ := smulAAddHom K A B a
  map_smul' := fun k ab ↦ by
    simp only [smulAAddHom, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
    induction ab using TensorProduct.induction_on
    · simp only [smul_zero, map_zero]
    · rename_i a' b
      obtain ⟨b, hb⟩ := b
      simp only [smulAAddHom', liftAddHom_tmul, TensorProduct.smul_tmul',
        SetLike.mk_smul_mk, liftAddHom_tmul]
      change _ * (k • a') * a = k • (_ * a' * _)
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    · rename_i x y hx hy
      simp only [smul_add, map_add, hx, add_right_inj, hy]
  }

lemma smulA_mul_smul : ∀ (x y : A ⊗[K] B) (b : A_inst K A B), smulA K A B b (x * y) =
    smulA K A B (smulA K A B b y) x := fun x y a ↦ by
  dsimp only [smulA, smulAAddHom, smulAAddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    LinearMap.coe_mk, AddHom.coe_mk]
  induction x using TensorProduct.induction_on
  · simp only [zero_mul, map_zero]
  · rename_i a' b
    induction y using TensorProduct.induction_on
    · simp only [mul_zero, map_zero, liftAddHom_tmul]; rfl
    · rename_i a1 b1
      obtain ⟨b1, hb1⟩ := b1; obtain ⟨b, hb⟩ := b
      unfold A_inst at *
      simp only [Algebra.TensorProduct.tmul_mul_tmul, Submonoid.mk_mul_mk, liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk]

      sorry
    sorry
  sorry

instance : Module (A ⊗[K] B) (A_inst K A B) where
  smul := fun x a ↦ smulA K A B a x
  one_smul := fun a ↦ by
    change smulA K A B _ _  = _
    simp only [smulA, smulAAddHom, smulAAddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      Algebra.TensorProduct.one_def, LinearMap.coe_mk, AddHom.coe_mk, liftAddHom_tmul]
    change _ * _ * _ = a
    simp only [OneMemClass.coe_one, mul_one, one_mul]
  mul_smul := smulA_mul_smul K A B
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry
-- lemma finiteM: Module.Finite A M := by
--   have i : Submodule.IsPrincipal (⊤ : Submodule A M) := inferInstance
--   refine ⟨⟨{i.1.choose}, ?_⟩⟩
--   symm
--   have := i.1.choose_spec
--   refine this.trans ?_
--   congr
--   simp only [Set.mem_singleton_iff, Finset.coe_singleton]

-- set_option synthInstance.maxHeartbeats 60000 in
-- instance (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
--   Module K $ Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) := inferInstance

-- set_option synthInstance.maxHeartbeats 60000 in
-- instance (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
--   Algebra K $ Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) := inferInstance

-- def C_iso_toFun_toFun (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]
--     (c : (Subalgebra.centralizer (A := A) K B)):
--     Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) where
--   toFun := fun m ↦ c • m
--   map_add' := smul_add _
--   map_smul' := fun x m ↦ by
--     simp only [Subalgebra.coe_centralizer, RingHom.id_apply]
--     induction x using TensorProduct.induction_on
--     · simp only [zero_smul, smul_zero]
--     · rename_i b l
--       change c • (smul1 _ _ _ _ _ _ _) = smul1 _ _ _ _ _ _ _
--       simp only [smul1, smul1AddHom, smul1AddHom', Subalgebra.coe_val, ZeroHom.toFun_eq_coe,
--         AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, liftAddHom_tmul,
--         AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.map_smul_of_tower]
--       obtain ⟨c, hc⟩ := c
--       rw [Subalgebra.mem_centralizer_iff] at hc
--       obtain ⟨b, hb⟩ := b
--       have hb' : b ∈ (B : Set A) := hb
--       specialize hc b hb'
--       simp only [Submonoid.mk_smul, ← mul_smul, hc]
--     · simp_all only [add_smul, smul_add]


-- lemma C_iso_mapmul (B : Subalgebra K A) [IsSimpleOrder (RingCon B)] :
--     ∀(x y : Subalgebra.centralizer (A := A) K B), C_iso_toFun_toFun K A M B (x * y) =
--     C_iso_toFun_toFun K A M B x * C_iso_toFun_toFun K A M B y := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
--   ext m
--   simp only [C_iso_toFun_toFun, Submonoid.mk_mul_mk, Submonoid.mk_smul, LinearMap.coe_mk,
--     AddHom.coe_mk, LinearMap.mul_apply, mul_smul]

-- /-- C →ₐ[K] End (B ⊗ L) M -/
-- def C_iso_toFun (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
--     (Subalgebra.centralizer (A := A) K B) →ₐ[K]
--     Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) where
--   toFun c := C_iso_toFun_toFun K A M B c
--   map_one' := by
--     ext
--     simp only [C_iso_toFun_toFun, one_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply]
--   map_mul' := C_iso_mapmul K A M B
--   map_zero' := by
--     ext
--     simp only [C_iso_toFun_toFun, zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
--   map_add' := fun x y ↦ by
--     ext m
--     simp only [C_iso_toFun_toFun, add_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
--   commutes' := fun k ↦ by
--     ext m
--     simp only [C_iso_toFun_toFun, algebraMap_smul, LinearMap.coe_mk, AddHom.coe_mk,
--       Module.algebraMap_end_apply]

-- instance findimM (B : Subalgebra K A) : Module.Finite (B ⊗[K] (Module.End A M))
--     (module_inst K A B M B.val) := inferInstance
-- -- f(c) = 0 → c • M = 0 → c ∈ Ann(M) →(A simple) c = 0

-- abbrev Annilator_TwoSidedIdeal (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]: RingCon B :=
--   RingCon.fromIdeal {x | x.1 ∈ (Subalgebra.centralizer (A := A) K B) ∧ ∀(m : M), x • m = 0} sorry _ _ _
--   $ fun ⟨b11, b12⟩ ⟨b21, b22⟩ ⟨hb11, hb12⟩ ↦ by
--     rw [Subalgebra.mem_centralizer_iff] at hb11
--     simp only [Submonoid.mk_mul_mk, Set.mem_setOf_eq, Submonoid.mk_smul]
--     constructor
--     · sorry
--     · sorry

-- lemma C_iso_inj (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]: Function.Injective
--     (C_iso_toFun K A M B) := RingHom.injective_iff_ker_eq_bot (C_iso_toFun K A M B)|>.2 $ by
--   ext ⟨c, hc⟩
--   constructor
--   · intro hhc
--     -- change c = 0
--     change C_iso_toFun K A M B ⟨c, hc⟩ = (0 : Module.End
--       (↥B ⊗[K] Module.End A M) (module_inst K A (↥B) M B.val)) at hhc
--     simp only [C_iso_toFun, C_iso_toFun_toFun, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
--       OneHom.coe_mk, Submonoid.mk_smul] at hhc
--     obtain ⟨ℬ, hℬ⟩ := findimM K A M B
--     -- apply DFunLike.ext_iff at hhc
--     sorry
--   · intro hhc
--     simp only [Ideal.mem_bot] at hhc ⊢
--     simp only [hhc, Submodule.zero_mem]

-- def C_iso (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
--     (Subalgebra.centralizer (A := A) K B) ≃ₐ[K]
--     Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val) :=
--   AlgEquiv.ofBijective (C_iso_toFun K A M B) ⟨C_iso_inj K A M B, sorry⟩

-- lemma double_centralizer1 (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
--     IsSimpleOrder (RingCon (Subalgebra.centralizer (A := A) K B)) := by
--   let C := Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val)
--   have simple_C: IsSimpleOrder (RingCon C) := sorry  -- need 074E (6)
--   -- haveI : FiniteDimensional K M := @Module.Finite.trans K A M _ _ _ _ _ _ _ _ (finiteM A M)
--   -- obtain ⟨m, hm, D, hD1, hD2, ⟨iso⟩⟩ := Wedderburn_Artin_algebra_version K (B ⊗[K] (Module.End A M))
--   exact OrderIso.isSimpleOrder_iff (RingCon.orderIsoOfRingEquiv (C_iso K A M B))|>.2 simple_C

-- lemma double_centralizer2 (B : Subalgebra K A) [IsSimpleOrder (RingCon B)]:
--     FiniteDimensional.finrank K A = (FiniteDimensional.finrank K B) * (FiniteDimensional.finrank K
--     (Module.End (B ⊗[K] (Module.End A M)) (module_inst K A B M B.val))) := sorry

-- -- R = A ⊗ B, unique R simple mod M, A is R-mod → A ≃ Mⁿ
-- -- Cₐ(B) ≃ End R A ≃ End R (Mⁿ) ≃ Mₙ(End R M) ≃ Mₙ(D)

-- def EndtoMat : Module.End R ((Fin n) → M) ≃ Mₙ(End R M)
