import BrauerGroup.BrauerGroup
import BrauerGroup.«074E»

suppress_compilation

universe u v w

open Classical MulOpposite
open scoped TensorProduct

variable (K : Type u) [Field K]

-- variable {A B M: Type u} [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
--         [csA : IsCentralSimple K A] [hSimple : IsSimpleOrder (RingCon B)]
--         [AddCommGroup M][Module A M][IsSimpleModule A M]
-- variable (L: Module.End A M)
-- -- lemma first
-- -- def L:= Module.End A M
-- -- instance (L: Module.End A M): DivisionRing L := sorry

set_option linter.unusedVariables false in
def module_inst (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] (f : B →ₐ[K] A) := M

instance (K A B M : Type u) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] (f: B →ₐ[K] A) [AddCommGroup M]:
    AddCommGroup (module_inst K A B M f) :=
  inferInstanceAs $ AddCommGroup M

instance inst_K_mod (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : Module K (module_inst K A B M f) :=
  Module.compHom M (algebraMap K A)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : Module A (module_inst K A B M f) :=
  inferInstanceAs (Module A M)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) : IsScalarTower K A (module_inst K A B M f) :=
  IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl

def smul1AddHom'  (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → B →+ (Module.End A M) →+ (module_inst K A B M f) :=
  fun m ↦ {
    toFun := fun b ↦ {
      toFun := fun l ↦ (f b) • (l m)
      map_zero' := by simp only [LinearMap.zero_apply, smul_zero]
      map_add' := fun l1 l2 ↦ by simp only [LinearMapClass.map_smul, ← smul_add]; rfl
    }
    map_zero' := by ext; simp
    map_add' := fun b1 b2 ↦ by
      ext l; simp only [map_add, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_coe,
      opAddEquiv_apply, Function.comp_apply, unop_op, AddMonoidHom.add_apply];
      exact Module.add_smul (f b1) (f b2) (l m)
  }

def smul1AddHom (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → (B ⊗[K] (Module.End A M)) →+ (module_inst K A B M f) := fun m ↦
  TensorProduct.liftAddHom (smul1AddHom' K A B M f m) fun k b l ↦ by
    simp only [smul1AddHom', AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMapClass.map_smul,
      smul_assoc, unop_smul, LinearMap.smul_apply]
    rw [smul_comm]

def smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A][Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    (module_inst K A B M f) → (B ⊗[K] (Module.End A M)) →ₗ[K] (module_inst K A B M f) :=
  fun m ↦ {
    __ := smul1AddHom K A B M f m
    map_smul' := fun k b ↦ by
      simp only [smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        RingHom.id_apply]
      induction b using TensorProduct.induction_on
      · simp only [smul_zero, map_zero]
      · rename_i b l
        simp only [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk, LinearMapClass.map_smul, smul_assoc]
        congr
        ext k m
        change k • m = algebraMap _ _ k • m
        simp only [algebraMap_smul]
      · rename_i bl1 bl2 hbl1 hbl2
        simp only [smul_add, map_add, hbl1, hbl2]
  }

lemma one_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):
    ∀(m : module_inst K A B M f), smul1 K A B M f m 1 = m := fun m ↦ by
  simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    Algebra.TensorProduct.one_def, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul, unop_one, LinearMap.one_apply]

lemma mul_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):  ∀ (x y : (B ⊗[K] (Module.End A M)))
    (m : module_inst K A B M f),
    smul1 K A B M f m (x * y) = smul1 K A B M f (smul1 K A B M f m y) x := fun x y m ↦ by
  dsimp [smul1, smul1AddHom, smul1AddHom']
  induction x using TensorProduct.induction_on
  · simp only [zero_mul, map_zero]
  · rename_i b1 l1
    induction y using TensorProduct.induction_on
    · simp only [mul_zero, map_zero, smul_zero, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    · rename_i b2 l2
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, unop_mul, LinearMap.mul_apply,
        LinearMapClass.map_smul]
      simp only [smul_smul]
    · simp_all [mul_add]
  · simp_all [add_mul]

lemma smul1_add (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A):  ∀ (r : (B ⊗[K] (Module.End A M)))
    (m1 m2 : module_inst K A B M f),
    smul1 K A B M f (m1 + m2) r = smul1 K A B M f m1 r + smul1 K A B M f m2 r := fun r m1 m2 ↦ by
  induction r using TensorProduct.induction_on
  · simp only [map_zero, smul_zero, add_zero]
  · simp only [smul1, smul1AddHom, smul1AddHom', map_add, smul_add, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  · rename_i a b ha hb
    simp_all only [smul1, smul1AddHom, smul1AddHom', map_add, smul_add, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, ← add_assoc, add_left_inj]
    nth_rw 2 [add_assoc]; nth_rw 4 [add_comm]
    rw [← add_assoc]

lemma add_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A): ∀ (r s : B ⊗[K] Module.End A M)
    (x : module_inst K A B M f), smul1 K A B M f x (r + s) =
    smul1 K A B M f x r + smul1 K A B M f x s := fun r s x ↦ by
  simp only [smul1, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add, LinearMap.coe_mk,
    AddHom.coe_mk]

instance IsMod (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    Module (B ⊗[K] (Module.End A M)) (module_inst K A B M f) where
  smul := fun r m => smul1 K A B M f m r
  one_smul := one_smul1 K A B M f
  mul_smul := mul_smul1 K A B M f
  smul_zero a := by
    change smul1 K A B M f 0 a = 0
    rw [smul1]
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk]
    induction a using TensorProduct.induction_on
    · simp only [map_zero]
    · rename_i b l
      simp only [smul1AddHom, smul1AddHom', map_zero, smul_zero, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    · simp_all [map_add]
  smul_add := smul1_add K A B M f
  add_smul := add_smul1 K A B M f
  zero_smul m := by
    change smul1 K A B M f m 0 = 0
    simp only [smul1, map_zero, smul_zero]

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    IsScalarTower K (B ⊗[K] Module.End A M) (module_inst K A B M f) where
  smul_assoc a x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b z =>
      change (smul1 K A B M f _ _) = _ • smul1 K A B M f _ _
      simp
    | add x y hx hy =>
      rw [smul_add, add_smul, hx, hy, add_smul, smul_add]

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f: B →ₐ[K] A) :
    Module.Finite (B ⊗[K] Module.End A M) (module_inst K A B M f) := by
  have : Module.Finite A M := ⟨⟨{gen A M}, eq_top_iff.2 fun x _ => by
    obtain ⟨a, rfl⟩ := gen_spec A M x
    apply Submodule.smul_mem
    refine Submodule.subset_span ?_
    aesop⟩⟩
  obtain ⟨s, hs⟩ : Module.Finite K M := Module.Finite.trans A M
  refine ⟨⟨s, eq_top_iff.2 ?_⟩⟩
  rintro x -
  have mem : (x : M) ∈ (Submodule.span K s : Submodule K M) := hs ▸ ⟨⟩
  obtain ⟨c, hc1, rfl⟩ := mem_span_set (R := K) (M := M) |>.1 mem
  refine Submodule.sum_mem _ fun k hk => ?_
  simp only
  rw [show (c k • k : module_inst K A B M f) =
    ((algebraMap K (B ⊗[K] Module.End A M) (c k)) • (show module_inst K A B M f from k)) by
      simp only [Algebra.TensorProduct.algebraMap_apply]
      change _ = smul1 K A B M f k _
      simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, AlgHom.commutes, algebraMap_smul, LinearMap.one_apply]]
  refine Submodule.smul_mem _ _ ?_
  simp only
  refine Submodule.subset_span ?_
  exact hc1 hk

instance tensor_is_simple (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [IsSimpleOrder (TwoSidedIdeal B)][AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] [csa_A : IsCentralSimple K A]: IsSimpleOrder
    (TwoSidedIdeal (B ⊗[K] (Module.End A M))) := by
  haveI := csa_A.2
  obtain ⟨n, hn, D, hD1, hD2, ⟨iso⟩⟩ := Wedderburn_Artin_algebra_version K A
  have : NeZero n := { out := hn }
  obtain ⟨e1⟩ := end_simple_mod_of_wedderburn' K A n D iso M
  haveI : IsCentralSimple K (Module.End A M) :=
    AlgEquiv.isCentralSimple (hcs := CSA_op_is_CSA K D $
      CSA_implies_CSA K A n D (by omega) _ iso csa_A) e1.symm
  exact @IsCentralSimple.TensorProduct.simple K _ B (Module.End A M) _ _ _ _ _ this

variable (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] [Ring B]
    [Algebra K B] [hB : IsSimpleOrder (RingCon B)] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f g : B →ₐ[K] A)

set_option linter.unusedVariables false in
lemma findimB (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] [Ring B]
    [Algebra K B] [hB : IsSimpleOrder (TwoSidedIdeal B)] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f g : B →ₐ[K] A):
    FiniteDimensional K B := FiniteDimensional.of_injective (K := K) (V₂ := A) f (by
    haveI := hA.2
    haveI : Nontrivial A := TwoSidedIdeal.instNontrivialOfIsSimpleOrder_brauerGroup A
    change Function.Injective f
    have H := TwoSidedIdeal.IsSimpleOrder.iff_eq_zero_or_injective B|>.1 hB (B := A) f
    refine H.resolve_left fun rid => ?_
    rw [eq_top_iff, TwoSidedIdeal.le_iff] at rid
    specialize @rid 1 ⟨⟩
    simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, TwoSidedIdeal.mem_ker, _root_.map_one,
        one_ne_zero] at rid )

omit hB in
lemma iso_fg [hB1 : IsSimpleOrder (TwoSidedIdeal B)]:
  Nonempty $ module_inst K A B M f ≃ₗ[B ⊗[K] (Module.End A M)] module_inst K A B M g := by
  haveI := findimB K A B M f g
  haveI := hA.2
  rw [linearEquiv_iff_finrank_eq_over_simple_ring K]
  rfl
-- -- lemma SkolemNoether_aux (A : Type u) [Ring A] [Algebra K A]
-- --   (M : Type u) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
-- --   (B : Type u) [Ring B] [Algebra K B] [Module B M] [IsScalarTower K B M]
-- --   [IsSimpleModule A M] [IsSimpleModule (B ⊗[K] (Aᵐᵒᵖ )) M] :
-- --   ∃ (φ : M →ₗ[A] M), function.surjective φ := sorry
-- -- variable (A: Type u ) [Ring A] [Algebra K A] [FiniteDimensional K A]:
/--
End_End_A
-/
theorem SkolemNoether (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] [Ring B]
    [Algebra K B] [hB : IsSimpleOrder (TwoSidedIdeal B)] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f g : B →ₐ[K] A):
    ∃(x : Aˣ), ∀(b : B), g b = x * f b * x⁻¹ := by
  obtain ⟨φ⟩ := iso_fg K A B M f g
  have := hA.2
  let ISO := end_end_iso K A M
  let Φ : Module.End (Module.End A M) M :=
    { toFun := fun m => φ m
      map_add' := by simp
      map_smul' := by
        intro F m
        simp only [LinearMap.smul_def, RingHom.id_apply]
        have : F m = smul1 K A B M f m (1 ⊗ₜ F) := by
          simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
            AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
            TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul]
        rw [this]
        erw [φ.map_smul]
        change smul1 K A B M _ _ (1 ⊗ₜ F) = _
        simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
          AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
          TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul] }
  let Ψ : Module.End (Module.End A M) M :=
    { toFun := fun m => φ.symm m
      map_add' := by simp
      map_smul' := by
        intro F m
        simp only [LinearMap.smul_def, RingHom.id_apply]
        have : F m = smul1 K A B M g m (1 ⊗ₜ F) := by
          simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
            AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
            TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul]
        rw [this]
        have := φ.symm.map_smul (1 ⊗ₜ F) m
        change φ.symm (smul1 K A B M _ _ _) = _ at this
        rw [this]
        change  smul1 K A B M _ _ (1 ⊗ₜ F) = _
        simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
          AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
          TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul] }

  let a := ISO.symm Φ
  let b := ISO.symm Ψ
  refine ⟨⟨a, b, (by
    apply_fun ISO using AlgEquiv.injective _
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_one, a, b]
    ext m
    simp only [LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      LinearMap.one_apply, Φ, Ψ]), (by
    apply_fun ISO using AlgEquiv.injective _
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_one, b, a]
    ext m
    simp only [LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply,
      LinearMap.one_apply, Ψ, Φ])⟩, ?_⟩
  intro x
  simp only [Units.inv_mk, a, b]
  apply_fun ISO using AlgEquiv.injective _
  simp only [end_end_iso, AlgEquiv.coe_ofBijective, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, map_mul, AlgEquiv.apply_symm_apply, ISO, Φ, Ψ]
  ext m
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply]
  have := φ.map_smul (x ⊗ₜ LinearMap.id) (φ.symm m)
  change φ (smul1 K A B M _ _ (x ⊗ₜ LinearMap.id)) = _ at this
  simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, LinearMap.id_coe, id_eq] at this
  rw [this]
  simp only [LinearEquiv.apply_symm_apply]
  change _ = smul1 K A B M _ _ (x ⊗ₜ LinearMap.id)
  simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, LinearMap.id_coe, id_eq]

theorem SkolemNoether' (K A B : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [hA : IsCentralSimple K A] [Ring B]
    [Algebra K B] [hB : IsSimpleOrder (TwoSidedIdeal B)] (f g : B →ₐ[K] A):
    ∃(x : Aˣ), ∀(b : B), g b = x * f b * x⁻¹ := by
  have := hA.2
  obtain ⟨n, hn, S, _, _, ⟨e⟩⟩ := Wedderburn_Artin_algebra_version K A
  haveI : NeZero n := ⟨hn⟩
  letI := Module.compHom (Fin n → S) e.toRingEquiv.toRingHom
  have : IsSimpleModule A (Fin n → S) := simple_mod_of_wedderburn K A n S e
  haveI : IsScalarTower K A (Fin n → S) := by
    constructor
    intro a b c
    ext i
    simp only [Pi.smul_apply]
    change ∑ _, _ = a • ∑ _, _
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, ZeroHom.coe_mk, map_smul,
      Matrix.smul_apply, smul_eq_mul, Algebra.smul_mul_assoc, Finset.smul_sum]

  exact SkolemNoether K A B (Fin n → S) f g
