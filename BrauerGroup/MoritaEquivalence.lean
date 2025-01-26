import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.SimpleModule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

open Matrix

open CategoryTheory BigOperators

universe u u' u'' v v' v'' w

local notation "M[" ι "," R "]" => Matrix ι ι R

variable (R : Type u) [Ring R]

variable (ι : Type w) [Fintype ι] [Inhabited ι] [DecidableEq ι]

instance (M : Type*) [AddCommGroup M] [Module R M] : Module M[ι, R] (ι → M) where
  smul N v i := ∑ j : ι, N i j • v j
  one_smul v := funext fun i => show ∑ _, _ = _ by simp [one_apply]
  mul_smul N₁ N₂ v := funext fun i => show ∑ _, _ = ∑ _, _ • (∑ _, _) by
    simp_rw [mul_apply, Finset.smul_sum, Finset.sum_smul, MulAction.mul_smul]
    rw [Finset.sum_comm]
  smul_zero v := funext fun i => show ∑ _, _ = _ by simp
  smul_add N v₁ v₂ := funext fun i => show ∑ j : ι, N i j • (v₁ + v₂) j = (∑ _, _) + (∑ _, _) by
    simp [Finset.sum_add_distrib]
  add_smul N₁ N₂ v := funext fun i => show ∑ j : ι, (N₁ + N₂) i j • v j = (∑ _, _) + (∑ _, _) by
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i => show ∑ _, _ = _ by simp

omit [Inhabited ι] in
lemma matrix_smul_vec_def {M : Type*} [AddCommGroup M] [Module R M] (N : M[ι, R]) (v : ι → M) :
    N • v = fun i => ∑ j : ι, N i j • v j := rfl

omit [Inhabited ι] in
lemma matrix_smul_vec_def' {M : Type*} [AddCommGroup M] [Module R M] (N : M[ι, R]) (v : ι → M) :
    N • v = ∑ j : ι, fun i => N i j • v j := by
  rw [matrix_smul_vec_def]
  ext
  simp

omit [Inhabited ι] in
lemma matrix_smul_vec_apply {M : Type*} [AddCommGroup M] [Module R M] (N : M[ι, R]) (v : ι → M)
    (i : ι) :
    (N • v) i = ∑ j : ι, N i j • v j := rfl

@[simps]
def toModuleCatOverMatrix : ModuleCat R ⥤ ModuleCat M[ι, R] where
  obj M := ModuleCat.of M[ι, R] (ι → M)
  map f := ModuleCat.ofHom {
    toFun := fun v i => f <| v i
    map_add' := fun x y => funext fun i => show f (x i + y i) = f (x i) + f (y i) from
      f.hom.map_add _ _
    map_smul' := fun m v => funext fun i => show f (∑ _, _) = ∑ _, _ by
      simp only [RingHom.id_apply, map_sum, _root_.map_smul] }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simps]
def fromModuleCatOverMatrix.α [Inhabited ι] (M : Type*) [AddCommGroup M] [Module M[ι, R] M] :
    AddSubgroup M where
  carrier := Set.range ((stdBasisMatrix (default : ι) (default : ι) (1 : R) : M[ι, R]) • ·)
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨-m, by simp⟩

open fromModuleCatOverMatrix

instance fromModuleCatOverMatrix.module_α (M : Type*) [AddCommGroup M] [Module M[ι, R] M] :
    Module R <| α R ι M where
  smul a x := ⟨(stdBasisMatrix default default a : M[ι, R]) • x.1, by
    obtain ⟨y, hy⟩ := x.2
    simp only [α, AddSubgroup.mem_mk, Set.mem_range]
    refine ⟨(stdBasisMatrix default default a : M[ι, R]) • y, hy ▸ ?_⟩
    simp only
    rw [← MulAction.mul_smul, ← MulAction.mul_smul]
    congr 1
    ext i j
    simp⟩
  one_smul := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • _
    rw [← MulAction.mul_smul]
    congr 1
    ext i j
    simp
  mul_smul := by
    rintro a a' ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • (stdBasisMatrix _ _ _ • _)
    dsimp only [id_eq, eq_mpr_eq_cast, cast_eq]
    rw [← MulAction.mul_smul, ← MulAction.mul_smul, ← MulAction.mul_smul]
    congr 1
    ext i j
    simp
  smul_zero a := by
    ext
    change stdBasisMatrix _ _ _ • 0 = 0
    simp
  smul_add := by
    rintro a ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • _ + stdBasisMatrix _ _ _ • _
    dsimp only [AddSubgroup.coe_add]
    rw [← MulAction.mul_smul, ← MulAction.mul_smul, ← smul_add, ← smul_add, ← MulAction.mul_smul]
  add_smul := by
    rintro a b ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = stdBasisMatrix _ _ _ • _ + stdBasisMatrix _ _ _ • _
    dsimp only
    rw [← MulAction.mul_smul, ← MulAction.mul_smul, ← MulAction.mul_smul, ← add_smul,
      ← add_mul, ← stdBasisMatrix_add]
  zero_smul := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    ext
    change stdBasisMatrix _ _ _ • _ = _
    simp only [stdBasisMatrix_zero, zero_smul, ZeroMemClass.coe_zero]

@[simp]
lemma fromModuleCatOverMatrix.smul_α_coe {M : Type*} [AddCommGroup M] [Module M[ι, R] M]
    (x : R) (y : α R ι M) : ((x • y : α R ι M) : M) =
    (stdBasisMatrix default default x : M[ι, R]) • y.1 := rfl

open fromModuleCatOverMatrix

set_option maxHeartbeats 400000 in
@[simps]
def fromModuleCatOverMatrix : ModuleCat M[ι, R] ⥤ ModuleCat R where
  obj M := .of _ $ α R ι M
  map f := ModuleCat.ofHom {
    toFun := fun x => ⟨f x.1, by
      simp only [α, AddSubgroup.coe_set_mk, AddSubgroup.mem_mk, Set.mem_range]
      obtain ⟨y, hy⟩ := x.2
      refine ⟨f y, ?_⟩
      simp only at hy
      rw [← hy, f.hom.map_smul]⟩
    map_add' := by
      rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
      refine Subtype.ext ?_
      show f ((stdBasisMatrix _ _ _ • x) + (stdBasisMatrix _ _ _ • y)) =
        f (stdBasisMatrix _ _ _ • x) + f (stdBasisMatrix _ _ _ • y)
      rw [map_add]
    map_smul' := by
      rintro r ⟨_, ⟨x, rfl⟩⟩
      simp only [RingHom.id_apply, LinearMapClass.map_smul]
      refine Subtype.ext ?_
      show f (_ • _) = _ • (_ • f _)
      simp only [LinearMapClass.map_smul] }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simps]
def matrix.unitIsoHom :
    toModuleCatOverMatrix R ι ⋙ fromModuleCatOverMatrix R ι ⟶
    𝟭 (ModuleCat R) where
  app X := ModuleCat.ofHom
    { toFun := fun x => ∑ i : ι, x.1 i
      map_add' := by
        rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
        simp only [toModuleCatOverMatrix_obj_carrier, AddSubmonoid.coe_add,
          ← Finset.sum_add_distrib]; rfl
      map_smul' := by
        rintro r ⟨_, ⟨x, rfl⟩⟩
        simp only [Functor.id_obj, toModuleCatOverMatrix_obj_carrier, Functor.comp_obj,
          fromModuleCatOverMatrix_obj_carrier, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [fromModuleCatOverMatrix.smul_α_coe, Subtype.coe_mk, ← MulAction.mul_smul]
        change ∑ _, _ = r • ∑ _, _
        simp only [StdBasisMatrix.mul_same, mul_one]
        simp only [stdBasisMatrix, of_apply, ite_smul, zero_smul, one_smul, Finset.smul_sum,
          smul_ite, smul_zero]}
  naturality {X Y} f := by
    simp only [Functor.comp_obj, toModuleCatOverMatrix_obj_carrier,
      fromModuleCatOverMatrix_obj_carrier, Functor.id_obj, Functor.comp_map, Functor.id_map]
    ext ⟨_, ⟨x, rfl⟩⟩
    change ∑ _, _ = f _
    simp only [fromModuleCatOverMatrix_map_hom_apply_coe, LinearMapClass.map_smul, Functor.comp_obj,
      toModuleCatOverMatrix_obj_carrier, fromModuleCatOverMatrix_obj_carrier,
      Functor.id_obj, Function.comp_apply]
    change _ = f (∑ i : ι, ∑ _, _)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [fromModuleCatOverMatrix_map_hom_apply_coe, toModuleCatOverMatrix_map_hom_apply]
    change f.hom (∑ _, _) = _
    rw [map_sum]

set_option maxHeartbeats 600000 in
@[simps]
def matrix.unitIsoInv :
    𝟭 (ModuleCat R) ⟶
    toModuleCatOverMatrix R ι ⋙ fromModuleCatOverMatrix R ι  where
  app X := ModuleCat.ofHom
    { toFun := fun x => (⟨Function.update (0 : ι → X) default x, by
        simp only [α, AddSubgroup.mem_mk, Set.mem_range]
        refine ⟨fun _ => x, ?_⟩
        refine funext fun i => ?_
        change ∑ _, _ = _
        simp only [stdBasisMatrix, of_apply, ite_smul, one_smul, zero_smul, Function.update,
          eq_rec_constant, Pi.zero_apply, dite_eq_ite]
        split_ifs with h
        · subst h
          simp only [true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · apply Finset.sum_eq_zero
          intro j _
          rw [if_neg]
          tauto ⟩ : α R ι (ι → X))
      map_add' := by
        rintro (x : X) (y : X)
        simp only [Functor.comp_obj, toModuleCatOverMatrix_obj_carrier,
          fromModuleCatOverMatrix_obj_carrier, Functor.id_obj]
        refine Subtype.ext $ funext fun i => ?_
        simp only [toModuleCatOverMatrix_obj_carrier]
        change _ =
          (Function.update (0 : ι → X) default x + Function.update (0 : ι → X) default y) i
        rw [← Function.update_add, zero_add]
      map_smul' := by
        rintro r (x : X)
        simp only [Functor.comp_obj, toModuleCatOverMatrix_obj_carrier,
          fromModuleCatOverMatrix_obj_carrier, Functor.id_obj, RingHom.id_apply]
        refine Subtype.ext $ funext fun i => ?_
        simp only [toModuleCatOverMatrix_obj_carrier]
        change _ = ∑ _, stdBasisMatrix default default r i _ • _
        simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, smul_ite,
          smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        split_ifs with h
        · subst h
          simp only [StdBasisMatrix.apply_same]
        · rw [StdBasisMatrix.apply_of_row_ne, zero_smul]
          exact Ne.symm h }
  naturality {X Y} f := by
    simp only [Functor.id_obj, Functor.comp_obj, toModuleCatOverMatrix_obj_carrier,
      fromModuleCatOverMatrix_obj_carrier, Functor.id_map, Functor.comp_map]
    ext x
    refine Subtype.ext $ funext fun i => ?_
    simp only [Functor.id_obj, Functor.comp_obj, toModuleCatOverMatrix_obj_carrier,
      fromModuleCatOverMatrix_obj_carrier, Function.comp_apply]
    erw [LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, fromModuleCatOverMatrix_map_hom_apply_coe,
      toModuleCatOverMatrix_map_hom_apply]
    change Function.update (0 : ι → Y) default (f x) i =
      f (Function.update (0 : ι → X) default x i)

    simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite]
    split_ifs with h
    · rfl
    · rw [map_zero]

@[simps]
def matrix.unitIso :
    toModuleCatOverMatrix R ι ⋙ fromModuleCatOverMatrix R ι ≅
    𝟭 (ModuleCat R) where
  hom := matrix.unitIsoHom R ι
  inv := matrix.unitIsoInv R ι
  hom_inv_id := by
    ext X ⟨_, ⟨x, rfl⟩⟩
    simp only [Functor.comp_obj, toModuleCatOverMatrix_obj_carrier,
      fromModuleCatOverMatrix_obj_carrier, NatTrans.comp_app, Functor.id_obj,
      Function.comp_apply, NatTrans.id_app, ModuleCat.id_apply]
    refine Subtype.ext $ funext fun i => ?_
    simp only [toModuleCatOverMatrix_obj_isAddCommGroup, toModuleCatOverMatrix_obj_isModule,
      fromModuleCatOverMatrix_obj_isAddCommGroup, toModuleCatOverMatrix_obj_carrier,
      fromModuleCatOverMatrix_obj_isModule, ModuleCat.hom_comp, fromModuleCatOverMatrix_obj_carrier,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    erw [matrix.unitIsoInv_app_hom_apply_coe]
    change _ = ∑ _, _
    erw [matrix.unitIsoHom_app_hom_apply]
    simp only [Function.update, Functor.id_obj, eq_rec_constant, Pi.zero_apply, dite_eq_ite]
    split_ifs with h
    · refine Finset.sum_congr rfl fun i _ => ?_
      change ∑ _, _ = _
      subst h
      simp only [stdBasisMatrix, of_apply, ite_smul, one_smul, zero_smul, true_and]
      split_ifs with h
      · subst h
        simp only [true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      · apply Finset.sum_eq_zero
        intro j _
        rw [if_neg]
        tauto
    · symm
      apply Finset.sum_eq_zero
      intro j _
      dsimp only [stdBasisMatrix, of_apply]
      rw [if_neg, zero_smul]
      tauto
  inv_hom_id := by
    ext X (x : X)
    simp only [Functor.id_obj, NatTrans.comp_app, Functor.comp_obj,
      toModuleCatOverMatrix_obj_carrier, fromModuleCatOverMatrix_obj_carrier,
      Function.comp_apply, NatTrans.id_app, ModuleCat.id_apply]
    erw [matrix.unitIsoHom_app_hom_apply]
    change (∑ i : ι, Function.update (0 : ι → X) default x i) = x
    simp [Function.update]


@[simps!]
noncomputable def matrix.counitIsoHomMap (M : ModuleCat M[ι, R]) :
    M ≅ (fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι).obj M :=
  LinearEquiv.toModuleIso $ LinearEquiv.ofBijective
    ({toFun := fun m i => ⟨(stdBasisMatrix default i 1 : M[ι, R]) • m, by
        simp only [α, AddSubgroup.mem_mk, Set.mem_range]
        refine ⟨(stdBasisMatrix default i 1 : M[ι, R]) • m, ?_⟩
        simp only [← MulAction.mul_smul, StdBasisMatrix.mul_same, mul_one]⟩
      map_add' := fun x y => funext fun i => Subtype.ext $
        show (stdBasisMatrix default i 1 : M[ι, R]) • (x + y) =
          (stdBasisMatrix default i 1 : M[ι, R]) • x +
          (stdBasisMatrix default i 1 : M[ι, R]) • y from smul_add _ _ _
      map_smul' := fun x m => funext fun i => Subtype.ext $ by
        simp only [RingHom.id_apply]
        change _ = Subtype.val (∑ _, _)
        simp only [AddSubmonoidClass.coe_finset_sum, smul_α_coe]

        simp_rw [← MulAction.mul_smul, StdBasisMatrix.mul_same, mul_one, ← Finset.sum_smul]
        congr 2
        conv_lhs => rw [Matrix.matrix_eq_sum_stdBasisMatrix x]
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_eq_single_of_mem (a := i)]
        pick_goal 2
        · exact Finset.mem_univ i

        pick_goal 2
        · intro j _ hj
          apply Finset.sum_eq_zero
          intro k _
          rw [StdBasisMatrix.mul_of_ne]
          exact hj.symm
        simp_rw [StdBasisMatrix.mul_same, one_mul] } : M →ₗ[M[ι, R]] ι → (α R ι ↑M))
    ⟨by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      rintro x (hx : _ = 0)
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at hx
      rw [show x = ∑ i : ι, (stdBasisMatrix i i 1 : M[ι, R]) • x by
        rw [← Finset.sum_smul, show ∑ i : ι, (stdBasisMatrix i i 1 : M[ι, R]) = 1 by
          ext
          simp only [sum_apply, stdBasisMatrix, one_apply]
          split_ifs with h
          · subst h
            simp only [of_apply, and_self, Finset.sum_ite_eq', Finset.mem_univ,
              ↓reduceIte]
          · apply Finset.sum_eq_zero
            intro k _
            simp_all only [Finset.mem_univ, of_apply, ite_eq_right_iff, isEmpty_Prop, not_and, not_false_eq_true,
              implies_true, IsEmpty.forall_iff]]; rw [one_smul]]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [show (stdBasisMatrix i i 1 : M[ι, R]) =
        stdBasisMatrix i default 1 * stdBasisMatrix default i 1
        by rw [StdBasisMatrix.mul_same, one_mul], MulAction.mul_smul]
      refine Submodule.smul_mem _ _ ?_
      rw [show _ • x = 0 from Subtype.ext_iff.1 $ congr_fun hx i]
      rfl, fun v => by
      refine ⟨∑ k : ι, (stdBasisMatrix k default 1 : M[ι, R]) • (v k), ?_⟩
      simp only [map_sum, _root_.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
      conv_rhs => rw [show v = ∑ k : ι, Function.update (0 : ι → (α R ι M)) k (v k) by
        ext i
        simp only [Finset.sum_apply, Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext j
      by_cases hij : i = j
      · subst hij
        change Subtype.val (∑ _, _) = _
        simp only [AddSubmonoidClass.coe_finset_sum, smul_α_coe, Function.update_self]
        simp_rw [← MulAction.mul_smul, StdBasisMatrix.mul_same, mul_one]
        rw [Finset.sum_eq_single_of_mem (a := default), StdBasisMatrix.apply_same]
        pick_goal 2
        · exact Finset.mem_univ _
        pick_goal 2
        · intro j _ hj
          simp only [stdBasisMatrix, of_apply, true_and]
          rw [if_neg]
          simp only [ite_self]
          rw [show (Matrix.of fun i' j' ↦ 0) = (0 : Matrix ι ι R) by rfl, zero_smul]
          exact hj.symm
        obtain ⟨y, hy⟩ := (v i).2
        rw [← hy]
        simp only [← MulAction.mul_smul, StdBasisMatrix.mul_same, mul_one]
      · rw [Function.update_of_ne]
        pick_goal 2
        · exact Ne.symm hij
        change Subtype.val (∑ _, _) = 0
        simp only [AddSubmonoidClass.coe_finset_sum, smul_α_coe]
        apply Finset.sum_eq_zero
        intro k _
        rw [StdBasisMatrix.apply_of_ne, stdBasisMatrix_zero, zero_smul]
        tauto⟩

@[simps]
noncomputable def matrix.counitIsoHom :
    fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι ⟶ 𝟭 (ModuleCat M[ι, R]) where
  app M := (matrix.counitIsoHomMap R ι M).inv
  naturality X Y f := by
    simp only [Functor.comp_obj, fromModuleCatOverMatrix_obj_carrier,
      toModuleCatOverMatrix_obj_carrier, Functor.id_obj, Functor.comp_map, Functor.id_map]
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    ext x
    simp only [toModuleCatOverMatrix_obj_carrier, fromModuleCatOverMatrix_obj_carrier,
      toModuleCatOverMatrix_obj_isAddCommGroup, fromModuleCatOverMatrix_obj_isAddCommGroup,
      toModuleCatOverMatrix_obj_isModule, fromModuleCatOverMatrix_obj_isModule, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply]
    refine funext fun i => ?_
    erw [toModuleCatOverMatrix_map_hom_apply]
    refine Subtype.ext ?_
    erw [fromModuleCatOverMatrix_map_hom_apply_coe]
    change _ = _ • _
    rw [← f.hom.map_smul]
    rfl

@[simps]
noncomputable def matrix.counitIsoInv :
    𝟭 (ModuleCat M[ι, R]) ⟶
    fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι where
  app M := (matrix.counitIsoHomMap R ι M).hom
  naturality X Y f := by
    simp only [Functor.id_obj, Functor.comp_obj, fromModuleCatOverMatrix_obj_carrier,
      toModuleCatOverMatrix_obj_carrier, Functor.id_map, Functor.comp_map]
    ext x
    simp only [Functor.comp_obj, fromModuleCatOverMatrix_obj_carrier,
      toModuleCatOverMatrix_obj_carrier, Function.comp_apply]
    refine funext fun i => Subtype.ext ?_
    erw [counitIsoHomMap_hom_hom_apply_coe, fromModuleCatOverMatrix_map_hom_apply_coe,
      counitIsoHomMap_hom_hom_apply_coe]
    rw [f.hom.map_smul]

@[simps]
noncomputable def matrix.counitIso :
    fromModuleCatOverMatrix R ι ⋙ toModuleCatOverMatrix R ι ≅ 𝟭 (ModuleCat M[ι, R]) where
  hom := matrix.counitIsoHom R ι
  inv := matrix.counitIsoInv R ι
  hom_inv_id := by ext X x; simp
  inv_hom_id := by ext; simp


@[simps]
noncomputable def moritaEquivalentToMatrix : ModuleCat R ≌ ModuleCat M[ι, R] where
  functor := toModuleCatOverMatrix R ι
  inverse := fromModuleCatOverMatrix R ι
  unitIso := matrix.unitIso R ι |>.symm
  counitIso := matrix.counitIso R ι
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, toModuleCatOverMatrix_obj_carrier, Functor.comp_obj,
      fromModuleCatOverMatrix_obj_carrier, Iso.symm_hom, matrix.unitIso_inv, matrix.counitIso_hom]
    ext (x : ι → X)
    simp only [matrix.counitIsoHom_app, Functor.comp_obj, fromModuleCatOverMatrix_obj_carrier,
      toModuleCatOverMatrix_obj_carrier, Function.comp_apply, ModuleCat.id_apply]
    apply_fun (matrix.counitIsoHomMap R ι _).hom using LinearEquiv.injective _
    erw [Iso.inv_hom_id_apply (matrix.counitIsoHomMap R ι _)]
    simp only [Functor.comp_obj, fromModuleCatOverMatrix_obj_carrier,
      toModuleCatOverMatrix_obj_carrier]
    refine funext fun i => Subtype.ext ?_
    erw [matrix.counitIsoHomMap_hom_hom_apply_coe, toModuleCatOverMatrix_map_hom_apply]
    refine funext fun j => ?_
    erw [matrix.unitIsoInv_app_hom_apply_coe]
    change _ = ∑ _, _
    simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, stdBasisMatrix,
      ite_smul, one_smul, zero_smul]
    split_ifs with h
    · subst h; simp
    · refine Eq.symm $ Finset.sum_eq_zero fun k _ => ?_
      simp only [of_apply, ite_smul, one_smul, zero_smul, ite_eq_right_iff, and_imp]
      tauto

namespace IsMoritaEquivalent
namespace division_ring -- auxilaries for division rings, don't use

variable (R : Type u) (S : Type u) [DivisionRing R] [DivisionRing S]
variable (e : ModuleCat.{u} R ≌ ModuleCat.{u} S)


-- This is a lemma on purpose, **don't** attempt to look at its definition
lemma division_ring_exists_unique_isSimpleModule
    (S : Type u) [DivisionRing S] (N : Type*) [AddCommGroup N] [Module S N] [IsSimpleModule S N] :
    Nonempty (N ≃ₗ[S] S) := by
  have inst4 := IsSimpleModule.nontrivial S N
  have H := Module.Free.of_divisionRing S N
  rw [Module.free_iff_set] at H
  obtain ⟨s, ⟨b⟩⟩ := H
  if hs1 : s = ∅
  then
    subst hs1
    have := b.index_nonempty
    simp only [nonempty_subtype, Set.mem_empty_iff_false, exists_const] at this
  else
    obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hs1
    have eq0 := IsSimpleOrder.eq_bot_or_eq_top (Submodule.span S {b ⟨i, hi⟩}) |>.resolve_left (by
      intro h
      simp only [Submodule.span_singleton_eq_bot] at h
      exact b.ne_zero ⟨i, hi⟩ h)
    have eq : s = {i} := by
      refine le_antisymm ?_ (by simpa)
      simp only [Set.le_eq_subset, Set.subset_singleton_iff]
      intro j hj
      have mem : b ⟨j, hj⟩ ∈ Submodule.span S {b ⟨i, hi⟩} := eq0 ▸ ⟨⟩
      rw [Submodule.mem_span_singleton] at mem
      obtain ⟨r, hr⟩ := mem
      have hr' := congr(b.repr $hr)
      simp only [LinearMapClass.map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
        mul_one] at hr'
      by_contra rid
      have hr' := congr($hr' ⟨i, hi⟩)
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (h := by simpa)] at hr'
      subst hr'
      simp only [zero_smul] at hr
      exact b.ne_zero _ hr.symm |>.elim

    subst eq
    refine ⟨b.repr ≪≫ₗ LinearEquiv.ofBijective ⟨⟨fun x => x ⟨i, by simp⟩, ?_⟩, ?_⟩ ⟨?_, ?_⟩⟩
    · intro x y; simp
    · intro x y; simp
    · intro x y hxy; ext; simpa using hxy
    · intro x; exact ⟨Finsupp.single ⟨i, by simp⟩ x, by simp⟩

instance : e.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

lemma isSimpleModule_iff_injective_or_eq_zero
    (R : Type u) [Ring R] (M : ModuleCat R) :
    IsSimpleModule R M ↔
    (Nontrivial M ∧ ∀ (N : ModuleCat R) (f : M ⟶ N), f = 0 ∨ Function.Injective f) := by
  constructor
  · intros inst1
    constructor
    · have := inst1.1
      rwa [Submodule.nontrivial_iff] at this
    · intro N f
      refine inst1.2 (LinearMap.ker f.hom) |>.elim
        (fun h => Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) <|
        fun h => Or.inl <| by
          simp only [LinearMap.ker_eq_top] at h
          ext : 1
          rw [h]; simp
  · rintro ⟨inst1, h⟩
    refine ⟨fun p => ?_⟩
    refine h (.of R (M ⧸ p)) (ModuleCat.ofHom (Submodule.mkQ p)) |>.elim (fun h => Or.inr ?_) <|
      fun h => Or.inl $ eq_bot_iff.2 fun x hx => h ?_
    · rw [ModuleCat.hom_ext_iff] at h
      simp only [ModuleCat.of_coe, ModuleCat.hom_zero] at h
      rw [← Submodule.ker_mkQ p, LinearMap.ker_eq_top, h]
    · rw [map_zero]
      exact Submodule.Quotient.mk_eq_zero _ |>.2 hx

open ZeroObject

variable {R S} in
instance _root_.CategoryTheory.Equivalence.nontrivial
    {R S : Type u} [Ring R] [Ring S] (e : ModuleCat.{v} R ≌ ModuleCat.{v} S)
    (M : ModuleCat.{v} R) [h : Nontrivial M] : Nontrivial (e.functor.obj M) := by
  obtain ⟨m, n, h⟩ := h
  by_contra inst1
  rw [not_nontrivial_iff_subsingleton] at inst1
  let iso1 : e.functor.obj M ≅ 0 :=
  { hom := ModuleCat.ofHom ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
    inv := ModuleCat.ofHom ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
    hom_inv_id := by ext; exact Subsingleton.elim _ _
    inv_hom_id := by ext; simp only [Function.comp_apply, Limits.id_zero]; rfl }
  let iso2 : M ≅ 0 := calc M
      _ ≅ e.inverse.obj (e.functor.obj M) := e.unitIso.app M
      _ ≅ e.inverse.obj 0 := e.inverse.mapIso iso1
      _ ≅ 0 := e.inverse.mapZeroObject
  let iso3 : (0 : ModuleCat R) ≅ ModuleCat.of.{v, u} R PUnit.{v + 1} :=
  { hom := ModuleCat.ofHom ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
    inv := ModuleCat.ofHom ⟨⟨fun _ => 0, by intros; simp⟩, by intros; simp⟩
    hom_inv_id := by ext; simp only [Function.comp_apply, Limits.id_zero]; rfl
    inv_hom_id := rfl }
  -- have := iso3.toLinearEquiv.injective (by
  --   have : ∀ x y : ModuleCat.of R PUnit.{1}, x = y := fun x y ↦ by
  --     exact rfl
  --   exact this m n
  --   )
  refine h <| LinearEquiv.injective iso2.toLinearEquiv <|
    iso3.toLinearEquiv.injective <| Subsingleton.elim _ _

variable (K : Type u) [Field K]


lemma IsSimpleModule.functor
    (R S : Type u) [Ring R] [Ring S] (e : ModuleCat.{v} R ≌ ModuleCat.{v} S)
    (M : ModuleCat.{v} R) [simple_module : IsSimpleModule R M] : IsSimpleModule S (e.functor.obj M) := by
  rw [isSimpleModule_iff_injective_or_eq_zero] at simple_module ⊢
  rcases simple_module with ⟨nontriv, H⟩
  refine ⟨e.nontrivial (h := nontriv), fun N f => ?_⟩
  let F := e.unit.app M ≫ e.inverse.map f
  rcases H _ F with H|H
  · simp only [Functor.id_obj, Functor.comp_obj, Preadditive.IsIso.comp_left_eq_zero, F] at H
    replace H : e.inverse.map f = e.inverse.map 0 := by simpa using H
    exact Or.inl $ e.inverse.map_injective H
  · simp only [Functor.id_obj, Functor.comp_obj, F] at H
    refine Or.inr ?_
    rw [← ModuleCat.mono_iff_injective] at H ⊢
    have m1 : Mono (e.functor.map $ e.unit.app M ≫ e.inverse.map f) := e.functor.map_mono _
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, Equivalence.fun_inv_map,
      Equivalence.functor_unit_comp_assoc] at m1
    exact mono_of_mono f (e.counitInv.app N)

end division_ring

end IsMoritaEquivalent
