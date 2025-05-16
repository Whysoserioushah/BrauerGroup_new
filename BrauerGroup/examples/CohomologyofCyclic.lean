import BrauerGroup.IsoSecond
import BrauerGroup.examples.ShortComplex.LeftHomologyMapData

universe u

suppress_compilation

open CategoryTheory

variable (n : ℕ) (G k : Type)  (σ : G) [Fintype G] [CommRing k]

abbrev N [Group G] : Rep.ofMulAction k G G ⟶ Rep.ofMulAction k G G where
  hom := ModuleCat.ofHom ((Representation.ofMulAction k G G).asAlgebraHom (∑ i : G, .single i 1))
  comm g := by
    ext g1 :3
    dsimp [ModuleCat.endRingEquiv]
    rw [← Representation.asAlgebraHom_single_one, ← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    rw [← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp
    -- Note: Add `MonoidAlgebra.finset_sum_apply`
    rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
    simp

-- lemma N_IsIso [Group G] : IsIso (N G k) := ⟨⟨{
--   hom := ModuleCat.ofHom _
--   comm := _
-- }, sorry⟩⟩

abbrev sigmaminus1 [CommGroup G]: Rep.ofMulAction k G G ⟶ Rep.ofMulAction k G G where
  hom := ModuleCat.ofHom ((Representation.ofMulAction k G G).asAlgebraHom (.single σ 1 - 1))
  comm g := by
    ext g1 :3
    dsimp [ModuleCat.endRingEquiv]
    rw [← Representation.asAlgebraHom_single_one, ← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    rw [← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp [mul_comm]
    -- Note: Add `MonoidAlgebra.finset_sum_apply`
    -- rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]

def ChainComplexAbel [CommGroup G] : ChainComplex (Rep k G) ℕ where
  X _ := Rep.ofMulAction k G G
  d i j := if j + 1 = i then if Even i then N G k else sigmaminus1 G k σ else 0
  shape := by simp +contextual
  d_comp_d' i j k1 := by
    rintro rfl rfl
    simp only [↓reduceIte, Nat.even_add_one, ite_not, Nat.not_odd_iff_even]
    split_ifs
    · ext : 2
      simp only [Action.comp_hom, one_smul,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, Action.zero_hom, ModuleCat.hom_zero]
      rw [← LinearMap.mul_eq_comp, ← map_mul]
      suffices ((MonoidAlgebra.single σ 1 - (1 : MonoidAlgebra k G)) * ∑ i : G, MonoidAlgebra.single i 1) = 0 by
        rw [this, map_zero]
      rw [sub_mul, sub_eq_zero]
      ext
      simp
      rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
      simp
    · ext : 2
      simp only [Action.comp_hom, one_smul,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, Action.zero_hom, ModuleCat.hom_zero]
      rw [← LinearMap.mul_eq_comp, ← map_mul]
      suffices ((∑ i : G, MonoidAlgebra.single i 1 ) * (MonoidAlgebra.single σ 1 - (1 : MonoidAlgebra k G))) = 0 by
        rw [this, map_zero]
      rw [mul_sub, sub_eq_zero]
      ext
      simp
      rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
      simp

abbrev π_aux [CommGroup G]: Action.Hom ((ChainComplexAbel G k σ).X Nat.zero)
    (((ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k)).X Nat.zero) where
  hom := ModuleCat.ofHom (Finsupp.lsum ℕ 1 : _ →ₗ[k] k)
  comm g := by
    ext x
    simp only [Nat.zero_eq, ChainComplex.single₀_obj_zero, ChainComplexAbel, ModuleCat.endRingEquiv,
      RingEquiv.symm_mk, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp,
      MonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Representation.isTrivial_def,
      ModuleCat.ofHom_id, Category.comp_id]
    erw [Finsupp.lsum_apply, Finsupp.lsum_apply]
    induction x using MonoidAlgebra.induction_on with
    | hM a =>
      simp
    | hadd f g _ _ =>
      classical
      simp
      rw [Finsupp.sum_add_index (by simp) (by simp),
        Finsupp.sum_add_index (by simp) (by simp)]
      simp_all
    | hsmul r f _ =>
      simp_all [MonoidAlgebra, Finsupp.sum_smul_index, ← Finsupp.mul_sum]
      congr 1

def CyclicCoh.π [CommGroup G] : (ChainComplexAbel G k σ) ⟶
    ((ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k)) where
  f ii := ii.casesOn (π_aux G k σ) fun _ ↦ 0
  comm' i j := by
    rintro rfl
    cases j
    pick_goal 2
    simp
    simp [ChainComplexAbel, ModuleCat.endRingEquiv]
    ext g
    simp only [Action.zero_hom, ModuleCat.hom_zero, LinearMap.zero_comp, LinearMap.zero_apply,
      Action.comp_hom, map_sub, Representation.asAlgebraHom_single, one_smul, map_one,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Pi.one_apply,
      Function.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
      Representation.ofMulAction_single, smul_eq_mul, LinearMap.one_apply]
    erw [Finsupp.lsum_single, Finsupp.lsum_single]
    simp

def CyclicCoh.homotopy_aux [CommGroup G]: Action.Hom (Rep.trivial k G k)
    ((ChainComplexAbel G k σ).X 0) where
  hom := ModuleCat.ofHom {
      toFun kk := Finsupp.linearEquivFunOnFinite k k G|>.symm <| Function.const G kk
      map_add' k1 k2 := by simp [← map_add]
      map_smul' k1 k2 := by simp only [RingHom.id_apply, ← map_smul]; rfl
    }
  comm _ := by
    ext
    simp only [ChainComplexAbel, Rep.trivial, ModuleCat.endRingEquiv, RingEquiv.symm_mk,
      RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
      RingHom.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply,
      Representation.isTrivial_def, ModuleCat.ofHom_id, Finsupp.linearEquivFunOnFinite,
      Equiv.invFun_as_coe, LinearEquiv.coe_symm_mk, Category.id_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_mk, AddHom.coe_mk, Function.const_one, ModuleCat.hom_comp, LinearMap.coe_comp]
    ext
    simp

abbrev elekg [CommGroup G] (x : MonoidAlgebra k G) : MonoidAlgebra k G :=
  ∑ i ∈ Finset.range (Fintype.card G), ∑ k ∈ Finset.range i, .single (σ^i)
  ((-1)^(i + k + 1) * x (σ^k))

lemma elekg_single [CommGroup G] (g : G) (hσ : Submonoid.powers σ = ⊤):
    elekg G k σ (.single g 1) = .single g 1 := by
  classical
  obtain ⟨m, rfl⟩ := Submonoid.mem_powers_iff g σ|>.1 <| by rw [hσ]; trivial
  ext g
  obtain ⟨m', rfl⟩ := Submonoid.mem_powers_iff g σ|>.1 <| by rw [hσ]; trivial
  have eq_iff (k k' : ℕ) : σ^k = σ^k' ↔ (Fintype.card G)∣(k - k') := sorry
  simp [MonoidAlgebra.single_apply, elekg, eq_iff] --Finset.sum_ite]
  sorry
  -- simp [elekg, MonoidAlgebra.single, Finsupp.single_apply, Finset.sum_ite]

lemma ele_is_preim [CommGroup G] (x : MonoidAlgebra k G) (hσ : Submonoid.powers σ = ⊤):
    (sigmaminus1 G k σ) (elekg G k σ x)
    = x + (∑ j ∈ Finset.range (Fintype.card G), x (σ^j)) • (sorry : MonoidAlgebra k G) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    simp [elekg]
    sorry
  | hadd f g _ _ => sorry
  | hsmul r f _ => sorry

-- lemma eq_sum_sigma [CommGroup G] (hσ : Submonoid.powers σ = ⊤) (x : MonoidAlgebra k G) :
--     x = ∑ i ∈ Finset.range (Fintype.card G), .single (σ^i) (x (σ^i)) := by
--   rw [← MonoidAlgebra.sum_single x]
--   change ∑ i ∈ x.support, MonoidAlgebra.single _ _ = _
--   simp
--   --rw [show x.support = Finset.range (Fintype.card G) from sorry]
--   sorry
omit [Fintype G] in
@[simp]
lemma MonoidAlgebra.sub_apply [Group G] (x y : MonoidAlgebra k G) (g : G) :
    (x - y) g = x g - y g := rfl

omit [Fintype G] in
@[simp]
lemma MonoidAlgebra.sum_apply [Group G] {α : Type*} (s : Finset α)
    (f : α → MonoidAlgebra k G) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  -- have := Finset.sum_apply (γ := G) g s
  sorry


lemma im_sigmainus1_eq_ker_π [CommGroup G] (hσ : Submonoid.powers σ = ⊤):
    LinearMap.ker ((CyclicCoh.π G k σ).f 0).1.hom ≤
    LinearMap.range (sigmaminus1 G k σ).1.hom := fun (x : MonoidAlgebra k G) hx ↦ by
  simp [CyclicCoh.π] at hx ⊢
  change _ = (0 : k) at hx

  let r' : ℕ → k := fun m ↦ - (∑ i : Fin (m + 1), x.2 (σ^i.1))
  use ∑ i ∈ Finset.range (Fintype.card G), .single (σ^i) (r' i)
  erw [map_sum]
  simp [Representation.ofMulAction_single, ← pow_succ']
  -- rw [← Finset.sum_sub_distrib]
  change (∑ i ∈ _, _ - ∑ i ∈ _, _ : MonoidAlgebra k G) = _
  ext g
  simp
  -- have := Equiv.mulLeft σ
  -- rw [← Finset.sum_equiv (Equiv.mulLeft σ) _ (fun _ _ ↦ rfl)]
  -- calc _
  -- _ = _ := sorry

  -- use (Finsupp.equivFunOnFinite.symm _)
  -- erw [Finsupp.lsum_apply] at hx
  -- simp [Representation.ofMulAction] at hx ⊢
  sorry

lemma N_ker_eq_im_sigmainus1 [CommGroup G]: LinearMap.ker (N G k).1.hom =
    LinearMap.range (sigmaminus1 G k σ).1.hom := SetLike.ext_iff.2 fun (x : MonoidAlgebra k G) ↦
  ⟨fun hx ↦ by
    simp at hx ⊢
    sorry, by sorry⟩

lemma sigmaminus1_ker_eq_N_im [CommGroup G]: LinearMap.ker (sigmaminus1 G k σ).1.hom = LinearMap.range (N G k).1.hom := by
  sorry

instance (V : ModuleCat k) [Subsingleton V]: Subsingleton (End V) where
  allEq _ _ := ModuleCat.hom_ext <| LinearMap.ext (fun _ ↦ Subsingleton.allEq _ _)

def singletonVasRep [Group G] (V : ModuleCat k) [Subsingleton V]: CategoryTheory.Limits.IsZero
    (⟨V, ⟨⟨0, Subsingleton.elim _ _⟩, fun _ _ ↦ rfl⟩⟩ : Rep k G) where
  unique_to W := ⟨⟨⟨0, fun _ ↦ by simp⟩, fun _ ↦ by ext (x : V); simp [Subsingleton.elim x 0]⟩⟩
  unique_from W := ⟨⟨⟨ModuleCat.ofHom 0, fun _ ↦ rfl⟩, fun f ↦ by ext x; simp; rw [Subsingleton.elim (f.1.hom x) 0]⟩⟩

omit [Fintype G] in
lemma singleton_isZero [Group G] : ∀ X : Rep k G, Limits.IsZero X → Subsingleton X := by
  intro X h
  have := CategoryTheory.Limits.IsZero.iso (singletonVasRep G k (.of k (⊥ : Submodule k k))) h
  have : (⊥ : Submodule k k) ≃ₗ[k] X.V := Iso.toLinearEquiv ({
    hom := this.1.hom
    inv := this.2.hom
    hom_inv_id := by rw [← Action.comp_hom, this.3]; rfl
    inv_hom_id := by rw [← Action.comp_hom, this.4]; rfl
  } : ModuleCat.of k _ ≅ X.V)
  exact Equiv.subsingleton.symm this.toEquiv

open ZeroObject in
instance singleton_zero [Group G]: Subsingleton (0 : Rep k G) :=
  singleton_isZero G k 0 (Limits.isZero_zero (Rep k G))

open ZeroObject in
instance [Group G]: Subsingleton ((forget₂ (Rep k G) (ModuleCat k)).obj 0) :=
  singleton_zero G k

open ZeroObject HomologicalComplex in
instance CyclicCoh.quasiIso [CommGroup G] (hσ : Submonoid.powers σ = ⊤):
    QuasiIso (CyclicCoh.π G k σ) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ← ShortComplex.quasiIso_map_iff_of_preservesLeftHomology
          (forget₂ (Rep k G) (ModuleCat k))]
      refine ShortComplex.IsQuasiIsoAt_iff_moduleCat k _ _ _ |>.2 ⟨by
        simpa [eq_comm (a := (0 : (forget₂ (Rep k G) (ModuleCat k)).obj _)),
          ChainComplexAbel, -map_sub] using im_sigmainus1_eq_ker_π G k σ hσ, by
        simp
        intro (a : k)
        change ∃ (x : MonoidAlgebra k G), (0 : k) = _ - _
        change ∃ (x : MonoidAlgebra k G), _ = ((π G k σ).1 0).1.hom x - _
        simp [π, π_aux]
        exact ⟨Finsupp.single 1 a, by
          rw [eq_comm, sub_eq_zero]; exact Finsupp.lsum_single _ _ _ _⟩⟩

    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · rw [HomologicalComplex.exactAt_iff,
          ← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
          ShortComplex.moduleCat_exact_iff]
        intro x hx
        -- change ((forget₂ (Rep k G) (ModuleCat k)).obj (@OfNat.ofNat (Rep k G) 0 (@Zero.toOfNat0 (Rep k G) (Limits.HasZeroObject.zero' (Rep k G)) : OfNat (Rep k G) 0) : Rep k G)) at x
        simp at *
        change (forget₂ (Rep k G) (ModuleCat k)).obj 0 at x
        exact Subsingleton.elim 0 x
      · rw [HomologicalComplex.exactAt_iff,
          ← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
          ShortComplex.moduleCat_exact_iff]
        intro x hx
        simp [ChainComplexAbel, Nat.even_add_one] at *
        split_ifs with h
        · rw [← Nat.not_odd_iff_even] at h
          simp [h] at hx
          change (sigmaminus1 G k σ).1.hom x = 0 at hx
          change MonoidAlgebra k G at x
          -- simp? at hx
          change ∃ (y : MonoidAlgebra k G), (N G k).1.hom _ = x
          rw [← LinearMap.mem_ker, sigmaminus1_ker_eq_N_im] at hx
          exact hx
        · rw [Nat.not_even_iff_odd] at h
          simp [h] at hx
          change (N G k).1.hom x = 0 at hx
          rw [← LinearMap.mem_ker, N_ker_eq_im_sigmainus1 G k σ] at hx
          exact hx

--   instQuasiIsoHom (CyclicCoh.homotopyEquiv G k σ)

def ProjectResolCyclic [CommGroup G] (hσ : Submonoid.powers σ = ⊤):
    ProjectiveResolution (Rep.trivial k G k) where
  complex := ChainComplexAbel G k σ
  projective n := by
    classical
    change Projective (Rep.ofMulAction k G G)

    exact Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
      @ModuleCat.projective_of_free.{0} _ _
        (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (G)).asModule)
        Unit <| by
          convert (Basis.singleton Unit (MonoidAlgebra k G))
          ext a b
          show (Representation.ofMulAction k G G).asAlgebraHom _ _ = a * b

          induction b using MonoidAlgebra.induction_on with
          | hM b =>
            induction a using MonoidAlgebra.induction_on with
            | hM a =>
              ext
              simp
              rw [MonoidAlgebra.single_mul_single]
              simp [MonoidAlgebra.single_apply, eq_inv_mul_iff_mul_eq]
            | hadd f g _ _ => simp_all [add_mul]
            | hsmul r f _ => simp_all
          | hadd f g _ _ => simp_all [mul_add]
          | hsmul r f _ => simp_all
  π := CyclicCoh.π G k σ
  quasiIso := CyclicCoh.quasiIso G k σ hσ

open groupCohomology

-- example [CommGroup G] (A : Rep k G) (n : ℕ ):
  -- (HomologicalComplex.sc ((ChainComplexAbel G k σ).linearYonedaObj k A) n).X n =
  -- ((Rep.ofMulAction k G G) ⟶ A) := rfl

abbrev N' [Group G] (A : Rep k G): A ⟶ A where
  hom := ModuleCat.ofHom (A.ρ.asAlgebraHom (∑ i, .single i 1))
  comm g := by
    ext x
    dsimp
    rw [← Representation.asAlgebraHom_single_one, ← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    rw [← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp
    -- Note: Add `MonoidAlgebra.finset_sum_apply`
    -- rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
    -- simp

abbrev sigmaminus1' [CommGroup G] (A : Rep k G): A ⟶ A where
  hom := ModuleCat.ofHom (A.ρ.asAlgebraHom (.single σ 1 - 1))
  comm g := by
    ext g1 :3
    dsimp [ModuleCat.endRingEquiv]
    rw [← Representation.asAlgebraHom_single_one, ← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    rw [← LinearMap.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp [mul_comm]

def Acomplex [CommGroup G] (A : Rep k G): CochainComplex (Rep k G) ℕ where
  X i := A
  d i j := if i + 1 = j then if Even j then (N' G k A) else sigmaminus1' G k σ A else 0
  shape := by simp +contextual
  d_comp_d' i j k1 := by
    rintro rfl rfl
    simp only [↓reduceIte, Nat.even_add_one, ite_not, Nat.not_odd_iff_even]
    split_ifs
    swap
    · ext : 2
      simp only [Action.comp_hom, one_smul,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, Action.zero_hom, ModuleCat.hom_zero]
      rw [← LinearMap.mul_eq_comp, ← map_mul]
      suffices ((MonoidAlgebra.single σ 1 - (1 : MonoidAlgebra k G)) * ∑ i : G, MonoidAlgebra.single i 1) = 0 by
        rw [this, map_zero]
      rw [sub_mul, sub_eq_zero]
      ext
      simp
      -- rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
      -- simp
    · ext : 2
      simp only [Action.comp_hom, one_smul,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, Action.zero_hom, ModuleCat.hom_zero]
      rw [← LinearMap.mul_eq_comp, ← map_mul]
      suffices ((∑ i : G, MonoidAlgebra.single i 1 ) * (MonoidAlgebra.single σ 1 - (1 : MonoidAlgebra k G))) = 0 by
        rw [this, map_zero]
      rw [mul_sub, sub_eq_zero]
      ext
      simp
      -- rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
      -- simp

omit [Fintype G] in
@[simp]
lemma forget₂_map_hom [Group G] (A B : Rep k G) (f : A ⟶ B): (forget₂ (Rep k G) (ModuleCat k)).map f = f.hom := rfl

omit [Fintype G] in
@[simp]
lemma forget₂_obj_coe [Group G] (A : Rep k G): (forget₂ (Rep k G) (ModuleCat k)).obj A = A.V := rfl

abbrev equiv_Acomplex [CommGroup G] (A : Rep k G): (ChainComplexAbel G k σ).linearYonedaObj k A ≅
    (forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _|>.obj (Acomplex G k σ A) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ LinearEquiv.toModuleIso (Rep.leftRegularHomEquiv A)) <|
  fun i j hij ↦ by
  cases hij
  simp [Acomplex, ChainComplexAbel]
  split_ifs
  · ext (f : Rep.ofMulAction k G G ⟶ A)
    simp [Representation.ofMulAction_single]
    -- needs fixing
    conv => enter [1, 2, c]; rw [← Rep.hom_comm_apply]
    simp [Representation.ofMulAction_single]
  · ext (f : Rep.ofMulAction k G G ⟶ A)
    simp [Representation.ofMulAction_single]
    rw [← Rep.hom_comm_apply]
    simp [Representation.ofMulAction_single]

def CyclicCoh.groupCoh [CommGroup G] (A : Rep k G) (hσ : Submonoid.powers σ = ⊤): groupCohomology A n ≅
    (((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _|>.obj
    (Acomplex G k σ A))).homology n :=
  groupCohomologyIsoExt A n ≪≫ (ProjectResolCyclic G k σ hσ).isoExt n A ≪≫
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (equiv_Acomplex G k σ A)

abbrev CyclicCoh.groupCoh0 [CommGroup G] (A : Rep k G) : groupCohomology A 0 ≅
  ModuleCat.of k A.ρ.invariants := groupCohomology.isoH0 A

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
open Limits in
-- @[simps K H i π]
def moduleCatLeftHomologyData (S : ShortComplex (ModuleCat k)) (P : Submodule k S.X₂)
    (hP : P = LinearMap.ker S.g.hom) (Q : Submodule k P)
    (hQ : Q.map P.subtype = LinearMap.range S.f.hom): S.LeftHomologyData where
  K := ModuleCat.of k P
  H := ModuleCat.of k (P ⧸ Q)
  i := ModuleCat.ofHom P.subtype
  π := ModuleCat.ofHom Q.mkQ
  wi := by aesop
  hi := by
    subst hP
    exact ModuleCat.kernelIsLimit _
  wπ := by
    subst hP;
    obtain rfl : Q = LinearMap.range S.moduleCatToCycles := by
      apply Submodule.map_injective_of_injective (f := (LinearMap.ker S.g.hom).subtype)
        Subtype.val_injective
      rw [hQ, ← LinearMap.range_comp]
      rfl
    simp_all only [Fork.ofι_pt, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    ext x
    simp_all only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    apply Exists.intro
    · rfl
  hπ := by
    subst hP
    obtain rfl : Q = LinearMap.range S.moduleCatToCycles := by
      apply Submodule.map_injective_of_injective (f := (LinearMap.ker S.g.hom).subtype)
        Subtype.val_injective
      rw [hQ, ← LinearMap.range_comp]
      rfl
    exact ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)
-- abbrev ShortComplex.moduleCatHomology_eq
-- fun x ↦ N G k ≫ x
-- example [CommGroup G] (A : Rep k G) : (LinearMap.range (N' G k A).1.hom).comap A.ρ.invariants.subtype := sorry
abbrev CyclicCoh.groupCohEven (hn : Even n) [h : NeZero n] [CommGroup G] (A : Rep k G)
    (hσ : Submonoid.powers σ = ⊤):
    groupCohomology A n ≅ .of k (A.ρ.invariants ⧸ (LinearMap.range (N' G k A).1.hom).comap
    A.ρ.invariants.subtype) :=
  (CyclicCoh.groupCoh n G k σ A hσ) ≪≫ (moduleCatLeftHomologyData k _ _
  (by
    simp [Acomplex, Nat.even_add_one, hn]
    ext x
    exact ⟨fun hx ↦ by
      simp [sub_eq_zero] at hx ⊢
      exact hx σ, fun hx ↦ by
      simp [sub_eq_zero, SetLike.ext_iff, Submonoid.mem_powers_iff] at hx hσ ⊢
      intro g
      obtain ⟨m, hm⟩ := hσ g
      subst hm
      induction m with
      | zero => simp
      | succ m hh => simp_all [pow_succ]⟩) _
    (by
      cases n
      · aesop
      · simp [Acomplex, Nat.even_add_one, hn]
        rintro x ⟨y, rfl⟩
        simp
        intro g
        simp_rw [←  LinearMap.mul_apply, ← map_mul]
        conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft g) _]
        rfl)).homologyIso

abbrev CyclicCoh.groupCohOdd (hn : Odd n) [h : NeZero n] [CommGroup G] (A : Rep k G)
  (hσ : Submonoid.powers σ = ⊤):
    groupCohomology A n ≅ .of k (LinearMap.ker (N' G k A).1.hom ⧸
      (LinearMap.range (sigmaminus1' G k σ A).1.hom).comap
      (LinearMap.ker (N' G k A).1.hom).subtype) :=
  (CyclicCoh.groupCoh n G k σ A hσ) ≪≫ (moduleCatLeftHomologyData k _ _
  (by simp [Acomplex, Nat.even_add_one, hn]) _ (by
    cases n with
    | zero => aesop
    | succ m =>
      simp [Acomplex, ← Nat.even_add_one, ← Nat.not_odd_iff_even, hn]
      rintro x ⟨y, rfl⟩
      simp [sub_eq_zero]
      simp_rw [←  LinearMap.mul_apply, ← map_mul]
      conv_rhs => rw [← Equiv.sum_comp (Equiv.mulRight σ) _]
      rfl)).homologyIso

instance CommG (G : Type*) (σ : G) [Group G] (hσ : Submonoid.powers σ = ⊤): CommGroup G where
  mul_comm a b := by
    obtain ⟨n, rfl⟩ := SetLike.ext_iff.1 hσ a|>.2 (by trivial)
    obtain ⟨m, rfl⟩ := SetLike.ext_iff.1 hσ b|>.2 (by trivial)
    simp [← pow_add, add_comm]

variable (F K : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K] (τ : K ≃ₐ[F] K)
    (hτ : Submonoid.powers τ = ⊤) [FiniteDimensional F K]

open scoped Classical in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 40000 in
/-- For K/F a finite cyclic extension, `Br(K/F)` is isomorphic to `(ℤ[Gal(K/F)])ᴳ/N(ℤ[Gal(K/F)])` where
  `N : ℤ[Gal(K/F)] → ℤ[Gal(K/F)]` sends `a` to ∑ σⁱa, σ is the generator of `Gal(K/F)`. -/
abbrev BrauerOverCyclic'  :
    Additive (RelativeBrGroup K F) ≃ₗ[ℤ]
    ((galAct F K).ρ.invariants ⧸ (LinearMap.range (N' _ ℤ _).1.hom).comap
    (galAct F K).ρ.invariants.subtype) :=
  letI : CommGroup (K ≃ₐ[F] K) := CommG (K ≃ₐ[F] K) τ hτ
  ({__ := RelativeBrGroup.isoSnd K F
    map_smul' z a := by simp} : _ ≃ₗ[ℤ] _ ) ≪≫ₗ
  (Iso.toLinearEquiv (groupCohomology.isoH2 (galAct F K)).symm) ≪≫ₗ
  (Iso.toLinearEquiv (CyclicCoh.groupCohEven 2 (K ≃ₐ[F] K) ℤ τ (by simp) (galAct F K) hτ))

abbrev invariants_eq : ((galAct F K).ρ.invariants : Submodule ℤ
  (Rep.ofMulDistribMulAction (K ≃ₐ[F] K) Kˣ).V) = sorry := sorry

set_option synthInstance.maxHeartbeats 40000 in
abbrev BrauerOverCyclic : Additive (RelativeBrGroup K F) ≃+
    Additive (Fˣ⧸(Units.map (Algebra.norm (S := K) F)).range) :=
  BrauerOverCyclic' F K τ hτ|>.toAddEquiv.trans
  sorry
