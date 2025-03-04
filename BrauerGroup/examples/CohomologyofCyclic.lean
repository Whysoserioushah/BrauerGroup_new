import Mathlib
import BrauerGroup.examples.«ShortComplex.LeftHomologyMapData»

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
    simp [ChainComplexAbel, ModuleCat.endRingEquiv]
    erw [Finsupp.lsum_apply, Finsupp.lsum_apply]
    induction x using MonoidAlgebra.induction_on with
    | hM a =>
      simp
      rw [Representation.ofMulAction_single, Finsupp.sum_single_index rfl]
      rfl
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
    simp [Representation.ofMulAction_single]
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
      RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp,
      MonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply,
      Finsupp.linearEquivFunOnFinite, Equiv.invFun_as_coe, LinearEquiv.coe_symm_mk,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, LinearMap.coe_mk,
      AddHom.coe_mk, Representation.apply_eq_self, Function.const_one]
    ext
    simp

lemma im_sigmainus1_eq_ker_π [CommGroup G]:
    LinearMap.ker ((CyclicCoh.π G k σ).f 0).1.hom ≤
    LinearMap.range (sigmaminus1 G k σ).1.hom := by
  sorry

lemma N_ker_eq_im_sigmainus1 [CommGroup G]: LinearMap.ker (N G k).1.hom = LinearMap.range (sigmaminus1 G k σ).1.hom := by
  sorry

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
instance CyclicCoh.quasiIso [CommGroup G]: QuasiIso (CyclicCoh.π G k σ) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ← ShortComplex.quasiIso_map_iff_of_preservesLeftHomology
          (forget₂ (Rep k G) (ModuleCat k))]
      refine ShortComplex.IsQuasiIsoAt_iff_moduleCat k _ _ _ |>.2 ⟨by
        simpa [eq_comm (a := (0 : (forget₂ (Rep k G) (ModuleCat k)).obj _)),
          ChainComplexAbel, -map_sub] using im_sigmainus1_eq_ker_π G k σ, by
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

def ProjectResolCyclic [CommGroup G]: ProjectiveResolution (Rep.trivial k G k) where
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

open groupCohomology

def CyclicCoh.groupCoh [CommGroup G] (A : Rep k G) : groupCohomology A n ≅
   ((ChainComplexAbel G k σ).linearYonedaObj k A).homology n :=
  groupCohomologyIsoExt A n ≪≫ (ProjectResolCyclic G k σ).isoExt n A

abbrev CyclicCoh.groupCoh0 [CommGroup G] (A : Rep k G) : groupCohomology A 0 ≅
  ModuleCat.of k A.ρ.invariants := groupCohomology.isoH0 A

example [CommGroup G] (A : Rep k G):
  ((ChainComplexAbel G k σ).linearYonedaObj k A).X n =
  ((Rep.ofMulAction k G G) ⟶ A) := rfl

abbrev CyclicCoh.groupCohEven (hn : Even n) [NeZero n] [CommGroup G] (A : Rep k G):
    groupCohomology A n ≅ sorry := sorry
    -- (A.ρ.invariants ⧸ LinearMap.range (N G k).1.hom) := sorry

-- example [CommGroup G] (A : Rep k G):
--   ((ChainComplexAbel G k σ).linearYonedaObj k A).homology n =
--   .of k (LinearMap.ker ((ChainComplexAbel G k σ).d (n + 1) (n + 2)).1.hom ⧸
--     LinearMap.range ((ChainComplexAbel G k σ).d n (n + 1)).1.hom) := sorry


  -- abbrev CyclicCoh.fromTwoCocycles (a : twoCocycles (Rep.ofMulAction ℤ G G)) :
--     H0 (Rep.ofMulAction ℤ G G) where
--   val := (a ⟨σ, σ⟩: MonoidAlgebra ℤ G)
--   property g := by
--     ext g'
--     simp [Representation.ofMulAction_def, Finsupp.mapDomain]
--     sorry

-- abbrev cyclicEquiv:  H2 (Rep.ofMulAction ℤ G G) ≃+ Additive G := sorry
