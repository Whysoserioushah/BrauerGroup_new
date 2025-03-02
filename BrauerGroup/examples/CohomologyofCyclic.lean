import Mathlib

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

-- def CyclicCoh.homotopyEquiv [CommGroup G]: HomotopyEquiv (ChainComplexAbel G k σ)
--     ((ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k)) where
--   hom := π G k σ
--   inv := (ChainComplex.fromSingle₀Equiv _ _).symm <| CyclicCoh.homotopy_aux G k _
--   homotopyHomInvId := {
--     hom i j := sorry
--       -- ChainComplexAbel G k σ|>.d j i
--     zero :=  sorry
--     -- simp +contextual

--     comm i := by
--       -- ext (x : MonoidAlgebra k G)
--       -- simp [ChainComplexAbel, π, π_aux, homotopy_aux]
--       -- cases i with
--       -- | zero =>
--       --   ext g g'
--       --   simp [Rep.trivial, Representation.trivial, ChainComplex.fromSingle₀Equiv,
--       --     Finsupp.linearEquivFunOnFinite, Finsupp.equivFunOnFinite]
--         -- erw [@dNext_eq ℕ (Rep k G) _ _ {
--         --   Rel i j := (j = i + 1)
--         --   next_eq := by simp
--         --   prev_eq := by simp
--         -- } _ (ChainComplexAbel G k σ) _ 0 1 (by sorry)]




--         sorry

--   }
--   homotopyInvHomId := sorry


instance CyclicCoh.quasiIso [CommGroup G]: QuasiIso (CyclicCoh.π G k σ) where
  quasiIsoAt i := by
    cases i with
    | zero => sorry
    | succ n => sorry
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

variable [Group G] (hσ : Submonoid.powers σ = ⊤)

open groupCohomology

abbrev CyclicCoh.fromTwoCocycles (a : twoCocycles (Rep.ofMulAction ℤ G G)) :
    H0 (Rep.ofMulAction ℤ G G) where
  val := (a ⟨σ, σ⟩: MonoidAlgebra ℤ G)
  property g := by
    ext g'
    simp [Representation.ofMulAction_def, Finsupp.mapDomain]
    sorry

abbrev cyclicEquiv:  H2 (Rep.ofMulAction ℤ G G) ≃+ Additive G := sorry
