module

public import BrauerGroup.IsoSecond
public import BrauerGroup.examples.ShortComplex.LeftHomologyMapData

@[expose] public section

suppress_compilation

open CategoryTheory Module

variable (n : ℕ) (G k : Type) (σ : G) [Fintype G] [CommRing k]

set_option backward.isDefEq.respectTransparency false in
abbrev N [Group G] : Rep.ofMulAction k G G ⟶ Rep.ofMulAction k G G :=
  Rep.ofHom <| (((Representation.ofMulAction k G G).asAlgebraHom
      (∑ i : G, .single i 1)).intertwiningMap_of_isIntertwiningMap _ _) <| by
    intro g g1
    ext g1 :3
    rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply,
      ← map_mul (Representation.asAlgebraHom _)]
    rw [← Module.End.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g' x
    classical
    simp only [map_mul, map_sum, Representation.asAlgebraHom_single, one_smul, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lsingle_apply, End.mul_apply, Representation.ofMulAction_single,
      smul_eq_mul, LinearMap.coe_sum, Finset.sum_apply, Finsupp.coe_finsetSum]
    rw [Fintype.sum_eq_single (x * g'⁻¹ * g⁻¹), Fintype.sum_eq_single (g⁻¹ * x * g'⁻¹)]
    · simp +contextual [mul_assoc]
    all_goals
    · rintro y hy
      refine Finsupp.single_eq_of_ne ?_
      simpa [eq_mul_inv_iff_mul_eq, eq_inv_mul_iff_mul_eq, eq_comm, ← mul_assoc] using hy

abbrev sigmaminus1 [CommGroup G] : Rep.ofMulAction k G G ⟶ Rep.ofMulAction k G G :=
  Rep.ofHom <| (((Representation.ofMulAction k G G).asAlgebraHom
      (.single σ 1 - 1)).intertwiningMap_of_isIntertwiningMap _ _) <| by
    intro g g1
    rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply,
      ← map_mul (Representation.asAlgebraHom _)]
    rw [← Module.End.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp [mul_comm]

def ChainComplexAbel [CommGroup G] : ChainComplex (Rep k G) ℕ where
  X _ := Rep.ofMulAction k G G
  d i j := if j + 1 = i then if Even i then N G k else sigmaminus1 G k σ else 0
  shape := by simp +contextual
  d_comp_d' i j k1 := by
    rintro rfl rfl
    simp only [↓reduceIte, Nat.even_add_one, ite_not]
    split_ifs
    · ext : 2
      simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, Rep.hom_ofHom,
        Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap]
      change (Representation.ofMulAction k G G).asAlgebraHom (MonoidAlgebra.single σ 1 - 1) *
        (Representation.ofMulAction k G G).asAlgebraHom (∑ i : G, MonoidAlgebra.single i 1) = 0
      rw [← map_mul]
      suffices ((MonoidAlgebra.single σ 1 - (1 : MonoidAlgebra k G)) *
        ∑ i : G, MonoidAlgebra.single i 1) = 0 by rw [this, map_zero]
      rw [sub_mul, sub_eq_zero]
      ext g
      simp only [MonoidAlgebra.single_mul_apply, one_mul]
      rw [show (∑ i : G, MonoidAlgebra.single i (1 : k)) (σ⁻¹ * g) =
          ∑ i : G, MonoidAlgebra.single i (1 : k) (σ⁻¹ * g) from Finsupp.finsetSum_apply _ _ _,
        show (∑ i : G, MonoidAlgebra.single i (1 : k)) g =
          ∑ i : G, MonoidAlgebra.single i (1 : k) g from Finsupp.finsetSum_apply _ _ _]
      simp
    · ext : 2
      simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, Rep.hom_ofHom,
        Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap]
      change (Representation.ofMulAction k G G).asAlgebraHom (∑ i : G, MonoidAlgebra.single i 1) *
        (Representation.ofMulAction k G G).asAlgebraHom (MonoidAlgebra.single σ 1 - 1) = 0
      rw [← map_mul]
      suffices (∑ i, .single i 1) * (.single σ 1 - 1 : MonoidAlgebra k G) = 0 by rw [this, map_zero]
      rw [mul_sub, sub_eq_zero]
      ext g
      simp only [MonoidAlgebra.mul_single_apply, mul_one]
      rw [show (∑ i : G, MonoidAlgebra.single i (1 : k)) (g * σ⁻¹) =
          ∑ i : G, MonoidAlgebra.single i (1 : k) (g * σ⁻¹) from Finsupp.finsetSum_apply _ _ _,
        show (∑ i : G, MonoidAlgebra.single i (1 : k)) g =
          ∑ i : G, MonoidAlgebra.single i (1 : k) g from Finsupp.finsetSum_apply _ _ _]
      simp

abbrev π_aux [CommGroup G] :
    (ChainComplexAbel G k σ).X Nat.zero ⟶
      ((ChainComplex.single₀ (Rep k G)).obj (.trivial k G k)).X Nat.zero :=
  Rep.ofHom <| ((Finsupp.lsum ℕ 1 : _ →ₗ[k] k).intertwiningMap_of_isIntertwiningMap _ _) <| by
    intro g x
    simp only [Representation.isTrivial_def, LinearMap.id_coe, id_eq]
    erw [Finsupp.lsum_apply, Finsupp.lsum_apply]
    classical
    rw [Representation.ofMulAction_def, Finsupp.lmapDomain_apply,
      Finsupp.sum_mapDomain_index (by simp) (by simp)]
    rfl

def CyclicCoh.π [CommGroup G] :
    ChainComplexAbel G k σ ⟶ (ChainComplex.single₀ (Rep k G)).obj (.trivial k G k) where
  f ii := ii.casesOn (π_aux G k σ) fun _ ↦ 0
  comm' i j := by
    rintro rfl
    cases j
    pick_goal 2
    · simp only [HomologicalComplex.single_obj_d, Limits.comp_zero]
    simp only [ChainComplexAbel, Nat.reduceAdd, ChainComplex.single₀_obj_zero, Nat.rec_one,
      HomologicalComplex.single_obj_d, zero_add, ↓reduceIte, Nat.not_even_one, Nat.rec_zero]
    ext g
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lsingle_apply, Rep.hom_ofHom]
    rw [show (LinearMap.intertwiningMap_of_isIntertwiningMap (Representation.ofMulAction k G G)
        (Representation.ofMulAction k G G)
          ((Representation.ofMulAction k G G).asAlgebraHom (MonoidAlgebra.single σ 1 - 1)) _
          ).toLinearMap (Finsupp.single g 1) =
        ((Representation.ofMulAction k G G).asAlgebraHom (MonoidAlgebra.single σ 1 - 1))
          (Finsupp.single g 1) from rfl]
    simp only [map_sub, Representation.asAlgebraHom_single, one_smul, map_one, LinearMap.sub_apply,
      Representation.ofMulAction_single, smul_eq_mul, Module.End.one_apply]
    erw [Finsupp.lsum_single, Finsupp.lsum_single]
    trans (0 : k)
    · exact map_zero _
    · simp

def CyclicCoh.homotopy_aux [CommGroup G] : .trivial k G k ⟶ (ChainComplexAbel G k σ).X 0 :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ({
      toFun kk := Finsupp.linearEquivFunOnFinite k k G|>.symm <| Function.const G kk
      map_add' k1 k2 := by simp [← map_add]
      map_smul' k1 k2 := by simp only [RingHom.id_apply, ← map_smul]; rfl
    } : k →ₗ[k] _) <| by
    classical
    intro g kk
    simp only [Representation.isTrivial_def, LinearMap.id_coe, id_eq, LinearMap.coe_mk,
      AddHom.coe_mk]
    apply Finsupp.ext
    intro g1
    rw [Representation.ofMulAction_def, Finsupp.lmapDomain_apply]
    simp only [Finsupp.linearEquivFunOnFinite, LinearEquiv.coe_symm_mk]
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (g⁻¹ * g1)]
    · rw [if_pos (by group)]; rfl
    · intro b _ hb
      rw [if_neg (fun h => hb (by rw [← h]; group))]
    · intro h; exact absurd (Finset.mem_univ _) h

abbrev elekg [CommGroup G] (x : MonoidAlgebra k G) : MonoidAlgebra k G :=
  ∑ i ∈ Finset.range (Fintype.card G), ∑ k ∈ Finset.range i, .single (σ^i)
  ((-1)^(i + k + 1) * x (σ^k))

lemma elekg_single [CommGroup G] (g : G) (hσ : Submonoid.powers σ = ⊤) :
    elekg G k σ (.single g 1) = .single g 1 := by
  classical
  obtain ⟨m, rfl⟩ := Submonoid.mem_powers_iff g σ|>.1 <| by rw [hσ]; trivial
  ext g
  obtain ⟨m', rfl⟩ := Submonoid.mem_powers_iff g σ|>.1 <| by rw [hσ]; trivial
  have eq_iff (k k' : ℕ) : σ^k = σ^k' ↔ (Fintype.card G)∣(k - k') := sorry
  simp [MonoidAlgebra.single_apply, elekg, eq_iff] --Finset.sum_ite]
  sorry
  -- simp [elekg, MonoidAlgebra.single, Finsupp.single_apply, Finset.sum_ite]

lemma ele_is_preim [CommGroup G] (x : MonoidAlgebra k G) (hσ : Submonoid.powers σ = ⊤) :
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

lemma im_sigmainus1_eq_ker_π [CommGroup G] (hσ : Submonoid.powers σ = ⊤) :
    LinearMap.ker ((CyclicCoh.π G k σ).f 0).hom.toLinearMap ≤
    LinearMap.range (sigmaminus1 G k σ).hom.toLinearMap := fun (x : MonoidAlgebra k G) hx ↦ by
  simp only [ChainComplex.single₀_obj_zero, CyclicCoh.π, Nat.rec_zero, LinearMap.mem_ker] at hx ⊢
  change _ = (0 : k) at hx
  let r' : ℕ → k := fun m ↦ - (∑ i : Fin (m + 1), x.2 (σ^i.1))
  use ∑ i ∈ Finset.range (Fintype.card G), .single (σ^i) (r' i)
  have hsig : ∀ y : MonoidAlgebra k G, (Rep.Hom.hom (sigmaminus1 G k σ)).toLinearMap y =
      (Representation.ofMulAction k G G).asAlgebraHom (.single σ 1 - 1) y := fun _ ↦ rfl
  simp only [hsig]
  erw [map_sum]
  simp only [LinearMap.sub_apply, Representation.ofMulAction_single, smul_eq_mul, ← pow_succ',
    map_sub, Representation.asAlgebraHom_single, one_smul, map_one,
    Module.End.one_apply, Finset.sum_sub_distrib]
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

lemma N_ker_eq_im_sigmainus1 [CommGroup G] :
    (N G k).hom.toLinearMap.ker = (sigmaminus1 G k σ).hom.toLinearMap.range := by
  ext x
  exact ⟨fun hx ↦ by
      simp at hx ⊢
      sorry, by sorry⟩

lemma sigmaminus1_ker_eq_N_im [CommGroup G] :
    (sigmaminus1 G k σ).hom.toLinearMap.ker = (N G k).hom.toLinearMap.range := by
  sorry

instance (V : ModuleCat k) [Subsingleton V] : Subsingleton (End V) where
  allEq _ _ := ModuleCat.hom_ext <| LinearMap.ext (fun _ ↦ Subsingleton.allEq _ _)

def singletonVasRep [Group G] (V : ModuleCat k) [Subsingleton V] : CategoryTheory.Limits.IsZero
    (Rep.of (⟨⟨0, Subsingleton.elim _ _⟩, fun _ _ ↦ rfl⟩ : Representation k G V)) where
  unique_to W := ⟨⟨⟨Rep.ofHom ⟨0, fun _ ↦ by ext (x : V); simp [Subsingleton.elim x 0]⟩⟩,
    fun _ ↦ by ext (x : V); simp [Subsingleton.elim x 0]⟩⟩
  unique_from W := ⟨⟨⟨Rep.ofHom ⟨0, fun _ ↦ by ext; simp⟩⟩, fun f ↦ by
    ext x
    simp only [Rep.hom_ofHom, LinearMap.zero_apply]
    rw [Subsingleton.elim (f.hom.toLinearMap x) 0]⟩⟩

omit [Fintype G] in
lemma singleton_isZero [Group G] : ∀ X : Rep k G, Limits.IsZero X → Subsingleton X := by
  intro X h
  have hid : (𝟙 X : X ⟶ X) = 0 := h.eq_of_src _ _
  refine ⟨fun x y ↦ ?_⟩
  have hx : (𝟙 X : X ⟶ X).hom.toLinearMap x = (0 : X ⟶ X).hom.toLinearMap x := by rw [hid]
  have hy : (𝟙 X : X ⟶ X).hom.toLinearMap y = (0 : X ⟶ X).hom.toLinearMap y := by rw [hid]
  simp only [Rep.hom_id, Representation.IntertwiningMap.toLinearMap_id, LinearMap.id_coe, id_eq,
    Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply] at hx hy
  rw [hx, hy]

open ZeroObject in
instance singleton_zero [Group G] : Subsingleton (0 : Rep k G) :=
  singleton_isZero G k 0 (Limits.isZero_zero (Rep k G))

open ZeroObject in
instance [Group G] : Subsingleton ((forget₂ (Rep k G) (ModuleCat k)).obj 0) :=
  singleton_zero G k

open ZeroObject HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
lemma CyclicCoh.quasiIso [CommGroup G] (hσ : Submonoid.powers σ = ⊤) :
    QuasiIso (CyclicCoh.π G k σ) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ← ShortComplex.quasiIso_map_iff_of_preservesLeftHomology
          (forget₂ (Rep k G) (ModuleCat k))]
      refine ShortComplex.IsQuasiIsoAt_iff_moduleCat k _ _ _ |>.2 ⟨?_, ?_⟩
      · intro a _ x hx
        refine im_sigmainus1_eq_ker_π G k σ hσ ?_
        simp only [LinearMap.mem_ker]
        simp only [Functor.mapShortComplex_map_τ₂, shortComplexFunctor'_map_τ₂,
          Rep.forget₂_moduleCat_map, ModuleCat.hom_ofHom] at hx
        exact hx.symm
      · intro (a : k) _
        refine ⟨Finsupp.single 1 a, rfl, 0, ?_⟩
        rw [map_zero, eq_comm, sub_eq_zero]
        change ((π G k σ).f 0).hom.toLinearMap (Finsupp.single 1 a) = a
        simp only [π, π_aux, Nat.rec_zero]
        erw [Finsupp.lsum_single]
        simp
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · rw [HomologicalComplex.exactAt_iff,
          ← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
          ShortComplex.moduleCat_exact_iff]
        intro x hx
        simp only [ShortComplex.map_g, shortComplexFunctor_obj_g, single_obj_d, Functor.map_zero,
          ModuleCat.hom_zero, ShortComplex.map_f, shortComplexFunctor_obj_f] at *
        have hsub : Subsingleton
            ↑((sc ((ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k)) (n + 1)).map
              (forget₂ (Rep k G) (ModuleCat k))).X₂ :=
          inferInstanceAs (Subsingleton ((forget₂ (Rep k G) (ModuleCat k)).obj 0))
        exact ⟨0, Subsingleton.elim _ _⟩
      · rw [HomologicalComplex.exactAt_iff,
          ← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
          ShortComplex.moduleCat_exact_iff]
        intro x hx
        simp only [ChainComplexAbel, ShortComplex.map_g, shortComplexFunctor_obj_g,
          ChainComplex.next_nat_succ, ↓reduceIte, Nat.even_add_one, Nat.not_even_iff_odd,
          ShortComplex.map_f, shortComplexFunctor_obj_f, ChainComplex.prev,
          Nat.not_odd_iff_even] at *
        split_ifs with h
        · rw [← Nat.not_odd_iff_even] at h
          simp only [h, ↓reduceIte] at hx
          change (sigmaminus1 G k σ).hom.toLinearMap x = 0 at hx
          change MonoidAlgebra k G at x
          -- simp? at hx
          change ∃ (y : MonoidAlgebra k G), (N G k).hom.toLinearMap _ = x
          rw [← LinearMap.mem_ker, sigmaminus1_ker_eq_N_im] at hx
          exact hx
        · rw [Nat.not_even_iff_odd] at h
          simp only [h, ↓reduceIte] at hx
          change (N G k).hom.toLinearMap x = 0 at hx
          rw [← LinearMap.mem_ker, N_ker_eq_im_sigmainus1 G k σ] at hx
          exact hx

--   instQuasiIsoHom (CyclicCoh.homotopyEquiv G k σ)

set_option maxSynthPendingDepth 2 in
def ProjectResolCyclic [CommGroup G] (hσ : Submonoid.powers σ = ⊤) :
    ProjectiveResolution (Rep.trivial k G k) where
  complex := ChainComplexAbel G k σ
  projective n := by
    classical
    change Projective (Rep.ofMulAction k G G)
    exact inferInstanceAs (Projective (Rep.leftRegular k G))
  π := CyclicCoh.π G k σ
  quasiIso := CyclicCoh.quasiIso G k σ hσ

open groupCohomology

-- example [CommGroup G] (A : Rep k G) (n : ℕ ) :
  -- (HomologicalComplex.sc ((ChainComplexAbel G k σ).linearYonedaObj k A) n).X n =
  -- ((Rep.ofMulAction k G G) ⟶ A) := rfl

abbrev N' [Group G] (A : Rep k G) : A ⟶ A :=
  Rep.ofHom <| ((A.ρ.asAlgebraHom (∑ i, .single i 1)).intertwiningMap_of_isIntertwiningMap
      A.ρ A.ρ) <| by
    intro g x
    rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply,
      ← map_mul (Representation.asAlgebraHom _)]
    rw [← Module.End.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp
    -- Note: Add `MonoidAlgebra.finsetSum_apply`
    -- rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
    -- simp

abbrev sigmaminus1' [CommGroup G] (A : Rep k G) : A ⟶ A :=
  Rep.ofHom <| ((A.ρ.asAlgebraHom (.single σ 1 - 1)).intertwiningMap_of_isIntertwiningMap
      A.ρ A.ρ) <| by
    intro g g1
    rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply,
      ← map_mul (Representation.asAlgebraHom _)]
    rw [← Module.End.mul_apply, ← map_mul (Representation.asAlgebraHom _)]
    congr 2
    ext g2
    simp [mul_comm]

def Acomplex [CommGroup G] (A : Rep k G) : CochainComplex (Rep k G) ℕ where
  X i := A
  d i j := if i + 1 = j then if Even j then (N' G k A) else sigmaminus1' G k σ A else 0
  shape := by simp +contextual
  d_comp_d' i j k1 := by
    rintro rfl rfl
    simp only [↓reduceIte, Nat.even_add_one, ite_not]
    split_ifs
    swap
    · ext : 2
      simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, Rep.hom_ofHom,
        Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap]
      change A.ρ.asAlgebraHom (MonoidAlgebra.single σ 1 - 1) *
        A.ρ.asAlgebraHom (∑ i : G, MonoidAlgebra.single i 1) = 0
      rw [← map_mul]
      suffices (.single σ 1 - 1 : MonoidAlgebra k G) * ∑ i, .single i 1 = 0 by rw [this, map_zero]
      rw [sub_mul, sub_eq_zero]
      ext
      simp
      -- rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
      -- simp
    · ext : 2
      simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, Rep.hom_ofHom,
        Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap]
      change A.ρ.asAlgebraHom (∑ i : G, MonoidAlgebra.single i 1) *
        A.ρ.asAlgebraHom (MonoidAlgebra.single σ 1 - 1) = 0
      rw [← map_mul]
      suffices (∑ i, .single i 1) * (.single σ 1 - 1 : MonoidAlgebra k G) = 0 by rw [this, map_zero]
      rw [mul_sub, sub_eq_zero]
      ext
      simp
      -- rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
      -- simp

omit [Fintype G] in
@[simp]
lemma forget₂_map_hom [Group G] (A B : Rep k G) (f : A ⟶ B) :
    (forget₂ (Rep k G) (ModuleCat k)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

omit [Fintype G] in
@[simp]
lemma forget₂_obj_coe [Group G] (A : Rep k G) : (forget₂ (Rep k G) (ModuleCat k)).obj A = A.V := rfl

abbrev equiv_Acomplex [CommGroup G] (A : Rep k G) : (ChainComplexAbel G k σ).linearYonedaObj k A ≅
    (forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _|>.obj (Acomplex G k σ A) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (Rep.leftRegularHomEquiv A).toModuleIso)
  fun i j hij ↦ by
  cases hij
  simp only [ChainComplexAbel, Acomplex, LinearEquiv.toModuleIso_hom,
    Functor.mapHomologicalComplex_obj_d, ↓reduceIte, forget₂_map_hom,
    ChainComplex.linearYonedaObj_d]
  split_ifs
  · ext (f : Rep.ofMulAction k G G ⟶ A)
    change (N' G k A).hom.toLinearMap (f.hom.toLinearMap (Finsupp.single (1 : G) 1)) =
      (N G k ≫ f).hom.toLinearMap (Finsupp.single (1 : G) 1)
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
    change A.ρ.asAlgebraHom (∑ i : G, .single i 1) (f.hom.toLinearMap (Finsupp.single (1 : G) 1)) =
      f.hom.toLinearMap ((Representation.ofMulAction k G G).asAlgebraHom
        (∑ i : G, .single i 1) (Finsupp.single (1 : G) 1))
    rw [map_sum, map_sum, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_sum,
      Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
    simp only [one_smul]
    exact (Rep.hom_comm_apply f i _).symm
  · ext (f : Rep.ofMulAction k G G ⟶ A)
    change (sigmaminus1' G k σ A).hom.toLinearMap (A.leftRegularHomEquiv f) =
      A.leftRegularHomEquiv (Linear.leftComp k A (sigmaminus1 G k σ) f)
    change (sigmaminus1' G k σ A).hom.toLinearMap (f.hom.toLinearMap (Finsupp.single (1 : G) 1)) =
      (sigmaminus1 G k σ ≫ f).hom.toLinearMap (Finsupp.single (1 : G) 1)
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
    change A.ρ.asAlgebraHom (.single σ 1 - 1) (f.hom.toLinearMap (Finsupp.single (1 : G) 1)) =
      f.hom.toLinearMap ((Representation.ofMulAction k G G).asAlgebraHom
        (.single σ 1 - 1) (Finsupp.single (1 : G) 1))
    rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, map_one, map_one,
      Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
    simp only [one_smul, Module.End.one_apply, Representation.IntertwiningMap.coe_toLinearMap]
    rw [← Rep.hom_comm_apply f σ _]

def CyclicCoh.groupCoh [CommGroup G] [DecidableEq G] (A : Rep k G) (hσ : Submonoid.powers σ = ⊤) :
    groupCohomology A n ≅
      (((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _|>.obj
        (Acomplex G k σ A))).homology n :=
  groupCohomologyIsoExt A n ≪≫ (ProjectResolCyclic G k σ hσ).isoExt n A ≪≫
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (equiv_Acomplex G k σ A)

abbrev CyclicCoh.groupCoh0 [CommGroup G] (A : Rep k G) : groupCohomology A 0 ≅
  ModuleCat.of k A.ρ.invariants := groupCohomology.H0Iso A

set_option maxHeartbeats 1200000 in
-- FIXME: Get rid of raised heartbeats
set_option synthInstance.maxHeartbeats 120000 in
-- FIXME: Get rid of raised heartbeats
open Limits in
-- @[simps K H i π]
def moduleCatLeftHomologyData (S : ShortComplex (ModuleCat k)) (P : Submodule k S.X₂)
    (hP : P = LinearMap.ker S.g.hom) (Q : Submodule k P)
    (hQ : Q.map P.subtype = LinearMap.range S.f.hom) : S.LeftHomologyData where
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
    ext x
    change S.moduleCatToCycles.range.mkQ
        (((ModuleCat.kernelIsLimit S.g).lift (KernelFork.ofι S.f _)).hom x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  hπ := by
    subst hP
    obtain rfl : Q = LinearMap.range S.moduleCatToCycles := by
      apply Submodule.map_injective_of_injective (f := (LinearMap.ker S.g.hom).subtype)
        Subtype.val_injective
      rw [hQ, ← LinearMap.range_comp]
      rfl
    exact ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

abbrev CyclicCoh.groupCohEven (hn : Even n) [h : NeZero n] [CommGroup G] [DecidableEq G]
    (A : Rep k G) (hσ : Submonoid.powers σ = ⊤) :
    groupCohomology A n ≅ .of k (A.ρ.invariants ⧸ (LinearMap.range (N' G k A).hom.toLinearMap).comap
    A.ρ.invariants.subtype) :=
  (CyclicCoh.groupCoh n G k σ A hσ) ≪≫ (moduleCatLeftHomologyData k _ _
  (by
    simp only [Acomplex, HomologicalComplex.shortComplexFunctor_obj_g,
      Functor.mapHomologicalComplex_obj_d, CochainComplex.next, ↓reduceIte, Nat.even_add_one, hn,
      not_true_eq_false, forget₂_map_hom]
    ext x
    have hker : ∀ y : A.V, y ∈ (ModuleCat.Hom.hom
        (ModuleCat.ofHom (Rep.Hom.hom (sigmaminus1' G k σ A)).toLinearMap)).ker ↔ A.ρ σ y = y := by
      intro y
      change A.ρ.asAlgebraHom (.single σ 1 - 1) y = 0 ↔ _
      rw [map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
        Representation.asAlgebraHom_single, one_smul]
    exact ⟨fun hx ↦ (hker x).2 (by
      simp only [Representation.mem_invariants] at hx
      exact hx σ), fun hx ↦ by
      have hx' := (hker x).1 hx
      simp only [Representation.mem_invariants]
      simp only [SetLike.ext_iff, Submonoid.mem_powers_iff, Submonoid.mem_top, iff_true] at hσ
      intro g
      obtain ⟨m, hm⟩ := hσ g
      subst hm
      induction m with
      | zero => simp
      | succ m hh => simp_all [pow_succ]⟩) _
    (by
      cases n
      · aesop
      · have hle : LinearMap.range (N' G k A).hom.toLinearMap ≤ A.ρ.invariants := by
          rintro x ⟨y, rfl⟩
          change A.ρ.asAlgebraHom (∑ i : G, .single i 1) y ∈ A.ρ.invariants
          rw [map_sum]
          simp only [Representation.asAlgebraHom_single, one_smul, LinearMap.coe_sum,
            Finset.sum_apply, Representation.mem_invariants, map_sum]
          intro g
          simp_rw [← Module.End.mul_apply, ← map_mul]
          conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft g) _]
          rfl
        simp only [Acomplex, HomologicalComplex.shortComplexFunctor_obj_f,
          Functor.mapHomologicalComplex_obj_d, CochainComplex.prev_nat_succ, ↓reduceIte, hn,
          forget₂_map_hom]
        exact (Submodule.map_comap_subtype A.ρ.invariants
          (LinearMap.range (N' G k A).hom.toLinearMap)).trans (inf_eq_right.2 hle))).homologyIso

abbrev CyclicCoh.groupCohOdd (hn : Odd n) [h : NeZero n] [CommGroup G] [DecidableEq G]
    (A : Rep k G) (hσ : Submonoid.powers σ = ⊤) :
    groupCohomology A n ≅ .of k (LinearMap.ker (N' G k A).hom.toLinearMap ⧸
      (LinearMap.range (sigmaminus1' G k σ A).hom.toLinearMap).comap
      (LinearMap.ker (N' G k A).hom.toLinearMap).subtype) :=
  (CyclicCoh.groupCoh n G k σ A hσ) ≪≫ (moduleCatLeftHomologyData k _ _
  (by
    simp only [Acomplex, HomologicalComplex.shortComplexFunctor_obj_g,
      Functor.mapHomologicalComplex_obj_d, CochainComplex.next,
      if_pos (show Even (n + 1) from Odd.add_one hn), if_true, forget₂_map_hom]
    rfl) _ (by
    cases n with
    | zero => aesop
    | succ m =>
      have hle : LinearMap.range (sigmaminus1' G k σ A).hom.toLinearMap ≤
          LinearMap.ker (N' G k A).hom.toLinearMap := by
        rintro x ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        change A.ρ.asAlgebraHom (∑ i : G, MonoidAlgebra.single i (1 : k))
          (A.ρ.asAlgebraHom (MonoidAlgebra.single σ 1 - 1) y) = 0
        rw [← Module.End.mul_apply, ← map_mul]
        suffices (∑ i : G, MonoidAlgebra.single i (1 : k)) * (MonoidAlgebra.single σ 1 - 1) = 0 by
          rw [this, map_zero, LinearMap.zero_apply]
        rw [mul_sub, sub_eq_zero]
        ext g
        simp only [MonoidAlgebra.mul_single_apply, mul_one]
        rw [show (∑ i : G, MonoidAlgebra.single i (1 : k)) (g * σ⁻¹) =
            ∑ i : G, MonoidAlgebra.single i (1 : k) (g * σ⁻¹) from Finsupp.finsetSum_apply _ _ _,
          show (∑ i : G, MonoidAlgebra.single i (1 : k)) g =
            ∑ i : G, MonoidAlgebra.single i (1 : k) g from Finsupp.finsetSum_apply _ _ _]
        simp
      simp only [Acomplex, HomologicalComplex.shortComplexFunctor_obj_f,
        Functor.mapHomologicalComplex_obj_d, CochainComplex.prev_nat_succ, ↓reduceIte,
        if_neg (show ¬Even (m + 1) from Nat.not_even_iff_odd.2 hn), forget₂_map_hom]
      exact (Submodule.map_comap_subtype (LinearMap.ker (N' G k A).hom.toLinearMap)
        (LinearMap.range (sigmaminus1' G k σ A).hom.toLinearMap)).trans
        (inf_eq_right.2 hle))).homologyIso

@[implicit_reducible]
def CommG (G : Type*) (σ : G) [Group G] (hσ : Submonoid.powers σ = ⊤) : CommGroup G where
  mul_comm a b := by
    obtain ⟨n, rfl⟩ := SetLike.ext_iff.1 hσ a|>.2 (by trivial)
    obtain ⟨m, rfl⟩ := SetLike.ext_iff.1 hσ b|>.2 (by trivial)
    simp [← pow_add, add_comm]

variable (F K : Type) [Field F] [Field K] [Algebra F K] [IsGalois F K] (τ : Gal(K/F))
    (hτ : Submonoid.powers τ = ⊤) [FiniteDimensional F K]

open scoped Classical in
/-- For K/F a finite cyclic extension, `Br(K/F)` is isomorphic to `(ℤ[Gal(K/F)])ᴳ/N(ℤ[Gal(K/F)])`
where `N : ℤ[Gal(K/F)] → ℤ[Gal(K/F)]` sends `a` to ∑ σⁱa, σ is the generator of `Gal(K/F)`. -/
abbrev BrauerOverCyclicAux :
    H2 (galAct F K) ≅
    ModuleCat.of ℤ ((galAct F K).ρ.invariants ⧸ (LinearMap.range (N' _ ℤ _).hom.toLinearMap).comap
    (galAct F K).ρ.invariants.subtype) :=
  letI : CommGroup Gal(K/F) := CommG Gal(K/F) τ hτ
  (CyclicCoh.groupCohEven 2 Gal(K/F) ℤ τ (by simp) (galAct F K) hτ)

abbrev BrauerOverCyclic' : Additive (RelativeBrGroup K F) ≃ₗ[ℤ] (↥(galAct F K).ρ.invariants ⧸
      Submodule.comap (galAct F K).ρ.invariants.subtype
        (LinearMap.range (N' (K ≃ₐ[F] K) ℤ (galAct F K)).hom.toLinearMap)) :=
  (RelativeBrGroup.isoSnd K F).toIntLinearEquiv ≪≫ₗ (BrauerOverCyclicAux F K τ hτ).toLinearEquiv

abbrev invariants_eq : ((galAct F K).ρ.invariants : Submodule ℤ
  (Rep.ofMulDistribMulAction Gal(K/F) Kˣ).V) = sorry := sorry

abbrev BrauerOverCyclic : Additive (RelativeBrGroup K F) ≃+
    Additive (Fˣ⧸(Units.map (Algebra.norm (S := K) F)).range) :=
  BrauerOverCyclic' F K τ hτ|>.toAddEquiv.trans
  sorry
