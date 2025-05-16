import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

universe v u

open CategoryTheory

variable (R : Type u) [CommRing R] (S₁ : ShortComplex (ModuleCat.{v} R))
  (S₂ : ShortComplex (ModuleCat R)) (f : S₁ ⟶ S₂)

abbrev φK : ↥(LinearMap.ker (ModuleCat.Hom.hom S₁.g)) →ₗ[R]
    ↥(LinearMap.ker (ModuleCat.Hom.hom S₂.g)) :=
  LinearMap.restrict f.2.hom
    <| fun x hx ↦ by
      have := (LinearMap.ext_iff.1 <| ModuleCat.hom_ext_iff|>.1 f.5) x
      simp at hx
      simp [hx] at this
      simp [this]

abbrev φH : ModuleCat.of R (↥(LinearMap.ker (ModuleCat.Hom.hom S₁.g)) ⧸ LinearMap.range S₁.moduleCatToCycles) ⟶
    ModuleCat.of R (↥(LinearMap.ker (ModuleCat.Hom.hom S₂.g)) ⧸ LinearMap.range S₂.moduleCatToCycles) :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ (φK _ _ _ f) <| fun ⟨x, hx1⟩ ⟨y, hy⟩ ↦ by
    simp [φK]
    simp_rw [Subtype.ext_iff] at hy ⊢
    simp at hy⊢
    rw [← hy]
    change ∃ y', _ = ModuleCat.Hom.hom _ (ModuleCat.Hom.hom S₁.f _)
    simp_rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    rw [← f.4]
    simp

@[simps]
def LeftHomologyMapData.ofModuleCat :
    ShortComplex.LeftHomologyMapData f
    (ShortComplex.moduleCatLeftHomologyData S₁)
    (ShortComplex.moduleCatLeftHomologyData S₂) where
  φK := ModuleCat.ofHom <| φK R S₁ S₂ f
  φH := φH R S₁ S₂ f
  commi := ModuleCat.hom_ext <| LinearMap.ext <| fun ⟨x, hx⟩ ↦ by simp
  commf' := ModuleCat.hom_ext <| LinearMap.ext <| fun x ↦ by
    simp
    rw [Subtype.ext_iff]
    simp only [LinearMap.restrict_coe_apply, ShortComplex.moduleCatToCycles_apply_coe]
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, f.4]
  commπ := ModuleCat.hom_ext <| LinearMap.ext <| fun ⟨x, hx⟩ ↦ by simp

def ShortComplex.IsQuasiIsoAt_iff_moduleCat: ShortComplex.QuasiIso f ↔
  ((∀ (a : ↑S₁.X₂), (ModuleCat.Hom.hom S₁.g) a = 0 →
    ∀ (x : ↑S₂.X₁), (ConcreteCategory.hom S₂.f) x = (ModuleCat.Hom.hom f.τ₂) a →
    ∃ y, (ConcreteCategory.hom S₁.f) y = a)) ∧
  ((∀ (a : ↑S₂.X₂), (ModuleCat.Hom.hom S₂.g) a = 0 →
    ∃ a_1, (ModuleCat.Hom.hom S₁.g) a_1 = 0 ∧
    ∃ y, (ConcreteCategory.hom S₂.f) y = (ModuleCat.Hom.hom f.τ₂) a_1 - a)) := by
  rw [ShortComplex.LeftHomologyMapData.quasiIso_iff (LeftHomologyMapData.ofModuleCat R S₁ S₂ f)]
  rw [ConcreteCategory.isIso_iff_bijective, Function.Bijective]
  congr!
  · rw [injective_iff_map_eq_zero]
    refine (Submodule.Quotient.mk_surjective _).forall.trans ?_
    simp [Subtype.ext_iff, SetLike.le_def]
  · refine (Submodule.Quotient.mk_surjective _).forall.trans ?_
    simp [Function.Surjective, SetLike.le_def, Subtype.ext_iff,
      (Submodule.Quotient.mk_surjective _).exists, Submodule.Quotient.eq]

  -- ShortComplex.LeftHomologyMapData.quasiIso_iff
  --   (LeftHomologyMapData.ofModuleCat R S₁ S₂ f)|>.2 <| by
  --   rw [ConcreteCategory.isIso_iff_bijective]
  --   refine ⟨?_, sorry⟩
  --   rw [injective_iff_map_eq_zero]
  --   rintro x hx
  --   obtain ⟨⟨x, hx1⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  --   simp [Subtype.ext_iff] at hx
  --   simp [Subtype.ext_iff]
    -- obtain ⟨⟨x2, hx2⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x2
    -- simp [Submodule.Quotient.eq] at h12
