module

public import Mathlib.RingTheory.Morita.Basic
public import BrauerGroup.Algebra.Algebra.Subalgebra.Basic
public import BrauerGroup.Algebra.Module.LinearMap.End
public import BrauerGroup.CategoryTheory.Endomorphism
public import BrauerGroup.RingTheory.Morita.Matrix
public import BrauerGroup.RingTheory.Morita.SimpleRing

/-!
# Morita equivalences, endomorphism rings and simple modules

A Morita equivalence `e` between `A` and `B` sends the endomorphism ring of an `A`-module `M`
to the endomorphism ring of the `B`-module `e.eqv.functor.obj M`, because the functor of an
equivalence is fully faithful.

## Main results

* `MoritaEquivalence.endRingEquiv`: a Morita equivalence between `A` and `B` induces a ring
  isomorphism `Module.End A M ≃+* Module.End B (e.eqv.functor.obj M)` for every `A`-module `M`.
* `end_simple_mod_of_wedderburn`: if `A ≃ₐ[k] Mₙ(D)` with `D` a division algebra, then the
  endomorphism algebra of the simple `A`-module `Dⁿ` is isomorphic to `Dᵐᵒᵖ`;
  `end_simple_mod_of_wedderburn'` generalizes this to an arbitrary simple `A`-module.
* `end_simple_mod_finite`: the endomorphism algebra of a simple module over a finite simple
  algebra `A` over a field `k` is finite-dimensional over `k`.
* `end_end_iso`: a finite simple algebra `A` over a field `k` is isomorphic to
  `Module.End (Module.End A M) M` for every simple `A`-module `M`, i.e. simple modules over a
  finite simple algebra are balanced.
* `finrank_mul_finrank_end`: the dimension formula for a finite simple algebra `A` over a field
  `k`: if `M` is a simple `A`-module and `L = Module.End A M`, then
  `dim_k A * dim_k L = (dim_k M) ^ 2`.
-/

@[expose] public section

universe w u v

open CategoryTheory

namespace MoritaEquivalence

variable {R : Type u} [CommSemiring R] {A : Type v} [Ring A] [Algebra R A]
  {B : Type w} [Ring B] [Algebra R B]

/-- A Morita equivalence `e : MoritaEquivalence R A B` induces a ring isomorphism
`Module.End A M ≃+* Module.End B (e.eqv.functor.obj M)` for every `A`-module `M`. -/
noncomputable def endRingEquiv (e : MoritaEquivalence R A B) (M : ModuleCat A) :
    Module.End A M ≃+* Module.End B (e.eqv.functor.obj M) :=
  (ModuleCat.endRingEquiv M).symm.trans <|
    (e.eqv.fullyFaithfulFunctor.ringEquivEnd M).trans (ModuleCat.endRingEquiv _)

@[simp]
lemma endRingEquiv_apply_apply (e : MoritaEquivalence R A B) (M : ModuleCat A)
    (f : Module.End A M) (x : e.eqv.functor.obj M) : (e.endRingEquiv M f) x =
    (e.eqv.functor.map (ModuleCat.ofHom f)).hom x := rfl

end MoritaEquivalence

variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] [IsSimpleRing A]
  [Module.Finite k A]

open Matrix.Module

omit [IsSimpleRing A] [Module.Finite k A] in
lemma compatible1 (n : ℕ) (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    [Module A (Fin n → D)] (smul_def : ∀ (a : A) (v : Fin n → D), a • v = wdb a • v) :
    LinearMap.CompatibleSMul (Fin n → D) (Fin n → D) (Matrix (Fin n) (Fin n) D) A where
  map_smul f M v := by
    rw [show M • v = wdb.symm M • v by simp [smul_def], map_smul, smul_def, wdb.apply_symm_apply]

omit [IsSimpleRing A] [Module.Finite k A] in
lemma compatible2 (n : ℕ) (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    [Module A (Fin n → D)] (smul_def : ∀ (a : A) (v : Fin n → D), a • v = wdb a • v) :
    LinearMap.CompatibleSMul (Fin n → D) (Fin n → D) A (Matrix (Fin n) (Fin n) D) where
  map_smul f M v := by rw [smul_def, smul_def, map_smul]

/-- `LinearMap.restrictScalars` is a linear map itself on `Module.End S M` -/
@[simps]
def Module.End.restrictScalarsLin {R₀ R S M : Type*} [CommSemiring R₀] [Semiring R] [Semiring S]
    [Algebra R₀ S] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M] [Module S M]
    [IsScalarTower R₀ R M] [IsScalarTower R₀ S M] [LinearMap.CompatibleSMul M M R S] :
    (M →ₗ[S] M) →ₗ[R₀] (M →ₗ[R] M) where
  toFun f := f.restrictScalars R
  map_add' := by simp
  map_smul' := by simp

/-- AlgEquiv between endomorphism rings by basechange -/
abbrev endCatEquiv (n : ℕ)
    (D : Type w) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    [Module A (Fin n → D)] (smul_def : ∀ (a : A) (v : Fin n → D), a • v = wdb a • v)
    [IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D)] [IsScalarTower k A (Fin n → D)]
    [SMulCommClass A k (Fin n → D)] :
    Module.End A (Fin n → D) ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  have := compatible1 k A n D wdb smul_def
  have := compatible2 k A n D wdb smul_def
  .ofAlgHom (AlgHom.ofLinearMap Module.End.restrictScalarsLin rfl (by intros; ext; simp))
  (AlgHom.ofLinearMap Module.End.restrictScalarsLin rfl (by intros; ext; simp))
  (by rfl) (by rfl)

/-- The `k`-algebra isomorphism between `End D D` and `End Mₙ(D) Dⁿ` induced by the Morita
equivalence between `D` and `Mₙ(D)`. -/
@[stacks 074E "(4) second part"]
noncomputable def Module.End.matAlgEquiv (n : ℕ) [NeZero n] (D : Type w)
    [DivisionRing D] [Algebra k D] :
    Module.End D D ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  .ofRingEquiv (f := (moritaEquivalenceMatrix D k (ι := Fin n) 0).endRingEquiv (.of D D))
    fun _ ↦ LinearMap.ext <| fun _ ↦ MoritaEquivalence.endRingEquiv_apply_apply ..

open IsSimpleRing

@[stacks 074E "(3) first part"]
noncomputable def end_simple_mod_of_wedderburn (n : ℕ) [NeZero n] (D : Type w) [DivisionRing D]
    [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
    Module.End A (Fin n → D) ≃ₐ[k] Dᵐᵒᵖ :=
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  (endCatEquiv k A n D wdb (fun _ _ ↦ rfl)).trans <| (Module.End.matAlgEquiv k n D).symm.trans
    (AlgEquiv.moduleEndSelf k (A := D)).symm

lemma end_simple_mod_of_wedderburn' (n : ℕ) [NeZero n] (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) (M : Type w) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    Nonempty (Module.End A M ≃ₐ[k] Dᵐᵒᵖ) :=
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A D wdb
  ⟨(linearEquiv_of_isSimpleModule_over_simple_ring A M (Fin n → D)|>.some.conjAlgEquiv (R := k)
    (S := A) (M₁ := M) (M₂ := Fin n → D)).trans <| end_simple_mod_of_wedderburn k A n D wdb⟩

@[stacks 074E "(5) part 2"]
instance end_simple_mod_finite (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] : Module.Finite k (Module.End A M) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  exact (Module.Finite.equiv_iff (MulOpposite.opLinearEquiv k (M := D) ≪≫ₗ
    (end_simple_mod_of_wedderburn' k A n D e M).some.symm.toLinearEquiv)).1 ‹_›

omit [IsSimpleRing A] in
open Submodule.IsPrincipal in
lemma gen_ne_zero (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    generator (R := A) (M := M) ⊤ ≠ 0 := fun h ↦ bot_ne_top.symm <|
  (eq_bot_iff_generator_eq_zero ⊤).2 h

omit [IsSimpleRing A] in
open Submodule.IsPrincipal in
lemma gen_spec (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] (m' : M) :
    ∃ a : A, m' = a • generator (R := A) (M := M) ⊤ := by
  simpa [Submodule.mem_span_singleton, eq_comm] using
    Submodule.ext_iff.1 (IsSimpleModule.span_singleton_eq_top A (M := M) (gen_ne_zero A M)) m'

/-- map from `A` to `End (End A M) M` induced by `a • ·` -/
@[simps]
def toEndEnd (M : Type*) [AddCommGroup M] [Module A M] : A →ₗ[A] Module.End (Module.End A M) M where
  toFun a := DistribSMul.toLinearMap _ _ a
  map_add' _ _ := by ext; simp [add_smul]
  map_smul' _ _ := by ext; simp [mul_smul]

/-- the map induced by `a • ·` is an alghom -/
@[simps]
def toEndEndAlgHom (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    A →ₐ[k] Module.End (Module.End A M) M where
  __ := toEndEnd A M
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_smul]
  map_zero' := by ext; simp
  commutes' a := by ext; simp

open Submodule.IsPrincipal in
instance (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Nontrivial (Module.End (Module.End A M) M) where
  exists_pair_ne := ⟨0, 1, fun eq ↦ gen_ne_zero A M congr($eq (generator (R := A) (M := M) ⊤)).symm⟩

omit [Module.Finite k A] in
lemma toEndEnd_injective
    (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Function.Injective (toEndEnd A M) :=
  RingHom.injective (toEndEndAlgHom k A M).toRingHom

/-- the definition of a balanced module (slightly different from literature) -/
class IsBalanced (M : Type*) [AddCommGroup M] [Module A M] : Prop where
  surj : Function.Surjective (toEndEnd A M)

instance : IsBalanced A A where
  surj f := by
    refine ⟨f 1, ?_⟩
    ext x
    simp only [toEndEnd_apply, DistribSMul.toLinearMap_apply, smul_eq_mul]
    let X : Module.End A A := LinearMap.mulRight _ x
    simpa [Module.End.smul_def, LinearMap.coe_mk, AddHom.coe_mk, one_mul, X]
      using (f.map_smul X 1).symm

omit [IsSimpleRing A] in
lemma IsBalanced.congr_aux (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (l : M ≃ₗ[A] N) (h : IsBalanced A M) : IsBalanced A N := by
  refine ⟨fun a => ?_⟩
  obtain ⟨b, hb⟩ := h.1 <| l.conjAddEquiv.symm a
  refine ⟨b, LinearMap.ext fun n ↦ ?_⟩
  have := congr(l $(by simpa using congr($hb <| l.symm n)))
  simp_all

omit [IsSimpleRing A] in
lemma IsBalanced.congr {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (l : M ≃ₗ[A] N) : IsBalanced A M ↔ IsBalanced A N :=
  ⟨IsBalanced.congr_aux _ _ _ l, IsBalanced.congr_aux _ _ _ l.symm⟩

@[simps]
private noncomputable def Module.End.of_coord {ι} (M : Type*) [AddCommGroup M] [Module A M]
    (f : Module.End A (ι →₀ M)) (i j : ι) : Module.End A M where
  toFun m := f (Finsupp.single i m) j
  map_add' := by simp
  map_smul' a m := by simp [RingHom.id_apply, ← Finsupp.smul_single]

@[simps!]
private noncomputable def Module.End.End_map {ι} (M : Type*) [AddCommGroup M] [Module A M]
    (g : Module.End (Module.End A M) M) : Module.End (Module.End A (ι →₀ M)) (ι →₀ M) where
  __ := Finsupp.mapRange.linearMap g
  map_smul' f v := Finsupp.ext fun i ↦ by
    classical
    simp only [End.smul_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, RingHom.id_apply]
    have eq (i j k : ι) : g ((f (.single i (v k))) j) = (f (.single i (g (v k)))) j := by
      simpa using g.map_smul (Module.End.of_coord A M f i j) (v k)
    conv_lhs => rw [← Finsupp.sum_single v]
    simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, eq]
    rw [← Finset.sum_apply, ← Finsupp.coe_finsetSum, ← map_sum]
    congr
    simp_all [Finsupp.ext_iff, Finsupp.single_apply]

lemma isBalanced_of_simpleMod (k : Type u) [Field k] (A M : Type v) [Ring A] [IsSimpleRing A]
    [Algebra k A] [Module.Finite k A] [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    IsBalanced A M := by
  classical
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨ι, ⟨e⟩⟩ := directSum_simple_module_over_simple_algebra' A A M
  have b : IsBalanced A (ι →₀ M) := IsBalanced.congr A e |>.1 inferInstance
  refine ⟨fun g => ?_⟩
  obtain ⟨a, ha⟩ := b.1 (Module.End.End_map A M g)
  refine ⟨a, LinearMap.ext fun m ↦ ?_⟩
  obtain ⟨i⟩ : Nonempty ι := not_isEmpty_iff.1 fun _ ↦ one_ne_zero <|
    @Subsingleton.elim A e.toEquiv.subsingleton 1 0
  have : a • m = g m := by
    have := Finsupp.ext_iff.1 (by simpa using congr($ha (Finsupp.single i m))) i
    simpa using this
  simp [this]

@[stacks 074E "(6)"]
noncomputable def end_end_iso
    (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    A ≃ₐ[k] Module.End (Module.End A M) M :=
  AlgEquiv.ofBijective (toEndEndAlgHom k A M) ⟨toEndEnd_injective k A M,
    isBalanced_of_simpleMod k A M |>.1⟩

@[stacks 074E "(5) part 3"]
private noncomputable def end_end_center_equiv (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    Subalgebra.center k (Module.End (Module.End A M) M) ≃ₐ[k] Subalgebra.center k A :=
  Subalgebra.centerCongr (end_end_iso k A M).symm

section dimensionFormula

/-- If `A ≃ₐ[k] Mₙ(D)`, then the endomorphism algebra of any simple `A`-module has the same
dimension over `k` as `D`. -/
lemma finrank_end_of_wedderburn (n : ℕ) [NeZero n] (D : Type w) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) (M : Type w) [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    Module.finrank k (Module.End A M) = Module.finrank k D :=
  ((end_simple_mod_of_wedderburn' k A n D wdb M).some.toLinearEquiv ≪≫ₗ
    (MulOpposite.opLinearEquiv k (M := D)).symm).finrank_eq

/-- If `A ≃ₐ[k] Mₙ(D)`, then any simple `A`-module has dimension `n * dim_k D` over `k`. -/
lemma finrank_simple_mod_of_wedderburn (n : ℕ) [NeZero n] (D : Type w) [DivisionRing D]
    [Algebra k D] [Module.Finite k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) (M : Type w)
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    Module.finrank k M = n * Module.finrank k D := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A D wdb
  obtain ⟨eM⟩ := linearEquiv_of_isSimpleModule_over_simple_ring A M (Fin n → D)
  rw [(eM.restrictScalars k).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

@[stacks 074E "(5) part 4"]
theorem finrank_mul_finrank_end (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Module.finrank k A * Module.finrank k (Module.End A M) = Module.finrank k M ^ 2 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, _, _, _, ⟨wdb⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  have hA : Module.finrank k A = n * n * Module.finrank k D := by
    rw [wdb.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin]
  rw [hA, finrank_end_of_wedderburn k A n D wdb M, finrank_simple_mod_of_wedderburn k A n D wdb M]
  ring

end dimensionFormula
