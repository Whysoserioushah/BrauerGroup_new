module

public import BrauerGroup.Algebra.Split.Basic
public import BrauerGroup.RingTheory.SimpleRing.Basic
public import BrauerGroup.RingTheory.SimpleRing.Centralizer

variable {k A L : Type*} [Field k] [Ring A] [Algebra k A] [Module.Finite k A]
  [Field L] [Algebra k L] (f : L →ₐ[k] A)

open scoped TensorProduct

private abbrev rightMod : Module L A where
  smul l a := a * f l
  mul_smul l1 l2 a := show a * f (l1 * l2) = a * f l2 * f l1 by
    rw [mul_comm, map_mul, ← mul_assoc]
  one_smul a := show a * f 1 = a by rw [map_one, mul_one]
  smul_zero l := show 0 * f l = 0 by rw [zero_mul]
  smul_add l a1 a2 := show (a1 + a2) * f l = a1 * f l + a2 * f l by rw [add_mul]
  add_smul l1 l2 a := show a * f (l1 + l2) = a * f l1 + a * f l2 by rw [map_add, mul_add]
  zero_smul a := show a * f 0 = 0 by rw [map_zero, mul_zero]

omit [Module.Finite k A] in
private lemma rightMod.smul_def (l : L) (a : A) :
    letI := rightMod f; (l • a : A) = a * f l := rfl

private abbrev scalarTower :
    letI := rightMod f; IsScalarTower k L A :=
  let : Module L A := rightMod f
  { smul_assoc k l a := show a * _ = k • (a * _) by simp}

open Algebra.IsCentralSimple

private lemma finrank_eq_deg [IsSimpleRing A] [Algebra.IsCentral k A]
    (hL : Module.finrank k A = Module.finrank k L * Module.finrank k L) :
    letI := rightMod f; Module.finrank L A = degree k A := by
  let := rightMod f
  have := scalarTower f
  have : Module.Finite L A := Module.Finite.right k L A
  simp only [← degree_sq_eq_finrank k A, ← pow_two, zero_le, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_left_inj₀] at hL
  have := hL ▸ Module.finrank_mul_finrank k L A
  rw [← degree_sq_eq_finrank k A] at this
  simpa [pow_two, ne_of_gt (degree_pos k A)] using this

include f in
public lemma Algebra.IsCentralSimple.split_of_finrank [IsSimpleRing A] [Algebra.IsCentral k A]
    (hL : Module.finrank k A = Module.finrank k L * Module.finrank k L) :
    Algebra.IsSplit k A L := by
  set n := Algebra.IsCentralSimple.degree k A with hn
  let : Module L A := rightMod f
  have := scalarTower f
  have : Module.Finite L A := Module.Finite.right k L A
  refine ⟨n, ne_of_gt (degree_pos k A), ⟨AlgEquiv.trans ?_
    (algEquivMatrix (Module.finBasisOfFinrankEq L A (finrank_eq_deg f hL)))⟩⟩
  let φ1 : A →ₐ[k] Module.End L A := {
    toFun a := {
      toFun := (a * ·)
      map_add' := by simp [mul_add]
      map_smul' := by simp [rightMod.smul_def, mul_assoc]
    }
    map_one' := by ext; simp
    map_mul' _ _ := by ext; simp [mul_assoc]
    map_zero' := by ext; simp
    map_add' _ _ := by ext; simp [add_mul]
    commutes' r := by ext; simp [Algebra.smul_def] }
  let φ : L ⊗[k] A →ₐ[L] Module.End L A := Algebra.TensorProduct.lift (Algebra.ofId L _) φ1 <| by
    simp [commute_iff_eq, LinearMap.ext_iff]
  refine AlgEquiv.ofBijective φ (φ.bijective_of_finrank_eq ?_)
  simp [Module.finrank_linearMap, finrank_eq_deg f hL, ← pow_two, degree_sq_eq_finrank k A]

include f in
/-- A field embedding into a finite-dimensional central simple algebra has degree at most the
degree of the algebra: the range is a commutative simple subalgebra contained in its own
centralizer, whose dimensions are complementary. -/
private lemma finrank_le_degree [IsSimpleRing A] [Algebra.IsCentral k A] :
    Module.finrank k L ≤ degree k A := by
  have finj : Function.Injective f := f.toRingHom.injective
  haveI : IsSimpleRing ↥f.range :=
    .of_ringEquiv (AlgEquiv.ofInjective f finj).toRingEquiv inferInstance
  haveI : IsMulCommutative ↥f.range := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (by simp [← map_mul, mul_comm])⟩⟩
  have hrange : Module.finrank k ↥f.range = Module.finrank k L :=
    ((AlgEquiv.ofInjective f finj).toLinearEquiv.finrank_eq).symm
  have h27 := Subalgebra.finrank_centralizer_mul_finrank (F := k) (A := A) f.range
  rw [hrange] at h27
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
  rw [degree_sq_eq_finrank k A, pow_two, ← h27]
  exact Nat.mul_le_mul_right _ (hrange ▸ Submodule.finrank_mono
    (Subalgebra.toSubmodule.le_iff_le.2
      ((Subalgebra.le_centralizer_iff_isMulCommutative f.range).2 inferInstance)))

/-- The size of the matrix algebra in a splitting isomorphism is the degree. -/
private lemma matrix_size_eq_degree [IsSimpleRing A] [Algebra.IsCentral k A] {m : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin m) (Fin m) L) : m = degree k A := by
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h1
  simp only [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin,
    ← pow_two, ← degree_sq_eq_finrank k A] at h1
  exact ((pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) two_ne_zero).1 h1).symm

/-- A finite-dimensional central division algebra split by `L` has degree at most
`finrank k L`: the simple module of the split algebra is a nonzero free `D`-module of
`k`-dimension `(degree k D) * finrank k L`. -/
private lemma degree_le_finrank {D : Type*} [DivisionRing D] [Algebra k D]
    [Module.Finite k D] [Algebra.IsCentral k D] [Module.Finite k L] {m : ℕ} (hm : m ≠ 0)
    (e : L ⊗[k] D ≃ₐ[L] Matrix (Fin m) (Fin m) L) : degree k D ≤ Module.finrank k L := by
  let Φ : (L ⊗[k] D) →ₐ[L] Module.End L (Fin m → L) :=
    (algEquivMatrix' (R := L)).symm.toAlgHom.comp e.toAlgHom
  let : Module D (Fin m → L) :=
    Module.compHom _ (Φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  haveI : IsScalarTower k D (Fin m → L) := ⟨fun c x v ↦ by
    change Φ ((1 : L) ⊗ₜ[k] (c • x)) v = c • Φ ((1 : L) ⊗ₜ[k] x) v
    rw [TensorProduct.tmul_smul, ← algebraMap_smul L c ((1 : L) ⊗ₜ[k] x : L ⊗[k] D),
      map_smul, LinearMap.smul_apply, algebraMap_smul]⟩
  have : Module.Finite D (Fin m → L) := Module.Finite.of_restrictScalars_finite k D _
  have : Module.Free D (Fin m → L) := Module.Free.of_divisionRing D _
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  have hV : Module.finrank k (Fin m → L) = m * Module.finrank k L := by
    simp [Module.finrank_pi_fintype, Finset.sum_const, Fintype.card_fin, smul_eq_mul]
  have hkey : degree k D * (degree k D * Module.finrank D (Fin m → L)) =
      degree k D * Module.finrank k L := by
    rw [← mul_assoc, ← pow_two, degree_sq_eq_finrank k D,
      Module.finrank_mul_finrank k D (Fin m → L), hV, matrix_size_eq_degree e]
  calc degree k D = degree k D * 1 := (mul_one _).symm
    _ ≤ degree k D * Module.finrank D (Fin m → L) :=
        Nat.mul_le_mul_left _ Module.finrank_pos
    _ = Module.finrank k L := Nat.eq_of_mul_eq_mul_left (degree_pos k D) hkey

/-- For a finite-dimensional central **division** algebra `D` over `k`, a field `L` admitting
an embedding `g : L →ₐ[k] D` splits `D` if and only if
`finrank k D = finrank k L * finrank k L`, i.e. iff `L` embeds as a maximal subfield.

The division hypothesis is essential: `M₂(k)` is split by `L = k` but has dimension `4`. -/
public lemma DivisionRing.split_iff_finrank {D : Type*} [DivisionRing D]
    [Algebra k D] [Module.Finite k D] [Algebra.IsCentral k D] (g : L →ₐ[k] D) :
    Algebra.IsSplit k D L ↔ Module.finrank k D = Module.finrank k L * Module.finrank k L := by
  refine ⟨fun ⟨m, hm, ⟨e⟩⟩ ↦ ?_, fun h ↦ split_of_finrank g h⟩
  haveI : Module.Finite k L := Module.Finite.of_injective g.toLinearMap g.toRingHom.injective
  rw [le_antisymm (finrank_le_degree g) (degree_le_finrank hm e), ← pow_two,
    degree_sq_eq_finrank k D]
