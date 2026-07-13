module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.Tactic.SuppressCompilation

/-!
# Cross product algebra: the underlying module and multiplication

This file constructs the cross product algebra `CrossProductAlgebra f` associated to a function
`f : Gal(K/F) × Gal(K/F) → Kˣ` of a field extension `K / F`: the free `K`-module on the basis
`Gal(K/F)`, equipped with the `F`-bilinear multiplication
`(c x_σ) * (d x_τ) = (c * σ d * f (σ, τ)) x_{στ}`.

Nothing in this file assumes that `f` is a 2-cocycle. The (associative) algebra structure and
central simplicity, which do, are in `BrauerGroup.Algebra.CrossProduct.CentralSimple`.

## References

* [*Advanced Algebra*]
-/

@[expose] public section

open Function Module

suppress_compilation

variable {R S F K : Type*} [Field F] [Field K] [Algebra F K] {f : Gal(K/F) × Gal(K/F) → Kˣ}

@[ext]
structure CrossProductAlgebra (f : Gal(K/F) × Gal(K/F) → Kˣ) where
  val : Gal(K/F) →₀ K

namespace CrossProductAlgebra
variable {x y : CrossProductAlgebra f}

lemma val_injective : Injective (val (f := f)) := fun _ _ ↦ CrossProductAlgebra.ext
lemma val_surjective : Surjective (val (f := f)) := fun x ↦ ⟨⟨x⟩, rfl⟩
lemma val_bijective : Bijective (val (f := f)) := ⟨val_injective, val_surjective⟩

@[simp] lemma val_inj : x.val = y.val ↔ x = y := val_injective.eq_iff

lemma «forall» {P : CrossProductAlgebra f → Prop} : (∀ x, P x) ↔ ∀ x, P (mk x) := by
  rw [val_surjective.forall]

instance : Nontrivial (CrossProductAlgebra f) := val_surjective.nontrivial

instance : Zero (CrossProductAlgebra f) where
  zero := ⟨0⟩

instance : Add (CrossProductAlgebra f) where
  add x y := ⟨x.val + y.val⟩

instance : Neg (CrossProductAlgebra f) where
  neg x := ⟨-x.val⟩

instance : Sub (CrossProductAlgebra f) where
  sub x y := ⟨x.val - y.val⟩

instance [Semiring R] [Module R K] : SMul R (CrossProductAlgebra f) where
  smul r x := ⟨r • x.val⟩

@[simp] lemma val_zero : (0 : CrossProductAlgebra f).val = 0 := rfl
@[simp] lemma val_add (x y : CrossProductAlgebra f) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_smul [Semiring R] [Module R K] (r : R) (x : CrossProductAlgebra f) :
    (r • x).val = r • x.val := rfl
@[simp] lemma val_neg (x : CrossProductAlgebra f) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : CrossProductAlgebra f) : (x - y).val = x.val - y.val := rfl

@[simp] lemma mk_zero : (mk 0 : CrossProductAlgebra f) = 0 := rfl
@[simp] lemma mk_add_mk (x y : Gal(K/F) →₀ K) :
    (mk x + mk y : CrossProductAlgebra f) = mk (x + y) := rfl
@[simp] lemma smul_mk [Semiring R] [Module R K] (r : R) (x : Gal(K/F) →₀ K) :
    (r • mk x : CrossProductAlgebra f) = mk (r • x) := rfl
@[simp] lemma neg_mk (x : Gal(K/F) →₀ K) : (- mk x : CrossProductAlgebra f) = mk (-x) := rfl
@[simp] lemma mk_sub_mk (x y : Gal(K/F) →₀ K) :
    (mk x - mk y : CrossProductAlgebra f) = mk (x - y) := rfl

instance addCommGroup : AddCommGroup (CrossProductAlgebra f) :=
  val_injective.addCommGroup val val_zero val_add val_neg val_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simps]
def valAddEquiv : CrossProductAlgebra f ≃+ (Gal(K/F) →₀ K) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := val_add

@[simp]
lemma val_finsuppSum {α M : Type*} [AddCommMonoid M] (g : α →₀ M)
    (h : α → M → CrossProductAlgebra f) :
    (g.sum h).val = g.sum (fun a m ↦ (h a m).val) := map_finsuppSum valAddEquiv ..

instance [Semiring R] [Module R K] : Module R (CrossProductAlgebra f) :=
  val_injective.module _ valAddEquiv.toAddMonoidHom val_smul

instance [Semiring R] [Semiring S] [Module R K] [Module S K] [Module R S] [IsScalarTower R S K] :
    IsScalarTower R S (CrossProductAlgebra f) where
  smul_assoc r s x := by ext; simp [smul_assoc]

@[simps]
def valLinearEquiv [Semiring R] [Module R K] : CrossProductAlgebra f ≃ₗ[R] (Gal(K/F) →₀ K) where
  __ := valAddEquiv
  map_smul' := val_smul

@[simps]
def basis : Basis Gal(K/F) K (CrossProductAlgebra f) where
  repr := valLinearEquiv

lemma basis_val (σ : Gal(K/F)) : (basis (f := f) σ).val = .single σ 1 := rfl
lemma mk_single_one (σ : Gal(K/F)) : mk (.single σ 1) = basis (f := f) σ := rfl

variable (f) in
def mulLinearMap : (Gal(K/F) →₀ K) →ₗ[F] (Gal(K/F) →₀ K) →ₗ[F] (Gal(K/F) →₀ K) :=
  Finsupp.lsum F fun σ =>
  { toFun c := Finsupp.lsum F fun τ =>
      { toFun d := .single (σ * τ) (c * σ d * f (σ, τ))
        map_add' := by simp [mul_add, add_mul]
        map_smul' := by simp only [map_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
          RingHom.id_apply, Finsupp.smul_single, implies_true] }
    map_add' _ _ := by ext; simp [add_mul]
    map_smul' _ _ := by ext; simp only [Algebra.smul_mul_assoc, Finsupp.lsum_comp_lsingle,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.coe_comp, comp_apply,
      Finsupp.lsingle_apply, LinearMap.smul_apply, Finsupp.coe_lsum, map_zero, mul_zero, zero_mul,
      Finsupp.single_zero, Finsupp.sum_single_index, Finsupp.smul_single] }

variable (f) in
@[simp]
lemma mulLinearMap_single_single (c d : K) (σ τ : Gal(K/F)) :
    mulLinearMap f (.single σ c) (.single τ d) = .single (σ * τ) (c * σ d * f (σ, τ)) := by
  simp [mulLinearMap]

variable (f) in
@[simp]
lemma mulLinearMap_single_left_apply (c : K) (σ : Gal(K/F)) (x : Gal(K/F) →₀ K) (τ : Gal(K/F)) :
    mulLinearMap f (.single σ c) x τ = c * σ (x (σ⁻¹ * τ)) * f (σ, σ⁻¹ * τ) := by
  classical simp +contextual [mulLinearMap, Finsupp.single_apply, ← eq_inv_mul_iff_mul_eq]

variable (f) in
@[simp]
lemma mulLinearMap_single_right_apply (c : K) (σ : Gal(K/F)) (x : Gal(K/F) →₀ K) (τ : Gal(K/F)) :
    mulLinearMap f x (.single σ c) τ = x (τ * σ⁻¹) * τ (σ⁻¹ c) * f (τ * σ⁻¹, σ) := by
  classical simp +contextual [mulLinearMap, Finsupp.single_apply, ← eq_mul_inv_iff_mul_eq]

instance : One (CrossProductAlgebra f) where
  one := ⟨.single 1 (f (1, 1))⁻¹⟩

instance : Mul (CrossProductAlgebra f) where
  mul x y := ⟨mulLinearMap f x.val y.val⟩

lemma one_def : (1 : CrossProductAlgebra f) = ⟨.single 1 (f (1, 1))⁻¹⟩ := rfl

@[simp] lemma val_one : (1 : CrossProductAlgebra f).val = .single 1 (f (1, 1))⁻¹ := rfl

@[simp]
lemma val_mul (x y : CrossProductAlgebra f) : (x * y).val = mulLinearMap f x.val y.val := rfl

@[simp] lemma mk_mul_mk (x y : Gal(K/F) →₀ K) :
    (mk x * mk y : CrossProductAlgebra f) = mk (mulLinearMap f x y) := rfl

lemma basis_smul_comm (σ : Gal(K/F)) (k1 k2 : K) (x : CrossProductAlgebra f) :
    (k1 • basis (f := f) σ) * (k2 • x) = σ k2 • k1 • basis σ * x := by
  apply val_injective
  simp only [basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, val_mul, val_smul, valAddEquiv_symm_apply_val,
    Finsupp.smul_single, smul_eq_mul, _root_.mul_one]
  induction x.val using Finsupp.induction_linear with
  | zero => simp
  | add _ _ _ _ => simp_all[smul_add]
  | single a b =>
    simp only [Finsupp.smul_single, smul_eq_mul, mulLinearMap_single_single, map_mul, ← mul_assoc,
      mul_comm k1 (σ k2)]

end CrossProductAlgebra
