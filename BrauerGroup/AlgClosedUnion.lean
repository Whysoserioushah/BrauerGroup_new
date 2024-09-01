import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Flat.Basic

import BrauerGroup.Quaternion

suppress_compilation

open TensorProduct

universe u

section
variable (K K_bar: Type u) [Field K] [Field K_bar] [Algebra K K_bar] [IsAlgClosure K K_bar]

variable (A : Type u) [AddCommGroup A] [Module K A]

open scoped IntermediateField

def intermediateTensor (L : IntermediateField K K_bar) : Submodule K (K_bar ⊗[K] A) :=
  LinearMap.range (LinearMap.rTensor _ (L.val.toLinearMap) : L ⊗[K] A →ₗ[K] K_bar ⊗[K] A)

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 400000 in
def intermediateTensor' (L : IntermediateField K K_bar) : Submodule L (K_bar ⊗[K] A) :=
  LinearMap.range ({LinearMap.rTensor _ (L.val.toLinearMap) with
    map_smul' := fun l x => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x a =>
        simp only [smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          _root_.map_mul, IntermediateField.coe_val]
        rfl
      | add x y hx hy => aesop } : L ⊗[K] A →ₗ[L] K_bar ⊗[K] A)

def intermediateTensorEquiv (L : IntermediateField K K_bar) :
    intermediateTensor K K_bar A L ≃ₗ[K] L ⊗[K] A :=
  LinearEquiv.symm $ LinearEquiv.ofBijective
    (LinearMap.rangeRestrict _)
    ⟨by
      intro x y hxy
      simp only [LinearMap.rangeRestrict, Subtype.ext_iff, LinearMap.codRestrict_apply] at hxy
      refine Module.Flat.rTensor_preserves_injective_linearMap _
        (fun x y h => by simpa using h) hxy, LinearMap.surjective_rangeRestrict _⟩

omit [IsAlgClosure K K_bar] in
@[simp]
lemma intermediateTensorEquiv_apply_tmul (L : IntermediateField K K_bar)
      (x : L) (a : A) (h : x.1 ⊗ₜ[K] a ∈ intermediateTensor K K_bar A L) :
    intermediateTensorEquiv K K_bar A L ⟨_, h⟩ =
    x ⊗ₜ a := by
  simp only [intermediateTensorEquiv]
  convert LinearEquiv.ofBijective_symm_apply_apply _ _
  rfl

set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 400000 in
def intermediateTensorEquiv' (L : IntermediateField K K_bar) :
    intermediateTensor' K K_bar A L ≃ₗ[L] L ⊗[K] A where
  toFun := intermediateTensorEquiv K K_bar A L
  map_add' := map_add _
  map_smul' := by
    rintro x ⟨-, ⟨y, rfl⟩⟩
    simp only [RingHom.id_apply]
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, SetLike.mk_smul_mk, smul_zero]
      erw [map_zero]
      rw [smul_zero]
    | tmul y a =>
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, IntermediateField.coe_val, SetLike.mk_smul_mk, smul_tmul',
        intermediateTensorEquiv_apply_tmul, smul_eq_mul]
      exact intermediateTensorEquiv_apply_tmul K K_bar A L (x • y) a _
    | add y z hy hz =>
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, SetLike.mk_smul_mk, map_add,
        smul_add] at hy hz ⊢
      convert congr($hy + $hz) using 1
      · rw [← (intermediateTensorEquiv K K_bar A L).map_add]; rfl
      · rw [← smul_add, ← (intermediateTensorEquiv K K_bar A L).map_add]; rfl
  invFun := (intermediateTensorEquiv K K_bar A L).symm
  left_inv := (intermediateTensorEquiv K K_bar A L).left_inv
  right_inv := (intermediateTensorEquiv K K_bar A L).right_inv

omit [IsAlgClosure K K_bar] in
lemma mem_intermediateTensor_iff_mem_intermediateTensor'
    {L : IntermediateField K K_bar} {x : K_bar ⊗[K] A} :
    x ∈ intermediateTensor K K_bar A L ↔ x ∈ intermediateTensor' K K_bar A L := by
  simp only [intermediateTensor, LinearMap.mem_range, intermediateTensor', LinearMap.coe_mk,
    LinearMap.coe_toAddHom]

omit [IsAlgClosure K K_bar] in
lemma intermediateTensor_mono {L1 L2 : IntermediateField K K_bar} (h : L1 ≤ L2) :
    intermediateTensor K K_bar A L1 ≤ intermediateTensor K K_bar A L2 := by
  have e1 : (LinearMap.rTensor _ (L1.val.toLinearMap) : L1 ⊗[K] A →ₗ[K] K_bar ⊗[K] A) =
    (LinearMap.rTensor _ (L2.val.toLinearMap) : L2 ⊗[K] A →ₗ[K] K_bar ⊗[K] A) ∘ₗ
    (LinearMap.rTensor A (L1.inclusion h) : L1 ⊗[K] A →ₗ[K] L2 ⊗[K] A) := by
    rw [← LinearMap.rTensor_comp]; rfl
  delta intermediateTensor
  rw [e1, LinearMap.range_comp, Submodule.map_le_iff_le_comap]
  rintro _ ⟨x, rfl⟩
  simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    Submodule.mem_comap, LinearMap.mem_range, exists_apply_eq_apply]

private abbrev SetOfFinite : Set (IntermediateField K K_bar) :=
  {M | FiniteDimensional K M}

omit [IsAlgClosure K K_bar] in
lemma is_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1)
    (Set.range fun (L : SetOfFinite K K_bar) ↦ intermediateTensor K K_bar A L) := by
  rintro _ ⟨⟨L1, (hL1 : FiniteDimensional _ _)⟩, rfl⟩ _ ⟨⟨L2, (hL2 : FiniteDimensional _ _)⟩, rfl⟩
  refine ⟨intermediateTensor K K_bar A (L1 ⊔ L2), ⟨⟨L1 ⊔ L2, show FiniteDimensional _ _ from
    ?_⟩, rfl⟩, ⟨intermediateTensor_mono K K_bar A le_sup_left,
      intermediateTensor_mono K K_bar A le_sup_right⟩⟩
  · apply (config := { allowSynthFailures := true }) IntermediateField.finiteDimensional_sup <;>
    assumption

omit [IsAlgClosure K K_bar] in
lemma SetOfFinite_nonempty : (Set.range fun (L : SetOfFinite K K_bar) ↦
    intermediateTensor K K_bar A L).Nonempty := by
  refine ⟨intermediateTensor K K_bar A ⊥, ⟨⟨⊥, ?_⟩, rfl⟩⟩
  simp only [SetOfFinite, Set.mem_setOf_eq, IntermediateField.bot_toSubalgebra]
  infer_instance

/-- K_bar ⊗[K] A = union of all finite subextension of K ⊗ A -/
theorem inter_tensor_union :
    ⨆ (L : SetOfFinite K K_bar),
    (intermediateTensor K K_bar A L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  |zero => simp
  |tmul x a =>
    have fin0: FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional (by
      observe : IsAlgebraic K x
      exact Algebra.IsIntegral.isIntegral x)
    refine Submodule.mem_sSup_of_directed (SetOfFinite_nonempty K K_bar A) (is_direct K K_bar A) |>.2
      ⟨intermediateTensor K K_bar A K⟮x⟯, ⟨⟨⟨K⟮x⟯, fin0⟩, rfl⟩,
        ⟨(⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ ⊗ₜ a), by simp⟩⟩⟩
  |add x y hx hy =>
  apply AddMemClass.add_mem <;> assumption

theorem algclosure_element_in (x : K_bar ⊗[K] A): ∃(F : IntermediateField K K_bar),
    FiniteDimensional K F ∧ x ∈ intermediateTensor K K_bar A F := by
  have mem : x ∈ (⊤ : Submodule K _) := ⟨⟩
  rw [← inter_tensor_union K K_bar A] at mem
  obtain ⟨_, ⟨⟨⟨L, hL1⟩, rfl⟩, hL⟩⟩ := Submodule.mem_sSup_of_directed (SetOfFinite_nonempty K K_bar A)
    (is_direct K K_bar A)|>.1 mem
  refine ⟨L, ⟨hL1, hL⟩⟩

def subfieldOf (x : K_bar ⊗[K] A) : IntermediateField K K_bar :=
  algclosure_element_in K K_bar A x|>.choose

instance (x : K_bar ⊗[K] A): FiniteDimensional K (subfieldOf K K_bar A x) :=
  (algclosure_element_in K K_bar A _).choose_spec.1

theorem mem_subfieldOf (x : K_bar ⊗[K] A) : x ∈ intermediateTensor K K_bar A
    (subfieldOf K K_bar A x) := (algclosure_element_in K K_bar A _).choose_spec.2

theorem mem_subfieldOf' (x : K_bar ⊗[K] A) : x ∈ intermediateTensor' K K_bar A
    (subfieldOf K K_bar A x) := by
  rw [← mem_intermediateTensor_iff_mem_intermediateTensor']
  exact mem_subfieldOf K K_bar A x

end

namespace lemma_tto
/-
%% LyX 2.4.1 created this file.  For more info, see https://www.lyx.org/.
%% Do not edit unless you really know what you are doing.
\documentclass[oneside,american]{amsart}
\usepackage[T1]{fontenc}
\usepackage[utf8]{luainputenc}
\usepackage{amstext}
\usepackage{amsthm}

\makeatletter
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Textclass specific LaTeX commands.
\numberwithin{equation}{section}
\numberwithin{figure}{section}
\theoremstyle{plain}
\newtheorem{thm}{\protect\theoremname}
\theoremstyle{plain}
\newtheorem{lem}[thm]{\protect\lemmaname}
\theoremstyle{definition}
\newtheorem{defn}[thm]{\protect\definitionname}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% User specified LaTeX commands.
\DeclareMathOperator{\Hom}{Hom}

\makeatother

\usepackage{babel}
\providecommand{\definitionname}{Definition}
\providecommand{\lemmaname}{Lemma}
\providecommand{\theoremname}{Theorem}

\begin{document}
\title{Galois Descent}

\maketitle
\tableofcontents{}

\section*{Some preliminary stuff}

In this section, let $K/k$ be a field extension and $V$ a $k$-vector
space. We sometimes use $V_{K}$ to denote the $K$-vector space $K\otimes_{k}V$.
We write $V^{\otimes_{k}^{p}}$ for $\underbrace{V\otimes_{k}\cdots\otimes_{k}V}_{p\text{ times}}$
when we feel like we need to stress the base field; or just $V^{\otimes^{p}}$
when $k$ is clear.
\begin{lem}
\label{lem:some-useful-basis}Some basis:
\begin{enumerate}
\item if $\mathcal{B}$ is a $k$-basis of $V$, then $\{1\otimes\bigotimes_{j=1}^{p}v_{j}|v_{j}\in\mathcal{B}\}$
is a basis for $K\otimes_{k}V^{\otimes^{p}}$;
\item if $\mathcal{B}$ is a $k$-basis of $V$,then $\{\bigotimes_{j=1}^{p}(1\otimes v_{j})|v_{j}\in\mathcal{B}\}$
is a basis for $(K\otimes_{k}V)^{\otimes_{K}^{p}}$.
\end{enumerate}
\end{lem}

\begin{lem}
\label{lem:some-useful-isos}Some isomorphisms:
\end{lem}

\begin{enumerate}
\item for any natural number $p$, we have $(K\otimes_{k}V)^{\otimes_{K}^{p}}\cong K\otimes_{k}V^{\otimes_{k}^{p}}$,
in another word the notation $V_{K}^{\otimes^{p}}$ is not ambiguous.
\end{enumerate}
\begin{proof}
I believe there is no canonical isomorphisms here, i.e. we need to
choose a basis $\mathcal{B}$ for $V$ and use lemma \ref{lem:some-useful-basis}.
\end{proof}

\section{Tensor of type $(p,q)$}

In this section, let $K/k$ be a field extension and $V$ a $k$-vector
space.
\begin{defn}
A tensor $\Phi$ of type $(p,q)$ is an element $\Hom_{k}(V^{\otimes q},V^{\otimes p})$,
i.e. a $k$-linear map from $\underbrace{V\otimes\cdots\otimes V}_{q\text{ times}}$
to $\underbrace{V\otimes\cdots\otimes V}_{p\text{ times}}$.

When $V$ is finite dimensional, a tensor of type $(p,q)$ is the
same as $V^{\otimes^{p}}\otimes_{k}\text{(}V^{\star}\text{)}^{\otimes^{q}}$.
The map from $V^{\otimes^{p}}\otimes_{k}\text{(}V^{\star}\text{)}^{\otimes^{q}}$
to $\Hom_{k}(V^{\otimes q},V^{\otimes p})$ is $x\otimes f\mapsto v_{1}\otimes\cdots\otimes
  v_{q}\mapsto f(v_{1})f(v_{2})...f(v_{q})x$
where $f$ is seen as $\text{(}V^{\otimes^{q}}\text{)}^{\star}$.
\end{defn}


\section{$k$-objects and $k$-morphisms}

In this section, let $k$ be a field and $V$ a $k$-vector space.
\end{document}

-/
variable (n : ℕ) [NeZero n] (k k_bar A : Type u) [Field k] [Field k_bar] [Algebra k k_bar]
  [IsAlgClosure k k_bar] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (iso : k_bar ⊗[k] A ≃ₐ[k_bar] Matrix (Fin n) (Fin n) k_bar)

def ee : Basis (Fin n × Fin n) k_bar (k_bar ⊗[k] A) :=
  Basis.map (Matrix.stdBasis k_bar _ _) iso.symm

local notation "e" => ee n k k_bar A iso


omit [NeZero n] [IsAlgClosure k k_bar] [FiniteDimensional k A] in
@[simp]
lemma ee_apply (i : Fin n × Fin n) : iso (e i) = Matrix.stdBasis k_bar (Fin n) (Fin n) i := by
  apply_fun iso.symm
  simp only [AlgEquiv.symm_apply_apply]
  have := Basis.map_apply (Matrix.stdBasis k_bar (Fin n) (Fin n)) iso.symm.toLinearEquiv i
  erw [← this]

def ℒℒ : IntermediateField k k_bar :=
  ⨆ (i : Fin n × Fin n), subfieldOf k k_bar A (e i)


local notation "ℒ" => ℒℒ n k k_bar A iso

instance : FiniteDimensional k ℒ :=
  IntermediateField.finiteDimensional_iSup_of_finite


def f (i : Fin n × Fin n) : subfieldOf k k_bar A (e i) →ₐ[k] ℒ :=
  subfieldOf k k_bar A (e i)|>.inclusion (le_sSup ⟨i, rfl⟩)

def e_hat' (i : Fin n × Fin n) : intermediateTensor' k k_bar A ℒ :=
  ⟨e i, by
    rw [← mem_intermediateTensor_iff_mem_intermediateTensor']
    exact intermediateTensor_mono k k_bar A
      (le_sSup (by simp)) $ mem_subfieldOf k k_bar A (e i)⟩

local notation "e^'" => e_hat' n k k_bar A iso
local notation "k⁻" => k_bar

omit [NeZero n] [FiniteDimensional k A] in
theorem e_hat_linear_independent : LinearIndependent ℒ e^' := by
  rw [linearIndependent_iff']
  intro s g h
  have h' : ∑ i ∈ s, algebraMap ℒ k⁻ (g i) • e i = 0 := by
    apply_fun Submodule.subtype _ at h
    simpa only [IntermediateField.algebraMap_apply, map_sum, map_smul, Submodule.coeSubtype,
      map_zero] using h

  have H := (linearIndependent_iff'.1 $ e |>.linearIndependent) s (algebraMap ℒ k⁻ ∘ g) h'
  intro i hi
  simpa using H i hi

-- shortcut instance search
set_option synthInstance.maxHeartbeats 40000 in
instance : Module ℒ (ℒ ⊗[k] A) := TensorProduct.leftModule

instance : FiniteDimensional ℒ (intermediateTensor' k k⁻ A ℒ) :=
    Module.Finite.equiv (intermediateTensorEquiv' k k_bar A ℒ).symm

omit [NeZero n] in
theorem dim_ℒ_eq : FiniteDimensional.finrank ℒ (intermediateTensor' k k⁻ A ℒ) = n^2 := by
    have eq1 := dim_eq k k⁻ A |>.trans iso.toLinearEquiv.finrank_eq
    simp only [FiniteDimensional.finrank_matrix, Fintype.card_fin] at eq1
    rw [pow_two, ← eq1, dim_eq k ℒ A]
    exact LinearEquiv.finrank_eq (intermediateTensorEquiv' k k_bar A ℒ)

def e_hat : Basis (Fin n × Fin n) ℒ (intermediateTensor' k k_bar A ℒ) :=
  basisOfLinearIndependentOfCardEqFinrank (e_hat_linear_independent n k k_bar A iso) $ by
    simp only [Fintype.card_prod, Fintype.card_fin, dim_ℒ_eq, pow_two]

local notation "e^" => e_hat n k k_bar A iso

def isoRestrict' : ℒ ⊗[k] A ≃ₗ[ℒ] Matrix (Fin n) (Fin n) ℒ :=
  (intermediateTensorEquiv' k k_bar A ℒ).symm ≪≫ₗ
  Basis.equiv (e^) (Matrix.stdBasis ℒ (Fin n) (Fin n)) (Equiv.refl _)

set_option synthInstance.maxHeartbeats 50000 in
instance : SMulCommClass k ℒ ℒ := inferInstance
-- instance : Algebra ℒ (ℒ ⊗[k] A) := Algebra.TensorProduct.leftAlgebra

def inclusion : ℒ ⊗[k] A →ₐ[ℒ] k⁻ ⊗[k] A :=
  Algebra.TensorProduct.map (Algebra.ofId ℒ k⁻) (AlgHom.id k A)

def inclusion' : Matrix (Fin n) (Fin n) ℒ →ₐ[ℒ] Matrix (Fin n) (Fin n) k⁻ :=
  AlgHom.mapMatrix (Algebra.ofId ℒ _)

omit [NeZero n] [FiniteDimensional k A] in
lemma inclusion'_injective : Function.Injective (inclusion' n k k_bar A iso) := by
  intro x y h
  ext i j
  rw [← Matrix.ext_iff] at h
  specialize h i j
  simp only [inclusion', Algebra.ofId, AlgHom.mapMatrix_apply, AlgHom.coe_mk, Matrix.map_apply,
    IntermediateField.algebraMap_apply, SetLike.coe_eq_coe] at h
  rw [h]

omit [NeZero n] [FiniteDimensional k A] in
/--
ℒ ⊗_k A ------>  intermidateTensor
  |              /
  | inclusion  /
  v          /
k⁻ ⊗_k A  <-
-/
lemma comm_triangle :
    (intermediateTensor' k k_bar A ℒ).subtype ∘ₗ
    (intermediateTensorEquiv' k k_bar A ℒ).symm.toLinearMap =
    (inclusion n k k_bar A iso).toLinearMap := by
  ext a
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, Submodule.coeSubtype, LinearEquiv.coe_coe, Function.comp_apply, inclusion,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.coe_id, id_eq]
  simp only [intermediateTensorEquiv', intermediateTensorEquiv, LinearEquiv.symm_symm,
    LinearEquiv.coe_symm_mk]
  rfl

/--
intermidateTensor ----> M_n(ℒ)
  | val                 | inclusion'
  v                     v
k⁻ ⊗_k A ----------> M_n(k⁻)
          iso
-/
lemma comm_square' :
    iso.toLinearEquiv.toLinearMap.restrictScalars ℒ ∘ₗ
    (intermediateTensor' k k_bar A ℒ).subtype =
    (inclusion' n k k_bar A iso).toLinearMap ∘ₗ
    Basis.equiv (e^) (Matrix.stdBasis ℒ (Fin n) (Fin n)) (Equiv.refl _) := by
  apply Basis.ext (e^)
  intro i
  conv_lhs => simp only [AlgEquiv.toLinearEquiv_toLinearMap, e_hat,
    basisOfLinearIndependentOfCardEqFinrank,
    Basis.coe_mk, e_hat', LinearMap.coe_comp, LinearMap.coe_restrictScalars, Submodule.coeSubtype,
    Function.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  simp only [ee_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
  ext a b
  simp only [inclusion', AlgHom.mapMatrix_apply, Matrix.map_apply]
  simp only [Algebra.ofId, AlgHom.coe_mk, IntermediateField.algebraMap_apply]
  rw [Matrix.stdBasis_eq_stdBasisMatrix]
  erw [Matrix.stdBasis_eq_stdBasisMatrix]
  simp only [Matrix.stdBasisMatrix]
  aesop

/--
     isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso
-/
lemma comm_square :
    (inclusion' n k k_bar A iso).toLinearMap ∘ₗ
    (isoRestrict' n k k_bar A iso).toLinearMap  =
    iso.toLinearEquiv.toLinearMap.restrictScalars ℒ ∘ₗ
    (inclusion n k k_bar A iso).toLinearMap := by
  rw [← comm_triangle n k k_bar A iso, ← LinearMap.comp_assoc, comm_square' n k k_bar A iso]
  rfl

set_option synthInstance.maxHeartbeats 40000 in
lemma isoRestrict_map_one : isoRestrict' n k k⁻ A iso 1 = 1 := by
  /-
        isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso

  Want to show isoRestrict 1 = 1
  inclusion' ∘ isoRestrict = iso ∘ inclusion
  inclusion' (isoRestrict 1) = iso (inclusion 1) = 1 = inclusion' 1
  since inclusion' is injective, isoRestrict 1 = 1
  -/
  have eq := congr($(comm_square n k k_bar A iso) 1)
  conv_rhs at eq =>
    rw [LinearMap.comp_apply]
    erw [_root_.map_one (f := inclusion n k k_bar A iso), map_one iso]
  refine inclusion'_injective n k k_bar A iso (eq.trans ?_)
  rw [_root_.map_one]

set_option synthInstance.maxHeartbeats 40000 in
lemma isoRestrict_map_mul (x y : ℒ ⊗[k] A) :
    isoRestrict' n k k⁻ A iso (x * y) =
    isoRestrict' n k k⁻ A iso x * isoRestrict' n k k⁻ A iso y := by
  /-
        isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso

  Want to show isoRestrict (x * y) = isoRestrict x * isoRestrict y
  inclusion' ∘ isoRestrict = iso ∘ inclusion
  inclusion' (isoRestrict (x * y)) = iso (inclusion (x * y)) = iso (inclusion x) * iso (inclusion y)
    = inclusion' (isoRestrict x) * inclusion' (isoRestrict y)
    = inclusion' (isoRestrict x * isoRestrict y)
  since inclusion' is injective, isoRestrict (x * y) = isoRestrict x * isoRestrict y

  -/
  have eq := congr($(comm_square n k k_bar A iso) (x * y))
  conv_rhs at eq =>
    rw [LinearMap.comp_apply]
    erw [_root_.map_mul (f := inclusion n k k_bar A iso), _root_.map_mul (f := iso)]
  have eq₁ := congr($(comm_square n k k_bar A iso) x)
  have eq₂ := congr($(comm_square n k k_bar A iso) y)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.coe_restrictScalars,
    AlgEquiv.toLinearMap_apply] at eq₁ eq₂
  rw [← eq₁, ← eq₂, ← _root_.map_mul] at eq
  refine inclusion'_injective n k k_bar A iso (eq.trans ?_)
  rw [_root_.map_mul]

def isoRestrict : ℒ ⊗[k] A ≃ₐ[ℒ] Matrix (Fin n) (Fin n) ℒ :=
  AlgEquiv.ofLinearEquiv (isoRestrict' n k k⁻ A iso)
    (isoRestrict_map_one n k k⁻ A iso) (isoRestrict_map_mul n k k⁻ A iso)

end lemma_tto
