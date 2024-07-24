import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

suppress_compilation

open TensorProduct

universe u

section
variable (K K_bar: Type u) [Field K] [Field K_bar] [Algebra K K_bar] [IsAlgClosure K K_bar]

variable (A : Type u) [AddCommGroup A] [Module K A]

open scoped IntermediateField

def intermediateTensor (L : IntermediateField K K_bar) : Submodule K (K_bar ⊗[K] A) :=
  LinearMap.range (LinearMap.rTensor _ (L.val.toLinearMap) : L ⊗[K] A →ₗ[K] K_bar ⊗[K] A)

def intermediateTensor' (L : IntermediateField K K_bar) : Submodule L (K_bar ⊗[K] A) :=
  LinearMap.range ({LinearMap.rTensor _ (L.val.toLinearMap) with
    map_smul' := fun l x => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply];
      sorry} : L ⊗[K] A →ₗ[L] K_bar ⊗[K] A)

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

lemma is_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1)
    (Set.range fun (L : SetOfFinite K K_bar) ↦ intermediateTensor K K_bar A L):= by
  rintro _ ⟨⟨L1, (hL1 : FiniteDimensional _ _)⟩, rfl⟩ _ ⟨⟨L2, (hL2 : FiniteDimensional _ _)⟩, rfl⟩
  refine ⟨intermediateTensor K K_bar A (L1 ⊔ L2), ⟨⟨L1 ⊔ L2, show FiniteDimensional _ _ from
    ?_⟩, rfl⟩, ⟨intermediateTensor_mono K K_bar A le_sup_left,
      intermediateTensor_mono K K_bar A le_sup_right⟩⟩
  · apply (config := { allowSynthFailures := true }) IntermediateField.finiteDimensional_sup <;>
    assumption

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
variable (n : ℕ) (k k_bar A : Type u) [Field k] [Field k_bar] [Algebra k k_bar]
  [IsAlgClosure k k_bar] [Ring A] [Algebra k A]
  (iso : k_bar ⊗[k] A ≃ₐ[k_bar] Matrix (Fin n) (Fin n) k_bar)

def inter_tensor (E : IntermediateField k k_bar) : Subalgebra k (k_bar ⊗[k] A) :=
  (Algebra.TensorProduct.map ({
    __ := Algebra.ofId E k_bar
    commutes' := fun _ => rfl} : E →ₐ[k]k_bar) (AlgHom.id k A)).range

def e : Basis (Fin n × Fin n) k_bar (k_bar ⊗[k] A) :=
  Basis.map (Matrix.stdBasis k_bar _ _) iso.symm

def ℒ : IntermediateField k k_bar :=
  ⨆ (i : Fin n × Fin n), subfieldOf k k_bar A (e n k k_bar A iso i)

instance : FiniteDimensional k $ ℒ n k k_bar A iso :=
  IntermediateField.finiteDimensional_iSup_of_finite

local notation "ℒ" => ℒ n k k_bar A iso

def f (i : Fin n × Fin n) : subfieldOf k k_bar A (e n k k_bar A iso i) →ₐ[k] ℒ :=
  subfieldOf k k_bar A (e n k k_bar A iso i)|>.inclusion (le_sSup ⟨i, rfl⟩)

def e_hat (i : Fin n × Fin n) : intermediateTensor k k_bar A ℒ :=
  ⟨e n k k_bar A iso i, intermediateTensor_mono k k_bar A
    (le_sSup (by simp)) $ mem_subfieldOf k k_bar A (e n k k_bar A iso i)⟩

-- theorem ehat_linear_independent : LinearIndependent ℒ (e_hat n k k_bar A iso) := _


end lemma_tto
