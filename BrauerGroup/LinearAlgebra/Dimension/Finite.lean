module

public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
## LinearEquiv of subsingleton
-/

@[expose] public section

/-- If `M` is trivial and `N` has the same rank as `M` then `M` has a linear-equivalence to `N`. -/
def Module.equivOfSingleton {k A M N : Type*} [Ring k] [StrongRankCondition k] [Ring A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module k M] [Module A N] [Module k N]
    [Module.Finite k N] [NoZeroSMulDivisors k N] (h1 : finrank k M = finrank k N)
    (h2 : Subsingleton M) : M ≃ₗ[A] N :=
  have := nontrivial_of_invariantBasisNumber k
  have : Subsingleton N := subsingleton_of_forall_eq 0 fun x ↦ by
    obtain ⟨a, ha, hax⟩ := finrank_eq_zero_iff.1 (h1 ▸ finrank_zero_of_subsingleton) x
    exact (eq_zero_or_eq_zero_of_smul_eq_zero hax).resolve_left ha
  LinearEquiv.ofSubsingleton M N
