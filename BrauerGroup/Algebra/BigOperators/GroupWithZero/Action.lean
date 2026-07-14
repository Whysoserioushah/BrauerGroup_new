module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Telescoping for products over an orbit

For a monoid `G` acting on a commutative monoid `M` by `MulDistribMulAction`, the partial
products `P m := ∏ k < m, g ^ k • c` of the orbit of `c` under `g` satisfy the twisted
telescoping identity `P (m + n) = P m * g ^ m • P n`.

Conceptually this is `pow_add` in the semidirect product `M ⋊ G` (the partial products are
the left components of `(⟨c, g⟩ : M ⋊ G) ^ m`).

Mathlib PR candidate: belongs next to `Finset.smul_prod'`.
-/

@[expose] public section

namespace Finset

variable {G M : Type*} [Monoid G] [CommMonoid M] [MulDistribMulAction G M]

/-- Twisted telescoping for the partial products of the orbit of `c` under `g`. -/
theorem prod_range_add_pow_smul (g : G) (c : M) (m n : ℕ) :
    ∏ k ∈ Finset.range (m + n), g ^ k • c
      = (∏ k ∈ Finset.range m, g ^ k • c) * g ^ m • ∏ k ∈ Finset.range n, g ^ k • c := by
  rw [Finset.prod_range_add, Finset.smul_prod']
  congr 1
  exact Finset.prod_congr rfl fun k _ ↦ by rw [smul_smul, ← pow_add]

end Finset
