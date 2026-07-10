module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed

@[expose] public section

/-- Every commutative subalgebra is contained in a maximal commutative subalgebra. -/
lemma exists_maximal_comm_subalgebra {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (M : Subalgebra R A) [IsMulCommutative M] :
    ∃ (L : Subalgebra R A), M ≤ L ∧ Maximal (fun S : Subalgebra R A ↦ IsMulCommutative S) L := by
  simp_rw +singlePass [← Set.mem_setOf (α := Subalgebra R A) (p := fun S ↦ IsMulCommutative S)]
  refine zorn_le_nonempty₀ (s := {S : Subalgebra R A | IsMulCommutative S})
    (fun K hK1 hK2 y hy ↦ ?_) _ (by simpa)
  simp only [Set.mem_setOf_eq]
  have : Nonempty K := ⟨⟨y, hy⟩⟩
  have : ∀ i : K, IsMulCommutative (i : Subalgebra R A) := fun i ↦ hK1 i.2
  exact ⟨⨆ i : K, (i : Subalgebra R A),
    Subalgebra.isMulCommutative_iSup hK2.directedOn.directed_val,
    fun z hz ↦ le_iSup (fun i : K ↦ (i : Subalgebra R A)) ⟨z, hz⟩⟩
