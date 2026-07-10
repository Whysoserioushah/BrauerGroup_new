module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-- Any commutative subalgebra of a finite-dimensional division algebra is a field. -/
lemma division_commsubalg_isField {k D : Type*} [Field k] [DivisionRing D] [Algebra k D]
    (L : Subalgebra k D) [Module.Finite k L] [hL : IsMulCommutative L] :
    IsField L where
  exists_pair_ne := nontrivial_iff.1 inferInstance
  mul_comm := isMulCommutative_iff.1 hL
  mul_inv_cancel {l} hl :=
    have : Function.Surjective (LinearMap.mulLeft k l) :=
      LinearMap.surjective_of_injective <| LinearMap.ker_eq_bot.1 <| by
      simp [SetLike.ext_iff, hl]
    ⟨(this 1).choose, (this 1).choose_spec⟩
