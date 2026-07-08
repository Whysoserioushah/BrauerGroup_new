module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Data.Matrix.Basic

@[expose] public section

theorem Module.finite_of_matrix {R M : Type*} (m n : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [Nonempty m] [Nonempty n] [Module.Finite R (Matrix m n M)] :
    Module.Finite R M := by
  obtain ⟨i⟩ := ‹Nonempty m›
  obtain ⟨j⟩ := ‹Nonempty n›
  exact .of_surjective (Matrix.entryLinearMap (R := R) (α := M) i j)
    fun x => ⟨.of fun _ _ => x, rfl⟩
