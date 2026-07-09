module

public import BrauerGroup.Wedderburn
public import BrauerGroup.RingTheory.Morita.End
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Uniqueness in the Wedderburn–Artin theorem

The bulk of the simple-module / endomorphism-algebra machinery that used to live here now lives in
`BrauerGroup.RingTheory.Morita.{Matrix, SimpleRing, End}`. What remains are the uniqueness
statements: the division algebra and the matrix size in a Wedderburn–Artin decomposition of a
finite simple algebra are determined up to isomorphism.
-/

@[expose] public section

universe u v w

section simple

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma Wedderburn_Artin_uniqueness₀
    (n n' : ℕ) [NeZero n] [NeZero n']
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (D' : Type v) [DivisionRing D'] [Algebra k D'] (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    Nonempty <| D ≃ₐ[k] D' := by
  haveI : IsSimpleRing A := .of_ringEquiv wdb.symm.toRingEquiv inferInstance
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc a b x := by
      ext i
      exact congrFun (smul_assoc a b x) i }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc a b x := by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm a b x := by
        change wdb a • b • x = b • wdb a • x
        ext i
        exact congrFun (smul_comm (wdb a) b x) i }
  haveI : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A D wdb
  have ⟨iso⟩ := end_simple_mod_of_wedderburn' k A n D wdb (Fin n → D)
  have ⟨iso'⟩ := end_simple_mod_of_wedderburn' k A n' D' wdb' (Fin n → D)
  exact ⟨AlgEquiv.op.symm (iso.symm.trans iso')⟩

lemma Wedderburn_Artin_uniqueness₁
    (n n' : ℕ) [NeZero n] [NeZero n']
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (D' : Type v) [DivisionRing D'] [Algebra k D'] (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    n = n' := by
  have ⟨iso⟩ := Wedderburn_Artin_uniqueness₀ k A n n' D wdb D' wdb'
  let e : Matrix (Fin n) (Fin n) D ≃ₐ[k] Matrix (Fin n') (Fin n') D :=
    wdb.symm.trans (wdb'.trans iso.symm.mapMatrix)
  haveI : Module.Finite k D := by
    haveI inst1 : Module.Finite k (Matrix (Fin n) (Fin n) D) := wdb.toLinearEquiv.finiteDimensional
    rw [← Module.rank_lt_aleph0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1
  have eq1 := Module.finrank_matrix k D (Fin n) (Fin n)
  have eq2 := Module.finrank_matrix k D (Fin n') (Fin n')
  simp only [Fintype.card_fin] at eq1 eq2
  have eq3 : n * n * Module.finrank k D = n' * n' * Module.finrank k D := by
    rw [← eq1, ← eq2]
    exact LinearEquiv.finrank_eq e
  simp only [mul_eq_mul_right_iff] at eq3
  replace eq3 := eq3.resolve_right (fun rid => by
    rw [Module.finrank_zero_iff] at rid
    simpa using rid.elim 0 1)
  simpa [← pow_two] using eq3

end simple
