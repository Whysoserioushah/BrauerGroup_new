import Mathlib

theorem rearrange_digits_diff_divisible_by_9
    (m m' : ℕ)(h_digits_perm : (Nat.digits 10 m').Perm (Nat.digits 10 m)) :
    (9 : ℤ) ∣ (m : ℤ) - (m' : ℤ) :=
  Nat.modEq_iff_dvd.1 <| Nat.modEq_nine_digits_sum m'|>.trans
    <| congrFun (congrArg HMod.hMod (List.Perm.sum_eq h_digits_perm)) 9 |>.trans
    <| (Nat.modEq_nine_digits_sum m).symm

example {K : Type*} [Field K] (R : Type*) [Ring R] [Algebra K R] :
  Matrix (Fin 1) (Fin 1) R ≃ₐ[K] R := by exact?
