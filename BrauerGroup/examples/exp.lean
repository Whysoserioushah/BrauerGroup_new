import Mathlib.Data.Nat.Digits.Div

theorem rearrange_digits_diff_divisible_by_9
    (m m' : ℕ)(h_digits_perm : (Nat.digits 10 m').Perm (Nat.digits 10 m)) :
    (9 : ℤ) ∣ (m : ℤ) - (m' : ℤ) :=
  Nat.modEq_iff_dvd.1 <| Nat.modEq_nine_digits_sum m'|>.trans
    <| congrFun (congrArg HMod.hMod (List.Perm.sum_eq h_digits_perm)) 9 |>.trans
    <| (Nat.modEq_nine_digits_sum m).symm
