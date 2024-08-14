import Lean
namespace Nat

instance (n:Nat) : Decidable (isPowerOfTwo n) := by
  apply decidable_of_iff (2^n.log2 = n)
  constructor <;> intro h
  exists n.log2
  rw[h]
  cases h;rename_i w h
  rw[h];clear h n
  congr
  induction w
  case zero _ => rfl
  case succ n h =>
    rw[Nat.pow_succ]
    unfold log2
    simp_all only [ge_iff_le, zero_lt_succ, mul_div_left,ite_eq_left_iff, Nat.not_le,ne_eq, false_and]
    intro i
    exfalso
    conv at i => rhs ; rw[←Nat.one_mul 2]
    have j := eq_zero_of_le_zero (le_of_lt_succ (Nat.lt_of_mul_lt_mul_right i))
    clear i h
    induction n
    case zero => contradiction
    case succ _ h => exact h (Nat.eq_zero_of_add_eq_zero_left j)
