import Lean
namespace Nat

theorem one_eq_succ_zero: 1 = succ 0 := rfl

theorem exist_add_of_le {a b:Nat}(h:b≤a): ∃(n:Nat),a=b+n := by
  induction h
  case _ => exists 0
  case _ _ _ h =>
    cases h;case _ w h=>
      rw[h]
      exists w+1
