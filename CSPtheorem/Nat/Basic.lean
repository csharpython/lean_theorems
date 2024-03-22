import Lean
namespace Nat

theorem exist_add_of_le {a b:Nat}(h:b≤a): ∃(n:Nat),a=b+n := by
  induction h
  case _ => exists 0
  case _ _ _ h =>
    cases h;case _ w h=>
      rw[succ_eq_add_one,h]
      exists w+1

@[simp] theorem one_add {a:Nat} : 1 + a = succ a := by simp[Nat.add_comm]

@[simp] theorem pow_one {a:Nat} : a ^ 1 = a := by rw[show 1 = Nat.succ 0 from rfl,pow_succ,pow_zero,Nat.one_mul]
@[simp] theorem one_pow {a:Nat} : 1 ^ a = 1 := by
  induction a
  case _ => rfl
  case _ _ dn => simp[pow_succ,dn]
@[simp] theorem zero_pow {a:Nat}(h:a≠0) : 0 ^ a = 0 := by
  cases a
  case _ => contradiction
  case _ => simp[pow_succ]
