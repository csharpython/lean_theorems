import Lean
namespace Nat

theorem lt_eq_succ_le {a b:Nat}: a < b ↔ succ a ≤ b := ⟨λt↦t,λt↦t⟩ -- 草
theorem exist_add_of_le {a b:Nat}(h:b≤a): ∃(n:Nat),a=b+n := by
  induction h
  case refl => exists 0
  case step m h h' =>
    cases h';case intro w h'=>
      rw[succ_eq_add_one,h']
      exists w+1
