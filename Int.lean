import Lean
import Mathlib.Tactic.ApplyAt
namespace Int
--==means==--
theorem add_mean {a b:Int} : Int.add a b = a + b := rfl
theorem sub_mean {a b:Int} : Int.sub a b = a - b := rfl
theorem mul_mean {a b:Int} : Int.mul a b = a * b := rfl
theorem negOfNat_mean (a:Nat) : negOfNat a = - ofNat a := rfl
theorem negSucc_mean (a:Nat) : negSucc a = negOfNat (Nat.succ a) := rfl
--==translator==--
theorem translate0 : ofNat 0 = 0 := rfl
theorem neg_zero : -0 = 0 := rfl
theorem add_sub_eq_sub_add {a b:Int} : a + (-b) = a - b := rfl
--==theorem-of-succ==--
theorem succ_neg_inj {a b:Nat} : negSucc a = negSucc b ↔ a = b := ⟨negSucc.inj,λh↦by rw[h]⟩
theorem neg_neg (a:Int) : -(-a) = a := by
  cases a
  try rw[←negOfNat_mean,←negSucc_mean]
  case ofNat p =>
    cases p
    all_goals rfl
  rfl
theorem neg_inj {a b:Int} : -a = -b ↔ a = b := ⟨λh↦by rw[←neg_neg a,←neg_neg b,h],λh↦by rw[h]⟩
--==theorem-of-add==--
theorem add_zero (a:Int) : a + 0 = a := by
  cases a
  all_goals rfl
theorem zero_add (a:Int) : 0 + a = a := by
  rw[←add_mean,←translate0]
  cases a
  all_goals simp[Int.add,subNatNat]
theorem add_comm {a b:Int} : a + b = b + a := by
  repeat rw[←add_mean]
  cases a
  all_goals cases b
  all_goals simp[Int.add,Nat.add_comm]
--==theorem-of-sub==--
theorem neg_comm {a b:Int} : -a-b = -b-a := by simp[←add_sub_eq_sub_add,add_comm]
theorem sub_triple_swap {a b:Int} : a-b=(-b)-(-a) := by simp[←add_sub_eq_sub_add,neg_neg,add_comm]
theorem subNatNat_add_left {a b:Nat} : subNatNat (a+b) a = b := by
  unfold subNatNat
  rw[Nat.sub_eq_zero_of_le,Nat.add_sub_cancel_left]
  exact Nat.le_add_right a b
theorem subNatNat_add_right {a b:Nat} : subNatNat (a+b) b = a := by
  unfold subNatNat
  rw[Nat.sub_eq_zero_of_le,Nat.add_sub_cancel]
  exact Nat.le_add_left b a
theorem subNatNat_add_add {a b c:Nat} : subNatNat (a+c) (b+c) = subNatNat a b := by
  unfold subNatNat
  repeat rw[Nat.add_sub_add_right]
--==theorem-of-mul==--
theorem mul_zero (a:Int) : a * 0 = 0 := by
  cases a
  all_goals rfl
theorem zero_mul (a:Int) : 0 * a = 0 := by
  rw[←mul_mean,←translate0]
  cases a
  all_goals simp[Int.mul]
  rfl
theorem mul_comm {a b:Int} : a * b = b * a := by
  repeat rw[←mul_mean]
  cases a
  all_goals cases b
  all_goals simp[Int.mul,Nat.mul_comm]
--==end-of-this-file==--
