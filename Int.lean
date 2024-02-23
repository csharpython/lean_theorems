import Lean
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
  case ofNat p =>
    cases p
    case zero => rfl
    case succ p' =>
      rw[←negOfNat_mean,←negSucc_mean]
      rfl
  case negSucc n => rfl
--==theorem-of-add==--
theorem Zadd_zero (a:Int) : a + 0 = a := by
  cases a
  all_goals rfl
theorem Zzero_add (a:Int) : 0 + a = a := by
  rw[←add_mean,←translate0]
  cases a
  all_goals simp[Int.add,subNatNat]
theorem Zadd_comm {a b:Int} : a + b = b + a := by
  repeat rw[←add_mean]
  cases a
  all_goals cases b
  all_goals simp[Int.add,Nat.add_comm]
