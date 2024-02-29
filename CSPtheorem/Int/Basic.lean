import CSPtheorem.Nat.Basic
namespace Int
--==Translators==--
theorem add_mean {a b:Int} : Int.add a b = a + b := rfl
theorem sub_mean {a b:Int} : Int.sub a b = a - b := rfl
theorem mul_mean {a b:Int} : Int.mul a b = a * b := rfl
theorem negOfNat_mean (a:Nat) : negOfNat a = - ofNat a := rfl
theorem negSucc_mean (a:Nat) : negSucc a = negOfNat (Nat.succ a) := rfl
theorem int_zero_eq_nat_zero : ofNat 0 = 0 := rfl
theorem neg_zero : -0 = 0 := rfl
theorem add_sub_eq_sub_add {a b:Int} : a + (-b) = a - b := rfl
theorem nat_to_int (a:Nat) : a = (a:Int) := rfl
--==Theorems==--
@[simp] theorem neg_neg (a:Int) : -(-a) = a := by
  cases a
  try rw[←negOfNat_mean,←negSucc_mean]
  case ofNat p =>
    cases p
    all_goals rfl
  rfl
theorem succ_neg_inj {a b:Nat} : negSucc a = negSucc b ↔ a = b := ⟨negSucc.inj,λh↦by rw[h]⟩
theorem neg_inj {a b:Int} : -a = -b ↔ a = b := ⟨λh↦by rw[←neg_neg a,←neg_neg b,h],λh↦by rw[h]⟩
theorem sub_self (a:Int) : a-a=0 := by
  rw[←add_sub_eq_sub_add,←add_mean]
  cases a
  case ofNat p =>
    cases p
    case zero => simp[int_zero_eq_nat_zero,neg_zero,Int.add]
    case succ p' => simp[←negOfNat_mean,←negSucc_mean,Int.add,subNatNat,int_zero_eq_nat_zero]
  case negSucc =>
    rw[negSucc_mean,negOfNat_mean,neg_neg,←negOfNat_mean,←negSucc_mean,Int.add] -- nth_rwが使えないときは、「rwしてから戻す」というテクニックが有効。
    simp[subNatNat,int_zero_eq_nat_zero]
@[simp] theorem add_zero (a:Int) : a + 0 = a := by
  cases a
  all_goals rfl
@[simp] theorem zero_add (a:Int) : 0 + a = a := by
  cases a
  all_goals simp[←add_mean,Int.add,subNatNat]
theorem add_comm {a b:Int} : a + b = b + a := by
  cases a
  all_goals cases b
  all_goals simp[←add_mean,Int.add,Nat.add_comm]

theorem neg_comm {a b:Int} : -a-b = -b-a := by simp[←add_sub_eq_sub_add,add_comm]
theorem sub_eq_neg_sub_neg {a b:Int} : a-b=(-b)-(-a) := by simp[←add_sub_eq_sub_add,neg_neg,add_comm]
@[simp] theorem subNatNat_add_left {a b:Nat} : subNatNat (a+b) a = b := by
  unfold subNatNat
  rw[Nat.sub_eq_zero_of_le,Nat.add_sub_cancel_left]
  exact Nat.le_add_right a b
@[simp] theorem subNatNat_add_right {a b:Nat} : subNatNat (a+b) b = a := by rw[Nat.add_comm,subNatNat_add_left]
@[simp] theorem subNatNat_add_add {a b c:Nat} : subNatNat (a+c) (b+c) = subNatNat a b := by
  unfold subNatNat
  repeat rw[Nat.add_sub_add_right]
theorem subNatNat_sub {c:Nat}(h:b≤a) : subNatNat (a-b) c=subNatNat a (b+c) := by
  calc subNatNat (a-b) c
    _ = subNatNat (a-b+b) (c+b) := by rw[←subNatNat_add_add] -- simp[←subNatNat_add_add] didn't work
    _ = subNatNat a (b+c) := by rw[Nat.sub_add_cancel h,Nat.add_comm]

/--theorem subNatNat_add {a b c:Nat} : subNatNat (a+b) c = a + subNatNat b c := by
  cases b.lt_or_ge c
  case inl h => sorry
  case inr h =>
    unfold subNatNat
    simp[Nat.sub_eq_zero_of_le h,Nat.sub_eq_zero_of_le (Nat.le_trans h (Nat.le_add_left b a)),Nat.add_sub_assoc h]
    rfl-/

@[simp] theorem mul_zero (a:Int) : a * 0 = 0 := by
  cases a
  all_goals rfl
@[simp] theorem zero_mul (a:Int) : 0 * a = 0 := by
  rw[←mul_mean,←int_zero_eq_nat_zero]
  cases a
  all_goals simp[Int.mul]
  rfl
theorem mul_comm {a b:Int} : a * b = b * a := by
  repeat rw[←mul_mean]
  cases a
  all_goals cases b
  all_goals simp[Int.mul,Nat.mul_comm]
