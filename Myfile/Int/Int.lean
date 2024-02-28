import Myfile.Nat.basic
namespace Int
--==Translators==--
theorem add_mean {a b:Int} : Int.add a b = a + b := rfl
theorem sub_mean {a b:Int} : Int.sub a b = a - b := rfl
theorem mul_mean {a b:Int} : Int.mul a b = a * b := rfl
theorem negOfNat_mean (a:Nat) : negOfNat a = - ofNat a := rfl
theorem negSucc_mean (a:Nat) : negSucc a = negOfNat (Nat.succ a) := rfl
theorem translate0 : ofNat 0 = 0 := rfl
theorem neg_zero : -0 = 0 := rfl
theorem add_sub_eq_sub_add {a b:Int} : a + (-b) = a - b := rfl
theorem nat_to_int (a:Nat) : a = (a:Int) := rfl
--==Theorems==--
theorem neg_neg (a:Int) : -(-a) = a := by
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
    case zero => simp[translate0,neg_zero,Int.add]
    case succ p' => simp[←negOfNat_mean,←negSucc_mean,Int.add,subNatNat,translate0]
  case negSucc =>
    rw[negSucc_mean,negOfNat_mean,neg_neg,←negOfNat_mean,←negSucc_mean,Int.add] -- nth_rwが使えないときは、「rwしてから戻す」というテクニックが有効。
    simp[subNatNat,translate0]
theorem add_zero (a:Int) : a + 0 = a := by
  cases a
  all_goals rfl
theorem zero_add (a:Int) : 0 + a = a := by
  cases a
  all_goals simp[←add_mean,Int.add,subNatNat]
theorem add_comm {a b:Int} : a + b = b + a := by
  cases a
  all_goals cases b
  all_goals simp[←add_mean,Int.add,Nat.add_comm]

theorem neg_comm {a b:Int} : -a-b = -b-a := by simp[←add_sub_eq_sub_add,add_comm]
theorem sub_triple_swap {a b:Int} : a-b=(-b)-(-a) := by simp[←add_sub_eq_sub_add,neg_neg,add_comm]
theorem subNatNat_add_left {a b:Nat} : subNatNat (a+b) a = b := by
  unfold subNatNat
  rw[Nat.sub_eq_zero_of_le,Nat.add_sub_cancel_left]
  exact Nat.le_add_right a b
theorem subNatNat_add_right {a b:Nat} : subNatNat (a+b) b = a := by rw[Nat.add_comm,subNatNat_add_left]
theorem subNatNat_add_add {a b c:Nat} : subNatNat (a+c) (b+c) = subNatNat a b := by
  unfold subNatNat
  repeat rw[Nat.add_sub_add_right]
-- theorem subNat_to_negNat (h:a≤b) : subNatNat a b = -(b-a) := sorry
theorem sub_comm₁ {c:Nat}(h:b≤a) : subNatNat (a-b) c=subNatNat a (b+c) := by
  calc subNatNat (a-b) c
    _ = subNatNat (a-b+b) (c+b) := by rw[←subNatNat_add_add] -- simp[←subNatNat_add_add] didn't work
    _ = subNatNat a (b+c) := by rw[Nat.sub_add_cancel h,Nat.add_comm]

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
/-
Theorem list
Basics
  neg_neg (a:Int) : -(-a) = a
  succ_neg_inj {a b:Nat} : negSucc a = negSucc b ↔ a = b
  neg_inj {a b:Int} : -a = -b ↔ a = b
  sub_self (a:Int) : a-a = 0
Additive
  add_zero (a:Int) : a+0 = a
  zero_add (a:Int) : 0+a = a
  add_comm {a b:Int} : a+b = b+a
Subtraction
  subNatNat_add_add {a b c:Nat} : subNatNat (a+c) (b+c) = subNatNat a b
  neg_comm {a b:Int} : -a-b = -b-a
  sub_triple_swap {a b:Int} : a-b=(-b)-(-a)
  subNatNat_add_left {a b:Nat} : subNatNat (a+b) a = b
  subNatNat_add_right {a b:Nat} : subNatNat (a+b) b = a
  sub_comm₁ {c:Nat}(h:b≤a) : subNatNat (a-b) c=subNatNat a (b+c)
Multiple
  mul_zero (a:Int) : a * 0 = 0
  zero_mul (a:Int) : 0 * a = 0
  mul_comm {a b:Int} : a * b = b * a
-/