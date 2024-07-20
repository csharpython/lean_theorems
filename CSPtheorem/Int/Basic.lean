import CSPtheorem.Nat.Basic
namespace Int
--==Translators==--
theorem sub_def {a b:Int} : Int.sub a b = a - b := rfl
theorem pow_def {a:Int}{b:Nat} : Int.pow a b = a ^ b := rfl
theorem negOfNat_def {a:Nat} : negOfNat a = - ofNat a := rfl
theorem negSucc_def {a:Nat} : negSucc a = negOfNat (Nat.succ a) := rfl
@[simp]theorem int_zero_eq_nat_zero : ofNat 0 = 0 := rfl
theorem add_neg_eq_sub {a b:Int} : a + (-b) = a - b := rfl

--==Theorems==--
theorem neg_comm {a b:Int} : -a-b = -b-a := by simp only [←add_neg_eq_sub,Int.add_comm]
theorem sub_eq_neg_sub_neg {a b:Int} : a-b=(-b)-(-a) := by simp[←add_neg_eq_sub,Int.add_comm]

@[simp]theorem subNatNat_zero {a:Nat} : subNatNat a 0 = a := by simp[subNatNat]
@[simp]theorem zero_subNatNat {a:Nat} : subNatNat 0 a = -a := by cases a <;> simp[subNatNat,Nat.sub_zero] ; rfl
theorem subNatNat_eq_sub {a b:Nat} : subNatNat a b = a - b := by cases b <;> simp[←add_neg_eq_sub,←negOfNat_def,←negSucc_def] <;> rfl

@[simp]theorem subNatNat_right_add {a b:Nat} : subNatNat a (b+a)= - b := by
  calc _
    _ = subNatNat (0 + a) (b + a) := by rw[Nat.zero_add]
    _ = -b := by rw[subNatNat_add_add 0 b _,zero_subNatNat]
@[simp]theorem subNatNat_left_add {a b:Nat} : subNatNat a (a+b)= - b := by rw[Nat.add_comm];simp

@[simp]theorem pow_one {a:Int} : a ^ 1 = a := by cases a <;> simp[←pow_def,Nat.one_eq_succ_zero,Int.pow]
