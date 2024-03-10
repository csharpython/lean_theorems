import CSPtheorem.Nat.Basic
namespace Int
--==Translators==--
theorem add_def {a b:Int} : Int.add a b = a + b := rfl
theorem sub_mean {a b:Int} : Int.sub a b = a - b := rfl
theorem mul_mean {a b:Int} : Int.mul a b = a * b := rfl
theorem negOfNat_mean (a:Nat) : negOfNat a = - ofNat a := rfl
theorem negSucc_def (a:Nat) : negSucc a = negOfNat (Nat.succ a) := rfl
@[simp]theorem int_zero_eq_nat_zero : ofNat 0 = 0 := rfl
@[simp]theorem neg_zero : -0 = 0 := rfl
theorem add_sub_eq_sub_add {a b:Int} : a + (-b) = a - b := rfl
theorem nat_to_int (a:Nat) : a = (a:Int) := rfl
--==Theorems==--
@[simp]theorem neg_neg (a:Int) : -(-a) = a := by
  cases a
  try rw[←negOfNat_mean,←negSucc_def]
  case ofNat p => cases p <;> rfl
  rfl
theorem succ_neg_inj {a b:Nat} : negSucc a = negSucc b ↔ a = b := ⟨negSucc.inj,λh↦by rw[h]⟩
theorem neg_inj {a b:Int} : -a = -b ↔ a = b := ⟨λh↦by rw[←neg_neg a,←neg_neg b,h],λh↦by rw[h]⟩
@[simp]theorem sub_self (a:Int) : a-a=0 := by
  rw[←add_sub_eq_sub_add,←add_def]
  match a with
  | 0 => simp[int_zero_eq_nat_zero,neg_zero,Int.add]
  | ofNat (Nat.succ _) => simp[←negOfNat_mean,←negSucc_def,Int.add,subNatNat,int_zero_eq_nat_zero]
  | negSucc _ =>
    rw[negSucc_def,negOfNat_mean,neg_neg,←negOfNat_mean,←negSucc_def,Int.add]
    simp[subNatNat,int_zero_eq_nat_zero]
@[simp]theorem add_zero (a:Int) : a + 0 = a := by cases a <;> rfl
@[simp]theorem zero_add (a:Int) : 0 + a = a := by cases a <;> simp[←add_def,Int.add,subNatNat]
theorem add_comm {a b:Int} : a + b = b + a := by cases a <;> cases b <;> simp[←add_def,Int.add,Nat.add_comm]

@[simp]theorem sub_zero (a:Int) : a-0 = a := by simp[←add_sub_eq_sub_add]
theorem neg_comm {a b:Int} : -a-b = -b-a := by simp[←add_sub_eq_sub_add,add_comm]
theorem sub_eq_neg_sub_neg {a b:Int} : a-b=(-b)-(-a) := by simp[←add_sub_eq_sub_add,add_comm]
@[simp]theorem subNatNat_zero (a:Nat) : subNatNat a 0 = a := by simp[subNatNat]
theorem subNatNat_eq_sub {a b:Nat} : subNatNat a b = a - b := by
  rw[←add_sub_eq_sub_add]
  cases b <;> simp[←negOfNat_mean,←negSucc_def] <;> rfl

@[simp]theorem subNatNat_add_left {a b:Nat} : subNatNat (a+b) a = b := by
  rw[subNatNat,Nat.sub_eq_zero_of_le,Nat.add_sub_cancel_left]
  exact Nat.le_add_right _ _
@[simp]theorem subNatNat_add_right {a b:Nat} : subNatNat (a+b) b = a := by rw[Nat.add_comm,subNatNat_add_left]
@[simp]theorem subNatNat_add_add {a b c:Nat} : subNatNat (a+c) (b+c) = subNatNat a b := by simp[subNatNat,Nat.add_sub_add_right]
theorem subNatNat_sub {c:Nat}(h:b≤a) : subNatNat (a-b) c=subNatNat a (b+c) := by
  calc _
    _ = subNatNat (a-b+b) (c+b) := by rw[←subNatNat_add_add] -- simp[←subNatNat_add_add] didn't work
    _ = subNatNat a (b+c) := by rw[Nat.sub_add_cancel h,Nat.add_comm]
@[simp]theorem subNatNat_right_add {a b:Nat} : subNatNat a (b+a)= - b := by
  calc _
    _ = subNatNat (0 + a) (b + a) := by rw[Nat.zero_add]
    _ = subNatNat 0 b := subNatNat_add_add
    _ = -b := by cases b <;> rfl
@[simp]theorem subNatNat_left_add {a b:Nat} : subNatNat a (a+b)= - b := by rw[Nat.add_comm];simp

@[simp]theorem subNatNat_add {a b c:Nat} : subNatNat (a+b) c = a + subNatNat b c := by
  cases b.lt_or_ge c
  case inl h =>
    cases Nat.exist_add_of_le (Nat.succ_le_of_lt h)
    case intro _ h' =>
      simp[h',Nat.add_comm,Nat.succ_eq_add_one,←Nat.add_assoc]
      rw[Nat.add_assoc,Nat.add_comm b,subNatNat_add_add,subNatNat_right_add,subNatNat_eq_sub,add_sub_eq_sub_add]
  case inr h =>
    unfold subNatNat
    simp[Nat.sub_eq_zero_of_le h,Nat.sub_eq_zero_of_le (Nat.le_trans h (Nat.le_add_left b a)),Nat.add_sub_assoc h]
    rfl
theorem subNatNat_add_neg {a b c:Nat} : subNatNat a b + negSucc c = subNatNat a (b + Nat.succ c) := by
  cases a.lt_or_ge b
  case inl h =>
    cases Nat.exist_add_of_le (Nat.succ_le_of_lt h)
    case _ _ h' =>
      rw[h',Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_assoc]
      simp[Nat.one_add,←negOfNat_mean,←negSucc_def,←add_def,Int.add,Nat.succ_add]
      rfl
  case inr h =>
    cases Nat.exist_add_of_le h
    case _ _ h' =>
      simp[h',Nat.add_comm b]
      conv => rhs;rw[←negOfNat_mean,←negSucc_def]
/--theorem add_assoc {a b c:Int} : a + b + c = a + (b + c) :=
  have OO_ : ∀(x y:Nat)(z:Int),ofNat x + ofNat y + z = ofNat x + (ofNat y + z) := by
    intro _ _ z
    cases z
    case ofNat => simp[←add_def,Int.add,Nat.add_assoc]
    case negSucc => simp[←add_def,Int.add]
  have ONO : ∀(x y z:Nat),ofNat x + negSucc y + ofNat z = ofNat x + (negSucc y + ofNat z) := by
    intro _ _ _
    conv in negSucc _ + ofNat _ => rw[add_comm]
    rw[←OO_]
    conv in _ + ofNat _ => rw[add_comm,←OO_]
    simp[add_comm]
  match a,b,c with
  | ofNat _,ofNat _,_ => OO_ _ _ _
  | ofNat _,negSucc _,ofNat _ => ONO _ _ _
  | negSucc _,ofNat _,ofNat _ => by
    conv => rhs ; rw[add_comm,OO_,add_comm]
    conv => lhs ; rw[add_comm,←ONO]
  | ofNat a,negSucc b,negSucc c => sorry
  | negSucc _,negSucc _,negSucc _ => by simp[←add_def,Int.add,Nat.succ_eq_add_one];rw[Nat.add_right_comm _,←Nat.add_assoc,←Nat.add_assoc]
  | _,_,_ => sorry-/
@[simp]theorem mul_zero (a:Int) : a * 0 = 0 := by cases a <;> rfl
@[simp]theorem zero_mul (a:Int) : 0 * a = 0 := by
  rw[←mul_mean,Int.mul]
  cases a <;> simp <;> rfl
theorem mul_comm {a b:Int} : a * b = b * a := by
  repeat rw[←mul_mean]
  cases a <;> cases b <;> simp[Int.mul,Nat.mul_comm]
