import CSPtheorem.Nat.Basic
namespace Int
--==Translators==--
theorem add_def {a b:Int} : Int.add a b = a + b := rfl
theorem sub_def {a b:Int} : Int.sub a b = a - b := rfl
theorem mul_def {a b:Int} : Int.mul a b = a * b := rfl
theorem pow_def (a:Int)(b:Nat) : Int.pow a b = a ^ b := rfl
theorem negOfNat_def (a:Nat) : negOfNat a = - ofNat a := rfl
theorem negSucc_def (a:Nat) : negSucc a = negOfNat (Nat.succ a) := rfl
@[simp]theorem int_zero_eq_nat_zero : ofNat 0 = 0 := rfl
@[simp]theorem neg_zero : -0 = 0 := rfl
theorem add_neg_eq_sub {a b:Int} : a + (-b) = a - b := rfl

--==Theorems==--
@[simp]theorem neg_neg (a:Int) : -(-a) = a := by
  cases a <;> try rfl
  case _ p => cases p <;> rfl
theorem negSucc_inj {a b:Nat} : negSucc a = negSucc b ↔ a = b := ⟨negSucc.inj,λh↦by rw[h]⟩
theorem neg_inj {a b:Int} : -a = -b ↔ a = b := ⟨λh↦by rw[←neg_neg a,←neg_neg b,h],λh↦by rw[h]⟩
@[simp]theorem sub_self (a:Int) : a-a=0 := by
  rw[←add_neg_eq_sub,←add_def]
  match a with
  | 0 => simp [neg_zero,Int.add]
  | ofNat (_+1) => simp[←negOfNat_def,←negSucc_def,Int.add,subNatNat]
  | negSucc _ =>
    rw[negSucc_def,negOfNat_def,neg_neg,←negOfNat_def,←negSucc_def,Int.add]
    simp[subNatNat,int_zero_eq_nat_zero]
@[simp]theorem add_zero (a:Int) : a + 0 = a := by cases a <;> rfl
@[simp]theorem zero_add (a:Int) : 0 + a = a := by cases a <;> simp[←add_def,Int.add,subNatNat]
theorem add_comm {a b:Int} : a + b = b + a := by cases a <;> cases b <;> simp[←add_def,Int.add,Nat.add_comm]

@[simp]theorem sub_zero (a:Int) : a-0 = a := by simp[←add_neg_eq_sub]
@[simp]theorem zero_sub (a:Int) : 0-a = -a := by simp[←add_neg_eq_sub]
theorem neg_comm {a b:Int} : -a-b = -b-a := by simp[←add_neg_eq_sub,add_comm]
theorem sub_eq_neg_sub_neg {a b:Int} : a-b=(-b)-(-a) := by simp[←add_neg_eq_sub,add_comm]

@[simp]theorem subNatNat_zero (a:Nat) : subNatNat a 0 = a := by simp[subNatNat]
@[simp]theorem zero_subNatNat (a:Nat) : subNatNat 0 a = -a := by cases a <;> simp[subNatNat,←negOfNat_def,negSucc_def]
@[simp]theorem subNatNat_self (a:Nat) : subNatNat a a = 0 := by simp[subNatNat]

theorem subNatNat_eq_sub {a b:Nat} : subNatNat a b = a - b := by cases b <;> simp[←add_neg_eq_sub,←negOfNat_def,←negSucc_def] <;> rfl

@[simp]theorem subNatNat_add_left {a b:Nat} : subNatNat (a+b) a = b := by rw[subNatNat,Nat.sub_eq_zero_of_le (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
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
    _ = -b := zero_subNatNat _
@[simp]theorem subNatNat_left_add {a b:Nat} : subNatNat a (a+b)= - b := by rw[Nat.add_comm];simp

theorem subNatNat_add {a b c:Nat} : subNatNat (a+b) c = a + subNatNat b c := by
  cases b.lt_or_ge c
  case _ h =>
    cases Nat.exist_add_of_le (Nat.succ_le_of_lt h)
    case _ _ h' =>
      simp[h',Nat.add_comm,Nat.succ_eq_add_one,←Nat.add_assoc]
      rw[Nat.add_assoc,Nat.add_comm b,subNatNat_add_add,subNatNat_right_add,subNatNat_eq_sub,add_neg_eq_sub]
  case _ h =>
    unfold subNatNat
    simp[Nat.sub_eq_zero_of_le h,Nat.sub_eq_zero_of_le (Nat.le_trans h (Nat.le_add_left b a)),Nat.add_sub_assoc h]
    rfl
theorem subNatNat_add_negSucc {a b c:Nat} : subNatNat a b + negSucc c = subNatNat a (b + Nat.succ c) := by
  cases a.lt_or_ge b
  case _ h =>
    cases Nat.exist_add_of_le (Nat.succ_le_of_lt h)
    case _ _ h' =>
      rw[h',Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_assoc]
      simp[Nat.one_add,←negOfNat_def,←negSucc_def,←add_def,Int.add,Nat.succ_add]
      rfl
  case _ h =>
    cases Nat.exist_add_of_le h
    case _ _ h' =>
      simp[h',Nat.add_comm b,subNatNat_add]
      conv => rhs;rw[←negOfNat_def,←negSucc_def]
-- Road to add_assoc
private theorem add_assoc₁ {a b:Nat}(c:Int) : ofNat a + ofNat b + c = ofNat a + (ofNat b+c) := by cases c <;> simp[←add_def,Int.add,Nat.add_assoc,subNatNat_add]
private theorem add_assoc₂ {x y z:Nat} : ofNat x + negSucc y + ofNat z = ofNat x + (negSucc y + ofNat z) := by
  conv in negSucc _ + ofNat _ => rw[add_comm]
  rw[←add_assoc₁]
  conv in _ + ofNat _ => rw[add_comm,←add_assoc₁]
  simp only [add_comm]
private theorem add_assoc₃ {a b c:Nat} : ofNat a + negSucc b + negSucc c = ofNat a + (negSucc b + negSucc c) := by
  conv => rhs ; simp only [←add_def,Int.add]
  conv => lhs ; lhs ; rw[←add_def,Int.add] ; simp
  conv => lhs ; rw[subNatNat_add_negSucc,Nat.add_succ,Nat.succ_add]
theorem add_assoc {a b c:Int} : a + b + c = a + (b + c) :=
  match a,b,c with
  | ofNat _,ofNat _,_ => add_assoc₁ _
  | ofNat _,negSucc _,ofNat _ => add_assoc₂
  | negSucc _,ofNat _,ofNat _ => by
    conv => rhs ; rw[add_comm,add_assoc₁,add_comm]
    conv => lhs ; rw[add_comm,←add_assoc₂]
  | ofNat _,negSucc _,negSucc _ => add_assoc₃
  | negSucc _,negSucc _,ofNat _ => by
    conv => lhs;rw[add_comm];rhs;rw[add_comm]
    conv => rhs;rw[add_comm];lhs;rw[add_comm]
    rw[add_assoc₃]
  | negSucc _,ofNat _,negSucc _ => by
    conv => lhs ; lhs ; rw[add_comm]
    conv => rhs ; rw[add_comm]
    simp[add_assoc₃]
    simp[add_comm]
  | negSucc _,negSucc _,negSucc _ => by simp[←add_def,Int.add,Nat.succ_eq_add_one];rw[Nat.add_right_comm _,←Nat.add_assoc,←Nat.add_assoc]
--done!
theorem neg_add {a b:Nat} : (-a) + (-b) = negOfNat (a+b) := by
  match a,b with
  | 0,_ => simp[negOfNat_def]
  | _,0 => simp[negOfNat_def]
  | Nat.succ x,Nat.succ y => simp[Nat.add_succ,Nat.succ_add,←negOfNat_def,←negSucc_def,←add_def,Int.add]

@[simp]theorem mul_zero (a:Int) : a * 0 = 0 := by cases a <;> rfl
@[simp]theorem zero_mul (a:Int) : 0 * a = 0 := by cases a <;> simp[←mul_def,Int.mul,negOfNat_def]
theorem mul_comm {a b:Int} : a * b = b * a := by cases a <;> cases b <;> simp only [←mul_def,Int.mul,Nat.mul_comm]
@[simp]theorem mul_one (a:Int) : a * 1 = a := by cases a <;> simp [←mul_def,Int.mul,←negSucc_def]
@[simp]theorem one_mul (a:Int) : 1 * a = a := by rw[mul_comm,mul_one]

@[simp]theorem pow_one (a:Int) : a ^ 1 = a := by cases a <;> simp[←pow_def,Nat.one_eq_succ_zero,Int.pow]
