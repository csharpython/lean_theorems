import CSPtheorem.Int.Basic
namespace Int
notation:max "|" a:max "|" => natAbs a

@[simp]theorem abs_abs {n : Int} : | |n| | = |n| := rfl

@[simp]theorem nonneg_natAbs {n : Int} : NonNeg |n| := NonNeg.mk |n|
@[simp]theorem natAbs_mul_sign {n : Int} : |n| * sign n = n := by
  cases n
  case ofNat n => cases n <;> dsimp ; simp only [natCast_add, Nat.cast_ofNat_Int, sign_of_add_one, Int.mul_one]
  case negSucc n => simp only [natAbs_negSucc, Nat.succ_eq_add_one, natCast_add, Nat.cast_ofNat_Int, sign,reduceNeg, Int.mul_neg, Int.mul_one] ; rfl

@[simp]theorem nonneg_square {n : Int} : NonNeg (n*n) := by
  cases n
  case ofNat n => exact NonNeg.mk (n*n)
  case negSucc n => exact NonNeg.mk ((n+1)*(n+1))
