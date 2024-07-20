import CSPtheorem.Int.Basic
namespace Int
notation:max "|" a:max "|" => natAbs a

@[simp]theorem abs_abs {n : Int} : | |n| | = |n| := rfl

@[simp]theorem sign_sign {n : Int} : sign (sign n) = sign n := by
  cases n
  case _ n => cases n <;> rfl
  case _ n => rfl

@[simp]theorem nonneg_natAbs {n : Int} : NonNeg |n| := NonNeg.mk |n|
@[simp]theorem natAbs_mul_sign {n : Int} : |n| * sign n = n := by
  cases n
  case _ n => cases n <;> simp[sign]
  case _ n => simp[sign,Int.mul_neg] ; rfl

@[simp]theorem nonneg_square {n : Int} : NonNeg (n*n) := by cases n <;> simp <;> rw[ofNat_mul_ofNat _ _] <;> apply NonNeg.mk
