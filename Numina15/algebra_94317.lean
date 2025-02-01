import Mathlib

/- Suppose that $a, b$ and $c$ are positive real numbers such that $a ^ {\log_3 7} = 27, b ^ {\log_7 11} = 49$ and $c ^ {\log_11 25} = √11$. Find
\[
a ^ {\log_3 7} + b ^ {\log_7 11} + c ^ {\log_11 25}
\] -/
theorem algebra_94317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ^ (Real.logb 3 7) = 27) (h2 : b ^ (Real.logb 7 11) = 49)
    (h3 : c ^ (Real.logb 11 25) = Real.sqrt 11) :
    a ^ ((Real.logb 3 7) ^ 2) + b ^ ((Real.logb 7 11) ^ 2) +
    c ^ ((Real.logb 11 25) ^ 2) = 469 := by
  -- Rewrite the squares in the exponent as multiplications and then use power rules to substitute in the assumed equations
  rw [pow_two, Real.rpow_mul, h1, pow_two, Real.rpow_mul, h2, pow_two, Real.rpow_mul, h3, Real.sqrt_eq_rpow]
  norm_num
  -- Bring this in a form where we can apply $a ^ {\log_a b} = b$
  suffices (3 ^ (3 : ℝ)) ^ Real.logb 3 7 + (7 ^ (2 : ℝ)) ^ Real.logb 7 11 + ((11:ℝ) ^ ((1 / 2 ): ℝ)) ^ Real.logb 11 (5 ^ (2: ℝ)) = 469 by norm_num at this; assumption
  -- Apply this three times
  rw [← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb]
  rw [← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb]
  rw [← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb]
  -- Also simplify $(5 ^ 2) ^ {1 / 2}$
  rw [← Real.rpow_mul]
  -- Now just calculate the sum
  norm_num
  -- Finish the remaining goals (positivity to make sure all calculations were allowed) by linarith
  all_goals linarith
