import Mathlib
open Complex

/- To satisfy the equation
\[
  \frac{a+b}{a} = \frac{b}{a+b},
\]
$a$ and $b$ must be
(A) both rational
(B) both real but not rational
(C) both not real
(D) one real, one not real
(E) one real, one not real or both not real -/
theorem algebra_98106 (a b : ℂ) (ha : a ≠ 0) (hab₁ : a + b ≠ 0) (hab₂ : (a + b) / a = b / (a + b)) :
    a.im ≠ 0 ∨ b.im ≠ 0 := by
  -- We can clear denominators and complete the square to get the equation:
  have hab₃ : (a + b/2) ^ 2 + (3 / 4) * b ^ 2 = 0 := by linear_combination (norm := field_simp) (a + b) * a * hab₂; ring
  -- Assume by contradiction that both $a$ and $b$ are real
  by_contra hab₄; simp at hab₄
  lift a to ℝ using hab₄.1
  lift b to ℝ using hab₄.2
  -- Then we do a case ditinction on whether $b$ is zero or not
  by_cases hb : b = 0
  -- In the first case, we see from hab₃ that $a ^ 2 = 0$, thus $a = 0$, a contradiction
  · simp [ha, hb] at hab₃
  -- In the second case, we obtain a contradiction from the equation hab₃, since the first summand is ≥ 0, while the second summand is > 0
  · have : b ^ 2 > 0 := sq_pos_of_ne_zero hb
    norm_cast at hab₃; apply_fun re at hab₃; simp [-ofReal_pow] at hab₃
    nlinarith
