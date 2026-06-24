import Mathlib

/- Exercise 12. Let $a, b, c$ be strictly positive integers such that $\frac{a^{2}-a-c}{b}+\frac{b^{2}-b-c}{a}=a+b+2$. Show that $a+b+c$ is a perfect square. -/
theorem algebra_292734 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₂ : (a^2 - a - c)/(b : ℚ) + (b^2 - b - c)/(a : ℚ) = a + b + 2) :
    IsSquare (a + b + c) := by
  -- First we lift all equations to $\mathbb{Q}$ to make use of field_simp etc.
  qify at h₂ ha hb
  field_simp [ha.ne, hb.ne] at h₂
  -- Then we show, as a rearrangement of the original equation, that $(a+b)(a+b+c) = (a+b)(a-b)^2$
  have h : (a + b) * (a + b + c) = (a + b) * (a - b) ^ 2 := by
    qify
    linear_combination -h₂
  -- We can cancel $a+b$ from both sides, as it is positive
  simp [show a + b ≠ 0 by qify; linarith] at h
  -- Thus we are done
  use (a - b);
  linear_combination h
