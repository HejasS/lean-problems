import Mathlib

/- If the radius of a circle is a rational number, its area is given by a number which is:
(A) rational (B) irrational (C) integral (D) a perfect square (E) none of these -/
theorem number_theory_94105 (r : ℚ) (hr : r > 0) :
    Irrational (Real.pi * r ^ 2) := by -- The area of a circle with radius r is πr^2
  norm_cast
  apply Irrational.mul_rat -- Multiplying an irrational number by a nonzero rational number gives an irrational number
  exact irrational_pi -- Pi is irrational
  simp; exact hr.ne.symm -- r^2 is nonzero, as it is bigger than zero
