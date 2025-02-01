import Mathlib

/- If $y=2x$ and $z=2y$, then x+y+zx+y+z equals
(A) x (B) 3x (C) 5x (D) 7x (E) 9x -/
theorem algebra_98363 {x y z : ℝ} (h₀ : y = 2 * x) (h₁ : z = 2 * y) : x + y + z = 7 * x := by
  -- Plug in $z=2y$ and then $y = 2x$ into the term $x+y+zx+y+z$
  rw [h₁, h₀]
  -- Simplify the expression: $x + (2 * x) + 2 * (2 * x) = 7 * x$
  ring
