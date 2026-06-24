import Mathlib

open Real Set

/- Task B-3.4. Determine the solutions of the inequality:

$$

2011 \cos \left(2 x^{2}-y\right) \geq x^{2}+2011

$$
 -/
theorem inequalities_214303 :
    { (x, y) | 2011 * cos (2 * x ^ 2 - y) ≥ x ^ 2 + 2011 } =
    { (x, y) | ∃ k : ℤ, x = 0 ∧ y = 2 * k * π} := by
  ext ⟨ x, y ⟩
  apply Iff.intro
  · intro h; simp at h
    -- Suppose that $(x, y)$ satisfies the inequality
    -- If $x^2 > 0$, then this would imply that $2011 > 2011$, a contradiction
    rcases ((show x ^ 2 ≥ 0 by nlinarith).lt_or_eq) with hx | hx
    · linarith [show (2011 : ℝ) > 2011 by calc
        2011 = 2011 * 1                   := by simp
           _ ≥ 2011 * cos (2 * x ^ 2 - y) := by linarith [cos_le_one (2 * x ^ 2 - y)]
           _ ≥ x ^ 2 + 2011               := by linarith
           _ > 2011                       := by nlinarith]
    -- Otherwise, $x = 0$ and thus $\cos(y) = 1$
    -- Thus, $y$ is of the required form
    · have hx := Eq.symm hx
      simp at hx
      simp [hx] at h ⊢
      have hy : cos y = 1 := by linarith [cos_le_one y]
      rw [cos_eq_one_iff] at hy
      obtain ⟨n, hn⟩ := hy
      exact ⟨n, by linarith⟩
  -- Clearly, all such pairs $(x, y)$ satisfy the inequality (even equality)
  · intro ⟨k, hx, hy⟩
    simp [hx, hy, show 2 * k * π = k * (2 * π) by ring]
