import Mathlib

open Real Set

/- The graphs of $y=\log_3 x, y=\log_x 3, y=\log_\frac{1}{3} x,$ and $y=\log_x \dfrac{1}{3}$ are plotted on the same set of axes. How many points in the plane with positive $x$-coordinates lie on two or more of the graphs?
$\textbf{(A)}\ 2\qquad\textbf{(B)}\ 3\qquad\textbf{(C)}\ 4\qquad\textbf{(D)}\ 5\qquad\textbf{(E)}\ 6$ -/
theorem algebra_97007 {f g h i : ℝ → ℝ}
    (hf : f = λ x => logb 3 x)
    (hg : g = λ x => logb x 3)
    (hh : h = λ x => logb (1/3) x)
    (hi : i = λ x => logb x (1/3)) :
    {(x, y) | 0 < x ∧ ((f x = y ∧ g x = y ∧ x ≠ 1) ∨ (f x = y ∧ h x = y) ∨ (f x = y ∧ i x = y ∧ x ≠ 1) ∨ (g x = y ∧ h x = y ∧ x ≠ 1) ∨ (g x = y ∧ i x = y ∧ x ≠ 1) ∨ (h x = y ∧ i x = y ∧ x ≠ 1))}.ncard = 5 := by
  -- We will find the explicit set of solutions
  suffices {(x, y) | 0 < x ∧ ((f x = y ∧ g x = y ∧ x ≠ 1) ∨ (f x = y ∧ h x = y) ∨ (f x = y ∧ i x = y ∧ x ≠ 1) ∨ (g x = y ∧ h x = y ∧ x ≠ 1) ∨ (g x = y ∧ i x = y ∧ x ≠ 1) ∨ (h x = y ∧ i x = y ∧ x ≠ 1))} = {(3, 1), (1/3, -1), (3, -1), (1/3, 1), (1,0)} by
    rw [this, show 5 = 4 + 1 by rfl];
    rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
    all_goals simp <;> try intro <;> split_ands
    all_goals norm_num
  -- Let (x, y) be in ℝ
  ext ⟨x, y⟩
  constructor
  · -- Then if (x, y) is on at least two of the graphs, it is one of the given points:
    intro hxy
    rcases hxy with ⟨ hx, ⟨hy1, hy2, hx0⟩  | ⟨hy1, hy2, hx0⟩ | ⟨hy1, hy2, hx0⟩ | ⟨hy1, hy2, hx0⟩ | ⟨hy1, hy2, hx0⟩ | ⟨hy1, hy2, hx0⟩ ⟩
    -- In the first case, $log_3 x = log_x 3$
    · have hx1 : f x = g x := by linarith
      simp [hf, hg] at hx1
      rw [← log_div_log, ← log_div_log] at hx1
      have hx2 : log x ≠ 0 := by simp; split_ands <;> by_contra! hx2 <;> simp [hx2] at hx hx0 <;> linarith
      field_simp [hx2] at hx1
      -- It follows that $(log x - log 3)(log x + log 3) = $
      have hx1 : (log x - log 3) * (log x + log 3) = 0 := by linarith
      simp at hx1
      rcases hx1 with hx1 | hx1
      -- So either $x = 3$
      · rw [← log_div, log_eq_zero] at hx1
        rcases hx1 with hx1 | hx1 | hx1
        · linarith
        · cancel_denoms at hx1
          simp [hx1, hf] at hy1
          rw [hx1, ← hy1]; simp
        · linarith
        all_goals linarith
      -- Or $x = 1/3$
      · rw [← log_mul, log_eq_zero] at hx1
        rcases hx1 with hx1 | hx1 | hx1
        · linarith
        · have hx1 : x = 1 / 3 := by linarith
          simp [hx1, hf] at hy1
          rw [hx1, ← hy1]; simp
        · linarith
        all_goals linarith
    -- In the second case, $log_3 x = log_(1/3) x$
    -- It follows that $x = 1$
    · have hx1 : f x = h x := by linarith
      simp [hf, hh] at hx1
      rw [← log_div_log, ← log_div_log] at hx1
      field_simp at hx1
      rcases hx1 with hx1 | hx1 | ⟨ hx1, hx1 ⟩
      · have hx1 := log_injOn_pos ?_ ?_ hx1
        linarith; simp; simp
      · linarith
      · simp [hf, hh]
      · linarith
    -- In the third case, $log_3 x = log_x (1/3)$
    -- This is impossible
    · have hx1 : f x = i x := by linarith
      simp [hf, hi] at hx1
      rw [← log_div_log, ← log_div_log] at hx1
      have hx2 : log x ≠ 0 := by simp; split_ands <;> by_contra! hx2 <;> simp [hx2] at hx hx0 <;> linarith
      field_simp [hx2] at hx1
      rw [← pow_two, ← pow_two] at hx1
      linarith [show (0 : ℝ) < 0 by calc
          0 ≤ log x ^ 2   := by nlinarith
          _ = - log 3 ^ 2 := hx1
          _ < 0 := by simp; apply sq_pos_of_pos; apply log_pos; linarith]
    -- In the fourth case, $log_x 3 = log_(1/3) x$
    -- This also leads to a contradiction
    · have hx1 : g x = h x := by linarith
      simp [hg, hh] at hx1
      rw [← log_div_log, ← log_div_log] at hx1
      have hx2 : log x ≠ 0 := by simp; split_ands <;> by_contra! hx2 <;> simp [hx2] at hx hx0 <;> linarith
      field_simp [hx2] at hx1
      simp [← pow_two, one_div, log_inv] at hx1
      linarith [show (0 : ℝ) < 0 by calc
          0 ≤ log x ^ 2   := by nlinarith
          _ = - log 3 ^ 2 := by linarith
          _ < 0 := by simp; apply sq_pos_of_pos; apply log_pos; linarith]
    -- In the fifth case, $log_x 3 = log_x (1/3)
    -- This leads to a contradiction
    · have hx1 : g x = i x := by linarith
      simp [hg, hi] at hx1
      rw [← log_div_log] at hx1
      have hx2 : log x ≠ 0 := by simp; split_ands <;> by_contra! hx2 <;> simp [hx2] at hx hx0 <;> linarith
      field_simp [hx2] at hx1
      have hx1 : log 3 = 0 := by linarith
      simp at hx1
      linarith
    -- In the last case, $log_(1/3) x = log_x (1/3)$
    · have hx1 : h x = i x := by linarith
      simp [hh, hi] at hx1
      rw [← log_div_log, ← log_div_log] at hx1
      have hx2 : log x ≠ 0 := by simp; split_ands <;> by_contra! hx2 <;> simp [hx2] at hx hx0 ; linarith
      field_simp [hx2] at hx1
      simp at hx1
      have hx1 : (log x - log 3) * (log x + log 3) = 0 := by nlinarith
      simp at hx1
      rcases hx1 with hx1 | hx1
      -- So either $x = 3$
      · rw [← log_div, log_eq_zero] at hx1
        rcases hx1 with hx1 | hx1 | hx1
        · linarith
        · cancel_denoms at hx1
          simp [hx1, hh, ← log_div_log] at hy1
          norm_num at hy1
          rw [hx1, ← hy1]; simp
        · linarith
        all_goals linarith
      -- Or $x = 1/3$
      · rw [← log_mul, log_eq_zero] at hx1
        rcases hx1 with hx1 | hx1 | hx1
        · linarith
        · have hx1 : x = 1 / 3 := by linarith
          simp [hx1, hh, ← log_div_log] at hy1
          norm_num at hy1
          rw [hx1, ← hy1]; simp
        · linarith
        all_goals linarith
  -- Now it remains to show that the given points fulfill the conditions
  · intro hxy
    rcases hxy with hxy | hxy | hxy | hxy | hxy
    all_goals simp at hxy; simp [hxy, hf, hg, hh, hi, ← log_div_log] <;> norm_num
