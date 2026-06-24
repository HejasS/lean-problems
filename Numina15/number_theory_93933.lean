import Mathlib

/- Find the largest integer $n$ satisfying the following conditions:

(i) $n^2$ can be expressed as the difference of two consecutive cubes;
(ii) $2n + 79$ is a perfect square. -/
theorem number_theory_93933 :
    IsGreatest {n : ℤ | (∃ k, n ^ 2 = (k + 1) ^ 3 - k ^ 3) ∧ (∃ m, 2 * n + 79 = m ^ 2)} 181 := by
  constructor
  -- 181 works, since $181^2 = 105^3 - 104^3$ and $2 \cdot 181 + 79 = 21^2$
  · simp; apply And.intro
    · use 104; ring
    · use 21; ring
  -- Suppose such $n, k, m$ are given
  · intro n ⟨⟨k, hk⟩, ⟨m, hm⟩⟩
    -- WLOG $m \geq 0$
    wlog hm' : m ≥ 0 generalizing m hm
    · apply this (-m)
      rw [hm]; simp
      linarith
    -- We have $(2 * n + 1)(2 * n - 1) = 3(2 * k + 1)^2$ by rearranging the equations
    have h1 : (2 * n + 1) * (2 * n - 1) = 3 * (2 * k + 1) ^ 2 := by
      linear_combination (norm := ring_nf) 4 * hk
    -- WLOG $n \geq 0$ as otherwise $n$ is already less than 181
    wlog h2 : 0 ≤ n
    · linarith
    -- Now, since $(2 * n + 1)(2 * n - 1)$ is three times a square, either $2 * n + 1$ or $2 * n - 1$ is a square and the other is three times a square.
    -- This is too much effort to prove in Mathlib right now]
    have h3 : (∃ a b, a ^ 2 = 2 * n + 1 ∧ 3 * b ^ 2 = 2 * n - 1) ∨ (∃ a b, 3 * a ^ 2 = 2 * n + 1 ∧ b ^ 2 = 2 * n - 1) := by sorry
    rcases h3 with h3 | h3
    -- If $2n + 1$ is $a^2$ and $2n - 1$ is $3b^2$, then $a^2 - 3b^2 = 2$, which is impossible since squares
    -- are never $2$ mod $3$
    · have ⟨a, b, hab1, hab2⟩ := h3
      have h4 : a ^ 2 = 3 * b ^ 2 + 2 := by
        rw [hab1, hab2]
        ring
      apply_fun @Int.cast (ZMod 3) at h4
      simp [show (3 : (ZMod 3)) = 0 by rfl] at h4
      have h5 : IsSquare (2 : ZMod 3) := by use a; linear_combination -h4
      simp [FiniteField.isSquare_two_iff] at h5
    -- Now suppose $2n + 1$ is $3a^2$ and $2n - 1$ is $b^2$
    · have ⟨a, b, hab1, hab2⟩ := h3
      have h4 : (m - b) * (m + b) = 80 := by linear_combination -hm - hab2
      wlog hb : b ≥ 0 generalizing b hab2
      · apply this (-b)
        rw [← hab2]; simp
        rw [← h4]; linarith
        linarith
      -- It suffices to show that $2b ≤ 38$, as $2n - 1 = b ^ 2$
      suffices 2 * b ≤ 38 by
        have : 2 * n - 1 ≤ 361 := by nlinarith
        linarith
      have h5 : (m : ℚ) + b ≠ 0 := by norm_cast; by_contra! h; rw [h] at h4; simp at h4
      -- $2b$ can be written as $(m + b) - \frac {80} {m + b}$
      have h6 : 2 * b = (((m : ℤ) + b : ℤ) : ℚ) - (80 : ℚ) / (((m : ℤ) + b : ℤ) : ℚ) := by
        apply_fun @Int.cast ℚ at h4; simp at h4; rw [← h4]
        field_simp
        ring
      -- Set $x = m + b$ and $y = m - b$
      generalize hx : m + b = x at h4 h6
      generalize hy : m - b = y at h4
      lift x to ℕ using (by linarith)
      lift y to ℕ using (by nlinarith)
      norm_cast at h4
      -- Then $x$ is a divisor of $80$
      have h7 : x ∈ Nat.divisors 80 := by
        rw [Nat.mem_divisors]
        rw [← h4]; simp
        split_ands <;> by_contra! h <;> simp [h] at h4
      -- The divisors of $80$ are $1, 2, 4, 5, 8, 10, 16, 20, 40, 80$
      rw [show Nat.divisors 80 = {1, 2, 4, 5, 8, 10, 16, 20, 40, 80} from rfl] at h7
      simp at h7
      qify; rw [h6]
      -- In all cases except $x = 80$, $2b$ is at most $38$
      rcases h7 with h|h|h|h|h|h|h|h|h|h
      all_goals simp [h]; try linarith
      -- If $x = 80$, then $2m = 81$, which is impossible
      simp [h] at h4
      have : 2 * m = 81 := by linarith
      omega
