import Mathlib

/- ## Task 16/81

Determine all ordered pairs of natural numbers $(n ; m)$ that satisfy the equation $2^{n}+65=m^{2}$! -/
theorem number_theory_159148 :
    { (n, m) | 2^n + 65 = m^2 } = {(4, 9), (10, 33)} := by
  ext ⟨n, m⟩
  constructor
  -- Suppose $m$ and $n$ fulfill the equation
  · intro h; simp at h
    rcases Nat.even_or_odd n with ⟨ k, hk ⟩ | ⟨ k, hk ⟩
    -- If $n = 2k$ is evne, then $2 ^ n$ is a square
    · rw [hk, pow_add, ← pow_two] at h
      have hk' : 2 ^ k ≤ m := by nlinarith
      have hk' : 2 ^ k + 1 ≤ m := by
        cases hk'.eq_or_lt
        · simp [*] at h
        · linarith
      -- Since $2 ^ n + 65$ is also a square, it follows that
      -- $2 * 2 ^ k + 1 ≤ 65$
      have hk' : 2 * 2 ^ k + 1 ≤ 65 := by nlinarith
      rcases (show k ≤ 6 ∨ 7 ≤ k by omega) with hk'' | hk''
      -- For all $k ≤ 6$ we manually check the solutions
      · interval_cases k <;> simp at h
        · exfalso
          apply @Nat.not_exists_sq' 8 66
          on_goal 3 => use m
          all_goals linarith
        · exfalso
          apply @Nat.not_exists_sq' 8 69
          on_goal 3 => use m
          all_goals linarith
        · rw [show 81 = 9 ^ 2 by rfl, sq_eq_sq₀] at h
          simp [h, hk]
          all_goals linarith
        · exfalso
          apply @Nat.not_exists_sq' 11 129
          on_goal 3 => use m
          all_goals linarith
        · exfalso
          apply @Nat.not_exists_sq' 17 321
          on_goal 3 => use m
          all_goals linarith
        · rw [show 1089 = 33 ^ 2 by rfl, sq_eq_sq₀] at h
          simp [h, hk]
          all_goals linarith
        · linarith
      -- for k ≥ 7, the above inequality is impossible
      · linarith [ Nat.pow_le_pow_of_le_right (show 0 < 2 by simp) (hk'')]
    -- If $n = 2k + 1$ is odd, then we consider the equation mod $5$
    · apply_fun (@Int.cast (ZMod 5)) at h
      simp [hk, pow_add, pow_mul, show (65 : (ZMod 5)) = 0 by rfl, show (4 : (ZMod 5)) = -1 by rfl] at h
      -- We see that $2 * (-1) ^ k \equiv m ^ 2$, but this is
      -- impossible since $-2$ and $2$ are not squares mod $5$
      rcases Nat.even_or_odd k with hk' | hk'
      <;> simp [hk'] at h
      · have hk'' : IsSquare (2 : ZMod 5) := by use m; linear_combination h
        norm_cast at hk''
      · have hk'' : IsSquare (-2 : ZMod 5) := by use m; linear_combination h
        norm_cast at hk''
  -- Finally, check that the two claimed solutions indeed work.
  intro h
  simp at *
  cases h <;> simp [*]
