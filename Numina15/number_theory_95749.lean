import Mathlib
set_option maxRecDepth 5000
/- Find the least positive integer $N$ such that the set of $1000$ consecutive integers beginning with $1000\cdot N$ contains no square of an integer. -/
theorem number_theory_95749 :
    IsLeast {N : ℕ | 0 < N ∧ ∀ k ∈ Finset.range 1000, ¬ ∃ m, m^2 = 1000 * N + k} 282 := by
  constructor
  -- 282 fulfills the property, because the set of $1000$ consecutive integers beginning with $1000 \cdot 282$ is contained between $531^2$ and $532^2$
  · simp; intro k hk m hm
    rw [pow_two ] at hm
    have hm1 : 531 * 531 < m * m := by linarith
    have hm2 : m * m < 532 * 532 := by linarith
    exact Nat.not_exists_sq hm1 hm2 ⟨m, rfl⟩
  -- Let N be any integer fulfilling the property
  · intro N ⟨hN1, hN2⟩
    -- Let $m = \lfloor \sqrt{1000 \cdot N} \rfloor$
    let m := Nat.sqrt (1000 * N)
    -- Then, for all $k$ in the range $0$ to $999$, $m^2 \leq 1000 \cdot N + k$ because $m^2 \leq 1000 \cdot N$
    have h1 : ∀ k ∈ Finset.range 1000, m ^ 2 ≤ 1000 * N + k := by unfold m; have := Nat.sqrt_mul_sqrt_lt_succ' (1000 * N); intro k hk; omega
    -- Also, we have three possibilities: $(m+1)^2 < 1000 \cdot N$, $1000 \cdot N \leq (m+1)^2 < 1000 \cdot N + 1000$, or $1000 \cdot N + 1000 \leq (m+1)^2$
    have h2 : ((m + 1) ^ 2 < 1000 * N) ∨ (1000 * N ≤ (m + 1) ^ 2 ∧ (m + 1) ^ 2 < 1000 * N + 1000) ∨ (1000 * N + 1000 ≤ (m + 1) ^ 2) := by omega
    rcases h2 with h2 | h2 | h2
    -- The first case is impossible, because $(m+1)^2 \geq 1000 \cdot N$
    · have := Nat.succ_le_succ_sqrt' (1000 * N)
      linarith
    -- The second case is also impossible, because $if $(m+1)^2$ falls in this range, then there is a square in the range $1000N + 0$ to $1000N + 999$
    · let k := (m + 1) ^ 2 - 1000 * N
      have hk : k ∈ Finset.range 1000 := by
        simp
        omega
      have hk2 : (m + 1) ^ 2 = 1000 * N + k := by omega
      exfalso; exact hN2 k hk ⟨m + 1, hk2⟩
    -- Thus, we have $1000 \cdot N + 1000 \leq (m+1)^2$
    · -- We also have $m ^ 2 + 1 \leq 1000 \cdot N$, because $m ^ 2 ≤ 1000N$ and because $1000N$ is not a square.
      have hm : m ^ 2 + 1 ≤ 1000 * N := by
        have := h1 0 (by simp)
        have : m ^ 2 ≠ 1000 * N := by
          by_contra! h; exact hN2 0 (by simp) ⟨m, h⟩
        omega
      -- Combining these two inequalities, we get that $m ≥ 500$
      have h3 : (m + 1) ^ 2 - m ^ 2 ≥ 1000 := by omega
      rw [show (m + 1) ^ 2 - m ^ 2 = 2 * m + 1 by ring_nf; omega] at h3
      have h4 : m ≥ 500 := by omega
      -- Let $k = m - 500$
      let k := m - 500; have hk : m = 500 + k := by omega
      rw [hk] at h2 hm
      qify at h2 hm
      -- Then the earlier inequalities, rearranged for $N$, become:
      have h2 : (N : ℚ) ≤ (k + 1) ^ 2 / 1000 + k + 250 := by linarith
      have hm : (N : ℚ) ≥ (k ^ 2 + 1) / 1000 + k + 250 := by linarith
      rcases (show k ≤ 30 ∨ k = 31 ∨ 32 ≤ k by omega) with h | h | h
      · -- If $k \leq 30$, we arrive at a contradiction:
        -- The first inequality implies that $k + 250 < N$
        have h5 : k + 250 < N := by
          qify
          have : ((k : ℚ) ^ 2 + 1) / 1000 > 0 := by nlinarith
          linarith
        -- The second inequality implies that $N < k + 251$
        have h6 : N < k + 251 := by
          qify
          have : k + 1 ≤ 31 := by linarith
          have : ((k : ℚ) + 1) ^ 2 / 1000 < 1 := by cancel_denoms; norm_cast; calc
            (k + 1) ^ 2 = (k + 1) * (k + 1) := by apply pow_two
                      _ ≤ 31 * (k + 1)      := by apply mul_le_mul_right'; assumption
                      _ ≤ 31 * 31           := by linarith
                      _ < 1000              := by linarith
          linarith
        omega
      · -- If $k = 31$, we conclude that $N = 282$ from the inequalities
        norm_num [h] at h2 hm
        rcases (show N ≤ 281 ∨ 282 ≤ N by omega) with hN | hN
        · qify at hN; linarith
        · linarith
      · -- If $k \geq 32$, we can easily show that $N \geq 282$
        qify at h ⊢
        have : (k : ℚ) ^ 2 ≥ 32 ^ 2 := by nlinarith
        linarith
