import Mathlib
open Real Int

theorem algebra_a8db6327 (x : ℝ) (hx : ∀ z : ℤ, x ≠ z) (hx' : x + 99 / x = ⌊ x ⌋ + 99 / ⌊ x ⌋) : x = -9.9 := by
  -- Let n be the integer part of x
  let n := ⌊ x ⌋
  -- Then x is between n and n + 1
  have h1 : n < x ∧ x < n + 1 := by
    unfold n
    split_ands
    · have := floor_le x
      exact this.lt_of_ne (by intro h; exact hx ⌊ x ⌋ h.symm)
    · exact lt_floor_add_one x
  -- The equation hx' yields the following:
  have h2 : (x - n) * (1 - 99 / (n * x)) = 0 := by
    unfold n
    have := hx 0
    norm_cast at this
    have : ⌊ x ⌋ ≠ 0 := by
      intro h
      simp [h] at hx'
      field_simp at hx'
      nlinarith
    linear_combination (norm := ring_nf) hx'
    field_simp; ring
  -- Since x is not an integer, x - n is nonzero
  have h3 : x - n ≠ 0 := by linarith
  -- Thus, in the above equation, the factor $1 - 99 / (nx)$ is zero, so $nx = 99$:
  have h4 : n * x = 99 := by
    simp [h3] at h2
    have : n * x ≠ 0 := by intro h; simp [h] at h2
    linear_combination (norm := field_simp) (n * x) * h2
  -- Thus $x = 99 / n$, so we have the inequalities:
  have h5 : n < (99 : ℝ) / n ∧ (99 : ℝ) / n < n + 1 := by
    have : x = 99 / n := by
      have : n ≠ 0 := by intro h; simp [h] at h4
      field_simp
      linarith
    rwa [←this]
  -- If n is positive, then the first inequality implies $n ^ 2 ≤ 99$, so $n ≤ 9$
  have h6 (h' : n ≥ 1) : n ≤ 9 := by
    have : n ≠ 0 := by intro h; simp [h] at h'
    have := h5.1
    apply_fun (· * (n : ℝ)) at this
    field_simp at this
    norm_cast at this
    by_contra! h''
    have h'' : 10 ≤ n := by linarith
    have : (100 : ℤ) < 99 := calc
      100 = 10 * 10 := by rfl
        _ ≤ n * 10  := by linarith
        _ ≤ n * n   := by nlinarith
        _ < 99      := by linarith
    linarith
    apply strictMono_mul_right_of_pos
    norm_cast
  -- Again if $n$ is positive, the second inequality implies $99 < n (n + 1)$, so $n ≥ 10$
  have h7 (h' : n ≥ 1) : n ≥ 10 := by
    have : n ≠ 0 := by intro h; simp [h] at h'
    have := h5.2
    apply_fun (· * (n : ℝ)) at this
    field_simp at this
    norm_cast at this
    by_contra! h''
    have h'' : n ≤ 9 := by linarith
    have : (99 : ℤ) < 90 := calc
      99 < (n + 1) * n := by linarith
       _ ≤ 10 * n      := by nlinarith
       _ ≤ 10 * 9      := by linarith
       _ = 90          := rfl
    linarith
    apply strictMono_mul_right_of_pos
    norm_cast
  -- Thus, $n$ cannot be positive
  have h8 (h' : n ≥ 1) : False := by linarith [h7 h', h6 h']
  wlog h9 : n < 0
  · simp at h9; rcases h9.eq_or_lt with h9 | h9
    -- $n$ is also not zero, because $nx = 99$
    · simp [← h9] at h4
    · exfalso; apply h8; linarith
  -- Thus, $n$ is negative
  -- Let $k := -n > 0$
  let k := -n
  have h10 : k > 0 := by unfold k; linarith
  -- Then we have the following inequalities for $k$
  have h11 : k > (99 : ℝ) / k ∧ (99 : ℝ) / k > k - 1 := by
    unfold k;
    split_ands
    <;> push_cast <;> linarith
  -- The first inequality implies $k ^ 2 ≥ 99$, so $k ≥ 10$
  have h12 : k ≥ 10 := by
    have := h11.1
    rify at h10
    apply_fun (· * (k : ℝ)) at this
    field_simp [h10.ne] at this
    norm_cast at this h10
    by_contra! h
    have h : k ≤ 9 := by linarith
    have : (99 : ℤ) < 81 := calc
      99 < k * k := by linarith
       _ ≤ 9 * k := by nlinarith
       _ ≤ 9 * 9 := by linarith
       _ = 81    := rfl
    linarith
    apply strictMono_mul_right_of_pos h10
  -- The second inqequality implies $99 > k (k - 1)$, so $k ≤ 10$, i.e. $k = 10$
  have h13 : k = 10 := by
    rcases h12.eq_or_lt with h12 | h12
    · linarith
    · have : 11 ≤ k := by linarith
      have := h11.2
      apply_fun (· * (k : ℝ)) at this
      field_simp [h10.ne] at this
      norm_cast at this
      have : (110 : ℤ) < 99 := calc
        110 = 10 * 11      := by linarith
          _ ≤ (k - 1) * 11 := by linarith
          _ < (k - 1) * k  := by nlinarith
          _ < 99           := by linarith
      linarith
      apply strictMono_mul_right_of_pos
      norm_cast
  -- Thus, $x = 99 / n = 99 / -k = -9.9$ as claimed
  have h14 : x = -9.9 := by
    unfold k at h13
    simp [show n = -10 by linarith] at h4
    linarith
  assumption
