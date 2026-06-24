import Mathlib
open Nat List Finset

theorem algebra_73 (birthyear : ℕ) (h: (2011 : ℤ) - birthyear = (digits 10 birthyear).sum) : 2014 - birthyear = 23 := by
  -- We show first that the sum of digits of the birthyear is between 2 (for 2 + 0 + 0 + 0) and 28 (for 1 + 9 + 9 + 9)
  have h1 : 2 ≤ (digits 10 birthyear).sum ∧ (digits 10 birthyear).sum ≤ 28 := by
    split_ands
    · by_contra!; interval_cases h' : (digits 10 birthyear).sum
      -- If the sum of digits is 0, then the birthyear must be 2011, a contradiction
      · have : birthyear = 2011 := by omega
        simp [this] at h'
      -- If the sum of digits is 1, then the birthyear must be 2010, a contradiction
      · have : birthyear = 2010 := by omega
        simp [this] at h'
    -- The birthyear is at most 2011
    · have : birthyear ≤ 2011 := by omega
      -- We can get the digits as follows:
      have : (digits 10 birthyear).sum = birthyear % 10 + (birthyear / 10 % 10 + (birthyear / 10 / 10 % 10 + (digits 10 (birthyear / 10 / 10 / 10)).sum)) := by
        wlog h' : birthyear ≠ 0
        · simp at h'; simp [h']
        rw [digits_eq_cons_digits_div _ h']
        wlog h'' : birthyear / 10 ≠ 0
        · simp at h''; simp [h'']
        rw [digits_eq_cons_digits_div _ h'']
        wlog h''' : birthyear / 10 / 10 ≠ 0
        · simp at h'''; simp [h''']
        rw [digits_eq_cons_digits_div _ h''']
        simp only [reduceLeDiff, List.sum_cons, ge_iff_le]
        all_goals linarith
      rw [this]
      -- The remaining term birthyear / 10 / 10 / 10 is at most 2, since birthyear is at most 2011
      have : birthyear / 10 / 10 / 10 ≤ 2 := by omega
      interval_cases h' : (birthyear / 10 / 10 / 10)
      -- If it is 0 or 1, then the sum of digits is at most 9 + 9 + 9 + 1 = 28
      · simp; omega
      · simp; omega
      -- If it is 2, then 2000 ≤ birthyear ≤ 2011, thus the second digit is 0
      · simp
        have : birthyear ≥ 2000 := by omega
        have : birthyear / 10 / 10 = 20 := by omega
        -- Then the sum of digits is at most 9 + 0 + 9 + 9 = 27
        omega
  -- Since 2011 - birthyear = sum of digits, the birthyear is between 1983 (= 2011-28) and 2009 (= 2011-2)
  have h2 : 1983 ≤ birthyear ∧ birthyear ≤ 2009 := by omega
  -- We have 3 cases, the 1980's, the 1990's and the 2000's
  have h3 : birthyear ∈ Icc 1983 1989 ∨ birthyear ∈ Icc 1990 1999 ∨ birthyear ∈ Icc 2000 2009 := by
    simp
    omega
  -- The 2000's are impossible
  have h4 (h' : birthyear ∈ Icc 2000 2009) : False := by
    simp at h'
    rw [Nat.digits_eq_cons_digits_div,
        show birthyear / 10 = 200 by omega,
        show birthyear = 2000 + birthyear % 10 by omega] at h
    simp at h
    all_goals omega
  -- The 1990's are only possible for birthyear 1991
  have h5 (h' : birthyear ∈ Icc 1990 1999) : birthyear = 1991 := by
    simp at h'
    rw [Nat.digits_eq_cons_digits_div,
        show birthyear / 10 = 199 by omega,
        show birthyear = 1990 + birthyear % 10 by omega] at h
    simp at h
    all_goals omega
  -- The 1980's are impossible
  have h6 (h' : birthyear ∈ Icc 1983 1989) : False := by
    simp at h'
    rw [Nat.digits_eq_cons_digits_div,
        show birthyear / 10 = 198 by omega,
        show birthyear = 1980 + birthyear % 10 by omega] at h
    simp at h
    all_goals omega
  -- Thus, the birthyear must be 1991
  have h7 : birthyear = 1991 := by
    rcases h3 with  h3 | h3 | h3
    · exact (h6 h3).elim
    · exact (h5 h3)
    · exact (h4 h3).elim
  -- and the age in 2014 is thus 23
  have h8 : 2014 - birthyear = 23 := by
    omega
  exact h8
