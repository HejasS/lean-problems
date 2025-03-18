## USER

7.5. On December 31, 2011, Yevgeny Alexandrovich's age coincided with the sum of the digits of his birth year. How old was Yevgeny Alexandrovich on December 31, 2014? Prove the uniqueness of the answer.

Solution. The maximum sum of the digits of the birth year can be $1+9+9+9=28$, and the minimum - 2. Therefore, Y.A. was born no earlier than 1983 and no later than 2009. Note that if we change only the last digit of the birth year, the sum of the digits will increase, while the age will decrease (and vice versa) by the same amount. Therefore, in each decade, there can be no more than one suitable year. It remains to check the possible decades. If the birth year falls in the 2000s, we get the equation $2+0+0+x=11-x$. Thus, $2x=9$, which has no solution in integers. If the birth year falls in the 1980s, we get the equation $1+9+8+x=31-x$ or $2x=13$, which also has no solution in integers. Finally, for the 1990s, we get the equation $1+9+9+x=21-x$. Solving it, we get the only solution: $x=1$. Therefore, Y.A. was born in 1991. Thus, in 2014, he was 23 years old.

```lean4
theorem algebra_73 (birthyear : ℕ) (h: (2011 : ℤ) - birthyear = (digits 10 birthyear).sum) : 2014 - birthyear = 23 := by sorry
```

## THINK

Okay, let's try to figure out how old Yevgeny Alexandrovich was on December 31, 2014, given that on December 31, 2011, his age was equal to the sum of the digits of his birth year. Hmm, that's an interesting problem. Let me break it down step by step.

First, let's denote his birth year as a four-digit number, say 19XY or 20XY, where X and Y are digits. Since we're dealing with the year 2011, he must have been born sometime before 2011. The problem states that on December 31, 2011, his age was equal to the sum of the digits of his birth year. So, if we can find his birth year such that the sum of its digits equals his age in 2011, then we can just add 3 years to that age to find his age in 2014.

Let me note that the sum of the digits of the birth year (let's call this S) must equal his age in 2011. Therefore, his birth year would be 2011 - S. But wait, since S is the sum of the digits of his birth year, we can set up an equation here. Let me formalize this.

Let S be the sum of the digits of his birth year, and his age in 2011 is also S. Therefore, birth year = 2011 - S. But S is also the sum of the digits of the birth year. So:

S = sum of digits of (2011 - S)

This seems a bit circular, but maybe we can find possible values of S that satisfy this equation.

First, let's think about the possible range of S. The birth year has to be between, say, 1900 and 2011 (since he was alive in 2011). Let's check the maximum and minimum possible sums.

The maximum sum of digits for a birth year would be for the year 1999: 1 + 9 + 9 + 9 = 28. The minimum sum would be for the year 2000: 2 + 0 + 0 + 0 = 2. So S can be between 2 and 28. Therefore, his age in 2011 is between 2 and 28, which means his birth year is between 2011 - 28 = 1983 and 2011 - 2 = 2009. So he was born between 1983 and 2009 inclusive.

```lean4
have h1 : 2 ≤ (birthyear.digits 10).sum ∧ (birthyear.digits 10).sum ≤ 28 := by sorry
```

```lean4
have h2 : 1983 ≤ birthyear ∧ birthyear ≤ 2009 := by sorry
```

Now, let's denote his birth year as 19AB or 20CD, where A, B, C, D are digits. Since the birth year is between 1983 and 2009, let's split this into two parts: 1983-1999 and 2000-2009.

[Proposed Modificiation:] Since the birth year is between 1983 and 2009, let's split this into three parts: 1983-1989, 1990-1999 and 2000-2009.

```lean4
have h3 : birthyear ∈ Icc 1983 1989 ∨ birthyear ∈ Icc 1990 1999 ∨ birthyear ∈ Icc 2000 2009 := by sorry
``` 

Let me consider the 2000s first. If he was born in the 2000s, the birth year would be 200X, where X is a digit from 0 to 9. The sum of the digits would be 2 + 0 + 0 + X = 2 + X. His age in 2011 would be 2011 - (2000 + X) = 11 - X. According to the problem, this age equals the sum of the digits, so:

11 - X = 2 + X

Solving this equation:

11 - 2 = X + X

9 = 2X => X = 4.5

But X has to be a digit (0-9), so there's no solution here. Therefore, there's no valid birth year in the 2000s that satisfies the condition. So we can eliminate the 2000s.

```lean4
have h4 (h' : birthyear ∈ Icc 2000 2009) : False := by sorry
```

Now let's check the 1990s. If he was born in 199X, the birth year is 199X, sum of digits is 1 + 9 + 9 + X = 19 + X. His age in 2011 is 2011 - 1990 - X = 21 - X. According to the problem, age equals sum of digits:

21 - X = 19 + X

Solving:

21 - 19 = X + X

2 = 2X => X = 1

So X is 1, which is a valid digit. Therefore, the birth year is 1991. Let's check: sum of digits is 1 + 9 + 9 + 1 = 20. His age in 2011 would be 2011 - 1991 = 20. That matches, so that's a valid solution.

```lean4
have h5 (h' : birthyear ∈ Icc 1990 1999) : birthyear = 1991 := by sorry
```

Now let's check the 1980s. If he was born in 198X, the birth year is 198X, sum of digits is 1 + 9 + 8 + X = 18 + X. His age in 2011 is 2011 - 1980 - X = 31 - X. According to the problem:

31 - X = 18 + X

Solving:

31 - 18 = X + X

13 = 2X => X = 6.5

Again, X must be a digit, so 6.5 is invalid. Therefore, no solution in the 1980s.

```lean4
have h6 (h' : birthyear ∈ Icc 1983 1989) : False := by sorry
```

Wait, the original problem says that the birth year is no earlier than 1983. So maybe we need to check from 1983 onwards. But the 198X gives X=6.5, which is invalid. Let me check if there's another way. Wait, maybe the birth year in the 1980s is between 1983 and 1989. So X would be from 3 to 9. But even so, the equation gives X=6.5, which isn't a digit. Therefore, no solution in the 1980s.

Similarly, for the 1970s, but since we already established the earliest birth year is 1983, we don't need to go further back.

Therefore, the only valid birth year is 1991. Therefore, in 2011, he was 20 years old, and in 2014, three years later, he would be 23.

```lean4
have h7 : birthyear = 1991 := by sorry
```

```lean4
have h8 : 2014 - birthyear = 23 := by sorry
```

But wait, the problem mentions proving the uniqueness of the answer. So we need to ensure that there are no other possible birth years.

Earlier, we checked the 2000s and found no solution, the 1990s had one solution, the 1980s had none, and prior to that, he would be too old (since the maximum sum of digits is 28, so the earliest birth year is 2011 - 28 = 1983). So from 1983 to 2009, we only found 1991 as the valid birth year.

Let me confirm that there are no other decades where this could happen. For example, maybe if he was born in 2009, let's check:

Birth year 2009: sum of digits is 2 + 0 + 0 + 9 = 11. His age in 2011 would be 2011 - 2009 = 2. But 11 ≠ 2, so that doesn't work.

What about 1999? Sum is 1 + 9 + 9 + 9 = 28. Age in 2011 would be 2011 - 1999 = 12. 28 ≠ 12.

Similarly, 1983: sum is 1 + 9 + 8 + 3 = 21. Age in 2011 would be 2011 - 1983 = 28. 21 ≠ 28.

So none of the edge cases work except 1991.

Therefore, uniqueness is proven because we checked all possible decades (1980s, 1990s, 2000s) and only found one solution in the 1990s. Additionally, since each decade can have at most one solution (as changing the last digit affects the sum and age inversely by the same amount, leading to at most one solution per decade), there's no possibility of another solution within the same decade.

Therefore, the answer is 23 years old in 2014.

**Final Answer**
\boxed{23}


## ASSISTANT


Given that Yevgeny Alexandrovich's age on December 31, 2011, coincided with the sum of the digits of his birth year, we need to determine his age on December 31, 2014.

1. **Possible Birth Year Range**:
   - The maximum sum of digits for a birth year (1999) is 28.
   - The minimum sum of digits for a birth year (2000) is 2.
   - Therefore, the birth year must be between 2011 - 28 = 1983 and 2011 - 2 = 2009.

2. **Checking Each Decade**:
   - **2000s**: The birth year would be 200X. The sum of digits is \(2 + 0 + 0 + X = 2 + X\). Age in 2011 is \(11 - X\). Solving \(11 - X = 2 + X\) gives \(X = 4.5\), which is not a valid digit.
   - **1990s**: The birth year would be 199X. The sum of digits is \(1 + 9 + 9 + X = 19 + X\). Age in 2011 is \(21 - X\). Solving \(21 - X = 19 + X\) gives \(X = 1\). This gives the birth year 1991, with sum of digits 20 and age in 2011 as 20, which is valid.
   - **1980s**: The birth year would be 198X. The sum of digits is \(1 + 9 + 8 + X = 18 + X\). Age in 2011 is \(31 - X\). Solving \(31 - X = 18 + X\) gives \(X = 6.5\), which is not a valid digit.

3. **Uniqueness Check**:
   - Each decade (1980s, 1990s, 2000s) was checked, and only the 1990s provided a valid solution (1991).
   - Changing the last digit in a decade affects the sum and age inversely, ensuring at most one solution per decade.

Thus, Yevgeny Alexandrovich was born in 1991. On December 31, 2014, he would be \(2014 - 1991 = 23\) years old.

\[
\boxed{23}
\]

So the corresponding complete Lean code is: 

```lean4
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
```