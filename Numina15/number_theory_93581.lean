import Mathlib
open Int

/- The largest number by which the expression $n ^ 3 − n$ is divisible for all possible integral values of $n$, is:
(A) 2 (B) 3 (C) 4 (D) 5 (E) 6 -/

theorem number_theory_93581 : IsGreatest {x | ∀ n : ℤ, x ∣ n ^ 3 - n} 6 := by
  apply And.intro <;> simp [mem_upperBounds]
  -- Show that 6 divides n ^ 3 - n
  · intro n
    rw [pow_three]
    rw [← EuclideanDomain.mod_eq_zero]
    -- Do a case distrinction of n mod 6
    mod_cases h: n % 6
    <;> unfold ModEq at h
    -- Plug in the value of n mod 6
    <;> rw [sub_emod, mul_emod, mul_emod n n, h]
    <;> simp
  -- Show that 6 is an upper bound for every x in the set
  · intro x hn
    -- Plug in n = 2: x | 6 => x ≤ 6
    exact le_of_dvd (by simp) (hn 2)
