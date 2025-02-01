import Mathlib
open Nat List

/- Find the least positive integer such that when its leftmost digit is deleted, the resulting integer is $\frac 1 {29}$​ of the original integer. -/
theorem number_theory_93086 : IsLeast {N | N > 0 ∧ (ofDigits 10 (digits 10 N).dropLast) * 29 = N} 725 := by
  constructor
  -- Show that 725 satisfies the property
  · simp
    show 25 * 29 = 725
    ring
  -- Show that every other number $N$ satisfying the property is at least 725
  · intro N ⟨hN₀, hN₁⟩
    -- Define a to be the list of digits. It is nonempty since N > 0
    let a := digits 10 N; have ha : a ≠ [] := by rw [digits_ne_nil_iff_ne_zero]; linarith
    -- Define N₀ to be the number obtained from N by removing the last digit
    let N₀ := ofDigits 10 a.dropLast
    -- Write N₀ in terms of N and its last digit and plug this into the assumption
    have h₀ : N = ofDigits 10 a := by rw [← ofDigits_digits 10 N]
    rw [← dropLast_append_getLast ha, ofDigits_append, show ofDigits 10 a.dropLast = N₀ by rfl, length_dropLast, ofDigits_singleton] at h₀
    -- Plug this into the assumption
    change N₀ * 29 = N at hN₁
    rw [h₀] at hN₁
    have h₁ : 7 * 4 * N₀ = 10 ^ (a.length - 1) * a.getLast ha := by linarith
    -- We see that 7 divides a power of 10 times the last digit of N
    -- Since it is prime it divides one of the two factors
    have h₂ : 7 ∣ 10 ^ (a.length - 1) * a.getLast ha := by rw [← h₁]; use (4 * N₀); ring
    rw [Nat.Prime.dvd_mul] at h₂
    -- The first case is impossible since then 7 | 10 would follows, in the other case we get that the last digit of N is 7
    have h₃ : a.getLast ha = 7 := by
      match h₂ with
      | Or.inl h₂ => have := Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 7 by norm_num) h₂; omega
      | Or.inr h₂ =>
        have : a.getLast ha ≠ 0 := by apply getLast_digit_ne_zero; linarith
        have : a.getLast ha < 10 := by
          apply digits_lt_base
          · simp
          · apply getLast_mem
        omega
    -- Plug this into our previous equation
    rw [h₃] at h₀ h₁
    have h₁ : 4 * N₀ = 10 ^ (a.length - 1) := by omega
    have h₄ : a.length - 1 ≥ 2 := by
      by_contra!
      have : a.length = 0 ∨ a.length = 1 ∨ a.length = 2 := by omega
      match this with
      | Or.inl ha₀ => rw [ha₀] at h₁; omega
      | Or.inr (Or.inl ha₁) => rw [ha₁] at h₁; omega
      | Or.inr (Or.inr ha₂) => rw [ha₂] at h₁; omega
    -- Now we can show that 4 * N ≥ (28 + 1) * 10 ^ 2 = 2900, which shows the claim
    have h₅ := calc
      4 * N = 4 * N₀ + 4 * 10 ^ (a.length - 1) * 7               := by rw [h₀]; ring
          _ = 10 ^ (a.length - 1) + 4 * 10 ^ (a.length - 1) * 7  := by rw [h₁]
          _ = 29 * 10 ^ (a.length - 1)                           := by ring
          _ ≥ 29 * 10 ^ 2                                        := by apply Nat.mul_le_mul_left; apply pow_le_pow <;> simp [h₄]
          _ = 2900                                               := by norm_num
    omega
    -- 7 is prime
    norm_num
