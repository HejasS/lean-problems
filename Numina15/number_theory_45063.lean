import Mathlib
open Nat

/- Prove that there exists a positive integer $k$ such that $k ⬝ 2 ^ n + 1$  is composite for every integer $n$. -/
theorem number_theory_45063 :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, ¬Nat.Prime (k * 2 ^ n + 1) := by
  use 2935363331541925531; simp
  intro n
  -- Show that $n$ falls into one of the following residue classes:
  have h_congr:
      n % 2 = 1 ∨
      n % 4 = 2 ∨
      n % 8 = 4 ∨
      n % 16 = 8 ∨
      n % 32 = 16 ∨
      n % 64 = 32 ∨
      n % 64 = 0 := by
    omega
  intro h_prime
  revert h_congr; simp only [imp_false, not_or]
  split_ands
  -- Do the case distiction
  · intro h -- If n % 2 = 1, then k is divisible by 3
    have: 3 = 1 ∨ 3 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 2), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
  · intro h -- If n % 4 = 2, then k is divisible by 5
    have: 5 = 1 ∨ 5 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 4), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
  · intro h -- If n % 8 = 4, then k is divisible by 17
    have: 17 = 1 ∨ 17 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 8), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
  · intro h -- If n % 16 = 8, then k is divisible by 257
    have: 257 = 1 ∨ 257 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 16), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
  · intro h -- If n % 32 = 16, then k is divisible by 65537
    have: 65537 = 1 ∨ 65537 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 32), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
  · intro h -- If n % 64 = 32, then k is divisible by 6700417
    have: 6700417 = 1 ∨ 6700417 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 64), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
  · intro h -- If n % 64 = 0, then k is divisible by 641
    have: 641 = 1 ∨ 641 = 2935363331541925531 * 2 ^ n + 1 := by
      apply (Prime.eq_one_or_self_of_dvd h_prime)
      zify
      rw [← EuclideanDomain.mod_eq_zero]
      norm_cast
      rw [← (mod_add_div n 64), h, pow_add, pow_mul, add_mod, mul_mod]
      simp only [reduceMod, reducePow, reduceAdd, one_mul, dvd_refl, mod_mod_of_dvd, one_mod, mul_mod, pow_mod, mod_succ, one_mod, one_pow, mul_one, mod_self]
    omega
