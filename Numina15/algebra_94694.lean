import Mathlib
open Polynomial Int
set_option maxHeartbeats 0

/- Find the smallest positive integer $ n $ with the property that the polynomial $x ^ 4- nx + 64$ can be written as a product of two nonconstant polynomials with integer coefficients. -/
theorem algebra_94694 : IsLeast { n : ℕ | n > 0 ∧ ∃ p q r s t u : ℤ, (X : Polynomial ℤ) ^ 4 - n • (X : Polynomial ℤ) + ((63 : ℤ) : ℤ[X]) = (p • X ^ 2 + q • X + (r : ℤ [X])) * (s • X ^ 2 + t • X + (u : ℤ[X]))} 8 := by
  constructor
  -- First we'll show that 8 is possible:
  · split_ands
    simp
    -- The example is $x ^ 4 - 8x + 63 = (x ^ 2)
    use 1, -4, 7, 1, 4, 9
    simp [Polynomial.smul_eq_C_mul, ←pow_mul']
    ring_nf
  · intro n ⟨hn, p, q, r, s, t, u, h⟩
    have h₄ : p * s = 1 := by
      apply_fun (coeff · 4) at h
      simp only [add_mul, mul_add, smul_eq_C_mul] at h
      ring_nf at h
      simp at h
      rw [← C_eq_intCast, show coeff (63 : ℤ[X]) 4 = 0 by simp, coeff_C, coeff_X] at h
      simp at h
      linarith
    wlog hp : p = 1
    · have hp : p ∣ 1 := by use s; linarith
      have hp := isUnit_of_dvd_one hp
      rw [Int.isUnit_iff] at hp
      have hp : p = -1 := by omega
      apply (this hn 1 (-q) (-r) (-s) (-t) (-u))
      linear_combination (norm := ring_nf) h
      ring_nf
      simp [smul_eq_C_mul, hp]
      ring_nf
      simp [hp] at h₄
      linarith; rfl
    simp [hp] at h₄
    simp [hp, h₄] at h
    have h₀ : r * u = 63 := by
      apply_fun (coeff · 0) at h
      simp only [nsmul_eq_mul, coeff_add, coeff_sub, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte,
        mul_coeff_zero, coeff_natCast_ite, coeff_X_zero, mul_zero, sub_self, coeff_ofNat_zero,
        zero_add, zsmul_eq_mul, intCast_coeff_zero, Int.cast_id, add_zero] at h
      linarith
    have h₁ : q * u + r * t = -n := by
      apply_fun (coeff · 1) at h
      simp only [add_mul, mul_add, smul_eq_C_mul] at h
      ring_nf at h
      simp at h
      rw [← C_eq_intCast, show coeff (63 : ℤ[X]) 1 = 0 by simp, coeff_C] at h
      simp at h
      linarith
    have h₂ : r + u + q * t = 0 := by
      apply_fun (coeff · 2) at h
      simp only [add_mul, mul_add, smul_eq_C_mul] at h
      ring_nf at h
      simp at h
      rw [← C_eq_intCast, show coeff (63 : ℤ[X]) 2 = 0 by simp, coeff_C, coeff_X] at h
      simp at h
      linarith
    have h₃ : q + t = 0 := by
      apply_fun (coeff · 3) at h
      simp only [add_mul, mul_add, smul_eq_C_mul] at h
      ring_nf at h
      simp at h
      rw [← C_eq_intCast, show coeff (63 : ℤ[X]) 3 = 0 by simp, coeff_C, coeff_X] at h
      simp at h
      linarith
    have h₂ : r + u = q ^ 2 := by linear_combination h₂ - 1 * q * h₃
    have : r ∣ 63 := by use u; linarith
    rw [← Int.natAbs_dvd] at this
    norm_cast at this
    have := Nat.mem_divisors.mpr ⟨this, by positivity⟩
    rw [show Nat.divisors 63 = {1, 3, 7, 9, 21, 63} by decide] at this
    simp at this
    rcases this with hr | hr | hr | hr | hr | hr
    <;> zify at hr <;> rcases eq_or_eq_neg_of_abs_eq hr with hr1 | hr1
    <;> simp [hr1] at h₀ <;> simp [h₀ , hr1] at h₂ <;> try omega
    · rw [show (64 : ℤ) = 8 ^ 2 by rfl, sq_eq_sq_iff_eq_or_eq_neg] at h₂
      rcases h₂ with hq | hq
      <;> rw [show t = -q by linarith, ← hq, h₀, hr1] at h₁ <;> linarith
    · simp [show u = -63 by linarith] at h₂; nlinarith
    · simp [show u = 21 by linarith] at h₂; exfalso; apply @Nat.not_exists_sq 4 24
      any_goals linarith
      use q.natAbs; zify; rw [← pow_two]; simp [h₂]
    · simp [show u = -21 by linarith] at h₂; nlinarith
    · simp [show u = 9 by linarith] at h₂
      rw [show (16 : ℤ) = 4 ^ 2 by rfl, sq_eq_sq_iff_eq_or_eq_neg] at h₂
      rcases h₂ with hq | hq
      <;> rw [show t = -q by linarith, ← hq, show u = 9 by linarith, hr1] at h₁ <;> linarith
    · simp [show u = -9 by linarith] at h₂; nlinarith
    · simp [show u = 7 by linarith] at h₂
      rw [show (16 : ℤ) = 4 ^ 2 by rfl, sq_eq_sq_iff_eq_or_eq_neg] at h₂
      rcases h₂ with hq | hq
      <;> rw [show t = -q by linarith, ← hq, show u = 7 by linarith, hr1] at h₁ <;> linarith
    · simp [show u = -7 by linarith] at h₂; nlinarith
    · simp [show u = 3 by linarith] at h₂; exfalso; apply @Nat.not_exists_sq 4 24
      any_goals linarith
      use q.natAbs; zify; rw [← pow_two]; simp [h₂]
    · simp [show u = -3 by linarith] at h₂; nlinarith
    · rw [show (64 : ℤ) = 8 ^ 2 by rfl, sq_eq_sq_iff_eq_or_eq_neg] at h₂
      rcases h₂ with hq | hq
      <;> rw [show t = -q by linarith, ← hq, h₀, hr1] at h₁ <;> linarith
    · simp [show u = -1 by linarith] at h₂; nlinarith
