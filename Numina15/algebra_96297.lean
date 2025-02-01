import Mathlib
open Complex

/- $A + B + C$ is an integral multiple of $\pi$. $x,y$ and $z$ are real numbers. If $x\sin(A) + y\sin(B) + z\sin(C) = x^2\sin(2A) + y^2\sin(2B) + z^2\sin(2C) = 0,
show that $ x^n\sin(nA) + y^n\sin(nB) + z^n\sin(nC) = 0$ for any positive integer $n$. -/
theorem algebra_96297 {A B C : ℝ} (hABC : ∃ k : ℤ, A + B + C = k * Real.pi)
    (x y z : ℝ) (h1 : x * Real.sin A + y * Real.sin B + z * Real.sin C = 0)
    (h2 : x ^ 2 * Real.sin (2 * A) + y ^ 2 * Real.sin (2 * B) + z ^ 2 * Real.sin (2 * C) = 0)
    (n : ℕ) (hn : n > 0) :
    x ^ n * Real.sin (n * A) + y ^ n * Real.sin (n * B) + z ^ n * Real.sin (n * C) = 0 := by
  -- Introduce complex numbers a b and c
  let a := x * exp (I * A)
  let b := y * exp (I * B)
  let c := z * exp (I * C)
  obtain ⟨k, hk⟩ := hABC
  -- abc is real, because exp (I * (A + B + C)) = exp (I * k * pi) is
  have h3 : (a * b * c).im = 0 := by calc
    (a * b * c).im
      = (x * exp (I * A) * (y * exp (I * B)) * (z * exp (I * C))).im      := by rfl
    _ = ((x * y * z : ℝ)  * (exp (I * A) * exp (I * B) * exp (I * C))).im := by norm_num; ring_nf
    _ = (x * y * z) * ((exp (I * A) * exp (I * B) * exp (I * C))).im      := by simp
    _ = x * y * z * (exp (I * A + I * B + I * C)).im                      := by repeat rw [← exp_add]
    _ = x * y * z * (exp ((A + B + C) * I)).im                            := by ring_nf
    _ = 0                                                                 := by rw [exp_mul_I]; norm_cast; rw [hk]; simp; apply Or.inr; norm_cast
  -- a + b + c is real, because the imaginary part of a (resp. b or c)
  -- is precisely x * sin (A) (resp. y * sin (B) or z * sin (C))
  -- and this sum is zero yb assumption
  have h1 : (a + b + c).im = 0 := by calc
    (a + b + c).im
      = (x * exp (I * A)).im + (y * exp (I * B)).im + (z * exp (I * C)).im := by unfold a b c; simp
    _ = x * (exp (I * A)).im + y * (exp (I * B)).im + z * (exp (I * C)).im := by simp
    _ = x * Real.sin A + y * Real.sin B + z * Real.sin C                   := by simp [mul_comm I, exp_mul_I]; norm_cast
    _ = 0                                                                  := by assumption
  -- The same argument is possible to show that a ^ 2 + b ^ 2 + c ^ 2 is real
  have h2 : (a ^ 2+ b ^ 2 + c ^ 2).im = 0 := by calc
    (a ^ 2+ b ^ 2 + c ^ 2).im
      = (x ^ 2 * exp (2 * I * A)).im + (y ^ 2 * exp (2 * I * B)).im + (z ^ 2 * exp (2 * I * C)).im := by unfold a b c; simp [mul_pow, ← exp_nat_mul]; ring_nf
    _ = x ^ 2* Real.sin (2 * A) + y ^ 2 * Real.sin (2 * B) + z ^ 2 * Real.sin (2 * C)              := by simp [mul_comm I, mul_assoc _ I, ← mul_assoc _ _ I, exp_mul_I]; norm_cast; ring_nf
    _ = 0                                                                                          := by assumption
  -- Then also a * b + b * c + c + a is real as it is a linear combination of the previous two
  have h2' : (a * b + b * c + c * a).im = 0 := by calc
    (a * b + b * c + c * a).im
      = (1/2 * ((a + b + c)^ 2  - (a ^ 2 + b ^ 2 + c ^ 2))).im := by ring_nf
    _ = 1/2 * ((a + b + c) ^ 2).im - 1/2 * (a ^ 2 + b ^ 2 + c ^ 2).im := by simp; ring
    _ = 0 := by simp only [pow_two (a + b + c), mul_im, h1, h2]; simp
  -- By the same argument as before it suffices to show that
  -- a ^ n + b ^ n + c ^ n is real
  suffices habc: (a ^ n + b ^ n + c ^ n).im = 0 by
    unfold a b c at habc
    simp [mul_pow, ← exp_nat_mul] at habc;
    simp [mul_comm I, mul_assoc _ I, ← mul_assoc _ _ I, exp_mul_I] at habc
    norm_cast at habc; ring_nf at habc; assumption
  -- We show this by induction on n:
  let rec hn : (m: ℕ) → (a ^ m + b ^ m + c ^ m).im = 0
  | 0 => by simp -- n = 0 is trivial
  | 1 => by simp; exact h1 -- n = 1 and 2 were shown before
  | 2 => by simp; exact h2
  | m + 3 => by -- For bigger m we can reduce to smaller m by Newton sums
    have h: (a ^ (m + 3) + b ^ (m + 3) + c ^ (m + 3))
      = (a ^ (m + 2) + b ^ (m + 2) + c ^ (m + 2)) * (a + b + c)
      - (a ^ (m + 1) + b ^ (m + 1) + c ^ (m + 1)) * (a * b  + b * c + c * a)
      + ((a ^ (m) + b ^ (m) + c ^ (m))) * (a * b * c)                       := by ring_nf
    apply_fun Complex.im at h
    rw [h]
    simp only [add_im, sub_im]
    simp only [mul_im, h1, h2', h3, hn m, hn (m+1), hn (m+2)]
    simp
  exact hn n
