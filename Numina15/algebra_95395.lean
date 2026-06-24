import Mathlib
open Real

/- Let $ x $ and $ y $ be real numbers such that $ \sin y \sin x ​= 3 $ and $ \cos y \cos x ​= 21 $​. The value of $\frac{\sin 2x}{\sin 2y} + \frac{\cos 2x}{\cos 2y}$ can be expressed in the form $\frac p q$​, where $ p $ and $ q $ are relatively prime positive integers. Find $ p + q $. -/
theorem algebra_95395 (x y : ℝ) (h₁ : sin x / sin y = 3) (h₂ : cos x / cos y = 1 / 2) (p q : ℕ) (h₃ : Nat.Coprime p q) (h₄ : sin (2 * x) / sin (2 * y) + cos (2 * x) / cos (2 * y) = p / q) : p + q = 107 := by
  -- All the following are nonzero, as otherwise the given equaitons couldn't hold
  have : sin y ≠ 0 := by intro h; simp [h] at h₁
  have : cos y ≠ 0 := by intro h; simp [h] at h₂
  -- We can calculate sin $(2 * x) / \sin (2 * y)$ using the double angle
  -- formula and the given equations
  have h₅ : sin (2 * x) / sin (2 * y) = 3 / 2 := by
    rw [sin_two_mul, sin_two_mul]
    field_simp at h₁ h₂ ⊢
    rw [h₁, ←h₂]
    ring
  -- We calculate the second term as follows:
  have h₆ : cos (2 * x) / cos (2 * y) = -19 / 29 := by
    -- We have the equations $\cos x = 1/2 \cos y$
    apply_fun (· * cos y) at h₂
    simp only [isUnit_iff_ne_zero, ne_eq, not_false_eq_true, IsUnit.div_mul_cancel, this] at h₂
    -- as well as $\sin x = 3 \sin y$
    field_simp at h₁
    -- Squaring these two and adding them together, we get (using the identity $\sin ^ 2 + \cos ^ 2 = 1$): $\sin y ^ 2 = 3 / 35$
    have hy: sin y ^ 2 = 3 / 35 := by
      linear_combination' (norm := ring_nf) -4 / 35 * (h₁ * h₁ + h₂ * h₂)
      rw [show cos x ^ 2 = 1 - sin x ^ 2 by linarith [cos_sq_add_sin_sq x],
          show cos y ^ 2 = 1 - sin y ^ 2 by linarith [cos_sq_add_sin_sq y]]
      ring_nf
    -- Plugging this into $h₁ ^ 2$, we get: $\sin x ^ 2 = 27 / 35$
    have hx: sin x ^ 2 = 27 / 35 := by
      linear_combination' (norm := ring_nf) h₁ * h₁
      rw [hy]; ring_nf
    -- Using the identity $\cos (2x) = 2 cos ^ 2 (x) - 1$, as well as $\sin ^ 2 + \cos ^ 2 = 1$, we can now calculate the second term
    rw [cos_two_mul, cos_two_mul,
        show cos x ^ 2 = 1 - sin x ^ 2 by linarith [cos_sq_add_sin_sq x],
        show cos y ^ 2 = 1 - sin y ^ 2 by linarith [cos_sq_add_sin_sq y]]
    simp only [hx, hy]
    ring_nf
  -- Plugging this in, we see that $p / q = 49 / 58$
  rw [h₅, h₆] at h₄
  ring_nf at h₄; norm_cast at h₄
  have hpq : Rat.divInt p q = Rat.divInt 49 58 := by rify; rw [h₄]; ring_nf
  have : q ≠ 0 := by intro h; simp [h] at h₄
  -- Since 49 and 58 are coprime, it follows that p = 49 and q = 58
  have : (Rat.divInt 49 58).den = 58 := by decide
  have : (Rat.divInt 49 58).num = 49 := by decide
  have h₇ : q = 58 := by
    apply_fun Rat.den at hpq
    rw [Rat.den_mk] at hpq
    simp [*] at hpq
    exact hpq
  have h₈ : p = 49 := by
    apply_fun Rat.num at hpq
    rw [Rat.num_mk] at hpq
    simp [*, - h₇] at hpq
    rw [show (q : ℤ).sign = 1 by rw [h₇]; decide] at hpq
    linarith
  -- Thus, $p + q = 107$
  simp [h₇, h₈]
