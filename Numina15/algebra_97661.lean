import Mathlib

/- Suppose that $x,y$ and $z$ are complex numbers such that $xy=-80-320i,yz=60$ and $zx=-96+24i$, where $i=\sqrt{-1}$.
Then there are real numbers $a$ and $b$ such that $x+y+z=a+bi$. Find $a^2+b^2$ -/
theorem algebra_97661 {x y z : ℂ} (hxy : x * y = -80 - 320 * .I) (hyz : y * z = 60) (hzx : z * x = -96 + 24 * .I) (a b : ℝ) (hab: x + y + z = a + b * .I ) :
    a ^ 2 + b ^ 2 = 74 := by
  -- None of the variables are zero
  have h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
    split_ands
    <;> intro h
    <;> simp [h] at hxy hzx
    <;> apply_fun Complex.im at hxy hzx
    <;> simp at hxy hzx
  have : (-80 - 320 * Complex.I) ≠ 0 := by intro h; apply_fun Complex.im at h; simp at h
  -- Calculate z/y as zx/yx
  have : z / y = (-3 * .I) / 10                := by calc
    z / y = (z * x) / (y * x)                  := by rw [mul_div_mul_right]; exact h.left
        _ = (-96 + 24 * .I) / (-80 - 320 * .I) := by rw [mul_comm y x, hxy, hzx]
        _ = (-3 * .I) / 10                     := by field_simp [*]; ring_nf; rw [Complex.I_sq]; ring_nf
  -- Calculate z^2 as zy * (z/y)
  have : z ^ 2 = - 18 * .I := by calc
    z ^ 2 = (z * y) * (z / y)       := by field_simp [h]; ring
        _ = 60 * ((-3 * .I) / 10 )  := by rw [mul_comm z y, hyz, this]
        _ = - 18 * .I               := by ring_nf
  have : (z + (3 - 3 * .I)) * (z - (3 - 3 * .I)) = 0 := by
    ring_nf; simp [Complex.I_sq, this]; ring_nf
  -- Do the case distinction on z
  -- In both cases we can now easily calculate x and y by plugging z into the equations
  -- We see that in both cases a^2 + b^2 = 74
  simp at this; cases this with
  | inl hz =>
    have hz : z = -3 + 3 * .I := by
      rw [add_eq_zero_iff_eq_neg] at hz
      rw [hz]
      ring
    have : -3 + 3 * Complex.I ≠ 0 := by rw [← hz]; exact h.right.right
    have hy : y = -10 - 10 * .I := by
      rw [hz] at hyz
      rw [← eq_div_iff_mul_eq] at hyz
      rw [hyz]; field_simp; ring_nf; rw [Complex.I_sq]; ring
      assumption
    have hx : x = 20 + 12 * .I := by
      rw [hz] at hzx
      rw [mul_comm, ← eq_div_iff_mul_eq] at hzx
      rw [hzx]; field_simp; ring_nf; rw [Complex.I_sq]; ring_nf
      assumption
    rw [hx, hy, hz] at hab
    have hab' := hab
    apply_fun Complex.im at hab
    apply_fun Complex.re at hab'
    simp at hab hab'
    rw [← hab, ← hab']; norm_num
  | inr hz =>
    have hz : z = 3 - 3 * .I := by
      rwa [← sub_eq_zero]
    have : 3 - 3 * Complex.I ≠ 0 := by rw [← hz]; exact h.right.right
    have hy : y = 10 + 10 * .I := by
      rw [hz] at hyz
      rw [← eq_div_iff_mul_eq] at hyz
      rw [hyz]; field_simp; ring_nf; rw [Complex.I_sq]; ring
      assumption
    have hx : x = -20 - 12 * .I := by
      rw [hz] at hzx
      rw [mul_comm, ← eq_div_iff_mul_eq] at hzx
      rw [hzx]; field_simp; ring_nf; rw [Complex.I_sq]; ring_nf
      assumption
    rw [hx, hy, hz] at hab
    have hab' := hab
    apply_fun Complex.im at hab
    apply_fun Complex.re at hab'
    simp at hab hab'
    rw [← hab, ← hab']; norm_num
