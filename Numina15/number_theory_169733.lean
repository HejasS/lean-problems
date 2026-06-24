import Mathlib

/- 16. $[\mathbf{9}]$ Solve for $x$ :

$$

x\lfloor x\lfloor x\lfloor x\lfloor x\rfloor\rfloor\rfloor\rfloor=122 \text {. }

$$
 -/
theorem number_theory_169733 (x : ℝ) :
    x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ = 122 ↔ x = 122 / 41 := by
  constructor
  -- Suppose we are given this equation
  · intro hx
    -- Then we may assume WLOG that $x > 0$, as otherwise the left-hand side is nonpositive
    wlog h1 : x > 0
    · have hx' : x < 0 := by by_contra! hx'; rcases hx'.lt_or_eq with h | h; linarith; simp [← h] at hx
      have : ⌊ x ⌋ < (0 : ℝ) := by simpa [Int.floor_lt]
      have : x * ⌊ x ⌋ > 0 := by nlinarith
      have : ⌊ x * ⌊ x ⌋ ⌋ ≥ 0 := by simp [Int.le_floor]; linarith
      rify at this
      have : x * ⌊ x * ⌊ x ⌋ ⌋ ≤ 0 := by nlinarith
      have : ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≤ (0 : ℝ) := by linarith [Int.floor_le (x * ⌊ x * ⌊ x ⌋ ⌋)]
      have : x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≥ 0 := by nlinarith
      have : ⌊ x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ⌋ ≥ 0 := by have := Int.floor_le_floor this; simp at this; linarith
      rify at this
      have : x * ⌊ x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ⌋ ≤ 0 := by nlinarith
      linarith
    -- Now assume for contradiction that $x \neq 122 / 41$
    by_contra! h
    have h2 : x < 122 / 41 ∨ 122 / 41 < x := h.lt_or_lt
    rcases h2 with h2 | h2
    -- If $x < 122 / 41$, then the left-hand side is less than $122$, by estimating all the inner terms step by step
    · have : ⌊ x ⌋ ≤ 2 := by have := Int.floor_le_floor h2.le; norm_num at this; linarith
      rify at this
      have : ⌊ x ⌋ ≥ 0 := by positivity
      have : x * ⌊ x ⌋ ≤ 244 / 41 := by nlinarith
      have : ⌊ x * ⌊ x ⌋ ⌋ ≤ 5 := by have := Int.floor_le_floor this; norm_num at this; linarith
      rify at this
      have : ⌊ x * ⌊ x ⌋ ⌋ ≥ 0 := by positivity
      have : x * ⌊ x * ⌊ x ⌋ ⌋ ≤ 610 / 41 := by nlinarith
      have : ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≤ 14 := by have := Int.floor_le_floor this; norm_num at this; linarith
      rify at this
      have : ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≥ 0 := by positivity
      have : x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≤ 1708 / 41 := by nlinarith
      have : ⌊ x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ⌋ ≤ 41 := by have := Int.floor_le_floor this; norm_num at this; linarith
      rify at this
      have : x * ⌊ x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ⌋ < 122 := by nlinarith
      linarith
    -- If $x > 122 / 41$, then the left-hand side is greater than $122$, by estimating all the inner terms step by step
    · have : ⌊ x ⌋ ≥ 2 := by have := Int.floor_le_floor h2.le; norm_num at this; linarith
      rify at this
      have : x * ⌊ x ⌋ ≥ 244 / 41 := by nlinarith
      have : ⌊ x * ⌊ x ⌋ ⌋ ≥ 5 := by have := Int.floor_le_floor this; norm_num at this; linarith
      rify at this
      have : x * ⌊ x * ⌊ x ⌋ ⌋ ≥ 610 / 41 := by nlinarith
      have : ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≥ 14 := by have := Int.floor_le_floor this; norm_num at this; linarith
      rify at this
      have : x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ≥ 1708 / 41 := by nlinarith
      have : ⌊ x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ⌋ ≥ 41 := by have := Int.floor_le_floor this; norm_num at this; linarith
      rify at this
      have : x * ⌊ x * ⌊ x * ⌊ x * ⌊ x ⌋ ⌋ ⌋ ⌋ > 122 := by nlinarith
      linarith
  -- Conversely, if $x = 122 / 41$, then the equation holds
  · intro hx; rw [hx]; norm_num
