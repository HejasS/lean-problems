import Mathlib

open Finset

/- 12. For $r=1,2,3, \ldots$, let $u_{r}=1+2+3+\ldots+r$. Find the value of

$$

\frac{1}{\left(\frac{1}{u_{1}}\right)}+\frac{2}{\left(\frac{1}{u_{1}}+\frac{1}{u_{2}}\right)}+\frac{3}{\left(\frac{1}{u_{1}}+\frac{1}{u_{2}}+\frac{1}{u_{3}}\right)}+\cdots+\frac{100}{\left(\frac{1}{u_{1}}+\frac{1}{u_{2}}+\cdots+\frac{1}{u_{100}}\right)}

$$
 -/
theorem algebra_98902 {u : ℕ → ℚ} (hu : ∀ r, u r = ∑ i in Icc 1 r, i) :
    ∑ i in Icc 1 100, (i / (∑ j in Icc 1 i, (1 / u j))) = 2575 := by
  -- We first show that the sum of the first $r$ natural numbers is $r(r+1)/2$, by induction.
  let rec h1 : (r : ℕ) → ∑ i in Icc (1 : ℕ) r, i = (r : ℚ) * (r + 1) / 2
  | 0 => by simp
  | r + 1 => by
    have := h1 r
    simp [← Nat.Ico_succ_right, Finset.sum_Ico_succ_top] at this ⊢
    rw [this]
    ring_nf
  simp_rw [h1] at hu
  -- Then, we show that for all $i$, $\sum_{r=1}^{i} \frac{1}{u_r} = \frac{2i}{i+1}$, again by induction
  let rec h2 : (i : ℕ) → ∑ r in Icc (1 : ℕ) i, ((1 : ℚ) / u r) = (2 * i : ℚ) / (i + 1)
  | 0 => by simp
  | i + 1 => by
    have := h2 i
    simp [← Nat.Ico_succ_right, Finset.sum_Ico_succ_top, hu (i + 1)] at this ⊢
    rw [this]
    field_simp
    ring_nf
  -- We rewrite the goal using the above equation
  simp_rw [h2]
  ring_nf
  -- We can simplify because two $i$'s cancel
  conv =>
    enter [1,2,i,1,1]
    equals (if i = 0 then 0 else 1) =>
      split
      · simp [*]
      · rw [Rat.mul_inv_cancel (i : ℚ)]; norm_cast
  simp_rw [ite_mul, Finset.sum_ite]
  simp
  -- Now we again use the formula h1 to finish
  push_cast at h1
  rw [Finset.filter_true_of_mem]
  · rw [← Finset.sum_mul, Finset.sum_add_distrib, h1 100]
    simp; ring_nf
  · intro r hr; simp at hr; linarith

-- Finset.sum_Ico_succ_top
