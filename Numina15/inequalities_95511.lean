import Mathlib
open Finset Real

/- Let a,b,ca,b,c be positive real numbers such that $a + b + c = \sqrt[3]{abc}$. Prove that
\[
2(ab + bc + ca) + 4 \min (a^2, b^2, c^2) \geq a^2 + b^2 + c^2
\] -/
theorem inequalities_95511 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3)) :
    2 * (a * b + b * c + c * a) + 4 * Finset.min' {a^2, b^2, c^2} (by simp) ≥  a ^ 2 + b ^ 2 + c ^ 2 := by
  -- WLOG abc = 1, as the inequality is homogeneous
  wlog h_abc : a * b * c = 1
  · let t := (a * b * c) ^ (1 / 3 : ℝ)
    have t_pos : t > 0 := by positivity
    have h := this (a / t) (b / t) (c / t) (by positivity) (by positivity) (by positivity)
      (by rw [mul_rpow, mul_rpow, div_rpow, div_rpow, div_rpow]
          field_simp
          rw [← rpow_add, ← rpow_add]
          norm_num
          rw [h, mul_rpow, mul_rpow]
          simp
          all_goals positivity)
      (by field_simp; unfold t; rw [← rpow_add, ← rpow_add]; norm_num; all_goals positivity)
    field_simp at h
    have := @Finset.min'_image _ _ _ _ (· / (t ^ 2))
      (by apply Monotone.div_const; exact monotone_id; positivity)
      {a^2, b^2, c^2} (by simp)
    simp at this
    rw [this] at h
    linear_combination (norm := field_simp) t^2 * h
    ring_nf; positivity
  -- WLOG a^2 is the minimum, by symmetry
  wlog h_min : Finset.min' {a^2, b^2, c^2} _ = a^2
  · have h_min' := min'_mem {a^2, b^2, c^2} (by simp)
    simp only [WithTop.coe_pow, mem_insert, mem_singleton] at h_min'
    rcases h_min' with amin | bmin | cmin
    · contradiction
    · have hSet : ({a ^ 2, b ^ 2, c ^ 2}: Finset ℝ) = {b ^ 2, a ^ 2, c ^ 2} := by simp [Insert.comm (a^2) (b^2)]
      have h := this b a c hb ha hc (by rwa [mul_comm b a, add_comm b a]) (by rw [← h_abc]; ring) (by simp_rw [← hSet]; assumption)
      simp_rw [mul_comm a b, mul_comm b c, mul_comm c a, add_comm (a^2) (b^2),
        show b * a + c * b + a * c = b * a + a * c + c * b by ring, hSet]
      assumption
    · have hSet : ({a ^ 2, b ^ 2, c ^ 2}: Finset ℝ) = {c ^ 2, b ^ 2, a ^ 2} := by rw [pair_comm (b^2) _ , pair_comm (b^2) _, Insert.comm]
      have h := this c b a hc hb ha (by rw [show c + b + a = a + b + c by ring, h, show a * b * c = c * b * a by ring])
         (by rw [← h_abc]; ring) (by simp_rw [← hSet]; assumption)
      simp_rw [
        show a * b + b * c + c * a = c * b + b * a + a * c by ring,
        show a ^ 2 + b ^ 2 + c ^ 2 = c ^ 2 + b ^ 2 + a ^ 2 by ring, hSet]
      assumption
  simp_rw [h_min]
  -- Now we have a + b + c = 4
  simp [h_abc] at h
  -- We have that (2 * a - 1) ^ 2 ≥ 0
  -- Multiplying this by 4 / a is equivalent to the inequality were trying to show
  have h_pos: (2 * a - 1) ^ 2 ≥ 0 := by positivity
  linear_combination (norm := ring_nf) (4 / a) * h_pos
  apply Eq.le
  field_simp
  linear_combination -(4 * h_abc) + (-(3 * a ^ 2) + a * b + a * c + 4 * a) * h
