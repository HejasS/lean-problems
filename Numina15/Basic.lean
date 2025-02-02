import Mathlib

theorem test : {x : ℕ| x ∈ Finset.range 20} = {x | 0 ≤ x ∧ x ≤ 19} := by
  ext x 
  constructor
  · simp; 
    have h : 3 = 3 := by rfl
    omega
  · simp; omega