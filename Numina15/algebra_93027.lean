import Mathlib
open Finset Set Real

/- Find the sum of the values of $x$ such that $\cos ^ ⁡3 3x + \cos ^⁡3 5x = 8 \cos⁡ ^ 3 4x \cos ^ ⁡3 x$, where $x$ is measured in degrees and $100 < x < 200$ -/
theorem algebra_93027
    (A: Finset ℝ)
    (hA: A.toSet = { x | x ∈ Set.Ioo 100 200 ∧ cos (3 * x * π / 180)^3 + cos (5 * x * π / 180)^3 = 8 * cos (4 * x * π / 180)^3 * cos (x * π / 180)^3}):
    ∑ x ∈ A, x = 906 := by
  -- It suffices to show that the set is precisely the following one:
  suffices A = {150,126,162,198,112.5,157.5} by rw [this]; norm_num
  have h_fin : A.toSet.Finite := by simp
  rw [← (@Set.toFinset_inj _ A.toSet _ _ (by rw [← hA]; infer_instance))] at hA
  simp at hA; rw [hA]
  have : {150, 126, 162, 198, 112.5, 157.5} = ({150, 126, 162, 198, 112.5, 157.5} : Finset ℝ ).toSet.toFinset := by simp
  rw [this, @Set.toFinset_inj]
  -- We show both inclusions
  apply eq_of_subset_of_subset
  -- First (hard) part: Every x in the set is one of those in our list
  · simp; intro x hx
    simp at hx; obtain ⟨hx_bounds, hx⟩ := hx
    -- Rewrite the given equation in terms of $x' = x * π / 180$
    rw [mul_assoc, ← mul_div, mul_assoc 4, ← mul_div 4, mul_assoc 5, ← mul_div 5] at hx
    generalize hxx': x * π / 180 = x' at *
    -- We have the following equation by the cosine sum formula
    have h_cos: 2 * cos (4 * x') * cos (x') = cos (5 * x') + cos (3 * x') := by
      rw [cos_add_cos]
      ring_nf
    -- Substitute this in the given equation `hx`
    have : 8 * cos (4 * x') ^ 3 * cos x' ^ 3 = (2 * cos (4 * x') * cos x') ^ 3 := by ring_nf
    rw [this, h_cos] at hx
    -- Set $a := \cos (3 * x'), b := \cos (5 * x')$
    generalize ha: cos (3 * x') = a at *
    generalize hb: cos (5 * x') = b at *
    -- hx then becomes the following equation
    have hx: a * b * (a + b) = 0 := by ring_nf at hx; simp at hx; rw [← add_mul] at hx; simp at hx; ring_nf; exact hx
    -- Now either a, b or a + b is zero
    rw [mul_eq_zero, mul_eq_zero] at hx
    match hx with
    -- case a = 0
    -- Use the fact that $\cos (t) = 0 \iff t = (2k + 1)π$ for some $k \in ℕ$
    -- to solve for $x$
    | Or.inl (Or.inl ha₀) =>
      rw [← ha, cos_eq_zero_iff] at ha₀
      obtain ⟨k, hk⟩ := ha₀
      rw [← hxx'] at hk
      have : π * π⁻¹ = 1 := by field_simp
      have hk: x = (2 * k + 1) * 30 := by
        apply_fun (· * 60 / π) at hk
        ring_nf at hk; rw [mul_assoc, this] at hk
        linarith
      rw [hk] at hx_bounds
      norm_cast at hx_bounds
      have : k = 2 := by omega
      rw [this] at hk; rw [hk]; norm_num
    -- case b = 0. Solve for $x$ in the same way as before
    | Or.inl (Or.inr hb₀) =>
      rw [←hb, cos_eq_zero_iff] at hb₀
      obtain ⟨k, hk⟩ := hb₀
      rw [← hxx'] at hk
      have : π * π⁻¹ = 1 := by field_simp
      have hk: x = (2 * k + 1) * 18 := by
        apply_fun (· * 60 / π) at hk
        ring_nf at hk; rw [mul_assoc _ π π⁻¹, this] at hk
        linarith
      rw [hk] at hx_bounds
      norm_cast at hx_bounds
      have : k = 3 ∨ k = 4 ∨ k = 5 := by omega
      match this with
      | Or.inl h => rw [h] at hk; rw [hk]; norm_num
      | Or.inr (Or.inl h) => rw [h] at hk; rw [hk]; norm_num
      | Or.inr (Or.inr h) => rw [h] at hk; rw [hk]; norm_num
    -- case a + b = 0.
    -- The equation `h_cos` says that $cos(x * pi / 180) * cos(4 * x * pi / 180) = a + b$
    -- Thus cos(x * pi / 180) = 0, or cos(4 * x * pi / 180) = 0
    | Or.inr hab₀ =>
      rw [add_comm, ← h_cos, mul_eq_zero] at hab₀
      simp at hab₀
      match hab₀ with
      -- case $\cos(x \cdot pi / 180) = 0$: Solve for $x$ as before
      | Or.inr h₀ =>
        rw [cos_eq_zero_iff] at h₀
        obtain ⟨k, hk⟩ := h₀
        rw [← hxx'] at hk
        have : π * π⁻¹ = 1 := by field_simp
        have hk: x = (2 * k + 1) * 90 := by
          apply_fun (· * 60 / π) at hk
          ring_nf at hk; rw [mul_assoc _ π π⁻¹, this] at hk
          linarith
        rw [hk] at hx_bounds
        norm_cast at hx_bounds
        omega
      -- case $\cos(4x \cdot pi / 180) = 0$: Solve for $x$ as before
      | Or.inl h₀ =>
        rw [cos_eq_zero_iff] at h₀
        obtain ⟨k, hk⟩ := h₀
        rw [← hxx'] at hk
        have : π * π⁻¹ = 1 := by field_simp
        have hk: x = (2 * k + 1) * 22.5 := by
          apply_fun (· * 60 / π) at hk
          ring_nf at hk; rw [mul_assoc _ π π⁻¹, this] at hk
          linarith
        rw [hk] at hx_bounds
        obtain ⟨hx_lb, hx_ub⟩ := hx_bounds
        apply_fun (fun x: ℝ => x * 2) at hx_lb
        apply_fun (fun x: ℝ => x * 2) at hx_ub
        ring_nf at hx_lb; ring_nf at hx_ub
        norm_cast at hx_lb; norm_cast at hx_ub
        have: k = 2 ∨ k = 3 := by omega
        cases this <;> simp [*] <;> norm_num
        all_goals apply StrictMono.mul_const <;> try simp
        all_goals exact strictMono_id
  -- Second part, showing that all these values satisfy the equation
  · intro x hx
    rw [mem_setOf]
    simp at hx
    -- We do the same manipulation to the equation as above
    rw [mul_assoc, ← mul_div, mul_assoc 4, ← mul_div 4, mul_assoc 5, ← mul_div 5]
    generalize hxx': x * π / 180 = x' at *
    have h_cos: 2 * cos (4 * x') * cos (x') = cos (5 * x') + cos (3 * x') := by
      rw [cos_add_cos]
      ring_nf
    have : 8 * cos (4 * x') ^ 3 * cos x' ^ 3 = (2 * cos (4 * x') * cos x') ^ 3 := by ring_nf
    rw [this, h_cos]
    generalize ha: cos (3 * x') = a at *
    generalize hb: cos (5 * x') = b at *
    ring_nf; simp; rw [← add_mul]; simp
    -- So it suffices to show in each case that a = 0, b = 0, or a + b = 0
    -- This can easily be checked in each case
    suffices hx: (100 < x ∧ x < 200) ∧ a * b * (a + b) = 0 by
      ring_nf at hx; assumption
    apply Or.elim hx
    -- case x = 150
    · intro hx
      rw [hx] at hxx'; rw [← hxx'] at ha; rw [← ha]
      rw [hx]; split_ands <;> try linarith
      simp; apply Or.inl; apply Or.inl
      ring_nf
      rw [cos_eq_zero_iff]; use 2; ring_nf
    intro hx; apply Or.elim hx
    -- case x = 126
    · intro hx
      rw [hx] at hxx'; rw [← hxx'] at hb; rw [← hb]
      rw [hx]; split_ands <;> try linarith
      simp; apply Or.inl; apply Or.inr
      ring_nf
      rw [cos_eq_zero_iff]; use 3; ring_nf
    intro hx; apply Or.elim hx
    -- case x = 162
    · intro hx
      rw [hx] at hxx'; rw [← hxx'] at hb; rw [← hb]
      rw [hx]; split_ands <;> try linarith
      simp; apply Or.inl; apply Or.inr
      ring_nf
      rw [cos_eq_zero_iff]; use 4; ring_nf
    intro hx; apply Or.elim hx
    -- case x = 198
    · intro hx
      rw [hx] at hxx'; rw [← hxx'] at hb; rw [← hb]
      rw [hx]; split_ands <;> try linarith
      simp; apply Or.inl; apply Or.inr
      ring_nf
      rw [cos_eq_zero_iff]; use 5; ring_nf
    intro hx; apply Or.elim hx
    -- case x = 112.5
    · intro hx
      rw [hx] at hxx'; rw [← hxx'] at h_cos; rw [add_comm, ← h_cos]
      rw [hx]; split_ands <;> try linarith
      simp; apply Or.inr; apply Or.intro_left
      ring_nf
      rw [cos_eq_zero_iff]; use 2; ring_nf
    -- case x = 157.5
    · intro hx
      rw [hx] at hxx'; rw [← hxx'] at h_cos; rw [add_comm, ← h_cos]
      rw [hx]; split_ands <;> try linarith
      simp; apply Or.inr; apply Or.intro_left
      ring_nf
      rw [cos_eq_zero_iff]; use 3; ring_nf
