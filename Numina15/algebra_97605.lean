import Mathlib
open Real

/- Suppose $\cos x=0$ and $\cos⁡ (x+z)=1/2$. What is the smallest possible positive value of $z$?
(A) π/6 (B) π/3 (C) π/2 (D) 5π/6 (E) 7π/6​ -/
theorem algebra_97605 :
IsLeast {z : ℝ | 0 < z ∧ ∃ x : ℝ, cos x = 0 ∧ cos (x + z) = 1 / 2} (π / 6) := by
  simp [cos_add] -- apply addition formula for cosine
  have h : cos (3 * π / 2) = 0 := by calc -- $\cos (3 \pi / 2) = 0$
    cos (3 * π / 2) = cos (π + π / 2) := by ring_nf
                                _ = 0 := by simp [cos_add]
  have h' : sin (3 * π / 2) = -1 := by calc -- $\sin (3 \pi / 2) = -1$
    sin (3 * π / 2) = sin (π + π / 2) := by ring_nf
                  _ = -1 := by simp [sin_add]
  constructor -- Show that π/6 is contained in the set and a lower bound
  · simp; repeat apply And.intro -- Contained
    · exact pi_pos
    · use (3 * π / 2); apply And.intro <;> simp [h, h'] -- Use x = π/6 and simplify
  · intro z ⟨zpos, x, hx, hxz⟩; simp [hx] at hxz -- Lower bound
    have : (sin x) ^ 2 = 1 := by calc -- sin x ^ 2 = 1, by trigonometric pythagoras
      sin x ^ 2 = 1 - cos x ^ 2 := by linarith [cos_sq_add_sin_sq x]
              _ = 1             := by simp [hx]
    simp at this; cases this <;> simp [*] at hxz -- do a case distinction whether sin x = 1 or -1
    · have hxz: sin z = - 2⁻¹ := by rw [←hxz]; simp
      by_contra hlt; simp at hlt
      have : 0 < - (2:ℝ) ⁻¹ := by calc -- If 0 < z < π/6, it follows that 0 = sin 0 < sin z = -1 / 2, a contradiction
        0 = sin 0 := by simp
        _ < sin z := by
          apply strictMonoOn_sin <;> try simp <;> try apply And.intro <;> try linarith;
          exact le_of_lt (half_pos pi_pos)
          exact zpos
        _ = -2⁻¹    := by rw [hxz]
      simp at this; linarith
    · by_contra hlt; simp at hlt
      have : (2 : ℝ)⁻¹ < 1 / 2    := by calc -- If 0 < z < π/6, it follows that 1/2 = sin z < sin π/6 = 1/2, a contradiction
        (2 : ℝ)⁻¹ = sin z         := by rw [hxz]
                  _ < sin (π / 6) := by
                    apply strictMonoOn_sin <;> try simp <;> try apply And.intro <;> try linarith
                    exact hlt
                  _ = 1 / 2       := by simp
      linarith
