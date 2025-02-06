import Mathlib

/- If $1998$ is written as a product of two positive integers whose difference is as small as possible, then the difference is
(A) 8
(B) 15
(C) 17
(D) 47
(E) 93 -/
theorem number_theory_93914 : IsLeast {d | ∃ a, a * (a + d) = 1998} 17 := by
  constructor
  -- 17 works as a difference, since $37 \cdot (17 + 37) = 1998$
  · use 37
  -- For any difference $d < 17$ that works, we have
  · intro d ⟨a, ha₁⟩
    by_contra ha₂; simp at ha₂
    -- $a \le 45$, since otherwise $a \cdot (a + d)$ would be bigger than $1998$
    have ha₃ : a ≤ 45 := by nlinarith
    -- $a > 37$, since otherwise $a \cdot (a + d)$ would be less than $1998$
    have ha₄ : 37 < a := by nlinarith
    -- and $a$ divides $1998$. Now we see that no $a$ between $38$ and $45$ divide $1998$, a contradiction.
    have ha₅ : a ∣ 1998 := by simp [← ha₁]
    interval_cases a <;> norm_num at ha₅
