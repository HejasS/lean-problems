import Mathlib

/- A [sequence](https://artofproblemsolving.com/wiki/index.php/Sequence) is defined over [non-negative](https://artofproblemsolving.com/wiki/index.php/Non-negative) integral indexes in the following way: $a_{0}=a_{1}=3$, $a_{n+1}a_{n-1}=a_{n}^{2}+2007$.
Find the [greatest integer](https://artofproblemsolving.com/wiki/index.php/Floor_function) that does not exceed $\frac{a_{2006}^{2}+a_{2007}^{2}}{a_{2006}a_{2007}}.$ -/
theorem algebra_93397 {a : ℕ → ℝ} (ha01 : a 0 = 3 ∧ a 1 = 3)
    (han : ∀ n, n ≥ 1 → a (n + 1) * a (n - 1) = a n ^ 2 + 2007) :
    ⌊ ((a 2006) ^ 2 + (a 2007) ^ 2) / (a 2006 * a 2007) ⌋ = 224 := by
  -- We have the following equation by assumption:
  have h0 (n): n ≥ 2 → a (n - 1) * (a (n - 1) + a (n + 1)) = a n * (a n + a (n - 2)) := by
    intro hn
    calc
      a (n - 1) * (a (n - 1) + a (n + 1))
        = a (n - 1) ^ 2 + a (n - 1) * a (n + 1)  := by ring
      _ = (a (n - 1) ^ 2 + 2007) + (a (n + 1) * a (n - 1)) - 2007 := by ring
      _ = (a n * a (n - 2)) + (a n ^ 2 + 2007) - 2007 := by rw [han n, ← han (n - 1), show n - 1 + 1 = n by omega, show n - 1 - 1 = n - 2 by omega] <;> omega
      _ = a n * (a n + a (n - 2)) := by ring
  -- None of the a(n) are zero, as otherwise $0 = a(n + 1) ^ 2 + 2007$, which is impossible
  have h1 (n) : a n ≠ 0 := by
    by_contra! ha
    have := han (n + 1) (by omega)
    rw [show n + 1 - 1 = n by simp, ha] at this
    simp at this
    have : a (n + 1) ^ 2 + 2007 > 0 := by nlinarith
    linarith
  -- Let $b(n) = \frac{a(n)}{a(n - 1)}$
  let b := fun n => a n / a (n - 1)
  -- Then $b(n) + \frac{1}{b(n - 1)} = b(3) + \frac{1}{b(2)}$ is an invariant of the sequence, as
  -- is easily seen by calculation
  let rec h2 : (n : ℕ) → (n ≥ 3) → b n + 1 / (b (n - 1)) = b 3 + 1 / (b 2)
  | 0 => by intro; linarith
  | 1 => by intro; linarith
  | 2 => by intro; linarith
  | 3 => by intro; ring
  | n + 4 => by
    intro _
    rw [← h2 (n + 3) (by linarith)]
    unfold b
    field_simp [h1]
    have h0 := h0 (n + 3)  (by linarith)
    simp at h0
    linear_combination h0
  -- Also, $b(2007) + \frac{1}{b(2007)} = 225$ because this is the value of $b(3) + \frac{1}{b(2)}$
  have h3 : b 3 + 1 / b 2 = 225 := by
    unfold b; simp
    field_simp [h1]
    have han2 := han 2 (by linarith); simp at han2
    have han1 := han 1 (by linarith); simp at han1
    linear_combination
      han2 / 3 + (1 / 9 * a 2 - 1 / 3) * han1 + (-(1 / 9 * a 2 ^ 2) + 1 / 3 * a 2) * ha01.left +
        (1 / 9 * a 1 * a 2 - 1 / 3 * a 3 - 1 / 3 * a 1 + 1 / 3 * a 2) * ha01.right
  rw [h3] at h2
  -- The expression in the problem statement is equal to $b(2007) + \frac{1}{b(2007)}$
  have h4 : (a 2006 ^ 2 + a 2007 ^ 2) / (a 2006 * a 2007) = b 2007 + 1 / b 2007 := by
    unfold b
    field_simp [h1]
    ring
  rw [h4]
  -- We can solve the given equation for $a(n+2)$ to get $a(n+2) = (a(n+1)^2 + 2007) / a(n)$
  have han' (n) : a (n + 2) = (a (n + 1) ^ 2 + 2007) / a n := by
      field_simp [h1]
      have := han (n + 1) (by linarith); simp at this
      linear_combination this
  -- From this it follows that $a(n) > 0$ for all $n$
  let rec h5 : (n : ℕ) → a n > 0
  | 0 => by simp [*]
  | 1 => by simp [*]
  | n + 2 => by
    rw [han']
    field_simp; exact h5 n
  -- and also that $a(n) < a(n + 1)$ for all $n$
  let rec h6 : (n : ℕ) → (n ≥ 1) → a n < a (n + 1)
  | 0 => by simp [*]
  | 1 => by simp [*]; linarith
  | n + 2 => by
      intro hn
      have : a (n + 1) < a (n + 2) := h6 (n + 1) (by linarith)
      apply_fun (a (n + 2)* · * a (n + 1)) at this; simp at this
      calc
      a (n + 3) = (a (n + 2) ^ 2 + 2007) / a (n + 1)         := by exact han' (n + 1)
              _ > (a (n + 2) * a (n + 1) + 2007) / a (n + 1) := by simp; rw [div_lt_div_iff₀]; nlinarith; all_goals apply h5
              _ = a (n + 2) + 2007 / a (n + 1)               := by field_simp [h1]
              _ > a (n + 2)                                  := by field_simp; apply h5
      apply StrictMono.mul_const
      apply StrictMono.const_mul
      exact fun ⦃a b⦄ a ↦ a
      all_goals apply h5
  -- We also show that $b(n) < b(n + 1)$ for all $n ≥ 2$, which follows from the original equation.
  let rec h7 : (n : ℕ) → (n ≥ 2) → b n < b (n + 1)
  | 0 => by simp [*]
  | 1 => by simp [*]
  | 2 => by unfold b; simp [*]; linarith
  | n + 3 => by
    intro; unfold b; simp_arith; rw [lt_div_iff₀' (h5 (n + 3)), mul_div, div_lt_iff₀ (h5 (n + 2))]
    have han := han (n + 3) (by linarith); simp_arith at han
    rw [han]
    linarith
  -- Now, we have $b(2007) + \frac{1}{b(2007)} < b(2008) + \frac{1}{b(2007)} = 225$
  have h8 : b 2007 + 1 / b 2007 < 225 := by calc
    b 2007 + 1 / b 2007 < b 2008 + 1 / b 2007 := by linarith [h7 2007 (by linarith)]
                      _ = 225                 := by rw [h2]; linarith
  -- Also, all $b(n)$ are at least 1 since the first one is 1 and they are increasing
  let rec h9 : (n : ℕ) → b n ≥ 1
  | 0 => by unfold b; simp [*]
  | 1 => by unfold b; simp [*]
  | 2 => by unfold b; simp [*]; linarith
  | n + 3 => by linarith [h9 (n + 2), h7 (n + 2) (by linarith)]
  -- Therefore, $b(2007) + \frac{1}{b(2007)} \geq (b(2007) + \frac{1}{b(2007)}) - 1 = 224$
  have h10 : b 2007 + 1 / b 2007 ≥ 224 := by
    have h9' := h9 2006; simp at h9'
    have := @one_div_le _ _ (b 2006) 1 (by linarith) (by linarith); simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
    rw [← this] at h9'
    have : 1 / b 2007 ≥ 0 := by simp; linarith [h9 2007]
    calc
      b 2007 + 1 / b 2007
       = (b 2007 + 1 / b 2006) + (1 / b 2007 - 1 / b 2006) := by ring
      _ = 225 + (1 / b 2007 - 1 / b 2006)                  := by rw [h2 2007 (by linarith)]
      _ ≥ 225 - 1 / b 2006                                 := by linarith
      _ ≥ 225 - 1                                          := by linarith
      _ = 224                                              := by linarith
  rw [Int.floor_eq_iff]
  -- Thus, $\lfloor b(2007) + \frac{1}{b(2007)} \rfloor = 224$
  split_ands <;> norm_cast
