import Mathlib
open Real Polynomial Filter Topology LaurentPolynomial

noncomputable def Polynomial.eval₃ := Polynomial.eval₂ (@LaurentPolynomial.C ℝ _)

/- Find all polynomials $P$ with real coefficients such that
\[
\frac{P(x)}{yz} + \frac{P(y)}{zx} + \frac{P(z)}{xy} = xyz(P(x-y) + P(y-z) + P(z-x))
\]
holds for all nonzero real numbers $x, y, z$ satisfying $2xyz=x+y+z$. -/
theorem algebra_98595 :
    { P : Polynomial ℝ |
    (∀ x y z : ℝ, x ≠ 0 → y ≠ 0 → z ≠ 0 → 2 * x * y * z = x + y + z →
    P.eval x / (y * z) + P.eval y / (z * x) + P.eval z / (x * y) =
    P.eval (x - y) + P.eval (y - z) + P.eval (z - x)) }
    = { P | ∃ c, P = c * (X ^ 2 + 3) } := by
  apply Set.ext
  intro P
  constructor
  -- Assume P satisfies the property; then it is of the given form
  · intro hP; simp at hP
    -- We show firt that P is even
    have h₀ (x): P.eval x =  P.eval (-x) := by
      -- We may assume WLOG that $x$ is not zero
      -- since if $x=0$, then $P(0) = P(-0)$
      wlog hx: x ≠ 0
      · simp at hx; simp [hx]
      -- We may also assume WLOG that $x>0$, as otherwise
      -- we can replace $x$ by $-x$
      wlog hx₁: x > 0
      · have hx : x < 0 := by
          simp at hx₁
          match hx₁.eq_or_lt with
          | Or.inl hx₁ => contradiction
          | Or.inr hx₁ => exact hx₁
        apply Eq.symm
        nth_rw 2 [← neg_neg x]
        apply this
        · assumption
        · linarith
        · linarith
      -- Now we define sequences $y_n$ and $z_n$ such that
      -- $2xyz = x + y + z$ for every $n$ and such that $z(n)$ converges to $0$
      -- and such that $y$ and $z$ are never $0$
      let y := fun n : ℕ => x * (-1 + 1 / (n + 2))
      have hy (n): y n ≠ 0 := by unfold y; simp [hx]; field_simp; linarith
      have hy₁ : Tendsto y atTop (𝓝 (-x)) := by
        unfold y
        suffices Tendsto (fun n : ℕ ↦ x * (-1 + 1 / (n + 2))) atTop (𝓝 (x * (-1 + 0))) by simp at this; simpa
        apply Tendsto.const_mul
        apply Tendsto.add
        apply tendsto_const_nhds
        norm_cast
        rw [@tendsto_add_atTop_iff_nat _ ( fun n => (1:ℝ) / (n)) _ 2]
        exact tendsto_one_div_atTop_nhds_zero_nat
      let z := fun n : ℕ => -x / (2 * n * x^2 + 2 * x^2 + n + 2)
      have hz (n): z n ≠ 0 := by unfold z; simp [hx]; nlinarith
      have hz₁ : Tendsto z atTop (𝓝 0) := by
        unfold z
        have : (fun n : ℕ ↦ -x / (2 * n * x ^ 2 + 2 * x ^ 2 + n + 2)) = fun n : ℕ ↦ - (x / (2 * n * x ^ 2 + 2 * x ^ 2 + n + 2)) := by
          apply _root_.funext
          intro n; rw [neg_div']
        rw [this, ← neg_zero]
        apply Tendsto.neg
        have : (fun n : ℕ => x / (2 * n * x ^ 2 + 2 * x ^ 2 + n + 2)) = (fun n : ℕ => ((2 * n * x ^ 2 + 2 * x ^ 2 + n + 2) / x))⁻¹ := by
          apply _root_.funext
          intro n; simp
        rw [this]
        apply Tendsto.inv_tendsto_atTop
        apply Tendsto.atTop_div_const
        · assumption
        · apply tendsto_atTop_add_const_right
          apply tendsto_atTop_add
          · apply tendsto_atTop_add_const_right
            apply Tendsto.atTop_mul_const
            · nlinarith
            · apply Tendsto.const_mul_atTop
              · simp
              · exact tendsto_natCast_atTop_atTop
          · exact tendsto_natCast_atTop_atTop
      -- By showing that the $y$ and $z$ we chose indeed satisfy this equation, we can
      -- conclude that we always have
      -- \[
      -- P(x) * x + P(y) * y + P(z) * z = x * y * z * (P(x-y) + P(y-z) + P(z-x))
      -- \]
      -- from the assumption by multiplying with $xyz$
      have h₀₀ : (fun n => P.eval x * x + P.eval (y n) * (y n) + P.eval (z n) * (z n))=
            fun n => x * (y n) * (z n) * (P.eval (x - (y n)) + P.eval (y n - (z n)) + P.eval (z n - x)) := by
        apply _root_.funext; intro n
        have := hP x (y n) (z n) hx (hy n) (hz n) (by
          unfold y z
          have : (n : ℝ) + 2 ≠ 0 := by linarith
          have : (2 * n * x^2 + 2 * x^2 + n + 2) ≠ 0 := by nlinarith
          field_simp
          ring)
        linear_combination (norm := field_simp [hx, hy n, hz n]) x * (y n) * (z n) * this
        ring
      -- The LHS converges to $P(x) * x + P(-x) * (-x) + P(0) * 0 = x * (P(x) - P(-x))$ by continuity of the polynomial $P$
      have h₀₁ : Tendsto (fun n => P.eval x * x + P.eval (y n) * (y n) + P.eval (z n) * (z n)) atTop (𝓝 (P.eval x * x + P.eval (-x) * (-x) + 0)) := by
        apply Tendsto.add; apply Tendsto.add
        · apply tendsto_const_nhds
        · apply Tendsto.mul
          apply P.continuous.seqContinuous
          all_goals
            exact hy₁
        · suffices Tendsto (fun x ↦ P.eval (z x) * z x) atTop (𝓝 (P.eval 0 * 0)) by simp at this; assumption
          apply Tendsto.mul
          apply P.continuous.seqContinuous
          all_goals
            exact hz₁
      -- The RHS converges to $0$, as $z$ does and the other terms converge to finite values
      have h₀₂ : Tendsto (fun n => x * y n * z n * (P.eval (x - y n) + P.eval (y n - z n) + P.eval (z n - x))) atTop (𝓝 (x * (-x) * 0 * (P.eval (x - (-x)) + P.eval ((-x) - 0) + P.eval (0 - x)))) := by
        repeat apply Tendsto.mul
        · simp
        · exact hy₁
        · exact hz₁
        · apply Tendsto.add
          apply Tendsto.add
          all_goals
            apply P.continuous.seqContinuous
            apply Tendsto.sub
            <;> simp [hy₁, hz₁]
      simp at h₀₁ h₀₂
      -- Thus, $x * (P(x) - P(-x)) = 0$
      rw [h₀₀] at h₀₁
      have h₀₃ := tendsto_nhds_unique h₀₁ h₀₂
      have h₀₃ : x * (P.eval x - P.eval (-x)) = 0 := by linarith
      -- Since $x\neq 0$, it follows that $P(x) = P(-x)$ as claimed.
      simp [hx] at h₀₃
      linarith
    have h₁ (x) (hx: x ≠ 0) : (x + 1 / x) * (P.eval (x + 1 / x) - P.eval (x - 1/x)) = 1 / x * P.eval x + x * P.eval (1 / x) := by
      let y := 1 / x
      have hy : y ≠ 0 := by unfold y; simp [hx]
      let z := x + 1 / x
      have hz : z ≠ 0 := by
        unfold z; field_simp
        nlinarith
      have : x * x + 1 ≠ 0 := by nlinarith
      have := hP x y z hx hy hz (by unfold y z; field_simp; ring)
      unfold y z at this
      linear_combination (norm := ring_nf) (x + 1/x) * this
      field_simp; rw [← h₀]; ring
    have h₂ : (T 1 + T (-1)) * (P.eval₃ (T 1 + T (-1)) - P.eval₃ (T 1 - T (-1))) = T (-1) * P.eval₃ (T 1) + T 1 * P.eval₃ (T (-1)) := by sorry
    match hP₁ : P.natDegree with
    | 0 => sorry
    | 1 => sorry
    | n + 2 =>
      have h₃ : n = n := rfl
      apply_fun ((T (-1) * P.eval₃ (T 1) + T 1 * P.eval₃ (T (-1))) : ℝ[T;T⁻¹]) at h₃
      nth_rw 1 [← h₂] at h₃
      unfold eval₃ at h₃; simp [Finsupp.add_apply] at h₃
      have (P Q : ℝ[T;T⁻¹]): (P + Q : ℝ[T;T⁻¹]) 1 = P 1 + Q 1 := by rfl

      unfold eval₃ at h₂
      #check _root_.funext
      simp only [eval₂_eq_sum_range, add_pow, sub_pow, Finset.mul_sum, ← Finset.sum_sub_distrib] at h₂
      have (x i) : (T 1 + T (-1)) *
        (LaurentPolynomial.C (P.coeff x) * (T 1 ^ i * T (-1) ^ (x - i) * ((x.choose i) : ℝ[T;T⁻¹] )) -
          LaurentPolynomial.C (P.coeff x) * ((-1) ^ (i + x) * T 1 ^ i * T (-1) ^ (x - i) * ((x.choose i) : ℝ[T;T⁻¹]))) = 0 := by
        simp?
      /- let x := fun n : ℕ => n + (1 : ℝ)
      have h₂ : Tendsto (fun n => (((x n) + 1 / (x n)) * (P.eval ((x n) + 1 / (x n)) - P.eval ((x n) - 1 / (x n)))) / ((x n) ^ (n+1))) atTop (𝓝 (2 * n + 4)):= by
        change P.natDegree = n + 2 at hP₁
        simp only [eval_eq_sum_range, Finset.mul_sum, hP₁]
        simp [Finset.sum_range_add, Finset.sum_range_add, show Finset.range 2 = {0, 1} by rfl]
        simp [-Finset.sum_sub_distrib, pow_add, add_mul x x⁻¹, sub_mul x x⁻¹, mul_comm x⁻¹] at h₁
        simp only [mul_comm x, mul_assoc] at h₁ -/

#check eval_eq_sum_range
