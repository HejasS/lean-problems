import Mathlib
open Polynomial hiding C
open Real Filter Topology LaurentPolynomial

set_option maxHeartbeats 400000

section algebra_98595
noncomputable def Polynomial.eval₃ := Polynomial.eval₂ (@LaurentPolynomial.C ℝ _)
end algebra_98595

/- Find all polynomials $P$ with real coefficients such that
\[
  \frac{P(x)}{yz} + \frac{P(y)}{zx} + \frac{P(z)}{xy} = P(x-y) + P(y-z) + P(z-x)
\]
holds for all nonzero real numbers $x, y, z$ satisfying $2xyz=x+y+z$. -/
theorem algebra_98595 : { P : Polynomial ℝ |
    (∀ x y z : ℝ, x ≠ 0 → y ≠ 0 → z ≠ 0 → 2 * x * y * z = x + y + z →
    P.eval x / (y * z) + P.eval y / (z * x) + P.eval z / (x * y) =
    P.eval (x - y) + P.eval (y - z) + P.eval (z - x)) } = { P | ∃ c : ℝ, P = c • (X ^ 2 + 3) } := by
  ext P
  constructor
  -- Assume P satisfies the property; then it is of the given form
  · intro hP
    simp at hP
    -- We show first that P is even
    have h₀ (x : ℝ) : P.eval x = P.eval (-x) := by
      -- We may assume WLOG that $x$ is not zero
      -- since if $x=0$, then $P(0) = P(-0)$
      wlog hx: x ≠ 0
      · simp at hx; simp [hx]
      -- We may also assume WLOG that $x>0$, as otherwise
      -- we can replace $x$ by $-x$
      wlog hx₁: x > 0 generalizing x
      · have hx : x < 0 := by
          simp at hx₁
          match hx₁.eq_or_lt with
          | Or.inl hx₁ => contradiction
          | Or.inr hx₁ => exact hx₁
        apply Eq.symm
        nth_rw 2 [← neg_neg x]
        apply this <;> linarith
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
      --   P(x) * x + P(y) * y + P(z) * z = x * y * z * (P(x-y) + P(y-z) + P(z-x))
      -- \]
      -- from the assumption by multiplying with $xyz$
      have h₀₀ : (fun n => P.eval x * x + P.eval (y n) * (y n) + P.eval (z n) * (z n))=
            fun n => x * (y n) * (z n) * (P.eval (x - (y n)) + P.eval (y n - (z n)) + P.eval (z n - x)) := by
        apply _root_.funext; intro n
        have := hP x (y n) (z n) hx (hy n) (hz n) (by
          unfold y z
          have : (n : ℝ) + 2 ≠ 0 := by linarith
          have : (2 * n * x ^ 2 + 2 * x ^ 2 + n + 2) ≠ 0 := by nlinarith
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
    -- Now we set $y = 1 / x$ and $z = x + 1 / x$. One checks that these satisfy $2xyz = x + y + z$,
    -- from this and the evenness of $P$ we obtain the following equation:
    have h₁ (x) (hx: x ≠ 0) : (x + 1 / x) * (P.eval (x + 1 / x) - P.eval (x - 1 / x)) = 1 / x * P.eval x + x * P.eval (1 / x) := by
      let y := 1 / x
      have hy : y ≠ 0 := by unfold y; simp [hx]
      let z := x + 1 / x
      have hz : z ≠ 0 := by
        unfold z; field_simp
        nlinarith
      have : x * x + 1 ≠ 0 := by nlinarith
      have := hP x y z hx hy hz (by unfold y z; field_simp; ring)
      unfold y z at this
      -- (By multiplying the orgiginal equation by xyz = z$)
      linear_combination (norm := ring_nf) (x + 1/x) * this
      field_simp; rw [← h₀]; ring
    -- Since this equation holds for all nonzero $x$, it holds as an equation of Laurent Polynomials
    -- Indeed, for this we only need the equation to hold for infinitely many $x$, but this  well known fact
    -- is not in Mathlib yet.
    have h₂ : (T 1 + T (-1)) * (P.eval₃ (T 1 + T (-1))) - (T 1 + T (-1)) * (P.eval₃ (T 1 - T (-1))) = T (-1) * P.eval₃ (T 1) + T 1 * P.eval₃ (T (-1)) := by
      apply eq_of_sub_eq_zero
      obtain ⟨n, f, hf⟩  := exists_T_pow  ((T 1 + T (-1)) * (P.eval₃ (T 1 + T (-1))) - (T 1 + T (-1)) * (P.eval₃ (T 1 - T (-1))) - ( T (-1) * P.eval₃ (T 1) + T 1 * P.eval₃ (T (-1))))
      apply_fun (· * (T n))
      simp only [Int.reduceNeg, zero_mul]
      rw [← hf, toLaurent_eq_zero]
      apply eq_of_infinite_eval_eq
      simp
      suffices h₂₀ : Set.Ioo 0 1 ⊆ {x | f.eval (x : ℝ) = 0} by
        apply Set.Infinite.mono h₂₀
        simp [Set.Ioo_infinite]
      intro x hx
      rw [Set.mem_setOf_eq]
      sorry
      apply IsUnit.mul_left_injective
      apply isUnit_T
    -- Now we differentiate on the degree of $P$
    match hP₁ : P.natDegree with
    -- If $P$ is constant, then our equation yields that it is in fact zero, so $c = 0$ works.
    | 0 =>
      rw [← eq_C_coeff_zero_iff_natDegree_eq_zero] at hP₁
      have := hP 1 1 2 (by simp) (by simp) (by simp) (by linarith)
      rw [hP₁] at this
      simp at this
      simp [this] at hP₁
      use 0; rw [hP₁]; simp
    -- If it has degree $1$, then by evenness the leading coefficient must be zero,
    -- a contradiction
    | 1 =>
      have := h₀ 1
      rw [P.as_sum_range, hP₁] at this
      simp [show Finset.range 2 = {0, 1} by rfl] at this
      have : P.coeff 1 = 0 := by linarith
      suffices P.coeff 1 ≠ 0 by contradiction
      apply coeff_ne_zero_of_eq_degree
      rw [degree_eq_iff_natDegree_eq, hP₁]
      apply @ne_zero_of_natDegree_gt _ _ _ 0
      linarith
    -- So from now on we will write the degree as $n + 2$ for a natural number $n$
    | n + 2 =>
      change P.natDegree = n + 2 at hP₁
      -- We consider the coefficient of $T ^ (n + 1)$ in the equality h₂
      have h₃ : n + 1 = n + 1 := by linarith
      apply_fun ((T (-1) * P.eval₃ (T 1) + T 1 * P.eval₃ (T (-1))) : ℝ[T;T⁻¹]) at h₃
      nth_rw 1 [← h₂] at h₃
      -- We need to show a couple of theorems about Laurent Polynomials because they don't have a
      -- good API in Mathlib yet
      have h₃₁ (Q : ℕ → ℝ[T;T⁻¹]) (k : ℕ): (∑ i ∈ Finset.range (k), (Q i)) (n + 1) = (∑ i ∈ Finset.range (k), (Q i (n + 1))) := by
        apply Finset.sum_apply'
      have h₃₂ (Q R : ℝ[T;T⁻¹]) : (Q + R) (n + 1) = Q (n + 1) + R (n + 1) := rfl
      have h₃₃ (Q R : ℝ[T;T⁻¹]) : (Q - R) (n + 1) = Q (n + 1) - R (n + 1) := rfl
      have h₃₄ (r : ℝ) (R : ℝ[T;T⁻¹]) : (r • R) (n + 1) = r * (R (n + 1)) := rfl
      have h₃₅ (R : ℝ[T;T⁻¹]) (r : ℝ) : C r * R = r • R := by sorry
      have h₃₆ (r : ℕ) (R : ℝ[T;T⁻¹]) : ((↑r : ℝ[T;T⁻¹]) * R) (n + 1) = r * (R (n + 1)) := by
        induction' r with r ih
        · simp
        · push_cast
          rw [add_mul, add_mul, ← ih]
          simp; rfl
      have h₃₇ (R : ℝ[T;T⁻¹])  : (-R) (n + 1) = - (R (n + 1)) := rfl
      have h₃₇ (r : ℤ) (R : ℝ[T;T⁻¹]) : ((r : ℝ[T;T⁻¹]) * R) ((↑n + 1) ) = r * (R (n + 1)) := by
        wlog hr : r ≥ 0 generalizing r
        · have hr' : -r ≥ 0 := by linarith
          have := this (-r) hr'; simp [h₃₇] at this
          assumption
        · lift r to ℕ using hr
          norm_cast
          exact h₃₆ r R
      have h₃₈ (n : ℕ): (-1 : ℝ[T;T⁻¹]) ^ n = (↑((-1 : ℤ) ^ n) : ℝ[T;T⁻¹]) := by sorry
      have h₃₉ (n : ℕ) : (n : ℝ[T;T⁻¹]) = C (n : ℝ) := rfl
      -- To calculate this, we expand the polynomial using the binomial theorem and pull everything inside the sums
      push_cast at h₃
      rw [h₃₂, h₃₃] at h₃
      unfold eval₃ at h₃; simp [Finsupp.add_apply] at h₃
      simp only [eval₂_eq_sum_range, add_pow, sub_pow, Finset.mul_sum, Finset.sum_mul, hP₁, add_mul, T_pow] at h₃
      -- Then we move all $T^n$ terms to the right, as well as the application to (n + 1) inwards, until
      -- we can simplify with T n m = 1 if n = m else 0
      simp_rw [← mul_assoc, ← T_mul, ← mul_assoc, ← T_add, mul_assoc, T_mul,
        h₃₁, h₃₂, h₃₉, ← mul_assoc, mul_comm _ ((-1 : ℝ[T;T⁻¹]) ^ _), mul_assoc, h₃₅, h₃₈, h₃₇,
        h₃₄, T_apply] at h₃
      -- We need to rewrite using Finset.sum_attach so that we have access to the bounds of the variables inside the sums
      simp at h₃
      simp_rw [Finset.sum_add_distrib, ← Finset.sum_attach (Finset.range _)] at h₃
      -- The following two terms appear in the sum and should be simplified
      have h₃₁₀ (i : { x // x ∈ Finset.range (n + 2 + 1) }) (j : { x // x ∈ Finset.range (i + 1) }) :
          (- (↑((i : ℕ) - (j : ℕ)) : ℤ) + j = n) ↔ (↑i = n ∧ j = n) ∨ (↑i = n + 2 ∧ j = n + 1) := by
        have := Finset.mem_range.mp i.2; have := Finset.mem_range.mp j.2
        omega
      have h₃₁₁ (i : { x // x ∈ Finset.range (n + 2 + 1) }) (j : { x // x ∈ Finset.range (i + 1) }) :
          (-(↑((i : ℕ) - (j : ℕ)) : ℤ) + j + -1 = ↑n + 1) ↔ (i = n + 2 ∧ j = n + 2) := by
        have := Finset.mem_range.mp i.2; have := Finset.mem_range.mp j.2
        omega
      simp_rw [h₃₁₀, h₃₁₁] at h₃
      -- We want to split up the cases even more
      have h₃₈ (i j : ℕ) (r : ℝ) :
          (if i = n ∧ j = n then r else 0) + (if i = n + 2 ∧ j = n + 1 then r else 0) =
          if ((i = n ∧ j = n) ∨ (i = n + 2 ∧ j = n + 1)) then r else 0 := by
        split <;> simp [*]
      simp_rw [← h₃₈, Finset.sum_add_distrib] at h₃
      -- We want to rewrite the conditions on the two indices in order to make use
      -- of a lean simp lemma which can simplify terms of the type
      -- ∑ x ∈ s, if x = a then r else 0
      -- (it is r if a is in s, else 0)
      have h₃₁₂ (A B : Prop) [Decidable A] [Decidable B] (r : ℝ) :
          (if A ∧ B then r else 0) = if A then (if B then r else 0) else 0 := by
        by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]
      simp_rw [h₃₁₂] at h₃
      simp at h₃
      -- We also need to rewrite the following since the i on the lhs is casted, so the simp lemma doesn't apply
      have h₃₁₃ (k l : ℕ) (hk : k ≤ l) (i : { x // x ∈ Finset.range (l + 1) }) : i = k ↔ i = ⟨k, show k ∈ Finset.range (l + 1) by simp; linarith⟩ := by
        apply Iff.intro
        · intro h; simp [← h]
        · intro h; simp [h]
      -- These two are also for the simp lemma
      have h₃₁₄ (a b : ℕ) : -1 + (a : ℤ) = (b : ℤ) + 1 ↔ a = b + 2 := by omega
      have h₃₁₅ (a b : ℕ) : 1 + -(a : ℤ) = (b : ℤ) + 1 ↔ a = 0 ∧ b = 0 := by omega
      simp_rw [h₃₁₃ n (n + 2) (by linarith), h₃₁₃ (n + 2) (n + 2) (by linarith)] at h₃
      simp at h₃
      simp_rw [
        h₃₁₅, h₃₁₂, h₃₁₄,
        h₃₁₃ 0 (n + 2) (by linarith),
        h₃₁₃ n n (by linarith),
        h₃₁₃ (n + 2) (n + 2) (by linarith),
        h₃₁₃ (n + 1) (n + 2) (by linarith),
      ] at h₃

      -- After doing this, we can finally simplify down the expression and obtain the equation below
      simp_arith at h₃
      ring_nf at h₃
      rw [mul_comm n 2, pow_mul] at h₃
      simp at h₃
      have h₃ : (P.coeff (2 + n) * 3 + 2 * n * P.coeff (2 + n)) = if n = 0 then P.coeff 0 else 0 := by linarith
      -- To work with this we must again distinguish cases whether $n = 0$ or not
      cases hn : n with
      -- In the case $0$ the equation shows that $3 \cdot P_2 = P_0$
      | zero =>
        simp [hn, add_comm (P.coeff 2) _] at h₃
        -- We can choose $c = P_2$
        use (P.coeff 2)
        nth_rw 1 [P.as_sum_range, hP₁, hn]
        simp [show Finset.range 3 = {0, 1, 2} by rfl]
        rw [← smul_X_eq_monomial, ← smul_X_eq_monomial, ← h₃, Polynomial.C_mul, ← Polynomial.smul_eq_C_mul]
        show P.coeff 2 • 3 + (P.coeff 1 • X ^ 1 + P.coeff 2 • X ^ 2) = P.coeff 2 • X ^ 2 + P.coeff 2 • 3
        -- Thus it suffices to show that the linear coefficient $P_1$ is $0$
        suffices P.coeff 1 = 0 by rw [this]; simp; ring
        -- But this is easily seen from evenness, e.g. by plugging in $1$
        have := h₀ 1
        rw [P.as_sum_range, hP₁, hn] at this
        simp [show Finset.range 3 = {0, 1, 2} by rfl] at this
        linarith
      | succ n =>
      -- In the $n + 1$ case the equation becomes $P_{n + 3} \cdot (5 + 2n) = 0$, so one of the factors must be zero
        simp [hn] at h₃
        have h₃ : P.coeff (3 + n) * (5 + 2 * n) = 0 := by
          linear_combination (norm := ring_nf) h₃
        simp at h₃; match h₃ with
        | Or.inl hn =>
        -- The first case is impossible because the leading coefficient cannot be zero
          have : P.coeff (3 + n) ≠ 0 := by
            apply coeff_ne_zero_of_eq_degree
            rw [degree_eq_iff_natDegree_eq, hP₁]
            linarith
            apply ne_zero_of_natDegree_gt
            linarith
          contradiction
        -- The second case $5 + 2n = 0$ is impossible since $n$ is a natural number
        | Or.inr hn => linarith
  -- Now suppose that $P$ is of the form $P(x) = c * (x ^ 2 + 1)$
  · intro ⟨c, hP⟩ x y z _ _ _ hxyz
    rw [hP]
    -- Then the desired equation, after clearing denominators, is a multiple of hxyz
    field_simp
    linear_combination (-(1 * c * x ^ 3 * z * y) + c * x ^ 2 * z ^ 2 * y - 1 * c * x * z ^ 3 * y +
        c * x ^ 2 * z * y ^ 2 + c * x * z ^ 2 * y ^ 2 - 1 * c * x * z * y ^ 3 - 3 * c * x * z * y) * hxyz
