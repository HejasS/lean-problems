import Mathlib
open List Finset Nat

/- The sum of four two-digit numbers is $221$. None of the eight digits is $0$ and no two of them are the same. Which of the following is not included among the eight digits?
(A) 1 (B) 2 (C) 3 (D) 4 (E) 5 -/

def one_to_nine : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9} -- Set of allowed digits
lemma le_nine : ∀ x ∈ one_to_nine, x ≤ 9 := by decide -- They are all at most 9
lemma ge_one : ∀ x ∈ one_to_nine, 1 ≤ x := by decide -- and at least 1

theorem number_theory_97382
    (a b c d e f g h: ℕ)
    (h_digit: {a, b, c, d, e, f, g, h} ⊆ one_to_nine)
    (h_sum: (10 * a + e) + (10 * b + f) + (10 * c + g) + (10 * d + h) = 221)
    (h_diff: [a, b, c, d, e, f, g, h].Nodup): 4 ∉ ({a, b, c, d, e, f, g, h}: Finset ℕ):= by
  -- Define complement set of the given digits. It should contain exactly one digit, m
  let M := one_to_nine \ {a, b, c, d, e, f, g, h}
  have : M.card = 1 := by
    unfold M; rw [card_sdiff]
    unfold one_to_nine; simp
    suffices 9 - ([a, b, c, d, e, f, g, h].toFinset).card = 1 by simp at this; assumption
    rw [toFinset_card_of_nodup]; simp; all_goals assumption
  rw [card_eq_one] at this; obtain ⟨m, hm⟩ := this;

  -- m is contained in {1, 2, ..., 9}
  have m_mem: {m} ⊆ one_to_nine := by calc
    {m} ⊆ M := by simp [hm]
    _ ⊆ one_to_nine := by unfold M; simp
  simp at m_mem

  -- and we even have {a, b, c, d, e, f, g, h} ∪ {m} = {1, 2, ..., 9} where
  -- the union is disjoint
  have h_union: {a, b, c, d, e, f, g, h} ∪ {m} = one_to_nine := by
    rw [←hm]; unfold M; rw [union_comm, sdiff_union_self_eq_union, union_eq_left];
    exact h_digit
  have h_disjoint : Disjoint ({a, b, c, d, e, f, g, h}: Finset ℕ) M := by
    rw [_root_.disjoint_comm]
    exact sdiff_disjoint

  -- Thus, a + b + c + d + e + f + h + m = 1 + 2 + ... + 9 = 45
  have h_sum': ∑ x ∈ {a, b, c, d, e, f, g, h}, x + ∑ x ∈ M, x = 45 := by
    rw [←sum_disjUnion]
    have : one_to_nine = disjUnion {a, b, c, d, e, f, g, h} M h_disjoint := by
      rw [disjUnion_eq_union, hm, h_union]
    rw [←this]; simp [one_to_nine]

  -- We have e + f + g + h % 10 = 221 % 10 = 1
  have : (e + f + g + h) % 10 = 1 := by calc
    (e + f + g + h) % 10
      = (10 * (a + b + c + d) + (e + f + g + h)) % 10                      := by rw [Nat.mul_add_mod]
      _ = ((10 * a + e) + (10 * b + f) + (10 * c + g) + (10 * d + h)) % 10 := by omega
      _ = 1                                                                := by simp [h_sum]

  -- All of e, f, g, h are different and at most 9, thus their sum is at most 9 + 8 + 7 + 6
  -- according to the following lemmas:

  -- 1: For  a nonempty list without duplicates, which is sorted decreasingly
  -- and where the first element is at most n, we have
  -- \[ l.sum \le l.length * n - l.length * (l.length - 1) / 2 \]
  let rec sum_le_of_nodup_sorted: ∀ (l: List ℕ) (h: l ≠ []) (h': l.Nodup) (_: l.Sorted fun x x' => x ≥ x') (n: ℕ) (_: l.head h ≤ n),
    2 * l.sum + (l.length) * (l.length) ≤ (2 * n + 1) * l.length
  -- We show this by induction on the length of the list
  -- When we decompose our list as a :: l, then we
  -- know that the first element of l is at most n - 1
  -- and we can then apply the induction hypothesis to l
  | [] => by simp
  | a :: l => by
    simp
    intros ha h' ha' hsort n hna
    match l with
    | [] => simp; assumption
    | b :: l =>
      simp at ha ha';
      have : (b :: l).head (cons_ne_nil _ _) ≤ (n - 1) := by simp; omega
      have h := sum_le_of_nodup_sorted (b :: l) (cons_ne_nil _ _) h' hsort (n - 1) this
      match n with
      | n + 1 =>
        simp [Nat.add_mul, Nat.mul_add, ←Nat.add_assoc]
        simp [Nat.add_mul, Nat.mul_add, ←Nat.add_assoc] at h
        omega
      | 0 => omega;

  -- 2: We can have the same conclusion if the list is not sorted, but instead
  -- every element is at most n
  let rec sum_le_of_nodup: ∀ (l: List ℕ) (h: l ≠ []) (h': l.Nodup) (n: ℕ) (h'': ∀ x ∈ l, x ≤ n),
      2 * l.sum + (l.length) * (l.length) ≤ (2 * n + 1) * l.length := by
    intros l h h' n h''
    -- The idea is to first sort the list and then apply
    -- the first lemma to the sorted list
    let l' := l.mergeSort (fun x x' => x ≥ x')
    have hperm: l' ~ l := by exact List.mergeSort_perm l _
    have hl₁ := Perm.length_eq hperm
    have hl₂ := Perm.sum_eq hperm
    rw [←hl₁, ←hl₂]
    apply sum_le_of_nodup_sorted
    · rwa [Perm.nodup_iff hperm]
    · unfold l'; unfold Sorted;
      have h_Sorted := @sorted_mergeSort _ (fun x x' => decide (x ≥ x')) (by simp; omega) (by simp; omega) l
      simp at h_Sorted; assumption
    · apply h''; rw [←(Perm.mem_iff hperm)]; apply head_mem; by_contra hc; simp [hc] at hperm; contradiction

  have : e + f + g + h ≤ 30 := by
    have : [e, f, g, h].Nodup := by
      apply @Nodup.of_append_right _ [a, b, c, d] [e, f, g, h]
      show [a, b, c, d, e, f, g, h].Nodup; assumption
    have hle := sum_le_of_nodup [e, f, g, h] (by simp) this 9 (
      by intros x hx; apply le_nine; apply h_digit; simp at hx; simp [hx]
    )
    simp at hle; linarith
  -- All of e, f, g, h are at least one, thus their sum is at least 4
  have : [e, f, g, h].length ≤ [e, f, g, h].sum := by
    apply length_le_sum_of_one_le
    intros x hx; apply ge_one; apply h_digit; simp at hx; simp [hx]
  simp at this

  -- Now 4 ≤ e + f + g + h ≤ 30 and the sum is 1 mod 10, thus
  -- it is either 11 or 21
  have : e + f + g + h = 11 ∨ e + f + g + h = 21 := by omega

  -- Do a case distinction
  -- In both cases we can calculate a + b + c + d, since
  -- 10 * (a + b + c + d) + (e + f + g + h) = 221.
  -- Then, we may also calculate m, since a + b + c + d + e + f + g + h + m = 45
  cases this with
  | inl sum =>
      have : a + b + c + d = 21 := by omega -- a + b + c + d = (221-11)/10
      have : ∑ x ∈ {a, b, c, d, e, f, g, h}, x = 32 := by
        have : {a, b, c, d, e, f, g, h} = [a, b, c, d, e, f, g, h].toFinset := by simp
        rw [this]
        rw [sum_toFinset]; simp; omega; assumption
      -- In the first case, we get m = 13 which is a contradiction
      simp [*] at h_sum'; have : m = 13 := by linarith;
      exfalso; simp [this, one_to_nine] at m_mem
  | inr sum =>
      have : a + b + c + d = 20 := by omega -- a + b + c + d = (221-21)/10
      have : ∑ x ∈ {a, b, c, d, e, f, g, h}, x = 41 := by
        have : {a, b, c, d, e, f, g, h} = [a, b, c, d, e, f, g, h].toFinset := by simp
        rw [this]
        rw [sum_toFinset]; simp; omega; assumption
      -- In the second case we get m = 4, thus the answer is 4
      simp [*] at h_sum'; have : m = 4 := by linarith;
      rw [hm, this, Finset.disjoint_singleton_right] at h_disjoint; exact h_disjoint
