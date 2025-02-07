import Mathlib

open List

theorem sum_le_of_nodup_sorted: ∀ (l: List ℕ) (h: l ≠ []) (h': l.Nodup) (_: l.Sorted fun x x' => x ≥ x') (n: ℕ) (_: l.head h ≤ n),
    2 * l.sum + (l.length) * (l.length) ≤ (2 * n + 1) * l.length
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

theorem sum_le_of_nodup: ∀ (l: List ℕ) (h: l ≠ []) (h': l.Nodup) (n: ℕ) (h'': ∀ x ∈ l, x ≤ n),
    2 * l.sum + (l.length) * (l.length) ≤ (2 * n + 1) * l.length := by
  intros l h h' n h''
  let l' := l.mergeSort (fun x x' => x ≥ x')
  have hperm: l' ~ l := by exact perm_mergeSort _ l
  have hl₁ := Perm.length_eq hperm
  have hl₂ := Perm.sum_eq hperm
  rw [←hl₁, ←hl₂]
  apply sum_le_of_nodup_sorted
  · rwa [Perm.nodup_iff hperm]
  · unfold_let l'; apply sorted_mergeSort
  · apply h''; rw [←(Perm.mem_iff hperm)]; apply head_mem; by_contra hc; simp [hc] at hperm; contradiction

theorem last_ge_len_of_sorted: ∀ (l: List ℕ) (h: l ≠ []) (_: l.Sorted fun x x' => x < x'),
    l.head h + l.length ≤ l.getLast h + 1
  | [] => by simp
  | [a] => by simp;
  | a :: b :: l => by
    intro _ hsort; rw [sorted_cons] at hsort;
    obtain ⟨hab, hsort⟩ := hsort; simp at hab; obtain ⟨hab, _⟩ := hab
    have ih: ((b::l).head (cons_ne_nil b l)) + (b::l).length ≤ ((b::l).getLast (cons_ne_nil b l)) + 1 :=
      last_ge_len_of_sorted (b::l) (cons_ne_nil b l) hsort
    have : (b :: l).head! ≤ (b :: l).getLast (cons_ne_nil b l) :=
      Sorted.head!_le hsort (getLast_mem _)
    simp at this ih
    simp; omega

theorem strict_sorted_of_sorted_nodup: ∀ (l: List ℕ) (h: l.Sorted fun x x' => x ≤ x') (h': l.Nodup),
    l.Sorted fun x x' => x < x'
  | []     => by simp
  | a :: l => by
    intro h h'
    simp at *; apply And.intro;
    · intro b hb; match (h.1 b hb).lt_or_eq with
      | Or.inr hab => exfalso; rw [hab] at h'; exact (h'.1 hb)
      | Or.inl _ => assumption
    · exact strict_sorted_of_sorted_nodup l h.2 h'.2

theorem nodup_sum: ∀ (l: List ℕ) (h: l ≠ []) (h': l.Nodup) (_: l.Sorted fun x x' => x ≤ x') (n: ℕ) (_: n ≤ l.head h),
    l.length * (l.length + 2 * n - 1)  ≤ 2 * l.sum
  | [] => by simp
  | a :: l => by
    simp
    intros ha h' ha' hsort n hna
    match l with
    | [] => simp; assumption
    | b :: l =>
      simp at ha ha';
      have : (n + 1) ≤ (b :: l).head (cons_ne_nil _ _):= by simp; omega
      have h := nodup_sum (b :: l) (cons_ne_nil _ _) h' hsort (n + 1) this
      generalize (b :: l).length = m at *; simp [mul_add] at h; simp [mul_add, add_mul]
      omega
