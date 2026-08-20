import CycleCommonality.Majorization.Karamata

/-!
# Inserting one value into a nonincreasing sequence

Lemma `lem:rank-one-majorization` of `adjacent_cycle_commonality.tex` applies Karamata to the
vector `v = (α₀, …, α_{N-2}, α_{N-1} + 1)`, which is **not** sorted — see point (2) of the audit.
The paper handles this with the "sum of the `j` largest = max over `j`-element subsets"
characterization.

Formalizing that characterization needs a chunk of sorting theory.  It is avoided here: since `v`
is `α` (truncated) with a single extra value `w` inserted, its nonincreasing rearrangement can be
written down *explicitly* as `bump α w p`, where `p` is the insertion position.  Both cases of the
paper's subset argument then appear directly as the two branches of `sum_bump`.

Main results:

* `bump` — `α` with `w` spliced in at position `p`;
* `sum_bump` — the prefix sums of `bump α w p` under any `F : ℝ → ℝ`, in closed form;
* `bump_antitone` — `bump α w p` is nonincreasing when `w` sits between `α (p-1)` and `α p`;
* `insertPos` — the correct insertion position, and its two defining properties.
-/

namespace CycleCommonality

open Finset

/-- `α` with the value `w` inserted at position `p`: the entries before `p` are those of `α`,
position `p` carries `w`, and the entries after `p` are those of `α` shifted by one. -/
noncomputable def bump (α : ℕ → ℝ) (w : ℝ) (p : ℕ) : ℕ → ℝ :=
  fun i => if i < p then α i else if i = p then w else α (i - 1)

@[simp] lemma bump_of_lt {α : ℕ → ℝ} {w : ℝ} {p i : ℕ} (h : i < p) :
    bump α w p i = α i := by simp [bump, h]

@[simp] lemma bump_self {α : ℕ → ℝ} {w : ℝ} {p : ℕ} : bump α w p p = w := by simp [bump]

lemma bump_of_gt {α : ℕ → ℝ} {w : ℝ} {p i : ℕ} (h : p < i) :
    bump α w p i = α (i - 1) := by
  have h1 : ¬ i < p := by omega
  have h2 : i ≠ p := by omega
  simp [bump, h1, h2]

/-- Closed form for the prefix sums of `bump α w p` under an arbitrary `F`.

The two branches are exactly the two cases of the paper's subset argument: either the `j` largest
entries avoid the bumped one (`j ≤ p`), or they include it (`p < j`). -/
theorem sum_bump (F : ℝ → ℝ) (α : ℕ → ℝ) (w : ℝ) (p : ℕ) : ∀ j : ℕ,
    ∑ i ∈ range j, F (bump α w p i)
      = (∑ i ∈ range (if j ≤ p then j else j - 1), F (α i)) + (if p < j then F w else 0) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      rcases lt_trichotomy j p with h | h | h
      · -- still strictly before the insertion point
        have h1 : j ≤ p := h.le
        have h2 : j + 1 ≤ p := h
        have h3 : ¬ p < j := by omega
        have h4 : ¬ p < j + 1 := by omega
        simp only [h1, h2, h3, h4, if_true, if_false, bump_of_lt h]
        rw [Finset.sum_range_succ]
        ring
      · -- landing exactly on the insertion point (after `subst`, the position is called `j`)
        subst h
        have h3 : ¬ j < j := lt_irrefl j
        have h4 : j < j + 1 := Nat.lt_succ_self j
        have h5 : ¬ (j + 1 ≤ j) := by omega
        simp only [le_refl, h3, h4, h5, if_true, if_false, bump_self,
          Nat.add_sub_cancel]
        ring
      · -- past the insertion point
        have h1 : ¬ j ≤ p := by omega
        have h2 : ¬ j + 1 ≤ p := by omega
        have h3 : p < j := h
        have h4 : p < j + 1 := by omega
        have h5 : j + 1 - 1 = j := by omega
        simp only [h1, h2, h3, h4, if_true, if_false, bump_of_gt h, h5]
        rw [show j = (j - 1) + 1 by omega, Finset.sum_range_succ]
        simp only [Nat.add_sub_cancel]
        ring

/-- `bump α w p` is nonincreasing on `range (M+1)` as soon as `w` sits below every `α i` with
`i < p` and above every `α i` with `p ≤ i < M`. -/
theorem bump_antitone {α : ℕ → ℝ} {w : ℝ} {p M : ℕ} (hpM : p ≤ M)
    (hα : ∀ i, i + 1 < M → α (i + 1) ≤ α i)
    (hup : ∀ i, i < p → w ≤ α i)
    (hdown : ∀ i, p ≤ i → i < M → α i ≤ w) :
    ∀ i, i + 1 < M + 1 → bump α w p (i + 1) ≤ bump α w p i := by
  intro i hi
  have hiM : i < M := by omega
  rcases lt_trichotomy (i + 1) p with h | h | h
  · rw [bump_of_lt h, bump_of_lt (by omega : i < p)]
    exact hα i (by omega)
  · rw [h, bump_self, bump_of_lt (by omega : i < p)]
    exact hup i (by omega)
  · -- `p < i + 1`, i.e. `p ≤ i`
    have hpi : p ≤ i := Nat.lt_succ_iff.mp h
    rcases eq_or_lt_of_le hpi with h2 | h2
    · -- `p = i`
      subst h2
      rw [bump_of_gt (by omega : p < p + 1), bump_self]
      simp only [Nat.add_sub_cancel]
      exact hdown p le_rfl hiM
    · -- `p < i`
      rw [bump_of_gt (by omega : p < i + 1), bump_of_gt h2]
      simp only [Nat.add_sub_cancel]
      have h3 := hα (i - 1) (by omega)
      rwa [show (i - 1) + 1 = i by omega] at h3

/-- The insertion position for `w` into the nonincreasing sequence `α` of length `M`:
the least index that is either past the end or carries a value below `w`. -/
noncomputable def insertPos (α : ℕ → ℝ) (w : ℝ) (M : ℕ) : ℕ :=
  Nat.find (p := fun i => i = M ∨ (i < M ∧ α i < w)) ⟨M, Or.inl rfl⟩

lemma insertPos_le (α : ℕ → ℝ) (w : ℝ) (M : ℕ) : insertPos α w M ≤ M := by
  classical
  have h := Nat.find_spec (p := fun i => i = M ∨ (i < M ∧ α i < w)) ⟨M, Or.inl rfl⟩
  rcases h with h | h
  · exact h.le
  · exact h.1.le

lemma le_of_lt_insertPos {α : ℕ → ℝ} {w : ℝ} {M : ℕ} :
    ∀ i, i < insertPos α w M → w ≤ α i := by
  classical
  intro i hi
  have hM : insertPos α w M ≤ M := insertPos_le α w M
  have hnot := Nat.find_min (p := fun i => i = M ∨ (i < M ∧ α i < w)) ⟨M, Or.inl rfl⟩ hi
  by_contra hcon
  exact hnot (Or.inr ⟨by omega, not_le.mp hcon⟩)

/-- A nonincreasing sequence really is nonincreasing between any two indices. -/
lemma le_of_antitone_step {α : ℕ → ℝ} {M : ℕ} (hα : ∀ i, i + 1 < M → α (i + 1) ≤ α i) :
    ∀ p k, p ≤ k → k < M → α k ≤ α p := by
  intro p k
  induction k with
  | zero => intro hk _; have : p = 0 := by omega
            simp [this]
  | succ k ih =>
      intro hk hkM
      rcases Nat.eq_or_lt_of_le hk with heq | hlt
      · rw [← heq]
      · exact le_trans (hα k (by omega)) (ih (by omega) (by omega))

lemma le_of_insertPos_le {α : ℕ → ℝ} {w : ℝ} {M : ℕ}
    (hα : ∀ i, i + 1 < M → α (i + 1) ≤ α i) :
    ∀ i, insertPos α w M ≤ i → i < M → α i ≤ w := by
  classical
  intro i hpi hiM
  have hspec : insertPos α w M = M ∨
      (insertPos α w M < M ∧ α (insertPos α w M) < w) :=
    Nat.find_spec (p := fun i => i = M ∨ (i < M ∧ α i < w)) ⟨M, Or.inl rfl⟩
  rcases hspec with h | h
  · omega
  · exact le_trans (le_of_antitone_step hα _ i hpi hiM) h.2.le

end CycleCommonality
