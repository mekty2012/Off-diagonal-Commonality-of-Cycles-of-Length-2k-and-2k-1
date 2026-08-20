import CycleCommonality.Majorization.Bump

/-!
# The rank-one lower majorization, in sequence form

This is Lemma `lem:rank-one-majorization` of `adjacent_cycle_commonality.tex` combined with
Karamata, stated purely about two real sequences.  No linear algebra appears yet: the spectral
hypotheses (interlacing, trace shift) are taken as inputs, and `Spectral/Interlace.lean` supplies
them.

Given `α` nonincreasing (the eigenvalues of `A`) and `μ` nonincreasing (the eigenvalues of
`A + P` for a rank-one orthogonal projection `P`) with

* `α i ≤ μ i`               (positive rank-one perturbation raises eigenvalues),
* `μ (i+1) ≤ α i`           (rank-one interlacing),
* `∑ μ = ∑ α + 1`           (the trace shifts by `Tr P = 1`),

the conclusion is `∑_{i<N-1} α i ^ n + (α (N-1) + 1) ^ n ≤ ∑_{i<N} μ i ^ n` for even `n`,
which is `eq:rank-one-majorization` followed by `eq:karamata`.
-/

namespace CycleCommonality

open Finset

/-- **Rank-one lower majorization**, combined with Karamata for `x ↦ x ^ n`, `n` even.

The vector `(α₀, …, α_{N-2}, α_{N-1} + 1)` is dominated in `n`-th powers by `μ`. -/
theorem rank_one_majorization_pow {N n : ℕ} (hn : Even n) (hn0 : n ≠ 0) (hN : 0 < N)
    (α μ : ℕ → ℝ)
    (hα : ∀ i, i + 1 < N → α (i + 1) ≤ α i)
    (hint1 : ∀ i, i < N → α i ≤ μ i)
    (hint2 : ∀ i, i + 1 < N → μ (i + 1) ≤ α i)
    (htr : ∑ i ∈ range N, μ i = (∑ i ∈ range N, α i) + 1) :
    (∑ i ∈ range (N - 1), α i ^ n) + (α (N - 1) + 1) ^ n ≤ ∑ i ∈ range N, μ i ^ n := by
  classical
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  simp only [Nat.add_sub_cancel] at *
  set w : ℝ := α M + 1 with hw
  set p : ℕ := insertPos α w M with hp
  have hpM : p ≤ M := insertPos_le α w M
  have hαM : ∀ i, i + 1 < M → α (i + 1) ≤ α i := fun i hi => hα i (by omega)
  set x : ℕ → ℝ := bump α w p with hx
  -- `x` is the nonincreasing rearrangement of the bumped vector
  have hx_anti : ∀ i, i + 1 < M + 1 → x (i + 1) ≤ x i :=
    bump_antitone hpM hαM (fun i hi => le_of_lt_insertPos i hi)
      (fun i h1 h2 => le_of_insertPos_le hαM i h1 h2)
  -- closed forms for the sums of `x`
  have hsplit : ∀ F : ℝ → ℝ,
      ∑ i ∈ range (M + 1), F (x i) = (∑ i ∈ range M, F (α i)) + F w := by
    intro F
    have := sum_bump F α w p (M + 1)
    rw [if_neg (by omega : ¬ (M + 1 ≤ p)), if_pos (by omega : p < M + 1)] at this
    simpa using this
  have hx_sum : ∑ i ∈ range (M + 1), x i = (∑ i ∈ range (M + 1), α i) + 1 := by
    have := hsplit id
    simp only [id] at this
    rw [this, hw, Finset.sum_range_succ]
    ring
  have hx_pow : ∑ i ∈ range (M + 1), x i ^ n
      = (∑ i ∈ range M, α i ^ n) + (α M + 1) ^ n := hsplit (fun t => t ^ n)
  -- the prefix-sum domination: the two branches are the paper's two subset cases
  have hpre : ∀ j, j ≤ M + 1 → ∑ i ∈ range j, x i ≤ ∑ i ∈ range j, μ i := by
    intro j hj
    have hxj := sum_bump id α w p j
    simp only [id] at hxj
    rcases le_or_gt j p with hcase | hcase
    · -- the `j` largest entries avoid the bumped one
      rw [hxj, if_pos hcase, if_neg (by omega : ¬ p < j), add_zero]
      exact Finset.sum_le_sum fun i hi =>
        hint1 i (by have := Finset.mem_range.mp hi; omega)
    · -- the `j` largest entries include the bumped one: pay for it with the trace identity
      rw [hxj, if_neg (by omega : ¬ j ≤ p), if_pos hcase]
      have hj1 : 1 ≤ j := by omega
      -- split both total sums at `j`
      have hMj : j + (M + 1 - j) = M + 1 := by omega
      have hMj' : (j - 1) + (M + 1 - j) = M := by omega
      have hsplitμ : ∑ i ∈ range (M + 1), μ i
          = (∑ i ∈ range j, μ i) + ∑ i ∈ range (M + 1 - j), μ (j + i) := by
        rw [← Finset.sum_range_add, hMj]
      have hsplitα : ∑ i ∈ range M, α i
          = (∑ i ∈ range (j - 1), α i) + ∑ i ∈ range (M + 1 - j), α ((j - 1) + i) := by
        rw [← Finset.sum_range_add, hMj']
      -- the tail of `μ` is dominated by the shifted tail of `α` (this is interlacing)
      have htail : ∑ i ∈ range (M + 1 - j), μ (j + i)
          ≤ ∑ i ∈ range (M + 1 - j), α ((j - 1) + i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        have h1 : (j - 1) + i + 1 < M + 1 := by omega
        have h2 := hint2 ((j - 1) + i) h1
        rwa [show (j - 1) + i + 1 = j + i by omega] at h2
      have hαsucc : ∑ i ∈ range (M + 1), α i = (∑ i ∈ range M, α i) + α M :=
        Finset.sum_range_succ α M
      rw [hw]
      linarith [htr, hsplitμ, hsplitα, htail, hαsucc]
  have hx_tot : ∑ i ∈ range (M + 1), x i = ∑ i ∈ range (M + 1), μ i := by
    rw [hx_sum, htr]
  have := karamata_pow (N := M + 1) hn hn0 x μ hx_anti hpre hx_tot
  rwa [hx_pow] at this

end CycleCommonality
