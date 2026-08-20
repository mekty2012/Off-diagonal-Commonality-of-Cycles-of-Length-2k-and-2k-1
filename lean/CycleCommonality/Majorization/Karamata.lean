import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Karamata's inequality for even powers

Mathlib has no majorization order and no Karamata inequality, so we build the special case the
proof of `adjacent_cycle_commonality.tex` needs: the convex function is `x ↦ x ^ n` with `n`
**even**, hence convex on all of `ℝ` — see point (3) of the audit, the inequality is false if one
only has convexity on `[0, ∞)`.

Everything is indexed by `ℕ` and summed over `Finset.range N`, which keeps the induction in
`abel_sum_eq` clean.  `Fin`-indexed data (Mathlib's `eigenvalues`) is transported in
`Majorization/Defs.lean`.

Main results:

* `pow_tangent_le` — the supporting-line inequality `x ^ n + n x ^ (n-1) (y - x) ≤ y ^ n`
  for even `n`, proved from Bernoulli after dividing by `x ^ n`;
* `abel_sum_nonneg` — summation by parts: if `c` is nonincreasing, all prefix sums of `d` are
  nonnegative, and the total sum of `d` vanishes, then `∑ c i * d i ≥ 0`;
* `karamata_pow` — if `x` is nonincreasing, every prefix sum of `x` is at most the corresponding
  prefix sum of `y`, and the totals agree, then `∑ x i ^ n ≤ ∑ y i ^ n`.

Note that `y` is *not* required to be sorted: only `x` is, because the slopes `n x i ^ (n-1)`
are what has to be nonincreasing for the Abel argument.
-/

namespace CycleCommonality

open Finset

/-! ### The supporting-line inequality -/

/-- Bernoulli in the form used below: `1 + n * (u - 1) ≤ u ^ n` for **even** `n` and every real
`u`.  For `u ≥ -1` this is `one_add_mul_le_pow`; for `u < -1` the left side is negative while the
right side is nonnegative. -/
theorem one_add_mul_sub_one_le_pow {n : ℕ} (hn : Even n) (u : ℝ) :
    1 + (n : ℝ) * (u - 1) ≤ u ^ n := by
  rcases le_or_gt (-1 : ℝ) u with hu | hu
  · have h : (-2 : ℝ) ≤ u - 1 := by linarith
    have := one_add_mul_le_pow h n
    simpa using this
  · have hup : (0 : ℝ) ≤ u ^ n := hn.pow_nonneg u
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact Or.inr h
      · exact Or.inl (by exact_mod_cast h)
    rcases hn1 with hn1 | rfl
    · nlinarith [hn1, hu]
    · simp

/-- The supporting-line (tangent) inequality for `x ↦ x ^ n` at even `n`:
`x ^ n + n * x ^ (n - 1) * (y - x) ≤ y ^ n` for all reals `x, y`. -/
theorem pow_tangent_le {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) (x y : ℝ) :
    x ^ n + (n : ℝ) * x ^ (n - 1) * (y - x) ≤ y ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)).symm⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd hn (by decide)
    · exact h
  rcases eq_or_ne x 0 with rfl | hx
  · have : (0 : ℝ) ^ m = 0 := zero_pow (by omega)
    simp [this, hn.pow_nonneg y]
  · -- divide by `x ^ (m+1) > 0` and apply Bernoulli to `u = y / x`
    have hxpos : (0 : ℝ) < x ^ (m + 1) := lt_of_le_of_ne (hn.pow_nonneg x) (by
      simpa [eq_comm] using (pow_ne_zero (m + 1) hx))
    set u : ℝ := y / x with hu
    have hyu : y = x * u := by rw [hu]; field_simp
    have hkey : 1 + ((m : ℝ) + 1) * (u - 1) ≤ u ^ (m + 1) := by
      have := one_add_mul_sub_one_le_pow hn u
      simpa using this
    have hxm : x ^ (m + 1) = x ^ m * x := by ring
    calc x ^ (m + 1) + ((m : ℝ) + 1) * x ^ m * (y - x)
        = x ^ (m + 1) * (1 + ((m : ℝ) + 1) * (u - 1)) := by
          rw [hyu]; rw [hxm]; ring
      _ ≤ x ^ (m + 1) * u ^ (m + 1) := by
          exact mul_le_mul_of_nonneg_left hkey hxpos.le
      _ = y ^ (m + 1) := by rw [hyu]; rw [mul_pow]

/-! ### Summation by parts -/

/-- The prefix sums of `d`. -/
private def pre (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, d i

/-- Abel's summation-by-parts identity. -/
theorem abel_sum_eq (c d : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, c i * d i
      = (∑ j ∈ range N, (c j - c (j + 1)) * pre d (j + 1)) + c N * pre d N := by
  induction N with
  | zero => simp [pre]
  | succ N ih =>
      have hpre : pre d (N + 1) = pre d N + d N := by
        simp [pre, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := N)]
      rw [hpre]
      ring

/-- Summation by parts, in the form used by Karamata: a nonincreasing weight against a
difference sequence with nonnegative prefix sums and vanishing total sum. -/
theorem abel_sum_nonneg {N : ℕ} (c d : ℕ → ℝ)
    (hc : ∀ i, i + 1 < N → c (i + 1) ≤ c i)
    (hS : ∀ j, j ≤ N → 0 ≤ ∑ i ∈ range j, d i)
    (htot : ∑ i ∈ range N, d i = 0) :
    0 ≤ ∑ i ∈ range N, c i * d i := by
  rw [abel_sum_eq]
  have hzero : pre d N = 0 := htot
  rw [hzero, mul_zero, add_zero]
  refine Finset.sum_nonneg ?_
  intro j hj
  rcases lt_or_ge (j + 1) N with hlt | hge
  · exact mul_nonneg (by linarith [hc j hlt]) (hS (j + 1) hlt.le)
  · -- `j + 1 = N`, and then the prefix sum is the (vanishing) total
    have : j + 1 = N := le_antisymm (Finset.mem_range.mp hj) hge
    rw [this, hzero, mul_zero]

/-! ### Karamata for even powers -/

/-- **Karamata's inequality** for `x ↦ x ^ n` with `n` even.

`x` is nonincreasing on `range N`, every prefix sum of `x` is dominated by the corresponding
prefix sum of `y`, and the two totals agree.  Then `∑ x ^ n ≤ ∑ y ^ n`. -/
theorem karamata_pow {N n : ℕ} (hn : Even n) (hn0 : n ≠ 0) (x y : ℕ → ℝ)
    (hx : ∀ i, i + 1 < N → x (i + 1) ≤ x i)
    (hpre : ∀ j, j ≤ N → ∑ i ∈ range j, x i ≤ ∑ i ∈ range j, y i)
    (htot : ∑ i ∈ range N, x i = ∑ i ∈ range N, y i) :
    ∑ i ∈ range N, x i ^ n ≤ ∑ i ∈ range N, y i ^ n := by
  set c : ℕ → ℝ := fun i => (n : ℝ) * x i ^ (n - 1) with hc
  set d : ℕ → ℝ := fun i => y i - x i with hd
  -- the slopes are nonincreasing because `n - 1` is odd
  have hodd : Odd (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)).symm⟩
    simp only [Nat.add_sub_cancel]
    have hme : ¬ Even m := by simpa [Nat.even_add_one] using hn
    exact Nat.not_even_iff_odd.mp hme
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcmono : ∀ i, i + 1 < N → c (i + 1) ≤ c i := by
    intro i hi
    have := (Odd.pow_le_pow hodd (a := x (i + 1)) (b := x i)).mpr (hx i hi)
    exact mul_le_mul_of_nonneg_left this hnpos
  have habel : 0 ≤ ∑ i ∈ range N, c i * d i := by
    refine abel_sum_nonneg c d hcmono ?_ ?_
    · intro j hj
      have := hpre j hj
      simp only [hd, Finset.sum_sub_distrib]
      linarith
    · simp only [hd, Finset.sum_sub_distrib]
      linarith [htot]
  have hterm : ∀ i ∈ range N, x i ^ n + c i * d i ≤ y i ^ n := by
    intro i _
    have := pow_tangent_le hn hn0 (x i) (y i)
    simpa [hc, hd, mul_assoc] using this
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at this
  linarith

end CycleCommonality
