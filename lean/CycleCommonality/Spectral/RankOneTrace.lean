import CycleCommonality.Spectral.Interlace
import CycleCommonality.Majorization.RankOne

/-!
# Corollary `cor:rank-one-trace`: the even trace under subtraction of a rank-one projection

This file proves the following rank-one trace bound:

```
  Tr (P - T) ^ n  ≥  (1 - λ₀) ^ n + ∑_{i ≠ 0} |λ i| ^ n            (n even),
```

where `λ` are the eigenvalues of the symmetric operator `T` in nonincreasing order and `P` is the
orthogonal projection onto a unit vector `u`.  Since `n` is even, `|λ i| ^ n = λ i ^ n`, so the
absolute values do not appear below.

The proof is the paper's: apply the rank-one lower majorization to `A = -T` — whose eigensystem is
`S.neg`, obtained by reversing and negating — and then Karamata.  All three spectral inputs come
from `Spectral/Interlace.lean`; the combinatorics is `Majorization/RankOne.lean`.

This is the point where the paper's inequality is **tight**: for the balanced two-clique graphon
the spectrum of `T` is `{1/2, -1/2}` and both sides equal `2 ^ (1-n)`.
-/

namespace CycleCommonality

open Finset Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

/-! ### Transport between `Fin N`- and `ℕ`-indexed sequences -/

/-- Extend a `Fin N`-indexed sequence to `ℕ` by zero.  `Majorization/RankOne.lean` is stated for
`ℕ`-indexed sequences (so that its inductions are over `Finset.range`). -/
noncomputable def ofFin (f : Fin N → ℝ) : ℕ → ℝ := fun k => if h : k < N then f ⟨k, h⟩ else 0

@[simp] lemma ofFin_coe (f : Fin N → ℝ) (i : Fin N) : ofFin f (i : ℕ) = f i := by
  simp [ofFin, i.isLt]

lemma ofFin_of_lt (f : Fin N → ℝ) {k : ℕ} (h : k < N) : ofFin f k = f ⟨k, h⟩ := by
  simp [ofFin, h]

lemma sum_range_ofFin (f : Fin N → ℝ) (g : ℝ → ℝ) :
    ∑ k ∈ range N, g (ofFin f k) = ∑ i, g (f i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => g (ofFin f k)) N]
  exact Finset.sum_congr rfl fun i _ => by rw [ofFin_coe]

lemma sum_range_ofFin_id (f : Fin N → ℝ) : ∑ k ∈ range N, ofFin f k = ∑ i, f i :=
  sum_range_ofFin f id

/-! ### The corollary -/

variable {T : E →ₗ[ℝ] E} {u : E}

/-- **Corollary `cor:rank-one-trace`.**  For even `n`, subtracting a symmetric operator from a
rank-one orthogonal projection can only increase the `n`-th trace beyond the value obtained by
shifting the Perron eigenvalue alone. -/
theorem trace_rankOne_sub_pow_ge
    (S : EigenSystem N T) (hn : finrank ℝ E = N) (hN : 0 < N) (hu : ‖u‖ = 1)
    {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) :
    (1 - S.val ⟨0, hN⟩) ^ n + ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (S.val i) ^ n
      ≤ LinearMap.trace ℝ E ((rankOne u - T) ^ n) := by
  classical
  -- the perturbed operator and its eigensystem
  have hsub : rankOne u - T = -T + rankOne u := by rw [sub_eq_neg_add]
  have hB : ((-T) + rankOne u).IsSymmetric := by
    intro x y
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right]
    rw [S.neg.symm x y, rankOne_isSymmetric u x y]
  set SA : EigenSystem N (-T) := S.neg with hSA
  set SB : EigenSystem N ((-T) + rankOne u) := EigenSystem.ofSymmetric hB hn with hSB
  -- the three spectral inputs
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hanti : ∀ i, i + 1 < N → ofFin SA.val (i + 1) ≤ ofFin SA.val i := by
    intro i hi
    rw [ofFin_of_lt _ hi, ofFin_of_lt _ (by omega : i < N)]
    exact SA.antitone (by exact Fin.mk_le_mk.mpr (by omega))
  have hint1 : ∀ i, i < N → ofFin SA.val i ≤ ofFin SB.val i := by
    intro i hi
    rw [ofFin_of_lt _ hi, ofFin_of_lt _ hi]
    exact val_le_of_rankOne SA SB hn ⟨i, hi⟩
  have hint2 : ∀ i, i + 1 < N → ofFin SB.val (i + 1) ≤ ofFin SA.val i := by
    intro i hi
    rw [ofFin_of_lt _ hi, ofFin_of_lt _ (by omega : i < N)]
    exact val_succ_le_of_rankOne SA SB hn hu0 ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  have htr : ∑ k ∈ range N, ofFin SB.val k = (∑ k ∈ range N, ofFin SA.val k) + 1 := by
    rw [sum_range_ofFin_id SB.val, sum_range_ofFin_id SA.val]
    simpa using sum_val_rankOne SA SB hu
  -- the majorization lemma
  have key := rank_one_majorization_pow (N := N) (n := n) hne hn0 hN
    (ofFin SA.val) (ofFin SB.val) hanti hint1 hint2 htr
  -- identify the right-hand side with the trace
  have hrhs : ∑ k ∈ range N, (ofFin SB.val k) ^ n
      = LinearMap.trace ℝ E ((rankOne u - T) ^ n) := by
    rw [sum_range_ofFin SB.val (fun t => t ^ n), hsub, SB.trace_pow_eq_sum n]
  -- identify the bumped entry with `1 - λ₀`
  have hrev : ((⟨N - 1, by omega⟩ : Fin N)).rev = (⟨0, hN⟩ : Fin N) := by
    apply Fin.ext
    simp [Fin.val_rev]
    omega
  have hlast : ofFin SA.val (N - 1) + 1 = 1 - S.val ⟨0, hN⟩ := by
    rw [ofFin_of_lt _ (by omega : N - 1 < N), hSA, EigenSystem.neg_val, hrev]
    ring
  -- identify the remaining sum with the sum over the nonzero eigenvalues
  have hhead : ∑ k ∈ range (N - 1), (ofFin SA.val k) ^ n
      = ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (S.val i) ^ n := by
    have hstep : ∀ k ∈ range (N - 1),
        (ofFin SA.val k) ^ n = (ofFin S.val (N - 1 - k)) ^ n := by
      intro k hk
      have hk' : k < N - 1 := Finset.mem_range.mp hk
      have h1 : ofFin SA.val k = -(S.val ((⟨k, by omega⟩ : Fin N).rev)) := by
        rw [ofFin_of_lt _ (by omega : k < N), hSA, EigenSystem.neg_val]
      have h2 : ((⟨k, by omega⟩ : Fin N)).rev = (⟨N - 1 - k, by omega⟩ : Fin N) := by
        apply Fin.ext; simp [Fin.val_rev]; omega
      rw [h1, h2, hne.neg_pow, ofFin_of_lt _ (by omega : N - 1 - k < N)]
    rw [Finset.sum_congr rfl hstep]
    -- reflect `k ↦ N - 1 - k` and peel off the `0`-th term on the other side
    have hrefl := Finset.sum_range_reflect (fun j => (ofFin S.val (j + 1)) ^ n) (N - 1)
    have hleft : ∑ k ∈ range (N - 1), (ofFin S.val (N - 1 - k)) ^ n
        = ∑ k ∈ range (N - 1), (ofFin S.val (N - 1 - 1 - k + 1)) ^ n := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < N - 1 := Finset.mem_range.mp hk
      have hidx : N - 1 - k = N - 1 - 1 - k + 1 := by omega
      rw [hidx]
    rw [hleft, hrefl]
    have herase : ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (S.val i) ^ n
        = (∑ i, (S.val i) ^ n) - (S.val ⟨0, hN⟩) ^ n := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [herase, ← sum_range_ofFin S.val (fun t => t ^ n)]
    have hsplit : ∑ k ∈ range N, (ofFin S.val k) ^ n
        = (∑ j ∈ range (N - 1), (ofFin S.val (j + 1)) ^ n) + (ofFin S.val 0) ^ n := by
      have h := Finset.sum_range_succ' (fun k => (ofFin S.val k) ^ n) (N - 1)
      rw [show N - 1 + 1 = N from by omega] at h
      exact h
    rw [hsplit, ofFin_of_lt _ hN]
    ring
  rw [hlast, hhead, hrhs] at key
  linarith [key]

end CycleCommonality
