import CycleCommonality.Discrete

/-!
# The balanced two-clique obstruction

`W_cl` is the balanced disjoint union of two cliques, so its complement `U = 1 - W_cl` is the
balanced complete bipartite graphon.  As a two-cell step graphon, `w = (1/2, 1/2)` and
`U i j = if i = j then 0 else 1`.

The two computations of `eq:two-clique-even-cycle` and `eq:bipartite-odd-cycle` become
`2 × 2` matrix identities:

```
  matC = (1/2) • 1        so   t(C_n, W_cl)      = 2 (1/2)^n = 2^{1-n},
  mat  = (1/2) • S,  S² = 1,   t(C_{n+1}, 1-W_cl) = 0   since `n+1` is odd and `Tr S = 0`.
```

Hence at any `a` beyond the critical point the scaled commonality inequality fails, which is the
inclusion `π(C_n, C_{n+1}) ⊆ (0, α*_n]`.
-/

namespace CycleCommonality

open Finset Matrix

/-- The balanced two-cell step graphon whose kernel is the complete bipartite graphon; its
complement is the balanced disjoint union of two cliques. -/
noncomputable def twoClique : StepGraphon 2 where
  w := fun _ => 1 / 2
  U := fun i j => if i = j then 0 else 1
  w_pos := fun _ => by norm_num
  w_sum := by simp
  U_symm := fun i j => by by_cases h : i = j <;> simp [h, eq_comm]
  U_nonneg := fun i j => by by_cases h : i = j <;> simp [h]
  U_le_one := fun i j => by by_cases h : i = j <;> simp [h]

namespace twoClique

lemma sqrt_half : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = 1 / 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- The exchange matrix `S`, with `S ^ 2 = 1` and `Tr S = 0`. -/
noncomputable def exch : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

lemma exch_sq : exch ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exch, sq, Matrix.mul_apply, Fin.sum_univ_two]

lemma trace_exch : Matrix.trace exch = 0 := by
  simp [exch, Matrix.trace]

lemma mat_eq : twoClique.mat = (1 / 2 : ℝ) • exch := by
  ext i j
  simp only [StepGraphon.mat, exch, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  show (if i = j then (0:ℝ) else 1) * Real.sqrt (1/2) * Real.sqrt (1/2) = _
  rw [mul_assoc, sqrt_half]
  ring

lemma matC_eq : twoClique.matC = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp only [StepGraphon.matC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  show (1 - if i = j then (0:ℝ) else 1) * Real.sqrt (1/2) * Real.sqrt (1/2) = _
  rw [mul_assoc, sqrt_half]
  by_cases h : i = j <;> simp [h]

/-- `eq:two-clique-even-cycle`: `t(C_n, W_cl) = 2^{1-n}`. -/
theorem densityCompl_eq (n : ℕ) : twoClique.densityCompl n = twoCliqueValue n := by
  rw [StepGraphon.densityCompl, matC_eq, smul_pow, one_pow, Matrix.trace_smul,
    Matrix.trace_one, twoCliqueValue]
  simp
  ring

/-- `eq:bipartite-odd-cycle`: odd cycles have density zero in the balanced bipartite graphon. -/
theorem density_odd_eq_zero {m : ℕ} (hm : Odd m) : twoClique.density m = 0 := by
  obtain ⟨k, rfl⟩ := hm
  have hpow : exch ^ (2 * k + 1) = exch := by
    rw [pow_succ, pow_mul, exch_sq, one_pow, one_mul]
  rw [StepGraphon.density, mat_eq, smul_pow, hpow, Matrix.trace_smul, trace_exch]
  simp

/-- **The two-clique obstruction.**  Beyond the critical point the scaled
commonality inequality fails. -/
theorem violates {n d : ℕ} (hne : Even n) (hn4 : 4 ≤ n)
    (hd : Odd d) (hd0 : 0 < d) {a c : ℝ}
    (hc0 : 0 ≤ c) (hcrit : rho n d c = twoCliqueValue n) (hca : c < a) :
    twoClique.densityCompl n + kappa n d a * twoClique.density (n + d) < rho n d a := by
  have hodd : Odd (n + d) := by
    rcases hne with ⟨q, hq⟩
    rcases hd with ⟨r, hr⟩
    refine ⟨q + r, ?_⟩
    omega
  rw [densityCompl_eq, density_odd_eq_zero hodd, mul_zero, add_zero, ← hcrit]
  exact rho_strictMonoOn (by omega) hd0 hc0 (le_trans hc0 hca.le) hca

end twoClique

end CycleCommonality
