import CycleCommonality.Model.TailBound
import CycleCommonality.Scalar.KappaBounds

/-!
# The finite spectral lower bound for `C_n` and `C_(n+d)`

Here `n` is even, `d` is positive and odd, and hence `n+d` is odd.  The dangerous-eigenvalue
argument uses the direct comparison `-λ > 1-a > 5/14`; no roots or fractional powers occur.
-/

namespace CycleCommonality

open Finset
open scoped RealInnerProductSpace

namespace StepGraphon

variable {N : ℕ} (G : CycleCommonality.StepGraphon N)

/-- The spectral reduction with tail factor `1 + κ λ^d`. -/
theorem spectral_reduction (hN : 0 < N) {n d : ℕ} (hne : Even n) (hn0 : n ≠ 0)
    (κ : ℝ) :
    fk n d κ (G.perron hN) +
        ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N),
          (G.lam i) ^ n * (1 + κ * (G.lam i) ^ d) ≤
      G.densityCompl n + κ * G.density (n + d) := by
  classical
  have hcor := trace_rankOne_sub_pow_ge (T := G.op) (u := G.unit) G.sys
    finrank_euclideanSpace_fin hN G.norm_unit hne hn0
  rw [G.trace_compl_pow n] at hcor
  have hodd : G.density (n + d) = ∑ i, (G.lam i) ^ (n + d) := by
    rw [CycleCommonality.StepGraphon.density,
      ← G.trace_op_pow (n + d), G.sys.trace_pow_eq_sum (n + d)]
    rfl
  have hsplit : ∑ i, (G.lam i) ^ (n + d) =
      (G.perron hN) ^ (n + d) +
        ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ (n + d) := by
    exact (Finset.add_sum_erase Finset.univ (fun i => (G.lam i) ^ (n + d))
      (Finset.mem_univ (⟨0, hN⟩ : Fin N))).symm
  have htail :
      ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N),
          (G.lam i) ^ n * (1 + κ * (G.lam i) ^ d) =
        (∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ n) +
          κ * ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N),
            (G.lam i) ^ (n + d) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [pow_add]
      ring
  rw [htail, hodd, hsplit, fk, CycleCommonality.StepGraphon.densityCompl]
  have hperron : G.perron hN = G.sys.val ⟨0, hN⟩ := rfl
  rw [hperron]
  have hlam : ∀ i : Fin N, G.lam i = G.sys.val i := fun _ => rfl
  simp only [hlam] at *
  linarith [hcor]

/-- A dangerous eigenvalue lies strictly to the left of `-b`. -/
lemma dangerous_above {d : ℕ} (hd : Odd d) {κ b x : ℝ} (hκ : 0 < κ)
    (hκb : κ * b ^ d < 1) (hx : 1 + κ * x ^ d < 0) :
    b < -x := by
  have hxneg : x < 0 := by
    by_contra hcon
    have hx0 : 0 ≤ x := not_lt.mp hcon
    have hp0 : 0 ≤ x ^ d := pow_nonneg hx0 _
    nlinarith [mul_nonneg hκ.le hp0]
  have hbeta0 : 0 ≤ -x := by linarith
  have hbetapow : 1 < κ * (-x) ^ d := by
    rw [hd.neg_pow]
    nlinarith
  by_contra hcon
  have hle : -x ≤ b := not_lt.mp hcon
  have hp := pow_le_pow_left₀ hbeta0 hle d
  have hmul := mul_le_mul_of_nonneg_left hp hκ.le
  nlinarith

/-- At most one tail index is dangerous, using `b > 5/14` and the tail square budget. -/
lemma dangerous_unique (hN : 0 < N) {d : ℕ} (hd : Odd d) {κ b : ℝ}
    (hκ : 0 < κ) (hb : (5 : ℝ) / 14 < b) (hκb : κ * b ^ d < 1)
    {i j : Fin N} (hi : i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N))
    (hj : j ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N))
    (hdi : 1 + κ * (G.lam i) ^ d < 0)
    (hdj : 1 + κ * (G.lam j) ^ d < 0) : i = j := by
  classical
  by_contra hij
  have htail := G.tail_sum_bound_quarter hN
  have hsub : ({i, j} : Finset (Fin N)) ⊆
      Finset.univ.erase (⟨0, hN⟩ : Fin N) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact hi
    · rw [Finset.mem_singleton] at hq'
      subst hq'
      exact hj
  have hpair : ∑ q ∈ ({i, j} : Finset (Fin N)), (G.lam q) ^ 2 =
      (G.lam i) ^ 2 + (G.lam j) ^ 2 := by
    rw [Finset.sum_pair hij]
  have hle : (G.lam i) ^ 2 + (G.lam j) ^ 2 ≤
      ∑ q ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam q) ^ 2 := by
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => sq_nonneg _
  have hiβ : b < -(G.lam i) := dangerous_above hd hκ hκb hdi
  have hjβ : b < -(G.lam j) := dangerous_above hd hκ hκb hdj
  have hi5 : (5 : ℝ) / 14 < -(G.lam i) := lt_trans hb hiβ
  have hj5 : (5 : ℝ) / 14 < -(G.lam j) := lt_trans hb hjβ
  have hi2 : ((5 : ℝ) / 14) ^ 2 < (G.lam i) ^ 2 := by nlinarith
  have hj2 : ((5 : ℝ) / 14) ^ 2 < (G.lam j) ^ 2 := by nlinarith
  nlinarith [hle, htail]

/-- The finite lower bound. -/
theorem lower_bound (hN : 0 < N) {n d : ℕ} (hne : Even n) (hn4 : 4 ≤ n)
    (hd : Odd d) (hd0 : 0 < d) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1)
    (hcrit : rho n d c = twoCliqueValue n) (ha0 : 0 < a) (hac : a ≤ c) :
    rho n d a ≤ G.densityCompl n + kappa n d a * G.density (n + d) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hdne : d ≠ 0 := by omega
  have ha1 : a < 1 := lt_of_le_of_lt hac hc1
  set κ := kappa n d a with hκdef
  set b : ℝ := 1 - a with hbdef
  have hκpos : 0 < κ := by
    rw [hκdef, kappa]
    positivity
  have hb5 : (5 : ℝ) / 14 < b := by
    rw [hbdef]
    exact five_fourteenths_lt_one_sub hn4 hd0 hc hc1 hcrit hac
  have hκb : κ * b ^ d < 1 := by
    rw [hκdef, hbdef]
    exact kappa_mul_one_sub_pow_lt_one hn4 hd0 hc hc1 hcrit ha0 hac
  have hred := CycleCommonality.StepGraphon.spectral_reduction G hN
    (d := d) hne hn0 κ
  have hperron0 : 0 ≤ G.perron hN := G.perron_nonneg hN
  have hperron1 : G.perron hN ≤ 1 := G.perron_le_one hN
  set S := Finset.univ.erase (⟨0, hN⟩ : Fin N) with hS
  by_cases hcase : ∃ i ∈ S, 1 + κ * (G.lam i) ^ d < 0
  · obtain ⟨i₀, hi₀S, hi₀⟩ := hcase
    set β : ℝ := -(G.lam i₀) with hβ
    have hbβ : b < β := by
      rw [hβ]
      exact dangerous_above hd hκpos hκb hi₀
    have hβperron : β ≤ G.perron hN := by
      have hp := G.abs_lam_le_perron hN i₀
      rw [hβ]
      linarith [neg_abs_le (G.lam i₀), le_abs_self (G.lam i₀), hp]
    have hβ1 : β ≤ 1 := le_trans hβperron hperron1
    have hother : ∀ i ∈ S.erase i₀,
        0 ≤ (G.lam i) ^ n * (1 + κ * (G.lam i) ^ d) := by
      intro i hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
      have hndanger : 0 ≤ 1 + κ * (G.lam i) ^ d := by
        by_contra hcon
        exact hine (CycleCommonality.StepGraphon.dangerous_unique G hN hd
          hκpos hb5 hκb hiS hi₀S (not_le.mp hcon) hi₀)
      exact mul_nonneg (hne.pow_nonneg _) hndanger
    have htailge : (G.lam i₀) ^ n * (1 + κ * (G.lam i₀) ^ d) ≤
        ∑ i ∈ S, (G.lam i) ^ n * (1 + κ * (G.lam i) ^ d) := by
      rw [← Finset.add_sum_erase _ _ hi₀S]
      linarith [Finset.sum_nonneg hother]
    have hfk : fk n d κ β ≤ fk n d κ (G.perron hN) := by
      rw [hbdef] at hbβ
      rw [hκdef]
      exact fk_mono hne hn0 hdne ha0 ha1 (le_of_lt hbβ) hβ1 hβperron
    have hpay : fk n d κ β +
        (G.lam i₀) ^ n * (1 + κ * (G.lam i₀) ^ d) =
        (1 - β) ^ n + β ^ n := by
      have hlam : G.lam i₀ = -β := by rw [hβ]; ring
      rw [hlam, fk, hne.neg_pow, hd.neg_pow, pow_add]
      ring
    have hconv : twoCliqueValue n ≤ (1 - β) ^ n + β ^ n :=
      two_point_convexity hne hn0 β
    have hmono : rho n d a ≤ twoCliqueValue n := by
      rw [← hcrit]
      rcases eq_or_lt_of_le hac with rfl | halt
      · exact le_rfl
      · exact (rho_strictMonoOn (by omega) hd0 (le_of_lt ha0)
          (by linarith : (0 : ℝ) ≤ c) halt).le
    linarith [hred, hfk, htailge, hpay, hconv, hmono]
  · simp only [not_exists, not_and, not_lt] at hcase
    have hnonneg : 0 ≤ ∑ i ∈ S,
        (G.lam i) ^ n * (1 + κ * (G.lam i) ^ d) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hne.pow_nonneg _) (hcase i hi)
    have hmin : rho n d a ≤ fk n d κ (G.perron hN) := by
      rw [hκdef]
      exact fk_min hne hn0 hdne ha0 ha1 hperron0
    linarith [hred, hnonneg, hmin]

end StepGraphon

end CycleCommonality
