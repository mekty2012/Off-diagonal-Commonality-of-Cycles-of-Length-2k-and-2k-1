import CycleCommonality.Model.TailBound
import CycleCommonality.Scalar.KappaBounds

/-!
# The spectral reduction and the lower bound, for step graphons

`prop:spectral-reduction` and `prop:lower-bound` of `adjacent_cycle_commonality.tex`, in the
finite model of `Model/StepModel.lean`.

`spectral_reduction` is Corollary `cor:rank-one-trace` plus the eigenvalue expansion of
`t(C_{n+1}, U) = Tr(T^{n+1})`, rearranged.  Note that no sign condition on `κ` is needed: the
`κ`-part of the rearrangement is an identity.

`lower_bound` is the paper's case split.  Call `i ≠ 0` *dangerous* when `1 + κ λ i < 0`.

* No dangerous index: every tail term is nonnegative because `n` is even, and `f_κ(λ₀) ≥ ρ_n(a)`
  by `fk_min`.
* One dangerous index `i₀` (there is at most one, by the tail sum bound against `κ² < 8`):
  write `β = -λ i₀ > 1/κ > b`.  Perron--Frobenius-type domination gives `λ₀ ≥ β`, so
  `f_κ(λ₀) ≥ f_κ(β)` by `fk_mono`, and the dangerous term is compensated exactly:
  `f_κ(β) + β^n(1 - κβ) = (1-β)^n + β^n ≥ 2^{1-n} ≥ ρ_n(a)`.
-/

namespace CycleCommonality

open Finset
open scoped RealInnerProductSpace

namespace StepGraphon

variable {N : ℕ} (G : StepGraphon N)

/-- **Proposition `prop:spectral-reduction`** (`eq:master-spectral`). -/
theorem spectral_reduction (hN : 0 < N) {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) (κ : ℝ) :
    fk n κ (G.perron hN)
        + ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ n * (1 + κ * G.lam i)
      ≤ G.densityCompl n + κ * G.density (n + 1) := by
  classical
  -- Corollary 3.2 for the kernel operator
  have hcor := trace_rankOne_sub_pow_ge (T := G.op) (u := G.unit) G.sys
    finrank_euclideanSpace_fin hN G.norm_unit hne hn0
  rw [G.trace_compl_pow n] at hcor
  -- the odd density expands over the eigenvalues
  have hodd : G.density (n + 1) = ∑ i, (G.lam i) ^ (n + 1) := by
    rw [density, ← G.trace_op_pow (n + 1), G.sys.trace_pow_eq_sum (n + 1)]
    rfl
  have hsplit : ∑ i, (G.lam i) ^ (n + 1)
      = (G.perron hN) ^ (n + 1)
        + ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ (n + 1) := by
    exact (Finset.add_sum_erase Finset.univ (fun i => (G.lam i) ^ (n + 1))
      (Finset.mem_univ (⟨0, hN⟩ : Fin N))).symm
  -- split the tail sum
  have htail : ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ n * (1 + κ * G.lam i)
      = (∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ n)
        + κ * ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ (n + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  rw [htail, hodd, hsplit, fk, densityCompl]
  have hperron : G.perron hN = G.sys.val ⟨0, hN⟩ := rfl
  rw [hperron]
  have hlam : ∀ i : Fin N, G.lam i = G.sys.val i := fun _ => rfl
  simp only [hlam] at *
  linarith [hcor]

/-- At most one index is dangerous: two would violate the tail sum bound. -/
lemma dangerous_unique (hN : 0 < N) {κ : ℝ} (_hκ0 : 0 < κ) (hκ8 : κ ^ 2 < 8)
    {i j : Fin N} (hi : i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N))
    (hj : j ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N))
    (hdi : 1 + κ * G.lam i < 0) (hdj : 1 + κ * G.lam j < 0) : i = j := by
  classical
  by_contra hne
  have htail := G.tail_sum_bound_quarter hN
  have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ.erase (⟨0, hN⟩ : Fin N) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact hi
    · rw [Finset.mem_singleton] at hk'; subst hk'; exact hj
  have hpair : ∑ k ∈ ({i, j} : Finset (Fin N)), (G.lam k) ^ 2
      = (G.lam i) ^ 2 + (G.lam j) ^ 2 := by
    rw [Finset.sum_pair hne]
  have hle : (G.lam i) ^ 2 + (G.lam j) ^ 2
      ≤ ∑ k ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam k) ^ 2 := by
    rw [← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => sq_nonneg _
  -- each dangerous eigenvalue contributes more than `1/κ²`
  have hsq : ∀ x : ℝ, 1 + κ * x < 0 → 1 < κ ^ 2 * x ^ 2 := by
    intro x hx
    have hxneg : κ * x < -1 := by linarith
    nlinarith [hxneg]
  have h1 := hsq _ hdi
  have h2 := hsq _ hdj
  nlinarith [h1, h2, hle, htail, hκ8, sq_nonneg κ]

/-- **Proposition `prop:lower-bound`**: commonality up to the critical point, for step
graphons. -/
theorem lower_bound (hN : 0 < N) {n : ℕ} (hne : Even n) (hn4 : 4 ≤ n)
    {a c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1) (hcrit : rho n c = twoCliqueValue n)
    (ha0 : 0 < a) (hac : a ≤ c) :
    rho n a ≤ G.densityCompl n + kappa n a * G.density (n + 1) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have ha1 : a < 1 := lt_of_le_of_lt hac hc1
  set κ := kappa n a with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef, kappa]
    have h1 : (0 : ℝ) < a ^ (n - 1) := by positivity
    have h2 : (0 : ℝ) < (1 - a) ^ n := by
      apply pow_pos; linarith
    have h3 : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    positivity
  have hκ8 : κ ^ 2 < 8 := kappa_sq_lt_eight hn4 hc hc1 hcrit ha0 hac
  have hκb : κ * (1 - a) < 1 := kappa_mul_lt_one hn4 hc hc1 hcrit ha0 hac
  have hred := G.spectral_reduction hN hne hn0 κ
  have hperron0 : 0 ≤ G.perron hN := G.perron_nonneg hN
  have hperron1 : G.perron hN ≤ 1 := G.perron_le_one hN
  set S := Finset.univ.erase (⟨0, hN⟩ : Fin N) with hS
  by_cases hcase : ∃ i ∈ S, 1 + κ * G.lam i < 0
  · -- Case 2: a single dangerous eigenvalue, compensated by the Perron eigenvalue
    obtain ⟨i₀, hi₀S, hi₀⟩ := hcase
    set β : ℝ := -(G.lam i₀) with hβ
    have hβκ : 1 / κ < β := by
      rw [div_lt_iff₀ hκpos, hβ]
      nlinarith [hi₀, hκpos]
    have hbβ : 1 - a < β := by
      have h1 : (1 : ℝ) - a < 1 / κ := by
        rw [lt_div_iff₀ hκpos]
        linarith [hκb]
      linarith [hβκ, h1]
    have hβperron : β ≤ G.perron hN := by
      have := G.abs_lam_le_perron hN i₀
      rw [hβ]
      linarith [neg_abs_le (G.lam i₀), le_abs_self (G.lam i₀), this]
    have hβ1 : β ≤ 1 := le_trans hβperron hperron1
    -- all other tail terms are nonnegative
    have hother : ∀ i ∈ S.erase i₀, 0 ≤ (G.lam i) ^ n * (1 + κ * G.lam i) := by
      intro i hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
      have hnd : 0 ≤ 1 + κ * G.lam i := by
        by_contra hcon
        exact hine (G.dangerous_unique hN hκpos hκ8 hiS hi₀S (not_le.mp hcon) hi₀)
      exact mul_nonneg (hne.pow_nonneg _) hnd
    have htailge : (G.lam i₀) ^ n * (1 + κ * G.lam i₀)
        ≤ ∑ i ∈ S, (G.lam i) ^ n * (1 + κ * G.lam i) := by
      rw [← Finset.add_sum_erase _ _ hi₀S]
      linarith [Finset.sum_nonneg hother]
    -- `f_κ` is increasing to the right of `b`
    have hfk : fk n κ β ≤ fk n κ (G.perron hN) :=
      fk_mono hne hn0 ha0 ha1 (le_of_lt hbβ) hβ1 hβperron
    -- the dangerous term is compensated exactly
    have hpay : fk n κ β + (G.lam i₀) ^ n * (1 + κ * G.lam i₀) = (1 - β) ^ n + β ^ n := by
      have hlam : G.lam i₀ = -β := by rw [hβ]; ring
      rw [hlam, fk, hne.neg_pow]
      ring
    have hconv : twoCliqueValue n ≤ (1 - β) ^ n + β ^ n := two_point_convexity hne hn0 β
    have hmono : rho n a ≤ twoCliqueValue n := by
      rw [← hcrit]
      rcases eq_or_lt_of_le hac with rfl | hlt
      · exact le_rfl
      · exact (rho_strictMonoOn (by omega) (le_of_lt ha0) (by linarith : (0:ℝ) ≤ c) hlt).le
    linarith [hred, hfk, htailge, hpay, hconv, hmono]
  · -- Case 1: no dangerous eigenvalue
    simp only [not_exists, not_and, not_lt] at hcase
    have hnonneg : 0 ≤ ∑ i ∈ S, (G.lam i) ^ n * (1 + κ * G.lam i) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hne.pow_nonneg _) (hcase i hi)
    have hmin : rho n a ≤ fk n κ (G.perron hN) := fk_min hne hn0 ha0 ha1 hperron0
    linarith [hred, hnonneg, hmin]

end StepGraphon

end CycleCommonality
