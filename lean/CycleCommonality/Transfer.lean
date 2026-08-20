import CycleCommonality.StepDensity

/-!
# From step graphons to all graphons

An inequality of the shape

```
  c ≤ t(C_n, 1−W) + κ · t(C_{n+1}, W)      (κ ≥ 0)
```

that holds for every step graphon holds for every graphon.  Given `W`, approximate it in `L¹` by a
step graphon (`exists_stepGraphon_l1_close`); both densities move by at most a constant multiple of
the `L¹` error (`abs_cycleDensity_sub_le`), and the error can be made arbitrarily small.

No compactness of the space of graphons is involved: a single graphon is approximated, and the
inequality is transported along that approximation.
-/

open MeasureTheory OddCycleBound

set_option linter.unusedSectionVars false

noncomputable section

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma l1norm_sub_comm (K L : Ω → Ω → ℝ) :
    l1norm μ (fun x y => K x y - L x y) = l1norm μ (fun x y => L x y - K x y) := by
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  exact abs_sub_comm _ _

lemma abs_le_one_of_isGraphon {V : Ω → Ω → ℝ} (hV : IsGraphon V μ) (x y : Ω) : |V x y| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [hV.nonneg x y], hV.le_one x y⟩

/-- The two densities of a graphon move by at most `r · ‖W − V‖₁`. -/
lemma abs_cycleDensity_sub_le_of_graphon {W V : Ω → Ω → ℝ} (hW : IsGraphon W μ)
    (hV : IsGraphon V μ) (m : ℕ) :
    |cycleDensity W μ (m + 2) - cycleDensity V μ (m + 2)|
      ≤ (m + 2) * l1norm μ (fun x y => W x y - V x y) :=
  abs_cycleDensity_sub_le (goodK_of_isGraphon hW) (goodK_of_isGraphon hV)
    (abs_le_one_of_isGraphon hW) (abs_le_one_of_isGraphon hV) m

/-- **Transfer.**  An inequality of the paper's shape that holds for all step graphons holds for
all graphons. -/
theorem commonality_of_stepKernel {n : ℕ} (hn : 2 ≤ n) {κ c : ℝ} (hκ : 0 ≤ κ)
    (hstep : ∀ V : Ω → Ω → ℝ, IsGraphon V μ → IsStepKernel V →
      c ≤ cycleDensity (cmpl V) μ n + κ * cycleDensity V μ (n + 1))
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    c ≤ cycleDensity (cmpl W) μ n + κ * cycleDensity W μ (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set C : ℝ := (m + 2) + κ * (m + 3) with hC
  have hC0 : 0 ≤ C := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hC]; nlinarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- pick an approximant accurate enough that both densities move by less than `δ`
  set ε : ℝ := δ / (C + 1) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨V, hV, _hVstep, hclose⟩ := exists_stepGraphon_l1_close hW hε0
  have hbase := hstep V hV _hVstep
  -- the complement densities are close
  have hcompl : |cycleDensity (cmpl W) μ (m + 2) - cycleDensity (cmpl V) μ (m + 2)|
      ≤ (m + 2) * ε := by
    refine le_trans (abs_cycleDensity_sub_le_of_graphon (isGraphon_cmpl hW)
      (isGraphon_cmpl hV) m) ?_
    have hnn : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    refine mul_le_mul_of_nonneg_left (le_of_lt ?_) hnn
    have hrw : l1norm μ (fun x y => cmpl W x y - cmpl V x y)
        = l1norm μ (fun x y => W x y - V x y) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show |(1 - W x y) - (1 - V x y)| = |W x y - V x y|
      have hneg : (1 - W x y) - (1 - V x y) = -(W x y - V x y) := by ring
      rw [hneg, abs_neg]
    rw [hrw]
    exact hclose
  -- and so are the graphon densities, at length `m + 3`
  have hplain : |cycleDensity W μ (m + 3) - cycleDensity V μ (m + 3)| ≤ (m + 3) * ε := by
    have h := abs_cycleDensity_sub_le_of_graphon hW hV (m + 1)
    have hidx : (m + 1) + 2 = m + 3 := by omega
    rw [hidx] at h
    refine le_trans h ?_
    have hnn : (0 : ℝ) ≤ ((m : ℝ) + 1) + 2 := by positivity
    have hle : l1norm μ (fun x y => W x y - V x y) ≤ ε := le_of_lt hclose
    have : (((m : ℕ) + 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 3 := by push_cast; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  -- combine
  have hCε : C * ε ≤ δ := by
    have hpos : (0 : ℝ) < C + 1 := by linarith
    rw [hε, mul_comm, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [hC0, hδ.le]
  have h1 : cycleDensity (cmpl V) μ (m + 2)
      ≤ cycleDensity (cmpl W) μ (m + 2) + ((m : ℝ) + 2) * ε := by
    have := abs_le.1 hcompl
    linarith [this.1, this.2]
  have h2 : κ * cycleDensity V μ (m + 3)
      ≤ κ * cycleDensity W μ (m + 3) + κ * (((m : ℝ) + 3) * ε) := by
    have := abs_le.1 hplain
    nlinarith [this.1, this.2, hκ]
  have hsum : c ≤ cycleDensity (cmpl W) μ (m + 2) + κ * cycleDensity W μ (m + 3) + C * ε := by
    have hidx : m + 2 + 1 = m + 3 := by omega
    rw [hidx] at hbase
    rw [hC]
    nlinarith [hbase, h1, h2]
  have hidx : m + 2 + 1 = m + 3 := by omega
  rw [hidx]
  linarith [hsum, hCε]

end CycleCommonality
