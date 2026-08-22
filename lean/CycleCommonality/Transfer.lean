import CycleCommonality.StepDensity

/-!
# From step graphons to all graphons

This transfer theorem accepts two arbitrary cycle lengths.  The main theorem applies it with the
even length `n` and the longer odd length `n+d`.
-/

open MeasureTheory CycleCommonality.Foundation

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

lemma abs_le_one_of_isGraphon {V : Ω → Ω → ℝ} (hV : IsGraphon V μ) (x y : Ω) :
    |V x y| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [hV.nonneg x y], hV.le_one x y⟩

/-- The cycle density of a graphon is Lipschitz in `L¹`. -/
lemma abs_cycleDensity_sub_le_of_graphon {W V : Ω → Ω → ℝ}
    (hW : IsGraphon W μ) (hV : IsGraphon V μ) (m : ℕ) :
    |cycleDensity W μ (m + 2) - cycleDensity V μ (m + 2)| ≤
      (m + 2) * l1norm μ (fun x y => W x y - V x y) :=
  abs_cycleDensity_sub_le (goodK_of_isGraphon hW) (goodK_of_isGraphon hV)
    (abs_le_one_of_isGraphon hW) (abs_le_one_of_isGraphon hV) m

/-- An inequality involving any two cycle lengths transfers from step graphons to all graphons. -/
theorem commonality_of_stepKernel {n l : ℕ} (hn : 2 ≤ n) (hl : 2 ≤ l)
    {κ target : ℝ} (hκ : 0 ≤ κ)
    (hstep : ∀ V : Ω → Ω → ℝ, IsGraphon V μ → IsStepKernel V →
      target ≤ cycleDensity (cmpl V) μ n + κ * cycleDensity V μ l)
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    target ≤ cycleDensity (cmpl W) μ n + κ * cycleDensity W μ l := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, l = q + 2 := ⟨l - 2, by omega⟩
  subst n
  subst l
  set C : ℝ := (m + 2) + κ * (q + 2) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η : ℝ := ε / (C + 1) with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨V, hV, hVstep, hclose⟩ := exists_stepGraphon_l1_close hW hη0
  have hbase := hstep V hV hVstep
  have hcompl :
      |cycleDensity (cmpl W) μ (m + 2) - cycleDensity (cmpl V) μ (m + 2)| ≤
        (m + 2) * η := by
    refine le_trans (abs_cycleDensity_sub_le_of_graphon (isGraphon_cmpl hW)
      (isGraphon_cmpl hV) m) ?_
    have hnn : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    refine mul_le_mul_of_nonneg_left (le_of_lt ?_) hnn
    have hrw : l1norm μ (fun x y => cmpl W x y - cmpl V x y) =
        l1norm μ (fun x y => W x y - V x y) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show |(1 - W x y) - (1 - V x y)| = |W x y - V x y|
      rw [show (1 - W x y) - (1 - V x y) = -(W x y - V x y) by ring, abs_neg]
    rw [hrw]
    exact hclose
  have hplain :
      |cycleDensity W μ (q + 2) - cycleDensity V μ (q + 2)| ≤ (q + 2) * η := by
    refine le_trans (abs_cycleDensity_sub_le_of_graphon hW hV q) ?_
    exact mul_le_mul_of_nonneg_left (le_of_lt hclose) (by positivity)
  have hCη : C * η ≤ ε := by
    have hpos : (0 : ℝ) < C + 1 := by linarith
    rw [hη, mul_comm, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [hC0, hε.le]
  have h1 : cycleDensity (cmpl V) μ (m + 2) ≤
      cycleDensity (cmpl W) μ (m + 2) + ((m : ℝ) + 2) * η := by
    have habs := abs_le.1 hcompl
    norm_num at habs ⊢
    linarith
  have h2 : κ * cycleDensity V μ (q + 2) ≤
      κ * cycleDensity W μ (q + 2) + κ * (((q : ℝ) + 2) * η) := by
    have habs := abs_le.1 hplain
    have hdens : cycleDensity V μ (q + 2) ≤
        cycleDensity W μ (q + 2) + ((q : ℝ) + 2) * η := by
      norm_num at habs ⊢
      linarith
    calc
      κ * cycleDensity V μ (q + 2) ≤
          κ * (cycleDensity W μ (q + 2) + ((q : ℝ) + 2) * η) :=
        mul_le_mul_of_nonneg_left hdens hκ
      _ = κ * cycleDensity W μ (q + 2) + κ * (((q : ℝ) + 2) * η) := by ring
  have hsum : target ≤ cycleDensity (cmpl W) μ (m + 2) +
      κ * cycleDensity W μ (q + 2) + C * η := by
    have herror : C * η = ((m : ℝ) + 2) * η + κ * (((q : ℝ) + 2) * η) := by
      rw [hC]
      ring
    rw [herror]
    linarith [hbase, h1, h2]
  linarith

end CycleCommonality
