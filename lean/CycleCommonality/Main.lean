import CycleCommonality.Graphon
import CycleCommonality.StepTheorem

/-!
# Exact commonality region for a shorter even and a longer odd cycle

The even length is `n`, the positive odd gap is `d`, and the odd length is `n+d`.
-/

open MeasureTheory CycleCommonality.Foundation

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The commonality inequality in the paper's orientation. -/
theorem commonality_graphon_compl {n d : ℕ} (hne : Even n) (hn4 : 4 ≤ n)
    (hd : Odd d) (hd0 : 0 < d) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1)
    (hcrit : rho n d c = twoCliqueValue n) (ha0 : 0 < a) (hac : a ≤ c)
    {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    rho n d a ≤ cycleDensity W μ n +
      kappa n d a * cycleDensity (cmpl W) μ (n + d) := by
  have h := commonality_graphon hne hn4 hd hd0 hc hc1 hcrit ha0 hac
    (isGraphon_cmpl hW)
  rwa [cmpl_cmpl] at h

/-- Both cycle densities written as the homomorphism-density integrals used in the paper. -/
theorem commonality_graphon_integral {m d : ℕ} (hne : Even (m + 1)) (hn4 : 4 ≤ m + 1)
    (hd : Odd d) (hd0 : 0 < d) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1)
    (hcrit : rho (m + 1) d c = twoCliqueValue (m + 1))
    (ha0 : 0 < a) (hac : a ≤ c) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    rho (m + 1) d a ≤
      (∫ v : Fin (m + 1) → Ω, ∏ i, (1 - W (v i) (v (i + 1))) ∂Measure.pi fun _ => μ) +
        kappa (m + 1) d a *
          ∫ v : Fin (m + d + 1) → Ω, ∏ i, W (v i) (v (i + 1)) ∂Measure.pi fun _ => μ := by
  have h := commonality_graphon hne hn4 hd hd0 hc hc1 hcrit ha0 hac hW
  rw [cycleDensity_eq_integral (goodK_cmpl hW) m] at h
  rw [show m + 1 + d = (m + d) + 1 by omega,
    cycleDensity_eq_integral (goodK_of_isGraphon hW) (m + d)] at h
  simpa [cmpl] using h

/-- The commonality region for all graphons on all probability spaces. -/
theorem commonality_graphon_iff {n d : ℕ} (hne : Even n) (hn4 : 4 ≤ n)
    (hd : Odd d) (hd0 : 0 < d) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1)
    (hcrit : rho n d c = twoCliqueValue n) (ha0 : 0 < a) :
    (∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (W : Ω → Ω → ℝ), IsGraphon W μ →
          rho n d a ≤ cycleDensity (cmpl W) μ n +
            kappa n d a * cycleDensity W μ (n + d)) ↔
      a ≤ c := by
  constructor
  · intro hall
    by_contra hcon
    have hca : c < a := not_le.mp hcon
    have hviol := twoClique.violates hne hn4 hd hd0
      (by linarith : (0 : ℝ) ≤ c) hcrit hca
    have hthis := hall (Fin 2) inferInstance twoClique.measure inferInstance twoClique.U
      twoClique.isGraphon
    have hcomp : cycleDensity (cmpl twoClique.U) twoClique.measure n =
        twoClique.densityCompl n := by
      simpa [show n - 1 + 1 = n by omega] using (twoClique.cycleDensity_eq (n - 1)).2
    have hplain : cycleDensity twoClique.U twoClique.measure (n + d) =
        twoClique.density (n + d) := by
      simpa [show n + d - 1 + 1 = n + d by omega] using
        (twoClique.cycleDensity_eq (n + d - 1)).1
    rw [hcomp, hplain] at hthis
    linarith
  · intro hac Ω _ μ _ W hW
    exact commonality_graphon hne hn4 hd hd0 hc hc1 hcrit ha0 hac hW

end CycleCommonality
