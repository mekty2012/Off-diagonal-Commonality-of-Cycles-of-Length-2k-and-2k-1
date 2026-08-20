import CycleCommonality.Graphon
import CycleCommonality.StepTheorem

/-!
# The commonality region of `C_n` and `C_{n+1}`

For `n = 2k ≥ 4` even, let `α*_n` be the unique point of `(1/2, 1)` with `ρ_n(α*) = 2^{1-n}`
(`exists_unique_critical`).  The scaled commonality inequality

```
  t(C_n, 1−W) + κ_n(a) · t(C_{n+1}, W) ≥ ρ_n(a)
```

holds for **every** graphon `W` on **every** probability space exactly when `a ≤ α*_n`.

`W : Ω² → [0,1]` is symmetric and jointly measurable over an arbitrary probability space `(Ω, μ)`
(`IsGraphon`), and the cycle density is the homomorphism density

```
  t(C_r, W) = ∫_{Ω^r} ∏_{i<r} W(x_i, x_{i+1}) dμ^{⊗r}        (indices read cyclically),
```

which is the form `commonality_graphon_integral` states the theorem in.
-/

open MeasureTheory OddCycleBound

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The commonality inequality, in the paper's orientation.**  Applying `commonality_graphon`
to the complement, which is again a graphon. -/
theorem commonality_graphon_compl {n : ℕ} (hne : Even n) (hn4 : 4 ≤ n) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1) (hcrit : rho n c = twoCliqueValue n) (ha0 : 0 < a)
    (hac : a ≤ c) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    rho n a ≤ cycleDensity W μ n + kappa n a * cycleDensity (cmpl W) μ (n + 1) := by
  have h := commonality_graphon hne hn4 hc hc1 hcrit ha0 hac (isGraphon_cmpl hW)
  rwa [cmpl_cmpl] at h

/-- **The commonality inequality, with both densities written as integrals.** -/
theorem commonality_graphon_integral {m : ℕ} (hne : Even (m + 1)) (hn4 : 4 ≤ m + 1) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1) (hcrit : rho (m + 1) c = twoCliqueValue (m + 1)) (ha0 : 0 < a)
    (hac : a ≤ c) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    rho (m + 1) a
      ≤ (∫ v : Fin (m + 1) → Ω, ∏ i, (1 - W (v i) (v (i + 1))) ∂(Measure.pi fun _ => μ))
        + kappa (m + 1) a
          * ∫ v : Fin (m + 2) → Ω, ∏ i, W (v i) (v (i + 1)) ∂(Measure.pi fun _ => μ) := by
  have h := commonality_graphon hne hn4 hc hc1 hcrit ha0 hac hW
  rwa [cycleDensity_eq_integral (goodK_cmpl hW) m,
    cycleDensity_eq_integral (goodK_of_isGraphon hW) (m + 1)] at h

/-- **The commonality region.**  For `n = 2k ≥ 4` and `c = α*_n` the critical point, the scaled
inequality holds for every graphon on every probability space if and only if `a ≤ α*_n`; beyond
the critical point it already fails for the balanced two-clique. -/
theorem commonality_graphon_iff {n : ℕ} (hne : Even n) (hn4 : 4 ≤ n) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1) (hcrit : rho n c = twoCliqueValue n) (ha0 : 0 < a) :
    (∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (W : Ω → Ω → ℝ), IsGraphon W μ →
          rho n a ≤ cycleDensity (cmpl W) μ n + kappa n a * cycleDensity W μ (n + 1))
      ↔ a ≤ c := by
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hviol := twoClique.violates hne hn4 (by linarith : (0 : ℝ) ≤ c) hcrit hcon
    have hthis := h (Fin 2) inferInstance twoClique.measure inferInstance twoClique.U
      twoClique.isGraphon
    rw [hm] at hthis
    rw [(twoClique.cycleDensity_eq m).2, (twoClique.cycleDensity_eq (m + 1)).1, ← hm] at hthis
    linarith
  · intro hac Ω _ μ _ W hW
    exact commonality_graphon hne hn4 hc hc1 hcrit ha0 hac hW

end CycleCommonality
