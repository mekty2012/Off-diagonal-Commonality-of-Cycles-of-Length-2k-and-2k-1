import CycleCommonality.Factored

/-!
# Cycle densities of a step kernel are finite sums

For a kernel `K x y = M (σ x) (σ y)` factoring through a measurable map to a finite type, the
cyclic integral of `Fubini.lean` pushes forward along `σ`: the product measure `μ^{⊗r}` on `Ω^r`
becomes `ν^{⊗r}` on `ι^r`, where `ν = σ_*μ` gives the cell weights.  On a finite space an integral
is a sum, so

```
  t(C_r, K) = ∑_{u : Fin r → ι} (∏ᵢ ν{uᵢ}) · ∏ᵢ M(uᵢ, u_{i+1}),
```

which is the cycle density of the weighted step graphon with cells `σ⁻¹{i}` and matrix `M`.
-/

open MeasureTheory CycleCommonality.Foundation

set_option linter.unusedSectionVars false

noncomputable section

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The cycle density of a step kernel.**  A finite sum over closed walks in the cells, weighted
by the cell masses. -/
theorem cycleDensity_of_factored {K : Ω → Ω → ℝ} (hK : GoodK K)
    {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {σ : Ω → ι} {M : ι → ι → ℝ} (hσ : Measurable σ) (heq : ∀ x y, K x y = M (σ x) (σ y)) (n : ℕ) :
    cycleDensity K μ (n + 1)
      = ∑ u : Fin (n + 1) → ι,
          (∏ i, (μ.map σ).real {u i}) * ∏ i, M (u i) (u (i + 1)) := by
  classical
  set ν : Measure ι := μ.map σ with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hσ.aemeasurable
  set F : (Fin (n + 1) → ι) → ℝ := fun u => ∏ i, M (u i) (u (i + 1)) with hF
  have hFmeas : Measurable F := measurable_of_finite F
  have hpres : MeasurePreserving (fun (v : Fin (n + 1) → Ω) (i : Fin (n + 1)) => σ (v i))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => ν) :=
    measurePreserving_pi _ _ fun _ => ⟨hσ, rfl⟩
  -- the cyclic integral, with the integrand read through `σ`
  have hcyc : cycleDensity K μ (n + 1)
      = ∫ v : Fin (n + 1) → Ω, F (fun i => σ (v i)) ∂(Measure.pi fun _ => μ) := by
    rw [cycleDensity_eq_integral hK n]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    exact Finset.prod_congr rfl fun i _ => heq _ _
  -- push it forward to the finite space
  have hmap : ∫ u : Fin (n + 1) → ι, F u ∂(Measure.pi fun _ => ν)
      = ∫ v : Fin (n + 1) → Ω, F (fun i => σ (v i)) ∂(Measure.pi fun _ => μ) := by
    rw [← hpres.map_eq]
    exact integral_map hpres.measurable.aemeasurable hFmeas.aestronglyMeasurable
  rw [hcyc, ← hmap, integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsingle : (Measure.pi fun _ : Fin (n + 1) => ν) {u} = ∏ i, ν {u i} := by
    have huniv : ({u} : Set (Fin (n + 1) → ι)) = Set.univ.pi fun i => {u i} := by
      ext w
      constructor
      · rintro rfl
        exact fun i _ => rfl
      · intro hw
        funext i
        exact hw i (Set.mem_univ i)
    rw [huniv, Measure.pi_pi]
  rw [smul_eq_mul]
  congr 1
  rw [Measure.real, hsingle, ENNReal.toReal_prod]
  rfl

end CycleCommonality
