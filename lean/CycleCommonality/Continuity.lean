import CycleCommonality.Fubini

/-!
# Cycle densities are Lipschitz in `L¹`

`|t(C_r, K) − t(C_r, K')| ≤ r · ‖K − K'‖₁` for kernels bounded by `1`, where

```
  ‖D‖₁ = ∫ x, ∫ y, |D x y| ∂μ ∂μ.
```

This is the estimate that lets an inequality proved for step graphons pass to an arbitrary graphon,
once the graphon is approximated in `L¹`.

The argument is not run under the `Ω^r` integral, where it would need the marginal of two
coordinates of a product measure.  It runs in the kernel algebra instead:

* `abs_compPow_le_one` — powers of a kernel bounded by `1` are bounded by `1`;
* `l1norm_compPow_sub_le` — `‖K^{∘n} − K'^{∘n}‖₁ ≤ (n+1)·‖K − K'‖₁`, by induction on the splitting
  `K^{∘(n+1)} − K'^{∘(n+1)} = (K − K') ∘ K^{∘n} + K' ∘ (K^{∘n} − K'^{∘n})`;
* `abs_cycleDensity_sub_le` — the trace written as a double integral, `trace (K^{∘n}) =
  ∫∫ K^{∘(n−1)}(x,y)·K(y,x)`, which is what converts the `L¹` bound into a bound on the trace.  The
  last step is needed because the diagonal `∫ Δ(x,x)` is *not* controlled by `∫∫|Δ|`.
-/

open MeasureTheory OddCycleBound

set_option linter.unusedSectionVars false

namespace CycleCommonality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The `L¹` norm of a kernel. -/
noncomputable def l1norm (μ : Measure Ω) (D : Ω → Ω → ℝ) : ℝ := ∫ x, ∫ y, |D x y| ∂μ ∂μ

lemma l1norm_nonneg (D : Ω → Ω → ℝ) : 0 ≤ l1norm μ D :=
  integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _

lemma goodK_abs {D : Ω → Ω → ℝ} (hD : GoodK D) : GoodK (fun x y => |D x y|) := by
  obtain ⟨C, hC0, hC⟩ := hD.bdd
  exact ⟨hD.meas.abs, C, hC0, fun x y => by rw [abs_abs]; exact hC x y⟩

lemma goodK_sub' {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    GoodK (fun x y => K x y - L x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  obtain ⟨C', hC0', hC'⟩ := hL.bdd
  refine ⟨hK.meas.sub hL.meas, C + C', by linarith, fun x y => ?_⟩
  have htri : |K x y - L x y| ≤ |K x y| + |L x y| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  exact htri.trans (add_le_add (hC x y) (hC' x y))

/-- Row sums of a bounded measurable kernel are measurable. -/
lemma rowsum_stronglyMeasurable {D : Ω → Ω → ℝ} (hD : GoodK D) :
    StronglyMeasurable (fun x => ∫ y, D x y ∂μ) :=
  (show StronglyMeasurable (Function.uncurry D) from
    hD.meas.stronglyMeasurable).integral_prod_right'

/-- Row sums of a bounded measurable kernel are integrable. -/
lemma rowsum_integrable {D : Ω → Ω → ℝ} (hD : GoodK D) :
    Integrable (fun x => ∫ y, D x y ∂μ) μ := by
  obtain ⟨C, _, hC⟩ := hD.bdd
  refine (integrable_const C).mono' (rowsum_stronglyMeasurable hD).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  calc |∫ y, D x y ∂μ| ≤ ∫ y, |D x y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, C ∂μ := integral_mono (hD.integrable_row x).abs (integrable_const C) (hC x)
    _ = C := by simp

/-- The `L¹` norm is subadditive. -/
lemma l1norm_add_le {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    l1norm μ (fun x y => A x y + B x y) ≤ l1norm μ A + l1norm μ B := by
  have h1 := rowsum_integrable (μ := μ) (goodK_abs hA)
  have h2 := rowsum_integrable (μ := μ) (goodK_abs hB)
  calc l1norm μ (fun x y => A x y + B x y)
      ≤ ∫ x, ((∫ y, |A x y| ∂μ) + ∫ y, |B x y| ∂μ) ∂μ := by
        refine integral_mono (rowsum_integrable (goodK_abs (goodK_add hA hB)))
          (h1.add h2) fun x => ?_
        rw [← integral_add ((goodK_abs hA).integrable_row x) ((goodK_abs hB).integrable_row x)]
        exact integral_mono ((goodK_abs (goodK_add hA hB)).integrable_row x)
          (((goodK_abs hA).integrable_row x).add ((goodK_abs hB).integrable_row x))
          (fun y => abs_add_le _ _)
    _ = l1norm μ A + l1norm μ B := integral_add h1 h2

/-- Both iterated integrals of `|D|` agree. -/
lemma l1norm_swap {D : Ω → Ω → ℝ} (hD : GoodK D) :
    l1norm μ D = ∫ y, ∫ x, |D x y| ∂μ ∂μ := by
  have hint : Integrable (Function.uncurry fun x y => |D x y|) (μ.prod μ) :=
    (goodK_abs hD).integrable_prod
  exact integral_integral_swap hint

/-! ### Powers of a contraction -/

lemma abs_compPow_le_one {K : Ω → Ω → ℝ} (hK : GoodK K) (hK1 : ∀ x y, |K x y| ≤ 1) :
    ∀ (n : ℕ) (x y : Ω), |compPow μ K n x y| ≤ 1
  | 0, x, y => hK1 x y
  | n + 1, x, y => by
      have hprev := abs_compPow_le_one hK hK1 n
      have hint : Integrable (fun z => K x z * compPow μ K n z y) μ :=
        integrable_KL hK (goodK_compPow hK n) x y
      show |∫ z, K x z * compPow μ K n z y ∂μ| ≤ 1
      calc |∫ z, K x z * compPow μ K n z y ∂μ|
          ≤ ∫ z, |K x z * compPow μ K n z y| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _z : Ω, (1 : ℝ) ∂μ := by
            refine integral_mono hint.abs (integrable_const 1) fun z => ?_
            rw [abs_mul]
            exact mul_le_one₀ (hK1 x z) (abs_nonneg _) (hprev z y)
        _ = 1 := by simp

/-! ### `L¹` bounds for a composition -/

/-- Composing on the right with a contraction does not increase the `L¹` norm. -/
lemma l1norm_comp_le_left {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L)
    (hL1 : ∀ x y, |L x y| ≤ 1) : l1norm μ (comp μ K L) ≤ l1norm μ K := by
  have hrow : ∀ x y : Ω, |comp μ K L x y| ≤ ∫ z, |K x z| ∂μ := by
    intro x y
    have hint : Integrable (fun z => K x z * L z y) μ := integrable_KL hK hL x y
    calc |comp μ K L x y| ≤ ∫ z, |K x z * L z y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, |K x z| ∂μ := by
          refine integral_mono hint.abs ((goodK_abs hK).integrable_row x) fun z => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hL1 z y)
  refine integral_mono (rowsum_integrable (goodK_abs (goodK_comp hK hL)))
    (rowsum_integrable (goodK_abs hK)) fun x => ?_
  calc (∫ y, |comp μ K L x y| ∂μ) ≤ ∫ _y : Ω, (∫ z, |K x z| ∂μ) ∂μ :=
        integral_mono ((goodK_abs (goodK_comp hK hL)).integrable_row x)
          (integrable_const _) (hrow x)
    _ = ∫ z, |K x z| ∂μ := by simp

/-- Composing on the left with a contraction does not increase the `L¹` norm. -/
lemma l1norm_comp_le_right {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L)
    (hK1 : ∀ x y, |K x y| ≤ 1) : l1norm μ (comp μ K L) ≤ l1norm μ L := by
  have hrow : ∀ x y : Ω, |comp μ K L x y| ≤ ∫ z, |L z y| ∂μ := by
    intro x y
    have hint : Integrable (fun z => K x z * L z y) μ := integrable_KL hK hL x y
    calc |comp μ K L x y| ≤ ∫ z, |K x z * L z y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, |L z y| ∂μ := by
          refine integral_mono hint.abs ((goodK_abs hL).integrable_col y) fun z => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hK1 x z)
  rw [l1norm_swap hL]
  have hstep : l1norm μ (comp μ K L) ≤ ∫ _x : Ω, (∫ y, ∫ z, |L z y| ∂μ ∂μ) ∂μ := by
    refine integral_mono (rowsum_integrable (goodK_abs (goodK_comp hK hL)))
      (integrable_const _) fun x => ?_
    exact integral_mono ((goodK_abs (goodK_comp hK hL)).integrable_row x)
      (goodK_abs hL).colsum_integrable (hrow x)
  simpa using hstep

/-! ### The telescoping estimate -/

/-- **The `L¹` estimate for kernel powers.** -/
lemma l1norm_compPow_sub_le {K K' : Ω → Ω → ℝ} (hK : GoodK K) (hK' : GoodK K')
    (hK1 : ∀ x y, |K x y| ≤ 1) (hK1' : ∀ x y, |K' x y| ≤ 1) :
    ∀ n : ℕ, l1norm μ (fun x y => compPow μ K n x y - compPow μ K' n x y)
      ≤ (n + 1) * l1norm μ (fun x y => K x y - K' x y)
  | 0 => by
      show l1norm μ (fun x y => K x y - K' x y)
        ≤ ((0 : ℕ) + 1 : ℝ) * l1norm μ (fun x y => K x y - K' x y)
      norm_num
  | n + 1 => by
      have hprev := l1norm_compPow_sub_le hK hK' hK1 hK1' n
      have hA := goodK_compPow (μ := μ) hK n
      have hA' := goodK_compPow (μ := μ) hK' n
      have hsplit : (fun x y => compPow μ K (n + 1) x y - compPow μ K' (n + 1) x y)
          = fun x y => comp μ (fun x y => K x y - K' x y) (compPow μ K n) x y
              + comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y) x y := by
        funext x y
        rw [comp_sub_left hK hK' hA, comp_sub_right hK' hA hA']
        show comp μ K (compPow μ K n) x y - comp μ K' (compPow μ K' n) x y = _
        ring
      rw [hsplit]
      have hb1 : l1norm μ (comp μ (fun x y => K x y - K' x y) (compPow μ K n))
          ≤ l1norm μ (fun x y => K x y - K' x y) :=
        l1norm_comp_le_left (goodK_sub' hK hK') hA (abs_compPow_le_one hK hK1 n)
      have hb2 : l1norm μ (comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y))
          ≤ l1norm μ (fun x y => compPow μ K n x y - compPow μ K' n x y) :=
        l1norm_comp_le_right hK' (goodK_sub' hA hA') hK1'
      have hadd : l1norm μ (fun x y =>
            comp μ (fun x y => K x y - K' x y) (compPow μ K n) x y
              + comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y) x y)
          ≤ l1norm μ (comp μ (fun x y => K x y - K' x y) (compPow μ K n))
            + l1norm μ (comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y)) :=
        l1norm_add_le (goodK_comp (goodK_sub' hK hK') hA)
          (goodK_comp hK' (goodK_sub' hA hA'))
      push_cast
      linarith [hadd, hb1, hb2, hprev]

/-! ### From the `L¹` bound to the trace -/

/-- `|trace (D ∘ A)| ≤ ‖D‖₁` when `A` is a contraction. -/
lemma abs_trace_comp_le_left {D A : Ω → Ω → ℝ} (hD : GoodK D) (hA : GoodK A)
    (hA1 : ∀ x y, |A x y| ≤ 1) : |trace μ (comp μ D A)| ≤ l1norm μ D := by
  have hrow : ∀ x : Ω, |∫ z, D x z * A z x ∂μ| ≤ ∫ z, |D x z| ∂μ := by
    intro x
    have hint : Integrable (fun z => D x z * A z x) μ := by
      obtain ⟨C, hC0, hC⟩ := hD.bdd
      refine Integrable.mono' ((hD.integrable_row x).abs.const_mul 1) ?_ ?_
      · exact (((hD.meas.comp measurable_prodMk_left)).mul
          ((hA.meas.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul, one_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hA1 z x)
    calc |∫ z, D x z * A z x ∂μ| ≤ ∫ z, |D x z * A z x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, |D x z| ∂μ := by
          refine integral_mono hint.abs ((goodK_abs hD).integrable_row x) fun z => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hA1 z x)
  calc |trace μ (comp μ D A)| ≤ ∫ x, |∫ z, D x z * A z x ∂μ| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ l1norm μ D := integral_mono (goodK_comp hD hA).diag_integrable.abs
        (rowsum_integrable (goodK_abs hD)) hrow

/-- `|trace (K ∘ D)| ≤ ‖D‖₁` when `K` is a contraction. -/
lemma abs_trace_comp_le_right {K D : Ω → Ω → ℝ} (hK : GoodK K) (hD : GoodK D)
    (hK1 : ∀ x y, |K x y| ≤ 1) : |trace μ (comp μ K D)| ≤ l1norm μ D := by
  have hrow : ∀ x : Ω, |∫ z, K x z * D z x ∂μ| ≤ ∫ z, |D z x| ∂μ := by
    intro x
    have hint : Integrable (fun z => K x z * D z x) μ := by
      refine Integrable.mono' ((hD.integrable_col x).abs.const_mul 1) ?_ ?_
      · exact (((hK.meas.comp measurable_prodMk_left)).mul
          ((hD.meas.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul, one_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hK1 x z)
    calc |∫ z, K x z * D z x ∂μ| ≤ ∫ z, |K x z * D z x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, |D z x| ∂μ := by
          refine integral_mono hint.abs ((goodK_abs hD).integrable_col x) fun z => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hK1 x z)
  have hswap : (∫ x, ∫ z, |D z x| ∂μ ∂μ) = l1norm μ D := (l1norm_swap hD).symm
  calc |trace μ (comp μ K D)| ≤ ∫ x, |∫ z, K x z * D z x ∂μ| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, ∫ z, |D z x| ∂μ ∂μ := integral_mono (goodK_comp hK hD).diag_integrable.abs
        (goodK_abs hD).colsum_integrable hrow
    _ = l1norm μ D := hswap

/-- **Cycle densities are `L¹`-Lipschitz.**  For kernels bounded by `1` and cycle length at least
two, `|t(C_r, K) − t(C_r, K')| ≤ r · ‖K − K'‖₁`. -/
theorem abs_cycleDensity_sub_le {K K' : Ω → Ω → ℝ} (hK : GoodK K) (hK' : GoodK K')
    (hK1 : ∀ x y, |K x y| ≤ 1) (hK1' : ∀ x y, |K' x y| ≤ 1) (n : ℕ) :
    |cycleDensity K μ (n + 2) - cycleDensity K' μ (n + 2)|
      ≤ (n + 2) * l1norm μ (fun x y => K x y - K' x y) := by
  have hA := goodK_compPow (μ := μ) hK n
  have hA' := goodK_compPow (μ := μ) hK' n
  have hsplit : cycleDensity K μ (n + 2) - cycleDensity K' μ (n + 2)
      = trace μ (comp μ (fun x y => K x y - K' x y) (compPow μ K n))
        + trace μ (comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y)) := by
    have e1 : comp μ (fun x y => K x y - K' x y) (compPow μ K n)
        = fun x y => comp μ K (compPow μ K n) x y - comp μ K' (compPow μ K n) x y :=
      comp_sub_left hK hK' hA
    have e2 : comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y)
        = fun x y => comp μ K' (compPow μ K n) x y - comp μ K' (compPow μ K' n) x y :=
      comp_sub_right hK' hA hA'
    rw [e1, e2, trace_sub (goodK_comp hK hA) (goodK_comp hK' hA),
      trace_sub (goodK_comp hK' hA) (goodK_comp hK' hA')]
    show trace μ (comp μ K (compPow μ K n)) - trace μ (comp μ K' (compPow μ K' n)) = _
    ring
  have hb1 : |trace μ (comp μ (fun x y => K x y - K' x y) (compPow μ K n))|
      ≤ l1norm μ (fun x y => K x y - K' x y) :=
    abs_trace_comp_le_left (goodK_sub' hK hK') hA (abs_compPow_le_one hK hK1 n)
  have hb2 : |trace μ (comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y))|
      ≤ l1norm μ (fun x y => compPow μ K n x y - compPow μ K' n x y) :=
    abs_trace_comp_le_right hK' (goodK_sub' hA hA') hK1'
  have hprev : l1norm μ (fun x y => compPow μ K n x y - compPow μ K' n x y)
      ≤ ((n : ℝ) + 1) * l1norm μ (fun x y => K x y - K' x y) :=
    l1norm_compPow_sub_le hK hK' hK1 hK1' n
  rw [hsplit]
  calc |trace μ (comp μ (fun x y => K x y - K' x y) (compPow μ K n))
          + trace μ (comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y))|
      ≤ |trace μ (comp μ (fun x y => K x y - K' x y) (compPow μ K n))|
        + |trace μ (comp μ K' (fun x y => compPow μ K n x y - compPow μ K' n x y))| :=
        abs_add_le _ _
    _ ≤ ((n : ℝ) + 2) * l1norm μ (fun x y => K x y - K' x y) := by linarith

end CycleCommonality
