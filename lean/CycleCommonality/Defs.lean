import CycleCommonality.Foundation.Kernel

/-!
# Graphons and their cycle densities

`Model/StepModel.lean` works with a finite weighted model, in which the cycle densities are
*defined* as traces of matrix powers.  This file gives the notions the theorem is about for an
arbitrary graphon on an arbitrary probability space `(Ω, μ)`.

`IsGraphon W μ` is in `Foundation/Graphon.lean`: symmetric, jointly measurable, `[0,1]`-valued.  The
kernel operations `comp`, `compPow` and `trace` are in `Foundation/Kernel.lean`.

`cycleDensity W μ r` is `t(C_r, W)`, in the form the argument runs in: a trace of a kernel power.
`Fubini.lean` proves it is the integral

```
  t(C_r, W) = ∫_{Ω^r} ∏_{i<r} W(x_i, x_{i+1}) dμ^{⊗r}        (indices cyclic),
```

which is the homomorphism-density definition used throughout this development.
-/

open MeasureTheory CycleCommonality.Foundation

set_option linter.unusedSectionVars false

namespace CycleCommonality

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The complementary graphon `1 − W`. -/
def cmpl (W : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => 1 - W x y

/-- `t(C_r, W)`: the cycle density of a kernel. -/
noncomputable def cycleDensity (W : Ω → Ω → ℝ) (μ : Measure Ω) (r : ℕ) : ℝ :=
  trace μ (compPow μ W (r - 1))

lemma cycleDensity_def (W : Ω → Ω → ℝ) (μ : Measure Ω) (r : ℕ) :
    cycleDensity W μ r = trace μ (compPow μ W (r - 1)) := rfl

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

lemma goodK_cmpl (hW : IsGraphon W μ) : GoodK (cmpl W) := by
  refine ⟨measurable_const.sub hW.meas, 1, zero_le_one, fun x y => ?_⟩
  have h0 := hW.nonneg x y
  have h1 := hW.le_one x y
  show |1 - W x y| ≤ 1
  rw [abs_le]
  constructor <;> linarith

lemma cmpl_cmpl (V : Ω → Ω → ℝ) : cmpl (cmpl V) = V := by
  funext x y
  show 1 - (1 - V x y) = V x y
  ring

/-- The complement of a graphon is a graphon. -/
lemma isGraphon_cmpl (hW : IsGraphon W μ) : IsGraphon (cmpl W) μ where
  meas := measurable_const.sub hW.meas
  nonneg := fun x y => by have := hW.le_one x y; show 0 ≤ 1 - W x y; linarith
  le_one := fun x y => by have := hW.nonneg x y; show 1 - W x y ≤ 1; linarith
  symm := fun x y => by show 1 - W x y = 1 - W y x; rw [hW.symm x y]

end CycleCommonality
