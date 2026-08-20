-- The definitions in the statement, and the theorem.
import CycleCommonality.Defs
import CycleCommonality.Main
-- The scalar functions ρ_n, κ_n and the critical point.
import CycleCommonality.Scalar.Rho
import CycleCommonality.Scalar.KappaBounds
-- Majorization and the spectral facts about the model's matrix.
import CycleCommonality.Majorization.Karamata
import CycleCommonality.Majorization.Bump
import CycleCommonality.Majorization.RankOne
import CycleCommonality.Spectral.Rayleigh
import CycleCommonality.Spectral.EigenSystem
import CycleCommonality.Spectral.Interlace
import CycleCommonality.Spectral.RankOneTrace
-- The finite model, and the exact region within it.
import CycleCommonality.Model.StepModel
import CycleCommonality.Model.TailBound
import CycleCommonality.Discrete
import CycleCommonality.Extremal
import CycleCommonality.StepTheorem
-- Cycle densities of a graphon, and the reduction to step graphons.
import CycleCommonality.Fubini
import CycleCommonality.Continuity
import CycleCommonality.StepApprox
import CycleCommonality.Factored
import CycleCommonality.StepDensity
import CycleCommonality.Transfer
import CycleCommonality.FiniteBridge
import CycleCommonality.Graphon

/-!
# The commonality region of adjacent cycles

The deliverable is `CycleCommonality.commonality_graphon_iff` in `Main.lean`: for even `n ≥ 4`
and `α*_n ∈ (1/2, 1)` the unique solution of `ρ_n(α*) = 2^{1−n}`, the scaled inequality

```
  t(C_n, 1−W) + κ_n(a) · t(C_{n+1}, W) ≥ ρ_n(a)
```

holds for **every** graphon `W` on **every** probability space `(Ω, μ)` if and only if
`a ≤ α*_n`.  `README.md` says how to build and how to audit.

## Reading the statement

Everything the theorem mentions is defined in `Defs.lean` — `cmpl` and `cycleDensity` — and in
`Scalar/Rho.lean` — `rho`, `kappa`, `twoCliqueValue` — on top of four notions taken from
`Foundation/`: `IsGraphon`, `comp`, `compPow` and `trace`.

`cycleDensity` is a trace of a kernel power, which is the form the proof runs in.  `Fubini.lean`
proves it is the integral of the source note,

```
  t(C_r, W) = ∫_{Ω^r} ∏_{i<r} W(x_i, x_{i+1}) dμ^{⊗r}        (indices read cyclically),
```

and `commonality_graphon_integral` states the theorem in that form.

## The two halves

**The finite model.**  `Model/StepModel.lean` fixes a weighted step graphon: positive weights `w`
summing to one and a symmetric `[0,1]`-valued matrix `U`, with the densities *defined* as traces
of powers of `T i j = U i j √(wᵢ) √(wⱼ)`.  Everything through `StepTheorem.lean` is finite
symmetric-matrix theory: the spectral decomposition of `T`, the rank-one majorization and Karamata
give `Discrete.lean`'s lower bound, and `Extremal.lean`'s balanced two-clique shows it is sharp.

**The reduction.**  `Fubini.lean` identifies the trace with the cyclic integral.  `Continuity.lean`
shows both densities are Lipschitz in `L¹`, `StepApprox.lean` approximates a graphon in `L¹` by a
finite-rank kernel, and `Factored.lean` repairs that into a step graphon; `Transfer.lean` then
carries any inequality of the theorem's shape from step graphons to all graphons.
`StepDensity.lean` and `FiniteBridge.lean` write both sides as sums over closed walks in the
cells, and `Graphon.lean` matches them, in both directions: a step kernel is a step graphon, and a
step graphon is a graphon on its own space of cells.

No cut metric, no regularity lemma and no compactness of the space of graphons appears anywhere;
the only approximation is of a single graphon, in `L¹`.
-/
