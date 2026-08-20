# Off-diagonal commonality of cycles of length 2k and 2k+1

For every even `n = 2k ≥ 4` there is a critical point `α*_n ∈ (1/2, 1)`, the unique solution of

```
  ρ_n(α) = 2^{1−n},        ρ_n(α) = α^{n−1}(α + n)/(n + 1),
```

such that for every graphon `W` on every probability space `(Ω, μ)` and every `a ∈ (0, α*_n]`

```
  t(C_n, 1−W) + κ_n(a) · t(C_{n+1}, W)  ≥  ρ_n(a),        κ_n(a) = n a^{n−1} / ((n+1)(1−a)^n),
```

while for `a > α*_n` the inequality already fails at the balanced two-clique.  So the commonality
region of the adjacent pair `(C_n, C_{n+1})` is exactly `(0, α*_n]`.  Here

```
  t(C_r, W) = ∫_{Ω^r} ∏_{i<r} W(x_i, x_{i+1}) dμ^{⊗r}        (indices read cyclically),
```

`W : Ω² → [0,1]` is symmetric and jointly measurable, and `(Ω, μ)` is an arbitrary probability
space — not `[0,1]`, not finite, not standard Borel, and `W` is not a step function.  The note
is `adjacent_cycle_commonality.pdf`; the Lean development is in `lean/`.

The results, all in `CycleCommonality`:

| | |
|---|---|
| `commonality_graphon` | the inequality, in the trace convention the proof runs in |
| `commonality_graphon_compl` | the same with `W` and `1−W` exchanged |
| `commonality_graphon_integral` | the inequality with both densities as integrals over `Ω^n` and `Ω^{n+1}` against the product measure, the form the note uses |
| `commonality_graphon_iff` | it holds for every graphon on every probability space **iff** `a ≤ α*_n` |
| `exists_unique_critical` | `α*_n` exists and is unique in `(1/2, 1)` |

## Building

Requires Lean `v4.31.0` (via `elan`); the pinned mathlib `v4.31.0` is fetched automatically.  In
`lean/`:

```
lake exe cache get                # download the prebuilt mathlib cache
lake build                        # builds everything; must end "Build completed successfully"
lake env lean CheckAxioms.lean    # axiom audit; see below
```

A clean build produces no warnings.

## Auditing the statement

The claim to check is that the Lean theorems say what the note says.  Five files, in this order —
nothing else needs to be read to establish it.

| Read | For |
|---|---|
| `lean/CycleCommonality/Main.lean` | the statements: lines 36, 44 and 58 |
| `lean/CycleCommonality/Defs.lean` | `cmpl` (32) and `cycleDensity` (35) |
| `lean/CycleCommonality/Scalar/Rho.lean` | `rho` (34), `kappa` (37), `twoCliqueValue` (190) |
| `lean/CycleCommonality/Foundation/Graphon.lean` | `IsGraphon`, line 35 — the hypothesis on `W` |
| `lean/CycleCommonality/Foundation/Kernel.lean` | `comp` (40), `compPow` (1432), `trace` (1445) |

These are the definitions the theorems are actually stated in; there is no separate summary to
trust.  Points worth checking explicitly:

* `IsGraphon W μ` asks only for joint measurability, symmetry and `0 ≤ W ≤ 1`.  `Ω` is an arbitrary
  `MeasurableSpace` with an `IsProbabilityMeasure`.
* `cycleDensity W μ r` is `trace (compPow W (r−1))`, the `(r−1)`-fold kernel composite traced;
  `Fubini.lean` line 273 (`cycleDensity_eq_integral`) proves it equals the integral over `Ω^r`,
  and that is the form `commonality_graphon_integral` is stated in.
* The critical point enters as a hypothesis `rho n c = twoCliqueValue n` together with
  `1/2 < c < 1`; `exists_unique_critical` (`StepTheorem.lean`, line 48) says exactly one `c`
  satisfies it, so the hypothesis pins `c = α*_n` rather than assuming anything about it.
* `commonality_graphon_iff` quantifies over the probability space as well as the graphon, so its
  forward direction is a genuine counterexample: `Graphon.lean` line 205
  (`StepGraphon.cycleDensity_eq`) realises the balanced two-clique as a graphon on a two-point
  space, whose densities are the ones `twoClique.violates` computes.

## Auditing the proof

`lake env lean CheckAxioms.lean` prints, for each named result, the axioms it depends on.  Every
line must read

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the standard classical axioms of mathlib.  Anything else — in particular
`sorryAx` — means something is unproved.  Equivalently: `grep -rn "sorry\|native_decide" lean/`
returns nothing, and `grep -rn "^axiom" lean/` returns nothing.

The development is laid out as follows.

```
lean/CycleCommonality.lean         index and architecture
lean/CycleCommonality/
  Defs.lean          the definitions the statement uses
  Main.lean          the theorem, in its three forms
  Graphon.lean       step kernels ↔ step graphons, and the theorem for all graphons
  StepTheorem.lean   the exact region, for step graphons
  Discrete.lean      the lower bound for a step graphon
  Extremal.lean      the balanced two-clique, where it is attained
  Fubini.lean        traces = integrals over Ω^r
  Continuity.lean    both densities are Lipschitz in L¹
  StepApprox.lean    an L¹ approximation by finite-rank kernels
  Factored.lean      those are step kernels, corrected into graphons
  StepDensity.lean   a step kernel's density is a finite sum over closed walks
  FiniteBridge.lean  so is Tr(T^r) for the finite model, and they agree
  Transfer.lean      an inequality for all step graphons holds for all graphons
  Scalar/            ρ_n, κ_n and the critical point
  Majorization/      Karamata, and the rank-one majorization
  Spectral/          the eigen-decomposition of the model's matrix
  Model/             the weighted step-graphon model and its spectral bounds
  Foundation/        kernel algebra and the L² operator of a kernel
```
