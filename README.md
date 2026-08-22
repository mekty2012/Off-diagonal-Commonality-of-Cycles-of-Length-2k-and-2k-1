# Commonality of a shorter even and a longer odd cycle

The parameter `d` below may be any positive odd integer.  Thus the result covers every pair
`(C_{2m}, C_{2k+1})` with `2m < 2k+1`.

Let `n ≥ 4` be even and let `d > 0` be odd, so the two cycle lengths are `n` and `n+d`.
There is a unique critical point `α*_{n,d} ∈ (1/2,1)` satisfying

```
  ρ_{n,d}(α) = 2^{1−n},
  ρ_{n,d}(α) = α^{n−1}(n+dα)/(n+d).
```

For every graphon `W` on every probability space `(Ω, μ)`, the scaled inequality

```
  t(C_n, 1−W) + κ_{n,d}(a) · t(C_{n+d}, W) ≥ ρ_{n,d}(a),
  κ_{n,d}(a) = n a^{n−1} / ((n+d)(1−a)^{n+d−1}),
```

holds exactly for `0 < a ≤ α*_{n,d}`.  Beyond the critical point it fails at the balanced
two-clique.  Here

```
  t(C_r, W) = ∫_{Ω^r} ∏_{i<r} W(x_i, x_{i+1}) dμ^{⊗r}        (indices read cyclically),
```

`W : Ω² → [0,1]` is symmetric and jointly measurable, and `(Ω, μ)` is an arbitrary probability
space — not `[0,1]`, not finite, not standard Borel, and `W` is not a step function.  The note is
`even_odd_cycle_commonality.pdf`; the Lean development is in `lean/`.

The results are in `CycleCommonality`:

| | |
|---|---|
| `commonality_graphon` | the graphon inequality for lengths `n` and `n+d` |
| `commonality_graphon_compl` | the same with `W` and `1−W` exchanged |
| `commonality_graphon_integral` | both densities written as product-measure integrals |
| `commonality_graphon_iff` | the inequality holds for every graphon **iff** `a ≤ α*_{n,d}` |
| `exists_unique_critical` | `α*_{n,d}` exists and is unique in `(1/2,1)` |

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

The claim to check is that the Lean theorems say what the note says.  Read these files in order.

| Read | For |
|---|---|
| `lean/CycleCommonality/Main.lean` | the graphon statements and exact region |
| `lean/CycleCommonality/Scalar/Rho.lean` | `rho`, `kappa`, the critical point and coefficient bounds |
| `lean/CycleCommonality/Defs.lean` | `cmpl` and `cycleDensity` |
| `lean/CycleCommonality/Foundation/Graphon.lean` | `IsGraphon` — the hypothesis on `W` |
| `lean/CycleCommonality/Foundation/Kernel.lean` | `comp`, `compPow`, and `trace` |

These are the definitions the theorems are actually stated in; there is no separate summary to
trust.  Points worth checking explicitly:

* `IsGraphon W μ` asks only for joint measurability, symmetry and `0 ≤ W ≤ 1`.  `Ω` is an arbitrary
  `MeasurableSpace` with an `IsProbabilityMeasure`.
* `cycleDensity W μ r` is `trace (compPow W (r−1))`, the `(r−1)`-fold kernel composite traced;
  `Fubini.lean` (`cycleDensity_eq_integral`) proves it equals the integral over `Ω^r`,
  and that is the form `commonality_graphon_integral` is stated in.
* The critical point enters as a hypothesis `rho n d c = twoCliqueValue n` together with
  `1/2 < c < 1`; `exists_unique_critical` says exactly one `c` satisfies it, so the
  hypothesis pins `c = α*_{n,d}` rather than assuming anything about it.
* `commonality_graphon_iff` quantifies over the probability space as well as the graphon, so its
  forward direction is a genuine counterexample: `Graphon.lean`
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
  Main.lean          exact graphon region, including the integral form
  Graphon.lean       step kernels ↔ step graphons, and the graphon lower bound
  StepTheorem.lean   the exact region for step graphons
  Discrete.lean      spectral reduction and finite lower bound for lengths n and n+d
  Extremal.lean      balanced two-clique calculations
  Fubini.lean        traces = integrals over Ω^r
  Continuity.lean    both densities are Lipschitz in L¹
  StepApprox.lean    an L¹ approximation by finite-rank kernels
  Factored.lean      those are step kernels, corrected into graphons
  StepDensity.lean   a step kernel's density is a finite sum over closed walks
  FiniteBridge.lean  so is Tr(T^r) for the finite model, and they agree
  Transfer.lean      an inequality for all step graphons holds for all graphons
  Scalar/            ρ_{n,d}, κ_{n,d}, the critical point, and the 5/14 bound
  Majorization/      Karamata, and the rank-one majorization
  Spectral/          the eigen-decomposition of the model's matrix
  Model/             the weighted step-graphon model and its spectral bounds
  Foundation/        kernel algebra and the L² operator of a kernel
```
