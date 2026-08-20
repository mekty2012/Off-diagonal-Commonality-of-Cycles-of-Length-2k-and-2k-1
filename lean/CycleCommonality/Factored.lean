import CycleCommonality.StepApprox

/-!
# Step kernels, as kernels that factor through a finite map

A *step kernel* is one of the form `K x y = M (σ x) (σ y)` for a measurable `σ : Ω → ι` with `ι`
finite.  The fibres of `σ` are the cells of a finite measurable partition of `Ω` and `M` is the
matrix of values, so this is the same data as a weighted step graphon — with the advantage that no
disjointness or covering conditions have to be carried: the fibres of a function partition its
domain automatically.

The two facts proved here:

* `isStepKernel_of_finiteRank` — a kernel `∑ⱼ aⱼ(x)·bⱼ(y)` whose factors have finite range is a
  step kernel, which is what turns the `L¹` approximation of `StepApprox.lean` into one;
* `IsStepKernel.symmetrise`, `IsStepKernel.truncate` — the two repairs that make an approximant a
  graphon again act on `M`, so they preserve the property.

Cycle densities of a step kernel are finite sums: pushing the cyclic integral of `Fubini.lean`
forward along `σ` replaces `μ^{⊗r}` by `(σ_*μ)^{⊗r}` on the finite type `ι`.
-/

open MeasureTheory OddCycleBound

set_option linter.unusedSectionVars false

noncomputable section

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `K` factors through a measurable map to a finite type. -/
def IsStepKernel (K : Ω → Ω → ℝ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
    (σ : Ω → ι) (M : ι → ι → ℝ), Measurable σ ∧ ∀ x y, K x y = M (σ x) (σ y)

/-- A kernel with finitely many separated factors of finite range is a step kernel: the point's
*signature*, the tuple of all the factor values at it, takes finitely many values, and the kernel
depends on its two arguments only through their signatures. -/
theorem isStepKernel_of_finiteRank {J : Type u} [Fintype J] {K : Ω → Ω → ℝ} {a b : J → Ω → ℝ}
    (ha : ∀ j, Good (a j)) (hb : ∀ j, Good (b j))
    (hfa : ∀ j, (Set.range (a j)).Finite) (hfb : ∀ j, (Set.range (b j)).Finite)
    (hsep : ∀ x y, K x y = ∑ j, a j x * b j y) : IsStepKernel K := by
  classical
  set φ : Ω → (J → ℝ) × (J → ℝ) := fun x => (fun j => a j x, fun j => b j x) with hφ
  have hφmeas : Measurable φ :=
    (measurable_pi_lambda _ fun j => (ha j).meas.measurable).prodMk
      (measurable_pi_lambda _ fun j => (hb j).meas.measurable)
  have hrange : (Set.range φ).Finite := by
    refine Set.Finite.subset (Set.Finite.prod (Set.Finite.pi fun j => hfa j)
      (Set.Finite.pi fun j => hfb j)) ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun j _ => Set.mem_range_self x, fun j _ => Set.mem_range_self x⟩
  exact ⟨↥(Set.range φ), hrange.fintype, inferInstance, inferInstance,
    fun x => ⟨φ x, Set.mem_range_self x⟩,
    fun p q => ∑ j, (p : (J → ℝ) × (J → ℝ)).1 j * (q : (J → ℝ) × (J → ℝ)).2 j,
    hφmeas.subtype_mk, fun x y => hsep x y⟩

/-! ### The two repairs preserve the property -/

theorem IsStepKernel.symmetrise {K : Ω → Ω → ℝ} (hK : IsStepKernel K) :
    IsStepKernel (symmetrise K) := by
  obtain ⟨ι, hfin, hms, hsing, σ, M, hσ, heq⟩ := hK
  exact ⟨ι, hfin, hms, hsing, σ, fun i j => (M i j + M j i) / 2, hσ, fun x y => by
    show (K x y + K y x) / 2 = _
    rw [heq x y, heq y x]⟩

theorem IsStepKernel.truncate {K : Ω → Ω → ℝ} (hK : IsStepKernel K) :
    IsStepKernel (truncate K) := by
  obtain ⟨ι, hfin, hms, hsing, σ, M, hσ, heq⟩ := hK
  exact ⟨ι, hfin, hms, hsing, σ, fun i j => min (max (M i j) 0) 1, hσ, fun x y => by
    show min (max (K x y) 0) 1 = _
    rw [heq x y]⟩

/-! ### The approximation, repaired into a graphon -/

/-- **Every graphon is an `L¹` limit of step graphons over the same probability space.**

The approximant is symmetric, `[0,1]`-valued and constant on the cells of a finite measurable
partition — that is, a step graphon — and no compactness, cut metric or regularity is used. -/
theorem exists_stepGraphon_l1_close {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Ω → Ω → ℝ, IsGraphon V μ ∧ IsStepKernel V ∧
      l1norm μ (fun x y => W x y - V x y) < ε := by
  classical
  obtain ⟨J, hJ, K, a, b, hK, ha, hb, hfa, hfb, hsep, hclose⟩ :=
    exists_finiteRank_l1_close (μ := μ) (goodK_of_isGraphon hW) hε
  have hstep : IsStepKernel K := isStepKernel_of_finiteRank ha hb hfa hfb hsep
  refine ⟨truncate (symmetrise K), ?_, (hstep.symmetrise).truncate, ?_⟩
  · -- the repaired kernel is a graphon
    exact
      { meas := (goodK_truncate (goodK_symmetrise hK)).meas
        nonneg := fun x y => truncate_nonneg _ x y
        le_one := fun x y => truncate_le_one _ x y
        symm := fun x y => truncate_symm (symmetrise_symm K) x y }
  · -- and it is no further from `W` than `K` was
    calc l1norm μ (fun x y => W x y - truncate (symmetrise K) x y)
        ≤ l1norm μ (fun x y => W x y - symmetrise K x y) :=
          l1norm_truncate_sub_le (goodK_symmetrise hK) (goodK_of_isGraphon hW)
            (fun x y => hW.nonneg x y) (fun x y => hW.le_one x y)
      _ ≤ l1norm μ (fun x y => W x y - K x y) :=
          l1norm_symmetrise_sub_le hK (goodK_of_isGraphon hW) (fun x y => hW.symm x y)
      _ < ε := hclose

end CycleCommonality
