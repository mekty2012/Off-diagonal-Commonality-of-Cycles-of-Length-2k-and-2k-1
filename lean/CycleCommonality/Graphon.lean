import CycleCommonality.FiniteBridge
import CycleCommonality.Transfer
import CycleCommonality.Discrete

/-!
# The commonality theorem for arbitrary graphons

A step kernel carries the same data as a weighted step graphon: its cells are the fibres of `σ`
and their weights are the pushforward masses.  The one adjustment is that `StepGraphon` requires
strictly positive weights, so cells of measure zero are dropped — they contribute nothing to any
of the sums, and the surviving cells have nonempty fibres, which is what lets the matrix inherit
symmetry and the `[0,1]` bounds from the kernel.

With that, `Discrete.lower_bound` applies to every step graphon, and `commonality_of_stepKernel`
carries the inequality to every graphon.
-/

open MeasureTheory OddCycleBound Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Restricting a weighted sum over tuples to the cells of positive weight, and re-indexing them
by `Fin N`. -/
lemma sum_tuple_restrict {ι : Type u} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (F : ι → ι → ℝ)
    (S : Finset ι) (hS : ∀ i, i ∉ S → w i = 0) (e : Fin S.card ≃ {x // x ∈ S}) (r : ℕ) :
    ∑ u : Fin (r + 1) → ι, (∏ i, w (u i)) * ∏ i, F (u i) (u (i + 1))
      = ∑ v : Fin (r + 1) → Fin S.card,
          (∏ i, w ((e (v i) : ι))) * ∏ i, F ((e (v i) : ι)) ((e (v (i + 1)) : ι)) := by
  classical
  set f : (Fin (r + 1) → ι) → ℝ := fun u => (∏ i, w (u i)) * ∏ i, F (u i) (u (i + 1)) with hf
  set Φ : (Fin (r + 1) → Fin S.card) → (Fin (r + 1) → ι) := fun v i => (e (v i) : ι) with hΦ
  have hinj : ∀ v ∈ (Finset.univ : Finset (Fin (r + 1) → Fin S.card)),
      ∀ v' ∈ (Finset.univ : Finset (Fin (r + 1) → Fin S.card)), Φ v = Φ v' → v = v' := by
    intro v _ v' _ h
    funext i
    have : (e (v i) : ι) = (e (v' i) : ι) := congrFun h i
    exact e.injective (Subtype.ext this)
  have himg : ∑ u ∈ Finset.univ.image Φ, f u = ∑ v : Fin (r + 1) → Fin S.card, f (Φ v) :=
    Finset.sum_image hinj
  have hsub : ∑ u ∈ Finset.univ.image Φ, f u = ∑ u : Fin (r + 1) → ι, f u := by
    refine Finset.sum_subset (Finset.subset_univ _) fun u _ hu => ?_
    -- a tuple outside the image meets a cell of weight zero
    have hex : ∃ i, u i ∉ S := by
      by_contra hcon
      push Not at hcon
      refine hu (Finset.mem_image.2 ⟨fun i => e.symm ⟨u i, hcon i⟩, Finset.mem_univ _, ?_⟩)
      funext i
      show (e (e.symm ⟨u i, hcon i⟩) : ι) = u i
      rw [Equiv.apply_symm_apply]
    obtain ⟨i, hi⟩ := hex
    have : (∏ k, w (u k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hS _ hi)
    rw [hf]
    simp [this]
  rw [← hsub, himg]

/-- **A step kernel is a weighted step graphon.**  Both cycle densities agree with those of the
finite model. -/
theorem exists_stepGraphon_of_isStepKernel {V : Ω → Ω → ℝ} (hV : IsGraphon V μ)
    (hstep : IsStepKernel V) :
    ∃ (N : ℕ) (G : StepGraphon N), ∀ r : ℕ,
      cycleDensity V μ (r + 1) = G.density (r + 1) ∧
        cycleDensity (cmpl V) μ (r + 1) = G.densityCompl (r + 1) := by
  classical
  obtain ⟨ι, hfin, hms, hsing, σ, M, hσ, heq⟩ := hstep
  set ν : Measure ι := μ.map σ with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hσ.aemeasurable
  set w : ι → ℝ := fun i => ν.real {i} with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => measureReal_nonneg
  -- the cells carry all the mass
  have hwsum : ∑ i, w i = 1 := by
    have h := sum_measureReal_singleton (μ := ν) (Finset.univ : Finset ι)
    rw [Finset.coe_univ, probReal_univ] at h
    exact h
  set S : Finset ι := Finset.univ.filter fun i => w i ≠ 0 with hS
  have hSmem : ∀ i, i ∉ S → w i = 0 := by
    intro i hi
    by_contra hne
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩)
  set e : Fin S.card ≃ {x // x ∈ S} := (S.equivFin).symm with he
  -- every surviving cell has a representative, its fibre having positive measure
  have hrep : ∀ k : Fin S.card, ∃ x : Ω, σ x = (e k : ι) := by
    intro k
    have hpos : w (e k : ι) ≠ 0 := (Finset.mem_filter.1 (e k).2).2
    have hmeas : ν {(e k : ι)} ≠ 0 := by
      intro hzero
      refine hpos ?_
      show ν.real {(e k : ι)} = 0
      rw [measureReal_def, hzero, ENNReal.toReal_zero]
    have hne : (σ ⁻¹' {(e k : ι)}).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      refine hmeas ?_
      rw [hν, Measure.map_apply hσ (measurableSet_singleton _), hcon, measure_empty]
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx⟩
  choose rep hrep using hrep
  -- the cycle density of any kernel factoring through `σ`, restricted to the surviving cells
  have key : ∀ (Mx : ι → ι → ℝ) (Kx : Ω → Ω → ℝ), GoodK Kx →
      (∀ x y, Kx x y = Mx (σ x) (σ y)) → ∀ r : ℕ,
      cycleDensity Kx μ (r + 1)
        = ∑ v : Fin (r + 1) → Fin S.card, (∏ i, w ((e (v i) : ι)))
            * ∏ i, Mx ((e (v i) : ι)) ((e (v (i + 1)) : ι)) := by
    intro Mx Kx hKx hKeq r
    rw [cycleDensity_of_factored hKx hσ hKeq r]
    exact sum_tuple_restrict w Mx S hSmem e r
  refine ⟨S.card, ⟨fun k => w (e k : ι), fun k l => M (e k : ι) (e l : ι), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the surviving cells have positive weight
    intro k
    exact lt_of_le_of_ne (hw0 _) (Ne.symm (Finset.mem_filter.1 (e k).2).2)
  · -- and carry all the mass, the discarded ones having none
    have h1 : (∑ k : Fin S.card, w (e k : ι)) = ∑ x : {x // x ∈ S}, w (x : ι) :=
      Fintype.sum_equiv e _ _ fun k => rfl
    have h2 : (∑ x : {x // x ∈ S}, w (x : ι)) = ∑ i ∈ S, w i := Finset.sum_coe_sort S w
    have h3 : (∑ i ∈ S, w i) = ∑ i, w i :=
      Finset.sum_subset (Finset.subset_univ S) fun i _ hi => hSmem i hi
    rw [h1, h2, h3, hwsum]
  · intro k l
    rw [← hrep k, ← hrep l, ← heq, ← heq]
    exact hV.symm _ _
  · intro k l
    rw [← hrep k, ← hrep l, ← heq]
    exact hV.nonneg _ _
  · intro k l
    rw [← hrep k, ← hrep l, ← heq]
    exact hV.le_one _ _
  · intro r
    refine ⟨?_, ?_⟩
    · rw [key M V (goodK_of_isGraphon hV) heq r, StepGraphon.density_eq_sum]
    · refine (key (fun i j => 1 - M i j) (cmpl V) (goodK_cmpl hV) (fun x y => ?_) r).trans ?_
      · show 1 - V x y = 1 - M (σ x) (σ y)
        rw [heq]
      · rw [StepGraphon.densityCompl_eq_sum]

/-- **The commonality theorem for graphons.**  For every graphon on every probability space, up to
the critical point. -/
theorem commonality_graphon {n : ℕ} (hne : Even n) (hn4 : 4 ≤ n) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1) (hcrit : rho n c = twoCliqueValue n) (ha0 : 0 < a)
    (hac : a ≤ c) {W : Ω → Ω → ℝ} (hW : IsGraphon W μ) :
    rho n a ≤ cycleDensity (cmpl W) μ n + kappa n a * cycleDensity W μ (n + 1) := by
  have ha1 : a < 1 := lt_of_le_of_lt hac hc1
  have hn0 : (0 : ℕ) < n := by omega
  have hκ : 0 ≤ kappa n a := by
    rw [kappa]
    have h1 : (0 : ℝ) < a ^ (n - 1) := by positivity
    have h2 : (0 : ℝ) < (1 - a) ^ n := pow_pos (by linarith) n
    have h3 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    positivity
  refine commonality_of_stepKernel (by omega) hκ (fun V hV hstep => ?_) hW
  obtain ⟨N, G, hG⟩ := exists_stepGraphon_of_isStepKernel hV hstep
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(hG m).2, (hG (m + 1)).1]
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      have hsum := G.w_sum
      simp at hsum
    · exact h
  exact G.lower_bound hN hne hn4 hc hc1 hcrit ha0 hac


/-! ### The converse direction: a step graphon is a graphon -/

namespace StepGraphon

variable {N : ℕ} (G : StepGraphon N)

/-- The cells of a step graphon, weighted by `w`, as a probability space. -/
noncomputable def measure : Measure (Fin N) :=
  Measure.sum fun i => ENNReal.ofReal (G.w i) • Measure.dirac i

lemma measure_singleton (j : Fin N) : G.measure {j} = ENNReal.ofReal (G.w j) := by
  rw [measure, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  rw [tsum_eq_single j (fun i hi => ?_)]
  · simp
  · simp [Measure.smul_apply, hi]

instance : IsProbabilityMeasure G.measure := by
  constructor
  have huniv : G.measure Set.univ = ∑' i, ENNReal.ofReal (G.w i) := by
    rw [measure, Measure.sum_apply _ MeasurableSet.univ]
    simp
  rw [huniv, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (G.w_pos i).le), G.w_sum,
    ENNReal.ofReal_one]

lemma measureReal_singleton (j : Fin N) : G.measure.real {j} = G.w j := by
  rw [Measure.real, measure_singleton, ENNReal.toReal_ofReal (G.w_pos j).le]

/-- The kernel of a step graphon is a graphon on its space of cells. -/
lemma isGraphon : IsGraphon G.U G.measure where
  meas := Measurable.of_discrete
  nonneg := G.U_nonneg
  le_one := G.U_le_one
  symm := G.U_symm

/-- Both cycle densities of a step graphon are those of the graphon it realises. -/
lemma cycleDensity_eq (r : ℕ) :
    cycleDensity G.U G.measure (r + 1) = G.density (r + 1) ∧
      cycleDensity (cmpl G.U) G.measure (r + 1) = G.densityCompl (r + 1) := by
  have hid : Measurable (id : Fin N → Fin N) := measurable_id
  have hmap : G.measure.map id = G.measure := Measure.map_id
  constructor
  · rw [cycleDensity_of_factored (goodK_of_isGraphon G.isGraphon) hid (fun _ _ => rfl) r,
      StepGraphon.density_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by
      rw [hmap]
      exact congrArg (· * _) (Finset.prod_congr rfl fun i _ => G.measureReal_singleton _)
  · refine (cycleDensity_of_factored (M := fun i j => 1 - G.U i j) (goodK_cmpl G.isGraphon) hid
      (fun _ _ => rfl) r).trans ?_
    rw [StepGraphon.densityCompl_eq_sum]
    exact Finset.sum_congr rfl fun v _ => by
      rw [hmap]
      exact congrArg (· * _) (Finset.prod_congr rfl fun i _ => G.measureReal_singleton _)

end StepGraphon

end CycleCommonality
