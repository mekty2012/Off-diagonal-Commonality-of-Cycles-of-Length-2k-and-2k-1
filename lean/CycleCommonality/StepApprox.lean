import CycleCommonality.Continuity
import CycleCommonality.Foundation.GraphonL2Operator

/-!
# Approximating a graphon by a step kernel

A *step kernel* is constant on the cells of `P × P` for a finite measurable partition `P` of `Ω`:
it is the same data as a weighted step graphon, with weights `μ (P i)`.

This file collects the operations that turn an arbitrary `L¹` approximation of a graphon into one
that is still a *graphon* — symmetric and `[0,1]`-valued — without losing accuracy:

* `l1norm_le_of_sq` — an `L²` bound gives an `L¹` bound, from the pointwise `|a| ≤ t + a²/t`;
* `abs_symmetrise_sub_le` — replacing `K` by `(K + Kᵀ)/2` does not increase the distance to a
  symmetric target;
* `abs_truncate_sub_le` — replacing `K` by `min (max K 0) 1` does not increase the distance to a
  `[0,1]`-valued target.

Both operations preserve being constant on the cells of `P × P`, so they turn a step kernel into a
step *graphon*.
-/

open MeasureTheory CycleCommonality.Foundation CycleCommonality.Foundation.Spectral.L2Kernel

set_option linter.unusedSectionVars false

namespace CycleCommonality

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `L²` controls `L¹` -/

/-- The elementary bound behind "an `L²` approximation is an `L¹` approximation":
`|a| ≤ t + a²/t` for every `t > 0`. -/
lemma abs_le_add_sq_div (a : ℝ) {t : ℝ} (ht : 0 < t) : |a| ≤ t + a ^ 2 / t := by
  rcases le_total |a| t with h | h
  · have hnn : 0 ≤ a ^ 2 / t := by positivity
    linarith
  · have h1 : |a| * t ≤ |a| * |a| := mul_le_mul_of_nonneg_left h (abs_nonneg a)
    have h2 : |a| ≤ a ^ 2 / t := by
      rw [le_div_iff₀ ht, ← sq_abs]
      nlinarith
    linarith

lemma integrable_sq_of_goodK {D : Ω → Ω → ℝ} (hD : GoodK D) :
    Integrable (fun p : Ω × Ω => (D p.1 p.2) ^ 2) (μ.prod μ) := by
  obtain ⟨C, hC0, hC⟩ := hD.bdd
  refine Integrable.mono' (integrable_const (C ^ 2))
    ((hD.meas.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC p.1 p.2) 2

/-- An `L²` bound gives an `L¹` bound: `‖D‖₁ ≤ t + ‖D‖₂²/t` for every `t > 0`. -/
lemma l1norm_le_of_sq {D : Ω → Ω → ℝ} (hD : GoodK D) {t : ℝ} (ht : 0 < t) :
    l1norm μ D ≤ t + (∫ p : Ω × Ω, (D p.1 p.2) ^ 2 ∂(μ.prod μ)) / t := by
  have hsq := integrable_sq_of_goodK (μ := μ) hD
  have hprod : (∫ p : Ω × Ω, |D p.1 p.2| ∂(μ.prod μ)) = l1norm μ D :=
    integral_prod _ (goodK_abs hD).integrable_prod
  rw [← hprod]
  calc (∫ p : Ω × Ω, |D p.1 p.2| ∂(μ.prod μ))
      ≤ ∫ p : Ω × Ω, (t + (D p.1 p.2) ^ 2 / t) ∂(μ.prod μ) :=
        integral_mono (goodK_abs hD).integrable_prod
          ((integrable_const t).add (hsq.div_const t))
          (fun p => abs_le_add_sq_div _ ht)
    _ = t + (∫ p : Ω × Ω, (D p.1 p.2) ^ 2 ∂(μ.prod μ)) / t := by
        rw [integral_add (integrable_const t) (hsq.div_const t), integral_div]
        simp

/-! ### Symmetrisation and truncation -/

/-- The symmetrisation of a kernel. -/
noncomputable def symmetrise (K : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => (K x y + K y x) / 2

/-- The truncation of a kernel to `[0,1]`. -/
noncomputable def truncate (K : Ω → Ω → ℝ) : Ω → Ω → ℝ := fun x y => min (max (K x y) 0) 1

lemma symmetrise_symm (K : Ω → Ω → ℝ) (x y : Ω) : symmetrise K x y = symmetrise K y x := by
  show (K x y + K y x) / 2 = (K y x + K x y) / 2
  ring

lemma truncate_nonneg (K : Ω → Ω → ℝ) (x y : Ω) : 0 ≤ truncate K x y :=
  le_min (le_max_right _ _) zero_le_one

lemma truncate_le_one (K : Ω → Ω → ℝ) (x y : Ω) : truncate K x y ≤ 1 := min_le_right _ _

lemma truncate_symm {K : Ω → Ω → ℝ} (hK : ∀ x y, K x y = K y x) (x y : Ω) :
    truncate K x y = truncate K y x := by
  show min (max (K x y) 0) 1 = min (max (K y x) 0) 1
  rw [hK x y]

lemma goodK_symmetrise {K : Ω → Ω → ℝ} (hK : GoodK K) : GoodK (symmetrise K) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  have hswap : Measurable (Function.uncurry fun x y => K y x) :=
    hK.meas.comp measurable_swap
  refine ⟨(hK.meas.add hswap).div_const 2, C, hC0, fun x y => ?_⟩
  show |(K x y + K y x) / 2| ≤ C
  rw [abs_div]
  have htri : |K x y + K y x| ≤ C + C := (abs_add_le _ _).trans (add_le_add (hC x y) (hC y x))
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  linarith

lemma goodK_truncate {K : Ω → Ω → ℝ} (hK : GoodK K) : GoodK (truncate K) := by
  refine ⟨(hK.meas.max measurable_const).min measurable_const, 1, zero_le_one, fun x y => ?_⟩
  rw [abs_le]
  exact ⟨by linarith [truncate_nonneg K x y], truncate_le_one K x y⟩

/-- Symmetrising moves a kernel no further from a symmetric target. -/
lemma abs_symmetrise_sub_le {K W : Ω → Ω → ℝ} (hW : ∀ x y, W x y = W y x) (x y : Ω) :
    |symmetrise K x y - W x y| ≤ (|K x y - W x y| + |K y x - W y x|) / 2 := by
  have hrw : symmetrise K x y - W x y = ((K x y - W x y) + (K y x - W y x)) / 2 := by
    show (K x y + K y x) / 2 - W x y = _
    rw [hW y x]
    ring
  rw [hrw, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  have := abs_add_le (K x y - W x y) (K y x - W y x)
  linarith

/-- Truncating moves a kernel no further from a `[0,1]`-valued target. -/
lemma abs_truncate_sub_le {K W : Ω → Ω → ℝ} (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x y, W x y ≤ 1)
    (x y : Ω) : |truncate K x y - W x y| ≤ |K x y - W x y| := by
  have h0 := hW0 x y
  have h1 := hW1 x y
  show |min (max (K x y) 0) 1 - W x y| ≤ |K x y - W x y|
  rcases le_total (K x y) 0 with hk | hk
  · have hmax : max (K x y) 0 = 0 := max_eq_right hk
    rw [hmax, min_eq_left zero_le_one]
    rw [abs_of_nonpos (by linarith : (0 : ℝ) - W x y ≤ 0),
      abs_of_nonpos (by linarith : K x y - W x y ≤ 0)]
    linarith
  · rcases le_total (K x y) 1 with hk1 | hk1
    · have hmax : max (K x y) 0 = K x y := max_eq_left hk
      rw [hmax, min_eq_left hk1]
    · have hmax : max (K x y) 0 = K x y := max_eq_left hk
      rw [hmax, min_eq_right hk1]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - W x y),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ K x y - W x y)]
      linarith

/-! ### The two repairs contract the `L¹` distance -/

/-- Truncation contracts the `L¹` distance to a `[0,1]`-valued target.  This one is pointwise. -/
lemma l1norm_truncate_sub_le {K W : Ω → Ω → ℝ} (hK : GoodK K) (hWg : GoodK W)
    (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x y, W x y ≤ 1) :
    l1norm μ (fun x y => W x y - truncate K x y) ≤ l1norm μ (fun x y => W x y - K x y) := by
  refine integral_mono (rowsum_integrable (goodK_abs (goodK_sub' hWg (goodK_truncate hK))))
    (rowsum_integrable (goodK_abs (goodK_sub' hWg hK))) fun x => ?_
  refine integral_mono ((goodK_abs (goodK_sub' hWg (goodK_truncate hK))).integrable_row x)
    ((goodK_abs (goodK_sub' hWg hK)).integrable_row x) fun y => ?_
  show |W x y - truncate K x y| ≤ |W x y - K x y|
  rw [abs_sub_comm (W x y) (truncate K x y), abs_sub_comm (W x y) (K x y)]
  exact abs_truncate_sub_le hW0 hW1 x y

/-- Symmetrisation contracts the `L¹` distance to a symmetric target.  Unlike truncation this is
not a pointwise bound: it holds only after integrating, because the `L¹` norm is invariant under
transposing the kernel. -/
lemma l1norm_symmetrise_sub_le {K W : Ω → Ω → ℝ} (hK : GoodK K) (hWg : GoodK W)
    (hWs : ∀ x y, W x y = W y x) :
    l1norm μ (fun x y => W x y - symmetrise K x y) ≤ l1norm μ (fun x y => W x y - K x y) := by
  set D : Ω → Ω → ℝ := fun x y => W x y - K x y with hDdef
  have hDg : GoodK D := goodK_sub' hWg hK
  have hSg : GoodK (fun x y => W x y - symmetrise K x y) := goodK_sub' hWg (goodK_symmetrise hK)
  have hpt : ∀ x y, |W x y - symmetrise K x y| ≤ (|D x y| + |D y x|) / 2 := by
    intro x y
    rw [abs_sub_comm]
    have h := abs_symmetrise_sub_le (K := K) hWs x y
    rw [abs_sub_comm (K x y) (W x y), abs_sub_comm (K y x) (W y x)] at h
    exact h
  have hsplit : ∀ x, (∫ y, (|D x y| + |D y x|) / 2 ∂μ)
      = ((∫ y, |D x y| ∂μ) + ∫ y, |D y x| ∂μ) / 2 := by
    intro x
    rw [integral_div, integral_add ((goodK_abs hDg).integrable_row x)
      ((goodK_abs hDg).integrable_col x)]
  have hint : Integrable (fun x => (∫ y, (|D x y| + |D y x|) / 2 ∂μ)) μ := by
    refine (Integrable.congr ?_ (Filter.Eventually.of_forall fun x => (hsplit x).symm))
    exact ((rowsum_integrable (goodK_abs hDg)).add
      (goodK_abs hDg).colsum_integrable).div_const 2
  calc l1norm μ (fun x y => W x y - symmetrise K x y)
      ≤ ∫ x, (∫ y, (|D x y| + |D y x|) / 2 ∂μ) ∂μ := by
        refine integral_mono (rowsum_integrable (goodK_abs hSg)) hint fun x => ?_
        refine integral_mono ((goodK_abs hSg).integrable_row x) ?_ (hpt x)
        exact (((goodK_abs hDg).integrable_row x).add
          ((goodK_abs hDg).integrable_col x)).div_const 2
    _ = ((∫ x, ∫ y, |D x y| ∂μ ∂μ) + ∫ x, ∫ y, |D y x| ∂μ ∂μ) / 2 := by
        rw [← integral_add (rowsum_integrable (goodK_abs hDg))
          (goodK_abs hDg).colsum_integrable, ← integral_div]
        exact integral_congr_ae (ae_of_all _ fun x => hsplit x)
    _ = l1norm μ D := by
        rw [← l1norm_swap hDg]
        show ((l1norm μ D) + l1norm μ D) / 2 = l1norm μ D
        ring

/-! ### `L²` approximation by a kernel with finite-range factors -/

/-- `(u + v)² ≤ 2u² + 2v²`. -/
lemma sq_add_le (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by nlinarith [sq_nonneg (u - v)]

/-- **The `L²` step.**  Every bounded measurable kernel is `L²`-approximated by one of the form
`∑ⱼ aⱼ(x)·bⱼ(y)` whose factors have finite range — that is, by a kernel constant on the cells of a
finite partition of `Ω`. -/
theorem exists_finiteRank_sq_close {K0 : Ω → Ω → ℝ} (hK0 : GoodK K0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (J : Type u) (_ : Fintype J) (K : Ω → Ω → ℝ) (a b : J → Ω → ℝ),
      GoodK K ∧ (∀ j, Good (a j)) ∧ (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧ (∀ j, (Set.range (b j)).Finite) ∧
      (∀ x y, K x y = ∑ j, a j x * b j y) ∧
      (∫ p : Ω × Ω, (K0 p.1 p.2 - K p.1 p.2) ^ 2 ∂(μ.prod μ)) < δ := by
  classical
  have hq0 : (0 : ℝ) < δ / 4 := by linarith
  -- a simple function within `L²` distance `√(δ/4)` of the kernel
  obtain ⟨S, hSlt, hSmem⟩ :=
    exists_simpleFunc_lpNorm_uncurry_sub_lt_of_goodK (mu := μ) hK0 (Real.sqrt_pos.mpr hq0)
  have haes : AEStronglyMeasurable (Function.uncurry K0 - ⇑S) (μ.prod μ) :=
    (goodK_memLp_prod_two (mu := μ) hK0).aestronglyMeasurable.sub hSmem.aestronglyMeasurable
  rw [lpNorm_two_eq_sqrt_integral_sq haes] at hSlt
  have hWS : (∫ p : Ω × Ω, (K0 p.1 p.2 - S p) ^ 2 ∂(μ.prod μ)) < δ / 4 := by
    set I : ℝ := ∫ p : Ω × Ω, (Function.uncurry K0 - ⇑S) p * (Function.uncurry K0 - ⇑S) p
      ∂(μ.prod μ) with hI
    have hI0 : 0 ≤ I := integral_nonneg fun p => mul_self_nonneg _
    have hIlt : I < δ / 4 := by
      by_contra hcon
      push Not at hcon
      exact absurd hSlt (not_lt.mpr (Real.sqrt_le_sqrt hcon))
    refine lt_of_le_of_lt (le_of_eq ?_) hIlt
    rw [hI]
    exact integral_congr_ae (ae_of_all _ fun p => by
      show (K0 p.1 p.2 - S p) ^ 2 = (K0 p.1 p.2 - S p) * (K0 p.1 p.2 - S p)
      ring)
  -- a rectangle-step function of the same `L²` accuracy
  set A : ℝ := ((SimpleFunc.range S).sum fun t => |t|) ^ 2 with hA
  set c : ℝ := ((SimpleFunc.range S).card : ℝ) with hc
  have hA0 : 0 ≤ A := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hpos : (0 : ℝ) < A * c + 1 := by positivity
  set η : ℝ := (δ / 4) / (A * c + 1) with hη
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨J, hJ, K, Bnd, a, b, hK, _hB0, _hKB, ha, hb, hfa, hfb, hsep, hSK⟩ :=
    exists_simpleFunc_rectangular_finiteRank_data_integral_sq_bound (Ω := Ω) μ S hη0
  refine ⟨J, hJ, K, a, b, hK, ha, hb, hfa, hfb, hsep, ?_⟩
  have hSK' : (∫ p : Ω × Ω, (S p - K p.1 p.2) ^ 2 ∂(μ.prod μ)) < δ / 4 := by
    refine lt_of_le_of_lt hSK ?_
    have hform : ((SimpleFunc.range S).sum fun t => |t|) ^ 2 * (c * η) = (A * c) * η := by
      rw [hA]; ring
    have hbound : (A * c) * η < δ / 4 := by
      rw [hη, mul_div_assoc', div_lt_iff₀ hpos]
      nlinarith
    calc ((SimpleFunc.range S).sum fun t => |t|) ^ 2 * (((SimpleFunc.range S).card : ℝ) * η)
        = (A * c) * η := by rw [← hc]; exact hform
      _ < δ / 4 := hbound
  -- combine the two errors
  have hint1 : Integrable (fun p : Ω × Ω => (K0 p.1 p.2 - S p) ^ 2) (μ.prod μ) := by
    have h1 : MemLp (fun p : Ω × Ω => K0 p.1 p.2 - S p) 2 (μ.prod μ) :=
      (goodK_memLp_prod_two (mu := μ) hK0).sub hSmem
    simpa [sq] using h1.integrable_sq
  have hint2 : Integrable (fun p : Ω × Ω => (S p - K p.1 p.2) ^ 2) (μ.prod μ) := by
    have h2 : MemLp (fun p : Ω × Ω => S p - K p.1 p.2) 2 (μ.prod μ) :=
      hSmem.sub (goodK_memLp_prod_two (mu := μ) hK)
    simpa [sq] using h2.integrable_sq
  calc (∫ p : Ω × Ω, (K0 p.1 p.2 - K p.1 p.2) ^ 2 ∂(μ.prod μ))
      ≤ ∫ p : Ω × Ω, (2 * (K0 p.1 p.2 - S p) ^ 2 + 2 * (S p - K p.1 p.2) ^ 2) ∂(μ.prod μ) := by
        refine integral_mono (integrable_sq_of_goodK (μ := μ) (goodK_sub' hK0 hK))
          ((hint1.const_mul 2).add (hint2.const_mul 2)) fun p => ?_
        have hle := sq_add_le (K0 p.1 p.2 - S p) (S p - K p.1 p.2)
        have hrw : K0 p.1 p.2 - K p.1 p.2 = (K0 p.1 p.2 - S p) + (S p - K p.1 p.2) := by ring
        rw [hrw]
        exact hle
    _ < δ := by
        rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2), integral_const_mul,
          integral_const_mul]
        linarith

/-- **The `L¹` step.**  Every bounded measurable kernel is `L¹`-approximated by one whose factors
have finite range. -/
theorem exists_finiteRank_l1_close {K0 : Ω → Ω → ℝ} (hK0 : GoodK K0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (J : Type u) (_ : Fintype J) (K : Ω → Ω → ℝ) (a b : J → Ω → ℝ),
      GoodK K ∧ (∀ j, Good (a j)) ∧ (∀ j, Good (b j)) ∧
      (∀ j, (Set.range (a j)).Finite) ∧ (∀ j, (Set.range (b j)).Finite) ∧
      (∀ x y, K x y = ∑ j, a j x * b j y) ∧
      l1norm μ (fun x y => K0 x y - K x y) < ε := by
  have hδ : 0 < ε ^ 2 / 8 := by positivity
  obtain ⟨J, hJ, K, a, b, hK, ha, hb, hfa, hfb, hsep, hsq⟩ :=
    exists_finiteRank_sq_close (μ := μ) hK0 hδ
  refine ⟨J, hJ, K, a, b, hK, ha, hb, hfa, hfb, hsep, ?_⟩
  have ht : (0 : ℝ) < ε / 4 := by linarith
  have hbound := l1norm_le_of_sq (μ := μ) (goodK_sub' hK0 hK) ht
  have hdiv : (∫ p : Ω × Ω, ((fun x y => K0 x y - K x y) p.1 p.2) ^ 2 ∂(μ.prod μ)) / (ε / 4)
      < ε / 2 := by
    rw [div_lt_iff₀ ht]
    calc (∫ p : Ω × Ω, ((fun x y => K0 x y - K x y) p.1 p.2) ^ 2 ∂(μ.prod μ))
        < ε ^ 2 / 8 := hsq
      _ = ε / 2 * (ε / 4) := by ring
  linarith
