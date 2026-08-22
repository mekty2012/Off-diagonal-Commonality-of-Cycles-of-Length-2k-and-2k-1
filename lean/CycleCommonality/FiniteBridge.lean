import CycleCommonality.StepDensity
import CycleCommonality.Model.StepModel

/-!
# The finite model as a sum over closed walks

`StepDensity.lean` writes the cycle density of a step kernel as a sum over closed walks in the
cells.  `Model/StepModel.lean` defines the density of a weighted step graphon as `Tr(Tʳ)` with
`T i j = U i j √(wᵢ) √(wⱼ)`.  This file identifies the two, which lets the finite commonality
theorem be applied to the approximants produced by `Factored.lean`.

Two steps:

* `trace_pow_eq_sum_cycleProd` — the closed-walk expansion of a matrix power.  Mathlib has this
  only for adjacency matrices, so it is proved here; the combinatorics is the same as in
  `Fubini.lean` and its `chainProd`, `prod_path_eq_chainProd` and `cons_add_one` are reused
  verbatim, none of them using the measure.
* the telescoping `∏ᵢ √(w(uᵢ))·√(w(u_{i+1})) = ∏ᵢ w(uᵢ)`, by reindexing along the cyclic shift.
-/

open MeasureTheory CycleCommonality.Foundation Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CycleCommonality

universe u

/-! ### The closed-walk expansion of a matrix power -/

variable {N : ℕ}

/-- Powers of a matrix, entrywise, as a sum over paths. -/
theorem pow_apply_eq_sum_chainProd (T : Matrix (Fin N) (Fin N) ℝ) :
    ∀ (n : ℕ) (x y : Fin N),
      (T ^ (n + 1)) x y = ∑ w : Fin n → Fin N, chainProd (fun _ => T) x w y
  | 0, x, y => by simp [pow_one]
  | n + 1, x, y => by
      have hstep : (T ^ (n + 2)) x y = ∑ z, T x z * (T ^ (n + 1)) z y := by
        rw [pow_succ' T (n + 1)]
        rfl
      have hz : ∀ z : Fin N, T x z * (T ^ (n + 1)) z y
          = ∑ w : Fin n → Fin N, T x z * chainProd (fun _ => T) z w y := by
        intro z
        rw [pow_apply_eq_sum_chainProd T n z y, Finset.mul_sum]
      rw [hstep]
      simp_rw [hz]
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin N) _ _ fun p => ?_
      show T x p.1 * chainProd (fun _ => T) p.1 p.2 y
        = chainProd (fun _ => T) x (Fin.cons p.1 p.2) y
      rw [chainProd_succ]
      simp

/-- **The closed-walk expansion.**  `Tr(T^{n+1})` sums the products along all closed walks of
length `n+1`. -/
theorem trace_pow_eq_sum_cycleProd (T : Matrix (Fin N) (Fin N) ℝ) (n : ℕ) :
    Matrix.trace (T ^ (n + 1)) = ∑ v : Fin (n + 1) → Fin N, ∏ i, T (v i) (v (i + 1)) := by
  classical
  have hx : ∀ x : Fin N, (T ^ (n + 1)) x x
      = ∑ w : Fin n → Fin N, chainProd (fun _ => T) x w x :=
    fun x => pow_apply_eq_sum_chainProd T n x x
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [hx]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin N) _ _ fun p => ?_
  show chainProd (fun _ => T) p.1 p.2 p.1
    = ∏ i, T ((Fin.cons p.1 p.2 : Fin (n + 1) → Fin N) i)
        ((Fin.cons p.1 p.2 : Fin (n + 1) → Fin N) (i + 1))
  rw [← prod_path_eq_chainProd (fun _ => T) p.1 p.2 p.1]
  exact Finset.prod_congr rfl fun i _ => by rw [cons_add_one]

/-! ### The weighted model -/

/-- For a matrix of the model's shape, the closed-walk expansion telescopes: each vertex of the
walk contributes `√wᵢ` twice, once as a source and once as a target. -/
theorem trace_weighted_pow_eq_sum (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : Fin N → Fin N → ℝ) (n : ℕ) :
    Matrix.trace ((Matrix.of fun i j => A i j * Real.sqrt (w i) * Real.sqrt (w j)) ^ (n + 1))
      = ∑ v : Fin (n + 1) → Fin N, (∏ i, w (v i)) * ∏ i, A (v i) (v (i + 1)) := by
  rw [trace_pow_eq_sum_cycleProd]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h1 : (∏ i, (Matrix.of fun i j => A i j * Real.sqrt (w i) * Real.sqrt (w j))
        (v i) (v (i + 1)))
      = (∏ i, A (v i) (v (i + 1)))
        * ((∏ i, Real.sqrt (w (v i))) * ∏ i, Real.sqrt (w (v (i + 1)))) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      show A (v i) (v (i + 1)) * Real.sqrt (w (v i)) * Real.sqrt (w (v (i + 1))) = _
      ring
  have h2 : (∏ i, Real.sqrt (w (v (i + 1)))) = ∏ i, Real.sqrt (w (v i)) :=
    Fintype.prod_equiv (Equiv.addRight (1 : Fin (n + 1))) _ _ fun i => rfl
  have h3 : (∏ i, Real.sqrt (w (v i))) * (∏ i, Real.sqrt (w (v i))) = ∏ i, w (v i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Real.mul_self_sqrt (hw _)
  rw [h1, h2, h3]
  ring

/-- The density of a weighted step graphon is the sum over closed walks. -/
theorem StepGraphon.density_eq_sum (G : StepGraphon N) (n : ℕ) :
    G.density (n + 1)
      = ∑ v : Fin (n + 1) → Fin N, (∏ i, G.w (v i)) * ∏ i, G.U (v i) (v (i + 1)) :=
  trace_weighted_pow_eq_sum G.w (fun i => (G.w_pos i).le) G.U n

/-- The same for the complementary density. -/
theorem StepGraphon.densityCompl_eq_sum (G : StepGraphon N) (n : ℕ) :
    G.densityCompl (n + 1)
      = ∑ v : Fin (n + 1) → Fin N, (∏ i, G.w (v i)) * ∏ i, (1 - G.U (v i) (v (i + 1))) :=
  trace_weighted_pow_eq_sum G.w (fun i => (G.w_pos i).le) (fun i j => 1 - G.U i j) n

end CycleCommonality
