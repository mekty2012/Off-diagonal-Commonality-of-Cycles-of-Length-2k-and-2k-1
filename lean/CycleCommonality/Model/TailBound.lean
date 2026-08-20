import CycleCommonality.Model.StepModel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lemma `lem:spectral-budget`: Perron--Frobenius-type domination and the tail sum bound

For a weighted step graphon with eigenvalues `λ₀ ≥ λ₁ ≥ … ≥ λ_{N-1}` of the kernel operator:

```
  0 ≤ λ₀ ≤ 1,        |λ i| ≤ λ₀,        ∑_{i ≠ 0} λ i ^ 2 ≤ λ₀ (1 - λ₀) ≤ 1/4.
```

All three use only `0 ≤ U ≤ 1` pointwise; positive semidefiniteness is never assumed.

The paper's `|f|` — the pointwise absolute value of a step function, again a step function — is
here the coordinatewise `absVec`, and `eq:absolute-rayleigh` is `inner_absVec_ge`.  The
Cauchy–Schwarz step bounding `λ₀ ≤ 1` is `Finset.sum_mul_sq_le_sq_mul_sq` against the weights.
-/

namespace CycleCommonality

open Finset Matrix
open scoped RealInnerProductSpace

variable {N : ℕ}

/-! ### Coordinates on `EuclideanSpace` -/

lemma euclid_norm_sq (v : EuclideanSpace ℝ (Fin N)) : ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 :=
  norm_sq_eq_sum (EuclideanSpace.basisFun (Fin N) ℝ) v

/-- The coordinatewise absolute value; the paper's `|f|`. -/
noncomputable def absVec (v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun i => |v i|

@[simp] lemma absVec_apply (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) : absVec v i = |v i| := rfl

lemma norm_absVec (v : EuclideanSpace ℝ (Fin N)) : ‖absVec v‖ = ‖v‖ := by
  have h : ‖absVec v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [euclid_norm_sq, euclid_norm_sq]
    exact Finset.sum_congr rfl fun i _ => by rw [absVec_apply, sq_abs]
  have h1 : (0 : ℝ) ≤ ‖absVec v‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [h, h1, h2]

namespace StepGraphon

variable (G : StepGraphon N)

/-- The eigensystem of the kernel operator. -/
noncomputable def sys : EigenSystem N G.op :=
  EigenSystem.ofSymmetric G.op_isSymmetric finrank_euclideanSpace_fin

/-- The eigenvalues of the kernel operator, in nonincreasing order. -/
noncomputable def lam (i : Fin N) : ℝ := G.sys.val i

/-- The Perron eigenvalue `λ₀`. -/
noncomputable def perron (hN : 0 < N) : ℝ := G.lam ⟨0, hN⟩

/-- The edge density `s = ∫∫ U` of the paper. -/
noncomputable def edgeDensity : ℝ := ∑ i, ∑ j, G.U i j * G.w i * G.w j

/-! ### Coordinate formulas -/

lemma inner_op (v : EuclideanSpace ℝ (Fin N)) :
    ⟪v, G.op v⟫ = ∑ i, ∑ j, v i * (G.mat i j * v j) :=
  inner_toEuclideanLin G.mat v

lemma sqrt_w_sq (i : Fin N) : Real.sqrt (G.w i) * Real.sqrt (G.w i) = G.w i :=
  Real.mul_self_sqrt (G.w_pos i).le

lemma mat_nonneg (i j : Fin N) : 0 ≤ G.mat i j := by
  simp only [mat, Matrix.of_apply]
  have := G.U_nonneg i j
  positivity

/-- `⟪u, T u⟫` is the edge density. -/
lemma inner_op_unit : ⟪G.unit, G.op G.unit⟫ = G.edgeDensity := by
  rw [inner_op, edgeDensity]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mat, Matrix.of_apply, unit_apply]
  calc Real.sqrt (G.w i)
        * (G.U i j * Real.sqrt (G.w i) * Real.sqrt (G.w j) * Real.sqrt (G.w j))
      = G.U i j * (Real.sqrt (G.w i) * Real.sqrt (G.w i))
        * (Real.sqrt (G.w j) * Real.sqrt (G.w j)) := by ring
    _ = G.U i j * G.w i * G.w j := by rw [G.sqrt_w_sq i, G.sqrt_w_sq j]

lemma edgeDensity_nonneg : 0 ≤ G.edgeDensity := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have := G.U_nonneg i j
  have hi := (G.w_pos i).le
  have hj := (G.w_pos j).le
  positivity

/-! ### `λ₀ ≤ 1` -/

/-- The quadratic form is bounded by the squared norm.  This is the paper's
`⟨|f|, T|f|⟩ ≤ (∫|f|)² ≤ ‖f‖²`, with Cauchy–Schwarz against the weights. -/
lemma inner_op_le (v : EuclideanSpace ℝ (Fin N)) : ⟪v, G.op v⟫ ≤ ‖v‖ ^ 2 := by
  have hterm : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      v i * (G.mat i j * v j)
        ≤ (|v i| * Real.sqrt (G.w i)) * (|v j| * Real.sqrt (G.w j)) := by
    intro i _ j _
    have hwi : (0 : ℝ) ≤ Real.sqrt (G.w i) := Real.sqrt_nonneg _
    have hwj : (0 : ℝ) ≤ Real.sqrt (G.w j) := Real.sqrt_nonneg _
    have hU0 := G.U_nonneg i j
    have hU1 := G.U_le_one i j
    have hX : v i * (G.mat i j * v j)
        = G.U i j * ((v i * Real.sqrt (G.w i)) * (v j * Real.sqrt (G.w j))) := by
      simp only [mat, Matrix.of_apply]; ring
    have habs : |(v i * Real.sqrt (G.w i)) * (v j * Real.sqrt (G.w j))|
        = (|v i| * Real.sqrt (G.w i)) * (|v j| * Real.sqrt (G.w j)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwi, abs_of_nonneg hwj]
    rw [hX, ← habs]
    set X := (v i * Real.sqrt (G.w i)) * (v j * Real.sqrt (G.w j)) with hXdef
    nlinarith [le_abs_self X, neg_abs_le X, abs_nonneg X, hU0, hU1]
  have h1 : ⟪v, G.op v⟫
      ≤ ∑ i, ∑ j, (|v i| * Real.sqrt (G.w i)) * (|v j| * Real.sqrt (G.w j)) := by
    rw [inner_op]
    exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
  have h2 : ∑ i, ∑ j, (|v i| * Real.sqrt (G.w i)) * (|v j| * Real.sqrt (G.w j))
      = (∑ i, |v i| * Real.sqrt (G.w i)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have h3 : (∑ i, |v i| * Real.sqrt (G.w i)) ^ 2
      ≤ (∑ i, |v i| ^ 2) * ∑ i, Real.sqrt (G.w i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h4 : ∑ i, Real.sqrt (G.w i) ^ 2 = 1 := by
    rw [← G.w_sum]
    exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (G.w_pos i).le
  have h5 : ∑ i, |v i| ^ 2 = ‖v‖ ^ 2 := by
    rw [euclid_norm_sq]
    exact Finset.sum_congr rfl fun i _ => sq_abs _
  rw [h2] at h1
  rw [h4, mul_one, h5] at h3
  linarith

lemma inner_basis_eq (i : Fin N) : ⟪G.sys.basis i, G.op (G.sys.basis i)⟫ = G.lam i :=
  G.sys.inner_basis i

lemma perron_le_one (hN : 0 < N) : G.perron hN ≤ 1 := by
  have h := G.inner_op_le (G.sys.basis ⟨0, hN⟩)
  rw [G.inner_basis_eq ⟨0, hN⟩, G.sys.basis.norm_eq_one] at h
  simpa [perron] using h

/-! ### `λ₀ ≥ 0` and Perron--Frobenius-type domination -/

lemma edgeDensity_le_perron (hN : 0 < N) : G.edgeDensity ≤ G.perron hN := by
  have h := G.sys.rayleigh_top hN G.unit
  rw [G.inner_op_unit, G.norm_unit] at h
  simpa [perron, lam] using h

lemma perron_nonneg (hN : 0 < N) : 0 ≤ G.perron hN :=
  le_trans G.edgeDensity_nonneg (G.edgeDensity_le_perron hN)

/-- `eq:absolute-rayleigh`: the quadratic form only grows under coordinatewise absolute value,
because the kernel is nonnegative. -/
lemma inner_absVec_ge (v : EuclideanSpace ℝ (Fin N)) :
    |⟪v, G.op v⟫| ≤ ⟪absVec v, G.op (absVec v)⟫ := by
  rw [inner_op, inner_op]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [absVec_apply, absVec_apply, abs_mul, abs_mul, abs_of_nonneg (G.mat_nonneg i j)]

/-- **Perron--Frobenius-type domination** `eq:perron-domination`: `|λ i| ≤ λ₀`. -/
theorem abs_lam_le_perron (hN : 0 < N) (i : Fin N) : |G.lam i| ≤ G.perron hN := by
  have h1 := G.inner_absVec_ge (G.sys.basis i)
  have h2 : ⟪absVec (G.sys.basis i), G.op (absVec (G.sys.basis i))⟫
      ≤ G.perron hN * ‖absVec (G.sys.basis i)‖ ^ 2 := G.sys.rayleigh_top hN _
  rw [norm_absVec, G.sys.basis.norm_eq_one, one_pow, mul_one] at h2
  rw [G.inner_basis_eq i] at h1
  exact le_trans h1 h2

/-! ### The tail sum bound -/

lemma sum_sq_lam : ∑ i, (G.lam i) ^ 2 = ∑ i, ∑ j, (G.mat i j) ^ 2 := by
  have h : ∑ i, (G.lam i) ^ 2 = Matrix.trace (G.mat ^ 2) := by
    rw [show (∑ i, (G.lam i) ^ 2) = ∑ i, (G.sys.val i) ^ 2 from rfl,
      ← G.sys.trace_pow_eq_sum 2, G.trace_op_pow 2]
  rw [h, sq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← G.mat_symm i j]
  ring

lemma sum_sq_mat_le : ∑ i, ∑ j, (G.mat i j) ^ 2 ≤ G.edgeDensity := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hU0 := G.U_nonneg i j
  have hU1 := G.U_le_one i j
  have hwi := (G.w_pos i).le
  have hwj := (G.w_pos j).le
  have hexp : (G.mat i j) ^ 2 = G.U i j * G.U i j * (G.w i * G.w j) := by
    simp only [mat, Matrix.of_apply, sq]
    calc (G.U i j * Real.sqrt (G.w i) * Real.sqrt (G.w j))
          * (G.U i j * Real.sqrt (G.w i) * Real.sqrt (G.w j))
        = G.U i j * G.U i j * (Real.sqrt (G.w i) * Real.sqrt (G.w i))
          * (Real.sqrt (G.w j) * Real.sqrt (G.w j)) := by ring
      _ = G.U i j * G.U i j * (G.w i * G.w j) := by
          rw [G.sqrt_w_sq i, G.sqrt_w_sq j]; ring
  rw [hexp]
  have hsq : G.U i j * G.U i j ≤ G.U i j := by nlinarith [hU0, hU1]
  have hww : (0 : ℝ) ≤ G.w i * G.w j := mul_nonneg hwi hwj
  calc G.U i j * G.U i j * (G.w i * G.w j) ≤ G.U i j * (G.w i * G.w j) :=
        mul_le_mul_of_nonneg_right hsq hww
    _ = G.U i j * G.w i * G.w j := by ring

/-- **The tail sum bound** `eq:tail-square-budget`. -/
theorem tail_sum_bound (hN : 0 < N) :
    ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ 2
      ≤ G.perron hN * (1 - G.perron hN) := by
  classical
  have hsum : ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ 2
      = (∑ i, (G.lam i) ^ 2) - (G.perron hN) ^ 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rfl
  have h1 := G.sum_sq_lam
  have h2 := G.sum_sq_mat_le
  have h3 := G.edgeDensity_le_perron hN
  rw [hsum]
  nlinarith [h1, h2, h3]

/-- The tail sum bound in the numeric form used in Case 2: at most `1/4`. -/
theorem tail_sum_bound_quarter (hN : 0 < N) :
    ∑ i ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N), (G.lam i) ^ 2 ≤ 1 / 4 := by
  have h := G.tail_sum_bound hN
  nlinarith [h, sq_nonneg (G.perron hN - 1 / 2)]

end StepGraphon

end CycleCommonality
