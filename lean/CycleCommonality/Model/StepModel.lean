import CycleCommonality.Spectral.RankOneTrace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The weighted step-graphon model

After the step-graphon reduction (`lem:step-reduction`) and the trace identity
(`lem:trace-density`), the proof of `adjacent_cycle_commonality.tex` is pure finite
symmetric-matrix theory.  This file fixes the finite model and the dictionary to the
operator statements of `Spectral/`.

A `StepGraphon N` is a finite measurable partition with weights `w` summing to `1` together with a
symmetric `[0,1]`-valued matrix `U` — the *complement* kernel `U = 1 - W` of the paper.  Following
the paper's `eq:trace-density`, the cycle densities are *defined* as traces:

```
  t(C_r, U) = Tr (T ^ r),        T i j = U i j √(w i) √(w j),
  t(C_r, W) = Tr ((P - T) ^ r),  P = rankOne u,  u i = √(w i).
```

`Graphon.lean` connects `Tr (T ^ r)` to the integral definition of homomorphism density; nothing
below depends on that.

The one structural fact making the model work is `compl_op`: `P - T` is exactly the operator of
the complement kernel, because `P` has matrix `√(w i) √(w j)`.
-/

namespace CycleCommonality

open Finset Matrix
open scoped RealInnerProductSpace

/-- A weighted step graphon: positive weights summing to one, and a symmetric `[0,1]`-valued
kernel matrix `U` (the paper's complement kernel `U = 1 - W`). -/
structure StepGraphon (N : ℕ) where
  /-- The cell weights. -/
  w : Fin N → ℝ
  /-- The kernel values. -/
  U : Fin N → Fin N → ℝ
  w_pos : ∀ i, 0 < w i
  w_sum : ∑ i, w i = 1
  U_symm : ∀ i j, U i j = U j i
  U_nonneg : ∀ i j, 0 ≤ U i j
  U_le_one : ∀ i j, U i j ≤ 1

namespace StepGraphon

variable {N : ℕ} (G : StepGraphon N)

/-- The vector `u i = √(w i)`; a unit vector since the weights sum to one. -/
noncomputable def unit : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun i => Real.sqrt (G.w i)

@[simp] lemma unit_apply (i : Fin N) : G.unit i = Real.sqrt (G.w i) := rfl

lemma unit_sq (i : Fin N) : G.unit i ^ 2 = G.w i := by
  rw [unit_apply, Real.sq_sqrt (G.w_pos i).le]

/-- The matrix of the kernel operator, `T i j = U i j √(w i) √(w j)`. -/
noncomputable def mat : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => G.U i j * Real.sqrt (G.w i) * Real.sqrt (G.w j)

/-- The matrix of the complement kernel operator. -/
noncomputable def matC : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (1 - G.U i j) * Real.sqrt (G.w i) * Real.sqrt (G.w j)

/-- The kernel operator on `EuclideanSpace ℝ (Fin N)`. -/
noncomputable def op : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
  Matrix.toEuclideanLin G.mat

lemma mat_symm (i j : Fin N) : G.mat i j = G.mat j i := by
  simp only [mat, Matrix.of_apply, G.U_symm i j]
  ring

lemma mat_isHermitian : Matrix.IsHermitian G.mat := by
  ext i j
  simpa [Matrix.conjTranspose_apply] using (G.mat_symm j i)

lemma op_isSymmetric : G.op.IsSymmetric := by
  rw [op]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr G.mat_isHermitian

/-! ### The dictionary -/

lemma inner_toEuclideanLin (M : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    ⟪v, Matrix.toEuclideanLin M v⟫ = ∑ i, ∑ j, v i * (M i j * v j) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrow : (Matrix.toEuclideanLin M v) i = ∑ j, M i j * v j := rfl
  rw [hrow, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `rankOne u` is the operator of the rank-one matrix `u i * u j`. -/
lemma rankOne_eq (u : EuclideanSpace ℝ (Fin N)) :
    rankOne u = Matrix.toEuclideanLin (Matrix.of fun i j => u i * u j) := by
  ext v i
  have hinner : (⟪u, v⟫ : ℝ) = ∑ j, u j * v j := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hl : (rankOne u v) i = (∑ j, u j * v j) * u i := by
    show (⟪u, v⟫ : ℝ) * u i = _
    rw [hinner]
  have hr : (Matrix.toEuclideanLin (Matrix.of fun i j => u i * u j) v) i
      = ∑ j, u i * u j * v j := rfl
  rw [hl, hr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`P - T` is the operator of the complement kernel.**  This is `eq:complement-operator`. -/
lemma compl_op : rankOne G.unit - G.op = Matrix.toEuclideanLin G.matC := by
  rw [rankOne_eq, op, ← map_sub]
  congr 1
  ext i j
  simp only [mat, matC, unit_apply, Matrix.sub_apply, Matrix.of_apply]
  ring

/-! ### Traces -/

/-- The trace of a matrix operator is the matrix trace. -/
lemma toMatrix_toEuclideanLin (M : Matrix (Fin N) (Fin N) ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (Matrix.toEuclideanLin M) = M := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

lemma toMatrix_pow (M : Matrix (Fin N) (Fin N) ℝ) (r : ℕ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (Matrix.toEuclideanLin M ^ r) = M ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih, toMatrix_toEuclideanLin]

/-- `Tr (T ^ r)` computed at the matrix level. -/
lemma trace_op_pow (r : ℕ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) (G.op ^ r) = Matrix.trace (G.mat ^ r) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis, op,
    toMatrix_pow]

/-- `Tr ((P - T) ^ r)` computed at the matrix level. -/
lemma trace_compl_pow (r : ℕ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) ((rankOne G.unit - G.op) ^ r)
      = Matrix.trace (G.matC ^ r) := by
  rw [compl_op, LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis,
    toMatrix_pow]

/-! ### Cycle densities -/

/-- The homomorphism density `t(C_r, U)` of `eq:trace-density`. -/
noncomputable def density (r : ℕ) : ℝ := Matrix.trace (G.mat ^ r)

/-- The homomorphism density `t(C_r, 1 - U)` of the complement. -/
noncomputable def densityCompl (r : ℕ) : ℝ := Matrix.trace (G.matC ^ r)

/-! ### The unit vector -/

lemma norm_unit : ‖G.unit‖ = 1 := by
  have h : ‖G.unit‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [← G.w_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← unit_sq G i]; ring
  have hnn : (0 : ℝ) ≤ ‖G.unit‖ := norm_nonneg _
  nlinarith [h, hnn]

lemma unit_ne_zero : G.unit ≠ 0 := by
  intro hcon
  have := G.norm_unit
  rw [hcon] at this
  simp at this

end StepGraphon

end CycleCommonality
