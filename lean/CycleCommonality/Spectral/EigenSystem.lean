import CycleCommonality.Spectral.Rayleigh

/-!
# Eigensystems, and the Rayleigh bounds relative to one

An `EigenSystem N T` packages an orthonormal basis of eigenvectors of `T` together with the
corresponding eigenvalues, listed in nonincreasing order.  Mathlib's
`hT.eigenvectorBasis`/`hT.eigenvalues` provide one (`EigenSystem.ofSymmetric`).

The abstraction makes it convenient to apply majorization to `A = -T`, whose eigenvalues are the
negated, *reversed*
eigenvalues of `T`.  Identifying `(-T).eigenvalues` with `fun i => -(T.eigenvalues i.rev)` would
need a uniqueness theorem for sorted eigenvalue lists, which Mathlib does not have.  With an
eigensystem the passage to `-T` is one line: reverse the basis and negate (`EigenSystem.neg`).

Main results:

* `EigenSystem.ofSymmetric`, `EigenSystem.neg` — the two constructions;
* `EigenSystem.rayleigh_ge`, `EigenSystem.rayleigh_le` — the Rayleigh bounds on `spectralSpan`;
* `EigenSystem.trace_eq_sum`, `EigenSystem.trace_pow_eq_sum` — traces of `T` and of `T ^ n`.
-/

namespace CycleCommonality

open Finset Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- `‖v‖ ^ 2` is the sum of the squared coordinates of `v`. -/
lemma norm_sq_eq_sum (b : OrthonormalBasis (Fin N) ℝ E) (v : E) :
    ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
  rw [← b.sum_sq_norm_inner_right v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← b.repr_apply_apply, Real.norm_eq_abs, sq_abs]

omit [FiniteDimensional ℝ E] in
/-- The trace of an operator is the sum of its diagonal entries in any orthonormal basis. -/
lemma trace_eq_sum_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T = ∑ i, ⟪b i, T (b i)⟫ := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis T]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]

/-- An orthonormal eigenbasis of `T` together with its eigenvalues in nonincreasing order. -/
structure EigenSystem (N : ℕ) (T : E →ₗ[ℝ] E) where
  /-- The orthonormal basis of eigenvectors. -/
  basis : OrthonormalBasis (Fin N) ℝ E
  /-- The eigenvalues, in nonincreasing order. -/
  val : Fin N → ℝ
  /-- `T` is symmetric. -/
  symm : T.IsSymmetric
  /-- The basis really is an eigenbasis. -/
  apply_basis : ∀ i, T (basis i) = val i • basis i
  /-- The eigenvalues are listed in nonincreasing order. -/
  antitone : Antitone val

namespace EigenSystem

variable {T : E →ₗ[ℝ] E}

/-- Mathlib's sorted spectral decomposition of a symmetric operator. -/
noncomputable def ofSymmetric (hT : T.IsSymmetric) (hn : finrank ℝ E = N) : EigenSystem N T where
  basis := hT.eigenvectorBasis hn
  val := hT.eigenvalues hn
  symm := hT
  apply_basis := fun i => by simp
  antitone := hT.eigenvalues_antitone hn

@[simp] lemma ofSymmetric_val (hT : T.IsSymmetric) (hn : finrank ℝ E = N) :
    (ofSymmetric hT hn).val = hT.eigenvalues hn := rfl

@[simp] lemma ofSymmetric_basis (hT : T.IsSymmetric) (hn : finrank ℝ E = N) :
    (ofSymmetric hT hn).basis = hT.eigenvectorBasis hn := rfl

/-- Negating the operator reverses the eigenbasis and negates the eigenvalues.  This is the step
that lets the majorization lemma be applied to `A = -T` for free. -/
noncomputable def neg (S : EigenSystem N T) : EigenSystem N (-T) where
  basis := S.basis.reindex (Fin.revPerm : Equiv.Perm (Fin N))
  val := fun i => -(S.val i.rev)
  symm := by
    intro x y
    simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, S.symm x y]
  apply_basis := by
    intro i
    have hb : (S.basis.reindex (Fin.revPerm : Equiv.Perm (Fin N))) i = S.basis i.rev := by
      simp [OrthonormalBasis.reindex_apply]
    rw [hb, LinearMap.neg_apply, S.apply_basis i.rev, neg_smul]
  antitone := by
    intro i j hij
    simpa using S.antitone (Fin.rev_le_rev.mpr hij)

omit [FiniteDimensional ℝ E] in
@[simp] lemma neg_val (S : EigenSystem N T) (i : Fin N) : S.neg.val i = -(S.val i.rev) := rfl

/-! ### Coordinates -/

omit [FiniteDimensional ℝ E] in
/-- In the eigenbasis, `T` acts diagonally. -/
lemma repr_apply (S : EigenSystem N T) (v : E) (i : Fin N) :
    S.basis.repr (T v) i = S.val i * S.basis.repr v i := by
  rw [S.basis.repr_apply_apply, ← S.symm (S.basis i) v, S.apply_basis i,
    real_inner_smul_left, S.basis.repr_apply_apply]

omit [FiniteDimensional ℝ E] in
/-- `⟪v, T v⟫` is the eigenvalue-weighted sum of the squared eigencoordinates of `v`. -/
lemma inner_apply_eq_sum (S : EigenSystem N T) (v : E) :
    ⟪v, T v⟫ = ∑ i, S.val i * (S.basis.repr v i) ^ 2 := by
  rw [← S.basis.sum_inner_mul_inner v (T v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪v, S.basis i⟫ = S.basis.repr v i := by
    rw [S.basis.repr_apply_apply]; exact real_inner_comm _ _
  have h2 : ⟪S.basis i, T v⟫ = S.val i * S.basis.repr v i := by
    rw [← S.basis.repr_apply_apply, S.repr_apply v i]
  rw [h1, h2]
  ring

/-! ### The Rayleigh bounds -/

omit [FiniteDimensional ℝ E] in
/-- On the span of the eigenvectors indexed by `F`, the quadratic form is bounded below by any
lower bound for the eigenvalues indexed by `F`. -/
lemma rayleigh_ge (S : EigenSystem N T) {F : Finset (Fin N)} {c : ℝ}
    (hF : ∀ j ∈ F, c ≤ S.val j) {v : E} (hv : v ∈ spectralSpan S.basis F) :
    c * ‖v‖ ^ 2 ≤ ⟪v, T v⟫ := by
  classical
  rw [S.inner_apply_eq_sum v, norm_sq_eq_sum S.basis v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ F
  · exact mul_le_mul_of_nonneg_right (hF i hi) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_spectralSpan hv hi]
    simp

omit [FiniteDimensional ℝ E] in
/-- On the span of the eigenvectors indexed by `F`, the quadratic form is bounded above by any
upper bound for the eigenvalues indexed by `F`. -/
lemma rayleigh_le (S : EigenSystem N T) {F : Finset (Fin N)} {c : ℝ}
    (hF : ∀ j ∈ F, S.val j ≤ c) {v : E} (hv : v ∈ spectralSpan S.basis F) :
    ⟪v, T v⟫ ≤ c * ‖v‖ ^ 2 := by
  classical
  rw [S.inner_apply_eq_sum v, norm_sq_eq_sum S.basis v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ F
  · exact mul_le_mul_of_nonneg_right (hF i hi) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_spectralSpan hv hi]
    simp

/-! ### Traces -/

omit [FiniteDimensional ℝ E] in
/-- `T` acts on the `i`-th eigenvector of `T ^ n` by `val i ^ n`. -/
lemma pow_apply_basis (S : EigenSystem N T) (n : ℕ) (i : Fin N) :
    (T ^ n) (S.basis i) = (S.val i) ^ n • S.basis i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, S.apply_basis i, smul_smul, pow_succ']
      ring_nf

omit [FiniteDimensional ℝ E] in
/-- The eigenvalues sum to the trace. -/
lemma trace_eq_sum (S : EigenSystem N T) : LinearMap.trace ℝ E T = ∑ i, S.val i := by
  rw [trace_eq_sum_inner S.basis T]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.apply_basis i, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp

omit [FiniteDimensional ℝ E] in
/-- The `n`-th powers of the eigenvalues sum to the trace of `T ^ n`. -/
lemma trace_pow_eq_sum (S : EigenSystem N T) (n : ℕ) :
    LinearMap.trace ℝ E (T ^ n) = ∑ i, (S.val i) ^ n := by
  rw [trace_eq_sum_inner S.basis (T ^ n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.pow_apply_basis n i, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp

end EigenSystem

omit [FiniteDimensional ℝ E] in
/-- The eigenvectors span everything. -/
lemma spectralSpan_univ (b : OrthonormalBasis (Fin N) ℝ E) :
    spectralSpan b Finset.univ = ⊤ := by
  have himg : (b '' ((Finset.univ : Finset (Fin N)) : Set (Fin N))) = Set.range b := by
    simp
  rw [spectralSpan, himg, ← OrthonormalBasis.coe_toBasis]
  exact b.toBasis.span_eq

namespace EigenSystem

variable {T : E →ₗ[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- **The Perron eigenvalue bounds the whole Rayleigh quotient.**  Used for Lemma
`lem:spectral-budget`. -/
lemma rayleigh_top (S : EigenSystem N T) (hN : 0 < N) (v : E) :
    ⟪v, T v⟫ ≤ S.val ⟨0, hN⟩ * ‖v‖ ^ 2 := by
  refine S.rayleigh_le (F := Finset.univ) (fun j _ => S.antitone ?_) ?_
  · exact Fin.le_def.mpr (Nat.zero_le _)
  · rw [spectralSpan_univ]
    exact Submodule.mem_top

omit [FiniteDimensional ℝ E] in
/-- The quadratic form at an eigenvector is the eigenvalue. -/
lemma inner_basis (S : EigenSystem N T) (i : Fin N) : ⟪S.basis i, T (S.basis i)⟫ = S.val i := by
  rw [S.apply_basis i, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp

end EigenSystem

end CycleCommonality
