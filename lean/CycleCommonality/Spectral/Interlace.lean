import CycleCommonality.Spectral.EigenSystem

/-!
# Rank-one interlacing, without Courant–Fischer

Adding a rank-one orthogonal projection `P` to a symmetric operator `A` interlaces the
eigenvalues:

```
  α i ≤ μ i        and        μ (i+1) ≤ α i.
```

The paper deduces this from the min–max principle.  Mathlib has no min–max principle, so both
inequalities are proved here by dimension counting against the Rayleigh bounds of
`Spectral/EigenSystem.lean`:

* for `α i ≤ μ i`, the span of the top `i+1` eigenvectors of `A` and the span of the bottom
  `N - i` eigenvectors of `A + P` have dimensions summing to `N + 1`, so they meet in a nonzero
  vector; `P ≥ 0` finishes;
* for `μ (i+1) ≤ α i`, the span of the top `i+2` eigenvectors of `A + P` and the span of the
  bottom `N - i` eigenvectors of `A` meet in dimension at least `2`, hence still meet the
  hyperplane `ker P = (ℝ ∙ u)ᗮ`; on a vector there `P` contributes nothing.

The trace identity `∑ μ = ∑ α + 1` is `sum_val_rankOne`.
-/

namespace CycleCommonality

open Finset Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

/-! ### The rank-one perturbation `x ↦ ⟪u, x⟫ • u` -/

/-- The rank-one positive semidefinite operator `x ↦ ⟪u, x⟫ • u`.  For a unit vector `u` this is
the orthogonal projection onto `ℝ ∙ u`, the operator called `P` in the paper. -/
noncomputable def rankOne (u : E) : E →ₗ[ℝ] E :=
  (innerSL ℝ u).toLinearMap.smulRight u

omit [FiniteDimensional ℝ E] in
@[simp] lemma rankOne_apply (u x : E) : rankOne u x = ⟪u, x⟫ • u := rfl

omit [FiniteDimensional ℝ E] in
lemma rankOne_isSymmetric (u : E) : (rankOne u).IsSymmetric := by
  intro x y
  simp only [rankOne_apply, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u x, real_inner_comm y u]
  ring

omit [FiniteDimensional ℝ E] in
/-- `rankOne u` is positive semidefinite: this is the only property of `P` used in the first
interlacing inequality. -/
lemma inner_rankOne_nonneg (u x : E) : 0 ≤ ⟪x, rankOne u x⟫ := by
  rw [rankOne_apply, real_inner_smul_right, real_inner_comm x u]
  exact mul_self_nonneg _

omit [FiniteDimensional ℝ E] in
/-- `rankOne u` vanishes on the hyperplane `(ℝ ∙ u)ᗮ`. -/
lemma rankOne_eq_zero_of_mem_orthogonal {u x : E} (hx : x ∈ (ℝ ∙ u)ᗮ) : rankOne u x = 0 := by
  have : ⟪u, x⟫ = 0 := hx u (Submodule.mem_span_singleton_self u)
  simp [rankOne_apply, this]

/-- The trace of `rankOne u` is `‖u‖ ^ 2`; for a unit vector it is `1 = Tr P`. -/
lemma trace_rankOne (u : E) : LinearMap.trace ℝ E (rankOne u) = ‖u‖ ^ 2 := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  rw [trace_eq_sum_inner b (rankOne u)]
  have h : ∀ i, ⟪b i, rankOne u (b i)⟫ = ⟪u, b i⟫ * ⟪b i, u⟫ := by
    intro i
    rw [rankOne_apply, real_inner_smul_right, real_inner_comm (b i) u]
  rw [Finset.sum_congr rfl fun i _ => h i, b.sum_inner_mul_inner u u,
    real_inner_self_eq_norm_sq]

/-! ### The three spectral inputs of the majorization lemma -/

variable {A : E →ₗ[ℝ] E} {u : E}

/-- **The trace shift**: adding a rank-one projection raises the sum of the eigenvalues by one. -/
theorem sum_val_rankOne (SA : EigenSystem N A) (SB : EigenSystem N (A + rankOne u))
    (hu : ‖u‖ = 1) :
    ∑ i, SB.val i = (∑ i, SA.val i) + 1 := by
  rw [← SB.trace_eq_sum, ← SA.trace_eq_sum, map_add, trace_rankOne u, hu]
  norm_num

/-- **Positive rank-one perturbations raise the eigenvalues**: `α i ≤ μ i`.

Dimension count: `(i+1) + (N-i) = N+1 > N`, so the top `i+1` eigenvectors of `A` and the bottom
`N-i` eigenvectors of `A + P` share a nonzero vector. -/
theorem val_le_of_rankOne (SA : EigenSystem N A) (SB : EigenSystem N (A + rankOne u))
    (hn : finrank ℝ E = N) (i : Fin N) :
    SA.val i ≤ SB.val i := by
  classical
  have hiN : (i : ℕ) < N := i.isLt
  set V := spectralSpan SA.basis (Finset.Iic i) with hV
  set W := spectralSpan SB.basis (Finset.Ici i) with hW
  have hdV : finrank ℝ V = (i : ℕ) + 1 := by
    rw [hV, finrank_spectralSpan]; exact Fin.card_Iic i
  have hdW : finrank ℝ W = N - (i : ℕ) := by
    rw [hW, finrank_spectralSpan]; exact Fin.card_Ici i
  obtain ⟨v, hv, hv0⟩ := exists_mem_inf_ne_zero (V := V) (W := W) (by rw [hn, hdV, hdW]; omega)
  have hnormpos : 0 < ‖v‖ ^ 2 := by positivity
  have h1 : SA.val i * ‖v‖ ^ 2 ≤ ⟪v, A v⟫ :=
    SA.rayleigh_ge (fun j hj => SA.antitone (Finset.mem_Iic.mp hj)) hv.1
  have h2 : ⟪v, (A + rankOne u) v⟫ ≤ SB.val i * ‖v‖ ^ 2 :=
    SB.rayleigh_le (fun j hj => SB.antitone (Finset.mem_Ici.mp hj)) hv.2
  have h3 : ⟪v, A v⟫ ≤ ⟪v, (A + rankOne u) v⟫ := by
    rw [LinearMap.add_apply, inner_add_right]
    linarith [inner_rankOne_nonneg u v]
  exact le_of_mul_le_mul_right (by linarith) hnormpos

/-- **Rank-one interlacing**: `μ (i+1) ≤ α i`.

Dimension count: the top `i+2` eigenvectors of `A + P` and the bottom `N-i` eigenvectors of `A`
meet in dimension at least `2`, hence still meet the hyperplane `(ℝ ∙ u)ᗮ`, on which `P` acts as
zero. -/
theorem val_succ_le_of_rankOne (SA : EigenSystem N A) (SB : EigenSystem N (A + rankOne u))
    (hn : finrank ℝ E = N) (hu : u ≠ 0) (i j : Fin N) (hij : (j : ℕ) = (i : ℕ) + 1) :
    SB.val j ≤ SA.val i := by
  classical
  have hiN : (i : ℕ) < N := i.isLt
  set V := spectralSpan SB.basis (Finset.Iic j) with hV
  set W := spectralSpan SA.basis (Finset.Ici i) with hW
  set U := (ℝ ∙ u)ᗮ with hU
  have hdV : finrank ℝ V = (i : ℕ) + 2 := by
    rw [hV, finrank_spectralSpan, Fin.card_Iic, hij]
  have hdW : finrank ℝ W = N - (i : ℕ) := by
    rw [hW, finrank_spectralSpan]; exact Fin.card_Ici i
  have hdU : finrank ℝ U + 1 = N := by
    have h := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ u)) (𝕜 := ℝ) (E := E)
    rw [← hU, finrank_span_singleton hu, hn] at h
    omega
  have h12 : 2 ≤ finrank ℝ ((V ⊓ W : Submodule ℝ E)) := by
    have hkey := finrank_inf_ge V W
    rw [hn, hdV, hdW] at hkey
    omega
  have hpos : 0 < finrank ℝ (((V ⊓ W) ⊓ U : Submodule ℝ E)) := by
    have hkey := finrank_inf_ge (V ⊓ W) U
    rw [hn] at hkey
    omega
  obtain ⟨v, hv, hv0⟩ := exists_mem_ne_zero_of_finrank_pos hpos
  have hnormpos : 0 < ‖v‖ ^ 2 := by positivity
  have h1 : SB.val j * ‖v‖ ^ 2 ≤ ⟪v, (A + rankOne u) v⟫ :=
    SB.rayleigh_ge (fun k hk => SB.antitone (Finset.mem_Iic.mp hk)) hv.1.1
  have h2 : ⟪v, A v⟫ ≤ SA.val i * ‖v‖ ^ 2 :=
    SA.rayleigh_le (fun k hk => SA.antitone (Finset.mem_Ici.mp hk)) hv.1.2
  have h3 : ⟪v, (A + rankOne u) v⟫ = ⟪v, A v⟫ := by
    rw [LinearMap.add_apply, inner_add_right, rankOne_eq_zero_of_mem_orthogonal hv.2,
      inner_zero_right, add_zero]
  exact le_of_mul_le_mul_right (by linarith) hnormpos

end CycleCommonality
