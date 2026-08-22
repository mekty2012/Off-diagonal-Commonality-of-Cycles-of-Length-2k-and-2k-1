import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Rayleigh bounds on spectral subspaces

Mathlib has no Courant–Fischer min–max principle.  The two rank-one interlacing inequalities used
here follow from dimension counting together with the elementary Rayleigh bounds proved here,
namely that on the span of a
set `S` of eigenvectors the quadratic form is squeezed between the smallest and the largest
eigenvalue indexed by `S`.

Working entirely in the coordinates of `hT.eigenvectorBasis`, both bounds are termwise
comparisons of the single sum `⟪v, T v⟫ = ∑ i, eigenvalue i * (coordinate i) ^ 2`.

Main definitions and results:

* `spectralSpan b S` — the span of the eigenvectors indexed by `S`;
* `finrank_spectralSpan` — its dimension is `S.card`;
* `inner_apply_eq_sum`, `norm_sq_eq_sum` — the quadratic form and the norm in coordinates;
* `rayleigh_ge`, `rayleigh_le` — the Rayleigh bounds on `spectralSpan`.
-/

namespace CycleCommonality

open Finset Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

/-! ### Coordinates of an orthonormal basis -/

/-- The submodule cut out by requiring the coordinates outside `S` to vanish. -/
def coordKer (b : OrthonormalBasis (Fin N) ℝ E) (S : Finset (Fin N)) : Submodule ℝ E where
  carrier := {v | ∀ j ∉ S, b.repr v j = 0}
  zero_mem' := by intro j _; simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro c x hx j hj; simp [hx j hj]

/-- The span of the basis vectors indexed by `S`. -/
def spectralSpan (b : OrthonormalBasis (Fin N) ℝ E) (S : Finset (Fin N)) : Submodule ℝ E :=
  Submodule.span ℝ (b '' (S : Set (Fin N)))

omit [FiniteDimensional ℝ E] in
lemma spectralSpan_le_coordKer (b : OrthonormalBasis (Fin N) ℝ E) (S : Finset (Fin N)) :
    spectralSpan b S ≤ coordKer b S := by
  classical
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩ j hj
  have hij : j ≠ i := by rintro rfl; exact hj hi
  simp [OrthonormalBasis.repr_self, hij]

omit [FiniteDimensional ℝ E] in
/-- Coordinates outside `S` vanish on `spectralSpan b S`. -/
lemma repr_eq_zero_of_mem_spectralSpan {b : OrthonormalBasis (Fin N) ℝ E} {S : Finset (Fin N)}
    {v : E} (hv : v ∈ spectralSpan b S) {j : Fin N} (hj : j ∉ S) : b.repr v j = 0 :=
  spectralSpan_le_coordKer b S hv j hj

omit [FiniteDimensional ℝ E] in
/-- The span of `S`-many orthonormal vectors has dimension `S.card`. -/
lemma finrank_spectralSpan (b : OrthonormalBasis (Fin N) ℝ E) (S : Finset (Fin N)) :
    finrank ℝ (spectralSpan b S) = S.card := by
  classical
  have hli : LinearIndependent ℝ (fun i : (S : Finset (Fin N)) => b (i : Fin N)) :=
    b.toBasis.linearIndependent.comp (fun i : (S : Finset (Fin N)) => (i : Fin N))
      Subtype.val_injective
  have hset : Set.range (fun i : (S : Finset (Fin N)) => b (i : Fin N))
      = b '' (S : Set (Fin N)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(i : Fin N), i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have := finrank_span_eq_card hli
  rw [hset] at this
  rw [spectralSpan, this, Fintype.card_coe]

/-! ### Dimension counting -/

/-- The dimension of an intersection is at least the excess of the sum of the dimensions over
`finrank E`.  This is what replaces the min–max principle in `Spectral/Interlace.lean`. -/
lemma finrank_inf_ge (V W : Submodule ℝ E) :
    finrank ℝ V + finrank ℝ W ≤ finrank ℝ E + finrank ℝ ((V ⊓ W : Submodule ℝ E)) := by
  have hsup : finrank ℝ ((V ⊔ W : Submodule ℝ E)) ≤ finrank ℝ E := Submodule.finrank_le _
  have hkey : finrank ℝ ((V ⊔ W : Submodule ℝ E)) + finrank ℝ ((V ⊓ W : Submodule ℝ E))
      = finrank ℝ V + finrank ℝ W := Submodule.finrank_sup_add_finrank_inf_eq V W
  omega

/-- A subspace of positive dimension contains a nonzero vector. -/
lemma exists_mem_ne_zero_of_finrank_pos {V : Submodule ℝ E} (h : 0 < finrank ℝ V) :
    ∃ v : E, v ∈ V ∧ v ≠ 0 := by
  have hnt : Nontrivial V := Module.finrank_pos_iff.mp h
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : V)
  exact ⟨v, hv, by simpa [Submodule.mk_eq_zero] using hv0⟩

/-- Two subspaces whose dimensions add to more than `finrank E` meet in a nonzero vector. -/
lemma exists_mem_inf_ne_zero {V W : Submodule ℝ E}
    (h : finrank ℝ E < finrank ℝ V + finrank ℝ W) :
    ∃ v : E, v ∈ V ⊓ W ∧ v ≠ 0 :=
  exists_mem_ne_zero_of_finrank_pos (by have := finrank_inf_ge V W; omega)

end CycleCommonality
