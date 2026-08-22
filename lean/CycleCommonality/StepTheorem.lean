import CycleCommonality.Extremal

/-!
# Exact region for a shorter even and a longer odd cycle, for step graphons

The even length is `n`, the positive odd gap is `d`, and the odd length is `n+d`.
-/

namespace CycleCommonality

/-- The scaled commonality inequality holds for every weighted step graphon exactly
up to the critical point. -/
theorem commonality_iff {n d : ℕ} (hne : Even n) (hn4 : 4 ≤ n)
    (hd : Odd d) (hd0 : 0 < d) {a c : ℝ}
    (hc : 1 / 2 < c) (hc1 : c < 1)
    (hcrit : rho n d c = twoCliqueValue n) (ha0 : 0 < a) :
    (∀ (N : ℕ), 0 < N → ∀ G : StepGraphon N,
        rho n d a ≤ G.densityCompl n + kappa n d a * G.density (n + d)) ↔
      a ≤ c := by
  constructor
  · intro hall
    by_contra hcon
    have hca : c < a := not_le.mp hcon
    have hviol := twoClique.violates hne hn4 hd hd0
      (by linarith : (0 : ℝ) ≤ c) hcrit hca
    have htwo := hall 2 (by norm_num) twoClique
    linarith
  · intro hac N hN G
    exact G.lower_bound hN hne hn4 hd hd0 hc hc1 hcrit ha0 hac

/-- The critical point exists and is unique in `(1/2,1)`. -/
theorem exists_unique_critical {n d : ℕ} (hn : 4 ≤ n) (hd : 0 < d) :
    ∃! c : ℝ, (1 / 2 < c ∧ c < 1) ∧ rho n d c = twoCliqueValue n := by
  obtain ⟨c, hc, hc1, hcrit⟩ := exists_critical (by omega : 2 ≤ n) hd
  refine ⟨c, ⟨⟨hc, hc1⟩, hcrit⟩, ?_⟩
  rintro q ⟨⟨hq, hq1⟩, hqcrit⟩
  by_contra hne
  have hmono := rho_strictMonoOn (by omega : 2 ≤ n) hd
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hm := hmono (by linarith : (0 : ℝ) ≤ q) (by linarith : (0 : ℝ) ≤ c) hlt
    rw [hqcrit, hcrit] at hm
    exact lt_irrefl _ hm
  · have hm := hmono (by linarith : (0 : ℝ) ≤ c) (by linarith : (0 : ℝ) ≤ q) hlt
    rw [hqcrit, hcrit] at hm
    exact lt_irrefl _ hm

end CycleCommonality
