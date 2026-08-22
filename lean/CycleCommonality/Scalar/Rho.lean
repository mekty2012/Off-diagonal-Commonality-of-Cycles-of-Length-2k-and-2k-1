import CycleCommonality.Majorization.Karamata
import Mathlib.Topology.Order.IntermediateValue

/-!
# Scalar theory for a shorter even cycle and a longer odd cycle

The even cycle has length `n`, the positive odd gap is `d`, and the odd cycle has length `n + d`.
This file develops the scalar functions, critical point, and coefficient bounds for these two
cycle lengths.
-/

namespace CycleCommonality

open Set Finset
open scoped RealInnerProductSpace

/-- The scaled target value
`rho n d a = a^(n-1) (n + d a) / (n+d)`. -/
noncomputable def rho (n d : ℕ) (a : ℝ) : ℝ :=
  a ^ (n - 1) * ((n : ℝ) + (d : ℝ) * a) / ((n + d : ℕ) : ℝ)

/-- The coefficient of the odd-cycle density. -/
noncomputable def kappa (n d : ℕ) (a : ℝ) : ℝ :=
  (n : ℝ) * a ^ (n - 1) /
    (((n + d : ℕ) : ℝ) * (1 - a) ^ (n + d - 1))

/-- The scalar function minimized at `1-a`. -/
noncomputable def fk (n d : ℕ) (κ x : ℝ) : ℝ :=
  (1 - x) ^ n + κ * x ^ (n + d)

/-- The supporting-line inequality for `x ↦ x^m` at a nonnegative point. -/
theorem pow_tangent_le_of_nonneg {m : ℕ} (hm : m ≠ 0) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ m + (m : ℝ) * x ^ (m - 1) * (y - x) ≤ y ^ m := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 :=
    ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm)).symm⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [zero_pow (by omega), zero_pow (by omega)]
      simpa using pow_nonneg hy (p + 1)
  · have hxp : (0 : ℝ) < x ^ (p + 1) := pow_pos hxpos _
    set u : ℝ := y / x with hu
    have hyu : y = x * u := by rw [hu]; field_simp
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    have hkey : 1 + ((p : ℝ) + 1) * (u - 1) ≤ u ^ (p + 1) := by
      have h := one_add_mul_le_pow (a := u - 1) (by linarith) (p + 1)
      simpa using h
    calc
      x ^ (p + 1) + ((p : ℝ) + 1) * x ^ p * (y - x) =
          x ^ (p + 1) * (1 + ((p : ℝ) + 1) * (u - 1)) := by
            rw [hyu]
            ring
      _ ≤ x ^ (p + 1) * u ^ (p + 1) := mul_le_mul_of_nonneg_left hkey hxp.le
      _ = y ^ (p + 1) := by rw [hyu, mul_pow]

lemma kappa_mul {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) {a : ℝ}
    (hb : (1 : ℝ) - a ≠ 0) :
    kappa n d a * (((n + d : ℕ) : ℝ) * (1 - a) ^ (n + d - 1)) =
      (n : ℝ) * a ^ (n - 1) := by
  have hpow : (1 - a) ^ (n + d - 1) ≠ 0 := pow_ne_zero _ hb
  have hnd : (((n + d : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (show n + d ≠ 0 by omega)
  unfold kappa
  field_simp

private lemma fk_supporting {n d : ℕ} (hne : Even n) (hn0 : n ≠ 0) (hd0 : d ≠ 0)
    (κ : ℝ) (hκ : 0 ≤ κ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    fk n d κ x + (y - x) *
        (κ * (((n + d : ℕ) : ℝ) * x ^ (n + d - 1)) -
          (n : ℝ) * (1 - x) ^ (n - 1)) ≤
      fk n d κ y := by
  have h1 : (1 - x) ^ n +
      (n : ℝ) * (1 - x) ^ (n - 1) * ((1 - y) - (1 - x)) ≤
      (1 - y) ^ n :=
    pow_tangent_le hne hn0 (1 - x) (1 - y)
  have h2 : x ^ (n + d) +
      (((n + d : ℕ) : ℝ) * x ^ (n + d - 1) * (y - x)) ≤ y ^ (n + d) := by
    simpa using pow_tangent_le_of_nonneg (m := n + d) (by omega) hx hy
  have h2' : κ * (x ^ (n + d) +
      (((n + d : ℕ) : ℝ) * x ^ (n + d - 1) * (y - x))) ≤
      κ * y ^ (n + d) := mul_le_mul_of_nonneg_left h2 hκ
  simp only [fk]
  nlinarith [h1, h2']

lemma fk_eq_rho {n d : ℕ} (hn0 : n ≠ 0) (hd0 : d ≠ 0) {a : ℝ}
    (_ha : a ≠ 0) (hb : (1 : ℝ) - a ≠ 0) :
    fk n d (kappa n d a) (1 - a) = rho n d a := by
  have hkm := kappa_mul hn0 hd0 hb
  have hcast : (((n + d : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (show n + d ≠ 0 by omega)
  have hterm :
      kappa n d a * (1 - a) * (1 - a) ^ (n + d - 1) =
        ((n : ℝ) * a ^ (n - 1) * (1 - a)) / ((n + d : ℕ) : ℝ) := by
    rw [eq_div_iff hcast]
    calc
      kappa n d a * (1 - a) * (1 - a) ^ (n + d - 1) * ((n + d : ℕ) : ℝ) =
          (kappa n d a * (((n + d : ℕ) : ℝ) * (1 - a) ^ (n + d - 1))) *
            (1 - a) := by ring
      _ = ((n : ℝ) * a ^ (n - 1)) * (1 - a) := by rw [hkm]
      _ = (n : ℝ) * a ^ (n - 1) * (1 - a) := by ring
  have hpow : (1 - a) ^ (n + d) =
      (1 - a) ^ (n + d - 1) * (1 - a) := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowa : a ^ n = a ^ (n - 1) * a := by
    rw [← pow_succ]
    congr 1
    omega
  rw [fk, rho]
  rw [show 1 - (1 - a) = a by ring, hpow]
  rw [show kappa n d a * ((1 - a) ^ (n + d - 1) * (1 - a)) =
      kappa n d a * (1 - a) * (1 - a) ^ (n + d - 1) by ring, hterm]
  rw [hpowa]
  field_simp
  push_cast
  ring

theorem fk_min {n d : ℕ} (hne : Even n) (hn0 : n ≠ 0) (hd0 : d ≠ 0)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x : ℝ} (hx : 0 ≤ x) :
    rho n d a ≤ fk n d (kappa n d a) x := by
  have hb : (1 : ℝ) - a ≠ 0 := by linarith
  have hb0 : (0 : ℝ) ≤ 1 - a := by linarith
  have hκ : 0 ≤ kappa n d a := by
    unfold kappa
    positivity
  have hcancel :
      kappa n d a * (((n + d : ℕ) : ℝ) * (1 - a) ^ (n + d - 1)) -
        (n : ℝ) * (1 - (1 - a)) ^ (n - 1) = 0 := by
    rw [kappa_mul hn0 hd0 hb]
    simp
  have h := fk_supporting hne hn0 hd0 (kappa n d a) hκ hb0 hx
  rw [hcancel, mul_zero, add_zero, fk_eq_rho hn0 hd0 (ne_of_gt ha0) hb] at h
  exact h

theorem fk_mono {n d : ℕ} (hne : Even n) (hn0 : n ≠ 0) (hd0 : d ≠ 0)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {y z : ℝ}
    (hby : 1 - a ≤ y) (hy1 : y ≤ 1) (hyz : y ≤ z) :
    fk n d (kappa n d a) y ≤ fk n d (kappa n d a) z := by
  have hb : (1 : ℝ) - a ≠ 0 := by linarith
  have hb0 : (0 : ℝ) ≤ 1 - a := by linarith
  have hy0 : (0 : ℝ) ≤ y := le_trans hb0 hby
  have hz0 : (0 : ℝ) ≤ z := le_trans hy0 hyz
  have hκ : 0 ≤ kappa n d a := by
    unfold kappa
    positivity
  have hslope : 0 ≤
      kappa n d a * (((n + d : ℕ) : ℝ) * y ^ (n + d - 1)) -
        (n : ℝ) * (1 - y) ^ (n - 1) := by
    have hpow : (1 - a) ^ (n + d - 1) ≤ y ^ (n + d - 1) :=
      pow_le_pow_left₀ hb0 hby _
    have h1y : (0 : ℝ) ≤ 1 - y := by linarith
    have hpow2 : (1 - y) ^ (n - 1) ≤ a ^ (n - 1) := by
      simpa using pow_le_pow_left₀ h1y (by linarith : 1 - y ≤ a) (n - 1)
    have hk := kappa_mul hn0 hd0 hb
    have hmul :
        kappa n d a * (((n + d : ℕ) : ℝ) * (1 - a) ^ (n + d - 1)) ≤
          kappa n d a * (((n + d : ℕ) : ℝ) * y ^ (n + d - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      · exact hκ
    have h3 : (n : ℝ) * (1 - y) ^ (n - 1) ≤ (n : ℝ) * a ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hpow2 (Nat.cast_nonneg n)
    linarith
  have h := fk_supporting hne hn0 hd0 (kappa n d a) hκ hy0 hz0
  nlinarith [h, hslope, sub_nonneg.mpr hyz]

lemma rho_eq_add {n d : ℕ} (hn : n ≠ 0) (a : ℝ) :
    rho n d a = ((n : ℝ) * a ^ (n - 1) + (d : ℝ) * a ^ n) /
      ((n + d : ℕ) : ℝ) := by
  have hpow : a ^ n = a ^ (n - 1) * a := by
    rw [← pow_succ]
    congr 1
    omega
  rw [rho, hpow]
  ring

theorem rho_strictMonoOn {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    StrictMonoOn (rho n d) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hn0 : n ≠ 0 := by omega
  have hnd : n + d ≠ 0 := by omega
  have h1 : x ^ (n - 1) < y ^ (n - 1) :=
    pow_lt_pow_left₀ hxy hx (by omega)
  have h2 : x ^ n < y ^ n := pow_lt_pow_left₀ hxy hx hn0
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hden : (0 : ℝ) < ((n + d : ℕ) : ℝ) := by positivity
  rw [rho_eq_add hn0, rho_eq_add hn0, div_lt_div_iff₀ hden hden]
  have h3 := mul_lt_mul_of_pos_left h1 hnpos
  have h4 := mul_lt_mul_of_pos_left h2 hdpos
  nlinarith

/-- The value `2^(1-n)` attained by the balanced two-clique graphon. -/
noncomputable def twoCliqueValue (n : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ n

/-- The critical point lies in `(1/2,1)`. -/
theorem exists_critical {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧ rho n d a = twoCliqueValue n := by
  have hnd : n + d ≠ 0 := by omega
  have hcont : ContinuousOn (rho n d) (Icc (1 / 2 : ℝ) 1) := by
    apply Continuous.continuousOn
    unfold rho
    fun_prop
  have hhalf : rho n d (1 / 2 : ℝ) < twoCliqueValue n := by
    have hn0 : n ≠ 0 := by omega
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (n - 1) := by positivity
    have hpow : (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (n - 1) * (1 / 2) := by
      rw [← pow_succ]
      congr 1
      omega
    have htarget : twoCliqueValue n = (1 / 2 : ℝ) ^ (n - 1) := by
      rw [twoCliqueValue, hpow]
      ring
    rw [rho_eq_add hn0, htarget, hpow]
    have hden : (0 : ℝ) < ((n + d : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hden]
    push_cast
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hone : twoCliqueValue n < rho n d 1 := by
    have hr : rho n d 1 = 1 := by
      rw [rho_eq_add (by omega : n ≠ 0)]
      simp only [one_pow, mul_one]
      rw [div_eq_one_iff_eq (by positivity)]
      push_cast
      ring
    rw [hr, twoCliqueValue]
    have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    nlinarith
  have hmem : twoCliqueValue n ∈ Icc (rho n d (1 / 2 : ℝ)) (rho n d 1) :=
    ⟨hhalf.le, hone.le⟩
  obtain ⟨a, ha, hfa⟩ :=
    intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1) hcont hmem
  refine ⟨a, ?_, ?_, hfa⟩
  · rcases lt_or_eq_of_le ha.1 with h | h
    · exact h
    · exact absurd (h ▸ hfa) (by simpa using hhalf.ne)
  · rcases lt_or_eq_of_le ha.2 with h | h
    · exact h
    · exact absurd (h ▸ hfa) (by simpa using hone.ne')

/-! ## Bounds at and below the critical point -/

/-- The critical equation after multiplying by `2^n`. -/
lemma critical_delta {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) {a : ℝ}
    (h : rho n d a = twoCliqueValue n) :
    (2 * a) ^ (n - 1) * (2 * ((n : ℝ) + (d : ℝ) * a)) =
      2 * ((n + d : ℕ) : ℝ) := by
  have hL : (((n + d : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (show n + d ≠ 0 by omega)
  have h' : a ^ (n - 1) * ((n : ℝ) + (d : ℝ) * a) =
      2 * (1 / 2 : ℝ) ^ n * ((n + d : ℕ) : ℝ) := by
    rw [rho, twoCliqueValue] at h
    rw [div_eq_iff hL] at h
    exact h
  have hpow : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hhalf : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 * a) ^ (n - 1) * (2 * ((n : ℝ) + (d : ℝ) * a)) =
        ((2 : ℝ) ^ (n - 1) * 2) *
          (a ^ (n - 1) * ((n : ℝ) + (d : ℝ) * a)) := by
            rw [mul_pow]
            ring
    _ = (2 : ℝ) ^ n *
          (2 * (1 / 2 : ℝ) ^ n * ((n + d : ℕ) : ℝ)) := by
      rw [hpow, h']
    _ = 2 * ((n + d : ℕ) : ℝ) := by
      rw [show (2 : ℝ) ^ n *
            (2 * (1 / 2 : ℝ) ^ n * ((n + d : ℕ) : ℝ)) =
            2 * (((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) * ((n + d : ℕ) : ℝ)) by ring,
          hhalf]
      ring

/-- The Bernoulli estimate on `δ = 2a-1`. -/
theorem delta_bound {n d : ℕ} (hn : 4 ≤ n) (hd : 0 < d) {a : ℝ}
    (ha : 1 / 2 < a) (ha1 : a < 1)
    (h : rho n d a = twoCliqueValue n) :
    2 * a - 1 < (d : ℝ) /
      (((n : ℝ) - 1) * (2 * (n : ℝ) + (d : ℝ))) := by
  set δ : ℝ := 2 * a - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hcast : (((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hB : (0 : ℝ) < 2 * (n : ℝ) + (d : ℝ) := by positivity
  have hcrit := critical_delta (by omega : n ≠ 0) (by omega : d ≠ 0) h
  have h2a : (2 : ℝ) * a = 1 + δ := by rw [hδ]; ring
  have hsum : 2 * ((n : ℝ) + (d : ℝ) * a) =
      2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ := by
    rw [hδ]
    ring
  rw [h2a, hsum] at hcrit
  have hp : (0 : ℝ) < (1 + δ) ^ (n - 1) := by positivity
  have hupper : (1 + δ) ^ (n - 1) * (2 * (n : ℝ) + (d : ℝ)) <
      2 * ((n + d : ℕ) : ℝ) := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    nlinarith [hcrit, mul_pos hp (mul_pos hdpos hδ0)]
  have hbern : 1 + ((n : ℝ) - 1) * δ ≤ (1 + δ) ^ (n - 1) := by
    have hb := one_add_mul_le_pow (a := δ) (by linarith) (n - 1)
    rwa [hcast] at hb
  have hkey : (1 + ((n : ℝ) - 1) * δ) *
      (2 * (n : ℝ) + (d : ℝ)) < 2 * ((n + d : ℕ) : ℝ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbern hB.le) hupper
  rw [lt_div_iff₀ (mul_pos hn1 hB)]
  push_cast at hkey ⊢
  nlinarith [hkey]

/-- The critical complement is uniformly larger than `5/14`. -/
theorem five_fourteenths_lt_one_sub_critical {n d : ℕ} (hn : 4 ≤ n) (hd : 0 < d)
    {c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n d c = twoCliqueValue n) :
    (5 : ℝ) / 14 < 1 - c := by
  set δ : ℝ := 2 * c - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hcrit := critical_delta (by omega : n ≠ 0) (by omega : d ≠ 0) h
  have h2c : (2 : ℝ) * c = 1 + δ := by rw [hδ]; ring
  have hsum : 2 * ((n : ℝ) + (d : ℝ) * c) =
      2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ := by
    rw [hδ]
    ring
  rw [h2c, hsum] at hcrit
  have hp : (0 : ℝ) < (1 + δ) ^ (n - 1) := by positivity
  have hL : (0 : ℝ) < ((n + d : ℕ) : ℝ) := by positivity
  have hBL : ((n + d : ℕ) : ℝ) <
      2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ := by
    push_cast
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    nlinarith [mul_pos hdpos hδ0]
  have hpowlt : (1 + δ) ^ (n - 1) < 2 := by
    have hm := mul_lt_mul_of_pos_left hBL hp
    nlinarith [hcrit, hm]
  by_contra hcon
  have hcomp : 1 - c ≤ (5 : ℝ) / 14 := not_lt.mp hcon
  have hδlower : (2 : ℝ) / 7 ≤ δ := by
    rw [hδ]
    linarith
  have hbase : (9 : ℝ) / 7 ≤ 1 + δ := by linarith
  have hcubelow : ((9 : ℝ) / 7) ^ 3 ≤ (1 + δ) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num) hbase 3
  have hpow3 : (1 + δ) ^ 3 ≤ (1 + δ) ^ (n - 1) := by
    exact pow_le_pow_right₀ (by linarith : 1 ≤ 1 + δ) (by omega : 3 ≤ n - 1)
  have : (2 : ℝ) < ((9 : ℝ) / 7) ^ 3 := by norm_num
  linarith

/-- Closed form for `κ(a)(1-a)^d`. -/
lemma kappa_mul_one_sub_pow {n d : ℕ} (hn : n ≠ 0) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    kappa n d a * (1 - a) ^ d =
      ((n : ℝ) / ((n + d : ℕ) : ℝ)) * (a / (1 - a)) ^ (n - 1) := by
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hexp : n + d - 1 = (n - 1) + d := by omega
  rw [kappa, hexp, pow_add, div_pow]
  field_simp

/-- `κ(a)(1-a)^d` is monotone in `a`. -/
lemma kappa_mul_one_sub_pow_mono {n d : ℕ} (hn : n ≠ 0) {a c : ℝ}
    (ha0 : 0 < a) (hac : a ≤ c) (hc1 : c < 1) :
    kappa n d a * (1 - a) ^ d ≤ kappa n d c * (1 - c) ^ d := by
  have ha1 : a < 1 := lt_of_le_of_lt hac hc1
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hbc : (0 : ℝ) < 1 - c := by linarith
  have hratio : a / (1 - a) ≤ c / (1 - c) := by
    rw [div_le_div_iff₀ hb hbc]
    nlinarith
  have hpow : (a / (1 - a)) ^ (n - 1) ≤ (c / (1 - c)) ^ (n - 1) :=
    pow_le_pow_left₀ (by positivity) hratio _
  rw [kappa_mul_one_sub_pow hn ha0 ha1,
    kappa_mul_one_sub_pow hn (lt_of_lt_of_le ha0 hac) hc1]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The critical endpoint satisfies `κ(c)(1-c)^d < 1`. -/
theorem kappa_star_mul_one_sub_pow_lt_one {n d : ℕ} (hn : 4 ≤ n) (hd : 0 < d)
    {c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n d c = twoCliqueValue n) :
    kappa n d c * (1 - c) ^ d < 1 := by
  set δ : ℝ := 2 * c - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hB : (0 : ℝ) < 2 * (n : ℝ) + (d : ℝ) := by positivity
  have hBδ : (0 : ℝ) < 2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ := by
    positivity
  have hL : (0 : ℝ) < ((n + d : ℕ) : ℝ) := by positivity
  have hcast : (((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hbern : 1 - ((n : ℝ) - 1) * δ ≤ (1 - δ) ^ (n - 1) := by
    have hb := one_add_mul_le_pow (a := -δ) (by linarith) (n - 1)
    rw [hcast] at hb
    calc
      1 - ((n : ℝ) - 1) * δ = 1 + ((n : ℝ) - 1) * (-δ) := by ring
      _ ≤ (1 + -δ) ^ (n - 1) := hb
      _ = (1 - δ) ^ (n - 1) := by ring_nf
  have hdb := delta_bound hn hd hc hc1 h
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hstep : ((n : ℝ) - 1) * δ <
      (d : ℝ) / (2 * (n : ℝ) + (d : ℝ)) := by
    rw [lt_div_iff₀ hB]
    rw [lt_div_iff₀ (mul_pos hn1 hB)] at hdb
    nlinarith [hdb]
  have hlow : (2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ)) <
      (1 - δ) ^ (n - 1) := by
    have hid : (2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ)) =
        1 - (d : ℝ) / (2 * (n : ℝ) + (d : ℝ)) := by
      field_simp
      ring
    rw [hid]
    linarith
  have hlowpos : 0 < (2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ)) := by
    positivity
  have hprod : 2 * (n : ℝ) <
      (2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ) * (1 - δ) ^ (n - 1) := by
    have hid : (2 * (n : ℝ) + (d : ℝ)) *
        ((2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ))) = 2 * (n : ℝ) := by
      field_simp
    calc
      2 * (n : ℝ) = (2 * (n : ℝ) + (d : ℝ)) *
          ((2 * (n : ℝ)) / (2 * (n : ℝ) + (d : ℝ))) := hid.symm
      _ < (2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ) *
          (1 - δ) ^ (n - 1) := by
        apply mul_lt_mul' (by nlinarith [mul_pos hdR hδ0]) hlow hlowpos.le
        positivity
  have hcrit := critical_delta (by omega : n ≠ 0) (by omega : d ≠ 0) h
  have h2c : (2 : ℝ) * c = 1 + δ := by rw [hδ]; ring
  have hsum : 2 * ((n : ℝ) + (d : ℝ) * c) =
      2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ := by
    rw [hδ]
    ring
  rw [h2c, hsum] at hcrit
  have h2b : (2 : ℝ) * (1 - c) = 1 - δ := by rw [hδ]; ring
  have hratio : c / (1 - c) = (1 + δ) / (1 - δ) := by
    rw [← h2c, ← h2b, mul_div_mul_left _ _ (two_ne_zero)]
  have hkey : kappa n d c * (1 - c) ^ d =
      ((n : ℝ) * (1 + δ) ^ (n - 1)) /
        (((n + d : ℕ) : ℝ) * (1 - δ) ^ (n - 1)) := by
    rw [kappa_mul_one_sub_pow (by omega : n ≠ 0) (by linarith) hc1,
      hratio, div_pow]
    field_simp
  rw [hkey, div_lt_one (by positivity)]
  have hfac : (1 + δ) ^ (n - 1) =
      (2 * ((n + d : ℕ) : ℝ)) /
        (2 * (n : ℝ) + (d : ℝ) + (d : ℝ) * δ) := by
    rw [eq_div_iff (ne_of_gt hBδ)]
    exact hcrit
  rw [hfac, ← mul_div_assoc, div_lt_iff₀ hBδ]
  have hm := mul_lt_mul_of_pos_left hprod hL
  push_cast at hm ⊢
  nlinarith

/-- The product bound for every parameter below the critical point. -/
theorem kappa_mul_one_sub_pow_lt_one {n d : ℕ} (hn : 4 ≤ n) (hd : 0 < d)
    {a c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n d c = twoCliqueValue n) (ha0 : 0 < a) (hac : a ≤ c) :
    kappa n d a * (1 - a) ^ d < 1 :=
  lt_of_le_of_lt (kappa_mul_one_sub_pow_mono (by omega) ha0 hac hc1)
    (kappa_star_mul_one_sub_pow_lt_one hn hd hc hc1 h)

/-- The uniform complement bound for every parameter below the critical point. -/
theorem five_fourteenths_lt_one_sub {n d : ℕ} (hn : 4 ≤ n) (hd : 0 < d)
    {a c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n d c = twoCliqueValue n) (hac : a ≤ c) :
    (5 : ℝ) / 14 < 1 - a := by
  have hcbd := five_fourteenths_lt_one_sub_critical hn hd hc hc1 h
  linarith

/-- `(1-x)^n + x^n ≥ 2^(1-n)` for even `n`. -/
theorem two_point_convexity {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) (x : ℝ) :
    twoCliqueValue n ≤ (1 - x) ^ n + x ^ n := by
  have h1 := pow_tangent_le hne hn0 (1 / 2 : ℝ) x
  have h2 := pow_tangent_le hne hn0 (1 / 2 : ℝ) (1 - x)
  have hsum :
      ((1 : ℝ) / 2) ^ n + (n : ℝ) * ((1 : ℝ) / 2) ^ (n - 1) * (x - 1 / 2) +
          (((1 : ℝ) / 2) ^ n +
            (n : ℝ) * ((1 : ℝ) / 2) ^ (n - 1) * ((1 - x) - 1 / 2)) =
        2 * ((1 : ℝ) / 2) ^ n := by ring
  rw [twoCliqueValue]
  linarith [h1, h2, hsum]

end CycleCommonality
