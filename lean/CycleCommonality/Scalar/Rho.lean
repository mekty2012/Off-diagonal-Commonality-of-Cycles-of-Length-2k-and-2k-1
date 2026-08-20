import CycleCommonality.Majorization.Karamata
import Mathlib.Topology.Order.IntermediateValue

/-!
# The scalar functions `ρ_n`, `κ_n`, and the minimum of `f_κ`

This is `eq:kappa-rho`–`lem:critical-point` of `adjacent_cycle_commonality.tex`.  For `a ∈ (0,1)`
and `b = 1 - a`,

```
  κ_n(a) = n a^{n-1} / ((n+1) b^n),      ρ_n(a) = a^{n-1}(a+n)/(n+1),
  f_κ(x) = (1-x)^n + κ x^{n+1}.
```

The paper argues by differentiating twice: `f_κ` is strictly convex and `f_κ'(b) = 0`, so `b` is
the unique minimiser and `f_κ(b) = ρ_n(a)`.  No calculus is needed here.  Both facts used
downstream — that `b` minimises `f_κ` on `[0, ∞)`, and that `f_κ` is monotone to the right of `b`
— follow from two *supporting-line* inequalities:

* `pow_tangent_le` (in `Majorization/Karamata.lean`), valid on all of `ℝ` for even exponents,
  applied to `(1-x)^n`;
* `pow_tangent_le_of_nonneg` below, valid on `[0, ∞)` for every exponent, applied to `x^{n+1}`.

Adding the two supporting lines produces the multiple `κ(n+1)b^n - n a^{n-1}` of `x - b`, which is
zero by the definition of `κ` — the same computation as the paper's `f_κ'(b) = 0`, but with no
derivative.
-/

namespace CycleCommonality

open Set

/-- The scaled target value `ρ_n(a) = a^{n-1}(a+n)/(n+1)` of `eq:kappa-rho`. -/
noncomputable def rho (n : ℕ) (a : ℝ) : ℝ := a ^ (n - 1) * (a + n) / (n + 1)

/-- The normalizing coefficient `κ_n(a) = n a^{n-1} / ((n+1)(1-a)^n)` of `eq:kappa-rho`. -/
noncomputable def kappa (n : ℕ) (a : ℝ) : ℝ := n * a ^ (n - 1) / ((n + 1) * (1 - a) ^ n)

/-- The function `f_κ(x) = (1-x)^n + κ x^{n+1}` of `eq:f-kappa`. -/
noncomputable def fk (n : ℕ) (κ x : ℝ) : ℝ := (1 - x) ^ n + κ * x ^ (n + 1)

/-! ### A supporting line for `x ^ m` on `[0, ∞)` -/

/-- The supporting-line inequality for `x ↦ x ^ m` at a nonnegative point, valid for every `m`.
(For even `m` the stronger `pow_tangent_le` holds on all of `ℝ`.) -/
theorem pow_tangent_le_of_nonneg {m : ℕ} (hm : m ≠ 0) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
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
    calc x ^ (p + 1) + ((p : ℝ) + 1) * x ^ p * (y - x)
        = x ^ (p + 1) * (1 + ((p : ℝ) + 1) * (u - 1)) := by
          rw [hyu]; ring
      _ ≤ x ^ (p + 1) * u ^ (p + 1) := mul_le_mul_of_nonneg_left hkey hxp.le
      _ = y ^ (p + 1) := by rw [hyu, mul_pow]

/-! ### The defining identity of `κ` -/

/-- `κ` is exactly the number making the two supporting lines cancel: `κ (n+1) b^n = n a^{n-1}`.
This is the paper's `f_κ'(b) = 0`. -/
lemma kappa_mul {n : ℕ} {a : ℝ} (hb : (1 : ℝ) - a ≠ 0) :
    kappa n a * ((n : ℝ) + 1) * (1 - a) ^ n = (n : ℝ) * a ^ (n - 1) := by
  have hbn : ((1 : ℝ) - a) ^ n ≠ 0 := pow_ne_zero n hb
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  unfold kappa
  field_simp

/-- `f_κ(b) = ρ_n(a)`, the paper's `eq:scalar-minimum`. -/
lemma fk_eq_rho {n : ℕ} (hn : n ≠ 0) {a : ℝ} (_ha : a ≠ 0) (hb : (1 : ℝ) - a ≠ 0) :
    fk n (kappa n a) (1 - a) = rho n a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)).symm⟩
  have hbn : ((1 : ℝ) - a) ^ (m + 1) ≠ 0 := pow_ne_zero _ hb
  simp only [fk, rho, kappa, Nat.add_sub_cancel]
  field_simp
  ring

/-! ### `b` minimises `f_κ`, and `f_κ` increases to the right of `b` -/

/-- The two supporting lines, added.  For any `y` to compare against `x`, both nonnegative, the
increment of `f_κ` is at least `(y - x) * (κ (n+1) x^n - n (1-x)^{n-1})`. -/
private lemma fk_supporting {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) (κ : ℝ) (hκ : 0 ≤ κ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    fk n κ x + (y - x) * (κ * ((n : ℝ) + 1) * x ^ n - (n : ℝ) * (1 - x) ^ (n - 1))
      ≤ fk n κ y := by
  have h1 : (1 - x) ^ n + (n : ℝ) * (1 - x) ^ (n - 1) * ((1 - y) - (1 - x)) ≤ (1 - y) ^ n :=
    pow_tangent_le hne hn0 (1 - x) (1 - y)
  have h2 : x ^ (n + 1) + ((n : ℝ) + 1) * x ^ n * (y - x) ≤ y ^ (n + 1) := by
    have := pow_tangent_le_of_nonneg (m := n + 1) (by omega) hx hy
    simpa using this
  have h2' : κ * (x ^ (n + 1) + ((n : ℝ) + 1) * x ^ n * (y - x)) ≤ κ * y ^ (n + 1) :=
    mul_le_mul_of_nonneg_left h2 hκ
  simp only [fk]
  nlinarith [h1, h2']

/-- **`b = 1 - a` minimises `f_κ` on `[0, ∞)`**, with minimum value `ρ_n(a)`.  This replaces the
paper's convexity argument. -/
theorem fk_min {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {x : ℝ} (hx : 0 ≤ x) :
    rho n a ≤ fk n (kappa n a) x := by
  have hb : (1 : ℝ) - a ≠ 0 := by linarith
  have hb0 : (0 : ℝ) ≤ 1 - a := by linarith
  have hκ : 0 ≤ kappa n a := by
    have : (0 : ℝ) < (1 - a) ^ n := by positivity
    apply div_nonneg
    · positivity
    · positivity
  have hcancel : kappa n a * ((n : ℝ) + 1) * (1 - a) ^ n
      - (n : ℝ) * (1 - (1 - a)) ^ (n - 1) = 0 := by
    rw [kappa_mul hb]
    simp
  have h := fk_supporting hne hn0 (kappa n a) hκ hb0 hx
  rw [hcancel, mul_zero, add_zero, fk_eq_rho hn0 (ne_of_gt ha0) hb] at h
  exact h

/-- **`f_κ` is monotone to the right of `b`**: this is what Case 2 of the main proof uses, where
the Perron eigenvalue `λ₁ ≥ β > b` compensates for the single dangerous eigenvalue. -/
theorem fk_mono {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {y z : ℝ} (hby : 1 - a ≤ y) (hy1 : y ≤ 1) (hyz : y ≤ z) :
    fk n (kappa n a) y ≤ fk n (kappa n a) z := by
  have hb : (1 : ℝ) - a ≠ 0 := by linarith
  have hb0 : (0 : ℝ) ≤ 1 - a := by linarith
  have hy0 : (0 : ℝ) ≤ y := le_trans hb0 hby
  have hz0 : (0 : ℝ) ≤ z := le_trans hy0 hyz
  have hκ : 0 ≤ kappa n a := by
    apply div_nonneg
    · positivity
    · have : (0 : ℝ) < (1 - a) ^ n := by positivity
      positivity
  -- the slope at `y` is nonnegative because it is nondecreasing and vanishes at `b`
  have hslope : 0 ≤ kappa n a * ((n : ℝ) + 1) * y ^ n - (n : ℝ) * (1 - y) ^ (n - 1) := by
    have hpow : (1 - a) ^ n ≤ y ^ n := pow_le_pow_left₀ hb0 hby n
    have h1y : (0 : ℝ) ≤ 1 - y := by linarith
    have hpow2 : (1 - y) ^ (n - 1) ≤ (1 - (1 - a)) ^ (n - 1) :=
      pow_le_pow_left₀ h1y (by linarith) (n - 1)
    have hk : kappa n a * ((n : ℝ) + 1) * (1 - a) ^ n = (n : ℝ) * a ^ (n - 1) := kappa_mul hb
    have hmul : kappa n a * ((n : ℝ) + 1) * (1 - a) ^ n
        ≤ kappa n a * ((n : ℝ) + 1) * y ^ n := by
      apply mul_le_mul_of_nonneg_left hpow
      positivity
    have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have ha' : (1 : ℝ) - (1 - a) = a := by ring
    rw [ha'] at hpow2
    have h3 : (n : ℝ) * (1 - y) ^ (n - 1) ≤ (n : ℝ) * a ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hpow2 hn0'
    linarith
  have h := fk_supporting hne hn0 (kappa n a) hκ hy0 hz0
  nlinarith [h, hslope, sub_nonneg.mpr hyz]

/-! ### `ρ_n` is strictly increasing, and the critical point -/

/-- `ρ_n(a) = (a^n + n a^{n-1})/(n+1)`, the form in which monotonicity is transparent. -/
lemma rho_eq_add {n : ℕ} (hn : n ≠ 0) (a : ℝ) :
    rho n a = (a ^ n + (n : ℝ) * a ^ (n - 1)) / ((n : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)).symm⟩
  simp only [rho, Nat.add_sub_cancel]
  push_cast
  ring

/-- **`ρ_n` is strictly increasing on `[0, ∞)`** (Lemma `lem:critical-point`). -/
theorem rho_strictMonoOn {n : ℕ} (hn : 2 ≤ n) : StrictMonoOn (rho n) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hn0 : n ≠ 0 := by omega
  have h1 : x ^ n < y ^ n := pow_lt_pow_left₀ hxy hx0 hn0
  have h2 : x ^ (n - 1) < y ^ (n - 1) := pow_lt_pow_left₀ hxy hx0 (by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [rho_eq_add hn0, rho_eq_add hn0, div_lt_div_iff₀ hden hden]
  have h3 : (n : ℝ) * x ^ (n - 1) < (n : ℝ) * y ^ (n - 1) := mul_lt_mul_of_pos_left h2 hnpos
  have hkey : x ^ n + (n : ℝ) * x ^ (n - 1) < y ^ n + (n : ℝ) * y ^ (n - 1) := by linarith
  exact mul_lt_mul_of_pos_right hkey hden

/-- The value `2 ^ (1-n)` attained by the balanced two-clique graphon, in the form it arises. -/
noncomputable def twoCliqueValue (n : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ n

lemma rho_half_lt {n : ℕ} (hn : 2 ≤ n) : rho n (1 / 2 : ℝ) < twoCliqueValue n := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)).symm⟩
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
  simp only [rho, twoCliqueValue, Nat.add_sub_cancel]
  rw [div_lt_iff₀ (by positivity)]
  have hhalf : (2 : ℝ) * (1 / 2 : ℝ) ^ (m + 1) = (1 / 2 : ℝ) ^ m := by
    rw [pow_succ]; ring
  rw [hhalf]
  nlinarith [hpos]

lemma lt_rho_one {n : ℕ} (hn : 2 ≤ n) : twoCliqueValue n < rho n 1 := by
  have hn0 : n ≠ 0 := by omega
  have hr : rho n 1 = 1 := by
    simp only [rho, one_pow, one_mul]
    rw [div_eq_one_iff_eq (by positivity)]
    ring
  rw [hr, twoCliqueValue]
  have h2 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  nlinarith [h2]

/-- **The critical point** `α*_n ∈ (1/2, 1)` with `ρ_n(α*_n) = 2 ^ (1-n)`
(Lemma `lem:critical-point`). -/
theorem exists_critical {n : ℕ} (hn : 2 ≤ n) :
    ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧ rho n a = twoCliqueValue n := by
  have hcont : ContinuousOn (rho n) (Icc (1 / 2 : ℝ) 1) := by
    apply Continuous.continuousOn
    unfold rho
    fun_prop
  have hmem : twoCliqueValue n ∈ Icc (rho n (1 / 2 : ℝ)) (rho n 1) :=
    ⟨(rho_half_lt hn).le, (lt_rho_one hn).le⟩
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1) hcont hmem
  refine ⟨a, ?_, ?_, hfa⟩
  · rcases lt_or_eq_of_le ha.1 with h | h
    · exact h
    · exact absurd (h ▸ hfa) (by simpa using (rho_half_lt hn).ne)
  · rcases lt_or_eq_of_le ha.2 with h | h
    · exact h
    · exact absurd (h ▸ hfa) (by simpa using (lt_rho_one hn).ne')


/-- `eq:two-point-convexity`: `(1-x)^n + x^n ≥ 2^{1-n}` for even `n`.  Two supporting lines at
`1/2`, whose slopes cancel. -/
theorem two_point_convexity {n : ℕ} (hne : Even n) (hn0 : n ≠ 0) (x : ℝ) :
    twoCliqueValue n ≤ (1 - x) ^ n + x ^ n := by
  have h1 := pow_tangent_le hne hn0 (1 / 2 : ℝ) x
  have h2 := pow_tangent_le hne hn0 (1 / 2 : ℝ) (1 - x)
  have hsum : ((1 : ℝ) / 2) ^ n + (n : ℝ) * ((1 : ℝ) / 2) ^ (n - 1) * (x - 1 / 2)
      + (((1 : ℝ) / 2) ^ n + (n : ℝ) * ((1 : ℝ) / 2) ^ (n - 1) * ((1 - x) - 1 / 2))
      = 2 * ((1 : ℝ) / 2) ^ n := by ring
  rw [twoCliqueValue]
  linarith [h1, h2, hsum]


end CycleCommonality
