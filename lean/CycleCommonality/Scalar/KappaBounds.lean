import CycleCommonality.Scalar.Rho

/-!
# Lemma `lem:kappa-bounds`: `κ* b* < 1` and `κ* < 27/13 < 2√2`

These are the only quantitative facts about the critical point used in the proof, and they are the
*tightest* step in the paper: numerically `κ*_n b*_n → 1` from below (0.98363 at `n = 4`, and
0.99999999995 at `n = 10^5`), so the chain

```
  (1-δ)^{n-1} ≥ 1 - (n-1)δ > 2n/(2n+1)      together with      2n+1+δ > 2n+1
```

is exactly what produces `(2n+1+δ)(1-δ)^{n-1} > 2n`.  There is no slack to spend on a coarser
estimate, so the proof below follows the paper's chain literally rather than handing the goal to
`nlinarith`.

Writing `δ = 2a - 1`, the critical equation `ρ_n(a) = 2^{1-n}` becomes `eq:delta-critical`:

```
  (1+δ)^{n-1} (2n+1+δ) = 2n+2.
```

Both Bernoulli applications are `one_add_mul_le_pow`.

Only `4 ≤ n` is used (not evenness): it enters through `(n-1)(2n+1) ≥ 27`.
-/

namespace CycleCommonality

open Set

/-! ### The critical equation in `δ` form -/

/-- `eq:delta-critical`: with `δ = 2a - 1`, the critical equation `ρ_n(a) = 2^{1-n}` reads
`(1+δ)^{n-1}(2n+1+δ) = 2n+2`. -/
lemma critical_delta {n : ℕ} (hn : n ≠ 0) {a : ℝ} (h : rho n a = twoCliqueValue n) :
    (2 * a) ^ (n - 1) * (2 * (a + (n : ℝ))) = 2 * ((n : ℝ) + 1) := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h' : a ^ (n - 1) * (a + (n : ℝ)) = 2 * (1 / 2 : ℝ) ^ n * ((n : ℝ) + 1) := by
    rw [rho, twoCliqueValue] at h
    field_simp at h
    linarith [h]
  have hpow : (2 : ℝ) ^ (n - 1) * a ^ (n - 1) = (2 * a) ^ (n - 1) := (mul_pow 2 a (n - 1)).symm
  have h2 : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hhalf : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc (2 * a) ^ (n - 1) * (2 * (a + (n : ℝ)))
      = ((2 : ℝ) ^ (n - 1) * 2) * (a ^ (n - 1) * (a + (n : ℝ))) := by rw [← hpow]; ring
    _ = (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ n * ((n : ℝ) + 1)) := by rw [h2, h']
    _ = 2 * ((n : ℝ) + 1) := by
        rw [show (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ n * ((n : ℝ) + 1))
          = 2 * ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) * ((n : ℝ) + 1) from by ring, hhalf]
        ring

/-! ### The bound on `δ` -/

/-- `eq:delta-bound`: `0 < δ < 1/((n-1)(2n+1))`.  Bernoulli applied to `(1+δ)^{n-1}`. -/
theorem delta_bound {n : ℕ} (hn : 4 ≤ n) {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (h : rho n a = twoCliqueValue n) :
    2 * a - 1 < 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) + 1)) := by
  set δ : ℝ := 2 * a - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ2 : δ < 1 := by rw [hδ]; linarith
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  -- the critical equation, rewritten
  have hcrit := critical_delta (by omega : n ≠ 0) h
  have h2a : (2 : ℝ) * a = 1 + δ := by rw [hδ]; ring
  have hsum : (2 : ℝ) * (a + (n : ℝ)) = 2 * (n : ℝ) + 1 + δ := by rw [hδ]; ring
  rw [h2a, hsum] at hcrit
  -- `(1+δ)^{n-1} = (2n+2)/(2n+1+δ) < (2n+2)/(2n+1)`
  have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 + δ := by linarith
  have hupper : (1 + δ) ^ (n - 1) * (2 * (n : ℝ) + 1) < 2 * (n : ℝ) + 2 := by
    have hp : (0 : ℝ) < (1 + δ) ^ (n - 1) := by positivity
    nlinarith [hcrit, hp, hδ0]
  -- Bernoulli
  have hbern : 1 + ((n : ℝ) - 1) * δ ≤ (1 + δ) ^ (n - 1) := by
    have := one_add_mul_le_pow (a := δ) (by linarith) (n - 1)
    rwa [hcast] at this
  -- combine
  have hkey : (1 + ((n : ℝ) - 1) * δ) * (2 * (n : ℝ) + 1) < 2 * (n : ℝ) + 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbern hden.le) hupper
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [hkey]

/-- `δ ≤ 1/27` for `n ≥ 4`, the numeric form used for the second bound. -/
theorem delta_lt_27 {n : ℕ} (hn : 4 ≤ n) {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (h : rho n a = twoCliqueValue n) :
    2 * a - 1 < 1 / 27 := by
  have hN : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbig : (27 : ℝ) ≤ ((n : ℝ) - 1) * (2 * (n : ℝ) + 1) := by nlinarith [hN]
  have h1 := delta_bound hn ha ha1 h
  have hpos : (0 : ℝ) < ((n : ℝ) - 1) * (2 * (n : ℝ) + 1) := by nlinarith [hN]
  have : 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) + 1)) ≤ 1 / 27 :=
    one_div_le_one_div_of_le (by norm_num) hbig
  linarith

/-! ### `κ b` in closed form, and its monotonicity -/

/-- `κ_n(a)(1-a) = (n/(n+1)) (a/(1-a))^{n-1}`, the form in which monotonicity in `a` is clear. -/
lemma kappa_mul_one_sub {n : ℕ} (hn : n ≠ 0) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    kappa n a * (1 - a) = ((n : ℝ) / ((n : ℝ) + 1)) * (a / (1 - a)) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)).symm⟩
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hbm : ((1 : ℝ) - a) ^ m ≠ 0 := by positivity
  simp only [kappa, Nat.add_sub_cancel, div_pow]
  rw [pow_succ]
  field_simp

/-- `κ_n(a)(1-a)` is monotone in `a` on `(0,1)`. -/
lemma kappa_mul_one_sub_mono {n : ℕ} (hn : n ≠ 0) {a c : ℝ} (ha0 : 0 < a) (hac : a ≤ c)
    (hc1 : c < 1) :
    kappa n a * (1 - a) ≤ kappa n c * (1 - c) := by
  have ha1 : a < 1 := lt_of_le_of_lt hac hc1
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hbc : (0 : ℝ) < 1 - c := by linarith
  have hratio : a / (1 - a) ≤ c / (1 - c) := by
    rw [div_le_div_iff₀ hb hbc]
    nlinarith [hac]
  have hnonneg : (0 : ℝ) ≤ a / (1 - a) := by positivity
  have hpow : (a / (1 - a)) ^ (n - 1) ≤ (c / (1 - c)) ^ (n - 1) :=
    pow_le_pow_left₀ hnonneg hratio (n - 1)
  rw [kappa_mul_one_sub hn ha0 ha1, kappa_mul_one_sub hn (lt_of_lt_of_le ha0 hac) hc1]
  apply mul_le_mul_of_nonneg_left hpow
  positivity

/-! ### The two bounds -/

/-- **`κ* b* < 1`** at the critical point.  This is the razor: the chain below is exactly tight. -/
theorem kappa_star_mul_lt_one {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n c = twoCliqueValue n) :
    kappa n c * (1 - c) < 1 := by
  set δ : ℝ := 2 * c - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ27 : δ < 1 / 27 := delta_lt_27 hn hc hc1 h
  have hN : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hb : (0 : ℝ) < 1 - c := by linarith
  -- the paper's chain: `(1-δ)^{n-1} > 2n/(2n+1)` and `2n+1+δ > 2n+1`
  have hbern : 1 - ((n : ℝ) - 1) * δ ≤ (1 - δ) ^ (n - 1) := by
    have := one_add_mul_le_pow (a := -δ) (by linarith) (n - 1)
    rw [hcast] at this
    calc 1 - ((n : ℝ) - 1) * δ = 1 + ((n : ℝ) - 1) * (-δ) := by ring
      _ ≤ (1 + -δ) ^ (n - 1) := this
      _ = (1 - δ) ^ (n - 1) := by ring_nf
  have hdb := delta_bound hn hc hc1 h
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hstep : ((n : ℝ) - 1) * δ < 1 / (2 * (n : ℝ) + 1) := by
    rw [lt_div_iff₀ hden]
    rw [lt_div_iff₀ (by positivity)] at hdb
    have hre : ((n : ℝ) - 1) * δ * (2 * (n : ℝ) + 1)
        = δ * (((n : ℝ) - 1) * (2 * (n : ℝ) + 1)) := by ring
    rw [hre]
    exact hdb
  have hne : (2 * (n : ℝ) + 1) ≠ 0 := ne_of_gt hden
  have hlow : 2 * (n : ℝ) / (2 * (n : ℝ) + 1) < (1 - δ) ^ (n - 1) := by
    have hid : 2 * (n : ℝ) / (2 * (n : ℝ) + 1) = 1 - 1 / (2 * (n : ℝ) + 1) := by
      rw [eq_sub_iff_add_eq, div_add_div _ _ hne hne, div_eq_one_iff_eq (by positivity)]
      ring
    rw [hid]
    linarith [hbern, hstep]
  have hlowpos : (0 : ℝ) < 2 * (n : ℝ) / (2 * (n : ℝ) + 1) := by positivity
  -- multiply the two strict lower bounds
  have hprod : 2 * (n : ℝ) < (2 * (n : ℝ) + 1 + δ) * (1 - δ) ^ (n - 1) := by
    have h1 : (2 * (n : ℝ) + 1) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1)) = 2 * (n : ℝ) := by
      field_simp
    calc 2 * (n : ℝ) = (2 * (n : ℝ) + 1) * (2 * (n : ℝ) / (2 * (n : ℝ) + 1)) := h1.symm
      _ < (2 * (n : ℝ) + 1 + δ) * (1 - δ) ^ (n - 1) := by
          apply mul_lt_mul' (by linarith) hlow hlowpos.le (by linarith)
  -- translate back: `κ c (1-c) < 1` is `2n < (2n+1+δ)(1-δ)^{n-1}`
  have hcrit := critical_delta (by omega : n ≠ 0) h
  have h2c : (2 : ℝ) * c = 1 + δ := by rw [hδ]; ring
  have hsum : (2 : ℝ) * (c + (n : ℝ)) = 2 * (n : ℝ) + 1 + δ := by rw [hδ]; ring
  rw [h2c, hsum] at hcrit
  have h2b : (2 : ℝ) * (1 - c) = 1 - δ := by rw [hδ]; ring
  -- `κ c (1-c) = n (2c)^{n-1} / ((n+1) (2(1-c))^{n-1})`
  have hcpos : (0 : ℝ) < c := by linarith
  have hdpos : (0 : ℝ) < 1 - δ := by linarith
  have hd : (0 : ℝ) < (1 - δ) ^ (n - 1) := pow_pos hdpos _
  have hcd : c / (1 - c) = (1 + δ) / (1 - δ) := by
    rw [← h2c, ← h2b, mul_div_mul_left _ _ (two_ne_zero)]
  have hkey : kappa n c * (1 - c)
      = ((n : ℝ) * (1 + δ) ^ (n - 1)) / (((n : ℝ) + 1) * (1 - δ) ^ (n - 1)) := by
    rw [kappa_mul_one_sub (by omega : n ≠ 0) hcpos hc1, hcd, div_pow]
    field_simp
  rw [hkey, div_lt_one (by positivity)]
  -- `n (1+δ)^{n-1} < (n+1)(1-δ)^{n-1}` follows from the critical equation and `hprod`
  have hfac : (1 + δ) ^ (n - 1) = (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1 + δ) := by
    rw [eq_div_iff (by linarith)]
    linarith [hcrit]
  rw [hfac, ← mul_div_assoc, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (n : ℝ) + 1 + δ)]
  nlinarith [mul_lt_mul_of_pos_left hprod (show (0:ℝ) < (n : ℝ) + 1 by positivity)]

/-- **`κ b < 1` for every `0 < a ≤ α*`** (`eq:kappa-bounds-all-a`, first half). -/
theorem kappa_mul_lt_one {n : ℕ} (hn : 4 ≤ n) {a c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n c = twoCliqueValue n) (ha0 : 0 < a) (hac : a ≤ c) :
    kappa n a * (1 - a) < 1 :=
  lt_of_le_of_lt (kappa_mul_one_sub_mono (by omega) ha0 hac hc1)
    (kappa_star_mul_lt_one hn hc hc1 h)

/-- **`κ < 27/13`** for every `0 < a ≤ α*` (`eq:kappa-bounds-all-a`, second half).
`1/κ > b = 1 - a ≥ 1 - α* > 13/27`. -/
theorem kappa_lt {n : ℕ} (hn : 4 ≤ n) {a c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n c = twoCliqueValue n) (ha0 : 0 < a) (hac : a ≤ c) :
    kappa n a < 27 / 13 := by
  have ha1 : a < 1 := lt_of_le_of_lt hac hc1
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hδ27 : 2 * c - 1 < 1 / 27 := delta_lt_27 hn hc hc1 h
  have hbc : (13 : ℝ) / 27 < 1 - c := by linarith
  have hba : (13 : ℝ) / 27 < 1 - a := by linarith
  have hmul := kappa_mul_lt_one hn hc hc1 h ha0 hac
  rw [← lt_div_iff₀ hb] at hmul
  calc kappa n a < 1 / (1 - a) := hmul
    _ < 27 / 13 := by
        rw [div_lt_div_iff₀ hb (by norm_num)]
        linarith

/-- `κ² < 8`, i.e. `κ < 2√2`: what "at most one dangerous eigenvalue" needs. -/
theorem kappa_sq_lt_eight {n : ℕ} (hn : 4 ≤ n) {a c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1)
    (h : rho n c = twoCliqueValue n) (ha0 : 0 < a) (hac : a ≤ c) :
    (kappa n a) ^ 2 < 8 := by
  have h1 := kappa_lt hn hc hc1 h ha0 hac
  have h0 : 0 ≤ kappa n a := by
    have ha1 : a < 1 := lt_of_le_of_lt hac hc1
    apply div_nonneg
    · positivity
    · have : (0 : ℝ) < (1 - a) ^ n := by
        apply pow_pos; linarith
      positivity
  nlinarith [h1, h0]

end CycleCommonality
