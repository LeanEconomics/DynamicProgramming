/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.BalancedGrowth
import NeoclassicalGrowth.RXHayashi
import NeoclassicalGrowth.RXTrend
import NeoclassicalGrowth.RXCapacity
import NeoclassicalGrowth.RBUtility
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Balanced-growth preferences and extensions of the RBC model

AKMM, §14.4.4, p. 427, and §14.5, pp. 432–434.

* **KPR preferences** `(c v(1 − ℓ))^{1−σ}/(1 − σ)` are AKMM Chapter 12's `kprU σ (v^{1−σ})`
  (`ext_kpr_form`), so the marginal rate of substitution is homogeneous of degree one in `c`
  (`ext_kpr_homog`, from Chapter 12's `kpr_homog`) and balanced growth with constant hours holds
  (Chapter 12's `eq_12_37_if`). With `σ = 1` and the Cobb–Douglas aggregator,
  `ln(c^{1−φ}(1 − ℓ)^φ) = (1 − φ)ln c + φ ln(1 − ℓ)` (`ext_cd_log`).
* The steady-state interest rate is `R = g^σ/β` (`ext_bgp_interest`), not `gσ/β`
  (`ext_interest_printed_false`).
* **Adjustment costs** (§14.5.2): `Ψ(i, k) = (ψ/2)(i/k − δ)²k` (`adjPsi`) is homogeneous of degree
  one (`adj_homog`; Miao's form for `Φ(i, k) = i − Ψ(i, k)`, `adj_Phi_homog`), zero at
  maintenance investment `i = δk` and nonnegative (`adj_maintenance`), convex in `i`
  (`adj_convex_i`) and jointly convex for `k > 0` (`adj_jointly_convex`).
  The accumulation `k′ = (1 − δ)k + i − Ψ(i, k)` has `∂k′/∂i = 1 − ψ(i/k − δ)` (`adj_dk_di`),
  so the shadow price of installed capital is exactly `q = 1/(1 − ψ(i/k − δ))`
  (`adj_shadow_price`); the printed `1 + ψ(i/k − δ)` agrees only at `i = δk` (`adj_q_printed_iff`,
  counterexample `adj_q_printed_false`) and is its first-order approximation, the error being
  `ψ²x²/(1 − ψx)` (`adj_q_first_order`); it is exact when the cost is paid out of output
  (`adj_shadow_price_resource`). Marginal `q` equals average `q` (Hayashi) by Miao's
  `proposition_14_3_1`, applied to this `Φ` (`adj_hayashi`).
* **Utilisation** (§14.5.3): with `y = z(uk)^αℓ^{1−α}`, the Solow residual computed with
  measured capital is `log z + α log u` (`ext_util_solow`); utilisation amplifies TFP shocks
  (Miao's `rx_cu_amplification`).
* **Investment-specific shocks** (§14.5.4): with `k′ = (1 − δ)k + qi`, the planner's shadow price
  of capital in consumption units is `1/q` (`ext_ist_price`; Miao's `rx_ist_price`: it falls when
  `q` rises).
* **Government spending** (§14.5.4): in the static economy `c = zℓ − g` with log–log utility,
  hours are `ℓ = (z + φg)/((1 + φ)z)` and rise with `g` (the negative income effect,
  `ext_gov_hours`, `ext_gov_hours_increasing`); if `g` is a perfect substitute for `c`
  (`C = c + g`), hours are `1/(1 + φ)` whatever `g` (`ext_gov_perfect_subst`).
-/

namespace AKMM.RealBusinessCycles

open Filter Topology Miao.NeoclassicalGrowth

/-! ### KPR preferences -/

/-- AKMM, p. 427: for `σ ≠ 1`, `c > 0`, `v > 0`, the KPR utility `(c v(x))^{1−σ}/(1 − σ)` is AKMM
Chapter 12's `kprU σ (v^{1−σ}) c x`. -/
theorem ext_kpr_form {σ c : ℝ} {v : ℝ → ℝ} (hσ : σ ≠ 1) (hc : 0 < c) {x : ℝ} (hv : 0 < v x) :
    (c * v x) ^ (1 - σ) / (1 - σ) = AKMM.LaborSupply.kprU σ (fun y => v y ^ (1 - σ)) c x := by
  simp only [AKMM.LaborSupply.kprU, hσ, ↓reduceIte, Real.mul_rpow hc.le hv.le]

/-- AKMM, p. 427, balanced growth: for KPR utility the marginal rate of substitution
`U_x/U_c` is homogeneous of degree one in consumption, `MRS(gc) = g·MRS(c)` (`g, c > 0`), so
consumption and the wage can grow at the same rate with constant hours. -/
theorem ext_kpr_homog {σ g c x : ℝ} {v v' : ℝ → ℝ} (hg : 0 < g) (hc : 0 < c) :
    AKMM.LaborSupply.kprUl σ v' (g * c) x / AKMM.LaborSupply.kprUC σ v (g * c) x =
      g * (AKMM.LaborSupply.kprUl σ v' c x / AKMM.LaborSupply.kprUC σ v c x) := by
  obtain ⟨h1, h2⟩ := AKMM.LaborSupply.kpr_homog (σ := σ) (v := v) (v' := v') (l := x) hg hc
  rw [h1, h2]
  have hp : 0 < g ^ (-σ) := Real.rpow_pos_of_pos hg _
  have e : g ^ (1 - σ) = g * g ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hg, Real.rpow_one]
  rw [e]
  by_cases h0 : AKMM.LaborSupply.kprUC σ v c x = 0
  · simp [h0]
  · field_simp

/-- AKMM, p. 427: with `σ = 1` and the Cobb–Douglas aggregator,
`ln(c^{1−φ}(1 − ℓ)^φ) = (1 − φ)ln c + φ ln(1 − ℓ)`. -/
theorem ext_cd_log {φ c ℓ : ℝ} (hc : 0 < c) (hℓ : ℓ < 1) :
    Real.log (c ^ (1 - φ) * (1 - ℓ) ^ φ) = (1 - φ) * Real.log c + φ * Real.log (1 - ℓ) := by
  have h1 : 0 < 1 - ℓ := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hc, Real.log_rpow h1]

/-- **AKMM, p. 427, the steady-state interest rate, corrected.** If marginal utility has the
KPR form `c^{−σ}w` (`w > 0` the constant leisure factor) and consumption grows at the gross rate
`g > 0`, the Euler equation `c^{−σ}w = βR(gc)^{−σ}w` holds iff `R = g^σ/β`. -/
theorem ext_bgp_interest {σ β g c w R : ℝ} (hβ : 0 < β) (hg : 0 < g) (hc : 0 < c) (hw : 0 < w) :
    c ^ (-σ) * w = β * R * ((g * c) ^ (-σ) * w) ↔ R = g ^ σ / β := by
  have hcs : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have hgs : 0 < g ^ σ := Real.rpow_pos_of_pos hg _
  have e : (g * c) ^ (-σ) = c ^ (-σ) / g ^ σ := by
    rw [Real.mul_rpow hg.le hc.le, Real.rpow_neg hg.le]
    field_simp
  rw [e]
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith
  · intro h
    rw [h]
    field_simp

/-- AKMM, p. 427: the printed "growth rate of consumption times `σ` divided by `β`" is not the
steady-state interest rate: at `g = 1.02`, `σ = 2`, `β = 0.99`, `g^σ/β ≠ gσ/β`. -/
theorem ext_interest_printed_false : (1.02 : ℝ) ^ (2 : ℝ) / 0.99 ≠ 1.02 * 2 / 0.99 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-! ### Capital adjustment costs -/

/-- AKMM, p. 433: the adjustment cost `Ψ(i, k) = (ψ/2)(i/k − δ)²k`. -/
noncomputable def adjPsi (ψ δ i k : ℝ) : ℝ := ψ / 2 * (i / k - δ) ^ 2 * k

/-- AKMM, p. 433, footnote 15: `Ψ` is homogeneous of degree one in `(i, k)`. -/
theorem adj_homog (ψ δ : ℝ) {l : ℝ} (hl : 0 < l) (i k : ℝ) :
    adjPsi ψ δ (l * i) (l * k) = l * adjPsi ψ δ i k := by
  unfold adjPsi
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · rw [mul_div_mul_left _ _ hl.ne']
    ring

/-- The net investment function `Φ(i, k) = i − Ψ(i, k)` of `k′ = (1 − δ)k + Φ(i, k)` is
homogeneous of degree one in Miao's form (the hypothesis of `proposition_14_3_1`). -/
theorem adj_Phi_homog (ψ δ : ℝ) :
    ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l →
      (fun q : ℝ × ℝ => q.1 - adjPsi ψ δ q.1 q.2) (l * p.1, l * p.2) =
        l * (fun q : ℝ × ℝ => q.1 - adjPsi ψ δ q.1 q.2) p := by
  intro l p hl
  simp only [adj_homog ψ δ hl]
  ring

/-- AKMM, p. 433: replacing depreciated capital is costless, `Ψ(δk, k) = 0`, and `Ψ ≥ 0` for
`ψ ≥ 0`, `k ≥ 0`. -/
theorem adj_maintenance {ψ δ k : ℝ} (hk : k ≠ 0) :
    adjPsi ψ δ (δ * k) k = 0 ∧ ∀ i, 0 ≤ ψ → 0 ≤ k → 0 ≤ adjPsi ψ δ i k := by
  refine ⟨by unfold adjPsi; rw [mul_div_cancel_right₀ _ hk]; ring, fun i hψ hk0 => ?_⟩
  unfold adjPsi
  positivity

/-- AKMM, p. 433: the adjustment cost is convex in investment (`ψ ≥ 0`, `k > 0`). -/
theorem adj_convex_i {ψ δ k : ℝ} (hψ : 0 ≤ ψ) (hk : 0 < k) :
    ConvexOn ℝ Set.univ (fun i => adjPsi ψ δ i k) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [adjPsi, smul_eq_mul]
  have hk' : k ≠ 0 := hk.ne'
  have e : ∀ u : ℝ, ψ / 2 * (u / k - δ) ^ 2 * k = ψ / (2 * k) * (u - δ * k) ^ 2 := fun u => by
    field_simp
  rw [e, e, e]
  have hc : 0 ≤ ψ / (2 * k) := by positivity
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : (a * x + (1 - a) * y - δ * k) ^ 2 ≤
      a * (x - δ * k) ^ 2 + (1 - a) * (y - δ * k) ^ 2 := by
    nlinarith [sq_nonneg (x - y), mul_nonneg ha hb]
  nlinarith [mul_le_mul_of_nonneg_left key hc]

/-- AKMM, p. 433: `Ψ` is jointly convex in `(i, k)` on `k > 0` (`ψ ≥ 0`): it is
`(ψ/2)(i − δk)²/k`, a quadratic-over-linear function. -/
theorem adj_jointly_convex {ψ δ : ℝ} (hψ : 0 ≤ ψ) :
    ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2} (fun p => adjPsi ψ δ p.1 p.2) := by
  have hcv : Convex ℝ {p : ℝ × ℝ | 0 < p.2} := by
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hp hq ⊢
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_mul, zero_add, show b = 1 by linarith, one_mul]; exact hq
    · have := mul_pos h hp; nlinarith [mul_nonneg hb hq.le]
  refine ⟨hcv, fun p hp q hq a b ha hb hab => ?_⟩
  simp only [Set.mem_ofPred_eq] at hp hq
  simp only [adjPsi, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  set x1 := p.1 - δ * p.2
  set x2 := q.1 - δ * q.2
  have e : ∀ u k : ℝ, k ≠ 0 → ψ / 2 * (u / k - δ) ^ 2 * k = ψ / 2 * ((u - δ * k) ^ 2 / k) :=
    fun u k hk => by field_simp
  have hk : 0 < a * p.2 + b * q.2 := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; rw [zero_mul, zero_add, show b = 1 by linarith, one_mul]; exact hq
    · have := mul_pos h hp; nlinarith [mul_nonneg hb hq.le]
  rw [e _ _ hk.ne', e _ _ hp.ne', e _ _ hq.ne']
  have hx : a * p.1 + b * q.1 - δ * (a * p.2 + b * q.2) = a * x1 + b * x2 := by
    simp only [x1, x2]; ring
  rw [hx]
  -- `(a x₁ + b x₂)²/(a k₁ + b k₂) ≤ a x₁²/k₁ + b x₂²/k₂`
  have key : (a * x1 + b * x2) ^ 2 / (a * p.2 + b * q.2) ≤
      a * (x1 ^ 2 / p.2) + b * (x2 ^ 2 / q.2) := by
    rw [div_le_iff₀ hk]
    have e2 : (a * (x1 ^ 2 / p.2) + b * (x2 ^ 2 / q.2)) * (a * p.2 + b * q.2) =
        (a * x1 + b * x2) ^ 2 + a * b * (x1 * q.2 - x2 * p.2) ^ 2 / (p.2 * q.2) := by
      field_simp; ring
    rw [e2]
    have : 0 ≤ a * b * (x1 * q.2 - x2 * p.2) ^ 2 / (p.2 * q.2) := by positivity
    linarith
  have hc : 0 ≤ ψ / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hc]

/-- AKMM, p. 433: in `k′ = (1 − δ)k + i − Ψ(i, k)`, `∂k′/∂i = 1 − ψ(i/k − δ)` (`k ≠ 0`). -/
theorem adj_dk_di {ψ δ i k : ℝ} (hk : k ≠ 0) :
    HasDerivAt (fun j => (1 - δ) * k + j - adjPsi ψ δ j k) (1 - ψ * (i / k - δ)) i := by
  have h1 : HasDerivAt (fun j => j / k - δ) (1 / k) i := by
    simpa using ((hasDerivAt_id i).div_const k).sub_const δ
  have h2 := ((h1.pow 2).const_mul (ψ / 2)).mul_const k
  have h3 := ((hasDerivAt_id i).const_add ((1 - δ) * k)).sub h2
  convert h3 using 1
  · funext j; simp [adjPsi]
  · simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp

/-- **AKMM, p. 433, the shadow price of installed capital, corrected.** If investment `i`
maximises `u(y − j) + W((1 − δ)k + j − Ψ(j, k))` locally, with `u′(c) = u₁ ≠ 0` and
`W′(k′) = w₁`, then `(w₁/u₁)(1 − ψ(i/k − δ)) = 1`: Tobin's `q = w₁/u₁` (the value of a unit of
installed capital in consumption units) is `1/(1 − ψ(i/k − δ))`. -/
theorem adj_shadow_price {ψ δ i k y u1 w1 : ℝ} {u W : ℝ → ℝ} (hk : k ≠ 0)
    (hu : HasDerivAt u u1 (y - i)) (hW : HasDerivAt W w1 ((1 - δ) * k + i - adjPsi ψ δ i k))
    (hmax : IsLocalMax (fun j => u (y - j) + W ((1 - δ) * k + j - adjPsi ψ δ j k)) i)
    (hu1 : u1 ≠ 0) :
    w1 / u1 * (1 - ψ * (i / k - δ)) = 1 ∧
      (1 - ψ * (i / k - δ) ≠ 0 → w1 / u1 = 1 / (1 - ψ * (i / k - δ))) := by
  have hc : HasDerivAt (fun j => y - j) (-1) i := by simpa using (hasDerivAt_id i).const_sub y
  have hd := (hu.comp i hc).add (hW.comp i (adj_dk_di hk))
  have h0 := hmax.hasDerivAt_eq_zero hd
  have e : w1 * (1 - ψ * (i / k - δ)) = u1 := by linarith
  have h1 : w1 / u1 * (1 - ψ * (i / k - δ)) = 1 := by
    rw [div_mul_eq_mul_div, e, div_self hu1]
  exact ⟨h1, fun hne => by rw [eq_div_iff hne, h1]⟩

/-- AKMM, p. 433: the printed `q = 1 + ψ(i/k − δ)` equals the exact `1/(1 − ψ(i/k − δ))` iff
`ψ(i/k − δ) = 0` (when `ψ(i/k − δ) ≠ 1`). -/
theorem adj_q_printed_iff {u : ℝ} (hu : 1 - u ≠ 0) : 1 / (1 - u) = 1 + u ↔ u = 0 := by
  rw [div_eq_iff hu]
  constructor
  · intro h
    have : u ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  · intro h; rw [h]; ring

/-- AKMM, p. 433: counterexample to the printed shadow price: `ψ = 1`, `i/k − δ = 1/2` gives
`1/(1 − ψ(i/k − δ)) = 2` but `1 + ψ(i/k − δ) = 3/2`. -/
theorem adj_q_printed_false : (1 : ℝ) / (1 - 1 * (1 / 2)) ≠ 1 + 1 * (1 / 2) := by norm_num

/-- The printed `1 + u` is the first-order approximation of `1/(1 − u)`:
`1/(1 − u) − (1 + u) = u²/(1 − u)`. -/
theorem adj_q_first_order {u : ℝ} (hu : 1 - u ≠ 0) : 1 / (1 - u) - (1 + u) = u ^ 2 / (1 - u) := by
  field_simp
  ring

/-- The printed `q` is exact when the adjustment cost is paid out of output: if `i` maximises
`u(y − j − Ψ(j, k)) + W((1 − δ)k + j)` locally (`u′ = u₁ ≠ 0`, `W′ = w₁`), then
`w₁/u₁ = 1 + ψ(i/k − δ)`. -/
theorem adj_shadow_price_resource {ψ δ i k y u1 w1 : ℝ} {u W : ℝ → ℝ} (hk : k ≠ 0)
    (hu : HasDerivAt u u1 (y - i - adjPsi ψ δ i k)) (hW : HasDerivAt W w1 ((1 - δ) * k + i))
    (hmax : IsLocalMax (fun j => u (y - j - adjPsi ψ δ j k) + W ((1 - δ) * k + j)) i)
    (hu1 : u1 ≠ 0) : w1 / u1 = 1 + ψ * (i / k - δ) := by
  have hdk := adj_dk_di (ψ := ψ) (δ := δ) (i := i) hk
  have hpsi : HasDerivAt (fun j => adjPsi ψ δ j k) (ψ * (i / k - δ)) i := by
    have := (((hasDerivAt_id i).const_add ((1 - δ) * k)).sub hdk)
    convert this using 1
    · funext j; simp
    · ring
  have hy : HasDerivAt (fun j => y - j) (-1) i := by simpa using (hasDerivAt_id i).const_sub y
  have hc : HasDerivAt (fun j => y - j - adjPsi ψ δ j k) (-1 - ψ * (i / k - δ)) i :=
    hy.sub hpsi
  have hl : HasDerivAt (fun j => (1 - δ) * k + j) 1 i := by
    simpa using (hasDerivAt_id i).const_add ((1 - δ) * k)
  have hd := (hu.comp i hc).add (hW.comp i hl)
  have h0 := hmax.hasDerivAt_eq_zero hd
  rw [div_eq_iff hu1]
  linarith

/-- **Hayashi's theorem for the AKMM adjustment cost** (AKMM, p. 433; Miao's
`proposition_14_3_1`): with `Φ(i, k) = i − Ψ(i, k)` (homogeneous of degree one, `adj_Phi_homog`)
and a linearly homogeneous production function, marginal `q` equals average `q`. -/
theorem adj_hayashi {S : Type*} [Fintype S] (T : RXTree S) {F : ℝ × ℝ → ℝ} {ψ δ β : ℝ}
    {Kn I N z w Λ Q a b FK FN P : List S → ℝ}
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p)
    (hΦd : ∀ h s, rx_HasPartials (fun q : ℝ × ℝ => q.1 - adjPsi ψ δ q.1 q.2) (a (s :: h))
      (b (s :: h)) (I (s :: h), Kn h))
    (hFd : ∀ h s, rx_HasPartials F (FK (s :: h)) (FN (s :: h)) (Kn h, N (s :: h)))
    (hacc : ∀ h s, Kn (s :: h) = (1 - δ) * Kn h + (I (s :: h) - adjPsi ψ δ (I (s :: h)) (Kn h)))
    (h48 : ∀ h s, Q (s :: h) * a (s :: h) = 1)
    (hw : ∀ h s, w (s :: h) = z (s :: h) * FN (s :: h))
    (h49 : ∀ h, Λ h * Q h = β * rx_E T (fun g => Λ g * (z g * FK g + Q g * (1 - δ + b g))) h)
    (hΛ : ∀ h, 0 < Λ h) (h : List S)
    (hP : Tendsto (fun n => ∑ j ∈ Finset.range n,
      rx_pv T (rx_sdf β Λ) (j + 1) (rx_div F z w N I Kn) h) atTop (𝓝 (P h)))
    (htvc : Tendsto (fun n => rx_pv T (rx_sdf β Λ) n (fun g => Q g * Kn g) h) atTop (𝓝 0)) :
    Q h * Kn h = P h ∧ (0 < Kn h → Q h = P h / Kn h) :=
  proposition_14_3_1 T (adj_Phi_homog ψ δ) hFhom hΦd hFd hacc h48 hw h49 hΛ h hP htvc

/-! ### Utilisation, investment-specific shocks, government spending -/

/-- AKMM, pp. 426–427 and 433: with variable utilisation, `y = z(uk)^αℓ^{1−α}`, the Solow residual
computed with measured capital `k` is `log y − α log k − (1 − α) log ℓ = log z + α log u`: it
mismeasures TFP by `α log u`. -/
theorem ext_util_solow {α z u k ℓ : ℝ} (hz : 0 < z) (hu : 0 < u) (hk : 0 < k) (hℓ : 0 < ℓ) :
    Real.log (z * (u * k) ^ α * ℓ ^ (1 - α)) - α * Real.log k - (1 - α) * Real.log ℓ =
      Real.log z + α * Real.log u := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hz.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow hℓ, Real.log_mul hu.ne' hk.ne']
  ring

/-- AKMM, p. 434: with investment-specific technology `k′ = (1 − δ)k + qi` (`q ≠ 0`), if `i`
maximises `u(y − j) + W((1 − δ)k + qj)` locally with `u′ = u₁ ≠ 0`, `W′ = w₁`, the shadow price
of capital in consumption units is `w₁/u₁ = 1/q`. -/
theorem ext_ist_price {δ k q y i u1 w1 : ℝ} {u W : ℝ → ℝ} (hq : q ≠ 0)
    (hu : HasDerivAt u u1 (y - i)) (hW : HasDerivAt W w1 ((1 - δ) * k + q * i))
    (hmax : IsLocalMax (fun j => u (y - j) + W ((1 - δ) * k + q * j)) i) (hu1 : u1 ≠ 0) :
    w1 / u1 = 1 / q := by
  have hc : HasDerivAt (fun j => y - j) (-1) i := by simpa using (hasDerivAt_id i).const_sub y
  have hl : HasDerivAt (fun j => (1 - δ) * k + q * j) q i := by
    simpa using ((hasDerivAt_id i).const_mul q).const_add ((1 - δ) * k)
  have h0 := hmax.hasDerivAt_eq_zero ((hu.comp i hc).add (hW.comp i hl))
  rw [div_eq_div_iff hu1 hq]
  linarith

/-- AKMM, p. 434: government spending financed out of output, `c = zℓ − g`, with log–log
utility: the intratemporal condition `z/c = φ/(1 − ℓ)` holds iff `ℓ = (z + φg)/((1 + φ)z)`
(`z > 0`, `c > 0`, `ℓ < 1`). -/
theorem ext_gov_hours {φ z g ℓ : ℝ} (hφ : 0 ≤ φ) (hz : 0 < z) (hc : 0 < z * ℓ - g) (hℓ : ℓ < 1) :
    z / (z * ℓ - g) = φ / (1 - ℓ) ↔ ℓ = (z + φ * g) / ((1 + φ) * z) := by
  have h1 : 0 < 1 - ℓ := by linarith
  have h2 : 0 < (1 + φ) * z := by positivity
  rw [div_eq_div_iff hc.ne' h1.ne', eq_div_iff h2.ne']
  constructor <;> intro h <;> linarith

/-- AKMM, p. 434: "if this elasticity is low, government spending is more like a tax … increasing
labor supply due to a negative income effect": hours `(z + φg)/((1 + φ)z)` strictly increase in
`g` (`φ > 0`). -/
theorem ext_gov_hours_increasing {φ z : ℝ} (hφ : 0 < φ) (hz : 0 < z) :
    StrictMono (fun g => (z + φ * g) / ((1 + φ) * z)) := by
  intro g g' hg
  have h2 : 0 < (1 + φ) * z := by positivity
  exact div_lt_div_of_pos_right (by nlinarith) h2

/-- AKMM, p. 434: "if the elasticity is very high, government spending is like private
consumption": if utility depends on `C = c + g` (perfect substitutes; the CES aggregate with
`ϕ = 1`, `θ = 1/2`, up to scale) and `c = zℓ − g`, then `C = zℓ` and the condition
`z/C = φ/(1 − ℓ)` gives `ℓ = 1/(1 + φ)`, whatever `g`. -/
theorem ext_gov_perfect_subst {φ z g ℓ : ℝ} (hφ : 0 ≤ φ) (hz : 0 < z) (hℓ0 : 0 < ℓ)
    (hℓ1 : ℓ < 1) :
    (z * ℓ - g) + g = z * ℓ ∧
      (z / ((z * ℓ - g) + g) = φ / (1 - ℓ) ↔ ℓ = 1 / (1 + φ)) := by
  have h1 : 0 < 1 - ℓ := by linarith
  refine ⟨by ring, ?_⟩
  rw [sub_add_cancel, div_eq_div_iff (by positivity) h1.ne', eq_div_iff (by positivity)]
  constructor
  · intro h
    have : z * (1 - ℓ) = z * (φ * ℓ) := by linarith
    have := mul_left_cancel₀ hz.ne' this
    linarith
  · intro h
    nlinarith

end AKMM.RealBusinessCycles
