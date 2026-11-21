/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Interest-rate pegs and interest-rate rules

AKMM, §17.3.3, "Price level indeterminacy under pure interest rate rules" and "Interest rate rules
with a target", pp. 515–516, with footnotes 14–15.

**The CIA peg** (`u(c) + l`, `z = 1`). `pegIsEquilibrium` collects the conditions of p. 515.
* `peg_pins`: every equilibrium has `q_t = β`, `p_{m,t}/p_{m,t+1} = β(1 + i_t)` and
  `u′(c_{t+1}) = 1 + i_t`: the peg determines inflation and consumption from `t = 1` on.
* `peg_c0`: initial consumption is `c₀ = min(p_{m,0}M₀, c₀*)`, `u′(c₀*) = 1`.
* `peg_exists`: every `p_{m,0} > 0` indexes an equilibrium; `peg_real_indeterminacy`: distinct
  `p_{m,0} ≤ c₀*/M₀` give distinct `c₀` (real, not just nominal, indeterminacy).

**Rules `i_t = φ(P_t/P̃_t)`** (17.39) with a constant real rate.
* `eq_17_40`: `x_{t+1} = x_t(1 + φ(x_t))/(1 + ĩ)`, `x = P/P̃`, `ĩ = φ(1)`; `rule_target`.
* `rule_map_hasDerivAt`: the slope at `1` is `1 + φ′(1)/(1 + ĩ)`.
* `rule_determinate`: if the slope has modulus `> 1` the only solution staying near `1` is
  `x ≡ 1`; `rule_indeterminate`: if it has modulus `< 1`, every start near `1` gives a solution
  converging to `1`.
* `rule_phi_pos_determinate`: `φ′(1) > 0` gives determinacy (the book's claim);
  `rule_phi_neg_indeterminate`: `−2(1 + ĩ) < φ′(1) < 0` gives indeterminacy;
  `rule_phi_very_neg_determinate` and `rule_printed_counterexample`: for `φ′(1) < −2(1 + ĩ)` the
  solution is again unique, so the printed "if `φ′(1) < 0` there is indeterminacy" is false.
* `rule_knife_edge`: footnote 15 for an affine rule with `φ′(1) = 0`: every constant ratio solves
  (17.40).
-/

open Filter Topology

namespace AKMM.Money

/-! ### The cash-in-advance interest-rate peg -/

/-- AKMM, p. 515: the equilibrium conditions of the CIA model with `u(c) + l`, `z = 1` and a
peg `i_t`: `c_t ≤ p_{m,t}M_t`, `u′(c_t) = λ_t + µ_t`, `1 = λ_t`, `q_tλ_t = βλ_{t+1}`,
`λ_tp_{m,t}/p_{m,t+1} = β(λ_{t+1} + µ_{t+1})`, the Fisher equation
`q_t(1 + i_t) = p_{m,t}/p_{m,t+1}`, and `µ_t ≥ 0` with complementary slackness. -/
def pegIsEquilibrium (β : ℝ) (du : ℝ → ℝ) (i pm M c lam mu q : ℕ → ℝ) : Prop :=
  ∀ t, 0 < pm t ∧ 0 < c t ∧ c t ≤ pm t * M t ∧ du (c t) = lam t + mu t ∧ lam t = 1 ∧
    q t * lam t = β * lam (t + 1) ∧ lam t * (pm t / pm (t + 1)) = β * (lam (t + 1) + mu (t + 1)) ∧
    q t * (1 + i t) = pm t / pm (t + 1) ∧ 0 ≤ mu t ∧ mu t * (pm t * M t - c t) = 0

/-- **AKMM, p. 515: the peg determines inflation.** In every equilibrium `q_t = β`,
`p_{m,t}/p_{m,t+1} = β(1 + i_t)` and `u′(c_{t+1}) = 1 + i_t`. -/
theorem peg_pins {β : ℝ} {du : ℝ → ℝ} {i pm M c lam mu q : ℕ → ℝ}
    (h : pegIsEquilibrium β du i pm M c lam mu q) (t : ℕ) :
    q t = β ∧ pm t / pm (t + 1) = β * (1 + i t) ∧ du (c (t + 1)) = 1 + i t := by
  obtain ⟨hp, -, -, -, hl, h22, h23, hF, -, -⟩ := h t
  obtain ⟨hp1, -, -, h20', hl', -⟩ := h (t + 1)
  have hq : q t = β := by rw [hl, hl'] at h22; linarith
  have hR : pm t / pm (t + 1) = β * (1 + i t) := by rw [← hF, hq]
  refine ⟨hq, hR, ?_⟩
  have hb : β ≠ 0 := by
    rintro rfl; rw [zero_mul] at hR; exact (div_pos hp hp1).ne' hR
  rw [hl, hl', hR, one_mul] at h23
  rw [h20', hl']
  exact (mul_left_cancel₀ hb h23).symm

/-- AKMM, p. 515: initial consumption is `c₀ = min(p_{m,0}M₀, c₀*)` where `u′(c₀*) = 1`: if the
CIA does not bind, `µ₀ = 0` and `c₀ = c₀*`; otherwise `c₀ = p_{m,0}M₀ < c₀*`. -/
theorem peg_c0 {β cs : ℝ} {du : ℝ → ℝ} {i pm M c lam mu q : ℕ → ℝ}
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hcs : 0 < cs) (hdu : du cs = 1)
    (h : pegIsEquilibrium β du i pm M c lam mu q) : c 0 = min (pm 0 * M 0) cs := by
  obtain ⟨-, hc, hcia, h20, hl, -, -, -, hmu, hcs'⟩ := h 0
  rw [hl] at h20
  rcases hmu.lt_or_eq with hpos | hzero
  · have hb : c 0 = pm 0 * M 0 := by
      rcases mul_eq_zero.1 hcs' with h' | h'
      · exact absurd h' hpos.ne'
      · linarith
    have hlt : c 0 < cs := by
      by_contra hn
      rcases (not_lt.1 hn).lt_or_eq with h' | h'
      · have := hanti hcs hc h'; linarith
      · rw [← h', hdu] at h20; linarith
    rw [← hb, min_eq_left hlt.le]
  · rw [← hzero, add_zero] at h20
    have hc0 : c 0 = cs := hanti.injOn hc hcs (h20.trans hdu.symm)
    rw [hc0, min_eq_right (hc0 ▸ hcia)]

/-- **AKMM, p. 515: every initial price of money indexes an equilibrium.** Suppose `u′` is
strictly decreasing on `(0, ∞)`, `u′(c₀*) = 1`, and `cinv` inverts `u′` on `[1, ∞)` with
positive values. For a peg `i_t > 0`, an initial stock `M₀ > 0` and every `p₀ > 0` there is an
equilibrium with `p_{m,0} = p₀`, `M_0 = M₀` (the later money stock is endogenous). -/
theorem peg_exists {β cs M0 p0 : ℝ} {du cinv : ℝ → ℝ} {i : ℕ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hcs : 0 < cs) (hdu : du cs = 1)
    (hcinv : ∀ x, 1 ≤ x → 0 < cinv x ∧ du (cinv x) = x) (hi : ∀ t, 0 < i t) (hM0 : 0 < M0)
    (hp0 : 0 < p0) :
    ∃ pm M c lam mu q : ℕ → ℝ, pegIsEquilibrium β du i pm M c lam mu q ∧ pm 0 = p0 ∧
      M 0 = M0 := by
  let pm : ℕ → ℝ := fun t => p0 / ∏ s ∈ Finset.range t, (β * (1 + i s))
  have hprod : ∀ t, 0 < ∏ s ∈ Finset.range t, (β * (1 + i s)) := fun t =>
    Finset.prod_pos fun s _ => mul_pos hβ (by linarith [hi s])
  have hpm : ∀ t, 0 < pm t := fun t => div_pos hp0 (hprod t)
  have hratio : ∀ t, pm t / pm (t + 1) = β * (1 + i t) := fun t => by
    simp only [pm, Finset.prod_range_succ]
    have := (hprod t).ne'
    have : β * (1 + i t) ≠ 0 := (mul_pos hβ (by linarith [hi t])).ne'
    field_simp
  let c : ℕ → ℝ := fun t => if t = 0 then min (p0 * M0) cs else cinv (1 + i (t - 1))
  let M : ℕ → ℝ := fun t => if t = 0 then M0 else c t / pm t
  let mu : ℕ → ℝ := fun t => du (c t) - 1
  have hc0 : c 0 = min (p0 * M0) cs := rfl
  have hcs1 : ∀ t, c (t + 1) = cinv (1 + i t) := fun t => by simp [c]
  have hdu1 : ∀ t, du (c (t + 1)) = 1 + i t := fun t => by
    rw [hcs1]; exact (hcinv _ (by linarith [hi t])).2
  refine ⟨pm, M, c, fun _ => 1, mu, fun _ => β, fun t => ?_, by simp [pm], rfl⟩
  cases t with
  | zero =>
    have hpm0 : pm 0 = p0 := by simp [pm]
    have hM0' : M 0 = M0 := rfl
    have hc0pos : 0 < c 0 := lt_min (mul_pos hp0 hM0) hcs
    have hmu1 : mu 1 = i 0 := by simp only [mu]; rw [hdu1 0]; ring
    refine ⟨hpm 0, hc0pos, ?_, by simp [mu], rfl, by ring, ?_, ?_, ?_, ?_⟩
    · rw [hpm0, hM0', hc0]; exact min_le_left _ _
    · rw [hratio, hmu1]; ring
    · rw [hratio]
    · rcases le_or_gt cs (p0 * M0) with hle | hlt
      · simp only [mu]; rw [show c 0 = cs by rw [hc0, min_eq_right hle], hdu, sub_self]
      · have : c 0 = p0 * M0 := by rw [hc0, min_eq_left hlt.le]
        have h1 : 1 < du (c 0) := hdu ▸ hanti (by rw [this]; exact mul_pos hp0 hM0) hcs
          (by rw [this]; exact hlt)
        simp only [mu]; linarith
    · rcases le_or_gt cs (p0 * M0) with hle | hlt
      · simp only [mu]; rw [show c 0 = cs by rw [hc0, min_eq_right hle], hdu, sub_self, zero_mul]
      · have : c 0 = p0 * M0 := by rw [hc0, min_eq_left hlt.le]
        rw [hpm0, hM0', this]; ring
  | succ s =>
    have hcpos : 0 < c (s + 1) := by rw [hcs1]; exact (hcinv _ (by linarith [hi s])).1
    have hMs : M (s + 1) = c (s + 1) / pm (s + 1) := by simp [M]
    have hbind : pm (s + 1) * M (s + 1) = c (s + 1) := by
      rw [hMs]; field_simp [(hpm (s + 1)).ne']
    have hmu1 : mu (s + 1 + 1) = i (s + 1) := by simp only [mu]; rw [hdu1 (s + 1)]; ring
    refine ⟨hpm _, hcpos, hbind.ge, by simp [mu], rfl, by ring, ?_, ?_, ?_, ?_⟩
    · rw [hratio, hmu1]; ring
    · rw [hratio]
    · simp only [mu]; rw [hdu1 s]; linarith [hi s]
    · rw [hbind, sub_self, mul_zero]

/-- **AKMM, p. 515: real indeterminacy.** Two equilibria with initial prices
`p_{m,0} < p′_{m,0} ≤ c₀*/M₀` (same `M₀`) have different initial consumption. -/
theorem peg_real_indeterminacy {β cs : ℝ} {du : ℝ → ℝ}
    {i pm M c lam mu q pm' M' c' lam' mu' q' : ℕ → ℝ} (hanti : StrictAntiOn du (Set.Ioi 0))
    (hcs : 0 < cs) (hdu : du cs = 1) (h : pegIsEquilibrium β du i pm M c lam mu q)
    (h' : pegIsEquilibrium β du i pm' M' c' lam' mu' q') (hM : M 0 = M' 0) (hM0 : 0 < M 0)
    (hlt : pm 0 < pm' 0) (hle : pm' 0 * M' 0 ≤ cs) : c 0 < c' 0 := by
  rw [peg_c0 hanti hcs hdu h, peg_c0 hanti hcs hdu h', min_eq_left hle,
    min_eq_left (by rw [hM]; nlinarith [hM ▸ hM0])]
  rw [hM]; exact mul_lt_mul_of_pos_right hlt (hM ▸ hM0)

/-! ### Interest-rate rules with a target -/

/-- AKMM, (17.40), p. 516: the map `x ↦ x(1 + φ(x))/(1 + ĩ)` of the price level relative to
target. -/
noncomputable def ruleMap (φ : ℝ → ℝ) (it x : ℝ) : ℝ := x * (1 + φ x) / (1 + it)

/-- **AKMM, (17.40)**, p. 516: with the Fisher equation `1 + i_t = (1 + r)P_{t+1}/P_t`, the rule
`i_t = φ(P_t/P̃_t)` (17.39) and the target `P̃_{t+1} = (1 + π̃)P̃_t`, `1 + ĩ = (1 + r)(1 + π̃)`:
`P_{t+1}/P̃_{t+1} = ((1 + φ(P_t/P̃_t))/(1 + ĩ)) P_t/P̃_t`. -/
theorem eq_17_40 {φ : ℝ → ℝ} {r it pit Pt Pt1 Qt Qt1 i : ℝ} (hr : 1 + r ≠ 0)
    (hpit : 1 + pit ≠ 0) (hPt : Pt ≠ 0) (hQt : Qt ≠ 0) (hF : 1 + i = (1 + r) * (Pt1 / Pt))
    (hrule : i = φ (Pt / Qt)) (htarget : Qt1 = (1 + pit) * Qt)
    (hit : 1 + it = (1 + r) * (1 + pit)) : Pt1 / Qt1 = ruleMap φ it (Pt / Qt) := by
  unfold ruleMap
  rw [← hrule, hF, hit, htarget]
  field_simp

/-- AKMM, p. 515: if the policy attains its target at every date, the interest rate is
`ĩ = φ(1)` and the target inflation rate is `(1 + ĩ)/(1 + r)`. -/
theorem rule_target {φ : ℝ → ℝ} {r Pt Pt1 i : ℝ} (hr : 1 + r ≠ 0) (hPt : Pt ≠ 0)
    (hF : 1 + i = (1 + r) * (Pt1 / Pt)) (hrule : i = φ 1) :
    i = φ 1 ∧ Pt1 / Pt = (1 + φ 1) / (1 + r) := by
  refine ⟨hrule, ?_⟩
  rw [← hrule, hF]; field_simp

/-- AKMM, p. 516: `x = 1` is a fixed point of (17.40) and the slope there is
`1 + φ′(1)/(1 + ĩ)`. -/
theorem rule_map_hasDerivAt {φ : ℝ → ℝ} {it d : ℝ} (hit : 1 + it ≠ 0) (hφ1 : φ 1 = it)
    (hφ : HasDerivAt φ d 1) :
    ruleMap φ it 1 = 1 ∧ HasDerivAt (ruleMap φ it) (1 + d / (1 + it)) 1 := by
  refine ⟨by unfold ruleMap; rw [hφ1, one_mul, div_self hit], ?_⟩
  have h := ((hasDerivAt_id' 1).mul ((hasDerivAt_const 1 (1 : ℝ)).add hφ)).div_const (1 + it)
  unfold ruleMap
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, hφ1]
  field_simp
  ring

/-- The local bound behind the linearisation: if `F(1) = 1` and `F′(1) = s`, for every `ε > 0`
there is `δ > 0` with `|F(x) − 1 − s(x − 1)| ≤ ε|x − 1|` for `|x − 1| < δ`. -/
theorem rule_local_bound {F : ℝ → ℝ} {s : ℝ} (hF : HasDerivAt F s 1) (h1 : F 1 = 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x, |x - 1| < δ → |F x - 1 - s * (x - 1)| ≤ ε * |x - 1| := by
  have h := (hasDerivAt_iff_isLittleO.1 hF).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := hball (by rwa [Real.dist_eq])
  simpa [h1, Real.norm_eq_abs, smul_eq_mul, mul_comm] using this

/-- **AKMM, p. 516 (determinacy).** If `F(1) = 1` and `|F′(1)| > 1`, there is `δ > 0` such that
the only solution of `x_{t+1} = F(x_t)` with `|x_t − 1| < δ` for all `t` is `x ≡ 1`. -/
theorem rule_determinate {F : ℝ → ℝ} {s : ℝ} (hF : HasDerivAt F s 1) (h1 : F 1 = 1)
    (hs : 1 < |s|) : ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = F (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  obtain ⟨δ, hδ, hb⟩ := rule_local_bound hF h1 (ε := (|s| - 1) / 2) (by linarith)
  set K := (|s| + 1) / 2 with hK
  have hK1 : 1 < K := by rw [hK]; linarith
  have hgrow : ∀ y, |y - 1| < δ → K * |y - 1| ≤ |F y - 1| := fun y hy => by
    have h := hb y hy
    have : |s * (y - 1)| ≤ |F y - 1| + |F y - 1 - s * (y - 1)| := by
      have h2 := abs_sub_abs_le_abs_sub (s * (y - 1)) (F y - 1)
      rw [abs_sub_comm (s * (y - 1)) (F y - 1)] at h2
      linarith
    rw [abs_mul] at this
    rw [hK]; nlinarith [abs_nonneg (y - 1)]
  refine ⟨δ, hδ, fun x hx hin t => ?_⟩
  have hpow : ∀ n, K ^ n * |x t - 1| ≤ |x (t + n) - 1| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hgrow _ (hin (t + n))
      rw [← hx] at this
      calc K ^ (n + 1) * |x t - 1| = K * (K ^ n * |x t - 1|) := by ring
        _ ≤ K * |x (t + n) - 1| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ |x (t + (n + 1)) - 1| := by rw [← add_assoc]; exact this
  by_contra hne
  have hpos : 0 < |x t - 1| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ / |x t - 1|) hK1
  have := hpow n
  have := hin (t + n)
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- **AKMM, p. 516 (indeterminacy).** If `F(1) = 1` and `|F′(1)| < 1`, there is `δ > 0` such that
every start `|x₀ − 1| < δ` generates a solution staying within `δ` of `1` and converging to `1`:
a continuum of bounded solutions. -/
theorem rule_indeterminate {F : ℝ → ℝ} {s : ℝ} (hF : HasDerivAt F s 1) (h1 : F 1 = 1)
    (hs : |s| < 1) : ∃ δ > 0, ∀ x0, |x0 - 1| < δ →
      (∀ t, |F^[t] x0 - 1| < δ) ∧ Tendsto (fun t => F^[t] x0) atTop (𝓝 1) := by
  obtain ⟨δ, hδ, hb⟩ := rule_local_bound hF h1 (ε := (1 - |s|) / 2) (by linarith)
  set K := (1 + |s|) / 2 with hK
  have hK1 : K < 1 := by rw [hK]; linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hshrink : ∀ y, |y - 1| < δ → |F y - 1| ≤ K * |y - 1| := fun y hy => by
    have h := hb y hy
    have : |F y - 1| ≤ |s * (y - 1)| + |F y - 1 - s * (y - 1)| := by
      have := abs_add_le (s * (y - 1)) (F y - 1 - s * (y - 1))
      rwa [add_sub_cancel] at this
    rw [abs_mul] at this
    rw [hK]; nlinarith [abs_nonneg (y - 1)]
  refine ⟨δ, hδ, fun x0 hx0 => ?_⟩
  have hall : ∀ t, |F^[t] x0 - 1| ≤ K ^ t * |x0 - 1| := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      have hin : |F^[n] x0 - 1| < δ :=
        lt_of_le_of_lt (ih.trans (mul_le_of_le_one_left (abs_nonneg _)
          (pow_le_one₀ hK0 hK1.le))) hx0
      rw [Function.iterate_succ_apply']
      calc |F (F^[n] x0) - 1| ≤ K * |F^[n] x0 - 1| := hshrink _ hin
        _ ≤ K * (K ^ n * |x0 - 1|) := mul_le_mul_of_nonneg_left ih hK0
        _ = K ^ (n + 1) * |x0 - 1| := by ring
  refine ⟨fun t => lt_of_le_of_lt ((hall t).trans (mul_le_of_le_one_left (abs_nonneg _)
    (pow_le_one₀ hK0 hK1.le))) hx0, ?_⟩
  have hlim : Tendsto (fun t => K ^ t * |x0 - 1|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const |x0 - 1|
  have : Tendsto (fun t => F^[t] x0 - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hall t) hlim
  simpa using this.add_const 1

/-- **AKMM, p. 516**: if `φ′(1) > 0` the bounded solution near `1` is unique, `P_t = P̃_t`. -/
theorem rule_phi_pos_determinate {φ : ℝ → ℝ} {it d : ℝ} (hit : 0 < 1 + it) (hφ1 : φ 1 = it)
    (hφ : HasDerivAt φ d 1) (hd : 0 < d) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = ruleMap φ it (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  obtain ⟨h1, hD⟩ := rule_map_hasDerivAt hit.ne' hφ1 hφ
  refine rule_determinate hD h1 ?_
  have : 0 < d / (1 + it) := div_pos hd hit
  rw [abs_of_pos (by linarith)]; linarith

/-- AKMM, p. 516, corrected: if `−2(1 + ĩ) < φ′(1) < 0` there is a continuum of solutions near
`1`, all converging to `1`. -/
theorem rule_phi_neg_indeterminate {φ : ℝ → ℝ} {it d : ℝ} (hit : 0 < 1 + it) (hφ1 : φ 1 = it)
    (hφ : HasDerivAt φ d 1) (hd : d < 0) (hd2 : -2 * (1 + it) < d) :
    ∃ δ > 0, ∀ x0, |x0 - 1| < δ → (∀ t, |(ruleMap φ it)^[t] x0 - 1| < δ) ∧
      Tendsto (fun t => (ruleMap φ it)^[t] x0) atTop (𝓝 1) := by
  obtain ⟨h1, hD⟩ := rule_map_hasDerivAt hit.ne' hφ1 hφ
  refine rule_indeterminate hD h1 ?_
  have a1 : d / (1 + it) < 0 := div_neg_of_neg_of_pos hd hit
  have a2 : -2 < d / (1 + it) := by rw [lt_div_iff₀ hit]; linarith
  rw [abs_lt]; constructor <;> linarith

/-- AKMM, p. 516, corrected: if `φ′(1) < −2(1 + ĩ)` the deviation is again explosive
(oscillating), and the bounded solution near `1` is unique. -/
theorem rule_phi_very_neg_determinate {φ : ℝ → ℝ} {it d : ℝ} (hit : 0 < 1 + it)
    (hφ1 : φ 1 = it) (hφ : HasDerivAt φ d 1) (hd : d < -2 * (1 + it)) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = ruleMap φ it (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  obtain ⟨h1, hD⟩ := rule_map_hasDerivAt hit.ne' hφ1 hφ
  refine rule_determinate hD h1 ?_
  have : d / (1 + it) < -2 := by rw [div_lt_iff₀ hit]; linarith
  rw [abs_of_neg (by linarith)]; linarith

/-- AKMM, p. 516: counterexample to the printed "if `φ′(1) < 0`, then there is indeterminacy".
The rule `φ(x) = −3(x − 1)` (`ĩ = 0`, `φ′(1) = −3 < 0`) has a unique solution near `1`. -/
theorem rule_printed_counterexample :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = ruleMap (fun y => -3 * (y - 1)) 0 (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  have hφ : HasDerivAt (fun y : ℝ => -3 * (y - 1)) (-3) 1 := by
    simpa using ((hasDerivAt_id' (1 : ℝ)).sub_const 1).const_mul (-3 : ℝ)
  exact rule_phi_very_neg_determinate (by norm_num) (by norm_num) hφ (by norm_num)

/-- AKMM, footnote 15, p. 516: for an affine rule with `φ′(1) = 0` (`φ ≡ ĩ`), every constant
ratio `P_t/P̃_t = x̄` solves (17.40): a continuum of non-diverging solutions. -/
theorem rule_knife_edge {it xb : ℝ} (hit : 1 + it ≠ 0) :
    ruleMap (fun _ => it) it xb = xb := by
  unfold ruleMap; field_simp

end AKMM.Money
