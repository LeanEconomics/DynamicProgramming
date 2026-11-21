/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.IncompleteMarkets
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The decision rules of Figure 7.4 for Markov income

AKMM, §7.6, pp. 213–215, Figure 7.4(A). The consumer of `IncompleteMarkets`: income `y` follows
a Markov chain `P(y, y′)` on a finite set `S` (the figure uses two values), `q = 1/(1 + r)`,
`V(a, y) = max_{a′ ≥ a̲} u(a + y − qa′) + βE[V(a′, y′)|y]` attained at `a′ = g(a, y)`. The standing
assumptions (`imf_Standing`) are those of the text: `β ≥ 0`, `1 + r > 0`, impatience
`β(1 + r) < 1`, `P` a stochastic matrix, `u` differentiable with `u′ > 0` strictly decreasing
(strictly concave `u`), and `V(·, y)` differentiable on `[a̲, ∞)` and concave (its derivative `V₁`
is nonincreasing). Consumption is `c(a, y) = a + y − qg(a, y)` (`imf_c`). Proved, for Markov
income:

* the savings rule and consumption are nondecreasing in assets, with
  `0 ≤ g(a₂, y) − g(a₁, y) ≤ (1 + r)(a₂ − a₁)` and `0 ≤ c(a₂, y) − c(a₁, y) ≤ a₂ − a₁`
  (`imf_g_mono`, `imf_c_mono`, `imf_g_lipschitz`, `imf_c_lipschitz`), hence continuous
  (`imf_g_continuousOn`, `imf_c_continuousOn`);
* in the state with the lowest consumption at `a` the consumer dissaves: `g(a, y) ≤ a`, strictly
  if `a > a̲` (`imf_min_dissave`); for two states with consumption increasing in income this is
  the figure's low-income rule, on the 45-degree line at `a̲` and below it above `a̲`;
* the borrowing constraint binds on a whole interval `[a̲, a̲ + δ)` in that state
  (`imf_binds_near_limit`, with `u′` continuous);
* with `r > 0`, consumption is unbounded in every state (`imf_c_unbounded`), and if
  `β(1 + r)u′(c) < u′(c + D)` for large `c`, where `D` bounds the income spread (true when
  `u′(c + D)/u′(c) → 1`, e.g. for CRRA utility, `imf_crra_spread`), there is `ā ≥ a̲` with
  `g(a, y) < a` for all `a ≥ ā` and all `y` (`imf_abar_exists`); with `r < 0` such an `ā`
  exists without the condition (`imf_abar_exists_neg`);
* the ergodic set `[a̲, ā]` is invariant (`imf_ergodic_invariant`), and from any initial assets
  and along every income history assets enter `[a̲, ā]` in finite time and stay there
  (`imf_enters_ergodic`).

Departures: the book reads these properties off a computed figure. For Markov income the
existence of `ā` needs a condition on `u` (it holds for the usual CRRA and log utilities), and the
case `r = 0` is in `IncomeFluctuationZeroRate`. Whether the high-income rule lies above the
45-degree line at `a̲` depends on the parameters: it fails in the instance of
`IncomeFluctuationStationary`.
-/

namespace AKMM.Uncertainty

open Filter Topology Set

variable {S : Type*} [Fintype S]

/-- AKMM, p. 213: the standing assumptions of §7.6 for the income-fluctuation problem with
Markov income. `β ≥ 0`, `1 + r > 0`, `β(1 + r) < 1`; `P` is a stochastic matrix; `(V, g)` solve
the Bellman equation with `q = 1/(1 + r)`; `u` has derivative `u′ > 0`, strictly decreasing on
`(0, ∞)`; `V(·, y)` has derivative `V₁(·, y)` on `[a̲, ∞)`, nonincreasing there (`V(·, y)`
concave). -/
def imf_Standing (u u' : ℝ → ℝ) (β r : ℝ) (P : S → S → ℝ) (inc : S → ℝ) (abar : ℝ)
    (V V1 g : S → ℝ → ℝ) : Prop :=
  0 ≤ β ∧ 0 < 1 + r ∧ β * (1 + r) < 1 ∧ (∀ y y', 0 ≤ P y y') ∧ (∀ y, ∑ y', P y y' = 1) ∧
    im_Bellman u β (1 / (1 + r)) P inc abar V g ∧
    (∀ c, 0 < c → HasDerivAt u (u' c) c) ∧ (∀ c, 0 < c → 0 < u' c) ∧
    StrictAntiOn u' (Ioi 0) ∧ (∀ y a, abar ≤ a → HasDerivAt (V y) (V1 y a) a) ∧
    ∀ y, AntitoneOn (V1 y) (Ici abar)

/-- AKMM, p. 213: consumption `c(a, y) = a + y − qg(a, y)` from the budget `qa′ + c = a + y`. -/
noncomputable def imf_c (r : ℝ) (inc : S → ℝ) (g : S → ℝ → ℝ) (y : S) (a : ℝ) : ℝ :=
  a + inc y - 1 / (1 + r) * g y a

variable {u u' : ℝ → ℝ} {β r : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ} {V V1 g : S → ℝ → ℝ}

/-- AKMM, p. 213: savings are feasible and consumption is positive, `g(a, y) ≥ a̲`,
`c(a, y) > 0`. -/
theorem imf_feasible (h : imf_Standing u u' β r P inc abar V V1 g) {y : S} {a : ℝ}
    (ha : abar ≤ a) : abar ≤ g y a ∧ 0 < imf_c r inc g y a := by
  obtain ⟨h1, h2⟩ := im_Bellman_feasible h.2.2.2.2.2.1 (y := y) ha
  exact ⟨h1, by unfold imf_c; linarith⟩

/-- The savings rule recovered from consumption: `g(a, y) = (1 + r)(a + y − c(a, y))`. -/
theorem imf_g_eq (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) (a : ℝ) :
    g y a = (1 + r) * (a + inc y - imf_c r inc g y a) := by
  have hr := h.2.1
  unfold imf_c
  field_simp
  ring

/-- AKMM, p. 213: the first-order condition with `q = 1/(1 + r)` in the form
`βE[V₁(a′, y′)|y] ≤ qu′(c)`, with equality when `a′ = g(a, y) > a̲`. -/
theorem imf_foc (h : imf_Standing u u' β r P inc abar V V1 g) {y : S} {a : ℝ} (ha : abar ≤ a) :
    β * ∑ y', P y y' * V1 y' (g y a) ≤ u' (imf_c r inc g y a) * (1 / (1 + r)) ∧
      (abar < g y a →
        u' (imf_c r inc g y a) * (1 / (1 + r)) = β * ∑ y', P y y' * V1 y' (g y a)) := by
  obtain ⟨-, -, -, -, -, hB, hu, -, -, hV, -⟩ := id h
  obtain ⟨hg, hc⟩ := imf_feasible h (y := y) ha
  exact im_foc hB ha (hu _ hc) fun y' => hV y' _ hg

/-- The expected marginal value of savings `Σ P(y, y′)V₁(a′, y′)` is nonincreasing in `a′`. -/
theorem imf_W_anti (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) {x₁ x₂ : ℝ}
    (h1 : abar ≤ x₁) (h12 : x₁ ≤ x₂) :
    ∑ y', P y y' * V1 y' x₂ ≤ ∑ y', P y y' * V1 y' x₁ :=
  Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left
    (h.2.2.2.2.2.2.2.2.2.2 y' h1 (h1.trans h12) h12) (h.2.2.2.1 y y')

/-- **AKMM, Fig. 7.4(A): the savings rule is nondecreasing in assets**, `a₁ ≤ a₂ ⇒
g(a₁, y) ≤ g(a₂, y)`, for Markov income. -/
theorem imf_g_mono (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) {a₁ a₂ : ℝ}
    (h1 : abar ≤ a₁) (h12 : a₁ ≤ a₂) : g y a₁ ≤ g y a₂ := by
  by_contra hlt
  push Not at hlt
  have hβ := h.1
  have hr := h.2.1
  have hq : 0 < 1 / (1 + r) := by positivity
  obtain ⟨hg2, hc2⟩ := imf_feasible h (y := y) (h1.trans h12)
  obtain ⟨-, hc1⟩ := imf_feasible h (y := y) h1
  have heq := (imf_foc h (y := y) h1).2 (hg2.trans_lt hlt)
  have hle := (imf_foc h (y := y) (h1.trans h12)).1
  have hW := mul_le_mul_of_nonneg_left (imf_W_anti h y hg2 hlt.le) hβ
  have hu : u' (imf_c r inc g y a₁) ≤ u' (imf_c r inc g y a₂) :=
    le_of_mul_le_mul_right (by linarith) hq
  have hcc : imf_c r inc g y a₁ < imf_c r inc g y a₂ := by
    unfold imf_c
    nlinarith
  exact absurd hu (not_le.2 (h.2.2.2.2.2.2.2.2.1 hc1 hc2 hcc))

/-- **AKMM, Fig. 7.4: consumption is nondecreasing in assets**, `a₁ ≤ a₂ ⇒
c(a₁, y) ≤ c(a₂, y)`. -/
theorem imf_c_mono (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) {a₁ a₂ : ℝ}
    (h1 : abar ≤ a₁) (h12 : a₁ ≤ a₂) : imf_c r inc g y a₁ ≤ imf_c r inc g y a₂ := by
  by_contra hlt
  push Not at hlt
  have hβ := h.1
  have hr := h.2.1
  have hq : 0 < 1 / (1 + r) := by positivity
  obtain ⟨hg1, hc1⟩ := imf_feasible h (y := y) h1
  obtain ⟨-, hc2⟩ := imf_feasible h (y := y) (h1.trans h12)
  have hgg : g y a₁ < g y a₂ := by
    unfold imf_c at hlt
    by_contra hg
    push Not at hg
    nlinarith
  have heq := (imf_foc h (y := y) (h1.trans h12)).2 (hg1.trans_lt hgg)
  have hle := (imf_foc h (y := y) h1).1
  have hW := mul_le_mul_of_nonneg_left (imf_W_anti h y hg1 hgg.le) hβ
  have hu : u' (imf_c r inc g y a₂) ≤ u' (imf_c r inc g y a₁) :=
    le_of_mul_le_mul_right (by linarith) hq
  exact absurd hu (not_le.2 (h.2.2.2.2.2.2.2.2.1 hc2 hc1 hlt))

/-- AKMM, Fig. 7.4: the marginal propensity to consume out of assets is in `[0, 1]`:
`0 ≤ c(a₂, y) − c(a₁, y) ≤ a₂ − a₁`. -/
theorem imf_c_lipschitz (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) {a₁ a₂ : ℝ}
    (h1 : abar ≤ a₁) (h12 : a₁ ≤ a₂) :
    0 ≤ imf_c r inc g y a₂ - imf_c r inc g y a₁ ∧
      imf_c r inc g y a₂ - imf_c r inc g y a₁ ≤ a₂ - a₁ := by
  have hr := h.2.1
  have hq : 0 < 1 / (1 + r) := by positivity
  have hg := imf_g_mono h y h1 h12
  refine ⟨by linarith [imf_c_mono h y h1 h12], ?_⟩
  unfold imf_c
  nlinarith

/-- AKMM, Fig. 7.4: the savings rule has slope in `[0, 1 + r]`:
`0 ≤ g(a₂, y) − g(a₁, y) ≤ (1 + r)(a₂ − a₁)`. -/
theorem imf_g_lipschitz (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) {a₁ a₂ : ℝ}
    (h1 : abar ≤ a₁) (h12 : a₁ ≤ a₂) :
    0 ≤ g y a₂ - g y a₁ ∧ g y a₂ - g y a₁ ≤ (1 + r) * (a₂ - a₁) := by
  have hr := h.2.1
  refine ⟨by linarith [imf_g_mono h y h1 h12], ?_⟩
  have hc := imf_c_mono h y h1 h12
  rw [imf_g_eq h y a₂, imf_g_eq h y a₁]
  nlinarith

/-- The savings rule is continuous on `[a̲, ∞)`. -/
theorem imf_g_continuousOn (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) :
    ContinuousOn (g y) (Ici abar) := by
  have hr := h.2.1
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (1 + r)) fun x hx z hz => ?_)
    |>.continuousOn
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hr.le]
  rcases le_total x z with hxz | hxz
  · obtain ⟨h0, h1⟩ := imf_g_lipschitz h y hx hxz
    rw [abs_sub_comm, abs_of_nonneg h0, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · obtain ⟨h0, h1⟩ := imf_g_lipschitz h y hz hxz
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    exact h1

/-- Consumption is continuous on `[a̲, ∞)`. -/
theorem imf_c_continuousOn (h : imf_Standing u u' β r P inc abar V V1 g) (y : S) :
    ContinuousOn (imf_c r inc g y) (Ici abar) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx z hz => ?_).continuousOn
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total x z with hxz | hxz
  · obtain ⟨h0, h1⟩ := imf_c_lipschitz h y hx hxz
    rw [abs_sub_comm, abs_of_nonneg h0, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · obtain ⟨h0, h1⟩ := imf_c_lipschitz h y hz hxz
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    exact h1

/-- The Euler equation in terms of `imf_c`: `u′(c(a, y)) = (1 + r)βΣ P(y, y′)u′(c(a′, y′))` when
`a′ = g(a, y) > a̲`. -/
theorem imf_euler_eq (h : imf_Standing u u' β r P inc abar V V1 g) {y : S} {a : ℝ}
    (ha : abar ≤ a) (hint : abar < g y a) :
    u' (imf_c r inc g y a) =
      (1 + r) * β * ∑ y', P y y' * u' (imf_c r inc g y' (g y a)) := by
  obtain ⟨hβ, hr, -, hP, -, hB, hu, -, -, hV, -⟩ := id h
  have := (im_euler hβ hr hP hB hu hV ha).2 hint
  simpa only [imf_c] using this

/-- If `a′ ≥ a`, the expected marginal utility tomorrow is at most `u′` of the lowest
consumption today: `Σ P(y, y′)u′(c(a′, y′)) ≤ u′(c(a, y*))` when `c(a, y*) ≤ c(a, y′)` for all
`y′`. -/
theorem imf_next_mu_le (h : imf_Standing u u' β r P inc abar V V1 g) {y ys : S} {a : ℝ}
    (ha : abar ≤ a) (hmin : ∀ y', imf_c r inc g ys a ≤ imf_c r inc g y' a)
    (hga : a ≤ g y a) :
    ∑ y', P y y' * u' (imf_c r inc g y' (g y a)) ≤ u' (imf_c r inc g ys a) := by
  obtain ⟨-, -, -, hP, hsum, -, -, -, hanti, -, -⟩ := id h
  calc ∑ y', P y y' * u' (imf_c r inc g y' (g y a)) ≤
        ∑ y', P y y' * u' (imf_c r inc g ys a) := by
        refine Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left ?_ (hP y y')
        have h1 := (imf_feasible h (y := ys) ha).2
        have h2 := (imf_feasible h (y := y') (ha.trans hga)).2
        have h3 := (hmin y').trans (imf_c_mono h y' ha hga)
        exact hanti.antitoneOn h1 h2 h3
    _ = u' (imf_c r inc g ys a) := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **AKMM, Fig. 7.4(A), p. 214: in the state with the lowest consumption the consumer draws
down savings**, `g(a, y) ≤ a`, strictly when `a > a̲`. For two income states with consumption
increasing in income this is the figure's low-income rule ("on the 45-degree line at `a̲`"). -/
theorem imf_min_dissave (h : imf_Standing u u' β r P inc abar V V1 g) {y : S} {a : ℝ}
    (ha : abar ≤ a) (hmin : ∀ y', imf_c r inc g y a ≤ imf_c r inc g y' a) :
    g y a ≤ a ∧ (abar < a → g y a < a) := by
  have hlt : abar < g y a → g y a < a := by
    intro hint
    by_contra hge
    push Not at hge
    have hβ := h.1
    have hr := h.2.1
    have hβr := h.2.2.1
    have heq := imf_euler_eq h ha hint
    have hle := imf_next_mu_le h ha hmin hge
    have hpos := h.2.2.2.2.2.2.2.1 _ (imf_feasible h (y := y) ha).2
    have : u' (imf_c r inc g y a) ≤ (1 + r) * β * u' (imf_c r inc g y a) := by
      rw [heq] at *
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    nlinarith
  refine ⟨?_, fun hab => ?_⟩
  · rcases (imf_feasible h (y := y) ha).1.lt_or_eq with h1 | h1
    · exact (hlt h1).le
    · rw [← h1]; exact ha
  · rcases (imf_feasible h (y := y) ha).1.lt_or_eq with h1 | h1
    · exact hlt h1
    · rw [← h1]; exact hab

omit [Fintype S] in
/-- There is a state with the lowest consumption at `a` (`S` finite and nonempty). -/
theorem imf_exists_min_state [Finite S] [Nonempty S] (r : ℝ) (inc : S → ℝ) (g : S → ℝ → ℝ) (a : ℝ) :
    ∃ ys, ∀ y', imf_c r inc g ys a ≤ imf_c r inc g y' a :=
  Finite.exists_min fun y => imf_c r inc g y a

/-- AKMM, p. 214 (with `r > 0`): consumption is unbounded in every state: for every `C` there is
`A` with `c(a, y) > C` for all `a ≥ A` and all `y`. -/
theorem imf_c_unbounded (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : 0 < r) (C : ℝ) :
    ∃ A, abar < A ∧ ∀ a, A ≤ a → ∀ y, C < imf_c r inc g y a := by
  set B := ∑ y, |inc y|
  refine ⟨max (abar + 1) ((1 + r) * (B + C) / r), by simp, fun a ha y => ?_⟩
  by_contra hle
  push Not at hle
  have hS : Nonempty S := ⟨y⟩
  obtain ⟨ys, hys⟩ := imf_exists_min_state r inc g a
  have ha1 : abar + 1 ≤ a := (le_max_left _ _).trans ha
  have ha2 : (1 + r) * (B + C) / r ≤ a := (le_max_right _ _).trans ha
  have hB : -B ≤ inc ys := by
    have h1 : |inc ys| ≤ B := Finset.single_le_sum (f := fun y => |inc y|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ ys)
    linarith [neg_abs_le (inc ys)]
  have hcs : imf_c r inc g ys a ≤ C := (hys y).trans hle
  have hga : a ≤ g ys a := by
    rw [imf_g_eq h ys a]
    have : (1 + r) * (B + C) ≤ r * a := by
      rw [div_le_iff₀ hr0] at ha2; linarith
    nlinarith
  have := (imf_min_dissave h (by linarith) hys).2 (by linarith)
  linarith

/-- AKMM, p. 214: the condition on `u` used for `ā` holds for CRRA marginal utility
`u′(c) = c^{−σ}`, `σ > 0`: if `k < 1` and `D ≥ 0`, then `kc^{−σ} < (c + D)^{−σ}` for all large
`c` (since `((c + D)/c)^σ → 1`). -/
theorem imf_crra_spread {σ k D : ℝ} (hσ : 0 < σ) (hk : k < 1) (hD : 0 ≤ D) :
    ∃ C, ∀ c, C ≤ c → 0 < c → k * c ^ (-σ) < (c + D) ^ (-σ) := by
  have hlim : Tendsto (fun c : ℝ => k * ((c + D) / c) ^ σ) atTop (𝓝 (k * 1 ^ σ)) := by
    refine Tendsto.const_mul k (Tendsto.rpow_const ?_ (Or.inr hσ.le))
    have h1 : Tendsto (fun c : ℝ => 1 + D / c) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    field_simp
  rw [Real.one_rpow, mul_one] at hlim
  obtain ⟨C, hC⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hk))
  refine ⟨C, fun c hc hc0 => ?_⟩
  have h1 := hC c hc
  have hcD : 0 < c + D := by linarith
  have hcσ : 0 < c ^ σ := Real.rpow_pos_of_pos hc0 σ
  have hcDσ : 0 < (c + D) ^ σ := Real.rpow_pos_of_pos hcD σ
  rw [Real.div_rpow hcD.le hc0.le, mul_div_assoc', div_lt_one hcσ] at h1
  rw [Real.rpow_neg hc0.le, Real.rpow_neg hcD.le, ← div_eq_mul_inv, div_lt_iff₀ hcσ,
    inv_mul_eq_div, lt_div_iff₀ hcDσ]
  linarith

/-- **AKMM, Fig. 7.4(A), p. 214: the bound `ā`** (Markov income, `r > 0`). If `D` bounds the
income spread and `β(1 + r)u′(c) < u′(c + D)` for all large `c`, there is `ā ≥ a̲` such that
`g(a, y) < a` for every `a ≥ ā` and every income state `y`. -/
theorem imf_abar_exists (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : 0 < r) {D : ℝ}
    (hD : ∀ y y', inc y - inc y' ≤ D)
    (hU : ∃ C, ∀ c, C ≤ c → 0 < c → β * (1 + r) * u' c < u' (c + D)) :
    ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  obtain ⟨C, hC⟩ := hU
  obtain ⟨A, hA, hcA⟩ := imf_c_unbounded h hr0 C
  refine ⟨A, hA.le, fun a ha y => ?_⟩
  by_contra hge
  push Not at hge
  have hS : Nonempty S := ⟨y⟩
  have hβ := h.1
  have hr := h.2.1
  have haa : abar ≤ a := hA.le.trans ha
  obtain ⟨ys, hys⟩ := imf_exists_min_state r inc g a
  have hgs := (imf_min_dissave h haa hys).1
  have hcs := imf_feasible h (y := ys) haa
  have hcy := imf_feasible h (y := y) haa
  have hgap : imf_c r inc g y a ≤ imf_c r inc g ys a + D := by
    have := hD y ys
    have hq : 0 < 1 / (1 + r) := by positivity
    unfold imf_c
    nlinarith
  have heq := imf_euler_eq h (y := y) haa (by linarith)
  have hle := imf_next_mu_le h haa hys hge
  have h1 : u' (imf_c r inc g y a) ≤ (1 + r) * β * u' (imf_c r inc g ys a) := by
    rw [heq]; exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hDnn : 0 ≤ D := by linarith [hD y y]
  have h2 : u' (imf_c r inc g ys a + D) ≤ u' (imf_c r inc g y a) :=
    h.2.2.2.2.2.2.2.2.1.antitoneOn hcy.2 (by simp only [mem_Ioi]; linarith [hcs.2]) hgap
  have h3 := hC _ (hcA a ha ys).le hcs.2
  linarith

/-- AKMM, Fig. 7.4(A), with `r < 0`: then `ā = (1 + r)Y/(−r)` (`Y` bounding income) works
without any condition on `u`: `g(a, y) < a` for all `a ≥ ā`. -/
theorem imf_abar_exists_neg (h : imf_Standing u u' β r P inc abar V V1 g) (hr0 : r < 0) :
    ∃ ab, abar ≤ ab ∧ ∀ a, ab ≤ a → ∀ y, g y a < a := by
  have hr := h.2.1
  set B := ∑ y, |inc y|
  refine ⟨max abar ((1 + r) * B / (-r)), le_max_left _ _, fun a ha y => ?_⟩
  have haa : abar ≤ a := (le_max_left _ _).trans ha
  have ha2 : (1 + r) * B / (-r) ≤ a := (le_max_right _ _).trans ha
  have hB : inc y ≤ B := (le_abs_self _).trans (Finset.single_le_sum (f := fun y => |inc y|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ y))
  have hc := (imf_feasible h (y := y) haa).2
  rw [imf_g_eq h y a]
  rw [div_le_iff₀ (by linarith)] at ha2
  nlinarith

/-- **AKMM, Fig. 7.4(A), p. 214: the ergodic set `[a̲, ā]` is invariant.** If `g(ā, y) ≤ ā` in
every state, then `a ∈ [a̲, ā]` implies `g(a, y) ∈ [a̲, ā]`. -/
theorem imf_ergodic_invariant (h : imf_Standing u u' β r P inc abar V V1 g) {ab : ℝ}
    (hab : ∀ y, g y ab ≤ ab) {a : ℝ} (ha : a ∈ Icc abar ab) (y : S) : g y a ∈ Icc abar ab :=
  ⟨(imf_feasible h ha.1).1, (imf_g_mono h y ha.1 ha.2).trans (hab y)⟩

/-- **AKMM, Fig. 7.4(A), p. 214: "if the consumer begins with initial assets above `ā`, they
will continuously spend down their assets regardless of their income until their assets reach
`ā`. So in the long run the consumer will have asset holdings on the ergodic set `[a̲, ā]`."**
For every income history `y_t` and initial assets `a₀ ≥ a̲`, the assets `a_{t+1} = g(a_t, y_t)`
are in `[a̲, ā]` from some date on. -/
theorem imf_enters_ergodic (h : imf_Standing u u' β r P inc abar V V1 g) {ab : ℝ}
    (hab0 : abar ≤ ab) (hab : ∀ a, ab ≤ a → ∀ y, g y a < a) (ys : ℕ → S) (as : ℕ → ℝ)
    (h0 : abar ≤ as 0) (hstep : ∀ t, as (t + 1) = g (ys t) (as t)) :
    ∃ T, ∀ t, T ≤ t → as t ∈ Icc abar ab := by
  have hr := h.2.1
  have hS : Nonempty S := ⟨ys 0⟩
  have hge : ∀ t, abar ≤ as t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih => rw [hstep]; exact (imf_feasible h ih).1
  have hinv : ∀ y, g y ab ≤ ab := fun y => (hab ab le_rfl y).le
  obtain ⟨T, hT⟩ : ∃ T, as T ≤ ab := by
    by_contra hall
    push Not at hall
    have hanti : Antitone as := antitone_nat_of_succ_le fun t => by
      rw [hstep]; exact (hab _ (hall t).le _).le
    have hbdd : BddBelow (range as) := ⟨ab, by rintro _ ⟨t, rfl⟩; exact (hall t).le⟩
    set L := ⨅ t, as t
    have hL : Tendsto as atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
    have hLab : ab ≤ L := le_ciInf fun t => (hall t).le
    have hle : ∀ t, L ≤ as t := fun t => ciInf_le hbdd t
    obtain ⟨y₀, hy₀⟩ := Finite.exists_max fun y => g y L
    have hε : 0 < L - g y₀ L := by linarith [hab L hLab y₀]
    have hev : ∀ᶠ t in atTop, as t < L + (L - g y₀ L) / (1 + r) :=
      hL.eventually (gt_mem_nhds (by have := div_pos hε hr; linarith))
    obtain ⟨t, ht⟩ := hev.exists
    have hlip := (imf_g_lipschitz h (ys t) (hab0.trans hLab) (hle t)).2
    have h1 : as (t + 1) < L := by
      rw [hstep]
      have h2 : (1 + r) * (as t - L) < L - g y₀ L := by
        have := (lt_div_iff₀' hr).1 (show as t - L < (L - g y₀ L) / (1 + r) by linarith)
        linarith
      linarith [hy₀ (ys t)]
    linarith [hle (t + 1)]
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hge T, hT⟩
  | succ t _ ih => rw [hstep]; exact imf_ergodic_invariant h hinv ih (ys t)

/-- **AKMM, p. 214: low-income consumers reach the borrowing constraint.** With `u′`
continuous, in a state `y₀` with the lowest consumption at `a̲` the constraint binds on a whole
interval: there is `δ > 0` with `g(a, y₀) = a̲` for `a̲ ≤ a < a̲ + δ`. -/
theorem imf_binds_near_limit (h : imf_Standing u u' β r P inc abar V V1 g)
    (hcont : ContinuousOn u' (Ioi 0)) {y₀ : S}
    (hmin : ∀ y', imf_c r inc g y₀ abar ≤ imf_c r inc g y' abar) :
    ∃ δ, 0 < δ ∧ ∀ a, abar ≤ a → a < abar + δ → g y₀ a = abar := by
  obtain ⟨hβ, hr, hβr, hP, hsum, hB, hu, hpos, hanti, hV, -⟩ := id h
  set q := 1 / (1 + r) with hqdef
  have hq : 0 < q := by positivity
  have hβq : β < q := by
    rw [hqdef, lt_div_iff₀ hr]; linarith
  have hg0 : g y₀ abar = abar :=
    le_antisymm (imf_min_dissave h le_rfl hmin).1 (imf_feasible h le_rfl).1
  set φ : ℝ → ℝ := fun a => q * u' (imf_c r inc g y₀ a) -
    β * ∑ y', P y₀ y' * u' (imf_c r inc g y' (g y₀ a)) with hφ
  have hc0 := (imf_feasible h (y := y₀) le_rfl).2
  have hφ0 : 0 < φ abar := by
    simp only [hφ, hg0]
    have hle : ∑ y', P y₀ y' * u' (imf_c r inc g y' abar) ≤ u' (imf_c r inc g y₀ abar) := by
      have := imf_next_mu_le h (y := y₀) le_rfl hmin (by rw [hg0])
      rwa [hg0] at this
    have := hpos _ hc0
    nlinarith
  have hmem : abar ∈ Ici abar := mem_Ici.2 le_rfl
  have hcwa : ∀ y', ContinuousWithinAt (fun a => u' (imf_c r inc g y' (g y₀ a))) (Ici abar)
      abar := by
    intro y'
    have hcy := (imf_feasible h (y := y') le_rfl).2
    have hg := imf_g_continuousOn h y₀ abar hmem
    have hc := imf_c_continuousOn h y' (g y₀ abar) (by rw [hg0]; exact hmem)
    have h1 : ContinuousWithinAt (fun a => imf_c r inc g y' (g y₀ a)) (Ici abar) abar :=
      hc.comp hg fun a ha => (imf_feasible h ha).1
    have h2 : ContinuousAt u' (imf_c r inc g y' (g y₀ abar)) := by
      rw [hg0]; exact hcont.continuousAt (Ioi_mem_nhds hcy)
    exact ContinuousAt.comp_continuousWithinAt (f := fun a => imf_c r inc g y' (g y₀ a)) h2 h1
  have hφc : ContinuousWithinAt φ (Ici abar) abar := by
    refine ContinuousWithinAt.sub (continuousWithinAt_const.mul ?_)
      (continuousWithinAt_const.mul ?_)
    · exact ContinuousAt.comp_continuousWithinAt (f := imf_c r inc g y₀)
        (hcont.continuousAt (Ioi_mem_nhds hc0)) (imf_c_continuousOn h y₀ abar hmem)
    · exact tendsto_finsetSum _ fun y' _ => continuousWithinAt_const.mul (hcwa y')
  have hev : ∀ᶠ a in 𝓝[≥] abar, 0 < φ a := hφc.eventually (lt_mem_nhds hφ0)
  obtain ⟨e, he, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  refine ⟨e - abar, by simp only [mem_Ioi] at he; linarith, fun a ha hae => ?_⟩
  have hφa : 0 < φ a := hsub ⟨ha, by linarith⟩
  refine le_antisymm ?_ (imf_feasible h ha).1
  by_contra hgt
  push Not at hgt
  have heq := (imf_foc h (y := y₀) ha).2 hgt
  have hsumeq : ∑ y', P y₀ y' * V1 y' (g y₀ a) =
      ∑ y', P y₀ y' * u' (imf_c r inc g y' (g y₀ a)) :=
    Finset.sum_congr rfl fun y' _ => by
      have hcy := (imf_feasible h (y := y') (imf_feasible h (y := y₀) ha).1).2
      congr 1
      exact im_envelope hB hgt (hV y' _ (imf_feasible h (y := y₀) ha).1) (hu _ hcy)
  rw [hsumeq] at heq
  simp only [hφ] at hφa
  linarith

end AKMM.Uncertainty
