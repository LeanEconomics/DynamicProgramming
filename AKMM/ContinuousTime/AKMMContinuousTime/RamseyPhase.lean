/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.RamseySaddle
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The phase diagram of the planner's problem off the saddle path

AKMM, §9.3.2 (p. 255, Figure 9.2) and Appendix 9.A.4 (pp. 847–848). The book reads the fate of
the paths that start off the saddle path from the phase diagram. Here they are proved, for the
general neoclassical model of EconomicGrowth's `CassPrimitives` (strictly concave `f` with Inada
conditions, strictly concave `u` with `u'(0+) = ∞`), from every `k(0) > 0` at which the saddle
path is constructed: wherever the Cass optimum invests strictly at every date, which holds for
all `0 < k(0) ≤ k**` (`ramseyPhase_interior_of_le`) and for all `k(0) ∈ (k**, k̂]` for some
`k̂ > k**` (`ramseyPhase_interior_above`, by time consistency of the Cass optimum).

* A *solution* (`ramseyPhaseSolution`) is a path with `c > 0` continuous, `k̇ = f(k) − δk − c`
  (9.33) and the first-order conditions (9.A.1)–(9.A.2), `μ = e^{−ρt}u'(c)`,
  `μ̇ = −μ(f'(k) − δ)`; with CRRA utility these are (9.33) and (9.35)
  (`ramseyPhase_solution_of_eq_9_35`). The saddle path is the project's: the certified Cass
  optimum `optimalPath P hk₀`, which solves the system (`ramseyPhase_saddle`); "above/below the
  saddle path" means `c(0) >/< policy P k(0)`. Below `k**` it rises to `k**`, above it falls.
* Paths from the same `k(0)` do not cross: lower `c(0)` means more capital and less consumption
  at every `t > 0` (`ramseyPhase_comparison`, two exponential barriers).
* The saddle path is the only solution from `k(0)` that satisfies the TVC (`ramseyPhase_unique`,
  from Mangasarian sufficiency and strict concavity); a solution that stays in `k ≤ k**`
  satisfies it (`ramseyPhase_tvc_of_le_steady`).
* Above the saddle path: no solution keeps `k > 0` for ever, and capital reaches `0` at a finite
  date (`ramseyPhase_above_saddle_not_global`, `ramseyPhase_above_saddle_reaches_zero`).
* Below the saddle path: the path either gains `k̇ > 0` right of `k**` and keeps rising
  (`ramseyPhase_rising`) or falls for ever (`ramseyPhase_falling`, possible only from
  `k(0) > k**`); either way (`ramseyPhase_tail`, `ramseyPhase_deriv_limit`), after a finite
  date the path is in `f'(k) < δ` for good, `c → 0`,
  `k → k^u` (the positive root of `f(k) = δk`, `ramseyPhase_root_unique`) and the TVC fails
  (`ramseyPhase_below_saddle`); so `appendix_9A4_below_saddle_violates_tvc` applies
  unconditionally (`appendix_9A4_below_saddle_enters_region`). Consumption is below the saddle
  path at every `t > 0`, and a feasible path from the same `k(0)` gives at least as much
  consumption at every date and strictly more after some date (`ramseyPhase_below_saddle_waste`;
  it leaves the original path smoothly, via Mathlib's smooth transition function).
* The book's model, Cobb–Douglas with CRRA utility: `ramseyPhase_above_saddle_crra_cobbDouglas`,
  `ramseyPhase_below_saddle_crra_cobbDouglas`; for `σ = α` a path below the saddle path is
  constructed in closed form (`ramseyPhase_below_saddle_exists`,
  `ramseyPhase_below_saddle_instance`).

Departures: the results are for the `k(0)` at which the saddle path is constructed (above);
for large `k(0) > k**` the Cass optimum has a zero-investment phase and the book's disinvesting
saddle path is not constructed; the solution notion assumes the path exists on `[0, ∞)` with
`c > 0` (for the path above the saddle path, only while `k > 0`); existence of off-saddle
solutions is proved only for `σ = α`.
-/

namespace AKMM.ContinuousTime

open Filter Topology RamseyCassKoopmans

/-- A function with positive derivative at `t` is larger than `g t` just after `t`. -/
theorem ramseyPhase_eventually_gt_right {g : ℝ → ℝ} {g' t : ℝ} (hg : HasDerivAt g g' t)
    (hpos : 0 < g') : ∀ᶠ s in 𝓝[>] t, g t < g s := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hg).mono_left
    (nhdsWithin_mono t fun x (hx : t < x) => ne_of_gt hx)
  filter_upwards [hs.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with s h1 h2
  rw [slope_def_field] at h1
  have h2' : 0 < s - t := sub_pos.mpr h2
  have := (div_pos_iff_of_pos_right h2').mp h1
  linarith

/-- A function with positive derivative at `t` is smaller than `g t` just before `t`. -/
theorem ramseyPhase_eventually_lt_left {g : ℝ → ℝ} {g' t : ℝ} (hg : HasDerivAt g g' t)
    (hpos : 0 < g') : ∀ᶠ s in 𝓝[<] t, g s < g t := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hg).mono_left
    (nhdsWithin_mono t fun x (hx : x < t) => ne_of_lt hx)
  filter_upwards [hs.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with s h1 h2
  rw [slope_def_field] at h1
  have h2' : s - t < 0 := sub_neg.mpr h2
  have := (div_pos_iff.mp h1).resolve_left fun h => absurd h.2 (not_lt.mpr h2'.le)
  linarith [this.1]

/-- AKMM, §9.3.2, (9.33) and (9.A.1)–(9.A.2): a **solution of the planner's first-order
system** on `[0, ∞)`: positive continuous consumption, the resource constraint
`k̇ = f(k) − δk − c`, and a costate `μ = e^{−ρt}u'(c)` (9.A.1) with
`μ̇ = −μ(f'(k) − δ)` (9.A.2). For CRRA utility this is (9.33) with (9.35)
(`ramseyPhase_solution_of_eq_9_35`). No initial condition on `c` and no TVC are imposed. -/
def ramseyPhaseSolution (f U : ℝ → ℝ) (ρ δ : ℝ) (k c μ : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → 0 < c t) ∧ ContinuousOn c (Set.Ici 0) ∧
    (∀ t, 0 ≤ t → HasDerivAt k (f (k t) - δ * k t - c t) t) ∧
    (∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * deriv U (c t)) ∧
    (∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (deriv f (k t) - δ))) t)

variable {f U : ℝ → ℝ} {ρ δ : ℝ}

/-- Marginal utility is strictly decreasing on `(0, ∞)`. -/
theorem ramseyPhase_uprime_anti (P : CassPrimitives f U ρ δ) :
    StrictAntiOn (deriv U) (Set.Ioi 0) :=
  P.U_conc.strictAntiOn_deriv fun c hc => P.U_diff c hc

/-- The marginal product is strictly decreasing on `(0, ∞)`. -/
theorem ramseyPhase_fprime_anti (P : CassPrimitives f U ρ δ) :
    StrictAntiOn (deriv f) (Set.Ioi 0) :=
  (P.f_conc.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun k hk => P.f_diff k hk

/-- Output is increasing on `(0, ∞)`. -/
theorem ramseyPhase_f_mono (P : CassPrimitives f U ρ δ) : MonotoneOn f (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun k hk => (P.f_diff k hk).continuousAt.continuousWithinAt)
    (fun k hk => (P.f_diff k (interior_subset hk)).differentiableWithinAt) fun k hk => ?_
  rw [interior_Ioi] at hk
  exact (P.f_prime_pos k hk).le

/-- Net output `f(k) − δk` is increasing on `(0, k**]`, where `f'(k) ≥ δ + ρ > δ`. -/
theorem ramseyPhase_net_mono (P : CassPrimitives f U ρ δ) :
    MonotoneOn (fun k => f k - δ * k) (Set.Ioc 0 (cassSteady P)) := by
  obtain ⟨hks, hks'⟩ := cassSteady_spec P
  refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 _)
    (fun k hk => ((P.f_diff k hk.1).continuousAt.sub
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt)
    (fun k hk => ((P.f_diff k (interior_subset hk).1).sub
      ((differentiableAt_id.const_mul δ))).differentiableWithinAt) fun k hk => ?_
  rw [interior_Ioc] at hk
  have hd : deriv (fun k => f k - δ * k) k = deriv f k - δ := by
    have h := (P.f_diff k hk.1).hasDerivAt.sub ((hasDerivAt_id k).const_mul δ)
    simp only [mul_one] at h
    exact h.deriv
  rw [hd]
  have := (ramseyPhase_fprime_anti P).antitoneOn hk.1 hks hk.2.le
  linarith [P.d_pos]

/-- AKMM, p. 255: from `0 < k(0) ≤ k**` the Cass optimum `optimalPath P hk₀` invests strictly
at every date (`ramseySaddle_path`), so it is an optimum with disinvestment allowed. -/
theorem ramseyPhase_interior_of_le (P : CassPrimitives f U ρ δ) {k₀ : ℝ} (hk₀ : 0 < k₀)
    (hle : k₀ ≤ cassSteady P) : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t := by
  obtain ⟨a', q', h0', hc', hint', -⟩ := ramseySaddle_path P hk₀ hle
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk₀
  have heq := hc'.eq P hc (h0'.trans h0.symm)
  intro t ht
  rw [(heq t ht).2.2]; exact hint' t ht

/-- AKMM, p. 255, **the saddle path above `k**`**: there is `k̂ > k**` such that from every
`k(0) ∈ (k**, k̂]` the Cass optimum invests strictly at every date, hence (by
`ramseySaddle_of_interior`) is the book's saddle path, which disinvests. Proof: the optimum from
`k** + 1` invests strictly after a finite date `T` and decreases to `k**`; every stock in
`(k**, k(T)]` is reached after `T`, and by time consistency the optimum from it is the tail. -/
theorem ramseyPhase_interior_above (P : CassPrimitives f U ρ δ) :
    ∃ khat, cassSteady P < khat ∧ ∀ k₀ (hk₀ : 0 < k₀), cassSteady P < k₀ → k₀ ≤ khat →
      ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t := by
  obtain ⟨hks, -⟩ := cassSteady_spec P
  have hk1 : 0 < cassSteady P + 1 := by linarith
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk1
  set a := optimalPath P hk1
  obtain ⟨ks, hks', hstat, b, Jb, hb0, -, -, -, -, -, -, -, -, -, ⟨T, hT0, hTinv⟩, -, hbuniq⟩ :=
    cass_general_dynamic f U ρ δ (cassSteady P + 1) P.d_pos P.m_pos hk1 P.f_conc P.f_zero
      P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont P.f_inada0 P.f_inadaTop
      P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont P.U_second_neg P.U_inada0
  obtain ⟨J, hJ⟩ := hc.welfare
  have huniq := (hbuniq a J (hc.isCassOptimal P hJ) h0).2
  have hainv : ∀ t, T ≤ t → 0 < a.investment t := fun t ht => by
    rw [(huniq t (hT0.trans ht)).2.2]; exact hTinv t ht
  obtain ⟨hklim, -, -, hanti, -⟩ := hc.dynamics P
  have hgt : cassSteady P < a.capital 0 := by rw [h0]; linarith
  have hA := (hanti hgt).1
  have hlow : ∀ t, 0 ≤ t → cassSteady P < a.capital t := fun t ht => by
    have h1 : a.capital (t + 1) < a.capital t := hA (Set.mem_Ici.mpr ht)
      (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have h2 : cassSteady P ≤ a.capital (t + 1) := by
      refine le_of_tendsto hklim ?_
      filter_upwards [eventually_ge_atTop (t + 1)] with s hs
      exact hA.antitoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hs
    linarith
  refine ⟨a.capital T, hlow T hT0, fun k₀ hk₀ hgt₀ hle₀ => ?_⟩
  obtain ⟨T', hT'⟩ := eventually_atTop.mp ((hklim.eventually (gt_mem_nhds hgt₀)).and
    (eventually_ge_atTop T))
  obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc' (hT' T' le_rfl).2
    (a.capital_continuous.mono fun x hx => hT0.trans hx.1)
    ⟨(hT' T' le_rfl).1.le, hle₀⟩
  have hs0 : 0 ≤ s := hT0.trans hs.1
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P hk₀
  have heq := (hc.shift P hs0).eq P hoc
    (by simp only [FeasiblePath.shift_capital, add_zero]; rw [hseq, ho0])
  intro t ht
  rw [(heq t ht).2.2]
  simp only [FeasiblePath.shift_investment]
  exact hainv _ (by linarith [hs.1])

/-- AKMM, p. 255: **the saddle path**, taken as the project's saddle path, the certified Cass
optimum `optimalPath P hk₀`, whenever it invests strictly at every date (for every
`0 < k(0) ≤ k**`, `ramseyPhase_interior_of_le`, and for `k(0) ∈ (k**, k̂]`,
`ramseyPhase_interior_above`). It solves the first-order system (`ramseyPhaseSolution`), its
initial consumption is `policy P k₀`, its capital is positive; below `k**` capital stays in
`(0, k**]` and does not fall (`c ≤ f(k) − δk`), above `k**` it stays above `k**`; capital is
bounded and consumption bounded away from `0`; and it is catching-up optimal in the book's
problem (9.33). -/
theorem ramseyPhase_saddle (P : CassPrimitives f U ρ δ) {k₀ : ℝ} (hk₀ : 0 < k₀)
    (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) :
    ∃ μ : ℝ → ℝ, ramseyPhaseSolution f U ρ δ (optimalPath P hk₀).capital
      (optimalPath P hk₀).consumption μ ∧ (optimalPath P hk₀).capital 0 = k₀ ∧
      (optimalPath P hk₀).consumption 0 = policy P k₀ ∧
      (∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).capital t) ∧
      (k₀ ≤ cassSteady P → ∀ t, 0 ≤ t → (optimalPath P hk₀).capital t ≤ cassSteady P ∧
        (optimalPath P hk₀).consumption t ≤
          f ((optimalPath P hk₀).capital t) - δ * (optimalPath P hk₀).capital t) ∧
      (cassSteady P < k₀ → ∀ t, 0 ≤ t → cassSteady P < (optimalPath P hk₀).capital t) ∧
      (∃ K C, 0 < C ∧ ∀ t, 0 ≤ t → (optimalPath P hk₀).capital t ≤ K ∧
        C ≤ (optimalPath P hk₀).consumption t) ∧
      ∀ k' c' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ k' t) → (∀ t, 0 ≤ t → 0 < c' t) →
        ContinuousOn c' (Set.Ici 0) →
        (∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) → k' 0 = k₀ →
        ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (c' t) ≤
          (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U ((optimalPath P hk₀).consumption t)) +
            ε := by
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk₀
  set a := optimalPath P hk₀
  obtain ⟨-, -, -, h9A1, h9A2, -, hopt⟩ := ramseySaddle_of_interior P hc hint
  have hkd : ∀ t, 0 ≤ t → HasDerivAt a.capital
      (f (a.capital t) - δ * a.capital t - a.consumption t) t := fun t ht => by
    have h := a.dynamics t ht
    have hr := a.resource t ht
    convert h using 1
    linarith
  obtain ⟨hklim, hclim, hmono, hanti, hconst⟩ := hc.dynamics P
  have hcss := cassSteadyConsumption_pos P
  simp only [cassSteadyConsumption] at hcss
  have hle_part : k₀ ≤ cassSteady P → ∀ t, 0 ≤ t → a.capital t ≤ cassSteady P ∧
      a.consumption t ≤ f (a.capital t) - δ * a.capital t := by
    intro hle t ht
    have hmon : MonotoneOn a.capital (Set.Ici 0) := by
      rcases hle.lt_or_eq with hlt | heq'
      · exact (hmono (h0 ▸ hlt)).1.monotoneOn
      · intro x hx y hy _
        rw [(hconst (h0.trans heq') x hx).1, (hconst (h0.trans heq') y hy).1]
    refine ⟨?_, ?_⟩
    · refine ge_of_tendsto hklim ?_
      filter_upwards [eventually_ge_atTop t] with s hs
      exact hmon ht (ht.trans hs) hs
    · by_contra hneg
      rw [not_le] at hneg
      have hd := (hkd t ht).neg
      have hev := ramseyPhase_eventually_gt_right hd (by linarith)
      obtain ⟨s, hs1, hs2⟩ := (hev.and self_mem_nhdsWithin).exists
      have := hmon ht (ht.trans (le_of_lt hs2)) (le_of_lt hs2)
      simp only [Pi.neg_apply] at hs1
      linarith
  have hgt_part : cassSteady P < k₀ → ∀ t, 0 ≤ t → cassSteady P < a.capital t := by
    intro hgt t ht
    have hA := (hanti (h0 ▸ hgt)).1
    have h1 : a.capital (t + 1) < a.capital t := hA (Set.mem_Ici.mpr ht)
      (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have h2 : cassSteady P ≤ a.capital (t + 1) := by
      refine le_of_tendsto hklim ?_
      filter_upwards [eventually_ge_atTop (t + 1)] with s hs
      exact hA.antitoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hs
    linarith
  have hbounds : ∃ K C, 0 < C ∧ ∀ t, 0 ≤ t → a.capital t ≤ K ∧ C ≤ a.consumption t := by
    rcases lt_trichotomy k₀ (cassSteady P) with hlt | heq' | hgt
    · obtain ⟨-, hM⟩ := hmono (h0 ▸ hlt)
      refine ⟨cassSteady P, a.consumption 0, a.consumption_pos 0 le_rfl, fun t ht =>
        ⟨(hle_part hlt.le t ht).1, hM.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht)
          ht⟩⟩
    · refine ⟨cassSteady P, f (cassSteady P) - δ * cassSteady P, hcss, fun t ht => ?_⟩
      rw [(hconst (h0.trans heq') t ht).1, (hconst (h0.trans heq') t ht).2]
      exact ⟨le_rfl, le_rfl⟩
    · obtain ⟨hA, hC⟩ := hanti (h0 ▸ hgt)
      refine ⟨k₀, f (cassSteady P) - δ * cassSteady P, hcss, fun t ht => ⟨?_, ?_⟩⟩
      · rw [← h0]; exact hA.antitoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
      · refine le_of_tendsto hclim ?_
        filter_upwards [eventually_ge_atTop t] with s hs
        exact hC.antitoneOn (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr (ht.trans hs)) hs
  refine ⟨fun s => discount ρ s * q s, ⟨a.consumption_pos, a.consumption_continuous, hkd,
    h9A1, h9A2⟩, h0, ?_, hc.capital_pos, hle_part, hgt_part, hbounds, ?_⟩
  · have := consumption_eq_policy P hc (le_refl (0 : ℝ))
    rwa [h0] at this
  · intro k' c' hk' hc' hcc' hkd' hk'0
    exact hopt k' c' hk' hc' hcc' hkd' (hk'0.trans h0.symm)

/-- AKMM, p. 255, Figure 9.2: **paths from the same `k(0)` do not cross.** If two solutions of
the first-order system start from the same capital stock and the first starts with lower
consumption, then at every date `t > 0` the first has strictly more capital and strictly less
consumption, as long as the second keeps `k > 0` (no positivity of the first is assumed). The
proof is a first-crossing argument with two exponential barriers. -/
theorem ramseyPhase_comparison (P : CassPrimitives f U ρ δ) {k₁ c₁ μ₁ k₂ c₂ μ₂ : ℝ → ℝ}
    (h₁ : ramseyPhaseSolution f U ρ δ k₁ c₁ μ₁) (h₂ : ramseyPhaseSolution f U ρ δ k₂ c₂ μ₂)
    (hk₂ : ∀ t, 0 ≤ t → 0 < k₂ t) (h0 : k₁ 0 = k₂ 0) (hc0 : c₁ 0 < c₂ 0) :
    ∀ t, 0 < t → k₂ t < k₁ t ∧ c₁ t < c₂ t := by
  obtain ⟨hc₁, -, hk₁d, hμ₁, hμ₁d⟩ := h₁
  obtain ⟨hc₂, -, hk₂d, hμ₂, hμ₂d⟩ := h₂
  have hU := ramseyPhase_uprime_anti P
  have hf' := ramseyPhase_fprime_anti P
  have hfm := ramseyPhase_f_mono P
  set x : ℝ → ℝ := fun t => k₁ t - k₂ t with hxdef
  set y : ℝ → ℝ := fun t => μ₁ t - μ₂ t with hydef
  have hyc : ∀ t, 0 ≤ t → (0 < y t ↔ c₁ t < c₂ t) := fun t ht => by
    simp only [y, hμ₁ t ht, hμ₂ t ht, sub_pos]
    rw [mul_lt_mul_iff_right₀ (Real.exp_pos _)]
    exact hU.lt_iff_gt (hc₂ t ht) (hc₁ t ht)
  have hμ₂pos : ∀ t, 0 ≤ t → 0 < μ₂ t := fun t ht => by
    rw [hμ₂ t ht]; exact mul_pos (Real.exp_pos _) (P.U_prime_pos _ (hc₂ t ht))
  have hx : ∀ t, 0 ≤ t → HasDerivAt x ((f (k₁ t) - δ * k₁ t - c₁ t) -
      (f (k₂ t) - δ * k₂ t - c₂ t)) t := fun t ht => (hk₁d t ht).sub (hk₂d t ht)
  have hy : ∀ t, 0 ≤ t → HasDerivAt y (-(μ₁ t * (deriv f (k₁ t) - δ)) -
      -(μ₂ t * (deriv f (k₂ t) - δ))) t := fun t ht => (hμ₁d t ht).sub (hμ₂d t ht)
  have hxc : ContinuousOn x (Set.Ici 0) := fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have hyc' : ContinuousOn y (Set.Ici 0) := fun t ht =>
    (hy t ht).continuousAt.continuousWithinAt
  have hx0 : x 0 = 0 := by simp [x, h0]
  have hy0 : 0 < y 0 := (hyc 0 le_rfl).mpr hc0
  have hxd0 : 0 < (f (k₁ 0) - δ * k₁ 0 - c₁ 0) - (f (k₂ 0) - δ * k₂ 0 - c₂ 0) := by
    rw [h0]; linarith
  have hev1 := ramseyPhase_eventually_gt_right (hx 0 le_rfl) hxd0
  have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < y s :=
    nhdsWithin_le_nhds ((hy 0 le_rfl).continuousAt.tendsto.eventually (lt_mem_nhds hy0))
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hev1.and hev2)
  have hεpos : ∀ t, t ∈ Set.Ioc 0 ε → 0 < x t ∧ 0 < y t := fun t ht => by
    have h := hεsub ht
    simp only [Set.mem_ofPred_eq, hx0] at h
    exact h
  have key : ∀ T, 0 < T → 0 < x T ∧ 0 < y T := by
    intro T hT
    by_contra hnot
    have hTε : ε ≤ T := by
      by_contra h
      exact hnot (hεpos T ⟨hT, (not_le.mp h).le⟩)
    set B : Set ℝ := {t | t ∈ Set.Icc ε T ∧ (x t ≤ 0 ∨ y t ≤ 0)} with hBdef
    have hB : B = (Set.Icc ε T ∩ x ⁻¹' Set.Iic 0) ∪ (Set.Icc ε T ∩ y ⁻¹' Set.Iic 0) := by
      ext t
      simp only [B, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_Iic, and_or_left]
    have hsub : Set.Icc ε T ⊆ Set.Ici 0 := fun t ht => (le_of_lt hε).trans ht.1
    have hBclosed : IsClosed B := by
      rw [hB]
      exact ((hxc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic).union
        ((hyc'.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
    have hTB : T ∈ B := by
      refine ⟨⟨hTε, le_rfl⟩, ?_⟩
      by_contra h
      push Not at h
      exact hnot ⟨h.1, h.2⟩
    have hBbdd : BddBelow B := ⟨ε, fun t ht => ht.1.1⟩
    set τ := sInf B with hτdef
    have hτB : τ ∈ B := hBclosed.csInf_mem ⟨T, hTB⟩ hBbdd
    have hετ : ε ≤ τ := hτB.1.1
    have hτT : τ ≤ T := hτB.1.2
    have hτ0 : 0 < τ := hε.trans_le hετ
    have hbefore : ∀ t, 0 < t → t < τ → 0 < x t ∧ 0 < y t := by
      intro t ht htτ
      by_cases htε : t ≤ ε
      · exact hεpos t ⟨ht, htε⟩
      · have hnB : t ∉ B := notMem_of_lt_csInf htτ hBbdd
        by_contra h
        refine hnB ⟨⟨(not_le.mp htε).le, htτ.le.trans hτT⟩, ?_⟩
        by_contra h'
        push Not at h'
        exact h ⟨h'.1, h'.2⟩
    have hord : ∀ t, 0 < t → t < τ → k₂ t ≤ k₁ t ∧ f (k₂ t) ≤ f (k₁ t) ∧
        deriv f (k₁ t) ≤ deriv f (k₂ t) ∧ c₁ t < c₂ t := by
      intro t ht htτ
      obtain ⟨hxt, hyt⟩ := hbefore t ht htτ
      have hk : k₂ t < k₁ t := by simp only [x] at hxt; linarith
      have hk2 := hk₂ t ht.le
      exact ⟨hk.le, hfm hk2 (hk2.trans hk) hk.le,
        hf'.antitoneOn hk2 (show (0 : ℝ) < k₁ t from hk2.trans hk) hk.le,
        (hyc t ht.le).mp hyt⟩
    -- the capital barrier
    have hxτ : 0 < x τ := by
      set X : ℝ → ℝ := fun t => Real.exp (δ * t) * x t
      have hXd : ∀ t, 0 ≤ t → HasDerivAt X (Real.exp (δ * t) * (δ * x t +
          ((f (k₁ t) - δ * k₁ t - c₁ t) - (f (k₂ t) - δ * k₂ t - c₂ t)))) t := by
        intro t ht
        have h' := (((hasDerivAt_id t).const_mul δ).exp).mul (hx t ht)
        have h : HasDerivAt X _ t := h'
        convert h using 1
        simp only [id, mul_one]
        ring
      have hmono : StrictMonoOn X (Set.Icc 0 τ) := by
        refine strictMonoOn_of_deriv_pos (convex_Icc 0 τ)
          (fun t ht => (hXd t ht.1).continuousAt.continuousWithinAt) fun t ht => ?_
        rw [interior_Icc] at ht
        rw [(hXd t ht.1.le).deriv]
        obtain ⟨-, hf2, -, hc⟩ := hord t ht.1 ht.2
        refine mul_pos (Real.exp_pos _) ?_
        simp only [x]
        linarith
      have h := hmono ⟨le_rfl, hτ0.le⟩ ⟨hτ0.le, le_rfl⟩ hτ0
      simp only [X, mul_zero, Real.exp_zero, one_mul] at h
      rw [hx0] at h
      exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h
    -- the costate barrier
    have hyτ : 0 < y τ := by
      have hcont : ContinuousOn (fun t => deriv f (k₂ t)) (Set.Icc 0 τ) :=
        P.f_prime_cont.comp (fun t ht => (hk₂d t ht.1).continuousAt.continuousWithinAt)
          fun t ht => hk₂ t ht.1
      obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcont
      have hMt : ∀ t ∈ Set.Icc 0 τ, deriv f (k₂ t) ≤ M := fun t ht => hM ⟨t, ht, rfl⟩
      set Y : ℝ → ℝ := fun t => Real.exp ((M - δ) * t) * y t
      have hYd : ∀ t, 0 ≤ t → HasDerivAt Y (Real.exp ((M - δ) * t) * ((M - δ) * y t +
          (-(μ₁ t * (deriv f (k₁ t) - δ)) - -(μ₂ t * (deriv f (k₂ t) - δ))))) t := by
        intro t ht
        have h' := (((hasDerivAt_id t).const_mul (M - δ)).exp).mul (hy t ht)
        have h : HasDerivAt Y _ t := h'
        convert h using 1
        simp only [id, mul_one]
        ring
      have hmono : MonotoneOn Y (Set.Icc 0 τ) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 τ)
          (fun t ht => (hYd t ht.1).continuousAt.continuousWithinAt)
          (fun t ht => (hYd t (interior_subset ht).1).differentiableAt.differentiableWithinAt)
          fun t ht => ?_
        rw [interior_Icc] at ht
        rw [(hYd t ht.1.le).deriv]
        obtain ⟨-, -, hfd, -⟩ := hord t ht.1 ht.2
        have hyt := (hbefore t ht.1 ht.2).2
        have hM' := hMt t ⟨ht.1.le, ht.2.le⟩
        have hμ := hμ₂pos t ht.1.le
        have e : (M - δ) * y t + (-(μ₁ t * (deriv f (k₁ t) - δ)) -
            -(μ₂ t * (deriv f (k₂ t) - δ))) =
            y t * (M - deriv f (k₁ t)) + μ₂ t * (deriv f (k₂ t) - deriv f (k₁ t)) := by
          simp only [y]; ring
        rw [e]
        refine mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg hyt.le ?_)
          (mul_nonneg hμ.le ?_)) <;> linarith
      have h := hmono ⟨le_rfl, hτ0.le⟩ ⟨hτ0.le, le_rfl⟩ hτ0.le
      simp only [Y, mul_zero, Real.exp_zero, one_mul] at h
      have := hy0.trans_le h
      exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp this
    rcases hτB.2 with h | h <;> linarith
  intro t ht
  obtain ⟨hxt, hyt⟩ := key t ht
  refine ⟨by simp only [x] at hxt; linarith, (hyc t ht.le).mp hyt⟩

/-- AKMM, p. 255 and Appendix 9.A.4: **the saddle path is the only path from `k(0)` that
satisfies the first-order conditions and the TVC.** Whenever the saddle path from `k(0)` is
constructed (the Cass optimum invests strictly; e.g. `0 < k(0) ≤ k**`), a solution of the
first-order system with `k > 0` that satisfies the TVC (9.34) starts on the saddle path:
`c(0) = policy P k(0)`. By `mangasarian_planner` it is catching-up optimal, and so is the saddle
path; if they differed, the average of the two capital paths, with the consumption it leaves
(at least the average consumption, by concavity of `f`), would beat it by a fixed margin, by
strict concavity of `u`. -/
theorem ramseyPhase_unique (P : CassPrimitives f U ρ δ) {k₀ : ℝ} (hk₀ : 0 < k₀)
    (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ)
    (hk : ∀ t, 0 ≤ t → 0 < k t) (h0 : k 0 = k₀)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0)) :
    c 0 = policy P k₀ := by
  obtain ⟨μs, hss, hs0, hsc0, hsb, -, -, -, hsopt⟩ := ramseyPhase_saddle P hk₀ hint
  set ks := (optimalPath P hk₀).capital
  set cs := (optimalPath P hk₀).consumption
  obtain ⟨hc, hcc, hkd, h9A1, h9A2⟩ := hsol
  obtain ⟨hcs, hccs, hksd, -, -⟩ := hss
  have hρ := P.d_pos
  by_contra hne
  rw [← hsc0] at hne
  have hks : ∀ t, 0 ≤ t → 0 < ks t := hsb
  set km : ℝ → ℝ := fun t => (k t + ks t) / 2 with hkmdef
  set cm : ℝ → ℝ := fun t => f (km t) - δ * km t -
    ((f (k t) - δ * k t - c t) + (f (ks t) - δ * ks t - cs t)) / 2 with hcmdef
  have hkm : ∀ t, 0 ≤ t → 0 < km t := fun t ht => by
    simp only [km]; linarith [hk t ht, hks t ht]
  have hkmd : ∀ t, 0 ≤ t → HasDerivAt km (f (km t) - δ * km t - cm t) t := fun t ht => by
    have h := ((hkd t ht).add (hksd t ht)).div_const 2
    convert h using 1
    simp only [cm]
    ring
  have hfmid : ∀ t, 0 ≤ t → (f (k t) + f (ks t)) / 2 ≤ f (km t) := fun t ht => by
    have h := P.f_conc.concaveOn.2 (Set.mem_Ici.mpr (hk t ht).le)
      (Set.mem_Ici.mpr (hks t ht).le) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at h
    simp only [km]
    convert h using 2 <;> ring
  have hcm : ∀ t, 0 ≤ t → (c t + cs t) / 2 ≤ cm t := fun t ht => by
    have := hfmid t ht
    simp only [cm, km] at this ⊢
    linarith
  have hcmpos : ∀ t, 0 ≤ t → 0 < cm t := fun t ht => by
    linarith [hcm t ht, hc t ht, hcs t ht]
  have hfc : ContinuousOn f (Set.Ioi 0) := fun x hx =>
    (P.f_diff x hx).continuousAt.continuousWithinAt
  have hkc : ContinuousOn k (Set.Ici 0) := fun t ht => (hkd t ht).continuousAt.continuousWithinAt
  have hksc : ContinuousOn ks (Set.Ici 0) := fun t ht =>
    (hksd t ht).continuousAt.continuousWithinAt
  have hkmc : ContinuousOn km (Set.Ici 0) := (hkc.add hksc).div_const 2
  have hfk : ContinuousOn (fun t => f (k t)) (Set.Ici 0) := hfc.comp hkc fun t ht => hk t ht
  have hfks : ContinuousOn (fun t => f (ks t)) (Set.Ici 0) :=
    hfc.comp hksc fun t ht => hks t ht
  have hfkm : ContinuousOn (fun t => f (km t)) (Set.Ici 0) :=
    hfc.comp hkmc fun t ht => hkm t ht
  have hcmc : ContinuousOn cm (Set.Ici 0) :=
    (hfkm.sub (continuousOn_const.mul hkmc)).sub
      ((((hfk.sub (continuousOn_const.mul hkc)).sub hcc).add
        ((hfks.sub (continuousOn_const.mul hksc)).sub hccs)).div_const 2)
  -- the two optimality statements
  have hA := (mangasarian_planner (f' := deriv f) P.f_conc.concaveOn P.U_conc.concaveOn
    (fun y hy => (P.U_diff y hy).hasDerivAt) (fun y hy => (P.U_prime_pos y hy).le) hk
    (fun t ht => (P.f_diff _ (hk t ht)).hasDerivAt) hc hcc hkd h9A1 h9A2 htvc
    (fun t ht => (hkm t ht).le) hcmpos hcmc hkmd (by simp only [km]; rw [hs0, h0]; ring)).1
  have hB := hsopt k c (fun t ht => (hk t ht).le) hc hcc hkd h0
  -- the strict concavity gap
  have hUc := P.U_cont
  set G : ℝ → ℝ := fun t => U ((c t + cs t) / 2) - (U (c t) + U (cs t)) / 2 with hGdef
  have hG0 : 0 < G 0 := by
    have h := P.U_conc.2 (Set.mem_Ioi.mpr (hc 0 le_rfl)) (Set.mem_Ioi.mpr (hcs 0 le_rfl)) hne
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at h
    simp only [G]
    have e : (c 0 + cs 0) / 2 = 1 / 2 * c 0 + 1 / 2 * cs 0 := by ring
    rw [e]
    linarith
  have hGnn : ∀ t, 0 ≤ t → 0 ≤ G t := fun t ht => by
    have h := P.U_conc.concaveOn.2 (Set.mem_Ioi.mpr (hc t ht)) (Set.mem_Ioi.mpr (hcs t ht))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at h
    simp only [G]
    have e : (c t + cs t) / 2 = 1 / 2 * c t + 1 / 2 * cs t := by ring
    rw [e]
    linarith
  have hUm : MonotoneOn U (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hUc
      (fun y hy => (P.U_diff y (interior_subset hy)).differentiableWithinAt) fun y hy => ?_
    rw [interior_Ioi] at hy
    exact (P.U_prime_pos y hy).le
  have hcavg : ∀ t, 0 ≤ t → 0 < (c t + cs t) / 2 := fun t ht => by
    linarith [hc t ht, hcs t ht]
  have hUcm : ∀ t, 0 ≤ t → U ((c t + cs t) / 2) ≤ U (cm t) := fun t ht =>
    hUm (hcavg t ht) (hcmpos t ht) (hcm t ht)
  -- continuity of the integrands
  have hE : Continuous fun t : ℝ => Real.exp (-ρ * t) := by fun_prop
  have hUcc : ContinuousOn (fun t => U (c t)) (Set.Ici 0) := hUc.comp hcc fun t ht => hc t ht
  have hUcsc : ContinuousOn (fun t => U (cs t)) (Set.Ici 0) :=
    hUc.comp hccs fun t ht => hcs t ht
  have hUcmc : ContinuousOn (fun t => U (cm t)) (Set.Ici 0) :=
    hUc.comp hcmc fun t ht => hcmpos t ht
  have hUavc : ContinuousOn (fun t => U ((c t + cs t) / 2)) (Set.Ici 0) :=
    hUc.comp ((hcc.add hccs).div_const 2) fun t ht => hcavg t ht
  have hGc : ContinuousOn G (Set.Ici 0) := hUavc.sub ((hUcc.add hUcsc).div_const 2)
  have hint : ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Ici 0) → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun t => Real.exp (-ρ * t) * g t) MeasureTheory.volume a b := by
    intro g hg a b ha hb
    refine ((hE.continuousOn).mul hg).mono ?_ |>.intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h
    · exact ha.trans h.1
    · exact hb.trans h.1
  -- a fixed welfare margin from the gap near `t = 0`
  have hev : ∀ᶠ t in 𝓝[≥] (0 : ℝ), G 0 / 2 < G t :=
    (hGc (0 : ℝ) (Set.mem_Ici.mpr le_rfl)).eventually (lt_mem_nhds (half_lt_self hG0))
  obtain ⟨t₀, ht₀, ht₀sub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hev
  set η := t₀ * (Real.exp (-ρ * t₀) * (G 0 / 2)) with hηdef
  have hη : 0 < η := mul_pos ht₀ (mul_pos (Real.exp_pos _) (half_pos hG0))
  have hgap : ∀ T, t₀ ≤ T → η ≤ ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * G t := by
    intro T hT
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint hGc 0 t₀ le_rfl ht₀.le)
      (hint hGc t₀ T ht₀.le (ht₀.le.trans hT))]
    have h1 : η ≤ ∫ t in (0 : ℝ)..t₀, Real.exp (-ρ * t) * G t := by
      have h := intervalIntegral.integral_mono_on ht₀.le
        (intervalIntegrable_const (μ := MeasureTheory.volume)
          (c := Real.exp (-ρ * t₀) * (G 0 / 2))) (hint hGc 0 t₀ le_rfl ht₀.le)
        fun t htt => by
          have hGt := ht₀sub htt
          simp only [Set.mem_ofPred_eq] at hGt
          refine mul_le_mul (Real.exp_le_exp.mpr ?_) hGt.le (half_pos hG0).le
            (Real.exp_pos _).le
          nlinarith [htt.2]
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
      exact h
    have h2 : 0 ≤ ∫ t in t₀..T, Real.exp (-ρ * t) * G t :=
      intervalIntegral.integral_nonneg hT fun t htt =>
        mul_nonneg (Real.exp_pos _).le (hGnn t (ht₀.le.trans htt.1))
    linarith
  have hlow : ∀ T, 0 ≤ T → (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (c t)) / 2 +
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (cs t)) / 2 +
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * G t) ≤
      ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (cm t) := by
    intro T hT
    have e : (fun t => Real.exp (-ρ * t) * U ((c t + cs t) / 2)) = fun t =>
        (1 / 2 * (Real.exp (-ρ * t) * U (c t)) + 1 / 2 * (Real.exp (-ρ * t) * U (cs t))) +
          Real.exp (-ρ * t) * G t := by
      funext t; simp only [G]; ring
    have hmono := intervalIntegral.integral_mono_on hT (hint hUavc 0 T le_rfl hT)
      (hint hUcmc 0 T le_rfl hT) fun t htt =>
        mul_le_mul_of_nonneg_left (hUcm t htt.1) (Real.exp_pos _).le
    rw [e, intervalIntegral.integral_add (((hint hUcc 0 T le_rfl hT).const_mul (1 / 2)).add
      ((hint hUcsc 0 T le_rfl hT).const_mul (1 / 2))) (hint hGc 0 T le_rfl hT),
      intervalIntegral.integral_add ((hint hUcc 0 T le_rfl hT).const_mul (1 / 2))
        ((hint hUcsc 0 T le_rfl hT).const_mul (1 / 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    linarith
  obtain ⟨T, hT⟩ := ((hA (η / 4) (by positivity)).and ((hB (η / 4) (by positivity)).and
    (eventually_ge_atTop t₀))).exists
  have h1 := hlow T (ht₀.le.trans hT.2.2)
  have h2 := hgap T hT.2.2
  linarith [hT.1, hT.2.1]

/-- AKMM, (9.A.1)–(9.A.3), p. 846: along a solution, `e^{ρt}μ(t) = u'(c(t))` and it grows at
the rate `ρ + δ − f'(k)`, i.e. `(d/dt) log u'(c) = −(f'(k) − (δ + ρ))`. -/
theorem ramseyPhase_marginal_utility {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (ρ * t) * μ t = deriv U (c t) ∧
      HasDerivAt (fun s => Real.exp (ρ * s) * μ s)
        (Real.exp (ρ * t) * μ t * (ρ + δ - deriv f (k t))) t := by
  obtain ⟨-, -, -, h9A1, h9A2⟩ := hsol
  refine ⟨?_, ?_⟩
  · rw [h9A1 t ht, ← mul_assoc, ← Real.exp_add]
    simp
  · have h' := (((hasDerivAt_id t).const_mul ρ).exp).mul (h9A2 t ht)
    have h : HasDerivAt (fun s => Real.exp (ρ * s) * μ s) _ t := h'
    convert h using 1
    simp only [id, mul_one]
    ring

/-- AKMM, p. 255 and (9.34): a solution whose capital stays in `(0, k**]` satisfies the TVC:
`ċ ≥ 0` there, so `u'(c(T)) ≤ u'(c(0))` and `e^{−ρT}u'(c(T))k(T) ≤ e^{−ρT}u'(c(0))k** → 0`. -/
theorem ramseyPhase_tvc_of_le_steady (P : CassPrimitives f U ρ δ) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (hk : ∀ t, 0 ≤ t → 0 < k t)
    (hkle : ∀ t, 0 ≤ t → k t ≤ cassSteady P) :
    Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0) := by
  obtain ⟨hks, hks'⟩ := cassSteady_spec P
  have hc := hsol.1
  have hanti : AntitoneOn (fun s => Real.exp (ρ * s) * μ s) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t ht => ((ramseyPhase_marginal_utility hsol ht).2).continuousAt.continuousWithinAt)
      (fun t ht => ((ramseyPhase_marginal_utility hsol
        (interior_subset ht)).2).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    obtain ⟨he, hd⟩ := ramseyPhase_marginal_utility hsol ht'
    rw [hd.deriv, he]
    have h1 := (ramseyPhase_fprime_anti P).antitoneOn (hk t ht') hks (hkle t ht')
    exact mul_nonpos_of_nonneg_of_nonpos (P.U_prime_pos _ (hc t ht')).le (by linarith)
  have hle : ∀ T, 0 ≤ T → deriv U (c T) ≤ deriv U (c 0) := fun T hT => by
    rw [← (ramseyPhase_marginal_utility hsol hT).1,
      ← (ramseyPhase_marginal_utility hsol le_rfl).1]
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT
  have hup : Tendsto (fun T => Real.exp (-ρ * T) * (deriv U (c 0) * cassSteady P)) atTop
      (𝓝 0) := by
    simpa using (mangasarian_exp_neg_tendsto P.d_pos).mul_const (deriv U (c 0) * cassSteady P)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (P.U_prime_pos _ (hc T hT)).le)
      (hk T hT).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact mul_le_mul (hle T hT) (hkle T hT) (hk T hT).le (P.U_prime_pos _ (hc 0 le_rfl)).le

/-- AKMM, p. 255, Figure 9.2: **a larger `c(0)` cannot be continued for ever.** Whenever the
saddle path from `k(0)` is constructed (the Cass optimum invests strictly; every
`0 < k(0) ≤ k**` and every `k(0) ∈ (k**, k̂]`), no solution of the first-order system starting
above it keeps `k(t) > 0` at every date: by `ramseyPhase_comparison` it would have less capital
and more consumption than the saddle path, so `k` bounded and `c` bounded away from `0`; it
would then satisfy the TVC and by `ramseyPhase_unique` start on the saddle path. -/
theorem ramseyPhase_above_saddle_not_global (P : CassPrimitives f U ρ δ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (hk : ∀ t, 0 ≤ t → 0 < k t) (h0 : k 0 = k₀)
    (habove : policy P k₀ < c 0) : False := by
  obtain ⟨μs, hss, hs0, hsc0, -, -, -, ⟨K, C, hC, hKC⟩, -⟩ := ramseyPhase_saddle P hk₀ hint
  have hcmp := ramseyPhase_comparison P hss hsol hk (hs0.trans h0.symm) (hsc0 ▸ habove)
  have hc := hsol.1
  have hU := ramseyPhase_uprime_anti P
  have hup : Tendsto (fun T => Real.exp (-ρ * T) * (deriv U C * K)) atTop (𝓝 0) := by
    simpa using (mangasarian_exp_neg_tendsto P.d_pos).mul_const (deriv U C * K)
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (P.U_prime_pos _ (hc T hT)).le)
        (hk T hT).le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hcT : C ≤ c T := (hKC T hT.le).2.trans (hcmp T hT).2.le
      have hkT : k T ≤ K := (hcmp T hT).1.le.trans (hKC T hT.le).1
      exact mul_le_mul (hU.antitoneOn hC (hC.trans_le hcT) hcT) hkT (hk T hT.le).le
        (P.U_prime_pos _ hC).le
  have hc0 := ramseyPhase_unique P hk₀ hint hsol hk h0 htvc
  linarith

/-- AKMM, p. 255: **a larger `c(0)` drives capital to zero in finite time.** Let `k` be
continuous on `[0, ∞)` with `k(0) = k₀ > 0` where the saddle path is constructed (as in
`ramseyPhase_above_saddle_not_global`), and let `(k, c, μ)` satisfy the first-order
system at every date `t` before which capital has stayed positive. If `c(0)` is above the saddle
path, then there is a date `T > 0` with `k(T) = 0` and `k > 0` on `[0, T)`; at `T` the economy
produces nothing and the Euler path becomes infeasible (`ramseyPlanner_zero_capital_infeasible`). -/
theorem ramseyPhase_above_saddle_reaches_zero (P : CassPrimitives f U ρ δ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) {k c μ : ℝ → ℝ}
    (hkc : ContinuousOn k (Set.Ici 0)) (h0 : k 0 = k₀) (habove : policy P k₀ < c 0)
    (hloc : ∀ t, 0 ≤ t → (∀ s ∈ Set.Icc 0 t, 0 < k s) → 0 < c t ∧ ContinuousAt c t ∧
      HasDerivAt k (f (k t) - δ * k t - c t) t ∧ μ t = Real.exp (-ρ * t) * deriv U (c t) ∧
      HasDerivAt μ (-(μ t * (deriv f (k t) - δ))) t) :
    ∃ T, 0 < T ∧ k T = 0 ∧ ∀ t ∈ Set.Ico 0 T, 0 < k t := by
  by_cases hall : ∀ t, 0 ≤ t → 0 < k t
  · exfalso
    have hl := fun t (ht : 0 ≤ t) => hloc t ht fun s hs => hall s hs.1
    refine ramseyPhase_above_saddle_not_global P hk₀ hint (c := c) (μ := μ)
      ⟨fun t ht => (hl t ht).1, fun t ht => (hl t ht).2.1.continuousWithinAt,
        fun t ht => (hl t ht).2.2.1, fun t ht => (hl t ht).2.2.2.1,
        fun t ht => (hl t ht).2.2.2.2⟩ hall h0 habove
  push Not at hall
  obtain ⟨t₁, ht₁, hkt₁⟩ := hall
  set S : Set ℝ := Set.Icc 0 t₁ ∩ k ⁻¹' Set.Iic 0 with hSdef
  have hSc : IsClosed S :=
    (hkc.mono Set.Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t₁, ⟨ht₁, le_rfl⟩, hkt₁⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set T := sInf S with hTdef
  have hTS : T ∈ S := hSc.csInf_mem hSne hSb
  have hT0 : 0 ≤ T := hTS.1.1
  have hkT : k T ≤ 0 := hTS.2
  have hbefore : ∀ t ∈ Set.Ico 0 T, 0 < k t := by
    intro t ht
    have hnS : t ∉ S := notMem_of_lt_csInf ht.2 hSb
    by_contra h
    exact hnS ⟨⟨ht.1, ht.2.le.trans hTS.1.2⟩, not_lt.mp h⟩
  have hTpos : 0 < T := by
    rcases hT0.lt_or_eq with h | h
    · exact h
    · rw [← h, h0] at hkT; linarith
  have hcont : ContinuousAt k T := (hkc T hT0).continuousAt (Ici_mem_nhds hTpos)
  have hge : 0 ≤ k T := by
    refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio T))) ?_
    filter_upwards [Ioo_mem_nhdsLT hTpos] with t ht
    exact (hbefore t ⟨ht.1.le, ht.2⟩).le
  exact ⟨T, hTpos, le_antisymm hkT hge, hbefore⟩

/-- AKMM, p. 255, Figure 9.2: the dash-dot curve `c = f(k) − δk` meets the capital axis at most
once at `k > 0`: positive solutions of `f(k) = δk` are unique (strict concavity, `f(0) = 0`). -/
theorem ramseyPhase_root_unique (P : CassPrimitives f U ρ δ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfa : f a = δ * a) (hfb : f b = δ * b) : a = b := by
  have key : ∀ x y : ℝ, 0 < x → x < y → f x = δ * x → f y = δ * y → False := by
    intro x y hx hxy hfx hfy
    have hy : 0 < y := hx.trans hxy
    have h := P.f_conc.2 (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr le_rfl) hy.ne'
      (div_pos hx hy) (sub_pos.mpr ((div_lt_one hy).mpr hxy)) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, P.f_zero] at h
    rw [div_mul_cancel₀ x hy.ne', hfy, hfx] at h
    have : x / y * (δ * y) = δ * x := by field_simp
    linarith
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b ha h hfa hfb).elim
  · exact h
  · exact (key b a hb h hfb hfa).elim

/-- If `k → k̄` and `k̇ = D` with `D → L`, then `L = 0`. -/
theorem ramseyPhase_deriv_limit {k D : ℝ → ℝ} {t₀ kbar L : ℝ}
    (hkd : ∀ t, t₀ ≤ t → HasDerivAt k (D t) t) (hk : Tendsto k atTop (𝓝 kbar))
    (hD : Tendsto D atTop (𝓝 L)) : L = 0 := by
  have key : ∀ {k D : ℝ → ℝ} {kbar L : ℝ}, (∀ t, t₀ ≤ t → HasDerivAt k (D t) t) →
      Tendsto k atTop (𝓝 kbar) → Tendsto D atTop (𝓝 L) → L ≤ 0 := by
    intro k D kbar L hkd hk hD
    by_contra hL
    rw [not_le] at hL
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (((hD.eventually (lt_mem_nhds (half_lt_self hL))).and
      (hk.eventually (gt_mem_nhds (lt_add_one kbar)))).and (eventually_ge_atTop t₀))
    have hmono : MonotoneOn (fun t => k t - L / 2 * t) (Set.Ici T₁) := by
      have hT₁0 : t₀ ≤ T₁ := (hT₁ T₁ le_rfl).2
      refine monotoneOn_of_deriv_nonneg (convex_Ici T₁)
        (fun t ht => ((hkd t (hT₁0.trans ht)).sub
          ((hasDerivAt_id' t).const_mul (L / 2))).continuousAt.continuousWithinAt)
        (fun t ht => ((hkd t (hT₁0.trans (interior_subset ht))).sub
          ((hasDerivAt_id' t).const_mul (L / 2))).differentiableAt.differentiableWithinAt)
        fun t ht => ?_
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun t => k t - L / 2 * t) _ t :=
        (hkd t (hT₁0.trans (le_of_lt ht))).sub ((hasDerivAt_id' t).const_mul (L / 2))
      rw [hd.deriv]
      linarith [(hT₁ t (le_of_lt ht)).1.1]
    have hkT₁ := (hT₁ T₁ le_rfl).1.2
    set t₃ := T₁ + 2 * (kbar + 1 - k T₁) / L + 1
    have hT₁t₃ : T₁ ≤ t₃ := by
      have : 0 ≤ 2 * (kbar + 1 - k T₁) / L := div_nonneg (by linarith) hL.le
      linarith
    have h1 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT₁t₃) hT₁t₃
    have h2 := (hT₁ t₃ hT₁t₃).1.2
    simp only at h1
    have e : L / 2 * t₃ - L / 2 * T₁ = kbar + 1 - k T₁ + L / 2 := by
      simp only [t₃]; field_simp; ring
    linarith
  have h1 := key hkd hk hD
  have h2 := key (fun t ht => (hkd t ht).neg) hk.neg hD.neg
  linarith

/-- AKMM, Appendix 9.A.4, pp. 847–848: the end of a path below the saddle path. If a solution
with `k > 0` has `c → 0` and `k → k^u > k**` with `f(k^u) = δk^u`, and stays right of `k**` after
some date, then `f'(k^u) < δ`; after a finite date `t̄` it is in `f'(k) < δ` for good, above some
`x̂ + η` with `f'(x̂) < δ`, `η > 0`; and the TVC fails, since `μ = e^{−ρt}u'(c)` rises there. -/
theorem ramseyPhase_tail (P : CassPrimitives f U ρ δ) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) {ku t₁ : ℝ}
    (hku : cassSteady P < ku) (hroot : f ku = δ * ku) (hkt : Tendsto k atTop (𝓝 ku))
    (ht₁ : 0 ≤ t₁) (hgt : ∀ t, t₁ ≤ t → cassSteady P < k t) :
    deriv f ku < δ ∧
    (∃ tbar, 0 ≤ tbar ∧ (∀ t, tbar ≤ t → deriv f (k t) < δ ∧ cassSteady P < k t) ∧
      ∃ xh η, 0 < xh ∧ 0 < η ∧ deriv f xh < δ ∧ ∀ t, tbar ≤ t → xh + η ≤ k t) ∧
    ¬ Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0) := by
  obtain ⟨hkss, -⟩ := cassSteady_spec P
  set kss := cassSteady P
  obtain ⟨hc, -, -, h9A1, h9A2⟩ := hsol
  have hku0 : 0 < ku := hkss.trans hku
  have hfku : deriv f ku < δ := by
    have h := P.f_conc.concaveOn.deriv_le_slope (Set.mem_Ici.mpr hkss.le)
      (Set.mem_Ici.mpr hku0.le) hku (P.f_diff ku hku0)
    rw [slope_def_field, hroot] at h
    have hcs : 0 < f kss - δ * kss := cassSteadyConsumption_pos P
    have : (δ * ku - f kss) / (ku - kss) < δ := by
      rw [div_lt_iff₀ (sub_pos.mpr hku)]; linarith
    linarith
  have hf'c : ContinuousAt (deriv f) ku := P.f_prime_cont.continuousAt (Ioi_mem_nhds hku0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hf'c.eventually (gt_mem_nhds hfku))
  set w := min ε (ku - kss) with hwdef
  have hw : 0 < w := lt_min hε (sub_pos.mpr hku)
  set xh := ku - w / 2
  set η := w / 4
  have hxh : kss < xh := by
    have : w ≤ ku - kss := min_le_right _ _
    simp only [xh]; linarith
  have hfxh : deriv f xh < δ := by
    refine hball ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> simp only [xh] <;> linarith [min_le_left ε (ku - kss)]
  have hlt : xh + η < ku := by simp only [xh, η]; linarith
  obtain ⟨T₄, hT₄⟩ := eventually_atTop.mp
    (((hf'c.tendsto.comp hkt).eventually (gt_mem_nhds hfku)).and
      (hkt.eventually (lt_mem_nhds hlt)))
  set tbar := max T₄ t₁ with htbardef
  have htbar0 : 0 ≤ tbar := ht₁.trans (le_max_right _ _)
  have hreg : ∀ t, tbar ≤ t → deriv f (k t) < δ ∧ kss < k t := fun t ht =>
    ⟨(hT₄ t ((le_max_left _ _).trans ht)).1, hgt t ((le_max_right _ _).trans ht)⟩
  refine ⟨hfku, ⟨tbar, htbar0, hreg, xh, η, hkss.trans hxh, by positivity, hfxh,
    fun t ht => (hT₄ t ((le_max_left _ _).trans ht)).2.le⟩, fun htvc => ?_⟩
  have hμmono : MonotoneOn μ (Set.Ici tbar) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici tbar)
      (fun t ht => (h9A2 t (htbar0.trans ht)).continuousAt.continuousWithinAt)
      (fun t ht => (h9A2 t
        (htbar0.trans (interior_subset ht))).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici] at ht
    have ht' : 0 ≤ t := htbar0.trans (le_of_lt ht)
    rw [(h9A2 t ht').deriv, h9A1 t ht']
    have hμ := mul_pos (Real.exp_pos (-ρ * t)) (P.U_prime_pos _ (hc t ht'))
    have := (hreg t (le_of_lt ht)).1
    nlinarith
  have hμ0 : 0 < μ tbar := by
    rw [h9A1 tbar htbar0]
    exact mul_pos (Real.exp_pos _) (P.U_prime_pos _ (hc tbar htbar0))
  have hpos : 0 < μ tbar * kss := mul_pos hμ0 hkss
  obtain ⟨T, hT1, hT2⟩ := ((htvc.eventually (gt_mem_nhds hpos)).and
    (eventually_ge_atTop tbar)).exists
  rw [← h9A1 T (htbar0.trans hT2)] at hT1
  have h1 := hμmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT2) hT2
  have h2 := (hreg T hT2).2
  have := mul_le_mul h1 h2.le hkss.le (hμ0.le.trans h1)
  linarith

/-- AKMM, p. 255, Figure 9.2: **a path that gains `k̇ > 0` right of `k**` keeps rising.** If a
solution with `k > 0` has `k(t₀) ≥ k**` and `k̇(t₀) > 0`, then `k̇ > 0` for ever after (at a
first loss `u'(c) − u'(f(k) − δk)` would have positive derivative while turning from positive to
zero), `u'(c) → ∞`, so `c → 0`, and `k` rises to a root `k^u > k**` of `f(k) = δk`. -/
theorem ramseyPhase_rising (P : CassPrimitives f U ρ δ) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (hk : ∀ t, 0 ≤ t → 0 < k t) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (hkt₀ : cassSteady P ≤ k t₀) (hDt₀ : 0 < f (k t₀) - δ * k t₀ - c t₀) :
    (∀ t, t₀ < t → cassSteady P < k t) ∧ Tendsto c atTop (𝓝 0) ∧
      ∃ ku, cassSteady P < ku ∧ f ku = δ * ku ∧ Tendsto k atTop (𝓝 ku) := by
  obtain ⟨hkss, hkss'⟩ := cassSteady_spec P
  set kss := cassSteady P with hkssdef
  have hsol' := hsol
  obtain ⟨hc, hcc, hkd, h9A1, h9A2⟩ := hsol'
  have hU := ramseyPhase_uprime_anti P
  have hf' := ramseyPhase_fprime_anti P
  have hρ := P.d_pos
  have hkc : ContinuousOn k (Set.Ici 0) := fun t ht => (hkd t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Set.Ioi 0) := fun x hx =>
    (P.f_diff x hx).continuousAt.continuousWithinAt
  set D : ℝ → ℝ := fun t => f (k t) - δ * k t - c t with hDdef
  have hDc : ContinuousOn D (Set.Ici 0) :=
    ((hfc.comp hkc fun t ht => hk t ht).sub (continuousOn_const.mul hkc)).sub hcc
  -- `k̇ > 0` is never lost after `t₀`
  have hDpos : ∀ t, t₀ ≤ t → 0 < D t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t', ht', hDt'⟩ := hcon
    set S : Set ℝ := Set.Icc t₀ t' ∩ D ⁻¹' Set.Iic 0 with hSdef
    have hSc : IsClosed S := (hDc.mono fun t ht => ht₀.trans ht.1).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
    have hSb : BddBelow S := ⟨t₀, fun t ht => ht.1.1⟩
    set τ := sInf S with hτdef
    have hτS : τ ∈ S := hSc.csInf_mem ⟨t', ⟨ht', le_rfl⟩, hDt'⟩ hSb
    have hτt₀ : t₀ < τ := by
      rcases hτS.1.1.lt_or_eq with h | h
      · exact h
      · have := hτS.2
        rw [← h] at this
        simp only [Set.mem_preimage, Set.mem_Iic] at this
        linarith
    have hτ0 : 0 < τ := lt_of_le_of_lt ht₀ hτt₀
    have hbefore : ∀ t ∈ Set.Ico t₀ τ, 0 < D t := by
      intro t ht
      have hnS : t ∉ S := notMem_of_lt_csInf ht.2 hSb
      by_contra h
      exact hnS ⟨⟨ht.1, ht.2.le.trans hτS.1.2⟩, not_lt.mp h⟩
    have hkmono : StrictMonoOn k (Set.Icc t₀ τ) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc t₀ τ)
        (fun t ht => (hkd t (ht₀.trans ht.1)).continuousAt.continuousWithinAt) fun t ht => ?_
      rw [interior_Icc] at ht
      rw [(hkd t (ht₀.trans ht.1.le)).deriv]
      exact hbefore t ⟨ht.1.le, ht.2⟩
    have hkτ : kss < k τ :=
      hkt₀.trans_lt (hkmono ⟨le_rfl, hτt₀.le⟩ ⟨hτt₀.le, le_rfl⟩ hτt₀)
    have hDcτ : ContinuousAt D τ := (hDc τ hτ0.le).continuousAt (Ici_mem_nhds hτ0)
    have hDτ : D τ = 0 := by
      refine le_antisymm hτS.2 (ge_of_tendsto
        (hDcτ.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio τ))) ?_)
      filter_upwards [Ioo_mem_nhdsLT hτt₀] with t ht
      exact (hbefore t ⟨ht.1.le, ht.2⟩).le
    have hFτ : 0 < f (k τ) - δ * k τ := by
      have := hc τ hτ0.le
      simp only [D] at hDτ
      linarith
    -- `E = u'(c) − u'(f(k) − δk)` would have positive derivative at `τ`
    obtain ⟨heτ, hφd⟩ := ramseyPhase_marginal_utility hsol hτ0.le
    have hFk : HasDerivAt (fun t => f (k t) - δ * k t)
        (deriv f (k τ) * D τ - δ * D τ) τ :=
      ((P.f_diff _ (hk τ hτ0.le)).hasDerivAt.comp τ (hkd τ hτ0.le)).sub
        ((hkd τ hτ0.le).const_mul δ)
    have hUFk := (P.U_second _ hFτ).hasDerivAt.comp τ hFk
    have hE := hφd.sub hUFk
    rw [hDτ] at hE
    have hEpos : 0 < Real.exp (ρ * τ) * μ τ * (ρ + δ - deriv f (k τ)) -
        deriv (deriv U) (f (k τ) - δ * k τ) * (deriv f (k τ) * 0 - δ * 0) := by
      have h1 : deriv f (k τ) < deriv f kss := hf' hkss (hk τ hτ0.le) hkτ
      rw [heτ]
      simp only [mul_zero, sub_zero]
      exact mul_pos (P.U_prime_pos _ (hc τ hτ0.le)) (by linarith)
    have hev := ramseyPhase_eventually_lt_left hE hEpos
    have hFev : ∀ᶠ t in 𝓝[<] τ, 0 < f (k t) - δ * k t :=
      nhdsWithin_le_nhds (hFk.continuousAt.tendsto.eventually (lt_mem_nhds hFτ))
    obtain ⟨t, ⟨h1, h3⟩, h4⟩ :=
      ((hev.and hFev).and (Ioo_mem_nhdsLT hτt₀)).exists
    have ht0' : 0 ≤ t := ht₀.trans h4.1.le
    have hcτ : c τ = f (k τ) - δ * k τ := by simp only [D] at hDτ; linarith
    simp only [Pi.sub_apply, Function.comp_apply] at h1
    rw [(ramseyPhase_marginal_utility hsol ht0').1, heτ, hcτ, sub_self] at h1
    have h1' : deriv U (c t) < deriv U (f (k t) - δ * k t) := by linarith
    have := (hU.lt_iff_gt (hc t ht0') h3).mp h1'
    have := hbefore t ⟨h4.1.le, h4.2⟩
    simp only [D] at this
    linarith
  -- capital rises for good after `t₀`
  have hkmono : StrictMonoOn k (Set.Ici t₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici t₀)
      (fun t ht => (hkd t (ht₀.trans ht)).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hkd t (ht₀.trans (le_of_lt ht))).deriv]
    exact hDpos t (le_of_lt ht)
  have hkge : ∀ t, t₀ < t → kss < k t := fun t ht =>
    hkt₀.trans_lt (hkmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht)
  -- `u'(c) → ∞`, hence `c → 0`
  set t₂ := t₀ + 1 with ht₂def
  have ht₂ : 0 ≤ t₂ := by linarith
  have hk₂ : kss < k t₂ := hkge t₂ (by linarith)
  set γ := ρ + δ - deriv f (k t₂) with hγdef
  have hγ : 0 < γ := by
    have := hf' hkss (hk t₂ ht₂) hk₂
    simp only [γ]; linarith
  set ψ : ℝ → ℝ := fun t => Real.exp (-γ * t) * (Real.exp (ρ * t) * μ t) with hψdef
  have hψd : ∀ t, 0 ≤ t → HasDerivAt ψ (Real.exp (-γ * t) * (Real.exp (ρ * t) * μ t) *
      (deriv f (k t₂) - deriv f (k t))) t := fun t ht => by
    have h' := (((hasDerivAt_id t).const_mul (-γ)).exp).mul
      (ramseyPhase_marginal_utility hsol ht).2
    have h : HasDerivAt ψ _ t := h'
    convert h using 1
    simp only [id, mul_one, γ]
    ring
  have hψmono : MonotoneOn ψ (Set.Ici t₂) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici t₂)
      (fun t ht => (hψd t (ht₂.trans ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hψd t (ht₂.trans (interior_subset ht))).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici] at ht
    have ht' : 0 ≤ t := ht₂.trans (le_of_lt ht)
    rw [(hψd t ht').deriv, (ramseyPhase_marginal_utility hsol ht').1]
    have ht'' : t₂ < t := ht
    have hkt : k t₂ ≤ k t := hkmono.monotoneOn (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (le_of_lt ht)
    have := hf'.antitoneOn (hk t₂ ht₂) (hk t ht') hkt
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (P.U_prime_pos _ (hc t ht')).le)
      (by linarith)
  have hψ₂ : 0 < ψ t₂ := by
    simp only [ψ]
    rw [(ramseyPhase_marginal_utility hsol ht₂).1]
    exact mul_pos (Real.exp_pos _) (P.U_prime_pos _ (hc t₂ ht₂))
  have hUc : Tendsto (fun t => deriv U (c t)) atTop atTop := by
    have hlow : Tendsto (fun t => Real.exp (γ * t) * ψ t₂) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hγ)).atTop_mul_const hψ₂
    refine tendsto_atTop_mono' atTop ?_ hlow
    filter_upwards [eventually_ge_atTop t₂] with t ht
    have h := hψmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    rw [← (ramseyPhase_marginal_utility hsol (ht₂.trans ht)).1]
    have e : Real.exp (ρ * t) * μ t = Real.exp (γ * t) * ψ t := by
      simp only [ψ]
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hc0 : Tendsto c atTop (𝓝 0) := by
    refine tendsto_order.mpr ⟨fun a ha => ?_, fun ε hε => ?_⟩
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact ha.trans (hc t ht)
    · filter_upwards [hUc.eventually_gt_atTop (deriv U ε), eventually_ge_atTop (0 : ℝ)]
        with t h1 ht
      by_contra h
      have := hU.antitoneOn (Set.mem_Ioi.mpr hε) (Set.mem_Ioi.mpr (hc t ht)) (not_lt.mp h)
      linarith
  -- capital converges to the upper root `k^u`
  obtain ⟨K, -, hcap⟩ := P.exists_capacity (k 0)
  have hkK : ∀ t, t₀ ≤ t → k t < K := fun t ht => by
    by_contra h
    have := hcap (k t) (not_lt.mp h)
    have := hDpos t ht
    have := hc t (ht₀.trans ht)
    simp only [D] at *
    linarith
  set g : ℝ → ℝ := fun t => k (max t t₀) with hgdef
  have hgmono : Monotone g := fun a b hab =>
    hkmono.monotoneOn (Set.mem_Ici.mpr (le_max_right _ _)) (Set.mem_Ici.mpr (le_max_right _ _))
      (max_le_max hab le_rfl)
  have hgbdd : BddAbove (Set.range g) :=
    ⟨K, by rintro _ ⟨t, rfl⟩; exact (hkK _ (le_max_right _ _)).le⟩
  set ku := ⨆ t, g t with hkudef
  have hgt : Tendsto g atTop (𝓝 ku) := tendsto_atTop_ciSup hgmono hgbdd
  have hkt : Tendsto k atTop (𝓝 ku) := by
    refine hgt.congr' ?_
    filter_upwards [eventually_ge_atTop t₀] with t ht
    simp only [g, max_eq_left ht]
  have hkuk : ∀ t, k (max t t₀) ≤ ku := fun t => le_ciSup hgbdd t
  have hku : kss < ku := by
    have := hkuk t₂
    rw [max_eq_left (by linarith : t₀ ≤ t₂)] at this
    linarith
  have hku0 : 0 < ku := hkss.trans hku
  have hFc : ContinuousAt (fun x => f x - δ * x) ku :=
    (P.f_diff ku hku0).continuousAt.sub (continuousAt_const.mul continuousAt_id)
  have hDt : Tendsto D atTop (𝓝 (f ku - δ * ku - 0)) :=
    (hFc.tendsto.comp hkt).sub hc0
  have hDt : Tendsto D atTop (𝓝 (f ku - δ * ku - 0)) :=
    (hFc.tendsto.comp hkt).sub hc0
  have hroot : f ku = δ * ku := by
    have := ramseyPhase_deriv_limit (t₀ := 0) (fun t ht => hkd t ht) hkt hDt
    linarith
  exact ⟨hkge, hc0, ku, hku, hroot, hkt⟩

/-- AKMM, p. 255, Figure 9.2: **a path right of `k**` with `k̇ ≤ 0` for ever.** If a solution with
`k > 0` stays right of `k**` with `k̇ ≤ 0` at every `t > 0`, and does not satisfy the TVC, then
`c → 0` and `k` falls to a root `k^u > k**` of `f(k) = δk`: `u'(c)` rises, so `c` falls; a
positive limit of `c` would give the TVC. -/
theorem ramseyPhase_falling (P : CassPrimitives f U ρ δ) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (hk : ∀ t, 0 ≤ t → 0 < k t)
    (hgt : ∀ t, 0 < t → cassSteady P < k t) (hD : ∀ t, 0 < t → f (k t) - δ * k t - c t ≤ 0)
    (hntvc : ¬ Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0)) :
    Tendsto c atTop (𝓝 0) ∧
      ∃ ku, cassSteady P < ku ∧ f ku = δ * ku ∧ Tendsto k atTop (𝓝 ku) := by
  obtain ⟨hkss, hkss'⟩ := cassSteady_spec P
  set kss := cassSteady P with hkssdef
  have hsol' := hsol
  obtain ⟨hc, hcc, hkd, h9A1, h9A2⟩ := hsol'
  have hU := ramseyPhase_uprime_anti P
  have hf' := ramseyPhase_fprime_anti P
  have hkanti : AntitoneOn k (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t ht => (hkd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hkd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hkd t (le_of_lt ht)).deriv]
    exact hD t ht
  have hkge : ∀ t, 0 ≤ t → kss < k t := fun t ht => by
    rcases ht.lt_or_eq with h | rfl
    · exact hgt t h
    · exact (hgt 1 one_pos).trans_le (hkanti (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr zero_le_one) zero_le_one)
  have hqmono : MonotoneOn (fun s => Real.exp (ρ * s) * μ s) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t ht => ((ramseyPhase_marginal_utility hsol ht).2).continuousAt.continuousWithinAt)
      (fun t ht => ((ramseyPhase_marginal_utility hsol
        (interior_subset ht)).2).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    obtain ⟨he, hd⟩ := ramseyPhase_marginal_utility hsol ht'
    rw [hd.deriv, he]
    have h1 := hf' hkss (hk t ht') (hkge t ht')
    exact mul_nonneg (P.U_prime_pos _ (hc t ht')).le (by linarith)
  have hcanti : ∀ a b, 0 ≤ a → a ≤ b → c b ≤ c a := fun a b ha hab => by
    have h := hqmono (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
    simp only at h
    rw [(ramseyPhase_marginal_utility hsol ha).1,
      (ramseyPhase_marginal_utility hsol (ha.trans hab)).1] at h
    exact (hU.le_iff_ge (hc a ha) (hc b (ha.trans hab))).mp h
  -- limits of `c` and `k`
  set gc : ℝ → ℝ := fun t => c (max t 0)
  have hgca : Antitone gc := fun a b hab =>
    hcanti _ _ (le_max_right _ _) (max_le_max hab le_rfl)
  have hgcb : BddBelow (Set.range gc) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact (hc _ (le_max_right _ _)).le⟩
  set cinf := ⨅ t, gc t
  have hct : Tendsto c atTop (𝓝 cinf) := by
    refine (tendsto_atTop_ciInf hgca hgcb).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [gc, max_eq_left ht]
  have hcinf : ∀ t, 0 ≤ t → cinf ≤ c t := fun t ht => by
    have := ciInf_le hgcb t
    simpa [gc, max_eq_left ht] using this
  have hc0 : cinf = 0 := by
    have hnn : 0 ≤ cinf := le_ciInf fun t => (hc _ (le_max_right _ _)).le
    by_contra hne
    have hpos : 0 < cinf := lt_of_le_of_ne hnn (Ne.symm hne)
    apply hntvc
    have hup : Tendsto (fun T => Real.exp (-ρ * T) * (deriv U cinf * k 0)) atTop (𝓝 0) := by
      simpa using (mangasarian_exp_neg_tendsto P.d_pos).mul_const (deriv U cinf * k 0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (P.U_prime_pos _ (hc T hT)).le)
        (hk T hT).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact mul_le_mul (hU.antitoneOn hpos (hc T hT) (hcinf T hT))
        (hkanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT) (hk T hT).le
        (P.U_prime_pos _ hpos).le
  rw [hc0] at hct
  set gk : ℝ → ℝ := fun t => k (max t 0)
  have hgka : Antitone gk := fun a b hab =>
    hkanti (Set.mem_Ici.mpr (le_max_right _ _)) (Set.mem_Ici.mpr (le_max_right _ _))
      (max_le_max hab le_rfl)
  have hgkb : BddBelow (Set.range gk) :=
    ⟨kss, by rintro _ ⟨t, rfl⟩; exact (hkge _ (le_max_right _ _)).le⟩
  set ku := ⨅ t, gk t
  have hkt : Tendsto k atTop (𝓝 ku) := by
    refine (tendsto_atTop_ciInf hgka hgkb).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [gk, max_eq_left ht]
  have hkuge : kss ≤ ku := le_ciInf fun t => (hkge _ (le_max_right _ _)).le
  have hku0 : 0 < ku := hkss.trans_le hkuge
  have hFc : ContinuousAt (fun x => f x - δ * x) ku :=
    (P.f_diff ku hku0).continuousAt.sub (continuousAt_const.mul continuousAt_id)
  have hDt : Tendsto (fun t => f (k t) - δ * k t - c t) atTop (𝓝 (f ku - δ * ku - 0)) :=
    (hFc.tendsto.comp hkt).sub hct
  have hroot : f ku = δ * ku := by
    have := ramseyPhase_deriv_limit (t₀ := 0) (fun t ht => hkd t ht) hkt hDt
    linarith
  have hku : kss < ku := by
    rcases hkuge.lt_or_eq with h | h
    · exact h
    · have hcs : 0 < f kss - δ * kss := cassSteadyConsumption_pos P
      rw [h] at hcs; linarith
  exact ⟨hct, ku, hku, hroot, hkt⟩

/-- AKMM, p. 255, Figure 9.2, and Appendix 9.A.4, pp. 847–848: **a smaller `c(0)`.** Let
`k(0) = k₀ > 0` be a stock from which the saddle path is constructed (the Cass optimum invests
strictly: every `k₀ ≤ k**`, `ramseyPhase_interior_of_le`, and every `k₀ ∈ (k**, k̂]`,
`ramseyPhase_interior_above`), and let `(k, c, μ)` solve the first-order system with `c(0)` below
the saddle path. Then

* at every `t > 0` it has more capital and less consumption than the saddle path (so `k > 0`);
* after some finite date `t̄` it is in the region `f'(k) < δ` (above the golden rule) and to the
  right of `k**` for good, indeed above `x̂ + η` with `f'(x̂) < δ`, `η > 0`;
* `c(t) → 0` and `k(t) → k^u`, the positive root of `f(k) = δk` (unique by
  `ramseyPhase_root_unique`), with `f'(k^u) < δ`;
* the TVC (9.34)/(9.A.5) fails.

From `k₀ ≤ k**` the path leaves `k ≤ k**` (otherwise the TVC would hold and `ramseyPhase_unique`
would put `c(0)` on the saddle path) with `k̇ > 0` and keeps rising (`ramseyPhase_rising`); from
`k₀ > k**` it either gains `k̇ > 0` (`ramseyPhase_rising`) or falls for ever
(`ramseyPhase_falling`); the end is `ramseyPhase_tail`. -/
theorem ramseyPhase_below_saddle (P : CassPrimitives f U ρ δ) {k₀ : ℝ} (hk₀ : 0 < k₀)
    (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (h0 : k 0 = k₀) (hbelow : c 0 < policy P k₀) :
    (∀ t, 0 < t → (optimalPath P hk₀).capital t < k t ∧
      c t < (optimalPath P hk₀).consumption t) ∧
    (∀ t, 0 ≤ t → 0 < k t) ∧
    (∃ tbar, 0 ≤ tbar ∧ (∀ t, tbar ≤ t → deriv f (k t) < δ ∧ cassSteady P < k t) ∧
      ∃ xh η, 0 < xh ∧ 0 < η ∧ deriv f xh < δ ∧ ∀ t, tbar ≤ t → xh + η ≤ k t) ∧
    Tendsto c atTop (𝓝 0) ∧
    (∃ ku, cassSteady P < ku ∧ f ku = δ * ku ∧ deriv f ku < δ ∧ Tendsto k atTop (𝓝 ku)) ∧
    ¬ Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0) := by
  obtain ⟨μs, hss, hs0, hsc0, hspos, hsle, hsgt, -, -⟩ := ramseyPhase_saddle P hk₀ hint
  obtain ⟨hkss, -⟩ := cassSteady_spec P
  set kss := cassSteady P with hkssdef
  have hcmp := ramseyPhase_comparison P hsol hss hspos (h0.trans hs0.symm) (hsc0 ▸ hbelow)
  have hk : ∀ t, 0 ≤ t → 0 < k t := fun t ht => by
    rcases ht.lt_or_eq with htp | rfl
    · exact (hspos t ht).trans (hcmp t htp).1
    · rw [h0]; exact hk₀
  have hkc : ContinuousOn k (Set.Ici 0) := fun t ht =>
    (hsol.2.2.1 t ht).continuousAt.continuousWithinAt
  have hntvc : ¬ Tendsto (fun T => Real.exp (-ρ * T) * deriv U (c T) * k T) atTop (𝓝 0) :=
    fun htvc => by
      have := ramseyPhase_unique P hk₀ hint hsol hk h0 htvc
      linarith
  have hfate : Tendsto c atTop (𝓝 0) ∧ ∃ ku, kss < ku ∧ f ku = δ * ku ∧
      Tendsto k atTop (𝓝 ku) ∧ ∃ t₁, 0 ≤ t₁ ∧ ∀ t, t₁ ≤ t → kss < k t := by
    by_cases hle : k₀ ≤ kss
    · have hleave : ∃ t₁, 0 ≤ t₁ ∧ kss < k t₁ := by
        by_contra h
        push Not at h
        exact hntvc (ramseyPhase_tvc_of_le_steady P hsol hk h)
      obtain ⟨t₁, ht₁, hkt₁⟩ := hleave
      obtain ⟨t₀, ht₀mem, hkt₀⟩ := intermediate_value_Icc ht₁ (hkc.mono Set.Icc_subset_Ici_self)
        ⟨show k 0 ≤ kss by rw [h0]; exact hle, hkt₁.le⟩
      have ht₀ : 0 ≤ t₀ := ht₀mem.1
      have hsb := hsle hle
      have hDt₀ : 0 < f (k t₀) - δ * k t₀ - c t₀ := by
        have hlt : c t₀ < (optimalPath P hk₀).consumption t₀ := by
          rcases ht₀.lt_or_eq with htp | heq
          · exact (hcmp t₀ htp).2
          · rw [← heq, hsc0]; exact hbelow
        have h1 := (hsb t₀ ht₀).2
        have h2 := ramseyPhase_net_mono P ⟨hspos t₀ ht₀, (hsb t₀ ht₀).1⟩ ⟨hkss, le_rfl⟩
          (hsb t₀ ht₀).1
        simp only at h2
        rw [hkt₀]
        linarith
      obtain ⟨hgt, hc0, ku, hku, hroot, hkt⟩ :=
        ramseyPhase_rising P hsol hk ht₀ hkt₀.ge hDt₀
      exact ⟨hc0, ku, hku, hroot, hkt, t₀ + 1, by linarith, fun t ht => hgt t (by linarith)⟩
    · rw [not_le] at hle
      have hgt : ∀ t, 0 < t → kss < k t := fun t ht =>
        (hsgt hle t ht.le).trans (hcmp t ht).1
      by_cases hex : ∃ t₀, 0 < t₀ ∧ 0 < f (k t₀) - δ * k t₀ - c t₀
      · obtain ⟨t₀, ht₀, hDt₀⟩ := hex
        obtain ⟨hgt', hc0, ku, hku, hroot, hkt⟩ :=
          ramseyPhase_rising P hsol hk ht₀.le (hgt t₀ ht₀).le hDt₀
        exact ⟨hc0, ku, hku, hroot, hkt, t₀ + 1, by linarith, fun t ht => hgt' t (by linarith)⟩
      · push Not at hex
        obtain ⟨hc0, ku, hku, hroot, hkt⟩ := ramseyPhase_falling P hsol hk hgt hex hntvc
        exact ⟨hc0, ku, hku, hroot, hkt, 1, zero_le_one, fun t ht => hgt t (by linarith)⟩
  obtain ⟨hc0, ku, hku, hroot, hkt, t₁, ht₁, hgt₁⟩ := hfate
  obtain ⟨hfku, hreg, -⟩ := ramseyPhase_tail P hsol hku hroot hkt ht₁ hgt₁
  exact ⟨hcmp, hk, hreg, hc0, ⟨ku, hku, hroot, hfku, hkt⟩, hntvc⟩

/-- AKMM, Appendix 9.A.4, pp. 847–848, **now unconditional** (from every `k(0)` where the saddle
path is constructed): below the saddle path, after a
finite date `t̄` capital is in the region `f'(k(t)) − δ < 0` at every `t ≥ t̄`, and it stays above
`k** > 0`, so `appendix_9A4_below_saddle_violates_tvc` applies with
`r(t) = f'(k(t)) − δ` (extended continuously to `t < 0`) and (9.A.6) fails. -/
theorem appendix_9A4_below_saddle_enters_region (P : CassPrimitives f U ρ δ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (h0 : k 0 = k₀) (hbelow : c 0 < policy P k₀) :
    ∃ tbar, 0 ≤ tbar ∧ (∀ t, tbar ≤ t → deriv f (k (max t 0)) - δ < 0) ∧
      (∀ t, tbar ≤ t → cassSteady P ≤ k t) ∧
      ¬ Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, (deriv f (k (max s 0)) - δ)) * k T)
        atTop (𝓝 0) := by
  obtain ⟨-, hk, ⟨tbar, htbar0, hreg, -⟩, -⟩ :=
    ramseyPhase_below_saddle P hk₀ hint hsol h0 hbelow
  have hkc : ContinuousOn k (Set.Ici 0) := fun t ht =>
    (hsol.2.2.1 t ht).continuousAt.continuousWithinAt
  have hr : Continuous fun s => deriv f (k (max s 0)) - δ := by
    have hm : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
    have h1 : Continuous fun s => k (max s 0) :=
      hkc.comp_continuous hm fun s => Set.mem_Ici.mpr (le_max_right s 0)
    exact (P.f_prime_cont.comp_continuous h1 fun s => hk _ (le_max_right s 0)).sub
      continuous_const
  have hneg : ∀ t, tbar ≤ t → deriv f (k (max t 0)) - δ < 0 := fun t ht => by
    rw [max_eq_left (htbar0.trans ht)]
    linarith [(hreg t ht).1]
  refine ⟨tbar, htbar0, hneg, fun t ht => (hreg t ht).2.le, ?_⟩
  exact (appendix_9A4_below_saddle_violates_tvc (tbar := tbar) hr (fun t ht => (hneg t ht).le)
    (cassSteady_spec P).1 fun t ht => (hreg t ht).2.le).2

/-- AKMM, p. 255: **over-accumulation "is a waste"**, made precise as dominance from time `0`.
Below the saddle path (from every `k(0)` where the saddle path is constructed), consumption is
lower than on the saddle path at every date `t > 0` (and tends to `0`, below the steady-state
consumption `f(k**) − δk** > 0`), and the allocation is dominated: there is a path `(k', c')`
from the same `k(0)`, feasible in the sense of the book's problem (9.33) as used throughout the
project (`k' > 0`, `c' > 0` continuous, `k̇' = f(k') − δk' − c'` at every `t ≥ 0`), with
`c' ≥ c` at every date and `c' > c` at every date after some `t₂`. It follows the original path
up to `t₂` and then consumes part of the capital above the golden rule:
`k' = k − η·s(t − t₂)` with `s` Mathlib's smooth transition function (`0` on `(−∞, 0]`,
increasing), so `k'` is differentiable at `t₂` too and no splice condition is needed. -/
theorem ramseyPhase_below_saddle_waste (P : CassPrimitives f U ρ δ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hint : ∀ t, 0 ≤ t → 0 < (optimalPath P hk₀).investment t) {k c μ : ℝ → ℝ}
    (hsol : ramseyPhaseSolution f U ρ δ k c μ) (h0 : k 0 = k₀) (hbelow : c 0 < policy P k₀) :
    (∀ t, 0 < t → c t < (optimalPath P hk₀).consumption t) ∧
    (∀ᶠ t in atTop, c t < f (cassSteady P) - δ * cassSteady P) ∧
    ∃ k' c' : ℝ → ℝ, k' 0 = k 0 ∧ ContinuousOn c' (Set.Ici 0) ∧
      (∀ t, 0 ≤ t → 0 < k' t ∧ 0 < c' t ∧ HasDerivAt k' (f (k' t) - δ * k' t - c' t) t ∧
        c t ≤ c' t) ∧
      ∃ t₂, 0 ≤ t₂ ∧ ∀ t, t₂ < t → c t < c' t := by
  obtain ⟨hcmp, hk, ⟨tbar, htbar0, -, xh, η, hxh, hη, hfxh, hxk⟩, hc0, -⟩ :=
    ramseyPhase_below_saddle P hk₀ hint hsol h0 hbelow
  obtain ⟨hc, hcc, hkd, -, -⟩ := hsol
  refine ⟨fun t ht => (hcmp t ht).2,
    hc0.eventually (gt_mem_nhds (cassSteadyConsumption_pos P)), ?_⟩
  set sm := Real.smoothTransition
  have hsmd : Differentiable ℝ sm :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have hsmc : Continuous (deriv sm) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  set φ : ℝ → ℝ := fun t => sm (t - tbar) with hφdef
  set φd : ℝ → ℝ := fun t => deriv sm (t - tbar) with hφddef
  have hφ : ∀ t, HasDerivAt φ (φd t) t := fun t =>
    (hsmd (t - tbar)).hasDerivAt.comp_sub_const t tbar
  have hφd : ∀ t, 0 ≤ φd t := fun t => Real.smoothTransition.monotone.deriv_nonneg
  have hφ0 : ∀ t, t ≤ tbar → φ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hφpos : ∀ t, tbar < t → 0 < φ t := fun t ht =>
    Real.smoothTransition.pos_of_pos (by linarith)
  have hφ1 : ∀ t, φ t ≤ 1 := fun t => Real.smoothTransition.le_one _
  set k' : ℝ → ℝ := fun t => k t - η * φ t with hk'def
  set c' : ℝ → ℝ := fun t => c t + ((f (k' t) - δ * k' t) - (f (k t) - δ * k t)) + η * φd t
    with hc'def
  have hxh0 : 0 < xh := hxh
  have hFanti : StrictAntiOn (fun x => f x - δ * x) (Set.Ici xh) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici xh)
      (fun x hx => ((P.f_diff x (hxh0.trans_le hx)).continuousAt.sub
        (continuousAt_const.mul continuousAt_id)).continuousWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hxh0.trans hx
    have hd : HasDerivAt (fun x => f x - δ * x) _ x :=
      (P.f_diff x hx0).hasDerivAt.sub ((hasDerivAt_id' x).const_mul δ)
    rw [hd.deriv]
    have := (ramseyPhase_fprime_anti P) hxh0 hx0 hx
    linarith
  have hk'eq : ∀ t, t ≤ tbar → k' t = k t := fun t ht => by
    simp only [k', hφ0 t ht, mul_zero, sub_zero]
  have hk'gt : ∀ t, tbar < t → xh ≤ k' t ∧ k' t < k t := fun t ht => by
    have h1 := hxk t ht.le
    have h2 := hφpos t ht
    have h3 := hφ1 t
    simp only [k']
    constructor <;> nlinarith
  have hk'pos : ∀ t, 0 ≤ t → 0 < k' t := fun t ht => by
    rcases le_or_gt t tbar with h | h
    · rw [hk'eq t h]; exact hk t ht
    · exact hxh0.trans_le (hk'gt t h).1
  have hF : ∀ t, 0 ≤ t → (f (k t) - δ * k t) ≤ (f (k' t) - δ * k' t) ∧
      (tbar < t → (f (k t) - δ * k t) < (f (k' t) - δ * k' t)) := fun t ht => by
    rcases le_or_gt t tbar with h | h
    · rw [hk'eq t h]
      exact ⟨le_rfl, fun h' => absurd h' (not_lt.mpr h)⟩
    · have hlt := hFanti (Set.mem_Ici.mpr (hk'gt t h).1)
        (Set.mem_Ici.mpr ((hk'gt t h).1.trans (hk'gt t h).2.le)) (hk'gt t h).2
      exact ⟨hlt.le, fun _ => hlt⟩
  have hcle : ∀ t, 0 ≤ t → c t ≤ c' t := fun t ht => by
    have := (hF t ht).1
    have := mul_nonneg hη.le (hφd t)
    simp only [c']
    linarith
  have hfc : ContinuousOn f (Set.Ioi 0) := fun x hx =>
    (P.f_diff x hx).continuousAt.continuousWithinAt
  have hkc : ContinuousOn k (Set.Ici 0) := fun t ht =>
    (hkd t ht).continuousAt.continuousWithinAt
  have hφc : Continuous φ := Real.smoothTransition.continuous.comp (continuous_sub_right tbar)
  have hφdc : Continuous φd := hsmc.comp (continuous_sub_right tbar)
  have hk'c : ContinuousOn k' (Set.Ici 0) := hkc.sub (continuousOn_const.mul hφc.continuousOn)
  refine ⟨k', c', by simp only [k']; rw [hφ0 0 htbar0, mul_zero, sub_zero], ?_,
    fun t ht => ⟨hk'pos t ht, (hc t ht).trans_le (hcle t ht), ?_, hcle t ht⟩, tbar, htbar0,
    fun t ht => ?_⟩
  · exact ((hcc.add (((hfc.comp hk'c fun t ht => hk'pos t ht).sub
      (continuousOn_const.mul hk'c)).sub
      ((hfc.comp hkc fun t ht => hk t ht).sub (continuousOn_const.mul hkc)))).add
      (continuousOn_const.mul hφdc.continuousOn))
  · have h := (hkd t ht).sub ((hφ t).const_mul η)
    convert h using 1
    simp only [c', k']
    ring
  · have ht0 : 0 ≤ t := htbar0.trans ht.le
    have := (hF t ht0).2 ht
    have := mul_nonneg hη.le (hφd t)
    simp only [c']
    linarith

/-- CRRA marginal utility: `u'(c) = c^{−σ}` for `c > 0`, `σ ≠ 1`. -/
theorem ramseyPhase_crra_deriv {σ x : ℝ} (hσ1 : σ ≠ 1) (hx : 0 < x) :
    deriv (crraUtility σ) x = x ^ (-σ) := by
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : crraUtility σ = fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [crraUtility]; ring
  rw [hu, (ramseySaddle_power_hasDerivAt _ _ _ hx).deriv]
  field_simp
  ring_nf

/-- AKMM, (9.33) and (9.35), p. 254: with CRRA utility, a path with `c > 0`, the resource
constraint and the Euler equation `ċ/c = (f'(k) − (δ + ρ))/σ` solves the first-order system, with
costate `μ = e^{−ρt}c^{−σ}`. -/
theorem ramseyPhase_solution_of_eq_9_35 {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) {k c : ℝ → ℝ}
    (hc : ∀ t, 0 ≤ t → 0 < c t)
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (f (k t) - δ * k t - c t) t)
    (hcd : ∀ t, 0 ≤ t → HasDerivAt c (c t * (deriv f (k t) - (δ + ρ)) / σ) t) :
    ramseyPhaseSolution f (crraUtility σ) ρ δ k c
      (fun t => Real.exp (-ρ * t) * c t ^ (-σ)) := by
  refine ⟨hc, fun t ht => (hcd t ht).continuousAt.continuousWithinAt, hkd,
    fun t ht => by rw [ramseyPhase_crra_deriv hσ1 (hc t ht)], fun t ht => ?_⟩
  have hct := hc t ht
  have h' := (((hasDerivAt_id' t).const_mul (-ρ)).exp).mul
    ((Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hct.ne')).comp t (hcd t ht))
  have h : HasDerivAt (fun t => Real.exp (-ρ * t) * c t ^ (-σ)) _ t := h'
  convert h using 1
  rw [Real.rpow_sub_one hct.ne']
  simp only [Function.comp_apply]
  field_simp
  ring

/-- AKMM, p. 255, **for the book's model** (Cobb–Douglas `f(k) = k^α`, CRRA utility, (9.33),
(9.35)): from `0 < k(0) ≤ k**`, a path starting above the saddle path cannot keep `k > 0` for
ever (`ramseyPhase_above_saddle_not_global`). -/
theorem ramseyPhase_above_saddle_crra_cobbDouglas {α σ ρ δ k₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hk₀ : 0 < k₀)
    (hle : k₀ ≤ cassSteady (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ)) {k c : ℝ → ℝ}
    (hk : ∀ t, 0 ≤ t → 0 < k t) (hc : ∀ t, 0 ≤ t → 0 < c t)
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (k t ^ α - δ * k t - c t) t)
    (hcd : ∀ t, 0 ≤ t → HasDerivAt c (c t * (α * k t ^ (α - 1) - (δ + ρ)) / σ) t)
    (h0 : k 0 = k₀) (habove : policy (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ) k₀ < c 0) :
    False := by
  have hF : ∀ t, 0 ≤ t → deriv (fun x : ℝ => x ^ α) (k t) = α * k t ^ (α - 1) := fun t ht =>
    (Real.hasDerivAt_rpow_const (Or.inl (hk t ht).ne')).deriv
  exact ramseyPhase_above_saddle_not_global _ hk₀ (ramseyPhase_interior_of_le _ hk₀ hle)
    (ramseyPhase_solution_of_eq_9_35 hσ hσ1 hc hkd fun t ht => by rw [hF t ht]; exact hcd t ht)
    hk h0 habove

/-- AKMM, p. 255 and Appendix 9.A.4, **for the book's model** (Cobb–Douglas `f(k) = k^α`, CRRA
utility, (9.33), (9.35)): from `0 < k(0) ≤ k**`, a path starting below the saddle path has
`c → 0`, enters `αk^{α−1} < δ` for good after a finite date, and violates the TVC
`lim e^{−ρT}c(T)^{−σ}k(T) = 0` (`ramseyPhase_below_saddle`). -/
theorem ramseyPhase_below_saddle_crra_cobbDouglas {α σ ρ δ k₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hk₀ : 0 < k₀)
    (hle : k₀ ≤ cassSteady (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ)) {k c : ℝ → ℝ}
    (hk : ∀ t, 0 ≤ t → 0 < k t) (hc : ∀ t, 0 ≤ t → 0 < c t)
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (k t ^ α - δ * k t - c t) t)
    (hcd : ∀ t, 0 ≤ t → HasDerivAt c (c t * (α * k t ^ (α - 1) - (δ + ρ)) / σ) t)
    (h0 : k 0 = k₀) (hbelow : c 0 < policy (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ) k₀) :
    Tendsto c atTop (𝓝 0) ∧ (∃ tbar, ∀ t, tbar ≤ t → α * k t ^ (α - 1) < δ) ∧
      ¬ Tendsto (fun T => Real.exp (-ρ * T) * c T ^ (-σ) * k T) atTop (𝓝 0) := by
  have hF : ∀ t, 0 ≤ t → deriv (fun x : ℝ => x ^ α) (k t) = α * k t ^ (α - 1) := fun t ht =>
    (Real.hasDerivAt_rpow_const (Or.inl (hk t ht).ne')).deriv
  obtain ⟨-, -, ⟨tbar, htbar0, hreg, -⟩, hc0, -, htvc⟩ :=
    ramseyPhase_below_saddle _ hk₀ (ramseyPhase_interior_of_le _ hk₀ hle)
    (ramseyPhase_solution_of_eq_9_35 hσ hσ1 hc hkd fun t ht => by rw [hF t ht]; exact hcd t ht)
    h0 hbelow
  refine ⟨hc0, ⟨tbar, fun t ht => ?_⟩, fun h => htvc (h.congr' ?_)⟩
  · rw [← hF t (htbar0.trans ht)]; exact (hreg t ht).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [ramseyPhase_crra_deriv hσ1 (hc T hT)]

/-- **A path below the saddle path exists** (so the theorems above are not vacuous), in the
book's model with `σ = α`: Cobb–Douglas `f(k) = k^α`, CRRA utility with `σ = α`, `ρ, δ > 0`. With
`λ = (δ + ρ)/α − δ > 0` the ratio `x = c/k` solves `ẋ = x(x − λ)`, so
`x(t) = λx₀/(x₀ + (λ − x₀)e^{λt})`, and `z = k^{1−α}` solves the linear equation
`ż = (1 − α)(1 − (δ + x)z)`, solved by an integrating factor. For `0 < x₀ < λ` small enough the
path starts at `k(0) = k**` below the saddle path and satisfies (9.33) and (9.35) at every
`t ≥ 0` with `k, c > 0`. -/
theorem ramseyPhase_below_saddle_exists {α ρ δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hδ : 0 < δ) :
    ∃ k c : ℝ → ℝ, (∀ t, 0 ≤ t → 0 < k t) ∧ (∀ t, 0 ≤ t → 0 < c t) ∧
      (∀ t, 0 ≤ t → HasDerivAt k (k t ^ α - δ * k t - c t) t) ∧
      (∀ t, 0 ≤ t → HasDerivAt c (c t * (α * k t ^ (α - 1) - (δ + ρ)) / α) t) ∧
      k 0 = cassSteady (ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ) ∧
      c 0 < policy (ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ)
        (cassSteady (ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ)) := by
  set P := ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ
  set kss := cassSteady P
  have hkss : 0 < kss := (cassSteady_spec P).1
  have hcss : 0 < kss ^ α - δ * kss := cassSteadyConsumption_pos P
  have hpol : policy P kss = kss ^ α - δ * kss := policy_steady P
  set lam := (δ + ρ) / α - δ with hlamdef
  have hlam : 0 < lam := by
    have : δ + ρ < (δ + ρ) / α := by
      rw [lt_div_iff₀ hα0]; nlinarith
    simp only [lam]; linarith
  set x₀ := min (lam / 2) ((kss ^ α - δ * kss) / kss / 2) with hx₀def
  have hx₀ : 0 < x₀ := lt_min (half_pos hlam) (half_pos (div_pos hcss hkss))
  have hx₀lam : x₀ < lam := (min_le_left _ _).trans_lt (half_lt_self hlam)
  have hx₀c : x₀ * kss < kss ^ α - δ * kss := by
    have h : x₀ < (kss ^ α - δ * kss) / kss :=
      (min_le_right _ _).trans_lt (half_lt_self (div_pos hcss hkss))
    rwa [lt_div_iff₀ hkss] at h
  set Den : ℝ → ℝ := fun t => x₀ + (lam - x₀) * Real.exp (lam * t) with hDendef
  have hDen : ∀ t, 0 < Den t := fun t => by
    simp only [Den]; nlinarith [Real.exp_pos (lam * t)]
  have hDend : ∀ t, HasDerivAt Den ((lam - x₀) * (Real.exp (lam * t) * lam)) t := fun t => by
    have h := ((((hasDerivAt_id' t).const_mul lam).exp).const_mul (lam - x₀)).const_add x₀
    convert h using 1
    ring
  set x : ℝ → ℝ := fun t => lam * x₀ / Den t with hxdef
  have hxpos : ∀ t, 0 < x t := fun t => div_pos (mul_pos hlam hx₀) (hDen t)
  have hxd : ∀ t, HasDerivAt x (x t * (x t - lam)) t := fun t => by
    have h := (hasDerivAt_const t (lam * x₀)).div (hDend t) (hDen t).ne'
    convert h using 1
    have := (hDen t).ne'
    simp only [x, Den] at this ⊢
    field_simp
    ring
  set B : ℝ → ℝ := fun t => lam * t - Real.log (Den t) + Real.log lam with hBdef
  have hBd : ∀ t, HasDerivAt B (x t) t := fun t => by
    have h := (((hasDerivAt_id' t).const_mul lam).sub ((hDend t).log (hDen t).ne')).add_const
      (Real.log lam)
    convert h using 1
    have := (hDen t).ne'
    simp only [x, Den] at this ⊢
    field_simp
    ring
  set A : ℝ → ℝ := fun t => (1 - α) * (δ * t + B t) with hAdef
  have hAd : ∀ t, HasDerivAt A ((1 - α) * (δ + x t)) t := fun t => by
    have h := (((hasDerivAt_id' t).const_mul δ).add (hBd t)).const_mul (1 - α)
    convert h using 1
    ring
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun t => (hAd t).continuousAt
  have hEc : Continuous fun s => Real.exp (A s) := Real.continuous_exp.comp hAc
  set I : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, Real.exp (A s) with hIdef
  have hId : ∀ t, HasDerivAt I (Real.exp (A t)) t := fun t =>
    (hEc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hI : ∀ t, 0 ≤ t → 0 ≤ I t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s _ => (Real.exp_pos _).le
  set z₀ := kss ^ (1 - α) with hz₀def
  have hz₀ : 0 < z₀ := Real.rpow_pos_of_pos hkss _
  set z : ℝ → ℝ := fun t => Real.exp (-A t) * (z₀ + (1 - α) * I t) with hzdef
  have hz : ∀ t, 0 ≤ t → 0 < z t := fun t ht =>
    mul_pos (Real.exp_pos _) (by nlinarith [hI t ht])
  have hzd : ∀ t, HasDerivAt z ((1 - α) * (1 - (δ + x t) * z t)) t := fun t => by
    have h' := ((hAd t).neg.exp).mul (((hId t).const_mul (1 - α)).const_add z₀)
    have h : HasDerivAt z _ t := h'
    convert h using 1
    have hE : Real.exp (-A t) * Real.exp (A t) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [z]
    linear_combination (α - 1) * hE
  set q := (1 - α)⁻¹ with hqdef
  have h1α : 0 < 1 - α := by linarith
  have hq1 : q * (1 - α) = 1 := inv_mul_cancel₀ h1α.ne'
  have hqm : q - 1 = q * α := by
    simp only [q]; field_simp; ring
  set k : ℝ → ℝ := fun t => z t ^ q with hkdef
  set c : ℝ → ℝ := fun t => x t * k t with hcdef
  have hk : ∀ t, 0 ≤ t → 0 < k t := fun t ht => Real.rpow_pos_of_pos (hz t ht) _
  have hkd : ∀ t, 0 ≤ t → HasDerivAt k (k t ^ α - δ * k t - c t) t := fun t ht => by
    have hzt := hz t ht
    have h' := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hzt.ne')).comp t (hzd t)
    have h : HasDerivAt k _ t := h'
    convert h using 1
    have hzα : (z t ^ q) ^ α = z t ^ (q - 1) := by rw [← Real.rpow_mul hzt.le, hqm]
    have hzs : z t ^ (q - 1) * z t = z t ^ q := by
      rw [Real.rpow_sub_one hzt.ne']; field_simp
    simp only [c, k]
    rw [hzα, ← hzs]
    have e : q * z t ^ (q - 1) * ((1 - α) * (1 - (δ + x t) * z t)) =
        (q * (1 - α)) * (z t ^ (q - 1) - (δ + x t) * (z t ^ (q - 1) * z t)) := by ring
    rw [e, hq1]
    ring
  have hcd : ∀ t, 0 ≤ t → HasDerivAt c (c t * (α * k t ^ (α - 1) - (δ + ρ)) / α) t :=
    fun t ht => by
    have hkt := hk t ht
    have h := (hxd t).mul (hkd t ht)
    convert h using 1
    simp only [c]
    rw [Real.rpow_sub_one hkt.ne']
    simp only [lam]
    field_simp
    ring
  have hA0 : A 0 = 0 := by
    simp only [A, B, Den, mul_zero, Real.exp_zero, mul_one, add_sub_cancel, zero_add,
      sub_add_cancel]
  have hk0 : k 0 = kss := by
    simp only [k, z, I, hA0, neg_zero, Real.exp_zero, one_mul, intervalIntegral.integral_same,
      mul_zero, add_zero, z₀, q]
    exact Real.rpow_rpow_inv hkss.le h1α.ne'
  have hx0 : x 0 = x₀ := by
    simp only [x, Den, mul_zero, Real.exp_zero, mul_one, add_sub_cancel]
    field_simp
  refine ⟨k, c, hk, fun t ht => mul_pos (hxpos t) (hk t ht), hkd, hcd, hk0, ?_⟩
  simp only [c, hk0, hx0, hpol]
  exact hx₀c

/-- AKMM, p. 255 and Appendix 9.A.4: the conclusions of `ramseyPhase_below_saddle_crra_cobbDouglas`
hold for an actual path of the book's model (`σ = α`, `ramseyPhase_below_saddle_exists`): its
consumption tends to `0`, it enters `αk^{α−1} < δ` for good, and it violates the TVC. -/
theorem ramseyPhase_below_saddle_instance {α ρ δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hδ : 0 < δ) :
    ∃ k c : ℝ → ℝ, k 0 = cassSteady (ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ) ∧
      c 0 < policy (ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ)
        (cassSteady (ramseySaddle_primitives hα0 hα1 hα0 hα1.ne hρ hδ)) ∧
      Tendsto c atTop (𝓝 0) ∧ (∃ tbar, ∀ t, tbar ≤ t → α * k t ^ (α - 1) < δ) ∧
      ¬ Tendsto (fun T => Real.exp (-ρ * T) * c T ^ (-α) * k T) atTop (𝓝 0) := by
  obtain ⟨k, c, hk, hc, hkd, hcd, hk0, hc0⟩ := ramseyPhase_below_saddle_exists hα0 hα1 hρ hδ
  exact ⟨k, c, hk0, hc0, ramseyPhase_below_saddle_crra_cobbDouglas hα0 hα1 hα0 hα1.ne hρ hδ
    (cassSteady_spec _).1 le_rfl hk hc hkd hcd hk0 hc0⟩

end AKMM.ContinuousTime
