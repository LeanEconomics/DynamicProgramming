/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.IHDetPrinciple
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exercise 7.4: restricting the state space of the Ramsey model

Miao, §7.6, Exercise 4, pp. 228–229. The deterministic Ramsey model
`max Σ βᵗ u(C_t)` subject to `C_t + K_{t+1} = f(K_t)`, `K₀` given, with `f` continuous and
strictly increasing, `f(0) = 0`, `x ≤ f(x) ≤ x_m` on `[0, x_m]` and `f(x) < x` for `x > x_m`
(`ex7_RamseyHyp`). With `C_t ≥ 0` and `K_{t+1} ≥ 0` the problem is the deterministic problem of
`IHDet` with `Γ(K) = [0, f(K)]` (`ex7_ramseyΓ`) and `F(K, K′) = u(f(K) − K′)` (`ex7_ramseyF`).

* `ex7_f_nonneg`, `ex7_f_le_max`: `0 ≤ f(K) ≤ max(K, x_m)` for `K ≥ 0`.
* `ex_7_4_invariant`: for every `b ≥ x_m`, `[0, b]` is invariant: `K ∈ [0, b]` and
  `K′ ∈ Γ(K)` give `K′ ∈ [0, b]`; `ex_7_4_path`: every feasible path from `K₀ ∈ [0, b]` stays in
  `[0, b]`, with consumption `C_t ∈ [0, b]`.
* `ex7_vstar_restrict`: if `Y` is invariant under `Γ` then the problem from `x₀ ∈ Y` and the
  problem on the state space `Y` (feasibility `Γ` and reward `F` restricted to `Y`) have the same
  value `v*`; `ex_7_4_restrict`: this is what "one can restrict the state space to `X`" means.
* `ex_7_4_bounded`: with `u` continuous on `[0, b]`, the reward is bounded on the graph of `Γ`
  over `X = [0, b]`.
* `ex_7_4`: the exercise. From `K₀ ∈ [0, x_m]`, the state space can be restricted to
  `X = [0, x_m]` and the reward is bounded there.
* `ex_7_4_eventually`: from any `K₀ ≥ 0`, `limsup K_t ≤ x_m` along every feasible path.

**Correction.** From `K₀ > x_m` the paths need not enter `[0, x_m]` (`ex_7_4_not_enter`: with
`f(x) = min(x, (1 + x)/2)`, `x_m = 1`, the feasible path `K_t = 1 + 2^{−t}` from `K₀ = 2` stays
above `1`), so `[0, x_m]` is not a valid state space for such `K₀`; the interval
`[0, max(K₀, x_m)]` is (`ex_7_4_large`), and the paths approach `[0, x_m]` (`ex_7_4_eventually`,
which is where continuity of `f` is used).
-/

namespace Miao.InfiniteHorizonDP

open Filter Topology

/-- The hypotheses of Exercise 7.4 (Miao, p. 229) on the production function `f` and `x_m ≥ 0`. -/
structure ex7_RamseyHyp (f : ℝ → ℝ) (xm : ℝ) : Prop where
  cont : ContinuousOn f (Set.Ici 0)
  mono : StrictMonoOn f (Set.Ici 0)
  zero : f 0 = 0
  xm_nonneg : 0 ≤ xm
  low : ∀ x ∈ Set.Icc 0 xm, x ≤ f x ∧ f x ≤ xm
  above : ∀ x, xm < x → f x < x

/-- The feasibility correspondence of the Ramsey model: `Γ(K) = {K′ : 0 ≤ K′ ≤ f(K)}`
(`C = f(K) − K′ ≥ 0`). -/
def ex7_ramseyΓ (f : ℝ → ℝ) (K : ℝ) : Set ℝ := {K' | 0 ≤ K' ∧ K' ≤ f K}

/-- The reward of the Ramsey model: `F(K, K′) = u(f(K) − K′)`. -/
def ex7_ramseyF (f u : ℝ → ℝ) (K K' : ℝ) : ℝ := u (f K - K')

variable {f : ℝ → ℝ} {xm : ℝ}

/-- `f(K) ≥ 0` for `K ≥ 0`. -/
theorem ex7_f_nonneg (h : ex7_RamseyHyp f xm) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ f K := by
  rcases hK.eq_or_lt with h0 | h0
  · rw [← h0, h.zero]
  · rw [← h.zero]
    exact (h.mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hK) h0).le

/-- `f(K) ≤ max(K, x_m)` for `K ≥ 0`. -/
theorem ex7_f_le_max (h : ex7_RamseyHyp f xm) {K : ℝ} (hK : 0 ≤ K) : f K ≤ max K xm := by
  rcases le_or_gt K xm with hk | hk
  · exact (h.low K ⟨hK, hk⟩).2.trans (le_max_right _ _)
  · exact (h.above K hk).le.trans (le_max_left _ _)

/-- **Exercise 7.4, invariance** (Miao, p. 229): for every `b ≥ x_m`, `K ∈ [0, b]` and
`K′ ∈ Γ(K)` give `K′ ∈ [0, b]`. -/
theorem ex_7_4_invariant (h : ex7_RamseyHyp f xm) {b : ℝ} (hb : xm ≤ b) {K K' : ℝ}
    (hK : K ∈ Set.Icc 0 b) (hK' : K' ∈ ex7_ramseyΓ f K) : K' ∈ Set.Icc 0 b :=
  ⟨hK'.1, hK'.2.trans ((ex7_f_le_max h hK.1).trans (max_le hK.2 hb))⟩

/-- **Exercise 7.4, feasible paths** (Miao, p. 229): every feasible path from `K₀ ∈ [0, b]`,
`b ≥ x_m`, stays in `[0, b]`, and consumption `C_t = f(K_t) − K_{t+1}` lies in `[0, b]`. -/
theorem ex_7_4_path (h : ex7_RamseyHyp f xm) {b : ℝ} (hb : xm ≤ b) {K₀ : ℝ}
    (hK₀ : K₀ ∈ Set.Icc 0 b) {p : ℕ → ℝ} (hp : p ∈ IHDet.Feasible (ex7_ramseyΓ f) K₀) (t : ℕ) :
    p t ∈ Set.Icc 0 b ∧ f (p t) - p (t + 1) ∈ Set.Icc 0 b := by
  have hin : ∀ t, p t ∈ Set.Icc 0 b := by
    intro t
    induction t with
    | zero => rw [hp.1]; exact hK₀
    | succ t ih => exact ex_7_4_invariant h hb ih (hp.2 t)
  refine ⟨hin t, ?_, ?_⟩
  · linarith [(hp.2 t).2]
  · have := ex7_f_le_max h (hin t).1
    have := (hp.2 t).1
    have := max_le (hin t).2 hb
    linarith

/-- Restricting a deterministic problem to an invariant set `Y` does not change its value: if
`Γ(x) ⊆ Y` for `x ∈ Y`, then for `x₀ ∈ Y` the value `v*(x₀)` of the problem `(Γ, F)` equals the
value of the problem on the state space `Y` with `Γ_Y(x) = Γ(x)` and `F_Y = F` on `Y × Y`. -/
theorem ex7_vstar_restrict {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} {Y : Set X}
    (hY : ∀ x ∈ Y, ∀ y ∈ Γ x, y ∈ Y) {x₀ : X} (hx₀ : x₀ ∈ Y) :
    IHDet.vstar Γ F β x₀ =
      IHDet.vstar (fun x : Y => {y : Y | (y : X) ∈ Γ x}) (fun x y : Y => F x y) β ⟨x₀, hx₀⟩ := by
  apply le_antisymm
  · refine iSup₂_le fun p hp => ?_
    have hin : ∀ t, p t ∈ Y := by
      intro t
      induction t with
      | zero => rw [hp.1]; exact hx₀
      | succ t ih => exact hY _ ih _ (hp.2 t)
    let q : ℕ → Y := fun t => ⟨p t, hin t⟩
    have hq : q ∈ IHDet.Feasible (fun x : Y => {y : Y | (y : X) ∈ Γ x}) ⟨x₀, hx₀⟩ :=
      ⟨Subtype.ext hp.1, fun t => hp.2 t⟩
    exact le_iSup₂_of_le (f := fun q (_ : q ∈ IHDet.Feasible
      (fun x : Y => {y : Y | (y : X) ∈ Γ x}) ⟨x₀, hx₀⟩) => IHDet.total (fun x y : Y => F x y) β q)
      q hq le_rfl
  · refine iSup₂_le fun q hq => ?_
    have hp : (fun t => (q t : X)) ∈ IHDet.Feasible Γ x₀ :=
      ⟨congrArg Subtype.val hq.1, fun t => hq.2 t⟩
    exact le_iSup₂_of_le (f := fun p (_ : p ∈ IHDet.Feasible Γ x₀) => IHDet.total F β p)
      _ hp le_rfl

/-- **Exercise 7.4, restriction** (Miao, p. 229): for `b ≥ x_m` and `K₀ ∈ [0, b]`, the value of
the Ramsey problem from `K₀` equals the value of the problem on the state space `X = [0, b]`. -/
theorem ex_7_4_restrict (h : ex7_RamseyHyp f xm) (u : ℝ → ℝ) (β : ℝ) {b : ℝ} (hb : xm ≤ b)
    {K₀ : ℝ} (hK₀ : K₀ ∈ Set.Icc 0 b) :
    IHDet.vstar (ex7_ramseyΓ f) (ex7_ramseyF f u) β K₀ =
      IHDet.vstar (fun K : Set.Icc 0 b => {K' : Set.Icc 0 b | (K' : ℝ) ∈ ex7_ramseyΓ f K})
        (fun K K' : Set.Icc 0 b => ex7_ramseyF f u K K') β ⟨K₀, hK₀⟩ :=
  ex7_vstar_restrict (fun _ hK _ hK' => ex_7_4_invariant h hb hK hK') hK₀

/-- **Exercise 7.4, bounded reward** (Miao, p. 229): if `u` is continuous on `[0, b]`, `b ≥ x_m`,
then `F(K, K′) = u(f(K) − K′)` is bounded on `{(K, K′) : K ∈ [0, b], K′ ∈ Γ(K)}`. -/
theorem ex_7_4_bounded (h : ex7_RamseyHyp f xm) {u : ℝ → ℝ} {b : ℝ} (hb : xm ≤ b)
    (hu : ContinuousOn u (Set.Icc 0 b)) :
    ∃ B, ∀ K ∈ Set.Icc 0 b, ∀ K' ∈ ex7_ramseyΓ f K, |ex7_ramseyF f u K K'| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  refine ⟨B, fun K hK K' hK' => ?_⟩
  have hc : f K - K' ∈ Set.Icc 0 b := by
    refine ⟨by linarith [hK'.2], ?_⟩
    have := ex7_f_le_max h hK.1
    have := max_le hK.2 hb
    linarith [hK'.1]
  have := hB _ hc
  rwa [Real.norm_eq_abs] at this

/-- **Exercise 7.4** (Miao, pp. 228–229). Under the hypotheses on `f` and with `u` continuous on
`[0, x_m]`: from every `K₀ ∈ [0, x_m]` every feasible path stays in `X = [0, x_m]`, the value of
the problem equals the value of the problem with state space `X`, and on `X` the reward is
bounded. -/
theorem ex_7_4 (h : ex7_RamseyHyp f xm) {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc 0 xm))
    (β : ℝ) {K₀ : ℝ} (hK₀ : K₀ ∈ Set.Icc 0 xm) :
    (∀ p ∈ IHDet.Feasible (ex7_ramseyΓ f) K₀, ∀ t, p t ∈ Set.Icc 0 xm) ∧
      IHDet.vstar (ex7_ramseyΓ f) (ex7_ramseyF f u) β K₀ =
        IHDet.vstar (fun K : Set.Icc 0 xm => {K' : Set.Icc 0 xm | (K' : ℝ) ∈ ex7_ramseyΓ f K})
          (fun K K' : Set.Icc 0 xm => ex7_ramseyF f u K K') β ⟨K₀, hK₀⟩ ∧
      ∃ B, ∀ K ∈ Set.Icc 0 xm, ∀ K' ∈ ex7_ramseyΓ f K, |ex7_ramseyF f u K K'| ≤ B :=
  ⟨fun _ hp t => (ex_7_4_path h le_rfl hK₀ hp t).1, ex_7_4_restrict h u β le_rfl hK₀,
    ex_7_4_bounded h le_rfl hu⟩

/-- **Exercise 7.4 for `K₀ > x_m`** (correction): the state space `X = [0, max(K₀, x_m)]` works
for every `K₀ ≥ 0`: the paths stay in `X`, the value is unchanged, and the reward is bounded on
`X` when `u` is continuous on `X`. -/
theorem ex_7_4_large (h : ex7_RamseyHyp f xm) {u : ℝ → ℝ} (β : ℝ) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hu : ContinuousOn u (Set.Icc 0 (max K₀ xm))) :
    (∀ p ∈ IHDet.Feasible (ex7_ramseyΓ f) K₀, ∀ t, p t ∈ Set.Icc 0 (max K₀ xm)) ∧
      IHDet.vstar (ex7_ramseyΓ f) (ex7_ramseyF f u) β K₀ =
        IHDet.vstar (fun K : Set.Icc 0 (max K₀ xm) =>
          {K' : Set.Icc 0 (max K₀ xm) | (K' : ℝ) ∈ ex7_ramseyΓ f K})
          (fun K K' : Set.Icc 0 (max K₀ xm) => ex7_ramseyF f u K K') β
          ⟨K₀, hK₀, le_max_left _ _⟩ ∧
      ∃ B, ∀ K ∈ Set.Icc 0 (max K₀ xm), ∀ K' ∈ ex7_ramseyΓ f K, |ex7_ramseyF f u K K'| ≤ B :=
  ⟨fun _ hp t => (ex_7_4_path h (le_max_right _ _) ⟨hK₀, le_max_left _ _⟩ hp t).1,
    ex_7_4_restrict h u β (le_max_right _ _) ⟨hK₀, le_max_left _ _⟩,
    ex_7_4_bounded h (le_max_right _ _) hu⟩

/-- **Exercise 7.4, paths approach `[0, x_m]`**: from every `K₀ ≥ 0`, along every feasible path,
for every `ε > 0` eventually `K_t ≤ x_m + ε` (`limsup K_t ≤ x_m`). -/
theorem ex_7_4_eventually (h : ex7_RamseyHyp f xm) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) {p : ℕ → ℝ}
    (hp : p ∈ IHDet.Feasible (ex7_ramseyΓ f) K₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, p t ≤ xm + ε := by
  have hpath := fun t => ex_7_4_path h (le_max_right K₀ xm) ⟨hK₀, le_max_left _ _⟩ hp t
  by_cases hN : ∃ N, p N ≤ xm
  · obtain ⟨N, hN⟩ := hN
    have hstay : ∀ k, p (N + k) ≤ xm := by
      intro k
      induction k with
      | zero => exact hN
      | succ k ih =>
        exact (ex_7_4_invariant h le_rfl ⟨(hpath (N + k)).1.1, ih⟩ (hp.2 (N + k))).2
    refine eventually_atTop.2 ⟨N, fun t ht => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    linarith [hstay k]
  · push Not at hN
    have hdec : ∀ t, p (t + 1) < p t := fun t => ((hp.2 t).2).trans_lt (h.above _ (hN t))
    have hanti : Antitone p := antitone_nat_of_succ_le fun t => (hdec t).le
    have hbdd : BddBelow (Set.range p) := ⟨xm, by rintro _ ⟨t, rfl⟩; exact (hN t).le⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    set L := ⨅ t, p t
    have hxL : xm ≤ L := le_ciInf fun t => (hN t).le
    have hL0 : 0 ≤ L := h.xm_nonneg.trans hxL
    have hLx : L ≤ xm := by
      by_contra hc
      push Not at hc
      have hf : Tendsto (fun t => f (p t)) atTop (𝓝 (f L)) :=
        ((h.cont L hL0).tendsto).comp (tendsto_nhdsWithin_iff.2
          ⟨hlim, Eventually.of_forall fun t => (hpath t).1.1⟩)
      have hle : L ≤ f L := le_of_tendsto_of_tendsto
        (hlim.comp (tendsto_add_atTop_nat 1)) hf
        (Eventually.of_forall fun t => (hp.2 t).2)
      linarith [h.above L hc]
    have hlt : L < xm + ε := by linarith
    exact (hlim.eventually (eventually_lt_nhds hlt)).mono fun t ht => ht.le

/-- The production function of the counterexample, `f(x) = min(x, (1 + x)/2)`, satisfies the
hypotheses of Exercise 7.4 with `x_m = 1`. -/
theorem ex7_cex_hyp : ex7_RamseyHyp (fun x => min x ((1 + x) / 2)) 1 where
  cont := (continuous_id.min ((continuous_const.add continuous_id).div_const 2)).continuousOn
  mono := fun a _ b _ hab => min_lt_min hab (by linarith)
  zero := by norm_num
  xm_nonneg := zero_le_one
  low := fun x hx => by
    have : min x ((1 + x) / 2) = x := min_eq_left (by linarith [hx.2])
    rw [this]
    exact ⟨le_rfl, hx.2⟩
  above := fun x hx => by
    have : min x ((1 + x) / 2) = (1 + x) / 2 := min_eq_right (by linarith)
    rw [this]
    linarith

/-- **Exercise 7.4: paths from `K₀ > x_m` need not enter `[0, x_m]`** (counterexample). With
`f(x) = min(x, (1 + x)/2)` and `x_m = 1`, the path `K_t = 1 + 2^{−t}` (zero consumption) is
feasible from `K₀ = 2` and `K_t > 1` for all `t`. -/
theorem ex_7_4_not_enter :
    ex7_RamseyHyp (fun x => min x ((1 + x) / 2)) 1 ∧
      (fun t : ℕ => 1 + (1 / 2 : ℝ) ^ t) ∈
        IHDet.Feasible (ex7_ramseyΓ fun x => min x ((1 + x) / 2)) 2 ∧
      ∀ t : ℕ, 1 < 1 + (1 / 2 : ℝ) ^ t := by
  refine ⟨ex7_cex_hyp, ⟨by norm_num, fun t => ⟨by positivity, ?_⟩⟩, fun t => by
    have : (0 : ℝ) < (1 / 2) ^ t := by positivity
    linarith⟩
  have hp : (0 : ℝ) < (1 / 2) ^ t := by positivity
  have e : min (1 + (1 / 2 : ℝ) ^ t) ((1 + (1 + (1 / 2) ^ t)) / 2) =
      (1 + (1 + (1 / 2) ^ t)) / 2 := min_eq_right (by linarith)
  simp only
  rw [e, pow_succ]
  linarith

end Miao.InfiniteHorizonDP
