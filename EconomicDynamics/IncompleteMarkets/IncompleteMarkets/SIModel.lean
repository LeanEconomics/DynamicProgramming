/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv

/-!
# §8.3.2: the income-fluctuation problem with iid income, in cash on hand

Copied from `EconomicDynamics/Applications` (module `SIModel`), namespace renamed.

Miao, §8.3, pp. 237–240, and §8.3.2, pp. 249–250. The consumer maximises `E Σ βᵗ u(c_t)`
subject to `c_t + a_{t+1} = R a_t + y_t`, `a_{t+1} ≥ −b`; labour income `y_t` is iid with law
`μ` supported in `[y_min, y_max]`. With `r = R − 1`, `â_{t+1} = a_{t+1} + b` and cash on hand
`x_t = R a_t + y_t + b` (p. 239) the constraints become `c_t + â_{t+1} = x_t`, `â_{t+1} ≥ 0` and
`x_{t+1} = R â_{t+1} + y_{t+1} − rb` (`SIModel.next`, `si_cash_on_hand`). Cash on hand never
falls below `x_min = y_min − rb` (`SIModel.next_ge`).

* `SIModel`: the primitives `(β, R, b, y_min, y_max, μ, u, u′)` with the book's standing
  hypotheses: `β ∈ (0, 1)`, `u′ > 0`, `u′` strictly decreasing (`u′′ < 0`) and continuous,
  `u′(0+) = ∞`, `u′(∞) = 0`, and `b < y_min/r`, i.e. `x_min > 0` (p. 239).
* `SIModel.Solution`: what the book assumes on p. 240: a solution `V` of the Bellman equation
  `V(x) = max_{â ∈ [0, x]} u(x − â) + β E V(Râ + y − rb)` (attained at the saving policy `â(x)`)
  which is strictly increasing, strictly concave and continuously differentiable, with the
  envelope condition `V′(x) = u′(c(x))`, `c(x) = x − â(x)`.
* The tools used throughout: `dV_strictAnti` (`V′` is strictly decreasing), the mean value
  bounds `tangent_V`, `SIModel.tangent_u`, integrability of `V` and `V′` along next period's cash on
  hand, the continuation value `W(s) = E V(Rs + y − rb)` and its marginal value
  `D(s) = E V′(Rs + y − rb)` with `R(s′ − s)D(s′) ≤ W(s′) − W(s) ≤ R(s′ − s)D(s)`
  (`W_sub_bounds`), `D` strictly decreasing (`D_strictAnti`) and continuous (`D_continuousOn`).

**Departures.** (1) `u` is real-valued and continuous at `0` (consumption `c = 0` is feasible),
which excludes the logarithm, as in §6.6.2. (2) "`V` is continuously differentiable" is taken
on `[x_min, ∞)` with `V` differentiable (two-sided) at every `x ≥ x_min`; the marginal value
`E V′(y − rb)` at a binding constraint involves `V′(x_min)`. (3) The book's `R > 1` is replaced
by `R > 0` (Lemma 8.3.1 is stated for `R > 0`); none of the results below needs `R > 1`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

/-- The **income-fluctuation problem** of Miao §8.3.2 (pp. 237–240, 249): discount factor `β`,
gross interest rate `R`, borrowing limit `b`, iid income with law `μ` supported in
`[y_min, y_max]`, utility `u` with derivative `du = u′` on `(0, ∞)`. -/
structure SIModel where
  β : ℝ
  R : ℝ
  b : ℝ
  ymin : ℝ
  ymax : ℝ
  μ : ProbabilityMeasure ℝ
  u : ℝ → ℝ
  du : ℝ → ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  R_pos : 0 < R
  b_nonneg : 0 ≤ b
  ymin_le_ymax : ymin ≤ ymax
  supp : ∀ᵐ y ∂(μ : Measure ℝ), y ∈ Set.Icc ymin ymax
  xmin_pos : 0 < ymin - (R - 1) * b
  u_cont : ContinuousOn u (Set.Ici 0)
  hasDerivAt_u : ∀ c, 0 < c → HasDerivAt u (du c) c
  du_pos : ∀ c, 0 < c → 0 < du c
  du_anti : StrictAntiOn du (Set.Ioi 0)
  du_cont : ContinuousOn du (Set.Ioi 0)
  inada_zero : Tendsto du (𝓝[>] 0) atTop
  inada_top : Tendsto du atTop (𝓝 0)

/-- Miao, p. 239: with `x_t = R a_t + y_t + b`, `â_{t+1} = a_{t+1} + b` and `r = R − 1`, the
budget `c_t + a_{t+1} = R a_t + y_t` becomes `c_t + â_{t+1} = x_t` and
`x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`; the borrowing limit `a_{t+1} ≥ −b` is `â_{t+1} ≥ 0`. -/
theorem si_cash_on_hand (R b a a' y y' c : ℝ) (hbud : c + a' = R * a + y) :
    c + (a' + b) = R * a + y + b ∧
      R * a' + y' + b = R * ((R * a + y + b) - c) + y' - (R - 1) * b ∧
      (-b ≤ a' ↔ 0 ≤ a' + b) := by
  refine ⟨by linarith, ?_, ⟨fun h => by linarith, fun h => by linarith⟩⟩
  have : a' = R * a + y - c := by linarith
  subst this
  ring

/-- The mean value bounds for `u` (`u′` decreasing): for `0 ≤ c < c′`,
`u′(c′)(c′ − c) ≤ u(c′) − u(c)`, and if `c > 0` also `u(c′) − u(c) ≤ u′(c)(c′ − c)`. -/
theorem SIModel.tangent_u (M : SIModel) {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') :
    M.du c' * (c' - c) ≤ M.u c' - M.u c ∧ (0 < c → M.u c' - M.u c ≤ M.du c * (c' - c)) := by
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope M.u M.du hcc
    (M.u_cont.mono fun z hz => Set.mem_Ici.2 (hc.trans hz.1))
    (fun z hz => M.hasDerivAt_u z (hc.trans_lt hz.1))
  have hpos : 0 < c' - c := sub_pos.2 hcc
  have heq : M.u c' - M.u c = M.du ξ * (c' - c) := by
    rw [hslope]; field_simp
  have hξ0 : 0 < ξ := hc.trans_lt hξ.1
  refine ⟨?_, fun hc0 => ?_⟩
  · rw [heq]
    exact mul_le_mul_of_nonneg_right
      (M.du_anti.antitoneOn (Set.mem_Ioi.2 hξ0) (Set.mem_Ioi.2 (hξ0.trans hξ.2)) hξ.2.le) hpos.le
  · rw [heq]
    exact mul_le_mul_of_nonneg_right
      (M.du_anti.antitoneOn (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 hξ0) hξ.1.le) hpos.le

/-- A strictly positive integrand has a strictly positive integral under a probability
measure. -/
theorem si_integral_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ y ∂μ, 0 < f y) : 0 < ∫ y, f y ∂μ := by
  have hnn : 0 ≤ᵐ[μ] f := hpos.mono fun y hy => hy.le
  rcases (integral_nonneg_of_ae hnn).lt_or_eq with h | h
  · exact h
  · have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hf).1 h.symm
    obtain ⟨y, hy1, hy2⟩ := (hpos.and h0).exists
    simp only [Pi.zero_apply] at hy2
    linarith

namespace SIModel

variable (M : SIModel)

/-- The law of income as a measure. -/
abbrev law : Measure ℝ := (M.μ : Measure ℝ)

/-- The net interest rate `r = R − 1`. -/
def r : ℝ := M.R - 1

/-- The lowest cash on hand `x_min = y_min − rb` (Miao, p. 249). -/
def xmin : ℝ := M.ymin - M.r * M.b

/-- Next period's cash on hand `x′ = Rs + y − rb` after saving `s = â` and income `y`. -/
def next (s y : ℝ) : ℝ := M.R * s + y - M.r * M.b

theorem xmin_pos' : 0 < M.xmin := M.xmin_pos

theorem next_ge {s y : ℝ} (hs : 0 ≤ s) (hy : M.ymin ≤ y) : M.xmin ≤ M.next s y := by
  have := mul_nonneg M.R_pos.le hs
  simp only [next, xmin]
  linarith

theorem next_sub (s s' y : ℝ) : M.next s' y - M.next s y = M.R * (s' - s) := by
  simp only [next]; ring

theorem continuous_next (y : ℝ) : Continuous fun s => M.next s y := by
  simp only [next]; fun_prop

theorem continuous_next_y (s : ℝ) : Continuous fun y => M.next s y := by
  simp only [next]; fun_prop

/-- Almost surely, `x_min ≤ Rs + y − rb ≤ Rs + y_max − rb`. -/
theorem ae_next {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ y ∂M.law, M.xmin ≤ M.next s y ∧ M.next s y ≤ M.next s M.ymax := by
  filter_upwards [M.supp] with y hy
  exact ⟨M.next_ge hs hy.1, by simp only [next]; linarith [hy.2]⟩

/-- A function continuous on `[x_min, ∞)` is integrable along next period's cash on hand. -/
theorem integrable_comp {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici M.xmin)) {s : ℝ}
    (hs : 0 ≤ s) : Integrable (fun y => f (M.next s y)) M.law := by
  set g : ℝ → ℝ := f ∘ fun z => max z M.xmin
  have hg : Continuous g :=
    hf.comp_continuous (continuous_id.max continuous_const)
      fun z => Set.mem_Ici.2 (le_max_right _ _)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := M.xmin) (b := M.next s M.ymax)).exists_bound_of_continuousOn
      (hf.mono Set.Icc_subset_Ici_self)
  have heq : (fun y => g (M.next s y)) =ᵐ[M.law] fun y => f (M.next s y) := by
    filter_upwards [M.ae_next hs] with y hy
    simp only [g, Function.comp_apply, max_eq_left hy.1]
  refine Integrable.of_bound ((hg.comp (M.continuous_next_y s)).aestronglyMeasurable.congr heq) C ?_
  filter_upwards [M.ae_next hs] with y hy
  exact hC _ hy

/-- A **solution** of the problem as assumed in Miao, p. 240: a value function `V` with
derivative `dV = V′` and saving policy `sav = â` that solves the Bellman equation (the maximum is
attained at `â(x)`), strictly increasing, strictly concave and continuously differentiable on
`[x_min, ∞)`, with the envelope condition `V′(x) = u′(x − â(x))`. -/
structure Solution where
  V : ℝ → ℝ
  dV : ℝ → ℝ
  sav : ℝ → ℝ
  hasDerivAt_V : ∀ x, M.xmin ≤ x → HasDerivAt V (dV x) x
  dV_cont : ContinuousOn dV (Set.Ici M.xmin)
  V_mono : StrictMonoOn V (Set.Ici M.xmin)
  V_concave : StrictConcaveOn ℝ (Set.Ici M.xmin) V
  sav_mem : ∀ x, M.xmin ≤ x → sav x ∈ Set.Icc 0 x
  bellman : ∀ x, M.xmin ≤ x → V x = M.u (x - sav x) + M.β * ∫ y, V (M.next (sav x) y) ∂M.law
  bellman_le : ∀ x, M.xmin ≤ x → ∀ s ∈ Set.Icc 0 x,
    M.u (x - s) + M.β * ∫ y, V (M.next s y) ∂M.law ≤ V x
  envelope : ∀ x, M.xmin ≤ x → dV x = M.du (x - sav x)

namespace Solution

variable {M} (S : M.Solution)

/-- The consumption policy `c(x) = x − â(x)`. -/
def cons (x : ℝ) : ℝ := x - S.sav x

/-- The continuation value `W(s) = E V(Rs + y − rb)`. -/
noncomputable def W (s : ℝ) : ℝ := ∫ y, S.V (M.next s y) ∂M.law

/-- The expected marginal value `D(s) = E V′(Rs + y − rb)`. -/
noncomputable def D (s : ℝ) : ℝ := ∫ y, S.dV (M.next s y) ∂M.law

theorem V_contOn : ContinuousOn S.V (Set.Ici M.xmin) :=
  fun x hx => (S.hasDerivAt_V x hx).continuousAt.continuousWithinAt

/-- `V′` is strictly decreasing on `[x_min, ∞)` (strict concavity). -/
theorem dV_strictAnti : StrictAntiOn S.dV (Set.Ici M.xmin) := by
  intro a ha c hc hac
  have h := S.V_concave.strictAntiOn_deriv (fun x hx => (S.hasDerivAt_V x hx).differentiableAt)
    ha hc hac
  rwa [(S.hasDerivAt_V a ha).deriv, (S.hasDerivAt_V c hc).deriv] at h

/-- `V′ ≥ 0` on `[x_min, ∞)` (`V` is increasing). -/
theorem dV_nonneg {x : ℝ} (hx : M.xmin ≤ x) : 0 ≤ S.dV x := by
  have h := (hasDerivAt_iff_tendsto_slope.1 (S.hasDerivAt_V x hx)).mono_left
    (nhdsGT_le_nhdsNE x)
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.2 (S.V_mono.monotoneOn (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 (hx.trans (Set.mem_Ioi.1 hz).le)) (Set.mem_Ioi.1 hz).le))
    (sub_pos.2 (Set.mem_Ioi.1 hz)).le

/-- The mean value bounds for `V`: for `x_min ≤ z ≤ z′`,
`V′(z′)(z′ − z) ≤ V(z′) − V(z) ≤ V′(z)(z′ − z)`. -/
theorem tangent_V {z z' : ℝ} (hz : M.xmin ≤ z) (hzz : z ≤ z') :
    S.dV z' * (z' - z) ≤ S.V z' - S.V z ∧ S.V z' - S.V z ≤ S.dV z * (z' - z) := by
  rcases hzz.lt_or_eq with hlt | heq
  · obtain ⟨ξ, hξm, hslope⟩ := exists_hasDerivAt_eq_slope S.V S.dV hlt
      (S.V_contOn.mono fun w hw => Set.mem_Ici.2 (hz.trans hw.1))
      (fun w hw => S.hasDerivAt_V w (hz.trans hw.1.le))
    have hpos : 0 < z' - z := sub_pos.2 hlt
    have heq : S.V z' - S.V z = S.dV ξ * (z' - z) := by
      rw [hslope]; field_simp
    have hξ : M.xmin ≤ ξ := hz.trans hξm.1.le
    rw [heq]
    refine ⟨mul_le_mul_of_nonneg_right (S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hξ)
      (Set.mem_Ici.2 (hz.trans hlt.le)) hξm.2.le) hpos.le,
      mul_le_mul_of_nonneg_right (S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hz)
      (Set.mem_Ici.2 hξ) hξm.1.le) hpos.le⟩
  · subst heq; simp

theorem integrable_V {s : ℝ} (hs : 0 ≤ s) : Integrable (fun y => S.V (M.next s y)) M.law :=
  M.integrable_comp S.V_contOn hs

theorem integrable_dV {s : ℝ} (hs : 0 ≤ s) : Integrable (fun y => S.dV (M.next s y)) M.law :=
  M.integrable_comp S.dV_cont hs

/-- `R(s′ − s)D(s′) ≤ W(s′) − W(s) ≤ R(s′ − s)D(s)` for `0 ≤ s ≤ s′`. -/
theorem W_sub_bounds {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') :
    M.R * (s' - s) * S.D s' ≤ S.W s' - S.W s ∧ S.W s' - S.W s ≤ M.R * (s' - s) * S.D s := by
  have hs' : 0 ≤ s' := hs.trans hss
  have hR := M.R_pos
  have hsub : S.W s' - S.W s = ∫ y, (S.V (M.next s' y) - S.V (M.next s y)) ∂M.law :=
    (integral_sub (S.integrable_V hs') (S.integrable_V hs)).symm
  have hD : ∀ t, M.R * (s' - s) * S.D t = ∫ y, S.dV (M.next t y) * (M.R * (s' - s)) ∂M.law :=
    fun t => by rw [integral_mul_const, D, mul_comm]
  have hle : ∀ᵐ y ∂M.law, M.xmin ≤ M.next s y ∧ M.next s y ≤ M.next s' y := by
    filter_upwards [M.ae_next hs] with y hy
    refine ⟨hy.1, ?_⟩
    have := M.next_sub s s' y
    nlinarith
  rw [hsub, hD, hD]
  constructor
  · refine integral_mono_ae ((S.integrable_dV hs').mul_const _)
      ((S.integrable_V hs').sub (S.integrable_V hs)) ?_
    filter_upwards [hle] with y hy
    have := (S.tangent_V hy.1 hy.2).1
    rwa [M.next_sub] at this
  · refine integral_mono_ae ((S.integrable_V hs').sub (S.integrable_V hs))
      ((S.integrable_dV hs).mul_const _) ?_
    filter_upwards [hle] with y hy
    have := (S.tangent_V hy.1 hy.2).2
    rwa [M.next_sub] at this

/-- `D(s) ≤ V′(x_min)`. -/
theorem D_le {s : ℝ} (hs : 0 ≤ s) : S.D s ≤ S.dV M.xmin := by
  have : S.D s ≤ ∫ _y, S.dV M.xmin ∂M.law := by
    refine integral_mono_ae (S.integrable_dV hs) (integrable_const _) ?_
    filter_upwards [M.ae_next hs] with y hy
    exact S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.1) hy.1
  simpa using this

/-- `D(s) ≥ 0`. -/
theorem D_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ S.D s := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [M.ae_next hs] with y hy
  exact S.dV_nonneg hy.1

/-- `D` is strictly decreasing on `[0, ∞)` (strict concavity of `V`). -/
theorem D_strictAnti : StrictAntiOn S.D (Set.Ici 0) := by
  intro s hs s' hs' hss
  have hs0 : (0 : ℝ) ≤ s := hs
  have hs'0 : (0 : ℝ) ≤ s' := hs'
  have hpos : 0 < ∫ y, (S.dV (M.next s y) - S.dV (M.next s' y)) ∂M.law := by
    refine si_integral_pos ((S.integrable_dV hs0).sub (S.integrable_dV hs'0)) ?_
    filter_upwards [M.ae_next hs0] with y hy
    have hlt : M.next s y < M.next s' y := by
      have := M.next_sub s s' y
      have := mul_pos M.R_pos (sub_pos.2 hss)
      linarith
    exact sub_pos.2 (S.dV_strictAnti (Set.mem_Ici.2 hy.1) (Set.mem_Ici.2 (hy.1.trans hlt.le)) hlt)
  rw [integral_sub (S.integrable_dV hs0) (S.integrable_dV hs'0)] at hpos
  change S.D s' < S.D s
  simp only [D]
  linarith

/-- `D` is continuous on `[0, ∞)` (dominated convergence, `0 ≤ V′ ≤ V′(x_min)`). -/
theorem D_continuousOn : ContinuousOn S.D (Set.Ici 0) := by
  refine continuousOn_of_dominated (bound := fun _ => S.dV M.xmin)
    (fun s hs => (S.integrable_dV hs).aestronglyMeasurable) (fun s hs => ?_)
    (integrable_const _) ?_
  · filter_upwards [M.ae_next hs] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (S.dV_nonneg hy.1)]
    exact S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.1) hy.1
  · filter_upwards [M.supp] with y hy
    exact S.dV_cont.comp (M.continuous_next y).continuousOn
      fun s hs => Set.mem_Ici.2 (M.next_ge hs hy.1)

end Solution

end SIModel

end Miao.IncompleteMarkets
