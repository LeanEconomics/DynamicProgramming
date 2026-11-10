/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBModel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field

/-!
# Various utility functions in the RBC model

Miao, §14.3.1, pp. 487–493.

* **KPR utility** (14.38) `u(c, n) = (c(1 − n)^χ)^{1−γ}/(1 − γ)` (`rb_u38`) is of the King–Plosser–
  Rebelo form (14.5) `c^{1−γ}v(n)/(1 − γ)` with `v(n) = (1 − n)^{χ(1−γ)}` (`rb_u38_kpr`), and
  (14.39) `ln c − χn^{1+ν}/(1 + ν)` (`rb_u39`) is of the form (14.6) (`rb_u39_kpr`).
* "When `γ = 1`, (14.38) reduces to (14.22)": corrected, `((c(1 − n)^χ)^{1−γ} − 1)/(1 − γ)`
  (which differs from (14.38) by the constant `1/(1 − γ)`, hence represents the same preferences)
  tends to `ln c + χ ln(1 − n)` as `γ → 1` (`rb_u38_limit`); (14.38) as printed has no limit at
  `γ = 1` (`rb_u38_printed_no_limit`).
* Marginal utilities and the marginal rate of substitution of (14.38):
  `u_c = c^{−γ}(1 − n)^{χ(1−γ)}`, `u_n = −χc^{1−γ}(1 − n)^{χ(1−γ)−1}`, `−u_n/u_c = χc/(1 − n)`
  for every `γ` (`rb_u38_uc`, `rb_u38_un`, `rb_u38_mrs`), so the intratemporal condition is
  (14.27) and the steady state and the calibrated `χ` do not depend on `γ` ("we still obtain
  `χ = 1.75`", `rb_u38_intratemporal`).
* Balanced growth (the KPR class): `u_c(gc, n) = g^{−γ}u_c(c, n)` and the MRS is homogeneous of
  degree one in `c` (`rb_u38_homog`); along `c_t = gᵗc₀`, `w_t = gᵗw₀`, `n` constant, the
  intratemporal condition holds at all dates iff at date 0, and the Euler equation holds with
  the constant gross return `R = g^γ/β` (`rb_u38_bgp`). For (14.39), `u_c = 1/c` and the MRS is
  `χn^νc` (`rb_u39_mrs`), also homogeneous of degree one in `c`.
* The Frisch elasticity of (14.39) is `1/ν` (`rb_u39_frisch`): with marginal utility `λ` held
  fixed, `χn^ν = λw` gives `n = (λw/χ)^{1/ν}` and `d ln n/d ln w = 1/ν`.
* **Indivisible labour** (`ν = 0`; Hansen (1985), Rogerson (1988)): with lotteries over working
  `n̄` hours or not, full insurance is optimal and the representative household's expected
  utility is `ln c − BN`, `N = pn̄`, `B = −χ ln(1 − n̄)/n̄ > 0`: (14.39) with `ν = 0`
  (`rb_lottery`).
* Labour-market comparative statics: with (14.39) the log-linearised supply is `νN̂ = ŵ − Ĉ`
  (`rb_u39_supply_loglin`); at given `Ĉ`, `K̂` the hours response to `ẑ` is `1/(α + ν)` (largest
  for indivisible labour) and the wage response is `ν/(α + ν)` (zero for `ν = 0`)
  (`rb_nu_responses`); a larger consumption response lowers hours and output and raises the
  wage (`rb_consumption_channel`, the intuition for Figure 14.7).
* **GHH utility** (14.40) `U(c − G(n))`: `−u_n/u_c = G′(n)` (`rb_ghh_mrs`), independent of `c`
  (no wealth effect), so hours solve `G′(n) = (1 − α)zK^αn^{−α}`, uniquely if `G′` is increasing
  (`rb_ghh_hours`); GHH preferences are outside the KPR class: the MRS is not homogeneous of
  degree one in `c` (`rb_ghh_not_kpr`).
* **Habit formation**: marginal utility `Λ_t = 1/(C_t − bC_{t−1}) − βbE_t[1/(C_{t+1} − bC_t)]`
  is the derivative of lifetime utility in `C_t` (`rb_habit_mu`, finitely many successor states).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### KPR utility (14.38)–(14.39) -/

/-- Miao, (14.38), p. 488: `u(c, n) = (c(1 − n)^χ)^{1−γ}/(1 − γ)`. -/
noncomputable def rb_u38 (γ χ c n : ℝ) : ℝ := (c * (1 - n) ^ χ) ^ (1 - γ) / (1 - γ)

/-- Miao, (14.39), p. 488: `u(c, n) = ln c − χn^{1+ν}/(1 + ν)`. -/
noncomputable def rb_u39 (ν χ c n : ℝ) : ℝ := Real.log c - χ * n ^ (1 + ν) / (1 + ν)

/-- Miao, p. 488: (14.38) is of the KPR form (14.5) `c^{1−γ}v(n)/(1 − γ)` with
`v(n) = (1 − n)^{χ(1−γ)}`. -/
theorem rb_u38_kpr (γ χ : ℝ) {c n : ℝ} (hc : 0 ≤ c) (hn : n ≤ 1) :
    rb_u38 γ χ c n = c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ)) / (1 - γ) := by
  rw [rb_u38, Real.mul_rpow hc (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith)]

/-- Miao, p. 488: (14.39) is of the KPR form (14.6) `ln c + v(n)` with
`v(n) = −χn^{1+ν}/(1 + ν)`. -/
theorem rb_u39_kpr (ν χ c n : ℝ) :
    rb_u39 ν χ c n = Real.log c + (fun m => -(χ * m ^ (1 + ν) / (1 + ν))) n := by
  simp only [rb_u39]
  ring

/-- Miao, p. 489, corrected: as `γ → 1`, `((c(1 − n)^χ)^{1−γ} − 1)/(1 − γ)`, which differs from
(14.38) by the constant `1/(1 − γ)`, tends to `ln c + χ ln(1 − n)`, the period utility of
(14.22). -/
theorem rb_u38_limit (χ : ℝ) {c n : ℝ} (hc : 0 < c) (hn : n < 1) :
    Tendsto (fun γ => (rb_u38 γ χ c n - 1 / (1 - γ))) (𝓝[≠] 1)
      (𝓝 (Real.log c + χ * Real.log (1 - n))) := by
  set x := c * (1 - n) ^ χ
  have hx : 0 < x := mul_pos hc (Real.rpow_pos_of_pos (by linarith) _)
  have hlog : Real.log x = Real.log c + χ * Real.log (1 - n) := by
    rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
  -- the derivative of `h ↦ x^h = exp(h ln x)` at `0` is `ln x`
  have hd : HasDerivAt (fun h => Real.exp (h * Real.log x)) (Real.log x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log x)).exp
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hmap : Tendsto (fun γ : ℝ => 1 - γ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun γ : ℝ => 1 - γ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with γ hγ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hγ ⊢
      intro h
      exact hγ (by linarith)
  rw [← hlog]
  refine (hs.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  simp only [Function.comp_apply, slope_def_field, zero_mul, Real.exp_zero, sub_zero, rb_u38]
  rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
  ring

/-- Miao, p. 489: the printed claim that (14.38) "reduces to" (14.22) at `γ = 1` cannot be read
as a limit: at `c = 1`, `n = 0`, (14.38) equals `1/(1 − γ)`, which has no finite limit as
`γ → 1`. -/
theorem rb_u38_printed_no_limit (χ L : ℝ) :
    ¬ Tendsto (fun γ => rb_u38 γ χ 1 0) (𝓝[≠] 1) (𝓝 L) := by
  intro h
  have h1 : Tendsto (fun γ => rb_u38 γ χ 1 0) (𝓝[>] 1) (𝓝 L) :=
    h.mono_left (nhdsWithin_mono _ fun γ hγ => ne_of_gt hγ)
  have hbot : Tendsto (fun γ : ℝ => rb_u38 γ χ 1 0) (𝓝[>] 1) atBot := by
    have hm : Tendsto (fun γ : ℝ => 1 - γ) (𝓝[>] 1) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun γ : ℝ => 1 - γ) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with γ hγ
        simp only [Set.mem_Ioi] at hγ
        simp only [Set.mem_Iio]
        linarith
    refine (tendsto_inv_nhdsLT_zero.comp hm).congr' (Eventually.of_forall fun γ => ?_)
    simp [rb_u38]
  exact not_tendsto_nhds_of_tendsto_atBot hbot L h1

/-- The marginal utility of consumption under (14.38): `u_c = c^{−γ}(1 − n)^{χ(1−γ)}`. -/
theorem rb_u38_uc {γ χ c n : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) (hn : n < 1) :
    HasDerivAt (fun c' => rb_u38 γ χ c' n) (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) c := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hd := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).mul_const
    ((1 - n) ^ (χ * (1 - γ)))).div_const (1 - γ)
  have heq : (fun c' => rb_u38 γ χ c' n) =ᶠ[𝓝 c]
      fun c' => c' ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ)) / (1 - γ) := by
    filter_upwards [lt_mem_nhds hc] with c' hc'
    exact rb_u38_kpr γ χ hc'.le hn.le
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- The marginal (dis)utility of labour under (14.38):
`u_n = −χc^{1−γ}(1 − n)^{χ(1−γ)−1}`. -/
theorem rb_u38_un {γ χ c n : ℝ} (hγ : γ ≠ 1) (hc : 0 ≤ c) (hn : n < 1) :
    HasDerivAt (fun n' => rb_u38 γ χ c n')
      (-(χ * c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ) - 1))) n := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hd := ((((hasDerivAt_id n).const_sub 1).rpow_const (p := χ * (1 - γ))
    (Or.inl (by simp; linarith))).const_mul (c ^ (1 - γ))).div_const (1 - γ)
  have heq : (fun n' => rb_u38 γ χ c n') =ᶠ[𝓝 n]
      fun n' => c ^ (1 - γ) * (1 - id n') ^ (χ * (1 - γ)) / (1 - γ) := by
    filter_upwards [gt_mem_nhds hn] with n' hn'
    exact rb_u38_kpr γ χ hc hn'.le
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [id]
  field_simp

/-- Miao, p. 489: under (14.38) the marginal rate of substitution is `−u_n/u_c = χc/(1 − n)` for
every `γ ≠ 1`, the same as under (14.22). -/
theorem rb_u38_mrs {γ χ c n : ℝ} (hc : 0 < c) (hn : n < 1) :
    χ * c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ) - 1) / (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) =
      χ * c / (1 - n) := by
  have h1n : 0 < 1 - n := by linarith
  rw [Real.rpow_sub h1n, Real.rpow_one, show 1 - γ = 1 + -γ by ring, Real.rpow_add hc,
    Real.rpow_one]
  have := Real.rpow_pos_of_pos hc (-γ)
  have := Real.rpow_pos_of_pos h1n (χ * (1 + -γ))
  field_simp

/-- Miao, p. 489 ("using the previous calibration strategy, we still obtain `χ = 1.75` in
(14.38)"): under (14.38) the intratemporal condition `−u_n/u_c = w` with `w` the marginal
product of labour is exactly (14.27), whatever `γ`; the steady-state Euler equation
`u_c = βu_c(R_k + 1 − δ)` at constant `(c, n)` is `1 = β(R_k + 1 − δ)`. Hence the steady state
and the calibrated `χ` (`RBSteadyState`) do not depend on `γ`. -/
theorem rb_u38_intratemporal {α β δ γ χ z K c n Rk : ℝ} (hc : 0 < c) (hn : n < 1) :
    (χ * c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ) - 1) / (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) =
        rb_MPL α z K n ↔ eq_14_27 α χ z K c n) ∧
      (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) =
          β * (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) * (Rk + 1 - δ) ↔ 1 = β * (Rk + 1 - δ)) := by
  refine ⟨by rw [rb_u38_mrs hc hn, eq_14_27], ?_⟩
  have hu : 0 < c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) :=
    mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos (by linarith) _)
  constructor
  · intro h
    have : c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * 1 =
        c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * (β * (Rk + 1 - δ)) := by linarith
    exact mul_left_cancel₀ hu.ne' this
  · intro h
    calc c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) = c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * 1 :=
          (mul_one _).symm
      _ = c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * (β * (Rk + 1 - δ)) := by rw [← h]
      _ = _ := by ring

/-- Balanced growth (Miao, pp. 459 and 488, the KPR class): under (14.38),
`u_c(gc, n) = g^{−γ}u_c(c, n)` and `MRS(gc, n) = g·MRS(c, n)`. -/
theorem rb_u38_homog {γ χ g c n : ℝ} (hg : 0 < g) (hc : 0 < c) :
    (g * c) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) = g ^ (-γ) * (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) ∧
      χ * (g * c) / (1 - n) = g * (χ * c / (1 - n)) := by
  refine ⟨?_, by ring⟩
  rw [Real.mul_rpow hg.le hc.le]
  ring

/-- Balanced growth path under (14.38): with `n` constant, `c_t = gᵗc₀` and `w_t = gᵗw₀`
(`g > 0`), the intratemporal condition `χc_t/(1 − n) = w_t` holds at every date iff it holds at
date `0`, and the Euler equation `u_c(c_t, n) = βu_c(c_{t+1}, n)R` holds at every date iff
`R = g^γ/β`. -/
theorem rb_u38_bgp {β γ χ g c0 w0 n R : ℝ} (hβ : 0 < β) (hg : 0 < g) (hc : 0 < c0)
    (hn : n < 1) :
    ((∀ t : ℕ, χ * (g ^ t * c0) / (1 - n) = g ^ t * w0) ↔ χ * c0 / (1 - n) = w0) ∧
      ((∀ t : ℕ, (g ^ t * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) =
          β * ((g ^ (t + 1) * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) * R) ↔
        R = g ^ γ / β) := by
  have hv : 0 < (1 - n) ^ (χ * (1 - γ)) := Real.rpow_pos_of_pos (by linarith) _
  constructor
  · constructor
    · intro h; simpa using h 0
    · intro h t
      rw [← h]
      ring
  · have key : ∀ t : ℕ, (g ^ (t + 1) * c0) ^ (-γ) = g ^ (-γ) * (g ^ t * c0) ^ (-γ) := fun t => by
      rw [pow_succ, mul_comm (g ^ t) g, mul_assoc, Real.mul_rpow hg.le (by positivity)]
    have hgg : g ^ (-γ) * g ^ γ = 1 := by
      rw [← Real.rpow_add hg, neg_add_cancel, Real.rpow_zero]
    constructor
    · intro h
      have h0 := h 0
      rw [key 0] at h0
      have hp : 0 < (g ^ 0 * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) :=
        mul_pos (Real.rpow_pos_of_pos (by simpa using hc) _) hv
      have h1 : 1 = β * g ^ (-γ) * R := by
        have : (g ^ 0 * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * 1 =
            (g ^ 0 * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * (β * g ^ (-γ) * R) := by
          rw [mul_one]; nth_rewrite 1 [h0]; ring
        exact mul_left_cancel₀ hp.ne' this
      rw [eq_div_iff hβ.ne']
      linear_combination (-(g ^ γ)) * h1 + (-(β * R)) * hgg
    · intro h t
      rw [key t, h]
      have hb : β ≠ 0 := hβ.ne'
      have : β * (g ^ (-γ) * (g ^ t * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) * (g ^ γ / β) =
          (g ^ (-γ) * g ^ γ) * ((g ^ t * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) := by
        field_simp
      rw [this, hgg, one_mul]

/-- Under (14.39), `u_c = 1/c`, `u_n = −χn^ν`, and `−u_n/u_c = χn^νc`, homogeneous of degree one
in `c` (balanced growth). -/
theorem rb_u39_mrs {ν χ c n : ℝ} (hc : 0 < c) (hn : 0 < n) (hν : 1 + ν ≠ 0) :
    HasDerivAt (fun c' => rb_u39 ν χ c' n) (1 / c) c ∧
      HasDerivAt (fun n' => rb_u39 ν χ c n') (-(χ * n ^ ν)) n ∧
      χ * n ^ ν / (1 / c) = χ * n ^ ν * c ∧
      ∀ g : ℝ, χ * n ^ ν * (g * c) = g * (χ * n ^ ν * c) := by
  refine ⟨?_, ?_, by field_simp, fun g => by ring⟩
  · have := (Real.hasDerivAt_log hc.ne').sub_const (χ * n ^ (1 + ν) / (1 + ν))
    simpa [rb_u39, one_div] using this
  · have h := (((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hn.ne')).const_mul χ).div_const
      (1 + ν)).const_sub (Real.log c)
    refine h.congr_deriv ?_
    rw [show 1 + ν - 1 = ν by ring]
    field_simp

/-- **The Frisch elasticity** of (14.39) is `1/ν` (Miao, p. 488): holding the marginal utility
of consumption `λ > 0` fixed, the first-order condition `χn^ν = λw` holds iff
`n = (λw/χ)^{1/ν}`, and along `w(s) = we^s`, `ln n(s) = ln n + s/ν`. -/
theorem rb_u39_frisch {ν χ lam w n : ℝ} (hν : 0 < ν) (hχ : 0 < χ) (hlam : 0 < lam)
    (hw : 0 < w) (hn : 0 < n) :
    (χ * n ^ ν = lam * w ↔ n = (lam * w / χ) ^ ν⁻¹) ∧
      ∀ s : ℝ, Real.log ((lam * (w * Real.exp s) / χ) ^ ν⁻¹) =
        Real.log ((lam * w / χ) ^ ν⁻¹) + s / ν := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun s => ?_⟩
  · rw [← h, mul_div_cancel_left₀ _ hχ.ne', Real.rpow_rpow_inv hn.le hν.ne']
  · rw [h, Real.rpow_inv_rpow (by positivity) hν.ne']
    field_simp
  · rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity),
      show lam * (w * Real.exp s) / χ = lam * w / χ * Real.exp s by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    field_simp

/-- The log-linearised labour supply under (14.39): the derivative of
`ln(χn^νc) − ln w` along `X(s) = Xe^{sX̂}` is `νN̂ + Ĉ − ŵ`, so supply is `νN̂ = ŵ − Ĉ`. -/
theorem rb_u39_supply_loglin {ν χ c n w : ℝ} (hχ : 0 < χ) (hc : 0 < c) (hn : 0 < n)
    (hw : 0 < w) (ch nh wh : ℝ) :
    ∀ s : ℝ, Real.log (χ * (n * Real.exp (s * nh)) ^ ν * (c * Real.exp (s * ch))) -
        Real.log (w * Real.exp (s * wh)) =
      Real.log (χ * n ^ ν * c) - Real.log w + s * (ν * nh + ch - wh) := by
  intro s
  rw [Real.mul_rpow hn.le (Real.exp_pos _).le, ← Real.exp_mul,
    show χ * (n ^ ν * Real.exp (s * nh * ν)) * (c * Real.exp (s * ch)) =
      χ * n ^ ν * c * Real.exp (s * nh * ν + s * ch) by rw [Real.exp_add]; ring,
    Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_mul hw.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 489 (Figure 14.8): with the supply `νN̂ = ŵ − Ĉ` and demand `ŵ = ẑ + αK̂ − αN̂`,
`N̂ = (ẑ + αK̂ − Ĉ)/(α + ν)` and `ŵ = (ν(ẑ + αK̂) + αĈ)/(α + ν)`; at given `Ĉ`, `K̂`, the hours
response `1/(α + ν)` to `ẑ` is decreasing in `ν` (largest for indivisible labour, `ν = 0`) and
the wage response `ν/(α + ν)` is increasing in `ν` (zero for `ν = 0`). -/
theorem rb_nu_responses {α : ℝ} (hα : 0 < α) :
    (∀ {ν c z k n wh : ℝ}, 0 ≤ ν → (ν * n = wh - c ∧ wh = z + α * k - α * n) →
      n = (z + α * k - c) / (α + ν) ∧ wh = (ν * (z + α * k) + α * c) / (α + ν)) ∧
      StrictAntiOn (fun ν : ℝ => 1 / (α + ν)) (Set.Ici 0) ∧
      StrictMonoOn (fun ν : ℝ => ν / (α + ν)) (Set.Ici 0) ∧ (0 : ℝ) / (α + 0) = 0 := by
  refine ⟨fun {ν c z k n wh} hν ⟨h1, h2⟩ => ?_, fun a ha b hb hab => ?_,
    fun a ha b hb hab => ?_, by simp⟩
  · have hd : 0 < α + ν := by linarith
    have hn : n = (z + α * k - c) / (α + ν) := by
      field_simp
      linarith
    refine ⟨hn, ?_⟩
    rw [h2, hn]
    field_simp
    ring
  · simp only [Set.mem_Ici] at ha hb
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · simp only [Set.mem_Ici] at ha hb
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- Miao, p. 489 (Figure 14.7): "the bigger is the consumption increase, the bigger is this
inward shift in labour supply, and therefore the smaller is the hours response in equilibrium and
the larger is the wage response. As a result, the initial jump in output is smaller." With the
supply `ζN̂ = ŵ − Ĉ` and demand `ŵ = ẑ + αK̂ − αN̂`, a larger `Ĉ` (at the same `ẑ`, `K̂`) gives
lower `N̂`, higher `ŵ` and lower `Ŷ = αK̂ + (1 − α)N̂ + ẑ`. -/
theorem rb_consumption_channel {α ζ z k c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hζ : 0 < ζ)
    (hc : c₁ < c₂) :
    (z + α * k - c₂) / (α + ζ) < (z + α * k - c₁) / (α + ζ) ∧
      (ζ * (z + α * k) + α * c₁) / (α + ζ) < (ζ * (z + α * k) + α * c₂) / (α + ζ) ∧
      α * k + (1 - α) * ((z + α * k - c₂) / (α + ζ)) + z <
        α * k + (1 - α) * ((z + α * k - c₁) / (α + ζ)) + z := by
  have hd : 0 < α + ζ := by linarith
  have h1 : (z + α * k - c₂) / (α + ζ) < (z + α * k - c₁) / (α + ζ) :=
    div_lt_div_of_pos_right (by linarith) hd
  refine ⟨h1, div_lt_div_of_pos_right (by nlinarith) hd, ?_⟩
  have : 0 < 1 - α := by linarith
  nlinarith

/-! ### Indivisible labour: the Hansen–Rogerson lottery -/

/-- **Indivisible labour** (Miao, p. 489; Hansen (1985), Rogerson (1988)). Each household works
`n̄ ∈ (0, 1)` hours or none; it works with probability `p ∈ [0, 1]` and consumes `c₁` if it works
and `c₀` if not, with `pc₁ + (1 − p)c₀ = c`. Its expected utility
`p(ln c₁ + χ ln(1 − n̄)) + (1 − p)(ln c₀ + χ ln 1)` is at most `ln c + pχ ln(1 − n̄)`, with
equality under full insurance `c₁ = c₀ = c`; and `ln c + pχ ln(1 − n̄) = ln c − BN` with
`N = pn̄` and `B = −χ ln(1 − n̄)/n̄ > 0`: (14.39) with `ν = 0`. -/
theorem rb_lottery {χ nbar p c c₁ c₀ : ℝ} (hχ : 0 < χ) (hn0 : 0 < nbar) (hn1 : nbar < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc₁ : 0 < c₁) (hc₀ : 0 < c₀)
    (hres : p * c₁ + (1 - p) * c₀ = c) :
    p * (Real.log c₁ + χ * Real.log (1 - nbar)) + (1 - p) * (Real.log c₀ + χ * Real.log 1) ≤
        Real.log c + p * (χ * Real.log (1 - nbar)) ∧
      (0 < c → p * (Real.log c + χ * Real.log (1 - nbar)) +
        (1 - p) * (Real.log c + χ * Real.log 1) = Real.log c + p * (χ * Real.log (1 - nbar))) ∧
      Real.log c + p * (χ * Real.log (1 - nbar)) =
        rb_u39 0 (-(χ * Real.log (1 - nbar)) / nbar) c (p * nbar) ∧
      0 < -(χ * Real.log (1 - nbar)) / nbar := by
  have hcpos : 0 < c := by
    rw [← hres]
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]; simpa using hc₀
    · have : 0 ≤ (1 - p) * c₀ := mul_nonneg (by linarith) hc₀.le
      nlinarith
  have hlog1 : Real.log (1 - nbar) < 0 := Real.log_neg (by linarith) (by linarith)
  refine ⟨?_, fun _ => by simp only [Real.log_one, mul_zero, add_zero]; ring, ?_, ?_⟩
  · -- Jensen for `ln` via the weighted AM–GM inequality
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hp0 (by linarith : 0 ≤ 1 - p)
      hc₁.le hc₀.le (by ring)
    have hpos : 0 < c₁ ^ p * c₀ ^ (1 - p) :=
      mul_pos (Real.rpow_pos_of_pos hc₁ _) (Real.rpow_pos_of_pos hc₀ _)
    have hl := Real.log_le_log hpos (hamgm.trans_eq hres)
    rw [Real.log_mul (Real.rpow_pos_of_pos hc₁ _).ne' (Real.rpow_pos_of_pos hc₀ _).ne',
      Real.log_rpow hc₁, Real.log_rpow hc₀] at hl
    simp only [Real.log_one, mul_zero, add_zero]
    nlinarith
  · simp only [rb_u39, add_zero, Real.rpow_one, div_one]
    field_simp
    ring
  · have : 0 < -(χ * Real.log (1 - nbar)) := by nlinarith
    positivity

/-! ### GHH utility (14.40) -/

/-- Miao, (14.40), p. 489: under GHH utility `u(c, n) = U(c − G(n))`, `u_c = U′(c − G(n))` and
`u_n = −U′(c − G(n))G′(n)`, so with `U′ > 0` the labour supply condition `−u_n/u_c = w` is
`G′(n) = w`, which does not involve `c`. -/
theorem rb_ghh_mrs {U G : ℝ → ℝ} {U' G' c n w : ℝ} (hU : HasDerivAt U U' (c - G n))
    (hG : HasDerivAt G G' n) (hU' : 0 < U') :
    HasDerivAt (fun c' => U (c' - G n)) U' c ∧
      HasDerivAt (fun n' => U (c - G n')) (-(U' * G')) n ∧ (U' * G' / U' = w ↔ G' = w) := by
  refine ⟨?_, ?_, ?_⟩
  · convert hU.comp c ((hasDerivAt_id c).sub_const (G n)) using 1
    · funext x
      simp only [Function.comp_apply, id]
    · ring
  · convert hU.comp n (hG.const_sub c) using 1
    · rfl
    · ring
  · rw [mul_div_cancel_left₀ _ hU'.ne']

/-- Miao, p. 490: "consumption does not affect labour supply ... the shift in labour demand
determines the change in hours and wage." With GHH preferences and `G′` monotone increasing,
the labour-market equilibrium `G′(n) = (1 − α)zK^αn^{−α}` has at most one solution `n > 0`, and
it does not depend on consumption. -/
theorem rb_ghh_hours {α z K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 < z) (hK : 0 < K)
    {G' : ℝ → ℝ} (hG : Monotone G') {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (h₁ : G' n₁ = rb_MPL α z K n₁) (h₂ : G' n₂ = rb_MPL α z K n₂) : n₁ = n₂ := by
  have hanti : ∀ a b, 0 < a → a < b → rb_MPL α z K b < rb_MPL α z K a := fun a b ha hab => by
    unfold rb_MPL
    have := Real.rpow_lt_rpow_of_neg ha hab (by linarith : -α < 0)
    have hc : 0 < (1 - α) * z * K ^ α :=
      mul_pos (mul_pos (by linarith) hz) (Real.rpow_pos_of_pos hK _)
    nlinarith
  rcases lt_trichotomy n₁ n₂ with h | h | h
  · have := hG h.le
    have := hanti n₁ n₂ hn₁ h
    linarith
  · exact h
  · have := hG h.le
    have := hanti n₂ n₁ hn₂ h
    linarith

/-- Miao, p. 488 ("other utility models outside the KPR class"): GHH utility is not of the KPR
class: with `G(n) = n²/2` the MRS `G′(n) = n` is not homogeneous of degree one in `c`
(`MRS(2c, 1) ≠ 2·MRS(c, 1)`), so it is not compatible with balanced growth with constant hours. -/
theorem rb_ghh_not_kpr : ¬ ∀ g c : ℝ, (fun (_ : ℝ) (n : ℝ) => n) (g * c) 1 =
    g * (fun (_ : ℝ) (n : ℝ) => n) c 1 := by
  intro h
  have := h 2 1
  norm_num at this

/-! ### Habit formation -/

/-- Miao, p. 492, habit formation: with lifetime utility `E∑βᵗ[ln(C_t − bC_{t−1}) + …]`, the
date-`t` consumption `C_t` enters `ln(C_t − bC_{t−1})` and `β ln(C_{t+1} − bC_t)`; with finitely
many successor states (`C_{t+1} = C₁ i` with probability `p i`), the derivative of these terms
in `C_t` is the marginal utility `Λ_t = 1/(C_t − bC_{t−1}) − βbE_t[1/(C_{t+1} − bC_t)]`. -/
theorem rb_habit_mu {ι : Type*} [Fintype ι] {β b Cm C : ℝ} {p C₁ : ι → ℝ} (hC : 0 < C - b * Cm)
    (hC₁ : ∀ i, 0 < C₁ i - b * C) :
    HasDerivAt (fun x => Real.log (x - b * Cm) + β * ∑ i, p i * Real.log (C₁ i - b * x))
      (1 / (C - b * Cm) - β * b * ∑ i, p i * (1 / (C₁ i - b * C))) C := by
  have h0 := ((hasDerivAt_id C).sub_const (b * Cm)).log hC.ne'
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((((hasDerivAt_id C).const_mul b).const_sub (C₁ i)).log (hC₁ i).ne').const_mul (p i))
  convert h0.add (hs.const_mul β) using 1
  · funext x
    simp
  · simp only [id, mul_one, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end Miao.NeoclassicalGrowth
