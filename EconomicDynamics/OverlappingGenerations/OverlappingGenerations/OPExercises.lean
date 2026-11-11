/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OPBubbles
import OverlappingGenerations.PhaseDiagram
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Exercises 16.3, 16.4 and 16.6–16.9

Miao, §16.4, pp. 556–558 (Exercise 16.5 is in `OPExercisesCES`).

* Cobb–Douglas technology `f(k) = Ak^α`: derivative and wage `w(k) = (1 − α)Ak^α`
  (`opCD`, `opCDfp`, `op_cd_hasDerivAt`, `op_cd_wage`); the steady state of `k = ck^α`
  (`opKstarCD`, `op_cd_steady_iff`) and global convergence of `k_{t+1} = ck_t^α`
  (`op_cd_converge`).
* **Exercise 16.3** (CRRA `u(c) = c^{1−γ}/(1 − γ)`, `f = k^α`): the saving function
  `s = w/(1 + β^{−1/γ}R^{1−1/γ})` (`opCRRASaving`) solves the Euler equation and is the optimum
  (`ex_16_3_euler`, `ex_16_3_optimal`); it increases in `R` for `γ < 1`, decreases for `γ > 1`
  and is `βw/(1 + β)` for `γ = 1` (`ex_16_3_mono_lt`, `ex_16_3_anti_gt`, `ex_16_3_gamma_one`);
  the law of motion (`ex_16_3_law`).
* **Exercise 16.4** (log, `f = k^α`): `k_{t+1} = β(1 − α)k_t^α/((1 + β)g_n)` (`ex_16_4_law`), the
  unique positive steady state (`ex_16_4_steady`), global convergence (`ex_16_4_converge`), the
  marginal product at the steady state and dynamic (in)efficiency, both of which occur
  (`ex_16_4_mpk`, `ex_16_4_inefficient`, `ex_16_4_efficient`).
* **Exercise 16.6** (depreciation `δ`): `R = 1 + f′(k) − δ` (`ex_16_6_rate`), the law of motion
  (`OPIsDiamondEqmDep`) and its `δ = 1` form (`ex_16_6_full`); with log utility the law does
  not depend on `δ` (`ex_16_6_log`).
* **Exercise 16.7** (spending `G_t` financed by lump-sum taxes on the young, log, `k^α`): the law
  `k_{t+1} = β((1 − α)k_t^α − G_t)/((1 + β)g_n)` (`ex_16_7_a`); a permanent increase lowers the
  stable steady state (`ex_16_7_b`); higher spending at any dates (permanent or temporary)
  lowers the whole capital path, strictly after the first higher date (`ex_16_7_bc_path`).
* **Exercise 16.8** (social security, log, `k^α`): pay-as-you-go saving and the law of motion
  (`ex_16_8_a_i`), less capital in steady state (`ex_16_8_a_ii`), the welfare effect at given
  prices (lifetime wealth falls iff `R > g_n`) and the steady-state consumption trade-off
  (`ex_16_8_a_iii`, `ex_16_8_a_iii_resources`); fully funded social security is neutral
  (`ex_16_8_b`).
* **Exercise 16.9**: the linearisation of the §16.3 system at the bubbly steady state
  (`ex_16_9_linearization`) has roots `0 < λ₁ < 1 < λ₂`: a saddle, with a unique convergent
  path for each initial capital (`ex_16_9_roots`, `ex_16_9_saddle`).

Not formalised: the drawings asked for in Exercise 16.7(b)–(c) (their content is
`ex_16_7_bc_path`) and the "explain the intuition" parts.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-! ### Cobb–Douglas technology -/

/-- Cobb–Douglas `f(k) = Ak^α`. -/
noncomputable def opCD (A α k : ℝ) : ℝ := A * k ^ α

/-- Its derivative `f′(k) = Aαk^{α−1}`. -/
noncomputable def opCDfp (A α k : ℝ) : ℝ := A * α * k ^ (α - 1)

theorem op_cd_hasDerivAt {A α k : ℝ} (hk : 0 < k) :
    HasDerivAt (opCD A α) (opCDfp A α k) k := by
  have := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).const_mul A
  unfold opCD opCDfp
  convert this using 1
  ring

/-- The Cobb–Douglas wage `w(k) = (1 − α)Ak^α`. -/
theorem op_cd_wage {A α k : ℝ} (hk : 0 < k) :
    opWage (opCD A α) (opCDfp A α) k = (1 - α) * A * k ^ α := by
  unfold opWage opCD opCDfp
  rw [Real.rpow_sub_one hk.ne']
  field_simp

/-- `k^α = k · k^{α−1}`. -/
theorem op_rpow_eq_mul {k α : ℝ} (hk : 0 < k) : k ^ α = k * k ^ (α - 1) := by
  rw [Real.rpow_sub_one hk.ne']; field_simp

/-- The positive steady state of `k = ck^α` (`0 < α < 1`, `c > 0`): `k* = c^{1/(1−α)}`. -/
noncomputable def opKstarCD (c α : ℝ) : ℝ := c ^ (1 - α)⁻¹

theorem op_kstarCD_pos {c α : ℝ} (hc : 0 < c) : 0 < opKstarCD c α :=
  Real.rpow_pos_of_pos hc _

/-- `k = ck^α` with `k > 0` iff `k = c^{1/(1−α)}`. -/
theorem op_cd_steady_iff {c α k : ℝ} (hc : 0 < c) (hα1 : α < 1) (hk : 0 < k) :
    k = c * k ^ α ↔ k = opKstarCD c α := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hka : 0 < k ^ α := Real.rpow_pos_of_pos hk α
  have hsub : k ^ (1 - α) = k / k ^ α := by
    rw [Real.rpow_sub hk, Real.rpow_one]
  constructor
  · intro h
    have : k ^ (1 - α) = c := by
      rw [hsub, div_eq_iff hka.ne']; exact h
    unfold opKstarCD
    rw [← this, Real.rpow_rpow_inv hk.le h1]
  · intro h
    have : k ^ (1 - α) = c := by
      rw [h]; unfold opKstarCD
      rw [Real.rpow_inv_rpow hc.le h1]
    rw [hsub, div_eq_iff hka.ne'] at this
    exact this

/-- Global convergence of `k_{t+1} = ck_t^α` from every `k₀ > 0` to `c^{1/(1−α)}`, via
`ln k_{t+1} − ln k* = α(ln k_t − ln k*)`. -/
theorem op_cd_converge {c α : ℝ} {k : ℕ → ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    (hk0 : 0 < k 0) (hlaw : ∀ t, k (t + 1) = c * k t ^ α) :
    (∀ t, 0 < k t) ∧ Tendsto k atTop (𝓝 (opKstarCD c α)) := by
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hlaw]; exact mul_pos hc (Real.rpow_pos_of_pos ih _)
  refine ⟨hpos, ?_⟩
  set L := Real.log c / (1 - α) with hL
  have h1 : (1 - α) ≠ 0 := by linarith
  have hlog : ∀ t, Real.log (k t) - L = α ^ t * (Real.log (k 0) - L) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hlaw, Real.log_mul hc.ne' (Real.rpow_pos_of_pos (hpos t) _).ne',
        Real.log_rpow (hpos t), pow_succ]
      have : Real.log c + α * Real.log (k t) - L = α * (Real.log (k t) - L) := by
        rw [hL]; field_simp; ring
      rw [this, ih]; ring
  have hT : Tendsto (fun t => Real.log (k t)) atTop (𝓝 L) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).mul_const (Real.log (k 0) - L)
    rw [zero_mul] at this
    have := this.add_const L
    rw [zero_add] at this
    refine this.congr fun t => ?_
    rw [← hlog t]; ring
  have hE := (Real.continuous_exp.tendsto L).comp hT
  have hk : (Real.exp ∘ fun t => Real.log (k t)) = k := by
    ext t; simp [Real.exp_log (hpos t)]
  rw [hk] at hE
  have hstar : Real.exp L = opKstarCD c α := by
    unfold opKstarCD
    rw [Real.rpow_def_of_pos hc, hL]
    congr 1
  rwa [hstar] at hE

/-! ### Exercise 16.3: CRRA utility -/

/-- The CRRA saving function `s(w, R) = w/(1 + β^{−1/γ}R^{1−1/γ})`. -/
noncomputable def opCRRASaving (β γ w R : ℝ) : ℝ :=
  w / (1 + β ^ (-1 / γ) * R ^ (1 - 1 / γ))

/-- CRRA utility `u(c) = c^{1−γ}/(1 − γ)` has `u′(c) = c^{−γ}`. -/
theorem op_crra_hasDerivAt {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun x => x ^ (1 - γ) / (1 - γ)) (c ^ (-γ)) c := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  convert this using 1
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- CRRA utility is strictly concave on `(0, ∞)` (`γ > 0`, `γ ≠ 1`). -/
theorem op_crra_strictConcave {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≠ 1) :
    StrictConcaveOn ℝ (Set.Ioi 0) (fun x => x ^ (1 - γ) / (1 - γ)) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun c hc => (op_crra_hasDerivAt hγ hc).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(op_crra_hasDerivAt hγ ha).deriv, (op_crra_hasDerivAt hγ hb).deriv]
  exact Real.rpow_lt_rpow_of_neg ha hab (by linarith)

/-- **Exercise 16.3** (Miao, p. 556): the CRRA saving `s = w/(1 + β^{−1/γ}R^{1−1/γ})` lies in
`(0, w)` and solves the Euler equation `(w − s)^{−γ} = β(Rs)^{−γ}R`. -/
theorem ex_16_3_euler {β γ w R : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hw : 0 < w) (hR : 0 < R) :
    0 < opCRRASaving β γ w R ∧ opCRRASaving β γ w R < w ∧
      (w - opCRRASaving β γ w R) ^ (-γ) =
        β * (R * opCRRASaving β γ w R) ^ (-γ) * R := by
  set q := β ^ (-1 / γ) * R ^ (1 - 1 / γ) with hq
  have hq0 : 0 < q := mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos hR _)
  have hs : opCRRASaving β γ w R = w / (1 + q) := rfl
  have hs0 : 0 < w / (1 + q) := div_pos hw (by linarith)
  have hws : w - w / (1 + q) = q * (w / (1 + q)) := by field_simp; ring
  refine ⟨by rw [hs]; exact hs0, by rw [hs, div_lt_iff₀ (by linarith)]; nlinarith, ?_⟩
  rw [hs, hws, Real.mul_rpow hq0.le hs0.le, Real.mul_rpow hR.le hs0.le, hq,
    Real.mul_rpow (Real.rpow_pos_of_pos hβ _).le (Real.rpow_pos_of_pos hR _).le,
    ← Real.rpow_mul hβ.le, ← Real.rpow_mul hR.le]
  have e1 : -1 / γ * -γ = 1 := by field_simp
  have e2 : (1 - 1 / γ) * -γ = -γ + 1 := by field_simp; ring
  rw [e1, e2, Real.rpow_one, Real.rpow_add hR, Real.rpow_one]
  ring

/-- **Exercise 16.3**: the CRRA saving maximises `u(w − s) + βu(Rs)` over `s ∈ (0, w)`. -/
theorem ex_16_3_optimal {β γ w R : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (hγ : γ ≠ 1) (hw : 0 < w)
    (hR : 0 < R) : ∀ s ∈ Set.Ioo 0 w,
      (w - s) ^ (1 - γ) / (1 - γ) + β * ((R * s) ^ (1 - γ) / (1 - γ)) ≤
        (w - opCRRASaving β γ w R) ^ (1 - γ) / (1 - γ) +
          β * ((R * opCRRASaving β γ w R) ^ (1 - γ) / (1 - γ)) := by
  obtain ⟨hs0, hsw, heul⟩ := ex_16_3_euler hβ hγ0 hw hR
  exact op_euler_sufficient (u := fun x => x ^ (1 - γ) / (1 - γ)) (up := fun c => c ^ (-γ))
    (op_crra_strictConcave hγ0 hγ).concaveOn hβ.le hR hs0 hsw
    (op_crra_hasDerivAt hγ (by linarith)) (op_crra_hasDerivAt hγ (mul_pos hR hs0)) heul

/-- **Exercise 16.3**: for `γ < 1` (substitution effect dominates) saving increases strictly
with the interest rate. -/
theorem ex_16_3_mono_lt {β γ w : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hw : 0 < w) :
    StrictMonoOn (opCRRASaving β γ w) (Set.Ioi 0) := by
  intro R hR R' hR' h
  have he : 1 - 1 / γ < 0 := by
    have : 1 < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
    linarith
  have hb := Real.rpow_pos_of_pos hβ (-1 / γ)
  have := Real.rpow_lt_rpow_of_neg hR h he
  unfold opCRRASaving
  apply div_lt_div_of_pos_left hw
  · have := Real.rpow_pos_of_pos (show (0 : ℝ) < R' from hR') (1 - 1 / γ); positivity
  · nlinarith

/-- **Exercise 16.3**: for `γ > 1` (income effect dominates) saving decreases strictly with the
interest rate. -/
theorem ex_16_3_anti_gt {β γ w : ℝ} (hβ : 0 < β) (hγ1 : 1 < γ) (hw : 0 < w) :
    StrictAntiOn (opCRRASaving β γ w) (Set.Ioi 0) := by
  intro R hR R' hR' h
  have hγ0 : 0 < γ := by linarith
  have he : 0 < 1 - 1 / γ := by
    have : 1 / γ < 1 := by rw [div_lt_iff₀ hγ0]; linarith
    linarith
  have hb := Real.rpow_pos_of_pos hβ (-1 / γ)
  have := Real.rpow_lt_rpow (le_of_lt hR) h he
  unfold opCRRASaving
  apply div_lt_div_of_pos_left hw
  · have := Real.rpow_pos_of_pos (show (0 : ℝ) < R from hR) (1 - 1 / γ); positivity
  · nlinarith

/-- **Exercise 16.3**: for `γ = 1` (log utility) saving `βw/(1 + β)` does not depend on `R`; it
is the log saving `opLogSaving` with no second-period income. -/
theorem ex_16_3_gamma_one {β w R : ℝ} (hβ : 0 < β) :
    opCRRASaving β 1 w R = β * w / (1 + β) ∧ opLogSaving β w 0 R = β * w / (1 + β) := by
  constructor
  · unfold opCRRASaving
    rw [show (-1 : ℝ) / 1 = -1 by norm_num, show (1 : ℝ) - 1 / 1 = 0 by norm_num,
      Real.rpow_zero, Real.rpow_neg_one]
    field_simp
    ring
  · unfold opLogSaving; ring

/-- **Exercise 16.3**: the equilibrium law of motion with CRRA utility and `f(k) = k^α`:
`k_{t+1} = (1 − α)k_t^α/(g_n[1 + β^{−1/γ}(1 + αk_{t+1}^{α−1})^{1−1/γ}])`. -/
theorem ex_16_3_law {β γ α gn : ℝ} {k : ℕ → ℝ} :
    OPIsDiamondEqm (opCRRASaving β γ) (opCD 1 α) (opCDfp 1 α) gn k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = (1 - α) * k t ^ α /
        (1 + β ^ (-1 / γ) * (1 + α * k (t + 1) ^ (α - 1)) ^ (1 - 1 / γ)) / gn := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [op_cd_wage h1] at h2
    exact h2.trans (by unfold opCRRASaving opRate opCDfp; ring_nf)
  · rw [op_cd_wage h1]
    exact h2.trans (by unfold opCRRASaving opRate opCDfp; ring_nf)

/-! ### Exercise 16.4: log utility and Cobb–Douglas -/

/-- **Exercise 16.4** (Miao, p. 556): with `u = ln c` and `f = k^α` the law of motion is
`k_{t+1} = β(1 − α)k_t^α/((1 + β)g_n)`. -/
theorem ex_16_4_law {β α gn : ℝ} {k : ℕ → ℝ} :
    OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCD 1 α) (opCDfp 1 α) gn k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = β * (1 - α) / ((1 + β) * gn) * k t ^ α := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [op_cd_wage h1] at h2
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)
  · rw [op_cd_wage h1]
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)

/-- **Exercise 16.4**: the unique positive steady state
`k* = [β(1 − α)/((1 + β)g_n)]^{1/(1−α)}`. -/
theorem ex_16_4_steady {β α gn k : ℝ} (hβ : 0 < β) (hα1 : α < 1) (hgn : 0 < gn) (hk : 0 < k) :
    k = β * (1 - α) / ((1 + β) * gn) * k ^ α ↔
      k = opKstarCD (β * (1 - α) / ((1 + β) * gn)) α :=
  op_cd_steady_iff (by have : 0 < 1 - α := by linarith
                       positivity) hα1 hk

/-- **Exercise 16.4**: every equilibrium path converges to `k*`. -/
theorem ex_16_4_converge {β α gn : ℝ} {k : ℕ → ℝ} (hβ : 0 < β) (hα0 : 0 < α) (hα1 : α < 1)
    (hgn : 0 < gn)
    (h : OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCD 1 α) (opCDfp 1 α) gn k) :
    Tendsto k atTop (𝓝 (opKstarCD (β * (1 - α) / ((1 + β) * gn)) α)) := by
  have hl := ex_16_4_law.1 h
  have hc : 0 < β * (1 - α) / ((1 + β) * gn) := by
    have : 0 < 1 - α := by linarith
    positivity
  exact (op_cd_converge hc hα0 hα1 (hl 0).1 fun t => (hl t).2).2

/-- **Exercise 16.4**: at the steady state `f′(k*) = α(1 + β)g_n/(β(1 − α))`, so the economy is
dynamically inefficient (`k* > k_G`) iff `α(1 + β)g_n/(β(1 − α)) < g_n − 1`. -/
theorem ex_16_4_mpk {β α gn : ℝ} (hβ : 0 < β) (hα1 : α < 1) (hgn : 0 < gn) :
    opCDfp 1 α (opKstarCD (β * (1 - α) / ((1 + β) * gn)) α) =
      α * (1 + β) * gn / (β * (1 - α)) := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have h1' : 0 < 1 - α := by linarith
  set c := β * (1 - α) / ((1 + β) * gn) with hc
  have hc0 : 0 < c := by positivity
  have hk := op_kstarCD_pos (α := α) hc0
  have hkk : opKstarCD c α ^ (1 - α) = c := by
    unfold opKstarCD; rw [Real.rpow_inv_rpow hc0.le h1]
  have hneg : opKstarCD c α ^ (α - 1) = c⁻¹ := by
    rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg hk.le, hkk]
  unfold opCDfp
  rw [hneg, hc]
  field_simp

/-- **Exercise 16.4**: dynamic inefficiency occurs: `α = 1/10`, `β = 1`, `g_n = 2` give
`f′(k*) = 4/9 < g_n − 1`. -/
theorem ex_16_4_inefficient :
    opCDfp 1 (1 / 10) (opKstarCD (1 * (1 - 1 / 10) / ((1 + 1) * 2)) (1 / 10)) < 2 - 1 := by
  rw [ex_16_4_mpk (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- **Exercise 16.4**: and so does dynamic efficiency: `α = 1/3`, `β = 1`, `g_n = 2` give
`f′(k*) = 2 > g_n − 1`. -/
theorem ex_16_4_efficient :
    2 - 1 < opCDfp 1 (1 / 3) (opKstarCD (1 * (1 - 1 / 3) / ((1 + 1) * 2)) (1 / 3)) := by
  rw [ex_16_4_mpk (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-! ### Exercise 16.6: depreciation -/

/-- The Diamond equilibrium with depreciation `δ`:
`k_{t+1} = s(w(k_t), 1 + f′(k_{t+1}) − δ)/g_n`. -/
def OPIsDiamondEqmDep (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn δ : ℝ) (k : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ k (t + 1) = s (opWage f fp (k t)) (1 + fp (k (t + 1)) - δ) / gn

/-- **Exercise 16.6** (Miao, p. 557): firms rent capital at `r`; profit maximisation gives
`r = f′(k)` (as in (16.15)), and a unit saved returns `R = 1 − δ + r = 1 + f′(k) − δ`. -/
theorem ex_16_6_rate {f fp : ℝ → ℝ} {K N r δ : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hf : HasDerivAt f (fp (K / N)) (K / N))
    (hmax : ∀ K' > 0, N * f (K' / N) - r * K' ≤ N * f (K / N) - r * K) :
    r = fp (K / N) ∧ 1 - δ + r = 1 + fp (K / N) - δ := by
  have h := eq_16_15 (R := r + 1) hK hN hf (by simpa using hmax)
  simp only [opRate] at h
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 16.6**: with full depreciation `δ = 1`, `R = f′(k)` and
`k_{t+1} = s(w(k_t), f′(k_{t+1}))/g_n`; with `δ = 0` it is (16.16). -/
theorem ex_16_6_full {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k : ℕ → ℝ} :
    (OPIsDiamondEqmDep s f fp gn 1 k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = s (opWage f fp (k t)) (fp (k (t + 1))) / gn) ∧
      (OPIsDiamondEqmDep s f fp gn 0 k ↔ OPIsDiamondEqm s f fp gn k) := by
  constructor
  · refine forall_congr' fun t => and_congr_right fun _ => ?_
    rw [show 1 + fp (k (t + 1)) - 1 = fp (k (t + 1)) by ring]
  · refine forall_congr' fun t => and_congr_right fun _ => ?_
    rw [show 1 + fp (k (t + 1)) - 0 = opRate fp (k (t + 1)) by simp [opRate]]

/-- **Exercise 16.6**: with log utility and `f = k^α` the law
`k_{t+1} = β(1 − α)k_t^α/((1 + β)g_n)` holds for every depreciation rate. -/
theorem ex_16_6_log {β α gn δ : ℝ} {k : ℕ → ℝ} :
    OPIsDiamondEqmDep (fun w R => opLogSaving β w 0 R) (opCD 1 α) (opCDfp 1 α) gn δ k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = β * (1 - α) / ((1 + β) * gn) * k t ^ α := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [op_cd_wage h1] at h2
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)
  · rw [op_cd_wage h1]
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)

/-! ### Exercise 16.7: government spending -/

/-- **Exercise 16.7(a)** (Miao, p. 557): with lump-sum taxes `G_t` on the young, log utility and
`f = k^α`, optimal saving is `β(w_t − G_t)/(1 + β)` (`op_log_saving` with income `w_t − G_t`),
and capital-market clearing gives `k_{t+1} = β((1 − α)k_t^α − G_t)/((1 + β)g_n)`. -/
theorem ex_16_7_a {β α gn : ℝ} {k Gs : ℕ → ℝ} (hβ : 0 < β) (hgn : 0 < gn)
    (hk : ∀ t, 0 < k t) :
    (∀ t, gn * k (t + 1) = opLogSaving β (opWage (opCD 1 α) (opCDfp 1 α) (k t) - Gs t) 0
      (opRate (opCDfp 1 α) (k (t + 1)))) ↔
      ∀ t, k (t + 1) = β * ((1 - α) * k t ^ α - Gs t) / ((1 + β) * gn) := by
  refine forall_congr' fun t => ?_
  rw [op_cd_wage (hk t)]
  unfold opLogSaving
  simp only [zero_div, sub_zero]
  have hb : (1 + β) ≠ 0 := by linarith
  constructor
  · intro h
    rw [eq_div_iff (mul_ne_zero hb hgn.ne')]
    field_simp at h
    linarith
  · intro h
    rw [h]; field_simp

/-- **Exercise 16.7(b)**: a permanent increase in spending from `G_L` to `G_H` lowers the stable
steady state. Steady states solve `(1 − α)k^α − dk = G` with `d = (1 + β)g_n/β`; on the stable
branch, where the slope of the law `α(1 − α)k^{α−1}/d` is at most `1`, `k_H < k_L`. -/
theorem ex_16_7_b {α d Glow Ghigh kL kH : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hkL : 0 < kL)
    (hkH : 0 < kH) (hGlh : Glow < Ghigh) (hL : (1 - α) * kL ^ α - d * kL = Glow)
    (hH : (1 - α) * kH ^ α - d * kH = Ghigh) (hstab : α * (1 - α) * kL ^ (α - 1) ≤ d) :
    kH < kL := by
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have ht := op_strictConcave_tangent (Real.strictConcaveOn_rpow hα0 hα1)
      (Set.mem_Ici.2 hkL.le) (Set.mem_Ici.2 hkH.le) h.ne' (Real.hasDerivAt_rpow_const
        (p := α) (Or.inl hkL.ne'))
    have h1 : 0 < 1 - α := by linarith
    have : (1 - α) * kH ^ α < (1 - α) * kL ^ α + α * (1 - α) * kL ^ (α - 1) * (kH - kL) := by
      nlinarith
    nlinarith
  · rw [h] at hL; linarith

/-- **Exercise 16.7(b)–(c)**: the capital path under any spending path `G′ ≥ G` (a permanent or a
temporary increase) lies below the path under `G` from the same `k₀`, strictly below after the
first date `T` with `G′_T > G_T`. -/
theorem ex_16_7_bc_path {β α gn : ℝ} {k k' Gs Gs' : ℕ → ℝ} (hβ : 0 < β) (hα0 : 0 < α)
    (hα1 : α < 1) (hgn : 0 < gn) (hk' : ∀ t, 0 < k' t) (h0 : k' 0 = k 0)
    (hlaw : ∀ t, k (t + 1) = β * ((1 - α) * k t ^ α - Gs t) / ((1 + β) * gn))
    (hlaw' : ∀ t, k' (t + 1) = β * ((1 - α) * k' t ^ α - Gs' t) / ((1 + β) * gn))
    (hG : ∀ t, Gs t ≤ Gs' t) :
    (∀ t, k' t ≤ k t) ∧ ∀ T, Gs T < Gs' T → ∀ t, T < t → k' t < k t := by
  have hc : 0 < β / ((1 + β) * gn) := by positivity
  have h1 : 0 < 1 - α := by linarith
  have hstep : ∀ t, k' t ≤ k t → k' (t + 1) ≤ k (t + 1) ∧
      (Gs t < Gs' t ∨ k' t < k t → k' (t + 1) < k (t + 1)) := by
    intro t ht
    have hp := Real.rpow_le_rpow (hk' t).le ht hα0.le
    rw [hlaw, hlaw']
    have e : ∀ x G, β * ((1 - α) * x - G) / ((1 + β) * gn) =
        β / ((1 + β) * gn) * ((1 - α) * x - G) := fun x G => by ring
    rw [e, e]
    refine ⟨mul_le_mul_of_nonneg_left (by nlinarith [hG t]) hc.le, fun hor => ?_⟩
    apply mul_lt_mul_of_pos_left _ hc
    rcases hor with hor | hor
    · nlinarith
    · have := Real.rpow_lt_rpow (hk' t).le hor hα0
      nlinarith [hG t]
  have hle : ∀ t, k' t ≤ k t := by
    intro t
    induction t with
    | zero => rw [h0]
    | succ t ih => exact (hstep t ih).1
  refine ⟨hle, fun T hT t ht => ?_⟩
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
    · exact (hstep t (hle t)).2 (Or.inr (ih h))
    · rw [h] at hT; exact (hstep t (hle t)).2 (Or.inl hT)

/-! ### Exercise 16.8: social security -/

/-- **Exercise 16.8(a)(i)** (Miao, p. 558): pay-as-you-go social security. The young pay `d_t`
and the old receive `g_nd_{t+1}`; optimal saving is `s = (β(w − d) − g_nd′/R)/(1 + β)`
(`op_log_saving` with incomes `w − d`, `g_nd′`), so the law of motion is
`g_nk_{t+1} = [β((1 − α)k_t^α − d_t) − g_nd_{t+1}/(1 + αk_{t+1}^{α−1})]/(1 + β)`. -/
theorem ex_16_8_a_i {β α gn : ℝ} {k ds : ℕ → ℝ} (hk : ∀ t, 0 < k t) :
    (∀ t, gn * k (t + 1) = opLogSaving β (opWage (opCD 1 α) (opCDfp 1 α) (k t) - ds t)
      (gn * ds (t + 1)) (opRate (opCDfp 1 α) (k (t + 1)))) ↔
      ∀ t, gn * k (t + 1) = (β * ((1 - α) * k t ^ α - ds t) -
        gn * ds (t + 1) / (1 + α * k (t + 1) ^ (α - 1))) / (1 + β) := by
  refine forall_congr' fun t => ?_
  rw [op_cd_wage (hk t)]
  unfold opLogSaving opRate opCDfp
  simp only [mul_one, one_mul]

/-- **Exercise 16.8(a)(ii)**: introducing social security lowers the steady-state capital stock:
a steady state with `d > 0` has less capital than the steady state `k₀` without. -/
theorem ex_16_8_a_ii {β α gn d k k0 : ℝ} (hβ : 0 < β) (hα0 : 0 < α) (hα1 : α < 1)
    (hgn : 0 < gn) (hd : 0 < d) (hk : 0 < k) (hk0 : 0 < k0)
    (hss : gn * k = (β * ((1 - α) * k ^ α - d) - gn * d / (1 + α * k ^ (α - 1))) / (1 + β))
    (hss0 : gn * k0 = β * ((1 - α) * k0 ^ α) / (1 + β)) : k < k0 := by
  have hR : 0 < 1 + α * k ^ (α - 1) := by
    have := Real.rpow_pos_of_pos hk (α - 1); positivity
  have hpd : 0 < gn * d / (1 + α * k ^ (α - 1)) := by positivity
  have h1 : (1 + β) * gn * k < β * (1 - α) * k ^ α := by
    rw [eq_div_iff (by linarith)] at hss
    nlinarith
  have h2 : (1 + β) * gn * k0 = β * (1 - α) * k0 ^ α := by
    rw [eq_div_iff (by linarith)] at hss0
    linarith
  rw [op_rpow_eq_mul hk] at h1
  rw [op_rpow_eq_mul hk0] at h2
  have hc : 0 < β * (1 - α) := mul_pos hβ (by linarith)
  have h1' : (1 + β) * gn < β * (1 - α) * k ^ (α - 1) := by nlinarith
  have h2' : (1 + β) * gn = β * (1 - α) * k0 ^ (α - 1) := by
    have : k0 * ((1 + β) * gn - β * (1 - α) * k0 ^ (α - 1)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hk0.ne'
    linarith
  by_contra h
  push Not at h
  have := Real.rpow_le_rpow_of_nonpos hk0 h (by linarith : α - 1 ≤ 0)
  nlinarith

/-- Lifetime utility of a generation at prices `(w, R)` under a constant pay-as-you-go
contribution `d`, at the optimal log saving: `ln c_y + β ln c_o` with lifetime wealth
`W = w − d + g_nd/R`. -/
noncomputable def opPAYGWelfare (β gn w R d : ℝ) : ℝ :=
  Real.log ((w - d + gn * d / R) / (1 + β)) +
    β * Real.log (β * R * (w - d + gn * d / R) / (1 + β))

/-- **Exercise 16.8(a)(iii)**: at given prices a larger contribution changes lifetime wealth by
`−(1 − g_n/R)` per unit: welfare of a generation falls iff `R > g_n` (dynamically efficient)
and rises iff `R < g_n` (dynamically inefficient). The optimal consumptions are those of
`op_log_saving`. -/
theorem ex_16_8_a_iii {β gn w R d1 d2 : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hd : d1 < d2) (hW1 : 0 < w - d1 + gn * d1 / R) (hW2 : 0 < w - d2 + gn * d2 / R) :
    (gn < R → opPAYGWelfare β gn w R d2 < opPAYGWelfare β gn w R d1) ∧
      (R < gn → opPAYGWelfare β gn w R d1 < opPAYGWelfare β gn w R d2) := by
  have hW : ∀ d, w - d + gn * d / R = w - d * (1 - gn / R) := fun d => by ring
  have hmono : ∀ W1 W2, 0 < W1 → W1 < W2 →
      Real.log (W1 / (1 + β)) + β * Real.log (β * R * W1 / (1 + β)) <
        Real.log (W2 / (1 + β)) + β * Real.log (β * R * W2 / (1 + β)) := by
    intro W1 W2 h1 h12
    have a : Real.log (W1 / (1 + β)) < Real.log (W2 / (1 + β)) :=
      Real.log_lt_log (by positivity) (div_lt_div_of_pos_right h12 (by linarith))
    have b : Real.log (β * R * W1 / (1 + β)) < Real.log (β * R * W2 / (1 + β)) :=
      Real.log_lt_log (by positivity)
        (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h12 (by positivity)) (by linarith))
    nlinarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply hmono _ _ hW2
    rw [hW, hW]
    have : 0 < 1 - gn / R := by rw [sub_pos, div_lt_one hR]; exact h
    nlinarith
  · apply hmono _ _ hW1
    rw [hW, hW]
    have : 1 - gn / R < 0 := by rw [sub_neg, one_lt_div hR]; exact h
    nlinarith

/-- **Exercise 16.8(a)(iii)**: steady-state consumption per worker `f(k) − (g_n − 1)k` rises with
`k` below the golden rule and falls above it; since social security lowers `k`
(`ex_16_8_a_ii`), it lowers steady-state consumption when the economy is dynamically efficient
and raises it when it is dynamically inefficient. -/
theorem ex_16_8_a_iii_resources {f fp : ℝ → ℝ} {gn kG : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k)
    (hkG : 0 < kG) (hG : fp kG = gn - 1) :
    (∀ x y, 0 < x → x < y → y ≤ kG → f x - (gn - 1) * x < f y - (gn - 1) * y) ∧
      (∀ x y, kG ≤ x → x < y → f y - (gn - 1) * y < f x - (gn - 1) * x) := by
  have hanti := op_fp_strictAnti hconc hfd
  constructor
  · intro x y hx hxy hy
    have hy0 : 0 < y := by linarith
    have ht := op_strictConcave_tangent hconc (Set.mem_Ici.2 hy0.le) (Set.mem_Ici.2 hx.le)
      hxy.ne (hfd y hy0)
    have : gn - 1 ≤ fp y := by
      rw [← hG]; exact hanti.antitoneOn (show y ∈ Set.Ioi 0 from hy0)
        (show kG ∈ Set.Ioi 0 from hkG) hy
    nlinarith
  · intro x y hx hxy
    have hx0 : 0 < x := by linarith
    have ht := op_strictConcave_tangent hconc (Set.mem_Ici.2 hx0.le)
      (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ y)) hxy.ne' (hfd x hx0)
    have : fp x ≤ gn - 1 := by
      rw [← hG]; exact hanti.antitoneOn (show kG ∈ Set.Ioi 0 from hkG)
        (show x ∈ Set.Ioi 0 from hx0) hx
    nlinarith

/-- **Exercise 16.8(b)** (Miao, p. 558): fully funded social security. The young contribute `d`,
the old receive `Rd`. Optimal private saving is `s = βw/(1 + β) − d` (`op_log_saving` with
incomes `w − d`, `Rd`), so total saving `s + d = βw/(1 + β)` and consumption are unchanged;
with `g_nk_{t+1} = s_t + d_t` the law of motion is that of Exercise 16.4: social security has no
effect on capital or welfare. (Private saving may be negative when `d > βw/(1 + β)`.) -/
theorem ex_16_8_b {β w R d : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    opLogSaving β (w - d) (R * d) R + d = opLogSaving β w 0 R ∧
      w - d - opLogSaving β (w - d) (R * d) R = w - opLogSaving β w 0 R ∧
      R * opLogSaving β (w - d) (R * d) R + R * d = R * opLogSaving β w 0 R := by
  unfold opLogSaving
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ### Exercise 16.9: linearisation of the bubble economy -/

/-- The coefficients of the linearised system at the bubbly steady state `(k_G, b*)`, with
`D = g_n − s_Rf″`: `dk′ = m₁₁dk + m₁₂db`, `db′ = m₂₁dk + db`. -/
noncomputable def opLinM11 (gn sw sR fpp kG bs : ℝ) : ℝ := -fpp * (sw * kG + bs) / (gn - sR * fpp)

noncomputable def opLinM12 (gn sR fpp : ℝ) : ℝ := -gn / (gn - sR * fpp)

noncomputable def opLinM21 (gn fpp bs : ℝ) : ℝ := fpp * bs / gn

/-- **Exercise 16.9** (Miao, p. 558): the linearisation. Taking total differentials of
`g_nk_{t+1} = s(w(k_t), R(k_{t+1})) − R(k_t)b_t` and `g_nb_{t+1} = R(k_t)b_t` at `(k_G, b*)`
(`R = g_n`, `w′ = −k_Gf″`, `R′ = f″`):
`g_ndk′ = −s_wk_Gf″dk + s_Rf″dk′ − f″b*dk − g_ndb` and `g_ndb′ = f″b*dk + g_ndb`. With
`D = g_n − s_Rf″ ≠ 0` these are equivalent to `dk′ = m₁₁dk + m₁₂db`, `db′ = m₂₁dk + db`. -/
theorem ex_16_9_linearization {gn sw sR fpp kG bs dk db dk' db' : ℝ} (hgn : 0 < gn)
    (hD : gn - sR * fpp ≠ 0) :
    (gn * dk' = sw * (-kG * fpp) * dk + sR * fpp * dk' - (fpp * bs * dk + gn * db) ∧
      gn * db' = fpp * bs * dk + gn * db) ↔
      (dk' = opLinM11 gn sw sR fpp kG bs * dk + opLinM12 gn sR fpp * db ∧
        db' = opLinM21 gn fpp bs * dk + 1 * db) := by
  have hD' : gn - fpp * sR ≠ 0 := by rwa [mul_comm]
  have e : opLinM11 gn sw sR fpp kG bs * dk + opLinM12 gn sR fpp * db =
      (-fpp * (sw * kG + bs) * dk - gn * db) / (gn - sR * fpp) := by
    unfold opLinM11 opLinM12; field_simp; ring
  have e2 : opLinM21 gn fpp bs * dk + 1 * db = (fpp * bs * dk + gn * db) / gn := by
    unfold opLinM21; field_simp
  rw [e, e2, eq_div_iff hD, eq_div_iff hgn.ne']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **Exercise 16.9**: with `s_w > 0`, `s_R ≥ 0`, `f″ < 0`, `b* > 0` the characteristic roots
satisfy `0 < λ₁ < 1 < λ₂`: the bubbly steady state is a saddle point (Miao, p. 555). -/
theorem ex_16_9_roots {gn sw sR fpp kG bs : ℝ} (hgn : 0 < gn) (hsw : 0 < sw) (hsR : 0 ≤ sR)
    (hfpp : fpp < 0) (hkG : 0 < kG) (hbs : 0 < bs) :
    cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 1 < 0 ∧
      0 < opLinM12 gn sR fpp * opLinM21 gn fpp bs ∧
      0 < cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 (-1) ∧
      0 < lamLo (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 ∧
      lamLo (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 < 1 ∧
      1 < lamHi (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 := by
  have hD : 0 < gn - sR * fpp := by nlinarith
  have hm : 0 < opLinM12 gn sR fpp * opLinM21 gn fpp bs := by
    unfold opLinM12 opLinM21
    rw [show -gn / (gn - sR * fpp) * (fpp * bs / gn) = (-fpp) * bs / (gn - sR * fpp) by
      field_simp]
    have : 0 < -fpp := by linarith
    positivity
  have hm11 : 0 < opLinM11 gn sw sR fpp kG bs := by
    unfold opLinM11
    have : 0 < -fpp := by linarith
    have : 0 < sw * kG + bs := by positivity
    positivity
  have h1 : cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 1
      < 0 := by
    simp only [cp22]; nlinarith
  have hdet : 0 < cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
      (opLinM21 gn fpp bs) 1 0 := by
    simp only [cp22]
    unfold opLinM11 opLinM12 opLinM21
    rw [show (0 : ℝ) ^ 2 - (-fpp * (sw * kG + bs) / (gn - sR * fpp) + 1) * 0 +
      (-fpp * (sw * kG + bs) / (gn - sR * fpp) * 1 -
        -gn / (gn - sR * fpp) * (fpp * bs / gn)) = (-fpp) * sw * kG / (gn - sR * fpp) by
      field_simp; ring]
    have : 0 < -fpp := by linarith
    positivity
  have hm1 : 0 < cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
      (opLinM21 gn fpp bs) 1 (-1) := by
    simp only [cp22] at hdet ⊢
    nlinarith
  obtain ⟨hlo, hhi⟩ := roots22_lt h1
  have hf := cp22_factor h1 0
  have hlo0 : 0 < lamLo (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
      (opLinM21 gn fpp bs) 1 := by
    rw [hf] at hdet
    nlinarith
  exact ⟨h1, hm, hm1, hlo0, hlo, hhi⟩

/-- **Exercise 16.9** and Miao, p. 555 ("this steady state is a saddle point. For any given
initial value `k₁`, there is a unique `b₁` on the saddle path"), for the linearised system: for
every initial deviation `dk₀` there is a solution converging to the steady state, and every
bounded solution starts on the saddle line `db₀ = κ dk₀`. -/
theorem ex_16_9_saddle {gn sw sR fpp kG bs : ℝ} (hgn : 0 < gn) (hsw : 0 < sw) (hsR : 0 ≤ sR)
    (hfpp : fpp < 0) (hkG : 0 < kG) (hbs : 0 < bs) (dk0 : ℝ) :
    (∃ dk db : ℕ → ℝ, IsSol22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
        (opLinM21 gn fpp bs) 1 dk db ∧ dk 0 = dk0 ∧
        Tendsto dk atTop (𝓝 0) ∧ Tendsto db atTop (𝓝 0)) ∧
      ∀ dk db : ℕ → ℝ, IsSol22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
        (opLinM21 gn fpp bs) 1 dk db → BddSeq dk → BddSeq db →
        db 0 = kSaddle (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
          (opLinM21 gn fpp bs) 1 * dk 0 := by
  obtain ⟨h1, hm, hc, -, -, -⟩ := ex_16_9_roots hgn hsw hsR hfpp hkG hbs
  refine ⟨(saddle22_iff h1 hm).2 hc dk0, fun dk db h hK hB => ?_⟩
  exact (sHi_zero_iff h1 hm dk db 0).1 (sHi_zero_of_bdd h1 h hK hB)

end Miao.OverlappingGenerations
