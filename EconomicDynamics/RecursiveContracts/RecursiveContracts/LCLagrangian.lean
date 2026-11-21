/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.LCDeterministic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The Lagrangian method of Marcet and Marimon (Miao §22.1.2, pp. 778–780)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.2, pp. 778–780, and the
first-best benchmark of p. 775. We work with deterministic endowments (the setting of
Exercise 22.1); the incentive constraint at `t` is `V_t(u(c)) ≥ U_t = V_t(u(y))`, with
multiplier `β^t α_t`, and the participation constraint is `V_0(u(c)) ≥ v₀` with multiplier `φ`.

Proved:
* (22.10): the cumulative multipliers `μ_t = μ_{t-1} + α_t`, `μ_{-1} = 0`, are the partial
  sums of `α` (`eq_22_10`);
* the rewriting of the Lagrangian: `Σ_t β^t α_t V_t(x) = Σ_s β^s μ_s x_s`, exactly for finite
  horizons with a remainder `μ_{T-1} β^T V_T(x)` (`lc_lagrangian_rewrite_finite`) and for the
  infinite horizon when the multipliers are nonnegative with bounded sums
  (`lc_lagrangian_rewrite`);
* the first-order condition `u'(c_t) = 1/(μ_t + φ)` and `−(μ_t + φ) = P_v(y_t, v_t)`
  (`lc_lagrangian_foc`, `lc_multiplier_value_derivative`);
* sufficiency: a feasible plan with nonnegative multipliers, complementary slackness and
  consumption maximising `−c + (μ_t + φ) u(c)` each period is optimal
  (`lc_lagrangian_sufficiency`): "the preceding three equations together with (22.10)
  characterize the solution";
* the first best (p. 775): without incentive constraints constant consumption with
  `u(c̄) = (1 − β) v₀` is optimal (`lc_first_best`).

Departure: the book states the Lagrangian with conditional expectations on the event tree; we
prove the rewriting and the sufficiency theorem for deterministic sequences, the case used in
Exercise 22.1.
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- Miao, (22.10), p. 779: `μ_t = α_0 + ⋯ + α_t`, the cumulative multiplier. -/
def lc_cumMult (α : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ Finset.range (t + 1), α s

/-- Miao, (22.10), p. 779: `μ_t = μ_{t-1} + α_t` with `μ_{-1} = 0`. -/
theorem eq_22_10 (α : ℕ → ℝ) :
    lc_cumMult α 0 = 0 + α 0 ∧ ∀ t, lc_cumMult α (t + 1) = lc_cumMult α t + α (t + 1) := by
  refine ⟨by simp [lc_cumMult], fun t => ?_⟩
  unfold lc_cumMult
  rw [Finset.sum_range_succ]

/-- Swapping the order of summation in the triangle `t ≤ s < T`. -/
theorem lc_triangle_swap (α z : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, α t * ∑ s ∈ Finset.Ico t T, z s =
      ∑ s ∈ Finset.range T, z s * lc_cumMult α s := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : ∀ t ∈ Finset.range (T + 1), α t * ∑ s ∈ Finset.Ico t (T + 1), z s =
        α t * ∑ s ∈ Finset.Ico t T, z s + α t * z T := by
      intro t ht
      rw [Finset.sum_Ico_succ_top (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)), mul_add]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      Finset.sum_range_succ (fun t => α t * ∑ s ∈ Finset.Ico t T, z s),
      Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero, ih,
      Finset.sum_range_succ (fun s => z s * lc_cumMult α s), ← Finset.sum_mul]
    unfold lc_cumMult
    ring

/-- Miao, p. 779, the rewriting of the Lagrangian, finite-horizon form:
`Σ_{t<T} β^t α_t V_t(x) = Σ_{s<T} β^s μ_s x_s + μ_{T-1} β^T V_T(x)`. -/
theorem lc_lagrangian_rewrite_finite {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (α : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, β ^ t * α t * lc_detValue β x t =
      ∑ s ∈ Finset.range T, β ^ s * lc_cumMult α s * x s +
        (∑ t ∈ Finset.range T, α t) * (β ^ T * lc_detValue β x T) := by
  have hsplit : ∀ t ∈ Finset.range T, β ^ t * α t * lc_detValue β x t =
      α t * ∑ s ∈ Finset.Ico t T, β ^ s * x s + α t * (β ^ T * lc_detValue β x T) := by
    intro t ht
    have htT : t ≤ T := (Finset.mem_range.mp ht).le
    rw [lc_detValue_split hβ0 hβ1 hx t (T - t), Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel' htT]
    have hT : β ^ T = β ^ t * β ^ (T - t) := by rw [← pow_add, Nat.add_sub_cancel' htT]
    rw [hT, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add]; ring
    · ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, lc_triangle_swap, ← Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Miao, p. 779, the rewriting of the Lagrangian:
`Σ_t β^t α_t E_t[Σ_{s ≥ t} β^{s-t} u(c_s)] = Σ_t β^t μ_t u(c_t)`, for nonnegative multipliers
with bounded cumulative sums and a bounded utility sequence `x`. -/
theorem lc_lagrangian_rewrite {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (α : ℕ → ℝ) (hα : ∀ t, 0 ≤ α t) {K : ℝ}
    (hK : ∀ t, lc_cumMult α t ≤ K) :
    ∑' t, β ^ t * α t * lc_detValue β x t = ∑' s, β ^ s * lc_cumMult α s * x s := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hx 0)
  have h1 : 0 < 1 - β := by linarith
  have hpart : ∀ T, ∑ t ∈ Finset.range T, α t ≤ K := by
    intro T
    cases T with
    | zero => simpa using (Finset.sum_nonneg fun t _ => hα t).trans (hK 0)
    | succ T => exact hK T
  have hK0 : 0 ≤ K := (Finset.sum_nonneg fun t _ => hα t).trans (hpart 0)
  have hμ : ∀ s, |lc_cumMult α s| ≤ K := fun s => by
    rw [abs_of_nonneg (show 0 ≤ lc_cumMult α s from Finset.sum_nonneg fun t _ => hα t)]
    exact hK s
  have hαs : Summable α := summable_of_sum_range_le hα hpart
  have hV := lc_detValue_abs_le hβ0 hβ1 hx
  have hL : Summable fun t => β ^ t * α t * lc_detValue β x t := by
    refine Summable.of_norm_bounded (hαs.mul_left (M / (1 - β))) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), abs_of_nonneg (hα t)]
    have := pow_le_one₀ hβ0 hβ1.le (n := t)
    calc β ^ t * α t * |lc_detValue β x t| ≤ 1 * α t * (M / (1 - β)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right this (hα t)) (hV t) (abs_nonneg _)
            (by rw [one_mul]; exact hα t)
      _ = M / (1 - β) * α t := by ring
  have hR : Summable fun s => β ^ s * lc_cumMult α s * x s := by
    have := lc_summable_geom hβ0 hβ1 (x := fun s => lc_cumMult α s * x s) (M := K * M)
      (fun s => by rw [abs_mul]; exact mul_le_mul (hμ s) (hx s) (abs_nonneg _) hK0)
    simpa only [mul_assoc] using this
  have hrem : Tendsto (fun T => (∑ t ∈ Finset.range T, α t) * (β ^ T * lc_detValue β x T))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun T => K * (M / (1 - β)) * β ^ T) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T),
        abs_of_nonneg (Finset.sum_nonneg fun t _ => hα t)]
      calc (∑ t ∈ Finset.range T, α t) * (β ^ T * |lc_detValue β x T|) ≤
            K * (β ^ T * (M / (1 - β))) := by
            gcongr
            · exact hpart T
            · exact hV T
        _ = K * (M / (1 - β)) * β ^ T := by ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul (K * (M / (1 - β)))
  have hlim := (hR.hasSum.tendsto_sum_nat).add hrem
  rw [add_zero] at hlim
  have hlim' := hL.hasSum.tendsto_sum_nat
  have heq : (fun T => ∑ t ∈ Finset.range T, β ^ t * α t * lc_detValue β x t) =
      fun T => ∑ s ∈ Finset.range T, β ^ s * lc_cumMult α s * x s +
        (∑ t ∈ Finset.range T, α t) * (β ^ T * lc_detValue β x T) := by
    funext T; exact lc_lagrangian_rewrite_finite hβ0 hβ1 hx α T
  rw [heq] at hlim'
  exact tendsto_nhds_unique hlim' hlim

/-- Miao, p. 779: the first-order condition for `c_t` in the rewritten Lagrangian: the
derivative of `(y_t − c) + (μ_t + φ) u(c)` is `−1 + (μ_t + φ) u'(c)`, which vanishes iff
`u'(c_t) = 1/(μ_t + φ)`. -/
theorem lc_lagrangian_foc {u : ℝ → ℝ} {c du : ℝ} (hu : HasDerivAt u du c) (y m : ℝ)
    (hm : m ≠ 0) :
    HasDerivAt (fun c' => y - c' + m * u c') (-1 + m * du) c ∧
      (-1 + m * du = 0 ↔ du = 1 / m) := by
  refine ⟨?_, ?_⟩
  · have := ((hasDerivAt_id c).const_sub y).add (hu.const_mul m)
    simp only [id] at this
    exact this
  · constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring

/-- Miao, p. 779: "`−(μ_t + φ)` is equal to `P_v(y_t, v_t)`": combining the first-order condition
`u'(c_t) = 1/(μ_t + φ)` with the envelope condition (22.8) `P_v = −1/u'(c_t)`. -/
theorem lc_multiplier_value_derivative {du m pv : ℝ} (hm : m ≠ 0) (hfoc : du = 1 / m)
    (henv : pv = -1 / du) : pv = -m := by
  rw [henv, hfoc]
  field_simp

/-- The agent's autarky values `U_t = V_t(u(y))` (Exercise 22.1, p. 797). -/
noncomputable def lc_detU (β : ℝ) (u : ℝ → ℝ) (y : ℕ → ℝ) (t : ℕ) : ℝ :=
  lc_detValue β (fun s => u (y s)) t

/-- The principal's value `Σ_t β^t (y_t − c_t)` (Miao, p. 775). -/
noncomputable def lc_detPrincipal (β : ℝ) (y c : ℕ → ℝ) : ℝ := ∑' t, β ^ t * (y t - c t)

/-- Feasible plans of the deterministic problem (Miao, (22.1)–(22.2), p. 775, and Exercise 22.1,
p. 797): positive bounded consumption with bounded utility, the incentive constraints
`V_t(u(c)) ≥ U_t` at every date and participation `V_0(u(c)) ≥ v₀`. -/
def lc_detFeasible (β : ℝ) (u : ℝ → ℝ) (y : ℕ → ℝ) (v₀ : ℝ) (c : ℕ → ℝ) : Prop :=
  (∀ t, 0 < c t) ∧ (∃ K, ∀ t, |c t| ≤ K ∧ |u (c t)| ≤ K) ∧
    (∀ t, lc_detU β u y t ≤ lc_detValue β (fun s => u (c s)) t) ∧
    v₀ ≤ lc_detValue β (fun s => u (c s)) 0

/-- Miao, p. 780, sufficiency of the Lagrangian conditions: let `c*` be feasible, `α_t ≥ 0`,
`φ ≥ 0` with complementary slackness, `μ_t` (22.10) bounded, and let `c*_t` maximise
`−c + (μ_t + φ) u(c)` over `c > 0` (the first-order condition for concave `u`). Then `c*`
maximises the principal's value among feasible plans. -/
theorem lc_lagrangian_sufficiency {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    {y : ℕ → ℝ} (hy : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) {v₀ : ℝ} {cs : ℕ → ℝ}
    (hcs : lc_detFeasible β u y v₀ cs) (α : ℕ → ℝ) (hα : ∀ t, 0 ≤ α t) {φ : ℝ} (hφ : 0 ≤ φ)
    (hCS : ∀ t, α t * (lc_detValue β (fun s => u (cs s)) t - lc_detU β u y t) = 0)
    (hCSφ : φ * (lc_detValue β (fun s => u (cs s)) 0 - v₀) = 0) {Kμ : ℝ}
    (hKμ : ∀ t, lc_cumMult α t ≤ Kμ)
    (hmax : ∀ t, ∀ x, 0 < x → -x + (lc_cumMult α t + φ) * u x ≤
      -cs t + (lc_cumMult α t + φ) * u (cs t))
    {c : ℕ → ℝ} (hc : lc_detFeasible β u y v₀ c) :
    lc_detPrincipal β y c ≤ lc_detPrincipal β y cs := by
  obtain ⟨Ky, hKy⟩ := hy
  obtain ⟨hcs0, ⟨K1, hK1⟩, hcsIC, _⟩ := hcs
  obtain ⟨hc0, ⟨K2, hK2⟩, hcIC, hcPK⟩ := hc
  set K := K1 + K2 + Ky with hKdef
  have hK10 : 0 ≤ K1 := (abs_nonneg _).trans (hK1 0).1
  have hK20 : 0 ≤ K2 := (abs_nonneg _).trans (hK2 0).1
  have hKy0 : 0 ≤ Ky := (abs_nonneg _).trans (hKy 0).1
  have huc : ∀ t, |u (c t)| ≤ K := fun t => by linarith [(hK2 t).2]
  have hucs : ∀ t, |u (cs t)| ≤ K := fun t => by linarith [(hK1 t).2]
  set d : ℕ → ℝ := fun s => u (c s) - u (cs s) with hd
  set e : ℕ → ℝ := fun s => cs s - c s with he
  have hdK : ∀ s, |d s| ≤ 2 * K := fun s => (abs_sub _ _).trans (by linarith [huc s, hucs s])
  have heK : ∀ s, |e s| ≤ 2 * K := fun s =>
    (abs_sub _ _).trans (by linarith [(hK1 s).1, (hK2 s).1])
  have hVd : ∀ t, lc_detValue β d t =
      lc_detValue β (fun s => u (c s)) t - lc_detValue β (fun s => u (cs s)) t :=
    lc_detValue_sub hβ0 hβ1 huc hucs
  have hPdiff : lc_detPrincipal β y c - lc_detPrincipal β y cs = lc_detValue β e 0 := by
    unfold lc_detPrincipal lc_detValue
    have hyc : ∀ t, |y t - c t| ≤ Ky + K2 := fun t =>
      (abs_sub _ _).trans (add_le_add (hKy t).1 (hK2 t).1)
    have hycs : ∀ t, |y t - cs t| ≤ Ky + K1 := fun t =>
      (abs_sub _ _).trans (add_le_add (hKy t).1 (hK1 t).1)
    rw [← (lc_summable_geom hβ0 hβ1 hyc).tsum_sub (lc_summable_geom hβ0 hβ1 hycs)]
    refine tsum_congr fun t => ?_
    simp only [he, zero_add]
    ring
  have hμ0 : ∀ t, 0 ≤ lc_cumMult α t := fun t => Finset.sum_nonneg fun s _ => hα s
  have hKμ0 : 0 ≤ Kμ := (hμ0 0).trans (hKμ 0)
  have hpart : ∀ T, ∑ t ∈ Finset.range T, α t ≤ Kμ := by
    intro T
    cases T with
    | zero => simpa using hKμ0
    | succ T => exact hKμ T
  -- the bound for every horizon
  set R : ℕ → ℝ := fun T => β ^ T * lc_detValue β e T +
    ((∑ t ∈ Finset.range T, α t) + φ) * (β ^ T * lc_detValue β d T) with hR
  have hbound : ∀ T, lc_detValue β e 0 ≤ R T := by
    intro T
    have hIC : 0 ≤ ∑ t ∈ Finset.range T, β ^ t * α t * lc_detValue β d t := by
      refine Finset.sum_nonneg fun t _ => ?_
      have h1 := hCS t
      have h2 : α t * (lc_detValue β (fun s => u (c s)) t - lc_detU β u y t) ≥ 0 :=
        mul_nonneg (hα t) (by linarith [hcIC t])
      rw [hVd t]
      have : α t * (lc_detValue β (fun s => u (c s)) t -
          lc_detValue β (fun s => u (cs s)) t) ≥ 0 := by nlinarith
      have := mul_nonneg (pow_nonneg hβ0 t) this
      linarith
    have hPK : 0 ≤ φ * lc_detValue β d 0 := by
      rw [hVd 0]
      nlinarith
    rw [lc_lagrangian_rewrite_finite hβ0 hβ1 hdK α T] at hIC
    rw [lc_detValue_split0 hβ0 hβ1 hdK T] at hPK
    rw [lc_detValue_split0 hβ0 hβ1 heK T]
    have hpt : ∑ s ∈ Finset.range T, β ^ s * e s +
        (∑ s ∈ Finset.range T, β ^ s * lc_cumMult α s * d s +
          φ * ∑ s ∈ Finset.range T, β ^ s * d s) ≤ 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_nonpos fun s _ => ?_
      have := hmax s (c s) (hc0 s)
      have h : e s + (lc_cumMult α s + φ) * d s ≤ 0 := by simp only [he, hd]; linarith
      have := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 s) h
      linarith
    simp only [hR]
    nlinarith
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have hVe := lc_detValue_abs_le hβ0 hβ1 heK
    have hVd' := lc_detValue_abs_le hβ0 hβ1 hdK
    refine squeeze_zero_norm (a := fun T => (2 * K / (1 - β) + (Kμ + φ) * (2 * K / (1 - β))) *
      β ^ T) (fun T => ?_) ?_
    · have hs0 : 0 ≤ ∑ t ∈ Finset.range T, α t := Finset.sum_nonneg fun t _ => hα t
      rw [Real.norm_eq_abs]
      simp only [hR]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T),
        abs_of_nonneg (add_nonneg hs0 hφ)]
      have hb1 : β ^ T * |lc_detValue β e T| ≤ β ^ T * (2 * K / (1 - β)) :=
        mul_le_mul_of_nonneg_left (hVe T) (pow_nonneg hβ0 T)
      have hb2 : ((∑ t ∈ Finset.range T, α t) + φ) * (β ^ T * |lc_detValue β d T|) ≤
          (Kμ + φ) * (β ^ T * (2 * K / (1 - β))) := by
        gcongr
        · exact hpart T
        · exact hVd' T
      nlinarith
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul
        (2 * K / (1 - β) + (Kμ + φ) * (2 * K / (1 - β)))
  have := ge_of_tendsto' hRlim hbound
  linarith

/-- Miao, p. 775, the first best: without incentive constraints, constant consumption `c̄` with
`u(c̄) = (1 − β) v₀` minimises the cost `Σ β^t c_t` among bounded positive plans with
`V_0(u(c)) ≥ v₀`, for concave `u` with derivative `du(c̄) > 0` (supporting line). The
risk-neutral principal fully insures the agent. -/
theorem lc_first_best {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} {cbar du v₀ : ℝ}
    (hdu : 0 < du) (hsupp : ∀ x, 0 < x → u x ≤ u cbar + du * (x - cbar))
    (hcbar : u cbar = (1 - β) * v₀) {c : ℕ → ℝ} (hc0 : ∀ t, 0 < c t) {K : ℝ}
    (hK : ∀ t, |c t| ≤ K ∧ |u (c t)| ≤ K) (hPK : v₀ ≤ lc_detValue β (fun s => u (c s)) 0) :
    ∑' t, β ^ t * cbar ≤ ∑' t, β ^ t * c t := by
  have h1 : 0 < 1 - β := by linarith
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0).1
  have hc' : ∀ t, |c t - cbar| ≤ K + |cbar| := fun t =>
    (abs_sub _ _).trans (add_le_add (hK t).1 le_rfl)
  have hu' : ∀ t, |u (c t) - u cbar| ≤ K + |u cbar| := fun t =>
    (abs_sub _ _).trans (add_le_add (hK t).2 le_rfl)
  have hineq : ∀ t, (u (c t) - u cbar) / du ≤ c t - cbar := by
    intro t
    rw [div_le_iff₀ hdu]
    linarith [hsupp (c t) (hc0 t)]
  have hsum := Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (hineq t)
    (pow_nonneg hβ0 t)) ((lc_summable_geom hβ0 hβ1 hu').div_const du |>.congr fun t => by ring)
    (lc_summable_geom hβ0 hβ1 hc')
  have hb1 : ∀ t, |u (c t)| ≤ K + |u cbar| := fun t => by linarith [(hK t).2, abs_nonneg (u cbar)]
  have hb2 : ∀ _t : ℕ, |u cbar| ≤ K + |u cbar| := fun _ => by linarith
  have hV : ∑' t, β ^ t * ((u (c t) - u cbar) / du) =
      (lc_detValue β (fun s => u (c s)) 0 - v₀) / du := by
    have := lc_detValue_sub hβ0 hβ1 hb1 (b := fun _ => u cbar) hb2 0
    have hconst : lc_detValue β (fun _ => u cbar) 0 = v₀ := by
      rw [lc_detValue_const hβ0 hβ1, hcbar]; field_simp
    rw [hconst] at this
    rw [← this, lc_detValue, ← tsum_div_const]
    refine tsum_congr fun t => ?_
    rw [zero_add]
    ring
  have hdiff : ∑' t, β ^ t * c t - ∑' t, β ^ t * cbar = ∑' t, β ^ t * (c t - cbar) := by
    rw [← (lc_summable_geom hβ0 hβ1 (fun t => (hK t).1)).tsum_sub
      (lc_summable_geom hβ0 hβ1 (x := fun _ => cbar) (fun _ => le_rfl))]
    exact tsum_congr fun t => by ring
  have hnn : 0 ≤ (lc_detValue β (fun s => u (c s)) 0 - v₀) / du := div_nonneg (by linarith) hdu.le
  linarith

end Miao.RecursiveContracts
