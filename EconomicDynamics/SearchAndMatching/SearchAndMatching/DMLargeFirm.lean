/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMBellman
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# §18.1: large firms

Miao, §18.1, "Large Firms", pp. 596–598, equations (18.22)–(18.27).

* `dm_firmProfit`, `dm_FirmFeasible`, `dm_FirmOptimal`: the firm's problem
  `max Σ βᵗ(F_t(N_t) − w_tN_t − κv_t)` subject to (18.22) `N_{t+1} = (1 − ρ)N_t + q^v_tv_t`,
  `v_t ≥ 0`. Departure: optimality is against plans that differ in finitely many periods (the
  comparison of the infinite sums reduces to a finite sum). `F_t(N) = AN` in the book; a general
  differentiable `F_t` is allowed (it is used in Exercise 18.1).
* `dm_firm_euler`: an optimal plan with positive vacancies at `t, t + 1` satisfies
  `κ/q^v_t = β(F′_{t+1}(N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`; with `F_t(N) = AN` this is
  (18.8) (`dm_largeFirm_eq_18_8`). Proof: a one-period perturbation of `N_{t+1}` financed by
  `v_t`, `v_{t+1}`, and Fermat's theorem.
* `dm_firmOptimal_of_euler`: conversely, when (18.8) holds every feasible plan is optimal (the
  firm is indifferent over vacancies: (18.23) plays the role of free entry); with
  `dm_firmOptimal_exists` this shows `dm_FirmOptimal` is satisfiable.
* `eq_18_23`: combining the first-order conditions (18.23) gives (18.8).
* `dm_aggregate_18_2`: aggregating (18.22) over a unit measure of firms gives (18.2).
* `eq_18_24`: with an affine continuation value and the vacancy first-order condition, the
  Bellman right side is independent of `v` and `∂J_t/∂N = A − w_t + (1 − ρ)κ/q^v_t = J^F_t`.
* `dm_Jn`: the marginal value of `ε` extra workers paid `w`, `J_n(w, t) = (w_t − w) + ∂J_t/∂N`
  (18.25).
* `eq_18_26`, `eq_18_27`: the large-firm bargaining problems are equivalent to (18.11).
-/

namespace Miao.SearchAndMatching

open Filter Topology MeasureTheory

/-- Miao, p. 597: the large firm's period profit `F_t(N_t) − w_tN_t − κv_t`. -/
def dm_firmProfit (F : ℕ → ℝ → ℝ) (w : ℕ → ℝ) (κ : ℝ) (N v : ℕ → ℝ) (t : ℕ) : ℝ :=
  F t (N t) - w t * N t - κ * v t

/-- Miao, (18.22), p. 596: a feasible employment–vacancy plan. -/
def dm_FirmFeasible (ρ : ℝ) (qv N v : ℕ → ℝ) : Prop :=
  ∀ t, N (t + 1) = (1 - ρ) * N t + qv t * v t ∧ 0 ≤ v t

/-- Miao, p. 597: an optimal plan of the large firm: feasible, and no feasible plan with the same
`N₀` that coincides with it from some date `T` on yields a higher discounted profit. -/
def dm_FirmOptimal (F : ℕ → ℝ → ℝ) (w : ℕ → ℝ) (κ β ρ : ℝ) (qv N v : ℕ → ℝ) : Prop :=
  dm_FirmFeasible ρ qv N v ∧ ∀ (T : ℕ) (N' v' : ℕ → ℝ), dm_FirmFeasible ρ qv N' v' →
    N' 0 = N 0 → (∀ t, T ≤ t → N' t = N t ∧ v' t = v t) →
      ∑ t ∈ Finset.range T, β ^ t * dm_firmProfit F w κ N' v' t ≤
        ∑ t ∈ Finset.range T, β ^ t * dm_firmProfit F w κ N v t

/-- Miao, (18.23), p. 597: an optimal plan of the large firm with `v_t, v_{t+1} > 0` satisfies
the job creation (Euler) equation `κ/q^v_t = β(F′_{t+1}(N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`.
-/
theorem dm_firm_euler {F : ℕ → ℝ → ℝ} {w qv N v : ℕ → ℝ} {κ β ρ Fn : ℝ}
    (hopt : dm_FirmOptimal F w κ β ρ qv N v) (t : ℕ) (hβ : 0 < β) (hq : 0 < qv t)
    (hq1 : 0 < qv (t + 1)) (hv : 0 < v t) (hv1 : 0 < v (t + 1))
    (hF : HasDerivAt (F (t + 1)) Fn (N (t + 1))) :
    κ / qv t = β * (Fn - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  set N' : ℝ → ℕ → ℝ := fun ε s ↦ N s + if s = t + 1 then ε else 0 with hN'
  set v' : ℝ → ℕ → ℝ := fun ε s ↦ v s + (if s = t then ε / qv t else 0) -
    (if s = t + 1 then (1 - ρ) * ε / qv (t + 1) else 0) with hv'
  set φ : ℝ → ℝ := fun ε ↦ β ^ t * -(κ * ε / qv t) + β ^ (t + 1) *
    (F (t + 1) (N (t + 1) + ε) - F (t + 1) (N (t + 1)) - w (t + 1) * ε +
      κ * ((1 - ρ) * ε / qv (t + 1))) with hφ
  have ht1 : t ≠ t + 1 := by omega
  have ht2 : t + 1 ≠ t := by omega
  have ht3 : t + 1 + 1 ≠ t + 1 := by omega
  -- the deviation changes the finite sum by `φ ε`
  have hsum : ∀ ε, ∑ s ∈ Finset.range (t + 1 + 1), β ^ s * dm_firmProfit F w κ (N' ε) (v' ε) s =
      ∑ s ∈ Finset.range (t + 1 + 1), β ^ s * dm_firmProfit F w κ N v s + φ ε := by
    intro ε
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
      Finset.sum_range_succ]
    have hlow : ∑ s ∈ Finset.range t, β ^ s * dm_firmProfit F w κ (N' ε) (v' ε) s =
        ∑ s ∈ Finset.range t, β ^ s * dm_firmProfit F w κ N v s := by
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      have hs' := Finset.mem_range.mp hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [dm_firmProfit, hN', hv', h1, h2]
    rw [hlow]
    generalize ∑ s ∈ Finset.range t, β ^ s * dm_firmProfit F w κ N v s = S
    simp only [dm_firmProfit, hN', hv', hφ, ht1, ht2, ↓reduceIte, add_zero, sub_zero]
    ring
  -- the deviation is feasible for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < v t + ε / qv t ∧
      0 < v (t + 1) - (1 - ρ) * ε / qv (t + 1) := by
    have c1 : ContinuousAt (fun ε : ℝ ↦ v t + ε / qv t) 0 := by fun_prop
    have c2 : ContinuousAt (fun ε : ℝ ↦ v (t + 1) - (1 - ρ) * ε / qv (t + 1)) 0 := by fun_prop
    have e1 := c1.eventually (lt_mem_nhds (show (0 : ℝ) < v t + 0 / qv t by simpa using hv))
    have e2 := c2.eventually
      (lt_mem_nhds (show (0 : ℝ) < v (t + 1) - (1 - ρ) * 0 / qv (t + 1) by simpa using hv1))
    filter_upwards [e1, e2] with ε h1 h2 using ⟨h1, h2⟩
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hev] with ε hε
    have hφ0 : φ 0 = 0 := by simp [hφ]
    rw [hφ0]
    have hfe : dm_FirmFeasible ρ qv (N' ε) (v' ε) := by
      intro s
      rcases eq_or_ne s t with rfl | hst
      · refine ⟨?_, ?_⟩
        · simp only [hN', hv', ht1, ↓reduceIte, add_zero, sub_zero]
          rw [(hfeas s).1]
          field_simp
          ring
        · simp only [hv', ht1, ↓reduceIte, sub_zero]; exact hε.1.le
      rcases eq_or_ne s (t + 1) with rfl | hst1
      · refine ⟨?_, ?_⟩
        · simp only [hN', hv', ht2, ht3, ↓reduceIte, add_zero]
          rw [(hfeas (t + 1)).1]
          field_simp
          ring
        · simp only [hv', ht2, ↓reduceIte, add_zero]; exact hε.2.le
      · have h1 : s + 1 ≠ t + 1 := by omega
        simp only [hN', hv', hst, hst1, h1, ↓reduceIte, add_zero, sub_zero]
        exact hfeas s
    have h0 : N' ε 0 = N 0 := by simp [hN']
    have hag : ∀ s, t + 1 + 1 ≤ s → N' ε s = N s ∧ v' ε s = v s := by
      intro s hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [hN', hv', h1, h2]
    have := hbest (t + 1 + 1) (N' ε) (v' ε) hfe h0 hag
    rw [hsum ε] at this
    linarith
  -- Fermat's theorem
  have h2 : HasDerivAt (fun ε : ℝ ↦ N (t + 1) + ε) 1 0 := (hasDerivAt_id' 0).const_add _
  have hF' : HasDerivAt (F (t + 1)) Fn (N (t + 1) + 0) := by rwa [add_zero]
  have hFc : HasDerivAt (fun ε ↦ F (t + 1) (N (t + 1) + ε)) (Fn * 1) 0 := hF'.comp 0 h2
  have hid := hasDerivAt_id' (0 : ℝ)
  have hd : HasDerivAt φ (β ^ t * -(κ * 1 / qv t) + β ^ (t + 1) *
      (Fn * 1 - w (t + 1) * 1 + κ * ((1 - ρ) * 1 / qv (t + 1)))) 0 :=
    (((hid.const_mul κ).div_const (qv t)).neg.const_mul (β ^ t)).add
      ((((hFc.sub_const (F (t + 1) (N (t + 1)))).sub (hid.const_mul (w (t + 1)))).add
        (((hid.const_mul (1 - ρ)).div_const (qv (t + 1))).const_mul κ)).const_mul (β ^ (t + 1)))
  have hz := hmax.hasDerivAt_eq_zero hd
  have hbt : 0 < β ^ t := pow_pos hβ t
  have key : β ^ t * (β * (Fn - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) - κ / qv t) = 0 := by
    rw [pow_succ] at hz
    linear_combination hz
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- Miao, p. 597: for the large firm with `F_t(N) = AN`, an optimal plan with positive vacancies
satisfies (18.8), "identical to" the small-firm job creation equation. -/
theorem dm_largeFirm_eq_18_8 {w qv N v : ℕ → ℝ} {A κ β ρ : ℝ}
    (hopt : dm_FirmOptimal (fun _ n ↦ A * n) w κ β ρ qv N v) (t : ℕ) (hβ : 0 < β)
    (hq : 0 < qv t) (hq1 : 0 < qv (t + 1)) (hv : 0 < v t) (hv1 : 0 < v (t + 1)) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) :=
  dm_firm_euler hopt t hβ hq hq1 hv hv1 (by simpa using (hasDerivAt_id' (N (t + 1))).const_mul A)

/-- Miao, p. 597: conversely, if (18.8) holds at every date, every feasible plan of the large
firm (with `F_t(N) = AN`) is optimal: the firm is indifferent over its vacancies, and (18.23)
determines aggregate vacancies as the free entry condition (18.6) does. -/
theorem dm_firmOptimal_of_euler {w qv N v : ℕ → ℝ} {A κ β ρ : ℝ} (hq : ∀ t, qv t ≠ 0)
    (h8 : ∀ t, κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)))
    (hfeas : dm_FirmFeasible ρ qv N v) :
    dm_FirmOptimal (fun _ n ↦ A * n) w κ β ρ qv N v := by
  refine ⟨hfeas, fun T N' v' hfeas' h0 hag ↦ le_of_eq ?_⟩
  set D : ℕ → ℝ := fun s ↦ β ^ s * (A - w s + (1 - ρ) * κ / qv s) * (N' s - N s) with hD
  have hterm : ∀ s, β ^ s * dm_firmProfit (fun _ n ↦ A * n) w κ N' v' s =
      β ^ s * dm_firmProfit (fun _ n ↦ A * n) w κ N v s + (D s - D (s + 1)) := by
    intro s
    have hk' : κ * v' s = κ / qv s * (N' (s + 1) - (1 - ρ) * N' s) := by
      rw [(hfeas' s).1]; field_simp [hq s]; ring
    have hk : κ * v s = κ / qv s * (N (s + 1) - (1 - ρ) * N s) := by
      rw [(hfeas s).1]; field_simp [hq s]; ring
    simp only [dm_firmProfit, hD]
    rw [pow_succ]
    linear_combination (-β ^ s) * hk' + β ^ s * hk + (-β ^ s * (N' (s + 1) - N (s + 1))) * h8 s
  rw [Finset.sum_congr rfl fun s _ ↦ hterm s, Finset.sum_add_distrib, Finset.sum_range_sub']
  have hD0 : D 0 = 0 := by simp [hD, h0]
  have hDT : D T = 0 := by simp [hD, (hag T le_rfl).1]
  rw [hD0, hDT, sub_zero, add_zero]

/-- Miao, p. 597: an optimal large-firm plan exists: in the steady state of a search equilibrium
(constant `w`, `q^v` satisfying (18.8)), the constant plan `N_t = N`, `v_t = ρN/q^v` is
optimal. -/
theorem dm_firmOptimal_exists {A κ β ρ w qv N : ℝ} (hq : 0 < qv) (hρ : 0 ≤ ρ) (hN : 0 ≤ N)
    (h8 : κ / qv = β * (A - w + (1 - ρ) * κ / qv)) :
    dm_FirmOptimal (fun _ n ↦ A * n) (fun _ ↦ w) κ β ρ (fun _ ↦ qv) (fun _ ↦ N)
      (fun _ ↦ ρ * N / qv) := by
  refine dm_firmOptimal_of_euler (fun _ ↦ hq.ne') (fun _ ↦ h8) fun t ↦ ⟨?_, by positivity⟩
  field_simp
  ring

/-- Miao, (18.23), p. 597: the first-order conditions `−κ + μ_tq^v_t = 0` (for `v_t`) and
`(A − w_{t+1}) + μ_{t+1}(1 − ρ) − β^{−1}μ_t = 0` (for `N_{t+1}`) combine to (18.8). -/
theorem eq_18_23 {A κ β ρ : ℝ} {w qv μ : ℕ → ℝ} (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0)
    (hv : ∀ t, -κ + μ t * qv t = 0)
    (hN : ∀ t, (A - w (t + 1)) + μ (t + 1) * (1 - ρ) - β⁻¹ * μ t = 0) (t : ℕ) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  have hμ : ∀ s, μ s = κ / qv s := fun s ↦ by
    have := hv s; field_simp [hq s]; linarith
  have h := hN t
  rw [hμ t, hμ (t + 1)] at h
  field_simp at h ⊢
  linear_combination (-1 : ℝ) * h

/-- Miao, p. 597: aggregating the firm-level law of motion (18.22) over a unit measure of firms,
with `q^v_t = q(θ_t)`, `θ_t = v_t/u_t` (aggregate vacancies `v_t = ∫ v^j_t`), gives the aggregate
law of motion (18.2) `N_{t+1} = (1 − ρ)N_t + M(u_t, v_t)`. -/
theorem dm_aggregate_18_2 (MF : DMMatchingFn) {J : Type*} [MeasurableSpace J] (μJ : Measure J)
    {ρ qv u : ℝ} {Nt Nt1 vt : J → ℝ} (hNi : Integrable Nt μJ) (hvi : Integrable vt μJ)
    (hj : ∀ j, Nt1 j = (1 - ρ) * Nt j + qv * vt j) (hu : 0 < u) (hv : 0 < ∫ j, vt j ∂μJ)
    (hqv : qv = dm_q MF ((∫ j, vt j ∂μJ) / u)) :
    ∫ j, Nt1 j ∂μJ = (1 - ρ) * ∫ j, Nt j ∂μJ + MF.M u (∫ j, vt j ∂μJ) := by
  have e : Nt1 = fun j ↦ (1 - ρ) * Nt j + qv * vt j := funext hj
  rw [e, integral_add (hNi.const_mul _) (hvi.const_mul _), integral_const_mul,
    integral_const_mul, dm_M_eq_mul_q MF hu hv, hqv]
  ring

/-- Miao, (18.24), p. 597: if the continuation value is affine, `J_{t+1}(N) = j_{t+1}N + c_{t+1}`,
and the vacancy first-order condition `κ = βj_{t+1}q^v_t` holds, then the Bellman right side
`AN − w_tN − vκ + βJ_{t+1}((1 − ρ)N + q^v_tv)` does not depend on `v` and equals
`(A − w_t + (1 − ρ)κ/q^v_t)N + βc_{t+1}`; so `J_t` is affine with
`∂J_t/∂N = A − w_t + (1 − ρ)μ_t = A − w_t + (1 − ρ)κ/q^v_t`, `μ_t = βj_{t+1}`, which is `J^F_t` by
(18.7). -/
theorem eq_18_24 {A κ β ρ w qv jn cn : ℝ} (hfoc : κ = β * jn * qv) (hq : qv ≠ 0) (N v : ℝ) :
    A * N - w * N - v * κ + β * (jn * ((1 - ρ) * N + qv * v) + cn) =
        (A - w + (1 - ρ) * κ / qv) * N + β * cn ∧
      A - w + (1 - ρ) * (β * jn) = A - w + (1 - ρ) * κ / qv ∧
      HasDerivAt (fun n ↦ (A - w + (1 - ρ) * κ / qv) * n + β * cn)
        (A - w + (1 - ρ) * κ / qv) N := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hfoc]; field_simp; ring
  · rw [hfoc]; field_simp
  · simpa using ((hasDerivAt_id' N).const_mul (A - w + (1 - ρ) * κ / qv)).add_const (β * cn)

/-- Miao, (18.25) and p. 598: with `ε` additional workers paid `w`, the Bellman right side is
`A(N + ε) − w_tN − wε − vκ + βJ_{t+1}((1 − ρ)(N + ε) + q^v_tv)`, and its derivative at `ε = 0`
is `A − w + (1 − ρ)βj_{t+1} = (w_t − w) + ∂J_t/∂N ≡ J_n(w, t)`. -/
theorem dm_Jn {A κ β ρ wt w qv jn cn N v : ℝ} (hfoc : κ = β * jn * qv) (hq : qv ≠ 0) :
    HasDerivAt (fun ε ↦ A * (N + ε) - wt * N - w * ε - v * κ +
        β * (jn * ((1 - ρ) * (N + ε) + qv * v) + cn))
      ((wt - w) + (A - wt + (1 - ρ) * κ / qv)) 0 := by
  have hid := hasDerivAt_id' (0 : ℝ)
  have h := ((((hid.const_add N).const_mul A).sub_const (wt * N)).sub
    (hid.const_mul w)).sub_const (v * κ) |>.add
    ((((hid.const_add N).const_mul (1 - ρ)).add_const (qv * v)).const_mul jn |>.add_const cn
      |>.const_mul β)
  convert h using 1
  rw [hfoc]; field_simp; ring

/-- Miao, (18.26), p. 598: in the large firm the worker's surplus at wage `w` is
`J^W_t(w) − J^U_t(w) = (J^W_t − J^U_t) + (w − w_t)` and the firm's is
`J_n(w, t) = J^F_t + (w_t − w)`; the equilibrium wage `w_t` solves the bargaining problem (18.26)
iff `ηJ^F_t = (1 − η)(J^W_t − J^U_t)`, the first-order condition of (18.11). -/
theorem eq_18_26 {η D JF wt : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hS : 0 < D + JF) :
    (0 ≤ D ∧ 0 ≤ JF ∧ IsMaxOn (fun w ↦ (D + (w - wt)) ^ η * (JF + (wt - w)) ^ (1 - η))
        {w | 0 ≤ D + (w - wt) ∧ 0 ≤ JF + (wt - w)} wt) ↔ η * JF = (1 - η) * D := by
  have e1 : ∀ w, D + (w - wt) = (D - wt) + w := fun w ↦ by ring
  have e2 : ∀ w, JF + (wt - w) = (JF + wt) - w := fun w ↦ by ring
  simp only [e1, e2]
  have h := dm_nash_solution (w := wt) hη0 hη1 (show 0 < (D - wt) + (JF + wt) by linarith)
  simp only [sub_add_cancel, add_sub_cancel_right] at h
  exact h

/-- Miao, (18.27), p. 598: since `∂J_t/∂N` at wage `w` is `A − w + (1 − ρ)κ/q^v_t`, which is the
filled-job value `J^F_t(w) = A − w + β(ρ·0 + (1 − ρ)J^F_{t+1})` of (18.4) under free entry
`J^F_{t+1} = κ/(βq^v_t)`, the objective of (18.27) coincides with that of (18.11). -/
theorem eq_18_27 {A κ β ρ η qv X JU : ℝ} (hβ : β ≠ 0) (hq : qv ≠ 0) :
    (fun w ↦ (w + X - JU) ^ η * (A - w + (1 - ρ) * κ / qv) ^ (1 - η)) =
      fun w ↦ (w + X - JU) ^ η * (A - w + β * (ρ * 0 + (1 - ρ) * (κ / (β * qv)))) ^ (1 - η) := by
  funext w
  congr 2
  field_simp
  ring

end Miao.SearchAndMatching
