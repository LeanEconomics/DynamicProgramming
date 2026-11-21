/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXTree
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# §14.3.2 Capacity utilization and Exercise 14.3

Miao, §14.3 (introduction, p. 493) and §14.3.2, pp. 493–494; Exercise 14.3, p. 507.

Capital depreciates at the rate `δ(u) = δ₀u^{δ₁}` (`rx_dep`, `δ₀ > 0`, `δ₁ > 1`), increasing and
strictly convex in the utilization rate `u > 0` (`rx_dep_strictMonoOn`, `rx_dep_strictConvexOn`),
`K_{t+1} = (1 − δ(uₜ))Kₜ + Iₜ` and `Yₜ = zₜ(Kₜuₜ)^α Nₜ^{1−α}` (`rx_cuY`). The model lives on
the event tree of `RXTree`.

* The planner's first-order conditions, derived by perturbing `K_{t+1}` at a node and `uₜ`:
  `u′(Cₜ) = βEₜ u′(C_{t+1})(1 − δ(u_{t+1}) + αY_{t+1}/K_{t+1})` (`rx_cu_planner_euler`) and
  `δ′(uₜ) = αYₜ/(Kₜuₜ)` (`rx_cu_planner_util`).
* The decentralisation: the firm's conditions `R_{kt} = αYₜ/(Kₜuₜ)` and the wage
  (`rx_cu_firm_foc`); the household's utilization condition `δ′(uₜ) = R_{kt}` (14.41)
  (`eq_14_41`) and its Euler equation (`rx_cu_household_euler`); with the firm's prices the
  household's conditions are the planner's (`rx_cu_decentralised_eq_planner`).
* Calibration (p. 494): in a steady state with `u = 1`, `δ₀δ₁ = 1/β − 1 + δ₀`, so
  `δ₁ = 1 + (1/β − 1)/δ₀ > 1` (`rx_cu_calibration`); with `β = 0.99`, `δ₀ = 0.025`,
  `δ₁ = 139/99` (`rx_cu_calibration_value`).
* Exercise 14.3 (its mathematical content: the steady state): the steady-state utilization
  rate is unique, `u^{δ₁} = (1/β − 1)/(δ₀(δ₁ − 1))` (`ex_14_3_utilization`), it equals one iff
  `δ₀(δ₁ − 1) = 1/β − 1` (`ex_14_3_u_eq_one`), and the steady-state capital–labour ratio solves
  `αzu^α(K/N)^{α−1} = δ₀δ₁u^{δ₁}` (`ex_14_3_capital_labour`). The calibration and the Dynare
  impulse responses of Exercise 14.3 are not formalised (computational).
* "The idea of capacity utilization is to allow the intensity of the use of capital to vary in
  response to TFP shocks" (p. 493): given `K`, `N`, the optimal utilization rate is strictly
  increasing in `z` (`rx_cu_util_increasing`), so output rises proportionally more than TFP
  (`rx_cu_amplification`).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- The depreciation rate `δ(u) = δ₀u^{δ₁}` (Miao, p. 493). -/
noncomputable def rx_dep (δ0 δ1 u : ℝ) : ℝ := δ0 * u ^ δ1

/-- Output with capacity utilization `Y = z(Ku)^α N^{1−α}` (Miao, p. 493). -/
noncomputable def rx_cuY (α z K u N : ℝ) : ℝ := z * (K * u) ^ α * N ^ (1 - α)

/-- Miao, p. 493: `δ′(u) = δ₀δ₁u^{δ₁−1}` for `u > 0`. -/
theorem rx_dep_hasDerivAt (δ0 δ1 : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (rx_dep δ0 δ1) (δ0 * δ1 * u ^ (δ1 - 1)) u := by
  have := (Real.hasDerivAt_rpow_const (p := δ1) (Or.inl hu.ne')).const_mul δ0
  unfold rx_dep
  convert this using 1
  ring

/-- Miao, p. 493: higher utilization makes capital depreciate faster. -/
theorem rx_dep_strictMonoOn {δ0 δ1 : ℝ} (h0 : 0 < δ0) (h1 : 1 < δ1) :
    StrictMonoOn (rx_dep δ0 δ1) (Set.Ioi 0) := by
  intro x hx y _ hxy
  unfold rx_dep
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hx) hxy (by linarith)) h0

/-- Miao, p. 493: `δ₁ > 1` makes `δ(·)` strictly convex (the curvature parameter). -/
theorem rx_dep_strictConvexOn {δ0 δ1 : ℝ} (h0 : 0 < δ0) (h1 : 1 < δ1) :
    StrictConvexOn ℝ (Set.Ici 0) (rx_dep δ0 δ1) := by
  have hc := strictConvexOn_rpow h1
  refine ⟨hc.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := hc.2 hx hy hxy ha hb hab
  simp only [rx_dep, smul_eq_mul] at this ⊢
  nlinarith [mul_lt_mul_of_pos_left this h0]

/-- `k ↦ z(ku)^α N^{1−α}` has derivative `αY/k` at `k > 0` (for `u > 0`). -/
theorem rx_cuY_hasDerivAt_K (α z u N : ℝ) {k : ℝ} (hk : 0 < k) (hu : 0 < u) :
    HasDerivAt (fun x => rx_cuY α z x u N) (α * rx_cuY α z k u N / k) k := by
  have hku : 0 < k * u := mul_pos hk hu
  have h1 : HasDerivAt (fun x => x * u) u k := by simpa using (hasDerivAt_id k).mul_const u
  have h2 := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hku.ne')).comp k h1
  have h3 := (h2.const_mul z).mul_const (N ^ (1 - α))
  unfold rx_cuY
  refine h3.congr_deriv ?_
  rw [Real.rpow_sub_one hku.ne']
  field_simp

/-- `v ↦ z(Kv)^α N^{1−α}` has derivative `αY/u` at `u > 0` (for `K > 0`). -/
theorem rx_cuY_hasDerivAt_u (α z K N : ℝ) {u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    HasDerivAt (fun v => rx_cuY α z K v N) (α * rx_cuY α z K u N / u) u := by
  have hku : 0 < K * u := mul_pos hK hu
  have h1 : HasDerivAt (fun v => K * v) K u := by simpa using (hasDerivAt_id u).const_mul K
  have h2 := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hku.ne')).comp u h1
  have h3 := (h2.const_mul z).mul_const (N ^ (1 - α))
  unfold rx_cuY
  refine h3.congr_deriv ?_
  rw [Real.rpow_sub_one hku.ne']
  field_simp

/-- Miao, p. 493, the planner's Euler equation with capacity utilization. At the node `h`
the planner chooses `K_{t+1} = k`; it enters `Cₜ = Yₜ − k + (1 − δ(uₜ))Kₜ` and, at each
successor `s`, `C_{t+1}(s) = Y_{t+1}(s) − K_{t+2}(s) + (1 − δ(u_{t+1}(s)))k` with
`Y_{t+1}(s) = z(s)(ku(s))^α N(s)^{1−α}`. If `K_{t+1}` is a local maximum of
`u(Cₜ) + βEₜu(C_{t+1})` (felicities `U₀`, `U₁ₛ` with derivatives `u′(Cₜ) = Λ₀`,
`u′(C_{t+1}(s)) = Λ₁(s)`), then
`u′(Cₜ) = βEₜ[u′(C_{t+1})(1 − δ(u_{t+1}) + αY_{t+1}/K_{t+1})]`. -/
theorem rx_cu_planner_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {α β δ0 δ1 Yt ut Kt K1 l0 : ℝ} {z u N K2 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hK1 : 0 < K1) (hu : ∀ s, 0 < u s)
    (hU0 : HasDerivAt U0 l0 (Yt - K1 + (1 - rx_dep δ0 δ1 ut) * Kt))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s)
      (rx_cuY α (z s) K1 (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * K1))
    (hmax : IsLocalMax (fun k => U0 (Yt - k + (1 - rx_dep δ0 δ1 ut) * Kt) + β * ∑ s,
      T.cp h s * U1 s (rx_cuY α (z s) k (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)) K1) :
    l0 = β * rx_Es T h (fun s => l1 s *
      (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1)) := by
  have hc0 : HasDerivAt (fun k => Yt - k + (1 - rx_dep δ0 δ1 ut) * Kt) (0 - 1 + 0) K1 :=
    ((hasDerivAt_const K1 Yt).sub (hasDerivAt_id K1)).add (hasDerivAt_const K1 _)
  have hc1 : ∀ s, HasDerivAt
      (fun k => rx_cuY α (z s) k (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
      (α * rx_cuY α (z s) K1 (u s) (N s) / K1 - 0 + (1 - rx_dep δ0 δ1 (u s)) * 1) K1 :=
    fun s => ((rx_cuY_hasDerivAt_K α (z s) (u s) (N s) hK1 (hu s)).sub
      (hasDerivAt_const K1 _)).add ((hasDerivAt_id K1).const_mul _)
  have e := rx_node_foc (c0 := fun k => Yt - k + (1 - rx_dep δ0 δ1 ut) * Kt)
    (c1 := fun s k => rx_cuY α (z s) k (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
    hU0 hc0 hU1 hc1 hmax
  simp only [rx_Es]
  have hs : ∀ s, T.cp h s * (l1 s * (α * rx_cuY α (z s) K1 (u s) (N s) / K1 - 0
      + (1 - rx_dep δ0 δ1 (u s)) * 1)) = T.cp h s * (l1 s *
      (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1)) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hs s] at e
  linarith

/-- Miao, p. 493, the planner's utilization condition `δ′(uₜ) = αYₜ/(Kₜuₜ)`. The rate `uₜ`
enters only `Cₜ = z(Kₜuₜ)^α Nₜ^{1−α} − K_{t+1} + (1 − δ(uₜ))Kₜ`; at a local maximum of
`u(Cₜ)` with `u′(Cₜ) ≠ 0` the marginal product of utilization equals the marginal cost
`δ′(uₜ)Kₜ`. -/
theorem rx_cu_planner_util {α δ0 δ1 z K N K1 u l0 : ℝ} {U0 : ℝ → ℝ} (hK : 0 < K) (hu : 0 < u)
    (hl0 : l0 ≠ 0) (hU0 : HasDerivAt U0 l0 (rx_cuY α z K u N - K1 + (1 - rx_dep δ0 δ1 u) * K))
    (hmax : IsLocalMax (fun v => U0 (rx_cuY α z K v N - K1 + (1 - rx_dep δ0 δ1 v) * K)) u) :
    δ0 * δ1 * u ^ (δ1 - 1) = α * rx_cuY α z K u N / (K * u) := by
  have hc : HasDerivAt (fun v => rx_cuY α z K v N - K1 + (1 - rx_dep δ0 δ1 v) * K)
      (α * rx_cuY α z K u N / u - 0 + (0 - δ0 * δ1 * u ^ (δ1 - 1)) * K) u :=
    ((rx_cuY_hasDerivAt_u α z K N hK hu).sub (hasDerivAt_const u K1)).add
      (((hasDerivAt_const u 1).sub (rx_dep_hasDerivAt δ0 δ1 hu)).mul_const K)
  have e := hmax.hasDerivAt_eq_zero (hU0.comp u hc)
  rcases mul_eq_zero.1 e with h0 | h0
  · exact absurd h0 hl0
  · field_simp
    field_simp at h0
    linarith

/-- Miao, p. 494, the firm's problem `max zk^α n^{1−α} − R_k k − wn`: at an interior maximum
`R_k = αzk^α n^{1−α}/k` and `w = (1 − α)zk^α n^{1−α}/n`; in equilibrium `k = Ku`, `n = N`, so
`R_{kt} = αYₜ/(Kₜuₜ)`. -/
theorem rx_cu_firm_foc {α z K u N R w : ℝ} (hK : 0 < K) (hu : 0 < u) (hN : 0 < N)
    (hk : IsLocalMax (fun k => z * k ^ α * N ^ (1 - α) - R * k - w * N) (K * u))
    (hn : IsLocalMax (fun n => z * (K * u) ^ α * n ^ (1 - α) - R * (K * u) - w * n) N) :
    R = α * rx_cuY α z K u N / (K * u) ∧ w = (1 - α) * rx_cuY α z K u N / N := by
  have hku : 0 < K * u := mul_pos hK hu
  constructor
  · have d : HasDerivAt (fun k => z * k ^ α * N ^ (1 - α) - R * k - w * N)
        (z * (α * (K * u) ^ (α - 1)) * N ^ (1 - α) - R * 1 - 0) (K * u) :=
      ((((Real.hasDerivAt_rpow_const (p := α) (Or.inl hku.ne')).const_mul z).mul_const _).sub
        ((hasDerivAt_id _).const_mul R)).sub (hasDerivAt_const _ _)
    have e := hk.hasDerivAt_eq_zero d
    rw [Real.rpow_sub_one hku.ne'] at e
    unfold rx_cuY
    field_simp at e ⊢
    linarith
  · have d : HasDerivAt (fun n => z * (K * u) ^ α * n ^ (1 - α) - R * (K * u) - w * n)
        (z * (K * u) ^ α * ((1 - α) * N ^ (1 - α - 1)) - 0 - w * 1) N :=
      (((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul _).sub
        (hasDerivAt_const _ _)).sub ((hasDerivAt_id _).const_mul w)
    have e := hn.hasDerivAt_eq_zero d
    rw [Real.rpow_sub_one hN.ne'] at e
    unfold rx_cuY
    field_simp at e ⊢
    linarith

/-- Miao, (14.41), p. 494. The household owns capital and rents the services `uₜKₜ` at the rate
`R_{kt}`; its budget gives `Cₜ = R_{kt}uₜKₜ + wₜNₜ − K_{t+1} + (1 − δ(uₜ))Kₜ`. At a local
maximum in `uₜ` with `u′(Cₜ) ≠ 0`: `δ′(uₜ) = R_{kt}`. -/
theorem eq_14_41 {δ0 δ1 R w K N K1 u l0 : ℝ} {U0 : ℝ → ℝ} (hK : 0 < K) (hu : 0 < u)
    (hl0 : l0 ≠ 0) (hU0 : HasDerivAt U0 l0 (R * (u * K) + w * N - K1 + (1 - rx_dep δ0 δ1 u) * K))
    (hmax : IsLocalMax (fun v => U0 (R * (v * K) + w * N - K1 + (1 - rx_dep δ0 δ1 v) * K)) u) :
    δ0 * δ1 * u ^ (δ1 - 1) = R := by
  have hc : HasDerivAt (fun v => R * (v * K) + w * N - K1 + (1 - rx_dep δ0 δ1 v) * K)
      (R * (1 * K) + 0 - 0 + (0 - δ0 * δ1 * u ^ (δ1 - 1)) * K) u :=
    ((((hasDerivAt_id u).mul_const K).const_mul R).add (hasDerivAt_const u _)).sub
      (hasDerivAt_const u K1) |>.add
      (((hasDerivAt_const u 1).sub (rx_dep_hasDerivAt δ0 δ1 hu)).mul_const K)
  have e := hmax.hasDerivAt_eq_zero (hU0.comp u hc)
  rcases mul_eq_zero.1 e with h0 | h0
  · exact absurd h0 hl0
  · have : (R - δ0 * δ1 * u ^ (δ1 - 1)) * K = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hK.ne'

/-- Miao, p. 494, the household's Euler equation with utilization: perturbing `K_{t+1} = k` in
`Cₜ = R_{kt}uₜKₜ + wₜNₜ − k + (1 − δ(uₜ))Kₜ` and
`C_{t+1}(s) = R_k(s)u(s)k + w(s)N(s) − K_{t+2}(s) + (1 − δ(u(s)))k` gives
`u′(Cₜ) = βEₜ[u′(C_{t+1})(R_{k,t+1}u_{t+1} + 1 − δ(u_{t+1}))]`. -/
theorem rx_cu_household_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β δ0 δ1 Wt K1 l0 : ℝ} {R u wN K2 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (Wt - K1))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s)
      (R s * u s * K1 + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * K1))
    (hmax : IsLocalMax (fun k => U0 (Wt - k) + β * ∑ s,
      T.cp h s * U1 s (R s * u s * k + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)) K1) :
    l0 = β * rx_Es T h (fun s => l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s))) := by
  have hc0 : HasDerivAt (fun k => Wt - k) (0 - 1) K1 := (hasDerivAt_const K1 Wt).sub
    (hasDerivAt_id K1)
  have hc1 : ∀ s, HasDerivAt
      (fun k => R s * u s * k + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
      (R s * u s * 1 + 0 - 0 + (1 - rx_dep δ0 δ1 (u s)) * 1) K1 :=
    fun s => ((((hasDerivAt_id K1).const_mul _).add (hasDerivAt_const K1 _)).sub
      (hasDerivAt_const K1 _)).add ((hasDerivAt_id K1).const_mul _)
  have e := rx_node_foc (c0 := fun k => Wt - k)
    (c1 := fun s k => R s * u s * k + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
    hU0 hc0 hU1 hc1 hmax
  simp only [rx_Es]
  have hs : ∀ s, T.cp h s * (l1 s * (R s * u s * 1 + 0 - 0 + (1 - rx_dep δ0 δ1 (u s)) * 1)) =
      T.cp h s * (l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s))) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hs s] at e
  linarith

/-- Miao, pp. 493–494: the decentralised equilibrium and the planner's problem give the same
conditions. With the firm's rental rate `R_k = αY/(Ku)` (`rx_cu_firm_foc`), the household's
Euler equation is the planner's (`rx_cu_household_euler` vs `rx_cu_planner_euler`), (14.41) is
the planner's utilization condition (`rx_cu_planner_util`), and the household's income
`R_kuK + wN` with `w = (1 − α)Y/N` is output `Y`, so its budget is the resource constraint. -/
theorem rx_cu_decentralised_eq_planner {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {α β δ0 δ1 K1 l0 : ℝ} {R u z N l1 : S → ℝ} (hK1 : 0 < K1) (hu : ∀ s, 0 < u s)
    (hR : ∀ s, R s = α * rx_cuY α (z s) K1 (u s) (N s) / (K1 * u s)) :
    (l0 = β * rx_Es T h (fun s => l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s))) ↔
      l0 = β * rx_Es T h (fun s => l1 s *
        (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1))) ∧
    (∀ {Rt ut Kt zt Nt : ℝ}, 0 < Kt → 0 < ut → Rt = α * rx_cuY α zt Kt ut Nt / (Kt * ut) →
      (δ0 * δ1 * ut ^ (δ1 - 1) = Rt ↔
        δ0 * δ1 * ut ^ (δ1 - 1) = α * rx_cuY α zt Kt ut Nt / (Kt * ut))) ∧
    (∀ {Rt wt ut Kt zt Nt : ℝ}, 0 < Kt → 0 < ut → 0 < Nt →
      Rt = α * rx_cuY α zt Kt ut Nt / (Kt * ut) → wt = (1 - α) * rx_cuY α zt Kt ut Nt / Nt →
      Rt * (ut * Kt) + wt * Nt = rx_cuY α zt Kt ut Nt) := by
  refine ⟨?_, fun _ _ hRt => by rw [hRt], fun hKt hut hNt hRt hwt => ?_⟩
  · have : ∀ s, l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s)) =
        l1 s * (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1) := by
      intro s
      rw [hR s]
      have := hu s
      field_simp
      ring
    simp only [this]
  · rw [hRt, hwt]
    field_simp
    ring

/-- Miao, p. 494, calibration. In a steady state with `u = 1`, the Euler equation gives
`1 = β(1 − δ(1) + αY/K)` and (14.41) with `R_k = αY/K` gives `δ′(1) = δ₀δ₁ = αY/K`; hence
`δ₀δ₁ = 1/β − 1 + δ₀` pins down `δ₀δ₁`, `δ₁ = 1 + (1/β − 1)/δ₀`, and `δ₁ > 1` when `β < 1`. -/
theorem rx_cu_calibration {β δ0 δ1 ay : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0)
    (heuler : 1 = β * (1 - rx_dep δ0 δ1 1 + ay)) (hutil : δ0 * δ1 * (1 : ℝ) ^ (δ1 - 1) = ay) :
    δ0 * δ1 = 1 / β - 1 + δ0 ∧ δ1 = 1 + (1 / β - 1) / δ0 ∧ (β < 1 → 1 < δ1) := by
  simp only [rx_dep, Real.one_rpow, mul_one] at heuler hutil
  have h1 : δ0 * δ1 = 1 / β - 1 + δ0 := by
    rw [hutil]
    field_simp
    linarith
  have h2 : δ1 = 1 + (1 / β - 1) / δ0 := by
    have : (1 / β - 1) / δ0 = δ1 - 1 := by
      rw [div_eq_iff hδ0.ne']
      linear_combination -h1
    linarith
  refine ⟨h1, h2, fun hβ1 => ?_⟩
  rw [h2]
  have : 0 < 1 / β - 1 := by
    rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ hβ]
    linarith
  have := div_pos this hδ0
  linarith

/-- Miao, p. 494, calibration: with `β = 0.99` (§14.2) and `δ₀ = 0.025`, `δ₁ = 139/99`. -/
theorem rx_cu_calibration_value {δ1 ay : ℝ}
    (heuler : 1 = 99 / 100 * (1 - rx_dep (1 / 40) δ1 1 + ay))
    (hutil : 1 / 40 * δ1 * (1 : ℝ) ^ (δ1 - 1) = ay) : δ1 = 139 / 99 := by
  have := (rx_cu_calibration (by norm_num) (by norm_num) heuler hutil).2.1
  rw [this]
  norm_num

/-- **Exercise 14.3** (Miao, p. 507), the steady-state utilization rate. In a nonstochastic
steady state the Euler equation is `1 = β(1 − δ(u) + αY/K)` and the utilization condition is
`δ′(u) = αY/(Ku)`. Then `u^{δ₁} = (1/β − 1)/(δ₀(δ₁ − 1))`, so the steady-state utilization
rate is unique: `u = ((1/β − 1)/(δ₀(δ₁ − 1)))^{1/δ₁}`. -/
theorem ex_14_3_utilization {β δ0 δ1 ay u : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0) (hδ1 : 1 < δ1)
    (hu : 0 < u) (heuler : 1 = β * (1 - rx_dep δ0 δ1 u + ay))
    (hutil : δ0 * δ1 * u ^ (δ1 - 1) = ay / u) :
    u ^ δ1 = (1 / β - 1) / (δ0 * (δ1 - 1)) ∧
      u = ((1 / β - 1) / (δ0 * (δ1 - 1))) ^ δ1⁻¹ := by
  have hay : ay = δ0 * δ1 * u ^ δ1 := by
    rw [Real.rpow_sub_one hu.ne'] at hutil
    field_simp at hutil
    linarith
  have h1 : u ^ δ1 = (1 / β - 1) / (δ0 * (δ1 - 1)) := by
    rw [hay] at heuler
    unfold rx_dep at heuler
    have : δ0 * (δ1 - 1) ≠ 0 := mul_ne_zero hδ0.ne' (by linarith)
    have hb : 1 / β = 1 - δ0 * u ^ δ1 + δ0 * δ1 * u ^ δ1 := by
      rw [div_eq_iff hβ.ne']
      linear_combination heuler
    rw [eq_div_iff this, hb]
    ring
  refine ⟨h1, ?_⟩
  rw [← h1, Real.rpow_rpow_inv hu.le (by linarith)]

/-- **Exercise 14.3** (Miao, p. 507), existence of the steady-state utilization rate: for
`0 < β < 1`, `u* = ((1/β − 1)/(δ₀(δ₁ − 1)))^{1/δ₁} > 0` together with `αY/K = δ₀δ₁u*^{δ₁}`
satisfies both steady-state conditions. -/
theorem ex_14_3_utilization_exists {β δ0 δ1 : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ0)
    (hδ1 : 1 < δ1) :
    let u := ((1 / β - 1) / (δ0 * (δ1 - 1))) ^ δ1⁻¹
    0 < u ∧ 1 = β * (1 - rx_dep δ0 δ1 u + δ0 * δ1 * u ^ δ1) ∧
      δ0 * δ1 * u ^ (δ1 - 1) = δ0 * δ1 * u ^ δ1 / u := by
  intro u
  have hc : 0 < (1 / β - 1) / (δ0 * (δ1 - 1)) := by
    apply div_pos
    · rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ hβ]
      linarith
    · exact mul_pos hδ0 (by linarith)
  have hu : 0 < u := Real.rpow_pos_of_pos hc _
  have hpow : u ^ δ1 = (1 / β - 1) / (δ0 * (δ1 - 1)) :=
    Real.rpow_inv_rpow hc.le (by linarith)
  refine ⟨hu, ?_, ?_⟩
  · unfold rx_dep
    rw [hpow]
    have : δ0 * (δ1 - 1) ≠ 0 := mul_ne_zero hδ0.ne' (by linarith)
    have hc' : δ0 * (δ1 - 1) * ((1 / β - 1) / (δ0 * (δ1 - 1))) = 1 / β - 1 :=
      mul_div_cancel₀ _ this
    have hb : β * (1 / β) = 1 := by field_simp
    linear_combination (-β) * hc' - hb
  · rw [Real.rpow_sub_one hu.ne']
    ring

/-- **Exercise 14.3** (Miao, p. 507) and p. 494: the steady-state utilization rate equals one
iff `δ₀(δ₁ − 1) = 1/β − 1` (equivalently `δ₀δ₁ = 1/β − 1 + δ₀`, `rx_cu_calibration`). -/
theorem ex_14_3_u_eq_one {β δ0 δ1 ay u : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0) (hδ1 : 1 < δ1)
    (hu : 0 < u) (heuler : 1 = β * (1 - rx_dep δ0 δ1 u + ay))
    (hutil : δ0 * δ1 * u ^ (δ1 - 1) = ay / u) :
    u = 1 ↔ δ0 * (δ1 - 1) = 1 / β - 1 := by
  obtain ⟨h1, h2⟩ := ex_14_3_utilization hβ hδ0 hδ1 hu heuler hutil
  have hne : δ0 * (δ1 - 1) ≠ 0 := mul_ne_zero hδ0.ne' (by linarith)
  constructor
  · intro hu1
    rw [hu1, Real.one_rpow, eq_div_iff hne, one_mul] at h1
    exact h1
  · intro hc
    rw [h2, ← hc, div_self hne, Real.one_rpow]

/-- **Exercise 14.3** (Miao, p. 507), the steady-state capital–labour ratio: with
`Y = z(Ku)^α N^{1−α}`, the condition `αY/K = r` (with `r = δ₀δ₁u^{δ₁}` from
`ex_14_3_utilization`) reads `αzu^α(K/N)^{α−1} = r`. -/
theorem ex_14_3_capital_labour {α z K u N : ℝ} (hK : 0 < K) (hu : 0 < u) (hN : 0 < N) :
    α * rx_cuY α z K u N / K = α * z * u ^ α * (K / N) ^ (α - 1) := by
  unfold rx_cuY
  rw [Real.mul_rpow hK.le hu.le, Real.div_rpow hK.le hN.le, Real.rpow_sub_one hK.ne',
    Real.rpow_sub_one hN.ne', show (1 : ℝ) - α = -(α - 1) by ring, Real.rpow_neg hN.le,
    Real.rpow_sub_one hN.ne']
  have : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  field_simp

/-- The utilization condition `δ₀δ₁u^{δ₁−1} = αz(Ku)^α N^{1−α}/(Ku)` is equivalent to
`u^{δ₁−α} = (α/(δ₀δ₁)) K^{α−1}N^{1−α} z`. -/
theorem rx_cu_util_closed {α δ0 δ1 z K u N : ℝ} (hδ0 : 0 < δ0) (hδ1 : 0 < δ1) (hK : 0 < K)
    (hu : 0 < u) (hfoc : δ0 * δ1 * u ^ (δ1 - 1) = α * rx_cuY α z K u N / (K * u)) :
    u ^ (δ1 - α) = α / (δ0 * δ1) * (K ^ (α - 1) * N ^ (1 - α)) * z := by
  unfold rx_cuY at hfoc
  rw [Real.mul_rpow hK.le hu.le, Real.rpow_sub_one hu.ne'] at hfoc
  rw [Real.rpow_sub hu, Real.rpow_sub_one hK.ne']
  have hua : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  field_simp at hfoc ⊢
  linarith

/-- Miao, p. 493: utilization responds to TFP. Given `K` and `N`, if `u` and `u′` satisfy the
planner's utilization condition at TFP levels `z < z′` (with `δ₀ > 0`, `δ₁ > 1 > α`), then
`u < u′`. -/
theorem rx_cu_util_increasing {α δ0 δ1 z z' K N u u' : ℝ} (hδ0 : 0 < δ0) (hδ1 : 1 < δ1)
    (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hN : 0 < N) (hu : 0 < u) (hu' : 0 < u')
    (hz : z < z')
    (hfoc : δ0 * δ1 * u ^ (δ1 - 1) = α * rx_cuY α z K u N / (K * u))
    (hfoc' : δ0 * δ1 * u' ^ (δ1 - 1) = α * rx_cuY α z' K u' N / (K * u')) : u < u' := by
  have e := rx_cu_util_closed hδ0 (by linarith) hK hu hfoc
  have e' := rx_cu_util_closed hδ0 (by linarith) hK hu' hfoc'
  have hc : 0 < α / (δ0 * δ1) * (K ^ (α - 1) * N ^ (1 - α)) :=
    mul_pos (div_pos hα0 (mul_pos hδ0 (by linarith)))
      (mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos hN _))
  by_contra hle
  have := Real.rpow_le_rpow hu'.le (not_lt.1 hle) (show 0 ≤ δ1 - α by linarith)
  rw [e, e'] at this
  nlinarith

/-- Miao, p. 493, amplification: given `K` and `N`, if utilization rises with TFP (`u < u′`,
`rx_cu_util_increasing`), output rises proportionally more than TFP:
`z′/z < Y(z′, u′)/Y(z, u)`. -/
theorem rx_cu_amplification {α z z' K N u u' : ℝ} (hα0 : 0 < α) (hz : 0 < z) (hz' : 0 < z')
    (hK : 0 < K) (hN : 0 < N) (hu : 0 < u) (huu : u < u') :
    z' / z < rx_cuY α z' K u' N / rx_cuY α z K u N := by
  unfold rx_cuY
  have hu' : 0 < u' := hu.trans huu
  rw [Real.mul_rpow hK.le hu.le, Real.mul_rpow hK.le hu'.le]
  have h1 : u ^ α < u' ^ α := Real.rpow_lt_rpow hu.le huu hα0
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hNa : 0 < N ^ (1 - α) := Real.rpow_pos_of_pos hN _
  have hua : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  rw [div_lt_div_iff₀ hz (by positivity)]
  have : z' * (z * (K ^ α * u ^ α) * N ^ (1 - α)) < z' * (z * (K ^ α * u' ^ α) * N ^ (1 - α)) := by
    gcongr
  linarith

end Miao.NeoclassicalGrowth
