/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The basic RBC model: technology, preferences and the static first-order conditions

Miao, §14.2, pp. 471–473. The planner maximises `E ∑ βᵗ[ln C_t + χ ln(1 − N_t)]` (14.22)
subject to `C_t + I_t = z_tK_t^αN_t^{1−α} = Y_t` (14.23), `K_{t+1} = (1 − δ)K_t + I_t` (14.24),
`ln z_t = ρ ln z_{t−1} + σε_t` (14.25).

* Cobb–Douglas technology: output `rb_Y`, marginal products `rb_MPK`, `rb_MPL`, the identities
  `R_k = αY/K`, `w = (1 − α)Y/N` (`rb_MPK_eq`, `rb_MPL_eq`), Euler's theorem (`rb_euler_thm`),
  the tangent (concavity) inequality (`rb_cd_tangent`), and the firm's problem: marginal-product
  prices give a profit maximum with zero profit (`rb_firm_optimal`), and conversely a profit
  maximum with positive inputs has marginal-product prices (`rb_firm_foc`).
* The intratemporal condition (14.27): given `K_t`, `K_{t+1}` (hence `I_t`), `N_t` maximises
  `ln(zK^αN^{1−α} − I) + χ ln(1 − N)` iff `χC/(1 − N) = (1 − α)zK^αN^{−α}`
  (`eq_14_27`, `rb_labour_suff`, `rb_labour_nec`).
* The Euler equation (14.26) derived from the one-step variation in `K_{t+1}` with a finite
  conditional distribution of the next-period state (`eq_14_26_node`, `rb_euler_node_suff`,
  `rb_euler_node_nec`); the general measure-theoretic statement is in `RBPlanner`.
* The shock (14.25) iterated (`eq_14_25_iter`), and the Solow residual `SR_t = ln z_t`
  (`rb_solow_residual`).

**Departures.** The book's (14.26) is stated for a general distribution of `ε`; here the
derivation by the one-step variation is carried out for a finite conditional distribution
(weights `p i ≥ 0`, `∑ p i = 1`), while `RBPlanner` proves the sufficiency of (14.26), (14.27) and
transversality with a general conditional expectation.
-/

namespace Miao.NeoclassicalGrowth

open Real

/-! ### Technology -/

/-- Cobb–Douglas output `Y = zK^αN^{1−α}` (Miao, (14.23), p. 472). -/
noncomputable def rb_Y (α z K N : ℝ) : ℝ := z * K ^ α * N ^ (1 - α)

/-- The marginal product of capital `αzK^{α−1}N^{1−α}`, the rental rate `R_k` (Miao, p. 472). -/
noncomputable def rb_MPK (α z K N : ℝ) : ℝ := α * z * K ^ (α - 1) * N ^ (1 - α)

/-- The marginal product of labour `(1 − α)zK^αN^{−α}`, the wage `w` (Miao, p. 472). -/
noncomputable def rb_MPL (α z K N : ℝ) : ℝ := (1 - α) * z * K ^ α * N ^ (-α)

theorem rb_rpow_sub_one' {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ (a - 1) = x ^ a / x := by
  rw [Real.rpow_sub_one hx.ne']

theorem rb_rpow_neg' {x : ℝ} (hx : 0 < x) (α : ℝ) : x ^ (-α) = x ^ (1 - α) / x := by
  rw [← rb_rpow_sub_one' hx]
  ring_nf

/-- Miao, p. 473: `R_k = αY/K`. -/
theorem rb_MPK_eq (α z : ℝ) {K N : ℝ} (hK : 0 < K) :
    rb_MPK α z K N = α * rb_Y α z K N / K := by
  rw [rb_MPK, rb_Y, rb_rpow_sub_one' hK]
  ring

/-- Miao, p. 473: `w = (1 − α)Y/N`. -/
theorem rb_MPL_eq (α z K : ℝ) {N : ℝ} (hN : 0 < N) :
    rb_MPL α z K N = (1 - α) * rb_Y α z K N / N := by
  rw [rb_MPL, rb_Y, rb_rpow_neg' hN]
  ring

/-- Euler's theorem for the constant-returns technology: `R_kK + wN = Y`. -/
theorem rb_euler_thm (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPK α z K N * K + rb_MPL α z K N * N = rb_Y α z K N := by
  rw [rb_MPK_eq α z hK, rb_MPL_eq α z K hN]
  field_simp
  ring

theorem rb_Y_pos {α z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    0 < rb_Y α z K N := by
  unfold rb_Y
  have := Real.rpow_pos_of_pos hK α
  have := Real.rpow_pos_of_pos hN (1 - α)
  positivity

theorem rb_MPK_pos {α z K N : ℝ} (hα : 0 < α) (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    0 < rb_MPK α z K N := by
  rw [rb_MPK_eq α z hK]
  have := rb_Y_pos (α := α) hz hK hN
  positivity

theorem rb_MPL_pos {α z K N : ℝ} (hα : α < 1) (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    0 < rb_MPL α z K N := by
  rw [rb_MPL_eq α z K hN]
  have := rb_Y_pos (α := α) hz hK hN
  have : 0 < 1 - α := by linarith
  positivity

/-- The Cobb–Douglas tangent inequality: for `0 < α < 1`, `z ≥ 0`, `K, N > 0` and
`K', N' ≥ 0`, `zK'^αN'^{1−α} ≤ R_kK' + wN'` with `R_k`, `w` the marginal products at `(K, N)`.
This is the joint concavity of the technology. -/
theorem rb_cd_tangent {α z K N K' N' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 ≤ z)
    (hK : 0 < K) (hN : 0 < N) (hK' : 0 ≤ K') (hN' : 0 ≤ N') :
    rb_Y α z K' N' ≤ rb_MPK α z K N * K' + rb_MPL α z K N * N' := by
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hα0.le (by linarith : 0 ≤ 1 - α)
    (div_nonneg hK' hK.le) (div_nonneg hN' hN.le) (by ring)
  rw [Real.div_rpow hK' hK.le, Real.div_rpow hN' hN.le] at hamgm
  have hKa := Real.rpow_pos_of_pos hK α
  have hNa := Real.rpow_pos_of_pos hN (1 - α)
  have hA : 0 < z * K ^ α * N ^ (1 - α) + 1 := by positivity
  have key : K' ^ α * N' ^ (1 - α) ≤
      (α * (K' / K) + (1 - α) * (N' / N)) * (K ^ α * N ^ (1 - α)) := by
    have h := mul_le_mul_of_nonneg_right hamgm (le_of_lt (mul_pos hKa hNa))
    calc K' ^ α * N' ^ (1 - α)
        = K' ^ α / K ^ α * (N' ^ (1 - α) / N ^ (1 - α)) * (K ^ α * N ^ (1 - α)) := by
          field_simp
      _ ≤ _ := h
  rw [rb_MPK, rb_MPL, rb_Y, rb_rpow_sub_one' hK, rb_rpow_neg' hN]
  have := mul_le_mul_of_nonneg_left key hz
  clear hA
  calc z * K' ^ α * N' ^ (1 - α) = z * (K' ^ α * N' ^ (1 - α)) := by ring
    _ ≤ z * ((α * (K' / K) + (1 - α) * (N' / N)) * (K ^ α * N ^ (1 - α))) := this
    _ = _ := by field_simp

/-- The tangent inequality in the form `Y(K', N') ≤ Y(K, N) + R_k(K' − K) + w(N' − N)`. -/
theorem rb_cd_tangent' {α z K N K' N' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 ≤ z)
    (hK : 0 < K) (hN : 0 < N) (hK' : 0 ≤ K') (hN' : 0 ≤ N') :
    rb_Y α z K' N' ≤
      rb_Y α z K N + rb_MPK α z K N * (K' - K) + rb_MPL α z K N * (N' - N) := by
  have h1 := rb_cd_tangent hα0 hα1 hz hK hN hK' hN'
  have h2 := rb_euler_thm α z hK hN
  linarith

/-! ### The firm's problem -/

/-- Profit `zK^αN^{1−α} − R_kK − wN` of the firm (Miao, p. 460 and p. 472). -/
noncomputable def rb_profit (α z Rk w K N : ℝ) : ℝ := rb_Y α z K N - Rk * K - w * N

/-- Miao, p. 472: with the marginal-product prices `R_k = αzK^{α−1}N^{1−α}`,
`w = (1 − α)zK^αN^{−α}`, `(K, N)` maximises the firm's profit over all `K', N' ≥ 0`, and the
maximal profit is zero. -/
theorem rb_firm_optimal {α z K N : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 ≤ z) (hK : 0 < K)
    (hN : 0 < N) :
    rb_profit α z (rb_MPK α z K N) (rb_MPL α z K N) K N = 0 ∧
      ∀ K' N', 0 ≤ K' → 0 ≤ N' →
        rb_profit α z (rb_MPK α z K N) (rb_MPL α z K N) K' N' ≤ 0 := by
  refine ⟨?_, fun K' N' hK' hN' => ?_⟩
  · rw [rb_profit, ← rb_euler_thm α z hK hN]
    ring
  · rw [rb_profit]
    linarith [rb_cd_tangent hα0 hα1 hz hK hN hK' hN']

theorem rb_hasDerivAt_Y_K (α z N : ℝ) {K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k => rb_Y α z k N) (rb_MPK α z K N) K := by
  have h := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul z
  have h2 := h.mul_const (N ^ (1 - α))
  convert h2 using 1
  · rfl
  · rw [rb_MPK]; ring

theorem rb_hasDerivAt_Y_N (α z K : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => rb_Y α z K n) (rb_MPL α z K N) N := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul (z * K ^ α)
  convert h using 1
  · rfl
  · rw [rb_MPL]; ring_nf

/-- Miao, p. 472, the converse: if `(K, N)` with `K, N > 0` maximises profit given `(R_k, w)`,
then `R_k` and `w` are the marginal products. -/
theorem rb_firm_foc {α z Rk w K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hmax : ∀ K' N', 0 ≤ K' → 0 ≤ N' → rb_profit α z Rk w K' N' ≤ rb_profit α z Rk w K N) :
    Rk = rb_MPK α z K N ∧ w = rb_MPL α z K N := by
  constructor
  · have hloc : IsLocalMax (fun k => rb_profit α z Rk w k N) K := by
      filter_upwards [lt_mem_nhds hK] with k hk using hmax k N hk.le hN.le
    have hd : HasDerivAt (fun k => rb_profit α z Rk w k N) (rb_MPK α z K N - Rk) K := by
      have := ((rb_hasDerivAt_Y_K α z N hK).sub ((hasDerivAt_id K).const_mul Rk)).sub_const
        (w * N)
      convert this using 1
      · funext k; simp [rb_profit]
      · ring
    linarith [hloc.hasDerivAt_eq_zero hd]
  · have hloc : IsLocalMax (fun n => rb_profit α z Rk w K n) N := by
      filter_upwards [lt_mem_nhds hN] with n hn using hmax K n hK.le hn.le
    have hd : HasDerivAt (fun n => rb_profit α z Rk w K n) (rb_MPL α z K N - w) N := by
      have := ((rb_hasDerivAt_Y_N α z K hN).sub_const (Rk * K)).sub
        ((hasDerivAt_id N).const_mul w)
      convert this using 1
      · funext n; simp [rb_profit]
      · ring
    linarith [hloc.hasDerivAt_eq_zero hd]

/-! ### Preferences and the intratemporal condition (14.27) -/

/-- Period utility `ln C + χ ln(1 − N)` (Miao, (14.22), p. 472). -/
noncomputable def rb_u (χ C N : ℝ) : ℝ := Real.log C + χ * Real.log (1 - N)

/-- Concavity of `ln`: `ln c' ≤ ln c + (c' − c)/c` for `c, c' > 0`. -/
theorem rb_log_tangent {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    Real.log c' ≤ Real.log c + (c' - c) / c := by
  have h := Real.log_le_sub_one_of_pos (div_pos hc' hc)
  rw [Real.log_div hc'.ne' hc.ne'] at h
  have : c' / c - 1 = (c' - c) / c := by field_simp
  linarith

/-- The utility tangent inequality: `u(c', n') ≤ u(c, n) + (c' − c)/c − χ(n' − n)/(1 − n)`. -/
theorem rb_u_tangent {χ c n c' n' : ℝ} (hχ : 0 ≤ χ) (hc : 0 < c) (hn : n < 1) (hc' : 0 < c')
    (hn' : n' < 1) :
    rb_u χ c' n' ≤ rb_u χ c n + (c' - c) / c - χ * ((n' - n) / (1 - n)) := by
  have h1 := rb_log_tangent hc hc'
  have h2 := rb_log_tangent (by linarith : 0 < 1 - n) (by linarith : 0 < 1 - n')
  have h3 := mul_le_mul_of_nonneg_left h2 hχ
  rw [rb_u, rb_u]
  have : (1 - n' - (1 - n)) / (1 - n) = -((n' - n) / (1 - n)) := by ring
  rw [this] at h3
  linarith

/-- The objective of the static labour choice given `(z, K)` and investment `I`:
`ln(zK^αN^{1−α} − I) + χ ln(1 − N)`. -/
noncomputable def rb_static (α χ z K I N : ℝ) : ℝ := rb_u χ (rb_Y α z K N - I) N

/-- Miao, (14.27), p. 472: the intratemporal condition `χC/(1 − N) = (1 − α)zK^αN^{−α}`. -/
def eq_14_27 (α χ z K C N : ℝ) : Prop := χ * C / (1 - N) = rb_MPL α z K N

/-- Miao, (14.27), sufficiency: if `N ∈ (0, 1)`, `C = zK^αN^{1−α} − I > 0` and (14.27) holds,
then `N` maximises the static objective over every `N' ∈ [0, 1)` with positive consumption. -/
theorem rb_labour_suff {α χ z K I N : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hχ : 0 ≤ χ)
    (hz : 0 ≤ z) (hK : 0 < K) (hN0 : 0 < N) (hN1 : N < 1) (hC : 0 < rb_Y α z K N - I)
    (hfoc : eq_14_27 α χ z K (rb_Y α z K N - I) N) {N' : ℝ} (hN0' : 0 ≤ N') (hN1' : N' < 1)
    (hC' : 0 < rb_Y α z K N' - I) :
    rb_static α χ z K I N' ≤ rb_static α χ z K I N := by
  have ht := rb_u_tangent hχ hC hN1 hC' hN1'
  have hY := rb_cd_tangent' (K' := K) hα0 hα1 hz hK hN0 hK.le hN0'
  set C := rb_Y α z K N - I
  have h1N : 0 < 1 - N := by linarith
  have hw : rb_MPL α z K N / C = χ / (1 - N) := by
    rw [eq_14_27] at hfoc
    rw [← hfoc]
    field_simp
  have hgap : (rb_Y α z K N' - I - C) / C ≤ rb_MPL α z K N * (N' - N) / C := by
    apply div_le_div_of_nonneg_right _ hC.le
    simp only [C]
    linarith
  have : rb_MPL α z K N * (N' - N) / C = χ * ((N' - N) / (1 - N)) := by
    rw [mul_comm, mul_div_assoc, mul_comm, hw]
    ring
  unfold rb_static
  linarith

theorem rb_hasDerivAt_static (α χ z K I : ℝ) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hC : 0 < rb_Y α z K N - I) :
    HasDerivAt (rb_static α χ z K I)
      (rb_MPL α z K N / (rb_Y α z K N - I) - χ / (1 - N)) N := by
  have h1 := ((rb_hasDerivAt_Y_N α z K hN0).sub_const I).log hC.ne'
  have h2 := (((hasDerivAt_id N).const_sub 1).log (by simp; linarith)).const_mul χ
  convert h1.add h2 using 1
  · funext n; simp [rb_static, rb_u]
  · simp only [id]
    field_simp
    ring

/-- Miao, (14.27), necessity: if `N ∈ (0, 1)` with positive consumption maximises the static
objective over `N' ∈ [0, 1)` with positive consumption, then (14.27) holds. -/
theorem rb_labour_nec {α χ z K I N : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hC : 0 < rb_Y α z K N - I)
    (hmax : ∀ N', 0 ≤ N' → N' < 1 → 0 < rb_Y α z K N' - I →
      rb_static α χ z K I N' ≤ rb_static α χ z K I N) :
    eq_14_27 α χ z K (rb_Y α z K N - I) N := by
  have hcont : ContinuousAt (fun n => rb_Y α z K n - I) N :=
    ((rb_hasDerivAt_Y_N α z K hN0).sub_const I).continuousAt
  have hloc : IsLocalMax (rb_static α χ z K I) N := by
    filter_upwards [lt_mem_nhds hN0, gt_mem_nhds hN1, hcont.eventually (lt_mem_nhds hC)]
      with n h0 h1 h2 using hmax n h0.le h1 h2
  have h0 := hloc.hasDerivAt_eq_zero (rb_hasDerivAt_static α χ z K I hN0 hN1 hC)
  rw [eq_14_27]
  have h1N : 0 < 1 - N := by linarith
  field_simp at h0 ⊢
  linarith

/-! ### The Euler equation (14.26) from the one-step variation -/

/-- The two-period objective of the variation in `K_{t+1} = k`: date-`t` consumption
`W − k` (`W = Y_t + (1 − δ)K_t`) and date-`t+1` consumption
`z_iK^αN_i^{1−α} + (1 − δ)k − K₂ᵢ` in state `i` with probability `p i`. -/
noncomputable def rb_node {ι : Type*} [Fintype ι] (α β δ W : ℝ) (p z N K₂ : ι → ℝ)
    (k : ℝ) : ℝ :=
  Real.log (W - k) + β * ∑ i, p i * Real.log (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)

/-- Miao, (14.26), p. 472, at a node with finitely many successor states:
`1/C_t = E_t[β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}]`. -/
def eq_14_26_node {ι : Type*} [Fintype ι] (α β δ W : ℝ) (p z N K₂ : ι → ℝ) (k : ℝ) : Prop :=
  1 / (W - k) =
    ∑ i, p i * (β * (rb_MPK α (z i) k (N i) + 1 - δ) /
      (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))

/-- Miao, (14.26), sufficiency of the Euler equation for the one-step variation: if
consumption is positive at `k > 0` in every state and (14.26) holds, `k` maximises the
two-period objective among all `k' ≥ 0` with positive consumption. -/
theorem rb_euler_node_suff {ι : Type*} [Fintype ι] {α β δ W : ℝ} {p z N K₂ : ι → ℝ} {k : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, 0 ≤ z i)
    (hN : ∀ i, 0 < N i) (hk : 0 < k) (hc0 : 0 < W - k)
    (hc1 : ∀ i, 0 < rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)
    (heul : eq_14_26_node α β δ W p z N K₂ k) {k' : ℝ} (hk' : 0 ≤ k') (hc0' : 0 < W - k')
    (hc1' : ∀ i, 0 < rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i) :
    rb_node α β δ W p z N K₂ k' ≤ rb_node α β δ W p z N K₂ k := by
  have h0 := rb_log_tangent hc0 hc0'
  have hi : ∀ i, p i * Real.log (rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i) ≤
      p i * Real.log (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i) +
        p i * ((rb_MPK α (z i) k (N i) + 1 - δ) /
          (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)) * (k' - k) := fun i => by
    have ht := rb_log_tangent (hc1 i) (hc1' i)
    have hY := rb_cd_tangent' hα0 hα1 (hz i) hk (hN i) hk' (hN i).le
    have hq : (rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i -
        (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)) /
          (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i) ≤
        (rb_MPK α (z i) k (N i) + 1 - δ) * (k' - k) /
          (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i) := by
      apply div_le_div_of_nonneg_right _ (hc1 i).le
      simp only [sub_self, mul_zero, add_zero] at hY
      nlinarith
    have := mul_le_mul_of_nonneg_left (ht.trans (add_le_add_right hq _)) (hp i)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hs := mul_le_mul_of_nonneg_left hsum hβ
  unfold rb_node
  rw [eq_14_26_node] at heul
  have hE : β * ((∑ i, p i * ((rb_MPK α (z i) k (N i) + 1 - δ) /
      (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))) * (k' - k)) = (k' - k) / (W - k) := by
    rw [div_eq_mul_one_div (k' - k), heul, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have : (W - k' - (W - k)) / (W - k) = -((k' - k) / (W - k)) := by ring
  rw [this] at h0
  nlinarith

/-- Miao, (14.26), necessity: if `k > 0` with positive consumption maximises the two-period
objective among all `k' > 0` with positive consumption, the Euler equation holds. -/
theorem rb_euler_node_nec {ι : Type*} [Fintype ι] {α β δ W : ℝ} {p z N K₂ : ι → ℝ} {k : ℝ}
    (hk : 0 < k) (hc0 : 0 < W - k)
    (hc1 : ∀ i, 0 < rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)
    (hmax : ∀ k', 0 < k' → 0 < W - k' →
      (∀ i, 0 < rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i) →
        rb_node α β δ W p z N K₂ k' ≤ rb_node α β δ W p z N K₂ k) :
    eq_14_26_node α β δ W p z N K₂ k := by
  have hdi : ∀ i, HasDerivAt (fun k => rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)
      (rb_MPK α (z i) k (N i) + (1 - δ)) k := fun i =>
    (((rb_hasDerivAt_Y_K α (z i) (N i) hk).add
      ((hasDerivAt_id k).const_mul (1 - δ))).sub_const (K₂ i)).congr_deriv (by simp)
  have hd : HasDerivAt (rb_node α β δ W p z N K₂)
      (-(1 / (W - k)) + β * ∑ i, p i * ((rb_MPK α (z i) k (N i) + (1 - δ)) /
        (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))) k := by
    have h0 : HasDerivAt (fun k => Real.log (W - k)) (-(1 / (W - k))) k := by
      have := ((hasDerivAt_id k).const_sub W).log hc0.ne'
      convert this using 1
      · rfl
      · exact (neg_div _ _).symm
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      ((hdi i).log (hc1 i).ne').const_mul (p i))
    convert h0.add (hs.const_mul β) using 1
    · funext k'
      simp [rb_node]
  have hev : ∀ᶠ k' in nhds k, ∀ i, 0 < rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i :=
    Filter.eventually_all.2 fun i => (hdi i).continuousAt.eventually (lt_mem_nhds (hc1 i))
  have hcW : ∀ᶠ k' in nhds k, 0 < W - k' :=
    ((continuous_const.sub continuous_id).continuousAt (x := k)).eventually (lt_mem_nhds hc0)
  have hloc : IsLocalMax (rb_node α β δ W p z N K₂) k := by
    filter_upwards [lt_mem_nhds hk, hcW, hev] with k' h1 h2 h3 using hmax k' h1 h2 h3
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [eq_14_26_node]
  rw [Finset.mul_sum] at h0
  rw [show (1 / (W - k)) = ∑ i, β * (p i * ((rb_MPK α (z i) k (N i) + (1 - δ)) /
      (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))) by linarith]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The shock process (14.25) and the Solow residual -/

/-- Miao, (14.25), p. 472: `ln z_t = ρ ln z_{t−1} + σε_t`, started from `ln z_0`. -/
noncomputable def rb_lnz (ρ σ lnz0 : ℝ) (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => lnz0
  | t + 1 => ρ * rb_lnz ρ σ lnz0 ε t + σ * ε (t + 1)

/-- Miao, (14.25) iterated: `ln z_t = ρᵗ ln z_0 + σ∑_{s<t} ρ^{t−1−s}ε_{s+1}`. -/
theorem eq_14_25_iter (ρ σ lnz0 : ℝ) (ε : ℕ → ℝ) (t : ℕ) :
    rb_lnz ρ σ lnz0 ε t =
      ρ ^ t * lnz0 + σ * ∑ s ∈ Finset.range t, ρ ^ (t - 1 - s) * ε (s + 1) := by
  induction t with
  | zero => simp [rb_lnz]
  | succ t ih =>
    rw [rb_lnz, ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have : ∀ s ∈ Finset.range t, ρ ^ (t - s) * ε (s + 1) =
        ρ * (ρ ^ (t - 1 - s) * ε (s + 1)) := fun s hs => by
      have hs' := Finset.mem_range.1 hs
      obtain ⟨j, rfl⟩ : ∃ j, t = s + 1 + j := ⟨t - (s + 1), by omega⟩
      rw [show s + 1 + j - 1 - s = j by omega, show s + 1 + j - s = j + 1 by omega]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring

/-- Miao, p. 482: in the model the Solow residual `SR_t = ln Y_t − α ln K_t − (1 − α) ln N_t`
equals `ln z_t`. -/
theorem rb_solow_residual {α z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    Real.log (rb_Y α z K N) - α * Real.log K - (1 - α) * Real.log N = Real.log z := by
  have hKa := Real.rpow_pos_of_pos hK α
  have hNa := Real.rpow_pos_of_pos hN (1 - α)
  rw [rb_Y, Real.log_mul (by positivity) hNa.ne', Real.log_mul hz.ne' hKa.ne',
    Real.log_rpow hK, Real.log_rpow hN]
  ring

end Miao.NeoclassicalGrowth
