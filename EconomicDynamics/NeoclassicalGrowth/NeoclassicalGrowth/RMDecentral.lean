/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RMPlanner
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.BigOperators.Field

/-!
# Decentralisations of the basic Ramsey model

Miao, §14.1.1, pp. 456–467. Per-capita sequences `c, i, n, k`, aggregates `C, I, N, K`,
technology `A_t = g_aᵗ`, population `gₙᵗ`. Partial derivatives of `F` are `F_K, F_N` (in capital
and in effective labour). Equilibria are described by the first-order conditions the text
derives; the necessity of the planner's conditions is proved in `RMPlanner`.

**Arrow–Debreu equilibrium** (pp. 457–460). The household's first-order conditions
`βᵗu_c = λq_t⁰`, `−βᵗu_n = λq_t⁰w_t`, `q_t⁰ = q_{t+1}⁰(R^k_{t+1} + 1 − δ)` (`RMADFOC`) imply the
Euler equation (14.7) and (14.8) (`rm_ad_euler`); conversely (14.7)–(14.8) give Arrow–Debreu
prices `q_t⁰ = βᵗu_c(c_t, n_t)/λ` (`rm_ad_of_hh`), and the two transversality conditions
`lim q_t⁰k_{t+1} = 0` and (14.9) are then equivalent (`rm_ad_tvc_iff`). The firm's first-order
conditions (14.3) follow from profit maximisation (`eq_14_3`), and firms make zero profit
(`rm_zero_profit` in `RMBasics`), so `Π = 0`.

**Households own capital** (pp. 460–461): the system (14.7), (14.8), (14.3), (14.4)
(`RMHHFOC`, `RMFirmFOC`, `RMClear`). Market clearing implies the per-capita accumulation
equation (14.2) and resource constraint (`rm_clear_percapita`).

**Firms own capital** (pp. 461–464): the asset-pricing equation (14.11) (`eq_14_11`), its forward
solution (14.12) under the no-bubble condition (14.13) (`eq_14_12`), the derivation of (14.13)
from the household's transversality condition (`eq_14_13`), the pricing kernel
`M_{t,t+j} = βʲu_c(c_{t+j}, n_{t+j})/u_c(c_t, n_t)` (`rmKernel`, `rm_kernel_zero`,
`rm_kernel_mul`), the firm's first-order condition for capital (`rm_firm_capital_foc`), the
equivalence of (14.14) with `Q ≡ 1` and (14.7) (`eq_14_14_iff_eq_14_7`, so the two sequential
arrangements have the same allocations), and the stock return `V_{t+1}/(V_t − D_t) =
u_c(c_t)/(βu_c(c_{t+1})) = R^k_{t+1} + 1 − δ` (`rm_stock_return`).

**Social planner** (pp. 464–465): competitive allocations satisfy the planner's first-order
conditions (`rm_ce_planner`: they are Pareto optimal in the first-order sense), and the planner's
allocation is supported by the prices `R^k_t = F_K`, `w_t = A_tF_N`, `q_t⁰ = βᵗu_c/u_c(c₀)`
(`rm_planner_ce`). With KPR utility the planner's conditions are equivalent to the detrended
system of p. 465, `g_a^σu_c(c̃_t, n_t) = βu_c(c̃_{t+1}, n_{t+1})[F_K(k̃_{t+1}, n_{t+1}) + 1 − δ]`
etc. (`rm_detrend_planner`), and the detrended prices are `R^k_t = F_K(k̃_t, n_t)`,
`w̃_t = F_N(k̃_t, n_t)` (`rm_detrend_prices`).

**Recursive competitive equilibrium** (pp. 465–467): with `g_a = gₙ = 1`, the household's
first-order and envelope conditions and the consistency conditions generate sequences that
satisfy the sequential equilibrium conditions (`rm_rce_sequential`).

**Correction.** The detrended competitive system printed on pp. 459–460 has
`u_c(c̃_t, n_t) = βu_c(c̃_{t+1}, n_{t+1})(R^k_{t+1} + 1 − δ)`; detrending (14.7) with KPR utility
gives the factor `g_a^σ` on the left, as in the planner's detrended system on p. 465. With the
true equation the printed one forces `g_a^σ = 1` (`rm_detrend_euler_misprint`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### Arrow–Debreu and sequential household conditions -/

/-- The household's sequential first-order conditions (14.7)–(14.8). -/
def RMHHFOC (uc un : ℝ → ℝ → ℝ) (β δ : ℝ) (c n Rk w : ℕ → ℝ) : Prop :=
  ∀ t, uc (c t) (n t) = β * uc (c (t + 1)) (n (t + 1)) * (Rk (t + 1) + 1 - δ) ∧
    -un (c t) (n t) / uc (c t) (n t) = w t

/-- The Arrow–Debreu household's first-order conditions (Miao, p. 458). -/
def RMADFOC (uc un : ℝ → ℝ → ℝ) (β δ lam : ℝ) (c n q Rk w : ℕ → ℝ) : Prop :=
  ∀ t, β ^ t * uc (c t) (n t) = lam * q t ∧ -(β ^ t * un (c t) (n t)) = lam * q t * w t ∧
    q t = q (t + 1) * (Rk (t + 1) + 1 - δ)

/-- Miao, p. 459–461: the Arrow–Debreu first-order conditions imply (14.7) and (14.8). -/
theorem rm_ad_euler {uc un : ℝ → ℝ → ℝ} {β δ lam : ℝ} {c n q Rk w : ℕ → ℝ} (hβ : 0 < β)
    (huc : ∀ t, uc (c t) (n t) ≠ 0) (h : RMADFOC uc un β δ lam c n q Rk w) :
    RMHHFOC uc un β δ c n Rk w := by
  intro t
  obtain ⟨h1, h2, h3⟩ := h t
  obtain ⟨h1', -, -⟩ := h (t + 1)
  have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
  refine ⟨?_, ?_⟩
  · have : β ^ t * uc (c t) (n t) =
        β ^ t * (β * uc (c (t + 1)) (n (t + 1)) * (Rk (t + 1) + 1 - δ)) := by
      rw [pow_succ] at h1'
      linear_combination h1 + lam * h3 - (Rk (t + 1) + 1 - δ) * h1'
    exact mul_left_cancel₀ hb this
  · rw [div_eq_iff (huc t)]
    have : β ^ t * (-un (c t) (n t)) = β ^ t * (w t * uc (c t) (n t)) := by
      linear_combination h2 - w t * h1
    exact mul_left_cancel₀ hb this

/-- Miao, p. 461 ("the equilibrium system is identical"): conversely, (14.7)–(14.8) and any
`λ ≠ 0` give Arrow–Debreu prices `q_t⁰ = βᵗu_c(c_t, n_t)/λ` satisfying the Arrow–Debreu
first-order conditions. -/
theorem rm_ad_of_hh {uc un : ℝ → ℝ → ℝ} {β δ lam : ℝ} {c n Rk w : ℕ → ℝ} (hlam : lam ≠ 0)
    (huc : ∀ t, uc (c t) (n t) ≠ 0) (h : RMHHFOC uc un β δ c n Rk w) :
    RMADFOC uc un β δ lam c n (fun t => β ^ t * uc (c t) (n t) / lam) Rk w := by
  intro t
  obtain ⟨h1, h2⟩ := h t
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [div_eq_iff (huc t)] at h2
    field_simp
    linear_combination β ^ t * h2
  · simp only [pow_succ]
    rw [h1]
    field_simp

/-- Miao, pp. 458, 461: with `q_t⁰ = βᵗu_c/λ`, the Arrow–Debreu transversality condition
`lim q_t⁰k_{t+1} = 0` is equivalent to (14.9). -/
theorem rm_ad_tvc_iff {uc : ℝ → ℝ → ℝ} {β lam : ℝ} {c n k : ℕ → ℝ} (hlam : lam ≠ 0) :
    Tendsto (fun t => β ^ t * uc (c t) (n t) / lam * k (t + 1)) atTop (𝓝 0) ↔
      Tendsto (fun t => β ^ t * uc (c t) (n t) * k (t + 1)) atTop (𝓝 0) := by
  constructor
  · intro h
    have := h.const_mul lam
    simp only [mul_zero] at this
    refine this.congr (fun t => ?_)
    field_simp
  · intro h
    have := h.div_const lam
    simp only [zero_div] at this
    refine this.congr (fun t => ?_)
    ring

/-! ### Firms and market clearing -/

/-- The firm's first-order conditions (14.3) on aggregates, `A_t = g_aᵗ`. -/
def RMFirmFOC (FK FN : ℝ → ℝ → ℝ) (ga : ℝ) (K N Rk w : ℕ → ℝ) : Prop :=
  ∀ t, FK (K t) (ga ^ t * N t) = Rk t ∧ ga ^ t * FN (K t) (ga ^ t * N t) = w t

/-- **(14.3)** (Miao, p. 458): if the firm's profit `F(K, AN) − R^kK − wN` is at a local maximum
in `K` and in `N` at `(K, N)`, and `F` has partial derivatives `F_K`, `F_N` there, then
`F_K(K, AN) = R^k` and `AF_N(K, AN) = w`. -/
theorem eq_14_3 {F FK FN : ℝ → ℝ → ℝ} {A K N Rk w : ℝ}
    (hK : HasDerivAt (fun x => F x (A * N)) (FK K (A * N)) K)
    (hN : HasDerivAt (fun y => F K y) (FN K (A * N)) (A * N))
    (hmaxK : IsLocalMax (fun x => F x (A * N) - Rk * x - w * N) K)
    (hmaxN : IsLocalMax (fun y => F K (A * y) - Rk * K - w * y) N) :
    FK K (A * N) = Rk ∧ A * FN K (A * N) = w := by
  have dK : HasDerivAt (fun x => F x (A * N) - Rk * x - w * N) (FK K (A * N) - Rk * 1) K :=
    (hK.sub ((hasDerivAt_id K).const_mul Rk)).sub_const _
  have hl : HasDerivAt (fun y => A * y) A N := by simpa using (hasDerivAt_id N).const_mul A
  have dN : HasDerivAt (fun y => F K (A * y) - Rk * K - w * y)
      (FN K (A * N) * A - w * 1) N :=
    ((hN.comp N hl).sub_const _).sub ((hasDerivAt_id N).const_mul w)
  have e1 := hmaxK.hasDerivAt_eq_zero dK
  have e2 := hmaxN.hasDerivAt_eq_zero dN
  constructor <;> linarith

/-- Market clearing (14.4a)–(14.4d). -/
def RMClear (F : ℝ → ℝ → ℝ) (ga gn δ : ℝ) (c i n k C I N K : ℕ → ℝ) : Prop :=
  ∀ t, C t = gn ^ t * c t ∧ K t = gn ^ t * k t ∧ I t = gn ^ t * i t ∧ N t = gn ^ t * n t ∧
    K (t + 1) = (1 - δ) * K t + I t ∧ C t + I t = F (K t) (ga ^ t * N t)

/-- Miao, (14.2) and (14.4): market clearing implies the per-capita accumulation equation
`gₙk_{t+1} = (1 − δ)k_t + i_t` and resource constraint `c_t + i_t = F(k_t, A_tn_t)`. -/
theorem rm_clear_percapita {F : ℝ → ℝ → ℝ} (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    {ga gn δ : ℝ} (hgn : 0 < gn) {c i n k C I N K : ℕ → ℝ}
    (h : RMClear F ga gn δ c i n k C I N K) (t : ℕ) :
    gn * k (t + 1) = (1 - δ) * k t + i t ∧ c t + i t = F (k t) (ga ^ t * n t) := by
  obtain ⟨hC, hK, hI, hN, hacc, hres⟩ := h t
  have hK1 := (h (t + 1)).2.1
  have hs : (0 : ℝ) < gn ^ t := pow_pos hgn t
  refine ⟨?_, ?_⟩
  · rw [hK1, hK, hI, pow_succ] at hacc
    have : gn ^ t * (gn * k (t + 1)) = gn ^ t * ((1 - δ) * k t + i t) := by linarith
    exact mul_left_cancel₀ hs.ne' this
  · rw [hC, hI, hK, hN] at hres
    exact (rm_planner_resource (fun s x y hs => hhom s x y hs) hgn t).1 hres

/-! ### The planner's conditions and the welfare theorems -/

/-- The planner's first-order conditions in per-capita terms (Miao, p. 464, with the
intratemporal condition corrected to `−u_n/u_c = A_tF_N`), the resource constraint and (14.2). -/
def RMPlannerFOC (uc un F FK FN : ℝ → ℝ → ℝ) (β ga gn δ : ℝ) (c i n k : ℕ → ℝ) : Prop :=
  ∀ t, uc (c t) (n t) =
      β * uc (c (t + 1)) (n (t + 1)) * (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + 1 - δ) ∧
    -un (c t) (n t) / uc (c t) (n t) = ga ^ t * FN (k t) (ga ^ t * n t) ∧
    c t + i t = F (k t) (ga ^ t * n t) ∧ gn * k (t + 1) = (1 - δ) * k t + i t

/-- **Competitive allocations are Pareto optimal** (Miao, p. 465): an allocation satisfying the
sequential equilibrium conditions (14.7), (14.8), (14.3), (14.4) satisfies the planner's
first-order conditions (`F_K`, `F_N` are homogeneous of degree zero, `k, n > 0`). -/
theorem rm_ce_planner {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ : ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (hgn : 0 < gn) (hga : 0 < ga) {c i n k C I N K Rk w : ℕ → ℝ}
    (hk : ∀ t, 0 < k t) (hn : ∀ t, 0 < n t)
    (hhh : RMHHFOC uc un β δ c n Rk w) (hfirm : RMFirmFOC FK FN ga K N Rk w)
    (hcl : RMClear F ga gn δ c i n k C I N K) : RMPlannerFOC uc un F FK FN β ga gn δ c i n k := by
  have hpr : ∀ t, FK (K t) (ga ^ t * N t) = FK (k t) (ga ^ t * n t) ∧
      FN (K t) (ga ^ t * N t) = FN (k t) (ga ^ t * n t) := by
    intro t
    obtain ⟨-, hK, -, hN, -, -⟩ := hcl t
    have he : ga ^ t * N t = gn ^ t * (ga ^ t * n t) := by rw [hN]; ring
    have hs := pow_pos hgn t
    have hy := mul_pos (pow_pos hga t) (hn t)
    rw [he, hK]
    exact ⟨hFK _ _ _ hs (hk t) hy, hFN _ _ _ hs (hk t) hy⟩
  intro t
  obtain ⟨hacc, hres⟩ := rm_clear_percapita hhom hgn hcl t
  refine ⟨?_, ?_, hres, hacc⟩
  · rw [(hhh t).1, ← (hfirm (t + 1)).1, (hpr (t + 1)).1]
  · rw [(hhh t).2, ← (hfirm t).2, (hpr t).2]

/-- **The planner's allocation is an equilibrium** (Miao, p. 465, "conversely, we can also find
equilibrium prices"): an allocation satisfying the planner's conditions, with
`R^k_t = F_K(k_t, A_tn_t)`, `w_t = A_tF_N(k_t, A_tn_t)` and the aggregates `gₙᵗ ×` per capita,
satisfies (14.7), (14.8), (14.3), (14.4), and the Arrow–Debreu conditions with
`q_t⁰ = βᵗu_c(c_t, n_t)/u_c(c₀, n₀)`. -/
theorem rm_planner_ce {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ : ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (hgn : 0 < gn) (hga : 0 < ga) {c i n k : ℕ → ℝ} (hk : ∀ t, 0 < k t) (hn : ∀ t, 0 < n t)
    (huc : ∀ t, uc (c t) (n t) ≠ 0) (h : RMPlannerFOC uc un F FK FN β ga gn δ c i n k) :
    let Rk := fun t => FK (k t) (ga ^ t * n t)
    let w := fun t => ga ^ t * FN (k t) (ga ^ t * n t)
    RMHHFOC uc un β δ c n Rk w ∧
      RMFirmFOC FK FN ga (fun t => gn ^ t * k t) (fun t => gn ^ t * n t) Rk w ∧
      RMClear F ga gn δ c i n k (fun t => gn ^ t * c t) (fun t => gn ^ t * i t)
        (fun t => gn ^ t * n t) (fun t => gn ^ t * k t) ∧
      RMADFOC uc un β δ (uc (c 0) (n 0)) c n
        (fun t => β ^ t * uc (c t) (n t) / uc (c 0) (n 0)) Rk w := by
  intro Rk w
  have hhh : RMHHFOC uc un β δ c n Rk w := fun t => ⟨(h t).1, (h t).2.1⟩
  refine ⟨hhh, fun t => ?_, fun t => ?_, rm_ad_of_hh (huc 0) huc hhh⟩
  · have he : ga ^ t * (gn ^ t * n t) = gn ^ t * (ga ^ t * n t) := by ring
    have hs := pow_pos hgn t
    have hy := mul_pos (pow_pos hga t) (hn t)
    rw [he]
    exact ⟨hFK _ _ _ hs (hk t) hy, by rw [hFN _ _ _ hs (hk t) hy]⟩
  · obtain ⟨-, -, hres, hacc⟩ := h t
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change gn ^ (t + 1) * k (t + 1) = (1 - δ) * (gn ^ t * k t) + gn ^ t * i t
      rw [pow_succ, mul_assoc, hacc]; ring
    · rw [show ga ^ t * (gn ^ t * n t) = gn ^ t * (ga ^ t * n t) by ring,
        hhom _ _ _ (pow_pos hgn t), ← hres]
      ring

/-! ### Detrending with KPR utility -/

/-- The detrended planner's system (Miao, p. 465): `g_a^σu_c(c̃_t, n_t) =
βu_c(c̃_{t+1}, n_{t+1})[F_K(k̃_{t+1}, n_{t+1}) + 1 − δ]`, `−u_n/u_c = F_N(k̃_t, n_t)`,
`c̃_t + ı̃_t = F(k̃_t, n_t)`, `gₙg_ak̃_{t+1} = (1 − δ)k̃_t + ı̃_t`. -/
def RMDetrendedFOC (uc un F FK FN : ℝ → ℝ → ℝ) (β ga gn δ σ : ℝ) (c i n k : ℕ → ℝ) : Prop :=
  ∀ t, ga ^ σ * uc (c t) (n t) =
      β * uc (c (t + 1)) (n (t + 1)) * (FK (k (t + 1)) (n (t + 1)) + 1 - δ) ∧
    -un (c t) (n t) / uc (c t) (n t) = FN (k t) (n t) ∧
    c t + i t = F (k t) (n t) ∧ gn * ga * k (t + 1) = (1 - δ) * k t + i t

/-- Miao, p. 465: with the KPR scaling `u_c(λc, n) = λ^{−σ}u_c(c, n)`, `u_n(λc, n) =
λ^{1−σ}u_n(c, n)` (true for (14.5), `rm_kpr_uc_scale`, `rm_kpr_un_scale`, and for (14.6) with
`σ = 1`) and constant returns, the planner's conditions for `x_t = g_aᵗx̃_t` (`x = c, i, k`) are
equivalent to the detrended system. -/
theorem rm_detrend_planner {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ σ : ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (huc : ∀ l x y, 0 < l → 0 < x → uc (l * x) y = l ^ (-σ) * uc x y)
    (hun : ∀ l x y, 0 < l → 0 < x → un (l * x) y = l ^ (1 - σ) * un x y)
    (hga : 0 < ga) {c i n k : ℕ → ℝ} (hc : ∀ t, 0 < c t) (hk : ∀ t, 0 < k t)
    (hn : ∀ t, 0 < n t) (hucp : ∀ t, uc (c t) (n t) ≠ 0) :
    RMPlannerFOC uc un F FK FN β ga gn δ (fun t => ga ^ t * c t) (fun t => ga ^ t * i t) n
        (fun t => ga ^ t * k t) ↔ RMDetrendedFOC uc un F FK FN β ga gn δ σ c i n k := by
  have hA : ∀ t, (0 : ℝ) < ga ^ t := fun t => pow_pos hga t
  have hp : ∀ t : ℕ, (ga ^ t) ^ (-σ) ≠ 0 := fun t => (Real.rpow_pos_of_pos (hA t) _).ne'
  have hsucc : ∀ t : ℕ, (ga ^ (t + 1)) ^ (-σ) = (ga ^ t) ^ (-σ) * ga ^ (-σ) := fun t => by
    rw [pow_succ, Real.mul_rpow (hA t).le hga.le]
  have hgs : ga ^ σ * ga ^ (-σ) = 1 := by
    rw [← Real.rpow_add hga]; simp
  have hrat : ∀ t : ℕ, (ga ^ t) ^ (1 - σ) = ga ^ t * (ga ^ t) ^ (-σ) := fun t => by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add (hA t), Real.rpow_one]
  have hK : ∀ t, FK (ga ^ t * k t) (ga ^ t * n t) = FK (k t) (n t) :=
    fun t => hFK _ _ _ (hA t) (hk t) (hn t)
  have hN : ∀ t, FN (ga ^ t * k t) (ga ^ t * n t) = FN (k t) (n t) :=
    fun t => hFN _ _ _ (hA t) (hk t) (hn t)
  have hF : ∀ t, F (ga ^ t * k t) (ga ^ t * n t) = ga ^ t * F (k t) (n t) :=
    fun t => hhom _ _ _ (hA t)
  have hu : ∀ t, uc (ga ^ t * c t) (n t) = (ga ^ t) ^ (-σ) * uc (c t) (n t) :=
    fun t => huc _ _ _ (hA t) (hc t)
  have hv : ∀ t, un (ga ^ t * c t) (n t) = (ga ^ t) ^ (1 - σ) * un (c t) (n t) :=
    fun t => hun _ _ _ (hA t) (hc t)
  have hmrs : ∀ t, -un (ga ^ t * c t) (n t) / uc (ga ^ t * c t) (n t) =
      ga ^ t * (-un (c t) (n t) / uc (c t) (n t)) := fun t => by
    rw [hu, hv, hrat]
    have := hp t
    have := hucp t
    field_simp
  apply forall_congr'
  intro t
  beta_reduce
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [hu, hu, hK, hsucc]
    constructor
    · intro h
      have : (ga ^ t) ^ (-σ) * (ga ^ σ * uc (c t) (n t)) = (ga ^ t) ^ (-σ) *
          (β * uc (c (t + 1)) (n (t + 1)) * (FK (k (t + 1)) (n (t + 1)) + 1 - δ)) := by
        linear_combination ga ^ σ * h + (ga ^ t) ^ (-σ) * β * uc (c (t + 1)) (n (t + 1)) *
          (FK (k (t + 1)) (n (t + 1)) + 1 - δ) * hgs
      exact mul_left_cancel₀ (hp t) this
    · intro h
      linear_combination (ga ^ t) ^ (-σ) * ga ^ (-σ) * h - (ga ^ t) ^ (-σ) * uc (c t) (n t) * hgs
  · rw [hmrs, hN]
    constructor
    · intro h; exact mul_left_cancel₀ (hA t).ne' h
    · intro h; rw [h]
  · rw [hF]
    constructor
    · intro h
      have : ga ^ t * (c t + i t) = ga ^ t * F (k t) (n t) := by linarith
      exact mul_left_cancel₀ (hA t).ne' this
    · intro h; rw [← h]; ring
  · rw [pow_succ]
    constructor
    · intro h
      have : ga ^ t * (gn * ga * k (t + 1)) = ga ^ t * ((1 - δ) * k t + i t) := by linarith
      exact mul_left_cancel₀ (hA t).ne' this
    · intro h
      linear_combination ga ^ t * h

/-- Miao, p. 460: detrended prices. With `K_t = gₙᵗg_aᵗk̃_t`, `N_t = gₙᵗn_t`, (14.3) gives
`R^k_t = F_K(k̃_t, n_t)` and `w̃_t = w_t/g_aᵗ = F_N(k̃_t, n_t)`. -/
theorem rm_detrend_prices {FK FN : ℝ → ℝ → ℝ}
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    {ga gn : ℝ} (hga : 0 < ga) (hgn : 0 < gn) {kt n : ℝ} (hk : 0 < kt) (hn : 0 < n) (t : ℕ) :
    FK (gn ^ t * ga ^ t * kt) (ga ^ t * (gn ^ t * n)) = FK kt n ∧
      ga ^ t * FN (gn ^ t * ga ^ t * kt) (ga ^ t * (gn ^ t * n)) / ga ^ t = FN kt n := by
  have hs : (0 : ℝ) < gn ^ t * ga ^ t := mul_pos (pow_pos hgn t) (pow_pos hga t)
  have he : ga ^ t * (gn ^ t * n) = (gn ^ t * ga ^ t) * n := by ring
  rw [he, hFK _ _ _ hs hk hn, hFN _ _ _ hs hk hn]
  exact ⟨rfl, by field_simp [(pow_pos hga t).ne']⟩

/-- Correction to Miao, pp. 459–460: the printed detrended Euler equation
`u_c(c̃_t) = βu_c(c̃_{t+1})(R^k_{t+1} + 1 − δ)` and the true one
`g_a^σu_c(c̃_t) = βu_c(c̃_{t+1})(R^k_{t+1} + 1 − δ)` hold together only if `g_a^σ = 1`. -/
theorem rm_detrend_euler_misprint {u0 u1 β R δ gs : ℝ} (hu : u0 ≠ 0)
    (htrue : gs * u0 = β * u1 * (R + 1 - δ)) (hprinted : u0 = β * u1 * (R + 1 - δ)) : gs = 1 := by
  have : (gs - 1) * u0 = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_right hu
  linarith

/-! ### Firms own capital -/

/-- **(14.11)** (Miao, p. 462): the first-order condition for share holdings
`u_c(c_t)(V_t − D_t) = βu_c(c_{t+1})V_{t+1}` gives `V_t = D_t + βu_c(c_{t+1})/u_c(c_t) V_{t+1}`. -/
theorem eq_14_11 {m0 m1 V0 V1 D0 β : ℝ} (hm : m0 ≠ 0) (h : m0 * (V0 - D0) = β * m1 * V1) :
    V0 = D0 + β * m1 / m0 * V1 := by
  field_simp
  linarith

/-- The partial-sum identity behind (14.12): iterating (14.11) `T` times,
`u_c(c_t)V_t = ∑_{j<T} βʲu_c(c_{t+j})D_{t+j} + β^Tu_c(c_{t+T})V_{t+T}`. -/
theorem rm_value_partial {m V D : ℕ → ℝ} {β : ℝ}
    (h : ∀ s, m s * (V s - D s) = β * m (s + 1) * V (s + 1)) (t T : ℕ) :
    m t * V t = ∑ j ∈ Finset.range T, β ^ j * m (t + j) * D (t + j) +
      β ^ T * m (t + T) * V (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have := h (t + T)
    rw [show t + (T + 1) = t + T + 1 by ring, pow_succ]
    linear_combination β ^ T * this

/-- **(14.12)** (Miao, p. 462): if (14.11) holds at every date and the no-bubble condition
(14.13) holds, then `V_t = ∑_{j≥0} βʲu_c(c_{t+j})/u_c(c_t) D_{t+j}` (as the limit of partial
sums). -/
theorem eq_14_12 {m V D : ℕ → ℝ} {β : ℝ} (hm : ∀ s, m s ≠ 0)
    (h : ∀ s, m s * (V s - D s) = β * m (s + 1) * V (s + 1)) (t : ℕ)
    (hnb : Tendsto (fun j => β ^ j * m (t + j) * V (t + j)) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * m (t + j) / m t * D (t + j)) atTop
      (𝓝 (V t)) := by
  have hT : ∀ T, ∑ j ∈ Finset.range T, β ^ j * m (t + j) / m t * D (t + j) =
      V t - β ^ T * m (t + T) * V (t + T) / m t := by
    intro T
    have := rm_value_partial h t T
    have hsum : ∑ j ∈ Finset.range T, β ^ j * m (t + j) / m t * D (t + j) =
        (∑ j ∈ Finset.range T, β ^ j * m (t + j) * D (t + j)) / m t := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum]
    field_simp [hm t]
    linarith
  simp only [hT]
  have := (hnb.div_const (m t)).const_sub (V t)
  simpa using this

/-- **(14.13)** (Miao, pp. 462–463): the household's transversality condition
`lim βᵗu_c(c_t)ψ_{t+1}(V_t − D_t) = 0`, `ψ ≡ 1` and the share first-order condition give the
no-bubble condition `lim_j βʲu_c(c_{t+j})V_{t+j} = 0` at every date `t`. -/
theorem eq_14_13 {m V D ψ : ℕ → ℝ} {β : ℝ} (hβ : 0 < β) (hψ : ∀ s, ψ s = 1)
    (h : ∀ s, m s * (V s - D s) = β * m (s + 1) * V (s + 1))
    (htvc : Tendsto (fun s => β ^ s * m s * ψ (s + 1) * (V s - D s)) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun j => β ^ j * m (t + j) * V (t + j)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s => β ^ (s + 1) * m (s + 1) * V (s + 1)) atTop (𝓝 0) := by
    refine htvc.congr (fun s => ?_)
    rw [hψ, mul_one, mul_assoc, h s, pow_succ]; ring
  have h2 : Tendsto (fun s => β ^ s * m s * V s) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 h1
  have h3 := ((tendsto_add_atTop_iff_nat t).2 h2).const_mul (β ^ t)⁻¹
  simp only [mul_zero] at h3
  refine h3.congr (fun j => ?_)
  rw [show j + t = t + j by ring, pow_add]
  field_simp [(pow_pos hβ t).ne']

/-- The pricing kernel `M_{t,t+j} = βʲu_c(c_{t+j})/u_c(c_t)` (Miao, p. 463). -/
noncomputable def rmKernel (β : ℝ) (m : ℕ → ℝ) (t j : ℕ) : ℝ :=
  β ^ j * m (t + j) / m t

/-- Miao, p. 462: `M_{t,t} = 1`. -/
theorem rm_kernel_zero (β : ℝ) {m : ℕ → ℝ} (t : ℕ) (hm : m t ≠ 0) : rmKernel β m t 0 = 1 := by
  simp [rmKernel, hm]

/-- The kernel is consistent across dates: `M_{t,t+j}M_{t+j,t+j+l} = M_{t,t+j+l}`. -/
theorem rm_kernel_mul (β : ℝ) {m : ℕ → ℝ} (hm : ∀ s, m s ≠ 0) (t j l : ℕ) :
    rmKernel β m t j * rmKernel β m (t + j) l = rmKernel β m t (j + l) := by
  simp only [rmKernel, pow_add, add_assoc]
  field_simp [hm (t + j)]

/-- Miao, (14.14), p. 463: the firm's first-order condition for `K_{t+1}`. If raising `K_{t+1}`
to `x` (financed by date-`t` dividends, paid back in date-`t+1` dividends
`F(x, A_{t+1}N_{t+1}) + (1 − δ)x`) leaves the value `−x + M_{t,t+1}[F(x, AN) + (1 − δ)x]` at a
local maximum at `K_{t+1}`, then `1 = M_{t,t+1}[F_K(K_{t+1}, A_{t+1}N_{t+1}) + 1 − δ]`, i.e.
(14.14) with `Q_t = Q_{t+1} = 1`. -/
theorem rm_firm_capital_foc {F FK : ℝ → ℝ → ℝ} {M δ K1 L1 : ℝ}
    (hF : HasDerivAt (fun x => F x L1) (FK K1 L1) K1)
    (hmax : IsLocalMax (fun x => -x + M * (F x L1 + (1 - δ) * x)) K1) :
    1 = M * (FK K1 L1 + (1 - δ) * 1) := by
  have hd : HasDerivAt (fun x => -x + M * (F x L1 + (1 - δ) * x))
      (-1 + M * (FK K1 L1 + (1 - δ) * 1)) K1 :=
    (hasDerivAt_id K1).neg.add ((hF.add ((hasDerivAt_id K1).const_mul (1 - δ))).const_mul M)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- Miao, p. 463: with `Q ≡ 1`, `M_{t,t+1} = βu_c(c_{t+1})/u_c(c_t)` and `R^k = F_K`, the firm's
condition (14.14) is equivalent to the household's Euler equation (14.7); so the arrangements
"households own capital" and "firms own capital" have the same equilibrium allocations. -/
theorem eq_14_14_iff_eq_14_7 {m0 m1 β FK δ : ℝ} (hm : m0 ≠ 0) :
    (1 = β * m1 / m0 * (FK + (1 - δ) * 1)) ↔ m0 = β * m1 * (FK + 1 - δ) := by
  constructor
  · intro h; field_simp at h; linarith
  · intro h; field_simp; linarith

/-- Miao, pp. 463–464: the stock return `V_{t+1}/(V_t − D_t) = u_c(c_t)/(βu_c(c_{t+1}))
= R^k_{t+1} + 1 − δ`, from the share first-order condition and (14.7). -/
theorem rm_stock_return {m0 m1 V0 V1 D0 β R δ : ℝ} (hβ : β ≠ 0) (hm1 : m1 ≠ 0)
    (hex : V0 - D0 ≠ 0) (h : m0 * (V0 - D0) = β * m1 * V1) (heul : m0 = β * m1 * (R + 1 - δ)) :
    V1 / (V0 - D0) = m0 / (β * m1) ∧ m0 / (β * m1) = R + 1 - δ := by
  refine ⟨?_, ?_⟩
  · rw [div_eq_div_iff hex (mul_ne_zero hβ hm1)]; linarith
  · rw [heul]; field_simp

/-! ### Recursive competitive equilibrium -/

/-- **Recursive competitive equilibrium generates a sequential equilibrium** (Miao, pp. 466–467,
`g_a = gₙ = 1`). Suppose the decision rules `g^c, g^n, g` and the law of motion `G` satisfy the
household's first-order conditions `u_c = βV_k(g(k, K), G(K))`, `−u_n = u_cW(K)`, the envelope
condition `V_k(k, K) = u_c(R^k(K) + 1 − δ)`, the price equations (14.15), and the consistency and
market-clearing conditions `g(K, K) = G(K)`, `G(K) − (1 − δ)K + C = F(K, N)`. Then the sequences
`K_{t+1} = G(K_t)`, `C_t = g^c(K_t, K_t)`, `N_t = g^n(K_t, K_t)` with prices `R^k(K_t)`, `W(K_t)`
satisfy (14.7), (14.8), (14.3) and the resource constraint. -/
theorem rm_rce_sequential {uc un F FK FN : ℝ → ℝ → ℝ} {Vk gc gnl g : ℝ → ℝ → ℝ}
    {G Rk W : ℝ → ℝ} {β δ : ℝ}
    (hfoc : ∀ k K, uc (gc k K) (gnl k K) = β * Vk (g k K) (G K))
    (hlab : ∀ k K, -un (gc k K) (gnl k K) = uc (gc k K) (gnl k K) * W K)
    (henv : ∀ k K, Vk k K = uc (gc k K) (gnl k K) * (Rk K + 1 - δ))
    (hprice : ∀ K, FK K (gnl K K) = Rk K ∧ FN K (gnl K K) = W K)
    (hcons : ∀ K, g K K = G K) (hres : ∀ K, G K - (1 - δ) * K + gc K K = F K (gnl K K))
    (huc : ∀ k K, uc (gc k K) (gnl k K) ≠ 0) (K : ℕ → ℝ) (hK : ∀ t, K (t + 1) = G (K t)) :
    let C := fun t => gc (K t) (K t)
    let N := fun t => gnl (K t) (K t)
    RMHHFOC uc un β δ C N (fun t => Rk (K t)) (fun t => W (K t)) ∧
      RMFirmFOC FK FN 1 K N (fun t => Rk (K t)) (fun t => W (K t)) ∧
      ∀ t, K (t + 1) - (1 - δ) * K t + C t = F (K t) (N t) := by
  intro C N
  refine ⟨fun t => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_⟩
  · simp only [C, N]
    rw [hfoc, hcons, ← hK, henv]
    ring
  · simp only [C, N]
    rw [div_eq_iff (huc _ _), hlab]; ring
  · simp only [one_pow, one_mul, N]
    exact ⟨(hprice _).1, (hprice _).2⟩
  · simp only [C, N]
    rw [hK, hres]

end Miao.NeoclassicalGrowth
