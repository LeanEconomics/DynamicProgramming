/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.Basics
import NewKeynesian.NKLogLinear
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The New Keynesian Phillips curve and the IS curve (Miao §19.1.7)

Miao, §19.1.7, pp. 624–627. The log-linear variables are random variables in a normed space
`V` with conditional expectations `E_t` (a `CondExpSystem`, as in Chapter 2); `δ = βθ`,
`|δ| < 1`. Present values are `PV_t(g) = ∑_k δ^kE_tg_{t+k}` (`nk_pv`), which equals
`E_t∑_k δ^kg_{t+k}` since `E_t` is continuous.

* (19.20): the "simplifying" step from the log-linearised (19.11) (`eq_19_20`).
* Plugging in (19.21): `P̂*_t(1 + b)/(1 − βθ) = E_t∑_k θ^kβ^k((1 + b)P̂_{t+k} + MĈ_{t+k})`
  (`nk_reset_plugged`); its recursive form
  `P̂*_t = (1 − βθ)(MĈ_t/(1 + b) + P̂_t) + βθE_tP̂*_{t+1}` (`nk_reset_recursive`, from the
  present-value recursion `nk_pv_rec`); the same for `q_t = P̂*_t − P̂_t` (`nk_q_recursive`).
* With (19.19): `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t` (`nk_pc_mc`).
* (19.23) (`eq_19_23`); with `Ŷ = Â + (1 − α)N̂` and the log-linear (19.18),
  `MĈ = ((ν + α + γ(1 − α))/(1 − α))(Ŷ − Ŷ^f)` (`nk_mc_gap`).
* (19.24), the New Keynesian Phillips curve, with the slope κ of (19.25) in both printed forms
  (`eq_19_24`, `nk_kappa`, `eq_19_25`, `nk_kappa_pos`).
* (19.27) from the definition of the natural rate (`eq_19_27`) and (19.28), the intertemporal
  IS curve (`eq_19_28`). The constant `ln β` is `ln β · 𝟙` for a fixed `F_0`-measurable unit
  `𝟙 ∈ V` (the constant random variable `1`).
-/

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The present value `PV_t(g) = ∑_k δ^kE_tg_{t+k}` (Miao, p. 621 with weights `(θβ)^k`). -/
noncomputable def nk_pv (E : CondExpSystem ℝ V) (δ : ℝ) (g : ℕ → V) (t : ℕ) : V :=
  ∑' k : ℕ, δ ^ k • E.E t (g (t + k))

omit [NormedSpace ℝ V] in
/-- A bounded sequence weighted by `δ^k`, `|δ| < 1`, is summable. -/
theorem nk_summable_geom [NormedSpace ℝ V] [CompleteSpace V] {δ : ℝ} (hδ : |δ| < 1)
    {f : ℕ → V} {C : ℝ} (hf : ∀ k, ‖f k‖ ≤ C) : Summable fun k => δ ^ k • f k :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg _) hδ).mul_right C)
    fun k => by
      rw [norm_smul, norm_pow, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf k) (pow_nonneg (abs_nonneg _) _)

/-- `∑_k δ^k • v = (1 − δ)⁻¹ • v` for `|δ| < 1`. -/
theorem nk_tsum_geom_smul {δ : ℝ} (hδ : |δ| < 1) (v : V) :
    ∑' k : ℕ, δ ^ k • v = (1 - δ)⁻¹ • v := by
  rw [(summable_geometric_of_abs_lt_one hδ).tsum_smul_const, tsum_geometric_of_abs_lt_one hδ]

/-- The present-value recursion (Miao, p. 625): for adapted bounded `g`,
`PV_t(g) = g_t + δE_tPV_{t+1}(g)`. -/
theorem nk_pv_rec [CompleteSpace V] (E : CondExpSystem ℝ V) {δ : ℝ} (hδ : |δ| < 1)
    {g : ℕ → V} {C : ℝ} (hg : ∀ t, ‖g t‖ ≤ C) (hga : ∀ t, E.E t (g t) = g t) (t : ℕ) :
    nk_pv E δ g t = g t + δ • E.E t (nk_pv E δ g (t + 1)) := by
  have hb : ∀ s k, ‖E.E s (g (s + k))‖ ≤ C := fun s k => (E.norm_apply_le _ _).trans (hg _)
  have hs := nk_summable_geom hδ (hb t)
  have hs1 := nk_summable_geom hδ (hb (t + 1))
  simp only [nk_pv]
  rw [(E.E t).map_tsum hs1, hs.tsum_eq_zero_add]
  simp only [map_smul, E.tower_le_apply (Nat.le_succ t), pow_zero, one_smul, add_zero, hga t]
  rw [← (nk_summable_geom hδ (fun k => (E.norm_apply_le t _).trans
    (hg (t + 1 + k)))).tsum_const_smul δ]
  congr 1
  refine tsum_congr fun k => ?_
  rw [smul_smul, pow_succ, mul_comm, show t + (k + 1) = t + 1 + k by omega]

/-- **(19.20)** (Miao, p. 624), the simplifying step. Divide the log-linearised (19.11) by the
common steady-state factor (`nk_loglin_reset_terms`): if for every `t`
`∑_k δ^kE_t(P̂*_t + (1 − γ)Ŷ_{t+k} + (ε − 1)P̂_{t+k}) =
 ∑_k δ^kE_t((1 − γ)Ŷ_{t+k} + εP̂_{t+k} + MĈ_{t+k|t})` with `P̂*` adapted and `Ŷ, P̂, MĈ`
bounded, then `P̂*_t/(1 − βθ) = ∑_k δ^kE_t(P̂_{t+k} + MĈ_{t+k|t})`, `δ = βθ`. -/
theorem eq_19_20 [CompleteSpace V] (E : CondExpSystem ℝ V) {δ γ ε : ℝ} (hδ : |δ| < 1)
    {ps y p : ℕ → V} {mkt : ℕ → ℕ → V} {C : ℝ} (hy : ∀ t, ‖y t‖ ≤ C) (hp : ∀ t, ‖p t‖ ≤ C)
    (hm : ∀ t k, ‖mkt t k‖ ≤ C) (hpsa : ∀ t, E.E t (ps t) = ps t)
    (hlin : ∀ t, ∑' k : ℕ, δ ^ k • E.E t (ps t + (1 - γ) • y (t + k) + (ε - 1) • p (t + k)) =
      ∑' k : ℕ, δ ^ k • E.E t ((1 - γ) • y (t + k) + ε • p (t + k) + mkt t k)) (t : ℕ) :
    (1 - δ)⁻¹ • ps t = ∑' k : ℕ, δ ^ k • E.E t (p (t + k) + mkt t k) := by
  set A : ℕ → V := fun k => δ ^ k • E.E t ((1 - γ) • y (t + k) + (ε - 1) • p (t + k))
  set B : ℕ → V := fun k => δ ^ k • E.E t (p (t + k) + mkt t k)
  have hA : Summable A := nk_summable_geom hδ (C := (|1 - γ| * C + |ε - 1| * C)) fun k => by
    refine (E.norm_apply_le _ _).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_)) <;>
      rw [norm_smul, Real.norm_eq_abs] <;> gcongr <;> simp_all
  have hB : Summable B := nk_summable_geom hδ (C := C + C) fun k =>
    (E.norm_apply_le _ _).trans ((norm_add_le _ _).trans (add_le_add (hp _) (hm _ _)))
  have hG : Summable fun k : ℕ => δ ^ k • ps t := nk_summable_geom hδ (C := ‖ps t‖) fun _ => le_rfl
  have hl : ∀ k, δ ^ k • E.E t (ps t + (1 - γ) • y (t + k) + (ε - 1) • p (t + k)) =
      δ ^ k • ps t + A k := fun k => by
    simp only [A, map_add, map_smul, hpsa t, add_assoc, smul_add]
  have hr : ∀ k, δ ^ k • E.E t ((1 - γ) • y (t + k) + ε • p (t + k) + mkt t k) =
      A k + B k := fun k => by
    simp only [A, B, map_add, map_smul, ← smul_add]
    congr 1
    module
  have h := hlin t
  simp only [hl, hr] at h
  rw [hG.tsum_add hA, hA.tsum_add hB, add_comm, add_left_cancel_iff, nk_tsum_geom_smul hδ] at h
  exact h

/-- Miao, p. 625: plugging (19.21) `MĈ_{t+k|t} = MĈ_{t+k} − b(P̂*_t − P̂_{t+k})` into (19.20):
`(1 + b)(1 − βθ)⁻¹P̂*_t = ∑_k δ^kE_t((1 + b)P̂_{t+k} + MĈ_{t+k})`. -/
theorem nk_reset_plugged [CompleteSpace V] (E : CondExpSystem ℝ V) {δ b : ℝ} (hδ : |δ| < 1)
    {ps p m : ℕ → V} {C : ℝ} (hp : ∀ t, ‖p t‖ ≤ C) (hmC : ∀ t, ‖m t‖ ≤ C)
    (hpsa : ∀ t, E.E t (ps t) = ps t) (t : ℕ)
    (h20 : (1 - δ)⁻¹ • ps t =
      ∑' k : ℕ, δ ^ k • E.E t (p (t + k) + (m (t + k) - b • (ps t - p (t + k))))) :
    (1 + b) • (1 - δ)⁻¹ • ps t = nk_pv E δ (fun s => (1 + b) • p s + m s) t := by
  set B : ℕ → V := fun k => δ ^ k • E.E t ((1 + b) • p (t + k) + m (t + k))
  have hB : Summable B := nk_summable_geom hδ (C := |1 + b| * C + C) fun k => by
    refine (E.norm_apply_le _ _).trans ((norm_add_le _ _).trans (add_le_add ?_ (hmC _)))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
  have hG : Summable fun k : ℕ => δ ^ k • (-(b • ps t)) :=
    nk_summable_geom hδ (C := ‖-(b • ps t)‖) fun _ => le_rfl
  have he : ∀ k, δ ^ k • E.E t (p (t + k) + (m (t + k) - b • (ps t - p (t + k)))) =
      B k + δ ^ k • (-(b • ps t)) := fun k => by
    simp only [B, map_add, map_sub, map_smul, hpsa t, ← smul_add]
    congr 1
    module
  simp only [he] at h20
  rw [hB.tsum_add hG, nk_tsum_geom_smul hδ] at h20
  simp only [nk_pv]
  change (1 + b) • (1 - δ)⁻¹ • ps t = ∑' k, B k
  rw [smul_comm]
  have : ∑' k, B k = (1 - δ)⁻¹ • ps t + (1 - δ)⁻¹ • (b • ps t) := by
    rw [h20]
    module
  rw [this]
  module

/-- Miao, p. 625: the recursive form of the reset price,
`P̂*_t = (1 − βθ)(MĈ_t/(1 + b) + P̂_t) + βθE_tP̂*_{t+1}` (`δ = βθ`, `1 + b ≠ 0`, `P̂`, `MĈ`
adapted and bounded). -/
theorem nk_reset_recursive [CompleteSpace V] (E : CondExpSystem ℝ V) {δ b : ℝ} (hδ : |δ| < 1)
    (hb : 1 + b ≠ 0) {ps p m : ℕ → V} {C : ℝ} (hp : ∀ t, ‖p t‖ ≤ C) (hmC : ∀ t, ‖m t‖ ≤ C)
    (hpa : ∀ t, E.E t (p t) = p t) (hma : ∀ t, E.E t (m t) = m t)
    (hpv : ∀ t, (1 + b) • (1 - δ)⁻¹ • ps t = nk_pv E δ (fun s => (1 + b) • p s + m s) t)
    (t : ℕ) : ps t = (1 - δ) • ((1 + b)⁻¹ • m t + p t) + δ • E.E t (ps (t + 1)) := by
  have hδ1 : 1 - δ ≠ 0 := by
    have := (abs_lt.1 hδ).2
    linarith
  have hgC : ∀ s, ‖(1 + b) • p s + m s‖ ≤ |1 + b| * C + C := fun s => by
    have h1 : ‖(1 + b) • p s‖ ≤ |1 + b| * C := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hp s) (abs_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add h1 (hmC s))
  have hrec := nk_pv_rec E hδ hgC (fun s => by simp only [map_add, map_smul, hpa, hma]) t
  rw [← hpv t, ← hpv (t + 1)] at hrec
  simp only [map_smul] at hrec
  have h2 : ps t = ((1 + b)⁻¹ * (1 - δ)) • ((1 + b) • p t + m t +
      δ • ((1 + b) • (1 - δ)⁻¹ • E.E t (ps (t + 1)))) := by
    rw [← hrec, smul_smul, smul_smul]
    have : (1 + b)⁻¹ * (1 - δ) * (1 + b) * (1 - δ)⁻¹ = 1 := by field_simp
    rw [this, one_smul]
  rw [h2]
  simp only [smul_add, smul_smul]
  match_scalars <;> field_simp

/-- Miao, p. 625: with `q_t = P̂*_t − P̂_t` and `P̂` adapted,
`q_t = ((1 − βθ)/(1 + b))MĈ_t + βθE_t(q_{t+1} + P̂_{t+1} − P̂_t)`. -/
theorem nk_q_recursive (E : CondExpSystem ℝ V) {δ b : ℝ} {ps p m : ℕ → V}
    (hpa : ∀ t, E.E t (p t) = p t) (t : ℕ)
    (h : ps t = (1 - δ) • ((1 + b)⁻¹ • m t + p t) + δ • E.E t (ps (t + 1))) :
    ps t - p t = ((1 - δ) / (1 + b)) • m t +
      δ • E.E t ((ps (t + 1) - p (t + 1)) + p (t + 1) - p t) := by
  simp only [map_sub, hpa t, sub_add_cancel]
  rw [h]
  match_scalars <;> ring

/-- Miao, p. 625: with (19.19) `q_t = θπ_t/(1 − θ)` and `π_{t+1} = P̂_{t+1} − P̂_t`, the
`q`-recursion gives `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t`. -/
theorem nk_pc_mc (E : CondExpSystem ℝ V) {β θ b : ℝ} (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1)
    {q p m pi : ℕ → V} (t : ℕ) (hq : ∀ s, q s = (θ / (1 - θ)) • pi s)
    (hpi : pi (t + 1) = p (t + 1) - p t)
    (h : q t = ((1 - β * θ) / (1 + b)) • m t +
      (β * θ) • E.E t (q (t + 1) + p (t + 1) - p t)) :
    pi t = β • E.E t (pi (t + 1)) + ((1 - β * θ) * (1 - θ) / (θ * (1 + b))) • m t := by
  have h1 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ1)
  rw [hq t, hq (t + 1), add_sub_assoc, ← hpi] at h
  have e : (θ / (1 - θ)) • pi (t + 1) + pi (t + 1) = (1 - θ)⁻¹ • pi (t + 1) := by
    match_scalars
    field_simp
    ring
  rw [e, map_smul] at h
  have h2 : pi t = ((1 - θ) / θ) • ((θ / (1 - θ)) • pi t) := by
    rw [smul_smul, div_mul_div_comm, mul_comm (1 - θ), div_self (mul_ne_zero hθ0 h1), one_smul]
  rw [h2, h]
  match_scalars <;> field_simp

/-- **(19.23)** (Miao, p. 625): from the log-linear (19.9), `MĈ = Ŵ − P̂ + (α/(1 − α))Ŷ −
(1/(1 − α))Â` (`nk_loglin_MC`), the log-linear (19.2), `Ŵ − P̂ = νN̂ + γĈ`
(`nk_loglin_19_2`), and `Ĉ = Ŷ`: `MĈ = νN̂ + γŶ + (α/(1 − α))Ŷ − (1/(1 − α))Â`. -/
theorem eq_19_23 {α ν γ : ℝ} {m w n c y a : V} (hm : m = w + (α / (1 - α)) • y - (1 / (1 - α)) • a)
    (hw : w = ν • n + γ • c) (hc : c = y) :
    m = ν • n + γ • y + (α / (1 - α)) • y - (1 / (1 - α)) • a := by
  rw [hm, hw, hc]

/-- Miao, p. 626: with `Ŷ = Â + (1 − α)N̂` (`nk_loglin_output`) and `Ŷ^f = ((1 + ν)/D)Â`
(`nk_loglin_19_18`), `D = γ(1 − α) + α + ν ≠ 0`, `α ≠ 1`, (19.23) becomes
`MĈ = (D/(1 − α))Ŷ − ((ν + 1)/(1 − α))Â = (D/(1 − α))(Ŷ − Ŷ^f)`. -/
theorem nk_mc_gap {α ν γ : ℝ} (hα : α ≠ 1) (hD : γ * (1 - α) + α + ν ≠ 0) {m n y a yf : V}
    (h23 : m = ν • n + γ • y + (α / (1 - α)) • y - (1 / (1 - α)) • a)
    (hy : y = a + (1 - α) • n) (hyf : yf = ((1 + ν) / (γ * (1 - α) + α + ν)) • a) :
    m = ((ν + α + γ * (1 - α)) / (1 - α)) • y - ((ν + 1) / (1 - α)) • a ∧
      m = ((ν + α + γ * (1 - α)) / (1 - α)) • (y - yf) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn : n = (1 - α)⁻¹ • (y - a) := by
    rw [hy]
    match_scalars
    · field_simp
    · ring
  have e1 : m = ((ν + α + γ * (1 - α)) / (1 - α)) • y - ((ν + 1) / (1 - α)) • a := by
    rw [h23, hn]
    match_scalars <;> field_simp <;> ring
  refine ⟨e1, ?_⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = γ * (1 - α) + α + ν := ⟨_, rfl⟩
  rw [← hDdef] at hyf hD
  rw [e1, hyf, show ν + α + γ * (1 - α) = D by rw [hDdef]; ring]
  match_scalars
  · rfl
  · field_simp
    ring

/-- **(19.25)** (Miao, p. 626): the slope of the Phillips curve,
`κ = ((1 − βθ)(1 − θ)/(θ(1 + b)))·((ν + α + γ(1 − α))/(1 − α))`, `b = εα/(1 − α)`. -/
noncomputable def nk_kappa (β θ γ ν α ε : ℝ) : ℝ :=
  (1 - β * θ) * (1 - θ) / (θ * (1 + nk_b ε α)) * ((ν + α + γ * (1 - α)) / (1 - α))

/-- **(19.25)** (Miao, p. 626), the second printed form:
`κ = (1 − βθ)(1 − θ)(ν + α + γ(1 − α))/(θ(1 − α + εα))` for `α < 1`, `ε ≥ 0`. -/
theorem eq_19_25 {β θ γ ν α ε : ℝ} (hα : α < 1) (hε : 0 ≤ ε) (hα0 : 0 ≤ α) :
    nk_kappa β θ γ ν α ε =
      (1 - β * θ) * (1 - θ) * (ν + α + γ * (1 - α)) / (θ * (1 - α + ε * α)) := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have h2 : 0 < 1 - α + ε * α := by nlinarith
  have h3 : (1 : ℝ) + nk_b ε α = (1 - α + ε * α) / (1 - α) := by
    rw [nk_b]
    field_simp
  rw [nk_kappa, h3]
  by_cases hθ : θ = 0
  · simp [hθ]
  · field_simp

/-- Miao, p. 626: `κ > 0` for `0 < θ < 1`, `0 < β < 1` (`βθ < 1`), `0 ≤ α < 1`, `ε ≥ 0` and
`ν, γ ≥ 0` with `ν + α + γ(1 − α) > 0` (e.g. `ν, γ > 0`). -/
theorem nk_kappa_pos {β θ γ ν α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 ≤ ε) (hD : 0 < ν + α + γ * (1 - α)) :
    0 < nk_kappa β θ γ ν α ε := by
  rw [eq_19_25 hα1 hε hα0]
  have h2 : 0 < 1 - α + ε * α := by nlinarith
  have : 0 < 1 - β * θ := by linarith
  have : 0 < 1 - θ := by linarith
  positivity

/-- **(19.24)** (Miao, p. 626), the New Keynesian Phillips curve `π_t = βE_tπ_{t+1} + κx_t`,
`x_t = Ŷ_t − Ŷ^f_t`, from `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t`
(`nk_pc_mc`) and `MĈ_t = ((ν + α + γ(1 − α))/(1 − α))x_t` (`nk_mc_gap`). -/
theorem eq_19_24 (E : CondExpSystem ℝ V) {β θ γ ν α ε : ℝ} {pi m x : ℕ → V} (t : ℕ)
    (hpc : pi t = β • E.E t (pi (t + 1)) +
      ((1 - β * θ) * (1 - θ) / (θ * (1 + nk_b ε α))) • m t)
    (hm : m t = ((ν + α + γ * (1 - α)) / (1 - α)) • x t) :
    pi t = β • E.E t (pi (t + 1)) + nk_kappa β θ γ ν α ε • x t := by
  rw [hpc, hm, smul_smul, nk_kappa]

/-- **(19.27)** (Miao, p. 627): the natural rate `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` (in
log-linear form, `𝟙` the constant random variable) gives
`Ŷ^f_t = E_tŶ^f_{t+1} − γ⁻¹(r^n_t + ln β)` (`γ ≠ 0`). -/
theorem eq_19_27 (E : CondExpSystem ℝ V) {β γ : ℝ} (hγ : γ ≠ 0) {one : V} {yf rn : ℕ → V}
    (t : ℕ) (h : rn t = (-Real.log β) • one + γ • (E.E t (yf (t + 1)) - yf t)) :
    yf t = E.E t (yf (t + 1)) - γ⁻¹ • (rn t + Real.log β • one) := by
  rw [h]
  match_scalars <;> field_simp <;> ring

/-- **(19.28)** (Miao, p. 627), the intertemporal IS curve: from (19.26)
`Ŷ_t = E_tŶ_{t+1} − γ⁻¹(i_t + ln β − E_tπ_{t+1})` and (19.27), the output gap
`x_t = Ŷ_t − Ŷ^f_t` satisfies `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1} − r^n_t)`. -/
theorem eq_19_28 (E : CondExpSystem ℝ V) {β γ : ℝ} {one : V} {y yf i pi rn : ℕ → V} (t : ℕ)
    (h26 : y t = E.E t (y (t + 1)) - γ⁻¹ • (i t + Real.log β • one - E.E t (pi (t + 1))))
    (h27 : yf t = E.E t (yf (t + 1)) - γ⁻¹ • (rn t + Real.log β • one)) :
    y t - yf t = E.E t (y (t + 1) - yf (t + 1)) - γ⁻¹ • (i t - E.E t (pi (t + 1)) - rn t) := by
  rw [h26, h27, map_sub]
  module

end Miao.NewKeynesian
