/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.CRSIndustry

/-!
# A constant-returns-to-scale industry: the dynamic program

SLP Exercise 6.9a, p. 160. The book asks for the unique bounded continuous solution on `ℝ₊`.
**Correction**: on `ℝ₊` every solution is unbounded, since choosing `y = 0` gives
`v(x) ≥ S(xφ(0)) + θ(1 − δ)x + βv(0)` (`crs_unbounded`). On a compact state space `[0, K]` with
`Γ(x) = [0, min{αx, K}]` (`crsΓ`) the problem is well posed:

* `crs_assumption43`, `crs_assumption44`: Assumptions 4.3–4.4 (`F` is continuous on the graph,
  including at `(0, 0)` where `|xφ(y/x)| ≤ φ(0)x`).
* `crsValue_of_fixed`: the bounded continuous fixed point, lifted to `ℝ`, is a concave solution
  (`F` is concave on the graph because the perspective `xφ(y/x)` is), so `CRSValue` applies.
* **Exercise 6.9a** (`ex_6_9a`): there is a unique bounded continuous solution; it is strictly
  increasing and strictly concave; the maximizer is unique and the policy is continuous.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {S φ S' φ' : ℝ → ℝ} {α θ δ β K : ℝ}

/-- **On `ℝ₊` the value function is unbounded.** -/
theorem crs_unbounded (h : CRSHyp S φ S' φ' α θ δ β) {V : ℝ → ℝ} {MS : ℝ}
    (hS : ∀ q, 0 ≤ q → MS ≤ S q)
    (hV : ∀ x, 0 ≤ x → crsF S φ θ δ x 0 + β * V 0 ≤ V x) : ¬ BddAbove (V '' Ici 0) := by
  rintro ⟨B, hB⟩
  have hc : 0 < θ * (1 - δ) := mul_pos h.θ_pos (by linarith [h.δ_lt])
  set x := (|B| + |MS| + |β * V 0| + 1) / (θ * (1 - δ))
  have hx : 0 ≤ x := by positivity
  have h1 := hV x hx
  have h2 := hB ⟨x, hx, rfl⟩
  have h3 := hS (crsQ φ x 0) (h.crsQ_nonneg hx le_rfl (by nlinarith [h.α_pos]))
  have hxe : θ * (1 - δ) * x = |B| + |MS| + |β * V 0| + 1 := by
    simp only [x]; rw [mul_div_cancel₀ _ hc.ne']
  simp only [crsF] at h1
  nlinarith [le_abs_self B, neg_abs_le MS, neg_abs_le (β * V 0)]

/-- `Γ(x) = [0, min{αx, K}]` on `[0, K]`. -/
def crsΓ (α K : ℝ) : Icc (0 : ℝ) K → Set (Icc (0 : ℝ) K) :=
  intervalΓ K (fun _ => 0) (fun x => min (α * x) K)

/-- `F` on `[0, K]²`. -/
noncomputable def crsFs (S φ : ℝ → ℝ) (θ δ K : ℝ) (p : Icc (0 : ℝ) K × Icc (0 : ℝ) K) : ℝ :=
  crsF S φ θ δ p.1.1 p.2.1

theorem crs_assumption43 (h : CRSHyp S φ S' φ' α θ δ β) (hK : 0 < K) :
    Assumption43 (crsΓ α K) :=
  intervalΓ_assumption43 continuousOn_const
    ((continuous_const.mul continuous_id).min continuous_const).continuousOn
    (fun _ _ => le_rfl) (fun _ hx => le_min (mul_nonneg h.α_pos.le hx.1) hK.le)
    (fun _ _ => min_le_right _ _)

/-- The cone `{(x, y) : 0 ≤ y ≤ αx}`. -/
def crsCone (α : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ α * p.1}

theorem ratio_mem_cone (h : CRSHyp S φ S' φ' α θ δ β) {p : ℝ × ℝ} (hp : p ∈ crsCone α) :
    p.2 / p.1 ∈ Icc 0 α := by
  rcases eq_or_lt_of_le hp.1 with h0 | hpos
  · rw [← h0, div_zero]; exact ⟨le_rfl, h.α_pos.le⟩
  · exact CRSHyp.ratio_mem hpos hp.2.1 hp.2.2

/-- Output is continuous on the cone, including at the vertex, where `|xφ(y/x)| ≤ φ(0)x`. -/
theorem continuousOn_crsQ (h : CRSHyp S φ S' φ' α θ δ β) (hφc : ContinuousOn φ (Icc 0 α)) :
    ContinuousOn (fun p : ℝ × ℝ => crsQ φ p.1 p.2) (crsCone α) := by
  intro p hp
  rcases eq_or_lt_of_le hp.1 with h0 | hpos
  · -- at the vertex
    have hp2 : p.2 = 0 := le_antisymm (by have := hp.2.2; rw [← h0, mul_zero] at this; exact this)
      hp.2.1
    have hval : crsQ φ p.1 p.2 = 0 := by simp [crsQ, ← h0]
    rw [ContinuousWithinAt, hval]
    have hlim : Tendsto (fun q : ℝ × ℝ => φ 0 * q.1) (𝓝[crsCone α] p) (𝓝 0) := by
      have hc : Tendsto (fun q : ℝ × ℝ => φ 0 * q.1) (𝓝 p) (𝓝 (φ 0 * p.1)) :=
        Continuous.tendsto (f := fun q : ℝ × ℝ => φ 0 * q.1) (by fun_prop) p
      rw [← h0, mul_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      rcases eq_or_lt_of_le hq.1 with hq0 | hqp
      · simp [crsQ, ← hq0]
      · exact h.crsQ_nonneg hq.1 hq.2.1 hq.2.2)]
    simp only [crsQ]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (h.φ_le (ratio_mem_cone h hq)) hq.1
  · -- away from the vertex
    have hr : ContinuousWithinAt (fun q : ℝ × ℝ => q.2 / q.1) (crsCone α) p :=
      (continuous_snd.continuousAt.div continuous_fst.continuousAt hpos.ne').continuousWithinAt
    have hφ' : ContinuousWithinAt (fun q : ℝ × ℝ => φ (q.2 / q.1)) (crsCone α) p :=
      ContinuousWithinAt.comp (g := φ) (f := fun q : ℝ × ℝ => q.2 / q.1)
        (hφc _ (ratio_mem_cone h hp)) hr fun q hq => ratio_mem_cone h hq
    exact continuous_fst.continuousWithinAt.mul hφ'

/-- `F` is continuous on the cone. -/
theorem continuousOn_crsF (h : CRSHyp S φ S' φ' α θ δ β) (hφc : ContinuousOn φ (Icc 0 α)) :
    ContinuousOn (fun p : ℝ × ℝ => crsF S φ θ δ p.1 p.2) (crsCone α) := by
  have hS : ContinuousOn S (Ici 0) := fun q hq =>
    (h.S_deriv q hq).continuousAt.continuousWithinAt
  have hSq := hS.comp (continuousOn_crsQ h hφc) fun p hp => mem_Ici.2
    (h.crsQ_nonneg hp.1 hp.2.1 hp.2.2)
  exact hSq.sub (continuous_const.mul (continuous_snd.sub
    (continuous_const.mul continuous_fst))).continuousOn

theorem graph_mem_cone {p : Icc (0 : ℝ) K × Icc (0 : ℝ) K}
    (hp : p.2 ∈ crsΓ α K p.1) : (p.1.1, p.2.1) ∈ crsCone α :=
  ⟨p.1.2.1, p.2.2.1, hp.2.trans (min_le_left _ _)⟩

/-- **Assumption 4.4.** -/
theorem crs_assumption44 (h : CRSHyp S φ S' φ' α θ δ β) (hφc : ContinuousOn φ (Icc 0 α)) :
    Assumption44 (crsΓ α K) (crsFs S φ θ δ K) β := by
  have hcont : ContinuousOn (crsFs S φ θ δ K) {p | p.2 ∈ crsΓ α K p.1} :=
    (continuousOn_crsF h hφc).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousOn fun p hp => graph_mem_cone hp
  -- `S` is bounded on the compact range of outputs
  have hS : ContinuousOn S (Icc 0 (K * φ 0)) := fun q hq =>
    (h.S_deriv q hq.1).continuousAt.continuousWithinAt
  obtain ⟨MS, hMS⟩ := isCompact_Icc.exists_bound_of_continuousOn hS
  refine ⟨hcont, ⟨MS + θ * (|K| + |K|), fun p hp => ?_⟩, h.β_pos, h.β_lt⟩
  have hc := graph_mem_cone hp
  have hq0 := h.crsQ_nonneg hc.1 hc.2.1 hc.2.2
  have hqK : crsQ φ p.1.1 p.2.1 ≤ K * φ 0 := by
    simp only [crsQ]
    exact mul_le_mul p.1.2.2 (h.φ_le (ratio_mem_cone h hc)) (h.φ_nonneg (ratio_mem_cone h hc))
      (le_trans p.1.2.1 p.1.2.2)
  have h1 := hMS _ ⟨hq0, hqK⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : |θ * (p.2.1 - (1 - δ) * p.1.1)| ≤ θ * (|K| + |K|) := by
    rw [abs_mul, abs_of_pos h.θ_pos]
    refine mul_le_mul_of_nonneg_left ?_ h.θ_pos.le
    have hx1 := p.1.2.1
    have hx2 := p.1.2.2
    have hy1 := p.2.2.1
    have hy2 := p.2.2.2
    have hK := le_abs_self K
    have h1δ : 0 ≤ (1 - δ) * p.1.1 := mul_nonneg (by linarith [h.δ_lt]) hx1
    have h2δ : (1 - δ) * p.1.1 ≤ p.1.1 := by nlinarith [h.δ_pos]
    rw [abs_le]
    constructor <;> linarith
  simp only [crsFs, crsF]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

theorem mem_crsΓ {x y : Icc (0 : ℝ) K} : y ∈ crsΓ α K x ↔ y.1 ≤ min (α * x.1) K :=
  ⟨fun h => h.2, fun h => ⟨y.2.1, h⟩⟩

/-- The bounded continuous fixed point, lifted to `ℝ`, is a concave solution. -/
theorem crsValue_of_fixed [Nonempty (Icc (0 : ℝ) K)] (h : CRSHyp S φ S' φ' α θ δ β) (hK : 0 < K)
    (hφc : ContinuousOn φ (Icc 0 α)) {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman (crs_assumption43 h hK) (crs_assumption44 (K := K) h hφc) v = v) :
    CRSValue S φ S' φ' α θ δ β K (liftR K v) := by
  have h43 := crs_assumption43 h hK
  have h44 := crs_assumption44 (K := K) h hφc
  -- `F` is concave on the graph, and the graph is convex
  have hF : ∀ x y x' y' : Icc (0 : ℝ) K, y ∈ crsΓ α K x → y' ∈ crsΓ α K x' →
      ∀ (θ' : ℝ) (h0 : 0 ≤ θ') (h1 : θ' ≤ 1),
        θ' * crsFs S φ θ δ K (x, y) + (1 - θ') * crsFs S φ θ δ K (x', y') ≤
          crsFs S φ θ δ K (cmb (convex_Icc 0 K) h0 h1 x x', cmb (convex_Icc 0 K) h0 h1 y y') :=
    fun x y x' y' hy hy' θ' h0 h1 => by
      have hc := graph_mem_cone (p := (x, y)) hy
      have hc' := graph_mem_cone (p := (x', y')) hy'
      have hq := h.crsQ_concave hc.1 hc'.1 hc.2.1 hc.2.2 hc'.2.1 hc'.2.2 h0
        (show (0 : ℝ) ≤ 1 - θ' by linarith) (by ring)
      have hq0 := h.crsQ_nonneg hc.1 hc.2.1 hc.2.2
      have hq0' := h.crsQ_nonneg hc'.1 hc'.2.1 hc'.2.2
      have hmix : 0 ≤ θ' * crsQ φ x.1 y.1 + (1 - θ') * crsQ φ x'.1 y'.1 :=
        add_nonneg (mul_nonneg h0 hq0) (mul_nonneg (by linarith) hq0')
      have hS1 := h.S_conc.concaveOn.2 (mem_Ici.2 hq0) (mem_Ici.2 hq0') h0
        (show (0 : ℝ) ≤ 1 - θ' by linarith) (by ring)
      have hS2 := h.S_mono.monotoneOn (mem_Ici.2 hmix) (mem_Ici.2 (hmix.trans hq)) hq
      simp only [smul_eq_mul] at hS1
      simp only [crsFs, crsF, cmb, smul_eq_mul]
      nlinarith
  have h48 : Assumption48 (convex_Icc 0 K) (crsΓ α K) :=
    fun x y x' y' hy hy' θ' h0 h1 => by
      rw [mem_crsΓ] at hy hy' ⊢
      simp only [cmb, smul_eq_mul]
      refine le_min ?_ ?_
      · have := mul_le_mul_of_nonneg_left (hy.trans (min_le_left _ _)) h0
        have := mul_le_mul_of_nonneg_left (hy'.trans (min_le_left _ _)) (by linarith : 0 ≤ 1 - θ')
        nlinarith
      · have := mul_le_mul_of_nonneg_left (hy.trans (min_le_right _ _)) h0
        have := mul_le_mul_of_nonneg_left (hy'.trans (min_le_right _ _)) (by linarith : 0 ≤ 1 - θ')
        nlinarith
  have hvc := fixed_concave_of_concaveF h43 h44 hF h48 hv
  refine ⟨h, hK, fun x hx y hy => ?_, fun x hx => ?_, concaveOn_liftR_of_concave hvc⟩
  · obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 v ⟨x, hx⟩
    rw [hv] at hmax
    have hyK : y ∈ Icc (0 : ℝ) K := ⟨hy.1, hy.2.trans (min_le_right _ _)⟩
    have := hmax ⟨y, hyK⟩ (mem_crsΓ.2 hy.2)
    rw [liftR_of_mem v hx, liftR_of_mem v hyK]
    exact this
  · obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax h43 h44 v ⟨x, hx⟩
    rw [hv] at hval
    refine ⟨y.1, ⟨y.2.1, mem_crsΓ.1 hy⟩, ?_⟩
    rw [liftR_of_mem v hx, liftR_of_mem v y.2, hval]
    rfl

/-- Maximizers are characterized by `F(x, y) + βv(y) = v(x)`. -/
theorem crs_mem_argmax_iff (h : CRSHyp S φ S' φ' α θ δ β) (hK : 0 < K)
    (hφc : ContinuousOn φ (Icc 0 α)) {v : Icc (0 : ℝ) K →ᵇ ℝ}
    (hv : bellman (crs_assumption43 h hK) (crs_assumption44 (K := K) h hφc) v = v)
    (x y : Icc (0 : ℝ) K) : y ∈ argmax (obj (crsFs S φ θ δ K) β v) (crsΓ α K) x ↔
      y.1 ≤ min (α * x.1) K ∧
        crsF S φ θ δ x.1 y.1 + β * liftR K v y.1 = liftR K v x.1 := by
  rw [liftR_of_mem v y.2, liftR_of_mem v x.2]
  have e := bellman_apply (crs_assumption43 h hK) (crs_assumption44 (K := K) h hφc) v x
  rw [hv] at e
  simp only [argmax, mem_ofPred_eq, Subtype.coe_eta, obj, crsFs, ← e, mem_crsΓ]

/-- **Exercise 6.9a.** On `[0, K]` there is a unique bounded continuous solution `v`; it is
strictly increasing and strictly concave; the maximizer is unique and the policy continuous. -/
theorem ex_6_9a [Nonempty (Icc (0 : ℝ) K)] (h : CRSHyp S φ S' φ' α θ δ β) (hK : 0 < K)
    (hφc : ContinuousOn φ (Icc 0 α)) :
    ∃ v : Icc (0 : ℝ) K →ᵇ ℝ,
      bellman (crs_assumption43 h hK) (crs_assumption44 (K := K) h hφc) v = v ∧
      (∀ w, bellman (crs_assumption43 h hK) (crs_assumption44 (K := K) h hφc) w = w → w = v) ∧
      StrictMonoOn (liftR K v) (Icc 0 K) ∧ StrictConcaveOn ℝ (Icc 0 K) (liftR K v) ∧
      UniqueArgmax (crsΓ α K) (obj (crsFs S φ θ δ K) β v) ∧
      Continuous (argmaxFn (crsΓ α K) (obj (crsFs S φ θ δ K) β v)) := by
  have h43 := crs_assumption43 h hK
  have h44 := crs_assumption44 (K := K) h hφc
  obtain ⟨v, hv, huniq, -, -⟩ := theorem_4_6 h43 h44
  have hV := crsValue_of_fixed h hK hφc hv
  have hUA : UniqueArgmax (crsΓ α K) (obj (crsFs S φ θ δ K) β v) :=
    ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc, continuousOn_obj h44 v.continuous,
      fun x y₁ hy₁ y₂ hy₂ => by
        obtain ⟨h1, e1⟩ := (crs_mem_argmax_iff h hK hφc hv x y₁).1 hy₁
        obtain ⟨h2, e2⟩ := (crs_mem_argmax_iff h hK hφc hv x y₂).1 hy₂
        exact Subtype.ext (hV.argmax_unique x.2 ⟨y₁.2.1, h1⟩ ⟨y₂.2.1, h2⟩ e1 e2)⟩
  exact ⟨v, hv, huniq, hV.strictMonoOn, hV.strictConcaveOn, hUA, hUA.continuous_argmaxFn⟩

/-! ### No stationary point: a counterexample to Exercise 6.9c -/

/-- `φ(u) = √(2 − u)` on `[0, 2]`. -/
noncomputable def sqrtPhi (u : ℝ) : ℝ := Real.sqrt (2 - u)

/-- `φ'(u) = −1/(2√(2 − u))`. -/
noncomputable def sqrtPhi' (u : ℝ) : ℝ := -1 / (2 * Real.sqrt (2 - u))

/-- `S(q) = 1 − e^{−q}`. -/
noncomputable def expS (q : ℝ) : ℝ := 1 - Real.exp (-q)

/-- `S'(q) = e^{−q}`. -/
noncomputable def expS' (q : ℝ) : ℝ := Real.exp (-q)

theorem sqrtPhi_hyp {θ δ : ℝ} (hθ : 0 < θ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    CRSHyp expS sqrtPhi expS' sqrtPhi' 2 θ δ (1 / 4) where
  α_gt := by norm_num
  θ_pos := hθ
  δ_pos := hδ0
  δ_lt := hδ1
  β_pos := by norm_num
  β_lt := by norm_num
  φ_anti u hu v hv huv := Real.sqrt_lt_sqrt (by linarith [hv.2]) (by linarith)
  φ_conc := by
    refine ⟨convex_Icc 0 2, fun u hu v hv huv a b ha hb hab => ?_⟩
    have := Real.strictConcaveOn_sqrt.2 (mem_Ici.2 (by linarith [hu.2] : (0 : ℝ) ≤ 2 - u))
      (mem_Ici.2 (by linarith [hv.2] : (0 : ℝ) ≤ 2 - v)) (fun he => huv (by linarith)) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    simp only [sqrtPhi]
    rw [show 2 - (a * u + b * v) = a * (2 - u) + b * (2 - v) by
      linear_combination (-2 : ℝ) * hab]
    exact this
  φ_zero := Real.sqrt_pos.2 (by norm_num)
  φ_α := by simp [sqrtPhi]
  φ_deriv u hu := by
    have h1 : HasDerivAt (fun u : ℝ => 2 - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 2
    have := h1.sqrt (by linarith [hu.2] : (2 : ℝ) - u ≠ 0)
    have e : sqrtPhi = fun y => Real.sqrt (2 - y) := rfl
    rw [e]
    simpa [sqrtPhi'] using this
  φ'_lim := by
    have h1 : Tendsto (fun u : ℝ => 2 - u) (𝓝[<] 2) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (Continuous.tendsto (f := fun u : ℝ => 2 - u) (by fun_prop) 2).mono_left
          (nhdsWithin_le_nhds (s := Iio (2 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [mem_Ioi]; linarith [mem_Iio.1 hu]
    have h2 : Tendsto (fun t : ℝ => 2 * Real.sqrt t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (Continuous.tendsto (f := fun t : ℝ => 2 * Real.sqrt t)
          (continuous_const.mul Real.continuous_sqrt) 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mem_Ioi.2 (mul_pos two_pos (Real.sqrt_pos.2 ht))
    have h3 := tendsto_neg_atTop_atBot.comp (tendsto_inv_nhdsGT_zero.comp (h2.comp h1))
    refine h3.congr fun u => ?_
    simp [sqrtPhi', div_eq_mul_inv]
  S_mono q _ q' _ hqq' := by
    simp only [expS]; linarith [Real.exp_lt_exp.2 (neg_lt_neg hqq')]
  S_conc := by
    refine ⟨convex_Ici 0, fun q _ q' _ hne a b ha hb hab => ?_⟩
    have := strictConvexOn_exp.2 (mem_univ (-q)) (mem_univ (-q')) (fun he => hne (by linarith))
      ha hb hab
    simp only [smul_eq_mul] at this ⊢
    simp only [expS]
    rw [show -(a * q + b * q') = a * -q + b * -q' by ring]
    nlinarith
  S_deriv q _ := by
    have := ((hasDerivAt_neg q).exp).const_sub 1
    have e : expS = fun x => 1 - Real.exp (-x) := rfl
    rw [e]
    convert this using 1
    simp [expS']

theorem continuousOn_sqrtPhi : ContinuousOn sqrtPhi (Icc 0 2) :=
  (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn

/-- **Exercise 6.9c is false as stated.** With `φ(u) = √(2 − u)`, `S(q) = 1 − e^{−q}`, `α = 2` and
`β = 1/4`, all the hypotheses hold, but `βφ(1) + (1 − β)φ'(1) = 1/4 − 3/8 < 0`, so the value
function has **no** positive stationary point on any `[0, K]`. -/
theorem ex_6_9c_counterexample [Nonempty (Icc (0 : ℝ) K)] {θ δ : ℝ} (hθ : 0 < θ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hK : 0 < K) :
    ∃ v : Icc (0 : ℝ) K →ᵇ ℝ,
      bellman (crs_assumption43 (sqrtPhi_hyp hθ hδ0 hδ1) hK)
        (crs_assumption44 (K := K) (sqrtPhi_hyp hθ hδ0 hδ1) continuousOn_sqrtPhi) v = v ∧
      ∀ x ∈ Ioo 0 K,
        crsF expS sqrtPhi θ δ x x + 1 / 4 * liftR K v x ≠ liftR K v x := by
  have H := sqrtPhi_hyp hθ hδ0 hδ1
  obtain ⟨v, hv, -⟩ := ex_6_9a H hK continuousOn_sqrtPhi
  refine ⟨v, hv, fun x hx => (crsValue_of_fixed H hK continuousOn_sqrtPhi hv).no_stationary
    ?_ hx⟩
  have h1 : sqrtPhi 1 = 1 := by norm_num [sqrtPhi]
  have h2 : sqrtPhi' 1 = -1 / 2 := by norm_num [sqrtPhi']
  rw [h1, h2]; norm_num

end StokeyLucasPrescott.DeterministicDynamics
