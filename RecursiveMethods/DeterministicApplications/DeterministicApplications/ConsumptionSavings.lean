/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.EulerEquations
import DeterministicApplications.Assumption42

/-!
# A consumption–savings problem: the optimal plan

SLP §5.17, pp. 126–128. Preferences `Σ βᵗU(c_t)`, income `I > 0` each period, wealth `x_t ≥ 0`
(no borrowing), interest factor `R` with `0 < R < 1/β`:
`c_t + x_{t+1}/R = I + x_t`, so `Γ(x) = [0, (I + x)R]` and `F(x, y) = U(I + x − y/R)`.

`U` is continuous, strictly increasing and strictly concave on `ℝ₊`, with a continuous derivative
`U'` on `(0, ∞)` (the book asks for `C¹` on `ℝ₊`; nothing here uses a derivative at `0`), and
`U'(c) → 0` as `c → ∞`. That last condition is not in the book, which needs some such condition:
see `ConsumptionSavingsCounterexample` for a counterexample.

Rather than building `v` interval by interval as the book does, we write down every optimal plan
at once. For a multiplier `μ > 0`, let `cI(p) = max{I, (U')⁻¹(p)}` (`cI`) and consume
`c_t = cI(μ/(Rβ)ᵗ)`. Consumption falls (`Rβ < 1`) until it reaches `I`, after which wealth is
zero. The wealth that this plan exhausts is `Ξ(μ) = Σ_t R⁻ᵗ(c_t − I)` (`wealth`, a finite sum),
and the plan's wealth path is `x_t = Ξ(μ/(Rβ)ᵗ)` (`planμ`). `Ξ` is continuous and decreasing,
from `+∞` down to `Ξ(U'(I)) = 0`, so every `x₀ ≥ 0` is `Ξ(μ)` for some `μ ∈ (0, U'(I)]`
(`exists_wealth_eq`).

The plan is optimal, and uniquely so, by a summation-by-parts argument (`abel_bound`). With
`p_t = βᵗU'(c_t)` we have `Rp_{t+1} ≤ p_t`, with equality unless `x_{t+1} = 0`. This bounds
`Σ p_t(c'_t − c_t)` for any feasible `c'` by `p₀(x'₀ − x₀)`, and concavity of `U` does the rest
(`value_bound`). This gives at once:

* optimality and uniqueness (`plan_total`, `total_lt`), and `v*(x₀) = V(μ)` (`vstar_eq`);
* the supergradient inequality `v*(z) ≤ v*(x₀) + U'(c₀)(z − x₀)` (`vstar_le_tangent`), which
  `ConsumptionSavingsPolicy` turns into differentiability and strict concavity of `v`.

**Exercise 5.17a** (`ex_5_17a`): `v*` is real-valued and satisfies (FE), and an optimal plan
satisfies `v*(x_t) = U(I + x_t − x_{t+1}/R) + βv*(x_{t+1})`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

/-- The hypotheses of §5.17. -/
structure CSHyp (U U' : ℝ → ℝ) (β R I : ℝ) : Prop where
  hβ0 : 0 < β
  hβ1 : β < 1
  hR : 0 < R
  hRβ : R * β < 1
  hI : 0 < I
  hUc : ContinuousOn U (Ici 0)
  hUd : ∀ c, 0 < c → HasDerivAt U (U' c) c
  hU'c : ContinuousOn U' (Ioi 0)
  hUm : StrictMonoOn U (Ici 0)
  hUcc : StrictConcaveOn ℝ (Ici 0) U
  hlim : Tendsto U' atTop (𝓝 0)

variable {U U' : ℝ → ℝ} {β R I : ℝ}

theorem CSHyp.rho_pos (h : CSHyp U U' β R I) : 0 < R * β := mul_pos h.hR h.hβ0

/-- `U` lies below its tangent lines. -/
theorem CSHyp.super_le (h : CSHyp U U' β R I) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c') :
    U c' ≤ U c + U' c * (c' - c) := by
  have := concave_le_fderiv h.hUcc.concaveOn (mem_Ici.2 hc.le) (mem_Ici.2 hc')
    (h.hUd c hc).hasFDerivAt
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
  linarith

/-- `U` lies strictly below its tangent lines away from the point of tangency. -/
theorem CSHyp.super_lt (h : CSHyp U U' β R I) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c')
    (hne : c' ≠ c) : U c' < U c + U' c * (c' - c) := by
  have hm := h.super_le hc (c' := (c + c') / 2) (by positivity)
  have hs := h.hUcc.2 (mem_Ici.2 hc.le) (mem_Ici.2 hc') (Ne.symm hne)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hs
  have e : (1 / 2 : ℝ) * c + 1 / 2 * c' = (c + c') / 2 := by ring
  rw [e] at hs
  linarith

theorem CSHyp.U'_pos (h : CSHyp U U' β R I) {c : ℝ} (hc : 0 < c) : 0 < U' c := by
  have h1 := h.super_lt hc (c' := c + 1) (by linarith) (by linarith)
  have h2 := h.hUm (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c + 1))
    (by linarith : c < c + 1)
  nlinarith

theorem CSHyp.U'_lt (h : CSHyp U U' β R I) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    U' b < U' a := by
  have h1 := h.super_lt ha (c' := b) (by linarith) hab.ne'
  have h2 := h.super_lt (ha.trans hab) (c' := a) ha.le hab.ne
  nlinarith

theorem CSHyp.U'_le (h : CSHyp U U' β R I) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    U' b ≤ U' a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact (h.U'_lt ha hlt).le

/-! ### Consumption at a given marginal utility -/

/-- `cI(p)`: the least `c ≥ I` with `U'(c) ≤ p`, i.e. `max{I, (U')⁻¹(p)}`. -/
noncomputable def cI (U' : ℝ → ℝ) (I p : ℝ) : ℝ := sInf {c | I ≤ c ∧ U' c ≤ p}

theorem CSHyp.cI_nonempty (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) :
    {c | I ≤ c ∧ U' c ≤ p}.Nonempty := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.hlim.eventually (gt_mem_nhds hp))
  exact ⟨max N I, le_max_right _ _, (hN _ (le_max_left _ _)).le⟩

theorem CSHyp.cI_mem (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) :
    I ≤ cI U' I p ∧ U' (cI U' I p) ≤ p := by
  have hcl : IsClosed {c | I ≤ c ∧ U' c ≤ p} :=
    (h.hU'c.mono fun c (hc : c ∈ Ici I) => lt_of_lt_of_le h.hI hc).preimage_isClosed_of_isClosed
      isClosed_Ici isClosed_Iic
  exact hcl.csInf_mem (h.cI_nonempty hp) ⟨I, fun _ hc => hc.1⟩

theorem cI_le {p c : ℝ} (hc : I ≤ c) (hpc : U' c ≤ p) : cI U' I p ≤ c :=
  csInf_le ⟨I, fun _ hc => hc.1⟩ ⟨hc, hpc⟩

theorem CSHyp.cI_pos (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) : 0 < cI U' I p :=
  h.hI.trans_le (h.cI_mem hp).1

theorem CSHyp.cI_of_le (h : CSHyp U U' β R I) {p : ℝ} (hp : U' I ≤ p) : cI U' I p = I :=
  le_antisymm (cI_le le_rfl hp) (h.cI_mem ((h.U'_pos h.hI).trans_le hp)).1

/-- Above `I`, `cI` inverts `U'`. -/
theorem CSHyp.cI_eq (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) (hgt : I < cI U' I p) :
    U' (cI U' I p) = p := by
  set c := cI U' I p
  refine le_antisymm (h.cI_mem hp).2 (not_lt.1 fun hlt => ?_)
  have hcont : ContinuousAt U' c := h.hU'c.continuousAt (Ioi_mem_nhds (h.hI.trans hgt))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hlt))
  set d := max (c - ε / 2) ((I + c) / 2)
  have hd1 : d < c := max_lt (by linarith) (by linarith)
  have hd2 : I ≤ d := le_max_of_le_right (by linarith)
  have hd3 : dist d c < ε := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor
    · linarith
    · linarith [le_max_left (c - ε / 2) ((I + c) / 2)]
  exact absurd (cI_le hd2 (hball hd3).le) (not_le.2 hd1)

theorem CSHyp.cI_U' (h : CSHyp U U' β R I) {c : ℝ} (hc : I ≤ c) : cI U' I (U' c) = c := by
  have hp := h.U'_pos (h.hI.trans_le hc)
  refine le_antisymm (cI_le hc le_rfl) (not_lt.1 fun hlt => ?_)
  exact absurd (h.cI_mem hp).2 (not_le.2 (h.U'_lt (h.cI_pos hp) hlt))

theorem CSHyp.cI_anti (h : CSHyp U U' β R I) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    cI U' I q ≤ cI U' I p :=
  cI_le (h.cI_mem hp).1 ((h.cI_mem hp).2.trans hpq)

theorem CSHyp.cI_gt (h : CSHyp U U' β R I) {p : ℝ} (hp : 0 < p) (hpI : p < U' I) :
    I < cI U' I p := by
  refine lt_of_le_of_ne (h.cI_mem hp).1 fun he => ?_
  have := (h.cI_mem hp).2
  rw [← he] at this
  linarith

theorem CSHyp.cI_strictAnti (h : CSHyp U U' β R I) {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hpI : p < U' I) : cI U' I q < cI U' I p := by
  have hgt := h.cI_gt hp hpI
  have hU := h.cI_eq hp hgt
  rcases eq_or_lt_of_le (h.cI_mem (hp.trans hpq)).1 with he | hlt
  · rw [← he]; exact hgt
  · have hUq := h.cI_eq (hp.trans hpq) hlt
    refine not_le.1 fun hle => ?_
    have := h.U'_le (h.hI.trans hgt) hle
    linarith

/-- `cI(p) ≥ c` once `p < U'(c)`. -/
theorem CSHyp.le_cI (h : CSHyp U U' β R I) {p c : ℝ} (hp : 0 < p)
    (hpc : p < U' c) : c ≤ cI U' I p := by
  refine not_lt.1 fun hlt => ?_
  have := h.U'_le (h.cI_pos hp) hlt.le
  linarith [(h.cI_mem hp).2]

theorem CSHyp.continuousAt_cI (h : CSHyp U U' β R I) {p₀ : ℝ} (hp₀ : 0 < p₀) :
    ContinuousAt (cI U' I) p₀ := by
  have hpos : ∀ᶠ p in 𝓝 p₀, 0 < p := lt_mem_nhds hp₀
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a I with haI | haI
    · filter_upwards [hpos] with p hp
      exact haI.trans_le (h.cI_mem hp).1
    · have hgt : I < cI U' I p₀ := lt_of_le_of_lt haI ha
      have hUa : p₀ < U' a := by
        have := h.U'_lt (h.hI.trans_le haI) ha
        rwa [h.cI_eq hp₀ hgt] at this
      filter_upwards [hpos, gt_mem_nhds hUa] with p hp hpa
      refine not_le.1 fun hle => ?_
      have := h.U'_le (h.cI_pos hp) hle
      linarith [(h.cI_mem hp).2]
  · set b' := (cI U' I p₀ + b) / 2
    have hb'1 : cI U' I p₀ < b' := by simp only [b']; linarith
    have hb'2 : b' < b := by simp only [b']; linarith
    have hUb : U' b' < p₀ := (h.U'_lt (h.cI_pos hp₀) hb'1).trans_le (h.cI_mem hp₀).2
    filter_upwards [lt_mem_nhds hUb] with p hp
    exact (cI_le ((h.cI_mem hp₀).1.trans hb'1.le) hp.le).trans_lt hb'2

/-! ### The wealth a multiplier exhausts -/

/-- `Ξ(μ) = Σ_t R⁻ᵗ(cI(μ/(Rβ)ᵗ) − I)`. -/
noncomputable def wealth (U' : ℝ → ℝ) (β R I μ : ℝ) : ℝ :=
  ∑' t : ℕ, (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I)

/-- From some date on, `μ/(Rβ)ᵗ ≥ U'(I)` (uniformly in `μ ≥ μ₁`). -/
theorem CSHyp.exists_K (h : CSHyp U U' β R I) {μ₁ : ℝ} (hμ₁ : 0 < μ₁) :
    ∃ K : ℕ, ∀ t, K ≤ t → ∀ μ, μ₁ ≤ μ → U' I ≤ μ / (R * β) ^ t := by
  have hU := h.U'_pos h.hI
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hμ₁ hU) h.hRβ
  refine ⟨K, fun t ht μ hμ => ?_⟩
  have hρt : (R * β) ^ t ≤ (R * β) ^ K := pow_le_pow_of_le_one h.rho_pos.le h.hRβ.le ht
  rw [le_div_iff₀ (pow_pos h.rho_pos t)]
  have := (lt_div_iff₀ hU).1 (hρt.trans_lt hK)
  linarith

theorem CSHyp.wealth_term_eq_zero (h : CSHyp U U' β R I) {μ : ℝ} {t : ℕ}
    (ht : U' I ≤ μ / (R * β) ^ t) : (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I) = 0 := by
  rw [h.cI_of_le ht, sub_self, mul_zero]

theorem CSHyp.wealth_eq_sum (h : CSHyp U U' β R I) {μ₁ : ℝ} (hμ₁ : 0 < μ₁) :
    ∃ K : ℕ, ∀ μ, μ₁ ≤ μ → wealth U' β R I μ =
      ∑ t ∈ Finset.range K, (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I) := by
  obtain ⟨K, hK⟩ := h.exists_K hμ₁
  exact ⟨K, fun μ hμ => tsum_eq_sum fun t ht =>
    h.wealth_term_eq_zero (hK t (by simpa using ht) μ hμ)⟩

theorem CSHyp.summable_wealth (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    Summable fun t : ℕ => (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I) := by
  obtain ⟨K, hK⟩ := h.exists_K hμ
  exact summable_of_ne_finset_zero (s := Finset.range K) fun t ht =>
    h.wealth_term_eq_zero (hK t (by simpa using ht) μ le_rfl)

theorem CSHyp.wealth_nonneg (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    0 ≤ wealth U' β R I μ :=
  tsum_nonneg fun t => mul_nonneg (inv_nonneg.2 (pow_pos h.hR t).le)
    (sub_nonneg.2 (h.cI_mem (div_pos hμ (pow_pos h.rho_pos t))).1)

/-- `Ξ(μ) = (cI(μ) − I) + R⁻¹Ξ(μ/(Rβ))`. -/
theorem CSHyp.wealth_shift (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    wealth U' β R I μ = (cI U' I μ - I) + R⁻¹ * wealth U' β R I (μ / (R * β)) := by
  rw [wealth, (h.summable_wealth hμ).tsum_eq_zero_add, wealth, ← tsum_mul_left]
  congr 1
  · simp
  · refine tsum_congr fun t => ?_
    rw [show μ / (R * β) ^ (t + 1) = μ / (R * β) / (R * β) ^ t by
      rw [pow_succ', div_mul_eq_div_div], pow_succ', mul_inv]
    ring

theorem CSHyp.wealth_of_ge (h : CSHyp U U' β R I) {μ : ℝ} (hμ : U' I ≤ μ) :
    wealth U' β R I μ = 0 := by
  refine (tsum_congr fun t => h.wealth_term_eq_zero ?_).trans tsum_zero
  exact hμ.trans (le_div_self ((h.U'_pos h.hI).le.trans hμ) (pow_pos h.rho_pos t)
    (pow_le_one₀ h.rho_pos.le h.hRβ.le))

theorem CSHyp.wealth_ge (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    cI U' I μ - I ≤ wealth U' β R I μ := by
  rw [h.wealth_shift hμ]
  exact le_add_of_nonneg_right
    (mul_nonneg (inv_nonneg.2 h.hR.le) (h.wealth_nonneg (div_pos hμ h.rho_pos)))

theorem CSHyp.wealth_anti (h : CSHyp U U' β R I) {μ μ' : ℝ} (hμ : 0 < μ) (hμμ' : μ ≤ μ') :
    wealth U' β R I μ' ≤ wealth U' β R I μ := by
  refine Summable.tsum_le_tsum (fun t => ?_) (h.summable_wealth (hμ.trans_le hμμ'))
    (h.summable_wealth hμ)
  have hρt := pow_pos h.rho_pos t
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (h.cI_anti (div_pos hμ hρt)
    (div_le_div_of_nonneg_right hμμ' hρt.le)) I) (inv_nonneg.2 (pow_pos h.hR t).le)

theorem CSHyp.wealth_strictAnti (h : CSHyp U U' β R I) {μ μ' : ℝ} (hμ : 0 < μ) (hμμ' : μ < μ')
    (hμI : μ < U' I) : wealth U' β R I μ' < wealth U' β R I μ := by
  rw [h.wealth_shift hμ, h.wealth_shift (hμ.trans hμμ')]
  have h1 := h.cI_strictAnti hμ hμμ' hμI
  have h2 := mul_le_mul_of_nonneg_left (h.wealth_anti (div_pos hμ h.rho_pos)
    (div_le_div_of_nonneg_right hμμ'.le h.rho_pos.le)) (inv_nonneg.2 h.hR.le)
  linarith

theorem CSHyp.wealth_pos (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (hμI : μ < U' I) :
    0 < wealth U' β R I μ := by
  rw [← h.wealth_of_ge (le_refl (U' I))]
  exact h.wealth_strictAnti hμ hμI hμI

/-- `Ξ(μ) > 0` only below `U'(I)`. -/
theorem CSHyp.lt_of_wealth_pos (h : CSHyp U U' β R I) {μ : ℝ} (hw : 0 < wealth U' β R I μ) :
    μ < U' I :=
  not_le.1 fun hle => by rw [h.wealth_of_ge hle] at hw; exact lt_irrefl _ hw

theorem CSHyp.continuousAt_wealth (h : CSHyp U U' β R I) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    ContinuousAt (wealth U' β R I) μ₀ := by
  obtain ⟨K, hK⟩ := h.wealth_eq_sum (half_pos hμ₀)
  have hev : (fun μ => ∑ t ∈ Finset.range K, (R ^ t)⁻¹ * (cI U' I (μ / (R * β) ^ t) - I))
      =ᶠ[𝓝 μ₀] wealth U' β R I := by
    filter_upwards [lt_mem_nhds (half_lt_self hμ₀)] with μ hμ
    exact (hK μ hμ.le).symm
  refine ContinuousAt.congr ?_ hev
  refine tendsto_finsetSum _ fun t _ => ?_
  have hc : ContinuousAt (fun μ => cI U' I (μ / (R * β) ^ t)) μ₀ :=
    (h.continuousAt_cI (div_pos hμ₀ (pow_pos h.rho_pos t))).comp
      (f := fun μ => μ / (R * β) ^ t) (continuous_id.div_const _).continuousAt
  exact continuousAt_const.mul (hc.sub continuousAt_const)

/-- Every `x₀ ≥ 0` is `Ξ(μ)` for some `μ ∈ (0, U'(I)]`. -/
theorem CSHyp.exists_wealth_eq (h : CSHyp U U' β R I) {x : ℝ} (hx : 0 ≤ x) :
    ∃ μ, 0 < μ ∧ μ ≤ U' I ∧ wealth U' β R I μ = x := by
  have hμ₁ : 0 < U' (I + x) := h.U'_pos (by linarith [h.hI])
  have hμ₁I : U' (I + x) ≤ U' I := h.U'_le h.hI (by linarith)
  have hcont : ContinuousOn (wealth U' β R I) (Icc (U' (I + x)) (U' I)) := fun μ hμ =>
    (h.continuousAt_wealth (hμ₁.trans_le hμ.1)).continuousWithinAt
  have hx1 : x ≤ wealth U' β R I (U' (I + x)) := by
    have := h.wealth_ge hμ₁
    rwa [h.cI_U' (by linarith : I ≤ I + x), add_sub_cancel_left] at this
  obtain ⟨μ, hμ, hμx⟩ := intermediate_value_Icc' hμ₁I hcont
    ⟨by rw [h.wealth_of_ge le_rfl]; exact hx, hx1⟩
  exact ⟨μ, hμ₁.trans_le hμ.1, hμ.2, hμx⟩

/-! ### The plan of a multiplier -/

/-- Wealth along the plan of `μ`: `x_t = Ξ(μ/(Rβ)ᵗ)`. -/
noncomputable def planμ (U' : ℝ → ℝ) (β R I μ : ℝ) (t : ℕ) : ℝ :=
  wealth U' β R I (μ / (R * β) ^ t)

/-- Consumption along the plan of `μ`: `c_t = cI(μ/(Rβ)ᵗ)`. -/
noncomputable def consμ (U' : ℝ → ℝ) (β R I μ : ℝ) (t : ℕ) : ℝ := cI U' I (μ / (R * β) ^ t)

theorem planμ_zero (μ : ℝ) : planμ U' β R I μ 0 = wealth U' β R I μ := by simp [planμ]

theorem consμ_zero (μ : ℝ) : consμ U' β R I μ 0 = cI U' I μ := by simp [consμ]

theorem div_pow_succ (μ ρ : ℝ) (t : ℕ) : μ / ρ ^ (t + 1) = μ / ρ ^ t / ρ := by
  rw [pow_succ, div_div]

/-- The budget constraint: `x_{t+1} = R(I + x_t − c_t)`. -/
theorem CSHyp.planμ_succ (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    planμ U' β R I μ (t + 1) = R * (I + planμ U' β R I μ t - consμ U' β R I μ t) := by
  have e := h.wealth_shift (div_pos hμ (pow_pos h.rho_pos t))
  rw [← div_pow_succ] at e
  simp only [planμ, consμ]
  set W := wealth U' β R I (μ / (R * β) ^ (t + 1))
  have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ h.hR.ne'
  rw [e]
  linear_combination (-W) * hRR

theorem CSHyp.consμ_eq (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    consμ U' β R I μ t = I + planμ U' β R I μ t - planμ U' β R I μ (t + 1) / R := by
  rw [h.planμ_succ hμ, mul_div_cancel_left₀ _ h.hR.ne']
  ring

theorem CSHyp.planμ_nonneg (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    0 ≤ planμ U' β R I μ t :=
  h.wealth_nonneg (div_pos hμ (pow_pos h.rho_pos t))

theorem CSHyp.consμ_ge (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    I ≤ consμ U' β R I μ t :=
  (h.cI_mem (div_pos hμ (pow_pos h.rho_pos t))).1

/-- The tail of a plan is a plan: `x_{t+s}` is the plan of `μ/(Rβ)ᵗ`. -/
theorem planμ_tail (μ : ℝ) (t s : ℕ) :
    planμ U' β R I (μ / (R * β) ^ t) s = planμ U' β R I μ (s + t) := by
  simp only [planμ, div_div, ← pow_add, add_comm t s]

theorem consμ_tail (μ : ℝ) (t s : ℕ) :
    consμ U' β R I (μ / (R * β) ^ t) s = consμ U' β R I μ (s + t) := by
  simp only [consμ, div_div, ← pow_add, add_comm t s]

/-- From some date on, the plan consumes `I` and holds no wealth. -/
theorem CSHyp.exists_plan_zero (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    ∃ K : ℕ, ∀ t, K ≤ t → planμ U' β R I μ t = 0 ∧ consμ U' β R I μ t = I := by
  obtain ⟨K, hK⟩ := h.exists_K hμ
  exact ⟨K, fun t ht => ⟨h.wealth_of_ge (hK t ht μ le_rfl), h.cI_of_le (hK t ht μ le_rfl)⟩⟩

/-- The Euler conditions along a plan: `RβU'(c_{t+1}) ≤ U'(c_t)`, with equality unless
`x_{t+1} = 0`. -/
theorem CSHyp.euler_step (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    R * β * U' (consμ U' β R I μ (t + 1)) ≤ U' (consμ U' β R I μ t) ∧
      (U' (consμ U' β R I μ t) - R * β * U' (consμ U' β R I μ (t + 1))) *
        planμ U' β R I μ (t + 1) = 0 := by
  have hρ := h.rho_pos
  set m := μ / (R * β) ^ t
  have hm : 0 < m := div_pos hμ (pow_pos hρ t)
  have hm' : m / (R * β) = μ / (R * β) ^ (t + 1) := (div_pow_succ μ (R * β) t).symm
  have hρm : R * β * (m / (R * β)) = m := mul_div_cancel₀ m hρ.ne'
  have hmm' : m ≤ m / (R * β) := le_div_self hm.le hρ h.hRβ.le
  simp only [consμ, planμ]
  rw [← hm']
  rcases eq_or_lt_of_le (h.cI_mem (hm.trans_le hmm')).1 with he | hgt
  · -- `c_{t+1} = I`: then `x_{t+1} = 0`
    have hUI : U' I ≤ m / (R * β) := by have := (h.cI_mem (hm.trans_le hmm')).2; rwa [← he] at this
    rw [h.wealth_of_ge hUI, mul_zero, ← he]
    refine ⟨?_, rfl⟩
    rcases eq_or_lt_of_le (h.cI_mem hm).1 with he' | hgt'
    · rw [← he']
      have := h.U'_pos h.hI
      nlinarith [h.hRβ]
    · rw [h.cI_eq hm hgt']
      have := mul_le_mul_of_nonneg_left hUI hρ.le
      rwa [hρm] at this
  · -- `c_{t+1} > I`: then `c_t > I` too and the Euler equation holds with equality
    have hgt' : I < cI U' I m := hgt.trans_le (h.cI_anti hm hmm')
    rw [h.cI_eq (hm.trans_le hmm') hgt, h.cI_eq hm hgt', hρm, sub_self, zero_mul]
    exact ⟨le_rfl, rfl⟩

/-! ### Summation by parts -/

/-- **Summation by parts.** If `Rp_{t+1} ≤ p_t`, with equality unless `x_{t+1} = 0`, and
`x' ≥ 0`, then `Σ_{t ≤ n} p_t(c'_t − c_t) ≤ p₀(x'₀ − x₀) + p_n(x_{n+1} − x'_{n+1})/R`, where
`c_t = x_t − x_{t+1}/R` (up to the common income `I`). -/
theorem abel_bound {R : ℝ} (hR : 0 < R) {p x x' : ℕ → ℝ}
    (hp : ∀ t, R * p (t + 1) ≤ p t) (hpx : ∀ t, (p t - R * p (t + 1)) * x (t + 1) = 0)
    (hx' : ∀ t, 0 ≤ x' t) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), p t * ((x' t - x' (t + 1) / R) - (x t - x (t + 1) / R)) ≤
      p 0 * (x' 0 - x 0) + p n * (x (n + 1) - x' (n + 1)) / R := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    apply le_of_eq
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : p n * (x (n + 1) - x' (n + 1)) / R + p (n + 1) * (x' (n + 1) - x (n + 1)) =
        -(x' (n + 1) * (p n - R * p (n + 1))) / R := by
      field_simp
      linear_combination hpx n
    have hk : 0 ≤ x' (n + 1) * (p n - R * p (n + 1)) / R :=
      div_nonneg (mul_nonneg (hx' (n + 1)) (by linarith [hp n])) hR.le
    have e : p (n + 1) * ((x' (n + 1) - x' (n + 1 + 1) / R) - (x (n + 1) - x (n + 1 + 1) / R)) =
        p (n + 1) * (x' (n + 1) - x (n + 1)) +
          p (n + 1) * (x (n + 1 + 1) - x' (n + 1 + 1)) / R := by
      ring
    rw [e]
    have : -(x' (n + 1) * (p n - R * p (n + 1))) / R =
        -(x' (n + 1) * (p n - R * p (n + 1)) / R) := neg_div _ _
    linarith

/-! ### The dynamic program -/

/-- Wealth levels `x ≥ 0`. -/
abbrev CSWealth := ↥(Ici (0 : ℝ))

/-- `Γ(x) = [0, (I + x)R]`. -/
def csΓ (R I : ℝ) (x : CSWealth) : Set CSWealth := {y | y.1 ≤ (I + x.1) * R}

/-- `F(x, y) = U(I + x − y/R)`, clamped at zero consumption off the graph of `Γ` (where it is
never evaluated). -/
noncomputable def csF (U : ℝ → ℝ) (R I : ℝ) (x y : CSWealth) : ℝ := U (max (I + x.1 - y.1 / R) 0)

/-- Consumption `c_t = I + x_t − x_{t+1}/R` along a plan. -/
noncomputable def consOf (R I : ℝ) (x : ℕ → CSWealth) (t : ℕ) : ℝ := I + (x t).1 - (x (t + 1)).1 / R

theorem CSHyp.consOf_nonneg (h : CSHyp U U' β R I) {z : CSWealth} {x : ℕ → CSWealth}
    (hx : x ∈ Feasible (csΓ R I) z) (t : ℕ) : 0 ≤ consOf R I x t := by
  have : (x (t + 1)).1 / R ≤ I + (x t).1 := (div_le_iff₀ h.hR).2 (hx.2 t)
  simp only [consOf]
  linarith

theorem CSHyp.csF_eq (h : CSHyp U U' β R I) {z : CSWealth} {x : ℕ → CSWealth}
    (hx : x ∈ Feasible (csΓ R I) z) (t : ℕ) : csF U R I (x t) (x (t + 1)) = U (consOf R I x t) := by
  change U (max (consOf R I x t) 0) = _
  rw [max_eq_left (h.consOf_nonneg hx t)]

theorem CSHyp.assumption41 (h : CSHyp U U' β R I) : Assumption41 (csΓ R I) := fun x =>
  ⟨⟨0, mem_Ici.2 le_rfl⟩, mul_nonneg (add_nonneg h.hI.le x.2) h.hR.le⟩

/-- `F ≥ U(0)`, so Assumption 4.2 holds. -/
theorem CSHyp.assumption42 (h : CSHyp U U' β R I) : Assumption42 (csΓ R I) (csF U R I) β :=
  assumption42_of_bddBelow (M := U 0) (fun _ _ => h.hUm.monotoneOn (mem_Ici.2 le_rfl)
    (mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)) h.hβ0.le h.hβ1

/-- The plan of `μ` as a sequence of wealth levels. -/
noncomputable def planN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) : CSWealth :=
  ⟨planμ U' β R I μ t, h.planμ_nonneg hμ t⟩

/-- The initial wealth `Ξ(μ)` of the plan of `μ`. -/
noncomputable def wealthN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) : CSWealth :=
  ⟨wealth U' β R I μ, h.wealth_nonneg hμ⟩

theorem CSHyp.planN_feasible (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    planN h hμ ∈ Feasible (csΓ R I) (wealthN h hμ) := by
  refine ⟨Subtype.ext (planμ_zero μ), fun t => ?_⟩
  change planμ U' β R I μ (t + 1) ≤ (I + planμ U' β R I μ t) * R
  rw [h.planμ_succ hμ]
  have := h.consμ_ge hμ t
  nlinarith [h.hR, h.hI]

theorem CSHyp.consOf_planN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (t : ℕ) :
    consOf R I (planN h hμ) t = consμ U' β R I μ t :=
  (h.consμ_eq hμ t).symm

/-- `V(μ) = Σ_t βᵗU(c_t)`, the value of the plan of `μ`. -/
noncomputable def valμ (U U' : ℝ → ℝ) (β R I μ : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * U (consμ U' β R I μ t)

theorem CSHyp.summable_val (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    Summable fun t : ℕ => β ^ t * U (consμ U' β R I μ t) := by
  obtain ⟨K, hK⟩ := h.exists_plan_zero hμ
  have hg : Summable fun t : ℕ => β ^ t * U I :=
    (summable_geometric_of_lt_one h.hβ0.le h.hβ1).mul_right _
  have hd : Summable fun t : ℕ => β ^ t * U (consμ U' β R I μ t) - β ^ t * U I :=
    summable_of_ne_finset_zero (s := Finset.range K) fun t ht => by
      rw [(hK t (by simpa using ht)).2, sub_self]
  exact (hd.add hg).congr fun t => by ring

theorem CSHyp.partialSum_planN (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    partialSum (csF U R I) β (planN h hμ) n =
      ∑ t ∈ Finset.range (n + 1), β ^ t * U (consμ U' β R I μ t) := by
  simp only [partialSum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h.csF_eq (h.planN_feasible hμ) t, h.consOf_planN hμ t]

theorem CSHyp.tendsto_plan (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n => partialSum (csF U R I) β (planN h hμ) n) atTop
      (𝓝 (valμ U U' β R I μ)) := by
  simp only [h.partialSum_planN hμ]
  exact (h.summable_val hμ).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem CSHyp.plan_total (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    total (csF U R I) β (planN h hμ) = (valμ U U' β R I μ : EReal) :=
  tendsto_nhds_unique (tendsto_total h.assumption42 (h.planN_feasible hμ))
    (EReal.tendsto_coe.2 (h.tendsto_plan hμ))

/-- The concavity gap `δ_t = U(c_t) + U'(c_t)(c'_t − c_t) − U(c'_t) ≥ 0`. -/
noncomputable def gapAt (U U' : ℝ → ℝ) (c c' : ℝ) : ℝ := U c + U' c * (c' - c) - U c'

theorem CSHyp.gapAt_nonneg (h : CSHyp U U' β R I) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c') :
    0 ≤ gapAt U U' c c' := by
  have := h.super_le hc hc'
  simp only [gapAt]
  linarith

/-- **The key bound.** Along any plan `x'` feasible from `z`, from some date on,
`Σ_{t ≤ n} βᵗU(c'_t) + Σ_{t ≤ n} βᵗδ_t ≤ Σ_{t ≤ n} βᵗU(c_t) + U'(c₀)(z − x₀)`. -/
theorem CSHyp.value_bound (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {z : CSWealth}
    {x' : ℕ → CSWealth} (hx' : x' ∈ Feasible (csΓ R I) z) :
    ∃ K : ℕ, ∀ n, K ≤ n →
      partialSum (csF U R I) β x' n + ∑ t ∈ Finset.range (n + 1),
        β ^ t * gapAt U U' (consμ U' β R I μ t) (consOf R I x' t) ≤
      partialSum (csF U R I) β (planN h hμ) n +
        U' (cI U' I μ) * (z.1 - wealth U' β R I μ) := by
  obtain ⟨K, hK⟩ := h.exists_plan_zero hμ
  refine ⟨K, fun n hn => ?_⟩
  have hc : ∀ t, consμ U' β R I μ t =
      I + planμ U' β R I μ t - planμ U' β R I μ (t + 1) / R := h.consμ_eq hμ
  have hp : ∀ t, R * (β ^ (t + 1) * U' (consμ U' β R I μ (t + 1))) ≤
      β ^ t * U' (consμ U' β R I μ t) := fun t => by
    have := mul_le_mul_of_nonneg_left (h.euler_step hμ t).1 (pow_nonneg h.hβ0.le t)
    calc R * (β ^ (t + 1) * U' (consμ U' β R I μ (t + 1)))
        = β ^ t * (R * β * U' (consμ U' β R I μ (t + 1))) := by ring
      _ ≤ _ := this
  have hpx : ∀ t, (β ^ t * U' (consμ U' β R I μ t) -
      R * (β ^ (t + 1) * U' (consμ U' β R I μ (t + 1)))) * planμ U' β R I μ (t + 1) = 0 :=
    fun t => by
      calc _ = β ^ t * ((U' (consμ U' β R I μ t) - R * β * U' (consμ U' β R I μ (t + 1))) *
            planμ U' β R I μ (t + 1)) := by ring
        _ = 0 := by rw [(h.euler_step hμ t).2, mul_zero]
  have hab := abel_bound h.hR hp hpx (x' := fun t => (x' t).1) (fun t => (x' t).2) n
  have hsum : partialSum (csF U R I) β x' n + ∑ t ∈ Finset.range (n + 1),
      β ^ t * gapAt U U' (consμ U' β R I μ t) (consOf R I x' t) =
      partialSum (csF U R I) β (planN h hμ) n + ∑ t ∈ Finset.range (n + 1),
        β ^ t * U' (consμ U' β R I μ t) * (((x' t).1 - (x' (t + 1)).1 / R) -
          (planμ U' β R I μ t - planμ U' β R I μ (t + 1) / R)) := by
    rw [h.partialSum_planN hμ]
    simp only [partialSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [h.csF_eq hx' t]
    simp only [gapAt, consOf]
    rw [hc t]
    ring
  have hxn : planμ U' β R I μ (n + 1) = 0 := (hK (n + 1) (by omega)).1
  have hpn : 0 ≤ β ^ n * U' (consμ U' β R I μ n) :=
    mul_nonneg (pow_nonneg h.hβ0.le n) (h.U'_pos (h.hI.trans_le (h.consμ_ge hμ n))).le
  have hlast : 0 ≤ β ^ n * U' (consμ U' β R I μ n) * (x' (n + 1)).1 / R :=
    div_nonneg (mul_nonneg hpn (x' (n + 1)).2) h.hR.le
  have hx0 : (x' 0).1 = z.1 := by rw [hx'.1]
  simp only [pow_zero, one_mul, consμ_zero, planμ_zero, hx0, hxn] at hab
  rw [hsum]
  have e : β ^ n * U' (consμ U' β R I μ n) * (0 - (x' (n + 1)).1) / R =
      -(β ^ n * U' (consμ U' β R I μ n) * (x' (n + 1)).1 / R) := by ring
  rw [e] at hab
  linarith

/-- Along any plan feasible from `z`: `u(x') ≤ V(μ) + U'(c₀)(z − x₀) − βᵗδ_t`. -/
theorem CSHyp.total_le (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {z : CSWealth}
    {x' : ℕ → CSWealth} (hx' : x' ∈ Feasible (csΓ R I) z) (t₀ : ℕ) :
    total (csF U R I) β x' ≤ ((valμ U U' β R I μ + U' (cI U' I μ) * (z.1 - wealth U' β R I μ) -
      β ^ t₀ * gapAt U U' (consμ U' β R I μ t₀) (consOf R I x' t₀) : ℝ) : EReal) := by
  obtain ⟨K, hK⟩ := h.value_bound hμ hx'
  have hgap : ∀ t, 0 ≤ β ^ t * gapAt U U' (consμ U' β R I μ t) (consOf R I x' t) := fun t =>
    mul_nonneg (pow_nonneg h.hβ0.le t) (h.gapAt_nonneg (h.hI.trans_le (h.consμ_ge hμ t))
      (h.consOf_nonneg hx' t))
  refine le_of_tendsto_of_tendsto (tendsto_total h.assumption42 hx')
    (EReal.tendsto_coe.2 (((h.tendsto_plan hμ).add_const
      (U' (cI U' I μ) * (z.1 - wealth U' β R I μ))).sub_const
        (β ^ t₀ * gapAt U U' (consμ U' β R I μ t₀) (consOf R I x' t₀)))) ?_
  filter_upwards [eventually_ge_atTop (max K t₀)] with n hn
  refine EReal.coe_le_coe_iff.2 ?_
  have hb := hK n (le_of_max_le_left hn)
  have hs := Finset.single_le_sum (f := fun t => β ^ t * gapAt U U' (consμ U' β R I μ t)
    (consOf R I x' t)) (fun t _ => hgap t)
    (Finset.mem_range.2 (by omega : t₀ < n + 1))
  linarith

/-- The supergradient bound `u(x') ≤ V(μ) + U'(c₀)(z − x₀)`. -/
theorem CSHyp.total_le_tangent (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {z : CSWealth}
    {x' : ℕ → CSWealth} (hx' : x' ∈ Feasible (csΓ R I) z) :
    total (csF U R I) β x' ≤
      ((valμ U U' β R I μ + U' (cI U' I μ) * (z.1 - wealth U' β R I μ) : ℝ) : EReal) := by
  refine (h.total_le hμ hx' 0).trans (EReal.coe_le_coe_iff.2 ?_)
  have := h.gapAt_nonneg (h.hI.trans_le (h.consμ_ge hμ 0)) (h.consOf_nonneg hx' 0)
  simp only [pow_zero, one_mul]
  linarith

/-- A feasible plan with the consumption of the plan of `μ`, from the same wealth, is that plan. -/
theorem CSHyp.eq_planN_of_cons (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ)
    {x' : ℕ → CSWealth} (h0 : (x' 0).1 = wealth U' β R I μ)
    (hc : ∀ t, consOf R I x' t = consμ U' β R I μ t) : x' = planN h hμ := by
  have key : ∀ t, (x' t).1 = planμ U' β R I μ t := by
    intro t
    induction t with
    | zero => rw [h0, planμ_zero]
    | succ t ih =>
      have e := hc t
      rw [h.consμ_eq hμ t] at e
      simp only [consOf] at e
      rw [ih] at e
      have hR := h.hR.ne'
      field_simp at e
      linarith
  funext t
  exact Subtype.ext (key t)

/-- **Uniqueness.** Every other plan feasible from `Ξ(μ)` does strictly worse. -/
theorem CSHyp.total_lt (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {x' : ℕ → CSWealth}
    (hx' : x' ∈ Feasible (csΓ R I) (wealthN h hμ)) (hne : x' ≠ planN h hμ) :
    total (csF U R I) β x' < (valμ U U' β R I μ : EReal) := by
  have hc : ∃ t, consOf R I x' t ≠ consμ U' β R I μ t := by
    by_contra hall
    push Not at hall
    exact hne (h.eq_planN_of_cons hμ (by rw [hx'.1]; rfl) hall)
  obtain ⟨t₀, ht₀⟩ := hc
  have hgap : 0 < gapAt U U' (consμ U' β R I μ t₀) (consOf R I x' t₀) := by
    have := h.super_lt (h.hI.trans_le (h.consμ_ge hμ t₀)) (h.consOf_nonneg hx' t₀) ht₀
    simp only [gapAt]
    linarith
  refine (h.total_le hμ hx' t₀).trans_lt (EReal.coe_lt_coe_iff.2 ?_)
  have := mul_pos (pow_pos h.hβ0 t₀) hgap
  simp only [wealthN, sub_self, mul_zero, add_zero]
  linarith

/-- `v*(Ξ(μ)) = V(μ)`. -/
theorem CSHyp.vstar_eq (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) :
    vstar (csΓ R I) (csF U R I) β (wealthN h hμ) = (valμ U U' β R I μ : EReal) := by
  refine le_antisymm (iSup₂_le fun x' hx' => (h.total_le_tangent hμ hx').trans ?_) ?_
  · simp [wealthN]
  · rw [← h.plan_total hμ]
    exact le_biSup (total (csF U R I) β) (h.planN_feasible hμ)

/-- The supergradient inequality `v*(z) ≤ v*(Ξ(μ)) + U'(c₀)(z − Ξ(μ))`. -/
theorem CSHyp.vstar_le_tangent (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) (z : CSWealth) :
    vstar (csΓ R I) (csF U R I) β z ≤
      ((valμ U U' β R I μ + U' (cI U' I μ) * (z.1 - wealth U' β R I μ) : ℝ) : EReal) :=
  iSup₂_le fun _ hx' => h.total_le_tangent hμ hx'

/-- The plan of `μ` is the unique optimal plan from `Ξ(μ)`. -/
theorem CSHyp.optimal_iff (h : CSHyp U U' β R I) {μ : ℝ} (hμ : 0 < μ) {x' : ℕ → CSWealth}
    (hx' : x' ∈ Feasible (csΓ R I) (wealthN h hμ)) :
    total (csF U R I) β x' = vstar (csΓ R I) (csF U R I) β (wealthN h hμ) ↔
      x' = planN h hμ := by
  rw [h.vstar_eq hμ]
  refine ⟨fun heq => by_contra fun hne => ?_, fun he => he ▸ h.plan_total hμ⟩
  exact lt_irrefl _ (heq ▸ h.total_lt hμ hx' hne)

/-- `v*` is real-valued: `v*(x) = V(μ)` for any `μ > 0` with `Ξ(μ) = x`. -/
theorem CSHyp.vstar_real (h : CSHyp U U' β R I) (x : CSWealth) :
    ∃ v : ℝ, vstar (csΓ R I) (csF U R I) β x = v := by
  obtain ⟨μ, hμ, -, hw⟩ := h.exists_wealth_eq x.2
  have : x = wealthN h hμ := Subtype.ext hw.symm
  exact ⟨_, this ▸ h.vstar_eq hμ⟩

/-- **Exercise 5.17a.** `v*` is real-valued and satisfies (FE), and an optimal plan satisfies
`v*(x_t) = U(I + x_t − x_{t+1}/R) + βv*(x_{t+1})`. -/
theorem ex_5_17a (h : CSHyp U U' β R I) :
    (∀ x : CSWealth, ∃ v : ℝ, vstar (csΓ R I) (csF U R I) β x = v) ∧
      SatisfiesFE (csΓ R I) (csF U R I) β (vstar (csΓ R I) (csF U R I) β) ∧
      ∀ (x₀ : CSWealth) (xs : ℕ → CSWealth), xs ∈ Feasible (csΓ R I) x₀ →
        total (csF U R I) β xs = vstar (csΓ R I) (csF U R I) β x₀ → ∀ t,
          vstar (csΓ R I) (csF U R I) β (xs t) = (U (consOf R I xs t) : EReal) +
            (β : EReal) * vstar (csΓ R I) (csF U R I) β (xs (t + 1)) :=
  ⟨h.vstar_real, theorem_4_2 h.hβ0.le h.assumption41 h.assumption42,
    fun _ _ hxs hopt t => by
      rw [theorem_4_4 h.hβ0 h.assumption42 hxs hopt t, h.csF_eq hxs t]⟩

end StokeyLucasPrescott.DeterministicApplications
