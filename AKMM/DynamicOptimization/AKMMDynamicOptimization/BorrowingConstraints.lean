/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.InfiniteHorizon

/-!
# Constraints in the consumption–saving problem: Theorem .3

AKMM, App. 4.A.1, pp. 827–829. Flow budget `a_{t+1} = (1 + r)a_t + w_t − c_t` (4.A.1), `r > −1`,
consumption `c_t ≥ 0`, and discounted wages `Σ w_t/(1 + r)ᵗ` finite.

* (4.A.2): `Σ_{t≤T} c_t/(1 + r)ᵗ + a_{T+1}/(1 + r)ᵀ = (1 + r)a₀ + Σ_{t≤T} w_t/(1 + r)ᵗ`
  (`eq_4A_2`).
* p. 827: `lim a_{T+1} ≥ 0` is too restrictive — a constant debt `−ε` is feasible and repaid
  forever (`appendix_4A_too_restrictive`).
* **Theorem .3** (`theorem_4A_3`): for a consumption plan, (i) the flow budget with the no-Ponzi
  condition (4.A.3), (ii) the flow budget with the natural borrowing limit (4.A.5) at every `t`,
  and (iii) the lifetime budget constraint (4.A.4) are equivalent. The nPg condition is read as
  "`a_{T+1}/(1 + r)ᵀ` converges to a limit `≥ 0`", as printed.
-/

namespace AKMM.DynamicOptimization

open Filter Topology

variable {r : ℝ} {a w c : ℕ → ℝ}

/-- **AKMM, (4.A.2), p. 827.** Combining the flow budget constraints (4.A.1) up to `T`. -/
theorem eq_4A_2 (hr : -1 < r) (hflow : ∀ t, a (t + 1) = (1 + r) * a t + w t - c t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t + a (T + 1) / (1 + r) ^ T =
      (1 + r) * a 0 + ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  induction T with
  | zero => simp only [zero_add, Finset.sum_range_one, pow_zero, div_one, hflow 0]; ring
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => c t / (1 + r) ^ t) (T + 1),
      Finset.sum_range_succ (fun t => w t / (1 + r) ^ t) (T + 1)]
    have h1 : (1 + r) ^ T ≠ 0 := (pow_pos hr' T).ne'
    have h2 : (1 + r) ^ (T + 1) ≠ 0 := (pow_pos hr' (T + 1)).ne'
    have e : a (T + 1 + 1) / (1 + r) ^ (T + 1) =
        a (T + 1) / (1 + r) ^ T + (w (T + 1) - c (T + 1)) / (1 + r) ^ (T + 1) := by
      rw [hflow (T + 1), pow_succ]; field_simp; ring
    rw [e, sub_div]
    linarith

/-- **AKMM, p. 827: `lim a_{T+1} ≥ 0` is too restrictive.** With a constant wage `w̄ > 0`, `r > 0`
and `0 < ε < w̄/(1 + r)`, holding the debt `a_t = −ε` forever with `c_t = w̄ − rε > 0` satisfies the
flow budget and the no-Ponzi condition (`a_{T+1}/(1 + r)ᵀ → 0`), but `a_{T+1} → −ε < 0`. -/
theorem appendix_4A_too_restrictive {wbar ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hεw : ε < wbar / (1 + r)) :
    (∀ t : ℕ, (fun _ : ℕ => -ε) (t + 1) = (1 + r) * (fun _ : ℕ => -ε) t + wbar -
      (wbar - r * ε)) ∧ 0 < wbar - r * ε ∧
      Tendsto (fun T : ℕ => -ε / (1 + r) ^ T) atTop (𝓝 0) ∧
      Tendsto (fun _ : ℕ => -ε) atTop (𝓝 (-ε)) ∧ -ε < 0 := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  refine ⟨fun t => by ring, ?_, ?_, tendsto_const_nhds, by linarith⟩
  · rw [lt_div_iff₀ hr'] at hεw; nlinarith
  · have : Tendsto (fun T : ℕ => (1 + r) ^ T) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    exact tendsto_const_nhds.div_atTop this

/-- The partial sums of `c_t/(1 + r)ᵗ` from the flow budget: `(4.A.2)` rearranged. -/
theorem appendix_4A_partial (hr : -1 < r) (hflow : ∀ t, a (t + 1) = (1 + r) * a t + w t - c t)
    (T : ℕ) : ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t =
      (1 + r) * a 0 + ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t -
        a (T + 1) / (1 + r) ^ T := by
  linarith [eq_4A_2 hr hflow T]

/-- **Theorem .3** (AKMM, App. 4.A.1, p. 828). Let `r > −1`, `c ≥ 0`, `Σ w_t/(1 + r)ᵗ` summable,
and let `a` follow the flow budget (4.A.1). The following are equivalent:
(i) the no-Ponzi-game condition (4.A.3): `a_{T+1}/(1 + r)ᵀ → L` for some `L ≥ 0`;
(ii) the natural borrowing limit (4.A.5): `a_{t+1} ≥ −Σ_{s>t} w_s/(1 + r)^{s−t}` for all `t`;
(iii) the lifetime budget constraint (4.A.4): `Σ c_t/(1 + r)ᵗ` is finite and
`Σ c_t/(1 + r)ᵗ ≤ (1 + r)a₀ + Σ w_t/(1 + r)ᵗ`. -/
theorem theorem_4A_3 (hr : -1 < r) (hc : ∀ t, 0 ≤ c t)
    (hw : Summable fun t => w t / (1 + r) ^ t)
    (hflow : ∀ t, a (t + 1) = (1 + r) * a t + w t - c t) :
    List.TFAE [∃ L, 0 ≤ L ∧ Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 L),
      ∀ t, -∑' j, w (j + (t + 1)) / (1 + r) ^ (j + 1) ≤ a (t + 1),
      (Summable fun t => c t / (1 + r) ^ t) ∧
        ∑' t, c t / (1 + r) ^ t ≤ (1 + r) * a 0 + ∑' t, w t / (1 + r) ^ t] := by
  have hr' : (0 : ℝ) < 1 + r := by linarith
  have hcn : ∀ t, 0 ≤ c t / (1 + r) ^ t := fun t => div_nonneg (hc t) (pow_pos hr' t).le
  set W := ∑' t, w t / (1 + r) ^ t
  have hWlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t) atTop (𝓝 W) :=
    (tendsto_add_atTop_iff_nat 1).2 hw.hasSum.tendsto_sum_nat
  -- the natural limit in discounted form (4.A.7)
  have hdisc : ∀ t, ∑' j, w (j + (t + 1)) / (1 + r) ^ (j + (t + 1)) =
      (∑' j, w (j + (t + 1)) / (1 + r) ^ (j + 1)) / (1 + r) ^ t := by
    intro t
    rw [← tsum_div_const]
    congr 1; funext j
    rw [show j + (t + 1) = (j + 1) + t by ring, pow_add]
    field_simp
  tfae_have 1 → 3 := by
    rintro ⟨L, hL, hlim⟩
    have hpart : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t) atTop
        (𝓝 ((1 + r) * a 0 + W - L)) := by
      simp only [appendix_4A_partial hr hflow]
      exact (tendsto_const_nhds.add hWlim).sub hlim
    have hs : HasSum (fun t => c t / (1 + r) ^ t) ((1 + r) * a 0 + W - L) :=
      (hasSum_iff_tendsto_nat_of_nonneg hcn _).2 ((tendsto_add_atTop_iff_nat 1).1 hpart)
    exact ⟨hs.summable, by rw [hs.tsum_eq]; linarith⟩
  tfae_have 3 → 1 := by
    rintro ⟨hs, hle⟩
    refine ⟨(1 + r) * a 0 + W - ∑' t, c t / (1 + r) ^ t, by linarith, ?_⟩
    have h1 := (tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat
    have : ∀ T, a (T + 1) / (1 + r) ^ T = (1 + r) * a 0 +
        ∑ t ∈ Finset.range (T + 1), w t / (1 + r) ^ t -
          ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t := fun T => by
      linarith [eq_4A_2 hr hflow T]
    simp only [this]
    exact (tendsto_const_nhds.add hWlim).sub h1
  tfae_have 1 → 2 := by
    intro h1
    obtain ⟨hs, -⟩ := (tfae_1_to_3 h1)
    obtain ⟨L, hL, hlim⟩ := h1
    have hLval : L = (1 + r) * a 0 + W - ∑' t, c t / (1 + r) ^ t := by
      have hpart : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t) atTop
          (𝓝 ((1 + r) * a 0 + W - L)) := by
        simp only [appendix_4A_partial hr hflow]
        exact (tendsto_const_nhds.add hWlim).sub hlim
      have := tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat)
        hpart
      linarith
    intro t
    have hsplitw := hw.sum_add_tsum_nat_add (t + 1)
    have hsplitc := hs.sum_add_tsum_nat_add (t + 1)
    have hat : a (t + 1) / (1 + r) ^ t = (1 + r) * a 0 +
        ∑ s ∈ Finset.range (t + 1), w s / (1 + r) ^ s -
          ∑ s ∈ Finset.range (t + 1), c s / (1 + r) ^ s := by
      linarith [eq_4A_2 hr hflow t]
    have htc : 0 ≤ ∑' j, c (j + (t + 1)) / (1 + r) ^ (j + (t + 1)) :=
      tsum_nonneg fun j => hcn _
    -- `a_{t+1}/(1 + r)ᵗ = L − Σ_{s>t}(w_s − c_s)/(1 + r)ˢ ≥ −Σ_{s>t} w_s/(1 + r)ˢ`
    have hge : -∑' j, w (j + (t + 1)) / (1 + r) ^ (j + (t + 1)) ≤ a (t + 1) / (1 + r) ^ t := by
      rw [hat]; linarith
    rw [hdisc t, ← neg_div, div_le_div_iff_of_pos_right (pow_pos hr' t)] at hge
    exact hge
  tfae_have 2 → 3 := by
    intro h2
    -- (4.A.7): `a_{T+1}/(1 + r)ᵀ ≥ −Σ_{s>T} w_s/(1 + r)ˢ`, and the tail tends to `0`
    have h7 : ∀ T, -∑' j, w (j + (T + 1)) / (1 + r) ^ (j + (T + 1)) ≤
        a (T + 1) / (1 + r) ^ T := fun T => by
      rw [hdisc T, ← neg_div, div_le_div_iff_of_pos_right (pow_pos hr' T)]
      exact h2 T
    have hbound : ∀ T, ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t ≤ (1 + r) * a 0 + W := by
      intro T
      have := hw.sum_add_tsum_nat_add (T + 1)
      rw [appendix_4A_partial hr hflow T]
      linarith [h7 T]
    have hs : Summable fun t => c t / (1 + r) ^ t := by
      refine summable_of_sum_range_le (c := (1 + r) * a 0 + W) hcn fun n => ?_
      rcases n with _ | n
      · have h0 := hbound 0
        rw [zero_add, Finset.sum_range_one] at h0
        rw [Finset.range_zero, Finset.sum_empty]
        linarith [hcn 0]
      · exact hbound n
    refine ⟨hs, ?_⟩
    exact le_of_tendsto' ((tendsto_add_atTop_iff_nat 1).2 hs.hasSum.tendsto_sum_nat) hbound
  tfae_finish

end AKMM.DynamicOptimization
