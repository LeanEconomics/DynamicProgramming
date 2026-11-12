/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.Huggett
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# More government debt moves the Bewley economy towards full insurance (Figure 11.7)

AKMM, §11.4.1, "Assets in positive supply", p. 319, Figure 11.7: in Bewley's endowment economy
the government supplies `B` bonds and the equilibrium rate solves `A(r*) = B`; "as `B` increases,
the economy moves closer to the full insurance outcome", i.e. `r*` rises towards the
complete-markets rate `r^{CM} = 1/β − 1`, where the household problem has no precautionary
motive (`hg_rate_below_cm`).

As in `Huggett`, the aggregate asset demand `A` is a function given as a hypothesis, continuous on
`[−1, r^{CM})` with `A(−1) = −a` (`hg_A_at_minus_one`) and `A(r) → ∞` as `r ↑ r^{CM}`; for
every `B > −a` an equilibrium exists (`hg_existence`).

* **Every selection of equilibrium rates tends to `r^{CM}` as `B → ∞`** (`bwy_rate_tendsto_cm`):
  `A` is bounded on each `[−1, r̄]`, `r̄ < r^{CM}`, so a large enough `B` can only be met above
  `r̄`. **Full insurance is not reached at any finite `B`**: `r* < r^{CM}` always
  (`bwy_eqm_exists_below_cm`).
* **The lowest equilibrium rate rises with `B`** (`bwy_lower_eqm`): below every equilibrium rate
  at `B′` there is an equilibrium rate at each `B ∈ (−a, B′)`. If `A` is strictly increasing (as
  drawn) the equilibrium rate is strictly increasing in `B` (`bwy_rate_strictMono`).
* **Taxes.** With `T = rB` the household's income depends on `B`, so in fact `A = A(r, B)`; the
  figure holds `A` fixed. The convergence survives if `A(·, B)` is bounded above on each
  `[−1, r̄]` uniformly in `B` (`bwy_rate_tendsto_cm_dep`, of which `bwy_rate_tendsto_cm` is the
  fixed-`A` case).
* A concrete instance, `A(r) = −1 + (1 + r)/(1 − r)` with `β = 1/2`, `a = 1`: the equilibrium
  rate is `B/(B + 2)`, increasing to `r^{CM} = 1` (`bwy_example`).

Departures: "closer to the full insurance outcome" is read as the equilibrium rate approaching the
complete-markets rate (the content of the figure); consumption dispersion is not formalised.
-/

namespace AKMM.Consumption

open Filter Topology

/-- **Figure 11.7, with `A` depending on `B`.** If `A(·, B)` is bounded above on each
`[−1, r̄]`, `r̄ < r^{CM}`, uniformly in `B`, then any equilibrium rates `r(B) ∈ (−1, r^{CM})`
with `A(r(B), B) = B` (for all large `B`) tend to `r^{CM}` from below as `B → ∞`. -/
theorem bwy_rate_tendsto_cm_dep {A : ℝ → ℝ → ℝ} {rcm : ℝ}
    (hbound : ∀ rbar < rcm, ∃ K, ∀ B r, r ∈ Set.Icc (-1) rbar → A r B ≤ K) {req : ℝ → ℝ}
    (heq : ∀ᶠ B in atTop, req B ∈ Set.Ioo (-1) rcm ∧ A (req B) B = B) :
    Tendsto req atTop (𝓝[<] rcm) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩,
    heq.mono fun B hB => hB.1.2⟩
  · obtain ⟨K, hK⟩ := hbound a ha
    filter_upwards [heq, eventually_gt_atTop K] with B hB hBK
    by_contra hle
    push Not at hle
    have := hK B (req B) ⟨hB.1.1.le, hle⟩
    rw [hB.2] at this
    linarith
  · exact heq.mono fun B hB => lt_trans hB.1.2 ha

/-- **Figure 11.7: more debt moves the economy towards full insurance.** If `A` is continuous on
`[−1, r^{CM})`, any equilibrium rates `r(B) ∈ (−1, r^{CM})` with `A(r(B)) = B` tend to
`r^{CM} = 1/β − 1` from below as `B → ∞`. -/
theorem bwy_rate_tendsto_cm {A : ℝ → ℝ} {β : ℝ} (hA : ContinuousOn A (Set.Ico (-1) (1 / β - 1)))
    {req : ℝ → ℝ} (heq : ∀ᶠ B in atTop, req B ∈ Set.Ioo (-1) (1 / β - 1) ∧ A (req B) = B) :
    Tendsto req atTop (𝓝[<] (1 / β - 1)) := by
  refine bwy_rate_tendsto_cm_dep (A := fun r _ => A r) (fun rbar hrbar => ?_) heq
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := rbar)).bddAbove_image
    (hA.mono fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hrbar⟩)
  exact ⟨K, fun _ r hr => hK ⟨r, hr, rfl⟩⟩

/-- **AKMM, p. 319: for every bond supply `B > −a` there is an equilibrium, and its rate is below
`r^{CM}`**: full insurance is not reached at any finite `B` (`hg_existence`). -/
theorem bwy_eqm_exists_below_cm {A : ℝ → ℝ} {β φ : ℝ} (hβ : 0 < β)
    (hA : ContinuousOn A (Set.Ico (-1) (1 / β - 1)))
    (hlim : Tendsto A (𝓝[<] (1 / β - 1)) atTop) (hA1 : A (-1) = -φ) {B : ℝ} (hB : -φ < B) :
    ∃ r ∈ Set.Ioo (-1) (1 / β - 1), A r = B ∧ r < 1 / β - 1 := by
  obtain ⟨r, hr, hAr⟩ := hg_existence hβ hA hlim hA1 hB
  exact ⟨r, hr, hAr, hr.2⟩

/-- **The lowest equilibrium rate rises with `B`.** If `r′` is an equilibrium rate for supply
`B′` and `−a < B < B′`, there is an equilibrium rate `r < r′` for `B`. -/
theorem bwy_lower_eqm {A : ℝ → ℝ} {rcm φ : ℝ} (hA : ContinuousOn A (Set.Ico (-1) rcm))
    (hA1 : A (-1) = -φ) {B B' r' : ℝ} (hB : -φ < B) (hBB : B < B')
    (hr' : r' ∈ Set.Ioo (-1) rcm) (hAr' : A r' = B') : ∃ r ∈ Set.Ioo (-1) r', A r = B := by
  have hsub : Set.Icc (-1) r' ⊆ Set.Ico (-1) rcm := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hr'.2⟩
  obtain ⟨r, hr, hAr⟩ := intermediate_value_Icc hr'.1.le (hA.mono hsub)
    (show B ∈ Set.Icc (A (-1)) (A r') from ⟨by rw [hA1]; exact hB.le, by rw [hAr']; exact hBB.le⟩)
  refine ⟨r, ⟨?_, ?_⟩, hAr⟩
  · rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h, hA1] at hAr; linarith
    · exact h
  · rcases eq_or_lt_of_le hr.2 with h | h
    · rw [h, hAr'] at hAr; linarith
    · exact h

/-- **With `A` strictly increasing (as drawn in Figure 11.7) the equilibrium rate is strictly
increasing in `B`.** -/
theorem bwy_rate_strictMono {A : ℝ → ℝ} {S : Set ℝ} (hA : StrictMonoOn A S) {B B' r r' : ℝ}
    (hr : r ∈ S) (hr' : r' ∈ S) (hAr : A r = B) (hAr' : A r' = B') (hBB : B < B') : r < r' := by
  by_contra hle
  push Not at hle
  have := hA.monotoneOn hr' hr hle
  linarith

/-- **A concrete instance.** With `β = 1/2` (`r^{CM} = 1`), `a = 1` and
`A(r) = −1 + (1 + r)/(1 − r)`, `A` is continuous on `[−1, 1)`, `A(−1) = −1`, `A → ∞` at `1`; the
equilibrium rate at `B > −1` is `B/(B + 2)`, and it tends to `r^{CM}` as `B → ∞`. -/
theorem bwy_example :
    ContinuousOn (fun r : ℝ => -1 + (1 + r) / (1 - r)) (Set.Ico (-1) (1 / (1 / 2) - 1)) ∧
    (fun r : ℝ => -1 + (1 + r) / (1 - r)) (-1) = -1 ∧
    Tendsto (fun r : ℝ => -1 + (1 + r) / (1 - r)) (𝓝[<] (1 / (1 / 2) - 1)) atTop ∧
    (∀ B : ℝ, -1 < B → B / (B + 2) ∈ Set.Ioo (-1) (1 / (1 / 2) - 1) ∧
      -1 + (1 + B / (B + 2)) / (1 - B / (B + 2)) = B) ∧
    Tendsto (fun B : ℝ => B / (B + 2)) atTop (𝓝[<] (1 / (1 / 2) - 1)) := by
  have hcm : (1 : ℝ) / (1 / 2) - 1 = 1 := by norm_num
  have hcont : ContinuousOn (fun r : ℝ => -1 + (1 + r) / (1 - r)) (Set.Ico (-1) 1) := by
    refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) fun r hr => ?_)
    have := hr.2; linarith
  have heqm : ∀ B : ℝ, -1 < B → B / (B + 2) ∈ Set.Ioo (-1) 1 ∧
      -1 + (1 + B / (B + 2)) / (1 - B / (B + 2)) = B := by
    intro B hB
    have h2 : 0 < B + 2 := by linarith
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ h2]; linarith
    · rw [div_lt_one h2]; linarith
    · have h3 : 1 - B / (B + 2) = 2 / (B + 2) := by field_simp; ring
      rw [h3]
      field_simp
      ring
  rw [hcm]
  refine ⟨hcont, by norm_num, ?_, heqm, ?_⟩
  · -- `(1 + r)/(1 − r) → ∞` as `r ↑ 1`
    have h1 : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sub_pos.2 (Set.mem_Iio.1 hr)
    have h2 : Tendsto (fun r : ℝ => (1 - r)⁻¹) (𝓝[<] 1) atTop :=
      tendsto_inv_nhdsGT_zero.comp h1
    have h3 : Tendsto (fun r : ℝ => 1 + r) (𝓝[<] 1) (𝓝 2) := by
      have : Tendsto (fun r : ℝ => 1 + r) (𝓝 1) (𝓝 (1 + 1)) :=
        (continuous_const.add continuous_id).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun r : ℝ => (1 + r) * (1 - r)⁻¹) (𝓝[<] 1) atTop :=
      Tendsto.pos_mul_atTop (by norm_num) h3 h2
    exact tendsto_atTop_add_const_left _ (-1) (h4.congr fun r => (div_eq_mul_inv _ _).symm)
  · have h := bwy_rate_tendsto_cm (A := fun r : ℝ => -1 + (1 + r) / (1 - r)) (β := 1 / 2)
      (req := fun B : ℝ => B / (B + 2)) (by rw [hcm]; exact hcont)
      (by
        rw [hcm]
        filter_upwards [eventually_gt_atTop (-1 : ℝ)] with B hB using heqm B hB)
    rwa [hcm] at h

end AKMM.Consumption
