/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMWelfare.OGProduction

/-!
# Figure .1: the golden rule and the efficient and inefficient regions

AKMM, Appendix 6.A, p. 838, Figure .1 ("Efficiency of the steady state"). The figure plots
steady-state consumption `c⋆ = f(k⋆) − k⋆` against `k⋆`, with `f(k) = F(k, ω_y + ω_o) + (1 − δ)k`
(corrected as in `appendix_6A_printed_f`): a hump with its peak `c^G` at the golden rule `k^G`,
the region left of `k^G` labelled "Efficient" and `f′(k⋆) ≥ 1`, the region right of it
"Inefficient" and `f′(k⋆) < 1`. The text says the golden rule maximises `c^G`.

For `f` strictly concave on `[0, ∞)`, differentiable at every `k > 0`, and a golden rule
`k^G > 0` with `f′(k^G) = 1` (the figure's assumption; the book states none):

* `c⋆` is uniquely maximised at `k^G` (`goldenrule_max`), strictly increasing on `[0, k^G]` and
  strictly decreasing on `[k^G, ∞)` (`goldenrule_increasing`, `goldenrule_decreasing`);
* `f′(k⋆) ≥ 1` iff `k⋆ ≤ k^G`, `f′(k⋆) < 1` iff `k⋆ > k^G` (`goldenrule_slope_iff`);
* with Theorem .5 (`theorem_A5`), a steady state `k⋆ > 0` with `c⋆ ≥ 0` is efficient iff
  `k⋆ ≤ k^G` (`goldenrule_efficient_iff`).

Together: `figure_A1`. Instance: `f(k) = 2√k + k/2` has its golden rule at `k^G = 4`
(`figure_A1_instance`, `figure_A1_instance_regions`).
-/

namespace AKMM.Welfare

open Miao.OverlappingGenerations

/-- **Figure .1: the slope of `f` against the golden rule.** For `f` strictly concave on
`[0, ∞)` with `f′(k^G) = 1`: `f′(k) > 1` for `0 < k < k^G` and `f′(k) < 1` for `k > k^G`. -/
theorem goldenrule_slope {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) {k : ℝ} (hk : 0 < k) :
    (k < kG → 1 < f' k) ∧ (kG < k → f' k < 1) := by
  have hkG' : kG ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 hkG.le
  have hk' : k ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 hk.le
  have hdG := hd kG hkG
  rw [hG] at hdG
  constructor
  · intro hlt
    have h1 := op_strictConcave_tangent hconc hkG' hk' hlt.ne hdG
    have h2 := op_strictConcave_tangent hconc hk' hkG' hlt.ne' (hd k hk)
    by_contra hcon
    push Not at hcon
    nlinarith
  · intro hlt
    have h1 := op_strictConcave_tangent hconc hkG' hk' hlt.ne' hdG
    have h2 := op_strictConcave_tangent hconc hk' hkG' hlt.ne (hd k hk)
    by_contra hcon
    push Not at hcon
    nlinarith

/-- **Figure .1: the efficient region is left of the golden rule** (AKMM, p. 838). For `k > 0`,
`f′(k) ≥ 1` iff `k ≤ k^G`. -/
theorem goldenrule_slope_iff {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) {k : ℝ} (hk : 0 < k) : 1 ≤ f' k ↔ k ≤ kG := by
  obtain ⟨h1, h2⟩ := goldenrule_slope hkG hconc hd hG hk
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    linarith [h2 hcon]
  · intro h
    rcases h.lt_or_eq with hlt | rfl
    · exact (h1 hlt).le
    · exact hG.ge

/-- **Figure .1: the golden rule maximises steady-state consumption** (AKMM, p. 838):
`f(k) − k < f(k^G) − k^G` for every `k ≥ 0`, `k ≠ k^G`. -/
theorem goldenrule_max {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) {k : ℝ} (hk : 0 ≤ k) (hne : k ≠ kG) : f k - k < f kG - kG := by
  have hdG := hd kG hkG
  rw [hG] at hdG
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hkG.le) (Set.mem_Ici.2 hk) hne hdG
  linarith

/-- **Figure .1: the rising branch** (AKMM, p. 838). `c⋆ = f(k⋆) − k⋆` is strictly increasing
on `[0, k^G]`. -/
theorem goldenrule_increasing {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) : StrictMonoOn (fun k => f k - k) (Set.Icc 0 kG) := by
  intro y hy z hz hyz
  have hz0 : 0 < z := hy.1.trans_lt hyz
  have hs := (goldenrule_slope_iff hkG hconc hd hG hz0).2 hz.2
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hz0.le) (Set.mem_Ici.2 hy.1) hyz.ne
    (hd z hz0)
  have h2 : f' z * (y - z) ≤ y - z := by nlinarith
  simp only
  linarith

/-- **Figure .1: the falling branch** (AKMM, p. 838). `c⋆ = f(k⋆) − k⋆` is strictly decreasing
on `[k^G, ∞)`. -/
theorem goldenrule_decreasing {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) : StrictAntiOn (fun k => f k - k) (Set.Ici kG) := by
  intro y hy z _ hyz
  have hy0 : 0 < y := hkG.trans_le hy
  have hs : f' y ≤ 1 := by
    rcases (Set.mem_Ici.1 hy).lt_or_eq with hlt | rfl
    · exact ((goldenrule_slope hkG hconc hd hG hy0).2 hlt).le
    · exact hG.le
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hy0.le)
    (Set.mem_Ici.2 (hy0.le.trans hyz.le)) hyz.ne' (hd y hy0)
  have h2 : f' y * (z - y) ≤ z - y := by nlinarith
  simp only
  linarith

/-- **Figure .1: efficient iff left of the golden rule** (AKMM, p. 838, with Theorem .5). A
steady state `k⋆ > 0` with `c⋆ = f(k⋆) − k⋆ ≥ 0` is dynamically efficient iff `k⋆ ≤ k^G`. -/
theorem goldenrule_efficient_iff {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) {kstar : ℝ} (hk : 0 < kstar) (hc : 0 ≤ f kstar - kstar) :
    deEfficient (fun _ => f) (fun _ => kstar) ↔ kstar ≤ kG := by
  rw [theorem_A5 hk hc hconc (hd kstar hk)]
  exact goldenrule_slope_iff hkG hconc hd hG hk

/-- **Figure .1** (AKMM, Appendix 6.A, p. 838). For `f` strictly concave on `[0, ∞)`,
differentiable at every `k > 0`, with a golden rule `k^G > 0`, `f′(k^G) = 1`: steady-state
consumption `c⋆ = f(k⋆) − k⋆` is uniquely maximised at `k^G` (the peak `c^G`), strictly
increasing on `[0, k^G]` and strictly decreasing on `[k^G, ∞)`; `f′(k⋆) ≥ 1` exactly left of
`k^G`; and a steady state `k⋆ > 0` with `c⋆ ≥ 0` is efficient exactly when `k⋆ ≤ k^G`, inefficient
when `k⋆ > k^G`. -/
theorem figure_A1 {f f' : ℝ → ℝ} {kG : ℝ} (hkG : 0 < kG)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hG : f' kG = 1) :
    (∀ k, 0 ≤ k → k ≠ kG → f k - k < f kG - kG) ∧
      StrictMonoOn (fun k => f k - k) (Set.Icc 0 kG) ∧
      StrictAntiOn (fun k => f k - k) (Set.Ici kG) ∧
      (∀ k, 0 < k → (1 ≤ f' k ↔ k ≤ kG)) ∧
      ∀ k, 0 < k → 0 ≤ f k - k →
        (deEfficient (fun _ => f) (fun _ => k) ↔ k ≤ kG) ∧
          (¬ deEfficient (fun _ => f) (fun _ => k) ↔ kG < k) :=
  ⟨fun _ hk hne => goldenrule_max hkG hconc hd hG hk hne,
    goldenrule_increasing hkG hconc hd hG, goldenrule_decreasing hkG hconc hd hG,
    fun _ hk => goldenrule_slope_iff hkG hconc hd hG hk,
    fun _ hk hc => ⟨goldenrule_efficient_iff hkG hconc hd hG hk hc, by
      rw [goldenrule_efficient_iff hkG hconc hd hG hk hc, not_le]⟩⟩

/-- **Figure .1, an instance.** `f(k) = 2√k + k/2` (`F = 2√k`, `δ = 1/2`) is strictly concave on
`[0, ∞)` with `f′(k) = 1/√k + 1/2` for `k > 0` and golden rule `k^G = 4`, so `figure_A1` applies:
steady states `k⋆ ∈ (0, 4]` are efficient, `k⋆ > 4` (with `c⋆ ≥ 0`) inefficient. -/
theorem figure_A1_instance :
    StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k + (1 - 1 / 2) * k) ∧
      (∀ k : ℝ, 0 < k → HasDerivAt (fun k : ℝ => 2 * √k + (1 - 1 / 2) * k)
        (1 / √k + (1 - 1 / 2)) k) ∧
      1 / √(4 : ℝ) + (1 - 1 / 2) = 1 := by
  refine ⟨?_, fun k hk => ?_, ?_⟩
  · have hsq := Real.strictConcaveOn_sqrt
    have h2 : StrictConcaveOn ℝ (Set.Ici 0) (fun k : ℝ => 2 * √k) := by
      refine ⟨hsq.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
      have := hsq.2 hx hy hxy ha hb hab
      simp only [smul_eq_mul] at this ⊢
      linarith
    exact h2.add_concaveOn ((concaveOn_id (convex_Ici 0)).smul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2))
  · have h := ((Real.hasDerivAt_sqrt hk.ne').const_mul 2).add
      ((hasDerivAt_id k).const_mul (1 - 1 / 2 : ℝ))
    refine h.congr_deriv ?_
    have : √k ≠ 0 := (Real.sqrt_pos.2 hk).ne'
    field_simp
  · have e : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e]
    norm_num

/-- **Figure .1, the instance's regions.** For `f(k) = 2√k + k/2`, a steady state `k⋆ > 0` with
`c⋆ ≥ 0` is efficient iff `k⋆ ≤ 4`; e.g. `k⋆ = 9` (`c⋆ = 3/2`) is inefficient. -/
theorem figure_A1_instance_regions :
    (∀ k : ℝ, 0 < k → 0 ≤ 2 * √k + (1 - 1 / 2) * k - k →
      (deEfficient (fun _ => fun k : ℝ => 2 * √k + (1 - 1 / 2) * k) (fun _ => k) ↔ k ≤ 4)) ∧
      ¬ deEfficient (fun _ => fun k : ℝ => 2 * √k + (1 - 1 / 2) * k) (fun _ => (9 : ℝ)) := by
  obtain ⟨hconc, hd, hG⟩ := figure_A1_instance
  have hF := figure_A1 (by norm_num : (0 : ℝ) < 4) hconc hd hG
  have e : √(9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun k hk hc => (hF.2.2.2.2 k hk hc).1, ?_⟩
  rw [(hF.2.2.2.2 9 (by norm_num) (by rw [e]; norm_num)).2]
  norm_num

end AKMM.Welfare
