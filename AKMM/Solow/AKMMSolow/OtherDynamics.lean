/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSolow.BasicModel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Other kinds of dynamics: endogenous growth, poverty traps, local stability

AKMM, §3.1.1, "Other kinds of dynamics", pp. 75–78 (the boxes on endogenous growth, poverty
traps, and non-monotonic dynamics and chaos), for the basic map `k ↦ (1 − δ)k + s f(k)`.

* **Endogenous growth** (p. 75): if `F₁(k, 1) > δ/s` everywhere there is no positive steady state
  and capital rises forever (`solow_endogenous_no_steady_state`); if `F₁(k, 1) ≥ c > δ/s`
  uniformly, capital grows at least geometrically and diverges (`solow_endogenous_growth`). In the
  `AK` case two countries keep a constant percentage gap (`solow_ak_constant_gap`); with
  `Y = AK + BL` (footnote 2) labour stops mattering asymptotically (`solow_ak_plus_labour`).
* **Poverty traps** (pp. 76–77): with an increasing map, of two adjacent steady states at least
  one is not locally attracting (`solow_poverty_trap_unstable`).
* **Non-monotonic dynamics** (p. 77): a decreasing map makes the path jump across the steady
  state (`solow_decreasing_map_overshoots`); footnote a, local stability when the slope at the
  steady state is below one in absolute value (`solow_local_stability`, with the geometric bound).
  This is the scalar fixed-point result of Miao's `DifferenceEquations`, proved here directly.

The chaos claim is narrative and is not formalised.
-/

namespace AKMM.Solow

open Filter Topology

/-- AKMM, p. 75 (endogenous growth): if the marginal product exceeds `δ/s` at every `k > 0`, then
`s f(k) > δ k` for every `k > 0`: there is no steady state with `k̄ > 0`, and every path of (3.5)
from `k₀ > 0` is strictly increasing ("`k_t` keeps growing larger over time"). -/
theorem solow_endogenous_no_steady_state {f : ℝ → ℝ} {s δ : ℝ} (hs : 0 < s)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hmp : ∀ k, 0 < k → δ / s < deriv f k) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (∀ x, 0 < x → δ * x < s * f x) ∧ (∀ x, 0 < x → δ * x ≠ s * f x) ∧ StrictMono k := by
  have hg : StrictMonoOn (fun x => s * f x - δ * x) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (f := fun x => s * f x - δ * x) (convex_Ici 0)
      ((hc.const_mul s).sub (continuousOn_id.const_mul δ))
    intro x hx
    rw [interior_Ici] at hx
    have hx' : (0 : ℝ) < x := hx
    have hD : HasDerivAt (fun x => s * f x - δ * x) (s * deriv f x - δ) x := by
      have := ((hd x hx').hasDerivAt.const_mul s).sub ((hasDerivAt_id' x).const_mul δ)
      rwa [mul_one] at this
    rw [hD.deriv]
    have := (div_lt_iff₀ hs).mp (hmp x hx')
    linarith
  have hpos : ∀ x, 0 < x → δ * x < s * f x := by
    intro x hx
    have := hg (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx.le) hx
    simp only [h0, mul_zero, sub_zero] at this
    linarith
  have hkpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ u ih => rw [hk u]; have := hpos _ ih; linarith
  refine ⟨hpos, fun x hx => ne_of_lt (hpos x hx), strictMono_nat_of_lt_succ fun t => ?_⟩
  rw [hk t]
  have := hpos _ (hkpos t)
  linarith

/-- AKMM, p. 75 (endogenous growth, "`F₁(k, 1)` uniformly above `δ/s`"): if `f'(k) ≥ c` for all
`k > 0` with `c > δ/s`, then `f(k) ≥ c k`, every path of (3.5) satisfies
`k_t ≥ (1 − δ + s c)^t k₀` with `1 − δ + s c > 1`, and `k_t → ∞`: unbounded growth "by itself". -/
theorem solow_endogenous_growth {f : ℝ → ℝ} {s δ c : ℝ} (hs : 0 < s)
    (hc : ContinuousOn f (Set.Ici 0)) (h0 : f 0 = 0) (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hcs : δ / s < c) (hmp : ∀ k, 0 < k → c ≤ deriv f k) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (∀ x, 0 ≤ x → c * x ≤ f x) ∧ 1 < 1 - δ + s * c ∧
      (∀ t, (1 - δ + s * c) ^ t * k 0 ≤ k t) ∧ Tendsto k atTop atTop := by
  have hg : MonotoneOn (fun x => f x - c * x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (f := fun x => f x - c * x) (convex_Ici 0)
      (hc.sub (continuousOn_id.const_mul c))
    · intro x hx
      rw [interior_Ici] at hx
      exact ((hd x hx).sub ((differentiableAt_id).const_mul c)).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : (0 : ℝ) < x := hx
      have hD : HasDerivAt (fun x => f x - c * x) (deriv f x - c) x := by
        have := (hd x hx').hasDerivAt.sub ((hasDerivAt_id' x).const_mul c)
        rwa [mul_one] at this
      rw [hD.deriv]
      linarith [hmp x hx']
  have hlin : ∀ x, 0 ≤ x → c * x ≤ f x := by
    intro x hx
    have := hg (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx) hx
    simp only [h0, mul_zero, sub_zero] at this
    linarith
  have hfac : 1 < 1 - δ + s * c := by
    have := (div_lt_iff₀ hs).mp hcs
    linarith
  have hbound : ∀ t, (1 - δ + s * c) ^ t * k 0 ≤ k t := by
    intro t
    induction t with
    | zero => simp
    | succ u ih =>
      have hku : 0 ≤ k u := le_trans (mul_nonneg (pow_nonneg (by linarith) _) hk0.le) ih
      rw [hk u, pow_succ]
      have := mul_le_mul_of_nonneg_left (hlin _ hku) hs.le
      have h2 : (1 - δ + s * c) * ((1 - δ + s * c) ^ u * k 0) ≤ (1 - δ + s * c) * k u :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      nlinarith
  refine ⟨hlin, hfac, hbound, ?_⟩
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hfac).atTop_mul_const hk0
  exact tendsto_atTop_mono hbound hpow

/-- AKMM, p. 76 (endogenous growth with `y = A k`): two identical countries starting from
different capital stocks stay forever different, with a constant percentage gap: `k_t/k'_t` is
constant. -/
theorem solow_ak_constant_gap {s δ A : ℝ} {k k' : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * (A * k t))
    (hk' : ∀ t, k' (t + 1) = (1 - δ) * k' t + s * (A * k' t))
    (hfac : 0 < 1 - δ + s * A) (h0 : 0 < k' 0) (t : ℕ) :
    k t / k' t = k 0 / k' 0 := by
  have e : ∀ (x : ℕ → ℝ), (∀ t, x (t + 1) = (1 - δ) * x t + s * (A * x t)) →
      ∀ t, x t = (1 - δ + s * A) ^ t * x 0 := by
    intro x hx t
    induction t with
    | zero => simp
    | succ u ih => rw [hx u, ih, pow_succ]; ring
  rw [e k hk t, e k' hk' t]
  have : 0 < (1 - δ + s * A) ^ t := pow_pos hfac t
  field_simp

/-- AKMM, footnote 2, p. 75: with `Y = AK + BL` (constant returns) and `A > δ/s`, capital per
worker diverges and the labour term stops mattering: the capital term's share `Ak_t/f(k_t)` of
output tends to one. -/
theorem solow_ak_plus_labour {s δ A B : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hA : δ / s < A) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * (A * k t + B)) :
    Tendsto k atTop atTop ∧ Tendsto (fun t => A * k t / (A * k t + B)) atTop (𝓝 1) := by
  have hApos : 0 < A := lt_of_le_of_lt (div_nonneg hδ hs.le) hA
  -- the affine technology has `f' = A`; we work with `f(k) = A k + B` on `k ≥ 0`
  have hfac : 1 < 1 - δ + s * A := by have := (div_lt_iff₀ hs).mp hA; linarith
  have hbound : ∀ t, (1 - δ + s * A) ^ t * k 0 ≤ k t := by
    intro t
    induction t with
    | zero => simp
    | succ u ih =>
      rw [hk u, pow_succ]
      have h2 : (1 - δ + s * A) * ((1 - δ + s * A) ^ u * k 0) ≤ (1 - δ + s * A) * k u :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have := mul_nonneg hs.le hB
      nlinarith
  have hdiv : Tendsto k atTop atTop :=
    tendsto_atTop_mono hbound ((tendsto_pow_atTop_atTop_of_one_lt hfac).atTop_mul_const hk0)
  refine ⟨hdiv, ?_⟩
  have hinv : Tendsto (fun t => B / (A * k t)) atTop (𝓝 0) :=
    (hdiv.const_mul_atTop hApos).const_div_atTop B
  have hlim := (hinv.const_add 1).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  rw [add_zero, inv_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdiv.eventually_gt_atTop 0] with t ht
  have : 0 < A * k t := mul_pos hApos ht
  field_simp

/-- AKMM, pp. 76–77 (poverty traps): a steady state `k̄` of a map `g` is locally attracting if
every path started close enough to it converges to it. -/
def SolowLocallyAttracting (g : ℝ → ℝ) (kbar : ℝ) : Prop :=
  ∃ ε > 0, ∀ x₀, |x₀ - kbar| < ε → Tendsto (fun t => g^[t] x₀) atTop (𝓝 kbar)

/-- AKMM, p. 77 (poverty traps): "at least one of the steady states will then not be stable".
For a continuous increasing map with adjacent steady states `k̄₁ < k̄₂` (no steady state
between them), `k̄₁` and `k̄₂` are not both locally attracting: between them the map lies on one
side of the diagonal, and paths started there move away from one of the two. -/
theorem solow_poverty_trap_unstable {g : ℝ → ℝ} {k₁ k₂ : ℝ} (hlt : k₁ < k₂)
    (hc : ContinuousOn g (Set.Icc k₁ k₂)) (hmono : MonotoneOn g (Set.Icc k₁ k₂))
    (h₁ : g k₁ = k₁) (h₂ : g k₂ = k₂) (hnone : ∀ x, k₁ < x → x < k₂ → g x ≠ x) :
    ¬ (SolowLocallyAttracting g k₁ ∧ SolowLocallyAttracting g k₂) := by
  rintro ⟨⟨ε₁, hε₁, hat₁⟩, ⟨ε₂, hε₂, hat₂⟩⟩
  -- the sign of `g x - x` is constant on `(k₁, k₂)`
  have hsign : (∀ x, k₁ < x → x < k₂ → x < g x) ∨ (∀ x, k₁ < x → x < k₂ → g x < x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, ha1, ha2, hga⟩, ⟨b, hb1, hb2, hgb⟩⟩ := hcon
    have hga' : g a < a := lt_of_le_of_ne hga (hnone a ha1 ha2)
    have hgb' : b < g b := lt_of_le_of_ne hgb (fun h => hnone b hb1 hb2 h.symm)
    have hcc : ContinuousOn (fun x => g x - x) (Set.Ioo k₁ k₂) :=
      (hc.mono Set.Ioo_subset_Icc_self).sub continuousOn_id
    have hiv := isPreconnected_Ioo.intermediate_value (Set.mem_Ioo.mpr ⟨ha1, ha2⟩)
      (Set.mem_Ioo.mpr ⟨hb1, hb2⟩) hcc
    obtain ⟨x, hx, hx0⟩ := hiv (Set.mem_Icc.mpr ⟨(by linarith : g a - a ≤ 0),
      (by linarith : (0 : ℝ) ≤ g b - b)⟩)
    have hx0' : g x - x = 0 := hx0
    exact hnone x hx.1 hx.2 (by linarith)
  rcases hsign with hup | hdown
  · -- paths just above `k₁` rise: `k₁` is not attracting
    set x₀ := k₁ + min ε₁ (k₂ - k₁) / 2 with hx₀
    have hm : 0 < min ε₁ (k₂ - k₁) := lt_min hε₁ (by linarith)
    have hx1 : k₁ < x₀ := by linarith
    have hx2 : x₀ ≤ k₂ := by have := min_le_right ε₁ (k₂ - k₁); linarith
    have hstay : ∀ t, x₀ ≤ g^[t] x₀ ∧ g^[t] x₀ ≤ k₂ := by
      intro t
      induction t with
      | zero => exact ⟨le_rfl, hx2⟩
      | succ u ih =>
        rw [Function.iterate_succ_apply']
        have hmem : g^[u] x₀ ∈ Set.Icc k₁ k₂ := ⟨by linarith [ih.1], ih.2⟩
        refine ⟨?_, ?_⟩
        · rcases ih.2.lt_or_eq with hl | he
          · exact ih.1.trans (hup _ (by linarith [ih.1]) hl).le
          · rw [he, h₂]; exact hx2
        · rw [← h₂]; exact hmono hmem (Set.right_mem_Icc.mpr hlt.le) ih.2
    have hlim := hat₁ x₀ (by
      rw [abs_of_pos (by linarith)]
      have := min_le_left ε₁ (k₂ - k₁)
      linarith)
    have := ge_of_tendsto hlim (Eventually.of_forall fun t => (hstay t).1)
    linarith
  · -- paths just below `k₂` fall: `k₂` is not attracting
    set x₀ := k₂ - min ε₂ (k₂ - k₁) / 2 with hx₀
    have hm : 0 < min ε₂ (k₂ - k₁) := lt_min hε₂ (by linarith)
    have hx2 : x₀ < k₂ := by linarith
    have hx1 : k₁ ≤ x₀ := by have := min_le_right ε₂ (k₂ - k₁); linarith
    have hstay : ∀ t, k₁ ≤ g^[t] x₀ ∧ g^[t] x₀ ≤ x₀ := by
      intro t
      induction t with
      | zero => exact ⟨hx1, le_rfl⟩
      | succ u ih =>
        rw [Function.iterate_succ_apply']
        have hmem : g^[u] x₀ ∈ Set.Icc k₁ k₂ := ⟨ih.1, by linarith [ih.2]⟩
        refine ⟨?_, ?_⟩
        · rw [← h₁]; exact hmono (Set.left_mem_Icc.mpr hlt.le) hmem ih.1
        · rcases ih.1.lt_or_eq with hl | he
          · exact (hdown _ hl (by linarith [ih.2])).le.trans ih.2
          · rw [← he, h₁]; exact hx1
    have hlim := hat₂ x₀ (by
      rw [abs_of_neg (by linarith)]
      have := min_le_left ε₂ (k₂ - k₁)
      linarith)
    have := le_of_tendsto hlim (Eventually.of_forall fun t => (hstay t).2)
    linarith

/-- AKMM, p. 77 (non-monotonic dynamics): when the right side of (3.5) is decreasing, the path
jumps across the steady state, so convergence, if any, is not monotonic. -/
theorem solow_decreasing_map_overshoots {g : ℝ → ℝ} {kbar x : ℝ} (hanti : StrictAnti g)
    (hfix : g kbar = kbar) : (x < kbar → kbar < g x) ∧ (kbar < x → g x < kbar) :=
  ⟨fun h => hfix ▸ hanti h, fun h => hfix ▸ hanti h⟩

/-- AKMM, footnote a, p. 78: "locally stable dynamics will occur if the slope at the steady state
is less than 1 in absolute value". If `g(k̄) = k̄` and `|g'(k̄)| < 1`, there are `ε > 0` and
`ρ < 1` with `|g^t(x₀) − k̄| ≤ ρ^t |x₀ − k̄|` whenever `|x₀ − k̄| < ε`; in particular every such
path converges to `k̄`. -/
theorem solow_local_stability {g : ℝ → ℝ} {kbar g' : ℝ} (hg : HasDerivAt g g' kbar)
    (hfix : g kbar = kbar) (hslope : |g'| < 1) :
    ∃ ε > 0, ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x₀, |x₀ - kbar| < ε →
      (∀ t, |g^[t] x₀ - kbar| ≤ ρ ^ t * |x₀ - kbar|) ∧
        Tendsto (fun t => g^[t] x₀) atTop (𝓝 kbar) := by
  set c := (1 - |g'|) / 2 with hcdef
  have hc : 0 < c := by linarith
  have hlo := (hasDerivAt_iff_isLittleO.mp hg).def hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set ρ := |g'| + c with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  have hstep : ∀ x, |x - kbar| < ε → |g x - kbar| ≤ ρ * |x - kbar| := by
    intro x hx
    have h := hball (by rw [Real.dist_eq]; exact hx)
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have htri : |g x - kbar| ≤ |g x - kbar - (x - kbar) * g'| + |(x - kbar) * g'| := by
      have := abs_add_le (g x - kbar - (x - kbar) * g') ((x - kbar) * g')
      rwa [sub_add_cancel] at this
    rw [abs_mul] at htri
    nlinarith [abs_nonneg (x - kbar)]
  refine ⟨ε, hε, ρ, hρ0, hρ1, fun x₀ hx₀ => ?_⟩
  have hbound : ∀ t, |g^[t] x₀ - kbar| ≤ ρ ^ t * |x₀ - kbar| := by
    intro t
    induction t with
    | zero => simp
    | succ u ih =>
      rw [Function.iterate_succ_apply']
      have hin : |g^[u] x₀ - kbar| < ε := by
        calc |g^[u] x₀ - kbar| ≤ ρ ^ u * |x₀ - kbar| := ih
          _ ≤ 1 * |x₀ - kbar| := mul_le_mul_of_nonneg_right
              (pow_le_one₀ hρ0 hρ1.le) (abs_nonneg _)
          _ < ε := by rw [one_mul]; exact hx₀
      calc |g (g^[u] x₀) - kbar| ≤ ρ * |g^[u] x₀ - kbar| := hstep _ hin
        _ ≤ ρ * (ρ ^ u * |x₀ - kbar|) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (u + 1) * |x₀ - kbar| := by ring
  refine ⟨hbound, ?_⟩
  have hpow : Tendsto (fun t => ρ ^ t * |x₀ - kbar|) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const |x₀ - kbar|
    rwa [zero_mul] at this
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun t => dist_nonneg) (fun t => by rw [Real.dist_eq]; exact hbound t) hpow

end AKMM.Solow
