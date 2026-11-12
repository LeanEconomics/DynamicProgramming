/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.PhaseDiagram
import AKMMDynamicOptimization.NGMDynamics
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The phase diagram: loci, saddle path, and the paths off it

AKMM, App. 4.A.4, pp. 831–835, Figures .1–.3. The difference system (4.A.8)–(4.A.9),
`k_{t+1} = f(k_t) + (1 − δ)k_t − c_t`, `u'(c_t) = βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)`, is
`saddleSystem`. A *path* is a solution with `k_t > 0` and `c_t > 0` for all `t`; it *converges*
if `k_t → k̄` and `c_t → c̄`.

* Figure .1: `c = f(k) − δk` is strictly increasing on `[0, k^G]`, strictly decreasing on
  `[k^G, ∞)`, positive on `(0, k^u)` and negative beyond `k^u`, with `k^G < k^u`
  (`saddle_kloc_shape`).
* Figure .2: the `c_{t+1} = c_t` locus `c = f(k) − δk + (k − k̄)` is strictly increasing, passes
  through `(k̄, c̄)` with `c̄ > 0`, has slope `1/β` there (the `k_{t+1} = k_t` locus has slope
  `1/β − 1 > 0`), cuts `c = 0` at exactly one `k̲ ∈ (0, k̄)`, and lies below the
  `k_{t+1} = k_t` locus exactly when `k < k̄` (`saddle_cloc_shape`). It is not vertical, as the
  figure draws it.
* Figure .3: the arrows (`saddle_arrows`).
* Monotonicity in `c₀` (`saddle_order`): from the same `k₀`, a lower `c₀` gives higher capital
  and lower consumption at every later date; then the capital gap grows near `k̄`, so two such
  paths cannot both exist when the lower-consumption one converges (`saddle_not_both`).
* **Saddle path, convergence iff on it** (`saddle_path_iff`): if a function `g` is such that
  from every `k₀ ∈ K` the path starting at `(k₀, g(k₀))` converges, then a path from
  `(k₀, c₀)`, `k₀ ∈ K`, converges iff `c₀ = g(k₀)`. Existence of `g`: the optimal policy, for
  `δ = 1` in SLP's §6.1 setting (`saddle_path_slp`), and in closed form for log utility and
  Cobb–Douglas production (`saddle_logCobbDouglas`); for every `δ ≤ 1` by shooting
  (`saddle_path_general`).
* **Above the saddle path** (`saddle_above_infeasible`): capital becomes nonpositive in finite
  time. Region `k_{t+1} ≤ k_t`, `k_{t+1} < k̄` is absorbing: there `k` falls and `c` rises
  (`saddle_regionA_absorbing`).
* **Below the saddle path** (`saddle_below`): eventually `k_t ≥ k̄ + η` and `c` falls, `c_t → 0`,
  eventually `k_t > k^G`, and the TVC expression tends to `+∞`. The book's "both `k_t` and `c_t`
  keep decreasing" is not what is true (or what the figure shows) for `k`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- The difference system (4.A.8)–(4.A.9) of AKMM, App. 4.A.4, p. 831, along `(k_t, c_t)`. -/
def saddleSystem (f f' u' : ℝ → ℝ) (β δ : ℝ) (k c : ℕ → ℝ) : Prop :=
  ∀ t, k (t + 1) = f (k t) + (1 - δ) * k t - c t ∧
    u' (c t) = β * u' (c (t + 1)) * (f' (k (t + 1)) + 1 - δ)

/-- AKMM, p. 832: total resources `f(k) + (1 − δ)k` are nondecreasing on `(0, ∞)` when `f` is
concave with `f' > 0` and `δ ≤ 1`. -/
theorem saddle_resources_mono {f f' : ℝ → ℝ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    f x + (1 - δ) * x ≤ f y + (1 - δ) * y := by
  have h1 := tangent_le hf (Set.mem_Ici.2 hy.le) (Set.mem_Ici.2 hx) (hfd y hy)
  nlinarith [mul_nonneg (hf'pos y hy).le (sub_nonneg.2 hxy),
    mul_nonneg (sub_nonneg.2 hδ1) (sub_nonneg.2 hxy)]

/-- AKMM, Figure .1, p. 832: three points `x < y < z` of `[0, ∞)` and a strictly concave `f`
give `(z − x)f(y) > (z − y)f(x) + (y − x)f(z)`. -/
theorem saddle_chord {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {x y z : ℝ}
    (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z) :
    (z - y) * f x + (y - x) * f z < (z - x) * f y := by
  have hzx : 0 < z - x := by linarith
  have h := hf.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ z)) (by linarith)
    (div_pos (by linarith : 0 < z - y) hzx) (div_pos (by linarith : 0 < y - x) hzx)
    (by rw [← add_div, div_eq_one_iff_eq hzx.ne']; ring)
  have e : ((z - y) / (z - x)) * x + ((y - x) / (z - x)) * z = y := by
    field_simp; ring
  simp only [smul_eq_mul] at h
  rw [e] at h
  have := mul_lt_mul_of_pos_left h hzx
  have e2 : (z - x) * ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) =
      (z - y) * f x + (y - x) * f z := by field_simp
  linarith

/-- **AKMM, Figure .1, p. 832: the shape of the `k_{t+1} = k_t` locus.** Let `f(0) = 0`, `f`
strictly concave on `[0, ∞)`, `f'(k^G) = δ` with `k^G > 0`, and `k^u > 0` with
`f(k^u) = δk^u` (it exists under the Inada conditions, `ngm_max_capital`). Then `c = f(k) − δk`
is strictly increasing on `[0, k^G]` and strictly decreasing on `[k^G, ∞)` (hump-shaped, peak at
the golden rule), `k^G < k^u`, and the locus is positive on `(0, k^u)` and negative beyond. -/
theorem saddle_kloc_shape {f : ℝ → ℝ} {δ kG ku : ℝ} (hf0 : f 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (hkG : 0 < kG) (hG : HasDerivAt f δ kG)
    (hku : 0 < ku) (hzero : f ku - δ * ku = 0) :
    StrictMonoOn (fun k => f k - δ * k) (Set.Icc 0 kG) ∧
      StrictAntiOn (fun k => f k - δ * k) (Set.Ici kG) ∧ kG < ku ∧
      (∀ k, 0 < k → k < ku → 0 < f k - δ * k) ∧ (∀ k, ku < k → f k - δ * k < 0) := by
  -- the peak: strictly above every other point
  have hpeak : ∀ x, 0 ≤ x → x ≠ kG → f x - δ * x < f kG - δ * kG := by
    intro x hx hne
    have := tangent_lt hf (Set.mem_Ici.2 hkG.le) (Set.mem_Ici.2 hx) (Ne.symm hne) hG
    linarith
  have hmono : StrictMonoOn (fun k => f k - δ * k) (Set.Icc 0 kG) := by
    intro x hx y hy hxy
    simp only
    rcases eq_or_lt_of_le hy.2 with he | hlt
    · rw [he]; exact hpeak x hx.1 (by linarith)
    · have h := saddle_chord hf hx.1 hxy hlt
      have hp := hpeak x hx.1 (by linarith)
      nlinarith
  refine ⟨hmono, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only
    have hx' : kG ≤ x := hx
    rcases eq_or_lt_of_le hx' with he | hlt
    · rw [← he]; exact hpeak y (by linarith) (by linarith)
    · have h := saddle_chord hf hkG.le hlt hxy
      have hp := hpeak y (by linarith) (by linarith)
      nlinarith
  · by_contra hle
    push Not at hle
    have h0 : (fun k => f k - δ * k) 0 < (fun k => f k - δ * k) ku :=
      hmono ⟨le_rfl, hkG.le⟩ ⟨hku.le, hle⟩ hku
    simp only [hf0] at h0
    linarith
  · intro k hk hkk
    have h := saddle_chord hf le_rfl hk hkk
    rw [hf0] at h
    nlinarith
  · intro k hk
    have h := saddle_chord hf le_rfl hku hk
    rw [hf0] at h
    nlinarith

/-- **AKMM, Figure .2 and (4.A.13), pp. 832–833: the shape of the `c_{t+1} = c_t` locus**
`c = f(k) − δk + (k − k̄)`. With `f(0) = 0`, `f` continuous and concave on `[0, ∞)`, `f' > 0`,
`δ ≤ 1`, `0 < β < 1` and (4.A.11): the locus is strictly increasing; at `k̄` its slope is `1/β`
and that of `c = f(k) − δk` is `1/β − 1 > 0`; `c̄ = f(k̄) − δk̄ > 0`; it cuts `c = 0` at exactly
one `k̲ ∈ (0, k̄)`; and it lies below `c = f(k) − δk` exactly when `k < k̄`. -/
theorem saddle_cloc_shape {f f' : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf0 : f 0 = 0) (hfc : ContinuousOn f (Set.Ici 0))
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ)) :
    StrictMonoOn (fun k => f k - δ * k + (k - kbar)) (Set.Ici 0) ∧
      HasDerivAt (fun k => f k - δ * k + (k - kbar)) (1 / β) kbar ∧
      HasDerivAt (fun k => f k - δ * k) (1 / β - 1) kbar ∧ 0 < 1 / β - 1 ∧
      0 < f kbar - δ * kbar ∧
      (∃! kl, 0 < kl ∧ kl < kbar ∧ f kl - δ * kl + (kl - kbar) = 0) ∧
      ∀ k, (f k - δ * k + (k - kbar) < f k - δ * k ↔ k < kbar) := by
  have hR : f' kbar + 1 - δ = 1 / β := by field_simp; linarith
  have h1β : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
  have hmono : StrictMonoOn (fun k => f k - δ * k + (k - kbar)) (Set.Ici 0) := by
    intro x hx y hy hxy
    have hy0 : 0 < y := lt_of_le_of_lt hx hxy
    have h1 := tangent_le hf (Set.mem_Ici.2 hy0.le) hx (hfd y hy0)
    simp only
    nlinarith [mul_pos (hf'pos y hy0) (sub_pos.2 hxy),
      mul_nonneg (sub_nonneg.2 hδ1) (sub_pos.2 hxy).le]
  have hd1 : HasDerivAt (fun k => f k - δ * k) (1 / β - 1) kbar := by
    have := (hfd kbar hkbar).sub ((hasDerivAt_id kbar).const_mul δ)
    refine this.congr_deriv ?_
    simp only [mul_one]; linarith
  have hd2 : HasDerivAt (fun k => f k - δ * k + (k - kbar)) (1 / β) kbar := by
    have := hd1.add ((hasDerivAt_id kbar).sub_const kbar)
    refine this.congr_deriv ?_
    ring
  have hcbar : 0 < f kbar - δ * kbar := by
    have h1 := tangent_le hf (Set.mem_Ici.2 hkbar.le) (Set.mem_Ici.2 le_rfl) (hfd kbar hkbar)
    rw [hf0] at h1
    have : δ < f' kbar := by linarith
    nlinarith
  refine ⟨hmono, hd2, hd1, by linarith, hcbar, ?_, fun k => ⟨fun h => by linarith,
    fun h => by linarith⟩⟩
  have hcont : ContinuousOn (fun k => f k - δ * k + (k - kbar)) (Set.Icc 0 kbar) :=
    ((hfc.mono Set.Icc_subset_Ici_self).sub (continuousOn_const.mul continuousOn_id)).add
      (continuousOn_id.sub continuousOn_const)
  obtain ⟨kl, hkl, hval⟩ := intermediate_value_Icc hkbar.le hcont
    (⟨by simp only [hf0]; linarith, by simp only; linarith⟩ :
      (0 : ℝ) ∈ Set.Icc ((fun k => f k - δ * k + (k - kbar)) 0)
        ((fun k => f k - δ * k + (k - kbar)) kbar))
  simp only at hval
  have hkl0 : kl ≠ 0 := by rintro rfl; rw [hf0] at hval; linarith
  have hklb : kl ≠ kbar := by rintro rfl; linarith
  refine ⟨kl, ⟨lt_of_le_of_ne hkl.1 (Ne.symm hkl0), lt_of_le_of_ne hkl.2 hklb, hval⟩, ?_⟩
  rintro y ⟨hy0, -, hy⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono (Set.mem_Ici.2 hy0.le) (Set.mem_Ici.2 hkl.1) h
    simp only at this; linarith
  · have := hmono (Set.mem_Ici.2 hkl.1) (Set.mem_Ici.2 hy0.le) h
    simp only at this; linarith

/-- **AKMM, Figure .3, pp. 832–833: the arrows of the phase diagram.** Along one step of
(4.A.8)–(4.A.9) with `k_{t+1}, c_t, c_{t+1} > 0` (and the hypotheses of (4.A.13)): `k` rises iff
`c_t` is below `f(k_t) − δk_t` and falls iff above; `c` rises iff `c_t` is above
`f(k_t) − δk_t + (k_t − k̄)` and falls iff below, i.e. iff `k_{t+1} > k̄`. -/
theorem saddle_arrows {f f' u' : ℝ → ℝ} {β δ kbar k k' c c' : ℝ} (hβ : 0 < β)
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ))
    (hk' : 0 < k') (hc : 0 < c) (hc' : 0 < c') (h48 : k' = f k + (1 - δ) * k - c)
    (h49 : u' c = β * u' c' * (f' k' + 1 - δ)) :
    (k < k' ↔ c < f k - δ * k) ∧ (k' < k ↔ f k - δ * k < c) ∧
      (c < c' ↔ f k - δ * k + (k - kbar) < c) ∧ (c' < c ↔ c < f k - δ * k + (k - kbar)) ∧
      (c' < c ↔ kbar < k') := by
  have h48' : k' - k = f k - δ * k - c := by rw [h48]; ring
  obtain ⟨a1, a2, -⟩ := eq_4A_12 (f := f) h48'
  obtain ⟨b1, b2⟩ := eq_4A_13 hβ hu'pos hu' hf' hkbar h411 hk' hc hc' h48' h49
  have hpos := hu'pos c' hc'
  have hfall : c' < c ↔ kbar < k' := by
    constructor
    · intro h
      have hu := hu' (Set.mem_Ioi.2 hc') (Set.mem_Ioi.2 hc) h
      by_contra hle
      push Not at hle
      have hf1 : f' kbar ≤ f' k' := hf'.antitoneOn (Set.mem_Ioi.2 hk') (Set.mem_Ioi.2 hkbar) hle
      have : β * u' c' * (f' kbar + 1 - δ) ≤ β * u' c' * (f' k' + 1 - δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_pos hβ hpos).le
      have e : β * u' c' * (f' kbar + 1 - δ) = u' c' := by
        have : β * u' c' * (f' kbar + 1 - δ) = u' c' * (β * (f' kbar + 1 - δ)) := by ring
        rw [this, ← h411, mul_one]
      linarith
    · intro h
      have hf1 : f' k' < f' kbar := hf' (Set.mem_Ioi.2 hkbar) (Set.mem_Ioi.2 hk') h
      have : β * u' c' * (f' k' + 1 - δ) < β * u' c' * (f' kbar + 1 - δ) :=
        mul_lt_mul_of_pos_left (by linarith) (mul_pos hβ hpos)
      have e : β * u' c' * (f' kbar + 1 - δ) = u' c' := by
        have : β * u' c' * (f' kbar + 1 - δ) = u' c' * (β * (f' kbar + 1 - δ)) := by ring
        rw [this, ← h411, mul_one]
      by_contra hle
      push Not at hle
      have := hu'.antitoneOn (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hc') hle
      linarith
  refine ⟨a1, a2, b1.trans b2, hfall.trans ⟨fun h => by linarith, fun h => by linarith⟩, hfall⟩

/-- **AKMM, p. 834: paths are ordered by `c₀`.** Two paths of (4.A.8)–(4.A.9) (positive `k`, `c`)
from the same `k₀` with `c₀ < c₀'`: at every date `k'_t ≤ k_t` and `c_t < c'_t`, with
`k'_{t+1} < k_{t+1}`, and `u'(c_t)/u'(c'_t)` is nondecreasing. Assumes `f` concave on `[0, ∞)`
with derivative `f' > 0`, `δ ≤ 1`, and `u' > 0` strictly decreasing. -/
theorem saddle_order {f f' u' : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hu' : StrictAntiOn u' (Set.Ioi 0)) {k c k' c' : ℕ → ℝ}
    (hs : saddleSystem f f' u' β δ k c) (hs' : saddleSystem f f' u' β δ k' c')
    (hk : ∀ t, 0 < k t) (hc : ∀ t, 0 < c t) (hk' : ∀ t, 0 < k' t) (hc' : ∀ t, 0 < c' t)
    (h0 : k 0 = k' 0) (hc0 : c 0 < c' 0) :
    ∀ t, k' t ≤ k t ∧ c t < c' t ∧ k' (t + 1) < k (t + 1) ∧
      u' (c t) * u' (c' (t + 1)) ≤ u' (c (t + 1)) * u' (c' t) := by
  -- capital at `t + 1` and the returns there
  have hkstep : ∀ t, k' t ≤ k t → c t < c' t → k' (t + 1) < k (t + 1) := by
    intro t hkt hct
    have := saddle_resources_mono hδ1 hf hfd hf'pos (hk' t).le hkt (hk t)
    rw [(hs t).1, (hs' t).1]
    linarith
  have hRle : ∀ t, k' (t + 1) < k (t + 1) →
      f' (k (t + 1)) + 1 - δ ≤ f' (k' (t + 1)) + 1 - δ := by
    intro t h
    have := deriv_le_of_concave hf (Set.mem_Ici.2 (hk' _).le) (Set.mem_Ici.2 (hk _).le) h.le
      (hfd _ (hk' _)) (hfd _ (hk _))
    linarith
  have hRpos : ∀ x, 0 < x → 0 < f' x + 1 - δ := fun x hx => by linarith [hf'pos x hx]
  have key : ∀ t, k' t ≤ k t ∧ c t < c' t := by
    intro t
    induction t with
    | zero => exact ⟨h0.symm.le, hc0⟩
    | succ t ih =>
      have hk1 := hkstep t ih.1 ih.2
      refine ⟨hk1.le, ?_⟩
      by_contra hle
      push Not at hle
      have hu1 : u' (c (t + 1)) ≤ u' (c' (t + 1)) :=
        hu'.antitoneOn (Set.mem_Ioi.2 (hc' _)) (Set.mem_Ioi.2 (hc _)) hle
      have hu0 : u' (c' t) < u' (c t) := hu' (Set.mem_Ioi.2 (hc t)) (Set.mem_Ioi.2 (hc' t)) ih.2
      have e1 : β * u' (c (t + 1)) * (f' (k (t + 1)) + 1 - δ) ≤
          β * u' (c' (t + 1)) * (f' (k (t + 1)) + 1 - δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu1 hβ.le) (hRpos _ (hk _)).le
      have e2 : β * u' (c' (t + 1)) * (f' (k (t + 1)) + 1 - δ) ≤
          β * u' (c' (t + 1)) * (f' (k' (t + 1)) + 1 - δ) :=
        mul_le_mul_of_nonneg_left (hRle t hk1) (mul_pos hβ (hu'pos _ (hc' _))).le
      linarith [(hs t).2, (hs' t).2]
  intro t
  have hk1 := hkstep t (key t).1 (key t).2
  refine ⟨(key t).1, (key t).2, hk1, ?_⟩
  have E1 : u' (c t) * u' (c' (t + 1)) =
      β * u' (c (t + 1)) * u' (c' (t + 1)) * (f' (k (t + 1)) + 1 - δ) := by
    rw [(hs t).2]; ring
  have E2 : u' (c (t + 1)) * u' (c' t) =
      β * u' (c (t + 1)) * u' (c' (t + 1)) * (f' (k' (t + 1)) + 1 - δ) := by
    rw [(hs' t).2]; ring
  rw [E1, E2]
  exact mul_le_mul_of_nonneg_left (hRle t hk1)
    (mul_pos (mul_pos hβ (hu'pos _ (hc _))) (hu'pos _ (hc' _))).le

/-- **AKMM, p. 834: the capital gap grows near the steady state.** Under the hypotheses of
`saddle_order`, `0 < β < 1`, (4.A.11) and `f'` continuous at `k̄`: two paths from the same `k₀`
with `c₀ < c₀'` cannot both exist if the lower-consumption one has `k_t → k̄`. Near `k̄` the
gap `k_t − k'_t` grows at least by the factor `f'(k_t) + 1 − δ → 1/β > 1` each period, while it
stays below `k_t`. -/
theorem saddle_not_both {f f' u' : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hu' : StrictAntiOn u' (Set.Ioi 0)) (h411 : 1 = β * (f' kbar + 1 - δ))
    (hf'c : ContinuousAt f' kbar) {k c k' c' : ℕ → ℝ}
    (hs : saddleSystem f f' u' β δ k c) (hs' : saddleSystem f f' u' β δ k' c')
    (hk : ∀ t, 0 < k t) (hc : ∀ t, 0 < c t) (hk' : ∀ t, 0 < k' t) (hc' : ∀ t, 0 < c' t)
    (h0 : k 0 = k' 0) (hc0 : c 0 < c' 0) (hconv : Tendsto k atTop (𝓝 kbar)) : False := by
  have hord := saddle_order hβ hδ1 hf hfd hf'pos hu'pos hu' hs hs' hk hc hk' hc' h0 hc0
  have hRbar : f' kbar + 1 - δ = 1 / β := by field_simp; linarith
  have h1β : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
  set σ := (1 + 1 / β) / 2 with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ : σ < 1 / β := by rw [hσdef]; linarith
  have hlim : Tendsto (fun t => f' (k t) + 1 - δ) atTop (𝓝 (1 / β)) := by
    have := ((hf'c.tendsto.comp hconv).add_const 1).sub_const δ
    rw [hRbar] at this
    exact this
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hlim.eventually (lt_mem_nhds hσ)).and
    (hconv.eventually (gt_mem_nhds (lt_add_one kbar))))
  have hDstep : ∀ t, T ≤ t → σ * (k t - k' t) ≤ k (t + 1) - k' (t + 1) := by
    intro t ht
    have h1 := tangent_le hf (Set.mem_Ici.2 (hk t).le) (Set.mem_Ici.2 (hk' t).le) (hfd _ (hk t))
    have hD := (hord t).1
    have hcc := (hord t).2.1
    have hσR := mul_le_mul_of_nonneg_right (hT t ht).1.le (sub_nonneg.2 hD)
    rw [(hs t).1, (hs' t).1]
    nlinarith
  have hDpos : 0 < k (T + 1) - k' (T + 1) := sub_pos.2 (hord T).2.2.1
  have hgrow : ∀ n, σ ^ n * (k (T + 1) - k' (T + 1)) ≤ k (T + 1 + n) - k' (T + 1 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hDstep (T + 1 + n) (by omega)
      rw [pow_succ]
      calc σ ^ n * σ * (k (T + 1) - k' (T + 1))
          = σ * (σ ^ n * (k (T + 1) - k' (T + 1))) := by ring
        _ ≤ σ * (k (T + 1 + n) - k' (T + 1 + n)) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ _ := this
  have hinf : Tendsto (fun n : ℕ => σ ^ n * (k (T + 1) - k' (T + 1))) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hσ1).atTop_mul_const hDpos
  obtain ⟨n, hn⟩ := (hinf.eventually_gt_atTop (kbar + 1)).exists
  have h1 := hgrow n
  have h2 := (hT (T + 1 + n) (by omega)).2
  have h3 := hk' (T + 1 + n)
  linarith

/-- **AKMM, p. 834: convergence iff on the saddle path.** Under the hypotheses of
`saddle_not_both`, let `g` be such that from every `k₀ ∈ K` some path starts at `(k₀, g(k₀))`
and converges to `(k̄, c̄)` (the saddle path; for the optimal policy see `saddle_path_slp` and
`saddle_logCobbDouglas`). Then a path of (4.A.8)–(4.A.9) with positive `k` and `c` and
`k₀ ∈ K` converges to `(k̄, c̄)` if and only if `c₀ = g(k₀)`. -/
theorem saddle_path_iff {f f' u' g : ℝ → ℝ} {β δ kbar cbar : ℝ} {K : Set ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hδ1 : δ ≤ 1) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0))
    (h411 : 1 = β * (f' kbar + 1 - δ)) (hf'c : ContinuousAt f' kbar)
    (hg : ∀ x ∈ K, ∃ ks cs : ℕ → ℝ, saddleSystem f f' u' β δ ks cs ∧ (∀ t, 0 < ks t) ∧
      (∀ t, 0 < cs t) ∧ ks 0 = x ∧ cs 0 = g x ∧ Tendsto ks atTop (𝓝 kbar) ∧
      Tendsto cs atTop (𝓝 cbar))
    {k c : ℕ → ℝ} (hs : saddleSystem f f' u' β δ k c) (hk : ∀ t, 0 < k t)
    (hc : ∀ t, 0 < c t) (hK : k 0 ∈ K) :
    (Tendsto k atTop (𝓝 kbar) ∧ Tendsto c atTop (𝓝 cbar)) ↔ c 0 = g (k 0) := by
  obtain ⟨ks, cs, hss, hks, hcs, hks0, hcs0, hksc, hcsc⟩ := hg (k 0) hK
  constructor
  · rintro ⟨hkc, -⟩
    rcases lt_trichotomy (c 0) (g (k 0)) with h | h | h
    · exact (saddle_not_both hβ hβ1 hδ1 hf hfd hf'pos hu'pos hu' h411 hf'c hs hss hk hc hks hcs
        hks0.symm (hcs0 ▸ h) hkc).elim
    · exact h
    · exact (saddle_not_both hβ hβ1 hδ1 hf hfd hf'pos hu'pos hu' h411 hf'c hss hs hks hcs hk hc
        hks0 (hcs0 ▸ h) hksc).elim
  · intro h
    have heq : ∀ t, k t = ks t ∧ c t = cs t := by
      intro t
      induction t with
      | zero => exact ⟨hks0.symm, h.trans hcs0.symm⟩
      | succ t ih =>
        have hk1 : k (t + 1) = ks (t + 1) := by rw [(hs t).1, (hss t).1, ih.1, ih.2]
        refine ⟨hk1, ?_⟩
        have hR : 0 < f' (k (t + 1)) + 1 - δ := by linarith [hf'pos _ (hk (t + 1))]
        have e : β * (f' (k (t + 1)) + 1 - δ) * u' (c (t + 1)) =
            β * (f' (k (t + 1)) + 1 - δ) * u' (cs (t + 1)) := by
          have h1 := (hs t).2
          have h2 := (hss t).2
          rw [ih.2, h2, ← hk1] at h1
          linarith
        have hu := mul_left_cancel₀ (mul_pos hβ hR).ne' e
        exact hu'.injOn (Set.mem_Ioi.2 (hc _)) (Set.mem_Ioi.2 (hcs _)) hu
    have hkf : k = ks := funext fun t => (heq t).1
    have hcf : c = cs := funext fun t => (heq t).2
    rw [hkf, hcf]
    exact ⟨hksc, hcsc⟩

/-- **AKMM, p. 834: above the saddle path capital becomes nonpositive in finite time.** Under the
hypotheses of `saddle_not_both`, if a path `(k*, c*)` from `k₀` converges to `k̄`, then any
solution of (4.A.8)–(4.A.9) from the same `k₀ > 0` with `c₀ > c*₀` and positive consumption
reaches `k_{T+1} ≤ 0` at some `T` with `k_s > 0` for `s ≤ T`. -/
theorem saddle_above_infeasible {f f' u' : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hu' : StrictAntiOn u' (Set.Ioi 0)) (h411 : 1 = β * (f' kbar + 1 - δ))
    (hf'c : ContinuousAt f' kbar) {k c ks cs : ℕ → ℝ}
    (hs : saddleSystem f f' u' β δ k c) (hss : saddleSystem f f' u' β δ ks cs)
    (hc : ∀ t, 0 < c t) (hks : ∀ t, 0 < ks t) (hcs : ∀ t, 0 < cs t)
    (hksc : Tendsto ks atTop (𝓝 kbar)) (h0 : k 0 = ks 0) (habove : cs 0 < c 0) :
    ∃ T, (∀ s, s ≤ T → 0 < k s) ∧ k (T + 1) ≤ 0 := by
  have hex : ∃ t, k t ≤ 0 := by
    by_contra hall
    push Not at hall
    exact saddle_not_both hβ hβ1 hδ1 hf hfd hf'pos hu'pos hu' h411 hf'c hss hs hks hcs hall hc
      h0.symm habove hksc
  classical
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, h0] at this
    linarith [hks 0]
  refine ⟨Nat.find hex - 1, fun s hs' => ?_, ?_⟩
  · have := Nat.find_min hex (show s < Nat.find hex by omega)
    push Not at this
    exact this
  · have := Nat.find_spec hex
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega]

/-- **AKMM, p. 834: the region above the saddle path, left of `c_{t+1} = c_t`, is absorbing.**
If at date `t` capital falls to `k_{t+1} ≤ k_t` with `0 < k_{t+1} < k̄` (and `c_t, c_{t+1} > 0`),
then `c_{t+1} > c_t` and `k_{t+2} < k_{t+1}`: `k` keeps falling and `c` keeps rising. -/
theorem saddle_regionA_absorbing {f f' u' : ℝ → ℝ} {β δ kbar : ℝ} (hβ : 0 < β) (hδ1 : δ ≤ 1)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf'pos : ∀ x, 0 < x → 0 < f' x) (hf' : StrictAntiOn f' (Set.Ioi 0))
    (hu'pos : ∀ x, 0 < x → 0 < u' x) (hu' : StrictAntiOn u' (Set.Ioi 0)) (hkbar : 0 < kbar)
    (h411 : 1 = β * (f' kbar + 1 - δ)) {k c : ℕ → ℝ} (hs : saddleSystem f f' u' β δ k c)
    {t : ℕ} (hk1 : 0 < k (t + 1)) (hc0 : 0 < c t) (hc1 : 0 < c (t + 1))
    (hfall : k (t + 1) ≤ k t) (hlow : k (t + 1) < kbar) :
    c t < c (t + 1) ∧ k (t + 2) < k (t + 1) ∧ k (t + 2) < kbar := by
  have h48' : k (t + 1) - k t = f (k t) - δ * k t - c t := by rw [(hs t).1]; ring
  have hrise : c t < c (t + 1) :=
    (eq_4A_13 hβ hu'pos hu' hf' hkbar h411 hk1 hc0 hc1 h48' (hs t).2).1.2 hlow
  have hm := saddle_resources_mono hδ1 hf hfd hf'pos hk1.le hfall (hk1.trans_le hfall)
  have e : k (t + 2) = f (k (t + 1)) + (1 - δ) * k (t + 1) - c (t + 1) := (hs (t + 1)).1
  have h1 : k (t + 1) = f (k t) + (1 - δ) * k t - c t := (hs t).1
  refine ⟨hrise, by linarith, by linarith⟩

/-- **AKMM, p. 834: below the saddle path.** Under the hypotheses of `saddle_not_both`, with
`f(0) = 0`, `f'` strictly decreasing, `u'` continuous at `c̄ > 0`, and the golden rule
`f'(k^G) = δ`, `k̄ < k^G`: let `(k*, c*)` be a path from `k₀` converging to `(k̄, c̄)` and
`(k, c)` a path from the same `k₀` with `c₀ < c*₀`. Then (i) from some date on `k_t ≥ k̄ + η`
(`η > 0`) and `c_t` strictly falls; (ii) `c_t → 0`; (iii) from some date on `k_t > k^G`; and (iv)
the TVC expression `β^{t+1}u'(c_{t+1})(f'(k_{t+1}) + 1 − δ)k_{t+1}` tends to `+∞`. -/
theorem saddle_below {f f' u' : ℝ → ℝ} {β δ kbar cbar kG : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hf0 : f 0 = 0) (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ x, 0 < x → HasDerivAt f (f' x) x) (hf'pos : ∀ x, 0 < x → 0 < f' x)
    (hf' : StrictAntiOn f' (Set.Ioi 0)) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    (hu' : StrictAntiOn u' (Set.Ioi 0)) (hkbar : 0 < kbar) (h411 : 1 = β * (f' kbar + 1 - δ))
    (hcbar : 0 < cbar) (hu'c : ContinuousAt u' cbar) (hG : f' kG = δ) (hkG : kbar < kG)
    {k c ks cs : ℕ → ℝ} (hs : saddleSystem f f' u' β δ k c)
    (hss : saddleSystem f f' u' β δ ks cs) (hk : ∀ t, 0 < k t) (hc : ∀ t, 0 < c t)
    (hks : ∀ t, 0 < ks t) (hcs : ∀ t, 0 < cs t) (hksc : Tendsto ks atTop (𝓝 kbar))
    (hcsc : Tendsto cs atTop (𝓝 cbar)) (h0 : k 0 = ks 0) (hbelow : c 0 < cs 0) :
    (∃ η > 0, ∃ T, ∀ t, T ≤ t → kbar + η ≤ k t ∧ c (t + 1) < c t) ∧
      Tendsto c atTop (𝓝 0) ∧ (∃ T, ∀ t, T ≤ t → kG < k t) ∧
      Tendsto (fun t => β ^ (t + 1) * u' (c (t + 1)) * (f' (k (t + 1)) + 1 - δ) * k (t + 1))
        atTop atTop := by
  have hord := saddle_order hβ hδ1 hf hfd hf'pos hu'pos hu' hs hss hk hc hks hcs h0 hbelow
  have hRpos : ∀ x, 0 < x → 0 < f' x + 1 - δ := fun x hx => by linarith [hf'pos x hx]
  -- (a) the marginal-utility ratio stays above `q > 1`
  set q := u' (c 0) / u' (cs 0) with hqdef
  have hucs0 := hu'pos _ (hcs 0)
  have hq1 : 1 < q := by
    rw [hqdef, one_lt_div hucs0]
    exact hu' (Set.mem_Ioi.2 (hc 0)) (Set.mem_Ioi.2 (hcs 0)) hbelow
  have hratio : ∀ t, q * u' (cs t) ≤ u' (c t) := by
    intro t
    induction t with
    | zero => rw [hqdef, div_mul_cancel₀ _ hucs0.ne']
    | succ t ih =>
      have h2 := (hord t).2.2.2
      have h3 := mul_le_mul_of_nonneg_right ih (hu'pos _ (hcs (t + 1))).le
      refine le_of_mul_le_mul_right ?_ (hu'pos _ (hcs t))
      nlinarith
  -- (b) consumption is eventually a fixed distance below `c̄`
  set q' := (1 + q) / 2 with hq'def
  have hucbar := hu'pos _ hcbar
  obtain ⟨e, he, hball⟩ := Metric.continuousAt_iff.1 hu'c ((q' - 1) * u' cbar)
    (mul_pos (by rw [hq'def]; linarith) hucbar)
  set e' := min (e / 2) (cbar / 2) with he'def
  have he'0 : 0 < e' := lt_min (by linarith) (by linarith)
  have he'1 : e' ≤ e / 2 := min_le_left _ _
  have he'2 : e' ≤ cbar / 2 := min_le_right _ _
  have hpt : u' (cbar - e') < q' * u' cbar := by
    have := hball (x := cbar - e') (by
      rw [Real.dist_eq, show cbar - e' - cbar = -e' by ring, abs_neg, abs_of_pos he'0]
      linarith)
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  have hu'lim : Tendsto (fun t => u' (cs t)) atTop (𝓝 (u' cbar)) := hu'c.tendsto.comp hcsc
  have hqq : q' / q * u' cbar < u' cbar := by
    have : q' / q < 1 := by rw [div_lt_one (by linarith)]; rw [hq'def]; linarith
    nlinarith
  obtain ⟨T1, hT1⟩ := eventually_atTop.1 (((hu'lim.eventually (lt_mem_nhds hqq)).and
    (hcsc.eventually (lt_mem_nhds (by linarith : cbar - e' / 2 < cbar)))).and
    (hksc.eventually (lt_mem_nhds (by linarith : kbar - e' / 4 < kbar))))
  have hclow : ∀ t, T1 ≤ t → c t < cbar - e' := by
    intro t ht
    by_contra hge
    push Not at hge
    have h1 : u' (c t) ≤ u' (cbar - e') :=
      hu'.antitoneOn (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (hc t)) hge
    have h2 := (hT1 t ht).1.1
    have h3 := hratio t
    have hq0 : 0 < q := by linarith
    have h4 : q' * u' cbar < q * u' (cs t) := by
      have := mul_lt_mul_of_pos_left h2 hq0
      rwa [show q * (q' / q * u' cbar) = q' * u' cbar by field_simp] at this
    linarith
  -- (i) capital eventually at least `k̄ + e'/4`, and consumption falls
  set η := e' / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hkhigh : ∀ t, T1 + 1 ≤ t → kbar + η ≤ k t := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hs1 : T1 ≤ s := by omega
    have hm := saddle_resources_mono hδ1 hf hfd hf'pos (hks s).le (hord s).1 (hk s)
    have hc1 := hclow s hs1
    have hc2 := (hT1 s hs1).1.2
    have hk2 := (hT1 (s + 1) (by omega)).2
    rw [(hs s).1]
    have := (hss s).1
    rw [hηdef]
    linarith
  have hcfall : ∀ t, T1 + 1 ≤ t → c (t + 1) < c t := by
    intro t ht
    have hkt := hkhigh (t + 1) (by omega)
    have h48 : k (t + 1) = f (k t) + (1 - δ) * k t - c t := (hs t).1
    exact ((saddle_arrows hβ hu'pos hu' hf' hkbar h411 (hk _) (hc t) (hc _) h48
      (hs t).2).2.2.2.2).2 (by linarith)
  refine ⟨⟨η, hη, T1 + 1, fun t ht => ⟨hkhigh t ht, hcfall t ht⟩⟩, ?_⟩
  -- (ii) `c → 0`: marginal utility grows geometrically
  set r := f' (kbar + η) + 1 - δ with hrdef
  have hr0 : 0 < r := hRpos _ (by linarith)
  have hRbar : f' kbar + 1 - δ = 1 / β := by field_simp; linarith
  have hβr : β * r < 1 := by
    have : f' (kbar + η) < f' kbar := hf' (Set.mem_Ioi.2 hkbar) (Set.mem_Ioi.2 (by linarith))
      (by linarith)
    have h1 : r < 1 / β := by rw [hrdef, ← hRbar]; linarith
    rw [lt_div_iff₀ hβ] at h1
    linarith
  have hβr0 : 0 < β * r := mul_pos hβ hr0
  set T := T1 + 1
  have hRle : ∀ t, T ≤ t → f' (k t) + 1 - δ ≤ r := by
    intro t ht
    have := hf'.antitoneOn (Set.mem_Ioi.2 (by linarith : 0 < kbar + η))
      (Set.mem_Ioi.2 (hk t)) (hkhigh t ht)
    rw [hrdef]; linarith
  have hgeo : ∀ n, u' (c T) ≤ (β * r) ^ n * u' (c (T + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have he := (hs (T + n)).2
      have hR := hRle (T + n + 1) (by omega)
      have hpos := hu'pos _ (hc (T + n + 1))
      have h1 : u' (c (T + n)) ≤ β * r * u' (c (T + n + 1)) := by
        rw [he]
        have := mul_le_mul_of_nonneg_left hR (mul_pos hβ hpos).le
        linarith
      calc u' (c T) ≤ (β * r) ^ n * u' (c (T + n)) := ih
        _ ≤ (β * r) ^ n * (β * r * u' (c (T + n + 1))) :=
          mul_le_mul_of_nonneg_left h1 (pow_pos hβr0 n).le
        _ = (β * r) ^ (n + 1) * u' (c (T + (n + 1))) := by rw [pow_succ]; ring_nf
  have hinf : Tendsto (fun n => u' (c (n + T))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => u' (c T) * ((β * r)⁻¹) ^ n) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv_iff₀.2 ⟨hβr0, hβr⟩)).const_mul_atTop
        (hu'pos _ (hc T))
    refine tendsto_atTop_mono (fun n => ?_) h1
    have := hgeo n
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hβr0 n), add_comm n T]
    linarith
  have hinf' : Tendsto (fun t => u' (c t)) atTop atTop :=
    (tendsto_add_atTop_iff_nat T).1 hinf
  have hc0 : Tendsto c atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun t => ha.trans (hc t),
      fun b hb => ?_⟩
    filter_upwards [hinf'.eventually_gt_atTop (u' b)] with t ht
    by_contra hge
    push Not at hge
    have := hu'.antitoneOn (Set.mem_Ioi.2 hb) (Set.mem_Ioi.2 (hc t)) hge
    linarith
  refine ⟨hc0, ?_⟩
  -- (iii) capital eventually above `k^G + m/2`
  have hkG0 : 0 < kG := hkbar.trans hkG
  set a := min (kbar + η) ((kbar + kG) / 2) with hadef
  have ha1 : a ≤ kbar + η := min_le_left _ _
  have ha2 : a ≤ (kbar + kG) / 2 := min_le_right _ _
  have hakbar : kbar < a := lt_min (by linarith) (by linarith)
  have ha0 : 0 < a := hkbar.trans hakbar
  have haG : a < kG := by linarith
  set m := f a - δ * a with hmdef
  have hm : 0 < m := by
    have h1 := tangent_le hf (Set.mem_Ici.2 ha0.le) (Set.mem_Ici.2 le_rfl) (hfd a ha0)
    rw [hf0] at h1
    have h2 : f' kG < f' a := hf' (Set.mem_Ioi.2 ha0) (Set.mem_Ioi.2 hkG0) haG
    rw [hmdef]
    nlinarith
  have hφ : ∀ x, a ≤ x → x ≤ kG → m ≤ f x - δ * x := by
    intro x hax hxG
    have hx0 : 0 < x := ha0.trans_le hax
    have h1 := tangent_le hf (Set.mem_Ici.2 hx0.le) (Set.mem_Ici.2 ha0.le) (hfd x hx0)
    have h2 : f' kG ≤ f' x := hf'.antitoneOn (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 hkG0) hxG
    rw [hmdef]
    nlinarith [mul_nonneg (by linarith : 0 ≤ f' x - δ) (sub_nonneg.2 hax)]
  obtain ⟨T2, hT2⟩ := eventually_atTop.1 (hc0.eventually (gt_mem_nhds (half_pos hm)))
  obtain ⟨T3, hT3a, hT3b⟩ : ∃ T3, T ≤ T3 ∧ T2 ≤ T3 := ⟨max T T2, le_max_left _ _, le_max_right _ _⟩
  have hstep : ∀ t, T3 ≤ t → k t + m / 2 ≤ k (t + 1) ∨ kG + m / 2 ≤ k (t + 1) := by
    intro t ht
    have hct := hT2 t (hT3b.trans ht)
    have hka : a ≤ k t := (ha1.trans (hkhigh t (hT3a.trans ht)))
    rw [(hs t).1]
    rcases le_or_gt (k t) kG with h | h
    · left
      have := hφ (k t) hka h
      linarith
    · right
      have h1 := saddle_resources_mono hδ1 hf hfd hf'pos hkG0.le h.le (hk t)
      have h2 := hφ kG haG.le le_rfl
      linarith
  have hP : ∀ n, a + n * (m / 2) ≤ k (T3 + n) ∨ kG + m / 2 ≤ k (T3 + n) := by
    intro n
    induction n with
    | zero =>
      left
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact ha1.trans (hkhigh T3 hT3a)
    | succ n ih =>
      rcases hstep (T3 + n) (Nat.le_add_right T3 n) with h | h
      · rcases ih with h' | h'
        · left; push_cast; rw [← add_assoc]; linarith
        · right; rw [← add_assoc]; linarith
      · right; rwa [← add_assoc]
  obtain ⟨N, hN⟩ := exists_nat_gt ((kG + m / 2 - a) / (m / 2))
  have hNm : kG + m / 2 < a + N * (m / 2) := by
    rw [div_lt_iff₀ (half_pos hm)] at hN
    linarith
  set κ := kG + m / 2 with hκdef
  have hκ : ∀ t, T3 + N ≤ t → κ ≤ k t := by
    intro t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = T3 + n := ⟨t - T3, by omega⟩
    rcases hP n with h | h
    · have hnN : (N : ℝ) ≤ n := Nat.cast_le.2 (by omega)
      have := mul_le_mul_of_nonneg_right hnN (half_pos hm).le
      linarith
    · exact h
  refine ⟨⟨T3 + N, fun t ht => by linarith [hκ t ht]⟩, ?_⟩
  -- (iv) the TVC expression diverges (`phase_below_saddle_violates_tvc`)
  have hκ0 : 0 < κ := by linarith
  have hκG : kG < κ := by linarith
  have hρ1 : f' κ + 1 - δ < 1 := by
    have := hf' (Set.mem_Ioi.2 hkG0) (Set.mem_Ioi.2 hκ0) hκG
    linarith
  exact phase_below_saddle_violates_tvc (mu := fun s => u' (c s))
    (R := fun s => f' (k s) + 1 - δ) (k := k) (T := T3 + N) (fun s => (hs s).2)
    (fun s => hRpos _ (hk s)) (hu'pos _ (hc 0)) (hRpos _ hκ0) hρ1
    (fun s hs' => by
      have := hf'.antitoneOn (Set.mem_Ioi.2 hκ0) (Set.mem_Ioi.2 (hk s)) (hκ s hs')
      linarith) hκ0 hκ

end AKMM.DynamicOptimization
