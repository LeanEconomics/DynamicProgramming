/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSolow.Convergence

/-!
# Figure claims: poverty traps (Fig. 3.3) and the speed of convergence (Fig. 3.5)

AKMM, §3.1.1, "Poverty traps", pp. 76–77 (Figure 3.3), and §3.4.1, p. 82 (Figure 3.5).

* **Poverty traps** (p. 77, Fig. 3.3). The figure's picture is captured by
  `SolowThreeCrossings`: `f` continuous and nondecreasing on `k > 0` (Assumption 1 weakened to
  weak monotonicity; no concavity, convexity or differentiability), `0 < δ < 1`, and the curve
  `(1 − δ)k + s f(k)` crossing the 45-degree line at `0 < k̄₁ < k̄₂ < k̄₃` with the figure's sign
  pattern (above, below, above, below). Then the basins are global: every path from
  `k₀ ∈ (0, k̄₂)` converges to `k̄₁`, from `k₀ > k̄₂` to `k̄₃`, and `k̄₂` is a rest point
  (`solow_poverty_trap_basins`); so `k̄₁`, `k̄₃` are locally attracting and `k̄₂` is not, and a
  small perturbation from `k̄₂` moves the path further away (`solow_poverty_trap_stability`).
* **Raising saving** (p. 77). If `f(k) ≥ m k` near `0` (as in the figure, where `f(0) > 0`) and
  `f(k)/k` falls strictly to zero beyond some `k̂`, then any saving rate `s' > δ/m` leaves exactly
  one positive steady state and every path converges to it (`solow_poverty_trap_saving_rise`);
  if `s' > s` it lies above `k̄₃`, and `k̄₁`, `k̄₂` disappear
  (`solow_poverty_trap_saving_rise_removes`). A temporary rise to `s'` for long enough, followed
  by a return to `s`, takes every economy to `k̄₃` (`solow_poverty_trap_temporary_saving`).
* A concrete technology `f(k) = max(1, min(2k − 2, 3))` with `s = δ = 1/10` has steady states
  `1, 2, 3` and satisfies every hypothesis (`solow_poverty_trap_example`); with `s' = 1/2` its
  unique steady state is `15` (`solow_poverty_trap_example_dynamics`).
* **Speed of convergence** (p. 82, Fig. 3.5). In the book's approximation the (relative) gap to
  the steady state obeys `x_{t+1} = (1 − λ)x_t`, so `x_t = (1 − λ)^t x_0`
  (`solow_linearised_gap_closed_form`). For `λ₁ < λ₂ ≤ 1` and the same initial gap, the gap
  under `λ₂` is smaller in absolute value at every date, strictly from date 1 on, both paths stay
  on the side they start (the figure's staircase from `k₀ < k̄`), and the faster path enters every
  band `|x| ≤ ε` no later (`solow_faster_convergence`): a higher `λ` means fewer steps, not "more
  steps" as printed. By (3.11) and (3.13) `λ` falls with `α` and rises with `δ`
  (`solow_speed_parameters`).
-/

namespace AKMM.Solow

open Filter Topology

/-- AKMM, p. 77, Figure 3.3 (the picture's hypotheses). `f` is continuous and nondecreasing on
`k > 0`, `0 < s`, `0 < δ < 1`, and the right side of (3.5), `(1 − δ)k + s f(k)`, crosses the
45-degree line exactly at `0 < k̄₁ < k̄₂ < k̄₃`: above it on `(0, k̄₁)` and `(k̄₂, k̄₃)`, below it
on `(k̄₁, k̄₂)` and beyond `k̄₃`. In the form `s f(k)` against `δ k`. -/
structure SolowThreeCrossings (f : ℝ → ℝ) (s δ k₁ k₂ k₃ : ℝ) : Prop where
  saving_pos : 0 < s
  depreciation_pos : 0 < δ
  depreciation_lt_one : δ < 1
  cont : ContinuousOn f (Set.Ioi 0)
  mono : MonotoneOn f (Set.Ioi 0)
  pos₁ : 0 < k₁
  lt₁₂ : k₁ < k₂
  lt₂₃ : k₂ < k₃
  fix₁ : δ * k₁ = s * f k₁
  fix₂ : δ * k₂ = s * f k₂
  fix₃ : δ * k₃ = s * f k₃
  above₁ : ∀ k, 0 < k → k < k₁ → δ * k < s * f k
  below₂ : ∀ k, k₁ < k → k < k₂ → s * f k < δ * k
  above₃ : ∀ k, k₂ < k → k < k₃ → δ * k < s * f k
  below₄ : ∀ k, k₃ < k → s * f k < δ * k

/-- AKMM, p. 77 (poverty traps, the rising branch of Fig. 3.3): for a continuous nondecreasing
map `g` on `k > 0` with `g(b) = b` and `g` above the diagonal on `(a, b)`, `a ≥ 0`, every path
from `x₀ ∈ (a, b]` rises monotonically to `b`. -/
theorem solow_ptrap_rise {g : ℝ → ℝ} {a b : ℝ} {x : ℕ → ℝ} (ha : 0 ≤ a)
    (hmono : MonotoneOn g (Set.Ioi 0)) (hc : ContinuousOn g (Set.Ioi 0)) (hfix : g b = b)
    (hup : ∀ y, a < y → y < b → y < g y) (h0 : a < x 0) (h0b : x 0 ≤ b)
    (hsucc : ∀ t, x (t + 1) = g (x t)) :
    Monotone x ∧ (∀ t, x 0 ≤ x t ∧ x t ≤ b) ∧ Tendsto x atTop (𝓝 b) := by
  have hb : 0 < b := by linarith
  have hinv : ∀ t, x 0 ≤ x t ∧ x t ≤ b := by
    intro t
    induction t with
    | zero => exact ⟨le_rfl, h0b⟩
    | succ u ih =>
      rw [hsucc u]
      have hpos : 0 < x u := by linarith [ih.1]
      refine ⟨?_, ?_⟩
      · rcases ih.2.lt_or_eq with hl | he
        · exact ih.1.trans (hup _ (by linarith [ih.1]) hl).le
        · rw [he, hfix]; exact h0b
      · rw [← hfix]; exact hmono (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hb) ih.2
  have hstep : ∀ t, x t ≤ x (t + 1) := by
    intro t
    rw [hsucc t]
    rcases (hinv t).2.lt_or_eq with hl | he
    · exact (hup _ (by linarith [(hinv t).1]) hl).le
    · rw [he, hfix]
  have hmon : Monotone x := monotone_nat_of_le_succ hstep
  have hbdd : BddAbove (Set.range x) := ⟨b, by rintro _ ⟨t, rfl⟩; exact (hinv t).2⟩
  have hlim := tendsto_atTop_ciSup hmon hbdd
  have hL0 : x 0 ≤ ⨆ t, x t := le_ciSup hbdd 0
  have hLb : ⨆ t, x t ≤ b := ciSup_le fun t => (hinv t).2
  have hLpos : 0 < ⨆ t, x t := by linarith
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (⨆ t, x t)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g (⨆ t, x t))) := by
    simp only [hsucc]
    exact ((hc.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hlim
  have hgL : g (⨆ t, x t) = ⨆ t, x t := tendsto_nhds_unique h2 h1
  have hLeq : (⨆ t, x t) = b := by
    rcases hLb.lt_or_eq with hl | he
    · exact absurd hgL (ne_of_gt (hup _ (by linarith) hl))
    · exact he
  exact ⟨hmon, hinv, hLeq ▸ hlim⟩

/-- AKMM, p. 77 (poverty traps, the falling branch of Fig. 3.3): for a continuous nondecreasing
map `g` on `k > 0` with `g(b) = b`, `b > 0`, and `g` below the diagonal on `(b, c)`, every path
from `x₀ ∈ [b, c)` falls monotonically to `b`. -/
theorem solow_ptrap_fall {g : ℝ → ℝ} {b c : ℝ} {x : ℕ → ℝ} (hb : 0 < b)
    (hmono : MonotoneOn g (Set.Ioi 0)) (hc : ContinuousOn g (Set.Ioi 0)) (hfix : g b = b)
    (hdown : ∀ y, b < y → y < c → g y < y) (h0 : b ≤ x 0) (h0c : x 0 < c)
    (hsucc : ∀ t, x (t + 1) = g (x t)) :
    Antitone x ∧ (∀ t, b ≤ x t ∧ x t ≤ x 0) ∧ Tendsto x atTop (𝓝 b) := by
  have hinv : ∀ t, b ≤ x t ∧ x t ≤ x 0 := by
    intro t
    induction t with
    | zero => exact ⟨h0, le_rfl⟩
    | succ u ih =>
      rw [hsucc u]
      refine ⟨?_, ?_⟩
      · rw [← hfix]
        exact hmono (Set.mem_Ioi.mpr hb) (Set.mem_Ioi.mpr (by linarith [ih.1])) ih.1
      · rcases ih.1.lt_or_eq with hl | he
        · exact (hdown _ hl (by linarith [ih.2])).le.trans ih.2
        · rw [← he, hfix]; exact h0
  have hstep : ∀ t, x (t + 1) ≤ x t := by
    intro t
    rw [hsucc t]
    rcases (hinv t).1.lt_or_eq with hl | he
    · exact (hdown _ hl (by linarith [(hinv t).2])).le
    · rw [← he, hfix]
  have hanti : Antitone x := antitone_nat_of_succ_le hstep
  have hbdd : BddBelow (Set.range x) := ⟨b, by rintro _ ⟨t, rfl⟩; exact (hinv t).1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hLb : b ≤ ⨅ t, x t := le_ciInf fun t => (hinv t).1
  have hLx : ⨅ t, x t ≤ x 0 := ciInf_le hbdd 0
  have hLpos : 0 < ⨅ t, x t := by linarith
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (⨅ t, x t)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g (⨅ t, x t))) := by
    simp only [hsucc]
    exact ((hc.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hlim
  have hgL : g (⨅ t, x t) = ⨅ t, x t := tendsto_nhds_unique h2 h1
  have hLeq : (⨅ t, x t) = b := by
    rcases hLb.lt_or_eq with hl | he
    · exact absurd hgL (ne_of_lt (hdown _ hl (by linarith)))
    · exact he.symm
  exact ⟨hanti, hinv, hLeq ▸ hlim⟩

/-- AKMM, p. 77, Fig. 3.3: under `SolowThreeCrossings` the right side of (3.5),
`g(k) = (1 − δ)k + s f(k)`, is continuous and nondecreasing on `k > 0`, fixes `k̄₁, k̄₂, k̄₃`, lies
above the diagonal on `(0, k̄₁)` and `(k̄₂, k̄₃)` and below it on `(k̄₁, k̄₂)` and `(k̄₃, ∞)`. -/
theorem solow_three_crossings_map {f : ℝ → ℝ} {s δ k₁ k₂ k₃ : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) :
    MonotoneOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) ∧
      ContinuousOn (fun x => (1 - δ) * x + s * f x) (Set.Ioi 0) ∧
      (1 - δ) * k₁ + s * f k₁ = k₁ ∧ (1 - δ) * k₂ + s * f k₂ = k₂ ∧
      (1 - δ) * k₃ + s * f k₃ = k₃ ∧
      (∀ y, 0 < y → y < k₁ → y < (1 - δ) * y + s * f y) ∧
      (∀ y, k₁ < y → y < k₂ → (1 - δ) * y + s * f y < y) ∧
      (∀ y, k₂ < y → y < k₃ → y < (1 - δ) * y + s * f y) ∧
      (∀ y, k₃ < y → (1 - δ) * y + s * f y < y) := by
  refine ⟨?_, ?_, by linarith [h.fix₁], by linarith [h.fix₂], by linarith [h.fix₃],
    fun y h1 h2 => by linarith [h.above₁ y h1 h2], fun y h1 h2 => by linarith [h.below₂ y h1 h2],
    fun y h1 h2 => by linarith [h.above₃ y h1 h2], fun y h1 => by linarith [h.below₄ y h1]⟩
  · intro x hx y hy hxy
    have h1 := mul_le_mul_of_nonneg_left (h.mono hx hy hxy) h.saving_pos.le
    have h2 := mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr h.depreciation_lt_one.le)
    simp only
    linarith
  · exact (continuousOn_id.const_mul (1 - δ)).add (h.cont.const_mul s)

/-- AKMM, p. 77, Fig. 3.3 (the basins): "when the economy starts from a very low `k₀`, the
economy converges to `k̄₁` and gets trapped in it"; "pushed up to a larger level than `k̄₂`, … it
would converge to `k̄₃`". Every path of (3.5) from `k₀ ∈ (0, k̄₂)` converges to `k̄₁`, from
`k₀ = k̄₂` stays there, and from `k₀ > k̄₂` converges to `k̄₃`. -/
theorem solow_poverty_trap_basins {f : ℝ → ℝ} {s δ k₁ k₂ k₃ : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = (1 - δ) * k t + s * f (k t)) :
    (k 0 < k₂ → Tendsto k atTop (𝓝 k₁)) ∧ (k 0 = k₂ → ∀ t, k t = k₂) ∧
      (k₂ < k 0 → Tendsto k atTop (𝓝 k₃)) := by
  obtain ⟨hm, hc, hf1, hf2, hf3, hu1, hd2, hu3, hd4⟩ := solow_three_crossings_map h
  have p1 := h.pos₁
  have p12 := h.lt₁₂
  have p23 := h.lt₂₃
  refine ⟨fun hlt => ?_, fun heq t => ?_, fun hgt => ?_⟩
  · rcases le_or_gt (k 0) k₁ with hle | hgt1
    · exact (solow_ptrap_rise le_rfl hm hc hf1 hu1 hk0 hle hk).2.2
    · exact (solow_ptrap_fall p1 hm hc hf1 hd2 hgt1.le hlt hk).2.2
  · induction t with
    | zero => exact heq
    | succ u ih => rw [hk u, ih]; exact hf2
  · rcases le_or_gt (k 0) k₃ with hle | hgt3
    · exact (solow_ptrap_rise (by linarith) hm hc hf3 hu3 hgt hle hk).2.2
    · exact (solow_ptrap_fall (by linarith) hm hc hf3 (fun y hy _ => hd4 y hy) hgt3.le
        (lt_add_one (k 0)) hk).2.2

/-- AKMM, p. 77, Fig. 3.3: "of these three, `k̄₁` and `k̄₃` are stable steady states", while `k̄₂`
is not: "a small perturbation away from the steady state leads further away from it". Under
`SolowThreeCrossings`, `k̄₁` and `k̄₃` are locally attracting for the map of (3.5), `k̄₂` is not,
and just below (above) `k̄₂` the map moves capital down (up), away from `k̄₂`. -/
theorem solow_poverty_trap_stability {f : ℝ → ℝ} {s δ k₁ k₂ k₃ : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) :
    SolowLocallyAttracting (fun x => (1 - δ) * x + s * f x) k₁ ∧
      SolowLocallyAttracting (fun x => (1 - δ) * x + s * f x) k₃ ∧
      ¬ SolowLocallyAttracting (fun x => (1 - δ) * x + s * f x) k₂ ∧
      (∀ y, k₁ < y → y < k₂ → (1 - δ) * y + s * f y < y) ∧
      (∀ y, k₂ < y → y < k₃ → y < (1 - δ) * y + s * f y) := by
  obtain ⟨-, -, -, -, -, -, hd2, hu3, -⟩ := solow_three_crossings_map h
  have p1 := h.pos₁
  have p12 := h.lt₁₂
  have p23 := h.lt₂₃
  set g := fun x => (1 - δ) * x + s * f x with hg
  have horb : ∀ x₀ : ℝ, ∀ t, g^[t + 1] x₀ = (1 - δ) * g^[t] x₀ + s * f (g^[t] x₀) :=
    fun x₀ t => Function.iterate_succ_apply' g t x₀
  have hlow : ∀ x₀, 0 < x₀ → x₀ < k₂ → Tendsto (fun t => g^[t] x₀) atTop (𝓝 k₁) :=
    fun x₀ h0 h2 => (solow_poverty_trap_basins h (k := fun t => g^[t] x₀) h0 (horb x₀)).1 h2
  have hhigh : ∀ x₀, k₂ < x₀ → Tendsto (fun t => g^[t] x₀) atTop (𝓝 k₃) :=
    fun x₀ h2 => (solow_poverty_trap_basins h (k := fun t => g^[t] x₀) (by
      change 0 < x₀; linarith) (horb x₀)).2.2 h2
  refine ⟨⟨min k₁ (k₂ - k₁), lt_min p1 (by linarith), fun x₀ hx => ?_⟩,
    ⟨k₃ - k₂, by linarith, fun x₀ hx => ?_⟩, ?_, hd2, hu3⟩
  · have hm1 := min_le_left k₁ (k₂ - k₁)
    have hm2 := min_le_right k₁ (k₂ - k₁)
    rw [abs_lt] at hx
    exact hlow x₀ (by linarith) (by linarith)
  · rw [abs_lt] at hx
    exact hhigh x₀ (by linarith)
  · rintro ⟨ε, hε, hat⟩
    have hm : 0 < min ε (k₂ - k₁) := lt_min hε (by linarith)
    have hm1 := min_le_left ε (k₂ - k₁)
    have hm2 := min_le_right ε (k₂ - k₁)
    have h2 := hat (k₂ - min ε (k₂ - k₁) / 2) (by
      rw [abs_lt]; constructor <;> linarith)
    have h1 := hlow (k₂ - min ε (k₂ - k₁) / 2) (by linarith) (by linarith)
    have := tendsto_nhds_unique h1 h2
    linarith

/-- AKMM, p. 77: "if the saving rate is raised sufficiently … the steady states `k̄₁` and `k̄₂`
will disappear and the economy converges globally". Suppose `f` is continuous and nondecreasing
on `k > 0`, `f(k) ≥ m k` on `(0, k̂]` for some `m > 0` (in Fig. 3.3, `f(0) > 0`), and the average
product `f(k)/k` is strictly decreasing on `[k̂, ∞)` with limit `0`. Then for every saving rate
`s' > δ/m` there is exactly one positive steady state `k̄ > k̂`, the curve is above the diagonal
below it and below the diagonal above it, and every path from `k₀ > 0` converges to it. -/
theorem solow_poverty_trap_saving_rise {f : ℝ → ℝ} {δ s' m kh : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hc : ContinuousOn f (Set.Ioi 0)) (hmono : MonotoneOn f (Set.Ioi 0)) (hm : 0 < m)
    (hkh : 0 < kh) (hlow : ∀ k, 0 < k → k ≤ kh → m * k ≤ f k)
    (hanti : StrictAntiOn (fun k => f k / k) (Set.Ici kh))
    (hlim : Tendsto (fun k => f k / k) atTop (𝓝 0)) (hs' : δ / m < s') :
    ∃ ks, kh < ks ∧ δ * ks = s' * f ks ∧ (∀ k, 0 < k → k < ks → δ * k < s' * f k) ∧
      (∀ k, ks < k → s' * f k < δ * k) ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → (∀ t, x (t + 1) = (1 - δ) * x t + s' * f (x t)) →
        Tendsto x atTop (𝓝 ks) := by
  have hs'pos : 0 < s' := lt_trans (div_pos hδ hm) hs'
  have hδs : δ < s' * m := (div_lt_iff₀ hm).mp hs'
  have hq : 0 < δ / s' := div_pos hδ hs'pos
  have hqm : δ / s' < m := (div_lt_iff₀ hs'pos).mpr (by linarith)
  have hkh_av : m ≤ f kh / kh := (le_div_iff₀ hkh).mpr (hlow kh hkh le_rfl)
  -- a capital stock beyond `k̂` with average product below `δ/s'`
  obtain ⟨K, hK, hKkh⟩ := ((hlim.eventually (gt_mem_nhds hq)).and
    (eventually_ge_atTop kh)).exists
  have hKpos : 0 < K := lt_of_lt_of_le hkh hKkh
  have hcav : ContinuousOn (fun k => f k / k) (Set.Icc kh K) := by
    have hsub : Set.Icc kh K ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le hkh hy.1
    exact (hc.mono hsub).div continuousOn_id fun y hy => ne_of_gt (hsub hy)
  obtain ⟨ks, hks, hksv⟩ := intermediate_value_Icc' hKkh hcav
    (Set.mem_Icc.mpr ⟨hK.le, by linarith⟩)
  have hksv' : f ks / ks = δ / s' := hksv
  have hkspos : 0 < ks := lt_of_lt_of_le hkh hks.1
  have hkslt : kh < ks := by
    rcases hks.1.lt_or_eq with hl | he
    · exact hl
    · rw [← he] at hksv'; linarith
  have hfix : δ * ks = s' * f ks := by
    rw [div_eq_div_iff (ne_of_gt hkspos) (ne_of_gt hs'pos)] at hksv'
    linarith
  have hbelow : ∀ k, 0 < k → k < ks → δ * k < s' * f k := by
    intro k hk hlt
    rcases le_or_gt k kh with hle | hgt
    · have := hlow k hk hle
      nlinarith
    · have h := hanti (Set.mem_Ici.mpr hgt.le) (Set.mem_Ici.mpr hks.1) hlt
      simp only at h
      rw [hksv', div_lt_div_iff₀ hs'pos hk] at h
      linarith
  have habove : ∀ k, ks < k → s' * f k < δ * k := by
    intro k hlt
    have hk : 0 < k := hkspos.trans hlt
    have h := hanti (Set.mem_Ici.mpr hks.1) (Set.mem_Ici.mpr (hks.1.trans hlt.le)) hlt
    simp only at h
    rw [hksv', div_lt_div_iff₀ hk hs'pos] at h
    linarith
  refine ⟨ks, hkslt, hfix, hbelow, habove, fun x hx0 hx => ?_⟩
  have hgm : StrictMonoOn (fun y => (1 - δ) * y + s' * f y) (Set.Ioi 0) := by
    intro y hy z hz hyz
    have h1 := mul_le_mul_of_nonneg_left (hmono hy hz hyz.le) hs'pos.le
    have h2 := mul_lt_mul_of_pos_left hyz (sub_pos.mpr hδ1)
    simp only
    linarith
  have hgc : ContinuousOn (fun y => (1 - δ) * y + s' * f y) (Set.Ioi 0) :=
    (continuousOn_id.const_mul (1 - δ)).add (hc.const_mul s')
  exact (Solow1956.DiscreteTime.Map.attracting_orbit hgm hgc hkspos (by linarith)
    (fun y hy hlt => by linarith [hbelow y hy hlt]) (fun y hlt => by linarith [habove y hlt])
    hx0 hx).2.2.2.2.2

/-- AKMM, p. 77 (poverty traps): raising the saving rate from `s` to `s' > max(s, δ/m)` removes
the steady states `k̄₁` and `k̄₂` of Fig. 3.3: the only positive steady state at `s'` lies above
`k̄₃`, at `k̄₁` and `k̄₂` the curve is now strictly above the diagonal, and the economy converges
globally to the new steady state. -/
theorem solow_poverty_trap_saving_rise_removes {f : ℝ → ℝ} {s δ k₁ k₂ k₃ s' m kh : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) (hm : 0 < m) (hkh : 0 < kh)
    (hlow : ∀ k, 0 < k → k ≤ kh → m * k ≤ f k)
    (hanti : StrictAntiOn (fun k => f k / k) (Set.Ici kh))
    (hlim : Tendsto (fun k => f k / k) atTop (𝓝 0)) (hs' : δ / m < s') (hss : s < s') :
    ∃ ks, k₃ < ks ∧ δ * ks = s' * f ks ∧ (∀ k, 0 < k → δ * k = s' * f k → k = ks) ∧
      δ * k₁ < s' * f k₁ ∧ δ * k₂ < s' * f k₂ ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → (∀ t, x (t + 1) = (1 - δ) * x t + s' * f (x t)) →
        Tendsto x atTop (𝓝 ks) := by
  obtain ⟨ks, -, hfix, hbelow, habove, hconv⟩ := solow_poverty_trap_saving_rise
    h.depreciation_pos h.depreciation_lt_one h.cont h.mono hm hkh hlow hanti hlim hs'
  have p1 := h.pos₁
  have p12 := h.lt₁₂
  have p23 := h.lt₂₃
  have hδ := h.depreciation_pos
  have hs := h.saving_pos
  -- at `k̄₃` the new curve is strictly above the diagonal
  have hf3 : 0 < f k₃ := by
    have := h.fix₃
    have : 0 < s * f k₃ := by rw [← this]; exact mul_pos hδ (by linarith)
    exact pos_of_mul_pos_right this hs.le
  have h3 : δ * k₃ < s' * f k₃ := by
    rw [h.fix₃]; exact mul_lt_mul_of_pos_right hss hf3
  have hks3 : k₃ < ks := by
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hl | he
    · linarith [habove k₃ hl]
    · rw [he] at hfix; linarith
  have huniq : ∀ k, 0 < k → δ * k = s' * f k → k = ks := by
    intro k hk he
    rcases lt_trichotomy k ks with hl | heq | hg
    · linarith [hbelow k hk hl]
    · exact heq
    · linarith [habove k hg]
  exact ⟨ks, hks3, hfix, huniq, hbelow k₁ p1 (by linarith), hbelow k₂ (by linarith)
    (by linarith), hconv⟩

/-- AKMM, p. 77 (escaping the trap): "to escape from the trap, the capital stock would have to be
pushed up to a larger level than `k̄₂`, from which it would converge to `k̄₃`. One way to achieve
this movement is to (temporarily) encourage very high saving." Under the hypotheses of
`solow_poverty_trap_saving_rise_removes`, from every `k₀ > 0` there is a date `T` such that
saving at `s'` before `T` and at the original `s` from `T` on takes the economy to `k̄₃`. -/
theorem solow_poverty_trap_temporary_saving {f : ℝ → ℝ} {s δ k₁ k₂ k₃ s' m kh : ℝ}
    (h : SolowThreeCrossings f s δ k₁ k₂ k₃) (hm : 0 < m) (hkh : 0 < kh)
    (hlow : ∀ k, 0 < k → k ≤ kh → m * k ≤ f k)
    (hanti : StrictAntiOn (fun k => f k / k) (Set.Ici kh))
    (hlim : Tendsto (fun k => f k / k) atTop (𝓝 0)) (hs' : δ / m < s') (hss : s < s')
    {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∃ T : ℕ, ∀ k : ℕ → ℝ, k 0 = k₀ →
      (∀ t, t < T → k (t + 1) = (1 - δ) * k t + s' * f (k t)) →
      (∀ t, T ≤ t → k (t + 1) = (1 - δ) * k t + s * f (k t)) → Tendsto k atTop (𝓝 k₃) := by
  obtain ⟨ks, hks3, -, -, -, -, hconv⟩ :=
    solow_poverty_trap_saving_rise_removes h hm hkh hlow hanti hlim hs' hss
  set g := fun y => (1 - δ) * y + s' * f y with hg
  have horb : ∀ t, g^[t + 1] k₀ = (1 - δ) * g^[t] k₀ + s' * f (g^[t] k₀) :=
    fun t => Function.iterate_succ_apply' g t k₀
  have hx := hconv (fun t => g^[t] k₀) hk₀ horb
  obtain ⟨T, hT⟩ := (hx.eventually (lt_mem_nhds (h.lt₂₃.trans hks3))).exists
  refine ⟨T, fun k hk0 hbefore hafter => ?_⟩
  have hagree : ∀ t, t ≤ T → k t = g^[t] k₀ := by
    intro t
    induction t with
    | zero => intro _; exact hk0
    | succ u ih =>
      intro hu
      rw [hbefore u (by omega), ih (by omega), horb u]
  have hkT : k₂ < k T := by rw [hagree T le_rfl]; exact hT
  have hshift : Tendsto (fun t => k (t + T)) atTop (𝓝 k₃) := by
    have hp : 0 < k₂ := h.pos₁.trans h.lt₁₂
    refine (solow_poverty_trap_basins h (k := fun t => k (t + T)) (by
      rw [zero_add]; linarith) (fun t => ?_)).2.2 (by
      rw [zero_add]; exact hkT)
    rw [show t + 1 + T = t + T + 1 by omega]
    exact hafter (t + T) (by omega)
  exact (tendsto_add_atTop_iff_nat T).mp hshift

/-- AKMM, p. 77, Fig. 3.3 (a concrete instance): a technology with a convex middle section,
`f(k) = max(1, min(2k − 2, 3))`, flat at `1` up to `k = 3/2`, rising with slope `2` and flat at
`3` from `k = 5/2`. -/
noncomputable def solowPovertyTrapTech (k : ℝ) : ℝ := max 1 (min (2 * k - 2) 3)

/-- AKMM, p. 77, Fig. 3.3: the hypotheses are not vacuous. With `f = solowPovertyTrapTech` and
`s = δ = 1/10`, `SolowThreeCrossings` holds with `k̄₁ = 1`, `k̄₂ = 2`, `k̄₃ = 3`; and
`f(k) ≥ (2/5)k` on `(0, 5/2]`, `f(k)/k = 3/k` is strictly decreasing on `[5/2, ∞)` with
limit `0`. -/
theorem solow_poverty_trap_example :
    SolowThreeCrossings solowPovertyTrapTech (1 / 10) (1 / 10) 1 2 3 ∧
      (∀ k, 0 < k → k ≤ 5 / 2 → 2 / 5 * k ≤ solowPovertyTrapTech k) ∧
      StrictAntiOn (fun k => solowPovertyTrapTech k / k) (Set.Ici (5 / 2)) ∧
      Tendsto (fun k => solowPovertyTrapTech k / k) atTop (𝓝 0) := by
  have hge : ∀ k, 1 ≤ solowPovertyTrapTech k := fun k => le_max_left _ _
  have htop : ∀ k, 5 / 2 ≤ k → solowPovertyTrapTech k = 3 := by
    intro k hk
    unfold solowPovertyTrapTech
    rw [min_eq_right (by linarith), max_eq_right (by norm_num)]
  have hv : ∀ k, solowPovertyTrapTech k = max 1 (min (2 * k - 2) 3) := fun k => rfl
  have h1 : solowPovertyTrapTech 1 = 1 := by
    rw [hv, min_eq_left (by norm_num), max_eq_left (by norm_num)]
  have h2 : solowPovertyTrapTech 2 = 2 := by
    rw [hv, min_eq_left (by norm_num), max_eq_right (by norm_num)]
    norm_num
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num,
    by rw [h1], by rw [h2], by rw [htop 3 (by norm_num)], ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (continuous_const.max (((continuous_const.mul continuous_id).sub
      continuous_const).min continuous_const)).continuousOn
  · intro x _ y _ hxy
    exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)
  · intro k _ hk
    linarith [hge k]
  · intro k hk1 hk2
    have : solowPovertyTrapTech k < k := by
      rw [hv]
      exact max_lt hk1 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    linarith
  · intro k hk2 hk3
    have : k < solowPovertyTrapTech k := by
      rw [hv]
      exact lt_of_lt_of_le (lt_min (by linarith) hk3) (le_max_right _ _)
    linarith
  · intro k hk3
    have : solowPovertyTrapTech k < k := by
      rw [hv]
      exact max_lt (by linarith) (lt_of_le_of_lt (min_le_right _ _) hk3)
    linarith
  · intro k _ hk
    linarith [hge k]
  · intro x hx y hy hxy
    have hx' : (5 : ℝ) / 2 ≤ x := hx
    have hy' : (5 : ℝ) / 2 ≤ y := hy
    simp only [htop x hx', htop y hy']
    exact div_lt_div_of_pos_left (by norm_num) (by linarith) hxy
  · have h3 : Tendsto (fun k : ℝ => 3 / k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop (5 / 2)] with k hk
    rw [htop k hk]

/-- AKMM, p. 77, Fig. 3.3, for the concrete technology `solowPovertyTrapTech` with
`s = δ = 1/10`: paths from `k₀ ∈ (0, 2)` converge to `1` and from `k₀ > 2` to `3`; `1` and `3`
are locally attracting and `2` is not; and at the saving rate `s' = 1/2` the only positive
steady state is `15`, to which every path converges. -/
theorem solow_poverty_trap_example_dynamics :
    (∀ k : ℕ → ℝ, 0 < k 0 → (∀ t, k (t + 1) = (1 - 1 / 10) * k t +
        1 / 10 * solowPovertyTrapTech (k t)) →
      (k 0 < 2 → Tendsto k atTop (𝓝 1)) ∧ (2 < k 0 → Tendsto k atTop (𝓝 3))) ∧
      SolowLocallyAttracting (fun x => (1 - 1 / 10) * x + 1 / 10 * solowPovertyTrapTech x) 1 ∧
      SolowLocallyAttracting (fun x => (1 - 1 / 10) * x + 1 / 10 * solowPovertyTrapTech x) 3 ∧
      ¬ SolowLocallyAttracting
        (fun x => (1 - 1 / 10) * x + 1 / 10 * solowPovertyTrapTech x) 2 ∧
      (∀ k, 0 < k → 1 / 10 * k = 1 / 2 * solowPovertyTrapTech k → k = 15) ∧
      1 / 10 * 15 = 1 / 2 * solowPovertyTrapTech 15 ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → (∀ t, x (t + 1) = (1 - 1 / 10) * x t +
        1 / 2 * solowPovertyTrapTech (x t)) → Tendsto x atTop (𝓝 15) := by
  obtain ⟨h, hlow, hanti, hlim⟩ := solow_poverty_trap_example
  obtain ⟨hs1, hs3, hs2, -, -⟩ := solow_poverty_trap_stability h
  obtain ⟨ks, -, -, huniq, -, -, hconv⟩ :=
    solow_poverty_trap_saving_rise_removes (s' := 1 / 2) h
    (by norm_num : (0 : ℝ) < 2 / 5) (by norm_num : (0 : ℝ) < 5 / 2) hlow hanti hlim
    (by norm_num) (by norm_num)
  have h15 : 1 / 10 * (15 : ℝ) = 1 / 2 * solowPovertyTrapTech 15 := by
    unfold solowPovertyTrapTech
    rw [min_eq_right (by norm_num), max_eq_right (by norm_num)]
    norm_num
  have hks : (15 : ℝ) = ks := huniq 15 (by norm_num) h15
  refine ⟨fun k hk0 hk => ?_, hs1, hs3, hs2, fun k hk he => (huniq k hk he).trans hks.symm, h15,
    fun x hx0 hx => hks ▸ hconv x hx0 hx⟩
  have hb := solow_poverty_trap_basins h hk0 hk
  exact ⟨hb.1, hb.2.2⟩

/-- AKMM, p. 82: in the book's approximation (3.10), written in relative deviations, the gap
`x_t = (k_t − k̄)/k̄` (or `Δk_t = k_t − k̄`) obeys `x_{t+1} = (1 − λ)x_t`, so
`x_t = (1 − λ)^t x_0`: `λ` is the fraction of the remaining gap closed each period. -/
theorem solow_linearised_gap_closed_form {lam : ℝ} {x : ℕ → ℝ}
    (hx : ∀ t, x (t + 1) = (1 - lam) * x t) (t : ℕ) : x t = (1 - lam) ^ t * x 0 := by
  induction t with
  | zero => simp
  | succ u ih => rw [hx u, ih, pow_succ]; ring

/-- AKMM, p. 82, Figure 3.5 ("slow and fast convergence"): "a large value of `λ` implies that
`Δk_{t+1}` becomes smaller (in absolute value) more quickly, implying a faster convergence". Two
economies with speeds `λ₁ < λ₂ ≤ 1` (as in (3.10), where `λ < 1`) start from the same gap
`x₀` in the approximation `x_{t+1} = (1 − λ)x_t`. Then at every date the gap of the faster one is
no larger in absolute value, strictly smaller from date 1 on when `x₀ ≠ 0`; starting below the
steady state (`x₀ ≤ 0`, the figure's `k₀ < k̄`) both stay below it with the faster one closer
(`x_t ≤ y_t ≤ 0`); and whenever the slower gap is within `ε` the faster one is too, so the
faster economy needs no more steps to come within any `ε` of the steady state (and strictly fewer
for some `ε`). -/
theorem solow_faster_convergence {lam₁ lam₂ : ℝ} {x y : ℕ → ℝ} (hlam : lam₁ < lam₂)
    (hlam₂ : lam₂ ≤ 1) (hx : ∀ t, x (t + 1) = (1 - lam₁) * x t)
    (hy : ∀ t, y (t + 1) = (1 - lam₂) * y t) (h0 : y 0 = x 0) :
    (∀ t, |y t| ≤ |x t|) ∧ (x 0 ≠ 0 → ∀ t, 0 < t → |y t| < |x t|) ∧
      (x 0 ≤ 0 → ∀ t, x t ≤ y t ∧ y t ≤ 0) ∧ (∀ ε t, |x t| ≤ ε → |y t| ≤ ε) ∧
      (x 0 ≠ 0 → ∃ ε, |y 1| ≤ ε ∧ ¬ |x 1| ≤ ε) := by
  have hb : 0 ≤ 1 - lam₂ := by linarith
  have hab : 1 - lam₂ < 1 - lam₁ := by linarith
  have hxt := solow_linearised_gap_closed_form hx
  have hyt := solow_linearised_gap_closed_form hy
  have hpow : ∀ t, (1 - lam₂) ^ t ≤ (1 - lam₁) ^ t := fun t => pow_le_pow_left₀ hb hab.le t
  have habs : ∀ t, |y t| ≤ |x t| := by
    intro t
    rw [hxt t, hyt t, h0, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hb t),
      abs_of_nonneg (pow_nonneg (hb.trans hab.le) t)]
    exact mul_le_mul_of_nonneg_right (hpow t) (abs_nonneg _)
  have hstrict : x 0 ≠ 0 → ∀ t, 0 < t → |y t| < |x t| := by
    intro hx0 t ht
    rw [hxt t, hyt t, h0, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hb t),
      abs_of_nonneg (pow_nonneg (hb.trans hab.le) t)]
    exact mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hab hb (Nat.pos_iff_ne_zero.mp ht))
      (abs_pos.mpr hx0)
  refine ⟨habs, hstrict, fun hx0 t => ?_, fun ε t hε => (habs t).trans hε, fun hx0 => ?_⟩
  · rw [hxt t, hyt t, h0]
    exact ⟨mul_le_mul_of_nonpos_right (hpow t) hx0,
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hb t) hx0⟩
  · exact ⟨|y 1|, le_rfl, not_le.mpr (hstrict hx0 1 one_pos)⟩

/-- AKMM, p. 83 ("the convergence is faster when `α` is small and `δ` is large"), for (3.11)
`λ = δ(1 − α)`, and the same for (3.13) `λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))` with
`(1 + γ)(1 + n) ≥ 1`: `λ` is strictly decreasing in `α` and strictly increasing in `δ`. -/
theorem solow_speed_parameters {α α' δ δ' G : ℝ} (hα : α < α') (hα1 : α' < 1) (hδ : 0 < δ)
    (hδδ : δ < δ') (hδ1 : δ' ≤ 1) (hG : 1 ≤ G) :
    δ * (1 - α') < δ * (1 - α) ∧ δ * (1 - α') < δ' * (1 - α') ∧
      (1 - α') * (1 - (1 - δ) / G) < (1 - α) * (1 - (1 - δ) / G) ∧
      (1 - α') * (1 - (1 - δ) / G) < (1 - α') * (1 - (1 - δ') / G) := by
  have hGpos : 0 < G := by linarith
  have hq : (1 - δ) / G < 1 := by
    rw [div_lt_one hGpos]; linarith
  have hqq : (1 - δ') / G < (1 - δ) / G := div_lt_div_of_pos_right (by linarith) hGpos
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end AKMM.Solow
