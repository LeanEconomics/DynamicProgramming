/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectBellman

/-!
# First-order and envelope conditions from the functional equation

SLP §18.1, pp. 545–546, (4)–(7). The book writes down the first-order condition (4) and the
envelope condition (5) for the bounded solution `W` of the individual's functional equation
(3), citing Chapter 4 (Theorems 4.10–4.11, Benveniste–Scheinkman), and evaluates them on the
diagonal to get (6)–(7). This module derives them.

* `hasDerivAt_of_concave_of_le` (**Benveniste–Scheinkman**, Theorem 4.10): a function `v`
  concave on a neighbourhood of `x₀`, minorised near `x₀` by a function `W` differentiable at
  `x₀` and touching it there, is differentiable at `x₀` with `v′(x₀) = W′(x₀)`. (Squeeze the
  slopes of `v` at `x₀` between those of `W` at `x₀` and at the reflected point `2x₀ − x`.)
* `bellman_concave`: for `U` concave and bounded on `[0, ∞)`, the bounded solution `W(·, k)`
  is concave in own capital `x` on `[0, ∞)`. (It is the supremum of the sequence-problem values
  (`bellman_isLUB`), the budget is linear in the path, and a convex combination of feasible
  paths is feasible.)
* `bellman_foc` (**§18.1 (4)**): at an optimal choice `y ∈ (0, A(k) + B(k)x)`, if `U` is
  differentiable at `c = A(k) + B(k)x − y` and `W(·, g(k))` at `y`, then
  `U′(c) = β W₁(y, g(k))`.
* `bellman_envelope` (**§18.1 (5)**): at `x > 0` with an optimal choice `y` and `c > 0`, `U`
  differentiable at `c` and concave: `W(·, k)` is differentiable at `x` with
  `W₁(x, k) = B(k) U′(c)`.
* `bellman_diagonal` (**§18.1 (6)–(7)**, generic budget): if `h(k)` is optimal at `(k, k)` and
  `h(h(k))` at `(h(k), h(k))`, with interior choices, then `φ(k) := W₁(k, k)` satisfies
  `φ(k) = B(k) U′(F(k) − h(k))` and `U′(F(k) − h(k)) = β φ(h(k))`; hence the Euler equation
  `U′(F(k) − h(k)) = β B(h(k)) U′(F(h(k)) − h(h(k)))`.
* `eq_18_1_4_5` and `eq_18_1_6_7`: the same for the taxed economy (3) literally, with
  `F = f`, `B = (1 − θ) f′`. `ex_18_1_foc_envelope`: the untaxed (2) (`θ = 0`).
* `eq_18_1_6_7_of_equilibrium`: combined with `indirect_equilibrium_full`: for the pseudo-planner's
  policy `ĥ` with interior choices, the bounded solution `W` of (3) satisfies (4)–(7), with
  `φ = W₁(k, k)`.

The hypotheses are those of SLP Theorem 4.11: interior state (`x > 0`), interior choice
(`0 < y`, `c > 0`), and differentiability of `U` at the optimal consumption. Differentiability of
`W(·, g(k))` at the optimal `y`, needed in (4), is itself supplied by (5) at the next date when
the next choice is interior (`bellman_diagonal`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- **Benveniste–Scheinkman** (SLP Theorem 4.10). Let `v` be concave on a set `S` that is a
neighbourhood of `x₀`, and let `W ≤ v` near `x₀` with `W(x₀) = v(x₀)` and `W` differentiable at
`x₀` with derivative `d`. Then `v` is differentiable at `x₀` with derivative `d`. -/
theorem hasDerivAt_of_concave_of_le {v W : ℝ → ℝ} {S : Set ℝ} {x₀ d : ℝ}
    (hv : ConcaveOn ℝ S v) (hS : S ∈ 𝓝 x₀) (hle : ∀ᶠ x in 𝓝 x₀, W x ≤ v x)
    (heq : W x₀ = v x₀) (hW : HasDerivAt W d x₀) : HasDerivAt v d x₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hW ⊢
  -- the reflection `x ↦ 2x₀ − x` maps `𝓝[≠] x₀` to itself
  have hr : Tendsto (fun x => 2 * x₀ - x) (𝓝[≠] x₀) (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x => 2 * x₀ - x) (𝓝 x₀) (𝓝 (2 * x₀ - x₀)) :=
        (continuous_const.sub continuous_id).tendsto x₀
      rw [show 2 * x₀ - x₀ = x₀ by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro h
      apply hx
      change x = x₀
      change 2 * x₀ - x = x₀ at h
      linarith
  have hL := hW.comp hr
  have hlo := hW.min hL
  have hhi := hW.max hL
  rw [min_self] at hlo
  rw [max_self] at hhi
  -- a symmetric neighbourhood on which everything holds
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hS hle)
  have hsq : ∀ᶠ x in 𝓝[≠] x₀, min (slope W x₀ x) ((slope W x₀ ∘ fun x => 2 * x₀ - x) x) ≤
      slope v x₀ x ∧ slope v x₀ x ≤
        max (slope W x₀ x) ((slope W x₀ ∘ fun x => 2 * x₀ - x) x) := by
    have hmem : Metric.ball x₀ δ ∈ 𝓝[≠] x₀ :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x₀ hδ)
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hne
    have hne' : x ≠ x₀ := hne
    set a := 2 * x₀ - x with ha
    have hxb : |x - x₀| < δ := by rwa [Metric.mem_ball, Real.dist_eq] at hx
    have hab : a ∈ Metric.ball x₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, ha]
      rw [show 2 * x₀ - x - x₀ = -(x - x₀) by ring, abs_neg]
      exact hxb
    have hx0b : x₀ ∈ Metric.ball x₀ δ := Metric.mem_ball_self hδ
    obtain ⟨hxS, hxW⟩ := hball hx
    obtain ⟨haS, haW⟩ := hball hab
    obtain ⟨hx0S, -⟩ := hball hx0b
    change W x ≤ v x at hxW
    change W a ≤ v a at haW
    simp only [Function.comp, slope_def_field]
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · -- `x < x₀ < a`
      have hxa : x₀ < a := by rw [ha]; linarith
      have h1 : (v x₀ - v x) / (x₀ - x) ≤ (W x₀ - W x) / (x₀ - x) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have h2 : (v a - v x₀) / (a - x₀) ≤ (v x₀ - v x) / (x₀ - x) :=
        hv.slope_anti_adjacent hxS haS hlt hxa
      have h3 : (W a - W x₀) / (a - x₀) ≤ (v a - v x₀) / (a - x₀) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e1 : (v x - v x₀) / (x - x₀) = (v x₀ - v x) / (x₀ - x) := by
        rw [← neg_sub (v x₀), ← neg_sub x₀, neg_div_neg_eq]
      have e2 : (W x - W x₀) / (x - x₀) = (W x₀ - W x) / (x₀ - x) := by
        rw [← neg_sub (W x₀), ← neg_sub x₀, neg_div_neg_eq]
      rw [e1, e2]
      exact ⟨(min_le_right _ _).trans (h3.trans h2), h1.trans (le_max_left _ _)⟩
    · -- `a < x₀ < x`
      have hxa : a < x₀ := by rw [ha]; linarith
      have h1 : (W x - W x₀) / (x - x₀) ≤ (v x - v x₀) / (x - x₀) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have h2 : (v x - v x₀) / (x - x₀) ≤ (v x₀ - v a) / (x₀ - a) :=
        hv.slope_anti_adjacent haS hxS hxa hgt
      have h3 : (v x₀ - v a) / (x₀ - a) ≤ (W x₀ - W a) / (x₀ - a) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e2 : (W a - W x₀) / (a - x₀) = (W x₀ - W a) / (x₀ - a) := by
        rw [← neg_sub (W x₀), ← neg_sub x₀, neg_div_neg_eq]
      rw [e2]
      exact ⟨(min_le_left _ _).trans h1, h2.trans (h3.trans (le_max_right _ _))⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hsq.mono fun _ h => h.1)
    (hsq.mono fun _ h => h.2)

/-- **Concavity of the bounded solution in own capital.** Under the hypotheses of
`bellman_isLUB` and with `U` concave on `[0, ∞)`, `x ↦ W(x, k)` is concave on `[0, ∞)` for every
`k ∈ K`. -/
theorem bellman_concave {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hUc : ConcaveOn ℝ (Ici 0) U) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hsol : SolvesBellman U A B g W β K)
    {k : ℝ} (hk : k ∈ K) : ConcaveOn ℝ (Ici 0) fun x => W x k := by
  refine ⟨convex_Ici 0, fun x hx x' hx' a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := hx
  have hx0' : (0 : ℝ) ≤ x' := hx'
  have hz : 0 ≤ a * x + b * x' := by positivity
  set at' : ℕ → ℝ := fun t => A (g^[t] k) with hat
  set bt : ℕ → ℝ := fun t => B (g^[t] k) with hbt
  have hL := bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hx0 hk
  have hL' := bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hx0' hk
  have hLz := bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hz hk
  -- any convex combination of attainable values is at most `W(a x + b x', k)`
  have key : ∀ S ∈ indivValues U β at' bt x, ∀ S' ∈ indivValues U β at' bt x',
      a * S + b * S' ≤ W (a * x + b * x') k := by
    rintro S ⟨p, hp, hS⟩ S' ⟨p', hp', hS'⟩
    set q : ℕ → ℝ := fun t => a * p t + b * p' t with hq
    have hcq : ∀ t, consPath at' bt q t = a * consPath at' bt p t + b * consPath at' bt p' t := by
      intro t
      simp only [consPath, hq]
      linear_combination (-at' t) * hab
    have hqf : IndivFeasible at' bt (a * x + b * x') q := by
      refine ⟨by simp only [hq, hp.1, hp'.1], fun t => ⟨?_, ?_⟩⟩
      · have := (hp.2 t).1
        have := (hp'.2 t).1
        simp only [hq]
        positivity
      · rw [hcq]
        have := (hp.2 t).2
        have := (hp'.2 t).2
        positivity
    have hsum : Summable fun t => β ^ t * U (consPath at' bt q t) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
        fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (hU _ (hqf.2 t).2) (pow_nonneg hβ0 t)
    have hle : a * S + b * S' ≤ ∑' t, β ^ t * U (consPath at' bt q t) := by
      refine hasSum_le (fun t => ?_) ((hS.mul_left a).add (hS'.mul_left b)) hsum.hasSum
      rw [hcq]
      have hcc := hUc.2 (mem_Ici.2 (hp.2 t).2) (mem_Ici.2 (hp'.2 t).2) ha hb hab
      simp only [smul_eq_mul] at hcc
      have := mul_le_mul_of_nonneg_left hcc (pow_nonneg hβ0 t)
      linarith
    exact hle.trans (hLz.1 ⟨q, hqf, hsum.hasSum⟩)
  -- pass to the suprema
  simp only [smul_eq_mul]
  by_contra hcon
  push Not at hcon
  set η := a * W x k + b * W x' k - W (a * x + b * x') k with hη
  have hηp : 0 < η := by linarith
  obtain ⟨S, hS, hS1, -⟩ := hL.exists_between (show W x k - η / 2 < W x k by linarith)
  obtain ⟨S', hS', hS1', -⟩ := hL'.exists_between (show W x' k - η / 2 < W x' k by linarith)
  have h := key S hS S' hS'
  have h1 := mul_le_mul_of_nonneg_left hS1.le ha
  have h2 := mul_le_mul_of_nonneg_left hS1'.le hb
  have : a * (W x k - η / 2) + b * (W x' k - η / 2) = a * W x k + b * W x' k - η / 2 := by
    have : a * (η / 2) + b * (η / 2) = η / 2 := by rw [← add_mul, hab, one_mul]
    linarith
  linarith

/-- The maximand of the functional equation is bounded above on `Γ(x, k)`. -/
theorem bellman_bddAbove {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hK : ∀ k ∈ K, g k ∈ K) (x : ℝ) {k : ℝ} (hk : k ∈ K) :
    BddAbove ((fun y => U (A k + B k * x - y) + β * W y (g k)) '' feasY A B x k) := by
  refine ⟨B₀ + β * M, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 := (abs_le.1 (hU _ hy.2)).2
  have h2 := (abs_le.1 (hW y hy.1 _ (hK k hk))).2
  have := mul_le_mul_of_nonneg_left h2 hβ0
  simp only
  linarith

/-- **The first-order condition §18.1 (4).** Let `W` be a bounded solution of the functional
equation, `x ≥ 0`, `k ∈ K`, and let `y` attain the supremum at `(x, k)` with
`0 < y < A(k) + B(k)x` (an interior choice). If `U` has derivative `u` at
`c = A(k) + B(k)x − y` and `W(·, g(k))` has derivative `w` at `y`, then `u = β w`:
`U′(c) = β W₁(y, g(k))`. -/
theorem bellman_foc {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hK : ∀ k ∈ K, g k ∈ K) (hsol : SolvesBellman U A B g W β K) {x k y u w : ℝ}
    (hx : 0 ≤ x) (hk : k ∈ K) (hy : 0 < y) (hc : y < A k + B k * x)
    (hopt : U (A k + B k * x - y) + β * W y (g k) = W x k)
    (hUd : HasDerivAt U u (A k + B k * x - y))
    (hWd : HasDerivAt (fun z => W z (g k)) w y) : u = β * w := by
  set φ : ℝ → ℝ := fun z => U (A k + B k * x - z) + β * W z (g k) with hφ
  have hmax : IsLocalMax φ y := by
    filter_upwards [Ioo_mem_nhds hy hc] with z hz
    have hzf : z ∈ feasY A B x k := ⟨hz.1.le, by linarith [hz.2]⟩
    change φ z ≤ φ y
    have h1 : φ y = W x k := hopt
    rw [h1, hsol x hx k hk]
    exact le_csSup (bellman_bddAbove hβ0 hU hW hK x hk) ⟨z, hzf, rfl⟩
  have hd1 : HasDerivAt (fun z => U (A k + B k * x - z)) (u * -1) y := by
    have hi : HasDerivAt (fun z => A k + B k * x - z) (-1) y :=
      (hasDerivAt_id y).const_sub (A k + B k * x)
    exact hUd.comp y hi
  have hd : HasDerivAt φ (u * -1 + β * w) y := hd1.add (hWd.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **The envelope condition §18.1 (5)** (Benveniste–Scheinkman). Let `U` be concave and
bounded on `[0, ∞)`, `W` a bounded solution of the functional equation, `k ∈ K`, `x > 0`, and
let `y ≥ 0` attain the supremum at `(x, k)` with positive consumption
`c = A(k) + B(k)x − y > 0`. If `U` has derivative `u` at `c`, then `W(·, k)` is differentiable
at `x` with `W₁(x, k) = B(k) u = B(k) U′(c)`. -/
theorem bellman_envelope {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hUc : ConcaveOn ℝ (Ici 0) U) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hsol : SolvesBellman U A B g W β K)
    {x k y u : ℝ} (hx : 0 < x) (hk : k ∈ K) (hy : 0 ≤ y) (hc : 0 < A k + B k * x - y)
    (hopt : U (A k + B k * x - y) + β * W y (g k) = W x k)
    (hUd : HasDerivAt U u (A k + B k * x - y)) :
    HasDerivAt (fun z => W z k) (B k * u) x := by
  set Wf : ℝ → ℝ := fun z => U (A k + B k * z - y) + β * W y (g k) with hWf
  have hi : HasDerivAt (fun z => A k + B k * z - y) (B k) x := by
    have := (((hasDerivAt_id x).const_mul (B k)).const_add (A k)).sub_const y
    simpa using this
  have hWfd : HasDerivAt Wf (B k * u) x := by
    have := (hUd.comp x hi).add_const (β * W y (g k))
    rw [mul_comm u] at this
    exact this
  have hcont : Continuous fun z => A k + B k * z - y := by fun_prop
  have hle : ∀ᶠ z in 𝓝 x, Wf z ≤ W z k := by
    filter_upwards [Ioi_mem_nhds hx, hcont.continuousAt.eventually (Ioi_mem_nhds hc)]
      with z hz hcz
    have hz0 : 0 ≤ z := le_of_lt hz
    have hyf : y ∈ feasY A B z k := ⟨hy, le_of_lt hcz⟩
    rw [hsol z hz0 k hk]
    exact le_csSup (bellman_bddAbove hβ0 hU hW hK z hk) ⟨y, hyf, rfl⟩
  exact hasDerivAt_of_concave_of_le (bellman_concave hβ0 hβ1 hUc hU hW hK hA hB hsol hk)
    (Ici_mem_nhds hx) hle hopt hWfd

/-- **§18.1 (6)–(7) on the diagonal, generic budget.** Let `U` be concave and bounded on
`[0, ∞)`, `W` a bounded solution of the functional equation with aggregate law `h`, and on `K`
let `A(k) + B(k) k = F(k)`. Let `k ∈ K` with `k > 0`, and suppose that `h(k)` is optimal at
`(k, k)` and `h(h(k))` at `(h(k), h(h(k)))` (`H(k, k; h) = h(k)`), with interior choices
`0 < h(k)`, `F(k) − h(k) > 0`, `h(h(k)) ≥ 0`, `F(h(k)) − h(h(k)) > 0`, and `U` differentiable
at both consumptions. Then, with `φ(k) = W₁(k, k)`:
(7) `W(·, k)` is differentiable at `k` and `φ(k) = B(k) U′(F(k) − h(k))`, and likewise at
`h(k)`; (6) `U′(F(k) − h(k)) = β φ(h(k))`; hence the Euler equation
`U′(F(k) − h(k)) = β B(h(k)) U′(F(h(k)) − h(h(k)))`. -/
theorem bellman_diagonal {U A B Fk h : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hUc : ConcaveOn ℝ (Ici 0) U) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, h k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hAB : ∀ k ∈ K, A k + B k * k = Fk k)
    (hsol : SolvesBellman U A B h W β K) {k : ℝ} (hk : k ∈ K) (hk0 : 0 < k)
    (hh0 : 0 < h k) (hc1 : 0 < Fk k - h k) (hhh0 : 0 ≤ h (h k))
    (hc2 : 0 < Fk (h k) - h (h k))
    (hopt1 : U (A k + B k * k - h k) + β * W (h k) (h k) = W k k)
    (hopt2 : U (A (h k) + B (h k) * h k - h (h k)) + β * W (h (h k)) (h (h k)) =
      W (h k) (h k))
    (hUd1 : DifferentiableAt ℝ U (Fk k - h k))
    (hUd2 : DifferentiableAt ℝ U (Fk (h k) - h (h k))) :
    HasDerivAt (fun x => W x k) (B k * deriv U (Fk k - h k)) k ∧
      HasDerivAt (fun x => W x (h k)) (B (h k) * deriv U (Fk (h k) - h (h k))) (h k) ∧
      deriv (fun x => W x k) k = B k * deriv U (Fk k - h k) ∧
      deriv U (Fk k - h k) = β * deriv (fun x => W x (h k)) (h k) ∧
      deriv U (Fk k - h k) = β * B (h k) * deriv U (Fk (h k) - h (h k)) := by
  have hhk := hK k hk
  have e1 : A k + B k * k - h k = Fk k - h k := by rw [hAB k hk]
  have e2 : A (h k) + B (h k) * h k - h (h k) = Fk (h k) - h (h k) := by rw [hAB _ hhk]
  have hd1 : HasDerivAt (fun x => W x k) (B k * deriv U (Fk k - h k)) k := by
    refine bellman_envelope hβ0 hβ1 hUc hU hW hK hA hB hsol hk0 hk hh0.le (by rwa [e1]) hopt1
      ?_
    rw [e1]
    exact hUd1.hasDerivAt
  have hd2 : HasDerivAt (fun x => W x (h k)) (B (h k) * deriv U (Fk (h k) - h (h k))) (h k) := by
    refine bellman_envelope hβ0 hβ1 hUc hU hW hK hA hB hsol hh0 hhk hhh0 (by rwa [e2]) hopt2 ?_
    rw [e2]
    exact hUd2.hasDerivAt
  have hfoc := bellman_foc hβ0 hU hW hK hsol hk0.le hk hh0 (by linarith [e1]) hopt1
    (by rw [e1]; exact hUd1.hasDerivAt) hd2
  refine ⟨hd1, hd2, hd1.deriv, ?_, ?_⟩
  · rw [hd2.deriv]
    exact hfoc
  · rw [hfoc]
    ring

/-- **§18.1 (4)–(5) for the taxed economy (3)**, literally. Tax `θ < 1` on capital income,
rebated; `U` concave and bounded on `[0, ∞)`; `f′ ≥ 0` and `f(k) − (1 − θ) k f′(k) ≥ 0` on `K`;
`W` a bounded solution of (3) with aggregate law `h`. Let `k ∈ K`, `x > 0`, and let `y = H(x, k)`
attain the supremum in (3) at `(x, k)`, with `0 < y` and consumption
`c = f(k) + (1 − θ)(x − k) f′(k) − y > 0`, `U` differentiable at `c`. Then
(5) `W₁(x, k) = (1 − θ) f′(k) U′(c)`; and (4) if `W(·, h(k))` is differentiable at `y`,
`U′(c) = β W₁(y, h(k))`. -/
theorem eq_18_1_4_5 {U f h : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : θ < 1) (hUc : ConcaveOn ℝ (Ici 0) U)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K)
    {x k y : ℝ} (hx : 0 < x) (hk : k ∈ K) (hy : 0 < y)
    (hc : 0 < f k + (1 - θ) * (x - k) * deriv f k - y)
    (hopt : U (f k + (1 - θ) * (x - k) * deriv f k - y) + β * W y (h k) = W x k)
    (hUd : DifferentiableAt ℝ U (f k + (1 - θ) * (x - k) * deriv f k - y)) :
    HasDerivAt (fun z => W z k)
        ((1 - θ) * deriv f k * deriv U (f k + (1 - θ) * (x - k) * deriv f k - y)) x ∧
      (DifferentiableAt ℝ (fun z => W z (h k)) y →
        deriv U (f k + (1 - θ) * (x - k) * deriv f k - y) =
          β * deriv (fun z => W z (h k)) y) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  have e : (fun k => f k - (1 - θ) * k * deriv f k) k + (fun k => (1 - θ) * deriv f k) k * x - y =
      f k + (1 - θ) * (x - k) * deriv f k - y := by simp only; ring
  refine ⟨?_, fun hWd => ?_⟩
  · refine bellman_envelope hβ0 hβ1 hUc hU hW hK hw hB hsol hx hk hy.le (by rwa [e])
      (by rwa [e]) ?_
    rw [e]
    exact hUd.hasDerivAt
  · refine bellman_foc hβ0 hU hW hK hsol hx.le hk hy (by linarith [e]) (by rwa [e]) ?_
      hWd.hasDerivAt
    rw [e]
    exact hUd.hasDerivAt

/-- **§18.1 (6)–(7) for the taxed economy (3)** (p. 546). Hypotheses of `eq_18_1_4_5`; let `h`
be an equilibrium at `k` and `h(k)` (`h(k)` optimal at `(k, k)`, `h(h(k))` optimal at
`(h(k), h(k))`) with `k > 0`, `h(k) > 0`, `h(h(k)) ≥ 0` and positive consumptions
`f(k) − h(k)`, `f(h(k)) − h(h(k))`, `U` differentiable there. Then `φ(k) := W₁(k, k; h)` satisfies
(7) `φ(k) = (1 − θ) f′(k) U′[f(k) − h(k)]` and (6) `U′[f(k) − h(k)] = β φ[h(k)]`; hence
`U′[f(k) − h(k)] = β (1 − θ) f′(h(k)) U′[f(h(k)) − h(h(k))]`. -/
theorem eq_18_1_6_7 {U f h : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : θ < 1) (hUc : ConcaveOn ℝ (Ici 0) U)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K)
    {k : ℝ} (hk : k ∈ K) (hk0 : 0 < k) (hh0 : 0 < h k) (hc1 : 0 < f k - h k)
    (hhh0 : 0 ≤ h (h k)) (hc2 : 0 < f (h k) - h (h k))
    (hopt1 : U (f k + (1 - θ) * (k - k) * deriv f k - h k) + β * W (h k) (h k) = W k k)
    (hopt2 : U (f (h k) + (1 - θ) * (h k - h k) * deriv f (h k) - h (h k)) +
      β * W (h (h k)) (h (h k)) = W (h k) (h k))
    (hUd1 : DifferentiableAt ℝ U (f k - h k))
    (hUd2 : DifferentiableAt ℝ U (f (h k) - h (h k))) :
    deriv (fun x => W x k) k = (1 - θ) * deriv f k * deriv U (f k - h k) ∧
      deriv U (f k - h k) = β * deriv (fun x => W x (h k)) (h k) ∧
      deriv U (f k - h k) = β * (1 - θ) * deriv f (h k) * deriv U (f (h k) - h (h k)) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  have e : ∀ k : ℝ, (fun k => f k - (1 - θ) * k * deriv f k) k +
      (fun k => (1 - θ) * deriv f k) k * k = f k := fun k => by simp only; ring
  have e' : ∀ k : ℝ, f k + (1 - θ) * (k - k) * deriv f k = f k := fun k => by ring
  rw [e'] at hopt1 hopt2
  obtain ⟨-, -, h3, h4, h5⟩ := bellman_diagonal (Fk := f) hβ0 hβ1 hUc hU hW hK hw hB
    (fun k _ => e k) hsol hk hk0 hh0 hc1 hhh0 hc2 (by rw [e]; exact hopt1)
    (by rw [e]; exact hopt2) hUd1 hUd2
  refine ⟨h3, h4, ?_⟩
  rw [h5]
  ring

/-- **(4)–(7) at the indirect equilibrium.** Under the hypotheses of `indirect_equilibrium_full`
(the pseudo-planner's policy `ĥ`, with the individual's transversality condition), let `W` be
the bounded solution of (3) with `h = ĥ`. At every `k ∈ K` with `k > 0`, `ĥ(k) > 0` and positive
consumptions `f(k) − ĥ(k)`, `f(ĥ(k)) − ĥ(ĥ(k))`, the function `φ(k) = W₁(k, k; ĥ)` exists and
satisfies (7) `φ(k) = (1 − θ) f′(k) U′[f(k) − ĥ(k)]` and (6) `U′[f(k) − ĥ(k)] = β φ[ĥ(k)]`.
So the solution of (6)–(7) produced by the pseudo-economy is the marginal value of the
individual's own capital, as the book asserts on p. 546. -/
theorem eq_18_1_6_7_of_equilibrium {U f h : ℝ → ℝ} {β θ B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ K, 0 ≤ deriv f k)
    (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k) (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0)) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
        (fun k => (1 - θ) * deriv f k) h W β K ∧
      ∀ k ∈ K, 0 < k → 0 < h k → 0 < f k - h k → 0 < f (h k) - h (h k) →
        deriv (fun x => W x k) k = (1 - θ) * deriv f k * deriv U (f k - h k) ∧
        deriv U (f k - h k) = β * deriv (fun x => W x (h k)) (h k) := by
  obtain ⟨W, M, hWb, hsol, -, hall⟩ := indirect_equilibrium_full hU hβ0 hβ1 hθ0 hθ hUd hU' hUb
    hf hK hK0 hfd hf' hw hc heul htvc
  refine ⟨W, M, hWb, hsol, fun k hk hk0 hh0 hc1 hc2 => ?_⟩
  have hhk := hK k hk
  have hfeas : ∀ k ∈ K, h k ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) k k := fun k hk => ⟨hK0 _ (hK k hk), by
        have := hc k hk
        simp only
        linarith⟩
  have hopt1 := ((hall k hk).2.2 (h k) (hfeas k hk)).2 rfl
  have hopt2 := ((hall (h k) hhk).2.2 (h (h k)) (hfeas _ hhk)).2 rfl
  obtain ⟨h1, h2, -⟩ := eq_18_1_6_7 hβ0.le hβ1 hθ hU.concaveOn hUb hK hf' hw hWb hsol hk hk0
    hh0 hc1 (hK0 _ (hK _ hhk)) hc2 hopt1 hopt2 (hUd _ hc1.le) (hUd _ hc2.le)
  exact ⟨h1, h2⟩

/-- **The first-order and envelope conditions for (2)** (Exercise 18.1 setting). Under the
hypotheses of `ex_18_1_full` (the planner's policy `g` with its Euler equation and transversality
condition), let `V` be the bounded solution of (2). At every `k ∈ K` with `k > 0`, `g(k) > 0` and
positive consumptions `f(k) − g(k)`, `f(g(k)) − g(g(k))`:
`V₁(k, k; g) = f′(k) U′[f(k) − g(k)]` and `U′[f(k) − g(k)] = β V₁(g(k), g(k); g)`. -/
theorem ex_18_1_foc_envelope {U f g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k) (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0)) :
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K ∧
      ∀ k ∈ K, 0 < k → 0 < g k → 0 < f k - g k → 0 < f (g k) - g (g k) →
        deriv (fun x => V x k) k = deriv f k * deriv U (f k - g k) ∧
        deriv U (f k - g k) = β * deriv (fun x => V x (g k)) (g k) := by
  obtain ⟨V, M, hVb, hsol, -, hall⟩ := ex_18_1_full hU hβ0 hβ1 hUd hU' hUb hf hK hK0 hfd hf' hw
    hc heul htvc
  refine ⟨V, M, hVb, hsol, fun k hk hk0 hg0 hc1 hc2 => ?_⟩
  have hgk := hK k hk
  have e : ∀ k : ℝ, (fun k => f k - k * deriv f k) k + deriv f k * k = f k := fun k => by
    simp only; ring
  have e' : ∀ k : ℝ, f k + (k - k) * deriv f k = f k := fun k => by ring
  have hfeas : ∀ k ∈ K, g k ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k :=
    fun k hk => ⟨hK0 _ (hK k hk), by have := hc k hk; simp only; linarith⟩
  have hopt1 := ((hall k hk).2 (g k) (hfeas k hk)).2 rfl
  have hopt2 := ((hall (g k) hgk).2 (g (g k)) (hfeas _ hgk)).2 rfl
  rw [e'] at hopt1 hopt2
  obtain ⟨-, -, h3, h4, -⟩ := bellman_diagonal (Fk := f) hβ0.le hβ1 hU.concaveOn hUb hVb hK hw
    hf' (fun k _ => e k) hsol hk hk0 hg0 hc1 (hK0 _ (hK _ hgk)) hc2 (by rw [e]; exact hopt1)
    (by rw [e]; exact hopt2) (hUd _ hc1.le) (hUd _ hc2.le)
  exact ⟨h3, h4⟩

end StokeyLucasPrescott.EquilibriaWithDistortions
