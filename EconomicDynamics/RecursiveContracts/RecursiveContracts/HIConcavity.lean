/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HIOptimal
import RecursiveContracts.HIAssumption

/-!
# Concavity of the value function (Proposition 22.3.1)

Miao, §22.3.1, pp. 792–793: under Assumption 22.3.1 (DARA) the Bellman operator maps concave
functions in `F` to concave functions, so the value function `P = lim Tᵏ L` is concave.

The proof follows the book. For contracts `(c⁰, w⁰)` at `v⁰` and `(c¹, w¹)` at `v¹`, the
averaged contract `(c*, w*)` delivers `δv⁰ + (1 − δ)v¹`, gives the principal at least the average
(`hi_mix_principal_ge`) and, by DARA, satisfies the local downward constraints
(`hi_mix_downward`); `w*` is monotone. Such a "relaxed" contract is then repaired into an
incentive-compatible one with the same promised value and a weakly higher value to the principal
(`hi_repair`), by alternating two moves:

* **reduce the spread of `w`** (`hi_adjust_increments`): lower every increment `wᵢ − wᵢ₋₁` to
  `max(Dᵢ, 0)`, where `βDᵢ = u(θᵢ + cᵢ₋₁) − u(θᵢ + cᵢ)` is the increment at which `Cᵢ,ᵢ₋₁` binds,
  keeping `Σ πᵢ wᵢ`. This is a sequence of mean-preserving spread reductions
  (`hi_spread_reduction_weak`) and weakly raises `Σ πᵢ f(wᵢ)` for concave `f`. If now `c` is
  decreasing, every local downward constraint binds and the contract is incentive compatible
  (`hi_upward_of_binding`, Lemma 22.3.2).
* **pool the transfers** (`hi_pool`): otherwise some pair has `cᵢ₋₁ < cᵢ` and `wᵢ₋₁ = wᵢ`. On the
  set of states sharing that continuation value, `c` is increasing; replacing it there by the
  single transfer `c̄` with the same expected utility lowers the expected transfer
  (`hi_pool_cost`, a Chebyshev-sum argument with the tangent line of `u`), keeps the local
  downward constraints and strictly lowers the number of steps of the contract (`hi_steps`).

The repair terminates by strong induction on `hi_steps`. This replaces the book's sketch on
p. 793 ("reduce `c*₂` until `C₂,₁` binds … adding a constant to each `c*ᵢ`"), which does not keep
promise keeping.

* `hi_T_concaveOn`: `T` maps concave functions in `F` to concave functions.
* `hi_L_concaveOn`: the lower bound `−b(v)/(1 − β)` is concave.
* `proposition_22_3_1_concave`: the value function `P` is concave on `(−∞, vmax)`.
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- A concave function on a convex set has decreasing increments there. -/
theorem hi_incr_le_on_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {x y d : ℝ}
    (hx : x ∈ s) (hyd : y + d ∈ s) (hxy : x ≤ y) (hd : 0 ≤ d) :
    f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hoc := hf.1.ordConnected
      have hy : y ∈ s := hoc.out hx hyd ⟨hxy.le, by linarith⟩
      have hxd : x + d ∈ s := hoc.out hx hyd ⟨by linarith, by linarith⟩
      have h1 := hf.neg.secant_mono (a := x) (x := x + d) (y := y + d) hx hxd hyd
        (by linarith) (by linarith) (by linarith)
      have h2 := hf.neg.secant_mono (a := y + d) (x := x) (y := y) hyd hx hy
        (by linarith) (by linarith) hxy.le
      simp only [Pi.neg_apply] at h1 h2
      have e1 : (-f (x + d) - -f x) / (x + d - x) = -((f (x + d) - f x) / d) := by
        rw [show x + d - x = d by ring]; ring
      have e2 : (-f (y + d) - -f x) / (y + d - x) = -((f (y + d) - f x) / (y + d - x)) := by
        ring
      have e3 : (-f x - -f (y + d)) / (x - (y + d)) = -((f (y + d) - f x) / (y + d - x)) := by
        rw [show x - (y + d) = -(y + d - x) by ring, div_neg]; ring
      have e4 : (-f y - -f (y + d)) / (y - (y + d)) = -((f (y + d) - f y) / d) := by
        rw [show y - (y + d) = -d by ring, div_neg]; ring
      rw [e1, e2] at h1
      rw [e3, e4] at h2
      exact (div_le_div_iff_of_pos_right hd).1 (by linarith)
    · simp
  · exact le_rfl

/-- For a concave function, the slope on `[x₁, x₂]` is at least the slope on `[x₃, x₄]` when
`x₁ < x₂ ≤ x₃ < x₄`. -/
theorem hi_slope_anti_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {x1 x2 x3 x4 : ℝ} (h1 : x1 ∈ s) (h4 : x4 ∈ s) (h12 : x1 < x2) (h23 : x2 ≤ x3)
    (h34 : x3 < x4) :
    (f x4 - f x3) / (x4 - x3) ≤ (f x2 - f x1) / (x2 - x1) := by
  have hoc := hf.1.ordConnected
  rcases h23.lt_or_eq with h23 | rfl
  · have hx2 : x2 ∈ s := hoc.out h1 h4 ⟨h12.le, by linarith⟩
    have a := hf.slope_anti_adjacent h1 (hoc.out h1 h4 ⟨by linarith, by linarith⟩) h12 h23
    have b := hf.slope_anti_adjacent hx2 h4 h23 h34
    linarith
  · exact hf.slope_anti_adjacent h1 h4 h12 h34

/-- Miao, pp. 793–794, weak form of `hi_spread_reduction`: for `f` concave on `(−∞, vmax)` and
`0 ≤ δ ≤ w_k − w_{k−1}`, the mean-preserving spread reduction weakly raises `Σ πⱼ f(wⱼ)`. -/
theorem hi_spread_reduction_weak (M : HIModel) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {w : Fin (M.N + 1) → ℝ}
    (hw : ∀ j, w j < hi_vmax M) (hmono : Monotone w) (i : Fin M.N) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδw : δ ≤ w i.succ - w i.castSucc) :
    (∀ j, hi_reduce M w i.succ δ j < hi_vmax M) ∧
      ∑ j, M.prob j * f (w j) ≤ ∑ j, M.prob j * f (hi_reduce M w i.succ δ j) := by
  rcases hδ0.lt_or_eq with hδ | hδ
  swap
  · subst hδ
    have : ∀ j, hi_reduce M w i.succ 0 j = w j := fun j => by
      unfold hi_reduce; split_ifs <;> ring
    simp only [this]
    exact ⟨hw, le_rfl⟩
  obtain ⟨hq0, hq1⟩ := hi_upperMass_bounds M i
  set q := hi_upperMass M i.succ
  set a := w i.castSucc
  set b := w i.succ
  set e := δ * (1 - q)
  have he : 0 < e := mul_pos hδ (by linarith)
  have hdq : 0 < δ * q := mul_pos hδ hq0
  have hab : a + δ * q ≤ b - e := by simp only [e]; nlinarith
  have hbV : b < hi_vmax M := hw _
  have hred : ∀ j, hi_reduce M w i.succ δ j =
      if i.succ ≤ j then w j - e else w j + δ * q := fun j => by
    unfold hi_reduce; split_ifs <;> simp only [e, q] <;> ring
  have hlow : ∀ j, ¬ i.succ ≤ j → w j ≤ a := fun j hj => by
    apply hmono
    rw [not_le] at hj
    exact Fin.le_castSucc_iff.2 hj
  have hhigh : ∀ j, i.succ ≤ j → b ≤ w j := fun j hj => hmono hj
  refine ⟨fun j => ?_, ?_⟩
  · rw [hred j]
    split_ifs with hj
    · linarith [hw j]
    · linarith [hlow j hj]
  set gainL := f (a + δ * q) - f a
  set lossU := f b - f (b - e)
  have hterm : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) ≤
      M.prob j * (f (hi_reduce M w i.succ δ j) - f (w j)) := fun j => by
    refine mul_le_mul_of_nonneg_left ?_ (M.prob_pos j).le
    rw [hred j]
    split_ifs with hj
    · have := hi_incr_le_on_concave hf (x := b - e) (y := w j - e) (d := e)
        (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith [hw j])
        (by linarith [hhigh j hj]) he.le
      simp only [sub_add_cancel] at this
      simp only [lossU]; linarith
    · have := hi_incr_le_on_concave hf (x := w j) (y := a) (d := δ * q)
        (by simp only [Set.mem_Iio]; linarith [hw j]) (by simp only [Set.mem_Iio]; linarith)
        (hlow j hj) hdq.le
      simp only [gainL]; linarith
  have hsum : ∑ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
      gainL - (gainL + lossU) * q := by
    have : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
        M.prob j * gainL - (gainL + lossU) * (M.prob j * (if i.succ ≤ j then 1 else 0)) :=
        fun j => by split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hi_sum_const, ← Finset.mul_sum]
    rfl
  have hslope := hi_slope_anti_concave hf (x1 := a) (x2 := a + δ * q) (x3 := b - e) (x4 := b)
    (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith)
    (by linarith) hab (by linarith)
  rw [show b - (b - e) = e by ring, show a + δ * q - a = δ * q by ring,
    div_le_div_iff₀ he hdq] at hslope
  have hpos : 0 ≤ gainL - (gainL + lossU) * q := by
    have h3 : lossU * (δ * q) ≤ gainL * (δ * (1 - q)) := hslope
    have : δ * (gainL - (gainL + lossU) * q) = gainL * (δ * (1 - q)) - lossU * (δ * q) := by
      ring
    have h4 : 0 ≤ δ * (gainL - (gainL + lossU) * q) := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hδ
  have htot := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [hsum] at htot
  simp only [mul_sub, Finset.sum_sub_distrib] at htot
  linarith

/-- The spread reduction lowers the reduced increment by `δ` and keeps the others. -/
theorem hi_reduce_incr (M : HIModel) (w : Fin (M.N + 1) → ℝ) (i l : Fin M.N) (δ : ℝ) :
    hi_reduce M w i.succ δ l.succ - hi_reduce M w i.succ δ l.castSucc =
      (w l.succ - w l.castSucc) - (if l = i then δ else 0) := by
  unfold hi_reduce
  by_cases hl : l = i
  · subst hl
    have hn : ¬ l.succ ≤ l.castSucc := not_le.2 Fin.castSucc_lt_succ
    simp only [le_refl, hn, ↓reduceIte]; ring
  · have hiff : (i.succ ≤ l.succ ↔ i.succ ≤ l.castSucc) := by
      rw [Fin.le_def, Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      have : l.val ≠ i.val := fun h => hl (Fin.ext h)
      omega
    by_cases h : i.succ ≤ l.castSucc
    · simp only [h, hiff.2 h, hl, ↓reduceIte]; ring
    · have h' : ¬ i.succ ≤ l.succ := fun h'' => h (hiff.1 h'')
      simp only [h, h', hl, ↓reduceIte]; ring

/-- Miao, pp. 792–793: lowering the increments of a monotone list of continuation values to any
targets `0 ≤ eₗ ≤ w_{l+1} − w_l`, keeping the mean, weakly raises `Σ πⱼ f(wⱼ)` for concave `f`
(a sequence of mean-preserving spread reductions). -/
theorem hi_adjust_increments (M : HIModel) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {w : Fin (M.N + 1) → ℝ}
    (hw : ∀ j, w j < hi_vmax M) (e : Fin M.N → ℝ) (he0 : ∀ l, 0 ≤ e l)
    (hle : ∀ l, e l ≤ w l.succ - w l.castSucc) :
    ∃ w' : Fin (M.N + 1) → ℝ, (∀ j, w' j < hi_vmax M) ∧
      (∀ l, w' l.succ - w' l.castSucc = e l) ∧
      ∑ j, M.prob j * w' j = ∑ j, M.prob j * w j ∧
      ∑ j, M.prob j * f (w j) ≤ ∑ j, M.prob j * f (w' j) := by
  have key : ∀ k : ℕ, ∃ w' : Fin (M.N + 1) → ℝ, (∀ j, w' j < hi_vmax M) ∧
      (∀ l : Fin M.N, w' l.succ - w' l.castSucc =
        if l.val < k then e l else w l.succ - w l.castSucc) ∧
      ∑ j, M.prob j * w' j = ∑ j, M.prob j * w j ∧
      ∑ j, M.prob j * f (w j) ≤ ∑ j, M.prob j * f (w' j) := by
    intro k
    induction k with
    | zero => exact ⟨w, hw, fun l => by simp, rfl, le_rfl⟩
    | succ k ih =>
      obtain ⟨w', hw', hinc, hmean, hineq⟩ := ih
      have hmono' : Monotone w' := Fin.monotone_iff_le_succ.2 fun l => by
        have h := hinc l
        split_ifs at h <;> linarith [he0 l, hle l]
      by_cases hk : k < M.N
      · set l0 : Fin M.N := ⟨k, hk⟩
        set δ := (w l0.succ - w l0.castSucc) - e l0
        have hδ : 0 ≤ δ := by simp only [δ]; linarith [hle l0]
        have hδw : δ ≤ w' l0.succ - w' l0.castSucc := by
          rw [hinc l0]
          simp only [l0, lt_irrefl, ↓reduceIte, δ]
          linarith [he0 l0]
        obtain ⟨hlt, hge⟩ := hi_spread_reduction_weak M hf hw' hmono' l0 hδ hδw
        refine ⟨hi_reduce M w' l0.succ δ, hlt, fun l => ?_, ?_, ?_⟩
        · rw [hi_reduce_incr, hinc l]
          by_cases hl : l = l0
          · subst hl
            simp only [l0, lt_irrefl, ↓reduceIte, lt_add_one, δ]
            ring
          · have hne : l.val ≠ k := fun h => hl (Fin.ext h)
            have e1 : (l.val < k + 1) ↔ (l.val < k) := by omega
            simp only [hl, ↓reduceIte, sub_zero, e1]
        · rw [hi_reduce_mean, hmean]
        · linarith
      · refine ⟨w', hw', fun l => ?_, hmean, hineq⟩
        have h1 : l.val < k := by have := l.isLt; omega
        have h2 : l.val < k + 1 := by omega
        rw [hinc l]
        simp only [h1, h2, ↓reduceIte]
  obtain ⟨w', h1, h2, h3, h4⟩ := key M.N
  exact ⟨w', h1, fun l => by rw [h2 l]; simp [l.isLt], h3, h4⟩

/-- Under Assumption 22.3.1, `u'` is strictly decreasing. -/
theorem hi_deriv_strictAnti {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') :
    StrictAnti u' :=
  strictAnti_of_deriv_neg fun x => by rw [(hu.2.1 x).deriv]; exact hu.2.2.2.1 x

/-- The tangent line bounds a concave utility: `u(y) ≤ u(x) + u'(x)(y − x)`. -/
theorem hi_tangent {u u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 u u' u'') (x y : ℝ) :
    u y ≤ u x + u' x * (y - x) := by
  have hanti := hi_deriv_strictAnti hu
  have hc : Continuous u := continuous_iff_continuousAt.2 fun z => (hu.1 z).continuousAt
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope u u' hxy hc.continuousOn
      fun z _ => hu.1 z
    have h1 : u' ξ ≤ u' x := (hanti hξ.1).le
    rw [eq_div_iff (by linarith)] at hd
    nlinarith
  · simp
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope u u' hxy hc.continuousOn
      fun z _ => hu.1 z
    have h1 : u' x ≤ u' ξ := (hanti hξ.2).le
    rw [eq_div_iff (by linarith)] at hd
    nlinarith

/-- Miao, p. 793 (the transfer repair): on a set `S` of states on which the transfer is
increasing, replacing it by the single transfer `c̄` with the same expected utility does not raise
the expected transfer, `(Σ_S πⱼ) c̄ ≤ Σ_S πⱼ cⱼ`. -/
theorem hi_pool_cost (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    (S : Finset (Fin (M.N + 1))) (hS : S.Nonempty) (c : Fin (M.N + 1) → ℝ)
    (hc : ∀ j ∈ S, ∀ k ∈ S, j ≤ k → c j ≤ c k) (cb : ℝ)
    (hcb : ∑ j ∈ S, M.prob j * M.u (M.θ j + cb) = ∑ j ∈ S, M.prob j * M.u (M.θ j + c j)) :
    (∑ j ∈ S, M.prob j) * cb ≤ ∑ j ∈ S, M.prob j * c j := by
  set P := ∑ j ∈ S, M.prob j
  have hP : 0 < P := Finset.sum_pos (fun j _ => M.prob_pos j) hS
  set m := (∑ j ∈ S, M.prob j * c j) / P
  set a : Fin (M.N + 1) → ℝ := fun j => u' (M.θ j + m)
  set b : Fin (M.N + 1) → ℝ := fun j => c j - m
  have hB : ∑ j ∈ S, M.prob j * b j = 0 := by
    simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, m]
    field_simp
    ring
  have hanti := hi_deriv_strictAnti hu
  -- Chebyshev: `Σ_S π a b ≤ 0`
  have hterm : ∀ j ∈ S, ∀ k ∈ S, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) ≤ 0 := by
    intro j hj k hk
    have hp : 0 ≤ M.prob j * M.prob k := mul_nonneg (M.prob_pos j).le (M.prob_pos k).le
    refine mul_nonpos_of_nonneg_of_nonpos hp ?_
    rcases le_total j k with hjk | hjk
    · have h1 : a k ≤ a j := hanti.antitone (by linarith [M.θ_strictMono.monotone hjk])
      have h2 : b j ≤ b k := by simp only [b]; linarith [hc j hj k hk hjk]
      nlinarith
    · have h1 : a j ≤ a k := hanti.antitone (by linarith [M.θ_strictMono.monotone hjk])
      have h2 : b k ≤ b j := by simp only [b]; linarith [hc k hk j hj hjk]
      nlinarith
  have hD : ∑ j ∈ S, ∑ k ∈ S, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) =
      2 * P * ∑ j ∈ S, M.prob j * (a j * b j) -
        2 * (∑ j ∈ S, M.prob j * a j) * ∑ j ∈ S, M.prob j * b j := by
    have e : ∀ j k, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) =
        M.prob j * (a j * b j) * M.prob k + M.prob j * (M.prob k * (a k * b k)) -
          M.prob j * a j * (M.prob k * b k) - M.prob j * b j * (M.prob k * a k) :=
      fun j k => by ring
    have h2 : ∑ j ∈ S, ∑ k ∈ S, M.prob j * M.prob k * ((a j - a k) * (b j - b k)) =
        (∑ j ∈ S, M.prob j * (a j * b j)) * (∑ k ∈ S, M.prob k) +
          (∑ j ∈ S, M.prob j) * (∑ k ∈ S, M.prob k * (a k * b k)) -
          (∑ j ∈ S, M.prob j * a j) * (∑ k ∈ S, M.prob k * b k) -
          (∑ j ∈ S, M.prob j * b j) * (∑ k ∈ S, M.prob k * a k) := by
      simp only [Finset.sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => e j k
    rw [h2]
    ring
  have hX : ∑ j ∈ S, M.prob j * (a j * b j) ≤ 0 := by
    have := Finset.sum_nonpos fun j hj => Finset.sum_nonpos fun k hk => hterm j hj k hk
    rw [hD, hB, mul_zero, sub_zero] at this
    nlinarith
  -- tangent lines
  have htan : ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) ≤ ∑ j ∈ S, M.prob j * M.u (M.θ j + m) := by
    have h1 : ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) ≤
        ∑ j ∈ S, (M.prob j * M.u (M.θ j + m) + M.prob j * (a j * b j)) :=
      Finset.sum_le_sum fun j _ => by
        have := hi_tangent hu (M.θ j + m) (M.θ j + c j)
        have e : M.θ j + c j - (M.θ j + m) = b j := by simp only [b]; ring
        rw [e] at this
        have := mul_le_mul_of_nonneg_left this (M.prob_pos j).le
        simp only [a]; linarith
    rw [Finset.sum_add_distrib] at h1
    linarith
  have hcbm : cb ≤ m := by
    by_contra h
    push Not at h
    have : ∑ j ∈ S, M.prob j * M.u (M.θ j + m) < ∑ j ∈ S, M.prob j * M.u (M.θ j + cb) :=
      Finset.sum_lt_sum_of_nonempty hS fun j _ =>
        mul_lt_mul_of_pos_left (M.u_strictMono (by linarith)) (M.prob_pos j)
    linarith
  have : P * m = ∑ j ∈ S, M.prob j * c j := by simp only [m]; field_simp
  nlinarith

/-- The number of steps of a contract: the pairs of adjacent states with different terms. -/
noncomputable def hi_steps (M : HIModel) (c w : Fin (M.N + 1) → ℝ) : ℕ :=
  (Finset.univ.filter fun l : Fin M.N => c l.succ ≠ c l.castSucc ∨ w l.succ ≠ w l.castSucc).card

/-- Miao, p. 793 (the transfer repair). If the local downward constraints hold, `w` is monotone,
and some pair has `wᵢ₋₁ = wᵢ` and `cᵢ₋₁ < cᵢ`, then pooling the transfers of all states sharing
that continuation value (keeping their expected utility) keeps the local downward constraints and
the agent's value, does not lower the principal's value, and lowers the number of steps. -/
theorem hi_pool (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    (f : ℝ → ℝ) {c w : Fin (M.N + 1) → ℝ}
    (hloc : ∀ l : Fin M.N, 0 ≤ hi_C M c w l.succ l.castSucc) (hmono : Monotone w)
    (l0 : Fin M.N) (hweq : w l0.succ = w l0.castSucc) (hclt : c l0.castSucc < c l0.succ) :
    ∃ c' : Fin (M.N + 1) → ℝ, (∀ l : Fin M.N, 0 ≤ hi_C M c' w l.succ l.castSucc) ∧
      hi_agentValue M c' w = hi_agentValue M c w ∧
      hi_principalValue M f c w ≤ hi_principalValue M f c' w ∧
      hi_steps M c' w < hi_steps M c w := by
  classical
  set w0 := w l0.succ
  set S := Finset.univ.filter fun j => w j = w0
  have hmemS : ∀ j, j ∈ S ↔ w j = w0 := fun j => by simp [S]
  have hS : S.Nonempty := ⟨l0.succ, (hmemS _).2 rfl⟩
  have hpair : ∀ l : Fin M.N, w l.succ = w l.castSucc → c l.castSucc ≤ c l.succ := by
    intro l hl
    have h := hloc l
    unfold hi_C at h
    rw [hl] at h
    have : M.u (M.θ l.succ + c l.castSucc) ≤ M.u (M.θ l.succ + c l.succ) := by linarith
    have := M.u_strictMono.le_iff_le.1 this
    linarith
  have hinter : ∀ j k m, j ∈ S → k ∈ S → j ≤ m → m ≤ k → m ∈ S := by
    intro j k m hj hk hjm hmk
    rw [hmemS] at hj hk ⊢
    exact le_antisymm (by rw [← hk]; exact hmono hmk) (by rw [← hj]; exact hmono hjm)
  have hcS : ∀ j ∈ S, ∀ k ∈ S, j ≤ k → c j ≤ c k := by
    have key : ∀ d : ℕ, ∀ j k : Fin (M.N + 1), k.val = j.val + d → j ∈ S → k ∈ S →
        c j ≤ c k := by
      intro d
      induction d with
      | zero =>
        intro j k h _ _
        have : j = k := Fin.ext (by omega)
        rw [this]
      | succ d ih =>
        intro j k h hj hk
        have hm : j.val + d < M.N := by omega
        set m : Fin M.N := ⟨j.val + d, hm⟩
        have hmS : m.castSucc ∈ S := hinter j k _ hj hk (Fin.le_def.2 (by simp [m]))
          (Fin.le_def.2 (by simp [m]; omega))
        have hks : m.succ = k := Fin.ext (by simp [m]; omega)
        have h1 := ih j m.castSucc (by simp [m]) hj hmS
        have hw : w m.succ = w m.castSucc := by
          rw [hks, (hmemS _).1 hk, (hmemS _).1 hmS]
        have h2 := hpair m hw
        rw [hks] at h2
        linarith
    intro j hj k hk hjk
    exact key (k.val - j.val) j k (by have := Fin.le_def.1 hjk; omega) hj hk
  obtain ⟨jlo, hjlo, hlo⟩ := S.exists_min_image c hS
  obtain ⟨jhi, hjhi, hhi⟩ := S.exists_max_image c hS
  set g : ℝ → ℝ := fun x => ∑ j ∈ S, M.prob j * M.u (M.θ j + x)
  have hg : Continuous g := continuous_finsetSum _ fun j _ =>
    continuous_const.mul (M.u_cont.comp (continuous_const.add continuous_id))
  have hgT1 : g (c jlo) ≤ ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (M.u_strictMono.monotone (by linarith [hlo j hj])) (M.prob_pos j).le
  have hgT2 : ∑ j ∈ S, M.prob j * M.u (M.θ j + c j) ≤ g (c jhi) :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (M.u_strictMono.monotone (by linarith [hhi j hj])) (M.prob_pos j).le
  obtain ⟨cb, ⟨hcb1, hcb2⟩, hcb⟩ :=
    intermediate_value_Icc (hlo jhi hjhi) hg.continuousOn ⟨hgT1, hgT2⟩
  set c' : Fin (M.N + 1) → ℝ := fun j => if j ∈ S then cb else c j
  -- sums against `c'`
  have hsplit : ∀ F : Fin (M.N + 1) → ℝ → ℝ,
      ∑ j, F j (c' j) = ∑ j, F j (c j) + ∑ j ∈ S, (F j cb - F j (c j)) := by
    intro F
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c', hmemS]
    split_ifs <;> ring
  refine ⟨c', fun l => ?_, ?_, ?_, ?_⟩
  · have h0 := hloc l
    unfold hi_C at h0 ⊢
    simp only [c']
    by_cases hsS : l.succ ∈ S <;> by_cases htS : l.castSucc ∈ S
    · simp only [hsS, htS, ↓reduceIte]
      rw [(hmemS _).1 hsS, (hmemS _).1 htS]
      linarith
    · simp only [hsS, htS, ↓reduceIte]
      have hmin : c l.succ ≤ cb := by
        have : l.succ ≤ jlo := by
          by_contra hlt
          push Not at hlt
          exact htS (hinter jlo l.succ l.castSucc hjlo hsS (Fin.le_castSucc_iff.2 hlt)
            Fin.castSucc_lt_succ.le)
        linarith [hcS _ hsS _ hjlo this]
      have := M.u_strictMono.monotone
        (show M.θ l.succ + c l.succ ≤ M.θ l.succ + cb by linarith)
      linarith
    · simp only [hsS, htS, ↓reduceIte]
      have hmax : cb ≤ c l.castSucc := by
        have : jhi ≤ l.castSucc := by
          by_contra hlt
          push Not at hlt
          have h1 : l.succ ≤ jhi := Fin.le_def.2 (by
            have := Fin.lt_def.1 hlt; simp only [Fin.val_castSucc] at this
            simp only [Fin.val_succ]; omega)
          exact hsS (hinter l.castSucc jhi l.succ htS hjhi Fin.castSucc_lt_succ.le h1)
        linarith [hcS _ hjhi _ htS this]
      have := M.u_strictMono.monotone
        (show M.θ l.succ + cb ≤ M.θ l.succ + c l.castSucc by linarith)
      linarith
    · simp only [hsS, htS, ↓reduceIte]
      exact h0
  · unfold hi_agentValue
    rw [hsplit fun j x => M.prob j * (M.u (M.θ j + x) + M.β * w j)]
    have : ∑ j ∈ S, (M.prob j * (M.u (M.θ j + cb) + M.β * w j) -
        M.prob j * (M.u (M.θ j + c j) + M.β * w j)) = 0 := by
      rw [← sub_eq_zero.2 hcb, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, add_zero]
  · unfold hi_principalValue
    rw [hsplit fun j x => M.prob j * (-x + M.β * f (w j))]
    have hcost := hi_pool_cost M hu S hS c (fun j hj k hk hjk => hcS j hj k hk hjk) cb hcb
    have : ∑ j ∈ S, (M.prob j * (-cb + M.β * f (w j)) - M.prob j * (-c j + M.β * f (w j))) =
        ∑ j ∈ S, M.prob j * c j - (∑ j ∈ S, M.prob j) * cb := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    linarith
  · unfold hi_steps
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨l0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl hclt.ne'
      · have hs0 : l0.succ ∈ S := (hmemS _).2 rfl
        have ht0 : l0.castSucc ∈ S := (hmemS _).2 hweq.symm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not]
        exact ⟨by simp only [c', hs0, ht0, ↓reduceIte], hweq⟩
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      by_cases hw : w l.succ = w l.castSucc
      · left
        rcases hl with hl | hl
        · by_cases hsS : l.succ ∈ S
          · have htS : l.castSucc ∈ S := (hmemS _).2 (hw.symm.trans ((hmemS _).1 hsS))
            exact absurd (by simp only [c', hsS, htS, ↓reduceIte]) hl
          · have htS : l.castSucc ∉ S := fun h => hsS ((hmemS _).2 (hw.trans ((hmemS _).1 h)))
            simpa only [c', hsS, htS, ↓reduceIte] using hl
        · exact absurd hw hl
      · exact Or.inr hw

/-- Miao, pp. 792–793: a contract satisfying the local downward constraints with monotone
continuation values can be repaired into an incentive-compatible contract, with every local
downward constraint binding, the same promised value and a weakly higher value to the
principal, against any continuation `f` that is concave on `(−∞, vmax)`. -/
theorem hi_repair (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) (c w : Fin (M.N + 1) → ℝ)
    (hloc : ∀ l : Fin M.N, 0 ≤ hi_C M c w l.succ l.castSucc) (hmono : Monotone w)
    (hw : ∀ j, w j < hi_vmax M) :
    ∃ c' w' : Fin (M.N + 1) → ℝ, hi_IC M c' w' ∧ hi_agentValue M c' w' = hi_agentValue M c w ∧
      (∀ j, w' j < hi_vmax M) ∧ hi_principalValue M f c w ≤ hi_principalValue M f c' w' ∧
      ∀ l : Fin M.N, hi_C M c' w' l.succ l.castSucc = 0 := by
  suffices h : ∀ s, ∀ c w : Fin (M.N + 1) → ℝ, hi_steps M c w = s →
      (∀ l : Fin M.N, 0 ≤ hi_C M c w l.succ l.castSucc) → Monotone w →
      (∀ j, w j < hi_vmax M) →
      ∃ c' w' : Fin (M.N + 1) → ℝ, hi_IC M c' w' ∧
        hi_agentValue M c' w' = hi_agentValue M c w ∧ (∀ j, w' j < hi_vmax M) ∧
        hi_principalValue M f c w ≤ hi_principalValue M f c' w' ∧
        ∀ l : Fin M.N, hi_C M c' w' l.succ l.castSucc = 0 from
    h _ c w rfl hloc hmono hw
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro c w hs hloc hmono hw
  set D : Fin M.N → ℝ := fun l =>
    (M.u (M.θ l.succ + c l.castSucc) - M.u (M.θ l.succ + c l.succ)) / M.β
  set e : Fin M.N → ℝ := fun l => max (D l) 0
  have hβD : ∀ l, M.β * D l =
      M.u (M.θ l.succ + c l.castSucc) - M.u (M.θ l.succ + c l.succ) := fun l => by
    have hβ := M.β_pos.ne'
    simp only [D]; field_simp
  have hincr : ∀ l, D l ≤ w l.succ - w l.castSucc := fun l => by
    have h1 := hloc l
    unfold hi_C at h1
    have h2 := hβD l
    have : M.β * D l ≤ M.β * (w l.succ - w l.castSucc) := by linarith
    exact le_of_mul_le_mul_left this M.β_pos
  have hle : ∀ l, e l ≤ w l.succ - w l.castSucc := fun l =>
    max_le (hincr l) (by linarith [hmono (Fin.castSucc_lt_succ : l.castSucc < l.succ).le])
  obtain ⟨w', hw', hinc', hmean, hineq⟩ :=
    hi_adjust_increments M hf hw e (fun l => le_max_right _ _) hle
  have hC' : ∀ l : Fin M.N, hi_C M c w' l.succ l.castSucc = M.β * (e l - D l) := fun l => by
    unfold hi_C
    linear_combination M.β * hinc' l + hβD l
  have hloc' : ∀ l : Fin M.N, 0 ≤ hi_C M c w' l.succ l.castSucc := fun l => by
    rw [hC']
    exact mul_nonneg M.β_pos.le (by simp only [e]; linarith [le_max_left (D l) 0])
  have hmono' : Monotone w' :=
    Fin.monotone_iff_le_succ.2 fun l => by linarith [hinc' l, le_max_right (D l) 0]
  have hagent : hi_agentValue M c w' = hi_agentValue M c w := by
    unfold hi_agentValue
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [hi_sum_mul_left M M.β w', hi_sum_mul_left M M.β w, hmean]
  have hpv : hi_principalValue M f c w ≤ hi_principalValue M f c w' := by
    unfold hi_principalValue
    simp only [mul_add, Finset.sum_add_distrib, add_le_add_iff_left]
    rw [hi_sum_mul_left M M.β (fun j => f (w j)), hi_sum_mul_left M M.β (fun j => f (w' j))]
    exact mul_le_mul_of_nonneg_left hineq M.β_pos.le
  have hsteps : hi_steps M c w' ≤ hi_steps M c w := by
    unfold hi_steps
    apply Finset.card_le_card
    intro l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    by_contra hn
    push Not at hn
    have hD0 : D l = 0 := by simp only [D, hn.1, sub_self, zero_div]
    have : w' l.succ = w' l.castSucc := by
      have := hinc' l
      simp only [e, hD0, max_self] at this
      linarith
    rcases h with h | h
    · exact h hn.1
    · exact h this
  by_cases hall : ∀ l : Fin M.N, c l.succ ≤ c l.castSucc
  · have hbind : ∀ l : Fin M.N, hi_C M c w' l.succ l.castSucc = 0 := fun l => by
      rw [hC']
      have h0 : 0 ≤ D l := by
        have := M.u_strictMono.monotone
          (show M.θ l.succ + c l.succ ≤ M.θ l.succ + c l.castSucc by linarith [hall l])
        have h2 := hβD l
        have : 0 ≤ M.β * D l := by linarith
        exact nonneg_of_mul_nonneg_right (by linarith) M.β_pos
      simp only [e, max_eq_left h0, sub_self, mul_zero]
    have hIC : hi_IC M c w' := lemma_22_3_2 M c w' fun l =>
      ⟨(hbind l).ge, (hi_upward_of_binding M c w' Fin.castSucc_lt_succ (hbind l) (hall l)).1⟩
    exact ⟨c, w', hIC, hagent, hw', hpv, hbind⟩
  · push Not at hall
    obtain ⟨l0, hl0⟩ := hall
    have hD : D l0 < 0 := by
      have := M.u_strictMono
        (show M.θ l0.succ + c l0.castSucc < M.θ l0.succ + c l0.succ by linarith)
      have h2 := hβD l0
      have : M.β * D l0 < 0 := by linarith
      by_contra h
      push Not at h
      linarith [mul_nonneg M.β_pos.le h]
    have hweq : w' l0.succ = w' l0.castSucc := by
      have := hinc' l0
      simp only [e, max_eq_right hD.le] at this
      linarith
    obtain ⟨c'', hloc'', hag'', hpv'', hst''⟩ := hi_pool M hu f hloc' hmono' l0 hweq hl0
    obtain ⟨c3, w3, hIC3, hag3, hw3, hpv3, hb3⟩ :=
      ih (hi_steps M c'' w') (by omega) c'' w' rfl hloc'' hmono' hw'
    exact ⟨c3, w3, hIC3, by rw [hag3, hag'', hagent], hw3, by linarith, hb3⟩

/-- Miao, pp. 792–793: for contracts feasible at `v⁰` and `v¹` and `δ ∈ (0, 1)`, there is an
incentive-compatible contract at `δv⁰ + (1 − δ)v¹` giving the principal at least the average of
their values, against a continuation concave on `(−∞, vmax)`. -/
theorem hi_mix_repair (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {v0 v1 : ℝ} {c0 w0 c1 w1 : Fin (M.N + 1) → ℝ} (h0 : hi_Feasible M v0 c0 w0)
    (h1 : hi_Feasible M v1 c1 w1) :
    ∃ c w, hi_Feasible M (δ * v0 + (1 - δ) * v1) c w ∧
      δ * hi_principalValue M f c0 w0 + (1 - δ) * hi_principalValue M f c1 w1 ≤
        hi_principalValue M f c w := by
  obtain ⟨cs, hcs⟩ := hi_exists_mix M hδ0.le hδ1.le c0 c1
  set ws : Fin (M.N + 1) → ℝ := fun i => δ * w0 i + (1 - δ) * w1 i
  have hloc : ∀ l : Fin M.N, 0 ≤ hi_C M cs ws l.succ l.castSucc := fun l =>
    hi_mix_downward M hu hδ0 hδ1 hcs Fin.castSucc_lt_succ.le (h0.1 _ _) (h1.1 _ _)
  have hm0 := (lemma_22_3_1 M c0 w0 h0.1).2
  have hm1 := (lemma_22_3_1 M c1 w1 h1.1).2
  have hmono : Monotone ws := fun i j hij => by
    simp only [ws]
    nlinarith [hm0 hij, hm1 hij]
  have hws : ∀ j, ws j < hi_vmax M := fun j => by
    simp only [ws]
    nlinarith [h0.2.2 j, h1.2.2 j]
  obtain ⟨c, w, hIC, hag, hw, hpv, -⟩ := hi_repair M hu hf cs ws hloc hmono hws
  refine ⟨c, w, ⟨hIC, ?_, hw⟩, ?_⟩
  · rw [hag, hi_mix_agentValue M hcs, h0.2.1, h1.2.1]
  · exact (hi_mix_principal_ge M hδ0.le hδ1.le hf hcs h0.2.2 h1.2.2).trans hpv

/-- **Proposition 22.3.1** (Miao, pp. 792–793), the induction step: under Assumption 22.3.1 the
Bellman operator maps a function in `F` that is concave on `(−∞, vmax)` to a concave function. -/
theorem hi_T_concaveOn (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    {f : ℝ → ℝ} (hF : hi_InF M f) (hf : ConcaveOn ℝ (Set.Iio (hi_vmax M)) f) :
    ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_T M f) := by
  refine ⟨convex_Iio _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hfU : ∀ w < hi_vmax M, f w ≤ hi_U M w := fun w hw => (hF w hw).2
  rcases ha.lt_or_eq with ha | ha
  swap
  · subst ha; simp only [zero_add] at hab; subst hab; simp
  rcases hb.lt_or_eq with hb | hb
  swap
  · subst hb; simp only [add_zero] at hab; subst hab; simp
  have hb' : b = 1 - a := by linarith
  have hxy : a * x + b * y < hi_vmax M := by
    have : a * x + b * y < a * hi_vmax M + b * hi_vmax M := by
      have := mul_lt_mul_of_pos_left (show x < hi_vmax M from hx) ha
      have := mul_lt_mul_of_pos_left (show y < hi_vmax M from hy) hb
      linarith
    rwa [← add_mul, hab, one_mul] at this
  have key : ∀ x0 ∈ hi_vals M f x, ∀ x1 ∈ hi_vals M f y,
      a * x0 + b * x1 ≤ hi_T M f (a * x + b * y) := by
    rintro _ ⟨c0, w0, h0, rfl⟩ _ ⟨c1, w1, h1, rfl⟩
    obtain ⟨c, w, hfeas, hle⟩ := hi_mix_repair M hu hf ha (by linarith) h0 h1
    rw [← hb'] at hfeas hle
    exact hle.trans (hi_le_T M hfU hfeas)
  have step : ∀ x0 ∈ hi_vals M f x, a * x0 + b * hi_T M f y ≤ hi_T M f (a * x + b * y) := by
    intro x0 hx0
    have : hi_T M f y ≤ (hi_T M f (a * x + b * y) - a * x0) / b := by
      refine csSup_le (hi_vals_nonempty M f hy) fun x1 hx1 => ?_
      rw [le_div_iff₀ hb]
      linarith [key x0 hx0 x1 hx1]
    rw [le_div_iff₀ hb] at this
    linarith
  have : hi_T M f x ≤ (hi_T M f (a * x + b * y) - b * hi_T M f y) / a := by
    refine csSup_le (hi_vals_nonempty M f hx) fun x0 hx0 => ?_
    rw [le_div_iff₀ ha]
    linarith [step x0 hx0]
  rw [le_div_iff₀ ha] at this
  linarith

/-- The lower bound `L(v) = −b(v)/(1 − β)` is concave: `b` inverts the concave increasing map
`b ↦ Σ πᵢ u(θᵢ + b)`. -/
theorem hi_L_concaveOn (M : HIModel) : ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_L M) := by
  refine ⟨convex_Iio _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hxy : a * x + b * y < hi_vmax M := by
    have := (convex_Iio (hi_vmax M)) hx hy ha hb hab
    simpa only [smul_eq_mul, Set.mem_Iio] using this
  have hB : a * hi_Bfun M (hi_b M x) + b * hi_Bfun M (hi_b M y) ≤
      hi_Bfun M (a * hi_b M x + b * hi_b M y) := by
    unfold hi_Bfun
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := M.u_strictConcave.concaveOn.2 (Set.mem_univ (M.θ i + hi_b M x))
      (Set.mem_univ (M.θ i + hi_b M y)) ha hb hab
    simp only [smul_eq_mul] at this
    have e : a * (M.θ i + hi_b M x) + b * (M.θ i + hi_b M y) =
        M.θ i + (a * hi_b M x + b * hi_b M y) := by
      rw [show a * (M.θ i + hi_b M x) + b * (M.θ i + hi_b M y) =
        (a + b) * M.θ i + (a * hi_b M x + b * hi_b M y) by ring, hab, one_mul]
    rw [e] at this
    nlinarith [M.prob_pos i]
  rw [hi_b_spec M hx, hi_b_spec M hy] at hB
  have hb_le : hi_b M (a * x + b * y) ≤ a * hi_b M x + b * hi_b M y := by
    rw [← (hi_Bfun_strictMono M).le_iff_le, hi_b_spec M hxy]
    linarith [show (1 - M.β) * (a * x + b * y) = a * ((1 - M.β) * x) + b * ((1 - M.β) * y) by
      ring]
  unfold hi_L
  have key : a * (-hi_b M x / (1 - M.β)) + b * (-hi_b M y / (1 - M.β)) =
      -(a * hi_b M x + b * hi_b M y) / (1 - M.β) := by ring
  rw [key]
  exact div_le_div_of_nonneg_right (by linarith) h1β.le

/-- The iterates `Pₖ = Tᵏ L` are concave under Assumption 22.3.1. -/
theorem hi_Pk_concaveOn (M : HIModel) {u' u'' : ℝ → ℝ} (hu : assumption_22_3_1 M.u u' u'')
    (k : ℕ) : ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_Pk M k) := by
  induction k with
  | zero => exact hi_L_concaveOn M
  | succ k ih =>
    have e : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    rw [e]
    exact hi_T_concaveOn M hu (hi_Pk_InF M k) ih

/-- **Proposition 22.3.1** (Miao, p. 791), concavity: under Assumption 22.3.1 the value function
`P = lim Tᵏ L` is concave on `(−∞, vmax)`. -/
theorem proposition_22_3_1_concave (M : HIModel) {u' u'' : ℝ → ℝ}
    (hu : assumption_22_3_1 M.u u' u'') : ConcaveOn ℝ (Set.Iio (hi_vmax M)) (hi_P M) :=
  hi_concaveOn_of_tendsto (fun k => hi_Pk_concaveOn M hu k) fun _ hx => hi_Pk_tendsto M hx

/-- Miao, p. 794, Proposition 22.3.2 from concavity alone: under Assumption 22.3.1 (without
Assumption 22.3.2), whenever an optimal contract exists at `v` there is an optimal contract at `v`
in which every local downward constraint binds and every local upward constraint holds. -/
theorem hi_proposition_22_3_2_concave (M : HIModel) {u' u'' : ℝ → ℝ}
    (hu : assumption_22_3_1 M.u u' u'') {v : ℝ} {c w : Fin (M.N + 1) → ℝ}
    (hopt : hi_Optimal M (hi_P M) v c w) :
    ∃ c' w', hi_Optimal M (hi_P M) v c' w' ∧
      ∀ l : Fin M.N, hi_C M c' w' l.succ l.castSucc = 0 ∧ 0 ≤ hi_C M c' w' l.castSucc l.succ := by
  obtain ⟨⟨hic, hpk, hw⟩, hbest⟩ := hopt
  obtain ⟨c', w', hIC, hag, hw', hpv, hbind⟩ := hi_repair M hu (proposition_22_3_1_concave M hu)
    c w (fun l => hic _ _) (lemma_22_3_1 M c w hic).2 hw
  refine ⟨c', w', ⟨⟨hIC, hag.trans hpk, hw'⟩, fun c'' w'' h => (hbest c'' w'' h).trans hpv⟩,
    fun l => ⟨hbind l, hIC _ _⟩⟩

end Miao.RecursiveContracts
