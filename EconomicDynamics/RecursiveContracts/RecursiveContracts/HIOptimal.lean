/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HIBellman
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv

/-!
# Optimal contracts: Propositions 22.3.2–22.3.3, (22.27)–(22.30), Lemma 22.3.3

Miao, §22.3.1–22.3.2, pp. 794–796.

* `assumption_22_3_2` (Assumption 22.3.2): the value function is strictly concave on
  `(−∞, vmax)`. `hi_Optimal M f v c w`: `(c, w)` attains the supremum in (22.23) against the
  continuation `f`.
* `hi_spread_reduction`: the "mean-preserving decrease in the spread" of the proofs of
  Propositions 22.3.1 and 22.3.2. Lowering the increment `w_k − w_{k−1}` of a monotone list of
  continuation values by `δ ≤ w_k − w_{k−1}` and adding the constant that keeps `Σ πᵢ wᵢ` raises
  `Σ πᵢ f(wᵢ)` strictly for a strictly concave `f`.
* `proposition_22_3_2`: in an optimal contract against a strictly concave continuation the local
  downward constraints bind; the local upward constraints then hold, and are slack whenever
  `cᵢ < cᵢ₋₁` (the book's "never bind"; see `docs/HI-corrections.md`).
* `proposition_22_3_3`: coinsurance, `u(θᵢ + cᵢ) + βwᵢ > u(θᵢ₋₁ + cᵢ₋₁) + βwᵢ₋₁` and
  `−cᵢ + βf(wᵢ) ≥ −cᵢ₋₁ + βf(wᵢ₋₁)`.
* `hi_FOC` collects the first-order conditions (22.27)–(22.29) (stated, as in the book, for given
  multipliers `λ`, `μᵢ`); `eq_22_30` derives the martingale property `Σ πᵢ P'(wᵢ) = P'(v)` from
  (22.28)–(22.29) by summing, and `hi_martingale_of_shift` proves (22.30) without multipliers by
  the argument on p. 796 (shift every `wᵢ` and use the envelope theorem).
* `lemma_22_3_3`: `w₁ < v < wₙ` (for `n ≥ 2`), from the first-order conditions, as in the book.
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- **Assumption 22.3.2** (Miao, p. 794). The value function `P` is strictly concave on
`(−∞, vmax)`. -/
def assumption_22_3_2 (M : HIModel) (P : ℝ → ℝ) : Prop :=
  StrictConcaveOn ℝ (Set.Iio (hi_vmax M)) P

/-- `(c, w)` is an optimal contract at `v` against the continuation `f`: it is feasible and no
feasible contract gives the principal more. -/
def hi_Optimal (M : HIModel) (f : ℝ → ℝ) (v : ℝ) (c w : Fin (M.N + 1) → ℝ) : Prop :=
  hi_Feasible M v c w ∧
    ∀ c' w', hi_Feasible M v c' w' → hi_principalValue M f c' w' ≤ hi_principalValue M f c w

/-- A strictly concave function on a convex set has decreasing increments there. -/
theorem hi_incr_le_on {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictConcaveOn ℝ s f) {x y d : ℝ}
    (hx : x ∈ s) (hyd : y + d ∈ s) (hxy : x ≤ y) (hd : 0 ≤ d) :
    f (y + d) - f y ≤ f (x + d) - f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · rcases hd.lt_or_eq with hd | rfl
    · have hoc := hf.1.ordConnected
      have hy : y ∈ s := hoc.out hx hyd ⟨hxy.le, by linarith⟩
      have hxd : x + d ∈ s := hoc.out hx hyd ⟨by linarith, by linarith⟩
      have h1 := hf.secant_strict_mono (a := x) (x := x + d) (y := y + d) hx hxd hyd
        (by linarith) (by linarith) (by linarith)
      have h2 := hf.secant_strict_mono (a := y + d) (x := x) (y := y) hyd hx hy
        (by linarith) (by linarith) hxy
      have e1 : (f (x + d) - f x) / (x + d - x) = (f (x + d) - f x) / d := by ring_nf
      have e2 : (f y - f (y + d)) / (y - (y + d)) = (f (y + d) - f y) / d := by
        rw [show y - (y + d) = -d by ring, div_neg, ← neg_div]; ring
      have e3 : (f x - f (y + d)) / (x - (y + d)) = (f (y + d) - f x) / (y + d - x) := by
        rw [show x - (y + d) = -(y + d - x) by ring, div_neg, ← neg_div]; ring
      rw [e1] at h1
      rw [e2, e3] at h2
      exact ((div_lt_div_iff_of_pos_right hd).1 (h2.trans h1)).le
    · simp
  · exact le_rfl

/-- For a strictly concave function, the slope on `[x₁, x₂]` exceeds the slope on `[x₃, x₄]`
when `x₁ < x₂ ≤ x₃ < x₄`. -/
theorem hi_slope_strict_anti {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictConcaveOn ℝ s f)
    {x1 x2 x3 x4 : ℝ} (h1 : x1 ∈ s) (h4 : x4 ∈ s) (h12 : x1 < x2) (h23 : x2 ≤ x3)
    (h34 : x3 < x4) :
    (f x4 - f x3) / (x4 - x3) < (f x2 - f x1) / (x2 - x1) := by
  have hoc := hf.1.ordConnected
  rcases h23.lt_or_eq with h23 | rfl
  · have hx2 : x2 ∈ s := hoc.out h1 h4 ⟨h12.le, by linarith⟩
    have a := hf.slope_anti_adjacent h1 (hoc.out h1 h4 ⟨by linarith, by linarith⟩) h12 h23
    have b := hf.slope_anti_adjacent hx2 h4 h23 h34
    linarith
  · exact hf.slope_anti_adjacent h1 h4 h12 h34

/-- The probability mass `q = Σ_{j ≥ k} πⱼ` of the states at or above `k`. -/
noncomputable def hi_upperMass (M : HIModel) (k : Fin (M.N + 1)) : ℝ :=
  ∑ j, M.prob j * (if k ≤ j then 1 else 0)

/-- `0 < q < 1` when `k` is not the lowest state. -/
theorem hi_upperMass_bounds (M : HIModel) (i : Fin M.N) :
    0 < hi_upperMass M i.succ ∧ hi_upperMass M i.succ < 1 := by
  constructor
  · have := Finset.single_le_sum (f := fun j => M.prob j * (if i.succ ≤ j then (1 : ℝ) else 0))
      (fun j _ => by split_ifs <;> simp [(M.prob_pos j).le]) (Finset.mem_univ i.succ)
    simp only [le_refl, ↓reduceIte, mul_one] at this
    exact lt_of_lt_of_le (M.prob_pos _) this
  · have e : 1 - hi_upperMass M i.succ = ∑ j, M.prob j * (if i.succ ≤ j then 0 else 1) := by
      have h : ∑ j, M.prob j * (if i.succ ≤ j then (0 : ℝ) else 1) + hi_upperMass M i.succ = 1 := by
        unfold hi_upperMass
        rw [← Finset.sum_add_distrib]
        convert M.prob_sum using 1
        exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
      linarith
    have := Finset.single_le_sum (f := fun j => M.prob j * (if i.succ ≤ j then (0 : ℝ) else 1))
      (fun j _ => by split_ifs <;> simp [(M.prob_pos j).le]) (Finset.mem_univ i.castSucc)
    have hn : ¬ i.succ ≤ i.castSucc := not_le.2 Fin.castSucc_lt_succ
    simp only [hn, ↓reduceIte, mul_one] at this
    linarith [M.prob_pos i.castSucc]

/-- The spread-reduced continuation values: `w'ⱼ = wⱼ + δq − δ·1{k ≤ j}`. -/
noncomputable def hi_reduce (M : HIModel) (w : Fin (M.N + 1) → ℝ) (k : Fin (M.N + 1))
    (δ : ℝ) (j : Fin (M.N + 1)) : ℝ :=
  w j + δ * hi_upperMass M k - (if k ≤ j then δ else 0)

/-- The spread reduction keeps the mean `Σ πⱼ wⱼ`. -/
theorem hi_reduce_mean (M : HIModel) (w : Fin (M.N + 1) → ℝ) (k : Fin (M.N + 1)) (δ : ℝ) :
    ∑ j, M.prob j * hi_reduce M w k δ j = ∑ j, M.prob j * w j := by
  unfold hi_reduce
  have : ∀ j, M.prob j * (w j + δ * hi_upperMass M k - (if k ≤ j then δ else 0)) =
      M.prob j * w j + M.prob j * (δ * hi_upperMass M k) -
        δ * (M.prob j * (if k ≤ j then 1 else 0)) := fun j => by split_ifs <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, hi_sum_const,
    ← Finset.mul_sum]
  unfold hi_upperMass
  ring

/-- Miao, pp. 793–794: the mean-preserving decrease in the spread. If `w` is monotone with
values in `(−∞, vmax)`, `k = i + 1` and `0 < δ ≤ w_k − w_{k−1}`, then the spread-reduced values
lie in `(−∞, vmax)` and `Σ πⱼ f(w'ⱼ) > Σ πⱼ f(wⱼ)` for `f` strictly concave on `(−∞, vmax)`. -/
theorem hi_spread_reduction (M : HIModel) {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ (Set.Iio (hi_vmax M)) f) {w : Fin (M.N + 1) → ℝ}
    (hw : ∀ j, w j < hi_vmax M) (hmono : Monotone w) (i : Fin M.N) {δ : ℝ} (hδ : 0 < δ)
    (hδw : δ ≤ w i.succ - w i.castSucc) :
    (∀ j, hi_reduce M w i.succ δ j < hi_vmax M) ∧
      ∑ j, M.prob j * f (w j) < ∑ j, M.prob j * f (hi_reduce M w i.succ δ j) := by
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
  -- position of each state relative to the reduced increment
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
  -- the gains below and the losses above
  set gainL := f (a + δ * q) - f a
  set lossU := f b - f (b - e)
  have hterm : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) ≤
      M.prob j * (f (hi_reduce M w i.succ δ j) - f (w j)) := fun j => by
    refine mul_le_mul_of_nonneg_left ?_ (M.prob_pos j).le
    rw [hred j]
    split_ifs with hj
    · have := hi_incr_le_on hf (x := b - e) (y := w j - e) (d := e)
        (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith [hw j])
        (by linarith [hhigh j hj]) he.le
      simp only [sub_add_cancel] at this
      simp only [lossU]; linarith
    · have := hi_incr_le_on hf (x := w j) (y := a) (d := δ * q)
        (by simp only [Set.mem_Iio]; linarith [hw j]) (by simp only [Set.mem_Iio]; linarith)
        (hlow j hj) hdq.le
      simp only [gainL]; linarith
  have hsum : ∑ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
      gainL - (gainL + lossU) * q := by
    have : ∀ j, M.prob j * (if i.succ ≤ j then -lossU else gainL) =
        M.prob j * gainL - (gainL + lossU) * (M.prob j * (if i.succ ≤ j then 1 else 0)) :=
        fun j => by
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hi_sum_const, ← Finset.mul_sum]
    rfl
  -- strict concavity: the slope below beats the slope above
  have hslope := hi_slope_strict_anti hf (x1 := a) (x2 := a + δ * q) (x3 := b - e) (x4 := b)
    (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith)
    (by linarith) hab (by linarith)
  rw [show b - (b - e) = e by ring, show a + δ * q - a = δ * q by ring,
    div_lt_div_iff₀ he hdq] at hslope
  have hpos : 0 < gainL - (gainL + lossU) * q := by
    have h3 : lossU * (δ * q) < gainL * (δ * (1 - q)) := hslope
    have : δ * (gainL - (gainL + lossU) * q) = gainL * (δ * (1 - q)) - lossU * (δ * q) := by ring
    have h4 : 0 < δ * (gainL - (gainL + lossU) * q) := by linarith
    exact pos_of_mul_pos_right h4 hδ.le
  have htot := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  rw [hsum] at htot
  simp only [mul_sub, Finset.sum_sub_distrib] at htot
  linarith

/-- `Σ πⱼ (a xⱼ) = a Σ πⱼ xⱼ`. -/
theorem hi_sum_mul_left (M : HIModel) (a : ℝ) (x : Fin (M.N + 1) → ℝ) :
    ∑ j, M.prob j * (a * x j) = a * ∑ j, M.prob j * x j := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

/-- **Proposition 22.3.2** (Miao, p. 794). In an optimal contract against a strictly concave
continuation (Assumption 22.3.2 for `f = P`), the local downward incentive constraints bind,
`Cᵢ,ᵢ₋₁ = 0`. Consequently the local upward constraints `Cᵢ₋₁,ᵢ ≥ 0` hold, and they are slack
(`Cᵢ₋₁,ᵢ > 0`) whenever `cᵢ < cᵢ₋₁`. -/
theorem proposition_22_3_2 (M : HIModel) {f : ℝ → ℝ} (hf : assumption_22_3_2 M f) {v : ℝ}
    {c w : Fin (M.N + 1) → ℝ} (hopt : hi_Optimal M f v c w) (i : Fin M.N) :
    hi_C M c w i.succ i.castSucc = 0 ∧ 0 ≤ hi_C M c w i.castSucc i.succ ∧
      (c i.succ < c i.castSucc → 0 < hi_C M c w i.castSucc i.succ) := by
  obtain ⟨⟨hic, hpk, hw⟩, hbest⟩ := hopt
  obtain ⟨hcm, hwm⟩ := lemma_22_3_1 M c w hic
  have hci : c i.succ ≤ c i.castSucc := hcm (Fin.castSucc_lt_succ).le
  have hbind : hi_C M c w i.succ i.castSucc = 0 := by
    by_contra hne
    have hCpos : 0 < hi_C M c w i.succ i.castSucc := lt_of_le_of_ne (hic _ _) (Ne.symm hne)
    set δ := hi_C M c w i.succ i.castSucc / M.β
    have hδ : 0 < δ := div_pos hCpos M.β_pos
    have hβδ : M.β * δ = hi_C M c w i.succ i.castSucc := by
      simp only [δ]; rw [mul_div_cancel₀ _ M.β_pos.ne']
    have hu : M.u (M.θ i.succ + c i.succ) ≤ M.u (M.θ i.succ + c i.castSucc) :=
      M.u_strictMono.monotone (by linarith)
    have hδw : δ ≤ w i.succ - w i.castSucc := by
      have : hi_C M c w i.succ i.castSucc ≤ M.β * (w i.succ - w i.castSucc) := by
        unfold hi_C; nlinarith
      nlinarith [M.β_pos]
    obtain ⟨hw', hgain⟩ := hi_spread_reduction M hf hw hwm i hδ hδw
    set w' := hi_reduce M w i.succ δ
    -- the new contract is incentive compatible
    have hC' : ∀ j l, hi_C M c w' j l = hi_C M c w j l +
        M.β * ((if i.succ ≤ l then δ else 0) - (if i.succ ≤ j then δ else 0)) := by
      intro j l; simp only [hi_C, w', hi_reduce]; ring
    have hloc : hi_LocalIC M c w' := by
      intro l
      by_cases hl : l = i
      · subst hl
        have hn : ¬ l.succ ≤ l.castSucc := not_le.2 Fin.castSucc_lt_succ
        have h0 : hi_C M c w' l.succ l.castSucc = 0 := by
          rw [hC']; simp only [hn, le_refl, ↓reduceIte]; linarith
        exact ⟨h0.ge, (hi_upward_of_binding M c w' Fin.castSucc_lt_succ h0 hci).1⟩
      · have hiff : (i.succ ≤ l.succ ↔ i.succ ≤ l.castSucc) := by
          rw [Fin.le_def, Fin.le_def]
          simp only [Fin.val_succ, Fin.val_castSucc]
          have : l.val ≠ i.val := fun h => hl (Fin.ext h)
          omega
        constructor
        · rw [hC']
          by_cases h : i.succ ≤ l.castSucc
          · simp only [h, hiff.2 h, ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
          · have h' : ¬ i.succ ≤ l.succ := fun h'' => h (hiff.1 h'')
            simp only [h, h', ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
        · rw [hC']
          by_cases h : i.succ ≤ l.castSucc
          · simp only [h, hiff.2 h, ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
          · have h' : ¬ i.succ ≤ l.succ := fun h'' => h (hiff.1 h'')
            simp only [h, h', ↓reduceIte, sub_self, mul_zero, add_zero]; exact hic _ _
    have hfeas : hi_Feasible M v c w' := by
      refine ⟨lemma_22_3_2 M c w' hloc, ?_, hw'⟩
      rw [← hpk]
      unfold hi_agentValue
      have h1 := hi_reduce_mean M w i.succ δ
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [hi_sum_mul_left M M.β w', hi_sum_mul_left M M.β w, h1]
    have hle := hbest c w' hfeas
    unfold hi_principalValue at hle
    have : ∑ j, M.prob j * (-c j + M.β * f (w j)) < ∑ j, M.prob j * (-c j + M.β * f (w' j)) := by
      simp only [mul_add, Finset.sum_add_distrib, add_lt_add_iff_left]
      rw [hi_sum_mul_left M M.β (fun j => f (w j)), hi_sum_mul_left M M.β (fun j => f (w' j))]
      exact mul_lt_mul_of_pos_left hgain M.β_pos
    linarith
  exact ⟨hbind, (hi_upward_of_binding M c w Fin.castSucc_lt_succ hbind hci).1,
    (hi_upward_of_binding M c w Fin.castSucc_lt_succ hbind hci).2⟩

/-- Changing one term of a weighted sum. -/
theorem hi_sum_ite (M : HIModel) (g : Fin (M.N + 1) → ℝ) (k : Fin (M.N + 1)) (x : ℝ) :
    ∑ j, M.prob j * (if j = k then x else g j) =
      ∑ j, M.prob j * g j + M.prob k * (x - g k) := by
  have : ∀ j, M.prob j * (if j = k then x else g j) =
      M.prob j * g j + (if j = k then M.prob k * (x - g k) else 0) := by
    intro j; split_ifs with h
    · subst h; ring
    · ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **Proposition 22.3.3** (Miao, p. 795). In an optimal contract against a strictly concave
continuation, `u(θᵢ + cᵢ) + βwᵢ > u(θᵢ₋₁ + cᵢ₋₁) + βwᵢ₋₁` and
`−cᵢ + βf(wᵢ) ≥ −cᵢ₋₁ + βf(wᵢ₋₁)`. -/
theorem proposition_22_3_3 (M : HIModel) {f : ℝ → ℝ} (hf : assumption_22_3_2 M f) {v : ℝ}
    {c w : Fin (M.N + 1) → ℝ} (hopt : hi_Optimal M f v c w) (i : Fin M.N) :
    M.u (M.θ i.castSucc + c i.castSucc) + M.β * w i.castSucc <
        M.u (M.θ i.succ + c i.succ) + M.β * w i.succ ∧
      -c i.castSucc + M.β * f (w i.castSucc) ≤ -c i.succ + M.β * f (w i.succ) := by
  have hbind := (proposition_22_3_2 M hf hopt i).1
  obtain ⟨⟨hic, hpk, hw⟩, hbest⟩ := hopt
  have hθ : M.θ i.castSucc < M.θ i.succ := M.θ_strictMono Fin.castSucc_lt_succ
  have heq : M.u (M.θ i.succ + c i.succ) + M.β * w i.succ =
      M.u (M.θ i.succ + c i.castSucc) + M.β * w i.castSucc := by
    unfold hi_C at hbind; linarith
  refine ⟨?_, ?_⟩
  · rw [heq]
    have := M.u_strictMono (show M.θ i.castSucc + c i.castSucc < M.θ i.succ + c i.castSucc by
      linarith)
    linarith
  · by_contra hlt
    push Not at hlt
    -- replace `(c_i, w_i)` by `(c_{i−1}, w_{i−1})`
    set k := i.succ
    set r : Fin (M.N + 1) → Fin (M.N + 1) := fun j => if j = k then i.castSucc else j
    set c' := fun j => c (r j)
    set w' := fun j => w (r j)
    have hown : ∀ j, M.u (M.θ j + c' j) + M.β * w' j = M.u (M.θ j + c j) + M.β * w j := by
      intro j
      simp only [c', w', r]
      split_ifs with h
      · subst h; exact heq.symm
      · rfl
    have hic' : hi_IC M c' w' := by
      intro j l
      have := hic j (r l)
      unfold hi_C at this ⊢
      rw [hown j]
      exact this
    have hpk' : hi_agentValue M c' w' = v := by
      rw [← hpk]; unfold hi_agentValue
      exact Finset.sum_congr rfl fun j _ => by rw [hown j]
    have hw'' : ∀ j, w' j < hi_vmax M := fun j => hw (r j)
    have hle := hbest c' w' ⟨hic', hpk', hw''⟩
    unfold hi_principalValue at hle
    have e : ∀ j, -c' j + M.β * f (w' j) = if j = k then -c i.castSucc + M.β * f (w i.castSucc)
        else -c j + M.β * f (w j) := fun j => by
      simp only [c', w', r]; split_ifs <;> rfl
    simp only [e] at hle
    rw [hi_sum_ite M (fun j => -c j + M.β * f (w j))] at hle
    have := mul_lt_mul_of_pos_left (sub_pos.2 hlt) (M.prob_pos k)
    linarith

/-- The book's `θᵢ₊₁` in (22.27), with the convention `θₙ₊₁ = θₙ` (it is multiplied by
`μₙ₊₁ = 0`). -/
def hi_θsucc (M : HIModel) (i : Fin (M.N + 1)) : ℝ := M.θ ⟨min (i.val + 1) M.N, by omega⟩

/-- Miao, (22.27)–(22.29), p. 795: the first-order conditions for an optimal contract `(c, w)` at
`v`, with multipliers `λ` for (22.25) and `μᵢ` for `Cᵢ,ᵢ₋₁ ≥ 0`, `μ₁ = μₙ₊₁ = 0`; `u'` and `P'`
are the derivatives of `u` and `P`. The multipliers are indexed from `0`: `μ 0` is the book's
`μ₁`, `μ (N + 1)` its `μₙ₊₁`. -/
def hi_FOC (M : HIModel) (u' dP : ℝ → ℝ) (v : ℝ) (c w : Fin (M.N + 1) → ℝ) (lam : ℝ)
    (μ : ℕ → ℝ) : Prop :=
  μ 0 = 0 ∧ μ (M.N + 1) = 0 ∧
    (∀ i : Fin (M.N + 1), M.prob i * (1 - lam * u' (M.θ i + c i)) =
      μ i.val * u' (M.θ i + c i) - μ (i.val + 1) * u' (hi_θsucc M i + c i)) ∧
    (∀ i : Fin (M.N + 1), M.prob i * (dP (w i) + lam) = μ (i.val + 1) - μ i.val) ∧
    dP v = -lam

/-- **(22.30)** (Miao, p. 795). Summing (22.28) over `i` and using (22.29):
`Σ πᵢ P'(wᵢ) = P'(v)`, so `P'(vₜ)` is a martingale. -/
theorem eq_22_30 (M : HIModel) {u' dP : ℝ → ℝ} {v lam : ℝ} {c w : Fin (M.N + 1) → ℝ}
    {μ : ℕ → ℝ} (h : hi_FOC M u' dP v c w lam μ) :
    ∑ i, M.prob i * dP (w i) = dP v := by
  obtain ⟨h0, hn, -, h28, h29⟩ := h
  have hsum : ∑ i : Fin (M.N + 1), M.prob i * (dP (w i) + lam) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => h28 i]
    rw [Fin.sum_univ_eq_sum_range (fun i => μ (i + 1) - μ i), Finset.sum_range_sub, hn, h0]
    ring
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.prob_sum, one_mul] at hsum
  linarith

/-- Miao, (22.30) and p. 796, without multipliers: if `P` solves the Bellman equation in `F`,
`(c, w)` attains `P(v)`, and `P` is differentiable at `v` and at each `wᵢ`, then
`Σ πᵢ P'(wᵢ) = P'(v)`. Raising every `wᵢ` by `ε` keeps incentive compatibility and delivers
`v + βε`, so `ε ↦ P(v + βε) − Σ πᵢ [−cᵢ + βP(wᵢ + ε)]` has a local minimum at `0`. -/
theorem hi_martingale_of_shift (M : HIModel) {P dP : ℝ → ℝ} (hP : hi_InF M P)
    (hfix : ∀ v < hi_vmax M, hi_T M P v = P v) {v : ℝ} {c w : Fin (M.N + 1) → ℝ}
    (hfeas : hi_Feasible M v c w) (hval : hi_principalValue M P c w = P v)
    (hdv : HasDerivAt P (dP v) v) (hdw : ∀ i, HasDerivAt P (dP (w i)) (w i)) :
    ∑ i, M.prob i * dP (w i) = dP v := by
  obtain ⟨hic, hpk, hw⟩ := hfeas
  have hv : v < hi_vmax M := hpk ▸ hi_agentValue_lt_vmax M hw
  set g : ℝ → ℝ := fun ε => P (v + M.β * ε) - hi_principalValue M P c (fun l => w l + ε)
  -- the shifted contract is feasible for small `ε`
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (∀ i, w i + ε < hi_vmax M) ∧ v + M.β * ε < hi_vmax M := by
    refine (Filter.eventually_all.2 fun i => ?_).and ?_
    · exact (isOpen_lt (continuous_const.add continuous_id) continuous_const).mem_nhds
        (by simpa using hw i)
    · exact (isOpen_lt (continuous_const.add (continuous_const.mul continuous_id))
        continuous_const).mem_nhds (by simpa using hv)
  have hmin : IsLocalMin g 0 := by
    filter_upwards [hev] with ε ⟨hwε, hvε⟩
    have hf : hi_Feasible M (v + M.β * ε) c (fun l => w l + ε) :=
      ⟨fun i j => by rw [hi_C_shift]; exact hic i j, by rw [hi_agentValue_shift, hpk], hwε⟩
    have := hi_le_T M (fun w hw => (hP w hw).2) hf
    rw [hfix _ hvε] at this
    simp only [g, mul_zero, add_zero, hval, sub_self]
    linarith
  have hd1 : HasDerivAt (fun ε => P (v + M.β * ε)) (dP v * M.β) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => v + M.β * ε) M.β 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul M.β).const_add v
    have hP0 : HasDerivAt P (dP v) ((fun ε : ℝ => v + M.β * ε) 0) := by simpa using hdv
    exact hP0.comp (0 : ℝ) hin
  have hd2 : HasDerivAt (fun ε => hi_principalValue M P c (fun l => w l + ε))
      (∑ i, M.prob i * (M.β * dP (w i))) 0 := by
    unfold hi_principalValue
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h := (show HasDerivAt P (dP (w i)) (w i + 0) by simpa using hdw i).comp_const_add
      (w i) 0
    exact ((h.const_mul M.β).const_add (-c i)).const_mul (M.prob i)
  have hz := hmin.hasDerivAt_eq_zero (hd1.sub hd2)
  have e : ∑ i, M.prob i * (M.β * dP (w i)) = M.β * ∑ i, M.prob i * dP (w i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at hz
  have : M.β * (dP v - ∑ i, M.prob i * dP (w i)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h M.β_pos.ne'
  · linarith

/-- Miao, p. 796: with `P` strictly concave and differentiable on `(−∞, vmax)`, the derivative is
strictly decreasing there. -/
theorem hi_strictAntiOn_deriv (M : HIModel) {P : ℝ → ℝ} (hP : assumption_22_3_2 M P)
    (hd : ∀ x < hi_vmax M, DifferentiableAt ℝ P x) :
    StrictAntiOn (deriv P) (Set.Iio (hi_vmax M)) :=
  hP.strictAntiOn_deriv fun x hx => hd x hx

/-- **Lemma 22.3.3** (Miao, p. 796). With at least two income states, in a contract satisfying
the incentive constraints and the first-order conditions (22.27)–(22.29), with `P'` strictly
decreasing on `(−∞, vmax)` (Assumption 22.3.2) and `u'` strictly decreasing, `w₁ < v < wₙ`. -/
theorem lemma_22_3_3 (M : HIModel) (hN : 1 ≤ M.N) {u' dP : ℝ → ℝ}
    (hu' : StrictAnti u') (hdP : StrictAntiOn dP (Set.Iio (hi_vmax M))) {v lam : ℝ}
    {c w : Fin (M.N + 1) → ℝ} {μ : ℕ → ℝ} (hfeas : hi_Feasible M v c w)
    (hfoc : hi_FOC M u' dP v c w lam μ) :
    w 0 < v ∧ v < w (Fin.last M.N) := by
  obtain ⟨hic, hpk, hw⟩ := hfeas
  have hv : v < hi_vmax M := hpk ▸ hi_agentValue_lt_vmax M hw
  have hwm := (lemma_22_3_1 M c w hic).2
  have h30 := eq_22_30 M hfoc
  obtain ⟨h0, hn, h27, h28, h29⟩ := hfoc
  -- if all `wᵢ` equal `v`, the first-order conditions force full smoothing: contradiction
  have key : (∀ i, w i = v) → False := by
    intro hall
    -- all `μ` vanish
    have hμ : ∀ m, m ≤ M.N + 1 → μ m = 0 := by
      intro m
      induction m with
      | zero => intro _; exact h0
      | succ m ih =>
        intro hm
        have := h28 ⟨m, by omega⟩
        simp only [hall, h29, neg_add_cancel, mul_zero] at this
        rw [ih (by omega)] at this
        linarith
    -- marginal utilities are equalised
    have hmu : ∀ i : Fin (M.N + 1), lam * u' (M.θ i + c i) = 1 := by
      intro i
      have := h27 i
      rw [hμ i.val (by omega), hμ (i.val + 1) (by omega)] at this
      have hp := M.prob_pos i
      have : M.prob i * (1 - lam * u' (M.θ i + c i)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    set i0 : Fin (M.N + 1) := ⟨0, by omega⟩
    set i1 : Fin (M.N + 1) := ⟨1, by omega⟩
    have hx : M.θ i0 + c i0 = M.θ i1 + c i1 := by
      apply hu'.injective
      have a := hmu i0
      have b := hmu i1
      have hl : lam ≠ 0 := fun h => by rw [h, zero_mul] at a; exact zero_ne_one a
      exact mul_left_cancel₀ hl (a.trans b.symm)
    have hθ : M.θ i0 < M.θ i1 := M.θ_strictMono (Fin.mk_lt_mk.2 (by omega))
    -- but equal continuation values and incentive compatibility give `c₁ = c₀`
    have hC := hic i1 i0
    unfold hi_C at hC
    rw [hall i0, hall i1] at hC
    have : M.u (M.θ i1 + c i0) ≤ M.u (M.θ i1 + c i1) := by linarith
    have := M.u_strictMono.le_iff_le.1 this
    linarith
  have hsum0 : ∑ i, M.prob i * (dP (w i) - dP v) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hi_sum_const, h30, sub_self]
  constructor
  · by_contra hge
    push Not at hge
    apply key
    intro i
    have hwi : v ≤ w i := hge.trans (hwm (Fin.zero_le i))
    have hle : ∀ j, M.prob j * (dP (w j) - dP v) ≤ 0 := fun j => by
      have : dP (w j) ≤ dP v :=
        hdP.antitoneOn hv (hw j) (hge.trans (hwm (Fin.zero_le j)))
      nlinarith [M.prob_pos j]
    have hz := (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hle j).1 hsum0 i (Finset.mem_univ _)
    have : dP (w i) = dP v := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (M.prob_pos i).ne'
      · linarith
    exact hdP.injOn (hw i) hv this
  · by_contra hge
    push Not at hge
    apply key
    intro i
    have hle : ∀ j, 0 ≤ M.prob j * (dP (w j) - dP v) := fun j => by
      have : dP v ≤ dP (w j) :=
        hdP.antitoneOn (hw j) hv ((hwm (Fin.le_last j)).trans hge)
      nlinarith [M.prob_pos j]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hle j).1 hsum0 i (Finset.mem_univ _)
    have : dP (w i) = dP v := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (M.prob_pos i).ne'
      · linarith
    exact hdP.injOn (hw i) hv this

/-- Lemma 22.3.3 needs at least two income states: with one state (`N = 0`) the conclusion
`w₁ < v < wₙ` is impossible, since `w₁ = wₙ`. -/
theorem hi_lemma_22_3_3_one_state (w : Fin 1 → ℝ) (v : ℝ) : ¬ (w 0 < v ∧ v < w (Fin.last 0)) :=
  fun h => lt_asymm h.1 h.2

end Miao.RecursiveContracts
