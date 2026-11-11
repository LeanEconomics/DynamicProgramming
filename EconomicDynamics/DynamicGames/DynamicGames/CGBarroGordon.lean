/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.CGRecursive
import DynamicGames.CGOnePeriod

/-!
# The repeated Barro–Gordon economy

Miao, Example 21.4.3, pp. 763–764: the one-period economy of Example 21.4.1 repeated, with the
government's objective `(1 − δ) ∑ δ^{t-1} [λ(y_t − y_n) − π_t²/2]` and `y_t = y_n + a(π_t − π^e_t)`,
so `r(π^e, π) = λa(π − π^e) − π²/2`.

* `example_21_4_3_best_deviation`: the most profitable one-period deviation is `ε = λa`.
* `example_21_4_3_range`: the trigger-strategy condition
  `−π²/2 ≥ (1 − δ)[λa(ε − π) − ε²/2] + δ(−(λa)²/2)` for all `ε` holds iff
  `(1 − 2δ)λa ≤ π ≤ λa`; the inequality factors as `(π − λa)(π − (1 − 2δ)λa) ≤ 0`. This holds
  for every `δ ∈ [0, 1)`; the book states it for `0 < δ < 0.5`, where the lower end is positive.
  `example_21_4_3_mono`: the range grows with `δ`.
* `example_21_4_3_nash`, `example_21_4_3`: the SPE statements. The general theory of
  `CGRepeated` needs bounded payoffs (as for the compact action sets of §21.4.1), so here
  inflation rates and forecasts lie in `[0, K]` with `K ≥ λa`; then infinite repetition of the
  Nash outcome `π = π^e = λa` is an SPE, and every `π ∈ [(1 − 2δ)λa, λa] ∩ [0, K]` is supported by
  the trigger strategy (revert to `λa` forever after a deviation), an instance of
  `example_21_4_5`.
-/

namespace Miao.DynamicGames

/-- Miao, p. 763: `r(π^e, π) = λ(y − y_n) − π²/2` with `y = y_n + a(π − π^e)` equals
`λa(π − π^e) − π²/2`. -/
theorem cg_bgGov_eq (lam a yn infe infl : ℝ) :
    cg_bgGov lam a yn infe infl = lam * a * (infl - infe) - infl ^ 2 / 2 := by
  unfold cg_bgGov; ring

/-- **Example 21.4.3** (Miao, p. 763): the most profitable one-period deviation from `π` is
`ε = λa`. -/
theorem example_21_4_3_best_deviation (lam a infl ε : ℝ) :
    lam * a * (ε - infl) - ε ^ 2 / 2 ≤ lam * a * (lam * a - infl) - (lam * a) ^ 2 / 2 := by
  nlinarith [sq_nonneg (ε - lam * a)]

/-- **Example 21.4.3** (Miao, pp. 763–764): the trigger-strategy condition
`−π²/2 ≥ (1 − δ)[λa(ε − π) − ε²/2] + δ(−(λa)²/2)` for all `ε` holds iff
`(1 − 2δ)λa ≤ π ≤ λa` (for every `δ ∈ [0, 1)` and `λa ≥ 0`). -/
theorem example_21_4_3_range {lam a δ infl : ℝ} (hla : 0 ≤ lam * a) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ ε, (1 - δ) * (lam * a * (ε - infl) - ε ^ 2 / 2) + δ * (-(lam * a) ^ 2 / 2) ≤
      -infl ^ 2 / 2) ↔ (1 - 2 * δ) * (lam * a) ≤ infl ∧ infl ≤ lam * a := by
  set L := lam * a with hL
  have hdL : 0 ≤ δ * L := mul_nonneg hδ0 hla
  constructor
  · intro h
    have h1 := h L
    have hprod : (infl - L) * (infl - (1 - 2 * δ) * L) ≤ 0 := by nlinarith
    constructor
    · by_contra hc
      push Not at hc
      have : 0 < (L - infl) * ((1 - 2 * δ) * L - infl) :=
        mul_pos (by nlinarith) (by linarith)
      nlinarith
    · by_contra hc
      push Not at hc
      have : 0 < (infl - L) * (infl - (1 - 2 * δ) * L) :=
        mul_pos (by linarith) (by nlinarith)
      nlinarith
  · rintro ⟨h1, h2⟩ ε
    have hb := example_21_4_3_best_deviation lam a infl ε
    rw [← hL] at hb
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ 1 - δ)
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-- **Example 21.4.3** (Miao, p. 764): "the range is larger for a larger `δ`". -/
theorem example_21_4_3_mono {L δ δ' : ℝ} (hL : 0 ≤ L) (hδ : δ ≤ δ') :
    (1 - 2 * δ') * L ≤ (1 - 2 * δ) * L := by nlinarith

/-- The Barro–Gordon payoff `r(π^e, π) = λa(π − π^e) − π²/2` on the action set `[0, K]`. -/
noncomputable def cg_bgR (lam a K : ℝ) (x y : Set.Icc (0 : ℝ) K) : ℝ :=
  lam * a * ((y : ℝ) - x) - (y : ℝ) ^ 2 / 2

/-- The competitive equilibria `π^e = π` on `[0, K]`. -/
def cg_bgCK (K : ℝ) : Set (Set.Icc (0 : ℝ) K × Set.Icc (0 : ℝ) K) := {q | (q.1 : ℝ) = q.2}

theorem cg_bgR_abs_le {lam a K : ℝ} (hla : 0 ≤ lam * a) (x y : Set.Icc (0 : ℝ) K) :
    |cg_bgR lam a K x y| ≤ lam * a * K + K ^ 2 / 2 := by
  obtain ⟨x, hx0, hxK⟩ := x
  obtain ⟨y, hy0, hyK⟩ := y
  unfold cg_bgR
  dsimp only
  rw [abs_le]
  have h1 : lam * a * (y - x) ≤ lam * a * K := mul_le_mul_of_nonneg_left (by linarith) hla
  have h2 : -(lam * a * K) ≤ lam * a * (y - x) := by
    have := mul_le_mul_of_nonneg_left (by linarith : -K ≤ y - x) hla
    linarith
  have h3 : y ^ 2 ≤ K ^ 2 := by nlinarith
  constructor <;> nlinarith [sq_nonneg y]

/-- **Example 21.4.3** (Miao, p. 763): "infinite repetition of the one-period Nash equilibrium
is an SPE". On `[0, K]` with `K ≥ λa > 0`, repeating `π^e = π = λa` is an SPE with value
`−(λa)²/2`. -/
theorem example_21_4_3_nash {lam a K δ : ℝ} (hl : 0 < lam) (ha : 0 < a) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (N : Set.Icc (0 : ℝ) K) (hN : (N : ℝ) = lam * a) :
    cg_IsSPE δ (cg_bgR lam a K) (cg_bgCK K) (fun _ => (N, N)) ∧
      cg_U δ (cg_bgR lam a K) (fun _ => (N, N)) = -(lam * a) ^ 2 / 2 := by
  have hla : 0 ≤ lam * a := (mul_pos hl ha).le
  have h := cg_nash_repetition_spe (C := cg_bgCK K) hδ0 hδ1 (cg_bgR_abs_le hla) (xN := N)
    (yN := N) rfl (fun y' => by
      unfold cg_bgR
      rw [hN]
      nlinarith [sq_nonneg ((y' : ℝ) - lam * a)])
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold cg_bgR
  rw [hN]
  ring

/-- **Example 21.4.3** (Miao, pp. 763–764). On `[0, K]` with `K ≥ λa > 0` and `δ ∈ [0, 1)`, every
`π ∈ [0, K]` with `(1 − 2δ)λa ≤ π ≤ λa` is supported by the trigger strategy (play
`π^e = π` while no one has deviated, revert to the Nash outcome `λa` forever after a deviation):
it is an SPE with value `−π²/2`. -/
theorem example_21_4_3 {lam a K δ : ℝ} (hl : 0 < lam) (ha : 0 < a) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (N : Set.Icc (0 : ℝ) K) (hN : (N : ℝ) = lam * a) (infl : Set.Icc (0 : ℝ) K)
    (h1 : (1 - 2 * δ) * (lam * a) ≤ infl) (h2 : (infl : ℝ) ≤ lam * a) :
    cg_IsSPE δ (cg_bgR lam a K) (cg_bgCK K)
        (cg_recStrat (cg_trigZh (cg_bgR lam a K infl infl) infl N)
          (cg_trigZg (cg_bgR lam a K infl infl) infl N)
          (cg_trigV (cg_bgR lam a K infl infl) (cg_bgR lam a K N N) infl infl)
          (cg_bgR lam a K infl infl)) ∧
      cg_U δ (cg_bgR lam a K)
        (cg_recStrat (cg_trigZh (cg_bgR lam a K infl infl) infl N)
          (cg_trigZg (cg_bgR lam a K infl infl) infl N)
          (cg_trigV (cg_bgR lam a K infl infl) (cg_bgR lam a K N N) infl infl)
          (cg_bgR lam a K infl infl)) = -(infl : ℝ) ^ 2 / 2 := by
  have hla : 0 ≤ lam * a := (mul_pos hl ha).le
  have hrange := (example_21_4_3_range (infl := (infl : ℝ)) hla hδ0 hδ1).2 ⟨h1, h2⟩
  have h := example_21_4_5 (C := cg_bgCK K) hδ0 hδ1 (cg_bgR_abs_le hla) (xb := infl) (yb := infl)
    (xN := N) (yN := N) rfl rfl (fun y' => by
      unfold cg_bgR
      rw [hN]
      nlinarith [sq_nonneg ((y' : ℝ) - lam * a)]) (fun y' => by
      have := hrange y'
      unfold cg_bgR
      rw [hN]
      nlinarith)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold cg_bgR
  ring

end Miao.DynamicGames
