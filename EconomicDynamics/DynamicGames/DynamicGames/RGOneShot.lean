/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.RGStageGame

/-!
# Subgame perfection and the one-shot deviation principle

Miao, §21.1.1, pp. 740–742: Definition 21.1.1 (subgame perfect equilibrium), Definition 21.1.2
(one-shot deviations) and Proposition 21.1.1 (the one-shot deviation principle), for pure
strategies, bounded stage payoffs `|u| ≤ M` and `0 ≤ δ < 1`.

* `rg_IsSPE δ u σ`: for every history `h`, `σ|h` is a Nash equilibrium of the subgame
  (Definition 21.1.1). Every continuation of an SPE is an SPE (`rg_isSPE_cont`), the remark
  "every subgame is completely identical to the original game" of p. 741.
* `rg_IsOneShotDev σ i h̄ τ`, `rg_IsProfitable δ u σ i h̄ τ` (Definition 21.1.2), and the value
  `(1 − δ) u(a'ᵢ, σ₋ᵢ(h̄)) + δ U(σ|(h̄, (a'ᵢ, σ₋ᵢ(h̄))))` of a one-shot deviation
  (`definition_21_1_2`).
* `proposition_21_1_1`: `σ` is an SPE iff there is no profitable one-shot deviation.

Departure: the book's proof sketch (finite deviations by induction, then truncation) is
replaced by the equivalent bound "the gain of any deviation in any subgame is at most
`2Mδⁿ` for every `n`", proved by induction on `n`.
-/

namespace Miao.DynamicGames

open Filter Topology

variable {ι : Type*} {A : ι → Type*}

/-- **Definition 21.1.1** (Miao, p. 741): `σ` is a subgame perfect equilibrium if, for every
history `h`, `σ|h` is a Nash equilibrium of the subgame after `h`:
`Uᵢ(σ|h) ≥ Uᵢ(τ, σ₋ᵢ|h)` for every strategy `τ` of every player `i`. -/
def rg_IsSPE (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) : Prop :=
  ∀ (h : rg_Hist A) (i : ι) (τ : rg_Hist A → A i),
    rg_U δ u (rg_dev (rg_cont σ h) i τ) i ≤ rg_U δ u (rg_cont σ h) i

/-- **Definition 21.1.1** (Miao, p. 741), unfolded. -/
theorem definition_21_1_1 (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) :
    rg_IsSPE δ u σ ↔ ∀ (h : rg_Hist A) (i : ι) (τ : rg_Hist A → A i),
      rg_U δ u (rg_dev (rg_cont σ h) i τ) i ≤ rg_U δ u (rg_cont σ h) i := Iff.rfl

/-- Miao, p. 741: every subgame is identical to the original game, so the continuation
`σ|h` of an SPE is an SPE. -/
theorem rg_isSPE_cont {δ : ℝ} {u : rg_Prof A → ι → ℝ} {σ : rg_Strat A} (hσ : rg_IsSPE δ u σ)
    (h : rg_Hist A) : rg_IsSPE δ u (rg_cont σ h) := by
  intro h' i τ
  rw [rg_cont_cont]
  exact hσ (h' ++ h) i τ

/-- Definition 21.1.2 (Miao, p. 741): `τ` is a one-shot deviation of player `i` from `σ` at
`h̄`: it differs from `σⁱ` at `h̄` and only there. -/
def rg_IsOneShotDev (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) (τ : rg_Hist A → A i) : Prop :=
  τ hbar ≠ σ hbar i ∧ ∀ h, h ≠ hbar → τ h = σ h i

/-- Definition 21.1.2 (Miao, p. 741): the one-shot deviation `τ` is profitable if
`Uᵢ(τ|h̄, σ₋ᵢ|h̄) > Uᵢ(σ|h̄)`. -/
def rg_IsProfitable (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) (i : ι)
    (hbar : rg_Hist A) (τ : rg_Hist A → A i) : Prop :=
  rg_U δ u (rg_cont σ hbar) i < rg_U δ u (rg_cont (rg_dev σ i τ) hbar) i

open Classical in
/-- The strategy of player `i` that plays `x` at `h̄` and follows `σ` elsewhere. -/
noncomputable def rg_oneShot (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) (x : A i) :
    rg_Hist A → A i :=
  fun h => if h = hbar then x else σ h i

/-- `rg_oneShot σ i h̄ x` is a one-shot deviation when `x ≠ σⁱ(h̄)`. -/
theorem rg_oneShot_isOneShotDev (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) {x : A i}
    (hx : x ≠ σ hbar i) : rg_IsOneShotDev σ i hbar (rg_oneShot σ i hbar x) := by
  refine ⟨?_, fun h hh => ?_⟩
  · simpa [rg_oneShot] using hx
  · simp [rg_oneShot, hh]

/-- A strategy that agrees with `σⁱ` at every history strictly longer than `h̄` does not change
the continuation after `(h̄, b)`. -/
theorem rg_cont_dev_after {σ : rg_Strat A} {i : ι} {hbar : rg_Hist A} {τ : rg_Hist A → A i}
    (hτ : ∀ h, h ≠ hbar → τ h = σ h i) (b : rg_Prof A) :
    rg_cont (rg_dev σ i τ) (b :: hbar) = rg_cont σ (b :: hbar) := by
  funext h'
  have hne : h' ++ b :: hbar ≠ hbar := by
    intro heq
    have := congrArg List.length heq
    simp at this
    omega
  simp only [rg_cont, rg_dev, hτ _ hne, rg_upd_eq_self]

/-- **Definition 21.1.2** (Miao, p. 741): the payoff of a strategy `τ` that differs from `σⁱ`
at most at `h̄` (in particular of a one-shot deviation), in the subgame after `h̄`:
`U(τ|h̄, σ₋ᵢ|h̄) = (1 − δ) u(b) + δ U(σ|(h̄, b))` with `b = (τ(h̄), σ₋ᵢ(h̄))`. -/
theorem definition_21_1_2 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A)
    (τ : rg_Hist A → A i) (hτ : ∀ h, h ≠ hbar → τ h = σ h i) (j : ι) :
    rg_U δ u (rg_cont (rg_dev σ i τ) hbar) j =
      (1 - δ) * u (rg_upd (σ hbar) i (τ hbar)) j +
        δ * rg_U δ u (rg_cont σ (rg_upd (σ hbar) i (τ hbar) :: hbar)) j := by
  rw [rg_U_cont_rec hM hδ0 hδ1]
  have hb : rg_dev σ i τ hbar = rg_upd (σ hbar) i (τ hbar) := rfl
  rw [hb, rg_cont_dev_after hτ]

/-- The value of the strategy `rg_oneShot σ i h̄ x` in the subgame after `h̄`. -/
theorem rg_oneShot_value {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) (x : A i)
    (j : ι) :
    rg_U δ u (rg_cont (rg_dev σ i (rg_oneShot σ i hbar x)) hbar) j =
      (1 - δ) * u (rg_upd (σ hbar) i x) j +
        δ * rg_U δ u (rg_cont σ (rg_upd (σ hbar) i x :: hbar)) j := by
  have h1 := definition_21_1_2 hM hδ0 hδ1 σ i hbar (rg_oneShot σ i hbar x)
    (fun h hh => by simp [rg_oneShot, hh]) j
  have h2 : rg_oneShot σ i hbar x hbar = x := by simp [rg_oneShot]
  rw [h1, h2]

/-- In an SPE no single-period deviation `x` at any history `h̄` pays:
`(1 − δ) uᵢ(x, σ₋ᵢ(h̄)) + δ Uᵢ(σ|(h̄, (x, σ₋ᵢ(h̄)))) ≤ Uᵢ(σ|h̄)`. -/
theorem rg_oneShot_le_of_isSPE {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : rg_Strat A} (hσ : rg_IsSPE δ u σ) (i : ι)
    (hbar : rg_Hist A) (x : A i) :
    (1 - δ) * u (rg_upd (σ hbar) i x) i +
        δ * rg_U δ u (rg_cont σ (rg_upd (σ hbar) i x :: hbar)) i ≤
      rg_U δ u (rg_cont σ hbar) i := by
  rw [← rg_oneShot_value hM hδ0 hδ1, rg_cont_dev]
  exact hσ hbar i _

/-- The gain from any deviation in any subgame is at most `2Mδⁿ`, for every `n`, when no
one-shot deviation is profitable. -/
theorem rg_gain_le_of_noOneShot {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : rg_Strat A} (i : ι)
    (hno : ∀ hbar τ, rg_IsOneShotDev σ i hbar τ → ¬ rg_IsProfitable δ u σ i hbar τ) (n : ℕ) :
    ∀ (h : rg_Hist A) (τ : rg_Hist A → A i),
      rg_U δ u (rg_dev (rg_cont σ h) i τ) i - rg_U δ u (rg_cont σ h) i ≤ 2 * M * δ ^ n := by
  induction n with
  | zero =>
    intro h τ
    have h1 := abs_le.1 (rg_abs_U_le hM hδ0 hδ1 (rg_dev (rg_cont σ h) i τ) i)
    have h2 := abs_le.1 (rg_abs_U_le hM hδ0 hδ1 (rg_cont σ h) i)
    simp only [pow_zero, mul_one]
    linarith [h1.2, h2.1]
  | succ n ih =>
    intro h τ
    set b := rg_upd (σ h) i (τ []) with hb
    have hrec := rg_U_rec hM hδ0 hδ1 (rg_dev (rg_cont σ h) i τ) i
    have h0 : rg_dev (rg_cont σ h) i τ [] = b := rfl
    have hc : rg_cont (rg_dev (rg_cont σ h) i τ) [b] =
        rg_dev (rg_cont σ (b :: h)) i (fun h' => τ (h' ++ [b])) := by
      rw [rg_cont_dev, rg_cont_cont]
      rfl
    rw [h0, hc] at hrec
    have hih := ih (b :: h) (fun h' => τ (h' ++ [b]))
    -- the one-shot deviation to `τ []` at `h` is not profitable
    have hone : (1 - δ) * u b i + δ * rg_U δ u (rg_cont σ (b :: h)) i ≤
        rg_U δ u (rg_cont σ h) i := by
      by_cases hx : τ [] = σ h i
      · have hbσ : b = σ h := by rw [hb, hx, rg_upd_eq_self]
        rw [hbσ, rg_U_cont_rec hM hδ0 hδ1 σ h i]
      · have hnp := hno h _ (rg_oneShot_isOneShotDev σ i h hx)
        unfold rg_IsProfitable at hnp
        rw [rg_oneShot_value hM hδ0 hδ1] at hnp
        exact not_lt.1 hnp
    have : δ * rg_U δ u (rg_dev (rg_cont σ (b :: h)) i (fun h' => τ (h' ++ [b]))) i ≤
        δ * (rg_U δ u (rg_cont σ (b :: h)) i + 2 * M * δ ^ n) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0
    rw [hrec, pow_succ]
    nlinarith

/-- **Proposition 21.1.1** (One-shot deviation principle, Miao, p. 741). With bounded stage
payoffs and `0 ≤ δ < 1`, `σ` is a subgame perfect equilibrium iff no player has a profitable
one-shot deviation from `σ`. -/
theorem proposition_21_1_1 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) :
    rg_IsSPE δ u σ ↔
      ∀ i hbar τ, rg_IsOneShotDev σ i hbar τ → ¬ rg_IsProfitable δ u σ i hbar τ := by
  constructor
  · intro hσ i hbar τ _ hp
    unfold rg_IsProfitable at hp
    rw [rg_cont_dev] at hp
    exact absurd (hσ hbar i _) (not_le.2 hp)
  · intro hno h i τ
    have hlim : Tendsto (fun n : ℕ => 2 * M * δ ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).const_mul (2 * M)
    have := ge_of_tendsto' hlim (fun n => rg_gain_le_of_noOneShot hM hδ0 hδ1 i (hno i) n h τ)
    linarith

end Miao.DynamicGames
