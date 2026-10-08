/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ValueOfInformation.Converse

/-!
# Binary signals: more accurate is more valuable

A binary state `θ ∈ {false, true}` and a binary signal that matches the state with probability
`q` (`binExp q`), as in models of noisy information, expert advice or test accuracy.

* `binExp_garble`: for `1/2 < q` and `1/2 ≤ q' ≤ q`, the less accurate experiment is a garbling
  of the more accurate one: pass the signal through a binary channel of accuracy
  `(q + q' − 1)/(2q − 1)`.
* `value_mono_accuracy`: so the more accurate signal is at least as valuable in every decision
  problem, with every prior (Blackwell).
* `value_guess`, `value_strict`: in the problem of guessing the state with a uniform prior the
  value is `max(q, 1 − q)`, so a strictly more accurate signal is strictly more valuable.
-/

open Finset

namespace DPExtensions.ValueOfInformation

/-- The binary experiment that reports the state with probability `q`. -/
def binExp (q : ℝ) (θ y : Bool) : ℝ := if θ = y then q else 1 - q

theorem binExp_isStochastic {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsStochastic (binExp q) :=
  ⟨fun θ y => by simp only [binExp]; split_ifs <;> linarith, fun θ => by
    cases θ <;> simp [binExp]⟩

/-- **A less accurate binary signal is a garbling of a more accurate one.** -/
theorem binExp_garble {q q' : ℝ} (hq : 1 / 2 < q) (hq' : 1 / 2 ≤ q') (hle : q' ≤ q) :
    ∃ M, IsStochastic M ∧ binExp q' = garble (binExp q) M := by
  have hd : 0 < 2 * q - 1 := by linarith
  set m := (q + q' - 1) / (2 * q - 1)
  have hm0 : 0 ≤ m := div_nonneg (by linarith) hd.le
  have hm1 : m ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨binExp m, binExp_isStochastic hm0 hm1, ?_⟩
  have hd' : 2 * q - 1 ≠ 0 := hd.ne'
  have hmul : (2 * q - 1) * m = q + q' - 1 := mul_div_cancel₀ _ hd'
  have key : q * m + (1 - q) * (1 - m) = q' := by linear_combination hmul
  funext θ y'
  cases θ <;> cases y' <;> simp only [binExp, garble, Fintype.sum_bool] <;> norm_num <;>
    linarith

/-- **More accurate signals are more valuable** in every decision problem. -/
theorem value_mono_accuracy {A : Type*} [Fintype A] [Nonempty A] {q q' : ℝ} (hq : 1 / 2 < q)
    (hq' : 1 / 2 ≤ q') (hle : q' ≤ q) (π : Bool → ℝ) (u : A → Bool → ℝ) :
    value π u (binExp q') ≤ value π u (binExp q) := by
  obtain ⟨M, hM, e⟩ := binExp_garble hq hq' hle
  rw [e]
  exact value_garble_le π u _ hM

theorem sup'_bool (f : Bool → ℝ) : univ.sup' univ_nonempty f = max (f true) (f false) := by
  refine le_antisymm (sup'_le _ _ fun b _ => ?_) (max_le (le_sup' f (mem_univ _))
    (le_sup' f (mem_univ _)))
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Guessing a binary state with a uniform prior: the value of `binExp q` is `max(q, 1 − q)`. -/
theorem value_guess (q : ℝ) :
    value (fun _ => 1 / 2) (fun a θ : Bool => if a = θ then (1 : ℝ) else 0) (binExp q) =
      max q (1 - q) := by
  simp only [value, sup'_bool, payoff, Fintype.sum_bool, binExp]
  norm_num
  rw [max_comm (1 / 2 * (1 - q)) (1 / 2 * q),
    ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- **A strictly more accurate signal is strictly more valuable** (in the guessing problem). -/
theorem value_strict {q q' : ℝ} (hq' : 1 / 2 ≤ q') (hlt : q' < q) :
    value (fun _ => 1 / 2) (fun a θ : Bool => if a = θ then (1 : ℝ) else 0) (binExp q') <
      value (fun _ => 1 / 2) (fun a θ : Bool => if a = θ then (1 : ℝ) else 0) (binExp q) := by
  rw [value_guess, value_guess, max_eq_left (by linarith), max_eq_left (by linarith)]
  exact hlt

end DPExtensions.ValueOfInformation
