/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Finite histories

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `HistoryTools`),
with the namespace renamed.

Copied from `RecursiveMethods/StochasticDP` (module `Histories`, SLP §8.2), with the namespace
renamed. Histories `sᵗ = (s₁, …, s_t)` are functions `Fin t → S`; `lastState s₀ sᵗ` is the most
recent state (`s₀` for the empty history, otherwise `s_t`). Used for Miao, §5.1, pp. 137–139.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory

variable {S : Type*} [MeasurableSpace S]

theorem measurable_cons (t : ℕ) :
    Measurable fun p : S × (Fin t → S) => (Fin.cons p.1 p.2 : Fin (t + 1) → S) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_snoc (t : ℕ) :
    Measurable fun p : (Fin t → S) × S => (Fin.snoc p.1 p.2 : Fin (t + 1) → S) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

theorem measurable_init (t : ℕ) : Measurable (Fin.init : (Fin (t + 1) → S) → Fin t → S) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The most recent state of a history started at `s₀`: `s₀` for the empty history, otherwise
the last entry. -/
def lastState (s₀ : S) : {t : ℕ} → (Fin t → S) → S
  | 0, _ => s₀
  | t + 1, h => h (Fin.last t)

theorem measurable_lastState (s₀ : S) (t : ℕ) : Measurable (lastState s₀ (t := t)) := by
  cases t with
  | zero => exact measurable_const
  | succ t => exact measurable_pi_apply _

omit [MeasurableSpace S] in
theorem lastState_cons (s₀ s₁ : S) {t : ℕ} (h : Fin t → S) :
    lastState s₀ (Fin.cons s₁ h : Fin (t + 1) → S) = lastState s₁ h := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [lastState]
    rw [← Fin.succ_last, Fin.cons_succ]

omit [MeasurableSpace S] in
theorem lastState_snoc (s₀ s : S) {t : ℕ} (h : Fin t → S) :
    lastState s₀ (Fin.snoc h s : Fin (t + 1) → S) = s := by
  simp [lastState]

end Miao.FiniteHorizonDP
