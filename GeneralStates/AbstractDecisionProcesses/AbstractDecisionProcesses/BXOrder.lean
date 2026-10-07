/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDecisionProcesses.OrderTheory
import AbstractDecisionProcesses.MarkovOperator
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The pointwise order on `bX`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §A.5.2.4 and Lemma A.1.3 (as used in
§2.3).

`bX` with the pointwise order is a value space for Chapter 2. In it, `vₙ ↑ v` (supremum in `bX`)
is pointwise monotone convergence (Lemma A.1.3), and **Corollary A.5.17** holds: `bX` is
countably Dedekind complete. Markov operators are order continuous (monotone convergence,
Lemma A.5.33).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

/-- A monotone sequence in `bX` converging pointwise to `w ∈ bX` increases to `w` in `bX`. -/
theorem isLUB_of_tendsto_bX {g : ℕ → ↥(bX X)} (hg : Monotone g) {w : ↥(bX X)}
    (hlim : ∀ x, Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x))) :
    IsLUB (range g) w := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    intro x
    exact Monotone.ge_of_tendsto (f := fun n => (g n : X → ℝ) x) (fun a b h => hg h x) (hlim x) n
  · intro x
    exact le_of_tendsto' (hlim x) fun n => hu ⟨n, rfl⟩ x

/-- **Lemma A.1.3** in `bX`: if `vₙ ↑ v` in `bX`, then `vₙ(x) → v(x)` at every `x`. -/
theorem tendsto_of_isLUB_bX {g : ℕ → ↥(bX X)} (hg : Monotone g) {w : ↥(bX X)}
    (hw : IsLUB (range g) w) (x : X) :
    Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x)) := by
  -- the pointwise supremum lies in `bX` and is the supremum in `bX`
  have hbdd : ∀ y, BddAbove (range fun n => (g n : X → ℝ) y) := fun y =>
    ⟨(w : X → ℝ) y, by rintro _ ⟨n, rfl⟩; exact hw.1 ⟨n, rfl⟩ y⟩
  set s : X → ℝ := fun y => ⨆ n, (g n : X → ℝ) y
  have hs : s ∈ bX X := by
    refine ⟨Measurable.iSup fun n => (g n).2.1, ?_⟩
    obtain ⟨M, hM⟩ := (g 0).2.2
    obtain ⟨N, hN⟩ := w.2.2
    refine ⟨max M N, fun y => abs_le.2 ⟨?_, ?_⟩⟩
    · have := le_ciSup (hbdd y) 0
      linarith [(abs_le.1 (hM y)).1, le_max_left M N]
    · have := ciSup_le fun n => hw.1 ⟨n, rfl⟩ y
      linarith [(abs_le.1 (hN y)).2, le_max_right M N]
  have hup : (⟨s, hs⟩ : ↥(bX X)) ∈ upperBounds (range g) := by
    rintro _ ⟨n, rfl⟩
    exact fun y => le_ciSup (hbdd y) n
  have h1 : w ≤ ⟨s, hs⟩ := hw.2 hup
  have hws : (w : X → ℝ) = s :=
    le_antisymm h1 fun y => ciSup_le fun n => hw.1 ⟨n, rfl⟩ y
  rw [hws]
  exact tendsto_atTop_ciSup (fun a b h => hg h x) (hbdd x)

/-- **Corollary A.5.17** (p. 379): `bX` is countably Dedekind complete. -/
theorem countablyDedekindComplete_bX : CountablyDedekindComplete ↥(bX X) := by
  intro A hne hc
  have : Countable A := hc.to_subtype
  have : Nonempty A := hne.to_subtype
  refine ⟨fun ⟨b, hb⟩ => ?_, fun ⟨b, hb⟩ => ?_⟩
  · have hbdd : ∀ y, BddAbove (range fun f : A => (f.1 : X → ℝ) y) := fun y =>
      ⟨(b : X → ℝ) y, by rintro _ ⟨f, rfl⟩; exact hb f.2 y⟩
    set s : X → ℝ := fun y => ⨆ f : A, (f.1 : X → ℝ) y
    obtain ⟨f₀⟩ := ‹Nonempty A›
    have hs : s ∈ bX X := by
      refine ⟨Measurable.iSup fun f => f.1.2.1, ?_⟩
      obtain ⟨M, hM⟩ := f₀.1.2.2
      obtain ⟨N, hN⟩ := b.2.2
      refine ⟨max M N, fun y => abs_le.2 ⟨?_, ?_⟩⟩
      · have := le_ciSup (hbdd y) f₀
        linarith [(abs_le.1 (hM y)).1, le_max_left M N]
      · have := ciSup_le fun f : A => hb f.2 y
        linarith [(abs_le.1 (hN y)).2, le_max_right M N]
    refine ⟨⟨s, hs⟩, fun f hf y => le_ciSup (hbdd y) ⟨f, hf⟩, fun u hu y => ?_⟩
    exact ciSup_le fun f => hu f.2 y
  · have hbdd : ∀ y, BddBelow (range fun f : A => (f.1 : X → ℝ) y) := fun y =>
      ⟨(b : X → ℝ) y, by rintro _ ⟨f, rfl⟩; exact hb f.2 y⟩
    set s : X → ℝ := fun y => ⨅ f : A, (f.1 : X → ℝ) y
    obtain ⟨f₀⟩ := ‹Nonempty A›
    have hs : s ∈ bX X := by
      refine ⟨Measurable.iInf fun f => f.1.2.1, ?_⟩
      obtain ⟨M, hM⟩ := f₀.1.2.2
      obtain ⟨N, hN⟩ := b.2.2
      refine ⟨max M N, fun y => abs_le.2 ⟨?_, ?_⟩⟩
      · have := le_ciInf fun f : A => hb f.2 y
        linarith [(abs_le.1 (hN y)).1, le_max_right M N]
      · have := ciInf_le (hbdd y) f₀
        linarith [(abs_le.1 (hM y)).2, le_max_left M N]
    refine ⟨⟨s, hs⟩, fun f hf y => ciInf_le (hbdd y) ⟨f, hf⟩, fun u hu y => ?_⟩
    exact le_ciInf fun f => hu f.2 y

/-- **Lemma A.5.33**-type monotone convergence: if `vₙ ↑ v` pointwise in `bX`, then
`Pvₙ → Pv` pointwise. -/
theorem tendsto_markovOp (P : Kernel X X) [IsMarkovKernel P] {g : ℕ → X → ℝ} {v : X → ℝ}
    (hg : ∀ n, g n ∈ bX X) (hv : v ∈ bX X) (hmono : ∀ y, Monotone fun n => g n y)
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (v y))) (x : X) :
    Tendsto (fun n => markovOp P (g n) x) atTop (𝓝 (markovOp P v x)) :=
  integral_tendsto_of_tendsto_of_monotone (fun n => integrable_of_mem_bX P (hg n) x)
    (integrable_of_mem_bX P hv x) (Filter.Eventually.of_forall hmono)
    (Filter.Eventually.of_forall hlim)

end SargentStachurski.AbstractDecisionProcesses
