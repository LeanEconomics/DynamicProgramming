/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# The crossing point of an Euler equation (the construction behind SLP §18.3 (7) and (9))

SLP §18.3, pp. 556–560, defines the operator `T` by "`(Th)(k)` is the `y` solving"
  `U′[ψ(k) − y] = (right-hand side in y)`,
where the left side is increasing in `y` and blows up at `y = ψ(k)`, and the right side is
nonincreasing in `y` and equals `+∞` wherever a next-period consumption is zero (Inada condition
of Assumption 18.2). This file isolates that one-dimensional construction, so that the
deterministic operator (7) and the stochastic operator (9) are two instances of it.

The right side is described abstractly on `[0, B]` by a predicate `Z y` ("some next-period
consumption is zero at `y`", where the right side is `+∞`) and a real function `R y` (its value
when `¬ Z y`). `IsEulerRHS B Z R` records that the extended-real function `Z, R` is
nonincreasing, continuous where finite and tends to `+∞` at the points where it is infinite.
For `P > 0` (current resources, `P = ψ(k)`) the *crossing point* is
  `eulerCross u Z R P := sup {y ∈ [0, P) : Z y ∨ u (P − y) < R y}`,
the supremum of the points where the left side lies strictly below the right side. It is the
extended-real reading of "the `y` solving (7)" (NOTE 18.3-E of the transcription).

* `eulerCross_spec`: if the left side is below the right side at `y = 0`, then **either** the
  crossing point is `< P`, both consumptions there are positive and the Euler equation holds,
  **or** the crossing point is `P` and the right side is `+∞` on all of `[0, P)` (no interior
  solution exists; the agent consumes nothing).
* `eulerCross_unique`: an interior solution of the Euler equation is the crossing point.
* `eulerCross_mono`, `eulerCross_le_add_sub` (more resources raise the crossing point, by at
  most the increase in resources) and `eulerCross_mono_rhs` (a larger right side raises it):
  the order properties behind Exercises 18.5 and 18.7.
* `eventually_abs_eulerCross_sub_le`: if right sides converge pointwise in the extended sense,
  the crossing points converge (the pointwise step of Exercise 18.6, done by the monotone
  crossing argument instead of the manual's Implicit Function Theorem).

Nothing here is in the book in this form; it is the common core of the proofs of
Exercises 18.5–18.8.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology

/-- The properties of the marginal utility `u = U′` used in §18.3: positive, strictly
decreasing and continuous on `(0, ∞)`, with the Inada condition `u(c) → ∞` as `c → 0⁺`
(Assumption 18.2). -/
structure IsMarginalUtility (u : ℝ → ℝ) : Prop where
  pos : ∀ c, 0 < c → 0 < u c
  strictAnti : StrictAntiOn u (Ioi 0)
  cont : ContinuousOn u (Ioi 0)
  inada : Tendsto u (𝓝[>] 0) atTop

/-- An extended-real "right side of the Euler equation" on `[0, B]`: it is `+∞` where `Z` holds
and `R y` otherwise. It is nonincreasing (`zero_anti`, `anti`), continuous where finite
(`cont`), and tends to `+∞` at the points where it is infinite (`blowup`). -/
structure IsEulerRHS (B : ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) : Prop where
  zero_anti : ∀ y y', 0 ≤ y' → y' ≤ y → y ≤ B → Z y → Z y'
  anti : ∀ y y', 0 ≤ y' → y' ≤ y → y ≤ B → ¬ Z y' → R y ≤ R y'
  cont : ∀ y ∈ Icc 0 B, ¬ Z y →
    (∀ᶠ y' in 𝓝[Icc 0 B] y, ¬ Z y') ∧ ContinuousWithinAt R (Icc 0 B) y
  blowup : ∀ y ∈ Icc 0 B, Z y → ∀ M : ℝ, ∀ᶠ y' in 𝓝[Icc 0 B] y, Z y' ∨ M < R y'

/-- The left side `u (P − y)` of the Euler equation lies strictly below the right side at `y`
(the right side being `+∞` if `Z y`). -/
def EulerBelow (u : ℝ → ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) (P y : ℝ) : Prop :=
  Z y ∨ u (P - y) < R y

/-- The points `y ∈ [0, P)` at which the left side is strictly below the right side. -/
def eulerSet (u : ℝ → ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) (P : ℝ) : Set ℝ :=
  {y | 0 ≤ y ∧ y < P ∧ EulerBelow u Z R P y}

/-- The crossing point of the Euler equation: the supremum of `eulerSet`. -/
noncomputable def eulerCross (u : ℝ → ℝ) (Z : ℝ → Prop) (R : ℝ → ℝ) (P : ℝ) : ℝ :=
  sSup (eulerSet u Z R P)

variable {u : ℝ → ℝ} {Z : ℝ → Prop} {R : ℝ → ℝ} {B P : ℝ}

/-- Moving `y` down while the current consumption `P − y` does not fall keeps the left side
below the right side (left side increasing, right side nonincreasing in `y`). -/
theorem eulerBelow_of_le (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' y y' : ℝ}
    (hy' : 0 ≤ y') (hyy : y' ≤ y) (hyB : y ≤ B) (hc : 0 < P - y) (hcc : P - y ≤ P' - y')
    (h : EulerBelow u Z R P y) : EulerBelow u Z R P' y' := by
  rcases h with h | h
  · exact Or.inl (hR.zero_anti y y' hy' hyy hyB h)
  · by_cases hz : Z y'
    · exact Or.inl hz
    · right
      have h1 : u (P' - y') ≤ u (P - y) :=
        hu.strictAnti.antitoneOn (mem_Ioi.2 hc) (mem_Ioi.2 (hc.trans_le hcc)) hcc
      exact h1.trans_lt (h.trans_le (hR.anti y y' hy' hyy hyB hz))

/-- `eulerSet` is bounded above by `P`. -/
theorem bddAbove_eulerSet : BddAbove (eulerSet u Z R P) :=
  ⟨P, fun _ hy => hy.2.1.le⟩

/-- The crossing point is nonnegative. -/
theorem eulerCross_nonneg : 0 ≤ eulerCross u Z R P :=
  Real.sSup_nonneg fun _ hy => hy.1

/-- The crossing point is at most the current resources `P`. -/
theorem eulerCross_le (hP : 0 ≤ P) : eulerCross u Z R P ≤ P :=
  Real.sSup_le (fun _ hy => hy.2.1.le) hP

/-- Every point of `eulerSet` lies below the crossing point. -/
theorem le_eulerCross_of_mem {y : ℝ} (hy : y ∈ eulerSet u Z R P) : y ≤ eulerCross u Z R P :=
  le_csSup bddAbove_eulerSet hy

/-- `eulerSet` is an initial segment: every `y ∈ [0, eulerCross)` belongs to it. -/
theorem mem_eulerSet_of_lt (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hPB : P ≤ B)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < eulerCross u Z R P) : y ∈ eulerSet u Z R P := by
  have hne : (eulerSet u Z R P).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : eulerCross u Z R P = 0 := by rw [eulerCross, hne, Real.sSup_empty]
    linarith
  obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne hy
  refine ⟨hy0, hyz.trans hz.2.1, ?_⟩
  exact eulerBelow_of_le hu hR hy0 hyz.le (hz.2.1.le.trans hPB) (by linarith [hz.2.1])
    (by linarith) hz.2.2

/-- If the left side is not below the right side at `z ∈ [0, P)`, the crossing point is at
most `z`. -/
theorem eulerCross_le_of_not_below (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R)
    (hPB : P ≤ B) {z : ℝ} (hz0 : 0 ≤ z) (hnb : ¬ EulerBelow u Z R P z) :
    eulerCross u Z R P ≤ z := by
  refine Real.sSup_le (fun y hy => ?_) hz0
  by_contra hzy
  have hzy := lt_of_not_ge hzy
  exact hnb (eulerBelow_of_le hu hR hz0 hzy.le (hy.2.1.le.trans hPB) (by linarith [hy.2.1])
    (by linarith) hy.2.2)

/-- If every `y ∈ [0, z)` lies in `eulerSet`, then `z` is at most the crossing point. -/
theorem le_eulerCross_of_forall {z : ℝ} (h : ∀ y, 0 ≤ y → y < z → y ∈ eulerSet u Z R P) :
    z ≤ eulerCross u Z R P := by
  refine le_of_forall_lt fun c hc => ?_
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact hc0.trans_le eulerCross_nonneg
  · have hy : (c + z) / 2 ∈ eulerSet u Z R P := h _ (by linarith) (by linarith)
    exact (show c < (c + z) / 2 by linarith).trans_le (le_eulerCross_of_mem hy)

/-- More current resources raise the crossing point (`k ↦ (Th)(k)` is nondecreasing). -/
theorem eulerCross_mono (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPP : P ≤ P') (hPB : P' ≤ B) (h0 : (eulerSet u Z R P).Nonempty) :
    eulerCross u Z R P ≤ eulerCross u Z R P' := by
  refine csSup_le_csSup bddAbove_eulerSet h0 fun y hy => ⟨hy.1, hy.2.1.trans_le hPP, ?_⟩
  exact eulerBelow_of_le hu hR hy.1 le_rfl ((hy.2.1.trans_le hPP).le.trans hPB)
    (by linarith [hy.2.1]) (by linarith) hy.2.2

/-- An increase `P' − P` of current resources raises the crossing point by at most `P' − P`
(`ψ − Th` is nondecreasing). -/
theorem eulerCross_le_add_sub (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPP : P ≤ P') (hPB : P' ≤ B) :
    eulerCross u Z R P' ≤ eulerCross u Z R P + (P' - P) := by
  have h0 : 0 ≤ eulerCross u Z R P := eulerCross_nonneg
  refine Real.sSup_le (fun y hy => ?_) (by linarith)
  rcases le_or_gt y (P' - P) with hyl | hyl
  · linarith
  · have hmem : y - (P' - P) ∈ eulerSet u Z R P := by
      refine ⟨by linarith, by linarith [hy.2.1], ?_⟩
      exact eulerBelow_of_le hu hR (by linarith) (by linarith) (hy.2.1.le.trans hPB)
        (by linarith [hy.2.1]) (by linarith) hy.2.2
    linarith [le_eulerCross_of_mem hmem]

/-- A larger right side raises the crossing point (the monotonicity of `T`, Exercise 18.7). -/
theorem eulerCross_mono_rhs {Z' : ℝ → Prop} {R' : ℝ → ℝ}
    (hZ : ∀ y, 0 ≤ y → y < P → Z y → Z' y)
    (hRR : ∀ y, 0 ≤ y → y < P → ¬ Z y → ¬ Z' y → R y ≤ R' y)
    (h0 : (eulerSet u Z R P).Nonempty) :
    eulerCross u Z R P ≤ eulerCross u Z' R' P := by
  refine csSup_le_csSup bddAbove_eulerSet h0 fun y hy => ⟨hy.1, hy.2.1, ?_⟩
  rcases hy.2.2 with h | h
  · exact Or.inl (hZ y hy.1 hy.2.1 h)
  · by_cases hz' : Z' y
    · exact Or.inl hz'
    · by_cases hz : Z y
      · exact Or.inl (hZ y hy.1 hy.2.1 hz)
      · exact Or.inr (h.trans_le (hRR y hy.1 hy.2.1 hz hz'))

/-- **The crossing point solves the Euler equation, or there is no interior solution.** If the
left side lies below the right side at `y = 0`, then either the crossing point `y*` is `< P`,
the next-period consumption at `y*` is positive (`¬ Z y*`) and `u (P − y*) = R y*`; or `y* = P`
and the right side is `+∞` on all of `[0, P)`. -/
theorem eulerCross_spec (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hP : 0 < P)
    (hPB : P ≤ B) (h0 : EulerBelow u Z R P 0) :
    (eulerCross u Z R P < P ∧ ¬ Z (eulerCross u Z R P) ∧
      u (P - eulerCross u Z R P) = R (eulerCross u Z R P)) ∨
    (eulerCross u Z R P = P ∧ ∀ y, 0 ≤ y → y < P → Z y) := by
  set y := eulerCross u Z R P with hydef
  have hne : (eulerSet u Z R P).Nonempty := ⟨0, le_rfl, hP, h0⟩
  have hy0 : 0 ≤ y := eulerCross_nonneg
  have hyP : y ≤ P := eulerCross_le hP.le
  rcases hyP.lt_or_eq with hlt | heq
  · left
    have hyB : y ∈ Icc 0 B := ⟨hy0, hlt.le.trans hPB⟩
    -- a point `y'` slightly above `y` that would lie in `eulerSet`
    have key : ∀ δ > 0, ∃ y', y < y' ∧ y' < P ∧ y' ∈ Metric.ball y δ ∩ Icc 0 B ∧
        P - (y + P) / 2 ≤ P - y' := by
      intro δ hδ
      refine ⟨y + min (δ / 2) ((P - y) / 2), ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · have : 0 < min (δ / 2) ((P - y) / 2) := lt_min (by linarith) (by linarith)
        linarith
      · linarith [min_le_right (δ / 2) ((P - y) / 2)]
      · rw [Metric.mem_ball, Real.dist_eq]
        have h1 : 0 < min (δ / 2) ((P - y) / 2) := lt_min (by linarith) (by linarith)
        rw [abs_of_pos (by linarith)]
        linarith [min_le_left (δ / 2) ((P - y) / 2)]
      · have : 0 < min (δ / 2) ((P - y) / 2) := lt_min (by linarith) (by linarith)
        linarith
      · linarith [min_le_right (δ / 2) ((P - y) / 2)]
      · linarith [min_le_right (δ / 2) ((P - y) / 2)]
    have hZ : ¬ Z y := by
      intro hz
      have hev := hR.blowup y hyB hz (u (P - (y + P) / 2))
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      obtain ⟨y', hyy', hy'P, hy'm, hc⟩ := key δ hδ
      have hmem : y' ∈ eulerSet u Z R P := by
        refine ⟨by linarith, hy'P, ?_⟩
        rcases hball hy'm with h | h
        · exact Or.inl h
        · right
          exact (hu.strictAnti.antitoneOn (mem_Ioi.2 (by linarith))
            (mem_Ioi.2 (by linarith)) hc).trans_lt h
      linarith [le_eulerCross_of_mem hmem]
    refine ⟨hlt, hZ, ?_⟩
    have hcont := (hR.cont y hyB hZ).2
    have hcu : ContinuousWithinAt (fun z => u (P - z)) (Icc 0 B) y :=
      ((hu.cont.continuousAt (Ioi_mem_nhds (by linarith : (0 : ℝ) < P - y))).comp
        (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
    rcases lt_trichotomy (u (P - y)) (R y) with hl | he | hg
    · exfalso
      have hev : ∀ᶠ z in 𝓝[Icc 0 B] y, u (P - z) < R z := hcu.eventually_lt hcont hl
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      obtain ⟨y', hyy', hy'P, hy'm, -⟩ := key δ hδ
      have hmem : y' ∈ eulerSet u Z R P := ⟨by linarith, hy'P, Or.inr (hball hy'm)⟩
      linarith [le_eulerCross_of_mem hmem]
    · exact he
    · exfalso
      have hev : ∀ᶠ z in 𝓝[Icc 0 B] y, ¬ Z z ∧ R z < u (P - z) :=
        (hR.cont y hyB hZ).1.and (hcont.eventually_lt hcu hg)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne (show y - δ < y by linarith)
      have hzy : z ≤ y := le_eulerCross_of_mem hz
      have hzm : z ∈ Metric.ball y δ ∩ Icc 0 B := by
        refine ⟨?_, hz.1, hz.2.1.le.trans hPB⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      obtain ⟨hnz, hlt'⟩ := hball hzm
      rcases hz.2.2 with h | h
      · exact hnz h
      · linarith
  · right
    refine ⟨heq, fun y0 hy00 hy0P => ?_⟩
    by_contra hnz
    obtain ⟨ε, hε, hεu⟩ : ∃ ε > 0, ∀ c, 0 < c → c < ε → R y0 < u c := by
      have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), R y0 < u c := hu.inada.eventually_gt_atTop (R y0)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      refine ⟨ε, hε, fun c hc0 hcε => hball ⟨?_, hc0⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc0]
      exact hcε
    set y1 := max y0 (P - ε / 2)
    have hy1P : y1 < P := max_lt hy0P (by linarith)
    have hy01 : y0 ≤ y1 := le_max_left _ _
    have hnz1 : ¬ Z y1 := fun h =>
      hnz (hR.zero_anti y1 y0 hy00 hy01 (hy1P.le.trans hPB) h)
    have hnb : ¬ EulerBelow u Z R P y1 := by
      rintro (h | h)
      · exact hnz1 h
      · have h1 : R y1 ≤ R y0 := hR.anti y1 y0 hy00 hy01 (hy1P.le.trans hPB) hnz
        have h2 : R y0 < u (P - y1) :=
          hεu _ (by linarith) (by linarith [le_max_right y0 (P - ε / 2)])
        linarith
    have := eulerCross_le_of_not_below hu hR hPB (hy00.trans hy01) hnb
    linarith

/-- If the left side is not below the right side at `0`, then `eulerSet` is empty and the
crossing point is `0`. -/
theorem eulerCross_eq_zero_of_not_below (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R)
    (hPB : P ≤ B) (h0 : ¬ EulerBelow u Z R P 0) : eulerCross u Z R P = 0 := by
  have hempty : eulerSet u Z R P = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y hy => h0 ?_
    exact eulerBelow_of_le hu hR le_rfl hy.1 (hy.2.1.le.trans hPB) (by linarith [hy.2.1])
      (by linarith [hy.1]) hy.2.2
  rw [eulerCross, hempty, Real.sSup_empty]

/-- **Kuhn–Tucker form of `eulerCross_spec`** (no interiority assumption at `0`). Exactly one of:
an interior solution of the Euler equation; a corner with zero consumption (`y* = P`, the right
side `+∞` on `[0, P)`); or a corner with zero saving (`y* = 0`, with `R 0 ≤ u P`: the Euler
equation holds as the inequality of a Kuhn–Tucker condition). -/
theorem eulerCross_spec_KT (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hP : 0 < P)
    (hPB : P ≤ B) :
    (eulerCross u Z R P < P ∧ ¬ Z (eulerCross u Z R P) ∧
      u (P - eulerCross u Z R P) = R (eulerCross u Z R P)) ∨
    (eulerCross u Z R P = P ∧ ∀ y, 0 ≤ y → y < P → Z y) ∨
    (eulerCross u Z R P = 0 ∧ ¬ Z 0 ∧ R 0 ≤ u P) := by
  by_cases h0 : EulerBelow u Z R P 0
  · rcases eulerCross_spec hu hR hP hPB h0 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨eulerCross_eq_zero_of_not_below hu hR hPB h0, fun h => h0 (Or.inl h),
      ?_⟩)
    by_contra hlt
    exact h0 (Or.inr (by simpa using lt_of_not_ge hlt))

/-- `eulerCross_mono` without the nonemptiness assumption. -/
theorem eulerCross_mono' (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPP : P ≤ P') (hPB : P' ≤ B) : eulerCross u Z R P ≤ eulerCross u Z R P' := by
  rcases (eulerSet u Z R P).eq_empty_or_nonempty with h | h
  · rw [eulerCross, h, Real.sSup_empty]; exact eulerCross_nonneg
  · exact eulerCross_mono hu hR hPP hPB h

/-- `eulerCross_mono_rhs` without the nonemptiness assumption. -/
theorem eulerCross_mono_rhs' {Z' : ℝ → Prop} {R' : ℝ → ℝ}
    (hZ : ∀ y, 0 ≤ y → y < P → Z y → Z' y)
    (hRR : ∀ y, 0 ≤ y → y < P → ¬ Z y → ¬ Z' y → R y ≤ R' y) :
    eulerCross u Z R P ≤ eulerCross u Z' R' P := by
  rcases (eulerSet u Z R P).eq_empty_or_nonempty with h | h
  · rw [eulerCross, h, Real.sSup_empty]; exact eulerCross_nonneg
  · exact eulerCross_mono_rhs hZ hRR h

/-- The crossing point is `1`-Lipschitz in the current resources `P` (for a fixed right side). -/
theorem abs_eulerCross_sub_le (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) {P' : ℝ}
    (hPB : P ≤ B) (hP'B : P' ≤ B) :
    |eulerCross u Z R P' - eulerCross u Z R P| ≤ |P' - P| := by
  rcases le_total P P' with h | h
  · have h1 := eulerCross_mono' hu hR h hP'B
    have h2 := eulerCross_le_add_sub hu hR h hP'B
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have h1 := eulerCross_mono' hu hR h hPB
    have h2 := eulerCross_le_add_sub hu hR h hPB
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- **Uniqueness.** An interior solution `y ∈ [0, P)` of the Euler equation with positive
next-period consumption is the crossing point. -/
theorem eulerCross_unique (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R) (hPB : P ≤ B)
    {y : ℝ} (hy0 : 0 ≤ y) (hyP : y < P) (hZ : ¬ Z y) (heq : u (P - y) = R y) :
    eulerCross u Z R P = y := by
  refine le_antisymm (eulerCross_le_of_not_below hu hR hPB hy0 ?_) ?_
  · rintro (h | h)
    · exact hZ h
    · exact h.ne heq
  · refine le_eulerCross_of_forall fun z hz0 hzy => ⟨hz0, hzy.trans hyP, ?_⟩
    by_cases hz : Z z
    · exact Or.inl hz
    · right
      have h1 : u (P - z) < u (P - y) :=
        hu.strictAnti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
      exact h1.trans_le (heq.trans_le (hR.anti y z hz0 hzy.le (hyP.le.trans hPB) hz))

/-- Pointwise convergence of a family of right sides `(Zs a, Rs a)` to `(Z, R)` at the point
`y`, in the extended-real sense: if `Z y` (the limit is `+∞`) the right sides eventually exceed
every bound, and otherwise they are eventually finite and converge to `R y`. -/
def RHSConvergesAt {α : Type*} (l : Filter α) (Zs : α → ℝ → Prop) (Rs : α → ℝ → ℝ)
    (Z : ℝ → Prop) (R : ℝ → ℝ) (y : ℝ) : Prop :=
  (Z y → ∀ M : ℝ, ∀ᶠ a in l, Zs a y ∨ M < Rs a y) ∧
    (¬ Z y → (∀ᶠ a in l, ¬ Zs a y) ∧ Tendsto (fun a => Rs a y) l (𝓝 (R y)))

/-- **Pointwise continuity of the crossing point** (the pointwise step of Exercise 18.6). If the
right sides `(Zs a, Rs a)` converge to `(Z, R)` at every `y ∈ [0, P)` and each of them lies
above the left side at `0`, then the crossing points converge. -/
theorem eventually_abs_eulerCross_sub_le {α : Type*} {l : Filter α} {Zs : α → ℝ → Prop}
    {Rs : α → ℝ → ℝ} (hu : IsMarginalUtility u) (hR : IsEulerRHS B Z R)
    (hRs : ∀ a, IsEulerRHS B (Zs a) (Rs a)) (hP : 0 < P) (hPB : P ≤ B)
    (hconv : ∀ y, 0 ≤ y → y < P → RHSConvergesAt l Zs Rs Z R y) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a in l, |eulerCross u (Zs a) (Rs a) P - eulerCross u Z R P| ≤ η := by
  set y := eulerCross u Z R P
  have hy0 : 0 ≤ y := eulerCross_nonneg
  have hyP : y ≤ P := eulerCross_le hP.le
  -- lower bound
  have hlow : ∀ᶠ a in l, y - η ≤ eulerCross u (Zs a) (Rs a) P := by
    rcases le_or_gt y η with hyη | hyη
    · refine Eventually.of_forall fun a => ?_
      have : 0 ≤ eulerCross u (Zs a) (Rs a) P := eulerCross_nonneg
      linarith
    · have hz : y - η ∈ eulerSet u Z R P :=
        mem_eulerSet_of_lt hu hR hPB (by linarith) (by linarith)
      have hzP : y - η < P := hz.2.1
      have hc := hconv (y - η) hz.1 hzP
      have hev : ∀ᶠ a in l, EulerBelow u (Zs a) (Rs a) P (y - η) := by
        rcases hz.2.2 with h | h
        · exact (hc.1 h (u (P - (y - η)))).mono fun a ha => ha
        · by_cases hZz : Z (y - η)
          · exact (hc.1 hZz (u (P - (y - η)))).mono fun a ha => ha
          · exact ((hc.2 hZz).2.eventually_const_lt h).mono fun a ha => Or.inr ha
      exact hev.mono fun a ha => le_eulerCross_of_mem ⟨hz.1, hzP, ha⟩
  -- upper bound
  have hup : ∀ᶠ a in l, eulerCross u (Zs a) (Rs a) P ≤ y + η := by
    rcases le_or_gt P (y + η) with hPη | hPη
    · exact Eventually.of_forall fun a => (eulerCross_le hP.le).trans hPη
    · have hz'nb : ¬ EulerBelow u Z R P (y + η / 2) := by
        intro h
        have := le_eulerCross_of_mem (show y + η / 2 ∈ eulerSet u Z R P from
          ⟨by linarith, by linarith, h⟩)
        linarith
      have hnZ' : ¬ Z (y + η / 2) := fun h => hz'nb (Or.inl h)
      have hR' : R (y + η / 2) ≤ u (P - (y + η / 2)) := not_lt.1 fun h => hz'nb (Or.inr h)
      have hnZ : ¬ Z (y + η) := fun h =>
        hnZ' (hR.zero_anti _ _ (by linarith) (by linarith) (hPη.le.trans hPB) h)
      have hRz : R (y + η) < u (P - (y + η)) := by
        have h1 := hR.anti (y + η) (y + η / 2) (by linarith) (by linarith) (hPη.le.trans hPB)
          hnZ'
        have h2 : u (P - (y + η / 2)) < u (P - (y + η)) :=
          hu.strictAnti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
        linarith
      have hc := (hconv (y + η) (by linarith) hPη).2 hnZ
      have hev : ∀ᶠ a in l, ¬ EulerBelow u (Zs a) (Rs a) P (y + η) :=
        (hc.1.and (hc.2.eventually_lt_const hRz)).mono fun a ha => by
          rintro (h | h)
          · exact ha.1 h
          · linarith [ha.2]
      exact hev.mono fun a ha =>
        eulerCross_le_of_not_below hu (hRs a) hPB (by linarith) ha
  filter_upwards [hlow, hup] with a h1 h2
  rw [abs_le]
  constructor <;> linarith

end StokeyLucasPrescott.EquilibriaWithDistortions
