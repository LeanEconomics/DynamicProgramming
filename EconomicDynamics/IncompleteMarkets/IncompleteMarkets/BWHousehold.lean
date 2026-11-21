/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# §17.2.1: the Huggett endowment economy, Definition 17.2.1 and Proposition 17.2.1

Miao, §17.1.1, pp. 560–562 (the household's problem (17.2), (17.4) and the stationary
distribution (17.7)) and §17.2.1, pp. 570–571 (Definition 17.2.1, Proposition 17.2.1).

A household receives the endowment `e(s)` in the idiosyncratic state `s ∈ E`, which follows a
Markov process with transition kernel `Q`. Given the risk-free rate `r` and the debt limit `φ`
it solves the Bellman equation (17.4)
`V(a, s) = max_{a' ∈ [−φ, (1 + r)a + e(s)]} u((1 + r)a + e(s) − a') + β ∫ V(a', s′) Q(ds′, s)`
(the budget (17.2) with `w = 1`, `c ≥ 0`, and the borrowing constraint (17.3a)).

* `BWEconomy`: the primitives `(β, u, Q, e)`. `BWEconomy.Bellman r φ y V g`: `V` solves (17.4)
  for the endowment `y`, the maximum attained by the policy `g`.
* `BWEconomy.Stationary g lam`: the stationarity condition (17.8) (= (17.7)),
  `λ(A × B) = ∫ 1_A(g(a, s)) Q(B, s) dλ(a, s)` for measurable rectangles.
* `BWEconomy.EaSet r φ y`: the set of long-run average asset holdings `Ea(r) = ∫ g dλ` over all
  solutions `(V, g)` of (17.4) and all stationary distributions `λ` of `g` on `S = [−φ, ∞) × E`.
  The book writes `Ea(r)` as a function; we do not assume that the solution and the stationary
  distribution are unique.
* `BWHuggettEqm H φ`: **Definition 17.2.1**; `definition_17_2_1`: `r` is an equilibrium rate iff
  `0 ∈ Ea(r)` ("the intersection of the `Ea(r)` curve with the vertical axis", p. 571).
* The change of variables `â = a + d` (`bw_bellman_shift`, `bw_stationary_shift`,
  `bw_EaSet_shift`): the problem with rate `r`, limit `φ` and endowment `y` is the problem with
  limit `φ − d` and endowment `y − rd`; asset holdings shift by `d`.
* **Proposition 17.2.1** (`proposition_17_2_1`, `proposition_17_2_1_policy`): at `r = 0` the
  shift does not change the endowment, so `Ea(0; b) = Ea(0; 0) − b`.
* `bw_natural_limit`: (17.4) has a solution only if `rφ ≤ e(s)` for every `s` (nonnegative
  consumption at the debt limit), i.e. `φ ≤ e_min/r` for `r > 0`: the natural borrowing limit.

**Departures.** (1) `Ea(r)` is a set (see above). (2) The book's proof of Proposition 17.2.1 ends
with the typo `Ea(0; b) = Ea(0; b) − b`; the statement (`Ea(0; 0) − b`) is what is proved.
(3) The Bellman equation carries the integrability of `V(a′, ·)` under `Q(·, s)`, which the book
leaves implicit.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **Huggett endowment economy** (Miao, §17.2.1, p. 570): discount factor `β`, utility
`u`, the transition kernel `Q` of the idiosyncratic state and the endowment `e(s)` (`w = 1`). -/
structure BWEconomy (E : Type*) [MeasurableSpace E] where
  β : ℝ
  u : ℝ → ℝ
  Q : Kernel E E
  e : E → ℝ

variable {E : Type*} [MeasurableSpace E]

namespace BWEconomy

/-- Miao, (17.2)–(17.4), pp. 560–561: `V` solves the Bellman equation of the household with
rate `r`, debt limit `φ` (`a ≥ −φ`) and endowment `y`, the maximum being attained at `g(a, s)`.
Consumption `c = (1 + r)a + y(s) − a′ ≥ 0` gives the upper bound on `a′`. -/
def Bellman (H : BWEconomy E) (r φ : ℝ) (y : E → ℝ) (V g : ℝ → E → ℝ) : Prop :=
  ∀ a s, -φ ≤ a →
    g a s ∈ Set.Icc (-φ) ((1 + r) * a + y s) ∧
    (∀ a', -φ ≤ a' → Integrable (fun s' => V a' s') (H.Q s)) ∧
    V a s = H.u ((1 + r) * a + y s - g a s) + H.β * ∫ s', V (g a s) s' ∂(H.Q s) ∧
    ∀ a' ∈ Set.Icc (-φ) ((1 + r) * a + y s),
      H.u ((1 + r) * a + y s - a') + H.β * ∫ s', V a' s' ∂(H.Q s) ≤ V a s

/-- Miao, (17.7)–(17.8), pp. 562, 570: `λ` is a **stationary distribution** for the policy `g`,
`λ(A × B) = ∫ 1_A(g(a, s)) Q(B, s) dλ(a, s)` for all measurable `A ⊆ ℝ`, `B ⊆ E`. -/
def Stationary (H : BWEconomy E) (g : ℝ → E → ℝ) (lam : Measure (ℝ × E)) : Prop :=
  ∀ A B, MeasurableSet A → MeasurableSet B →
    lam (A ×ˢ B) = ∫⁻ p, A.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2) * H.Q p.2 B ∂lam

/-- Miao, p. 562: the **long-run average assets** `Ea(r) = ∫ g dλ*`, as the set of values over
all solutions of (17.4) with debt limit `φ` and endowment `y` and all stationary probability
distributions on `S = [−φ, ∞) × E` with integrable `g`. -/
def EaSet (H : BWEconomy E) (r φ : ℝ) (y : E → ℝ) : Set ℝ :=
  {m | ∃ (V g : ℝ → E → ℝ) (lam : Measure (ℝ × E)), IsProbabilityMeasure lam ∧
    lam {p | p.1 < -φ} = 0 ∧ H.Bellman r φ y V g ∧ H.Stationary g lam ∧
    Integrable (fun p => g p.1 p.2) lam ∧ m = ∫ p, g p.1 p.2 ∂lam}

end BWEconomy

/-- The shift `(a, s) ↦ (a + d, s)` of the state space. -/
noncomputable def bw_shift (d : ℝ) : ℝ × E ≃ᵐ ℝ × E :=
  (MeasurableEquiv.addRight d).prodCongr (MeasurableEquiv.refl E)

theorem bw_shift_apply (d : ℝ) (p : ℝ × E) : bw_shift d p = (p.1 + d, p.2) := rfl

/-- Miao, p. 571 (proof of Proposition 17.2.1), for any `r`: with `â = a + d` the budget
`c + a′ = (1 + r)a + y` becomes `c + â′ = (1 + r)â + y − rd` and `a′ ≥ −φ` becomes
`â′ ≥ −(φ − d)`; so `V̂(â) = V(â − d)`, `ĝ(â) = g(â − d) + d` solve the problem with limit
`φ − d` and endowment `y − rd`. -/
theorem bw_bellman_shift {H : BWEconomy E} {r φ d φ' : ℝ} {y y' : E → ℝ} {V g : ℝ → E → ℝ}
    (h : H.Bellman r φ y V g) (hφ : φ' = φ - d) (hy : ∀ s, y' s = y s - r * d) :
    H.Bellman r φ' y' (fun x s => V (x - d) s) (fun x s => g (x - d) s + d) := by
  intro x s hx
  subst hφ
  have hx' : -φ ≤ x - d := by linarith
  obtain ⟨hg, hint, hV, hmax⟩ := h (x - d) s hx'
  have key : (1 + r) * x + y' s = (1 + r) * (x - d) + y s + d := by rw [hy]; ring
  refine ⟨?_, fun a' ha' => hint (a' - d) (by linarith), ?_, fun a' ha' => ?_⟩
  · rw [key]; exact ⟨by linarith [hg.1], by linarith [hg.2]⟩
  · simp only [key, add_sub_cancel_right]
    rw [show (1 + r) * (x - d) + y s + d - (g (x - d) s + d) =
      (1 + r) * (x - d) + y s - g (x - d) s by ring]
    exact hV
  · rw [key] at ha' ⊢
    have := hmax (a' - d) ⟨by linarith [ha'.1], by linarith [ha'.2]⟩
    rwa [show (1 + r) * (x - d) + y s + d - a' = (1 + r) * (x - d) + y s - (a' - d) by ring]

/-- The shift of a solution is reversible: (17.4) with `(φ, y)` has the solution `(V, g)` iff
(17.4) with `(φ − d, y − rd)` has the shifted solution. -/
theorem bw_bellman_shift_iff {H : BWEconomy E} {r φ d : ℝ} {y : E → ℝ} {V g : ℝ → E → ℝ} :
    H.Bellman r φ y V g ↔ H.Bellman r (φ - d) (fun s => y s - r * d)
      (fun x s => V (x - d) s) (fun x s => g (x - d) s + d) := by
  refine ⟨fun h => bw_bellman_shift h rfl fun _ => rfl, fun h => ?_⟩
  have := bw_bellman_shift (d := -d) (φ' := φ) (y' := y) h (by ring) (fun s => by ring)
  simpa only [sub_neg_eq_add, add_sub_cancel_right, add_neg_cancel_right] using this

/-- Stationarity is preserved by the shift: if `λ` is stationary for `g`, then its image under
`(a, s) ↦ (a + d, s)` is stationary for `ĝ(â, s) = g(â − d, s) + d`. -/
theorem bw_stationary_shift {H : BWEconomy E} {g : ℝ → E → ℝ} {lam : Measure (ℝ × E)}
    (h : H.Stationary g lam) (d : ℝ) :
    H.Stationary (fun x s => g (x - d) s + d) (lam.map (bw_shift d)) := by
  intro A B hA hB
  have hA' : MeasurableSet ((fun x : ℝ => x + d) ⁻¹' A) := (measurable_id.add_const d) hA
  have hpre : (bw_shift (E := E) d) ⁻¹' (A ×ˢ B) = ((fun x : ℝ => x + d) ⁻¹' A) ×ˢ B := by
    ext p; simp [bw_shift_apply]
  rw [MeasurableEquiv.map_apply, hpre, h _ B hA' hB, lintegral_map_equiv]
  refine lintegral_congr fun p => ?_
  simp only [bw_shift_apply, add_sub_cancel_right]
  by_cases hm : g p.1 p.2 + d ∈ A
  · simp [Set.indicator, hm]
  · simp [Set.indicator, hm]

/-- The support condition `λ{a < −φ} = 0` is preserved by the shift (with limit `φ − d`). -/
theorem bw_supp_shift {lam : Measure (ℝ × E)} {φ : ℝ} (h : lam {p | p.1 < -φ} = 0) (d : ℝ) :
    lam.map (bw_shift d) {p | p.1 < -(φ - d)} = 0 := by
  rw [MeasurableEquiv.map_apply]
  convert h using 2
  ext p
  simp only [Set.mem_preimage, bw_shift_apply, Set.mem_ofPred_eq]
  constructor <;> intro hp <;> linarith

/-- Integrability of the shifted policy. -/
theorem bw_integrable_shift {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {g : ℝ → E → ℝ}
    (h : Integrable (fun p => g p.1 p.2) lam) (d : ℝ) :
    Integrable (fun p : ℝ × E => g (p.1 - d) p.2 + d) (lam.map (bw_shift d)) := by
  rw [integrable_map_equiv]
  simpa [Function.comp_def, bw_shift_apply] using h.add (integrable_const d)

/-- Mean asset holdings shift by `d`: `∫ ĝ d(shift λ) = ∫ g dλ + d`. -/
theorem bw_integral_shift {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {g : ℝ → E → ℝ}
    (h : Integrable (fun p => g p.1 p.2) lam) (d : ℝ) :
    ∫ p, (g (p.1 - d) p.2 + d) ∂(lam.map (bw_shift d)) = ∫ p, g p.1 p.2 ∂lam + d := by
  rw [integral_map_equiv]
  simp only [bw_shift_apply, add_sub_cancel_right]
  rw [integral_add h (integrable_const d)]
  simp

/-- The image of a probability measure under the shift is a probability measure. -/
theorem bw_isProb_shift {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] (d : ℝ) :
    IsProbabilityMeasure (lam.map (bw_shift d)) :=
  (Measure.isProbabilityMeasure_map_iff (bw_shift d).measurable.aemeasurable).2 inferInstance

/-- Miao, p. 571: if `m ∈ Ea(r)` for limit `φ` and endowment `y`, then `m + d ∈ Ea(r)` for
limit `φ − d` and endowment `y − rd`. -/
theorem bw_EaSet_shift {H : BWEconomy E} {r φ d φ' m : ℝ} {y y' : E → ℝ}
    (hm : m ∈ H.EaSet r φ y) (hφ : φ' = φ - d) (hy : ∀ s, y' s = y s - r * d) :
    m + d ∈ H.EaSet r φ' y' := by
  obtain ⟨V, g, lam, hP, hsupp, hB, hS, hI, rfl⟩ := hm
  refine ⟨fun x s => V (x - d) s, fun x s => g (x - d) s + d, lam.map (bw_shift d),
    bw_isProb_shift d, ?_, bw_bellman_shift hB hφ hy, bw_stationary_shift hS d,
    bw_integrable_shift hI d, (bw_integral_shift hI d).symm⟩
  rw [hφ]
  exact bw_supp_shift hsupp d

/-- The change of variables as an identity of sets: `Ea(r; φ − d, y − rd) = Ea(r; φ, y) + d`. -/
theorem bw_EaSet_shift_eq (H : BWEconomy E) (r φ d : ℝ) (y : E → ℝ) :
    H.EaSet r (φ - d) (fun s => y s - r * d) = (fun m => m + d) '' H.EaSet r φ y := by
  ext m
  refine ⟨fun hm => ⟨m - d, ?_, by ring⟩, ?_⟩
  · have := bw_EaSet_shift (d := -d) (φ' := φ) (y' := y) hm (by ring) (fun s => by ring)
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg] using this
  · rintro ⟨m', hm', rfl⟩
    exact bw_EaSet_shift hm' rfl fun _ => rfl

/-- **Proposition 17.2.1** (Miao, p. 571), policy form. At `r = 0`, with `â = a + b`, the
problem with debt limit `b` is the problem with limit `0` for the same endowment: `(V, g)`
solves (17.4) with limit `b` iff `V̂(â) = V(â − b)`, `ĝ(â) = g(â − b) + b` solve it with limit
`0`. So the optimal policy for `â` is independent of `b`: `g(a; b) + b = ĝ(a + b; 0)`. -/
theorem proposition_17_2_1_policy (H : BWEconomy E) (b : ℝ) (y : E → ℝ) (V g : ℝ → E → ℝ) :
    H.Bellman 0 b y V g ↔
      H.Bellman 0 0 y (fun x s => V (x - b) s) (fun x s => g (x - b) s + b) := by
  rw [bw_bellman_shift_iff (d := b)]
  simp only [sub_self, zero_mul, sub_zero]

/-- **Proposition 17.2.1** (Miao, p. 571). When `r = 0`, `Ea(0; b) = Ea(0; 0) − b`: the set of
long-run average asset holdings with debt limit `b` is that with limit `0` shifted by `−b`. -/
theorem proposition_17_2_1 (H : BWEconomy E) (b : ℝ) (y : E → ℝ) :
    H.EaSet 0 b y = (fun m => m - b) '' H.EaSet 0 0 y := by
  have h := bw_EaSet_shift_eq H 0 b b y
  simp only [sub_self, zero_mul, sub_zero] at h
  rw [h, Set.image_image]
  simp

/-- Miao, (17.3), p. 560: the problem (17.4) has a solution only if consumption can be
nonnegative at the debt limit, `−φ ≤ (1 + r)(−φ) + y(s)`, i.e. `rφ ≤ y(s)` for every state:
with `r > 0` the debt limit cannot exceed the natural borrowing limit `y_min/r`. -/
theorem bw_natural_limit {H : BWEconomy E} {r φ : ℝ} {y : E → ℝ} {V g : ℝ → E → ℝ}
    (h : H.Bellman r φ y V g) (s : E) : r * φ ≤ y s := by
  obtain ⟨hg, -⟩ := h (-φ) s le_rfl
  have h1 := hg.1.trans hg.2
  have : (1 + r) * -φ = -φ - r * φ := by ring
  linarith

/-- **Definition 17.2.1** (Miao, p. 570). A **stationary recursive competitive equilibrium** of
the Huggett economy with debt limit `φ`: a value function `V`, an asset policy `g`, a risk-free
rate `r` and a stationary probability measure `λ*` on `S = [−φ, ∞) × E` such that (i) `g` solves
the household's problem (17.4) and `V` is its value function, (ii) the asset market clears,
`∫ g dλ* = 0`, and (iii) `λ*` is stationary, (17.8). -/
structure BWHuggettEqm (H : BWEconomy E) (φ : ℝ) where
  V : ℝ → E → ℝ
  g : ℝ → E → ℝ
  r : ℝ
  lam : Measure (ℝ × E)
  isProb : IsProbabilityMeasure lam
  supp : lam {p | p.1 < -φ} = 0
  bellman : H.Bellman r φ H.e V g
  integrable : Integrable (fun p => g p.1 p.2) lam
  clear : ∫ p, g p.1 p.2 ∂lam = 0
  stationary : H.Stationary g lam

/-- **Definition 17.2.1** (Miao, pp. 570–571): `r` is a stationary equilibrium rate of the Huggett
economy with debt limit `φ` iff `0 ∈ Ea(r)`, i.e. the equilibrium rate is where the `Ea(r)` curve
meets the vertical axis (Figure 17.3). -/
theorem definition_17_2_1 (H : BWEconomy E) (φ r : ℝ) :
    (∃ eqm : BWHuggettEqm H φ, eqm.r = r) ↔ 0 ∈ H.EaSet r φ H.e := by
  constructor
  · rintro ⟨eqm, rfl⟩
    exact ⟨eqm.V, eqm.g, eqm.lam, eqm.isProb, eqm.supp, eqm.bellman, eqm.stationary,
      eqm.integrable, eqm.clear.symm⟩
  · rintro ⟨V, g, lam, hP, hsupp, hB, hS, hI, h0⟩
    exact ⟨⟨V, g, r, lam, hP, hsupp, hB, hI, h0.symm, hS⟩, rfl⟩

end Miao.IncompleteMarkets
