/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.LCAutarky
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Function

/-!
# The Bellman equation with the promised value as the state (Miao §22.1.1, pp. 776–778)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.1, pp. 776–778. The principal's
value `P(θᵢ, v)` solves
`P(θᵢ, v) = max_{c, {wⱼ}} θᵢ − c + β Σⱼ π(θⱼ|θᵢ) P(θⱼ, wⱼ)` subject to the incentive
constraints (22.3) `wⱼ ≥ U_d(θⱼ)` and the promise-keeping constraint (22.4)
`u(c) + β Σⱼ π(θⱼ|θᵢ) wⱼ ≥ v`.

Proved here, for any solution `P` of the Bellman equation (`lc_Bellman`):
* the constraint set is convex and the Bellman operator maps concave `P` to concave `P`
  (`lc_feasible_convex`, `lc_bellman_concave`); `P` is decreasing in `v`;
* the promise-keeping constraint binds (`lc_promise_keeping_binds`);
* the first-order conditions (22.5)–(22.6) of the Lagrangian, the envelope condition (22.7),
  and (22.8)–(22.9). The envelope condition is derived by a perturbation argument (raise `v` and
  consumption together) instead of being assumed; the multipliers `λⱼ ≥ 0` with complementary
  slackness are constructed from one-sided perturbations of `wⱼ`;
* the two cases `λⱼ > 0` (the incentive constraint binds, `wⱼ = U_d(θⱼ)`, consumption rises and
  depends on `θⱼ` only: amnesia) and `λⱼ = 0` (consumption is unchanged);
* the optimal contract: next-period consumption is `max{h(θⱼ), c}` with `h(θⱼ)` the consumption
  at `(θⱼ, U_d(θⱼ))`, i.e. (22.11); consumption never falls and is eventually constant.

Correction. The book also states that for `λⱼ = 0`, (22.9) "implies that `wⱼ = v`", so that
`w = max{U_d(y), v}` and promised values never decrease. That is true when the endowments are
i.i.d. (`lc_iid_promised_value`), the case treated by Ljungqvist and Sargent, but false for a
general Markov chain: see `lc_promise_decrease_counterexample` in `LCInstances`.

Consumption is restricted to `c > 0`; the utility function enters through hypotheses
(strictly increasing on `(0, ∞)` with a continuous inverse `g`, derivative `du > 0`).
-/

namespace Miao.RecursiveContracts

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- Miao, (22.3)–(22.4), p. 776: `(c, w)` is feasible at `(θᵢ, v)`: `c > 0`, the incentive
constraints `wⱼ ≥ U_d(θⱼ)` and promise keeping `u(c) + β Σⱼ π(θⱼ|θᵢ) wⱼ ≥ v`. -/
def lc_feasible (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ) (i : ι) (v c : ℝ)
    (w : ι → ℝ) : Prop :=
  0 < c ∧ (∀ j, Ud j ≤ w j) ∧ v ≤ u c + β * ∑ j, pl i j * w j

/-- The Bellman objective `θᵢ − c + β Σⱼ π(θⱼ|θᵢ) P(θⱼ, wⱼ)` (Miao, p. 776). -/
def lc_obj (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (P : ι → ℝ → ℝ) (i : ι) (c : ℝ)
    (w : ι → ℝ) : ℝ :=
  θ i - c + β * ∑ j, pl i j * P j (w j)

/-- The set of attainable objective values at `(θᵢ, v)`. -/
def lc_valueSet (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v : ℝ) : Set ℝ :=
  {x | ∃ c w, lc_feasible β pl u Ud i v c w ∧ x = lc_obj β pl θ P i c w}

/-- Miao, p. 776: the Bellman equation holds at `(θᵢ, v)`: `P(θᵢ, v)` is the maximum. -/
def lc_BellmanAt (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v : ℝ) : Prop :=
  IsGreatest (lc_valueSet β pl θ u Ud P i v) (P i v)

/-- Miao, p. 776: `P` solves the Bellman equation at every state and promised value. -/
def lc_Bellman (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) : Prop :=
  ∀ i v, lc_BellmanAt β pl θ u Ud P i v

/-- `(c, w)` attains `P(θᵢ, v)`. -/
def lc_Optimal (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v c : ℝ) (w : ι → ℝ) : Prop :=
  lc_feasible β pl u Ud i v c w ∧ lc_obj β pl θ P i c w = P i v

/-- The upper bound part of the Bellman equation. -/
theorem lc_BellmanAt.lc_obj_le {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} {i : ι} {v : ℝ} (hB : lc_BellmanAt β pl θ u Ud P i v) {c : ℝ}
    {w : ι → ℝ} (hf : lc_feasible β pl u Ud i v c w) : lc_obj β pl θ P i c w ≤ P i v :=
  hB.2 ⟨c, w, hf, rfl⟩

/-- The Bellman maximum is attained. -/
theorem lc_BellmanAt.lc_exists_optimal {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ}
    {Ud : ι → ℝ} {P : ι → ℝ → ℝ} {i : ι} {v : ℝ} (hB : lc_BellmanAt β pl θ u Ud P i v) :
    ∃ c w, lc_Optimal β pl θ u Ud P i v c w := by
  obtain ⟨c, w, hf, he⟩ := hB.1
  exact ⟨c, w, hf, he.symm⟩

/-- Miao, p. 776: "the constraint set is convex": the set of `(v, c, w)` satisfying
(22.3)–(22.4) is convex when `u` is concave. -/
theorem lc_feasible_convex (β : ℝ) (pl : ι → ι → ℝ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Set.Ioi 0) u) (Ud : ι → ℝ) (i : ι) :
    Convex ℝ {p : ℝ × ℝ × (ι → ℝ) | lc_feasible β pl u Ud i p.1 p.2.1 p.2.2} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨(convex_Ioi (0 : ℝ)) hp1 hq1 ha hb hab, fun j => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := add_le_add (mul_le_mul_of_nonneg_left (hp2 j) ha)
      (mul_le_mul_of_nonneg_left (hq2 j) hb)
    rw [← add_mul, hab, one_mul] at this
    exact this
  · have hc := hu.2 (Set.mem_Ioi.mpr hp1) (Set.mem_Ioi.mpr hq1) ha hb hab
    simp only [smul_eq_mul] at hc
    have hs : ∑ j, pl i j * (a * p.2.2 j + b * q.2.2 j) =
        a * ∑ j, pl i j * p.2.2 j + b * ∑ j, pl i j * q.2.2 j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left hp3 ha, mul_le_mul_of_nonneg_left hq3 hb]

/-- Miao, p. 776: "the value function `P` is concave in `v`": if the continuation values
`P(θⱼ, ·)` are concave and `u` is concave, the Bellman maximum `Q(v)` at `θᵢ` is concave in `v`
(the Bellman operator preserves concavity). -/
theorem lc_bellman_concave {β : ℝ} (hβ : 0 ≤ β) {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ (Set.Ioi 0) u) (Ud : ι → ℝ) (P : ι → ℝ → ℝ)
    (hP : ∀ j, ConcaveOn ℝ Set.univ (P j)) (i : ι) (hpl : ∀ j, 0 ≤ pl i j) (Q : ℝ → ℝ)
    (hQ : ∀ v, IsGreatest (lc_valueSet β pl θ u Ud P i v) (Q v)) :
    ConcaveOn ℝ Set.univ Q := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨c1, w1, hf1, he1⟩ := (hQ x).1
  obtain ⟨c2, w2, hf2, he2⟩ := (hQ y).1
  have hconv := lc_feasible_convex β pl hu Ud i (x := (x, c1, w1)) hf1 (y := (y, c2, w2)) hf2
    ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_ofPred_eq] at hconv
  have hle := (hQ (a • x + b • y)).2 ⟨_, _, hconv, rfl⟩
  refine le_trans ?_ hle
  rw [he1, he2]
  simp only [lc_obj, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have hPj : ∀ j, a * P j (w1 j) + b * P j (w2 j) ≤ P j (a * w1 j + b * w2 j) := by
    intro j
    have := (hP j).2 (Set.mem_univ (w1 j)) (Set.mem_univ (w2 j)) ha hb hab
    simpa only [smul_eq_mul] using this
  have hs : a * ∑ j, pl i j * P j (w1 j) + b * ∑ j, pl i j * P j (w2 j) ≤
      ∑ j, pl i j * P j (a * w1 j + b * w2 j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_left (hPj j) (hpl j)
    linarith
  have hθ : θ i = a * θ i + b * θ i := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hs hβ]

/-- Miao, p. 776: `P(θᵢ, ·)` is decreasing in the promised value. -/
theorem lc_bellman_antitone {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P) (i : ι) : Antitone (P i) := by
  intro v v' hvv'
  obtain ⟨c, w, hf, he⟩ := (hB i v').1
  rw [he]
  exact (hB i v).lc_obj_le ⟨hf.1, hf.2.1, hvv'.trans hf.2.2⟩

/-- Miao, p. 777: "the promise-keeping constraint always binds": at an optimum
`u(c) + β Σⱼ π(θⱼ|θᵢ) wⱼ = v` (lowering `c` would otherwise raise the principal's value). -/
theorem lc_promise_keeping_binds {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ}
    {Ud : ι → ℝ} {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : lc_BellmanAt β pl θ u Ud P i v) (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hu : ContinuousAt u c) : u c + β * ∑ j, pl i j * w j = v := by
  obtain ⟨⟨hc, hw, hv⟩, he⟩ := hopt
  by_contra hne
  have hlt : v < u c + β * ∑ j, pl i j * w j := lt_of_le_of_ne hv (Ne.symm hne)
  set s := β * ∑ j, pl i j * w j
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousAt_iff.mp hu (u c + s - v) (by linarith)
  set y := c - min δ c / 2
  have hm : 0 < min δ c := lt_min hδ hc
  have hy : 0 < y := by have := min_le_right δ c; simp only [y]; linarith
  have hyd : dist y c < δ := by
    rw [Real.dist_eq, abs_lt]
    have := min_le_left δ c
    constructor <;> simp only [y] <;> linarith
  have huy := hδu hyd
  rw [Real.dist_eq, abs_lt] at huy
  have := hB.lc_obj_le (c := y) (w := w) ⟨hy, hw, by linarith [huy.1]⟩
  rw [← he] at this
  simp only [lc_obj, y] at this
  linarith

/-- The derivative of the inverse utility `g = u⁻¹` at `u(c)` is `1/u'(c)`. -/
theorem lc_inv_hasDerivAt {u g : ℝ → ℝ} (hg : Continuous g) (hug : ∀ a, u (g a) = a) {c du : ℝ}
    (hgu : g (u c) = c) (hu : HasDerivAt u du c) (hdu : du ≠ 0) :
    HasDerivAt g du⁻¹ (u c) := by
  refine HasDerivAt.of_local_left_inverse hg.continuousAt ?_ hdu (Eventually.of_forall hug)
  rw [hgu]
  exact hu

/-- Miao, (22.8), p. 777: the envelope condition `P_v(θᵢ, v) = −1/u'(c)`. Derived by raising the
promised value and current utility together: `v' ↦ P(θᵢ, v') + u⁻¹(u(c) + v' − v)` is minimised
at `v' = v`. -/
theorem eq_22_8 {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u g : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : ∀ v', lc_BellmanAt β pl θ u Ud P i v') (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (hgu : g (u c) = c)
    {du : ℝ} (hu : HasDerivAt u du c) (hdu : du ≠ 0) {p : ℝ} (hP : HasDerivAt (P i) p v) :
    p = -du⁻¹ := by
  obtain ⟨⟨hc, hw, hv⟩, he⟩ := hopt
  have hg' := lc_inv_hasDerivAt hg hug hgu hu hdu
  have hinner : HasDerivAt (fun v' => u c + (v' - v)) 1 v := by
    simpa using ((hasDerivAt_id v).sub_const v).const_add (u c)
  have hg2 : HasDerivAt g du⁻¹ (u c + (v - v)) := by rw [sub_self, add_zero]; exact hg'
  have hsum := hP.add (hg2.comp v hinner)
  have hmin : IsLocalMin (fun v' => P i v' + (g ∘ fun v' => u c + (v' - v)) v') v := by
    refine Eventually.of_forall fun v' => ?_
    have hfe : lc_feasible β pl u Ud i v' (g (u c + (v' - v))) w :=
      ⟨hgpos _, hw, by rw [hug]; linarith⟩
    have := (hB v').lc_obj_le hfe
    simp only [lc_obj] at this he
    simp only [Function.comp_apply, sub_self, add_zero, hgu]
    linarith
  have := hmin.hasDerivAt_eq_zero hsum
  linarith

/-- Miao, (22.7), p. 777: the envelope condition `P₂(θᵢ, v) = −μ`, where `μ = 1/u'(c) > 0` is the
multiplier of the promise-keeping constraint given by (22.5). -/
theorem eq_22_7 {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u g : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : ∀ v', lc_BellmanAt β pl θ u Ud P i v') (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (hgu : g (u c) = c)
    {du : ℝ} (hu : HasDerivAt u du c) (hdu : 0 < du) {p : ℝ} (hP : HasDerivAt (P i) p v) :
    let μ := du⁻¹
    0 < μ ∧ p = -μ :=
  ⟨inv_pos.mpr hdu, eq_22_8 hB hopt hg hgpos hug hgu hu hdu.ne' hP⟩

/-- The Lagrangian of the Bellman problem (Miao, p. 776):
`L = θᵢ − c + β Σⱼ πᵢⱼ P(θⱼ, wⱼ) + Σⱼ λⱼ (wⱼ − U_d(θⱼ)) + μ (u(c) + β Σⱼ πᵢⱼ wⱼ − v)`. -/
def lc_lagrangian (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) (u : ℝ → ℝ) (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v c : ℝ) (w lam : ι → ℝ) (μ : ℝ) : ℝ :=
  lc_obj β pl θ P i c w + ∑ j, lam j * (w j - Ud j) + μ * (u c + β * ∑ j, pl i j * w j - v)

/-- Miao, (22.5), p. 776: the first-order condition for `c`: `∂L/∂c = −1 + μ u'(c)`, which
vanishes iff `u'(c) = 1/μ`; then `μ > 0` because `u' > 0`. -/
theorem eq_22_5 (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ) {u : ℝ → ℝ} (Ud : ι → ℝ)
    (P : ι → ℝ → ℝ) (i : ι) (v : ℝ) (w lam : ι → ℝ) (μ : ℝ) {c du : ℝ}
    (hu : HasDerivAt u du c) (hdu : 0 < du) :
    HasDerivAt (fun c' => lc_lagrangian β pl θ u Ud P i v c' w lam μ) (-1 + μ * du) c ∧
      (-1 + μ * du = 0 ↔ du = 1 / μ) ∧ (-1 + μ * du = 0 → 0 < μ) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  · have h1 : HasDerivAt (fun c' => θ i - c') (-1) c := by
      simpa using (hasDerivAt_id c).const_sub (θ i)
    have h2 := ((hu.add_const (β * ∑ j, pl i j * w j)).sub_const v).const_mul μ
    have h3 := ((h1.add_const (β * ∑ j, pl i j * P j (w j))).add_const
      (∑ j, lam j * (w j - Ud j))).add h2
    convert h3 using 1
    funext c'
    simp only [lc_lagrangian, lc_obj, Pi.add_apply]
  · constructor
    · intro h
      have hμ : μ ≠ 0 := by rintro rfl; simp at h
      field_simp
      linarith
    · intro h
      have hμ : μ ≠ 0 := by rintro rfl; simp at h; linarith
      rw [h]; field_simp; ring
  · have : μ * du = 1 := by linarith
    by_contra hμ
    have : μ * du ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hμ) hdu.le
    linarith

/-- Replacing one coordinate of `w` changes a separable sum by the change in that term. -/
theorem lc_sum_update [DecidableEq ι] (F : ι → ℝ → ℝ) (w : ι → ℝ) (j : ι) (x : ℝ) :
    ∑ k, F k (Function.update w j x k) = ∑ k, F k (w k) + (F j x - F j (w j)) := by
  have : ∀ k, F k (Function.update w j x k) =
      F k (w k) + if k = j then F j x - F j (w j) else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- Miao, (22.6), p. 776: the first-order condition for `wⱼ`. The Lagrangian's partial
derivative in `wⱼ` is `β πᵢⱼ P₂(θⱼ, wⱼ) + λⱼ + μ β πᵢⱼ`; and at an optimum there is a multiplier
`λⱼ ≥ 0` with complementary slackness `λⱼ (wⱼ − U_d(θⱼ)) = 0` making it vanish, with
`μ = 1/u'(c)`. The multiplier is constructed by moving `wⱼ` and `c` together so that promise
keeping is unchanged (one-sided at a binding incentive constraint). -/
theorem eq_22_6 [DecidableEq ι] {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} {i : ι} {v c : ℝ} {w : ι → ℝ}
    (hB : lc_BellmanAt β pl θ u Ud P i v) (hopt : lc_Optimal β pl θ u Ud P i v c w)
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (hgu : g (u c) = c)
    {du : ℝ} (hu : HasDerivAt u du c) (hdu : 0 < du) (j : ι) (hpl : 0 ≤ pl i j) {q : ℝ}
    (hq : HasDerivAt (P j) q (w j)) (lam : ι → ℝ) (μ : ℝ) :
    HasDerivAt (fun x => lc_lagrangian β pl θ u Ud P i v c (Function.update w j x) lam μ)
        (β * pl i j * q + lam j + μ * β * pl i j) (w j) ∧
      ∃ lamj : ℝ, 0 ≤ lamj ∧ lamj * (w j - Ud j) = 0 ∧
        β * pl i j * q + lamj + du⁻¹ * β * pl i j = 0 := by
  constructor
  · have hL : (fun x => lc_lagrangian β pl θ u Ud P i v c (Function.update w j x) lam μ) =
        fun x => (lc_lagrangian β pl θ u Ud P i v c w lam μ - β * pl i j * P j (w j)
          - lam j * w j - μ * β * pl i j * w j) +
          (β * pl i j * P j x + lam j * x + μ * β * pl i j * x) := by
      funext x
      simp only [lc_lagrangian, lc_obj]
      rw [lc_sum_update (fun k y => pl i k * P k y), lc_sum_update (fun k y => lam k * (y - Ud k)),
        lc_sum_update (fun k y => pl i k * y)]
      ring
    rw [hL]
    have := ((hq.const_mul (β * pl i j)).add ((hasDerivAt_id (w j)).const_mul (lam j))).add
      ((hasDerivAt_id (w j)).const_mul (μ * β * pl i j))
    simp only [id, mul_one] at this
    exact this.const_add _
  obtain ⟨⟨hc, hw, hv⟩, he⟩ := hopt
  set D := β * pl i j * (du⁻¹ + q) with hD
  -- the perturbed objective
  set f : ℝ → ℝ := fun t => θ i - g (u c - β * pl i j * t) +
    β * (∑ k, pl i k * P k (w k) + (pl i j * P j (w j + t) - pl i j * P j (w j))) with hf
  have hfeas : ∀ t, Ud j - w j ≤ t → f t ≤ P i v := by
    intro t ht
    have hfe : lc_feasible β pl u Ud i v (g (u c - β * pl i j * t))
        (Function.update w j (w j + t)) := by
      refine ⟨hgpos _, fun k => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; simp only [Function.update_self]; linarith
        · rw [Function.update_of_ne hk]; exact hw k
      · rw [hug, lc_sum_update (fun k y => pl i k * y)]
        nlinarith
    have := hB.lc_obj_le hfe
    simp only [lc_obj] at this
    rw [lc_sum_update (fun k y => pl i k * P k y)] at this
    exact this
  have hf0 : f 0 = P i v := by
    simp only [hf, mul_zero, sub_zero, add_zero, hgu, sub_self]
    simpa only [lc_obj] using he
  have hg' := lc_inv_hasDerivAt hg hug hgu hu hdu.ne'
  have hinner : HasDerivAt (fun t => u c - β * pl i j * t) (-(β * pl i j)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (β * pl i j)).const_sub (u c)
  have hg2 : HasDerivAt g du⁻¹ (u c - β * pl i j * 0) := by rw [mul_zero, sub_zero]; exact hg'
  have hPj : HasDerivAt (fun t => P j (w j + t)) q 0 := by
    have h1 : HasDerivAt (fun t => w j + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (w j)
    have h2 : HasDerivAt (P j) q (w j + 0) := by rw [add_zero]; exact hq
    convert h2.comp 0 h1 using 1
    · rfl
    · ring
  have hfd : HasDerivAt f D 0 := by
    have := ((hg2.comp 0 hinner).const_sub (θ i)).add
      ((((hPj.const_mul (pl i j)).sub_const (pl i j * P j (w j))).const_add
        (∑ k, pl i k * P k (w k))).const_mul β)
    convert this using 1
    · funext x
      simp only [hf, Pi.add_apply, Function.comp_apply]
    · rw [hD]
      ring
  have hDle : D ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hT := hfd.tendsto_slope_zero_right
    have hev := (hT.eventually (lt_mem_nhds hpos)).and self_mem_nhdsWithin
    obtain ⟨t, ht, ht0⟩ := hev.exists
    simp only [zero_add, smul_eq_mul] at ht ht0
    have := hfeas t (by linarith [hw j])
    have hpos' : 0 < f t - f 0 := by
      by_contra hn
      push Not at hn
      have : t⁻¹ * (f t - f 0) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) hn
      linarith
    linarith
  refine ⟨-D, by linarith, ?_, by simp only [hD]; ring⟩
  rcases (hw j).lt_or_eq with hlt | heq
  · have hmax : IsLocalMax f 0 := by
      have : Set.Ioi (Ud j - w j) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by linarith)
      filter_upwards [this] with t ht
      rw [hf0]
      exact hfeas t (le_of_lt ht)
    have := hmax.hasDerivAt_eq_zero hfd
    rw [this]; ring
  · rw [heq]; ring

/-- Miao, (22.9), p. 777: combining (22.6) and (22.7),
`P_v(θⱼ, wⱼ) = P_v(θᵢ, v) − λⱼ / (β π(θⱼ|θᵢ))`. -/
theorem eq_22_9 {β πij q p lamj μ : ℝ} (hβ : 0 < β) (hπ : 0 < πij) (h7 : p = -μ)
    (h6 : β * πij * q + lamj + μ * β * πij = 0) : q = p - lamj / (β * πij) := by
  rw [h7]
  field_simp
  linarith

/-- Miao, p. 777, "States where `λᵢ > 0`": the incentive constraint binds, `wⱼ = U_d(θⱼ)`, and
next-period consumption is `h(θⱼ)`, the consumption at `(θⱼ, U_d(θⱼ))`, which depends on `θⱼ`
only (amnesia); it is strictly above current consumption. Here `cⱼ` is the consumption at
`(θⱼ, wⱼ)` given by the policy `σ`, and `P_v(θⱼ, wⱼ) ≥ −1/u'(cⱼ)`. -/
theorem lc_binding_case {β πij q lamj c : ℝ} {wj Udj : ℝ} {σ : ℝ → ℝ} {du : ℝ → ℝ}
    (hβ : 0 < β) (hπ : 0 < πij) (hc : 0 < c) (hcj : 0 < σ wj)
    (hdupos : ∀ x, 0 < x → 0 < du x) (hduanti : StrictAntiOn du (Set.Ioi 0))
    (hCS : lamj * (wj - Udj) = 0) (h6 : β * πij * q + lamj + (du c)⁻¹ * β * πij = 0)
    (henv : q = -(du (σ wj))⁻¹) (hlam : 0 < lamj) :
    wj = Udj ∧ σ wj = σ Udj ∧ c < σ wj := by
  have hw : wj = Udj := by
    rcases mul_eq_zero.mp hCS with h | h
    · linarith
    · linarith
  refine ⟨hw, by rw [hw], ?_⟩
  have h9 := eq_22_9 hβ hπ rfl h6
  rw [henv] at h9
  have hlt : (du c)⁻¹ < (du (σ wj))⁻¹ := by
    have : 0 < lamj / (β * πij) := div_pos hlam (mul_pos hβ hπ)
    linarith
  rw [inv_lt_inv₀ (hdupos c hc) (hdupos _ hcj)] at hlt
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · exact absurd (hduanti hcj hc h) (not_lt.mpr hlt.le)
  · rw [h] at hlt; exact lt_irrefl _ hlt

/-- Miao, p. 777, "States where `λᵢ = 0`": the incentive constraint does not bind and (22.9)
gives `P_v(θⱼ, wⱼ) = P_v(θᵢ, v)`, so by (22.8) next-period consumption equals current
consumption. -/
theorem lc_slack_case {β πij q c cj : ℝ} {du : ℝ → ℝ} (hc : 0 < c) (hcj : 0 < cj)
    (hduanti : StrictAntiOn du (Set.Ioi 0))
    (h6 : β * πij * q + 0 + (du c)⁻¹ * β * πij = 0) (hβπ : β * πij ≠ 0)
    (henv : q = -(du cj)⁻¹) : cj = c := by
  have : q = -(du c)⁻¹ := by
    have h : β * πij * (q + (du c)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hβπ
    · linarith
  rw [henv, neg_inj, inv_inj] at this
  exact hduanti.injOn hcj hc this

/-- Miao, p. 778, "The Optimal Contract", in the general Markov case. Let `σc, σw` be optimal
policies for a solution `P` of the Bellman equation, differentiable with `P_v(θⱼ, ·)` decreasing
(`P` concave). If `π(θⱼ|θᵢ) > 0`, next-period consumption after `θⱼ` is
`max{h(θⱼ), c}`, where `h(θⱼ) = σc(θⱼ, U_d(θⱼ))` is the consumption when the incentive
constraint binds; consumption never falls, and it rises only if the incentive constraint at
`θⱼ` binds (`wⱼ = U_d(θⱼ)`). -/
theorem lc_optimal_contract {β : ℝ} (hβ : 0 < β) {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P)
    (σc : ι → ℝ → ℝ) (σw : ι → ℝ → ι → ℝ)
    (hσ : ∀ k x, lc_Optimal β pl θ u Ud P k x (σc k x) (σw k x))
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (hgu : ∀ x, 0 < x → g (u x) = x) (du : ℝ → ℝ) (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdupos : ∀ x, 0 < x → 0 < du x) (hduanti : StrictAntiOn du (Set.Ioi 0))
    (dP : ι → ℝ → ℝ) (hdP : ∀ k x, HasDerivAt (P k) (dP k x) x) (hconc : ∀ k, Antitone (dP k))
    (i : ι) (v : ℝ) (j : ι) (hπ : 0 < pl i j) :
    σc j (σw i v j) = max (σc j (Ud j)) (σc i v) ∧ σc i v ≤ σc j (σw i v j) ∧
      (σc i v < σc j (σw i v j) → σw i v j = Ud j) ∧
      (Ud j < σw i v j → σc j (σw i v j) = σc i v) := by
  classical
  have hc : 0 < σc i v := (hσ i v).1.1
  have hcj : 0 < σc j (σw i v j) := (hσ j _).1.1
  have hf1 : 0 < σc j (Ud j) := (hσ j _).1.1
  have henv : ∀ k x, dP k x = -(du (σc k x))⁻¹ := fun k x =>
    eq_22_8 (fun v' => hB k v') (hσ k x) hg hgpos hug (hgu _ (hσ k x).1.1)
      (hdu _ (hσ k x).1.1) (hdupos _ (hσ k x).1.1).ne' (hdP k x)
  obtain ⟨lamj, hl0, hCS, h6⟩ := (eq_22_6 (hB i v) (hσ i v) hg hgpos hug (hgu _ hc)
    (hdu _ hc) (hdupos _ hc) j hπ.le (hdP j (σw i v j)) (fun _ => 0) 0).2
  rw [henv j] at h6
  have hβπ : 0 < β * pl i j := mul_pos hβ hπ
  have hinv : (du (σc i v))⁻¹ ≤ (du (σc j (σw i v j)))⁻¹ := by
    have h9 := eq_22_9 hβ hπ rfl h6
    have := div_nonneg hl0 hβπ.le
    linarith
  rw [inv_le_inv₀ (hdupos _ hc) (hdupos _ hcj)] at hinv
  have hmono : σc i v ≤ σc j (σw i v j) := by
    by_contra h
    push Not at h
    exact absurd (hduanti hcj hc h) (not_lt.mpr hinv)
  have hslack : Ud j < σw i v j → σc j (σw i v j) = σc i v := by
    intro hlt
    have hl : lamj = 0 := by
      rcases mul_eq_zero.mp hCS with h | h
      · exact h
      · linarith
    rw [hl] at h6
    exact lc_slack_case hc hcj hduanti (q := -(du (σc j (σw i v j)))⁻¹) h6 hβπ.ne' rfl
  have hbind : σc i v < σc j (σw i v j) → σw i v j = Ud j := by
    intro hlt
    by_contra hne
    have := hslack (lt_of_le_of_ne ((hσ i v).1.2.1 j) (Ne.symm hne))
    linarith
  refine ⟨?_, hmono, hbind, hslack⟩
  rcases ((hσ i v).1.2.1 j).lt_or_eq with hlt | heq
  · have hcj' := hslack hlt
    have hd := hconc j hlt.le
    rw [henv, henv, neg_le_neg_iff, inv_le_inv₀ (hdupos _ hf1) (hdupos _ hcj)] at hd
    have : σc j (Ud j) ≤ σc j (σw i v j) := by
      by_contra h
      push Not at h
      exact absurd (hduanti hcj hf1 h) (not_lt.mpr hd)
    rw [hcj'] at this ⊢
    exact (max_eq_right this).symm
  · rw [← heq] at hmono ⊢
    exact (max_eq_left hmono).symm

/-- Miao, (22.11), p. 780: along any history of positive-probability transitions, optimal
consumption follows `c_t = max{c_{t-1}, h(y_t)}` with the minimum consumption function
`h(θⱼ) = σc(θⱼ, U_d(θⱼ))`, the consumption delivered when the incentive constraint binds. -/
theorem eq_22_11 {β : ℝ} (hβ : 0 < β) {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P)
    (σc : ι → ℝ → ℝ) (σw : ι → ℝ → ι → ℝ)
    (hσ : ∀ k x, lc_Optimal β pl θ u Ud P k x (σc k x) (σw k x))
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (hgu : ∀ x, 0 < x → g (u x) = x) (du : ℝ → ℝ) (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdupos : ∀ x, 0 < x → 0 < du x) (hduanti : StrictAntiOn du (Set.Ioi 0))
    (dP : ι → ℝ → ℝ) (hdP : ∀ k x, HasDerivAt (P k) (dP k x) x) (hconc : ∀ k, Antitone (dP k))
    (y : ℕ → ι) (v : ℕ → ℝ) (hy : ∀ t, 0 < pl (y t) (y (t + 1)))
    (hv : ∀ t, v (t + 1) = σw (y t) (v t) (y (t + 1))) (t : ℕ) :
    σc (y (t + 1)) (v (t + 1)) = max (σc (y t) (v t)) (σc (y (t + 1)) (Ud (y (t + 1)))) := by
  rw [hv t, max_comm]
  exact (lc_optimal_contract hβ hB σc σw hσ hg hgpos hug hgu du hdu hdupos hduanti dP hdP hconc
    (y t) (v t) (y (t + 1)) (hy t)).1

omit [Fintype ι] in
/-- Miao, p. 778: "Consumption stays constant during periods when the incentive constraint does
not bind and increases during periods when it binds". With finitely many states a path
`c_{t+1} = max{c_t, h(y_{t+1})}` is nondecreasing and eventually constant. -/
theorem lc_consumption_eventually_constant [Finite ι] (h : ι → ℝ) (y : ℕ → ι) (c : ℕ → ℝ)
    (hc : ∀ t, c (t + 1) = max (c t) (h (y (t + 1)))) :
    Monotone c ∧ ∃ T, ∀ t, T ≤ t → c t = c T := by
  have hmono : Monotone c := monotone_nat_of_le_succ fun t => by rw [hc t]; exact le_max_left _ _
  refine ⟨hmono, ?_⟩
  have hmem : ∀ t, c t ∈ insert (c 0) (Set.range h) := by
    intro t
    induction t with
    | zero => exact Set.mem_insert _ _
    | succ t ih =>
      rw [hc t]
      rcases max_choice (c t) (h (y (t + 1))) with he | he
      · rw [he]; exact ih
      · rw [he]; exact Set.mem_insert_of_mem _ ⟨_, rfl⟩
  have hfin : (Set.range c).Finite :=
    ((Set.finite_range h).insert (c 0)).subset (Set.range_subset_iff.mpr hmem)
  obtain ⟨x, ⟨T, rfl⟩, hx⟩ := Set.exists_max_image (Set.range c) id hfin ⟨c 0, 0, rfl⟩
  exact ⟨T, fun t ht => le_antisymm (hx _ ⟨t, rfl⟩) (hmono ht)⟩

/-- Miao, p. 778 (i.i.d. case): when the transition probabilities do not depend on the current
state, `P(θᵢ, v) − θᵢ` does not depend on `i`. -/
theorem lc_iid_value_shift {β : ℝ} {pl : ι → ι → ℝ} {θ : ι → ℝ} {u : ℝ → ℝ} {Ud : ι → ℝ}
    {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P) (hiid : ∀ i i' k, pl i k = pl i' k)
    (i i' : ι) (v : ℝ) : P i v - θ i = P i' v - θ i' := by
  have key : ∀ i i', P i v ≤ P i' v + θ i - θ i' := by
    intro i i'
    obtain ⟨c, w, ⟨hc, hw, hv⟩, he⟩ := (hB i v).1
    have hf' : lc_feasible β pl u Ud i' v c w := by
      refine ⟨hc, hw, ?_⟩
      simp_rw [← hiid i i']
      exact hv
    have := (hB i' v).lc_obj_le hf'
    rw [he]
    simp only [lc_obj] at this ⊢
    simp_rw [hiid i i']
    linarith
  linarith [key i i', key i' i]

/-- Miao, p. 777–778, the claims "`λᵢ = 0` implies `wᵢ = v`" and `w = max{U_d(y), v}`, proved in
the i.i.d. case (Ljungqvist and Sargent's setting) for a strictly concave differentiable `P`:
the promised value after `θⱼ` is `max{U_d(θⱼ), v}`, so promised values never decrease. For a
general Markov chain this fails (`lc_promise_decrease_counterexample`). -/
theorem lc_iid_promised_value {β : ℝ} (hβ : 0 < β) {pl : ι → ι → ℝ} {θ : ι → ℝ}
    {u g : ℝ → ℝ} {Ud : ι → ℝ} {P : ι → ℝ → ℝ} (hB : lc_Bellman β pl θ u Ud P)
    (hiid : ∀ i i' k, pl i k = pl i' k)
    (σc : ι → ℝ → ℝ) (σw : ι → ℝ → ι → ℝ)
    (hσ : ∀ k x, lc_Optimal β pl θ u Ud P k x (σc k x) (σw k x))
    (hg : Continuous g) (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (hgu : ∀ x, 0 < x → g (u x) = x) (du : ℝ → ℝ) (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdupos : ∀ x, 0 < x → 0 < du x)
    (dP : ι → ℝ → ℝ) (hdP : ∀ k x, HasDerivAt (P k) (dP k x) x)
    (hsconc : ∀ k, StrictAnti (dP k)) (i : ι) (v : ℝ) (j : ι) (hπ : 0 < pl i j) :
    σw i v j = max (Ud j) v ∧ v ≤ σw i v j := by
  classical
  have hc : 0 < σc i v := (hσ i v).1.1
  have hsame : ∀ x, dP j x = dP i x := by
    intro x
    have hfun : P j = fun x => P i x + (θ j - θ i) := by
      funext x
      linarith [lc_iid_value_shift hB hiid j i x]
    have := (hdP i x).add_const (θ j - θ i)
    rw [← hfun] at this
    exact (hdP j x).unique this
  have henv := eq_22_8 (fun v' => hB i v') (hσ i v) hg hgpos hug (hgu _ hc) (hdu _ hc)
    (hdupos _ hc).ne' (hdP i v)
  obtain ⟨lamj, hl0, hCS, h6⟩ := (eq_22_6 (hB i v) (hσ i v) hg hgpos hug (hgu _ hc)
    (hdu _ hc) (hdupos _ hc) j hπ.le (hdP j (σw i v j)) (fun _ => 0) 0).2
  have hβπ : 0 < β * pl i j := mul_pos hβ hπ
  have h9 := eq_22_9 hβ hπ henv h6
  rw [← hsame v] at h9
  have hle : dP j (σw i v j) ≤ dP j v := by
    have := div_nonneg hl0 hβπ.le
    linarith
  have hw := (hσ i v).1.2.1 j
  have hvw : v ≤ σw i v j := by
    by_contra h
    push Not at h
    exact absurd ((hsconc j) h) (not_lt.mpr hle)
  refine ⟨?_, hvw⟩
  rcases hw.lt_or_eq with hlt | heq
  · have hl : lamj = 0 := by
      rcases mul_eq_zero.mp hCS with h | h
      · exact h
      · linarith
    rw [hl, zero_div, sub_zero] at h9
    have := (hsconc j).injective h9
    rw [this, max_eq_right (this ▸ hlt).le]
  · rw [← heq] at hvw ⊢
    exact (max_eq_left hvw).symm

omit [Fintype ι] in
/-- Miao, p. 778, "Promised values never decrease" and full insurance in the i.i.d. case: if
`v_{t+1} = max{U_d(y_{t+1}), v_t}` then promised values are nondecreasing, and once the state
with the largest autarky value has been visited the promised value, hence consumption, stays
constant forever. -/
theorem lc_iid_full_insurance (Ud : ι → ℝ) (y : ℕ → ι) (v : ℕ → ℝ)
    (hv : ∀ t, v (t + 1) = max (Ud (y (t + 1))) (v t)) (T : ℕ)
    (hmax : ∀ k, Ud k ≤ Ud (y T)) (hT : Ud (y T) ≤ v T) :
    Monotone v ∧ ∀ t, T ≤ t → v t = v T := by
  refine ⟨monotone_nat_of_le_succ fun t => by rw [hv t]; exact le_max_right _ _, ?_⟩
  intro t ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← add_assoc, hv, ih (Nat.le_add_right T n)]
    exact max_eq_right ((hmax _).trans hT)

end Miao.RecursiveContracts
