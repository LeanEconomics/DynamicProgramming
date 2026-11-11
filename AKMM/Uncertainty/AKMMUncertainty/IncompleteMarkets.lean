/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# An incomplete-markets economy

AKMM, §7.6, pp. 213–215. Income `y` follows a Markov chain `P(y, y′)` on a finite set; the
consumer saves in one asset with price `q = 1/(1 + r)`, `qa′ + c = a + y`, subject to the borrowing
limit `a′ ≥ a̲`:
`V(a, y) = max_{a′ ≥ a̲} u(a + y − qa′) + β Σ_{y′} P(y, y′)V(a′, y′)` attained at `a′ = g(a, y)`
(`im_Bellman`; consumption is positive).

* The first-order condition (corrected): `u′(c)q ≥ βE[V₁(a′, y′)|y]`, with equality when
  `a′ > a̲` (`im_foc`).
* The envelope condition `V₁(a, y) = u′(c)` for `a > a̲` (`im_envelope`), and `V₁(a̲, y) ≥ u′(c)` at
  the limit (`im_envelope_boundary`).
* The Euler equation (corrected): `u′(c) ≥ (1 + r)βE[u′(c′)|y]`, with equality when `a′ > a̲`
  (`im_euler`).

Departures: the book states the first-order condition and the Euler equation as equalities,
although it then says that low-income consumers hit the borrowing constraint; at a binding
constraint only the inequality holds. The decision rules, the bound `ā` and the ergodic set
`[a̲, ā]` and the simulated stationary distribution are read off Figure 7.4 (figure claims,
deferred; for i.i.d. income and `β(1 + r) < 1` they are Miao's Lemma 8.3.3 and Proposition 8.3.1
in `Applications`).
-/

namespace AKMM.Uncertainty

open Filter Topology Set

variable {S : Type*} [Fintype S]

/-- AKMM, p. 213: the consumer's Bellman equation with the borrowing limit `a′ ≥ a̲`: for
`a ≥ a̲`, `g(a, y)` is feasible (`a′ ≥ a̲`, positive consumption), attains the maximum, and `V` is
the maximum value. -/
def im_Bellman (u : ℝ → ℝ) (β q : ℝ) (P : S → S → ℝ) (inc : S → ℝ) (abar : ℝ)
    (V g : S → ℝ → ℝ) : Prop :=
  ∀ y a, abar ≤ a → (abar ≤ g y a ∧ q * g y a < a + inc y) ∧
    V y a = u (a + inc y - q * g y a) + β * ∑ y', P y y' * V y' (g y a) ∧
    ∀ a', abar ≤ a' → q * a' < a + inc y →
      u (a + inc y - q * a') + β * ∑ y', P y y' * V y' a' ≤ V y a

theorem im_Bellman_feasible {u : ℝ → ℝ} {β q : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ}
    {V g : S → ℝ → ℝ}
    (hB : im_Bellman u β q P inc abar V g) {y : S} {a : ℝ} (ha : abar ≤ a) :
    abar ≤ g y a ∧ q * g y a < a + inc y :=
  (hB y a ha).1

/-- **AKMM, p. 213 (corrected): the first-order condition.** With `u` differentiable at `c` and
each `V(·, y′)` at `a′ = g(a, y)`: `u′(c)q ≥ β Σ P(y, y′)V₁(a′, y′)`, with equality if
`a′ > a̲`. -/
theorem im_foc {u : ℝ → ℝ} {β q : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ} {V g : S → ℝ → ℝ}
    (hB : im_Bellman u β q P inc abar V g) {y : S} {a : ℝ} (ha : abar ≤ a) {du : ℝ} {V1 : S → ℝ}
    (hu : HasDerivAt u du (a + inc y - q * g y a)) (hV : ∀ y', HasDerivAt (V y') (V1 y') (g y a)) :
    β * ∑ y', P y y' * V1 y' ≤ du * q ∧ (abar < g y a → du * q = β * ∑ y', P y y' * V1 y') := by
  obtain ⟨-, hval, hle⟩ := hB y a ha
  obtain ⟨hg0, hgc⟩ := im_Bellman_feasible hB ha
  set φ : ℝ → ℝ := fun a' => u (a + inc y - q * a') + β * ∑ y', P y y' * V y' a' with hφ
  have hd : HasDerivAt φ (du * (-q) + β * ∑ y', P y y' * V1 y') (g y a) := by
    have hin : HasDerivAt (fun a' : ℝ => a + inc y - q * a') (-q) (g y a) := by
      simpa using ((hasDerivAt_id' (g y a)).const_mul q).const_sub (a + inc y)
    refine (hu.comp (g y a) hin).add (HasDerivAt.const_mul β ?_)
    exact HasDerivAt.fun_sum fun y' _ => (hV y').const_mul (P y y')
  have hgt : ∀ᶠ a' in 𝓝 (g y a), q * a' < a + inc y :=
    (continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const hgc
  -- a local maximum on `[g, ∞)`: the right derivative is nonpositive
  have hmaxOn : IsLocalMaxOn φ (Ici (g y a)) (g y a) := by
    filter_upwards [nhdsWithin_le_nhds hgt, self_mem_nhdsWithin] with a' h1 h2
    rw [hφ]
    simp only
    rw [← hval]
    exact hle a' (hg0.trans h2) h1
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici (g y a)) (g y a) :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [segment_eq_Icc (by linarith)]; exact Icc_subset_Ici_self)
  have hnp := hmaxOn.hasFDerivWithinAt_nonpos hd.hasDerivWithinAt.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hnp
  refine ⟨by linarith, fun hint => ?_⟩
  have hmax : IsLocalMax φ (g y a) := by
    filter_upwards [hgt, lt_mem_nhds hint] with a' h1 h2
    rw [hφ]
    simp only
    rw [← hval]
    exact hle a' h2.le h1
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, p. 213: the envelope condition** `V₁(a, y) = u′(c)` for `a > a̲`, when `V(·, y)` is
differentiable at `a` and `u` at `c = a + inc y − qg(a, y)`. -/
theorem im_envelope {u : ℝ → ℝ} {β q : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ} {V g : S → ℝ → ℝ}
    (hB : im_Bellman u β q P inc abar V g) {y : S} {a : ℝ} (ha : abar < a) {du V1 : ℝ}
    (hV : HasDerivAt (V y) V1 a) (hu : HasDerivAt u du (a + inc y - q * g y a)) : V1 = du := by
  obtain ⟨-, hval, -⟩ := hB y a ha.le
  obtain ⟨hg0, hgc⟩ := im_Bellman_feasible hB ha.le
  set a' := g y a
  set ψ : ℝ → ℝ := fun j => V y j - (u (j + inc y - q * a') + β * ∑ y', P y y' * V y' a') with hψ
  have hd : HasDerivAt ψ (V1 - du) a := by
    have h1 : HasDerivAt (fun j => u (j + inc y - q * a')) du a := by
      have hin : HasDerivAt (fun j : ℝ => j + inc y - q * a') 1 a := by
        simpa using ((hasDerivAt_id' a).add_const (inc y)).sub_const (q * a')
      exact (hu.comp a hin).congr_deriv (mul_one du)
    exact hV.sub (h1.add_const _)
  have hmin : IsLocalMin ψ a := by
    have hcont : ContinuousAt (fun j : ℝ => j + inc y) a := by fun_prop
    filter_upwards [lt_mem_nhds ha, continuousAt_const.eventually_lt hcont hgc] with j hj hj'
    have := (hB y j hj.le).2.2 a' hg0 hj'
    have h0 : ψ a = 0 := by rw [hψ]; simp only; rw [hval]; ring
    rw [h0]
    simp only [hψ]
    linarith
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- AKMM, p. 213: at any `a ≥ a̲` (in particular at the borrowing limit) the envelope argument
gives `V₁(a, y) ≥ u′(c)`. -/
theorem im_envelope_boundary {u : ℝ → ℝ} {β q : ℝ} {P : S → S → ℝ} {inc : S → ℝ} {abar : ℝ}
    {V g : S → ℝ → ℝ} (hB : im_Bellman u β q P inc abar V g) {y : S} {a : ℝ} (ha : abar ≤ a)
    {du V1 : ℝ} (hV : HasDerivAt (V y) V1 a) (hu : HasDerivAt u du (a + inc y - q * g y a)) :
    du ≤ V1 := by
  obtain ⟨-, hval, -⟩ := hB y a ha
  obtain ⟨hg0, hgc⟩ := im_Bellman_feasible hB ha
  set a' := g y a
  set ψ : ℝ → ℝ := fun j => V y j - (u (j + inc y - q * a') + β * ∑ y', P y y' * V y' a') with hψ
  have hd : HasDerivAt ψ (V1 - du) a := by
    have h1 : HasDerivAt (fun j => u (j + inc y - q * a')) du a := by
      have hin : HasDerivAt (fun j : ℝ => j + inc y - q * a') 1 a := by
        simpa using ((hasDerivAt_id' a).add_const (inc y)).sub_const (q * a')
      exact (hu.comp a hin).congr_deriv (mul_one du)
    exact hV.sub (h1.add_const _)
  have hminOn : IsLocalMinOn ψ (Ici a) a := by
    have hcont : ContinuousAt (fun j : ℝ => j + inc y) a := by fun_prop
    filter_upwards [nhdsWithin_le_nhds (continuousAt_const.eventually_lt hcont hgc),
      self_mem_nhdsWithin] with j hj' hj
    have := (hB y j (ha.trans hj)).2.2 a' hg0 hj'
    have h0 : ψ a = 0 := by rw [hψ]; simp only; rw [hval]; ring
    rw [h0]
    simp only [hψ]
    linarith
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici a) a :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [segment_eq_Icc (by linarith)]; exact Icc_subset_Ici_self)
  have hnp := hminOn.neg.hasFDerivWithinAt_nonpos hd.neg.hasDerivWithinAt.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hnp
  linarith

/-- **AKMM, p. 213 (corrected): the Euler equation.** With `q = 1/(1 + r)`, `r > −1`,
`P ≥ 0`, `u` differentiable on `(0, ∞)` with derivative `u′`, and `V(·, y)` differentiable on
`[a̲, ∞)`: `u′(c) ≥ (1 + r)β Σ P(y, y′)u′(c′)` with `c′ = a′ + y′ − qg(a′, y′)`, and equality
when `a′ = g(a, y) > a̲`. -/
theorem im_euler {u u' : ℝ → ℝ} {β r : ℝ} (hβ : 0 ≤ β) (hr : 0 < 1 + r) {P : S → S → ℝ}
    (hP : ∀ y y', 0 ≤ P y y') {inc : S → ℝ} {abar : ℝ} {V V1 g : S → ℝ → ℝ}
    (hB : im_Bellman u β (1 / (1 + r)) P inc abar V g)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hV : ∀ y a, abar ≤ a → HasDerivAt (V y) (V1 y a) a) {y : S} {a : ℝ} (ha : abar ≤ a) :
    (1 + r) * β * ∑ y', P y y' *
        u' (g y a + inc y' - 1 / (1 + r) * g y' (g y a)) ≤ u' (a + inc y - 1 / (1 + r) * g y a) ∧
      (abar < g y a → u' (a + inc y - 1 / (1 + r) * g y a) = (1 + r) * β * ∑ y', P y y' *
        u' (g y a + inc y' - 1 / (1 + r) * g y' (g y a))) := by
  set q := 1 / (1 + r) with hqdef
  obtain ⟨hg0, hgc⟩ := im_Bellman_feasible hB ha
  have hc : 0 < a + inc y - q * g y a := by linarith
  have hcy : ∀ y', 0 < g y a + inc y' - q * g y' (g y a) := fun y' => by
    have := (im_Bellman_feasible hB (y := y') hg0).2
    linarith
  obtain ⟨hineq, heq⟩ := im_foc hB ha (hu _ hc) (fun y' => hV y' (g y a) hg0)
  have hq : q * (1 + r) = 1 := by rw [hqdef]; field_simp
  refine ⟨?_, fun hint => ?_⟩
  · have hbd : ∑ y', P y y' * u' (g y a + inc y' - q * g y' (g y a)) ≤
        ∑ y', P y y' * V1 y' (g y a) := Finset.sum_le_sum fun y' _ =>
      mul_le_mul_of_nonneg_left (im_envelope_boundary hB hg0 (hV y' _ hg0) (hu _ (hcy y')))
        (hP y y')
    have h1 := mul_le_mul_of_nonneg_left hbd hβ
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hineq) hr.le
    calc (1 + r) * β * ∑ y', P y y' * u' (g y a + inc y' - q * g y' (g y a)) =
        (1 + r) * (β * ∑ y', P y y' * u' (g y a + inc y' - q * g y' (g y a))) := by ring
      _ ≤ (1 + r) * (u' (a + inc y - q * g y a) * (q)) := h2
      _ = _ := by rw [mul_comm, mul_assoc, hq, mul_one]
  · have he := heq hint
    have hsum : ∑ y', P y y' * V1 y' (g y a) =
        ∑ y', P y y' * u' (g y a + inc y' - q * g y' (g y a)) :=
      Finset.sum_congr rfl fun y' _ => by
        rw [im_envelope hB hint (hV y' _ hg0) (hu _ (hcy y'))]
    rw [hsum] at he
    calc u' (a + inc y - q * g y a) =
        (1 + r) * (u' (a + inc y - q * g y a) * (q)) := by
          rw [mul_comm (1 + r), mul_assoc, hq, mul_one]
      _ = _ := by rw [he]; ring

end AKMM.Uncertainty
