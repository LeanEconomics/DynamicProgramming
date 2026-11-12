/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInequality.Dynastic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# §21.2.3: distortions and credit-market restrictions

AKMM, §21.2.3, pp. 647–648.

* **A progressive capital-income tax** (p. 647, fn 25): gross capital income
  `f(a) = a(1 + (r − δ)(1 − τ(a)))`. `pt_hasDerivAt`: the gross marginal return is
  `1 + (r − δ)(1 − τ(a) − aτ′(a))`; footnote 25 prints `τ′(a)/a` in place of `aτ′(a)`, which agrees
  only for `a² = 1` or `τ′(a) = 0` (`pt_printed_iff`, `pt_printed_counterexample`).
  `pt_steady_euler`: in a steady state with no profitable one-period deviation,
  `β(1 + (r − δ)(1 − τ(a) − aτ′(a))) = 1` (`pt_steady_euler_example` shows the hypothesis is met).
  `pt_g_strictMonoOn`: if `τ′ > 0` is nondecreasing, `τ(a) + aτ′(a)` is strictly increasing on
  `a ≥ 0`; `pt_unique`, `pt_equal_wealth`: the steady-state condition then holds at most at one
  `a ≥ 0`, so all savers hold the same wealth. `pt_proportional`: a flat tax leaves the
  condition independent of `a`.
* **Two agents with alternating endowments** (p. 648): `ta_q_eq_beta`: without borrowing
  limits the Euler equations of both agents and market clearing force `qₜ = β` and constant
  consumption; `ta_footnote_26`: the equilibrium with `a₀ = 0` (consumption
  `(ȳ + βy)/(1 + β)` and `(βȳ + y)/(1 + β)`, optimal by Chapter 11's Euler sufficiency) and
  `ta_footnote_26_richer`: agent A consumes more.
  `ta_binding_alloc`: with the limit `a` binding, `c = ȳ + a(1 + q)` and `y − a(1 + q)`;
  `ta_binding_kkt`: if `q` solves `qu′(ȳ + a(1 + q)) = βu′(y − a(1 + q))` and the borrower is
  poorer, the borrower's Euler inequality holds strictly (the limit binds) and `q > β`;
  `ta_binding_strictMono`, `ta_binding_unique`, `ta_binding_exists`: the equation has exactly one
  solution.
-/

namespace AKMM.Inequality

open Filter Topology AKMM.Consumption

/-! ### Progressive capital taxation -/

/-- AKMM, p. 647: gross capital income `a(1 + (r − δ)(1 − τ(a)))`. -/
def pt_gross (r δ : ℝ) (τ : ℝ → ℝ) (a : ℝ) : ℝ := a * (1 + (r - δ) * (1 - τ a))

/-- **AKMM, fn 25, p. 648 (corrected): the gross return on saving.**
`d/da [a(1 + (r − δ)(1 − τ(a)))] = 1 + (r − δ)(1 − τ(a) − aτ′(a))`. -/
theorem pt_hasDerivAt {r δ a τ' : ℝ} {τ : ℝ → ℝ} (hτ : HasDerivAt τ τ' a) :
    HasDerivAt (pt_gross r δ τ) (1 + (r - δ) * (1 - τ a - a * τ')) a := by
  have h := (hasDerivAt_id a).mul ((hτ.const_sub 1).const_mul (r - δ) |>.const_add 1)
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- **AKMM, fn 25: the printed return `1 + (r − δ)(1 − τ(a) − τ′(a)/a)`** equals the true one iff
`r = δ`, `τ′(a) = 0` or `a² = 1` (for `a ≠ 0`). -/
theorem pt_printed_iff {r δ a τa τ' : ℝ} (ha : a ≠ 0) :
    1 + (r - δ) * (1 - τa - τ' / a) = 1 + (r - δ) * (1 - τa - a * τ') ↔
      r = δ ∨ τ' = 0 ∨ a ^ 2 = 1 := by
  constructor
  · intro h
    have h1 : (r - δ) * τ' * (a ^ 2 - 1) = 0 := by
      have : (r - δ) * (a * τ' - τ' / a) = 0 := by linarith
      have e : (r - δ) * τ' * (a ^ 2 - 1) = a * ((r - δ) * (a * τ' - τ' / a)) := by
        field_simp
      rw [e, this, mul_zero]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (h | h | h)
    · rw [h, sub_self, zero_mul, zero_mul]
    · rw [h, zero_div, mul_zero]
    · have e : τ' / a = a * τ' := by
        rw [div_eq_iff ha]
        linear_combination (-τ') * h
      rw [e]

/-- AKMM, fn 25: a concrete discrepancy: `τ(a) = a/10`, `r − δ = 1/10`, `a = 2`: the true gross
return is `1.06`, the printed formula gives `1.075`. -/
theorem pt_printed_counterexample :
    HasDerivAt (pt_gross (1 / 10) 0 (fun a => a / 10)) (53 / 50) 2 ∧
      1 + (1 / 10 - 0) * (1 - 2 / 10 - (1 / 10) / 2) ≠ (53 / 50 : ℝ) := by
  refine ⟨?_, by norm_num⟩
  have h := pt_hasDerivAt (r := 1 / 10) (δ := 0) (a := 2) (τ := fun a => a / 10)
    (τ' := 1 / 10) (by simpa using (hasDerivAt_id (2 : ℝ)).div_const 10)
  convert h using 1
  norm_num

/-- **AKMM, fn 25: "in steady state this expression times `β` must equal 1".** Let the
consumer hold `a` forever with consumption `c = f(a) − a + y`. If saving `a + h` for one
period and returning to `a` is never better
(`u(c − h) + βu(c + f(a + h) − f(a)) ≤ u(c) + βu(c)`), `u′(c) ≠ 0` and `f′(a)` exists, then
`βf′(a) = 1`. With `f = pt_gross r δ τ` this is `β(1 + (r − δ)(1 − τ(a) − aτ′(a))) = 1`. -/
theorem pt_steady_euler {β a c du f' : ℝ} {u f : ℝ → ℝ} (hu : HasDerivAt u du c)
    (hf : HasDerivAt f f' a) (hdu : du ≠ 0)
    (hdev : ∀ h, u (c - h) + β * u (c + (f (a + h) - f a)) ≤ u c + β * u c) :
    β * f' = 1 := by
  set φ := fun h => u (c - h) + β * u (c + (f (a + h) - f a)) with hφ
  have hd1 : HasDerivAt (fun h => u (c - h)) (du * (-1)) 0 := by
    have : HasDerivAt (fun h : ℝ => c - h) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub c
    have hu' : HasDerivAt u du (c - 0) := by rw [sub_zero]; exact hu
    exact hu'.comp 0 this
  have hd2 : HasDerivAt (fun h => u (c + (f (a + h) - f a))) (du * f') 0 := by
    have hin : HasDerivAt (fun h : ℝ => c + (f (a + h) - f a)) f' 0 := by
      have hf' : HasDerivAt (fun h => f (a + h)) f' 0 := by
        have := HasDerivAt.comp_const_add a 0 (by rwa [add_zero])
        simpa using this
      simpa using (hf'.sub_const (f a)).const_add c
    have hu' : HasDerivAt u du (c + (f (a + 0) - f a)) := by simpa using hu
    exact hu'.comp 0 hin
  have hφd : HasDerivAt φ (du * (-1) + β * (du * f')) 0 := hd1.add (hd2.const_mul β)
  have hmax : IsLocalMax φ 0 := Filter.Eventually.of_forall fun h => by
    simp only [hφ, add_zero, sub_self, sub_zero]
    exact hdev h
  have h0 := hmax.hasDerivAt_eq_zero hφd
  have : du * (β * f' - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hdu
  · linarith

/-- The hypothesis of `pt_steady_euler` is met: linear utility, `f(a) = Ra`, `βR = 1`. -/
theorem pt_steady_euler_example {β R a c : ℝ} (hβR : β * R = 1) :
    ∀ h, (c - h) + β * (c + (R * (a + h) - R * a)) ≤ c + β * c := by
  intro h
  have : β * (R * (a + h) - R * a) = h := by
    have e : R * (a + h) - R * a = R * h := by ring
    rw [e, ← mul_assoc, hβR, one_mul]
  linarith

/-- **AKMM, p. 647.** If `τ′ > 0` is nondecreasing on `a ≥ 0` (the book: "positive and strictly
increasing"), then `g(a) = τ(a) + aτ′(a)` is strictly increasing on `a ≥ 0`. -/
theorem pt_g_strictMonoOn {τ τd : ℝ → ℝ} (hτ : ∀ a, HasDerivAt τ (τd a) a)
    (hpos : ∀ a, 0 ≤ a → 0 < τd a) (hmono : MonotoneOn τd (Set.Ici 0)) :
    StrictMonoOn (fun a => τ a + a * τd a) (Set.Ici 0) := by
  have hτm : StrictMonoOn τ (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hτ x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hτ x).deriv]
      exact hpos x (le_of_lt hx)
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  have h1 := hτm hx hy hxy
  have h2 : τd x ≤ τd y := hmono hx hy hxy.le
  have h3 : x * τd x ≤ y * τd y :=
    mul_le_mul hxy.le h2 (hpos x hx').le (hx'.trans hxy.le)
  simp only
  linarith

/-- **AKMM, p. 647.** If `g = τ + aτ′` is strictly increasing on a set `S` and `r ≠ δ`, the
steady-state condition `β(1 + (r − δ)(1 − g(a))) = 1` holds for at most one `a ∈ S`. -/
theorem pt_unique {β r δ : ℝ} {g : ℝ → ℝ} {S : Set ℝ} (hβ : β ≠ 0) (hr : r ≠ δ)
    (hg : StrictMonoOn g S) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hsa : β * (1 + (r - δ) * (1 - g a)) = 1) (hsb : β * (1 + (r - δ) * (1 - g b)) = 1) :
    a = b := by
  have hrd : r - δ ≠ 0 := sub_ne_zero.2 hr
  have h1 : β * (r - δ) * (g a - g b) = 0 := by linarith
  have hgab : g a = g b := by
    rcases mul_eq_zero.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hβ
      · exact absurd h' hrd
    · linarith
  exact hg.injOn ha hb hgab

/-- **AKMM, p. 648: "in steady state, `aᵢ = aᵢ′` for all `i` and `i′`".** Under the hypotheses of
`pt_g_strictMonoOn`, any two savers (`a ≥ 0`) satisfying the steady-state condition hold the
same wealth. -/
theorem pt_equal_wealth {ι : Type*} {β r δ : ℝ} {τ τd : ℝ → ℝ} (hβ : β ≠ 0) (hr : r ≠ δ)
    (hτ : ∀ a, HasDerivAt τ (τd a) a) (hpos : ∀ a, 0 ≤ a → 0 < τd a)
    (hmono : MonotoneOn τd (Set.Ici 0)) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hss : ∀ i, β * (1 + (r - δ) * (1 - τ (a i) - a i * τd (a i))) = 1) (i j : ι) :
    a i = a j := by
  have hg := pt_g_strictMonoOn hτ hpos hmono
  refine pt_unique hβ hr hg (ha i) (ha j) ?_ ?_
  · linear_combination hss i
  · linear_combination hss j

/-- **AKMM, p. 648: "proportional taxes … lower saving, but not differentially across saving
levels".** With a flat rate (`τ′ = 0`) the steady-state condition does not depend on `a`. -/
theorem pt_proportional (β r δ τ0 a b : ℝ) :
    β * (1 + (r - δ) * (1 - τ0 - a * 0)) = β * (1 + (r - δ) * (1 - τ0 - b * 0)) := by
  ring

/-! ### Two agents with alternating endowments -/

/-- **AKMM, p. 648: "there will be full consumption smoothing and `q = β`".** If both agents'
Euler equations `qₜu′(cₜ) = βu′(cₜ₊₁)` hold, total consumption is constant and `u′` is
strictly decreasing, then `qₜ = β` and each agent's consumption is constant. -/
theorem ta_q_eq_beta {β Y : ℝ} {du : ℝ → ℝ} {q cA cB : ℕ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x)
    (hcA : ∀ t, 0 < cA t) (hcB : ∀ t, 0 < cB t)
    (hA : ∀ t, q t * du (cA t) = β * du (cA (t + 1)))
    (hB : ∀ t, q t * du (cB t) = β * du (cB (t + 1)))
    (hY : ∀ t, cA t + cB t = Y) (t : ℕ) :
    q t = β ∧ cA (t + 1) = cA t ∧ cB (t + 1) = cB t := by
  have hYt := hY t
  have hYs := hY (t + 1)
  -- compare consumptions through marginal utilities
  have key : ∀ x y : ℝ, 0 < x → 0 < y → (du x < du y ↔ y < x) := by
    intro x y hx hy
    constructor
    · intro h
      by_contra hle
      have hle := not_lt.1 hle
      rcases hle.eq_or_lt with e | e
      · rw [e] at h; exact lt_irrefl _ h
      · have := hanti hx hy e; linarith
    · intro h; exact hanti hy hx h
  have hdA := hdu _ (hcA t)
  have hdB := hdu _ (hcB t)
  rcases lt_trichotomy (q t) β with hq | hq | hq
  · exfalso
    have h1 : du (cA (t + 1)) < du (cA t) := by
      have := hA t
      have : q t * du (cA t) < β * du (cA t) := mul_lt_mul_of_pos_right hq hdA
      nlinarith
    have h2 : du (cB (t + 1)) < du (cB t) := by
      have := hB t
      have : q t * du (cB t) < β * du (cB t) := mul_lt_mul_of_pos_right hq hdB
      nlinarith
    have := (key _ _ (hcA _) (hcA _)).1 h1
    have := (key _ _ (hcB _) (hcB _)).1 h2
    linarith
  · refine ⟨hq, ?_, ?_⟩
    · have h := hA t
      rw [hq] at h
      have h' : du (cA t) = du (cA (t + 1)) := mul_left_cancel₀ hβ.ne' h
      by_contra hne
      rcases lt_or_gt_of_ne hne with e | e
      · have := hanti (hcA _) (hcA _) e; linarith
      · have := hanti (hcA _) (hcA _) e; linarith
    · have h := hB t
      rw [hq] at h
      have h' : du (cB t) = du (cB (t + 1)) := mul_left_cancel₀ hβ.ne' h
      by_contra hne
      rcases lt_or_gt_of_ne hne with e | e
      · have := hanti (hcB _) (hcB _) e; linarith
      · have := hanti (hcB _) (hcB _) e; linarith
  · exfalso
    have h1 : du (cA t) < du (cA (t + 1)) := by
      have := hA t
      have : β * du (cA t) < q t * du (cA t) := mul_lt_mul_of_pos_right hq hdA
      nlinarith
    have h2 : du (cB t) < du (cB (t + 1)) := by
      have := hB t
      have : β * du (cB t) < q t * du (cB t) := mul_lt_mul_of_pos_right hq hdB
      nlinarith
    have := (key _ _ (hcA _) (hcA _)).1 h1
    have := (key _ _ (hcB _) (hcB _)).1 h2
    linarith

/-- AKMM, p. 648: agent A's endowment, `ȳ` in even periods and `y` in odd periods. -/
def ta_endow (yH yL : ℝ) (t : ℕ) : ℝ := if Even t then yH else yL

/-- AKMM, fn 26: agent A's assets with `a₀ = 0`: `0` in even periods, `(ȳ − y)/(1 + β)` in odd
periods. -/
noncomputable def ta_assets (β yH yL : ℝ) (t : ℕ) : ℝ :=
  if Even t then 0 else (yH - yL) / (1 + β)

/-- **AKMM, fn 26, p. 648: the unconstrained equilibrium with `a₀ = 0`.** With `q = β`
(`R = 1/β`), agent A consumes `(ȳ + βy)/(1 + β)` and agent B `(βȳ + y)/(1 + β)` every period;
A's assets alternate between `0` and `(ȳ − y)/(1 + β)`, B's are their negative (bonds clear), and
both plans are optimal (Chapter 11's Euler sufficiency, `cd_optimal_of_euler`). -/
theorem ta_footnote_26 {β yH yL : ℝ} {u du : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hyL : 0 < yL)
    (hy : yL < yH) (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z)) :
    cd_Optimal β β⁻¹ 0 u (ta_endow yH yL) (fun _ => (yH + β * yL) / (1 + β))
        (ta_assets β yH yL) ∧
      cd_Optimal β β⁻¹ 0 u (ta_endow yL yH) (fun _ => (β * yH + yL) / (1 + β))
        (fun t => -ta_assets β yH yL t) ∧
      ∀ t, ta_assets β yH yL t + -ta_assets β yH yL t = 0 := by
  have hR : 0 < β⁻¹ := inv_pos.2 hβ
  have h1β : 0 < 1 + β := by linarith
  have hsum : ∀ yA yB : ℝ, 0 ≤ yA → 0 ≤ yB →
      Summable fun j => β⁻¹⁻¹ ^ j * ta_endow yA yB j := by
    intro yA yB hA hB
    rw [inv_inv]
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ.le j) ?_) (fun j => ?_)
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right (yA + yB))
    · unfold ta_endow; split_ifs <;> assumption
    · unfold ta_endow
      split_ifs <;> exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ.le j)
  have htvc : ∀ s : ℝ, Tendsto (fun t => (s * ta_assets β yH yL t) / β⁻¹ ^ t) atTop (𝓝 0) := by
    intro s
    have hb : ∀ t, |s * ta_assets β yH yL t| ≤ |s| * ((yH - yL) / (1 + β)) := by
      intro t
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
      unfold ta_assets
      have : 0 ≤ (yH - yL) / (1 + β) := div_nonneg (by linarith) h1β.le
      split_ifs
      · simpa using this
      · rw [abs_of_nonneg this]
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul
      (|s| * ((yH - yL) / (1 + β)))
    rw [mul_zero] at hg
    have e : ∀ t : ℕ, (s * ta_assets β yH yL t) / β⁻¹ ^ t = (s * ta_assets β yH yL t) * β ^ t :=
      fun t => by rw [inv_pow, div_inv_eq_mul]
    simp_rw [e]
    refine squeeze_zero_norm (fun t => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ t)]
    exact mul_le_mul_of_nonneg_right (hb t) (pow_nonneg hβ.le t)
  refine ⟨?_, ?_, fun t => by ring⟩
  · apply cd_optimal_of_euler hβ hR htan
    · refine ⟨by simp [ta_assets], fun t => ?_, fun _ => div_pos (by nlinarith) h1β, ?_⟩
      · unfold ta_assets ta_endow
        rcases Nat.even_or_odd t with ht | ht
        · have ht1 : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 (Even.add_one ht)
          simp only [ht, ht1, ↓reduceIte]
          field_simp
          ring
        · have ht1 : Even (t + 1) := Odd.add_one ht
          have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
          simp only [ht', ht1, ↓reduceIte]
          field_simp
          ring
      · simpa using htvc 1
    · intro t; rw [mul_inv_cancel₀ hβ.ne', one_mul]
    · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
    · exact hsum yH yL (by linarith) hyL.le
  · apply cd_optimal_of_euler hβ hR htan
    · refine ⟨by simp [ta_assets], fun t => ?_, fun _ => div_pos (by nlinarith) h1β, ?_⟩
      · unfold ta_assets ta_endow
        rcases Nat.even_or_odd t with ht | ht
        · have ht1 : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 (Even.add_one ht)
          simp only [ht, ht1, ↓reduceIte]
          field_simp
          ring
        · have ht1 : Even (t + 1) := Odd.add_one ht
          have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
          simp only [ht', ht1, ↓reduceIte]
          field_simp
          ring
      · have := htvc (-1)
        simpa using this
    · intro t; rw [mul_inv_cancel₀ hβ.ne', one_mul]
    · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
    · exact hsum yL yH hyL.le (by linarith)

/-- **AKMM, fn 26: "agent A is richer in present-value terms … and will therefore permanently
have a somewhat higher consumption".** For `0 < β < 1` and `ȳ > y`,
`(ȳ + βy)/(1 + β) > (βȳ + y)/(1 + β)`. -/
theorem ta_footnote_26_richer {β yH yL : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hy : yL < yH) :
    (β * yH + yL) / (1 + β) < (yH + β * yL) / (1 + β) := by
  apply div_lt_div_of_pos_right _ (by linarith)
  nlinarith

/-- **AKMM, p. 648: the stationary allocation with a binding limit `a < 0`.** The currently poor
agent borrows to the limit (`a′ = a`), the currently rich one enters with debt `a` and lends
`−a`: their budgets `c + q(−a) = ȳ + a` and `c + qa = y − a` give consumption `ȳ + a(1 + q)` and
`y − a(1 + q)`, which sum to `ȳ + y`. -/
theorem ta_binding_alloc (q a yH yL : ℝ) :
    (yH + a * (1 + q)) + q * (-a) = yH + a ∧ (yL - a * (1 + q)) + q * a = yL + (-a) ∧
      (yH + a * (1 + q)) + (yL - a * (1 + q)) = yH + yL := by
  refine ⟨by ring, by ring, by ring⟩

/-- **AKMM, p. 648: the limit binds.** If `q` solves `qu′(ȳ + a(1 + q)) = βu′(y − a(1 + q))`
and the borrower consumes less (`y − a(1 + q) < ȳ + a(1 + q)`), then `q > β` and the borrower's
Euler inequality holds strictly: `qu′(y − a(1 + q)) > βu′(ȳ + a(1 + q))`, so he would borrow
more if allowed. -/
theorem ta_binding_kkt {β q a yH yL : ℝ} {du : ℝ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x)
    (hpoor : 0 < yL - a * (1 + q)) (hlt : yL - a * (1 + q) < yH + a * (1 + q))
    (heq : q * du (yH + a * (1 + q)) = β * du (yL - a * (1 + q))) :
    β < q ∧ β * du (yH + a * (1 + q)) < q * du (yL - a * (1 + q)) := by
  have hrich : 0 < yH + a * (1 + q) := hpoor.trans hlt
  have hd : du (yH + a * (1 + q)) < du (yL - a * (1 + q)) := hanti hpoor hrich hlt
  have hdr := hdu _ hrich
  have hdp := hdu _ hpoor
  constructor
  · by_contra hle
    have hle := not_lt.1 hle
    have : q * du (yH + a * (1 + q)) < β * du (yL - a * (1 + q)) :=
      calc q * du (yH + a * (1 + q)) ≤ β * du (yH + a * (1 + q)) :=
            mul_le_mul_of_nonneg_right hle hdr.le
        _ < β * du (yL - a * (1 + q)) := mul_lt_mul_of_pos_left hd hβ
    linarith
  · have h1 : β * du (yH + a * (1 + q)) * du (yH + a * (1 + q)) <
        β * du (yL - a * (1 + q)) * du (yL - a * (1 + q)) := by
      have := mul_lt_mul hd hd.le hdr hdp.le
      nlinarith
    rw [← heq] at h1
    have : β * du (yH + a * (1 + q)) * du (yH + a * (1 + q)) <
        q * du (yL - a * (1 + q)) * du (yH + a * (1 + q)) := by nlinarith
    exact lt_of_mul_lt_mul_right this hdr.le

/-- AKMM, p. 648: the excess of the lender's marginal valuation,
`h(q) = qu′(ȳ + a(1 + q)) − βu′(y − a(1 + q))`. -/
def ta_h (β a yH yL : ℝ) (du : ℝ → ℝ) (q : ℝ) : ℝ :=
  q * du (yH + a * (1 + q)) - β * du (yL - a * (1 + q))

/-- **AKMM, p. 648: "one equation and one unknown".** For `a < 0`, `u′ > 0` strictly decreasing,
`h` is strictly increasing on the prices `q > 0` with positive consumptions. -/
theorem ta_binding_strictMono {β a yH yL : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (ha : a < 0)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x) :
    StrictMonoOn (ta_h β a yH yL du)
      {q | 0 < q ∧ 0 < yH + a * (1 + q) ∧ 0 < yL - a * (1 + q)} := by
  rintro p ⟨hp, hpr, hpp⟩ q ⟨hq, hqr, hqp⟩ hpq
  have hr : yH + a * (1 + q) < yH + a * (1 + p) := by nlinarith
  have hpo : yL - a * (1 + p) < yL - a * (1 + q) := by nlinarith
  have h1 : du (yH + a * (1 + p)) < du (yH + a * (1 + q)) := hanti hqr hpr hr
  have h2 : du (yL - a * (1 + q)) < du (yL - a * (1 + p)) := hanti hpp hqp hpo
  have hd1 := hdu _ hpr
  unfold ta_h
  have : p * du (yH + a * (1 + p)) < q * du (yH + a * (1 + q)) :=
    calc p * du (yH + a * (1 + p)) < q * du (yH + a * (1 + p)) :=
          mul_lt_mul_of_pos_right hpq hd1
      _ < q * du (yH + a * (1 + q)) := mul_lt_mul_of_pos_left h1 hq
  have : β * du (yL - a * (1 + q)) < β * du (yL - a * (1 + p)) := mul_lt_mul_of_pos_left h2 hβ
  linarith

/-- **AKMM, p. 648: the stationary interest rate is unique.** -/
theorem ta_binding_unique {β a yH yL p q : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (ha : a < 0)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x)
    (hp : 0 < p ∧ 0 < yH + a * (1 + p) ∧ 0 < yL - a * (1 + p))
    (hq : 0 < q ∧ 0 < yH + a * (1 + q) ∧ 0 < yL - a * (1 + q))
    (hhp : ta_h β a yH yL du p = 0) (hhq : ta_h β a yH yL du q = 0) : p = q :=
  (ta_binding_strictMono hβ ha hanti hdu).injOn hp hq (hhp.trans hhq.symm)

/-- **AKMM, p. 648: the stationary interest rate exists.** If `u′` is continuous on `(0, ∞)`,
`a < 0`, the borrower is poorer at `q = β` (`y − a(1 + β) < ȳ + a(1 + β)`), and some
`q₁ ≥ β` with `ȳ + a(1 + q₁) > 0` has `h(q₁) ≥ 0`, then `h(q) = 0` for some `q ∈ (β, q₁]`. -/
theorem ta_binding_exists {β a yH yL q₁ : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (ha : a < 0)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hcont : ContinuousOn du (Set.Ioi 0))
    (hyL : 0 < yL) (hlt : yL - a * (1 + β) < yH + a * (1 + β)) (hq₁ : β ≤ q₁)
    (hr₁ : 0 < yH + a * (1 + q₁)) (hh₁ : 0 ≤ ta_h β a yH yL du q₁) :
    ∃ q, β < q ∧ q ≤ q₁ ∧ ta_h β a yH yL du q = 0 := by
  have hpoor : ∀ q, β ≤ q → 0 < yL - a * (1 + q) := fun q hq => by nlinarith [hq]
  have hrich : ∀ q, q ≤ q₁ → 0 < yH + a * (1 + q) := fun q hq => by nlinarith [hq]
  have hβneg : ta_h β a yH yL du β < 0 := by
    unfold ta_h
    have := hanti (hpoor β le_rfl) (hlt.trans_le' le_rfl |>.trans' (hpoor β le_rfl)) hlt
    have h' : du (yH + a * (1 + β)) < du (yL - a * (1 + β)) :=
      hanti (hpoor β le_rfl) ((hpoor β le_rfl).trans hlt) hlt
    nlinarith
  have hc : ContinuousOn (ta_h β a yH yL du) (Set.Icc β q₁) := by
    unfold ta_h
    refine (continuousOn_id.mul ?_).sub (continuousOn_const.mul ?_)
    · exact hcont.comp (by fun_prop) fun q hq => hrich q hq.2
    · exact hcont.comp (by fun_prop) fun q hq => hpoor q hq.1
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc hq₁ hc ⟨hβneg.le, hh₁⟩
  refine ⟨q, ?_, hq.2, hq0⟩
  rcases hq.1.eq_or_lt with e | e
  · rw [← e] at hq0; linarith
  · exact e

end AKMM.Inequality
