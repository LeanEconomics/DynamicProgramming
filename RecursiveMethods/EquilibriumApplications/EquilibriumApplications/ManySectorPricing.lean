/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorEnvelope

/-!
# Pricing securities: riskless bonds, lotteries, Modigliani–Miller, martingales

SLP §16.2, pp. 484–485, Exercises 16.2(e), (f), (h) and the martingale property, for a general
measurable shock space: the state is `(x, z)`, next period's state is `(g(x, z), z′)` with
`z′ ∼ Q(z, ·)`, and `m(x, z) = U′(c(x, z)) > 0` is the marginal utility of consumption.

* `ex_16_2e`: from (2), the price of a riskless one-period claim (`f ≡ 1`) is
  `q = β ∫ U′(c[g, z′]) Q(z, dz′)/U′(c)`, and that of a bond paying `1` on `E` is
  `q_E = β ∫_E U′(c[g, z′]) Q(z, dz′)/U′(c)`.
* `ex_16_2f`: **lottery tickets**: with `Q((z₁, z₂), A₁ × A₂) = Q₁(z₁, A₁) Q₂(z₂, A₂)`, `f`
  depending only on `z₁` and technology only on `z₂`, `q = q₁ · ∫ f dQ₁(z₁, ·)` with `q₁` the
  riskless price: the gamble is priced risk-neutrally.
* `ms_eq3_unique`: (3) has at most one solution with `U′(c) q` bounded (`|d| ≤ βⁿ C`).
* **Exercise 16.2(h)** (`ex_16_2h`, Modigliani–Miller): if `q_i` are the bounded prices of `f_i`,
  the bounded price of `f = Σ_i f_i` is `Σ_i q_i`.
* `ex_16_2h_bubble_counterexample` (NOTE to Ex 16.2h): without boundedness (3) has other solutions:
  a worthless asset (`f = 0`) with price `q(n) = 2ⁿ` (`β = 1/2`, states `n ↦ n + 1`) solves (3), so
  the price of `f₁ + f₂ = 0 + 0` need not be `q₁ + q₂ = 0`.
* `ms_martingale_increment`, `ms_martingale_prices` (p. 485): by (3′) the increment
  `w_{t+1} = βU′(c_{t+1})(f_{t+1} + q_{t+1}) − U′(c_t)q_t` has conditional mean `0` given the state
  (the martingale property of `W_t = Σ_{s ≤ t} w_s` for the Markov chain); with constant marginal
  utility, `β = 1` and no dividend, `q_t = E_t q_{t+1}`.

**Corrections.**
* (h): additivity holds for the bounded ("fundamental") solution of (3); bubbles break it.
* (p. 485): `β = 1` is outside the model (`β < 1`), an approximation as the text says;
  integrability is needed for the martingale property (assumed here). The martingale statement is
  given in its one-step (conditional-mean-zero) form for the Markov kernel; the path-space
  martingale (Ionescu-Tulcea measure on histories) is not formalised.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory Filter Topology Set

variable {X Z : Type*} [MeasurableSpace Z]

/-! ### Exercise 16.2(e) -/

/-- **Exercise 16.2(e)**: by (2), `U′(c) q = β ∫ U′(c[g, z′]) f(z′) Q(z, dz′)`: for a riskless claim
(`f ≡ 1`) the price is `β ∫ U′(c[g, z′]) Q(z, dz′) / U′(c)`; for a bond paying one unit on `E`
(`f = 1_E`) it is `β ∫_E U′(c[g, z′]) Q(z, dz′) / U′(c)`. -/
theorem ex_16_2e (Q : Z → Measure Z) (β : ℝ) (m : X × Z → ℝ) (hm : ∀ p, 0 < m p)
    (g : X × Z → X) (q : X × Z → ℝ) (x : X) (z : Z) :
    (m (x, z) * q (x, z) = β * ∫ z', m (g (x, z), z') * 1 ∂(Q z) ↔
      q (x, z) = β * (∫ z', m (g (x, z), z') ∂(Q z)) / m (x, z)) ∧
    ∀ E : Set Z, MeasurableSet E →
      (m (x, z) * q (x, z) = β * ∫ z', m (g (x, z), z') * E.indicator 1 z' ∂(Q z) ↔
        q (x, z) = β * (∫ z' in E, m (g (x, z), z') ∂(Q z)) / m (x, z)) := by
  have hpos := hm (x, z)
  refine ⟨?_, fun E hE => ?_⟩
  · simp only [mul_one]
    rw [eq_div_iff hpos.ne', mul_comm]
  · have : (fun z' => m (g (x, z), z') * E.indicator 1 z') =
        E.indicator fun z' => m (g (x, z), z') := by
      funext z'
      by_cases h : z' ∈ E
      · simp [h]
      · simp [h]
    rw [this, integral_indicator hE, eq_div_iff hpos.ne', mul_comm]

/-! ### Exercise 16.2(f) -/

/-- **Exercise 16.2(f), lottery tickets**: let `z = (z₁, z₂)` have independent components,
`Q((z₁, z₂), A₁ × A₂) = Q₁(z₁, A₁) Q₂(z₂, A₂)`, let the technology (hence marginal utility `m₂` and
law of motion `g₂`) depend only on `z₂` and the payoff `f₁` only on `z₁`. If `q` satisfies (2), then
`q = [β ∫ m₂(g₂(x, z₂), z₂′) Q₂(z₂, dz₂′)/m₂(x, z₂)] · ∫ f₁ dQ₁(z₁, ·)`: the riskless price times
the expected payoff. -/
theorem ex_16_2f {Z₁ Z₂ : Type*} [MeasurableSpace Z₁] [MeasurableSpace Z₂]
    (Q : Z₁ × Z₂ → Measure (Z₁ × Z₂)) (Q₁ : Z₁ → Measure Z₁) (Q₂ : Z₂ → Measure Z₂)
    [∀ z, SigmaFinite (Q₁ z)] [∀ z, SigmaFinite (Q₂ z)]
    (hQ : ∀ z₁ z₂ (A₁ : Set Z₁) (A₂ : Set Z₂), MeasurableSet A₁ → MeasurableSet A₂ →
      Q (z₁, z₂) (A₁ ×ˢ A₂) = Q₁ z₁ A₁ * Q₂ z₂ A₂)
    (β : ℝ) (m₂ : X × Z₂ → ℝ) (hm : ∀ p, 0 < m₂ p) (g₂ : X × Z₂ → X) (f₁ : Z₁ → ℝ)
    (q : X × (Z₁ × Z₂) → ℝ) (x : X) (z₁ : Z₁) (z₂ : Z₂)
    (h2 : m₂ (x, z₂) * q (x, (z₁, z₂)) =
      β * ∫ z', m₂ (g₂ (x, z₂), z'.2) * f₁ z'.1 ∂(Q (z₁, z₂))) :
    q (x, (z₁, z₂)) =
      (β * (∫ z₂', m₂ (g₂ (x, z₂), z₂') ∂(Q₂ z₂)) / m₂ (x, z₂)) * ∫ z₁', f₁ z₁' ∂(Q₁ z₁) := by
  have hprod : (Q₁ z₁).prod (Q₂ z₂) = Q (z₁, z₂) :=
    Measure.prod_eq fun A₁ A₂ h₁ h₂ => hQ z₁ z₂ A₁ A₂ h₁ h₂
  have hint : ∫ z', m₂ (g₂ (x, z₂), z'.2) * f₁ z'.1 ∂(Q (z₁, z₂)) =
      (∫ z₁', f₁ z₁' ∂(Q₁ z₁)) * ∫ z₂', m₂ (g₂ (x, z₂), z₂') ∂(Q₂ z₂) := by
    rw [← hprod, ← integral_prod_mul]
    congr 1
    funext z'
    ring
  rw [hint] at h2
  have hpos := hm (x, z₂)
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  linarith

/-! ### Exercise 16.2(h) -/

/-- `q` **solves (3)** for the dividend `f` (with the integrability needed to manipulate (3)):
`m(x, z) q(x, z) = β ∫ m(g, z′)(f(g, z′) + q(g, z′)) Q(z, dz′)`, `g = g(x, z)`. -/
def MsEq3 (Q : Z → Measure Z) (β : ℝ) (m : X × Z → ℝ) (g : X × Z → X) (f q : X × Z → ℝ) : Prop :=
  ∀ x z, Integrable (fun z' => m (g (x, z), z') * q (g (x, z), z')) (Q z) ∧
    Integrable (fun z' => m (g (x, z), z') * f (g (x, z), z')) (Q z) ∧
    m (x, z) * q (x, z) = β * ∫ z', m (g (x, z), z') * (f (g (x, z), z') + q (g (x, z), z')) ∂(Q z)

/-- **At most one solution of (3) with `U′(c) q` bounded** (`0 ≤ β < 1`, `Q` Markov):
`d = m(q₁ − q₂)` satisfies `d = β ∫ d(g, z′) dQ`, so `|d| ≤ βⁿ C → 0`. -/
theorem ms_eq3_unique {Q : Z → Measure Z} [∀ z, IsProbabilityMeasure (Q z)] {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {m : X × Z → ℝ} (hm : ∀ p, 0 < m p) {g : X × Z → X}
    {f q₁ q₂ : X × Z → ℝ} (h₁ : MsEq3 Q β m g f q₁) (h₂ : MsEq3 Q β m g f q₂) {C : ℝ}
    (hC : ∀ p, |m p * q₁ p - m p * q₂ p| ≤ C) : q₁ = q₂ := by
  have hd : ∀ x z, m (x, z) * q₁ (x, z) - m (x, z) * q₂ (x, z) =
      β * ∫ z', (m (g (x, z), z') * q₁ (g (x, z), z') - m (g (x, z), z') * q₂ (g (x, z), z'))
        ∂(Q z) := by
    intro x z
    obtain ⟨i1, if1, e1⟩ := h₁ x z
    obtain ⟨i2, -, e2⟩ := h₂ x z
    rw [e1, e2, ← mul_sub, ← integral_sub (by simp only [mul_add]; exact if1.add i1)
      (by simp only [mul_add]; exact if1.add i2), integral_sub i1 i2]
    congr 1
    rw [← integral_sub i1 i2]
    congr 1
    funext z'
    ring
  have key : ∀ n p, |m p * q₁ p - m p * q₂ p| ≤ β ^ n * C := by
    intro n
    induction n with
    | zero => intro p; rw [pow_zero, one_mul]; exact hC p
    | succ n ih =>
      rintro ⟨x, z⟩
      rw [hd x z, abs_mul, abs_of_nonneg hβ0, pow_succ, mul_comm (β ^ n) β, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hβ0
      have := norm_integral_le_of_norm_le_const (μ := Q z)
        (f := fun z' =>
          m (g (x, z), z') * q₁ (g (x, z), z') - m (g (x, z), z') * q₂ (g (x, z), z'))
        (C := β ^ n * C) (Eventually.of_forall fun z' => by
          rw [Real.norm_eq_abs]; exact ih _)
      simpa [probReal_univ] using this
  funext p
  have hlim : Tendsto (fun n : ℕ => β ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const C
  have h0 : |m p * q₁ p - m p * q₂ p| ≤ 0 := ge_of_tendsto' hlim fun n => key n p
  have := sub_eq_zero.1 (abs_nonpos_iff.1 h0)
  exact mul_left_cancel₀ (hm p).ne' this

/-- Sums of solutions of (3) solve (3) for the summed dividend. -/
theorem ms_eq3_sum {ι : Type*} (s : Finset ι) {Q : Z → Measure Z} {β : ℝ} {m : X × Z → ℝ}
    {g : X × Z → X} {f q : ι → X × Z → ℝ} (h : ∀ i ∈ s, MsEq3 Q β m g (f i) (q i)) :
    MsEq3 Q β m g (fun p => ∑ i ∈ s, f i p) (fun p => ∑ i ∈ s, q i p) := by
  intro x z
  have hq : ∀ i ∈ s, Integrable (fun z' => m (g (x, z), z') * q i (g (x, z), z')) (Q z) :=
    fun i hi => (h i hi x z).1
  have hf : ∀ i ∈ s, Integrable (fun z' => m (g (x, z), z') * f i (g (x, z), z')) (Q z) :=
    fun i hi => (h i hi x z).2.1
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.mul_sum] using integrable_finsetSum s hq
  · simpa [Finset.mul_sum] using integrable_finsetSum s hf
  · have e : ∀ i ∈ s, m (x, z) * q i (x, z) = β * ∫ z', m (g (x, z), z') *
        (f i (g (x, z), z') + q i (g (x, z), z')) ∂(Q z) := fun i hi => (h i hi x z).2.2
    rw [Finset.mul_sum, Finset.sum_congr rfl e, ← Finset.mul_sum,
      ← integral_finsetSum s fun i hi => by simp only [mul_add]; exact (hf i hi).add (hq i hi)]
    congr 2
    funext z'
    rw [← Finset.sum_add_distrib, Finset.mul_sum]

/-- **Exercise 16.2(h)** (Modigliani–Miller): if `q_i` are the bounded prices of the securities
`f_i` (solutions of (3) with `U′(c) q_i` bounded) and `q` is the bounded price of `f = Σ_i f_i`,
then `q = Σ_i q_i`. -/
theorem ex_16_2h {ι : Type*} (s : Finset ι) {Q : Z → Measure Z} [∀ z, IsProbabilityMeasure (Q z)]
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {m : X × Z → ℝ} (hm : ∀ p, 0 < m p) {g : X × Z → X}
    {f qi : ι → X × Z → ℝ} (hi : ∀ i ∈ s, MsEq3 Q β m g (f i) (qi i))
    (hbi : ∀ i ∈ s, ∃ C, ∀ p, |m p * qi i p| ≤ C) {q : X × Z → ℝ}
    (hq : MsEq3 Q β m g (fun p => ∑ i ∈ s, f i p) q) (hb : ∃ C, ∀ p, |m p * q p| ≤ C) :
    q = fun p => ∑ i ∈ s, qi i p := by
  choose! C hC using hbi
  obtain ⟨C₀, hC₀⟩ := hb
  refine ms_eq3_unique hβ0 hβ1 hm hq (ms_eq3_sum s hi) (C := C₀ + ∑ i ∈ s, C i) fun p => ?_
  calc |m p * q p - m p * ∑ i ∈ s, qi i p| ≤ |m p * q p| + |∑ i ∈ s, m p * qi i p| := by
        rw [Finset.mul_sum]; exact abs_sub _ _
    _ ≤ C₀ + ∑ i ∈ s, C i := add_le_add (hC₀ p) ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i hi => hC i hi p))

/-- **Counterexample: bubbles** (NOTE to Ex 16.2h): states `n ∈ ℕ` moving deterministically to
`n + 1`, constant marginal utility `1`, `β = 1/2`, no dividend: both `q ≡ 0` and the unbounded
`q(n) = 2ⁿ` solve (3). So with `f₁ = f₂ = 0` (prices `q₁ = q₂ = 0`), `q(n) = 2ⁿ ≠ q₁ + q₂` is a
solution of (3) for `f₁ + f₂`: additivity needs the bounded solution. -/
theorem ex_16_2h_bubble_counterexample :
    MsEq3 (fun _ : Unit => Measure.dirac ()) (1 / 2) (fun _ : ℕ × Unit => 1)
        (fun p => p.1 + 1) (fun _ => 0) (fun _ => 0) ∧
      MsEq3 (fun _ : Unit => Measure.dirac ()) (1 / 2) (fun _ : ℕ × Unit => 1)
        (fun p => p.1 + 1) (fun _ => 0 + 0) (fun p => (2 : ℝ) ^ p.1) ∧
      (fun p : ℕ × Unit => (2 : ℝ) ^ p.1) ≠ fun _ => 0 + 0 := by
  refine ⟨fun x z => ⟨integrable_const _, integrable_const _, by simp⟩,
    fun x z => ⟨?_, by simp, ?_⟩, fun h => ?_⟩
  · simp
  · simp only [one_mul, add_zero, zero_add]
    rw [integral_dirac]
    ring
  · have := congrFun h (0, ())
    norm_num at this

/-! ### The martingale property (p. 485) -/

/-- **(3′) and the martingale increment**: if `q` solves (3), the increment
`w = β U′(c′)(f′ + q′) − U′(c) q` has conditional mean `0` given the state `(x, z)`. -/
theorem ms_martingale_increment {Q : Z → Measure Z} [∀ z, IsProbabilityMeasure (Q z)] {β : ℝ}
    {m : X × Z → ℝ} {g : X × Z → X} {f q : X × Z → ℝ} (h : MsEq3 Q β m g f q) (x : X) (z : Z) :
    ∫ z', (β * (m (g (x, z), z') * (f (g (x, z), z') + q (g (x, z), z'))) - m (x, z) * q (x, z))
      ∂(Q z) = 0 := by
  obtain ⟨iq, iff, e⟩ := h x z
  have hint : Integrable (fun z' => m (g (x, z), z') * (f (g (x, z), z') + q (g (x, z), z')))
      (Q z) := by simp only [mul_add]; exact iff.add iq
  rw [integral_sub (hint.const_mul β) (integrable_const _), integral_const_mul, integral_const,
    probReal_univ, one_smul, e, sub_self]

/-- **The martingale property of prices** (p. 485): with constant marginal utility, `β = 1` and no
dividend, (3) says `q(x, z) = ∫ q(g(x, z), z′) Q(z, dz′)`, i.e. `q_t = E_t q_{t+1}`. -/
theorem ms_martingale_prices {Q : Z → Measure Z} [∀ z, IsProbabilityMeasure (Q z)] {m₀ : ℝ}
    (hm₀ : 0 < m₀) {g : X × Z → X} {q : X × Z → ℝ}
    (h : MsEq3 Q 1 (fun _ => m₀) g (fun _ => 0) q) (x : X) (z : Z) :
    q (x, z) = ∫ z', q (g (x, z), z') ∂(Q z) := by
  obtain ⟨-, -, e⟩ := h x z
  simp only [zero_add, one_mul, integral_const_mul] at e
  exact mul_left_cancel₀ hm₀.ne' e

end StokeyLucasPrescott.EquilibriumApplications
