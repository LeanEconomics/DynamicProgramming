/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMHeterogeneousFirms.SimpleModel

/-!
# Monopolistic competition (AKMM §22.6.1)

AKMM, §22.6.1, pp. 677–679. The final good is the Dixit–Stiglitz aggregate (22.16) of a unit
mass of intermediate goods, a probability space `(Ω, P)`; `σ > 1`. The Dixit–Stiglitz aggregate,
the price index and the final producer's cost minimisation are imported from Miao's Chapter 19
(`Miao.NewKeynesian.nk_aggY`, `nk_priceIndex`, `eq_19_6_foc`, `eq_19_6`, `eq_19_7`), which is the
same model with `ε = σ`.

* **(22.17)–(22.18)**: the first-order condition `pᵢ = λyᵢ^{−1/σ}Y^{1/σ}` is the demand curve, the
  multiplier is the price index and `∫pᵢyᵢ = λY` (`eq_22_17`); with `P = 1`, the inverse demand
  (22.18) (`eq_22_18`).
* **(22.19)–(22.20)**: the monopolist's problem is the scale problem of §22.2 with returns
  `γ(σ−1)/σ` and productivity `a^{(σ−1)/σ}Y^{1/σ}` (`eq_22_19`, `eq_22_20`), so it is well posed
  for `γ < σ/(σ−1)`, in particular under constant returns `γ = 1`.
* **(22.21)–(22.22)**: the constant markup `p = σ/(σ−1)·MC` (`eq_22_22`).
* **Aggregation**: `Y = (c/γ)(σ/(σ−1))M` (`mc_output_eq`), and `Y = AM^γ` with
  `A = (∫ a^{1/(σ/(σ−1)−γ)})^{σ/(σ−1)−γ}` (`mc_aggregate`, `mc_aggregate_eq`).
-/

open MeasureTheory

namespace AKMM.HeterogeneousFirms

/-- AKMM, (22.17), p. 678: **the final producer's first-order condition** `pᵢ = λyᵢ^{−1/σ}Y^{1/σ}`
is the demand curve `yᵢ = (pᵢ/λ)^{−σ}Y`; along it, `∫pᵢyᵢ = λY` iff `λ` is the price index
`(∫ p^{1−σ})^{1/(1−σ)}` (so `λ = P`). Imported from Miao (19.6)–(19.7). -/
theorem eq_22_17 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ Y lam : ℝ} (hσ : 1 < σ) (hY : 0 < Y) (hlam : 0 < lam) {p y : Ω → ℝ}
    (hp : ∀ i, 0 < p i) (hy : ∀ i, 0 < y i) (hI : Integrable (fun i => p i ^ (1 - σ)) P)
    (hfoc : ∀ i, lam * Y ^ (1 / σ) * y i ^ (-1 / σ) = p i) :
    (∀ i, y i = (p i / lam) ^ (-σ) * Y) ∧
      (∫ i, p i * y i ∂P = lam * Y ↔ lam = Miao.NewKeynesian.nk_priceIndex P σ p) := by
  have hd : ∀ i, y i = (p i / lam) ^ (-σ) * Y := fun i =>
    (Miao.NewKeynesian.eq_19_6_foc (by linarith) hlam hY (hy i) (hp i)).mp (hfoc i)
  refine ⟨hd, ?_⟩
  have e : ∫ i, p i * y i ∂P = ∫ i, p i * ((p i / lam) ^ (-σ) * Y) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun i => by simp only [hd i])
  rw [e]
  exact Miao.NewKeynesian.eq_19_7 hσ hY hlam hp hI

/-- AKMM, (22.18), p. 678: with the final good as numeraire (`P = λ = 1`) the inverse demand is
`pᵢ = yᵢ^{−1/σ}Y^{1/σ}`. -/
theorem eq_22_18 {σ Y yi : ℝ} :
    1 * Y ^ (1 / σ) * yi ^ (-1 / σ) = yi ^ (-1 / σ) * Y ^ (1 / σ) := by ring

/-- `(a mᵞ)^{1−1/σ}Y^{1/σ} = (a^{(σ−1)/σ}Y^{1/σ}) m^{γ(σ−1)/σ}`. -/
theorem mc_revenue_eq {σ γ a m Y : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (ha : 0 < a) (hm : 0 ≤ m) :
    (a * m ^ γ) ^ (-1 / σ) * Y ^ (1 / σ) * (a * m ^ γ) =
      a ^ ((σ - 1) / σ) * Y ^ (1 / σ) * m ^ (γ * ((σ - 1) / σ)) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  rcases hm.lt_or_eq with hm | rfl
  · have hy : 0 < a * m ^ γ := mul_pos ha (Real.rpow_pos_of_pos hm γ)
    have e : (a * m ^ γ) ^ (-1 / σ) * (a * m ^ γ) = (a * m ^ γ) ^ ((σ - 1) / σ) := by
      rw [← Real.rpow_add_one hy.ne']
      congr 1
      field_simp
      ring
    rw [mul_right_comm, e, Real.mul_rpow ha.le (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le]
    ring
  · rw [Real.zero_rpow hγ.ne', Real.zero_rpow (mul_pos hγ hθ).ne']
    ring

/-- AKMM, (22.19), p. 678: **the monopolist's problem**. Taking `Y` as given, firm `i` maximises
`pᵢyᵢ − cm = (am^γ)^{−1/σ}Y^{1/σ}·am^γ − cm`. This is the scale problem of §22.2 with productivity
`a^{(σ−1)/σ}Y^{1/σ}` and returns `γ(σ−1)/σ`, so for `0 < γ(σ−1)/σ < 1` its maximiser is
`m* = simpleScale (γ(σ−1)/σ) c (a^{(σ−1)/σ}Y^{1/σ})`. -/
theorem eq_22_19 {σ γ c a Y m : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1)
    (hc : 0 < c) (ha : 0 < a) (hY : 0 < Y) (hm : 0 ≤ m) :
    (a * m ^ γ) ^ (-1 / σ) * Y ^ (1 / σ) * (a * m ^ γ) - c * m ≤
      (a * simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^ γ) ^ (-1 / σ) *
          Y ^ (1 / σ) *
          (a * simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^ γ) -
        c * simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hA : 0 < a ^ ((σ - 1) / σ) * Y ^ (1 / σ) := by positivity
  have hs := (simple_scale_pos hc (mul_pos hγ hθ) hA).le
  rw [mc_revenue_eq hσ hγ ha hm, mc_revenue_eq hσ hγ ha hs]
  exact eq_22_1 hc (mul_pos hγ hθ) hg hA hm

/-- AKMM, (22.20), p. 679: **the first-order condition**
`(1 − 1/σ)γa^{1−1/σ}m^{γ−γ/σ−1}Y^{1/σ} = c` characterises the monopolist's optimum. -/
theorem eq_22_20 {σ γ c a Y m : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1)
    (hc : 0 < c) (ha : 0 < a) (hY : 0 < Y) (hm : 0 < m) :
    (1 - 1 / σ) * γ * a ^ (1 - 1 / σ) * m ^ (γ - γ / σ - 1) * Y ^ (1 / σ) = c ↔
      m = simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hA : 0 < a ^ ((σ - 1) / σ) * Y ^ (1 / σ) := by positivity
  rw [← eq_22_2 hc (mul_pos hγ hθ) hg hA hm]
  have hσ0 : σ ≠ 0 := by linarith
  have e1 : (1 - 1 / σ) = (σ - 1) / σ := by field_simp
  have e2 : γ - γ / σ - 1 = γ * ((σ - 1) / σ) - 1 := by field_simp
  rw [e1, e2]
  have hg0 : 0 < γ * ((σ - 1) / σ) := mul_pos hγ hθ
  constructor
  · intro h; rw [eq_div_iff hg0.ne']; rw [← h]; ring
  · intro h; rw [eq_div_iff hg0.ne'] at h; rw [← h]; ring

/-- AKMM, (22.21)–(22.22), p. 679: **the constant markup**. At the optimum (first-order condition
(22.20)), the price `p = (am^γ)^{−1/σ}Y^{1/σ}` is `σ/(σ−1)` times the marginal cost
`MC = cm^{1−γ}/(γa)`. -/
theorem eq_22_22 {σ γ c a Y m : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (ha : 0 < a) (hY : 0 < Y)
    (hm : 0 < m)
    (hfoc : (1 - 1 / σ) * γ * a ^ (1 - 1 / σ) * m ^ (γ - γ / σ - 1) * Y ^ (1 / σ) = c) :
    (a * m ^ γ) ^ (-1 / σ) * Y ^ (1 / σ) = σ / (σ - 1) * (c * m ^ (1 - γ) / (γ * a)) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  rw [← hfoc, Real.mul_rpow ha.le (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le]
  have ea : a ^ (1 - 1 / σ) / a = a ^ (-1 / σ) := by
    rw [← Real.rpow_sub_one ha.ne']; congr 1; ring
  have em : m ^ (γ - γ / σ - 1) * m ^ (1 - γ) = m ^ (γ * (-1 / σ)) := by
    rw [← Real.rpow_add hm]; congr 1; ring
  calc a ^ (-1 / σ) * m ^ (γ * (-1 / σ)) * Y ^ (1 / σ)
      = σ / (σ - 1) * ((1 - 1 / σ) * γ * (a ^ (1 - 1 / σ) / a) *
          (m ^ (γ - γ / σ - 1) * m ^ (1 - γ)) * Y ^ (1 / σ) / γ) := by
        rw [ea, em]; field_simp
    _ = _ := by field_simp

/-- AKMM, p. 679: **`Y = (c/γ)(σ/(σ−1))M`**. Revenue `pᵢyᵢ` is `(c/(γ(σ−1)/σ))mᵢ` at each
firm's optimum (§22.2 with returns `γ(σ−1)/σ`); final-good zero profit `∫pᵢyᵢ = Y` gives the
claim. -/
theorem mc_output_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {σ γ c Y : ℝ}
    (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1) (hc : 0 < c) (hY : 0 < Y)
    {a : Ω → ℝ} (ha : ∀ i, 0 < a i)
    (hrev : ∫ i, a i ^ ((σ - 1) / σ) * Y ^ (1 / σ) *
      simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^
        (γ * ((σ - 1) / σ)) ∂P = Y) :
    Y = c / γ * (σ / (σ - 1)) *
      ∫ i, simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ∂P := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hA : ∀ i, 0 < a i ^ ((σ - 1) / σ) * Y ^ (1 / σ) := fun i => by
    have := ha i; positivity
  calc Y = _ := hrev.symm
    _ = _ := eq_22_3 P hc (mul_pos hγ hθ) hg hA
    _ = _ := by
      have hσ0 : σ ≠ 0 := by linarith
      have hσ1 : σ - 1 ≠ 0 := by linarith
      congr 1
      field_simp

/-- AKMM, p. 679: the modified aggregate productivity
`A = (∫ a^{1/(σ/(σ−1)−γ)})^{σ/(σ−1)−γ}`. -/
noncomputable def mcTFP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σ γ : ℝ)
    (a : Ω → ℝ) : ℝ :=
  (∫ i, a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) ^ (σ / (σ - 1) - γ)

/-- AKMM, p. 679: **the aggregate production function under monopolistic competition**. If the
combined inputs are `mᵢ = K aᵢ^{1/(σ/(σ−1)−γ)}` for some `K > 0` (the optimum, `mc_scale_form`),
then the Dixit–Stiglitz output of `yᵢ = aᵢmᵢ^γ` is `AM^γ`. -/
theorem mc_aggregate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {σ γ K : ℝ}
    (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1) (hK : 0 < K) {a : Ω → ℝ}
    (ha : ∀ i, 0 < a i) (hS : 0 < ∫ i, a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) :
    Miao.NewKeynesian.nk_aggY P σ
        (fun i => a i * (K * a i ^ (1 / (σ / (σ - 1) - γ))) ^ γ) =
      mcTFP P σ γ a * (∫ i, K * a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) ^ γ := by
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : 0 < σ - 1 := by linarith
  set θ := (σ - 1) / σ with hθdef
  have hθ : 0 < θ := div_pos hσ1 (by linarith)
  have hinv : σ / (σ - 1) = 1 / θ := by rw [hθdef]; field_simp
  have hD : 0 < 1 / θ - γ := by
    rw [sub_pos, lt_div_iff₀ hθ]; linarith [mul_comm γ θ]
  unfold Miao.NewKeynesian.nk_aggY mcTFP
  rw [hinv] at hS ⊢
  rw [← hθdef]
  set e := 1 / (1 / θ - γ) with he
  have he0 : 0 < e := by positivity
  have hy : ∀ i, (a i * (K * a i ^ e) ^ γ) ^ θ = K ^ (γ * θ) * a i ^ e := fun i => by
    have hai := ha i
    have h1 : (K * a i ^ e) ^ γ = K ^ γ * a i ^ (e * γ) := by
      rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hai.le]
    rw [h1, show a i * (K ^ γ * a i ^ (e * γ)) = K ^ γ * a i ^ (1 + e * γ) by
        rw [Real.rpow_add hai, Real.rpow_one]; ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK.le,
      ← Real.rpow_mul hai.le]
    congr 2
    have hne : 1 - θ * γ ≠ 0 := by linarith [mul_comm γ θ]
    rw [he]; field_simp; ring
  set S := ∫ i, a i ^ e ∂P
  rw [integral_congr_ae (Filter.Eventually.of_forall hy), integral_const_mul, integral_const_mul,
    Real.mul_rpow (by positivity) hS.le, Real.mul_rpow hK.le hS.le, ← Real.rpow_mul hK.le]
  rw [show γ * θ * (1 / θ) = γ by field_simp]
  rw [show S ^ (1 / θ) = S ^ (1 / θ - γ) * S ^ γ by rw [← Real.rpow_add hS]; ring_nf]
  ring

/-- The optimal combined input has the form `K a^{1/(σ/(σ−1)−γ)}`, with `K` common to all
firms. -/
theorem mc_scale_form {σ γ c a Y : ℝ} (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1)
    (hc : 0 < c) (ha : 0 < a) (hY : 0 < Y) :
    simpleScale (γ * ((σ - 1) / σ)) c (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) =
      ((γ * ((σ - 1) / σ)) / c * Y ^ (1 / σ)) ^ (1 / (1 - γ * ((σ - 1) / σ))) *
        a ^ (1 / (σ / (σ - 1) - γ)) := by
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hg1 : 0 < 1 - γ * ((σ - 1) / σ) := by linarith
  unfold simpleScale
  rw [show γ * ((σ - 1) / σ) * (a ^ ((σ - 1) / σ) * Y ^ (1 / σ)) / c =
      (γ * ((σ - 1) / σ) / c * Y ^ (1 / σ)) * a ^ ((σ - 1) / σ) by ring,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le]
  congr 2
  field_simp

/-- AKMM, p. 679: **`Y = AM^γ` at the monopolistic-competition equilibrium**, combining
`mc_scale_form` and `mc_aggregate`. -/
theorem mc_aggregate_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {σ γ c Y : ℝ}
    (hσ : 1 < σ) (hγ : 0 < γ) (hg : γ * ((σ - 1) / σ) < 1) (hc : 0 < c) (hY : 0 < Y)
    {a : Ω → ℝ} (ha : ∀ i, 0 < a i) (hS : 0 < ∫ i, a i ^ (1 / (σ / (σ - 1) - γ)) ∂P) :
    Miao.NewKeynesian.nk_aggY P σ (fun i => a i *
        simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ^ γ) =
      mcTFP P σ γ a *
        (∫ i, simpleScale (γ * ((σ - 1) / σ)) c (a i ^ ((σ - 1) / σ) * Y ^ (1 / σ)) ∂P) ^ γ := by
  have hθ : 0 < (σ - 1) / σ := div_pos (by linarith) (by linarith)
  have hK : 0 < ((γ * ((σ - 1) / σ)) / c * Y ^ (1 / σ)) ^ (1 / (1 - γ * ((σ - 1) / σ))) := by
    have : 0 < γ * ((σ - 1) / σ) := mul_pos hγ hθ
    positivity
  have h := mc_aggregate P hσ hγ hg hK ha hS
  simp only [← mc_scale_form hσ hγ hg hc (ha _) hY] at h
  exact h

end AKMM.HeterogeneousFirms
