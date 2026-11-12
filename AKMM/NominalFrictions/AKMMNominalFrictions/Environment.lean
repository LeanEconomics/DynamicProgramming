/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.CES
import NewKeynesian.NKHouseholds

/-!
# The New Keynesian environment and the household's problem

AKMM, §18.3, pp. 536–539: preferences (18.1), the CES final-goods technology (18.2), the
intermediate technology (18.3), the demand curve (18.4), the price index, the real budget
constraint, and the household's first-order conditions (18.5)–(18.6).

* `env_ces`: on the book's continuum `[0, 1]`, every input bundle producing `Y` costs at least
  `P · Y`; it costs exactly `P · Y` iff it is the demand schedule (18.4); the schedule produces
  `Y` and costs `P Y` (Galí's `unitInterval_expenditure_minimisation`). Hence the cost function
  is `Y ↦ P Y` and `P` is its derivative (footnote 4, `env_cost_deriv`).
* `env_demand_elasticity`: the price elasticity of (18.4) is `−ε`.
* `env_marginal_cost`, `env_profit`: with `y = Aℓ` the real marginal cost is `w/A` and real
  profit is `(p − w/A) p^{−ε} Y`.
* `env_real_budget`, `env_relprice_law`: the budget constraint in real terms and the law
  `p_{t+1} = p_t/(1 + π_{t+1})` for a firm that does not reset.
* `env_labour_foc`, `eq_18_6`: the intratemporal condition `C^{−σ} w = L^ψ` as the first-order
  condition of the labour choice.
* `env_euler_foc`, `eq_18_5`: under perfect foresight, the Euler equation (18.5) as the
  first-order condition of shifting saving by one bond; `eq_18_5_stochastic`: the conditional
  form from the bond first-order condition (Miao's `eq_19_3`).
-/

namespace AKMM.NominalFrictions

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-- AKMM, (18.1), p. 536: period utility `C^{1−σ}/(1 − σ) − L^{1+ψ}/(1 + ψ)`. -/
noncomputable def nfU (σ ψ C L : ℝ) : ℝ := C ^ (1 - σ) / (1 - σ) - L ^ (1 + ψ) / (1 + ψ)

/-- AKMM, (18.2)–(18.4) and p. 537, on the book's continuum `j ∈ [0, 1]`: with positive
intermediate prices `P_j`, (i) every bundle `y_j ≥ 0` costs at least `P · Y`, `Y` the CES
aggregate (18.2) and `P = (∫ P_j^{1−ε})^{1/(1−ε)}`; (ii) it costs exactly `P · Y` iff
`y_j = (P_j/P)^{−ε} Y` (18.4) almost everywhere; (iii) the schedule (18.4) produces `Y`;
(iv) it costs `P Y`. From Galí's `unitInterval_expenditure_minimisation`. -/
theorem env_ces {ε : ℝ} (hε : 1 < ε) {Pj : ℝ → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : IntegrableOn (fun j => Pj j ^ (1 - ε)) (Set.Icc 0 1)) {y : ℝ → ℝ}
    (hy : ∀ j, 0 ≤ y j) (hPy : IntegrableOn (fun j => Pj j * y j) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * cesAgg (volume.restrict (Set.Icc 0 1)) ε y
        ≤ ∫ j in Set.Icc 0 1, Pj j * y j ∧
      (∫ j in Set.Icc 0 1, Pj j * y j
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε y ↔
        ∀ᵐ j ∂(volume.restrict (Set.Icc 0 1)),
          y j = demand (volume.restrict (Set.Icc 0 1)) ε Pj
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε y) j) ∧
      (∀ Y : ℝ, 0 ≤ Y → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Pj Y) = Y) ∧
      ∀ Y : ℝ, ∫ j in Set.Icc 0 1, Pj j * demand (volume.restrict (Set.Icc 0 1)) ε Pj Y j
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Y :=
  unitInterval_expenditure_minimisation hε hP hPi hy hPy

/-- AKMM, p. 537 and footnote 4: by `env_ces` the least cost of producing `Y ≥ 0` is `P Y`
(attained by the demand schedule, and no bundle producing `Y` costs less), so the cost function
is `Y ↦ P Y`; `P` is its derivative with respect to the quantity produced. -/
theorem env_cost_deriv {ε : ℝ} (hε : 1 < ε) {Pj : ℝ → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : IntegrableOn (fun j => Pj j ^ (1 - ε)) (Set.Icc 0 1)) {Y : ℝ} (hY : 0 ≤ Y) :
    (∀ y : ℝ → ℝ, (∀ j, 0 ≤ y j) → IntegrableOn (fun j => Pj j * y j) (Set.Icc 0 1) →
        cesAgg (volume.restrict (Set.Icc 0 1)) ε y = Y →
        priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Y ≤ ∫ j in Set.Icc 0 1, Pj j * y j) ∧
      cesAgg (volume.restrict (Set.Icc 0 1)) ε (demand (volume.restrict (Set.Icc 0 1)) ε Pj Y)
        = Y ∧
      ∫ j in Set.Icc 0 1, Pj j * demand (volume.restrict (Set.Icc 0 1)) ε Pj Y j
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Y ∧
      HasDerivAt (fun Z => priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj * Z)
        (priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj) Y := by
  refine ⟨fun y hy hPy hYy => ?_, (env_ces hε hP hPi (fun _ => le_refl 0)
    (by simp)).2.2.1 Y hY, (env_ces hε hP hPi (fun _ => le_refl 0) (by simp)).2.2.2 Y, ?_⟩
  · have h := (env_ces hε hP hPi hy hPy).1
    rwa [hYy] at h
  · simpa using (hasDerivAt_id Y).const_mul (priceIndex (volume.restrict (Set.Icc 0 1)) ε Pj)

/-- AKMM, (18.4), p. 537: "the price elasticity of the demand facing an intermediate goods
producer is `ε`": `y(p) = (p/P)^{−ε} Y` has `y'(p) · p / y(p) = −ε`. -/
theorem env_demand_elasticity {ε P Y p : ℝ} (hP : 0 < P) (hY : 0 < Y) (hp : 0 < p) :
    HasDerivAt (fun q => (q / P) ^ (-ε) * Y) (-ε * (p / P) ^ (-ε - 1) * (1 / P) * Y) p ∧
      -ε * (p / P) ^ (-ε - 1) * (1 / P) * Y * p / ((p / P) ^ (-ε) * Y) = -ε := by
  have hq : 0 < p / P := div_pos hp hP
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun q => q / P) (1 / P) p := by
      simpa using (hasDerivAt_id p).div_const P
    have h2 := (h1.rpow_const (p := -ε) (Or.inl hq.ne')).mul_const Y
    convert h2 using 1
    ring
  · have h3 : (p / P) ^ (-ε) = (p / P) ^ (-ε - 1) * (p / P) := by
      rw [← Real.rpow_add_one hq.ne']; ring_nf
    have h4 : 0 < (p / P) ^ (-ε - 1) := Real.rpow_pos_of_pos hq _
    rw [h3]
    field_simp

/-- AKMM, (18.3), p. 536: with `y = Aℓ` the real cost of producing `y` is `w y/A`, so the real
marginal cost is `w/A`, common across firms. -/
theorem env_marginal_cost {w A y : ℝ} : HasDerivAt (fun z => w * (z / A)) (w / A) y := by
  have h := (hasDerivAt_id y).const_mul (w / A)
  simp only [id, mul_one] at h
  convert h using 1
  funext z
  ring

/-- AKMM, p. 539: real profits `m = p y − w ℓ = (p − w/A) y = (p − w/A) p^{−ε} Y`, using
(18.3) for `ℓ` and (18.4) (relative price `p`) for `y`. -/
theorem env_profit {ε p w A Y y ℓ : ℝ} (hA : A ≠ 0) (h3 : y = A * ℓ) (h4 : y = p ^ (-ε) * Y) :
    p * y - w * ℓ = (p - w / A) * y ∧ p * y - w * ℓ = (p - w / A) * p ^ (-ε) * Y := by
  have hl : ℓ = y / A := by rw [h3]; field_simp
  refine ⟨by rw [hl]; field_simp, ?_⟩
  rw [hl, h4]; field_simp

/-- AKMM, p. 538: the budget constraint `B_{t+1} + P_t C_t = P_t w_t L_t + (1 + i_{t−1}) B_t +
P_t m_t` in real terms: with `b_t = B_t/P_{t−1}` and `1 + π_t = P_t/P_{t−1}`,
`b_{t+1} + C_t = w_t L_t + (1 + i_{t−1})/(1 + π_t) b_t + m_t`. -/
theorem env_real_budget {Bn B P Pm C w L i m : ℝ} (hP : 0 < P) (hPm : 0 < Pm) :
    Bn + P * C = P * w * L + (1 + i) * B + P * m ↔
      Bn / P + C = w * L + (1 + i) / (P / Pm) * (B / Pm) + m := by
  have e : (1 + i) / (P / Pm) * (B / Pm) = (1 + i) * B / P := by field_simp
  rw [e]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- AKMM, p. 538: a firm that does not reset its nominal price `P_j` has relative price
`p_{t+1} = P_j/P_{t+1} = p_t/(1 + π_{t+1})`, with `1 + π_{t+1} = P_{t+1}/P_t`. -/
theorem env_relprice_law {Pj P Pn : ℝ} (hP : 0 < P) (hPn : 0 < Pn) :
    Pj / Pn = (Pj / P) / (Pn / P) := by
  field_simp

/-- AKMM, p. 538: the marginal value of labour. Working `L` more hours at real wage `w` with
consumption `C₀ + wL`, the derivative of `nfU σ ψ (C₀ + w L) L` in `L` is
`(C₀ + wL)^{−σ} w − L^ψ`. -/
theorem env_labour_foc {σ ψ C₀ w L : ℝ} (hσ : σ ≠ 1) (hψ : 0 < ψ) (hC : 0 < C₀ + w * L)
    (hL : 0 < L) :
    HasDerivAt (fun l => nfU σ ψ (C₀ + w * l) l) ((C₀ + w * L) ^ (-σ) * w - L ^ ψ) L := by
  have h1 : HasDerivAt (fun l => C₀ + w * l) w L := by
    simpa using ((hasDerivAt_id L).const_mul w).const_add C₀
  have hc := (Miao.NewKeynesian.nk_hasDerivAt_pow_div hσ hC).comp L h1
  have hψ1 : (1 : ℝ) + ψ ≠ 0 := by linarith
  have hl := (Real.hasDerivAt_rpow_const (p := 1 + ψ) (Or.inl hL.ne')).div_const (1 + ψ)
  have e : (1 + ψ) * L ^ (1 + ψ - 1) / (1 + ψ) = L ^ ψ := by
    rw [show 1 + ψ - 1 = ψ by ring]; field_simp
  rw [e] at hl
  exact hc.sub hl

/-- AKMM, (18.6), p. 538: the intratemporal labour-supply condition `C^{−σ} w = L^ψ` is the
first-order condition of the labour choice (`env_labour_foc`). -/
theorem eq_18_6 {σ ψ C₀ w L : ℝ} (hσ : σ ≠ 1) (hψ : 0 < ψ) (hC : 0 < C₀ + w * L) (hL : 0 < L) :
    HasDerivAt (fun l => nfU σ ψ (C₀ + w * l) l) 0 L ↔ (C₀ + w * L) ^ (-σ) * w = L ^ ψ := by
  constructor
  · intro h
    have := (env_labour_foc hσ hψ hC hL).unique h
    linarith
  · intro h
    have := env_labour_foc hσ hψ hC hL
    rwa [h, sub_self] at this

/-- AKMM, p. 538: the marginal value of saving. Buying `b` more real bonds at `t` lowers
`C_t` by `b` and raises `C_{t+1}` by `R b`, `R = (1 + i_t)/(1 + π_{t+1})`; the derivative of
`u(C_t − b) + β u(C_{t+1} + R b)` at `b = 0` is `−C_t^{−σ} + β R C_{t+1}^{−σ}`. -/
theorem env_euler_foc {σ β R C₀ C₁ L₀ L₁ ψ : ℝ} (hσ : σ ≠ 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    HasDerivAt (fun b => nfU σ ψ (C₀ - b) L₀ + β * nfU σ ψ (C₁ + R * b) L₁)
      (-C₀ ^ (-σ) + β * (R * C₁ ^ (-σ))) 0 := by
  have h0 : HasDerivAt (fun b : ℝ => C₀ - b) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub C₀
  have h1 : HasDerivAt (fun b : ℝ => C₁ + R * b) R 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add C₁
  have hu0 := Miao.NewKeynesian.nk_hasDerivAt_pow_div hσ (by simpa using hC₀ : 0 < C₀ - 0)
  have hu1 := Miao.NewKeynesian.nk_hasDerivAt_pow_div hσ (by simpa using hC₁ : 0 < C₁ + R * 0)
  have hA := ((hu0.comp 0 h0).sub_const (L₀ ^ (1 + ψ) / (1 + ψ)))
  have hB := (((hu1.comp 0 h1).sub_const (L₁ ^ (1 + ψ) / (1 + ψ))).const_mul β)
  have h := hA.add hB
  simp only [sub_zero, mul_zero, add_zero] at h
  convert h using 1
  · funext b
    simp only [nfU, Function.comp_apply, Pi.add_apply]
  · ring

/-- AKMM, (18.5), p. 538 (perfect foresight): saving is optimal at the margin iff
`C_t^{−σ} = β (1 + i_t)/(1 + π_{t+1}) C_{t+1}^{−σ}` (`env_euler_foc`). -/
theorem eq_18_5 {σ β i π' C₀ C₁ L₀ L₁ ψ : ℝ} (hσ : σ ≠ 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    HasDerivAt (fun b => nfU σ ψ (C₀ - b) L₀ + β * nfU σ ψ (C₁ + (1 + i) / (1 + π') * b) L₁)
        0 0 ↔ C₀ ^ (-σ) = β * ((1 + i) / (1 + π') * C₁ ^ (-σ)) := by
  have h := env_euler_foc (R := (1 + i) / (1 + π')) (L₀ := L₀) (L₁ := L₁) (ψ := ψ) (β := β)
    hσ hC₀ hC₁
  constructor
  · intro h0
    have := h.unique h0
    linarith
  · intro he
    rwa [he, neg_add_cancel] at h

/-- AKMM, (18.5), p. 538 (under uncertainty): from the bond first-order condition
`C_t^{−σ}/(P_t(1 + i_t)) = E_t[β C_{t+1}^{−σ}/P_{t+1}]`, the Euler equation holds in the form
`1 = β(1 + i_t) E_t[(C_{t+1}/C_t)^{−σ} P_t/P_{t+1}]`, i.e. (18.5) with
`P_t/P_{t+1} = 1/(1 + π_{t+1})` (Miao's `eq_19_3`, `E_t = μ[·|ℱ_t]`). -/
theorem eq_18_5_stochastic {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : MeasurableSpace Ω} {β σ : ℝ} {C P i : ℕ → Ω → ℝ} (t : ℕ) (hC : ∀ s ω, 0 < C s ω)
    (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hB : (fun ω => C t ω ^ (-σ) / (P t ω * (1 + i t ω))) =ᵐ[μ]
      μ[fun ω => β * C (t + 1) ω ^ (-σ) / P (t + 1) ω | ℱ])
    (hmeas : StronglyMeasurable[ℱ] (fun ω => C t ω ^ σ * P t ω))
    (hint1 : Integrable (fun ω => C (t + 1) ω ^ (-σ) / P (t + 1) ω) μ)
    (hint2 : Integrable (fun ω => (C (t + 1) ω / C t ω) ^ (-σ) * (P t ω / P (t + 1) ω)) μ) :
    (fun _ => (1 : ℝ)) =ᵐ[μ] fun ω => β * (1 + i t ω) *
      μ[fun ω => (C (t + 1) ω / C t ω) ^ (-σ) * (P t ω / P (t + 1) ω) | ℱ] ω :=
  Miao.NewKeynesian.eq_19_3 (mΩ := mΩ) (μ := μ) (β := β) (Λ := fun s ω => C s ω ^ (-σ)) t hC hP hi
    (fun _ _ => rfl) hB hmeas hint1 hint2

end AKMM.NominalFrictions
