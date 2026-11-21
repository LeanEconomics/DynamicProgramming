/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.Jones
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Quality ladders and creative destruction

AKMM, §13.5.2 (pp. 398–404) and Appendix 13.A.9 (p. 861): Aghion and Howitt (1992) in a
lab-equipment version. Write `X = A(1−φ)/ψ` and `π̄ = φAX^{(1−φ)/φ}L`, the flow profit per
unit of quality.

* Final goods: (13.62)–(13.63) (`eq_13_62`, `eq_13_63`).
* Monopoly: the quantity `X^{1/φ}L` (independent of `q`), the price `ψq/(1−φ)` and profit
  (13.65) `π̄q` (`eq_13_65`); aggregates `Y` and `X(t)` in terms of `Q` (`quality_aggregates`).
* Drastic and incremental innovation: (13.A.26), (13.64), and limit pricing (13.A.27)
  (`eq_13_A_26`, `eq_13_64`, `eq_13_A_27`).
* Research: free entry `V/q = 1/(λη)` and the Arrow replacement effect
  (`quality_research_foc`, `quality_arrow_replacement`).
* The leader's value with creative destruction at rate `z`: `V = π̄q/(r + z)`
  (`quality_value`).
* The aggregate quality index is *defined* by its mean-field ODE `Q̇ = (λ−1)zQ`; for one ladder
  with Poisson arrivals, `E[q(t)] = q_0e^{(λ−1)zt}` (`quality_single_ladder`).
* The balanced growth path (13.66) (`eq_13_66`) and its comparative statics
  (`quality_comparative_statics`, `quality_growth_mono_lambda`, `quality_growth_anti_psi`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, p. 400: flow profit per unit of quality, `π̄ = φAX^{(1−φ)/φ}L`. -/
noncomputable def qlPiBar (A φ ψ L : ℝ) : ℝ := φ * A * romerX A φ ψ ^ ((1 - φ) / φ) * L

/-- AKMM, (13.62), p. 400: the wage is the marginal product of labour, `w = φY/L`. -/
theorem eq_13_62 {A φ S L : ℝ} (hL : 0 < L) :
    HasDerivAt (fun l => A / (1 - φ) * l ^ φ * S) (φ * (A / (1 - φ) * L ^ φ * S) / L) L :=
  eq_13_23 hL

/-- AKMM, (13.63), p. 400: the first-order condition `AL^φqx^{−φ} = p` for `x > 0`, `p > 0`,
`A, q > 0`, is solved exactly by `x = (Aq/p)^{1/φ}L`. -/
theorem eq_13_63 {A φ q p L x : ℝ} (hφ0 : 0 < φ) (hA : 0 < A) (hq : 0 < q) (hp : 0 < p)
    (hL : 0 < L) (hx : 0 < x) :
    A * L ^ φ * q * x ^ (-φ) = p ↔ x = (A * q / p) ^ (1 / φ) * L := by
  have hAqp : 0 < A * q / p := by positivity
  constructor
  · intro h
    have e : x ^ φ = A * q / p * L ^ φ := by
      rw [Real.rpow_neg hx.le] at h
      have hxφ : 0 < x ^ φ := by positivity
      field_simp at h ⊢
      linarith
    have := congrArg (fun y : ℝ => y ^ (1 / φ)) e
    rw [← Real.rpow_mul hx.le, mul_one_div_cancel hφ0.ne', Real.rpow_one,
      Real.mul_rpow hAqp.le (by positivity), ← Real.rpow_mul hL.le,
      mul_one_div_cancel hφ0.ne', Real.rpow_one] at this
    exact this
  · intro h
    rw [h, Real.mul_rpow (by positivity) hL.le, ← Real.rpow_mul hAqp.le,
      show 1 / φ * -φ = -1 by field_simp, Real.rpow_neg_one, Real.rpow_neg hL.le]
    field_simp

/-- AKMM, (13.65), p. 400: **the quality-ladder monopolist**. Facing (13.63), the leader's
profit `AL^φqx^{1−φ} − ψqx` is maximised over `x ≥ 0` at `x = X^{1/φ}L` (independent of `q`),
where the price is `ψq/(1−φ)` and profit is `π̄q`. -/
theorem eq_13_65 {A φ ψ q L x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hq : 0 < q) (hL : 0 < L) (hx : 0 ≤ x) :
    A * q * L ^ φ * x ^ (1 - φ) - ψ * q * x ≤
        A * q * L ^ φ * romerXMon A φ ψ L ^ (1 - φ) - ψ * q * romerXMon A φ ψ L ∧
      A * q * L ^ φ * romerXMon A φ ψ L ^ (-φ) = ψ * q / (1 - φ) ∧
      ψ * q / (1 - φ) * romerXMon A φ ψ L - ψ * q * romerXMon A φ ψ L = qlPiBar A φ ψ L * q := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : romerX (A * q) φ (ψ * q) = romerX A φ ψ := by unfold romerX; field_simp
  have hmon : romerXMon (A * q) φ (ψ * q) L = romerXMon A φ ψ L := by
    unfold romerXMon; rw [hX]
  have h := eq_13_33 (A := A * q) (ψ := ψ * q) (by positivity) hφ0 hφ1 (by positivity) hL hx
  rw [hmon] at h
  refine ⟨h.1, h.2, ?_⟩
  have hp := eq_13_34 (A := A) (Ly := L) hA hφ1 hψ (φ := φ)
  unfold qlPiBar
  rw [show 1 / φ - 1 = (1 - φ) / φ by field_simp] at hp
  rw [show ψ * q / (1 - φ) * romerXMon A φ ψ L - ψ * q * romerXMon A φ ψ L =
    q * (ψ / (1 - φ) * romerXMon A φ ψ L - ψ * romerXMon A φ ψ L) by ring, hp]
  ring

/-- AKMM, p. 401: **aggregates**. With every line at `x = X^{1/φ}L` and `Q = ∫q`, output is
`Y = (A/(1−φ))X^{(1−φ)/φ}QL` and intermediate spending is
`X(t) = ψQx = ψ^{1−1/φ}(A(1−φ))^{1/φ}QL`. -/
theorem quality_aggregates {A φ ψ Q L : ℝ} (hA : 0 < A) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hL : 0 < L) :
    A / (1 - φ) * L ^ φ * (Q * romerXMon A φ ψ L ^ (1 - φ)) =
        A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Q * L ∧
      ψ * Q * romerXMon A φ ψ L = ψ ^ (1 - 1 / φ) * (A * (1 - φ)) ^ (1 / φ) * Q * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
  refine ⟨?_, ?_⟩
  · rw [eq_13_35 (N := Q) hL hX]; ring
  · unfold romerXMon romerX
    rw [Real.div_rpow (by positivity) hψ.le, Real.rpow_sub hψ, Real.rpow_one]
    ring

/-- AKMM, (13.A.26), p. 861: **limit pricing**. With quality-weighted perfect substitutes the
final producer buys the leader's version `v` (quality `λq'`) rather than the follower's
(quality `q'`, priced at marginal cost `ψq'`) iff
`p/(λq')^{1/(1−φ)} ≤ ψq'/q'^{1/(1−φ)}`, i.e. iff the markup `μ = p/(ψλq')` satisfies
`μ ≤ λ^{φ/(1−φ)}`. -/
theorem eq_13_A_26 {φ ψ lam q' p : ℝ} (hφ1 : φ < 1) (hψ : 0 < ψ) (hlam : 0 < lam)
    (hq' : 0 < q') :
    p / (lam * q') ^ (1 / (1 - φ)) ≤ ψ * q' / q' ^ (1 / (1 - φ)) ↔
      p / (ψ * (lam * q')) ≤ lam ^ (φ / (1 - φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  rw [Real.mul_rpow hlam.le hq'.le]
  have hq1 : 0 < q' ^ (1 / (1 - φ)) := by positivity
  have hl1 : 0 < lam ^ (1 / (1 - φ)) := by positivity
  have hlφ : lam ^ (1 / (1 - φ)) = lam * lam ^ (φ / (1 - φ)) := by
    rw [show 1 / (1 - φ) = φ / (1 - φ) + 1 by field_simp; ring, Real.rpow_add hlam,
      Real.rpow_one]; ring
  rw [div_le_div_iff₀ (by positivity) hq1, div_le_iff₀ (by positivity), hlφ]
  constructor <;> intro h <;> nlinarith [h, mul_pos hq1 (mul_pos hψ hq'),
    Real.rpow_pos_of_pos hlam (φ / (1 - φ))]

/-- AKMM, (13.64), p. 400, and App. 13.A.9: **the drastic-innovation condition**. The monopoly
markup `1/(1−φ)` is feasible under limit pricing, `1/(1−φ) ≤ λ^{φ/(1−φ)}`, iff
`λ ≥ (1/(1−φ))^{(1−φ)/φ}`. -/
theorem eq_13_64 {φ lam : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hlam : 0 < lam) :
    1 / (1 - φ) ≤ lam ^ (φ / (1 - φ)) ↔ (1 / (1 - φ)) ^ ((1 - φ) / φ) ≤ lam := by
  have h1φ : 0 < 1 - φ := by linarith
  have hp : 0 < (1 - φ) / φ := by positivity
  have hinv : (lam ^ (φ / (1 - φ))) ^ ((1 - φ) / φ) = lam := by
    rw [← Real.rpow_mul hlam.le, show φ / (1 - φ) * ((1 - φ) / φ) = 1 by field_simp,
      Real.rpow_one]
  constructor
  · intro h
    have := Real.rpow_le_rpow (by positivity) h hp.le
    rwa [hinv] at this
  · intro h
    have := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ φ / (1 - φ))
    rwa [← Real.rpow_mul (by positivity), show (1 - φ) / φ * (φ / (1 - φ)) = 1 by field_simp,
      Real.rpow_one] at this

/-- The profit of a leader charging markup `μ` over marginal cost, up to a positive factor:
`(μ − 1)μ^{−1/φ}`. -/
noncomputable def qlMarkupProfit (φ μ : ℝ) : ℝ := (μ - 1) * μ ^ (-(1 / φ))

/-- AKMM, (13.A.27), p. 861: **profits and the markup**. With demand (13.63), profit at markup
`μ` is proportional to `(μ − 1)μ^{−1/φ}`, which is strictly increasing on `[1, 1/(1−φ)]` and
strictly decreasing on `[1/(1−φ), ∞)`. Hence under incremental innovation,
`λ^{φ/(1−φ)} < 1/(1−φ)`, the best feasible markup is the limit price `μ = λ^{φ/(1−φ)}`, and
under (13.64) it is the monopoly markup `1/(1−φ)`. -/
theorem eq_13_A_27 {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    StrictMonoOn (qlMarkupProfit φ) (Set.Icc 1 (1 / (1 - φ))) ∧
      StrictAntiOn (qlMarkupProfit φ) (Set.Ici (1 / (1 - φ))) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hd : ∀ μ, 0 < μ → HasDerivAt (qlMarkupProfit φ)
      (μ ^ (-(1 / φ) - 1) * ((1 - (1 - φ) * μ) / φ)) μ := fun μ hμ => by
    have h1 := ((hasDerivAt_id' μ).sub_const 1).mul
      (Real.hasDerivAt_rpow_const (p := -(1 / φ)) (Or.inl hμ.ne'))
    unfold qlMarkupProfit
    convert h1 using 1
    rw [Real.rpow_sub_one hμ.ne']
    field_simp
    ring
  have hcont : ∀ S : Set ℝ, S ⊆ Set.Ioi 0 → ContinuousOn (qlMarkupProfit φ) S := fun S hS μ hμ =>
    (hd μ (hS hμ)).continuousAt.continuousWithinAt
  have h1 : (1 : ℝ) ≤ 1 / (1 - φ) := by rw [le_div_iff₀ h1φ]; linarith
  refine ⟨strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcont _ fun μ hμ => by
    simp only [Set.mem_Icc] at hμ; exact Set.mem_Ioi.mpr (by linarith)) fun μ hμ => ?_,
    strictAntiOn_of_deriv_neg (convex_Ici _) (hcont _ fun μ hμ => by
    simp only [Set.mem_Ici] at hμ; exact Set.mem_Ioi.mpr (by linarith)) fun μ hμ => ?_⟩
  · rw [interior_Icc] at hμ
    have hμ0 : 0 < μ := by linarith [hμ.1]
    rw [(hd μ hμ0).deriv]
    have : (1 - φ) * μ < 1 := by have := hμ.2; rw [lt_div_iff₀ h1φ] at this; linarith
    apply mul_pos (by positivity)
    exact div_pos (by linarith) hφ0
  · rw [interior_Ici] at hμ
    have hμ0 : 0 < μ := by simp only [Set.mem_Ioi] at hμ; linarith
    rw [(hd μ hμ0).deriv]
    have : 1 < (1 - φ) * μ := by
      simp only [Set.mem_Ioi] at hμ; rw [div_lt_iff₀ h1φ] at hμ; linarith
    apply mul_neg_of_pos_of_neg (by positivity)
    exact div_neg_of_neg_of_pos (by linarith) hφ0

/-- AKMM, p. 401: **the research first-order condition**. The research firm's objective
`(ηZ/q)λV − Z` is linear in `Z ≥ 0`; a positive `Z` is optimal iff `ηλV/q = 1`, and then the
ratio `V/q = 1/(λη)` is the same on every line. -/
theorem quality_research_foc {η lam V q Z : ℝ} (hZ : 0 < Z) :
    (∀ Z', 0 ≤ Z' → η * Z' / q * lam * V - Z' ≤ η * Z / q * lam * V - Z) ↔
      η / q * lam * V = 1 := by
  have key : ∀ Z', η * Z' / q * lam * V - Z' = Z' * (η / q * lam * V - 1) := fun Z' => by ring
  simp only [key]
  constructor
  · intro h
    have h0 := h 0 le_rfl
    have h2 := h (2 * Z) (by linarith)
    rw [zero_mul] at h0
    nlinarith
  · intro h Z' _
    rw [h]; simp

/-- AKMM, p. 401: free entry gives `V/q = 1/(λη)` (the first-order condition rearranged). -/
theorem quality_V_over_q {η lam V q : ℝ} (hη : 0 < η) (hlam : 0 < lam) (hq : 0 < q)
    (h : η / q * lam * V = 1) : V / q = 1 / (lam * η) := by
  field_simp at h ⊢; linarith

/-- AKMM, p. 401: **the Arrow replacement effect**. If entrants are indifferent,
`ηλV/q = 1`, with `V > 0`, then an incumbent improving its own product gains only
`(λ − 1)V`: `η(λ−1)V/q < ηλV/q = 1`, so its research objective `(ηZ/q)(λ−1)V − Z` is
uniquely maximised at `Z = 0`. -/
theorem quality_arrow_replacement {η lam V q : ℝ} (hη : 0 < η) (hq : 0 < q)
    (hV : 0 < V) (hfoc : η / q * lam * V = 1) :
    η / q * (lam - 1) * V < η / q * lam * V ∧
      ∀ Z, 0 < Z → η * Z / q * (lam - 1) * V - Z < 0 := by
  have hlt : η / q * (lam - 1) * V < η / q * lam * V := by
    have : 0 < η / q * V := by positivity
    nlinarith
  refine ⟨hlt, fun Z hZ => ?_⟩
  have e : η * Z / q * (lam - 1) * V - Z = Z * (η / q * (lam - 1) * V - 1) := by ring
  rw [e]
  exact mul_neg_of_pos_of_neg hZ (by linarith)

/-- AKMM, p. 402: **the leader's value**. With constant `r` and destruction rate `z`
(`r + z > 0`), the value `V` of a line of quality `q` solves `V̇ = (r + z)V − π̄q`; without a
bubble (`e^{−(r+z)T}V(T) → 0`) it is `V = π̄q/(r + z)`, so `V/q = π̄/(r + z)`. -/
theorem quality_value {r z πq : ℝ} {V : ℝ → ℝ} (hrz : 0 < r + z)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V ((r + z) * V t - πq) t)
    (hnb : Tendsto (fun T => Real.exp (-(r + z) * T) * V T) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → V t = πq / (r + z) := by
  have h := jones_value_unique (r := r + z) (n := 0) (π0 := πq) (V := V) hrz
    (fun t ht => by simpa using hV t ht) hnb
  intro t ht
  rw [h t ht]
  simp

/-- AKMM, p. 403: **one quality ladder**. If the number of steps by time `t` is Poisson with
mean `zt`, the expected quality `∑ₖ e^{−zt}(zt)^k/k! · q_0λ^k` is `q_0e^{(λ−1)zt}`, and it grows
at the rate `(λ − 1)z`, the mean-field law `Q̇ = (λ−1)zQ` used for the aggregate index. -/
theorem quality_single_ladder {z lam q0 t : ℝ} :
    ∑' k : ℕ, Real.exp (-(z * t)) * (z * t) ^ k / (k.factorial) * (q0 * lam ^ k) =
        q0 * Real.exp ((lam - 1) * z * t) ∧
      HasDerivAt (fun s => q0 * Real.exp ((lam - 1) * z * s))
        ((lam - 1) * z * (q0 * Real.exp ((lam - 1) * z * t))) t := by
  refine ⟨?_, ?_⟩
  · have hexp : Real.exp (lam * (z * t)) = ∑' k : ℕ, (lam * (z * t)) ^ k / (k.factorial) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have e : ∀ k : ℕ, Real.exp (-(z * t)) * (z * t) ^ k / (k.factorial) * (q0 * lam ^ k) =
        q0 * Real.exp (-(z * t)) * ((lam * (z * t)) ^ k / (k.factorial)) := fun k => by
      rw [mul_pow]; ring
    simp only [e]
    rw [tsum_mul_left, ← hexp, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · have := (((hasDerivAt_id' t).const_mul ((lam - 1) * z)).exp).const_mul q0
    convert this using 1
    ring

/-- AKMM, (13.66), p. 403: **the balanced growth path**. If `r + z = ληπ̄` (free entry with
`V/q = π̄/(r + z)`), `r = σg + ρ` (Euler) and `g = (λ − 1)z` (the mean-field index), with
`λ > 1`, `σ > 0`, then `g = (ληπ̄ − ρ)/(σ + 1/(λ−1))`, `r = ρ + (ληπ̄ − ρ)/(1 + 1/(σ(λ−1)))`
and `z = (ληπ̄ − ρ)/(1 + (λ−1)σ)`. -/
theorem eq_13_66 {lam η πb σ ρ r z g : ℝ} (hlam : 1 < lam) (hσ : 0 < σ)
    (hfree : r + z = lam * η * πb) (heuler : r = σ * g + ρ) (hg : g = (lam - 1) * z) :
    g = (lam * η * πb - ρ) / (σ + 1 / (lam - 1)) ∧
      r = ρ + (lam * η * πb - ρ) / (1 + 1 / (σ * (lam - 1))) ∧
      z = (lam * η * πb - ρ) / (1 + (lam - 1) * σ) := by
  have hl : 0 < lam - 1 := by linarith
  have hz : z = (lam * η * πb - ρ) / (1 + (lam - 1) * σ) := by
    rw [eq_div_iff (by positivity)]
    rw [heuler, hg] at hfree
    linarith
  refine ⟨?_, ?_, hz⟩
  · rw [hg, hz]; field_simp; ring
  · rw [heuler, hg, hz]; field_simp; ring

/-- AKMM, p. 403: **comparative statics**. When `ληπ̄ > ρ` (positive growth), the growth rate
`g(η, π̄, ρ, σ) = (ληπ̄ − ρ)/(σ + 1/(λ−1))` is strictly increasing in `η` and in `π̄` (hence in
`L`, since `π̄ ∝ L`), strictly decreasing in `ρ`, and strictly decreasing in `σ > 0`. -/
theorem quality_comparative_statics {lam η πb σ ρ : ℝ} (hlam : 1 < lam) (hσ : 0 < σ)
    (hπ : 0 < πb) (hη : 0 < η) (hpos : ρ < lam * η * πb) :
    StrictMonoOn (fun η' => (lam * η' * πb - ρ) / (σ + 1 / (lam - 1))) (Set.Ioi 0) ∧
      StrictMonoOn (fun π' => (lam * η * π' - ρ) / (σ + 1 / (lam - 1))) (Set.Ioi 0) ∧
      StrictAnti (fun ρ' => (lam * η * πb - ρ') / (σ + 1 / (lam - 1))) ∧
      StrictAntiOn (fun σ' => (lam * η * πb - ρ) / (σ' + 1 / (lam - 1))) (Set.Ioi 0) := by
  have hl : 0 < lam - 1 := by linarith
  have hden : 0 < σ + 1 / (lam - 1) := by positivity
  refine ⟨fun a _ b _ hab => ?_, fun a _ b _ hab => ?_, fun a b hab => ?_,
    fun a ha b _ hab => ?_⟩
  · apply div_lt_div_of_pos_right _ hden
    have : lam * a * πb < lam * b * πb := by
      have := mul_lt_mul_of_pos_left hab (by linarith : (0 : ℝ) < lam)
      exact mul_lt_mul_of_pos_right this hπ
    linarith
  · apply div_lt_div_of_pos_right _ hden
    have := mul_lt_mul_of_pos_left hab (by positivity : (0 : ℝ) < lam * η)
    linarith
  · exact div_lt_div_of_pos_right (by linarith) hden
  · simp only [Set.mem_Ioi] at ha
    exact div_lt_div_of_pos_left (by linarith) (by positivity) (by linarith)

/-- AKMM, p. 403: **growth rises with the step size `λ`**. For `λ > 1` with `ληπ̄ > ρ`,
`g(λ) = (ληπ̄ − ρ)/(σ + 1/(λ−1))` is strictly increasing in `λ`. -/
theorem quality_growth_mono_lambda {η πb σ ρ : ℝ} (hσ : 0 < σ) (hπ : 0 < πb) (hη : 0 < η) :
    StrictMonoOn (fun lam => (lam * η * πb - ρ) / (σ + 1 / (lam - 1)))
      {lam | 1 < lam ∧ ρ < lam * η * πb} := by
  intro a ha b hb hab
  have ha1 : 0 < a - 1 := by linarith [ha.1]
  have hb1 : 0 < b - 1 := by linarith [hb.1]
  have hda : 0 < σ + 1 / (a - 1) := by positivity
  have hdb : 0 < σ + 1 / (b - 1) := by positivity
  have hden : σ + 1 / (b - 1) < σ + 1 / (a - 1) := by
    have := one_div_lt_one_div_of_lt ha1 (by linarith : a - 1 < b - 1)
    linarith
  have hnum : a * η * πb - ρ < b * η * πb - ρ := by
    have := mul_lt_mul_of_pos_right hab (mul_pos hη hπ)
    linarith
  calc (a * η * πb - ρ) / (σ + 1 / (a - 1)) < (b * η * πb - ρ) / (σ + 1 / (a - 1)) :=
        div_lt_div_of_pos_right hnum hda
    _ < (b * η * πb - ρ) / (σ + 1 / (b - 1)) :=
        div_lt_div_of_pos_left (by linarith [hb.2]) hdb hden

/-- AKMM, p. 403: **growth falls with the cost `ψ`**: `π̄ = φAX^{(1−φ)/φ}L` with
`X = A(1−φ)/ψ` is strictly decreasing in `ψ > 0`. -/
theorem quality_growth_anti_psi {A φ L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hL : 0 < L) : StrictAntiOn (fun ψ => qlPiBar A φ ψ L) (Set.Ioi 0) := by
  have h1φ : 0 < 1 - φ := by linarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold qlPiBar romerX
  have hlt : A * (1 - φ) / b < A * (1 - φ) / a :=
    div_lt_div_of_pos_left (by positivity) ha hab
  have := Real.rpow_lt_rpow (by positivity) hlt (by positivity : (0 : ℝ) < (1 - φ) / φ)
  have hc : 0 < φ * A := by positivity
  nlinarith [mul_lt_mul_of_pos_left this hc]

end AKMM.Growth
