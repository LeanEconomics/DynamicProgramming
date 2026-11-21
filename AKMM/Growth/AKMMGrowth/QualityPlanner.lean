/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.QualityLadders

/-!
# Quality ladders: the planner

AKMM, §13.5.2 (p. 404) and Appendix 13.A.10 (pp. 861–862). Write
`κ = (A/(1−φ))(A/ψ)^{(1−φ)/φ}L`, so that the planner's output is `Y^{SP} = κQ`.

* Static: `x^{SP} = (A/ψ)^{1/φ}L` maximises net output on each line, `x^{SP} > x^{DE}`
  (`quality_planner_static`); `X^{SP} = (1−φ)Y^{SP}`, `Y − X = φY`, `Y^{SP} > Y^{DE}`
  (`quality_planner_aggregates`).
* Dynamic: with `Z = φY − C` and `Q̇ = (λ−1)ηZ`, the planner's problem is an AK problem with
  return `(λ−1)ηφκ`; the balanced path with growth (13.A.28)
  `g^{SP} = ((λ−1)ηφκ − ρ)/σ` is optimal (`eq_13_A_28`), with the stated comparative statics
  (`quality_planner_comparative_statics`).
* The printed Hamiltonian has `e^{ρt}`; with it the same conditions would give
  `((λ−1)ηφκ + ρ)/σ` (`quality_planner_hamiltonian_sign`).
* `g^{SP}` can be above or below `g^{DE}` (`quality_sp_vs_de_ambiguous`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, App. 13.A.10, p. 861: **the planner's static problem**. On a line of quality `q > 0`,
net output `(A/(1−φ))L^φqx^{1−φ} − ψqx` is maximised over `x ≥ 0` at `x^{SP} = (A/ψ)^{1/φ}L`,
and `x^{SP} > x^{DE} = (A(1−φ)/ψ)^{1/φ}L`. -/
theorem quality_planner_static {A φ ψ q L x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hq : 0 < q) (hL : 0 < L) (hx : 0 ≤ x) :
    A * q / (1 - φ) * L ^ φ * x ^ (1 - φ) - ψ * q * x ≤
        A * q / (1 - φ) * L ^ φ * ((A / ψ) ^ (1 / φ) * L) ^ (1 - φ) -
          ψ * q * ((A / ψ) ^ (1 / φ) * L) ∧
      romerXMon A φ ψ L < (A / ψ) ^ (1 / φ) * L := by
  have h := eq_13_A_16 (A := A * q) (ψ := ψ * q) (by positivity) hφ0 hφ1 (by positivity) hL hx
  rw [show A * q / (ψ * q) = A / ψ by field_simp] at h
  refine ⟨h.1, ?_⟩
  have hr := romer_machine_ratio hA hφ0 hφ1 hψ hL
  have hpos : 0 < (A / ψ) ^ (1 / φ) * L := by positivity
  have := hr.1
  rw [div_eq_iff hpos.ne'] at this
  rw [this]
  nlinarith [hr.2.1]

/-- AKMM, App. 13.A.10, p. 862: **the planner's aggregates**. With `x^{SP}` on every line,
`Y^{SP} = (A/(1−φ))(A/ψ)^{(1−φ)/φ}QL`, `X^{SP} = ψLQ(A/ψ)^{1/φ} = (1−φ)Y^{SP}`, so
`Y^{SP} − X^{SP} = φY^{SP}`, and `Y^{SP} > Y^{DE} = (A/(1−φ))(A(1−φ)/ψ)^{(1−φ)/φ}QL`. -/
theorem quality_planner_aggregates {A φ ψ Q L : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hQ : 0 < Q) (hL : 0 < L) :
    A / (1 - φ) * L ^ φ * (Q * ((A / ψ) ^ (1 / φ) * L) ^ (1 - φ)) =
        A / (1 - φ) * (A / ψ) ^ ((1 - φ) / φ) * Q * L ∧
      ψ * L * Q * (A / ψ) ^ (1 / φ) = (1 - φ) * (A / (1 - φ) * (A / ψ) ^ ((1 - φ) / φ) * Q * L) ∧
      A / (1 - φ) * romerX A φ ψ ^ ((1 - φ) / φ) * Q * L <
        A / (1 - φ) * (A / ψ) ^ ((1 - φ) / φ) * Q * L := by
  have h1φ : 0 < 1 - φ := by linarith
  have hAψ : 0 < A / ψ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.mul_rpow (by positivity) hL.le, ← Real.rpow_mul hAψ.le,
      show 1 / φ * (1 - φ) = (1 - φ) / φ by ring]
    have : L ^ φ * L ^ (1 - φ) = L := by
      rw [← Real.rpow_add hL, show φ + (1 - φ) = 1 by ring, Real.rpow_one]
    linear_combination (A / (1 - φ) * Q * (A / ψ) ^ ((1 - φ) / φ)) * this
  · rw [show 1 / φ = (1 - φ) / φ + 1 by field_simp; ring, Real.rpow_add hAψ, Real.rpow_one]
    field_simp
  · have hlt : romerX A φ ψ < A / ψ := by
      unfold romerX
      rw [div_lt_div_iff_of_pos_right hψ]
      nlinarith
    have hX : 0 < romerX A φ ψ := by unfold romerX; positivity
    have := Real.rpow_lt_rpow hX.le hlt (by positivity : (0 : ℝ) < (1 - φ) / φ)
    have hc : 0 < A / (1 - φ) := by positivity
    have hQL : 0 < Q * L := by positivity
    nlinarith [mul_lt_mul_of_pos_left this hc, mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left this hc) hQL]

/-- AKMM, (13.A.28), p. 862: **the planner's growth rate**. With `Q̇ = (λ−1)η(φκQ − C)`
(`Z = φY^{SP} − C`, `z = ηZ/Q`, `Q̇ = (λ−1)zQ`), the planner's problem in `S = Q/((λ−1)η)` is
the AK problem `Ṡ = (λ−1)ηφκS − C`. If `σ(λ−1)ηφκ > (λ−1)ηφκ − ρ` and `u` is concave with
`u'(C) = C^{−σ}`, the path `C(t) = ((λ−1)ηφκ − g^{SP})S_0e^{g^{SP}t}` with
`g^{SP} = ((λ−1)ηφκ − ρ)/σ` is catching-up optimal against every path from `Q_0` with
`Q ≥ 0` and positive continuous consumption. -/
theorem eq_13_A_28 {lam η φκ σ ρ Q0 : ℝ} {u : ℝ → ℝ} {Q' C' : ℝ → ℝ} (hlam : 1 < lam)
    (hη : 0 < η) (hσ : 0 < σ) (hQ0 : 0 < Q0)
    (hbound : (lam - 1) * η * φκ - ρ < σ * ((lam - 1) * η * φκ))
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hQ' : ∀ t, 0 ≤ t → 0 ≤ Q' t) (hC' : ∀ t, 0 ≤ t → 0 < C' t)
    (hCc' : ContinuousOn C' (Set.Ici 0))
    (hQd' : ∀ t, 0 ≤ t → HasDerivAt Q' ((lam - 1) * η * (φκ * Q' t - C' t)) t)
    (h0 : Q' 0 = Q0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (C' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) *
        u (((lam - 1) * η * φκ - ((lam - 1) * η * φκ - ρ) / σ) *
          (Q0 / ((lam - 1) * η) * Real.exp (((lam - 1) * η * φκ - ρ) / σ * t)))) + ε := by
  have hl : 0 < (lam - 1) * η := mul_pos (by linarith) hη
  have hb : (lam - 1) * η * φκ - 0 - ρ < σ * ((lam - 1) * η * φκ - 0 - 0) := by
    simpa using hbound
  have h := ak_optimal (A := (lam - 1) * η * φκ) (δ := 0) (n := 0) (k0 := Q0 / ((lam - 1) * η))
    (k' := fun t => Q' t / ((lam - 1) * η)) (c' := C') hσ (by positivity) hb hconc hu
    (fun t ht => by have := hQ' t ht; positivity) hC' hCc' (fun t ht => by
      have hl1 : lam - 1 ≠ 0 := by linarith
      convert (hQd' t ht).div_const ((lam - 1) * η) using 1
      field_simp
      ring) (by rw [h0])
  simp only [sub_zero, akG] at h
  exact h

/-- AKMM, App. 13.A.10, p. 862: the comparative statics of (13.A.28): `g^{SP}` is strictly
increasing in `λ`, in `η` and in `κ` (so in `L`), strictly decreasing in `ρ`, and strictly
decreasing in `σ > 0` when positive. -/
theorem quality_planner_comparative_statics {lam η φκ σ ρ : ℝ} (hlam : 1 < lam) (hη : 0 < η)
    (hκ : 0 < φκ) (hσ : 0 < σ) (hpos : ρ < (lam - 1) * η * φκ) :
    StrictMono (fun l => ((l - 1) * η * φκ - ρ) / σ) ∧
      StrictMono (fun e => ((lam - 1) * e * φκ - ρ) / σ) ∧
      StrictMono (fun k => ((lam - 1) * η * k - ρ) / σ) ∧
      StrictAnti (fun r => ((lam - 1) * η * φκ - r) / σ) ∧
      StrictAntiOn (fun s => ((lam - 1) * η * φκ - ρ) / s) (Set.Ioi 0) := by
  have hl : 0 < lam - 1 := by linarith
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_,
    fun a ha b _ hab => ?_⟩
  · apply div_lt_div_of_pos_right _ hσ
    nlinarith [mul_pos hη hκ]
  · apply div_lt_div_of_pos_right _ hσ
    nlinarith [mul_pos hl hκ]
  · apply div_lt_div_of_pos_right _ hσ
    nlinarith [mul_pos hl hη]
  · exact div_lt_div_of_pos_right (by linarith) hσ
  · simp only [Set.mem_Ioi] at ha
    exact div_lt_div_of_pos_left (by linarith) ha hab

/-- AKMM, App. 13.A.10, p. 862: **the sign of the discount in the Hamiltonian**. The printed
Hamiltonian has `e^{ρt}`. With it, the first-order condition `e^{ρt}C^{−σ} = μ(λ−1)η` and the
costate equation `μ̇ = −μ(λ−1)ηφκ` give `Ċ/C = ((λ−1)ηφκ + ρ)/σ`, which differs from (13.A.28)
whenever `ρ ≠ 0`; (13.A.28) needs `e^{−ρt}`. -/
theorem quality_planner_hamiltonian_sign {lam η φκ σ ρ t Cdot : ℝ} {C μ : ℝ → ℝ}
    (hσ : 0 < σ) (hC : 0 < C t) (hCd : HasDerivAt C Cdot t)
    (hfoc : ∀ s, Real.exp (ρ * s) * C s ^ (-σ) = μ s * ((lam - 1) * η))
    (hcost : HasDerivAt μ (-(μ t * ((lam - 1) * η * φκ))) t) :
    Cdot / C t = ((lam - 1) * η * φκ + ρ) / σ ∧
      (((lam - 1) * η * φκ + ρ) / σ = ((lam - 1) * η * φκ - ρ) / σ ↔ ρ = 0) := by
  refine ⟨?_, ?_⟩
  · have h := eq_13_19 (A := (lam - 1) * η * φκ) (δ := 0) (ρ := -ρ) (n := 0)
      (μ := fun s => μ s * ((lam - 1) * η)) hσ hC hCd (fun s => by
        rw [← hfoc s]; simp) (by
        convert hcost.mul_const ((lam - 1) * η) using 1; ring)
    rw [h]
    unfold akG
    ring
  · constructor
    · intro h
      field_simp at h
      linarith
    · intro h; rw [h]; ring

/-- AKMM, p. 404 and App. 13.A.10: **`g^{SP}` versus `g^{DE}` is ambiguous**. Take `φ = 1/2`,
`A = 2`, `ψ = 1`, `η = 1`, so that `π̄ = L` and `φκ = 4L`, and `σ = 1`. With `λ = 2`, `L = 1`,
`ρ = 1/10`, `g^{DE} = 19/20 < g^{SP} = 39/10`; with `λ = 11/10`, `L = 10`, `ρ = 39/10`,
`g^{DE} = 71/110 > g^{SP} = 1/10 > 0`. -/
theorem quality_sp_vs_de_ambiguous :
    (∀ L : ℝ, qlPiBar 2 (1 / 2) 1 L = L) ∧
    (∀ L : ℝ, 1 / 2 * (2 / (1 - 1 / 2) * (2 / 1 : ℝ) ^ (((1 : ℝ) - 1 / 2) / (1 / 2)) * L) =
      4 * L) ∧
    ((2 * 1 * 1 - 1 / 10) / (1 + 1 / (2 - 1)) : ℝ) < ((2 - 1) * 1 * (4 * 1) - 1 / 10) / 1 ∧
    (((11 / 10 - 1) * 1 * (4 * 10) - 39 / 10) / 1 : ℝ) <
      (11 / 10 * 1 * 10 - 39 / 10) / (1 + 1 / (11 / 10 - 1)) ∧
    (0 : ℝ) < ((11 / 10 - 1) * 1 * (4 * 10) - 39 / 10) / 1 := by
  refine ⟨fun L => ?_, fun L => ?_, by norm_num, by norm_num, by norm_num⟩
  · unfold qlPiBar romerX
    rw [show ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 by norm_num, Real.rpow_one]
    norm_num
  · rw [show ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 by norm_num, Real.rpow_one]
    ring

end AKMM.Growth
