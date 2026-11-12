/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMGrowth.RomerDynamics
import AKMMGrowth.AKGrowth

/-!
# Expanding varieties: the planner and policy

AKMM, §13.5.1 (pp. 391–392) and Appendix 13.A.6 (pp. 853–854).

* The static problem (13.A.16): `x^{SP} = (A/ψ)^{1/φ}L_y` is the unique maximiser
  (`eq_13_A_16`); collapsing the constraints gives (13.A.17) (`eq_13_A_17`).
* The first-order conditions (13.A.18)–(13.A.19) give the Euler equation (13.A.21)
  (`eq_13_A_21`), and balanced growth gives `L_y^{SP}` and `g^{SP}` (13.50)–(13.51)
  (`romer_planner_Ly`, `eq_13_50`, `eq_13_51`).
* With `X = (M/η)N`, `M = ψ(A/ψ)^{1/φ}φ/(1−φ)`, the planner's problem is an AK problem
  `Ẋ = ηLX − c`; under (13.49) the balanced path is catching-up optimal from every `N(0)`, so
  there are no transitional dynamics (`romer_planner_optimal`).
* `x^{DE}/x^{SP} = (1−φ)^{1/φ} < 1`, not the printed `(1−φ)^φ` (`romer_machine_ratio`,
  `romer_machine_ratio_printed_false`).
* A purchase subsidy `τ` gives the planner's machine quantity iff `τ = φ` (`1 − τ = 1 − φ`), not
  the printed `1 − τ = (1−φ)^{−1}`, which lowers machine use (`romer_subsidy`); even then growth
  `(ηL − ρ)/(1 + σ)` is below `g^{SP}` (`romer_subsidy_not_efficient`).
* The decentralised growth rate is strictly below the planner's (`romer_planner_growth_gt`).
-/

namespace AKMM.Growth

open Real Filter Topology

/-- AKMM, (13.A.16), p. 853: **the planner's static problem**. Per variety, final output net of
machine costs, `(A/(1−φ))L_y^φx^{1−φ} − ψx`, is maximised over `x ≥ 0` at
`x^{SP} = (A/ψ)^{1/φ}L_y`, where `AL_y^φx^{−φ} = ψ`. -/
theorem eq_13_A_16 {A φ ψ Ly x : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) (hx : 0 ≤ x) :
    A / (1 - φ) * Ly ^ φ * x ^ (1 - φ) - ψ * x ≤
        A / (1 - φ) * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (1 - φ) - ψ * ((A / ψ) ^ (1 / φ) * Ly) ∧
      A * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (-φ) = ψ := by
  have h1φ : 0 < 1 - φ := by linarith
  have hX : romerX (A / (1 - φ)) φ ψ = A / ψ := by unfold romerX; field_simp
  have h := eq_13_33 (A := A / (1 - φ)) (by positivity) hφ0 hφ1 hψ hLy hx
  unfold romerXMon at h
  rw [hX] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have : A * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (-φ) =
      (1 - φ) * (A / (1 - φ) * Ly ^ φ * ((A / ψ) ^ (1 / φ) * Ly) ^ (-φ)) := by field_simp
  rw [this, h2]
  field_simp

/-- AKMM, (13.A.17), p. 853: with `x = (A/ψ)^{1/φ}L_y` for every variety, the resource
constraint (13.48) `c = Y − ψNx` is `c = M L_yN` with `M = ψ(A/ψ)^{1/φ}φ/(1−φ)`. -/
theorem eq_13_A_17 {A φ ψ Ly N : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) :
    A / (1 - φ) * Ly ^ φ * (N * ((A / ψ) ^ (1 / φ) * Ly) ^ (1 - φ)) -
        ψ * N * ((A / ψ) ^ (1 / φ) * Ly) =
      ψ * (A / ψ) ^ (1 / φ) * (φ / (1 - φ)) * Ly * N := by
  have h1φ : 0 < 1 - φ := by linarith
  have hAψ : 0 < A / ψ := by positivity
  rw [Real.mul_rpow (by positivity) hLy.le, ← Real.rpow_mul hAψ.le,
    show 1 / φ * (1 - φ) = 1 / φ - 1 by field_simp, Real.rpow_sub_one hAψ.ne']
  have : Ly ^ φ * Ly ^ (1 - φ) = Ly := by
    rw [← Real.rpow_add hLy, show φ + (1 - φ) = 1 by ring, Real.rpow_one]
  have e : A / (1 - φ) * Ly ^ φ * (N * ((A / ψ) ^ (1 / φ) / (A / ψ) * Ly ^ (1 - φ))) =
      ψ / (1 - φ) * (A / ψ) ^ (1 / φ) * N * (Ly ^ φ * Ly ^ (1 - φ)) := by
    field_simp
  rw [e, this]
  field_simp
  ring

/-- AKMM, (13.A.18)–(13.A.21), p. 854: **the planner's Euler equation**. If
`λ = e^{−ρt}c^{−σ}M/η` (13.A.18) and `λ̇ = −ηLλ` (13.A.19), then `ċ/c = (ηL − ρ)/σ`. -/
theorem eq_13_A_21 {σ ρ η L M t cdot : ℝ} {c lam : ℝ → ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (hM : 0 < M) (hc : 0 < c t) (hcd : HasDerivAt c cdot t)
    (h18 : lam = fun s => Real.exp (-ρ * s) * c s ^ (-σ) * (M / η))
    (h19 : HasDerivAt lam (-(η * L) * lam t) t) :
    cdot / c t = (η * L - ρ) / σ := by
  have h := eq_13_A_7 (n := 0) (r := η * L) (lam := fun s => lam s * (η / M)) hσ hc hcd
    (by rw [h18]; funext s; field_simp; ring_nf) (by
      convert h19.mul_const (η / M) using 1; ring)
  rw [h]

/-- AKMM, p. 854: **balanced growth for the planner**. If `ċ/c = (ηL − ρ)/σ` and, with
`L_y` constant, `ċ/c = Ṅ/N = η(L − L_y)`, then `L_y^{SP} = ((σ − 1)L + ρ/η)/σ`. -/
theorem romer_planner_Ly {σ ρ η L Ly : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (h : (η * L - ρ) / σ = η * (L - Ly)) : Ly = ((σ - 1) * L + ρ / η) / σ := by
  field_simp at h ⊢
  nlinarith [h]

/-- AKMM, (13.50), p. 392: the planner's growth rate `g^{SP} = (ηL − ρ)/σ` is
`η(L − L_y^{SP})`. -/
theorem eq_13_50 {σ ρ η L : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    η * (L - ((σ - 1) * L + ρ / η) / σ) = (η * L - ρ) / σ := by
  field_simp; ring

/-- AKMM, (13.51), p. 392: the planner's machine quantity
`x = (A/ψ)^{1/φ}L_y^{SP} = (A/ψ)^{1/φ}((σ − 1)L + ρ/η)/σ`. -/
theorem eq_13_51 {A ψ φ σ ρ η L : ℝ} :
    (A / ψ) ^ (1 / φ) * (((σ - 1) * L + ρ / η) / σ) =
      (A / ψ) ^ (1 / φ) * ((σ - 1) * L + ρ / η) / σ := by ring

/-- AKMM, (13.47)–(13.51) and p. 392: **the planner's optimum**. Under (13.49)
`(1 − σ)ηL < ρ` and `u` concave with `u'(c) = c^{−σ}`, from `N(0) = N_0 > 0` the path with
`c(t) = (ηL − g)(M/η)N_0e^{gt}`, `g = (ηL − ρ)/σ` (so `L_y = c/(MN)` is constant at `L_y^{SP}`
and `N` grows at `g`) is catching-up optimal against every path with `N' ≥ 0` from `N_0`,
`Ṅ' = ηLN' − ηc'/M` ((13.A.17) in (13.42)), and positive continuous consumption. -/
theorem romer_planner_optimal {σ ρ η L M N0 : ℝ} {u : ℝ → ℝ} {N' c' : ℝ → ℝ} (hσ : 0 < σ)
    (hη : 0 < η) (hM : 0 < M) (hN0 : 0 < N0) (h1349 : (1 - σ) * η * L < ρ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (y ^ (-σ)) y)
    (hN' : ∀ t, 0 ≤ t → 0 ≤ N' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hNd' : ∀ t, 0 ≤ t → HasDerivAt N' (η * L * N' t - η * c' t / M) t) (h0 : N' 0 = N0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u ((η * L - (η * L - ρ) / σ) *
        (M / η * N0 * Real.exp ((η * L - ρ) / σ * t)))) + ε := by
  have hbound : η * L - 0 - ρ < σ * (η * L - 0 - 0) := by nlinarith
  have h := ak_optimal (A := η * L) (δ := 0) (n := 0) (k0 := M / η * N0)
    (k' := fun t => M / η * N' t) (c' := c') hσ (by positivity) hbound hconc hu
    (fun t ht => by have := hN' t ht; positivity)
    hc' hcc' (fun t ht => by
      convert (hNd' t ht).const_mul (M / η) using 1
      field_simp
      ring) (by rw [h0])
  simp only [sub_zero, akG] at h
  exact h

/-- AKMM, p. 392 and App. 13.A.10, p. 861: **machine use**. For the same `L_y > 0`,
`x^{DE}/x^{SP} = ((A(1−φ)/ψ)^{1/φ}L_y)/((A/ψ)^{1/φ}L_y) = (1−φ)^{1/φ} < 1`, so
`x^{SP}/x^{DE} = (1−φ)^{−1/φ} > 1`. -/
theorem romer_machine_ratio {A φ ψ Ly : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hψ : 0 < ψ) (hLy : 0 < Ly) :
    romerXMon A φ ψ Ly / ((A / ψ) ^ (1 / φ) * Ly) = (1 - φ) ^ (1 / φ) ∧
      (1 - φ) ^ (1 / φ) < 1 ∧ 1 < (1 - φ) ^ (-(1 / φ)) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hlt : (1 - φ) ^ (1 / φ) < 1 := Real.rpow_lt_one h1φ.le (by linarith) (by positivity)
  refine ⟨?_, hlt, ?_⟩
  · unfold romerXMon romerX
    rw [show A * (1 - φ) / ψ = (1 - φ) * (A / ψ) by ring, Real.mul_rpow h1φ.le (by positivity)]
    have : 0 < (A / ψ) ^ (1 / φ) := by positivity
    field_simp
  · rw [Real.rpow_neg h1φ.le]
    exact one_lt_inv_iff₀.mpr ⟨by positivity, hlt⟩

/-- AKMM, p. 392: **the printed factor is wrong**: for `0 < φ < 1`,
`(1−φ)^φ ≠ (1−φ)^{1/φ}`, so machine use is not "too low by a factor of `(1−φ)^φ`". -/
theorem romer_machine_ratio_printed_false {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    (1 - φ) ^ φ ≠ (1 - φ) ^ (1 / φ) := by
  have h1φ : 0 < 1 - φ := by linarith
  have hφ : φ < 1 / φ := by
    rw [lt_div_iff₀ hφ0]; nlinarith
  exact (Real.rpow_lt_rpow_of_exponent_gt h1φ (by linarith) hφ).ne'

/-- AKMM, p. 392: **the machine subsidy**. With final producers paying `(1 − τ)p` (`τ < 1`), the
inverse demand facing a monopolist is `AL_y^φx^{−φ}/(1 − τ)`, so its quantity is
`x(τ) = ((A/(1−τ))(1−φ)/ψ)^{1/φ}L_y` (by `eq_13_33`). Then `x(τ) = x^{SP}` iff `τ = φ`, i.e.
`1 − τ = 1 − φ`; and the printed choice `1 − τ = (1−φ)^{−1}` gives `x(τ) < x^{DE}`. -/
theorem romer_subsidy {A φ ψ Ly τ : ℝ} (hA : 0 < A) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hψ : 0 < ψ)
    (hLy : 0 < Ly) (hτ : τ < 1) :
    (romerXMon (A / (1 - τ)) φ ψ Ly = (A / ψ) ^ (1 / φ) * Ly ↔ τ = φ) ∧
      (1 - τ = 1 / (1 - φ) → romerXMon (A / (1 - τ)) φ ψ Ly < romerXMon A φ ψ Ly) := by
  have h1φ : 0 < 1 - φ := by linarith
  have h1τ : 0 < 1 - τ := by linarith
  have hφinv : 0 < 1 / φ := by positivity
  unfold romerXMon romerX
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have h2 := mul_right_cancel₀ hLy.ne' h
    have h3 := congrArg (fun x : ℝ => x ^ φ) h2
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      one_div_mul_cancel hφ0.ne', Real.rpow_one, Real.rpow_one] at h3
    field_simp at h3
    nlinarith [h3]
  · rw [h]
    congr 2
    field_simp
  · rw [h]
    apply mul_lt_mul_of_pos_right _ hLy
    apply Real.rpow_lt_rpow (by positivity) _ hφinv
    rw [show A / (1 / (1 - φ)) * (1 - φ) / ψ = (1 - φ) * (A * (1 - φ) / ψ) by field_simp]
    have : 0 < A * (1 - φ) / ψ := by positivity
    nlinarith

/-- AKMM, p. 392: **the subsidy does not restore efficiency**. With the subsidy `τ = φ` the
monopolist's quantity is `x^{SP}`, profits are `φ(A/(1−φ))(A/ψ)^{(1−φ)/φ}L_y` and free entry gives
`V = (φA/(η(1−φ)))(A/ψ)^{(1−φ)/φ}`, so `r = π/V = ηL_y`: this is `r = η(1−φ)θL_y` with
`θ = 1/(1−φ)`, and the balanced growth rate of `romer_theta_growth_mono` is
`(ηL − ρ)/(1 + σ)`, strictly below `g^{SP} = (ηL − ρ)/σ` when `ηL > ρ`. -/
theorem romer_subsidy_not_efficient {φ η σ ρ L : ℝ} (hφ1 : φ < 1) (hσ : 0 < σ)
    (hpos : ρ < η * L) :
    ((1 - φ) * (1 / (1 - φ)) * η * L - ρ) / ((1 - φ) * (1 / (1 - φ)) + σ) =
        (η * L - ρ) / (1 + σ) ∧ (η * L - ρ) / (1 + σ) < (η * L - ρ) / σ := by
  have h1φ : (1 - φ) ≠ 0 := by linarith
  refine ⟨by field_simp, div_lt_div_of_pos_left (by linarith) hσ (by linarith)⟩

/-- AKMM, p. 392: **decentralised growth is too low**. If `0 < φ < 1`, `σ > 0` and `ηL > ρ`,
`g^{DE} = ((1−φ)ηL − ρ)/(1 − φ + σ) < g^{SP} = (ηL − ρ)/σ`. -/
theorem romer_planner_growth_gt {φ η σ ρ L : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hσ : 0 < σ)
    (hη : 0 < η) (hL : 0 < L) (hpos : ρ < η * L) :
    ((1 - φ) * η * L - ρ) / (1 - φ + σ) < (η * L - ρ) / σ := by
  have h : 0 < 1 - φ + σ := by linarith
  rw [div_lt_div_iff₀ h hσ]
  have : 0 < (1 - φ) * (η * L - ρ) + σ * φ * η * L := by
    have : 0 < η * L - ρ := by linarith
    positivity
  nlinarith

end AKMM.Growth
