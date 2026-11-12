/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Oligopoly and endogenous markups: Atkeson–Burstein (AKMM §22.6.2, App. 22.A.4)

AKMM, §22.6.2, pp. 679–681, and Appendix 22.A.4, pp. 892–893. Sector `i` has `J` brands combined
by the CES aggregator (22.23) with elasticity `η > σ > 1`; the sector good enters (22.16).

* **The nested CES (22.24)–(22.25)**: with brand prices `p̂ⱼ = p qⱼ^{−1/η}y^{1/η}`, the sector
  price is the CES index of the brand prices and `Σ p̂ⱼqⱼ = py` (`eq_22_24`, `eq_22_25`); the sales
  share is `sⱼ = qⱼ^{(η−1)/η}/Σₖ qₖ^{(η−1)/η}` (`eq_22_29`).
* **Cournot (22.27)–(22.28)**: the derivative of the brand's revenue with respect to its own
  quantity, taking `Y` but not the sector output as given, is `p̂(1 − 1/ε(s))` with
  `ε(s) = ((1−s)/η + s/σ)^{−1}` (`eq_22_28`), so marginal revenue equal to marginal cost gives
  the markup `p̂ = ε/(ε−1)·MC` (`eq_22_27`).
* **Properties of `ε`**: `ε(0) = η`, `ε(1) = σ`, `ε` strictly decreasing on `[0, 1]` with values
  in `[σ, η]` (`cournot_endpoints`, `cournot_strictAntiOn`, `cournot_mem_Icc`); with `J` symmetric
  firms `ε = ((J−1)/(ηJ) + 1/(σJ))^{−1}` (`cournot_symmetric`), equal to `σ` for `J = 1`, rising in
  `J` (`cournot_symmetric_mono`) and tending to `η` (`cournot_symmetric_tendsto`); markups fall
  with `ε` (`markup_strictAnti`).
* **Bertrand (App. 22.A.4)**: the brand's demand `q = p̂^{−η}p^{η−σ}Y` has elasticity
  `ε(s) = η(1−s) + σs` (`bertrand_demand_deriv`, `eq_22_A_4`), giving the same pricing rule
  (`bertrand_markup`). Printed signs corrected: `(q/p̂)/(∂q/∂p̂) = −1/ε` and the first-order
  condition is `(1 + (q/p̂)/(∂q/∂p̂))p̂ = MC` (`bertrand_ratio`).
* **Cournot markups exceed Bertrand markups** (`cournot_le_bertrand`, `markup_cournot_ge`).
-/

open Filter Topology

namespace AKMM.HeterogeneousFirms

/-! ### The nested CES -/

/-- AKMM, (22.23), p. 680: sector output `y = (Σⱼ qⱼ^{(η−1)/η})^{η/(η−1)}`. -/
noncomputable def sectorOutput {J : Type*} [Fintype J] (η : ℝ) (q : J → ℝ) : ℝ :=
  (∑ j, q j ^ ((η - 1) / η)) ^ (η / (η - 1))

theorem sectorOutput_rpow {J : Type*} [Fintype J] {η : ℝ} (hη : 1 < η) {q : J → ℝ}
    (hq : ∀ j, 0 < q j) [Nonempty J] :
    sectorOutput η q ^ ((η - 1) / η) = ∑ j, q j ^ ((η - 1) / η) := by
  have hS : 0 < ∑ j, q j ^ ((η - 1) / η) :=
    Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _) Finset.univ_nonempty
  unfold sectorOutput
  rw [← Real.rpow_mul hS.le, show η / (η - 1) * ((η - 1) / η) = 1 by
    have : η - 1 ≠ 0 := by linarith
    have : η ≠ 0 := by linarith
    field_simp, Real.rpow_one]

/-- AKMM, (22.24)–(22.25), p. 680: with brand prices `p̂ⱼ = p qⱼ^{−1/η}y^{1/η}` (the within-sector
cost-minimisation condition (22.24)), total spending is `Σ p̂ⱼqⱼ = py` (22.25). -/
theorem eq_22_25 {J : Type*} [Fintype J] [Nonempty J] {η p : ℝ} (hη : 1 < η) {q : J → ℝ}
    (hq : ∀ j, 0 < q j) :
    ∑ j, p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j = p * sectorOutput η q := by
  have hη0 : η ≠ 0 := by linarith
  have hy : 0 < sectorOutput η q := by
    unfold sectorOutput
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _)
      Finset.univ_nonempty) _
  have e : ∀ j, p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j =
      p * sectorOutput η q ^ (1 / η) * q j ^ ((η - 1) / η) := fun j => by
    rw [show q j ^ ((η - 1) / η) = q j ^ (-1 / η) * q j by
      rw [← Real.rpow_add_one (hq j).ne']; congr 1; field_simp; ring]
    ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, ← sectorOutput_rpow hη hq,
    mul_assoc, ← Real.rpow_add hy]
  rw [show 1 / η + (η - 1) / η = 1 by field_simp; ring, Real.rpow_one]

/-- AKMM, p. 680, after (22.24): the sector price is the CES index of the brand prices,
`p = (Σ p̂ⱼ^{1−η})^{1/(1−η)}`. -/
theorem eq_22_24 {J : Type*} [Fintype J] [Nonempty J] {η p : ℝ} (hη : 1 < η) (hp : 0 < p)
    {q : J → ℝ} (hq : ∀ j, 0 < q j) :
    (∑ j, (p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η)) ^ (1 - η)) ^ (1 / (1 - η)) = p := by
  have hη0 : η ≠ 0 := by linarith
  have hη1 : 1 - η ≠ 0 := by linarith
  have hy : 0 < sectorOutput η q := by
    unfold sectorOutput
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _)
      Finset.univ_nonempty) _
  have e : ∀ j, (p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η)) ^ (1 - η) =
      p ^ (1 - η) * sectorOutput η q ^ ((1 - η) / η) * q j ^ ((η - 1) / η) := fun j => by
    have hqj := hq j
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hp.le (by positivity),
      ← Real.rpow_mul hqj.le, ← Real.rpow_mul hy.le]
    rw [show -1 / η * (1 - η) = (η - 1) / η by field_simp; ring,
      show 1 / η * (1 - η) = (1 - η) / η by ring]
    ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, ← sectorOutput_rpow hη hq,
    mul_assoc, ← Real.rpow_add hy, show (1 - η) / η + (η - 1) / η = 0 by ring, Real.rpow_zero,
    mul_one, ← Real.rpow_mul hp.le, mul_one_div_cancel hη1, Real.rpow_one]

/-- AKMM, (22.29), p. 681: the sales share `sⱼ = p̂ⱼqⱼ/(py) = qⱼ^{(η−1)/η}/Σₖ qₖ^{(η−1)/η}`. -/
theorem eq_22_29 {J : Type*} [Fintype J] [Nonempty J] {η p : ℝ} (hη : 1 < η) (hp : 0 < p)
    {q : J → ℝ} (hq : ∀ j, 0 < q j) (j : J) :
    p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j / (p * sectorOutput η q) =
      q j ^ ((η - 1) / η) / ∑ k, q k ^ ((η - 1) / η) := by
  have hη0 : η ≠ 0 := by linarith
  have hy : 0 < sectorOutput η q := by
    unfold sectorOutput
    exact Real.rpow_pos_of_pos (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hq j) _)
      Finset.univ_nonempty) _
  have hqρ : q j ^ (-1 / η) * q j = q j ^ ((η - 1) / η) := by
    rw [← Real.rpow_add_one (hq j).ne']; congr 1; field_simp; ring
  have e1 : p * q j ^ (-1 / η) * sectorOutput η q ^ (1 / η) * q j =
      (p * sectorOutput η q ^ (1 / η)) * q j ^ ((η - 1) / η) := by rw [← hqρ]; ring
  have e2 : p * sectorOutput η q =
      (p * sectorOutput η q ^ (1 / η)) * sectorOutput η q ^ ((η - 1) / η) := by
    rw [mul_assoc, ← Real.rpow_add hy, show 1 / η + (η - 1) / η = 1 by field_simp; ring,
      Real.rpow_one]
  have hne : p * sectorOutput η q ^ (1 / η) ≠ 0 := by positivity
  rw [e1, e2, mul_div_mul_left _ _ hne, sectorOutput_rpow hη hq]

/-! ### Cournot -/

/-- AKMM, (22.28), p. 681: the Cournot demand elasticity `ε(s) = ((1−s)/η + s/σ)^{−1}`. -/
noncomputable def cournotElas (σ η s : ℝ) : ℝ := ((1 - s) / η + s / σ)⁻¹

/-- AKMM, App. 22.A.4, p. 893: the Bertrand demand elasticity `ε(s) = η(1−s) + σs`. -/
def bertrandElas (σ η s : ℝ) : ℝ := η * (1 - s) + σ * s

/-- AKMM, (22.28), p. 681: **the Cournot marginal revenue**. Let the other brands contribute
`C ≥ 0` to `Σ qₖ^ρ`, `ρ = (η−1)/η`, so `y(q) = (C + q^ρ)^{1/ρ}`; the revenue
`p̂q = q^ρ(C + q^ρ)^{(1/η−1/σ)/ρ}Y^{1/σ}` (from (22.18), (22.24)) has derivative `p̂(1 − 1/ε(s))`
at `q > 0`, with `p̂ = q^{ρ−1}(C + q^ρ)^{(1/η−1/σ)/ρ}Y^{1/σ}` and the sales share
`s = q^ρ/(C + q^ρ)`. -/
theorem eq_22_28 {σ η C Z q : ℝ} (hσ : 1 < σ) (hη : 1 < η) (hC : 0 ≤ C) (hq : 0 < q) :
    HasDerivAt
      (fun x => Z * x ^ ((η - 1) / η) * (C + x ^ ((η - 1) / η)) ^ ((1 / η - 1 / σ) /
        ((η - 1) / η)))
      (Z * q ^ ((η - 1) / η - 1) * (C + q ^ ((η - 1) / η)) ^ ((1 / η - 1 / σ) / ((η - 1) / η)) *
        (1 - 1 / cournotElas σ η (q ^ ((η - 1) / η) / (C + q ^ ((η - 1) / η))))) q := by
  set ρ := (η - 1) / η with hρ
  set κ := (1 / η - 1 / σ) / ρ with hκ
  have hη0 : η ≠ 0 := by linarith
  have hσ0 : σ ≠ 0 := by linarith
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact div_ne_zero (by linarith) hη0
  have hqρ : 0 < q ^ ρ := Real.rpow_pos_of_pos hq ρ
  have hg : 0 < C + q ^ ρ := by linarith
  have h1 : HasDerivAt (fun x => x ^ ρ) (ρ * q ^ (ρ - 1)) q :=
    Real.hasDerivAt_rpow_const (Or.inl hq.ne')
  have h3 : HasDerivAt (fun x => (C + x ^ ρ) ^ κ)
      (ρ * q ^ (ρ - 1) * κ * (C + q ^ ρ) ^ (κ - 1)) q :=
    (h1.const_add C).rpow_const (Or.inl hg.ne')
  have h := (h1.mul h3).const_mul Z
  convert h using 1
  · funext x; simp only [Pi.mul_apply]; ring
  · rw [cournotElas, one_div, inv_inv, Real.rpow_sub_one hg.ne']
    have hρκ : ρ * κ = 1 / η - 1 / σ := by rw [hκ]; field_simp
    have hρ' : ρ = 1 - 1 / η := by rw [hρ]; field_simp
    linear_combination (-(Z * q ^ (ρ - 1) * (C + q ^ ρ) ^ κ)) * hρ' +
      (-(Z * q ^ (ρ - 1) * (C + q ^ ρ) ^ κ * (q ^ ρ / (C + q ^ ρ)))) * hρκ

/-- AKMM, (22.27), p. 680: **Cournot pricing**. If marginal revenue `p̂(1 − 1/ε)` equals marginal
cost `MC` and `ε > 1`, then `p̂ = ε/(ε−1)·MC`. -/
theorem eq_22_27 {ε ph MC : ℝ} (hε : 1 < ε) (h : ph * (1 - 1 / ε) = MC) :
    ph = ε / (ε - 1) * MC := by
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [← h]; field_simp

/-- AKMM, p. 681: `ε(0) = η` and `ε(1) = σ`. -/
theorem cournot_endpoints (σ η : ℝ) : cournotElas σ η 0 = η ∧ cournotElas σ η 1 = σ := by
  unfold cournotElas; simp

/-- AKMM, p. 681: for `1 < σ < η`, `ε(s)` **decreases strictly** on `[0, 1]`. -/
theorem cournot_strictAntiOn {σ η : ℝ} (hσ : 1 < σ) (hση : σ < η) :
    StrictAntiOn (cournotElas σ η) (Set.Icc 0 1) := by
  intro s hs t ht hst
  unfold cournotElas
  have hη : 0 < η := by linarith
  have hσ0 : 0 < σ := by linarith
  have hd : 1 / η < 1 / σ := one_div_lt_one_div_of_lt hσ0 hση
  have hps : 0 < (1 - s) / η + s / σ := by
    have h1 : 0 ≤ (1 - s) / η := div_nonneg (by linarith [hs.2]) hη.le
    have h2 : 0 ≤ s / σ := div_nonneg hs.1 hσ0.le
    rcases hs.1.lt_or_eq with h | h
    · have : 0 < s / σ := div_pos h hσ0; linarith
    · subst h; simp only [sub_zero, one_div, zero_div, add_zero, inv_pos, gt_iff_lt]; exact hη
  apply inv_strictAnti₀ hps
  have : (1 - s) / η + s / σ = 1 / η + s * (1 / σ - 1 / η) := by ring
  have : (1 - t) / η + t / σ = 1 / η + t * (1 / σ - 1 / η) := by ring
  nlinarith

/-- AKMM, p. 681: for `s ∈ [0, 1]` and `1 < σ < η`, `σ ≤ ε(s) ≤ η`. -/
theorem cournot_mem_Icc {σ η s : ℝ} (hσ : 1 < σ) (hση : σ < η) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    cournotElas σ η s ∈ Set.Icc σ η := by
  have hA := cournot_strictAntiOn hσ hση
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨e0, e1⟩ := cournot_endpoints σ η
  constructor
  · calc σ = cournotElas σ η 1 := e1.symm
      _ ≤ cournotElas σ η s := hA.antitoneOn hs h1 hs.2
  · calc cournotElas σ η s ≤ cournotElas σ η 0 := hA.antitoneOn h0 hs hs.1
      _ = η := e0

/-- AKMM, p. 681: **symmetric firms**: with `s = 1/J`,
`ε = ((1/η)(J−1)/J + 1/(σJ))^{−1}`. -/
theorem cournot_symmetric (σ η : ℝ) {J : ℝ} (hJ : J ≠ 0) :
    cournotElas σ η (1 / J) = (1 / η * ((J - 1) / J) + 1 / (σ * J))⁻¹ := by
  unfold cournotElas
  congr 1
  field_simp

/-- AKMM, p. 681: one firm per sector (`J = 1`) is monopolistic competition, `ε = σ`. -/
theorem cournot_symmetric_one (σ η : ℝ) : cournotElas σ η (1 / 1) = σ := by
  rw [div_one]; exact (cournot_endpoints σ η).2

/-- AKMM, p. 681: **the markup falls as the number of firms rises**: `ε(1/J)` is strictly
increasing in `J ≥ 1`. -/
theorem cournot_symmetric_mono {σ η : ℝ} (hσ : 1 < σ) (hση : σ < η) {J J' : ℕ} (hJ : 1 ≤ J)
    (hJJ : J < J') : cournotElas σ η (1 / (J : ℝ)) < cournotElas σ η (1 / (J' : ℝ)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ'0 : (0 : ℝ) < J' := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hJ).trans hJJ
  have hJJ' : (J : ℝ) < J' := by exact_mod_cast hJJ
  apply cournot_strictAntiOn hσ hση
  · have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    exact ⟨div_nonneg zero_le_one hJ'0.le, (div_le_one hJ'0).mpr (by linarith)⟩
  · have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    exact ⟨div_nonneg zero_le_one hJ0.le, (div_le_one hJ0).mpr h1⟩
  · exact one_div_lt_one_div_of_lt hJ0 hJJ'

/-- AKMM, p. 681: **`ε(1/J) → η` as `J → ∞`**. -/
theorem cournot_symmetric_tendsto {σ η : ℝ} (hη : 0 < η) :
    Tendsto (fun J : ℕ => cournotElas σ η (1 / (J : ℝ))) atTop (𝓝 η) := by
  have h : Tendsto (fun J : ℕ => (1 / (J : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hc : ContinuousAt (cournotElas σ η) 0 := by
    unfold cournotElas
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    simp only [sub_zero, one_div, zero_div, add_zero, ne_eq, inv_eq_zero]; exact hη.ne'
  have := hc.tendsto.comp h
  rwa [(cournot_endpoints σ η).1] at this

/-- AKMM, p. 681: the markup `ε/(ε−1)` is strictly decreasing in `ε > 1`. -/
theorem markup_strictAnti : StrictAntiOn (fun ε : ℝ => ε / (ε - 1)) (Set.Ioi 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < y - 1 := by linarith
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

/-! ### Bertrand -/

/-- AKMM, App. 22.A.4, pp. 892–893: **the Bertrand demand curve**. With the other brands'
`D = Σ_{k≠j} p̂ₖ^{1−η} ≥ 0`, sector price `p = (D + p̂^{1−η})^{1/(1−η)}` (22.A.4) and sector demand
`y = p^{−σ}Y` (22.A.3), the brand demand `q = (p̂/p)^{−η}y` from (22.A.2) is
`p̂^{−η}(D + p̂^{1−η})^{(η−σ)/(1−η)}Y`. -/
theorem bertrand_demand_form {σ η D Y ph : ℝ} (hη : 1 < η) (hD : 0 ≤ D) (hph : 0 < ph) :
    (ph / (D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η) *
        (((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) * Y) =
      ph ^ (-η) * (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η)) * Y := by
  have hG : 0 < D + ph ^ (1 - η) := by have := Real.rpow_pos_of_pos hph (1 - η); linarith
  have hp : 0 < (D + ph ^ (1 - η)) ^ (1 / (1 - η)) := Real.rpow_pos_of_pos hG _
  have h1η : 1 - η ≠ 0 := by linarith
  have e : ((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) /
      ((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η) = (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η)) := by
    rw [← Real.rpow_sub hp, ← Real.rpow_mul hG.le]; congr 1; field_simp; ring
  calc (ph / (D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η) *
        (((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) * Y)
      = ph ^ (-η) * (((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-σ) /
          ((D + ph ^ (1 - η)) ^ (1 / (1 - η))) ^ (-η)) * Y := by
        rw [Real.div_rpow hph.le hp.le]; ring
    _ = _ := by rw [e]

/-- AKMM, App. 22.A.4, p. 893: **the Bertrand demand slope**. The derivative of
`q(p̂) = p̂^{−η}(D + p̂^{1−η})^{(η−σ)/(1−η)}Y` is `−ε(s)q/p̂` with `ε(s) = η(1−s) + σs` and
`s = p̂^{1−η}/(D + p̂^{1−η})` the sales share. -/
theorem bertrand_demand_deriv {σ η D Y ph : ℝ} (hη : 1 < η) (hD : 0 ≤ D) (hph : 0 < ph) :
    HasDerivAt (fun x => x ^ (-η) * (D + x ^ (1 - η)) ^ ((η - σ) / (1 - η)) * Y)
      (-bertrandElas σ η (ph ^ (1 - η) / (D + ph ^ (1 - η))) *
        (ph ^ (-η) * (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η)) * Y) / ph) ph := by
  have h1η : 1 - η ≠ 0 := by linarith
  have hpp : 0 < ph ^ (1 - η) := Real.rpow_pos_of_pos hph _
  have hG : 0 < D + ph ^ (1 - η) := by linarith
  have ha : HasDerivAt (fun x => x ^ (-η)) (-η * ph ^ (-η - 1)) ph :=
    Real.hasDerivAt_rpow_const (Or.inl hph.ne')
  have hb : HasDerivAt (fun x => x ^ (1 - η)) ((1 - η) * ph ^ (1 - η - 1)) ph :=
    Real.hasDerivAt_rpow_const (Or.inl hph.ne')
  have hc : HasDerivAt (fun x => (D + x ^ (1 - η)) ^ ((η - σ) / (1 - η)))
      ((1 - η) * ph ^ (1 - η - 1) * ((η - σ) / (1 - η)) *
        (D + ph ^ (1 - η)) ^ ((η - σ) / (1 - η) - 1)) ph :=
    (hb.const_add D).rpow_const (Or.inl hG.ne')
  have h := (ha.mul hc).mul_const Y
  convert h using 1
  rw [bertrandElas, Real.rpow_sub_one hG.ne', Real.rpow_sub_one hph.ne',
    Real.rpow_sub_one hph.ne']
  have e : ph ^ (1 - η) = ph * ph ^ (-η) := by
    rw [show (1 - η) = -η + 1 by ring, Real.rpow_add_one hph.ne']; ring
  rw [e] at hG ⊢
  have : 0 < ph ^ (-η) := Real.rpow_pos_of_pos hph _
  field_simp
  ring

/-- AKMM, App. 22.A.4, p. 893, corrected: with `q' = −εq/p̂`, `(q/p̂)/q' = −1/ε` (printed `1/ε`). -/
theorem bertrand_ratio {ε q ph : ℝ} (hε : ε ≠ 0) (hq : q ≠ 0) (hph : ph ≠ 0) :
    (q / ph) / (-ε * q / ph) = -(1 / ε) := by
  field_simp

/-- AKMM, App. 22.A.4, p. 893: the printed `(q/p̂)/(∂q/∂p̂) = 1/ε` is false for every `ε ≠ 0`. -/
theorem bertrand_ratio_printed_false {ε q ph : ℝ} (hε : ε ≠ 0) (hq : q ≠ 0) (hph : ph ≠ 0) :
    (q / ph) / (-ε * q / ph) ≠ 1 / ε := by
  rw [bertrand_ratio hε hq hph]
  intro h
  have : 1 / ε = 0 := by linarith
  exact hε (by simpa using this)

/-- AKMM, App. 22.A.4, p. 893: **Bertrand pricing**. The first-order condition
`p̂q' + q = MC·q'` with `q' = −εq/p̂`, `q > 0`, `ε > 1` gives `p̂ = ε/(ε−1)·MC`; equivalently the
corrected `(1 + (q/p̂)/q')p̂ = MC`. -/
theorem bertrand_markup {ε q ph MC : ℝ} (hε : 1 < ε) (hq : 0 < q) (hph : 0 < ph)
    (hfoc : ph * (-ε * q / ph) + q = MC * (-ε * q / ph)) :
    ph = ε / (ε - 1) * MC ∧ (1 + (q / ph) / (-ε * q / ph)) * ph = MC := by
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hMC : MC = ph * (1 - 1 / ε) := by
    field_simp at hfoc ⊢
    nlinarith
  refine ⟨by rw [hMC]; field_simp, ?_⟩
  rw [bertrand_ratio hε0 hq.ne' hph.ne', hMC]; ring

/-- AKMM, App. 22.A.4: `ε(0) = η`, `ε(1) = σ` for Bertrand too, and `ε` decreases in `s` when
`σ < η`. -/
theorem eq_22_A_4 {σ η : ℝ} (hση : σ < η) :
    bertrandElas σ η 0 = η ∧ bertrandElas σ η 1 = σ ∧ StrictAnti (bertrandElas σ η) := by
  refine ⟨by simp [bertrandElas], by simp [bertrandElas], fun s t hst => ?_⟩
  unfold bertrandElas; nlinarith

/-- AKMM, p. 681: **the Cournot elasticity is below the Bertrand elasticity** (harmonic versus
arithmetic mean of `η` and `σ`) for `s ∈ [0, 1]`. -/
theorem cournot_le_bertrand {σ η s : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    cournotElas σ η s ≤ bertrandElas σ η s := by
  unfold cournotElas bertrandElas
  obtain ⟨h0, h1⟩ := hs
  have hps : 0 < (1 - s) / η + s / σ := by
    rcases h0.lt_or_eq with h | h
    · have : 0 < s / σ := div_pos h hσ
      have : 0 ≤ (1 - s) / η := div_nonneg (by linarith) hη.le
      linarith
    · subst h; simp only [sub_zero, one_div, zero_div, add_zero, inv_pos]; exact hη
  rw [inv_le_iff_one_le_mul₀' hps]
  have key : (η * (1 - s) + σ * s) * ((1 - s) / η + s / σ) - 1 =
      s * (1 - s) * (η - σ) ^ 2 / (η * σ) := by
    field_simp; ring
  have : 0 ≤ s * (1 - s) * (η - σ) ^ 2 / (η * σ) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)
  linarith

/-- AKMM, p. 681: **Cournot markups are at least Bertrand markups**. -/
theorem markup_cournot_ge {σ η s : ℝ} (hσ : 1 < σ) (hση : σ < η) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    bertrandElas σ η s / (bertrandElas σ η s - 1) ≤
      cournotElas σ η s / (cournotElas σ η s - 1) := by
  have hc := cournot_mem_Icc hσ hση hs
  have hle := cournot_le_bertrand (σ := σ) (η := η) (by linarith) (by linarith) hs
  have hc1 : 1 < cournotElas σ η s := by linarith [hc.1]
  rcases hle.lt_or_eq with h | h
  · exact (markup_strictAnti (Set.mem_Ioi.mpr hc1)
      (Set.mem_Ioi.mpr (show 1 < bertrandElas σ η s by linarith)) h).le
  · rw [h]

end AKMM.HeterogeneousFirms
