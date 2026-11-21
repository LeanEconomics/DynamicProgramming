/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.BWExamples
import IncompleteMarkets.AYExistence
import IncompleteMarkets.AYIncomeFluct
import AKMMConsumption.Deterministic

/-!
# The endowment economy: Huggett and Bewley

AKMM, §11.4.1, (11.47)–(11.50), pp. 315–320.

The household problem (11.47), the transition (11.48)–(11.49) and stationarity are Miao's
(`Miao.IncompleteMarkets`): `BWEconomy.Bellman r φ y V g` (the Bellman equation with rate `r`,
debt limit `φ = a`, endowment `y`, maximum attained by `g`), `BWEconomy.Stationary g λ` (the fixed
point of (11.49) on measurable rectangles), `BWHuggettEqm` (Definition 17.2.1) and
`definition_17_2_1` (`r` is an equilibrium rate iff `0 ∈ Ea(r)`).

* **The stationary equilibrium** (p. 316) with bond supply `B` and lump-sum tax `T`
  (`hg_IsStationaryEqm`): `B = T = 0` is Huggett's definition, `B > 0` with (11.50) is Bewley's.
  Stationarity makes mean assets equal mean saving (`hg_mean_assets_eq_mean_policy`), so mean
  consumption is `∫y + rB − T` (`hg_mean_consumption`): with zero net supply the goods market
  clears automatically (`hg_goods_clear_zero_supply`, so AKMM's definition is Miao's
  Definition 17.2.1, `hg_eqm_iff_miao`), and with positive supply it clears iff **(11.50)**
  `rB = T` (`eq_11_50`). Concrete equilibria: Miao's cycle economy (`hg_cycle_eqm`,
  `hg_cycle_huggett`).
* **Existence** (p. 318): at `r = −1` every household borrows to the limit, so `A(−1) = −a`
  (`hg_policy_at_minus_one`, `hg_A_at_minus_one`); continuity of `A`, `A(r) → ∞` as `r ↑ 1/β − 1`
  and `−a < B` give an equilibrium rate in `(−1, 1/β − 1)` (`hg_existence`, by Miao's crossing
  argument), for zero supply a stationary equilibrium (`hg_existence_eqm`).
* **`r* < 1/β − 1`** (p. 318): every stationary distribution of the income fluctuation problem
  with nondegenerate income has `βR < 1` (Miao's `ay_beta_R_lt_one`, `ay_r_lt_rho`;
  `hg_rate_below_cm`).
* **Uniqueness** (p. 318): a strictly increasing `A` crosses `B` once (`hg_unique_of_strictMono`).
  **Correction:** "the smaller is `σ` the larger is the income effect" — in the two-period CRRA
  problem saving rises with `R` iff `σ < 1`, where the *substitution* effect dominates
  (`hg_saving_ratio_crra`, `hg_saving_increasing_iff`).

Departures: `A(r)` is a function given as a hypothesis (the book asserts its continuity, by SLP
Theorems 12.12–12.13, and the limit at `1/β − 1`); Miao's `EaSet` handles a possibly
set-valued `A`. The ACHLLM uniqueness theorem (continuous time, `σ < 1`) is not formalised.
-/

namespace AKMM.Consumption

open MeasureTheory Filter Topology ProbabilityTheory Miao.IncompleteMarkets

variable {E : Type*} [MeasurableSpace E]

/-! ### The stationary equilibrium -/

/-- **AKMM, p. 316 (zero supply) and pp. 319–320 (positive supply).** A recursive stationary
competitive equilibrium of the endowment economy with debt limit `φ`, bond supply `B` and lump-sum
tax `T`: `V, g` solve (11.47) with income `y − T`, `λ` is a stationary probability measure on
`[−φ, ∞) × E`, the asset market clears, `∫g dλ = B`, and the goods market clears,
`∫c dλ = ∫y dλ` with `c = (1 + r)a + y − T − g`. -/
def hg_IsStationaryEqm (H : BWEconomy E) (φ B T r : ℝ) (V g : ℝ → E → ℝ)
    (lam : Measure (ℝ × E)) : Prop :=
  IsProbabilityMeasure lam ∧ lam {p | p.1 < -φ} = 0 ∧
    H.Bellman r φ (fun s => H.e s - T) V g ∧ H.Stationary g lam ∧
    Integrable (fun p => g p.1 p.2) lam ∧ ∫ p, g p.1 p.2 ∂lam = B ∧
    ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam

/-- AKMM, p. 317: stationarity (11.49) with a Markov kernel makes the asset marginal of `λ` the
image of `λ` under the policy: `λ(A × E) = λ{g ∈ A}`. -/
theorem hg_map_fst_eq (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} (hst : H.Stationary g lam)
    (hgm : AEMeasurable (fun p : ℝ × E => g p.1 p.2) lam) :
    lam.map Prod.fst = lam.map (fun p => g p.1 p.2) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, Measure.map_apply_of_aemeasurable hgm hA]
  have h := hst A Set.univ hA MeasurableSet.univ
  simp only [measure_univ, mul_one] at h
  rw [show Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set E) by ext; simp, h]
  have : (fun p : ℝ × E => A.indicator (1 : ℝ → ENNReal) (g p.1 p.2)) =
      ((fun p : ℝ × E => g p.1 p.2) ⁻¹' A).indicator 1 := by
    ext p; simp only [Set.indicator, Pi.one_apply]; rfl
  rw [this, lintegral_indicator_one₀ (hgm.nullMeasurableSet_preimage hA)]

/-- Under a stationary distribution, assets are integrable when saving is. -/
theorem hg_integrable_assets (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) : Integrable (fun p : ℝ × E => p.1) lam := by
  have hi : Integrable (fun x : ℝ => x) (lam.map fun p => g p.1 p.2) :=
    (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).2 hg
  rw [← hg_map_fst_eq H hst hg.aemeasurable] at hi
  exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 hi

/-- AKMM, p. 317: under a stationary distribution, mean assets equal mean saving,
`∫a dλ = ∫g dλ`. -/
theorem hg_mean_assets_eq_mean_policy (H : BWEconomy E) [IsMarkovKernel H.Q]
    {g : ℝ → E → ℝ} {lam : Measure (ℝ × E)} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) :
    ∫ p, p.1 ∂lam = ∫ p, g p.1 p.2 ∂lam := by
  have h1 : ∫ p, p.1 ∂lam = ∫ x, x ∂(lam.map Prod.fst) :=
    (integral_map measurable_fst.aemeasurable aestronglyMeasurable_id).symm
  have h2 : ∫ p, g p.1 p.2 ∂lam = ∫ x, x ∂(lam.map fun p => g p.1 p.2) :=
    (integral_map hg.aemeasurable aestronglyMeasurable_id).symm
  rw [h1, h2, hg_map_fst_eq H hst hg.aemeasurable]

/-- AKMM, pp. 316 and 319: mean consumption in a stationary distribution. With mean saving `B`,
`∫[(1 + r)a + y − T − g] dλ = ∫y dλ + rB − T`. -/
theorem hg_mean_consumption (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {r T B : ℝ} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) (ha : Integrable (fun p : ℝ × E => p.1) lam)
    (he : Integrable (fun p : ℝ × E => H.e p.2) lam) (hB : ∫ p, g p.1 p.2 ∂lam = B) :
    ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam + r * B - T := by
  have hma := hg_mean_assets_eq_mean_policy H hst hg
  have i1 : Integrable (fun p : ℝ × E => (1 + r) * p.1 + H.e p.2) lam := (ha.const_mul _).add he
  have i2 : Integrable (fun p : ℝ × E => (1 + r) * p.1 + H.e p.2 - T) lam :=
    i1.sub (integrable_const T)
  have e1 : ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam =
      ∫ p, ((1 + r) * p.1 + H.e p.2 - T) ∂lam - ∫ p, g p.1 p.2 ∂lam := integral_sub i2 hg
  have e2 : ∫ p, ((1 + r) * p.1 + H.e p.2 - T) ∂lam =
      ∫ p, ((1 + r) * p.1 + H.e p.2) ∂lam - T := by
    rw [integral_sub i1 (integrable_const T), integral_const]; simp
  have e3 : ∫ p, ((1 + r) * p.1 + H.e p.2) ∂lam = (1 + r) * ∫ p, p.1 ∂lam + ∫ p, H.e p.2 ∂lam := by
    rw [integral_add (ha.const_mul _) he, integral_const_mul]
  rw [e1, e2, e3, hma, hB]
  ring

/-- **AKMM, p. 316: with zero net supply the goods market clears.** If the asset market clears,
`∫g dλ = 0`, and `T = 0`, then mean consumption equals the mean endowment. -/
theorem hg_goods_clear_zero_supply (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {r : ℝ} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) (ha : Integrable (fun p : ℝ × E => p.1) lam)
    (he : Integrable (fun p : ℝ × E => H.e p.2) lam) (hclear : ∫ p, g p.1 p.2 ∂lam = 0) :
    ∫ p, ((1 + r) * p.1 + H.e p.2 - 0 - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam := by
  rw [hg_mean_consumption H hst hg ha he hclear]
  ring

/-- **AKMM, p. 316 and Miao's Definition 17.2.1.** With zero supply and no taxes, AKMM's
stationary equilibrium is Miao's (`BWHuggettEqm`): the goods-market condition is implied
(given integrable assets and endowments under `λ`). -/
theorem hg_eqm_iff_miao (H : BWEconomy E) [IsMarkovKernel H.Q] (φ r : ℝ) (V g : ℝ → E → ℝ)
    (lam : Measure (ℝ × E)) [IsProbabilityMeasure lam]
    (ha : Integrable (fun p : ℝ × E => p.1) lam) (he : Integrable (fun p : ℝ × E => H.e p.2) lam) :
    hg_IsStationaryEqm H φ 0 0 r V g lam ↔
      lam {p | p.1 < -φ} = 0 ∧ H.Bellman r φ H.e V g ∧ H.Stationary g lam ∧
        Integrable (fun p => g p.1 p.2) lam ∧ ∫ p, g p.1 p.2 ∂lam = 0 := by
  have hy : (fun s => H.e s - 0) = H.e := by funext s; ring
  unfold hg_IsStationaryEqm
  rw [hy]
  constructor
  · rintro ⟨-, h1, h2, h3, h4, h5, -⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨inferInstance, h1, h2, h3, h4, h5, hg_goods_clear_zero_supply H h3 h4 ha he h5⟩

/-- **AKMM, (11.50), p. 319: assets in positive supply.** In a stationary distribution with
`∫g dλ = B`, the goods market clears iff the government budget `rB = T` holds. -/
theorem eq_11_50 (H : BWEconomy E) [IsMarkovKernel H.Q] {g : ℝ → E → ℝ}
    {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {r T B : ℝ} (hst : H.Stationary g lam)
    (hg : Integrable (fun p => g p.1 p.2) lam) (ha : Integrable (fun p : ℝ × E => p.1) lam)
    (he : Integrable (fun p : ℝ × E => H.e p.2) lam) (hB : ∫ p, g p.1 p.2 ∂lam = B) :
    ∫ p, ((1 + r) * p.1 + H.e p.2 - T - g p.1 p.2) ∂lam = ∫ p, H.e p.2 ∂lam ↔ r * B = T := by
  rw [hg_mean_consumption H hst hg ha he hB]
  constructor <;> intro h <;> linarith

/-- Miao's cycle economy has a Markov (deterministic) transition kernel. -/
theorem hg_cycle_markov : IsMarkovKernel bw_cycle.Q := by
  change IsMarkovKernel (Kernel.deterministic (fun s : Bool => !s) Measurable.of_discrete)
  infer_instance

/-- Integrability against Miao's cycle distribution `½δ_{(0, true)} + ½δ_{(1/2, false)}`. -/
theorem hg_cycle_integrable (f : ℝ × Bool → ℝ) : Integrable f bw_cycleLam :=
  ((integrable_dirac (by simp)).smul_measure (by simp)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))

/-- **The definition is not vacuous (positive supply).** Miao's cycle economy at `r = 0`, with no
borrowing, bond supply `B = 1/4` and `T = rB = 0`, is a stationary equilibrium. -/
theorem hg_cycle_eqm :
    hg_IsStationaryEqm bw_cycle 0 (1 / 4) 0 0 bw_cycleV bw_cycleG bw_cycleLam := by
  have hP := bw_cycleLam_isProb
  have := hg_cycle_markov
  have hy : (fun s => bw_cycle.e s - 0) = bw_cycle.e := by funext s; ring
  refine ⟨hP, bw_cycleLam_supp, by rw [hy]; exact bw_cycle_bellman, bw_cycle_stationary,
    bw_cycle_integrable, bw_cycle_mean, ?_⟩
  exact (eq_11_50 bw_cycle bw_cycle_stationary bw_cycle_integrable (hg_cycle_integrable _)
    (hg_cycle_integrable _) bw_cycle_mean).2 (by ring)

/-- **The definition is not vacuous (zero supply).** The cycle economy with debt limit `1/4` has a
Huggett stationary equilibrium in AKMM's sense (Miao's `bw_cycle_huggett`). -/
theorem hg_cycle_huggett : ∃ (V g : ℝ → Bool → ℝ) (lam : Measure (ℝ × Bool)),
    hg_IsStationaryEqm bw_cycle (1 / 4) 0 0 0 V g lam := by
  obtain ⟨eqm, hr⟩ := bw_cycle_huggett
  have hP := eqm.isProb
  have := hg_cycle_markov
  refine ⟨eqm.V, eqm.g, eqm.lam, ?_⟩
  have ha := hg_integrable_assets bw_cycle eqm.stationary eqm.integrable
  have he : Integrable (fun p : ℝ × Bool => bw_cycle.e p.2) eqm.lam := by
    refine Integrable.of_bound (C := 2) ?_ (Eventually.of_forall fun p => ?_)
    · exact (Measurable.of_discrete.comp measurable_snd).aestronglyMeasurable
    · simp only [bw_cycle]
      split_ifs <;> norm_num
  have := (hg_eqm_iff_miao bw_cycle (1 / 4) eqm.r eqm.V eqm.g eqm.lam ha he).2
    ⟨eqm.supp, eqm.bellman, eqm.stationary, eqm.integrable, eqm.clear⟩
  rwa [hr] at this

/-! ### Existence -/

/-- **AKMM, p. 318: "if `r = −1`, it is optimal to borrow up to the limit since one would never
have to repay".** With `r = −1` and `u` strictly increasing on `[0, ∞)`, every solution of (11.47)
has `g(a, s) = −a` (the debt limit) at every state. -/
theorem hg_policy_at_minus_one (H : BWEconomy E) (hu : StrictMonoOn H.u (Set.Ici 0))
    {φ : ℝ} {y : E → ℝ} {V g : ℝ → E → ℝ} (hB : H.Bellman (-1) φ y V g) :
    ∀ a s, -φ ≤ a → g a s = -φ := by
  have h0 : ∀ x : ℝ, (1 + -1) * x = 0 := fun x => by ring
  -- the value does not depend on assets: the budget does not
  have hV : ∀ x s', -φ ≤ x → V x s' = V (-φ) s' := by
    intro x s' hx
    obtain ⟨hg1, -, he1, hle1⟩ := hB x s' hx
    obtain ⟨hg2, -, he2, hle2⟩ := hB (-φ) s' le_rfl
    rw [h0, zero_add] at hg1 hg2 he1 he2 hle1 hle2
    apply le_antisymm
    · rw [he1]; exact hle2 _ hg1
    · rw [he2]; exact hle1 _ hg2
  intro a s ha
  obtain ⟨hg, -, he, hle⟩ := hB a s ha
  rw [h0, zero_add] at hg he hle
  have hI : ∫ s', V (g a s) s' ∂(H.Q s) = ∫ s', V (-φ) s' ∂(H.Q s) :=
    integral_congr_ae (Eventually.of_forall fun s' => hV _ s' hg.1)
  have hfeas : -φ ∈ Set.Icc (-φ) (y s) := ⟨le_rfl, hg.1.trans hg.2⟩
  have h := hle _ hfeas
  rw [he, hI] at h
  have hu' : H.u (y s - -φ) ≤ H.u (y s - g a s) := by linarith
  have h1 : (0 : ℝ) ≤ y s - -φ := by linarith [hg.1, hg.2]
  have h2 : (0 : ℝ) ≤ y s - g a s := by linarith [hg.2]
  have := (hu.le_iff_le h1 h2).1 hu'
  linarith [hg.1]

/-- **AKMM, p. 318: `A(−1) = −a`.** At `r = −1`, mean saving under any distribution on
`[−φ, ∞) × E` is the debt limit `−φ`. -/
theorem hg_A_at_minus_one (H : BWEconomy E) (hu : StrictMonoOn H.u (Set.Ici 0)) {φ : ℝ}
    {y : E → ℝ} {V g : ℝ → E → ℝ} (hB : H.Bellman (-1) φ y V g) {lam : Measure (ℝ × E)}
    [IsProbabilityMeasure lam] (hsupp : lam {p | p.1 < -φ} = 0) :
    ∫ p, g p.1 p.2 ∂lam = -φ := by
  have hae : ∀ᵐ p ∂lam, -φ ≤ p.1 := by
    rw [ae_iff]
    simpa only [not_le] using hsupp
  have : ∫ p, g p.1 p.2 ∂lam = ∫ _p, -φ ∂lam :=
    integral_congr_ae (hae.mono fun p hp => hg_policy_at_minus_one H hu hB p.1 p.2 hp)
  rw [this, integral_const]
  simp

/-- AKMM, p. 318, in Miao's set-valued form: `Ea(−1) ⊆ {−φ}`. -/
theorem hg_EaSet_at_minus_one (H : BWEconomy E) (hu : StrictMonoOn H.u (Set.Ici 0)) (φ : ℝ)
    (y : E → ℝ) : H.EaSet (-1) φ y ⊆ {-φ} := by
  rintro m ⟨V, g, lam, hP, hsupp, hB, -, -, rfl⟩
  exact hg_A_at_minus_one H hu hB hsupp

/-- **AKMM, p. 318 (Figures 11.6–11.7): existence.** If the aggregate asset demand `A` is
continuous on `[−1, 1/β − 1)`, `A(−1) = −a`, `A(r) → ∞` as `r ↑ 1/β − 1`, and the bond supply
satisfies `−a < B`, then `A(r*) = B` for some `r* ∈ (−1, 1/β − 1)` (Miao's crossing argument). -/
theorem hg_existence {A : ℝ → ℝ} {β φ B : ℝ} (hβ : 0 < β)
    (hA : ContinuousOn A (Set.Ico (-1) (1 / β - 1)))
    (hlim : Tendsto A (𝓝[<] (1 / β - 1)) atTop) (hA1 : A (-1) = -φ) (hB : -φ < B) :
    ∃ r ∈ Set.Ioo (-1) (1 / β - 1), A r = B := by
  have hr0 : (-1 : ℝ) < 1 / β - 1 := by have := one_div_pos.2 hβ; linarith
  exact ay_existence (Kd := fun _ => B) hr0 hA continuousOn_const hlim (by rw [hA1]; exact hB)

/-- **AKMM, p. 318: a Huggett equilibrium exists.** If `A(r) ∈ Ea(r)` (a selection of Miao's
long-run asset holdings) satisfies the hypotheses of `hg_existence` with `a > 0`, there is a
stationary equilibrium (Definition 17.2.1) with rate in `(−1, 1/β − 1)`. -/
theorem hg_existence_eqm (H : BWEconomy E) {A : ℝ → ℝ} {φ : ℝ} (hβ : 0 < H.β) (hφ : 0 < φ)
    (hsel : ∀ r ∈ Set.Ico (-1) (1 / H.β - 1), A r ∈ H.EaSet r φ H.e)
    (hA : ContinuousOn A (Set.Ico (-1) (1 / H.β - 1)))
    (hlim : Tendsto A (𝓝[<] (1 / H.β - 1)) atTop) (hA1 : A (-1) = -φ) :
    ∃ eqm : BWHuggettEqm H φ, eqm.r ∈ Set.Ioo (-1) (1 / H.β - 1) := by
  obtain ⟨r, hr, hAr⟩ := hg_existence hβ hA hlim hA1 (by linarith : -φ < 0)
  have h0 : (0 : ℝ) ∈ H.EaSet r φ H.e := hAr ▸ hsel r ⟨hr.1.le, hr.2⟩
  obtain ⟨eqm, he⟩ := (definition_17_2_1 H φ r).2 h0
  exact ⟨eqm, he ▸ hr⟩

/-- **AKMM, p. 318: "the equilibrium interest rate `r*` will always lie below its complete market
counterpart `1/β − 1`", so `βR* < 1`.** In Miao's income fluctuation problem, every stationary
distribution of cash on hand with nondegenerate income has `βR < 1` and `r < 1/β − 1` (Miao's
`ay_beta_R_lt_one`, `ay_r_lt_rho`, by an Euler-equation variance argument). -/
theorem hg_rate_below_cm {M : SIModel} (S : M.Solution) {lam : Measure ℝ}
    [IsProbabilityMeasure lam] (hst : ay_IsStationaryCoh S lam)
    (hnd : ∀ c : ℝ, M.law {y | y ≠ c} ≠ 0) : M.β * M.R < 1 ∧ M.r < 1 / M.β - 1 :=
  ⟨ay_beta_R_lt_one S hst hnd, ay_r_lt_rho S hst hnd⟩

/-! ### Uniqueness -/

/-- **AKMM, p. 318: "uniqueness is guaranteed if `A(r)` is monotonically increasing".** A strictly
increasing `A` meets the supply `B` at most once. -/
theorem hg_unique_of_strictMono {A : ℝ → ℝ} {S : Set ℝ} (hA : StrictMonoOn A S) {B r r' : ℝ}
    (hr : r ∈ S) (hr' : r' ∈ S) (h : A r = B) (h' : A r' = B) : r = r' :=
  hA.injOn hr hr' (h.trans h'.symm)

/-- AKMM, p. 318: in the two-period CRRA problem with no second-period income, the Euler
equation `(y₀ − a)^{−σ} = βR(Ra)^{−σ}` gives the saving ratio `a/(y₀ − a) = β^{1/σ}R^{1/σ − 1}`. -/
theorem hg_saving_ratio_crra {σ β R y₀ a : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (ha : 0 < a) (hc : 0 < y₀ - a) (h : (y₀ - a) ^ (-σ) = β * R * (R * a) ^ (-σ)) :
    a / (y₀ - a) = β ^ (1 / σ) * R ^ (1 / σ - 1) := by
  have e := eq_11_14 hσ (mul_pos hβ hR) hc (mul_pos hR ha) h
  rw [Real.mul_rpow hβ.le hR.le] at e
  rw [Real.rpow_sub_one hR.ne', ← mul_div_assoc, ← e]
  field_simp

/-- **Correction to AKMM, p. 318** ("the smaller is `σ` the larger is the income effect and a
higher `r` increases savings"). In the two-period CRRA problem the saving ratio
`β^{1/σ}R^{1/σ − 1}` is strictly increasing in `R` iff `σ < 1`: saving rises with the interest
rate when the elasticity of substitution `1/σ` exceeds one, i.e. when the *substitution* effect
dominates. -/
theorem hg_saving_increasing_iff {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    StrictMonoOn (fun R : ℝ => β ^ (1 / σ) * R ^ (1 / σ - 1)) (Set.Ioi 0) ↔ σ < 1 := by
  have hk : 0 < β ^ (1 / σ) := Real.rpow_pos_of_pos hβ _
  constructor
  · intro hmono
    by_contra hge
    push Not at hge
    have hexp : 1 / σ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hσ]; exact hge
    have := hmono (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos) one_lt_two
    simp only [Real.one_rpow, mul_one] at this
    have h2 : (2 : ℝ) ^ (1 / σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two hexp
    nlinarith
  · intro hlt R hR R' _ hRR
    have hexp : 0 < 1 / σ - 1 := by rw [sub_pos, lt_div_iff₀ hσ]; linarith
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hR) hRR hexp) hk

end AKMM.Consumption
