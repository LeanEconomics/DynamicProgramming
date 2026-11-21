/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AAVariational
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# Smooth ambiguity utility

Miao, §20.2.2, pp. 697–701: the static smooth ambiguity model (20.9) of Klibanoff, Marinacci and
Mukerji, the generalized recursive smooth ambiguity model (20.10) of Hayashi–Miao and Ju–Miao,
the homothetic specification (20.11)–(20.15) and its limits (20.16)–(20.18), and the nested models
(Hansen–Sargent multiplier with hidden states; (20.19)).

The hidden state `z` ranges over a finite type `Z`, with prior (posterior) `μ` and likelihoods
`π z` on the finite state space `S`.

* (20.9) and its Bayesian reduction: with affine `v` the model is subjective expected utility
  under the predictive distribution `∑ μ(z)π_z` (`aa_kmm_affine`); with concave `v` the smooth
  ambiguity index is below the Bayesian one (`aa_kmm_concave_le`).
* (20.10): the certainty equivalent `M(x) = v⁻¹(E_μ v(u⁻¹(E_{π_z} u(x))))` (`aa_smoothM`); when
  `v ∘ u⁻¹` is affine, `M(x) = u⁻¹(E u(x))` under the predictive distribution, Epstein–Zin with
  hidden states (`aa_smoothM_linear`). Bayes' rule (`aa_posterior`, `aa_posterior_isDistribution`,
  `aa_posterior_martingale`).
* (20.12)–(20.15): with power `u` and `v`, `M` is (20.15) (`aa_smoothM_power`); the recursion
  (20.14) on the tree (`aa_juU`). For `η = γ` it is Epstein–Zin under the predictive distribution
  (`aa_ju_neutral`, `aa_juU_neutral`); `M` (hence `U`) is decreasing in `η`
  (`aa_ju_antitone`, `aa_W_ju_antitone`), and `η ≥ γ` (`η ≤ γ`) puts it below (above) the
  Epstein–Zin value (`aa_ju_le_KP`, `aa_KP_le_ju`). The power-mean inequality behind these is
  `aa_powMean_mono`.
* (20.16): the limit `ρ → 1` of the CES aggregator is Cobb–Douglas (`aa_W_tendsto_rho_one`), and
  `V = ln U` then satisfies (20.16) (`eq_20_16`). (20.17): the limit `γ → 1` (`eq_20_17`).
  (20.18): the limit `η → ∞` (`eq_20_18`).
* Hansen–Sargent multiplier preferences with hidden states (`aa_smoothM_exp`), which are
  Kreps–Porteus–Epstein–Zin when `θ₁ = θ₂` (`aa_smoothM_exp_equal`, footnote 2).
* (20.19) of Klibanoff et al. (2009) is the case `u = id` of (20.10) (`eq_20_19`); with power
  utility and `γ > 1` it is not well defined since `E u(c) < 0` lies outside the domain of
  `φ(x) = x^{1−α}/(1−α)` (`aa_juMiao_illDefined`); with `γ = ρ ∈ (0, 1)` and
  `α = 1 − (1 − η)/(1 − γ)`, (20.14)–(20.15) is ordinally equivalent to (20.19)
  (`aa_juMiao_ordinal`); the exponential `φ` is always well defined (`aa_smoothM_expPhi`).

Not formalised: the remark that the exponential specification lacks homogeneity (no statement).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S Z : Type*} [Fintype S] [Fintype Z]

/-! ### Power means -/

/-- Jensen's inequality for `t ↦ tᵏ` convex on `(0, ∞)`. -/
theorem aa_jensen_rpow {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {k : ℝ}
    (hk : ConvexOn ℝ (Set.Ioi 0) fun t : ℝ => t ^ k) {y : Z → ℝ} (hy : ∀ z, 0 < y z) :
    (∑ z, μ z * y z) ^ k ≤ ∑ z, μ z * y z ^ k := by
  have := hk.map_sum_le (t := Finset.univ) (w := μ) (p := y) (fun z _ => hμ.nonneg z)
    hμ.sum_eq_one (fun z _ => hy z)
  simpa [smul_eq_mul] using this

/-- The power mean `(∑ μ yʳ)^{1/r}`. -/
noncomputable def aa_powMean (r : ℝ) (μ y : Z → ℝ) : ℝ := (∑ z, μ z * y z ^ r) ^ r⁻¹

/-- **The power-mean inequality**: for `r ≤ r'`, both nonzero, `M_r(y) ≤ M_{r'}(y)`. -/
theorem aa_powMean_mono [Nonempty Z] {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {y : Z → ℝ}
    (hy : ∀ z, 0 < y z) {r r' : ℝ} (hr : r ≠ 0) (hr' : r' ≠ 0) (hrr : r ≤ r') :
    aa_powMean r μ y ≤ aa_powMean r' μ y := by
  have hpos : ∀ t : ℝ, 0 < ∑ z, μ z * y z ^ t := fun t =>
    aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hy z) t
  have hpow : ∀ z (a b : ℝ), (y z ^ a) ^ b = y z ^ (a * b) := fun z a b =>
    (Real.rpow_mul (hy z).le a b).symm
  unfold aa_powMean
  rcases lt_or_gt_of_ne hr with hneg | hpos'
  · -- `r < 0`: Jensen for `t ↦ t^{r/r'}` applied to `y^{r'}`
    set k := r / r' with hk
    have hconv : ConvexOn ℝ (Set.Ioi 0) fun t : ℝ => t ^ k := by
      rcases lt_or_gt_of_ne hr' with hneg' | hpos''
      · have hk1 : 1 ≤ k := by rw [hk, le_div_iff_of_neg hneg']; linarith
        exact (convexOn_rpow hk1).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
      · exact SS.convexOn_rpow_of_neg (div_neg_of_neg_of_pos hneg hpos'')
    have hJ := aa_jensen_rpow hμ hconv fun z => Real.rpow_pos_of_pos (hy z) r'
    have e1 : ∀ z, (y z ^ r') ^ k = y z ^ r := fun z => by
      rw [hpow, hk, mul_div_cancel₀ _ hr']
    simp only [e1] at hJ
    have h2 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (hpos r') k) hJ
      (inv_lt_zero.2 hneg).le
    rwa [← Real.rpow_mul (hpos r').le, hk, div_mul_eq_mul_div, mul_inv_cancel₀ hr,
      one_div] at h2
  · -- `r > 0`: Jensen for `t ↦ t^{r'/r}` applied to `y^r`
    set k := r' / r with hk
    have hk1 : 1 ≤ k := by rw [hk, le_div_iff₀ hpos']; linarith
    have hconv : ConvexOn ℝ (Set.Ioi 0) fun t : ℝ => t ^ k :=
      (convexOn_rpow hk1).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
    have hJ := aa_jensen_rpow hμ hconv fun z => Real.rpow_pos_of_pos (hy z) r
    have e1 : ∀ z, (y z ^ r) ^ k = y z ^ r' := fun z => by
      rw [hpow, hk, mul_div_cancel₀ _ hr]
    simp only [e1] at hJ
    have hr'0 : 0 < r' := hpos'.trans_le hrr
    have h2 := Real.rpow_le_rpow (Real.rpow_pos_of_pos (hpos r) k).le hJ (inv_pos.2 hr'0).le
    rwa [← Real.rpow_mul (hpos r).le, hk, div_mul_eq_mul_div, mul_inv_cancel₀ hr'.symm.symm,
      one_div] at h2

/-! ### The static model (20.9) -/

/-- The predictive distribution `p(s) = ∑_z μ(z)π_z(s)`. -/
def aa_predictive (μ : Z → ℝ) (π : Z → S → ℝ) : S → ℝ := fun s => ∑ z, μ z * π z s

theorem aa_predictive_isDistribution {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) : SS.IsDistribution (aa_predictive μ π) := by
  refine ⟨fun s => Finset.sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) ((hπ z).nonneg s), ?_⟩
  unfold aa_predictive
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, (hπ _).sum_eq_one, hμ.sum_eq_one]

/-- Expectation under the predictive distribution is the average of the model expectations. -/
theorem aa_E_predictive (μ : Z → ℝ) (π : Z → S → ℝ) (f : S → ℝ) :
    aa_E (aa_predictive μ π) f = ∑ z, μ z * aa_E (π z) f := by
  simp only [aa_E, aa_predictive, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => by ring

/-- The smooth ambiguity utility (20.9): `U(c) = v⁻¹(∫ v(∫ u(c) dq) dμ(q))`, with the inverse
`vinv` of `v` supplied. -/
noncomputable def aa_kmmU (u v vinv : ℝ → ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (c : S → ℝ) : ℝ :=
  vinv (∑ z, μ z * v (aa_E (π z) fun s => u (c s)))

/-- Miao, p. 697: with an affine `v` (ambiguity neutrality) the smooth ambiguity model (20.9) is
subjective expected utility under the predictive distribution. -/
theorem aa_kmm_affine {u v vinv : ℝ → ℝ} {a b : ℝ} (hv : ∀ y, v y = a * y + b)
    (hinv : ∀ y, vinv (v y) = y) {μ : Z → ℝ} (hμ : SS.IsDistribution μ) (π : Z → S → ℝ)
    (c : S → ℝ) : aa_kmmU u v vinv μ π c = aa_E (aa_predictive μ π) fun s => u (c s) := by
  unfold aa_kmmU
  have : ∑ z, μ z * v (aa_E (π z) fun s => u (c s)) =
      v (aa_E (aa_predictive μ π) fun s => u (c s)) := by
    simp only [hv, aa_E_predictive, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      hμ.sum_eq_one, one_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [this, hinv]

/-- Miao, p. 697: an ambiguity-averse decision maker (concave `v`) values a plan below the Bayesian
(expected-utility under the predictive distribution) decision maker:
`∫ v(∫ u dq) dμ ≤ v(∫ u d p̄)`. -/
theorem aa_kmm_concave_le {u v : ℝ → ℝ} {I : Set ℝ} (hv : ConcaveOn ℝ I v) {μ : Z → ℝ}
    (hμ : SS.IsDistribution μ) (π : Z → S → ℝ) (c : S → ℝ)
    (hI : ∀ z, (aa_E (π z) fun s => u (c s)) ∈ I) :
    ∑ z, μ z * v (aa_E (π z) fun s => u (c s)) ≤
      v (aa_E (aa_predictive μ π) fun s => u (c s)) := by
  have := hv.le_map_sum (t := Finset.univ) (w := μ) (fun z _ => hμ.nonneg z) hμ.sum_eq_one
    (fun z _ => hI z)
  simpa [smul_eq_mul, aa_E_predictive] using this

/-! ### The generalized recursive model (20.10) -/

/-- The certainty equivalent of (20.10): `M(x) = v⁻¹(E_μ v(u⁻¹(E_{π_z} u(x))))`. -/
noncomputable def aa_smoothM (u uinv v vinv : ℝ → ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (x : S → ℝ) :
    ℝ :=
  vinv (∑ z, μ z * v (uinv (aa_E (π z) fun s => u (x s))))

/-- Miao, p. 698: when `v ∘ u⁻¹` is affine, (20.10) reduces to Epstein–Zin with hidden states:
`M(x) = u⁻¹(E u(x))` under the predictive distribution. -/
theorem aa_smoothM_linear {u uinv v vinv : ℝ → ℝ} {a b : ℝ}
    (hvu : ∀ y, v (uinv y) = a * y + b) (hinv : ∀ y, vinv (v (uinv y)) = uinv y)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) (π : Z → S → ℝ) (x : S → ℝ) :
    aa_smoothM u uinv v vinv μ π x = uinv (aa_E (aa_predictive μ π) fun s => u (x s)) := by
  unfold aa_smoothM
  have : ∑ z, μ z * v (uinv (aa_E (π z) fun s => u (x s))) =
      v (uinv (aa_E (aa_predictive μ π) fun s => u (x s))) := by
    simp only [hvu, aa_E_predictive, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      hμ.sum_eq_one, one_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [this, hinv]

/-- Bayes' rule: the posterior over hidden states after observing `s`. -/
noncomputable def aa_posterior (μ : Z → ℝ) (π : Z → S → ℝ) (s : S) : Z → ℝ :=
  fun z => μ z * π z s / aa_predictive μ π s

/-- Miao, p. 698: the posterior obtained by Bayes' rule is a distribution when the observation has
positive predictive probability. -/
theorem aa_posterior_isDistribution {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) {s : S} (hs : 0 < aa_predictive μ π s) :
    SS.IsDistribution (aa_posterior μ π s) :=
  ⟨fun z => div_nonneg (mul_nonneg (hμ.nonneg z) ((hπ z).nonneg s)) hs.le, by
    simp only [aa_posterior, ← Finset.sum_div]
    exact div_self hs.ne'⟩

/-- The posterior is a martingale: its predictive expectation is the prior. -/
theorem aa_posterior_martingale {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) (z : Z) :
    ∑ s, aa_predictive μ π s * aa_posterior μ π s z = μ z := by
  have e : ∀ s, aa_predictive μ π s * aa_posterior μ π s z = μ z * π z s := fun s => by
    by_cases h : aa_predictive μ π s = 0
    · have h0 : ∀ z' ∈ Finset.univ, 0 ≤ μ z' * π z' s := fun z' _ =>
        mul_nonneg (hμ.nonneg z') ((hπ z').nonneg s)
      have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 h z (Finset.mem_univ z)
      simp [aa_posterior, h, this]
    · simp only [aa_posterior]
      field_simp
  simp [e, ← Finset.mul_sum, (hπ z).sum_eq_one]

/-! ### The homothetic specification (20.11)–(20.15) -/

/-- The power utility `u(x) = x^{1−γ}/(1−γ)` of (20.12) (and `v` of (20.13) with `η`). -/
noncomputable def aa_powU (γ x : ℝ) : ℝ := x ^ (1 - γ) / (1 - γ)

/-- Its inverse `u⁻¹(y) = ((1 − γ)y)^{1/(1−γ)}`. -/
noncomputable def aa_powUinv (γ y : ℝ) : ℝ := ((1 - γ) * y) ^ (1 - γ)⁻¹

theorem aa_powUinv_powU {γ : ℝ} (hγ : γ ≠ 1) {x : ℝ} (hx : 0 < x) :
    aa_powUinv γ (aa_powU γ x) = x := by
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_powUinv aa_powU
  rw [mul_div_cancel₀ _ h1, Real.rpow_rpow_inv hx.le h1]

/-- The certainty equivalent (20.15):
`M(x) = (E_μ (E_{π_z} x^{1−γ})^{(1−η)/(1−γ)})^{1/(1−η)}`. -/
noncomputable def aa_ju (γ η : ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (x : S → ℝ) : ℝ :=
  (∑ z, μ z * (aa_E (π z) fun s => x s ^ (1 - γ)) ^ ((1 - η) / (1 - γ))) ^ (1 - η)⁻¹

/-- **(20.15)** (Miao, p. 699): with the power utilities (20.12)–(20.13), the certainty equivalent
of (20.10) is (20.15). -/
theorem aa_smoothM_power [Nonempty S] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1) {μ : Z → ℝ}
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_smoothM (aa_powU γ) (aa_powUinv γ) (aa_powU η) (aa_powUinv η) μ π x = aa_ju γ η μ π x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have he : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  have hE : ∀ z, 0 < aa_E (π z) fun s => x s ^ (1 - γ) := fun z =>
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  have inner : ∀ z, aa_powU η (aa_powUinv γ (aa_E (π z) fun s => aa_powU γ (x s))) =
      (aa_E (π z) fun s => x s ^ (1 - γ)) ^ ((1 - η) / (1 - γ)) / (1 - η) := fun z => by
    unfold aa_powU aa_powUinv
    have : (1 - γ) * aa_E (π z) (fun s => x s ^ (1 - γ) / (1 - γ)) =
        aa_E (π z) fun s => x s ^ (1 - γ) := by
      rw [← aa_E_smul]
      congr 1
      funext s
      field_simp
    rw [this, ← Real.rpow_mul (hE z).le, inv_mul_eq_div]
  unfold aa_smoothM aa_ju
  simp only [inner]
  unfold aa_powUinv
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by field_simp

/-- The generalized recursive smooth ambiguity utility (20.14) on the event tree: at the node `h`
the posterior is `μ h` and the likelihoods are `π h`; `U_T = c_T`. -/
noncomputable def aa_juU (β ρ γ η : ℝ) (μ : List S → Z → ℝ) (π : List S → Z → S → ℝ)
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => c h
  | n + 1, h => aa_W β ρ (c h) (aa_ju γ η (μ h) (π h) fun s => aa_juU β ρ γ η μ π c n (s :: h))

/-- (20.15) as a power mean of the model-wise certainty equivalents
`Y_z = (E_{π_z} x^{1−γ})^{1/(1−γ)}`. -/
theorem aa_ju_eq_powMean [Nonempty S] {γ : ℝ} (hγ : γ ≠ 1) (η : ℝ) (μ : Z → ℝ)
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_ju γ η μ π x = aa_powMean (1 - η) μ fun z => aa_KP γ (π z) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_ju aa_powMean aa_KP
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  have hE : 0 < aa_E (π z) fun s => x s ^ (1 - γ) :=
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  rw [← Real.rpow_mul hE.le, inv_mul_eq_div]

/-- Miao, p. 699: with `η = γ` the decision maker is ambiguity neutral and (20.15) is the
Kreps–Porteus certainty equivalent of Epstein–Zin under the predictive distribution. -/
theorem aa_ju_neutral {γ : ℝ} (hγ : γ ≠ 1) (μ : Z → ℝ) (π : Z → S → ℝ) (x : S → ℝ) :
    aa_ju γ γ μ π x = aa_KP γ (aa_predictive μ π) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_ju aa_KP
  rw [div_self hg, aa_E_predictive]
  simp

/-- Miao, p. 699: with `η = γ`, the recursion (20.14) is the Epstein–Zin recursion (20.3) under
the predictive one-step-ahead distributions. -/
theorem aa_juU_neutral {β ρ γ : ℝ} (hγ : γ ≠ 1) (μ : List S → Z → ℝ) (π : List S → Z → S → ℝ)
    (c : List S → ℝ) :
    ∀ n h, aa_juU β ρ γ γ μ π c n h =
      aa_ezU β ρ γ (fun h' => aa_predictive (μ h') (π h')) c n h
  | 0, h => rfl
  | n + 1, h => by
    simp only [aa_juU, aa_ezU, aa_ju_neutral hγ]
    rw [show (fun s => aa_juU β ρ γ γ μ π c n (s :: h)) =
      (fun s => aa_ezU β ρ γ (fun h' => aa_predictive (μ h') (π h')) c n (s :: h)) from
        funext fun s => aa_juU_neutral hγ μ π c n (s :: h)]

/-- Miao, p. 699: "a more ambiguity-averse agent with a higher value of `η` has a lower utility
level": the certainty equivalent (20.15) is decreasing in `η` (`η, η' ≠ 1`). -/
theorem aa_ju_antitone [Nonempty S] [Nonempty Z] {γ : ℝ} (hγ : γ ≠ 1) {μ : Z → ℝ}
    (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) {η η' : ℝ} (hη : η ≠ 1) (hη' : η' ≠ 1) (hηη' : η ≤ η') :
    aa_ju γ η' μ π x ≤ aa_ju γ η μ π x := by
  rw [aa_ju_eq_powMean hγ _ _ hπ hx, aa_ju_eq_powMean hγ _ _ hπ hx]
  exact aa_powMean_mono hμ (fun z => aa_KP_pos γ (hπ z) hx) (sub_ne_zero.2 (Ne.symm hη'))
    (sub_ne_zero.2 (Ne.symm hη)) (by linarith)

/-- Miao, p. 699: ambiguity aversion `η ≥ γ` lowers the certainty equivalent below the Epstein–Zin
(ambiguity-neutral) value. -/
theorem aa_ju_le_KP [Nonempty S] [Nonempty Z] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1) (hγη : γ ≤ η)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) : aa_ju γ η μ π x ≤ aa_KP γ (aa_predictive μ π) x := by
  rw [← aa_ju_neutral hγ]
  exact aa_ju_antitone hγ hμ hπ hx hγ hη hγη

/-- `η ≤ γ` (ambiguity loving) raises the certainty equivalent above the Epstein–Zin value. -/
theorem aa_KP_le_ju [Nonempty S] [Nonempty Z] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1) (hηγ : η ≤ γ)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) : aa_KP γ (aa_predictive μ π) x ≤ aa_ju γ η μ π x := by
  rw [← aa_ju_neutral hγ]
  exact aa_ju_antitone hγ hμ hπ hx hη hγ hηγ

/-- Miao, p. 699: the utility (20.14) is decreasing in `η` (one step, any positive continuation). -/
theorem aa_W_ju_antitone [Nonempty S] [Nonempty Z] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) {c : ℝ} (hc : 0 < c) {x : S → ℝ} (hx : ∀ s, 0 < x s)
    {η η' : ℝ} (hη : η ≠ 1) (hη' : η' ≠ 1) (hηη' : η ≤ η') :
    aa_W β ρ c (aa_ju γ η' μ π x) ≤ aa_W β ρ c (aa_ju γ η μ π x) := by
  have hpos : ∀ e, 0 < aa_ju γ e μ π x := fun e => by
    rw [aa_ju_eq_powMean hγ _ _ hπ hx]
    exact Real.rpow_pos_of_pos (aa_E_pos hμ fun z => Real.rpow_pos_of_pos
      (aa_KP_pos γ (hπ z) hx) _) _
  exact (aa_W_strictMonoOn hβ0 hβ1 hρ hc).monotoneOn (hpos η') (hpos η)
    (aa_ju_antitone hγ hμ hπ hx hη hη' hηη')

/-! ### The limits (20.16)–(20.18) -/

/-- Miao, p. 699: as `ρ → 1` the CES aggregator (20.11) tends to the Cobb–Douglas aggregator
`c^{1−β}y^β`. -/
theorem aa_W_tendsto_rho_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {c y : ℝ} (hc : 0 < c)
    (hy : 0 < y) :
    Tendsto (fun ρ => aa_W β ρ c y) (𝓝[≠] 1) (𝓝 (c ^ (1 - β) * y ^ β)) := by
  set p : Bool → ℝ := fun b => if b then β else 1 - β with hp
  set v : Bool → ℝ := fun b => if b then Real.log y else Real.log c with hv
  have hpD : SS.IsDistribution p :=
    ⟨fun b => by cases b <;> simp [hp] <;> linarith, by simp [hp]⟩
  have hL := aa_tendsto_logmgf hpD v
  have hsub : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact sub_ne_zero.2 (Ne.symm hρ)
  have h2 := (Real.continuous_exp.tendsto _).comp (hL.comp hsub)
  have hlim : Real.exp (aa_E p v) = c ^ (1 - β) * y ^ β := by
    simp only [aa_E, Fintype.sum_bool, hp, hv, ↓reduceIte, Bool.false_eq_true]
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hy, ← Real.exp_add]
    ring_nf
  rw [hlim] at h2
  refine h2.congr fun ρ => ?_
  simp only [Function.comp_apply, aa_W, Fintype.sum_bool, hp, hv, ↓reduceIte,
    Bool.false_eq_true]
  have hb : 0 < (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) ∨
      (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) = 0 := by
    rcases (show (0 : ℝ) ≤ (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) by
      have := Real.rpow_pos_of_pos hc (1 - ρ)
      have := Real.rpow_pos_of_pos hy (1 - ρ)
      nlinarith).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have e1 : β * Real.exp ((1 - ρ) * Real.log y) + (1 - β) * Real.exp ((1 - ρ) * Real.log c) =
      (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) := by
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hy]
    ring_nf
  rw [e1]
  rcases hb with hb | hb
  · rw [Real.rpow_def_of_pos hb]
    ring_nf
  · have hβ' : β = 0 ∧ 1 - β = 0 := by
      have := Real.rpow_pos_of_pos hc (1 - ρ)
      have := Real.rpow_pos_of_pos hy (1 - ρ)
      constructor <;> nlinarith
    exact absurd (hβ'.1 ▸ hβ'.2) (by norm_num)

/-- **(20.16)** (Miao, p. 699): at `ρ = 1` the aggregator is `U = c^{1−β}M^β`, and with
`U_{t+1} = exp V_{t+1}` the log utility `V = ln U` satisfies
`V_t = (1 − β) ln c_t + (β/(1 − η)) ln E_μ exp(((1 − η)/(1 − γ)) ln E_{π_z} exp((1 − γ)V_{t+1}))`.
-/
theorem eq_20_16 [Nonempty S] {β γ η : ℝ} {μ : Z → ℝ} (hμ : SS.IsDistribution μ) [Nonempty Z]
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) {c : ℝ} (hc : 0 < c) (V : S → ℝ) :
    Real.log (c ^ (1 - β) * aa_ju γ η μ π (fun s => Real.exp (V s)) ^ β) =
      (1 - β) * Real.log c + β / (1 - η) * Real.log (∑ z, μ z * Real.exp ((1 - η) / (1 - γ) *
        Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s)))) := by
  have hE : ∀ z, 0 < aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ) := fun z =>
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (Real.exp_pos _) _
  have e1 : ∀ z, (aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ)) =
      ∑ s, π z s * Real.exp ((1 - γ) * V s) := fun z => by
    unfold aa_E
    exact Finset.sum_congr rfl fun s _ => by
      dsimp only
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm (V s)]
  have hS : 0 < ∑ z, μ z * (aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ)) ^
      ((1 - η) / (1 - γ)) := aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hE z) _
  have hM : 0 < aa_ju γ η μ π (fun s => Real.exp (V s)) := Real.rpow_pos_of_pos hS _
  rw [Real.log_mul (Real.rpow_pos_of_pos hc _).ne' (Real.rpow_pos_of_pos hM _).ne',
    Real.log_rpow hc, Real.log_rpow hM]
  unfold aa_ju
  rw [Real.log_rpow hS]
  have e2 : ∑ z, μ z * (aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ)) ^ ((1 - η) / (1 - γ)) =
      ∑ z, μ z * Real.exp ((1 - η) / (1 - γ) *
        Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s))) :=
    Finset.sum_congr rfl fun z _ => by
      rw [Real.rpow_def_of_pos (hE z), e1, mul_comm (Real.log _)]
  rw [e2]
  ring

/-- **(20.17)** (Miao, p. 700): as `γ → 1`, the right side of (20.16) tends to
`(1 − β) ln c_t + (β/(1 − η)) ln E_μ exp((1 − η)E_{π_z}[V_{t+1}])`. -/
theorem eq_20_17 {β η : ℝ} {μ : Z → ℝ} (hμ : SS.IsDistribution μ) [Nonempty Z]
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) (c : ℝ) (V : S → ℝ) :
    Tendsto (fun γ => (1 - β) * Real.log c + β / (1 - η) * Real.log (∑ z, μ z *
        Real.exp ((1 - η) / (1 - γ) * Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s)))))
      (𝓝[≠] 1)
      (𝓝 ((1 - β) * Real.log c + β / (1 - η) *
        Real.log (∑ z, μ z * Real.exp ((1 - η) * aa_E (π z) V)))) := by
  have hsub : Tendsto (fun γ : ℝ => 1 - γ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun γ : ℝ => 1 - γ) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with γ hγ
      exact sub_ne_zero.2 (Ne.symm hγ)
  have hz : ∀ z, Tendsto (fun γ => (1 - η) / (1 - γ) *
      Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s))) (𝓝[≠] 1)
        (𝓝 ((1 - η) * aa_E (π z) V)) := fun z => by
    have := ((aa_tendsto_logmgf (hπ z) V).comp hsub).const_mul (1 - η)
    refine this.congr fun γ => ?_
    simp only [Function.comp_apply]
    ring
  have hsum : Tendsto (fun γ => ∑ z, μ z * Real.exp ((1 - η) / (1 - γ) *
      Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s)))) (𝓝[≠] 1)
        (𝓝 (∑ z, μ z * Real.exp ((1 - η) * aa_E (π z) V))) :=
    tendsto_finsetSum _ fun z _ => ((Real.continuous_exp.tendsto _).comp (hz z)).const_mul (μ z)
  have hpos : 0 < ∑ z, μ z * Real.exp ((1 - η) * aa_E (π z) V) :=
    aa_E_pos hμ fun z => Real.exp_pos _
  exact tendsto_const_nhds.add ((hsum.log hpos.ne').const_mul _)

/-- **(20.18)** (Miao, p. 700): as `η → ∞` the log-exponential specification (20.17) tends to the
recursive multiple-priors form `V_t = (1 − β) ln c_t + β min_z E_{π_z}[V_{t+1}]`, provided the
minimising model has positive posterior probability. Here `X z = E_{π_z}[V_{t+1}]`. -/
theorem eq_20_18 {β : ℝ} {μ : Z → ℝ} (hμ : SS.IsDistribution μ) (c : ℝ) (X : Z → ℝ) {z₀ : Z}
    (hmin : ∀ z, X z₀ ≤ X z) (hμz : 0 < μ z₀) :
    Tendsto (fun η => (1 - β) * Real.log c + β / (1 - η) *
        Real.log (∑ z, μ z * Real.exp ((1 - η) * X z))) atTop
      (𝓝 ((1 - β) * Real.log c + β * X z₀)) := by
  have hk : Tendsto (fun η : ℝ => η + -1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have h := ((aa_tendsto_softmin hμ X hmin hμz).comp hk).const_mul β
  refine (tendsto_const_nhds.add h).congr fun η => ?_
  simp only [Function.comp_apply]
  have e1 : ∀ z, -(η + -1) * X z = (1 - η) * X z := fun z => by ring
  simp only [e1]
  have e2 : (1 - η) = -(η + -1) := by ring
  rw [e2, div_neg, div_eq_mul_inv]
  ring

/-! ### Exponential specifications and the nested models -/

/-- The inverse `u⁻¹(y) = −θ ln(−y)` of the exponential utility. -/
noncomputable def aa_expUinv (θ y : ℝ) : ℝ := -θ * Real.log (-y)

/-- Miao, p. 699: with `u(x) = −exp(−x/θ₁)` and `v(x) = −exp(−x/θ₂)`, the certainty equivalent of
(20.10) is the recursive multiplier with hidden states of Hansen and Sargent (2007),
`M(x) = −θ₂ ln E_μ (E_{π_z} exp(−x/θ₁))^{θ₁/θ₂}`. -/
theorem aa_smoothM_exp [Nonempty S] {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (μ : Z → ℝ)
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) (x : S → ℝ) :
    aa_smoothM (aa_expU θ₁) (aa_expUinv θ₁) (aa_expU θ₂) (aa_expUinv θ₂) μ π x =
      -θ₂ * Real.log (∑ z, μ z * (∑ s, π z s * Real.exp (-x s / θ₁)) ^ (θ₁ / θ₂)) := by
  have hA : ∀ z, 0 < ∑ s, π z s * Real.exp (-x s / θ₁) := fun z =>
    aa_E_pos (hπ z) fun s => Real.exp_pos _
  have inner : ∀ z, aa_expU θ₂ (aa_expUinv θ₁ (aa_E (π z) fun s => aa_expU θ₁ (x s))) =
      -(∑ s, π z s * Real.exp (-x s / θ₁)) ^ (θ₁ / θ₂) := fun z => by
    have e : (aa_E (π z) fun s => aa_expU θ₁ (x s)) = -∑ s, π z s * Real.exp (-x s / θ₁) := by
      simp [aa_E, aa_expU, Finset.sum_neg_distrib]
    rw [e]
    unfold aa_expU aa_expUinv
    rw [neg_neg, Real.rpow_def_of_pos (hA z)]
    congr 2
    field_simp
  unfold aa_smoothM
  simp only [inner, mul_neg, Finset.sum_neg_distrib]
  unfold aa_expUinv
  rw [neg_neg]

/-- Miao, p. 699, footnote 2: with `θ₁ = θ₂ = θ` the multiplier model with hidden states is the
risk-sensitive (Kreps–Porteus–Epstein–Zin) certainty equivalent under the predictive
distribution. -/
theorem aa_smoothM_exp_equal [Nonempty S] {θ : ℝ} (hθ : 0 < θ) (μ : Z → ℝ)
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) (x : S → ℝ) :
    aa_smoothM (aa_expU θ) (aa_expUinv θ) (aa_expU θ) (aa_expUinv θ) μ π x =
      -θ * Real.log (∑ s, aa_predictive μ π s * Real.exp (-x s / θ)) := by
  rw [aa_smoothM_exp hθ hθ μ hπ x, div_self hθ.ne']
  simp only [Real.rpow_one]
  have := aa_E_predictive μ π fun s => Real.exp (-x s / θ)
  simp only [aa_E] at this
  rw [this]

/-- Miao, p. 700: the exponential `φ(x) = −exp(−x/θ)` makes `φ⁻¹(E_μ φ(y)) = −θ ln E_μ exp(−y/θ)`
well defined for every real `y`. -/
theorem aa_smoothM_expPhi (θ : ℝ) (μ y : Z → ℝ) :
    aa_expUinv θ (∑ z, μ z * aa_expU θ (y z)) = -θ * Real.log (∑ z, μ z * Real.exp (-y z / θ)) := by
  unfold aa_expUinv aa_expU
  simp [Finset.sum_neg_distrib]

/-- **(20.19)** (Miao, p. 700): with `W(c, y) = u(c) + βy` and the identity in place of the inner
utility, (20.10) is the model of Klibanoff et al. (2009):
`V_t = u(c_t) + βφ⁻¹(E_μ φ(E_{π_z}[V_{t+1}]))`. -/
theorem eq_20_19 (u φ φinv : ℝ → ℝ) (β : ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (c : ℝ) (V : S → ℝ) :
    u c + β * aa_smoothM id id φ φinv μ π V = u c + β * φinv (∑ z, μ z * φ (aa_E (π z) V)) := by
  rfl

/-- Miao, p. 700: with the power utility (20.12) and `γ > 1`, every expected utility is negative,
so it lies outside the domain `x > 0` of `φ(x) = x^{1−α}/(1−α)`: (20.19) is not well defined. -/
theorem aa_juMiao_illDefined [Nonempty S] {γ : ℝ} (hγ : 1 < γ) {p : S → ℝ}
    (hp : SS.IsDistribution p) {c : S → ℝ} (hc : ∀ s, 0 < c s) :
    aa_E p (fun s => aa_powU γ (c s)) < 0 := by
  have h : 0 < aa_E p fun s => -aa_powU γ (c s) := aa_E_pos hp fun s => by
    unfold aa_powU
    rw [neg_pos]
    exact div_neg_of_pos_of_neg (Real.rpow_pos_of_pos (hc s) _) (by linarith)
  have e : (aa_E p fun s => -aa_powU γ (c s)) = -aa_E p fun s => aa_powU γ (c s) := by
    simp [aa_E, Finset.sum_neg_distrib]
  linarith

/-- The recursion (20.19) on the event tree, with terminal utility `V_T = ψ(c_T)`. -/
noncomputable def aa_kmm09U (u φ φinv ψ : ℝ → ℝ) (β : ℝ) (μ : List S → Z → ℝ)
    (π : List S → Z → S → ℝ) (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => ψ (c h)
  | n + 1, h => u (c h) + β * φinv (∑ z, μ h z * φ (aa_E (π h z)
      fun s => aa_kmm09U u φ φinv ψ β μ π c n (s :: h)))

/-- The utility (20.14) is positive. -/
theorem aa_juU_pos [Nonempty S] [Nonempty Z] {β ρ γ η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : γ ≠ 1) {μ : List S → Z → ℝ} (hμ : ∀ h, SS.IsDistribution (μ h))
    {π : List S → Z → S → ℝ} (hπ : ∀ h z, SS.IsDistribution (π h z)) {c : List S → ℝ}
    (hc : ∀ h, 0 < c h) : ∀ n h, 0 < aa_juU β ρ γ η μ π c n h
  | 0, h => hc h
  | n + 1, h => by
    refine aa_W_pos hβ0 hβ1 (hc h) ?_
    rw [aa_ju_eq_powMean hγ _ _ (hπ h) fun s => aa_juU_pos hβ0 hβ1 hγ hμ hπ hc n (s :: h)]
    exact Real.rpow_pos_of_pos (aa_E_pos (hμ h) fun z => Real.rpow_pos_of_pos
      (aa_KP_pos γ (hπ h z) fun s => aa_juU_pos hβ0 hβ1 hγ hμ hπ hc n (s :: h)) _) _

/-- The one-step ordinal equivalence behind `aa_juMiao_ordinal`. With `ρ = γ ∈ (0, 1)`,
`k = (1 − γ)(1 − β)` and `1 − α = (1 − η)/(1 − γ)`, the transform `V = U^{1−γ}/k` of (20.14)
satisfies
`V = u(c) + βφ⁻¹(E_μ φ(E_{π_z} V'))`, `u(c) = c^{1−γ}/(1−γ)`, `φ(x) = x^{1−α}/(1−α)`. -/
theorem aa_juMiao_step [Nonempty S] [Nonempty Z] {β γ η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ1 : γ < 1)
    (hη : η ≠ 1) {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) {c : ℝ} (hc : 0 < c) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_W β γ c (aa_ju γ η μ π x) ^ (1 - γ) / ((1 - γ) * (1 - β)) =
      aa_powU γ c + β * aa_powUinv (1 - (1 - η) / (1 - γ)) (∑ z, μ z *
        aa_powU (1 - (1 - η) / (1 - γ))
          (aa_E (π z) fun s => x s ^ (1 - γ) / ((1 - γ) * (1 - β)))) := by
  set k := (1 - γ) * (1 - β) with hk
  set a := (1 - η) / (1 - γ) with ha
  have hg : 0 < 1 - γ := by linarith
  have hb : 0 < 1 - β := by linarith
  have hk0 : 0 < k := mul_pos hg hb
  have ha0 : a ≠ 0 := div_ne_zero (sub_ne_zero.2 (Ne.symm hη)) hg.ne'
  have e1 : 1 - (1 - a) = a := by ring
  have hE : ∀ z, 0 < aa_E (π z) fun s => x s ^ (1 - γ) := fun z =>
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  set T := ∑ z, μ z * (aa_E (π z) fun s => x s ^ (1 - γ)) ^ a with hT
  have hT0 : 0 < T := aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hE z) _
  have hM : aa_ju γ η μ π x = T ^ (1 - η)⁻¹ := rfl
  have hM0 : 0 < aa_ju γ η μ π x := by rw [hM]; exact Real.rpow_pos_of_pos hT0 _
  -- the left side
  have hL : aa_W β γ c (aa_ju γ η μ π x) ^ (1 - γ) =
      (1 - β) * c ^ (1 - γ) + β * T ^ a⁻¹ := by
    unfold aa_W
    have hA : 0 ≤ (1 - β) * c ^ (1 - γ) + β * aa_ju γ η μ π x ^ (1 - γ) :=
      add_nonneg (mul_nonneg hb.le (Real.rpow_pos_of_pos hc _).le)
        (mul_nonneg hβ0.le (Real.rpow_pos_of_pos hM0 _).le)
    rw [Real.rpow_inv_rpow hA hg.ne', hM, ← Real.rpow_mul hT0.le]
    congr 3
    rw [ha]
    field_simp
  -- the right side
  have hR : aa_powUinv (1 - a) (∑ z, μ z * aa_powU (1 - a)
      (aa_E (π z) fun s => x s ^ (1 - γ) / k)) = T ^ a⁻¹ / k := by
    have hEk : ∀ z, (aa_E (π z) fun s => x s ^ (1 - γ) / k) =
        (aa_E (π z) fun s => x s ^ (1 - γ)) / k := fun z => by
      rw [div_eq_inv_mul, ← aa_E_smul]
      congr 1
      funext s
      ring
    unfold aa_powUinv aa_powU
    simp only [e1, hEk]
    have hsum : a * ∑ z, μ z * (((aa_E (π z) fun s => x s ^ (1 - γ)) / k) ^ a / a) =
        T / k ^ a := by
      rw [hT, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Real.div_rpow (hE z).le hk0.le]
      field_simp
    rw [hsum, Real.div_rpow hT0.le (Real.rpow_pos_of_pos hk0 _).le,
      ← Real.rpow_mul hk0.le, mul_inv_cancel₀ ha0, Real.rpow_one]
  rw [hL, hR, aa_powU]
  field_simp
  ring

/-- Miao, p. 700: with `ρ = γ ∈ (0, 1)` and `α = 1 − (1 − η)/(1 − γ)`, the generalized smooth
ambiguity utility (20.14)–(20.15) is ordinally equivalent to the model (20.19) of Klibanoff et al.
(2009): `V = U^{1−γ}/((1 − γ)(1 − β))` (a strictly increasing transform of `U`) satisfies (20.19)
at every node, with the terminal utility `V_T = c_T^{1−γ}/((1 − γ)(1 − β))`. -/
theorem aa_juMiao_ordinal [Nonempty S] [Nonempty Z] {β γ η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ1 : γ < 1) (hη : η ≠ 1) {μ : List S → Z → ℝ} (hμ : ∀ h, SS.IsDistribution (μ h))
    {π : List S → Z → S → ℝ} (hπ : ∀ h z, SS.IsDistribution (π h z)) {c : List S → ℝ}
    (hc : ∀ h, 0 < c h) :
    ∀ n h, aa_kmm09U (aa_powU γ) (aa_powU (1 - (1 - η) / (1 - γ)))
        (aa_powUinv (1 - (1 - η) / (1 - γ))) (fun y => y ^ (1 - γ) / ((1 - γ) * (1 - β))) β μ π c
        n h = aa_juU β γ γ η μ π c n h ^ (1 - γ) / ((1 - γ) * (1 - β))
  | 0, h => rfl
  | n + 1, h => by
    have hγ : γ ≠ 1 := hγ1.ne
    simp only [aa_kmm09U, aa_juU]
    rw [aa_juMiao_step hβ0 hβ1 hγ1 hη (hμ h) (hπ h) (hc h)
      fun s => aa_juU_pos hβ0 hβ1 hγ hμ hπ hc n (s :: h)]
    congr 3
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 3
    funext s
    exact aa_juMiao_ordinal hβ0 hβ1 hγ1 hη hμ hπ hc n (s :: h)

end Miao.RecursiveUtility
