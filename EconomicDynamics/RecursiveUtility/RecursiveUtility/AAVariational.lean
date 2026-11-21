/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.AAMaxmin
import RecursiveUtility.AALimits
import RecursiveUtility.SSAdversarial

/-!
# Variational, divergence and multiplier utility

Miao, §20.2.2, pp. 693–696 (static models), on a finite state space `S` with reference
distribution `p`.

* Variational utility `U(c) = min_q {∫ u dq + c(q)}` (`aa_variational`); with zero cost it is
  maxmin utility (`aa_variational_zero`).
* The `w`-weighted `φ`-divergence `D_φʷ(q‖p) = ∫ w φ(dq/dp) dp` (`aa_phiDiv`), with
  `D(p‖p) = 0` and `D ≥ 0` (`aa_phiDiv_self`, `aa_phiDiv_nonneg`), and divergence utility
  `min_q {∫ u dq + θD(q‖p)}` (`aa_divU`). It is at most expected utility under `p` and
  increasing in `θ`: a smaller `θ` is more ambiguity averse (`aa_divU_le_E`, `aa_divU_mono`).
* Relative entropy `φ(x) = x ln x − x + 1` (`aa_klPhi`; `φ ≥ 0`, `φ(1) = 0`, `φ(t)/t → ∞`):
  `D_φ¹(q‖p) = ∫ ln(dq/dp) dq` (`aa_phiDiv_kl`), so divergence utility is the multiplier utility
  of Hansen and Sargent, and solving the minimisation gives the risk-sensitive utility
  `−θ ln ∫ exp(−u/θ) dp` (`aa_multiplier_isLeast`, `aa_divU_kl`). As `θ → ∞` it tends to expected
  utility (`aa_riskSensitive_tendsto`). It is the certainty equivalent of the exponential utility
  `−exp(−x/θ)`, whose absolute risk aversion is `1/θ` (`aa_riskSensitive_eq_ce`,
  `aa_expU_arrowPratt`): "concern for robustness enhances risk aversion by `1/θ`".
* The relative Gini index `φ(x) = (x − 1)²/2` (`aa_chiPhi`): on the domain `c − Ec ≤ θ`, divergence
  utility with `u(c) = c` is the monotone mean–variance utility `E c − Var(c)/(2θ)`, attained by the
  density `1 − (c − Ec)/θ` (`aa_chi2_mmv`).

Not formalised: the probabilistic sophistication of divergence preferences with `w = 1` and their
failure to explain the Ellsberg paradox (results of Maccheroni, Marinacci and Rustichini (2006a)
that the text cites without derivation).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-- The set `Δ(S)` of all distributions on `S`. -/
def aa_Δ (S : Type*) [Fintype S] : Set (S → ℝ) := {q | SS.IsDistribution q}

/-- Variational utility `U(c) = inf_{q ∈ Q} {∫ u dq + c(q)}` (Miao, p. 693). -/
noncomputable def aa_variational (Q : Set (S → ℝ)) (cost : (S → ℝ) → ℝ) (u : S → ℝ) : ℝ :=
  sInf ((fun q => aa_E q u + cost q) '' Q)

/-- Miao, p. 694: with zero cost, variational utility is maxmin expected utility. -/
theorem aa_variational_zero (Q : Set (S → ℝ)) (u : S → ℝ) :
    aa_variational Q (fun _ => 0) u = aa_maxmin Q u := by
  simp [aa_variational, aa_maxmin]

/-- The `w`-weighted `φ`-divergence `D_φʷ(q‖p) = ∫ w φ(dq/dp) dp` (Miao, p. 694), with
`dq/dp = q/p`. -/
noncomputable def aa_phiDiv (φ : ℝ → ℝ) (w p q : S → ℝ) : ℝ := ∑ s, w s * φ (q s / p s) * p s

/-- Divergence utility `U(c) = inf_{q ∈ Q} {∫ u dq + θD_φʷ(q‖p)}` (Miao, p. 694). -/
noncomputable def aa_divU (φ : ℝ → ℝ) (w p : S → ℝ) (θ : ℝ) (Q : Set (S → ℝ)) (u : S → ℝ) : ℝ :=
  aa_variational Q (fun q => θ * aa_phiDiv φ w p q) u

/-- `D(p‖p) = 0` when `φ(1) = 0`. -/
theorem aa_phiDiv_self {φ : ℝ → ℝ} (hφ : φ 1 = 0) (w p : S → ℝ) : aa_phiDiv φ w p p = 0 := by
  unfold aa_phiDiv
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases h : p s = 0
  · simp [h]
  · simp [div_self h, hφ]

/-- `D ≥ 0` when `φ ≥ 0`, `w ≥ 0`. -/
theorem aa_phiDiv_nonneg {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {w p : S → ℝ} (hw : ∀ s, 0 ≤ w s)
    (hp : SS.IsDistribution p) (q : S → ℝ) : 0 ≤ aa_phiDiv φ w p q :=
  Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hw s) (hφ _)) (hp.nonneg s)

theorem aa_divU_bdd {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {w p : S → ℝ} (hw : ∀ s, 0 ≤ w s)
    (hp : SS.IsDistribution p) {θ : ℝ} (hθ : 0 ≤ θ) {Q : Set (S → ℝ)}
    (hQ : ∀ q ∈ Q, SS.IsDistribution q) (u : S → ℝ) :
    BddBelow ((fun q => aa_E q u + θ * aa_phiDiv φ w p q) '' Q) :=
  ⟨-∑ s, |u s|, by
    rintro _ ⟨q, hq, rfl⟩
    have := aa_E_ge_neg (hQ q hq) u
    have := mul_nonneg hθ (aa_phiDiv_nonneg hφ hw hp q)
    dsimp only
    linarith⟩

/-- Divergence utility is at most expected utility under the reference model `p` (Miao, p. 694:
the decision maker takes `p` into account among the nearby models). -/
theorem aa_divU_le_E {φ : ℝ → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : φ 1 = 0) {w p : S → ℝ}
    (hw : ∀ s, 0 ≤ w s) (hp : SS.IsDistribution p) {θ : ℝ} (hθ : 0 ≤ θ) {Q : Set (S → ℝ)}
    (hQ : ∀ q ∈ Q, SS.IsDistribution q) (hpQ : p ∈ Q) (u : S → ℝ) :
    aa_divU φ w p θ Q u ≤ aa_E p u := by
  have := csInf_le (aa_divU_bdd hφ0 hw hp hθ hQ u) ⟨p, hpQ, rfl⟩
  simpa [aa_divU, aa_variational, aa_phiDiv_self hφ1] using this

/-- Miao, p. 694: a smaller `θ` means a larger degree of ambiguity aversion: divergence utility is
increasing in `θ`. -/
theorem aa_divU_mono {φ : ℝ → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) {w p : S → ℝ} (hw : ∀ s, 0 ≤ w s)
    (hp : SS.IsDistribution p) {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ') {Q : Set (S → ℝ)}
    (hQ : ∀ q ∈ Q, SS.IsDistribution q) (hne : Q.Nonempty) (u : S → ℝ) :
    aa_divU φ w p θ Q u ≤ aa_divU φ w p θ' Q u := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨q, hq, rfl⟩
  refine (csInf_le (aa_divU_bdd hφ0 hw hp hθ hQ u) ⟨q, hq, rfl⟩).trans ?_
  have := mul_le_mul_of_nonneg_right hθθ' (aa_phiDiv_nonneg hφ0 hw hp q)
  dsimp only
  linarith

/-! ### Relative entropy and multiplier utility -/

/-- The relative-entropy index `φ(x) = x ln x − x + 1` (Miao, p. 695). -/
noncomputable def aa_klPhi (x : ℝ) : ℝ := x * Real.log x - x + 1

theorem aa_klPhi_one : aa_klPhi 1 = 0 := by simp [aa_klPhi]

/-- `φ(x) = x ln x − x + 1 ≥ 0` on `ℝ₊`, as the book requires of a divergence index. -/
theorem aa_klPhi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ aa_klPhi x := by
  unfold aa_klPhi
  rcases hx.lt_or_eq with hx | hx
  · have h := Real.one_sub_inv_le_log_of_pos hx
    have : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left h hx.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at this
    linarith
  · subst hx
    simp

/-- `φ(t)/t → ∞` for the relative-entropy index. -/
theorem aa_klPhi_superlinear : Tendsto (fun t => aa_klPhi t / t) atTop atTop := by
  have h : Tendsto (fun t : ℝ => Real.log t - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) Real.tendsto_log_atTop |>.congr fun t => by ring
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [aa_klPhi, le_div_iff₀ ht]
  nlinarith

/-- Miao, p. 695: for `φ(x) = x ln x − x + 1`, `w = 1` and a reference model `p` with full support,
`D_φ¹(q‖p) = ∫ ln(dq/dp) dq`, the relative entropy (Kullback–Leibler divergence). -/
theorem aa_phiDiv_kl {p q : S → ℝ} (hp : SS.IsDistribution p) (hpos : ∀ s, 0 < p s)
    (hq : SS.IsDistribution q) : aa_phiDiv aa_klPhi (fun _ => 1) p q = SS.klDiv q p := by
  unfold aa_phiDiv aa_klPhi SS.klDiv
  have e : ∀ s, 1 * (q s / p s * Real.log (q s / p s) - q s / p s + 1) * p s =
      q s * Real.log (q s / p s) - q s + p s := fun s => by
    field_simp [(hpos s).ne']
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one]
  ring

/-- **Multiplier utility solves to risk-sensitive utility** (Miao, p. 695; Hansen and Sargent):
for `θ > 0`, `min_{q ≪ p} {∫ u dq + θ ∫ ln(dq/dp) dq} = −θ ln ∫ exp(−u/θ) dp`, the minimum being
attained. -/
theorem aa_multiplier_isLeast {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (u : S → ℝ) :
    IsLeast {y | ∃ q, SS.IsDistribution q ∧ SS.AbsCont q p ∧ y = aa_E q u + θ * SS.klDiv q p}
      (-θ * Real.log (∑ s, p s * Real.exp (-u s / θ))) := by
  have key := SS.entropic_isLeast (θ := -θ⁻¹) (by simpa using hθ) hp u
  have e1 : (-θ⁻¹)⁻¹ = -θ := by rw [inv_neg, inv_inv]
  rw [e1] at key
  have e2 : (∑ x, Real.exp (-θ⁻¹ * u x) * p x) = ∑ s, p s * Real.exp (-u s / θ) :=
    Finset.sum_congr rfl fun s _ => by rw [mul_comm]; congr 2; field_simp
  rw [e2] at key
  convert key using 2
  ext y
  simp only [aa_E]
  constructor
  · rintro ⟨q, hq, hac, rfl⟩
    exact ⟨q, hq, hac, by rw [Finset.sum_congr rfl fun s _ => mul_comm (q s) (u s)]; ring⟩
  · rintro ⟨q, hq, hac, rfl⟩
    exact ⟨q, hq, hac, by rw [Finset.sum_congr rfl fun s _ => mul_comm (q s) (u s)]; ring⟩

/-- Miao, p. 695: with a full-support reference model, divergence utility with relative entropy
and `w = 1` over all of `Δ(S)` equals the risk-sensitive utility `−θ ln ∫ exp(−u/θ) dp`. -/
theorem aa_divU_kl {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (u : S → ℝ) :
    aa_divU aa_klPhi (fun _ => 1) p θ (aa_Δ S) u =
      -θ * Real.log (∑ s, p s * Real.exp (-u s / θ)) := by
  refine IsLeast.csInf_eq ?_
  have h := aa_multiplier_isLeast hθ hp u
  have hset : ((fun q => aa_E q u + θ * aa_phiDiv aa_klPhi (fun _ => 1) p q) '' aa_Δ S) =
      {y | ∃ q, SS.IsDistribution q ∧ SS.AbsCont q p ∧ y = aa_E q u + θ * SS.klDiv q p} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, fun s hs => absurd hs (hpos s).ne', by dsimp only; rw [aa_phiDiv_kl hp hpos hq]⟩
    · rintro ⟨q, hq, -, rfl⟩
      exact ⟨q, hq, by dsimp only; rw [aa_phiDiv_kl hp hpos hq]⟩
  rwa [hset]

/-- Miao, p. 694: "when `θ` goes to infinity, the model reduces to expected utility":
`−θ ln ∫ exp(−u/θ) dp → ∫ u dp` as `θ → ∞`. -/
theorem aa_riskSensitive_tendsto {p : S → ℝ} (hp : SS.IsDistribution p) (u : S → ℝ) :
    Tendsto (fun θ => -θ * Real.log (∑ s, p s * Real.exp (-u s / θ))) atTop (𝓝 (aa_E p u)) := by
  have h1 := aa_tendsto_logmgf hp (fun s => -u s)
  have h2 : Tendsto (fun θ : ℝ => θ⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_mono_right (fun x hx => ne_of_gt hx) tendsto_inv_atTop_nhdsGT_zero
  have h3 := (h1.comp h2).neg
  have hE : -aa_E p (fun s => -u s) = aa_E p u := by
    simp [aa_E, Finset.sum_neg_distrib]
  rw [hE] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  have e : ∀ s, θ⁻¹ * -u s = -u s / θ := fun s => by ring
  simp only [Function.comp_apply, inv_inv, e]
  ring

/-- The exponential utility `u(x) = −exp(−x/θ)`. -/
noncomputable def aa_expU (θ x : ℝ) : ℝ := -Real.exp (-x / θ)

/-- Miao, p. 695: risk-sensitive utility is the certainty equivalent of the exponential utility,
`u(−θ ln E exp(−x/θ)) = E u(x)`. -/
theorem aa_riskSensitive_eq_ce {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    [Nonempty S] (x : S → ℝ) :
    aa_expU θ (-θ * Real.log (∑ s, p s * Real.exp (-x s / θ))) =
      aa_E p fun s => aa_expU θ (x s) := by
  have hpos : 0 < ∑ s, p s * Real.exp (-x s / θ) := aa_E_pos hp fun s => Real.exp_pos _
  unfold aa_expU
  rw [show -(-θ * Real.log (∑ s, p s * Real.exp (-x s / θ))) / θ =
    Real.log (∑ s, p s * Real.exp (-x s / θ)) by field_simp, Real.exp_log hpos]
  simp [aa_E, Finset.sum_neg_distrib]

/-- Miao, p. 695: "concern for robustness enhances risk aversion by `1/θ`": the exponential
utility has `u'(x) = θ⁻¹e^{−x/θ}`, `u''(x) = −θ⁻²e^{−x/θ}`, so absolute risk aversion
`−u''/u' = 1/θ`. -/
theorem aa_expU_arrowPratt {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (aa_expU θ) (θ⁻¹ * Real.exp (-x / θ)) x ∧
      HasDerivAt (fun y => θ⁻¹ * Real.exp (-y / θ)) (-θ⁻¹ * (θ⁻¹ * Real.exp (-x / θ))) x ∧
      -(-θ⁻¹ * (θ⁻¹ * Real.exp (-x / θ))) / (θ⁻¹ * Real.exp (-x / θ)) = θ⁻¹ := by
  have hd : HasDerivAt (fun y : ℝ => -y / θ) (-1 / θ) x := by
    simpa using ((hasDerivAt_id x).neg.div_const θ)
  refine ⟨?_, ?_, ?_⟩
  · have e : aa_expU θ = fun y => -Real.exp (-y / θ) := rfl
    rw [e]
    convert hd.exp.neg using 1
    field_simp
  · have := hd.exp.const_mul θ⁻¹
    convert this using 1
    field_simp
  · have : Real.exp (-x / θ) ≠ 0 := (Real.exp_pos _).ne'
    field_simp

/-! ### The relative Gini concentration index and monotone mean–variance utility -/

/-- The relative Gini concentration index (`χ²` divergence) `φ(x) = (x − 1)²/2` (Miao, p. 695). -/
noncomputable def aa_chiPhi (x : ℝ) : ℝ := (x - 1) ^ 2 / 2

theorem aa_chiPhi_one : aa_chiPhi 1 = 0 := by simp [aa_chiPhi]

theorem aa_chiPhi_nonneg (x : ℝ) : 0 ≤ aa_chiPhi x := by unfold aa_chiPhi; positivity

/-- `φ(t)/t → ∞` for the Gini index. -/
theorem aa_chiPhi_superlinear : Tendsto (fun t => aa_chiPhi t / t) atTop atTop := by
  have h0 : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
  have h : Tendsto (fun t : ℝ => t / 2 + -1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ (-1) h0
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [aa_chiPhi, le_div_iff₀ ht]
  nlinarith

/-- The variance `Var_p(x) = E_p (x − E_p x)²`. -/
noncomputable def aa_Var (p x : S → ℝ) : ℝ := aa_E p fun s => (x s - aa_E p x) ^ 2

/-- The completed square behind the monotone mean–variance formula: for every distribution `q`,
`E_q x + θD_χ²(q‖p) = E_p x − Var_p(x)/(2θ) + ∑ p (θ/2)(q/p − 1 + (x − E_p x)/θ)²`. -/
theorem aa_chi2_identity {θ : ℝ} (hθ : 0 < θ) {p q : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (hq : SS.IsDistribution q) (x : S → ℝ) :
    aa_E q x + θ * aa_phiDiv aa_chiPhi (fun _ => 1) p q =
      aa_E p x - aa_Var p x / (2 * θ) +
        ∑ s, p s * (θ / 2 * (q s / p s - 1 + (x s - aa_E p x) / θ) ^ 2) := by
  set m := aa_E p x with hm
  have hterm : ∀ s, q s * x s + θ * (1 * aa_chiPhi (q s / p s) * p s) =
      p s * x s - p s * (x s - m) ^ 2 / (2 * θ) +
        p s * (θ / 2 * (q s / p s - 1 + (x s - m) / θ) ^ 2) + m * (q s - p s) := fun s => by
    unfold aa_chiPhi
    field_simp [(hpos s).ne']
    ring
  have hsum : ∑ s, m * (q s - p s) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one, sub_self, mul_zero]
  unfold aa_E aa_phiDiv aa_Var
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun s _ => hterm s,
    Finset.sum_add_distrib, hsum, add_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div]
  rfl

/-- **Monotone mean–variance utility** (Miao, pp. 695–696; Maccheroni, Marinacci and Rustichini
(2006a)). For `φ(x) = (x − 1)²/2`, `w = 1`, `θ > 0` and a full-support reference model `p`, on the
domain `c − E c ≤ θ` divergence utility with `u(c) = c` is `E c − Var(c)/(2θ)`, attained at the
density `dq*/dp = 1 − (c − E c)/θ`. -/
theorem aa_chi2_mmv {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (c : S → ℝ) (hdom : ∀ s, c s - aa_E p c ≤ θ) :
    IsLeast ((fun q => aa_E q c + θ * aa_phiDiv aa_chiPhi (fun _ => 1) p q) '' aa_Δ S)
      (aa_E p c - aa_Var p c / (2 * θ)) := by
  set qs : S → ℝ := fun s => p s * (1 - (c s - aa_E p c) / θ) with hqs
  have hqsD : SS.IsDistribution qs := by
    refine ⟨fun s => mul_nonneg (hp.nonneg s) ?_, ?_⟩
    · rw [sub_nonneg, div_le_one hθ]
      exact hdom s
    · have h1 : ∑ s, p s * (c s - aa_E p c) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_eq_one, one_mul]
        unfold aa_E
        ring
      have h2 : ∑ s, qs s = ∑ s, p s - (∑ s, p s * (c s - aa_E p c)) / θ := by
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by simp only [hqs]; ring
      rw [h2, h1, hp.sum_eq_one]
      simp
  refine ⟨⟨qs, hqsD, ?_⟩, ?_⟩
  · dsimp only
    rw [aa_chi2_identity hθ hp hpos hqsD c]
    have h0 : ∀ s, p s * (θ / 2 * (qs s / p s - 1 + (c s - aa_E p c) / θ) ^ 2) = 0 := fun s => by
      simp only [hqs]
      rw [mul_div_cancel_left₀ _ (hpos s).ne']
      ring
    simp [h0]
  · rintro _ ⟨q, hq, rfl⟩
    dsimp only
    rw [aa_chi2_identity hθ hp hpos hq c]
    have : 0 ≤ ∑ s, p s * (θ / 2 * (q s / p s - 1 + (c s - aa_E p c) / θ) ^ 2) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (hp.nonneg s) (by positivity)
    linarith

end Miao.RecursiveUtility
