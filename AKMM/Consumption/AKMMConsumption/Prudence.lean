/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Precautionary saving

AKMM, §11.3.4, pp. 304–309: the precautionary motive with borrowing constraints, (11.34), and
with prudence, (11.35)–(11.40), with footnotes 17–19.

A mean-preserving spread is stated as the **convex order** (`pr_ConvexOrderOn Y μ ν`: both laws
live on `Y` and `∫φ dμ ≤ ∫φ dν` for every `φ` convex on `Y` that both integrate). By
Rothschild–Stiglitz (the book's fn. 17) this is the MPS order for distributions with the same
mean; the characterisation itself is not proved. Two-point spreads are an instance
(`pr_two_point_spread`), and the convex order preserves the mean (`pr_convexOrder_mean`).

* **(11.34)** a spread in next-period income lowers `Eₜ min{yₜ₊₁ + aₜ₊₁ + a/R, Eₜ₊₁cₜ₊₂}`
  (`eq_11_34_spread`).
* **(11.35)** the Euler equation `u′(y₀ − a₁) = βRE₀u′(Ra₁ + y₁)` has at most one root
  (`eq_11_35_unique`); the comparative-statics step (`pr_root_mono`); with `u′` convex, a
  mean-preserving spread of `y₁` raises saving (`pr_spread_raises_saving`); for a two-point
  spread saving rises iff `u′` is midpoint convex at the old `c₁` (`pr_two_point_iff`); with
  quadratic utility a spread leaves the Euler equation unchanged (`pr_quadratic_no_precaution`).
* **DARA ⇒ prudence** (p. 307): `α′ = (−u‴u′ + (u″)²)/(u′)²` (`pr_ara_deriv`), and `α′ < 0`
  gives `u‴ > (u″)²/u′ > 0` (`pr_dara_prudent`).
* **(11.36)** (Blanchard–Mankiw) holds exactly when `u′` is quadratic on the support, with
  `r − ρ` replaced by `(r − ρ)/(1 + r) = 1 − (βR)⁻¹` (`eq_11_36_exact`, `pr_betaR_inv`).
* **(11.37)–(11.40)** differentiating the envelope condition: `c′ = V″/u″ > 0` (`eq_11_38`),
  `c″` (`eq_11_39`), and `c″ ≤ 0` iff `V‴V′/(V″)² ≥ u‴u′/(u″)²` (`eq_11_40`).
* **Footnote 19, HARA:** the risk tolerance `T = −u′/u″` has `T′ = κ − 1`, `κ = u‴u′/(u″)²`
  (`pr_tolerance_deriv`), so `T` affine gives `κ` constant (`pr_hara_kappa_const`); quadratic
  `κ = 0`, CARA `κ = 1`, CRRA `κ = (σ + 1)/σ > 1` (`pr_kappa_quadratic`, `pr_kappa_cara`,
  `pr_kappa_crra`). **Correction:** `κ ≥ 0` needs prudence: the HARA marginal utility
  `√(1 − 2c)` has `κ = −1` (`pr_hara_kappa_neg`).
-/

namespace AKMM.Consumption

open MeasureTheory Filter Topology

/-! ### The convex order -/

/-- AKMM, p. 306 and fn. 17: `ν` is a mean-preserving spread of `μ` on `Y`, as the convex order:
both laws live on `Y`, and `∫φ dμ ≤ ∫φ dν` for every `φ` convex on `Y` integrable under both. -/
def pr_ConvexOrderOn (Y : Set ℝ) (μ ν : Measure ℝ) : Prop :=
  (∀ᵐ y ∂μ, y ∈ Y) ∧ (∀ᵐ y ∂ν, y ∈ Y) ∧
    ∀ φ : ℝ → ℝ, ConvexOn ℝ Y φ → Integrable φ μ → Integrable φ ν → ∫ y, φ y ∂μ ≤ ∫ y, φ y ∂ν

/-- The convex order preserves the mean (apply it to `y` and `−y`). -/
theorem pr_convexOrder_mean {Y : Set ℝ} (hY : Convex ℝ Y) {μ ν : Measure ℝ}
    (h : pr_ConvexOrderOn Y μ ν) (hμ : Integrable (fun y => y) μ)
    (hν : Integrable (fun y => y) ν) : ∫ y, y ∂μ = ∫ y, y ∂ν := by
  have h1 := h.2.2 (fun y => y) (convexOn_id hY) hμ hν
  have h2 := h.2.2 (fun y => -y) (concaveOn_id hY).neg hμ.neg hν.neg
  rw [integral_neg, integral_neg] at h2
  linarith

/-- A two-point mean-preserving spread: `δₘ` is below `½δ_{m−h} + ½δ_{m+h}` in the convex order on
any convex `Y` containing `m ± h` (Jensen). This is the instance behind fn. 17. -/
theorem pr_two_point_spread {Y : Set ℝ} {m h : ℝ} (hY : Convex ℝ Y) (h1 : m - h ∈ Y)
    (h2 : m + h ∈ Y) :
    pr_ConvexOrderOn Y (Measure.dirac m)
      ((1 / 2 : ENNReal) • Measure.dirac (m - h) + (1 / 2 : ENNReal) • Measure.dirac (m + h)) := by
  have hm : m ∈ Y := by
    have := hY h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1; ring
  refine ⟨by rw [ae_dirac_eq]; exact hm, ?_, fun φ hφ _ hν => ?_⟩
  · rw [ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h1) _,
      Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h2) _⟩
  · rw [integral_add_measure (hν.mono_measure (Measure.le_add_right le_rfl))
      (hν.mono_measure (Measure.le_add_left le_rfl)), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, integral_dirac]
    have := hφ.2 h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • (m - h) + (1 / 2 : ℝ) • (m + h) = m := by simp only [smul_eq_mul]; ring
    rw [e] at this
    simp only [smul_eq_mul] at this ⊢
    norm_num at this ⊢
    linarith

/-! ### Borrowing constraints: (11.34) -/

/-- **AKMM, (11.34), p. 305.** `y ↦ min{y + A, K}` is concave, so a mean-preserving spread of
next-period income lowers `E min{yₜ₊₁ + aₜ₊₁ + a/R, Eₜ₊₁cₜ₊₂}` (with `A = aₜ₊₁ + a/R` and
`K = Eₜ₊₁cₜ₊₂` held fixed): consumption today falls and saving rises. -/
theorem eq_11_34_spread {Y : Set ℝ} (hY : Convex ℝ Y) {μ ν : Measure ℝ}
    (h : pr_ConvexOrderOn Y μ ν) (A K : ℝ) (hμ : Integrable (fun y => min (y + A) K) μ)
    (hν : Integrable (fun y => min (y + A) K) ν) :
    ∫ y, min (y + A) K ∂ν ≤ ∫ y, min (y + A) K ∂μ := by
  have hconc : ConcaveOn ℝ Y fun y => min (y + A) K :=
    ((concaveOn_id hY).add_const A).inf (concaveOn_const K hY)
  have := h.2.2 _ hconc.neg hμ.neg hν.neg
  simp only [Pi.neg_apply] at this
  rw [integral_neg, integral_neg] at this
  linarith

/-! ### Prudence: the two-period problem (11.35) -/

/-- **AKMM, (11.35), p. 306: "the solution for `a₁` is uniquely determined".** If the left side
`F` is strictly increasing and the right side `G` antitone (on a set `S`), the Euler equation
`F(a₁) = G(a₁)` has at most one root in `S`. -/
theorem eq_11_35_unique {S : Set ℝ} {F G : ℝ → ℝ} (hF : StrictMonoOn F S) (hG : AntitoneOn G S)
    {a a' : ℝ} (ha : a ∈ S) (ha' : a' ∈ S) (h : F a = G a) (h' : F a' = G a') : a = a' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hF ha ha' hlt; have := hG ha ha' hlt.le; linarith
  · have := hF ha' ha hlt; have := hG ha' ha hlt.le; linarith

/-- AKMM, p. 306 (Figure 11.3): the comparative statics of (11.35). The left side `F` is strictly
increasing; the new right side `G₂` is antitone and lies above the old one at the old root `a₁`.
Then the new root `a₂` is at least `a₁`. -/
theorem pr_root_mono {F G₁ G₂ : ℝ → ℝ} {a₁ a₂ : ℝ}
    (hG₂ : a₂ < a₁ → G₂ a₁ ≤ G₂ a₂) (h₁ : F a₁ = G₁ a₁) (h₂ : F a₂ = G₂ a₂)
    (hup : G₁ a₁ ≤ G₂ a₁) (hFmono : a₂ < a₁ → F a₂ < F a₁) : a₁ ≤ a₂ := by
  by_contra hlt
  push Not at hlt
  have := hFmono hlt
  have := hG₂ hlt
  linarith

/-- The right side of (11.35), `βRE u′(Ra₁ + y₁)` under the law `μ` of `y₁`. -/
noncomputable def pr_rhs (du : ℝ → ℝ) (β R : ℝ) (μ : Measure ℝ) (a : ℝ) : ℝ :=
  β * R * ∫ y, du (R * a + y) ∂μ

/-- **AKMM, p. 306: prudence and precautionary saving.** Let `u′` be strictly decreasing and
convex on `(0, ∞)`, `β, R > 0`, and let the law `ν` of `y₁` be a mean-preserving spread of `μ`
on the convex set `Y` (convex order). If `a₁` solves (11.35) under `μ`, `a₂` solves it under `ν`,
and both plans have positive consumption (`y₀ − aᵢ > 0`, `Raᵢ + y > 0` on `Y`), then `a₂ ≥ a₁`:
the spread raises saving. -/
theorem pr_spread_raises_saving {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0))
    (hconv : ConvexOn ℝ (Set.Ioi 0) du) {β R y₀ a₁ a₂ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    {Y : Set ℝ} (hY : Convex ℝ Y) {μ ν : Measure ℝ} (hspread : pr_ConvexOrderOn Y μ ν)
    (hc₀₁ : 0 < y₀ - a₁) (hc₀₂ : 0 < y₀ - a₂) (hc₁ : ∀ y ∈ Y, 0 < R * a₁ + y)
    (hc₂ : ∀ y ∈ Y, 0 < R * a₂ + y)
    (hμ₁ : Integrable (fun y => du (R * a₁ + y)) μ) (hν₁ : Integrable (fun y => du (R * a₁ + y)) ν)
    (hν₂ : Integrable (fun y => du (R * a₂ + y)) ν)
    (h₁ : du (y₀ - a₁) = pr_rhs du β R μ a₁) (h₂ : du (y₀ - a₂) = pr_rhs du β R ν a₂) :
    a₁ ≤ a₂ := by
  -- `y ↦ u′(Ra₁ + y)` is convex on `Y`
  have hφ : ConvexOn ℝ Y fun y => du (R * a₁ + y) := by
    refine ⟨hY, fun x hx z hz s t hs ht hst => ?_⟩
    have e : R * a₁ + (s • x + t • z) = s • (R * a₁ + x) + t • (R * a₁ + z) := by
      simp only [smul_eq_mul]
      linear_combination (-(R * a₁)) * hst
    simp only [e]
    exact hconv.2 (hc₁ x hx) (hc₁ z hz) hs ht hst
  have hup : pr_rhs du β R μ a₁ ≤ pr_rhs du β R ν a₁ := by
    unfold pr_rhs
    exact mul_le_mul_of_nonneg_left (hspread.2.2 _ hφ hμ₁ hν₁) (mul_pos hβ hR).le
  by_contra hlt
  push Not at hlt
  -- the left side is strictly increasing in `a`
  have hF : du (y₀ - a₂) < du (y₀ - a₁) :=
    hdu hc₀₁ hc₀₂ (by linarith)
  -- the right side under `ν` is antitone in `a`
  have hG : pr_rhs du β R ν a₁ ≤ pr_rhs du β R ν a₂ := by
    unfold pr_rhs
    refine mul_le_mul_of_nonneg_left (integral_mono_ae hν₁ hν₂ ?_) (mul_pos hβ hR).le
    filter_upwards [hspread.2.1] with y hy
    exact (hdu.antitoneOn (hc₂ y hy) (hc₁ y hy) (by nlinarith))
  linarith

/-- **AKMM, p. 306: "if `u′` is convex then … the right-hand side will increase", and
conversely.** For the two-point spread of a sure income `m` into `m ± h`, with roots `a₁` (sure
income) and `a₂` (spread) of (11.35) and positive consumption in both plans: saving weakly rises
iff `u′` is midpoint convex at the old second-period consumption `x = Ra₁ + m`,
`u′(x) ≤ (u′(x − h) + u′(x + h))/2`. -/
theorem pr_two_point_iff {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0)) {β R y₀ m h a₁ a₂ : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hc₀₁ : 0 < y₀ - a₁) (hc₀₂ : 0 < y₀ - a₂)
    (hlo₁ : 0 < R * a₁ + (m - h)) (hlo₂ : 0 < R * a₂ + (m - h)) (hh : 0 ≤ h)
    (h₁ : du (y₀ - a₁) = β * R * du (R * a₁ + m))
    (h₂ : du (y₀ - a₂) = β * R * ((du (R * a₂ + (m - h)) + du (R * a₂ + (m + h))) / 2)) :
    a₁ ≤ a₂ ↔ du (R * a₁ + m) ≤ (du (R * a₁ + m - h) + du (R * a₁ + m + h)) / 2 := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hG : ∀ {a a' : ℝ}, 0 < R * a + (m - h) → a ≤ a' →
      (du (R * a' + (m - h)) + du (R * a' + (m + h))) / 2 ≤
        (du (R * a + (m - h)) + du (R * a + (m + h))) / 2 := by
    intro a a' ha haa
    have h1 : du (R * a' + (m - h)) ≤ du (R * a + (m - h)) :=
      hdu.antitoneOn (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (by nlinarith)) (by nlinarith)
    have h2 : du (R * a' + (m + h)) ≤ du (R * a + (m + h)) :=
      hdu.antitoneOn (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (by nlinarith)) (by nlinarith)
    linarith
  have e1 : R * a₁ + m - h = R * a₁ + (m - h) := by ring
  have e2 : R * a₁ + m + h = R * a₁ + (m + h) := by ring
  rw [e1, e2]
  constructor
  · intro hle
    -- `F(a₁) ≤ F(a₂) = G₂(a₂) ≤ G₂(a₁)`
    have hF : du (y₀ - a₁) ≤ du (y₀ - a₂) :=
      hdu.antitoneOn (Set.mem_Ioi.2 hc₀₂) (Set.mem_Ioi.2 hc₀₁) (by linarith)
    have := hG hlo₁ hle
    have : β * R * du (R * a₁ + m) ≤
        β * R * ((du (R * a₁ + (m - h)) + du (R * a₁ + (m + h))) / 2) := by
      rw [← h₁]; calc du (y₀ - a₁) ≤ du (y₀ - a₂) := hF
        _ = _ := h₂
        _ ≤ _ := mul_le_mul_of_nonneg_left this hβR.le
    exact le_of_mul_le_mul_left this hβR
  · intro hconv
    by_contra hlt
    push Not at hlt
    have hF : du (y₀ - a₂) < du (y₀ - a₁) := hdu (Set.mem_Ioi.2 hc₀₁) (Set.mem_Ioi.2 hc₀₂)
      (by linarith)
    have := hG hlo₂ hlt.le
    have := mul_le_mul_of_nonneg_left hconv hβR.le
    have := mul_le_mul_of_nonneg_left (hG hlo₂ hlt.le) hβR.le
    linarith

/-- **AKMM, p. 304: no precautionary saving with quadratic utility.** If `u′(c) = b₁ − b₂c`, the
right side of (11.35) depends on the law of `y₁` only through its mean, so a mean-preserving
spread (convex order) leaves the Euler equation, and hence saving, unchanged. -/
theorem pr_quadratic_no_precaution {b₁ b₂ β R a : ℝ} {Y : Set ℝ} (hY : Convex ℝ Y)
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hspread : pr_ConvexOrderOn Y μ ν) (hμ : Integrable (fun y => y) μ)
    (hν : Integrable (fun y => y) ν) :
    pr_rhs (fun c => b₁ - b₂ * c) β R μ a = pr_rhs (fun c => b₁ - b₂ * c) β R ν a := by
  have hm := pr_convexOrder_mean hY hspread hμ hν
  unfold pr_rhs
  have hint : ∀ ρ : Measure ℝ, [IsProbabilityMeasure ρ] → Integrable (fun y => y) ρ →
      ∫ y, b₁ - b₂ * (R * a + y) ∂ρ = b₁ - b₂ * (R * a + ∫ y, y ∂ρ) := by
    intro ρ _ hρ
    have h1 : Integrable (fun y => b₂ * (R * a + y)) ρ :=
      ((integrable_const (R * a)).add hρ).const_mul b₂
    rw [integral_sub (integrable_const b₁) h1, integral_const, integral_const_mul,
      integral_add (integrable_const _) hρ, integral_const]
    simp
  rw [hint μ hμ, hint ν hν, hm]

/-! ### DARA implies prudence -/

/-- **AKMM, p. 307.** The coefficient of absolute risk aversion `α = −u″/u′` has derivative
`α′ = (−u‴u′ + (u″)²)/(u′)²`. -/
theorem pr_ara_deriv {u1 u2 : ℝ → ℝ} {c u3c : ℝ} (h1 : HasDerivAt u1 (u2 c) c)
    (h2 : HasDerivAt u2 u3c c) (hne : u1 c ≠ 0) :
    HasDerivAt (fun x => -u2 x / u1 x) ((-u3c * u1 c + u2 c ^ 2) / u1 c ^ 2) c := by
  have := h2.neg.div h1 hne
  convert this using 1
  simp only [Pi.neg_apply]
  ring

/-- **AKMM, p. 307: DARA implies prudence.** If `u′ > 0`, `u″ ≠ 0` and absolute risk aversion is
strictly decreasing at `c` (`α′(c) < 0`), then `u‴(c) > (u″(c))²/u′(c) > 0`. -/
theorem pr_dara_prudent {u1c u2c u3c : ℝ} (h1 : 0 < u1c) (h2 : u2c ≠ 0)
    (hdara : (-u3c * u1c + u2c ^ 2) / u1c ^ 2 < 0) : u2c ^ 2 / u1c < u3c ∧ 0 < u2c ^ 2 / u1c := by
  have hpos : 0 < u1c ^ 2 := by positivity
  rw [div_lt_iff₀ hpos, zero_mul] at hdara
  refine ⟨?_, div_pos (by positivity) h1⟩
  rw [div_lt_iff₀ h1]
  linarith

/-! ### Blanchard–Mankiw (11.36) -/

/-- AKMM, p. 308: with `β = 1/(1 + ρ)`, `1 − (βR)⁻¹ = (r − ρ)/(1 + r)` exactly; the book uses
`(βR)⁻¹ ≃ 1 + ρ − r`. -/
theorem pr_betaR_inv {r ρ : ℝ} (hr : 0 < 1 + r) :
    1 - (1 / (1 + ρ) * (1 + r))⁻¹ = (r - ρ) / (1 + r) := by
  field_simp
  ring

/-- **AKMM, (11.36), p. 308 (Blanchard and Mankiw 1988), exact version.** Let next-period
consumption take the values `c′ₖ` with probabilities `pₖ` (summing to `1`), and let `u′` be
quadratic on the support: `u′(c′ₖ) = u′(c) + u″(c)(c′ₖ − c) + ½u‴(c)(c′ₖ − c)²` (cubic `u`).
Then the Euler equation `u′(c) = βREu′(c′)` gives
`E[(c′ − c)/c] = EIS(c)(1 − (βR)⁻¹) + ½P(c)E[((c′ − c)/c)²]` with `EIS = −u′/(cu″)` and
`P = −u‴c/u″`. -/
theorem eq_11_36_exact {ι : Type*} [Fintype ι] {p c' : ι → ℝ} (hp : ∑ k, p k = 1)
    {c u1c u2c u3c βR : ℝ} (hc : 0 < c) (hu2 : u2c ≠ 0) (hβR : 0 < βR) {du : ℝ → ℝ}
    (htaylor : ∀ k, du (c' k) = u1c + u2c * (c' k - c) + 1 / 2 * u3c * (c' k - c) ^ 2)
    (heuler : u1c = βR * ∑ k, p k * du (c' k)) :
    ∑ k, p k * ((c' k - c) / c) =
      (-u1c / (c * u2c)) * (1 - βR⁻¹) +
        1 / 2 * (-u3c * c / u2c) * ∑ k, p k * ((c' k - c) / c) ^ 2 := by
  have hm1 : ∑ k, p k * ((c' k - c) / c) = (∑ k, p k * c' k - c) / c := by
    rw [eq_div_iff hc.ne', Finset.sum_mul]
    have : ∀ k, p k * ((c' k - c) / c) * c = p k * c' k - p k * c := fun k => by
      field_simp
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  have hm2 : ∑ k, p k * ((c' k - c) / c) ^ 2 = (∑ k, p k * (c' k - c) ^ 2) / c ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by rw [div_pow]; ring
  have hEdu : ∑ k, p k * du (c' k) = u1c + u2c * (∑ k, p k * c' k - c) +
      1 / 2 * u3c * ∑ k, p k * (c' k - c) ^ 2 := by
    simp_rw [htaylor]
    have : ∀ k, p k * (u1c + u2c * (c' k - c) + 1 / 2 * u3c * (c' k - c) ^ 2) =
        u1c * p k + u2c * (p k * c' k) - u2c * c * p k + 1 / 2 * u3c * (p k * (c' k - c) ^ 2) :=
      fun k => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hp]
    ring
  rw [hm1, hm2]
  rw [hEdu] at heuler
  generalize ∑ k, p k * c' k = m1 at heuler ⊢
  generalize ∑ k, p k * (c' k - c) ^ 2 = M2 at heuler ⊢
  have hm : m1 - c = (u1c * βR⁻¹ - u1c - 1 / 2 * u3c * M2) / u2c := by
    rw [eq_div_iff hu2]
    have : u1c * βR⁻¹ = u1c + u2c * (m1 - c) + 1 / 2 * u3c * M2 :=
      calc u1c * βR⁻¹ = βR * (u1c + u2c * (m1 - c) + 1 / 2 * u3c * M2) * βR⁻¹ := by
            rw [← heuler]
        _ = u1c + u2c * (m1 - c) + 1 / 2 * u3c * M2 := by field_simp
    linarith
  rw [hm]
  field_simp
  ring

/-! ### Concavity of the consumption function: (11.37)–(11.40) -/

/-- **AKMM, (11.38), p. 308.** If the envelope condition (11.37) `u′(c(a)) = V′(a)` holds near
`a`, `c` is differentiable at `a`, `u′` has derivative `u″` at `c(a)` and `V′` has derivative
`V″(a)`, then `c′(a) = V″(a)/u″(c(a))`; with `V″ < 0` and `u″ < 0`, `c′(a) > 0`. -/
theorem eq_11_38 {u1 V1 c : ℝ → ℝ} {a c1 u2c V2a : ℝ}
    (henv : ∀ᶠ x in 𝓝 a, u1 (c x) = V1 x) (hc : HasDerivAt c c1 a)
    (hu : HasDerivAt u1 u2c (c a)) (hV : HasDerivAt V1 V2a a) (hu2 : u2c < 0) (hV2 : V2a < 0) :
    c1 = V2a / u2c ∧ 0 < c1 := by
  have h1 : HasDerivAt (fun x => u1 (c x)) (u2c * c1) a := hu.comp a hc
  have h2 : HasDerivAt (fun x => u1 (c x)) V2a a := hV.congr_of_eventuallyEq henv
  have e := h1.unique h2
  have hc1 : c1 = V2a / u2c := by rw [eq_div_iff hu2.ne]; linarith
  exact ⟨hc1, by rw [hc1]; exact div_pos_of_neg_of_neg hV2 hu2⟩

/-- **AKMM, (11.39), p. 308.** Differentiating `c′(a) = V″(a)/u″(c(a))`:
`c″(a) = (V‴(a)u″(c(a)) − V″(a)u‴(c(a))c′(a))/[u″(c(a))]²`. -/
theorem eq_11_39 {u2 V2 c : ℝ → ℝ} {a c1 u3c V3a : ℝ} (hc : HasDerivAt c c1 a)
    (hu : HasDerivAt u2 u3c (c a)) (hV : HasDerivAt V2 V3a a) (hne : u2 (c a) ≠ 0) :
    HasDerivAt (fun x => V2 x / u2 (c x))
      ((V3a * u2 (c a) - V2 a * (u3c * c1)) / u2 (c a) ^ 2) a :=
  hV.div (hu.comp a hc) hne

/-- **AKMM, (11.40), p. 309 (Carroll and Kimball 1996, Lemma 2).** With the envelope condition
`V′(a) = u′(c(a)) > 0`, `c′ = V″/u″`, `u″ < 0` and `V″ ≠ 0`: the expression (11.39) for `c″` is
`≤ 0` iff `V‴V′/(V″)² ≥ u‴u′/(u″)²`. -/
theorem eq_11_40 {V1a V2a V3a u1c u2c u3c c1 : ℝ} (henv : V1a = u1c) (hu1 : 0 < u1c)
    (hu2 : u2c < 0) (hV2 : V2a ≠ 0) (hc1 : c1 = V2a / u2c) :
    (V3a * u2c - V2a * (u3c * c1)) / u2c ^ 2 ≤ 0 ↔
      u3c * u1c / u2c ^ 2 ≤ V3a * V1a / V2a ^ 2 := by
  subst henv hc1
  have hu2sq : 0 < u2c ^ 2 := by nlinarith
  have hV2sq : 0 < V2a ^ 2 := by positivity
  have h3 : u2c ^ 3 < 0 := Odd.pow_neg (by decide) hu2
  have e : (V3a * u2c - V2a * (u3c * (V2a / u2c))) / u2c ^ 2 =
      (V3a * u2c ^ 2 - u3c * V2a ^ 2) / u2c ^ 3 := by
    field_simp
  rw [e, div_nonpos_iff, div_le_div_iff₀ hu2sq hV2sq]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · nlinarith [mul_nonneg hu1.le h1]
    · exact absurd h2 (not_le.2 h3)
  · intro h
    left
    refine ⟨?_, h3.le⟩
    by_contra hD
    push Not at hD
    nlinarith [mul_neg_of_pos_of_neg hu1 hD]

/-! ### HARA and footnote 19 -/

/-- The index `κ = u‴u′/(u″)²` of (11.40) (prudence relative to risk aversion). -/
noncomputable def pr_kappa (u1c u2c u3c : ℝ) : ℝ := u3c * u1c / u2c ^ 2

/-- AKMM, p. 308 and fn. 18–19: the absolute risk tolerance `T = −u′/u″` has derivative
`T′ = κ − 1`. -/
theorem pr_tolerance_deriv {u1 u2 : ℝ → ℝ} {c u3c : ℝ} (h1 : HasDerivAt u1 (u2 c) c)
    (h2 : HasDerivAt u2 u3c c) (hne : u2 c ≠ 0) :
    HasDerivAt (fun x => -u1 x / u2 x) (pr_kappa (u1 c) (u2 c) u3c - 1) c := by
  have := h1.neg.div h2 hne
  convert this using 1
  simp only [Pi.neg_apply]
  unfold pr_kappa
  field_simp
  ring

/-- **AKMM, p. 309, fn. 18: HARA gives a constant `κ`.** If the risk tolerance is affine,
`−u′(c)/u″(c) = η + sc` on an open set `S`, then `κ = 1 + s` on `S`. -/
theorem pr_hara_kappa_const {u1 u2 u3 : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) {η s : ℝ}
    (h1 : ∀ c ∈ S, HasDerivAt u1 (u2 c) c) (h2 : ∀ c ∈ S, HasDerivAt u2 (u3 c) c)
    (hne : ∀ c ∈ S, u2 c ≠ 0) (hT : ∀ c ∈ S, -u1 c / u2 c = η + s * c) :
    ∀ c ∈ S, pr_kappa (u1 c) (u2 c) (u3 c) = 1 + s := by
  intro c hc
  have hd := pr_tolerance_deriv (h1 c hc) (h2 c hc) (hne c hc)
  have hT' : HasDerivAt (fun x => -u1 x / u2 x) s c := by
    have : HasDerivAt (fun x => η + s * x) s c := by
      simpa using ((hasDerivAt_id c).const_mul s).const_add η
    exact this.congr_of_eventuallyEq (Filter.eventually_of_mem (hS.mem_nhds hc) hT)
  have := hd.unique hT'
  linarith

/-- **AKMM, fn. 19: quadratic utility has `κ = 0`** (`u′ = b₁ − b₂c`, `u″ = −b₂`, `u‴ = 0`). -/
theorem pr_kappa_quadratic (b₁ b₂ c : ℝ) : pr_kappa (b₁ - b₂ * c) (-b₂) 0 = 0 := by
  simp [pr_kappa]

/-- **AKMM, fn. 19: CARA utility has `κ = 1`** (`u′ = e^{−θc}`, `u″ = −θe^{−θc}`,
`u‴ = θ²e^{−θc}`, `θ ≠ 0`). -/
theorem pr_kappa_cara {θ : ℝ} (hθ : θ ≠ 0) (c : ℝ) :
    pr_kappa (Real.exp (-θ * c)) (-θ * Real.exp (-θ * c)) (θ ^ 2 * Real.exp (-θ * c)) = 1 := by
  unfold pr_kappa
  have := Real.exp_pos (-θ * c)
  field_simp

/-- **AKMM, fn. 19: CRRA utility has `κ = (σ + 1)/σ > 1`** (`u′ = c^{−σ}`, `u″ = −σc^{−σ−1}`,
`u‴ = σ(σ + 1)c^{−σ−2}`, `c, σ > 0`). -/
theorem pr_kappa_crra {σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    pr_kappa (c ^ (-σ)) (-σ * c ^ (-σ - 1)) (σ * (σ + 1) * c ^ (-σ - 2)) = (σ + 1) / σ ∧
      1 < (σ + 1) / σ := by
  refine ⟨?_, by rw [lt_div_iff₀ hσ]; linarith⟩
  unfold pr_kappa
  have e1 : c ^ (-σ - 2) * c ^ (-σ) = (c ^ (-σ - 1)) ^ 2 := by
    rw [← Real.rpow_add hc, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num; ring_nf
  have hp : 0 < c ^ (-σ - 1) := Real.rpow_pos_of_pos hc _
  rw [mul_assoc, e1, mul_pow, neg_sq]
  field_simp

/-- The derivatives of the HARA marginal utility `u′(c) = (1 − 2c)^{1/2}` on `c < 1/2`
(risk tolerance `−u′/u″ = 1 − 2c`, slope `s = −2`). -/
theorem pr_hara_neg_derivs {c : ℝ} (hc : c < 1 / 2) :
    HasDerivAt (fun x : ℝ => (1 - 2 * x) ^ (1 / 2 : ℝ)) (-(1 - 2 * c) ^ (-1 / 2 : ℝ)) c ∧
      HasDerivAt (fun x : ℝ => -(1 - 2 * x) ^ (-1 / 2 : ℝ)) (-(1 - 2 * c) ^ (-3 / 2 : ℝ)) c := by
  have hpos : 0 < 1 - 2 * c := by linarith
  have hlin : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) c := by
    simpa using ((hasDerivAt_id c).const_mul 2).const_sub 1
  constructor
  · have := hlin.rpow_const (p := 1 / 2) (Or.inl hpos.ne')
    convert this using 1
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]; ring
  · have := (hlin.rpow_const (p := -1 / 2) (Or.inl hpos.ne')).neg
    convert this using 1
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num]; ring

/-- **Correction to AKMM, p. 309** ("if `u` belongs to the HARA class, then … the right hand side
of (11.40) is equal to a constant `κ ≥ 0`"). Without prudence `κ` can be negative: the HARA
marginal utility `u′(c) = (1 − 2c)^{1/2}` (`u′ > 0`, `u″ < 0` on `c < 1/2`) has `κ = −1`. -/
theorem pr_hara_kappa_neg {c : ℝ} (hc : c < 1 / 2) :
    0 < (1 - 2 * c) ^ (1 / 2 : ℝ) ∧ -(1 - 2 * c) ^ (-1 / 2 : ℝ) < 0 ∧
      pr_kappa ((1 - 2 * c) ^ (1 / 2 : ℝ)) (-(1 - 2 * c) ^ (-1 / 2 : ℝ))
        (-(1 - 2 * c) ^ (-3 / 2 : ℝ)) = -1 := by
  have hpos : 0 < 1 - 2 * c := by linarith
  refine ⟨Real.rpow_pos_of_pos hpos _, neg_neg_of_pos (Real.rpow_pos_of_pos hpos _), ?_⟩
  unfold pr_kappa
  have e : (1 - 2 * c) ^ (-3 / 2 : ℝ) * (1 - 2 * c) ^ (1 / 2 : ℝ) =
      ((1 - 2 * c) ^ (-1 / 2 : ℝ)) ^ 2 := by
    rw [← Real.rpow_add hpos, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hp : 0 < (1 - 2 * c) ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  rw [neg_mul, e, neg_sq]
  field_simp

end AKMM.Consumption
