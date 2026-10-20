/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.WelfareSecond
import EquilibriumApplications.SequenceSupport

/-!
# A one-sector model of growth under certainty: the commodity space and Assumptions 15.1–15.7

SLP §16.1, pp. 476–478. The commodity space is `S = ℓ∞` (`BddSeq ℝ`). The consumption set is
`X = ℓ∞⁺` (`gcX`), preferences are `u(x) = Σ_t βᵗ U(x_t)` (`gcU`), and the production set is
`Y = {y ≥ 0 : ∃ k ≥ 0, k₀ = k̂, k_{t+1} + y_t ≤ f(k_t)}` (`gcY`).

* `GrowthCertaintyHyp`: the restrictions on `β`, `U`, `f` (p. 476–477), with "`f` bounded"
  replaced by its correct form (see **Correction** 1): `f(k̄) = k̄ > 0` and `f(k) < k` for `k > k̄`.
* `gc_capital_le`, `gc_output_le`: feasible capital and output are bounded by
  `k_max = max {k̂, k̄}`, so `Y ⊆ ℓ∞⁺` is well defined.
* `gc_bounded_forces_full_depreciation`, `gc_bounded_counterexample` (NOTE p. 476).
* `gc_kbar_counterexample` (NOTE p. 477): boundedness does not give `k̄`.
* `gcRatio`, `gc_example_hyp`: a concrete economy satisfying `GrowthCertaintyHyp`
  (`U(c) = c/(1 + c)`, `f(k) = 2k/(1 + k)`, `β = 1/2`, `k̂ = 2`, `k̄ = 1`).
* `gc_localNonsatiation`: local nonsatiation (needed by Theorem 15.3).
* **Exercise 16.1(b)** (`ex_16_1b_assumptions`, p. 477): Assumptions 15.1–15.5 hold; 15.5 by the
  corrected interior point `gc_interior_nonempty`.
* `ex_16_1b_cheaper`: for a nonzero `φ` supporting `(x⁰, x⁰)`, `φ(x⁰) > 0 = φ(0)`, so `0` is a
  cheaper point (corrected argument).
* `ex_16_1b_manual_cheaper_counterexample`, `ex_16_1b_manual_interior_counterexample`: the two
  faulty steps of the solutions manual.
* **Exercise 16.1(c)** (`ex_16_1c_assumptions`, p. 477): Assumptions 15.6 and 15.7 hold.
* `gc_price_pos` (NOTE p. 477): every competitive equilibrium price `p_t = φ(e_t)` is positive, so
  the interest rates `r_t` (`gcRate`, `1/(1 + r_t) = p_{t+1}/p_t`) are well defined;
  `gc_discount_prod` and `gc_budget_iff`: the budget constraint in interest-rate form.

**Corrections.**
1. (p. 476) With `F ≥ 0`, `f(k) = F(k, 1) + (1 − δ)k ≥ (1 − δ)k` is unbounded unless `δ = 1`
   (`gc_bounded_forces_full_depreciation`; for `δ = 1/2` no `F ≥ 0` makes `f` bounded,
   `gc_bounded_counterexample`). The hypothesis used instead is the one of §5.1: there is `k̄ > 0`
   with `f(k̄) = k̄` and `f(k) < k` for `k > k̄`; then every feasible capital path stays below
   `k_max = max {k̂, k̄}`, which is all the arguments need.
2. (p. 477) Boundedness alone does not give `k̄ > 0` with `f(k̄) = k̄`: `k/(1 + k)` is bounded,
   continuous, strictly increasing, strictly concave, vanishes at `0` and has no positive fixed
   point (`gc_kbar_counterexample`). The book's later "`f′(0) > 1`" is what is needed.
3. (Solutions manual, Ex 16.1b, Assumption 15.5) The manual takes `k̂ ∈ (0, k̄)` as if it were a
   choice; for `k̂ ≥ k̄` its candidate `y_t ≡ (f(k̂) − k̂)/2` is not an interior point of `Y`
   (`ex_16_1b_manual_interior_counterexample`; the concrete economy `gc_example_hyp` has
   `k̂ = 2 > k̄ = 1`). The corrected interior point (`gc_interior_nonempty`) uses
   `k₀ = k̂`, `k_t = κ` for `t ≥ 1`, with `0 < κ < min {k̄, f(k̂)}`.
4. (Solutions manual, Ex 16.1b, cheaper point) "`φ(x⁰) = 0` implies `x⁰ = 0` or `φ ≡ 0`" is false:
   `φ(x) = x₀` is positive and nonzero and vanishes at `x⁰ = (0, 1, 1, …) ≠ 0`
   (`ex_16_1b_manual_cheaper_counterexample`). Correct argument (`ex_16_1b_cheaper`): `φ` is
   positive on `ℓ∞⁺` (`gc_supporting_nonneg`), so `|φ(z)| ≤ ‖z‖ φ(𝟙)` and `φ(𝟙) > 0`; an interior
   point `y*` of `Y` has `y* ≥ ε𝟙`, so `φ(x⁰) = φ(y⁰) ≥ φ(y*) ≥ ε φ(𝟙) > 0`.
5. (p. 477) Defining `r_t` needs `p_t > 0`, which the book does not prove; it follows from (E2)
   because `U` is strictly increasing (`gc_price_pos`).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

/-! ### The model -/

/-- The restrictions of §16.1 (pp. 476–477) on `β`, `U`, `f` and `k̂`. "`f` bounded" (which with
`F ≥ 0` forces `δ = 1`, Correction 1) is replaced by: `f(k̄) = k̄` for some `k̄ > 0` and `f(k) < k`
for `k > k̄`. `U` is bounded on `ℝ₊`, as in the book. -/
structure GrowthCertaintyHyp (U f : ℝ → ℝ) (β khat kbar : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  U_bdd : ∃ M, ∀ c, 0 ≤ c → |U c| ≤ M
  U_cont : ContinuousOn U (Ici 0)
  U_strictMono : StrictMonoOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  f_cont : ContinuousOn f (Ici 0)
  f_strictMono : StrictMonoOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_zero : f 0 = 0
  khat_pos : 0 < khat
  kbar_pos : 0 < kbar
  f_kbar : f kbar = kbar
  f_lt_self : ∀ k, kbar < k → f k < k

/-- The consumption set `X = ℓ∞⁺` (p. 476). -/
def gcX : Set (BddSeq ℝ) := seqSet (Ici 0)

/-- The production set `Y` (p. 477): nonnegative output sequences `y` supported by a nonnegative
capital path `k` with `k₀ = k̂` and `k_{t+1} + y_t ≤ f(k_t)`. (The book asks `k ∈ ℓ∞⁺`; under
`GrowthCertaintyHyp` every such `k` is bounded by `k_max`, `gc_capital_le`.) -/
def gcY (f : ℝ → ℝ) (khat : ℝ) : Set (BddSeq ℝ) :=
  {y | (∀ t, 0 ≤ y t) ∧ ∃ k : ℕ → ℝ, k 0 = khat ∧ (∀ t, 0 ≤ k t) ∧ ∀ t, k (t + 1) + y t ≤ f (k t)}

/-- Preferences `u(x) = Σ_t βᵗ U(x_t)` (p. 476). -/
noncomputable def gcU (β : ℝ) (U : ℝ → ℝ) : BddSeq ℝ → ℝ := discountedUtility β U

/-- The bound `k_max = max {k̂, k̄}` on feasible capital. -/
def gcKmax (khat kbar : ℝ) : ℝ := max khat kbar

variable {U f : ℝ → ℝ} {β khat kbar : ℝ}

/-- `x ∈ X` means `x_t ≥ 0` for all `t`. -/
theorem mem_gcX {x : BddSeq ℝ} : x ∈ gcX ↔ ∀ t, 0 ≤ x t := Iff.rfl

/-- `f ≥ 0` on `ℝ₊`. -/
theorem gc_f_nonneg (h : GrowthCertaintyHyp U f β khat kbar) {k : ℝ} (hk : 0 ≤ k) : 0 ≤ f k := by
  have := h.f_strictMono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk) hk
  rwa [h.f_zero] at this

/-- `f > 0` on `(0, ∞)`. -/
theorem gc_f_pos (h : GrowthCertaintyHyp U f β khat kbar) {k : ℝ} (hk : 0 < k) : 0 < f k := by
  have := h.f_strictMono (mem_Ici.2 le_rfl) (mem_Ici.2 hk.le) hk
  rwa [h.f_zero] at this

/-- `f(k) > k` on `(0, k̄)` (strict concavity, `f(0) = 0`, `f(k̄) = k̄`). -/
theorem gc_lt_f_of_lt_kbar (h : GrowthCertaintyHyp U f β khat kbar) {k : ℝ} (hk0 : 0 < k)
    (hk : k < kbar) : k < f k := by
  have hb0 : 0 < k / kbar := div_pos hk0 h.kbar_pos
  have hb1 : k / kbar < 1 := (div_lt_one h.kbar_pos).2 hk
  have := h.f_strictConcave.2 (mem_Ici.2 le_rfl) (mem_Ici.2 h.kbar_pos.le) h.kbar_pos.ne
    (sub_pos.2 hb1) hb0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h.f_zero, h.f_kbar] at this
  rwa [div_mul_cancel₀ _ h.kbar_pos.ne'] at this

/-- `f(k) ≤ k_max` on `[0, k_max]`. -/
theorem gc_f_le_kmax (h : GrowthCertaintyHyp U f β khat kbar) {k : ℝ} (hk0 : 0 ≤ k)
    (hk : k ≤ gcKmax khat kbar) : f k ≤ gcKmax khat kbar := by
  have hkm : 0 ≤ gcKmax khat kbar := hk0.trans hk
  have h1 := h.f_strictMono.monotoneOn (mem_Ici.2 hk0) (mem_Ici.2 hkm) hk
  refine h1.trans ?_
  rcases (le_max_right khat kbar).lt_or_eq with hlt | heq
  · exact (h.f_lt_self _ hlt).le
  · rw [gcKmax, ← heq, h.f_kbar]

/-- `k_max > 0`. -/
theorem gc_kmax_pos (h : GrowthCertaintyHyp U f β khat kbar) : 0 < gcKmax khat kbar :=
  h.khat_pos.trans_le (le_max_left _ _)

/-- **Feasible capital is bounded** by `k_max = max {k̂, k̄}` (the corrected form of "`f`
bounded"). -/
theorem gc_capital_le (h : GrowthCertaintyHyp U f β khat kbar) {y k : ℕ → ℝ} (hy : ∀ t, 0 ≤ y t)
    (hk0 : k 0 = khat) (hk : ∀ t, 0 ≤ k t) (hkf : ∀ t, k (t + 1) + y t ≤ f (k t)) :
    ∀ t, k t ≤ gcKmax khat kbar := by
  intro t
  induction t with
  | zero => rw [hk0]; exact le_max_left _ _
  | succ t ih =>
    have := hkf t
    linarith [hy t, gc_f_le_kmax h (hk t) ih]

/-- **Feasible output is bounded** by `k_max`. -/
theorem gc_output_le (h : GrowthCertaintyHyp U f β khat kbar) {y : BddSeq ℝ}
    (hy : y ∈ gcY f khat) (t : ℕ) : y t ≤ gcKmax khat kbar := by
  obtain ⟨hy0, k, hk0, hk, hkf⟩ := hy
  have := hkf t
  linarith [hk (t + 1), gc_f_le_kmax h (hk t) (gc_capital_le h hy0 hk0 hk hkf t)]

/-! ### The NOTEs on pp. 476–477 -/

/-- **NOTE p. 476**: with `F ≥ 0` and `δ ≤ 1`, the function `f(k) = F(k, 1) + (1 − δ)k` is bounded
on `ℝ₊` only if `δ = 1`. -/
theorem gc_bounded_forces_full_depreciation {F : ℝ → ℝ → ℝ} {δ B : ℝ}
    (hF : ∀ k, 0 ≤ k → 0 ≤ F k 1) (hδ : δ ≤ 1) (hB : ∀ k, 0 ≤ k → F k 1 + (1 - δ) * k ≤ B) :
    δ = 1 := by
  by_contra hne
  have hlt : 0 < 1 - δ := sub_pos.2 (lt_of_le_of_ne hδ hne)
  set k := (|B| + 1) / (1 - δ) with hk
  have hk0 : 0 ≤ k := div_nonneg (by positivity) hlt.le
  have hkk : (1 - δ) * k = |B| + 1 := by rw [hk]; field_simp
  have := hB k hk0
  linarith [hF k hk0, le_abs_self B]

/-- **Counterexample** (NOTE p. 476): for `δ = 1/2`, in the book's range `(0, 1]`, no `F ≥ 0`
makes `f(k) = F(k, 1) + (1 − δ)k` bounded on `ℝ₊`. -/
theorem gc_bounded_counterexample :
    ¬ ∃ F : ℝ → ℝ → ℝ, (∀ k, 0 ≤ k → 0 ≤ F k 1) ∧ ∃ B, ∀ k, 0 ≤ k → F k 1 + (1 - 1 / 2) * k ≤ B :=
  fun ⟨_, hF, _, hB⟩ => by
    have := gc_bounded_forces_full_depreciation hF (by norm_num) hB
    norm_num at this

/-- The functions `k ↦ c k/(1 + k)`, used for the counterexample of the NOTE on p. 477 and for a
concrete economy. -/
noncomputable def gcRatio (c : ℝ) (k : ℝ) : ℝ := c * k / (1 + k)

/-- `k ↦ c k/(1 + k)` is strictly concave on `ℝ₊` for `c > 0`. -/
theorem gcRatio_strictConcave {c : ℝ} (hc : 0 < c) : StrictConcaveOn ℝ (Ici 0) (gcRatio c) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [gcRatio, smul_eq_mul]
  have hx' : (0 : ℝ) ≤ x := hx
  have hy' : (0 : ℝ) ≤ y := hy
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + y := by linarith
  have h3 : 0 < 1 + (a * x + (1 - a) * y) := by nlinarith
  rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ h1.ne' h2.ne',
    div_lt_div_iff₀ (mul_pos h1 h2) h3]
  have hxy2 : 0 < (x - y) ^ 2 := by positivity
  have hab' : 0 < a * (1 - a) := mul_pos ha hb
  nlinarith [mul_pos (mul_pos hc hab') hxy2]

/-- `k ↦ c k/(1 + k)` is strictly increasing on `ℝ₊` for `c > 0`. -/
theorem gcRatio_strictMono {c : ℝ} (hc : 0 < c) : StrictMonoOn (gcRatio c) (Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  simp only [gcRatio]
  rw [div_lt_div_iff₀ (by linarith) (by linarith [hy.out])]
  nlinarith

/-- `k ↦ c k/(1 + k)` is continuous on `ℝ₊`. -/
theorem gcRatio_continuousOn (c : ℝ) : ContinuousOn (gcRatio c) (Ici 0) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by
    have : (0 : ℝ) ≤ x := hx
    linarith

/-- `0 ≤ c k/(1 + k) ≤ c` on `ℝ₊`, `c ≥ 0`. -/
theorem gcRatio_mem_Icc {c : ℝ} (hc : 0 ≤ c) {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ gcRatio c k ∧ gcRatio c k ≤ c := by
  simp only [gcRatio]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **Counterexample** (NOTE p. 477): `f(k) = k/(1 + k)` is continuous, strictly increasing,
strictly concave, bounded, and `f(0) = 0`, but has no `k̄ > 0` with `f(k̄) = k̄`: boundedness does
not give `k̄` (the book's `f′(0) > 1` is needed; here `f′(0) = 1`). -/
theorem gc_kbar_counterexample :
    ContinuousOn (gcRatio 1) (Ici 0) ∧ StrictMonoOn (gcRatio 1) (Ici 0) ∧
      StrictConcaveOn ℝ (Ici 0) (gcRatio 1) ∧ gcRatio 1 0 = 0 ∧
      (∀ k, 0 ≤ k → |gcRatio 1 k| ≤ 1) ∧ ¬ ∃ kbar, 0 < kbar ∧ gcRatio 1 kbar = kbar := by
  refine ⟨gcRatio_continuousOn 1, gcRatio_strictMono one_pos, gcRatio_strictConcave one_pos,
    by simp [gcRatio], fun k hk => ?_, ?_⟩
  · obtain ⟨h0, h1⟩ := gcRatio_mem_Icc zero_le_one hk
    rw [abs_of_nonneg h0]; exact h1
  · rintro ⟨k, hk, hfix⟩
    simp only [gcRatio, one_mul] at hfix
    rw [div_eq_iff (by linarith)] at hfix
    nlinarith

/-- **A concrete economy** satisfying `GrowthCertaintyHyp`: `U(c) = c/(1 + c)`,
`f(k) = 2k/(1 + k)`, `β = 1/2`, `k̂ = 2`, `k̄ = 1`. It has `k̂ > k̄`. -/
theorem gc_example_hyp : GrowthCertaintyHyp (gcRatio 1) (gcRatio 2) (1 / 2) 2 1 where
  beta_pos := by norm_num
  beta_lt_one := by norm_num
  U_bdd := ⟨1, fun c hc => by
    obtain ⟨h0, h1⟩ := gcRatio_mem_Icc zero_le_one hc
    rw [abs_of_nonneg h0]; exact h1⟩
  U_cont := gcRatio_continuousOn 1
  U_strictMono := gcRatio_strictMono one_pos
  U_strictConcave := gcRatio_strictConcave one_pos
  f_cont := gcRatio_continuousOn 2
  f_strictMono := gcRatio_strictMono two_pos
  f_strictConcave := gcRatio_strictConcave two_pos
  f_zero := by simp [gcRatio]
  khat_pos := by norm_num
  kbar_pos := by norm_num
  f_kbar := by norm_num [gcRatio]
  f_lt_self k hk := by
    simp only [gcRatio]
    rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-! ### Coordinates in `ℓ∞` -/

/-- Coordinates of a sum. -/
theorem gc_coord_add (x y : BddSeq ℝ) (t : ℕ) : (x + y) t = x t + y t := by
  rw [lp.coeFn_add]; rfl

/-- Coordinates of a scalar multiple. -/
theorem gc_coord_smul (c : ℝ) (x : BddSeq ℝ) (t : ℕ) : (c • x) t = c * x t := by
  rw [lp.coeFn_smul]; rfl

/-- Coordinates of a difference. -/
theorem gc_coord_sub (x y : BddSeq ℝ) (t : ℕ) : (x - y) t = x t - y t := by
  rw [lp.coeFn_sub]; rfl

/-- Coordinates of the constant sequence `𝟙`. -/
theorem gc_coord_one (t : ℕ) : oneSeq t = 1 := rfl

/-- Coordinates of the unit vector `e_s`. -/
theorem gc_coord_single (s t : ℕ) :
    (lp.single ∞ s (1 : ℝ) : BddSeq ℝ) t = if t = s then 1 else 0 := by
  rw [lp.single_apply, Pi.single_apply]

/-- `|x_t| ≤ ‖x‖`. -/
theorem gc_abs_coord_le (x : BddSeq ℝ) (t : ℕ) : |x t| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using norm_seq_coord_le x t

/-! ### Properties of `u` -/

/-- The series defining `u(x)` converges on `X`. -/
theorem gc_summable (h : GrowthCertaintyHyp U f β khat kbar) {x : BddSeq ℝ} (hx : x ∈ gcX) :
    Summable fun t => β ^ t * U (x t) :=
  let ⟨_, hM⟩ := h.U_bdd
  summable_discounted h.beta_pos.le h.beta_lt_one (fun c hc => hM c hc) hx

/-- `X` is convex. -/
theorem gc_convex_X : Convex ℝ gcX := convex_seqSet (E := ℝ) (convex_Ici 0)

/-- `u` is monotone on `X`. -/
theorem gc_utility_mono (h : GrowthCertaintyHyp U f β khat kbar) {x z : BddSeq ℝ} (hx : x ∈ gcX)
    (hz : z ∈ gcX) (hxz : ∀ t, x t ≤ z t) : gcU β U x ≤ gcU β U z :=
  Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left
    (h.U_strictMono.monotoneOn (hx t) (hz t) (hxz t)) (pow_nonneg h.beta_pos.le t))
    (gc_summable h hx) (gc_summable h hz)

/-- `u` is strictly increasing on `X`: `x ≤ z` with `x_{t₀} < z_{t₀}` gives `u(x) < u(z)`. -/
theorem gc_utility_lt (h : GrowthCertaintyHyp U f β khat kbar) {x z : BddSeq ℝ} (hx : x ∈ gcX)
    (hz : z ∈ gcX) (hxz : ∀ t, x t ≤ z t) {t₀ : ℕ} (ht₀ : x t₀ < z t₀) :
    gcU β U x < gcU β U z :=
  Summable.tsum_lt_tsum (i := t₀) (fun t => mul_le_mul_of_nonneg_left
    (h.U_strictMono.monotoneOn (hx t) (hz t) (hxz t)) (pow_nonneg h.beta_pos.le t))
    (mul_lt_mul_of_pos_left (h.U_strictMono (hx t₀) (hz t₀) ht₀) (pow_pos h.beta_pos t₀))
    (gc_summable h hx) (gc_summable h hz)

/-- `u` is concave on `X`. -/
theorem gc_utility_concave (h : GrowthCertaintyHyp U f β khat kbar) :
    ConcaveOn ℝ gcX (gcU β U) := by
  obtain ⟨M, hM⟩ := h.U_bdd
  refine ⟨convex_seqSet (convex_Ici 0), fun x hx z hz a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have := discountedUtility_concave h.beta_pos.le h.beta_lt_one (fun c hc => hM c hc)
    h.U_strictConcave.concaveOn hx hz ha (by linarith)
  simpa [gcU, smul_eq_mul] using this

/-- `u` is strictly concave along the midpoint of two distinct points of `X`. -/
theorem gc_utility_strict_midpoint (h : GrowthCertaintyHyp U f β khat kbar) {x z : BddSeq ℝ}
    (hx : x ∈ gcX) (hz : z ∈ gcX) (hne : x ≠ z) :
    (gcU β U x + gcU β U z) / 2 < gcU β U ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) := by
  have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z ∈ gcX :=
    convex_seqSet (convex_Ici 0) hx hz (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨t₀, ht₀⟩ : ∃ t, x t ≠ z t := by
    by_contra hcon
    push Not at hcon
    exact hne (lp.ext (funext hcon))
  have hmt : ∀ t, ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) t = 1 / 2 * x t + 1 / 2 * z t :=
    fun t => by rw [gc_coord_add, gc_coord_smul, gc_coord_smul]
  have hterm : ∀ t, β ^ t * U (x t) + β ^ t * U (z t) ≤
      2 * (β ^ t * U (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) t)) := fun t => by
    have := h.U_strictConcave.concaveOn.2 (hx t) (hz t) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [hmt]
    simp only [smul_eq_mul] at this
    nlinarith [mul_le_mul_of_nonneg_left this (pow_nonneg h.beta_pos.le t)]
  have hstrict : β ^ t₀ * U (x t₀) + β ^ t₀ * U (z t₀) <
      2 * (β ^ t₀ * U (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) t₀)) := by
    have := h.U_strictConcave.2 (hx t₀) (hz t₀) ht₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [hmt]
    simp only [smul_eq_mul] at this
    nlinarith [mul_lt_mul_of_pos_left this (pow_pos h.beta_pos t₀)]
  have hlt := Summable.tsum_lt_tsum (i := t₀) hterm hstrict
    ((gc_summable h hx).add (gc_summable h hz)) ((gc_summable h hm).mul_left 2)
  rw [(gc_summable h hx).tsum_add (gc_summable h hz), tsum_mul_left] at hlt
  change (∑' t, β ^ t * U (x t) + ∑' t, β ^ t * U (z t)) / 2 <
    ∑' t, β ^ t * U (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) t)
  linarith

/-- **Local nonsatiation** on `X = ℓ∞⁺` (the hypothesis of Theorem 15.3): `x + 𝟙/(n + 1) → x`
and is strictly preferred. -/
theorem gc_localNonsatiation {ι : Type*} (h : GrowthCertaintyHyp U f β khat kbar) :
    LocalNonsatiation (fun _ : ι => gcX) (fun _ => gcU β U) := by
  intro i x hx
  have hmem : ∀ n : ℕ, x + (1 / ((n : ℝ) + 1)) • oneSeq ∈ gcX := fun n => mem_gcX.2 fun t => by
    rw [gc_coord_add, gc_coord_smul, gc_coord_one, mul_one]
    have := mem_gcX.1 hx t
    positivity
  refine ⟨fun n => x + (1 / ((n : ℝ) + 1)) • oneSeq, hmem, ?_, fun n => ?_⟩
  · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 := (h1.smul_const oneSeq).const_add x
    simpa using h0
  · refine gc_utility_lt h hx (hmem n) (fun t => ?_) (t₀ := 0) ?_ <;>
    · rw [gc_coord_add, gc_coord_smul, gc_coord_one, mul_one]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith

/-! ### The economy as a Chapter 15 economy: Exercise 16.1(b) -/

/-- With one firm, the aggregate technology is the firm's production set. -/
theorem gc_aggTech_unit (Y : Set (BddSeq ℝ)) : aggTech (fun _ : Unit => Y) = Y := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

/-- `Y` is convex (Assumption 15.4): convex combinations of supporting capital paths are
supporting, by concavity of `f`. -/
theorem gc_convex_Y (h : GrowthCertaintyHyp U f β khat kbar) : Convex ℝ (gcY f khat) := by
  rintro y ⟨hy0, k, hk0, hk, hkf⟩ y' ⟨hy0', k', hk0', hk', hkf'⟩ a b ha hb hab
  refine ⟨fun t => ?_, fun t => a * k t + b * k' t, ?_, fun t => ?_, fun t => ?_⟩
  · rw [gc_coord_add, gc_coord_smul, gc_coord_smul]
    have := hy0 t; have := hy0' t
    positivity
  · simp only [hk0, hk0', ← add_mul, hab, one_mul]
  · have := hk t; have := hk' t
    positivity
  · rw [gc_coord_add, gc_coord_smul, gc_coord_smul]
    have hc := h.f_strictConcave.concaveOn.2 (mem_Ici.2 (hk t)) (mem_Ici.2 (hk' t)) ha hb hab
    simp only [smul_eq_mul] at hc
    nlinarith [hkf t, hkf' t]

/-- **Assumption 15.5, corrected interior point** (NOTE to the manual's Ex 16.1b). Pick
`0 < κ < min {k̄, f(k̂)}`, the capital path `k₀ = k̂`, `k_t = κ` (`t ≥ 1`), and
`m = min {f(k̂) − κ, f(κ) − κ} > 0`; the ball of radius `m/2` about `y ≡ m/2` lies in `Y`. This
works for every `k̂ > 0`, including `k̂ ≥ k̄`. -/
theorem gc_interior_nonempty (h : GrowthCertaintyHyp U f β khat kbar) :
    (interior (gcY f khat)).Nonempty := by
  have hfk : 0 < f khat := gc_f_pos h h.khat_pos
  set κ := min (kbar / 2) (f khat / 2) with hκ
  have hκ0 : 0 < κ := lt_min (half_pos h.kbar_pos) (half_pos hfk)
  have hκk : κ < kbar := (min_le_left _ _).trans_lt (half_lt_self h.kbar_pos)
  have hκf : κ < f khat := (min_le_right _ _).trans_lt (half_lt_self hfk)
  have hfκ : κ < f κ := gc_lt_f_of_lt_kbar h hκ0 hκk
  set m := min (f khat - κ) (f κ - κ) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  refine ⟨(m / 2) • oneSeq, interior_maximal (t := Metric.ball ((m / 2) • oneSeq) (m / 2)) ?_
    Metric.isOpen_ball (Metric.mem_ball_self (half_pos hm0))⟩
  intro y hy
  have hyt : ∀ t, |y t - m / 2| < m / 2 := fun t => by
    have := (gc_abs_coord_le (y - (m / 2) • oneSeq) t).trans_lt (mem_ball_iff_norm.1 hy)
    rwa [gc_coord_sub, gc_coord_smul, gc_coord_one, mul_one] at this
  refine ⟨fun t => ?_, fun t => if t = 0 then khat else κ, by simp, fun t => ?_, fun t => ?_⟩
  · linarith [(abs_lt.1 (hyt t)).1]
  · dsimp only
    split_ifs
    exacts [h.khat_pos.le, hκ0.le]
  · have h1 := (abs_lt.1 (hyt t)).2
    rcases t with _ | t
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      linarith [min_le_left (f khat - κ) (f κ - κ)]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      linarith [min_le_right (f khat - κ) (f κ - κ)]

/-- An interior point of `Y` is bounded below by a positive constant (`Y ⊆ ℓ∞⁺`). -/
theorem gc_interior_ge {y : BddSeq ℝ} (hy : y ∈ interior (gcY f khat)) :
    ∃ ε > 0, ∀ t, ε ≤ y t := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  refine ⟨r / 2, half_pos hr, fun t => ?_⟩
  have hmem : y - (r / 2) • oneSeq ∈ gcY f khat := hball (by
    rw [mem_ball_iff_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    calc r / 2 * ‖oneSeq‖ ≤ r / 2 * 1 :=
          mul_le_mul_of_nonneg_left norm_oneSeq_le (half_pos hr).le
      _ < r := by linarith)
  have := hmem.1 t
  rw [gc_coord_sub, gc_coord_smul, gc_coord_one] at this
  linarith

/-- **Exercise 16.1(b)**: under the restrictions of §16.1, `u`, `X`, `Y` satisfy Assumptions
15.1–15.5. 15.1: `X` is convex. 15.2: from concavity of `U` (Ex 15.10b). 15.3: from continuity and
boundedness of `U` (Ex 15.10b). 15.4: from concavity of `f` (`gc_convex_Y`). 15.5: from `k̂ > 0`,
continuity, monotonicity, concavity of `f` and `f(k̄) = k̄` (`gc_interior_nonempty`). -/
theorem ex_16_1b_assumptions (h : GrowthCertaintyHyp U f β khat kbar) :
    Assumption15_1 (fun _ : Unit => gcX) ∧ Assumption15_2 (fun _ : Unit => gcX) (fun _ => gcU β U) ∧
      Assumption15_3 (fun _ : Unit => gcX) (fun _ => gcU β U) ∧
      Assumption15_4 (fun _ : Unit => gcY f khat) ∧
      Assumption15_5 (BddSeq ℝ) (fun _ : Unit => gcY f khat) := by
  obtain ⟨M, hM⟩ := h.U_bdd
  obtain ⟨h2, h3, -⟩ := ex_15_10b (C := Ici (0 : ℝ)) h.beta_pos.le h.beta_lt_one
    (mem_Ici.2 le_rfl) (fun c hc => hM c hc) h.U_cont h.U_strictConcave.concaveOn
  refine ⟨fun _ => convex_seqSet (convex_Ici 0), fun _ => h2, fun _ => h3, ?_, Or.inl ?_⟩
  · rw [Assumption15_4, gc_aggTech_unit]
    exact gc_convex_Y h
  · rw [gc_aggTech_unit]
    exact gc_interior_nonempty h

/-! ### The cheaper point -/

/-- A functional `φ` satisfying (3) of Theorem 15.4 at `x⁰ ∈ X` is **positive** on `ℓ∞⁺`:
`x⁰ + z` is weakly preferred to `x⁰` for `z ≥ 0`. -/
theorem gc_supporting_nonneg (h : GrowthCertaintyHyp U f β khat kbar) {x₀ : BddSeq ℝ}
    (hx₀ : x₀ ∈ gcX) {φ : StrongDual ℝ (BddSeq ℝ)}
    (hφ : ∀ z ∈ gcX, gcU β U x₀ ≤ gcU β U z → φ x₀ ≤ φ z) {z : BddSeq ℝ} (hz : z ∈ gcX) :
    0 ≤ φ z := by
  have hsum : x₀ + z ∈ gcX := mem_gcX.2 fun t => by
    rw [gc_coord_add]
    exact add_nonneg (mem_gcX.1 hx₀ t) (mem_gcX.1 hz t)
  have := hφ _ hsum (gc_utility_mono h hx₀ hsum fun t => by
    rw [gc_coord_add]
    linarith [mem_gcX.1 hz t])
  rw [map_add] at this
  linarith

/-- A positive functional on `ℓ∞` is bounded by its value at `𝟙`: `|φ(z)| ≤ ‖z‖ φ(𝟙)`. -/
theorem gc_abs_le_of_nonneg {φ : StrongDual ℝ (BddSeq ℝ)} (hφ : ∀ z ∈ gcX, 0 ≤ φ z)
    (z : BddSeq ℝ) : |φ z| ≤ ‖z‖ * φ oneSeq := by
  have h1 : ‖z‖ • oneSeq - z ∈ gcX := mem_gcX.2 fun t => by
    rw [gc_coord_sub, gc_coord_smul, gc_coord_one, mul_one]
    linarith [(abs_le.1 (gc_abs_coord_le z t)).2]
  have h2 : ‖z‖ • oneSeq + z ∈ gcX := mem_gcX.2 fun t => by
    rw [gc_coord_add, gc_coord_smul, gc_coord_one, mul_one]
    linarith [(abs_le.1 (gc_abs_coord_le z t)).1]
  have a1 := hφ _ h1
  have a2 := hφ _ h2
  rw [map_sub, map_smul, smul_eq_mul] at a1
  rw [map_add, map_smul, smul_eq_mul] at a2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A nonzero positive functional on `ℓ∞` has `φ(𝟙) > 0`. -/
theorem gc_one_pos {φ : StrongDual ℝ (BddSeq ℝ)} (hφ : ∀ z ∈ gcX, 0 ≤ φ z) (hne : φ ≠ 0) :
    0 < φ oneSeq := by
  rcases (hφ oneSeq (mem_gcX.2 fun _ => zero_le_one)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hne
    ext z
    have := gc_abs_le_of_nonneg hφ z
    rw [← heq, mul_zero] at this
    simpa using abs_nonpos_iff.1 this

/-- **Exercise 16.1(b), the cheaper point (corrected)**: if `φ ≠ 0` satisfies (3)–(4) of Theorem
15.4 at the symmetric allocation `(x⁰, x⁰)`, then `φ(0) < φ(x⁰)`, so `0 ∈ X` is a cheaper point
and the Remark after Theorem 15.4 applies. -/
theorem ex_16_1b_cheaper (h : GrowthCertaintyHyp U f β khat kbar) {x₀ : BddSeq ℝ}
    (hx₀ : x₀ ∈ gcX) {φ : StrongDual ℝ (BddSeq ℝ)} (hne : φ ≠ 0)
    (hsup : SupportsAllocation (fun _ : Unit => gcX) (fun _ => gcU β U)
      (fun _ : Unit => gcY f khat) (fun _ => x₀) (fun _ => x₀) φ) : φ 0 < φ x₀ := by
  have hpos : ∀ z ∈ gcX, 0 ≤ φ z := fun z hz =>
    gc_supporting_nonneg h hx₀ (fun w hw hle => hsup.1 () w hw hle) hz
  obtain ⟨y, hy⟩ := gc_interior_nonempty h
  obtain ⟨ε, hε, hεy⟩ := gc_interior_ge hy
  have h1 : y - ε • oneSeq ∈ gcX := mem_gcX.2 fun t => by
    rw [gc_coord_sub, gc_coord_smul, gc_coord_one, mul_one]
    linarith [hεy t]
  have h2 := hpos _ h1
  rw [map_sub, map_smul, smul_eq_mul] at h2
  have h3 := hsup.2 () y (interior_subset hy)
  have h4 := gc_one_pos hpos hne
  rw [map_zero]
  nlinarith

/-- Evaluation at a coordinate as a continuous linear functional on `ℓ∞`. -/
noncomputable def gcEval (t : ℕ) : StrongDual ℝ (BddSeq ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => x t
      map_add' := fun x y => gc_coord_add x y t
      map_smul' := fun c x => gc_coord_smul c x t } 1
    fun x => by simpa [Real.norm_eq_abs] using gc_abs_coord_le x t

/-- Value of the evaluation functional. -/
theorem gcEval_apply (t : ℕ) (x : BddSeq ℝ) : gcEval t x = x t := rfl

/-- **Counterexample** (manual, Ex 16.1b): "`φ(x⁰) = 0` implies `x⁰ = 0` or `φ ≡ 0`" is false for
positive functionals: `φ(x) = x₀` is positive on `ℓ∞⁺`, nonzero, and vanishes at
`x⁰ = (0, 1, 1, …) ≠ 0`. -/
theorem ex_16_1b_manual_cheaper_counterexample :
    (∀ z ∈ gcX, 0 ≤ gcEval 0 z) ∧ gcEval 0 ≠ 0 ∧
      ∃ x₀ ∈ gcX, x₀ ≠ 0 ∧ gcEval 0 x₀ = 0 := by
  refine ⟨fun z hz => mem_gcX.1 hz 0, fun h0 => ?_, oneSeq - lp.single ∞ 0 1, ?_, fun h0 => ?_, ?_⟩
  · have := congrArg (fun φ : StrongDual ℝ (BddSeq ℝ) => φ oneSeq) h0
    simp [gcEval_apply, gc_coord_one] at this
  · refine mem_gcX.2 fun t => ?_
    rw [gc_coord_sub, gc_coord_one, gc_coord_single]
    split_ifs <;> norm_num
  · have := congrArg (fun x : BddSeq ℝ => x 1) h0
    simp only [gc_coord_sub, gc_coord_one, gc_coord_single, one_ne_zero, ↓reduceIte] at this
    norm_num at this
  · rw [gcEval_apply, gc_coord_sub, gc_coord_one, gc_coord_single]
    simp

/-- **Counterexample** (manual, Ex 16.1b, Assumption 15.5): when `k̂ ≥ k̄` the manual's candidate
`y_t ≡ (f(k̂) − k̂)/2` is not an interior point of `Y` (its coordinates are `≤ 0`, while interior
points are bounded below by a positive constant). The economy `gc_example_hyp` has `k̂ > k̄`. -/
theorem ex_16_1b_manual_interior_counterexample (h : GrowthCertaintyHyp U f β khat kbar)
    (hk : kbar ≤ khat) : ((f khat - khat) / 2) • oneSeq ∉ interior (gcY f khat) := by
  intro hint
  obtain ⟨ε, hε, hεy⟩ := gc_interior_ge hint
  have := hεy 0
  rw [gc_coord_smul, gc_coord_one, mul_one] at this
  have hle : f khat ≤ khat := by
    rcases hk.lt_or_eq with hlt | heq
    · exact (h.f_lt_self _ hlt).le
    · rw [← heq, h.f_kbar]
  linarith

/-! ### Exercise 16.1(c): Assumptions 15.6 and 15.7 -/

/-- Truncations of a production plan are production plans, supported by the same capital path. -/
theorem gc_seqTruncClosed_Y : SeqTruncClosed (gcY f khat) := by
  rintro y ⟨hy0, k, hk0, hk, hkf⟩
  refine Eventually.of_forall fun T => ⟨fun t => ?_, k, hk0, hk, fun t => ?_⟩
  · rw [seqTrunc_apply]
    split_ifs
    exacts [hy0 t, le_rfl]
  · rw [seqTrunc_apply]
    split_ifs
    · exact hkf t
    · linarith [hkf t, hy0 t]

/-- **Exercise 16.1(c)**: Assumptions 15.6 and 15.7 hold. `X` and `Y` are closed under truncation
(for `Y`, keep the capital path, using `y_t ≥ 0`), and `u(xᵀ) → u(x)` since `U` is bounded. -/
theorem ex_16_1c_assumptions (h : GrowthCertaintyHyp U f β khat kbar) :
    Assumption15_6 (fun _ : Unit => gcX) (fun _ : Unit => gcY f khat) ∧
      Assumption15_7 (fun _ : Unit => gcX) (fun _ => gcU β U) := by
  obtain ⟨M, hM⟩ := h.U_bdd
  exact ⟨⟨fun _ => (ex_15_10a (convex_Ici 0) (mem_Ici.2 le_rfl)).2, fun _ => gc_seqTruncClosed_Y⟩,
    fun _ => ex_15_10b_tail h.beta_pos.le h.beta_lt_one (mem_Ici.2 le_rfl) (fun c hc => hM c hc)⟩

/-! ### Prices and interest rates (p. 477) -/

/-- **Prices are positive** (NOTE p. 477): in any competitive equilibrium of an economy whose
consumers have `(X, u)`, `p_t = φ(e_t) > 0`, because `x⁰ + e_t` is strictly preferred to `x⁰`, so by
(E2) it costs strictly more. -/
theorem gc_price_pos {ι κ : Type*} [Fintype ι] [Fintype κ] (h : GrowthCertaintyHyp U f β khat kbar)
    {Y : κ → Set (BddSeq ℝ)} {x₀ : ι → BddSeq ℝ} {y₀ : κ → BddSeq ℝ}
    {φ : StrongDual ℝ (BddSeq ℝ)}
    (hCE : CompetitiveEq (fun _ : ι => gcX) (fun _ => gcU β U) Y x₀ y₀ φ) (i : ι) (t : ℕ) :
    0 < φ (lp.single ∞ t 1) := by
  have hx := hCE.1.1 i
  have hcoord : ∀ s, x₀ i s ≤ (x₀ i + (lp.single ∞ t (1 : ℝ) : BddSeq ℝ)) s := fun s => by
    rw [gc_coord_add, gc_coord_single]
    split_ifs <;> linarith
  have hmem : x₀ i + (lp.single ∞ t (1 : ℝ) : BddSeq ℝ) ∈ gcX := mem_gcX.2 fun s =>
    (mem_gcX.1 hx s).trans (hcoord s)
  have hlt := ce_cost_lt_of_utility_lt hCE i hmem (gc_utility_lt h hx hmem hcoord (t₀ := t)
    (by rw [gc_coord_add, gc_coord_single]; simp))
  rw [map_add] at hlt
  linarith

/-- The **real interest rate** `r_t`, defined by `1/(1 + r_t) = p_{t+1}/p_t` (p. 477). -/
noncomputable def gcRate (p : ℕ → ℝ) (t : ℕ) : ℝ := p t / p (t + 1) - 1

/-- `1/(1 + r_t) = p_{t+1}/p_t` for positive prices. -/
theorem gc_rate_spec {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (t : ℕ) :
    1 / (1 + gcRate p t) = p (t + 1) / p t := by
  have h1 := (hp t).ne'
  have h2 := (hp (t + 1)).ne'
  simp only [gcRate, add_sub_cancel]
  field_simp

/-- The discount factors: `Π_{s<t} (1 + r_s)⁻¹ = p_t / p_0`. -/
theorem gc_discount_prod {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (t : ℕ) :
    ∏ s ∈ Finset.range t, (1 + gcRate p s)⁻¹ = p t / p 0 := by
  induction t with
  | zero => simp [(hp 0).ne']
  | succ t ih =>
    rw [Finset.prod_range_succ, ih, ← one_div, gc_rate_spec hp t]
    have := (hp t).ne'
    field_simp

/-- **The budget constraint in interest-rate form** (p. 477): dividing by `p₀`,
`Σ_t p_t x_t ≤ Σ_t p_t x⁰_t` iff `Σ_t (Π_{s<t} (1 + r_s)⁻¹) x_t ≤ Σ_t (Π_{s<t} (1 + r_s)⁻¹) x⁰_t`
(the `t = 0` term has the empty product `1`). -/
theorem gc_budget_iff {p x x₀ : ℕ → ℝ} (hp : ∀ t, 0 < p t) :
    (∑' t, p t * x t ≤ ∑' t, p t * x₀ t) ↔
      (∑' t, (∏ s ∈ Finset.range t, (1 + gcRate p s)⁻¹) * x t ≤
        ∑' t, (∏ s ∈ Finset.range t, (1 + gcRate p s)⁻¹) * x₀ t) := by
  have hrw : ∀ y : ℕ → ℝ, ∑' t, (∏ s ∈ Finset.range t, (1 + gcRate p s)⁻¹) * y t =
      (∑' t, p t * y t) / p 0 := fun y => by
    rw [← tsum_div_const]
    congr 1
    ext t
    rw [gc_discount_prod hp]
    ring
  rw [hrw, hrw, div_le_div_iff_of_pos_right (hp 0)]

end StokeyLucasPrescott.EquilibriumApplications
