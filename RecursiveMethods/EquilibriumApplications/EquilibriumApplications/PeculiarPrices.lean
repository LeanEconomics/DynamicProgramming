/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.PeculiarModel
import EquilibriumApplications.WelfareSecond

/-!
# A peculiar example (§16.6): supporting prices in `ℓ∞`

SLP §16.6, pp. 494–495, for the economy of `PeculiarModel` (one household with `X = ℓ∞⁺` and
`u(x) = Σ_t 2^{−(t+1)}[1 − exp(−x_t 2^{t+1})]`, one firm with `Y = {y ≤ x*}`, `x*_t = 2^{−(t+1)}`;
time starts at `t = 0`). Conditions (1), (2) (p. 494) on `φ ∈ (ℓ∞)*` are
(1) `x ∈ X, u(x) ≥ u(x*) ⇒ φ(x) ≥ φ(x*)` and (2) `y ∈ Y ⇒ φ(y) ≤ φ(y*)`; `ψ = seqRegularPart φ`
is (3), `ψ(x) = lim_T φ(xᵀ)`.

* **Exercise 16.6(b)** (`ex_16_6b`, p. 495): the "natural" prices `p = (c, c, …)`, `c ≠ 0`, do not
  define a continuous linear functional on `ℓ∞`; indeed no `φ ∈ (ℓ∞)*` has `φ(eₜ) = c` for all `t`
  (`pec_const_price_not_dual`).
* **Exercise 16.6(c)** (`ex_16_6c`): every `φ` satisfying (1)–(2) has `ψ = 0`.
* **The real conclusion of the example** (`pec_real_conclusion`; not stated in the book):
  supporting functionals `φ ≠ 0` exist (Theorem 15.4, `pec_supporting_exists`), but every one of
  them has `ψ = 0`, `φ(x*) = 0` (`pec_phi_star_eq_zero`), vanishes on finitely supported
  sequences, and is `≥ 0` on `X`, so no consumption is cheaper than `x*` and the Remark after
  Theorem 15.4 never applies (`pec_no_cheaper_point`); and the economy has **no competitive
  equilibrium at all** in `ℓ∞` (`pec_no_competitiveEq`): `x* + e₀` costs `φ(x*)` and is
  strictly preferred.

**Corrections (solutions manual, Exercise 16.6(c)).**
* *First case (`p_t > p_1`).* The manual moves an amount from period `t` to period 1 and claims
  that utility rises. It falls, for every amount and every pair of periods
  (`pec_equal_transfer_lowers_utility`): at `x*` all marginal utilities equal `e⁻¹`, and by strict
  concavity an equal transfer loses more than it gains. The structure of the manual's argument
  is right: since the move strictly lowers the cost `ψ`, a weak utility gain *would* contradict
  condition (1). (So the transcription's NOTE is wrong to say that the contradiction is with (E2)
  rather than (1): it is with (1), and the error is only the sign of the utility change.) The
  repair (`pec_transfer_gain`) is an unequal transfer: take `ε` from the dearer period and give
  `rε`, `r > 1`, to the cheaper one; for small `ε` utility does not fall, and for `r p_cheap <
  p_dear` the cost falls strictly, contradicting (1).
* *Second case (`p_1 > p_t`).* The manual keeps `ψ(x′) = ψ(x*)` with `u(x′) > u(x*)`; that does not
  contradict (1) (which needs `ψ(x′) < ψ(x*)`). The proof here covers both cases at once with a
  strict cost decrease, and needs only `p_s > 0` and `p_t < p_s` for some `t ≠ s`, which holds
  because `Σ_t |p_t| < ∞` forces `p_t → 0`; the manual's step "all `p_t` equal" is not needed.
* *`p_t < 0`.* "Set `y_t = −∞`" is replaced by `y* − eₜ ∈ Y` (`pec_price_nonneg`).
* The manual's (b) is correct; the version here holds for every `c ≠ 0`, and only uses the values
  of `φ` on the unit vectors.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

/-! ### Exercise 16.6(b) -/

/-- No continuous linear functional on `ℓ∞` gives the same price `c ≠ 0` to every unit vector:
by Lemma 15.5 (`seqRegularPart_real`), `Σ_t |φ(eₜ)| ≤ ‖φ‖ < ∞`. -/
theorem pec_const_price_not_dual {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ φ : StrongDual ℝ (BddSeq ℝ), ∀ t, φ (lp.single ∞ t 1) = c := by
  rintro ⟨φ, hφ⟩
  have h := (seqRegularPart_real φ).1
  simp only [hφ] at h
  exact hc (abs_eq_zero.1 ((summable_const_iff |c|).1 h))

/-- **Exercise 16.6(b)** (p. 495): for `c ≠ 0` the price vector `p = (c, c, …)` does not define a
continuous linear functional on `ℓ∞`, i.e. there is no `φ ∈ (ℓ∞)*` with `φ(x) = Σ_t c x_t`
(whenever, or even only where, the series converges). -/
theorem ex_16_6b {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ φ : StrongDual ℝ (BddSeq ℝ), ∀ x : BddSeq ℝ, HasSum (fun t => c * x t) (φ x) := by
  rintro ⟨φ, hφ⟩
  refine pec_const_price_not_dual hc ⟨φ, fun t => ?_⟩
  refine (hφ (lp.single ∞ t 1)).unique ?_
  have := hasSum_pi_single t c
  refine this.congr_fun fun q => ?_
  rw [lp.single_apply]
  rcases eq_or_ne q t with rfl | hq
  · simp
  · simp [Pi.single_eq_of_ne hq]

/-! ### Moving consumption between periods at `x*` -/

/-- The change in period `t`'s term when `x*_t = w_t` changes by `d`:
`w_t e⁻¹ (1 − exp(−d / w_t))`. -/
theorem pecTerm_pecW_add (t : ℕ) (d : ℝ) :
    pecTerm t (pecW t + d) - pecTerm t (pecW t) =
      pecW t * Real.exp (-1) * (1 - Real.exp (-(d / pecW t))) := by
  have hw := (pecW_pos t).ne'
  unfold pecTerm
  have : -((pecW t + d) / pecW t) = -1 + -(d / pecW t) := by field_simp; ring
  rw [this, Real.exp_add, div_self hw]
  ring

/-- Coordinates of `x* + a eₜ + b eₛ`, `s ≠ t`, at `s`. -/
theorem pec_two_single_apply_s {s t : ℕ} (hst : s ≠ t) (a : ℝ) :
    (pecStar + (lp.single ∞ t a : BddSeq ℝ)) s = pecW s := by
  rw [pec_add_single_apply, Function.update_of_ne hst, pecStar_apply]

/-- `x* + a eₜ ∈ X` when `w_t + a ≥ 0`. -/
theorem pec_add_single_mem {x : BddSeq ℝ} (hx : x ∈ pecX) (t : ℕ) {a : ℝ} (ha : 0 ≤ x t + a) :
    x + (lp.single ∞ t a : BddSeq ℝ) ∈ pecX := fun q => by
  rw [pec_add_single_apply]
  rcases eq_or_ne q t with rfl | hq
  · simpa using ha
  · simpa [Function.update_of_ne hq] using hx q

/-- Utility of `x* + a eₜ + b eₛ` (`s ≠ t`, `w_t + a ≥ 0`, `w_s + b ≥ 0`). -/
theorem pecU_star_two_single {s t : ℕ} (hst : s ≠ t) {a b : ℝ} (ha : 0 ≤ pecW t + a)
    (hb : 0 ≤ pecW s + b) :
    pecU (pecStar + (lp.single ∞ t a : BddSeq ℝ) + (lp.single ∞ s b : BddSeq ℝ)) =
      pecU pecStar + pecW t * Real.exp (-1) * (1 - Real.exp (-(a / pecW t))) +
        pecW s * Real.exp (-1) * (1 - Real.exp (-(b / pecW s))) := by
  have h1 : pecStar + (lp.single ∞ t a : BddSeq ℝ) ∈ pecX :=
    pec_add_single_mem pecStar_mem_pecX t (by simpa using ha)
  have hs := pec_two_single_apply_s hst a
  rw [pecU_add_single h1 s (by rw [hs]; exact hb), hs,
    pecU_add_single pecStar_mem_pecX t (by simpa using ha), pecStar_apply, pecTerm_pecW_add,
    pecTerm_pecW_add]

/-- **The manual's equal transfer lowers utility.** For periods `s ≠ t` and `0 < ε ≤ w_s`,
moving `ε` of consumption from period `s` to period `t` at `x*` strictly lowers utility:
`u(x* + ε eₜ − ε eₛ) < u(x*)`. -/
theorem pec_equal_transfer_lowers_utility {s t : ℕ} (hst : s ≠ t) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε ≤ pecW s) :
    pecU (pecStar + (lp.single ∞ t ε : BddSeq ℝ) + (lp.single ∞ s (-ε) : BddSeq ℝ)) <
      pecU pecStar := by
  have hwt := pecW_pos t
  have hws := pecW_pos s
  rw [pecU_star_two_single hst (by linarith) (by linarith)]
  have ha : 0 < ε / pecW t := div_pos hε hwt
  have hb : 0 < ε / pecW s := div_pos hε hws
  have h1 := Real.add_one_lt_exp (neg_ne_zero.2 ha.ne')
  have h2 := Real.add_one_lt_exp hb.ne'
  have he := Real.exp_pos (-1)
  rw [neg_div, neg_neg]
  have g1 : pecW t * (1 - Real.exp (-(ε / pecW t))) < ε := by
    have : pecW t * (ε / pecW t) = ε := by field_simp
    nlinarith
  have g2 : ε < -(pecW s * (1 - Real.exp (ε / pecW s))) := by
    have : pecW s * (ε / pecW s) = ε := by field_simp
    nlinarith
  nlinarith

/-- **The corrected transfer.** For periods `s ≠ t` and `r > 1`, some `0 < ε < w_s` makes taking
`ε` from period `s` and giving `rε` to period `t` weakly raise utility at `x*`. -/
theorem pec_transfer_gain {s t : ℕ} (hst : s ≠ t) {r : ℝ} (hr : 1 < r) :
    ∃ ε > 0, ε < pecW s ∧ pecU pecStar ≤
      pecU (pecStar + (lp.single ∞ t (r * ε) : BddSeq ℝ) + (lp.single ∞ s (-ε) : BddSeq ℝ)) := by
  have hwt := pecW_pos t
  have hws := pecW_pos s
  have hK : 0 < 1 / pecW s + 1 / pecW t := by positivity
  set ε := (r - 1) / (r * (1 / pecW s + 1 / pecW t)) with hεdef
  have hr0 : 0 < r := by linarith
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεK : r * ε * (1 / pecW s + 1 / pecW t) = r - 1 := by
    rw [hεdef]; field_simp
  have hεs : ε < pecW s := by
    have h1 : r * ε / pecW s < r := by
      have : r * ε / pecW s + r * ε / pecW t = r - 1 := by rw [← hεK]; ring
      have : 0 < r * ε / pecW t := by positivity
      linarith
    rw [div_lt_iff₀ hws] at h1
    nlinarith
  refine ⟨ε, hε, hεs, ?_⟩
  rw [pecU_star_two_single hst (by positivity) (by linarith)]
  set a := r * ε / pecW t with ha
  set b := ε / pecW s with hb
  have ha0 : 0 ≤ a := by positivity
  have hb1 : b < 1 := (div_lt_one hws).2 hεs
  have hrel : r * (1 - b) = 1 + a := by
    have : r * ε / pecW s + r * ε / pecW t = r - 1 := by rw [← hεK]; ring
    rw [ha, hb]
    have : r * (ε / pecW s) = r * ε / pecW s := by ring
    linarith
  rw [neg_div, neg_neg]
  set A := Real.exp (-a)
  set B := Real.exp b
  have hA : A * (1 + a) ≤ 1 := by
    have h := Real.add_one_le_exp a
    have hm : A * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos (-a)
    nlinarith
  have hB : B * (1 - b) ≤ 1 := by
    have h := Real.add_one_le_exp (-b)
    have hm : B * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_pos b
    nlinarith
  have hwa : pecW t * a = r * ε := by rw [ha]; field_simp
  have hwb : pecW s * b = ε := by rw [hb]; field_simp
  have hX : r * ε ≤ pecW t * (1 - A) * (1 + a) := by nlinarith
  have hY : pecW s * (B - 1) * (1 - b) ≤ ε := by nlinarith
  have hY' : pecW s * (B - 1) * (1 + a) ≤ r * ε := by
    rw [← hrel]; nlinarith
  have hXY : pecW s * (B - 1) ≤ pecW t * (1 - A) := by
    have h1a : 0 < 1 + a := by linarith
    nlinarith
  have he := Real.exp_pos (-1)
  nlinarith

/-! ### Exercise 16.6(c) -/

/-- Unit vectors are finitely supported. -/
theorem pec_single_mem_seqC00 (t : ℕ) (a : ℝ) : (lp.single ∞ t a : BddSeq ℝ) ∈ seqC00 ℝ :=
  (eventually_gt_atTop t).mono fun q hq => by
    rw [lp.single_apply, Pi.single_eq_of_ne (ne_of_gt hq)]

/-- `ψ(x + a eₜ) = ψ(x) + a φ(eₜ)`. -/
theorem pec_seqRegularPart_add_single (φ : StrongDual ℝ (BddSeq ℝ)) (x : BddSeq ℝ) (t : ℕ)
    (a : ℝ) : seqRegularPart φ (x + lp.single ∞ t a) =
      seqRegularPart φ x + a * φ (lp.single ∞ t 1) := by
  rw [map_add, seqRegularPart_eq_of_mem_seqC00 φ (pec_single_mem_seqC00 t a)]
  have : (lp.single ∞ t a : BddSeq ℝ) = a • (lp.single ∞ t 1 : BddSeq ℝ) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul]

/-- Theorem 15.6 for the §16.6 economy: if `φ` satisfies (1) and (2), so does `ψ`. -/
theorem pec_regular_supports {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) :
    (∀ z ∈ pecX, pecU pecStar ≤ pecU z → seqRegularPart φ pecStar ≤ seqRegularPart φ z) ∧
    ∀ w ∈ pecY, seqRegularPart φ w ≤ seqRegularPart φ pecStar := by
  obtain ⟨r1, r2, -, -⟩ := theorem_15_6 (x₀ := fun _ => pecStar) (y₀ := fun _ => pecStar)
    pec_assumption15_1 pec_assumption15_2 pec_assumption15_6 pec_assumption15_7
    ((pec_feasible_iff _ _).2 ⟨pecStar_mem_pecX, pecStar_mem_pecY, rfl⟩) φ
    (fun _ => h1) (fun _ => h2) (fun _ => ⟨_, pec_nonsatiated.1, pec_nonsatiated.2⟩)
  exact ⟨r1 (), r2 ()⟩

/-- The prices `p_t = φ(eₜ)` are nonnegative under (2): `y* − eₜ ∈ Y`. -/
theorem pec_price_nonneg {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) (t : ℕ) : 0 ≤ φ (lp.single ∞ t 1) := by
  have hmem : pecStar + (lp.single ∞ t (-1) : BddSeq ℝ) ∈ pecY := fun q => by
    rw [pec_add_single_apply]
    rcases eq_or_ne q t with rfl | hq
    · simp
    · simp [Function.update_of_ne hq]
  have := (pec_regular_supports h1 h2).2 _ hmem
  rw [pec_seqRegularPart_add_single] at this
  linarith

/-- The key step of Exercise 16.6(c), corrected: under (1)–(2) no period `t ≠ s` is strictly
cheaper than period `s`. -/
theorem pec_price_not_lt {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) {s t : ℕ} (hst : s ≠ t) :
    ¬ φ (lp.single ∞ t 1) < φ (lp.single ∞ s 1) := by
  intro hlt
  set ps := φ (lp.single ∞ s 1)
  set pt := φ (lp.single ∞ t 1)
  have hpt := pec_price_nonneg h1 h2 t
  have hsum : 0 < ps + pt := by linarith
  set r := 2 * ps / (ps + pt) with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hsum]; linarith
  have hrp : r * pt < ps := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ hsum]; nlinarith
  obtain ⟨ε, hε, hεs, hu⟩ := pec_transfer_gain hst hr1
  have hmem1 : pecStar + (lp.single ∞ t (r * ε) : BddSeq ℝ) ∈ pecX :=
    pec_add_single_mem pecStar_mem_pecX t (by simp; nlinarith [pecW_pos t])
  have hmem : pecStar + (lp.single ∞ t (r * ε) : BddSeq ℝ) + (lp.single ∞ s (-ε) : BddSeq ℝ) ∈
      pecX := pec_add_single_mem hmem1 s (by rw [pec_two_single_apply_s hst]; linarith)
  have := (pec_regular_supports h1 h2).1 _ hmem hu
  rw [pec_seqRegularPart_add_single, pec_seqRegularPart_add_single] at this
  nlinarith

/-- **Exercise 16.6(c)** (p. 495): if `φ ∈ (ℓ∞)*` satisfies (1) and (2), then its regular part
`ψ(x) = lim_T φ(xᵀ)` is identically zero. -/
theorem ex_16_6c {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) : seqRegularPart φ = 0 := by
  obtain ⟨hsumm, -, hrep⟩ := seqRegularPart_real φ
  have hp0 : ∀ s, φ (lp.single ∞ s 1) = 0 := by
    intro s
    refine le_antisymm (not_lt.1 fun hpos => ?_) (pec_price_nonneg h1 h2 s)
    have hlim := hsumm.of_abs.tendsto_atTop_zero
    obtain ⟨t, hts, ht⟩ := ((eventually_gt_atTop s).and
      (hlim.eventually (gt_mem_nhds hpos))).exists
    exact pec_price_not_lt h1 h2 (ne_of_lt hts) ht
  ext x
  refine (hrep x).unique ?_
  simp [hp0]

/-! ### The real conclusion of the example -/

/-- The truncations of `x*` converge to `x*` in `ℓ∞` (`x*_t → 0`). -/
theorem pec_tendsto_seqTrunc_star :
    Tendsto (fun T => seqTrunc T pecStar) atTop (𝓝 pecStar) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) tendsto_pecW
  refine lp.norm_le_of_forall_le (pecW_pos T).le fun t => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, seqTrunc_apply]
  split_ifs with h
  · simp [(pecW_pos T).le]
  · rw [zero_sub, norm_neg, pecStar_apply, Real.norm_eq_abs, abs_of_pos (pecW_pos t)]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- **Every supporting functional gives `x*` the value zero**: under (1)–(2), `φ(x*) = 0`. -/
theorem pec_phi_star_eq_zero {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) : φ pecStar = 0 := by
  have hψ := tendsto_apply_seqTrunc φ pecStar
  rw [ex_16_6c h1 h2, zero_apply] at hψ
  exact tendsto_nhds_unique ((φ.continuous.tendsto pecStar).comp pec_tendsto_seqTrunc_star) hψ

/-- Under (1)–(2), `φ` vanishes on finitely supported sequences. -/
theorem pec_phi_seqC00 {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) {x : BddSeq ℝ} (hx : x ∈ seqC00 ℝ) : φ x = 0 := by
  rw [← seqRegularPart_eq_of_mem_seqC00 φ hx, ex_16_6c h1 h2, zero_apply]

/-- Under (1)–(2), `φ ≥ 0` on `X`, so no consumption is cheaper than `x*`: the cheaper-point
hypothesis of the Remark after Theorem 15.4 fails for every supporting `φ`. -/
theorem pec_no_cheaper_point {φ : StrongDual ℝ (BddSeq ℝ)}
    (h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z)
    (h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar) : ∀ z ∈ pecX, φ pecStar ≤ φ z := by
  intro z hz
  have hmem : z + pecStar ∈ pecX := fun t => by
    rw [lp.coeFn_add, Pi.add_apply, pecStar_apply]; linarith [hz t, pecW_pos t]
  have hle : pecU pecStar ≤ pecU (z + pecStar) :=
    pecUfun_le pecStar_mem_pecX fun t => by
      rw [lp.coeFn_add, Pi.add_apply]; linarith [hz t]
  have := h1 _ hmem hle
  rw [map_add, pec_phi_star_eq_zero h1 h2] at this
  rw [pec_phi_star_eq_zero h1 h2]
  linarith

/-- `(x*, y*, φ)` is not a competitive equilibrium, for any `φ ∈ (ℓ∞)*`. -/
theorem pec_not_competitiveEq (φ : StrongDual ℝ (BddSeq ℝ)) :
    ¬ CompetitiveEq (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY)
      (fun _ => pecStar) (fun _ => pecStar) φ := by
  intro hCE
  have h1 : ∀ z ∈ pecX, pecU pecStar ≤ pecU z → φ pecStar ≤ φ z := fun z hz hle =>
    ce_cost_le_of_utility_le pec_localNonsatiation hCE () hz hle
  have h2 : ∀ w ∈ pecY, φ w ≤ φ pecStar := hCE.2.2 ()
  have hcost : φ (pecStar + lp.single ∞ 0 1) ≤ φ pecStar := by
    rw [map_add, pec_phi_seqC00 h1 h2 (pec_single_mem_seqC00 0 1), add_zero]
  have := hCE.2.1 () _ pec_nonsatiated.1 hcost
  exact absurd pec_nonsatiated.2 (not_lt.2 this)

/-- **The economy of §16.6 has no competitive equilibrium in `ℓ∞`**: by Theorem 15.3 an
equilibrium allocation would be Pareto optimal, hence `x* = y*`, and `pec_not_competitiveEq`. -/
theorem pec_no_competitiveEq :
    ¬ ∃ (x y : Unit → BddSeq ℝ) (φ : StrongDual ℝ (BddSeq ℝ)),
      CompetitiveEq (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY) x y φ := by
  rintro ⟨x, y, φ, hCE⟩
  obtain ⟨hx, hy⟩ := (pec_paretoOptimal_iff x y).1 (theorem_15_3 pec_localNonsatiation hCE)
  have hxf : x = fun _ => pecStar := funext fun i => by cases i; exact hx
  have hyf : y = fun _ => pecStar := funext fun i => by cases i; exact hy
  subst hxf hyf
  exact pec_not_competitiveEq φ hCE

/-- Theorem 15.4 applies (Exercise 16.6(a)): some `φ ≠ 0` satisfies (1) and (2). -/
theorem pec_supporting_exists :
    ∃ φ : StrongDual ℝ (BddSeq ℝ), φ ≠ 0 ∧
      SupportsAllocation (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY)
        (fun _ => pecStar) (fun _ => pecStar) φ :=
  theorem_15_4 (h := ()) pec_assumption15_1 pec_assumption15_2 pec_assumption15_3
    pec_assumption15_4 pec_assumption15_5 ((pec_paretoOptimal_iff _ _).2 ⟨rfl, rfl⟩)
    pec_nonsatiated.1 pec_nonsatiated.2

/-- **The real conclusion of §16.6.** In `ℓ∞`: the unique Pareto optimum `x* = y*` is supported by
some `φ ≠ 0` (Theorem 15.4); every supporting `φ` has regular part `ψ = 0` (Theorem 15.6 gives
only the zero functional), `φ(x*) = 0`, and no cheaper point; and there is no competitive
equilibrium at all. -/
theorem pec_real_conclusion :
    (∃ φ : StrongDual ℝ (BddSeq ℝ), φ ≠ 0 ∧
      SupportsAllocation (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY)
        (fun _ => pecStar) (fun _ => pecStar) φ) ∧
    (∀ φ : StrongDual ℝ (BddSeq ℝ),
      SupportsAllocation (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY)
        (fun _ => pecStar) (fun _ => pecStar) φ →
      seqRegularPart φ = 0 ∧ φ pecStar = 0 ∧ ¬ ∃ z ∈ pecX, φ z < φ pecStar) ∧
    ¬ ∃ (x y : Unit → BddSeq ℝ) (φ : StrongDual ℝ (BddSeq ℝ)),
      CompetitiveEq (fun _ : Unit => pecX) (fun _ : Unit => pecU) (fun _ : Unit => pecY) x y φ :=
  ⟨pec_supporting_exists, fun _ hφ => ⟨ex_16_6c (hφ.1 ()) (hφ.2 ()),
    pec_phi_star_eq_zero (hφ.1 ()) (hφ.2 ()), fun ⟨z, hz, hlt⟩ =>
      absurd (pec_no_cheaper_point (hφ.1 ()) (hφ.2 ()) z hz) (not_le.2 hlt)⟩,
    pec_no_competitiveEq⟩

end StokeyLucasPrescott.EquilibriumApplications
