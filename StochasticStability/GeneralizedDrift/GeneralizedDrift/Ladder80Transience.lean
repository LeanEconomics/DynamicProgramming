/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.LadderExample
import GeneralizedDrift.DriftCriteria

/-!
# Transience of the bottom rung of the chain (19.80) (MT p. 506)

Meyn and Tweedie, (19.80)–(19.81), p. 506: the up-or-down ladder chain with the bottom rung
(19.80) (`ladderChainKernel (exLam p q) (ex80Star p q r)`, `LadderExample`) "is transient on
`[0]` if `r` and `q` are small enough, and `p − ½` is not too large". The book argues through the
mean increment (19.81) of the process on `[0]`; here the claim is quantified and proved with a
test function on the whole ladder.

* `eq_19_81_transient`: if `q < ½` and `D = (1 − q)(1 − 2r) − q(2p − 1)(1 + 1/(1 − 2q)) > 0`,
  there are `θ > 0` and `K` with `P_{(i,x)}(σ_{[0] ∩ {⌊x⌋₊ ≤ M}} < ∞) ≤ e^{−θ(⌊x⌋₊ − Ki − M)}`.
  From `(0, x)` with `⌊x⌋₊ > M` the process on `[0]` never returns below level `M` with
  positive probability, which tends to `1` as `x → ∞`.
* The proof: `W(i, x) = ⌊x⌋₊ − Ki` with `K = (2p − 1)/(1 − 2q) + D/2` has mean increments
  bounded below by a positive `δ` both on `[0]` (where the rung goes up with probability `q`
  and `X` moves with `r`) and above it (rung up `q`, down `1 − q`, `X` moves with `p`), and the
  increments are bounded, so `e^{−θW}` is superharmonic for small `θ` (`ex80_exists_test`,
  `four_exp_le`, `ex80_superharmonic`). Proposition 8.4.1 (`proposition_8_4_1`) then bounds the
  hitting probability.
* `lintegral_ladderChainKernel`, `lintegral_twoPoint`: integrals against the ladder kernel and
  the two-point moves.

**Remarks.** `D > 0` is exactly the condition that the mean increment of `X` over one step of the
process on `[0]` is positive: `(1 − q)(1 − 2r) + q(1 − 2p)(1 + E[L])`, where
`E[L] = 1/(1 − 2q)` is the mean time for the rung walk to return from rung `1` to rung `0`.
The book's (19.81) uses `(1 − q)/(1 − 2q)` for this mean, which is smaller (not formalised).
The book's qualitative condition ("`r` and `q` small enough, `p − ½` not too large") gives `D > 0`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- `eᵘ ≤ 1 + u + u²` for `|u| ≤ 1`. -/
theorem exp_le_quad {u : ℝ} (hu : |u| ≤ 1) : Real.exp u ≤ 1 + u + u ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le hu
  have := le_abs_self (Real.exp u - 1 - u)
  linarith

/-- One term of the exponential bound: `w e^{θc} ≤ w (1 + θc + θ²B²)` for `|c| ≤ B`, `θB ≤ 1`. -/
theorem mul_exp_le {w c B θ : ℝ} (hw : 0 ≤ w) (hc : |c| ≤ B) (hθ0 : 0 ≤ θ) (hθB : θ * B ≤ 1) :
    w * Real.exp (θ * c) ≤ w * (1 + θ * c + θ ^ 2 * B ^ 2) := by
  refine mul_le_mul_of_nonneg_left ?_ hw
  have hu : |θ * c| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_left hc hθ0).trans hθB
  refine (exp_le_quad hu).trans ?_
  have hc2 : c ^ 2 ≤ B ^ 2 := by
    have := abs_nonneg c
    nlinarith [sq_abs c]
  nlinarith [sq_nonneg θ]

/-- **The exponential test for four moves**: weights `wⱼ ≥ 0` summing to `1`, increments
`|cⱼ| ≤ B` with `Σ wⱼ cⱼ ≤ −δ`, and `0 ≤ θ`, `θB ≤ 1`, `θB² ≤ δ` give `Σ wⱼ e^{θcⱼ} ≤ 1`. -/
theorem four_exp_le {w₁ w₂ w₃ w₄ c₁ c₂ c₃ c₄ B δ θ : ℝ} (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂)
    (h₃ : 0 ≤ w₃) (h₄ : 0 ≤ w₄) (hsum : w₁ + w₂ + w₃ + w₄ = 1) (hc₁ : |c₁| ≤ B)
    (hc₂ : |c₂| ≤ B) (hc₃ : |c₃| ≤ B) (hc₄ : |c₄| ≤ B)
    (hdrift : w₁ * c₁ + w₂ * c₂ + w₃ * c₃ + w₄ * c₄ ≤ -δ) (hθ0 : 0 ≤ θ) (hθB : θ * B ≤ 1)
    (hθδ : θ * B ^ 2 ≤ δ) :
    w₁ * Real.exp (θ * c₁) + w₂ * Real.exp (θ * c₂) + w₃ * Real.exp (θ * c₃) +
      w₄ * Real.exp (θ * c₄) ≤ 1 := by
  have e₁ := mul_exp_le h₁ hc₁ hθ0 hθB
  have e₂ := mul_exp_le h₂ hc₂ hθ0 hθB
  have e₃ := mul_exp_le h₃ hc₃ hθ0 hθB
  have e₄ := mul_exp_le h₄ hc₄ hθ0 hθB
  have hsq : θ ^ 2 * B ^ 2 ≤ θ * δ := by
    have := mul_le_mul_of_nonneg_left hθδ hθ0
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hdrift hθ0
  have hexp : w₁ * (1 + θ * c₁ + θ ^ 2 * B ^ 2) + w₂ * (1 + θ * c₂ + θ ^ 2 * B ^ 2) +
      w₃ * (1 + θ * c₃ + θ ^ 2 * B ^ 2) + w₄ * (1 + θ * c₄ + θ ^ 2 * B ^ 2) =
      (w₁ + w₂ + w₃ + w₄) * (1 + θ ^ 2 * B ^ 2) +
        θ * (w₁ * c₁ + w₂ * c₂ + w₃ * c₃ + w₄ * c₄) := by ring
  rw [hsum] at hexp
  linarith

/-- Integrating against the ladder chain: `∫ f dP(i, x) = ∫ f(0, ·) dΛ*ᵢ(x) +
Σ_{k ≤ i} ∫ f(i + 1 − k, ·) dΛₖ(x)`. -/
theorem lintegral_ladderChainKernel (Λ Λs : ℕ → Kernel ℝ ℝ) (i : ℕ) (x : ℝ)
    {f : ℕ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂ladderChainKernel Λ Λs (i, x) = ∫⁻ y, f (0, y) ∂Λs i x +
      ∑ k ∈ Finset.range (i + 1), ∫⁻ y, f (i + 1 - k, y) ∂Λ k x := by
  rw [ladderChainKernel_apply, ladderRow, FunLike.coe_add, Pi.add_apply, lintegral_add_measure,
    Kernel.map_apply _ measurable_prodMk_left, lintegral_map hf measurable_prodMk_left,
    Kernel.sum_apply, lintegral_sum_measure, tsum_fintype]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∫⁻ y, f (i + 1 - k, y) ∂Λ k x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Kernel.map_apply _ measurable_prodMk_left, lintegral_map hf measurable_prodMk_left]

/-- `∫ g d(a δ_{x−1} + b δ_{x+1}) = a g(x − 1) + b g(x + 1)`. -/
theorem lintegral_twoPoint (a b : ℝ≥0∞) (x : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂twoPoint a b x = a * g (exDown x) + b * g (exUp x) := by
  change ∫⁻ y, g y ∂(a • Measure.dirac (exDown x) + b • Measure.dirac (exUp x)) = _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hg, lintegral_dirac' _ hg, smul_eq_mul, smul_eq_mul]

/-- The level function `W(i, x) = ⌊x⌋₊ − K i`. -/
noncomputable def ex80W (K : ℝ) (z : ℕ × ℝ) : ℝ := (⌊z.2⌋₊ : ℝ) - K * z.1

/-- The exponential test function `e^{−θW}`. -/
noncomputable def ex80V (K θ : ℝ) (z : ℕ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-θ * ex80W K z))

theorem measurable_ex80V (K θ : ℝ) : Measurable (ex80V K θ) := by
  have h1 : Measurable fun z : ℕ × ℝ => ((⌊z.2⌋₊ : ℕ) : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      (Nat.measurable_floor.comp measurable_snd)
  have h2 : Measurable fun z : ℕ × ℝ => ((z.1 : ℕ) : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_fst
  unfold ex80V ex80W
  fun_prop

theorem floor_exDown (x : ℝ) : ⌊exDown x⌋₊ = ⌊x⌋₊ - 1 := by
  rw [exDown, Nat.floor_natCast]

theorem floor_exUp (x : ℝ) : ⌊exUp x⌋₊ = ⌊x⌋₊ + 1 := by
  rw [exUp, Nat.floor_natCast]

/-- A move down on `X` lowers the level by at most one. -/
theorem ex80V_down (K : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (j : ℕ) (x : ℝ) :
    ex80V K θ (j, exDown x) ≤
      ENNReal.ofReal (Real.exp (-θ * ((⌊x⌋₊ : ℝ) - 1 - K * j))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [ex80W, floor_exDown]
  have : ((⌊x⌋₊ : ℝ) - 1) ≤ ((⌊x⌋₊ - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h | h
    · rw [h]; norm_num
    · rw [Nat.cast_sub h]; simp
  simp only
  nlinarith

theorem ex80V_up (K θ : ℝ) (j : ℕ) (x : ℝ) :
    ex80V K θ (j, exUp x) = ENNReal.ofReal (Real.exp (-θ * ((⌊x⌋₊ : ℝ) + 1 - K * j))) := by
  rw [ex80V, ex80W, floor_exUp]
  push_cast
  rfl

/-- The two-point integral of `e^{−θW}` on rung `j`. -/
theorem lintegral_twoPoint_ex80V (K : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (j : ℕ) (x : ℝ) :
    ∫⁻ y, ex80V K θ (j, y) ∂twoPoint (ENNReal.ofReal a) (ENNReal.ofReal b) x ≤
      ENNReal.ofReal (a * Real.exp (-θ * ((⌊x⌋₊ : ℝ) - 1 - K * j)) +
        b * Real.exp (-θ * ((⌊x⌋₊ : ℝ) + 1 - K * j))) := by
  rw [lintegral_twoPoint (g := fun y => ex80V K θ (j, y)) _ _ _
      ((measurable_ex80V K θ).comp measurable_prodMk_left),
    ex80V_up, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul hb]
  exact add_le_add (mul_le_mul' le_rfl (ex80V_down K hθ j x)) le_rfl

theorem exLam_zero_eq (p q : ℝ) :
    exLam p q 0 = twoPoint (ENNReal.ofReal (p * q)) (ENNReal.ofReal ((1 - p) * q)) := by
  simp [exLam]

theorem exLam_two_eq (p q : ℝ) :
    exLam p q 2 =
      twoPoint (ENNReal.ofReal (p * (1 - q))) (ENNReal.ofReal ((1 - p) * (1 - q))) := by
  simp [exLam]

theorem exLam_other (p q : ℝ) {k : ℕ} (h0 : k ≠ 0) (h2 : k ≠ 2) : exLam p q k = 0 := by
  simp [exLam, h0, h2]

/-- `e^{−θ(n − 1 − K j)} = e^{−θ(n − K i)} e^{θc}` for `c = K(j − i) + 1`. -/
theorem exp_down (θ n K i j c : ℝ) (hc : K * (j - i) + 1 = c) :
    Real.exp (-θ * (n - 1 - K * j)) = Real.exp (-θ * (n - K * i)) * Real.exp (θ * c) := by
  rw [← Real.exp_add, ← hc]; congr 1; ring

/-- `e^{−θ(n + 1 − K j)} = e^{−θ(n − K i)} e^{θc}` for `c = K(j − i) − 1`. -/
theorem exp_up (θ n K i j c : ℝ) (hc : K * (j - i) - 1 = c) :
    Real.exp (-θ * (n + 1 - K * j)) = Real.exp (-θ * (n - K * i)) * Real.exp (θ * c) := by
  rw [← Real.exp_add, ← hc]; congr 1; ring

/-- **`e^{−θW}` is superharmonic for the chain (19.80)** when the exponential tests at rung `0`
and above rung `0` hold. -/
theorem ex80_superharmonic {p q r K θ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hθ : 0 ≤ θ)
    (h0 : p * q * Real.exp (θ * (1 + K)) + (1 - p) * q * Real.exp (θ * (K - 1)) +
      r * (1 - q) * Real.exp (θ * 1) + (1 - r) * (1 - q) * Real.exp (θ * (-1)) ≤ 1)
    (h1 : p * q * Real.exp (θ * (1 + K)) + (1 - p) * q * Real.exp (θ * (K - 1)) +
      p * (1 - q) * Real.exp (θ * (1 - K)) + (1 - p) * (1 - q) * Real.exp (θ * (-1 - K)) ≤ 1)
    (z : ℕ × ℝ) :
    ∫⁻ w, ex80V K θ w ∂ladderChainKernel (exLam p q) (ex80Star p q r) z ≤ ex80V K θ z := by
  obtain ⟨i, x⟩ := z
  have hq' : 0 ≤ 1 - q := by linarith
  have hp' : 0 ≤ 1 - p := by linarith
  have hr' : 0 ≤ 1 - r := by linarith
  rw [lintegral_ladderChainKernel _ _ i x (measurable_ex80V K θ)]
  set n : ℝ := (⌊x⌋₊ : ℝ) with hn
  set E := Real.exp (-θ * (n - K * i)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hVz : ex80V K θ (i, x) = ENNReal.ofReal E := rfl
  rw [hVz]
  -- the up-rung part `Λ₀` to rung `i + 1`
  have hup : ∫⁻ y, ex80V K θ (i + 1, y) ∂exLam p q 0 x ≤ ENNReal.ofReal
      (p * q * (E * Real.exp (θ * (1 + K))) + (1 - p) * q * (E * Real.exp (θ * (K - 1)))) := by
    rw [exLam_zero_eq]
    refine (lintegral_twoPoint_ex80V K hθ (by positivity) (by positivity) (i + 1) x).trans
      (le_of_eq ?_)
    congr 1
    rw [exp_down θ n K i ((i + 1 : ℕ) : ℝ) (1 + K) (by push_cast; ring),
      exp_up θ n K i ((i + 1 : ℕ) : ℝ) (K - 1) (by push_cast; ring), ← hE]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have hstay : ∫⁻ y, ex80V K θ (0, y) ∂ex80Star p q r 0 x ≤ ENNReal.ofReal
        (r * (1 - q) * (E * Real.exp (θ * 1)) +
          (1 - r) * (1 - q) * (E * Real.exp (θ * (-1)))) := by
      simp only [ex80Star, ↓reduceIte]
      refine (lintegral_twoPoint_ex80V K hθ (by positivity) (by positivity) 0 x).trans
        (le_of_eq ?_)
      congr 1
      rw [exp_down θ n K ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) 1 (by ring),
        exp_up θ n K ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) (-1) (by ring), ← hE]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
    calc _ ≤ ENNReal.ofReal (r * (1 - q) * (E * Real.exp (θ * 1)) +
            (1 - r) * (1 - q) * (E * Real.exp (θ * (-1)))) + ENNReal.ofReal
            (p * q * (E * Real.exp (θ * (1 + K))) +
              (1 - p) * q * (E * Real.exp (θ * (K - 1)))) := add_le_add hstay (by simpa using hup)
      _ ≤ ENNReal.ofReal E := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    -- the down-rung part to rung `j`
    have hdown2 : ∫⁻ y, ex80V K θ (j, y) ∂twoPoint (ENNReal.ofReal (p * (1 - q)))
        (ENNReal.ofReal ((1 - p) * (1 - q))) x ≤ ENNReal.ofReal
        (p * (1 - q) * (E * Real.exp (θ * (1 - K))) +
          (1 - p) * (1 - q) * (E * Real.exp (θ * (-1 - K)))) := by
      refine (lintegral_twoPoint_ex80V K hθ (by positivity) (by positivity) j x).trans
        (le_of_eq ?_)
      congr 1
      rw [exp_down θ n K ((j + 1 : ℕ) : ℝ) (j : ℝ) (1 - K) (by push_cast; ring),
        exp_up θ n K ((j + 1 : ℕ) : ℝ) (j : ℝ) (-1 - K) (by push_cast; ring), ← hE]
    have hsplit : ∫⁻ y, ex80V K θ (0, y) ∂ex80Star p q r (j + 1) x +
        ∑ k ∈ Finset.range (j + 1 + 1), ∫⁻ y, ex80V K θ (j + 1 + 1 - k, y) ∂exLam p q k x =
        ∫⁻ y, ex80V K θ (j, y) ∂twoPoint (ENNReal.ofReal (p * (1 - q)))
          (ENNReal.ofReal ((1 - p) * (1 - q))) x +
        ∫⁻ y, ex80V K θ (j + 1 + 1, y) ∂exLam p q 0 x := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simp only [ex80Star, zero_add, one_ne_zero, ↓reduceIte]
        rw [Finset.sum_range_succ, Finset.sum_range_one, exLam_other p q one_ne_zero
          (by norm_num)]
        simp
      · rw [show ex80Star p q r (j + 1) = 0 by simp [ex80Star, show j ≠ 0 by omega]]
        rw [Finset.sum_eq_add 0 2 (by norm_num) (fun k _ hk => by
          rw [exLam_other p q hk.1 hk.2]; simp) (fun h => absurd (Finset.mem_range.2 (by omega)) h)
          (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
        rw [exLam_two_eq, show j + 1 + 1 - 2 = j by omega]
        simp [add_comm]
    rw [hsplit]
    calc _ ≤ ENNReal.ofReal (p * (1 - q) * (E * Real.exp (θ * (1 - K))) +
            (1 - p) * (1 - q) * (E * Real.exp (θ * (-1 - K)))) + ENNReal.ofReal
            (p * q * (E * Real.exp (θ * (1 + K))) +
              (1 - p) * q * (E * Real.exp (θ * (K - 1)))) := add_le_add hdown2 hup
      _ ≤ ENNReal.ofReal E := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith

/-- **The choice of `K` and `θ`**: if `q < ½` and
`D = (1 − q)(1 − 2r) − q(2p − 1)(1 + 1/(1 − 2q)) > 0`, the level `W = ⌊x⌋₊ − K i` with
`K = (2p − 1)/(1 − 2q) + D/2` has positive mean increments at rung `0` and above it, and for small
`θ > 0` the exponential tests of `ex80_superharmonic` hold. -/
theorem ex80_exists_test {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq : q < 1 / 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hD : 0 < (1 - q) * (1 - 2 * r) - q * (2 * p - 1) * (1 + (1 - 2 * q)⁻¹)) :
    ∃ K θ : ℝ, 0 < θ ∧
      p * q * Real.exp (θ * (1 + K)) + (1 - p) * q * Real.exp (θ * (K - 1)) +
        r * (1 - q) * Real.exp (θ * 1) + (1 - r) * (1 - q) * Real.exp (θ * (-1)) ≤ 1 ∧
      p * q * Real.exp (θ * (1 + K)) + (1 - p) * q * Real.exp (θ * (K - 1)) +
        p * (1 - q) * Real.exp (θ * (1 - K)) + (1 - p) * (1 - q) * Real.exp (θ * (-1 - K)) ≤ 1 := by
  set D := (1 - q) * (1 - 2 * r) - q * (2 * p - 1) * (1 + (1 - 2 * q)⁻¹) with hDdef
  have h2q : 0 < 1 - 2 * q := by linarith
  set t := D / 2 with ht
  have ht0 : 0 < t := by positivity
  set K := (2 * p - 1) / (1 - 2 * q) + t with hK
  set B := 1 + |K| with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith [abs_nonneg K]
  have hB0 : 0 < B := by linarith
  set δ := min (t * (1 - 2 * q)) (3 * D / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  set θ := min (1 / B) (δ / B ^ 2) with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) (by positivity)
  have hθB : θ * B ≤ 1 := by
    have := min_le_left (1 / B) (δ / B ^ 2)
    rw [← hθ] at this
    calc θ * B ≤ 1 / B * B := mul_le_mul_of_nonneg_right this hB0.le
      _ = 1 := by field_simp
  have hθδ : θ * B ^ 2 ≤ δ := by
    have := min_le_right (1 / B) (δ / B ^ 2)
    rw [← hθ] at this
    calc θ * B ^ 2 ≤ δ / B ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = δ := by field_simp
  have hc1 : |1 + K| ≤ B := (abs_add_le _ _).trans (by rw [abs_one])
  have hc2 : |K - 1| ≤ B := (abs_sub _ _).trans (by rw [abs_one, hB]; linarith)
  have hc3 : |1 - K| ≤ B := (abs_sub _ _).trans (by rw [abs_one, hB])
  have hc4 : |-1 - K| ≤ B := (abs_sub _ _).trans (by rw [abs_neg, abs_one, hB])
  have hc5 : |(1 : ℝ)| ≤ B := by rw [abs_one]; exact hB1
  have hc6 : |(-1 : ℝ)| ≤ B := by rw [abs_neg, abs_one]; exact hB1
  have hKe : K * (1 - 2 * q) = 2 * p - 1 + t * (1 - 2 * q) := by
    rw [hK, add_mul, div_mul_cancel₀ _ h2q.ne']
  have hDe : q * (2 * p - 1) * (1 + (1 - 2 * q)⁻¹) =
      q * (2 * p - 1) + q * ((2 * p - 1) / (1 - 2 * q)) := by
    rw [div_eq_mul_inv]; ring
  have hw1 : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hw2 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith) hq0
  have hw3 : 0 ≤ r * (1 - q) := mul_nonneg hr0 (by linarith)
  have hw4 : 0 ≤ (1 - r) * (1 - q) := mul_nonneg (by linarith) (by linarith)
  have hw5 : 0 ≤ p * (1 - q) := mul_nonneg hp0 (by linarith)
  have hw6 : 0 ≤ (1 - p) * (1 - q) := mul_nonneg (by linarith) (by linarith)
  have hdr0 : p * q * (1 + K) + (1 - p) * q * (K - 1) + r * (1 - q) * 1 +
      (1 - r) * (1 - q) * (-1) ≤ -δ := by
    -- rung `0`: mean increment of `W` is `D − qt ≥ 3D/4`
    have h1 : δ ≤ 3 * D / 4 := min_le_right _ _
    have hqt : q * t ≤ t / 2 := by nlinarith
    have hK' : q * K = q * ((2 * p - 1) / (1 - 2 * q)) + q * t := by rw [hK]; ring
    have e : p * q * (1 + K) + (1 - p) * q * (K - 1) + r * (1 - q) * 1 +
        (1 - r) * (1 - q) * (-1) = q * K + q * (2 * p - 1) - (1 - q) * (1 - 2 * r) := by ring
    rw [e]
    nlinarith
  have hdr1 : p * q * (1 + K) + (1 - p) * q * (K - 1) + p * (1 - q) * (1 - K) +
      (1 - p) * (1 - q) * (-1 - K) ≤ -δ := by
    -- above rung `0`: mean increment of `W` is `t(1 − 2q)`
    have h1 : δ ≤ t * (1 - 2 * q) := min_le_left _ _
    have e : p * q * (1 + K) + (1 - p) * q * (K - 1) + p * (1 - q) * (1 - K) +
        (1 - p) * (1 - q) * (-1 - K) = (2 * p - 1) - K * (1 - 2 * q) := by ring
    rw [e, hKe]
    linarith
  have hf0 := four_exp_le hw1 hw2 hw3 hw4 (by ring) hc1 hc2 hc5 hc6 hdr0 hθ0.le hθB hθδ
  have hf1 := four_exp_le hw1 hw2 hw5 hw6 (by ring) hc1 hc2 hc3 hc4 hdr1 hθ0.le hθB hθδ
  exact ⟨K, θ, hθ0, hf0, hf1⟩

/-- **(19.81), quantified: the chain (19.80) is transient on `[0]`** (MT p. 506). If `q < ½` and
`(1 − q)(1 − 2r) − q(2p − 1)(1 + 1/(1 − 2q)) > 0` (true when `r` and `q` are small and
`p − ½` is not too large), there are `θ > 0` and `K` such that from any state `(i, x)` the
probability of ever entering `[0] ∩ {⌊x⌋₊ ≤ M}` is at most `e^{−θ(⌊x⌋₊ − Ki − M)}`; in particular
from `(0, x)` with `⌊x⌋₊ > M` the process on `[0]` never returns below `M` with positive
probability, and this probability tends to `1` as `x → ∞`. -/
theorem eq_19_81_transient {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq : q < 1 / 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hD : 0 < (1 - q) * (1 - 2 * r) - q * (2 * p - 1) * (1 + (1 - 2 * q)⁻¹)) :
    haveI := isMarkovKernel_ex80 hp0 hp1 hq0 (by linarith) hr0 hr1
    ∃ θ : ℝ, 0 < θ ∧ ∃ K : ℝ, ∀ (M : ℕ) (z : ℕ × ℝ),
      hitProbZero (ladderChainKernel (exLam p q) (ex80Star p q r))
        {w | w.1 = 0 ∧ ⌊w.2⌋₊ ≤ M} z ≤
        ENNReal.ofReal (Real.exp (-θ * ((⌊z.2⌋₊ : ℝ) - K * z.1 - M))) := by
  have := isMarkovKernel_ex80 hp0 hp1 hq0 (by linarith) hr0 hr1
  obtain ⟨K, θ, hθ, h0, h1⟩ := ex80_exists_test hp0 hp1 hq0 hq hr0 hr1 hD
  refine ⟨θ, hθ, K, fun M z => ?_⟩
  set P := ladderChainKernel (exLam p q) (ex80Star p q r)
  have hC : MeasurableSet {w : ℕ × ℝ | w.1 = 0 ∧ ⌊w.2⌋₊ ≤ M} :=
    (measurable_fst (measurableSet_singleton 0)).inter
      ((Nat.measurable_floor.comp measurable_snd) measurableSet_Iic)
  set h : ℕ × ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (θ * M)) * ex80V K θ w with hh
  have hsup : ∀ x ∉ {w : ℕ × ℝ | w.1 = 0 ∧ ⌊w.2⌋₊ ≤ M}, ∫⁻ y, h y ∂P x ≤ h x := fun x _ => by
    simp only [hh]
    rw [lintegral_const_mul _ (measurable_ex80V K θ)]
    exact mul_le_mul' le_rfl (ex80_superharmonic hp0 hp1 hq0 (by linarith) hr0 hr1 hθ.le h0 h1 x)
  have hC1 : ∀ x ∈ {w : ℕ × ℝ | w.1 = 0 ∧ ⌊w.2⌋₊ ≤ M}, 1 ≤ h x := fun x hx => by
    obtain ⟨hx1, hx2⟩ := hx
    simp only [hh]
    rw [ex80V, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    rw [ex80W, hx1]
    have : (⌊x.2⌋₊ : ℝ) ≤ M := by exact_mod_cast hx2
    push_cast
    nlinarith
  refine ((proposition_8_4_1 P hC).2.2 h hsup hC1 z).trans (le_of_eq ?_)
  simp only [hh]
  rw [ex80V, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ex80W]
  congr 2
  ring

end MeynTweedie.GeneralizedDrift
