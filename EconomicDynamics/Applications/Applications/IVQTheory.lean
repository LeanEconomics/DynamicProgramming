/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.EUTools
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# §8.6.2 Q theory of investment

Miao, §8.6.2, pp. 278–280. The firm maximises `Σ βᵗ[π(Kₜ) − Iₜ − Ψ(Iₜ, Kₜ)]` subject to
`K_{t+1} = (1 − δ)Kₜ + Iₜ` (8.29), with convex adjustment cost `Ψ`.

* `iv_HasPartials Ψ a b p`: `Ψ` is (Fréchet) differentiable at `p` with partial derivatives
  `Ψ₁(p) = a`, `Ψ₂(p) = b`.
* (8.30)–(8.31) are derived by perturbing `K_{t+1}` (`eq_8_30_8_31`), with `Qₜ = 1 + Ψ₁(Iₜ, Kₜ)`.
* Investment increases with `Q` when `Ψ` is convex in `I` (`iv_invest_mono`). **Correction**:
  the book's assumptions `Ψ₁ > 0`, `Ψ₁₁ < 0` (with `Ψ ≥ 0`, `Ψ(0, ·) = 0`) are inconsistent
  (`iv_psi_assumptions_inconsistent`), and with `Ψ₁₁ < 0` investment would *decrease* in `Q`
  (`iv_invest_anti_of_concave`); the intended assumptions are `Ψ₁₁ > 0` and `Ψ₁` with the sign of
  `I` (as in §8.6.3, `Ψ₁(0, K) = 0`).
* (8.33): forward iteration of (8.31) (`iv_Q_iterate`) and the present-value formula
  (`eq_8_33`) under the book's condition `lim βᵀ(1 − δ)ᵀQ_{T+1} = 0`. **Correction**: that
  condition does not follow from the transversality condition (8.32) in general
  (`iv_tvc_not_implies`: negative investment); it does when `Q ≥ 0` and investment is
  nonnegative (`iv_tvc_implies`).
* Hayashi's result: Euler's theorem for linearly homogeneous `Ψ` (`iv_euler_homog`), the
  one-step identity `QₜK_{t+1} = β[AK_{t+1} − Ψ_{t+1} − I_{t+1}] + βK_{t+2}Q_{t+1}`
  (`iv_hayashi_step`), its iteration (`iv_hayashi_iterate`) and the limit
  `QₜK_{t+1} = Σ_{j ≥ 1} βʲ[π(K_{t+j}) − I_{t+j} − Ψ(I_{t+j}, K_{t+j})]` under (8.32)
  (`iv_hayashi`), i.e. marginal Q equals average Q (`iv_marginal_eq_average`).
* Sufficiency (not stated in the book, which only writes the conditions): when
  `(I, K) ↦ π(K) − I − Ψ(I, K)` is concave, a plan satisfying (8.30)–(8.31) with `Q ≥ 0` beats
  every feasible plan with nonnegative capital up to the term `βᵀQ_TK*_{T+1}`
  (`iv_q_sufficient`), so with (8.32) it is optimal (`iv_q_optimal`).
-/

namespace Miao.Applications

open Filter Topology

/-- `Ψ : ℝ × ℝ → ℝ` is differentiable at `p` with partial derivatives `Ψ₁(p) = a` and
`Ψ₂(p) = b`. -/
def iv_HasPartials (Ψ : ℝ × ℝ → ℝ) (a b : ℝ) (p : ℝ × ℝ) : Prop :=
  HasFDerivAt Ψ (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) p

/-- The derivative of `Ψ` along a differentiable path `k ↦ (x k, y k)`. -/
theorem iv_HasPartials.comp {Ψ : ℝ × ℝ → ℝ} {a b : ℝ} {x y : ℝ → ℝ} {x' y' k : ℝ}
    (hΨ : iv_HasPartials Ψ a b (x k, y k)) (hx : HasDerivAt x x' k) (hy : HasDerivAt y y' k) :
    HasDerivAt (fun s => Ψ (x s, y s)) (a * x' + b * y') k := by
  unfold iv_HasPartials at hΨ
  have := HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun s => (x s, y s)) k hΨ
    (HasDerivAt.prodMk hx hy)
  simpa [Function.comp_def, smul_eq_mul] using this

/-- Miao, (8.30)–(8.31), p. 278. Substitute `Iₜ = k − (1 − δ)Kₜ` and
`I_{t+1} = K_{t+2} − (1 − δ)k`; the terms of the objective involving `k = K_{t+1}` are
`βᵗ[π(Kₜ) − Iₜ − Ψ(Iₜ, Kₜ)] + β^{t+1}[π(k) − I_{t+1} − Ψ(I_{t+1}, k)]`. If `K_{t+1}` maximises
them locally then, with `Qₜ = 1 + Ψ₁(Iₜ, Kₜ)` (8.30) and `Q_{t+1} = 1 + Ψ₁(I_{t+1}, K_{t+1})`,
`Qₜ = β[π′(K_{t+1}) − Ψ₂(I_{t+1}, K_{t+1})] + β(1 − δ)Q_{t+1}` (8.31). -/
theorem eq_8_30_8_31 {prof : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} {β δ Kt K1 K2 dpr a0 b0 a1 b1 : ℝ}
    {t : ℕ} (hβ : 0 < β) (hpr : HasDerivAt prof dpr K1)
    (hΨ0 : iv_HasPartials Ψ a0 b0 (K1 - (1 - δ) * Kt, Kt))
    (hΨ1 : iv_HasPartials Ψ a1 b1 (K2 - (1 - δ) * K1, K1))
    (hmax : IsLocalMax (fun k => β ^ t * (prof Kt - (k - (1 - δ) * Kt) - Ψ (k - (1 - δ) * Kt, Kt))
      + β ^ (t + 1) * (prof k - (K2 - (1 - δ) * k) - Ψ (K2 - (1 - δ) * k, k))) K1) :
    1 + a0 = β * (dpr - b1) + β * (1 - δ) * (1 + a1) := by
  have d0 : HasDerivAt (fun k => Ψ (k - (1 - δ) * Kt, Kt)) (a0 * 1 + b0 * 0) K1 :=
    hΨ0.comp (x := fun k => k - (1 - δ) * Kt) (y := fun _ => Kt)
      ((hasDerivAt_id K1).sub_const _) (hasDerivAt_const K1 Kt)
  have d1 : HasDerivAt (fun k => Ψ (K2 - (1 - δ) * k, k)) (a1 * (0 - (1 - δ) * 1) + b1 * 1)
      K1 :=
    hΨ1.comp (x := fun k => K2 - (1 - δ) * k) (y := fun k => k)
      ((hasDerivAt_const K1 K2).sub ((hasDerivAt_id K1).const_mul _)) (hasDerivAt_id K1)
  have d : HasDerivAt (fun k => β ^ t * (prof Kt - (k - (1 - δ) * Kt) - Ψ (k - (1 - δ) * Kt, Kt))
      + β ^ (t + 1) * (prof k - (K2 - (1 - δ) * k) - Ψ (K2 - (1 - δ) * k, k)))
      (β ^ t * (0 - 1 - (a0 * 1 + b0 * 0)) + β ^ (t + 1) * (dpr - (0 - (1 - δ) * 1)
        - (a1 * (0 - (1 - δ) * 1) + b1 * 1))) K1 := by
    apply HasDerivAt.add
    · exact (((hasDerivAt_const K1 _).sub ((hasDerivAt_id K1).sub_const _)).sub d0).const_mul _
    · exact ((hpr.sub ((hasDerivAt_const K1 _).sub ((hasDerivAt_id K1).const_mul _))).sub
        d1).const_mul _
  have e := hmax.hasDerivAt_eq_zero d
  have hbt : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at e
  have : β ^ t * (β * (dpr - b1) + β * (1 - δ) * (1 + a1) - (1 + a0)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- Miao, p. 279: "(8.30) shows that investment increases with `Q`". If `Ψ₁(·, K)` is strictly
increasing (`Ψ` strictly convex in `I`, i.e. `Ψ₁₁ > 0`) and `1 + Ψ₁(I, K) = Q`,
`1 + Ψ₁(I′, K) = Q′` with `Q < Q′`, then `I < I′`. -/
theorem iv_invest_mono {Ψ1 : ℝ → ℝ} (hmono : StrictMono Ψ1) {I I' Q Q' : ℝ}
    (h : 1 + Ψ1 I = Q) (h' : 1 + Ψ1 I' = Q') (hQ : Q < Q') : I < I' := by
  by_contra hc
  have := hmono.monotone (not_lt.1 hc)
  linarith

/-- **Correction** to Miao, p. 278: with the printed assumption `Ψ₁₁ < 0` (`Ψ₁(·, K)` strictly
decreasing) investment would *decrease* with `Q`. -/
theorem iv_invest_anti_of_concave {Ψ1 : ℝ → ℝ} (hanti : StrictAnti Ψ1) {I I' Q Q' : ℝ}
    (h : 1 + Ψ1 I = Q) (h' : 1 + Ψ1 I' = Q') (hQ : Q < Q') : I' < I := by
  by_contra hc
  have := hanti.antitone (not_lt.1 hc)
  linarith

/-- **Correction** to Miao, p. 278: the assumptions on `Ψ : ℝ × ℝ₊ → ℝ₊` cannot all hold.
No function `Ψ(·, K)` of `I` satisfies `Ψ(0, K) = 0`, `Ψ ≥ 0` and `Ψ₁ > 0` everywhere: it
would be strictly increasing, so `Ψ(−1, K) < 0`. -/
theorem iv_psi_assumptions_inconsistent :
    ¬ ∃ (Ψ Ψ1 : ℝ → ℝ), Ψ 0 = 0 ∧ (∀ I, 0 ≤ Ψ I) ∧ (∀ I, HasDerivAt Ψ (Ψ1 I) I) ∧
      ∀ I, 0 < Ψ1 I := by
  rintro ⟨Ψ, Ψ1, h0, hnn, hd, hpos⟩
  have := strictMono_of_hasDerivAt_pos hd hpos (show (-1 : ℝ) < 0 by norm_num)
  linarith [hnn (-1)]

/-- Miao, p. 279: forward iteration of (8.31), `Qₜ = βmₜ₊₁ + β(1 − δ)Q_{t+1}` with
`mₛ = π′(Kₛ) − Ψ₂(Iₛ, Kₛ)`:
`Qₜ = Σ_{j<T} β^{j+1}(1 − δ)ʲ m_{t+j+1} + βᵀ(1 − δ)ᵀQ_{t+T}`. -/
theorem iv_Q_iterate {β δ : ℝ} {Q m : ℕ → ℝ}
    (h : ∀ t, Q t = β * m (t + 1) + β * (1 - δ) * Q (t + 1)) (t T : ℕ) :
    Q t = ∑ j ∈ Finset.range T, β ^ (j + 1) * (1 - δ) ^ j * m (t + j + 1)
      + β ^ T * (1 - δ) ^ T * Q (t + T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, h (t + n), show t + (n + 1) = t + n + 1 by omega]
    ring

/-- The shifted tail condition: from `βᵀ(1 − δ)ᵀQ_{T+1} → 0` (with `β(1 − δ) > 0`) we get
`βᵀ(1 − δ)ᵀQ_{t+T} → 0` for every `t`. -/
theorem iv_tail_shift {c : ℝ} (hc : 0 < c) {Q : ℕ → ℝ}
    (h : Tendsto (fun T => c ^ T * Q (T + 1)) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => c ^ T * Q (t + T)) atTop (𝓝 0) := by
  have hy : Tendsto (fun n => c ^ n * Q n) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have := h.const_mul c
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    rw [pow_succ]
    ring
  have h2 : Tendsto (fun T => (c ^ t)⁻¹ * (c ^ (T + t) * Q (T + t))) atTop (𝓝 0) := by
    have := ((tendsto_add_atTop_iff_nat t).2 hy).const_mul (c ^ t)⁻¹
    rw [mul_zero] at this
    exact this
  refine h2.congr fun T => ?_
  have : c ^ t ≠ 0 := (pow_pos hc t).ne'
  rw [pow_add, add_comm T t]
  field_simp

/-- Miao, (8.33), p. 279: under (8.31) and the book's condition
`lim_{T→∞} βᵀ(1 − δ)ᵀQ_{T+1} = 0`,
`Qₜ = Σ_{j ≥ 1} βʲ(1 − δ)^{j−1}[π′(K_{t+j}) − Ψ₂(I_{t+j}, K_{t+j})]`
(as the limit of the partial sums), for every `t`. -/
theorem eq_8_33 {β δ : ℝ} (hβ : 0 < β) (hδ : δ < 1) {Q m : ℕ → ℝ}
    (h : ∀ t, Q t = β * m (t + 1) + β * (1 - δ) * Q (t + 1))
    (htail : Tendsto (fun T => β ^ T * (1 - δ) ^ T * Q (T + 1)) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ (j + 1) * (1 - δ) ^ j * m (t + j + 1))
      atTop (𝓝 (Q t)) := by
  have hc : 0 < β * (1 - δ) := mul_pos hβ (by linarith)
  have h1 : Tendsto (fun T => (β * (1 - δ)) ^ T * Q (T + 1)) atTop (𝓝 0) := by
    refine htail.congr fun T => ?_
    rw [mul_pow]
  have h2 := iv_tail_shift hc h1 t
  have h3 : Tendsto (fun T => Q t - β ^ T * (1 - δ) ^ T * Q (t + T)) atTop (𝓝 (Q t - 0)) :=
    tendsto_const_nhds.sub (h2.congr fun T => by rw [mul_pow])
  rw [sub_zero] at h3
  refine h3.congr fun T => ?_
  rw [iv_Q_iterate h t T]
  ring

/-- **Correction** to Miao, p. 279: the condition `lim βᵀ(1 − δ)ᵀQ_{T+1} = 0` does *not* follow
from the transversality condition (8.32) in general. With `β = δ = 1/2`, `Qₜ = 4ᵗ`,
`Kₜ = 4^{−t}` (so `Iₜ = −Kₜ/4 < 0`, and (8.31) holds with `π′ = Ψ₂`), (8.32) holds:
`βᵀQ_TK_{T+1} = 2^{−T}/4 → 0`, but `βᵀ(1 − δ)ᵀQ_{T+1} = 4` for all `T`. -/
theorem iv_tvc_not_implies :
    let β : ℝ := 1 / 2
    let δ : ℝ := 1 / 2
    let Q : ℕ → ℝ := fun t => 4 ^ t
    let K : ℕ → ℝ := fun t => (1 / 4) ^ t
    (∀ t, Q t = β * 0 + β * (1 - δ) * Q (t + 1)) ∧ (∀ t, 0 < K t ∧ 0 < Q t) ∧
      Tendsto (fun T => β ^ T * Q T * K (T + 1)) atTop (𝓝 0) ∧
      ¬ Tendsto (fun T => β ^ T * (1 - δ) ^ T * Q (T + 1)) atTop (𝓝 0) := by
  intro β δ Q K
  refine ⟨fun t => ?_, fun t => ⟨by positivity, by positivity⟩, ?_, ?_⟩
  · simp only [β, δ, Q, pow_succ]; ring
  · have : Tendsto (fun T : ℕ => (1 / 4 : ℝ) * (1 / 2) ^ T) atTop (𝓝 ((1 / 4) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    simp only [β, Q, K, pow_succ, ← mul_pow]
    have h2 : (2 : ℝ) ^ T * (1 / 4) ^ T = (1 / 2) ^ T := by rw [← mul_pow]; norm_num
    linear_combination (-1 / 4 : ℝ) * h2
  · intro hT
    have h4 : (fun T => β ^ T * (1 - δ) ^ T * Q (T + 1)) = fun _ => (4 : ℝ) := by
      funext T
      simp only [β, δ, Q, pow_succ, ← mul_pow]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    rw [h4] at hT
    have := tendsto_nhds_unique hT tendsto_const_nhds
    norm_num at this

/-- Miao, p. 279, corrected: if `Qₜ ≥ 0`, investment is nonnegative (`K_{t+1} ≥ (1 − δ)Kₜ`),
`K₀ > 0`, `0 < β` and `0 < δ < 1`, then the transversality condition (8.32)
`βᵀQ_TK_{T+1} → 0` implies `βᵀ(1 − δ)ᵀQ_{T+1} → 0`. -/
theorem iv_tvc_implies {β δ : ℝ} (hβ : 0 < β) (hδ : δ < 1) {Q K : ℕ → ℝ}
    (hQ : ∀ t, 0 ≤ Q t) (hK0 : 0 < K 0) (hI : ∀ t, (1 - δ) * K t ≤ K (t + 1))
    (htvc : Tendsto (fun T => β ^ T * Q T * K (T + 1)) atTop (𝓝 0)) :
    Tendsto (fun T => β ^ T * (1 - δ) ^ T * Q (T + 1)) atTop (𝓝 0) := by
  have h1δ : 0 < 1 - δ := by linarith
  have hKlow : ∀ n, (1 - δ) ^ n * K 0 ≤ K n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (1 - δ) ^ (n + 1) * K 0 = (1 - δ) * ((1 - δ) ^ n * K 0) := by ring
        _ ≤ (1 - δ) * K n := mul_le_mul_of_nonneg_left ih h1δ.le
        _ ≤ K (n + 1) := hI n
  set c := β * (1 - δ) ^ 2 * K 0 with hc
  have hc0 : 0 < c := by positivity
  have hup : Tendsto (fun T => c⁻¹ * (β ^ (T + 1) * Q (T + 1) * K (T + 1 + 1))) atTop
      (𝓝 (c⁻¹ * 0)) :=
    ((tendsto_add_atTop_iff_nat 1).2 htvc).const_mul _
  rw [mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun T => ?_)
    (fun T => ?_)
  · have := hQ (T + 1)
    positivity
  · simp only
    rw [le_inv_mul_iff₀ hc0]
    have hk := hKlow (T + 2)
    have hq : 0 ≤ β ^ (T + 1) * Q (T + 1) := mul_nonneg (pow_nonneg hβ.le _) (hQ _)
    calc c * (β ^ T * (1 - δ) ^ T * Q (T + 1))
        = β ^ (T + 1) * Q (T + 1) * ((1 - δ) ^ (T + 2) * K 0) := by rw [hc]; ring
      _ ≤ β ^ (T + 1) * Q (T + 1) * K (T + 1 + 1) := mul_le_mul_of_nonneg_left hk hq

/-- Miao, p. 280 (Euler's theorem for linearly homogeneous functions): if
`Ψ(λI, λK) = λΨ(I, K)` for all `λ > 0` and `Ψ` has partial derivatives `Ψ₁ = a`, `Ψ₂ = b` at
`(I, K)`, then `Ψ(I, K) = IΨ₁ + KΨ₂`, i.e. `Ψ₂ = (Ψ − IΨ₁)/K`. -/
theorem iv_euler_homog {Ψ : ℝ × ℝ → ℝ} {I K a b : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → Ψ (l * I, l * K) = l * Ψ (I, K))
    (hd : iv_HasPartials Ψ a b (I, K)) : Ψ (I, K) = I * a + K * b := by
  have hd' : iv_HasPartials Ψ a b ((fun l : ℝ => l * I) 1, (fun l : ℝ => l * K) 1) := by
    simpa using hd
  have d1 : HasDerivAt (fun l : ℝ => Ψ (l * I, l * K)) (a * I + b * K) 1 := by
    have := hd'.comp ((hasDerivAt_id (1 : ℝ)).mul_const I) ((hasDerivAt_id (1 : ℝ)).mul_const K)
    simpa using this
  have d2 : HasDerivAt (fun l : ℝ => Ψ (l * I, l * K)) (Ψ (I, K)) 1 := by
    have h0 : HasDerivAt (fun l : ℝ => l * Ψ (I, K)) (1 * Ψ (I, K)) 1 :=
      (hasDerivAt_id (1 : ℝ)).mul_const _
    rw [one_mul] at h0
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with l hl
    exact hhom l hl
  have := d1.unique d2
  linarith

/-- Miao, p. 280, the one-step identity behind Hayashi's result. With `π(K) = AK`, (8.30) at
`t + 1` (`Q_{t+1} = 1 + Ψ₁`), (8.31) at `t`, Euler's identity `Ψ = IΨ₁ + KΨ₂` at
`(I_{t+1}, K_{t+1})` and `K_{t+2} = (1 − δ)K_{t+1} + I_{t+1}`:
`QₜK_{t+1} = β[AK_{t+1} − Ψ(I_{t+1}, K_{t+1}) − I_{t+1}] + βK_{t+2}Q_{t+1}`. -/
theorem iv_hayashi_step {β δ A Qt Qt1 K1 K2 I1 Ψv a b : ℝ} (h830 : Qt1 = 1 + a)
    (h831 : Qt = β * (A - b) + β * (1 - δ) * Qt1) (heuler : Ψv = I1 * a + K1 * b)
    (hK : K2 = (1 - δ) * K1 + I1) :
    Qt * K1 = β * (A * K1 - Ψv - I1) + β * K2 * Qt1 := by
  subst h830 h831 heuler hK
  ring

/-- Miao, p. 280: iterating `iv_hayashi_step`,
`QₜK_{t+1} = Σ_{j<T} β^{j+1}D_{t+j+1} + βᵀQ_{t+T}K_{t+T+1}` where `D` is the dividend. -/
theorem iv_hayashi_iterate {β : ℝ} {Q K D : ℕ → ℝ}
    (h : ∀ t, Q t * K (t + 1) = β * D (t + 1) + β * K (t + 2) * Q (t + 1)) (t T : ℕ) :
    Q t * K (t + 1) = ∑ j ∈ Finset.range T, β ^ (j + 1) * D (t + j + 1)
      + β ^ T * Q (t + T) * K (t + T + 1) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show t + (n + 1) = t + n + 1 by omega]
    have := h (t + n)
    rw [show t + n + 2 = t + n + 1 + 1 by omega] at this
    linear_combination β ^ n * this

/-- **Hayashi's result** (Miao, pp. 279–280). Let `π(K) = AK`, `Ψ` linearly homogeneous with
partial derivatives `Ψ₁, Ψ₂` along the plan, and let `(Iₜ, Kₜ, Qₜ)` satisfy (8.29), (8.30),
(8.31) and the transversality condition (8.32). Then for every `t`
`QₜK_{t+1} = Σ_{j ≥ 1} βʲ[π(K_{t+j}) − I_{t+j} − Ψ(I_{t+j}, K_{t+j})]` (limit of partial sums):
marginal `Q` times the capital stock is the ex-dividend value of the firm. -/
theorem iv_hayashi {β δ A : ℝ} (hβ : 0 < β) {Ψ : ℝ × ℝ → ℝ} {Ψ1 Ψ2 : ℕ → ℝ}
    {Q I K : ℕ → ℝ} (hhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Ψ (l * p.1, l * p.2) = l * Ψ p)
    (hd : ∀ t, iv_HasPartials Ψ (Ψ1 t) (Ψ2 t) (I t, K t))
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + I t) (h830 : ∀ t, Q t = 1 + Ψ1 t)
    (h831 : ∀ t, Q t = β * (A - Ψ2 (t + 1)) + β * (1 - δ) * Q (t + 1))
    (h832 : Tendsto (fun T => β ^ T * Q T * K (T + 1)) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T,
      β ^ (j + 1) * (A * K (t + j + 1) - I (t + j + 1) - Ψ (I (t + j + 1), K (t + j + 1))))
      atTop (𝓝 (Q t * K (t + 1))) := by
  have hstep : ∀ s, Q s * K (s + 1) = β * (A * K (s + 1) - I (s + 1) - Ψ (I (s + 1), K (s + 1)))
      + β * K (s + 2) * Q (s + 1) := by
    intro s
    have he := iv_euler_homog (fun l hl => hhom l (I (s + 1), K (s + 1)) hl) (hd (s + 1))
    have := iv_hayashi_step (h830 (s + 1)) (h831 s) he (hK (s + 1))
    rw [this]
    ring
  have hres : Tendsto (fun T => β ^ T * Q (t + T) * K (t + T + 1)) atTop (𝓝 0) := by
    have h2 := ((tendsto_add_atTop_iff_nat t).2 h832).const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    have : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [pow_add, add_comm T t]
    field_simp
  have h3 : Tendsto (fun T => Q t * K (t + 1) - β ^ T * Q (t + T) * K (t + T + 1)) atTop
      (𝓝 (Q t * K (t + 1) - 0)) := tendsto_const_nhds.sub hres
  rw [sub_zero] at h3
  refine h3.congr fun T => ?_
  rw [iv_hayashi_iterate (D := fun s => A * K s - I s - Ψ (I s, K s)) hstep t T]
  ring

/-- Miao, p. 280: **marginal Q equals average Q**. Under the hypotheses of `iv_hayashi`, if
`K_{t+1} > 0`, then `Qₜ = Vₜ/K_{t+1}` where `Vₜ` is the ex-dividend value of the firm
(`Σ_{j ≥ 1} βʲ` dividends) divided by the replacement cost of its capital. -/
theorem iv_marginal_eq_average {β δ A : ℝ} (hβ : 0 < β) {Ψ : ℝ × ℝ → ℝ} {Ψ1 Ψ2 : ℕ → ℝ}
    {Q I K : ℕ → ℝ} (hhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Ψ (l * p.1, l * p.2) = l * Ψ p)
    (hd : ∀ t, iv_HasPartials Ψ (Ψ1 t) (Ψ2 t) (I t, K t))
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + I t) (h830 : ∀ t, Q t = 1 + Ψ1 t)
    (h831 : ∀ t, Q t = β * (A - Ψ2 (t + 1)) + β * (1 - δ) * Q (t + 1))
    (h832 : Tendsto (fun T => β ^ T * Q T * K (T + 1)) atTop (𝓝 0)) (t : ℕ)
    (hKpos : 0 < K (t + 1)) {V : ℝ}
    (hV : Tendsto (fun T => ∑ j ∈ Finset.range T,
      β ^ (j + 1) * (A * K (t + j + 1) - I (t + j + 1) - Ψ (I (t + j + 1), K (t + j + 1))))
      atTop (𝓝 V)) :
    Q t = V / K (t + 1) := by
  have := tendsto_nhds_unique hV (iv_hayashi hβ hhom hd hK h830 h831 h832 t)
  rw [this]
  field_simp

/-- The one-period reward of the Q-theory firm, `f(I, K) = π(K) − I − Ψ(I, K)`. -/
def iv_qReward (prof : ℝ → ℝ) (Ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := prof p.2 - p.1 - Ψ p

/-- The derivative of the reward `f(I, K) = π(K) − I − Ψ(I, K)`. -/
theorem iv_qReward_hasFDerivAt {prof : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {dpr a b : ℝ}
    (hpr : HasDerivAt prof dpr p.2) (hΨ : iv_HasPartials Ψ a b p) (v : ℝ × ℝ) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (iv_qReward prof Ψ) L p ∧
      L v = dpr * v.2 - v.1 - (a * v.1 + b * v.2) := by
  refine ⟨dpr • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ -
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ), ?_, by simp⟩
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => prof q.2) (dpr • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hpr.comp_hasFDerivAt p (hasFDerivAt_snd)
  exact (h1.sub hasFDerivAt_fst).sub hΨ

/-- Sufficiency of (8.30)–(8.31) (Miao, pp. 278–279; the book only writes the conditions). Let
`f(I, K) = π(K) − I − Ψ(I, K)` be concave on a convex set `S`, and let the plan `(I*, K*)` with
multipliers `Q ≥ 0` satisfy (8.29), (8.30) `Qₜ = 1 + Ψ₁(I*ₜ, K*ₜ)` and (8.31). Then every
plan `(I, K)` with the same `K₀`, satisfying (8.29), with `(Iₜ, Kₜ) ∈ S` and `Kₜ ≥ 0`, satisfies
`Σ_{t≤T} βᵗf(Iₜ, Kₜ) ≤ Σ_{t≤T} βᵗf(I*ₜ, K*ₜ) + βᵀQ_TK*_{T+1}` for every `T`. -/
theorem iv_q_sufficient {prof : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {β δ : ℝ}
    (hβ : 0 ≤ β) (hf : ConcaveOn ℝ S (iv_qReward prof Ψ)) {Is Ks I K Q dpr a b : ℕ → ℝ}
    (hpr : ∀ t, HasDerivAt prof (dpr t) (Ks t))
    (hΨ : ∀ t, iv_HasPartials Ψ (a t) (b t) (Is t, Ks t))
    (hKs : ∀ t, Ks (t + 1) = (1 - δ) * Ks t + Is t) (hSs : ∀ t, (Is t, Ks t) ∈ S)
    (h830 : ∀ t, Q t = 1 + a t)
    (h831 : ∀ t, Q t = β * (dpr (t + 1) - b (t + 1)) + β * (1 - δ) * Q (t + 1))
    (hQ : ∀ t, 0 ≤ Q t)
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + I t) (hS : ∀ t, (I t, K t) ∈ S)
    (hK0 : K 0 = Ks 0) (hKnn : ∀ t, 0 ≤ K t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * iv_qReward prof Ψ (I t, K t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * iv_qReward prof Ψ (Is t, Ks t)
        + β ^ T * Q T * Ks (T + 1) := by
  have grad : ∀ t, iv_qReward prof Ψ (I t, K t) ≤ iv_qReward prof Ψ (Is t, Ks t)
      - Q t * (I t - Is t) + (dpr t - b t) * (K t - Ks t) := by
    intro t
    obtain ⟨L, hL, hLv⟩ := iv_qReward_hasFDerivAt (p := (Is t, Ks t)) (hpr t) (hΨ t)
      ((I t, K t) - (Is t, Ks t))
    have := eu_concave_le_fderiv hf (hSs t) (hS t) hL
    rw [hLv] at this
    simp only [Prod.fst_sub, Prod.snd_sub] at this
    rw [h830 t]
    linarith
  have main : ∀ T, ∑ t ∈ Finset.range (T + 1), β ^ t * (iv_qReward prof Ψ (I t, K t)
      - iv_qReward prof Ψ (Is t, Ks t)) ≤ -(β ^ T * Q T * (K (T + 1) - Ks (T + 1))) := by
    intro T
    induction T with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul]
      have := grad 0
      have hI : I 0 - Is 0 = K 1 - Ks 1 := by rw [hK 0, hKs 0, hK0]; ring
      rw [hI, hK0, sub_self, mul_zero, add_zero] at this
      rw [hK0]
      linarith
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have g := mul_le_mul_of_nonneg_left (grad (n + 1)) (pow_nonneg hβ (n + 1))
      have key : β ^ (n + 1) * ((1 - δ) * Q (n + 1) + (dpr (n + 1) - b (n + 1))) =
          β ^ n * Q n := by rw [h831 n, pow_succ]; ring
      have hI : I (n + 1) - Is (n + 1) = (K (n + 1 + 1) - Ks (n + 1 + 1))
          - (1 - δ) * (K (n + 1) - Ks (n + 1)) := by rw [hK (n + 1), hKs (n + 1)]; ring
      rw [hI] at g
      have e : β ^ (n + 1) * (iv_qReward prof Ψ (Is (n + 1), Ks (n + 1)) - Q (n + 1) *
          ((K (n + 1 + 1) - Ks (n + 1 + 1)) - (1 - δ) * (K (n + 1) - Ks (n + 1)))
          + (dpr (n + 1) - b (n + 1)) * (K (n + 1) - Ks (n + 1))) =
          β ^ (n + 1) * iv_qReward prof Ψ (Is (n + 1), Ks (n + 1))
          - β ^ (n + 1) * Q (n + 1) * (K (n + 1 + 1) - Ks (n + 1 + 1))
          + β ^ (n + 1) * ((1 - δ) * Q (n + 1) + (dpr (n + 1) - b (n + 1)))
            * (K (n + 1) - Ks (n + 1)) := by ring
      rw [e, key] at g
      nlinarith
  have hm := main T
  rw [Finset.sum_congr rfl (fun t _ => mul_sub (β ^ t) _ _), Finset.sum_sub_distrib] at hm
  have hnn : 0 ≤ β ^ T * Q T * K (T + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hβ T) (hQ T)) (hKnn (T + 1))
  nlinarith

/-- Optimality of the Q-theory plan (Miao, pp. 278–279): under the hypotheses of
`iv_q_sufficient` and the transversality condition (8.32) `βᵀQ_TK*_{T+1} → 0`, if the
discounted rewards of the plan `(I*, K*)` converge to `J*` and those of a competing plan converge
to `J`, then `J ≤ J*`. -/
theorem iv_q_optimal {prof : ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {β δ : ℝ}
    (hβ : 0 ≤ β) (hf : ConcaveOn ℝ S (iv_qReward prof Ψ)) {Is Ks I K Q dpr a b : ℕ → ℝ}
    (hpr : ∀ t, HasDerivAt prof (dpr t) (Ks t))
    (hΨ : ∀ t, iv_HasPartials Ψ (a t) (b t) (Is t, Ks t))
    (hKs : ∀ t, Ks (t + 1) = (1 - δ) * Ks t + Is t) (hSs : ∀ t, (Is t, Ks t) ∈ S)
    (h830 : ∀ t, Q t = 1 + a t)
    (h831 : ∀ t, Q t = β * (dpr (t + 1) - b (t + 1)) + β * (1 - δ) * Q (t + 1))
    (hQ : ∀ t, 0 ≤ Q t)
    (h832 : Tendsto (fun T => β ^ T * Q T * Ks (T + 1)) atTop (𝓝 0))
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + I t) (hS : ∀ t, (I t, K t) ∈ S)
    (hK0 : K 0 = Ks 0) (hKnn : ∀ t, 0 ≤ K t) {J Js : ℝ}
    (hJs : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * iv_qReward prof Ψ (Is t, Ks t))
      atTop (𝓝 Js))
    (hJ : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * iv_qReward prof Ψ (I t, K t))
      atTop (𝓝 J)) : J ≤ Js := by
  have hsum := hJs.add h832
  rw [add_zero] at hsum
  exact le_of_tendsto_of_tendsto hJ hsum (Eventually.of_forall fun T =>
    iv_q_sufficient hβ hf hpr hΨ hKs hSs h830 h831 hQ hK hS hK0 hKnn T)

end Miao.Applications
