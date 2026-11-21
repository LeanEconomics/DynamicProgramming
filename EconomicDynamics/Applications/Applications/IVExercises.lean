/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.IVQTheory
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Exercises 8.12 and 8.13 (Q theory)

Miao, §8.7, Exercises 12–13, pp. 289–290.

**Exercise 8.12** (Hayashi's result from the Bellman equation). With `π(K) = AK` and `Ψ`
linearly homogeneous, the Bellman equation is
`V(K) = max_I AK − I − Ψ(I, K) + βV((1 − δ)K + I)` (`iv_bellRHS`, `iv_SolvesBellman`; we
require the next capital stock to be positive).
* If `V` solves it, so does `K ↦ λ⁻¹V(λK)` (`ex_8_12_scaling`); hence a unique solution is
  linearly homogeneous, `V(K) = V(1)K` (`ex_8_12_homog`).
* The first-order condition `1 + Ψ₁(I, K) = βV′(K′)` (`ex_8_12_foc`) and the envelope
  condition `V′(K) = A − Ψ₂(I, K) + β(1 − δ)V′(K′)` (`ex_8_12_envelope`) are (8.30)–(8.31) with
  `Qₜ = βV′(K_{t+1})`: **marginal Q is the discounted marginal value of capital installed for
  next period**.
* With `V(K) = vK`, marginal `Q = βv = βV(K_{t+1})/K_{t+1}` is average Q, and
  `QK_{t+1} = Σ_{j≥1} βʲ` dividends under the transversality condition (`ex_8_12_hayashi`).

**Exercise 8.13**: `max Σ βᵗ[AKₜ − Iₜ − Iₜ²/(2Kₜ)]`, `K_{t+1} = Iₜ + (1 − δ)Kₜ`, `β = 1/(1 + r)`.
With `D = (r + δ)² + 2(r + δ) − 2A` and `i = r + δ − √D`:
* the adjustment cost is convex and the reward concave on `K > 0` (`iv_concave13`);
* the plan `Iₜ = iKₜ`, `Kₜ = (1 − δ + i)ᵗK₀`, `Qₜ = 1 + i` satisfies (8.30)–(8.32)
  (`ex_8_13_foc`, `ex_8_13_tvc`) when `D > 0`;
* the value of the firm is `V(K₀) = (1 + r)(1 + i)K₀` (`ex_8_13_value`), and the plan is
  optimal (`ex_8_13`). Conditions for a finite value: `D > 0` (and `1 − δ + i > 0` so that
  capital stays positive). If `D < 0` the value is infinite (`ex_8_13_unbounded`).
-/

namespace Miao.Applications

open Filter Topology

/-- The right side of the Bellman equation of Exercise 8.12 (Miao, p. 289):
`AK − I − Ψ(I, K) + βV((1 − δ)K + I)`. -/
def iv_bellRHS (A β δ : ℝ) (Ψ : ℝ × ℝ → ℝ) (V : ℝ → ℝ) (K I : ℝ) : ℝ :=
  A * K - I - Ψ (I, K) + β * V ((1 - δ) * K + I)

/-- `V` solves the Bellman equation of Exercise 8.12 on `K > 0`: for every `K > 0` the
maximum over investments `I` with `(1 − δ)K + I > 0` of `iv_bellRHS` is attained and equals
`V(K)`. -/
def iv_SolvesBellman (A β δ : ℝ) (Ψ : ℝ × ℝ → ℝ) (V : ℝ → ℝ) : Prop :=
  ∀ K, 0 < K → (∀ I, 0 < (1 - δ) * K + I → iv_bellRHS A β δ Ψ V K I ≤ V K) ∧
    ∃ I, 0 < (1 - δ) * K + I ∧ iv_bellRHS A β δ Ψ V K I = V K

/-- **Exercise 8.12** (Miao, p. 289): if `Ψ` is linearly homogeneous and `V` solves the
Bellman equation, so does `K ↦ λ⁻¹V(λK)` for every `λ > 0`. -/
theorem ex_8_12_scaling {A β δ : ℝ} {Ψ : ℝ × ℝ → ℝ} {V : ℝ → ℝ}
    (hhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Ψ (l * p.1, l * p.2) = l * Ψ p)
    (hV : iv_SolvesBellman A β δ Ψ V) {l : ℝ} (hl : 0 < l) :
    iv_SolvesBellman A β δ Ψ (fun K => l⁻¹ * V (l * K)) := by
  have key : ∀ K I, iv_bellRHS A β δ Ψ (fun K => l⁻¹ * V (l * K)) K I =
      l⁻¹ * iv_bellRHS A β δ Ψ V (l * K) (l * I) := by
    intro K I
    unfold iv_bellRHS
    have := hhom l (I, K) hl
    simp only at this ⊢
    rw [this, show l * ((1 - δ) * K + I) = (1 - δ) * (l * K) + l * I by ring]
    field_simp
  intro K hK
  obtain ⟨hle, I, hI, heq⟩ := hV (l * K) (mul_pos hl hK)
  refine ⟨fun J hJ => ?_, l⁻¹ * I, ?_, ?_⟩
  · rw [key]
    have := hle (l * J) (by nlinarith)
    exact mul_le_mul_of_nonneg_left this (inv_pos.2 hl).le
  · have : 0 < l⁻¹ * ((1 - δ) * (l * K) + I) := mul_pos (inv_pos.2 hl) hI
    have e : l⁻¹ * ((1 - δ) * (l * K) + I) = (1 - δ) * K + l⁻¹ * I := by field_simp
    linarith
  · rw [key, show l * (l⁻¹ * I) = I by field_simp, heq]

/-- **Exercise 8.12** (Miao, p. 289): if the Bellman equation has a unique solution `V` on
`K > 0`, then `V` is linearly homogeneous, `V(K) = V(1)K`. -/
theorem ex_8_12_homog {A β δ : ℝ} {Ψ : ℝ × ℝ → ℝ} {V : ℝ → ℝ}
    (hhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Ψ (l * p.1, l * p.2) = l * Ψ p)
    (hV : iv_SolvesBellman A β δ Ψ V)
    (huniq : ∀ W, iv_SolvesBellman A β δ Ψ W → ∀ K, 0 < K → W K = V K) {K : ℝ}
    (hK : 0 < K) : V K = V 1 * K := by
  have := huniq _ (ex_8_12_scaling hhom hV hK) 1 one_pos
  rw [mul_one] at this
  rw [← this]
  field_simp

/-- **Exercise 8.12** (Miao, p. 289), the first-order condition: if `I*` maximises the right
side of the Bellman equation locally, `V` is differentiable at `K′ = (1 − δ)K + I*` and `Ψ`
has partial derivatives `Ψ₁ = a`, `Ψ₂ = b` at `(I*, K)`, then `1 + Ψ₁(I*, K) = βV′(K′)`:
(8.30) with `Q = βV′(K′)`. -/
theorem ex_8_12_foc {A β δ K I dV a b : ℝ} {Ψ : ℝ × ℝ → ℝ} {V : ℝ → ℝ}
    (hmax : IsLocalMax (iv_bellRHS A β δ Ψ V K) I)
    (hVd : HasDerivAt V dV ((1 - δ) * K + I)) (hΨ : iv_HasPartials Ψ a b (I, K)) :
    1 + a = β * dV := by
  have d1 : HasDerivAt (fun J => Ψ (J, K)) (a * 1 + b * 0) I :=
    hΨ.comp (x := fun J => J) (y := fun _ => K) (hasDerivAt_id I) (hasDerivAt_const I K)
  have d2 : HasDerivAt (fun J => V ((1 - δ) * K + J)) dV I := by
    have hin : HasDerivAt (fun J : ℝ => (1 - δ) * K + J) 1 I := by
      simpa using (hasDerivAt_id I).const_add ((1 - δ) * K)
    have h := hVd.comp I hin
    rw [mul_one] at h
    exact h
  have d : HasDerivAt (iv_bellRHS A β δ Ψ V K) (0 - 1 - (a * 1 + b * 0) + β * dV) I :=
    (((hasDerivAt_const I (A * K)).sub (hasDerivAt_id I)).sub d1).add (d2.const_mul β)
  have := hmax.hasDerivAt_eq_zero d
  linarith

/-- **Exercise 8.12** (Miao, p. 289), the envelope condition: if `V(k) ≥ Ak − I* − Ψ(I*, k) +
βV((1 − δ)k + I*)` for `k` near `K` with equality at `K` (the Bellman equation with `I*`
optimal at `K`), `V` is differentiable at `K` and at `K′ = (1 − δ)K + I*`, and `Ψ` has partial
derivatives `a, b` at `(I*, K)`, then `V′(K) = A − Ψ₂(I*, K) + β(1 − δ)V′(K′)`. With
`Q_{t−1} = βV′(Kₜ)` and `Qₜ = βV′(K_{t+1})` this is (8.31). -/
theorem ex_8_12_envelope {A β δ K I dV0 dV1 a b : ℝ} {Ψ : ℝ × ℝ → ℝ} {V : ℝ → ℝ}
    (hle : ∀ᶠ k in 𝓝 K, iv_bellRHS A β δ Ψ V k I ≤ V k)
    (heq : iv_bellRHS A β δ Ψ V K I = V K) (hV0 : HasDerivAt V dV0 K)
    (hV1 : HasDerivAt V dV1 ((1 - δ) * K + I)) (hΨ : iv_HasPartials Ψ a b (I, K)) :
    dV0 = A - b + β * (1 - δ) * dV1 := by
  have d1 : HasDerivAt (fun k => Ψ (I, k)) (a * 0 + b * 1) K :=
    hΨ.comp (x := fun _ => I) (y := fun k => k) (hasDerivAt_const K I) (hasDerivAt_id K)
  have d2 : HasDerivAt (fun k => V ((1 - δ) * k + I)) (dV1 * (1 - δ)) K := by
    have hin : HasDerivAt (fun k : ℝ => (1 - δ) * k + I) (1 - δ) K := by
      simpa using ((hasDerivAt_id K).const_mul (1 - δ)).add_const I
    exact hV1.comp K hin
  have d : HasDerivAt (fun k => V k - iv_bellRHS A β δ Ψ V k I)
      (dV0 - (A * 1 - 0 - (a * 0 + b * 1) + β * (dV1 * (1 - δ)))) K :=
    hV0.sub (((((hasDerivAt_id K).const_mul A).sub (hasDerivAt_const K I)).sub d1).add
      (d2.const_mul β))
  have hmin : IsLocalMin (fun k => V k - iv_bellRHS A β δ Ψ V k I) K := by
    filter_upwards [hle] with k hk
    simp only [heq, sub_self]
    linarith
  have := hmin.hasDerivAt_eq_zero d
  linarith

/-- **Exercise 8.12** (Miao, p. 289), Hayashi's result from the Bellman equation. Let
`V(K) = vK` on `K > 0` (as for a unique solution, `ex_8_12_homog`) and let the plan
`(Iₜ, Kₜ)` with `Kₜ > 0` attain the Bellman equation at every date:
`V(Kₜ) = AKₜ − Iₜ − Ψ(Iₜ, Kₜ) + βV(K_{t+1})`, `K_{t+1} = (1 − δ)Kₜ + Iₜ`. Put `Q = βv`
(marginal Q, `= βV′(K_{t+1})`). Then `QK_{t+1} = βV(K_{t+1})` (marginal Q is average Q:
`Q = βV(K_{t+1})/K_{t+1}`), and if `βᵀQK_{T+1} → 0`,
`QK_{t+1} = Σ_{j≥1} βʲ[AK_{t+j} − I_{t+j} − Ψ(I_{t+j}, K_{t+j})]`. -/
theorem ex_8_12_hayashi {A β δ v : ℝ} (hβ : 0 < β) {Ψ : ℝ × ℝ → ℝ} {V : ℝ → ℝ}
    (hlin : ∀ K, 0 < K → V K = v * K) {I K : ℕ → ℝ} (hKpos : ∀ t, 0 < K t)
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + I t)
    (hbell : ∀ t, iv_bellRHS A β δ Ψ V (K t) (I t) = V (K t))
    (htvc : Tendsto (fun T => β ^ T * (β * v) * K (T + 1)) atTop (𝓝 0)) (t : ℕ) :
    (β * v) * K (t + 1) = β * V (K (t + 1)) ∧
      Tendsto (fun T => ∑ j ∈ Finset.range T,
        β ^ (j + 1) * (A * K (t + j + 1) - I (t + j + 1) - Ψ (I (t + j + 1), K (t + j + 1))))
        atTop (𝓝 ((β * v) * K (t + 1))) := by
  refine ⟨by rw [hlin _ (hKpos _)]; ring, ?_⟩
  have hstep : ∀ s, (fun _ => β * v) s * K (s + 1) =
      β * (A * K (s + 1) - I (s + 1) - Ψ (I (s + 1), K (s + 1)))
      + β * K (s + 2) * (fun _ => β * v) (s + 1) := by
    intro s
    have hb := hbell (s + 1)
    unfold iv_bellRHS at hb
    rw [← hK (s + 1), hlin _ (hKpos _), hlin _ (hKpos _)] at hb
    simp only
    rw [show s + 2 = s + 1 + 1 by omega]
    linear_combination (-β) * hb
  have hres : Tendsto (fun T => β ^ T * (β * v) * K (t + T + 1)) atTop (𝓝 0) := by
    have h2 := ((tendsto_add_atTop_iff_nat t).2 htvc).const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    have : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [pow_add, add_comm T t]
    field_simp
  have h3 := (tendsto_const_nhds (x := (β * v) * K (t + 1))).sub hres
  rw [sub_zero] at h3
  refine h3.congr fun T => ?_
  have := iv_hayashi_iterate (Q := fun _ => β * v)
    (D := fun s => A * K s - I s - Ψ (I s, K s)) hstep t T
  rw [this]
  ring

/-- The adjustment cost of Exercise 8.13, `Ψ(I, K) = I²/(2K)`. -/
noncomputable def iv_psi13 (p : ℝ × ℝ) : ℝ := p.1 ^ 2 / (2 * p.2)

/-- **Exercise 8.13** (Miao, p. 290): `Ψ(I, K) = I²/(2K)` is linearly homogeneous. -/
theorem iv_psi13_hom (l : ℝ) (p : ℝ × ℝ) (hl : 0 < l) :
    iv_psi13 (l * p.1, l * p.2) = l * iv_psi13 p := by
  unfold iv_psi13
  rcases eq_or_ne p.2 0 with h | h
  · simp [h]
  · field_simp

/-- **Exercise 8.13** (Miao, p. 290): for `K > 0`, `Ψ(I, K) = I²/(2K)` has partial derivatives
`Ψ₁ = I/K` and `Ψ₂ = −I²/(2K²)`. -/
theorem iv_psi13_partials {I K : ℝ} (hK : 0 < K) :
    iv_HasPartials iv_psi13 (I / K) (-(I ^ 2) / (2 * K ^ 2)) (I, K) := by
  have h2K : (2 * K) ≠ 0 := by positivity
  have hinv : HasFDerivAt (fun p : ℝ × ℝ => (2 * p.2)⁻¹)
      ((-((2 * K) ^ 2)⁻¹) • ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) (I, K) :=
    (hasDerivAt_inv h2K).comp_hasFDerivAt (I, K) (hasFDerivAt_snd.const_smul (2 : ℝ))
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (I, K) :=
    hasFDerivAt_fst
  have hm := (hfst.mul hfst).mul hinv
  have hfun : iv_psi13 = fun p : ℝ × ℝ => p.1 * p.1 * (2 * p.2)⁻¹ := by
    funext p
    unfold iv_psi13
    rw [div_eq_mul_inv, sq]
  unfold iv_HasPartials
  rw [hfun]
  refine hm.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  simp
  field_simp
  ring

/-- **Exercise 8.13** (Miao, p. 290): `(I, K) ↦ AK − I − I²/(2K)` is concave on `ℝ × (0, ∞)`
(the cost `I²/(2K)` is convex: `(aI₁ + bI₂)²/(aK₁ + bK₂) ≤ aI₁²/K₁ + bI₂²/K₂`). -/
theorem iv_concave13 (A : ℝ) :
    ConcaveOn ℝ (Set.univ ×ˢ Set.Ioi 0) (iv_qReward (fun K => A * K) iv_psi13) := by
  refine ⟨convex_univ.prod (convex_Ioi 0), fun p hp q hq a b ha hb hab => ?_⟩
  have hK1 : 0 < p.2 := hp.2
  have hK2 : 0 < q.2 := hq.2
  simp only [iv_qReward, iv_psi13, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add]
  have hK : 0 < a * p.2 + b * q.2 := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hab ⊢; simp only [zero_mul, zero_add]; rw [zero_add] at hab; rw [hab]; linarith
    · nlinarith
  have key : (a * p.1 + b * q.1) ^ 2 * (p.2 * q.2) ≤
      (a * p.1 ^ 2 * q.2 + b * q.1 ^ 2 * p.2) * (a * p.2 + b * q.2) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 * q.2 - q.1 * p.2))]
  have hc : (a * p.1 + b * q.1) ^ 2 / (2 * (a * p.2 + b * q.2)) ≤
      a * (p.1 ^ 2 / (2 * p.2)) + b * (q.1 ^ 2 / (2 * q.2)) := by
    have e : a * (p.1 ^ 2 / (2 * p.2)) + b * (q.1 ^ 2 / (2 * q.2)) =
        (a * p.1 ^ 2 * q.2 + b * q.1 ^ 2 * p.2) / (2 * (p.2 * q.2)) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlin : a * (A * p.2 - p.1) + b * (A * q.2 - q.1) =
      A * (a * p.2 + b * q.2) - (a * p.1 + b * q.1) := by ring
  nlinarith

/-- The investment rate of Exercise 8.13, `i = r + δ − √D` with
`D = (r + δ)² + 2(r + δ) − 2A`. -/
noncomputable def iv_i13 (A r δ : ℝ) : ℝ :=
  (r + δ) - Real.sqrt ((r + δ) ^ 2 + 2 * (r + δ) - 2 * A)

/-- **Exercise 8.13** (Miao, p. 290): `i` solves the stationary Q equation
`(1 + r)(1 + i) = A + i²/2 + (1 − δ)(1 + i)`, i.e. `Q = 1 + i` satisfies (8.31) with
`β = 1/(1 + r)` and `Ψ₂ = −i²/2`, when `D ≥ 0`. -/
theorem ex_8_13_quadratic {A r δ : ℝ} (hD : 0 ≤ (r + δ) ^ 2 + 2 * (r + δ) - 2 * A) :
    (1 + r) * (1 + iv_i13 A r δ) = A + iv_i13 A r δ ^ 2 / 2 + (1 - δ) * (1 + iv_i13 A r δ) := by
  unfold iv_i13
  have hs := Real.sq_sqrt hD
  nlinarith [hs]

/-- **Exercise 8.13** (Miao, p. 290): the candidate plan `Kₜ = gᵗK₀`, `Iₜ = iKₜ`,
`g = 1 − δ + i`, with `Qₜ = 1 + i` satisfies (8.29), (8.30) `Qₜ = 1 + Ψ₁(Iₜ, Kₜ)` and (8.31)
`Qₜ = β(A − Ψ₂(I_{t+1}, K_{t+1})) + β(1 − δ)Q_{t+1}`, for `β = 1/(1 + r)`, `r > −1`, `D ≥ 0`,
`K₀ > 0` and `g > 0`. -/
theorem ex_8_13_foc {A r δ K0 : ℝ} (hr : -1 < r) (hD : 0 ≤ (r + δ) ^ 2 + 2 * (r + δ) - 2 * A)
    (hK0 : 0 < K0) (hg : 0 < 1 - δ + iv_i13 A r δ) (t : ℕ) :
    let i := iv_i13 A r δ
    let K : ℕ → ℝ := fun s => (1 - δ + i) ^ s * K0
    let I : ℕ → ℝ := fun s => i * K s
    K (t + 1) = (1 - δ) * K t + I t ∧ 0 < K t ∧
      iv_HasPartials iv_psi13 (I t / K t) (-(I t ^ 2) / (2 * K t ^ 2)) (I t, K t) ∧
      1 + i = 1 + I t / K t ∧
      1 + i = 1 / (1 + r) * (A - -(I (t + 1) ^ 2) / (2 * K (t + 1) ^ 2))
        + 1 / (1 + r) * (1 - δ) * (1 + i) := by
  intro i K I
  have hKt : ∀ s, 0 < K s := fun s => mul_pos (pow_pos hg s) hK0
  have hIK : ∀ s, I s / K s = i := fun s => by
    simp only [I]; field_simp [(hKt s).ne']
  refine ⟨by simp only [K, I, pow_succ]; ring, hKt t, iv_psi13_partials (hKt t),
    by rw [hIK], ?_⟩
  have hq := ex_8_13_quadratic hD
  have e : I (t + 1) ^ 2 / (2 * K (t + 1) ^ 2) = i ^ 2 / 2 := by
    have := hIK (t + 1)
    rw [div_eq_iff (hKt (t + 1)).ne'] at this
    rw [this]
    field_simp [(hKt (t + 1)).ne']
  have h1r : (1 + r) ≠ 0 := by linarith
  rw [neg_div, sub_neg_eq_add, e]
  field_simp
  linarith

/-- **Exercise 8.13** (Miao, p. 290): when `D > 0` the transversality condition (8.32)
`βᵀQ_TK_{T+1} → 0` holds along the candidate plan (`0 < βg < 1`). -/
theorem ex_8_13_tvc {A r δ K0 : ℝ} (hr : -1 < r) (hD : 0 < (r + δ) ^ 2 + 2 * (r + δ) - 2 * A)
    (hg : 0 < 1 - δ + iv_i13 A r δ) :
    Tendsto (fun T : ℕ => (1 / (1 + r)) ^ T * (1 + iv_i13 A r δ)
      * ((1 - δ + iv_i13 A r δ) ^ (T + 1) * K0)) atTop (𝓝 0) := by
  set g := 1 - δ + iv_i13 A r δ
  have h1r : 0 < 1 + r := by linarith
  have hlt : g / (1 + r) < 1 := by
    rw [div_lt_one h1r]
    have : 0 < Real.sqrt ((r + δ) ^ 2 + 2 * (r + δ) - 2 * A) := Real.sqrt_pos.2 hD
    simp only [g, iv_i13]
    linarith
  have h0 : 0 ≤ g / (1 + r) := by positivity
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt).const_mul
    ((1 + iv_i13 A r δ) * g * K0))
  rw [mul_zero] at this
  refine this.congr fun T => ?_
  rw [div_pow, pow_succ, one_div, inv_pow]
  field_simp

/-- **Exercise 8.13** (Miao, p. 290), the value of the firm: when `D > 0` and `g > 0`, the
discounted profits of the candidate plan converge to `V(K₀) = (1 + r)(1 + i)K₀`. -/
theorem ex_8_13_value {A r δ K0 : ℝ} (hr : -1 < r) (hK0 : 0 < K0)
    (hD : 0 < (r + δ) ^ 2 + 2 * (r + δ) - 2 * A) (hg : 0 < 1 - δ + iv_i13 A r δ) :
    Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (1 / (1 + r)) ^ t *
      iv_qReward (fun K => A * K) iv_psi13
        (iv_i13 A r δ * ((1 - δ + iv_i13 A r δ) ^ t * K0), (1 - δ + iv_i13 A r δ) ^ t * K0))
      atTop (𝓝 ((1 + r) * (1 + iv_i13 A r δ) * K0)) := by
  set i := iv_i13 A r δ with hi
  set g := 1 - δ + i with hgdef
  have h1r : 0 < 1 + r := by linarith
  have hsq : 0 < Real.sqrt ((r + δ) ^ 2 + 2 * (r + δ) - 2 * A) := Real.sqrt_pos.2 hD
  have hlt : g / (1 + r) < 1 := by
    rw [div_lt_one h1r]
    simp only [g, i, iv_i13]
    linarith
  have h0 : 0 ≤ g / (1 + r) := by positivity
  have hq := ex_8_13_quadratic hD.le
  rw [← hi] at hq
  have hterm : ∀ t : ℕ, (1 / (1 + r)) ^ t * iv_qReward (fun K => A * K) iv_psi13
      (i * (g ^ t * K0), g ^ t * K0) = (A - i - i ^ 2 / 2) * K0 * (g / (1 + r)) ^ t := by
    intro t
    have hgt : 0 < g ^ t * K0 := mul_pos (pow_pos hg t) hK0
    unfold iv_qReward iv_psi13
    simp only
    field_simp
    ring_nf
  have hs := (hasSum_geometric_of_lt_one h0 hlt).mul_left ((A - i - i ^ 2 / 2) * K0)
  have ht := ((hs.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
  have hval : (A - i - i ^ 2 / 2) * K0 * (1 - g / (1 + r))⁻¹ = (1 + r) * (1 + i) * K0 := by
    have hne : (1 + r) - g ≠ 0 := by simp only [g, i, iv_i13]; linarith
    rw [one_sub_div h1r.ne', inv_div]
    field_simp
    simp only [g]
    nlinarith [hq]
  rw [hval] at ht
  refine ht.congr fun T => ?_
  simp only [Function.comp_apply]
  exact Finset.sum_congr rfl fun t _ => (hterm t).symm

/-- **Exercise 8.13** (Miao, p. 290), the optimal investment policy. Let `β = 1/(1 + r)`,
`r > −1`, `δ ≥ 0`, `K₀ > 0`, `D = (r + δ)² + 2(r + δ) − 2A > 0` and `g = 1 − δ + i > 0` with
`i = r + δ − √D`. Then the policy `Iₜ = iKₜ` (constant investment rate `i`, marginal and average
`Q = 1 + i`) is optimal: every plan with `Kₜ > 0` satisfying `K_{t+1} = Iₜ + (1 − δ)Kₜ`,
`K₀` given, whose discounted profits converge, has value at most `(1 + r)(1 + i)K₀`, the value of
the firm (`ex_8_13_value`). -/
theorem ex_8_13 {A r δ K0 : ℝ} (hr : -1 < r) (hδ : 0 ≤ δ) (hK0 : 0 < K0)
    (hD : 0 < (r + δ) ^ 2 + 2 * (r + δ) - 2 * A) (hg : 0 < 1 - δ + iv_i13 A r δ)
    {I K : ℕ → ℝ} (hK : ∀ t, K (t + 1) = (1 - δ) * K t + I t) (hKpos : ∀ t, 0 < K t)
    (hK0' : K 0 = K0) {J : ℝ}
    (hJ : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (1 / (1 + r)) ^ t *
      iv_qReward (fun K => A * K) iv_psi13 (I t, K t)) atTop (𝓝 J)) :
    J ≤ (1 + r) * (1 + iv_i13 A r δ) * K0 := by
  have h1r : 0 < 1 + r := by linarith
  have foc := fun t => ex_8_13_foc hr hD.le hK0 hg t
  refine iv_q_optimal (S := Set.univ ×ˢ Set.Ioi 0) (δ := δ) (by positivity) (iv_concave13 A)
    (Is := fun t => iv_i13 A r δ * ((1 - δ + iv_i13 A r δ) ^ t * K0))
    (Ks := fun t => (1 - δ + iv_i13 A r δ) ^ t * K0) (Q := fun _ => 1 + iv_i13 A r δ)
    (dpr := fun _ => A) (fun t => by simpa using (hasDerivAt_id _).const_mul A)
    (fun t => (foc t).2.2.1) (fun t => (foc t).1) (fun t => ⟨Set.mem_univ _, (foc t).2.1⟩)
    (fun t => (foc t).2.2.2.1) (fun t => (foc t).2.2.2.2)
    (fun t => by show 0 ≤ 1 + iv_i13 A r δ; linarith)
    (ex_8_13_tvc hr hD hg) hK (fun t => ⟨Set.mem_univ _, hKpos t⟩) (by simp [hK0'])
    (fun t => (hKpos t).le) (ex_8_13_value hr hK0 hD hg) hJ

/-- **Exercise 8.13** (Miao, p. 290), when the value is infinite: if
`D = (r + δ)² + 2(r + δ) − 2A < 0` (and `r > −1`, `K₀ > 0`), the feasible plan with constant
investment rate `r + δ` (capital growing at the gross rate `1 + r`) has discounted profits
`(T + 1)K₀(A − (r + δ) − (r + δ)²/2) → +∞`. -/
theorem ex_8_13_unbounded {A r δ K0 : ℝ} (hr : -1 < r) (hK0 : 0 < K0)
    (hD : (r + δ) ^ 2 + 2 * (r + δ) - 2 * A < 0) :
    let K : ℕ → ℝ := fun t => (1 + r) ^ t * K0
    let I : ℕ → ℝ := fun t => (r + δ) * K t
    (∀ t, K (t + 1) = (1 - δ) * K t + I t ∧ 0 < K t) ∧
      Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (1 / (1 + r)) ^ t *
        iv_qReward (fun K => A * K) iv_psi13 (I t, K t)) atTop atTop := by
  intro K I
  have h1r : 0 < 1 + r := by linarith
  have hKt : ∀ t, 0 < K t := fun t => mul_pos (pow_pos h1r t) hK0
  refine ⟨fun t => ⟨by simp only [K, I, pow_succ]; ring, hKt t⟩, ?_⟩
  set κ := K0 * (A - (r + δ) - (r + δ) ^ 2 / 2) with hκ
  have hκ0 : 0 < κ := mul_pos hK0 (by nlinarith)
  have hterm : ∀ t, (1 / (1 + r)) ^ t * iv_qReward (fun K => A * K) iv_psi13 (I t, K t) = κ := by
    intro t
    have hp : ((1 + r) ^ t) ≠ 0 := (pow_pos h1r t).ne'
    have hb : (1 / (1 + r)) ^ t = ((1 + r) ^ t)⁻¹ := by rw [one_div, inv_pow]
    simp only [iv_qReward, iv_psi13, I, K, hκ, hb]
    field_simp
  have hsum : ∀ T, ∑ t ∈ Finset.range (T + 1), (1 / (1 + r)) ^ t *
      iv_qReward (fun K => A * K) iv_psi13 (I t, K t) = ((T : ℝ) + 1) * κ := by
    intro T
    rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    ring
  simp only [hsum]
  exact Tendsto.atTop_mul_const hκ0 (tendsto_atTop_add_const_right _ 1
    tendsto_natCast_atTop_atTop)

end Miao.Applications
