/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.IVQTheory
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Uzawa's adjustment costs (8.34) and Exercise 8.14

Miao, p. 280, (8.34), and Exercise 8.14, p. 290. The firm maximises `Σ βᵗ[π(Kₜ) − Iₜ]` subject to
`K_{t+1} = (1 − δ)Kₜ + Φ(Iₜ, Kₜ)` (8.34): `I` units of investment become `Φ(I, K)` units of
capital, with `Φ₁ > 0`, `Φ₁₁ < 0`, `Φ(0, ·) = 0`.

With the multiplier `βᵗQₜ` on (8.34) the first-order conditions are
`QₜΦ₁(Iₜ, Kₜ) = 1` and `Qₜ = β[π′(K_{t+1}) + Q_{t+1}(1 − δ + Φ₂(I_{t+1}, K_{t+1}))]`.

* Sufficiency: if `π(K) − I` and `Φ` are concave, `Q ≥ 0` and the first-order conditions hold,
  then the plan beats every feasible plan with nonnegative capital up to `βᵀQ_TK*_{T+1}`
  (`ex_8_14_sufficient`), hence is optimal under the transversality condition
  (`ex_8_14_optimal`).
* The investment policy: `Iₜ = i(Qₜ, Kₜ)` solves `Φ₁(I, K) = 1/Q`, and is increasing in `Q`
  (`ex_8_14_invest_mono`).
* Q theory: forward iteration of the Euler equation for `Q` (`ex_8_14_Q_iterate`) and the
  present-value formula `Qₜ = Σ_{j≥1} βʲ (Π_{s=1}^{j−1} (1 − δ + Φ₂_{t+s})) π′(K_{t+j})`
  (`ex_8_14_Q_pv`); with `π = AK` and `Φ` linearly homogeneous, Hayashi's result
  `QₜK_{t+1} = Σ_{j≥1} βʲ[AK_{t+j} − I_{t+j}]` (`ex_8_14_hayashi_step`, `ex_8_14_hayashi`).
* "Both formulations deliver similar results" (p. 280): if `G(·, K)` inverts `Φ(·, K)`, the
  Uzawa model is the (8.29) model with `Ψ(X, K) = G(X, K) − X` (`ex_8_14_equiv`), `Ψ(0, K) = 0`
  when `Φ(0, K) = 0`, and the two `Q`'s agree: `1 + Ψ₁ = 1/Φ₁` (`ex_8_14_Q_same`).
-/

namespace Miao.Applications

open Filter Topology

/-- **Exercise 8.14** (Miao, p. 290), sufficiency of the first-order conditions. Let
`(I, K) ↦ π(K) − I` and `Φ` be concave on a convex set `S`; let `(I*, K*)` satisfy (8.34), with
`Φ₁ = a`, `Φ₂ = b` along it, and multipliers `Q ≥ 0` with `QₜΦ₁(I*ₜ, K*ₜ) = 1` and
`Qₜ = β[π′(K*_{t+1}) + Q_{t+1}(1 − δ + Φ₂(I*_{t+1}, K*_{t+1}))]`. Then every plan `(I, K)` with
the same `K₀`, satisfying (8.34), with values in `S` and `K ≥ 0`, satisfies
`Σ_{t≤T} βᵗ[π(Kₜ) − Iₜ] ≤ Σ_{t≤T} βᵗ[π(K*ₜ) − I*ₜ] + βᵀQ_TK*_{T+1}`. -/
theorem ex_8_14_sufficient {prof : ℝ → ℝ} {Φ : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {β δ : ℝ}
    (hβ : 0 ≤ β) (hf : ConcaveOn ℝ S (fun p => prof p.2 - p.1)) (hΦc : ConcaveOn ℝ S Φ)
    {Is Ks I K Q dpr a b : ℕ → ℝ}
    (hpr : ∀ t, HasDerivAt prof (dpr t) (Ks t))
    (hΦ : ∀ t, iv_HasPartials Φ (a t) (b t) (Is t, Ks t))
    (hKs : ∀ t, Ks (t + 1) = (1 - δ) * Ks t + Φ (Is t, Ks t)) (hSs : ∀ t, (Is t, Ks t) ∈ S)
    (hfoc1 : ∀ t, Q t * a t = 1)
    (hfoc2 : ∀ t, Q t = β * (dpr (t + 1) + Q (t + 1) * (1 - δ + b (t + 1))))
    (hQ : ∀ t, 0 ≤ Q t)
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + Φ (I t, K t)) (hS : ∀ t, (I t, K t) ∈ S)
    (hK0 : K 0 = Ks 0) (hKnn : ∀ t, 0 ≤ K t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (prof (K t) - I t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * (prof (Ks t) - Is t) + β ^ T * Q T * Ks (T + 1) := by
  have grad : ∀ t, (prof (K t) - I t) - (prof (Ks t) - Is t) ≤
      (dpr t + Q t * (1 - δ + b t)) * (K t - Ks t) - Q t * (K (t + 1) - Ks (t + 1)) := by
    intro t
    have hfd : HasFDerivAt (fun p : ℝ × ℝ => prof p.2 - p.1)
        (dpr t • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (Is t, Ks t) :=
      ((hpr t).comp_hasFDerivAt (Is t, Ks t) hasFDerivAt_snd).sub hasFDerivAt_fst
    have g1 := eu_concave_le_fderiv hf (hSs t) (hS t) hfd
    have g2 := eu_concave_le_fderiv hΦc (hSs t) (hS t) (hΦ t)
    simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul] at g1 g2
    have hΦt : Φ (I t, K t) - Φ (Is t, Ks t) =
        (K (t + 1) - Ks (t + 1)) - (1 - δ) * (K t - Ks t) := by rw [hK t, hKs t]; ring
    have g3 := mul_le_mul_of_nonneg_left g2 (hQ t)
    have h1 : Q t * (a t * (I t - Is t)) = I t - Is t := by rw [← mul_assoc, hfoc1 t, one_mul]
    have g4 : Q t * (Φ (I t, K t) - Φ (Is t, Ks t)) ≤ (I t - Is t)
        + Q t * b t * (K t - Ks t) := by linarith
    rw [hΦt] at g4
    linear_combination g1 + g4
  have main : ∀ T, ∑ t ∈ Finset.range (T + 1), β ^ t * ((prof (K t) - I t)
      - (prof (Ks t) - Is t)) ≤ -(β ^ T * Q T * (K (T + 1) - Ks (T + 1))) := by
    intro T
    induction T with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul]
      have := grad 0
      rw [hK0, sub_self, mul_zero, zero_sub] at this
      rw [hK0]
      linarith
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have g := mul_le_mul_of_nonneg_left (grad (n + 1)) (pow_nonneg hβ (n + 1))
      have key : β ^ (n + 1) * (dpr (n + 1) + Q (n + 1) * (1 - δ + b (n + 1))) =
          β ^ n * Q n := by rw [hfoc2 n, pow_succ]; ring
      have e : β ^ (n + 1) * ((dpr (n + 1) + Q (n + 1) * (1 - δ + b (n + 1)))
          * (K (n + 1) - Ks (n + 1)) - Q (n + 1) * (K (n + 1 + 1) - Ks (n + 1 + 1))) =
          β ^ (n + 1) * (dpr (n + 1) + Q (n + 1) * (1 - δ + b (n + 1)))
            * (K (n + 1) - Ks (n + 1))
          - β ^ (n + 1) * Q (n + 1) * (K (n + 1 + 1) - Ks (n + 1 + 1)) := by ring
      rw [e, key] at g
      nlinarith
  have hm := main T
  rw [Finset.sum_congr rfl (fun t _ => mul_sub (β ^ t) _ _), Finset.sum_sub_distrib] at hm
  have hnn : 0 ≤ β ^ T * Q T * K (T + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hβ T) (hQ T)) (hKnn (T + 1))
  nlinarith

/-- **Exercise 8.14** (Miao, p. 290), optimality: under the hypotheses of `ex_8_14_sufficient`
and the transversality condition `βᵀQ_TK*_{T+1} → 0`, if the discounted profits of `(I*, K*)`
converge to `J*` and those of a competing feasible plan converge to `J`, then `J ≤ J*`. -/
theorem ex_8_14_optimal {prof : ℝ → ℝ} {Φ : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {β δ : ℝ}
    (hβ : 0 ≤ β) (hf : ConcaveOn ℝ S (fun p => prof p.2 - p.1)) (hΦc : ConcaveOn ℝ S Φ)
    {Is Ks I K Q dpr a b : ℕ → ℝ}
    (hpr : ∀ t, HasDerivAt prof (dpr t) (Ks t))
    (hΦ : ∀ t, iv_HasPartials Φ (a t) (b t) (Is t, Ks t))
    (hKs : ∀ t, Ks (t + 1) = (1 - δ) * Ks t + Φ (Is t, Ks t)) (hSs : ∀ t, (Is t, Ks t) ∈ S)
    (hfoc1 : ∀ t, Q t * a t = 1)
    (hfoc2 : ∀ t, Q t = β * (dpr (t + 1) + Q (t + 1) * (1 - δ + b (t + 1))))
    (hQ : ∀ t, 0 ≤ Q t) (htvc : Tendsto (fun T => β ^ T * Q T * Ks (T + 1)) atTop (𝓝 0))
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + Φ (I t, K t)) (hS : ∀ t, (I t, K t) ∈ S)
    (hK0 : K 0 = Ks 0) (hKnn : ∀ t, 0 ≤ K t) {J Js : ℝ}
    (hJs : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * (prof (Ks t) - Is t))
      atTop (𝓝 Js))
    (hJ : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * (prof (K t) - I t))
      atTop (𝓝 J)) : J ≤ Js := by
  have hsum := hJs.add htvc
  rw [add_zero] at hsum
  exact le_of_tendsto_of_tendsto hJ hsum (Eventually.of_forall fun T =>
    ex_8_14_sufficient hβ hf hΦc hpr hΦ hKs hSs hfoc1 hfoc2 hQ hK hS hK0 hKnn T)

/-- **Exercise 8.14** (Miao, p. 290), the investment policy: `QΦ₁(I, K) = 1`, so investment
solves `Φ₁(I, K) = 1/Q`; since `Φ₁₁ < 0` (`Φ₁(·, K)` strictly decreasing), investment increases
with `Q`: if `QΦ₁(I) = 1`, `Q′Φ₁(I′) = 1` and `0 < Q < Q′`, then `I < I′`. -/
theorem ex_8_14_invest_mono {Φ1 : ℝ → ℝ} (hanti : StrictAnti Φ1) {I I' Q Q' : ℝ}
    (hQ0 : 0 < Q) (h : Q * Φ1 I = 1) (h' : Q' * Φ1 I' = 1) (hQ : Q < Q') : I < I' := by
  by_contra hc
  have hle := hanti.antitone (not_lt.1 hc)
  have hΦ : 0 < Φ1 I := by
    by_contra hn
    nlinarith
  nlinarith

/-- **Exercise 8.14** (Miao, p. 290): forward iteration of
`Qₜ = β[π′(K_{t+1}) + Q_{t+1}gₜ₊₁]` with `gₛ = 1 − δ + Φ₂(Iₛ, Kₛ)`:
`Qₜ = Σ_{j<T} β^{j+1}(Π_{s<j} g_{t+s+1}) π′(K_{t+j+1}) + βᵀ(Π_{s<T} g_{t+s+1})Q_{t+T}`. -/
theorem ex_8_14_Q_iterate {β : ℝ} {Q m g : ℕ → ℝ}
    (h : ∀ t, Q t = β * (m (t + 1) + Q (t + 1) * g (t + 1))) (t T : ℕ) :
    Q t = ∑ j ∈ Finset.range T, β ^ (j + 1) * (∏ s ∈ Finset.range j, g (t + s + 1))
        * m (t + j + 1)
      + β ^ T * (∏ s ∈ Finset.range T, g (t + s + 1)) * Q (t + T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, h (t + n), Finset.prod_range_succ,
      show t + (n + 1) = t + n + 1 by omega]
    ring

/-- **Exercise 8.14** (Miao, p. 290), the Q theory in Uzawa's framework: if the residual
`βᵀ(Π_{s<T} g_{t+s+1})Q_{t+T}` tends to zero, then
`Qₜ = Σ_{j≥1} βʲ(Π_{s=1}^{j−1} g_{t+s}) π′(K_{t+j})` (limit of partial sums): `Q` is the present
value of the marginal products of a unit of capital, which depreciates at the rate
`δ − Φ₂`. -/
theorem ex_8_14_Q_pv {β : ℝ} {Q m g : ℕ → ℝ}
    (h : ∀ t, Q t = β * (m (t + 1) + Q (t + 1) * g (t + 1))) (t : ℕ)
    (hres : Tendsto (fun T => β ^ T * (∏ s ∈ Finset.range T, g (t + s + 1)) * Q (t + T)) atTop
      (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ (j + 1) * (∏ s ∈ Finset.range j, g (t + s + 1))
      * m (t + j + 1)) atTop (𝓝 (Q t)) := by
  have h3 := (tendsto_const_nhds (x := Q t)).sub hres
  rw [sub_zero] at h3
  refine h3.congr fun T => ?_
  rw [ex_8_14_Q_iterate h t T]
  ring

/-- **Exercise 8.14** (Miao, p. 290), Hayashi's one-step identity in Uzawa's framework. With
`π(K) = AK`, `Q_{t+1}Φ₁ = 1`, `Qₜ = β[A + Q_{t+1}(1 − δ + Φ₂)]`, Euler's identity
`Φ = IΦ₁ + KΦ₂` at `(I_{t+1}, K_{t+1})` and `K_{t+2} = (1 − δ)K_{t+1} + Φ`:
`QₜK_{t+1} = β[AK_{t+1} − I_{t+1}] + βQ_{t+1}K_{t+2}`. -/
theorem ex_8_14_hayashi_step {β δ A Qt Qt1 K1 K2 I1 Φv a b : ℝ} (hfoc1 : Qt1 * a = 1)
    (hfoc2 : Qt = β * (A + Qt1 * (1 - δ + b))) (heuler : Φv = I1 * a + K1 * b)
    (hK : K2 = (1 - δ) * K1 + Φv) :
    Qt * K1 = β * (A * K1 - I1) + β * K2 * Qt1 := by
  subst hfoc2 heuler hK
  linear_combination (-(β * I1)) * hfoc1

/-- **Exercise 8.14** (Miao, p. 290), Hayashi's result in Uzawa's framework: with `π(K) = AK`,
`Φ` linearly homogeneous with partial derivatives `Φ₁, Φ₂` along the plan, the first-order
conditions, (8.34) and the transversality condition `βᵀQ_TK_{T+1} → 0`,
`QₜK_{t+1} = Σ_{j≥1} βʲ[AK_{t+j} − I_{t+j}]`: marginal Q equals average Q. -/
theorem ex_8_14_hayashi {β δ A : ℝ} (hβ : 0 < β) {Φ : ℝ × ℝ → ℝ} {Φ1 Φ2 : ℕ → ℝ}
    {Q I K : ℕ → ℝ} (hhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p)
    (hd : ∀ t, iv_HasPartials Φ (Φ1 t) (Φ2 t) (I t, K t))
    (hK : ∀ t, K (t + 1) = (1 - δ) * K t + Φ (I t, K t)) (hfoc1 : ∀ t, Q t * Φ1 t = 1)
    (hfoc2 : ∀ t, Q t = β * (A + Q (t + 1) * (1 - δ + Φ2 (t + 1))))
    (htvc : Tendsto (fun T => β ^ T * Q T * K (T + 1)) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ (j + 1) * (A * K (t + j + 1) - I (t + j + 1)))
      atTop (𝓝 (Q t * K (t + 1))) := by
  have hstep : ∀ s, Q s * K (s + 1) = β * (A * K (s + 1) - I (s + 1))
      + β * K (s + 2) * Q (s + 1) := fun s =>
    ex_8_14_hayashi_step (hfoc1 (s + 1)) (hfoc2 s)
      (iv_euler_homog (fun l hl => hhom l (I (s + 1), K (s + 1)) hl) (hd (s + 1))) (hK (s + 1))
  have hres : Tendsto (fun T => β ^ T * Q (t + T) * K (t + T + 1)) atTop (𝓝 0) := by
    have h2 := ((tendsto_add_atTop_iff_nat t).2 htvc).const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    have : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    rw [pow_add, add_comm T t]
    field_simp
  have h3 := (tendsto_const_nhds (x := Q t * K (t + 1))).sub hres
  rw [sub_zero] at h3
  refine h3.congr fun T => ?_
  rw [iv_hayashi_iterate (D := fun s => A * K s - I s) hstep t T]
  ring

/-- **Exercise 8.14** / Miao p. 280, "both formulations deliver similar results". Let `G(·, K)`
be the inverse of `Φ(·, K)` and put `Ψ(X, K) = G(X, K) − X`. A plan `(I, K)` satisfying (8.34)
gives the plan `Xₜ = Φ(Iₜ, Kₜ)` satisfying (8.29); conversely a plan `(X, K)` satisfying (8.29)
gives `Iₜ = G(Xₜ, Kₜ)` satisfying (8.34); the rewards agree, `π(K) − I = π(K) − X − Ψ(X, K)`;
and `Ψ(0, K) = 0` when `Φ(0, K) = 0`. -/
theorem ex_8_14_equiv {prof : ℝ → ℝ} {Φ G : ℝ × ℝ → ℝ} {δ : ℝ}
    (hGΦ : ∀ I K, G (Φ (I, K), K) = I) (hΦG : ∀ X K, Φ (G (X, K), K) = X) :
    (∀ I K : ℕ → ℝ, (∀ t, K (t + 1) = (1 - δ) * K t + Φ (I t, K t)) →
        ∀ t, K (t + 1) = (1 - δ) * K t + (fun s => Φ (I s, K s)) t) ∧
      (∀ X K : ℕ → ℝ, (∀ t, K (t + 1) = (1 - δ) * K t + X t) →
        ∀ t, K (t + 1) = (1 - δ) * K t + Φ (G (X t, K t), K t)) ∧
      (∀ I K₀ : ℝ, prof K₀ - I = prof K₀ - Φ (I, K₀) - (G (Φ (I, K₀), K₀) - Φ (I, K₀))) ∧
      (∀ K₀, Φ (0, K₀) = 0 → G (0, K₀) - 0 = 0) := by
  refine ⟨fun I K h t => h t, fun X K h t => by rw [hΦG]; exact h t,
    fun I K₀ => by rw [hGΦ]; ring, fun K₀ h0 => ?_⟩
  have := hGΦ 0 K₀
  rw [h0] at this
  rw [this, sub_zero]

/-- **Exercise 8.14** / Miao p. 280: the two `Q`'s agree. If `Φ(·, K)` has derivative
`Φ₁ ≠ 0` at `I`, and `G(·, K)` is continuous at `X = Φ(I, K)` and inverts `Φ(·, K)` near `X`,
then `Ψ(·, K) = G(·, K) − id` has derivative `1/Φ₁ − 1` at `X`; so the (8.30)-multiplier
`1 + Ψ₁(X, K)` of the transformed model equals Uzawa's `Q = 1/Φ₁(I, K)`. -/
theorem ex_8_14_Q_same {Φ G : ℝ → ℝ} {I φ1 : ℝ} (hΦ : HasDerivAt Φ φ1 I) (hφ1 : φ1 ≠ 0)
    (hG : ContinuousAt G (Φ I)) (hGI : G (Φ I) = I)
    (hinv : ∀ᶠ y in 𝓝 (Φ I), Φ (G y) = y) :
    HasDerivAt (fun x => G x - x) (φ1⁻¹ - 1) (Φ I) ∧ 1 + (φ1⁻¹ - 1) = 1 / φ1 := by
  have hΦ' : HasDerivAt Φ φ1 (G (Φ I)) := by rw [hGI]; exact hΦ
  refine ⟨(HasDerivAt.of_local_left_inverse hG hΦ' hφ1 hinv).sub (hasDerivAt_id _), by ring⟩

end Miao.Applications
