/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.FSNeoclassical
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Fiscal stimulus in a DNK model: the Phillips curve and the Taylor-rule multiplier

Miao, §19.3, pp. 643–647, (19.44)–(19.52) (following Woodford 2011). The model is deterministic.

* (19.44): the zero-inflation steady state has `r̄ = −ln β` (`eq_19_44`); with `r_t = r̄` for all
  `t` and `C_t → C̄`, consumption is constant at `C̄` and the multiplier is one
  (`fs_constant_real_rate`).
* (19.45)–(19.46): the firm's cost-minimisation first-order conditions (`fs_costmin_foc`), the
  common labour/capital ratio (`fs_ratio_strictMonoOn`, `fs_common_ratio`), which equals aggregate
  hours (`fs_ratio_eq_hours`), and the common marginal cost (`eq_19_46`).
* (19.47): `ṽ'(Y)/u'(Y − G) = MC` (`eq_19_47`).
* The recursive reset-price equation, `q_t` and the Phillips curve
  `π_t = βπ_{t+1} + (1 − βθ)(1 − θ)/θ · MĈ_t` (`fs_reset_recursive`, `fs_q_recursive`,
  `fs_nkpc`).
* The log-linearised Euler equation (19.50) with `σ = 1/η_u` (`fs_euler_loglin`, `eq_19_50`).
* The log-linearisation of (19.47): `MĈ = (η_u + η_v)(Ŷ − ΓĜ)` (`fs_mc_loglin`, as a directional
  derivative). The book prints `(η_u + η_v)Ŷ_t − ΓĜ_t`; the `Γ` term must also be multiplied by
  `η_u + η_v`, as the book's own (19.48) uses.
* (19.48): the forward solution `π_t = κΣβʲ(Ŷ_{t+j} − ΓĜ_{t+j})`, the unique bounded solution
  (`fs_forward_hasSum`, `fs_forward_exists`, `eq_19_48`, `fs_kappa_pos`).
* (19.49)–(19.52): with `Ĝ_t = ρᵗĜ₀` the conjecture (19.51) is an equilibrium iff the
  coefficients are given by (19.52) (`eq_19_52`); `ψ > 0` (`fs_psi_pos`), `0 < γ_y < 1`
  (`fs_gammaY_pos`, `fs_gammaY_lt_one`), and `γ_y < Γ` iff `φ_y` is large enough
  (`fs_gammaY_lt_Gamma_iff`). We read the garbled (19.52) as
  `γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)`, which is what the derivation gives.
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- A real sequence is bounded. -/
def fs_Bdd (x : ℕ → ℝ) : Prop := ∃ B, ∀ t, |x t| ≤ B

/-- Miao, (19.44), p. 644: in a zero-inflation steady state `C_t = C̄`, the Euler equation
`u'(C_t)/(βu'(C_{t+1})) = exp(r_t)` gives `r̄ = −ln β`. -/
theorem eq_19_44 {β uC r : ℝ} (hβ : 0 < β) (hu : uC ≠ 0) (h : uC / (β * uC) = Real.exp r) :
    r = -Real.log β := by
  have : Real.exp r = β⁻¹ := by
    rw [← h]
    field_simp
  rw [← Real.log_exp r, this, Real.log_inv]

/-- Miao, p. 644: if monetary policy keeps `r_t = r̄ = −ln β` for all `t`, `u'` is injective
and `C_t → C̄`, then `C_t = C̄` for all `t`, and `Y_t = C̄ + G_t`: every unit of government
purchases raises output by one unit (`Y_t − Y_s = G_t − G_s`). -/
theorem fs_constant_real_rate {β Cb : ℝ} {u1 : ℝ → ℝ} {C G Y : ℕ → ℝ} (hβ : 0 < β)
    (hinj : Function.Injective u1) (hu : ∀ t, u1 (C (t + 1)) ≠ 0)
    (heul : ∀ t, u1 (C t) / (β * u1 (C (t + 1))) = Real.exp (-Real.log β))
    (hlim : Tendsto C atTop (𝓝 Cb)) (hres : ∀ t, C t + G t = Y t) :
    (∀ t, C t = Cb) ∧ ∀ t s, Y t - Y s = G t - G s := by
  have hstep : ∀ t, C (t + 1) = C t := by
    intro t
    have h := heul t
    rw [Real.exp_neg, Real.exp_log hβ] at h
    have hb : u1 (C t) = u1 (C (t + 1)) := by
      have := hu t
      field_simp at h
      linarith
    exact (hinj hb).symm
  have hconst : ∀ t, C t = C 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
  have hC0 : C 0 = Cb := by
    have : Tendsto C atTop (𝓝 (C 0)) := by
      have : C = fun _ => C 0 := funext hconst
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique this hlim
  refine ⟨fun t => (hconst t).trans hC0, fun t s => ?_⟩
  rw [← hres t, ← hres s, hconst t, hconst s]
  ring

/-- Miao, (19.45), p. 644–645: the partial derivatives of the constant-returns technology
`F(K, N) = Kf(N/K)` at `K > 0`: `∂F/∂K = f(n) − nf'(n)` and `∂F/∂N = f'(n)`, `n = N/K`. The
cost-minimisation first-order conditions are `R^k/P = MC·∂F/∂K` and `W/P = MC·∂F/∂N`. -/
theorem fs_costmin_foc {f f1 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x) {K N : ℝ}
    (hK : 0 < K) :
    HasDerivAt (fun k => k * f (N / k)) (f (N / K) - N / K * f1 (N / K)) K ∧
      HasDerivAt (fun m => K * f (m / K)) (f1 (N / K)) N := by
  constructor
  · have h1 : HasDerivAt (fun k => N / k) (-N / K ^ 2) K := by
      refine ((hasDerivAt_const K N).div (hasDerivAt_id' K) hK.ne').congr_deriv ?_
      ring
    have h2 := (hf (N / K)).comp K h1
    refine ((hasDerivAt_id' K).mul h2).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
    ring
  · have h1 : HasDerivAt (fun m => m / K) (1 / K) N := by
      simpa using (hasDerivAt_id N).div_const K
    refine (((hf (N / K)).comp N h1).const_mul K).congr_deriv ?_
    field_simp

/-- Miao, p. 645: eliminating `MC` from the two first-order conditions gives
`(R^k/P)/(W/P) = h(n) = f(n)/f'(n) − n`; `h` is strictly increasing on `n > 0` when `f > 0`,
`f' > 0` and `f'' < 0` (`h' = −ff''/f'² > 0`). -/
theorem fs_ratio_strictMonoOn {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hpos : ∀ x, 0 < x → 0 < f x) (hd : ∀ x, 0 < f1 x)
    (hcc : ∀ x, f2 x < 0) : StrictMonoOn (fun n => f n / f1 n - n) (Set.Ioi 0) := by
  have hder : ∀ x, HasDerivAt (fun n => f n / f1 n - n)
      ((f1 x * f1 x - f x * f2 x) / f1 x ^ 2 - 1) x := fun x =>
    ((hf x).div (hf1 x) (hd x).ne').sub (hasDerivAt_id x)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x _ => (hder x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hder x).deriv]
    have h1 := hd x
    have h2 := hpos x hx
    have h3 := hcc x
    have : (f1 x * f1 x - f x * f2 x) / f1 x ^ 2 - 1 = -(f x * f2 x) / f1 x ^ 2 := by
      field_simp
      ring
    rw [this]
    apply div_pos _ (by positivity)
    nlinarith [mul_pos h2 (neg_pos.2 h3)]

/-- Miao, p. 645: every firm chooses the same labour/capital ratio: if two firms' ratios
`n₁, n₂ > 0` both satisfy the first-order conditions with the same factor prices
(`h(n₁) = h(n₂)`), then
`n₁ = n₂`. -/
theorem fs_common_ratio {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hpos : ∀ x, 0 < x → 0 < f x) (hd : ∀ x, 0 < f1 x)
    (hcc : ∀ x, f2 x < 0) {n₁ n₂ : ℝ} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (h : f n₁ / f1 n₁ - n₁ = f n₂ / f1 n₂ - n₂) : n₁ = n₂ :=
  (fs_ratio_strictMonoOn hf hf1 hpos hd hcc).injOn h₁ h₂ h

/-- Miao, p. 645: with a common labour/capital ratio `n` (`N_j = nK_j`) and total capital one
(`Σ K_j = 1`), the ratio equals aggregate hours `N = Σ N_j`. -/
theorem fs_ratio_eq_hours {ι : Type*} (s : Finset ι) (K L : ι → ℝ) (n : ℝ)
    (hL : ∀ j ∈ s, L j = n * K j) (hK : ∑ j ∈ s, K j = 1) : ∑ j ∈ s, L j = n := by
  rw [Finset.sum_congr rfl hL, ← Finset.mul_sum, hK, mul_one]

/-- Miao, (19.46), p. 645: the common real marginal cost `MC = W/(Pf'(N))`, from
`W/P = MC·f'(N)`. -/
theorem eq_19_46 {W P f1N MC : ℝ} (hP : P ≠ 0) (hf : f1N ≠ 0) (h : W / P = MC * f1N) :
    MC = W / (P * f1N) := by
  field_simp at h ⊢
  linarith

/-- Miao, (19.47), p. 645: from the labour-supply condition `v'(N)/u'(Y − G) = W/P` and
`W/P = MC·f'(N)`, with `N = f⁻¹(Y)`: `ṽ'(Y)/u'(Y − G) = MC`, where `ṽ'(Y) = v'(N)/f'(N)`
(`fs_vtilde_hasDerivAt`). -/
theorem eq_19_47 {u1 v1 f1 finv : ℝ → ℝ} {N Y G w MC : ℝ} (hN : finv Y = N)
    (hlab : v1 N / u1 (Y - G) = w) (hmc : w = MC * f1 N) (hf : f1 N ≠ 0) (hu : u1 (Y - G) ≠ 0) :
    v1 (finv Y) / f1 (finv Y) / u1 (Y - G) = MC := by
  rw [hN]
  rw [hmc] at hlab
  field_simp at hlab ⊢
  linarith

/-- Miao, p. 646: the recursive form of the log-linearised reset price,
`P̂*_t = (1 − βθ)(MĈ_t + P̂_t) + βθP̂*_{t+1}`, from
`P̂*_t = (1 − βθ)Σ_k (θβ)ᵏ(P̂_{t+k} + MĈ_{t+k})`. -/
theorem fs_reset_recursive {β θ : ℝ} {P MC Ps : ℕ → ℝ}
    (hs : ∀ t, Summable fun k => (θ * β) ^ k * (P (t + k) + MC (t + k)))
    (hPs : ∀ t, Ps t = (1 - β * θ) * ∑' k, (θ * β) ^ k * (P (t + k) + MC (t + k))) (t : ℕ) :
    Ps t = (1 - β * θ) * (MC t + P t) + β * θ * Ps (t + 1) := by
  rw [hPs t, hPs (t + 1), (hs t).tsum_eq_zero_add]
  have : ∀ k, (θ * β) ^ (k + 1) * (P (t + (k + 1)) + MC (t + (k + 1))) =
      θ * β * ((θ * β) ^ k * (P (t + 1 + k) + MC (t + 1 + k))) := fun k => by
    rw [show t + (k + 1) = t + 1 + k by ring]
    ring
  simp_rw [this, tsum_mul_left]
  simp only [pow_zero, add_zero, one_mul]
  ring

/-- Miao, p. 646: `q_t = P̂*_t − P̂_t` satisfies
`q_t = (1 − βθ)MĈ_t + βθ(q_{t+1} + P̂_{t+1} − P̂_t)`. -/
theorem fs_q_recursive {β θ : ℝ} {P MC Ps : ℕ → ℝ}
    (hrec : ∀ t, Ps t = (1 - β * θ) * (MC t + P t) + β * θ * Ps (t + 1)) (t : ℕ) :
    Ps t - P t = (1 - β * θ) * MC t + β * θ * ((Ps (t + 1) - P (t + 1)) + P (t + 1) - P t) := by
  rw [hrec t]
  ring

/-- Miao, p. 646: with (19.19) `q_t = θπ_t/(1 − θ)` and `π_{t+1} = P̂_{t+1} − P̂_t`, the
recursion for `q_t` is the New Keynesian Phillips curve
`π_t = βπ_{t+1} + (1 − βθ)(1 − θ)/θ · MĈ_t`. -/
theorem fs_nkpc {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {P MC q infl : ℕ → ℝ}
    (hq : ∀ t, q t = (1 - β * θ) * MC t + β * θ * (q (t + 1) + P (t + 1) - P t))
    (h19 : ∀ t, q t = θ / (1 - θ) * infl t) (hπ : ∀ t, infl (t + 1) = P (t + 1) - P t) (t : ℕ) :
    infl t = β * infl (t + 1) + (1 - β * θ) * (1 - θ) / θ * MC t := by
  have h := hq t
  rw [h19 t, h19 (t + 1), add_sub_assoc, ← hπ t] at h
  have h1 : 1 - θ ≠ 0 := by linarith
  field_simp at h ⊢
  linear_combination h

/-- Miao, p. 646: the log-linearisation of (19.47) `MC = ṽ'(Y)/u'(Y − G)`. Along the direction
`Y = Ȳ(1 + sŶ)`, `G = Ḡ + sȲĜ`, the derivative of `ln MC` at `s = 0` is
`(η_u + η_v)(Ŷ − ΓĜ)`, i.e. `MĈ = (η_u + η_v)(Ŷ − ΓĜ)` to first order. -/
theorem fs_mc_loglin {u1 vt1 : ℝ → ℝ} {Yb Gb u2 vt2 a b : ℝ}
    (hu : HasDerivAt u1 u2 (Yb - Gb)) (hvt : HasDerivAt vt1 vt2 Yb) (hu1 : 0 < u1 (Yb - Gb))
    (hvt1 : 0 < vt1 Yb) (hYb : 0 < Yb)
    (hsum : fs_etaU Yb (u1 (Yb - Gb)) u2 + fs_etaV Yb (vt1 Yb) vt2 ≠ 0) :
    HasDerivAt (fun s => Real.log (vt1 (Yb + s * (Yb * a)) /
        u1 ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))))
      ((fs_etaU Yb (u1 (Yb - Gb)) u2 + fs_etaV Yb (vt1 Yb) vt2) *
        (a - fs_Gamma (fs_etaU Yb (u1 (Yb - Gb)) u2) (fs_etaV Yb (vt1 Yb) vt2) * b)) 0 := by
  have hl1 : HasDerivAt (fun s : ℝ => Yb + s * (Yb * a)) (Yb * a) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (Yb * a)).const_add Yb).congr_deriv (by ring)
  have hl2 : HasDerivAt (fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))
      (Yb * a - Yb * b) 0 :=
    (hl1.sub (((hasDerivAt_id' (0 : ℝ)).mul_const (Yb * b)).const_add Gb)).congr_deriv
      (by ring)
  have hv : HasDerivAt (fun s : ℝ => vt1 (Yb + s * (Yb * a))) (vt2 * (Yb * a)) 0 := by
    have hvt' : HasDerivAt vt1 vt2 (Yb + 0 * (Yb * a)) := by simpa using hvt
    exact hvt'.comp (h := fun s : ℝ => Yb + s * (Yb * a)) 0 hl1
  have hw : HasDerivAt (fun s : ℝ => u1 ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b))))
      (u2 * (Yb * a - Yb * b)) 0 := by
    have hu' : HasDerivAt u1 u2 ((Yb + 0 * (Yb * a)) - (Gb + 0 * (Yb * b))) := by simpa using hu
    exact hu'.comp (h := fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) 0 hl2
  have hq := hv.div hw (by simpa using hu1.ne')
  have hlog := hq.log (by
    simp only [Pi.div_apply, zero_mul, add_zero]
    exact div_ne_zero hvt1.ne' hu1.ne')
  refine hlog.congr_deriv ?_
  simp only [zero_mul, add_zero, Pi.div_apply]
  have hΓ : ∀ A B : ℝ, A + B ≠ 0 → (A + B) * (a - fs_Gamma A B * b) = (A + B) * a - A * b :=
    fun A B h => by
      unfold fs_Gamma
      field_simp
  rw [hΓ _ _ hsum]
  unfold fs_etaU fs_etaV
  field_simp
  ring

/-- Forward solution of `p_t = a p_{t+1} + x_t` with `|a| < 1`: every bounded solution is the
discounted sum `p_t = Σⱼ aʲ x_{t+j}` (Miao, (19.48), p. 646, and (1.8) of Chapter 1). -/
theorem fs_forward_hasSum {a : ℝ} (ha : |a| < 1) {p x : ℕ → ℝ} (hp : fs_Bdd p) (hx : fs_Bdd x)
    (hrec : ∀ t, p t = a * p (t + 1) + x t) (t : ℕ) :
    HasSum (fun j => a ^ j * x (t + j)) (p t) := by
  obtain ⟨B, hB⟩ := hp
  obtain ⟨Bx, hBx⟩ := hx
  have hpart : ∀ n, ∑ j ∈ Finset.range n, a ^ j * x (t + j) = p t - a ^ n * p (t + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hrec (t + n), show t + (n + 1) = t + n + 1 by ring]
      ring
  have haa : |(|a|)| < 1 := by rwa [abs_abs]
  have hsum : Summable (fun j => a ^ j * x (t + j)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one haa).mul_right Bx) ?_
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hBx _) (by positivity)
  rw [hsum.hasSum_iff_tendsto_nat]
  have hz : Tendsto (fun n => a ^ n * p (t + n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => |a| ^ n * B) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const B
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
  have := (tendsto_const_nhds (x := p t)).sub hz
  simp only [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [hpart]

/-- The discounted sum `p_t = Σⱼ aʲ x_{t+j}` (`|a| < 1`, `x` bounded) is a bounded solution of
`p_t = a p_{t+1} + x_t` (Miao, (19.48), p. 646). -/
theorem fs_forward_exists {a : ℝ} (ha : |a| < 1) {x : ℕ → ℝ} (hx : fs_Bdd x) :
    fs_Bdd (fun t => ∑' j, a ^ j * x (t + j)) ∧
      ∀ t, ∑' j, a ^ j * x (t + j) = a * ∑' j, a ^ j * x (t + 1 + j) + x t := by
  obtain ⟨Bx, hBx⟩ := hx
  have haa : |(|a|)| < 1 := by rwa [abs_abs]
  have hbd : ∀ t j, ‖a ^ j * x (t + j)‖ ≤ |a| ^ j * Bx := fun t j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hBx _) (by positivity)
  have hsum : ∀ t, Summable (fun j => a ^ j * x (t + j)) := fun t =>
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one haa).mul_right Bx) (hbd t)
  refine ⟨⟨(1 - |a|)⁻¹ * Bx, fun t => ?_⟩, fun t => ?_⟩
  · have := tsum_of_norm_bounded ((hasSum_geometric_of_abs_lt_one haa).mul_right Bx) (hbd t)
    rwa [Real.norm_eq_abs] at this
  · rw [(hsum t).tsum_eq_zero_add]
    have : ∀ j, a ^ (j + 1) * x (t + (j + 1)) = a * (a ^ j * x (t + 1 + j)) := fun j => by
      rw [show t + (j + 1) = t + 1 + j by ring]
      ring
    simp_rw [this, tsum_mul_left]
    simp only [pow_zero, add_zero, one_mul]
    ring

/-- Miao, p. 646: `κ = (1 − βθ)(1 − θ)(η_u + η_v)/θ > 0`. -/
theorem fs_kappa_pos {β θ ηu ηv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 < ηu) (hv : 0 < ηv) : 0 < (1 - β * θ) * (1 - θ) * (ηu + ηv) / θ := by
  have : β * θ < 1 := by nlinarith
  apply div_pos _ hθ0
  apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- Miao, (19.48), p. 646: combining the Phillips curve
`π_t = βπ_{t+1} + (1 − βθ)(1 − θ)/θ · MĈ_t` with `MĈ_t = (η_u + η_v)(Ŷ_t − ΓĜ_t)`, every bounded
inflation path satisfies `π_t = κΣⱼ βʲ(Ŷ_{t+j} − ΓĜ_{t+j})` with
`κ = (1 − βθ)(1 − θ)(η_u + η_v)/θ`; conversely this sum is a bounded solution. -/
theorem eq_19_48 {β θ ηu ηv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {infl Y G MC : ℕ → ℝ}
    (hY : fs_Bdd Y) (hG : fs_Bdd G)
    (hmc : ∀ t, MC t = (ηu + ηv) * (Y t - fs_Gamma ηu ηv * G t)) :
    ((fs_Bdd infl ∧ ∀ t, infl t = β * infl (t + 1) + (1 - β * θ) * (1 - θ) / θ * MC t) ↔
      ∀ t, infl t = (1 - β * θ) * (1 - θ) * (ηu + ηv) / θ *
        ∑' j, β ^ j * (Y (t + j) - fs_Gamma ηu ηv * G (t + j))) := by
  set κ := (1 - β * θ) * (1 - θ) * (ηu + ηv) / θ
  set Γ := fs_Gamma ηu ηv
  have hβa : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  obtain ⟨BY, hBY⟩ := hY
  obtain ⟨BG, hBG⟩ := hG
  have hx : fs_Bdd (fun t => κ * (Y t - Γ * G t)) := by
    refine ⟨|κ| * (BY + |Γ| * BG), fun t => ?_⟩
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc |Y t - Γ * G t| ≤ |Y t| + |Γ * G t| := abs_sub _ _
      _ ≤ BY + |Γ| * BG := by
        rw [abs_mul]
        exact add_le_add (hBY t) (mul_le_mul_of_nonneg_left (hBG t) (abs_nonneg _))
  have hkx : ∀ t, (1 - β * θ) * (1 - θ) / θ * MC t = κ * (Y t - Γ * G t) := fun t => by
    rw [hmc t]
    ring
  have hfac : ∀ t, ∑' j, β ^ j * (κ * (Y (t + j) - Γ * G (t + j))) =
      κ * ∑' j, β ^ j * (Y (t + j) - Γ * G (t + j)) := fun t => by
    rw [← tsum_mul_left]
    congr 1
    funext j
    ring
  constructor
  · rintro ⟨hπ, hrec⟩ t
    have h := (fs_forward_hasSum hβa hπ hx (fun t => by rw [hrec t, hkx t]) t).tsum_eq
    rw [← h, hfac]
  · intro h
    obtain ⟨hb, hr⟩ := fs_forward_exists hβa hx
    have hπeq : infl = fun t => ∑' j, β ^ j * (κ * (Y (t + j) - Γ * G (t + j))) := by
      funext t
      rw [h t, hfac]
    rw [hπeq]
    refine ⟨hb, fun t => ?_⟩
    beta_reduce
    rw [hkx t, hr t]

/-- Miao, p. 646: the log-linearisation of marginal utility in the Euler equation (19.44). Along
`C = C̄ + sȲ(Ŷ − Ĝ)` the derivative of `ln u'(C)` at `s = 0` is `−η_u(Ŷ − Ĝ)`. -/
theorem fs_euler_loglin {u1 : ℝ → ℝ} {Cb Yb u2 a b : ℝ} (hu : HasDerivAt u1 u2 Cb)
    (hu1 : 0 < u1 Cb) (hYb : 0 < Yb) :
    HasDerivAt (fun s => Real.log (u1 (Cb + s * (Yb * (a - b)))))
      (-fs_etaU Yb (u1 Cb) u2 * (a - b)) 0 := by
  have hl : HasDerivAt (fun s : ℝ => Cb + s * (Yb * (a - b))) (Yb * (a - b)) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (Yb * (a - b))).const_add Cb).congr_deriv (by ring)
  have hu' : HasDerivAt u1 u2 (Cb + 0 * (Yb * (a - b))) := by simpa using hu
  have h := (hu'.comp (h := fun s : ℝ => Cb + s * (Yb * (a - b))) 0 hl).log
    (by simpa using hu1.ne')
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, zero_mul, add_zero]
  unfold fs_etaU
  field_simp

/-- Miao, (19.50), p. 646: with the log-linear marginal utility `ln u'(C_t) = ln u'(C̄) − η_u x_t`
(`x_t = Ŷ_t − Ĝ_t`, `fs_euler_loglin`), the Euler equation (19.44) in logs,
`ln u'(C_t) − ln u'(C_{t+1}) = r_t + ln β` with `r_t = i_t − π_{t+1}` and `r̄ = −ln β`, gives
`x_t = x_{t+1} − σ(i_t − π_{t+1} − r̄)` with `σ = 1/η_u`. -/
theorem eq_19_50 {ηu L x0 x1 l0 l1 i π1 β : ℝ} (hηu : ηu ≠ 0) (h0 : l0 = L - ηu * x0)
    (h1 : l1 = L - ηu * x1) (heul : l0 - l1 = (i - π1) + Real.log β) :
    x0 = x1 - 1 / ηu * (i - π1 - -Real.log β) := by
  rw [h0, h1] at heul
  field_simp
  linear_combination -heul

/-- `ψ = σ(φ_y + κ(φ_π − ρ)/(1 − βρ))` (Miao, p. 647). -/
noncomputable def fs_psi (σ φy κ φπ β ρ : ℝ) : ℝ := σ * (φy + κ / (1 - β * ρ) * (φπ - ρ))

/-- The Taylor-rule multiplier `γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)` (Miao, (19.52), p. 647). -/
noncomputable def fs_gammaY (σ φy κ φπ β ρ Γ : ℝ) : ℝ :=
  (1 - ρ + (fs_psi σ φy κ φπ β ρ - σ * φy) * Γ) / (1 - ρ + fs_psi σ φy κ φπ β ρ)

/-- Miao, p. 647: `ψ > 0` (for `σ, κ > 0`, `φ_y ≥ 0`, `0 < β < 1`, `ρ < 1 < φ_π`), and
`ψ − σφ_y > 0`. -/
theorem fs_psi_pos {σ φy κ φπ β ρ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) :
    0 < fs_psi σ φy κ φπ β ρ - σ * φy ∧ 0 < fs_psi σ φy κ φπ β ρ := by
  have hD : 0 < 1 - β * ρ := by nlinarith
  have h1 : 0 < κ / (1 - β * ρ) * (φπ - ρ) := mul_pos (div_pos hκ hD) (by linarith)
  unfold fs_psi
  constructor
  · nlinarith
  · positivity

/-- Miao, p. 647: `γ_y > 0` (for `0 ≤ Γ`). -/
theorem fs_gammaY_pos {σ φy κ φπ β ρ Γ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) (hΓ : 0 ≤ Γ) :
    0 < fs_gammaY σ φy κ φπ β ρ Γ := by
  obtain ⟨h1, h2⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  unfold fs_gammaY
  apply div_pos _ (by linarith)
  nlinarith [mul_nonneg h1.le hΓ]

/-- Miao, p. 647: "One can check that `γ_y < 1`" (for `Γ < 1`): the multiplier under the Taylor
rule is smaller than under the constant-real-rate policy. -/
theorem fs_gammaY_lt_one {σ φy κ φπ β ρ Γ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) (hΓ : Γ < 1) :
    fs_gammaY σ φy κ φπ β ρ Γ < 1 := by
  obtain ⟨h1, h2⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  unfold fs_gammaY
  rw [div_lt_one (by linarith)]
  nlinarith [mul_pos h1 (sub_pos.2 hΓ), mul_nonneg hσ.le hφy]

/-- Miao, p. 647: the Taylor-rule multiplier is smaller than the neoclassical multiplier `Γ`
iff `φ_y > (1 − ρ)(1 − Γ)/(σΓ)`, i.e. for any large enough `φ_y`. -/
theorem fs_gammaY_lt_Gamma_iff {σ φy κ φπ β ρ Γ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) (hΓ : 0 < Γ) :
    fs_gammaY σ φy κ φπ β ρ Γ < Γ ↔ (1 - ρ) * (1 - Γ) / (σ * Γ) < φy := by
  obtain ⟨h1, h2⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  unfold fs_gammaY
  rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The Taylor-rule equilibrium conditions (19.48)–(19.50) (Miao, pp. 646–647):
`π_t = κΣⱼβʲ(Ŷ_{t+j} − ΓĜ_{t+j})`, `i_t = r̄ + φ_ππ_t + φ_yŶ_t` and
`Ŷ_t − Ĝ_t = Ŷ_{t+1} − Ĝ_{t+1} − σ(i_t − π_{t+1} − r̄)`. -/
def fs_TaylorEqm (κ β σ Γ φπ φy rb : ℝ) (Y infl i G : ℕ → ℝ) : Prop :=
  ∀ t, infl t = κ * ∑' j, β ^ j * (Y (t + j) - Γ * G (t + j)) ∧
    i t = rb + φπ * infl t + φy * Y t ∧
    Y t - G t = Y (t + 1) - G (t + 1) - σ * (i t - infl (t + 1) - rb)

/-- Miao, (19.51)–(19.52), p. 647: with `Ĝ_t = ρᵗĜ₀`, `Ĝ₀ ≠ 0`, the conjecture
`Ŷ_t = γ_yĜ_t`, `π_t = γ_πĜ_t`, `i_t = r̄ + γ_iĜ_t` is an equilibrium iff
`γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)` (19.52), `γ_π = κ(γ_y − Γ)/(1 − βρ)` and
`γ_i = φ_πγ_π + φ_yγ_y`. -/
theorem eq_19_52 {κ β σ Γ φπ φy rb ρ G0 γy γπ γi : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hφπ : 1 < φπ)
    (hG0 : G0 ≠ 0) :
    fs_TaylorEqm κ β σ Γ φπ φy rb (fun t => γy * (ρ ^ t * G0)) (fun t => γπ * (ρ ^ t * G0))
        (fun t => rb + γi * (ρ ^ t * G0)) (fun t => ρ ^ t * G0) ↔
      γy = fs_gammaY σ φy κ φπ β ρ Γ ∧ γπ = κ * (γy - Γ) / (1 - β * ρ) ∧
        γi = φπ * γπ + φy * γy := by
  have hD : 0 < 1 - β * ρ := by nlinarith
  have hβρ0 : 0 ≤ β * ρ := by positivity
  have hβρ1 : β * ρ < 1 := by nlinarith
  obtain ⟨-, hψ⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  have hsum : ∀ t, ∑' j, β ^ j * (γy * (ρ ^ (t + j) * G0) - Γ * (ρ ^ (t + j) * G0)) =
      (γy - Γ) * (ρ ^ t * G0) / (1 - β * ρ) := fun t => by
    have : ∀ j, β ^ j * (γy * (ρ ^ (t + j) * G0) - Γ * (ρ ^ (t + j) * G0)) =
        (γy - Γ) * (ρ ^ t * G0) * (β * ρ) ^ j := fun j => by
      rw [pow_add, mul_pow]
      ring
    simp_rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβρ0 hβρ1]
    field_simp
  unfold fs_TaylorEqm
  simp_rw [hsum]
  have hψd : 0 < 1 - ρ + fs_psi σ φy κ φπ β ρ := by linarith
  have hc : κ * (γy - Γ) / (1 - β * ρ) = κ / (1 - β * ρ) * (γy - Γ) := by ring
  rw [hc]
  constructor
  · intro h
    obtain ⟨e1, e2, e3⟩ := h 0
    simp only [pow_zero, one_mul, zero_add, pow_one] at e1 e2 e3
    have hγπ : γπ = κ / (1 - β * ρ) * (γy - Γ) := by
      apply mul_right_cancel₀ hG0
      rw [e1]
      ring
    have hγi : γi = φπ * γπ + φy * γy := by
      apply mul_right_cancel₀ hG0
      linear_combination e2
    have key : (1 - ρ) * (γy - 1) = -σ * (γi - ρ * γπ) := by
      apply mul_right_cancel₀ hG0
      linear_combination e3
    refine ⟨?_, hγπ, hγi⟩
    rw [hγi, hγπ] at key
    unfold fs_gammaY
    rw [eq_div_iff hψd.ne']
    unfold fs_psi
    linear_combination key
  · rintro ⟨hγy, hγπ, hγi⟩ t
    have hγ' : γy * (1 - ρ + fs_psi σ φy κ φπ β ρ) =
        1 - ρ + (fs_psi σ φy κ φπ β ρ - σ * φy) * Γ := by
      rw [hγy]
      unfold fs_gammaY
      field_simp
    have key : (1 - ρ) * (γy - 1) = -σ * (γi - ρ * γπ) := by
      rw [hγi, hγπ]
      unfold fs_psi at hγ'
      linear_combination hγ'
    refine ⟨?_, ?_, ?_⟩
    · rw [hγπ]
      ring
    · rw [hγi]
      ring
    · rw [pow_succ]
      linear_combination (ρ ^ t * G0) * key

end Miao.NewKeynesian
