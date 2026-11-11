/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXAdjustment
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Investment adjustment costs (14.50)–(14.52) and Exercise 14.6

Miao, §14.3.3, pp. 500–501, and Exercise 14.6, p. 508, on the event tree of `RXTree`.

* With `K_{t+1} = (1 − δ)Kₜ + G(Iₜ, I_{t−1})`, the firm's first-order conditions (14.50) and
  (14.51) are the stationarity of its Lagrangian in `Iₜ` and in `K_{t+1}` (`eq_14_50`,
  `eq_14_51`); `Iₜ` enters `G(Iₜ, I_{t−1})` at `t` and `G(I_{t+1}, Iₜ)` at every successor.
* (14.52) `G(I, I₋) = (1 − S(I/I₋))I`: partial derivatives `G₁ = 1 − S(x) − xS′(x)`,
  `G₂ = S′(x)x²`, `x = I/I₋` (`rx_G52`, `rx_G52_d1`, `rx_G52_d2`); with `S(1) = S′(1) = 0`,
  `G(I, I) = I`, `G₁ = 1`, `G₂ = 0` at `x = 1` (`rx_G52_steady`); the steady state has
  `I/K = δ`, `Q = 1`, `zF_K = 1/β − 1 + δ`, independently of `κ` (`eq_14_52_steady`).
* **Exercise 14.6** (risk neutrality: `Λ` constant, so the discount factor is `β`). Each
  log-linearised equation is the derivative at `ε = 0` of the equation along the path
  `X = X̄e^{εx̂}` of every variable (log-deviations `x̂`), at the steady state `I/K = δ`,
  `Q = 1`, `R̄_k = 1/β − 1 + δ`:
  - (14.43): `q̂ₜ + κδ(îₜ − k̂ₜ) = 0` (`ex_14_6_invest_43`, solved
    `îₜ − k̂ₜ = −q̂ₜ/(κδ)` in `ex_14_6_invest_43_solved`), `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ`
    (`ex_14_6_capital_43`) and `q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + (1 − δ)q̂_{t+1} − κδ²(î_{t+1} −
    k̂_{t+1})]` (`ex_14_6_Q_43`), which with the investment equation is
    `q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + q̂_{t+1}]` (`ex_14_6_Q_43_solved`);
  - (14.52): `q̂ₜ − κ(îₜ − î_{t−1}) + βκ(Eₜî_{t+1} − îₜ) = 0` (`ex_14_6_invest_52`), i.e.
    `îₜ = î_{t−1}/(1 + β) + βEₜî_{t+1}/(1 + β) + q̂ₜ/(κ(1 + β))` (`ex_14_6_invest_52_solved`),
    `q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + (1 − δ)q̂_{t+1}]` (`ex_14_6_Q_52`) and
    `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ` (`ex_14_6_capital_52`).
  - The differences (`ex_14_6_differences`): under (14.43) the investment rate depends only on
    current `q̂`; under (14.52) investment depends on lagged investment with weight
    `1/(1 + β) ∈ (0, 1)` (inertia), and the `q̂` equations differ by the term `δq̂_{t+1}`.
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- Miao, (14.50), p. 500. The terms of the firm's Lagrangian (multiplier `ΛQ` on
`K_{t+1} = (1 − δ)Kₜ + G(Iₜ, I_{t−1})`) in `Iₜ = x` at the node `h` are
`Λₜ(−x + QₜG(x, I_{t−1})) + βEₜΛ_{t+1}Q_{t+1}G(I_{t+1}, x)`. Their derivative is
`Λₜ(QₜG₁ + Eₜ[βΛ_{t+1}Q_{t+1}G₂/Λₜ] − 1)`; for `Λₜ ≠ 0` stationarity is (14.50):
`QₜG₁(Iₜ, I_{t−1}) + Eₜ[βΛ_{t+1}Q_{t+1}G₂(I_{t+1}, Iₜ)/Λₜ] = 1`. -/
theorem eq_14_50 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {G : ℝ × ℝ → ℝ}
    {β Λt Qt It Ip G1 : ℝ} {Λ Q I G2 : S → ℝ} (hΛ : Λt ≠ 0)
    (hG1 : HasDerivAt (fun x => G (x, Ip)) G1 It)
    (hG2 : ∀ s, HasDerivAt (fun x => G (I s, x)) (G2 s) It) :
    HasDerivAt (fun x => Λt * (-x + Qt * G (x, Ip)) + β * ∑ s, T.cp h s * (Λ s * Q s *
        G (I s, x)))
      (Λt * (Qt * G1 + rx_Es T h (fun s => β * Λ s / Λt * Q s * G2 s) - 1)) It ∧
    (Λt * (Qt * G1 + rx_Es T h (fun s => β * Λ s / Λt * Q s * G2 s) - 1) = 0 ↔
      Qt * G1 + rx_Es T h (fun s => β * Λ s / Λt * Q s * G2 s) = 1) := by
  refine ⟨?_, ?_⟩
  · have hs : HasDerivAt (fun x => ∑ s, T.cp h s * (Λ s * Q s * G (I s, x)))
        (∑ s, T.cp h s * (Λ s * Q s * G2 s)) It :=
      HasDerivAt.fun_sum fun s _ => ((hG2 s).const_mul _).const_mul _
    have := (((hasDerivAt_id' It).neg.add (hG1.const_mul Qt)).const_mul Λt).add
      (hs.const_mul β)
    refine this.congr_deriv ?_
    have e : Λt * ∑ s, T.cp h s * (β * Λ s / Λt * Q s * G2 s) =
        β * ∑ s, T.cp h s * (Λ s * Q s * G2 s) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    simp only [rx_Es]
    linear_combination -e
  · constructor
    · intro h0
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 hΛ
      · linarith
    · intro h0
      rw [h0, sub_self, mul_zero]

/-- Miao, (14.51), p. 500. The terms of the Lagrangian in `K_{t+1} = k` are
`−ΛₜQₜk + βEₜΛ_{t+1}[z_{t+1}F(k, N_{t+1}) + Q_{t+1}(1 − δ)k]` (with investment adjustment costs
`K_{t+1}` does not enter `G`); stationarity is (14.51)
`ΛₜQₜ = βEₜΛ_{t+1}[z_{t+1}F_K(K_{t+1}, N_{t+1}) + Q_{t+1}(1 − δ)]`. -/
theorem eq_14_51 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {F : ℝ × ℝ → ℝ}
    {β δ Λt Qt K1 : ℝ} {Λ Q z N FK : S → ℝ}
    (hF : ∀ s, HasDerivAt (fun k => F (k, N s)) (FK s) K1) :
    HasDerivAt (fun k => Λt * (-(Qt * k)) + β * ∑ s, T.cp h s * (Λ s * (z s * F (k, N s) +
        Q s * (1 - δ) * k)))
      (β * rx_Es T h (fun s => Λ s * (z s * FK s + Q s * (1 - δ))) - Λt * Qt) K1 ∧
    (β * rx_Es T h (fun s => Λ s * (z s * FK s + Q s * (1 - δ))) - Λt * Qt = 0 ↔
      Λt * Qt = β * rx_Es T h (fun s => Λ s * (z s * FK s + Q s * (1 - δ)))) := by
  refine ⟨?_, by constructor <;> intro h0 <;> linarith⟩
  have hs : HasDerivAt (fun k => ∑ s, T.cp h s * (Λ s * (z s * F (k, N s) + Q s * (1 - δ) * k)))
      (∑ s, T.cp h s * (Λ s * (z s * FK s + Q s * (1 - δ) * 1))) K1 :=
    HasDerivAt.fun_sum fun s _ => ((((hF s).const_mul (z s)).add
      ((hasDerivAt_id' K1).const_mul _)).const_mul _).const_mul _
  have := ((((hasDerivAt_id' K1).const_mul Qt).neg).const_mul Λt).add (hs.const_mul β)
  refine this.congr_deriv ?_
  simp only [rx_Es, mul_one]
  ring

/-- The investment adjustment cost function (14.52), `G(I, I₋) = (1 − S(I/I₋))I`. -/
noncomputable def rx_G52 (S : ℝ → ℝ) (I Ip : ℝ) : ℝ := (1 - S (I / Ip)) * I

/-- Miao, (14.52), p. 500: `G₁ = 1 − S(x) − xS′(x)` with `x = I/I₋`. -/
theorem rx_G52_d1 {S : ℝ → ℝ} {dS I Ip : ℝ} (hS : HasDerivAt S dS (I / Ip)) :
    HasDerivAt (fun y => rx_G52 S y Ip) (1 - S (I / Ip) - I / Ip * dS) I := by
  have h1 := hS.comp I ((hasDerivAt_id' I).div_const Ip)
  have := ((hasDerivAt_const I (1 : ℝ)).sub h1).mul (hasDerivAt_id' I)
  unfold rx_G52
  refine this.congr_deriv ?_
  simp only [Function.comp_def, Pi.sub_apply]
  ring

/-- Miao, (14.52), p. 500: `G₂ = S′(x)x²` with `x = I/I₋`, `I₋ ≠ 0`. -/
theorem rx_G52_d2 {S : ℝ → ℝ} {dS I Ip : ℝ} (hIp : Ip ≠ 0) (hS : HasDerivAt S dS (I / Ip)) :
    HasDerivAt (fun y => rx_G52 S I y) (dS * (I / Ip) ^ 2) Ip := by
  have hd : HasDerivAt (fun y => I / y) (-(I / Ip ^ 2)) Ip := by
    have := (hasDerivAt_inv hIp).const_mul I
    simpa [div_eq_mul_inv] using this
  have h1 := hS.comp Ip hd
  have := ((hasDerivAt_const Ip (1 : ℝ)).sub h1).mul_const I
  unfold rx_G52
  refine this.congr_deriv ?_
  field_simp
  ring

/-- Miao, p. 500: with `S(1) = S′(1) = 0`, `G(I, I) = I` (for every `I`), and at `I = I₋ ≠ 0`
the partial derivatives are `G₁ = 1`, `G₂ = 0`. -/
theorem rx_G52_steady {S : ℝ → ℝ} {dS1 I : ℝ} (hS0 : S 1 = 0) (hdS : dS1 = 0) (hI : I ≠ 0) :
    rx_G52 S I I = I ∧ 1 - S (I / I) - I / I * dS1 = 1 ∧ dS1 * (I / I) ^ 2 = 0 := by
  simp [rx_G52, div_self hI, hS0, hdS]

/-- `G(I, I) = I` also at `I = 0`. -/
theorem rx_G52_diag {S : ℝ → ℝ} (hS0 : S 1 = 0) (I : ℝ) : rx_G52 S I I = I := by
  rcases eq_or_ne I 0 with h | h
  · simp [rx_G52, h]
  · exact (rx_G52_steady hS0 rfl h).1

/-- Miao, p. 500: "these assumptions ensure that the steady-state investment rate `I/K` is
equal to `δ` and `Q = 1`" and `κ` does not affect the nonstochastic steady state. In a steady
state with constant `Λ`, constant investment `I ≠ 0` and `K > 0`: `K = (1 − δ)K + G(I, I)`,
(14.50) `QG₁ + βQG₂ = 1` and (14.51) `Q = β(zF_K + Q(1 − δ))` give `I/K = δ`, `Q = 1` and
`zF_K = 1/β − 1 + δ`. -/
theorem eq_14_52_steady {S : ℝ → ℝ} {dS1 δ β K I Q zFK : ℝ} (hS0 : S 1 = 0) (hdS : dS1 = 0)
    (hβ : 0 < β) (hK : 0 < K) (hI : I ≠ 0) (hacc : K = (1 - δ) * K + rx_G52 S I I)
    (h50 : Q * (1 - S (I / I) - I / I * dS1) + β * Q * (dS1 * (I / I) ^ 2) = 1)
    (h51 : Q = β * (zFK + Q * (1 - δ))) : I / K = δ ∧ Q = 1 ∧ zFK = 1 / β - 1 + δ := by
  obtain ⟨e0, e1, e2⟩ := rx_G52_steady hS0 hdS hI
  rw [e0] at hacc
  rw [e1, e2] at h50
  have hQ : Q = 1 := by linarith
  refine ⟨?_, hQ, ?_⟩
  · field_simp
    linarith
  · rw [hQ] at h51
    field_simp
    linarith

/-- `ε ↦ c·e^{εa}` has derivative `ca` at `0`. -/
theorem rx_hasDerivAt_exp (c a : ℝ) : HasDerivAt (fun ε => c * Real.exp (ε * a)) (c * a) 0 := by
  have := (((hasDerivAt_id' (0 : ℝ)).mul_const a).exp).const_mul c
  refine this.congr_deriv ?_
  simp

/-- `ε ↦ e^{εa}` has derivative `a` at `0`. -/
theorem rx_hasDerivAt_exp1 (a : ℝ) : HasDerivAt (fun ε => Real.exp (ε * a)) a 0 := by
  have := ((hasDerivAt_id' (0 : ℝ)).mul_const a).exp
  refine this.congr_deriv ?_
  simp

/-- Along the path `I = Īe^{εî}`, `K = K̄e^{εk̂}` with `Ī = δK̄`, the investment rate is
`I/K = δe^{ε(î − k̂)}`. -/
theorem rx_ratio_path {δ Kb ι k ε : ℝ} (hK : Kb ≠ 0) :
    δ * Kb * Real.exp (ε * ι) / (Kb * Real.exp (ε * k)) = δ * Real.exp (ε * (ι - k)) := by
  rw [mul_sub, Real.exp_sub]
  have := Real.exp_pos (ε * k)
  field_simp

/-- The rate path `ε ↦ δe^{ε(î − k̂)}` composed with a function differentiable at `δ`. -/
theorem rx_hasDerivAt_rate {f : ℝ → ℝ} {df δ ι k : ℝ} (hf : HasDerivAt f df δ) :
    HasDerivAt (fun ε => f (δ * Real.exp (ε * (ι - k)))) (df * (δ * (ι - k))) 0 := by
  have hp := rx_hasDerivAt_exp δ (ι - k)
  have hf' : HasDerivAt f df (δ * Real.exp (0 * (ι - k))) := by simpa using hf
  exact hf'.comp 0 hp

/-- **Exercise 14.6** (Miao, p. 508), (14.43), the investment equation `Qϕ′(I/K) = 1`. Along
`Q = e^{εq̂}`, `I/K = δe^{ε(î − k̂)}`, with `ϕ′(δ) = 1` and `ϕ″(δ) = κ`, the derivative at
`ε = 0` is `q̂ + κδ(î − k̂)`: the log-linearised equation is `q̂ₜ + κδ(îₜ − k̂ₜ) = 0`. -/
theorem ex_14_6_invest_43 {dϕ : ℝ → ℝ} {δ κ q ι k : ℝ} (h1 : dϕ δ = 1)
    (hκ : HasDerivAt dϕ κ δ) :
    HasDerivAt (fun ε => Real.exp (ε * q) * dϕ (δ * Real.exp (ε * (ι - k))) - 1)
      (q + κ * δ * (ι - k)) 0 := by
  have h := ((rx_hasDerivAt_exp 1 q).mul (rx_hasDerivAt_rate (ι := ι) (k := k) hκ)).sub_const 1
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun ε => by simp)
  simp [h1]
  ring

/-- **Exercise 14.6**, (14.43): solving the linearised investment equation, the investment
rate is proportional to the current `q̂`: `îₜ − k̂ₜ = −q̂ₜ/(κδ)` (`κ < 0`, so `î − k̂` rises
with `q̂`). -/
theorem ex_14_6_invest_43_solved {δ κ q ι k : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 0) :
    q + κ * δ * (ι - k) = 0 ↔ ι - k = -q / (κ * δ) := by
  constructor
  · intro h0
    field_simp
    linarith
  · intro h0
    rw [h0]
    field_simp
    ring

/-- **Exercise 14.6**, (14.43), capital accumulation `K_{t+1} = (1 − δ)Kₜ + ϕ(Iₜ/Kₜ)Kₜ`. Along
`K_{t+1} = K̄e^{εk̂′}`, `Kₜ = K̄e^{εk̂}`, `Iₜ/Kₜ = δe^{ε(î − k̂)}`, with `ϕ(δ) = δ`, `ϕ′(δ) = 1`,
the derivative is `K̄(k̂′ − (1 − δ)k̂ − δî)`: `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ`. -/
theorem ex_14_6_capital_43 {ϕ : ℝ → ℝ} {δ Kb k' k ι : ℝ} (h0 : ϕ δ = δ)
    (h1 : HasDerivAt ϕ 1 δ) :
    HasDerivAt (fun ε => Kb * Real.exp (ε * k') - (1 - δ) * (Kb * Real.exp (ε * k))
        - ϕ (δ * Real.exp (ε * (ι - k))) * (Kb * Real.exp (ε * k)))
      (Kb * (k' - (1 - δ) * k - δ * ι)) 0 := by
  have h := ((rx_hasDerivAt_exp Kb k').sub ((rx_hasDerivAt_exp Kb k).const_mul (1 - δ))).sub
    ((rx_hasDerivAt_rate (ι := ι) (k := k) h1).mul (rx_hasDerivAt_exp Kb k))
  refine h.congr_deriv ?_
  simp [h0]
  ring

/-- **Exercise 14.6**, (14.43), the Q equation under risk neutrality,
`Qₜ = βEₜ[R_{k,t+1} + Q_{t+1}(1 − δ + Φ_K)]` with `Φ_K = ϕ(i) − iϕ′(i)`. Along
`Qₜ = e^{εq̂}`, `R_k(s) = R̄e^{εr̂(s)}`, `Q(s) = e^{εq̂(s)}`, `i(s) = δe^{ε(î(s) − k̂(s))}`, with
`ϕ(δ) = δ`, `ϕ′(δ) = 1`, `ϕ″(δ) = κ`, the derivative at `0` is
`q̂ − βEₜ[R̄r̂ + (1 − δ)q̂′ − κδ²(î′ − k̂′)]`. -/
theorem ex_14_6_Q_43 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {ϕ dϕ : ℝ → ℝ}
    {δ κ β Rb q : ℝ} {r q1 ι1 k1 : S → ℝ} (h0 : ϕ δ = δ) (h1 : dϕ δ = 1)
    (hϕ : HasDerivAt ϕ 1 δ) (hκ : HasDerivAt dϕ κ δ) :
    HasDerivAt (fun ε => Real.exp (ε * q) - β * ∑ s, T.cp h s * (Rb * Real.exp (ε * r s) +
        Real.exp (ε * q1 s) * (1 - δ + (ϕ (δ * Real.exp (ε * (ι1 s - k1 s))) -
          δ * Real.exp (ε * (ι1 s - k1 s)) * dϕ (δ * Real.exp (ε * (ι1 s - k1 s)))))))
      (q - β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s
        - κ * δ ^ 2 * (ι1 s - k1 s))) 0 := by
  have hs : ∀ s, HasDerivAt (fun ε => T.cp h s * (Rb * Real.exp (ε * r s) +
      Real.exp (ε * q1 s) * (1 - δ + (ϕ (δ * Real.exp (ε * (ι1 s - k1 s))) -
        δ * Real.exp (ε * (ι1 s - k1 s)) * dϕ (δ * Real.exp (ε * (ι1 s - k1 s)))))))
      (T.cp h s * (Rb * r s + (1 - δ) * q1 s - κ * δ ^ 2 * (ι1 s - k1 s))) 0 := by
    intro s
    have hA := rx_hasDerivAt_rate (ι := ι1 s) (k := k1 s) hϕ
    have hB := rx_hasDerivAt_exp δ (ι1 s - k1 s)
    have hC := rx_hasDerivAt_rate (ι := ι1 s) (k := k1 s) hκ
    have hK := (hA.sub (hB.mul hC)).const_add (1 - δ)
    have := ((rx_hasDerivAt_exp Rb (r s)).add ((rx_hasDerivAt_exp1 (q1 s)).mul hK)).const_mul
      (T.cp h s)
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, zero_mul, Real.exp_zero, mul_one, h0, h1]
    ring
  exact (rx_hasDerivAt_exp1 q).sub
    ((HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hs s).const_mul β)

/-- **Exercise 14.6**, (14.43): substituting the linearised investment equation at `t + 1`
(`κδ(î′ − k̂′) = −q̂′`) into `ex_14_6_Q_43`, the Q equation is
`q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + q̂_{t+1}]`. -/
theorem ex_14_6_Q_43_solved {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ κ β Rb q : ℝ} {r q1 ι1 k1 : S → ℝ} (hinv : ∀ s, q1 s + κ * δ * (ι1 s - k1 s) = 0) :
    q - β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s - κ * δ ^ 2 * (ι1 s - k1 s)) = 0 ↔
      q = β * rx_Es T h (fun s => Rb * r s + q1 s) := by
  have e : ∀ s, Rb * r s + (1 - δ) * q1 s - κ * δ ^ 2 * (ι1 s - k1 s) = Rb * r s + q1 s := by
    intro s
    linear_combination (-δ) * hinv s
  simp only [e]
  constructor <;> intro h0 <;> linarith

/-- The functions `g₁(x) = 1 − S(x) − xS′(x)` and `g₂(x) = S′(x)x²` of (14.52) have, with
`S(1) = S′(1) = 0` and `S″(1) = κ`, the values `g₁(1) = 1`, `g₂(1) = 0` and derivatives
`g₁′(1) = −κ`, `g₂′(1) = κ`. -/
theorem rx_g52_derivs {S dS : ℝ → ℝ} {κ : ℝ} (hS0 : S 1 = 0) (hdS0 : dS 1 = 0)
    (hS : HasDerivAt S (dS 1) 1) (hκ : HasDerivAt dS κ 1) :
    (1 - S 1 - 1 * dS 1 = 1) ∧ dS 1 * 1 ^ 2 = 0 ∧
      HasDerivAt (fun x => 1 - S x - x * dS x) (-κ) 1 ∧
      HasDerivAt (fun x => dS x * x ^ 2) κ 1 := by
  refine ⟨by simp [hS0, hdS0], by simp [hdS0], ?_, ?_⟩
  · have := ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hS).sub ((hasDerivAt_id' 1).mul hκ)
    refine this.congr_deriv ?_
    simp [hdS0]
  · have := hκ.mul ((hasDerivAt_id' (1 : ℝ)).pow 2)
    refine this.congr_deriv ?_
    simp [hdS0]

/-- `g₁(x) = 1 − S(x) − xS′(x)`, so that `G₁(I, I₋) = g₁(I/I₋)` for (14.52) (`rx_G52_d1`). -/
noncomputable def rx_g1 (S dS : ℝ → ℝ) (x : ℝ) : ℝ := 1 - S x - x * dS x

/-- `g₂(x) = S′(x)x²`, so that `G₂(I, I₋) = g₂(I/I₋)` for (14.52) (`rx_G52_d2`). -/
noncomputable def rx_g2 (dS : ℝ → ℝ) (x : ℝ) : ℝ := dS x * x ^ 2

/-- **Exercise 14.6** (Miao, p. 508), (14.52), the investment equation (14.50) under risk
neutrality, `QₜG₁(Iₜ, I_{t−1}) + βEₜQ_{t+1}G₂(I_{t+1}, Iₜ) = 1`, with `G₁ = g₁(Iₜ/I_{t−1})`,
`G₂ = g₂(I_{t+1}/Iₜ)`. Along `Q = e^{εq̂}`, `Iₜ/I_{t−1} = e^{ε(îₜ − î_{t−1})}`,
`I_{t+1}/Iₜ = e^{ε(î_{t+1} − îₜ)}`, with `S(1) = S′(1) = 0`, `S″(1) = κ`, the derivative at `0`
is `q̂ₜ − κ(îₜ − î_{t−1}) + βκ(Eₜî_{t+1} − îₜ)`. -/
theorem ex_14_6_invest_52 {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Sf dS : ℝ → ℝ} {κ β q ι ιm : ℝ} {q1 ι1 : S → ℝ} (hS0 : Sf 1 = 0) (hdS0 : dS 1 = 0)
    (hS : HasDerivAt Sf (dS 1) 1) (hκ : HasDerivAt dS κ 1) :
    HasDerivAt (fun ε => Real.exp (ε * q) * rx_g1 Sf dS (Real.exp (ε * (ι - ιm))) + β * ∑ s,
        T.cp h s * (Real.exp (ε * q1 s) * rx_g2 dS (Real.exp (ε * (ι1 s - ι)))) - 1)
      (q - κ * (ι - ιm) + β * κ * (rx_Es T h ι1 - ι)) 0 := by
  obtain ⟨e1, e2, d1, d2⟩ := rx_g52_derivs hS0 hdS0 hS hκ
  have d1' : HasDerivAt (rx_g1 Sf dS) (-κ) (Real.exp (0 * (ι - ιm))) := by
    rw [zero_mul, Real.exp_zero]
    exact d1
  have hA := (rx_hasDerivAt_exp1 q).mul (d1'.comp 0 (rx_hasDerivAt_exp1 (ι - ιm)))
  have hs : ∀ s, HasDerivAt (fun ε => T.cp h s * (Real.exp (ε * q1 s) *
      rx_g2 dS (Real.exp (ε * (ι1 s - ι))))) (T.cp h s * (κ * (ι1 s - ι))) 0 := by
    intro s
    have d2' : HasDerivAt (rx_g2 dS) κ (Real.exp (0 * (ι1 s - ι))) := by
      rw [zero_mul, Real.exp_zero]
      exact d2
    have := ((rx_hasDerivAt_exp1 (q1 s)).mul (d2'.comp 0 (rx_hasDerivAt_exp1 (ι1 s - ι)))).const_mul
      (T.cp h s)
    refine this.congr_deriv ?_
    simp only [zero_mul, Real.exp_zero, Function.comp_apply]
    have : rx_g2 dS 1 = 0 := e2
    rw [this]
    ring
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hs s).const_mul β
  refine ((hA.add hsum).sub_const 1).congr_deriv ?_
  have : rx_g1 Sf dS 1 = 1 := e1
  simp only [zero_mul, Real.exp_zero, Function.comp_apply, this, rx_Es]
  have hc : ∑ s, T.cp h s * (κ * (ι1 s - ι)) = κ * (∑ s, T.cp h s * ι1 s - ι) := by
    have : ∑ s, T.cp h s * (κ * (ι1 s - ι)) = κ * ∑ s, T.cp h s * ι1 s -
        κ * ι * ∑ s, T.cp h s := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, T.cp_sum]
    ring
  rw [hc]
  ring

/-- **Exercise 14.6**, (14.52): solving the linearised investment equation,
`îₜ = î_{t−1}/(1 + β) + βEₜî_{t+1}/(1 + β) + q̂ₜ/(κ(1 + β))`. -/
theorem ex_14_6_invest_52_solved {κ β q ι ιm Eι : ℝ} (hκ : κ ≠ 0) (hβ : 0 < β) :
    q - κ * (ι - ιm) + β * κ * (Eι - ι) = 0 ↔
      ι = ιm / (1 + β) + β / (1 + β) * Eι + q / (κ * (1 + β)) := by
  have h1 : (1 + β) ≠ 0 := by linarith
  constructor
  · intro h0
    field_simp
    linear_combination -h0
  · intro h0
    rw [h0]
    field_simp
    ring

/-- **Exercise 14.6**, (14.52), the Q equation (14.51) under risk neutrality,
`Qₜ = βEₜ[R_{k,t+1} + Q_{t+1}(1 − δ)]`: along `Qₜ = e^{εq̂}`, `R_k(s) = R̄e^{εr̂(s)}`,
`Q(s) = e^{εq̂(s)}` the derivative is `q̂ − βEₜ[R̄r̂ + (1 − δ)q̂′]`. -/
theorem ex_14_6_Q_52 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {δ β Rb q : ℝ}
    {r q1 : S → ℝ} :
    HasDerivAt (fun ε => Real.exp (ε * q) - β * ∑ s, T.cp h s * (Rb * Real.exp (ε * r s) +
        Real.exp (ε * q1 s) * (1 - δ)))
      (q - β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s)) 0 := by
  have hs : ∀ s, HasDerivAt (fun ε => T.cp h s * (Rb * Real.exp (ε * r s) +
      Real.exp (ε * q1 s) * (1 - δ))) (T.cp h s * (Rb * r s + (1 - δ) * q1 s)) 0 := by
    intro s
    have := ((rx_hasDerivAt_exp Rb (r s)).add ((rx_hasDerivAt_exp1 (q1 s)).mul_const
      (1 - δ))).const_mul (T.cp h s)
    exact this.congr_deriv (by ring)
  exact (rx_hasDerivAt_exp1 q).sub
    ((HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hs s).const_mul β)

/-- **Exercise 14.6**, (14.52), capital accumulation
`K_{t+1} = (1 − δ)Kₜ + (1 − S(Iₜ/I_{t−1}))Iₜ`: along `K_{t+1} = K̄e^{εk̂′}`, `Kₜ = K̄e^{εk̂}`,
`Iₜ = δK̄e^{εî}`, `Iₜ/I_{t−1} = e^{ε(î − î₋)}`, with `S(1) = S′(1) = 0`, the derivative is
`K̄(k̂′ − (1 − δ)k̂ − δî)`: `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ`. -/
theorem ex_14_6_capital_52 {Sf : ℝ → ℝ} {dS1 δ Kb k' k ι ιm : ℝ} (hS0 : Sf 1 = 0)
    (hdS0 : dS1 = 0) (hS : HasDerivAt Sf dS1 1) :
    HasDerivAt (fun ε => Kb * Real.exp (ε * k') - (1 - δ) * (Kb * Real.exp (ε * k))
        - (1 - Sf (Real.exp (ε * (ι - ιm)))) * (δ * Kb * Real.exp (ε * ι)))
      (Kb * (k' - (1 - δ) * k - δ * ι)) 0 := by
  have hS' : HasDerivAt Sf dS1 (Real.exp (0 * (ι - ιm))) := by simpa using hS
  have hc := hS'.comp 0 (rx_hasDerivAt_exp1 (ι - ιm))
  have h := ((rx_hasDerivAt_exp Kb k').sub ((rx_hasDerivAt_exp Kb k).const_mul (1 - δ))).sub
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hc).mul (rx_hasDerivAt_exp (δ * Kb) ι))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Function.comp_apply, zero_mul, Real.exp_zero, hS0, hdS0]
  ring

/-- **Exercise 14.6** (Miao, p. 508), "discuss the differences". (1) Under (14.43) the
linearised investment rate is pinned down by the current `q̂` alone: two solutions with the same
`q̂ₜ` and `k̂ₜ` have the same `îₜ`, whatever past investment was. (2) Under (14.52) current
investment puts the weight `1/(1 + β) ∈ (0, 1)` on lagged investment (inertia) and
`β/(1 + β)` on expected future investment, the weights summing to one. (3) The two `q̂`
equations differ by `βδEₜq̂_{t+1}`. -/
theorem ex_14_6_differences {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ κ β Rb : ℝ} {r q1 : S → ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 0) (hβ : 0 < β) :
    (∀ q ι ι' k : ℝ, q + κ * δ * (ι - k) = 0 → q + κ * δ * (ι' - k) = 0 → ι = ι') ∧
    (0 < 1 / (1 + β) ∧ 1 / (1 + β) < 1 ∧ 1 / (1 + β) + β / (1 + β) = 1) ∧
    β * rx_Es T h (fun s => Rb * r s + q1 s) -
      β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s) = β * δ * rx_Es T h q1 := by
  refine ⟨fun q ι ι' k h1 h2 => ?_, ⟨by positivity, ?_, ?_⟩, ?_⟩
  · have : κ * δ * (ι - ι') = 0 := by linarith
    have hkd : κ * δ ≠ 0 := mul_ne_zero hκ hδ
    have := (mul_eq_zero.1 this).resolve_left hkd
    linarith
  · rw [div_lt_one (by linarith)]
    linarith
  · field_simp
  · simp only [rx_Es, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring

end Miao.NeoclassicalGrowth
