/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXAdjustment
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §14.3.4 Stochastic trends

Miao, §14.3.4, pp. 501–503: the basic RBC model (log utility `ln C + χ ln(1 − N)`,
`Y = zK^α N^{1−α}`) with a unit-root technology shock `ln zₜ = μ_z + ln z_{t−1} + σεₜ`,
`z_{−1} = 1`.

* The random walk with drift: `ln zₜ = (t + 1)μ_z + σΣ_{j≤t} εⱼ` (`rx_lnz_walk`).
* Detrending: `X̃ₜ = Xₜ/zₜ^{1/(1−α)}` for `C, I, Y, w`, `K̃_{t+1} = K_{t+1}/zₜ^{1/(1−α)}`; with
  `zₜ = z_{t−1}e^{μ_z + σεₜ}` (`e = μ_z + σεₜ`), each equilibrium condition is equivalent to its
  detrended form displayed on p. 501: the Euler equation (`rx_detrend_euler`, on the event
  tree), labour supply (`rx_detrend_labour`), the resource constraint (`rx_detrend_resource`),
  output (`rx_detrend_output`), capital accumulation (`rx_detrend_capital`), the rental rate
  (`rx_detrend_rental`) and the wage (`rx_detrend_wage`). The key scaling identity is
  `zₜ^{1/(1−α)} = z_{t−1}^{1/(1−α)}e^{e/(1−α)}` (`rx_trend_scale`).
* Transforming back (p. 502): `ln xₜ = ln x̃ₜ + ln zₜ/(1 − α)`, and
  `ln xₜ − ln x̃_ss = (ln x̃ₜ − ln x̃_ss) + ln zₜ/(1 − α)` (`rx_detrend_back`).
* The steady state of the detrended system (`εₜ = 0`, `G = e^{μ_z/(1−α)}`,
  `rx_trend_exp_G`): the rental rate is `R = G/β − 1 + δ`, the capital–labour ratio solves
  `αG^{1−α}k^{α−1} = R`, `I/K = 1 − (1 − δ)/G`, and hours are `N = w/(w + χc)`; the steady
  state is unique (`rx_trend_steady_unique`) and exists, with `0 < N < 1` and positive
  consumption, when `R > 0` and `β ≤ 1` (`rx_trend_steady_exists`).
* Other sources of shocks (pp. 503–505): with investment-specific technology
  `K_{t+1} = (1 − δ)Kₜ + vₜIₜ`, `Qₜ = 1/vₜ` and `ΛₜQₜ = βEₜΛ_{t+1}[R_{k,t+1} + (1 − δ)Q_{t+1}]`
  (`rx_ist_foc`, an instance of `rx_dec1_euler` with `Φ(I, K) = vI`, `G(X, K) = X/v`); the
  capital price falls when `v` rises (`rx_ist_price`). With lump-sum government spending the
  steady-state capital–labour ratio does not depend on `Ḡ` (`rx_gov_kn`).
* Not formalised (computational/numerical): the calibration and the Dynare impulse responses
  (Figures 14.10–14.13) and the qualitative statements read off them.
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- Miao, p. 501: the random walk with drift `ln zₜ = μ_z + ln z_{t−1} + σεₜ`, `ln z_{−1} = 0`,
gives `ln zₜ = (t + 1)μ_z + σΣ_{j≤t} εⱼ`. -/
theorem rx_lnz_walk {μ σ : ℝ} {lz ε : ℕ → ℝ} (h0 : lz 0 = μ + 0 + σ * ε 0)
    (h : ∀ t, lz (t + 1) = μ + lz t + σ * ε (t + 1)) (t : ℕ) :
    lz t = (t + 1) * μ + σ * ∑ j ∈ Finset.range (t + 1), ε j := by
  induction t with
  | zero => simp [h0]
  | succ n ih =>
    rw [h n, ih, Finset.sum_range_succ _ (n + 1)]
    push_cast
    ring

/-- The scaling identity: if `zₜ = z_{t−1}e^{e}` with `z_{t−1} > 0`, then
`zₜ^{1/(1−α)} = z_{t−1}^{1/(1−α)}e^{e/(1−α)}`. -/
theorem rx_trend_scale {α zp e : ℝ} (hzp : 0 < zp) :
    (zp * Real.exp e) ^ (1 / (1 - α)) = zp ^ (1 / (1 - α)) * Real.exp (e / (1 - α)) := by
  rw [Real.mul_rpow hzp.le (Real.exp_pos e).le, ← Real.exp_mul]
  ring_nf

/-- Miao, p. 501, the detrended output equation. With `Ỹ = Y/zₜ^{1/(1−α)}`,
`K̃ = K/z_{t−1}^{1/(1−α)}` and `zₜ = z_{t−1}e^{e}`:
`Y = zₜKₜ^α Nₜ^{1−α}` iff `Ỹ = e^{αe/(α−1)}K̃^α Nₜ^{1−α}`. -/
theorem rx_detrend_output {α zp e Y K N : ℝ} (hα : α ≠ 1) (hzp : 0 < zp) (hK : 0 < K) :
    Y = zp * Real.exp e * K ^ α * N ^ (1 - α) ↔
      Y / (zp * Real.exp e) ^ (1 / (1 - α)) =
        Real.exp (α / (α - 1) * e) * (K / zp ^ (1 / (1 - α))) ^ α * N ^ (1 - α) := by
  have h1 : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hA : 0 < zp ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzp _
  have key : Real.exp (α / (α - 1) * e) * (K / zp ^ (1 / (1 - α))) ^ α *
      (zp * Real.exp e) ^ (1 / (1 - α)) = zp * Real.exp e * K ^ α := by
    rw [Real.rpow_def_of_pos (div_pos hK hA), Real.rpow_def_of_pos (mul_pos hzp (Real.exp_pos e)),
      Real.rpow_def_of_pos hK, Real.log_div hK.ne' hA.ne', Real.log_rpow hzp,
      Real.log_mul hzp.ne' (Real.exp_pos e).ne', Real.log_exp]
    conv_rhs => rw [← Real.exp_log hzp]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have : α - 1 ≠ 0 := sub_ne_zero.2 hα
    field_simp
    ring
  have hz : 0 < (zp * Real.exp e) ^ (1 / (1 - α)) :=
    Real.rpow_pos_of_pos (mul_pos hzp (Real.exp_pos e)) _
  rw [div_eq_iff hz.ne', ← key]
  constructor <;> intro h <;> rw [h] <;> ring

/-- Miao, p. 501, detrended capital accumulation. With `K̃_{t+1} = K_{t+1}/zₜ^{1/(1−α)}`,
`K̃ₜ = Kₜ/z_{t−1}^{1/(1−α)}`, `Ĩ = I/zₜ^{1/(1−α)}`, `zₜ = z_{t−1}e^{e}`:
`K_{t+1} = (1 − δ)Kₜ + Iₜ` iff `K̃_{t+1} = e^{e/(α−1)}(1 − δ)K̃ₜ + Ĩₜ`. -/
theorem rx_detrend_capital {α δ zp e K' K I : ℝ} (hα : α ≠ 1) (hzp : 0 < zp) :
    K' = (1 - δ) * K + I ↔
      K' / (zp * Real.exp e) ^ (1 / (1 - α)) =
        Real.exp (e / (α - 1)) * (1 - δ) * (K / zp ^ (1 / (1 - α))) +
          I / (zp * Real.exp e) ^ (1 / (1 - α)) := by
  rw [rx_trend_scale hzp]
  have hA : 0 < zp ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzp _
  have hB := Real.exp_pos (e / (1 - α))
  have hBB : Real.exp (e / (α - 1)) * Real.exp (e / (1 - α)) = 1 := by
    have : α - 1 ≠ 0 := sub_ne_zero.2 hα
    have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
    rw [← Real.exp_add, show e / (α - 1) + e / (1 - α) = 0 by field_simp; ring, Real.exp_zero]
  have e1 : Real.exp (e / (α - 1)) * (1 - δ) * (K / zp ^ (1 / (1 - α))) =
      (1 - δ) * K / (zp ^ (1 / (1 - α)) * Real.exp (e / (1 - α))) := by
    field_simp
    linear_combination (1 - δ) * K * hBB
  rw [e1, ← add_div, div_left_inj' (mul_pos hA hB).ne']

/-- Miao, p. 501, the detrended rental rate: `R_k = αY/K` iff
`R_k = (αỸ/K̃)e^{e/(1−α)}`. -/
theorem rx_detrend_rental {α zp e R Y K : ℝ} (hzp : 0 < zp) :
    R = α * Y / K ↔
      R = α * (Y / (zp * Real.exp e) ^ (1 / (1 - α))) / (K / zp ^ (1 / (1 - α))) *
        Real.exp (e / (1 - α)) := by
  rw [rx_trend_scale hzp]
  have hA : 0 < zp ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzp _
  have hB := Real.exp_pos (e / (1 - α))
  have : α * (Y / (zp ^ (1 / (1 - α)) * Real.exp (e / (1 - α)))) / (K / zp ^ (1 / (1 - α))) *
      Real.exp (e / (1 - α)) = α * Y / K := by
    rcases eq_or_ne K 0 with hK | hK
    · simp [hK]
    · field_simp
  rw [this]

/-- Miao, p. 501, detrended labour supply: `χCₜ/(1 − Nₜ) = wₜ` iff `χC̃ₜ/(1 − Nₜ) = w̃ₜ`. -/
theorem rx_detrend_labour {χ C N w a : ℝ} (ha : 0 < a) :
    χ * C / (1 - N) = w ↔ χ * (C / a) / (1 - N) = w / a := by
  rw [show χ * (C / a) / (1 - N) = χ * C / (1 - N) / a by ring, div_left_inj' ha.ne']

/-- Miao, p. 501, the detrended resource constraint: `C + I = Y` iff `C̃ + Ĩ = Ỹ`. -/
theorem rx_detrend_resource {C I Y a : ℝ} (ha : 0 < a) : C + I = Y ↔ C / a + I / a = Y / a := by
  rw [← add_div, div_left_inj' ha.ne']

/-- Miao, p. 501, the detrended wage: if `w = (1 − α)Y/N` (the firm's condition) and
`Y = zₜKₜ^α Nₜ^{1−α}`, then `w̃ = (1 − α)e^{αe/(α−1)}K̃^α N^{−α}`. -/
theorem rx_detrend_wage {α zp e Y K N w : ℝ} (hα : α ≠ 1) (hzp : 0 < zp) (hK : 0 < K)
    (hN : 0 < N) (hw : w = (1 - α) * Y / N) (hY : Y = zp * Real.exp e * K ^ α * N ^ (1 - α)) :
    w / (zp * Real.exp e) ^ (1 / (1 - α)) =
      (1 - α) * Real.exp (α / (α - 1) * e) * (K / zp ^ (1 / (1 - α))) ^ α * N ^ (-α) := by
  have hYt := (rx_detrend_output hα hzp hK).1 hY
  rw [hw, show (1 - α) * Y / N / (zp * Real.exp e) ^ (1 / (1 - α)) =
    (1 - α) * (Y / (zp * Real.exp e) ^ (1 / (1 - α))) / N by ring, hYt,
    show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hN.ne']
  field_simp

/-- Miao, p. 501, the detrended Euler equation, on the event tree. At the node `h` with TFP
`zₜ > 0`, successors with `z_{t+1}(s) = zₜe^{e(s)}`: `1/Cₜ = βEₜ[(R_{k,t+1} + 1 − δ)/C_{t+1}]`
iff `1/C̃ₜ = βEₜ[e^{e_{t+1}/(α−1)}(R_{k,t+1} + 1 − δ)/C̃_{t+1}]`, where
`C̃ₜ = Cₜ/zₜ^{1/(1−α)}`, `C̃_{t+1}(s) = C_{t+1}(s)/z_{t+1}(s)^{1/(1−α)}`. -/
theorem rx_detrend_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {α β δ zt Ct : ℝ} {C1 R1 e1 : S → ℝ} (hα : α ≠ 1) (hzt : 0 < zt) :
    1 / Ct = β * rx_Es T h (fun s => 1 / C1 s * (R1 s + 1 - δ)) ↔
      1 / (Ct / zt ^ (1 / (1 - α))) = β * rx_Es T h (fun s =>
        1 / (C1 s / (zt * Real.exp (e1 s)) ^ (1 / (1 - α))) * Real.exp (e1 s / (α - 1)) *
          (R1 s + 1 - δ)) := by
  have hA : 0 < zt ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzt _
  have hs : ∀ s, 1 / (C1 s / (zt * Real.exp (e1 s)) ^ (1 / (1 - α))) *
      Real.exp (e1 s / (α - 1)) * (R1 s + 1 - δ) =
        zt ^ (1 / (1 - α)) * (1 / C1 s * (R1 s + 1 - δ)) := by
    intro s
    rw [rx_trend_scale hzt, one_div_div]
    have hBB : Real.exp (e1 s / (1 - α)) * Real.exp (e1 s / (α - 1)) = 1 := by
      have : α - 1 ≠ 0 := sub_ne_zero.2 hα
      have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
      rw [← Real.exp_add, show e1 s / (1 - α) + e1 s / (α - 1) = 0 by field_simp; ring,
        Real.exp_zero]
    rw [div_eq_mul_one_div (zt ^ (1 / (1 - α)) * _)]
    linear_combination zt ^ (1 / (1 - α)) * (1 / C1 s) * (R1 s + 1 - δ) * hBB
  simp only [hs]
  rw [rx_Es_mul_left, one_div_div, div_eq_mul_one_div (zt ^ _), mul_left_comm β]
  constructor
  · intro h0
    rw [h0]
  · intro h0
    exact mul_left_cancel₀ hA.ne' h0

/-- Miao, p. 502, transforming back: `ln xₜ = ln x̃ₜ + ln zₜ/(1 − α)` for
`x̃ₜ = xₜ/zₜ^{1/(1−α)}`, and the impulse responses
`ln xₜ − ln x̃_ss = (ln x̃ₜ − ln x̃_ss) + ln zₜ/(1 − α)`. -/
theorem rx_detrend_back {α x z xss : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Real.log x = Real.log (x / z ^ (1 / (1 - α))) + Real.log z / (1 - α) ∧
      Real.log x - Real.log xss = (Real.log (x / z ^ (1 / (1 - α))) - Real.log xss) +
        Real.log z / (1 - α) := by
  have h1 : Real.log x = Real.log (x / z ^ (1 / (1 - α))) + Real.log z / (1 - α) := by
    rw [Real.log_div hx.ne' (Real.rpow_pos_of_pos hz _).ne', Real.log_rpow hz]
    ring
  exact ⟨h1, by rw [h1]; ring⟩

/-- Miao, p. 501: at `εₜ = 0` the exponential factors of the detrended system are powers of
the steady-state gross growth rate `G = e^{μ_z/(1−α)}` of the trend:
`e^{αμ_z/(α−1)} = G^{−α}`, `e^{μ_z/(α−1)} = G⁻¹`. -/
theorem rx_trend_exp_G {α μ : ℝ} (hα : α ≠ 1) :
    Real.exp (α / (α - 1) * μ) = Real.exp (μ / (1 - α)) ^ (-α) ∧
      Real.exp (μ / (α - 1)) = (Real.exp (μ / (1 - α)))⁻¹ := by
  have : α - 1 ≠ 0 := sub_ne_zero.2 hα
  have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_mul]
    congr 1
    field_simp
    ring
  · rw [← Real.exp_neg]
    congr 1
    field_simp
    ring

/-- The steady state of the detrended system of p. 501 at `εₜ = 0`, written with
`G = e^{μ_z/(1−α)}` (`rx_trend_exp_G`): Euler equation, labour supply, resource constraint,
output, capital accumulation, rental rate and wage. -/
def rx_trendSS (α β δ χ G C I Y K N Rk w : ℝ) : Prop :=
  1 = β / G * (Rk + 1 - δ) ∧ χ * C / (1 - N) = w ∧ C + I = Y ∧
    Y = G ^ (-α) * K ^ α * N ^ (1 - α) ∧ K = G⁻¹ * (1 - δ) * K + I ∧ Rk = α * Y / K * G ∧
    w = (1 - α) * G ^ (-α) * K ^ α * N ^ (-α)

/-- The steady-state rental rate `R = G/β − 1 + δ`. -/
noncomputable def rx_trR (β δ G : ℝ) : ℝ := G / β - 1 + δ

/-- The steady-state capital–labour ratio `k = (R/(αG^{1−α}))^{1/(α−1)}`. -/
noncomputable def rx_trk (α β δ G : ℝ) : ℝ := (rx_trR β δ G / (α * G ^ (1 - α))) ^ (α - 1)⁻¹

/-- Output per hour `y = G^{−α}k^α`. -/
noncomputable def rx_try (α β δ G : ℝ) : ℝ := G ^ (-α) * rx_trk α β δ G ^ α

/-- Investment per hour `i = (1 − (1 − δ)/G)k`. -/
noncomputable def rx_tri (α β δ G : ℝ) : ℝ := (1 - (1 - δ) / G) * rx_trk α β δ G

/-- Consumption per hour `c = y − i`. -/
noncomputable def rx_trc (α β δ G : ℝ) : ℝ := rx_try α β δ G - rx_tri α β δ G

/-- Hours `N = w/(w + χc)` with `w = (1 − α)y`. -/
noncomputable def rx_trN (α β δ χ G : ℝ) : ℝ :=
  (1 - α) * rx_try α β δ G / ((1 - α) * rx_try α β δ G + χ * rx_trc α β δ G)

theorem rx_rpow_kN {α k N : ℝ} (hk : 0 < k) (hN : 0 < N) :
    (k * N) ^ α * N ^ (1 - α) = k ^ α * N ∧ (k * N) ^ α * N ^ (-α) = k ^ α := by
  rw [Real.mul_rpow hk.le hN.le]
  constructor
  · rw [mul_assoc, ← Real.rpow_add hN, show α + (1 - α) = 1 by ring, Real.rpow_one]
  · rw [mul_assoc, ← Real.rpow_add hN, show α + -α = 0 by ring, Real.rpow_zero, mul_one]

/-- `k^{α−1} = R/(αG^{1−α})` for the closed-form `k`, when `R > 0`. -/
theorem rx_trk_pow {α β δ G : ℝ} (hα : α ≠ 1) (hα0 : 0 < α) (hG : 0 < G)
    (hR : 0 < rx_trR β δ G) :
    0 < rx_trk α β δ G ∧ rx_trk α β δ G ^ (α - 1) = rx_trR β δ G / (α * G ^ (1 - α)) := by
  have hc : 0 < rx_trR β δ G / (α * G ^ (1 - α)) :=
    div_pos hR (mul_pos hα0 (Real.rpow_pos_of_pos hG _))
  exact ⟨Real.rpow_pos_of_pos hc _, Real.rpow_inv_rpow hc.le (sub_ne_zero.2 hα)⟩

/-- Miao, p. 501: uniqueness of the steady state of the detrended system. Any steady state
with `K > 0`, `0 < N < 1` has the rental rate `R = G/β − 1 + δ`, the capital–labour ratio
`K/N = k`, investment `I = (1 − (1 − δ)/G)K` and hours `N = w/(w + χc)` of `rx_trN`. -/
theorem rx_trend_steady_unique {α β δ χ G C I Y K N Rk w : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hG : 0 < G) (hK : 0 < K) (hN : 0 < N) (hN1 : N < 1)
    (hss : rx_trendSS α β δ χ G C I Y K N Rk w) :
    Rk = rx_trR β δ G ∧ K / N = rx_trk α β δ G ∧ I = (1 - (1 - δ) / G) * K ∧
      N = rx_trN α β δ χ G := by
  obtain ⟨hE, hL, hRes, hY, hKa, hRk, hw⟩ := hss
  have hα : α ≠ 1 := ne_of_lt hα1
  have hR : Rk = rx_trR β δ G := by
    unfold rx_trR
    field_simp at hE ⊢
    linarith
  have hk : 0 < K / N := div_pos hK hN
  have hKkN : K = K / N * N := by field_simp
  obtain ⟨e1, e2⟩ := rx_rpow_kN (α := α) hk hN
  rw [← hKkN] at e1 e2
  have hYk : Y = N * (G ^ (-α) * (K / N) ^ α) := by rw [hY, mul_assoc, e1]; ring
  have hwk : w = (1 - α) * (G ^ (-α) * (K / N) ^ α) := by rw [hw, mul_assoc, e2]; ring
  have hpow : (K / N) ^ (α - 1) = rx_trR β δ G / (α * G ^ (1 - α)) := by
    rw [← hR, hRk, hYk, Real.rpow_sub_one hk.ne', show (1 : ℝ) - α = -α + 1 by ring,
      Real.rpow_add_one hG.ne']
    have : 0 < G ^ (-α) := Real.rpow_pos_of_pos hG _
    field_simp
  have hkeq : K / N = rx_trk α β δ G := by
    unfold rx_trk
    rw [← hpow, Real.rpow_rpow_inv hk.le (sub_ne_zero.2 hα)]
  have hI : I = (1 - (1 - δ) / G) * K := by
    field_simp
    field_simp at hKa
    linarith
  refine ⟨hR, hkeq, hI, ?_⟩
  have hC : C = N * rx_trc α β δ G := by
    have : C = Y - I := by linarith
    have hKN : K = N * rx_trk α β δ G := by rw [← hkeq]; field_simp
    rw [this, hYk, hI, hkeq, hKN]
    unfold rx_trc rx_try rx_tri
    ring
  have hwe : w = (1 - α) * rx_try α β δ G := by rw [hwk, hkeq]; rfl
  have hlab : χ * C = w * (1 - N) := by
    have : 1 - N ≠ 0 := by linarith
    field_simp at hL
    linarith
  have hy : 0 < rx_try α β δ G := by
    unfold rx_try
    rw [← hkeq]
    exact mul_pos (Real.rpow_pos_of_pos hG _) (Real.rpow_pos_of_pos hk _)
  have hsum : N * ((1 - α) * rx_try α β δ G + χ * rx_trc α β δ G) =
      (1 - α) * rx_try α β δ G := by
    rw [hC, hwe] at hlab
    linarith
  have hpos : 0 < (1 - α) * rx_try α β δ G := mul_pos (by linarith) hy
  have hden : (1 - α) * rx_try α β δ G + χ * rx_trc α β δ G ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsum
    linarith
  unfold rx_trN
  field_simp
  linarith

/-- Miao, p. 501: existence of the steady state of the detrended system. If `0 < α < 1`,
`0 < β ≤ 1`, `χ > 0`, `G > 0` and `R = G/β − 1 + δ > 0`, then consumption per hour
`c = y − i` is positive, hours `N = w/(w + χc)` lie in `(0, 1)`, and
`(C, I, Y, K) = (cN, iN, yN, kN)`, `R_k = R`, `w = (1 − α)y` is a steady state. -/
theorem rx_trend_steady_exists {α β δ χ G : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hχ : 0 < χ) (hG : 0 < G) (hR : 0 < rx_trR β δ G) :
    0 < rx_trc α β δ G ∧ 0 < rx_trN α β δ χ G ∧ rx_trN α β δ χ G < 1 ∧
      rx_trendSS α β δ χ G (rx_trc α β δ G * rx_trN α β δ χ G)
        (rx_tri α β δ G * rx_trN α β δ χ G) (rx_try α β δ G * rx_trN α β δ χ G)
        (rx_trk α β δ G * rx_trN α β δ χ G) (rx_trN α β δ χ G) (rx_trR β δ G)
        ((1 - α) * rx_try α β δ G) := by
  have hα : α ≠ 1 := ne_of_lt hα1
  obtain ⟨hk, hkp⟩ := rx_trk_pow hα hα0 hG hR
  have hGa : 0 < G ^ (-α) := Real.rpow_pos_of_pos hG _
  have hy : 0 < rx_try α β δ G := mul_pos hGa (Real.rpow_pos_of_pos hk _)
  have hyk : rx_try α β δ G = rx_trR β δ G / (α * G) * rx_trk α β δ G := by
    unfold rx_try
    have e : rx_trk α β δ G ^ α = rx_trk α β δ G ^ (α - 1) * rx_trk α β δ G := by
      rw [Real.rpow_sub_one hk.ne']
      field_simp
    rw [e, hkp, show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hG.ne']
    field_simp
  have hRD : α * (G - 1 + δ) < rx_trR β δ G := by
    have hGb : G ≤ G / β := by rw [le_div_iff₀ hβ]; nlinarith
    unfold rx_trR at hR ⊢
    rcases le_or_gt (G - 1 + δ) 0 with hD | hD
    · nlinarith
    · nlinarith
  have hc : 0 < rx_trc α β δ G := by
    have e : rx_trc α β δ G = rx_trk α β δ G * ((rx_trR β δ G - α * (G - 1 + δ)) / (α * G)) := by
      unfold rx_trc rx_tri
      rw [hyk]
      field_simp
      ring
    rw [e]
    exact mul_pos hk (div_pos (by linarith) (mul_pos hα0 hG))
  have hw : 0 < (1 - α) * rx_try α β δ G := mul_pos (by linarith) hy
  have hden : 0 < (1 - α) * rx_try α β δ G + χ * rx_trc α β δ G := by positivity
  have hN : 0 < rx_trN α β δ χ G := div_pos hw hden
  have hN1 : rx_trN α β δ χ G < 1 := by
    unfold rx_trN
    rw [div_lt_one hden]
    nlinarith [mul_pos hχ hc]
  have hNd : rx_trN α β δ χ G * ((1 - α) * rx_try α β δ G + χ * rx_trc α β δ G) =
      (1 - α) * rx_try α β δ G := by
    unfold rx_trN
    field_simp
  obtain ⟨e1, e2⟩ := rx_rpow_kN (α := α) hk hN
  refine ⟨hc, hN, hN1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rx_trR
    field_simp
    ring
  · have : 1 - rx_trN α β δ χ G ≠ 0 := by linarith
    field_simp
    linarith
  · unfold rx_trc
    ring
  · rw [mul_assoc, e1]
    unfold rx_try
    ring
  · unfold rx_tri
    field_simp
    ring
  · rw [hyk]
    field_simp
  · rw [mul_assoc, e2]
    unfold rx_try
    ring

/-- Investment-specific technology `Φ(I, K) = vI` (Miao, p. 503) has partial derivatives
`Φ_I = v`, `Φ_K = 0`; its inverse `G(X, K) = X/v` (for `v ≠ 0`) has `G_X = 1/v`, `G_K = 0`.
(A concrete instance of the hypotheses of `rx_uzawa_euler` and `rx_inverse_partials`.) -/
theorem rx_linear_partials {v : ℝ} (hv : v ≠ 0) (p : ℝ × ℝ) :
    rx_HasPartials (fun q : ℝ × ℝ => v * q.1) v 0 p ∧
      rx_HasPartials (fun q : ℝ × ℝ => q.1 / v) (1 / v) 0 p ∧
      ∀ X K : ℝ, (fun q : ℝ × ℝ => v * q.1) ((fun q : ℝ × ℝ => q.1 / v) (X, K), K) = X := by
  refine ⟨?_, ?_, fun X K => by simp only; field_simp⟩
  · unfold rx_HasPartials
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul v
    refine this.congr_fderiv ?_
    ext <;> simp
  · unfold rx_HasPartials
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul_const (1 / v)
    refine (this.congr_fderiv ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun q => div_eq_mul_one_div q.1 v)
    ext <;> simp

/-- Miao, p. 503, investment-specific shocks, decentralisation 1: with
`K_{t+1} = (1 − δ)Kₜ + vₜIₜ` the `Iₜ` condition is `Qₜvₜ = 1`, i.e. `Qₜ = 1/vₜ`
(`rx_invest_foc`), and perturbing `K_{t+1} = k` (financed by `Iₜ = (k − (1 − δ)Kₜ)/vₜ`, with
`I_{t+1}(s) = (K_{t+2}(s) − (1 − δ)k)/v(s)`) gives
`ΛₜQₜ = βEₜΛ_{t+1}[R_{k,t+1} + (1 − δ)Q_{t+1}]`. -/
theorem rx_ist_foc {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ β Kt K1 yt vt l0 : ℝ} {R wN K2 v l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (yt - (K1 - (1 - δ) * Kt) / vt))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (R s * K1 + wN s - (K2 s - (1 - δ) * K1) / v s))
    (hmax : IsLocalMax (fun k => U0 (yt - (k - (1 - δ) * Kt) / vt) + β * ∑ s,
      T.cp h s * U1 s (R s * k + wN s - (K2 s - (1 - δ) * k) / v s)) K1) :
    l0 * (1 / vt) = β * rx_Es T h (fun s => l1 s * (R s + (1 - δ) * (1 / v s))) := by
  have hc0 : HasDerivAt (fun k => yt - (k - (1 - δ) * Kt) / vt) (0 - (1 - 0) / vt) K1 :=
    (hasDerivAt_const K1 yt).sub (((hasDerivAt_id' K1).sub (hasDerivAt_const K1 _)).div_const vt)
  have hc1 : ∀ s, HasDerivAt (fun k => R s * k + wN s - (K2 s - (1 - δ) * k) / v s)
      (R s * 1 + 0 - (0 - (1 - δ) * 1) / v s) K1 := fun s =>
    ((((hasDerivAt_id' K1).const_mul (R s)).add (hasDerivAt_const K1 _)).sub
      (((hasDerivAt_const K1 _).sub ((hasDerivAt_id' K1).const_mul _)).div_const (v s)))
  have e := rx_node_foc (c0 := fun k => yt - (k - (1 - δ) * Kt) / vt)
    (c1 := fun s k => R s * k + wN s - (K2 s - (1 - δ) * k) / v s) hU0 hc0 hU1 hc1 hmax
  have hs : ∀ s, T.cp h s * (l1 s * (R s * 1 + 0 - (0 - (1 - δ) * 1) / v s)) =
      T.cp h s * (l1 s * (R s + (1 - δ) * (1 / v s))) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hs s] at e
  simp only [rx_Es]
  linarith

/-- Miao, p. 503: "the capital price is equal to `1/vₜ`"; a positive investment-specific
technology shock lowers it: `0 < v < v′ ⇒ 1/v′ < 1/v`. -/
theorem rx_ist_price {v v' : ℝ} (hv : 0 < v) (hvv : v < v') : 1 / v' < 1 / v :=
  one_div_lt_one_div_of_lt hv hvv

/-- Miao, p. 505, government spending financed by lump-sum taxes: the resource constraint
`C + I + G = zK^α N^{1−α}` does not enter the steady-state Euler equation
`1 = β(R_k + 1 − δ)` or the rental rate `R_k = α(K/N)^{α−1}` (with `z = 1`), so the
steady-state capital–labour ratio `((1/β − 1 + δ)/α)^{1/(α−1)}` does not depend on `Ḡ`. -/
theorem rx_gov_kn {α β δ Rk k : ℝ} (hα : α ≠ 1) (hβ : 0 < β) (hα0 : 0 < α) (hk : 0 < k)
    (hE : 1 = β * (Rk + 1 - δ)) (hR : Rk = α * k ^ (α - 1)) :
    k = ((1 / β - 1 + δ) / α) ^ (α - 1)⁻¹ := by
  have : (1 / β - 1 + δ) / α = k ^ (α - 1) := by
    rw [div_eq_iff hα0.ne', mul_comm, ← hR]
    field_simp
    linarith
  rw [this, Real.rpow_rpow_inv hk.le (sub_ne_zero.2 hα)]

end Miao.NeoclassicalGrowth
