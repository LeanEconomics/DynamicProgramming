/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import OperatorsFixedPoints.NonnegativeMatrices
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The carbon cycle

AKMM, §25.3.2 (pp. 755–756) and the carbon accounting of §25.4.2 (p. 770).

* (25.6)–(25.8), corrected. As printed the outflows `φ₁₂S` from the atmosphere and `φ₃₂Sᴸ` from
  the deep ocean carry a plus sign, although (25.7) adds them to the upper reservoir, so total
  carbon grows by `2φ₁₂S + 2φ₃₂Sᴸ + E` (`eq_25_6_printed_total`, `eq_25_6_printed_false`).
  With the signs corrected, total carbon grows by exactly the emissions (`eq_25_6_total`).
* Without emissions the corrected map is a mass-preserving linear map: the transpose of its
  matrix is a Markov matrix in the sense of Sargent–Stachurski (`carbon_isMarkov`), so an
  invariant distribution of carbon exists (`carbon_exists_invariant`, from
  `IsMarkov.exists_stationary`); for positive flows it is unique for each total, with
  `φ₁₂S = φ₂₁Sᵁ` and `φ₂₃Sᵁ = φ₃₂Sᴸ` (`carbon_invariant_iff`, `carbon_invariant_unique`).
* Linearity ("the key feature again is linearity", p. 756): the stocks are the emission-free
  path plus a time-invariant kernel applied to past emissions (`carbon_superposition`), so the
  three-reservoir model is of the form (25.9).
* (25.9)–(25.10): excess carbon `S_t − S₀ = Σ_v (1 − d_{t−v})E_v` (`excessCarbon`), the
  book's lag form (`eq_25_9`), the response of `S_{t+j}` to an emission at `t` is `1 − d_j`
  (`excessCarbon_pulse`); the GHKT kernel (25.10) lies in `[0, 1]`, falls with the lag
  (`ghktKernel_mem_Icc`, `ghktKernel_antitone`) and tends to `φ_L`, the share that stays
  forever (`eq_25_10_tendsto`); the within-period loss is `(1 − φ_L)(1 − φ₀)`, not `1 − φ₀`
  as the text says (`eq_25_10_within_period`); the discounted kernel sum has the closed form
  `φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ))` (`ghktKernel_hasSum`).
-/

namespace AKMM.Sustainability

open Real Filter Topology

/-- The flow parameters `(φ₁₂, φ₂₁, φ₂₃, φ₃₂)` of the three-reservoir carbon cycle. -/
structure CarbonFlows where
  /-- atmosphere to upper ocean and biosphere -/
  f12 : ℝ
  /-- upper reservoir to atmosphere -/
  f21 : ℝ
  /-- upper reservoir to deep ocean -/
  f23 : ℝ
  /-- deep ocean to upper reservoir -/
  f32 : ℝ

/-- AKMM, (25.6)–(25.8), p. 755, with the outflow signs corrected: the emission-free part of
the carbon cycle as a linear map of `(S, Sᵁ, Sᴸ)`. -/
def carbonLin (p : CarbonFlows) : ℝ × ℝ × ℝ →ₗ[ℝ] ℝ × ℝ × ℝ where
  toFun x := (x.1 - p.f12 * x.1 + p.f21 * x.2.1,
    x.2.1 + p.f12 * x.1 - (p.f21 + p.f23) * x.2.1 + p.f32 * x.2.2,
    x.2.2 + p.f23 * x.2.1 - p.f32 * x.2.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Prod.smul_mk,
      Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

/-- AKMM, (25.6)–(25.8), p. 755, corrected: one period of the carbon cycle with emissions `E`,
which enter the atmosphere. -/
def carbonStep (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  carbonLin p x + E • ((1 : ℝ), (0 : ℝ), (0 : ℝ))

/-- AKMM, (25.6)–(25.8) as printed, p. 755: `S_t − S_{t−1} = φ₁₂S_{t−1} + φ₂₁Sᵁ_{t−1} + E_{t−1}`
and `Sᴸ_t − Sᴸ_{t−1} = φ₂₃Sᵁ_{t−1} + φ₃₂Sᴸ_{t−1}`. -/
def carbonStepPrinted (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.1 + p.f12 * x.1 + p.f21 * x.2.1 + E,
    x.2.1 + p.f12 * x.1 - (p.f21 + p.f23) * x.2.1 + p.f32 * x.2.2,
    x.2.2 + p.f23 * x.2.1 + p.f32 * x.2.2)

/-- Total carbon in the three reservoirs. -/
def carbonTotal (x : ℝ × ℝ × ℝ) : ℝ := x.1 + x.2.1 + x.2.2

/-- AKMM, (25.6)–(25.8), p. 755, corrected: the cycle only moves carbon between reservoirs, so
total carbon increases by exactly the emissions. -/
theorem eq_25_6_total (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) :
    carbonTotal (carbonStep p E x) = carbonTotal x + E := by
  simp [carbonStep, carbonLin, carbonTotal]
  ring

/-- AKMM, (25.6)–(25.8) as printed, p. 755: total carbon grows by `2φ₁₂S + 2φ₃₂Sᴸ + E`. -/
theorem eq_25_6_printed_total (p : CarbonFlows) (E : ℝ) (x : ℝ × ℝ × ℝ) :
    carbonTotal (carbonStepPrinted p E x) = carbonTotal x + 2 * p.f12 * x.1 +
      2 * p.f32 * x.2.2 + E := by
  simp [carbonStepPrinted, carbonTotal]
  ring

/-- AKMM, p. 755: the printed system does not conserve carbon: with Folini et al.'s flows and
one unit of carbon in the atmosphere and no emissions, total carbon rises. -/
theorem eq_25_6_printed_false :
    carbonTotal (carbonStepPrinted ⟨0.053, 0.0536, 0.0042, 0.001422⟩ 0 (1, 0, 0)) ≠
      carbonTotal ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
  rw [eq_25_6_printed_total]
  norm_num

/-- The matrix of `carbonLin` acting on `(S, Sᵁ, Sᴸ)` as a column vector. -/
def carbonMatrix (p : CarbonFlows) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - p.f12, p.f21, 0; p.f12, 1 - p.f21 - p.f23, p.f32; 0, p.f23, 1 - p.f32]

/-- AKMM, p. 755: with flows that are shares (`0 ≤ φ₁₂ ≤ 1`, `φ₂₁, φ₂₃ ≥ 0`,
`φ₂₁ + φ₂₃ ≤ 1`, `0 ≤ φ₃₂ ≤ 1`) the carbon matrix is column-stochastic: its transpose is a
Markov matrix in the sense of Sargent–Stachurski (Vol. 1, p. 71). -/
theorem carbon_isMarkov {p : CarbonFlows} (h12 : 0 ≤ p.f12) (h12' : p.f12 ≤ 1)
    (h21 : 0 ≤ p.f21) (h23 : 0 ≤ p.f23) (h2 : p.f21 + p.f23 ≤ 1) (h32 : 0 ≤ p.f32)
    (h32' : p.f32 ≤ 1) :
    SargentStachurski.OperatorsFixedPoints.IsMarkov (carbonMatrix p).transpose where
  nonneg i j := by
    fin_cases i <;> fin_cases j <;> simp [carbonMatrix] <;> linarith
  rowsum i := by
    fin_cases i <;> (simp [carbonMatrix, Fin.sum_univ_three]; try ring)

/-- AKMM, p. 755: the matrix represents the corrected emission-free cycle. -/
theorem carbonMatrix_mulVec (p : CarbonFlows) (x : ℝ × ℝ × ℝ) :
    Matrix.mulVec (carbonMatrix p) ![x.1, x.2.1, x.2.2] =
      ![(carbonLin p x).1, (carbonLin p x).2.1, (carbonLin p x).2.2] := by
  ext i
  fin_cases i <;> (simp [carbonMatrix, carbonLin, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]; try ring)

/-- AKMM, p. 755: without emissions there is an invariant distribution of carbon across the
reservoirs (Perron–Frobenius, `IsMarkov.exists_stationary` of `OperatorsFixedPoints`). -/
theorem carbon_exists_invariant {p : CarbonFlows} (h12 : 0 ≤ p.f12) (h12' : p.f12 ≤ 1)
    (h21 : 0 ≤ p.f21) (h23 : 0 ≤ p.f23) (h2 : p.f21 + p.f23 ≤ 1) (h32 : 0 ≤ p.f32)
    (h32' : p.f32 ≤ 1) :
    ∃ x : ℝ × ℝ × ℝ, 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2 ∧ carbonTotal x = 1 ∧
      carbonStep p 0 x = x := by
  obtain ⟨ψ, hψ0, hψ1, hψ⟩ := (carbon_isMarkov h12 h12' h21 h23 h2 h32 h32').exists_stationary
  refine ⟨(ψ 0, ψ 1, ψ 2), hψ0 0, hψ0 1, hψ0 2, ?_, ?_⟩
  · simpa [carbonTotal, Fin.sum_univ_three] using hψ1
  · have h0 := congrFun hψ 0
    have h1 := congrFun hψ 1
    have h2' := congrFun hψ 2
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, carbonMatrix] at h0 h1 h2'
    simp only [carbonStep, carbonLin, LinearMap.coe_mk, AddHom.coe_mk, zero_smul, add_zero,
      Prod.mk.injEq]
    refine ⟨by linarith, by linarith, by linarith⟩

/-- AKMM, p. 755: without emissions, a distribution `(S, Sᵁ, Sᴸ)` is invariant iff the flows
balance pairwise: `φ₁₂S = φ₂₁Sᵁ` and `φ₂₃Sᵁ = φ₃₂Sᴸ`. -/
theorem carbon_invariant_iff (p : CarbonFlows) (x : ℝ × ℝ × ℝ) :
    carbonStep p 0 x = x ↔ p.f12 * x.1 = p.f21 * x.2.1 ∧ p.f23 * x.2.1 = p.f32 * x.2.2 := by
  simp only [carbonStep, carbonLin, LinearMap.coe_mk, AddHom.coe_mk, zero_smul, add_zero]
  obtain ⟨a, b, c⟩ := x
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, by linarith⟩

/-- AKMM, p. 755: with positive flows the invariant distribution of a given total is unique. -/
theorem carbon_invariant_unique {p : CarbonFlows} (h12 : 0 < p.f12) (h21 : 0 < p.f21)
    (h23 : 0 < p.f23) (h32 : 0 < p.f32) {x y : ℝ × ℝ × ℝ} (hx : carbonStep p 0 x = x)
    (hy : carbonStep p 0 y = y) (hxy : carbonTotal x = carbonTotal y) : x = y := by
  rw [carbon_invariant_iff] at hx hy
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  simp only [carbonTotal] at hx hy hxy
  -- express everything through the atmospheric stock
  have hb : b = p.f12 / p.f21 * a := by field_simp; linarith [hx.1]
  have hb' : b' = p.f12 / p.f21 * a' := by field_simp; linarith [hy.1]
  have hc : c = p.f23 / p.f32 * b := by field_simp; linarith [hx.2]
  have hc' : c' = p.f23 / p.f32 * b' := by field_simp; linarith [hy.2]
  have hk : 0 < 1 + p.f12 / p.f21 + p.f23 / p.f32 * (p.f12 / p.f21) := by positivity
  have haa : a = a' := by
    rw [hc, hb, hc', hb'] at hxy
    have : (1 + p.f12 / p.f21 + p.f23 / p.f32 * (p.f12 / p.f21)) * (a - a') = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  subst haa
  have hbb : b = b' := by rw [hb, hb']
  subst hbb
  have hcc : c = c' := by rw [hc, hc']
  rw [hcc]

/-- The carbon stocks under an emission path `E`, from initial stocks `x₀`. -/
def carbonPath (p : CarbonFlows) (E : ℕ → ℝ) (x₀ : ℝ × ℝ × ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => x₀
  | t + 1 => carbonStep p (E t) (carbonPath p E x₀ t)

/-- The unit-pulse emission path: one unit at date `0`. -/
def carbonPulse (t : ℕ) : ℝ := if t = 0 then 1 else 0

/-- The response of the stocks to a unit pulse, `j` periods after it is emitted. -/
def carbonResponse (p : CarbonFlows) (j : ℕ) : ℝ × ℝ × ℝ :=
  carbonPath p carbonPulse 0 (j + 1)

/-- AKMM, p. 756, "the key feature again is linearity": the stocks are the emission-free path
plus a time-invariant response kernel applied to past emissions,
`x_t = x_t⁰ + Σ_{v<t} E_v · r_{t−1−v}`. -/
theorem carbon_superposition (p : CarbonFlows) (E : ℕ → ℝ) (x₀ : ℝ × ℝ × ℝ) (t : ℕ) :
    carbonPath p E x₀ t = carbonPath p 0 x₀ t +
      ∑ v ∈ Finset.range t, E v • carbonResponse p (t - 1 - v) := by
  -- the response kernel itself evolves by the emission-free map
  have hresp : ∀ j, carbonResponse p (j + 1) = carbonLin p (carbonResponse p j) := by
    intro j
    simp [carbonResponse, carbonPath, carbonStep, carbonPulse]
  have hresp0 : carbonResponse p 0 = ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    simp [carbonResponse, carbonPath, carbonStep, carbonPulse]
  induction t with
  | zero => simp [carbonPath]
  | succ n ih =>
    rw [carbonPath, ih, carbonPath, Finset.sum_range_succ]
    simp only [carbonStep, map_add, map_sum, map_smul, Pi.zero_apply, zero_smul, add_zero]
    have hsum : ∑ v ∈ Finset.range n, E v • carbonLin p (carbonResponse p (n - 1 - v)) =
        ∑ v ∈ Finset.range n, E v • carbonResponse p (n + 1 - 1 - v) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv' : v < n := Finset.mem_range.mp hv
      have : n + 1 - 1 - v = n - 1 - v + 1 := by omega
      rw [this, hresp]
    rw [hsum, show n + 1 - 1 - n = 0 by omega, hresp0]
    abel

/-- AKMM, (25.10), p. 756: the GHKT kernel `1 − d_s = φ_L + (1 − φ_L)φ₀(1 − φ)^s`. -/
noncomputable def ghktKernel (φL φ0 φ : ℝ) (s : ℕ) : ℝ := φL + (1 - φL) * φ0 * (1 - φ) ^ s

/-- AKMM, p. 756: with `0 < φ < 2` (in particular a depreciation rate `φ ∈ (0, 1]`) the kernel
tends to `φ_L`: the share `φ_L` of an emission stays in the atmosphere forever. -/
theorem eq_25_10_tendsto {φL φ0 φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2) :
    Tendsto (ghktKernel φL φ0 φ) atTop (𝓝 φL) := by
  have hq : |1 - φ| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).const_mul ((1 - φL) * φ0)
  have h2 := this.const_add φL
  rw [mul_zero, add_zero] at h2
  exact h2

/-- AKMM, p. 756: with shares `φ_L, φ₀, φ ∈ [0, 1]` the kernel is a share. -/
theorem ghktKernel_mem_Icc {φL φ0 φ : ℝ} (hL : 0 ≤ φL) (hL1 : φL ≤ 1) (h0 : 0 ≤ φ0)
    (h01 : φ0 ≤ 1) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1) (s : ℕ) :
    ghktKernel φL φ0 φ s ∈ Set.Icc 0 1 := by
  have hp : 0 ≤ (1 - φ) ^ s := pow_nonneg (by linarith) s
  have hp1 : (1 - φ) ^ s ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hm : 0 ≤ (1 - φL) * φ0 := mul_nonneg (by linarith) h0
  constructor
  · unfold ghktKernel; positivity
  · unfold ghktKernel
    nlinarith [mul_le_mul_of_nonneg_left hp1 hm]

/-- AKMM, p. 756: the share remaining in the atmosphere falls with the lag. -/
theorem ghktKernel_antitone {φL φ0 φ : ℝ} (hL1 : φL ≤ 1) (h0 : 0 ≤ φ0) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) : Antitone (ghktKernel φL φ0 φ) := by
  intro s s' hss
  have hm : 0 ≤ (1 - φL) * φ0 := mul_nonneg (by linarith) h0
  unfold ghktKernel
  have := pow_le_pow_of_le_one (by linarith : 0 ≤ 1 - φ) (by linarith) hss
  nlinarith [mul_le_mul_of_nonneg_left this hm]

/-- AKMM, p. 756: the text says "the share that leaves the atmosphere within a period [is]
`1 − φ₀`"; by (25.10) the within-period loss is `d₀ = (1 − φ_L)(1 − φ₀)`: `1 − φ₀` is the share
of the non-permanent part `1 − φ_L` that leaves. The three shares add up to one. -/
theorem eq_25_10_within_period (φL φ0 φ : ℝ) :
    1 - ghktKernel φL φ0 φ 0 = (1 - φL) * (1 - φ0) ∧
      φL + (1 - φL) * (1 - φ0) + (1 - φL) * φ0 = 1 := by
  exact ⟨by simp only [ghktKernel, pow_zero]; ring, by ring⟩

/-- AKMM, p. 756: the within-period loss is `1 − φ₀` only when `φ_L = 0`; with the GHKT
calibration `φ_L = 0.2`, `φ₀ = 0.393` it is `0.4856`, not `0.607`. -/
theorem eq_25_10_within_period_printed_false :
    1 - ghktKernel 0.2 0.393 0.0228 0 ≠ 1 - 0.393 := by
  rw [(eq_25_10_within_period _ _ _).1]
  norm_num

/-- AKMM, (25.32) via (25.10): the discounted kernel sum has the closed form
`Σ_j β^j(1 − d_j) = φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ))`. -/
theorem ghktKernel_hasSum {φL φ0 φ β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) :
    HasSum (fun j => β ^ j * ghktKernel φL φ0 φ j)
      (φL / (1 - β) + (1 - φL) * φ0 / (1 - β * (1 - φ))) := by
  have hq0 : 0 ≤ β * (1 - φ) := mul_nonneg hβ0 (by linarith)
  have hq1 : β * (1 - φ) < 1 := by nlinarith
  have h1 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left φL
  have h2 := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - φL) * φ0)
  convert h1.add h2 using 1
  · funext j; simp only [ghktKernel, mul_pow]; ring
  · field_simp

/-- AKMM, (25.9), p. 756 and p. 770: excess atmospheric carbon at `t` from emissions `E_v` at
dates `v ≤ t`, `S_t − S₀ = Σ_{v ≤ t}(1 − d_{t−v})E_v` (the kernel `k = 1 − d`). -/
def excessCarbon (k E : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ v ∈ Finset.range (t + 1), k (t - v) * E v

/-- AKMM, (25.9), p. 756: in the book's lag form, `S_t − S₀ = Σ_{s ≤ t}(1 − d_s)E_{t−s}` (the
book writes the summation index as `t`; emissions start at date `0`). -/
theorem eq_25_9 (k E : ℕ → ℝ) (t : ℕ) :
    excessCarbon k E t = ∑ s ∈ Finset.range (t + 1), k s * E (t - s) := by
  unfold excessCarbon
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.mp hs
  congr 2; omega

/-- AKMM, p. 770: one more unit of emissions at date `t` raises excess carbon at `t + j` by
`1 − d_j`: `∂S_{t+j}/∂E_t = 1 − d_j`. -/
theorem excessCarbon_pulse (k E : ℕ → ℝ) (t j : ℕ) (h : ℝ) :
    excessCarbon k (fun v => E v + if v = t then h else 0) (t + j) =
      excessCarbon k E (t + j) + h * k j := by
  unfold excessCarbon
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range (t + j + 1)) t]
  simp only [Finset.mem_range, show t < t + j + 1 by omega, ↓reduceIte]
  rw [show t + j - t = j by omega]
  ring

end AKMM.Sustainability
