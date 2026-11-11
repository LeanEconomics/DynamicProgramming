/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFSteady
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Examples 10.1.1–10.1.4

Miao, §10.1.1, pp. 329 and 334–337.

* **Example 10.1.1** (Guvenen's labor income process): the state-space form with
  `x_t = (α, β, z_t)'`, `ε_t = (η_t/σ_η, v_t/σ_v)'` (`example_10_1_1`); the noises are
  uncorrelated (`CD' = 0`). Correction: the printed measurement equation uses
  `(η_{t+1}, v_{t+1})'`; with `y_t = α + βt + z_t + v_t` the shock is `ε_t = (η_t, v_t)'`, as
  (10.2) requires (`example_10_1_1_misprint`). The book also takes unit variances in `C, D`; here
  the loadings carry `σ_η, σ_v` so that `Eε_tε_t' = I`.
* The scalar filter (`kf_scalarSys`: `x_{t+1} = ax_t + cε¹_{t+1}`, `y_t = x_t + dε²_t`): the
  covariance recursion is `Σ_{t+1|t} = a²d²Σ/(Σ + d²) + c²` (`kf_scalarRic`), the gain
  `K_t = Σ/(Σ + d²)`, `Ω_t = Σ + d²` (`kf_scalar_filter`), and for `c ≠ 0, d ≠ 0` the iterates
  converge from every `Σ₀ ≥ 0` to the unique nonnegative fixed point, the positive root of
  `Σ² + d²(1 − a² − c²/d²)Σ − c²d² = 0` (`kf_scalar_tendsto`, a contraction argument).
* **Example 10.1.2** (Muth): `K_t = Σ_t/(Σ_t + R)`, `Σ_{t+1} = (Σ_t(R + Q) + QR)/(Σ_t + R)`,
  `Σ_t → Σ = (Q + √(Q² + 4QR))/2`, `K_t → K`, the filter `x̂_{t+1|t} = (1 − K_t)x̂_{t|t−1} + K_ty_t`
  and, at the steady state, Cagan's adaptive expectations formula (`example_10_1_2`,
  `example_10_1_2_adaptive`); the case `Q = 0`: `σ_{t+1} = σ_tR/(σ_t + R)`, the innovation form
  and `K²(σ + R) = Kσ` (`example_10_1_2_constant`).
* **Example 10.1.3** (long-run productivity growth): the stationary `Σ` and `K` formulas, the
  innovation variance `Σ + σ_v²`, `K²(Σ + σ_v²) = KΣ`, the filter in levels (`example_10_1_3`,
  `example_10_1_3_filter`); misprint `Eε_t` for `Eη_t` noted.
* **Example 10.1.4** (likelihood): the Gaussian log density `kf_logDens` is the logarithm of the
  `N(0, Ω)` density formula `kf_gaussDens`, and the log-likelihood of the innovations is
  `−(n_yT/2)ln 2π − ½∑ ln|Ω_t| − ½∑ a_t'Ω_t⁻¹a_t` (`example_10_1_4`). That the conditional density
  of `y_t` given `y^{t−1}` is this normal density is the Gaussian reading, which is not
  formalised; the prediction-error decomposition is taken as the definition of the likelihood.
-/

open Filter Topology Matrix

namespace Miao.PartialInformation

/-! ### Example 10.1.1 -/

/-- The measurement matrix `G_t = [1 t 1]` of Example 10.1.1. -/
def kf_laborG (t : ℕ) : Matrix (Fin 1) (Fin 3) ℝ := !![1, (t : ℝ), 1]

/-- **Example 10.1.1** (Miao, p. 329): Guvenen's log labor income `y_t = α + βt + z_t + v_t`,
`z_{t+1} = ρz_t + η_{t+1}` (with `η_t = σ_ηe¹_t`, `v_t = σ_ve²_t`) has the state-space form
`x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = G_tx_t + Dε_t` with `x_t = (α, β, z_t)'`, `ε_t = (e¹_t, e²_t)'`,
`A = diag(1, 1, ρ)`, `C = [0 0; 0 0; σ_η 0]`, `G_t = [1 t 1]`, `D = [0 σ_v]`, and `CD' = 0`. -/
theorem example_10_1_1 (α β ρ ση σv : ℝ) (z e1 e2 : ℕ → ℝ) (y : ℕ → ℝ)
    (hz : ∀ t, z (t + 1) = ρ * z t + ση * e1 (t + 1))
    (hy : ∀ t, y t = α + β * t + z t + σv * e2 t) (t : ℕ) :
    ![α, β, z (t + 1)] = !![1, 0, 0; 0, 1, 0; 0, 0, ρ] *ᵥ ![α, β, z t] +
      !![0, 0; 0, 0; ση, 0] *ᵥ ![e1 (t + 1), e2 (t + 1)] ∧
    (fun _ : Fin 1 => y t) = kf_laborG t *ᵥ ![α, β, z t] + !![0, σv] *ᵥ ![e1 t, e2 t] ∧
    !![0, 0; 0, 0; ση, 0] * (!![0, σv] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [hz, mul_comm]
  · funext i
    simp [kf_laborG, hy]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply]

/-- Example 10.1.1, the printed measurement equation `y_t = G_tx_t + D(η_{t+1}, v_{t+1})'` is a
misprint: with `α = β = z = 0` and `v₀ = 1`, all other shocks `0`, the income process gives
`y₀ = 1` while the printed form gives `0`. -/
theorem example_10_1_1_misprint :
    ∃ (z e1 e2 y : ℕ → ℝ), (∀ t, z (t + 1) = 0 * z t + 1 * e1 (t + 1)) ∧
      (∀ t, y t = 0 + 0 * t + z t + 1 * e2 t) ∧
      (fun _ : Fin 1 => y 0) ≠ kf_laborG 0 *ᵥ ![0, 0, z 0] + !![0, 1] *ᵥ ![e1 1, e2 1] := by
  refine ⟨fun _ => 0, fun _ => 0, fun t => if t = 0 then 1 else 0,
    fun t => if t = 0 then 1 else 0, fun t => by simp, fun t => by simp, fun h => ?_⟩
  have := congrFun h 0
  simp [kf_laborG] at this

/-! ### The scalar filter -/

theorem kf_inv_fin_one (M : Matrix (Fin 1) (Fin 1) ℝ) : M⁻¹ 0 0 = (M 0 0)⁻¹ := by
  simp

/-- The scalar system `x_{t+1} = ax_t + cε¹_{t+1}`, `y_t = x_t + dε²_t`, `x₀ ∼ (x̄₀, s₀)`. -/
noncomputable def kf_scalarSys (a c d xbar0 s0 : ℝ) : KFSystem (Fin 1) (Fin 1) (Fin 1) (Fin 2) :=
  KFSystem.const !![a] 0 !![c, 0] 1 0 !![0, d] (fun _ => xbar0) !![s0]

/-- The scalar Riccati map `s ↦ aRs/(s + R) + q`. -/
noncomputable def kf_scalarRic (a R q s : ℝ) : ℝ := a * R * s / (s + R) + q

/-- The positive root of `s² + (R − aR − q)s − qR = 0`. -/
noncomputable def kf_scalarRoot (a R q : ℝ) : ℝ :=
  (-(R - a * R - q) + Real.sqrt ((R - a * R - q) ^ 2 + 4 * q * R)) / 2

theorem kf_scalar_CD (c d : ℝ) :
    (!![c, 0] : Matrix (Fin 1) (Fin 2) ℝ) * (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [mul_apply]

theorem kf_scalar_DD (d : ℝ) :
    ((!![0, d] : Matrix (Fin 1) (Fin 2) ℝ) * (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ) 0 0 =
      d ^ 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, add_zero,
    Fin.succ_zero_eq_one]
  ring

/-- The filter recursion of the scalar system (with `B = 0` and no measurement input):
`x̂_{t+1|t} = ax̂_{t|t−1} + aK_t(y_t − x̂_{t|t−1})`. -/
theorem kf_scalar_xpred (a c d xbar0 s0 : ℝ) {Ω : Type*} (y : ℕ → Ω → Fin 1 → ℝ)
    (u : ℕ → Ω → Fin 1 → ℝ) (t : ℕ) (ω : Ω) :
    (kf_scalarSys a c d xbar0 s0).xpred y 0 u (t + 1) ω 0 =
      a * (kf_scalarSys a c d xbar0 s0).xpred y 0 u t ω 0 +
        a * (kf_scalarSys a c d xbar0 s0).K t 0 0 *
          (y t ω 0 - (kf_scalarSys a c d xbar0 s0).xpred y 0 u t ω 0) := by
  rw [KFSystem.kf_pred_recursive]
  simp only [kf_app, KFSystem.innov, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, mulVec,
    dotProduct, Fin.sum_univ_one, Matrix.mul_apply, kf_scalarSys, KFSystem.const, of_apply,
    cons_val', empty_val', cons_val_fin_one, Matrix.zero_apply, zero_mul, add_zero,
    Matrix.one_apply_eq, one_mul, sub_zero]

/-- The dual Riccati operator of the scalar system, entrywise. -/
theorem kf_scalar_dualT (a c d : ℝ) (P : Matrix (Fin 1) (Fin 1) ℝ) (hp : P 0 0 + d ^ 2 ≠ 0) :
    (kf_dual !![a] (1 : Matrix (Fin 1) (Fin 1) ℝ) !![c, 0] !![0, d]).T P 0 0 =
      kf_scalarRic (a ^ 2) (d ^ 2) (c ^ 2) (P 0 0) := by
  have hinv := kf_inv_fin_one (!![0, d] * !![0, d]ᵀ + 1 * P * 1)
  simp only [LSProblem.T, kf_dual, LSProblem.G, LSProblem.N, one_smul, transpose_transpose,
    transpose_zero, zero_add, transpose_one, Matrix.one_mul, Matrix.mul_one] at hinv ⊢
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, transpose_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, hinv, add_zero, Fin.succ_zero_eq_one]
  rw [show 0 * 0 + d * d + P 0 0 = P 0 0 + d ^ 2 by ring, kf_scalarRic]
  field_simp
  ring

/-- The scalar filter (Miao, pp. 334–336): `Σ_{t|t−1} ≥ 0`,
`Σ_{t+1|t} = a²d²Σ_{t|t−1}/(Σ_{t|t−1} + d²) + c²`, `K_t = Σ_{t|t−1}/(Σ_{t|t−1} + d²)` and
`Ω_{t|t−1} = Σ_{t|t−1} + d²`, for `d ≠ 0`, `s₀ ≥ 0`. -/
theorem kf_scalar_filter (a c d xbar0 s0 : ℝ) (hd : d ≠ 0) (hs0 : 0 ≤ s0) (t : ℕ) :
    0 ≤ (kf_scalarSys a c d xbar0 s0).Spred t 0 0 ∧
      (kf_scalarSys a c d xbar0 s0).Spred (t + 1) 0 0 =
        kf_scalarRic (a ^ 2) (d ^ 2) (c ^ 2) ((kf_scalarSys a c d xbar0 s0).Spred t 0 0) ∧
      (kf_scalarSys a c d xbar0 s0).K t 0 0 = (kf_scalarSys a c d xbar0 s0).Spred t 0 0 /
        ((kf_scalarSys a c d xbar0 s0).Spred t 0 0 + d ^ 2) ∧
      (kf_scalarSys a c d xbar0 s0).Om t 0 0 =
        (kf_scalarSys a c d xbar0 s0).Spred t 0 0 + d ^ 2 := by
  have hS : kf_scalarSys a c d xbar0 s0 =
      KFSystem.const !![a] 0 !![c, 0] 1 0 !![0, d] (fun _ => xbar0) !![s0] := rfl
  rw [hS]
  set S := KFSystem.const !![a] 0 !![c, 0] 1 0 !![0, d] (fun _ => xbar0) !![s0] with hSdef
  have hd2 : 0 < d ^ 2 := by positivity
  have hrec : ∀ t, S.Spred (t + 1) = (kf_dual !![a] 1 !![c, 0] !![0, d]).T (S.Spred t) := by
    intro t
    rw [hSdef, (kf_const_Spred _ _ _ _ _ _ _ _ (kf_scalar_CD c d) (t + 1)).1,
      Function.iterate_succ_apply', ← (kf_const_Spred _ _ _ _ _ _ _ _ (kf_scalar_CD c d) t).1]
  have hnn : ∀ t, 0 ≤ S.Spred t 0 0 := by
    intro t
    induction t with
    | zero =>
      change 0 ≤ (!![s0] : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      simpa using hs0
    | succ t ih =>
      rw [hrec, kf_scalar_dualT a c d _ (by positivity), kf_scalarRic]
      positivity
  refine ⟨hnn t, by rw [hrec, kf_scalar_dualT a c d _ (by linarith [hnn t])], ?_, ?_⟩
  · rw [hSdef, (kf_const_Spred _ _ _ _ _ _ _ _ (kf_scalar_CD c d) t).2, ← hSdef]
    have hinv := kf_inv_fin_one (1 * S.Spred t * 1ᵀ + !![0, d] * !![0, d]ᵀ)
    simp only [kf_steadyGain, transpose_one, Matrix.one_mul, Matrix.mul_apply, Fin.sum_univ_one,
      mul_one] at hinv ⊢
    rw [hinv, Matrix.add_apply, kf_scalar_DD, div_eq_mul_inv]
  · have hCl : S.Cl t * (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ = 0 := by
      cases t with
      | zero => exact Matrix.zero_mul _
      | succ t => exact kf_scalar_CD c d
    have hDC : (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ) * (S.Cl t)ᵀ = 0 := by
      rw [← transpose_transpose (!![0, d] * (S.Cl t)ᵀ), transpose_mul, transpose_transpose, hCl,
        transpose_zero]
    simp only [KFSystem.Om, kf_Om]
    rw [show S.G t = 1 from rfl, show S.D t = !![0, d] from rfl, Matrix.mul_assoc 1 (S.Cl t),
      hCl, hDC]
    simp only [Matrix.mul_zero, add_zero, Matrix.one_mul, transpose_one, Matrix.mul_one,
      Matrix.add_apply, kf_scalar_DD, Matrix.zero_apply]

/-- The scalar Riccati map is nonnegative on `[0, ∞)`. -/
theorem kf_scalarRic_nonneg {a R q s : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    0 ≤ kf_scalarRic a R q s := by
  unfold kf_scalarRic
  have : 0 < s + R := by linarith
  positivity

/-- The scalar steady state (Miao, pp. 334–336): for `a ≥ 0`, `R > 0`, `q > 0` the root
`s* = (−(R − aR − q) + √((R − aR − q)² + 4qR))/2` is positive, is the unique nonnegative fixed
point of `s ↦ aRs/(s + R) + q`, and the iterates converge to it from every `s₀ ≥ 0` (the map is a
contraction with modulus `aR/(s* + R) < 1` towards `s*`). -/
theorem kf_scalar_tendsto {a R q : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hq : 0 < q) :
    0 < kf_scalarRoot a R q ∧ kf_scalarRic a R q (kf_scalarRoot a R q) = kf_scalarRoot a R q ∧
      (∀ s, 0 ≤ s → kf_scalarRic a R q s = s → s = kf_scalarRoot a R q) ∧
      ∀ s0, 0 ≤ s0 → Tendsto (fun t => (kf_scalarRic a R q)^[t] s0) atTop
        (𝓝 (kf_scalarRoot a R q)) := by
  set b := R - a * R - q
  set Δ := b ^ 2 + 4 * q * R
  set r := kf_scalarRoot a R q
  have hΔ : b ^ 2 < Δ := by simp only [Δ]; nlinarith
  have hsq : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt (by nlinarith)
  have hgt : b < Real.sqrt Δ ∧ -b < Real.sqrt Δ := by
    have h0 : |b| < Real.sqrt Δ := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hΔ
    exact ⟨lt_of_le_of_lt (le_abs_self b) h0, lt_of_le_of_lt (neg_le_abs b) h0⟩
  have hr : r = (-b + Real.sqrt Δ) / 2 := rfl
  have hrpos : 0 < r := by rw [hr]; linarith [hgt.1, hgt.2]
  have hquad : r ^ 2 + b * r - q * R = 0 := by
    rw [hr]
    nlinarith [hsq]
  have hfix : kf_scalarRic a R q r = r := by
    unfold kf_scalarRic
    have : r + R ≠ 0 := by linarith
    field_simp
    nlinarith [hquad]
  have hκ : a * R < r + R := by
    have h1 : r * (r + R - a * R) = q * (r + R) := by nlinarith [hquad]
    have h2 : 0 < r * (r + R - a * R) := by rw [h1]; positivity
    have := (pos_iff_pos_of_mul_pos h2).1 hrpos
    linarith
  refine ⟨hrpos, hfix, fun s hs hfs => ?_, fun s0 hs0 => ?_⟩
  · have hsR : s + R ≠ 0 := by linarith
    unfold kf_scalarRic at hfs
    field_simp at hfs
    have hq' : s ^ 2 + b * s - q * R = 0 := by simp only [b]; nlinarith [hfs]
    have hprod : (s - r) * (s + r + b) = 0 := by nlinarith [hquad, hq']
    have hpos : 0 < s + r + b := by rw [hr]; linarith [hgt.2]
    have := (mul_eq_zero.1 hprod).resolve_right hpos.ne'
    linarith
  · set κ := a * R / (r + R)
    have hκ0 : 0 ≤ κ := by positivity
    have hκ1 : κ < 1 := (div_lt_one (by linarith)).2 hκ
    have hcontr : ∀ s, 0 ≤ s → |kf_scalarRic a R q s - r| ≤ κ * |s - r| := by
      intro s hs
      have hsR : 0 < s + R := by linarith
      have hrR : 0 < r + R := by linarith
      have heq : kf_scalarRic a R q s - r = a * R * R * (s - r) / ((s + R) * (r + R)) := by
        conv_lhs => rw [← hfix]
        unfold kf_scalarRic
        field_simp
        ring
      rw [heq, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a * R * R),
        abs_of_pos (by positivity : 0 < (s + R) * (r + R))]
      rw [div_le_iff₀ (by positivity)]
      have : κ * |s - r| * ((s + R) * (r + R)) = a * R * |s - r| * (s + R) := by
        simp only [κ]
        field_simp
      rw [this]
      have habs := abs_nonneg (s - r)
      nlinarith [mul_nonneg (mul_nonneg ha hR.le) habs]
    have hnn : ∀ t, 0 ≤ (kf_scalarRic a R q)^[t] s0 := by
      intro t
      induction t with
      | zero => exact hs0
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact kf_scalarRic_nonneg ha hR hq.le ih
    have hbd : ∀ t, |(kf_scalarRic a R q)^[t] s0 - r| ≤ κ ^ t * |s0 - r| := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc _ ≤ κ * |(kf_scalarRic a R q)^[t] s0 - r| := hcontr _ (hnn t)
          _ ≤ κ * (κ ^ t * |s0 - r|) := mul_le_mul_of_nonneg_left ih hκ0
          _ = κ ^ t * κ * |s0 - r| := by ring
    have hlim : Tendsto (fun t => κ ^ t * |s0 - r|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const |s0 - r|
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun t => dist_nonneg) (fun t => by rw [Real.dist_eq]; exact hbd t) hlim

/-! ### Example 10.1.2 (Muth) -/

/-- **Example 10.1.2** (Muth, Miao, p. 334). The scalar system `x_{t+1} = x_t + η_{t+1}`,
`y_t = x_t + v_t`, `Eη² = Q`, `Ev² = R > 0`, `Σ₀ ≥ 0`: (i) `K_t = Σ_{t|t−1}/(Σ_{t|t−1} + R)` and
`Σ_{t+1|t} = (Σ_{t|t−1}(R + Q) + QR)/(Σ_{t|t−1} + R)`; (ii) the filter is
`x̂_{t+1|t} = (1 − K_t)x̂_{t|t−1} + K_ty_t`; (iii) for `Q > 0`,
`Σ_{t|t−1} → Σ = (Q + √(Q² + 4QR))/2`
and `K_t → K = Σ/(Σ + R)`. -/
theorem example_10_1_2 {Q R : ℝ} (hQ : 0 ≤ Q) (hR : 0 < R) (xbar0 s0 : ℝ) (hs0 : 0 ≤ s0)
    {Ω : Type*} (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) :
    (∀ t, (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0 =
        (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 /
          ((kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 + R) ∧
      (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred (t + 1) 0 0 =
        ((kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 * (R + Q) + Q * R) /
          ((kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 + R)) ∧
    (∀ t ω, (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).xpred y 0 u (t + 1) ω 0 =
      (1 - (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0) *
        (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).xpred y 0 u t ω 0 +
      (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0 * y t ω 0) ∧
    (0 < Q → Tendsto (fun t => (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0)
        atTop (𝓝 ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2)) ∧
      Tendsto (fun t => (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0) atTop
        (𝓝 ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 /
          ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 + R)))) := by
  set S := kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hQ2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
  have hF := fun t => kf_scalar_filter 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0 hd hs0 t
  have hrec : ∀ t, S.Spred (t + 1) 0 0 = kf_scalarRic 1 R Q (S.Spred t 0 0) := by
    intro t
    rw [(hF t).2.1, hR2, hQ2, one_pow]
  have hK : ∀ t, S.K t 0 0 = S.Spred t 0 0 / (S.Spred t 0 0 + R) := by
    intro t
    rw [(hF t).2.2.1, hR2]
  refine ⟨fun t => ⟨hK t, ?_⟩, fun t ω => ?_, fun hQp => ?_⟩
  · rw [hrec, kf_scalarRic]
    have : S.Spred t 0 0 + R ≠ 0 := by linarith [(hF t).1]
    field_simp
    ring
  · rw [kf_scalar_xpred]
    ring
  · have hSt : Tendsto (fun t => S.Spred t 0 0) atTop
        (𝓝 ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2)) := by
      have hroot : kf_scalarRoot 1 R Q = (Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 := by
        simp only [kf_scalarRoot]
        ring_nf
      rw [← hroot]
      have h := (kf_scalar_tendsto zero_le_one hR hQp).2.2.2 (S.Spred 0 0 0) (hF 0).1
      refine (tendsto_add_atTop_iff_nat 0).1 (h.congr fun t => ?_)
      induction t with
      | zero => rfl
      | succ t ih => rw [Function.iterate_succ_apply', ih, ← hrec]
    refine ⟨hSt, ?_⟩
    have hpos : 0 < (Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 + R := by
      have := Real.sqrt_nonneg (Q ^ 2 + 4 * Q * R)
      linarith
    simp only [hK]
    exact hSt.div (hSt.add_const R) hpos.ne'

/-- Example 10.1.2 (Miao, p. 334): started at the steady state `Σ` (a fixed point of the Riccati
map), the gain is constant, `K_t = K`, and the filter is Cagan's adaptive expectations formula
`x̂_{t+1|t} = (1 − K)x̂_{t|t−1} + Ky_t`. -/
theorem example_10_1_2_adaptive {Q R : ℝ} (hR : 0 < R) (xbar0 : ℝ) {s : ℝ}
    (hfix : (kf_dual !![1] (1 : Matrix (Fin 1) (Fin 1) ℝ) !![Real.sqrt Q, 0]
      !![0, Real.sqrt R]).T !![s] = !![s]) (hs : 0 ≤ s)
    {Ω : Type*} (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) (t : ℕ) (ω : Ω) :
    (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).K t 0 0 = s / (s + R) ∧
      (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).xpred y 0 u (t + 1) ω 0 =
        (1 - s / (s + R)) * (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).xpred y 0 u t ω 0
          + s / (s + R) * y t ω 0 := by
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hP : (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).Spred t = !![s] :=
    (kf_steady_fixed _ _ _ _ _ _ _ (kf_scalar_CD _ _) hfix t).1
  have hK : (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).K t 0 0 = s / (s + R) := by
    rw [(kf_scalar_filter 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s hd hs t).2.2.1, hP, hR2]
    simp
  refine ⟨hK, ?_⟩
  rw [kf_scalar_xpred, hK]
  ring

/-- Example 10.1.2 with `Q = 0` (Miao, pp. 334–335): `σ_{t+1} = σ_tR/(σ_t + R)` (with
`σ_t = Σ_{t|t−1}`), `K_t = σ_t/(σ_t + R)`, `m_t = (1 − K_t)m_{t−1} + K_ty_t`
(`m_{t−1} = x̂_{t|t−1}`),
and the variance of `K_ta_t`, `K_t²(σ_t + R)`, equals `K_tσ_t` (so `K_ta_t = √(K_tσ_t) ξ_t` with
`ξ_t` of unit variance). -/
theorem example_10_1_2_constant {R : ℝ} (hR : 0 < R) (xbar0 s0 : ℝ) (hs0 : 0 ≤ s0) (t : ℕ) :
    (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred (t + 1) 0 0 =
        (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 * R /
          ((kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 + R) ∧
      (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).K t 0 0 ^ 2 *
          ((kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 + R) =
        (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).K t 0 0 *
          (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 := by
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  obtain ⟨hnn, hrec, hK, -⟩ := kf_scalar_filter 1 0 (Real.sqrt R) xbar0 s0 hd hs0 t
  have hpos : (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 + R ≠ 0 := by linarith
  rw [hR2] at hrec hK
  refine ⟨?_, ?_⟩
  · rw [hrec, kf_scalarRic]
    field_simp
    ring
  · rw [hK]
    field_simp

/-! ### Example 10.1.3 -/

/-- **Example 10.1.3** (Miao, pp. 335–336), the stationary filter. With `φ = σ_η²/σ_v²` and
`b = 1 − ρ² − φ`, the stationary covariance `Σ = (σ_v²/2)(−b + √(b² + 4φ))` is the unique
nonnegative solution of `Σ = ρ²(1 − Σ(Σ + σ_v²)⁻¹)Σ + σ_η²`, the stationary gain is
`K = Σ/(Σ + σ_v²) = 1 − 2/(2 − b + √(b² + 4φ))`, and `K²(Σ + σ_v²) = KΣ`. The filter covariances
of the scalar system `(a, c, d) = (ρ, σ_η, σ_v)` converge to `Σ` from every `Σ₀ ≥ 0`, and the
innovation variance is `Ω_t = Σ_{t|t−1} + σ_v²` (`→ Σ + σ_v²`). -/
theorem example_10_1_3 {ρ ση σv : ℝ} (hη : ση ≠ 0) (hv : σv ≠ 0) (xbar0 s0 : ℝ) (hs0 : 0 ≤ s0) :
    let φ := ση ^ 2 / σv ^ 2
    let b := 1 - ρ ^ 2 - φ
    let Sg := σv ^ 2 / 2 * (-b + Real.sqrt (b ^ 2 + 4 * φ))
    0 < Sg ∧ Sg = ρ ^ 2 * (1 - Sg * (Sg + σv ^ 2)⁻¹) * Sg + ση ^ 2 ∧
      (∀ s, 0 ≤ s → s = ρ ^ 2 * (1 - s * (s + σv ^ 2)⁻¹) * s + ση ^ 2 → s = Sg) ∧
      Sg / (Sg + σv ^ 2) = 1 - 2 / (2 - b + Real.sqrt (b ^ 2 + 4 * φ)) ∧
      (Sg / (Sg + σv ^ 2)) ^ 2 * (Sg + σv ^ 2) = Sg / (Sg + σv ^ 2) * Sg ∧
      Tendsto (fun t => (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0) atTop (𝓝 Sg) ∧
      ∀ t, (kf_scalarSys ρ ση σv xbar0 s0).Om t 0 0 =
        (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0 + σv ^ 2 := by
  intro φ b Sg
  have hv2 : 0 < σv ^ 2 := by positivity
  have hη2 : 0 < ση ^ 2 := by positivity
  obtain ⟨hpos, hfix, huniq, hconv⟩ := kf_scalar_tendsto (sq_nonneg ρ) hv2 hη2
  have hroot : kf_scalarRoot (ρ ^ 2) (σv ^ 2) (ση ^ 2) = Sg := by
    simp only [kf_scalarRoot, Sg, b, φ]
    have h1 : (σv ^ 2 - ρ ^ 2 * σv ^ 2 - ση ^ 2) ^ 2 + 4 * ση ^ 2 * σv ^ 2 =
        (σv ^ 2) ^ 2 * ((1 - ρ ^ 2 - ση ^ 2 / σv ^ 2) ^ 2 + 4 * (ση ^ 2 / σv ^ 2)) := by
      field_simp
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hv2.le]
    field_simp
  have hform : ∀ s, 0 ≤ s → ρ ^ 2 * (1 - s * (s + σv ^ 2)⁻¹) * s + ση ^ 2 =
      kf_scalarRic (ρ ^ 2) (σv ^ 2) (ση ^ 2) s := by
    intro s hs
    have : s + σv ^ 2 ≠ 0 := by linarith
    unfold kf_scalarRic
    field_simp
    ring
  rw [hroot] at hpos hfix huniq hconv
  have hSg1 : Sg + σv ^ 2 ≠ 0 := by linarith
  have hsq : Real.sqrt (b ^ 2 + 4 * φ) ^ 2 = b ^ 2 + 4 * φ :=
    Real.sq_sqrt (by have : 0 ≤ φ := by positivity
                     nlinarith)
  have hSgdef : Sg = σv ^ 2 / 2 * (-b + Real.sqrt (b ^ 2 + 4 * φ)) := rfl
  refine ⟨hpos, by rw [hform _ hpos.le, hfix], fun s hs h => huniq s hs (by rw [← hform s hs,
    ← h]), ?_, by field_simp, ?_, fun t => ?_⟩
  · have h2 : 2 - b + Real.sqrt (b ^ 2 + 4 * φ) ≠ 0 := by
      have : 0 < -b + Real.sqrt (b ^ 2 + 4 * φ) := by
        have := hpos
        rw [hSgdef] at this
        exact (pos_iff_pos_of_mul_pos this).1 (by positivity)
      linarith
    rw [eq_sub_iff_add_eq, div_add_div _ _ hSg1 h2, div_eq_one_iff_eq (mul_ne_zero hSg1 h2),
      hSgdef]
    field_simp
    ring
  · have hd : σv ≠ 0 := hv
    have hF := fun t => kf_scalar_filter ρ ση σv xbar0 s0 hd hs0 t
    have h := hconv ((kf_scalarSys ρ ση σv xbar0 s0).Spred 0 0 0) (hF 0).1
    refine (h.congr fun t => ?_)
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', ih, ← (hF t).2.1]
  · exact (kf_scalar_filter ρ ση σv xbar0 s0 hv hs0 t).2.2.2

/-- Example 10.1.3 (Miao, pp. 335–336), the filter in levels: with `y_t = z_t − z_{t−1}`, the
deviation-form filter `m̃_{t+1} = ρm̃_t + K(ỹ_{t+1} − ρm̃_t)` (`m̃ = x̂ − g`, `ỹ = y − g`) is
`x̂_{t+1|t+1} = ρx̂_{t|t} + (1 − ρ)g + Ka_{t+1}`,
`a_{t+1} = z_{t+1} − z_t − ρx̂_{t|t} − (1 − ρ)g`. -/
theorem example_10_1_3_filter (ρ g K : ℝ) (m z : ℕ → ℝ)
    (hm : ∀ t, m (t + 1) - g = ρ * (m t - g) + K * ((z (t + 1) - z t - g) - ρ * (m t - g)))
    (t : ℕ) :
    m (t + 1) = ρ * m t + (1 - ρ) * g + K * (z (t + 1) - z t - ρ * m t - (1 - ρ) * g) := by
  linear_combination hm t

/-! ### Example 10.1.4 -/

/-- The `N(0, Ω)` density formula `(2π)^{−n/2}|Ω|^{−1/2}exp(−½a'Ω⁻¹a)`. -/
noncomputable def kf_gaussDens {Y : Type*} [Fintype Y] [DecidableEq Y] (Om : Matrix Y Y ℝ)
    (a : Y → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(Fintype.card Y : ℝ) / 2) * Om.det ^ (-(1 : ℝ) / 2) *
    Real.exp (-(1 / 2) * (a ⬝ᵥ (Om⁻¹ *ᵥ a)))

/-- The Gaussian log density `−(n/2)ln 2π − ½ln|Ω| − ½a'Ω⁻¹a`. -/
noncomputable def kf_logDens {Y : Type*} [Fintype Y] [DecidableEq Y] (Om : Matrix Y Y ℝ)
    (a : Y → ℝ) : ℝ :=
  -(Fintype.card Y / 2) * Real.log (2 * Real.pi) - 1 / 2 * Real.log Om.det -
    1 / 2 * (a ⬝ᵥ (Om⁻¹ *ᵥ a))

/-- **Example 10.1.4** (Miao, pp. 336–337): for `|Ω_t| > 0`, the log-likelihood
`∑_{t=1}^T ln p(y_t|y^{t−1})`, each factor the `N(ŷ_{t|t−1}, Ω_{t|t−1})` density at `y_t`, i.e. the
`N(0, Ω_t)` density at the innovation `a_t`, is
`−(n_yT/2)ln 2π − ½∑ln|Ω_t| − ½∑a_t'Ω_t⁻¹a_t`. -/
theorem example_10_1_4 {Y : Type*} [Fintype Y] [DecidableEq Y] (Om : ℕ → Matrix Y Y ℝ)
    (a : ℕ → Y → ℝ) (T : ℕ) (hdet : ∀ t, 0 < (Om t).det) :
    (∀ t, Real.log (kf_gaussDens (Om t) (a t)) = kf_logDens (Om t) (a t)) ∧
      ∑ t ∈ Finset.Icc 1 T, Real.log (kf_gaussDens (Om t) (a t)) =
        -(Fintype.card Y * T / 2) * Real.log (2 * Real.pi) -
          1 / 2 * ∑ t ∈ Finset.Icc 1 T, Real.log (Om t).det -
          1 / 2 * ∑ t ∈ Finset.Icc 1 T, a t ⬝ᵥ ((Om t)⁻¹ *ᵥ a t) := by
  have hlog : ∀ t, Real.log (kf_gaussDens (Om t) (a t)) = kf_logDens (Om t) (a t) := by
    intro t
    have h2 : 0 < 2 * Real.pi := by positivity
    unfold kf_gaussDens kf_logDens
    have h3 := Real.rpow_pos_of_pos h2 (-(Fintype.card Y : ℝ) / 2)
    have h4 := Real.rpow_pos_of_pos (hdet t) (-(1 : ℝ) / 2)
    rw [Real.log_mul (mul_pos h3 h4).ne' (Real.exp_pos _).ne', Real.log_mul h3.ne' h4.ne',
      Real.log_rpow h2, Real.log_rpow (hdet t), Real.log_exp]
    ring
  refine ⟨hlog, ?_⟩
  simp only [hlog, kf_logDens, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  ring

end Miao.PartialInformation
