/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Monetary policy design: the efficient allocation (Miao §19.2.1)

Miao, §19.2.1, pp. 630–631, with the inefficiency measure `Φ` and `x*` of p. 634.

The planner's problem of p. 630 is static date by date. With the firms indexed by a probability
space `(Ω, μ)` (the book's `dj` on `[0, 1]`), firm output `Y_j = A N_j^{1−α}` and the CES
aggregate `Y = (∫ Y_j^{(ε−1)/ε})^{ε/(ε−1)}`:
* `mp_ces_le`, `mp_ces_symmetric`, `mp_ces_lt`: for any labour allocation with `∫ N_j = N`,
  `Y ≤ AN^{1−α}`, with equality for the symmetric allocation `N_j = N` (then `Y_j = Y`) and
  strict inequality unless `N_j = N` almost everywhere ("`Y_t^j = Y_t = C_t`, `N_t^j = N_t`").
* `mp_planner_foc`: with the utility (19.1) without money (`mpU`), an interior maximiser of
  `u(AN^{1−α}, N)` satisfies `−u_N/u_C = (1 − α)AN^{−α} = MPN`.
* `mp_mrs_iff_log`, `mp_mrs_output`: the condition `MRS = MPN/m` (`m = 1` efficient, `m = μ`
  flexible prices) has the unique solution `ln N = (ln((1 − α)/(mχ)) + (1 − γ)ln A)/D`,
  `D = γ(1 − α) + α + ν`, and then output is `mpYout = ((1 − α)/(mχ))^{(1−α)/D} A^{(1+ν)/D}`,
  i.e. (19.18), with `m = 1` the efficient output `Y^e`.
* `mp_subsidy`: the employment subsidy `τ = 1/ε` gives `(1 − τ)μ = 1`, so the firm's condition
  `(1 − τ)W/P = MPN/μ` becomes `W/P = MPN`, and `τ = 1/ε` is the only such subsidy;
  `mp_subsidy_household` (footnote 6): a subsidy to the household must be `1/(ε − 1)`;
  `mp_flex_subsidy_efficient`: with the subsidy the flexible-price output is `Y^e`.
* `mp_distortion`: in the flexible-price equilibrium with subsidy `τ`,
  `−u_N/u_C = MPN(1 − Φ)` with `Φ = 1 − 1/((1 − τ)μ)` (p. 634), and `Φ = 0` iff `τ = 1/ε`.
* `mp_yf_loglinear`: `ŷ^f = (1 + ν)/D · â` (used on p. 634); `mp_xstar_first_order`:
  `ln(Y^e/Y^f) = −((1 − α)/D)ln(1 − Φ)`, which equals `x* = Φ(1 − α)/D` up to `2((1 − α)/D)Φ²`
  for `|Φ| ≤ 1/2` ("up to first-order approximation, `x*` is the log of `Y^e/Y^f`").

The firm FOC, the household FOC and the flexible-price equilibrium are §19.1 (another part);
here they enter as the equations the text writes on p. 631.
-/

namespace Miao.NewKeynesian

open MeasureTheory

/-! ### The CES aggregate and the symmetric allocation -/

/-- The CES aggregate `Y = (∫ Y_j^{(ε−1)/ε} dj)^{ε/(ε−1)}` (Miao, p. 630). -/
noncomputable def mpCES {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ) (μ : Measure Ω) (Yj : Ω → ℝ) :
    ℝ :=
  (∫ j, Yj j ^ ((ε - 1) / ε) ∂μ) ^ (ε / (ε - 1))

/-- The exponent `q = (1 − α)(ε − 1)/ε` of `N_j` in `Y_j^{(ε−1)/ε}`; `0 < q < 1`. -/
theorem mp_q_bounds {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) :
    0 < (1 - α) * ((ε - 1) / ε) ∧ (1 - α) * ((ε - 1) / ε) < 1 := by
  have he0 : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  have he1 : (ε - 1) / ε < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine ⟨mul_pos (by linarith) he0, ?_⟩
  nlinarith

/-- `(AN_j^{1−α})^{(ε−1)/ε} = A^{(ε−1)/ε} N_j^q`. -/
theorem mp_firm_term {α ε A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n) :
    (A * n ^ (1 - α)) ^ ((ε - 1) / ε) = A ^ ((ε - 1) / ε) * n ^ ((1 - α) * ((ε - 1) / ε)) := by
  rw [Real.mul_rpow hA (Real.rpow_nonneg hn _), ← Real.rpow_mul hn]

/-- `(A^{(ε−1)/ε} N^q)^{ε/(ε−1)} = AN^{1−α}`. -/
theorem mp_ces_const {α ε A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) (hε : 1 < ε) :
    (A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))) ^ (ε / (ε - 1)) = A * N ^ (1 - α) := by
  have he : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have hinv : ε / (ε - 1) = ((ε - 1) / ε)⁻¹ := by rw [inv_div]
  rw [Real.rpow_mul hN, ← Real.mul_rpow hA (Real.rpow_nonneg hN _), hinv,
    Real.rpow_rpow_inv (mul_nonneg hA (Real.rpow_nonneg hN _)) he]

/-- `N_j^q` is integrable whenever `N_j ≥ 0` is (`N^q ≤ 1 + N` for `0 < q < 1`). -/
theorem mp_integrable_rpow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {n : Ω → ℝ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hn : ∀ j, 0 ≤ n j) (hi : Integrable n μ) :
    Integrable (fun j => n j ^ q) μ := by
  refine Integrable.mono' ((integrable_const 1).add hi)
    ((Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hn j) _)]
  rcases le_total (n j) 1 with h | h
  · have := Real.rpow_le_one (hn j) h hq0.le
    simp only [Pi.add_apply]
    linarith [hn j]
  · have := Real.rpow_le_rpow_of_exponent_le h hq1.le
    rw [Real.rpow_one] at this
    simp only [Pi.add_apply]
    linarith

/-- **The symmetric allocation is output-maximising** (Miao, p. 630). For a probability measure
on the firms, `A ≥ 0`, `0 ≤ α < 1`, `ε > 1` and any integrable labour allocation `N_j ≥ 0`,
`Y = (∫(AN_j^{1−α})^{(ε−1)/ε})^{ε/(ε−1)} ≤ A(∫N_j)^{1−α}`. -/
theorem mp_ces_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α ε A : ℝ} (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) {n : Ω → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hi : Integrable n μ) :
    mpCES ε μ (fun j => A * n j ^ (1 - α)) ≤ A * (∫ j, n j ∂μ) ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := mp_q_bounds hα0 hα1 hε
  set q := (1 - α) * ((ε - 1) / ε)
  have hN : 0 ≤ ∫ j, n j ∂μ := integral_nonneg hn
  have hqi := mp_integrable_rpow hq0 hq1 hn hi
  have hJ : ∫ j, n j ^ q ∂μ ≤ (∫ j, n j ∂μ) ^ q :=
    (Real.strictConcaveOn_rpow hq0 hq1).concaveOn.le_map_integral
      (Real.continuous_rpow_const hq0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hn) hi hqi
  have hI0 : 0 ≤ ∫ j, n j ^ q ∂μ := integral_nonneg fun j => Real.rpow_nonneg (hn j) _
  simp only [mpCES]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun j => mp_firm_term hA (hn j)),
    integral_const_mul, ← mp_ces_const (α := α) hA hN hε]
  exact Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hA _) hI0)
    (mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hA _)) (div_pos (by linarith) (by linarith)).le

/-- Miao, p. 631: at the symmetric allocation `N_j = N`, `Y_j = Y = AN^{1−α}`. -/
theorem mp_ces_symmetric {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {α ε A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) (hε : 1 < ε) :
    mpCES ε μ (fun _ => A * N ^ (1 - α)) = A * N ^ (1 - α) := by
  simp only [mpCES, integral_const, probReal_univ, one_smul]
  rw [mp_firm_term hA hN, mp_ces_const hA hN hε]

/-- **Uniqueness of the symmetric allocation** (Miao, p. 631: "`Y_t^j = Y_t`, `N_t^j = N_t` for
all `j`"). For `A > 0`, unless `N_j = ∫N_j` for almost every `j`, output is strictly below
`A(∫N_j)^{1−α}`. -/
theorem mp_ces_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α ε A : ℝ} (hA : 0 < A) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) {n : Ω → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hi : Integrable n μ)
    (hne : ¬ n =ᵐ[μ] Function.const Ω (∫ j, n j ∂μ)) :
    mpCES ε μ (fun j => A * n j ^ (1 - α)) < A * (∫ j, n j ∂μ) ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := mp_q_bounds hα0 hα1 hε
  set q := (1 - α) * ((ε - 1) / ε)
  have hN : 0 ≤ ∫ j, n j ∂μ := integral_nonneg hn
  have hqi := mp_integrable_rpow hq0 hq1 hn hi
  have hJ : ∫ j, n j ^ q ∂μ < (∫ j, n j ∂μ) ^ q := by
    rcases (Real.strictConcaveOn_rpow hq0 hq1).ae_eq_const_or_lt_map_average
      (Real.continuous_rpow_const hq0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hn) hi hqi with h | h
    · rw [average_eq_integral] at h
      exact absurd h hne
    · simpa only [average_eq_integral] using h
  have hI0 : 0 ≤ ∫ j, n j ^ q ∂μ := integral_nonneg fun j => Real.rpow_nonneg (hn j) _
  simp only [mpCES]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun j => mp_firm_term hA.le (hn j)),
    integral_const_mul, ← mp_ces_const (α := α) hA.le hN hε]
  exact Real.rpow_lt_rpow (mul_nonneg (Real.rpow_nonneg hA.le _) hI0)
    (mul_lt_mul_of_pos_left hJ (Real.rpow_pos_of_pos hA _)) (div_pos (by linarith) (by linarith))

/-! ### The planner's first-order condition -/

/-- The period utility (19.1) without money: `u(C, N) = C^{1−γ}/(1 − γ) − χN^{1+ν}/(1 + ν)`. -/
noncomputable def mpU (γ χ ν C N : ℝ) : ℝ := C ^ (1 - γ) / (1 - γ) - χ * N ^ (1 + ν) / (1 + ν)

/-- `u_C = C^{−γ}` for (19.1) (`γ ≠ 1`, `C > 0`). -/
theorem mp_hasDerivAt_uC {γ χ ν C N : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun c => mpU γ χ ν c N) (C ^ (-γ)) C := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hC.ne')).div_const (1 - γ)).sub_const
    (χ * N ^ (1 + ν) / (1 + ν))
  refine this.congr_deriv ?_
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- `u_N = −χN^ν` for (19.1) (`ν ≠ −1`, `N > 0`). -/
theorem mp_hasDerivAt_uN {γ χ ν C N : ℝ} (hν : ν ≠ -1) (hN : 0 < N) :
    HasDerivAt (fun n => mpU γ χ ν C n) (-(χ * N ^ ν)) N := by
  have h1 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  have := (((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + ν)).const_sub (C ^ (1 - γ) / (1 - γ))
  refine this.congr_deriv ?_
  rw [show 1 + ν - 1 = ν by ring]
  field_simp

/-- The marginal product of labour: `d(AN^{1−α})/dN = (1 − α)AN^{−α}`. -/
theorem mp_hasDerivAt_mpn {α A N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => A * n ^ (1 - α)) ((1 - α) * A * N ^ (-α)) N := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A
  convert this using 1
  rw [show 1 - α - 1 = -α by ring]
  ring

/-- **The planner's condition** (Miao, p. 631). If `N > 0` maximises `u(AN^{1−α}, N)` locally
(`γ ≠ 1`, `ν ≠ −1`, `A > 0`), then `−u_N/u_C = (1 − α)AN^{−α}`: with `C = AN^{1−α}`,
`χN^ν/C^{−γ} = MPN`. -/
theorem mp_planner_foc {γ χ ν α A N : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hA : 0 < A) (hN : 0 < N)
    (hmax : IsLocalMax (fun n => mpU γ χ ν (A * n ^ (1 - α)) n) N) :
    χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ) = (1 - α) * A * N ^ (-α) := by
  set C := A * N ^ (1 - α)
  have hC : 0 < C := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h2 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  have hc := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hC.ne')).comp N
    (mp_hasDerivAt_mpn (α := α) (A := A) hN)).div_const (1 - γ)
  have hn := ((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + ν)
  have hd := hc.sub hn
  have h0 := hmax.hasDerivAt_eq_zero hd
  have hCg : 0 < C ^ (-γ) := Real.rpow_pos_of_pos hC _
  rw [show 1 - γ - 1 = -γ by ring, show 1 + ν - 1 = ν by ring] at h0
  rw [div_eq_iff hCg.ne']
  field_simp at h0
  linear_combination (-1) * h0

/-! ### Solving `MRS = MPN/m` -/

/-- The output solving `MRS = MPN/m`: `((1 − α)/(mχ))^{(1−α)/D} A^{(1+ν)/D}`,
`D = γ(1 − α) + α + ν` (Miao, (19.18); `m = 1` is the efficient output `Y^e`). -/
noncomputable def mpYout (α γ ν χ m A : ℝ) : ℝ :=
  ((1 - α) / (m * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν)) *
    A ^ ((1 + ν) / (γ * (1 - α) + α + ν))

/-- Miao, p. 631: for `A, N, χ, m > 0`, `α < 1`, `D = γ(1 − α) + α + ν ≠ 0`, the condition
`χN^ν = (AN^{1−α})^{−γ}(1 − α)AN^{−α}/m` holds iff
`ln N = (ln((1 − α)/(mχ)) + (1 − γ)ln A)/D`; in particular it has exactly one solution. -/
theorem mp_mrs_iff_log {α γ ν χ m A N : ℝ} (hα : α < 1) (hχ : 0 < χ) (hm : 0 < m) (hA : 0 < A)
    (hN : 0 < N) (hD : γ * (1 - α) + α + ν ≠ 0) :
    χ * N ^ ν = (A * N ^ (1 - α)) ^ (-γ) * ((1 - α) * A * N ^ (-α)) / m ↔
      Real.log N = (Real.log ((1 - α) / (m * χ)) + (1 - γ) * Real.log A) /
        (γ * (1 - α) + α + ν) := by
  have h1a : 0 < 1 - α := by linarith
  have hNa := Real.rpow_pos_of_pos hN (1 - α)
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA hNa
  have hL : 0 < χ * N ^ ν := mul_pos hχ (Real.rpow_pos_of_pos hN _)
  have hR : 0 < (A * N ^ (1 - α)) ^ (-γ) * ((1 - α) * A * N ^ (-α)) / m :=
    div_pos (mul_pos (Real.rpow_pos_of_pos hC _)
      (mul_pos (mul_pos h1a hA) (Real.rpow_pos_of_pos hN _))) hm
  rw [← Real.log_injOn_pos.eq_iff hL hR]
  rw [Real.log_mul hχ.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN,
    Real.log_div (ne_of_gt (mul_pos (Real.rpow_pos_of_pos hC _)
      (mul_pos (mul_pos h1a hA) (Real.rpow_pos_of_pos hN _)))) hm.ne',
    Real.log_mul (Real.rpow_pos_of_pos hC _).ne'
      (mul_pos (mul_pos h1a hA) (Real.rpow_pos_of_pos hN _)).ne',
    Real.log_rpow hC, Real.log_mul hA.ne' hNa.ne', Real.log_rpow hN,
    Real.log_mul (mul_pos h1a hA).ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN,
    Real.log_mul h1a.ne' hA.ne', Real.log_div h1a.ne' (mul_pos hm hχ).ne',
    Real.log_mul hm.ne' hχ.ne', eq_div_iff hD]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- **Output under `MRS = MPN/m`** (Miao, p. 631 and (19.18)): if `ln N` solves the condition of
`mp_mrs_iff_log`, then `Y = AN^{1−α} = mpYout`. -/
theorem mp_mrs_output {α γ ν χ m A N : ℝ} (hα : α < 1) (hχ : 0 < χ) (hm : 0 < m) (hA : 0 < A)
    (hN : 0 < N) (hD : γ * (1 - α) + α + ν ≠ 0)
    (h : χ * N ^ ν = (A * N ^ (1 - α)) ^ (-γ) * ((1 - α) * A * N ^ (-α)) / m) :
    A * N ^ (1 - α) = mpYout α γ ν χ m A := by
  have hlog := (mp_mrs_iff_log hα hχ hm hA hN hD).1 h
  have h1a : 0 < 1 - α := by linarith
  have hk : 0 < (1 - α) / (m * χ) := div_pos h1a (mul_pos hm hχ)
  rw [mpYout, Real.rpow_def_of_pos hk, Real.rpow_def_of_pos hA, ← Real.exp_add,
    Real.rpow_def_of_pos hN, ← Real.exp_log hA, ← Real.exp_add, Real.log_exp, hlog]
  congr 1
  have hDi : (γ * (1 - α) + α + ν) * (γ * (1 - α) + α + ν)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  linear_combination (-Real.log A) * hDi

/-! ### The employment subsidy -/

/-- **The employment subsidy** (Miao, p. 631). With `μ = ε/(ε − 1)` (`ε > 1`), the subsidy
`τ = 1/ε` gives `(1 − τ)μ = 1`, so the firm's condition `(1 − τ)W/P = MPN/μ` becomes
`W/P = MPN`; conversely `(1 − τ)μ = 1` forces `τ = 1/ε`. -/
theorem mp_subsidy {ε τ w mpn : ℝ} (hε : 1 < ε) :
    ((1 - τ) * (ε / (ε - 1)) = 1 ↔ τ = 1 / ε) ∧
      (τ = 1 / ε → (1 - τ) * w = mpn / (ε / (ε - 1)) → w = mpn) := by
  have h0 : ε ≠ 0 := by linarith
  have h1 : ε - 1 ≠ 0 := by linarith
  have key : (1 - τ) * (ε / (ε - 1)) = 1 ↔ τ = 1 / ε := by
    constructor
    · intro h
      field_simp at h ⊢
      linarith
    · intro h
      rw [h]
      field_simp
  refine ⟨key, fun hτ hw => ?_⟩
  have hk := key.2 hτ
  have hμ : ε / (ε - 1) ≠ 0 := div_ne_zero h0 h1
  rw [eq_div_iff hμ] at hw
  linear_combination hw - w * hk

/-- **Footnote 6** (Miao, p. 631): if the subsidy `τ_h` is paid to the household, the household's
condition `MRS = (1 + τ_h)W/P` and the firm's `W/P = MPN/μ` give `MRS = MPN` (for `MPN ≠ 0`) iff
`τ_h = 1/(ε − 1)`. -/
theorem mp_subsidy_household {ε τh mpn mrs w : ℝ} (hε : 1 < ε) (hmpn : mpn ≠ 0)
    (hhh : mrs = (1 + τh) * w) (hfirm : w = mpn / (ε / (ε - 1))) :
    mrs = mpn ↔ τh = 1 / (ε - 1) := by
  have h0 : ε ≠ 0 := by linarith
  have h1 : ε - 1 ≠ 0 := by linarith
  rw [hhh, hfirm]
  have e : (1 + τh) * (mpn / (ε / (ε - 1))) = mpn * ((1 + τh) * (ε - 1) / ε) := by
    field_simp
  rw [e]
  constructor
  · intro h
    have hk : (1 + τh) * (ε - 1) / ε = 1 := mul_left_cancel₀ hmpn (by rw [h, mul_one])
    rw [div_eq_one_iff_eq h0] at hk
    rw [eq_div_iff h1]
    linear_combination hk
  · intro h
    have hk : (1 + τh) * (ε - 1) / ε = 1 := by
      rw [h, div_eq_one_iff_eq h0]
      field_simp
      ring
    rw [hk, mul_one]

/-- Miao, p. 631: with the subsidy `τ = 1/ε` the flexible-price condition `MRS = MPN/((1 − τ)μ)`
is the efficient one, so flexible-price output is the efficient output `Y^e = mpYout … 1 …`. -/
theorem mp_flex_subsidy_efficient {α γ ν χ ε A : ℝ} (hε : 1 < ε) :
    mpYout α γ ν χ ((1 - 1 / ε) * (ε / (ε - 1))) A = mpYout α γ ν χ 1 A := by
  rw [((mp_subsidy (τ := 1 / ε) (w := 0) (mpn := 0) hε).1).2 rfl]

/-- **The steady-state distortion `Φ`** (Miao, p. 634). In the flexible-price equilibrium with
subsidy `τ` (household `MRS = W/P`, firm `(1 − τ)W/P = MPN/μ`, `(1 − τ)μ ≠ 0`),
`MRS = MPN(1 − Φ)` with `Φ = 1 − 1/((1 − τ)μ)`; `Φ = 0` iff `τ = 1/ε`. -/
theorem mp_distortion {ε τ w mpn mrs : ℝ} (hε : 1 < ε) (hτ : (1 - τ) * (ε / (ε - 1)) ≠ 0)
    (hhh : mrs = w) (hfirm : (1 - τ) * w = mpn / (ε / (ε - 1))) :
    mrs = mpn * (1 - (1 - 1 / ((1 - τ) * (ε / (ε - 1))))) ∧
      (1 - 1 / ((1 - τ) * (ε / (ε - 1))) = 0 ↔ τ = 1 / ε) := by
  have h0 : ε ≠ 0 := by linarith
  have h1 : ε - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [hhh, sub_sub_cancel, mul_one_div, eq_div_iff hτ]
    rw [eq_div_iff (div_ne_zero h0 h1)] at hfirm
    linear_combination hfirm
  · rw [← (mp_subsidy (w := 0) (mpn := 0) hε).1, sub_eq_zero, eq_comm, div_eq_one_iff_eq hτ,
      eq_comm]

/-- Miao, p. 634 ("`ŷ^f_t = (1 + ν)/(γ(1 − α) + ν + α) a_t`"): log flexible-price (or efficient)
output is affine in `ln A` with slope `(1 + ν)/D`. -/
theorem mp_yf_loglinear {α γ ν χ m A A' : ℝ} (hα : α < 1) (hχ : 0 < χ) (hm : 0 < m)
    (hA : 0 < A) (hA' : 0 < A') :
    Real.log (mpYout α γ ν χ m A) - Real.log (mpYout α γ ν χ m A') =
      (1 + ν) / (γ * (1 - α) + α + ν) * (Real.log A - Real.log A') := by
  have hk : 0 < (1 - α) / (m * χ) := div_pos (by linarith) (mul_pos hm hχ)
  simp only [mpYout]
  rw [Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hA _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hA' _).ne',
    Real.log_rpow hk, Real.log_rpow hA, Real.log_rpow hA']
  ring

/-- `x* = Φ(1 − α)/(γ(1 − α) + ν + α)` (Miao, p. 634). -/
noncomputable def mpXstar (α γ ν Φ : ℝ) : ℝ := Φ * (1 - α) / (γ * (1 - α) + ν + α)

/-- **`x*` and the efficiency gap** (Miao, p. 634). With the effective markup
`m = (1 − τ)μ = 1/(1 − Φ)` (`Φ < 1`), `ln(Y^e/Y^f) = −((1 − α)/D)ln(1 − Φ)`, and for `|Φ| ≤ 1/2`
it differs from `x*` by at most `2((1 − α)/D)Φ²`: `x*` is `ln(Y^e/Y^f)` to first order. -/
theorem mp_xstar_first_order {α γ ν χ Φ A : ℝ} (hα : α < 1) (hχ : 0 < χ) (hA : 0 < A)
    (hD : 0 < γ * (1 - α) + ν + α) (hΦ : |Φ| ≤ 1 / 2) :
    Real.log (mpYout α γ ν χ 1 A / mpYout α γ ν χ (1 / (1 - Φ)) A) =
        -((1 - α) / (γ * (1 - α) + ν + α)) * Real.log (1 - Φ) ∧
      |Real.log (mpYout α γ ν χ 1 A / mpYout α γ ν χ (1 / (1 - Φ)) A) - mpXstar α γ ν Φ| ≤
        2 * ((1 - α) / (γ * (1 - α) + ν + α)) * Φ ^ 2 := by
  have h1a : 0 < 1 - α := by linarith
  have hΦ1 : 0 < 1 - Φ := by have := (abs_le.1 hΦ).2; linarith
  have hm : 0 < 1 / (1 - Φ) := by positivity
  have hk1 : 0 < (1 - α) / (1 * χ) := div_pos h1a (by linarith)
  have hk2 : 0 < (1 - α) / (1 / (1 - Φ) * χ) := div_pos h1a (mul_pos hm hχ)
  have hD' : γ * (1 - α) + α + ν = γ * (1 - α) + ν + α := by ring
  have heq : Real.log (mpYout α γ ν χ 1 A / mpYout α γ ν χ (1 / (1 - Φ)) A) =
      -((1 - α) / (γ * (1 - α) + ν + α)) * Real.log (1 - Φ) := by
    simp only [mpYout]
    rw [Real.log_div (mul_pos (Real.rpow_pos_of_pos hk1 _) (Real.rpow_pos_of_pos hA _)).ne'
        (mul_pos (Real.rpow_pos_of_pos hk2 _) (Real.rpow_pos_of_pos hA _)).ne',
      Real.log_mul (Real.rpow_pos_of_pos hk1 _).ne' (Real.rpow_pos_of_pos hA _).ne',
      Real.log_mul (Real.rpow_pos_of_pos hk2 _).ne' (Real.rpow_pos_of_pos hA _).ne',
      Real.log_rpow hk1, Real.log_rpow hk2, Real.log_div h1a.ne' (by positivity),
      Real.log_div h1a.ne' (mul_pos hm hχ).ne', one_mul,
      Real.log_mul hm.ne' hχ.ne', one_div, Real.log_inv, hD']
    ring
  refine ⟨heq, ?_⟩
  rw [heq, mpXstar]
  have hl : |(∑ i ∈ Finset.range 1, Φ ^ (i + 1) / (i + 1)) + Real.log (1 - Φ)| ≤
      |Φ| ^ (1 + 1) / (1 - |Φ|) :=
    Real.abs_log_sub_add_sum_range_le (by linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_zero, pow_one,
    div_one] at hl
  have hb : |Φ| ^ 2 / (1 - |Φ|) ≤ 2 * Φ ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [sq_nonneg Φ]
  have hc : 0 ≤ (1 - α) / (γ * (1 - α) + ν + α) := div_nonneg h1a.le hD.le
  have : -((1 - α) / (γ * (1 - α) + ν + α)) * Real.log (1 - Φ) -
      Φ * (1 - α) / (γ * (1 - α) + ν + α) =
      -((1 - α) / (γ * (1 - α) + ν + α)) * (Φ + Real.log (1 - Φ)) := by ring
  rw [this, abs_mul, abs_neg, abs_of_nonneg hc]
  calc (1 - α) / (γ * (1 - α) + ν + α) * |Φ + Real.log (1 - Φ)|
      ≤ (1 - α) / (γ * (1 - α) + ν + α) * (2 * Φ ^ 2) :=
        mul_le_mul_of_nonneg_left (hl.trans hb) hc
    _ = 2 * ((1 - α) / (γ * (1 - α) + ν + α)) * Φ ^ 2 := by ring

end Miao.NewKeynesian
