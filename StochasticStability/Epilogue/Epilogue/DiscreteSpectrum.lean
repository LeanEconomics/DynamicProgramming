/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.SpectralGap

/-!
# A drift criterion for a discrete spectrum (MT §20.1.4, Propositions 20.1.4–20.1.5)

Meyn and Tweedie, pp. 517–518.

* `nonlinGen` (20.10): the nonlinear generator `H(G) = log(Pe^G/e^G)`; `DriftDV3` (20.11): the
  Donsker–Varadhan condition `Pe^V ≤ exp(−δf + b 1_C) e^V`; `driftDV3_iff_nonlinGen`: the two
  forms agree (`H(V) ≤ −δf + b 1_C`).
* `driftV4_of_driftDV3` (p. 517, corrected): (DV3) with `f ≥ 1` and `V ≤ M` on `C` gives (V4)
  for `e^V` with `1 − β = e^{−δ}` and `b' = e^b e^M`.
* `truncKernel` (`P̂ₙ = I_{C_f(n)}P`); **Proposition 20.1.4** (`proposition_20_1_4`, p. 518):
  `|||P − P̂ₙ|||_v ≤ e^{−δn}` whenever `C ⊆ C_f(n)`, so `|||P − P̂ₙ|||_v → 0`, `v = e^V`.
* **Proposition 20.1.5, the part proved here** (`proposition_20_1_5_compact`, p. 518): on a
  countable space with `f` coercive and `C` finite, the `P̂ₙ` are operators of finite rank on
  `L∞_v` (`suppSub`, `finiteDimensional_suppSub`) converging to `P` in operator norm, so `P` is a
  compact operator (`isCompactOperator_of_finiteDimensional_range`, Mathlib's
  `isCompactOperator_of_tendsto`), and every nonzero point of `S_v(P)` is an eigenvalue (Mathlib's
  Fredholm alternative `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`).

**Correction.** On p. 517 the constant of the (V4) bound derived from (DV3) is given as
`b' = b + sup_C e^V`; it must be `b' = e^b sup_C e^V` (or any larger constant).
`driftV4_of_driftDV3_book_counterexample`: the swap chain on `{0, 1}` with `C = {0}`, `f ≡ 1`,
`δ = 1`, `b = 4`, `V(0) = 0`, `V(1) = 3` satisfies (DV3), but `∆e^V(0) = e³ − 1 > 5 − β`.

**Elsewhere.** The remaining step of Proposition 20.1.5 — that a norm limit of finite-rank
operators has a discrete spectrum (finitely many points in `|z| ≥ ε`, each a pole of finite
multiplicity), Theorem 3.5 of Kontoyiannis–Meyn [219] — is the Riesz–Schauder theory of compact
operators, proved in `CompactSpectrum` (`proposition_20_1_5`). Hypotheses: `V` is real-valued
(the book allows `V = ∞`), `V ≥ 0` and `f ≥ 1` as in (DV3).
-/
namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The nonlinear generator and (DV3) -/

/-- **The nonlinear generator** (20.10), MT p. 517: `H(G) = log(Pe^G / e^G)`. -/
noncomputable def nonlinGen (P : Kernel X X) (G : X → ℝ) (x : X) : ℝ :=
  Real.log ((∫ y, Real.exp (G y) ∂P x) / Real.exp (G x))

/-- **The drift condition (DV3)** of Donsker and Varadhan (20.11), MT p. 517, in the
multiplicative form `Pe^V ≤ exp(−δf + b 1_C) e^V` (for finite `V ≥ 0`). -/
def DriftDV3 (P : Kernel X X) (V f : X → ℝ) (δ b : ℝ) (C : Set X) : Prop :=
  ∀ x, ∫⁻ y, ENNReal.ofReal (Real.exp (V y)) ∂P x ≤
    ENNReal.ofReal (Real.exp (-δ * f x + b * C.indicator 1 x + V x))

/-- **(20.11) in terms of the nonlinear generator**: when `e^V` is `P(x, ·)`-integrable,
`H(V) ≤ −δf + b 1_C` is (DV3). -/
theorem driftDV3_iff_nonlinGen (P : Kernel X X) [IsMarkovKernel P] {V f : X → ℝ}
    (hint : ∀ x, Integrable (fun y => Real.exp (V y)) (P x)) {δ b : ℝ}
    {C : Set X} :
    DriftDV3 P V f δ b C ↔ ∀ x, nonlinGen P V x ≤ -δ * f x + b * C.indicator 1 x := by
  have hpos : ∀ x, 0 < ∫ y, Real.exp (V y) ∂P x := fun x =>
    integral_exp_pos (hint x)
  have hlin : ∀ x, ∫⁻ y, ENNReal.ofReal (Real.exp (V y)) ∂P x =
      ENNReal.ofReal (∫ y, Real.exp (V y) ∂P x) := fun x =>
    (ofReal_integral_eq_lintegral_ofReal (hint x)
      (Eventually.of_forall fun y => (Real.exp_pos _).le)).symm
  refine forall_congr' fun x => ?_
  rw [hlin, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, nonlinGen,
    Real.log_le_iff_le_exp (div_pos (hpos x) (Real.exp_pos _)),
    div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]

/-- **(DV3) implies a version of (V4)** for `e^V` (MT p. 517), corrected: if `f ≥ 1` and
`V ≤ M` on `C`, then `Pe^V ≤ e^{−δ} e^V + e^b e^M 1_C`, i.e. (V4) with `1 − β = e^{−δ}` and
`b' = e^b sup_C e^V`. -/
theorem driftV4_of_driftDV3 {P : Kernel X X} {V f : X → ℝ} {δ b M : ℝ} {C : Set X}
    (hδ : 0 < δ) (hf : ∀ x, 1 ≤ f x) (hVC : ∀ x ∈ C, V x ≤ M)
    (h : DriftDV3 P V f δ b C) :
    DriftV4 P (fun x => ENNReal.ofReal (Real.exp (V x))) (ENNReal.ofReal (Real.exp (-δ)))
      (ENNReal.ofReal (Real.exp b * Real.exp M)) C := by
  intro x
  refine (h x).trans ?_
  by_cases hx : x ∈ C
  · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, mul_one]
    refine le_trans ?_ le_add_self
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := hVC x hx
    nlinarith [hf x]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero, add_zero, add_zero,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith [hf x]

/-- The deterministic swap `0 ↔ 1` on `Bool`, the counterexample chain for the constant `b'`. -/
noncomputable def swapKernel : Kernel Bool Bool :=
  Kernel.deterministic not (measurable_of_countable _)

/-- **The constant `b' = b + sup_C e^V` of p. 517 is wrong.** For the swap chain, `C = {false}`,
`f ≡ 1`, `δ = 1`, `b = 4`, `V(false) = 0`, `V(true) = 3`, (DV3) holds, but at `x = false`,
`∆e^V = e³ − 1 > −β e^0 + b + sup_C e^V = 5 − β` with `1 − β = e^{−1}`. -/
theorem driftV4_of_driftDV3_book_counterexample :
    DriftDV3 swapKernel (fun x => if x then 3 else 0) (fun _ => 1) 1 4 {false} ∧
      ¬ (Real.exp 3 - Real.exp 0 ≤ -(1 - Real.exp (-1)) * Real.exp 0 + (4 + Real.exp 0)) := by
  have he1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  have he3 : 8 ≤ Real.exp 3 := by
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
      _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
  refine ⟨fun x => ?_, ?_⟩
  · rw [swapKernel, Kernel.deterministic_apply,
      lintegral_dirac' _ (measurable_of_countable _)]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    cases x <;> simp only [Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true, indicator_of_mem (mem_singleton false), Pi.one_apply,
      indicator_of_notMem (show true ∉ ({false} : Set Bool) by decide)] <;> norm_num
  · rw [Real.exp_zero]
    linarith

/-! ### Proposition 20.1.4: truncation -/

/-- **The truncated kernel** `P̂ₙ = I_{C_f(n)} P` (MT p. 518), `C_f(n) = {f ≤ n}`. -/
noncomputable def truncKernel (P : Kernel X X) {f : X → ℝ} (hf : Measurable f) (n : ℝ) :
    Kernel X X :=
  Kernel.piecewise (s := {x | f x ≤ n})
    (measurableSet_le hf (measurable_const : Measurable fun _ : X => n)) P 0

/-- **Proposition 20.1.4** (MT p. 518): under (DV3), whenever `C ⊆ C_f(n)`,
`|||P − P̂ₙ|||_v ≤ e^{−δn}` with `v = e^V`; hence `|||P − P̂ₙ|||_v → 0` when `C ⊆ C_f(n)` for all
large `n`. -/
theorem proposition_20_1_4 {P : Kernel X X} {V f : X → ℝ} (hf : Measurable f) {δ b : ℝ}
    {C : Set X} (hδ : 0 < δ) (h : DriftDV3 P V f δ b C) :
    (∀ n : ℕ, C ⊆ {x | f x ≤ n} →
      vOpNorm (fun x => ENNReal.ofReal (Real.exp (V x))) P (truncKernel P hf n) ≤
        ENNReal.ofReal (Real.exp (-δ * n))) ∧
      ((∃ N : ℕ, ∀ n ≥ N, C ⊆ {x | f x ≤ n}) →
        Tendsto (fun n : ℕ =>
          vOpNorm (fun x => ENNReal.ofReal (Real.exp (V x))) P (truncKernel P hf n))
          atTop (𝓝 0)) := by
  have hbound : ∀ n : ℕ, C ⊆ {x | f x ≤ n} →
      vOpNorm (fun x => ENNReal.ofReal (Real.exp (V x))) P (truncKernel P hf n) ≤
        ENNReal.ofReal (Real.exp (-δ * n)) := fun n hC => by
    refine vOpNorm_le fun x => ?_
    rw [truncKernel, Kernel.piecewise_apply]
    by_cases hx : x ∈ {x | f x ≤ (n : ℝ)}
    · rw [ite_eq_left hx, fNorm_self]; exact zero_le
    · rw [ite_eq_right hx, zero_apply]
      refine (fNorm_le_add _ _ _).trans ?_
      rw [lintegral_zero_measure, add_zero]
      have hxC : x ∉ C := fun hc => hx (hC hc)
      have hfx : (n : ℝ) < f x := not_le.1 hx
      refine (h x).trans ?_
      rw [indicator_of_notMem hxC, mul_zero, add_zero, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      nlinarith
  refine ⟨hbound, fun ⟨N, hN⟩ => ?_⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-δ * n))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have : Tendsto (fun n : ℕ => -δ * (n : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
    exact Real.tendsto_exp_atBot.comp this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop N] with n hn using hbound n (hN n hn)


/-! ### Proposition 20.1.5: finite-rank approximation and compactness -/

/-- An operator of finite rank is compact. -/
theorem isCompactOperator_of_finiteDimensional_range {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : E →L[ℂ] E)
    (hT : FiniteDimensional ℂ (LinearMap.range (T : E →ₗ[ℂ] E))) : IsCompactOperator T := by
  set W := LinearMap.range (T : E →ₗ[ℂ] E)
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have hK : IsCompact ((Subtype.val : W → E) '' Metric.closedBall (0 : W) ‖T‖) :=
    (isCompact_closedBall _ _).image continuous_subtype_val
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[ℂ] E)
    one_pos).2 (hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed))
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨T x, LinearMap.mem_range_self _ x⟩, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖T x‖ ≤ ‖T‖
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖T‖ := mul_one _

/-- The functions in `L∞_V` vanishing off `S` (weighted coordinates). -/
def suppSub (S : Set X) : Submodule ℂ (BM X) where
  carrier := {g | ∀ x ∉ S, bmFun g x = 0}
  add_mem' {g h} hg hh x hx := by rw [bmFun_add, hg x hx, hh x hx, add_zero]
  zero_mem' x _ := bmFun_zero x
  smul_mem' c g hg x hx := by rw [bmFun_smul, hg x hx, mul_zero]

/-- Functions supported on a finite set form a finite-dimensional space. -/
theorem finiteDimensional_suppSub {S : Set X} (hS : S.Finite) :
    FiniteDimensional ℂ (suppSub (X := X) S) := by
  have : Finite S := hS.to_subtype
  let r : suppSub (X := X) S →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun g s => bmFun (g : BM X) s
      map_add' := fun g h => funext fun s => bmFun_add _ _ _
      map_smul' := fun c g => funext fun s => bmFun_smul _ _ _ }
  refine FiniteDimensional.of_injective r fun g h hgh => Subtype.ext (bm_ext fun x => ?_)
  by_cases hx : x ∈ S
  · exact congrFun hgh ⟨x, hx⟩
  · rw [g.2 x hx, h.2 x hx]

variable [Countable X] [MeasurableSingletonClass X] in
/-- **Proposition 20.1.5, the finite-rank approximation** (MT p. 518): on a countable space,
under (DV3) with `f` coercive (finite sublevel sets), `C` finite and `V ≥ 0`, the truncations
`P̂ₙ` act on `L∞_v`, `v = e^V`, as operators of finite rank converging to `P` in operator norm,
so `P` is a compact operator on `L∞_v`; by the Fredholm alternative (Mathlib) every nonzero point
of `S_v(P)` is an eigenvalue. -/
theorem proposition_20_1_5_compact {P : Kernel X X} [IsMarkovKernel P] {V f : X → ℝ}
    {δ b : ℝ} {C : Set X} (hδ : 0 < δ) (hV0 : ∀ x, 0 ≤ V x) (hf1 : ∀ x, 1 ≤ f x)
    (hcoer : ∀ n : ℝ, {x | f x ≤ n}.Finite) (hC : C.Finite) (h : DriftDV3 P V f δ b C) :
    (∀ n : ℕ, FiniteDimensional ℂ (LinearMap.range
      (kOp (fun x => Real.exp (V x)) (truncKernel P (measurable_of_countable f) n) :
        BM X →ₗ[ℂ] BM X))) ∧
      Tendsto (fun n : ℕ => kOp (fun x => Real.exp (V x))
        (truncKernel P (measurable_of_countable f) n)) atTop
        (𝓝 (kOp (fun x => Real.exp (V x)) P)) ∧
      IsCompactOperator (kOp (fun x => Real.exp (V x)) P) ∧
      ∀ z ∈ spectrumV (fun x => Real.exp (V x)) P, z ≠ 0 →
        Module.End.HasEigenvalue
          (kOp (fun x => Real.exp (V x)) P : Module.End ℂ (BM X)) z := by
  have := completeSpace_BM (X := X)
  have hf : Measurable f := measurable_of_countable f
  have hv1 : ∀ x, 1 ≤ Real.exp (V x) := fun x => Real.one_le_exp (hV0 x)
  have hvm : Measurable fun x => Real.exp (V x) := measurable_of_countable _
  have hc : ∀ x, ∫⁻ y, ENNReal.ofReal (Real.exp (V y)) ∂P x ≤
      ENNReal.ofReal (Real.exp |b| * Real.exp (V x)) := fun x =>
    (h x).trans (ENNReal.ofReal_le_ofReal (by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 : b * C.indicator 1 x ≤ |b| := by
        by_cases hx : x ∈ C
        · rw [indicator_of_mem hx, Pi.one_apply, mul_one]; exact le_abs_self b
        · rw [indicator_of_notMem hx, mul_zero]; exact abs_nonneg b
      nlinarith [hf1 x]))
  have hWP : WeightOK (fun x => Real.exp (V x)) P := ⟨hvm, hv1, _, (Real.exp_pos _).le, hc⟩
  have hWT : ∀ n : ℕ, WeightOK (fun x => Real.exp (V x)) (truncKernel P hf n) := fun n =>
    ⟨hvm, hv1, _, (Real.exp_pos _).le, fun x => by
      rw [truncKernel, Kernel.piecewise_apply]
      by_cases hx : x ∈ {x | f x ≤ (n : ℝ)}
      · rw [ite_eq_left hx]; exact hc x
      · rw [ite_eq_right hx, zero_apply, lintegral_zero_measure]; exact zero_le⟩
  have hfin : ∀ n : ℕ, FiniteDimensional ℂ (LinearMap.range
      (kOp (fun x => Real.exp (V x)) (truncKernel P hf n) : BM X →ₗ[ℂ] BM X)) := fun n => by
    have : FiniteDimensional ℂ (suppSub (X := X) {x | f x ≤ (n : ℝ)}) :=
      finiteDimensional_suppSub (hcoer n)
    refine Submodule.finiteDimensional_of_le (S₂ := suppSub {x | f x ≤ (n : ℝ)}) ?_
    rintro _ ⟨g, rfl⟩ x hx
    change bmFun (kOp (fun x => Real.exp (V x)) (truncKernel P hf n) g) x = 0
    rw [kOp_apply (hWT n), kFun, truncKernel, Kernel.piecewise_apply, ite_eq_right hx,
      zero_apply, integral_zero_measure, mul_zero]
  obtain ⟨M, hM⟩ := (hC.image f).bddAbove
  set N := ⌈M⌉₊
  have hCN : ∀ n ≥ N, C ⊆ {x | f x ≤ (n : ℝ)} := fun n hn x hx =>
    (hM ⟨x, hx, rfl⟩).trans ((Nat.le_ceil M).trans (by exact_mod_cast hn))
  have hnorm : ∀ n ≥ N, ‖kOp (fun x => Real.exp (V x)) (truncKernel P hf n) -
      kOp (fun x => Real.exp (V x)) P‖ ≤ 2 * Real.exp (-δ * n) := fun n hn => by
    refine (norm_sub_rev (kOp (fun x => Real.exp (V x)) (truncKernel P hf n))
      (kOp (fun x => Real.exp (V x)) P)).trans_le ?_
    refine norm_kOp_sub_le hWP (hWT n) (Real.exp_pos _).le fun x => ?_
    have h1 := (proposition_20_1_4 hf hδ h).1 n (hCN n hn)
    have h2 := fNorm_le_vOpNorm_mul (V := fun x => ENNReal.ofReal (Real.exp (V x))) P
      (truncKernel P hf n) (x := x) (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact h2.trans (mul_le_mul' h1 le_rfl)
  have htend : Tendsto (fun n : ℕ => kOp (fun x => Real.exp (V x)) (truncKernel P hf n)) atTop
      (𝓝 (kOp (fun x => Real.exp (V x)) P)) := by
    refine (tendsto_iff_norm_sub_tendsto_zero (b := kOp (fun x => Real.exp (V x)) P)).2 ?_
    have hlim : Tendsto (fun n : ℕ => 2 * Real.exp (-δ * n)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => -δ * (n : ℝ)) atTop atBot :=
        tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
      have := (Real.tendsto_exp_atBot.comp this).const_mul 2
      rwa [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop N] with n hn using hnorm n hn
  have hcomp : IsCompactOperator (kOp (fun x => Real.exp (V x)) P) :=
    isCompactOperator_of_tendsto htend (Eventually.of_forall fun n =>
      isCompactOperator_of_finiteDimensional_range _ (hfin n))
  exact ⟨hfin, htend, hcomp, fun z hz hz0 => (hcomp.hasEigenvalue_iff_mem_spectrum hz0).2 hz⟩

end MeynTweedie.Epilogue
