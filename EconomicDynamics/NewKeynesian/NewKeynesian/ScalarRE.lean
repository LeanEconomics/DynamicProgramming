/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.CondExpL1
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation

/-!
# Scalar linear rational expectations models

Copied from `EconomicDynamics/RationalExpectations` (module `ScalarRE`), namespace renamed.

Miao, §2.2, pp. 48–52. Abstract setting: a `CondExpSystem ℝ V` on a complete normed space `V`
of scalar random variables (for instance `condExpSystemL1_real`); a process is `x : ℕ → V`,
adapted if `E_t x_t = x_t` (`sre_IsAdapted`), stable if bounded (`sre_IsBounded`, which is
Definition 2.3.1 for one variable, `sre_isStableProc_iff`).

* Lag operators (p. 48): `L^{-j}X_t = E_tX_{t+j}` (`sre_lagInv`), the rule
  `LʲE_tX_{t+i} = E_tX_{t+i−j}` (`sre_lagE`), `LʲE_tX_{t+j} = X_t` (`sre_lagE_self`),
  `L^{-i}L^{-j} = L^{-(i+j)}` (`sre_lagInv_lagInv`, law of iterated expectations).
* `E_tx_{t+1} = bx_t + f_t`, `|b| > 1`, `f` bounded adapted: the forward solution
  `x*_t = −∑ⱼ b^{−j−1}E_tf_{t+j}` (`sre_fwd`) converges, is adapted, bounded and solves
  (`sre_fwd_adapted`, `sre_fwd_bound`, `sre_fwd_rec`); with `f = cz` this is (2.3) (`eq_2_3`).
  It is the only stable adapted solution (`eq_2_3_unique`). Bubbles (2.4): `x* + B` solves iff
  `E_tB_{t+1} = bB_t`, and every adapted solution is of this form (`eq_2_4`,
  `eq_2_4_every`). The transversality condition (2.5) holds for every stable process
  (`eq_2_5_of_bounded`), forces `x = x*` (`eq_2_5_rules_out_bubbles`) and fails for every
  nonzero adapted bubble (`eq_2_5_bubble_fails`).
* Example 2.2.1 (Blanchard–Watson): `E_td_{t+j} = ρʲd_t` (`example_2_2_1_Ed`), the fundamental
  price `d_t/(R − ρ)` (`example_2_2_1_fundamental`, `example_2_2_1_general`); the bursting
  bubble satisfies (2.4) (`example_2_2_1_bubble`, concrete: functions on `Ω` with `μ[·|ℱ t]`;
  `example_2_2_1_bubble_L1` in `L¹`), and the coin's conditional mean is `q` when it is
  independent of `ℱ_t` (`example_2_2_1_coin`).
* (2.6)–(2.9): with `a = λ₁ + λ₂`, `b = −λ₁λ₂`, `|λ₁| < 1 < |λ₂|`, the process
  `x_t = λ₁x_{t−1} − (c/λ₂)∑ⱼλ₂^{−j}E_tz_{t+j}` (`sre_second`, `eq_2_9`) is the unique stable
  adapted solution of (2.6) on the dates `t ≥ 1` with the given `x₀` (`eq_2_6_solution`,
  `eq_2_6_unique`).
* (2.10): the reduction (`eq_2_10_reduce`), and the book's recipe made precise: if `λ₁, λ₂` are
  the roots of `λ² = (a₀ + a₁)λ + a₂` with `|λ₁| < 1 < |λ₂|`, and `a₀ ≠ λ₁`, there is exactly
  one stable adapted solution with the given `x₀` (`eq_2_10_solution`, `eq_2_10_unique`); for
  `a₀ = λ₁` uniqueness fails (`eq_2_10_indeterminate`).
* §2.2.2 (p. 51): the guess `x_t = Gx_{t−1} + Hz_t` solves (2.6) iff a coefficient identity
  holds (`uc_iff`); matching coefficients is sufficient (`uc_sufficient`) and necessary when
  the guess works for two initial values and `z ≢ 0` (`uc_necessary`); with `G = λ₁`,
  `H = c/(G + ρ − a)` is well defined (`uc_denominator_ne_zero`) and the guess is the
  lag-operator solution (`uc_eq_lag_solution`).

Departures from the book (see the docstrings):
* "Bounded" in the book means Definition 2.3.1 (`sup_t E|z_t| < ∞`); all processes are
  explicitly adapted.
* (2.6) and (2.10) involve `x_{t−1}`, so they are imposed for `t ≥ 1` with `x₀` given.
* Example 2.2.1 and §2.2.2 assume `ε` IID with mean zero; what is used is only the
  martingale-difference property `E_tε_{t+1} = 0` (hence `E_td_{t+1} = ρd_t`).
* (2.10): the book says the reduced equation "is similar to (2.7)", but it contains `x_{t−1}`,
  not `E_{t−1}x_{t−1}`; the book's final step solves for `x_t` from (2.10), whose coefficient
  on `x_t` is `a₀ − λ₁` once `E_tx_{t+1} = λ₁x_t + ω_t` is substituted, so the condition is
  `a₀ ≠ λ₁` (not `a₀ ≠ 0`); for `a₀ = λ₁` there are sunspot solutions.
-/

open Filter Topology MeasureTheory

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Scalar processes -/

/-- A scalar process `x` is adapted: `E_tx_t = x_t` (Miao, p. 45). -/
def sre_IsAdapted (E : CondExpSystem ℝ V) (x : ℕ → V) : Prop :=
  ∀ t, E.E t (x t) = x t

/-- A scalar process is bounded (stable, Definition 2.3.1). -/
def sre_IsBounded (x : ℕ → V) : Prop :=
  ∃ M, ∀ t, ‖x t‖ ≤ M

omit [NormedSpace ℝ V] in
/-- **Definition 2.3.1** (Miao, p. 52) for one variable: stable iff bounded. -/
theorem sre_isStableProc_iff (x : ℕ → V) :
    IsStableProc (fun t (_ : Unit) => x t) ↔ sre_IsBounded x := by
  constructor
  · rintro ⟨M, -, hM⟩
    exact ⟨M, fun t => (hM t ()).le⟩
  · rintro ⟨M, hM⟩
    refine ⟨|M| + 1, by positivity, fun t _ => ?_⟩
    linarith [hM t, le_abs_self M]

theorem sre_isAdaptedV_iff (E : CondExpSystem ℝ V) (x : ℕ → V) :
    IsAdaptedV E (fun t (_ : Unit) => x t) ↔ sre_IsAdapted E x :=
  ⟨fun h t => h t (), fun h t _ => h t⟩

theorem sre_adapted_succ (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x)
    (t : ℕ) : E.E (t + 1) (x t) = x t := by
  rw [← hx t, E.tower_ge_apply (Nat.le_succ t), hx t]

theorem sre_adapted_le (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x)
    {s t : ℕ} (h : s ≤ t) : E.E t (x s) = x s := by
  rw [← hx s, E.tower_ge_apply h, hx s]

/-- The conditional expectations from date `k` on: `E'_t = E_{t+k}`. -/
def sre_shiftSys (E : CondExpSystem ℝ V) (k : ℕ) : CondExpSystem ℝ V where
  E t := E.E (t + k)
  norm_le t := E.norm_le (t + k)
  tower_le s t h := E.tower_le _ _ (by omega)
  tower_ge s t h := E.tower_ge _ _ (by omega)

theorem sre_shiftSys_E (E : CondExpSystem ℝ V) (k t : ℕ) :
    (sre_shiftSys E k).E t = E.E (t + k) := rfl

/-! ### Lag operators -/

/-- The inverse lag operator (Miao, p. 48): `L^{-j}X_t = E_tX_{t+j}`. -/
def sre_lagInv (E : CondExpSystem ℝ V) (j : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => E.E t (x (t + j))

/-- The lag operator (Miao, p. 48): `LʲX_t = X_{t−j}` (for `t ≥ j`). -/
def sre_lag (j : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => x (t - j)

/-- The rule of Miao, p. 48: `Lʲ` applied to `E_tX_{t+i}` is `E_tX_{t+i−j}` (for `j ≤ i`): the
lag shifts the date of the variable, not the date of the expectation. -/
def sre_lagE (E : CondExpSystem ℝ V) (j i : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => E.E t (x (t + i - j))

/-- Miao, p. 48: `LʲE_tX_{t+j} = E_tX_t = X_t` for an adapted `X`, which is why
`L^{-j}X_t = E_tX_{t+j}` is the inverse of `Lʲ`. -/
theorem sre_lagE_self (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x) (j : ℕ) :
    sre_lagE E j j x = x := by
  funext t
  simp only [sre_lagE, Nat.add_sub_cancel]
  exact hx t

/-- Miao, p. 48: `L⁰X = X` for adapted `X`. -/
theorem sre_lagInv_zero (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x) :
    sre_lagInv E 0 x = x := by
  funext t
  exact hx t

/-- Miao, p. 48: `L^{-i}L^{-j}X_t = E_tE_{t+i}X_{t+i+j} = L^{-(i+j)}X_t`. -/
theorem sre_lagInv_lagInv (E : CondExpSystem ℝ V) (i j : ℕ) (x : ℕ → V) :
    sre_lagInv E i (sre_lagInv E j x) = sre_lagInv E (i + j) x := by
  funext t
  simp only [sre_lagInv, Nat.add_assoc]
  exact E.tower_le_apply (Nat.le_add_right t i) _

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Miao, p. 48: lags compose additively, `Lⁱ(LʲX)_t = X_{t−i−j}`. -/
theorem sre_lag_lag (i j : ℕ) (x : ℕ → V) : sre_lag i (sre_lag j x) = sre_lag (i + j) x := by
  funext t
  simp only [sre_lag]
  congr 1
  omega

/-- Miao, p. 48: `E_tx_{t+1} = bx_t + cz_t` is `(L^{-1} − b)x_t = cz_t`. -/
theorem sre_lag_form (E : CondExpSystem ℝ V) (b c : ℝ) (x z : ℕ → V) :
    (∀ t, E.E t (x (t + 1)) = b • x t + c • z t) ↔
      sre_lagInv E 1 x - b • x = c • z := by
  constructor
  · intro h
    funext t
    simp only [Pi.sub_apply, Pi.smul_apply, sre_lagInv, h t]
    abel
  · intro h t
    have := congrFun h t
    simp only [Pi.sub_apply, Pi.smul_apply, sre_lagInv] at this
    rw [← this]
    abel

/-! ### The first-order equation `E_tx_{t+1} = bx_t + f_t` -/

/-- Iterating `E_te_{t+1} = be_t` with the law of iterated expectations:
`E_te_{t+k} = bᵏe_t`. -/
theorem sre_iter (E : CondExpSystem ℝ V) {b : ℝ} {e : ℕ → V} (he : sre_IsAdapted E e)
    (hrec : ∀ t, E.E t (e (t + 1)) = b • e t) (k t : ℕ) :
    E.E t (e (t + k)) = b ^ k • e t := by
  induction k with
  | zero => simpa using he t
  | succ k ih =>
    rw [← Nat.add_assoc, ← E.tower_le_apply (Nat.le_add_right t k), hrec, map_smul, ih,
      smul_smul, pow_succ, mul_comm]

/-- A bounded adapted solution of `E_te_{t+1} = be_t` with `|b| > 1` is zero. -/
theorem sre_bubble_bounded_zero (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {e : ℕ → V}
    (he : sre_IsAdapted E e) (hrec : ∀ t, E.E t (e (t + 1)) = b • e t)
    (hbd : sre_IsBounded e) : e = 0 := by
  obtain ⟨M, hM⟩ := hbd
  funext t
  by_contra hne
  have hpos : 0 < ‖e t‖ := norm_pos_iff.2 hne
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / ‖e t‖) hb
  have h1 : |b| ^ k * ‖e t‖ ≤ M := by
    calc |b| ^ k * ‖e t‖ = ‖E.E t (e (t + k))‖ := by
          rw [sre_iter E he hrec, norm_smul, norm_pow, Real.norm_eq_abs]
      _ ≤ ‖e (t + k)‖ := E.norm_apply_le _ _
      _ ≤ M := hM _
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-- Two bounded adapted solutions of `E_tx_{t+1} = bx_t + f_t`, `|b| > 1`, coincide. -/
theorem sre_unique_of_bounded (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f x y : ℕ → V}
    (hx : sre_IsAdapted E x) (hy : sre_IsAdapted E y) (hxb : sre_IsBounded x)
    (hyb : sre_IsBounded y) (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t)
    (hys : ∀ t, E.E t (y (t + 1)) = b • y t + f t) : x = y := by
  have h := sre_bubble_bounded_zero E hb (e := x - y)
    (fun t => by simp only [Pi.sub_apply, map_sub, hx t, hy t])
    (fun t => by simp only [Pi.sub_apply, map_sub, hxs, hys, smul_sub]; abel)
    (by
      obtain ⟨M, hM⟩ := hxb
      obtain ⟨N, hN⟩ := hyb
      exact ⟨M + N, fun t => (norm_sub_le _ _).trans (add_le_add (hM t) (hN t))⟩)
  exact funext fun t => sub_eq_zero.1 (congrFun h t)

/-- The forward (fundamental) solution `x*_t = −∑ⱼ b^{−j−1}E_tf_{t+j}` of
`E_tx_{t+1} = bx_t + f_t`. -/
noncomputable def sre_fwd (E : CondExpSystem ℝ V) (b : ℝ) (f : ℕ → V) : ℕ → V :=
  fun t => -∑' j : ℕ, (b⁻¹) ^ (j + 1) • E.E t (f (t + j))

theorem sre_inv_abs_lt_one {b : ℝ} (hb : 1 < |b|) : |b⁻¹| < 1 := by
  rw [abs_inv]
  exact inv_lt_one_of_one_lt₀ hb

/-- The terms of the forward sum are dominated by a geometric series. -/
theorem sre_fwd_term_le (E : CondExpSystem ℝ V) (b : ℝ) {f : ℕ → V} {M : ℝ}
    (hM : ∀ t, ‖f t‖ ≤ M) (t j : ℕ) :
    ‖(b⁻¹) ^ (j + 1) • E.E t (f (t + j))‖ ≤ M * |b⁻¹| * |b⁻¹| ^ j := by
  rw [norm_smul, norm_pow, Real.norm_eq_abs, pow_succ]
  calc |b⁻¹| ^ j * |b⁻¹| * ‖E.E t (f (t + j))‖ ≤ |b⁻¹| ^ j * |b⁻¹| * M := by
        gcongr
        exact (E.norm_apply_le _ _).trans (hM _)
    _ = M * |b⁻¹| * |b⁻¹| ^ j := by ring

theorem sre_fwd_summable [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f : ℕ → V} {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) (t : ℕ) :
    Summable fun j : ℕ => (b⁻¹) ^ (j + 1) • E.E t (f (t + j)) :=
  Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg _) (sre_inv_abs_lt_one hb)).mul_left _)
    (sre_fwd_term_le E b hM t)

/-- The forward solution is bounded: `‖x*_t‖ ≤ M|b|^{-1}/(1 − |b|^{-1})`. -/
theorem sre_fwd_bound (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f : ℕ → V} {M : ℝ}
    (hM : ∀ t, ‖f t‖ ≤ M) (t : ℕ) :
    ‖sre_fwd E b f t‖ ≤ M * |b⁻¹| * (1 - |b⁻¹|)⁻¹ := by
  rw [sre_fwd, norm_neg]
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (abs_nonneg _) (sre_inv_abs_lt_one hb)).mul_left _)
    (sre_fwd_term_le E b hM t)

theorem sre_fwd_isBounded (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f : ℕ → V}
    (hf : sre_IsBounded f) : sre_IsBounded (sre_fwd E b f) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨_, sre_fwd_bound E hb hM⟩

/-- The forward solution is adapted. -/
theorem sre_fwd_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f : ℕ → V} (hf : sre_IsBounded f) : sre_IsAdapted E (sre_fwd E b f) := by
  obtain ⟨M, hM⟩ := hf
  intro t
  simp only [sre_fwd, map_neg]
  rw [(E.E t).map_tsum (sre_fwd_summable E hb hM t)]
  simp only [map_smul, E.idem]

/-- The forward solution solves `E_tx_{t+1} = bx_t + f_t`. -/
theorem sre_fwd_rec [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) (t : ℕ) :
    E.E t (sre_fwd E b f (t + 1)) = b • sre_fwd E b f t + f t := by
  obtain ⟨M, hM⟩ := hf
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, abs_zero] at hb
    linarith
  have hs := sre_fwd_summable E hb hM t
  have hs1 := sre_fwd_summable E hb hM (t + 1)
  simp only [sre_fwd, map_neg]
  rw [(E.E t).map_tsum hs1, hs.tsum_eq_zero_add]
  simp only [map_smul, E.tower_le_apply (Nat.le_succ t), smul_neg, smul_add, Nat.add_zero,
    hfa t, zero_add, pow_one, smul_smul, mul_inv_cancel₀ hb0, one_smul]
  have hs2 : Summable fun j : ℕ => (b⁻¹) ^ (j + 1 + 1) • E.E t (f (t + (j + 1))) :=
    (summable_nat_add_iff 1).2 hs
  have h2 : (∑' j : ℕ, (b⁻¹) ^ (j + 1) • E.E t (f (t + 1 + j))) =
      b • ∑' j : ℕ, (b⁻¹) ^ (j + 1 + 1) • E.E t (f (t + (j + 1))) := by
    rw [← hs2.tsum_const_smul b]
    congr 1
    funext j
    simp only [smul_smul, pow_succ (b⁻¹) (j + 1)]
    rw [show t + 1 + j = t + (j + 1) by omega]
    congr 1
    field_simp
  rw [h2]
  abel

/-- **(2.3)** (Miao, p. 49): for `|b| > 1` and a stable adapted `z`, the fundamental solution
`x_t = −c∑ⱼ b^{−j−1}E_tz_{t+j}` of `E_tx_{t+1} = bx_t + cz_t` is a stable adapted solution. -/
theorem eq_2_3 [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) (c : ℝ)
    {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) :
    (∀ t, sre_fwd E b (c • z) t = -(c • ∑' j : ℕ, (b⁻¹) ^ (j + 1) • E.E t (z (t + j)))) ∧
    sre_IsAdapted E (sre_fwd E b (c • z)) ∧ sre_IsBounded (sre_fwd E b (c • z)) ∧
    ∀ t, E.E t (sre_fwd E b (c • z) (t + 1)) = b • sre_fwd E b (c • z) t + c • z t := by
  have hcza : sre_IsAdapted E (c • z) := fun t => by simp [hza t]
  have hczb : sre_IsBounded (c • z) := by
    obtain ⟨M, hM⟩ := hz
    exact ⟨|c| * M, fun t => by
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]; gcongr; exact hM t⟩
  obtain ⟨M, hM⟩ := hz
  refine ⟨fun t => ?_, sre_fwd_adapted E hb hczb, sre_fwd_isBounded E hb hczb,
    sre_fwd_rec E hb hcza hczb⟩
  simp only [sre_fwd, Pi.smul_apply, map_smul]
  rw [← (sre_fwd_summable E hb hM t).tsum_const_smul c]
  congr 2
  funext j
  rw [smul_comm]

/-- **(2.3)** (Miao, p. 49), uniqueness: the fundamental solution is the only stable adapted
solution. -/
theorem eq_2_3_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f x : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) (hx : sre_IsAdapted E x)
    (hxb : sre_IsBounded x) (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t) :
    x = sre_fwd E b f :=
  sre_unique_of_bounded E hb hx (sre_fwd_adapted E hb hf) hxb (sre_fwd_isBounded E hb hf) hxs
    (sre_fwd_rec E hb hfa hf)

/-- **(2.4)** (Miao, p. 49), with any particular solution `p`: `p + B` solves
`E_tx_{t+1} = bx_t + f_t` iff the bubble satisfies `E_tB_{t+1} = bB_t`. -/
theorem eq_2_4_of_particular (E : CondExpSystem ℝ V) (b : ℝ) {f p B : ℕ → V}
    (hp : ∀ t, E.E t (p (t + 1)) = b • p t + f t) :
    (∀ t, E.E t ((p + B) (t + 1)) = b • (p + B) t + f t) ↔
      ∀ t, E.E t (B (t + 1)) = b • B t := by
  constructor
  · intro h t
    have := h t
    simp only [Pi.add_apply, map_add, hp t, smul_add] at this
    calc E.E t (B (t + 1)) = (b • p t + f t + E.E t (B (t + 1))) - (b • p t + f t) := by abel
      _ = b • B t := by rw [this]; abel
  · intro h t
    simp only [Pi.add_apply, map_add, hp t, h t, smul_add]
    abel

/-- **(2.4)** (Miao, p. 49): `x* + B` solves iff `E_tB_{t+1} = bB_t`. -/
theorem eq_2_4 [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f B : ℕ → V}
    (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) :
    (∀ t, E.E t ((sre_fwd E b f + B) (t + 1)) = b • (sre_fwd E b f + B) t + f t) ↔
      ∀ t, E.E t (B (t + 1)) = b • B t :=
  eq_2_4_of_particular E b (sre_fwd_rec E hb hfa hf)

/-- Miao, p. 49: every adapted solution is `x* + B` with an adapted bubble `B`
(`E_tB_{t+1} = bB_t`). -/
theorem eq_2_4_every [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f x : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) (hx : sre_IsAdapted E x)
    (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t) :
    ∃ B, x = sre_fwd E b f + B ∧ sre_IsAdapted E B ∧ ∀ t, E.E t (B (t + 1)) = b • B t := by
  refine ⟨x - sre_fwd E b f, by abel, fun t => ?_, ?_⟩
  · simp only [Pi.sub_apply, map_sub, hx t, sre_fwd_adapted E hb hf t]
  · refine (eq_2_4 E hb hfa hf).1 ?_
    simpa using hxs

/-- The transversality (no-bubble) condition **(2.5)** (Miao, p. 49):
`lim_{T→∞} b^{−T}E_tx_{t+T} = 0` for every `t`. -/
def sre_Transversality (E : CondExpSystem ℝ V) (b : ℝ) (x : ℕ → V) : Prop :=
  ∀ t, Tendsto (fun T : ℕ => (b⁻¹) ^ T • E.E t (x (t + T))) atTop (𝓝 0)

/-- Miao, p. 49: every stable process satisfies (2.5) when `|b| > 1`. -/
theorem eq_2_5_of_bounded (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {x : ℕ → V}
    (hx : sre_IsBounded x) : sre_Transversality E b x := by
  obtain ⟨M, hM⟩ := hx
  intro t
  have hlim : Tendsto (fun T : ℕ => M * |b⁻¹| ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _)
      (sre_inv_abs_lt_one hb)).const_mul M
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm]
  gcongr
  exact (E.norm_apply_le _ _).trans (hM _)

/-- An adapted bubble satisfying (2.5) is zero. -/
theorem sre_bubble_tvc_zero (E : CondExpSystem ℝ V) {b : ℝ} (hb0 : b ≠ 0) {e : ℕ → V}
    (he : sre_IsAdapted E e) (hrec : ∀ t, E.E t (e (t + 1)) = b • e t)
    (htv : sre_Transversality E b e) : e = 0 := by
  funext t
  have hconst : (fun T : ℕ => (b⁻¹) ^ T • E.E t (e (t + T))) = fun _ => e t := by
    funext T
    rw [sre_iter E he hrec, smul_smul, ← mul_pow, inv_mul_cancel₀ hb0, one_pow, one_smul]
  have := htv t
  rw [hconst] at this
  exact tendsto_nhds_unique tendsto_const_nhds this

/-- Miao, p. 49: a nonzero adapted bubble violates (2.5): `b^{−T}E_tB_{t+T} = B_t`. -/
theorem eq_2_5_bubble_fails (E : CondExpSystem ℝ V) {b : ℝ} (hb0 : b ≠ 0) {B : ℕ → V}
    (hB : sre_IsAdapted E B) (hrec : ∀ t, E.E t (B (t + 1)) = b • B t) (hne : B ≠ 0) :
    ¬ sre_Transversality E b B :=
  fun h => hne (sre_bubble_tvc_zero E hb0 hB hrec h)

/-- Two adapted solutions of `E_tx_{t+1} = bx_t + f_t` that satisfy (2.5) coincide. -/
theorem sre_unique_of_tvc (E : CondExpSystem ℝ V) {b : ℝ} (hb0 : b ≠ 0) {f x y : ℕ → V}
    (hx : sre_IsAdapted E x) (hy : sre_IsAdapted E y) (hxt : sre_Transversality E b x)
    (hyt : sre_Transversality E b y) (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t)
    (hys : ∀ t, E.E t (y (t + 1)) = b • y t + f t) : x = y := by
  have h := sre_bubble_tvc_zero E hb0 (e := x - y)
    (fun t => by simp only [Pi.sub_apply, map_sub, hx t, hy t])
    (fun t => by simp only [Pi.sub_apply, map_sub, hxs, hys, smul_sub]; abel)
    (fun t => by
      have := (hxt t).sub (hyt t)
      simpa only [Pi.sub_apply, map_sub, smul_sub, sub_zero] using this)
  exact funext fun t => sub_eq_zero.1 (congrFun h t)

/-- **(2.5)** (Miao, p. 49): "if we impose the transversality condition, bubbles cannot
exist": an adapted solution satisfying (2.5) is the fundamental solution. -/
theorem eq_2_5_rules_out_bubbles [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ}
    (hb : 1 < |b|) {f x : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f)
    (hx : sre_IsAdapted E x) (hxt : sre_Transversality E b x)
    (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t) : x = sre_fwd E b f := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, abs_zero] at hb
    linarith
  exact sre_unique_of_tvc E hb0 hx (sre_fwd_adapted E hb hf) hxt
    (eq_2_5_of_bounded E hb (sre_fwd_isBounded E hb hf)) hxs (sre_fwd_rec E hb hfa hf)

/-- The forward sum when `E_tf_{t+1} = ρf_t` with `|ρ| < |b|`: `x*_t = (ρ − b)^{−1}f_t`
(no boundedness needed: the terms are `b^{−j−1}ρʲf_t`). -/
theorem sre_fwd_ar1 (E : CondExpSystem ℝ V) {b ρ : ℝ} (hρb : |ρ| < |b|) {f : ℕ → V}
    (hfa : sre_IsAdapted E f) (hf : ∀ t, E.E t (f (t + 1)) = ρ • f t) (t : ℕ) :
    sre_fwd E b f t = (ρ - b)⁻¹ • f t := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, abs_zero] at hρb
    linarith [abs_nonneg ρ]
  have hr : |ρ * b⁻¹| < 1 := by
    rw [abs_mul, abs_inv]
    have hpos : 0 < |b| := by linarith [abs_nonneg ρ]
    rw [mul_inv_lt_iff₀ hpos, one_mul]
    exact hρb
  have hterm : (fun j : ℕ => (b⁻¹) ^ (j + 1) • E.E t (f (t + j))) =
      fun j => (b⁻¹ * (ρ * b⁻¹) ^ j) • f t := by
    funext j
    rw [sre_iter E hfa hf, smul_smul, mul_pow, pow_succ]
    congr 1
    ring
  have hsum : HasSum (fun j : ℕ => b⁻¹ * (ρ * b⁻¹) ^ j) (b⁻¹ * (1 - ρ * b⁻¹)⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hr).mul_left _
  simp only [sre_fwd, hterm]
  rw [(hsum.smul_const (f t)).tsum_eq, ← neg_smul]
  congr 1
  have h1 : (1 - ρ * b⁻¹) ≠ 0 := by
    intro h
    have : ρ * b⁻¹ = 1 := by linarith
    rw [this, abs_one] at hr
    exact lt_irrefl _ hr
  have h2 : ρ - b ≠ 0 := by
    intro h
    have : ρ = b := by linarith
    rw [this] at hρb
    exact lt_irrefl _ hρb
  have h3 : b - ρ ≠ 0 := by
    intro h
    apply h2
    linarith
  field_simp
  ring

/-! ### Example 2.2.1 (Blanchard and Watson): abstract part -/

/-- Example 2.2.1 (Miao, p. 49): `d_t = ρd_{t−1} + ε_t` with `E_tε_{t+1} = 0` gives
`E_td_{t+j} = ρʲd_t`. The book assumes `ε` IID with mean zero; only the martingale-difference
property `E_tε_{t+1} = 0` is used. -/
theorem example_2_2_1_Ed (E : CondExpSystem ℝ V) {ρ : ℝ} {d ε : ℕ → V}
    (hd : sre_IsAdapted E d) (hrec : ∀ t, d (t + 1) = ρ • d t + ε (t + 1))
    (hε : ∀ t, E.E t (ε (t + 1)) = 0) (j t : ℕ) : E.E t (d (t + j)) = ρ ^ j • d t :=
  sre_iter E hd (fun t => by rw [hrec, map_add, hε, add_zero, map_smul, hd]) j t

/-- Example 2.2.1 (Miao, p. 49): the fundamental price `p_t = d_t/(R − ρ)` solves
`p_t = (E_tp_{t+1} + d_t)/R` and is the fundamental solution `∑ⱼ R^{−j−1}E_td_{t+j}`
(written as `sre_fwd E R (−d)`). -/
theorem example_2_2_1_fundamental (E : CondExpSystem ℝ V) {R ρ : ℝ} (hR : 1 < R)
    (hρ : |ρ| < 1) {d ε : ℕ → V} (hd : sre_IsAdapted E d)
    (hrec : ∀ t, d (t + 1) = ρ • d t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0) :
    (∀ t, (R - ρ)⁻¹ • d t = R⁻¹ • (E.E t ((R - ρ)⁻¹ • d (t + 1)) + d t)) ∧
    ∀ t, sre_fwd E R (-d) t = (R - ρ)⁻¹ • d t := by
  have hEd : ∀ t, E.E t (d (t + 1)) = ρ • d t := fun t => by
    simpa using example_2_2_1_Ed E hd hrec hε 1 t
  have hRρ : R - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    intro h; linarith
  constructor
  · intro t
    rw [map_smul, hEd, smul_smul]
    have hR0 : R ≠ 0 := by positivity
    have hk : R⁻¹ * ((R - ρ)⁻¹ * ρ + 1) = (R - ρ)⁻¹ := by
      field_simp
      ring
    calc (R - ρ)⁻¹ • d t = (R⁻¹ * ((R - ρ)⁻¹ * ρ + 1)) • d t := by rw [hk]
      _ = R⁻¹ • (((R - ρ)⁻¹ * ρ) • d t + d t) := by rw [mul_smul, add_smul, one_smul]
  · intro t
    have hρR : |ρ| < |R| := by rw [abs_of_pos (show (0 : ℝ) < R by linarith)]; linarith
    rw [sre_fwd_ar1 E hρR (f := -d) (fun t => by simp [hd t]) (fun t => by
      simp [hEd t]) t]
    simp only [Pi.neg_apply, smul_neg, ← neg_smul]
    congr 1
    rw [← inv_neg, neg_sub]

/-- Example 2.2.1 (Miao, pp. 49–50): the general adapted solution of `p_t = (E_tp_{t+1} + d_t)/R`
is `p_t = d_t/(R − ρ) + B_t` with `E_tB_{t+1} = RB_t`, and with `d` stable the fundamental price
is the only stable adapted one; a transversality condition like (2.5) rules out bubbles. -/
theorem example_2_2_1_general [CompleteSpace V] (E : CondExpSystem ℝ V) {R ρ : ℝ} (hR : 1 < R)
    (hρ : |ρ| < 1) {d ε p : ℕ → V} (hd : sre_IsAdapted E d)
    (hrec : ∀ t, d (t + 1) = ρ • d t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0)
    (hp : sre_IsAdapted E p) (hps : ∀ t, p t = R⁻¹ • (E.E t (p (t + 1)) + d t)) :
    (∃ B, p = (fun t => (R - ρ)⁻¹ • d t) + B ∧ ∀ t, E.E t (B (t + 1)) = R • B t) ∧
    (sre_IsBounded d → sre_Transversality E R p → p = fun t => (R - ρ)⁻¹ • d t) ∧
    (sre_IsBounded d → sre_IsBounded p → p = fun t => (R - ρ)⁻¹ • d t) := by
  have hR0 : R ≠ 0 := by positivity
  have hRabs : 1 < |R| := by rw [abs_of_pos (by linarith)]; exact hR
  have hsol : ∀ t, E.E t (p (t + 1)) = R • p t + (-d) t := fun t => by
    rw [hps t, smul_smul, mul_inv_cancel₀ hR0, one_smul, Pi.neg_apply]; abel
  obtain ⟨hfund, hfwd⟩ := example_2_2_1_fundamental E hR hρ hd hrec hε
  have hpart : ∀ t, E.E t ((fun t => (R - ρ)⁻¹ • d t) (t + 1)) =
      R • (fun t => (R - ρ)⁻¹ • d t) t + (-d) t := fun t => by
    have h := hfund t
    simp only [Pi.neg_apply]
    conv_rhs => rw [h, smul_smul, mul_inv_cancel₀ hR0, one_smul]
    abel
  have hda : sre_IsAdapted E (-d) := fun t => by simp [hd t]
  refine ⟨⟨p - fun t => (R - ρ)⁻¹ • d t, by abel, ?_⟩, fun hdb htv => ?_, fun hdb hpb => ?_⟩
  · refine (eq_2_4_of_particular E R (p := fun s => (R - ρ)⁻¹ • d s) hpart).1 ?_
    simpa using hsol
  · have hnb : sre_IsBounded (-d) := by
      obtain ⟨M, hM⟩ := hdb; exact ⟨M, fun t => by simpa using hM t⟩
    rw [eq_2_5_rules_out_bubbles E hRabs hda hnb hp htv hsol]
    funext t; exact hfwd t
  · have hnb : sre_IsBounded (-d) := by
      obtain ⟨M, hM⟩ := hdb; exact ⟨M, fun t => by simpa using hM t⟩
    rw [eq_2_3_unique E hRabs hda hnb hp hpb hsol]
    funext t; exact hfwd t

/-! ### Boundedness of a stable backward recursion -/

omit [NormedSpace ℝ V] in
/-- If `‖x_{t+1}‖ ≤ |λ|‖x_t‖ + U` with `|λ| < 1`, then `‖x_t‖ ≤ ‖x₀‖ + U/(1 − |λ|)`. -/
theorem sre_bounded_of_rec {x : ℕ → V} {lam U : ℝ} (hl : |lam| < 1) (hU : 0 ≤ U)
    (h : ∀ t, ‖x (t + 1)‖ ≤ |lam| * ‖x t‖ + U) (t : ℕ) :
    ‖x t‖ ≤ ‖x 0‖ + U / (1 - |lam|) := by
  have h1 : 0 < 1 - |lam| := by linarith
  have hq : 0 ≤ U / (1 - |lam|) := div_nonneg hU h1.le
  induction t with
  | zero => linarith
  | succ t ih =>
    have hk : |lam| * (U / (1 - |lam|)) + U = U / (1 - |lam|) := by
      field_simp
      ring
    calc ‖x (t + 1)‖ ≤ |lam| * ‖x t‖ + U := h t
      _ ≤ |lam| * (‖x 0‖ + U / (1 - |lam|)) + U := by gcongr
      _ = |lam| * ‖x 0‖ + (|lam| * (U / (1 - |lam|)) + U) := by ring
      _ ≤ 1 * ‖x 0‖ + U / (1 - |lam|) := by
          rw [hk]; gcongr
      _ = ‖x 0‖ + U / (1 - |lam|) := by ring

theorem sre_smul_isBounded {x : ℕ → V} (c : ℝ) (hx : sre_IsBounded x) :
    sre_IsBounded (c • x) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨|c| * M, fun t => by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]; gcongr; exact hM t⟩

theorem sre_smul_isAdapted (E : CondExpSystem ℝ V) {x : ℕ → V} (c : ℝ)
    (hx : sre_IsAdapted E x) : sre_IsAdapted E (c • x) := fun t => by simp [hx t]

/-! ### The second-order equation (2.6) -/

/-- **(2.6)** (Miao, p. 50): `E_tx_{t+1} = ax_t + bx_{t−1} + cz_t`, imposed for `t ≥ 1` (it involves
`x_{t−1}`; `x₀` is given), written at date `t + 1`. -/
def sre_IsSol26 (E : CondExpSystem ℝ V) (a b c : ℝ) (z x : ℕ → V) : Prop :=
  ∀ t, E.E (t + 1) (x (t + 2)) = a • x (t + 1) + b • x t + c • z (t + 1)

/-- The lag-operator solution of (2.6) (Miao, p. 50): `x_t = λ₁x_{t−1} + u_t` with
`u = −c∑ⱼλ₂^{−j−1}E_tz_{t+j}`, the forward solution of `E_tu_{t+1} = λ₂u_t + cz_t`. -/
noncomputable def sre_second (E : CondExpSystem ℝ V) (lam1 lam2 c : ℝ) (z : ℕ → V) (x0 : V) :
    ℕ → V
  | 0 => x0
  | t + 1 => lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1)

/-- **(2.9)** (Miao, p. 50): the forward part is `−(c/λ₂)∑ⱼλ₂^{−j}E_tz_{t+j}`, so
`x_t = λ₁x_{t−1} − (c/λ₂)∑ⱼλ₂^{−j}E_tz_{t+j}`. -/
theorem eq_2_9 [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 : ℝ} (hl2 : 1 < |lam2|)
    (c : ℝ) {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) (x0 : V) (t : ℕ) :
    sre_second E lam1 lam2 c z x0 (t + 1) = lam1 • sre_second E lam1 lam2 c z x0 t -
      (c / lam2) • ∑' j : ℕ, (lam2⁻¹) ^ j • E.E (t + 1) (z (t + 1 + j)) := by
  obtain ⟨M, hM⟩ := hz
  have hs := sre_fwd_summable E hl2 hM (t + 1)
  have hs0 : Summable fun j : ℕ => (lam2⁻¹) ^ j • E.E (t + 1) (z (t + 1 + j)) := by
    have := hs.const_smul lam2
    refine this.congr fun j => ?_
    have h0 : lam2 ≠ 0 := by
      intro h; rw [h, abs_zero] at hl2; linarith
    rw [smul_smul, pow_succ, ← mul_assoc, mul_comm lam2, mul_assoc, mul_inv_cancel₀ h0,
      mul_one]
  rw [sre_second, (eq_2_3 E hl2 c hza ⟨M, hM⟩).1, sub_eq_add_neg]
  congr 1
  congr 1
  rw [← hs0.tsum_const_smul, ← hs.tsum_const_smul]
  congr 1
  funext j
  rw [smul_smul, smul_smul, pow_succ, div_eq_mul_inv]
  congr 1
  ring

theorem sre_second_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 : ℝ}
    (hl2 : 1 < |lam2|) (c : ℝ) {z : ℕ → V} (hz : sre_IsBounded z) {x0 : V}
    (hx0 : E.E 0 x0 = x0) : sre_IsAdapted E (sre_second E lam1 lam2 c z x0) := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    simp only [sre_second, map_add, map_smul]
    rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih,
      sre_fwd_adapted E hl2 (sre_smul_isBounded c hz) (t + 1)]

/-- Miao, (2.6)–(2.9), p. 50: with `a = λ₁ + λ₂`, `b = −λ₁λ₂` (the characteristic roots of
Section 1.3), `|λ₁| < 1 < |λ₂|` and `z` stable and adapted, the lag-operator process is a stable
adapted solution of (2.6) on the dates `t ≥ 1` with the given `x₀`. -/
theorem eq_2_6_solution [CompleteSpace V] (E : CondExpSystem ℝ V) {a b c lam1 lam2 : ℝ}
    (ha : a = lam1 + lam2) (hb : b = -(lam1 * lam2)) (hl1 : |lam1| < 1) (hl2 : 1 < |lam2|)
    {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x0 : V}
    (hx0 : E.E 0 x0 = x0) :
    sre_second E lam1 lam2 c z x0 0 = x0 ∧ sre_IsAdapted E (sre_second E lam1 lam2 c z x0) ∧
      sre_IsBounded (sre_second E lam1 lam2 c z x0) ∧
      sre_IsSol26 E a b c z (sre_second E lam1 lam2 c z x0) := by
  have hczb := sre_smul_isBounded c hz
  have hXa := sre_second_adapted E hl2 c hz (lam1 := lam1) hx0
  refine ⟨rfl, hXa, ?_, fun t => ?_⟩
  · obtain ⟨U, hU⟩ := sre_fwd_isBounded E hl2 hczb
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
    refine ⟨_, sre_bounded_of_rec hl1 hU0 (fun t => ?_)⟩
    calc ‖sre_second E lam1 lam2 c z x0 (t + 1)‖
        = ‖lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1)‖ := rfl
      _ ≤ ‖lam1 • sre_second E lam1 lam2 c z x0 t‖ + ‖sre_fwd E lam2 (c • z) (t + 1)‖ :=
          norm_add_le _ _
      _ ≤ |lam1| * ‖sre_second E lam1 lam2 c z x0 t‖ + U := by
          rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hU _
  · have h1 : sre_second E lam1 lam2 c z x0 (t + 2) =
        lam1 • sre_second E lam1 lam2 c z x0 (t + 1) + sre_fwd E lam2 (c • z) (t + 1 + 1) := rfl
    have h2 : sre_second E lam1 lam2 c z x0 (t + 1) =
        lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1) := rfl
    have hrec := sre_fwd_rec E hl2 (sre_smul_isAdapted E c hza) hczb (t + 1)
    rw [h1, map_add, map_smul, hXa (t + 1), hrec, Pi.smul_apply, h2, ha, hb]
    module

/-- Miao, (2.6)–(2.9), p. 50, uniqueness: the lag-operator process is the only stable adapted
solution of (2.6) (dates `t ≥ 1`) with the given `x₀`. -/
theorem eq_2_6_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {a b c lam1 lam2 : ℝ}
    (ha : a = lam1 + lam2) (hb : b = -(lam1 * lam2)) (hl2 : 1 < |lam2|) {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x : ℕ → V} (hxa : sre_IsAdapted E x)
    (hxb : sre_IsBounded x) (hxs : sre_IsSol26 E a b c z x) :
    x = sre_second E lam1 lam2 c z (x 0) := by
  set u := sre_fwd E lam2 (c • z) with hu
  have hczb := sre_smul_isBounded c hz
  have hcza := sre_smul_isAdapted E c hza
  set E' := sre_shiftSys E 1
  have hv : (fun t => x (t + 1) - lam1 • x t) = fun t => u (t + 1) := by
    refine sre_unique_of_bounded E' hl2 (f := fun t => c • z (t + 1)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro t
      change E.E (t + 1) _ = _
      rw [map_sub, map_smul, hxa (t + 1), sre_adapted_succ E hxa t]
    · intro t
      exact sre_fwd_adapted E hl2 hczb (t + 1)
    · obtain ⟨M, hM⟩ := hxb
      exact ⟨M + |lam1| * M, fun t => (norm_sub_le _ _).trans (add_le_add (hM _)
        (by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hM t))⟩
    · obtain ⟨M, hM⟩ := sre_fwd_isBounded E hl2 hczb
      exact ⟨M, fun t => hM _⟩
    · intro t
      change E.E (t + 1) _ = _
      rw [map_sub, map_smul, hxs t, hxa (t + 1), ha, hb]
      module
    · intro t
      change E.E (t + 1) _ = _
      exact sre_fwd_rec E hl2 hcza hczb (t + 1)
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    have := congrFun hv t
    change x (t + 1) = lam1 • sre_second E lam1 lam2 c z (x 0) t + u (t + 1)
    rw [← ih, ← this]
    abel

/-! ### The equation (2.10) -/

/-- **(2.10)** (Miao, p. 51): `E_tx_{t+1} = a₀x_t + a₁E_{t−1}x_t + a₂x_{t−1} + cz_t`, for `t ≥ 1`,
written at date `t + 1`. -/
def sre_IsSol210 (E : CondExpSystem ℝ V) (a0 a1 a2 c : ℝ) (z x : ℕ → V) : Prop :=
  ∀ t, E.E (t + 1) (x (t + 2)) =
    a0 • x (t + 1) + a1 • E.E t (x (t + 1)) + a2 • x t + c • z (t + 1)

/-- Miao, p. 51: taking `E_{t−1}` of (2.10) gives
`E_{t−1}x_{t+1} = (a₀ + a₁)E_{t−1}x_t + a₂x_{t−1} + cE_{t−1}z_t`. -/
theorem eq_2_10_reduce (E : CondExpSystem ℝ V) {a0 a1 a2 c : ℝ} {z x : ℕ → V}
    (hxa : sre_IsAdapted E x) (hxs : sre_IsSol210 E a0 a1 a2 c z x) (t : ℕ) :
    E.E t (x (t + 2)) = (a0 + a1) • E.E t (x (t + 1)) + a2 • x t + c • E.E t (z (t + 1)) := by
  have := congrArg (E.E t) (hxs t)
  rw [E.tower_le_apply (Nat.le_succ t)] at this
  rw [this]
  simp only [map_add, map_smul, E.idem, hxa t, add_smul]

/-- The forcing `c E_tz_{t+1}` of the reduced forward equation. -/
noncomputable def sre_force210 (E : CondExpSystem ℝ V) (c : ℝ) (z : ℕ → V) : ℕ → V :=
  fun s => c • E.E s (z (s + 1))

theorem sre_force210_adapted (E : CondExpSystem ℝ V) (c : ℝ) (z : ℕ → V) :
    sre_IsAdapted E (sre_force210 E c z) := fun s => by simp [sre_force210, E.idem]

theorem sre_force210_bounded (E : CondExpSystem ℝ V) (c : ℝ) {z : ℕ → V}
    (hz : sre_IsBounded z) : sre_IsBounded (sre_force210 E c z) := by
  obtain ⟨M, hM⟩ := hz
  exact ⟨|c| * M, fun s => by
    rw [sre_force210, norm_smul, Real.norm_eq_abs]
    gcongr
    exact (E.norm_apply_le _ _).trans (hM _)⟩

/-- The solution of (2.10) built as the book describes (Miao, p. 51): `ω = E_tx_{t+1} − λ₁x_t`
is the forward solution of `E_tω_{t+1} = λ₂ω_t + cE_tz_{t+1}`, and (2.10) is then solved for
`x_t`: `x_{t+1} = λ₁x_t + (a₀ − λ₁)^{−1}(ω_{t+1} − a₁ω_t − cz_{t+1})`. -/
noncomputable def sre_sol210 (E : CondExpSystem ℝ V) (lam1 lam2 a0 a1 c : ℝ) (z : ℕ → V)
    (x0 : V) : ℕ → V
  | 0 => x0
  | t + 1 => lam1 • sre_sol210 E lam1 lam2 a0 a1 c z x0 t +
      (a0 - lam1)⁻¹ • (sre_fwd E lam2 (sre_force210 E c z) (t + 1) -
        a1 • sre_fwd E lam2 (sre_force210 E c z) t - c • z (t + 1))

theorem sre_sol210_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 c : ℝ}
    (hl2 : 1 < |lam2|) {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x0 : V}
    (hx0 : E.E 0 x0 = x0) : sre_IsAdapted E (sre_sol210 E lam1 lam2 a0 a1 c z x0) := by
  have hω := sre_fwd_adapted E hl2 (sre_force210_bounded E c hz)
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    simp only [sre_sol210, map_add, map_smul, map_sub]
    rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih, hω (t + 1), hza (t + 1),
      sre_adapted_succ E hω t]

/-- The key identity: `E_tx_{t+1} = λ₁x_t + ω_t` along the constructed solution. -/
theorem sre_sol210_E [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 c : ℝ}
    (hsum : lam1 + lam2 = a0 + a1) (hne : a0 ≠ lam1) (hl2 : 1 < |lam2|) {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x0 : V} (hx0 : E.E 0 x0 = x0) (t : ℕ) :
    E.E t (sre_sol210 E lam1 lam2 a0 a1 c z x0 (t + 1)) =
      lam1 • sre_sol210 E lam1 lam2 a0 a1 c z x0 t + sre_fwd E lam2 (sre_force210 E c z) t := by
  have hfb := sre_force210_bounded E c hz
  have hω := sre_fwd_adapted E hl2 hfb
  have hrec := sre_fwd_rec E hl2 (sre_force210_adapted E c z) hfb t
  have hXa := sre_sol210_adapted E (lam1 := lam1) (a0 := a0) (a1 := a1) (c := c) hl2 hza hz hx0
  have hk : (a0 - lam1)⁻¹ * (a0 - lam1) = 1 := inv_mul_cancel₀ (sub_ne_zero.2 hne)
  simp only [sre_sol210, map_add, map_smul, map_sub]
  rw [hXa t, hrec, hω t, sre_force210]
  have ha1 : a1 = lam1 + lam2 - a0 := by linarith
  subst ha1
  linear_combination (norm := module) hk • sre_fwd E lam2 (sre_force210 E c z) t

/-- Miao, (2.10), p. 51, existence (the book's recipe, made precise): let `λ₁, λ₂` be the roots
of `λ² = (a₀ + a₁)λ + a₂` (`λ₁ + λ₂ = a₀ + a₁`, `λ₁λ₂ = −a₂`) with `|λ₁| < 1 < |λ₂|`, and
`a₀ ≠ λ₁`. For stable adapted `z`, `sre_sol210` is a stable adapted solution of (2.10) with the
given `x₀`. -/
theorem eq_2_10_solution [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 a2 c : ℝ}
    (hsum : lam1 + lam2 = a0 + a1) (hprod : a2 = -(lam1 * lam2)) (hne : a0 ≠ lam1)
    (hl1 : |lam1| < 1) (hl2 : 1 < |lam2|) {z : ℕ → V} (hza : sre_IsAdapted E z)
    (hz : sre_IsBounded z) {x0 : V} (hx0 : E.E 0 x0 = x0) :
    sre_sol210 E lam1 lam2 a0 a1 c z x0 0 = x0 ∧
      sre_IsAdapted E (sre_sol210 E lam1 lam2 a0 a1 c z x0) ∧
      sre_IsBounded (sre_sol210 E lam1 lam2 a0 a1 c z x0) ∧
      sre_IsSol210 E a0 a1 a2 c z (sre_sol210 E lam1 lam2 a0 a1 c z x0) := by
  set X := sre_sol210 E lam1 lam2 a0 a1 c z x0 with hX
  set ω := sre_fwd E lam2 (sre_force210 E c z) with hωdef
  have hfb := sre_force210_bounded E c hz
  have hXa : sre_IsAdapted E X := sre_sol210_adapted E hl2 hza hz hx0
  have hk : (a0 - lam1) * (a0 - lam1)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.2 hne)
  refine ⟨rfl, hXa, ?_, fun t => ?_⟩
  · obtain ⟨W, hW⟩ := sre_fwd_isBounded E hl2 hfb
    obtain ⟨Z, hZ⟩ := hz
    have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
    have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
    have hU0 : 0 ≤ |(a0 - lam1)⁻¹| * (W + |a1| * W + |c| * Z) := by positivity
    refine ⟨_, sre_bounded_of_rec hl1 hU0 (fun t => ?_)⟩
    have hinner : ‖ω (t + 1) - a1 • ω t - c • z (t + 1)‖ ≤ W + |a1| * W + |c| * Z := by
      calc ‖ω (t + 1) - a1 • ω t - c • z (t + 1)‖
          ≤ ‖ω (t + 1) - a1 • ω t‖ + ‖c • z (t + 1)‖ := norm_sub_le _ _
        _ ≤ ‖ω (t + 1)‖ + ‖a1 • ω t‖ + ‖c • z (t + 1)‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ W + |a1| * W + |c| * Z := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            gcongr
            · exact hW _
            · exact hW _
            · exact hZ _
    calc ‖X (t + 1)‖
        = ‖lam1 • X t + (a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1))‖ := rfl
      _ ≤ ‖lam1 • X t‖ + ‖(a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1))‖ :=
          norm_add_le _ _
      _ ≤ |lam1| * ‖X t‖ + |(a0 - lam1)⁻¹| * (W + |a1| * W + |c| * Z) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
  · have h1 := sre_sol210_E E hsum hne hl2 hza hz hx0 (c := c) (t + 1)
    have h0 := sre_sol210_E E hsum hne hl2 hza hz hx0 (c := c) t
    rw [h1, h0]
    have hdef : X (t + 1) =
        lam1 • X t + (a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1)) := rfl
    have hDX : (a0 - lam1) • X (t + 1) =
        ((a0 - lam1) * lam1) • X t + (ω (t + 1) - a1 • ω t - c • z (t + 1)) := by
      rw [hdef]
      linear_combination (norm := module) hk • (ω (t + 1) - a1 • ω t - c • z (t + 1))
    have ha1 : a1 = lam1 + lam2 - a0 := by linarith
    subst ha1 hprod
    linear_combination (norm := module) -hDX

/-- Miao, (2.10), p. 51, uniqueness: under the hypotheses of `eq_2_10_solution`, every stable
adapted solution of (2.10) is `sre_sol210` with its own `x₀`. -/
theorem eq_2_10_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 a2 c : ℝ}
    (hsum : lam1 + lam2 = a0 + a1) (hprod : a2 = -(lam1 * lam2)) (hne : a0 ≠ lam1)
    (hl2 : 1 < |lam2|) {z : ℕ → V} (hz : sre_IsBounded z)
    {x : ℕ → V} (hxa : sre_IsAdapted E x) (hxb : sre_IsBounded x)
    (hxs : sre_IsSol210 E a0 a1 a2 c z x) :
    x = sre_sol210 E lam1 lam2 a0 a1 c z (x 0) := by
  set ω := sre_fwd E lam2 (sre_force210 E c z) with hωdef
  have hfb := sre_force210_bounded E c hz
  have hw : (fun t => E.E t (x (t + 1)) - lam1 • x t) = ω := by
    refine sre_unique_of_bounded E hl2 (f := sre_force210 E c z) ?_
      (sre_fwd_adapted E hl2 hfb) ?_ (sre_fwd_isBounded E hl2 hfb) ?_
      (sre_fwd_rec E hl2 (sre_force210_adapted E c z) hfb)
    · intro t
      simp only [map_sub, map_smul, E.idem, hxa t]
    · obtain ⟨M, hM⟩ := hxb
      exact ⟨M + |lam1| * M, fun t => (norm_sub_le _ _).trans (add_le_add
        ((E.norm_apply_le _ _).trans (hM _))
        (by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hM t))⟩
    · intro t
      simp only [map_sub, map_smul]
      rw [E.tower_le_apply (Nat.le_succ t), eq_2_10_reduce E hxa hxs t, sre_force210]
      have ha1 : a1 = lam1 + lam2 - a0 := by linarith
      subst ha1 hprod
      module
  have hk : (a0 - lam1)⁻¹ * (a0 - lam1) = 1 := inv_mul_cancel₀ (sub_ne_zero.2 hne)
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    have e1 : E.E (t + 1) (x (t + 2)) = lam1 • x (t + 1) + ω (t + 1) := by
      have := congrFun hw (t + 1)
      rw [← this]; abel
    have e0 : E.E t (x (t + 1)) = lam1 • x t + ω t := by
      have := congrFun hw t
      rw [← this]; abel
    have heq := hxs t
    rw [e1, e0] at heq
    change x (t + 1) = lam1 • sre_sol210 E lam1 lam2 a0 a1 c z (x 0) t +
      (a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1))
    rw [← ih]
    have ha1 : a1 = lam1 + lam2 - a0 := by linarith
    subst ha1 hprod
    linear_combination (norm := module) -(a0 - lam1)⁻¹ • heq - hk • (x (t + 1) - lam1 • x t)

/-- The sunspot process `x_{t+1} = λ₁x_t + η_{t+1}`. -/
def sre_sunspot (lam1 : ℝ) (η : ℕ → V) (x0 : V) : ℕ → V
  | 0 => x0
  | t + 1 => lam1 • sre_sunspot lam1 η x0 t + η (t + 1)

/-- Miao, (2.10), p. 51, the condition `a₀ ≠ λ₁` cannot be dropped: if `a₀ = λ₁` (so
`a₁ = λ₂`, `a₂ = −λ₁λ₂`) and `c = 0`, then for every adapted `η` with `E_tη_{t+1} = 0`,
`x_{t+1} = λ₁x_t + η_{t+1}` solves (2.10); it is stable when `η` is bounded and `|λ₁| < 1`.
Taking `η = 0` and any nonzero bounded martingale difference gives two different stable solutions
with the same `x₀`. -/
theorem eq_2_10_indeterminate (E : CondExpSystem ℝ V) {lam1 lam2 : ℝ} (hl1 : |lam1| < 1)
    {z η : ℕ → V} (hηa : sre_IsAdapted E η) (hη : ∀ t, E.E t (η (t + 1)) = 0) {x0 : V}
    (hx0 : E.E 0 x0 = x0) :
    sre_IsAdapted E (sre_sunspot lam1 η x0) ∧
      sre_IsSol210 E lam1 lam2 (-(lam1 * lam2)) 0 z (sre_sunspot lam1 η x0) ∧
      (sre_IsBounded η → sre_IsBounded (sre_sunspot lam1 η x0)) := by
  have hXa : sre_IsAdapted E (sre_sunspot lam1 η x0) := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      simp only [sre_sunspot, map_add, map_smul]
      rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih, hηa]
  refine ⟨hXa, fun t => ?_, fun ⟨U, hU⟩ => ?_⟩
  · have h1 : sre_sunspot lam1 η x0 (t + 2) = lam1 • sre_sunspot lam1 η x0 (t + 1) + η (t + 2) :=
      rfl
    have h0 : sre_sunspot lam1 η x0 (t + 1) = lam1 • sre_sunspot lam1 η x0 t + η (t + 1) := rfl
    rw [h1, map_add, map_smul, hXa (t + 1), hη (t + 1)]
    conv_rhs => rw [h0, map_add, map_smul, hXa t, hη t]
    rw [h0]
    module
  · have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
    refine ⟨_, sre_bounded_of_rec hl1 hU0 (fun t => ?_)⟩
    calc ‖sre_sunspot lam1 η x0 (t + 1)‖ = ‖lam1 • sre_sunspot lam1 η x0 t + η (t + 1)‖ := rfl
      _ ≤ |lam1| * ‖sre_sunspot lam1 η x0 t‖ + U := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hU _

/-! ### §2.2.2: the method of undetermined coefficients -/

/-- The guess of §2.2.2 (Miao, p. 51): `x_t = Gx_{t−1} + Hz_t`. -/
def sre_uc (G H : ℝ) (z : ℕ → V) (x0 : V) : ℕ → V
  | 0 => x0
  | t + 1 => G • sre_uc G H z x0 t + H • z (t + 1)

theorem sre_uc_adapted (E : CondExpSystem ℝ V) (G H : ℝ) {z : ℕ → V} (hza : sre_IsAdapted E z)
    {x0 : V} (hx0 : E.E 0 x0 = x0) : sre_IsAdapted E (sre_uc G H z x0) := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    simp only [sre_uc, map_add, map_smul]
    rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih, hza]

/-- §2.2.2 (Miao, pp. 51–52): with `z_t = ρz_{t−1} + ε_t`, `E_{t−1}ε_t = 0` (so
`E_tz_{t+1} = ρz_t`; the book assumes `ε` IID with mean zero), the guess solves (2.6) iff
`(G² − aG − b)x_{t−1} + (GH + ρH − aH − c)z_t = 0` for all `t ≥ 1`. (The book's display
`E_t(Gx_t + Hz_{t+1}) = a(Gx_{t−1} + Hz_t) + bx_{t−1} + cz_t = G²x_{t−1} + GHz_t + ρHz_t` chains
the equation and the evaluation of its left side; the matching conditions are as printed.) -/
theorem uc_iff (E : CondExpSystem ℝ V) {a b c ρ G H : ℝ} {z : ℕ → V} (hza : sre_IsAdapted E z)
    (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) {x0 : V} (hx0 : E.E 0 x0 = x0) :
    sre_IsSol26 E a b c z (sre_uc G H z x0) ↔
      ∀ t, (G ^ 2 - a * G - b) • sre_uc G H z x0 t +
        (G * H + ρ * H - a * H - c) • z (t + 1) = 0 := by
  have hXa := sre_uc_adapted E G H hza hx0
  refine forall_congr' fun t => ?_
  have h1 : sre_uc G H z x0 (t + 2) = G • sre_uc G H z x0 (t + 1) + H • z (t + 2) := rfl
  have h0 : sre_uc G H z x0 (t + 1) = G • sre_uc G H z x0 t + H • z (t + 1) := rfl
  rw [h1, map_add, map_smul, map_smul, hXa (t + 1), hz (t + 1), h0, ← sub_eq_zero]
  constructor
  · intro h
    rw [← h]
    module
  · intro h
    rw [← h]
    module

/-- §2.2.2 (Miao, p. 52): matching coefficients, `G² = aG + b` and `GH + ρH = aH + c`, is
sufficient for the guess to solve (2.6). -/
theorem uc_sufficient (E : CondExpSystem ℝ V) {a b c ρ G H : ℝ} {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) {x0 : V}
    (hx0 : E.E 0 x0 = x0) (hG : G ^ 2 = a * G + b) (hH : G * H + ρ * H = a * H + c) :
    sre_IsSol26 E a b c z (sre_uc G H z x0) := by
  refine (uc_iff E hza hz hx0).2 fun t => ?_
  rw [show G ^ 2 - a * G - b = 0 by linarith, show G * H + ρ * H - a * H - c = 0 by linarith,
    zero_smul, zero_smul, add_zero]

/-- §2.2.2 (Miao, p. 52): matching coefficients is necessary as soon as the guess solves (2.6)
for two different initial values and `z` is not identically zero. -/
theorem uc_necessary (E : CondExpSystem ℝ V) {a b c ρ G H : ℝ} {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) {x0 x0' : V}
    (hx0 : E.E 0 x0 = x0) (hx0' : E.E 0 x0' = x0') (hne : x0 ≠ x0')
    (hs : sre_IsSol26 E a b c z (sre_uc G H z x0))
    (hs' : sre_IsSol26 E a b c z (sre_uc G H z x0')) {t : ℕ} (hzt : z (t + 1) ≠ 0) :
    G ^ 2 = a * G + b ∧ G * H + ρ * H = a * H + c := by
  have h := (uc_iff E hza hz hx0).1 hs
  have h' := (uc_iff E hza hz hx0').1 hs'
  have hG : G ^ 2 - a * G - b = 0 := by
    have h0 := h 0
    have h0' := h' 0
    have : (G ^ 2 - a * G - b) • (x0 - x0') = 0 := by
      have e : sre_uc G H z x0 0 = x0 := rfl
      have e' : sre_uc G H z x0' 0 = x0' := rfl
      rw [e] at h0
      rw [e'] at h0'
      rw [smul_sub]
      linear_combination (norm := module) h0 - h0'
    exact (smul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have ht := h t
  rw [hG, zero_smul, zero_add] at ht
  have hH := (smul_eq_zero.1 ht).resolve_right hzt
  constructor <;> linarith

/-- §2.2.2 (Miao, p. 52): with `a = λ₁ + λ₂`, `|ρ| < 1 < |λ₂|`, the denominator of
`H = c/(G + ρ − a)` at the stable root `G = λ₁` is `ρ − λ₂ ≠ 0`. -/
theorem uc_denominator_ne_zero {a lam1 lam2 ρ : ℝ} (ha : a = lam1 + lam2) (hρ : |ρ| < 1)
    (hl2 : 1 < |lam2|) : lam1 + ρ - a ≠ 0 := by
  rw [ha]
  intro h
  have : ρ = lam2 := by linarith
  rw [this] at hρ
  linarith

/-- §2.2.2 (Miao, p. 52): the stable root `G = λ₁` and `H = c/(G + ρ − a)` satisfy both
matching conditions. -/
theorem uc_stable_root {a b c lam1 lam2 ρ : ℝ} (ha : a = lam1 + lam2) (hb : b = -(lam1 * lam2))
    (hρ : |ρ| < 1) (hl2 : 1 < |lam2|) :
    lam1 ^ 2 = a * lam1 + b ∧
      lam1 * (c / (lam1 + ρ - a)) + ρ * (c / (lam1 + ρ - a)) =
        a * (c / (lam1 + ρ - a)) + c := by
  have hd := uc_denominator_ne_zero ha hρ hl2
  refine ⟨by rw [ha, hb]; ring, ?_⟩
  field_simp
  ring

/-- §2.2.2 (Miao, p. 52): the undetermined-coefficients solution with `G = λ₁`,
`H = c/(G + ρ − a)` is the lag-operator solution of (2.6)–(2.9). -/
theorem uc_eq_lag_solution (E : CondExpSystem ℝ V) {a c lam1 lam2 ρ : ℝ}
    (ha : a = lam1 + lam2) (hρ : |ρ| < 1) (hl2 : 1 < |lam2|) {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) (x0 : V) :
    sre_second E lam1 lam2 c z x0 = sre_uc lam1 (c / (lam1 + ρ - a)) z x0 := by
  have hd := uc_denominator_ne_zero ha hρ hl2
  have hρl : |ρ| < |lam2| := by linarith
  have hu : ∀ t, sre_fwd E lam2 (c • z) t = (c / (lam1 + ρ - a)) • z t := by
    intro t
    rw [sre_fwd_ar1 E hρl (sre_smul_isAdapted E c hza) (fun t => by
      simp only [Pi.smul_apply, map_smul, hz t, smul_comm c ρ]) t, Pi.smul_apply, smul_smul]
    congr 1
    rw [ha, show lam1 + ρ - (lam1 + lam2) = ρ - lam2 by ring]
    field_simp
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1) =
      lam1 • sre_uc lam1 (c / (lam1 + ρ - a)) z x0 t + (c / (lam1 + ρ - a)) • z (t + 1)
    rw [ih, hu]

/-! ### Example 2.2.1: the bursting bubble, concretely -/

/-- Example 2.2.1 (Miao, p. 50): a coin `θ_{t+1}` independent of `F_t` with mean `q` (for a
0–1 coin, `Pr(θ_{t+1} = 1) = q`) has conditional mean `E_tθ_{t+1} = q`. -/
theorem example_2_2_1_coin {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (t : ℕ) {θ : Ω → ℝ} {q : ℝ}
    (hθ : Measurable θ) (hind : ProbabilityTheory.Indep (MeasurableSpace.comap θ inferInstance)
      (ℱ t) μ) (hq : ∫ ω, θ ω ∂μ = q) :
    μ[θ | ℱ t] =ᵐ[μ] fun _ => q := by
  have h := condExp_indep_eq hθ.comap_le (ℱ.le t)
    (Measurable.of_comap_le le_rfl).stronglyMeasurable hind
  rw [hq] at h
  exact h

/-- **Example 2.2.1** (Miao, p. 50): the bursting bubble
`B_{t+1} = (R/q)B_tθ_{t+1} + e_{t+1}` with a 0–1 coin `θ_{t+1}` of conditional mean `q` and
`E_te_{t+1} = 0` satisfies (2.4): `E_tB_{t+1} = RB_t`. -/
theorem example_2_2_1_bubble {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {R q : ℝ} (hq : q ≠ 0) {B θ e : ℕ → Ω → ℝ}
    (t : ℕ) (hB : StronglyMeasurable[ℱ t] (B t)) (hBi : Integrable (B t) μ)
    (hθm : StronglyMeasurable (θ (t + 1))) (hθ01 : ∀ ω, θ (t + 1) ω = 0 ∨ θ (t + 1) ω = 1)
    (hθ : μ[θ (t + 1) | ℱ t] =ᵐ[μ] fun _ => q) (hei : Integrable (e (t + 1)) μ)
    (he : μ[e (t + 1) | ℱ t] =ᵐ[μ] 0)
    (hrec : ∀ ω, B (t + 1) ω = R / q * B t ω * θ (t + 1) ω + e (t + 1) ω) :
    μ[B (t + 1) | ℱ t] =ᵐ[μ] fun ω => R * B t ω := by
  have hθb : ∀ ω, ‖θ (t + 1) ω‖ ≤ 1 := fun ω => by
    rcases hθ01 ω with h | h <;> simp [h]
  have hθi : Integrable (θ (t + 1)) μ :=
    Integrable.of_bound hθm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hθb)
  have hfm : StronglyMeasurable[ℱ t] (fun ω => R / q * B t ω) := hB.const_mul _
  have hfi : Integrable (fun ω => R / q * B t ω) μ := hBi.const_mul _
  have hprod : Integrable ((fun ω => R / q * B t ω) * θ (t + 1)) μ :=
    hfi.mul_bdd hθm.aestronglyMeasurable (Filter.Eventually.of_forall hθb)
  have hsplit : B (t + 1) = (fun ω => R / q * B t ω) * θ (t + 1) + e (t + 1) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, hrec ω]
  rw [hsplit]
  have h1 := condExp_add hprod hei (ℱ t)
  have h2 := condExp_mul_of_stronglyMeasurable_left hfm hprod hθi
  filter_upwards [h1, h2, hθ, he] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.mul_apply, h3, h4, Pi.zero_apply, add_zero]
  field_simp

/-- **Example 2.2.1** in `L¹` (Miao, p. 50): the classes of the bursting bubble satisfy (2.4)
for the conditional expectations `condExpSystemL1_real`, so the abstract results above apply
(a nonzero such bubble violates (2.5), `eq_2_5_bubble_fails`). -/
theorem example_2_2_1_bubble_L1 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {R : ℝ} {B : ℕ → Ω → ℝ} (t : ℕ)
    (hBi : ∀ s, Integrable (B s) μ) (hB : μ[B (t + 1) | ℱ t] =ᵐ[μ] fun ω => R * B t ω) :
    (condExpSystemL1_real ℱ μ).E t ((hBi (t + 1)).toL1 _) = R • (hBi t).toL1 _ := by
  apply Lp.ext
  have h1 := condExpSystemL1_ae_eq ℝ ℱ μ t ((hBi (t + 1)).toL1 _)
  have h2 : μ[⇑((hBi (t + 1)).toL1 (B (t + 1))) | ℱ t] =ᵐ[μ] μ[B (t + 1) | ℱ t] :=
    condExp_congr_ae (Integrable.coeFn_toL1 _)
  have h3 := Lp.coeFn_smul R ((hBi t).toL1 (B t))
  have h4 := Integrable.coeFn_toL1 (hBi t)
  change _ =ᵐ[μ] _
  filter_upwards [h1, h2, hB, h3, h4] with ω e1 e2 e3 e4 e5
  rw [condExpSystemL1_real, e1, e2, e3, e4, Pi.smul_apply, e5, smul_eq_mul]

end Miao.NewKeynesian
