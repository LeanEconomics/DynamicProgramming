/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUEulerSufficiency
import InfiniteHorizonDP.CSDeterministic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.ConditionalExpectation

/-!
# Example 7.5.1 (Phelps 1962; Levhari–Srinivasan 1969)

Miao, §7.5, pp. 227–228: `max E Σ βᵗ u(c_t)` with CRRA `u(c) = c^{1−γ}/(1−γ)` (`log c` at
`γ = 1`, `cs_crra` from §6.6.2), `x_{t+1} = R_{t+1}(x_t − c_t)`, `x₀ > 0`, returns `R_t > 0`.

* `eq_7_39`: the policy `c = Ax` with `A = 1 − (βm)^{1/γ}`, `m = E[R^{1−γ}]`, solves the Euler
  equation after `E_t` is taken, `A^{−γ}x^{−γ} = β A^{−γ}(x − Ax)^{−γ} m`; `eq_7_39_unique`: it is
  the only `A ∈ (0, 1)` that does. `example_7_5_1_log`: `γ = 1` gives `A = 1 − β`.
  `example_7_5_1_A_mem`: `A ∈ (0, 1)` iff `0 < βm < 1` (for `βm ≥ 0`, as here).
* `example_7_5_1_tvc_det`: `βᵗA^{−γ}(1 − A)^{t(1−γ)}x₀^{1−γ}mᵗ = A^{−γ}x₀^{1−γ}(1 − A)ᵗ → 0`.
* The stochastic model in the Euler class (**the book's change of variables**, p. 221): the
  state is the saving `y_t = x_{t−1} − c_{t−1}` (with `R_0 = 1`, `y_0 = x₀`), so
  `x_t = R_t y_t`, `c_t = R_t y_t − y_{t+1}` and `u(y, R, y′) = u(Ry − y′)` with
  `Γ(y, R) = {y′ : 0 ≤ y′ < Ry}` (`eu_phelpsModel`); then `X = ℝ₊`,
  `u_x = R u′(c) > 0`, `u_a = −u′(c) < 0`. `eu_phelpsCash`, `eu_phelpsState`: the cash on hand and
  the state under `c_t = Ax_t`.
* `example_7_5_1_cash_rpow` and `example_7_5_1_tvc_formula`: the printed computation,
  `E[βᵗc_t^{−γ}x_t] = βᵗA^{−γ}(1 − A)^{t(1−γ)}x₀^{1−γ}E[Π_{s=1}^t R_s^{1−γ}]` (correct);
  `example_7_5_1_prod_moment`: `E[Π_{s=1}^t R_s^{1−γ}] = mᵗ` when `E_t[R_{t+1}^{1−γ}] = m`
  (`example_7_5_1_condmoment`: this holds when `R_{t+1}` is independent of `ℱ_t`);
  `example_7_5_1_tvc`: the transversality condition of the book holds.
* `example_7_5_1_euler`: the policy satisfies the Euler equation (7.34); `example_7_5_1`:
  it is optimal, by the sufficiency argument of Theorem 7.5.2 (`eu_euler_sufficient`).

**Departures.** (1) The book's "iid" is used only through `E_t[R_{t+1}^{1−γ}] = m`; the
integrability of `R_{t+1}^{1−γ}`, of `Π_{s ≤ t} R_s^{1−γ}` and of `(x_t)^{−γ}R_{t+1}^{1−γ}` is
assumed (it does not follow from iid without moment conditions such as `E[R^{−γ}] < ∞`).
(2) Theorem 7.5.2 does not apply verbatim: off the graph of `Γ` (`c ≤ 0`) the reward is not
defined (it is `−∞` for `γ ≥ 1`), so Assumptions 7.3.2–7.3.4 fail on `X × X`, and the strict part
of Assumption 7.3.3 fails on the graph (`u` is constant along `(y, y′) + s(1, R)`). The proof of
Theorem 7.5.2 needs only concavity on the graph (`eu_euler_sufficient`), which holds.
(3) Consumption is kept positive (`y′ < Ry`); for `γ < 1` the book allows `c = 0`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### The algebra of (7.39) -/

/-- **(7.39)** (Miao, p. 227): with `m = E[R^{1−γ}]`, `βm > 0` and `A = 1 − (βm)^{1/γ}`, the
Euler equation `A^{−γ}x^{−γ} = β E[R A^{−γ}R^{−γ}(x − Ax)^{−γ}] = β A^{−γ}(x − Ax)^{−γ} m`
holds for every `x > 0`. -/
theorem eq_7_39 {β m γ x : ℝ} (hγ : 0 < γ) (hbm : 0 < β * m) (hx : 0 < x) :
    (1 - (β * m) ^ (1 / γ)) ^ (-γ) * x ^ (-γ) =
      β * ((1 - (β * m) ^ (1 / γ)) ^ (-γ) * (x - (1 - (β * m) ^ (1 / γ)) * x) ^ (-γ) * m) := by
  set A := 1 - (β * m) ^ (1 / γ)
  have h1A : 1 - A = (β * m) ^ (1 / γ) := by simp [A]
  have hpos : 0 < (β * m) ^ (1 / γ) := Real.rpow_pos_of_pos hbm _
  have hxA : x - A * x = (1 - A) * x := by ring
  rw [hxA, Real.mul_rpow (by rw [h1A]; exact hpos.le) hx.le, h1A, ← Real.rpow_mul hbm.le]
  have e : 1 / γ * -γ = -1 := by field_simp
  rw [e, Real.rpow_neg_one]
  have hb0 : β ≠ 0 := left_ne_zero_of_mul hbm.ne'
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hbm.ne'
  field_simp

/-- **(7.39) is the only solution** in `(0, 1)` (Miao, p. 227): if `A ∈ (0, 1)` satisfies
`A^{−γ}x^{−γ} = β A^{−γ}(x − Ax)^{−γ} m` for some `x > 0`, then `A = 1 − (βm)^{1/γ}`. -/
theorem eq_7_39_unique {β m γ x A : ℝ} (hγ : 0 < γ) (hA0 : 0 < A) (hA1 : A < 1) (hx : 0 < x)
    (h : A ^ (-γ) * x ^ (-γ) = β * (A ^ (-γ) * (x - A * x) ^ (-γ) * m)) :
    A = 1 - (β * m) ^ (1 / γ) := by
  have h1A : 0 < 1 - A := by linarith
  have hxA : x - A * x = (1 - A) * x := by ring
  rw [hxA, Real.mul_rpow h1A.le hx.le] at h
  have hAp : 0 < A ^ (-γ) := Real.rpow_pos_of_pos hA0 _
  have hxp : 0 < x ^ (-γ) := Real.rpow_pos_of_pos hx _
  have h1 : 1 = β * m * (1 - A) ^ (-γ) := by
    have := h
    field_simp at this
    nlinarith [this]
  have h2 : (1 - A) ^ γ = β * m := by
    rw [Real.rpow_neg h1A.le] at h1
    have hne : (1 - A) ^ γ ≠ 0 := (Real.rpow_pos_of_pos h1A _).ne'
    field_simp at h1
    linarith
  have h3 : (β * m) ^ (1 / γ) = 1 - A := by
    rw [← h2, one_div, Real.rpow_rpow_inv h1A.le hγ.ne']
  linarith

/-- **Example 7.5.1, log utility** (Miao, p. 228): for `γ = 1`, `E[R^{1−γ}] = 1`, so
`A = 1 − β`. -/
theorem example_7_5_1_log {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (R : Ω → ℝ) (β : ℝ) :
    1 - (β * ∫ ω, R ω ^ ((1 : ℝ) - 1) ∂P) ^ (1 / (1 : ℝ)) = 1 - β := by
  simp

/-- **Example 7.5.1, `A ∈ (0, 1)`** (Miao, p. 228): for `γ > 0` and `βm ≥ 0`,
`A = 1 − (βm)^{1/γ} ∈ (0, 1)` iff `0 < βm < 1` (equivalently `0 < (βm)^{1/γ} < 1`). -/
theorem example_7_5_1_A_mem {β m γ : ℝ} (hγ : 0 < γ) (hbm : 0 ≤ β * m) :
    (0 < 1 - (β * m) ^ (1 / γ) ∧ 1 - (β * m) ^ (1 / γ) < 1) ↔ (0 < β * m ∧ β * m < 1) := by
  have hg : 0 < 1 / γ := by positivity
  constructor
  · rintro ⟨h0, h1⟩
    have hp : 0 < (β * m) ^ (1 / γ) := by linarith
    have hbm' : 0 < β * m := by
      rcases hbm.eq_or_lt with h | h
      · rw [← h, Real.zero_rpow hg.ne'] at hp; exact absurd hp (lt_irrefl 0)
      · exact h
    refine ⟨hbm', ?_⟩
    have hlt : (β * m) ^ (1 / γ) < 1 := by linarith
    rcases (Real.rpow_lt_one_iff_of_pos hbm').1 hlt with h | h
    · linarith [h.2]
    · exact h.1
  · rintro ⟨h0, h1⟩
    exact ⟨by linarith [Real.rpow_lt_one hbm h1 hg], by linarith [Real.rpow_pos_of_pos h0 (1 / γ)]⟩

/-- **The transversality computation, deterministic part** (Miao, p. 228): with
`A = 1 − (βm)^{1/γ} ∈ (0, 1)`,
`βᵗ A^{−γ}(1 − A)^{t(1−γ)} x₀^{1−γ} mᵗ = A^{−γ} x₀^{1−γ} (1 − A)ᵗ`, which tends to `0`. -/
theorem example_7_5_1_tvc_det {β m γ x₀ : ℝ} (hγ : 0 < γ) (hbm : 0 < β * m)
    (hbm1 : β * m < 1) :
    (∀ t : ℕ, β ^ t * (1 - (β * m) ^ (1 / γ)) ^ (-γ) *
      ((β * m) ^ (1 / γ)) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) * m ^ t =
      (1 - (β * m) ^ (1 / γ)) ^ (-γ) * x₀ ^ (1 - γ) * ((β * m) ^ (1 / γ)) ^ t) ∧
    Tendsto (fun t : ℕ => (1 - (β * m) ^ (1 / γ)) ^ (-γ) * x₀ ^ (1 - γ) *
      ((β * m) ^ (1 / γ)) ^ t) atTop (𝓝 0) := by
  set q := (β * m) ^ (1 / γ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hbm _
  have hq1 : q < 1 := Real.rpow_lt_one hbm.le hbm1 (by positivity)
  have hqγ : q ^ γ = β * m := by rw [hq, one_div, Real.rpow_inv_rpow hbm.le hγ.ne']
  refine ⟨fun t => ?_, ?_⟩
  · have e1 : q ^ ((t : ℝ) * (1 - γ)) = (q ^ (1 - γ)) ^ t := by
      rw [mul_comm, Real.rpow_mul_natCast hq0.le]
    have e2 : β * m * q ^ (1 - γ) = q := by
      rw [← hqγ, ← Real.rpow_add hq0]; simp
    rw [e1]
    calc β ^ t * (1 - q) ^ (-γ) * (q ^ (1 - γ)) ^ t * x₀ ^ (1 - γ) * m ^ t
        = (1 - q) ^ (-γ) * x₀ ^ (1 - γ) * (β * m * q ^ (1 - γ)) ^ t := by ring
      _ = _ := by rw [e2]
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul
      ((1 - q) ^ (-γ) * x₀ ^ (1 - γ))
    simpa using this

/-! ### CRRA utility -/

/-- The derivative of CRRA utility: `u′(c) = c^{−γ}` for `c > 0`. -/
theorem eu_crra_hasDerivAt {γ c : ℝ} (hc : 0 < c) : HasDerivAt (cs_crra γ) (c ^ (-γ)) c := by
  by_cases h1 : γ = 1
  · subst h1
    have : cs_crra 1 = Real.log := funext fun x => by simp [cs_crra]
    rw [this, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hc.ne'
  · have hp : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have : cs_crra γ = fun x => x ^ (1 - γ) / (1 - γ) := funext fun x => by simp [cs_crra, h1]
    rw [this]
    have h := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
    refine h.congr_deriv ?_
    have e : 1 - γ - 1 = -γ := by ring
    rw [e]
    field_simp

/-- CRRA utility is concave on `(0, ∞)` (from the tangent-line inequality `cs_crra_tangent`). -/
theorem eu_crra_concave {γ : ℝ} (hγ : 0 < γ) : ConcaveOn ℝ (Set.Ioi 0) (cs_crra γ) := by
  refine ⟨convex_Ioi 0, fun a ha b hb θ η hθ hη hs => ?_⟩
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  set c := θ • a + η • b
  have hc : 0 < c := by
    simp only [c, smul_eq_mul]
    rcases hθ.eq_or_lt with h | h
    · subst h; simp only [zero_add] at hs; subst hs; simpa using hb'
    · nlinarith [mul_pos h ha']
  have h1 := cs_crra_tangent hγ hc ha'
  have h2 := cs_crra_tangent hγ hc hb'
  have e : θ * (a - c) + η * (b - c) = 0 := by
    simp only [c, smul_eq_mul]
    have : η = 1 - θ := by linarith
    subst this; ring
  simp only [smul_eq_mul]
  have h1' := mul_le_mul_of_nonneg_left h1 hθ
  have h2' := mul_le_mul_of_nonneg_left h2 hη
  have e2 : θ * (c ^ (-γ) * (a - c)) + η * (c ^ (-γ) * (b - c)) = 0 := by
    linear_combination c ^ (-γ) * e
  have e3 : θ * cs_crra γ c + η * cs_crra γ c = cs_crra γ c := by rw [← add_mul, hs, one_mul]
  linarith

/-! ### The model in the Euler class -/

/-- **Example 7.5.1 in the Euler class** (Miao, pp. 221, 227): the state is the saving
`y = x − c ≥ 0` carried into the period, the shock is the return `R`, the choice is next
period's saving `y′ ∈ [0, Ry)` and the reward is `u(Ry − y′)`. -/
noncomputable def eu_phelpsModel (γ β : ℝ) : eu_EulerModel 1 ℝ where
  X := {y | 0 ≤ y 0}
  Q := 0
  Γ := fun y R => {y' | 0 ≤ y' 0 ∧ y' 0 < R * y 0}
  u := fun y R y' => cs_crra γ (R * y 0 - y' 0)
  β := β

/-- The partial derivatives of the reward of `eu_phelpsModel` at a point with consumption
`c = R y₀ − y′₀ > 0`: the reward is differentiable and its derivative applied to `v` is
`c^{−γ}(R v₁ − v₂)`. -/
theorem eu_phelps_fderiv {γ β R : ℝ} {p : (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hc : 0 < R * p.1 0 - p.2 0) :
    DifferentiableAt ℝ ((eu_phelpsModel γ β).uu R) p ∧
      ∀ v, fderiv ℝ ((eu_phelpsModel γ β).uu R) p v =
        (R * p.1 0 - p.2 0) ^ (-γ) * (R * v.1 0 - v.2 0) := by
  have hg : DifferentiableAt ℝ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => R * q.1 0 - q.2 0) p := by
    fun_prop
  have hd : DifferentiableAt ℝ ((eu_phelpsModel γ β).uu R) p := by
    have := (eu_crra_hasDerivAt (γ := γ) hc).differentiableAt.comp p hg
    exact this
  refine ⟨hd, fun v => ?_⟩
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hd' : HasFDerivAt ((eu_phelpsModel γ β).uu R) (fderiv ℝ ((eu_phelpsModel γ β).uu R) p)
      (p + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have hin : HasDerivAt (fun s : ℝ => R * (p + s • v).1 0 - (p + s • v).2 0)
      (R * v.1 0 - v.2 0) 0 := by
    have : (fun s : ℝ => R * (p + s • v).1 0 - (p + s • v).2 0) =
        fun s => (R * p.1 0 - p.2 0) + s * (R * v.1 0 - v.2 0) := by
      funext s; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (R * v.1 0 - v.2 0)).const_add
      (R * p.1 0 - p.2 0)
  have hc' : 0 < R * (p + (0 : ℝ) • v).1 0 - (p + (0 : ℝ) • v).2 0 := by simpa using hc
  have h2 := (eu_crra_hasDerivAt (γ := γ) hc').comp (0 : ℝ) hin
  have huniq := h1.unique h2
  simp only [zero_smul, add_zero] at huniq
  rw [huniq]

/-- The cash on hand under the policy `c_t = A x_t`: `x₀` given,
`x_{t+1} = R_{t+1}(1 − A)x_t`. -/
noncomputable def eu_phelpsCash {Ω : Type*} (R : ℕ → Ω → ℝ) (A x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => R (t + 1) ω * ((1 - A) * eu_phelpsCash R A x₀ t ω)

/-- The state (saving carried into the period) under the policy `c_t = A x_t`: `y₀ = x₀`,
`y_{t+1} = (1 − A)x_t`. -/
noncomputable def eu_phelpsState {Ω : Type*} (R : ℕ → Ω → ℝ) (A x₀ : ℝ) : ℕ → Ω → (Fin 1 → ℝ)
  | 0 => fun _ _ => x₀
  | t + 1 => fun ω _ => (1 - A) * eu_phelpsCash R A x₀ t ω

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ m0}

/-- The cash on hand is positive. -/
theorem eu_phelpsCash_pos {R : ℕ → Ω → ℝ} {A x₀ : ℝ} (hR : ∀ t ω, 0 < R t ω) (hA : A < 1)
    (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) : 0 < eu_phelpsCash R A x₀ t ω := by
  induction t with
  | zero => exact hx₀
  | succ t ih =>
    have : 0 < 1 - A := by linarith
    exact mul_pos (hR _ ω) (mul_pos this ih)

/-- With `R₀ = 1`, the cash on hand is `x_t = R_t y_t`. -/
theorem eu_phelps_cash_eq {R : ℕ → Ω → ℝ} {A x₀ : ℝ} (hR0 : ∀ ω, R 0 ω = 1) (t : ℕ) (ω : Ω) :
    R t ω * eu_phelpsState R A x₀ t ω 0 = eu_phelpsCash R A x₀ t ω := by
  cases t with
  | zero => simp [eu_phelpsState, eu_phelpsCash, hR0]
  | succ t => rfl

/-- The cash on hand is adapted. -/
theorem eu_phelpsCash_measurable {R : ℕ → Ω → ℝ} {A x₀ : ℝ} (hRm : ∀ t, Measurable[ℱ t] (R t))
    (t : ℕ) : Measurable[ℱ t] (eu_phelpsCash R A x₀ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (hRm (t + 1)).mul ((ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl).const_mul _)

/-- **The printed computation, pathwise** (Miao, p. 228): `x_t = (1 − A)ᵗ x₀ Π_{s=1}^t R_s`, so
`x_t^{1−γ} = (1 − A)^{t(1−γ)} x₀^{1−γ} Π_{s=1}^t R_s^{1−γ}`. -/
theorem example_7_5_1_cash_rpow {R : ℕ → Ω → ℝ} {A x₀ γ : ℝ} (hR : ∀ t ω, 0 < R t ω)
    (hA : A < 1) (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) :
    eu_phelpsCash R A x₀ t ω ^ (1 - γ) = (1 - A) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) *
      ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) := by
  have h1A : 0 < 1 - A := by linarith
  induction t with
  | zero => simp [eu_phelpsCash]
  | succ t ih =>
    have hc := eu_phelpsCash_pos hR hA hx₀ t ω
    simp only [eu_phelpsCash]
    rw [Real.mul_rpow (hR _ ω).le (mul_pos h1A hc).le, Real.mul_rpow h1A.le hc.le, ih,
      Finset.prod_range_succ]
    have e : (1 - A) ^ (((t + 1 : ℕ) : ℝ) * (1 - γ)) =
        (1 - A) ^ ((t : ℝ) * (1 - γ)) * (1 - A) ^ (1 - γ) := by
      rw [← Real.rpow_add h1A]; congr 1; push_cast; ring
    rw [e]
    ring

/-- **`E_t[R_{t+1}^{1−γ}] = m` from independence** (Miao, p. 228: "`R_t` is iid"): if
`R_{t+1}` is independent of `ℱ_t` and `E[R_{t+1}^{1−γ}] = m`, then `E_t[R_{t+1}^{1−γ}] = m`
almost surely. -/
theorem example_7_5_1_condmoment [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ m : ℝ} (t : ℕ)
    (hRm : Measurable (R (t + 1)))
    (hind : Indep (MeasurableSpace.comap (R (t + 1)) inferInstance) (ℱ t) P)
    (hm : ∫ ω, R (t + 1) ω ^ (1 - γ) ∂P = m) :
    P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m := by
  have hle : MeasurableSpace.comap (R (t + 1)) inferInstance ≤ m0 := hRm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap (R (t + 1)) inferInstance]
      fun ω => R (t + 1) ω ^ (1 - γ) :=
    ((Measurable.pow_const measurable_id (1 - γ)).comp (comap_measurable (R (t + 1)))
      ).stronglyMeasurable
  have := condExp_indep_eq hle (ℱ.le t) hsm hind
  rw [hm] at this
  exact this

/-- **`E[Π_{s=1}^t R_s^{1−γ}] = mᵗ`** (Miao, p. 228): if `E_t[R_{t+1}^{1−γ}] = m` almost surely,
`R` is adapted and the partial products are integrable. -/
theorem example_7_5_1_prod_moment [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ m : ℝ}
    (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI2 : ∀ t, Integrable (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) P)
    (t : ℕ) : ∫ ω, ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) ∂P = m ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmeas : StronglyMeasurable[ℱ t] fun ω => ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) := by
      refine (Finset.measurable_prod _ fun s hs => ?_).stronglyMeasurable
      have hst : s + 1 ≤ t := by have := Finset.mem_range.1 hs; omega
      exact (((hRm (s + 1)).mono (ℱ.mono hst) le_rfl).pow_const _)
    have hprod : (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) =
        fun ω => (∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ)) * R (t + 1) ω ^ (1 - γ) := by
      funext ω; rw [Finset.prod_range_succ]
    obtain ⟨_, heq⟩ := OCModel.oc_integral_mul_condExp hmeas (by rw [← hprod]; exact hI2 t)
      (hI1 t)
    have hae : (fun ω => (∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ)) *
        (P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t]) ω) =ᵐ[P]
        fun ω => (∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ)) * m := by
      filter_upwards [hcm t] with ω hω
      rw [hω]
    rw [hprod, heq, integral_congr_ae hae, integral_mul_const, ih, pow_succ]

/-- **The transversality computation as printed** (Miao, p. 228): with `c_t = A x_t`,
`E[βᵗ c_t^{−γ} x_t] = βᵗ A^{−γ}(1 − A)^{t(1−γ)} x₀^{1−γ} E[Π_{s=1}^t R_s^{1−γ}]`. -/
theorem example_7_5_1_tvc_formula {R : ℕ → Ω → ℝ} {A x₀ γ β : ℝ} (hR : ∀ t ω, 0 < R t ω)
    (hA0 : 0 < A) (hA : A < 1) (hx₀ : 0 < x₀) (t : ℕ) :
    ∫ ω, β ^ t * ((A * eu_phelpsCash R A x₀ t ω) ^ (-γ) * eu_phelpsCash R A x₀ t ω) ∂P =
      β ^ t * A ^ (-γ) * (1 - A) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) *
        ∫ ω, ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) ∂P := by
  have hpt : ∀ ω, β ^ t * ((A * eu_phelpsCash R A x₀ t ω) ^ (-γ) * eu_phelpsCash R A x₀ t ω) =
      β ^ t * A ^ (-γ) * (1 - A) ^ ((t : ℝ) * (1 - γ)) * x₀ ^ (1 - γ) *
        ∏ s ∈ Finset.range t, R (s + 1) ω ^ (1 - γ) := by
    intro ω
    have hc := eu_phelpsCash_pos hR hA hx₀ t ω
    have e : eu_phelpsCash R A x₀ t ω ^ (-γ) * eu_phelpsCash R A x₀ t ω =
        eu_phelpsCash R A x₀ t ω ^ (1 - γ) := by
      rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add_one hc.ne']
    rw [Real.mul_rpow hA0.le hc.le, mul_assoc (A ^ (-γ)), e,
      example_7_5_1_cash_rpow hR hA hx₀ t ω]
    ring
  simp only [hpt]
  rw [integral_const_mul]

/-- **The transversality condition of Example 7.5.1** (Miao, p. 228):
`lim_t E[βᵗ c_t^{−γ} x_t] = 0` when `0 < βm < 1`, `A = 1 − (βm)^{1/γ}`, given
`E_t[R_{t+1}^{1−γ}] = m` and the integrability of the partial products. -/
theorem example_7_5_1_tvc [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ β m x₀ A : ℝ}
    (hγ : 0 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) (hA : A = 1 - (β * m) ^ (1 / γ))
    (hx₀ : 0 < x₀) (hR : ∀ t ω, 0 < R t ω) (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI2 : ∀ t, Integrable (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) P) :
    Tendsto (fun t : ℕ => ∫ ω, β ^ t * ((A * eu_phelpsCash R A x₀ t ω) ^ (-γ) *
      eu_phelpsCash R A x₀ t ω) ∂P) atTop (𝓝 0) := by
  subst hA
  have hA := (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  obtain ⟨hdet, hlim⟩ := example_7_5_1_tvc_det (x₀ := x₀) hγ hbm hbm1
  refine hlim.congr fun t => ?_
  rw [example_7_5_1_tvc_formula hR hA.1 hA.2 hx₀ t,
    example_7_5_1_prod_moment hRm hcm hI1 hI2 t]
  have e : 1 - (1 - (β * m) ^ (1 / γ)) = (β * m) ^ (1 / γ) := by ring
  rw [e]
  exact (hdet t).symm

/-- The derivatives of the reward along the policy `c_t = Ax_t` (Miao, p. 227): consumption is
`c_t = R_t y_t − y_{t+1} = A x_t > 0`, `u_a = −c_t^{−γ}` and `u_x = c_t^{−γ} R_t`. -/
theorem eu_phelps_derivs {R : ℕ → Ω → ℝ} {γ β A x₀ : ℝ} (hR : ∀ t ω, 0 < R t ω)
    (hR0 : ∀ ω, R 0 ω = 1) (hA0 : 0 < A) (hA1 : A < 1) (hx₀ : 0 < x₀) (t : ℕ) (ω : Ω) :
    R t ω * eu_phelpsState R A x₀ t ω 0 - eu_phelpsState R A x₀ (t + 1) ω 0 =
      A * eu_phelpsCash R A x₀ t ω ∧
    DifferentiableAt ℝ ((eu_phelpsModel γ β).uu (R t ω))
      (eu_phelpsState R A x₀ t ω, eu_phelpsState R A x₀ (t + 1) ω) ∧
    (eu_phelpsModel γ β).ua (eu_phelpsState R A x₀ t ω) (R t ω)
      (eu_phelpsState R A x₀ (t + 1) ω) 0 = -(A * eu_phelpsCash R A x₀ t ω) ^ (-γ) ∧
    (eu_phelpsModel γ β).ux (eu_phelpsState R A x₀ t ω) (R t ω)
      (eu_phelpsState R A x₀ (t + 1) ω) 0 = (A * eu_phelpsCash R A x₀ t ω) ^ (-γ) * R t ω := by
  have hcons : R t ω * eu_phelpsState R A x₀ t ω 0 - eu_phelpsState R A x₀ (t + 1) ω 0 =
      A * eu_phelpsCash R A x₀ t ω := by
    rw [eu_phelps_cash_eq hR0]
    simp only [eu_phelpsState]
    ring
  have hc := eu_phelpsCash_pos hR hA1 hx₀ t ω
  have hf := eu_phelps_fderiv (γ := γ) (β := β) (R := R t ω)
    (p := (eu_phelpsState R A x₀ t ω, eu_phelpsState R A x₀ (t + 1) ω))
    (by rw [hcons]; positivity)
  refine ⟨hcons, hf.1, ?_, ?_⟩
  · simp only [eu_EulerModel.ua]
    rw [hf.2, hcons]
    simp
  · simp only [eu_EulerModel.ux]
    rw [hf.2, hcons]
    simp

/-- **Example 7.5.1, the Euler equation** (Miao, p. 227): the policy `c_t = A x_t` with
`A = 1 − (βm)^{1/γ}` satisfies (7.34) in the Euler-class form,
`−c_t^{−γ} + β E_t[R_{t+1} c_{t+1}^{−γ}] = 0`, given `E_t[R_{t+1}^{1−γ}] = m` and the
integrability of `R_{t+1}^{1−γ}` and of `((1 − A)x_t)^{−γ} R_{t+1}^{1−γ}`. -/
theorem example_7_5_1_euler [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ β m x₀ A : ℝ}
    (hγ : 0 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) (hA : A = 1 - (β * m) ^ (1 / γ))
    (hx₀ : 0 < x₀) (hR : ∀ t ω, 0 < R t ω) (hR0 : ∀ ω, R 0 ω = 1)
    (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI3 : ∀ t, Integrable (fun ω => ((1 - A) * eu_phelpsCash R A x₀ t ω) ^ (-γ) *
      R (t + 1) ω ^ (1 - γ)) P) :
    (eu_phelpsModel γ β).IsEuler P ℱ R (eu_phelpsState R A x₀) := by
  have hA01 : 0 < A ∧ A < 1 := by rw [hA]; exact (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  have h1A : 0 < 1 - A := by linarith [hA01.2]
  intro t i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  set f : Ω → ℝ := fun ω => A ^ (-γ) * ((1 - A) * eu_phelpsCash R A x₀ t ω) ^ (-γ) with hf
  have hux : (fun ω' => (eu_phelpsModel γ β).ux (eu_phelpsState R A x₀ (t + 1) ω') (R (t + 1) ω')
      (eu_phelpsState R A x₀ (t + 2) ω') 0) = fun ω' => f ω' * R (t + 1) ω' ^ (1 - γ) := by
    funext ω'
    rw [(eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA01.1 hA01.2 hx₀ (t + 1) ω').2.2.2]
    have hct := eu_phelpsCash_pos hR hA01.2 hx₀ t ω'
    have hR1 := hR (t + 1) ω'
    have e : eu_phelpsCash R A x₀ (t + 1) ω' =
        R (t + 1) ω' * ((1 - A) * eu_phelpsCash R A x₀ t ω') := rfl
    rw [e, show A * (R (t + 1) ω' * ((1 - A) * eu_phelpsCash R A x₀ t ω')) =
        A * ((1 - A) * eu_phelpsCash R A x₀ t ω') * R (t + 1) ω' by ring,
      Real.mul_rpow (mul_pos hA01.1 (mul_pos h1A hct)).le hR1.le,
      Real.mul_rpow hA01.1.le (mul_pos h1A hct).le]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add_one hR1.ne']
    simp only [hf]
    ring
  have hfm : StronglyMeasurable[ℱ t] f :=
    (((eu_phelpsCash_measurable hRm t).const_mul (1 - A)).pow_const (-γ) |>.const_mul
      (A ^ (-γ))).stronglyMeasurable
  have hfg : Integrable (fun ω => f ω * R (t + 1) ω ^ (1 - γ)) P := by
    refine ((hI3 t).const_mul (A ^ (-γ))).congr (Eventually.of_forall fun ω => ?_)
    simp only [hf]; ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hfm hfg (hI1 t)
  rw [hux]
  filter_upwards [hpull, hcm t] with ω h1 h2
  have h1' : (P[fun ω => f ω * R (t + 1) ω ^ (1 - γ) | ℱ t]) ω = f ω * m := by
    rw [show (fun ω => f ω * R (t + 1) ω ^ (1 - γ)) = f * fun ω => R (t + 1) ω ^ (1 - γ) from rfl,
      h1, Pi.mul_apply, h2]
  rw [h1', (eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA01.1 hA01.2 hx₀ t ω).2.2.1]
  simp only [Pi.zero_apply, hf]
  have hct := eu_phelpsCash_pos hR hA01.2 hx₀ t ω
  have key := eq_7_39 hγ hbm hct
  rw [← hA] at key
  rw [Real.mul_rpow hA01.1.le hct.le, key, show eu_phelpsCash R A x₀ t ω -
    A * eu_phelpsCash R A x₀ t ω = (1 - A) * eu_phelpsCash R A x₀ t ω by ring]
  simp only [eu_phelpsModel]
  ring

/-- **Example 7.5.1, optimality** (Miao, p. 228): the policy `c_t = A x_t`,
`A = 1 − (βm)^{1/γ}`, `0 < βm < 1`, is optimal: by the sufficiency argument of Theorem 7.5.2
(`eu_euler_sufficient`, with concavity on the graph of `Γ`), the Euler equation and the
transversality condition, every feasible plan `x` (with the integrability `EulerInt`) has
`S_T(x) ≤ S_T(x*) + w_T`, `w_T → 0`. The shock is the return process `R` (adapted, positive,
`R_0 = 1`) with `E_t[R_{t+1}^{1−γ}] = m`. -/
theorem example_7_5_1 [IsProbabilityMeasure P] {R : ℕ → Ω → ℝ} {γ β m x₀ A : ℝ}
    (hγ : 0 < γ) (hβ : 0 < β ∧ β < 1) (hbm : 0 < β * m) (hbm1 : β * m < 1)
    (hA : A = 1 - (β * m) ^ (1 / γ)) (hx₀ : 0 < x₀) (hR : ∀ t ω, 0 < R t ω)
    (hR0 : ∀ ω, R 0 ω = 1) (hRm : ∀ t, Measurable[ℱ t] (R t))
    (hcm : ∀ t, P[fun ω => R (t + 1) ω ^ (1 - γ) | ℱ t] =ᵐ[P] fun _ => m)
    (hI1 : ∀ t, Integrable (fun ω => R (t + 1) ω ^ (1 - γ)) P)
    (hI2 : ∀ t, Integrable (fun ω => ∏ s ∈ Finset.range (t + 1), R (s + 1) ω ^ (1 - γ)) P)
    (hI3 : ∀ t, Integrable (fun ω => ((1 - A) * eu_phelpsCash R A x₀ t ω) ^ (-γ) *
      R (t + 1) ω ^ (1 - γ)) P)
    {x : ℕ → Ω → (Fin 1 → ℝ)} (hx : (eu_phelpsModel γ β).IsPlan ℱ R (fun _ => x₀) x)
    (hint : eu_EulerModel.EulerInt P R (eu_phelpsModel γ β) (eu_phelpsState R A x₀) x) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, (eu_phelpsModel γ β).eu_partialJ P R x T ≤
        (eu_phelpsModel γ β).eu_partialJ P R (eu_phelpsState R A x₀) T + w T := by
  have hA01 : 0 < A ∧ A < 1 := by rw [hA]; exact (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  have h1A : 0 < 1 - A := by linarith [hA01.2]
  have hD := fun t ω => eu_phelps_derivs (γ := γ) (β := β) hR hR0 hA01.1 hA01.2 hx₀ t ω
  have hcpos := fun t ω => eu_phelpsCash_pos hR hA01.2 hx₀ t ω
  have hst : ∀ t ω, 0 < eu_phelpsState R A x₀ t ω 0 := fun t ω => by
    cases t with
    | zero => exact hx₀
    | succ t => exact mul_pos h1A (hcpos t ω)
  -- the candidate is a feasible plan
  have hplan : (eu_phelpsModel γ β).IsPlan ℱ R (fun _ => x₀) (eu_phelpsState R A x₀) := by
    refine ⟨fun ω => rfl, fun t => ?_, fun t ω => ⟨(hst t ω).le, (hst (t + 1) ω).le, ?_⟩⟩
    · change Measurable[ℱ t] fun ω (_ : Fin 1) => (1 - A) * eu_phelpsCash R A x₀ t ω
      exact (continuous_pi fun _ => continuous_id).measurable.comp
        ((eu_phelpsCash_measurable hRm t).const_mul _)
    · have := (hD t ω).1
      have := mul_pos hA01.1 (hcpos t ω)
      linarith
  -- the graph of `Γ` and concavity on it
  set C : ℝ → Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
    fun r => {p | 0 ≤ p.1 0 ∧ 0 ≤ p.2 0 ∧ p.2 0 < r * p.1 0} with hC
  have hcon : ∀ r, ConcaveOn ℝ (C r) ((eu_phelpsModel γ β).uu r) := by
    intro r
    have hconv : Convex ℝ (C r) := by
      intro p hp q hq a b ha hb hab
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
      · nlinarith [mul_nonneg ha hp1, mul_nonneg hb hq1]
      · nlinarith [mul_nonneg ha hp2, mul_nonneg hb hq2]
      rcases ha.eq_or_lt with h | h
      · subst h; simp only [zero_add] at hab; subst hab; simpa using hq3
      · nlinarith [mul_pos h (sub_pos.2 hp3), mul_nonneg hb (sub_pos.2 hq3).le]
    refine ⟨hconv, fun p hp q hq a b ha hb hab => ?_⟩
    have hcp : (0 : ℝ) < r * p.1 0 - p.2 0 := by linarith [hp.2.2]
    have hcq : (0 : ℝ) < r * q.1 0 - q.2 0 := by linarith [hq.2.2]
    have h := (eu_crra_concave hγ).2 (show r * p.1 0 - p.2 0 ∈ Set.Ioi (0 : ℝ) from hcp)
      (show r * q.1 0 - q.2 0 ∈ Set.Ioi (0 : ℝ) from hcq) ha hb hab
    simp only [smul_eq_mul] at h
    simp only [eu_EulerModel.uu, eu_phelpsModel, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    convert h using 2
    ring
  -- the transversality condition (7.35)
  have htvc : (eu_phelpsModel γ β).TVC735 P R (eu_phelpsState R A x₀) := by
    have hlim := example_7_5_1_tvc (P := P) hγ hbm hbm1 hA hx₀ hR hRm hcm hI1 hI2
    have := hlim.const_mul (-(1 - A))
    rw [mul_zero] at this
    unfold eu_EulerModel.TVC735
    refine this.congr fun T => ?_
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [eu_dot, Fin.sum_univ_one, (hD T ω).2.2.1]
    simp only [eu_phelpsState, eu_phelpsModel]
    ring
  refine eu_EulerModel.eu_euler_sufficient hβ.1.le hplan hx C hcon (fun t ω => ⟨?_, ?_⟩)
    (fun t ω => (hD t ω).2.1)
    (example_7_5_1_euler hγ hbm hbm1 hA hx₀ hR hR0 hRm hcm hI1 hI3) (fun t ω i => ?_)
    (fun t ω i => ?_) hint htvc
  · refine ⟨(hst t ω).le, (hst (t + 1) ω).le, ?_⟩
    have := (hD t ω).1
    have := mul_pos hA01.1 (hcpos t ω)
    linarith
  · exact ⟨(hx.2.2 t ω).1, (hx.2.2 t ω).2⟩
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [(hD (t + 1) ω).2.2.2]
    exact mul_nonneg (Real.rpow_pos_of_pos (mul_pos hA01.1 (hcpos _ ω)) _).le (hR _ ω).le
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    exact (hx.2.2 (t + 1) ω).1

end Miao.InfiniteHorizonDP
