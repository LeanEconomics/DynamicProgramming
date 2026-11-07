/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CSCARA
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exercise 7.7: the Schechtman–Escudero model as `T → ∞`, the limit policies

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `EXCARA`), namespace renamed.

Miao, §7.6, Exercise 7, p. 229. The exercise says "Let `T → ∞` in Exercise 8 of Chapter 6";
the Schechtman–Escudero (1977) model is **Exercise 9** of Chapter 6 (Exercise 6.8 is the
deterministic CRRA problem): exponential utility `−e^{−γc}`, iid income `y ∈ [y_min, y_max]` with
law `μ`, no borrowing constraint, cash on hand `x = Ra + y`. Chapter 6 (`ex_6_9`): with `n + 1`
periods to go, `v_n(x) = −A_n e^{−α_n x}`, `α_n = γ/Σ_{k ≤ n} R^{−k}`, and the saving
`s_{n+1}(x) = (γx + L_n)/(γ + α_n R)`, `L_n = ln(βA_nM_nα_nR/γ)`, `M_n = E e^{−α_n y}`.

The limit, for `R > 1` (`ex_7_7_limit`):
* `α_n → ᾱ = γ(1 − 1/R)` (`ex7_caraAbar`), so the marginal propensity to consume
  `1/Σ_{k ≤ n+1} R^{−k}` tends to `1 − 1/R`;
* `M_n → M̄ = E e^{−ᾱy}` (dominated convergence), and `ln A_{n+1} = c_n ln A_n + d_n` with
  `c_n = γ/(γ + α_nR) → c̄ = 1/R` and `d_n → d̄` (`ex7_cara_logA_rec`); by `ex7_affine_tendsto`,
  `ln A_n → d̄/(1 − c̄)`: `A_n → Ā = e^{d̄/(1 − c̄)}` (`ex7_caraAlim`);
* hence `L_n → L̄ = ln(βĀM̄ᾱR/γ)` and the saving policy converges pointwise,
  `s_{n+1}(x) → s̄(x) = (γx + L̄)/(γ + ᾱR) = x/R + L̄/(γR)` (`ex7_caraSbar`); consumption
  `c̄(x) = (1 − 1/R)x − L̄/(γR)`.
* `ex_7_7_bellman`: `V̄(x) = −Āe^{−ᾱx}` solves the infinite-horizon Bellman equation
  `V̄(x) = sup_s −e^{−γ(x−s)} + β E V̄(Rs + y)`, uniquely maximised at `s̄(x)`.

Optimality, and its failure without a no-Ponzi condition, are in `EXCARAMDP`.
-/

namespace Miao.Applications

open MeasureTheory Filter Topology

/-- **Affine recursions with converging coefficients**: if `a_{n+1} = c_n a_n + d_n`, `c_n ≥ 0`,
`c_n → c < 1` and `d_n → d`, then `a_n → d/(1 − c)`. -/
theorem ex7_affine_tendsto {a c d : ℕ → ℝ} {c₀ d₀ : ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hc : Tendsto c atTop (𝓝 c₀)) (hc1 : c₀ < 1) (hd : Tendsto d atTop (𝓝 d₀))
    (hrec : ∀ n, a (n + 1) = c n * a n + d n) : Tendsto a atTop (𝓝 (d₀ / (1 - c₀))) := by
  set ℓ := d₀ / (1 - c₀)
  have h1c : 0 < 1 - c₀ := by linarith
  have hℓ : ℓ = c₀ * ℓ + d₀ := by simp only [ℓ]; field_simp; ring
  have hc00 : 0 ≤ c₀ := ge_of_tendsto' hc hc0
  set q := (1 + c₀) / 2
  have hq1 : q < 1 := by simp only [q]; linarith
  have hq0 : 0 ≤ q := by simp only [q]; linarith
  set η : ℕ → ℝ := fun n => (c n - c₀) * ℓ + (d n - d₀)
  have hη : Tendsto η atTop (𝓝 0) := by
    have := ((hc.sub_const c₀).mul_const ℓ).add (hd.sub_const d₀)
    simpa using this
  have he : ∀ n, a (n + 1) - ℓ = c n * (a n - ℓ) + η n := fun n => by
    rw [hrec n]; simp only [η]; linear_combination (-1 : ℝ) * hℓ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hc.eventually (eventually_le_nhds
    (show c₀ < q by simp only [q]; linarith)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε * (1 - q) / 2 := by have : 0 < 1 - q := by linarith
                                      positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hη _ hδ
  set N := max N₀ N₁
  have hbound : ∀ k, |a (N + k) - ℓ| ≤ q ^ k * |a N - ℓ| + ε / 2 := by
    intro k
    induction k with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ k ih =>
      rw [← add_assoc, he]
      have hcn : c (N + k) ≤ q := hN₀ _ (by omega)
      have hηn : |η (N + k)| < ε * (1 - q) / 2 := by
        have := hN₁ (N + k) (by omega)
        rwa [Real.dist_eq, sub_zero] at this
      calc |c (N + k) * (a (N + k) - ℓ) + η (N + k)|
          ≤ c (N + k) * |a (N + k) - ℓ| + |η (N + k)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg (hc0 _)]
        _ ≤ q * (q ^ k * |a N - ℓ| + ε / 2) + ε * (1 - q) / 2 := by
            have h1 : c (N + k) * |a (N + k) - ℓ| ≤ q * (q ^ k * |a N - ℓ| + ε / 2) :=
              (mul_le_mul_of_nonneg_right hcn (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left ih hq0)
            linarith
        _ = q ^ (k + 1) * |a N - ℓ| + ε / 2 := by ring
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const |a N - ℓ|
  rw [zero_mul] at hgeo
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hgeo (ε / 2) (by positivity)
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq]
  have h1 := hbound (K + k)
  have h2 := hK (K + k) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg hq0 _) (abs_nonneg _))] at h2
  rw [← add_assoc] at h1
  linarith

/-! ### The limits of the coefficients -/

/-- The limit exponent `ᾱ = γ(1 − 1/R)`. -/
noncomputable def ex7_caraAbar (γ R : ℝ) : ℝ := γ * (1 - R⁻¹)

/-- `M̄ = E e^{−ᾱy}`. -/
noncomputable def ex7_caraMbar (γ R : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ y, Real.exp (-(ex7_caraAbar γ R * y)) ∂μ

/-- `c̄ = γ/(γ + ᾱR)` (`= 1/R`). -/
noncomputable def ex7_caraCbar (γ R : ℝ) : ℝ := γ / (γ + ex7_caraAbar γ R * R)

/-- `d̄ = ln(1 + γ/(ᾱR)) + c̄ ln(βM̄ᾱR/γ)`. -/
noncomputable def ex7_caraDbar (γ β R : ℝ) (μ : Measure ℝ) : ℝ :=
  Real.log (1 + γ / (ex7_caraAbar γ R * R)) +
    ex7_caraCbar γ R * Real.log (β * ex7_caraMbar γ R μ * ex7_caraAbar γ R * R / γ)

/-- The limit coefficient `Ā = e^{d̄/(1 − c̄)}`. -/
noncomputable def ex7_caraAlim (γ β R : ℝ) (μ : Measure ℝ) : ℝ :=
  Real.exp (ex7_caraDbar γ β R μ / (1 - ex7_caraCbar γ R))

/-- `L̄ = ln(βĀM̄ᾱR/γ)`. -/
noncomputable def ex7_caraLbar (γ β R : ℝ) (μ : Measure ℝ) : ℝ :=
  Real.log (β * ex7_caraAlim γ β R μ * ex7_caraMbar γ R μ * ex7_caraAbar γ R * R / γ)

/-- The limit saving policy `s̄(x) = (γx + L̄)/(γ + ᾱR)`. -/
noncomputable def ex7_caraSbar (γ β R : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (γ * x + ex7_caraLbar γ β R μ) / (γ + ex7_caraAbar γ R * R)

theorem ex7_caraAbar_pos {γ R : ℝ} (hγ : 0 < γ) (hR : 1 < R) : 0 < ex7_caraAbar γ R := by
  have : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  exact mul_pos hγ (by linarith)

/-- `γ + ᾱR = γR` and `c̄ = 1/R`. -/
theorem ex7_caraAbar_R {γ R : ℝ} (hR : 1 < R) :
    γ + ex7_caraAbar γ R * R = γ * R ∧ (0 < γ → ex7_caraCbar γ R = R⁻¹) := by
  have hR0 : R ≠ 0 := by linarith
  have e : γ + ex7_caraAbar γ R * R = γ * R := by
    simp only [ex7_caraAbar]; field_simp; ring
  refine ⟨e, fun hγ => ?_⟩
  rw [ex7_caraCbar, e]; field_simp

/-- `e^{−αy}` is integrable for `μ` concentrated on a bounded interval, with
`e^{−αy} ≤ e^{|α|(|y_min| + |y_max|)}` there. -/
theorem ex7_exp_bound {ymin ymax α y : ℝ} (hy : y ∈ Set.Icc ymin ymax) :
    Real.exp (-(α * y)) ≤ Real.exp (|α| * (|ymin| + |ymax|)) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : |y| ≤ |ymin| + |ymax| := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self ymax, abs_nonneg ymin, hy.2]
    · rw [abs_of_neg h]; linarith [neg_abs_le ymin, abs_nonneg ymax, hy.1]
  have h2 : -(α * y) ≤ |α| * |y| := by
    rw [← abs_mul]; exact neg_le_abs _
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg α))

theorem ex7_exp_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ] {ymin ymax : ℝ}
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (α : ℝ) :
    Integrable (fun y => Real.exp (-(α * y))) μ := by
  refine (integrable_const (Real.exp (|α| * (|ymin| + |ymax|)))).mono'
    (by fun_prop : Continuous fun y => Real.exp (-(α * y))).aestronglyMeasurable ?_
  filter_upwards [hμ] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact ex7_exp_bound hy

/-- The facts of Exercise 6.9 used below: `α_n = γ/Σ_{k ≤ n} R^{−k} ∈ (0, γ]`, `A_n > 0`,
`M_n > 0`. -/
theorem ex7_cara_facts {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (n : ℕ) :
    0 < cs_caraAlpha γ R n ∧ cs_caraAlpha γ R n ≤ γ ∧ 0 < cs_caraA γ β R μ n ∧
      0 < cs_caraM γ R μ n ∧ cs_caraAlpha γ R n = γ / ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k := by
  obtain ⟨hα, hA, hαS, -⟩ := (ex_6_9 hγ hβ hR hμ n).1
  refine ⟨hα, ?_, hA, cs_cara_M_pos hα hμ, hαS⟩
  rw [hαS]
  have h1 : 1 ≤ ∑ k ∈ Finset.range (n + 1), R⁻¹ ^ k := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero]
    have : 0 ≤ ∑ k ∈ Finset.range n, R⁻¹ ^ (k + 1) :=
      Finset.sum_nonneg fun k _ => pow_nonneg (inv_nonneg.2 hR.le) _
    linarith
  exact div_le_self hγ.le h1

/-- `α_n → ᾱ = γ(1 − 1/R)` for `R > 1`. -/
theorem ex7_cara_alpha_tendsto {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) :
    Tendsto (cs_caraAlpha γ R) atTop (𝓝 (ex7_caraAbar γ R)) := by
  have hR0 : 0 < R := by linarith
  have hi0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hi1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hgeo := ((hasSum_geometric_of_lt_one hi0 hi1).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  have h1 : (1 - R⁻¹)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have := (tendsto_const_nhds (x := γ)).div hgeo h1
  rw [div_inv_eq_mul] at this
  exact this.congr fun n => ((ex7_cara_facts hγ hβ hR0 hμ n).2.2.2.2).symm

/-- `M_n → M̄`, by dominated convergence. -/
theorem ex7_cara_M_tendsto {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) :
    Tendsto (cs_caraM γ R μ) atTop (𝓝 (ex7_caraMbar γ R μ)) := by
  have hR0 : 0 < R := by linarith
  have hα := ex7_cara_alpha_tendsto hγ hβ hR hμ
  refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (γ * (|ymin| + |ymax|)))
    (fun n => (by fun_prop : Continuous fun y =>
      Real.exp (-(cs_caraAlpha γ R n * y))).aestronglyMeasurable) (integrable_const _)
    (fun n => ?_) (Eventually.of_forall fun y => ?_)
  · filter_upwards [hμ] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (ex7_exp_bound hy).trans (Real.exp_le_exp.2 ?_)
    obtain ⟨h0, h1, -⟩ := ex7_cara_facts hγ hβ hR0 hμ n
    rw [abs_of_pos h0]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · exact (Real.continuous_exp.tendsto _).comp ((hα.mul_const y).neg)

/-- **The recursion of `ln A_n`**: `ln A_{n+1} = c_n ln A_n + d_n` with `c_n = γ/(γ + α_nR)`
and `d_n = ln(1 + γ/(α_nR)) + c_n ln(βM_nα_nR/γ)`. -/
theorem ex7_cara_logA_rec {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (n : ℕ) :
    Real.log (cs_caraA γ β R μ (n + 1)) =
      γ / (γ + cs_caraAlpha γ R n * R) * Real.log (cs_caraA γ β R μ n) +
        (Real.log (1 + γ / (cs_caraAlpha γ R n * R)) + γ / (γ + cs_caraAlpha γ R n * R) *
          Real.log (β * cs_caraM γ R μ n * cs_caraAlpha γ R n * R / γ)) := by
  obtain ⟨hα, -, hA, hM, -⟩ := ex7_cara_facts hγ hβ hR hμ n
  have hαR : 0 < cs_caraAlpha γ R n * R := mul_pos hα hR
  simp only [cs_caraA]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    show β * cs_caraA γ β R μ n * cs_caraM γ R μ n * cs_caraAlpha γ R n * R / γ =
      cs_caraA γ β R μ n * (β * cs_caraM γ R μ n * cs_caraAlpha γ R n * R / γ) by ring,
    Real.log_mul hA.ne' (by positivity)]
  ring

/-- **Exercise 7.7, the limit** (Miao, p. 229), `R > 1`: as the horizon recedes,
`α_n → ᾱ = γ(1 − 1/R)`, the marginal propensity to consume `1/Σ_{k ≤ n+1} R^{−k}` tends to
`1 − 1/R`, `A_n → Ā` (`ex7_caraAlim`), `L_n → L̄`, and for every `x` the optimal saving
`s_{n+1}(x)` of Exercise 6.9 tends to `s̄(x) = (γx + L̄)/(γ + ᾱR)`; `γ + ᾱR = γR`, so
`s̄(x) = x/R + L̄/(γR)`. -/
theorem ex_7_7_limit {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) :
    Tendsto (cs_caraAlpha γ R) atTop (𝓝 (ex7_caraAbar γ R)) ∧
      Tendsto (fun n => 1 / ∑ k ∈ Finset.range (n + 2), R⁻¹ ^ k) atTop (𝓝 (1 - R⁻¹)) ∧
      Tendsto (cs_caraA γ β R μ) atTop (𝓝 (ex7_caraAlim γ β R μ)) ∧
      Tendsto (cs_caraL γ β R μ) atTop (𝓝 (ex7_caraLbar γ β R μ)) ∧
      (∀ x, Tendsto (fun n => cs_caraS γ β R μ n x) atTop (𝓝 (ex7_caraSbar γ β R μ x))) ∧
      ∀ x, ex7_caraSbar γ β R μ x = x / R + ex7_caraLbar γ β R μ / (γ * R) := by
  have hR0 : 0 < R := by linarith
  have hα := ex7_cara_alpha_tendsto hγ hβ hR hμ
  have hM := ex7_cara_M_tendsto hγ hβ hR hμ
  have hab := ex7_caraAbar_pos hγ hR
  have hMb : 0 < ex7_caraMbar γ R μ := cs_cara_M_pos hab hμ
  obtain ⟨hγR, hc⟩ := ex7_caraAbar_R (γ := γ) hR
  have hc' := hc hγ
  have hi1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hi0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  -- the coefficients of the recursion
  have hαR : Tendsto (fun n => cs_caraAlpha γ R n * R) atTop (𝓝 (ex7_caraAbar γ R * R)) :=
    hα.mul_const R
  have habR : ex7_caraAbar γ R * R ≠ 0 := (mul_pos hab hR0).ne'
  have hcn : Tendsto (fun n => γ / (γ + cs_caraAlpha γ R n * R)) atTop
      (𝓝 (ex7_caraCbar γ R)) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add hαR) (by rw [hγR]; positivity)
  have hdn : Tendsto (fun n => Real.log (1 + γ / (cs_caraAlpha γ R n * R)) +
      γ / (γ + cs_caraAlpha γ R n * R) *
        Real.log (β * cs_caraM γ R μ n * cs_caraAlpha γ R n * R / γ)) atTop
      (𝓝 (ex7_caraDbar γ β R μ)) := by
    refine ((tendsto_const_nhds.add (tendsto_const_nhds.div hαR habR)).log
      (by positivity)).add (hcn.mul ?_)
    refine ((((tendsto_const_nhds.mul hM).mul hα).mul_const R).div_const γ).log ?_
    have := mul_pos (mul_pos (mul_pos hβ hMb) hab) hR0
    exact (div_pos this hγ).ne'
  have hlogA : Tendsto (fun n => Real.log (cs_caraA γ β R μ n)) atTop
      (𝓝 (ex7_caraDbar γ β R μ / (1 - ex7_caraCbar γ R))) :=
    ex7_affine_tendsto (fun n => by
      have := (ex7_cara_facts hγ hβ hR0 hμ n).1; positivity) hcn (by rw [hc']; exact hi1)
      hdn (ex7_cara_logA_rec hγ hβ hR0 hμ)
  have hA : Tendsto (cs_caraA γ β R μ) atTop (𝓝 (ex7_caraAlim γ β R μ)) :=
    ((Real.continuous_exp.tendsto _).comp hlogA).congr fun n =>
      Real.exp_log (ex7_cara_facts hγ hβ hR0 hμ n).2.2.1
  have hAb : 0 < ex7_caraAlim γ β R μ := Real.exp_pos _
  have hL : Tendsto (cs_caraL γ β R μ) atTop (𝓝 (ex7_caraLbar γ β R μ)) := by
    refine (((((tendsto_const_nhds.mul hA).mul hM).mul hα).mul_const R).div_const γ).log ?_
    have := mul_pos (mul_pos (mul_pos (mul_pos hβ hAb) hMb) hab) hR0
    exact (div_pos this hγ).ne'
  refine ⟨hα, ?_, hA, hL, fun x => ?_, fun x => ?_⟩
  · have hgeo := ((hasSum_geometric_of_lt_one hi0 hi1).tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 2)
    have := (tendsto_const_nhds (x := (1 : ℝ))).div hgeo (inv_ne_zero (by linarith))
    rw [one_div, inv_inv] at this
    exact this
  · exact ((tendsto_const_nhds.add hL).div (tendsto_const_nhds.add hαR)
      (by rw [hγR]; positivity))
  · rw [ex7_caraSbar, hγR]
    field_simp

/-- **Exercise 7.7, the Bellman equation of the limit** (Miao, p. 229), `R > 1`:
`V̄(x) = −Āe^{−ᾱx}` satisfies, for every `x`, `V̄(x) = sup_s −e^{−γ(x−s)} + β E V̄(Rs + y)`; the
supremum is attained only at `s̄(x)`, and there
`β E V̄(R s̄(x) + y) = V̄(x)/R` and `−e^{−γ(x − s̄(x))} = (1 − 1/R) V̄(x)`. -/
theorem ex_7_7_bellman {γ β R ymin ymax : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hγ : 0 < γ) (hβ : 0 < β) (hR : 1 < R) (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc ymin ymax) (x : ℝ) :
    let V : ℝ → ℝ := fun x => -(ex7_caraAlim γ β R μ * Real.exp (-(ex7_caraAbar γ R * x)))
    (∀ s, s ≠ ex7_caraSbar γ β R μ x →
      -Real.exp (-(γ * (x - s))) + β * ∫ y, V (R * s + y) ∂μ <
        -Real.exp (-(γ * (x - ex7_caraSbar γ β R μ x))) +
          β * ∫ y, V (R * ex7_caraSbar γ β R μ x + y) ∂μ) ∧
    V x = -Real.exp (-(γ * (x - ex7_caraSbar γ β R μ x))) +
      β * ∫ y, V (R * ex7_caraSbar γ β R μ x + y) ∂μ ∧
    β * ∫ y, V (R * ex7_caraSbar γ β R μ x + y) ∂μ = V x / R ∧
    -Real.exp (-(γ * (x - ex7_caraSbar γ β R μ x))) = (1 - R⁻¹) * V x := by
  intro V
  have hR0 : 0 < R := by linarith
  set α := ex7_caraAbar γ R
  set A := ex7_caraAlim γ β R μ
  set M := ex7_caraMbar γ R μ
  set s₀ := ex7_caraSbar γ β R μ x
  have hab : 0 < α := ex7_caraAbar_pos hγ hR
  have hM : 0 < M := cs_cara_M_pos hab hμ
  have hA : 0 < A := Real.exp_pos _
  obtain ⟨hγR, hc⟩ := ex7_caraAbar_R (γ := γ) hR
  have hK : 0 < β * A * M := by positivity
  have hden : 0 < γ + α * R := by positivity
  have hs₀ : (γ + α * R) * s₀ = γ * x + Real.log (β * A * M * α * R / γ) := by
    change (γ + α * R) * ((γ * x + Real.log (β * A * M * α * R / γ)) / (γ + α * R)) = _
    field_simp
  obtain ⟨hmax, hval⟩ := cs_cara_step hγ hab hR0 hK x s₀ hs₀
  have hobj : ∀ s, -Real.exp (-(γ * (x - s))) + β * ∫ y, V (R * s + y) ∂μ =
      -Real.exp (-(γ * (x - s))) - β * A * M * Real.exp (-(α * R * s)) := fun s => by
    have : ∫ y, V (R * s + y) ∂μ = -(A * M) * Real.exp (-(α * R * s)) := cs_cara_integral μ A α R s
    rw [this]; ring
  -- the fixed point: `(1 + γ/(ᾱR)) e^{γL̄/(γ + ᾱR)} = Ā`
  have hfix : (1 + γ / (α * R)) * Real.exp (γ * Real.log (β * A * M * α * R / γ) / (γ + α * R)) =
      A := by
    have hlog : Real.log (β * A * M * α * R / γ) = Real.log A + Real.log (β * M * α * R / γ) := by
      rw [← Real.log_mul hA.ne' (by positivity)]; congr 1; ring
    have hAdef : Real.log A = ex7_caraDbar γ β R μ / (1 - ex7_caraCbar γ R) := by
      simp only [A, ex7_caraAlim, Real.log_exp]
    have hc1 : 1 - ex7_caraCbar γ R ≠ 0 := by
      rw [hc hγ]; have := inv_lt_one_of_one_lt₀ hR; linarith
    have hcdef : γ / (γ + α * R) = ex7_caraCbar γ R := rfl
    rw [← Real.exp_log (show 0 < 1 + γ / (α * R) by positivity), ← Real.exp_add]
    nth_rewrite 2 [← Real.exp_log hA]
    congr 1
    have hDdef : ex7_caraDbar γ β R μ = Real.log (1 + γ / (α * R)) +
        ex7_caraCbar γ R * Real.log (β * M * α * R / γ) := rfl
    rw [mul_div_right_comm, hcdef, hlog, hAdef, hDdef]
    generalize Real.log (1 + γ / (α * R)) = X
    generalize Real.log (β * M * α * R / γ) = Y
    generalize ex7_caraCbar γ R = c at hc1 ⊢
    field_simp
    ring
  have hαe : γ * α * R / (γ + α * R) = α := by rw [hγR]; field_simp
  rw [hfix, hαe] at hval
  -- the first-order condition `β A M e^{−ᾱRs̄} = (γ/(ᾱR)) e^{−γ(x − s̄)}`
  have hE1 : Real.exp (-(γ * (x - s₀))) =
      (β * A * M * α * R / γ) * Real.exp (-(α * R * s₀)) := by
    rw [← Real.exp_log (show 0 < β * A * M * α * R / γ by positivity), ← Real.exp_add]
    congr 1; linarith
  have hfoc : β * A * M * Real.exp (-(α * R * s₀)) =
      Real.exp (-(γ * (x - s₀))) / (R - 1) := by
    rw [hE1]
    have : α * R = γ * (R - 1) := by
      change γ * (1 - R⁻¹) * R = _
      have : R ≠ 0 := hR0.ne'
      field_simp
    rw [show β * A * M * α * R / γ = β * A * M * (α * R) / γ by ring, this]
    have h' : R - 1 ≠ 0 := by linarith
    field_simp
  have hV : V x = -Real.exp (-(γ * (x - s₀))) - β * A * M * Real.exp (-(α * R * s₀)) := by
    change -(A * Real.exp (-(α * x))) = _
    rw [← neg_mul, ← hval]
  have hR1 : R - 1 ≠ 0 := by linarith
  refine ⟨fun s hs => by rw [hobj, hobj]; exact hmax s hs, by rw [hobj, hV], ?_, ?_⟩
  · have hI : ∫ y, V (R * s₀ + y) ∂μ = -(A * M) * Real.exp (-(α * R * s₀)) :=
      cs_cara_integral μ A α R s₀
    rw [hI, hV, show β * (-(A * M) * Real.exp (-(α * R * s₀))) =
      -(β * A * M * Real.exp (-(α * R * s₀))) by ring, hfoc]
    field_simp
    ring
  · rw [hV, hfoc]
    field_simp
    ring

end Miao.Applications
