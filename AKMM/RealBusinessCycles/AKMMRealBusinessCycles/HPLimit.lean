/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMRealBusinessCycles.HPFilter
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# The HP trend as `λ → ∞`

AKMM, §14.3.1, p. 411: "In the limit as `λ → ∞`, the extracted trend converges to a linear
function." We prove the precise statement: the HP trend `(I + λA)⁻¹Y` converges to the OLS
linear trend of `Y` (the regression of `Y_t` on `(1, t)`).

* The OLS linear trend (`hpOLS`, `T ≥ 2`): explicit coefficients from the normal equations
  (`hp_ols_normal`); it is affine and has zero penalty (`hp_pen_affine`); among affine sequences
  it is the unique best fit, `fit(x) = fit(τ̂) + ‖x − τ̂‖²` (`hp_ols_pythagoras`).
* Along the HP trends, the fit is bounded by `fit(τ̂)` and the penalty by `fit(τ̂)/λ`
  (`hp_trend_bounds`).
* **The limit** (`hp_limit_ols`): `(I + λA)⁻¹Y → τ̂` as `λ → ∞`, by compactness: every cluster
  point has zero penalty (so it is affine, `hp_pen_zero_iff`) and fit at most `fit(τ̂)`, so it is
  `τ̂`.
-/

namespace AKMM.RealBusinessCycles

open Matrix Filter Topology

/-- `S₁ = Σ t`. -/
def hpS1 (T : ℕ) : ℝ := ∑ t : Fin T, (t.val : ℝ)

/-- `S₂ = Σ t²`. -/
def hpS2 (T : ℕ) : ℝ := ∑ t : Fin T, (t.val : ℝ) ^ 2

/-- The determinant `T S₂ − S₁²` of the normal equations. -/
def hpDet (T : ℕ) : ℝ := T * hpS2 T - hpS1 T ^ 2

/-- The OLS intercept. -/
noncomputable def hpOLSa {T : ℕ} (Y : Fin T → ℝ) : ℝ :=
  ((∑ t, Y t) * hpS2 T - hpS1 T * ∑ t, (t.val : ℝ) * Y t) / hpDet T

/-- The OLS slope. -/
noncomputable def hpOLSb {T : ℕ} (Y : Fin T → ℝ) : ℝ :=
  (T * ∑ t, (t.val : ℝ) * Y t - hpS1 T * ∑ t, Y t) / hpDet T

/-- The OLS linear trend `τ̂_t = â + b̂t`. -/
noncomputable def hpOLS {T : ℕ} (Y : Fin T → ℝ) : Fin T → ℝ := fun t => hpOLSa Y + hpOLSb Y * t.val

/-- `T S₂ − S₁² = T Σ(t − S₁/T)² > 0` for `T ≥ 2`. -/
theorem hp_det_pos {T : ℕ} (hT : 2 ≤ T) : 0 < hpDet T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  set m := hpS1 T / T
  have hsum : ∑ t : Fin T, ((t.val : ℝ) - m) ^ 2 = hpS2 T - hpS1 T ^ 2 / T := by
    have : ∑ t : Fin T, ((t.val : ℝ) - m) ^ 2 =
        hpS2 T - 2 * m * hpS1 T + T * m ^ 2 := by
      simp only [hpS2, hpS1, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rw [this]; simp only [m]; field_simp; ring
  have hpos : 0 < ∑ t : Fin T, ((t.val : ℝ) - m) ^ 2 := by
    by_contra hle
    have h0 := le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun t _ => sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg ((t.val : ℝ) - m)).1 h0
    have e0 := hz ⟨0, by omega⟩ (Finset.mem_univ _)
    have e1 := hz ⟨1, by omega⟩ (Finset.mem_univ _)
    simp only [Nat.cast_zero, Nat.cast_one] at e0 e1
    nlinarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 e0,
      pow_eq_zero_iff (n := 2) two_ne_zero |>.1 e1]
  unfold hpDet
  have : T * hpS2 T - hpS1 T ^ 2 = T * (hpS2 T - hpS1 T ^ 2 / T) := by field_simp
  rw [this, ← hsum]
  positivity

/-- The normal equations of the OLS linear trend: `Σ(Y_t − τ̂_t) = 0` and `Σ t(Y_t − τ̂_t) = 0`. -/
theorem hp_ols_normal {T : ℕ} (hT : 2 ≤ T) (Y : Fin T → ℝ) :
    ∑ t, (Y t - hpOLS Y t) = 0 ∧ ∑ t, (t.val : ℝ) * (Y t - hpOLS Y t) = 0 := by
  have hd := (hp_det_pos hT).ne'
  have e1 : ∑ t, (Y t - hpOLS Y t) = (∑ t, Y t) - T * hpOLSa Y - hpOLSb Y * hpS1 T := by
    simp only [hpOLS, hpS1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have e2 : ∑ t, (t.val : ℝ) * (Y t - hpOLS Y t) =
      (∑ t, (t.val : ℝ) * Y t) - hpOLSa Y * hpS1 T - hpOLSb Y * hpS2 T := by
    have e : ∀ t : Fin T, (t.val : ℝ) * (Y t - hpOLS Y t) =
        (t.val : ℝ) * Y t - hpOLSa Y * t.val - hpOLSb Y * (t.val : ℝ) ^ 2 := fun t => by
      simp only [hpOLS]; ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hpS1, hpS2]
  rw [e1, e2]
  simp only [hpOLSa, hpOLSb]
  constructor <;> field_simp <;> unfold hpDet <;> ring

/-- An affine sequence has zero penalty. -/
theorem hp_pen_affine {T : ℕ} (τ : Fin T → ℝ) (a b : ℝ) (h : ∀ t, τ t = a + b * t.val) :
    hpPen T τ = 0 := by
  have hx : ∀ m, m < T → hpExt τ m = a + b * m := fun m hm => by
    rw [show hpExt τ m = τ ⟨m, hm⟩ by simp [hpExt, hm]]
    exact h ⟨m, hm⟩
  have hall : ∀ k : Fin T, (hpD T *ᵥ τ) k = 0 := by
    intro k
    rw [hp_D_apply]
    split_ifs with hk
    · rw [hx _ (by omega), hx _ k.isLt, hx _ hk.2, Nat.cast_sub hk.1]
      push_cast
      ring
    · rfl
  unfold hpPen
  simp [hall]

/-- **The OLS trend is the best affine fit** (Pythagoras): for affine `x`,
`fit(x) = fit(τ̂) + Σ(τ̂_t − x_t)²`. -/
theorem hp_ols_pythagoras {T : ℕ} (hT : 2 ≤ T) (Y x : Fin T → ℝ) (a b : ℝ)
    (hx : ∀ t, x t = a + b * t.val) :
    hpFit Y x = hpFit Y (hpOLS Y) + ∑ t, (hpOLS Y t - x t) ^ 2 := by
  obtain ⟨n1, n2⟩ := hp_ols_normal hT Y
  have hcross : ∑ t, (Y t - hpOLS Y t) * (hpOLS Y t - x t) = 0 := by
    have e : ∀ t : Fin T, (Y t - hpOLS Y t) * (hpOLS Y t - x t) =
        (hpOLSa Y - a) * (Y t - hpOLS Y t) + (hpOLSb Y - b) * ((t.val : ℝ) * (Y t - hpOLS Y t)) :=
      fun t => by rw [hx t]; simp only [hpOLS]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, n1, n2, mul_zero, add_zero]
  unfold hpFit
  have e : ∀ t : Fin T, (Y t - x t) ^ 2 = (Y t - hpOLS Y t) ^ 2 +
      2 * ((Y t - hpOLS Y t) * (hpOLS Y t - x t)) + (hpOLS Y t - x t) ^ 2 := fun t => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
  ring

/-- The OLS trend is affine. -/
theorem hp_ols_affine {T : ℕ} (Y : Fin T → ℝ) :
    ∀ t, hpOLS Y t = hpOLSa Y + hpOLSb Y * t.val := fun _ => rfl

/-- Bounds along the HP trends: for `λ > 0`, `fit(τ_λ) ≤ fit(τ̂)` and
`λ‖Dτ_λ‖² ≤ fit(τ̂)`. -/
theorem hp_trend_bounds {T : ℕ} {lam : ℝ} (hlam : 0 < lam) (Y : Fin T → ℝ) :
    hpFit Y ((1 + lam • hpA T)⁻¹ *ᵥ Y) ≤ hpFit Y (hpOLS Y) ∧
      lam * hpPen T ((1 + lam • hpA T)⁻¹ *ᵥ Y) ≤ hpFit Y (hpOLS Y) := by
  have h := hp_trend_exists hlam.le Y (hpOLS Y)
  have hp := hp_pen_affine (hpOLS Y) _ _ (hp_ols_affine Y)
  unfold hpObj at h
  rw [hp, mul_zero, add_zero] at h
  have h1 := mul_nonneg hlam.le (hp_pen_nonneg T ((1 + lam • hpA T)⁻¹ *ᵥ Y))
  have h2 := hp_fit_nonneg Y ((1 + lam • hpA T)⁻¹ *ᵥ Y)
  constructor <;> linarith

theorem hp_continuous_pen (T : ℕ) : Continuous (hpPen T) := by
  unfold hpPen
  fun_prop

theorem hp_continuous_fit {T : ℕ} (Y : Fin T → ℝ) : Continuous (hpFit Y) := by
  unfold hpFit
  fun_prop

/-- A continuous function bounded eventually along `f` is bounded at cluster points. -/
theorem hp_cluster_le {α X : Type*} [TopologicalSpace X] {l : Filter α} {f : α → X} {x : X}
    {g : X → ℝ} (hg : Continuous g) (hx : MapClusterPt x l f) {c : ℝ}
    (hev : ∀ᶠ a in l, g (f a) ≤ c) : g x ≤ c := by
  by_contra h
  have hn : ∀ᶠ y in 𝓝 x, c < g y := (hg.tendsto x).eventually (lt_mem_nhds (not_le.1 h))
  obtain ⟨a, h1, h2⟩ := ((hx.frequently hn).and_eventually hev).exists
  linarith

/-- **AKMM, p. 411: as `λ → ∞` the HP trend converges to a linear function**, namely the OLS
linear trend of `Y` (`T ≥ 2`). -/
theorem hp_limit_ols {T : ℕ} (hT : 2 ≤ T) (Y : Fin T → ℝ) :
    Tendsto (fun lam : ℝ => (1 + lam • hpA T)⁻¹ *ᵥ Y) atTop (𝓝 (hpOLS Y)) := by
  set C := hpFit Y (hpOLS Y)
  set τ := fun lam : ℝ => (1 + lam • hpA T)⁻¹ *ᵥ Y
  set K : Set (Fin T → ℝ) := Set.pi Set.univ fun t => Set.Icc (Y t - (C + 1)) (Y t + (C + 1))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ᶠ lam in atTop, τ lam ∈ K := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    intro t _
    have hfit := (hp_trend_bounds hlam Y).1
    have ht : (Y t - τ lam t) ^ 2 ≤ C := by
      refine le_trans ?_ hfit
      exact Finset.single_le_sum (f := fun s => (Y s - τ lam s) ^ 2) (fun s _ => sq_nonneg _)
        (Finset.mem_univ t)
    have hab : |Y t - τ lam t| ≤ C + 1 := by
      have := sq_abs (Y t - τ lam t)
      nlinarith [abs_nonneg (Y t - τ lam t)]
    rw [abs_le] at hab
    exact ⟨by linarith, by linarith⟩
  refine hK.tendsto_nhds_of_unique_mapClusterPt hmem fun x _ hx => ?_
  have hpen : hpPen T x ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    refine hp_cluster_le (hp_continuous_pen T) hx ?_
    filter_upwards [eventually_gt_atTop ((C + 1) / ε)] with lam hlam
    have hl : 0 < lam := lt_of_le_of_lt (div_nonneg (by linarith [hp_fit_nonneg Y (hpOLS Y)])
      hε.le) hlam
    have hb := (hp_trend_bounds hl Y).2
    have h1 : C + 1 < lam * ε := by rwa [div_lt_iff₀ hε] at hlam
    have hp0 := hp_pen_nonneg T (τ lam)
    by_contra hc
    nlinarith
  have hfit : hpFit Y x ≤ C := by
    refine hp_cluster_le (hp_continuous_fit Y) hx ?_
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact (hp_trend_bounds hlam Y).1
  have haff := (hp_pen_zero_iff x).1 hpen
  have hpy := hp_ols_pythagoras hT Y x (hpExt x 0) (hpExt x 1 - hpExt x 0)
    (fun t => by rw [haff t]; ring)
  have hsq : ∑ t, (hpOLS Y t - x t) ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  funext t
  have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => sq_nonneg (hpOLS Y s - x s)).1 hsq t
    (Finset.mem_univ t)
  have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
  linarith

end AKMM.RealBusinessCycles
