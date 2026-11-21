/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.BWAggregate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# §17.3.2: the Krusell–Smith method; Exercise 17.5

Miao, §17.3.2, pp. 581–583, and Exercise 17.5, p. 584.

* `bw_moments`: the vector `m = (m₁, …, m_I)` of the first `I` (raw) moments of the wealth
  marginal of `λ`; `bw_moments_first`: `m₁ = K`. A law of motion `m′ = H_I(m, z)` is any map.
* `bw_ksLaw`, `eq_17_12`: the log-linear law (17.12) `ln K′ = b_{0z} + b_{1z} ln K` (`K′ > 0`).
* `bw_ksR`, `bw_ksW`: prices from the firm's conditions `zF_K(K, L) = r + δ`, `zF_L(K, L) = w`.
* `bw_ksBellman`: the agent's problem (17.13) with aggregate state `(K, z)` and perceived law
  (17.12).
* Steps 3–5 as a fixed-point problem: `bw_olsSlope`, `bw_olsIntercept` (the regression of
  Step 4 on the periods `t` with `z_t = z`), `bw_ksUpdate` (the map from the coefficients
  `(b₀, b₁)` to the estimated `(β₀, β₁)`, given the simulated capital path), `bw_ksConsistent`
  (Step 5: `(β₀, β₁) = (b₀, b₁)`, a fixed point).
* `bw_ols_exact`, `bw_rsq_exact`: if the aggregated path obeys the perceived law exactly, OLS
  returns its coefficients and `R² = 1`; hence `bw_ks_fixed_point_of_exact`: such a law is a
  fixed point (consistent).
* **Exercise 17.5** (`BWLeisureEqm`): endogenous leisure in the Krusell–Smith model, a recursive
  equilibrium with labour supply `n(a, l; λ, z) ∈ [0, 1]` and `L = ∫ l n dλ`; `ex_17_5` gives a
  concrete instance.

The simulation itself (Step 3, `N = 100000`, `T = 2000`, `T₀ = 500`), Step 6 (`R²` and added
moments) and the approximate-aggregation explanations are computational and not formalised.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L]

/-- Miao, p. 581: the vector of the first `I` moments `m_i = ∫ aⁱ dλ` of the wealth distribution
(the marginal of `λ` in `a`); the book's list (mean, variance, skewness, kurtosis) is the
corresponding central/standardised version of the same information. -/
noncomputable def bw_moments (I : ℕ) (lam : Measure (ℝ × L)) : Fin I → ℝ :=
  fun i => ∫ p, p.1 ^ (i.val + 1) ∂lam

/-- Miao, p. 581: the first moment is aggregate capital, `m₁ = K`. -/
theorem bw_moments_first (I : ℕ) (lam : Measure (ℝ × L)) :
    bw_moments (I + 1) lam 0 = bw_aggK lam := by
  simp [bw_moments, bw_aggK]

/-- The Krusell–Smith law of motion (17.12), `K′ = exp(b_{0z} + b_{1z} ln K)`. -/
noncomputable def bw_ksLaw (b0 b1 : Z → ℝ) (z : Z) (K : ℝ) : ℝ :=
  Real.exp (b0 z + b1 z * Real.log K)

omit [MeasurableSpace Z] in
/-- Miao, (17.12), p. 581: `ln K′ = b_{0z} + b_{1z} ln K`, with `K′ > 0`, and `K′` depends on
`(K, z)` only, not on `z′`. -/
theorem eq_17_12 (b0 b1 : Z → ℝ) (z : Z) (K : ℝ) :
    Real.log (bw_ksLaw b0 b1 z K) = b0 z + b1 z * Real.log K ∧ 0 < bw_ksLaw b0 b1 z K :=
  ⟨Real.log_exp _, Real.exp_pos _⟩

/-- The interest rate `r(K, L, z) = zF_K(K, L) − δ` (Miao, p. 582). -/
def bw_ksR (A : BWAggEconomy Z L) (K Lb : ℝ) (z : Z) : ℝ := A.zval z * A.FK K Lb - A.δ

/-- The wage `w(K, L, z) = zF_L(K, L)` (Miao, p. 582). -/
def bw_ksW (A : BWAggEconomy Z L) (K Lb : ℝ) (z : Z) : ℝ := A.zval z * A.FL K Lb

/-- Miao, p. 582: the prices satisfy the firm's conditions. -/
theorem bw_ks_prices (A : BWAggEconomy Z L) (K Lb : ℝ) (z : Z) :
    A.zval z * A.FK K Lb = bw_ksR A K Lb z + A.δ ∧ A.zval z * A.FL K Lb = bw_ksW A K Lb z := by
  constructor
  · unfold bw_ksR; ring
  · rfl

/-- Miao, (17.13), p. 582: the agent's problem with the perceived law (17.12),
`V(a, l; K, z) = max_{a′} u(c) + β E[V(a′, l′; K′, z′) | z, l]`, `K′ = exp(b_{0z} + b_{1z} ln K)`,
`c + a′ = (1 + r(K, L_z, z))a + w(K, L_z, z)l`, `a′ ≥ 0` (`L_z` the aggregate labour in `z`). -/
def bw_ksBellman (A : BWAggEconomy Z L) (Lz : Z → ℝ) (b0 b1 : Z → ℝ)
    (V g : ℝ → L → ℝ → Z → ℝ) : Prop :=
  ∀ a l K z, 0 ≤ a →
    g a l K z ∈ Set.Icc 0 ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l) ∧
    V a l K z = A.u ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l -
        g a l K z) +
      A.β * ∫ p, V (g a l K z) p.2 (bw_ksLaw b0 b1 z K) p.1 ∂(A.Q (z, l)) ∧
    ∀ a' ∈ Set.Icc 0 ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l),
      A.u ((1 + bw_ksR A K (Lz z) z) * a + bw_ksW A K (Lz z) z * A.lab l - a') +
        A.β * ∫ p, V a' p.2 (bw_ksLaw b0 b1 z K) p.1 ∂(A.Q (z, l)) ≤ V a l K z

/-- The sample mean over a finite set of periods. -/
noncomputable def bw_mean (s : Finset ℕ) (x : ℕ → ℝ) : ℝ := (∑ t ∈ s, x t) / s.card

/-- Step 4 (Miao, p. 582): the OLS slope of `y` on `x` over the periods `s`. -/
noncomputable def bw_olsSlope (s : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  (∑ t ∈ s, (x t - bw_mean s x) * (y t - bw_mean s y)) / ∑ t ∈ s, (x t - bw_mean s x) ^ 2

/-- Step 4: the OLS intercept. -/
noncomputable def bw_olsIntercept (s : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  bw_mean s y - bw_olsSlope s x y * bw_mean s x

/-- Step 6 (Miao, p. 583): the `R²` of the regression. -/
noncomputable def bw_rsq (s : Finset ℕ) (x y : ℕ → ℝ) : ℝ :=
  1 - (∑ t ∈ s, (y t - (bw_olsIntercept s x y + bw_olsSlope s x y * x t)) ^ 2) /
    ∑ t ∈ s, (y t - bw_mean s y) ^ 2

/-- If `y_t = b₀ + b₁x_t` on `s` and `x` is not constant on `s`, OLS returns `(b₀, b₁)`. -/
theorem bw_ols_exact {s : Finset ℕ} {x y : ℕ → ℝ} {b0 b1 : ℝ}
    (hy : ∀ t ∈ s, y t = b0 + b1 * x t) (hvar : ∑ t ∈ s, (x t - bw_mean s x) ^ 2 ≠ 0) :
    bw_olsSlope s x y = b1 ∧ bw_olsIntercept s x y = b0 := by
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp at hvar
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hmy : bw_mean s y = b0 + b1 * bw_mean s x := by
    unfold bw_mean
    rw [Finset.sum_congr rfl hy, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hslope : bw_olsSlope s x y = b1 := by
    unfold bw_olsSlope
    have : ∑ t ∈ s, (x t - bw_mean s x) * (y t - bw_mean s y) =
        b1 * ∑ t ∈ s, (x t - bw_mean s x) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hy t ht, hmy]; ring
    rw [this]
    field_simp
  refine ⟨hslope, ?_⟩
  unfold bw_olsIntercept
  rw [hslope, hmy]; ring

/-- If the data obey `y_t = b₀ + b₁x_t` exactly on `s`, the regression fits perfectly: `R² = 1`. -/
theorem bw_rsq_exact {s : Finset ℕ} {x y : ℕ → ℝ} {b0 b1 : ℝ}
    (hy : ∀ t ∈ s, y t = b0 + b1 * x t) (hvar : ∑ t ∈ s, (x t - bw_mean s x) ^ 2 ≠ 0) :
    bw_rsq s x y = 1 := by
  obtain ⟨h1, h0⟩ := bw_ols_exact hy hvar
  unfold bw_rsq
  rw [h1, h0]
  have : ∑ t ∈ s, (y t - (b0 + b1 * x t)) ^ 2 = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [hy t ht]; ring
  rw [this, zero_div, sub_zero]

/-- The periods of the regression sample `[T₀, T)` in which the aggregate state is `z`. -/
noncomputable def bw_ksSample [DecidableEq Z] (zs : ℕ → Z) (T0 T : ℕ) (z : Z) : Finset ℕ :=
  (Finset.Ico T0 T).filter fun t => zs t = z

/-- Steps 3–4 (Miao, p. 582) as a map: given the capital path `Kbar` simulated under the
coefficients `(b₀, b₁)` (`sim b0 b1`), regress `ln K̄_{t+1}` on `ln K̄_t` separately for each `z`
over the sample `[T₀, T)`, giving the new coefficients `(β₀, β₁)`. -/
noncomputable def bw_ksUpdate [DecidableEq Z] (sim : (Z → ℝ) → (Z → ℝ) → ℕ → ℝ) (zs : ℕ → Z)
    (T0 T : ℕ) (b0 b1 : Z → ℝ) : (Z → ℝ) × (Z → ℝ) :=
  (fun z => bw_olsIntercept (bw_ksSample zs T0 T z) (fun t => Real.log (sim b0 b1 t))
      (fun t => Real.log (sim b0 b1 (t + 1))),
    fun z => bw_olsSlope (bw_ksSample zs T0 T z) (fun t => Real.log (sim b0 b1 t))
      (fun t => Real.log (sim b0 b1 (t + 1))))

/-- Step 5 (Miao, p. 583): the perceived law (17.12) is **consistent** with the law generated by
aggregating individual choices iff `(b₀, b₁)` is a fixed point of the update. -/
def bw_ksConsistent [DecidableEq Z] (sim : (Z → ℝ) → (Z → ℝ) → ℕ → ℝ) (zs : ℕ → Z) (T0 T : ℕ)
    (b0 b1 : Z → ℝ) : Prop :=
  bw_ksUpdate sim zs T0 T b0 b1 = (b0, b1)

omit [MeasurableSpace Z] in
/-- Miao, pp. 582–583: if the simulated aggregate path obeys the perceived law (17.12) exactly,
`K̄_{t+1} = exp(b_{0z_t} + b_{1z_t} ln K̄_t)` on the sample, and `ln K̄_t` varies within each
`z`-subsample, then `(b₀, b₁)` is a fixed point of the Krusell–Smith iteration (consistent). -/
theorem bw_ks_fixed_point_of_exact [DecidableEq Z] {sim : (Z → ℝ) → (Z → ℝ) → ℕ → ℝ}
    {zs : ℕ → Z} {T0 T : ℕ} {b0 b1 : Z → ℝ}
    (hlaw : ∀ t, T0 ≤ t → t < T → sim b0 b1 (t + 1) = bw_ksLaw b0 b1 (zs t) (sim b0 b1 t))
    (hvar : ∀ z, ∑ t ∈ bw_ksSample zs T0 T z,
      (Real.log (sim b0 b1 t) - bw_mean (bw_ksSample zs T0 T z)
        (fun t => Real.log (sim b0 b1 t))) ^ 2 ≠ 0) :
    bw_ksConsistent sim zs T0 T b0 b1 := by
  have key : ∀ z, ∀ t ∈ bw_ksSample zs T0 T z,
      Real.log (sim b0 b1 (t + 1)) = b0 z + b1 z * Real.log (sim b0 b1 t) := by
    intro z t ht
    simp only [bw_ksSample, Finset.mem_filter, Finset.mem_Ico] at ht
    rw [hlaw t ht.1.1 ht.1.2, (eq_17_12 b0 b1 _ _).1, ht.2]
  unfold bw_ksConsistent bw_ksUpdate
  ext z
  · exact (bw_ols_exact (key z) (hvar z)).2
  · exact (bw_ols_exact (key z) (hvar z)).1

/-- **Exercise 17.5** (Miao, p. 584): **a recursive equilibrium of the Krusell–Smith model with
endogenous leisure**. Utility `v(c, 1 − n)` over consumption and leisure; the household chooses
`a′ ≥ 0` and hours `n ∈ [0, 1]` with `c + a′ = (1 + r(λ, z))a + w(λ, z)ln`, `c ≥ 0`;
aggregate labour is `L(λ, z) = ∫ l n(a, l; λ, z) dλ`; firms' conditions
hold at `(K, L(λ, z))`; and the law of motion is generated by the asset
policy (corrected form (iv) of Definition 17.3.1). -/
structure BWLeisureEqm (A : BWAggEconomy Z L) (v : ℝ → ℝ → ℝ) where
  V : ℝ → L → Measure (ℝ × L) → Z → ℝ
  g : ℝ → L → Measure (ℝ × L) → Z → ℝ
  n : ℝ → L → Measure (ℝ × L) → Z → ℝ
  G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)
  r : Measure (ℝ × L) → Z → ℝ
  w : Measure (ℝ × L) → Z → ℝ
  bellman : ∀ a l lam z, 0 ≤ a →
    n a l lam z ∈ Set.Icc 0 1 ∧
    g a l lam z ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l * n a l lam z) ∧
    (∀ a', 0 ≤ a' → Integrable (fun p : Z × L => V a' p.2 (G lam z p.1) p.1) (A.Q (z, l))) ∧
    V a l lam z = v ((1 + r lam z) * a + w lam z * A.lab l * n a l lam z - g a l lam z)
        (1 - n a l lam z) +
      A.β * ∫ p, V (g a l lam z) p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ∧
    ∀ h ∈ Set.Icc (0 : ℝ) 1, ∀ a' ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l * h),
      v ((1 + r lam z) * a + w lam z * A.lab l * h - a') (1 - h) +
        A.β * ∫ p, V a' p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ≤ V a l lam z
  firmK : ∀ lam z, A.zval z * A.FK (bw_aggK lam)
    (∫ p, A.lab p.2 * n p.1 p.2 lam z ∂lam) = r lam z + A.δ
  firmL : ∀ lam z, A.zval z * A.FL (bw_aggK lam)
    (∫ p, A.lab p.2 * n p.1 p.2 lam z ∂lam) = w lam z
  law : A.Law g G

/-- **Exercise 17.5** is not vacuous: in `bw_aggExample` with `v(c, h) = c` (leisure not valued),
`V(a) = 2a + 2`, `g(a) = a`, full-time work `n = 1`, `G(λ, z; z′) = λ`, `r = w = 1` is a recursive
equilibrium with endogenous leisure. -/
noncomputable def ex_17_5 : BWLeisureEqm bw_aggExample (fun c _ => c) where
  V := fun a _ _ _ => 2 * a + 2
  g := fun a _ _ _ => a
  n := fun _ _ _ _ => 1
  G := fun lam _ _ => lam
  r := fun _ _ => 1
  w := fun _ _ => 1
  bellman := by
    intro a l lam z ha
    simp only [bw_aggExample_Q, integral_dirac]
    refine ⟨⟨zero_le_one, le_rfl⟩, ⟨ha, ?_⟩, fun a' _ => Integrable.of_finite, ?_,
      fun h hh a' _ => ?_⟩
    · simp only [bw_aggExample]; linarith
    · simp only [bw_aggExample]; ring
    · simp only [bw_aggExample]; linarith [hh.2]
  firmK := fun _ _ => by simp only [bw_aggExample]; norm_num
  firmL := fun _ _ => by simp only [bw_aggExample]; norm_num
  law := bw_recEqm_example.law

end Miao.IncompleteMarkets
