/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.LevyCiesielski
import LimitTheorems.PathSpaceC01
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance

/-!
# Standard Brownian motion on `[0,1]` and Wiener measure (MT, App. D.6.2, p. 563)

The functional CLT (MT, Theorem D.6.4, p. 563, and Theorem 17.4.4) has standard Brownian motion
on `[0,1]` as its limit; the book defines it by its properties (continuous paths, `B(0) = 0`,
independent Gaussian increments `N(0, |t − s|)`) and assumes that it exists. Here it is built
from `LevyCiesielski.lean`, on the i.i.d. Gaussian sequence space `(ℕ → ℝ, gaussSeq)`.

**The process.**
* `brownian t ω = levyPath ω t`; `continuous_brownian` (every path is continuous),
  `brownian_zero` (every path starts at `0`), `measurable_brownian`.
* `measurable_levyPath`: the path map is measurable for any Borel σ-algebra on
  `C(unitInterval, ℝ)` (passed as instance hypotheses, see `PathSpaceC01`).
* `gaussSeq_map_fidiLin_levyPath`: `Σ_i c i B(t i)` has law `N(0, Σ_{i,j} c i c j min(t i, t j))`
  (finite Gaussian sums, the covariance identity `tendsto_schauder_sum_mul`, and
  `map_eq_gaussianReal_of_tendsto`).

**Wiener measure.**
* `wienerMeasure = gaussSeq.map levyPath`; `isProbabilityMeasure_wienerMeasure`.
* `wienerMeasure_fidiLin`: the law of `fidiLin t c` is
  `gaussianReal 0 (Σ_{i,j} c i c j min (t i) (t j)).toNNReal`.
* `eq_wienerMeasure_of_fidiLin`: this characterises Wiener measure among finite measures.
* `wienerMeasure_map_eval`, `wienerMeasure_map_eval_one`, `wienerMeasure_map_sub`:
  `f t ~ N(0, t)`, `f 1 ~ N(0, 1)`, `f t − f s ~ N(0, |t − s|)`.

**The book's defining properties (MT, App. D.6.2, p. 563).**
* `hasGaussianLaw_brownian_vec`, `isGaussianProcess_brownian`: finite vectors `(B(u i))_i` are
  jointly Gaussian (Mathlib's `IsGaussianProcess`).
* `gaussSeq_map_brownian`, `covariance_brownian`: `B(t) ~ N(0, t)`, `Cov(B s, B t) = min s t`.
* (i) `continuous_brownian`, `brownian_zero`: continuous paths (every `ω`), `B(0) = 0`.
* (ii) `indepFun_brownian_increment`: `B(t) − B(s)` is independent of `(B(r j))_j` whenever
  `r j ≤ s ≤ t` (every finite family of earlier times; via zero covariance in a Gaussian vector).
* (iii) `gaussSeq_map_brownian_sub`: `B(t) − B(s) ~ N(0, |t − s|)`.

Not formalised: the law of `sup_t B(t)` (reflection principle); no later result needs it.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped ENNReal NNReal

/-- **Brownian motion on `[0,1]`**, realised on the Gaussian sequence space `(ℕ → ℝ, gaussSeq)`:
`brownian t ω = levyPath ω t`. -/
noncomputable def brownian (t : unitInterval) (ω : ℕ → ℝ) : ℝ := levyPath ω t

/-- Every path of `brownian` is continuous. -/
theorem continuous_brownian (ω : ℕ → ℝ) : Continuous fun t => brownian t ω :=
  (levyPath ω).continuous

/-- Every path of `brownian` starts at `0`. -/
theorem brownian_zero (ω : ℕ → ℝ) : brownian 0 ω = 0 := levyPath_zero ω

open Classical in
/-- The truncated partial sums converge, for every `ω`, to `levyPath ω`. -/
lemma tendsto_lcPartial_ite (ω : ℕ → ℝ) :
    Tendsto (fun N => if ω ∈ lcGood then lcPartial N ω else 0) atTop (𝓝 (levyPath ω)) := by
  by_cases hω : ω ∈ lcGood
  · simpa [hω] using tendsto_lcPartial_levyPath hω
  · simp only [hω, ite_false, levyPath]
    exact tendsto_const_nhds

/-- The path map `ω ↦ levyPath ω` is measurable, for any Borel σ-algebra on the path space. -/
theorem measurable_levyPath [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] : Measurable levyPath := by
  classical
  refine measurable_of_tendsto_metrizable
    (f := fun N ω => if ω ∈ lcGood then lcPartial N ω else 0) (fun N => ?_)
    (tendsto_pi_nhds.2 tendsto_lcPartial_ite)
  exact Measurable.ite measurableSet_lcGood (continuous_lcPartial N).measurable measurable_const

/-- Each `brownian t` is measurable. -/
theorem measurable_brownian (t : unitInterval) : Measurable (brownian t) := by
  let : MeasurableSpace C(unitInterval, ℝ) := borel _
  have : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
  exact (continuous_eval_const t).measurable.comp measurable_levyPath

/-- The variance `Σ_{i,j} c i c j min (t i) (t j)` of `fidiLin t c` under Wiener measure. -/
noncomputable def bmVar {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * min (t i : ℝ) (t j)

/-- The coefficient of `ξ_m` in `fidiLin t c` of the Schauder series. -/
noncomputable def bmCoeff {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) (m : ℕ) :
    ℝ :=
  ∑ i, c i * schauder m (t i)

/-- The partial variances converge: `Σ_{m<2^N} (bmCoeff t c m)² → bmVar t c`. -/
lemma tendsto_sum_bmCoeff_sq {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) :
    Tendsto (fun N => ∑ m ∈ range (2 ^ N), bmCoeff t c m ^ 2) atTop (𝓝 (bmVar t c)) := by
  have he : ∀ N, ∑ m ∈ range (2 ^ N), bmCoeff t c m ^ 2
      = ∑ i, ∑ j, c i * c j * ∑ m ∈ range (2 ^ N), schauder m (t i) * schauder m (t j) := by
    intro N
    simp_rw [bmCoeff, sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [he]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (tendsto_schauder_sum_mul (t i).2 (t j).2).const_mul _

/-- **Finite-dimensional laws of Brownian motion.** For a finite family of times `t i` and
coefficients `c i`, `Σ_i c i B(t i)` is centred Gaussian with variance
`Σ_{i,j} c i c j min (t i) (t j)`. -/
theorem gaussSeq_map_sum_brownian {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) :
    gaussSeq.map (fun ω => ∑ i, c i * brownian (t i) ω) = gaussianReal 0 (bmVar t c).toNNReal := by
  have := isProbabilityMeasure_gaussSeq
  refine map_eq_gaussianReal_of_tendsto (X := fun N ω => ∑ m ∈ range (2 ^ N), bmCoeff t c m * ω m)
    (v := fun N => (∑ m ∈ range (2 ^ N), bmCoeff t c m ^ 2).toNNReal)
    (fun N => (Finset.measurable_sum _ fun m _ =>
      measurable_const.mul (measurable_pi_apply m)).aemeasurable)
    (fun N => gaussSeq_map_sum _ _) ?_
    ((continuous_real_toNNReal.tendsto _).comp (tendsto_sum_bmCoeff_sq t c))
  filter_upwards [ae_mem_lcGood] with ω hω
  have he : ∀ N, ∑ m ∈ range (2 ^ N), bmCoeff t c m * ω m
      = ∑ i, c i * ∑ m ∈ range (2 ^ N), ω m * schauder m (t i) := by
    intro N
    simp_rw [bmCoeff, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [he]
  exact tendsto_finsetSum _ fun i _ => (tendsto_lcPartial_apply hω (t i)).const_mul _

/-- The fidi functionals of the Lévy–Ciesielski path: `fidiLin t c (levyPath ω)` has law
`N(0, Σ_{i,j} c i c j min (t i) (t j))`. -/
theorem gaussSeq_map_fidiLin_levyPath {k : ℕ} (t : Fin k → unitInterval) (c : Fin k → ℝ) :
    gaussSeq.map (fun ω => fidiLin t c (levyPath ω)) = gaussianReal 0 (bmVar t c).toNNReal :=
  gaussSeq_map_sum_brownian t c

/-! ### Wiener measure -/

/-- **Wiener measure** on `C([0,1], ℝ)`: the law of the Lévy–Ciesielski path `levyPath` under the
i.i.d. Gaussian sequence measure. It is defined for any σ-algebra on the path space; the results
below assume it is the Borel σ-algebra. -/
noncomputable def wienerMeasure [MeasurableSpace C(unitInterval, ℝ)] :
    Measure C(unitInterval, ℝ) :=
  gaussSeq.map levyPath

/-- Wiener measure is a probability measure. -/
theorem isProbabilityMeasure_wienerMeasure [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] : IsProbabilityMeasure wienerMeasure := by
  have := isProbabilityMeasure_gaussSeq
  unfold wienerMeasure
  infer_instance

/-- **Characterisation of Wiener measure.** Under `wienerMeasure`, every linear fidi functional
`fidiLin t c f = Σ_i c i f (t i)` is centred Gaussian with variance
`Σ_{i,j} c i c j min (t i) (t j)`. -/
theorem wienerMeasure_fidiLin [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {k : ℕ} (t : Fin k → unitInterval) (c : Fin k → ℝ) :
    wienerMeasure.map (fidiLin t c)
      = gaussianReal 0 (∑ i, ∑ j, c i * c j * min (t i : ℝ) (t j)).toNNReal := by
  unfold wienerMeasure
  rw [Measure.map_map (measurable_fidiLin t c) measurable_levyPath]
  exact gaussSeq_map_fidiLin_levyPath t c

/-- **Uniqueness of Wiener measure.** A finite measure on `C([0,1], ℝ)` with the fidi laws of
`wienerMeasure_fidiLin` is Wiener measure (Cramér–Wold, `ext_of_fidiLin`). -/
theorem eq_wienerMeasure_of_fidiLin [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] (μ : Measure C(unitInterval, ℝ)) [IsFiniteMeasure μ]
    (h : ∀ (k : ℕ) (t : Fin k → unitInterval) (c : Fin k → ℝ),
      μ.map (fidiLin t c) = gaussianReal 0 (∑ i, ∑ j, c i * c j * min (t i : ℝ) (t j)).toNNReal) :
    μ = wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  exact ext_of_fidiLin fun k t c => by rw [h, wienerMeasure_fidiLin]

/-- Under Wiener measure, `f t` is `N(0, t)`. -/
theorem wienerMeasure_map_eval [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] (t : unitInterval) :
    wienerMeasure.map (fun f : C(unitInterval, ℝ) => f t) = gaussianReal 0 (t : ℝ).toNNReal := by
  have h := wienerMeasure_fidiLin (fun _ : Fin 1 => t) (fun _ => 1)
  have hf : fidiLin (fun _ : Fin 1 => t) (fun _ => 1) = fun f : C(unitInterval, ℝ) => f t := by
    funext f; simp [fidiLin_apply]
  rw [hf] at h
  rw [h]
  simp

/-- Under Wiener measure, `f 1` is standard Gaussian. -/
theorem wienerMeasure_map_eval_one [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] :
    wienerMeasure.map (fun f : C(unitInterval, ℝ) => f 1) = gaussianReal 0 1 := by
  rw [wienerMeasure_map_eval]
  simp

/-! ### Gaussian process, covariance and increments (MT, App. D.6.2, p. 563) -/

/-- Any finite vector `(B(u i))_i` of values of Brownian motion is jointly Gaussian. -/
theorem hasGaussianLaw_brownian_vec {ι : Type*} [Finite ι] (u : ι → unitInterval) :
    HasGaussianLaw (fun ω i => brownian (u i) ω) gaussSeq := by
  classical
  have := Fintype.ofFinite ι
  have hV : Measurable fun ω (i : ι) => brownian (u i) ω :=
    Measurable.of_eval fun i => measurable_brownian (u i)
  refine ⟨hV.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L =>
    ⟨0, (bmVar u fun i => L fun j => if i = j then 1 else 0).toNNReal, ?_⟩⟩
  rw [Measure.map_map L.continuous.measurable hV]
  have hL : (L ∘ fun ω (i : ι) => brownian (u i) ω)
      = fun ω => ∑ i, L (fun j => if i = j then 1 else 0) * brownian (u i) ω := by
    funext ω
    rw [Function.comp_apply, ← ContinuousLinearMap.coe_coe, LinearMap.pi_apply_eq_sum_univ]
    simp_rw [smul_eq_mul, mul_comm (brownian _ ω)]
  rw [hL]
  exact gaussSeq_map_sum_brownian u _

/-- Brownian motion is a Gaussian process (in Mathlib's sense, `IsGaussianProcess`). -/
theorem isGaussianProcess_brownian : IsGaussianProcess brownian gaussSeq :=
  ⟨fun I => hasGaussianLaw_brownian_vec (fun i : I => (i : unitInterval))⟩

/-- Each `B(t)` is square integrable. -/
lemma memLp_brownian (t : unitInterval) : MemLp (brownian t) 2 gaussSeq :=
  (isGaussianProcess_brownian.hasGaussianLaw_eval t).memLp_two

/-- The variance of a random variable with law `N(μ, v)` is `v`. -/
lemma variance_of_map_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) {μ : ℝ} {v : ℝ≥0} (h : P.map X = gaussianReal μ v) :
    Var[X; P] = v := by
  have := variance_map (X := id) (μ := P) measurable_id.aemeasurable hX
  rw [h, variance_id_gaussianReal] at this
  exact this.symm

/-- `B(t)` has law `N(0, t)`. -/
theorem gaussSeq_map_brownian (t : unitInterval) :
    gaussSeq.map (brownian t) = gaussianReal 0 (t : ℝ).toNNReal := by
  have h := gaussSeq_map_sum_brownian (fun _ : Unit => t) (fun _ => 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, bmVar, mul_one, min_self] at h
  exact h

/-- **Covariance of Brownian motion**: `Cov(B(s), B(t)) = min s t`. -/
theorem covariance_brownian (s t : unitInterval) :
    cov[brownian s, brownian t; gaussSeq] = min (s : ℝ) t := by
  have := isProbabilityMeasure_gaussSeq
  have hsum := gaussSeq_map_sum_brownian ![s, t] ![1, 1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, bmVar,
    mul_one, min_self] at hsum
  have hvs := variance_of_map_eq_gaussianReal (measurable_brownian s).aemeasurable
    (gaussSeq_map_brownian s)
  have hvt := variance_of_map_eq_gaussianReal (measurable_brownian t).aemeasurable
    (gaussSeq_map_brownian t)
  have hv := variance_of_map_eq_gaussianReal
    ((measurable_brownian s).add (measurable_brownian t)).aemeasurable hsum
  have hadd := variance_add (memLp_brownian s) (memLp_brownian t)
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have hm0 : (0 : ℝ) ≤ min (s : ℝ) t := le_min hs0 ht0
  rw [Real.coe_toNNReal _ hs0] at hvs
  rw [Real.coe_toNNReal _ ht0] at hvt
  rw [min_comm (t : ℝ) s, Real.coe_toNNReal _ (by linarith)] at hv
  rw [hvs, hvt] at hadd
  linarith

/-- **Gaussian increments** (MT, App. D.6.2 (iii)): `B(t) − B(s)` has law `N(0, |t − s|)`. -/
theorem gaussSeq_map_brownian_sub (s t : unitInterval) :
    gaussSeq.map (fun ω => brownian t ω - brownian s ω)
      = gaussianReal 0 (|(t : ℝ) - s|).toNNReal := by
  have h := gaussSeq_map_sum_brownian ![t, s] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, bmVar,
    mul_one, min_self, neg_mul, mul_neg, neg_neg] at h
  have he : (fun ω => brownian t ω + -brownian s ω) = fun ω => brownian t ω - brownian s ω := by
    funext ω; ring
  rw [he] at h
  rw [h]
  congr 2
  rcases le_total (t : ℝ) s with hts | hts
  · rw [min_eq_left hts, min_eq_right hts, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right hts, min_eq_left hts, abs_of_nonneg (by linarith)]; ring

/-- **Independent increments** (MT, App. D.6.2 (ii)): for `r j ≤ s ≤ t`, the increment
`B(t) − B(s)` is independent of the vector `(B(r j))_j`, for every finite family of earlier
times. -/
theorem indepFun_brownian_increment {ι : Type*} [Finite ι] {s t : unitInterval}
    (r : ι → unitInterval) (hr : ∀ j, r j ≤ s) (hst : s ≤ t) :
    IndepFun (fun ω => brownian t ω - brownian s ω) (fun ω j => brownian (r j) ω) gaussSeq := by
  have := isProbabilityMeasure_gaussSeq
  have := Fintype.ofFinite ι
  let u : Fin 2 ⊕ ι → unitInterval := Sum.elim ![t, s] r
  let P : (Fin 2 ⊕ ι) → (Fin 2 ⊕ ι → ℝ) →L[ℝ] ℝ := fun a =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ⊕ ι => ℝ) a
  let L : (Fin 2 ⊕ ι → ℝ) →L[ℝ] (Unit → ℝ) × (ι → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Unit => P (Sum.inl 0) - P (Sum.inl 1)).prod
      (ContinuousLinearMap.pi fun j => P (Sum.inr j))
  have hG := (hasGaussianLaw_brownian_vec u).map_fun L
  have hG' : HasGaussianLaw (fun ω => (fun _ : Unit => brownian t ω - brownian s ω,
      fun j => brownian (r j) ω)) gaussSeq := hG
  have hind := hG'.indepFun_of_covariance_eval (X := fun _ : Unit => fun ω =>
      brownian t ω - brownian s ω) (Y := fun j => brownian (r j)) fun _ j => by
    rw [covariance_fun_sub_left (memLp_brownian t) (memLp_brownian s) (memLp_brownian (r j)),
      covariance_brownian, covariance_brownian]
    have h1 : (r j : ℝ) ≤ s := hr j
    have h2 : (s : ℝ) ≤ t := hst
    rw [min_eq_right (h1.trans h2), min_eq_right h1, sub_self]
  exact hind.comp (φ := fun f => f ()) (ψ := id) (by fun_prop : Measurable fun f : Unit → ℝ => f ())
    measurable_id

/-- Under Wiener measure the increment `f t − f s` is `N(0, |t − s|)`. -/
theorem wienerMeasure_map_sub [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] (s t : unitInterval) :
    wienerMeasure.map (fun f : C(unitInterval, ℝ) => f t - f s)
      = gaussianReal 0 (|(t : ℝ) - s|).toNNReal := by
  unfold wienerMeasure
  rw [Measure.map_map (by fun_prop) measurable_levyPath]
  exact gaussSeq_map_brownian_sub s t

end MeynTweedie.LimitTheorems
