/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleAsymptotic
import OwenScrambling.ScrambleHammersley
import OwenScrambling.Owen1DCLT
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Loh's CLT for scrambled nets: the additive case, and two corrections (post #2, Loh 2003)

Post #2: "If we use an RQMC estimator with a digital net and nested uniform scrambling (Owen
scrambling) then a standard CLT applies and the asymptotic distribution is normally distributed"
(Loh 2003). Loh (2003) proves, by Stein's method, that for a scrambled `(0,m,s)`-net in base `b`
and an integrand whose mixed partial derivative `∂^s f/∂x₁⋯∂x_s` satisfies a Hölder condition
(Owen's smoothness class; the precise hypotheses, including the variance lower bound the proof
needs, are those of Loh's paper as summarised by Basu and Mukherjee 2017), the estimator
standardised by its own standard deviation is asymptotically `N(0,1)` as `m → ∞`.

**Reading.** "A standard CLT applies" is read as `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`, for the law
`scrambledLaw f (d m)` of the scrambled estimator of a sequence of `(0,m,s)`-nets `d m`
(`m` digits, `n = b^m` points).

## Main results

* **Loh's CLT for additive integrands, any dimension** (`tendstoInDistribution_scrambledLaw_addFn`):
  for `f(x) = Σ_j g_j(x_j)` with each `g_j` measurable and `C¹` on `[0,1]`, at least one not
  constant, `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`. Ingredients: in each coordinate a scrambled `(0,m,s)`-net
  visits every cell of length `b^{-m}` exactly once (`injective_coord_net`,
  `bijective_cellFin_scramble`), so the error is a sum over the points of independent, centred,
  bounded terms (`addTerm`, `sum_addTerm`, `integral_addTerm`, `abs_addTerm_le`) whose variances add
  to `Σ_j σ²_n(g_j)` (`sum_integral_sq_addTerm`, `integral_sq_sum_pi`); the bounded Lindeberg CLT
  of `Owen1DLindeberg` gives the CLT for EVERY fixed sequence of scrambles
  (`tendstoInDistribution_scrambledEstimate_addFn`), and `tendsto_avg_of_forall` passes to the
  mixture over the scrambles.
* `variance_scrambledLaw_addFn`: `Var(μ̂) = Σ_j σ²_n(g_j)` (the one-dimensional stratified
  variances `stratVar` of `Owen1DVariance`); `tendsto_cube_mul_variance_scrambledLaw_addFn`:
  `n³ Var(μ̂) → Σ_j (1/12) ∫₀¹ g_j'²`.
* Concrete instances for `s = 2` with the Hammersley net (`ScrambleHammersley`), any base `b ≥ 2`:
  `variance_scrambledLaw_hammersley_le` (`Var ≤ (b/(b-1)) σ²/n ≤ e σ²/n`),
  `tendsto_variance_scrambledLaw_hammersley` (`o(1/n)`) and
  `tendstoInDistribution_scrambledLaw_hammersley` (CLT, additive integrands).
* Digital shift versus nested scrambling (post #2's contrast): `digitShiftScramble` (the digital
  shift is the nested scramble with the same translation at every node of a level),
  `digitShift_ne_pair_law` (it does not have Owen's pair law). The non-normality of the
  digitally shifted estimator in one dimension is in `DigitalShift` of the `PointSets` project;
  `Owen1DCLT` contrasts the Owen net with the random shift.

**Correction 1 (scale).** The limit is not a "standard" CLT at the Monte Carlo scale: for EVERY
measurable `f ∈ L²`, `√n (μ̂ - μ) → 0` in probability (`tendsto_scrambledLaw_sqrt_error_ge`, from
`Var = o(1/n)`), so `√n (μ̂ - μ)` has no non-degenerate normal limit
(`not_tendstoInDistribution_sqrt_scaled_error`). Normality holds only after normalising by
`√Var(μ̂) = o(n^{-1/2})` (of order `n^{-3/2}` for smooth additive `f`).

**Correction 2 (integrand).** Smoothness and non-degeneracy are needed, in every dimension: a
scrambled `(0,m,s)`-net integrates step functions on elementary cubes of level `R` exactly once
`m ≥ sR` (`scrambledLaw_stepFn_ne_eq_zero`), so for such `f` no normalisation gives a normal
limit (`not_tendstoInDistribution_stepFn`). (In one dimension, `Owen1DCounterexample` gives a
discontinuous `f` with positive variance and no normal limit, and `Owen1DCLT` the constant case.)

**Not formalised.** Loh's theorem for non-additive integrands in `s ≥ 2` dimensions. There the
Haar components with two or more active coordinates couple the points through shared node
permutations, the error is no longer a sum of independent terms, and Loh's Stein-method argument
(with a lower bound on `Var(μ̂)`; Owen 1997b: `Var = O(n^{-3} (log n)^{s-1})` for smooth `f`) would
be needed. Nets with `t > 0` are not treated; the post's digital nets (e.g. Sobol' points in base
`2`) have `t > 0` in general once `s ≥ 3`, a case Loh's theorem does not cover.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal NNReal Topology

variable {b D : ℕ}

/-- The law of the scrambled-net estimator is a probability measure. -/
theorem isProbabilityMeasure_scrambledLaw {s n : ℕ} {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f)
    (d : Fin n → Fin s → Fin D → Fin b) : IsProbabilityMeasure (scrambledLaw f d) := by
  have := isProbabilityMeasure_remLaw s n
  exact isProbabilityMeasure_mixLaw (measurable_scrambledEstimate hfm d)

/-- **At the Monte Carlo scale the scrambled-net error vanishes** (Chebyshev and
`Var = o(1/n)`): for every `ε > 0`, `P(|√n (μ̂ - μ)| ≥ ε) → 0`. -/
theorem tendsto_scrambledLaw_sqrt_error_ge (hb : 1 < b) {s : ℕ} (hs : 1 ≤ s)
    (hsb : s ≤ b + 1)
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun m ↦ scrambledLaw f (d m)
      {x | ε ≤ |Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))|}) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hT := tendsto_pow_mul_variance_scrambledLaw hb hs hsb d hnet hfm hf
  have hbound : ∀ m, scrambledLaw f (d m)
      {x | ε ≤ |Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))|} ≤
      ENNReal.ofReal ((b : ℝ) ^ m * Var[fun x ↦ x; scrambledLaw f (d m)] / ε ^ 2) := by
    intro m
    have hP := isProbabilityMeasure_scrambledLaw hfm (d m)
    have hL : MemLp (fun x : ℝ ↦ x) 2 (scrambledLaw f (d m)) :=
      memLp_id_mixLaw (measurable_scrambledEstimate hfm (d m))
        (memLp_scrambledEstimate hb0 hf (d m))
    have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
    have hmean := integral_scrambledLaw hb0 hn hfm hf (d m)
    have hsq : 0 < Real.sqrt ((b : ℝ) ^ m) := Real.sqrt_pos.2 (pow_pos hb' m)
    have hc : 0 < ε / Real.sqrt ((b : ℝ) ^ m) := div_pos hε hsq
    have hset : {x | ε ≤ |Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))|} =
        {x | ε / Real.sqrt ((b : ℝ) ^ m) ≤
          |(fun x : ℝ ↦ x) x - ∫ y, (fun x : ℝ ↦ x) y ∂(scrambledLaw f (d m))|} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hmean, abs_mul, abs_of_pos hsq, div_le_iff₀ hsq, mul_comm]
    rw [hset]
    refine le_trans (meas_ge_le_variance_div_sq hL hc) (le_of_eq ?_)
    congr 1
    rw [div_pow, Real.sq_sqrt (pow_pos hb' m).le]
    field_simp
  have hlim : Tendsto (fun m ↦ ENNReal.ofReal ((b : ℝ) ^ m *
      Var[fun x ↦ x; scrambledLaw f (d m)] / ε ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hT.div_const (ε ^ 2))
    rwa [zero_div, ENNReal.ofReal_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    hbound

/-- **Correction: no CLT at the Monte Carlo scale `√n`** (post #2): for scrambled `(0,m,s)`-nets
(`s ≤ b + 1`) and EVERY measurable `f ∈ L²`, `√n (μ̂ - μ)` does not converge in distribution to any
normal law `N(m₀, v)` with `v ≠ 0` (it converges to `0` in probability). The normal limit of
Loh (2003) holds only after normalising by the true standard deviation, which is `o(n^{-1/2})`. -/
theorem not_tendstoInDistribution_sqrt_scaled_error (hb : 1 < b) {s : ℕ} (hs : 1 ≤ s)
    (hsb : s ≤ b + 1) (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s))
    [∀ m, IsProbabilityMeasure (scrambledLaw f (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution
      (fun m x ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))) atTop Y
      (fun m ↦ scrambledLaw f (d m)) P' := by
  intro h
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_Ioi (a := (1 : ℝ)))
  change (P'.map Y) (Ioi 1) ≤ atTop.liminf fun m ↦ ((scrambledLaw f (d m)).map
    (fun x ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s)))) (Ioi 1) at hle
  have hmeas : ∀ m : ℕ, Measurable
      (fun x : ℝ ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s))) := fun m ↦
    (measurable_id.sub_const _).const_mul _
  have hzero : Tendsto (fun m ↦ ((scrambledLaw f (d m)).map
      (fun x ↦ Real.sqrt ((b : ℝ) ^ m) * (x - ∫ y, f y ∂(uniformCube s)))) (Ioi 1))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_scrambledLaw_sqrt_error_ge hb hs hsb d hnet hfm hf one_pos) (fun _ ↦ zero_le)
      fun m ↦ ?_
    rw [Measure.map_apply (hmeas m) measurableSet_Ioi]
    refine measure_mono fun x hx ↦ ?_
    rw [Set.mem_preimage, Set.mem_Ioi] at hx
    rw [Set.mem_ofPred_eq]
    exact le_trans hx.le (le_abs_self _)
  rw [hzero.liminf_eq, nonpos_iff_eq_zero] at hle
  exact ne_gaussianReal_of_measure_Ioi_eq_zero hle m₀ hv hY.map_eq

/-- **Independent coordinates of a product law**: `E[g(v_j) h(v_k)] = (∫ g)(∫ h)` for
`j ≠ k` under `Measure.pi fun _ ↦ ν`. -/
theorem integral_pi_eval_mul {ι α : Type*} [Fintype ι] [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {g h : α → ℝ} (hg : AEStronglyMeasurable g ν)
    (hh : AEStronglyMeasurable h ν) {j k : ι} (hjk : j ≠ k) :
    ∫ v, g (v j) * h (v k) ∂(Measure.pi fun _ : ι ↦ ν) = (∫ x, g x ∂ν) * ∫ x, h x ∂ν := by
  have hind : iIndepFun (fun (l : ι) (v : ι → α) ↦ v l) (Measure.pi fun _ : ι ↦ ν) :=
    iIndepFun_pi (X := fun _ (x : α) ↦ x) fun _ ↦ aemeasurable_id
  have hpair := hind.indepFun hjk
  have hmj := measurePreserving_eval (fun _ : ι ↦ ν) j
  have hmk := measurePreserving_eval (fun _ : ι ↦ ν) k
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : ι ↦ ν).map (fun v : ι → α ↦ v j)) := by
    rw [show (fun v : ι → α ↦ v j) = Function.eval j from rfl, hmj.map_eq]
    exact hg
  have hh' : AEStronglyMeasurable h ((Measure.pi fun _ : ι ↦ ν).map (fun v : ι → α ↦ v k)) := by
    rw [show (fun v : ι → α ↦ v k) = Function.eval k from rfl, hmk.map_eq]
    exact hh
  have h1 := hpair.integral_comp_mul_comp (f := g) (g := h) hmj.measurable.aemeasurable
    hmk.measurable.aemeasurable hg' hh'
  have e1 : ∫ v, g (v j) ∂(Measure.pi fun _ : ι ↦ ν) = ∫ x, g x ∂ν := by
    have := integral_map hmj.measurable.aemeasurable (by rw [hmj.map_eq]; exact hg)
    rw [hmj.map_eq] at this
    exact this.symm
  have e2 : ∫ v, h (v k) ∂(Measure.pi fun _ : ι ↦ ν) = ∫ x, h x ∂ν := by
    have := integral_map hmk.measurable.aemeasurable (by rw [hmk.map_eq]; exact hh)
    rw [hmk.map_eq] at this
    exact this.symm
  calc ∫ v, g (v j) * h (v k) ∂(Measure.pi fun _ : ι ↦ ν)
      = ∫ v, ((g ∘ fun v : ι → α ↦ v j) * (h ∘ fun v : ι → α ↦ v k)) v
          ∂(Measure.pi fun _ : ι ↦ ν) := rfl
    _ = (∫ v, (g ∘ fun v : ι → α ↦ v j) v ∂(Measure.pi fun _ : ι ↦ ν)) *
          ∫ v, (h ∘ fun v : ι → α ↦ v k) v ∂(Measure.pi fun _ : ι ↦ ν) := h1
    _ = (∫ x, g x ∂ν) * ∫ x, h x ∂ν := by rw [← e1, ← e2]; rfl

/-- **Second moment of a sum of independent centred coordinates**:
`E[(Σ_j Z_j(v_j))²] = Σ_j E[Z_j²]` when the `Z_j` are centred and square integrable. -/
theorem integral_sq_sum_pi {ι α : Type*} [Fintype ι] [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {Z : ι → α → ℝ} (hZ : ∀ j, MemLp (Z j) 2 ν)
    (h0 : ∀ j, ∫ x, Z j x ∂ν = 0) :
    ∫ v, (∑ j, Z j (v j)) ^ 2 ∂(Measure.pi fun _ : ι ↦ ν) = ∑ j, ∫ x, Z j x ^ 2 ∂ν := by
  classical
  have hmp : ∀ j, MeasurePreserving (Function.eval j) (Measure.pi fun _ : ι ↦ ν) ν :=
    fun j ↦ measurePreserving_eval (fun _ : ι ↦ ν) j
  have hL : ∀ j, MemLp (fun v : ι → α ↦ Z j (v j)) 2 (Measure.pi fun _ : ι ↦ ν) := by
    intro j
    have h : MemLp (Z j) 2 ((Measure.pi fun _ : ι ↦ ν).map (Function.eval j)) := by
      rw [(hmp j).map_eq]
      exact hZ j
    exact h.comp_of_map (hmp j).measurable.aemeasurable
  have e : ∀ v : ι → α, (∑ j, Z j (v j)) ^ 2 = ∑ j, ∑ k, Z j (v j) * Z k (v k) := fun v ↦ by
    rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Eventually.of_forall e),
    integral_finsetSum (f := fun j (v : ι → α) ↦ ∑ k, Z j (v j) * Z k (v k)) _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦ (hL j).integrable_mul (hL k)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum (f := fun k (v : ι → α) ↦ Z j (v j) * Z k (v k)) _ fun k _ ↦
      (hL j).integrable_mul (hL k), Finset.sum_eq_single j]
  · have h := (hZ j).integrable_sq
    have := integral_map (hmp j).measurable.aemeasurable
      (f := fun x ↦ Z j x ^ 2) (by rw [(hmp j).map_eq]; exact h.aestronglyMeasurable)
    rw [(hmp j).map_eq] at this
    rw [this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [Function.eval]; ring)
  · intro k _ hkj
    rw [integral_pi_eval_mul (hZ j).aestronglyMeasurable (hZ k).aestronglyMeasurable
      (Ne.symm hkj), h0 j, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **A `(0,m,s)`-net has distinct coordinates**: the digit strings of coordinate `j` of
different points differ (the one-dimensional projections are `(0,m,1)`-nets). -/
theorem injective_coord_net (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (j : Fin s) :
    Function.Injective fun i ↦ d i j := by
  intro i i' h
  simp only at h
  set r : Fin s → ℕ := Function.update 0 j m with hr
  have hrs : ∑ k, r k = m := by
    rw [hr, Finset.sum_update_of_mem (Finset.mem_univ j)]
    simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]
  have hcard := card_agree_net_eq_one hb hmD hnet hrs i
  have hmem : ∀ i'', d i'' j = d i j →
      i'' ∈ Finset.univ.filter fun i' ↦ ∀ k, Agree (r k) (d i k) (d i' k) := by
    intro i'' hi''
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun k ↦ ?_⟩
    by_cases hk : k = j
    · subst hk
      rw [hr, Function.update_self, hi'']
      exact fun l _ ↦ rfl
    · rw [hr, Function.update_of_ne hk, Pi.zero_apply]
      exact fun l hl ↦ absurd hl (Nat.not_lt_zero _)
  exact Finset.card_le_one.1 hcard.le _ (hmem i rfl) _ (hmem i' h.symm)

/-- **The cell deviation bound**: for `g` `K`-Lipschitz on `[0,1]` and `w ∈ [0,1)`,
`|g((c + w)/n) - E g((c + U)/n)| ≤ K/n`. -/
theorem abs_cell_sub_integral_le {g : ℝ → ℝ} (hc : ContinuousOn g (Icc 0 1)) {K : ℝ}
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ K * |x - y|) {n : ℕ}
    (c : Fin n) {w : ℝ} (hw : w ∈ Ico (0 : ℝ) 1) :
    |g (stratumMap n c w) - ∫ x, g (stratumMap n c x) ∂uniformIco| ≤ K / n := by
  have := isProbabilityMeasure_uniformIco
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (Fin.pos c).ne')
  have hK0 : 0 ≤ K := by
    have h := hK 1 (right_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hpt : ∀ x ∈ Ico (0 : ℝ) 1, |g (stratumMap n c w) - g (stratumMap n c x)| ≤ K / n := by
    intro x hx
    refine (hK _ (stratumMap_mem_Icc c (Ico_subset_Icc_self hw)) _
      (stratumMap_mem_Icc c (Ico_subset_Icc_self hx))).trans ?_
    have heq : stratumMap n c w - stratumMap n c x = (w - x) / n := by
      simp only [stratumMap]
      ring
    rw [heq, abs_div, abs_of_pos hn]
    have hux : |w - x| ≤ 1 := abs_le.2 ⟨by linarith [hw.1, hx.2], by linarith [hw.2, hx.1]⟩
    calc K * (|w - x| / n) ≤ K * (1 / n) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hux hn.le) hK0
      _ = K / n := by ring
  have heq : g (stratumMap n c w) - ∫ x, g (stratumMap n c x) ∂uniformIco =
      ∫ x, (g (stratumMap n c w) - g (stratumMap n c x)) ∂uniformIco := by
    rw [integral_sub (integrable_const _) (integrable_cell hc c), integral_const,
      probReal_univ, one_smul]
  rw [heq]
  have h := norm_integral_le_of_norm_le_const (μ := uniformIco)
    (f := fun x ↦ g (stratumMap n c w) - g (stratumMap n c x)) (C := K / n)
    (ae_restrict_of_forall_mem measurableSet_Ico fun x hx ↦ by
      rw [Real.norm_eq_abs]
      exact hpt x hx)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h

/-- In each coordinate, a scrambled `(0,m,s)`-net with `m` digits visits every cell of length
`b^{-m}` exactly once: `i ↦ cell of coordinate j of the scrambled point i` is a bijection. -/
theorem bijective_cellFin_scramble (hb : 0 < b) {m s : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (ρ : Fin s → Scramble b m) (j : Fin s) :
    Function.Bijective fun i ↦ cellFin hb (scramble (ρ j) (d i j)) := by
  refine Finite.injective_iff_bijective.1 fun i i' h ↦ ?_
  have h1 : cellVal (scramble (ρ j) (d i j)) = cellVal (scramble (ρ j) (d i' j)) :=
    congrArg Fin.val h
  exact injective_coord_net hb le_rfl hnet j
    (scramble_injective (ρ j) (cellVal_injective hb h1))

/-- An additive integrand `x ↦ Σ_j g_j(x_j)`. -/
noncomputable def addFn {s : ℕ} (g : Fin s → ℝ → ℝ) (x : Fin s → ℝ) : ℝ := ∑ j, g j (x j)

/-- The centred contribution of point `i` to the scrambled-net estimator of an additive
integrand: `n⁻¹ Σ_j (g_j(X_{ij}) - E g_j(X_{ij} | cell))`. -/
noncomputable def addTerm {s n : ℕ} (g : Fin s → ℝ → ℝ) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) (i : Fin n) (v : Fin s → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, (g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
    ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco)

/-- A digit point with `m` digits is the stratified point of its cell. -/
theorem digitPoint_eq_stratumMap_cellFin (hb : 0 < b) {m : ℕ} (x : Fin m → Fin b) (w : ℝ) :
    digitPoint x w = stratumMap (b ^ m) (cellFin hb x) w :=
  digitPoint_eq_stratumMap x w

/-- **The error of the scrambled estimator of an additive integrand is a sum over the points**:
`μ̂ - μ = Σ_i addTerm i (u_i)`. -/
theorem sum_addTerm (hb : 0 < b) {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {g : Fin s → ℝ → ℝ}
    (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) (ρ : Fin s → Scramble b m)
    (u : Fin (b ^ m) → Fin s → ℝ) :
    ∑ i, addTerm g d ρ i (u i) =
      scrambledEstimate (addFn g) d ρ u - ∑ j, ∫ x, g j x ∂uniformIco := by
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb).ne'
  have hcell : ∀ j, ∑ i, ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco =
      ((b ^ m : ℕ) : ℝ) * ∫ x, g j x ∂uniformIco := by
    intro j
    have h1 : ∑ i, ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco =
        ∑ c : Fin (b ^ m), ∫ w, g j (stratumMap (b ^ m) c w) ∂uniformIco := by
      rw [← (bijective_cellFin_scramble hb hnet ρ j).sum_comp
        (fun c : Fin (b ^ m) ↦ ∫ w, g j (stratumMap (b ^ m) c w) ∂uniformIco)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [digitPoint_eq_stratumMap_cellFin hb]
    rw [h1, ← inv_mul_sum_integral_cell (hgc j) hn]
    have : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    field_simp
  unfold addTerm scrambledEstimate sampleMean addFn
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j ↦ ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w)
    ∂uniformIco)]
  simp only [hcell, ← Finset.mul_sum]
  have : ((b ^ m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp
  rfl

/-- The cell function of a coordinate is in `L^p`. -/
theorem memLp_cell_coord {m : ℕ} {g₁ : ℝ → ℝ} (hgm : Measurable g₁)
    (hgc : ContinuousOn g₁ (Icc 0 1)) (hb : 0 < b) (x : Fin m → Fin b) (p : ℝ≥0∞) :
    MemLp (fun w ↦ g₁ (digitPoint x w)) p uniformIco := by
  refine memLp_uniformIco_of_continuousOn (hgm.comp (measurable_digitPoint x)) ?_ p
  have hc : ContinuousOn (fun w ↦ g₁ (stratumMap (b ^ m) (cellFin hb x) w)) (Icc 0 1) :=
    hgc.comp (continuous_stratumMap _ _).continuousOn
      (fun u hu ↦ stratumMap_mem_Icc (cellFin hb x) hu)
  refine hc.congr fun w _ ↦ ?_
  rw [Function.comp_apply, digitPoint_eq_stratumMap_cellFin hb]

/-- `E[g(v_j)] = ∫ g` for `v ~ U[0,1)^s`. -/
theorem integral_uniformCube_eval {s : ℕ} {g : ℝ → ℝ} (hg : AEStronglyMeasurable g uniformIco)
    (j : Fin s) : ∫ v, g (v j) ∂(uniformCube s) = ∫ x, g x ∂uniformIco := by
  have := isProbabilityMeasure_uniformIco
  have hmp := measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j
  have := integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg)
  rw [hmp.map_eq] at this
  exact this.symm

/-- `v ↦ g(v_j)` is in `L^p(U[0,1)^s)` when `g ∈ L^p(U[0,1))`. -/
theorem memLp_uniformCube_eval {s : ℕ} {p : ℝ≥0∞} {g : ℝ → ℝ} (hg : MemLp g p uniformIco)
    (j : Fin s) : MemLp (fun v : Fin s → ℝ ↦ g (v j)) p (uniformCube s) := by
  have := isProbabilityMeasure_uniformIco
  have hmp := measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j
  have h : MemLp g p ((uniformCube s).map (Function.eval j)) := by
    rw [hmp.map_eq]
    exact hg
  exact h.comp_of_map hmp.measurable.aemeasurable

/-- The point terms are centred. -/
theorem integral_addTerm {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1))
    (hb : 0 < b) (ρ : Fin s → Scramble b m) (i : Fin (b ^ m)) :
    ∫ v, addTerm g d ρ i v ∂(uniformCube s) = 0 := by
  have := isProbabilityMeasure_uniformIco
  have := isProbabilityMeasure_uniformCube s
  have hL : ∀ j, MemLp (fun w ↦ g j (digitPoint (scramble (ρ j) (d i j)) w)) 2 uniformIco :=
    fun j ↦ memLp_cell_coord (hgm j) (hgc j) hb _ 2
  unfold addTerm
  rw [integral_const_mul, integral_finsetSum (f := fun j (v : Fin s → ℝ) ↦
    g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
      ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco) _ fun j _ ↦
    ((memLp_uniformCube_eval (hL j) j).integrable one_le_two).sub (integrable_const _)]
  rw [Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [integral_sub ((memLp_uniformCube_eval (hL j) j).integrable one_le_two)
    (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_uniformCube_eval (hL j).aestronglyMeasurable j, sub_self]

/-- The point terms are in `L²`. -/
theorem memLp_addTerm {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1))
    (hb : 0 < b) (ρ : Fin s → Scramble b m) (i : Fin (b ^ m)) :
    MemLp (addTerm g d ρ i) 2 (uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  unfold addTerm
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun j _ ↦
    (memLp_uniformCube_eval (memLp_cell_coord (hgm j) (hgc j) hb _ 2) j).sub (memLp_const _)

/-- **Variance of the point terms**: `Σ_i E[addTerm_i²] = Σ_j σ²_n(g_j)`, the sum over the
coordinates of the one-dimensional stratified variances (`stratVar`). -/
theorem sum_integral_sq_addTerm {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {g : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) (hb : 0 < b)
    (ρ : Fin s → Scramble b m) :
    ∑ i, ∫ v, addTerm g d ρ i v ^ 2 ∂(uniformCube s) = ∑ j, stratVar (b ^ m) (g j) := by
  have := isProbabilityMeasure_uniformIco
  set Z : Fin (b ^ m) → Fin s → ℝ → ℝ := fun i j w ↦
    g j (digitPoint (scramble (ρ j) (d i j)) w) -
      ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco with hZ
  have hL : ∀ i j, MemLp (fun w ↦ g j (digitPoint (scramble (ρ j) (d i j)) w)) 2 uniformIco :=
    fun i j ↦ memLp_cell_coord (hgm j) (hgc j) hb _ 2
  have hZL : ∀ i j, MemLp (Z i j) 2 uniformIco := fun i j ↦ (hL i j).sub (memLp_const _)
  have hZ0 : ∀ i j, ∫ w, Z i j w ∂uniformIco = 0 := by
    intro i j
    rw [hZ, integral_sub ((hL i j).integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hvar : ∀ i j, ∫ w, Z i j w ^ 2 ∂uniformIco =
      Var[fun w ↦ g j (stratumMap (b ^ m) (cellFin hb (scramble (ρ j) (d i j))) w);
        uniformIco] := by
    intro i j
    rw [variance_eq_integral ((hL i j).aestronglyMeasurable.aemeasurable.congr
      (Eventually.of_forall fun w ↦ by
        simp only [digitPoint_eq_stratumMap_cellFin hb]))]
    simp only [hZ, digitPoint_eq_stratumMap_cellFin hb]
  have hterm : ∀ i, ∫ v, addTerm g d ρ i v ^ 2 ∂(uniformCube s) =
      ((b ^ m : ℕ) : ℝ)⁻¹ ^ 2 * ∑ j, ∫ w, Z i j w ^ 2 ∂uniformIco := by
    intro i
    have e : ∀ v : Fin s → ℝ, addTerm g d ρ i v ^ 2 =
        ((b ^ m : ℕ) : ℝ)⁻¹ ^ 2 * (∑ j, Z i j (v j)) ^ 2 := fun v ↦ by
      unfold addTerm
      rw [mul_pow]
    rw [integral_congr_ae (Eventually.of_forall e), integral_const_mul,
      integral_sq_sum_pi (hZL i) (hZ0 i)]
  simp only [hterm, hvar, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold stratVar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact (bijective_cellFin_scramble hb hnet ρ j).sum_comp
    (fun c : Fin (b ^ m) ↦ Var[fun w ↦ g j (stratumMap (b ^ m) c w); uniformIco])

/-- **Bound on the point terms**: if each `g_j` is `K_j`-Lipschitz on `[0,1]`, then
`|addTerm_i(v)| ≤ (Σ_j K_j)/n²` for `v ∈ [0,1)^s`. -/
theorem abs_addTerm_le {m s : ℕ} {d : Fin (b ^ m) → Fin s → Fin m → Fin b}
    {g : Fin s → ℝ → ℝ} (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) {K : Fin s → ℝ}
    (hK : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g j x - g j y| ≤ K j * |x - y|)
    (hb : 0 < b) (ρ : Fin s → Scramble b m) (i : Fin (b ^ m)) {v : Fin s → ℝ}
    (hv : ∀ j, v j ∈ Ico (0 : ℝ) 1) :
    |addTerm g d ρ i v| ≤ (∑ j, K j) / ((b ^ m : ℕ) : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < ((b ^ m : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pow_pos hb)
  unfold addTerm
  rw [abs_mul, abs_of_pos (inv_pos.2 hn)]
  have h1 : |∑ j, (g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
      ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco)| ≤
      ∑ j, K j / ((b ^ m : ℕ) : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    simp only [digitPoint_eq_stratumMap_cellFin hb]
    exact abs_cell_sub_integral_le (hgc j) (hK j) _ (hv j)
  calc ((b ^ m : ℕ) : ℝ)⁻¹ * |∑ j, (g j (digitPoint (scramble (ρ j) (d i j)) (v j)) -
        ∫ w, g j (digitPoint (scramble (ρ j) (d i j)) w) ∂uniformIco)|
      ≤ ((b ^ m : ℕ) : ℝ)⁻¹ * ∑ j, K j / ((b ^ m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hn.le)
    _ = (∑ j, K j) / ((b ^ m : ℕ) : ℝ) ^ 2 := by
        rw [← Finset.sum_div]
        field_simp

/-- An additive integrand is measurable. -/
theorem measurable_addFn {s : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) :
    Measurable (addFn g) :=
  Finset.measurable_sum _ fun j _ ↦ (hgm j).comp (measurable_pi_apply j)

/-- An additive integrand with coordinates continuous on `[0,1]` is in `L²` of the cube. -/
theorem memLp_addFn {s : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) (p : ℝ≥0∞) : MemLp (addFn g) p (uniformCube s) :=
  memLp_finsetSum _ fun j _ ↦
    memLp_uniformCube_eval (memLp_uniformIco_of_continuousOn (hgm j) (hgc j) p) j

/-- The integral of an additive integrand: `∫ Σ_j g_j(x_j) = Σ_j ∫₀¹ g_j`. -/
theorem integral_addFn {s : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) :
    ∫ x, addFn g x ∂(uniformCube s) = ∑ j, ∫ x, g j x ∂uniformIco := by
  unfold addFn
  rw [integral_finsetSum (f := fun j (x : Fin s → ℝ) ↦ g j (x j)) _ fun j _ ↦
    (memLp_uniformCube_eval (memLp_uniformIco_of_continuousOn (hgm j) (hgc j) 1) j).integrable
      le_rfl]
  exact Finset.sum_congr rfl fun j _ ↦
    integral_uniformCube_eval (hgm j).aestronglyMeasurable j

/-- **The variance of a scrambled `(0,m,s)`-net for an additive integrand** is the sum of the
one-dimensional stratified variances: `Var(μ̂) = Σ_j σ²_n(g_j)`. -/
theorem variance_scrambledLaw_addFn (hb : 0 < b) {m s : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j)) (hgc : ∀ j, ContinuousOn (g j) (Icc 0 1)) :
    Var[fun x ↦ x; scrambledLaw (addFn g) d] = ∑ j, stratVar (b ^ m) (g j) := by
  have hU := isProbabilityMeasure_uniformCube s
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb).ne'
  rw [variance_scrambledLaw_eq_sum hb hn (measurable_addFn hgm) (memLp_addFn hgm hgc 2) d,
    integral_addFn hgm hgc]
  have hρ : ∀ ρ : Fin s → Scramble b m, ∫ u, (scrambledEstimate (addFn g) d ρ u -
      ∑ j, ∫ x, g j x ∂uniformIco) ^ 2 ∂(remLaw s (b ^ m)) = ∑ j, stratVar (b ^ m) (g j) := by
    intro ρ
    rw [integral_congr_ae (Eventually.of_forall fun u ↦ by
      rw [← sum_addTerm hb hnet hgc ρ u]), integral_sq_sum_pi (ν := uniformCube s)
      (fun i ↦ memLp_addTerm hgm hgc hb ρ i) (fun i ↦ integral_addTerm hgm hgc hb ρ i),
      sum_integral_sq_addTerm hnet hgm hgc hb ρ]
  rw [Finset.sum_congr rfl fun ρ _ ↦ hρ ρ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Fin s → Scramble b m) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The point terms are measurable. -/
theorem measurable_addTerm {s n : ℕ} {g : Fin s → ℝ → ℝ} (hgm : ∀ j, Measurable (g j))
    (d : Fin n → Fin s → Fin D → Fin b) (ρ : Fin s → Scramble b D) (i : Fin n) :
    Measurable (addTerm g d ρ i) := by
  unfold addTerm
  exact (Finset.measurable_sum _ fun j _ ↦
    ((hgm j).comp ((measurable_digitPoint _).comp (measurable_pi_apply j))).sub_const _).const_mul
      _

/-- **The CLT for a fixed sequence of scrambles, additive integrands** (Lindeberg): for
`(0,m,s)`-nets with `m` digits, additive `f = Σ_j g_j(x_j)` with each `g_j` measurable and `C¹`
on `[0,1]`, at least one non-constant, and ANY sequence of nested scrambles `ρ_m`, the
standardised estimator `(μ̂ - μ)/σ_n` with `σ_n² = Σ_j σ²_n(g_j)` converges in distribution to
`N(0,1)` over the remainders. -/
theorem tendstoInDistribution_scrambledEstimate_addFn (hb : 1 < b) {s : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {g g' : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) (hnc : ∃ j, ∃ x ∈ Icc (0 : ℝ) 1, g j x ≠ g j 0)
    (ρ : (m : ℕ) → Fin s → Scramble b m) [∀ m, IsProbabilityMeasure (remLaw s (b ^ m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m u ↦ (scrambledEstimate (addFn g) (d m) (ρ m) u -
      ∑ j, ∫ x, g j x ∂uniformIco) / Real.sqrt (∑ j, stratVar (b ^ m) (g j))) atTop Z
      (fun m ↦ remLaw s (b ^ m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hU := isProbabilityMeasure_uniformCube s
  have hgc : ∀ j, ContinuousOn (g j) (Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  choose K hK using fun j ↦ exists_lipschitz_of_C1 (hg j) (hg' j)
  set σ2 : ℕ → ℝ := fun m ↦ ∑ j, stratVar (b ^ m) (g j) with hσ2
  have hσ2nn : ∀ m, 0 ≤ σ2 m := fun m ↦ Finset.sum_nonneg fun j _ ↦ stratVar_nonneg _ _
  set nR : ℕ → ℝ := fun m ↦ ((b ^ m : ℕ) : ℝ) with hnR
  have hnpos : ∀ m, 0 < nR m := fun m ↦ Nat.cast_pos.2 (Nat.pow_pos hb0)
  have hNtop : Tendsto (fun m : ℕ ↦ b ^ m) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb
  have hnRtop : Tendsto nR atTop atTop := tendsto_natCast_atTop_atTop.comp hNtop
  -- the rate `n³ σ² → c > 0`
  set c : ℝ := ∑ j, (∫ x in (0 : ℝ)..1, g' j x ^ 2) / 12 with hc
  have hcube : Tendsto (fun m ↦ nR m ^ 3 * σ2 m) atTop (𝓝 c) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin s)) fun j _ ↦
      (tendsto_cube_mul_stratVar (hg j) (hg' j)).comp hNtop
    simp only [Function.comp_def] at h
    refine h.congr fun m ↦ ?_
    simp only [hnR, hσ2, Finset.mul_sum]
  have hcpos : 0 < c := by
    obtain ⟨j₀, hj₀⟩ := hnc
    have h₀ := integral_sq_deriv_pos (hg j₀) (hg' j₀) hj₀
    have hle : (∫ x in (0 : ℝ)..1, g' j₀ x ^ 2) / 12 ≤ c :=
      Finset.single_le_sum (f := fun j ↦ (∫ x in (0 : ℝ)..1, g' j x ^ 2) / 12)
        (fun j _ ↦ div_nonneg (intervalIntegral.integral_nonneg zero_le_one
          fun x _ ↦ sq_nonneg _) (by norm_num)) (Finset.mem_univ j₀)
    linarith [div_pos h₀ (show (0 : ℝ) < 12 by norm_num)]
  have hσpos : ∀ᶠ m in atTop, 0 < σ2 m := by
    filter_upwards [hcube.eventually (lt_mem_nhds hcpos)] with m hm
    exact pos_of_mul_pos_right hm (pow_nonneg (hnpos m).le 3)
  -- the terms
  set X : (m : ℕ) → Fin (b ^ m) → (Fin (b ^ m) → Fin s → ℝ) → ℝ := fun m i u ↦
    addTerm g (d m) (ρ m) i (u i) / Real.sqrt (σ2 m) with hX
  set δ : ℕ → ℝ := fun m ↦ (∑ j, K j) / Real.sqrt (nR m * (nR m ^ 3 * σ2 m)) with hδ
  have hfun : (fun m u ↦ (scrambledEstimate (addFn g) (d m) (ρ m) u -
      ∑ j, ∫ x, g j x ∂uniformIco) / Real.sqrt (∑ j, stratVar (b ^ m) (g j))) =
      fun m u ↦ ∑ i, X m i u := by
    funext m u
    rw [← sum_addTerm hb0 (hnet m) hgc (ρ m) u, Finset.sum_div]
  rw [hfun]
  refine tendstoInDistribution_sum_of_bounded (L := fun m ↦ b ^ m) (X := X)
    (fun m i ↦ ((measurable_addTerm hgm (d m) (ρ m) i).comp
      (measurable_pi_apply i)).aemeasurable.div_const _)
    (fun m ↦ iIndepFun_pi (X := fun i v ↦ addTerm g (d m) (ρ m) i v / Real.sqrt (σ2 m))
      fun i ↦ ((measurable_addTerm hgm (d m) (ρ m) i).div_const _).aemeasurable)
    (fun m i ↦ ?_) (δ := δ) ?_ (fun m i ↦ ?_) (v := 1) ?_ (by rwa [Real.toNNReal_one])
  · -- centred
    simp only [hX]
    rw [integral_div, integral_remLaw_eval (g := addTerm g (d m) (ρ m) i)
      (measurable_addTerm hgm (d m) (ρ m) i).aestronglyMeasurable i,
      integral_addTerm hgm hgc hb0 (ρ m) i, zero_div]
  · -- δ → 0
    have h1 : Tendsto (fun m ↦ nR m * (nR m ^ 3 * σ2 m)) atTop atTop :=
      hnRtop.atTop_mul_pos hcpos hcube
    exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp h1)
  · -- bounded
    filter_upwards [ae_mem_cube_remLaw s (b ^ m)] with u hu
    have hb1 := abs_addTerm_le (d := d m) hgc hK hb0 (ρ m) i (hu i)
    simp only [hX, hδ]
    have hsq : Real.sqrt (nR m * (nR m ^ 3 * σ2 m)) = nR m ^ 2 * Real.sqrt (σ2 m) := by
      rw [show nR m * (nR m ^ 3 * σ2 m) = (nR m ^ 2) ^ 2 * σ2 m by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
    rw [hsq, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), ← div_div]
    exact div_le_div_of_nonneg_right hb1 (Real.sqrt_nonneg _)
  · -- variances sum to one
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hσpos] with m hm
    have e : ∀ i, ∫ u, X m i u ^ 2 ∂(remLaw s (b ^ m)) =
        (∫ v, addTerm g (d m) (ρ m) i v ^ 2 ∂(uniformCube s)) / σ2 m := by
      intro i
      simp only [hX, div_pow, Real.sq_sqrt (hσ2nn m)]
      rw [integral_div, integral_remLaw_eval (g := fun v ↦ addTerm g (d m) (ρ m) i v ^ 2)
        ((memLp_addTerm hgm hgc hb0 (ρ m) i).integrable_sq.aestronglyMeasurable) i]
    simp only [e, ← Finset.sum_div]
    rw [sum_integral_sq_addTerm (hnet m) hgm hgc hb0 (ρ m), div_self hm.ne']

/-- **Scrambled nets integrate step functions exactly**: for a level-`R` step function and every
`(0,m,s)`-net with `m ≥ sR` (and `R ≤ m`), the scrambled estimator equals `∫ f` almost surely:
its law puts no mass off `∫ f`. -/
theorem scrambledLaw_stepFn_ne_eq_zero (hb : 0 < b) {s R m : ℕ} (hsR : s * R ≤ m) (hRm : R ≤ m)
    {d : Fin (b ^ m) → Fin s → Fin m → Fin b} (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    {G : (Fin s → ℕ) → ℝ} {M : ℝ} (hG : ∀ a, |G a| ≤ M) :
    scrambledLaw (stepFn b R G) d {x | x ≠ ∫ y, stepFn b R G y ∂(uniformCube s)} = 0 := by
  have hmeas : MeasurableSet {x : ℝ | x ≠ ∫ y, stepFn b R G y ∂(uniformCube s)} :=
    (measurableSet_singleton _).compl
  unfold scrambledLaw mixLaw
  rw [Measure.smul_apply, Measure.finsetSum_apply, Finset.sum_eq_zero, smul_zero]
  intro ρ _
  rw [Measure.map_apply (measurable_scrambledEstimate (measurable_stepFn b R G) d ρ) hmeas,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_mem_cube_remLaw s (b ^ m)] with u hu
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not]
  exact sampleMean_stepFn_scrambledPoint hb le_rfl hRm hsR hnet hG ρ hu

/-- **Correction: no CLT for step functions** (in every dimension): for a level-`R` step function
`f` and `(0,m,s)`-nets, the error `μ̂ - μ` vanishes almost surely once `m ≥ sR`, so for ANY
normalisation `c_m` the normalised error `(μ̂ - μ)/c_m` does not converge in distribution to a
normal law `N(m₀, v)` with `v ≠ 0`. Smoothness (and non-degeneracy) are needed, as in Loh (2003). -/
theorem not_tendstoInDistribution_stepFn (hb : 0 < b) {s R : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {G : (Fin s → ℕ) → ℝ} {M : ℝ} (hG : ∀ a, |G a| ≤ M) (c : ℕ → ℝ)
    [∀ m, IsProbabilityMeasure (scrambledLaw (stepFn b R G) (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution (fun m x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m) atTop
      Y (fun m ↦ scrambledLaw (stepFn b R G) (d m)) P' := by
  intro h
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_Ioi (a := (0 : ℝ)))
  change (P'.map Y) (Ioi 0) ≤ atTop.liminf fun m ↦ ((scrambledLaw (stepFn b R G) (d m)).map
    (fun x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m)) (Ioi 0) at hle
  have hev : ∀ᶠ m in atTop, ((scrambledLaw (stepFn b R G) (d m)).map
      (fun x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m)) (Ioi 0) = 0 := by
    filter_upwards [eventually_ge_atTop (s * R + R)] with m hm
    have hmeas : Measurable fun x : ℝ ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m :=
      (measurable_id.sub_const _).div_const _
    rw [Measure.map_apply hmeas measurableSet_Ioi]
    refine measure_mono_null (fun x hx ↦ ?_)
      (scrambledLaw_stepFn_ne_eq_zero hb (by omega) (by omega) (hnet m) hG)
    rw [Set.mem_preimage, Set.mem_Ioi] at hx
    rw [Set.mem_ofPred_eq]
    intro hxe
    rw [hxe, sub_self, zero_div] at hx
    exact lt_irrefl 0 hx
  have hzero : Tendsto (fun m ↦ ((scrambledLaw (stepFn b R G) (d m)).map
      (fun x ↦ (x - ∫ y, stepFn b R G y ∂(uniformCube s)) / c m)) (Ioi 0)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun m hm ↦ hm.symm)
  rw [hzero.liminf_eq, nonpos_iff_eq_zero] at hle
  exact ne_gaussianReal_of_measure_Ioi_eq_zero hle m₀ hv hY.map_eq

/-- **The exact rate for additive integrands**: `n³ Var(μ̂) → Σ_j (1/12) ∫₀¹ g_j'²`, so the
RMSE of the scrambled `(0,m,s)`-net is of order `n^{-3/2}` (no `log n` factor, compare Owen
1997b's `O(n^{-3} (log n)^{s-1})` for general smooth integrands). -/
theorem tendsto_cube_mul_variance_scrambledLaw_addFn (hb : 1 < b) {s : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {g g' : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) :
    Tendsto (fun m ↦ ((b ^ m : ℕ) : ℝ) ^ 3 * Var[fun x ↦ x; scrambledLaw (addFn g) (d m)])
      atTop (𝓝 (∑ j, (∫ x in (0 : ℝ)..1, g' j x ^ 2) / 12)) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hgc : ∀ j, ContinuousOn (g j) (Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  have hNtop : Tendsto (fun m : ℕ ↦ b ^ m) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hb
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin s)) fun j _ ↦
    (tendsto_cube_mul_stratVar (hg j) (hg' j)).comp hNtop
  refine h.congr fun m ↦ ?_
  simp only [Function.comp_def]
  rw [variance_scrambledLaw_addFn hb0 (hnet m) hgm hgc, Finset.mul_sum]

/-- **Averages over finite sets converge when every selection does**: if `a m (ρ m) → L` for
every choice `ρ m ∈ R m`, then the averages `(#R m)⁻¹ Σ_ρ a m ρ → L` (take the worst `ρ`). -/
theorem tendsto_avg_of_forall {R : ℕ → Type*} [∀ m, Fintype (R m)] [∀ m, Nonempty (R m)]
    {a : (m : ℕ) → R m → ℝ} {L : ℝ}
    (h : ∀ ρ : (m : ℕ) → R m, Tendsto (fun m ↦ a m (ρ m)) atTop (𝓝 L)) :
    Tendsto (fun m ↦ (Fintype.card (R m) : ℝ)⁻¹ * ∑ ρ, a m ρ) atTop (𝓝 L) := by
  have hmax : ∀ m, ∃ ρ ∈ (Finset.univ : Finset (R m)), ∀ ρ' ∈ (Finset.univ : Finset (R m)),
      |a m ρ' - L| ≤ |a m ρ - L| := fun m ↦
    Finset.exists_max_image _ (fun ρ ↦ |a m ρ - L|) Finset.univ_nonempty
  choose ρ _ hρ using hmax
  have hstar := h ρ
  rw [tendsto_iff_norm_sub_tendsto_zero] at hstar ⊢
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hstar
  have hc : (0 : ℝ) < (Fintype.card (R m) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have e : (Fintype.card (R m) : ℝ)⁻¹ * ∑ ρ', a m ρ' - L =
      (Fintype.card (R m) : ℝ)⁻¹ * ∑ ρ', (a m ρ' - L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_mul, abs_of_pos (inv_pos.2 hc)]
  calc (Fintype.card (R m) : ℝ)⁻¹ * |∑ ρ', (a m ρ' - L)|
      ≤ (Fintype.card (R m) : ℝ)⁻¹ * ∑ _ρ' : R m, |a m (ρ m) - L| :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun ρ' _ ↦ hρ m ρ' (Finset.mem_univ _))) (inv_nonneg.2 hc.le)
    _ = |a m (ρ m) - L| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **Loh's CLT for additive integrands** (post #2; Loh 2003, for `f = Σ_j g_j(x_j)`): for
`(0,m,s)`-nets in base `b` with `m` digits, scrambled by independent uniform nested scrambles
with independent uniform remainders, and `g_j` measurable and `C¹` on `[0,1]` with at least one
non-constant, the scrambled-net estimator standardised by its own standard deviation converges in
distribution to `N(0,1)`: `(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)` as `n = b^m → ∞`. -/
theorem tendstoInDistribution_scrambledLaw_addFn (hb : 1 < b) {s : ℕ}
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0) {g g' : Fin s → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) (hnc : ∃ j, ∃ x ∈ Icc (0 : ℝ) 1, g j x ≠ g j 0)
    [∀ m, IsProbabilityMeasure (scrambledLaw (addFn g) (d m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, addFn g y ∂(uniformCube s)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (addFn g) (d m)]) atTop Z
      (fun m ↦ scrambledLaw (addFn g) (d m)) P' := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hgc : ∀ j, ContinuousOn (g j) (Icc 0 1) := fun j x hx ↦ (hg j x hx).continuousWithinAt
  have hrem : ∀ m, IsProbabilityMeasure (remLaw s (b ^ m)) := fun m ↦
    isProbabilityMeasure_remLaw s _
  have hseq := fun ρ ↦ tendstoInDistribution_scrambledEstimate_addFn hb d hnet hgm hg hg' hnc ρ hZ
  have hY : ∀ m, Measurable (fun x : ℝ ↦ (x - ∫ y, addFn g y ∂(uniformCube s)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (addFn g) (d m)]) := fun m ↦
    (measurable_id.sub_const _).div_const _
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ (fun m ↦ (hY m).aemeasurable)
    hZ.aemeasurable]
  intro φ
  have hvar : ∀ m, Var[fun x ↦ x; scrambledLaw (addFn g) (d m)] =
      ∑ j, stratVar (b ^ m) (g j) := fun m ↦ variance_scrambledLaw_addFn hb0 (hnet m) hgm hgc
  have hmean : ∫ y, addFn g y ∂(uniformCube s) = ∑ j, ∫ x, g j x ∂uniformIco :=
    integral_addFn hgm hgc
  have hint : ∀ m, ∫ x, φ ((x - ∫ y, addFn g y ∂(uniformCube s)) /
      Real.sqrt Var[fun x ↦ x; scrambledLaw (addFn g) (d m)]) ∂(scrambledLaw (addFn g) (d m)) =
      (Fintype.card (Fin s → Scramble b m) : ℝ)⁻¹ * ∑ ρ, ∫ u,
        φ ((scrambledEstimate (addFn g) (d m) ρ u - ∑ j, ∫ x, g j x ∂uniformIco) /
          Real.sqrt (∑ j, stratVar (b ^ m) (g j))) ∂(remLaw s (b ^ m)) := by
    intro m
    rw [hvar m, hmean]
    unfold scrambledLaw
    exact integral_mixLaw (measurable_scrambledEstimate (measurable_addFn hgm) (d m))
      (g := fun x ↦ φ ((x - ∑ j, ∫ x, g j x ∂uniformIco) /
        Real.sqrt (∑ j, stratVar (b ^ m) (g j))))
      (φ.continuous.comp ((continuous_id.sub continuous_const).div_const _))
      fun ρ ↦ Integrable.of_bound
        ((φ.continuous.measurable.comp (((measurable_scrambledEstimate (measurable_addFn hgm)
          (d m) ρ).sub_const _).div_const _)).aestronglyMeasurable) ‖φ‖
        (Eventually.of_forall fun u ↦ φ.norm_coe_le_norm _)
  simp only [hint]
  refine tendsto_avg_of_forall (R := fun m ↦ Fin s → Scramble b m) fun ρ ↦ ?_
  exact ((tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (hseq ρ).forall_aemeasurable hZ.aemeasurable).1 (hseq ρ)) φ

/-- **Owen's bounds for the scrambled Hammersley net** (`s = 2`, any base `b ≥ 2`):
`Var(μ̂) ≤ (b/(b-1)) σ²/n ≤ e σ²/n` (so `≤ 2σ²/n` in base `2`), for every measurable
`f ∈ L²([0,1)²)`. The hypotheses of the general theorems are satisfiable. -/
theorem variance_scrambledLaw_hammersley_le (hb : 1 < b) (m : ℕ) {f : (Fin 2 → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) :
    Var[fun x ↦ x; scrambledLaw f (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)] ≤
      ((b : ℝ) / ((b : ℝ) - 1)) * Var[f; uniformCube 2] / (b ^ m : ℕ) ∧
    Var[fun x ↦ x; scrambledLaw f (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)] ≤
      Real.exp 1 * Var[f; uniformCube 2] / (b ^ m : ℕ) := by
  have h1 := variance_scrambledLaw_le hb le_rfl (isNet_hammersley hb m) (by omega) hfm hf
  rw [show 2 - 1 = 1 from rfl, pow_one] at h1
  exact ⟨h1, variance_scrambledLaw_le_exp_one hb le_rfl (isNet_hammersley hb m) hb hfm hf⟩

/-- **The scrambled Hammersley net beats Monte Carlo asymptotically**: `n Var(μ̂) → 0` for
every measurable `f ∈ L²([0,1)²)`. -/
theorem tendsto_variance_scrambledLaw_hammersley (hb : 1 < b) {f : (Fin 2 → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube 2)) :
    Tendsto (fun m ↦ (b : ℝ) ^ m *
      Var[fun x ↦ x; scrambledLaw f (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)])
      atTop (𝓝 0) :=
  tendsto_pow_mul_variance_scrambledLaw hb (by norm_num) (by omega) _ (isNet_hammersley hb) hfm hf

/-- **Loh's CLT for the scrambled Hammersley net and additive integrands**: in `s = 2`
dimensions, for `f(x) = g₀(x₀) + g₁(x₁)` with `C¹` coordinates, one non-constant,
`(μ̂ - μ)/√Var(μ̂) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_scrambledLaw_hammersley (hb : 1 < b) {g g' : Fin 2 → ℝ → ℝ}
    (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (g j) (g' j x) (Icc 0 1) x)
    (hg' : ∀ j, ContinuousOn (g' j) (Icc 0 1)) (hnc : ∃ j, ∃ x ∈ Icc (0 : ℝ) 1, g j x ≠ g j 0)
    [∀ m, IsProbabilityMeasure
      (scrambledLaw (addFn g) (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m))]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m x ↦ (x - ∫ y, addFn g y ∂(uniformCube 2)) /
      Real.sqrt Var[fun x ↦ x;
        scrambledLaw (addFn g) (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)]) atTop Z
      (fun m ↦ scrambledLaw (addFn g) (hammersleyDigits (lt_trans Nat.zero_lt_one hb) m)) P' :=
  tendstoInDistribution_scrambledLaw_addFn hb _ (isNet_hammersley hb) hgm hg hg' hnc hZ

/-- The **random digital shift as a nested scramble**: the permutation at every node of level
`k` is the same translation `x ↦ x + c_k` (mod `b`), whatever the prefix. -/
def digitShiftScramble {D : ℕ} [NeZero b] (c : Fin D → Fin b) : Scramble b D :=
  fun node ↦ Equiv.addRight (c node.1)

/-- The digital shift adds the shift digitwise. -/
theorem scramble_digitShiftScramble {D : ℕ} [NeZero b] (c x : Fin D → Fin b) (k : Fin D) :
    scramble (digitShiftScramble c) x k = x k + c k := rfl

/-- **The digital shift does not have Owen's pair law** (post #2's contrast between the digital
shift and nested uniform scrambling). In base `2` with two digits, the strings `x = 00` and
`x' = 10` (no common leading digit) are sent to `y = 00`, `y' = 11` by NO digital shift, whereas a
positive fraction of nested uniform scrambles does so (`card_scramble_pair`): under the digital
shift the difference `σx' - σx = x' - x` is fixed, so the scrambled pair is far from uniform on
the pairs with the same common prefix. -/
theorem digitShift_ne_pair_law :
    (∀ c : Fin 2 → Fin 2, ¬ (scramble (digitShiftScramble c) ![0, 0] = ![0, 0] ∧
      scramble (digitShiftScramble c) ![1, 0] = ![1, 1])) ∧
    0 < (Finset.univ.filter fun ρ : Scramble 2 2 ↦
      scramble ρ ![0, 0] = ![0, 0] ∧ scramble ρ ![1, 0] = ![1, 1]).card := by
  constructor
  · rintro c ⟨h1, h2⟩
    have e0 := congrFun h1 0
    have e1 := congrFun h2 0
    have e2 := congrFun h1 1
    have e3 := congrFun h2 1
    rw [scramble_digitShiftScramble] at e0 e1 e2 e3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e0 e1 e2 e3
    rw [zero_add] at e0 e2
    rw [e2] at e3
    exact absurd e3 (by decide)
  · have hcp : commonPrefix (![0, 0] : Fin 2 → Fin 2) ![1, 0] = 0 := by
      by_contra h
      have h1 : 1 ≤ commonPrefix (![0, 0] : Fin 2 → Fin 2) ![1, 0] := Nat.one_le_iff_ne_zero.2 h
      have := (agree_iff_le_commonPrefix (by norm_num) _ _).2 h1 0 (by norm_num)
      exact absurd this (by decide)
    have h := card_scramble_pair (b := 2) (by norm_num) ![0, 0] ![1, 0] ![0, 0] ![1, 1]
    rw [hcp, pairKernel_eq_const (by norm_num) (fun l hl ↦ absurd hl (Nat.not_lt_zero _))
      (by decide)] at h
    have hpos : (0 : ℝ) < (Fintype.card (Scramble 2 2) : ℝ) *
        ((2 : ℕ) : ℝ) ^ (0 + 1) /
          ((((2 : ℕ) : ℝ) - 1) * ((2 : ℕ) : ℝ) ^ 2 * ((2 : ℕ) : ℝ) ^ 2) := by
      have : (0 : ℝ) < (Fintype.card (Scramble 2 2) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
      norm_num
      positivity
    rw [mul_div_assoc] at hpos
    rw [← h] at hpos
    exact_mod_cast hpos

end RQMCMarkov.OwenScrambling
