/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.CLTCriteria
import LimitTheorems.PeriodicErgodic

/-!
# The CLT from every initial law, for periodic chains (MT §17.4.2, Theorem 17.4.5)

Meyn and Tweedie, Theorem 17.4.5 (CLT part, p. 448) and the proof of Theorem 17.4.4 (p. 447):
the book passes from the stationary chain `P_π` to every initial condition by "an obvious
generalization of Proposition 17.1.6". `CLTTransfer` does this for aperiodic chains, through the
total variation convergence `‖Pᵐ(x, ·) − π‖ → 0`, which fails for periodic chains. Here the
transfer is proved for every positive Harris chain, periodic or not; the book's claim is true.

**The argument.** For a period `d` and `L ≥ 1`, put `M = dL`. For each `m < M`,
`Sₙ = Sₘ + Sₙ₋ₘ ∘ θᵐ`, and the first `m` terms are negligible after division by `√n`. The length
`n − m` is then shortened to `n − M` for every `m`; the error is at most the sum of the `M` last
truncated increments `min(2, |t| n^{−1/2} |g(Φⱼ)|)`, whose `P_x`-expectations vanish because the
law of `Φⱼ` is dominated by `d` times a phase average, which converges to `π` in total variation
(Theorem 13.3.4 (i)). After that, the Markov property makes the average over `m < M` of the
`P_x`-characteristic functions an integral against the Cesàro average `M⁻¹ Σ_{m<M} Pᵐ(x, ·)`,
which is within `L⁻¹ Σ_{N<L} ‖phase average N − π‖` of `π` in total variation; this is small for
large `L`.

* `sum_range_mul_eq_sum_sum`: `Σ_{k<dL} F(k) = Σ_{N<L} Σ_{r<d} F(dN + r)`.
* `norm_cexp_pathSum_sub_le`: `‖e^{itsS_b} − e^{itsS_a}‖ ≤ Σ_{a≤j<b} min(2, |ts| |g(Φⱼ₊₁)|)`.
* `pow_le_smul_phaseAvg`, `integral_pow_le_phaseAvg`: `Pʲ(x, ·) ≤ d · (phase average)`.
* `tvNorm_cesaro_le_phaseAvg`: the Cesàro average against the phase averages.
* `tendstoInDistribution_pathKernel_of_stationary_periodic`: the transfer `P_π → P_x`, for every
  positive Harris chain.
* `tendstoInDistribution_pathMeasure_of_pathKernel`: from every `P_x` to every `P_μ`.

**Results.**
* **Theorem 17.4.5**, CLT part (`theorem_17_4_5_clt_periodic`, p. 448): for a positive Harris
  chain of any period, `n^{−1/2} Sₙ(g − c) ⇒ N(0, γ_g²)` under every `P_x`;
  `theorem_17_4_5_clt_initial`: under every initial law `P_μ`.

**Corrections.** None: the transfer claimed by the book holds for periodic positive Harris chains
(no counterexample exists); only the total-variation route of `CLTTransfer` needs aperiodicity.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- `Σ_{k < dL} F(k) = Σ_{N < L} Σ_{r < d} F(dN + r)`. -/
theorem sum_range_mul_eq_sum_sum {M : Type*} [AddCommMonoid M] (F : ℕ → M) (d L : ℕ) :
    ∑ k ∈ Finset.range (d * L), F k =
      ∑ N ∈ Finset.range L, ∑ r ∈ Finset.range d, F (d * N + r) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show d * (L + 1) = d * L + d by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]

omit [MeasurableSpace X] in
/-- The characteristic-function integrands of two partial sums differ by at most the truncated
increments: for `a ≤ b`,
`‖e^{its Sᵦ} − e^{its Sₐ}‖ ≤ Σ_{a ≤ j < b} min(2, |ts| |g(ω_{j+1})|)`. -/
theorem norm_cexp_pathSum_sub_le (g : X → ℝ) (t s : ℝ) (ω : ℕ → X) {a b : ℕ} (hab : a ≤ b) :
    ‖Complex.exp ((t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I) -
      Complex.exp ((t : ℂ) * ((s * pathSum g a ω : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑ j ∈ Finset.Ico a b, min 2 (|t * s| * |g (ω (j + 1))|) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    set w := Complex.exp (((t * s * g (ω (b + 1)) : ℝ) : ℂ) * Complex.I) with hw
    have hsplit : Complex.exp ((t : ℂ) * ((s * pathSum g (b + 1) ω : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I) * w := by
      rw [hw, ← Complex.exp_add, pathSum, pathSum, Finset.sum_range_succ]
      congr 1
      push_cast
      ring
    have hw1 : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hstep : ‖Complex.exp ((t : ℂ) * ((s * pathSum g (b + 1) ω : ℝ) : ℂ) * Complex.I) -
        Complex.exp ((t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I)‖ ≤
        min 2 (|t * s| * |g (ω (b + 1))|) := by
      rw [hsplit, ← mul_sub_one, norm_mul]
      have he : ‖Complex.exp ((t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        rw [show (t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I =
          ((t * (s * pathSum g b ω) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [he, one_mul]
      refine le_min ((norm_sub_le _ _).trans (by rw [hw1, norm_one]; norm_num)) ?_
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * s * g (ω (b + 1)))
      rw [hw, mul_comm _ Complex.I]
      refine this.trans (le_of_eq ?_)
      rw [Real.norm_eq_abs, abs_mul]
    calc _ ≤ ‖Complex.exp ((t : ℂ) * ((s * pathSum g (b + 1) ω : ℝ) : ℂ) * Complex.I) -
          Complex.exp ((t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I)‖ +
          ‖Complex.exp ((t : ℂ) * ((s * pathSum g b ω : ℝ) : ℂ) * Complex.I) -
          Complex.exp ((t : ℂ) * ((s * pathSum g a ω : ℝ) : ℂ) * Complex.I)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by rw [add_comm]; exact add_le_add ih hstep


/-- `Pʲ(x, ·) ≤ d · d⁻¹ Σ_{r<d} P^{d⌊j/d⌋+r}(x, ·)`: one step is dominated by `d` times the phase
average of its block. -/
theorem pow_le_smul_phaseAvg (P : Kernel X X) [IsMarkovKernel P] {d : ℕ} (hd : 0 < d) (x : X)
    (j : ℕ) : (P ^ j : Kernel X X) x ≤ (d : ℝ≥0∞) • phaseAvg P d (j / d) (Measure.dirac x) := by
  rw [phaseAvg, smul_smul, ENNReal.mul_inv_cancel (by exact_mod_cast hd.ne')
    (ENNReal.natCast_ne_top d), one_smul]
  refine Measure.le_intro fun A hA _ => ?_
  rw [Measure.finsetSum_apply]
  have hj : (P ^ j : Kernel X X) x A =
      ((P ^ (d * (j / d) + j % d) : Kernel X X) ∘ₘ Measure.dirac x) A := by
    rw [Nat.div_add_mod, dirac_kernel]
  rw [hj]
  exact Finset.single_le_sum (f := fun r => ((P ^ (d * (j / d) + r) : Kernel X X) ∘ₘ
    Measure.dirac x) A) (fun r _ => zero_le) (Finset.mem_range.2 (Nat.mod_lt j hd))

/-- For `0 ≤ ρ ≤ 2`, `Pʲρ(x) ≤ d (π(ρ) + 2 ‖Q − π‖)`, `Q` the phase average of the block of
`j`. -/
theorem integral_pow_le_phaseAvg (P : Kernel X X) [IsMarkovKernel P] {d : ℕ} (hd : 0 < d)
    {π : Measure X} [IsFiniteMeasure π] {ρ : X → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ2 : ∀ y, ρ y ≤ 2) (x : X) (j : ℕ) :
    ∫ y, ρ y ∂(P ^ j : Kernel X X) x ≤
      d * (∫ y, ρ y ∂π + 2 * tvNorm (phaseAvg P d (j / d) (Measure.dirac x)) π) := by
  have := isFiniteMeasure_phaseAvg (P := P) hd (j / d) (Measure.dirac x)
  set Q := phaseAvg P d (j / d) (Measure.dirac x) with hQ
  have hb : ∀ y, |ρ y| ≤ 2 := fun y => by rw [abs_of_nonneg (hρ0 y)]; exact hρ2 y
  have : IsFiniteMeasure ((d : ℝ≥0∞) • Q) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top Q univ)⟩
  have hint : Integrable ρ ((d : ℝ≥0∞) • Q) :=
    Integrable.of_bound hρm.aestronglyMeasurable 2 (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have h1 := integral_mono_measure (pow_le_smul_phaseAvg P hd x j)
    (Eventually.of_forall fun y => hρ0 y) hint
  rw [integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul] at h1
  have h2 := abs_integral_sub_le_mul_tvNorm Q π hρm two_pos hb
  have h3 : ∫ y, ρ y ∂Q ≤ ∫ y, ρ y ∂π + 2 * tvNorm Q π := by
    have := (abs_le.1 h2).2; linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d))


/-- **Cesàro averages and phase averages**: for `L ≥ 1`,
`‖(dL)⁻¹ Σ_{m<dL} Pᵐ(x, ·) − π‖ ≤ L⁻¹ Σ_{N<L} ‖d⁻¹ Σ_{r<d} P^{dN+r}(x, ·) − π‖`. -/
theorem tvNorm_cesaro_le_phaseAvg (P : Kernel X X) [IsMarkovKernel P] {d : ℕ} (hd : 0 < d)
    (π : Measure X) [IsProbabilityMeasure π] (x : X) {L : ℕ} (hL : 0 < L) :
    tvNorm (((d * L : ℕ) : ℝ≥0∞)⁻¹ • ∑ m ∈ Finset.range (d * L), (P ^ m : Kernel X X) x) π ≤
      (L : ℝ)⁻¹ * ∑ N ∈ Finset.range L, tvNorm (phaseAvg P d N (Measure.dirac x)) π := by
  have hQf : ∀ N, IsFiniteMeasure (phaseAvg P d N (Measure.dirac x)) := fun N =>
    isFiniteMeasure_phaseAvg hd N _
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  have hL0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL.ne'
  have hblock : ∀ N, ∑ r ∈ Finset.range d, (P ^ (d * N + r) : Kernel X X) x =
      (d : ℝ≥0∞) • phaseAvg P d N (Measure.dirac x) := fun N => by
    rw [phaseAvg, smul_smul, ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top d), one_smul]
    exact Finset.sum_congr rfl fun r _ => (dirac_kernel _ x).symm
  have hmeas : ((d * L : ℕ) : ℝ≥0∞)⁻¹ • ∑ m ∈ Finset.range (d * L), (P ^ m : Kernel X X) x =
      (L : ℝ≥0∞)⁻¹ • ∑ N ∈ Finset.range L, phaseAvg P d N (Measure.dirac x) := by
    rw [sum_range_mul_eq_sum_sum (fun m => (P ^ m : Kernel X X) x)]
    simp_rw [hblock]
    rw [← Finset.smul_sum, smul_smul, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top d)), mul_comm (d : ℝ≥0∞)⁻¹,
      mul_assoc, ENNReal.inv_mul_cancel hd0 (ENNReal.natCast_ne_top d), mul_one]
  have hπ : π = (L : ℝ≥0∞)⁻¹ • ∑ _N ∈ Finset.range L, π := by
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
      ENNReal.inv_mul_cancel hL0 (ENNReal.natCast_ne_top L), one_smul]
  have hS1 : IsFiniteMeasure (∑ N ∈ Finset.range L, phaseAvg P d N (Measure.dirac x)) :=
    ⟨by rw [Measure.finsetSum_apply]; exact ENNReal.sum_lt_top.2 fun N _ => measure_lt_top _ _⟩
  have hS2 : IsFiniteMeasure (∑ _N ∈ Finset.range L, π) :=
    ⟨by rw [Measure.finsetSum_apply]; exact ENNReal.sum_lt_top.2 fun N _ => measure_lt_top _ _⟩
  rw [hmeas]
  conv_lhs => rw [hπ]
  refine (tvNorm_smul_le _ _ _).trans ?_
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact mul_le_mul_of_nonneg_left (tvNorm_finsetSum_le _ _ _) (by positivity)


/-- **Transfer of the CLT from the stationary chain to every initial state, for every period**:
for a positive Harris chain (aperiodic or not), if `n^{−1/2} Sₙ(g)` converges in distribution
under `P_π`, it converges to the same limit under every `P_x`. The proof replaces the total
variation convergence of `Pᵐ(x, ·)`, which fails for periodic chains, by that of the Cesàro
averages `(dL)⁻¹ Σ_{m<dL} Pᵐ(x, ·)` (Theorem 13.3.4 (i)), and controls the end effect of
shifting the start of the sum by `m < dL` steps through the same averages. -/
theorem tendstoInDistribution_pathKernel_of_stationary_periodic
    [MeasurableSpace.CountablyGenerated X] {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {g : X → ℝ} (hg : Measurable g) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (h : haveI := isProbabilityMeasure_pathMeasure P π
      TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum g n ω) atTop Z
        (fun _ => pathMeasure P π) P') (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum g n ω) atTop Z
      (fun _ => pathKernel P x) P' := by
  have := isProbabilityMeasure_pathMeasure P π
  have := isMarkovKernel_pathKernel P
  obtain ⟨d, hper⟩ := exists_isPeriod P hph.1.1
  have hd : 0 < d := hper.1
  have hSm : ∀ n : ℕ, Measurable fun ω : ℕ → X => (√(n : ℝ))⁻¹ * pathSum g n ω := fun n =>
    measurable_const.mul (measurable_pathSum hg n)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hSm n).aemeasurable)
    h.aemeasurable_limit fun t => ?_
  set φ := charFun (P'.map Z) t with hφ
  -- the characteristic functions as integrals
  have hcf : ∀ (μ : Measure (ℕ → X)) (n : ℕ), charFun (μ.map fun ω => (√(n : ℝ))⁻¹ *
      pathSum g n ω) t = ∫ ω, Complex.exp ((t : ℂ) * (((√(n : ℝ))⁻¹ * pathSum g n ω : ℝ) : ℂ) *
        Complex.I) ∂μ := by
    intro μ n
    have hcont : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) := by
      fun_prop
    rw [charFun_apply_real, integral_map (hSm n).aemeasurable hcont.aestronglyMeasurable]
  simp_rw [hcf]
  set E : (ℕ → X) → ℕ → ℕ → ℂ := fun ω n j => Complex.exp ((t : ℂ) *
    (((√(n : ℝ))⁻¹ * pathSum g j ω : ℝ) : ℂ) * Complex.I) with hE
  have hEm : ∀ n j, Measurable fun ω => E ω n j := fun n j =>
    Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul (measurable_pathSum hg j)))).mul measurable_const)
  have hE1 : ∀ ω n j, ‖E ω n j‖ = 1 := fun ω n j => by
    simp only [hE]
    rw [show (t : ℂ) * (((√(n : ℝ))⁻¹ * pathSum g j ω : ℝ) : ℂ) * Complex.I =
      ((t * ((√(n : ℝ))⁻¹ * pathSum g j ω) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hEint : ∀ (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ] n j,
      Integrable (fun ω => E ω n j) μ := fun μ _ n j =>
    Integrable.of_bound (hEm n j).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hE1 ω n j).le)
  have hEsh : ∀ m n j, Integrable (fun ω => E (shift m ω) n j) (pathKernel P x) := fun m n j =>
    Integrable.of_bound ((hEm n j).comp (measurable_shift m)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hE1 _ n j).le)
  -- for each `m`: the stationary part converges
  have hstat : ∀ m : ℕ, Tendsto (fun n => ∫ ω, E ω n (n - m) ∂pathMeasure P π) atTop (𝓝 φ) := by
    intro m
    have hN : Tendsto (fun n : ℕ => n - m) atTop atTop := tendsto_sub_atTop_nat m
    have hc : Tendsto (fun n : ℕ => √((n - m : ℕ) : ℝ) / √(n : ℝ)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => ((n - m : ℕ) : ℝ) / n) atTop (𝓝 1) := by
        have h2 : Tendsto (fun n : ℕ => 1 - (m : ℝ) / n) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
        rw [sub_zero] at h2
        refine h2.congr' (eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩)
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        change (1 : ℝ) - m / n = ((n - m : ℕ) : ℝ) / n
        rw [Nat.cast_sub (by omega)]
        field_simp
      have h3 := (Real.continuous_sqrt.tendsto _).comp h1
      rw [Real.sqrt_one] at h3
      refine h3.congr fun n => ?_
      rw [Function.comp_apply, Real.sqrt_div' _ (Nat.cast_nonneg n)]
    have hX := tendstoInDistribution_const_mul_seq (tendstoInDistribution_comp_index h hN) hc
    rw [show (fun ω => 1 * Z ω) = Z from funext fun ω => one_mul _] at hX
    have hcf' := hX.tendsto_charFun t
    rw [← hφ] at hcf'
    refine hcf'.congr' (eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩)
    have hmeas : Measurable fun ω => √((n - m : ℕ) : ℝ) / √(n : ℝ) *
        ((√((n - m : ℕ) : ℝ))⁻¹ * pathSum g (n - m) ω) :=
      measurable_const.mul (measurable_const.mul (measurable_pathSum hg _))
    have hcont : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) := by
      fun_prop
    rw [charFun_apply_real, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hE]
    congr 2
    have hn0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
    have hnm0 : (0 : ℝ) < √((n - m : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n - m by omega))
    have c1 : ((√((n - m : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnm0.ne'
    have c2 : ((√(n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp
  -- for each `m`: the first `m` terms are negligible
  have hfirst : ∀ m : ℕ, Tendsto (fun n => ∫ ω, (E ω n n - E (shift m ω) n (n - m))
      ∂pathKernel P x) atTop (𝓝 0) := by
    intro m
    have hpt : ∀ ω, Tendsto (fun n => E ω n n - E (shift m ω) n (n - m)) atTop (𝓝 0) := by
      intro ω
      have hfac : ∀ n, m ≤ n → E ω n n - E (shift m ω) n (n - m) =
          E (shift m ω) n (n - m) * (Complex.exp ((t : ℂ) *
            (((√(n : ℝ))⁻¹ * pathSum g m ω : ℝ) : ℂ) * Complex.I) - 1) := by
        intro n hmn
        simp only [hE]
        rw [pathSum_split g hmn ω, mul_sub, mul_one, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      have hlim : Tendsto (fun n : ℕ => Complex.exp ((t : ℂ) *
          (((√(n : ℝ))⁻¹ * pathSum g m ω : ℝ) : ℂ) * Complex.I) - 1) atTop (𝓝 0) := by
        have hsq : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have h2 := hsq.mul_const (pathSum g m ω)
        rw [zero_mul] at h2
        have h3 : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) - 1 := by
          fun_prop
        have h4 := (h3.tendsto 0).comp h2
        rw [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, sub_self] at h4
        exact h4
      have hnorm : Tendsto (fun n : ℕ => ‖Complex.exp ((t : ℂ) *
          (((√(n : ℝ))⁻¹ * pathSum g m ω : ℝ) : ℂ) * Complex.I) - 1‖) atTop (𝓝 0) := by
        simpa using hlim.norm
      exact squeeze_zero_norm' (eventually_atTop.2 ⟨m, fun n hn => by
        rw [hfac n hn, norm_mul, hE1, one_mul]⟩) hnorm
    have h1 := tendsto_integral_of_dominated_convergence (μ := pathKernel P x)
      (F := fun n ω => E ω n n - E (shift m ω) n (n - m)) (f := fun _ => (0 : ℂ))
      (fun _ => (2 : ℝ)) (fun n => ((hEm n n).sub ((hEm n (n - m)).comp
        (measurable_shift m))).aestronglyMeasurable) (integrable_const 2)
      (fun n => Eventually.of_forall fun ω => (norm_sub_le _ _).trans (by
        rw [hE1, hE1]; norm_num)) (Eventually.of_forall hpt)
    simpa using h1
  -- the Markov property at time `m`
  have hmarkov : ∀ m n j, ∫ ω, E (shift m ω) n j ∂pathKernel P x =
      ∫ y, ∫ ω, E ω n j ∂pathKernel P y ∂(P ^ m : Kernel X X) x := by
    intro m n j
    have := isMarkovKernel_pow P m
    rw [← integral_map (measurable_shift m).aemeasurable (hEm n j).aestronglyMeasurable,
      pathKernel_map_shift, pathMeasure_eq_comp]
    have := isProbabilityMeasure_pathMeasure P ((P ^ m : Kernel X X) x)
    rw [integral_measure_comp_complex]
    rw [← pathMeasure_eq_comp]
    exact hEint _ n j
  have hstatm : ∀ n j, ∫ ω, E ω n j ∂pathMeasure P π =
      ∫ y, ∫ ω, E ω n j ∂pathKernel P y ∂π := by
    intro n j
    rw [pathMeasure_eq_comp, integral_measure_comp_complex]
    rw [← pathMeasure_eq_comp]
    exact hEint _ n j
  have hhm : ∀ n j, Measurable fun y => ∫ ω, E ω n j ∂pathKernel P y := fun n j =>
    (StronglyMeasurable.integral_kernel (hEm n j).stronglyMeasurable).measurable
  have hh1 : ∀ n j y, ‖∫ ω, E ω n j ∂pathKernel P y‖ ≤ 1 := fun n j y =>
    (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω =>
      (hE1 ω n j).le)).trans (by simp)
  -- the phase averages and their Cesàro means
  have htv : Tendsto (fun N => tvNorm (phaseAvg P d N (Measure.dirac x)) π) atTop (𝓝 0) :=
    theorem_13_3_4_i hph hper hπ (Measure.dirac x)
  have hτc := htv.cesaro
  -- the truncated increments `ρₙ = min(2, |t| n^{−1/2} |g|)`
  set ρ : ℕ → X → ℝ := fun n y => min 2 (|t * (√(n : ℝ))⁻¹| * |g y|) with hρ
  have hρm : ∀ n, Measurable (ρ n) := fun n =>
    measurable_const.min (measurable_const.mul (continuous_abs.measurable.comp hg))
  have hρ0 : ∀ n y, 0 ≤ ρ n y := fun n y => le_min zero_le_two (by positivity)
  have hρ2 : ∀ n y, ρ n y ≤ 2 := fun n y => min_le_left _ _
  have hρπ : Tendsto (fun n => ∫ y, ρ n y ∂π) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hpt : ∀ y, Tendsto (fun n => ρ n y) atTop (𝓝 0) := fun y => by
      have h1 := ((hsq.const_mul t).abs.mul_const |g y|)
      rw [mul_zero, abs_zero, zero_mul] at h1
      have hc : Continuous fun z : ℝ => min (2 : ℝ) z := continuous_const.min continuous_id
      have h2 := (hc.tendsto 0).comp h1
      rw [min_eq_right zero_le_two] at h2
      exact h2
    have h := tendsto_integral_of_dominated_convergence (μ := π) (F := ρ) (f := fun _ => 0)
      (fun _ => (2 : ℝ)) (fun n => (hρm n).aestronglyMeasurable) (integrable_const 2)
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 n y)]; exact hρ2 n y)
      (Eventually.of_forall hpt)
    rwa [integral_zero] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the averaging length `M = dL`
  obtain ⟨L0, hL0⟩ := Metric.tendsto_atTop.1 hτc (ε / 8) (by positivity)
  set L := L0 + 1 with hLdef
  have hLpos : 0 < L := Nat.succ_pos L0
  have hLb : (L : ℝ)⁻¹ * ∑ N ∈ Finset.range L, tvNorm (phaseAvg P d N (Measure.dirac x)) π <
      ε / 8 := by
    have := hL0 L (by omega)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun N _ => tvNorm_nonneg _ _))] at this
  set M := d * L with hMdef
  have hMpos : 0 < M := Nat.mul_pos hd hLpos
  -- the end effect `W n`
  set W : ℕ → ℝ := fun n => ∑ i ∈ Finset.range M,
    ∫ y, ρ n y ∂(P ^ (n - M + 1 + i) : Kernel X X) x with hWdef
  have hW : Tendsto W atTop (𝓝 0) := by
    have hterm : ∀ i ∈ Finset.range M, Tendsto (fun n => (d : ℝ) * (∫ y, ρ n y ∂π +
        2 * tvNorm (phaseAvg P d ((n - M + 1 + i) / d) (Measure.dirac x)) π)) atTop (𝓝 0) := by
      intro i _
      have hidx : Tendsto (fun n : ℕ => (n - M + 1 + i) / d) atTop atTop :=
        (Nat.tendsto_div_const_atTop hd.ne').comp
          (tendsto_atTop_atTop.2 fun b => ⟨b + M, fun n hn => by omega⟩)
      have := (hρπ.add ((htv.comp hidx).const_mul 2)).const_mul (d : ℝ)
      rwa [mul_zero, add_zero, mul_zero] at this
    have hsum := tendsto_finsetSum _ hterm
    rw [Finset.sum_const_zero] at hsum
    refine squeeze_zero (fun n => Finset.sum_nonneg fun i _ =>
      integral_nonneg fun y => hρ0 n y) (fun n => Finset.sum_le_sum fun i _ => ?_) hsum
    have := isMarkovKernel_pow P (n - M + 1 + i)
    exact integral_pow_le_phaseAvg P hd (hρm n) (hρ0 n) (hρ2 n) x _
  have hend : ∀ m < M, ∀ n, M ≤ n → ‖∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x -
      ∫ ω, E (shift m ω) n (n - M) ∂pathKernel P x‖ ≤ W n := by
    intro m hm n hn
    rw [← integral_sub (hEsh m n _) (hEsh m n _)]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ ω : ℕ → X, ‖E (shift m ω) n (n - m) - E (shift m ω) n (n - M)‖ ≤
        ∑ j ∈ Finset.Ico (n - M) (n - m), ρ n (ω (m + (j + 1))) := fun ω => by
      have := norm_cexp_pathSum_sub_le g t (√(n : ℝ))⁻¹ (shift m ω) (a := n - M) (b := n - m)
        (by omega)
      exact this
    have hint : ∀ j, Integrable (fun ω : ℕ → X => ρ n (ω (m + (j + 1)))) (pathKernel P x) :=
      fun j => Integrable.of_bound ((hρm n).comp (measurable_pi_apply _)).aestronglyMeasurable 2
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 n _)]; exact hρ2 n _)
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
      (integrable_finsetSum _ fun j _ => hint j) (Eventually.of_forall hpt)).trans ?_
    rw [integral_finsetSum _ fun j _ => hint j]
    simp_rw [integral_coord_eq P (hρm n) x]
    set F : ℕ → ℝ := fun k => ∫ y, ρ n y ∂(P ^ k : Kernel X X) x with hF
    have hF0 : ∀ k, 0 ≤ F k := fun k => integral_nonneg fun y => hρ0 n y
    change ∑ j ∈ Finset.Ico (n - M) (n - m), F (m + (j + 1)) ≤ W n
    have h1 : ∑ j ∈ Finset.Ico (n - M) (n - m), F (m + (j + 1)) =
        ∑ k ∈ Finset.Ico (n - M + (m + 1)) (n - m + (m + 1)), F k := by
      rw [← Finset.sum_Ico_add']
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1; ring
    have h2 : ∑ k ∈ Finset.Ico (n - M + (m + 1)) (n - m + (m + 1)), F k ≤
        ∑ k ∈ Finset.Ico (n - M + 1) (n + 1), F k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => hF0 k
      rw [Finset.mem_Ico] at hk ⊢
      omega
    have h3 : ∑ k ∈ Finset.Ico (n - M + 1) (n + 1), F k = W n := by
      rw [Finset.sum_Ico_eq_sum_range, show n + 1 - (n - M + 1) = M by omega]
    rw [h1]
    exact h2.trans h3.le
  -- the Cesàro average of `Pᵐ(x, ·)`, `m < M`
  set Ces : Measure X := ((M : ℕ) : ℝ≥0∞)⁻¹ • ∑ m ∈ Finset.range M, (P ^ m : Kernel X X) x
    with hCes
  have hM0 : ((M : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hCesP : IsProbabilityMeasure Ces := ⟨by
    rw [hCes, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    have h1 : ∀ m ∈ Finset.range M, (P ^ m : Kernel X X) x univ = 1 := fun m _ => by
      have := isMarkovKernel_pow P m; exact measure_univ
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      ENNReal.inv_mul_cancel hM0 (ENNReal.natCast_ne_top M)]⟩
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hCesint : ∀ n, ∫ y, ∫ ω, E ω n (n - M) ∂pathKernel P y ∂Ces =
      (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∫ ω, E (shift m ω) n (n - M) ∂pathKernel P x := by
    intro n
    have hi : ∀ m ∈ Finset.range M, Integrable (fun y => ∫ ω, E ω n (n - M) ∂pathKernel P y)
        ((P ^ m : Kernel X X) x) := fun m _ => by
      have := isMarkovKernel_pow P m
      exact Integrable.of_bound (hhm n _).aestronglyMeasurable 1
        (Eventually.of_forall fun y => hh1 n _ y)
    rw [hCes, integral_smul_measure, integral_finsetSum_measure hi, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Complex.real_smul]
    simp_rw [hmarkov]
    push_cast
    rfl
  have hT3 : ∀ n, ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∫ ω, E (shift m ω) n (n - M)
      ∂pathKernel P x - ∫ ω, E ω n (n - M) ∂pathMeasure P π‖ ≤ ε / 4 := by
    intro n
    rw [← hCesint, hstatm]
    refine (norm_integral_sub_le_two_tvNorm (hhm n _) (hh1 n _)).trans ?_
    have := tvNorm_cesaro_le_phaseAvg P hd π x hLpos
    linarith
  -- the three vanishing parts
  have hT1 : Tendsto (fun n => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (∫ ω, E ω n n ∂pathKernel P x - ∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x)) atTop
      (𝓝 0) := by
    have h := (tendsto_finsetSum (Finset.range M) fun m _ => hfirst m).const_mul (M : ℂ)⁻¹
    rw [Finset.sum_const_zero, mul_zero] at h
    refine h.congr fun n => ?_
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    exact integral_sub (hEint _ n n) (hEsh m n _)
  have hT2 : Tendsto (fun n => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
      (∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x -
        ∫ ω, E (shift m ω) n (n - M) ∂pathKernel P x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (eventually_atTop.2 ⟨M, fun n hn => ?_⟩) hW
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ m ∈ Finset.range M, (∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x -
        ∫ ω, E (shift m ω) n (n - M) ∂pathKernel P x)‖ ≤ M * W n := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum fun m (hm : m ∈ Finset.range M) =>
        hend m (Finset.mem_range.1 hm) n hn
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
    calc (M : ℝ)⁻¹ * ‖_‖ ≤ (M : ℝ)⁻¹ * (M * W n) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = W n := by field_simp
  have hT4 := tendsto_sub_nhds_zero_iff.2 (hstat M)
  have hsum3 := (hT1.add hT2).add hT4
  rw [add_zero, add_zero] at hsum3
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hsum3 (ε / 2) (by positivity)
  refine ⟨max N₁ M, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  rw [dist_eq_norm, sub_zero] at h1
  rw [dist_eq_norm]
  have hid : ∫ ω, E ω n n ∂pathKernel P x - φ =
      ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
        (∫ ω, E ω n n ∂pathKernel P x - ∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x) +
      (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M,
        (∫ ω, E (shift m ω) n (n - m) ∂pathKernel P x -
          ∫ ω, E (shift m ω) n (n - M) ∂pathKernel P x) +
      (∫ ω, E ω n (n - M) ∂pathMeasure P π - φ)) +
      ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∫ ω, E (shift m ω) n (n - M) ∂pathKernel P x -
        ∫ ω, E ω n (n - M) ∂pathMeasure P π) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
    ring
  rw [hid]
  calc _ ≤ _ := norm_add_le _ _
    _ < ε / 2 + ε / 4 := add_lt_add_of_lt_of_le h1 (hT3 n)
    _ < ε := by linarith


/-- **From every initial state to every initial law**: if `Yₙ ⇒ Z` in distribution under `P_x`
for every `x`, then also under `P_μ = ∫ μ(dx) P_x` for every initial probability `μ` (dominated
convergence of the characteristic functions). -/
theorem tendstoInDistribution_pathMeasure_of_pathKernel (P : Kernel X X) [IsMarkovKernel P]
    {Y : ℕ → (ℕ → X) → ℝ} (hY : ∀ n, Measurable (Y n)) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (h : haveI := isMarkovKernel_pathKernel P
      ∀ x, TendstoInDistribution Y atTop Z (fun _ => pathKernel P x) P')
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution Y atTop Z (fun _ => pathMeasure P μ) P' := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := univ)
    (by rw [measure_univ]; exact one_ne_zero)
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hY n).aemeasurable)
    (h x₀).aemeasurable_limit fun t => ?_
  have hcont : Continuous fun y : ℝ => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) := by fun_prop
  have hcf : ∀ (ν : Measure (ℕ → X)) (n : ℕ), charFun (ν.map (Y n)) t =
      ∫ ω, Complex.exp ((t : ℂ) * (Y n ω : ℂ) * Complex.I) ∂ν := fun ν n => by
    rw [charFun_apply_real, integral_map (hY n).aemeasurable hcont.aestronglyMeasurable]
  have hm : ∀ n, Measurable fun ω => Complex.exp ((t : ℂ) * (Y n ω : ℂ) * Complex.I) :=
    fun n => hcont.measurable.comp (hY n)
  have h1 : ∀ n ω, ‖Complex.exp ((t : ℂ) * (Y n ω : ℂ) * Complex.I)‖ = 1 := fun n ω => by
    rw [show (t : ℂ) * (Y n ω : ℂ) * Complex.I = ((t * Y n ω : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hmix : ∀ n, charFun ((pathMeasure P μ).map (Y n)) t =
      ∫ x, charFun ((pathKernel P x).map (Y n)) t ∂μ := fun n => by
    simp_rw [hcf]
    rw [pathMeasure_eq_comp, integral_measure_comp_complex]
    rw [← pathMeasure_eq_comp]
    exact Integrable.of_bound (hm n).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (h1 n ω).le)
  simp_rw [hmix]
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => charFun ((pathKernel P x).map (Y n)) t)
    (f := fun _ => charFun (P'.map Z) t) (fun _ => (1 : ℝ))
    (fun n => by
      simp_rw [hcf]
      exact (StronglyMeasurable.integral_kernel (hm n).stronglyMeasurable).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [hcf]
      exact (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω =>
        (h1 n ω).le)).trans (by simp))
    (Eventually.of_forall fun x => (h x).tendsto_charFun t)
  rwa [integral_const, probReal_univ, one_smul] at hlim

/-- **Theorem 17.4.5**, the CLT (MT p. 448), from every initial state and for every period: for
a positive Harris chain (aperiodic or not) with invariant probability `π` and a solution `ĝ` of
`ĝ − Pĝ = g − c` with `ĝ, Pĝ ∈ L²(π)`, `n^{−1/2} Sₙ(g − c) ⇒ N(0, γ_g²)` under every `P_x`. -/
theorem theorem_17_4_5_clt_periodic [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hgm : Measurable g)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π).toNNReal) P')
    (x : X) :
    haveI := isMarkovKernel_pathKernel P
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun x => g x - c) n ω)
      atTop Z (fun _ => pathKernel P x) P' :=
  tendstoInDistribution_pathKernel_of_stationary_periodic hph hπ (hgm.sub measurable_const)
    (theorem_17_4_5_clt_stationary hph.1 hπ hsol hghm hgm hgh2 hPgh2 hZ) x

/-- **Theorem 17.4.5**, the CLT (MT p. 448), under every initial law `μ`, for every period. -/
theorem theorem_17_4_5_clt_initial [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hph : IsPositiveHarris P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) {g gh : X → ℝ} {c : ℝ}
    (hsol : IsPoissonSolution P g gh c) (hghm : Measurable gh) (hgm : Measurable g)
    (hgh2 : MemLp gh 2 π) (hPgh2 : MemLp (kernelInt P gh) 2 π)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (∫ x, (gh x ^ 2 - kernelInt P gh x ^ 2) ∂π).toNNReal) P')
    (μ : Measure X) [IsProbabilityMeasure μ] :
    haveI := isProbabilityMeasure_pathMeasure P μ
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * pathSum (fun x => g x - c) n ω)
      atTop Z (fun _ => pathMeasure P μ) P' :=
  tendstoInDistribution_pathMeasure_of_pathKernel P (fun n => measurable_const.mul
    (measurable_pathSum (hgm.sub measurable_const) n))
    (fun x => theorem_17_4_5_clt_periodic hph hπ hsol hghm hgm hgh2 hPgh2 hZ x) μ

end MeynTweedie.LimitTheorems
