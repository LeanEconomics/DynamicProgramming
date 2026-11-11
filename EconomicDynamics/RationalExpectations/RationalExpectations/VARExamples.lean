/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.VARMoments
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ConditionalExpectation

/-!
# Counterexamples for §2.1 and p. 56

Miao, p. 47 and p. 56. The probability space is the infinite product `Ω = ℕ → Fin N` of uniform
laws on `Fin N` (`vex_P N`, `Measure.infinitePi`), whose coordinates are independent
(`iIndepFun_infinitePi`); the filtration is `Filtration.piLE`, `F_t = σ(ω₀, …, ω_t)`.

* **A white noise need not satisfy (2.2)** (p. 56): on `ℕ → Fin 8`, `ε_{2j} = f(ω_j)` with `f`
  taking the values `−1, 0, 1` with probabilities `3/8, 1/4, 3/8`, and
  `ε_{2j+1} = 2(ε_{2j}² − 3/4)`. Then `{ε_t}` is a white noise with variance `3/4`
  (`whiteNoise_example`), but `ε₁` is a function of `ε₀`, so for every filtration to which `ε` is
  adapted (for instance `piLE`) `E₀ε₁ = ε₁ ≠ 0` (`whiteNoise_not_mds`).
* **(2.1)–(2.2) do not determine the law of `z`** (p. 47, "unique stationary distribution"): on
  `ℕ → Fin 4`, with `Φ = 0`, `Σ = 1`, the shocks `ε_t = a(ω_t)`, `a` uniform on
  `{−√2, 0, 0, √2}`, and `ε_t = b(ω_t)`, `b` uniform on `{−1, 1, 1, −1}`, both satisfy (2.2) for
  `piLE` and both `z_t = ε_t` are covariance-stationary solutions of (2.1)–(2.2) with the same
  first and second moments, but `Ez_t⁴ = 2` in the first and `1` in the second
  (`stationary_law_not_unique`). What (2.1)–(2.2) do determine for stable `Φ` is the stationary
  mean and autocovariances (`var_stationary_moments`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

/-- The uniform law on `Fin N`. -/
noncomputable abbrev vex_unif (N : ℕ) [NeZero N] : Measure (Fin N) :=
  (PMF.uniformOfFintype (Fin N)).toMeasure

/-- The product of independent uniform coordinates on `ℕ → Fin N`. -/
noncomputable abbrev vex_P (N : ℕ) [NeZero N] : Measure (ℕ → Fin N) :=
  Measure.infinitePi fun _ => vex_unif N

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem vex_coord_measurable (F : Fin N → ℝ) (j : ℕ) :
    Measurable fun ω : ℕ → Fin N => F (ω j) :=
  (measurable_of_finite F).comp (measurable_pi_apply j)

/-- `E F(ω_j) = (∑ᵢF(i))/N`. -/
theorem vex_integral_coord (F : Fin N → ℝ) (j : ℕ) :
    ∫ ω, F (ω j) ∂vex_P N = (∑ i, F i) / N := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => vex_unif N) j
  rw [show (∫ ω, F (ω j) ∂vex_P N) = ∫ x, F x ∂(Measure.map (Function.eval j) (vex_P N)) from
    (integral_map hmp.measurable.aemeasurable
      (measurable_of_finite F).aestronglyMeasurable).symm, hmp.map_eq, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, div_eq_inv_mul, Finset.mul_sum]

/-- Independent coordinates: `E F(ω_j)G(ω_{j'}) = EF(ω_j) EG(ω_{j'})` for `j ≠ j'`. -/
theorem vex_integral_coord2 (F G : Fin N → ℝ) {j j' : ℕ} (hne : j ≠ j') :
    ∫ ω, F (ω j) * G (ω j') ∂vex_P N = (∑ i, F i) / N * ((∑ i, G i) / N) := by
  have hind : IndepFun (fun ω : ℕ → Fin N => ω j) (fun ω => ω j') (vex_P N) :=
    (iIndepFun_infinitePi (P := fun _ => vex_unif N) (X := fun _ x => x)
      (fun _ => measurable_id)).indepFun hne
  have h2 := hind.comp (measurable_of_finite F) (measurable_of_finite G)
  have h3 := h2.integral_fun_mul_eq_mul_integral
    (vex_coord_measurable F j).aestronglyMeasurable
    (vex_coord_measurable G j').aestronglyMeasurable
  simp only [Function.comp_apply] at h3
  rw [h3, vex_integral_coord, vex_integral_coord]

theorem vex_memLp (F : Fin N → ℝ) (j : ℕ) : MemLp (fun ω : ℕ → Fin N => F (ω j)) 2 (vex_P N) :=
  MemLp.of_bound (vex_coord_measurable F j).aestronglyMeasurable (∑ i, |F i|)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i => |F i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ _))

omit [NeZero N] in
/-- The coordinate `ω_j` is `F_t`-measurable for `j ≤ t`. -/
theorem vex_coord_meas_piLE (F : Fin N → ℝ) {j t : ℕ} (h : j ≤ t) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => Fin N) t] fun ω => F (ω j) := by
  have h1 : Measurable[Filtration.piLE (X := fun _ : ℕ => Fin N) t]
      (Preorder.restrictLe (π := fun _ : ℕ => Fin N) t) := Measurable.of_comap_le le_rfl
  exact (measurable_of_finite F).comp
    ((measurable_pi_apply (⟨j, Set.mem_Iic.2 h⟩ : Set.Iic t)).comp h1)

/-- The coordinate `ω_{t+1}` is independent of `F_t = σ(ω₀, …, ω_t)`. -/
theorem vex_indep (F : Fin N → ℝ) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → Fin N => F (ω (t + 1))) inferInstance)
      (Filtration.piLE (X := fun _ : ℕ => Fin N) t) (vex_P N) := by
  have hi : iIndepFun (fun (i : ℕ) (ω : ℕ → Fin N) => ω i) (vex_P N) :=
    iIndepFun_infinitePi (P := fun _ => vex_unif N) (X := fun _ x => x) (fun _ => measurable_id)
  have h := hi.indepFun_finset {t + 1} (Finset.Iic t) (by simp)
    (fun i => measurable_pi_apply i)
  have hm : Measurable fun v : (({t + 1} : Finset ℕ) → Fin N) => F (v ⟨t + 1, by simp⟩) :=
    (measurable_of_finite F).comp (measurable_pi_apply _)
  have h2 := h.comp hm measurable_id
  rw [IndepFun_iff_Indep] at h2
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact h2

/-- `E_tF(ω_{t+1}) = EF(ω_{t+1})` for the filtration `piLE`. -/
theorem vex_condExp (F : Fin N → ℝ) (t : ℕ) :
    (vex_P N)[fun ω => F (ω (t + 1)) | Filtration.piLE (X := fun _ : ℕ => Fin N) t] =ᵐ[vex_P N]
      fun _ => (∑ i, F i) / N := by
  have h := condExp_indep_eq (vex_coord_measurable F (t + 1)).comap_le
    (Filtration.le _ t) (Measurable.of_comap_le le_rfl).stronglyMeasurable (vex_indep F t)
  rw [vex_integral_coord] at h
  exact h

/-! ### A white noise that does not satisfy (2.2) -/

/-- `f` takes the values `−1, 0, 1` with probabilities `3/8, 1/4, 3/8`. -/
def vex_f : Fin 8 → ℝ := ![-1, -1, -1, 0, 0, 1, 1, 1]

/-- `g = 2(f² − 3/4)`. -/
noncomputable def vex_g : Fin 8 → ℝ := fun i => 2 * (vex_f i ^ 2 - 3 / 4)

/-- `ε_{2j} = f(ω_j)`, `ε_{2j+1} = g(ω_j)`. -/
noncomputable def vex_F (t : ℕ) : Fin 8 → ℝ := if t % 2 = 0 then vex_f else vex_g

/-- The white noise of the counterexample (Miao, p. 56). -/
noncomputable def vex_wn (t : ℕ) (ω : ℕ → Fin 8) (_ : Unit) : ℝ := vex_F t (ω (t / 2))

theorem vex_sum_F (t : ℕ) : ∑ i, vex_F t i = 0 := by
  unfold vex_F
  split_ifs
  · simp [Fin.sum_univ_eight, vex_f]
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
    norm_num

theorem vex_sum_FF (t : ℕ) : ∑ i, vex_F t i * vex_F t i = 6 := by
  unfold vex_F
  split_ifs
  · simp [Fin.sum_univ_eight, vex_f]
    norm_num
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
    norm_num

theorem vex_sum_FG {t s : ℕ} (hts : t ≠ s) (hj : t / 2 = s / 2) :
    ∑ i, vex_F t i * vex_F s i = 0 := by
  have h2 : t % 2 ≠ s % 2 := by omega
  unfold vex_F
  split_ifs with h1 h3 h3
  · omega
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
  · omega

theorem vex_g_ne_zero (i : Fin 8) : vex_g i ≠ 0 := by
  fin_cases i <;> norm_num [vex_g, vex_f]

/-- Definition 2.3.3 (Miao, p. 56): `vex_wn` is a white noise with variance `3/4`. -/
theorem whiteNoise_example :
    var_IsWhiteNoise (vex_P 8) vex_wn (Matrix.of fun _ _ => (3 / 4 : ℝ)) := by
  refine ⟨fun t _ => vex_memLp (vex_F t) (t / 2), fun t _ => ?_, fun t s => ?_⟩
  · simp only [vex_wn]
    rw [vex_integral_coord, vex_sum_F, zero_div]
  · split_ifs with hts
    · subst hts
      ext i j
      change ∫ ω, vex_F t (ω (t / 2)) * vex_F t (ω (t / 2)) ∂vex_P 8 = (3 / 4 : ℝ)
      have := vex_integral_coord (N := 8) (fun x => vex_F t x * vex_F t x) (t / 2)
      rw [this, vex_sum_FF]
      norm_num
    · ext i j
      change ∫ ω, vex_F t (ω (t / 2)) * vex_F s (ω (s / 2)) ∂vex_P 8 = (0 : ℝ)
      by_cases hj : t / 2 = s / 2
      · have := vex_integral_coord (N := 8) (fun x => vex_F t x * vex_F s x) (t / 2)
        rw [← hj, this, vex_sum_FG hts hj, zero_div]
      · rw [vex_integral_coord2 _ _ hj, vex_sum_F, zero_div, zero_mul]

/-- Miao, p. 56: "a white noise may not satisfy (2.2)": for every filtration to which the white
noise `vex_wn` is adapted, `E₀ε₁ ≠ 0`, because `ε₁ = 2(ε₀² − 3/4)` is `F₀`-measurable and never
zero. Adapted filtrations exist, e.g. `piLE` (`vex_wn_adapted`). -/
theorem whiteNoise_not_mds (ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Fin 8)))
    (hℱ : ∀ t, Measurable[ℱ t] fun ω => vex_wn t ω ()) :
    ¬ (vex_P 8)[fun ω => vex_wn 1 ω () | ℱ 0] =ᵐ[vex_P 8] 0 := by
  intro h
  have he : (fun ω : ℕ → Fin 8 => vex_wn 1 ω ()) =
      fun ω => 2 * ((vex_wn 0 ω ()) ^ 2 - 3 / 4) := by
    funext ω
    simp [vex_wn, vex_F, vex_g]
  have hm : Measurable[ℱ 0] fun ω => vex_wn 1 ω () := by
    rw [he]
    exact (((hℱ 0).pow_const 2).sub_const _).const_mul _
  have hint : Integrable (fun ω => vex_wn 1 ω ()) (vex_P 8) :=
    (vex_memLp (vex_F 1) 0).integrable one_le_two
  rw [condExp_of_stronglyMeasurable (ℱ.le 0) hm.stronglyMeasurable hint] at h
  obtain ⟨ω, hω⟩ := h.exists
  exact vex_g_ne_zero (ω 0) (by simpa [vex_wn, vex_F] using hω)

/-- The white noise `vex_wn` is adapted to `piLE`. -/
theorem vex_wn_adapted (t : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => Fin 8) t] fun ω => vex_wn t ω () :=
  vex_coord_meas_piLE (vex_F t) (Nat.div_le_self t 2)

/-! ### (2.1)–(2.2) do not pin down the stationary law -/

/-- The shock `ε_t = F(ω_t)`. -/
def vex_sh (F : Fin 4 → ℝ) (t : ℕ) (ω : ℕ → Fin 4) (_ : Unit) : ℝ := F (ω t)

/-- With `∑F = 0` and `∑F² = 4`, `ε_t = F(ω_t)` satisfies (2.2) for `piLE`. -/
theorem vex_sh_mds {F : Fin 4 → ℝ} (h1 : ∑ i, F i = 0) (h2 : ∑ i, F i * F i = 4) :
    var_ShockMDS (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) (vex_sh F) := by
  refine ⟨fun t _ => vex_memLp F t, fun t _ => vex_coord_meas_piLE F le_rfl, fun t _ => ?_,
    fun t _ _ => ?_⟩
  · refine (vex_condExp F t).trans (Eventually.of_forall fun ω => ?_)
    simp [h1]
  · refine (vex_condExp (N := 4) (fun x => F x * F x) t).trans
      (Eventually.of_forall fun ω => ?_)
    simp only [h2]
    norm_num

theorem vex_zero_stable :
    IsStableMatrix ((0 : Matrix Unit Unit ℝ).map Complex.ofRealHom) := by
  refine isStableMatrix_of_tendsto 0 fun v => tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [zero_pow (by omega), Matrix.zero_mulVec]

/-- With `Φ = 0`, `z_t = ε_t` solves (2.1) with `Σ = 1`. -/
theorem vex_model {F : Fin 4 → ℝ} (h1 : ∑ i, F i = 0) (h2 : ∑ i, F i * F i = 4) :
    var_Model Unit (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) 0 1 (vex_sh F)
      (vex_sh F) := by
  refine ⟨fun t ω => ?_, fun _ => vex_memLp F 0, fun _ => vex_coord_meas_piLE F le_rfl,
    vex_sh_mds h1 h2⟩
  simp [Matrix.zero_mulVec, Matrix.one_mulVec]

theorem vex_lyapSol_zero : var_lyapSol (0 : Matrix Unit Unit ℝ) (1 * 1ᵀ) = 1 := by
  ext i j
  simp only [var_lyapSol, Matrix.of_apply]
  rw [tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
  simp

/-- The two shock laws. -/
noncomputable def vex_a : Fin 4 → ℝ := ![-Real.sqrt 2, 0, 0, Real.sqrt 2]

/-- The second shock law. -/
def vex_b : Fin 4 → ℝ := ![-1, 1, 1, -1]

theorem vex_a_sums :
    ∑ i, vex_a i = 0 ∧ ∑ i, vex_a i * vex_a i = 4 ∧ ∑ i, vex_a i ^ 4 = 8 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  refine ⟨by simp [Fin.sum_univ_four, vex_a], ?_, ?_⟩
  · simp [Fin.sum_univ_four, vex_a, h2]
    norm_num
  · have h4' : (-Real.sqrt 2) ^ 4 = 4 := by rw [Even.neg_pow (by decide), h4]
    simp [Fin.sum_univ_four, vex_a, h4, h4']
    norm_num

theorem vex_b_sums :
    ∑ i, vex_b i = 0 ∧ ∑ i, vex_b i * vex_b i = 4 ∧ ∑ i, vex_b i ^ 4 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_four, vex_b] <;> norm_num

/-- Miao, p. 47 (corrected): "if all eigenvalues of `Φ` are inside the unit circle then `{z_t}`
has a unique stationary distribution" fails under (2.1)–(2.2) alone. On one probability space
with one filtration, `Φ = 0` (stable), `Σ = 1`, the shocks `vex_sh vex_a` and `vex_sh vex_b`
both satisfy (2.2); both `z_t = ε_t` are covariance-stationary solutions with the same mean `0`
and autocovariances, yet `Ez_t⁴ = 2` for the first and `Ez_t⁴ = 1` for the second, so the laws of
`z_t` differ. -/
theorem stationary_law_not_unique :
    IsStableMatrix ((0 : Matrix Unit Unit ℝ).map Complex.ofRealHom) ∧
      var_Model Unit (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) 0 1 (vex_sh vex_a)
        (vex_sh vex_a) ∧
      var_Model Unit (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) 0 1 (vex_sh vex_b)
        (vex_sh vex_b) ∧
      var_IsCovStationary (vex_P 4) (vex_sh vex_a) ∧
      var_IsCovStationary (vex_P 4) (vex_sh vex_b) ∧
      ∀ t, ∫ ω, vex_sh vex_a t ω () ^ 4 ∂vex_P 4 = 2 ∧ ∫ ω, vex_sh vex_b t ω () ^ 4 ∂vex_P 4 = 1
    := by
  obtain ⟨a1, a2, a4⟩ := vex_a_sums
  obtain ⟨b1, b2, b4⟩ := vex_b_sums
  have ha := vex_model a1 a2
  have hb := vex_model b1 b2
  have hcov : ∀ {F : Fin 4 → ℝ}, ∑ i, F i = 0 → ∑ i, F i * F i = 4 →
      var_IsCovStationary (vex_P 4) (vex_sh F) := fun {F} h1 h2 => by
    refine (var_stationary_of_initial (vex_model h1 h2) vex_zero_stable ?_ ?_).1
    · funext i
      simp only [var_mean, vex_sh]
      rw [vex_integral_coord, h1]
      simp
    · rw [vex_lyapSol_zero]
      ext i j
      obtain rfl : i = j := Subsingleton.elim _ _
      rw [Matrix.one_apply_eq]
      change ∫ ω, F (ω 0) * F (ω 0) ∂vex_P 4 = (1 : ℝ)
      have := vex_integral_coord (N := 4) (fun x => F x * F x) 0
      rw [this, h2]
      norm_num
  refine ⟨vex_zero_stable, ha, hb, hcov a1 a2, hcov b1 b2, fun t => ⟨?_, ?_⟩⟩
  · have := vex_integral_coord (N := 4) (fun x => vex_a x ^ 4) t
    simp only [vex_sh]
    rw [this, a4]
    norm_num
  · have := vex_integral_coord (N := 4) (fun x => vex_b x ^ 4) t
    simp only [vex_sh]
    rw [this, b4]
    norm_num

end Miao.RationalExpectations
