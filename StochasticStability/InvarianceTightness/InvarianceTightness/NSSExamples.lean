/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.NSSPeriodicity
import InvarianceTightness.LinearTChains

/-!
# Forward accessible examples (MT §7.1.3, §7.2.1, §7.4)

Meyn and Tweedie, §7.1.3, pp. 151–152, the linear example of §7.2.1, p. 155, and §7.4,
pp. 161–163.

* Helpers: `duF_eq_of_hasFDerivAt`, `dxF_eq_of_hasFDerivAt` (partial derivatives from the
  sections of `F`); `hasFDerivAt_controlMap_succ_of` (the chain rule step at a point, for maps
  smooth only near the trajectory); `continuousComponent_trivial_of_dirac`;
  `continuousComponent_restrict` and `isTChain_restrictKernel_of_local` (restriction of
  continuous components to an absorbing set); `isPeriodOf_one_of_fixedPoint` (a fixed point
  `F(x*, u*) = x*`, `u* ∈ O`, in a minimal set makes it aperiodic: the deterministic form of "any
  cycle must contain `x*`", p. 161); `tendsto_zero_of_affine_recursion`.
* `isLSCDensity_uniform` (p. 149): the uniform law on a bounded open interval satisfies (SNSS3)
  (the Gaussian case is `isLSCDensity_gaussianReal` in `NSSAdaptiveControl`).
* **The simple bilinear model** (§7.1.3). `bilinear_duF`, `bilinear_dxF`,
  `bilinear_genCtrb_two`: the controllability vectors `bx₀ + 1` and
  `[(θ + bu₂)(bx₀ + 1) | bx₁ + 1]`. `bilinear_component_trivial` (p. 152): the one-step kernel
  has no everywhere non-trivial continuous component (`T(−1/b, ℝ) = 0`).
  **Proposition 7.1.3** (p. 152): `proposition_7_1_3`, under (SBL2) the bilinear model is a
  T-chain when `b = 0` or `θ ≠ 1`. **Correction:** for `θ = 1`, `b ≠ 0` the claim is false:
  `−1/b` is a fixed point of every control (`bilinear_theta_one_fixed`), so CM(F) is not forward
  accessible (`bilinear_theta_one_not_forwardAccessible`; the book's "non-zero for almost every
  `(u₁, u₂)`" fails at `x₀ = −1/b`), and the model is not a T-chain
  (`proposition_7_1_3_counterexample`, for every disturbance law without atoms).
* **The linear model** (p. 153, p. 155). `linear_rankCondition_iff`: for `F(x, u) = Ax + Bu` the
  rank condition is controllability; `lcm_isMinimal_ctrbSubspace`: with `O = ℝᵖ`, the range `X₀`
  of the controllability matrix is minimal; `lcm_minimal_unique`: under (LSS5) it is the only
  minimal set; `lcm_minimal_not_unique`: without (LSS5) uniqueness fails (`xₖ₊₁ = xₖ`).
* **The dependent parameter bilinear model** (§7.4.1). `isLSCDensity_prod`, `controlSet_prod`:
  (DBL2) gives (NSS3) with `O = O_z × O_w`; `dbl_duF`, `dbl_rankCondition`: the first order
  controllability matrix is the identity. **Proposition 7.4.1** (p. 161):
  `proposition_7_4_1_tChain` (a T-chain) and `proposition_7_4_1` (under (7.24), a `ψ`-irreducible
  aperiodic T-chain); `dbl_tendsto` is the convergence `(θₖ, Yₖ) → x*` of the proof.
* **The gumleaf attractor** (§7.4.2). `gumleafDomain = {xᵃ ≠ 0, xᵇ ≠ 0}`, `gumleaf_contDiffAt`,
  `gumleaf_duF`, `gumleaf_dxF_fst`, `gumleaf_genCtrb_two` (the second order controllability
  matrix, of full rank). **Proposition 7.4.2** (p. 162): `proposition_7_4_2`, under (NSS3) the
  domain is absorbing, every point of it has a non-trivial continuous component of `P²`, and the
  model restricted to it is a T-chain. (On all of `ℝ²` the step, with `1/0 = 0`, is not
  continuous; the book cites Proposition 7.2.6 where Proposition 7.1.5 is meant.)
* **The adaptive control model** (§7.4.3). `sac_tendsto` (p. 163): with zero
  disturbances `Φₖ → (σ_z²/(1 − α²), 0, 0)` from every state of the state space (the hypothesis
  `σ_z² < 1` is not needed). **Corrections:** the interior of the state space is not reached in one
  step from every initial condition (`sac_upper_boundary`, `sacKernel_interior_eq_zero`: from
  `(σ_z²/(1 − α²), θ̃, 0)` the chain stays on the boundary `Σ = σ_z²/(1 − α²)` for one step), and
  for `α = 0` the interior is empty (`sac_interior_empty_of_alpha_zero`). The rank computation and
  Proposition 7.4.3 itself are in `NSSAdaptiveControl`.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Helpers -/

/-- `Λ = ∂F/∂u (x, w)` from the derivative of the section `w' ↦ F(x, w')`. -/
theorem duF_eq_of_hasFDerivAt {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : X × W → X} {x : X} {w : W}
    (hF : DifferentiableAt ℝ F (x, w)) {L : W →L[ℝ] X}
    (hL : HasFDerivAt (fun w' => F (x, w')) L w) : duF F x w = L :=
  (hF.hasFDerivAt.comp w (hasFDerivAt_prodMk_right x w)).unique hL

/-- `Ξ = ∂F/∂x (x, w)` from the derivative of the section `x' ↦ F(x', w)`. -/
theorem dxF_eq_of_hasFDerivAt {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : X × W → X} {x : X} {w : W}
    (hF : DifferentiableAt ℝ F (x, w)) {L : X →L[ℝ] X}
    (hL : HasFDerivAt (fun x' => F (x', w)) L x) : dxF F x w = L :=
  (hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x w)).unique hL

/-- If the sampled kernel `K_a` puts all its mass at `z` from `x₀`, and no other point charges
`z`, then every continuous component of `K_a` vanishes at `x₀` (on `ℝ`, which has no isolated
points). -/
theorem continuousComponent_trivial_of_dirac {P : Kernel ℝ ℝ} {a : ℕ → ℝ≥0∞} {T : Kernel ℝ ℝ}
    (hT : IsContinuousComponent P a T) {x₀ z : ℝ} (h1 : sampledKernel P a x₀ {z}ᶜ = 0)
    (h2 : ∀ x, x ≠ x₀ → sampledKernel P a x {z} = 0) : T x₀ univ = 0 := by
  have hc : T x₀ {z}ᶜ = 0 := nonpos_iff_eq_zero.1 ((hT.2.1 x₀ _).trans h1.le)
  have hz : T x₀ {z} = 0 := by
    by_contra hne
    have hev := (hT.2.2 {z} (measurableSet_singleton z)) x₀ 0 (pos_iff_ne_zero.2 hne)
    obtain ⟨x, hx, hxne⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {x₀}ᶜ ∈ 𝓝[≠] x₀)).exists
    have := (hT.2.1 x {z}).trans (h2 x hxne).le
    exact (lt_of_lt_of_le hx this).ne' rfl
  have := measure_univ_le_add_compl (μ := T x₀) {z}
  rw [hz, hc, add_zero] at this
  exact nonpos_iff_eq_zero.1 this

/-- The uniform law on a bounded open interval satisfies the density condition (SNSS3), with
control set the interval (MT p. 149). -/
theorem isLSCDensity_uniform {a b : ℝ} (hab : a < b) :
    IsLSCDensity (volume.withDensity ((Ioo a b).indicator fun _ => ENNReal.ofReal (b - a)⁻¹))
      ((Ioo a b).indicator fun _ => ENNReal.ofReal (b - a)⁻¹) ∧
    controlSet ((Ioo a b).indicator fun _ => ENNReal.ofReal (b - a)⁻¹) = Ioo a b ∧
    IsProbabilityMeasure
      (volume.withDensity ((Ioo a b).indicator fun _ => ENNReal.ofReal (b - a)⁻¹)) := by
  have hba : 0 < b - a := by linarith
  refine ⟨⟨lowerSemicontinuous_indicator_of_isOpen isOpen_Ioo lowerSemicontinuous_const, rfl⟩,
    ?_, ⟨?_⟩⟩
  · ext x
    by_cases hx : x ∈ Ioo a b
    · simp [controlSet, hx, hba]
    · simp [controlSet, hx]
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_indicator measurableSet_Ioo, setLIntegral_const, Real.volume_Ioo,
      ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hba.ne', ENNReal.ofReal_one]

/-! ### The simple bilinear model (§7.1.3) -/

/-- An affine equation `c + d w = z` with `d ≠ 0` has the single solution `(z − c)/d`. -/
theorem setOf_affine_mem_singleton (c d z : ℝ) (hd : d ≠ 0) :
    {w : ℝ | c + d * w ∈ ({z} : Set ℝ)} = {(z - c) / d} := by
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff]
  rw [eq_div_iff hd]
  constructor <;> intro h <;> linarith

/-- The bilinear step is `C¹`. -/
theorem contDiff_one_bilinearStep (θ b : ℝ) : ContDiff ℝ 1 (bilinearStep θ b) := by
  unfold bilinearStep
  fun_prop

/-- The first order controllability vector of the bilinear model (MT p. 152):
`∂F/∂u (x₀, u₁) = bx₀ + 1`. -/
theorem bilinear_duF (θ b x w c : ℝ) : duF (bilinearStep θ b) x w c = (b * x + 1) * c := by
  have hd : HasDerivAt (fun w' => bilinearStep θ b (x, w')) (b * x + 1) w := by
    have : (fun w' => bilinearStep θ b (x, w')) = fun w' => θ * x + (b * x + 1) * w' := by
      funext w'; simp only [bilinearStep]; ring
    rw [this]
    simpa using ((hasDerivAt_id w).const_mul (b * x + 1)).const_add (θ * x)
  rw [duF_eq_of_hasFDerivAt ((contDiff_one_bilinearStep θ b).differentiable one_ne_zero _)
    hd.hasFDerivAt]
  simp [mul_comm]

/-- `∂F/∂x (x, w) = θ + bw` for the bilinear model (MT p. 152). -/
theorem bilinear_dxF (θ b x w a : ℝ) : dxF (bilinearStep θ b) x w a = (θ + b * w) * a := by
  have hd : HasDerivAt (fun x' => bilinearStep θ b (x', w)) (θ + b * w) x := by
    have : (fun x' => bilinearStep θ b (x', w)) = fun x' => (θ + b * w) * x' + w := by
      funext x'; simp only [bilinearStep]; ring
    rw [this]
    simpa using ((hasDerivAt_id x).const_mul (θ + b * w)).add_const w
  rw [dxF_eq_of_hasFDerivAt ((contDiff_one_bilinearStep θ b).differentiable one_ne_zero _)
    hd.hasFDerivAt]
  simp [mul_comm]

/-- The second order controllability vector (MT p. 152):
`[(θ + bu₂)(bx₀ + 1) | bx₁ + 1]` with `x₁ = F(x₀, u₁)`. -/
theorem bilinear_genCtrb_two (θ b x : ℝ) (u v : Fin 2 → ℝ) :
    genCtrb (bilinearStep θ b) 2 x u v =
      (θ + b * u 1) * ((b * x + 1) * v 0) + (b * bilinearStep θ b (x, u 0) + 1) * v 1 := by
  rw [genCtrb_succ_apply, genCtrb_one_apply, bilinear_dxF, bilinear_duF, bilinear_duF]
  rfl

/-- The rank condition (CM2) for the bilinear model when `b = 0` or `θ ≠ 1`. -/
theorem bilinear_rankCondition {θ b : ℝ} (hθb : b = 0 ∨ θ ≠ 1) {O : Set ℝ} (hO : O.Nonempty) :
    RankCondition (bilinearStep θ b) O := by
  intro x
  obtain ⟨w₀, hw₀⟩ := hO
  by_cases hx : b * x + 1 = 0
  · have hb : b ≠ 0 := by rintro rfl; simp at hx
    have hθ : θ ≠ 1 := hθb.resolve_left hb
    refine ⟨2, fun _ => w₀, by norm_num, fun _ => hw₀, fun t => ⟨![0, t / (1 - θ)], ?_⟩⟩
    rw [bilinear_genCtrb_two]
    have hx1 : b * bilinearStep θ b (x, w₀) + 1 = 1 - θ := by
      have hxb : x = -1 / b := by field_simp; linarith
      simp only [bilinearStep, hxb]
      field_simp
      ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hx1, mul_zero, mul_zero, zero_add, mul_div_cancel₀ t (sub_ne_zero.2 hθ.symm)]
  · refine ⟨1, fun _ => w₀, one_pos, fun _ => hw₀, fun t => ⟨fun _ => t / (b * x + 1), ?_⟩⟩
    rw [genCtrb_one_apply, bilinear_duF, mul_div_cancel₀ t hx]

/-- **Proposition 7.1.3** (MT p. 152), corrected: under (SBL1)–(SBL2) (a lower semicontinuous
density; the second moment is not needed) the simple bilinear model is a T-chain, provided
`b = 0` or `θ ≠ 1`. See `proposition_7_1_3_counterexample` for `θ = 1`, `b ≠ 0`. -/
theorem proposition_7_1_3 {Γ : Measure ℝ} [IsProbabilityMeasure Γ] {γ : ℝ → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) {θ b : ℝ} (hθb : b = 0 ∨ θ ≠ 1) :
    IsTChain (bilinearKernel Γ θ b) :=
  (proposition_7_1_5 hΓ (contDiff_one_bilinearStep θ b)
    (bilinear_rankCondition hθb (controlSet_nonempty hΓ))).2

/-- **The one-step kernel of the bilinear model has no everywhere non-trivial continuous
component** (MT pp. 151–152): `P(−1/b, {−θ/b}) = 1` while `P(x, {−θ/b}) = 0` for `x ≠ −1/b`, so
every continuous component `T` of `P` has `T(−1/b, ℝ) = 0`. -/
theorem bilinear_component_trivial {Γ : Measure ℝ} [IsProbabilityMeasure Γ] [NullSingletonClass Γ]
    {θ b : ℝ} (hb : b ≠ 0) {T : Kernel ℝ ℝ}
    (hT : IsContinuousComponent (bilinearKernel Γ θ b) (diracDist 1) T) : T (-1 / b) univ = 0 := by
  refine continuousComponent_trivial_of_dirac hT (z := -θ / b) ?_ fun x hx => ?_
  · rw [sampledKernel_diracDist, pow_one, bilinearKernel_apply' Γ θ b _
      (measurableSet_singleton _).compl]
    have : {w : ℝ | θ * (-1 / b) + (b * (-1 / b) + 1) * w ∈ ({-θ / b} : Set ℝ)ᶜ} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_compl_iff, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_not]
      field_simp
      ring
    rw [this, measure_empty]
  · rw [sampledKernel_diracDist, pow_one, bilinearKernel_apply' Γ θ b _ (measurableSet_singleton _)]
    have hx' : b * x + 1 ≠ 0 := fun h => hx (by field_simp; linarith)
    rw [setOf_affine_mem_singleton _ _ _ hx', measure_singleton]

/-- For `θ = 1` and `b ≠ 0`, `−1/b` is a fixed point of the bilinear step for every control. -/
theorem bilinear_theta_one_fixed {b : ℝ} (hb : b ≠ 0) (k : ℕ) (u : Fin k → ℝ) :
    controlMap (bilinearStep 1 b) k (-1 / b) u = -1 / b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [controlMap_succ, ih]
    simp only [bilinearStep]
    field_simp
    ring

/-- **Correction** (MT p. 152): for `θ = 1`, `b ≠ 0`, the control model of the bilinear model is
not forward accessible (for any control set): `A₊(−1/b) = {−1/b}`. -/
theorem bilinear_theta_one_not_forwardAccessible {b : ℝ} (hb : b ≠ 0) (O : Set ℝ) :
    ¬ IsForwardAccessible (bilinearStep 1 b) O := by
  intro h
  have hsub : reach (bilinearStep 1 b) O (-1 / b) ⊆ {-1 / b} := by
    intro y hy
    obtain ⟨k, u, -, rfl⟩ := mem_reach_iff.1 hy
    exact bilinear_theta_one_fixed hb k u
  obtain ⟨y, hy⟩ := h (-1 / b)
  have := interior_mono hsub hy
  rw [interior_singleton] at this
  exact this

/-- **Correction to Proposition 7.1.3** (MT p. 152): for `θ = 1` and `b ≠ 0` the simple bilinear
model is not a T-chain, for every disturbance law without atoms (in particular under (SBL2)):
`−1/b` is absorbing, and no other point ever reaches it. -/
theorem proposition_7_1_3_counterexample {Γ : Measure ℝ} [IsProbabilityMeasure Γ]
    [NullSingletonClass Γ] {b : ℝ} (hb : b ≠ 0) : ¬ IsTChain (bilinearKernel Γ 1 b) := by
  set P := bilinearKernel Γ 1 b
  have hM := isMarkovKernel_bilinearKernel Γ 1 b
  set x₀ : ℝ := -1 / b
  have hbx : b * x₀ + 1 = 0 := by simp only [x₀]; field_simp; ring
  have hP0 : P x₀ {x₀} = 1 := by
    rw [bilinearKernel_apply' Γ 1 b _ (measurableSet_singleton _)]
    have : {w : ℝ | 1 * x₀ + (b * x₀ + 1) * w ∈ ({x₀} : Set ℝ)} = univ := by
      ext w; simp [hbx]
    rw [this, measure_univ]
  have hAbs : IsAbsorbing P {x₀} := fun x hx => by rw [mem_singleton_iff.1 hx]; exact hP0
  have hP1 : ∀ x, x ≠ x₀ → P x {x₀} = 0 := fun x hx => by
    rw [bilinearKernel_apply' Γ 1 b _ (measurableSet_singleton _)]
    have hx' : b * x + 1 ≠ 0 := fun h => hx (by simp only [x₀]; field_simp; linarith)
    rw [setOf_affine_mem_singleton _ _ _ hx', measure_singleton]
  have hPn : ∀ n x, x ≠ x₀ → (P ^ n) x {x₀} = 0 := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
        indicator_of_notMem (by simpa using hx)]
    | succ n ih =>
      intro x hx
      rw [pow_succ_apply' P n x (measurableSet_singleton _)]
      refine nonpos_iff_eq_zero.1 ((lintegral_mono fun y => ?_).trans
        (le_of_eq ((lintegral_indicator_one (measurableSet_singleton x₀)).trans (ih x hx))))
      by_cases hy : y = x₀
      · rw [hy, indicator_of_mem (mem_singleton x₀), Pi.one_apply]
        exact prob_le_one
      · rw [hP1 y hy]; exact zero_le
  rintro ⟨a, T, -, hT, hpos⟩
  refine (hpos x₀).ne' (continuousComponent_trivial_of_dirac hT (z := x₀) ?_ fun x hx => ?_)
  · rw [sampledKernel_apply P a x₀ (measurableSet_singleton _).compl]
    simp [hAbs.pow_compl (measurableSet_singleton _) _ (mem_singleton x₀)]
  · rw [sampledKernel_apply P a x (measurableSet_singleton _)]
    simp [hPn _ x hx]

/-! ### Aperiodicity from a fixed point -/

/-- A fixed point `F(x*, u*) = x*` with `u* ∈ O` in a minimal set `M` makes `M` aperiodic: `x*`
would lie in two consecutive classes of the periodic orbit of Theorem 7.3.3. (This is the
deterministic form of the book's "any cycle must contain the state `x*`", p. 161.) -/
theorem isPeriodOf_one_of_fixedPoint {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O) (h : RankCondition F O)
    {M : Set X} (hM : IsMinimal F O M) {x : X} (hx : x ∈ M) {u : W} (hu : u ∈ O)
    (hfix : F (x, u) = x) : IsPeriodOf F O M 1 := by
  obtain ⟨d, hd, G, hG, hGM, -⟩ := theorem_7_3_3 hF hO h hM
  have hx' : x ∈ ⋃ i, G i := by rw [hGM]; exact hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx'
  have h1 := hG.step i x hi u hu
  rw [hfix] at h1
  have h2 : i + 1 = i := by
    by_contra hne
    exact Set.disjoint_left.1 (hG.disjoint _ _ hne) h1 hi
  have h3 : ((1 : ℕ) : ZMod d) = 0 := by
    push_cast
    linear_combination h2
  have hd1 : d = 1 := Nat.dvd_one.1 ((ZMod.natCast_eq_zero_iff 1 d).1 h3)
  subst hd1
  exact hd

/-! ### Affine recursions -/

/-- If `eₖ₊₁ = aₖ eₖ + bₖ` with `aₖ → a`, `|a| < 1` and `bₖ → 0`, then `eₖ → 0`. -/
theorem tendsto_zero_of_affine_recursion {a : ℝ} (ha : |a| < 1) {as bs e : ℕ → ℝ}
    (has : Tendsto as atTop (𝓝 a)) (hbs : Tendsto bs atTop (𝓝 0))
    (he : ∀ k, e (k + 1) = as k * e k + bs k) : Tendsto e atTop (𝓝 0) := by
  obtain ⟨ρ, haρ, hρ1⟩ := exists_between ha
  have hρ0 : 0 < ρ := lt_of_le_of_lt (abs_nonneg a) haρ
  have hev : ∀ᶠ k in atTop, |as k| ≤ ρ := by
    have : ∀ᶠ k in atTop, |as k| < ρ :=
      ((continuous_abs.tendsto a).comp has).eventually (gt_mem_nhds haρ)
    exact this.mono fun k hk => hk.le
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / 2 * (1 - ρ) := by nlinarith
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.1 hbs _ hε'
  set K₂ := max K K₁
  -- `|e (K₂ + j)| ≤ ρ ^ j |e K₂| + ε / 2`
  have hj : ∀ j, |e (K₂ + j)| ≤ ρ ^ j * |e K₂| + ε / 2 := by
    intro j
    induction j with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ j ih =>
      have h1 := hK (K₂ + j) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
      have h2 : |bs (K₂ + j)| < ε / 2 * (1 - ρ) := by
        have := hK₁ (K₂ + j) (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
        rwa [Real.dist_eq, sub_zero] at this
      rw [← add_assoc, he, pow_succ]
      calc |as (K₂ + j) * e (K₂ + j) + bs (K₂ + j)|
          ≤ |as (K₂ + j)| * |e (K₂ + j)| + |bs (K₂ + j)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ ρ * (ρ ^ j * |e K₂| + ε / 2) + ε / 2 * (1 - ρ) := by
            gcongr
        _ = ρ ^ j * ρ * |e K₂| + ε / 2 := by ring
  have hpow : Tendsto (fun j : ℕ => ρ ^ j * |e K₂|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const |e K₂|
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hpow (ε / 2) (by linarith)
  refine ⟨K₂ + J, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 := hJ (J + j) (Nat.le_add_right _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1
  rw [Real.dist_eq, sub_zero, add_assoc]
  linarith [hj (J + j)]

/-! ### The dependent parameter bilinear model (§7.4.1) -/

/-- (DBL2): independent `Z` and `W` with lower semicontinuous densities give the density
`γ_z(z) γ_w(w)` of `(Z, W)`, again lower semicontinuous (the density condition (NSS3)). -/
theorem isLSCDensity_prod {Γz Γw : Measure ℝ} {γz γw : ℝ → ℝ≥0∞} (hz : IsLSCDensity Γz γz)
    (hw : IsLSCDensity Γw γw) :
    IsLSCDensity (Γz.prod Γw) (fun p : ℝ × ℝ => γz p.1 * γw p.2) := by
  refine ⟨lowerSemicontinuous_mul_ennreal (hz.1.comp continuous_fst) (hw.1.comp continuous_snd),
    ?_⟩
  rw [hz.2, hw.2, prod_withDensity hz.1.measurable hw.1.measurable, Measure.volume_eq_prod]

/-- The control set of `(Z, W)` is `O_z × O_w`. -/
theorem controlSet_prod (γz γw : ℝ → ℝ≥0∞) :
    controlSet (fun p : ℝ × ℝ => γz p.1 * γw p.2) = controlSet γz ×ˢ controlSet γw := by
  ext p
  simp [controlSet]

/-- The dependent parameter bilinear step is `C¹`. -/
theorem contDiff_one_dblStep (α : ℝ) : ContDiff ℝ 1 (dblStep α) := by
  unfold dblStep
  fun_prop

/-- `∂F/∂(Z, W)` is the identity for the dependent parameter bilinear model (MT p. 161). -/
theorem dbl_duF (α : ℝ) (x w v : ℝ × ℝ) : duF (dblStep α) x w v = v := by
  have hd : HasFDerivAt (fun w' : ℝ × ℝ => dblStep α (x, w')) (ContinuousLinearMap.id ℝ (ℝ × ℝ))
      w := by
    have : (fun w' : ℝ × ℝ => dblStep α (x, w')) = fun w' => (α * x.1, x.1 * x.2) + w' := by
      funext w'; rfl
    rw [this]
    exact (hasFDerivAt_id w).const_add _
  rw [duF_eq_of_hasFDerivAt ((contDiff_one_dblStep α).differentiable one_ne_zero _) hd]
  rfl

/-- The first order controllability matrix of the dependent parameter bilinear model is the
identity (MT p. 161), so the rank condition holds with `k = 1`. -/
theorem dbl_rankCondition (α : ℝ) {O : Set (ℝ × ℝ)} (hO : O.Nonempty) :
    RankCondition (dblStep α) O := by
  intro x
  obtain ⟨w₀, hw₀⟩ := hO
  refine ⟨1, fun _ => w₀, one_pos, fun _ => hw₀, fun t => ⟨fun _ => t, ?_⟩⟩
  rw [genCtrb_one_apply, dbl_duF]

/-- **Proposition 7.4.1**, first part (MT p. 161): under (DBL1)–(DBL2) the dependent parameter
bilinear model is a T-chain. -/
theorem proposition_7_4_1_tChain {Γz Γw : Measure ℝ} [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] {γz γw : ℝ → ℝ≥0∞} (hz : IsLSCDensity Γz γz)
    (hw : IsLSCDensity Γw γw) (α : ℝ) : IsTChain (dblKernel Γz Γw α) :=
  (proposition_7_1_5 (isLSCDensity_prod hz hw) (contDiff_one_dblStep α)
    (dbl_rankCondition α (controlSet_nonempty (isLSCDensity_prod hz hw)))).2

/-- With constant controls `(z*, w*)`, the dependent parameter bilinear model converges to
`x* = (z*/(1 − α), w*/(1 − θ*))`, `θ* = z*/(1 − α)`, when `|α| < 1` and `|θ*| < 1`
(MT p. 161). -/
theorem dbl_tendsto {α : ℝ} (hα : |α| < 1) {zs ws : ℝ} (hθ : |zs / (1 - α)| < 1) (y : ℝ × ℝ) :
    Tendsto (fun k => controlMap (dblStep α) k y fun _ => (zs, ws)) atTop
      (𝓝 (zs / (1 - α), ws / (1 - zs / (1 - α)))) := by
  set θs := zs / (1 - α)
  set Ys := ws / (1 - θs)
  have h1α : 1 - α ≠ 0 := by
    have := (abs_lt.1 hα).2; intro h; linarith
  have h1θ : 1 - θs ≠ 0 := by
    have := (abs_lt.1 hθ).2; intro h; linarith
  set x : ℕ → ℝ × ℝ := fun k => controlMap (dblStep α) k y fun _ => (zs, ws)
  have hrec : ∀ k, x (k + 1) = dblStep α (x k, (zs, ws)) := fun k => rfl
  have hθrec : ∀ k, (x (k + 1)).1 - θs = α * ((x k).1 - θs) + 0 := fun k => by
    rw [hrec, dblStep_fst]
    have : α * θs + zs = θs := by simp only [θs]; field_simp; ring
    linarith
  have hθt : Tendsto (fun k => (x k).1 - θs) atTop (𝓝 0) :=
    tendsto_zero_of_affine_recursion hα tendsto_const_nhds tendsto_const_nhds hθrec
  have hθt' : Tendsto (fun k => (x k).1) atTop (𝓝 θs) := by
    simpa using hθt.add_const θs
  have hYrec : ∀ k, (x (k + 1)).2 - Ys = (x k).1 * ((x k).2 - Ys) + ((x k).1 - θs) * Ys :=
    fun k => by
      rw [hrec, dblStep_snd]
      have key : ∀ t : ℝ, 1 - t ≠ 0 → t * (ws / (1 - t)) + ws = ws / (1 - t) := fun t ht => by
        field_simp; ring
      have : θs * Ys + ws = Ys := key θs h1θ
      linear_combination this
  have hYt : Tendsto (fun k => (x k).2 - Ys) atTop (𝓝 0) :=
    tendsto_zero_of_affine_recursion hθ hθt' (by simpa using hθt.mul_const Ys) hYrec
  have hYt' : Tendsto (fun k => (x k).2) atTop (𝓝 Ys) := by
    simpa using hYt.add_const Ys
  exact hθt'.prodMk_nhds hYt'

/-- **Proposition 7.4.1** (MT p. 161): under (DBL1)–(DBL2), if some `z* ∈ O_z` has
`|z*/(1 − α)| < 1` (7.24), the dependent parameter bilinear model is a `ψ`-irreducible aperiodic
T-chain. The state `x* = (z*/(1 − α), w*/(1 − θ*))` (`w* ∈ O_w`) is globally attracting and a
fixed point of the control `(z*, w*)`. -/
theorem proposition_7_4_1 {Γz Γw : Measure ℝ} [IsProbabilityMeasure Γz]
    [IsProbabilityMeasure Γw] {γz γw : ℝ → ℝ≥0∞} (hz : IsLSCDensity Γz γz)
    (hw : IsLSCDensity Γw γw) {α : ℝ} (hα : |α| < 1) {zs : ℝ} (hzs : zs ∈ controlSet γz)
    (h724 : |zs / (1 - α)| < 1) :
    have := isMarkovKernel_dblKernel Γz Γw α
    ∃ ψ : Measure (ℝ × ℝ), IsMaximalIrreducibility (dblKernel Γz Γw α) ψ ∧
      IsAperiodic (dblKernel Γz Γw α) ψ ∧ IsTChain (dblKernel Γz Γw α) := by
  have hΓ := isLSCDensity_prod hz hw
  obtain ⟨ws, hws⟩ := controlSet_nonempty hw
  set O := controlSet (fun p : ℝ × ℝ => γz p.1 * γw p.2)
  have hu : (zs, ws) ∈ O := by
    change (zs, ws) ∈ controlSet (fun p : ℝ × ℝ => γz p.1 * γw p.2)
    rw [controlSet_prod]; exact ⟨hzs, hws⟩
  have hF := contDiff_one_dblStep α
  have hrank := dbl_rankCondition α ⟨_, hu⟩
  have hFx : ∀ w ∈ O, Continuous fun x => dblStep α (x, w) := fun w _ =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  set xs : ℝ × ℝ := (zs / (1 - α), ws / (1 - zs / (1 - α)))
  have hga : IsGloballyAttracting (dblStep α) O xs := by
    intro y
    refine mem_iInter₂.2 fun N _ => mem_closure_of_tendsto (dbl_tendsto hα h724 y) ?_
    refine eventually_atTop.2 ⟨N, fun k hk => mem_iUnion₂.2 ⟨k, hk, ?_⟩⟩
    rw [reachKSet_singleton]
    exact ⟨_, fun _ => hu, rfl⟩
  have hirr : IsMIrreducible (dblStep α) O := (proposition_7_2_5_i hFx ⟨_, hu⟩).2 ⟨xs, hga⟩
  obtain ⟨hmin, -, -⟩ := proposition_7_2_5_ii hFx ⟨_, hu⟩ hga
  have h1α : 1 - α ≠ 0 := by
    have := (abs_lt.1 hα).2; intro h; linarith
  have h1θ : 1 - zs / (1 - α) ≠ 0 := by
    have := (abs_lt.1 h724).2; intro h; linarith
  have hfix : dblStep α (xs, (zs, ws)) = xs := by
    refine Prod.ext ?_ ?_
    · change α * (zs / (1 - α)) + zs = zs / (1 - α)
      field_simp; ring
    · change zs / (1 - α) * (ws / (1 - zs / (1 - α))) + ws = ws / (1 - zs / (1 - α))
      have key : ∀ t : ℝ, 1 - t ≠ 0 → t * (ws / (1 - t)) + ws = ws / (1 - t) := fun t ht => by
        field_simp; ring
      exact key _ h1θ
  have hap := isPeriodOf_one_of_fixedPoint hF (isOpen_controlSet hΓ.1) hrank hmin
    (subset_closure (self_mem_reach _ _ xs)) hu hfix
  exact theorem_7_3_5_ii hΓ hF hrank hirr hmin hap

/-! ### Restricting to an absorbing set -/

/-- A continuous component of `K_a` restricts to a continuous component of the restriction of
the chain to an absorbing set `A`, with the same total mass at points of `A`. -/
theorem continuousComponent_restrict {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {P : Kernel X X} [IsMarkovKernel P] {a : ℕ → ℝ≥0∞} {T : Kernel X X}
    (hT : IsContinuousComponent P a T) {A : Set X} (hA : MeasurableSet A)
    (hAbs : IsAbsorbing P A) :
    ∃ TA : Kernel A A, IsContinuousComponent (restrictKernel P hA) a TA ∧
      ∀ x : A, TA x univ = T x univ := by
  set TA : Kernel A A :=
    (T.comap Subtype.val measurable_subtype_coe).comapRight (MeasurableEmbedding.subtype_coe hA)
  have hTA : ∀ x B, MeasurableSet B → TA x B = T x (Subtype.val '' B) := fun x B hB => by
    rw [Kernel.comapRight_apply' _ _ _ hB, Kernel.comap_apply]
  have himg : ∀ B : Set A, MeasurableSet B → MeasurableSet (Subtype.val '' B) := fun B hB =>
    (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
  have hcompl : ∀ x : A, T x Aᶜ = 0 := fun x => by
    have h1 := hT.2.1 x Aᶜ
    rw [sampledKernel_apply P a x hA.compl] at h1
    simp_rw [hAbs.pow_compl hA _ x.2, mul_zero, tsum_zero] at h1
    exact nonpos_iff_eq_zero.1 h1
  refine ⟨TA, ⟨fun x => ?_, fun x => ?_, fun B hB => ?_⟩, fun x => ?_⟩
  · rw [hTA x univ MeasurableSet.univ]
    exact (measure_mono (subset_univ _)).trans (hT.1 x)
  · refine Measure.le_intro fun B hB _ => ?_
    rw [hTA x B hB, sampledKernel_apply _ a x hB]
    simp_rw [restrictKernel_pow_apply P hA hAbs _ x hB]
    rw [← sampledKernel_apply P a x (himg B hB)]
    exact hT.2.1 x _
  · have : (fun x : A => TA x B) = (fun y => T y (Subtype.val '' B)) ∘ Subtype.val :=
      funext fun x => hTA x B hB
    rw [this]
    exact (hT.2.2 _ (himg B hB)).comp continuous_subtype_val
  · rw [hTA x univ MeasurableSet.univ, image_univ, Subtype.range_coe]
    refine le_antisymm (measure_mono (subset_univ _)) ?_
    calc T x univ ≤ T x A + T x Aᶜ := measure_univ_le_add_compl A
      _ = T x A := by rw [hcompl x, add_zero]

/-- If every point of an absorbing set `A` has a continuous component non-trivial at it, the
restriction of the chain to `A` is a T-chain (Proposition 6.2.4 on `A`). -/
theorem isTChain_restrictKernel_of_local {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [SecondCountableTopology X] {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A)
    (h : ∀ x ∈ A, ∃ a T, IsSamplingDist a ∧ IsContinuousComponent P a T ∧ 0 < T x univ) :
    IsTChain (restrictKernel P hA) := by
  refine proposition_6_2_4 fun x => ?_
  obtain ⟨a, T, ha, hT, hpos⟩ := h x x.2
  obtain ⟨TA, hTA, hmass⟩ := continuousComponent_restrict hT hA hAbs
  exact ⟨a, TA, ha, hTA, by rw [hmass]; exact hpos⟩

/-- A disturbance law with a density charges no point. -/
theorem IsLSCDensity.nullSingletonClass {W : Type*} [NormedAddCommGroup W] [MeasureSpace W]
    {Γ : Measure W}
    {γ : W → ℝ≥0∞} (hΓ : IsLSCDensity Γ γ) [NullSingletonClass (volume : Measure W)] :
    NullSingletonClass Γ :=
  ⟨fun w => by rw [hΓ.2]; exact withDensity_absolutelyContinuous _ _ (measure_singleton w)⟩

/-! ### The gumleaf attractor (§7.4.2) -/

/-- The open set `{x : xᵃ ≠ 0, xᵇ ≠ 0}` on which the noisy gumleaf step is smooth. -/
def gumleafDomain : Set (ℝ × ℝ) := {x | x.1 ≠ 0 ∧ x.2 ≠ 0}

/-- The gumleaf domain is open. -/
theorem isOpen_gumleafDomain : IsOpen gumleafDomain :=
  (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)

/-- The noisy gumleaf step is `C¹` near every point whose state lies in the gumleaf domain. -/
theorem gumleaf_contDiffAt {x : ℝ × ℝ} (hx : x ∈ gumleafDomain) (w : ℝ) :
    ContDiffAt ℝ 1 gumleafNoisyStep (x, w) := by
  have h1 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × ℝ => 1 / p.1.1) (x, w) := by
    simp only [one_div]
    exact (contDiffAt_inv ℝ hx.1).comp (x, w) (contDiff_fst.comp contDiff_fst).contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × ℝ => 1 / p.1.2) (x, w) := by
    simp only [one_div]
    exact (contDiffAt_inv ℝ hx.2).comp (x, w) (contDiff_snd.comp contDiff_fst).contDiffAt
  exact ((h1.sub h2).add contDiffAt_snd).prodMk (contDiff_fst.comp contDiff_fst).contDiffAt

/-- `∂F/∂u = (1, 0)` for the noisy gumleaf step. -/
theorem gumleaf_duF {x : ℝ × ℝ} (hx : x ∈ gumleafDomain) (w c : ℝ) :
    duF gumleafNoisyStep x w c = (c, 0) := by
  have hd : HasFDerivAt (fun w' => gumleafNoisyStep (x, w')) (ContinuousLinearMap.inl ℝ ℝ ℝ) w := by
    have : (fun w' => gumleafNoisyStep (x, w')) =
        fun w' => ((1 / x.1 - 1 / x.2, x.1) + ContinuousLinearMap.inl ℝ ℝ ℝ w') := by
      funext w'
      simp only [gumleafNoisyStep, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero]
    rw [this]
    exact (ContinuousLinearMap.inl ℝ ℝ ℝ).hasFDerivAt.const_add _
  rw [duF_eq_of_hasFDerivAt ((gumleaf_contDiffAt hx w).differentiableAt one_ne_zero) hd]
  rfl

/-- `∂F/∂x (a', 0) = (−a'/(xᵃ)², a')` for the noisy gumleaf step. -/
theorem gumleaf_dxF_fst {x : ℝ × ℝ} (hx : x ∈ gumleafDomain) (w a : ℝ) :
    dxF gumleafNoisyStep x w (a, 0) = (-(a / x.1 ^ 2), a) := by
  set L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((-(x.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ - (-(x.2 ^ 2)⁻¹) •
      ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hd : HasFDerivAt (fun x' => gumleafNoisyStep (x', w)) L x := by
    have h1 : HasFDerivAt (fun x' : ℝ × ℝ => x'.1⁻¹)
        ((-(x.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
      have := (hasDerivAt_inv hx.1).hasFDerivAt.comp x (hasFDerivAt_fst (p := x))
      refine this.congr_fderiv ?_
      ext <;> simp
    have h2 : HasFDerivAt (fun x' : ℝ × ℝ => x'.2⁻¹)
        ((-(x.2 ^ 2)⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
      have := (hasDerivAt_inv hx.2).hasFDerivAt.comp x (hasFDerivAt_snd (p := x))
      refine this.congr_fderiv ?_
      ext <;> simp
    have h3 := ((h1.sub h2).add_const w).prodMk (hasFDerivAt_fst (p := x))
    have : (fun x' => gumleafNoisyStep (x', w)) =
        fun x' : ℝ × ℝ => (x'.1⁻¹ - x'.2⁻¹ + w, x'.1) := by
      funext x'; simp [gumleafNoisyStep, one_div]
    rw [this]
    exact h3
  rw [dxF_eq_of_hasFDerivAt ((gumleaf_contDiffAt hx w).differentiableAt one_ne_zero) hd]
  simp [L, div_eq_mul_inv, mul_comm]

/-- The chain rule step for the control maps at a point where `F` is differentiable (a local
form of `hasFDerivAt_controlMap`). -/
theorem hasFDerivAt_controlMap_succ_of {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : X × W → X} {k : ℕ} {x : X}
    {u : Fin (k + 1) → W}
    (hk : HasFDerivAt (controlMap F k x) (genCtrb F k x (Fin.init u)) (Fin.init u))
    (hF : DifferentiableAt ℝ F (controlMap F k x (Fin.init u), u (Fin.last k))) :
    HasFDerivAt (controlMap F (k + 1) x) (genCtrb F (k + 1) x u) u := by
  have h1 : HasFDerivAt (fun v : Fin (k + 1) → W => controlMap F k x (initCLM k v))
      ((genCtrb F k x (Fin.init u)).comp (initCLM k)) u :=
    hk.comp u (initCLM (W := W) k).hasFDerivAt
  have h2 : HasFDerivAt (fun v : Fin (k + 1) → W => v (Fin.last k))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) (Fin.last k)) u :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) (Fin.last k)).hasFDerivAt
  have h3 := hF.hasFDerivAt.comp u (h1.prodMk h2)
  refine h3.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rw [fderiv_apply_eq_dxF_add_duF]
  rfl

/-- An open non-empty subset of `ℝ` contains a point different from any given `c`. -/
theorem exists_mem_ne_of_isOpen {O : Set ℝ} (hO : IsOpen O) (hne : O.Nonempty) (c : ℝ) :
    ∃ u ∈ O, u ≠ c := by
  obtain ⟨w, hw⟩ := hne
  by_cases hwc : w = c
  · subst hwc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO w hw
    refine ⟨w + ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
    linarith
  · exact ⟨w, hw, hwc⟩

/-- The second order controllability matrix of the gumleaf model (MT p. 162), in the sign
convention of `gumleafNoisyStep`: `C²(v) = (−v₁/(x₁ᵃ)² + v₂, v₁)` with `x₁ = F(x₀, u₁)`, of full
rank wherever the step is smooth. -/
theorem gumleaf_genCtrb_two {x : ℝ × ℝ} (hx : x ∈ gumleafDomain) {u : Fin 2 → ℝ}
    (hx1 : gumleafNoisyStep (x, u 0) ∈ gumleafDomain) (v : Fin 2 → ℝ) :
    genCtrb gumleafNoisyStep 2 x u v =
      (-(v 0 / (gumleafNoisyStep (x, u 0)).1 ^ 2) + v 1, v 0) := by
  rw [genCtrb_succ_apply, genCtrb_one_apply]
  change dxF gumleafNoisyStep (gumleafNoisyStep (x, u 0)) (u 1)
      (duF gumleafNoisyStep x (u 0) (v 0)) + duF gumleafNoisyStep (gumleafNoisyStep (x, u 0))
        (u 1) (v 1) = _
  rw [gumleaf_duF hx, gumleaf_dxF_fst hx1, gumleaf_duF hx1]
  simp

/-- **Proposition 7.4.2** (MT p. 162), in the form proved here: under (NSS3), the noisy gumleaf
model (2.12) keeps the open set `{xᵃ ≠ 0, xᵇ ≠ 0}` (where the step is smooth) with probability
one, every point of it has a continuous component of `P²` non-trivial at it, and the model
restricted to this set is a T-chain. (The book cites Proposition 7.2.6 for this; it is
Proposition 7.1.5. On all of `ℝ²`, with Lean's `1/0 = 0`, the step is not continuous.) -/
theorem proposition_7_4_2 {Γ : Measure ℝ} [IsProbabilityMeasure Γ] {γ : ℝ → ℝ≥0∞}
    (hΓ : IsLSCDensity Γ γ) :
    have := isMarkovKernel_gumleafKernel Γ
    IsAbsorbing (gumleafKernel Γ) gumleafDomain ∧
      (∀ x ∈ gumleafDomain, ∃ T : Kernel (ℝ × ℝ) (ℝ × ℝ),
        IsContinuousComponent (gumleafKernel Γ) (diracDist 2) T ∧ 0 < T x univ) ∧
      IsTChain (restrictKernel (gumleafKernel Γ) isOpen_gumleafDomain.measurableSet) := by
  have hM := isMarkovKernel_gumleafKernel Γ
  have hns := hΓ.nullSingletonClass
  have hD := isOpen_gumleafDomain
  have hAbs : IsAbsorbing (gumleafKernel Γ) gumleafDomain := by
    intro x hx
    rw [gumleafKernel, recursionKernel_apply' Γ measurable_gumleafNoisyStep x hD.measurableSet]
    have : {w : ℝ | gumleafNoisyStep (x, w) ∈ gumleafDomain} = {1 / x.2 - 1 / x.1}ᶜ := by
      ext w
      simp only [gumleafNoisyStep, gumleafDomain, mem_ofPred_eq, mem_compl_iff,
        mem_singleton_iff]
      constructor
      · rintro ⟨h1, -⟩ h2; apply h1; rw [h2]; ring
      · intro h; refine ⟨fun h1 => h ?_, hx.1⟩; linarith
    rw [this, measure_compl (measurableSet_singleton _) (measure_ne_top _ _), measure_singleton,
      measure_univ, tsub_zero]
  have hcomp : ∀ x ∈ gumleafDomain, ∃ T : Kernel (ℝ × ℝ) (ℝ × ℝ),
      IsContinuousComponent (gumleafKernel Γ) (diracDist 2) T ∧ 0 < T x univ := by
    intro x hx
    have hO := isOpen_controlSet hΓ.1
    obtain ⟨u0, hu0, hu0c⟩ := exists_mem_ne_of_isOpen hO (controlSet_nonempty hΓ)
      (1 / x.2 - 1 / x.1)
    obtain ⟨u1, hu1⟩ := controlSet_nonempty hΓ
    set u : Fin 2 → ℝ := ![u0, u1]
    have hx1 : gumleafNoisyStep (x, u 0) ∈ gumleafDomain := by
      refine ⟨fun h => hu0c ?_, hx.1⟩
      change 1 / x.1 - 1 / x.2 + u0 = 0 at h
      linarith
    set G := fun p : (ℝ × ℝ) × (Fin 2 → ℝ) => controlMap gumleafNoisyStep 2 p.1 p.2
    have hGeq : G = fun p => gumleafNoisyStep (gumleafNoisyStep (p.1, p.2 0), p.2 1) := rfl
    have hp0 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × (Fin 2 → ℝ) => p.2 0) (x, u) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff.comp
        contDiff_snd).contDiffAt
    have hp1 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × (Fin 2 → ℝ) => p.2 1) (x, u) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff.comp
        contDiff_snd).contDiffAt
    have hin1 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ) × (Fin 2 → ℝ) =>
        gumleafNoisyStep (p.1, p.2 0)) (x, u) :=
      ContDiffAt.comp (g := gumleafNoisyStep) (x, u) (gumleaf_contDiffAt hx (u 0))
        (contDiffAt_fst.prodMk hp0)
    have hG : ContDiffAt ℝ 1 G (x, u) := by
      rw [hGeq]
      exact ContDiffAt.comp (g := gumleafNoisyStep) (x, u) (gumleaf_contDiffAt hx1 (u 1))
        (hin1.prodMk hp1)
    have hderiv : HasFDerivAt (controlMap gumleafNoisyStep 2 x)
        (genCtrb gumleafNoisyStep 2 x u) u := by
      have h0 : HasFDerivAt (controlMap gumleafNoisyStep 0 x)
          (genCtrb gumleafNoisyStep 0 x (Fin.init (Fin.init u))) (Fin.init (Fin.init u)) :=
        hasFDerivAt_const x _
      have h1 := hasFDerivAt_controlMap_succ_of h0
        ((gumleaf_contDiffAt hx (u 0)).differentiableAt one_ne_zero)
      exact hasFDerivAt_controlMap_succ_of h1
        ((gumleaf_contDiffAt hx1 (u 1)).differentiableAt one_ne_zero)
    have hpart : (fderiv ℝ G (x, u)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (Fin 2 → ℝ)) =
        genCtrb gumleafNoisyStep 2 x u :=
      ((hG.differentiableAt one_ne_zero).hasFDerivAt.comp u
        (hasFDerivAt_prodMk_right x u)).unique hderiv
    have hsurj : Function.Surjective
        ((fderiv ℝ G (x, u)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (Fin 2 → ℝ))) := by
      rw [hpart]
      rintro ⟨s, t⟩
      refine ⟨![t, s + t / (gumleafNoisyStep (x, u 0)).1 ^ 2], ?_⟩
      rw [gumleaf_genCtrb_two hx hx1]
      simp
    have hu : ∀ i, u i ∈ controlSet γ := by
      intro i
      fin_cases i
      · exact hu0
      · exact hu1
    exact (exists_continuousComponent hΓ measurable_gumleafNoisyStep hu hG hsurj).1
  refine ⟨hAbs, hcomp, isTChain_restrictKernel_of_local hD.measurableSet hAbs fun x hx => ?_⟩
  obtain ⟨T, hT, hpos⟩ := hcomp x hx
  exact ⟨diracDist 2, T, isSamplingDist_diracDist 2, hT, hpos⟩

/-! ### The adaptive control model (§7.4.3) -/

/-- **The deterministic limit of the adaptive control model** (MT p. 163): with zero disturbances
`Z = W = 0`, from every state with `Σ₀ ∈ [σ_z², σ_z²/(1 − α²)]`,
`Φₖ → (σ_z²/(1 − α²), 0, 0)` (for `|α| < 1`, `σ_w ≠ 0`; the book's `σ_z² < 1` is not needed). -/
theorem sac_tendsto {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) {x₀ : ℝ × ℝ × ℝ}
    (hx₀ : x₀.1 ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))) :
    Tendsto (fun k => controlMap (sacStep α σz σw) k x₀ fun _ => (0, 0)) atTop
      (𝓝 (σz ^ 2 / (1 - α ^ 2), 0, 0)) := by
  set x : ℕ → ℝ × ℝ × ℝ := fun k => controlMap (sacStep α σz σw) k x₀ fun _ => (0, 0)
  have hrec : ∀ k, x (k + 1) = sacStep α σz σw (x k, (0, 0)) := fun k => rfl
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have hI : ∀ k, (x k).1 ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2)) := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih =>
      rw [hrec]
      have hxk : x k = ((x k).1, (x k).2.1, (x k).2.2) := rfl
      rw [hxk]
      exact sacStep_sigma_mem hα hσw ih (0, 0)
  have hS0 : ∀ k, 0 ≤ (x k).1 := fun k => le_trans (sq_nonneg σz) (hI k).1
  have hσ2 : 0 < σw ^ 2 := by positivity
  set D : ℕ → ℝ := fun k => (x k).1 * (x k).2.2 ^ 2 + σw ^ 2
  have hD : ∀ k, 0 < D k := fun k => by
    have := mul_nonneg (hS0 k) (sq_nonneg (x k).2.2); simp only [D]; linarith
  -- the components of the recursion
  have hSig : ∀ k, (x (k + 1)).1 = σz ^ 2 + α ^ 2 * (x k).1 * (σw ^ 2 / D k) := fun k => by
    rw [hrec]; simp only [sacStep, D]; ring
  have hθ : ∀ k, (x (k + 1)).2.1 = α * (σw ^ 2 / D k) * (x k).2.1 := fun k => by
    have hDk : (x k).1 * (x k).2.2 ^ 2 + σw ^ 2 ≠ 0 := (hD k).ne'
    rw [hrec]
    simp only [sacStep, D, add_zero]
    field_simp
    ring
  have hY : ∀ k, (x (k + 1)).2.2 = (x k).2.1 * (x k).2.2 + 0 := fun k => by
    rw [hrec]; simp [sacStep]
  have hs1 : ∀ k, σw ^ 2 / D k ≤ 1 := fun k => by
    rw [div_le_one (hD k)]
    have := mul_nonneg (hS0 k) (sq_nonneg (x k).2.2); simp only [D]; linarith
  have hs0 : ∀ k, 0 ≤ σw ^ 2 / D k := fun k => (div_pos hσ2 (hD k)).le
  -- `θ̃ₖ → 0` geometrically
  have hθb : ∀ k, |(x k).2.1| ≤ |α| ^ k * |(x 0).2.1| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hθ, abs_mul, abs_mul, abs_of_nonneg (hs0 k), pow_succ]
      calc |α| * (σw ^ 2 / D k) * |(x k).2.1| ≤ |α| * 1 * |(x k).2.1| := by
            gcongr; exact hs1 k
        _ ≤ |α| * (|α| ^ k * |(x 0).2.1|) := by rw [mul_one]; gcongr
        _ = |α| ^ k * |α| * |(x 0).2.1| := by ring
  have hθt : Tendsto (fun k => (x k).2.1) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => (hθb k)) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg α) hα).mul_const
      |(x 0).2.1|
  -- `Yₖ → 0`
  have hYt : Tendsto (fun k => (x k).2.2) atTop (𝓝 0) :=
    tendsto_zero_of_affine_recursion (by simp) hθt tendsto_const_nhds hY
  -- `Σₖ → σ_z²/(1 − α²)`
  set Ss := σz ^ 2 / (1 - α ^ 2)
  have hSs : σz ^ 2 + α ^ 2 * Ss = Ss := by
    simp only [Ss]; field_simp [(by linarith : (1 : ℝ) - α ^ 2 ≠ 0)]; ring
  have hDt : Tendsto D atTop (𝓝 (σw ^ 2)) := by
    have hb : ∀ k, |(x k).1 * (x k).2.2 ^ 2| ≤ Ss * (x k).2.2 ^ 2 := fun k => by
      rw [abs_mul, abs_of_nonneg (hS0 k), abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hI k).2 (sq_nonneg _)
    have h0 : Tendsto (fun k => (x k).1 * (x k).2.2 ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => hb k) ?_
      simpa using (hYt.pow 2).const_mul Ss
    simpa [D] using h0.add_const (σw ^ 2)
  have hst : Tendsto (fun k => σw ^ 2 / D k) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := σw ^ 2)).div hDt hσ2.ne'
    rwa [div_self hσ2.ne'] at this
  have hSrec : ∀ k, (x (k + 1)).1 - Ss =
      (α ^ 2 * (σw ^ 2 / D k)) * ((x k).1 - Ss) + α ^ 2 * Ss * (σw ^ 2 / D k - 1) := fun k => by
    rw [hSig]; linear_combination hSs
  have hSt : Tendsto (fun k => (x k).1 - Ss) atTop (𝓝 0) := by
    refine tendsto_zero_of_affine_recursion (a := α ^ 2) (by rwa [abs_of_nonneg (sq_nonneg α)])
      (by simpa using hst.const_mul (α ^ 2)) ?_ hSrec
    simpa using (hst.sub_const 1).const_mul (α ^ 2 * Ss)
  have hSt' : Tendsto (fun k => (x k).1) atTop (𝓝 Ss) := by simpa using hSt.add_const Ss
  exact hSt'.prodMk_nhds (hθt.prodMk_nhds hYt)

/-- **Correction** (MT p. 162): the interior `(σ_z², σ_z²/(1 − α²)) × ℝ²` of the state space is not
reached in one step from every initial condition: from `(σ_z²/(1 − α²), θ̃, 0)` the next value of
`Σ` is `σ_z²/(1 − α²)` again, whatever the disturbance (`|α| < 1`, `σ_w ≠ 0`). -/
theorem sac_upper_boundary {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) (θ : ℝ)
    (z : ℝ × ℝ) :
    (sacStep α σz σw ((σz ^ 2 / (1 - α ^ 2), θ, 0), z)).1 = σz ^ 2 / (1 - α ^ 2) := by
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have h1 : (1 : ℝ) - α ^ 2 ≠ 0 := by linarith
  simp only [sacStep]
  field_simp
  ring

/-- **Correction** (MT p. 162), kernel form: from `(σ_z²/(1 − α²), θ̃, 0)` the adaptive control
model enters the interior of the state space with probability zero in one step. -/
theorem sacKernel_interior_eq_zero (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) (θ : ℝ) :
    sacKernel Γ α σz σw (σz ^ 2 / (1 - α ^ 2), θ, 0)
      {p | p.1 ∈ Ioo (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Ioo (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))} :=
    measurable_fst measurableSet_Ioo
  rw [sacKernel, recursionKernel_apply' Γ (measurable_sacStep α σz σw) _ hm]
  have : {w : ℝ × ℝ | sacStep α σz σw ((σz ^ 2 / (1 - α ^ 2), θ, 0), w) ∈
      {p : ℝ × ℝ × ℝ | p.1 ∈ Ioo (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))}} = ∅ := by
    ext w
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rw [sac_upper_boundary hα hσw θ w]
    exact fun h => lt_irrefl _ h.2
  rw [this, measure_empty]

/-- For `α = 0` the interval `[σ_z², σ_z²/(1 − α²)]` of the adaptive control model is a single
point, so its interior is empty and the book's restriction to the interior is vacuous. -/
theorem sac_interior_empty_of_alpha_zero (σz : ℝ) :
    Ioo (σz ^ 2) (σz ^ 2 / (1 - (0 : ℝ) ^ 2)) = ∅ := by
  simp

/-! ### The linear model as a special case -/

open scoped Matrix in
/-- **The linear model** (MT p. 153): for `F(x, u) = A x + B u` and a non-empty control set, the
rank condition (CM3) is controllability of `(A, B)` (LCM3). -/
theorem linear_rankCondition_iff {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) {O : Set (Fin p → ℝ)} (hO : O.Nonempty) :
    RankCondition (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) O ↔
      IsControllable A B := by
  rw [isControllable_iff_exists_rank]
  constructor
  · intro h
    obtain ⟨k, u, -, -, hs⟩ := h 0
    refine ⟨k, (rank_ctrbMatrix_eq_iff A B k).2 (LinearMap.range_eq_top.2 fun y => ?_)⟩
    obtain ⟨v, hv⟩ := hs y
    exact ⟨v, by rw [← genCtrb_linear A B k 0 u v]; exact hv⟩
  · rintro ⟨k, hk⟩ x
    obtain ⟨w₀, hw₀⟩ := hO
    have htop : LinearMap.range (ctrbMap A B (n + 1)) = ⊤ := by
      rw [rank_ctrbMatrix_eq_iff] at hk
      refine eq_top_iff.2 fun y _ => range_ctrbMap_mono A B (Nat.le_succ n) ?_
      have hn : LinearMap.range (ctrbMap A B n) = ⊤ :=
        eq_top_iff.2 (hk.symm.le.trans (range_ctrbMap_le_n A B k))
      rw [hn]; trivial
    refine ⟨n + 1, fun _ => w₀, Nat.succ_pos n, fun _ => hw₀, fun y => ?_⟩
    obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop y
    exact ⟨v, by rw [genCtrb_linear]; exact hv⟩

open scoped Matrix in
/-- **The minimal set of the linear control model** (MT p. 155): with `O = ℝᵖ`, the range `X₀` of
the controllability matrix `C_n` is a minimal set of LCM(F, G). -/
theorem lcm_isMinimal_ctrbSubspace {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) :
    IsMinimal (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) univ
      (LinearMap.range (ctrbMap A B n) : Set (Fin n → ℝ)) := by
  set F := fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2
  set X₀ : Set (Fin n → ℝ) := ↑(LinearMap.range (ctrbMap A B n))
  have hFx : ∀ w ∈ (univ : Set (Fin p → ℝ)), Continuous fun x => F (x, w) := fun w _ =>
    (Continuous.matrix_mulVec continuous_const continuous_id).add
      (continuous_const : Continuous fun _ : Fin n → ℝ => B *ᵥ w)
  have hinv : IsCMInvariant F univ X₀ := isCMInvariant_iff_step.2 fun x hx w _ =>
    ctrbSubspace_absorbing_step A B hx w
  have hcl : IsClosed X₀ := Submodule.closed_of_finiteDimensional _
  refine ((proposition_7_2_3 hFx ⟨0, trivial⟩ ⟨0, Submodule.zero_mem _⟩).1).2 fun x hx => ?_
  refine Subset.antisymm (hinv.closure_reach_subset hcl hx) fun y hy => subset_closure ?_
  have hAx : (A ^ n) *ᵥ x ∈ X₀ := by
    have := hinv.reachK_subset hx n ⟨fun _ => 0, fun _ => trivial, rfl⟩
    rwa [show controlMap F n x (fun _ => 0) = lcmTrajectory A B n x (fun _ => 0) from rfl,
      lcmTrajectory_eq_ctrbMap, show (fun _ : Fin n => (0 : Fin p → ℝ)) = 0 from rfl, map_zero,
      add_zero] at this
  obtain ⟨u, hu⟩ := Submodule.sub_mem _ hy hAx
  refine mem_reach_iff.2 ⟨n, u, fun _ => trivial, ?_⟩
  change lcmTrajectory A B n x u = y
  rw [lcmTrajectory_eq_ctrbMap, hu, add_sub_cancel]

open scoped Matrix in
/-- **Uniqueness of the minimal set under (LSS5)** (MT p. 155): if `A` satisfies the eigenvalue
condition, `X₀` is the only minimal set of LCM(F, G) with `O = ℝᵖ`. -/
theorem lcm_minimal_unique {n p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (B : Matrix (Fin n) (Fin p) ℝ) (hA : IsStableMatrix A) {M : Set (Fin n → ℝ)}
    (hM : IsMinimal (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) univ M) :
    M = (LinearMap.range (ctrbMap A B n) : Set (Fin n → ℝ)) := by
  set F := fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2
  have hFx : ∀ w ∈ (univ : Set (Fin p → ℝ)), Continuous fun x => F (x, w) := fun w _ =>
    (Continuous.matrix_mulVec continuous_const continuous_id).add
      (continuous_const : Continuous fun _ : Fin n → ℝ => B *ᵥ w)
  have hX := lcm_isMinimal_ctrbSubspace A B
  obtain ⟨y, hy⟩ := hM.1
  have hcl := ((proposition_7_2_3 hFx ⟨0, trivial⟩ hM.1).1.1 hM) y hy
  obtain ⟨C, r, hC, hr0, hr1, hbd⟩ := isStableMatrix_geometric hA
  have hsub : (LinearMap.range (ctrbMap A B n) : Set (Fin n → ℝ)) ⊆ M := by
    intro z hz
    rw [← hcl]
    have hz' : ∀ k, n ≤ k → ∃ u, ctrbMap A B k u = z := fun k hk =>
      range_ctrbMap_mono A B hk hz
    choose! u hu using hz'
    have ht : Tendsto (fun k => (A ^ k) *ᵥ y + z) atTop (𝓝 z) := by
      have h0 : Tendsto (fun k => (A ^ k) *ᵥ y) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun k => hbd k y) ?_
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul C).mul_const
          ‖y‖
      simpa using h0.add_const z
    refine mem_closure_of_tendsto ht (eventually_atTop.2 ⟨n, fun k hk => ?_⟩)
    refine mem_reach_iff.2 ⟨k, u k, fun _ => trivial, ?_⟩
    change lcmTrajectory A B k y (u k) = _
    rw [lcmTrajectory_eq_ctrbMap, hu k hk]
  exact (hM.2.2.2 _ hsub hX.1 hX.2.1 hX.2.2.1).symm

open scoped Matrix in
/-- Without (LSS5) the minimal set need not be unique (MT p. 155): for `xₖ₊₁ = xₖ` every point
is a minimal set. -/
theorem lcm_minimal_not_unique (v : Fin 1 → ℝ) :
    IsMinimal (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ q.1 +
      (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ q.2) univ {v} := by
  refine ⟨singleton_nonempty v, isClosed_singleton, ?_, fun C hC hne _ _ => ?_⟩
  · rw [isCMInvariant_iff_step]
    intro x hx w _
    rw [mem_singleton_iff] at hx ⊢
    simp [hx]
  · obtain ⟨c, hc⟩ := hne
    exact Subset.antisymm hC (singleton_subset_iff.2 (by rwa [mem_singleton_iff.1 (hC hc)] at hc))

end MeynTweedie.InvarianceTightness
