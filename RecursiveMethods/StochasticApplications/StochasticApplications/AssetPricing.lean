/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.BetaPosterior

/-!
# Asset prices: the pricing equation

SLP §10.6, Exercise 10.6e, pp. 303–304. On a compact state space `Z` with a Feller transition `Q`,
the Markov operator `M` maps `C(Z)` into itself (`fellerOp`), linearly and monotonically. For
`h ∈ C(Z)` and `0 < β < 1` the equation `φ = h + βMφ` (6) has a unique solution in `C(Z)`; it
is `φ = Σₙ βⁿ Mⁿ h`, and it is positive when `h` is (`ex_10_6e_general`).

For the exchange economy (`ex_10_6e`), `Z ⊆ ℝᵏ₊₊`, `U′` is continuous and positive, and
`hᵢ(z) = β ∫ U′(z′·1) z′ᵢ Q(z, dz′)`. Each `φᵢ` is positive, and `p*ᵢ = φᵢ/U′(z·1)` solves the
equilibrium condition `U′(z·1) p*ᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + p*ᵢ(z′)] Q(z, dz′)` (5).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction

variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  (Q : Kernel Z Z) [IsMarkovKernel Q]

omit [OpensMeasurableSpace Z] in
theorem abs_markovOpR_le (f : Z →ᵇ ℝ) (z : Z) : |markovOpR Q f z| ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := Q z) (C := ‖f‖) (f := fun z' => f z')
    (Eventually.of_forall fun z' => f.norm_coe_le_norm z')
  simpa [markovOpR, measureReal_def, Real.norm_eq_abs] using this

theorem integrable_bcf (f : Z →ᵇ ℝ) (z : Z) : Integrable (fun z' => f z') (Q z) :=
  integrable_of_abs_le f.continuous.measurable fun z' => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z'

/-- The Markov operator on `C(Z)`, for `Q` Feller: `(Mf)(z) = ∫ f(z′) Q(z, dz′)`. -/
noncomputable def fellerOp (hQ : IsFeller Q) (f : Z →ᵇ ℝ) : Z →ᵇ ℝ :=
  ofNormedAddCommGroup (markovOpR Q f) (hQ f f.continuous ⟨‖f‖, fun z => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z⟩) ‖f‖ fun z => by
    rw [Real.norm_eq_abs]; exact abs_markovOpR_le Q f z

variable {Q} (hQ : IsFeller Q)

omit [OpensMeasurableSpace Z] in
theorem fellerOp_apply (f : Z →ᵇ ℝ) (z : Z) : fellerOp Q hQ f z = ∫ z', f z' ∂Q z := rfl

theorem fellerOp_add (f g : Z →ᵇ ℝ) :
    fellerOp Q hQ (f + g) = fellerOp Q hQ f + fellerOp Q hQ g := by
  ext z
  simp only [fellerOp_apply, coe_add, Pi.add_apply]
  exact integral_add (integrable_bcf Q f z) (integrable_bcf Q g z)

omit [OpensMeasurableSpace Z] in
theorem fellerOp_smul (c : ℝ) (f : Z →ᵇ ℝ) : fellerOp Q hQ (c • f) = c • fellerOp Q hQ f := by
  ext z
  simp only [fellerOp_apply, coe_smul, smul_eq_mul]
  exact integral_const_mul c _

omit [OpensMeasurableSpace Z] in
theorem fellerOp_const (a : ℝ) : fellerOp Q hQ (const Z a) = const Z a := by
  ext z
  simp [fellerOp_apply]

theorem fellerOp_mono {f g : Z →ᵇ ℝ} (hfg : f ≤ g) : fellerOp Q hQ f ≤ fellerOp Q hQ g :=
  fun z => integral_mono (integrable_bcf Q f z) (integrable_bcf Q g z) fun z' => hfg z'

omit [OpensMeasurableSpace Z] in
theorem norm_fellerOp_le (f : Z →ᵇ ℝ) : ‖fellerOp Q hQ f‖ ≤ ‖f‖ :=
  (norm_le (norm_nonneg f)).2 fun z => by
    rw [Real.norm_eq_abs]; exact abs_markovOpR_le Q f z

omit [OpensMeasurableSpace Z] in
theorem norm_fellerOp_iterate_le (n : ℕ) (f : Z →ᵇ ℝ) : ‖(fellerOp Q hQ)^[n] f‖ ≤ ‖f‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (norm_fellerOp_le hQ _).trans ih

/-- The operator of (6): `Tφ = h + βMφ`. -/
noncomputable def priceT (β : ℝ) (h φ : Z →ᵇ ℝ) : Z →ᵇ ℝ := h + β • fellerOp Q hQ φ

theorem priceT_contraction {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (h : Z →ᵇ ℝ) :
    IsContraction (priceT hQ β h) β := by
  refine ⟨hβ0, hβ1, blackwell hβ0.le (fun f g hfg z => ?_) (fun f a _ z => ?_)⟩
  · change h z + β * fellerOp Q hQ f z ≤ h z + β * fellerOp Q hQ g z
    have h1 : fellerOp Q hQ f z ≤ fellerOp Q hQ g z := fellerOp_mono hQ hfg z
    nlinarith [mul_le_mul_of_nonneg_left h1 hβ0.le]
  · change h z + β * fellerOp Q hQ (f + const Z a) z ≤ h z + β * fellerOp Q hQ f z + β * a
    rw [fellerOp_add, fellerOp_const]
    change h z + β * (fellerOp Q hQ f z + a) ≤ _
    linarith

/-- The partial sums `Σ_{m<n} βᵐMᵐh` are the iterates `Tⁿ0`. -/
theorem priceT_iterate_zero (β : ℝ) (h : Z →ᵇ ℝ) (n : ℕ) :
    (priceT hQ β h)^[n] 0 = ∑ m ∈ Finset.range n, β ^ m • (fellerOp Q hQ)^[m] h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, priceT, Finset.sum_range_succ']
    have hlin : ∀ s : Finset ℕ, fellerOp Q hQ (∑ m ∈ s, β ^ m • (fellerOp Q hQ)^[m] h) =
        ∑ m ∈ s, β ^ m • (fellerOp Q hQ)^[m + 1] h := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have := fellerOp_smul hQ 0 0
        simpa using this
      | insert a s ha ih' =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, fellerOp_add, fellerOp_smul, ih',
          Function.iterate_succ_apply']
    rw [hlin, Finset.smul_sum]
    simp only [smul_smul, pow_zero, one_smul, Function.iterate_zero, id, ← pow_succ']
    abel

/-- **Exercise 10.6e** (general form). For `h ∈ C(Z)` and `0 < β < 1`, `φ = h + βMφ` has a unique
solution `φ ∈ C(Z)`; `φ = Σₙ βⁿMⁿh`; and `φ > 0` if `h > 0`. -/
theorem ex_10_6e_general {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (h : Z →ᵇ ℝ) :
    ∃ φ : Z →ᵇ ℝ, φ = h + β • fellerOp Q hQ φ ∧
      (∀ ψ : Z →ᵇ ℝ, ψ = h + β • fellerOp Q hQ ψ → ψ = φ) ∧
      HasSum (fun n => β ^ n • (fellerOp Q hQ)^[n] h) φ ∧
      ((∀ z, 0 < h z) → ∀ z, 0 < φ z) := by
  have hT := priceT_contraction hQ hβ0 hβ1 h
  obtain ⟨φ, hφ, huniq, hrate⟩ := theorem_3_2 hT
  refine ⟨φ, hφ.symm, fun ψ hψ => huniq ψ hψ.symm, ?_, fun hpos z => ?_⟩
  · -- the series converges absolutely, and its partial sums are `Tⁿ0 → φ`
    have hsum : Summable fun n => β ^ n • (fellerOp Q hQ)^[n] h := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right ‖h‖)
        fun n => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hβ0 n)]
      exact mul_le_mul_of_nonneg_left (norm_fellerOp_iterate_le hQ n h) (pow_nonneg hβ0.le n)
    have hlim : Tendsto (fun n => (priceT hQ β h)^[n] 0) atTop (𝓝 φ) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun n => hrate 0 n) ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (dist 0 φ)
    simp only [priceT_iterate_zero] at hlim
    have := hsum.hasSum.tendsto_sum_nat
    rw [tendsto_nhds_unique hlim this]
    exact hsum.hasSum
  · -- `φ ≥ 0` (the closed set of nonnegative functions is invariant), so `φ ≥ h > 0`
    have hclosed : IsClosed {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z} := by
      have : {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z} = ⋂ z, {f | 0 ≤ f z} := by ext; simp
      rw [this]
      exact isClosed_iInter fun z => isClosed_le continuous_const (continuous_eval_const z)
    have hmaps : MapsTo (priceT hQ β h) {f | ∀ z, 0 ≤ f z} {f | ∀ z, 0 ≤ f z} := by
      intro f hf z
      have := fellerOp_mono hQ (show 0 ≤ f from hf) z
      have h0 : fellerOp Q hQ 0 = 0 := by simpa using fellerOp_smul hQ 0 0
      rw [h0] at this
      simp only [priceT, coe_add, coe_smul, Pi.add_apply, smul_eq_mul]
      have := hpos z
      change 0 ≤ fellerOp Q hQ f z at *
      positivity
    have hφ0 := (corollary_1 (S' := {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z})
      (S'' := {f : Z →ᵇ ℝ | ∀ z, 0 ≤ f z}) hT hφ ⟨0, fun _ => le_rfl⟩ hclosed hmaps hmaps).1
    have hM := fellerOp_mono hQ (show 0 ≤ φ from hφ0) z
    have h0 : fellerOp Q hQ 0 = 0 := by simpa using fellerOp_smul hQ 0 0
    rw [h0] at hM
    rw [← hφ]
    simp only [priceT, coe_add, coe_smul, Pi.add_apply, smul_eq_mul]
    have := hpos z
    change 0 ≤ fellerOp Q hQ φ z at hM
    positivity

/-- **Exercise 10.6e.** Let `Z` be compact with a Feller transition `Q`, let `dᵢ(z) > 0` be the
dividends (continuous), `U′ > 0` continuous, and `hᵢ(z) = β ∫ U′(z′·1) z′ᵢ Q(z, dz′)`. Then for
each asset `i` the equation `φᵢ = hᵢ + βMφᵢ` (6) has a unique solution in `C(Z)`, it is
positive, it equals `Σₙ βⁿMⁿhᵢ`, and `p*ᵢ(z) = φᵢ(z)/U′(z·1)` solves (5):
`U′(z·1) p*ᵢ(z) = β ∫ U′(z′·1)[z′ᵢ + p*ᵢ(z′)] Q(z, dz′)`. -/
theorem ex_10_6e [CompactSpace Z] {k : ℕ} {d : Fin k → Z → ℝ} (hd : ∀ i, Continuous (d i))
    (hdpos : ∀ i z, 0 < d i z) {Up : ℝ → ℝ} (hUc : Continuous Up) (hUpos : ∀ c, 0 < Up c)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin k) :
    ∃ h φ : Z →ᵇ ℝ, (∀ z, h z = β * ∫ z', Up (∑ j, d j z') * d i z' ∂Q z) ∧
      φ = h + β • fellerOp Q hQ φ ∧
      (∀ ψ : Z →ᵇ ℝ, ψ = h + β • fellerOp Q hQ ψ → ψ = φ) ∧
      HasSum (fun n => β ^ n • (fellerOp Q hQ)^[n] h) φ ∧ (∀ z, 0 < φ z) ∧
      ∀ z, Up (∑ j, d j z) * (φ z / Up (∑ j, d j z)) =
        β * ∫ z', Up (∑ j, d j z') * (d i z' + φ z' / Up (∑ j, d j z')) ∂Q z := by
  have hgc : Continuous fun z => Up (∑ j, d j z) * d i z :=
    (hUc.comp (continuous_finsetSum _ fun j _ => hd j)).mul (hd i)
  set g : Z →ᵇ ℝ := mkOfCompact ⟨_, hgc⟩
  set h : Z →ᵇ ℝ := β • fellerOp Q hQ g
  have hh : ∀ z, h z = β * ∫ z', Up (∑ j, d j z') * d i z' ∂Q z := fun _ => rfl
  have hpos : ∀ z, 0 < h z := fun z => by
    rw [hh]
    refine mul_pos hβ0 ?_
    have := integral_lt_integral_of_lt (μ := Q z) (integrable_const (0 : ℝ))
      (integrable_bcf Q g z) fun z' => mul_pos (hUpos _) (hdpos i z')
    rw [integral_const, smul_zero] at this
    exact this
  obtain ⟨φ, hφ, huniq, hsum, hφpos⟩ := ex_10_6e_general hQ hβ0 hβ1 h
  refine ⟨h, φ, hh, hφ, huniq, hsum, hφpos hpos, fun z => ?_⟩
  rw [mul_div_cancel₀ _ (hUpos _).ne']
  have e : ∀ z', Up (∑ j, d j z') * (d i z' + φ z' / Up (∑ j, d j z')) = g z' + φ z' :=
    fun z' => by
      change _ = Up (∑ j, d j z') * d i z' + φ z'
      field_simp [(hUpos (∑ j, d j z')).ne']
  simp_rw [e]
  rw [integral_add (integrable_bcf Q g z) (integrable_bcf Q φ z), mul_add]
  conv_lhs => rw [hφ]
  rfl

end StokeyLucasPrescott.StochasticApplications
