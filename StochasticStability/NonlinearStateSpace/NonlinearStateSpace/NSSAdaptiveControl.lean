/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearStateSpace.NSSExamples

/-!
# The adaptive control model (MT §7.4.3)

Meyn and Tweedie, §7.4.3, pp. 162–163, for the closed loop simple adaptive control model
`sacStep` (MT (2.22)–(2.24)) with Gaussian disturbances (`sacGaussianKernel`), on the state space
`sacSpace = [σ_z², σ_z²/(1 − α²)] × ℝ²`.

* `sac_contDiffAt`: the step is smooth wherever `ΣY² + σ_w² ≠ 0`, in particular on the state
  space; `sac_duF` and `sac_dxF_fst`: the derivative in the disturbance, and the `Σ`-row of the
  derivative in the state (`∂Σ'/∂θ̃ = 0`, `∂Σ'/∂Y = −2α²σ_w²Σ²Y/(ΣY² + σ_w²)²`).
* `sac_genCtrb_surjective`: the second order controllability matrix has rank 3 when `Y₁ ≠ 0`
  (MT p. 163).
* `isLSCDensity_gaussianReal`: a non-degenerate Gaussian law satisfies (NSS3) with `O = ℝ`.
* `sacSpace` is closed and absorbing (`isAbsorbing_sacSpace`).
* **Proposition 7.4.3** (p. 162): `proposition_7_4_3`, the adaptive control model restricted to
  its state space is a `ψ`-irreducible aperiodic T-chain (`ψ` maximal).

**Corrections and hypotheses.** The book assumes `|α| < 1` and `σ_z² < 1`. The proof here
assumes `|α| < 1`, `α ≠ 0`, `σ_z ≠ 0` and `σ_w ≠ 0`, and does not use `σ_z² < 1`. For `α = 0` (or
`σ_z = 0`) the interval `[σ_z², σ_z²/(1 − α²)]` is a single point, so the state space is a plane
in `ℝ³` and the three-dimensional rank condition fails; the book's argument does not apply. The
book restricts the chain to the interior of the state space, claimed absorbing and reached in one
step; the latter is false (`sacKernel_interior_eq_zero` in `NSSExamples`). Here the chain is
restricted to the closed state space itself, which is absorbing, and the continuous components
are built at every point of it, including the boundary. ψ-irreducibility comes from the
reachable state `x* = (σ_z²/(1 − α²), 0, 0)`, the zero-noise limit (`sac_tendsto`), and
aperiodicity from `x*` being a fixed point: from near `x*` the chain is in a small neighbourhood
of `x*` at times `1` and `2` with positive probability, which no cycle of period `d ≥ 2` allows.
-/

namespace MeynTweedie.NonlinearStateSpace

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-! ### Smoothness and derivatives of the step -/

/-- The adaptive control step is `C¹` wherever `ΣY² + σ_w² ≠ 0`. -/
theorem sac_contDiffAt {α σz σw : ℝ} {p : ℝ × ℝ × ℝ} {q : ℝ × ℝ}
    (hne : p.1 * p.2.2 ^ 2 + σw ^ 2 ≠ 0) : ContDiffAt ℝ 1 (sacStep α σz σw) (p, q) := by
  unfold sacStep
  fun_prop (disch := simpa using hne)

/-- The derivative in the disturbance:
`Λ(dz, dw) = (0, dz − αΣY dw/(ΣY² + σ_w²), dw)`. -/
theorem sac_duF {α σz σw : ℝ} {p : ℝ × ℝ × ℝ} (hne : p.1 * p.2.2 ^ 2 + σw ^ 2 ≠ 0)
    (q v : ℝ × ℝ) :
    duF (sacStep α σz σw) p q v =
      (0, v.1 - α * p.1 * p.2.2 / (p.1 * p.2.2 ^ 2 + σw ^ 2) * v.2, v.2) := by
  set c : ℝ := α * p.1 * p.2.2 / (p.1 * p.2.2 ^ 2 + σw ^ 2)
  set L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) := (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ - c • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hsec : (fun w : ℝ × ℝ => sacStep α σz σw (p, w)) =
      fun w => sacStep α σz σw (p, 0) + L w := by
    funext w
    simp only [sacStep, L, ContinuousLinearMap.prod_apply, zero_apply,
      sub_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk_add_mk,
      Prod.fst_zero, Prod.snd_zero, add_zero, c]
    refine Prod.ext rfl (Prod.ext ?_ (by ring))
    simp only
    field_simp
    ring
  have hd : HasFDerivAt (fun w : ℝ × ℝ => sacStep α σz σw (p, w)) L q := by
    rw [hsec]
    exact L.hasFDerivAt.const_add _
  rw [duF_eq_of_hasFDerivAt ((sac_contDiffAt hne).differentiableAt one_ne_zero) hd]
  simp [L, c]

/-- The `Σ`-row of the derivative in the state, on directions `(0, a, b)`:
`∂Σ'/∂θ̃ = 0` and `∂Σ'/∂Y = −2α²σ_w²Σ²Y/(ΣY² + σ_w²)²` (MT p. 163). -/
theorem sac_dxF_fst {α σz σw : ℝ} {p : ℝ × ℝ × ℝ} (hne : p.1 * p.2.2 ^ 2 + σw ^ 2 ≠ 0)
    (q : ℝ × ℝ) (a b : ℝ) :
    (dxF (sacStep α σz σw) p q (0, a, b)).1 =
      -(2 * α ^ 2 * σw ^ 2 * p.1 ^ 2 * p.2.2 * b / (p.1 * p.2.2 ^ 2 + σw ^ 2) ^ 2) := by
  have hdiff := (sac_contDiffAt (α := α) (σz := σz) (q := q) hne).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun x' => sacStep α σz σw (x', q)) (dxF (sacStep α σz σw) p q) p := by
    unfold dxF
    exact hdiff.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p q)
  set v : ℝ × ℝ × ℝ := (0, a, b)
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have h2 := h1.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
  have h3 := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  set S := p.1
  set Y := p.2.2
  have hfun : ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) ∘ (fun x' => sacStep α σz σw (x', q)) ∘
      fun t : ℝ => p + t • v) =
      fun t : ℝ => σz ^ 2 + α ^ 2 * σw ^ 2 * S / (S * (Y + t * b) ^ 2 + σw ^ 2) := by
    funext t
    simp [sacStep, v, S, Y]
  rw [hfun] at h3
  have hd : HasDerivAt (fun t : ℝ => S * (Y + t * b) ^ 2 + σw ^ 2) (S * (2 * Y * b)) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const b).const_add Y).pow 2).const_mul S
    simpa using this.add_const (σw ^ 2)
  have hd0 : S * (Y + 0 * b) ^ 2 + σw ^ 2 ≠ 0 := by simpa using hne
  have h4 := ((hasDerivAt_const (0 : ℝ) (α ^ 2 * σw ^ 2 * S)).div hd hd0).const_add (σz ^ 2)
  have h5 := h3.unique h4
  simp only [ContinuousLinearMap.coe_fst', zero_mul, add_zero] at h5
  rw [h5]
  field_simp
  ring

/-! ### The second order controllability matrix -/

/-- **The second order controllability matrix has rank 3** when `Y₁ ≠ 0` (MT p. 163), for
`α ≠ 0`, `σ_w ≠ 0`, `Σ₁ ≠ 0`, at points where the step is smooth. -/
theorem sac_genCtrb_surjective {α σz σw : ℝ} (hα : α ≠ 0) (hσw : σw ≠ 0) {p : ℝ × ℝ × ℝ}
    (hne : p.1 * p.2.2 ^ 2 + σw ^ 2 ≠ 0) {u : Fin 2 → ℝ × ℝ}
    (hne1 : (sacStep α σz σw (p, u 0)).1 * (sacStep α σz σw (p, u 0)).2.2 ^ 2 + σw ^ 2 ≠ 0)
    (hS1 : (sacStep α σz σw (p, u 0)).1 ≠ 0) (hY1 : (sacStep α σz σw (p, u 0)).2.2 ≠ 0) :
    Function.Surjective (genCtrb (sacStep α σz σw) 2 p u) := by
  set F := sacStep α σz σw
  set p₁ := F (p, u 0)
  have hgen : ∀ v : Fin 2 → ℝ × ℝ, genCtrb F 2 p u v =
      dxF F p₁ (u 1) (duF F p (u 0) (v 0)) + duF F p₁ (u 1) (v 1) := fun v => by
    rw [genCtrb_succ_apply, genCtrb_one_apply]
    rfl
  set κ : ℝ := -(2 * α ^ 2 * σw ^ 2 * p₁.1 ^ 2 * p₁.2.2 * 1 / (p₁.1 * p₁.2.2 ^ 2 + σw ^ 2) ^ 2)
  have hκ : κ ≠ 0 := by
    simp only [κ, neg_ne_zero, mul_one]
    exact div_ne_zero (by positivity) (pow_ne_zero 2 hne1)
  have hSig : ∀ v : Fin 2 → ℝ × ℝ, (genCtrb F 2 p u v).1 = κ * (v 0).2 := fun v => by
    rw [hgen, Prod.fst_add, sac_duF hne, sac_dxF_fst hne1, sac_duF hne1]
    simp only [κ, add_zero]
    field_simp
  intro t
  set v₀ : Fin 2 → ℝ × ℝ := ![(0, t.1 / κ), (0, 0)]
  set r := genCtrb F 2 p u v₀
  set β : ℝ := α * p₁.1 * p₁.2.2 / (p₁.1 * p₁.2.2 ^ 2 + σw ^ 2)
  set dw : ℝ := t.2.2 - r.2.2
  set dz : ℝ := t.2.1 - r.2.1 + β * dw
  refine ⟨v₀ + ![(0, 0), (dz, dw)], ?_⟩
  have hv1 : genCtrb F 2 p u ![(0, 0), (dz, dw)] = (0, dz - β * dw, dw) := by
    rw [hgen]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [sac_duF hne, sac_duF hne1]
    simp only [mul_zero, sub_zero, β]
    have : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := rfl
    rw [this, map_zero, zero_add]
  rw [map_add, hv1]
  have hr1 : r.1 = t.1 := by
    change (genCtrb F 2 p u v₀).1 = t.1
    rw [hSig]
    simp only [v₀, Matrix.cons_val_zero]
    field_simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simpa using hr1
  · simp only [Prod.snd_add, Prod.fst_add, dz]; ring
  · simp only [Prod.snd_add, dw]; ring

/-! ### The Gaussian disturbances and the state space -/

/-- A non-degenerate centred Gaussian law satisfies (NSS3), with density `gaussianPDF`. -/
theorem isLSCDensity_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) :
    IsLSCDensity (gaussianReal 0 v) (gaussianPDF 0 v) :=
  ⟨(ENNReal.continuous_ofReal.comp (by unfold gaussianPDFReal; fun_prop)).lowerSemicontinuous,
    gaussianReal_of_var_ne_zero 0 hv⟩

/-- The disturbance law of `sacGaussianKernel` satisfies (NSS3) with control set `ℝ²`. -/
theorem sac_isLSCDensity {σz σw : ℝ} (hσz : σz ≠ 0) (hσw : σw ≠ 0) :
    IsLSCDensity ((gaussianReal 0 (σz ^ 2).toNNReal).prod (gaussianReal 0 (σw ^ 2).toNNReal))
      (fun p : ℝ × ℝ => gaussianPDF 0 (σz ^ 2).toNNReal p.1 * gaussianPDF 0 (σw ^ 2).toNNReal p.2)
      ∧ controlSet (fun p : ℝ × ℝ =>
        gaussianPDF 0 (σz ^ 2).toNNReal p.1 * gaussianPDF 0 (σw ^ 2).toNNReal p.2) = univ := by
  have hz : (σz ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hw : (σw ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  refine ⟨isLSCDensity_prod (isLSCDensity_gaussianReal hz) (isLSCDensity_gaussianReal hw), ?_⟩
  rw [controlSet_prod]
  have h1 : controlSet (gaussianPDF 0 (σz ^ 2).toNNReal) = univ :=
    eq_univ_of_forall fun x => gaussianPDF_pos 0 hz x
  have h2 : controlSet (gaussianPDF 0 (σw ^ 2).toNNReal) = univ :=
    eq_univ_of_forall fun x => gaussianPDF_pos 0 hw x
  rw [h1, h2, univ_prod_univ]

/-- The state space `[σ_z², σ_z²/(1 − α²)] × ℝ²` of the adaptive control model (MT p. 36). -/
def sacSpace (α σz : ℝ) : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc (σz ^ 2) (σz ^ 2 / (1 - α ^ 2))}

/-- The state space is closed. -/
theorem isClosed_sacSpace (α σz : ℝ) : IsClosed (sacSpace α σz) :=
  isClosed_Icc.preimage continuous_fst

/-- On the state space the denominator `ΣY² + σ_w²` is positive. -/
theorem sac_den_pos {α σz σw : ℝ} (hσw : σw ≠ 0) {p : ℝ × ℝ × ℝ} (hp : p ∈ sacSpace α σz) :
    0 < p.1 * p.2.2 ^ 2 + σw ^ 2 := by
  have h1 : 0 ≤ p.1 := le_trans (sq_nonneg σz) hp.1
  have := mul_nonneg h1 (sq_nonneg p.2.2)
  positivity

/-- The state space is invariant for every control (MT p. 36). -/
theorem sac_isInvariant {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) :
    IsInvariant (sacStep α σz σw) univ (sacSpace α σz) :=
  isInvariant_iff_step.2 fun _ hx w _ => sacStep_sigma_mem hα hσw hx w

/-- The state space is absorbing for the adaptive control model. -/
theorem isAbsorbing_sacSpace (Γ : Measure (ℝ × ℝ)) [IsProbabilityMeasure Γ] {α σz σw : ℝ}
    (hα : |α| < 1) (hσw : σw ≠ 0) : IsAbsorbing (sacKernel Γ α σz σw) (sacSpace α σz) := by
  intro x hx
  rw [sacKernel, recursionKernel_apply' Γ (measurable_sacStep α σz σw) x
    (isClosed_sacSpace α σz).measurableSet]
  have : {w : ℝ × ℝ | sacStep α σz σw (x, w) ∈ sacSpace α σz} = univ :=
    eq_univ_of_forall fun w => sacStep_sigma_mem hα hσw hx w
  rw [this, measure_univ]

/-- The zero-noise fixed point `x* = (σ_z²/(1 − α²), 0, 0)` (MT p. 163). -/
theorem sac_fixed {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) :
    sacStep α σz σw ((σz ^ 2 / (1 - α ^ 2), 0, 0), 0) = (σz ^ 2 / (1 - α ^ 2), 0, 0) := by
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have h1 : (1 : ℝ) - α ^ 2 ≠ 0 := by linarith
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [sacStep, Prod.fst_zero, Prod.snd_zero]
    field_simp
    ring
  · simp [sacStep]
  · simp [sacStep]

/-- The chain rule step for continuity of the control maps at a point. -/
theorem continuousAt_controlMap_succ_of {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    {F : X × W → X} {k : ℕ} {x : X} {u : Fin (k + 1) → W}
    (hk : ContinuousAt (controlMap F k x) (Fin.init u))
    (hF : ContinuousAt F (controlMap F k x (Fin.init u), u (Fin.last k))) :
    ContinuousAt (controlMap F (k + 1) x) u := by
  have hinit : Continuous fun v : Fin (k + 1) → W => Fin.init v :=
    continuous_pi fun i => continuous_apply _
  have h := ContinuousAt.comp (g := F) (x := u) hF
    ((hk.comp hinit.continuousAt).prodMk (continuous_apply (Fin.last k)).continuousAt)
  exact h

/-! ### Continuous components and reachability -/

/-- **Continuous components at every point of the state space**: for `|α| < 1`, `α ≠ 0`,
`σ_z ≠ 0`, `σ_w ≠ 0`, every `x ∈ sacSpace` has a continuous component of `P²` non-trivial at `x`
and an open small neighbourhood (rank condition with controls `((0, 1 − θ̃Y), (0, 0))`, which
make `Y₁ = 1`). -/
theorem sac_exists_component {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) {x : ℝ × ℝ × ℝ} (hx : x ∈ sacSpace α σz) :
    (∃ T : Kernel (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ),
      IsContinuousComponent (sacGaussianKernel α σz σw) (diracDist 2) T ∧ 0 < T x univ) ∧
      ∃ N : Set (ℝ × ℝ × ℝ), IsOpen N ∧ x ∈ N ∧ IsSmall (sacGaussianKernel α σz σw) N := by
  obtain ⟨hΓ, hO⟩ := sac_isLSCDensity hσz hσw
  set F := sacStep α σz σw
  set u : Fin 2 → ℝ × ℝ := ![(0, 1 - x.2.1 * x.2.2), 0]
  have hp1 : F (x, u 0) ∈ sacSpace α σz := sacStep_sigma_mem hα hσw hx _
  have hY1 : (F (x, u 0)).2.2 = 1 := by simp [F, sacStep, u]
  have hS1 : (F (x, u 0)).1 ≠ 0 := (lt_of_lt_of_le (by positivity) hp1.1).ne'
  have hne := (sac_den_pos hσw hx).ne'
  have hne1 := (sac_den_pos hσw hp1).ne'
  set G := fun p : (ℝ × ℝ × ℝ) × (Fin 2 → ℝ × ℝ) => controlMap F 2 p.1 p.2
  have hGeq : G = fun p => F (F (p.1, p.2 0), p.2 1) := rfl
  have hp0 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ × ℝ) × (Fin 2 → ℝ × ℝ) => p.2 0) (x, u) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ × ℝ) 0).contDiff.comp
      contDiff_snd).contDiffAt
  have hp1' : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ × ℝ) × (Fin 2 → ℝ × ℝ) => p.2 1) (x, u) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ × ℝ) 1).contDiff.comp
      contDiff_snd).contDiffAt
  have hin1 : ContDiffAt ℝ 1 (fun p : (ℝ × ℝ × ℝ) × (Fin 2 → ℝ × ℝ) => F (p.1, p.2 0)) (x, u) :=
    ContDiffAt.comp (g := F) (x, u) (sac_contDiffAt hne) (contDiffAt_fst.prodMk hp0)
  have hG : ContDiffAt ℝ 1 G (x, u) := by
    rw [hGeq]
    exact ContDiffAt.comp (g := F) (x, u) (sac_contDiffAt hne1) (hin1.prodMk hp1')
  have hderiv : HasFDerivAt (controlMap F 2 x) (genCtrb F 2 x u) u := by
    have h0 : HasFDerivAt (controlMap F 0 x) (genCtrb F 0 x (Fin.init (Fin.init u)))
        (Fin.init (Fin.init u)) := hasFDerivAt_const x _
    have h1 := hasFDerivAt_controlMap_succ_of h0
      ((sac_contDiffAt (α := α) (σz := σz) (q := u 0) hne).differentiableAt one_ne_zero)
    exact hasFDerivAt_controlMap_succ_of h1
      ((sac_contDiffAt (α := α) (σz := σz) (q := u 1) hne1).differentiableAt one_ne_zero)
  have hpart : (fderiv ℝ G (x, u)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (Fin 2 → ℝ × ℝ)) =
      genCtrb F 2 x u :=
    ((hG.differentiableAt one_ne_zero).hasFDerivAt.comp u
      (hasFDerivAt_prodMk_right x u)).unique hderiv
  have hsurj : Function.Surjective
      ((fderiv ℝ G (x, u)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (Fin 2 → ℝ × ℝ))) := by
    rw [hpart]
    exact sac_genCtrb_surjective hα0 hσw hne hne1 hS1 (by rw [hY1]; exact one_ne_zero)
  have hu : ∀ i, u i ∈ controlSet
      (fun p : ℝ × ℝ => gaussianPDF 0 (σz ^ 2).toNNReal p.1 *
        gaussianPDF 0 (σw ^ 2).toNNReal p.2) := fun i => by rw [hO]; trivial
  have := exists_continuousComponent hΓ (measurable_sacStep α σz σw) hu hG hsurj
  exact ⟨this.1, this.2 two_pos⟩

/-- Along the zero-noise path from a point of the state space the control maps are continuous in
the controls at `0`. -/
theorem sac_continuousAt_zero {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) {y : ℝ × ℝ × ℝ}
    (hy : y ∈ sacSpace α σz) (k : ℕ) :
    ContinuousAt (controlMap (sacStep α σz σw) k y) 0 := by
  induction k with
  | zero => exact continuous_const.continuousAt
  | succ k ih =>
    refine continuousAt_controlMap_succ_of ih ?_
    have hmem : controlMap (sacStep α σz σw) k y (Fin.init (0 : Fin (k + 1) → ℝ × ℝ)) ∈
        sacSpace α σz :=
      (sac_isInvariant hα hσw).reachK_subset hy k ⟨_, fun _ => trivial, rfl⟩
    exact (sac_contDiffAt (sac_den_pos hσw hmem).ne').continuousAt

/-- From a point of the state space, `Pᵏ(y, U) > 0` for every open `U` containing the `k`-th
point of the zero-noise path. -/
theorem sac_pow_pos {α σz σw : ℝ} (hα : |α| < 1) (hσz : σz ≠ 0) (hσw : σw ≠ 0)
    {y : ℝ × ℝ × ℝ} (hy : y ∈ sacSpace α σz) (k : ℕ) {U : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hkU : controlMap (sacStep α σz σw) k y 0 ∈ U) :
    0 < (sacGaussianKernel α σz σw ^ k) y U := by
  obtain ⟨hΓ, hO⟩ := sac_isLSCDensity hσz hσw
  rw [sacGaussianKernel, sacKernel,
    recursionKernel_pow_apply' _ (measurable_sacStep α σz σw) k y hU.measurableSet]
  have hpre : {u | controlMap (sacStep α σz σw) k y u ∈ U} ∈ 𝓝 (0 : Fin k → ℝ × ℝ) :=
    (sac_continuousAt_zero hα hσw hy k).preimage_mem_nhds (hU.mem_nhds hkU)
  obtain ⟨V, hVsub, hVo, h0V⟩ := mem_nhds_iff.1 hpre
  exact lt_of_lt_of_le (pi_measure_pos_of_isOpen hΓ hVo h0V fun i => by rw [hO]; trivial)
    (measure_mono hVsub)

/-- Along the zero-noise path from a point of the state space the control maps are jointly
continuous at `(y, 0)`. -/
theorem sac_continuousAt_joint {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) {y : ℝ × ℝ × ℝ}
    (hy : y ∈ sacSpace α σz) (k : ℕ) :
    ContinuousAt (fun p : (ℝ × ℝ × ℝ) × (Fin k → ℝ × ℝ) => controlMap (sacStep α σz σw) k p.1 p.2)
      (y, 0) := by
  induction k with
  | zero => exact continuous_fst.continuousAt
  | succ k ih =>
    have hmem : controlMap (sacStep α σz σw) k y (Fin.init (0 : Fin (k + 1) → ℝ × ℝ)) ∈
        sacSpace α σz :=
      (sac_isInvariant hα hσw).reachK_subset hy k ⟨_, fun _ => trivial, rfl⟩
    have hF := (sac_contDiffAt (α := α) (σz := σz) (q := (0 : ℝ × ℝ))
      (sac_den_pos hσw hmem).ne').continuousAt
    have hi : Continuous fun p : (ℝ × ℝ × ℝ) × (Fin (k + 1) → ℝ × ℝ) => (p.1, Fin.init p.2) :=
      continuous_fst.prodMk ((continuous_pi fun i => continuous_apply _).comp continuous_snd)
    have h2 := ContinuousAt.comp
      (f := fun p : (ℝ × ℝ × ℝ) × (Fin (k + 1) → ℝ × ℝ) => (p.1, Fin.init p.2))
      (x := (y, (0 : Fin (k + 1) → ℝ × ℝ))) ih hi.continuousAt
    have h := ContinuousAt.comp (g := sacStep α σz σw) (x := (y, (0 : Fin (k + 1) → ℝ × ℝ))) hF
      (h2.prodMk ((continuous_apply (Fin.last k)).comp continuous_snd).continuousAt)
    exact h

/-- The zero-noise path from `x*` stays at `x*`. -/
theorem sac_controlMap_fixed {α σz σw : ℝ} (hα : |α| < 1) (hσw : σw ≠ 0) (k : ℕ) :
    controlMap (sacStep α σz σw) k (σz ^ 2 / (1 - α ^ 2), 0, 0) 0 =
      (σz ^ 2 / (1 - α ^ 2), 0, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [controlMap_succ]
    change sacStep α σz σw (controlMap (sacStep α σz σw) k (σz ^ 2 / (1 - α ^ 2), 0, 0) 0, 0) = _
    rw [ih, sac_fixed hα hσw]

/-! ### Proposition 7.4.3 -/

/-- **Proposition 7.4.3** (MT p. 162), corrected: for the simple adaptive control model with
Gaussian disturbances, `|α| < 1`, `α ≠ 0`, `σ_z ≠ 0` and `σ_w ≠ 0`, the chain restricted to its
state space `[σ_z², σ_z²/(1 − α²)] × ℝ²` is a `ψ`-irreducible aperiodic T-chain, `ψ` a maximal
irreducibility measure. -/
theorem proposition_7_4_3 {α σz σw : ℝ} (hα : |α| < 1) (hα0 : α ≠ 0) (hσz : σz ≠ 0)
    (hσw : σw ≠ 0) :
    have := isMarkovKernel_sacGaussianKernel α σz σw
    let _ := isMarkovKernel_restrictKernel (sacGaussianKernel α σz σw)
      (isClosed_sacSpace α σz).measurableSet (isAbsorbing_sacSpace _ hα hσw)
    IsTChain
        (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet) ∧
      ∃ ψ : Measure (sacSpace α σz),
        IsMaximalIrreducibility
          (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet) ψ ∧
        IsAperiodic
          (restrictKernel (sacGaussianKernel α σz σw) (isClosed_sacSpace α σz).measurableSet)
          ψ := by
  have hPM := isMarkovKernel_sacGaussianKernel α σz σw
  obtain ⟨hΓ, hO⟩ := sac_isLSCDensity hσz hσw
  set P := sacGaussianKernel α σz σw
  set F := sacStep α σz σw
  set X := sacSpace α σz
  have hXm : MeasurableSet X := (isClosed_sacSpace α σz).measurableSet
  have hAbs : IsAbsorbing P X := isAbsorbing_sacSpace _ hα hσw
  let _ := isMarkovKernel_restrictKernel P hXm hAbs
  set PX := restrictKernel P hXm
  have hT : IsTChain PX := isTChain_restrictKernel_of_local hXm hAbs fun x hx => by
    obtain ⟨T, hT, hpos⟩ := (sac_exists_component hα hα0 hσz hσw hx).1
    exact ⟨diracDist 2, T, isSamplingDist_diracDist 2, hT, hpos⟩
  have hα2 : α ^ 2 < 1 := by
    have := sq_abs α
    nlinarith [abs_nonneg α]
  have hxs : ((σz ^ 2 / (1 - α ^ 2), 0, 0) : ℝ × ℝ × ℝ) ∈ X := by
    refine ⟨?_, le_rfl⟩
    change σz ^ 2 ≤ σz ^ 2 / (1 - α ^ 2)
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg σz, sq_nonneg α]
  set xs : X := ⟨(σz ^ 2 / (1 - α ^ 2), 0, 0), hxs⟩
  have htrans : ∀ n (y : X) {U : Set (ℝ × ℝ × ℝ)}, IsOpen U →
      (PX ^ n) y ((Subtype.val : X → ℝ × ℝ × ℝ) ⁻¹' U) = (P ^ n) y U := by
    intro n y U hU
    rw [restrictKernel_pow_apply P hXm hAbs n y (measurable_subtype_coe hU.measurableSet),
      Subtype.image_preimage_coe, inter_comm, measure_inter_conull (hAbs.pow_compl hXm n y.2)]
  have hreach : IsReachable PX xs := by
    intro O hO hxO y
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hO
    rw [potKernel_pos_iff _ hO.measurableSet]
    have ht := sac_tendsto (α := α) (σz := σz) (σw := σw) hα hσw (x₀ := (y : ℝ × ℝ × ℝ)) y.2
    obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (hU.mem_nhds hxO))
    refine ⟨K, ?_⟩
    rw [htrans _ y hU]
    exact sac_pow_pos hα hσz hσw y.2 (K + 1) hU (hK (K + 1) (by omega))
  obtain ⟨a, T, ha, hTc, hTpos⟩ := hT
  have hψ0 := proposition_6_2_1 hTc hreach
  have hne : T xs ≠ 0 := fun h => by
    have := hTpos xs
    rw [h] at this
    simp at this
  have hmax := isMaximalIrreducibility_maxIrrMeasure PX hψ0 hne
  refine ⟨⟨a, T, ha, hTc, hTpos⟩, _, hmax, ?_⟩
  set ψ := maxIrrMeasure PX (T xs)
  -- a small neighbourhood `N` of `x*`, restricted to `X`
  obtain ⟨N, hNo, hxN, m, ν, hN⟩ := (sac_exists_component hα hα0 hσz hσw hxs).2
  set NX : Set X := (Subtype.val : X → ℝ × ℝ × ℝ) ⁻¹' N
  have hνX : IsSmallSet PX m (ν.comap (Subtype.val : X → ℝ × ℝ × ℝ)) NX := by
    refine ⟨measurable_subtype_coe hNo.measurableSet, hN.2.1, fun h0 => ?_, fun x hx => ?_⟩
    · have h1 : ν Xᶜ = 0 := nonpos_iff_eq_zero.1
        ((hN.le_apply hxN Xᶜ).trans (hAbs.pow_compl hXm m hxs).le)
      have h2 : (ν.comap (Subtype.val : X → ℝ × ℝ × ℝ)) univ = ν X := by
        rw [(MeasurableEmbedding.subtype_coe hXm).comap_apply, image_univ, Subtype.range_coe]
      apply hN.2.2.1
      rw [← Measure.measure_univ_eq_zero]
      have h3 := measure_univ_le_add_compl (μ := ν) X
      rw [h1, add_zero, ← h2, h0, Measure.coe_zero, Pi.zero_apply] at h3
      exact nonpos_iff_eq_zero.1 h3
    · refine Measure.le_intro fun B hB _ => ?_
      rw [(MeasurableEmbedding.subtype_coe hXm).comap_apply,
        restrictKernel_pow_apply P hXm hAbs m x hB]
      exact hN.le_apply hx _
  -- from near `x*`, the chain is in `N` at times `1` and `2` with positive probability
  have hnear : ∀ k, ∃ V ∈ 𝓝 ((σz ^ 2 / (1 - α ^ 2), 0, 0) : ℝ × ℝ × ℝ),
      ∀ x ∈ V, 0 < (P ^ k) x N := by
    intro k
    have hc := sac_continuousAt_joint (α := α) (σw := σw) hα hσw hxs k
    have hmem : controlMap F k (σz ^ 2 / (1 - α ^ 2), 0, 0) 0 ∈ N := by
      rw [sac_controlMap_fixed hα hσw]; exact hxN
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ :=
      mem_nhds_prod_iff.1 (hc.preimage_mem_nhds (hNo.mem_nhds hmem))
    refine ⟨V₁, hV₁, fun x hx => ?_⟩
    obtain ⟨V, hVsub, hVo, h0V⟩ := mem_nhds_iff.1 hV₂
    rw [show P = sacKernel _ α σz σw from rfl, sacKernel,
      recursionKernel_pow_apply' _ (measurable_sacStep α σz σw) k x hNo.measurableSet]
    refine lt_of_lt_of_le (pi_measure_pos_of_isOpen hΓ hVo h0V fun i => by rw [hO]; trivial)
      (measure_mono fun u hu => ?_)
    exact hsub (mk_mem_prod hx (hVsub hu))
  obtain ⟨V1, hV1, hP1⟩ := hnear 1
  obtain ⟨V2, hV2, hP2⟩ := hnear 2
  have hψV : 0 < ψ ((Subtype.val : X → ℝ × ℝ × ℝ) ⁻¹' (V1 ∩ V2)) := by
    have hsupp := (lemma_6_1_4 hmax xs).1 hreach
    exact (Measure.mem_support_iff_forall _).1 hsupp _
      (continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem hV1 hV2))
  refine ⟨one_pos, ⟨fun _ => univ, ⟨fun _ => MeasurableSet.univ,
    fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ x _ => measure_univ,
    by simp [iInter_const, measure_empty]⟩⟩, fun d' D hd' hD => ?_⟩
  have : NeZero d' := ⟨hd'.ne'⟩
  obtain ⟨c, hc⟩ : ∃ c, 0 < ψ ((Subtype.val : X → ℝ × ℝ × ℝ) ⁻¹' (V1 ∩ V2) ∩ D c) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Subtype.val : X → ℝ × ℝ × ℝ) ⁻¹' (V1 ∩ V2) ⊆
        (⋃ c, (Subtype.val : X → ℝ × ℝ × ℝ) ⁻¹' (V1 ∩ V2) ∩ D c) ∪ (⋃ i, D i)ᶜ := by
      intro x hx
      by_cases hxD : x ∈ ⋃ i, D i
      · obtain ⟨c, hc⟩ := mem_iUnion.1 hxD
        exact Or.inl (mem_iUnion.2 ⟨c, hx, hc⟩)
      · exact Or.inr hxD
    exact hψV.ne' (measure_mono_null hsub (measure_union_null
      (measure_iUnion_null fun c => nonpos_iff_eq_zero.1 (hcon c)) hD.null_compl))
  obtain ⟨x, ⟨hx1, hx2⟩, hxc⟩ := nonempty_of_measure_ne_zero hc.ne'
  have hpos : ∀ k : ℕ, 0 < (P ^ k) (x : ℝ × ℝ × ℝ) N →
      ∃ y : X, y ∈ NX ∧ y ∈ D (c + k) := by
    intro k hk
    have := isMarkovKernel_pow PX k
    have h1 : 0 < (PX ^ k) x (NX ∩ D (c + k)) := by
      rw [measure_inter_conull]
      · rw [htrans k x hNo]; exact hk
      · rw [prob_compl_eq_zero_iff (hD.measurableSet _)]
        exact hD.pow_apply k hxc
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero h1.ne'
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨y, hyN, hyD⟩ := hpos 1 (hP1 _ hx1)
  obtain ⟨z, hzN, hzD⟩ := hpos 2 (hP2 _ hx2)
  have hcz := cycle_class_eq_of_isSmallSet hD hνX hyN hyD hzN hzD
  have h1 : ((1 : ℕ) : ZMod d') = 0 := by
    push_cast at hcz ⊢
    linear_combination -hcz
  exact Nat.le_of_dvd one_pos ((ZMod.natCast_eq_zero_iff 1 d').1 h1)

end MeynTweedie.NonlinearStateSpace
