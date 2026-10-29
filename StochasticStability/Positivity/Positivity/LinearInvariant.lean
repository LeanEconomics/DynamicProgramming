/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.Invariance
import Positivity.LinearTChains
import Mathlib.Probability.Independence.InfinitePi

/-!
# The invariant probability of the linear state space model (MT §10.5.4)

Meyn and Tweedie, §10.5.4, pp. 252–253. `lssMatrixKernel Γ F G` is the model
`X_{k+1} = F X_k + G W_{k+1}` on `ℝⁿ` (LSS1)–(LSS2), with i.i.d. disturbances of law `Γ` on
`ℝᵖ`. Under the eigenvalue condition (LSS5) (`IsStableMatrix F`) and a first moment
`E|W| < ∞`:

* `ae_summable_lssSeries`: the series `X_∞ = Σᵢ Fⁱ G Wᵢ` converges absolutely almost surely under
  `Γ^{⊗ℕ}` (its expected norm is at most `C ‖G‖ E|W| / (1 − r)`, with `‖Fⁱ‖ ≤ C rⁱ`,
  Lemma 6.3.4);
* `lssSeries_cons`: `X_∞(v, W₀, W₁, …) = G v + F X_∞(W₀, W₁, …)`;
* `infinitePi_map_head_tail'`: under `Γ^{⊗ℕ}` the first coordinate and the shifted sequence are
  independent, with laws `Γ` and `Γ^{⊗ℕ}`;
* `isInvariant_lssLimitLaw`: the law `π_∞` of `X_∞` is an invariant probability for the model
  (MT p. 253).

**Not formalised.** The convergence `Pᵏg(x₀) → E[g(X_∞)]` (the book's route to invariance through
(10.4)) is replaced by the direct identity `X_∞ ∘ cons = G v + F X_∞`; the Gaussian form
`π = N(0, Σ)` is proved for the scalar model in `ModelInvariant`
(`isInvariant_ar1_gaussian_stable`).
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal Matrix

/-! ### The first coordinate and the shift of an i.i.d. sequence -/

variable {W : Type*} [MeasurableSpace W]

/-- The coordinates of an i.i.d. sequence `Γ^{⊗ℕ}` are independent. -/
theorem iIndep_coords' (Γ : Measure W) [IsProbabilityMeasure Γ] :
    iIndep (fun i => MeasurableSpace.comap (fun w : ℕ → W => w i) inferInstance)
      (Measure.infinitePi fun _ : ℕ => Γ) :=
  (iIndepFun_iff_iIndep _ _ _).1
    (iIndepFun_infinitePi (P := fun _ : ℕ => Γ) (X := fun _ => id) (fun _ => measurable_id))

/-- The shift `(w₀, w₁, …) ↦ (w₁, w₂, …)`. -/
def seqShift (w : ℕ → W) : ℕ → W := fun i => w (i + 1)

/-- The shift is measurable. -/
theorem measurable_seqShift : Measurable (seqShift (W := W)) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (i + 1)

/-- The shift of an i.i.d. sequence is i.i.d. with the same law. -/
theorem infinitePi_map_seqShift (Γ : Measure W) [IsProbabilityMeasure Γ] :
    (Measure.infinitePi fun _ : ℕ => Γ).map seqShift = Measure.infinitePi fun _ : ℕ => Γ := by
  have h := (iIndep_coords' Γ).precomp (g := fun i => i + 1) (fun a b hab => by simpa using hab)
  have h' : iIndepFun (fun i (w : ℕ → W) => w (i + 1)) (Measure.infinitePi fun _ : ℕ => Γ) :=
    (iIndepFun_iff_iIndep _ _ _).2 h
  have := h'.map_fun_eq_infinitePi_map (fun i => measurable_pi_apply (i + 1))
  rw [show seqShift = fun (w : ℕ → W) i => w (i + 1) from rfl, this]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval _ _

/-- Under `Γ^{⊗ℕ}` the first coordinate and the shifted sequence are independent. -/
theorem indepFun_head_seqShift (Γ : Measure W) [IsProbabilityMeasure Γ] :
    IndepFun (fun w : ℕ → W => w 0) seqShift (Measure.infinitePi fun _ : ℕ => Γ) := by
  set m : ℕ → MeasurableSpace (ℕ → W) :=
    fun i => MeasurableSpace.comap (fun w : ℕ → W => w i) inferInstance
  have hle : ∀ i, m i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  have hind := indep_iSup_of_disjoint hle (iIndep_coords' Γ)
    (S := {0}) (T := Ici 1) (by
      rw [Set.disjoint_left]
      intro i hi hi'
      rw [mem_singleton_iff] at hi
      rw [hi] at hi'
      exact absurd (mem_Ici.1 hi') (by omega))
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
  · exact le_iSup₂ (f := fun j (_ : j ∈ ({0} : Set ℕ)) => m j) 0 rfl
  · simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, iSup_le_iff]
    intro i
    exact le_iSup₂ (f := fun j (_ : j ∈ Ici 1) => m j) (i + 1) (by simp)

/-- Under `Γ^{⊗ℕ}`, `(w₀, (w₁, w₂, …))` has law `Γ ⊗ Γ^{⊗ℕ}`. -/
theorem infinitePi_map_head_tail' (Γ : Measure W) [IsProbabilityMeasure Γ] :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun y => (y 0, seqShift y)) =
      Γ.prod (Measure.infinitePi fun _ : ℕ => Γ) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    measurable_seqShift.aemeasurable).1 (indepFun_head_seqShift Γ), infinitePi_map_seqShift,
    Measure.infinitePi_map_eval]

/-- The sequence `(v, w₀, w₁, …)`. -/
def consSeq (v : W) (w : ℕ → W) : ℕ → W
  | 0 => v
  | i + 1 => w i

/-- `consSeq` is measurable. -/
theorem measurable_consSeq : Measurable fun q : W × (ℕ → W) => consSeq q.1 q.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  cases i with
  | zero => exact measurable_fst
  | succ i => exact (measurable_pi_apply i).comp measurable_snd

/-- `Γ^{⊗ℕ} = (Γ ⊗ Γ^{⊗ℕ}) ∘ cons⁻¹`. -/
theorem prod_map_consSeq (Γ : Measure W) [IsProbabilityMeasure Γ] :
    (Γ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fun q => consSeq q.1 q.2) =
      Measure.infinitePi fun _ : ℕ => Γ := by
  rw [← infinitePi_map_head_tail', Measure.map_map measurable_consSeq
    ((measurable_pi_apply 0).prodMk measurable_seqShift)]
  have : ((fun q : W × (ℕ → W) => consSeq q.1 q.2) ∘ fun y => (y 0, seqShift y)) = id := by
    funext y; funext i; cases i <;> rfl
  rw [this, Measure.map_id]

/-! ### The series `X_∞ = Σ Fⁱ G Wᵢ` -/

variable {n p : ℕ}

/-- The series `X_∞ = Σᵢ Fⁱ G wᵢ` (zero when it does not converge). -/
noncomputable def lssSeries (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (w : ℕ → Fin p → ℝ) : Fin n → ℝ :=
  ∑' i, (F ^ i) *ᵥ (G *ᵥ w i)

/-- `X_∞` is measurable. -/
theorem measurable_lssSeries (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Measurable (lssSeries F G) :=
  Measurable.tsum (f := fun i (w : ℕ → Fin p → ℝ) => (F ^ i) *ᵥ (G *ᵥ w i)) fun i =>
    (measurable_mulVec (F ^ i)).comp ((measurable_mulVec G).comp (measurable_pi_apply i))

/-- The terms of the series. -/
noncomputable def lssTerm (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (w : ℕ → Fin p → ℝ) (i : ℕ) : Fin n → ℝ :=
  (F ^ i) *ᵥ (G *ᵥ w i)

/-- `‖G v‖ ≤ K ‖v‖` for the operator norm `K` of `v ↦ Gv`. -/
theorem norm_mulVec_le (G : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    ‖G *ᵥ v‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toLin' G)‖ * ‖v‖ := by
  have := (LinearMap.toContinuousLinearMap (Matrix.toLin' G)).le_opNorm v
  simpa [Matrix.toLin'_apply] using this

/-- Under (LSS5) and `E|W| < ∞`, the series `Σ Fⁱ G Wᵢ` converges absolutely almost surely. -/
theorem ae_summable_lssSeries (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) (G : Matrix (Fin n) (Fin p) ℝ)
    (hint : ∫⁻ v, ‖v‖ₑ ∂Γ ≠ ∞) :
    ∀ᵐ w ∂(Measure.infinitePi fun _ : ℕ => Γ), Summable fun i => ‖lssTerm F G w i‖ := by
  obtain ⟨C, r, hC, hr0, hr1, hbound⟩ := isStableMatrix_geometric hF
  set K := ‖LinearMap.toContinuousLinearMap (Matrix.toLin' G)‖
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  have hterm : ∀ w i, ‖lssTerm F G w i‖ₑ ≤ ENNReal.ofReal (C * K * r ^ i) * ‖w i‖ₑ := by
    intro w i
    have h1 : ‖lssTerm F G w i‖ ≤ C * K * r ^ i * ‖w i‖ :=
      calc ‖lssTerm F G w i‖ ≤ C * r ^ i * ‖G *ᵥ w i‖ := hbound i _
        _ ≤ C * r ^ i * (K * ‖w i‖) := by
            gcongr
            exact norm_mulVec_le G (w i)
        _ = C * K * r ^ i * ‖w i‖ := by ring
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  have hmeas : ∀ i, Measurable fun w : ℕ → Fin p → ℝ => ‖lssTerm F G w i‖ₑ := fun i =>
    ((measurable_mulVec (F ^ i)).comp ((measurable_mulVec G).comp
      (measurable_pi_apply i))).enorm
  have hint' : ∫⁻ w, ∑' i, ‖lssTerm F G w i‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun i => (hmeas i).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' i, ENNReal.ofReal (C * K * r ^ i) * ∫⁻ v, ‖v‖ₑ ∂Γ) ?_
      (ENNReal.tsum_le_tsum fun i => ?_)
    · rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ hint
      have hs : Summable fun i => C * K * r ^ i :=
        (summable_geometric_of_lt_one hr0.le hr1).mul_left _
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs]
      exact ENNReal.ofReal_ne_top
    · calc ∫⁻ w, ‖lssTerm F G w i‖ₑ ∂μ ≤ ∫⁻ w, ENNReal.ofReal (C * K * r ^ i) * ‖w i‖ₑ ∂μ :=
            lintegral_mono fun w => hterm w i
        _ = ENNReal.ofReal (C * K * r ^ i) * ∫⁻ v, ‖v‖ₑ ∂Γ := by
            rw [lintegral_const_mul _ ((measurable_pi_apply i).enorm),
              ← lintegral_map (f := fun v : Fin p → ℝ => ‖v‖ₑ) measurable_enorm
                (measurable_pi_apply i), Measure.infinitePi_map_eval]
  filter_upwards [ae_lt_top (Measurable.tsum hmeas) hint'] with w hw
  have : ∑' i, (‖lssTerm F G w i‖₊ : ℝ≥0∞) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hw.ne
  have h := NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)
  simpa using h

/-- `X_∞(v, w₀, w₁, …) = G v + F X_∞(w₀, w₁, …)` when `Σ Fⁱ G wᵢ` converges absolutely. -/
theorem lssSeries_cons (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (v : Fin p → ℝ) {w : ℕ → Fin p → ℝ} (hs : Summable fun i => ‖lssTerm F G w i‖) :
    lssSeries F G (consSeq v w) = G *ᵥ v + F *ᵥ lssSeries F G w := by
  set T := LinearMap.toContinuousLinearMap (Matrix.toLin' F)
  have hT : ∀ x, T x = F *ᵥ x := fun x => by simp [T, Matrix.toLin'_apply]
  have hsum : Summable (lssTerm F G w) := hs.of_norm
  have hsucc : ∀ i, (F ^ (i + 1)) *ᵥ (G *ᵥ consSeq v w (i + 1)) = T (lssTerm F G w i) := fun i => by
    simp only [hT, lssTerm, Matrix.mulVec_mulVec, pow_succ']
    rw [Matrix.mul_assoc]
    rfl
  have hsum' : Summable fun i => (F ^ (i + 1)) *ᵥ (G *ᵥ consSeq v w (i + 1)) := by
    simp_rw [hsucc]
    exact T.summable hsum
  rw [lssSeries, tsum_eq_zero_add' (f := fun i => (F ^ i) *ᵥ (G *ᵥ consSeq v w i)) hsum']
  simp_rw [hsucc]
  rw [← T.map_tsum hsum, hT, pow_zero, Matrix.one_mulVec]
  rfl

/-- `μP = (μ ⊗ Γ) ∘ step⁻¹` for the LSS model. -/
theorem lssMatrixKernel_comp (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (π : Measure (Fin n → ℝ))
    [SFinite π] :
    lssMatrixKernel Γ F G ∘ₘ π = (π.prod Γ).map fun q => F *ᵥ q.1 + G *ᵥ q.2 := by
  ext A hA
  rw [measure_kernel_apply _ _ hA, Measure.map_apply (measurable_lssMatrixStep F G) hA,
    Measure.prod_apply (measurable_lssMatrixStep F G hA)]
  refine lintegral_congr fun x => ?_
  rw [lssMatrixKernel, recursionKernel_apply' Γ (measurable_lssMatrixStep F G) x hA]
  rfl

/-- The law `π_∞` of `X_∞ = Σ Fⁱ G Wᵢ` under `Γ^{⊗ℕ}`. -/
noncomputable def lssLimitLaw (Γ : Measure (Fin p → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin p) ℝ) : Measure (Fin n → ℝ) :=
  (Measure.infinitePi fun _ : ℕ => Γ).map (lssSeries F G)

/-- `π_∞` is a probability measure. -/
theorem isProbabilityMeasure_lssLimitLaw (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    IsProbabilityMeasure (lssLimitLaw Γ F G) := by
  unfold lssLimitLaw; infer_instance

/-- **§10.5.4** (MT p. 253): under (LSS5) and `E|W| < ∞`, the law `π_∞` of
`X_∞ = Σᵢ Fⁱ G Wᵢ` is an invariant probability for the linear state space model. -/
theorem isInvariant_lssLimitLaw (Γ : Measure (Fin p → ℝ)) [IsProbabilityMeasure Γ]
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsStableMatrix F) (G : Matrix (Fin n) (Fin p) ℝ)
    (hint : ∫⁻ v, ‖v‖ₑ ∂Γ ≠ ∞) :
    IsInvariant (lssMatrixKernel Γ F G) (lssLimitLaw Γ F G) := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  have hL := measurable_lssSeries F G
  have := isProbabilityMeasure_lssLimitLaw Γ F G
  have hstep := measurable_lssMatrixStep F G
  unfold IsInvariant
  have hprod : (μ.map (lssSeries F G)).prod Γ = (μ.prod Γ).map (Prod.map (lssSeries F G) id) := by
    rw [← Measure.map_prod_map μ Γ hL measurable_id, Measure.map_id]
  rw [lssMatrixKernel_comp, lssLimitLaw, hprod, Measure.map_map hstep (hL.prodMap measurable_id)]
  -- `π_∞ = (Γ ⊗ μ) ∘ (v, w) ↦ G v + F X_∞(w)`
  have hg : Measurable fun q : (Fin p → ℝ) × (ℕ → Fin p → ℝ) =>
      G *ᵥ q.1 + F *ᵥ lssSeries F G q.2 :=
    ((measurable_mulVec G).comp measurable_fst).add ((measurable_mulVec F).comp
      (hL.comp measurable_snd))
  have hae : ∀ᵐ q ∂(Γ.prod μ), Summable fun i => ‖lssTerm F G q.2 i‖ := by
    have hmap : (Γ.prod μ).map (Prod.snd : (Fin p → ℝ) × (ℕ → Fin p → ℝ) → ℕ → Fin p → ℝ) = μ := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    have h0 : ∀ᵐ w ∂μ, Summable fun i => ‖lssTerm F G w i‖ := ae_summable_lssSeries Γ hF G hint
    rw [← hmap] at h0
    exact ae_of_ae_map measurable_snd.aemeasurable h0
  have h1 : μ.map (lssSeries F G) = (Γ.prod μ).map fun q => G *ᵥ q.1 + F *ᵥ lssSeries F G q.2 := by
    have hc : μ = (Γ.prod μ).map (fun q => consSeq q.1 q.2) := (prod_map_consSeq Γ).symm
    conv_lhs => rw [hc]
    rw [Measure.map_map hL measurable_consSeq]
    refine Measure.map_congr (hae.mono fun q hq => ?_)
    exact lssSeries_cons F G q.1 hq
  rw [h1, ← Measure.prod_swap,
    Measure.map_map (hstep.comp (hL.prodMap measurable_id)) measurable_swap]
  congr 1
  funext q
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, Prod.map_fst, Prod.map_snd, id]
  exact add_comm _ _

end MeynTweedie.Positivity
