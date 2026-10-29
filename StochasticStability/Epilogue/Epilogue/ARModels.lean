/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.VUniformErgodic
import Epilogue.ModelNonlinearModels

/-!
# Autoregressive and state space models (MT §16.5)

Meyn and Tweedie, §16.5, pp. 414–418.

**Quadratic forms.** `quadForm M x = xᵀ M x` on `ℝⁿ = Fin n → ℝ`.
* `quadForm_smul`, `quadForm_add` (for symmetric `M`): `q(u + w) = q(u) + 2 (Mu)ᵀ w + q(w)`;
  `quadForm_nonneg`, `quadForm_add_le` (`q(u + w) ≤ 2 q(u) + 2 q(w)`) for `M ≥ 0`.
* `exists_quadForm_bounds`: for positive definite `M`, `a |x|² ≤ xᵀ M x ≤ b |x|²` with `a > 0`
  (compactness of the unit sphere).

**The multidimensional RCA model** (16.38), `Φₖ₊₁ = (A + Γₖ₊₁) Φₖ + Wₖ₊₁` (`rcaKernel`).
* `rca_lintegral_quadForm`, (16.42): `E[V(Φₖ₊₁) | Φₖ = x] = E[xᵀ(A + Γ)ᵀ M (A + Γ)x] + E[WᵀMW]`
  (for `E[W] = 0` and independent `Γ`, `W`), so with (16.41)
  `PV(x) = V(x) − xᵀNx + E[WᵀMW]` (16.43) for `V(x) = xᵀMx`.
* **Theorem 16.5.1** (`theorem_16_5_1`, p. 415): `Φ` is `V`-uniformly ergodic for
  `V(x) = |x|² + 1`, and every invariant probability has finite second moments (a second-order
  stationary version exists).

**Hypotheses.** The book proves Theorem 16.5.1 from two results it quotes from Nicholls and
Quinn [299]: under (RCA1)–(RCA2), for positive definite `N` the matrix `M` of (16.40) is positive
definite, and (16.41) `E[xᵀ(A + Γ)ᵀ M (A + Γ)x] = xᵀMx − xᵀNx`. These are hypotheses here (the
pair `M`, `N`), as are `ψ`-irreducibility, aperiodicity and the petiteness of compact sets, which
the book derives from the density condition (RCA3) through the T-chain property (Theorem 6.2.9);
as in `GeometricModels`, that derivation is not formalised for these models. Of (RCA2) only
`E[W] = 0` and the finiteness of `E[W Wᵀ]` are used directly. `|x|² + 1` replaces the book's
`|x|²`, since (V4) needs `V ≥ 1`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal Topology

/-! ### Quadratic forms -/

/-- The quadratic form `q_M(x) = xᵀ M x` on `ℝⁿ`. -/
def quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- `q_M` is continuous. -/
theorem continuous_quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (quadForm M) := by
  unfold quadForm
  exact continuous_id.dotProduct (Continuous.matrix_mulVec continuous_const continuous_id)

/-- `q_M(t x) = t² q_M(x)`. -/
theorem quadForm_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    quadForm M (t • x) = t ^ 2 * quadForm M x := by
  unfold quadForm
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- `wᵀ M u = uᵀ M w` for symmetric `M`. -/
theorem dotProduct_mulVec_comm_of_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) (u w : Fin n → ℝ) : w ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ w) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

/-- **Expanding the square**: `q(u + w) = q(u) + 2 uᵀ M w + q(w)` for symmetric `M`. -/
theorem quadForm_add {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M)
    (u w : Fin n → ℝ) :
    quadForm M (u + w) = quadForm M u + 2 * (u ⬝ᵥ (M *ᵥ w)) + quadForm M w := by
  unfold quadForm
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_mulVec_comm_of_symm hM u w]
  ring

/-- `q_M ≥ 0` for positive semidefinite `M`. -/
theorem quadForm_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (x : Fin n → ℝ) : 0 ≤ quadForm M x := by
  have := hM.dotProduct_mulVec_nonneg x
  simpa [quadForm] using this

/-- `q(u + w) ≤ 2 q(u) + 2 q(w)` for positive semidefinite `M` (from `q(u − w) ≥ 0`). -/
theorem quadForm_add_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (u w : Fin n → ℝ) : quadForm M (u + w) ≤ 2 * quadForm M u + 2 * quadForm M w := by
  have hsym : Mᵀ = M := by
    have := hM.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have h1 := quadForm_add hsym u w
  have h2 := quadForm_add hsym u (-w)
  have h3 := quadForm_nonneg hM (u + -w)
  have hneg : quadForm M (-w) = quadForm M w := by
    rw [show -w = (-1 : ℝ) • w by simp, quadForm_smul]; ring
  have hcross : u ⬝ᵥ (M *ᵥ -w) = -(u ⬝ᵥ (M *ᵥ w)) := by
    rw [mulVec_neg, dotProduct_neg]
  rw [hneg, hcross] at h2
  linarith

/-- **Two-sided bounds for a positive definite form**: `a |x|² ≤ xᵀMx ≤ b |x|²` with `a > 0`, where
`|x|² = x ⬝ x` (by compactness of the unit sphere `{x ⬝ x = 1}`). -/
theorem exists_quadForm_bounds {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x, a * (x ⬝ᵥ x) ≤ quadForm M x ∧ quadForm M x ≤ b * (x ⬝ᵥ x) := by
  set S : Set (Fin n → ℝ) := {x | x ⬝ᵥ x = 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq (by fun_prop) continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset fun x hx => ?_)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    have hx' : x ⬝ᵥ x = 1 := hx
    rw [← hx', dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have : 0 ≤ ∑ j ∈ Finset.univ.erase i, x j * x j :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    nlinarith
  -- the scaling to the sphere
  have hscale : ∀ x : Fin n → ℝ, x ≠ 0 →
      ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ∈ S ∧ 0 < x ⬝ᵥ x := fun x hx => by
    have hpos : 0 < x ⬝ᵥ x := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
    refine ⟨?_, hpos⟩
    change (Real.sqrt (x ⬝ᵥ x))⁻¹ • x ⬝ᵥ (Real.sqrt (x ⬝ᵥ x))⁻¹ • x = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
      inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hq : ∀ x : Fin n → ℝ, x ≠ 0 →
      quadForm M x = (x ⬝ᵥ x) * quadForm M ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) := fun x hx => by
    have hpos := (hscale x hx).2
    rw [quadForm_smul, inv_pow, Real.sq_sqrt hpos.le, ← mul_assoc, mul_inv_cancel₀ hpos.ne',
      one_mul]
  rcases S.eq_empty_or_nonempty with h0 | hne
  · -- `n = 0`: every vector is `0`
    have hx0 : ∀ x : Fin n → ℝ, x = 0 := fun x => by
      by_contra hx
      have := (hscale x hx).1
      rw [h0] at this
      exact this
    refine ⟨1, 0, one_pos, fun x => ?_⟩
    rw [hx0 x]
    simp [quadForm]
  obtain ⟨xmin, hxmin, hmin⟩ := hSc.exists_isMinOn hne (continuous_quadForm M).continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hSc.exists_isMaxOn hne (continuous_quadForm M).continuousOn
  have hxmin0 : xmin ≠ 0 := fun h => by
    have : xmin ⬝ᵥ xmin = 1 := hxmin
    rw [h] at this; simp at this
  have ha : 0 < quadForm M xmin := by
    have := hM.dotProduct_mulVec_pos hxmin0
    simpa [quadForm] using this
  refine ⟨quadForm M xmin, quadForm M xmax, ha, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp [quadForm]
  have hy := (hscale x hx).1
  have hpos := (hscale x hx).2
  rw [hq x hx]
  have h1 := mul_le_mul_of_nonneg_left (hmin hy) hpos.le
  have h2 := mul_le_mul_of_nonneg_left (hmax hy) hpos.le
  exact ⟨by linarith, by linarith⟩

/-- A form with square-integrable coordinates is integrable: `q_M(w) = Σᵢⱼ Mᵢⱼ wᵢ wⱼ`. -/
theorem integrable_quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {μ : Measure (Fin n → ℝ)}
    (h2 : ∀ i j, Integrable (fun w => w i * w j) μ) : Integrable (quadForm M) μ := by
  have e : quadForm M = fun w => ∑ i, ∑ j, M i j * (w i * w j) := by
    funext w
    simp only [quadForm, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (h2 i j).const_mul _

/-! ### The RCA model -/

/-- **(16.42)** (MT p. 416): for the RCA model with `E[W] = 0` and `Γ`, `W` independent,
`E[q_M(Φₖ₊₁) + 1 | Φₖ = x] = E[q_M((A + Γ)x)] + E[q_M(W)] + 1`. -/
theorem rca_lintegral_quadForm {n : ℕ} (ΓΓ : Measure (Matrix (Fin n) (Fin n) ℝ))
    [IsProbabilityMeasure ΓΓ] (ΓW : Measure (Fin n → ℝ)) [IsProbabilityMeasure ΓW]
    (A : Matrix (Fin n) (Fin n) ℝ) {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (hW1 : ∀ i, Integrable (fun w => w i) ΓW) (hW0 : ∀ i, ∫ w, w i ∂ΓW = 0)
    (hW2 : Integrable (quadForm M) ΓW) (x : Fin n → ℝ)
    (hG : Integrable (fun G => quadForm M ((A + G) *ᵥ x)) ΓΓ) :
    ∫⁻ y, ENNReal.ofReal (quadForm M y + 1) ∂rcaKernel ΓΓ ΓW A x =
      ENNReal.ofReal (∫ G, quadForm M ((A + G) *ᵥ x) ∂ΓΓ + ∫ w, quadForm M w ∂ΓW + 1) := by
  have hsym : Mᵀ = M := by
    have := hM.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hqm : Measurable (quadForm M) := (continuous_quadForm M).measurable
  have hfm : Measurable fun y => ENNReal.ofReal (quadForm M y + 1) :=
    (hqm.add_const 1).ennreal_ofReal
  rw [rcaKernel, recursionKernel_apply _ (measurable_rcaStep A),
    lintegral_map hfm (show Measurable fun w : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
      rcaStep A (x, w) from (measurable_rcaStep A).comp measurable_prodMk_left),
    lintegral_prod (fun z => ENNReal.ofReal (quadForm M (rcaStep A (x, z)) + 1))
      ((hfm.comp ((measurable_rcaStep A).comp measurable_prodMk_left)).aemeasurable)]
  set cW := ∫ w, quadForm M w ∂ΓW with hcW
  -- the inner integral over `W`
  have hinner : ∀ G : Matrix (Fin n) (Fin n) ℝ,
      ∫⁻ w, ENNReal.ofReal (quadForm M (rcaStep A (x, (G, w))) + 1) ∂ΓW =
        ENNReal.ofReal (quadForm M ((A + G) *ᵥ x) + cW + 1) := fun G => by
    obtain ⟨u, hu⟩ : ∃ u, u = (A + G) *ᵥ x := ⟨_, rfl⟩
    rw [← hu]
    have hexp : ∀ w, quadForm M (rcaStep A (x, (G, w))) + 1 =
        (quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j + quadForm M w := fun w => by
      rw [show rcaStep A (x, (G, w)) = u + w by rw [hu]; rfl, quadForm_add hsym,
        dotProduct_mulVec]
      simp only [dotProduct]
      ring
    have hlin : Integrable (fun w => ∑ j, (u ᵥ* M) j * w j) ΓW :=
      integrable_finsetSum _ fun j _ => (hW1 j).const_mul _
    have hlin0 : ∫ w, ∑ j, (u ᵥ* M) j * w j ∂ΓW = 0 := by
      rw [integral_finsetSum _ fun j _ => (hW1 j).const_mul _]
      exact Finset.sum_eq_zero fun j _ => by rw [integral_const_mul, hW0, mul_zero]
    have hint : Integrable (fun w => (quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j +
        quadForm M w) ΓW := ((integrable_const _).add (hlin.const_mul 2)).add hW2
    have hnn : 0 ≤ᵐ[ΓW] fun w => (quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j +
        quadForm M w := Eventually.of_forall fun w => by
      change (0 : ℝ) ≤ (quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j + quadForm M w
      rw [← hexp]; linarith [quadForm_nonneg hM (rcaStep A (x, (G, w)))]
    have h := ofReal_integral_eq_lintegral_ofReal hint hnn
    have hcongr : ∫⁻ w, ENNReal.ofReal (quadForm M (rcaStep A (x, (G, w))) + 1) ∂ΓW =
        ∫⁻ w, ENNReal.ofReal ((quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j +
          quadForm M w) ∂ΓW := lintegral_congr fun w => by rw [hexp w]
    rw [hcongr, ← h]
    congr 1
    have i1 : Integrable (fun w => (quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j) ΓW :=
      (integrable_const _).add (hlin.const_mul 2)
    have e1 : ∫ w, ((quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j + quadForm M w) ∂ΓW =
        ∫ w, ((quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j) ∂ΓW + ∫ w, quadForm M w ∂ΓW :=
      integral_add i1 hW2
    have e2 : ∫ w, ((quadForm M u + 1) + 2 * ∑ j, (u ᵥ* M) j * w j) ∂ΓW =
        ∫ _w, (quadForm M u + 1) ∂ΓW + ∫ w, 2 * ∑ j, (u ᵥ* M) j * w j ∂ΓW :=
      integral_add (integrable_const _) (hlin.const_mul 2)
    have e3 : ∫ w, 2 * ∑ j, (u ᵥ* M) j * w j ∂ΓW = 2 * ∫ w, ∑ j, (u ᵥ* M) j * w j ∂ΓW :=
      integral_const_mul _ _
    have e4 : ∫ _w, (quadForm M u + 1) ∂ΓW = quadForm M u + 1 := by
      rw [integral_const, probReal_univ, one_smul]
    rw [e1, e2, e3, hlin0, e4, ← hcW]
    ring
  simp_rw [hinner]
  have hc0 : 0 ≤ cW := integral_nonneg fun w => quadForm_nonneg hM w
  have hGi : Integrable (fun G => quadForm M ((A + G) *ᵥ x) + cW + 1) ΓΓ :=
    (hG.add (integrable_const _)).add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal hGi
    (Eventually.of_forall fun G => by
      change (0 : ℝ) ≤ quadForm M ((A + G) *ᵥ x) + cW + 1
      have := quadForm_nonneg hM ((A + G) *ᵥ x)
      linarith)]
  rw [integral_add (f := fun G => quadForm M ((A + G) *ᵥ x) + cW) (g := fun _ => (1 : ℝ))
      (hG.add (integrable_const _)) (integrable_const _),
    integral_add (f := fun G => quadForm M ((A + G) *ᵥ x)) (g := fun _ => cW) hG
      (integrable_const _), integral_const, integral_const, probReal_univ, one_smul, one_smul]

/-- `{x | x ⬝ x ≤ c}` is compact. -/
theorem isCompact_dotProduct_le {n : ℕ} (c : ℝ) :
    IsCompact {x : Fin n → ℝ | x ⬝ᵥ x ≤ c} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) continuous_const)
    ((Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := Real.sqrt (max c 0))).subset
      fun x hx => ?_)
  have hx' : x ⬝ᵥ x ≤ c := hx
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have : x i ^ 2 ≤ x ⬝ᵥ x := by
    rw [dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), sq]
    have : 0 ≤ ∑ j ∈ Finset.univ.erase i, x j * x j :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    linarith
  linarith [le_max_left c 0]

/-- The squared Euclidean norm `|x|² = x ⬝ x` is nonnegative. -/
theorem dotProduct_self_nonneg' {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- **Theorem 16.5.1** (MT p. 415): for the multidimensional RCA model (16.38) with `E[W] = 0`,
`E[WWᵀ]` finite, and positive definite `M`, `N` satisfying (16.41),
`E[xᵀ(A + Γ)ᵀ M (A + Γ)x] = xᵀMx − xᵀNx` (the results of [299] quoted in the proof), if the chain
is `ψ`-irreducible and aperiodic with compact sets petite, then it is positive and
`V`-uniformly ergodic for `V(x) = |x|² + 1`: every invariant probability `μ` has
`∫ |x|² dμ < ∞` (a second-order stationary version exists) and
`|||Pᵏ − 1 ⊗ μ|||_V ≤ R r⁻ᵏ` for some `r > 1`, `R < ∞`. -/
theorem theorem_16_5_1 {n : ℕ} (ΓΓ : Measure (Matrix (Fin n) (Fin n) ℝ))
    [IsProbabilityMeasure ΓΓ] (ΓW : Measure (Fin n → ℝ)) [IsProbabilityMeasure ΓW]
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hW1 : ∀ i, Integrable (fun w => w i) ΓW) (hW0 : ∀ i, ∫ w, w i ∂ΓW = 0)
    (hW2 : ∀ i j, Integrable (fun w => w i * w j) ΓW)
    {M N : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) (hN : N.PosDef)
    (h41i : ∀ x, Integrable (fun G => quadForm M ((A + G) *ᵥ x)) ΓΓ)
    (h41 : ∀ x, ∫ G, quadForm M ((A + G) *ᵥ x) ∂ΓΓ = quadForm M x - quadForm N x)
    {ψ : Measure (Fin n → ℝ)}
    (hψ : haveI := isMarkovKernel_rcaKernel ΓΓ ΓW A
      IsMaximalIrreducibility (rcaKernel ΓΓ ΓW A) ψ)
    (hap : IsAperiodic (rcaKernel ΓΓ ΓW A) ψ)
    (hcpt : ∀ K, IsCompact K → IsPetite (rcaKernel ΓΓ ΓW A) K) :
    haveI := isMarkovKernel_rcaKernel ΓΓ ΓW A
    IsPositive (rcaKernel ΓΓ ΓW A) ψ ∧
      ∀ (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ],
        IsInvariant (rcaKernel ΓΓ ΓW A) μ →
        ∫⁻ x, ENNReal.ofReal (x ⬝ᵥ x) ∂μ ≠ ∞ ∧
        ∃ r : ℝ≥0∞, 1 < r ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ k,
          vErgDist (fun x => ENNReal.ofReal (x ⬝ᵥ x + 1)) (rcaKernel ΓΓ ΓW A) μ k ≤
            R * r⁻¹ ^ k := by
  have := isMarkovKernel_rcaKernel ΓΓ ΓW A
  set P := rcaKernel ΓΓ ΓW A with hP
  obtain ⟨aM, bM, haM, hbM⟩ := exists_quadForm_bounds hM
  obtain ⟨aN, _bN, haN, hNb⟩ := exists_quadForm_bounds hN
  have hdd := dotProduct_self_nonneg' (n := n)
  set bM' := max bM 1 with hbM'
  have hbM'0 : 0 < bM' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMub : ∀ x, quadForm M x ≤ bM' * (x ⬝ᵥ x) := fun x =>
    (hbM x).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hdd x))
  have hqM0 : ∀ x, 0 ≤ quadForm M x := quadForm_nonneg hM.posSemidef
  set ε := min (aN / bM') (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (div_pos haN hbM'0) (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hNM : ∀ x, ε * quadForm M x ≤ quadForm N x := fun x => by
    calc ε * quadForm M x ≤ aN / bM' * quadForm M x :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (hqM0 x)
      _ ≤ aN / bM' * (bM' * (x ⬝ᵥ x)) :=
          mul_le_mul_of_nonneg_left (hMub x) (div_pos haN hbM'0).le
      _ = aN * (x ⬝ᵥ x) := by field_simp
      _ ≤ quadForm N x := (hNb x).1
  set cW := ∫ w, quadForm M w ∂ΓW with hcW
  have hcW0 : 0 ≤ cW := integral_nonneg hqM0
  have hW2' := integrable_quadForm M hW2
  -- the drift for `V₀(x) = q_M(x) + 1`
  set V₀ : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (quadForm M x + 1) with hV₀
  have hV₀m : Measurable V₀ := ((continuous_quadForm M).measurable.add_const 1).ennreal_ofReal
  have hV₀1 : ∀ x, 1 ≤ V₀ x := fun x => by
    rw [hV₀, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [hqM0 x])
  have hPV : ∀ x, ∫⁻ y, V₀ y ∂P x ≤ ENNReal.ofReal (1 - ε) * V₀ x + ENNReal.ofReal (ε + cW) :=
    fun x => by
      rw [hP, hV₀, rca_lintegral_quadForm ΓΓ ΓW A hM.posSemidef hW1 hW0 hW2' x (h41i x), h41 x,
        ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by nlinarith [hqM0 x])
          (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [hNM x]
  have hU : IsUnboundedOffPetite P V₀ := fun ℓ hℓ => by
    obtain ⟨a, ν, -, ha, hν, hle⟩ := hcpt _ (isCompact_dotProduct_le (ℓ.toReal / aM))
    refine ⟨a, ν, measurableSet_le hV₀m measurable_const, ha, hν, fun x hx => hle x ?_⟩
    have hx' : V₀ x ≤ ℓ := hx
    have h1 : quadForm M x + 1 ≤ ℓ.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hℓ).1 hx'
    change x ⬝ᵥ x ≤ ℓ.toReal / aM
    rw [le_div_iff₀ haM]
    nlinarith [(hbM x).1]
  obtain ⟨ρ, b, hρ, hb, C, hC, hd⟩ := (lemma_15_2_8 hV₀m hV₀1).2 ⟨hU, _, _,
    ENNReal.ofReal_lt_one.2 (by linarith), ENNReal.ofReal_ne_top, hPV⟩
  -- the equivalence of `V₀` and `V`
  set V : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (x ⬝ᵥ x + 1) with hV
  have hVm : Measurable V := ((by fun_prop : Continuous fun x : Fin n → ℝ =>
    x ⬝ᵥ x).measurable.add_const 1).ennreal_ofReal
  have hV1 : ∀ x, 1 ≤ V x := fun x => by
    rw [hV, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [hdd x])
  have hVt : ∀ x, V x ≠ ∞ := fun x => ENNReal.ofReal_ne_top
  set c : ℝ := max bM' (aM⁻¹ + 1) with hc
  have hc1 : 1 ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hequiv : ∀ x, V x ≤ ENNReal.ofReal c * V₀ x ∧ V₀ x ≤ ENNReal.ofReal c * V x := fun x => by
    rw [hV, hV₀, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith)]
    have h1 : x ⬝ᵥ x ≤ aM⁻¹ * quadForm M x := by
      rw [le_inv_mul_iff₀ haM]; exact (hbM x).1
    have hc2 : aM⁻¹ + 1 ≤ c := le_max_right _ _
    have hc3 : bM' ≤ c := le_max_left _ _
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
    · nlinarith [hqM0 x, hdd x, inv_pos.2 haM]
    · nlinarith [hMub x, hdd x]
  have key := (theorem_16_0_1 hψ hap hVm hV1 hVt)
  refine ⟨(geometric_ergodic_of_driftV4 hψ hap hV₀m hV₀1 hρ hb hC hd
    (x₀ := 0) ENNReal.ofReal_ne_top).1, fun μ _ hμ => ?_⟩
  have key2 := (key μ hμ).out 4 2
  have h2 := key2.1 ⟨V₀, hV₀m, hV₀1, ENNReal.ofReal c, ENNReal.ofReal_ne_top,
    hequiv, ρ, b, hρ, hb, C, hC, hd⟩
  obtain ⟨r, hr, R, hR, hbd⟩ := h2
  refine ⟨?_, r, hr, R, hR, hbd⟩
  have h0 : vErgDist V P μ 0 ≠ ∞ := ne_top_of_le_ne_top (by simpa using hR) (hbd 0)
  have hμV := lintegral_ne_top_of_vErgDist_zero hVm hV1 (hVt 0) P μ h0
  exact ne_top_of_le_ne_top hμV (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (by linarith))

end MeynTweedie.Epilogue
