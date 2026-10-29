/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.ControlModel
import InvarianceTightness.LinearControllability
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Forward accessibility and the rank condition (MT §7.1.1, §7.1.4)

Meyn and Tweedie, §7.1.1, pp. 147–148, and §7.1.4, pp. 152–153. The state space `X` and the
control space `W` are real normed spaces (finite-dimensional where the rank condition is used);
`F : X × W → X` and the controls range over `O ⊆ W`.

* `dxF F x w = Ξ` and `duF F x w = Λ`: the derivatives `∂F/∂x` and `∂F/∂u` at `(x, w)`.
* `genCtrb F k x u = C_x^k(u)` (MT (7.11), p. 153): the generalized controllability matrix, as a
  linear map `(v₁, …, vₖ) ↦ Σᵢ Ξₖ ⋯ Ξᵢ₊₁ Λᵢ vᵢ`, built by the recursion
  `C^{k+1}(v) = Ξₖ₊₁ C^k(v₁, …, vₖ) + Λₖ₊₁ vₖ₊₁`.
* `hasFDerivAt_controlMap` (MT p. 153, "the controllability matrix is the derivative of the
  state with respect to the input sequence"): `C_x^k(u)` is the derivative of `u ↦ Fₖ(x, u)`.
  `contDiff_controlMap`: the control maps are `Cⁿ` jointly when `F` is, and
  `fderiv_controlMap_comp_inr` identifies the partial derivative in `u`.
* `sensitivity F k x u = ∇Φₖ` (MT (7.26), p. 163): `∇Φ₀ = I`, `∇Φₖ₊₁ = Ξₖ₊₁ ∇Φₖ`, and
  `hasFDerivAt_controlMap_left`: it is the derivative of `Fₖ(·, u)` (MT p. 163).
* `genCtrb_linear` (MT (7.12), p. 153): for `F(x, u) = A x + B u` the generalized controllability
  matrix is the controllability matrix `[A^{k−1}B | ⋯ | B]` of (LCM3) (`ctrbMap`).
* `HasFullRankAt`, `RankCondition` (MT (CM3), (7.13), p. 153; (CM2), (7.4), p. 148 in the scalar
  case): for each `x` some `C_x^k(u)`, `u ∈ Oᵏ`, `k ≥ 1`, is onto, i.e. has rank `n`
  (`surjective_iff_finrank_range`; in the scalar case, is non-zero, `surjective_iff_ne_zero`).
* **Proposition 7.1.4** (p. 153): `proposition_7_1_4_of_rank`, the rank condition implies forward
  accessibility (open mapping theorem for `C¹` maps with onto derivative); and
  `proposition_7_1_4_of_forwardAccessible`, forward accessibility implies the rank condition when
  the critical values of each `Fₖ(x, ·)` on `Oᵏ` are Lebesgue-null (`CriticalValuesNull`).
* **Theorem 7.1.1** (p. 148): for the scalar model (`X = ℝ`) forward accessibility is equivalent to
  (CM2) (`theorem_7_1_1`), for `C¹` maps, with no Sard hypothesis: when every `C_x^k(u)` vanishes
  the maps `Fₖ(x, ·)` are locally constant on `Oᵏ`, so `A₊(x)` is countable
  (`countable_image_of_hasFDerivAt_zero`).

**Hypotheses.** The book takes `F` smooth (`C^∞`). Everything here uses only `C¹`. The "only if"
half of Proposition 7.1.4 is, in the book, a consequence of Sard's theorem for the maps
`Fₖ(x, ·) : Oᵏ → X`, whose domain dimension `kp` exceeds `n` for large `k`. Mathlib has Sard's
lemma only in equal dimension (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) and for a
lower-dimensional domain, so this half takes the conclusion of Sard's theorem, that the critical
values are null, as the explicit hypothesis `CriticalValuesNull`. The scalar case needs no such
hypothesis. In the book's (CM3) `k ∈ ℤ₊` may be `0`; here `k ≥ 1`, which loses nothing (on a
non-trivial space `C⁰ = 0` is not onto, and on the trivial space every `C^k` is onto).
-/

namespace MeynTweedie.InvarianceTightness

open Set Filter Topology MeasureTheory
open scoped Matrix

variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-! ### The generalized controllability matrix -/

/-- `Ξ = ∂F/∂x` at `(x, w)` (MT p. 152). -/
noncomputable def dxF (F : X × W → X) (x : X) (w : W) : X →L[ℝ] X :=
  (fderiv ℝ F (x, w)).comp (ContinuousLinearMap.inl ℝ X W)

/-- `Λ = ∂F/∂u` at `(x, w)` (MT p. 152). -/
noncomputable def duF (F : X × W → X) (x : X) (w : W) : W →L[ℝ] X :=
  (fderiv ℝ F (x, w)).comp (ContinuousLinearMap.inr ℝ X W)

/-- The projection `(v₁, …, vₖ₊₁) ↦ (v₁, …, vₖ)` as a continuous linear map. -/
noncomputable def initCLM (k : ℕ) : (Fin (k + 1) → W) →L[ℝ] (Fin k → W) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) i.castSucc

/-- `initCLM k v = Fin.init v`. -/
theorem initCLM_apply (k : ℕ) (v : Fin (k + 1) → W) : initCLM k v = Fin.init v := rfl

/-- The **generalized controllability matrix** `C_x^k(u)` (MT (7.11), p. 153), as the linear map
`(v₁, …, vₖ) ↦ Σᵢ Ξₖ ⋯ Ξᵢ₊₁ Λᵢ vᵢ` along the trajectory `xᵢ = Fᵢ(x, u)`, defined by the recursion
`C^{k+1}(v) = Ξₖ₊₁ C^k(v₁, …, vₖ) + Λₖ₊₁ vₖ₊₁`. -/
noncomputable def genCtrb (F : X × W → X) : (k : ℕ) → X → (Fin k → W) → ((Fin k → W) →L[ℝ] X)
  | 0, _, _ => 0
  | k + 1, x, u =>
      (dxF F (controlMap F k x (Fin.init u)) (u (Fin.last k))).comp
          ((genCtrb F k x (Fin.init u)).comp (initCLM k)) +
        (duF F (controlMap F k x (Fin.init u)) (u (Fin.last k))).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) (Fin.last k))

/-- The recursion for `C_x^{k+1}(u)` (the block structure of (7.11)). -/
theorem genCtrb_succ_apply (F : X × W → X) (k : ℕ) (x : X) (u v : Fin (k + 1) → W) :
    genCtrb F (k + 1) x u v =
      dxF F (controlMap F k x (Fin.init u)) (u (Fin.last k))
          (genCtrb F k x (Fin.init u) (Fin.init v)) +
        duF F (controlMap F k x (Fin.init u)) (u (Fin.last k)) (v (Fin.last k)) := rfl

/-- `C_x^1(u) = Λ₁ = ∂F/∂u (x, u₁)` (the first order controllability vector, MT p. 152). -/
theorem genCtrb_one_apply (F : X × W → X) (x : X) (u v : Fin 1 → W) :
    genCtrb F 1 x u v = duF F x (u 0) (v 0) := by
  rw [genCtrb_succ_apply]
  simp [genCtrb]

/-- The derivative of `F` at `(a, b)` splits as `Ξ a' + Λ b'`. -/
theorem fderiv_apply_eq_dxF_add_duF (F : X × W → X) (x : X) (w : W) (a : X) (b : W) :
    fderiv ℝ F (x, w) (a, b) = dxF F x w a + duF F x w b := by
  rw [dxF, duF, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← map_add]
  simp

/-- **The controllability matrix is the derivative of the control map** (MT p. 153): for a
differentiable `F`, `u ↦ Fₖ(x, u)` has derivative `C_x^k(u)`. -/
theorem hasFDerivAt_controlMap {F : X × W → X} (hF : Differentiable ℝ F) (k : ℕ) (x : X)
    (u : Fin k → W) : HasFDerivAt (controlMap F k x) (genCtrb F k x u) u := by
  induction k with
  | zero =>
    have : controlMap F 0 x = fun _ => x := rfl
    rw [this]
    exact hasFDerivAt_const x u
  | succ k ih =>
    have h1 : HasFDerivAt (fun v : Fin (k + 1) → W => controlMap F k x (initCLM k v))
        ((genCtrb F k x (Fin.init u)).comp (initCLM k)) u :=
      (ih (Fin.init u)).comp u (initCLM (W := W) k).hasFDerivAt
    have h2 : HasFDerivAt (fun v : Fin (k + 1) → W => v (Fin.last k))
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) (Fin.last k)) u :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) (Fin.last k)).hasFDerivAt
    have h3 := ((hF _).hasFDerivAt).comp u (h1.prodMk h2)
    refine h3.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    rw [fderiv_apply_eq_dxF_add_duF]
    rfl

/-- The control maps are jointly `Cⁿ` when `F` is. -/
theorem contDiff_controlMap {F : X × W → X} {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) (k : ℕ) :
    ContDiff ℝ n fun p : X × (Fin k → W) => controlMap F k p.1 p.2 := by
  induction k with
  | zero => exact contDiff_fst
  | succ k ih =>
    have hc : ContDiff ℝ n (⇑(initCLM (W := W) k) ∘ Prod.snd : X × (Fin (k + 1) → W) → _) :=
      (initCLM (W := W) k).contDiff.comp contDiff_snd
    have hi : ContDiff ℝ n fun p : X × (Fin (k + 1) → W) => (p.1, initCLM k p.2) :=
      contDiff_fst.prodMk hc
    have hl : ContDiff ℝ n fun p : X × (Fin (k + 1) → W) => p.2 (Fin.last k) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => W) (Fin.last k)).contDiff.comp
        contDiff_snd
    exact hF.comp ((ih.comp hi).prodMk hl)

/-- The partial derivative in the controls of the joint control map is `C_x^k(u)`. -/
theorem fderiv_controlMap_comp_inr {F : X × W → X} (hF : ContDiff ℝ 1 F) (k : ℕ) (x : X)
    (u : Fin k → W) :
    (fderiv ℝ (fun p : X × (Fin k → W) => controlMap F k p.1 p.2) (x, u)).comp
      (ContinuousLinearMap.inr ℝ X (Fin k → W)) = genCtrb F k x u := by
  have hD := ((contDiff_controlMap hF k).differentiable one_ne_zero (x, u)).hasFDerivAt
  have h1 := hD.comp u (hasFDerivAt_prodMk_right x u)
  exact h1.unique (hasFDerivAt_controlMap (hF.differentiable one_ne_zero) k x u)

/-! ### The sensitivity process -/

/-- The **sensitivity process** `∇Φₖ` along the controls `u` (MT (7.26), p. 163): `∇Φ₀ = I` and
`∇Φₖ₊₁ = Ξₖ₊₁ ∇Φₖ`, with `Ξₖ₊₁ = ∂F/∂x (xₖ, uₖ₊₁)`. -/
noncomputable def sensitivity (F : X × W → X) : (k : ℕ) → X → (Fin k → W) → (X →L[ℝ] X)
  | 0, _, _ => ContinuousLinearMap.id ℝ X
  | k + 1, x, u =>
      (dxF F (controlMap F k x (Fin.init u)) (u (Fin.last k))).comp
        (sensitivity F k x (Fin.init u))

/-- **The sensitivity process is the derivative of the state in the initial state** (MT p. 163):
`∇Φₖ = dΦₖ/dΦ₀`. -/
theorem hasFDerivAt_controlMap_left {F : X × W → X} (hF : Differentiable ℝ F) (k : ℕ) (x : X)
    (u : Fin k → W) :
    HasFDerivAt (fun y => controlMap F k y u) (sensitivity F k x u) x := by
  induction k generalizing x with
  | zero => exact hasFDerivAt_id x
  | succ k ih =>
    have h1 := ih x (Fin.init u)
    have h2 := ((hF _).hasFDerivAt).comp x (h1.prodMk (hasFDerivAt_const (u (Fin.last k)) x))
    refine h2.congr_fderiv ?_
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, zero_apply]
    rw [fderiv_apply_eq_dxF_add_duF, map_zero, add_zero]
    rfl

/-! ### The linear case (7.12) -/

/-- `∂/∂x` and `∂/∂u` of `F(x, u) = A x + B u` (on `ℝⁿ × ℝᵖ`). -/
theorem dxF_duF_linear {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (x : Fin n → ℝ) (w : Fin p → ℝ) :
    (∀ a, dxF (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) x w a = A *ᵥ a) ∧
      ∀ b, duF (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) x w b = B *ᵥ b := by
  set L : ((Fin n → ℝ) × (Fin p → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    (LinearMap.toContinuousLinearMap A.mulVecLin).coprod
      (LinearMap.toContinuousLinearMap B.mulVecLin)
  have hL : (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) = L := by
    funext q
    simp [L]
  have hd : fderiv ℝ (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) (x, w) = L := by
    rw [hL]
    exact L.fderiv
  refine ⟨fun a => ?_, fun b => ?_⟩
  · rw [dxF, hd]
    simp [L]
  · rw [duF, hd]
    simp [L]

/-- **The linear case** (MT (7.12), p. 153): for `F(x, u) = A x + B u` the generalized
controllability matrix is the controllability matrix `[A^{k−1}B | ⋯ | AB | B]` of (LCM3),
whatever the trajectory. -/
theorem genCtrb_linear {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (k : ℕ) (x : Fin n → ℝ) (u v : Fin k → Fin p → ℝ) :
    genCtrb (fun q : (Fin n → ℝ) × (Fin p → ℝ) => A *ᵥ q.1 + B *ᵥ q.2) k x u v =
      ctrbMap A B k v := by
  induction k with
  | zero => simp [genCtrb, ctrbMap]
  | succ k ih =>
    rw [genCtrb_succ_apply, (dxF_duF_linear A B _ _).1, (dxF_duF_linear A B _ _).2, ih,
      ctrbMap_apply, ctrbMap_apply, Fin.sum_univ_castSucc, Matrix.mulVec_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
      have hi : k - 1 - (i : ℕ) + 1 = k + 1 - 1 - ((Fin.castSucc i : Fin (k + 1)) : ℕ) := by
        simp only [Fin.val_castSucc]
        have := i.2
        omega
      rw [hi]
      rfl
    · simp

/-! ### The rank condition -/

/-- The rank condition holds at `x` with `k ≥ 1` steps and admissible controls `u ∈ Oᵏ`:
`C_x^k(u)` is onto (MT (7.13), p. 153; (7.4), p. 148). -/
def HasFullRankAt (F : X × W → X) (O : Set W) (x : X) (k : ℕ) (u : Fin k → W) : Prop :=
  0 < k ∧ (∀ i, u i ∈ O) ∧ Function.Surjective (genCtrb F k x u)

/-- The **rank condition** (CM3) (MT p. 153; (CM2), p. 148, in the scalar case): from each
initial condition, some `C_x^k(u)` with `u ∈ Oᵏ` is onto. -/
def RankCondition (F : X × W → X) (O : Set W) : Prop := ∀ x, ∃ k u, HasFullRankAt F O x k u

/-- A linear map onto a finite-dimensional space is onto iff its rank is the dimension (the form
`rank C_x^k = n` of (7.13)). -/
theorem surjective_iff_finrank_range {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ X] (L : E →ₗ[ℝ] X) :
    Function.Surjective L ↔ Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ X := by
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h; rw [h, finrank_top]
  · exact fun h => Submodule.eq_top_of_finrank_eq h

/-- A linear map to `ℝ` is onto iff it is non-zero: in the scalar case the rank condition says the
controllability vector (7.4) is non-zero. -/
theorem surjective_iff_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E] (L : E →ₗ[ℝ] ℝ) :
    Function.Surjective L ↔ L ≠ 0 := by
  constructor
  · intro h h0
    obtain ⟨v, hv⟩ := h 1
    rw [h0] at hv
    simp at hv
  · intro h t
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (LinearMap.ext hc)
    exact ⟨(t / L v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ t hv]⟩

/-- The image of the open set `Oᵏ` under `Fₖ(x, ·)` is a neighbourhood of every point at which
the rank condition holds (open mapping theorem for `C¹` maps). -/
theorem image_mem_nhds_of_hasFullRankAt [FiniteDimensional ℝ X] [FiniteDimensional ℝ W]
    {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O) {x : X} {k : ℕ}
    {u : Fin k → W} (h : HasFullRankAt F O x k u) :
    controlMap F k x '' {v | ∀ i, v i ∈ O} ∈ 𝓝 (controlMap F k x u) := by
  have hs : HasStrictFDerivAt (controlMap F k x) (genCtrb F k x u) u := by
    have hc : ContDiffAt ℝ 1 (controlMap F k x) u :=
      ((contDiff_controlMap hF k).comp (contDiff_const.prodMk contDiff_id)).contDiffAt
    have := hc.hasStrictFDerivAt one_ne_zero
    rwa [(hasFDerivAt_controlMap (hF.differentiable one_ne_zero) k x u).fderiv] at this
  rw [← hs.map_nhds_eq_of_surj (LinearMap.range_eq_top.2 h.2.2)]
  refine image_mem_map ?_
  have : {v : Fin k → W | ∀ i, v i ∈ O} = Set.pi univ fun _ => O := by
    ext v; simp
  rw [this]
  exact (isOpen_set_pi finite_univ fun _ _ => hO).mem_nhds (by simpa using h.2.1)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The image of `Oᵏ` under `Fₖ(x, ·)` is `A₊ᵏ(x)`. -/
theorem reachK_eq_image (F : X × W → X) (O : Set W) (k : ℕ) (x : X) :
    reachK F O k x = controlMap F k x '' {v | ∀ i, v i ∈ O} := by
  ext y
  simp [reachK]

/-- **Proposition 7.1.4**, "if" (MT p. 153): for `C¹` maps `F` and an open control set, the rank
condition (CM3) implies forward accessibility. -/
theorem proposition_7_1_4_of_rank [FiniteDimensional ℝ X] [FiniteDimensional ℝ W]
    {F : X × W → X} (hF : ContDiff ℝ 1 F) {O : Set W} (hO : IsOpen O) (h : RankCondition F O) :
    IsForwardAccessible F O := by
  intro x
  obtain ⟨k, u, hk⟩ := h x
  refine ⟨controlMap F k x u, mem_interior_iff_mem_nhds.2 ?_⟩
  refine mem_of_superset (image_mem_nhds_of_hasFullRankAt hF hO hk) ?_
  rw [← reachK_eq_image]
  exact reachK_subset_reach F O k x

/-- The conclusion of **Sard's theorem** for the control maps (the hypothesis of the "only if" half
of Proposition 7.1.4): for every `x` and `k`, the critical values of `Fₖ(x, ·)` on `Oᵏ` (images
of the controls at which `C_x^k` is not onto) form a `μ`-null set, `μ` a Haar (Lebesgue)
measure on `X`. -/
def CriticalValuesNull [MeasurableSpace X] (μ : Measure X) (F : X × W → X) (O : Set W) : Prop :=
  ∀ x k, μ (controlMap F k x ''
    {u | (∀ i, u i ∈ O) ∧ ¬ Function.Surjective (genCtrb F k x u)}) = 0

/-- **Proposition 7.1.4**, "only if" (MT p. 153): if the critical values of the control maps are
null (Sard's theorem, `CriticalValuesNull`), forward accessibility implies the rank condition. -/
theorem proposition_7_1_4_of_forwardAccessible [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddHaarMeasure] [FiniteDimensional ℝ X] [Nontrivial X] {F : X × W → X}
    {O : Set W} (hS : CriticalValuesNull μ F O) (h : IsForwardAccessible F O) :
    RankCondition F O := by
  intro x
  by_contra hc
  push Not at hc
  have hsub : reach F O x ⊆ {x} ∪ ⋃ k, controlMap F k x ''
      {u | (∀ i, u i ∈ O) ∧ ¬ Function.Surjective (genCtrb F k x u)} := by
    intro y hy
    obtain ⟨k, u, hu, rfl⟩ := mem_reach_iff.1 hy
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Or.inl rfl
    · exact Or.inr (mem_iUnion.2 ⟨k, u, ⟨hu, fun hs => hc k u ⟨hk, hu, hs⟩⟩, rfl⟩)
  have h0 : μ (reach F O x) = 0 :=
    measure_mono_null hsub (measure_union_null (measure_singleton x)
      (measure_iUnion_null fun k => hS x k))
  obtain ⟨y, hy⟩ := h x
  have hpos := isOpen_interior.measure_pos μ ⟨y, hy⟩
  exact hpos.ne' (measure_mono_null interior_subset h0)

/-! ### Theorem 7.1.1: the scalar model -/

/-- A map with zero derivative on an open subset of a second-countable normed space has a
countable image there (it is constant on balls). -/
theorem countable_image_of_hasFDerivAt_zero {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : E → Y} {s : Set E}
    (hs : IsOpen s) (hf : ∀ u ∈ s, HasFDerivAt f (0 : E →L[ℝ] Y) u) : (f '' s).Countable := by
  have hr : ∀ u : s, ∃ r > 0, Metric.ball (u : E) r ⊆ s := fun u =>
    Metric.isOpen_iff.1 hs u u.2
  choose r hr0 hrs using hr
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun u : s => Metric.ball (u : E) (r u)) fun u => Metric.isOpen_ball
  refine (hT.image fun u : s => f u).mono ?_
  rintro _ ⟨u, hu, rfl⟩
  have : u ∈ ⋃ i ∈ T, Metric.ball (i : E) (r i) := by
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨u, hu⟩, Metric.mem_ball_self (hr0 _)⟩
  obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 this
  refine ⟨i, hi, ?_⟩
  have hd : ∀ z ∈ Metric.ball (i : E) (r i), HasFDerivAt f (0 : E →L[ℝ] Y) z :=
    fun z hz => hf z (hrs i hz)
  exact (convex_ball _ _).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz]; exact (hd z hz).fderiv)
    (Metric.mem_ball_self (hr0 i)) hui

/-- **Theorem 7.1.1** (MT p. 148): for the scalar control model (`X = ℝ`) with a `C¹` map `F` and
an open control set, CM(F) is forward accessible iff the rank condition (CM2) holds: some
controllability vector `[∂Fₖ/∂u₁ | ⋯ | ∂Fₖ/∂uₖ]` (7.4) at admissible controls is non-zero. The
book omits the proof; here the "only if" half needs no Sard theorem. -/
theorem theorem_7_1_1 [FiniteDimensional ℝ W] {F : ℝ × W → ℝ} (hF : ContDiff ℝ 1 F) {O : Set W}
    (hO : IsOpen O) : IsForwardAccessible F O ↔ RankCondition F O := by
  refine ⟨fun h x => ?_, proposition_7_1_4_of_rank hF hO⟩
  by_contra hc
  push Not at hc
  have hzero : ∀ k (u : Fin k → W), (∀ i, u i ∈ O) → genCtrb F k x u = 0 := by
    intro k u hu
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rfl
    · by_contra hne
      refine hc k u ⟨hk, hu, ?_⟩
      have := (surjective_iff_ne_zero (genCtrb F k x u : (Fin k → W) →ₗ[ℝ] ℝ)).2
        (fun h0 => hne (ContinuousLinearMap.coe_injective h0))
      exact this
  have hcount : (reach F O x).Countable := by
    refine countable_iUnion fun k => ?_
    rw [reachK_eq_image]
    have hopen : IsOpen {v : Fin k → W | ∀ i, v i ∈ O} := by
      have : {v : Fin k → W | ∀ i, v i ∈ O} = Set.pi univ fun _ => O := by ext v; simp
      rw [this]
      exact isOpen_set_pi finite_univ fun _ _ => hO
    refine countable_image_of_hasFDerivAt_zero hopen fun u hu => ?_
    have := hasFDerivAt_controlMap (hF.differentiable one_ne_zero) k x u
    rwa [hzero k u hu] at this
  obtain ⟨y, hy⟩ := h x
  have hpos := isOpen_interior.measure_pos (volume : Measure ℝ) ⟨y, hy⟩
  exact hpos.ne' (measure_mono_null interior_subset (hcount.measure_zero _))

end MeynTweedie.InvarianceTightness
