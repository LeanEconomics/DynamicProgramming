/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.BoundedMonotone
import StochasticApplications.InteriorPoints
import StochasticApplications.Envelope

/-!
# Bounded returns: concavity, policy functions, differentiability

SLP §9.2, pp. 264–267 and 269–270: Theorems 9.8–9.10 and Exercises 9.7d–f. The endogenous
state space is a convex set `X ⊆ ℝˡ` and the action space a convex set `Y ⊆ ℝᵐ` (Assumptions 9.4
and 9.16); `θx + (1 − θ)x′` is `cmb`.

* Assumption 9.10 (`Assumption910`: `F(·, ·, z)` concave on `A_z`, strictly when `x ≠ x′`) and
  Assumption 9.11 (`Assumption911`: `A_z` convex).
* **Exercise 9.7d** (`ex_9_7d`): if `φ(·, ·, z′)` is affine (`IsAffineφ`), `v(·, z)` is strictly
  concave. **Correction:** the solutions manual asserts this for `φ(·, ·, z′)` concave; then
  `f[φ(x, y, z′), z′]` is concave only if `f` is also nondecreasing in `x`, so the hypotheses of
  part (c) are needed as well (`ex_9_7d_concave`, which runs the contraction on the closed set of
  functions concave and nondecreasing in `x`). **Second correction:** that `G` is single-valued
  does not follow from Assumption 9.10, which is strict only in `x`: if neither `F` nor `φ`
  depends on `y`, every feasible `y` is optimal. We add that `φ(x, ·, z′)` is one-to-one
  (`ex_9_7d_policy`); in the first formulation `φ(x, y, z′) = y` is.
* **Theorem 9.8** (`theorem_9_8`): the first formulation; `v(·, z)` strictly concave and `G` a
  continuous single-valued function.
* **Exercise 9.7e** and **Theorem 9.9** (`ex_9_7e`, `theorem_9_9`): from a concave `v₀`, the
  policy functions of `vₙ = Tⁿv₀` converge to `g` pointwise, uniformly if `S` is compact.
* **Exercise 9.7f** and **Theorem 9.10** (`ex_9_7f`, `theorem_9_10`): if `φ` does not depend on
  `x`, `x₀ ∈ int X`, `g(x₀, z₀) ∈ int Γ(x₀, z₀)` and `F(·, g(x₀, z₀), z₀)` is differentiable at
  `x₀` (Assumption 9.12), then `v(·, z₀)` is differentiable at `x₀` with
  `vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]` (Benveniste–Scheinkman, Theorem 4.10).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- `θx + (1 − θ)x′` in the convex set `S`. -/
def cmb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} (hS : Convex ℝ S)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x x' : S) : S :=
  ⟨θ • x.1 + (1 - θ) • x'.1, hS x.2 x'.2 h0 (by linarith) (by ring)⟩

theorem cmb_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : S) : cmb hS h0 h1 x x = x := by
  ext1; simp only [cmb]; rw [← add_smul]; simp

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {SX : Set E} {SY : Set E'}

/-- `f` is concave on `S`. -/
def IsConcaveS (hS : Convex ℝ SX) (f : SX → ℝ) : Prop :=
  ∀ x x' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), θ * f x + (1 - θ) * f x' ≤ f (cmb hS h0 h1 x x')

/-- `f` is strictly concave on `S`. -/
def IsStrictConcaveS (hS : Convex ℝ SX) (f : SX → ℝ) : Prop :=
  ∀ x x', x ≠ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * f x + (1 - θ) * f x' < f (cmb hS h0.le h1.le x x')

/-- A strictly concave function is concave. -/
theorem IsStrictConcaveS.isConcaveS {hS : Convex ℝ SX} {f : SX → ℝ}
    (hf : IsStrictConcaveS hS f) : IsConcaveS hS f := by
  intro x x' θ h0 h1
  rcases eq_or_ne x x' with rfl | hne
  · rw [cmb_self]; linarith
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (hf x x' hne θ h0' h1').le

variable [MeasurableSpace E] [MeasurableSpace E']
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]

/-- **Assumption 9.10.** For each `z`, `F(·, ·, z)` is concave on `A_z`, strictly if `x ≠ x′`. -/
def Assumption910 (hX : Convex ℝ SX) (hY : Convex ℝ SY) (M : Model SX SY Z) : Prop :=
  ∀ z x y x' y', y ∈ M.Γ (x, z) → y' ∈ M.Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * M.F (x, y, z) + (1 - θ) * M.F (x', y', z) ≤
      M.F (cmb hX h0.le h1.le x x', cmb hY h0.le h1.le y y', z) ∧
    (x ≠ x' → θ * M.F (x, y, z) + (1 - θ) * M.F (x', y', z) <
      M.F (cmb hX h0.le h1.le x x', cmb hY h0.le h1.le y y', z))

/-- **Assumption 9.11.** For each `z`, `A_z` is convex. -/
def Assumption911 (hX : Convex ℝ SX) (hY : Convex ℝ SY) (M : Model SX SY Z) : Prop :=
  ∀ z x y x' y', y ∈ M.Γ (x, z) → y' ∈ M.Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    cmb hY h0 h1 y y' ∈ M.Γ (cmb hX h0 h1 x x', z)

/-- `φ(·, ·, z′)` is affine. -/
def IsAffineφ (hX : Convex ℝ SX) (hY : Convex ℝ SY) (M : Model SX SY Z) : Prop :=
  ∀ x y x' y' z' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z') =
      cmb hX h0 h1 (M.φ (x, y, z')) (M.φ (x', y', z'))

variable {hX : Convex ℝ SX} {hY : Convex ℝ SY}

omit [MeasurableSpace E] [MeasurableSpace E'] [MeasurableSpace Z] in
/-- The functions concave in `x` form a closed subset of `C(S)`. -/
theorem isClosed_concaveX (hX : Convex ℝ SX) :
    IsClosed {f : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => f (x, z)} := by
  have : {f : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => f (x, z)} =
      ⋂ z, ⋂ x, ⋂ x', ⋂ θ : ℝ, ⋂ h0 : 0 ≤ θ, ⋂ h1 : θ ≤ 1,
        {f : SX × Z →ᵇ ℝ | θ * f (x, z) + (1 - θ) * f (x', z) ≤ f (cmb hX h0 h1 x x', z)} := by
    ext f; simp [IsConcaveS]
  rw [this]
  refine isClosed_iInter fun z => isClosed_iInter fun x => isClosed_iInter fun x' =>
    isClosed_iInter fun θ => isClosed_iInter fun h0 => isClosed_iInter fun h1 =>
      isClosed_le ?_ (continuous_eval_const _)
  exact (continuous_const.mul (continuous_eval_const _)).add
    (continuous_const.mul (continuous_eval_const _))

variable (M : Model SX SY Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- **Concavity passes through the integral** (Lemma 9.5): with `φ` affine and `f(·, z′)`
concave, `θ E₀ + (1 − θ) E₁ ≤ E_θ` for the expected continuation values. -/
theorem expV_comb (h : BoundedDP M) (haff : IsAffineφ hX hY M) {f : SX × Z →ᵇ ℝ}
    (hf : ∀ z, IsConcaveS hX fun x => f (x, z)) {x x' : SX} {y y' : SY} {z : Z}
    (hy : y ∈ M.Γ (x, z)) (hy' : y' ∈ M.Γ (x', z)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hyθ : cmb hY h0 h1 y y' ∈ M.Γ (cmb hX h0 h1 x x', z)) :
    θ * expV M f (x, z) y + (1 - θ) * expV M f (x', z) y' ≤
      expV M f (cmb hX h0 h1 x x', z) (cmb hY h0 h1 y y') := by
  have i0 := integrable_integrand M h f hy z
  have i1 := integrable_integrand M h f hy' z
  have iθ := integrable_integrand M h f hyθ z
  simp only [expV]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  refine integral_mono ((i0.const_mul θ).add (i1.const_mul _)) iθ fun z' => ?_
  change θ * f (M.φ (x, y, z'), z') + (1 - θ) * f (M.φ (x', y', z'), z') ≤
    f (M.φ (cmb hX h0 h1 x x', cmb hY h0 h1 y y', z'), z')
  rw [haff]
  exact hf z' _ _ θ h0 h1

/-- The strict version: with `f(·, z′)` strictly concave and `φ(x, y, z′) ≠ φ(x′, y′, z′)`. -/
theorem expV_comb_strict (h : BoundedDP M) (haff : IsAffineφ hX hY M) {f : SX × Z →ᵇ ℝ}
    (hf : ∀ z, IsStrictConcaveS hX fun x => f (x, z)) {x x' : SX} {y y' : SY} {z : Z}
    (hy : y ∈ M.Γ (x, z)) (hy' : y' ∈ M.Γ (x', z)) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hyθ : cmb hY h0.le h1.le y y' ∈ M.Γ (cmb hX h0.le h1.le x x', z))
    (hne : ∀ z', M.φ (x, y, z') ≠ M.φ (x', y', z')) :
    θ * expV M f (x, z) y + (1 - θ) * expV M f (x', z) y' <
      expV M f (cmb hX h0.le h1.le x x', z) (cmb hY h0.le h1.le y y') := by
  have i0 := integrable_integrand M h f hy z
  have i1 := integrable_integrand M h f hy' z
  have iθ := integrable_integrand M h f hyθ z
  simp only [expV]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  refine integral_lt_integral_of_lt ((i0.const_mul θ).add (i1.const_mul _)) iθ fun z' => ?_
  change θ * f (M.φ (x, y, z'), z') + (1 - θ) * f (M.φ (x', y', z'), z') <
    f (M.φ (cmb hX h0.le h1.le x x', cmb hY h0.le h1.le y y', z'), z')
  rw [haff]
  exact hf z' _ _ (hne z') θ h0 h1

omit [OpensMeasurableSpace Z] in
/-- `T` maps `f` to a function strictly concave in `x`, given the concavity inequality for the
expected continuation values of `f` (Lemma 9.5; `expV_comb` when `φ` is affine). -/
theorem bellman_maps_concave (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) {f : SX × Z →ᵇ ℝ}
    (hE : ∀ x x' y y' z, y ∈ M.Γ (x, z) → y' ∈ M.Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 ≤ θ)
      (h1 : θ ≤ 1), θ * expV M f (x, z) y + (1 - θ) * expV M f (x', z) y' ≤
        expV M f (cmb hX h0 h1 x x', z) (cmb hY h0 h1 y y')) (z : Z) :
    IsStrictConcaveS hX fun x => bellman M h f (x, z) := by
  intro x₀ x₁ hne θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M h f (x₀, z)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M h f (x₁, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h f (cmb hX h0.le h1.le x₀ x₁, z)
  have hyθ := h911 z x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0.le h1.le
  have hF := (h910 z x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0 h1).2 hne
  have hE' := mul_le_mul_of_nonneg_left (hE x₀ x₁ y₀ y₁ z hy₀ hy₁ θ h0.le h1.le) h.β_pos.le
  have hm := hmax _ hyθ
  simp only [rhs] at hv₀ hv₁ hm
  dsimp only at hv₀ hv₁ hm ⊢
  rw [hv₀, hv₁]
  nlinarith

/-- **Exercise 9.7d** (`φ(·, ·, z′)` affine). The fixed point `v(·, z)` is strictly concave. -/
theorem ex_9_7d (h : BoundedDP M) (h910 : Assumption910 hX hY M) (h911 : Assumption911 hX hY M)
    (haff : IsAffineφ hX hY M) {v : SX × Z →ᵇ ℝ} (hv : bellman M h v = v) (z : Z) :
    IsStrictConcaveS hX fun x => v (x, z) := by
  have hmaps := fun (f : SX × Z →ᵇ ℝ) (hf : ∀ z, IsConcaveS hX fun x => f (x, z)) =>
    bellman_maps_concave M h h910 h911 (f := f) fun x x' y y' z hy hy' θ h0 h1 =>
      expV_comb M h haff hf hy hy' h0 h1 (h911 z x y x' y' hy hy' θ h0 h1)
  exact (corollary_1 (S' := {f : SX × Z →ᵇ ℝ | ∀ z, IsConcaveS hX fun x => f (x, z)})
    (S'' := {f | ∀ z, IsStrictConcaveS hX fun x => f (x, z)}) (bellman_contraction M h) hv
    ⟨0, fun _ _ _ _ _ _ => by simp⟩ (isClosed_concaveX hX)
    (fun f hf z => (hmaps f hf z).isConcaveS) hmaps).2 z

/-- With `w(·, z′)` strictly concave and `φ(x, ·, z′)` one-to-one, the objective
`F(x, y, z) + β ∫ w[φ(x, y, z′), z′] Q(z, dz′)` has at most one maximizer on `Γ(x, z)`. -/
theorem argmax_unique_of_strictConcave (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {w : SX × Z →ᵇ ℝ}
    (hw : ∀ z, IsStrictConcaveS hX fun x => w (x, z)) :
    ∀ s, ∀ y₁ ∈ argmax (objG M w) M.Γ s, ∀ y₂ ∈ argmax (objG M w) M.Γ s, y₁ = y₂ := by
  rintro ⟨x, z⟩ y₁ hy₁ y₂ hy₂
  by_contra hne
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hmem := h911 z x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh.le hh1.le
  have hF := (h910 z x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh hh1).1
  have hE := expV_comb_strict M h haff hw hy₁.1 hy₂.1 hh hh1 hmem
    fun z' => hinj x y₁ y₂ z' hne
  rw [cmb_self] at hmem hF hE
  have hle := le_maxValue (continuousOn_objG M h w) (h.compact (x, z)) hmem
  have e1 := hy₁.2
  have e2 := hy₂.2
  simp only [objG, rhs] at hle e1 e2
  nlinarith [h.β_pos]

/-- **Exercise 9.7d** (`G` single-valued and continuous), when `φ(x, ·, z′)` is one-to-one. -/
theorem ex_9_7d_policy [Nonempty SY] (h : BoundedDP M) (h910 : Assumption910 hX hY M)
    (h911 : Assumption911 hX hY M) (haff : IsAffineφ hX hY M)
    (hinj : ∀ x y y' z', y ≠ y' → M.φ (x, y, z') ≠ M.φ (x, y', z')) {v : SX × Z →ᵇ ℝ}
    (hv : bellman M h v = v) :
    UniqueArgmax M.Γ (objG M v) ∧ (∀ s, policy M v s = {argmaxFn M.Γ (objG M v) s}) ∧
      Continuous (argmaxFn M.Γ (objG M v)) := by
  have huniq := argmax_unique_of_strictConcave M h h910 h911 haff hinj
    (ex_9_7d M h h910 h911 haff hv)
  have hU : UniqueArgmax M.Γ (objG M v) :=
    ⟨h.nonempty, h.compact, h.lhc, h.uhc, continuousOn_objG M h v, huniq⟩
  refine ⟨hU, fun s => ?_, hU.continuous_argmaxFn⟩
  rw [policy_eq_argmax M h hv]
  exact hU.argmax_eq s

/-- **Theorem 9.8** (first formulation). Under Assumptions 9.4–9.7 and 9.10–9.11, `v(·, z)` is
strictly concave for each `z`, and `G` is a continuous single-valued function. -/
theorem theorem_9_8 [Nonempty SX] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : SX × Z → Set SX)
    (F : SX × SX × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h910 : Assumption910 hX hX (Model.first Q Γ F β))
    (h911 : Assumption911 hX hX (Model.first Q Γ F β)) {v : SX × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) :
    (∀ z, IsStrictConcaveS hX fun x => v (x, z)) ∧
      (∀ s, policy (Model.first Q Γ F β) v s =
        {argmaxFn Γ (objG (Model.first Q Γ F β) v) s}) ∧
      Continuous (argmaxFn Γ (objG (Model.first Q Γ F β) v)) := by
  have haff : IsAffineφ hX hX (Model.first Q Γ F β) := fun _ _ _ _ _ _ _ _ => rfl
  obtain ⟨-, h2, h3⟩ := ex_9_7d_policy (Model.first Q Γ F β) h h910 h911 haff
    (fun _ _ _ _ hne => hne) hv
  exact ⟨ex_9_7d (Model.first Q Γ F β) h h910 h911 haff hv, h2, h3⟩

end StokeyLucasPrescott.StochasticApplications
