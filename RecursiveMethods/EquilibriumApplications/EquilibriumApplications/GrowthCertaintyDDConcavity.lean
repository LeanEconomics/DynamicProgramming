/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyDDBoundedReturns

/-!
# Concavity and the policy function

Copied unchanged (apart from imports and the namespace `GrowthCertaintyDD`) from the Chapter 6
project `DeterministicDynamics` (module `DeterministicDynamics.Concavity`),
for Exercise 16.1(e)–(g).

SLP §4.2, pp. 80–82. The state space is a convex set `S` in a real normed space (the book's
`X ⊆ ℝˡ`); functions on it are concave along the combinations `θx + (1 − θ)x'` (`cmb`).

* `IsConcaveS`, `IsStrictConcaveS`: (strict) concavity on `S`.
* `Assumption47` (`F` concave on the graph, strictly in `x`), `Assumption48` (the graph of `Γ` is
  convex).
* `bellman_maps_concave`: `T` maps concave functions to strictly concave ones.
* `theorem_4_8`: the fixed point `v` is strictly concave, the policy correspondence is a
  single-valued function `g`, and `g` is continuous.
* `theorem_4_9`: from a concave `v₀`, the policy functions `gₙ` of `vₙ = Tⁿv₀` converge to `g`
  pointwise, and uniformly when `S` is compact.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

namespace GrowthCertaintyDD

open Set Filter Topology BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

/-- `θx + (1 − θ)x'` in the convex set `S`. -/
def cmb (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x x' : S) : S :=
  ⟨θ • x.1 + (1 - θ) • x'.1, hS x.2 x'.2 h0 (by linarith) (by ring)⟩

/-- Auxiliary result `cmb_self` of the copied Chapter 4–6 development. -/
theorem cmb_self (hS : Convex ℝ S) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : S) :
    cmb hS h0 h1 x x = x := by
  ext1; simp only [cmb]; rw [← add_smul]; simp

/-- `f` is concave on `S`. -/
def IsConcaveS (hS : Convex ℝ S) (f : S → ℝ) : Prop :=
  ∀ x x' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), θ * f x + (1 - θ) * f x' ≤ f (cmb hS h0 h1 x x')

/-- `f` is strictly concave on `S`. -/
def IsStrictConcaveS (hS : Convex ℝ S) (f : S → ℝ) : Prop :=
  ∀ x x', x ≠ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * f x + (1 - θ) * f x' < f (cmb hS h0.le h1.le x x')

/-- **Assumption 4.7.** `F` is concave on the graph `A`, strictly when `x ≠ x'`. -/
def Assumption47 (hS : Convex ℝ S) (Γ : S → Set S) (F : S × S → ℝ) : Prop :=
  ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * F (x, y) + (1 - θ) * F (x', y') ≤ F (cmb hS h0.le h1.le x x', cmb hS h0.le h1.le y y') ∧
    (x ≠ x' →
      θ * F (x, y) + (1 - θ) * F (x', y') < F (cmb hS h0.le h1.le x x', cmb hS h0.le h1.le y y'))

/-- **Assumption 4.8.** `y ∈ Γ(x)` and `y' ∈ Γ(x')` imply `θy + (1 − θ)y' ∈ Γ(θx + (1 − θ)x')`. -/
def Assumption48 (hS : Convex ℝ S) (Γ : S → Set S) : Prop :=
  ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' → ∀ (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
    cmb hS h0 h1 y y' ∈ Γ (cmb hS h0 h1 x x')

variable {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ} {β : ℝ}

/-- The concave functions form a closed subset of `C(S)`. -/
theorem isClosed_concave (hS : Convex ℝ S) : IsClosed {f : S →ᵇ ℝ | IsConcaveS hS f} := by
  have : {f : S →ᵇ ℝ | IsConcaveS hS f} = ⋂ x, ⋂ x', ⋂ θ : ℝ, ⋂ h0 : 0 ≤ θ, ⋂ h1 : θ ≤ 1,
      {f : S →ᵇ ℝ | θ * f x + (1 - θ) * f x' ≤ f (cmb hS h0 h1 x x')} := by
    ext f; simp [IsConcaveS]
  rw [this]
  refine isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_iInter fun θ =>
    isClosed_iInter fun h0 => isClosed_iInter fun h1 => isClosed_le ?_ (continuous_eval_const _)
  exact (continuous_const.mul (continuous_eval_const x)).add
    (continuous_const.mul (continuous_eval_const x'))

/-- `T` maps concave functions into strictly concave ones (proof of Theorem 4.8). -/
theorem bellman_maps_concave (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {f : S →ᵇ ℝ}
    (hf : IsConcaveS hS f) : IsStrictConcaveS hS (bellman h43 h44 f) := by
  intro x₀ x₁ hne θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax h43 h44 f x₀
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax h43 h44 f x₁
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax h43 h44 f (cmb hS h0.le h1.le x₀ x₁)
  have hyθ := h48 x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0.le h1.le
  have hF := (h47 x₀ y₀ x₁ y₁ hy₀ hy₁ θ h0 h1).2 hne
  have hfc := mul_le_mul_of_nonneg_left (hf y₀ y₁ θ h0.le h1.le) h44.β_pos.le
  rw [hv₀, hv₁]
  refine lt_of_lt_of_le ?_ (hmax _ hyθ)
  nlinarith

/-- `T` preserves concavity. -/
theorem bellman_concave (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {f : S →ᵇ ℝ}
    (hf : IsConcaveS hS f) : IsConcaveS hS (bellman h43 h44 f) := by
  intro x x' θ h0 h1
  rcases eq_or_ne x x' with rfl | hne
  · rw [cmb_self]; linarith
  rcases h0.eq_or_lt with rfl | h0'
  · simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  rcases h1.eq_or_lt with rfl | h1'
  · simp only [one_mul, sub_self, zero_mul, add_zero]
    exact le_of_eq (congrArg _ (Subtype.ext (by simp [cmb])))
  exact (bellman_maps_concave h43 h44 h47 h48 hf x x' hne θ h0' h1').le

/-- With `w` strictly concave, `y ↦ F(x, y) + βw(y)` has at most one maximizer on `Γ(x)`. -/
theorem argmax_unique_of_strictConcave (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {w : S →ᵇ ℝ}
    (hw : IsStrictConcaveS hS w) (x : S) :
    ∀ y₁ ∈ argmax (obj F β w) Γ x, ∀ y₂ ∈ argmax (obj F β w) Γ x, y₁ = y₂ := by
  intro y₁ hy₁ y₂ hy₂
  by_contra hne
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hmem := h48 x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh.le hh1.le
  rw [cmb_self] at hmem
  have hF := (h47 x y₁ x y₂ hy₁.1 hy₂.1 (1 / 2) hh hh1).1
  rw [cmb_self] at hF
  have hvs := mul_lt_mul_of_pos_left (hw y₁ y₂ hne (1 / 2) hh hh1) h44.β_pos
  have hle := le_maxValue (continuousOn_obj h44 w.continuous) (h43.compact x) hmem
  have e1 := hy₁.2
  have e2 := hy₂.2
  simp only [obj] at hle e1 e2
  linarith

/-- **Theorem 4.8.** Under Assumptions 4.3–4.4 and 4.7–4.8, the fixed point `v` is strictly
concave, the policy correspondence `G` is single-valued, and its selection `g` is continuous. -/
theorem theorem_4_8 [Nonempty S] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) :
    IsStrictConcaveS hS v ∧ UniqueArgmax Γ (obj F β v) ∧
      (∀ x, argmax (obj F β v) Γ x = {argmaxFn Γ (obj F β v) x}) ∧
      Continuous (argmaxFn Γ (obj F β v)) := by
  have hvc : IsStrictConcaveS hS v :=
    (corollary_1 (S' := {f : S →ᵇ ℝ | IsConcaveS hS f}) (S'' := {f | IsStrictConcaveS hS f})
      (bellman_contraction h43 h44) hv ⟨0, fun x x' θ _ _ => by simp⟩ (isClosed_concave hS)
      (fun _ hf => bellman_concave h43 h44 h47 h48 hf)
      (fun _ hf => bellman_maps_concave h43 h44 h47 h48 hf)).2
  have huniq := argmax_unique_of_strictConcave h43 h44 h47 h48 hvc
  have hU : UniqueArgmax Γ (obj F β v) :=
    ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc, continuousOn_obj h44 v.continuous, huniq⟩
  exact ⟨hvc, hU, hU.argmax_eq, hU.continuous_argmaxFn⟩

/-- **Theorem 4.9 (convergence of the policy functions).** Let `v₀` be bounded, continuous and
concave, `vₙ = Tⁿv₀` and `gₙ` the maximizer for `vₙ`. Then `gₙ → g` pointwise, and uniformly
if `S` is compact. -/
theorem theorem_4_9 [Nonempty S] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) {v₀ : S →ᵇ ℝ} (hv₀ : IsConcaveS hS v₀) :
    (∀ x, Tendsto (fun n => argmaxFn Γ (obj F β ((bellman h43 h44)^[n] v₀)) x) atTop
      (𝓝 (argmaxFn Γ (obj F β v) x))) ∧
    (CompactSpace S → TendstoUniformly
      (fun n => argmaxFn Γ (obj F β ((bellman h43 h44)^[n] v₀)))
      (argmaxFn Γ (obj F β v)) atTop) := by
  set T := bellman h43 h44
  -- every iterate is concave, and from `n = 1` on strictly concave
  have hconc : ∀ n, IsConcaveS hS (T^[n] v₀) := by
    intro n
    induction n with
    | zero => exact hv₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact bellman_concave h43 h44 h47 h48 ih
  have hU : ∀ n, UniqueArgmax Γ (obj F β (T^[n + 1] v₀)) := fun n => by
    have hsc : IsStrictConcaveS hS (T^[n + 1] v₀) := by
      rw [Function.iterate_succ_apply']
      exact bellman_maps_concave h43 h44 h47 h48 (hconc n)
    exact ⟨h43.nonempty, h43.compact, h43.lhc, h43.uhc,
      continuousOn_obj h44 (T^[n + 1] v₀).continuous,
      argmax_unique_of_strictConcave h43 h44 h47 h48 hsc⟩
  have hUv := (theorem_4_8 h43 h44 h47 h48 hv).2.1
  -- `F + βvₙ → F + βv` uniformly
  have hunif : TendstoUniformlyOn (fun n => obj F β (T^[n + 1] v₀)) (obj F β v) atTop
      (graph Γ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => β * (β ^ (n + 1) * dist v₀ v)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h44.β_pos.le h44.β_lt).comp
        (tendsto_add_atTop_nat 1)).mul_const (dist v₀ v) |>.const_mul β
      simpa using this
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn p _
    have hd : dist (T^[n + 1] v₀) v ≤ β ^ (n + 1) * dist v₀ v := by
      obtain ⟨w, -, hwu, hwr⟩ := theorem_3_2 (bellman_contraction h43 h44)
      rw [← hwu v hv] at hwr
      exact hwr v₀ (n + 1)
    simp only [obj, Real.dist_eq]
    calc |F p + β * v p.2 - (F p + β * (T^[n + 1] v₀) p.2)|
        = β * |v p.2 - (T^[n + 1] v₀) p.2| := by
          rw [show F p + β * v p.2 - (F p + β * (T^[n + 1] v₀) p.2) =
            β * (v p.2 - (T^[n + 1] v₀) p.2) by ring, abs_mul, abs_of_pos h44.β_pos]
      _ ≤ β * (β ^ (n + 1) * dist v₀ v) := by
          refine mul_le_mul_of_nonneg_left ?_ h44.β_pos.le
          rw [← Real.dist_eq, dist_comm]
          exact (dist_coe_le_dist _).trans hd
      _ < ε := hn
  refine ⟨fun x => ?_, fun _ => ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).1 (theorem_3_8 hUv hU hunif x)
  · have := theorem_3_8_uniform hUv hU hunif
    rw [Metric.tendstoUniformly_iff] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (this ε hε)
    refine eventually_atTop.2 ⟨N + 1, fun n hn x => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hN m (by omega) x

end GrowthCertaintyDD

end StokeyLucasPrescott.EquilibriumApplications
