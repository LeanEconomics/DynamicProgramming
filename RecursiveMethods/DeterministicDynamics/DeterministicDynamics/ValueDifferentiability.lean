/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.Concavity
import DeterministicDynamics.Envelope
import DeterministicDynamics.InteriorPoints

/-!
# Differentiability of the value function

SLP Theorem 4.11, p. 85. The state space is a convex set `S ⊆ ℝˡ`; a function `f` on `S` is
extended by zero to `ℝˡ` (`liftS`) so that its derivative at interior points of `S` makes sense.

* `concaveOn_liftS`: a concave function on `S` gives a concave function on `S ⊆ ℝˡ`.
* `eventually_mem_Γ`: if `g(x₀)` is interior to `Γ(x₀)`, then `g(x₀) ∈ Γ(x)` for all `x` near
  `x₀`. The book takes this from the continuity of `Γ`; it uses the convexity of the values of
  `Γ` (Assumption 4.8).
* `theorem_4_11`: if `x₀ ∈ int S`, `g(x₀) ∈ int Γ(x₀)` and `x ↦ F(x, g(x₀))` is differentiable at
  `x₀`, then `v` is differentiable at `x₀` with `Dv(x₀) = D_xF(x₀, g(x₀))`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {S : Set (Fin l → ℝ)} {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ}
  {β : ℝ}

/-- A function on `S` extended by zero to `ℝˡ`. -/
noncomputable def liftS (f : S → ℝ) (x : Fin l → ℝ) : ℝ := by
  classical exact if hx : x ∈ S then f ⟨x, hx⟩ else 0

theorem liftS_of_mem (f : S → ℝ) {x : Fin l → ℝ} (hx : x ∈ S) : liftS f x = f ⟨x, hx⟩ := by
  simp only [liftS, hx, ↓reduceDIte]

/-- A strictly concave function is concave. -/
theorem IsStrictConcaveS.isConcaveS {f : S → ℝ} (hf : IsStrictConcaveS hS f) :
    IsConcaveS hS f := by
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

/-- A concave function on `S` is concave on `S ⊆ ℝˡ` after extension. -/
theorem concaveOn_liftS {f : S → ℝ} (hf : IsConcaveS hS f) : ConcaveOn ℝ S (liftS f) := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hmem : a • x + b • y ∈ S := hS hx hy ha hb hab
  rw [liftS_of_mem f hx, liftS_of_mem f hy, liftS_of_mem f hmem, smul_eq_mul, smul_eq_mul]
  have := hf ⟨x, hx⟩ ⟨y, hy⟩ a ha ha1
  subst hb'
  exact this

/-- Under Assumption 4.8 the values of `Γ` are convex subsets of `ℝˡ`. -/
theorem convex_image_Γ (h48 : Assumption48 hS Γ) (x : S) : Convex ℝ (Subtype.val '' Γ x) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h48 x y x y' hy hy' a ha (by linarith)
  rw [cmb_self] at this
  exact ⟨_, this, rfl⟩

/-- If `g₀` is interior to `Γ(x₀)` (as a subset of `ℝˡ`), then `g₀ ∈ Γ(x)` for all `x` near
`x₀` (continuity of `Γ` and Assumption 4.8). -/
theorem eventually_mem_Γ (h43 : Assumption43 Γ) (h48 : Assumption48 hS Γ) {x₀ g₀ : S}
    (hg : g₀.1 ∈ interior (Subtype.val '' Γ x₀)) : ∀ᶠ x in 𝓝 x₀, g₀ ∈ Γ x := by
  have hlhc : IsLHC (fun x => Subtype.val '' Γ x) x₀ := by
    refine ⟨(h43.lhc x₀).1.image _, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ xs hxs
    obtain ⟨N, ys, hys, hlim⟩ := (h43.lhc x₀).2 y hy xs hxs
    exact ⟨N, fun n => (ys n).1, fun n hn => ⟨ys n, hys n hn, rfl⟩,
      (continuous_subtype_val.tendsto y).comp hlim⟩
  have hseq : ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x₀) → ∀ᶠ n in atTop, g₀ ∈ Γ (xs n) :=
    fun xs hxs => (eventually_mem_of_mem_interior (convex_image_Γ h48) hlhc hg hxs).mono
      fun n ⟨y, hy, hyg⟩ => Subtype.ext hyg ▸ hy
  exact eventually_iff_seq_eventually.2 hseq

/-- **Theorem 4.11 (differentiability of the value function).** Under Assumptions 4.3–4.4 and
4.7–4.8, if `x₀ ∈ int S`, `g(x₀) ∈ int Γ(x₀)` and `x ↦ F(x, g(x₀))` has derivative `DF` at `x₀`,
then `v` is differentiable at `x₀` with derivative `DF`, i.e. `vᵢ(x₀) = Fᵢ(x₀, g(x₀))`. -/
theorem theorem_4_11 [Nonempty S] (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h47 : Assumption47 hS Γ F) (h48 : Assumption48 hS Γ) {v : S →ᵇ ℝ}
    (hv : bellman h43 h44 v = v) {x₀ : S} (hint : S ∈ 𝓝 x₀.1)
    (hg : (argmaxFn Γ (obj F β v) x₀).1 ∈ interior (Subtype.val '' Γ x₀))
    {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt (liftS fun x => F (x, argmaxFn Γ (obj F β v) x₀)) DF x₀.1) :
    HasFDerivAt (liftS v) DF x₀.1 := by
  set g₀ := argmaxFn Γ (obj F β v) x₀
  obtain ⟨hvc, hU, -, -⟩ := theorem_4_8 h43 h44 h47 h48 hv
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => F (x, g₀)) x + β * v g₀
  have hW : HasFDerivAt W DF x₀.1 := hF.add_const _
  -- `W(x₀) = v(x₀)`
  have hg₀ := hU.argmaxFn_mem x₀
  have hvx : ∀ x : S, v x = maxValue (obj F β v) Γ x := fun x => by
    rw [← bellman_apply h43 h44, hv]
  have heq : W x₀.1 = liftS v x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx x₀]
    exact hg₀.2
  -- `W ≤ v` near `x₀`
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS v x := by
    have h1 := eventually_mem_Γ (hS := hS) h43 h48 (x₀ := x₀) (g₀ := g₀) hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx ⟨x, hxS⟩]
    exact le_maxValue (continuousOn_obj h44 v.continuous) (h43.compact _) (hx ⟨x, hxS⟩ rfl)
  exact theorem_4_10 (concaveOn_liftS hvc.isConcaveS) hint hW heq hle

end StokeyLucasPrescott.DeterministicDynamics
