/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.OCMaxPrincipleLinks
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# §§7.4–7.5: tools (supergradients, the limit step, inequality (7.38))

Copied from `EconomicDynamics/InfiniteHorizonDP` (module `EUTools`), namespace renamed.

Miao, §§7.4–7.5, pp. 217–227. Tools for the Maximum Principle and the Euler-equation results.

* `eu_concave_le_fderiv` and `eu_le_of_le_add_tendsto_zero` are copied from
  `RecursiveMethods/DeterministicDP` (module `EulerEquations`: `concave_le_fderiv`,
  `le_of_le_add_tendsto_zero`), namespace renamed: a concave function lies below its tangent
  plane at a point of differentiability, on any convex set (not only on the whole space); and the
  limit step `s′_T ≤ s_T + w_T`, `w_T → 0` ⇒ `lim s′ ≤ lim s` in `[−∞, +∞]`.
* `eu_supergradient`: the supergradient inequality on a convex subset of `ℝ²`, with the partial
  derivatives written as `deriv` (as in `oc_supergradient`, which needs concavity on all of `ℝ²`).
* `eu_limsup_le`: the limit step of the sufficiency proofs in the form we use for optimality.
  If `S*_T → J*` and `S_T ≤ S*_T + w_T` with `w_T → 0`, then `S_T ≤ J* + ε` eventually: the
  partial sums of the competing plan are eventually at most `J* + ε`, whether or not they
  converge (they may tend to `−∞`).
* `eq_7_38` (**inequality (7.38)**, p. 224): for `f` concave on `[0, 1]`, `γ ∈ [0, 1)` and
  `λ ∈ [γ, 1)`, `(f(1) − f(λ))/(1 − λ) ≤ (f(1) − f(γ))/(1 − γ)`. The book allows
  `f : [0, 1] → ℝ ∪ {−∞}` with `f(1) > −∞`; when `f(γ) = −∞` the right side is `+∞` and there is
  nothing to prove, so we state the real-valued case.
* `eu_clm_pair`: a continuous linear form on `ℝⁿ × ℝⁿ` in coordinates,
  `L(v, w) = Σᵢ vᵢ L(eᵢ, 0) + Σᵢ wᵢ L(0, eᵢ)`, so that `L(v, w) = u_x · v + u_a · w` with the
  partial derivatives as vectors.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- A concave function lies below its tangent plane (copied from
`RecursiveMethods/DeterministicDP`, `concave_le_fderiv`): if `φ` is concave on a convex set `A`
containing `z₀` and `z`, and has derivative `φ'` at `z₀`, then `φ(z) ≤ φ(z₀) + φ'(z − z₀)`. -/
theorem eu_concave_le_fderiv {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {A : Set F'} {φ : F' → ℝ} (hφ : ConcaveOn ℝ A φ) {z₀ z : F'} (hz₀ : z₀ ∈ A) (hz : z ∈ A)
    {φ' : F' →L[ℝ] ℝ} (hd : HasFDerivAt φ φ' z₀) : φ z ≤ φ z₀ + φ' (z - z₀) := by
  set g : ℝ → ℝ := fun t => φ (z₀ + t • (z - z₀))
  have hg : HasDerivAt g (φ' (z - z₀)) 0 := by
    have hline : HasDerivAt (fun t : ℝ => z₀ + t • (z - z₀)) (z - z₀) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - z₀)).const_add z₀
    have hd' : HasFDerivAt φ φ' (z₀ + (0 : ℝ) • (z - z₀)) := by simpa using hd
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    simpa [g, Function.comp_def] using this
  have hslope : ∀ t : ℝ, 0 < t → t ≤ 1 → φ z - φ z₀ ≤ t⁻¹ • (g (0 + t) - g 0) := by
    intro t ht0 ht1
    have hc := hφ.2 hz₀ hz (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    have e : (1 - t) • z₀ + t • z = z₀ + t • (z - z₀) := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hc
    simp only [g, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    linarith
  have hlim := hg.tendsto_slope_zero_right
  refine sub_le_iff_le_add'.1 (ge_of_tendsto hlim ?_)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
  exact hslope t ht.1 ht.2.le

/-- The limit step (copied from `RecursiveMethods/DeterministicDP`,
`le_of_le_add_tendsto_zero`): if `sₙ → L`, `wₙ → 0`, `s′ₙ ≤ sₙ + wₙ` and `s′ₙ → L′` in
`[−∞, +∞]`, then `L′ ≤ L`. -/
theorem eu_le_of_le_add_tendsto_zero {s s' w : ℕ → ℝ} {L L' : EReal}
    (hs : Tendsto (fun n => (s n : EReal)) atTop (𝓝 L))
    (hs' : Tendsto (fun n => (s' n : EReal)) atTop (𝓝 L'))
    (hw : Tendsto w atTop (𝓝 0)) (h : ∀ n, s' n ≤ s n + w n) : L' ≤ L := by
  have hw' : Tendsto (fun n => ((w n : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
    have := EReal.tendsto_coe.2 hw
    rwa [EReal.coe_zero] at this
  have hsum : Tendsto (fun n => ((s n + w n : ℝ) : EReal)) atTop (𝓝 (L + 0)) := by
    simp only [EReal.coe_add]
    exact (EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))).tendsto.comp
      (hs.prodMk_nhds hw')
  rw [add_zero] at hsum
  exact le_of_tendsto_of_tendsto hs' hsum (Eventually.of_forall fun n =>
    EReal.coe_le_coe_iff.2 (h n))

/-- The limit step of the sufficiency proofs: if `S*_T → J*`, `w_T → 0` and
`S_T ≤ S*_T + w_T`, then for every `ε > 0`, eventually `S_T ≤ J* + ε`. -/
theorem eu_limsup_le {S Ss w : ℕ → ℝ} {J : ℝ} (hSs : Tendsto Ss atTop (𝓝 J))
    (hw : Tendsto w atTop (𝓝 0)) (h : ∀ T, S T ≤ Ss T + w T) :
    ∀ ε > 0, ∀ᶠ T in atTop, S T ≤ J + ε := by
  intro ε hε
  have hsum : Tendsto (fun T => Ss T + w T) atTop (𝓝 (J + 0)) := hSs.add hw
  rw [add_zero] at hsum
  filter_upwards [(tendsto_order.1 hsum).2 (J + ε) (by linarith)] with T hT
  exact (h T).trans hT.le

/-- **The supergradient inequality on a convex subset of `ℝ²`**: if `h` is concave on `S`,
`p, q ∈ S` and `h` is differentiable at `p`, then
`h(q) ≤ h(p) + (q₁ − p₁) ∂₁h(p) + (q₂ − p₂) ∂₂h(p)`. -/
theorem eu_supergradient {S : Set (ℝ × ℝ)} {h : ℝ × ℝ → ℝ} (hc : ConcaveOn ℝ S h)
    {p q : ℝ × ℝ} (hp : p ∈ S) (hq : q ∈ S) (hd : DifferentiableAt ℝ h p) :
    h q ≤ h p + (q.1 - p.1) * deriv (fun y => h (y, p.2)) p.1 +
      (q.2 - p.2) * deriv (fun b => h (p.1, b)) p.2 := by
  set L := fderiv ℝ h p
  have hL : HasFDerivAt h L p := hd.hasFDerivAt
  have h1 : deriv (fun y => h (y, p.2)) p.1 = L (1, 0) := by
    have : HasDerivAt (fun y : ℝ => (y, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hL.comp_hasDerivAt p.1 this).deriv
  have h2 : deriv (fun b => h (p.1, b)) p.2 = L (0, 1) := by
    have : HasDerivAt (fun b : ℝ => (p.1, b)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hL.comp_hasDerivAt p.2 this).deriv
  have ht := eu_concave_le_fderiv hc hp hq hL
  have hdec : q - p = (q.1 - p.1) • ((1 : ℝ), (0 : ℝ)) + (q.2 - p.2) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at ht
  rw [h1, h2]
  linarith

/-- **Inequality (7.38)** (Miao, p. 224): let `f` be concave on `[0, 1]`. Then for `γ ∈ [0, 1)`
and `λ ∈ [γ, 1)`, `(f(1) − f(λ))/(1 − λ) ≤ (f(1) − f(γ))/(1 − γ)`. The proof is the book's:
with `α = (1 − λ)/(1 − γ) ∈ (0, 1]`, `λ = αγ + (1 − α)·1`, so concavity gives
`f(λ) ≥ αf(γ) + (1 − α)f(1)`. -/
theorem eq_7_38 {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Icc 0 1) f) {γ lam : ℝ} (hγ0 : 0 ≤ γ)
    (hγl : γ ≤ lam) (hl1 : lam < 1) :
    (f 1 - f lam) / (1 - lam) ≤ (f 1 - f γ) / (1 - γ) := by
  have h1γ : 0 < 1 - γ := by linarith
  have h1l : 0 < 1 - lam := by linarith
  set α := (1 - lam) / (1 - γ) with hα
  have hα0 : 0 ≤ α := div_nonneg h1l.le h1γ.le
  have hα1 : α ≤ 1 := (div_le_one h1γ).2 (by linarith)
  have hcomb : α • γ + (1 - α) • (1 : ℝ) = lam := by
    simp only [smul_eq_mul, mul_one, hα]
    field_simp
    ring
  have hc : α • f γ + (1 - α) • f 1 ≤ f (α • γ + (1 - α) • (1 : ℝ)) :=
    hf.2 (⟨hγ0, by linarith⟩ : γ ∈ Set.Icc (0 : ℝ) 1)
      (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) hα0 (by linarith) (by ring)
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hc
  rw [div_le_div_iff₀ h1l h1γ]
  have key : f 1 - f lam ≤ α * (f 1 - f γ) := by nlinarith
  have : α * (1 - γ) = 1 - lam := by rw [hα]; field_simp
  have h2 := mul_le_mul_of_nonneg_right key h1γ.le
  have h3 : α * (f 1 - f γ) * (1 - γ) = (f 1 - f γ) * (1 - lam) := by rw [← this]; ring
  linarith

/-- A continuous linear form on `ℝⁿ × ℝⁿ` in coordinates:
`L(v, w) = Σᵢ vᵢ L(eᵢ, 0) + Σᵢ wᵢ L(0, eᵢ)`. -/
theorem eu_clm_pair {n : ℕ} (L : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (v w : Fin n → ℝ) :
    L (v, w) = ∑ i, v i * L (Pi.single i 1, 0) + ∑ i, w i * L (0, Pi.single i 1) := by
  have hv : (v, (0 : Fin n → ℝ)) = ∑ i, v i • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin n → ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have hw : ((0 : Fin n → ℝ), w) = ∑ i, w i • ((0 : Fin n → ℝ), (Pi.single i 1 : Fin n → ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsplit : (v, w) = (v, (0 : Fin n → ℝ)) + ((0 : Fin n → ℝ), w) := by simp
  rw [hsplit, map_add, hv, hw, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

end Miao.IncompleteMarkets
