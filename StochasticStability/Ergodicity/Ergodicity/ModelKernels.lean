/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.MarkovProperty
import Ergodicity.ModelRecursion
import Mathlib.Probability.Independence.InfinitePi

/-!
# Transition kernels of random recursions (MT §3.5.5)

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelKernels.lean`), with the namespace changed to
`MeynTweedie.Ergodicity` and the imports to `InvariantMeasures.*`.

Meyn and Tweedie, §3.5.5, pp. 71–72: the kernel of the scalar nonlinear state space model
SNSS(F), and more generally of any random recursion `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)`, together with the
general fact behind every model of §§3.3 and 3.5: driven by i.i.d. noise independent of `X₀`,
such a recursion is a Markov chain with that kernel.

The kernel itself is `recursionKernel Γ F` (from `ModelRecursion`), `P(x, ·) = Γ ∘ F(x, ·)⁻¹`.

* `recursionKernel_eq_lintegral_indicator`: `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)` (MT p. 72).
* `kfun_recursionKernel`, `kfunR_recursionKernel`: `Ph(x) = ∫ h(F(x, w)) Γ(dw)` for nonnegative
  and for real measurable `h` (MT p. 72).
* `eq_3_44`: (3.44), `Pᵏ(x, A) = ∫ 1{Fₖ(x, w₁, …, wₖ) ∈ A} Γ(dw₁)⋯Γ(dwₖ)`, with the product
  measure `Γ^{⊗k}`; `recursionKernel_pow_succ_apply` gives the iterated form
  `Pᵏ⁺¹(x, A) = ∫ Pᵏ(F(x, w), A) Γ(dw)`.
* `recursion_eq_controlMap`: a process with `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` satisfies
  `Xₖ = Fₖ(X₀, W₁, …, Wₖ)` (MT p. 72).
* `isMarkovChain_canonPath`: on the canonical space `X × V^ℕ` with law `μ ⊗ Γ^{⊗ℕ}`, the
  recursion `canonPath F` is a Markov chain with kernel `P` and initial law `μ`. It is proved with
  `isMarkovChain_of_step` along the history filtration `histFilt`.
* `isMarkovChain_of_recursion`: on any probability space, a recursion whose initial state and
  noise have joint law `μ ⊗ Γ^{⊗ℕ}` is a Markov chain with kernel `P`.
* `IsIIDNoise` and `isMarkovChain_of_iid`: the book's hypotheses, `W₁, W₂, …` i.i.d. with law `Γ`
  and independent of `X₀` (SNSS2), imply the joint law above, so the recursion is a Markov chain
  with kernel `P` (MT p. 72, "since `{Wₙ}` is assumed i.i.d.").
* `IsMarkovChain.map_eq`: the law of `Φₙ` for any Markov chain is `μPⁿ` (3.8).
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]

/-- The SNSS(F) kernel (MT p. 72): `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)`. -/
theorem recursionKernel_eq_lintegral_indicator (Γ : Measure V) [SFinite Γ] {F : X × V → X}
    (hF : Measurable F) (x : X) {A : Set X} (hA : MeasurableSet A) :
    recursionKernel Γ F x A = ∫⁻ w, A.indicator 1 (F (x, w)) ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [recursionKernel_apply Γ hF x, ← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) hFx]

/-- MT p. 72: `Ph(x) = E[h(Xₙ₊₁) | Xₙ = x] = ∫ h(F(x, w)) Γ(dw)` for measurable `h ≥ 0`. -/
theorem kfun_recursionKernel (Γ : Measure V) [SFinite Γ] {F : X × V → X} (hF : Measurable F)
    {h : X → ℝ≥0∞} (hh : Measurable h) (x : X) :
    kfun (recursionKernel Γ F) h x = ∫⁻ w, h (F (x, w)) ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [kfun, recursionKernel_apply Γ hF x, lintegral_map hh hFx]

/-- MT p. 72: `Ph(x) = ∫ h(F(x, w)) Γ(dw)` for real measurable `h` (bounded `h` in the
book). -/
theorem kfunR_recursionKernel (Γ : Measure V) [SFinite Γ] {F : X × V → X} (hF : Measurable F)
    {h : X → ℝ} (hh : Measurable h) (x : X) :
    kfunR (recursionKernel Γ F) h x = ∫ w, h (F (x, w)) ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [kfunR, recursionKernel_apply Γ hF x,
    integral_map hFx.aemeasurable hh.aestronglyMeasurable]

/-- (3.44), MT p. 72: `Pᵏ(x, A) = ∫⋯∫ 1{Fₖ(x, w₁, …, wₖ) ∈ A} Γ(dw₁)⋯Γ(dwₖ)`, the
integral against the product law `Γ^{⊗k}` of `(W₁, …, Wₖ)`. -/
theorem eq_3_44 (Γ : Measure V) [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F)
    (k : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (recursionKernel Γ F ^ k) x A =
      ∫⁻ u, A.indicator 1 (controlMap F k x u) ∂(Measure.pi fun _ : Fin k => Γ) := by
  rw [recursionKernel_pow_apply Γ hF k x, ← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) (measurable_controlMap_right hF k x)]

/-- The iterated form of (3.44): `Pᵏ⁺¹(x, A) = ∫ Pᵏ(F(x, w), A) Γ(dw)`. -/
theorem recursionKernel_pow_succ_apply (Γ : Measure V) [IsProbabilityMeasure Γ]
    {F : X × V → X} (hF : Measurable F) (k : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    (recursionKernel Γ F ^ (k + 1)) x A =
      ∫⁻ w, (recursionKernel Γ F ^ k) (F (x, w)) A ∂Γ := by
  have hFx : Measurable fun w => F (x, w) := hF.comp measurable_prodMk_left
  rw [pow_succ_apply _ k x hA, recursionKernel_apply Γ hF x,
    lintegral_map (Kernel.measurable_coe _ hA) hFx]

/-! ### The recursion on the canonical space `X × V^ℕ` -/

/-- The history `(x, w₀, …, w_{n−1})` of a point `(x, w)` of the canonical space. Coordinate
`wₖ` of the canonical noise sequence plays the role of `Wₖ₊₁`. -/
def histMap (n : ℕ) (p : X × (ℕ → V)) : X × (Fin n → V) := (p.1, fun i => p.2 i)

/-- The history map is measurable. -/
theorem measurable_histMap (n : ℕ) : Measurable (histMap (X := X) (V := V) n) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp
    measurable_snd)

/-- The canonical recursion `Ψₙ(x, w) = Fₙ(x, w₀, …, w_{n−1})`: `Ψ₀ = x` and
`Ψₙ₊₁ = F(Ψₙ, wₙ)`. -/
def canonPath (F : X × V → X) (n : ℕ) (p : X × (ℕ → V)) : X :=
  controlMap F n p.1 fun i : Fin n => p.2 i

omit [MeasurableSpace X] [MeasurableSpace V] in
/-- `Ψ₀(x, w) = x`. -/
theorem canonPath_zero (F : X × V → X) (p : X × (ℕ → V)) : canonPath F 0 p = p.1 := rfl

omit [MeasurableSpace X] [MeasurableSpace V] in
/-- `Ψₙ₊₁ = F(Ψₙ, wₙ)`. -/
theorem canonPath_succ (F : X × V → X) (n : ℕ) (p : X × (ℕ → V)) :
    canonPath F (n + 1) p = F (canonPath F n p, p.2 n) := rfl

/-- Each `Ψₙ` is measurable. -/
theorem measurable_canonPath {F : X × V → X} (hF : Measurable F) (n : ℕ) :
    Measurable (canonPath F n) :=
  (measurable_controlMap hF n).comp (measurable_histMap n)

/-- The history filtration `𝓖ₙ = σ(x, w₀, …, w_{n−1})` on the canonical space. -/
def histFilt : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (X × (ℕ → V))) where
  seq n := MeasurableSpace.comap (histMap n) inferInstance
  mono' m n hmn := by
    have hproj : Measurable fun q : X × (Fin n → V) =>
        ((q.1, fun i : Fin m => q.2 (Fin.castLE hmn i)) : X × (Fin m → V)) :=
      measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp
        measurable_snd)
    have h : histMap (X := X) (V := V) m =
        (fun q : X × (Fin n → V) => ((q.1, fun i : Fin m => q.2 (Fin.castLE hmn i)) :
          X × (Fin m → V))) ∘ histMap n := rfl
    change MeasurableSpace.comap (histMap m) _ ≤ MeasurableSpace.comap (histMap n) _
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hproj.comap_le
  le' n := (measurable_histMap n).comap_le

/-- The first `n` coordinates of an i.i.d. sequence `w ∼ Γ^{⊗ℕ}` have law `Γ^{⊗n}`. -/
theorem infinitePi_map_fin (Γ : Measure V) [IsProbabilityMeasure Γ] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Γ).map (fun ω : ℕ → V => fun i : Fin n => ω i) =
      Measure.pi fun _ : Fin n => Γ := by
  have hm : Measurable fun ω : ℕ → V => fun i : Fin n => ω i :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set S : Finset ℕ := Finset.range n with hS
  set t : ℕ → Set V := fun k => if h : k < n then s ⟨k, h⟩ else Set.univ with ht
  have hpre : (fun ω : ℕ → V => fun i : Fin n => ω i) ⁻¹' Set.univ.pi s =
      Set.pi (S : Set ℕ) t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hS, ht,
      Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h k hk
      rw [dite_eq_left hk]
      exact h ⟨k, hk⟩
    · intro h i
      have := h i i.2
      rwa [dite_eq_left i.2] at this
  have hmt : ∀ k ∈ S, MeasurableSet (t k) := fun k _ => by
    simp only [ht]
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre, Measure.infinitePi_pi (fun _ : ℕ => Γ) hmt, hS, Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [ht, dite_eq_left i.2]

/-- Splitting off the last coordinate: under `Γ^{⊗(n+1)}`, `(u₀, …, u_{n−1})` and `uₙ` are
independent with laws `Γ^{⊗n}` and `Γ`. -/
theorem pi_map_init_last (Γ : Measure V) [IsProbabilityMeasure Γ] (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => Γ).map (fun u => (Fin.init u, u (Fin.last n))) =
      (Measure.pi fun _ : Fin n => Γ).prod Γ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Γ) (Fin.last n)
  have h : (fun u : Fin (n + 1) → V => (Fin.init u, u (Fin.last n))) =
      Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) (Fin.last n)) := by
    funext u
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  rw [h, ← Measure.map_map measurable_swap hmp.measurable, hmp.map_eq, Measure.prod_swap]

/-- Under `μ ⊗ Γ^{⊗ℕ}`, the history `(x, w₀, …, w_{n−1})` and the next noise `wₙ` are
independent, with laws `μ ⊗ Γ^{⊗n}` and `Γ`. -/
theorem law_hist_next (μ : Measure X) [SFinite μ] (Γ : Measure V) [IsProbabilityMeasure Γ]
    (n : ℕ) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => Γ)).map (fun p => (histMap n p, p.2 n)) =
      (μ.prod (Measure.pi fun _ : Fin n => Γ)).prod Γ := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hAB : Measurable fun w : ℕ → V => ((fun i : Fin n => w i), w n) :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply n)
  have hν : ν.map (fun w : ℕ → V => ((fun i : Fin n => w i), w n)) =
      (Measure.pi fun _ : Fin n => Γ).prod Γ := by
    have hc : (fun w : ℕ → V => ((fun i : Fin n => w i), w n)) =
        (fun u : Fin (n + 1) → V => (Fin.init u, u (Fin.last n))) ∘
          (fun w : ℕ → V => fun i : Fin (n + 1) => w i) := by
      funext w
      rfl
    have hg : Measurable fun u : Fin (n + 1) → V => (Fin.init u, u (Fin.last n)) :=
      (measurable_pi_iff.2 fun i => measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hf : Measurable fun w : ℕ → V => fun i : Fin (n + 1) => w i :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    rw [hc, ← Measure.map_map hg hf,
      infinitePi_map_fin, pi_map_init_last]
  have h1 : (μ.prod ν).map (Prod.map id fun w : ℕ → V => ((fun i : Fin n => w i), w n)) =
      μ.prod ((Measure.pi fun _ : Fin n => Γ).prod Γ) := by
    rw [← Measure.map_prod_map _ _ measurable_id hAB, Measure.map_id, hν]
  have hmp := (measurePreserving_prodAssoc μ (Measure.pi fun _ : Fin n => Γ) Γ).symm
  have h2 : (fun p : X × (ℕ → V) => (histMap n p, p.2 n)) =
      (MeasurableEquiv.prodAssoc (α := X) (β := Fin n → V) (γ := V)).symm ∘
        (Prod.map id fun w : ℕ → V => ((fun i : Fin n => w i), w n)) := by
    funext p
    rfl
  rw [h2, ← Measure.map_map hmp.measurable (measurable_id.prodMap hAB), h1, hmp.map_eq]

/-- The one-step property of the canonical recursion: for `G ∈ 𝓖ₙ` and measurable `f ≥ 0`,
`∫_G f(Ψₙ₊₁) = ∫_G Pf(Ψₙ)`. -/
theorem canon_step (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) (n : ℕ)
    {G : Set (X × (ℕ → V))} (hG : MeasurableSet[histFilt n] G) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p in G, f (canonPath F (n + 1) p) ∂(μ.prod (Measure.infinitePi fun _ => Γ)) =
      ∫⁻ p in G, ∫⁻ y, f y ∂recursionKernel Γ F (canonPath F n p)
        ∂(μ.prod (Measure.infinitePi fun _ => Γ)) := by
  obtain ⟨S, hS, rfl⟩ := hG
  set ρ := μ.prod (Measure.infinitePi fun _ : ℕ => Γ)
  set Θ : X × (ℕ → V) → (X × (Fin n → V)) × V := fun p => (histMap n p, p.2 n) with hΘdef
  have hΘ : Measurable Θ :=
    (measurable_histMap n).prodMk ((measurable_pi_apply n).comp measurable_snd)
  have hcm : Measurable fun q : X × (Fin n → V) => controlMap F n q.1 q.2 :=
    measurable_controlMap hF n
  have hφ : Measurable fun z : (X × (Fin n → V)) × V =>
      f (F (controlMap F n z.1.1 z.1.2, z.2)) :=
    hf.comp (hF.comp ((hcm.comp measurable_fst).prodMk measurable_snd))
  have hpre : histMap n ⁻¹' S = Θ ⁻¹' (S ×ˢ univ) := by
    ext p
    simp [Θ]
  have hL : ∫⁻ p in histMap n ⁻¹' S, f (canonPath F (n + 1) p) ∂ρ =
      ∫⁻ q in S, ∫⁻ v, f (F (controlMap F n q.1 q.2, v)) ∂Γ
        ∂(μ.prod (Measure.pi fun _ : Fin n => Γ)) := by
    rw [hpre]
    change ∫⁻ p in Θ ⁻¹' (S ×ˢ univ),
      (fun z : (X × (Fin n → V)) × V => f (F (controlMap F n z.1.1 z.1.2, z.2))) (Θ p) ∂ρ = _
    rw [← setLIntegral_map (hS.prod MeasurableSet.univ) hφ hΘ, law_hist_next,
      setLIntegral_prod _ hφ.aemeasurable]
    simp only [Measure.restrict_univ]
  have hmarg : ρ.map (histMap n) = μ.prod (Measure.pi fun _ : Fin n => Γ) := by
    have : histMap n = Prod.fst ∘ Θ := rfl
    rw [this, ← Measure.map_map measurable_fst hΘ, law_hist_next, Measure.map_fst_prod,
      measure_univ, one_smul]
  have hψ : Measurable fun q : X × (Fin n → V) =>
      ∫⁻ v, f (F (controlMap F n q.1 q.2, v)) ∂Γ :=
    hφ.lintegral_prod_right'
  rw [hL, ← hmarg, setLIntegral_map hS hψ (measurable_histMap n)]
  refine lintegral_congr fun p => ?_
  exact (kfun_recursionKernel Γ hF hf _).symm

/-- **The recursion on the canonical space is a Markov chain** (MT p. 72): under
`μ ⊗ Γ^{⊗ℕ}`, `Ψₙ₊₁ = F(Ψₙ, wₙ)` is a Markov chain with kernel `P(x, A) = Γ{w : F(x, w) ∈ A}`
and initial law `μ`. -/
theorem isMarkovChain_canonPath (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) :
    IsMarkovChain (recursionKernel Γ F) μ (μ.prod (Measure.infinitePi fun _ => Γ))
      (canonPath F) := by
  refine isMarkovChain_of_step _ μ (𝓖 := histFilt) (fun n => ?_) ?_
    (fun n G hG f hf => canon_step μ Γ hF n hG hf)
  · exact (measurable_controlMap hF n).comp (comap_measurable (histMap n))
  · rw [show canonPath F 0 = Prod.fst from rfl, Measure.map_fst_prod, measure_univ, one_smul]

omit [MeasurableSpace X] [MeasurableSpace V] in
variable {Ω : Type*} in
/-- MT p. 72: a process with `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` satisfies `Xₖ = Fₖ(X₀, W₁, …, Wₖ)`. -/
theorem recursion_eq_controlMap {F : X × V → X} {Φ : ℕ → Ω → X} {W : ℕ → Ω → V}
    (hrec : ∀ n ω, Φ (n + 1) ω = F (Φ n ω, W (n + 1) ω)) (k : ℕ) (ω : Ω) :
    Φ k ω = controlMap F k (Φ 0 ω) fun i => W (i + 1) ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [hrec, ih]
    rfl

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- **A random recursion is a Markov chain** (MT p. 72, and the general fact behind §3.5).
On any space `(Ω, ℙ)`, if `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` and `(X₀, (W₁, W₂, …))` has law `μ ⊗ Γ^{⊗ℕ}`,
then `X` is a Markov chain with kernel `P(x, A) = Γ{w : F(x, w) ∈ A}` and initial law `μ`. -/
theorem isMarkovChain_of_recursion (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) {pr : Measure Ω}
    {Φ : ℕ → Ω → X} {W : ℕ → Ω → V} (hΦ0 : Measurable (Φ 0)) (hW : ∀ n, Measurable (W n))
    (hrec : ∀ n ω, Φ (n + 1) ω = F (Φ n ω, W (n + 1) ω))
    (hlaw : pr.map (fun ω => (Φ 0 ω, fun n => W (n + 1) ω)) =
      μ.prod (Measure.infinitePi fun _ => Γ)) :
    IsMarkovChain (recursionKernel Γ F) μ pr Φ := by
  set Θ : Ω → X × (ℕ → V) := fun ω => (Φ 0 ω, fun n => W (n + 1) ω)
  have hΘ : Measurable Θ := hΦ0.prodMk (measurable_pi_iff.2 fun n => hW (n + 1))
  have hcomp : ∀ n, Φ n = canonPath F n ∘ Θ := fun n => by
    funext ω
    exact recursion_eq_controlMap hrec n ω
  have hc := isMarkovChain_canonPath μ Γ hF
  refine ⟨fun n => hcomp n ▸ (measurable_canonPath hF n).comp hΘ, fun n A hA => ?_⟩
  have hset : {ω | ∀ i ≤ n, Φ i ω ∈ A i} = Θ ⁻¹' {p | ∀ i ≤ n, canonPath F i p ∈ A i} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hcomp, Function.comp_apply]
  have hmeas : MeasurableSet {p : X × (ℕ → V) | ∀ i ≤ n, canonPath F i p ∈ A i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurable_canonPath hF i (hA i)
  rw [hset, ← Measure.map_apply hΘ hmeas, hlaw]
  exact hc.fdd n A hA

variable {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) (X₀ : Ω → X) (W : ℕ → Ω → V)
  (Γ : Measure V) in
/-- The noise hypotheses of the book (SNSS2), (SLM2), (RW1), (Q1)–(Q2), …: the disturbances
`W₁, W₂, …` are i.i.d. with law `Γ` and independent of the initial state `X₀`. The coordinate
`W₀` is not used. -/
structure IsIIDNoise : Prop where
  /-- Each `Wₙ` is a random variable. -/
  measurable : ∀ n, Measurable (W n)
  /-- `Wₙ₊₁ ∼ Γ`. -/
  law : ∀ n, pr.map (W (n + 1)) = Γ
  /-- `W₁, W₂, …` are mutually independent. -/
  iIndep : iIndepFun (fun n => W (n + 1)) pr
  /-- The noise sequence is independent of `X₀`. -/
  indep : IndepFun X₀ (fun ω n => W (n + 1) ω) pr

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- Under `IsIIDNoise`, the initial state and the noise have joint law `μ ⊗ Γ^{⊗ℕ}`. -/
theorem IsIIDNoise.map_eq {pr : Measure Ω} [IsProbabilityMeasure pr] {X₀ : Ω → X}
    {W : ℕ → Ω → V} {Γ : Measure V} (h : IsIIDNoise pr X₀ W Γ) (hX₀ : Measurable X₀) :
    pr.map (fun ω => (X₀ ω, fun n => W (n + 1) ω)) =
      (pr.map X₀).prod (Measure.infinitePi fun _ => Γ) := by
  have hWm : Measurable fun ω n => W (n + 1) ω :=
    measurable_pi_iff.2 fun n => h.measurable (n + 1)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX₀.aemeasurable hWm.aemeasurable).1 h.indep,
    h.iIndep.map_fun_eq_infinitePi_map (fun n => h.measurable (n + 1))]
  simp_rw [h.law]

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- **I.i.d. noise makes a recursion Markov** (MT p. 72). If `Xₙ₊₁ = F(Xₙ, Wₙ₊₁)` with
`W₁, W₂, …` i.i.d. with law `Γ` and independent of `X₀ ∼ μ`, then `X` is a Markov chain with
kernel `P(x, A) = ∫ 1{F(x, w) ∈ A} Γ(dw)` and initial law `μ`. -/
theorem isMarkovChain_of_iid (μ : Measure X) [IsProbabilityMeasure μ] (Γ : Measure V)
    [IsProbabilityMeasure Γ] {F : X × V → X} (hF : Measurable F) {pr : Measure Ω}
    [IsProbabilityMeasure pr] {Φ : ℕ → Ω → X} {W : ℕ → Ω → V} (hΦ0 : Measurable (Φ 0))
    (hrec : ∀ n ω, Φ (n + 1) ω = F (Φ n ω, W (n + 1) ω)) (hinit : pr.map (Φ 0) = μ)
    (hW : IsIIDNoise pr (Φ 0) W Γ) :
    IsMarkovChain (recursionKernel Γ F) μ pr Φ := by
  refine isMarkovChain_of_recursion μ Γ hF hΦ0 hW.measurable hrec ?_
  rw [hW.map_eq hΦ0, hinit]

variable {Ω : Type*} [MeasurableSpace Ω] in
/-- (3.8) for any Markov chain: the law of `Φₙ` is `μPⁿ`. -/
theorem IsMarkovChain.map_eq {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] {pr : Measure Ω} {Φ : ℕ → Ω → X} (h : IsMarkovChain P μ pr Φ)
    (n : ℕ) : pr.map (Φ n) = (P ^ n) ∘ₘ μ := by
  have hΦ : Measurable fun ω n => Φ n ω := measurable_pi_iff.2 h.measurable
  have hc : Φ n = (fun ω : ℕ → X => ω n) ∘ fun ω n => Φ n ω := rfl
  rw [hc, ← Measure.map_map (measurable_pi_apply n) hΦ, law_eq_pathMeasure P μ h,
    pathMeasure_map_coord]

end MeynTweedie.Ergodicity
