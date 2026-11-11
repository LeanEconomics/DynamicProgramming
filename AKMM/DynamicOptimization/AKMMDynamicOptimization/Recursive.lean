/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.Principle
import DeterministicDP.BoundedReturns
import DeterministicDP.Concavity
import DeterministicDP.Envelope
import DeterministicDynamics.GrowthStability
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact

/-!
# Recursive methods: the Bellman equation and the properties of the value function

AKMM, §4.4.1–4.4.3, pp. 114–120. The sequence-problem machinery is SLP's (`DeterministicDP`):
`Feasible`, `vstar` (the value `V` of (4.21), in the extended reals), `SatisfiesFE`, the Bellman
operator `bellman` on bounded continuous functions.

* (4.21)–(4.22): `V` satisfies the Bellman equation (`eq_4_22`, SLP Theorem 4.2), and along an
  optimal plan `V(x) = F(x, g(x)) + βV(g(x))` (`eq_4_22_policy`, SLP Theorem 4.4).
* The periodic NGM (p. 117) is recursive in the state `(k, parity)` (`periodic_bellman`); the
  printed constraint set `Γ_i(k) = [0, A_if(k) + (1 − δ)k − k']` is wrong
  (`periodic_printed_gamma`).
* The delayed-depreciation NGM (p. 118) is recursive in `(i_{t−1}, i_{t−2})`, with the discount
  factor the printed equation omits (`delayed_bellman`); without `β` the Bellman operator is not
  a contraction (`delayed_no_discount_not_contraction`).
* The properties of `V` (pp. 119–120): 1. value-function iteration converges, with
  `‖V_{n+1} − V‖ ≤ β‖V_n − V‖` (`property_1`, SLP Theorem 4.6); 2. `V` strictly increasing
  (`property_2`, SLP Theorem 4.7); 3. `V` strictly concave and the policy unique and continuous
  (`property_3`, SLP Theorem 4.8); 4. `V` differentiable at interior choices, with the envelope
  formula (`property_4`, from SLP Theorem 4.10).
* Property 5 ("`g` strictly increasing") is false under the stated conditions
  (`property_5_counterexample`); it holds with increasing differences (`property_5_corrected`,
  monotone policy) and in the NGM (`property_5_ngm`, SLP Exercise 6.1b).
-/

namespace AKMM.DynamicOptimization

open Filter Topology BoundedContinuousFunction StokeyLucasPrescott.DeterministicDP

/-- **AKMM, (4.21)–(4.22), pp. 115–116: the Bellman equation.** The value function
`V(x₀) = sup Σ βᵗF(x_t, x_{t+1})` satisfies `V(x) = sup_{x' ∈ Γ(x)} {F(x, x') + βV(x')}`, given
nonempty `Γ` and convergent partial sums (SLP Theorem 4.2). -/
theorem eq_4_22 {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β) : SatisfiesFE Γ F β (vstar Γ F β) :=
  theorem_4_2 hβ h41 h42

/-- AKMM, p. 117: along an optimal plan `x_{t+1} = g(x_t)`, `V(x_t) = F(x_t, x_{t+1}) +
βV(x_{t+1})` (SLP Theorem 4.4). -/
theorem eq_4_22_policy {X : Type*} {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ : 0 < β)
    (h42 : Assumption42 Γ F β) {x₀ : X} {xs : ℕ → X} (hxs : xs ∈ Feasible Γ x₀)
    (hopt : total F β xs = vstar Γ F β x₀) (t : ℕ) :
    vstar Γ F β (xs t) = (F (xs t) (xs (t + 1)) : EReal) + (β : EReal) * vstar Γ F β (xs (t + 1)) :=
  theorem_4_4 hβ h42 hxs hopt t

/-- The periodic NGM in the state `(k, i)`: `Γ̃(k, i) = {(k', ¬i) : 0 ≤ k' ≤ A_if(k) + (1 − δ)k}`
(`i = true` for the even periods with `A_h`). -/
def periodicGamma (A : Bool → ℝ) (f : ℝ → ℝ) (δ : ℝ) (s : ℝ × Bool) : Set (ℝ × Bool) :=
  (fun k' => (k', !s.2)) '' Set.Icc 0 (A s.2 * f s.1 + (1 - δ) * s.1)

/-- The periodic NGM's return `u(A_if(k) + (1 − δ)k − k')`. -/
noncomputable def periodicF (A : Bool → ℝ) (u f : ℝ → ℝ) (δ : ℝ) (s s' : ℝ × Bool) : ℝ :=
  u (A s.2 * f s.1 + (1 - δ) * s.1 - s'.1)

/-- **AKMM, p. 117: the periodic NGM is recursive** in `(k, parity)`: the value functions
`V_h(k) = V(k, true)` and `V_l(k) = V(k, false)` satisfy
`V_h(k) = max_{k' ∈ Γ_h(k)} {u(A_hf(k) + (1 − δ)k − k') + βV_l(k')}` and symmetrically, with
`Γ_i(k) = [0, A_if(k) + (1 − δ)k]`. -/
theorem periodic_bellman {A : Bool → ℝ} {u f : ℝ → ℝ} {δ β : ℝ} (hβ : 0 ≤ β)
    (h41 : Assumption41 (periodicGamma A f δ))
    (h42 : Assumption42 (periodicGamma A f δ) (periodicF A u f δ) β) (k : ℝ) (i : Bool) :
    vstar (periodicGamma A f δ) (periodicF A u f δ) β (k, i) =
      ⨆ k' ∈ Set.Icc 0 (A i * f k + (1 - δ) * k),
        ((u (A i * f k + (1 - δ) * k - k') : ℝ) : EReal) +
          (β : EReal) * vstar (periodicGamma A f δ) (periodicF A u f δ) β (k', !i) := by
  rw [eq_4_22 hβ h41 h42 (k, i), periodicGamma, iSup_image]
  rfl

/-- **AKMM, p. 118, corrected.** The printed `Γ_i(k) = [0, A_if(k) + (1 − δ)k − k']`, read as a
constraint on `k'`, is `0 ≤ k' ≤ (A_if(k) + (1 − δ)k)/2`: it excludes, e.g., consuming nothing,
`k' = A_if(k) + (1 − δ)k > 0`, which the resource constraint allows. -/
theorem periodic_printed_gamma {R : ℝ} (hR : 0 < R) :
    (∀ k', k' ∈ Set.Icc 0 (R - k') ↔ 0 ≤ k' ∧ 2 * k' ≤ R) ∧ R ∈ Set.Icc 0 R ∧
      R ∉ Set.Icc 0 (R - R) := by
  refine ⟨fun k' => ?_, ⟨hR.le, le_rfl⟩, fun h => ?_⟩
  · rw [Set.mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · have := h.2; linarith

/-- The delayed-depreciation NGM in the state `(i_{t−1}, i_{t−2})`, with
`k_t = i_{t−1} + i_{t−2}`: `Γ̃(i', i) = {(i'', i') : 0 ≤ i'' ≤ f(i' + i)}`. -/
def delayedGamma (f : ℝ → ℝ) (s : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun i'' => (i'', s.1)) '' Set.Icc 0 (f (s.1 + s.2))

/-- The delayed-depreciation return `u(f(i' + i) − i'')`. -/
noncomputable def delayedF (u f : ℝ → ℝ) (s s' : ℝ × ℝ) : ℝ := u (f (s.1 + s.2) - s'.1)

/-- **AKMM, p. 118, corrected: the delayed-depreciation NGM.** The value function satisfies
`V(i', i) = max_{0 ≤ i'' ≤ f(i' + i)} {u(f(i' + i) − i'') + βV(i'', i')}`; the book omits `β`. -/
theorem delayed_bellman {u f : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) (h41 : Assumption41 (delayedGamma f))
    (h42 : Assumption42 (delayedGamma f) (delayedF u f) β) (i' i : ℝ) :
    vstar (delayedGamma f) (delayedF u f) β (i', i) =
      ⨆ i'' ∈ Set.Icc 0 (f (i' + i)), ((u (f (i' + i) - i'') : ℝ) : EReal) +
        (β : EReal) * vstar (delayedGamma f) (delayedF u f) β (i'', i') := by
  rw [eq_4_22 hβ h41 h42 (i', i), delayedGamma, iSup_image]
  rfl

/-- The undiscounted operator printed on p. 118:
`(Tv)(i', i) = sup_{0 ≤ i'' ≤ f(i' + i)} {u(f(i' + i) − i'') + v(i'', i')}`. -/
noncomputable def delayedPrinted (u f : ℝ → ℝ) (v : ℝ × ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  ⨆ y : Set.Icc (0 : ℝ) (f (s.1 + s.2)), u (f (s.1 + s.2) - y.1) + v (y.1, s.1)

/-- **AKMM, p. 118 and fn. 15: without `β` the Bellman operator is not a contraction.** With `u`
nondecreasing and `f ≥ 0`, the printed operator satisfies `T(0 + c) = T0 + c`, so no modulus
`β' < 1` bounds `|Tv − Tw|` by `β'` times a bound on `|v − w|`. -/
theorem delayed_no_discount_not_contraction {u f : ℝ → ℝ} (hu : MonotoneOn u (Set.Ici 0))
    (hf : ∀ x, 0 ≤ f x) :
    (∀ c s, delayedPrinted u f (fun _ => c) s = delayedPrinted u f (fun _ => 0) s + c) ∧
    ¬ ∃ β' < 1, ∀ v w : ℝ × ℝ → ℝ, (∀ s, |v s - w s| ≤ 1) →
      ∀ s, |delayedPrinted u f v s - delayedPrinted u f w s| ≤ β' := by
  have hshift : ∀ c s, delayedPrinted u f (fun _ => c) s =
      delayedPrinted u f (fun _ => 0) s + c := by
    intro c s
    have hne : Nonempty (Set.Icc (0 : ℝ) (f (s.1 + s.2))) :=
      ⟨⟨0, le_rfl, hf _⟩⟩
    have hbdd : BddAbove (Set.range fun y : Set.Icc (0 : ℝ) (f (s.1 + s.2)) =>
        u (f (s.1 + s.2) - y.1) + 0) := by
      refine ⟨u (f (s.1 + s.2)) + 0, ?_⟩
      rintro _ ⟨y, rfl⟩
      have := hu (Set.mem_Ici.2 (by linarith [y.2.2])) (Set.mem_Ici.2 (hf _))
        (by linarith [y.2.1] : f (s.1 + s.2) - y.1 ≤ f (s.1 + s.2))
      simp only [add_zero]
      exact this
    have := (OrderIso.addRight c).map_ciSup hbdd
    simp only [OrderIso.addRight_apply] at this
    simp only [delayedPrinted]
    rw [this]
    simp only [add_zero]
  refine ⟨hshift, fun ⟨β', hβ', h⟩ => ?_⟩
  have := h (fun _ => 1) (fun _ => 0) (fun _ => by norm_num) (0, 0)
  rw [hshift 1] at this
  simp only [add_sub_cancel_left, abs_one] at this
  linarith

/-- **AKMM, p. 119, property 1: value-function iteration.** Under SLP's Assumptions 4.3–4.4
(`Γ` nonempty, compact-valued and continuous; `F` bounded and continuous; `0 < β < 1`) the
Bellman operator has a unique fixed point `V`, the iterates satisfy
`‖V_{n+1} − V‖ ≤ β‖V_n − V‖`, and so `‖V_n − V‖ ≤ βⁿ‖V_0 − V‖ → 0` (SLP Theorem 4.6). -/
theorem property_1 {X : Type*} [MetricSpace X] [Nonempty X] {Γ : X → Set X} {F : X × X → ℝ}
    {β : ℝ} (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) :
    ∃ V : X →ᵇ ℝ, bellman h43 h44 V = V ∧ (∀ W, bellman h43 h44 W = W → W = V) ∧
      (∀ V₀ (n : ℕ), dist ((bellman h43 h44)^[n + 1] V₀) V ≤
        β * dist ((bellman h43 h44)^[n] V₀) V) ∧
      (∀ V₀ (n : ℕ), dist ((bellman h43 h44)^[n] V₀) V ≤ β ^ n * dist V₀ V) ∧
      ∀ V₀, Tendsto (fun n => (bellman h43 h44)^[n] V₀) atTop (𝓝 V) := by
  obtain ⟨V, hV, huniq, hrate, -⟩ := theorem_4_6 h43 h44
  have hc := bellman_contraction h43 h44
  refine ⟨V, hV, huniq, fun V₀ n => ?_, hrate, fun V₀ => ?_⟩
  · rw [Function.iterate_succ_apply']
    conv_lhs => rw [← hV]
    exact hc.2.2 _ _
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (hrate V₀) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h44.β_pos.le h44.β_lt).mul_const
      (dist V₀ V)

/-- **AKMM, p. 120, property 2.** If `F` is strictly increasing in its first argument and `Γ` is
monotone (`x ≤ x̃ ⇒ Γ(x) ⊆ Γ(x̃)`), `V` is strictly increasing (SLP Theorem 4.7). -/
theorem property_2 {X : Type*} [MetricSpace X] [Nonempty X] [PartialOrder X] {Γ : X → Set X}
    {F : X × X → ℝ} {β : ℝ} (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β)
    (h45 : ∀ x x' y, x < x' → y ∈ Γ x → F (x, y) < F (x', y))
    (h46 : ∀ x x', x ≤ x' → Γ x ⊆ Γ x') {V : X →ᵇ ℝ} (hV : bellman h43 h44 V = V) :
    StrictMono V :=
  theorem_4_7 h43 h44 h45 h46 hV

/-- **AKMM, p. 120, property 3.** If `F` is strictly concave and `Γ` convex
(`x' ∈ Γ(x), x̃' ∈ Γ(x̃) ⇒ θx' + (1 − θ)x̃' ∈ Γ(θx + (1 − θ)x̃)`), `V` is strictly concave and the
policy is unique (and continuous) (SLP Theorem 4.8). -/
theorem property_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    [Nonempty S] {hS : Convex ℝ S} {Γ : S → Set S} {F : S × S → ℝ} {β : ℝ}
    (h43 : Assumption43 Γ) (h44 : Assumption44 Γ F β) (h47 : Assumption47 hS Γ F)
    (h48 : Assumption48 hS Γ) {V : S →ᵇ ℝ} (hV : bellman h43 h44 V = V) :
    IsStrictConcaveS hS V ∧ (∀ x, argmax (obj F β V) Γ x = {argmaxFn Γ (obj F β V) x}) ∧
      Continuous (argmaxFn Γ (obj F β V)) := by
  obtain ⟨h1, -, h3, h4⟩ := theorem_4_8 h43 h44 h47 h48 hV
  exact ⟨h1, h3, h4⟩

/-- **AKMM, p. 120, property 4, and the envelope theorem (p. 122).** Let `V` be concave near
`x₀`, satisfy the Bellman inequality `F(x, x') + βV(x') ≤ V(x)` for `x' ∈ Γ(x)`, with equality at
`x' = g(x₀)`, and let the choice be interior (`g(x₀) ∈ Γ(x)` for `x` near `x₀`). If `F(·, g(x₀))`
is differentiable at `x₀`, then `V` is differentiable there and `V'(x₀) = F₁(x₀, g(x₀))`
(Benveniste–Scheinkman, SLP Theorem 4.10). -/
theorem property_4 {V : ℝ → ℝ} {S : Set ℝ} (hV : ConcaveOn ℝ S V) {x₀ y₀ : ℝ} (hS : S ∈ 𝓝 x₀)
    {Γ : ℝ → Set ℝ} {F : ℝ → ℝ → ℝ} {β F1 : ℝ}
    (hbell : ∀ x, ∀ y ∈ Γ x, F x y + β * V y ≤ V x) (heq : V x₀ = F x₀ y₀ + β * V y₀)
    (hint : ∀ᶠ x in 𝓝 x₀, y₀ ∈ Γ x) (hF : HasDerivAt (fun x => F x y₀) F1 x₀) :
    HasDerivAt V F1 x₀ := by
  have hW : HasDerivAt (fun x => F x y₀ + β * V y₀) F1 x₀ := hF.add_const _
  have := theorem_4_10 hV hS hW.hasFDerivAt heq.symm
    (hint.mono fun x hx => hbell x y₀ hx)
  simpa using this.hasDerivAt

/-- The return of the counterexample to property 5: `F(x, y) = 3x − x² − (y − 1 + x/2)²` on
`[0, 1]²`. -/
noncomputable def prop5F (x y : ℝ) : ℝ := 3 * x - x ^ 2 - (y - 1 + x / 2) ^ 2

/-- **AKMM, p. 120, property 5 is false as stated.** `F(x, y) = 3x − x² − (y − 1 + x/2)²` with
`X = [0, 1]` and `Γ(x) = [0, 1]` (monotone and convex) is jointly strictly concave, strictly
increasing in `x` and smooth. Yet for every continuous `V` on `[0, 1]` — in particular the
solution of the Bellman equation — a policy `g` (a maximizer of `F(x, y) + βV(y)` over `y`)
exists, and no policy is strictly increasing: since `F₁₂ < 0`, maximizers move down as `x`
rises. -/
theorem property_5_counterexample :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (fun p => prop5F p.1 p.2) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1, StrictMonoOn (fun x => prop5F x y) (Set.Icc 0 1)) ∧
    ContDiff ℝ 1 (fun p : ℝ × ℝ => prop5F p.1 p.2) ∧
    ∀ (β : ℝ) (V : ℝ → ℝ), ContinuousOn V (Set.Icc 0 1) →
      (∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ y ∈ Set.Icc (0 : ℝ) 1, prop5F x y + β * V y ≤ prop5F x (g x) + β * V (g x)) ∧
      ∀ g : ℝ → ℝ, (∀ x ∈ Set.Icc (0 : ℝ) 1, g x ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ y ∈ Set.Icc (0 : ℝ) 1, prop5F x y + β * V y ≤ prop5F x (g x) + β * V (g x)) →
        ¬ StrictMonoOn g (Set.Icc 0 1) := by
  refine ⟨⟨(convex_Icc 0 1).prod (convex_Icc 0 1), fun p hp q hq hpq a b ha hb hab => ?_⟩,
    fun y hy x hx x' hx' hxx' => ?_, ?_, fun β V hV => ⟨?_, fun g hg hmono => ?_⟩⟩
  · -- `θF(p) + (1 − θ)F(q) = F(θp + (1 − θ)q) − θ(1 − θ)Q(p − q)`, `Q` positive definite
    simp only [prop5F, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hQ : 0 < (p.1 - q.1) ^ 2 + (p.2 - q.2 + (p.1 - q.1) / 2) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have h1 : (p.1 - q.1) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (p.2 - q.2 +
        (p.1 - q.1) / 2)]) (sq_nonneg _)
      have h1' : p.1 = q.1 := by nlinarith [sq_nonneg (p.1 - q.1)]
      have h2 : (p.2 - q.2 + (p.1 - q.1) / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1)]
      have h2' : p.2 = q.2 := by rw [h1'] at h2; nlinarith [sq_nonneg (p.2 - q.2)]
      exact hpq (Prod.ext h1' h2')
    have hab' : 0 < a * (1 - a) := mul_pos ha hb
    nlinarith [mul_pos hab' hQ]
  · simp only [prop5F]
    have := hx.1; have := hx'.2; have := hy.2
    nlinarith [mul_pos (sub_pos.2 hxx') (show 0 < 4 - y - 5 / 4 * (x + x') by linarith)]
  · simp only [prop5F]
    fun_prop
  · -- a maximizer exists for each `x`: continuity on the compact `[0, 1]`
    have hex : ∀ x : ℝ, ∃ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
        prop5F x z + β * V z ≤ prop5F x y + β * V y := by
      intro x
      have hc : ContinuousOn (fun z => prop5F x z + β * V z) (Set.Icc 0 1) :=
        (Continuous.continuousOn (by unfold prop5F; fun_prop)).add (continuousOn_const.mul hV)
      obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one) hc
      exact ⟨y, hy, fun z hz => hmax hz⟩
    choose g hg using hex
    exact ⟨g, fun x _ => ⟨(hg x).1, (hg x).2⟩⟩
  · have h0 := hg 0 ⟨le_rfl, zero_le_one⟩
    have h1 := hg 1 ⟨zero_le_one, le_rfl⟩
    have hlt := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    have a1 := h0.2 (g 1) h1.1
    have a2 := h1.2 (g 0) h0.1
    simp only [prop5F] at a1 a2
    nlinarith

/-- **AKMM, p. 120, property 5, corrected (Topkis).** With `Γ(x) = [x̲, γ(x)]`, `γ` nondecreasing,
and strictly increasing differences
`F(x₂, y₂) − F(x₂, y₁) > F(x₁, y₂) − F(x₁, y₁)` for `x₁ < x₂`, `y₁ < y₂` (`F₁₂ > 0` for smooth
`F`), maximizers of `F(x, y) + βV(y)` are nondecreasing in `x`, for every `V`. -/
theorem property_5_corrected {F : ℝ → ℝ → ℝ} {V : ℝ → ℝ} {β lo : ℝ} {γ : ℝ → ℝ}
    (hγ : Monotone γ)
    (hid : ∀ x₁ x₂ y₁ y₂, x₁ < x₂ → y₁ < y₂ → F x₁ y₂ - F x₁ y₁ < F x₂ y₂ - F x₂ y₁)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) (hy₁ : y₁ ∈ Set.Icc lo (γ x₁))
    (hy₂ : y₂ ∈ Set.Icc lo (γ x₂))
    (hmax₁ : ∀ y ∈ Set.Icc lo (γ x₁), F x₁ y + β * V y ≤ F x₁ y₁ + β * V y₁)
    (hmax₂ : ∀ y ∈ Set.Icc lo (γ x₂), F x₂ y + β * V y ≤ F x₂ y₂ + β * V y₂) : y₁ ≤ y₂ := by
  by_contra hcon
  push Not at hcon
  have a1 := hmax₁ y₂ ⟨hy₂.1, by linarith [hy₁.2]⟩
  have a2 := hmax₂ y₁ ⟨hy₁.1, hy₁.2.trans (hγ hx.le)⟩
  have := hid x₁ x₂ y₂ y₁ hx hcon
  linarith

/-- **AKMM, p. 120, property 5 in the NGM.** In SLP's §6.1 setting (`U`, `f` strictly increasing,
strictly concave, `C¹`, with Inada conditions; `f` is total resources), the optimal policy is
strictly increasing on `[0, k̄]` (SLP Exercise 6.1b). -/
theorem property_5_ngm {U f U' f' : ℝ → ℝ} {β kbar : ℝ} [Nonempty (Set.Icc (0 : ℝ) kbar)]
    {v : Set.Icc (0 : ℝ) kbar →ᵇ ℝ}
    (S : StokeyLucasPrescott.DeterministicDynamics.Setting61 U f U' f' β kbar v) :
    StrictMonoOn (StokeyLucasPrescott.DeterministicDynamics.gpol U f β kbar v) (Set.Icc 0 kbar) :=
  StokeyLucasPrescott.DeterministicDynamics.ex_6_1b S

end AKMM.DynamicOptimization
