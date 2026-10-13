/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.BoundedReturns

/-!
# Finite or countable state spaces and policy iteration

SLP Exercise 4.4, pp. 82–83. `X` carries the discrete topology, so `X →ᵇ ℝ` is `B(X)`, the
bounded functions with the sup norm; `Γ` is nonempty and finite-valued; `F` is bounded on the
graph; `0 < β < 1`. (Countability of `X` is not used.)

* `bellmanD` (`T`), `ex_4_4a`: `T` maps `B(X)` into itself, has a unique fixed point `v`,
  `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the policy correspondence is nonempty.
* `policyOp` (`T_h`), `ex_4_4b`: for a feasible policy `h`, `T_h` has a unique fixed point.
* `ex_4_4c`: policy iteration. From any feasible `h₀`, alternate the value `wₙ` of `hₙ` with an
  improving policy `hₙ₊₁`; then `wₙ → v`, and `Tⁿw₀ ≤ wₙ ≤ v`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDP

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {Γ : X → Set X} {F : X → X → ℝ}
  {β : ℝ}

/-- The hypotheses of Exercise 4.4. -/
structure DiscreteSetup (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) : Prop where
  nonempty : ∀ x, (Γ x).Nonempty
  finite : ∀ x, (Γ x).Finite
  bdd : ∃ B, ∀ x, ∀ y ∈ Γ x, |F x y| ≤ B
  β_pos : 0 < β
  β_lt : β < 1

/-- `max_{y ∈ Γ(x)} [F(x, y) + βf(y)]`. -/
noncomputable def maxD (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  sSup ((fun y => F x y + β * f y) '' Γ x)

omit [TopologicalSpace X] [DiscreteTopology X] in
theorem exists_maxD (h : DiscreteSetup Γ F β) (f : X → ℝ) (x : X) :
    ∃ y ∈ Γ x, maxD Γ F β f x = F x y + β * f y ∧ ∀ z ∈ Γ x, F x z + β * f z ≤ F x y + β * f y := by
  obtain ⟨y, hy, hmax⟩ := Set.exists_max_image (Γ x) (fun y => F x y + β * f y) (h.finite x)
    (h.nonempty x)
  have hgr : IsGreatest ((fun y => F x y + β * f y) '' Γ x) (F x y + β * f y) :=
    ⟨⟨y, hy, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz⟩
  exact ⟨y, hy, hgr.csSup_eq, hmax⟩

omit [TopologicalSpace X] [DiscreteTopology X] in
theorem le_maxD (h : DiscreteSetup Γ F β) (f : X → ℝ) {x y : X} (hy : y ∈ Γ x) :
    F x y + β * f y ≤ maxD Γ F β f x := by
  obtain ⟨z, -, hz, hmax⟩ := exists_maxD h f x
  rw [hz]; exact hmax y hy

/-- The operator `T` on `B(X)`. -/
noncomputable def bellmanD (h : DiscreteSetup Γ F β) (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (maxD Γ F β f) (h.bdd.choose + β * ‖f‖) fun x => by
    obtain ⟨y, hy, hval, -⟩ := exists_maxD h f x
    rw [hval, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add (h.bdd.choose_spec x y hy) ?_)
    rw [abs_mul, abs_of_pos h.β_pos]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) h.β_pos.le

theorem bellmanD_apply (h : DiscreteSetup Γ F β) (f : X →ᵇ ℝ) (x : X) :
    bellmanD h f x = maxD Γ F β f x := rfl

theorem bellmanD_mono (h : DiscreteSetup Γ F β) {f g : X →ᵇ ℝ} (hfg : f ≤ g) :
    bellmanD h f ≤ bellmanD h g := fun x => by
  change maxD Γ F β f x ≤ maxD Γ F β g x
  obtain ⟨y, hy, hval, -⟩ := exists_maxD h f x
  rw [hval]
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (show f y ≤ g y from hfg y)
    h.β_pos.le)).trans (le_maxD h g hy)

theorem bellmanD_add_const (h : DiscreteSetup Γ F β) (f : X →ᵇ ℝ) (a : ℝ) :
    bellmanD h (f + const X a) ≤ bellmanD h f + const X (β * a) := fun x => by
  obtain ⟨y, hy, hval, -⟩ := exists_maxD h (f + const X a) x
  have h1 := le_maxD h f hy
  have e : bellmanD h (f + const X a) x = F x y + β * (f y + a) := by
    rw [bellmanD_apply, BoundedContinuousFunction.coe_add, hval]; simp
  have e2 : (bellmanD h f + const X (β * a)) x = maxD Γ F β f x + β * a := by
    simp [bellmanD_apply]
  change bellmanD h (f + const X a) x ≤ (bellmanD h f + const X (β * a)) x
  rw [e, e2]
  linarith

theorem bellmanD_contraction (h : DiscreteSetup Γ F β) : IsContraction (bellmanD h) β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => bellmanD_mono h)
    (fun f a _ => bellmanD_add_const h f a)⟩

/-- **Exercise 4.4a.** `T : B(X) → B(X)` has a unique fixed point `v`, (4) holds, and the
policy correspondence `G(x) = {y ∈ Γ(x) : v(x) = F(x, y) + βv(y)}` is nonempty. -/
theorem ex_4_4a (h : DiscreteSetup Γ F β) :
    ∃ v : X →ᵇ ℝ, bellmanD h v = v ∧ (∀ w, bellmanD h w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellmanD h)^[n] v₀) v ≤ β ^ n * dist v₀ v) ∧
      ∀ x, ∃ y ∈ Γ x, v x = F x y + β * v y := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 (bellmanD_contraction h)
  refine ⟨v, hv, huniq, hrate, fun x => ?_⟩
  obtain ⟨y, hy, hval, -⟩ := exists_maxD h v x
  refine ⟨y, hy, ?_⟩
  rw [← hval, ← bellmanD_apply h, hv]

/-- The policy operator `(T_h f)(x) = F(x, h(x)) + βf(h(x))`. -/
noncomputable def policyOp (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun x => F x (hp x) + β * f (hp x)) (h.bdd.choose + β * ‖f‖)
    fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add (h.bdd.choose_spec x _ (hhp x)) ?_)
      rw [abs_mul, abs_of_pos h.β_pos]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) h.β_pos.le

theorem policyOp_apply (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    (f : X →ᵇ ℝ) (x : X) : policyOp h hp hhp f x = F x (hp x) + β * f (hp x) := rfl

theorem policyOp_mono (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    {f g : X →ᵇ ℝ} (hfg : f ≤ g) : policyOp h hp hhp f ≤ policyOp h hp hhp g := fun x => by
  change F x (hp x) + β * f (hp x) ≤ F x (hp x) + β * g (hp x)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (show f (hp x) ≤ g (hp x) from hfg _)
    h.β_pos.le)

theorem policyOp_contraction (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x) :
    IsContraction (policyOp h hp hhp) β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => policyOp_mono h hp hhp)
    (fun f a _ x => by
      change F x (hp x) + β * (f + const X a) (hp x) ≤
        (policyOp h hp hhp f + const X (β * a)) x
      simp only [BoundedContinuousFunction.add_apply, const_apply, policyOp_apply]
      linarith)⟩

/-- **Exercise 4.4b.** For every feasible policy `h`, `T_h : B(X) → B(X)` has a unique fixed
point. -/
theorem ex_4_4b (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x) :
    ∃ w : X →ᵇ ℝ, policyOp h hp hhp w = w ∧ ∀ w', policyOp h hp hhp w' = w' → w' = w := by
  obtain ⟨w, hw, huniq, -⟩ := theorem_3_2 (policyOp_contraction h hp hhp)
  exact ⟨w, hw, huniq⟩

/-- `T_h ≤ T`. -/
theorem policyOp_le_bellmanD (h : DiscreteSetup Γ F β) (hp : X → X) (hhp : ∀ x, hp x ∈ Γ x)
    (f : X →ᵇ ℝ) : policyOp h hp hhp f ≤ bellmanD h f := fun x =>
  le_maxD h f (hhp x)

omit [DiscreteTopology X] in
/-- `{f : g ≤ f}` and `{f : f ≤ g}` are closed in `B(X)`. -/
theorem isClosed_ge (g : X →ᵇ ℝ) : IsClosed {f : X →ᵇ ℝ | g ≤ f} := by
  have : {f : X →ᵇ ℝ | g ≤ f} = ⋂ x, {f : X →ᵇ ℝ | g x ≤ f x} := by
    ext f; simp only [mem_ofPred_eq, mem_iInter]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_eval_const x)

omit [DiscreteTopology X] in
theorem isClosed_le' (g : X →ᵇ ℝ) : IsClosed {f : X →ᵇ ℝ | f ≤ g} := by
  have : {f : X →ᵇ ℝ | f ≤ g} = ⋂ x, {f : X →ᵇ ℝ | f x ≤ g x} := by
    ext f; simp only [mem_ofPred_eq, mem_iInter]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun x => isClosed_le (continuous_eval_const x) continuous_const

/-- **Exercise 4.4c (policy iteration).** Let `hₙ` be feasible policies and `wₙ` the fixed point
of `T_{hₙ}`, with `hₙ₊₁(x)` maximizing `F(x, y) + βwₙ(y)` over `Γ(x)`. Then
`w₀ ≤ Tw₀ ≤ w₁ ≤ Tw₁ ≤ ⋯`, `Tⁿw₀ ≤ wₙ ≤ v`, and `wₙ → v`. -/
theorem ex_4_4c (h : DiscreteSetup Γ F β) {v : X →ᵇ ℝ} (hv : bellmanD h v = v)
    (hp : ℕ → X → X) (hhp : ∀ n x, hp n x ∈ Γ x) (w : ℕ → X →ᵇ ℝ)
    (hw : ∀ n, policyOp h (hp n) (hhp n) (w n) = w n)
    (himp : ∀ n x, ∀ y ∈ Γ x, F x y + β * w n y ≤ F x (hp (n + 1) x) + β * w n (hp (n + 1) x)) :
    (∀ n, w n ≤ bellmanD h (w n) ∧ bellmanD h (w n) ≤ w (n + 1)) ∧
      (∀ n, (bellmanD h)^[n] (w 0) ≤ w n ∧ w n ≤ v) ∧ Tendsto w atTop (𝓝 v) := by
  -- `wₙ ≤ Twₙ`
  have h1 : ∀ n, w n ≤ bellmanD h (w n) := fun n => by
    rw [← hw n]
    exact (policyOp_le_bellmanD h _ _ _).trans (bellmanD_mono h (le_of_eq (hw n).symm))
  -- `Twₙ = T_{hₙ₊₁} wₙ`
  have h2 : ∀ n, bellmanD h (w n) = policyOp h (hp (n + 1)) (hhp (n + 1)) (w n) := fun n => by
    ext x
    refine le_antisymm ?_ (policyOp_le_bellmanD h _ _ _ x)
    change maxD Γ F β (w n) x ≤ _
    obtain ⟨y, hy, hval, -⟩ := exists_maxD h (w n) x
    rw [hval, policyOp_apply]
    exact himp n x y hy
  -- `Twₙ ≤ wₙ₊₁`: the set `{f : Twₙ ≤ f}` is closed and invariant under `T_{hₙ₊₁}`
  have h3 : ∀ n, bellmanD h (w n) ≤ w (n + 1) := fun n => by
    set g := bellmanD h (w n)
    have hinv : MapsTo (policyOp h (hp (n + 1)) (hhp (n + 1))) {f | g ≤ f} {f | g ≤ f} :=
      fun f hf => by
        have hg : g ≤ policyOp h (hp (n + 1)) (hhp (n + 1)) g := by
          have := policyOp_mono h (hp (n + 1)) (hhp (n + 1)) (h1 n)
          rwa [← h2 n] at this
        exact hg.trans (policyOp_mono h _ _ hf)
    exact (corollary_1 (S' := {f | g ≤ f}) (S'' := {f | g ≤ f}) (policyOp_contraction h _ _)
      (hw (n + 1)) ⟨g, (le_refl g : g ≤ g)⟩ (isClosed_ge g)
      hinv hinv).1
  -- `wₙ ≤ v`: the set `{f : f ≤ v}` is closed and invariant under `T_{hₙ}`
  have h4 : ∀ n, w n ≤ v := fun n => by
    have hinv : MapsTo (policyOp h (hp n) (hhp n)) {f | f ≤ v} {f | f ≤ v} := fun f hf =>
      (policyOp_le_bellmanD h _ _ f).trans ((bellmanD_mono h hf).trans (le_of_eq hv))
    exact (corollary_1 (S' := {f | f ≤ v}) (S'' := {f | f ≤ v}) (policyOp_contraction h _ _)
      (hw n) ⟨v, (le_refl v : v ≤ v)⟩ (isClosed_le' v)
      hinv hinv).1
  -- `Tⁿw₀ ≤ wₙ`
  have h5 : ∀ n, (bellmanD h)^[n] (w 0) ≤ w n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (bellmanD_mono h ih).trans (h3 n)
  refine ⟨fun n => ⟨h1 n, h3 n⟩, fun n => ⟨h5 n, h4 n⟩, ?_⟩
  -- squeeze: `dist (wₙ) v ≤ dist (Tⁿw₀) v → 0`
  obtain ⟨v', hv', huniq, hrate⟩ := theorem_3_2 (bellmanD_contraction h)
  rw [← huniq v hv] at hrate
  have hT : Tendsto (fun n => (bellmanD h)^[n] (w 0)) atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => hrate (w 0) n) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.β_pos.le h.β_lt).mul_const
      (dist (w 0) v)
  rw [tendsto_iff_dist_tendsto_zero] at hT ⊢
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hT
  refine (dist_le dist_nonneg).2 fun x => ?_
  have a1 : (bellmanD h)^[n] (w 0) x ≤ w n x := h5 n x
  have a2 : w n x ≤ v x := h4 n x
  have a3 := dist_coe_le_dist (f := (bellmanD h)^[n] (w 0)) (g := v) x
  rw [Real.dist_eq] at a3 ⊢
  rw [abs_of_nonpos (by linarith)] at ⊢
  rw [abs_of_nonpos (by linarith)] at a3
  linarith

end StokeyLucasPrescott.DeterministicDP
