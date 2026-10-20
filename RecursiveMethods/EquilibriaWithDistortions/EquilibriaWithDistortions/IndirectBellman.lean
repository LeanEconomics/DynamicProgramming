/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectDP

/-!
# Existence of the bounded solution of (2)/(3), and the planner's problem

SLP §18.1, pp. 543–546, the bounded case.

**Existence.** The Bellman operator of the individual's functional equation,
`(Tw)(x, k) = sup_{y ∈ Γ(x, k)} {U[A(k) + B(k) x − y] + β w(y, g(k))}` (`bellOp`), acts on the
Banach space `ℓ^∞` of bounded functions on the state set `{(x, k) : x ≥ 0, k ∈ K}`
(`DPState`, `lp (fun _ => ℝ) ⊤`; no continuity is needed). Only boundedness of `U` and
nonemptiness of `Γ` are used: `T` maps `ℓ^∞` into itself (`bellOp_abs_le`) and
`|Tw − Tw′| ≤ β ‖w − w′‖` (`bellOp_sub_le`), so it is a `β`-contraction (`bellLp_contracting`)
and has a fixed point (`exists_bellman_solution`), the unique bounded solution
(`bellman_unique`).

**The planner.** If the planner's path `k_{t+1} = g(k_t)` satisfies the planner's Euler equation
and transversality condition, it is optimal in the planner's sequence problem
(`planner_optimal`): with `a_t = f(k_t) − k_t f′(k_t)`, `b_t = f′(k_t)`, concavity of `f` gives
`f(k′_t) − k′_{t+1} ≤ a_t + b_t k′_t − k′_{t+1}`, so any planner-feasible path is feasible for the
individual facing the planner's prices and does no better there, where `euler_tvc_optimal`
applies. So the planner's value is the full maximum of `∑ β^t U(f(k_t) − k_{t+1})`
(`plannerValues`).

**Exercise 18.1 and the taxed economy, with existence** (`ex_18_1_full`,
`indirect_equilibrium_full`). The bounded solution `V` of (2) exists and is unique;
`V(k, k; g) = v(k)` where `v(k)` is the maximal value of the planner's sequence problem; and
`G(k, k; g) = g(k)` is the unique optimal choice. For (3) with `h = ĥ`: the bounded solution
exists and is unique, `ĥ` is optimal in the pseudo-economy (8) with discount factor `(1 − θ)β`,
and `H(k, k; ĥ) = ĥ(k)`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- The state set `{(x, k) : x ≥ 0, k ∈ K}`. -/
abbrev DPState (K : Set ℝ) : Type := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.2 ∈ K}

/-- Extension of a function on states to `ℝ × ℝ` by `0`. -/
noncomputable def wExt {K : Set ℝ} (w : DPState K → ℝ) (x k : ℝ) : ℝ :=
  @dite _ (0 ≤ x ∧ k ∈ K) (Classical.propDecidable _) (fun h => w ⟨(x, k), h⟩) fun _ => 0

/-- `wExt w = w` on states. -/
theorem wExt_of_mem {K : Set ℝ} (w : DPState K → ℝ) {x k : ℝ} (h : 0 ≤ x ∧ k ∈ K) :
    wExt w x k = w ⟨(x, k), h⟩ := by
  simp [wExt, h.1, h.2]

/-- The Bellman operator of the individual's functional equation (2)/(3). -/
noncomputable def bellOp (U A B g : ℝ → ℝ) (β : ℝ) {K : Set ℝ} (w : DPState K → ℝ)
    (s : DPState K) : ℝ :=
  sSup ((fun y => U (A s.1.2 + B s.1.2 * s.1.1 - y) + β * wExt w y (g s.1.2)) ''
    feasY A B s.1.1 s.1.2)

/-- `T` maps bounded functions to bounded functions: `|w| ≤ M ⇒ |Tw| ≤ B₀ + βM`. -/
theorem bellOp_abs_le {U A B g : ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k)
    (hB : ∀ k ∈ K, 0 ≤ B k) {w : DPState K → ℝ} (hw : ∀ s, |w s| ≤ M) (s : DPState K) :
    |bellOp U A B g β w s| ≤ B₀ + β * M := by
  obtain ⟨⟨x, k⟩, hx, hk⟩ := s
  have h0 : (0 : ℝ) ∈ feasY A B x k :=
    ⟨le_rfl, by have := mul_nonneg (hB k hk) hx; linarith [hA k hk]⟩
  have hel : ∀ y ∈ feasY A B x k,
      |U (A k + B k * x - y) + β * wExt w y (g k)| ≤ B₀ + β * M := by
    intro y hy
    rw [wExt_of_mem w ⟨hy.1, hK k hk⟩]
    have h1 := hU _ hy.2
    have h2 := mul_le_mul_of_nonneg_left (hw ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩) hβ0
    calc _ ≤ |U (A k + B k * x - y)| + |β * w ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩| := abs_add_le _ _
      _ ≤ B₀ + β * M := by rw [abs_mul, abs_of_nonneg hβ0]; linarith
  have hne : ((fun y => U (A k + B k * x - y) + β * wExt w y (g k)) '' feasY A B x k).Nonempty :=
    ⟨_, 0, h0, rfl⟩
  have hbdd : BddAbove ((fun y => U (A k + B k * x - y) + β * wExt w y (g k)) ''
      feasY A B x k) :=
    ⟨B₀ + β * M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.1 (hel y hy)).2⟩
  rw [abs_le]
  constructor
  · exact (abs_le.1 (hel 0 h0)).1.trans (le_csSup hbdd ⟨0, h0, rfl⟩)
  · exact csSup_le hne (by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.1 (hel y hy)).2)

/-- **The `β`-contraction estimate**: `|w − w′| ≤ D ⇒ |Tw − Tw′| ≤ βD`. -/
theorem bellOp_sub_le {U A B g : ℝ → ℝ} {β B₀ M M' D : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k)
    (hB : ∀ k ∈ K, 0 ≤ B k) {w w' : DPState K → ℝ} (hw : ∀ s, |w s| ≤ M)
    (hw' : ∀ s, |w' s| ≤ M') (hD : ∀ s, |w s - w' s| ≤ D) (s : DPState K) :
    |bellOp U A B g β w s - bellOp U A B g β w' s| ≤ β * D := by
  have key : ∀ (v v' : DPState K → ℝ) (N N' : ℝ), (∀ s, |v s| ≤ N) → (∀ s, |v' s| ≤ N') →
      (∀ s, v s - v' s ≤ D) → bellOp U A B g β v s ≤ bellOp U A B g β v' s + β * D := by
    intro v v' N N' hv hv' hvD
    obtain ⟨⟨x, k⟩, hx, hk⟩ := s
    have h0 : (0 : ℝ) ∈ feasY A B x k :=
      ⟨le_rfl, by have := mul_nonneg (hB k hk) hx; linarith [hA k hk]⟩
    have hbdd' : BddAbove ((fun y => U (A k + B k * x - y) + β * wExt v' y (g k)) ''
        feasY A B x k) := by
      refine ⟨B₀ + β * N', ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      beta_reduce
      rw [wExt_of_mem v' ⟨hy.1, hK k hk⟩]
      have h1 := (abs_le.1 (hU _ hy.2)).2
      have h2 := mul_le_mul_of_nonneg_left (abs_le.1 (hv' ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩)).2 hβ0
      linarith
    refine csSup_le ⟨_, 0, h0, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hmem := le_csSup hbdd' ⟨y, hy, rfl⟩
    beta_reduce at hmem ⊢
    rw [wExt_of_mem v ⟨hy.1, hK k hk⟩]
    rw [wExt_of_mem v' ⟨hy.1, hK k hk⟩] at hmem
    have h3 := mul_le_mul_of_nonneg_left (hvD ⟨(y, g k), ⟨hy.1, hK k hk⟩⟩) hβ0
    change U (A k + B k * x - y) + β * v ⟨(y, g k), _⟩ ≤
      sSup ((fun y => U (A k + B k * x - y) + β * wExt v' y (g k)) '' feasY A B x k) + β * D
    nlinarith
  rw [abs_le]
  constructor
  · have := key w' w M' M hw' hw (fun s => by have := abs_le.1 (hD s); linarith)
    linarith
  · have := key w w' M M' hw hw' (fun s => (abs_le.1 (hD s)).2)
    linarith

/-- The Bellman operator on `ℓ^∞(DPState K)`. -/
noncomputable def bellLp (U A B g : ℝ → ℝ) (β B₀ : ℝ) {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k)
    (hB : ∀ k ∈ K, 0 ≤ B k) (w : lp (fun _ : DPState K => ℝ) ⊤) :
    lp (fun _ : DPState K => ℝ) ⊤ :=
  ⟨bellOp U A B g β (fun s => w s), memℓp_infty ⟨B₀ + β * ‖w‖, by
    rintro _ ⟨s, rfl⟩
    exact bellOp_abs_le hβ0 hU hK hA hB
      (fun s => lp.norm_apply_le_norm ENNReal.top_ne_zero w s) s⟩⟩

/-- **The Bellman operator is a `β`-contraction** of `ℓ^∞` (sup norm). -/
theorem bellLp_contracting {U A B g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) :
    ContractingWith (Real.toNNReal β) (bellLp U A B g β B₀ hβ0 hU hK hA hB) := by
  refine ⟨Real.toNNReal_lt_one.2 hβ1, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
  rw [Real.coe_toNNReal _ hβ0, dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (mul_nonneg hβ0 (norm_nonneg _)) fun s => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  refine bellOp_sub_le hβ0 hU hK hA hB (fun s => lp.norm_apply_le_norm ENNReal.top_ne_zero w s)
    (fun s => lp.norm_apply_le_norm ENNReal.top_ne_zero w' s) (fun s => ?_) s
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero (w - w') s
  rwa [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at this

/-- **Existence of the bounded solution** of the individual's functional equation (2)/(3):
for `0 ≤ β < 1`, `U` bounded on `[0, ∞)`, `K` invariant under `g`, and `A, B ≥ 0` on `K`
(so `Γ(x, k) ∋ 0` is nonempty), there is a bounded `W` solving the functional equation on
`[0, ∞) × K`: the fixed point of the contraction `bellLp`. -/
theorem exists_bellman_solution {U A B g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U A B g W β K := by
  have hT := bellLp_contracting hβ0 hβ1 hU hK hA hB
  set w := ContractingWith.fixedPoint _ hT with hw
  have hfix : bellLp U A B g β B₀ hβ0 hU hK hA hB w = w :=
    ContractingWith.fixedPoint_isFixedPt (f := bellLp U A B g β B₀ hβ0 hU hK hA hB) hT
  refine ⟨wExt fun s => w s, ‖w‖, fun x hx k hk => ?_, fun x hx k hk => ?_⟩
  · rw [wExt_of_mem _ ⟨hx, hk⟩]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero w _
  · rw [wExt_of_mem _ ⟨hx, hk⟩]
    have := congrArg (fun v : lp (fun _ : DPState K => ℝ) ⊤ => v ⟨(x, k), ⟨hx, hk⟩⟩) hfix
    simp only at this
    rw [← this]
    rfl

/-! ### The planner's problem -/

/-- The values `∑ β^t U(f(k_t) − k_{t+1})` of the planner's feasible paths from `k₀`
(`k_t ≥ 0`, `0 ≤ k_{t+1} ≤ f(k_t)`). -/
def plannerValues (U f : ℝ → ℝ) (β k₀ : ℝ) : Set ℝ :=
  {S | ∃ k : ℕ → ℝ, k 0 = k₀ ∧ (∀ t, 0 ≤ k t ∧ 0 ≤ f (k t) - k (t + 1)) ∧
    HasSum (fun t => β ^ t * U (f (k t) - k (t + 1))) S}

/-- **Sufficiency of Euler + transversality for the planner** (Theorem 4.15 for §18.1 (1)). Let
`U` be concave, nondecreasing, differentiable with `U′ ≥ 0` and bounded on `[0, ∞)`,
`0 ≤ β < 1`, `f` concave on `[0, ∞)`, and let the path `ks` (`ks_t ≥ 0`, `f(ks_t) − ks_{t+1} ≥ 0`,
`f` differentiable at `ks_t` with `f′(ks_t) ≥ 0`) satisfy the planner's Euler equation and
transversality condition. Then its value is the greatest value of the planner's problem. -/
theorem planner_optimal {U f : ℝ → ℝ} {β B₀ : ℝ} {ks : ℕ → ℝ} (hU : ConcaveOn ℝ (Ici 0) U)
    (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ t, DifferentiableAt ℝ f (ks t)) (hf' : ∀ t, 0 ≤ deriv f (ks t))
    (hks : ∀ t, 0 ≤ ks t) (hc : ∀ t, 0 ≤ f (ks t) - ks (t + 1))
    (heul : ∀ t, deriv U (f (ks t) - ks (t + 1)) =
      β * deriv U (f (ks (t + 1)) - ks (t + 2)) * deriv f (ks (t + 1)))
    (htvc : Tendsto (fun t => β ^ t * deriv U (f (ks t) - ks (t + 1)) * deriv f (ks t) * ks t)
      atTop (𝓝 0)) :
    IsGreatest (plannerValues U f β (ks 0)) (∑' t, β ^ t * U (f (ks t) - ks (t + 1))) := by
  have hsumb : ∀ c : ℕ → ℝ, (∀ t, 0 ≤ c t) → Summable fun t => β ^ t * U (c t) := by
    intro c hc0
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hUb _ (hc0 t)) (pow_nonneg hβ0 t)
  have hS' := (hsumb _ hc).hasSum
  refine ⟨⟨ks, rfl, fun t => ⟨hks t, hc t⟩, hS'⟩, ?_⟩
  rintro S ⟨k, hk0, hk, hS⟩
  set a : ℕ → ℝ := fun t => f (ks t) - ks t * deriv f (ks t) with ha
  set b : ℕ → ℝ := fun t => deriv f (ks t) with hb
  have hcons : ∀ t, consPath a b ks t = f (ks t) - ks (t + 1) := fun t => by
    simp only [consPath, ha, hb]
    ring
  -- the planner's feasible path does no better in the individual's problem at the planner's prices
  have htan : ∀ t, f (k t) - k (t + 1) ≤ consPath a b k t := fun t => by
    have := concave_le_tangent hf (hk t).1 (hks t) (hfd t)
    simp only [consPath, ha, hb]
    linarith
  have hfeas : IndivFeasible a b (ks 0) k :=
    ⟨hk0, fun t => ⟨(hk t).1, ((hk t).2).trans (htan t)⟩⟩
  have hS2 := (hsumb _ fun t => (hfeas.2 t).2).hasSum
  have hle1 : S ≤ ∑' t, β ^ t * U (consPath a b k t) :=
    hasSum_le (fun t => mul_le_mul_of_nonneg_left (hUm (mem_Ici.2 (hk t).2)
      (mem_Ici.2 (hfeas.2 t).2) (htan t)) (pow_nonneg hβ0 t)) hS hS2
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b ks t) := fun t =>
    hUd _ ((hcons t).symm ▸ hc t)
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b ks t) := fun t =>
    mul_nonneg (hf' t) (hU' _ ((hcons t).symm ▸ hc t))
  have heul' : ∀ t, deriv U (consPath a b ks t) =
      β * b (t + 1) * deriv U (consPath a b ks (t + 1)) := fun t => by
    rw [hcons, hcons, heul t, hb]
    ring
  have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b ks T) * ks T) atTop
      (𝓝 0) := by
    refine htvc.congr fun t => ?_
    rw [hcons, hb]
    ring
  have hv' : HasSum (fun t => β ^ t * U (consPath a b ks t))
      (∑' t, β ^ t * U (f (ks t) - ks (t + 1))) := by
    simpa only [hcons] using hS'
  exact hle1.trans (euler_tvc_optimal hU hβ0 hUd' (fun t => (hcons t).symm ▸ hc t) hp heul'
    htvc' hfeas hS2 hv')

/-! ### The value of following a policy -/

/-- The value `∑ β^t U[F(k_t) − k_{t+1}]` of the path `k_t = g^t(k)`. -/
noncomputable def pathValue (U Fk g : ℝ → ℝ) (β k : ℝ) : ℝ :=
  ∑' t, β ^ t * U (Fk (g^[t] k) - g (g^[t] k))

/-- `pathValue` is bounded by `B₀/(1 − β)` and satisfies the policy equation
`v(k) = U[F(k) − g(k)] + β v(g(k))` on an invariant `K` with `F − g ≥ 0`. -/
theorem pathValue_spec {U Fk g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K)
    (hc : ∀ k ∈ K, 0 ≤ Fk k - g k) :
    (∀ k ∈ K, |pathValue U Fk g β k| ≤ (1 - β)⁻¹ * B₀) ∧
      ∀ k ∈ K, pathValue U Fk g β k = U (Fk k - g k) + β * pathValue U Fk g β (g k) := by
  have hgeo := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right B₀
  have hsum : ∀ k ∈ K, Summable fun t => β ^ t * U (Fk (g^[t] k) - g (g^[t] k)) := by
    intro k hk
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hUb _ (hc _ (iterate_mem hK hk t))) (pow_nonneg hβ0 t)
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hb : ∀ t, |β ^ t * U (Fk (g^[t] k) - g (g^[t] k))| ≤ β ^ t * B₀ := fun t => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (hUb _ (hc _ (iterate_mem hK hk t))) (pow_nonneg hβ0 t)
    rw [abs_le]
    constructor
    · have := hasSum_le (fun t => (abs_le.1 (hb t)).1) hgeo.neg (hsum k hk).hasSum
      simp only [pathValue]
      linarith
    · exact hasSum_le (fun t => (abs_le.1 (hb t)).2) (hsum k hk).hasSum hgeo
  · simp only [pathValue]
    rw [(hsum k hk).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, Function.iterate_zero, id]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [Function.iterate_succ_apply, pow_succ]
    ring

/-! ### Exercise 18.1 and the taxed economy, with existence -/

/-- **Exercise 18.1, complete** (p. 544). Let `0 < β < 1`; `U` strictly concave on `[0, ∞)`,
differentiable with `U′ ≥ 0` and bounded there; `f` concave on `[0, ∞)`; `K ⊆ [0, ∞)` invariant
under `g`, with `f` differentiable, `f′ ≥ 0`, `f(k) − k f′(k) ≥ 0`, `f(k) − g(k) ≥ 0` on `K`; and
let `g` satisfy the planner's Euler equation and transversality condition. Then:
(i) the individual's functional equation (2) has a bounded solution `V` on `[0, ∞) × K`, and any
two bounded solutions agree;
(ii) for `k ∈ K`, `V(k, k; g) = v(k)`, the maximal value of the planner's problem from `k`
(attained by the path of `g`);
(iii) `G(k, k; g) = g(k)`: `y` is optimal in (2) at `(k, k)` iff `y = g(k)`. -/
theorem ex_18_1_full {U f g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k) (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0)) :
    ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K ∧
      (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ K, |V' x k| ≤ M') →
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V' β K →
          ∀ x, 0 ≤ x → ∀ k ∈ K, V' x k = V x k) ∧
      ∀ k ∈ K, IsGreatest (plannerValues U f β k) (V k k) ∧
        ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
          (U (f k + (k - k) * deriv f k - y) + β * V y (g k) = V k k ↔ y = g k) := by
  obtain ⟨V, M, hVb, hsol⟩ := exists_bellman_solution (U := U) (g := g)
    (A := fun k => f k - k * deriv f k) (B := deriv f) hβ0.le hβ1 hUb hK hw hf'
  obtain ⟨hvb, hpol⟩ := pathValue_spec (Fk := f) hβ0.le hβ1 hUb hK hc
  have hUm : MonotoneOn U (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun c hc => (hUd c hc).continuousAt.continuousWithinAt)
      (fun c hc => (hUd c (interior_subset hc)).differentiableWithinAt) fun c hc => ?_
    exact hU' c (interior_subset hc)
  refine ⟨V, M, hVb, hsol, fun V' M' hV' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hV' hVb hK hw hf' hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := ex_18_1_dp hU hβ0 hβ1 hUd hU' hUb hK hK0 hf' hw hc heul htvc hvb hpol
    hVb hsol k hk
  refine ⟨?_, h4⟩
  have hkt := iterate_mem hK hk
  have hP := planner_optimal (ks := fun t => g^[t] k) hU.concaveOn hUm hβ0.le hβ1 hUb hUd hU'
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      exact heul _ (hkt t))
    (by simpa only [Function.iterate_succ_apply'] using htvc k hk)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  rw [h1]
  exact hP

/-- **The taxed economy (3), complete** (pp. 545–546). Tax `θ ∈ [0, 1)` on capital income,
rebated. Let `ĥ` satisfy the Euler equation of the pseudo-economy (8) with discount factor
`(1 − θ)β` and the individual's transversality condition (hypotheses as in `ex_18_1_full`).
Then: the functional equation (3) with `h = ĥ` has a bounded solution `W`, unique among bounded
solutions; the path of `ĥ` is optimal in the pseudo-economy (its value is the maximal value of
the pseudo-planner's problem with discount factor `(1 − θ)β`); `W(k, k; ĥ)` is the individual's
value of following `ĥ`; and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice at `(k, k)`, so `ĥ`
is a recursive competitive equilibrium. -/
theorem indirect_equilibrium_full {U f h : ℝ → ℝ} {β θ B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hfd : ∀ k ∈ K, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ K, 0 ≤ deriv f k)
    (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k) (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0)) :
    ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) ∧
      SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
        (fun k => (1 - θ) * deriv f k) h W β K ∧
      (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ K, |W' x k| ≤ M') →
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) h W' β K →
          ∀ x, 0 ≤ x → ∀ k ∈ K, W' x k = W x k) ∧
      ∀ k ∈ K, IsGreatest (plannerValues U f ((1 - θ) * β) k)
          (pathValue U f h ((1 - θ) * β) k) ∧
        W k k = pathValue U f h β k ∧
        ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
          (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (h k) = W k k ↔ y = h k) := by
  have hB : ∀ k ∈ K, 0 ≤ (1 - θ) * deriv f k := fun k hk => mul_nonneg (by linarith) (hf' k hk)
  obtain ⟨W, M, hWb, hsol⟩ := exists_bellman_solution (U := U) (g := h)
    (A := fun k => f k - (1 - θ) * k * deriv f k) (B := fun k => (1 - θ) * deriv f k)
    hβ0.le hβ1 hUb hK hw hB
  obtain ⟨hvb, hpol⟩ := pathValue_spec (Fk := f) hβ0.le hβ1 hUb hK hc
  have hUm : MonotoneOn U (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun c hc => (hUd c hc).continuousAt.continuousWithinAt)
      (fun c hc => (hUd c (interior_subset hc)).differentiableWithinAt) fun c hc => ?_
    exact hU' c (interior_subset hc)
  refine ⟨W, M, hWb, hsol, fun W' M' hW' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hW' hWb hK hw hB hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := indirect_equilibrium_dp hU hβ0 hβ1 hθ hUd hU' hUb hK hK0 hf' hw hc heul
    htvc hvb hpol hWb hsol k hk
  refine ⟨?_, h1, h4⟩
  have hkt := iterate_mem hK hk
  have hβ' : 0 ≤ (1 - θ) * β := mul_nonneg (by linarith) hβ0.le
  have hβ'1 : (1 - θ) * β < 1 := by nlinarith
  -- the pseudo-planner's transversality condition follows from the individual's
  have htvc' := tvc_indiv_imp_pseudo hθ0 hθ (z := fun t => deriv U (f (h^[t] k) -
    h (h^[t] k)) * deriv f (h^[t] k) * h^[t] k) (by
      refine (htvc k hk).congr fun t => ?_
      ring)
  have hP := planner_optimal (ks := fun t => h^[t] k) hU.concaveOn hUm hβ' hβ'1 hUb hUd hU'
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      rw [heul _ (hkt t)])
    (by
      refine htvc'.congr fun t => ?_
      simp only [Function.iterate_succ_apply']
      ring)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  exact hP

end StokeyLucasPrescott.EquilibriaWithDistortions
