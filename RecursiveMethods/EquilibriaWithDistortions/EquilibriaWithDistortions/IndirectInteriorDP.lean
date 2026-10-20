/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectExistenceEquilibrium

/-!
# Exercise 18.1 and the taxed economy with `U` differentiable only along the path

SLP §18.1, pp. 543–546. `dp_diagonal`, `ex_18_1_dp`, `indirect_equilibrium_dp`,
`planner_optimal`, `ex_18_1_full` and `indirect_equilibrium_full` assume that `U` is
differentiable with `U′ ≥ 0` at every `c ≥ 0`. Their proofs use the derivative only at the
consumptions `F(k) − g(k)`, `k ∈ K`, of the aggregate path. Here the same results are proved under
that pointwise hypothesis, with monotonicity of `U` assumed directly. This admits utilities with
`U′(0+) = ∞`, such as `U(c) = 1 − e^{−√c}`, which are not differentiable at `0`; these are the
utilities for which `IndirectInterior` proves the planner's policy interior.

* `dp_diagonal_pathwise`: `dp_diagonal` with `U` differentiable, `U′ ≥ 0`, at `F(k) − g(k)`,
  `k ∈ K`, only.
* `ex_18_1_dp_pathwise`, `indirect_equilibrium_dp_pathwise`: likewise for `ex_18_1_dp` and
  `indirect_equilibrium_dp` (pp. 544, 546).
* `planner_optimal_pathwise`: `planner_optimal` with `U` monotone, and differentiable with
  `U′ ≥ 0` along the planner's path only (Theorem 4.15 for (1)).
* `ex_18_1_full_pathwise`, `indirect_equilibrium_full_pathwise`: `ex_18_1_full` and
  `indirect_equilibrium_full` under the same weakening.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- **The diagonal of the functional equation, `U` differentiable along the path only.** As
`dp_diagonal`, with `U` differentiable and `U′ ≥ 0` only at the consumptions `F(k) − g(k)`,
`k ∈ K`: then `W(k, k) = v(k)`, `g(k) ∈ Γ(k, k)` attains the supremum at `(k, k)`, and it is the
only `y ∈ Γ(k, k)` that does. -/
theorem dp_diagonal_pathwise {U A B Fk g v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ}
    {K : Set ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (Fk k - g k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (Fk k - g k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hAB : ∀ k ∈ K, A k + B k * k = Fk k)
    (hc : ∀ k ∈ K, 0 ≤ Fk k - g k)
    (heul : ∀ k ∈ K, deriv U (Fk k - g k) =
      β * B (g k) * deriv U (Fk (g k) - g (g k)))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * B (g^[t] k) *
      deriv U (Fk (g^[t] k) - g (g^[t] k)) * g^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (Fk k - g k) + β * v (g k))
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hsol : SolvesBellman U A B g W β K) :
    ∀ k ∈ K, W k k = v k ∧ g k ∈ feasY A B k k ∧
      U (A k + B k * k - g k) + β * W (g k) (g k) = W k k ∧
      ∀ y ∈ feasY A B k k, U (A k + B k * k - y) + β * W y (g k) = W k k → y = g k := by
  -- the diagonal value
  have hdiag : ∀ k ∈ K, W k k = v k ∧
      IsGreatest (indivValues U β (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k) (v k) ∧
      ∀ x S, IndivFeasible (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k x →
        HasSum (fun t => β ^ t * U (consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k))
          x t)) S → ∀ t₀ : ℕ, S ≤ v k - β ^ t₀ * (U (Fk (g^[t₀] k) - g (g^[t₀] k)) +
            deriv U (Fk (g^[t₀] k) - g (g^[t₀] k)) * (consPath (fun t => A (g^[t] k))
              (fun t => B (g^[t] k)) x t₀ - (Fk (g^[t₀] k) - g (g^[t₀] k))) -
            U (consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x t₀)) := by
    intro k hk
    have hkt := iterate_mem hK hk
    set a : ℕ → ℝ := fun t => A (g^[t] k) with ha
    set b : ℕ → ℝ := fun t => B (g^[t] k) with hb
    set xs : ℕ → ℝ := fun t => g^[t] k with hxs
    have hcons : ∀ t, consPath a b xs t = Fk (g^[t] k) - g (g^[t] k) := fun t => by
      simp only [consPath, ha, hb, hxs, Function.iterate_succ_apply']
      rw [← hAB _ (hkt t)]
    have hcs : ∀ t, 0 ≤ consPath a b xs t := fun t => (hcons t).symm ▸ hc _ (hkt t)
    have hfeas : IndivFeasible a b (xs 0) xs := ⟨rfl, fun t => ⟨hK0 _ (hkt t), hcs t⟩⟩
    have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b xs t) := fun t => by
      rw [hcons]; exact hUd _ (hkt t)
    have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t) := fun t => by
      rw [hcons]; exact mul_nonneg (hB _ (hkt t)) (hU' _ (hkt t))
    have heul' : ∀ t, deriv U (consPath a b xs t) =
        β * b (t + 1) * deriv U (consPath a b xs (t + 1)) := fun t => by
      rw [hcons, hcons, heul _ (hkt t)]
      simp only [hb, Function.iterate_succ_apply']
    have htvc' : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop
        (𝓝 0) := by
      refine (htvc k hk).congr fun t => ?_
      rw [hcons]
    have hv' : HasSum (fun t => β ^ t * U (consPath a b xs t)) (v k) := by
      have := policyValue_hasSum hβ0.le hβ1 hK hv (fun k hk => hUb _ (hc k hk)) hpol hk
      simpa only [hcons] using this
    have hG := euler_tvc_isGreatest hU.concaveOn hβ0.le hUd' hp heul' htvc' hfeas hv'
    have hL := bellman_isLUB hβ0.le hβ1 hUb hW hK hA hB hsol (hK0 k hk) hk
    refine ⟨hL.unique hG.isLUB, hG, fun x S hx hS t₀ => ?_⟩
    have := euler_tvc_gap hU.concaveOn hβ0.le hUd' hcs hp heul' htvc' hx hS hv' t₀
    rwa [hcons t₀] at this
  intro k hk
  obtain ⟨hWk, -, hgap⟩ := hdiag k hk
  have hgk := hK k hk
  have hAk : A k + B k * k - g k = Fk k - g k := by rw [hAB k hk]
  refine ⟨hWk, ⟨hK0 _ hgk, by rw [hAk]; exact hc k hk⟩, ?_, fun y hy hyW => ?_⟩
  · rw [hAk, (hdiag _ hgk).1, hWk, hpol k hk]
  · by_contra hne
    set cy := A k + B k * k - y with hcy
    set cs := Fk k - g k with hcs
    have hcne : cy ≠ cs := by
      intro h
      apply hne
      rw [hcy, hcs, ← hAB k hk] at h
      linarith
    set r0 := U cs + deriv U cs * (cy - cs) - U cy with hr0
    have hr0p : 0 < r0 := by
      have := strictConcave_lt_tangent hU hy.2 (hc k hk) hcne (hUd k hk)
      rw [hr0]
      linarith
    -- every continuation from `(y, g(k))` gives at most `v(k) − r₀`
    have hub : W y (g k) ≤ (v k - r0 - U cy) / β := by
      refine (bellman_isLUB hβ0.le hβ1 hUb hW hK hA hB hsol hy.1 hgk).2 ?_
      rintro S' ⟨x', hx', hS'⟩
      rw [le_div_iff₀ hβ0]
      set x : ℕ → ℝ := fun t => Nat.casesOn t k fun t => x' t with hxdef
      have hx0 : x 0 = k := rfl
      have hxs : ∀ t, x (t + 1) = x' t := fun t => rfl
      have hit : ∀ t : ℕ, g^[t + 1] k = g^[t] (g k) := fun t => Function.iterate_succ_apply _ _ _
      have hc0 : consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x 0 = cy := by
        simp only [consPath, hx0, hxs, hx'.1, Function.iterate_zero, id, hcy]
      have hcsucc : ∀ t, consPath (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) x (t + 1) =
          consPath (fun t => A (g^[t] (g k))) (fun t => B (g^[t] (g k))) x' t := fun t => by
        simp only [consPath, hxs, hit]
      have hfeas : IndivFeasible (fun t => A (g^[t] k)) (fun t => B (g^[t] k)) k x := by
        refine ⟨hx0, fun t => ?_⟩
        rcases t with _ | t
        · exact ⟨hK0 k hk, hc0 ▸ hy.2⟩
        · rw [hcsucc t]
          exact ⟨(hx'.2 t).1, (hx'.2 t).2⟩
      have hsum : HasSum (fun t => β ^ t * U (consPath (fun t => A (g^[t] k))
          (fun t => B (g^[t] k)) x t)) (U cy + β * S') := by
        refine (hasSum_nat_add_iff' 1).1 ?_
        have e : (U cy + β * S') - ∑ i ∈ range 1, β ^ i * U (consPath (fun t => A (g^[t] k))
            (fun t => B (g^[t] k)) x i) = β * S' := by
          simp [hc0]
        rw [e]
        refine (hS'.mul_left β).congr_fun fun t => ?_
        simp only [hcsucc t, pow_succ]
        ring
      have h := hgap x _ hfeas hsum 0
      simp only [pow_zero, one_mul, Function.iterate_zero, id, hc0] at h
      linarith
    have h1 : U cy + β * W y (g k) ≤ v k - r0 := by
      have := mul_le_mul_of_nonneg_left hub hβ0.le
      rw [mul_div_cancel₀ _ hβ0.ne'] at this
      linarith
    rw [hyW, hWk] at h1
    linarith

/-- **Exercise 18.1, literally, `U` differentiable along the path only** (p. 544). As
`ex_18_1_dp`, with `U` differentiable and `U′ ≥ 0` only at `f(k) − g(k)`, `k ∈ K`: for a bounded
solution `V` of (2), `V(k, k; g) = v(k)` and `g(k)` is the unique optimal choice at `(k, k)`. -/
theorem ex_18_1_dp_pathwise {U f g v : ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - g k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, g k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - g k)
    (heul : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (f k - g k) + β * v (g k))
    (hV : ∀ x, 0 ≤ x → ∀ k ∈ K, |V x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) g V β K) :
    ∀ k ∈ K, V k k = v k ∧
      (∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
        U (f k + (k - k) * deriv f k - y) + β * V y (g k) = V k k ↔ y = g k) := by
  have hD := dp_diagonal_pathwise (A := fun k => f k - k * deriv f k) (B := deriv f) (Fk := f)
    hU hβ0 hβ1 hUd hU' hUb hK hK0 hw hf' (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring)
    (fun k hk => (htvc k hk).congr fun t => by ring) hv hpol hV hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (k - k) * deriv f k - y = f k - k * deriv f k + deriv f k * k - y :=
    fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyV => h4 y hy (by rw [← e]; exact hyV), fun hyg => ?_⟩⟩
  rw [hyg, e]
  exact h3

/-- **The indirect method gives a recursive competitive equilibrium, `U` differentiable along
the path only** (pp. 545–546). As `indirect_equilibrium_dp`, with `U` differentiable and
`U′ ≥ 0` only at `f(k) − ĥ(k)`, `k ∈ K`: for a bounded solution `W` of (3) with `h = ĥ`,
`W(k, k; ĥ) = v(k)` and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice at `(k, k)`. -/
theorem indirect_equilibrium_dp_pathwise {U f h v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M Mv : ℝ}
    {K : Set ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ < 1)
    (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - h k))
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hK : ∀ k ∈ K, h k ∈ K) (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hf' : ∀ k ∈ K, 0 ≤ deriv f k) (hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k)
    (hc : ∀ k ∈ K, 0 ≤ f k - h k)
    (heul : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k))
    (htvc : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0))
    (hv : ∀ k ∈ K, |v k| ≤ Mv) (hpol : ∀ k ∈ K, v k = U (f k - h k) + β * v (h k))
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M)
    (hsol : SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
      (fun k => (1 - θ) * deriv f k) h W β K) :
    ∀ k ∈ K, W k k = v k ∧
      ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
        (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (h k) = W k k ↔ y = h k) := by
  have hD := dp_diagonal_pathwise (A := fun k => f k - (1 - θ) * k * deriv f k)
    (B := fun k => (1 - θ) * deriv f k) (Fk := f) hU hβ0 hβ1 hUd hU' hUb hK hK0 hw
    (fun k hk => mul_nonneg (by linarith) (hf' k hk)) (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring) htvc hv hpol hW hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (1 - θ) * (k - k) * deriv f k - y =
      f k - (1 - θ) * k * deriv f k + (1 - θ) * deriv f k * k - y := fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyW => h4 y hy (by rw [← e]; exact hyW), fun hyh => ?_⟩⟩
  rw [hyh, e]
  exact h3

/-- **Sufficiency of Euler + transversality for the planner, `U` differentiable along the path
only** (Theorem 4.15 for §18.1 (1)). As `planner_optimal`, with `U` concave, nondecreasing and
bounded on `[0, ∞)`, and differentiable with `U′ ≥ 0` only at the path's consumptions
`f(ks_t) − ks_{t+1}`. Then the path's value is the greatest value of the planner's problem. -/
theorem planner_optimal_pathwise {U f : ℝ → ℝ} {β B₀ : ℝ} {ks : ℕ → ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hUd : ∀ t, DifferentiableAt ℝ U (f (ks t) - ks (t + 1)))
    (hU' : ∀ t, 0 ≤ deriv U (f (ks t) - ks (t + 1))) (hf : ConcaveOn ℝ (Ici 0) f)
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
  have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b ks t) := fun t => by
    rw [hcons]; exact hUd t
  have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b ks t) := fun t => by
    rw [hcons]; exact mul_nonneg (hf' t) (hU' t)
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

/-- **Exercise 18.1, complete, `U` differentiable along the path only** (p. 544). As
`ex_18_1_full`, with `U` strictly concave, nondecreasing and bounded on `[0, ∞)`, and
differentiable with `U′ ≥ 0` only at the consumptions `f(k) − g(k)`, `k ∈ K`. Then (2) has a
bounded solution `V` on `[0, ∞) × K`, unique among bounded solutions; `V(k, k; g)` is the maximal
value of the planner's problem from `k ∈ K`; and `G(k, k; g) = g(k)`. -/
theorem ex_18_1_full_pathwise {U f g : ℝ → ℝ} {β B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - g k))
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
  refine ⟨V, M, hVb, hsol, fun V' M' hV' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hV' hVb hK hw hf' hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := ex_18_1_dp_pathwise hU hβ0 hβ1 hUd hU' hUb hK hK0 hf' hw hc heul htvc hvb
    hpol hVb hsol k hk
  refine ⟨?_, h4⟩
  have hkt := iterate_mem hK hk
  have hP := planner_optimal_pathwise (ks := fun t => g^[t] k) hU.concaveOn hUm hβ0.le hβ1 hUb
    (fun t => by simp only [Function.iterate_succ_apply']; exact hUd _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hU' _ (hkt t))
    hf (fun t => hfd _ (hkt t)) (fun t => hf' _ (hkt t)) (fun t => hK0 _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hc _ (hkt t))
    (fun t => by
      simp only [Function.iterate_succ_apply']
      exact heul _ (hkt t))
    (by simpa only [Function.iterate_succ_apply'] using htvc k hk)
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at hP
  rw [h1]
  exact hP

/-- **The taxed economy (3), complete, `U` differentiable along the path only** (pp. 545–546).
As `indirect_equilibrium_full`, with `U` strictly concave, nondecreasing and bounded on
`[0, ∞)`, and differentiable with `U′ ≥ 0` only at the consumptions `f(k) − ĥ(k)`, `k ∈ K`.
Then (3) with `h = ĥ` has a bounded solution `W`, unique among bounded solutions; the path of
`ĥ` is optimal in the pseudo-economy with discount factor `(1 − θ)β`; `W(k, k; ĥ)` is the
individual's value of following `ĥ`; and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice. -/
theorem indirect_equilibrium_full_pathwise {U f h : ℝ → ℝ} {β θ B₀ : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hUm : MonotoneOn U (Ici 0)) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hUd : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k))
    (hU' : ∀ k ∈ K, 0 ≤ deriv U (f k - h k)) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
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
  refine ⟨W, M, hWb, hsol, fun W' M' hW' hsol' x hx k hk =>
    bellman_unique hβ0.le hβ1 hUb hW' hWb hK hw hB hsol' hsol x hx k hk, fun k hk => ?_⟩
  obtain ⟨h1, h4⟩ := indirect_equilibrium_dp_pathwise hU hβ0 hβ1 hθ hUd hU' hUb hK hK0 hf' hw
    hc heul htvc hvb hpol hWb hsol k hk
  refine ⟨?_, h1, h4⟩
  have hkt := iterate_mem hK hk
  have hβ' : 0 ≤ (1 - θ) * β := mul_nonneg (by linarith) hβ0.le
  have hβ'1 : (1 - θ) * β < 1 := by nlinarith
  -- the pseudo-planner's transversality condition follows from the individual's
  have htvc' := tvc_indiv_imp_pseudo hθ0 hθ (z := fun t => deriv U (f (h^[t] k) -
    h (h^[t] k)) * deriv f (h^[t] k) * h^[t] k) (by
      refine (htvc k hk).congr fun t => ?_
      ring)
  have hP := planner_optimal_pathwise (ks := fun t => h^[t] k) hU.concaveOn hUm hβ' hβ'1 hUb
    (fun t => by simp only [Function.iterate_succ_apply']; exact hUd _ (hkt t))
    (fun t => by simp only [Function.iterate_succ_apply']; exact hU' _ (hkt t))
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
