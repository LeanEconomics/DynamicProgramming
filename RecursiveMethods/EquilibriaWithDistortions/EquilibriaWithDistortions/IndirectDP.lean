/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectApproach

/-!
# The individual's functional equation and Exercise 18.1 stated literally

SLP §18.1, pp. 544–546, the bounded case. The individual with own capital `x`, facing
aggregate capital `k` that moves by `k′ = g(k)`, solves the functional equation
`W(x, k) = sup_{y ∈ Γ(x, k)} {U[A(k) + B(k) x − y] + β W(y, g(k))}`
(`SolvesBellman`) with `Γ(x, k) = {y : y ≥ 0, A(k) + B(k) x − y ≥ 0}` (`feasY`). The book's (2)
is `A(k) = f(k) − k f′(k)`, `B(k) = f′(k)`; its (3) (tax `θ`, rebate) is
`A(k) = f(k) − (1 − θ) k f′(k)`, `B(k) = (1 − θ) f′(k)`.

* `bellman_isLUB` (the dynamic-programming step, cf. Theorems 4.2–4.3): if `U` is bounded on
  `[0, ∞)` and `W` is a bounded solution of the functional equation, then `W(x₀, k₀)` is the
  supremum of the sequence-problem values `∑ β^t U(c_t)` over feasible paths from `x₀` with prices
  from `k_t = g^t(k₀)`. In particular the bounded solution is unique.
* `policyValue_hasSum`: a bounded `v` with `v(k) = U[F(k) − g(k)] + β v(g(k))` (the planner's
  value under its optimal policy `g`, from (1)) is the value of the path `k_{t+1} = g(k_t)`.
* `euler_tvc_gap`: the quantitative form of `euler_tvc_strict`.
* `dp_diagonal`: if the path `k_{t+1} = g(k_t)` from every `k ∈ K` satisfies the individual's
  Euler equation and transversality condition, then for the bounded solution `W`:
  `W(k, k) = v(k)`, and `g(k)` is the **unique** maximiser in the functional equation at `(k, k)`.
* **Exercise 18.1, literally** (`ex_18_1_dp`): `V(k, k; g) = v(k)` and `G(k, k; g) = g(k)` for the
  bounded solution `V` of (2).
* **The taxed economy, literally** (`indirect_equilibrium_dp`, p. 546): for the bounded solution
  `W` of (3) with `h = ĥ` the pseudo-planner's policy, `H(k, k; ĥ) = ĥ(k)` (the definition of a
  recursive competitive equilibrium, p. 545).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set Finset

/-- The constraint set `Γ(x, k) = {y : y ≥ 0, A(k) + B(k) x − y ≥ 0}`. -/
def feasY (A B : ℝ → ℝ) (x k : ℝ) : Set ℝ := {y | 0 ≤ y ∧ 0 ≤ A k + B k * x - y}

/-- `W` solves the individual's functional equation on `[0, ∞) × K`:
`W(x, k) = sup_{y ∈ Γ(x, k)} {U[A(k) + B(k) x − y] + β W(y, g(k))}`. -/
def SolvesBellman (U A B g : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (β : ℝ) (K : Set ℝ) : Prop :=
  ∀ x, 0 ≤ x → ∀ k ∈ K,
    W x k = sSup ((fun y => U (A k + B k * x - y) + β * W y (g k)) '' feasY A B x k)

/-- A path defined by a selection: `x_0 = x₀`, `x_{t+1} = sel(x_t, g^t(k₀))`. -/
noncomputable def selPath (sel : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x₀ k₀ : ℝ) (t : ℕ) : ℝ :=
  Nat.rec (motive := fun _ => ℝ) x₀ (fun t xt => sel xt (g^[t] k₀)) t

/-- `g^t(k₀) ∈ K` when `K` is invariant. -/
theorem iterate_mem {g : ℝ → ℝ} {K : Set ℝ} (hK : ∀ k ∈ K, g k ∈ K) {k₀ : ℝ} (hk₀ : k₀ ∈ K) :
    ∀ t : ℕ, g^[t] k₀ ∈ K := by
  intro t
  induction t with
  | zero => exact hk₀
  | succ t ih => rw [Function.iterate_succ_apply']; exact hK _ ih

/-- **The bounded solution of the functional equation is the sequence-problem value.** Let
`0 ≤ β < 1`, `|U| ≤ B₀` on `[0, ∞)`, `K` invariant under `g`, `A, B ≥ 0` on `K`, and let `W`,
with `|W| ≤ M` on `[0, ∞) × K`, solve the functional equation. Then for `x₀ ≥ 0`, `k₀ ∈ K`,
`W(x₀, k₀)` is the least upper bound of the values `∑ β^t U(c_t)` of the feasible paths from
`x₀` with prices from `k_t = g^t(k₀)`. -/
theorem bellman_isLUB {U A B g : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hK : ∀ k ∈ K, g k ∈ K)
    (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k) (hsol : SolvesBellman U A B g W β K)
    {x₀ k₀ : ℝ} (hx₀ : 0 ≤ x₀) (hk₀ : k₀ ∈ K) :
    IsLUB (indivValues U β (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) x₀) (W x₀ k₀) := by
  have hkt := iterate_mem hK hk₀
  have hgk : ∀ t : ℕ, g^[t + 1] k₀ = g (g^[t] k₀) := fun t => Function.iterate_succ_apply' _ _ _
  have hne : ∀ x, 0 ≤ x → ∀ k ∈ K, (0 : ℝ) ∈ feasY A B x k := fun x hx k hk =>
    ⟨le_rfl, by have := mul_nonneg (hB k hk) hx; linarith [hA k hk]⟩
  have hbdd : ∀ x, 0 ≤ x → ∀ k ∈ K, BddAbove
      ((fun y => U (A k + B k * x - y) + β * W y (g k)) '' feasY A B x k) := by
    intro x hx k hk
    refine ⟨B₀ + β * M, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := (abs_le.1 (hU _ hy.2)).2
    have h2 := (abs_le.1 (hW y hy.1 _ (hK k hk))).2
    have := mul_le_mul_of_nonneg_left h2 hβ0
    simp only
    linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  constructor
  · -- every value is at most `W(x₀, k₀)`
    rintro S ⟨x, hx, hS⟩
    have key : ∀ T, ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) x t) + β ^ T * W (x T) (g^[T] k₀) ≤ W x₀ k₀ := by
      intro T
      induction T with
      | zero => simp [hx.1]
      | succ T ih =>
        rw [sum_range_succ]
        have hstep : U (consPath (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) x T) +
            β * W (x (T + 1)) (g^[T + 1] k₀) ≤ W (x T) (g^[T] k₀) := by
          rw [hsol _ (hx.2 T).1 _ (hkt T), hgk T]
          exact le_csSup (hbdd _ (hx.2 T).1 _ (hkt T))
            ⟨x (T + 1), ⟨(hx.2 (T + 1)).1, (hx.2 T).2⟩, rfl⟩
        have := mul_le_mul_of_nonneg_left hstep (pow_nonneg hβ0 T)
        rw [pow_succ]
        nlinarith
    have hle : ∀ T, ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) x t) ≤ W x₀ k₀ + β ^ T * M := by
      intro T
      have h1 := key T
      have h2 := (abs_le.1 (hW _ (hx.2 T).1 _ (hkt T))).1
      have := mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ0 T)
      linarith
    have hlim : Tendsto (fun T : ℕ => W x₀ k₀ + β ^ T * M) atTop (𝓝 (W x₀ k₀)) := by
      simpa using (hpow.mul_const M).const_add (W x₀ k₀)
    exact le_of_tendsto_of_tendsto' hS.tendsto_sum_nat hlim hle
  · -- `W(x₀, k₀)` is the least upper bound
    intro b hb
    by_contra hlt
    push Not at hlt
    set η := W x₀ k₀ - b with hη
    have hηp : 0 < η := by linarith
    set δ := η * (1 - β) / 2 with hδ
    have hδp : 0 < δ := by have : 0 < 1 - β := by linarith
                           positivity
    have hsel : ∀ x k, ∃ y, 0 ≤ x → k ∈ K → y ∈ feasY A B x k ∧
        W x k - δ < U (A k + B k * x - y) + β * W y (g k) := by
      intro x k
      by_cases h : 0 ≤ x ∧ k ∈ K
      · have hlt' : W x k - δ < sSup ((fun y => U (A k + B k * x - y) + β * W y (g k)) ''
            feasY A B x k) := by
          rw [← hsol x h.1 k h.2]
          linarith
        obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ :=
          exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨0, hne x h.1 k h.2⟩) hlt'
        exact ⟨y, fun _ _ => ⟨hy, hy'⟩⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose sel hsel using hsel
    set xp := selPath sel g x₀ k₀ with hxp
    have hxp0 : xp 0 = x₀ := rfl
    have hxps : ∀ t, xp (t + 1) = sel (xp t) (g^[t] k₀) := fun t => rfl
    have hnn : ∀ t, 0 ≤ xp t := by
      intro t
      induction t with
      | zero => exact hx₀
      | succ t ih => rw [hxps]; exact ((hsel _ _ ih (hkt t)).1).1
    have hfeas : IndivFeasible (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) x₀ xp := by
      refine ⟨hxp0, fun t => ⟨hnn t, ?_⟩⟩
      have := ((hsel _ _ (hnn t) (hkt t)).1).2
      simp only [consPath]
      rw [hxps]
      exact this
    have hcons : ∀ t, consPath (fun t => A (g^[t] k₀)) (fun t => B (g^[t] k₀)) xp t =
        A (g^[t] k₀) + B (g^[t] k₀) * xp t - sel (xp t) (g^[t] k₀) := fun t => by
      simp only [consPath, hxps]
    have hsum : Summable fun t => β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) xp t) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
        fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (hU _ (hfeas.2 t).2) (pow_nonneg hβ0 t)
    have hval := hb ⟨xp, hfeas, hsum.hasSum⟩
    have key : ∀ T, W x₀ k₀ ≤ ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
        (fun t => B (g^[t] k₀)) xp t) + β ^ T * W (xp T) (g^[T] k₀) +
          δ * ∑ t ∈ range T, β ^ t := by
      intro T
      induction T with
      | zero => simp [hxp0]
      | succ T ih =>
        rw [sum_range_succ, sum_range_succ, hcons T, ← hxps T]
        have hstep := ((hsel _ _ (hnn T) (hkt T)).2)
        rw [← hxps, ← hgk T] at hstep
        have := mul_le_mul_of_nonneg_left hstep.le (pow_nonneg hβ0 T)
        rw [pow_succ]
        linarith
    have hgeo : ∀ T, ∑ t ∈ range T, β ^ t ≤ (1 - β)⁻¹ := fun T => by
      rw [← tsum_geometric_of_lt_one hβ0 hβ1]
      exact (summable_geometric_of_lt_one hβ0 hβ1).sum_le_tsum _
        (fun i _ => pow_nonneg hβ0 i)
    have hle : ∀ T, W x₀ k₀ - δ * (1 - β)⁻¹ - β ^ T * M ≤
        ∑ t ∈ range T, β ^ t * U (consPath (fun t => A (g^[t] k₀))
          (fun t => B (g^[t] k₀)) xp t) := by
      intro T
      have h1 := key T
      have h2 := (abs_le.1 (hW _ (hnn T) _ (hkt T))).2
      have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ0 T)
      have h4 := mul_le_mul_of_nonneg_left (hgeo T) hδp.le
      linarith
    have hlim : Tendsto (fun T : ℕ => W x₀ k₀ - δ * (1 - β)⁻¹ - β ^ T * M) atTop
        (𝓝 (W x₀ k₀ - δ * (1 - β)⁻¹)) := by
      simpa using (hpow.mul_const M).const_sub (W x₀ k₀ - δ * (1 - β)⁻¹)
    have hS := le_of_tendsto_of_tendsto' hlim hsum.hasSum.tendsto_sum_nat hle
    have e : δ * (1 - β)⁻¹ = η / 2 := by
      rw [hδ]
      have : (1 - β) ≠ 0 := by linarith
      field_simp
    linarith

/-- **Uniqueness of the bounded solution** of the functional equation (the book's "the unique
solution of (2)"): two bounded solutions agree on `[0, ∞) × K`. -/
theorem bellman_unique {U A B g : ℝ → ℝ} {W W' : ℝ → ℝ → ℝ} {β B₀ M M' : ℝ} {K : Set ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hU : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hW : ∀ x, 0 ≤ x → ∀ k ∈ K, |W x k| ≤ M) (hW' : ∀ x, 0 ≤ x → ∀ k ∈ K, |W' x k| ≤ M')
    (hK : ∀ k ∈ K, g k ∈ K) (hA : ∀ k ∈ K, 0 ≤ A k) (hB : ∀ k ∈ K, 0 ≤ B k)
    (hsol : SolvesBellman U A B g W β K) (hsol' : SolvesBellman U A B g W' β K) :
    ∀ x, 0 ≤ x → ∀ k ∈ K, W x k = W' x k := fun _ hx _ hk =>
  (bellman_isLUB hβ0 hβ1 hU hW hK hA hB hsol hx hk).unique
    (bellman_isLUB hβ0 hβ1 hU hW' hK hA hB hsol' hx hk)

/-- **The value of the policy `g`.** If `0 ≤ β < 1`, `K` is invariant under `g`, `v` is bounded on
`K` and `v(k) = U[F(k) − g(k)] + β v(g(k))` on `K` (the planner's functional equation (1) at its
optimal policy), then `v(k₀) = ∑ β^t U[F(k_t) − k_{t+1}]` along `k_t = g^t(k₀)`, provided the terms
are bounded. -/
theorem policyValue_hasSum {U Fk g v : ℝ → ℝ} {β Mv B₀ : ℝ} {K : Set ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hK : ∀ k ∈ K, g k ∈ K) (hv : ∀ k ∈ K, |v k| ≤ Mv)
    (hU : ∀ k ∈ K, |U (Fk k - g k)| ≤ B₀)
    (hpol : ∀ k ∈ K, v k = U (Fk k - g k) + β * v (g k)) {k₀ : ℝ} (hk₀ : k₀ ∈ K) :
    HasSum (fun t => β ^ t * U (Fk (g^[t] k₀) - g (g^[t] k₀))) (v k₀) := by
  have hkt := iterate_mem hK hk₀
  have hsum : Summable fun t => β ^ t * U (Fk (g^[t] k₀) - g (g^[t] k₀)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B₀)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hU _ (hkt t)) (pow_nonneg hβ0 t)
  refine hsum.hasSum_iff_tendsto_nat.2 ?_
  have key : ∀ T, v k₀ = ∑ t ∈ range T, β ^ t * U (Fk (g^[t] k₀) - g (g^[t] k₀)) +
      β ^ T * v (g^[T] k₀) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_range_succ, Function.iterate_succ_apply', ih, hpol _ (hkt T), pow_succ]
      ring
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  have hrem : Tendsto (fun T : ℕ => β ^ T * v (g^[T] k₀)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun T => ?_) (by simpa using hpow.mul_const Mv)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hv _ (hkt T)) (pow_nonneg hβ0 T)
  have h := (tendsto_const_nhds (x := v k₀)).sub hrem
  rw [sub_zero] at h
  refine h.congr fun T => ?_
  rw [key T]
  ring

/-- **Quantitative strict optimality.** Under the hypotheses of `euler_tvc_optimal`, every
feasible path `x` from `xs_0` has value at most
`S′ − β^{t₀}(U(c*_{t₀}) + U′(c*_{t₀})(c_{t₀} − c*_{t₀}) − U(c_{t₀}))`, for any date `t₀`. -/
theorem euler_tvc_gap {U : ℝ → ℝ} {β : ℝ} {a b xs x : ℕ → ℝ} {S S' : ℝ}
    (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 ≤ β)
    (hUd : ∀ t, DifferentiableAt ℝ U (consPath a b xs t))
    (hxs : ∀ t, 0 ≤ consPath a b xs t)
    (hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t))
    (heul : ∀ t, deriv U (consPath a b xs t) =
      β * b (t + 1) * deriv U (consPath a b xs (t + 1)))
    (htvc : Tendsto (fun T => β ^ T * b T * deriv U (consPath a b xs T) * xs T) atTop (𝓝 0))
    (hx : IndivFeasible a b (xs 0) x)
    (hS : HasSum (fun t => β ^ t * U (consPath a b x t)) S)
    (hS' : HasSum (fun t => β ^ t * U (consPath a b xs t)) S') (t₀ : ℕ) :
    S ≤ S' - β ^ t₀ * (U (consPath a b xs t₀) + deriv U (consPath a b xs t₀) *
      (consPath a b x t₀ - consPath a b xs t₀) - U (consPath a b x t₀)) := by
  set r : ℕ → ℝ := fun t => β ^ t * (U (consPath a b xs t) + deriv U (consPath a b xs t) *
    (consPath a b x t - consPath a b xs t) - U (consPath a b x t)) with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => by
    have h := concave_le_tangent hU (hx.2 t).2 (hxs t) (hUd t)
    exact mul_nonneg (pow_nonneg hβ t) (by linarith)
  have key : ∀ T, t₀ < T → ∑ t ∈ range T, β ^ t * U (consPath a b x t) ≤
      ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
        β ^ T * b T * deriv U (consPath a b xs T) * xs T - r t₀ := by
    intro T hT
    have htel := euler_telescope U β a b xs x heul hx.1 T
    have hsum : ∑ t ∈ range T, β ^ t * U (consPath a b x t) =
        ∑ t ∈ range T, β ^ t * U (consPath a b xs t) +
          ∑ t ∈ range T, β ^ t * (deriv U (consPath a b xs t) *
            (consPath a b x t - consPath a b xs t)) - ∑ t ∈ range T, r t := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      simp only [hr]
      ring
    have hle : r t₀ ≤ ∑ t ∈ range T, r t :=
      single_le_sum (fun t _ => hr0 t) (mem_range.2 hT)
    have h1 : 0 ≤ β ^ T * (b T * deriv U (consPath a b xs T)) :=
      mul_nonneg (pow_nonneg hβ T) (hp T)
    have h2 := (hx.2 T).1
    rw [hsum, htel]
    nlinarith
  have hlim := (hS'.tendsto_sum_nat.add htvc).sub_const (r t₀)
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto hS.tendsto_sum_nat hlim
    (eventually_atTop.2 ⟨t₀ + 1, fun T hT => key T (by omega)⟩)

/-- **The diagonal of the functional equation.** Let `U` be strictly concave on `[0, ∞)`,
differentiable with `U′ ≥ 0` there, `|U| ≤ B₀` on `[0, ∞)`, `0 < β < 1`, `K ⊆ [0, ∞)` invariant
under `g`, and on `K`: `A, B ≥ 0`, `A(k) + B(k) k = F(k)`, `F(k) − g(k) ≥ 0`, and the Euler
equation `U′[F(k) − g(k)] = β B(g(k)) U′[F(g(k)) − g(g(k))]`; let the transversality condition
`β^t B(k_t) U′(c_t) k_t → 0` hold along `k_t = g^t(k)` for every `k ∈ K`. Let `v` be bounded on
`K` with `v(k) = U[F(k) − g(k)] + β v(g(k))`, and `W` a bounded solution of the functional
equation. Then for every `k ∈ K`: `W(k, k) = v(k)`; `g(k) ∈ Γ(k, k)` attains the supremum at
`(k, k)`; and it is the only `y ∈ Γ(k, k)` that does. -/
theorem dp_diagonal {U A B Fk g v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
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
    have hUd' : ∀ t, DifferentiableAt ℝ U (consPath a b xs t) := fun t => hUd _ (hcs t)
    have hp : ∀ t, 0 ≤ b t * deriv U (consPath a b xs t) := fun t =>
      mul_nonneg (hB _ (hkt t)) (hU' _ (hcs t))
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
      have := strictConcave_lt_tangent hU hy.2 (hc k hk) hcne (hUd _ (hc k hk))
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

/-- **Exercise 18.1, stated literally** (p. 544). Let `0 < β < 1`, `U` strictly concave on
`[0, ∞)`, differentiable with `U′ ≥ 0` and bounded there; let `K ⊆ [0, ∞)` be invariant under the
planner's policy `g`, with `f′(k) ≥ 0`, `f(k) − k f′(k) ≥ 0` and `f(k) − g(k) ≥ 0` on `K`; let `g`
satisfy the planner's Euler equation and transversality condition, and let the planner's value
`v` (bounded on `K`) satisfy `v(k) = U[f(k) − g(k)] + β v(g(k))` (functional equation (1) at its
policy). If `V` is a bounded solution of the individual's functional equation (2) on
`[0, ∞) × K`, then `V(k, k; g) = v(k)` for all `k ∈ K`, and `g(k)` is the unique optimal choice
`G(k, k; g)` in (2) at `(k, k)`. -/
theorem ex_18_1_dp {U f g v : ℝ → ℝ} {V : ℝ → ℝ → ℝ} {β B₀ M Mv : ℝ} {K : Set ℝ}
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
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
  have hD := dp_diagonal (A := fun k => f k - k * deriv f k) (B := deriv f) (Fk := f) hU hβ0
    hβ1 hUd hU' hUb hK hK0 hw hf' (fun k _ => by ring) hc
    (fun k hk => by rw [heul k hk]; ring)
    (fun k hk => (htvc k hk).congr fun t => by ring) hv hpol hV hsol
  intro k hk
  obtain ⟨h1, -, h3, h4⟩ := hD k hk
  have e : ∀ y, f k + (k - k) * deriv f k - y = f k - k * deriv f k + deriv f k * k - y :=
    fun y => by ring
  refine ⟨h1, fun y hy => ⟨fun hyV => h4 y hy (by rw [← e]; exact hyV), fun hyg => ?_⟩⟩
  rw [hyg, e]
  exact h3

/-- **The indirect method gives a recursive competitive equilibrium** (pp. 545–546). In the
economy with capital-income tax `θ ∈ [0, 1)` rebated lump sum, let `ĥ` be the policy of the
pseudo-economy with discount factor `(1 − θ)β` (Euler equation
`U′[f(k) − ĥ(k)] = (1 − θ)β U′[f(ĥ(k)) − ĥ(ĥ(k))] f′(ĥ(k))`) satisfying the individual's
transversality condition, with `v(k) = U[f(k) − ĥ(k)] + β v(ĥ(k))` bounded (the individual's
value of following `ĥ`). If `W` is a bounded solution of the individual's functional equation (3)
with `h = ĥ`, then `W(k, k; ĥ) = v(k)` and the unique optimal choice at `(k, k)` is
`H(k, k; ĥ) = ĥ(k)`: `ĥ` is a recursive competitive equilibrium. -/
theorem indirect_equilibrium_dp {U f h v : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {β θ B₀ M Mv : ℝ}
    {K : Set ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ < 1)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
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
  have hD := dp_diagonal (A := fun k => f k - (1 - θ) * k * deriv f k)
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

end StokeyLucasPrescott.EquilibriaWithDistortions
