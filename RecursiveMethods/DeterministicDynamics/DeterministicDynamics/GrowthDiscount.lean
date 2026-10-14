/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.WeakConcavity

/-!
# Exercise 5.1e: saving rises with the discount factor

SLP §5.1, p. 105: writing `g(x, β)` for the policy function, `g(x, β)` is increasing in `β`.

The manual iterates `T_{β'}` from `v(·, β)` and argues from first-order conditions that the
policies `g_k` rise with `k`; that step needs more than it states. Here the argument is a lattice
(Topkis) argument and needs neither interior solutions nor differentiability.

* `concave_exchange`: for concave `φ`, `p ≤ q` and `δ ≥ 0`,
  `φ(p) + φ(q + δ) ≤ φ(q) + φ(p + δ)`. With `U` concave and `f` increasing this makes
  `U(f(x) − y)` have increasing differences in `(x, y)`.
* `bellman_sub_monotone`: if `β'a − βb` is nondecreasing, so is `T_{β'}a − T_βb`.
* `discounted_value_monotone`: `β'v(·, β') − βv(·, β)` is nondecreasing for `β ≤ β'` (iterate
  `T_{β'}` from `v(·, β)` and pass to the limit).
* `policy_le_of_discount_le`: every optimal choice under `β'` is at least the unique optimal
  choice under `β`; `ex_5_1e`: `g(x, β) ≤ g(x, β')` under the hypotheses of Exercise 5.1c.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {U f : ℝ → ℝ} {β β' xbar : ℝ}

/-- For concave `φ`, moving `δ` from the larger point to the smaller one raises the sum:
`φ(p) + φ(q + δ) ≤ φ(q) + φ(p + δ)` when `p ≤ q`, `0 ≤ δ`. -/
theorem concave_exchange {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConcaveOn ℝ s φ) {p q δ : ℝ}
    (hp : p ∈ s) (hqδ : q + δ ∈ s) (hpq : p ≤ q) (hδ : 0 ≤ δ) :
    φ p + φ (q + δ) ≤ φ q + φ (p + δ) := by
  rcases eq_or_lt_of_le (add_nonneg (sub_nonneg.2 hpq) hδ) with hL | hL
  · have hq : q = p := by linarith
    have hδ0 : δ = 0 := by linarith
    subst hq hδ0
    simp
  set L := q - p + δ
  set t := δ / L
  have ht0 : 0 ≤ t := div_nonneg hδ hL.le
  have ht1 : t ≤ 1 := (div_le_one hL).2 (by linarith)
  have hLne : L ≠ 0 := hL.ne'
  have h1 := hφ.2 hp hqδ ht0 (sub_nonneg.2 ht1) (by ring)
  have h2 := hφ.2 hp hqδ (sub_nonneg.2 ht1) ht0 (by ring)
  have htL : t * (q - p + δ) = δ := div_mul_cancel₀ δ hLne
  have e1 : t • p + (1 - t) • (q + δ) = q := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * htL
  have e2 : (1 - t) • p + t • (q + δ) = p + δ := by
    simp only [smul_eq_mul]; linear_combination htL
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- `U(f(x) − y)` has increasing differences: for `x₁ ≤ x₂` and `y₁ ≤ y₂ ≤ f(x₁)`,
`F(x₂, y₂) + F(x₁, y₁) ≥ F(x₁, y₂) + F(x₂, y₁)`. -/
theorem growthF_increasingDiff (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    {x₁ x₂ y₁ y₂ : Icc (0 : ℝ) xbar} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) (hy₂ : y₂.1 ≤ f x₁.1) :
    growthF U f xbar (x₁, y₂) + growthF U f xbar (x₂, y₁) ≤
      growthF U f xbar (x₂, y₂) + growthF U f xbar (x₁, y₁) := by
  have hf : f x₁.1 ≤ f x₂.1 := h.f_mono.monotoneOn (mem_Ici.2 x₁.2.1) (mem_Ici.2 x₂.2.1) hx
  have hy' : y₁.1 ≤ y₂.1 := hy
  have := concave_exchange hU (p := f x₁.1 - y₂.1) (q := f x₂.1 - y₂.1) (δ := y₂.1 - y₁.1)
    (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith [y₁.2.1])) (by linarith) (by linarith)
  simp only [growthF]
  rw [show f x₂.1 - y₂.1 + (y₂.1 - y₁.1) = f x₂.1 - y₁.1 by ring,
    show f x₁.1 - y₂.1 + (y₂.1 - y₁.1) = f x₁.1 - y₁.1 by ring] at this
  linarith

/-- **The lattice step.** If `y ↦ β'a(y) − βb(y)` is nondecreasing, so is
`x ↦ (T_{β'}a)(x) − (T_βb)(x)`. -/
theorem bellman_sub_monotone (h : GrowthHyp U f β xbar) (h' : GrowthHyp U f β' xbar)
    (hU : ConcaveOn ℝ (Ici 0) U) {a b : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hD : Monotone fun y => β' * a y - β * b y) :
    Monotone fun x => bellman (growth_assumption43 h') (growth_assumption44 h') a x -
      bellman (growth_assumption43 h) (growth_assumption44 h) b x := by
  intro x₁ x₂ hx
  have hf : f x₁.1 ≤ f x₂.1 := h.f_mono.monotoneOn (mem_Ici.2 x₁.2.1) (mem_Ici.2 x₂.2.1) hx
  obtain ⟨c, hc, hcv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h') (growth_assumption44 h') a x₁
  obtain ⟨d, hd, hdv, -⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) b x₂
  obtain ⟨-, -, -, hmax'⟩ :=
    exists_bellman_argmax (growth_assumption43 h') (growth_assumption44 h') a x₂
  obtain ⟨-, -, -, hmax⟩ :=
    exists_bellman_argmax (growth_assumption43 h) (growth_assumption44 h) b x₁
  have hc' : c.1 ≤ f x₁.1 := hc
  have hd' : d.1 ≤ f x₂.1 := hd
  simp only
  rw [hcv, hdv]
  rcases le_total c d with hcd | hdc
  · -- `c ≤ d`: use `d` at `x₂` under `β'` and `c` at `x₁` under `β`
    have e1 := hmax' d hd
    have e2 := hmax c hc
    have e3 := hD hcd
    simp only at e3
    linarith
  · -- `d ≤ c`: use `c` at `x₂` under `β'` and `d` at `x₁` under `β`
    have e1 := hmax' c (show c.1 ≤ f x₂.1 by linarith)
    have e2 := hmax d (show d.1 ≤ f x₁.1 by linarith [show d.1 ≤ c.1 from hdc])
    have e3 := growthF_increasingDiff h hU hx hdc hc'
    linarith

/-- **Exercise 5.1e, increasing differences.** For `β ≤ β'`, `y ↦ β'v(y, β') − βv(y, β)` is
nondecreasing. -/
theorem discounted_value_monotone (h : GrowthHyp U f β xbar) (h' : GrowthHyp U f β' xbar)
    (hββ' : β ≤ β') (hU : ConcaveOn ℝ (Ici 0) U) {v v' : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hv' : bellman (growth_assumption43 h') (growth_assumption44 h') v' = v') :
    Monotone fun y => β' * v' y - β * v y := by
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  set T' := bellman (growth_assumption43 h') (growth_assumption44 h')
  have hvm : Monotone v := by
    obtain ⟨u, -, huniq, -, hmono, -⟩ := ex_5_1ab h
    rw [huniq v hv]
    exact hmono.monotone
  -- the iterates `wₙ = T_{β'}ⁿ v` keep `β'wₙ − βv` nondecreasing
  have hstep : ∀ n : ℕ, Monotone fun y => β' * (T'^[n] v) y - β * v y := by
    intro n
    induction n with
    | zero =>
      intro y₁ y₂ hy
      have := hvm hy
      simp only [Function.iterate_zero, id_eq]
      nlinarith
    | succ n ih =>
      have hm := bellman_sub_monotone h h' hU ih
      rw [hv] at hm
      intro y₁ y₂ hy
      have e1 := hm hy
      have e2 := hvm hy
      simp only [Function.iterate_succ_apply'] at e1 ⊢
      change T' (T'^[n] v) y₁ - v y₁ ≤ T' (T'^[n] v) y₂ - v y₂ at e1
      nlinarith [h'.β_pos]
  -- pass to the limit `wₙ → v'`
  obtain ⟨u, hu, huniq, hrate, -⟩ :=
    theorem_4_6 (growth_assumption43 h') (growth_assumption44 h')
  have hu' : v' = u := huniq v' hv'
  subst hu'
  have hlim : Tendsto (fun n => T'^[n] v) atTop (𝓝 v') := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (hrate v) ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h'.β_pos.le h'.β_lt).mul_const (dist v v')
  intro y₁ y₂ hy
  have hpt : ∀ y, Tendsto (fun n => β' * (T'^[n] v) y - β * v y) atTop
      (𝓝 (β' * v' y - β * v y)) := fun y =>
    ((((continuous_eval_const y).tendsto v').comp hlim).const_mul β').sub_const _
  exact le_of_tendsto_of_tendsto (hpt y₁) (hpt y₂) (Eventually.of_forall fun n => hstep n hy)

/-- **Exercise 5.1e.** If the policy under `β` is unique, then every optimal choice under any
`β' ≥ β` is at least as large: saving rises with patience. -/
theorem policy_le_of_discount_le [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (h' : GrowthHyp U f β' xbar) (hββ' : β ≤ β') (hU : ConcaveOn ℝ (Ici 0) U)
    {v v' : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hv' : bellman (growth_assumption43 h') (growth_assumption44 h') v' = v')
    (huniq : UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v))
    (x : Icc (0 : ℝ) xbar) {y' : Icc (0 : ℝ) xbar}
    (hy' : y' ∈ argmax (obj (growthF U f xbar) β' v') (growthΓ f xbar) x) :
    argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x ≤ y' := by
  set y := argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x
  have hy : y ∈ growthΓ f xbar x := (huniq.argmaxFn_mem x).1
  by_contra hlt
  push Not at hlt
  have h1 := huniq.lt_of_ne hy'.1 hlt.ne
  have h2 : obj (growthF U f xbar) β' v' (x, y) ≤ obj (growthF U f xbar) β' v' (x, y') := by
    rw [hy'.2]
    exact le_maxValue (continuousOn_obj (growth_assumption44 h') v'.continuous)
      ((growth_assumption43 h').compact x) hy
  have hD := discounted_value_monotone h h' hββ' hU hv hv' hlt.le
  simp only [obj] at h1 h2 hD
  linarith

/-- **Exercise 5.1e** under the hypotheses of Exercise 5.1c: `g(x, β) ≤ g(x, β')` for
`β ≤ β'`. -/
theorem ex_5_1e [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (h' : GrowthHyp U f β' xbar) (hββ' : β ≤ β') (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {v v' : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v)
    (hv' : bellman (growth_assumption43 h') (growth_assumption44 h') v' = v')
    (x : Icc (0 : ℝ) xbar) :
    argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v) x ≤
      argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β' v') x :=
  policy_le_of_discount_le h h' hββ' hU.concaveOn hv hv' (ex_5_1c_weak h hU hf hv).2.1 x
    ((ex_5_1c_weak h' hU hf hv').2.1.argmaxFn_mem x)

end StokeyLucasPrescott.DeterministicDynamics
