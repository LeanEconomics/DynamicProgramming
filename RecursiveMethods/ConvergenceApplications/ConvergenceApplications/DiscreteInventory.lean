/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.ConditionM

/-!
# A discrete-space (s, S) inventory problem

SLP §13.1, pp. 389–390, Exercise 13.1. Demand is `1` with probability `θ` and `0` with
probability `1 − θ`; stocks are `x ∈ ℕ`; ordering up to `y` from `0` costs `c₀ + c₁y`; a unit
sold earns `p`; `β` is the discount factor. Put `γ = θβ/(1 − (1 − θ)β)` (`discGamma`) and
`B₂ = θp/(1 − β)` (`discB2`).

The book's claim that an optimal policy has `s = 0` (never order before a stock-out, "try it")
is not part of the functional equations (1)–(2), which already build it in; it is not
formalised here.

## Exercise 13.1a (p. 390)

* `discGamma_pos_lt_one`: `0 < γ < 1` for `θ > 0`, `0 < β < 1`.
* `ex_13_1a_eq1`: the solutions of (1) (`DiscEq1`) are exactly `v(x) = B₂ − Kγˣ`,
  `K = B₂ − v(0)`.
* `ex_13_1a_eq2_iff`, `orderCost_fixedPoint_iff`: for such `v`, (2) (`DiscEq2`) is
  `K = min_{y ≥ 1} (c₀ + c₁y + Kγʸ)`, which holds iff `K = K* := min_{S ≥ 1} (c₀ + c₁S)/(1 − γˢ)`
  (`orderCost`).
* `exists_isMinOn_orderCost`: for `c₁ > 0` the minimum `K*` is attained.
* `orderCost_isMaxOn_iff_isMinOn`: the optimal order sizes in (2) are exactly the minimisers of
  the cost per cycle.
* `stopping_isMaxOn`, `exists_stopping_index`: for `K ≥ 0` the smallest `y ≥ 1` with
  `K(1 − γ)γʸ ≤ c₁` is optimal (concavity of the increments).
* `ex_13_1a`: for `c₀ ≥ 0`, `c₁ > 0` a solution of (1)–(2) exists; every solution has this form,
  and a finite optimal order size `S` exists and is characterised as above.

## Exercise 13.1b (p. 390)

`discKernel θ S : Kernel ℕ ℕ`: from `x ≥ 1` to `x − 1` w.p. `θ`, stay w.p. `1 − θ`; from `0` to
`S − 1` w.p. `θ`, to `S` w.p. `1 − θ`. Let `E = {0, …, S}`.

* `isMarkov_discKernel`: it is a Markov kernel.
* `ex_13_1b_closed`: `E` is closed.
* `ex_13_1b_communicate`, `ex_13_1b_minimal` (`0 < θ < 1`): every state of `E` is reached from
  every state, so `E` is a minimal closed set, the ergodic set.
* `ex_13_1b_transient`: states `x > S` are transient: `Pⁿ(x, {x}) = (1 − θ)ⁿ → 0`, the chain
  never returns to `x` after leaving it, and `Pⁿ(x, E) ≥ 1 − (1 − θ/2)ⁿ2^{x−S} → 1`.
* `ex_13_1b_not_cyclic` (`θ < 1`): there are no cyclically moving subsets.

## Exercise 13.1c (p. 390)

* `discKernelE θ S`: the chain on `E` (the subtype `Iic S`); `discKpowE_map` relates it to the
  chain on `ℕ` (`Pⁿ_E(x, ·)` pushed into `ℕ` is `Pⁿ(x, ·)`).
* `ex_13_1c_conditionM`: Condition M holds on `E` with `N = S + 1`, `ε = θˢ(1 − θ)^{S+1}`, via
  `P^{S+1}(x, {S}) ≥ ε` (Exercise 11.5a).
* `ex_13_1c`: by Theorem 11.12, `π_E` (`discPiE`) is the unique invariant distribution on `E`
  and `T*ⁿλ₀ → π_E` in total variation, geometrically, for every `λ₀`.
* `discPi_invariant`, `ex_13_1c_weights`: `π = (1/S) Σ_{z=1}^{S} P(z, ·)` (`discPi`) is
  invariant, with `π₀ = θ/S`, `π_x = 1/S` (`1 ≤ x ≤ S − 1`), `π_S = (1 − θ)/S` (for `S = 1`:
  `π₀ = θ`, `π₁ = 1 − θ`).
* `ex_13_1c_nat`: every invariant probability measure on `ℕ` is concentrated on `E` and equals
  `π`. (Proof: `λ(Eᶜ) = ∫ Pⁿ(x, Eᶜ) λ(dx) → 0` by dominated convergence, rather than the
  balance equations at `x > S`.)
* `ex_13_1c_nat_convergence`: `T*ⁿλ₀ → π` in total variation for every initial distribution
  `λ₀` on `ℕ`; `ex_13_1c_nat_not_uniform`: the convergence is not uniform in `λ₀`.

## Corrections

* **Correction** (Exercise 13.1a, "suitable restrictions"). With `c₁ = 0` and `c₀ > 0` the cost
  per cycle `c₀/(1 − γˢ)` is strictly decreasing, no finite `S` is optimal, and (1)–(2) have no
  solution (`ex_13_1a_c1_zero`).
* **Correction** (manual, Exercise 13.1a). The manual's stopping condition
  `(B₂ − v(0))(1 − γ)γ^{S+1} ≤ c₁` has the wrong exponent; the right one is `S`
  (`stopping_isMaxOn`). For `θ = 1/2`, `β = 2/3` (`γ = 1/2`), `c₀ = 10`, `c₁ = 1` the manual's
  rule picks `S = 2`, which is not optimal; the correct rule picks the optimal `S = 3`
  (`ex_13_1a_manual_counterexample`).
* **Correction** (NOTE to Exercise 13.1b,c). With `θ = 1` and `S ≥ 2` the chain is the
  deterministic cycle `0 → S − 1 → ⋯ → 1 → 0` and `T*ⁿδ₀` does not converge
  (`ex_13_1b_theta_one`).
* **Correction** (NOTE to Exercise 13.1c). The notes' bound `Pˢ(x, {0}) ≥ θˢ` on `E` is false
  (`0` has no self-loop): `P²(1, {0}) = 3/16 < 9/16` for `S = 2`, `θ = 3/4`
  (`ex_13_1c_note_counterexample`). Condition M holds instead through the state `S`, which has a
  self-loop (`ex_13_1c_conditionM`).
* **Correction** (NOTE to Exercise 13.1c). Condition M fails for the chain on all of `ℕ`
  (`ex_13_1c_not_conditionM_nat`), so Theorem 11.12 is applied on `E`.
* **Correction** (manual, Exercise 13.1c). The manual's answer `p̄ᵢ = 1/S` on `{0, …, S}`
  (`manualPi`) has total mass `(S + 1)/S ≠ 1` (`ex_13_1c_manual_mass`) and, for `S ≥ 2`, is not
  invariant (`ex_13_1c_manual_not_invariant`).
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-! ### Exercise 13.1a: the functional equation and the optimal order size -/

/-- The effective discount factor `γ = θβ/(1 − (1 − θ)β)` of the inventory problem (SLP §13.1,
p. 390, [Derived]); `0 < γ < 1` by `discGamma_pos_lt_one`. -/
noncomputable def discGamma (θ β : ℝ) : ℝ := θ * β / (1 - (1 - θ) * β)

/-- `B₂ = θp/(1 − β)`, the value of an infinite stock (SLP §13.1, p. 390, [Derived]). -/
noncomputable def discB2 (θ β p : ℝ) : ℝ := θ * p / (1 - β)

/-- Equation (1) of SLP §13.1 (p. 390): `v(x) = θ[p + βv(x − 1)] + (1 − θ)βv(x)` for `x ≥ 1`,
written with `x + 1` in place of `x`. -/
def DiscEq1 (θ β p : ℝ) (v : ℕ → ℝ) : Prop :=
  ∀ x, v (x + 1) = θ * (p + β * v x) + (1 - θ) * β * v (x + 1)

/-- Equation (2) of SLP §13.1 (p. 390): `v(0) = max_{y ≥ 1} [−c₀ − c₁y + v(y)]`. -/
def DiscEq2 (c₀ c₁ : ℝ) (v : ℕ → ℝ) : Prop :=
  IsGreatest ((fun y : ℕ => -c₀ - c₁ * y + v y) '' Ici 1) (v 0)

/-- The cost per cycle `S ↦ (c₀ + c₁S)/(1 − γˢ)` of ordering up to `S`; its minimum over
`S ≥ 1` is `B₂ − v(0)` (SLP §13.1, p. 390, [Derived]). -/
noncomputable def orderCost (γ c₀ c₁ : ℝ) (S : ℕ) : ℝ := (c₀ + c₁ * S) / (1 - γ ^ S)

variable {θ β p c₀ c₁ : ℝ}

/-- The denominator `1 − (1 − θ)β` of `γ` is positive. -/
theorem discDen_pos (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < 1 - (1 - θ) * β := by
  nlinarith

/-- `0 < γ < 1` for `θ > 0` and `0 < β < 1`. -/
theorem discGamma_pos_lt_one (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < discGamma θ β ∧ discGamma θ β < 1 := by
  have hD := discDen_pos hθ0 hβ0 hβ1
  refine ⟨div_pos (mul_pos hθ0 hβ0) hD, (div_lt_one hD).2 (by nlinarith)⟩

/-- **Exercise 13.1a**, equation (1) (p. 390). The solutions of (1) on `ℕ` are exactly
`v(x) = B₂ − Kγˣ` with `K = B₂ − v(0)`. -/
theorem ex_13_1a_eq1 (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβ1 : β < 1) (v : ℕ → ℝ) :
    DiscEq1 θ β p v ↔
      ∀ x, v x = discB2 θ β p - (discB2 θ β p - v 0) * discGamma θ β ^ x := by
  have hD := discDen_pos hθ0 hβ0 hβ1
  set D := 1 - (1 - θ) * β
  set γ := discGamma θ β
  set B := discB2 θ β p
  have hγD : γ * D = θ * β := div_mul_cancel₀ _ hD.ne'
  have hB : B * (1 - β) = θ * p := div_mul_cancel₀ _ (by linarith)
  -- the key identity
  have key : ∀ (K : ℝ) (x : ℕ), (B - K * γ ^ (x + 1)) * D = θ * p + θ * β * (B - K * γ ^ x) := by
    intro K x
    rw [pow_succ]
    linear_combination (-(K * γ ^ x)) * hγD + hB
  constructor
  · intro h x
    induction x with
    | zero => simp
    | succ x ih =>
      have h1 : v (x + 1) * D = θ * p + θ * β * v x := by
        simp only [D]; linear_combination h x
      refine mul_right_cancel₀ hD.ne' ?_
      rw [h1, key, ← ih]
  · intro h x
    have := key (B - v 0) x
    rw [← h, ← h] at this
    have h2 : v (x + 1) * D = θ * p + θ * β * v x := this
    simp only [D] at h2
    linear_combination h2


variable {γ : ℝ}

/-- `1 − γˢ > 0` for `0 ≤ γ < 1` and `S ≥ 1`. -/
theorem one_sub_pow_pos_of_lt_one (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {S : ℕ} (hS : 1 ≤ S) :
    0 < 1 - γ ^ S := by
  have := pow_lt_one₀ hγ0 hγ1 (by omega : S ≠ 0)
  linarith

/-- **Exercise 13.1a**, equation (2) (p. 390). For `v(x) = B − Kγˣ`, equation (2) says
`K = min_{y ≥ 1} (c₀ + c₁y + Kγʸ)`. -/
theorem ex_13_1a_eq2_iff (v : ℕ → ℝ) (B K : ℝ) (hv : ∀ x, v x = B - K * γ ^ x) :
    DiscEq2 c₀ c₁ v ↔ IsLeast ((fun y : ℕ => c₀ + c₁ * y + K * γ ^ y) '' Ici 1) K := by
  have h0 : v 0 = B - K := by rw [hv]; simp
  constructor
  · rintro ⟨⟨y, hy, hyeq⟩, hle⟩
    refine ⟨⟨y, hy, ?_⟩, ?_⟩
    · dsimp only at hyeq; rw [hv, h0] at hyeq; linarith
    · rintro _ ⟨y', hy', rfl⟩
      have := hle (mem_image_of_mem _ hy')
      dsimp only at this ⊢; rw [hv, h0] at this; linarith
  · rintro ⟨⟨y, hy, hyeq⟩, hle⟩
    refine ⟨⟨y, hy, ?_⟩, ?_⟩
    · dsimp only at hyeq ⊢; rw [hv, h0]; linarith
    · rintro _ ⟨y', hy', rfl⟩
      have := hle (mem_image_of_mem _ hy')
      dsimp only at this ⊢; rw [hv, h0]; linarith

/-- `K = min_{y ≥ 1} (c₀ + c₁y + Kγʸ)` iff `K = min_{S ≥ 1} (c₀ + c₁S)/(1 − γˢ)`: the
fixed-point equation for `K` has exactly one solution, the minimal cost per cycle `K*`. -/
theorem orderCost_fixedPoint_iff (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (K : ℝ) :
    IsLeast ((fun y : ℕ => c₀ + c₁ * y + K * γ ^ y) '' Ici 1) K ↔
      IsLeast (orderCost γ c₀ c₁ '' Ici 1) K := by
  have hle : ∀ S : ℕ, 1 ≤ S → (K ≤ c₀ + c₁ * S + K * γ ^ S ↔ K ≤ orderCost γ c₀ c₁ S) := by
    intro S hS
    rw [orderCost, le_div_iff₀ (one_sub_pow_pos_of_lt_one hγ0 hγ1 hS)]
    constructor <;> intro h <;> linarith
  have heq : ∀ S : ℕ, 1 ≤ S → (c₀ + c₁ * S + K * γ ^ S = K ↔ orderCost γ c₀ c₁ S = K) := by
    intro S hS
    rw [orderCost, div_eq_iff (one_sub_pow_pos_of_lt_one hγ0 hγ1 hS).ne']
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨⟨y, hy, hyeq⟩, h⟩
    refine ⟨⟨y, hy, (heq y hy).1 hyeq⟩, ?_⟩
    rintro _ ⟨S, hS, rfl⟩
    exact (hle S hS).1 (h (mem_image_of_mem _ hS))
  · rintro ⟨⟨y, hy, hyeq⟩, h⟩
    refine ⟨⟨y, hy, (heq y hy).2 hyeq⟩, ?_⟩
    rintro _ ⟨S, hS, rfl⟩
    exact (hle S hS).2 (h (mem_image_of_mem _ hS))

/-- `(c₀ + c₁S)/(1 − γˢ) ≥ c₀ + c₁S` when `c₀ + c₁S ≥ 0`. -/
theorem orderCost_ge (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {S : ℕ} (hS : 1 ≤ S)
    (h : 0 ≤ c₀ + c₁ * S) : c₀ + c₁ * S ≤ orderCost γ c₀ c₁ S := by
  have hp := one_sub_pow_pos_of_lt_one hγ0 hγ1 hS
  rw [orderCost, le_div_iff₀ hp]
  nlinarith [pow_nonneg hγ0 S]

/-- For `c₁ > 0` the cost per cycle attains its minimum on `{1, 2, …}` (it is at least
`c₀ + c₁S → ∞`). -/
theorem exists_isMinOn_orderCost (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hc₁ : 0 < c₁) :
    ∃ S, 1 ≤ S ∧ IsMinOn (orderCost γ c₀ c₁) (Ici 1) S := by
  obtain ⟨M, hM⟩ := exists_nat_ge ((max (orderCost γ c₀ c₁ 1) 0 - c₀) / c₁)
  rw [div_le_iff₀ hc₁] at hM
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 (M + 1)) (orderCost γ c₀ c₁)
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hS1 := (Finset.mem_Icc.1 hS).1
  refine ⟨S, hS1, fun S' (hS' : 1 ≤ S') => ?_⟩
  by_cases hS'M : S' ≤ M + 1
  · exact hmin S' (Finset.mem_Icc.2 ⟨hS', hS'M⟩)
  · have hMS' : (M : ℝ) ≤ S' := by exact_mod_cast (by omega : M ≤ S')
    have h0 : max (orderCost γ c₀ c₁ 1) 0 ≤ c₀ + c₁ * S' := by nlinarith
    calc orderCost γ c₀ c₁ S ≤ orderCost γ c₀ c₁ 1 :=
          hmin 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
      _ ≤ c₀ + c₁ * S' := (le_max_left _ _).trans h0
      _ ≤ orderCost γ c₀ c₁ S' := orderCost_ge hγ0 hγ1 hS' ((le_max_right _ _).trans h0)

/-- With `K = K*`, the maximisers `y ≥ 1` of `−c₁y − K*γʸ` (the order sizes solving (2)) are
exactly the minimisers of the cost per cycle `(c₀ + c₁S)/(1 − γˢ)`. -/
theorem orderCost_isMaxOn_iff_isMinOn (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {K : ℝ}
    (hK : IsLeast (orderCost γ c₀ c₁ '' Ici 1) K) {y : ℕ} (hy : 1 ≤ y) :
    IsMaxOn (fun y : ℕ => -c₁ * y - K * γ ^ y) (Ici 1) y ↔
      IsMinOn (orderCost γ c₀ c₁) (Ici 1) y := by
  have hK' := (orderCost_fixedPoint_iff hγ0 hγ1 K).2 hK
  obtain ⟨⟨y₀, hy₀, hy₀eq⟩, hlow⟩ := hK'
  obtain ⟨⟨y₁, hy₁, hy₁eq⟩, hlow'⟩ := hK
  have hf : ∀ S : ℕ, S ∈ Ici 1 → K ≤ c₀ + c₁ * S + K * γ ^ S :=
    fun S hS => hlow (mem_image_of_mem _ hS)
  have hg : ∀ S : ℕ, S ∈ Ici 1 → K ≤ orderCost γ c₀ c₁ S :=
    fun S hS => hlow' (mem_image_of_mem _ hS)
  have heq : ∀ S : ℕ, 1 ≤ S → (c₀ + c₁ * S + K * γ ^ S = K ↔ orderCost γ c₀ c₁ S = K) := by
    intro S hS
    rw [orderCost, div_eq_iff (one_sub_pow_pos_of_lt_one hγ0 hγ1 hS).ne']
    constructor <;> intro h <;> linarith
  dsimp only at hy₀eq hy₁eq
  constructor
  · intro hmax S hS
    have h1 : c₀ + c₁ * y + K * γ ^ y = K := by
      have : -c₁ * y₀ - K * γ ^ y₀ ≤ -c₁ * y - K * γ ^ y := hmax hy₀
      linarith [hf y hy]
    have := (heq y hy).1 h1
    exact this ▸ hg S hS
  · intro hmin S hS
    have h1 : orderCost γ c₀ c₁ y = K := le_antisymm (hy₁eq ▸ hmin hy₁) (hg y hy)
    have := (heq y hy).2 h1
    change -c₁ * S - K * γ ^ S ≤ -c₁ * y - K * γ ^ y
    linarith [hf S hS]

/-- The stopping rule ([Derived], p. 390). For `K ≥ 0` the increments
`−c₁ + K(1 − γ)γʸ` of `y ↦ −c₁y − Kγʸ` decrease, so the smallest `y₀ ≥ 1` with
`K(1 − γ)γ^{y₀} ≤ c₁` is a maximiser on `{1, 2, …}`. -/
theorem stopping_isMaxOn (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {K : ℝ} (hK : 0 ≤ K) {y₀ : ℕ}
    (hstop : K * (1 - γ) * γ ^ y₀ ≤ c₁)
    (hbefore : ∀ y : ℕ, 1 ≤ y → y < y₀ → c₁ < K * (1 - γ) * γ ^ y) :
    IsMaxOn (fun y : ℕ => -c₁ * y - K * γ ^ y) (Ici 1) y₀ := by
  set h : ℕ → ℝ := fun y => -c₁ * y - K * γ ^ y
  have hinc : ∀ y : ℕ, h (y + 1) - h y = -c₁ + K * (1 - γ) * γ ^ y := by
    intro y; simp only [h]; push_cast; ring
  have hafter : ∀ d : ℕ, h (y₀ + d) ≤ h y₀ := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 := hinc (y₀ + d)
      have h2 : K * (1 - γ) * γ ^ (y₀ + d) ≤ K * (1 - γ) * γ ^ y₀ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hγ0 hγ1.le (by omega))
          (mul_nonneg hK (by linarith))
      rw [← add_assoc]
      linarith
  have hbef : ∀ d y : ℕ, y + d = y₀ → 1 ≤ y → h y ≤ h y₀ := by
    intro d
    induction d with
    | zero => intro y hy _; rw [← hy, Nat.add_zero]
    | succ d ih =>
      intro y hy hy1
      have h1 := ih (y + 1) (by omega) (by omega)
      have h2 := hinc y
      have h3 := hbefore y hy1 (by omega)
      linarith
  intro y (hy : 1 ≤ y)
  rcases le_or_gt y₀ y with hle | hlt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact hafter d
  · exact hbef (y₀ - y) y (by omega) hy

/-- `K* ≥ 0` when `c₀, c₁ ≥ 0`. -/
theorem nonneg_of_isLeast_orderCost (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    {K : ℝ} (hK : IsLeast (orderCost γ c₀ c₁ '' Ici 1) K) : 0 ≤ K := by
  obtain ⟨⟨S, hS, rfl⟩, -⟩ := hK
  exact div_nonneg (by positivity) (one_sub_pow_pos_of_lt_one hγ0 hγ1 hS).le

/-- For `K ≥ 0` and `c₁ > 0` there is a smallest `y₀ ≥ 1` with `K(1 − γ)γ^{y₀} ≤ c₁`. -/
theorem exists_stopping_index (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {K : ℝ} (hK : 0 ≤ K) (hc₁ : 0 < c₁) :
    ∃ y₀ : ℕ, 1 ≤ y₀ ∧ K * (1 - γ) * γ ^ y₀ ≤ c₁ ∧
      ∀ y : ℕ, 1 ≤ y → y < y₀ → c₁ < K * (1 - γ) * γ ^ y := by
  classical
  have hP : ∃ y : ℕ, 1 ≤ y ∧ K * (1 - γ) * γ ^ y ≤ c₁ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hc₁ (by linarith : (0 : ℝ) < K + 1)) hγ1
    rw [lt_div_iff₀ (by linarith)] at hn
    refine ⟨n + 1, by omega, ?_⟩
    have h1 : (1 - γ) * γ ≤ 1 := by nlinarith
    have h2 : 0 ≤ K * γ ^ n := mul_nonneg hK (pow_nonneg hγ0 n)
    calc K * (1 - γ) * γ ^ (n + 1) = K * γ ^ n * ((1 - γ) * γ) := by ring
      _ ≤ K * γ ^ n * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ c₁ := by nlinarith [pow_nonneg hγ0 n]
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, fun y hy hlt => ?_⟩
  have := Nat.find_min hP hlt
  exact lt_of_not_ge fun h => this ⟨hy, h⟩

/-- For `v(y) = B − Kγʸ`, `y` maximises `−c₀ − c₁y + v(y)` iff it maximises `−c₁y − Kγʸ`. -/
theorem discValue_isMaxOn_iff {B K : ℝ} {v : ℕ → ℝ} (hv : ∀ x, v x = B - K * γ ^ x) (y : ℕ) :
    IsMaxOn (fun y : ℕ => -c₀ - c₁ * y + v y) (Ici 1) y ↔
      IsMaxOn (fun y : ℕ => -c₁ * y - K * γ ^ y) (Ici 1) y := by
  simp only [isMaxOn_iff, hv]
  exact forall₂_congr fun _ _ => by constructor <;> intro h <;> linarith

/-- **Exercise 13.1a** (p. 390). Let `0 < θ`, `0 < β < 1`, `c₀ ≥ 0`, `c₁ > 0`. A function `v`
satisfying (1) and (2) exists. Every such `v` has `K = B₂ − v(0)` equal to the minimal cost per
cycle `min_{S ≥ 1} (c₀ + c₁S)/(1 − γˢ)` and `v(x) = B₂ − Kγˣ`; the optimal order sizes in (2) are
exactly the minimisers of the cost per cycle; and the smallest `S ≥ 1` with `K(1 − γ)γˢ ≤ c₁` is a
finite optimal order size (the characterisation of `S` in terms of the parameters). -/
theorem ex_13_1a (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc₀ : 0 ≤ c₀) (hc₁ : 0 < c₁) :
    (∃ v, DiscEq1 θ β p v ∧ DiscEq2 c₀ c₁ v) ∧
    ∀ v, DiscEq1 θ β p v → DiscEq2 c₀ c₁ v →
      IsLeast (orderCost (discGamma θ β) c₀ c₁ '' Ici 1) (discB2 θ β p - v 0) ∧
      (∀ x, v x = discB2 θ β p - (discB2 θ β p - v 0) * discGamma θ β ^ x) ∧
      (∀ y, 1 ≤ y → (IsMaxOn (fun y : ℕ => -c₀ - c₁ * y + v y) (Ici 1) y ↔
        IsMinOn (orderCost (discGamma θ β) c₀ c₁) (Ici 1) y)) ∧
      ∃ S, 1 ≤ S ∧ IsMaxOn (fun y : ℕ => -c₀ - c₁ * y + v y) (Ici 1) S ∧
        (discB2 θ β p - v 0) * (1 - discGamma θ β) * discGamma θ β ^ S ≤ c₁ ∧
        ∀ y : ℕ, 1 ≤ y → y < S →
          c₁ < (discB2 θ β p - v 0) * (1 - discGamma θ β) * discGamma θ β ^ y := by
  obtain ⟨hγ0, hγ1⟩ := discGamma_pos_lt_one hθ0 hβ0 hβ1
  set γ := discGamma θ β
  set B := discB2 θ β p
  refine ⟨?_, fun v h1 h2 => ?_⟩
  · obtain ⟨S, hS, hmin⟩ := exists_isMinOn_orderCost hγ0.le hγ1 (c₀ := c₀) hc₁
    set K := orderCost γ c₀ c₁ S
    have hK : IsLeast (orderCost γ c₀ c₁ '' Ici 1) K :=
      ⟨mem_image_of_mem _ hS, by rintro _ ⟨S', hS', rfl⟩; exact hmin hS'⟩
    have hv : ∀ x, (fun x : ℕ => B - K * γ ^ x) x = B - K * γ ^ x := fun _ => rfl
    refine ⟨fun x => B - K * γ ^ x, (ex_13_1a_eq1 hθ0 hβ0 hβ1 _).2 fun x => ?_,
      (ex_13_1a_eq2_iff _ B K hv).2 ((orderCost_fixedPoint_iff hγ0.le hγ1 K).2 hK)⟩
    simp only [B, γ]; ring
  · have hv := (ex_13_1a_eq1 hθ0 hβ0 hβ1 v).1 h1
    have hK := (orderCost_fixedPoint_iff hγ0.le hγ1 _).1 ((ex_13_1a_eq2_iff v B _ hv).1 h2)
    have hK0 := nonneg_of_isLeast_orderCost hγ0.le hγ1 hc₀ hc₁.le hK
    refine ⟨hK, hv, fun y hy => (discValue_isMaxOn_iff hv y).trans
      (orderCost_isMaxOn_iff_isMinOn hγ0.le hγ1 hK hy), ?_⟩
    obtain ⟨S, hS, hstop, hbef⟩ := exists_stopping_index hγ0.le hγ1 hK0 hc₁
    exact ⟨S, hS, (discValue_isMaxOn_iff hv S).2 (stopping_isMaxOn hγ0.le hγ1 hK0 hstop hbef),
      hstop, hbef⟩

/-- **Correction** (Exercise 13.1a, p. 390). With `c₁ = 0` and `c₀ > 0` the cost per cycle
`c₀/(1 − γˢ)` is strictly decreasing, so no finite order size is optimal, and (1)–(2) have no
solution: the "suitable restrictions" must include `c₁ > 0`. -/
theorem ex_13_1a_c1_zero (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc₀ : 0 < c₀) :
    (∀ S : ℕ, 1 ≤ S →
      orderCost (discGamma θ β) c₀ 0 (S + 1) < orderCost (discGamma θ β) c₀ 0 S) ∧
    (¬ ∃ S, 1 ≤ S ∧ IsMinOn (orderCost (discGamma θ β) c₀ 0) (Ici 1) S) ∧
    ¬ ∃ v, DiscEq1 θ β p v ∧ DiscEq2 c₀ 0 v := by
  obtain ⟨hγ0, hγ1⟩ := discGamma_pos_lt_one hθ0 hβ0 hβ1
  set γ := discGamma θ β
  have hdec : ∀ S : ℕ, 1 ≤ S → orderCost γ c₀ 0 (S + 1) < orderCost γ c₀ 0 S := by
    intro S hS
    simp only [orderCost, zero_mul, add_zero]
    exact div_lt_div_of_pos_left hc₀ (one_sub_pow_pos_of_lt_one hγ0.le hγ1 hS)
      (by linarith [pow_lt_pow_right_of_lt_one₀ hγ0 hγ1 (by omega : S < S + 1)])
  have hnomin : ¬ ∃ S, 1 ≤ S ∧ IsMinOn (orderCost γ c₀ 0) (Ici 1) S := by
    rintro ⟨S, hS, hmin⟩
    have := hmin (show S + 1 ∈ Ici 1 by simp)
    exact absurd this (not_le.2 (hdec S hS))
  refine ⟨hdec, hnomin, ?_⟩
  rintro ⟨v, h1, h2⟩
  have hv := (ex_13_1a_eq1 hθ0 hβ0 hβ1 (p := p) v).1 h1
  have hK := (orderCost_fixedPoint_iff hγ0.le hγ1 _).1 ((ex_13_1a_eq2_iff v _ _ hv).1 h2)
  obtain ⟨⟨S, hS, hSeq⟩, hlow⟩ := hK
  exact hnomin ⟨S, hS, fun S' hS' => hSeq ▸ hlow (mem_image_of_mem _ hS')⟩

/-- **Correction** (manual, Exercise 13.1a). With `θ = 1/2`, `β = 2/3` (so `γ = 1/2`),
`c₀ = 10`, `c₁ = 1`, the manual's stopping rule with exponent `S + 1` (smallest `S` with
`K(1 − γ)γ^{S+1} ≤ c₁`) picks `S = 2`, which is not optimal, while the rule with exponent `S`
picks the optimal `S = 3`. -/
theorem ex_13_1a_manual_counterexample :
    discGamma (1 / 2) (2 / 3) = 1 / 2 ∧
    ∀ K, IsLeast (orderCost (1 / 2) 10 1 '' Ici 1) K →
      (¬ K * (1 - 1 / 2) * (1 / 2) ^ (1 + 1) ≤ 1 ∧ K * (1 - 1 / 2) * (1 / 2) ^ (2 + 1) ≤ 1) ∧
      ¬ IsMinOn (orderCost (1 / 2) 10 1) (Ici 1) 2 ∧
      IsMinOn (orderCost (1 / 2) 10 1) (Ici 1) 3 := by
  refine ⟨by norm_num [discGamma], fun K hK => ?_⟩
  have hK3 : K ≤ 104 / 7 := by
    have := hK.2 (mem_image_of_mem _ (show (3 : ℕ) ∈ Ici 1 by simp))
    norm_num [orderCost] at this ⊢; linarith
  have hK11 : 11 ≤ K := by
    obtain ⟨⟨S, hS, rfl⟩, -⟩ := hK
    have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have := orderCost_ge (γ := 1 / 2) (c₀ := 10) (c₁ := 1) (by norm_num) (by norm_num) hS
      (by linarith)
    linarith
  have h2 : ¬ IsMinOn (orderCost (1 / 2) 10 1) (Ici 1) 2 := by
    intro h
    have := h (show (3 : ℕ) ∈ Ici 1 by simp)
    norm_num [orderCost] at this
  refine ⟨⟨by norm_num; linarith, by norm_num; linarith⟩, h2, ?_⟩
  refine (orderCost_isMaxOn_iff_isMinOn (by norm_num) (by norm_num) hK (by norm_num)).1
    (stopping_isMaxOn (by norm_num) (by norm_num) (by linarith) ?_ ?_)
  · norm_num; linarith
  · intro y hy hy3
    interval_cases y <;> norm_num <;> linarith


/-! ### Exercise 13.1b: the Markov chain of optimally managed inventories -/

/-- The stock after the ordering decision: order up to `S` at a stock-out, otherwise do not
order. -/
def restock (S x : ℕ) : ℕ := if x = 0 then S else x

/-- The transition function of optimally managed inventories (Exercise 13.1b, p. 390): from
`x ≥ 1` go to `x − 1` with probability `θ` and stay with probability `1 − θ`; from `0` go to
`S − 1` with probability `θ` and to `S` with probability `1 − θ`. -/
noncomputable def discKernel (θ : ℝ) (S : ℕ) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun x =>
    ENNReal.ofReal θ • Measure.dirac (restock S x - 1) +
      ENNReal.ofReal (1 - θ) • Measure.dirac (restock S x)

variable {S : ℕ}

/-- The definition of `discKernel`. -/
theorem discKernel_apply (x : ℕ) : discKernel θ S x =
    ENNReal.ofReal θ • Measure.dirac (restock S x - 1) +
      ENNReal.ofReal (1 - θ) • Measure.dirac (restock S x) := rfl

/-- No order is placed at a positive stock. -/
theorem restock_of_ne_zero {x : ℕ} (hx : x ≠ 0) : restock S x = x := by simp [restock, hx]

/-- At a stock-out the stock is raised to `S`. -/
theorem restock_zero : restock S 0 = S := by simp [restock]

/-- No order is placed at a positive stock. -/
theorem restock_succ (z : ℕ) : restock S (z + 1) = z + 1 := restock_of_ne_zero (by omega)

/-- `discKernel θ S` is a Markov kernel for `0 ≤ θ ≤ 1`. -/
theorem isMarkov_discKernel (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : IsMarkovKernel (discKernel θ S) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [discKernel_apply]
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-- Every subset of `ℕ` is measurable. -/
theorem discMeasurableSet (A : Set ℕ) : MeasurableSet A := MeasurableSet.of_discrete

/-- First-step analysis: `(η ∘ P)(x, A) = θη(r(x) − 1, A) + (1 − θ)η(r(x), A)`, `r = restock`. -/
theorem comp_discKernel_real (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (η : Kernel ℕ ℕ) [IsFiniteKernel η]
    (x : ℕ) (A : Set ℕ) :
    ((η ∘ₖ discKernel θ S) x).real A =
      θ * (η (restock S x - 1)).real A + (1 - θ) * (η (restock S x)).real A := by
  rw [measureReal_def, Kernel.comp_apply' _ _ _ (discMeasurableSet A), discKernel_apply,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  rfl

/-- First-step analysis for `Pⁿ⁺¹`. -/
theorem discKpow_succ_real (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n x : ℕ) (A : Set ℕ) :
    (kpow (discKernel θ S) (n + 1) x).real A =
      θ * (kpow (discKernel θ S) n (restock S x - 1)).real A +
        (1 - θ) * (kpow (discKernel θ S) n (restock S x)).real A := by
  have := isMarkov_discKernel (S := S) h0 h1
  have := isMarkov_kpow (κ := discKernel θ S) n
  exact comp_discKernel_real h0 h1 _ x A

/-- `δ_a({y})` as an indicator. -/
theorem dirac_real_singleton_nat (a y : ℕ) :
    (Measure.dirac a).real {y} = if a = y then 1 else 0 := by
  by_cases h : a = y
  · subst h; simp
  · simp [h, measureReal_def]

/-- The transition probabilities `P(x, {y})`. -/
theorem discKernel_real_singleton (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℕ) :
    (discKernel θ S x).real {y} =
      θ * (if restock S x - 1 = y then 1 else 0) +
        (1 - θ) * (if restock S x = y then 1 else 0) := by
  have := discKpow_succ_real (S := S) h0 h1 0 x {y}
  simp only [kpow, Kernel.id_apply] at this
  rw [Kernel.id_comp] at this
  rw [this]
  rw [dirac_real_singleton_nat, dirac_real_singleton_nat]

/-- `δ_a(A)` as an indicator. -/
theorem dirac_real_nat (a : ℕ) (A : Set ℕ) :
    (Measure.dirac a).real A = A.indicator 1 a := by
  by_cases h : a ∈ A <;> simp [measureReal_def, h]

/-- The transition probabilities `P(x, A)`. -/
theorem discKernel_real (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : ℕ) (A : Set ℕ) :
    (discKernel θ S x).real A =
      θ * A.indicator 1 (restock S x - 1) + (1 - θ) * A.indicator 1 (restock S x) := by
  have := comp_discKernel_real (S := S) h0 h1 Kernel.id x A
  rw [Kernel.id_comp, Kernel.id_apply, Kernel.id_apply, dirac_real_nat, dirac_real_nat] at this
  exact this

/-- A closed set (`P(x, Fᶜ) = 0` for `x ∈ F`) is closed for every `Pⁿ`. -/
theorem kpow_compl_eq_zero_of_closed {X : Type*} [MeasurableSpace X] {κ : Kernel X X}
    [IsMarkovKernel κ] {F : Set X} (hF : MeasurableSet F) (h : ∀ x ∈ F, κ x Fᶜ = 0) :
    ∀ n, ∀ x ∈ F, kpow κ n x Fᶜ = 0 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [kpow, Kernel.id_apply]
    rw [Measure.dirac_apply' _ hF.compl, Set.indicator_of_notMem (not_not_intro hx)]
  | succ n ih =>
    intro x hx
    simp only [kpow]
    rw [Kernel.comp_apply' _ _ _ hF.compl]
    have hae : ∀ᵐ x' ∂κ x, x' ∈ F := by
      have := (measure_eq_zero_iff_ae_notMem).1 (h x hx)
      filter_upwards [this] with x' hx' using not_not.1 hx'
    rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with x' hx' using ih x' hx'),
      lintegral_zero]


/-- Ordering never raises the stock above `max(x, S)`. -/
theorem restock_le {M x : ℕ} (hSM : S ≤ M) (hx : x ≤ M) : restock S x ≤ M := by
  unfold restock; split_ifs <;> omega

/-- `{0, …, M}` is closed for `M ≥ S`. -/
theorem discKernel_compl_Iic (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {M : ℕ} (hSM : S ≤ M) {x : ℕ}
    (hx : x ≤ M) : discKernel θ S x (Iic M)ᶜ = 0 := by
  have := isMarkov_discKernel (S := S) h0 h1
  have h := discKernel_real (S := S) h0 h1 x (Iic M)ᶜ
  have ha : restock S x - 1 ∉ (Iic M)ᶜ := not_not_intro (by
    simp only [mem_Iic]; have := restock_le hSM hx; omega)
  have hb : restock S x ∉ (Iic M)ᶜ := not_not_intro (by
    simp only [mem_Iic]; exact restock_le hSM hx)
  rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb] at h
  simp only [mul_zero, add_zero] at h
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h

/-- `{0, …, M}` is closed for `Pⁿ`, `M ≥ S`. -/
theorem discKpow_compl_Iic (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {M : ℕ} (hSM : S ≤ M) (n : ℕ) {x : ℕ}
    (hx : x ≤ M) : kpow (discKernel θ S) n x (Iic M)ᶜ = 0 := by
  have := isMarkov_discKernel (S := S) h0 h1
  exact kpow_compl_eq_zero_of_closed measurableSet_Iic
    (fun y hy => discKernel_compl_Iic h0 h1 hSM hy) n x hx

/-- `Pⁿ(x, {0, …, M}) = 1` for `x ≤ M`, `M ≥ S`. -/
theorem discKpow_real_Iic (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {M : ℕ} (hSM : S ≤ M) (n : ℕ) {x : ℕ}
    (hx : x ≤ M) : (kpow (discKernel θ S) n x).real (Iic M) = 1 := by
  have := isMarkov_discKernel (S := S) h0 h1
  have := isMarkov_kpow (κ := discKernel θ S) n
  have h := probReal_compl_eq_one_sub (μ := kpow (discKernel θ S) n x) (measurableSet_Iic (a := M))
  rw [measureReal_def, discKpow_compl_Iic h0 h1 hSM n hx] at h
  simp at h; linarith

/-- Chapman–Kolmogorov lower bound through an intermediate state:
`Pⁿ(x, {y}) Pᵐ(y, {z}) ≤ Pⁿ⁺ᵐ(x, {z})`. -/
theorem kpow_chapman_real_nat (κ : Kernel ℕ ℕ) [IsMarkovKernel κ] (n m x y z : ℕ) :
    (kpow κ n x).real {y} * (kpow κ m y).real {z} ≤ (kpow κ (n + m) x).real {z} := by
  have := isMarkov_kpow (κ := κ) (n + m)
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [kpow_add_apply n m x (measurableSet_singleton z)]
  calc kpow κ n x {y} * kpow κ m y {z} = ∫⁻ x' in {y}, kpow κ m x' {z} ∂kpow κ n x := by
        rw [lintegral_singleton, mul_comm]
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- Going down `d` units in `d` periods: `Pᵈ(y + d, {y}) ≥ θᵈ`. -/
theorem discKpow_down (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (d y : ℕ) :
    θ ^ d ≤ (kpow (discKernel θ S) d (y + d)).real {y} := by
  have := isMarkov_discKernel (S := S) h0 h1
  induction d with
  | zero => simp [kpow, Kernel.id_apply]
  | succ d ih =>
    have := isMarkov_kpow (κ := discKernel θ S) d
    rw [discKpow_succ_real h0 h1, restock_of_ne_zero (by omega),
      show y + (d + 1) - 1 = y + d by omega, pow_succ]
    nlinarith [measureReal_nonneg (μ := kpow (discKernel θ S) d (y + (d + 1))) (s := {y})]

/-- Staying put for `d` periods at `x ≥ 1`: `Pᵈ(x, {x}) ≥ (1 − θ)ᵈ`. -/
theorem discKpow_stay (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (d : ℕ) {x : ℕ} (hx : x ≠ 0) :
    (1 - θ) ^ d ≤ (kpow (discKernel θ S) d x).real {x} := by
  have := isMarkov_discKernel (S := S) h0 h1
  induction d with
  | zero => simp [kpow, Kernel.id_apply]
  | succ d ih =>
    have := isMarkov_kpow (κ := discKernel θ S) d
    rw [discKpow_succ_real h0 h1, restock_of_ne_zero hx, pow_succ]
    nlinarith [measureReal_nonneg (μ := kpow (discKernel θ S) d (x - 1)) (s := {x})]

/-- `P(0, {S}) ≥ 1 − θ`. -/
theorem discKpow_one_zero_S (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    1 - θ ≤ (kpow (discKernel θ S) 1 0).real {S} := by
  have := isMarkov_discKernel (S := S) h0 h1
  rw [kpow_one, discKernel_real_singleton h0 h1, restock_zero]
  simp only [↓reduceIte, mul_one]
  have : 0 ≤ θ * (if S - 1 = S then (1 : ℝ) else 0) := by split_ifs <;> simp [h0]
  linarith

/-- The path `x → 0 → S → y`: `P^{x+1+(S−y)}(x, {y}) ≥ θˣ(1 − θ)θ^{S−y}`. -/
theorem discKpow_path (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {x y : ℕ} (hy : y ≤ S) :
    θ ^ x * (1 - θ) * θ ^ (S - y) ≤ (kpow (discKernel θ S) (x + 1 + (S - y)) x).real {y} := by
  have := isMarkov_discKernel (S := S) h0 h1
  have hA := discKpow_down (S := S) h0 h1 x 0
  rw [zero_add] at hA
  have hB := discKpow_one_zero_S (S := S) h0 h1
  have hC := discKpow_down (S := S) h0 h1 (S - y) y
  rw [Nat.add_sub_cancel' hy] at hC
  have h01 := kpow_chapman_real_nat (discKernel θ S) x 1 x 0 S
  have h02 := kpow_chapman_real_nat (discKernel θ S) (x + 1) (S - y) x S y
  have hθx : 0 ≤ θ ^ x := pow_nonneg h0 x
  have h1θ : 0 ≤ 1 - θ := by linarith
  calc θ ^ x * (1 - θ) * θ ^ (S - y)
      ≤ (kpow (discKernel θ S) x x).real {0} * (kpow (discKernel θ S) 1 0).real {S} *
          (kpow (discKernel θ S) (S - y) S).real {y} := by
        gcongr
    _ ≤ (kpow (discKernel θ S) (x + 1) x).real {S} * (kpow (discKernel θ S) (S - y) S).real {y} :=
        mul_le_mul_of_nonneg_right h01 measureReal_nonneg
    _ ≤ _ := h02

/-- The path `x → 0 → S`, then staying at `S`: `P^{S+1}(x, {S}) ≥ θˣ(1 − θ)^{1+S−x}`. -/
theorem discKpow_path_S (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hS : 1 ≤ S) {x : ℕ} (hx : x ≤ S) :
    θ ^ x * (1 - θ) * (1 - θ) ^ (S - x) ≤ (kpow (discKernel θ S) (S + 1) x).real {S} := by
  have := isMarkov_discKernel (S := S) h0 h1
  have hA := discKpow_down (S := S) h0 h1 x 0
  rw [zero_add] at hA
  have hB := discKpow_one_zero_S (S := S) h0 h1
  have hC := discKpow_stay (S := S) h0 h1 (S - x) (x := S) (by omega)
  have h01 := kpow_chapman_real_nat (discKernel θ S) x 1 x 0 S
  have h02 := kpow_chapman_real_nat (discKernel θ S) (x + 1) (S - x) x S S
  rw [show x + 1 + (S - x) = S + 1 by omega] at h02
  have hθx : 0 ≤ θ ^ x := pow_nonneg h0 x
  have h1θ : 0 ≤ 1 - θ := by linarith
  calc θ ^ x * (1 - θ) * (1 - θ) ^ (S - x)
      ≤ (kpow (discKernel θ S) x x).real {0} * (kpow (discKernel θ S) 1 0).real {S} *
          (kpow (discKernel θ S) (S - x) S).real {S} := by
        gcongr
    _ ≤ (kpow (discKernel θ S) (x + 1) x).real {S} * (kpow (discKernel θ S) (S - x) S).real {S} :=
        mul_le_mul_of_nonneg_right h01 measureReal_nonneg
    _ ≤ _ := h02


/-- From `y ≤ M` (`M ≥ S`) the chain never reaches a state `z > M`. -/
theorem discKpow_real_singleton_eq_zero (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {M : ℕ} (hSM : S ≤ M) (n : ℕ)
    {y z : ℕ} (hy : y ≤ M) (hz : M < z) : (kpow (discKernel θ S) n y).real {z} = 0 := by
  have := isMarkov_discKernel (S := S) h0 h1
  have := isMarkov_kpow (κ := discKernel θ S) n
  refine le_antisymm ?_ measureReal_nonneg
  have h := measureReal_mono (μ := kpow (discKernel θ S) n y)
    (show {z} ⊆ (Iic M)ᶜ by simp only [singleton_subset_iff, mem_compl_iff, mem_Iic]; omega)
  rwa [measureReal_def (s := (Iic M)ᶜ), discKpow_compl_Iic h0 h1 hSM n hy,
    ENNReal.toReal_zero] at h

/-- Geometric escape from the transient states: `Pⁿ(x, Eᶜ) ≤ (1 − θ/2)ⁿ 2^{x−S}` (a
Lyapunov bound with `V(x) = 2^{x−S}` on `x > S`). -/
theorem discKpow_lyapunov (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n x : ℕ) :
    (kpow (discKernel θ S) n x).real (Iic S)ᶜ ≤ (1 - θ / 2) ^ n * 2 ^ (x - S) := by
  have := isMarkov_discKernel (S := S) h0 h1
  induction n generalizing x with
  | zero =>
    simp only [kpow, Kernel.id_apply, dirac_real_nat, pow_zero, one_mul]
    calc _ ≤ (1 : ℝ) := by
          unfold Set.indicator; split_ifs <;> simp
      _ ≤ _ := one_le_pow₀ (by norm_num)
  | succ n ih =>
    have := isMarkov_kpow (κ := discKernel θ S) n
    by_cases hx : x ≤ S
    · rw [measureReal_def, discKpow_compl_Iic h0 h1 le_rfl _ hx, ENNReal.toReal_zero]
      exact mul_nonneg (pow_nonneg (by linarith) _) (by positivity)
    · rw [discKpow_succ_real h0 h1, restock_of_ne_zero (by omega)]
      have ha := ih (x - 1)
      have hb := ih x
      have h2 : (2 : ℝ) ^ (x - S) = 2 ^ (x - 1 - S) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [h2] at hb ⊢
      have h1θ : 0 ≤ 1 - θ := by linarith
      have := mul_le_mul_of_nonneg_left ha h0
      have := mul_le_mul_of_nonneg_left hb h1θ
      rw [pow_succ]
      nlinarith

/-- **Exercise 13.1b** (p. 390). `E = {0, …, S}` is closed: `P(x, E) = Pⁿ(x, E) = 1` for
`x ∈ E`. -/
theorem ex_13_1b_closed (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {x : ℕ} (hx : x ≤ S) (n : ℕ) :
    discKernel θ S x (Iic S) = 1 ∧ kpow (discKernel θ S) n x (Iic S) = 1 := by
  have := isMarkov_discKernel (S := S) h0 h1
  have := isMarkov_kpow (κ := discKernel θ S) n
  exact ⟨(prob_compl_eq_zero_iff measurableSet_Iic).1 (discKernel_compl_Iic h0 h1 le_rfl hx),
    (prob_compl_eq_zero_iff measurableSet_Iic).1 (discKpow_compl_Iic h0 h1 le_rfl n hx)⟩

/-- **Exercise 13.1b** (p. 390). For `0 < θ < 1` every state `y ∈ E` is reached from every
state `x`, in `x + 1 + (S − y)` steps. -/
theorem ex_13_1b_communicate (h0 : 0 < θ) (h1 : θ < 1) {x y : ℕ} (hy : y ≤ S) :
    0 < (kpow (discKernel θ S) (x + 1 + (S - y)) x).real {y} :=
  lt_of_lt_of_le (by have : 0 < 1 - θ := by linarith
                     positivity) (discKpow_path h0.le h1.le hy)

/-- **Exercise 13.1b** (p. 390). `E` is a minimal closed set (the ergodic set): every nonempty
closed `F ⊆ E` equals `E`. -/
theorem ex_13_1b_minimal (h0 : 0 < θ) (h1 : θ < 1) {F : Set ℕ} (hFE : F ⊆ Iic S)
    (hne : F.Nonempty) (hF : ∀ x ∈ F, discKernel θ S x Fᶜ = 0) : F = Iic S := by
  have := isMarkov_discKernel (S := S) h0.le h1.le
  refine subset_antisymm hFE fun y (hy : y ≤ S) => ?_
  by_contra hyF
  obtain ⟨x, hx⟩ := hne
  have hpos := ex_13_1b_communicate (x := x) h0 h1 hy
  have := isMarkov_kpow (κ := discKernel θ S) (x + 1 + (S - y))
  have hzero := kpow_compl_eq_zero_of_closed (discMeasurableSet F) hF (x + 1 + (S - y)) x hx
  have := measureReal_mono (μ := kpow (discKernel θ S) (x + 1 + (S - y)) x)
    (singleton_subset_iff.2 (show y ∈ Fᶜ from hyF))
  rw [measureReal_def (s := Fᶜ), hzero, ENNReal.toReal_zero] at this
  linarith

/-- **Exercise 13.1b** (p. 390). The states `x > S` are transient: `Pⁿ(x, {x}) = (1 − θ)ⁿ → 0`,
the chain never returns to `x` once it has left it, and `Pⁿ(x, E) → 1` (geometrically). -/
theorem ex_13_1b_transient (h0 : 0 < θ) (h1 : θ ≤ 1) {x : ℕ} (hx : S < x) :
    (∀ n, (kpow (discKernel θ S) n x).real {x} = (1 - θ) ^ n) ∧
    Tendsto (fun n => (kpow (discKernel θ S) n x).real {x}) atTop (𝓝 0) ∧
    (∀ y < x, ∀ n, (kpow (discKernel θ S) n y).real {x} = 0) ∧
    (∀ n, (kpow (discKernel θ S) n x).real (Iic S)ᶜ ≤ (1 - θ / 2) ^ n * 2 ^ (x - S)) ∧
    Tendsto (fun n => (kpow (discKernel θ S) n x).real (Iic S)) atTop (𝓝 1) := by
  have := isMarkov_discKernel (S := S) h0.le h1
  have hnr : ∀ y < x, ∀ n, (kpow (discKernel θ S) n y).real {x} = 0 := fun y hy n =>
    discKpow_real_singleton_eq_zero h0.le h1 (M := x - 1) (by omega) n (by omega) (by omega)
  have hdiag : ∀ n, (kpow (discKernel θ S) n x).real {x} = (1 - θ) ^ n := by
    intro n
    induction n with
    | zero => simp [kpow, Kernel.id_apply]
    | succ n ih =>
      rw [discKpow_succ_real h0.le h1, restock_of_ne_zero (by omega), hnr (x - 1) (by omega), ih,
        pow_succ]
      ring
  refine ⟨hdiag, ?_, hnr, fun n => discKpow_lyapunov h0.le h1 n x, ?_⟩
  · simp only [hdiag]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  · have hlim : Tendsto (fun n => (1 - θ / 2) ^ n * (2 : ℝ) ^ (x - S)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - θ / 2)
        (by linarith)).mul_const ((2 : ℝ) ^ (x - S))
    have hc : Tendsto (fun n => (kpow (discKernel θ S) n x).real (Iic S)ᶜ) atTop (𝓝 0) :=
      squeeze_zero (fun _ => measureReal_nonneg) (fun n => discKpow_lyapunov h0.le h1 n x) hlim
    have heq : ∀ n, (kpow (discKernel θ S) n x).real (Iic S) =
        1 - (kpow (discKernel θ S) n x).real (Iic S)ᶜ := by
      intro n
      have := isMarkov_kpow (κ := discKernel θ S) n
      rw [probReal_compl_eq_one_sub measurableSet_Iic]; ring
    simp only [heq]
    simpa using hc.const_sub 1

/-- **Exercise 13.1b** (p. 390). For `θ < 1` there are no cyclically moving subsets: `E` has no
partition into `k ≥ 2` sets `D₁, …, D_k` with `P(x, D_{i+1}) = 1` for `x ∈ D_i` (indices mod
`k`), because of the self-loop `P(S, {S}) ≥ 1 − θ > 0`. -/
theorem ex_13_1b_not_cyclic (h0 : 0 ≤ θ) (h1 : θ < 1) (hS : 1 ≤ S) (m : ℕ)
    (D : Fin (m + 2) → Set ℕ) (hdisj : Pairwise (Function.onFun Disjoint D))
    (hcover : ⋃ i, D i = Iic S) (hcyc : ∀ i, ∀ x ∈ D i, discKernel θ S x (D (i + 1)) = 1) :
    False := by
  have := isMarkov_discKernel (S := S) h0 h1.le
  have hSmem : S ∈ ⋃ i, D i := hcover ▸ (mem_Iic.2 le_rfl)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hSmem
  have hc := (prob_compl_eq_zero_iff (discMeasurableSet _)).2 (hcyc i S hi)
  have hSi1 : S ∈ D (i + 1) := by
    by_contra hn
    have hstay := discKpow_stay (S := S) h0 h1.le 1 (x := S) (by omega)
    rw [kpow_one, pow_one] at hstay
    have := measureReal_mono (μ := discKernel θ S S)
      (singleton_subset_iff.2 (show S ∈ (D (i + 1))ᶜ from hn))
    rw [measureReal_def (s := (D (i + 1))ᶜ), hc, ENNReal.toReal_zero] at this
    linarith
  have hne : i ≠ i + 1 := by
    intro h
    have := congrArg (· - i) h
    simp at this
  exact Set.disjoint_left.1 (hdisj hne) hi hSi1

/-- For `θ = 1` the chain is deterministic: `x ↦ r(x) − 1`. -/
theorem discKernel_theta_one (S : ℕ) :
    discKernel 1 S =
      Kernel.deterministic (fun x => restock S x - 1) (measurable_of_countable _) := by
  ext x : 1
  rw [discKernel_apply, Kernel.deterministic_apply]
  simp

/-- For `θ = 1`, `d` steps from `y + d` lead to `y`. -/
theorem restock_iterate_down (S d y : ℕ) : (fun x => restock S x - 1)^[d] (y + d) = y := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, restock_of_ne_zero (by omega),
      show y + (d + 1) - 1 = y + d by omega, ih]

/-- **Correction** (NOTE to Exercise 13.1b,c, p. 390). For `θ = 1` and `S ≥ 2` the chain is
the deterministic cycle `0 → S − 1 → ⋯ → 1 → 0` of period `S`: `T*^{Sk}δ₀ = δ₀`,
`T*^{Sk+1}δ₀ = δ_{S−1}`, and `T*ⁿδ₀` converges neither setwise nor in total variation. -/
theorem ex_13_1b_theta_one (hS : 2 ≤ S) :
    (∀ k, kpow (discKernel 1 S) (S * k) 0 = Measure.dirac 0) ∧
    (∀ k, kpow (discKernel 1 S) (S * k + 1) 0 = Measure.dirac (S - 1)) ∧
    (¬ ∃ c, Tendsto (fun n => (kpow (discKernel 1 S) n 0).real {0}) atTop (𝓝 c)) ∧
    ¬ ∃ lam : Measure ℕ, IsProbabilityMeasure lam ∧
      Tendsto (fun n => tvDist (adjointOp (kpow (discKernel 1 S) n) (Measure.dirac 0)) lam)
        atTop (𝓝 0) := by
  set f : ℕ → ℕ := fun x => restock S x - 1
  have hS0 : f^[S] 0 = 0 := by
    obtain ⟨T, rfl⟩ : ∃ T, S = T + 1 := ⟨S - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    have : f 0 = 0 + T := by simp [f, restock_zero]
    rw [this, restock_iterate_down]
  have hk : ∀ k, f^[S * k] 0 = 0 := fun k => by
    rw [Function.iterate_mul]; exact Function.iterate_fixed hS0 k
  have hk1 : ∀ k, f^[S * k + 1] 0 = S - 1 := fun k => by
    rw [Function.iterate_succ_apply', hk k]; simp [f, restock_zero]
  have hA : ∀ k, kpow (discKernel 1 S) (S * k) 0 = Measure.dirac 0 := fun k => by
    rw [discKernel_theta_one, kpow_deterministic, hk]
  have hB : ∀ k, kpow (discKernel 1 S) (S * k + 1) 0 = Measure.dirac (S - 1) := fun k => by
    rw [discKernel_theta_one, kpow_deterministic, hk1]
  have hmul : Tendsto (fun k => S * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k (by omega)) tendsto_id
  have hmul1 : Tendsto (fun k => S * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => by
      change k ≤ S * k + 1; have := Nat.le_mul_of_pos_left k (by omega : 0 < S); omega)
      tendsto_id
  have hnot : ¬ ∃ c, Tendsto (fun n => (kpow (discKernel 1 S) n 0).real {0}) atTop (𝓝 c) := by
    rintro ⟨c, hc⟩
    have e1 := hc.comp hmul
    have e2 := hc.comp hmul1
    have v1 : (fun n => (kpow (discKernel 1 S) n 0).real {0}) ∘ (fun k => S * k) = fun _ => 1 := by
      funext k; simp [hA k]
    have v2 : (fun n => (kpow (discKernel 1 S) n 0).real {0}) ∘ (fun k => S * k + 1) =
        fun _ => 0 := by
      funext k; simp [hB k, show S - 1 ≠ 0 by omega]
    rw [v1] at e1
    rw [v2] at e2
    have := tendsto_nhds_unique e1 tendsto_const_nhds
    have := tendsto_nhds_unique e2 tendsto_const_nhds
    linarith
  refine ⟨hA, hB, hnot, ?_⟩
  rintro ⟨lam, hlam, hconv⟩
  have := isMarkov_discKernel (S := S) zero_le_one le_rfl (θ := 1)
  refine hnot ⟨lam.real {0}, ?_⟩
  have hd : ∀ n, adjointOp (kpow (discKernel 1 S) n) (Measure.dirac 0) =
      kpow (discKernel 1 S) n 0 := fun n => by
    simp only [adjointOp]; exact Measure.dirac_bind (Kernel.measurable _) 0
  have hle : ∀ n, |(kpow (discKernel 1 S) n 0).real {0} - lam.real {0}| ≤
      tvDist (adjointOp (kpow (discKernel 1 S) n) (Measure.dirac 0)) lam := by
    intro n
    have := isMarkov_kpow (κ := discKernel 1 S) n
    have h2 := two_abs_le_tvDist (kpow (discKernel 1 S) n 0) lam (measurableSet_singleton 0)
    rw [hd]
    linarith [abs_nonneg ((kpow (discKernel 1 S) n 0).real {0} - lam.real {0})]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hle hconv


/-! ### Exercise 13.1c: the chain on the ergodic set `E = {0, …, S}` -/

/-- The chain on the ergodic set `E = {0, …, S}` (as the subtype `Iic S`): `P_E(x, A) = P(x, A)`. -/
noncomputable def discKernelE (θ : ℝ) (S : ℕ) : Kernel (Iic S) (Iic S) :=
  Kernel.comapRight (Kernel.comap (discKernel θ S) Subtype.val measurable_subtype_coe)
    (MeasurableEmbedding.subtype_coe measurableSet_Iic)

/-- `discKernelE θ S` is a Markov kernel (because `E` is closed). -/
theorem isMarkov_discKernelE (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : IsMarkovKernel (discKernelE θ S) :=
  Kernel.IsMarkovKernel.comapRight _ _ fun x => by
    rw [Subtype.range_coe, Kernel.comap_apply]
    exact (ex_13_1b_closed h0 h1 x.2 0).1

/-- The chain on `E`, pushed into `ℕ`, is the chain on `ℕ` started in `E`. -/
theorem discKernelE_map (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : Iic S) :
    (discKernelE θ S x).map Subtype.val = discKernel θ S x := by
  ext A hA
  rw [Measure.map_apply measurable_subtype_coe hA, discKernelE,
    Kernel.comapRight_apply' _ _ _ (measurable_subtype_coe hA), Kernel.comap_apply,
    Subtype.image_preimage_coe, inter_comm, measure_inter_conull]
  exact discKernel_compl_Iic h0 h1 le_rfl x.2

/-- `T*` commutes with the inclusion `E → ℕ`. -/
theorem adjointOp_discKernelE_map (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (lam : Measure (Iic S)) :
    (adjointOp (discKernelE θ S) lam).map Subtype.val =
      adjointOp (discKernel θ S) (lam.map Subtype.val) := by
  ext A hA
  rw [Measure.map_apply measurable_subtype_coe hA,
    adjointOp_apply _ _ (measurable_subtype_coe hA), adjointOp_apply _ _ hA,
    lintegral_map (Kernel.measurable_coe _ hA) measurable_subtype_coe]
  refine lintegral_congr fun x => ?_
  rw [← discKernelE_map h0 h1, Measure.map_apply measurable_subtype_coe hA]

/-- `T*ⁿ` commutes with the inclusion `E → ℕ`. -/
theorem adjointOp_discKpowE_map (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n : ℕ) (lam : Measure (Iic S)) :
    (adjointOp (kpow (discKernelE θ S) n) lam).map Subtype.val =
      adjointOp (kpow (discKernel θ S) n) (lam.map Subtype.val) := by
  rw [← adjointOp_iterate, ← adjointOp_iterate]
  induction n generalizing lam with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
      adjointOp_discKernelE_map h0 h1]

/-- `Pⁿ_E(x, ·)`, pushed into `ℕ`, is `Pⁿ(x, ·)`. -/
theorem discKpowE_map (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n : ℕ) (x : Iic S) :
    (kpow (discKernelE θ S) n x).map Subtype.val = kpow (discKernel θ S) n x := by
  have := adjointOp_discKpowE_map h0 h1 n (Measure.dirac x)
  rwa [Measure.map_dirac' measurable_subtype_coe, adjointOp, adjointOp,
    Measure.dirac_bind (Kernel.measurable _), Measure.dirac_bind (Kernel.measurable _)] at this

/-- `Pⁿ_E(x, {s}) = Pⁿ(x, {s})`. -/
theorem discKpowE_real_singleton (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n : ℕ) (x s : Iic S) :
    (kpow (discKernelE θ S) n x).real {s} = (kpow (discKernel θ S) n x).real {(s : ℕ)} := by
  rw [← discKpowE_map h0 h1, measureReal_def, measureReal_def,
    Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
  congr 2
  ext z; simp [Subtype.ext_iff]

/-- **Exercise 13.1c** (p. 390). For `0 < θ < 1` the chain on `E` satisfies Condition M with
`N = S + 1`, `ε = θˢ(1 − θ)^{S+1}`: `P^{S+1}(x, {S}) ≥ ε` for every `x ∈ E` (Exercise 11.5a). -/
theorem ex_13_1c_conditionM (h0 : 0 < θ) (h1 : θ < 1) (hS : 1 ≤ S) :
    ConditionMFor (discKernelE θ S) (S + 1) (θ ^ S * (1 - θ) ^ (S + 1)) := by
  have h1θ : 0 < 1 - θ := by linarith
  refine ⟨by omega, by positivity, fun A _ => ?_⟩
  set s₀ : Iic S := ⟨S, mem_Iic.2 le_rfl⟩
  have hbound : ∀ s, θ ^ S * (1 - θ) ^ (S + 1) ≤ (kpow (discKernelE θ S) (S + 1) s).real {s₀} := by
    intro s
    rw [discKpowE_real_singleton h0.le h1.le]
    refine le_trans ?_ (discKpow_path_S h0.le h1.le hS s.2)
    have ha : θ ^ S ≤ θ ^ (s : ℕ) := pow_le_pow_of_le_one h0.le h1.le s.2
    have hb : (1 - θ) ^ S ≤ (1 - θ) ^ (S - s) :=
      pow_le_pow_of_le_one h1θ.le (by linarith) (Nat.sub_le _ _)
    calc θ ^ S * (1 - θ) ^ (S + 1) = θ ^ S * (1 - θ) * (1 - θ) ^ S := by ring
      _ ≤ θ ^ (s : ℕ) * (1 - θ) * (1 - θ) ^ (S - s) := by gcongr
  have := isMarkov_discKernelE (S := S) h0.le h1.le
  have := isMarkov_kpow (κ := discKernelE θ S) (S + 1)
  by_cases hs₀ : s₀ ∈ A
  · exact Or.inl fun s => (hbound s).trans (measureReal_mono (singleton_subset_iff.2 hs₀))
  · exact Or.inr fun s => (hbound s).trans (measureReal_mono (singleton_subset_iff.2 hs₀))

/-- **Correction** (NOTE to Exercise 13.1c). The bound `Pˢ(x, {0}) ≥ θˢ` on `E` claimed in the
notes is false: for `S = 2`, `θ = 3/4`, `P²(1, {0}) = θ(1 − θ) = 3/16 < 9/16 = θ²`. -/
theorem ex_13_1c_note_counterexample :
    (kpow (discKernelE (3 / 4) 2) 2 ⟨1, by simp⟩).real {⟨0, by simp⟩} = 3 / 16 ∧
      (3 / 16 : ℝ) < (3 / 4) ^ 2 := by
  refine ⟨?_, by norm_num⟩
  rw [discKpowE_real_singleton (by norm_num) (by norm_num)]
  have h := discKpow_succ_real (S := 2) (θ := 3 / 4) (by norm_num) (by norm_num) 1 1 {0}
  rw [kpow_one, discKernel_real_singleton (by norm_num) (by norm_num),
    discKernel_real_singleton (by norm_num) (by norm_num)] at h
  simp only [restock] at h
  norm_num at h ⊢
  exact h


/-- The invariant distribution, written as `π = (1/S) Σ_{z=1}^{S} P(z, ·)`; its weights are
`π₀ = θ/S`, `π_x = 1/S` (`1 ≤ x ≤ S − 1`), `π_S = (1 − θ)/S` (`ex_13_1c_weights`). -/
noncomputable def discPi (θ : ℝ) (S : ℕ) : Measure ℕ :=
  ENNReal.ofReal (1 / S) • ∑ z ∈ Finset.range S, discKernel θ S (z + 1)

/-- `π(A) = (1/S) Σ_{z=1}^{S} P(z, A)`. -/
theorem discPi_apply (A : Set ℕ) :
    discPi θ S A = ENNReal.ofReal (1 / S) * ∑ z ∈ Finset.range S, discKernel θ S (z + 1) A := by
  rw [discPi, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

/-- `π(A) = (1/S) Σ_{z=1}^{S} P(z, A)` in real terms. -/
theorem discPi_real (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (A : Set ℕ) :
    (discPi θ S).real A = 1 / S * ∑ z ∈ Finset.range S, (discKernel θ S (z + 1)).real A := by
  have := isMarkov_discKernel (S := S) h0 h1
  rw [measureReal_def, discPi_apply, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  rfl

/-- `π` is a probability measure. -/
theorem discPi_univ (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hS : 1 ≤ S) :
    IsProbabilityMeasure (discPi θ S) := by
  have := isMarkov_discKernel (S := S) h0 h1
  refine ⟨?_⟩
  rw [discPi_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hS), ENNReal.ofReal_natCast,
    ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : S ≠ 0)) (ENNReal.natCast_ne_top S)]

/-- `π` is concentrated on `E`. -/
theorem discPi_compl (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : discPi θ S (Iic S)ᶜ = 0 := by
  rw [discPi_apply, Finset.sum_eq_zero fun z hz =>
    discKernel_compl_Iic h0 h1 le_rfl (by simp at hz; omega), mul_zero]

/-- `∫ P(y, A) P(x, dy) = θP(r(x) − 1, A) + (1 − θ)P(r(x), A)`. -/
theorem lintegral_discKernel (x : ℕ) (A : Set ℕ) :
    ∫⁻ y, discKernel θ S y A ∂discKernel θ S x =
      ENNReal.ofReal θ * discKernel θ S (restock S x - 1) A +
        ENNReal.ofReal (1 - θ) * discKernel θ S (restock S x) A := by
  rw [discKernel_apply x, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, smul_eq_mul, smul_eq_mul]

/-- `π` is invariant: `T*π = π` (on `ℕ`). The proof uses `P(0, ·) = P(S, ·)`. -/
theorem discPi_invariant (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hS : 1 ≤ S) :
    adjointOp (discKernel θ S) (discPi θ S) = discPi θ S := by
  ext A hA
  rw [adjointOp_apply _ _ hA, discPi, lintegral_smul_measure, lintegral_finsetSum_measure,
    Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  simp only [lintegral_discKernel, restock_succ, Nat.add_sub_cancel, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hshift : ∑ z ∈ Finset.range S, discKernel θ S z A =
      ∑ z ∈ Finset.range S, discKernel θ S (z + 1) A := by
    obtain ⟨T, rfl⟩ : ∃ T, S = T + 1 := ⟨S - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    congr 2
  rw [hshift, ← add_mul, ← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-- The weights of `π`: `π{y} = (θ[y < S] + (1 − θ)[1 ≤ y ≤ S])/S`. -/
theorem discPi_real_singleton (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (y : ℕ) :
    (discPi θ S).real {y} =
      1 / S * (θ * (if y < S then 1 else 0) + (1 - θ) * (if 1 ≤ y ∧ y ≤ S then 1 else 0)) := by
  rw [discPi_real h0 h1]
  congr 1
  simp only [discKernel_real_singleton h0 h1, restock_succ, Nat.add_sub_cancel,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  · simp
  · rcases y with _ | y
    · simp
    · simp

/-- **Exercise 13.1c** (p. 390), the characterisation of the invariant distribution:
`π₀ = θ/S`, `π_x = 1/S` for `1 ≤ x ≤ S − 1`, `π_S = (1 − θ)/S`, and `π_x = 0` for `x > S`
(for `S = 1`: `π₀ = θ`, `π₁ = 1 − θ`). -/
theorem ex_13_1c_weights (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hS : 1 ≤ S) :
    (discPi θ S).real {0} = θ / S ∧
    (∀ y, 1 ≤ y → y < S → (discPi θ S).real {y} = 1 / S) ∧
    (discPi θ S).real {S} = (1 - θ) / S ∧
    ∀ y, S < y → (discPi θ S).real {y} = 0 := by
  refine ⟨?_, fun y hy hyS => ?_, ?_, fun y hy => ?_⟩ <;> rw [discPi_real_singleton h0 h1]
  · simp [show 0 < S by omega]; ring
  · simp [hyS, hy, hyS.le]
  · simp [show 1 ≤ S from hS]; ring
  · simp [show ¬ y < S by omega, show ¬ y ≤ S by omega]


/-- Under Condition M, two invariant probability measures coincide (Lemma 11.11 with `k = 1`). -/
theorem invariant_eq_of_conditionMFor {X : Type*} [MeasurableSpace X] {κ : Kernel X X}
    [IsMarkovKernel κ] {N : ℕ} {ε : ℝ} (hM : ConditionMFor κ N ε) {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : adjointOp κ μ = μ)
    (hν : adjointOp κ ν = ν) : μ = ν := by
  have hfix : ∀ (lam : Measure X), adjointOp κ lam = lam → adjointOp (kpow κ (N * 1)) lam = lam :=
    fun lam h => by rw [← adjointOp_iterate]; exact Function.iterate_fixed h _
  have h := tvDist_iterate_le hM μ ν 1
  rw [hfix μ hμ, hfix ν hν, pow_one] at h
  have h0 := tvDist_nonneg μ ν
  have hε := hM.2.1
  exact eq_of_tvDist_eq_zero (by nlinarith)

/-- The invariant distribution on `E`, the restriction of `π`. -/
noncomputable def discPiE (θ : ℝ) (S : ℕ) : Measure (Iic S) :=
  (discPi θ S).comap Subtype.val

/-- A measure on `ℕ` concentrated on `E` is the push-forward of its restriction to `E`. -/
theorem map_comap_Iic_of_compl_null {μ : Measure ℕ} (h : μ (Iic S)ᶜ = 0) :
    (μ.comap Subtype.val).map (Subtype.val : Iic S → ℕ) = μ := by
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Iic).map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem ((measure_eq_zero_iff_ae_notMem).1 h |>.mono
    fun _ hx => not_not.1 hx)

/-- The restriction to `E` of a probability measure concentrated on `E` is a probability
measure. -/
theorem isProb_comap_Iic_of_compl_null {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (h : μ (Iic S)ᶜ = 0) : IsProbabilityMeasure (μ.comap (Subtype.val : Iic S → ℕ)) := by
  refine ⟨?_⟩
  have := congrArg (· univ) (map_comap_Iic_of_compl_null h)
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at this
  rw [this, measure_univ]

/-- The restriction to `E` of an invariant measure concentrated on `E` is invariant for the
chain on `E`. -/
theorem invariantE_of_invariant (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {μ : Measure ℕ}
    (hc : μ (Iic S)ᶜ = 0) (hμ : adjointOp (discKernel θ S) μ = μ) :
    adjointOp (discKernelE θ S) (μ.comap Subtype.val) = μ.comap Subtype.val := by
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_Iic (a := S))
  rw [← hemb.comap_map (adjointOp (discKernelE θ S) (μ.comap Subtype.val)),
    adjointOp_discKernelE_map h0 h1, map_comap_Iic_of_compl_null hc, hμ]

/-- `Pⁿ(x, E) → 1` for every `x`: `Pⁿ(x, Eᶜ) → 0`. -/
theorem tendsto_discKpow_real_compl (h0 : 0 < θ) (h1 : θ ≤ 1) (x : ℕ) :
    Tendsto (fun n => (kpow (discKernel θ S) n x).real (Iic S)ᶜ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => (1 - θ / 2) ^ n * (2 : ℝ) ^ (x - S)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - θ / 2)
      (by linarith)).mul_const ((2 : ℝ) ^ (x - S))
  exact squeeze_zero (fun _ => measureReal_nonneg) (fun n => discKpow_lyapunov h0.le h1 n x) hlim

/-- **Exercise 13.1c** (p. 390), on `E`. For `0 < θ < 1` and `S ≥ 1`, `π_E` is the unique
invariant probability measure of the chain on `E`, and `T*ⁿλ₀ → π_E` in total variation for every
initial `λ₀`, with `‖T*ⁿλ₀ − π_E‖ ≤ 2(1 − ε)^{⌊n/(S+1)⌋}`, `ε = θˢ(1 − θ)^{S+1}` (Theorem 11.12). -/
theorem ex_13_1c (h0 : 0 < θ) (h1 : θ < 1) (hS : 1 ≤ S) :
    IsProbabilityMeasure (discPiE θ S) ∧
    adjointOp (discKernelE θ S) (discPiE θ S) = discPiE θ S ∧
    (∀ μ : Measure (Iic S), IsProbabilityMeasure μ →
      adjointOp (discKernelE θ S) μ = μ → μ = discPiE θ S) ∧
    ∀ (l₀ : Measure (Iic S)) [IsProbabilityMeasure l₀],
      (∀ n, tvDist (adjointOp (kpow (discKernelE θ S) n) l₀) (discPiE θ S) ≤
        2 * (1 - θ ^ S * (1 - θ) ^ (S + 1)) ^ (n / (S + 1))) ∧
      Tendsto (fun n => tvDist (adjointOp (kpow (discKernelE θ S) n) l₀) (discPiE θ S))
        atTop (𝓝 0) := by
  have := isMarkov_discKernelE (S := S) h0.le h1.le
  have := discPi_univ (S := S) h0.le h1.le hS
  have hc := discPi_compl (S := S) h0.le h1.le
  have hP : IsProbabilityMeasure (discPiE θ S) := isProb_comap_Iic_of_compl_null hc
  have hinv : adjointOp (discKernelE θ S) (discPiE θ S) = discPiE θ S :=
    invariantE_of_invariant h0.le h1.le hc (discPi_invariant h0.le h1.le hS)
  have hM := ex_13_1c_conditionM h0 h1 hS
  have : Nonempty (Iic S) := ⟨⟨0, by simp⟩⟩
  obtain ⟨lstar, hlp, -, -, hlinv, hbound⟩ := theorem_11_12 hM
  have heq : discPiE θ S = lstar := invariant_eq_of_conditionMFor hM hinv hlinv
  subst heq
  refine ⟨hP, hinv, fun μ hμ hμinv => invariant_eq_of_conditionMFor hM hμinv hinv,
    fun l₀ _ => ⟨hbound l₀, ?_⟩⟩
  set ε := θ ^ S * (1 - θ) ^ (S + 1)
  have hε0 : 0 < ε := by have : 0 < 1 - θ := by linarith
                         positivity
  have hε1 : ε ≤ 1 := by
    have ha : θ ^ S ≤ 1 := pow_le_one₀ h0.le h1.le
    have hb : (1 - θ) ^ (S + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    calc ε ≤ 1 * 1 := mul_le_mul ha hb (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hlim : Tendsto (fun n => 2 * (1 - ε) ^ (n / (S + 1))) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - ε)
      (by linarith)).comp (Nat.tendsto_div_const_atTop (by omega : S + 1 ≠ 0))).const_mul 2
    simpa using this
  exact squeeze_zero (fun n => by
    have := isProb_adjoint (κ := discKernelE θ S) n l₀
    exact tvDist_nonneg _ _) (hbound l₀) hlim


/-- The weights of `π_E` are those of `π`. -/
theorem discPiE_real_singleton (s : Iic S) :
    (discPiE θ S).real {s} = (discPi θ S).real {(s : ℕ)} := by
  rw [measureReal_def, measureReal_def, discPiE,
    (MeasurableEmbedding.subtype_coe measurableSet_Iic).comap_apply, image_singleton]

/-- **Exercise 13.1c** (p. 390), on `ℕ`. `π` is an invariant probability measure of the chain on
`ℕ`, and every invariant probability measure on `ℕ` is concentrated on `E` and equals `π`. -/
theorem ex_13_1c_nat (h0 : 0 < θ) (h1 : θ < 1) (hS : 1 ≤ S) :
    IsProbabilityMeasure (discPi θ S) ∧ adjointOp (discKernel θ S) (discPi θ S) = discPi θ S ∧
    ∀ μ : Measure ℕ, IsProbabilityMeasure μ → adjointOp (discKernel θ S) μ = μ →
      μ (Iic S)ᶜ = 0 ∧ μ = discPi θ S := by
  have := isMarkov_discKernel (S := S) h0.le h1.le
  have hπ := discPi_univ (S := S) h0.le h1.le hS
  refine ⟨hπ, discPi_invariant h0.le h1.le hS, fun μ hμ hinv => ?_⟩
  -- the mass off `E` vanishes
  have hfix : ∀ n, adjointOp (kpow (discKernel θ S) n) μ = μ := fun n => by
    rw [← adjointOp_iterate]; exact Function.iterate_fixed hinv n
  have hreal : ∀ n, μ.real (Iic S)ᶜ = ∫ x, (kpow (discKernel θ S) n x).real (Iic S)ᶜ ∂μ := by
    intro n
    have := isMarkov_kpow (κ := discKernel θ S) n
    have h := bind_real_eq (kpow (discKernel θ S) n) μ (measurableSet_Iic (a := S)).compl
    rwa [hfix n] at h
  have hlim : Tendsto (fun n => ∫ x, (kpow (discKernel θ S) n x).real (Iic S)ᶜ ∂μ) atTop
      (𝓝 (∫ _, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => AEStronglyMeasurable.of_discrete) (integrable_const 1) (fun n => ?_)
      (ae_of_all _ fun x => tendsto_discKpow_real_compl h0 h1.le x)
    refine ae_of_all _ fun x => ?_
    have := isMarkov_kpow (κ := discKernel θ S) n
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  rw [integral_zero] at hlim
  have hc0 : μ.real (Iic S)ᶜ = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr hreal) hlim
  have hc : μ (Iic S)ᶜ = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hc0
  refine ⟨hc, ?_⟩
  -- the restriction to `E` is invariant for the chain on `E`
  have hμE := isProb_comap_Iic_of_compl_null hc
  have hπE : IsProbabilityMeasure (discPiE θ S) :=
    isProb_comap_Iic_of_compl_null (discPi_compl h0.le h1.le)
  have := isMarkov_discKernelE (S := S) h0.le h1.le
  have heq : μ.comap Subtype.val = discPiE θ S :=
    invariant_eq_of_conditionMFor (ex_13_1c_conditionM h0 h1 hS)
      (invariantE_of_invariant h0.le h1.le hc hinv)
      (invariantE_of_invariant h0.le h1.le (discPi_compl h0.le h1.le)
        (discPi_invariant h0.le h1.le hS))
  rw [← map_comap_Iic_of_compl_null hc, heq, discPiE,
    map_comap_Iic_of_compl_null (discPi_compl h0.le h1.le)]

/-- From a state `x > S + n`, `E` is not reached in `n` steps. -/
theorem discKpow_real_Iic_eq_zero (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n : ℕ) {x : ℕ} (hx : S + n < x) :
    (kpow (discKernel θ S) n x).real (Iic S) = 0 := by
  have := isMarkov_discKernel (S := S) h0 h1
  induction n generalizing x with
  | zero => simp [kpow, Kernel.id_apply, show ¬ x ≤ S by omega]
  | succ n ih =>
    rw [discKpow_succ_real h0 h1, restock_of_ne_zero (by omega), ih (by omega), ih (by omega)]
    ring

/-- **Correction** (NOTE to Exercise 13.1c). Condition M fails for the chain on all of `ℕ`: from
`x > S + N` the set `E` is not reached in `N` steps, and from `0` its complement is never
reached. -/
theorem ex_13_1c_not_conditionM_nat (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ¬ ConditionM (discKernel θ S) := by
  rintro ⟨N, ε, -, hε, hM⟩
  have := isMarkov_discKernel (S := S) h0 h1
  rcases hM (Iic S) measurableSet_Iic with h | h
  · have := h (S + N + 1)
    rw [discKpow_real_Iic_eq_zero h0 h1 N (by omega)] at this
    linarith
  · have := h 0
    rw [measureReal_def, discKpow_compl_Iic h0 h1 le_rfl N (Nat.zero_le S)] at this
    simp at this; linarith

/-- The manual's answer to Exercise 13.1c: mass `1/S` at each of `0, 1, …, S`. -/
noncomputable def manualPi (S : ℕ) : Measure ℕ :=
  ∑ i ∈ Finset.range (S + 1), ENNReal.ofReal (1 / S) • Measure.dirac i

/-- **Correction** (manual, Exercise 13.1c). The manual's answer has total mass `(S + 1)/S ≠ 1`,
so it is not a probability distribution. -/
theorem ex_13_1c_manual_mass (hS : 1 ≤ S) :
    (manualPi S).real univ = (S + 1) / S ∧ manualPi S univ ≠ 1 := by
  have hr : (manualPi S).real univ = (S + 1) / S := by
    rw [measureReal_def, manualPi, Measure.finsetSum_apply,
      ENNReal.toReal_sum (fun _ _ => by simp)]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / S), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  refine ⟨hr, fun h => ?_⟩
  rw [measureReal_def, h, ENNReal.toReal_one, eq_div_iff (by positivity)] at hr
  linarith

/-- **Correction** (manual, Exercise 13.1c). For `S ≥ 2` and `θ < 1` the manual's answer is not
invariant: `T*p̄({0}) = θ/S ≠ 1/S = p̄({0})`. -/
theorem ex_13_1c_manual_not_invariant (h0 : 0 ≤ θ) (h1 : θ < 1) (hS : 2 ≤ S) :
    adjointOp (discKernel θ S) (manualPi S) ≠ manualPi S := by
  intro h
  have := isMarkov_discKernel (S := S) h0 h1.le
  have e := congrArg (· {0}) h
  rw [adjointOp_apply _ _ (measurableSet_singleton 0), manualPi,
    lintegral_finsetSum_measure, Measure.finsetSum_apply] at e
  simp only [lintegral_smul_measure, lintegral_dirac, Measure.smul_apply, smul_eq_mul] at e
  obtain ⟨T, rfl⟩ : ∃ T, S = T + 2 := ⟨S - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_range_succ'] at e
  have hz : ∀ i : ℕ, discKernel θ (T + 2) (i + 1 + 1) {0} = 0 := by
    intro i
    rw [discKernel_apply, restock_succ]
    simp
  simp only [hz, mul_zero, Finset.sum_const_zero, zero_add] at e
  rw [discKernel_apply, discKernel_apply, restock_zero, restock_succ] at e
  have e' : ENNReal.ofReal ((T : ℝ) + 2)⁻¹ * ENNReal.ofReal θ = ENNReal.ofReal ((T : ℝ) + 2)⁻¹ := by
    simpa using e
  have hpos : 0 < ((T : ℝ) + 2)⁻¹ := by positivity
  rw [← ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_eq_ofReal_iff (by positivity) hpos.le] at e'
  nlinarith


/-- `‖T*μ − ν‖ ≤ ∫ ‖P(x, ·) − ν‖ μ(dx)` on `ℕ`. -/
theorem tvDist_adjointOp_le_nat (κ : Kernel ℕ ℕ) [IsMarkovKernel κ] (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (adjointOp κ μ) ν ≤ ∫ x, tvDist (κ x) ν ∂μ := by
  have := (theorem_8_2 κ μ).1
  have hint : Integrable (fun x => tvDist (κ x) ν) μ :=
    integrable_of_abs_le μ (Measurable.of_discrete) (C := 2) fun x => by
      rw [abs_of_nonneg (tvDist_nonneg _ _)]; exact tvDist_le_two _ _
  have h := tvDist_le_of_forall (adjointOp κ μ) ν (δ := (∫ x, tvDist (κ x) ν ∂μ) / 2)
    fun A hA => by
      have hf : Integrable (fun x => (κ x).real A) μ :=
        integrable_of_abs_le μ (Measurable.of_discrete) (C := 1) fun x => by
          rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
      have hc : ν.real A = ∫ _, ν.real A ∂μ := by simp
      rw [bind_real_eq κ μ hA, hc, ← integral_sub hf (integrable_const _)]
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_div]
      refine integral_mono (hf.sub (integrable_const _)).abs (hint.div_const _) fun x => ?_
      have := two_abs_le_tvDist (κ x) ν hA
      dsimp only; linarith
  linarith


/-- The inclusion `E → ℕ` does not increase total variation distances. -/
theorem tvDist_map_subtype_le (μ ν : Measure (Iic S)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tvDist (μ.map Subtype.val) (ν.map Subtype.val) ≤ tvDist μ ν := by
  have h := tvDist_le_of_forall (μ.map Subtype.val) (ν.map Subtype.val)
    (δ := tvDist μ ν / 2) fun A hA => by
      rw [measureReal_def, measureReal_def, Measure.map_apply measurable_subtype_coe hA,
        Measure.map_apply measurable_subtype_coe hA]
      have := two_abs_le_tvDist μ ν (measurable_subtype_coe hA)
      rw [measureReal_def, measureReal_def] at this
      linarith
  linarith

/-- `Pⁿ(x, ·) → π` in total variation for `x ∈ E`. -/
theorem tendsto_tvDist_discKpow_of_le (h0 : 0 < θ) (h1 : θ < 1) (hS : 1 ≤ S) {x : ℕ}
    (hx : x ≤ S) :
    Tendsto (fun k => tvDist (kpow (discKernel θ S) k x) (discPi θ S)) atTop (𝓝 0) := by
  have := isMarkov_discKernel (S := S) h0.le h1.le
  have := isMarkov_discKernelE (S := S) h0.le h1.le
  have := discPi_univ (S := S) h0.le h1.le hS
  obtain ⟨hP, -, -, hconv⟩ := ex_13_1c h0 h1 hS
  set x' : Iic S := ⟨x, hx⟩
  have hlim := (hconv (Measure.dirac x')).2
  have hd : ∀ k, adjointOp (kpow (discKernelE θ S) k) (Measure.dirac x') =
      kpow (discKernelE θ S) k x' := fun k => by
    simp only [adjointOp]; exact Measure.dirac_bind (Kernel.measurable _) _
  simp only [hd] at hlim
  refine squeeze_zero (fun k => by
    have := isMarkov_kpow (κ := discKernel θ S) k
    exact tvDist_nonneg _ _) (fun k => ?_) hlim
  have := isMarkov_kpow (κ := discKernelE θ S) k
  have e1 := discKpowE_map h0.le h1.le k x'
  have e2 : (discPiE θ S).map Subtype.val = discPi θ S :=
    map_comap_Iic_of_compl_null (discPi_compl h0.le h1.le)
  have := tvDist_map_subtype_le (kpow (discKernelE θ S) k x') (discPiE θ S)
  rwa [e1, e2] at this

/-- `Pⁿ(x, ·) → π` in total variation for every `x ∈ ℕ`: split `Pᵐ⁺ᵏ(x, ·)` through
`Pᵐ(x, ·)`, whose mass off `E` tends to zero. -/
theorem tendsto_tvDist_discKpow (h0 : 0 < θ) (h1 : θ < 1) (hS : 1 ≤ S) (x : ℕ) :
    Tendsto (fun k => tvDist (kpow (discKernel θ S) k x) (discPi θ S)) atTop (𝓝 0) := by
  have := isMarkov_discKernel (S := S) h0.le h1.le
  have := discPi_univ (S := S) h0.le h1.le hS
  set e : ℕ → ℝ := fun k =>
    ∑ y ∈ Finset.range (S + 1), tvDist (kpow (discKernel θ S) k y) (discPi θ S)
  have he : Tendsto e atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (S + 1)) fun y hy =>
      tendsto_tvDist_discKpow_of_le h0 h1 hS (x := y) (by simp at hy; omega)
    simpa using this
  have hbound : ∀ m k, tvDist (kpow (discKernel θ S) (m + k) x) (discPi θ S) ≤
      e k + 2 * (kpow (discKernel θ S) m x).real (Iic S)ᶜ := by
    intro m k
    have := isMarkov_kpow (κ := discKernel θ S) m
    have := isMarkov_kpow (κ := discKernel θ S) k
    have hk : kpow (discKernel θ S) (m + k) x =
        adjointOp (kpow (discKernel θ S) k) (kpow (discKernel θ S) m x) := by
      rw [kpow_add, Kernel.comp_apply]; rfl
    rw [hk]
    refine (tvDist_adjointOp_le_nat _ _ _).trans ?_
    have hg : ∀ y, tvDist (kpow (discKernel θ S) k y) (discPi θ S) ≤
        e k + 2 * (Iic S)ᶜ.indicator 1 y := by
      intro y
      have he0 : 0 ≤ e k := Finset.sum_nonneg fun _ _ => tvDist_nonneg _ _
      by_cases hy : y ≤ S
      · rw [Set.indicator_of_notMem (not_not_intro (mem_Iic.2 hy)), mul_zero, add_zero]
        exact Finset.single_le_sum (f := fun y => tvDist (kpow (discKernel θ S) k y) (discPi θ S))
          (fun _ _ => tvDist_nonneg _ _) (Finset.mem_range.2 (by omega))
      · rw [Set.indicator_of_mem (show y ∈ (Iic S)ᶜ by simp; omega), Pi.one_apply]
        linarith [tvDist_le_two (kpow (discKernel θ S) k y) (discPi θ S)]
    have hi : Integrable (fun y => e k + 2 * (Iic S)ᶜ.indicator 1 y) (kpow (discKernel θ S) m x) :=
      (integrable_const _).add ((integrable_const 1).indicator measurableSet_Iic.compl
        |>.const_mul 2)
    calc ∫ y, tvDist (kpow (discKernel θ S) k y) (discPi θ S) ∂kpow (discKernel θ S) m x
        ≤ ∫ y, (e k + 2 * (Iic S)ᶜ.indicator 1 y) ∂kpow (discKernel θ S) m x :=
          integral_mono (integrable_of_abs_le _ Measurable.of_discrete (C := 2) fun y => by
            rw [abs_of_nonneg (tvDist_nonneg _ _)]; exact tvDist_le_two _ _) hi hg
      _ = e k + 2 * (kpow (discKernel θ S) m x).real (Iic S)ᶜ := by
          rw [integral_add (integrable_const _) ((integrable_const 1).indicator
            measurableSet_Iic.compl |>.const_mul 2), integral_const, integral_const_mul,
            integral_indicator_one measurableSet_Iic.compl]
          simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨m, hm⟩ := ((tendsto_discKpow_real_compl h0 h1.le (S := S) x).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 4))).exists
  obtain ⟨K, hK⟩ := eventually_atTop.1 (he.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < δ / 2)))
  refine ⟨m + K, fun n hn => ?_⟩
  have := isMarkov_kpow (κ := discKernel θ S) n
  have h := hbound m (n - m)
  rw [Nat.add_sub_cancel' (by omega)] at h
  have := hK (n - m) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tvDist_nonneg _ _)]
  linarith

/-- **Exercise 13.1c** (p. 390), convergence on `ℕ`. For `0 < θ < 1`, `T*ⁿλ₀ → π` in total
variation for every initial probability `λ₀` on `ℕ` (dominated convergence over `λ₀`). -/
theorem ex_13_1c_nat_convergence (h0 : 0 < θ) (h1 : θ < 1) (hS : 1 ≤ S) (l₀ : Measure ℕ)
    [IsProbabilityMeasure l₀] :
    Tendsto (fun n => tvDist (adjointOp (kpow (discKernel θ S) n) l₀) (discPi θ S)) atTop
      (𝓝 0) := by
  have := isMarkov_discKernel (S := S) h0.le h1.le
  have := discPi_univ (S := S) h0.le h1.le hS
  have hlim : Tendsto (fun n => ∫ x, tvDist (kpow (discKernel θ S) n x) (discPi θ S) ∂l₀) atTop
      (𝓝 (∫ _, (0 : ℝ) ∂l₀)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 2)
      (fun n => AEStronglyMeasurable.of_discrete) (integrable_const 2) (fun n => ?_)
      (ae_of_all _ fun x => tendsto_tvDist_discKpow h0 h1 hS x)
    refine ae_of_all _ fun x => ?_
    have := isMarkov_kpow (κ := discKernel θ S) n
    rw [Real.norm_eq_abs, abs_of_nonneg (tvDist_nonneg _ _)]
    exact tvDist_le_two _ _
  rw [integral_zero] at hlim
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · have := isProb_adjoint (κ := discKernel θ S) n l₀
    exact tvDist_nonneg _ _
  · have := isMarkov_kpow (κ := discKernel θ S) n
    exact tvDist_adjointOp_le_nat _ _ _

/-- The convergence on `ℕ` is not uniform in the initial distribution (NOTE to
Exercise 13.1c): `‖T*ⁿδ_{S+n+1} − π‖ = 2` for every `n`. -/
theorem ex_13_1c_nat_not_uniform (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hS : 1 ≤ S) (n : ℕ) :
    2 ≤ tvDist (adjointOp (kpow (discKernel θ S) n) (Measure.dirac (S + n + 1))) (discPi θ S) := by
  have := isMarkov_discKernel (S := S) h0 h1
  have := isMarkov_kpow (κ := discKernel θ S) n
  have := discPi_univ (S := S) h0 h1 hS
  have hd : adjointOp (kpow (discKernel θ S) n) (Measure.dirac (S + n + 1)) =
      kpow (discKernel θ S) n (S + n + 1) := by
    simp only [adjointOp]; exact Measure.dirac_bind (Kernel.measurable _) _
  rw [hd]
  have h := two_abs_le_tvDist (kpow (discKernel θ S) n (S + n + 1)) (discPi θ S)
    (measurableSet_Iic (a := S))
  have hπ : (discPi θ S).real (Iic S) = 1 := by
    have := probReal_compl_eq_one_sub (μ := discPi θ S) (measurableSet_Iic (a := S))
    rw [measureReal_def (s := (Iic S)ᶜ), discPi_compl h0 h1] at this
    simp at this; linarith
  rw [discKpow_real_Iic_eq_zero h0 h1 n (by omega), hπ] at h
  norm_num at h; linarith

end StokeyLucasPrescott.ConvergenceApplications
