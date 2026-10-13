/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.ExtendedReals

/-!
# The Principle of Optimality

SLP §4.1, pp. 67–77. The sequence problem

  (SP) `v*(x₀) = sup Σ_{t ≥ 0} βᵗ F(x_t, x_{t+1})` over plans with `x_{t+1} ∈ Γ(x_t)`,

and the functional equation

  (FE) `v(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]`,

with values in the extended reals `R̄ = EReal`.

* `Feasible` (`Π(x₀)`), `partialSum` (`uₙ`), `total` (`u`), `vstar` (`v*`), `SatisfiesFE`,
  `Assumption41`, `Assumption42`.
* `lemma_4_1`: `u(x) = F(x₀, x₁) + βu(x')`.
* `theorem_4_2`: `v*` satisfies (FE).
* `theorem_4_3`: a solution of (FE) with `βⁿv(xₙ) → 0` along every feasible plan is `v*`.
  Its two halves are `total_le_of_FE` and `ex_4_3a` (`v ≤ v*` when `limsup βⁿv(xₙ) ≤ 0`);
  `ex_4_3b` is Exercise 4.3b.
* `theorem_4_4`: an optimal plan satisfies `v*(x*_t) = F(x*_t, x*_{t+1}) + βv*(x*_{t+1})`.
  This needs `β > 0`; the book allows `β ≥ 0` (`theorem_4_4_beta_zero`).
* `theorem_4_5`: a feasible plan satisfying (9) with `limsup βᵗv*(x*_t) ≤ 0` is optimal.
* `Gstar`, `optimal_generated_by_Gstar`, `generated_by_Gstar_optimal`: the optimal policy
  correspondence.
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

variable {X : Type*}

/-- `Π(x₀)`: the plans feasible from `x₀`. -/
def Feasible (Γ : X → Set X) (x₀ : X) : Set (ℕ → X) :=
  {x | x 0 = x₀ ∧ ∀ t, x (t + 1) ∈ Γ (x t)}

/-- `uₙ(x) = Σ_{t=0}^n βᵗ F(x_t, x_{t+1})`. -/
def partialSum (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (n + 1), β ^ t * F (x t) (x (t + 1))

/-- **Assumption 4.1.** `Γ(x)` is nonempty for every `x`. -/
def Assumption41 (Γ : X → Set X) : Prop := ∀ x, (Γ x).Nonempty

/-- **Assumption 4.2.** Along every feasible plan the partial sums converge in `R̄`. -/
def Assumption42 (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) : Prop :=
  ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∃ L : EReal,
    Tendsto (fun n => (partialSum F β x n : EReal)) atTop (𝓝 L)

/-- `u(x) = lim uₙ(x)`. -/
noncomputable def total (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) : EReal :=
  limUnder atTop fun n => (partialSum F β x n : EReal)

/-- The supremum function `v*(x₀) = sup_{x ∈ Π(x₀)} u(x)`. -/
noncomputable def vstar (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (x₀ : X) : EReal :=
  ⨆ x ∈ Feasible Γ x₀, total F β x

/-- `v` satisfies the functional equation (FE). By `eq_biSup_iff` this is the book's
definition through (4)–(7), p. 71. -/
def SatisfiesFE (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (v : X → EReal) : Prop :=
  ∀ x, v x = ⨆ y ∈ Γ x, ((F x y : EReal) + (β : EReal) * v y)

variable {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}

theorem tendsto_total (h42 : Assumption42 Γ F β) {x₀ : X} {x : ℕ → X} (hx : x ∈ Feasible Γ x₀) :
    Tendsto (fun n => (partialSum F β x n : EReal)) atTop (𝓝 (total F β x)) :=
  tendsto_nhds_limUnder (h42 x₀ x hx)

/-- The plan `x' = (x₁, x₂, …)`. -/
def tail (k : ℕ) (x : ℕ → X) : ℕ → X := fun t => x (t + k)

theorem tail_mem {x₀ : X} {x : ℕ → X} (hx : x ∈ Feasible Γ x₀) (k : ℕ) :
    tail k x ∈ Feasible Γ (x k) :=
  ⟨by simp [tail], fun t => by
    simp only [tail, show t + 1 + k = (t + k) + 1 by ring]
    exact hx.2 _⟩

theorem tail_tail (x : ℕ → X) (k : ℕ) : tail 1 (tail k x) = tail (k + 1) x := by
  funext t; simp only [tail]; congr 1; ring

/-- The plan `(x₀, x'₀, x'₁, …)`. -/
def consPlan (x₀ : X) (x' : ℕ → X) : ℕ → X
  | 0 => x₀
  | t + 1 => x' t

theorem consPlan_mem {x₀ y : X} (hy : y ∈ Γ x₀) {x' : ℕ → X} (hx' : x' ∈ Feasible Γ y) :
    consPlan x₀ x' ∈ Feasible Γ x₀ := by
  refine ⟨rfl, fun t => ?_⟩
  cases t with
  | zero => simpa [consPlan, hx'.1] using hy
  | succ t => exact hx'.2 t

theorem tail_consPlan (x₀ : X) (x' : ℕ → X) : tail 1 (consPlan x₀ x') = x' := rfl

/-- Under Assumption 4.1 every `Π(x₀)` is nonempty. -/
theorem feasible_nonempty (h41 : Assumption41 Γ) (x₀ : X) : (Feasible Γ x₀).Nonempty := by
  refine ⟨fun n => Nat.rec x₀ (fun _ z => (h41 z).some) n, rfl, fun t => ?_⟩
  exact (h41 _).some_mem

theorem partialSum_succ (x : ℕ → X) (n : ℕ) :
    partialSum F β x (n + 1) = F (x 0) (x 1) + β * partialSum F β (tail 1 x) n := by
  simp only [partialSum, tail]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem partialSum_succ' (x : ℕ → X) (n : ℕ) :
    partialSum F β x (n + 1) = partialSum F β x n + β ^ (n + 1) * F (x (n + 1)) (x (n + 2)) := by
  simp only [partialSum]
  rw [Finset.sum_range_succ]

/-- **Lemma 4.1.** `u(x) = F(x₀, x₁) + βu(x')` for every feasible plan, `β ≥ 0`. -/
theorem lemma_4_1 (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {x₀ : X} {x : ℕ → X}
    (hx : x ∈ Feasible Γ x₀) :
    total F β x = (F (x 0) (x 1) : EReal) + (β : EReal) * total F β (tail 1 x) := by
  have h1 := (tendsto_total h42 hx).comp (tendsto_add_atTop_nat 1)
  have h2 := ((continuous_add_mul (F (x 0) (x 1)) β hβ).tendsto _).comp
    (tendsto_total h42 (tail_mem hx 1))
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, partialSum_succ, EReal.coe_add, EReal.coe_mul]

/-- **Theorem 4.2.** Under Assumptions 4.1–4.2, `v*` satisfies (FE). -/
theorem theorem_4_2 (hβ : 0 ≤ β) (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β) :
    SatisfiesFE Γ F β (vstar Γ F β) := by
  intro x₀
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    rw [lemma_4_1 hβ h42 hx]
    have hx1 : x 1 ∈ Γ x₀ := hx.1 ▸ hx.2 0
    calc (F (x 0) (x 1) : EReal) + (β : EReal) * total F β (tail 1 x)
        ≤ (F x₀ (x 1) : EReal) + (β : EReal) * vstar Γ F β (x 1) := by
          rw [hx.1]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (le_biSup (total F β) (tail_mem hx 1)) (EReal.coe_nonneg.2 hβ))
      _ ≤ _ := le_biSup (fun y => (F x₀ y : EReal) + (β : EReal) * vstar Γ F β y) hx1
  · refine iSup₂_le fun y hy => ?_
    rw [vstar, add_mul_biSup _ β hβ (feasible_nonempty h41 y)]
    refine iSup₂_le fun x' hx' => ?_
    have hc := consPlan_mem hy hx'
    have := lemma_4_1 hβ h42 hc
    rw [tail_consPlan] at this
    change total F β (consPlan x₀ x') = (F x₀ (x' 0) : EReal) + _ at this
    rw [hx'.1] at this
    rw [← this]
    exact le_biSup (total F β) hc

/-- Along a feasible plan, `uₙ(x) + βⁿ⁺¹v(xₙ₊₁) ≤ v(x₀)` when `v(x) ≥ F(x, y) + βv(y)` for all
`y ∈ Γ(x)`; in the limit, `u(x) ≤ v(x₀)` if `liminf βⁿv(xₙ) ≥ 0`. -/
theorem total_le_of_FE (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {v : X → EReal}
    (hv : ∀ x, ∀ y ∈ Γ x, (F x y : EReal) + (β : EReal) * v y ≤ v x) {x₀ : X} {x : ℕ → X}
    (hx : x ∈ Feasible Γ x₀)
    (hlim : 0 ≤ liminf (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop) :
    total F β x ≤ v x₀ := by
  have key : ∀ n, (partialSum F β x n : EReal) + ((β ^ (n + 1) : ℝ) : EReal) * v (x (n + 1)) ≤
      v x₀ := by
    intro n
    induction n with
    | zero =>
      simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        pow_one]
      exact hx.1 ▸ hv _ _ (hx.2 0)
    | succ n ih =>
      refine le_trans ?_ ih
      rw [partialSum_succ', EReal.coe_add, add_assoc]
      refine add_le_add le_rfl ?_
      have hpow : (0 : ℝ) ≤ β ^ (n + 1) := pow_nonneg hβ _
      calc ((β ^ (n + 1) * F (x (n + 1)) (x (n + 2)) : ℝ) : EReal) +
            ((β ^ (n + 1 + 1) : ℝ) : EReal) * v (x (n + 1 + 1))
          = ((β ^ (n + 1) : ℝ) : EReal) *
              ((F (x (n + 1)) (x (n + 1 + 1)) : EReal) + (β : EReal) * v (x (n + 1 + 1))) := by
            rw [coe_mul_add _ _ hpow, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, ← pow_succ]
        _ ≤ ((β ^ (n + 1) : ℝ) : EReal) * v (x (n + 1)) :=
            mul_le_mul_of_nonneg_left (hv _ _ (hx.2 _)) (EReal.coe_nonneg.2 hpow)
  refine le_of_add_le_liminf key (tendsto_total h42 hx) ?_
  rwa [liminf_nat_add (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) 1]

/-- From `a < c + βw` with `β > 0` and real `a, c`: `(a − c)/β < w`. -/
theorem div_lt_of_lt_add_mul {a c β : ℝ} (hβ : 0 < β) {w : EReal}
    (h : (a : EReal) < (c : EReal) + (β : EReal) * w) : (((a - c) / β : ℝ) : EReal) < w := by
  by_contra hle
  push Not at hle
  have := add_le_add (le_refl (c : EReal))
    (mul_le_mul_of_nonneg_left hle (EReal.coe_nonneg.2 hβ.le))
  rw [← EReal.coe_mul, ← EReal.coe_add, mul_div_cancel₀ _ hβ.ne', add_sub_cancel] at this
  exact absurd (h.trans_le this) (lt_irrefl _)

/-- **Exercise 4.3a.** If `v` satisfies (FE), `β > 0` and `limsup βⁿv(xₙ) ≤ 0` along every
feasible plan, then `v ≤ v*`. For a real `a < v(x₀)`, choose `x_{t+1} ∈ Γ(x_t)` with
`a_t < F(x_t, x_{t+1}) + βv(x_{t+1})` and set `a_{t+1} = (a_t − F(x_t, x_{t+1}))/β`; then
`a = uₙ(x) + βⁿ⁺¹a_{n+1} < uₙ(x) + βⁿ⁺¹v(x_{n+1})`, and `a ≤ u(x)` in the limit. -/
theorem ex_4_3a (hβ : 0 < β) (h42 : Assumption42 Γ F β) {v : X → EReal}
    (hv : SatisfiesFE Γ F β v)
    (hlim : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      limsup (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop ≤ 0) (x₀ : X) :
    v x₀ ≤ vstar Γ F β x₀ := by
  -- states paired with targets below their value
  set P := {p : X × ℝ // (p.2 : EReal) < v p.1}
  have hstep : ∀ p : P, ∃ y ∈ Γ p.1.1,
      (p.1.2 : EReal) < (F p.1.1 y : EReal) + (β : EReal) * v y := fun p =>
    lt_biSup_iff.1 (hv p.1.1 ▸ p.2)
  choose next hnext hlt using hstep
  let step : P → P := fun p =>
    ⟨(next p, (p.1.2 - F p.1.1 (next p)) / β), div_lt_of_lt_add_mul hβ (hlt p)⟩
  refine le_of_forall_coe_lt_le fun a ha => ?_
  let s : ℕ → P := fun n => step^[n] ⟨(x₀, a), ha⟩
  have hs : ∀ n, s (n + 1) = step (s n) := fun n => Function.iterate_succ_apply' _ _ _
  set x : ℕ → X := fun n => (s n).1.1
  set b : ℕ → ℝ := fun n => (s n).1.2
  have hx : x ∈ Feasible Γ x₀ := ⟨rfl, fun t => by
    change (s (t + 1)).1.1 ∈ Γ (s t).1.1
    rw [hs]; exact hnext _⟩
  have hb : ∀ t, b t = F (x t) (x (t + 1)) + β * b (t + 1) := fun t => by
    change (s t).1.2 = F (s t).1.1 (s (t + 1)).1.1 + β * (s (t + 1)).1.2
    rw [hs]
    change (s t).1.2 = F (s t).1.1 (next (s t)) + β * ((((s t).1.2 - F (s t).1.1 (next (s t))) / β))
    field_simp
    ring
  -- `a = uₙ(x) + βⁿ⁺¹ b_{n+1}`
  have hsum : ∀ n, a = partialSum F β x n + β ^ (n + 1) * b (n + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        pow_one]
      exact hb 0
    | succ n ih =>
      rw [partialSum_succ', ih, hb (n + 1)]
      ring
  have key : ∀ n, (a : EReal) ≤ (partialSum F β x n : EReal) +
      ((β ^ (n + 1) : ℝ) : EReal) * v (x (n + 1)) := fun n => by
    rw [hsum n, EReal.coe_add, EReal.coe_mul]
    refine add_le_add le_rfl ((mulIso _ (pow_pos hβ _)).monotone (s (n + 1)).2.le)
  have hlim' := hlim x₀ x hx
  rw [← limsup_nat_add (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) 1] at hlim'
  exact (le_of_le_add_limsup key (tendsto_total h42 hx) hlim').trans (le_biSup _ hx)

/-- **Theorem 4.3.** Under Assumptions 4.1–4.2, a solution `v` of (FE) with `βⁿv(xₙ) → 0` along
every feasible plan is the supremum function. -/
theorem theorem_4_3 (hβ : 0 ≤ β) (h41 : Assumption41 Γ) (h42 : Assumption42 Γ F β)
    {v : X → EReal} (hv : SatisfiesFE Γ F β v)
    (h8 : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      Tendsto (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop (𝓝 0)) :
    v = vstar Γ F β := by
  funext x₀
  rcases hβ.eq_or_lt with h0 | hpos
  · -- with `β = 0` both sides equal `sup_{y ∈ Γ(x₀)} F(x₀, y)`
    subst h0
    rw [hv x₀, theorem_4_2 le_rfl h41 h42 x₀]
    simp only [EReal.coe_zero, zero_mul]
  · refine le_antisymm (ex_4_3a hpos h42 hv (fun x₀ x hx => (h8 x₀ x hx).limsup_eq.le) x₀) ?_
    refine iSup₂_le fun x hx => total_le_of_FE hpos.le h42 (fun x y hy => ?_) hx
      (h8 x₀ x hx).liminf_eq.ge
    rw [hv x]
    exact le_biSup (fun y => (F x y : EReal) + (β : EReal) * v y) hy

/-- **Exercise 4.3b.** If in addition to the hypotheses of Exercise 4.3a every feasible plan is
weakly dominated by one along which `βⁿv(xₙ) → 0`, then `v = v*`. -/
theorem ex_4_3b (hβ : 0 < β) (h42 : Assumption42 Γ F β) {v : X → EReal}
    (hv : SatisfiesFE Γ F β v)
    (hlim : ∀ x₀, ∀ x ∈ Feasible Γ x₀,
      limsup (fun n => ((β ^ n : ℝ) : EReal) * v (x n)) atTop ≤ 0)
    (hdom : ∀ x₀, ∀ x ∈ Feasible Γ x₀, ∃ x' ∈ Feasible Γ x₀,
      Tendsto (fun n => ((β ^ n : ℝ) : EReal) * v (x' n)) atTop (𝓝 0) ∧
        total F β x ≤ total F β x') :
    v = vstar Γ F β := by
  funext x₀
  refine le_antisymm (ex_4_3a hβ h42 hv hlim x₀) (iSup₂_le fun x hx => ?_)
  obtain ⟨x', hx', hlim', hle⟩ := hdom x₀ x hx
  refine hle.trans (total_le_of_FE hβ.le h42 (fun x y hy => ?_) hx' hlim'.liminf_eq.ge)
  rw [hv x]
  exact le_biSup (fun y => (F x y : EReal) + (β : EReal) * v y) hy

/-- **Theorem 4.4.** If `x*` is optimal from `x₀` and `β > 0`, then
`v*(x*_t) = F(x*_t, x*_{t+1}) + βv*(x*_{t+1})` for all `t`. -/
theorem theorem_4_4 (hβ : 0 < β) (h42 : Assumption42 Γ F β) {x₀ : X} {xs : ℕ → X}
    (hxs : xs ∈ Feasible Γ x₀) (hopt : total F β xs = vstar Γ F β x₀) (t : ℕ) :
    vstar Γ F β (xs t) =
      (F (xs t) (xs (t + 1)) : EReal) + (β : EReal) * vstar Γ F β (xs (t + 1)) := by
  -- every tail of an optimal plan is optimal
  have htail : ∀ k, total F β (tail k xs) = vstar Γ F β (xs k) := by
    intro k
    induction k with
    | zero =>
      have : tail 0 xs = xs := rfl
      rw [this, hopt, hxs.1]
    | succ k ih =>
      have hk := tail_mem hxs k
      refine le_antisymm ?_ (iSup₂_le fun x' hx' => ?_)
      · have := le_biSup (total F β) (tail_mem hk 1)
        have e : tail k xs 1 = xs (k + 1) := by simp [tail, add_comm]
        rw [tail_tail, e] at this
        exact this
      · have hy : xs (k + 1) ∈ Γ (xs k) := hxs.2 k
        have hc := consPlan_mem hy hx'
        have h1 : total F β (consPlan (xs k) x') ≤ total F β (tail k xs) :=
          ih ▸ le_biSup (total F β) hc
        rw [lemma_4_1 hβ.le h42 hc, lemma_4_1 hβ.le h42 hk, tail_consPlan, tail_tail] at h1
        change (F (xs k) (x' 0) : EReal) + _ ≤ (F (xs (0 + k)) (xs (1 + k)) : EReal) + _ at h1
        rw [hx'.1, zero_add, add_comm 1 k] at h1
        have h2 := ((addIso (F (xs k) (xs (k + 1)))).le_iff_le).1 h1
        exact ((mulIso β hβ).le_iff_le).1 h2
  have h1 := htail t
  rw [lemma_4_1 hβ.le h42 (tail_mem hxs t), tail_tail, htail (t + 1)] at h1
  have e0 : tail t xs 0 = xs t := by simp [tail]
  have e1 : tail t xs 1 = xs (t + 1) := by simp [tail, add_comm]
  rw [e0, e1] at h1
  exact h1.symm

/-- **Theorem 4.4 needs `β > 0`.** With `β = 0`, two states, `Γ(x) = {false, true}` and
`F(x, y) = 1` if `y = true`, `0` otherwise, the plan `(false, true, false, false, …)` is optimal
from `false`, but `v*(true) = 1 ≠ 0 = F(true, false) + 0 · v*(false)`, so (9) fails at `t = 1`. -/
theorem theorem_4_4_beta_zero :
    let F : Bool → Bool → ℝ := fun _ y => if y then 1 else 0
    let xs : ℕ → Bool := fun t => decide (t = 1)
    Assumption42 (fun _ => Set.univ) F 0 ∧ xs ∈ Feasible (fun _ => Set.univ) false ∧
      total F 0 xs = vstar (fun _ => Set.univ) F 0 false ∧
      vstar (fun _ => Set.univ) F 0 (xs 1) ≠
        (F (xs 1) (xs 2) : EReal) + ((0 : ℝ) : EReal) * vstar (fun _ => Set.univ) F 0 (xs 2) := by
  intro F xs
  -- with `β = 0` the partial sums are `F(x₀, x₁)`
  have hps : ∀ (x : ℕ → Bool) (n : ℕ), partialSum F 0 x n = F (x 0) (x 1) := by
    intro x n
    induction n with
    | zero => simp [partialSum]
    | succ n ih => rw [partialSum_succ', ih]; simp
  have h42 : Assumption42 (fun _ => Set.univ) F 0 := fun _ x _ =>
    ⟨_, by simp only [hps]; exact tendsto_const_nhds⟩
  have htot : ∀ x : ℕ → Bool, total F 0 x = (F (x 0) (x 1) : EReal) := fun x =>
    tendsto_nhds_unique (tendsto_nhds_limUnder (h42 (x 0) x ⟨rfl, fun _ => trivial⟩))
      (by simp only [hps]; exact tendsto_const_nhds)
  have hF1 : ∀ a b, F a b ≤ 1 := fun a b => by simp only [F]; split_ifs <;> norm_num
  -- `v*(b) = 1` for every `b`
  have hv : ∀ b, vstar (fun _ => Set.univ) F 0 b = 1 := fun b => by
    refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
    · rw [htot]; exact_mod_cast hF1 (x 0) (x 1)
    · have hx : (fun t : ℕ => if t = 0 then b else true) ∈ Feasible (fun _ => Set.univ) b :=
        ⟨by simp, fun _ => trivial⟩
      have := le_biSup (total F 0) hx
      rw [htot] at this
      refine le_trans ?_ this
      simp [F]
  refine ⟨h42, ⟨by simp [xs], fun _ => trivial⟩, ?_, ?_⟩
  · rw [htot, hv]; simp [F, xs]
  · rw [hv]; simp [F, xs]

/-- **Theorem 4.5.** A feasible plan satisfying (9) and (11) `limsup βᵗv*(x*_t) ≤ 0` attains the
supremum. -/
theorem theorem_4_5 (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {x₀ : X} {xs : ℕ → X}
    (hxs : xs ∈ Feasible Γ x₀)
    (h9 : ∀ t, vstar Γ F β (xs t) =
      (F (xs t) (xs (t + 1)) : EReal) + (β : EReal) * vstar Γ F β (xs (t + 1)))
    (h11 : limsup (fun t => ((β ^ t : ℝ) : EReal) * vstar Γ F β (xs t)) atTop ≤ 0) :
    total F β xs = vstar Γ F β x₀ := by
  refine le_antisymm (le_biSup (total F β) hxs) ?_
  have key : ∀ n, vstar Γ F β x₀ = (partialSum F β xs n : EReal) +
      ((β ^ (n + 1) : ℝ) : EReal) * vstar Γ F β (xs (n + 1)) := by
    intro n
    induction n with
    | zero =>
      simp only [partialSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        pow_one]
      rw [← hxs.1]
      exact h9 0
    | succ n ih =>
      rw [ih, h9 (n + 1), coe_mul_add _ _ (pow_nonneg hβ _), partialSum_succ', EReal.coe_add,
        add_assoc, ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul, ← pow_succ]
      simp only [add_assoc]
  rw [← limsup_nat_add (fun t => ((β ^ t : ℝ) : EReal) * vstar Γ F β (xs t)) 1] at h11
  exact le_of_le_add_limsup (fun n => (key n).le) (tendsto_total h42 hxs) h11

/-- The optimal policy correspondence `G*(x) = {y ∈ Γ(x) : v*(x) = F(x, y) + βv*(y)}`. -/
def Gstar (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (x : X) : Set X :=
  {y | y ∈ Γ x ∧ vstar Γ F β x = (F x y : EReal) + (β : EReal) * vstar Γ F β y}

/-- Every optimal plan is generated by `G*` (from Theorem 4.4). -/
theorem optimal_generated_by_Gstar (hβ : 0 < β) (h42 : Assumption42 Γ F β) {x₀ : X}
    {xs : ℕ → X} (hxs : xs ∈ Feasible Γ x₀) (hopt : total F β xs = vstar Γ F β x₀) (t : ℕ) :
    xs (t + 1) ∈ Gstar Γ F β (xs t) :=
  ⟨hxs.2 t, theorem_4_4 hβ h42 hxs hopt t⟩

/-- A plan generated by `G*` and satisfying (11) is optimal (from Theorem 4.5). -/
theorem generated_by_Gstar_optimal (hβ : 0 ≤ β) (h42 : Assumption42 Γ F β) {x₀ : X}
    {xs : ℕ → X} (h0 : xs 0 = x₀) (hgen : ∀ t, xs (t + 1) ∈ Gstar Γ F β (xs t))
    (h11 : limsup (fun t => ((β ^ t : ℝ) : EReal) * vstar Γ F β (xs t)) atTop ≤ 0) :
    total F β xs = vstar Γ F β x₀ :=
  theorem_4_5 hβ h42 ⟨h0, fun t => (hgen t).1⟩ (fun t => (hgen t).2) h11

end StokeyLucasPrescott.DeterministicDP
