/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CDBudget
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Euler inequality (8.7) and the transversality condition (8.8)

Miao, §8.3, pp. 239–240, for deterministic income `y_t` (the setting of §8.3.1).

In the variables of p. 239 a plan from cash on hand `x₀` is a consumption sequence `c` and a
cash-on-hand path `x` with `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb` (`cd_IsPath`); it is feasible
(`cd_Feasible`) if `0 < c_t ≤ x_t`, i.e. `â_{t+1} = x_t − c_t ≥ 0`. Utility may be unbounded,
so optimality (`cd_Optimal`) is stated by partial sums: for every feasible plan `c′` and `ε > 0`,
eventually `∑_{t≤T} βᵗu(c′_t) ≤ ∑_{t≤T} βᵗu(c_t) + ε` (the plan is not overtaken). For plans
with summable utility this gives `∑ βᵗu(c′_t) ≤ ∑ βᵗu(c_t)` (`cd_tsum_le_of_optimal`).

* `cd_Euler` is (8.7) and `cd_TVC` is (8.8); `cd_TVCs` is the transversality condition on saving,
  `βᵗu′(c_t)â_{t+1} → 0`, which (8.8) implies when `y_t ≥ rb` (`cd_TVCs_of_TVC`).
* `cd_sum_le`, `cd_partial_le`: the concavity bound on partial sums; `cd_sufficient`,
  `eq_8_7_8_8_sufficient`: "These conditions are also sufficient for optimality" (p. 240). The
  proof is the deterministic Euler–transversality sufficiency argument of Theorem 7.5.2, done
  directly in these variables, with the borrowing constraint handled by the Euler inequality.
* `eq_8_7`: "By the Maximum Principle, we can derive the Euler inequality" (p. 239): every
  optimal plan satisfies (8.7) (one-period perturbations of saving).
* `cd_budget_iter`: iterating the budget from date `t`.
-/

namespace Miao.Applications

open Filter Topology

/-- Miao, p. 239: a feasible plan from cash on hand `x₀`: `0 < c_t ≤ x_t` (saving
`â_{t+1} = x_t − c_t ≥ 0`). Consumption is strictly positive (see the corrections file). -/
def cd_Feasible (R b : ℝ) (y : ℕ → ℝ) (x₀ : ℝ) (c x : ℕ → ℝ) : Prop :=
  cd_IsPath R b y x₀ c x ∧ ∀ t, 0 < c t ∧ c t ≤ x t

/-- The partial sum `∑_{t≤T} βᵗu(c_t)` of the objective of §8.3. -/
noncomputable def cd_partial (U : cd_Utility) (β : ℝ) (c : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), β ^ t * U.u (c t)

/-- Miao, p. 237: an optimal plan, by partial sums (utility may be unbounded): no feasible plan
overtakes it by more than any `ε > 0`. -/
def cd_Optimal (U : cd_Utility) (β R b : ℝ) (y : ℕ → ℝ) (x₀ : ℝ) (c x : ℕ → ℝ) : Prop :=
  cd_Feasible R b y x₀ c x ∧ ∀ c' x', cd_Feasible R b y x₀ c' x' →
    ∀ ε > 0, ∀ᶠ T in atTop, cd_partial U β c' T ≤ cd_partial U β c T + ε

/-- Miao, (8.7), p. 239: the Euler inequality `u′(c_t) ≥ βRu′(c_{t+1})`, with equality if
`â_{t+1} = x_t − c_t > 0`. -/
def cd_Euler (U : cd_Utility) (β R : ℝ) (c x : ℕ → ℝ) : Prop :=
  ∀ t, β * R * U.du (c (t + 1)) ≤ U.du (c t) ∧
    (c t < x t → U.du (c t) = β * R * U.du (c (t + 1)))

/-- Miao, (8.8), p. 239: the transversality condition `lim βᵗu′(c_t)x_t = 0`. -/
def cd_TVC (U : cd_Utility) (β : ℝ) (c x : ℕ → ℝ) : Prop :=
  Tendsto (fun t => β ^ t * U.du (c t) * x t) atTop (𝓝 0)

/-- The transversality condition on saving: `lim βᵗu′(c_t)â_{t+1} = 0`, `â_{t+1} = x_t − c_t`. -/
def cd_TVCs (U : cd_Utility) (β : ℝ) (c x : ℕ → ℝ) : Prop :=
  Tendsto (fun t => β ^ t * U.du (c t) * (x t - c t)) atTop (𝓝 0)

/-- The concavity bound behind the sufficiency of (8.7)–(8.8): for feasible plans `c`, `c′`
from the same `x₀`, with `c` satisfying (8.7),
`∑_{t≤T} βᵗu′(c_t)(c′_t − c_t) ≤ βᵀu′(c_T)(â_{T+1} − â′_{T+1})`. -/
theorem cd_sum_le (U : cd_Utility) {β R b : ℝ} (hβ : 0 ≤ β) {y : ℕ → ℝ} {x₀ : ℝ}
    {c x c' x' : ℕ → ℝ} (h : cd_Feasible R b y x₀ c x) (h' : cd_Feasible R b y x₀ c' x')
    (hE : cd_Euler U β R c x) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * U.du (c t) * (c' t - c t) ≤
      β ^ T * U.du (c T) * ((x T - c T) - (x' T - c' T)) := by
  obtain ⟨⟨hx0, hp⟩, hf⟩ := h
  obtain ⟨⟨hx0', hp'⟩, hf'⟩ := h'
  induction T with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, hx0, hx0']
    exact le_of_eq (by ring)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have e : c' (n + 1) - c (n + 1) =
        R * ((x' n - c' n) - (x n - c n)) + ((x (n + 1) - c (n + 1)) - (x' (n + 1) - c' (n + 1)))
        := by rw [hp n, hp' n]; ring
    rw [e]
    have hkey : β ^ n * U.du (c n) * ((x n - c n) - (x' n - c' n)) +
        β ^ (n + 1) * U.du (c (n + 1)) * (R * ((x' n - c' n) - (x n - c n))) ≤ 0 := by
      have e2 : β ^ n * U.du (c n) * ((x n - c n) - (x' n - c' n)) +
          β ^ (n + 1) * U.du (c (n + 1)) * (R * ((x' n - c' n) - (x n - c n))) =
          β ^ n * ((x' n - c' n) - (x n - c n)) * (β * R * U.du (c (n + 1)) - U.du (c n)) := by
        ring
      rw [e2]
      have hβn : 0 ≤ β ^ n := pow_nonneg hβ n
      rcases (sub_nonneg.2 (hf n).2).lt_or_eq with hs | hs
      · rw [(hE n).2 (sub_pos.1 hs), sub_self, mul_zero]
      · have h1 : 0 ≤ (x' n - c' n) - (x n - c n) := by
          rw [← hs, sub_zero]; exact sub_nonneg.2 (hf' n).2
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβn h1) (sub_nonpos.2 (hE n).1)
    nlinarith [ih, hkey]

/-- Miao, p. 240: with (8.7), `∑_{t≤T} βᵗu(c′_t) ≤ ∑_{t≤T} βᵗu(c_t) + βᵀu′(c_T)â_{T+1}` for
every feasible `c′`. -/
theorem cd_partial_le (U : cd_Utility) {β R b : ℝ} (hβ : 0 ≤ β) {y : ℕ → ℝ} {x₀ : ℝ}
    {c x c' x' : ℕ → ℝ} (h : cd_Feasible R b y x₀ c x) (h' : cd_Feasible R b y x₀ c' x')
    (hE : cd_Euler U β R c x) (T : ℕ) :
    cd_partial U β c' T ≤ cd_partial U β c T + β ^ T * U.du (c T) * (x T - c T) := by
  have h1 := cd_sum_le U hβ h h' hE T
  have h2 : cd_partial U β c' T ≤ cd_partial U β c T +
      ∑ t ∈ Finset.range (T + 1), β ^ t * U.du (c t) * (c' t - c t) := by
    unfold cd_partial
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have := U.cd_tangent (h.2 t).1 (h'.2 t).1
    have hβt : 0 ≤ β ^ t := pow_nonneg hβ t
    nlinarith
  have h3 : 0 ≤ β ^ T * U.du (c T) * (x' T - c' T) :=
    mul_nonneg (mul_nonneg (pow_nonneg hβ T) (U.du_pos _ (h.2 T).1).le) (sub_nonneg.2 (h'.2 T).2)
  nlinarith

/-- Miao, p. 240: the Euler inequality (8.7) and the transversality condition on saving are
sufficient for optimality. -/
theorem cd_sufficient (U : cd_Utility) {β R b : ℝ} (hβ : 0 ≤ β) {y : ℕ → ℝ} {x₀ : ℝ}
    {c x : ℕ → ℝ} (h : cd_Feasible R b y x₀ c x) (hE : cd_Euler U β R c x)
    (hT : cd_TVCs U β c x) : cd_Optimal U β R b y x₀ c x := by
  refine ⟨h, fun c' x' h' ε hε => ?_⟩
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with T hTε
  have := cd_partial_le U hβ h h' hE T
  linarith

/-- Miao, p. 239: (8.8) implies the transversality condition on saving when `y_t ≥ rb`, given
(8.7): if `â_{T+1} > 0` then `βᵀu′(c_T)Râ_{T+1} = β^{T+1}u′(c_{T+1})Râ_{T+1} ≤
Rβ^{T+1}u′(c_{T+1})x_{T+1}`. -/
theorem cd_TVCs_of_TVC (U : cd_Utility) {β R b : ℝ} (hβ : 0 < β)
    {y : ℕ → ℝ} (hy : ∀ t, (R - 1) * b ≤ y t) {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_Feasible R b y x₀ c x) (hE : cd_Euler U β R c x) (hT : cd_TVC U β c x) :
    cd_TVCs U β c x := by
  have hup : ∀ t, β ^ t * U.du (c t) * (x t - c t) ≤
      β ^ (t + 1) * U.du (c (t + 1)) * x (t + 1) := fun t => by
    have hpath := h.1.2 t
    have hs := sub_nonneg.2 (h.2 t).2
    rcases hs.lt_or_eq with hs' | hs'
    · rw [(hE t).2 (sub_pos.1 hs'), hpath]
      have h1 : 0 ≤ β ^ (t + 1) * U.du (c (t + 1)) :=
        mul_nonneg (pow_nonneg hβ.le _) (U.du_pos _ (h.2 _).1).le
      have h2 := hy (t + 1)
      have e : β ^ t * (β * R * U.du (c (t + 1))) * (x t - c t) =
          β ^ (t + 1) * U.du (c (t + 1)) * (R * (x t - c t)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) h1
    · rw [← hs', mul_zero]
      exact le_of_eq_of_le rfl (by
        have := (h.2 (t + 1)).1
        have h3 : 0 ≤ x (t + 1) := le_trans this.le (h.2 (t + 1)).2
        exact mul_nonneg (mul_nonneg (pow_nonneg hβ.le _) (U.du_pos _ this).le) h3)
  have hlow : ∀ t, 0 ≤ β ^ t * U.du (c t) * (x t - c t) := fun t =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ.le _) (U.du_pos _ (h.2 t).1).le)
      (sub_nonneg.2 (h.2 t).2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hT.comp (tendsto_add_atTop_nat 1)) hlow hup

/-- Miao, (8.7)–(8.8), p. 240: "These conditions are also sufficient for optimality." With
`y_t ≥ rb`, a feasible plan satisfying the Euler inequality (8.7) and the transversality
condition (8.8) is optimal. -/
theorem eq_8_7_8_8_sufficient (U : cd_Utility) {β R b : ℝ} (hβ : 0 < β)
    {y : ℕ → ℝ} (hy : ∀ t, (R - 1) * b ≤ y t) {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_Feasible R b y x₀ c x) (hE : cd_Euler U β R c x) (hT : cd_TVC U β c x) :
    cd_Optimal U β R b y x₀ c x :=
  cd_sufficient U hβ.le h hE (cd_TVCs_of_TVC U hβ hy h hE hT)

/-- The partial sums converge to the series when utility is summable. -/
theorem cd_tendsto_partial (U : cd_Utility) {β : ℝ} {c : ℕ → ℝ}
    (hs : Summable fun t => β ^ t * U.u (c t)) :
    Tendsto (cd_partial U β c) atTop (𝓝 (∑' t, β ^ t * U.u (c t))) :=
  hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- For plans with summable utility, an optimal plan has the largest value
`∑ βᵗu(c_t)`. -/
theorem cd_tsum_le_of_optimal (U : cd_Utility) {β R b : ℝ} {y : ℕ → ℝ} {x₀ : ℝ}
    {c x c' x' : ℕ → ℝ} (h : cd_Optimal U β R b y x₀ c x) (h' : cd_Feasible R b y x₀ c' x')
    (hs : Summable fun t => β ^ t * U.u (c t)) (hs' : Summable fun t => β ^ t * U.u (c' t)) :
    ∑' t, β ^ t * U.u (c' t) ≤ ∑' t, β ^ t * U.u (c t) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact le_of_tendsto_of_tendsto (cd_tendsto_partial U hs')
    ((cd_tendsto_partial U hs).add_const ε) (h.2 c' x' h' ε hε)

/-- Two optimal plans with summable utility have the same value. -/
theorem cd_tsum_eq_of_optimal (U : cd_Utility) {β R b : ℝ} {y : ℕ → ℝ} {x₀ : ℝ}
    {c x c' x' : ℕ → ℝ} (h : cd_Optimal U β R b y x₀ c x) (h' : cd_Optimal U β R b y x₀ c' x')
    (hs : Summable fun t => β ^ t * U.u (c t)) (hs' : Summable fun t => β ^ t * U.u (c' t)) :
    ∑' t, β ^ t * U.u (c' t) = ∑' t, β ^ t * U.u (c t) :=
  le_antisymm (cd_tsum_le_of_optimal U h h'.1 hs hs') (cd_tsum_le_of_optimal U h' h.1 hs' hs)

/-- Miao, p. 239: iterating the budget from date `t`, with `ρ = R⁻¹`:
`∑_{n≤N} ρⁿc_{t+n} + ρᴺâ_{t+N+1} = x_t + ∑_{n<N} ρ^{n+1}(y_{t+n+1} − rb)`. -/
theorem cd_budget_iter {R b : ℝ} (hR : R ≠ 0) {y : ℕ → ℝ} {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_IsPath R b y x₀ c x) (t N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), R⁻¹ ^ n * c (t + n) + R⁻¹ ^ N * (x (t + N) - c (t + N)) =
      x t + ∑ n ∈ Finset.range N, R⁻¹ ^ (n + 1) * (y (t + n + 1) - (R - 1) * b) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (fun n => R⁻¹ ^ n * c (t + n)) (N + 1),
      Finset.sum_range_succ (fun n => R⁻¹ ^ (n + 1) * (y (t + n + 1) - (R - 1) * b)) N]
    have hp := h.2 (t + N)
    have e1 : t + (N + 1) = t + N + 1 := by omega
    rw [e1]
    have e : R⁻¹ ^ (N + 1) * c (t + N + 1) + R⁻¹ ^ (N + 1) * (x (t + N + 1) - c (t + N + 1)) =
        R⁻¹ ^ N * (x (t + N) - c (t + N)) +
          R⁻¹ ^ (N + 1) * (y (t + N + 1) - (R - 1) * b) := by
      rw [hp, pow_succ]
      field_simp
      ring
    linarith

/-- The one-period perturbation of saving used for (8.7): consume `δ` less at `t` and `Rδ` more
at `t + 1`. -/
theorem cd_perturb_feasible {R b : ℝ} {y : ℕ → ℝ} {x₀ : ℝ} {c x : ℕ → ℝ}
    (h : cd_Feasible R b y x₀ c x) (t : ℕ) {δ : ℝ} (h1 : δ < c t) (h2 : -(x t - c t) ≤ δ)
    (h3 : -c (t + 1) < R * δ) :
    cd_Feasible R b y x₀
      (fun j => c j - (if j = t then δ else 0) + (if j = t + 1 then R * δ else 0))
      (fun j => x j + (if j = t + 1 then R * δ else 0)) := by
  obtain ⟨⟨hx0, hp⟩, hf⟩ := h
  refine ⟨⟨?_, fun j => ?_⟩, fun j => ?_⟩
  · simp [hx0]
  · have hpj := hp j
    by_cases hj : j = t
    · subst hj
      simp only [↓reduceIte]
      simp only [hpj]
      ring
    · by_cases hj' : j = t + 1
      · subst hj'
        simp only [show t + 1 + 1 ≠ t + 1 from by omega, ↓reduceIte, hj, add_zero, sub_zero]
        rw [hpj]
        ring
      · simp only [hj, hj', show j + 1 ≠ t + 1 from fun e => hj (by omega), ↓reduceIte,
          add_zero, sub_zero]
        exact hpj
  · have hfj := hf j
    by_cases hj : j = t
    · subst hj
      simp only [show j ≠ j + 1 from by omega, ↓reduceIte, add_zero]
      constructor <;> linarith
    · by_cases hj' : j = t + 1
      · subst hj'
        simp only [hj, ↓reduceIte, sub_zero]
        constructor <;> linarith
      · simp only [hj, hj', ↓reduceIte, sub_zero, add_zero]
        exact hfj

/-- The gain of the perturbation in every partial sum from `T ≥ t + 1` on. -/
theorem cd_perturb_partial (U : cd_Utility) (β R : ℝ) (c : ℕ → ℝ) (t : ℕ) (δ : ℝ) {T : ℕ}
    (hT : t + 1 ≤ T) :
    cd_partial U β (fun j => c j - (if j = t then δ else 0) + (if j = t + 1 then R * δ else 0))
        T =
      cd_partial U β c T + (β ^ t * (U.u (c t - δ) - U.u (c t)) +
        β ^ (t + 1) * (U.u (c (t + 1) + R * δ) - U.u (c (t + 1)))) := by
  unfold cd_partial
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add t (t + 1) (by omega)]
  · simp only [show t ≠ t + 1 from by omega, show t + 1 ≠ t from by omega, ↓reduceIte,
      add_zero, sub_zero]
    ring
  · intro j _ hj
    simp only [hj.1, hj.2, ↓reduceIte, sub_zero, add_zero, sub_self]
  · intro hm
    exact absurd (Finset.mem_range.2 (by omega)) hm
  · intro hm
    exact absurd (Finset.mem_range.2 (by omega)) hm

/-- Miao, (8.7), p. 239: "By the Maximum Principle, we can derive the Euler inequality": every
optimal plan satisfies `u′(c_t) ≥ βRu′(c_{t+1})`, with equality if `â_{t+1} > 0`. The proof
perturbs saving at one date: `g(δ) = βᵗ[u(c_t − δ) − u(c_t)] + β^{t+1}[u(c_{t+1} + Rδ) −
u(c_{t+1})] ≤ 0` for all feasible `δ` (`δ > 0` always; `δ < 0` when `â_{t+1} > 0`), and
`g′(0) = βᵗ(βRu′(c_{t+1}) − u′(c_t))`. -/
theorem eq_8_7 (U : cd_Utility) {β R b : ℝ} (hβ : 0 < β) (hR : 0 < R) {y : ℕ → ℝ} {x₀ : ℝ}
    {c x : ℕ → ℝ} (h : cd_Optimal U β R b y x₀ c x) : cd_Euler U β R c x := by
  intro t
  have hf := h.1.2
  set g : ℝ → ℝ := fun δ => β ^ t * (U.u (c t - δ) - U.u (c t)) +
    β ^ (t + 1) * (U.u (c (t + 1) + R * δ) - U.u (c (t + 1)))
  have hg0 : g 0 = 0 := by simp [g]
  -- `g δ ≤ 0` for feasible `δ`
  have hgle : ∀ δ, δ < c t → -(x t - c t) ≤ δ → -c (t + 1) < R * δ → g δ ≤ 0 := by
    intro δ h1 h2 h3
    have hfe := cd_perturb_feasible h.1 t h1 h2 h3
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨T, hT, hT1⟩ := ((h.2 _ _ hfe ε hε).and (eventually_ge_atTop (t + 1))).exists
    rw [cd_perturb_partial U β R c t δ hT1] at hT
    simp only [g]
    linarith
  -- the derivative of `g` at `0`
  set d := β ^ t * (β * R * U.du (c (t + 1)) - U.du (c t))
  have hgd : HasDerivAt g d 0 := by
    have h1 : HasDerivAt (fun δ => U.u (c t - δ)) (U.du (c t) * (-1)) 0 := by
      have hu : HasDerivAt U.u (U.du (c t)) (c t - 0) := by
        rw [sub_zero]; exact U.hasDerivAt _ (hf t).1
      exact hu.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_sub (c t))
    have h2 : HasDerivAt (fun δ => U.u (c (t + 1) + R * δ)) (U.du (c (t + 1)) * (R * 1)) 0 := by
      have hu : HasDerivAt U.u (U.du (c (t + 1))) (c (t + 1) + R * 0) := by
        rw [mul_zero, add_zero]; exact U.hasDerivAt _ (hf (t + 1)).1
      exact hu.comp (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).const_mul R).const_add (c (t + 1)))
    have := ((h1.sub_const (U.u (c t))).const_mul (β ^ t)).add
      ((h2.sub_const (U.u (c (t + 1)))).const_mul (β ^ (t + 1)))
    convert this using 1
    simp only [d]
    ring
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hgd
  simp only [zero_add, hg0, sub_zero, smul_eq_mul] at hslope
  have hβt : 0 < β ^ t := pow_pos hβ t
  have hd_le : d ≤ 0 := by
    by_contra hd
    push Not at hd
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ⁻¹ * g δ :=
      (hslope.mono_left (nhdsWithin_mono _ fun z hz => ne_of_gt hz)).eventually
        (lt_mem_nhds hd)
    obtain ⟨δ, hδ, hδ'⟩ := (hev.and (Ioo_mem_nhdsGT (hf t).1)).exists
    have hδ0 : 0 < δ := hδ'.1
    have hgδ := hgle δ hδ'.2 (by linarith [sub_nonneg.2 (hf t).2])
      (by nlinarith [(hf (t + 1)).1])
    have : 0 < g δ := by
      have := mul_pos hδ0 hδ
      rwa [← mul_assoc, mul_inv_cancel₀ hδ0.ne', one_mul] at this
    linarith
  refine ⟨?_, fun hs => ?_⟩
  · have : β * R * U.du (c (t + 1)) - U.du (c t) ≤ 0 := by
      by_contra hc
      push Not at hc
      exact absurd hd_le (not_le.2 (mul_pos hβt hc))
    linarith
  · by_contra hne
    have hd : d < 0 := by
      rcases hd_le.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        apply hne
        have := (mul_eq_zero.1 heq).resolve_left hβt.ne'
        linarith
    have hev : ∀ᶠ δ in 𝓝[<] (0 : ℝ), δ⁻¹ * g δ < 0 :=
      (hslope.mono_left (nhdsWithin_mono _ fun z hz => ne_of_lt hz)).eventually
        (gt_mem_nhds hd)
    set m := min (x t - c t) (c (t + 1) / R)
    have hm : 0 < m := lt_min (sub_pos.2 hs) (div_pos (hf (t + 1)).1 hR)
    obtain ⟨δ, hδ, hδ'⟩ := (hev.and (Ioo_mem_nhdsLT (show -m < 0 by linarith))).exists
    have hδ0 : δ < 0 := hδ'.2
    have hm1 : m ≤ x t - c t := min_le_left _ _
    have hm2 : m ≤ c (t + 1) / R := min_le_right _ _
    have h3 : -c (t + 1) < R * δ := by
      have : R * m ≤ c (t + 1) := by rw [le_div_iff₀ hR] at hm2; linarith
      nlinarith [hδ'.1]
    have hgδ := hgle δ (by linarith [(hf t).1]) (by linarith [hδ'.1]) h3
    have : 0 < g δ := by
      have := mul_pos_of_neg_of_neg hδ0 hδ
      rwa [← mul_assoc, mul_inv_cancel₀ hδ0.ne, one_mul] at this
    linarith

end Miao.Applications
