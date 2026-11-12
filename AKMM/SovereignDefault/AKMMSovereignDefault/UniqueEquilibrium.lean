/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import AKMMSovereignDefault.MarkovPerfect

/-!
# Existence and uniqueness of the Markov perfect equilibrium with one-period debt

AKMM, Appendix 24.A.1, p. 901 ("Uniqueness"): "Auclert and Rognlie (2016) and Aguiar and
Amador (2019) show that in versions of the model with one-period bonds (i.e., when `δ = 1`), a
unique equilibrium exists. Furthermore, Aguiar and Amador (2019) show that the model can be
recast in a formulation that satisfies Blackwell's sufficient conditions." The book cites the
result without proof; this module proves it (beyond the text).

**Setting** (departure D10). The book's quantitative model of §24.4 with one-period debt
(`δ = 1`), finitely many income states (Markov matrix `P`), risk-neutral lenders with
`r > 0`, permanent exclusion after default (`ψ = 0`, the original Eaton–Gersovitz model) and a
*continuum* of debt levels: the sovereign may choose any `B′ ≤ B̄` (a borrowing limit
`B̄ ≥ 0`; saving, `B′ < 0`, is allowed), and states `B` range over `ℝ`. Utility `u : ℝ → ℝ`
is nondecreasing and uniformly continuous; for existence it is also satiated
(`u(c) = u(c̄)` for `c ≥ c̄`). The default cost is nonnegative, `φ(Y) ≥ 0`.

* The equilibrium (`IsOneMPE`) is the book's definition (§24.4.3, (24.9)–(24.12), (a)–(c)) at
  `δ = 1`, `ψ = 0`, with (24.11) a maximum over `B′ ≤ B̄` attained by the borrowing rule and
  values in the space of bounded functions.
* **Replication** (Auclert–Rognlie): if every debt the first price schedule lets the sovereign
  repay, the second lets it repay after a debt reduction `x`, then a sovereign facing the
  second schedule with debt `B − x/(1 + r)` does at least as well as one facing the first with
  debt `B` (`ue_replication`, with the revenue bound `ue_revenue`).
* **Uniqueness** (`ue_mpe_unique`): any two equilibria have the same values, default rule and
  prices. Iterating the replication shrinks the debt gap by `1/(1 + r)` each step.
* **Existence** (`ue_mpe_exists`): the debt capacities `b̄(Y)` (the largest debt repaid at
  income `Y`) are the fixed point of a map on `ℝ^Y` that is a contraction of modulus
  `1/(1 + r)` (the Blackwell recast; `ue_cutoff_lipschitz`). For a capacity vector the price
  is `q(B′, Y) = (1 + r)⁻¹ Pr(B′ ≤ b̄(Y′) | Y)`, the sovereign's Bellman equation is solved by
  monotone iteration (`ue_fixed_point`, Blackwell's monotonicity and discounting on bounded
  functions of an arbitrary state space), and at the fixed point the optimal borrowing exists
  because the objective is upper semicontinuous in `B′` and satiation makes very large savings
  useless (`ue_attain`).
* A concrete economy satisfying every hypothesis, with its unique equilibrium
  (`ue_example_exists_unique`).
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

/-- The one-period-debt economy with a continuum of debt levels (departure D10): income levels
`inc` with Markov matrix `P`, utility `u`, default cost `φ`, discount factor `β ∈ [0, 1)`, the
lenders' rate `r > 0` and the borrowing limit `B̄ ≥ 0`. -/
structure UEModel (Y : Type*) [Fintype Y] where
  /-- Income levels. -/
  inc : Y → ℝ
  /-- The income transition matrix. -/
  P : Matrix Y Y ℝ
  /-- `P` is a Markov matrix. -/
  markov : IsMarkov P
  /-- Utility. -/
  u : ℝ → ℝ
  /-- The income cost of default. -/
  φ : ℝ → ℝ
  /-- The discount factor. -/
  β : ℝ
  /-- `β ≥ 0`. -/
  β_nonneg : 0 ≤ β
  /-- `β < 1`. -/
  β_lt_one : β < 1
  /-- The lenders' risk-free rate. -/
  r : ℝ
  /-- `r > 0`. -/
  r_pos : 0 < r
  /-- The borrowing limit `B̄`. -/
  bmax : ℝ
  /-- `B̄ ≥ 0`. -/
  bmax_nonneg : 0 ≤ bmax

/-- **Blackwell's sufficient conditions on an arbitrary state space** (monotone iteration): if
`T` maps functions with values in `[m, K]` into themselves, is monotone and discounts constants,
`T(f + k) ≤ Tf + βk`, then `T` has a fixed point with values in `[m, K]`. The iterates from the
constants `m` and `K` increase and decrease, are `β^n(K − m)` apart, and the supremum of the
increasing sequence is the fixed point. No metric on the function space is needed. -/
theorem ue_fixed_point {α γ : Type*} (T : (α → γ → ℝ) → α → γ → ℝ) {β m K : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hmK : m ≤ K)
    (hmono : ∀ f g : α → γ → ℝ, (∀ a c, m ≤ f a c) → (∀ a c, g a c ≤ K + (K - m)) →
      (∀ a c, f a c ≤ g a c) → ∀ a c, T f a c ≤ T g a c)
    (hdisc : ∀ (f : α → γ → ℝ) (k : ℝ), (∀ a c, m ≤ f a c ∧ f a c ≤ K) → 0 ≤ k →
      ∀ a c, T (fun a c => f a c + k) a c ≤ T f a c + β * k)
    (hbox : ∀ f : α → γ → ℝ, (∀ a c, m ≤ f a c ∧ f a c ≤ K) → ∀ a c, m ≤ T f a c ∧ T f a c ≤ K) :
    ∃ V : α → γ → ℝ, (∀ a c, T V a c = V a c) ∧ ∀ a c, m ≤ V a c ∧ V a c ≤ K := by
  set L : ℕ → α → γ → ℝ := fun n => T^[n] (fun _ _ => m) with hLdef
  set U : ℕ → α → γ → ℝ := fun n => T^[n] (fun _ _ => K) with hUdef
  have hLs : ∀ n, L (n + 1) = T (L n) := fun n => Function.iterate_succ_apply' T n _
  have hUs : ∀ n, U (n + 1) = T (U n) := fun n => Function.iterate_succ_apply' T n _
  have hL0 : L 0 = fun _ _ => m := rfl
  have hU0 : U 0 = fun _ _ => K := rfl
  have hKm : 0 ≤ K - m := by linarith
  have hL : ∀ n a c, m ≤ L n a c ∧ L n a c ≤ K := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0]; exact ⟨le_rfl, hmK⟩
    | succ n ih => intro a c; rw [hLs]; exact hbox _ ih a c
  have hU : ∀ n a c, m ≤ U n a c ∧ U n a c ≤ K := by
    intro n
    induction n with
    | zero => intro a c; rw [hU0]; exact ⟨hmK, le_rfl⟩
    | succ n ih => intro a c; rw [hUs]; exact hbox _ ih a c
  have hLmono : ∀ n a c, L n a c ≤ L (n + 1) a c := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0]; exact (hL 1 a c).1
    | succ n ih =>
      intro a c
      rw [hLs (n + 1)]
      conv_lhs => rw [hLs n]
      exact hmono _ _ (fun a c => (hL n a c).1) (fun a c => by linarith [(hL (n + 1) a c).2])
        ih a c
  have hUanti : ∀ n a c, U (n + 1) a c ≤ U n a c := by
    intro n
    induction n with
    | zero => intro a c; rw [hU0]; exact (hU 1 a c).2
    | succ n ih =>
      intro a c
      rw [hUs (n + 1)]
      conv_rhs => rw [hUs n]
      exact hmono _ _ (fun a c => (hU (n + 1) a c).1) (fun a c => by linarith [(hU n a c).2])
        ih a c
  have hLU : ∀ n a c, L n a c ≤ U n a c := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0, hU0]; exact hmK
    | succ n ih =>
      intro a c
      rw [hLs, hUs]
      exact hmono _ _ (fun a c => (hL n a c).1) (fun a c => by linarith [(hU n a c).2]) ih a c
  have hgap : ∀ n a c, U n a c ≤ L n a c + β ^ n * (K - m) := by
    intro n
    induction n with
    | zero => intro a c; rw [hL0, hU0]; simp
    | succ n ih =>
      intro a c
      have hpow : β ^ n ≤ 1 := pow_le_one₀ hβ0 hβ1.le
      have hk : 0 ≤ β ^ n * (K - m) := mul_nonneg (pow_nonneg hβ0 n) hKm
      rw [hUs, hLs]
      calc T (U n) a c ≤ T (fun a c => L n a c + β ^ n * (K - m)) a c :=
            hmono _ _ (fun a c => (hU n a c).1)
              (fun a c => by nlinarith [(hL n a c).2]) ih a c
        _ ≤ T (L n) a c + β * (β ^ n * (K - m)) := hdisc _ _ (hL n) hk a c
        _ = T (L n) a c + β ^ (n + 1) * (K - m) := by ring
  have hbdd : ∀ a c, BddAbove (Set.range fun n => L n a c) := fun a c =>
    ⟨K, by rintro _ ⟨n, rfl⟩; exact (hL n a c).2⟩
  set V : α → γ → ℝ := fun a c => ⨆ n, L n a c with hVdef
  have hLV : ∀ n a c, L n a c ≤ V a c := fun n a c => le_ciSup (hbdd a c) n
  have hVU : ∀ n a c, V a c ≤ U n a c := by
    intro n a c
    refine ciSup_le fun k => ?_
    have hLm : Monotone fun n => L n a c := monotone_nat_of_le_succ fun n => hLmono n a c
    have hUa : Antitone fun n => U n a c := antitone_nat_of_succ_le fun n => hUanti n a c
    calc L k a c ≤ L (max k n) a c := hLm (le_max_left k n)
      _ ≤ U (max k n) a c := hLU _ a c
      _ ≤ U n a c := hUa (le_max_right k n)
  have hVbox : ∀ a c, m ≤ V a c ∧ V a c ≤ K := fun a c =>
    ⟨(hL 0 a c).1.trans (hLV 0 a c), (hVU 0 a c).trans (hU 0 a c).2⟩
  refine ⟨V, fun a c => le_antisymm ?_ ?_, hVbox⟩
  · have hle : ∀ n, T V a c ≤ V a c + β ^ n * (K - m) := fun n =>
      calc T V a c ≤ T (U n) a c :=
            hmono _ _ (fun a c => (hVbox a c).1) (fun a c => by linarith [(hU n a c).2])
              (hVU n) a c
        _ = U (n + 1) a c := by rw [hUs]
        _ ≤ U n a c := hUanti n a c
        _ ≤ L n a c + β ^ n * (K - m) := hgap n a c
        _ ≤ V a c + β ^ n * (K - m) := by linarith [hLV n a c]
    have ht : Filter.Tendsto (fun n : ℕ => V a c + β ^ n * (K - m)) Filter.atTop
        (nhds (V a c + 0 * (K - m))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const _).const_add _
    rw [zero_mul, add_zero] at ht
    exact ge_of_tendsto' ht hle
  · refine ciSup_le fun n => ?_
    calc L n a c ≤ L (n + 1) a c := hLmono n a c
      _ = T (L n) a c := by rw [hLs]
      _ ≤ T V a c := hmono _ _ (fun a c => (hL n a c).1)
          (fun a c => by linarith [(hVbox a c).2]) (fun a c => hLV n a c) a c

variable {Y : Type*} [Fintype Y]

/-- Expectations under a Markov row are bounded by bounds on the integrand. -/
theorem ue_sum_le {P : Matrix Y Y ℝ} (hP : IsMarkov P) {f : Y → ℝ} {K : ℝ} (h : ∀ j, f j ≤ K)
    (y : Y) : ∑ j, P y j * f j ≤ K :=
  calc ∑ j, P y j * f j ≤ ∑ j, P y j * K :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP.nonneg y j)
    _ = K := by rw [← sum_mul, hP.rowsum, one_mul]

/-- Expectations under a Markov row are bounded below by lower bounds on the integrand. -/
theorem ue_le_sum {P : Matrix Y Y ℝ} (hP : IsMarkov P) {f : Y → ℝ} {K : ℝ} (h : ∀ j, K ≤ f j)
    (y : Y) : K ≤ ∑ j, P y j * f j :=
  calc K = ∑ j, P y j * K := by rw [← sum_mul, hP.rowsum, one_mul]
    _ ≤ ∑ j, P y j * f j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP.nonneg y j)

/-- Expectations under a Markov row are monotone. -/
theorem ue_sum_mono {P : Matrix Y Y ℝ} (hP : IsMarkov P) {f g : Y → ℝ} (h : ∀ j, f j ≤ g j)
    (y : Y) : ∑ j, P y j * f j ≤ ∑ j, P y j * g j :=
  sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hP.nonneg y j)

/-- Expectations under a Markov row shift with constants. -/
theorem ue_sum_add {P : Matrix Y Y ℝ} (hP : IsMarkov P) (f : Y → ℝ) (c : ℝ) (y : Y) :
    ∑ j, P y j * (f j + c) = ∑ j, P y j * f j + c := by
  simp only [mul_add, sum_add_distrib, ← sum_mul, hP.rowsum, one_mul]

namespace UEModel

variable (M : UEModel Y)

/-- AKMM, (24.12) at `δ = 1`: the price `q(B′, Y) = (1 + r)⁻¹ Σ_j P(Y, j) a(B′, j)` given the
repayment indicator (or probability) `a = 1 − D̂`. -/
noncomputable def price (a : ℝ → Y → ℝ) (b' : ℝ) (y : Y) : ℝ :=
  (1 + M.r)⁻¹ * ∑ j, M.P y j * a b' j

/-- AKMM, (24.11) at `δ = 1`: the objective `u(Y − B + q(B′, Y)B′) + βE V(B′, Y′)` of the
repaying sovereign with debt `B` choosing `B′`. -/
def obj (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (b' : ℝ) : ℝ :=
  M.u (M.inc y - b + q b' y * b') + M.β * ∑ j, M.P y j * V b' j

/-- AKMM, (24.10) at `ψ = 0`: the right-hand side `u(Y − φ(Y)) + βE V^D(Y′)`. -/
def defaultRHS (VD : Y → ℝ) (y : Y) : ℝ :=
  M.u (M.inc y - M.φ (M.inc y)) + M.β * ∑ j, M.P y j * VD j

end UEModel

variable (M : UEModel Y) (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D : ℝ → Y → ℝ) (Bh : ℝ → Y → ℝ)
  (q : ℝ → Y → ℝ) in
/-- **AKMM, §24.4.3**, pp. 744–745, Markov perfect equilibrium with one-period debt (`δ = 1`),
permanent exclusion (`ψ = 0`) and a continuum of debt levels `B′ ≤ B̄` (departure D10): bounded
values `V`, `V^R`, `V^D`, a default rule `D̂`, a borrowing rule `B̂` and a price `q` with
(a) (24.9)–(24.11), (b) (24.12), (c) `D̂` and `B̂` optimal. -/
structure IsOneMPE : Prop where
  /-- Values lie in the space of bounded functions. -/
  bdd : ∃ K, ∀ b y, V b y ≤ K
  /-- (a) (24.9). -/
  eq_24_9 : ∀ b y, V b y = max (VD y) (VR b y)
  /-- (a) (24.10) with `ψ = 0`. -/
  eq_24_10 : ∀ y, VD y = M.defaultRHS VD y
  /-- (a) (24.11): `V^R` is an upper bound of the objective over `B′ ≤ B̄` ... -/
  eq_24_11 : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y
  /-- (b) (24.12) with `δ = 1`: `q(B′, Y) = (1 + r)⁻¹ E[1 − D̂(B′, Y′)]`. -/
  eq_24_12 : ∀ b' y, b' ≤ M.bmax → q b' y = (1 + M.r)⁻¹ * ∑ j, M.P y j * (1 - D b' j)
  /-- (c) the default rule is optimal (ties repaid). -/
  default_opt : ∀ b y, D b y = if VR b y < VD y then 1 else 0
  /-- The borrowing rule is feasible. -/
  borrow_le : ∀ b y, Bh b y ≤ M.bmax
  /-- (c) ... and the borrowing rule attains it, so (24.11) is a maximum. -/
  borrow_opt : ∀ b y, M.obj q V b y (Bh b y) = VR b y

/-- The repayment indicator of a vector of debt capacities `b̄`: `1{B′ ≤ b̄(Y′)}`. -/
noncomputable def ue_thr {Y : Type*} (bt : Y → ℝ) (b' : ℝ) (j : Y) : ℝ :=
  if b' ≤ bt j then 1 else 0

namespace UEModel

variable (M : UEModel Y)

/-- The price lies in `[0, (1 + r)⁻¹]` when the repayment indicator lies in `[0, 1]`. -/
theorem ue_price_mem {a : ℝ → Y → ℝ} {b' : ℝ} (ha : ∀ j, 0 ≤ a b' j ∧ a b' j ≤ 1) (y : Y) :
    0 ≤ M.price a b' y ∧ M.price a b' y ≤ (1 + M.r)⁻¹ := by
  have hr : 0 < (1 + M.r)⁻¹ := inv_pos.2 (by linarith [M.r_pos])
  unfold price
  exact ⟨mul_nonneg hr.le (ue_le_sum M.markov (fun j => (ha j).1) y),
    mul_le_of_le_one_right hr.le (ue_sum_le M.markov (fun j => (ha j).2) y)⟩

/-- Without default risk the price is the risk-free price `(1 + r)⁻¹`. -/
theorem ue_price_one {a : ℝ → Y → ℝ} {b' : ℝ} (ha : ∀ j, a b' j = 1) (y : Y) :
    M.price a b' y = (1 + M.r)⁻¹ := by
  unfold price
  simp only [ha, mul_one, M.markov.rowsum]

/-- The price is monotone in the repayment indicator. -/
theorem ue_price_mono {a a' : ℝ → Y → ℝ} {b' b'' : ℝ} (h : ∀ j, a b' j ≤ a' b'' j) (y : Y) :
    M.price a b' y ≤ M.price a' b'' y :=
  mul_le_mul_of_nonneg_left (ue_sum_mono M.markov h y) (inv_nonneg.2 (by linarith [M.r_pos]))

/-- **The revenue bound.** If every debt `B′` repaid under `a₁` is repaid under `a₂` after a
reduction `x ≥ 0`, and debt `B′ ≤ 0` is always repaid, then issuing `B′ − x` at the second price
raises at least the revenue of issuing `B′` at the first, less `x/(1 + r)`. -/
theorem ue_revenue {a₁ a₂ q₁ q₂ : ℝ → Y → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hq₁ : ∀ b' y, b' ≤ M.bmax → q₁ b' y = M.price a₁ b' y)
    (hq₂ : ∀ b' y, b' ≤ M.bmax → q₂ b' y = M.price a₂ b' y)
    (ha₁ : ∀ b' j, 0 ≤ a₁ b' j ∧ a₁ b' j ≤ 1)
    (hneg₁ : ∀ b' j, b' ≤ 0 → a₁ b' j = 1) (hneg₂ : ∀ b' j, b' ≤ 0 → a₂ b' j = 1)
    (hdom : ∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - x) j) {b' : ℝ} (hb' : b' ≤ M.bmax)
    (y : Y) : q₁ b' y * b' - x * (1 + M.r)⁻¹ ≤ q₂ (b' - x) y * (b' - x) := by
  rw [hq₁ b' y hb', hq₂ (b' - x) y (by linarith)]
  have hp1 := M.ue_price_mem (fun j => ha₁ b' j) y
  have hp12 : M.price a₁ b' y ≤ M.price a₂ (b' - x) y :=
    M.ue_price_mono (fun j => hdom b' j hb') y
  rcases le_or_gt 0 (b' - x) with hpos | hneg
  · nlinarith [mul_le_mul_of_nonneg_right hp12 hpos, mul_le_mul_of_nonneg_right hp1.2 hx]
  · rw [M.ue_price_one (fun j => hneg₂ (b' - x) j hneg.le) y]
    rcases le_or_gt 0 b' with hb0 | hb0
    · nlinarith [mul_le_mul_of_nonneg_right hp1.2 hb0]
    · rw [M.ue_price_one (fun j => hneg₁ b' j hb0.le) y]
      linarith

/-- **The replication argument** (Auclert–Rognlie 2016). Let `V^R₁` be the supremum of the
objective at the prices `q₁` (approximated by feasible choices) and `V^R₂` an upper bound of the
objective at `q₂`, with `V_k = max(V^D, V^R_k)`, `V₁` bounded and `V₂` nonincreasing in debt. If
issuing `B′ − x` at `q₂` raises the revenue of `B′` at `q₁` less `g ≤ x`, then a sovereign with
debt `B − g` facing `q₂` does at least as well as one with debt `B` facing `q₁`:
`V^R₁(B, Y) ≤ V^R₂(B − g, Y)`. The proof bounds `e = sup (V₁(B) − V₂(B − g))` by `max(0, βe)`. -/
theorem ue_replication (hu : Monotone M.u) {q₁ q₂ V₁ V₂ VR₁ VR₂ : ℝ → Y → ℝ} {VD : Y → ℝ}
    {x g : ℝ} (hx : 0 ≤ x) (hgx : g ≤ x)
    (hV₁ : ∀ b y, V₁ b y = max (VD y) (VR₁ b y)) (hV₂ : ∀ b y, V₂ b y = max (VD y) (VR₂ b y))
    (hK : ∃ K, ∀ b y, V₁ b y ≤ K)
    (hsup : ∀ b y ε, 0 < ε → ∃ b', b' ≤ M.bmax ∧ VR₁ b y ≤ M.obj q₁ V₁ b y b' + ε)
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q₂ V₂ b y b' ≤ VR₂ b y)
    (hanti : ∀ b b' y, b ≤ b' → V₂ b' y ≤ V₂ b y)
    (hrev : ∀ b' y, b' ≤ M.bmax → q₁ b' y * b' - g ≤ q₂ (b' - x) y * (b' - x)) (b : ℝ)
    (y : Y) : VR₁ b y ≤ VR₂ (b - g) y := by
  obtain ⟨K, hK⟩ := hK
  have hV₂low : ∀ b j, -‖VD‖ ≤ V₂ b j := fun b j => by
    rw [hV₂]
    have h1 := norm_le_pi_norm VD j
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (VD j), le_max_left (VD j) (VR₂ b j)]
  set e := ⨆ p : ℝ × Y, (V₁ p.1 p.2 - V₂ (p.1 - g) p.2) with he
  have hbdd : BddAbove (Set.range fun p : ℝ × Y => V₁ p.1 p.2 - V₂ (p.1 - g) p.2) :=
    ⟨K + ‖VD‖, by rintro _ ⟨p, rfl⟩; linarith [hK p.1 p.2, hV₂low (p.1 - g) p.2]⟩
  have hle_e : ∀ b j, V₁ b j ≤ V₂ (b - g) j + e := fun b j => by
    have h1 := le_ciSup hbdd (b, j)
    simp only at h1
    linarith
  have step1 : ∀ b y, VR₁ b y ≤ VR₂ (b - g) y + M.β * e := by
    intro b y
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨b', hb', hε'⟩ := hsup b y ε hε
    have hc : M.inc y - b + q₁ b' y * b' ≤ M.inc y - (b - g) + q₂ (b' - x) y * (b' - x) := by
      linarith [hrev b' y hb']
    have hs : ∑ j, M.P y j * V₁ b' j ≤ ∑ j, M.P y j * V₂ (b' - x) j + e := by
      rw [← ue_sum_add M.markov]
      exact ue_sum_mono M.markov (fun j => (hle_e b' j).trans
        (by linarith [hanti (b' - x) (b' - g) j (by linarith)])) y
    have h1 : M.obj q₁ V₁ b y b' ≤ M.obj q₂ V₂ (b - g) y (b' - x) + M.β * e := by
      unfold UEModel.obj
      nlinarith [hu hc, mul_le_mul_of_nonneg_left hs M.β_nonneg]
    have h2 := hle (b - g) y (b' - x) (by linarith)
    linarith
  have step2 : e ≤ max 0 (M.β * e) := by
    have : Nonempty Y := ⟨y⟩
    refine ciSup_le fun p => ?_
    rw [hV₁, hV₂]
    have h1 := step1 p.1 p.2
    have hA : max (VD p.2) (VR₁ p.1 p.2) ≤
        max (VD p.2) (VR₂ (p.1 - g) p.2) + max 0 (M.β * e) :=
      max_le (by linarith [le_max_left (VD p.2) (VR₂ (p.1 - g) p.2), le_max_left 0 (M.β * e)])
        (by linarith [le_max_right (VD p.2) (VR₂ (p.1 - g) p.2), le_max_right 0 (M.β * e)])
    linarith
  have step3 : e ≤ 0 := by
    by_contra hcon
    have hpos : 0 < e := lt_of_not_ge hcon
    have hbe : 0 ≤ M.β * e := mul_nonneg M.β_nonneg hpos.le
    rw [max_eq_right hbe] at step2
    nlinarith [M.β_lt_one]
  linarith [step1 b y, mul_nonpos_of_nonneg_of_nonpos M.β_nonneg step3]

/-- **Uniform continuity of the repayment value in debt.** If `V^R` is the supremum of the
objective over `B′ ≤ B̄` and `u` is uniformly continuous, then reducing debt by less than `η`
raises `V^R` by at most `ε`. -/
theorem ue_modulus (huc : UniformContinuous M.u) {q V VR : ℝ → Y → ℝ}
    (hsup : ∀ b y ε, 0 < ε → ∃ b', b' ≤ M.bmax ∧ VR b y ≤ M.obj q V b y b' + ε)
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ b y h, 0 ≤ h → h < η → VR (b - h) y ≤ VR b y + ε := by
  obtain ⟨η, hη, H⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  refine ⟨η, hη, fun b y h h0 hη' => ?_⟩
  obtain ⟨b', hb', hb'ε⟩ := hsup (b - h) y (ε / 2) (half_pos hε)
  have hd : dist (M.inc y - (b - h) + q b' y * b') (M.inc y - b + q b' y * b') < η := by
    rw [Real.dist_eq]
    have : M.inc y - (b - h) + q b' y * b' - (M.inc y - b + q b' y * b') = h := by ring
    rw [this, abs_of_nonneg h0]
    exact hη'
  have hu := H hd
  rw [Real.dist_eq] at hu
  have hu' := (abs_lt.1 hu).2
  have h2 := hle b y b' hb'
  unfold UEModel.obj at hb'ε h2
  linarith

/-- **`V^R` is nonincreasing in debt** when it is the supremum of the objective. -/
theorem ue_VR_antitone (hu : Monotone M.u) {q V VR : ℝ → Y → ℝ}
    (hsup : ∀ b y ε, 0 < ε → ∃ b', b' ≤ M.bmax ∧ VR b y ≤ M.obj q V b y b' + ε)
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y) {b b'' : ℝ} (hbb : b ≤ b'')
    (y : Y) : VR b'' y ≤ VR b y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b', hb', hb'ε⟩ := hsup b'' y ε hε
  have h1 : M.obj q V b'' y b' ≤ M.obj q V b y b' := by
    unfold UEModel.obj
    have := hu (show M.inc y - b'' + q b' y * b' ≤ M.inc y - b + q b' y * b' by linarith)
    linarith
  linarith [hle b y b' hb']

/-- **Debt `B ≤ 0` is always repaid**: with `φ ≥ 0` and `u` nondecreasing, keeping `B′ = 0` is
worth at least `V^D(Y)`. -/
theorem ue_repay_nonpos (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y))
    {q V VR : ℝ → Y → ℝ} {VD : Y → ℝ}
    (hle : ∀ b y b', b' ≤ M.bmax → M.obj q V b y b' ≤ VR b y) (hV : ∀ b y, VD y ≤ V b y)
    (hVD : ∀ y, VD y = M.defaultRHS VD y) {b : ℝ} (hb : b ≤ 0) (y : Y) : VD y ≤ VR b y := by
  have h1 := hle b y 0 M.bmax_nonneg
  have h2 : M.u (M.inc y - M.φ (M.inc y)) ≤ M.u (M.inc y - b + q 0 y * 0) :=
    hu (by linarith [hφ y])
  have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun j => hV 0 j) y) M.β_nonneg
  rw [hVD y]
  unfold UEModel.obj at h1
  unfold UEModel.defaultRHS
  linarith

/-- AKMM, (24.10) at `ψ = 0`: the default value is unique. -/
theorem ue_VD_unique {VD₁ VD₂ : Y → ℝ} (h₁ : ∀ y, VD₁ y = M.defaultRHS VD₁ y)
    (h₂ : ∀ y, VD₂ y = M.defaultRHS VD₂ y) : VD₁ = VD₂ := by
  funext y
  have : Nonempty Y := ⟨y⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => |VD₁ j - VD₂ j|
  have hdiff : VD₁ j₀ - VD₂ j₀ = M.β * ∑ j, M.P j₀ j * (VD₁ j - VD₂ j) := by
    rw [h₁ j₀, h₂ j₀]
    unfold UEModel.defaultRHS
    simp only [mul_sub, sum_sub_distrib]
    ring
  have hs : |∑ j, M.P j₀ j * (VD₁ j - VD₂ j)| ≤ |VD₁ j₀ - VD₂ j₀| :=
    calc |∑ j, M.P j₀ j * (VD₁ j - VD₂ j)| ≤ ∑ j, |M.P j₀ j * (VD₁ j - VD₂ j)| :=
          abs_sum_le_sum_abs _ _
      _ = ∑ j, M.P j₀ j * |VD₁ j - VD₂ j| := by
          refine sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (M.markov.nonneg j₀ j)]
      _ ≤ |VD₁ j₀ - VD₂ j₀| := ue_sum_le M.markov hj₀ j₀
  have hle : |VD₁ j₀ - VD₂ j₀| ≤ M.β * |VD₁ j₀ - VD₂ j₀| := by
    calc |VD₁ j₀ - VD₂ j₀| = M.β * |∑ j, M.P j₀ j * (VD₁ j - VD₂ j)| := by
          rw [hdiff, abs_mul, abs_of_nonneg M.β_nonneg]
      _ ≤ M.β * |VD₁ j₀ - VD₂ j₀| := mul_le_mul_of_nonneg_left hs M.β_nonneg
  have h0 : |VD₁ j₀ - VD₂ j₀| = 0 := by
    nlinarith [abs_nonneg (VD₁ j₀ - VD₂ j₀), M.β_lt_one]
  have hy := hj₀ y
  rw [h0] at hy
  have := abs_nonneg (VD₁ y - VD₂ y)
  have h' : |VD₁ y - VD₂ y| = 0 := le_antisymm hy this
  linarith [abs_eq_zero.1 h']

/-- In an equilibrium `V^R` is approximated by feasible choices (here attained by `B̂`). -/
theorem ue_mpe_sup {V VR : ℝ → Y → ℝ} {VD : Y → ℝ} {D Bh q : ℝ → Y → ℝ}
    (h : IsOneMPE M V VR VD D Bh q) (b : ℝ) (y : Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ b', b' ≤ M.bmax ∧ VR b y ≤ M.obj q V b y b' + ε :=
  ⟨Bh b y, h.borrow_le b y, by rw [h.borrow_opt]; linarith⟩

/-- One direction of uniqueness: in two equilibria, `V^R₁ ≤ V^R₂`. The debt-reduction gap
`x_n = B̄(1 + r)^{−n}` makes the repayment sets nested, `D̂₁(B′) = 0 ⇒ D̂₂(B′ − x_n) = 0`; each
replication step shrinks it by `1/(1 + r)`; uniform continuity closes the gap. -/
theorem ue_mpe_VR_le (hu : Monotone M.u) (huc : UniformContinuous M.u)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Y → ℝ}
    {VD₁ VD₂ : Y → ℝ} (h₁ : IsOneMPE M V₁ VR₁ VD₁ D₁ Bh₁ q₁)
    (h₂ : IsOneMPE M V₂ VR₂ VD₂ D₂ Bh₂ q₂) (b : ℝ) (y : Y) : VR₁ b y ≤ VR₂ b y := by
  have hVD : VD₁ = VD₂ := M.ue_VD_unique h₁.eq_24_10 h₂.eq_24_10
  subst hVD
  set ρ : ℝ := (1 + M.r)⁻¹ with hρ
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hρ0 : 0 < ρ := inv_pos.2 hr1
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by linarith [M.r_pos])
  set a₁ : ℝ → Y → ℝ := fun b j => 1 - D₁ b j with ha₁
  set a₂ : ℝ → Y → ℝ := fun b j => 1 - D₂ b j with ha₂
  have hrep₁ : ∀ b j, VD₁ j ≤ VR₁ b j → a₁ b j = 1 := fun b j h => by
    simp only [ha₁, h₁.default_opt, not_lt.2 h, ↓reduceIte, sub_zero]
  have hrep₂ : ∀ b j, VD₁ j ≤ VR₂ b j → a₂ b j = 1 := fun b j h => by
    simp only [ha₂, h₂.default_opt, not_lt.2 h, ↓reduceIte, sub_zero]
  have hdef₁ : ∀ b j, VR₁ b j < VD₁ j → a₁ b j = 0 := fun b j h => by
    simp only [ha₁, h₁.default_opt, h, ↓reduceIte, sub_self]
  have hmem₁ : ∀ b j, 0 ≤ a₁ b j ∧ a₁ b j ≤ 1 := fun b j => by
    rcases lt_or_ge (VR₁ b j) (VD₁ j) with h | h
    · rw [hdef₁ b j h]; norm_num
    · rw [hrep₁ b j h]; norm_num
  have hmem₂ : ∀ b j, 0 ≤ a₂ b j ∧ a₂ b j ≤ 1 := fun b j => by
    simp only [ha₂, h₂.default_opt]
    split_ifs <;> norm_num
  have hneg₁ : ∀ b j, b ≤ 0 → a₁ b j = 1 := fun b j hb =>
    hrep₁ b j (M.ue_repay_nonpos hu hφ h₁.eq_24_11
      (fun b y => by rw [h₁.eq_24_9]; exact le_max_left _ _) h₁.eq_24_10 hb j)
  have hneg₂ : ∀ b j, b ≤ 0 → a₂ b j = 1 := fun b j hb =>
    hrep₂ b j (M.ue_repay_nonpos hu hφ h₂.eq_24_11
      (fun b y => by rw [h₂.eq_24_9]; exact le_max_left _ _) h₁.eq_24_10 hb j)
  have hq₁ : ∀ b' y, b' ≤ M.bmax → q₁ b' y = M.price a₁ b' y := fun b' y hb' =>
    h₁.eq_24_12 b' y hb'
  have hq₂ : ∀ b' y, b' ≤ M.bmax → q₂ b' y = M.price a₂ b' y := fun b' y hb' =>
    h₂.eq_24_12 b' y hb'
  have hanti₂ : ∀ b b' y, b ≤ b' → V₂ b' y ≤ V₂ b y := fun b b' y hbb => by
    rw [h₂.eq_24_9, h₂.eq_24_9]
    exact max_le_max le_rfl (M.ue_VR_antitone hu (M.ue_mpe_sup h₂) h₂.eq_24_11 hbb y)
  set xs : ℕ → ℝ := fun n => M.bmax * ρ ^ n with hxs
  have hx0 : ∀ n, 0 ≤ xs n := fun n => mul_nonneg M.bmax_nonneg (pow_nonneg hρ0.le n)
  have hstep : ∀ n, (∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - xs n) j) →
      ∀ b y, VR₁ b y ≤ VR₂ (b - xs (n + 1)) y := by
    intro n hdom b y
    have hxs1 : xs (n + 1) = xs n * ρ := by simp only [hxs, pow_succ]; ring
    refine M.ue_replication hu (hx0 n) (by rw [hxs1]; nlinarith [hx0 n]) h₁.eq_24_9
      h₂.eq_24_9 h₁.bdd (M.ue_mpe_sup h₁) h₂.eq_24_11 hanti₂ (fun b' y hb' => ?_) b y
    rw [hxs1]
    exact M.ue_revenue (hx0 n) hq₁ hq₂ hmem₁ hneg₁ hneg₂ hdom hb' y
  have hdom : ∀ n, ∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - xs n) j := by
    intro n
    induction n with
    | zero =>
      intro b' j hb'
      rw [hneg₂ _ j (by simp only [hxs, pow_zero, mul_one]; linarith)]
      exact (hmem₁ b' j).2
    | succ n ih =>
      intro b' j _
      rcases lt_or_ge (VR₁ b' j) (VD₁ j) with h | h
      · rw [hdef₁ b' j h]; exact (hmem₂ _ j).1
      · rw [hrep₁ b' j h, hrep₂ _ j (h.trans (hstep n ih b' j))]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc (M.ue_mpe_sup h₂) h₂.eq_24_11 hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hη (by linarith [M.bmax_nonneg] :
    (0 : ℝ) < M.bmax + 1)) hρ1
  have hxn : xs (n + 1) < η := by
    have h1 : ρ ^ (n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.le_succ n)
    have h2 : M.bmax * ρ ^ n < η := by
      have := (lt_div_iff₀ (by linarith [M.bmax_nonneg] : (0 : ℝ) < M.bmax + 1)).1 hn
      nlinarith [pow_nonneg hρ0.le n, M.bmax_nonneg]
    simp only [hxs]
    nlinarith [M.bmax_nonneg]
  have h1 := hstep n (hdom n) b y
  have h2 := hmod b y (xs (n + 1)) (hx0 (n + 1)) hxn
  linarith

/-- **Uniqueness of the Markov perfect equilibrium with one-period debt** (Auclert–Rognlie
2016; Aguiar–Amador 2019; AKMM, p. 901, beyond the text): with `u` nondecreasing and uniformly
continuous, `φ ≥ 0`, `r > 0`, any two equilibria have the same value functions `V`, `V^R`,
`V^D`, the same default rule `D̂` and the same prices `q(B′, Y)` for `B′ ≤ B̄`. (The borrowing
rule is unique up to the choice among maximisers.) -/
theorem ue_mpe_unique (hu : Monotone M.u) (huc : UniformContinuous M.u)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Y → ℝ}
    {VD₁ VD₂ : Y → ℝ} (h₁ : IsOneMPE M V₁ VR₁ VD₁ D₁ Bh₁ q₁)
    (h₂ : IsOneMPE M V₂ VR₂ VD₂ D₂ Bh₂ q₂) :
    V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧ ∀ b' y, b' ≤ M.bmax → q₁ b' y = q₂ b' y := by
  have hVD : VD₁ = VD₂ := M.ue_VD_unique h₁.eq_24_10 h₂.eq_24_10
  have hVR : VR₁ = VR₂ := funext fun b => funext fun y =>
    le_antisymm (M.ue_mpe_VR_le hu huc hφ h₁ h₂ b y) (M.ue_mpe_VR_le hu huc hφ h₂ h₁ b y)
  have hD : D₁ = D₂ := funext fun b => funext fun y => by
    rw [h₁.default_opt, h₂.default_opt, hVR, hVD]
  refine ⟨funext fun b => funext fun y => by rw [h₁.eq_24_9, h₂.eq_24_9, hVR, hVD], hVR, hVD,
    hD, fun b' y hb' => by rw [h₁.eq_24_12 b' y hb', h₂.eq_24_12 b' y hb', hD]⟩

/-- The utility of a satiated nondecreasing `u` is bounded by its satiation level. -/
theorem ue_u_le (hu : Monotone M.u) {cbar : ℝ} (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar)
    (c : ℝ) : M.u c ≤ M.u cbar := by
  rcases le_total c cbar with h | h
  · exact hu h
  · rw [hsat c h]

/-- The objective is bounded above when `u` and the continuation value are. -/
theorem ue_obj_le {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) (b' : ℝ) : M.obj q V b y b' ≤ ub + M.β * K := by
  unfold obj
  have := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun j => hV b' j) y) M.β_nonneg
  linarith [hub (M.inc y - b + q b' y * b')]

/-- The value of repaying as the supremum of the objective over `B′ ≤ B̄`. -/
noncomputable def VRsup (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) : ℝ :=
  ⨆ b' : ℝ, M.obj q V b y (min b' M.bmax)

/-- The Bellman operator of (24.9) and (24.11) given `V^D` and the prices `q`. -/
noncomputable def bell (VD : Y → ℝ) (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) : ℝ :=
  max (VD y) (M.VRsup q V b y)

/-- The debt capacity at income `Y`: the largest debt in `[0, B̄]` that is repaid. -/
noncomputable def cutoff (VD : Y → ℝ) (q V : ℝ → Y → ℝ) (j : Y) : ℝ :=
  sSup {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup q V b j}

/-- The family defining `V^R` is bounded above. -/
theorem ue_VRsup_bdd {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) :
    BddAbove (Set.range fun b' : ℝ => M.obj q V b y (min b' M.bmax)) :=
  ⟨ub + M.β * K, by rintro _ ⟨b', rfl⟩; exact M.ue_obj_le hub hV b y _⟩

/-- `V^R` bounds the objective at every feasible `B′`. -/
theorem ue_VRsup_le {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) {b' : ℝ} (hb' : b' ≤ M.bmax) :
    M.obj q V b y b' ≤ M.VRsup q V b y := by
  have := le_ciSup (M.ue_VRsup_bdd hub (q := q) hV b y) b'
  rwa [min_eq_left hb'] at this

/-- `V^R` is approximated by feasible choices. -/
theorem ue_VRsup_sup (q V : ℝ → Y → ℝ) (b : ℝ) (y : Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ b', b' ≤ M.bmax ∧ M.VRsup q V b y ≤ M.obj q V b y b' + ε := by
  have h : M.VRsup q V b y - ε < M.VRsup q V b y := by linarith
  obtain ⟨b'', hb''⟩ := exists_lt_of_lt_ciSup h
  exact ⟨min b'' M.bmax, min_le_right _ _, by linarith⟩

/-- `V^R` is bounded above. -/
theorem ue_VRsup_ub {ub K : ℝ} (hub : ∀ c, M.u c ≤ ub) {q V : ℝ → Y → ℝ}
    (hV : ∀ b j, V b j ≤ K) (b : ℝ) (y : Y) : M.VRsup q V b y ≤ ub + M.β * K :=
  ciSup_le fun _ => M.ue_obj_le hub hV b y _

/-- AKMM, (24.10) at `ψ = 0`: a default value exists, bounded by `ū/(1 − β)`. -/
theorem ue_VD_exists {ub : ℝ} (hub : ∀ c, M.u c ≤ ub) :
    ∃ VD : Y → ℝ, (∀ y, VD y = M.defaultRHS VD y) ∧ ∀ y, VD y ≤ ub / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := ub / (1 - M.β) with hK
  set A := ‖fun y => M.u (M.inc y - M.φ (M.inc y))‖ with hA
  set m := min K (-A / (1 - M.β)) with hm
  have hKK : ub + M.β * K = K := by rw [hK]; field_simp; ring
  have hmA : m ≤ -A + M.β * m := by
    have h1 : m ≤ -A / (1 - M.β) := min_le_right _ _
    rw [le_div_iff₀ h1β] at h1
    linarith
  have hAy : ∀ y, -A ≤ M.u (M.inc y - M.φ (M.inc y)) := fun y => by
    have h1 := norm_le_pi_norm (fun y => M.u (M.inc y - M.φ (M.inc y))) y
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (M.u (M.inc y - M.φ (M.inc y)))]
  obtain ⟨W, hW, hWb⟩ := ue_fixed_point (α := Unit) (γ := Y)
    (fun f _ y => M.defaultRHS (f ()) y) M.β_nonneg M.β_lt_one (min_le_left _ _)
    (fun f g _ _ hfg _ y => by
      unfold defaultRHS
      linarith [mul_le_mul_of_nonneg_left
        (ue_sum_mono M.markov (fun j => hfg () j) y) M.β_nonneg])
    (fun f k _ _ _ y => by
      simp only [defaultRHS, ue_sum_add M.markov]
      linarith)
    (fun f hf _ y => by
      unfold defaultRHS
      refine ⟨?_, ?_⟩
      · have := mul_le_mul_of_nonneg_left (ue_le_sum M.markov (fun j => (hf () j).1) y)
          M.β_nonneg
        linarith [hAy y]
      · have := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun j => (hf () j).2) y)
          M.β_nonneg
        linarith [hub (M.inc y - M.φ (M.inc y))])
  exact ⟨fun y => W () y, fun y => (hW () y).symm, fun y => (hWb () y).2⟩

/-- AKMM, (24.9) and (24.11) for given prices `q`: a bounded solution `V` exists (Blackwell's
conditions on the bounded functions of `(B, Y) ∈ ℝ × Y`, `ue_fixed_point`). -/
theorem ue_sol_exists {ub : ℝ} (hub : ∀ c, M.u c ≤ ub) {VD : Y → ℝ}
    (hVD : ∀ y, VD y ≤ ub / (1 - M.β)) (q : ℝ → Y → ℝ) :
    ∃ V : ℝ → Y → ℝ, (∀ b y, M.bell VD q V b y = V b y) ∧
      ∀ b y, min (ub / (1 - M.β)) (-‖VD‖) ≤ V b y ∧ V b y ≤ ub / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := ub / (1 - M.β) with hK
  have hKK : ub + M.β * K = K := by rw [hK]; field_simp; ring
  have hmVD : ∀ y, min K (-‖VD‖) ≤ VD y := fun y => by
    have h1 := norm_le_pi_norm VD y
    rw [Real.norm_eq_abs] at h1
    exact (min_le_right _ _).trans (by linarith [neg_abs_le (VD y)])
  refine ue_fixed_point (M.bell VD q) M.β_nonneg M.β_lt_one (min_le_left _ _) ?_ ?_ ?_
  · intro f g _ hg hfg b y
    refine max_le_max le_rfl (ciSup_mono (M.ue_VRsup_bdd hub hg b y) fun b' => ?_)
    unfold obj
    linarith [mul_le_mul_of_nonneg_left
      (ue_sum_mono M.markov (fun j => hfg (min b' M.bmax) j) y) M.β_nonneg]
  · intro f k hf hk b y
    have hS : M.VRsup q (fun a c => f a c + k) b y ≤ M.VRsup q f b y + M.β * k := by
      refine ciSup_le fun b' => ?_
      have h1 : M.obj q f b y (min b' M.bmax) ≤ M.VRsup q f b y :=
        le_ciSup (M.ue_VRsup_bdd hub (q := q) (fun a c => (hf a c).2) b y) b'
      have h2 : M.obj q (fun a c => f a c + k) b y (min b' M.bmax) =
          M.obj q f b y (min b' M.bmax) + M.β * k := by
        simp only [obj, ue_sum_add M.markov]
        ring
      rw [h2]
      linarith
    unfold bell
    exact max_le (by linarith [le_max_left (VD y) (M.VRsup q f b y), mul_nonneg M.β_nonneg hk])
      (by linarith [le_max_right (VD y) (M.VRsup q f b y)])
  · intro f hf b y
    refine ⟨(hmVD y).trans (le_max_left _ _), max_le (hVD y) ?_⟩
    have := M.ue_VRsup_ub hub (q := q) (fun a c => (hf a c).2) b y
    linarith

omit [Fintype Y] in
/-- The repayment indicator lies in `[0, 1]`. -/
theorem ue_thr_mem (bt : Y → ℝ) (b' : ℝ) (j : Y) : 0 ≤ ue_thr bt b' j ∧ ue_thr bt b' j ≤ 1 := by
  unfold ue_thr
  split_ifs <;> norm_num

omit [Fintype Y] in
/-- With nonnegative capacities, debt `B′ ≤ 0` is repaid. -/
theorem ue_thr_nonpos {bt : Y → ℝ} (hbt : ∀ j, 0 ≤ bt j) {b' : ℝ} (hb' : b' ≤ 0) (j : Y) :
    ue_thr bt b' j = 1 := by
  unfold ue_thr
  simp only [hb'.trans (hbt j), ↓reduceIte]

/-- **The Blackwell recast** (Aguiar–Amador 2019): the map from debt capacities to the
capacities they induce moves by at most `1/(1 + r)` times the change in the capacities:
`b̄′₁(Y) ≤ b̄′₂(Y) + ‖b̄₁ − b̄₂‖/(1 + r)`. It follows from the replication argument. -/
theorem ue_cutoff_le (hu : Monotone M.u) {ub : ℝ} (hub : ∀ c, M.u c ≤ ub)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {VD : Y → ℝ} (hVD : ∀ y, VD y = M.defaultRHS VD y)
    {bt₁ bt₂ : Y → ℝ} (h0₁ : ∀ j, 0 ≤ bt₁ j) (h0₂ : ∀ j, 0 ≤ bt₂ j) {V₁ V₂ : ℝ → Y → ℝ}
    (hV₁ : ∀ b y, M.bell VD (M.price (ue_thr bt₁)) V₁ b y = V₁ b y)
    (hV₁b : ∀ b y, V₁ b y ≤ ub / (1 - M.β))
    (hV₂ : ∀ b y, M.bell VD (M.price (ue_thr bt₂)) V₂ b y = V₂ b y)
    (hV₂b : ∀ b y, V₂ b y ≤ ub / (1 - M.β)) (j : Y) :
    M.cutoff VD (M.price (ue_thr bt₁)) V₁ j ≤
      M.cutoff VD (M.price (ue_thr bt₂)) V₂ j + dist bt₁ bt₂ * (1 + M.r)⁻¹ := by
  have hx : 0 ≤ dist bt₁ bt₂ := dist_nonneg
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hρ : (1 + M.r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [M.r_pos])
  have hg0 : 0 ≤ dist bt₁ bt₂ * (1 + M.r)⁻¹ := mul_nonneg hx (inv_nonneg.2 hr1.le)
  have hgx : dist bt₁ bt₂ * (1 + M.r)⁻¹ ≤ dist bt₁ bt₂ := mul_le_of_le_one_right hx hρ
  have hE₁ : ∀ b y, V₁ b y = max (VD y) (M.VRsup (M.price (ue_thr bt₁)) V₁ b y) :=
    fun b y => by rw [← hV₁ b y]; rfl
  have hE₂ : ∀ b y, V₂ b y = max (VD y) (M.VRsup (M.price (ue_thr bt₂)) V₂ b y) :=
    fun b y => by rw [← hV₂ b y]; rfl
  have hsup₂ := M.ue_VRsup_sup (M.price (ue_thr bt₂)) V₂
  have hle₂ : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt₂)) V₂ b y b' ≤
      M.VRsup (M.price (ue_thr bt₂)) V₂ b y := fun b y _ hb' => M.ue_VRsup_le hub hV₂b b y hb'
  have hle₁ : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt₁)) V₁ b y b' ≤
      M.VRsup (M.price (ue_thr bt₁)) V₁ b y := fun b y _ hb' => M.ue_VRsup_le hub hV₁b b y hb'
  have hanti₂ : ∀ b b' y, b ≤ b' → V₂ b' y ≤ V₂ b y := fun b b' y h => by
    rw [hE₂, hE₂]
    exact max_le_max le_rfl (M.ue_VR_antitone hu hsup₂ hle₂ h y)
  have hdom : ∀ b' j, b' ≤ M.bmax → ue_thr bt₁ b' j ≤ ue_thr bt₂ (b' - dist bt₁ bt₂) j := by
    intro b' j _
    unfold ue_thr
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      have h3 := dist_le_pi_dist bt₁ bt₂ j
      rw [Real.dist_eq] at h3
      linarith [le_abs_self (bt₁ j - bt₂ j)]
    · norm_num
    · exact le_rfl
  have hrep : ∀ b y, M.VRsup (M.price (ue_thr bt₁)) V₁ b y ≤
      M.VRsup (M.price (ue_thr bt₂)) V₂ (b - dist bt₁ bt₂ * (1 + M.r)⁻¹) y :=
    M.ue_replication hu hx hgx hE₁ hE₂ ⟨_, hV₁b⟩ (M.ue_VRsup_sup _ _) hle₂ hanti₂
      (fun b' y hb' => M.ue_revenue hx (fun _ _ _ => rfl) (fun _ _ _ => rfl) (ue_thr_mem bt₁)
        (fun _ j h => ue_thr_nonpos h0₁ h j) (fun _ j h => ue_thr_nonpos h0₂ h j) hdom hb' y)
  set S₁ := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup (M.price (ue_thr bt₁)) V₁ b j} with hS₁
  set S₂ := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup (M.price (ue_thr bt₂)) V₂ b j} with hS₂
  have h0S₁ : (0 : ℝ) ∈ S₁ := ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hle₁
    (fun b y => by rw [hE₁]; exact le_max_left _ _) hVD le_rfl j⟩
  have h0S₂ : (0 : ℝ) ∈ S₂ := ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hle₂
    (fun b y => by rw [hE₂]; exact le_max_left _ _) hVD le_rfl j⟩
  have hbdd₂ : BddAbove S₂ := ⟨M.bmax, fun b hb => hb.2.1⟩
  have hc0 : 0 ≤ sSup S₂ := le_csSup hbdd₂ h0S₂
  change sSup S₁ ≤ sSup S₂ + dist bt₁ bt₂ * (1 + M.r)⁻¹
  refine csSup_le ⟨0, h0S₁⟩ fun b hb => ?_
  obtain ⟨_, hbm, hbv⟩ := hb
  rcases le_or_gt 0 (b - dist bt₁ bt₂ * (1 + M.r)⁻¹) with h | h
  · have hmem : b - dist bt₁ bt₂ * (1 + M.r)⁻¹ ∈ S₂ :=
      ⟨h, by linarith, hbv.trans (hrep b j)⟩
    linarith [le_csSup hbdd₂ hmem]
  · linarith

/-- **The debt capacities are a fixed point of a contraction.** Given, for each capacity vector
`b̄`, a bounded solution of the Bellman equation at the prices `q = (1 + r)⁻¹ E 1{B′ ≤ b̄(Y′)}`,
the map `b̄ ↦` (the induced capacities) has a fixed point `b̄ ≥ 0` (Banach, modulus
`1/(1 + r)`, `ue_cutoff_le`). -/
theorem ue_capacity_fixed (hu : Monotone M.u) {ub : ℝ} (hub : ∀ c, M.u c ≤ ub)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {VD : Y → ℝ} (hVD : ∀ y, VD y = M.defaultRHS VD y)
    (Vf : (Y → ℝ) → ℝ → Y → ℝ)
    (hVf : ∀ bt b y, M.bell VD (M.price (ue_thr bt)) (Vf bt) b y = Vf bt b y)
    (hVfb : ∀ bt b y, Vf bt b y ≤ ub / (1 - M.β)) :
    ∃ bt : Y → ℝ, (∀ j, 0 ≤ bt j) ∧ ∀ j, M.cutoff VD (M.price (ue_thr bt)) (Vf bt) j = bt j := by
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hρ0 : 0 ≤ (1 + M.r)⁻¹ := inv_nonneg.2 hr1.le
  have hF0 : ∀ bt j, 0 ≤ M.cutoff VD (M.price (ue_thr bt)) (Vf bt) j := fun bt j => by
    have hE : ∀ b y, Vf bt b y = max (VD y) (M.VRsup (M.price (ue_thr bt)) (Vf bt) b y) :=
      fun b y => by rw [← hVf bt b y]; rfl
    have h0 : (0 : ℝ) ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧
        VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) b j} :=
      ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ
        (fun b y _ hb' => M.ue_VRsup_le hub (hVfb bt) b y hb')
        (fun b y => by rw [hE]; exact le_max_left _ _) hVD le_rfl j⟩
    exact le_csSup ⟨M.bmax, fun b hb => hb.2.1⟩ h0
  set G : (Y → ℝ) → Y → ℝ := fun bt =>
    fun j => M.cutoff VD (M.price (ue_thr fun i => max (bt i) 0)) (Vf fun i => max (bt i) 0) j
    with hG
  have hdmax : ∀ a b : Y → ℝ, dist (fun i => max (a i) 0) (fun i => max (b i) 0) ≤ dist a b :=
    fun a b => (dist_pi_le_iff dist_nonneg).2 fun i => by
      rw [Real.dist_eq]
      exact (abs_max_sub_max_le_abs (a i) (b i) 0).trans (by
        rw [← Real.dist_eq]; exact dist_le_pi_dist a b i)
  have hone : ∀ a b : Y → ℝ, ∀ j, G a j ≤ G b j + (1 + M.r)⁻¹ * dist a b := fun a b j => by
    have h1 := M.ue_cutoff_le hu hub hφ hVD (fun i => le_max_right (a i) 0)
      (fun i => le_max_right (b i) 0) (hVf _) (hVfb _) (hVf _) (hVfb _) j
    have h2 := mul_le_mul_of_nonneg_right (hdmax a b) hρ0
    simp only [hG]
    linarith
  have hc : ContractingWith (Real.toNNReal (1 + M.r)⁻¹) G := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hρ0, NNReal.coe_one]
      exact inv_lt_one_of_one_lt₀ (by linarith [M.r_pos])
    · rw [Real.coe_toNNReal _ hρ0]
      refine (dist_pi_le_iff (mul_nonneg hρ0 dist_nonneg)).2 fun j => ?_
      rw [Real.dist_eq, abs_le]
      constructor
      · have h := hone b a j
        rw [dist_comm b a] at h
        linarith
      · linarith [hone a b j]
  set b₀ := ContractingWith.fixedPoint G hc with hb₀
  have hfix : G b₀ = b₀ := hc.fixedPoint_isFixedPt
  have hb0 : ∀ j, 0 ≤ b₀ j := fun j => by
    rw [← hfix]
    exact hF0 _ j
  have hmax : (fun i => max (b₀ i) 0) = b₀ := funext fun i => max_eq_left (hb0 i)
  refine ⟨b₀, hb0, fun j => ?_⟩
  have h := congrFun hfix j
  simp only [hG, hmax] at h
  exact h

/-- **Existence of the optimal borrowing** at the prices induced by nonnegative capacities: the
objective is upper semicontinuous in `B′` (the price `(1 + r)⁻¹ Σ P 1{B′ ≤ b̄}` jumps down,
and `1{B′ ≤ b̄}B′ = min(B′, b̄ 1{B′ ≤ b̄})` for `b̄ ≥ 0`; `V` is continuous in debt), and by
satiation saving beyond `K₀` (enough to consume `c̄` forever) is never better than saving `K₀`,
so the supremum over `B′ ≤ B̄` is a maximum over the compact `[−K₀, B̄]`. -/
theorem ue_attain (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) {VD : Y → ℝ} {bt : Y → ℝ} (hbt : ∀ j, 0 ≤ bt j)
    {V : ℝ → Y → ℝ} (hV : ∀ b y, M.bell VD (M.price (ue_thr bt)) V b y = V b y)
    (hVb : ∀ b y, V b y ≤ M.u cbar / (1 - M.β)) (b : ℝ) (y : Y) :
    ∃ b', b' ≤ M.bmax ∧
      M.obj (M.price (ue_thr bt)) V b y b' = M.VRsup (M.price (ue_thr bt)) V b y := by
  have hub := M.ue_u_le hu hsat
  have h1β : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hE : ∀ b y, V b y = max (VD y) (M.VRsup (M.price (ue_thr bt)) V b y) :=
    fun b y => by rw [← hV b y]; rfl
  have hle : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt)) V b y b' ≤
      M.VRsup (M.price (ue_thr bt)) V b y := fun b y _ hb' => M.ue_VRsup_le hub hVb b y hb'
  have hsup := M.ue_VRsup_sup (M.price (ue_thr bt)) V
  have hqneg : ∀ b' y, b' ≤ 0 → M.price (ue_thr bt) b' y = (1 + M.r)⁻¹ := fun b' y hb' =>
    M.ue_price_one (fun j => ue_thr_nonpos hbt hb' j) y
  -- `V` is continuous in debt
  have hcont : ∀ j, Continuous fun b => V b j := by
    intro j
    have hVR : Continuous fun b => M.VRsup (M.price (ue_thr bt)) V b j := by
      refine Metric.continuous_iff.2 fun b₀ ε hε => ?_
      obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc hsup hle (half_pos hε)
      refine ⟨η, hη, fun b₁ hb₁ => ?_⟩
      rw [Real.dist_eq] at hb₁ ⊢
      have hb₁' := abs_lt.1 hb₁
      rw [abs_lt]
      rcases le_total b₁ b₀ with h | h
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₀ j (b₀ - b₁) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₁ j (b₁ - b₀) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
    have heq : (fun b => V b j) = fun b => max (VD j) (M.VRsup (M.price (ue_thr bt)) V b j) :=
      funext fun b => hE b j
    rw [heq]
    exact continuous_const.max hVR
  -- savings `K₀` give consumption `≥ c̄` forever
  set K₀ := max 0 ((cbar + ‖M.inc‖) * (1 + M.r) / M.r) with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_left _ _
  have hcons : ∀ j, cbar ≤ M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ := fun j => by
    have hj : -‖M.inc‖ ≤ M.inc j := by
      have h1 := norm_le_pi_norm M.inc j
      rw [Real.norm_eq_abs] at h1
      linarith [neg_abs_le (M.inc j)]
    have h2 : (cbar + ‖M.inc‖) * (1 + M.r) / M.r ≤ K₀ := le_max_right _ _
    rw [div_le_iff₀ M.r_pos] at h2
    have h3 : cbar + ‖M.inc‖ ≤ K₀ * M.r / (1 + M.r) := by
      rw [le_div_iff₀ hr1]
      linarith
    have h4 : M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ = M.inc j + K₀ * M.r / (1 + M.r) := by
      field_simp
      ring
    rw [h4]
    linarith
  have hw : ∀ j, M.u cbar / (1 - M.β) ≤ V (-K₀) j := by
    intro j
    have : Nonempty Y := ⟨j⟩
    obtain ⟨j₀, hj₀⟩ := Finite.exists_min fun j => V (-K₀) j
    have hge : ∀ j, M.u cbar + M.β * V (-K₀) j₀ ≤ V (-K₀) j := fun j => by
      have h1 := hle (-K₀) j (-K₀) (by linarith [M.bmax_nonneg])
      have h2 : M.obj (M.price (ue_thr bt)) V (-K₀) j (-K₀) =
          M.u cbar + M.β * ∑ i, M.P j i * V (-K₀) i := by
        unfold obj
        rw [hqneg (-K₀) j (by linarith), hsat _ (hcons j)]
      have h3 := mul_le_mul_of_nonneg_left (ue_le_sum M.markov (fun i => hj₀ i) j) M.β_nonneg
      rw [hE (-K₀) j]
      linarith [le_max_right (VD j) (M.VRsup (M.price (ue_thr bt)) V (-K₀) j)]
    have h5 := hge j₀
    have h6 : M.u cbar / (1 - M.β) ≤ V (-K₀) j₀ := by
      rw [div_le_iff₀ h1β]
      linarith
    exact h6.trans (hj₀ j)
  have hred : ∀ b', b' ≤ -K₀ →
      M.obj (M.price (ue_thr bt)) V b y b' ≤ M.obj (M.price (ue_thr bt)) V b y (-K₀) := by
    intro b' hb'
    unfold obj
    rw [hqneg b' y (by linarith), hqneg (-K₀) y (by linarith)]
    have h1 : M.u (M.inc y - b + (1 + M.r)⁻¹ * b') ≤ M.u (M.inc y - b + (1 + M.r)⁻¹ * -K₀) :=
      hu (by linarith [mul_le_mul_of_nonneg_left hb' (inv_nonneg.2 hr1.le)])
    have h2 : ∑ j, M.P y j * V b' j ≤ ∑ j, M.P y j * V (-K₀) j :=
      ue_sum_mono M.markov (fun j => (hVb b' j).trans (hw j)) y
    nlinarith [mul_le_mul_of_nonneg_left h2 M.β_nonneg]
  -- upper semicontinuity of the objective in `B′`
  have hrev : ∀ b', M.price (ue_thr bt) b' y * b' = (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') := by
    intro b'
    unfold price ue_thr
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 1
    split_ifs with h
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 h), one_mul, inf_eq_left.2 h]
    · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_Iic.1 h')), zero_mul,
        inf_eq_right.2 (by linarith [hbt j, not_le.1 h])]
  have hsc : ∀ (c : ℝ) {f : ℝ → ℝ}, 0 ≤ c → UpperSemicontinuous f →
      UpperSemicontinuous fun x => c * f x := fun c f hc hf =>
    (continuous_const.mul continuous_id).comp_upperSemicontinuous hf
      (fun a b h => mul_le_mul_of_nonneg_left h hc)
  have ht : ∀ j, UpperSemicontinuous fun b' : ℝ =>
      b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b' := fun j =>
    continuous_id.upperSemicontinuous.inf (isClosed_Iic.upperSemicontinuous_indicator (hbt j))
  have hR : UpperSemicontinuous fun b' : ℝ => (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') :=
    hsc _ (inv_nonneg.2 hr1.le)
      (upperSemicontinuous_sum fun j _ => hsc _ (M.markov.nonneg y j) (ht j))
  have hgc : Continuous fun z : ℝ => M.inc y - b + z := continuous_const.add continuous_id
  have hU : UpperSemicontinuous fun b' : ℝ => M.u (M.inc y - b + (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) :=
    (huc.continuous.comp hgc).comp_upperSemicontinuous hR (fun a c h => hu (by linarith))
  have hC : Continuous fun b' : ℝ => M.β * ∑ j, M.P y j * V b' j :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul (hcont j))
  have husc : UpperSemicontinuous fun b' => M.obj (M.price (ue_thr bt)) V b y b' := by
    have heq : (fun b' => M.obj (M.price (ue_thr bt)) V b y b') = fun b' =>
        M.u (M.inc y - b + (1 + M.r)⁻¹ *
          ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) +
        M.β * ∑ j, M.P y j * V b' j := funext fun b' => by
      unfold obj
      rw [hrev b']
    rw [heq]
    exact hU.add hC.upperSemicontinuous
  obtain ⟨bs, hbs, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (⟨0, by linarith, M.bmax_nonneg⟩ : (Set.Icc (-K₀) M.bmax).Nonempty) isCompact_Icc
    (husc.upperSemicontinuousOn _)
  refine ⟨bs, hbs.2, le_antisymm (hle b y bs hbs.2) (ciSup_le fun b'' => ?_)⟩
  rcases le_total (-K₀) (min b'' M.bmax) with h | h
  · exact isMaxOn_iff.1 hmax _ ⟨h, min_le_right _ _⟩
  · exact (hred _ h).trans (isMaxOn_iff.1 hmax _ ⟨le_rfl, by linarith [M.bmax_nonneg]⟩)

/-- **Existence of the Markov perfect equilibrium with one-period debt** (Auclert–Rognlie
2016; Aguiar–Amador 2019; AKMM, p. 901, beyond the text): with `u` nondecreasing, uniformly
continuous and satiated, `φ ≥ 0` and `r > 0`, an equilibrium exists. The prices are those of
the fixed-point capacities `b̄` (`ue_capacity_fixed`): `q(B′, Y) = (1 + r)⁻¹ Pr(B′ ≤ b̄(Y′))`. -/
theorem ue_mpe_exists (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) :
    ∃ (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ), IsOneMPE M V VR VD D Bh q := by
  have hub := M.ue_u_le hu hsat
  obtain ⟨VD, hVD, hVDle⟩ := M.ue_VD_exists hub
  have hsol := fun bt : Y → ℝ => M.ue_sol_exists hub hVDle (M.price (ue_thr bt))
  choose Vf hVf hVfb using hsol
  obtain ⟨bt, hbt0, hbt⟩ := M.ue_capacity_fixed hu hub hφ hVD Vf hVf
    (fun bt b y => (hVfb bt b y).2)
  have hVb : ∀ b y, Vf bt b y ≤ M.u cbar / (1 - M.β) := fun b y => (hVfb bt b y).2
  have hE : ∀ b y, Vf bt b y = max (VD y) (M.VRsup (M.price (ue_thr bt)) (Vf bt) b y) :=
    fun b y => by rw [← hVf bt b y]; rfl
  have hle : ∀ b y b', b' ≤ M.bmax → M.obj (M.price (ue_thr bt)) (Vf bt) b y b' ≤
      M.VRsup (M.price (ue_thr bt)) (Vf bt) b y := fun b y _ hb' => M.ue_VRsup_le hub hVb b y hb'
  have hsup := M.ue_VRsup_sup (M.price (ue_thr bt)) (Vf bt)
  have hatt := M.ue_attain hu huc hsat hbt0 (hVf bt) hVb
  choose Bh hBh hBhopt using hatt
  have hiff : ∀ b' j, b' ≤ M.bmax →
      (b' ≤ bt j ↔ VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) b' j) := by
    intro b' j hb'
    set S := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) b j}
      with hS
    have hbtS : bt j = sSup S := (hbt j).symm
    have hbdd : BddAbove S := ⟨M.bmax, fun b hb => hb.2.1⟩
    have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hle
      (fun b y => by rw [hE]; exact le_max_left _ _) hVD le_rfl j⟩
    constructor
    · intro h
      have hclosed : VD j ≤ M.VRsup (M.price (ue_thr bt)) (Vf bt) (bt j) j := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc hsup hle hε
        obtain ⟨s, hs, hslt⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩
          (by linarith : sSup S - η < sSup S)
        have hsle : s ≤ sSup S := le_csSup hbdd hs
        have h1 := hmod (sSup S) j (sSup S - s) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h1
        rw [hbtS]
        linarith [hs.2.2]
      exact hclosed.trans (M.ue_VR_antitone hu hsup hle h j)
    · intro h
      rcases le_total b' 0 with h0 | h0
      · exact h0.trans (hbt0 j)
      · rw [hbtS]
        exact le_csSup hbdd ⟨h0, hb', h⟩
  refine ⟨Vf bt, M.VRsup (M.price (ue_thr bt)) (Vf bt), VD,
    fun b y => if M.VRsup (M.price (ue_thr bt)) (Vf bt) b y < VD y then 1 else 0, Bh,
    M.price (ue_thr bt), ?_⟩
  exact { bdd := ⟨_, hVb⟩
          eq_24_9 := hE
          eq_24_10 := hVD
          eq_24_11 := hle
          eq_24_12 := fun b' y hb' => by
            have hp : M.price (ue_thr bt) b' y =
                (1 + M.r)⁻¹ * ∑ j, M.P y j * ue_thr bt b' j := rfl
            rw [hp]
            congr 1
            refine sum_congr rfl fun j _ => ?_
            congr 1
            have hj := hiff b' j hb'
            have ht1 : ue_thr bt b' j = if b' ≤ bt j then 1 else 0 := rfl
            rw [ht1]
            split_ifs with h1 h2 h2
            · exact absurd (hj.1 h1) (not_le.2 h2)
            · norm_num
            · norm_num
            · exact absurd (hj.2 (not_lt.1 h2)) h1
          default_opt := fun _ _ => rfl
          borrow_le := hBh
          borrow_opt := hBhopt }

/-- **Existence and uniqueness** (AKMM, p. 901, beyond the text): under the hypotheses of
`ue_mpe_exists` there is a Markov perfect equilibrium, and all equilibria share their value
functions, default rule and prices (`ue_mpe_unique`). -/
theorem ue_mpe_exists_unique (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) :
    (∃ (V VR : ℝ → Y → ℝ) (VD : Y → ℝ) (D Bh q : ℝ → Y → ℝ), IsOneMPE M V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Y → ℝ} {VD₁ VD₂ : Y → ℝ},
        IsOneMPE M V₁ VR₁ VD₁ D₁ Bh₁ q₁ → IsOneMPE M V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧
          ∀ b' y, b' ≤ M.bmax → q₁ b' y = q₂ b' y :=
  ⟨M.ue_mpe_exists hu huc hsat hφ, fun h₁ h₂ => M.ue_mpe_unique hu huc hφ h₁ h₂⟩

end UEModel

/-- A concrete economy satisfying every hypothesis of `ue_mpe_exists_unique`: income `1` or `2`
(`false`, `true`), i.i.d. with probability `1/2`; utility `u(c) = min(c, 3)` (nondecreasing,
1-Lipschitz, satiated at `c̄ = 3`); default cost `φ(Y) = Y/4`; `β = 1/2`, `r = 1/4` and the
borrowing limit `B̄ = 1`. -/
noncomputable def ue_example : UEModel Bool where
  inc := fun y => if y then 2 else 1
  P := fun _ _ => 1 / 2
  markov := ⟨fun _ _ => by norm_num, fun _ => by rw [Fintype.sum_bool]; norm_num⟩
  u := fun c => min c 3
  φ := fun Yc => Yc / 4
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  r := 1 / 4
  r_pos := by norm_num
  bmax := 1
  bmax_nonneg := zero_le_one

/-- The example meets the hypotheses: `u` nondecreasing, uniformly continuous and satiated at
`3`, `φ ≥ 0`. -/
theorem ue_example_hyp : Monotone ue_example.u ∧ UniformContinuous ue_example.u ∧
    (∀ c, 3 ≤ c → ue_example.u c = ue_example.u 3) ∧
    ∀ y, 0 ≤ ue_example.φ (ue_example.inc y) := by
  refine ⟨fun a b h => min_le_min_right 3 h, (LipschitzWith.id.min_const 3).uniformContinuous,
    fun c hc => ?_, fun y => ?_⟩
  · change min c 3 = min 3 3
    rw [min_eq_right hc, min_self]
  · change 0 ≤ (if y then (2 : ℝ) else 1) / 4
    split_ifs <;> norm_num

/-- **The example has a Markov perfect equilibrium, and it is unique** (in values, default
rule and prices): `ue_mpe_exists_unique` is not vacuous. -/
theorem ue_example_exists_unique :
    (∃ (V VR : ℝ → Bool → ℝ) (VD : Bool → ℝ) (D Bh q : ℝ → Bool → ℝ),
      IsOneMPE ue_example V VR VD D Bh q) ∧
      ∀ {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℝ → Bool → ℝ} {VD₁ VD₂ : Bool → ℝ},
        IsOneMPE ue_example V₁ VR₁ VD₁ D₁ Bh₁ q₁ → IsOneMPE ue_example V₂ VR₂ VD₂ D₂ Bh₂ q₂ →
        V₁ = V₂ ∧ VR₁ = VR₂ ∧ VD₁ = VD₂ ∧ D₁ = D₂ ∧
          ∀ b' y, b' ≤ ue_example.bmax → q₁ b' y = q₂ b' y := by
  obtain ⟨h1, h2, h3, h4⟩ := ue_example_hyp
  exact ue_example.ue_mpe_exists_unique h1 h2 h3 h4

end AKMM.SovereignDefault
