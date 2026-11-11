import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Convex.Topology
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The repeated game: stage game, histories, strategies, discounted payoffs

Miao, Chapter 21 introduction and §21.1.1, pp. 737–741. The stage game is `G = {N, A, u}`:
players `i : ι`, action sets `A i`, action profiles `rg_Prof A = ∀ i, A i`, and a payoff map
`u : rg_Prof A → ι → ℝ` (`u a i` is player `i`'s payoff `uᵢ(a)`). Assumption 21.1.1 (bounded
payoffs; finite or compact action sets with continuous payoffs) is carried as explicit
hypotheses: `hM : ∀ a j, |u a j| ≤ M` here, finiteness or compactness and continuity in the
modules that need them.

* A history `hᵗ = (a₁, …, a_{t−1})` is a list of past action profiles, stored newest first
  (`rg_Hist A`); the initial history is `[]`. A pure strategy profile is a map from histories to
  action profiles (`rg_Strat A`); player `i`'s component is `fun h => σ h i`.
* `rg_hist σ t` is the history after `t` periods of play, `rg_path σ t = a_{t+1}(σ)` the
  action profile of period `t + 1` (time is indexed from `0` here, from `1` in the book).
* `rg_cont σ h` is the continuation profile `σ|h` of the subgame after `h`; `rg_dev σ i τ`
  replaces player `i`'s strategy by `τ`.
* `rg_pathPay δ u q = (1 − δ) Σₜ δᵗ u(qₜ)` and `rg_U δ u σ = U(σ)`, the discounted average payoff.

Proved: the recursion `U(σ|h) = (1 − δ) u(σ(h)) + δ U(σ|(σ(h), h))` (`rg_U_cont_rec`), the
subgame payoff formula of p. 741 (`rg_U_subgame`), and the bounds `|U| ≤ M` and
`m ≤ U ≤ M'` for payoffs between `m` and `M'`.
-/

namespace Miao.DynamicGames

variable {ι : Type*} {A : ι → Type*}

/-- Action profiles `a = (a₁, …, aₙ) ∈ A = ×ᵢ Aᵢ` (Miao, p. 739). -/
abbrev rg_Prof (A : ι → Type*) := ∀ i, A i

/-- Histories `hᵗ ∈ Hᵗ = A^{t−1}` (Miao, p. 740), stored newest first: after `hᵗ` and the profile
`aₜ` the history is `aₜ :: hᵗ`. -/
abbrev rg_Hist (A : ι → Type*) := List (rg_Prof A)

/-- Pure strategy profiles `σ = (σ¹, …, σⁿ)` (Miao, p. 740): each `σⁱ` maps histories to `Aᵢ`. -/
abbrev rg_Strat (A : ι → Type*) := rg_Hist A → rg_Prof A

open Classical in
/-- The profile `(a'ᵢ, a₋ᵢ)`: player `i`'s action replaced by `x`. -/
noncomputable def rg_upd (a : rg_Prof A) (i : ι) (x : A i) : rg_Prof A := Function.update a i x

/-- `rg_upd` is `Function.update` for any decidable equality on players. -/
theorem rg_upd_eq [DecidableEq ι] (a : rg_Prof A) (i : ι) (x : A i) :
    rg_upd a i x = Function.update a i x := by
  unfold rg_upd
  congr
  exact Subsingleton.elim _ _

/-- `(a'ᵢ, a₋ᵢ)ᵢ = a'ᵢ`. -/
theorem rg_upd_self (a : rg_Prof A) (i : ι) (x : A i) : rg_upd a i x i = x := by
  classical
  rw [rg_upd_eq]
  exact Function.update_self i x a

/-- `(a'ᵢ, a₋ᵢ)ⱼ = aⱼ` for `j ≠ i`. -/
theorem rg_upd_ne (a : rg_Prof A) {i j : ι} (x : A i) (h : j ≠ i) : rg_upd a i x j = a j := by
  classical
  rw [rg_upd_eq]
  exact Function.update_of_ne h x a

/-- `(aᵢ, a₋ᵢ) = a`. -/
theorem rg_upd_eq_self (a : rg_Prof A) (i : ι) : rg_upd a i (a i) = a := by
  classical
  rw [rg_upd_eq]
  exact Function.update_eq_self i a

/-- A unilateral deviation by `i` that changes the profile is a deviation by `i` only: if
`(x, a₋ⱼ) = (y, a₋ᵢ) ≠ a` then `i = j`. -/
theorem rg_upd_player_eq (a : rg_Prof A) {i j : ι} (x : A j) (y : A i)
    (h : rg_upd a j x = rg_upd a i y) (hne : rg_upd a j x ≠ a) : i = j := by
  by_contra hij
  apply hne
  have hx : x = a j := by
    have := congrFun h j
    rw [rg_upd_self, rg_upd_ne a y (Ne.symm hij)] at this
    exact this
  rw [hx, rg_upd_eq_self]

/-- The continuation profile `σ|h` of the subgame after `h` (Miao, p. 740):
`σ|h(h') = σ(h, h')`. -/
def rg_cont (σ : rg_Strat A) (h : rg_Hist A) : rg_Strat A := fun h' => σ (h' ++ h)

/-- The profile `(τ, σ₋ᵢ)`: player `i` uses `τ`, the others follow `σ`. -/
noncomputable def rg_dev (σ : rg_Strat A) (i : ι) (τ : rg_Hist A → A i) : rg_Strat A :=
  fun h => rg_upd (σ h) i (τ h)

/-- The history after `t` periods of play of `σ`, `hᵗ⁺¹ = (a₁(σ), …, aₜ(σ))` (Miao, p. 740). -/
def rg_hist (σ : rg_Strat A) : ℕ → rg_Hist A
  | 0 => []
  | t + 1 => σ (rg_hist σ t) :: rg_hist σ t

/-- The path `{aₜ(σ)}` generated by `σ` (Miao, p. 740): `rg_path σ t = a_{t+1}(σ)`. -/
def rg_path (σ : rg_Strat A) (t : ℕ) : rg_Prof A := σ (rg_hist σ t)

/-- The discounted average payoff `(1 − δ) Σₜ δᵗ u(qₜ)` of a path `q`. -/
noncomputable def rg_pathPay (δ : ℝ) (u : rg_Prof A → ι → ℝ) (q : ℕ → rg_Prof A) :
    ι → ℝ :=
  fun j => (1 - δ) * ∑' t, δ ^ t * u (q t) j

/-- The discounted average payoff `Uᵢ(σ) = (1 − δ) Σ_{t ≥ 1} δ^{t−1} uᵢ(aₜ(σ))` (Miao, p. 740). -/
noncomputable def rg_U (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) : ι → ℝ :=
  rg_pathPay δ u (rg_path σ)

/-- `σ|∅ = σ`. -/
theorem rg_cont_nil (σ : rg_Strat A) : rg_cont σ [] = σ := by
  funext h
  simp [rg_cont]

/-- `(σ|h)|h' = σ|(h, h')`. -/
theorem rg_cont_cont (σ : rg_Strat A) (h h' : rg_Hist A) :
    rg_cont (rg_cont σ h) h' = rg_cont σ (h' ++ h) := by
  funext h''
  simp [rg_cont, List.append_assoc]

/-- `(τ, σ₋ᵢ)|h = (τ|h, σ₋ᵢ|h)`. -/
theorem rg_cont_dev (σ : rg_Strat A) (i : ι) (τ : rg_Hist A → A i) (h : rg_Hist A) :
    rg_cont (rg_dev σ i τ) h = rg_dev (rg_cont σ h) i (fun h' => τ (h' ++ h)) := rfl

/-- Deviating to one's own strategy changes nothing. -/
theorem rg_dev_self (σ : rg_Strat A) (i : ι) : rg_dev σ i (fun h => σ h i) = σ := by
  funext h
  exact rg_upd_eq_self (σ h) i

/-- Play in the subgame after a history `hᵗ` on the path of `σ` continues the path of `σ`. -/
theorem rg_hist_cont (σ : rg_Strat A) (t s : ℕ) :
    rg_hist (rg_cont σ (rg_hist σ t)) s ++ rg_hist σ t = rg_hist σ (t + s) := by
  induction s with
  | zero => simp [rg_hist]
  | succ s ih =>
    change rg_cont σ (rg_hist σ t) (rg_hist (rg_cont σ (rg_hist σ t)) s) ::
        (rg_hist (rg_cont σ (rg_hist σ t)) s ++ rg_hist σ t) =
      σ (rg_hist σ (t + s)) :: rg_hist σ (t + s)
    simp only [rg_cont, ih]

/-- The path of `σ|hᵗ` for `hᵗ` on the path of `σ` is `{aₛ(σ)}_{s ≥ t}`. -/
theorem rg_path_cont (σ : rg_Strat A) (t s : ℕ) :
    rg_path (rg_cont σ (rg_hist σ t)) s = rg_path σ (t + s) := by
  simp only [rg_path, rg_cont, rg_hist_cont]

/-- Bounded stage payoffs make the discounted sums summable. -/
theorem rg_summable {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (q : ℕ → rg_Prof A) (j : ι) : Summable (fun t => δ ^ t * u (q t) j) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
  exact mul_le_mul_of_nonneg_left (hM _ _) (pow_nonneg hδ0 t)

/-- The recursion of a path payoff:
`(1 − δ) Σ δᵗ u(qₜ) = (1 − δ) u(q₀) + δ (1 − δ) Σ δᵗ u(qₜ₊₁)`. -/
theorem rg_pathPay_succ {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : ℕ → rg_Prof A) (j : ι) :
    rg_pathPay δ u q j =
      (1 - δ) * u (q 0) j + δ * rg_pathPay δ u (fun t => q (t + 1)) j := by
  unfold rg_pathPay
  rw [(rg_summable hM hδ0 hδ1 q j).tsum_eq_zero_add]
  have : ∀ t : ℕ, δ ^ (t + 1) * u (q (t + 1)) j = δ * (δ ^ t * u (q (t + 1)) j) := by
    intro t
    ring
  simp only [this, tsum_mul_left, pow_zero, one_mul]
  ring

/-- Path payoffs between `m` and `M'`: if `m ≤ u(qₜ)ⱼ ≤ M'` for all `t` then
`m ≤ (1 − δ) Σ δᵗ u(qₜ)ⱼ ≤ M'`. -/
theorem rg_pathPay_mem {δ M m M' : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : ℕ → rg_Prof A) (j : ι) (hm : ∀ t, m ≤ u (q t) j)
    (hM' : ∀ t, u (q t) j ≤ M') : m ≤ rg_pathPay δ u q j ∧ rg_pathPay δ u q j ≤ M' := by
  have hg := summable_geometric_of_lt_one hδ0 hδ1
  have hs := rg_summable hM hδ0 hδ1 q j
  have h1 : 0 < 1 - δ := by linarith
  have hgeo : ∀ c : ℝ, (1 - δ) * ∑' t : ℕ, δ ^ t * c = c := by
    intro c
    rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
    field_simp
  unfold rg_pathPay
  constructor
  · calc m = (1 - δ) * ∑' t : ℕ, δ ^ t * m := (hgeo m).symm
      _ ≤ (1 - δ) * ∑' t, δ ^ t * u (q t) j := by
        refine mul_le_mul_of_nonneg_left ?_ h1.le
        exact (hg.mul_right m).tsum_le_tsum
          (fun t => mul_le_mul_of_nonneg_left (hm t) (pow_nonneg hδ0 t)) hs
  · calc (1 - δ) * ∑' t, δ ^ t * u (q t) j ≤ (1 - δ) * ∑' t : ℕ, δ ^ t * M' := by
          refine mul_le_mul_of_nonneg_left ?_ h1.le
          exact hs.tsum_le_tsum
            (fun t => mul_le_mul_of_nonneg_left (hM' t) (pow_nonneg hδ0 t)) (hg.mul_right M')
      _ = M' := hgeo M'

/-- `|(1 − δ) Σ δᵗ u(qₜ)ⱼ| ≤ M` when `|u| ≤ M`. -/
theorem rg_abs_pathPay_le {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : ℕ → rg_Prof A) (j : ι) : |rg_pathPay δ u q j| ≤ M := by
  obtain ⟨h1, h2⟩ := rg_pathPay_mem hM hδ0 hδ1 q j (fun t => (abs_le.1 (hM (q t) j)).1)
    (fun t => (abs_le.1 (hM (q t) j)).2)
  exact abs_le.2 ⟨h1, h2⟩

/-- `|Uⱼ(σ)| ≤ M` when `|u| ≤ M`. -/
theorem rg_abs_U_le {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (j : ι) : |rg_U δ u σ j| ≤ M :=
  rg_abs_pathPay_le hM hδ0 hδ1 _ j

/-- The recursion `U(σ) = (1 − δ) u(a₁(σ)) + δ U(σ|a₁(σ))`. -/
theorem rg_U_rec {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (σ : rg_Strat A) (j : ι) :
    rg_U δ u σ j = (1 - δ) * u (σ []) j + δ * rg_U δ u (rg_cont σ [σ []]) j := by
  unfold rg_U
  rw [rg_pathPay_succ hM hδ0 hδ1]
  have h1 : rg_hist σ 1 = [σ []] := rfl
  have : (fun t => rg_path σ (t + 1)) = rg_path (rg_cont σ [σ []]) := by
    funext t
    rw [← h1, rg_path_cont, Nat.add_comm]
  rw [this]
  rfl

/-- The recursion in a subgame: `U(σ|h) = (1 − δ) u(σ(h)) + δ U(σ|(h, σ(h)))`. -/
theorem rg_U_cont_rec {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (h : rg_Hist A) (j : ι) :
    rg_U δ u (rg_cont σ h) j =
      (1 - δ) * u (σ h) j + δ * rg_U δ u (rg_cont σ (σ h :: h)) j := by
  rw [rg_U_rec hM hδ0 hδ1, rg_cont_cont]
  rfl

/-- Miao, p. 741: the payoff for the subgame after the history `hᵗ` of `σ` is
`Uᵢ(σ|hᵗ) = (1 − δ) Σ_{s ≥ t} δ^{s−t} uᵢ(aₛ(σ))`. -/
theorem rg_U_subgame (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) (t : ℕ) :
    rg_U δ u (rg_cont σ (rg_hist σ t)) = rg_pathPay δ u (fun s => rg_path σ (t + s)) := by
  unfold rg_U
  congr 1
  funext s
  exact rg_path_cont σ t s

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Subgame perfection and the one-shot deviation principle

Miao, §21.1.1, pp. 740–742: Definition 21.1.1 (subgame perfect equilibrium), Definition 21.1.2
(one-shot deviations) and Proposition 21.1.1 (the one-shot deviation principle), for pure
strategies, bounded stage payoffs `|u| ≤ M` and `0 ≤ δ < 1`.

* `rg_IsSPE δ u σ`: for every history `h`, `σ|h` is a Nash equilibrium of the subgame
  (Definition 21.1.1). Every continuation of an SPE is an SPE (`rg_isSPE_cont`), the remark
  "every subgame is completely identical to the original game" of p. 741.
* `rg_IsOneShotDev σ i h̄ τ`, `rg_IsProfitable δ u σ i h̄ τ` (Definition 21.1.2), and the value
  `(1 − δ) u(a'ᵢ, σ₋ᵢ(h̄)) + δ U(σ|(h̄, (a'ᵢ, σ₋ᵢ(h̄))))` of a one-shot deviation
  (`definition_21_1_2`).
* `proposition_21_1_1`: `σ` is an SPE iff there is no profitable one-shot deviation.

Departure: the book's proof sketch (finite deviations by induction, then truncation) is
replaced by the equivalent bound "the gain of any deviation in any subgame is at most
`2Mδⁿ` for every `n`", proved by induction on `n`.
-/

namespace Miao.DynamicGames

open Filter Topology

variable {ι : Type*} {A : ι → Type*}

/-- **Definition 21.1.1** (Miao, p. 741): `σ` is a subgame perfect equilibrium if, for every
history `h`, `σ|h` is a Nash equilibrium of the subgame after `h`:
`Uᵢ(σ|h) ≥ Uᵢ(τ, σ₋ᵢ|h)` for every strategy `τ` of every player `i`. -/
def rg_IsSPE (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) : Prop :=
  ∀ (h : rg_Hist A) (i : ι) (τ : rg_Hist A → A i),
    rg_U δ u (rg_dev (rg_cont σ h) i τ) i ≤ rg_U δ u (rg_cont σ h) i

/-- **Definition 21.1.1** (Miao, p. 741), unfolded. -/
theorem definition_21_1_1 (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) :
    rg_IsSPE δ u σ ↔ ∀ (h : rg_Hist A) (i : ι) (τ : rg_Hist A → A i),
      rg_U δ u (rg_dev (rg_cont σ h) i τ) i ≤ rg_U δ u (rg_cont σ h) i := Iff.rfl

/-- Miao, p. 741: every subgame is identical to the original game, so the continuation
`σ|h` of an SPE is an SPE. -/
theorem rg_isSPE_cont {δ : ℝ} {u : rg_Prof A → ι → ℝ} {σ : rg_Strat A} (hσ : rg_IsSPE δ u σ)
    (h : rg_Hist A) : rg_IsSPE δ u (rg_cont σ h) := by
  intro h' i τ
  rw [rg_cont_cont]
  exact hσ (h' ++ h) i τ

/-- Definition 21.1.2 (Miao, p. 741): `τ` is a one-shot deviation of player `i` from `σ` at
`h̄`: it differs from `σⁱ` at `h̄` and only there. -/
def rg_IsOneShotDev (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) (τ : rg_Hist A → A i) : Prop :=
  τ hbar ≠ σ hbar i ∧ ∀ h, h ≠ hbar → τ h = σ h i

/-- Definition 21.1.2 (Miao, p. 741): the one-shot deviation `τ` is profitable if
`Uᵢ(τ|h̄, σ₋ᵢ|h̄) > Uᵢ(σ|h̄)`. -/
def rg_IsProfitable (δ : ℝ) (u : rg_Prof A → ι → ℝ) (σ : rg_Strat A) (i : ι)
    (hbar : rg_Hist A) (τ : rg_Hist A → A i) : Prop :=
  rg_U δ u (rg_cont σ hbar) i < rg_U δ u (rg_cont (rg_dev σ i τ) hbar) i

open Classical in
/-- The strategy of player `i` that plays `x` at `h̄` and follows `σ` elsewhere. -/
noncomputable def rg_oneShot (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) (x : A i) :
    rg_Hist A → A i :=
  fun h => if h = hbar then x else σ h i

/-- `rg_oneShot σ i h̄ x` is a one-shot deviation when `x ≠ σⁱ(h̄)`. -/
theorem rg_oneShot_isOneShotDev (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) {x : A i}
    (hx : x ≠ σ hbar i) : rg_IsOneShotDev σ i hbar (rg_oneShot σ i hbar x) := by
  refine ⟨?_, fun h hh => ?_⟩
  · simpa [rg_oneShot] using hx
  · simp [rg_oneShot, hh]

/-- A strategy that agrees with `σⁱ` at every history strictly longer than `h̄` does not change
the continuation after `(h̄, b)`. -/
theorem rg_cont_dev_after {σ : rg_Strat A} {i : ι} {hbar : rg_Hist A} {τ : rg_Hist A → A i}
    (hτ : ∀ h, h ≠ hbar → τ h = σ h i) (b : rg_Prof A) :
    rg_cont (rg_dev σ i τ) (b :: hbar) = rg_cont σ (b :: hbar) := by
  funext h'
  have hne : h' ++ b :: hbar ≠ hbar := by
    intro heq
    have := congrArg List.length heq
    simp at this
    omega
  simp only [rg_cont, rg_dev, hτ _ hne, rg_upd_eq_self]

/-- **Definition 21.1.2** (Miao, p. 741): the payoff of a strategy `τ` that differs from `σⁱ`
at most at `h̄` (in particular of a one-shot deviation), in the subgame after `h̄`:
`U(τ|h̄, σ₋ᵢ|h̄) = (1 − δ) u(b) + δ U(σ|(h̄, b))` with `b = (τ(h̄), σ₋ᵢ(h̄))`. -/
theorem definition_21_1_2 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A)
    (τ : rg_Hist A → A i) (hτ : ∀ h, h ≠ hbar → τ h = σ h i) (j : ι) :
    rg_U δ u (rg_cont (rg_dev σ i τ) hbar) j =
      (1 - δ) * u (rg_upd (σ hbar) i (τ hbar)) j +
        δ * rg_U δ u (rg_cont σ (rg_upd (σ hbar) i (τ hbar) :: hbar)) j := by
  rw [rg_U_cont_rec hM hδ0 hδ1]
  have hb : rg_dev σ i τ hbar = rg_upd (σ hbar) i (τ hbar) := rfl
  rw [hb, rg_cont_dev_after hτ]

/-- The value of the strategy `rg_oneShot σ i h̄ x` in the subgame after `h̄`. -/
theorem rg_oneShot_value {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (i : ι) (hbar : rg_Hist A) (x : A i)
    (j : ι) :
    rg_U δ u (rg_cont (rg_dev σ i (rg_oneShot σ i hbar x)) hbar) j =
      (1 - δ) * u (rg_upd (σ hbar) i x) j +
        δ * rg_U δ u (rg_cont σ (rg_upd (σ hbar) i x :: hbar)) j := by
  have h1 := definition_21_1_2 hM hδ0 hδ1 σ i hbar (rg_oneShot σ i hbar x)
    (fun h hh => by simp [rg_oneShot, hh]) j
  have h2 : rg_oneShot σ i hbar x hbar = x := by simp [rg_oneShot]
  rw [h1, h2]

/-- In an SPE no single-period deviation `x` at any history `h̄` pays:
`(1 − δ) uᵢ(x, σ₋ᵢ(h̄)) + δ Uᵢ(σ|(h̄, (x, σ₋ᵢ(h̄)))) ≤ Uᵢ(σ|h̄)`. -/
theorem rg_oneShot_le_of_isSPE {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : rg_Strat A} (hσ : rg_IsSPE δ u σ) (i : ι)
    (hbar : rg_Hist A) (x : A i) :
    (1 - δ) * u (rg_upd (σ hbar) i x) i +
        δ * rg_U δ u (rg_cont σ (rg_upd (σ hbar) i x :: hbar)) i ≤
      rg_U δ u (rg_cont σ hbar) i := by
  rw [← rg_oneShot_value hM hδ0 hδ1, rg_cont_dev]
  exact hσ hbar i _

/-- The gain from any deviation in any subgame is at most `2Mδⁿ`, for every `n`, when no
one-shot deviation is profitable. -/
theorem rg_gain_le_of_noOneShot {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : rg_Strat A} (i : ι)
    (hno : ∀ hbar τ, rg_IsOneShotDev σ i hbar τ → ¬ rg_IsProfitable δ u σ i hbar τ) (n : ℕ) :
    ∀ (h : rg_Hist A) (τ : rg_Hist A → A i),
      rg_U δ u (rg_dev (rg_cont σ h) i τ) i - rg_U δ u (rg_cont σ h) i ≤ 2 * M * δ ^ n := by
  induction n with
  | zero =>
    intro h τ
    have h1 := abs_le.1 (rg_abs_U_le hM hδ0 hδ1 (rg_dev (rg_cont σ h) i τ) i)
    have h2 := abs_le.1 (rg_abs_U_le hM hδ0 hδ1 (rg_cont σ h) i)
    simp only [pow_zero, mul_one]
    linarith [h1.2, h2.1]
  | succ n ih =>
    intro h τ
    set b := rg_upd (σ h) i (τ []) with hb
    have hrec := rg_U_rec hM hδ0 hδ1 (rg_dev (rg_cont σ h) i τ) i
    have h0 : rg_dev (rg_cont σ h) i τ [] = b := rfl
    have hc : rg_cont (rg_dev (rg_cont σ h) i τ) [b] =
        rg_dev (rg_cont σ (b :: h)) i (fun h' => τ (h' ++ [b])) := by
      rw [rg_cont_dev, rg_cont_cont]
      rfl
    rw [h0, hc] at hrec
    have hih := ih (b :: h) (fun h' => τ (h' ++ [b]))
    -- the one-shot deviation to `τ []` at `h` is not profitable
    have hone : (1 - δ) * u b i + δ * rg_U δ u (rg_cont σ (b :: h)) i ≤
        rg_U δ u (rg_cont σ h) i := by
      by_cases hx : τ [] = σ h i
      · have hbσ : b = σ h := by rw [hb, hx, rg_upd_eq_self]
        rw [hbσ, rg_U_cont_rec hM hδ0 hδ1 σ h i]
      · have hnp := hno h _ (rg_oneShot_isOneShotDev σ i h hx)
        unfold rg_IsProfitable at hnp
        rw [rg_oneShot_value hM hδ0 hδ1] at hnp
        exact not_lt.1 hnp
    have : δ * rg_U δ u (rg_dev (rg_cont σ (b :: h)) i (fun h' => τ (h' ++ [b]))) i ≤
        δ * (rg_U δ u (rg_cont σ (b :: h)) i + 2 * M * δ ^ n) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0
    rw [hrec, pow_succ]
    nlinarith

/-- **Proposition 21.1.1** (One-shot deviation principle, Miao, p. 741). With bounded stage
payoffs and `0 ≤ δ < 1`, `σ` is a subgame perfect equilibrium iff no player has a profitable
one-shot deviation from `σ`. -/
theorem proposition_21_1_1 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) :
    rg_IsSPE δ u σ ↔
      ∀ i hbar τ, rg_IsOneShotDev σ i hbar τ → ¬ rg_IsProfitable δ u σ i hbar τ := by
  constructor
  · intro hσ i hbar τ _ hp
    unfold rg_IsProfitable at hp
    rw [rg_cont_dev] at hp
    exact absurd (hσ hbar i _) (not_le.2 hp)
  · intro hno h i τ
    have hlim : Tendsto (fun n : ℕ => 2 * M * δ ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).const_mul (2 * M)
    have := ge_of_tendsto' hlim (fun n => rg_gain_le_of_noOneShot hM hδ0 hδ1 i (hno i) n h τ)
    linarith

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The equilibrium payoff set and the APS operator `B`

Miao, §21.1.2, pp. 742–744: Definitions 21.1.3–21.1.4, Lemmas 21.1.1–21.1.2, Theorem 21.1.1 and
the recursive representation of SPE payoffs below it, and Lemma 21.1.3 (§21.1.3, p. 746).

* `rg_V δ u`: the set `V` of (pure-strategy) SPE payoffs.
* `rg_Admissible δ u W a w` (Definition 21.1.3) and `rg_B δ u W` (Definition 21.1.4).
* `lemma_21_1_1`: `V ⊆ B(V)` (its proof is the one-shot game `{N, A, u^w}` of p. 742 with
  `w(a) = U(σ*|a)`).
* `lemma_21_1_2` (self-generation): a bounded `W ⊆ B(W)` has `B(W) ⊆ V`. The strategy of the
  proof is built from choice functions `g, nx` by the state recursion `v₁ = v`,
  `v_{t+1} = nx(vₜ, aₜ)`, `aₜ = g(vₜ)` (`rg_state`, `rg_recStrat`, `rg_recStrat_spec`).
* `theorem_21_1_1` (factorization): `V = B(V)`; `theorem_21_1_1_recursive`: every SPE payoff is
  generated by such a recursive strategy with states in `V`.
* `lemma_21_1_3`: `B` is monotone.

"Bounded" for a set `W ⊆ ℝⁿ` is `rg_Bdd W`: one bound on all coordinates of all points.
-/

namespace Miao.DynamicGames

variable {ι : Type*} {A : ι → Type*}

/-- The set `V` of subgame perfect equilibrium payoffs (Miao, p. 742). -/
def rg_V (δ : ℝ) (u : rg_Prof A → ι → ℝ) : Set (ι → ℝ) :=
  {v | ∃ σ : rg_Strat A, rg_IsSPE δ u σ ∧ rg_U δ u σ = v}

/-- Definition 21.1.3 (Miao, p. 742): `(a, w)` is admissible with respect to `W` if `w` maps
`A` into `W` and `a` is a Nash equilibrium of the game `{N, A, u^w}`,
`u^w = (1 − δ) u + δ w`. -/
def rg_Admissible (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) (a : rg_Prof A)
    (w : rg_Prof A → ι → ℝ) : Prop :=
  (∀ a', w a' ∈ W) ∧ ∀ (i : ι) (x : A i),
    (1 - δ) * u (rg_upd a i x) i + δ * w (rg_upd a i x) i ≤ (1 - δ) * u a i + δ * w a i

/-- Definition 21.1.4 (Miao, pp. 742–743): `B(W)` is the set of `v = (1 − δ) u(a) + δ w(a)` for
pairs `(a, w)` admissible with respect to `W`. -/
def rg_B (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | ∃ a w, rg_Admissible δ u W a w ∧ v = fun j => (1 - δ) * u a j + δ * w a j}

/-- **Definition 21.1.3** (Miao, p. 742), unfolded. -/
theorem definition_21_1_3 (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) (a : rg_Prof A)
    (w : rg_Prof A → ι → ℝ) :
    rg_Admissible δ u W a w ↔ (∀ a', w a' ∈ W) ∧ ∀ (i : ι) (x : A i),
      (1 - δ) * u (rg_upd a i x) i + δ * w (rg_upd a i x) i ≤
        (1 - δ) * u a i + δ * w a i := Iff.rfl

/-- **Definition 21.1.4** (Miao, pp. 742–743), unfolded. -/
theorem definition_21_1_4 (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) (v : ι → ℝ) :
    v ∈ rg_B δ u W ↔
      ∃ a w, rg_Admissible δ u W a w ∧ v = fun j => (1 - δ) * u a j + δ * w a j := Iff.rfl

/-- A set `W ⊆ ℝⁿ` is bounded: one bound on all coordinates of all its points. -/
def rg_Bdd (W : Set (ι → ℝ)) : Prop := ∃ K, ∀ x ∈ W, ∀ j, |x j| ≤ K

/-- `V` is bounded: `|U| ≤ M` when `|u| ≤ M`. -/
theorem rg_V_bdd {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : ∀ v ∈ rg_V δ u, ∀ j, |v j| ≤ M := by
  rintro v ⟨σ, -, rfl⟩ j
  exact rg_abs_U_le hM hδ0 hδ1 σ j

/-- **Lemma 21.1.1** (Miao, p. 743): `V ⊆ B(V)`. For an SPE `σ*`, `(a*₁, w)` with
`w(a) = U(σ*|a)` is admissible with respect to `V` and gives `U(σ*)`. -/
theorem lemma_21_1_1 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_V δ u ⊆ rg_B δ u (rg_V δ u) := by
  rintro v ⟨σ, hσ, rfl⟩
  refine ⟨σ [], fun a' => rg_U δ u (rg_cont σ [a']), ⟨fun a' => ?_, fun i x => ?_⟩, ?_⟩
  · exact ⟨_, rg_isSPE_cont hσ [a'], rfl⟩
  · have := rg_oneShot_le_of_isSPE hM hδ0 hδ1 hσ i [] x
    simp only [rg_cont_nil] at this
    rwa [rg_U_rec hM hδ0 hδ1 σ i] at this
  · funext j
    exact rg_U_rec hM hδ0 hδ1 σ j

/-- The state recursion of Lemma 21.1.2 (Miao, p. 743): `v₁ = v` and
`v_{t+1} = nx(vₜ, aₜ)` (`nx(x, ·)` is the continuation value function chosen for `x`). -/
def rg_state (nx : (ι → ℝ) → rg_Prof A → ι → ℝ) (v : ι → ℝ) : rg_Hist A → ι → ℝ
  | [] => v
  | a :: h => nx (rg_state nx v h) a

/-- The recursive strategy `σₜ(hᵗ) = g(vₜ)` of Lemma 21.1.2 and of p. 744. -/
def rg_recStrat (g : (ι → ℝ) → rg_Prof A) (nx : (ι → ℝ) → rg_Prof A → ι → ℝ) (v : ι → ℝ) :
    rg_Strat A :=
  fun h => g (rg_state nx v h)

/-- The construction in the proof of Lemma 21.1.2 (Miao, p. 743). Let `S` be a set on which
`(g x, nx x)` is admissible with respect to `W ⊆ S` and generates `x`, `W` bounded, `v ∈ S`.
Then the recursive strategy is an SPE, and its continuation payoff after `h` is the state
`v(h)`: `U(σ|h) = v(h)` (this uses that `W` is bounded). -/
theorem rg_recStrat_spec {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W S : Set (ι → ℝ)} (hWb : rg_Bdd W) (hWS : W ⊆ S)
    (g : (ι → ℝ) → rg_Prof A) (nx : (ι → ℝ) → rg_Prof A → ι → ℝ)
    (hgn : ∀ x ∈ S, rg_Admissible δ u W (g x) (nx x) ∧
      x = fun j => (1 - δ) * u (g x) j + δ * nx x (g x) j)
    {v : ι → ℝ} (hv : v ∈ S) :
    rg_IsSPE δ u (rg_recStrat g nx v) ∧
      ∀ h, rg_U δ u (rg_cont (rg_recStrat g nx v) h) = rg_state nx v h := by
  set σ := rg_recStrat g nx v with hσdef
  obtain ⟨K, hK⟩ := hWb
  have hS : ∀ h, rg_state nx v h ∈ S := by
    intro h
    induction h with
    | nil => exact hv
    | cons a h ih => exact hWS ((hgn _ ih).1.1 a)
  have hbd : ∀ h j, |rg_state nx v h j| ≤ |K| + |v j| := by
    intro h j
    cases h with
    | nil =>
      simp only [rg_state]
      linarith [abs_nonneg K]
    | cons a h =>
      have h1 := hK _ ((hgn _ (hS h)).1.1 a) j
      have h2 := abs_nonneg (v j)
      have h3 := le_abs_self K
      exact le_trans h1 (by linarith)
  have hstate : ∀ h j, rg_state nx v h j =
      (1 - δ) * u (σ h) j + δ * rg_state nx v (σ h :: h) j := by
    intro h j
    have := congrFun (hgn _ (hS h)).2 j
    exact this
  have hval : ∀ h, rg_U δ u (rg_cont σ h) = rg_state nx v h := by
    intro h
    funext j
    have hD : ∀ n : ℕ, ∀ h, |rg_U δ u (rg_cont σ h) j - rg_state nx v h j| ≤
        (M + (|K| + |v j|)) * δ ^ n := by
      intro n
      induction n with
      | zero =>
        intro h
        have h1 := rg_abs_U_le hM hδ0 hδ1 (rg_cont σ h) j
        have h2 := hbd h j
        simp only [pow_zero, mul_one]
        calc |rg_U δ u (rg_cont σ h) j - rg_state nx v h j|
            ≤ |rg_U δ u (rg_cont σ h) j| + |rg_state nx v h j| := abs_sub _ _
          _ ≤ M + (|K| + |v j|) := add_le_add h1 h2
      | succ n ih =>
        intro h
        rw [rg_U_cont_rec hM hδ0 hδ1 σ h j, hstate h j]
        have : (1 - δ) * u (σ h) j + δ * rg_U δ u (rg_cont σ (σ h :: h)) j -
            ((1 - δ) * u (σ h) j + δ * rg_state nx v (σ h :: h) j) =
            δ * (rg_U δ u (rg_cont σ (σ h :: h)) j - rg_state nx v (σ h :: h) j) := by ring
        rw [this, abs_mul, abs_of_nonneg hδ0, pow_succ]
        have := ih (σ h :: h)
        nlinarith
    have hlim : Filter.Tendsto (fun n : ℕ => (M + (|K| + |v j|)) * δ ^ n) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).const_mul (M + (|K| + |v j|))
    have := ge_of_tendsto' hlim (fun n => hD n h)
    have h0 := abs_nonneg (rg_U δ u (rg_cont σ h) j - rg_state nx v h j)
    have : |rg_U δ u (rg_cont σ h) j - rg_state nx v h j| = 0 := le_antisymm this h0
    rw [abs_eq_zero, sub_eq_zero] at this
    exact this
  refine ⟨?_, hval⟩
  rw [proposition_21_1_1 hM hδ0 hδ1]
  intro i hbar τ hτ hp
  unfold rg_IsProfitable at hp
  rw [definition_21_1_2 hM hδ0 hδ1 σ i hbar τ hτ.2, hval, hval] at hp
  have hadm := (hgn _ (hS hbar)).1.2 i (τ hbar)
  have hst := hstate hbar i
  have hnext : rg_state nx v (rg_upd (σ hbar) i (τ hbar) :: hbar) =
      nx (rg_state nx v hbar) (rg_upd (σ hbar) i (τ hbar)) := rfl
  have hnext' : rg_state nx v (σ hbar :: hbar) = nx (rg_state nx v hbar) (σ hbar) := rfl
  have hg : σ hbar = g (rg_state nx v hbar) := rfl
  rw [hnext] at hp
  rw [hnext'] at hst
  rw [← hg] at hadm
  linarith

/-- **Lemma 21.1.2** (Self-generation, Miao, p. 743): if `W ⊆ ℝⁿ` is bounded and
`W ⊆ B(W)`, then `B(W) ⊆ V`. -/
theorem lemma_21_1_2 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W : Set (ι → ℝ)} (hWb : rg_Bdd W)
    (hW : W ⊆ rg_B δ u W) : rg_B δ u W ⊆ rg_V δ u := by
  intro v hv
  obtain ⟨a0, w0, -, -⟩ := id hv
  have hch : ∀ x : ι → ℝ, ∃ p : rg_Prof A × (rg_Prof A → ι → ℝ),
      x ∈ rg_B δ u W → rg_Admissible δ u W p.1 p.2 ∧
        x = fun j => (1 - δ) * u p.1 j + δ * p.2 p.1 j := by
    intro x
    by_cases hx : x ∈ rg_B δ u W
    · obtain ⟨a, w, h1, h2⟩ := hx
      exact ⟨(a, w), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(a0, w0), fun h => absurd h hx⟩
  choose p hp using hch
  obtain ⟨hσ, hval⟩ := rg_recStrat_spec hM hδ0 hδ1 hWb hW (fun x => (p x).1) (fun x => (p x).2)
    (fun x hx => hp x hx) hv
  refine ⟨_, hσ, ?_⟩
  have := hval []
  rwa [rg_cont_nil] at this

/-- **Theorem 21.1.1** (Factorization, Miao, p. 744): `V = B(V)`. -/
theorem theorem_21_1_1 {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_V δ u = rg_B δ u (rg_V δ u) :=
  Set.Subset.antisymm (lemma_21_1_1 hM hδ0 hδ1)
    (lemma_21_1_2 hM hδ0 hδ1 ⟨M, rg_V_bdd hM hδ0 hδ1⟩ (lemma_21_1_1 hM hδ0 hδ1))

/-- Miao, pp. 744–745, after Theorem 21.1.1: every SPE payoff `v₁ ∈ V` is supported by a
recursive strategy `aₜ = g(vₜ)`, `v_{t+1} = nx(vₜ, aₜ)`, whose states `vₜ` lie in `V` and are
the continuation payoffs. -/
theorem theorem_21_1_1_recursive {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {v : ι → ℝ} (hv : v ∈ rg_V δ u) :
    ∃ (g : (ι → ℝ) → rg_Prof A) (nx : (ι → ℝ) → rg_Prof A → ι → ℝ),
      rg_IsSPE δ u (rg_recStrat g nx v) ∧ rg_U δ u (rg_recStrat g nx v) = v ∧
      (∀ h, rg_recStrat g nx v h = g (rg_state nx v h)) ∧
      (∀ h a, rg_state nx v (a :: h) = nx (rg_state nx v h) a) ∧
      (∀ h, rg_state nx v h ∈ rg_V δ u ∧
        rg_U δ u (rg_cont (rg_recStrat g nx v) h) = rg_state nx v h) := by
  obtain ⟨σ0, -, -⟩ := id hv
  have hch : ∀ x : ι → ℝ, ∃ p : rg_Prof A × (rg_Prof A → ι → ℝ),
      x ∈ rg_B δ u (rg_V δ u) → rg_Admissible δ u (rg_V δ u) p.1 p.2 ∧
        x = fun j => (1 - δ) * u p.1 j + δ * p.2 p.1 j := by
    intro x
    by_cases hx : x ∈ rg_B δ u (rg_V δ u)
    · obtain ⟨a, w, h1, h2⟩ := hx
      exact ⟨(a, w), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(σ0 [], fun _ => x), fun h => absurd h hx⟩
  choose p hp using hch
  have hBV := theorem_21_1_1 hM hδ0 hδ1 (u := u)
  have hvB : v ∈ rg_B δ u (rg_V δ u) := hBV ▸ hv
  obtain ⟨hσ, hval⟩ := rg_recStrat_spec hM hδ0 hδ1 ⟨M, rg_V_bdd hM hδ0 hδ1⟩ hBV.le
    (fun x => (p x).1) (fun x => (p x).2) (fun x hx => hp x hx) hvB
  refine ⟨_, _, hσ, ?_, fun _ => rfl, fun _ _ => rfl, fun h => ⟨?_, hval h⟩⟩
  · have := hval []
    rwa [rg_cont_nil] at this
  · rw [← hval h]
    exact ⟨_, rg_isSPE_cont hσ h, rfl⟩

/-- **Lemma 21.1.3** (Monotonicity, Miao, p. 746): `W ⊆ W'` implies `B(W) ⊆ B(W')`. -/
theorem lemma_21_1_3 (δ : ℝ) (u : rg_Prof A → ι → ℝ) {W W' : Set (ι → ℝ)} (h : W ⊆ W') :
    rg_B δ u W ⊆ rg_B δ u W' := by
  rintro v ⟨a, w, ⟨hw, hic⟩, rfl⟩
  exact ⟨a, w, ⟨fun a' => h (hw a'), hic⟩, rfl⟩

/-- A stage-game Nash equilibrium `a*`: `uᵢ(a'ᵢ, a*₋ᵢ) ≤ uᵢ(a*)` for all `i, a'ᵢ`. -/
def rg_IsStageNash (u : rg_Prof A → ι → ℝ) (a : rg_Prof A) : Prop :=
  ∀ (i : ι) (x : A i), u (rg_upd a i x) i ≤ u a i

/-- Repeating a stage-game Nash equilibrium is an SPE: `u(a*) ∈ V`; in particular `V` is
nonempty whenever the stage game has a pure Nash equilibrium (Miao, p. 746 uses `V ≠ ∅`). -/
theorem rg_stageNash_mem_V {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {a : rg_Prof A} (ha : rg_IsStageNash u a) :
    u a ∈ rg_V δ u := by
  have hgen : u a = fun j => (1 - δ) * u a j + δ * (fun _ => u a) a j := by
    funext j
    ring
  have hadm : rg_Admissible δ u {u a} a (fun _ => u a) := by
    refine ⟨fun _ => rfl, fun i x => ?_⟩
    have := mul_le_mul_of_nonneg_left (ha i x) (by linarith : (0 : ℝ) ≤ 1 - δ)
    linarith
  have hW : ({u a} : Set (ι → ℝ)) ⊆ rg_B δ u {u a} := by
    rintro v rfl
    exact ⟨a, _, hadm, hgen⟩
  have hbd : rg_Bdd ({u a} : Set (ι → ℝ)) := ⟨M, by rintro v rfl j; exact hM a j⟩
  exact lemma_21_1_2 hM hδ0 hδ1 hbd hW (hW rfl)

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 21.1.1: the repeated prisoner's dilemma

Miao, Example 21.1.1, p. 744. Two players, actions `C = true` and `D = false`, payoffs
`u(C, C) = (1, 1)`, `u(C, D) = (−1, 2)`, `u(D, C) = (2, −1)`, `u(D, D) = (0, 0)`.

* `example_21_1_1_DD`: `(D, D)` with `w ≡ (0, 0)` is admissible with respect to
  `W = {(1, 1), (0, 0)}` and gives `(0, 0)`, for every `δ ∈ [0, 1)`.
* `example_21_1_1_CC`: `(C, C)` with `w(C, C) = (1, 1)`, `w(y) = (0, 0)` otherwise, is admissible
  and gives `(1, 1)` when `δ ≥ 1/2`.
* `example_21_1_1`: for `1/2 ≤ δ < 1`, `W` is self-generating, hence `W ⊆ V`.
* `rg_pd_stageNash`: `(D, D)` is a stage-game Nash equilibrium, so `V ≠ ∅` for every `δ`
  (`rg_pd_V_nonempty`); this is the concrete instance used for the existence of a stage Nash
  equilibrium elsewhere in the chapter.
-/

namespace Miao.DynamicGames

/-- The prisoner's dilemma payoff of a player who plays `x` against `y` (`true = C`). -/
def rg_pdPay : Bool → Bool → ℝ
  | true, true => 1
  | true, false => -1
  | false, true => 2
  | false, false => 0

/-- The prisoner's dilemma payoffs `u(a)ᵢ = pdPay(aᵢ, a₋ᵢ)` (Miao, p. 744). -/
def rg_pdU (a : rg_Prof (fun _ : Fin 2 => Bool)) (i : Fin 2) : ℝ := rg_pdPay (a i) (a (1 - i))

/-- The candidate self-generating set `W = {(1, 1), (0, 0)}` of Example 21.1.1. -/
def rg_pdW : Set (Fin 2 → ℝ) := {fun _ => 1, fun _ => 0}

/-- Profile updates in the prisoner's dilemma, computed. -/
theorem rg_pd_upd (a : rg_Prof (fun _ : Fin 2 => Bool)) (i : Fin 2) (x : Bool) :
    rg_upd a i x = fun j => if j = i then x else a j := by
  rw [rg_upd_eq]
  funext j
  exact Function.update_apply a i x j

/-- `|u| ≤ 2` in the prisoner's dilemma. -/
theorem rg_pd_bound (a : rg_Prof (fun _ : Fin 2 => Bool)) (j : Fin 2) : |rg_pdU a j| ≤ 2 := by
  unfold rg_pdU
  cases a j <;> cases a (1 - j) <;> norm_num [rg_pdPay]

/-- **Example 21.1.1** (Miao, p. 744), `(0, 0)`: `(D, D)` and `w ≡ (0, 0)` are admissible with
respect to `W` for every `δ ∈ [0, 1)`: `0 = (1 − δ) uᵢ(D, D) + δ wᵢ(D, D)` and
`0 ≥ (1 − δ) uᵢ(aᵢ, D) + δ wᵢ(aᵢ, D)`. -/
theorem example_21_1_1_DD {δ : ℝ} (hδ1 : δ < 1) :
    rg_Admissible δ rg_pdU rg_pdW (fun _ => false) (fun _ => fun _ => 0) ∧
      (fun _ => (0 : ℝ)) = fun j => (1 - δ) * rg_pdU (fun _ => false) j + δ * 0 := by
  refine ⟨⟨fun _ => Or.inr rfl, fun i x => ?_⟩, ?_⟩
  · rw [rg_pd_upd]
    fin_cases i <;> cases x <;> simp [rg_pdU, rg_pdPay] <;> linarith
  · funext j
    simp [rg_pdU, rg_pdPay]

/-- The continuation values `w(C, C) = (1, 1)`, `w(y) = (0, 0)` otherwise. -/
def rg_pdWCC (a : rg_Prof (fun _ : Fin 2 => Bool)) : Fin 2 → ℝ :=
  if a = (fun _ => true) then fun _ => 1 else fun _ => 0

/-- **Example 21.1.1** (Miao, p. 744), `(1, 1)`: for `δ ≥ 1/2`, `(C, C)` with `w(C, C) = (1, 1)`
and `w(y) = (0, 0)` otherwise is admissible with respect to `W`:
`1 = (1 − δ) uᵢ(C, C) + δ wᵢ(C, C)` and `1 ≥ (1 − δ) uᵢ(aᵢ, C) + δ wᵢ(aᵢ, C)`. -/
theorem example_21_1_1_CC {δ : ℝ} (hδ : 1 / 2 ≤ δ) :
    rg_Admissible δ rg_pdU rg_pdW (fun _ => true) rg_pdWCC ∧
      (fun _ => (1 : ℝ)) =
        fun j => (1 - δ) * rg_pdU (fun _ => true) j + δ * rg_pdWCC (fun _ => true) j := by
  refine ⟨⟨fun a' => ?_, fun i x => ?_⟩, ?_⟩
  · unfold rg_pdWCC
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [rg_pd_upd]
    fin_cases i <;> cases x <;>
      simp [rg_pdU, rg_pdPay, rg_pdWCC, funext_iff] <;> linarith
  · funext j
    simp [rg_pdU, rg_pdPay, rg_pdWCC]

/-- **Example 21.1.1** (Miao, p. 744): if `1/2 ≤ δ < 1`, `W = {(1, 1), (0, 0)}` is
self-generating, hence `W ⊆ V` by Lemma 21.1.2. -/
theorem example_21_1_1 {δ : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) :
    rg_pdW ⊆ rg_B δ rg_pdU rg_pdW ∧ rg_pdW ⊆ rg_V δ rg_pdU := by
  have hself : rg_pdW ⊆ rg_B δ rg_pdU rg_pdW := by
    rintro v (rfl | rfl)
    · exact ⟨_, _, (example_21_1_1_CC hδ).1, (example_21_1_1_CC hδ).2⟩
    · exact ⟨_, _, (example_21_1_1_DD hδ1).1, by simpa using (example_21_1_1_DD hδ1).2⟩
  have hbd : rg_Bdd rg_pdW := ⟨1, by rintro x (rfl | rfl) j <;> simp⟩
  exact ⟨hself, hself.trans
    (lemma_21_1_2 rg_pd_bound (by linarith) hδ1 hbd hself)⟩

/-- `(D, D)` is a Nash equilibrium of the prisoner's dilemma stage game. -/
theorem rg_pd_stageNash : rg_IsStageNash rg_pdU (fun _ => false) := by
  intro i x
  rw [rg_pd_upd]
  fin_cases i <;> cases x <;> simp [rg_pdU, rg_pdPay]

/-- In the repeated prisoner's dilemma `(0, 0) ∈ V` for every `δ ∈ [0, 1)`. -/
theorem rg_pd_V_nonempty {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (fun _ => (0 : ℝ)) ∈ rg_V δ rg_pdU := by
  have := rg_stageNash_mem_V rg_pd_bound hδ0 hδ1 rg_pd_stageNash
  have h : rg_pdU (fun _ => false) = fun _ => 0 := by
    funext j
    simp [rg_pdU, rg_pdPay]
  rwa [h] at this

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# `V` is the maximal fixed point of `B` in the feasible payoff set

Miao, §21.1.1, p. 740 (the feasible payoff set) and Theorem 21.1.2, p. 745.

* `rg_feasible u = co {u(a) : a ∈ A}`, the feasible payoff set; `rg_box M = [−M, M]ⁿ`.
* `rg_U_mem_closure_feasible`: every payoff `U(σ)` lies in the closure of the feasible set (an
  infinite convex combination of stage payoffs); for finite `A` the feasible set is closed and
  `U(σ) ∈ rg_feasible u` (`rg_V_subset_feasible`).
* `rg_BOn F`: `B` as a monotone map on the complete lattice `{W : W ⊆ F}` of subsets of a convex
  `F` containing all stage payoffs.
* `theorem_21_1_2` (finite `A`, `F` the feasible set): `V` is the greatest fixed point
  (`OrderHom.gfp`, Knaster–Tarski) of `B` on the subsets of `F`, it equals the union of the
  self-generating subsets of `F`, and contains every fixed point in `F`.
* `theorem_21_1_2_closure`: the same for any action sets, with `F` the closure of the feasible
  set (departure: with infinite `A` the book's convex hull need not be closed, and `V` is only
  shown to lie in its closure).
-/

namespace Miao.DynamicGames

open Filter Topology

variable {ι : Type*} {A : ι → Type*}

/-- The feasible payoff set `W = co {u(a) ∈ ℝⁿ : a ∈ A}` (Miao, p. 740). -/
def rg_feasible (u : rg_Prof A → ι → ℝ) : Set (ι → ℝ) := convexHull ℝ (Set.range u)

/-- Every stage payoff `u(a)` is feasible. -/
theorem rg_u_mem_feasible (u : rg_Prof A → ι → ℝ) (a : rg_Prof A) : u a ∈ rg_feasible u :=
  subset_convexHull ℝ (Set.range u) (Set.mem_range_self a)

/-- The box `[−M, M]ⁿ`. -/
def rg_box (ι : Type*) (M : ℝ) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Icc (-M) M

/-- The box `[−M, M]ⁿ` is convex. -/
theorem rg_box_convex (M : ℝ) : Convex ℝ (rg_box ι M) :=
  convex_pi fun _ _ => convex_Icc _ _

/-- The box `[−M, M]ⁿ` is closed. -/
theorem rg_box_isClosed (M : ℝ) : IsClosed (rg_box ι M) :=
  isClosed_set_pi fun _ _ => isClosed_Icc

/-- Membership in the box. -/
theorem rg_mem_box {M : ℝ} {x : ι → ℝ} : x ∈ rg_box ι M ↔ ∀ j, |x j| ≤ M := by
  simp only [rg_box, Set.mem_univ_pi, Set.mem_Icc, abs_le]

/-- The closed feasible set lies in `[−M, M]ⁿ` when `|u| ≤ M`. -/
theorem rg_closure_feasible_subset_box {M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) : closure (rg_feasible u) ⊆ rg_box ι M := by
  refine closure_minimal (convexHull_min ?_ (rg_box_convex M)) (rg_box_isClosed M)
  rintro x ⟨a, rfl⟩
  exact rg_mem_box.2 (hM a)

/-- Each continuation payoff `U(σ|h)` is within `2Mδⁿ` of a point of the feasible set. -/
theorem rg_U_near_feasible {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) (n : ℕ) :
    ∀ h, ∃ c ∈ rg_feasible u, ∀ j, |rg_U δ u (rg_cont σ h) j - c j| ≤ 2 * M * δ ^ n := by
  induction n with
  | zero =>
    intro h
    refine ⟨u (σ h), rg_u_mem_feasible u (σ h), fun j => ?_⟩
    have h1 := rg_abs_U_le hM hδ0 hδ1 (rg_cont σ h) j
    have h2 := hM (σ h) j
    calc |rg_U δ u (rg_cont σ h) j - u (σ h) j|
        ≤ |rg_U δ u (rg_cont σ h) j| + |u (σ h) j| := abs_sub _ _
      _ ≤ 2 * M * δ ^ 0 := by rw [pow_zero]; linarith
  | succ n ih =>
    intro h
    obtain ⟨c, hc, hcj⟩ := ih (σ h :: h)
    refine ⟨(1 - δ) • u (σ h) + δ • c, ?_, fun j => ?_⟩
    · exact convex_convexHull ℝ _ (rg_u_mem_feasible u (σ h)) hc (by linarith) hδ0
        (by ring)
    · rw [rg_U_cont_rec hM hδ0 hδ1 σ h j]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (1 - δ) * u (σ h) j + δ * rg_U δ u (rg_cont σ (σ h :: h)) j -
          ((1 - δ) * u (σ h) j + δ * c j) = δ * (rg_U δ u (rg_cont σ (σ h :: h)) j - c j) := by
        ring
      rw [this, abs_mul, abs_of_nonneg hδ0, pow_succ]
      have := hcj j
      nlinarith

/-- Every payoff `U(σ) = (1 − δ) Σ δᵗ u(aₜ)` lies in the closure of the feasible set. -/
theorem rg_U_mem_closure_feasible {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : rg_Strat A) : rg_U δ u σ ∈ closure (rg_feasible u) := by
  have hc := fun n => rg_U_near_feasible hM hδ0 hδ1 σ n []
  choose c hcF hcj using hc
  simp only [rg_cont_nil] at hcj
  refine mem_closure_of_tendsto (b := atTop) (f := c) (tendsto_pi_nhds.2 fun j => ?_)
    (Eventually.of_forall hcF)
  have hlim : Tendsto (fun n : ℕ => 2 * M * δ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).const_mul (2 * M)
  have hl : Tendsto (fun n => rg_U δ u σ j - 2 * M * δ ^ n) atTop (𝓝 (rg_U δ u σ j)) := by
    simpa using tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun n => rg_U δ u σ j + 2 * M * δ ^ n) atTop (𝓝 (rg_U δ u σ j)) := by
    simpa using tendsto_const_nhds.add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr (fun n => ?_) (fun n => ?_)
  · have := (abs_le.1 (hcj n j)).2
    simp only
    linarith
  · have := (abs_le.1 (hcj n j)).1
    simp only
    linarith

/-- `V` lies in the closure of the feasible set. -/
theorem rg_V_subset_closure_feasible {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    rg_V δ u ⊆ closure (rg_feasible u) := by
  rintro v ⟨σ, -, rfl⟩
  exact rg_U_mem_closure_feasible hM hδ0 hδ1 σ

/-- For finite `A` the feasible set is compact, hence closed. -/
theorem rg_closure_feasible_of_finite [Finite (rg_Prof A)] (u : rg_Prof A → ι → ℝ) :
    closure (rg_feasible u) = rg_feasible u :=
  ((Set.finite_range u).isCompact_convexHull ℝ).isClosed.closure_eq

/-- For finite `A`, `V` lies in the feasible set `co {u(a)}`. -/
theorem rg_V_subset_feasible [Finite (rg_Prof A)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_V δ u ⊆ rg_feasible u := by
  rw [← rg_closure_feasible_of_finite u]
  exact rg_V_subset_closure_feasible hM hδ0 hδ1

/-- `B` maps subsets of a convex set `F` containing every `u(a)` into `F`. -/
theorem rg_B_subset_of_convex {δ : ℝ} {u : rg_Prof A → ι → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {F : Set (ι → ℝ)} (hFc : Convex ℝ F) (hFu : ∀ a, u a ∈ F) {W : Set (ι → ℝ)}
    (hW : W ⊆ F) : rg_B δ u W ⊆ F := by
  rintro v ⟨a, w, ⟨hw, -⟩, rfl⟩
  have := hFc (hFu a) (hW (hw a)) (by linarith : (0 : ℝ) ≤ 1 - δ) hδ0 (by ring)
  convert this using 1

/-- `B` as a monotone operator on the complete lattice of subsets of `F`. -/
def rg_BOn (δ : ℝ) (u : rg_Prof A → ι → ℝ) (F : Set (ι → ℝ))
    (hF : ∀ W, W ⊆ F → rg_B δ u W ⊆ F) : Set.Iic F →o Set.Iic F where
  toFun W := ⟨rg_B δ u W.1, hF W.1 W.2⟩
  monotone' _ _ h := lemma_21_1_3 δ u h

/-- The fixed-point characterisation behind Theorem 21.1.2, for any convex `F ⊆ [−M, M]ⁿ` that
contains every `u(a)` and `V`. -/
theorem rg_maximal_fixed_point {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {F : Set (ι → ℝ)} (hFc : Convex ℝ F) (hFu : ∀ a, u a ∈ F)
    (hFb : F ⊆ rg_box ι M) (hVF : rg_V δ u ⊆ F) :
    (OrderHom.gfp (rg_BOn δ u F fun _ hW => rg_B_subset_of_convex hδ0 hδ1 hFc hFu hW)).1 =
        rg_V δ u ∧
      rg_V δ u = ⋃₀ {W | W ⊆ F ∧ W ⊆ rg_B δ u W} ∧
      ∀ W, W ⊆ F → W = rg_B δ u W → W ⊆ rg_V δ u := by
  have hbdF : ∀ W, W ⊆ F → rg_Bdd W := fun W hW => ⟨M, fun x hx => rg_mem_box.1 (hFb (hW hx))⟩
  have hself : ∀ W, W ⊆ F → W ⊆ rg_B δ u W → W ⊆ rg_V δ u := fun W hW hWB =>
    hWB.trans (lemma_21_1_2 hM hδ0 hδ1 (hbdF W hW) hWB)
  refine ⟨?_, ?_, fun W hW hWB => hself W hW hWB.le⟩
  · set f := rg_BOn δ u F fun _ hW => rg_B_subset_of_convex hδ0 hδ1 hFc hFu hW
    apply Set.Subset.antisymm
    · have hfix : f (OrderHom.gfp f) = OrderHom.gfp f := OrderHom.map_gfp f
      have hG : (OrderHom.gfp f).1 = rg_B δ u (OrderHom.gfp f).1 :=
        (congrArg Subtype.val hfix).symm
      exact hself _ (OrderHom.gfp f).2 hG.le
    · have : (⟨rg_V δ u, hVF⟩ : Set.Iic F) ≤ f ⟨rg_V δ u, hVF⟩ := lemma_21_1_1 hM hδ0 hδ1
      exact OrderHom.le_gfp f this
  · apply Set.Subset.antisymm
    · exact Set.subset_sUnion_of_mem ⟨hVF, lemma_21_1_1 hM hδ0 hδ1⟩
    · rintro x ⟨W, ⟨hW, hWB⟩, hx⟩
      exact hself W hW hWB hx

/-- **Theorem 21.1.2** (Miao, p. 745), for finite `A`: `V` is the maximal fixed point of `B` on
the lattice of subsets of the feasible payoff set `co {u(a)}`: it is the greatest fixed point
given by Tarski's theorem, the union of all self-generating subsets, and it contains every fixed
point of `B` in the feasible set. -/
theorem theorem_21_1_2 [Finite (rg_Prof A)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (OrderHom.gfp (rg_BOn δ u (rg_feasible u) fun _ hW => rg_B_subset_of_convex hδ0 hδ1
        (convex_convexHull ℝ _) (rg_u_mem_feasible u) hW)).1 = rg_V δ u ∧
      rg_V δ u = ⋃₀ {W | W ⊆ rg_feasible u ∧ W ⊆ rg_B δ u W} ∧
      ∀ W, W ⊆ rg_feasible u → W = rg_B δ u W → W ⊆ rg_V δ u :=
  rg_maximal_fixed_point hM hδ0 hδ1 (convex_convexHull ℝ _)
    (rg_u_mem_feasible u)
    ((subset_closure).trans (rg_closure_feasible_subset_box hM))
    (rg_V_subset_feasible hM hδ0 hδ1)

/-- **Theorem 21.1.2** (Miao, p. 745), any action sets: the same with the closure of the
feasible set in place of the feasible set. -/
theorem theorem_21_1_2_closure {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (OrderHom.gfp (rg_BOn δ u (closure (rg_feasible u)) fun _ hW => rg_B_subset_of_convex hδ0
        hδ1 (convex_convexHull ℝ _).closure
        (fun a => subset_closure (rg_u_mem_feasible u a)) hW)).1 = rg_V δ u ∧
      rg_V δ u = ⋃₀ {W | W ⊆ closure (rg_feasible u) ∧ W ⊆ rg_B δ u W} ∧
      ∀ W, W ⊆ closure (rg_feasible u) → W = rg_B δ u W → W ⊆ rg_V δ u :=
  rg_maximal_fixed_point hM hδ0 hδ1 (convex_convexHull ℝ _).closure
    (fun a => subset_closure (rg_u_mem_feasible u a))
    (rg_closure_feasible_subset_box hM) (rg_V_subset_closure_feasible hM hδ0 hδ1)

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Compactness: Proposition 21.1.2, Lemma 21.1.4, Exercises 21.1–21.2

Miao, Proposition 21.1.2 (p. 745), Lemma 21.1.4 (p. 746) and Exercises 21.1–21.2 (p. 771).

* `rg_mem_B_iff_punish`: when every coordinate `xᵢ` attains its minimum `pᵢ` on `W`, the
  continuation values off the equilibrium action can be taken to be the worst punishments:
  `v ∈ B(W)` iff `v = (1 − δ) u(a) + δ w₀` with `w₀ ∈ W` and
  `(1 − δ) uᵢ(a'ᵢ, a₋ᵢ) + δ min_W xᵢ ≤ vᵢ` for all `i, a'ᵢ`. This is the Cronshaw–Luenberger form
  of `B` (p. 747) and the key to compactness for infinite action sets.
* `ex_21_2`: with compact action sets and continuous payoffs, `B(W)` is compact for compact `W`;
  `lemma_21_1_4` is the finite case.
* `ex_21_1`: with compact action sets and continuous payoffs, `V` is compact;
  `proposition_21_1_2` is the finite case. The proof is the book's second proof
  (`cl V ⊆ B(cl V)`, then Lemma 21.1.2), with the compactness of `B(cl V)` replacing the
  extraction of a convergent subsequence of admissible pairs.
-/

namespace Miao.DynamicGames

variable {ι : Type*} {A : ι → Type*}

/-- Admissibility with the worst punishments (Miao, p. 747, the operator of Cronshaw and
Luenberger): if `pᵢ ∈ W` minimises the `i`-th coordinate on `W`, then `v ∈ B(W)` iff
`v = (1 − δ) u(a) + δ w₀` for some `a` and `w₀ ∈ W` with
`(1 − δ) uᵢ(a'ᵢ, a₋ᵢ) + δ (pᵢ)ᵢ ≤ (1 − δ) uᵢ(a) + δ (w₀)ᵢ` for all `i, a'ᵢ`. -/
theorem rg_mem_B_iff_punish {δ : ℝ} {u : rg_Prof A → ι → ℝ} (hδ0 : 0 ≤ δ) {W : Set (ι → ℝ)}
    {p : ι → ι → ℝ} (hp : ∀ i, p i ∈ W ∧ ∀ x ∈ W, p i i ≤ x i) {v : ι → ℝ} :
    v ∈ rg_B δ u W ↔ ∃ a, ∃ w0 ∈ W, (v = fun j => (1 - δ) * u a j + δ * w0 j) ∧
      ∀ (i : ι) (x : A i),
        (1 - δ) * u (rg_upd a i x) i + δ * p i i ≤ (1 - δ) * u a i + δ * w0 i := by
  constructor
  · rintro ⟨a, w, ⟨hw, hic⟩, rfl⟩
    refine ⟨a, w a, hw a, rfl, fun i x => le_trans ?_ (hic i x)⟩
    have := mul_le_mul_of_nonneg_left ((hp i).2 _ (hw (rg_upd a i x))) hδ0
    linarith
  · rintro ⟨a, w0, hw0, rfl, hic⟩
    classical
    let w : rg_Prof A → ι → ℝ := fun a' =>
      if a' = a then w0 else if h : ∃ k, ∃ y : A k, a' = rg_upd a k y then p h.choose else w0
    have hwa : w a = w0 := by simp [w]
    refine ⟨a, w, ⟨fun a' => ?_, fun i x => ?_⟩, by rw [hwa]⟩
    · simp only [w]
      split_ifs
      · exact hw0
      · exact (hp _).1
      · exact hw0
    · rw [hwa]
      by_cases hx : rg_upd a i x = a
      · rw [hx, hwa]
      · have hex : ∃ k, ∃ y : A k, rg_upd a i x = rg_upd a k y := ⟨i, x, rfl⟩
        have hwv : w (rg_upd a i x) = p hex.choose := by
          simp only [w]
          split_ifs
          rfl
        obtain ⟨y, hy⟩ := hex.choose_spec
        have hji : hex.choose = i := rg_upd_player_eq a x y hy hx
        rw [hwv, hji]
        exact hic i x

/-- **Exercise 21.2** (Miao, p. 771; Lemma 21.1.4 for compact action sets). With compact action
sets, continuous payoffs and `δ ≥ 0`, `B(W)` is compact whenever `W` is compact. -/
theorem ex_21_2 [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] {δ : ℝ}
    {u : rg_Prof A → ι → ℝ} (hu : ∀ j, Continuous fun a => u a j) (hδ0 : 0 ≤ δ)
    {W : Set (ι → ℝ)} (hW : IsCompact W) : IsCompact (rg_B δ u W) := by
  rcases W.eq_empty_or_nonempty with rfl | hne
  · convert isCompact_empty
    ext v
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨a, w, ⟨hw, -⟩, -⟩
    exact hw a
  have hmin : ∀ i, ∃ x ∈ W, IsMinOn (fun y : ι → ℝ => y i) W x := fun i =>
    hW.exists_isMinOn hne (continuous_apply i).continuousOn
  choose p hpW hpmin using hmin
  have hp : ∀ i, p i ∈ W ∧ ∀ x ∈ W, p i i ≤ x i := fun i => ⟨hpW i, fun x hx => hpmin i hx⟩
  classical
  set S : Set (rg_Prof A × (ι → ℝ)) := {q | q.2 ∈ W} ∩ ⋂ (i : ι), ⋂ (x : A i),
    {q | (1 - δ) * u (rg_upd q.1 i x) i + δ * p i i ≤ (1 - δ) * u q.1 i + δ * q.2 i} with hS
  have hupd : ∀ (i : ι) (x : A i),
      Continuous fun q : rg_Prof A × (ι → ℝ) => u (rg_upd q.1 i x) i := by
    intro i x
    have : (fun q : rg_Prof A × (ι → ℝ) => rg_upd q.1 i x) =
        fun q => Function.update q.1 i x := by
      funext q
      rw [rg_upd_eq]
    exact (hu i).comp (this ▸ continuous_fst.update i continuous_const)
  have hSc : IsClosed S := by
    refine (hW.isClosed.preimage continuous_snd).inter
      (isClosed_iInter fun i => isClosed_iInter fun x => isClosed_le ?_ ?_)
    · exact (continuous_const.mul (hupd i x)).add continuous_const
    · exact (continuous_const.mul ((hu i).comp continuous_fst)).add
        (continuous_const.mul ((continuous_apply i).comp continuous_snd))
  have hSk : IsCompact S :=
    (isCompact_univ.prod hW).of_isClosed_subset hSc fun q hq => ⟨trivial, hq.1⟩
  have himg : rg_B δ u W = (fun q : rg_Prof A × (ι → ℝ) =>
      fun j => (1 - δ) * u q.1 j + δ * q.2 j) '' S := by
    ext v
    rw [rg_mem_B_iff_punish hδ0 hp]
    constructor
    · rintro ⟨a, w0, hw0, rfl, hic⟩
      refine ⟨(a, w0), ⟨hw0, ?_⟩, rfl⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hic
    · rintro ⟨⟨a, w0⟩, ⟨hw0, hic⟩, rfl⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hic
      exact ⟨a, w0, hw0, rfl, hic⟩
  rw [himg]
  refine hSk.image (continuous_pi fun j => ?_)
  exact (continuous_const.mul ((hu j).comp continuous_fst)).add
    (continuous_const.mul ((continuous_apply j).comp continuous_snd))

/-- **Lemma 21.1.4** (Compactness, Miao, p. 746): with finitely many players and finite action
sets, `B(W)` is compact if `W` is compact. -/
theorem lemma_21_1_4 [Finite ι] [∀ i, Finite (A i)] {δ : ℝ} {u : rg_Prof A → ι → ℝ}
    (hδ0 : 0 ≤ δ) {W : Set (ι → ℝ)} (hW : IsCompact W) : IsCompact (rg_B δ u W) := by
  let _ : ∀ i, TopologicalSpace (A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (A i) := fun _ => ⟨rfl⟩
  exact ex_21_2 (fun _ => continuous_of_discreteTopology) hδ0 hW

/-- `[−M, M]ⁿ` is compact. -/
theorem rg_box_isCompact (M : ℝ) : IsCompact (rg_box ι M) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- **Exercise 21.1** (Miao, p. 771; Proposition 21.1.2 for compact action sets). With compact
action sets, continuous bounded payoffs and `0 ≤ δ < 1`, the SPE payoff set `V` is compact. -/
theorem ex_21_1 [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hu : ∀ j, Continuous fun a => u a j) (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : IsCompact (rg_V δ u) := by
  have hVbox : rg_V δ u ⊆ rg_box ι M := fun v hv => rg_mem_box.2 (rg_V_bdd hM hδ0 hδ1 v hv)
  have hcl : closure (rg_V δ u) ⊆ rg_box ι M := closure_minimal hVbox (rg_box_isClosed M)
  have hclc : IsCompact (closure (rg_V δ u)) :=
    (rg_box_isCompact M).of_isClosed_subset isClosed_closure hcl
  have hB := ex_21_2 hu hδ0 hclc
  have h1 : rg_V δ u ⊆ rg_B δ u (closure (rg_V δ u)) :=
    (theorem_21_1_1 hM hδ0 hδ1).subset.trans (lemma_21_1_3 δ u subset_closure)
  have h2 : closure (rg_V δ u) ⊆ rg_B δ u (closure (rg_V δ u)) := closure_minimal h1 hB.isClosed
  have h3 : rg_B δ u (closure (rg_V δ u)) ⊆ rg_V δ u :=
    lemma_21_1_2 hM hδ0 hδ1 ⟨M, fun x hx => rg_mem_box.1 (hcl hx)⟩ h2
  have hclosed : IsClosed (rg_V δ u) := closure_subset_iff_isClosed.1 (h2.trans h3)
  exact (rg_box_isCompact M).of_isClosed_subset hclosed hVbox

/-- **Proposition 21.1.2** (Miao, p. 745): with finitely many players and finite action sets,
the SPE payoff set `V` is compact. -/
theorem proposition_21_1_2 [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : IsCompact (rg_V δ u) := by
  let _ : ∀ i, TopologicalSpace (A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (A i) := fun _ => ⟨rfl⟩
  exact ex_21_1 (fun _ => continuous_of_discreteTopology) hM hδ0 hδ1

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Computing `V` by iterating `B`

Miao, §21.1.3, pp. 746–747: Theorem 21.1.3 and the operators of Cronshaw–Luenberger and of
Judd–Yeltekin–Conklin. Finitely many players and finite action sets, as in the book.

* `theorem_21_1_3`: if `W₀ ⊇ V` is compact and `B(W₀) ⊆ W₀`, then `Wₜ = Bᵗ(W₀)` are compact,
  decreasing, contain `V`, and `V = ⋂ₜ Wₜ`. `theorem_21_1_3_hausdorff`: `Wₜ → V` in the
  Hausdorff distance (the book's `V = lim Bᵗ(W₀)`).
* `rg_maxBox u = ×ᵢ [uᵢ min, uᵢ max]`, the maximal payoff set: compact, contains `V`, and
  `B(maxBox) ⊆ maxBox`, so it is a valid `W₀` (`rg_theorem_21_1_3_maxBox`).
* `rg_BCL`: the operator `B` of Cronshaw–Luenberger with the worst punishment
  `w̲ᵢ = inf_{w ∈ W} wᵢ`; it equals `B` on compact sets (`rg_BCL_eq`), and `V` is its largest
  compact fixed point (`rg_cronshaw_luenberger`).
* `rg_Bstar W = co B(co W)` (Judd–Yeltekin–Conklin) is monotone (`rg_Bstar_mono`). Its
  compactness-preservation is not formalised: Mathlib v4.34.0 lacks compactness of the convex
  hull of a compact set (Carathéodory).
-/

namespace Miao.DynamicGames

open Filter Topology

variable {ι : Type*} {A : ι → Type*}

/-- A compact subset of `ℝⁿ` is bounded (`n` finite). -/
theorem rg_bdd_of_isCompact [Finite ι] {W : Set (ι → ℝ)} (hW : IsCompact W) : rg_Bdd W := by
  have := Fintype.ofFinite ι
  have hb : ∀ j, BddAbove ((fun x : ι → ℝ => |x j|) '' W) := fun j =>
    hW.bddAbove_image (continuous_abs.comp (continuous_apply j)).continuousOn
  choose C hC using hb
  refine ⟨∑ j, |C j|, fun x hx j => ?_⟩
  have h1 : |x j| ≤ C j := hC j ⟨x, hx, rfl⟩
  have h2 : |C j| ≤ ∑ k, |C k| :=
    Finset.single_le_sum (f := fun k => |C k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
  linarith [le_abs_self (C j)]

/-- **Theorem 21.1.3** (Miao, p. 746). With finitely many players and finite action sets, let
`W₀ ⊇ V` be compact with `B(W₀) ⊆ W₀`. Then every `Wₜ = Bᵗ(W₀)` is compact,
`V ⊆ ⋯ ⊆ W₂ ⊆ W₁ ⊆ W₀`, and `V = ⋂ₜ Wₜ`. -/
theorem theorem_21_1_3 [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W0 : Set (ι → ℝ)}
    (hW0 : IsCompact W0) (hVW : rg_V δ u ⊆ W0) (hBW : rg_B δ u W0 ⊆ W0) :
    (∀ t, IsCompact ((rg_B δ u)^[t] W0)) ∧
      (∀ t, (rg_B δ u)^[t + 1] W0 ⊆ (rg_B δ u)^[t] W0) ∧
      (∀ t, rg_V δ u ⊆ (rg_B δ u)^[t] W0) ∧ rg_V δ u = ⋂ t, (rg_B δ u)^[t] W0 := by
  set Wt : ℕ → Set (ι → ℝ) := fun t => (rg_B δ u)^[t] W0 with hWt
  have hsucc : ∀ t, Wt (t + 1) = rg_B δ u (Wt t) := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hc : ∀ t, IsCompact (Wt t) := by
    intro t
    induction t with
    | zero => exact hW0
    | succ t ih => rw [hsucc]; exact lemma_21_1_4 hδ0 ih
  have hstep : ∀ t, Wt (t + 1) ⊆ Wt t := by
    intro t
    induction t with
    | zero => exact hBW
    | succ t ih =>
      rw [hsucc, hsucc]
      rw [hsucc] at ih
      exact lemma_21_1_3 δ u ih
  have hV : ∀ t, rg_V δ u ⊆ Wt t := by
    intro t
    induction t with
    | zero => exact hVW
    | succ t ih =>
      rw [hsucc, theorem_21_1_1 hM hδ0 hδ1]
      exact lemma_21_1_3 δ u ih
  have hanti : Antitone Wt := antitone_nat_of_succ_le hstep
  refine ⟨hc, hstep, hV, Set.Subset.antisymm (Set.subset_iInter hV) ?_⟩
  set K := ⋂ t, Wt t with hK
  have hKW0 : K ⊆ W0 := Set.iInter_subset Wt 0
  have hKB : K ⊆ rg_B δ u K := by
    intro v hv
    have hvt : ∀ t, v ∈ rg_B δ u (Wt t) := fun t => hsucc t ▸ Set.mem_iInter.1 hv (t + 1)
    choose a w hadm hveq using hvt
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber a
    have hinf : (a ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
    classical
    let S : ℕ → Set (rg_Prof A → ι → ℝ) := fun t =>
      (⋂ a', {w' | w' a' ∈ Wt t}) ∩ ((⋂ (i : ι), ⋂ (x : A i), {w' | (1 - δ) * u (rg_upd y i x) i +
        δ * w' (rg_upd y i x) i ≤ (1 - δ) * u y i + δ * w' y i}) ∩
        {w' | v = fun j => (1 - δ) * u y j + δ * w' y j})
    have hSmem : ∀ t w', w' ∈ S t ↔ rg_Admissible δ u (Wt t) y w' ∧
        v = fun j => (1 - δ) * u y j + δ * w' y j := by
      intro t w'
      simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, rg_Admissible,
        and_assoc]
    have hSne : ∀ t, (S t).Nonempty := by
      intro t
      obtain ⟨s, hs, hts⟩ := hinf.exists_gt t
      have hys : a s = y := hs
      refine ⟨w s, (hSmem t (w s)).2 ⟨⟨fun a' => hanti hts.le ((hadm s).1 a'), ?_⟩, ?_⟩⟩
      · rw [← hys]
        exact (hadm s).2
      · rw [← hys]
        exact hveq s
    have hScl : ∀ t, IsClosed (S t) := by
      intro t
      refine (isClosed_iInter fun a' => (hc t).isClosed.preimage (continuous_apply a')).inter
        ((isClosed_iInter fun i => isClosed_iInter fun x => isClosed_le ?_ ?_).inter ?_)
      · exact continuous_const.add
          (continuous_const.mul ((continuous_apply i).comp (continuous_apply _)))
      · exact continuous_const.add
          (continuous_const.mul ((continuous_apply i).comp (continuous_apply _)))
      · exact isClosed_eq continuous_const (continuous_pi fun j => continuous_const.add
          (continuous_const.mul ((continuous_apply j).comp (continuous_apply y))))
    have hSstep : ∀ t, S (t + 1) ⊆ S t := by
      intro t w' hw'
      rw [hSmem] at hw' ⊢
      exact ⟨⟨fun a' => hstep t (hw'.1.1 a'), hw'.1.2⟩, hw'.2⟩
    have hS0 : IsCompact (S 0) :=
      (isCompact_univ_pi fun _ => hW0).of_isClosed_subset (hScl 0)
        fun w' hw' a' _ => ((hSmem 0 w').1 hw').1.1 a'
    obtain ⟨w', hw'⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSstep hSne hS0 hScl
    have hw't : ∀ t, w' ∈ S t := Set.mem_iInter.1 hw'
    refine ⟨y, w', ⟨fun a' => Set.mem_iInter.2 fun t => ((hSmem t w').1 (hw't t)).1.1 a',
      ((hSmem 0 w').1 (hw't 0)).1.2⟩, ((hSmem 0 w').1 (hw't 0)).2⟩
  have hKb : rg_Bdd K := by
    obtain ⟨C, hC⟩ := rg_bdd_of_isCompact hW0
    exact ⟨C, fun x hx => hC x (hKW0 hx)⟩
  exact hKB.trans (lemma_21_1_2 hM hδ0 hδ1 hKb hKB)

/-- **Theorem 21.1.3** (Miao, p. 746), `V = lim_{t→∞} Bᵗ(W₀)`: the decreasing compact sets
`Bᵗ(W₀)` converge to `V` in the Hausdorff distance. -/
theorem theorem_21_1_3_hausdorff [Fintype ι] [∀ i, Finite (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {W0 : Set (ι → ℝ)} (hW0 : IsCompact W0) (hVW : rg_V δ u ⊆ W0) (hBW : rg_B δ u W0 ⊆ W0) :
    Tendsto (fun t => Metric.hausdorffDist ((rg_B δ u)^[t] W0) (rg_V δ u)) atTop (𝓝 0) := by
  obtain ⟨hc, hstep, hV, heq⟩ := theorem_21_1_3 hM hδ0 hδ1 hW0 hVW hBW
  set Wt : ℕ → Set (ι → ℝ) := fun t => (rg_B δ u)^[t] W0 with hWt
  have hanti : Antitone Wt := antitone_nat_of_succ_le hstep
  rcases (rg_V δ u).eq_empty_or_nonempty with hVe | _
  · simp only [hVe, Metric.hausdorffDist_empty]
    exact tendsto_const_nhds
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℕ → Set (ι → ℝ) := fun t => Wt t ∩ {x | ε / 2 ≤ Metric.infDist x (rg_V δ u)}
  have hCcl : ∀ t, IsClosed (C t) := fun t =>
    (hc t).isClosed.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt _))
  have hCstep : ∀ t, C (t + 1) ⊆ C t := fun t =>
    Set.inter_subset_inter_left _ (hstep t)
  obtain ⟨T, hT⟩ : ∃ T, C T = ∅ := by
    by_contra hne
    push Not at hne
    have hne' : ∀ t, (C t).Nonempty := hne
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCstep
      hne' ((hc 0).of_isClosed_subset (hCcl 0) Set.inter_subset_left) hCcl
    have hxt : ∀ t, x ∈ C t := Set.mem_iInter.1 hx
    have hxV : x ∈ rg_V δ u := by
      rw [heq]
      exact Set.mem_iInter.2 fun t => (hxt t).1
    have := (hxt 0).2
    simp only [Set.mem_ofPred_eq, Metric.infDist_zero_of_mem hxV] at this
    linarith
  refine ⟨T, fun n hn => ?_⟩
  have hlt : ∀ x ∈ Wt n, Metric.infDist x (rg_V δ u) < ε / 2 := by
    intro x hx
    by_contra hge
    have : x ∈ C T := ⟨hanti hn hx, not_lt.1 hge⟩
    rw [hT] at this
    exact this
  have hle : Metric.hausdorffDist (Wt n) (rg_V δ u) ≤ ε / 2 :=
    Metric.hausdorffDist_le_of_infDist (by linarith) (fun x hx => (hlt x hx).le)
      (fun x hx => by rw [Metric.infDist_zero_of_mem (hV n hx)]; linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
  linarith

/-- `uᵢ min = min_{a ∈ A} uᵢ(a)` (Miao, p. 747). -/
noncomputable def rg_umin (u : rg_Prof A → ι → ℝ) (i : ι) : ℝ := ⨅ a, u a i

/-- `uᵢ max = max_{a ∈ A} uᵢ(a)` (Miao, p. 747). -/
noncomputable def rg_umax (u : rg_Prof A → ι → ℝ) (i : ι) : ℝ := ⨆ a, u a i

/-- The maximal payoff set `W = ×ᵢ [uᵢ min, uᵢ max]` (Miao, p. 747). -/
def rg_maxBox (u : rg_Prof A → ι → ℝ) : Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Icc (rg_umin u i) (rg_umax u i)

/-- Every stage payoff lies in the maximal payoff set (finite `A`). -/
theorem rg_u_mem_maxBox [Finite (rg_Prof A)] (u : rg_Prof A → ι → ℝ) (a : rg_Prof A) :
    u a ∈ rg_maxBox u := by
  refine Set.mem_univ_pi.2 fun i => ⟨?_, ?_⟩
  · exact ciInf_le (Set.finite_range fun a => u a i).bddBelow a
  · exact le_ciSup (Set.finite_range fun a => u a i).bddAbove a

/-- The maximal payoff set is compact. -/
theorem rg_maxBox_isCompact (u : rg_Prof A → ι → ℝ) : IsCompact (rg_maxBox u) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- `V` lies in the maximal payoff set (finite `A`). -/
theorem rg_V_subset_maxBox [Finite (rg_Prof A)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_V δ u ⊆ rg_maxBox u := by
  rintro v ⟨σ, -, rfl⟩
  refine Set.mem_univ_pi.2 fun i => ?_
  have h := fun t => Set.mem_univ_pi.1 (rg_u_mem_maxBox u (rg_path σ t)) i
  exact rg_pathPay_mem hM hδ0 hδ1 _ i (fun t => (h t).1) (fun t => (h t).2)

/-- `B` maps the maximal payoff set into itself (finite `A`). -/
theorem rg_B_maxBox_subset [Finite (rg_Prof A)] {δ : ℝ} {u : rg_Prof A → ι → ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : rg_B δ u (rg_maxBox u) ⊆ rg_maxBox u :=
  rg_B_subset_of_convex hδ0 hδ1 (convex_pi fun _ _ => convex_Icc _ _) (rg_u_mem_maxBox u)
    le_rfl

/-- Miao, p. 747: the maximal payoff set is a valid starting point for Theorem 21.1.3, so
`V = ⋂ₜ Bᵗ(×ᵢ [uᵢ min, uᵢ max])`. -/
theorem rg_theorem_21_1_3_maxBox [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    rg_V δ u = ⋂ t, (rg_B δ u)^[t] (rg_maxBox u) :=
  (theorem_21_1_3 hM hδ0 hδ1 (rg_maxBox_isCompact u) (rg_V_subset_maxBox hM hδ0 hδ1)
    (rg_B_maxBox_subset hδ0 hδ1)).2.2.2

/-- The operator of Cronshaw and Luenberger (Miao, p. 747): `B(W)` is the set of
`(1 − δ) u(a) + δ w` with `w ∈ W` satisfying `ICᵢ` for all `i`:
`(1 − δ) uᵢ(a) + δ wᵢ ≥ (1 − δ) uᵢ(a'ᵢ, a₋ᵢ) + δ w̲ᵢ` for all `a'ᵢ`, `w̲ᵢ = inf_{w ∈ W} wᵢ`. -/
noncomputable def rg_BCL (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | ∃ a, ∃ w ∈ W, (v = fun j => (1 - δ) * u a j + δ * w j) ∧ ∀ (i : ι) (x : A i),
    (1 - δ) * u (rg_upd a i x) i + δ * sInf ((fun y : ι → ℝ => y i) '' W) ≤
      (1 - δ) * u a i + δ * w i}

/-- On compact sets the Cronshaw–Luenberger operator is the APS operator `B`. -/
theorem rg_BCL_eq {δ : ℝ} {u : rg_Prof A → ι → ℝ} (hδ0 : 0 ≤ δ) {W : Set (ι → ℝ)}
    (hW : IsCompact W) : rg_BCL δ u W = rg_B δ u W := by
  rcases W.eq_empty_or_nonempty with rfl | hne
  · ext v
    simp only [rg_BCL, Set.mem_empty_iff_false, false_and, exists_false, Set.mem_ofPred_eq,
      false_iff]
    rintro ⟨a, w, ⟨hw, -⟩, -⟩
    exact hw a
  have hmin : ∀ i, ∃ x ∈ W, IsMinOn (fun y : ι → ℝ => y i) W x := fun i =>
    hW.exists_isMinOn hne (continuous_apply i).continuousOn
  choose p hpW hpmin using hmin
  have hp : ∀ i, p i ∈ W ∧ ∀ x ∈ W, p i i ≤ x i := fun i => ⟨hpW i, fun x hx => hpmin i hx⟩
  have hinf : ∀ i, sInf ((fun y : ι → ℝ => y i) '' W) = p i i := fun i =>
    IsLeast.csInf_eq ⟨⟨p i, hpW i, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact (hp i).2 x hx⟩
  ext v
  rw [rg_mem_B_iff_punish hδ0 hp]
  simp only [rg_BCL, Set.mem_ofPred_eq, hinf]

/-- Cronshaw and Luenberger (Miao, p. 747): with finitely many players and finite action sets,
`V` lies in the maximal payoff set, is a fixed point of their operator, and contains every
compact `W` with `W ⊆ B(W)`; so `V` is its largest compact fixed point. -/
theorem rg_cronshaw_luenberger [Finite ι] [∀ i, Finite (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    rg_V δ u ⊆ rg_maxBox u ∧ rg_V δ u = rg_BCL δ u (rg_V δ u) ∧
      ∀ W, IsCompact W → W ⊆ rg_BCL δ u W → W ⊆ rg_V δ u := by
  refine ⟨rg_V_subset_maxBox hM hδ0 hδ1, ?_, fun W hW hWB => ?_⟩
  · rw [rg_BCL_eq hδ0 (proposition_21_1_2 hM hδ0 hδ1)]
    exact theorem_21_1_1 hM hδ0 hδ1
  · rw [rg_BCL_eq hδ0 hW] at hWB
    exact hWB.trans (lemma_21_1_2 hM hδ0 hδ1 (rg_bdd_of_isCompact hW) hWB)

/-- The operator `B*(co W) = co B(co W)` of Judd, Yeltekin and Conklin (Miao, p. 747). -/
noncomputable def rg_Bstar (δ : ℝ) (u : rg_Prof A → ι → ℝ) (W : Set (ι → ℝ)) :
    Set (ι → ℝ) :=
  convexHull ℝ (rg_B δ u (convexHull ℝ W))

/-- Miao, p. 747: `B*` is monotone. -/
theorem rg_Bstar_mono (δ : ℝ) (u : rg_Prof A → ι → ℝ) {W W' : Set (ι → ℝ)} (h : W ⊆ W') :
    rg_Bstar δ u W ⊆ rg_Bstar δ u W' :=
  convexHull_mono (lemma_21_1_3 δ u (convexHull_mono h))

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Simple strategies

Miao, §21.1.4, pp. 748–749: Definition 21.1.5, Proposition 21.1.3 and Abreu's result that every
SPE payoff is supported by a simple strategy profile with the harshest punishments.

* Automaton strategies (`rg_autState`, `rg_autStrat`): a state `s`, an output `f s` and a
  transition `τ s a`. Their continuation strategies are automaton strategies started at the
  current state (`rg_cont_autStrat`), and the one-shot deviation principle reduces to one
  inequality per state (`rg_aut_isSPE`, `rg_aut_ic_of_isSPE`).
* `rg_simpleStrat Q` (Definition 21.1.5): the states are `(k, t)` = "on path `Qᵏ` at its date
  `t`" (`k = none` is `Q⁰`, `k = some j` is `Qʲ`); `rg_devBy b a` names the unique player whose
  unilateral deviation turns `b` into `a`.
* `rg_pathVal δ u Q k t = Uⱼ(Qᵏ; t + 1)` of the book (dates from `0` here).
* `proposition_21_1_3`: the simple strategy is an SPE iff, for all `k, t, j` and all
  `a'ⱼ ≠ aᵏⱼ(t)`, `(1 − δ) uⱼ(a'ⱼ, aᵏ₋ⱼ(t)) + δ Uⱼ(Qʲ; 1) ≤ (1 − δ) uⱼ(aᵏ(t)) + δ Uⱼ(Qᵏ; t + 1)`
  (every player having at least two actions, for "only if"; "if" holds always:
  `rg_proposition_21_1_3_if`).
* Corrections. The printed condition has `Uⱼ(Qʲ; t + 1)` where the punishment restarts,
  `Uⱼ(Qʲ; 1)`, and quantifies over all `a'ⱼ ∈ Aⱼ` including `aᵏⱼ(t)`. Both are false:
  `rg_proposition_21_1_3_misprint_restart` (repeated prisoner's dilemma, `δ = 9/10`, a two-period
  stick-and-carrot punishment) and `rg_proposition_21_1_3_misprint_own` (a game in which the
  punishment path of player 1 is better for him than the equilibrium path).
* `rg_abreu_simple` (p. 749): with compact action sets and continuous payoffs, every SPE `σ*` is
  matched in payoff by an SPE simple strategy whose punishment paths `Qʲ` give player `j` his
  minimal SPE payoff.
-/

namespace Miao.DynamicGames

variable {ι : Type*} {A : ι → Type*}

/-- The state of an automaton after a history: `s(∅) = s₀`, `s(h, a) = τ(s(h), a)`. -/
def rg_autState {S : Type*} (s0 : S) (τ : S → rg_Prof A → S) : rg_Hist A → S
  | [] => s0
  | a :: h => τ (rg_autState s0 τ h) a

/-- The strategy profile of an automaton: play `f(s(h))` after `h`. -/
def rg_autStrat {S : Type*} (s0 : S) (f : S → rg_Prof A) (τ : S → rg_Prof A → S) :
    rg_Strat A :=
  fun h => f (rg_autState s0 τ h)

/-- The state after `(h, h')` is the state after `h'` started from the state after `h`. -/
theorem rg_autState_append {S : Type*} (s0 : S) (τ : S → rg_Prof A → S) (h h' : rg_Hist A) :
    rg_autState s0 τ (h' ++ h) = rg_autState (rg_autState s0 τ h) τ h' := by
  induction h' with
  | nil => rfl
  | cons a h' ih => simp only [List.cons_append, rg_autState, ih]

/-- The continuation of an automaton strategy is the automaton started at the current state. -/
theorem rg_cont_autStrat {S : Type*} (s0 : S) (f : S → rg_Prof A) (τ : S → rg_Prof A → S)
    (h : rg_Hist A) : rg_cont (rg_autStrat s0 f τ) h = rg_autStrat (rg_autState s0 τ h) f τ := by
  funext h'
  simp only [rg_cont, rg_autStrat, rg_autState_append]

/-- The recursion of automaton values: `U(s) = (1 − δ) u(f s) + δ U(τ(s, f s))`. -/
theorem rg_autVal_rec {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {S : Type*} (f : S → rg_Prof A) (τ : S → rg_Prof A → S)
    (s : S) (j : ι) :
    rg_U δ u (rg_autStrat s f τ) j =
      (1 - δ) * u (f s) j + δ * rg_U δ u (rg_autStrat (τ s (f s)) f τ) j := by
  rw [rg_U_rec hM hδ0 hδ1, rg_cont_autStrat]
  rfl

/-- One-shot deviation principle for automata: if a set `R` of states contains `s₀`, is closed
under transitions, and no player gains from a one-period deviation at a state of `R`, the
automaton strategy is an SPE. -/
theorem rg_aut_isSPE {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {S : Type*} (s0 : S) (f : S → rg_Prof A)
    (τ : S → rg_Prof A → S) (R : Set S) (hs0 : s0 ∈ R) (hR : ∀ s ∈ R, ∀ a, τ s a ∈ R)
    (hic : ∀ s ∈ R, ∀ (i : ι) (x : A i), x ≠ f s i →
      (1 - δ) * u (rg_upd (f s) i x) i + δ * rg_U δ u (rg_autStrat (τ s (rg_upd (f s) i x)) f τ) i
        ≤ rg_U δ u (rg_autStrat s f τ) i) :
    rg_IsSPE δ u (rg_autStrat s0 f τ) := by
  have hreach : ∀ h, rg_autState s0 τ h ∈ R := by
    intro h
    induction h with
    | nil => exact hs0
    | cons a h ih => exact hR _ ih a
  rw [proposition_21_1_1 hM hδ0 hδ1]
  intro i hbar τ' hτ' hp
  unfold rg_IsProfitable at hp
  rw [definition_21_1_2 hM hδ0 hδ1 _ i hbar τ' hτ'.2, rg_cont_autStrat, rg_cont_autStrat] at hp
  exact absurd (hic _ (hreach hbar) i (τ' hbar) hτ'.1) (not_le.2 hp)

/-- Conversely, in an SPE automaton no one-period deviation pays at any reachable state. -/
theorem rg_aut_ic_of_isSPE {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {S : Type*} (s0 : S) (f : S → rg_Prof A)
    (τ : S → rg_Prof A → S) (hσ : rg_IsSPE δ u (rg_autStrat s0 f τ)) (h : rg_Hist A) (i : ι)
    (x : A i) :
    (1 - δ) * u (rg_upd (f (rg_autState s0 τ h)) i x) i +
        δ * rg_U δ u (rg_autStrat (τ (rg_autState s0 τ h) (rg_upd (f (rg_autState s0 τ h)) i x))
          f τ) i ≤
      rg_U δ u (rg_autStrat (rg_autState s0 τ h) f τ) i := by
  have := rg_oneShot_le_of_isSPE hM hδ0 hδ1 hσ i h x
  rw [rg_cont_autStrat, rg_cont_autStrat] at this
  exact this

open Classical in
/-- The player whose unilateral deviation turns the prescribed profile `b` into `a`, if any. -/
noncomputable def rg_devBy (b a : rg_Prof A) : Option ι :=
  if h : ∃ j, ∃ x : A j, a = rg_upd b j x ∧ a ≠ b then some h.choose else none

/-- No deviation: `devBy(b, b) = none`. -/
theorem rg_devBy_self (b : rg_Prof A) : rg_devBy b b = none := by
  simp [rg_devBy]

/-- A unilateral deviation by `j` is attributed to `j`. -/
theorem rg_devBy_upd (b : rg_Prof A) (j : ι) {x : A j} (hx : x ≠ b j) :
    rg_devBy b (rg_upd b j x) = some j := by
  have hne : rg_upd b j x ≠ b := fun h => hx (by rw [← congrFun h j, rg_upd_self])
  have hex : ∃ k, ∃ y : A k, rg_upd b j x = rg_upd b k y ∧ rg_upd b j x ≠ b :=
    ⟨j, x, rfl, hne⟩
  have hd : rg_devBy b (rg_upd b j x) = some hex.choose := by
    unfold rg_devBy
    split_ifs
    rfl
  obtain ⟨y, hy, -⟩ := hex.choose_spec
  rw [hd, rg_upd_player_eq b x y hy hne]

/-- A profile that is no unilateral deviation from `b` is attributed to nobody. -/
theorem rg_devBy_none (b a : rg_Prof A) (h : ¬ ∃ j, ∃ x : A j, a = rg_upd b j x) :
    rg_devBy b a = none := by
  unfold rg_devBy
  split_ifs with h'
  · obtain ⟨j, x, hx, -⟩ := h'
    exact absurd ⟨j, x, hx⟩ h
  · rfl

/-- The transitions of the simple strategy `σ(Q⁰, …, Qⁿ)` (Definition 21.1.5): on path `Qᵏ` at
its date `t`, a unilateral deviation by `j` starts `Qʲ`; otherwise `Qᵏ` continues. -/
noncomputable def rg_simpleTrans (Q : Option ι → ℕ → rg_Prof A) (s : Option ι × ℕ)
    (a : rg_Prof A) : Option ι × ℕ :=
  match rg_devBy (Q s.1 s.2) a with
  | some j => (some j, 0)
  | none => (s.1, s.2 + 1)

/-- Definition 21.1.5 (Miao, p. 748): the simple strategy profile `σ(Q⁰, Q¹, …, Qⁿ)`; `Q none`
is `Q⁰` and `Q (some j)` is `Qʲ`. -/
noncomputable def rg_simpleStrat (Q : Option ι → ℕ → rg_Prof A) : rg_Strat A :=
  rg_autStrat (none, 0) (fun s => Q s.1 s.2) (rg_simpleTrans Q)

/-- **Definition 21.1.5** (Miao, p. 748): (i) play starts on `Q⁰`; on path `Qᵏ` at date `t`,
(ii) the prescribed play continues `Qᵏ`, a unilateral deviation by `j` starts `Qʲ`, and a
simultaneous deviation by more than one player continues `Qᵏ`. -/
theorem definition_21_1_5 (Q : Option ι → ℕ → rg_Prof A) (k : Option ι) (t : ℕ) :
    rg_simpleStrat Q [] = Q none 0 ∧
      rg_simpleTrans Q (k, t) (Q k t) = (k, t + 1) ∧
      (∀ (j : ι) (x : A j), x ≠ Q k t j →
        rg_simpleTrans Q (k, t) (rg_upd (Q k t) j x) = (some j, 0)) ∧
      ∀ a, (¬ ∃ j, ∃ x : A j, a = rg_upd (Q k t) j x) → rg_simpleTrans Q (k, t) a = (k, t + 1) := by
  refine ⟨rfl, ?_, fun j x hx => ?_, fun a ha => ?_⟩
  · simp [rg_simpleTrans, rg_devBy_self]
  · simp [rg_simpleTrans, rg_devBy_upd _ j hx]
  · simp [rg_simpleTrans, rg_devBy_none _ a ha]

/-- `Uⱼ(Qᵏ; t + 1) = (1 − δ) Σ_{s ≥ 1} δ^{s−1} uⱼ(aᵏ(t + s))` (Miao, p. 748), with dates
from `0`: the value of path `Qᵏ` from its date `t` on. -/
noncomputable def rg_pathVal (δ : ℝ) (u : rg_Prof A → ι → ℝ) (Q : Option ι → ℕ → rg_Prof A)
    (k : Option ι) (t : ℕ) : ι → ℝ :=
  rg_pathPay δ u (fun s => Q k (t + s))

/-- `Uⱼ(Qᵏ; t + 1) = (1 − δ) uⱼ(aᵏ(t)) + δ Uⱼ(Qᵏ; t + 2)`. -/
theorem rg_pathVal_succ {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (Q : Option ι → ℕ → rg_Prof A) (k : Option ι) (t : ℕ)
    (j : ι) :
    rg_pathVal δ u Q k t j = (1 - δ) * u (Q k t) j + δ * rg_pathVal δ u Q k (t + 1) j := by
  unfold rg_pathVal
  rw [rg_pathPay_succ hM hδ0 hδ1]
  have : (fun s => Q k (t + (s + 1))) = fun s => Q k (t + 1 + s) := by
    funext s
    rw [Nat.add_assoc, Nat.add_comm 1 s]
  rw [this, Nat.add_zero]

/-- On the simple strategy started at `(k, t)`, play follows `Qᵏ` from date `t`. -/
theorem rg_simple_state_hist (Q : Option ι → ℕ → rg_Prof A) (k : Option ι) (t s : ℕ) :
    rg_autState (k, t) (rg_simpleTrans Q)
      (rg_hist (rg_autStrat (k, t) (fun s => Q s.1 s.2) (rg_simpleTrans Q)) s) = (k, t + s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [rg_hist, rg_autState, rg_autStrat, ih]
    simp [rg_simpleTrans, rg_devBy_self, Nat.add_assoc]

/-- The value of the simple strategy at `(k, t)` is `U(Qᵏ; t + 1)`. -/
theorem rg_simple_val (δ : ℝ) (u : rg_Prof A → ι → ℝ) (Q : Option ι → ℕ → rg_Prof A)
    (k : Option ι) (t : ℕ) :
    rg_U δ u (rg_autStrat (k, t) (fun s => Q s.1 s.2) (rg_simpleTrans Q)) =
      rg_pathVal δ u Q k t := by
  unfold rg_U rg_pathVal
  congr 1
  funext s
  simp only [rg_path]
  conv_lhs => simp only [rg_autStrat]
  rw [rg_simple_state_hist]

/-- The payoff of `σ(Q⁰, …, Qⁿ)` is `U(Q⁰; 1)`. -/
theorem rg_simple_payoff (δ : ℝ) (u : rg_Prof A → ι → ℝ) (Q : Option ι → ℕ → rg_Prof A) :
    rg_U δ u (rg_simpleStrat Q) = rg_pathVal δ u Q none 0 :=
  rg_simple_val δ u Q none 0

/-- Every state `(k, t)` of a simple strategy is reached when every player has at least two
actions. -/
theorem rg_simple_reach [∀ j, Nontrivial (A j)] (Q : Option ι → ℕ → rg_Prof A) (k : Option ι)
    (t : ℕ) : ∃ h, rg_autState (none, 0) (rg_simpleTrans Q) h = (k, t) := by
  cases k with
  | none =>
    refine ⟨rg_hist (rg_simpleStrat Q) t, ?_⟩
    have := rg_simple_state_hist Q none 0 t
    rwa [Nat.zero_add] at this
  | some j =>
    obtain ⟨x, hx⟩ := exists_ne (Q none 0 j)
    refine ⟨rg_hist (rg_autStrat (some j, 0) (fun s => Q s.1 s.2) (rg_simpleTrans Q)) t ++
      [rg_upd (Q none 0) j x], ?_⟩
    rw [rg_autState_append]
    have h0 : rg_autState (none, 0) (rg_simpleTrans Q) [rg_upd (Q none 0) j x] = (some j, 0) :=
      (definition_21_1_5 Q none 0).2.2.1 j x hx
    rw [h0, rg_simple_state_hist, Nat.zero_add]

/-- The "if" half of Proposition 21.1.3 (corrected), with no assumption on the action sets. -/
theorem rg_proposition_21_1_3_if {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (Q : Option ι → ℕ → rg_Prof A)
    (hQ : ∀ (k : Option ι) (t : ℕ) (j : ι) (x : A j), x ≠ Q k t j →
      (1 - δ) * u (rg_upd (Q k t) j x) j + δ * rg_pathVal δ u Q (some j) 0 j ≤
        (1 - δ) * u (Q k t) j + δ * rg_pathVal δ u Q k (t + 1) j) :
    rg_IsSPE δ u (rg_simpleStrat Q) := by
  refine rg_aut_isSPE hM hδ0 hδ1 _ _ _ Set.univ trivial (fun _ _ _ => trivial) ?_
  rintro ⟨k, t⟩ - i x hx
  rw [(definition_21_1_5 Q k t).2.2.1 i x hx, rg_simple_val, rg_simple_val,
    rg_pathVal_succ hM hδ0 hδ1 Q k t i]
  exact hQ k t i x hx

/-- **Proposition 21.1.3** (Miao, p. 748), corrected. If every player has at least two actions,
the simple strategy profile `σ(Q⁰, …, Qⁿ)` is an SPE iff
`(1 − δ) uⱼ(a'ⱼ, aᵏ₋ⱼ(t)) + δ Uⱼ(Qʲ; 1) ≤ (1 − δ) uⱼ(aᵏ(t)) + δ Uⱼ(Qᵏ; t + 1)` for all
`a'ⱼ ≠ aᵏⱼ(t)`, all `j`, all paths `k = 0, …, n` and all dates `t`. -/
theorem proposition_21_1_3 [∀ j, Nontrivial (A j)] {δ M : ℝ} {u : rg_Prof A → ι → ℝ}
    (hM : ∀ a j, |u a j| ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (Q : Option ι → ℕ → rg_Prof A) :
    rg_IsSPE δ u (rg_simpleStrat Q) ↔
      ∀ (k : Option ι) (t : ℕ) (j : ι) (x : A j), x ≠ Q k t j →
        (1 - δ) * u (rg_upd (Q k t) j x) j + δ * rg_pathVal δ u Q (some j) 0 j ≤
          (1 - δ) * u (Q k t) j + δ * rg_pathVal δ u Q k (t + 1) j := by
  refine ⟨fun hσ k t j x hx => ?_, rg_proposition_21_1_3_if hM hδ0 hδ1 Q⟩
  obtain ⟨h, hh⟩ := rg_simple_reach Q k t
  have := rg_aut_ic_of_isSPE hM hδ0 hδ1 _ _ _ hσ h j x
  rw [hh] at this
  simp only at this
  rw [(definition_21_1_5 Q k t).2.2.1 j x hx, rg_simple_val, rg_simple_val,
    rg_pathVal_succ hM hδ0 hδ1 Q k t j] at this
  exact this

/-- The payoff of a constant path is the stage payoff. -/
theorem rg_pathPay_const {δ M : ℝ} {u : rg_Prof A → ι → ℝ} (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (b : rg_Prof A) (j : ι) :
    rg_pathPay δ u (fun _ => b) j = u b j := by
  obtain ⟨h1, h2⟩ := rg_pathPay_mem hM hδ0 hδ1 (fun _ => b) j (fun _ => le_rfl) (fun _ => le_rfl)
  exact le_antisymm h2 h1

/-- The stick-and-carrot paths of `rg_proposition_21_1_3_misprint_restart`: `Q⁰ = (C, C)`
forever, and `Qʲ = (D, D), (D, D), (C, C), (C, C), …` for each player. -/
def rg_pdStick (k : Option (Fin 2)) (t : ℕ) : rg_Prof (fun _ : Fin 2 => Bool) :=
  if k = none ∨ 2 ≤ t then fun _ => true else fun _ => false

/-- The path values of the stick-and-carrot paths for `δ = 9/10`: `1` on `(C, C)` stretches,
`9/10` one period before them, `81/100` two periods before. -/
theorem rg_pdStick_val (k : Option (Fin 2)) (t : ℕ) (j : Fin 2) :
    rg_pathVal (9 / 10) rg_pdU rg_pdStick k t j =
      if k = none ∨ 2 ≤ t then 1 else if t = 1 then 9 / 10 else 81 / 100 := by
  have hδ0 : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hδ1 : (9 / 10 : ℝ) < 1 := by norm_num
  have hcar : ∀ k t, (k = none ∨ 2 ≤ t) → rg_pathVal (9 / 10) rg_pdU rg_pdStick k t j = 1 := by
    intro k t hkt
    have : (fun s => rg_pdStick k (t + s)) = fun _ => fun _ => true := by
      funext s
      have : k = none ∨ 2 ≤ t + s := by
        rcases hkt with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      unfold rg_pdStick
      simp only [this, ↓reduceIte]
    unfold rg_pathVal
    rw [this, rg_pathPay_const rg_pd_bound hδ0 hδ1]
    simp [rg_pdU, rg_pdPay]
  by_cases hkt : k = none ∨ 2 ≤ t
  · simp only [hkt, ↓reduceIte, hcar k t hkt]
  · simp only [hkt, ↓reduceIte]
    obtain ⟨j', rfl⟩ : ∃ j', k = some j' := Option.ne_none_iff_exists'.1 (by tauto)
    have hDD : ∀ s, s < 2 → rg_pdU (rg_pdStick (some j') s) j = 0 := by
      intro s hs
      have : ¬ (some j' = none ∨ 2 ≤ s) := by simp; omega
      unfold rg_pdStick
      simp only [this, ↓reduceIte]
      simp [rg_pdU, rg_pdPay]
    have h1 : rg_pathVal (9 / 10) rg_pdU rg_pdStick (some j') 1 j = 9 / 10 := by
      rw [rg_pathVal_succ rg_pd_bound hδ0 hδ1, hDD 1 (by norm_num),
        hcar _ 2 (Or.inr le_rfl)]
      norm_num
    by_cases ht : t = 1
    · simp only [ht, ↓reduceIte, h1]
    · simp only [ht, ↓reduceIte]
      have ht0 : t = 0 := by omega
      rw [ht0, rg_pathVal_succ rg_pd_bound hδ0 hδ1, hDD 0 (by norm_num), h1]
      norm_num

/-- Correction to Proposition 21.1.3: after a deviation by `j` the punishment `Qʲ` restarts, so
the condition involves `Uⱼ(Qʲ; 1)`, not the printed `Uⱼ(Qʲ; t + 1)`. In the repeated prisoner's
dilemma with `δ = 9/10`, the simple strategy with `Q⁰ = (C, C)` forever and the two-period
stick-and-carrot punishments `Qʲ` is an SPE, but the printed condition fails at `t = 1` (book
dates), even restricted to `a'ⱼ ≠ aᵏⱼ(t)`. -/
theorem rg_proposition_21_1_3_misprint_restart :
    rg_IsSPE (9 / 10) rg_pdU (rg_simpleStrat rg_pdStick) ∧
      ¬ ∀ (k : Option (Fin 2)) (t : ℕ) (j : Fin 2) (x : Bool), x ≠ rg_pdStick k t j →
        (1 - 9 / 10) * rg_pdU (rg_upd (rg_pdStick k t) j x) j +
            9 / 10 * rg_pathVal (9 / 10) rg_pdU rg_pdStick (some j) (t + 1) j ≤
          (1 - 9 / 10) * rg_pdU (rg_pdStick k t) j +
            9 / 10 * rg_pathVal (9 / 10) rg_pdU rg_pdStick k (t + 1) j := by
  have hdevC : ∀ j : Fin 2, rg_pdU (rg_upd (fun _ => true) j false) j = 2 := by
    intro j
    rw [rg_pd_upd]
    fin_cases j <;> simp [rg_pdU, rg_pdPay]
  have hdevD : ∀ j : Fin 2, rg_pdU (rg_upd (fun _ => false) j true) j = -1 := by
    intro j
    rw [rg_pd_upd]
    fin_cases j <;> simp [rg_pdU, rg_pdPay]
  refine ⟨rg_proposition_21_1_3_if rg_pd_bound (by norm_num) (by norm_num) _ ?_, ?_⟩
  · intro k t j x hx
    rw [rg_pdStick_val, rg_pdStick_val]
    have hj0 : ¬ (some j = none ∨ 2 ≤ 0) := by simp
    have h00 : (0 : ℕ) ≠ 1 := by norm_num
    by_cases hkt : k = none ∨ 2 ≤ t
    · have hQ : rg_pdStick k t = fun _ => true := by
        unfold rg_pdStick
        simp only [hkt, ↓reduceIte]
      have hkt1 : k = none ∨ 2 ≤ t + 1 := by
        rcases hkt with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      rw [hQ] at hx ⊢
      have hxf : x = false := by simpa using hx
      rw [hxf, hdevC]
      simp only [hkt1, hj0, h00, ↓reduceIte, rg_pdU, rg_pdPay]
      norm_num
    · have hQ : rg_pdStick k t = fun _ => false := by
        unfold rg_pdStick
        simp only [hkt, ↓reduceIte]
      rw [hQ] at hx ⊢
      have hxt : x = true := by simpa using hx
      rw [hxt, hdevD]
      have ht : t < 2 := by
        by_contra h
        exact hkt (Or.inr (by omega))
      simp only [hj0, h00, ↓reduceIte, rg_pdU, rg_pdPay]
      split_ifs with h1 h2
      · norm_num
      · norm_num
      · exfalso
        exact h1 (Or.inr (by omega))
  · intro h
    have := h none 0 0 false (by simp [rg_pdStick])
    have hQ : rg_pdStick none 0 = fun _ => true := by simp [rg_pdStick]
    have hj0 : ¬ ((some (0 : Fin 2)) = none ∨ 2 ≤ 0 + 1) := by simp
    rw [hQ, hdevC, rg_pdStick_val, rg_pdStick_val] at this
    simp only [hj0, true_or, ↓reduceIte, rg_pdU, rg_pdPay] at this
    norm_num at this

/-- The stage payoffs of `rg_proposition_21_1_3_misprint_own`: player 1 (index `0`) gets `−10`
for playing `false` plus `1` if player 2 plays `true`; player 2 gets `0`. -/
def rg_ownU (a : rg_Prof (fun _ : Fin 2 => Bool)) (i : Fin 2) : ℝ :=
  if i = 0 then (if a 0 then 0 else -10) + (if a 1 then 1 else 0) else 0

/-- The paths of `rg_proposition_21_1_3_misprint_own`: `(true, true)` forever on player 1's
punishment path, `(true, false)` forever otherwise. -/
def rg_ownQ (k : Option (Fin 2)) (_t : ℕ) : rg_Prof (fun _ : Fin 2 => Bool) :=
  if k = some 0 then fun _ => true else ![true, false]

/-- Correction to Proposition 21.1.3: the condition must be restricted to `a'ⱼ ≠ aᵏⱼ(t)`. In the
game `rg_ownU` with `δ = 1/2`, the simple strategy `rg_ownQ` is an SPE, yet the condition
fails for `a'ⱼ = aᵏⱼ(t)` (player 1's punishment path is better for him than `Q⁰`), both as
printed and with `Uⱼ(Qʲ; 1)`. -/
theorem rg_proposition_21_1_3_misprint_own :
    rg_IsSPE (1 / 2) rg_ownU (rg_simpleStrat rg_ownQ) ∧
      (¬ ∀ (k : Option (Fin 2)) (t : ℕ) (j : Fin 2) (x : Bool),
        (1 - 1 / 2) * rg_ownU (rg_upd (rg_ownQ k t) j x) j +
            1 / 2 * rg_pathVal (1 / 2) rg_ownU rg_ownQ (some j) 0 j ≤
          (1 - 1 / 2) * rg_ownU (rg_ownQ k t) j +
            1 / 2 * rg_pathVal (1 / 2) rg_ownU rg_ownQ k (t + 1) j) ∧
      ¬ ∀ (k : Option (Fin 2)) (t : ℕ) (j : Fin 2) (x : Bool),
        (1 - 1 / 2) * rg_ownU (rg_upd (rg_ownQ k t) j x) j +
            1 / 2 * rg_pathVal (1 / 2) rg_ownU rg_ownQ (some j) (t + 1) j ≤
          (1 - 1 / 2) * rg_ownU (rg_ownQ k t) j +
            1 / 2 * rg_pathVal (1 / 2) rg_ownU rg_ownQ k (t + 1) j := by
  have hb : ∀ a j, |rg_ownU a j| ≤ 10 := by
    intro a j
    unfold rg_ownU
    split_ifs <;> norm_num
  have hval : ∀ k t j, rg_pathVal (1 / 2) rg_ownU rg_ownQ k t j = rg_ownU (rg_ownQ k 0) j := by
    intro k t j
    unfold rg_pathVal
    have : (fun s => rg_ownQ k (t + s)) = fun _ => rg_ownQ k 0 := rfl
    rw [this, rg_pathPay_const hb (by norm_num) (by norm_num)]
  have hupd : ∀ (b : rg_Prof (fun _ : Fin 2 => Bool)) (j : Fin 2) (x : Bool),
      rg_upd b j x = fun i => if i = j then x else b i := rg_pd_upd
  refine ⟨rg_proposition_21_1_3_if hb (by norm_num) (by norm_num) _ ?_, ?_, ?_⟩
  · intro k t j x hx
    rw [hval, hval]
    rw [hupd]
    have h0 : rg_ownQ k t 0 = true := by unfold rg_ownQ; split_ifs <;> rfl
    have hQ0 : rg_ownQ k 0 = rg_ownQ k t := rfl
    by_cases hj : j = 0
    · subst hj
      rw [h0] at hx
      have hxf : x = false := by simpa using hx
      subst hxf
      set b := rg_ownQ k t with hb
      have e1 : rg_ownU (fun i => if i = 0 then false else b i) 0 =
          -10 + (if b 1 then 1 else 0) := by simp [rg_ownU]
      have e2 : rg_ownU b 0 = (if b 1 then 1 else 0) := by simp [rg_ownU, h0]
      have e3 : rg_ownU (rg_ownQ (some 0) 0) 0 = 1 := by simp [rg_ownU, rg_ownQ]
      rw [e1, e2, e3, hQ0, e2]
      split_ifs <;> norm_num
    · simp [rg_ownU, hj]
  · intro h
    have := h none 0 0 true
    rw [hval, hval, hupd] at this
    simp [rg_ownU, rg_ownQ] at this
    norm_num at this
  · intro h
    have := h none 0 0 true
    rw [hval, hval, hupd] at this
    simp [rg_ownU, rg_ownQ] at this
    norm_num at this

/-- Miao, pp. 748–749 (Abreu 1988): with compact action sets and continuous bounded payoffs,
every SPE `σ*` is matched by an SPE simple strategy: `Q⁰` is the path of `σ*` and `Qʲ` is the
path of an SPE that minimises player `j`'s payoff over `V` (the harshest punishment `wʲ`). -/
theorem rg_abreu_simple [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] {δ M : ℝ}
    {u : rg_Prof A → ι → ℝ} (hu : ∀ j, Continuous fun a => u a j) (hM : ∀ a j, |u a j| ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : rg_Strat A} (hσ : rg_IsSPE δ u σ) :
    ∃ Q : Option ι → ℕ → rg_Prof A, rg_IsSPE δ u (rg_simpleStrat Q) ∧
      rg_U δ u (rg_simpleStrat Q) = rg_U δ u σ ∧ Q none = rg_path σ ∧
      ∀ j, rg_pathVal δ u Q (some j) 0 ∈ rg_V δ u ∧
        ∀ v ∈ rg_V δ u, rg_pathVal δ u Q (some j) 0 j ≤ v j := by
  have hVc := ex_21_1 hu hM hδ0 hδ1
  have hne : (rg_V δ u).Nonempty := ⟨_, σ, hσ, rfl⟩
  have hmin : ∀ j, ∃ x ∈ rg_V δ u, IsMinOn (fun y : ι → ℝ => y j) (rg_V δ u) x := fun j =>
    hVc.exists_isMinOn hne (continuous_apply j).continuousOn
  choose p hpV hpmin using hmin
  have hsp : ∀ j, ∃ ρ : rg_Strat A, rg_IsSPE δ u ρ ∧ rg_U δ u ρ = p j := fun j => hpV j
  choose ρ hρ hρp using hsp
  let R : Option ι → rg_Strat A := fun k => k.elim σ ρ
  have hR : ∀ k, rg_IsSPE δ u (R k) := by
    intro k
    cases k with
    | none => exact hσ
    | some j => exact hρ j
  let Q : Option ι → ℕ → rg_Prof A := fun k => rg_path (R k)
  have hQv : ∀ k t, rg_pathVal δ u Q k t = rg_U δ u (rg_cont (R k) (rg_hist (R k) t)) := by
    intro k t
    rw [rg_U_subgame]
    rfl
  have hpj : ∀ j, rg_pathVal δ u Q (some j) 0 = p j := by
    intro j
    rw [hQv, ← hρp j]
    simp only [rg_hist, rg_cont_nil]
    rfl
  refine ⟨Q, rg_proposition_21_1_3_if hM hδ0 hδ1 Q fun k t j x _ => ?_, ?_, rfl,
    fun j => ⟨by rw [hpj]; exact hpV j, fun v hv => by rw [hpj]; exact hpmin j hv⟩⟩
  · have h1 := rg_oneShot_le_of_isSPE hM hδ0 hδ1 (hR k) j (rg_hist (R k) t) x
    have h2 : rg_U δ u (rg_cont (R k) (rg_upd (R k (rg_hist (R k) t)) j x :: rg_hist (R k) t))
        ∈ rg_V δ u := ⟨_, rg_isSPE_cont (hR k) _, rfl⟩
    have h3 : p j j ≤ rg_U δ u (rg_cont (R k) (rg_upd (R k (rg_hist (R k) t)) j x ::
        rg_hist (R k) t)) j := hpmin j h2
    have h4 : rg_pathVal δ u Q (some j) 0 j = p j j := by rw [hpj]
    have e : rg_U δ u (rg_cont (R k) (rg_hist (R k) t)) j =
        (1 - δ) * u (Q k t) j + δ * rg_pathVal δ u Q k (t + 1) j := by
      rw [← hQv]
      exact rg_pathVal_succ hM hδ0 hδ1 Q k t j
    have h6 := mul_le_mul_of_nonneg_left h3 hδ0
    change (1 - δ) * u (rg_upd (Q k t) j x) j + δ * rg_U δ u (rg_cont (R k)
      (rg_upd (Q k t) j x :: rg_hist (R k) t)) j ≤ _ at h1
    change _ ≤ δ * rg_U δ u (rg_cont (R k) (rg_upd (Q k t) j x :: rg_hist (R k) t)) j at h6
    rw [h4]
    linarith
  · rw [rg_simple_payoff, hQv]
    simp only [rg_hist, rg_cont_nil]
    rfl

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Repeated games with imperfect public monitoring

Miao, §21.1.5, pp. 749–751: a stage game whose players see only a public signal `y ∈ Y`
drawn with probability `f(y | a)`; payoffs `u_i(a) = ∑_y f(y|a) r_i(a_i, y)`; public strategies;
the expected discounted average payoff; perfect public equilibrium (Definition 21.1.6);
admissibility and the operator `B` (Definitions 21.1.7–21.1.8). The text says that "almost all
the results for the case of perfect monitoring carry over"; we prove the PPE versions of
Lemma 21.1.1 (`dg_ppe_subset_B`), the one-shot deviation principle (`dg_oneShot_ppe`),
self-generation (`dg_selfGeneration_ppe`), factorization (`dg_factorization_ppe`), maximality
(`dg_ppe_greatest_fixedPoint`), monotonicity (`dg_B_mono`) and compactness of `B(W)` for finite
action sets (`dg_B_isCompact`).

Setting and departures.
* Players form a finite type `ι`, action sets `A i` are arbitrary types, `Y` is a finite type.
  The signal law `f a` is a probability vector; continuity and the full support assumption of
  the text are not needed for these results. Rewards `r_i` are bounded by `M`.
* A public history is the list of past signals, OLDEST FIRST; a profile of public strategies is
  `σ : List Y → ∀ j, A j`, and its continuation after `h` is `dg_cont σ h = σ (h ++ ·)`.
* The payoff is `U_i(σ) = (1 − δ) ∑_t δᵗ E[u_i(a_t)]`, the expectation being taken over signal
  histories (`dg_ex`).
* Deviations in Definition 21.1.6 are public pure strategies `τ : List Y → A i`. The text allows
  any pure strategy on private histories, but a pure strategy's own past actions are a function
  of the public history, so every pure strategy is outcome-equivalent to a public one.
-/

namespace Miao.DynamicGames

/-- The data of a repeated game with imperfect public monitoring (Miao, p. 749): the signal
law `f(y | a)` (a probability vector for each action profile) and the realised rewards
`r_i(a_i, y)`, bounded by `M`. -/
structure DGPublicGame (ι : Type) (A : ι → Type) (Y : Type) [Fintype Y] where
  /-- The signal law `f(y | a)`. -/
  f : (∀ i, A i) → Y → ℝ
  /-- Probabilities are nonnegative. -/
  f_nonneg : ∀ a y, 0 ≤ f a y
  /-- Probabilities sum to one. -/
  f_sum : ∀ a, ∑ y, f a y = 1
  /-- The realised reward `r_i(a_i, y)`. -/
  r : ∀ i, A i → Y → ℝ
  /-- A bound on the rewards. -/
  M : ℝ
  /-- Rewards are bounded. -/
  r_bound : ∀ i ai y, |r i ai y| ≤ M

variable {ι : Type} {A : ι → Type} {Y : Type} [Fintype Y]

/-- Miao, p. 750: the ex ante stage payoff `u_i(a) = ∑_y f(y|a) r_i(a_i, y)`. -/
def dg_u (G : DGPublicGame ι A Y) (i : ι) (a : ∀ j, A j) : ℝ := ∑ y, G.f a y * G.r i (a i) y

/-- The continuation `σ|_h` of a public strategy (or profile) after the public history `h`. -/
def dg_cont {B : Type*} (σ : List Y → B) (h : List Y) : List Y → B := fun h' => σ (h ++ h')

/-- The profile `(τ, σ₋ᵢ)`: player `i` plays the public strategy `τ`, the others follow `σ`. -/
def dg_dev [DecidableEq ι] (σ : List Y → ∀ j, A j) (i : ι) (τ : List Y → A i) :
    List Y → ∀ j, A j := fun h => Function.update (σ h) i (τ h)

/-- The expected stage payoff of player `i` at date `t` (date `0` is the first period) under the
public profile `σ`: at date `0` it is `u_i(σ(∅))`; at `t + 1` average over the first signal. -/
def dg_ex (G : DGPublicGame ι A Y) (i : ι) : ℕ → (List Y → ∀ j, A j) → ℝ
  | 0, σ => dg_u G i (σ [])
  | t + 1, σ => ∑ y, G.f (σ []) y * dg_ex G i t (fun h => σ (y :: h))

/-- Miao, p. 750: the expected discounted average payoff `U_i(σ) = (1 − δ) ∑ δᵗ E u_i(a_t)`. -/
noncomputable def dg_U (G : DGPublicGame ι A Y) (δ : ℝ) (σ : List Y → ∀ j, A j) (i : ι) : ℝ :=
  (1 - δ) * ∑' t : ℕ, δ ^ t * dg_ex G i t σ

/-- `|u_i(a)| ≤ M`. -/
theorem dg_abs_u_le (G : DGPublicGame ι A Y) (i : ι) (a : ∀ j, A j) : |dg_u G i a| ≤ G.M := by
  unfold dg_u
  calc |∑ y, G.f a y * G.r i (a i) y| ≤ ∑ y, |G.f a y * G.r i (a i) y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, G.f a y * G.M := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (G.f_nonneg a y)]
        exact mul_le_mul_of_nonneg_left (G.r_bound i (a i) y) (G.f_nonneg a y)
    _ = G.M := by rw [← Finset.sum_mul, G.f_sum a, one_mul]

/-- A probability average of numbers bounded by `M` in absolute value is bounded by `M`. -/
theorem dg_abs_avg_le (p : Y → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (x : Y → ℝ)
    (M : ℝ) (hx : ∀ y, |x y| ≤ M) : |∑ y, p y * x y| ≤ M := by
  calc |∑ y, p y * x y| ≤ ∑ y, |p y * x y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, p y * M := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (hp0 y)]
        exact mul_le_mul_of_nonneg_left (hx y) (hp0 y)
    _ = M := by rw [← Finset.sum_mul, hp1, one_mul]

/-- `|E u_i(a_t)| ≤ M` at every date. -/
theorem dg_abs_ex_le (G : DGPublicGame ι A Y) (i : ι) (t : ℕ) :
    ∀ σ : List Y → ∀ j, A j, |dg_ex G i t σ| ≤ G.M := by
  induction t with
  | zero => intro σ; exact dg_abs_u_le G i _
  | succ t ih =>
      intro σ
      exact dg_abs_avg_le _ (G.f_nonneg _) (G.f_sum _) _ _ fun y => ih _

/-- The discounted series defining `U_i(σ)` is summable. -/
theorem dg_summable (G : DGPublicGame ι A Y) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : List Y → ∀ j, A j) (i : ι) : Summable fun t : ℕ => δ ^ t * dg_ex G i t σ := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_left G.M)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hδ0, mul_comm]
  exact mul_le_mul_of_nonneg_right (dg_abs_ex_le G i t σ) (pow_nonneg hδ0 t)

/-- `|U_i(σ)| ≤ M` for every public profile. -/
theorem dg_abs_U_le (G : DGPublicGame ι A Y) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : List Y → ∀ j, A j) (i : ι) : |dg_U G δ σ i| ≤ G.M := by
  have hg := (summable_geometric_of_lt_one hδ0 hδ1).mul_left G.M
  have hs := dg_summable G hδ0 hδ1 σ i
  have hgeo : ∑' t : ℕ, G.M * δ ^ t = G.M * (1 - δ)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1]
  have hb : ∀ t : ℕ, |δ ^ t * dg_ex G i t σ| ≤ G.M * δ ^ t := fun t => by
    rw [abs_mul, abs_pow, abs_of_nonneg hδ0, mul_comm]
    exact mul_le_mul_of_nonneg_right (dg_abs_ex_le G i t σ) (pow_nonneg hδ0 t)
  have hup : ∑' t : ℕ, δ ^ t * dg_ex G i t σ ≤ G.M * (1 - δ)⁻¹ :=
    hgeo ▸ hs.tsum_le_tsum (fun t => (abs_le.mp (hb t)).2) hg
  have hlo : -(G.M * (1 - δ)⁻¹) ≤ ∑' t : ℕ, δ ^ t * dg_ex G i t σ := by
    have := hg.neg.tsum_le_tsum (fun t => (abs_le.mp (hb t)).1) hs
    rwa [tsum_neg, hgeo] at this
  have h1 : 0 < 1 - δ := by linarith
  have e : (1 - δ) * (G.M * (1 - δ)⁻¹) = G.M := by field_simp
  unfold dg_U
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hlo h1.le
    rw [mul_neg, e] at this
    exact this
  · have := mul_le_mul_of_nonneg_left hup h1.le
    rwa [e] at this

/-- Miao, p. 751 ("we can still find a recursive structure"): the payoff of a public profile is
the current payoff plus the discounted expected continuation payoff,
`U_i(σ) = (1 − δ) u_i(σ(∅)) + δ ∑_y f(y | σ(∅)) U_i(σ|_y)`. -/
theorem dg_U_rec (G : DGPublicGame ι A Y) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : List Y → ∀ j, A j) (i : ι) :
    dg_U G δ σ i = (1 - δ) * dg_u G i (σ []) +
      δ * ∑ y, G.f (σ []) y * dg_U G δ (dg_cont σ [y]) i := by
  have hs := dg_summable G hδ0 hδ1 σ i
  have h1 : ∀ t : ℕ, δ ^ (t + 1) * dg_ex G i (t + 1) σ =
      δ * ∑ y, G.f (σ []) y * (δ ^ t * dg_ex G i t (dg_cont σ [y])) := by
    intro t
    simp only [dg_ex, Finset.mul_sum, pow_succ]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : dg_cont σ [y] = fun h => σ (y :: h) := rfl
    rw [hc]
    ring
  have key : ∑' t : ℕ, δ ^ (t + 1) * dg_ex G i (t + 1) σ =
      δ * ∑ y, G.f (σ []) y * ∑' t : ℕ, δ ^ t * dg_ex G i t (dg_cont σ [y]) := by
    rw [tsum_congr h1, tsum_mul_left,
      Summable.tsum_finsetSum fun y _ => (dg_summable G hδ0 hδ1 _ i).mul_left _]
    congr 1
    exact Finset.sum_congr rfl fun y _ => tsum_mul_left
  have h2 : ∑ y, G.f (σ []) y * dg_U G δ (dg_cont σ [y]) i =
      (1 - δ) * ∑ y, G.f (σ []) y * ∑' t : ℕ, δ ^ t * dg_ex G i t (dg_cont σ [y]) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by unfold dg_U; ring
  rw [h2]
  unfold dg_U
  rw [hs.tsum_eq_zero_add, key]
  simp only [pow_zero, one_mul, dg_ex]
  ring

omit [Fintype Y] in
/-- The continuation of a continuation: `σ|_{h ++ h'} = (σ|_h)|_{h'}`. -/
theorem dg_cont_append (σ : List Y → ∀ j, A j) (h h' : List Y) :
    dg_cont σ (h ++ h') = dg_cont (dg_cont σ h) h' := by
  funext h''
  simp only [dg_cont, List.append_assoc]

/-- A function bounded above whose values are all at most `δ` times its supremum, `δ < 1`, is
nonpositive. This is the contraction step in the one-shot deviation principle and in
self-generation. -/
theorem dg_nonpos_of_le_mul_iSup {X : Type*} (g : X → ℝ) (hb : BddAbove (Set.range g))
    {δ : ℝ} (hδ1 : δ < 1) (hg : ∀ x, g x ≤ δ * ⨆ z, g z) (x : X) : g x ≤ 0 := by
  have hne : Nonempty X := ⟨x⟩
  have hS : (⨆ z, g z) ≤ δ * ⨆ z, g z := ciSup_le hg
  have hS0 : (⨆ z, g z) ≤ 0 := by
    by_contra hc
    have hc' : 0 < ⨆ z, g z := lt_of_not_ge hc
    have := mul_lt_mul_of_pos_right hδ1 hc'
    linarith
  exact (le_ciSup hb x).trans hS0

/-- A probability average of the values of a function bounded above is at most its supremum. -/
theorem dg_avg_le_iSup {X : Type*} (g : X → ℝ) (hb : BddAbove (Set.range g)) (p : Y → ℝ)
    (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (k : Y → X) :
    ∑ y, p y * g (k y) ≤ ⨆ z, g z :=
  calc ∑ y, p y * g (k y) ≤ ∑ y, p y * ⨆ z, g z :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (le_ciSup hb _) (hp0 y)
    _ = ⨆ z, g z := by rw [← Finset.sum_mul, hp1, one_mul]

/-- **Definition 21.1.6** (Miao, p. 750). The public profile `σ` is a perfect public equilibrium
(PPE) if after every public history `h` the continuation `σ|_h` is a Nash equilibrium:
`U_i(σ|_h) ≥ U_i(τ, σ₋ᵢ|_h)` for every player `i` and every (public) strategy `τ`. -/
def dg_IsPPE [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) (σ : List Y → ∀ j, A j) : Prop :=
  ∀ h i (τ : List Y → A i), dg_U G δ (dg_dev (dg_cont σ h) i τ) i ≤ dg_U G δ (dg_cont σ h) i

/-- The set `E(δ)` of PPE payoff vectors. -/
def dg_PPEPayoffs [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) : Set (ι → ℝ) :=
  {v | ∃ σ, dg_IsPPE G δ σ ∧ dg_U G δ σ = v}

/-- The payoff vector generated by the action profile `a` and continuation payoffs `w`:
`(1 − δ) u(a) + δ ∑_y f(y|a) w(y)`. -/
def dg_gen (G : DGPublicGame ι A Y) (δ : ℝ) (a : ∀ j, A j) (w : Y → ι → ℝ) : ι → ℝ :=
  fun i => (1 - δ) * dg_u G i a + δ * ∑ y, G.f a y * w y i

/-- **Definition 21.1.7** (Miao, p. 751). `(a, w(·))` is admissible with respect to `W` if
`w(y) ∈ W` for every signal and no player gains by a one-period deviation:
`(1 − δ) u_i(a) + δ ∑_y f(y|a) w_i(y) ≥ (1 − δ) u_i(a'_i, a₋ᵢ) + δ ∑_y f(y|a'_i, a₋ᵢ) w_i(y)`. -/
def dg_Admissible [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) (W : Set (ι → ℝ))
    (a : ∀ j, A j) (w : Y → ι → ℝ) : Prop :=
  (∀ y, w y ∈ W) ∧ ∀ i (b : A i), dg_gen G δ (Function.update a i b) w i ≤ dg_gen G δ a w i

/-- **Definition 21.1.8** (Miao, p. 751). `B(W)` is the set of `v = (1 − δ) u(a) + δ ∑ f(y|a) w(y)`
over pairs `(a, w)` admissible with respect to `W`. -/
def dg_B [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) (W : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {v | ∃ a w, dg_Admissible G δ W a w ∧ v = dg_gen G δ a w}

/-- The PPE analogue of Proposition 21.1.1 (one-shot deviation principle, Miao, pp. 741 and 751):
for a public profile `σ` and player `i`, no deviation `τ` is profitable after any public history
iff no one-period deviation `b` is profitable after any public history (followed by `σ`). -/
theorem dg_oneShot_ppe [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (σ : List Y → ∀ j, A j) (i : ι) :
    (∀ h (τ : List Y → A i), dg_U G δ (dg_dev (dg_cont σ h) i τ) i ≤ dg_U G δ (dg_cont σ h) i)
      ↔ ∀ h (b : A i), (1 - δ) * dg_u G i (Function.update (σ h) i b) +
          δ * ∑ y, G.f (Function.update (σ h) i b) y * dg_U G δ (dg_cont σ (h ++ [y])) i ≤
          dg_U G δ (dg_cont σ h) i := by
  constructor
  · intro H h b
    let τ : List Y → A i := fun h' => if h' = [] then b else σ (h ++ h') i
    have h0 : dg_dev (dg_cont σ h) i τ [] = Function.update (σ h) i b := by
      simp only [dg_dev, dg_cont, List.append_nil, τ, ↓reduceIte]
    have hc : ∀ y, dg_cont (dg_dev (dg_cont σ h) i τ) [y] = dg_cont σ (h ++ [y]) := by
      intro y
      funext h'
      have hne : ([y] ++ h' = []) = False := by simp
      simp only [dg_cont, dg_dev, τ, hne, ↓reduceIte, List.append_assoc,
        Function.update_eq_self]
    have := H h τ
    rw [dg_U_rec G hδ0 hδ1, h0] at this
    simp only [hc] at this
    exact this
  · intro H
    suffices key : ∀ τ : List Y → A i, ∀ h, dg_U G δ (dg_dev (dg_cont σ h) i (dg_cont τ h)) i ≤
        dg_U G δ (dg_cont σ h) i by
      intro h τ
      have := key (fun h'' => τ (h''.drop h.length)) h
      have e : (dg_cont (fun h'' => τ (h''.drop h.length)) h) = τ := by
        funext h'; simp only [dg_cont, List.drop_left]
      rwa [e] at this
    intro τ
    let D : List Y → ℝ := fun h => dg_U G δ (dg_dev (dg_cont σ h) i (dg_cont τ h)) i
    let S : List Y → ℝ := fun h => dg_U G δ (dg_cont σ h) i
    have hD : ∀ h, D h = (1 - δ) * dg_u G i (Function.update (σ h) i (τ h)) +
        δ * ∑ y, G.f (Function.update (σ h) i (τ h)) y * D (h ++ [y]) := by
      intro h
      have h0 : dg_dev (dg_cont σ h) i (dg_cont τ h) [] = Function.update (σ h) i (τ h) := by
        simp only [dg_dev, dg_cont, dg_cont, List.append_nil]
      have hc : ∀ y, dg_cont (dg_dev (dg_cont σ h) i (dg_cont τ h)) [y] =
          dg_dev (dg_cont σ (h ++ [y])) i (dg_cont τ (h ++ [y])) := by
        intro y; funext h'
        simp only [dg_cont, dg_dev, dg_cont, List.append_assoc]
      simp only [D]
      rw [dg_U_rec G hδ0 hδ1, h0]
      simp only [hc]
    have hb : BddAbove (Set.range fun h => D h - S h) := by
      refine ⟨2 * G.M, ?_⟩
      rintro _ ⟨h, rfl⟩
      have h1 := abs_le.mp (dg_abs_U_le G hδ0 hδ1 (dg_dev (dg_cont σ h) i (dg_cont τ h)) i)
      have h2 := abs_le.mp (dg_abs_U_le G hδ0 hδ1 (dg_cont σ h) i)
      simp only [D, S]
      linarith [h1.2, h2.1]
    have hg : ∀ h, D h - S h ≤ δ * ⨆ z, (D z - S z) := by
      intro h
      have hos := H h (τ h)
      have havg := dg_avg_le_iSup (fun z => D z - S z) hb _
        (G.f_nonneg (Function.update (σ h) i (τ h))) (G.f_sum _) (fun y => h ++ [y])
      have hsplit : ∑ y, G.f (Function.update (σ h) i (τ h)) y * (D (h ++ [y]) - S (h ++ [y]))
          = ∑ y, G.f (Function.update (σ h) i (τ h)) y * D (h ++ [y]) -
            ∑ y, G.f (Function.update (σ h) i (τ h)) y * S (h ++ [y]) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hsplit] at havg
      rw [hD h]
      simp only [S] at hos havg ⊢
      nlinarith [mul_le_mul_of_nonneg_left havg hδ0]
    exact fun h => sub_nonpos.mp (dg_nonpos_of_le_mul_iSup _ hb hδ1 hg h)

/-- The PPE analogue of Lemma 21.1.1 (Miao, pp. 743 and 751): every PPE payoff is generated by
an admissible pair with continuation payoffs in `E(δ)`, i.e. `E(δ) ⊆ B(E(δ))`. The first-period
action is `σ(∅)` and the continuation payoff after `y` is `U(σ|_y)`. -/
theorem dg_ppe_subset_B [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) : dg_PPEPayoffs G δ ⊆ dg_B G δ (dg_PPEPayoffs G δ) := by
  rintro v ⟨σ, hσ, rfl⟩
  refine ⟨σ [], fun y => dg_U G δ (dg_cont σ [y]), ⟨fun y => ⟨dg_cont σ [y], ?_, rfl⟩, ?_⟩, ?_⟩
  · intro h i τ
    rw [← dg_cont_append]
    exact hσ ([y] ++ h) i τ
  · intro i b
    have := ((dg_oneShot_ppe G hδ0 hδ1 σ i).mp (fun h τ => hσ h i τ)) [] b
    have e : dg_cont σ [] = σ := rfl
    simp only [List.nil_append, e] at this
    have h2 := dg_U_rec G hδ0 hδ1 σ i
    simp only [dg_gen]
    linarith
  · funext i
    exact dg_U_rec G hδ0 hδ1 σ i

open Classical in
/-- The action used by the self-generation construction at a target payoff `v ∈ B(W)`
(a default `a₀` outside `B(W)`). -/
noncomputable def dg_sgAct [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) (W : Set (ι → ℝ))
    (a₀ : ∀ j, A j) (v : ι → ℝ) : ∀ j, A j :=
  if h : v ∈ dg_B G δ W then Classical.choose h else a₀

open Classical in
/-- The continuation payoffs used by the self-generation construction at `v ∈ B(W)`. -/
noncomputable def dg_sgNext [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ)
    (W : Set (ι → ℝ)) (v : ι → ℝ) : Y → ι → ℝ :=
  if h : v ∈ dg_B G δ W then Classical.choose (Classical.choose_spec h) else fun _ => v

/-- The promised payoff after the public history `h`, starting from `v`. -/
noncomputable def dg_sgPath [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ)
    (W : Set (ι → ℝ)) : (ι → ℝ) → List Y → ι → ℝ
  | v, [] => v
  | v, y :: h => dg_sgPath G δ W (dg_sgNext G δ W v y) h

/-- The recursive public strategy of the self-generation proof (Miao, p. 743):
`σ(h) = a(v(h))`, the promised payoff `v(h)` being the state. -/
noncomputable def dg_sgStrat [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ)
    (W : Set (ι → ℝ)) (a₀ : ∀ j, A j) (v : ι → ℝ) : List Y → ∀ j, A j :=
  fun h => dg_sgAct G δ W a₀ (dg_sgPath G δ W v h)

/-- At `v ∈ B(W)` the chosen pair is admissible and generates `v`. -/
theorem dg_sg_spec [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) (W : Set (ι → ℝ))
    (a₀ : ∀ j, A j) {v : ι → ℝ} (hv : v ∈ dg_B G δ W) :
    dg_Admissible G δ W (dg_sgAct G δ W a₀ v) (dg_sgNext G δ W v) ∧
      v = dg_gen G δ (dg_sgAct G δ W a₀ v) (dg_sgNext G δ W v) := by
  have e1 : dg_sgAct G δ W a₀ v = Classical.choose hv := by
    unfold dg_sgAct
    split_ifs
    rfl
  have e2 : dg_sgNext G δ W v = Classical.choose (Classical.choose_spec hv) := by
    unfold dg_sgNext
    split_ifs
    rfl
  rw [e1, e2]
  exact Classical.choose_spec (Classical.choose_spec hv)

/-- The continuation of the recursive strategy after `h` is the recursive strategy started at the
promised payoff `v(h)`. -/
theorem dg_sgStrat_cont [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) (W : Set (ι → ℝ))
    (a₀ : ∀ j, A j) (h : List Y) : ∀ v, dg_cont (dg_sgStrat G δ W a₀ v) h =
      dg_sgStrat G δ W a₀ (dg_sgPath G δ W v h) := by
  induction h with
  | nil => intro v; rfl
  | cons y h ih =>
      intro v
      have := ih (dg_sgNext G δ W v y)
      funext h'
      exact congrFun this h'

/-- If `W ⊆ B(W)`, promised payoffs stay in `B(W)`. -/
theorem dg_sgPath_mem [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) {W : Set (ι → ℝ)}
    (hW : W ⊆ dg_B G δ W) (h : List Y) :
    ∀ v, v ∈ dg_B G δ W → dg_sgPath G δ W v h ∈ dg_B G δ W := by
  induction h with
  | nil => intro v hv; exact hv
  | cons y h ih =>
      intro v hv
      exact ih _ (hW ((dg_sg_spec G δ W (Classical.choose hv) hv).1.1 y))

omit [Fintype Y] in
/-- A bounded set of payoff vectors has bounded coordinates. -/
theorem dg_coord_bound [Finite ι] {W : Set (ι → ℝ)} (hWb : Bornology.IsBounded W) :
    ∃ C, ∀ w ∈ W, ∀ i, |w i| ≤ C := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hWb
  exact ⟨C, fun w hw i => (norm_le_pi_norm w i).trans (hC w hw)⟩

/-- In the self-generation construction the recursive strategy started at `v ∈ B(W)` delivers
the payoff `v`, when `W` is bounded and `W ⊆ B(W)` (Miao, p. 743, "`v = U(σ)` … because `W` is
bounded"). -/
theorem dg_sgStrat_U [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W : Set (ι → ℝ)} (hWb : Bornology.IsBounded W)
    (hW : W ⊆ dg_B G δ W) (a₀ : ∀ j, A j) (v : ι → ℝ) (hv : v ∈ dg_B G δ W) :
    dg_U G δ (dg_sgStrat G δ W a₀ v) = v := by
  obtain ⟨C, hC⟩ := dg_coord_bound hWb
  funext i
  let g : {x // x ∈ dg_B G δ W} → ℝ := fun x => |dg_U G δ (dg_sgStrat G δ W a₀ x.1) i - x.1 i|
  have hbx : ∀ x ∈ dg_B G δ W, |x i| ≤ G.M + C := by
    rintro x ⟨a, w, ⟨hw, -⟩, rfl⟩
    simp only [dg_gen]
    have h1 := dg_abs_u_le G i a
    have h2 := dg_abs_avg_le (G.f a) (G.f_nonneg a) (G.f_sum a) (fun y => w y i) C
      (fun y => hC _ (hw y) i)
    calc |(1 - δ) * dg_u G i a + δ * ∑ y, G.f a y * w y i|
        ≤ |(1 - δ) * dg_u G i a| + |δ * ∑ y, G.f a y * w y i| := abs_add_le _ _
      _ = (1 - δ) * |dg_u G i a| + δ * |∑ y, G.f a y * w y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - δ)]
      _ ≤ (1 - δ) * G.M + δ * C := by
          gcongr
      _ ≤ G.M + C := by
          have hM : 0 ≤ G.M := (abs_nonneg _).trans h1
          have hC0 : 0 ≤ C := (abs_nonneg _).trans h2
          nlinarith
  have hb : BddAbove (Set.range g) := by
    refine ⟨G.M + (G.M + C), ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [g]
    calc |dg_U G δ (dg_sgStrat G δ W a₀ x.1) i - x.1 i|
        ≤ |dg_U G δ (dg_sgStrat G δ W a₀ x.1) i| + |x.1 i| := abs_sub _ _
      _ ≤ G.M + (G.M + C) := add_le_add (dg_abs_U_le G hδ0 hδ1 _ i) (hbx x.1 x.2)
  have hg : ∀ x, g x ≤ δ * ⨆ z, g z := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨hw, -⟩, hxe⟩ := dg_sg_spec G δ W a₀ hx
    set a := dg_sgAct G δ W a₀ x
    set w := dg_sgNext G δ W x
    have hrec := dg_U_rec G hδ0 hδ1 (dg_sgStrat G δ W a₀ x) i
    have hc : ∀ y, dg_cont (dg_sgStrat G δ W a₀ x) [y] = dg_sgStrat G δ W a₀ (w y) :=
      fun y => dg_sgStrat_cont G δ W a₀ [y] x
    have h0 : dg_sgStrat G δ W a₀ x [] = a := rfl
    simp only [hc, h0] at hrec
    have hxi : x i = (1 - δ) * dg_u G i a + δ * ∑ y, G.f a y * w y i := congrFun hxe i
    have hdiff : dg_U G δ (dg_sgStrat G δ W a₀ x) i - x i =
        δ * ∑ y, G.f a y * (dg_U G δ (dg_sgStrat G δ W a₀ (w y)) i - w y i) := by
      have hs : ∑ y, G.f a y * (dg_U G δ (dg_sgStrat G δ W a₀ (w y)) i - w y i) =
          ∑ y, G.f a y * dg_U G δ (dg_sgStrat G δ W a₀ (w y)) i - ∑ y, G.f a y * w y i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hrec, hxi, hs]
      ring
    have havg := dg_avg_le_iSup g hb (G.f a) (G.f_nonneg a) (G.f_sum a)
      (fun y => ⟨w y, hW (hw y)⟩)
    simp only [g]
    rw [hdiff, abs_mul, abs_of_nonneg hδ0]
    refine mul_le_mul_of_nonneg_left ?_ hδ0
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq_of_le ?_ havg)
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [abs_mul, abs_of_nonneg (G.f_nonneg a y)]
  have := dg_nonpos_of_le_mul_iSup g hb hδ1 hg ⟨v, hv⟩
  simp only [g] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-- The recursive strategy of the self-generation proof is a PPE (Miao, p. 743: "there is no
profitable one-shot deviation from `σ` by construction"). -/
theorem dg_sgStrat_isPPE [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W : Set (ι → ℝ)} (hWb : Bornology.IsBounded W)
    (hW : W ⊆ dg_B G δ W) (a₀ : ∀ j, A j) (v : ι → ℝ) (hv : v ∈ dg_B G δ W) :
    dg_IsPPE G δ (dg_sgStrat G δ W a₀ v) := by
  intro h0 i
  refine (dg_oneShot_ppe G hδ0 hδ1 _ i).mpr ?_ h0
  intro h b
  set x := dg_sgPath G δ W v h
  have hx : x ∈ dg_B G δ W := dg_sgPath_mem G δ hW h v hv
  obtain ⟨⟨hw, hic⟩, hxe⟩ := dg_sg_spec G δ W a₀ hx
  have hch : dg_cont (dg_sgStrat G δ W a₀ v) h = dg_sgStrat G δ W a₀ x :=
    dg_sgStrat_cont G δ W a₀ h v
  have hσh : dg_sgStrat G δ W a₀ v h = dg_sgAct G δ W a₀ x := by
    have := congrFun hch []
    simp only [dg_cont, List.append_nil] at this
    exact this
  have hcy : ∀ y, dg_U G δ (dg_cont (dg_sgStrat G δ W a₀ v) (h ++ [y])) i =
      dg_sgNext G δ W x y i := by
    intro y
    rw [dg_cont_append, hch, dg_sgStrat_cont G δ W a₀ [y] x]
    exact congrFun (dg_sgStrat_U G hδ0 hδ1 hWb hW a₀ _ (hW (hw y))) i
  rw [hσh, hch, dg_sgStrat_U G hδ0 hδ1 hWb hW a₀ x hx]
  simp only [hcy]
  have := hic i b
  simp only [dg_gen] at this
  rw [congrFun hxe i]
  simp only [dg_gen]
  exact this

/-- The PPE analogue of Lemma 21.1.2 (Self-Generation, Miao, pp. 743 and 751): if `W` is bounded
and `W ⊆ B(W)`, then `B(W) ⊆ E(δ)`; every payoff in `B(W)` is the payoff of a PPE. -/
theorem dg_selfGeneration_ppe [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W : Set (ι → ℝ)} (hWb : Bornology.IsBounded W)
    (hW : W ⊆ dg_B G δ W) : dg_B G δ W ⊆ dg_PPEPayoffs G δ := by
  intro v hv
  obtain ⟨a₀, -⟩ := id hv
  exact ⟨dg_sgStrat G δ W a₀ v, dg_sgStrat_isPPE G hδ0 hδ1 hWb hW a₀ v hv,
    dg_sgStrat_U G hδ0 hδ1 hWb hW a₀ v hv⟩

/-- A self-generating bounded set consists of PPE payoffs: `W ⊆ B(W) ⊆ E(δ)`. -/
theorem dg_selfGenerating_subset_ppe [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {W : Set (ι → ℝ)} (hWb : Bornology.IsBounded W)
    (hW : W ⊆ dg_B G δ W) : W ⊆ dg_PPEPayoffs G δ :=
  hW.trans (dg_selfGeneration_ppe G hδ0 hδ1 hWb hW)

/-- PPE payoffs are bounded by `|M|` in every coordinate, so `E(δ)` is bounded. -/
theorem dg_ppe_isBounded [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : Bornology.IsBounded (dg_PPEPayoffs G δ) := by
  have := Fintype.ofFinite ι
  refine isBounded_iff_forall_norm_le.mpr ⟨|G.M|, ?_⟩
  rintro _ ⟨σ, -, rfl⟩
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact (dg_abs_U_le G hδ0 hδ1 σ i).trans (le_abs_self _)

/-- The PPE analogue of Theorem 21.1.1 (Factorization, Miao, pp. 744 and 751): `E(δ) = B(E(δ))`. -/
theorem dg_factorization_ppe [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) : dg_PPEPayoffs G δ = dg_B G δ (dg_PPEPayoffs G δ) :=
  le_antisymm (dg_ppe_subset_B G hδ0 hδ1)
    (dg_selfGeneration_ppe G hδ0 hδ1 (dg_ppe_isBounded G hδ0 hδ1) (dg_ppe_subset_B G hδ0 hδ1))

/-- The PPE analogue of Theorem 21.1.2 (Miao, pp. 745 and 751): `E(δ)` is the largest bounded
fixed point of `B`, and it contains every bounded self-generating set. -/
theorem dg_ppe_greatest_fixedPoint [Finite ι] [DecidableEq ι] (G : DGPublicGame ι A Y)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    IsGreatest {W | Bornology.IsBounded W ∧ W = dg_B G δ W} (dg_PPEPayoffs G δ) ∧
      ∀ W, Bornology.IsBounded W → W ⊆ dg_B G δ W → W ⊆ dg_PPEPayoffs G δ :=
  ⟨⟨⟨dg_ppe_isBounded G hδ0 hδ1, dg_factorization_ppe G hδ0 hδ1⟩,
    fun _ ⟨hb, he⟩ => dg_selfGenerating_subset_ppe G hδ0 hδ1 hb he.le⟩,
    fun _ hb hW => dg_selfGenerating_subset_ppe G hδ0 hδ1 hb hW⟩

/-- The PPE analogue of Lemma 21.1.3 (Monotonicity, Miao, pp. 745 and 751): `W ⊆ W'` implies
`B(W) ⊆ B(W')`. -/
theorem dg_B_mono [DecidableEq ι] (G : DGPublicGame ι A Y) (δ : ℝ) {W W' : Set (ι → ℝ)}
    (hWW : W ⊆ W') : dg_B G δ W ⊆ dg_B G δ W' := by
  rintro v ⟨a, w, ⟨hw, hic⟩, rfl⟩
  exact ⟨a, w, ⟨fun y => hWW (hw y), hic⟩, rfl⟩

/-- `w ↦ (1 − δ) u(a) + δ ∑_y f(y|a) w(y)` is continuous. -/
theorem dg_gen_continuous (G : DGPublicGame ι A Y) (δ : ℝ) (a : ∀ j, A j) :
    Continuous (dg_gen G δ a) := by
  unfold dg_gen
  refine continuous_pi fun i => ?_
  refine continuous_const.add (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun y _ =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply y))

/-- The PPE analogue of Lemma 21.1.4 (Compactness, Miao, pp. 745 and 751), for finitely many
action profiles: if `W` is compact then `B(W)` is compact. -/
theorem dg_B_isCompact [DecidableEq ι] [Finite (∀ j, A j)] (G : DGPublicGame ι A Y) (δ : ℝ)
    {W : Set (ι → ℝ)} (hW : IsCompact W) : IsCompact (dg_B G δ W) := by
  have hset : dg_B G δ W = ⋃ a : (∀ j, A j),
      dg_gen G δ a '' (Set.univ.pi (fun _ : Y => W) ∩
        {w | ∀ i (b : A i), dg_gen G δ (Function.update a i b) w i ≤ dg_gen G δ a w i}) := by
    ext v
    simp only [dg_B, dg_Admissible, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image,
      Set.mem_inter_iff, Set.mem_univ_pi]
    constructor
    · rintro ⟨a, w, ⟨hw, hic⟩, rfl⟩
      exact ⟨a, w, ⟨hw, hic⟩, rfl⟩
    · rintro ⟨a, w, ⟨hw, hic⟩, rfl⟩
      exact ⟨a, w, ⟨hw, hic⟩, rfl⟩
  rw [hset]
  refine isCompact_iUnion fun a => IsCompact.image ?_ (dg_gen_continuous G δ a)
  refine (isCompact_univ_pi fun _ => hW).inter_right ?_
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun b => isClosed_le ?_ ?_
  · exact (continuous_apply i).comp (dg_gen_continuous G δ _)
  · exact (continuous_apply i).comp (dg_gen_continuous G δ a)

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Example 21.1.2: the noisy prisoner's dilemma

Miao, Example 21.1.2, pp. 751–753. Two players, actions `C` (`true`) and `D` (`false`); public
signal `G` (`true`) or `B` (`false`) with `Pr(G | a) = p, q, r` when two, one, none of the players
cooperate. The realised rewards `r_i(a_i, y)` of the text give the ex ante payoffs of the
prisoner's dilemma of Example 21.1.1 (`example_21_1_2_payoffs`).

The text's claim that `W = {(v, v), (v', v')}`, `v = δr/(1 − δ(p − r))`,
`v' = (1 − δ + δr)/(1 − δ(p − r))`, is self-generating when `1/(p − r) ≥ δ ≥ 1/(p + q − 2r)` is
misprinted. Its own proof shows that the four displayed conditions hold iff
`1/(p − q + p − r) ≤ δ ≤ 1/(p − r + q − r)` (`example_21_1_2_DD_ic_iff`,
`example_21_1_2_CC_ic_iff`), and `W` is self-generating on that interval (`example_21_1_2`),
hence consists of PPE payoffs (`example_21_1_2_ppe`). With `p = 9/10`, `q = 2/5`, `r = 1/10`,
`δ = 19/20` the printed hypotheses hold but `W` is not self-generating
(`example_21_1_2_printed_false`). The assumption `p − q > q − r` is exactly what makes the
corrected interval nonempty (`example_21_1_2_interval`).
-/

namespace Miao.DynamicGames

/-- `Pr(G | a)` in Example 21.1.2: `p` if both cooperate, `q` if one does, `r` if neither. -/
def dg_pdProbG (p q r : ℝ) (a : Fin 2 → Bool) : ℝ :=
  if a 0 && a 1 then p else if a 0 || a 1 then q else r

/-- The signal law `f(y | a)` of Example 21.1.2. -/
def dg_pdF (p q r : ℝ) (a : Fin 2 → Bool) (y : Bool) : ℝ :=
  if y then dg_pdProbG p q r a else 1 - dg_pdProbG p q r a

/-- The realised rewards `r_i(a_i, y)` of Example 21.1.2 (Miao, p. 751). -/
noncomputable def dg_pdR (p q r : ℝ) (ai y : Bool) : ℝ :=
  if ai then (if y then 1 + (2 - 2 * p) / (p - q) else 1 - 2 * p / (p - q))
  else (if y then (2 - 2 * r) / (q - r) else -2 * r / (q - r))

/-- A bound on the rewards of Example 21.1.2. -/
noncomputable def dg_pdM (p q r : ℝ) : ℝ :=
  |1 + (2 - 2 * p) / (p - q)| + |1 - 2 * p / (p - q)| + |(2 - 2 * r) / (q - r)| +
    |-2 * r / (q - r)|

/-- `Pr(G | a) ∈ [0, 1]` when `0 ≤ r < q < p ≤ 1`. -/
theorem dg_pdProbG_mem {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (a : Fin 2 → Bool) : 0 ≤ dg_pdProbG p q r a ∧ dg_pdProbG p q r a ≤ 1 := by
  unfold dg_pdProbG
  split_ifs <;> constructor <;> linarith

/-- The noisy prisoner's dilemma as a repeated game with imperfect public monitoring. -/
noncomputable def dg_noisyPD (p q r : ℝ) (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p)
    (hp : p ≤ 1) : DGPublicGame (Fin 2) (fun _ => Bool) Bool where
  f := dg_pdF p q r
  f_nonneg a y := by
    have := dg_pdProbG_mem hr hrq hqp hp a
    unfold dg_pdF
    split_ifs <;> linarith
  f_sum a := by simp only [Fintype.sum_bool, dg_pdF, ↓reduceIte, Bool.false_eq_true]; ring
  r _ := dg_pdR p q r
  M := dg_pdM p q r
  r_bound _ ai y := by
    unfold dg_pdR dg_pdM
    have h1 := abs_nonneg (1 + (2 - 2 * p) / (p - q))
    have h2 := abs_nonneg (1 - 2 * p / (p - q))
    have h3 := abs_nonneg ((2 - 2 * r) / (q - r))
    have h4 := abs_nonneg (-2 * r / (q - r))
    cases ai <;> cases y <;> simp only [↓reduceIte, Bool.false_eq_true] <;> linarith

/-- The ex ante payoff of player `i` in Example 21.1.2, as a function of `Pr(G | a)`:
`1 + (2 Pr(G|a) − 2p)/(p − q)` if `i` cooperates, `(2 Pr(G|a) − 2r)/(q − r)` if `i` defects. -/
theorem dg_noisyPD_u {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (i : Fin 2) (a : Fin 2 → Bool) :
    dg_u (dg_noisyPD p q r hr hrq hqp hp) i a =
      if a i then 1 + (2 * dg_pdProbG p q r a - 2 * p) / (p - q)
      else (2 * dg_pdProbG p q r a - 2 * r) / (q - r) := by
  have hpq : p - q ≠ 0 := by linarith
  have hqr : q - r ≠ 0 := by linarith
  simp only [dg_u, dg_noisyPD, Fintype.sum_bool, dg_pdF, dg_pdR, ↓reduceIte,
    Bool.false_eq_true]
  cases a i <;> simp only [↓reduceIte, Bool.false_eq_true] <;> field_simp <;> ring

/-- The prisoner's dilemma matrix of Example 21.1.1: own action, other's action. -/
def dg_pdMatrix (ai aj : Bool) : ℝ :=
  if ai then (if aj then 1 else -1) else (if aj then 2 else 0)

/-- **Example 21.1.2** (Miao, p. 752): the ex ante payoffs `u_i(a) = ∑_y f(y|a) r_i(a_i, y)` are
those of the prisoner's dilemma of Example 21.1.1. -/
theorem example_21_1_2_payoffs {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p)
    (hp : p ≤ 1) (a : Fin 2 → Bool) :
    dg_u (dg_noisyPD p q r hr hrq hqp hp) 0 a = dg_pdMatrix (a 0) (a 1) ∧
      dg_u (dg_noisyPD p q r hr hrq hqp hp) 1 a = dg_pdMatrix (a 1) (a 0) := by
  have hpq : p - q ≠ 0 := by linarith
  have hqr : q - r ≠ 0 := by linarith
  rw [dg_noisyPD_u, dg_noisyPD_u]
  unfold dg_pdProbG dg_pdMatrix
  cases a 0 <;> cases a 1 <;>
    simp only [↓reduceIte, Bool.false_eq_true, Bool.and_self, Bool.or_self, Bool.and_false,
      Bool.and_true, Bool.or_false, Bool.or_true] <;>
    constructor <;> field_simp <;> ring

/-- The ex ante payoffs of Example 21.1.2 as the prisoner's dilemma matrix, for either player. -/
theorem dg_noisyPD_u_matrix {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (i : Fin 2) (a : Fin 2 → Bool) :
    dg_u (dg_noisyPD p q r hr hrq hqp hp) i a =
      dg_pdMatrix (a i) (if i = 0 then a 1 else a 0) := by
  have h := example_21_1_2_payoffs hr hrq hqp hp a
  fin_cases i
  · exact h.1
  · exact h.2

/-- The bad continuation payoff `v = δr/(1 − δ(p − r))` of Example 21.1.2. -/
noncomputable def dg_pdV (p r δ : ℝ) : ℝ := δ * r / (1 - δ * (p - r))

/-- The good continuation payoff `v' = (1 − δ + δr)/(1 − δ(p − r))` of Example 21.1.2. -/
noncomputable def dg_pdV' (p r δ : ℝ) : ℝ := (1 - δ + δ * r) / (1 - δ * (p - r))

/-- The candidate set `W = {(v, v), (v', v')}` of Example 21.1.2. -/
noncomputable def dg_pdW (p r δ : ℝ) : Set (Fin 2 → ℝ) :=
  {fun _ => dg_pdV p r δ, fun _ => dg_pdV' p r δ}

/-- **Example 21.1.2** (Miao, p. 752): the promise-keeping equation for `v` under `(D, D)`,
`v = (1 − δ)·0 + δ((1 − r)v + rv')`. -/
theorem example_21_1_2_DD_eq {p r δ : ℝ} (hD : 1 - δ * (p - r) ≠ 0) :
    dg_pdV p r δ = (1 - δ) * 0 + δ * ((1 - r) * dg_pdV p r δ + r * dg_pdV' p r δ) := by
  unfold dg_pdV dg_pdV'
  field_simp
  ring

/-- **Example 21.1.2** (Miao, p. 752): the promise-keeping equation for `v'` under `(C, C)`,
`v' = (1 − δ)·1 + δ((1 − p)v + pv')`. -/
theorem example_21_1_2_CC_eq {p r δ : ℝ} (hD : 1 - δ * (p - r) ≠ 0) :
    dg_pdV' p r δ = (1 - δ) * 1 + δ * ((1 - p) * dg_pdV p r δ + p * dg_pdV' p r δ) := by
  unfold dg_pdV dg_pdV'
  field_simp
  ring

/-- **Example 21.1.2** (Miao, p. 752): the incentive constraint for `(D, D)`,
`v ≥ (1 − δ)(−1) + δ((1 − q)v + qv')`, holds iff `δ ≤ 1/(p − r + q − r)`. -/
theorem example_21_1_2_DD_ic_iff {p q r δ : ℝ} (hrq : r < q) (hqp : q < p) (hδ1 : δ < 1)
    (hD : 0 < 1 - δ * (p - r)) :
    (1 - δ) * (-1) + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ) ≤ dg_pdV p r δ ↔
      δ ≤ 1 / (p - r + q - r) := by
  have key : dg_pdV p r δ - ((1 - δ) * (-1) + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ))
      = (1 - δ) / (1 - δ * (p - r)) * (1 - δ * (p - r + q - r)) := by
    unfold dg_pdV dg_pdV'
    field_simp
    ring
  have hc : 0 < (1 - δ) / (1 - δ * (p - r)) := div_pos (by linarith) hD
  rw [le_div_iff₀ (by linarith), ← sub_nonneg, key]
  rw [mul_nonneg_iff_of_pos_left hc]
  constructor <;> intro h <;> linarith

/-- **Example 21.1.2** (Miao, pp. 752–753): the incentive constraint for `(C, C)`,
`v' ≥ (1 − δ)·2 + δ((1 − q)v + qv')`, holds iff `δ ≥ 1/(p − q + p − r)`. -/
theorem example_21_1_2_CC_ic_iff {p q r δ : ℝ} (hrq : r < q) (hqp : q < p) (hδ1 : δ < 1)
    (hD : 0 < 1 - δ * (p - r)) :
    (1 - δ) * 2 + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ) ≤ dg_pdV' p r δ ↔
      1 / (p - q + p - r) ≤ δ := by
  have key : dg_pdV' p r δ - ((1 - δ) * 2 + δ * ((1 - q) * dg_pdV p r δ + q * dg_pdV' p r δ))
      = (1 - δ) / (1 - δ * (p - r)) * (δ * (p - q + p - r) - 1) := by
    unfold dg_pdV dg_pdV'
    field_simp
    ring
  have hc : 0 < (1 - δ) / (1 - δ * (p - r)) := div_pos (by linarith) hD
  rw [div_le_iff₀ (by linarith), ← sub_nonneg, key]
  rw [mul_nonneg_iff_of_pos_left hc]
  constructor <;> intro h <;> linarith

/-- Example 21.1.2 (Miao, p. 751): the assumption `p − q > q − r` is what makes the corrected
interval `[1/(p − q + p − r), 1/(p − r + q − r)]` nonempty. -/
theorem example_21_1_2_interval {p q r : ℝ} (hrq : r < q) (hqp : q < p) :
    1 / (p - q + p - r) < 1 / (p - r + q - r) ↔ q - r < p - q := by
  rw [one_div_lt_one_div (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-- The generated payoff in the noisy prisoner's dilemma: with `Pr(G | a) = P`,
`(1 − δ) u_i(a) + δ(P w_i(G) + (1 − P) w_i(B))`. -/
theorem dg_noisyPD_gen {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    (δ : ℝ) (a : Fin 2 → Bool) (w : Bool → Fin 2 → ℝ) (i : Fin 2) :
    dg_gen (dg_noisyPD p q r hr hrq hqp hp) δ a w i =
      (1 - δ) * dg_u (dg_noisyPD p q r hr hrq hqp hp) i a +
        δ * (dg_pdProbG p q r a * w true i + (1 - dg_pdProbG p q r a) * w false i) := by
  simp only [dg_gen, Fintype.sum_bool]
  rfl

/-- **Example 21.1.2** (Miao, pp. 751–753), corrected. If
`1/(p − q + p − r) ≤ δ ≤ 1/(p − r + q − r)` and `δ < 1`, the set
`W = {(v, v), (v', v')}` is self-generating: `(v, v)` is enforced by `(D, D)` and `(v', v')` by
`(C, C)`, both with `w(G) = (v', v')`, `w(B) = (v, v)`. -/
theorem example_21_1_2 {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    {δ : ℝ} (hδ1 : δ < 1) (hlo : 1 / (p - q + p - r) ≤ δ)
    (hhi : δ ≤ 1 / (p - r + q - r)) :
    dg_pdW p r δ ⊆ dg_B (dg_noisyPD p q r hr hrq hqp hp) δ (dg_pdW p r δ) := by
  have hD : 0 < 1 - δ * (p - r) := by nlinarith
  have hpq : p - q ≠ 0 := by linarith
  have hqr : q - r ≠ 0 := by linarith
  let w : Bool → Fin 2 → ℝ := fun y =>
    if y then (fun _ => dg_pdV' p r δ) else (fun _ => dg_pdV p r δ)
  have hw : ∀ y, w y ∈ dg_pdW p r δ := by
    intro y; cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hDDic := (example_21_1_2_DD_ic_iff hrq hqp hδ1 hD).mpr hhi
  have hCCic := (example_21_1_2_CC_ic_iff hrq hqp hδ1 hD).mpr hlo
  have hDDeq := example_21_1_2_DD_eq (p := p) (r := r) hD.ne'
  have hCCeq := example_21_1_2_CC_eq (p := p) (r := r) hD.ne'
  rintro x (rfl | rfl)
  · refine ⟨fun _ => false, w, ⟨hw, ?_⟩, ?_⟩
    · intro i b
      cases b
      · rw [Function.update_eq_self]
      · rw [dg_noisyPD_gen, dg_noisyPD_gen, dg_noisyPD_u_matrix, dg_noisyPD_u_matrix]
        fin_cases i <;> simp [dg_pdMatrix, dg_pdProbG, Function.update, w] <;> linarith
    · funext i
      rw [dg_noisyPD_gen, dg_noisyPD_u_matrix]
      simp only [dg_pdMatrix, dg_pdProbG, w, Bool.and_self, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, ite_self]
      linarith
  · refine ⟨fun _ => true, w, ⟨hw, ?_⟩, ?_⟩
    · intro i b
      cases b
      · rw [dg_noisyPD_gen, dg_noisyPD_gen, dg_noisyPD_u_matrix, dg_noisyPD_u_matrix]
        fin_cases i <;> simp [dg_pdMatrix, dg_pdProbG, Function.update, w] <;> linarith
      · rw [Function.update_eq_self]
    · funext i
      rw [dg_noisyPD_gen, dg_noisyPD_u_matrix]
      simp only [dg_pdMatrix, dg_pdProbG, w, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
        ite_self]
      linarith

/-- **Example 21.1.2** (Miao, p. 752), with Lemma 21.1.2 for PPE: on the corrected interval the
payoffs `(v, v)` and `(v', v')` are PPE payoffs. -/
theorem example_21_1_2_ppe {p q r : ℝ} (hr : 0 ≤ r) (hrq : r < q) (hqp : q < p) (hp : p ≤ 1)
    {δ : ℝ} (hδ1 : δ < 1) (hlo : 1 / (p - q + p - r) ≤ δ)
    (hhi : δ ≤ 1 / (p - r + q - r)) :
    dg_pdW p r δ ⊆ dg_PPEPayoffs (dg_noisyPD p q r hr hrq hqp hp) δ := by
  have hfin : (dg_pdW p r δ).Finite := (Set.finite_singleton _).insert _
  have hδ0 : 0 ≤ δ := le_trans (one_div_pos.mpr (by linarith)).le hlo
  exact dg_selfGenerating_subset_ppe _ hδ0 hδ1 hfin.isBounded
    (example_21_1_2 hr hrq hqp hp hδ1 hlo hhi)

/-- The corrected Example 21.1.2 is not vacuous: `p = 9/10`, `q = 2/5`, `r = 1/10`, `δ = 4/5`
satisfy its hypotheses (with full support and `p − q > q − r`), so `(v, v) = (2/9, 2/9)` and
`(v', v') = (7/9, 7/9)` are PPE payoffs. -/
theorem example_21_1_2_instance :
    ∃ (hr : (0 : ℝ) ≤ 1 / 10) (hrq : (1 / 10 : ℝ) < 2 / 5) (hqp : (2 / 5 : ℝ) < 9 / 10)
      (hp : (9 / 10 : ℝ) ≤ 1),
      dg_pdW (9 / 10) (1 / 10) (4 / 5) ⊆
        dg_PPEPayoffs (dg_noisyPD (9 / 10) (2 / 5) (1 / 10) hr hrq hqp hp) (4 / 5) ∧
      dg_pdV (9 / 10) (1 / 10) (4 / 5) = 2 / 9 ∧ dg_pdV' (9 / 10) (1 / 10) (4 / 5) = 7 / 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · exact example_21_1_2_ppe _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
  · unfold dg_pdV; norm_num
  · unfold dg_pdV'; norm_num

/-- **Example 21.1.2** (Miao, p. 752): the printed claim is false. For `p = 9/10`, `q = 2/5`,
`r = 1/10` (so `p − q > q − r`) and `δ = 19/20`, the printed hypotheses
`1/(p − r) ≥ δ ≥ 1/(p + q − 2r)` hold, but `W = {(v, v), (v', v')}` is not self-generating:
`(v, v)` is not in `B(W)`. -/
theorem example_21_1_2_printed_false :
    ∃ (hr : (0 : ℝ) ≤ 1 / 10) (hrq : (1 / 10 : ℝ) < 2 / 5) (hqp : (2 / 5 : ℝ) < 9 / 10)
      (hp : (9 / 10 : ℝ) ≤ 1),
      (2 / 5 : ℝ) - 1 / 10 < 9 / 10 - 2 / 5 ∧
      (19 / 20 : ℝ) ≤ 1 / (9 / 10 - 1 / 10) ∧ 1 / (9 / 10 + 2 / 5 - 2 * (1 / 10)) ≤ (19 / 20 : ℝ) ∧
      ¬ dg_pdW (9 / 10) (1 / 10) (19 / 20) ⊆
        dg_B (dg_noisyPD (9 / 10) (2 / 5) (1 / 10) hr hrq hqp hp) (19 / 20)
          (dg_pdW (9 / 10) (1 / 10) (19 / 20)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_⟩
  intro hsub
  have hV : dg_pdV (9 / 10) (1 / 10) (19 / 20) = 19 / 48 := by unfold dg_pdV; norm_num
  have hV' : dg_pdV' (9 / 10) (1 / 10) (19 / 20) = 29 / 48 := by unfold dg_pdV'; norm_num
  obtain ⟨a, w, ⟨hw, hic⟩, he⟩ := hsub (Or.inl rfl)
  have e0 := congrFun he 0
  have e1 := congrFun he 1
  rw [dg_noisyPD_gen, dg_noisyPD_u] at e0 e1
  have ic0 := hic 0 true
  rw [dg_noisyPD_gen, dg_noisyPD_gen, dg_noisyPD_u, dg_noisyPD_u] at ic0
  have hw' : ∀ y, w y = (fun _ => (19 / 48 : ℝ)) ∨ w y = (fun _ => (29 / 48 : ℝ)) := by
    intro y
    rcases hw y with h | h
    · left; rw [h, hV]
    · right; rw [Set.mem_singleton_iff.mp h, hV']
  rcases hw' true with ht | ht <;> rcases hw' false with hf | hf <;>
    simp only [ht, hf, hV] at e0 e1 ic0 <;>
    cases h0 : a 0 <;> cases h1 : a 1 <;>
    simp [dg_pdProbG, Function.update, h0, h1] at e0 e1 ic0 <;>
    linarith

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic stochastic games and Markov perfect equilibrium

Miao, §21.2, pp. 753–755. An `n`-player stochastic game `{S, A, p, δ, u}`: states `S`, action
profiles `A = ∏ A_i`, a transition law `p(s' | s, a)`, payoffs `u_i(s, a)` and discount factors
`δ_i`. Markov strategies `σ_t : S → A`; the payoff
`U_i(s₁; σ) = (1 − δ_i) E ∑ δ_i^{t−1} u_i(s_t, σ_t(s_t))`; Markov perfect equilibrium
(Definition 21.2.1). We prove the recursive form of the payoff (`dg_mU_rec`) and that a
stationary Markov profile is an MPE iff its value functions solve the players' coupled Bellman
equations (`definition_21_2_1_bellman_iff`, `dg_stationaryMPE_bellman`). For the deterministic
case we define the Sleet–Yeltekin operator `B` on state-indexed sets (p. 755) and prove that it
is monotone (`dg_SY_mono`) and preserves compactness (`dg_SY_isCompact`), as the text claims.
A repeated prisoner's dilemma, as a one-state stochastic game, has the stationary MPE "always
defect" (`dg_pdStochGame_mpe`).

Setting and departures.
* The state space is a finite type (the text allows a Euclidean state space with a transition
  probability); dates start at `0`; payoffs are bounded by `M`.
* In Definition 21.2.1 the deviations `σ_i` are Markov strategies `τ_t : S → A_i`
  (time-varying). The text does not say which class of strategies a deviator may use; against
  Markov opponents player `i` faces a Markov decision problem.
* The text's claim that the maximal fixed point of `B` is the "Markov perfect equilibrium payoff
  correspondence" is not formalised: `B` uses history-dependent continuation values (the
  punishments `μ_{i,s}`), so its fixed points are subgame perfect, not Markov perfect, payoff
  sets, and the text gives no proof.
-/

namespace Miao.DynamicGames

/-- A stochastic game `{S, A, p, δ, u}` (Miao, p. 753) with finitely many states, bounded payoffs
and player-specific discount factors in `[0, 1)`. -/
structure DGStochGame (ι : Type) (A : ι → Type) (S : Type) [Fintype S] where
  /-- The transition law `p(s' | s, a)`. -/
  P : S → (∀ i, A i) → S → ℝ
  /-- Probabilities are nonnegative. -/
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  /-- Probabilities sum to one. -/
  P_sum : ∀ s a, ∑ s', P s a s' = 1
  /-- Payoffs `u_i(s, a)`. -/
  u : ι → S → (∀ i, A i) → ℝ
  /-- A bound on the payoffs. -/
  M : ℝ
  /-- Payoffs are bounded. -/
  u_bound : ∀ i s a, |u i s a| ≤ M
  /-- Discount factors `δ_i`. -/
  δ : ι → ℝ
  /-- `0 ≤ δ_i`. -/
  δ_nonneg : ∀ i, 0 ≤ δ i
  /-- `δ_i < 1`. -/
  δ_lt_one : ∀ i, δ i < 1

variable {ι : Type} {A : ι → Type} {S : Type} [Fintype S]

/-- A Markov strategy profile continued from date `t`: `(σ|_t)_k = σ_{k + t}`. -/
def dg_shift {B : Type*} (σ : ℕ → B) (t : ℕ) : ℕ → B := fun k => σ (k + t)

/-- The Markov profile in which player `i` uses the Markov strategy `τ` and the others follow
`σ`. -/
def dg_mdev [DecidableEq ι] (σ : ℕ → S → ∀ j, A j) (i : ι) (τ : ℕ → S → A i) :
    ℕ → S → ∀ j, A j := fun t s => Function.update (σ t s) i (τ t s)

/-- The expected payoff of player `i` at date `t` from the current state `s` under the Markov
profile `σ`. -/
def dg_mex (G : DGStochGame ι A S) (i : ι) : ℕ → S → (ℕ → S → ∀ j, A j) → ℝ
  | 0, s, σ => G.u i s (σ 0 s)
  | t + 1, s, σ => ∑ s', G.P s (σ 0 s) s' * dg_mex G i t s' (fun k => σ (k + 1))

/-- Miao, p. 754: the expected discounted average payoff
`U_i(s; σ) = (1 − δ_i) E[∑ δ_iᵗ u_i(s_t, σ_t(s_t)) | s₀ = s]`. -/
noncomputable def dg_mU (G : DGStochGame ι A S) (i : ι) (s : S) (σ : ℕ → S → ∀ j, A j) : ℝ :=
  (1 - G.δ i) * ∑' t : ℕ, G.δ i ^ t * dg_mex G i t s σ

/-- `|E u_i(s_t, σ_t(s_t))| ≤ M` at every date. -/
theorem dg_abs_mex_le (G : DGStochGame ι A S) (i : ι) (t : ℕ) :
    ∀ s (σ : ℕ → S → ∀ j, A j), |dg_mex G i t s σ| ≤ G.M := by
  induction t with
  | zero => intro s σ; exact G.u_bound i s _
  | succ t ih =>
      intro s σ
      exact dg_abs_avg_le _ (G.P_nonneg s _) (G.P_sum s _) _ _ fun s' => ih s' _

/-- The discounted series defining `U_i(s; σ)` is summable. -/
theorem dg_msummable (G : DGStochGame ι A S) (i : ι) (s : S) (σ : ℕ → S → ∀ j, A j) :
    Summable fun t : ℕ => G.δ i ^ t * dg_mex G i t s σ := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (G.δ_nonneg i) (G.δ_lt_one i)).mul_left G.M) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (G.δ_nonneg i), mul_comm]
  exact mul_le_mul_of_nonneg_right (dg_abs_mex_le G i t s σ) (pow_nonneg (G.δ_nonneg i) t)

/-- `|U_i(s; σ)| ≤ M`. -/
theorem dg_abs_mU_le (G : DGStochGame ι A S) (i : ι) (s : S) (σ : ℕ → S → ∀ j, A j) :
    |dg_mU G i s σ| ≤ G.M := by
  have hδ0 := G.δ_nonneg i
  have hδ1 := G.δ_lt_one i
  have hg := (summable_geometric_of_lt_one hδ0 hδ1).mul_left G.M
  have hs := dg_msummable G i s σ
  have hgeo : ∑' t : ℕ, G.M * G.δ i ^ t = G.M * (1 - G.δ i)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1]
  have hb : ∀ t : ℕ, |G.δ i ^ t * dg_mex G i t s σ| ≤ G.M * G.δ i ^ t := fun t => by
    rw [abs_mul, abs_pow, abs_of_nonneg hδ0, mul_comm]
    exact mul_le_mul_of_nonneg_right (dg_abs_mex_le G i t s σ) (pow_nonneg hδ0 t)
  have hup : ∑' t : ℕ, G.δ i ^ t * dg_mex G i t s σ ≤ G.M * (1 - G.δ i)⁻¹ :=
    hgeo ▸ hs.tsum_le_tsum (fun t => (abs_le.mp (hb t)).2) hg
  have hlo : -(G.M * (1 - G.δ i)⁻¹) ≤ ∑' t : ℕ, G.δ i ^ t * dg_mex G i t s σ := by
    have := hg.neg.tsum_le_tsum (fun t => (abs_le.mp (hb t)).1) hs
    rwa [tsum_neg, hgeo] at this
  have h1 : 0 < 1 - G.δ i := by linarith
  have e : (1 - G.δ i) * (G.M * (1 - G.δ i)⁻¹) = G.M := by field_simp
  unfold dg_mU
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hlo h1.le
    rw [mul_neg, e] at this
    exact this
  · have := mul_le_mul_of_nonneg_left hup h1.le
    rwa [e] at this

/-- Miao, p. 754: the payoff of a Markov profile is the current payoff plus the discounted
expected continuation payoff,
`U_i(s; σ) = (1 − δ_i) u_i(s, σ₀(s)) + δ_i ∑_{s'} p(s' | s, σ₀(s)) U_i(s'; σ|₁)`. -/
theorem dg_mU_rec (G : DGStochGame ι A S) (i : ι) (s : S) (σ : ℕ → S → ∀ j, A j) :
    dg_mU G i s σ = (1 - G.δ i) * G.u i s (σ 0 s) +
      G.δ i * ∑ s', G.P s (σ 0 s) s' * dg_mU G i s' (dg_shift σ 1) := by
  have hs := dg_msummable G i s σ
  have h1 : ∀ t : ℕ, G.δ i ^ (t + 1) * dg_mex G i (t + 1) s σ =
      G.δ i * ∑ s', G.P s (σ 0 s) s' * (G.δ i ^ t * dg_mex G i t s' (dg_shift σ 1)) := by
    intro t
    simp only [dg_mex, Finset.mul_sum, pow_succ]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have hc : dg_shift σ 1 = fun k => σ (k + 1) := rfl
    rw [hc]
    ring
  have key : ∑' t : ℕ, G.δ i ^ (t + 1) * dg_mex G i (t + 1) s σ =
      G.δ i * ∑ s', G.P s (σ 0 s) s' * ∑' t : ℕ, G.δ i ^ t * dg_mex G i t s' (dg_shift σ 1) := by
    rw [tsum_congr h1, tsum_mul_left,
      Summable.tsum_finsetSum fun s' _ => (dg_msummable G i s' _).mul_left _]
    congr 1
    exact Finset.sum_congr rfl fun s' _ => tsum_mul_left
  have h2 : ∑ s', G.P s (σ 0 s) s' * dg_mU G i s' (dg_shift σ 1) =
      (1 - G.δ i) * ∑ s', G.P s (σ 0 s) s' *
        ∑' t : ℕ, G.δ i ^ t * dg_mex G i t s' (dg_shift σ 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by unfold dg_mU; ring
  rw [h2]
  unfold dg_mU
  rw [hs.tsum_eq_zero_add, key]
  simp only [pow_zero, one_mul, dg_mex]
  ring

/-- **Definition 21.2.1** (Miao, p. 754). A Markov profile `σ = {σ_t}` is a Markov perfect
equilibrium if at every date `t` and state `s`, no player gains by deviating to another Markov
strategy from then on: `U_i(s; σ|_t) ≥ U_i(s; (τ, σ₋ᵢ)|_t)`. -/
def dg_IsMPE [DecidableEq ι] (G : DGStochGame ι A S) (σ : ℕ → S → ∀ j, A j) : Prop :=
  ∀ t s i (τ : ℕ → S → A i), dg_mU G i s (dg_mdev (dg_shift σ t) i τ) ≤ dg_mU G i s (dg_shift σ t)

/-- **Definition 21.2.1** (Miao, p. 754): a stationary MPE is an MPE `σ_t = σ` independent of
`t`. -/
def dg_IsStationaryMPE [DecidableEq ι] (G : DGStochGame ι A S) (σ : S → ∀ j, A j) : Prop :=
  dg_IsMPE G (fun _ => σ)

/-- The value functions `V_i(s) = U_i(s; σ)` of a stationary Markov profile. -/
noncomputable def dg_mV (G : DGStochGame ι A S) (σ : S → ∀ j, A j) (i : ι) (s : S) : ℝ :=
  dg_mU G i s (fun _ => σ)

/-- The Bellman equation of a stationary profile (Miao, p. 754):
`V_i(s) = (1 − δ_i) u_i(s, σ(s)) + δ_i ∑_{s'} p(s' | s, σ(s)) V_i(s')`. -/
theorem dg_mV_bellman (G : DGStochGame ι A S) (σ : S → ∀ j, A j) (i : ι) (s : S) :
    dg_mV G σ i s = (1 - G.δ i) * G.u i s (σ s) +
      G.δ i * ∑ s', G.P s (σ s) s' * dg_mV G σ i s' := by
  unfold dg_mV
  rw [dg_mU_rec]
  rfl

/-- **Definition 21.2.1** (Miao, pp. 754–755): a stationary Markov profile `σ` is a stationary
MPE iff no player gains from a one-period deviation at any state:
`(1 − δ_i) u_i(s, b, σ₋ᵢ(s)) + δ_i ∑_{s'} p(s' | s, b, σ₋ᵢ(s)) V_i(s') ≤ V_i(s)` for all
`i, s, b` (the coupled Bellman inequalities). -/
theorem definition_21_2_1_bellman_iff [DecidableEq ι] (G : DGStochGame ι A S)
    (σ : S → ∀ j, A j) :
    dg_IsStationaryMPE G σ ↔ ∀ i s (b : A i),
      (1 - G.δ i) * G.u i s (Function.update (σ s) i b) +
        G.δ i * ∑ s', G.P s (Function.update (σ s) i b) s' * dg_mV G σ i s' ≤
        dg_mV G σ i s := by
  have hsh : ∀ t, dg_shift (fun _ : ℕ => σ) t = fun _ => σ := fun t => rfl
  constructor
  · intro H i s b
    let τ : ℕ → S → A i := fun k s' => if k = 0 then b else σ s' i
    have h := H 0 s i τ
    rw [hsh, dg_mU_rec] at h
    have h1 : dg_shift (dg_mdev (fun _ => σ) i τ) 1 = fun _ => σ := by
      funext k s'
      simp only [dg_shift, dg_mdev, τ, Nat.add_one_ne_zero, ↓reduceIte, Function.update_eq_self]
    have h0 : dg_mdev (fun _ => σ) i τ 0 s = Function.update (σ s) i b := by
      simp only [dg_mdev, τ, ↓reduceIte]
    rw [h1, h0] at h
    exact h
  · intro H t s0 i τ'
    rw [hsh]
    suffices key : ∀ τ : ℕ → S → A i, ∀ t s,
        dg_mU G i s (dg_mdev (fun _ => σ) i (dg_shift τ t)) ≤ dg_mV G σ i s by
      have := key (fun k => τ' (k - t)) t s0
      have e : dg_shift (fun k => τ' (k - t)) t = τ' := by
        funext k; simp only [dg_shift, Nat.add_sub_cancel]
      rwa [e] at this
    intro τ
    let D : ℕ × S → ℝ := fun x => dg_mU G i x.2 (dg_mdev (fun _ => σ) i (dg_shift τ x.1))
    let g : ℕ × S → ℝ := fun x => D x - dg_mV G σ i x.2
    have hD : ∀ t s, D (t, s) = (1 - G.δ i) * G.u i s (Function.update (σ s) i (τ t s)) +
        G.δ i * ∑ s', G.P s (Function.update (σ s) i (τ t s)) s' * D (t + 1, s') := by
      intro t s
      have hc : dg_shift (dg_mdev (fun _ => σ) i (dg_shift τ t)) 1 =
          dg_mdev (fun _ => σ) i (dg_shift τ (t + 1)) := by
        funext k s'
        simp only [dg_shift, dg_mdev, Nat.add_assoc, Nat.add_comm 1 t]
      have h0 : dg_mdev (fun _ => σ) i (dg_shift τ t) 0 s = Function.update (σ s) i (τ t s) := by
        simp only [dg_mdev, dg_shift, Nat.zero_add]
      simp only [D]
      rw [dg_mU_rec, hc, h0]
    have hb : BddAbove (Set.range g) := by
      refine ⟨2 * G.M, ?_⟩
      rintro _ ⟨x, rfl⟩
      have h1 := abs_le.mp (dg_abs_mU_le G i x.2 (dg_mdev (fun _ => σ) i (dg_shift τ x.1)))
      have h2 := abs_le.mp (dg_abs_mU_le G i x.2 (fun _ => σ))
      simp only [g, D, dg_mV]
      linarith [h1.2, h2.1]
    have hg : ∀ x, g x ≤ G.δ i * ⨆ z, g z := by
      rintro ⟨t, s⟩
      have hos := H i s (τ t s)
      have havg := dg_avg_le_iSup g hb _ (G.P_nonneg s (Function.update (σ s) i (τ t s)))
        (G.P_sum s _) (fun s' => (t + 1, s'))
      have hsplit : ∑ s', G.P s (Function.update (σ s) i (τ t s)) s' * g (t + 1, s') =
          ∑ s', G.P s (Function.update (σ s) i (τ t s)) s' * D (t + 1, s') -
            ∑ s', G.P s (Function.update (σ s) i (τ t s)) s' * dg_mV G σ i s' := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by simp only [g]; ring
      rw [hsplit] at havg
      have hD' := hD t s
      simp only [g]
      rw [hD']
      nlinarith [mul_le_mul_of_nonneg_left havg (G.δ_nonneg i)]
    exact fun t s => sub_nonpos.mp (dg_nonpos_of_le_mul_iSup g hb (G.δ_lt_one i) hg (t, s))

/-- The coupled Bellman equations (Miao, pp. 754–756): `σ` is a stationary MPE iff for every
player `i` and state `s`, `V_i(s)` is the largest value of
`(1 − δ_i) u_i(s, b, σ₋ᵢ(s)) + δ_i ∑_{s'} p(s' | s, b, σ₋ᵢ(s)) V_i(s')` over `b ∈ A_i`, attained
at `b = σ_i(s)`. -/
theorem dg_stationaryMPE_bellman [DecidableEq ι] (G : DGStochGame ι A S) (σ : S → ∀ j, A j) :
    dg_IsStationaryMPE G σ ↔ ∀ i s, IsGreatest (Set.range fun b : A i =>
      (1 - G.δ i) * G.u i s (Function.update (σ s) i b) +
        G.δ i * ∑ s', G.P s (Function.update (σ s) i b) s' * dg_mV G σ i s') (dg_mV G σ i s) := by
  rw [definition_21_2_1_bellman_iff]
  constructor
  · intro H i s
    refine ⟨⟨σ s i, ?_⟩, ?_⟩
    · simp only [Function.update_eq_self]
      exact (dg_mV_bellman G σ i s).symm
    · rintro _ ⟨b, rfl⟩
      exact H i s b
  · intro H i s b
    exact (H i s).2 ⟨b, rfl⟩

/-- The punishment value `μ_{i,s} = min{w_i : w ∈ W_s}` of the Sleet–Yeltekin operator
(Miao, p. 755), as an infimum. -/
noncomputable def dg_SYmu {S' : Type} (W : S' → Set (ι → ℝ)) (i : ι) (s : S') : ℝ :=
  sInf ((fun w => w i) '' W s)

/-- The Sleet–Yeltekin operator for a deterministic dynamic game `s' = f(s, a)` (Miao, p. 755):
`B(W)_s` is the set of `(1 − δ) u(s, a) + δ w` with `w ∈ W_{f(s,a)}` and, for every player and
one-period deviation `a'_i`, `(1 − δ) u_i(s, a) + δ w_i ≥ (1 − δ) u_i(s, a'_i, a₋ᵢ) +
δ μ_{i, f(s, a'_i, a₋ᵢ)}`. -/
def dg_SY [DecidableEq ι] {S' : Type} (u : ι → S' → (∀ j, A j) → ℝ) (f : S' → (∀ j, A j) → S')
    (δ : ℝ) (W : S' → Set (ι → ℝ)) (s : S') : Set (ι → ℝ) :=
  {v | ∃ a w, w ∈ W (f s a) ∧
    (∀ i (b : A i), (1 - δ) * u i s (Function.update a i b) +
      δ * dg_SYmu W i (f s (Function.update a i b)) ≤ (1 - δ) * u i s a + δ * w i) ∧
    v = fun i => (1 - δ) * u i s a + δ * w i}

/-- Miao, p. 755: "`B` is monotone". If `W_s ⊆ W'_s` for every state, with `W_s` nonempty and
`W'_s` bounded below in every coordinate (as for nonempty compact values), then
`B(W)_s ⊆ B(W')_s`: the continuation set grows and the punishments `μ` fall. -/
theorem dg_SY_mono [DecidableEq ι] {S' : Type} (u : ι → S' → (∀ j, A j) → ℝ)
    (f : S' → (∀ j, A j) → S') {δ : ℝ} (hδ0 : 0 ≤ δ) {W W' : S' → Set (ι → ℝ)}
    (hWW : ∀ s, W s ⊆ W' s) (hne : ∀ s, (W s).Nonempty)
    (hbdd : ∀ s i, BddBelow ((fun w => w i) '' W' s)) (s : S') :
    dg_SY u f δ W s ⊆ dg_SY u f δ W' s := by
  rintro v ⟨a, w, hw, hic, rfl⟩
  refine ⟨a, w, hWW _ hw, fun i b => le_trans ?_ (hic i b), rfl⟩
  have hmu : dg_SYmu W' i (f s (Function.update a i b)) ≤
      dg_SYmu W i (f s (Function.update a i b)) :=
    csInf_le_csInf (hbdd _ i) ((hne _).image _) (Set.image_mono (hWW _))
  have := mul_le_mul_of_nonneg_left hmu hδ0
  linarith

/-- Miao, p. 755: "`B` … preserves compactness". With finitely many action profiles, if every
`W_s` is compact then every `B(W)_s` is compact. -/
theorem dg_SY_isCompact [DecidableEq ι] [Finite (∀ j, A j)] {S' : Type}
    (u : ι → S' → (∀ j, A j) → ℝ) (f : S' → (∀ j, A j) → S') (δ : ℝ) {W : S' → Set (ι → ℝ)}
    (hW : ∀ s, IsCompact (W s)) (s : S') : IsCompact (dg_SY u f δ W s) := by
  let L : (∀ j, A j) → (ι → ℝ) → (ι → ℝ) := fun a w i => (1 - δ) * u i s a + δ * w i
  have hL : ∀ a, Continuous (L a) := fun a =>
    continuous_pi fun i => continuous_const.add (continuous_const.mul (continuous_apply i))
  have hset : dg_SY u f δ W s = ⋃ a : (∀ j, A j), L a '' (W (f s a) ∩
      {w | ∀ i (b : A i), (1 - δ) * u i s (Function.update a i b) +
        δ * dg_SYmu W i (f s (Function.update a i b)) ≤ (1 - δ) * u i s a + δ * w i}) := by
    ext v
    simp only [dg_SY, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, w, hw, hic, rfl⟩
      exact ⟨a, w, ⟨hw, hic⟩, rfl⟩
    · rintro ⟨a, w, ⟨hw, hic⟩, rfl⟩
      exact ⟨a, w, hw, hic, rfl⟩
  rw [hset]
  refine isCompact_iUnion fun a => IsCompact.image ?_ (hL a)
  refine (hW _).inter_right ?_
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun b => isClosed_le continuous_const ?_
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

/-- Miao, p. 753 ("repeated games are the special case of this model"): the prisoner's dilemma of
Example 21.1.1 as a stochastic game with a single state and common discount factor `δ`. -/
noncomputable def dg_pdStochGame (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    DGStochGame (Fin 2) (fun _ => Bool) Unit where
  P _ _ _ := 1
  P_nonneg _ _ _ := zero_le_one
  P_sum _ _ := by simp
  u i _ a := dg_pdMatrix (a i) (if i = 0 then a 1 else a 0)
  M := 2
  u_bound i _ a := by
    unfold dg_pdMatrix
    split_ifs <;> norm_num
  δ _ := δ
  δ_nonneg _ := hδ0
  δ_lt_one _ := hδ1

/-- Definition 21.2.1 is not vacuous: in the single-state prisoner's dilemma, always defecting is
a stationary Markov perfect equilibrium for every `δ ∈ [0, 1)`, with value `0`. -/
theorem dg_pdStochGame_mpe (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    dg_IsStationaryMPE (dg_pdStochGame δ hδ0 hδ1) (fun _ _ => false) ∧
      ∀ i, dg_mV (dg_pdStochGame δ hδ0 hδ1) (fun _ _ => false) i () = 0 := by
  have hV : ∀ i, dg_mV (dg_pdStochGame δ hδ0 hδ1) (fun _ _ => false) i () = 0 := by
    intro i
    have h := dg_mV_bellman (dg_pdStochGame δ hδ0 hδ1) (fun _ _ => false) i ()
    have hu : (dg_pdStochGame δ hδ0 hδ1).u i () (fun _ => false) = 0 := by
      simp [dg_pdStochGame, dg_pdMatrix]
    have hP : ∀ a s s', (dg_pdStochGame δ hδ0 hδ1).P s a s' = 1 := fun _ _ _ => rfl
    have hd : (dg_pdStochGame δ hδ0 hδ1).δ i = δ := rfl
    simp only [hu, hP, hd, one_mul, Fintype.univ_unit, Finset.sum_singleton, mul_zero,
      zero_add] at h
    have : (1 - δ) * dg_mV (dg_pdStochGame δ hδ0 hδ1) (fun _ _ => false) i () = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left (by linarith)
  refine ⟨(definition_21_2_1_bellman_iff _ _).mpr fun i s b => ?_, hV⟩
  have hP : ∀ a s s', (dg_pdStochGame δ hδ0 hδ1).P s a s' = 1 := fun _ _ _ => rfl
  have hd : (dg_pdStochGame δ hδ0 hδ1).δ i = δ := rfl
  have hs : s = () := rfl
  subst hs
  simp only [hP, hd, Fintype.univ_unit, Finset.sum_singleton, hV, mul_zero, add_zero]
  have hu : (dg_pdStochGame δ hδ0 hδ1).u i () (Function.update (fun _ => false) i b) ≤ 0 := by
    simp only [dg_pdStochGame]
    fin_cases i <;> cases b <;> simp [dg_pdMatrix, Function.update]
  nlinarith

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The log fishing problem behind the Great Fish War

Miao, §21.3, pp. 755–757. Every best-response problem of §21.3 (each country in the Markov
perfect equilibrium, the Stackelberg leader, and the Stackelberg follower of Exercise 21.3)
reduces to one problem: given the stock `x`, catch `c ∈ (0, Rx)`, leaving the stock
`x' = (θ(Rx − c))^α` for next period, to maximise `∑ βᵗ ln c_t`. Here `R x` is what the other
country leaves and `θ` the share of the remainder that survives its reaction.

We solve it by the guess-and-verify method of the text: `V(x) = κ ln x + ν` with
`κ = 1/(1 − αβ)` solves the Bellman equation, the unique maximiser being `c = (1 − αβ) R x`
(`dg_fp_bellman`, `dg_fp_bellman_eq`, `dg_fp_bellman_unique`). Coefficient matching forces
`κ = 1/(1 − αβ)` (`dg_fp_kappa_forced`). Then `V(x₀)` is the value of the problem: every
feasible plan whose discounted utility series converges does no better (`dg_fp_optimal`), and
the policy plan attains it (`dg_fp_policy_value`). Along the policy plan the stock converges to
`x̄ = (θαβR)^{α/(1−α)}` (`dg_fp_path_tendsto`).

The maximisation step is the elementary fact that `ln c + K ln(R − c)` has its unique maximum on
`(0, R)` at `c = R/(1 + K)` (`dg_log_max`), proved from `ln y ≤ y − 1`.
-/

namespace Miao.DynamicGames

/-- The maximisation step of §21.3 (Miao, pp. 756–757): for `R, K > 0` and `0 < c < R`,
`ln c + K ln(R − c) ≤ ln c* + K ln(R − c*)` with `c* = R/(1 + K)`, strictly unless `c = c*`. -/
theorem dg_log_max {R K c : ℝ} (hR : 0 < R) (hK : 0 < K) (hc0 : 0 < c) (hcR : c < R) :
    Real.log c + K * Real.log (R - c) ≤
      Real.log (R / (1 + K)) + K * Real.log (R - R / (1 + K)) ∧
    (c ≠ R / (1 + K) → Real.log c + K * Real.log (R - c) <
      Real.log (R / (1 + K)) + K * Real.log (R - R / (1 + K))) := by
  have h1K : 0 < 1 + K := by linarith
  have hcs : 0 < R / (1 + K) := div_pos hR h1K
  have hds : R - R / (1 + K) = K * R / (1 + K) := by field_simp; ring
  have hdp : 0 < R - R / (1 + K) := by rw [hds]; positivity
  have hRc : 0 < R - c := by linarith
  have e1 : Real.log c - Real.log (R / (1 + K)) = Real.log (c / (R / (1 + K))) :=
    (Real.log_div hc0.ne' hcs.ne').symm
  have e2 : Real.log (R - c) - Real.log (R - R / (1 + K)) =
      Real.log ((R - c) / (R - R / (1 + K))) := (Real.log_div hRc.ne' hdp.ne').symm
  have hsum : (c / (R / (1 + K)) - 1) + K * ((R - c) / (R - R / (1 + K)) - 1) = 0 := by
    rw [hds]; field_simp; ring
  have hq1 : 0 < c / (R / (1 + K)) := div_pos hc0 hcs
  have hq2 : 0 < (R - c) / (R - R / (1 + K)) := div_pos hRc hdp
  have l2 := Real.log_le_sub_one_of_pos hq2
  constructor
  · have l1 := Real.log_le_sub_one_of_pos hq1
    nlinarith [mul_le_mul_of_nonneg_left l2 hK.le]
  · intro hne
    have hne1 : c / (R / (1 + K)) ≠ 1 := by
      intro h
      exact hne ((div_eq_one_iff_eq hcs.ne').mp h)
    have l1 := Real.log_lt_sub_one_of_pos hq1 hne1
    nlinarith [mul_le_mul_of_nonneg_left l2 hK.le]

/-- The next stock `x' = (θ(Rx − c))^α` of the fishing problem. -/
noncomputable def dg_fpNext (α R θ x c : ℝ) : ℝ := (θ * (R * x - c)) ^ α

/-- The coefficient `κ = 1/(1 − αβ)` of `ln x` in the value function. -/
noncomputable def dg_fpKappa (α β : ℝ) : ℝ := 1 / (1 - α * β)

/-- The constant `ν = (ln((1 − αβ)R) + K ln(αβR) + K ln θ)/(1 − β)` of the value function, with
`K = αβκ = αβ/(1 − αβ)`. -/
noncomputable def dg_fpNu (α β R θ : ℝ) : ℝ :=
  (Real.log ((1 - α * β) * R) + α * β * dg_fpKappa α β * Real.log (α * β * R) +
    α * β * dg_fpKappa α β * Real.log θ) / (1 - β)

/-- The conjectured value function `V(x) = κ ln x + ν` (Miao, p. 756). -/
noncomputable def dg_fpV (α β R θ x : ℝ) : ℝ := dg_fpKappa α β * Real.log x + dg_fpNu α β R θ

/-- The right side of the Bellman equation, `ln c + β V((θ(Rx − c))^α)`. -/
noncomputable def dg_fpRHS (α β R θ x c : ℝ) : ℝ :=
  Real.log c + β * dg_fpV α β R θ (dg_fpNext α R θ x c)

/-- The Bellman right side in reduced form: `ln c + K ln(Rx − c) + K ln θ + βν`, `K = αβκ`. -/
theorem dg_fpRHS_eq {α β R θ x c : ℝ} (hθ : 0 < θ) (hc : c < R * x) :
    dg_fpRHS α β R θ x c = Real.log c + α * β * dg_fpKappa α β * Real.log (R * x - c) +
      α * β * dg_fpKappa α β * Real.log θ + β * dg_fpNu α β R θ := by
  have hp : 0 < θ * (R * x - c) := mul_pos hθ (by linarith)
  unfold dg_fpRHS dg_fpV dg_fpNext
  rw [Real.log_rpow hp, Real.log_mul hθ.ne' (by linarith)]
  ring

/-- `K = αβκ` satisfies `1 + K = κ`. -/
theorem dg_fpKappa_eq {α β : ℝ} (hab : α * β < 1) :
    1 + α * β * dg_fpKappa α β = dg_fpKappa α β := by
  unfold dg_fpKappa
  have : 1 - α * β ≠ 0 := by linarith
  field_simp
  ring

/-- Miao, p. 757 ("substituting this rule back into the Bellman equation"): at the policy
`c = (1 − αβ)Rx` the Bellman equation `V(x) = ln c + βV(x')` holds with `κ = 1/(1 − αβ)`. -/
theorem dg_fp_bellman_eq {α β R θ x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx : 0 < x) :
    dg_fpRHS α β R θ x ((1 - α * β) * R * x) = dg_fpV α β R θ x := by
  have h1 : 0 < 1 - α * β := by linarith
  have hab0 : 0 < α * β := mul_pos hα hβ
  rw [dg_fpRHS_eq hθ (by nlinarith [mul_pos hab0 (mul_pos hR hx)])]
  have e1 : R * x - (1 - α * β) * R * x = (α * β * R) * x := by ring
  rw [e1, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hx.ne']
  unfold dg_fpV dg_fpNu dg_fpKappa
  have hb : 1 - β ≠ 0 := by linarith
  field_simp
  ring

/-- The guess-and-verify step (Miao, pp. 756–757): `V(x) = κ ln x + ν` solves the Bellman
inequality `ln c + βV((θ(Rx − c))^α) ≤ V(x)` for every feasible catch `0 < c < Rx`. -/
theorem dg_fp_bellman {α β R θ x c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx : 0 < x) (hc0 : 0 < c) (hc : c < R * x) :
    dg_fpRHS α β R θ x c ≤ dg_fpV α β R θ x := by
  have h1 : 0 < 1 - α * β := by linarith
  have hK : 0 < α * β * dg_fpKappa α β := by unfold dg_fpKappa; positivity
  have hstar : (R * x) / (1 + α * β * dg_fpKappa α β) = (1 - α * β) * R * x := by
    rw [dg_fpKappa_eq hab]; unfold dg_fpKappa; field_simp
  have hm := (dg_log_max (mul_pos hR hx) hK hc0 hc).1
  rw [hstar] at hm
  have hlt : (1 - α * β) * R * x < R * x := by
    nlinarith [mul_pos (mul_pos hα hβ) (mul_pos hR hx)]
  rw [← dg_fp_bellman_eq hα hβ hab hβ1 hR hθ hx, dg_fpRHS_eq hθ hc, dg_fpRHS_eq hθ hlt]
  linarith

/-- The maximiser of the Bellman equation is unique: any catch `c ≠ (1 − αβ)Rx` gives strictly
less (Miao, p. 757, "the first-order condition"). -/
theorem dg_fp_bellman_unique {α β R θ x c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx : 0 < x) (hc0 : 0 < c) (hc : c < R * x)
    (hne : c ≠ (1 - α * β) * R * x) : dg_fpRHS α β R θ x c < dg_fpV α β R θ x := by
  have h1 : 0 < 1 - α * β := by linarith
  have hK : 0 < α * β * dg_fpKappa α β := by unfold dg_fpKappa; positivity
  have hstar : (R * x) / (1 + α * β * dg_fpKappa α β) = (1 - α * β) * R * x := by
    rw [dg_fpKappa_eq hab]; unfold dg_fpKappa; field_simp
  have hm := (dg_log_max (mul_pos hR hx) hK hc0 hc).2 (by rw [hstar]; exact hne)
  rw [hstar] at hm
  have hlt : (1 - α * β) * R * x < R * x := by
    nlinarith [mul_pos (mul_pos hα hβ) (mul_pos hR hx)]
  rw [← dg_fp_bellman_eq hα hβ hab hβ1 hR hθ hx, dg_fpRHS_eq hθ hc, dg_fpRHS_eq hθ hlt]
  linarith

/-- Miao, p. 756 ("substituting these decision rules back into the value functions, we can
solve `κ_i = 1/(1 − αβ_i)`"): if `κ ln x + ν = ln(kx) + β(κα ln(sx) + ν)` for all `x > 0`
(a linear catch `kx` leaving `sx`), then `κ = 1/(1 − αβ)`. -/
theorem dg_fp_kappa_forced {α β κ ν k s : ℝ} (hab : α * β < 1) (hk : 0 < k) (hs : 0 < s)
    (h : ∀ x : ℝ, 0 < x → κ * Real.log x + ν =
      Real.log (k * x) + β * (κ * α * Real.log (s * x) + ν)) :
    κ = 1 / (1 - α * β) := by
  have h1 := h 1 one_pos
  have he := h (Real.exp 1) (Real.exp_pos 1)
  rw [Real.log_mul hk.ne' (Real.exp_pos 1).ne', Real.log_mul hs.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at he
  rw [mul_one, mul_one, Real.log_one] at h1
  have hk1 : κ = 1 + α * β * κ := by linarith
  have : 1 - α * β ≠ 0 := by linarith
  field_simp
  linarith

/-- Telescoping the Bellman inequality along a feasible plan:
`∑_{t<T} βᵗ ln c_t + βᵀ V(x_T) ≤ V(x₀)`. -/
theorem dg_fp_telescope {α β R θ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (x c : ℕ → ℝ)
    (hfeas : ∀ t, 0 < c t ∧ c t < R * x t) (hlaw : ∀ t, x (t + 1) = dg_fpNext α R θ (x t) (c t))
    (T : ℕ) : ∑ t ∈ Finset.range T, β ^ t * Real.log (c t) + β ^ T * dg_fpV α β R θ (x T) ≤
      dg_fpV α β R θ (x 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hxT : 0 < x T := by
        have := (hfeas T).1.trans (hfeas T).2
        exact pos_of_mul_pos_right this hR.le
      have hb := dg_fp_bellman hα hβ hab hβ1 hR hθ hxT (hfeas T).1 (hfeas T).2
      unfold dg_fpRHS at hb
      rw [← hlaw T] at hb
      rw [Finset.sum_range_succ]
      have := mul_le_mul_of_nonneg_left hb (pow_nonneg hβ.le T)
      rw [pow_succ]
      nlinarith

/-- Optimality of the guess (Miao, p. 756): every feasible plan (`0 < c_t < Rx_t`,
`x_{t+1} = (θ(Rx_t − c_t))^α`) whose discounted utility series converges yields at most
`V(x₀)`. -/
theorem dg_fp_optimal {α β R θ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (x c : ℕ → ℝ)
    (hfeas : ∀ t, 0 < c t ∧ c t < R * x t) (hlaw : ∀ t, x (t + 1) = dg_fpNext α R θ (x t) (c t))
    (hsum : Summable fun t => β ^ t * Real.log (c t)) :
    ∑' t, β ^ t * Real.log (c t) ≤ dg_fpV α β R θ (x 0) := by
  have hκ : 0 < dg_fpKappa α β := by unfold dg_fpKappa; exact one_div_pos.mpr (by linarith)
  let e : ℕ → ℝ := fun T => dg_fpKappa α β * (β ^ T * Real.log (c T)) -
    dg_fpKappa α β * Real.log R * β ^ T + dg_fpNu α β R θ * β ^ T
  have hlow : ∀ T, e T ≤ β ^ T * dg_fpV α β R θ (x T) := by
    intro T
    have hxT : 0 < x T := pos_of_mul_pos_right ((hfeas T).1.trans (hfeas T).2) hR.le
    have hl : Real.log (c T) ≤ Real.log R + Real.log (x T) := by
      rw [← Real.log_mul hR.ne' hxT.ne']
      exact Real.log_le_log (hfeas T).1 (hfeas T).2.le
    have hbT := pow_nonneg hβ.le T
    simp only [e]
    unfold dg_fpV
    nlinarith [mul_le_mul_of_nonneg_left hl (mul_nonneg hκ.le hbT)]
  have hβT := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
  have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
    have h1 := (hsum.tendsto_atTop_zero.const_mul (dg_fpKappa α β))
    have h2 := hβT.const_mul (dg_fpKappa α β * Real.log R)
    have h3 := hβT.const_mul (dg_fpNu α β R θ)
    have := (h1.sub h2).add h3
    simpa using this
  have hS := hsum.hasSum.tendsto_sum_nat
  have hR' : Filter.Tendsto (fun T => dg_fpV α β R θ (x 0) - e T) Filter.atTop
      (nhds (dg_fpV α β R θ (x 0) - 0)) := tendsto_const_nhds.sub he
  rw [sub_zero] at hR'
  refine le_of_tendsto_of_tendsto' hS hR' fun T => ?_
  have := dg_fp_telescope hα hβ hab hβ1 hR hθ x c hfeas hlaw T
  linarith [hlow T]

/-- The stock path under the policy `c = (1 − αβ)Rx`: `x_{t+1} = (θαβR x_t)^α`. -/
noncomputable def dg_fpPath (α β R θ x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => (θ * α * β * R * dg_fpPath α β R θ x₀ t) ^ α

/-- The stock stays positive along the policy path. -/
theorem dg_fpPath_pos {α β R θ x₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hR : 0 < R) (hθ : 0 < θ)
    (hx₀ : 0 < x₀) (t : ℕ) : 0 < dg_fpPath α β R θ x₀ t := by
  induction t with
  | zero => exact hx₀
  | succ t ih => exact Real.rpow_pos_of_pos (by positivity) _

/-- Along the policy path `ln x_{t+1} = α(ln(θαβR) + ln x_t)`. -/
theorem dg_fpPath_log {α β R θ x₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hR : 0 < R) (hθ : 0 < θ)
    (hx₀ : 0 < x₀) (t : ℕ) : Real.log (dg_fpPath α β R θ x₀ (t + 1)) =
      α * (Real.log (θ * α * β * R) + Real.log (dg_fpPath α β R θ x₀ t)) := by
  have hp := dg_fpPath_pos hα hβ hR hθ hx₀ t
  change Real.log ((θ * α * β * R * dg_fpPath α β R θ x₀ t) ^ α) = _
  rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) hp.ne']

/-- The policy plan is feasible: `0 < (1 − αβ)Rx_t < Rx_t` and `x_{t+1}` follows the law. -/
theorem dg_fpPath_feasible {α β R θ x₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) (t : ℕ) :
    (0 < (1 - α * β) * R * dg_fpPath α β R θ x₀ t ∧
      (1 - α * β) * R * dg_fpPath α β R θ x₀ t < R * dg_fpPath α β R θ x₀ t) ∧
    dg_fpPath α β R θ x₀ (t + 1) =
      dg_fpNext α R θ (dg_fpPath α β R θ x₀ t) ((1 - α * β) * R * dg_fpPath α β R θ x₀ t) := by
  have hp := dg_fpPath_pos hα hβ hR hθ hx₀ t
  have h1 : 0 < 1 - α * β := by linarith
  have hab0 : 0 < α * β := mul_pos hα hβ
  refine ⟨⟨by positivity, ?_⟩, ?_⟩
  · have := mul_pos hR hp
    nlinarith
  · change (θ * α * β * R * dg_fpPath α β R θ x₀ t) ^ α = _
    unfold dg_fpNext
    congr 1
    ring

/-- `|ln x_t|` stays bounded along the policy path. -/
theorem dg_fpPath_log_bound {α β R θ x₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) (t : ℕ) :
    |Real.log (dg_fpPath α β R θ x₀ t)| ≤
      |Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α) := by
  have h1 : 0 < 1 - α := by linarith
  have hB : 0 ≤ |Real.log (θ * α * β * R)| / (1 - α) := div_nonneg (abs_nonneg _) h1.le
  induction t with
  | zero => change |Real.log x₀| ≤ _; linarith
  | succ t ih =>
      rw [dg_fpPath_log hα hβ hR hθ hx₀, abs_mul, abs_of_pos hα]
      have ht := abs_add_le (Real.log (θ * α * β * R)) (Real.log (dg_fpPath α β R θ x₀ t))
      have key : α * (|Real.log (θ * α * β * R)| + (|Real.log x₀| +
          |Real.log (θ * α * β * R)| / (1 - α))) ≤
          |Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α) := by
        have hB1 : (1 - α) * (|Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α)) =
            (1 - α) * |Real.log x₀| + |Real.log (θ * α * β * R)| := by field_simp
        have hL := mul_le_of_le_one_left (abs_nonneg (Real.log (θ * α * β * R))) hα1.le
        have hx0 := mul_nonneg h1.le (abs_nonneg (Real.log x₀))
        nlinarith
      calc α * |Real.log (θ * α * β * R) + Real.log (dg_fpPath α β R θ x₀ t)|
          ≤ α * (|Real.log (θ * α * β * R)| + (|Real.log x₀| +
              |Real.log (θ * α * β * R)| / (1 - α))) := by
            refine mul_le_mul_of_nonneg_left ?_ hα.le
            linarith
        _ ≤ _ := key

/-- The policy plan attains `V(x₀)` (Miao, p. 757): the utility series of
`c_t = (1 − αβ)Rx_t` converges and `∑ βᵗ ln c_t = V(x₀)`. -/
theorem dg_fp_policy_value {α β R θ x₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hab : α * β < 1) (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) :
    HasSum (fun t => β ^ t * Real.log ((1 - α * β) * R * dg_fpPath α β R θ x₀ t))
      (dg_fpV α β R θ x₀) := by
  set x := dg_fpPath α β R θ x₀
  set B := |Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α)
  have h1 : 0 < 1 - α * β := by linarith
  have hlb := dg_fpPath_log_bound hα hα1 hβ hR hθ hx₀
  have hlc : ∀ t, |Real.log ((1 - α * β) * R * x t)| ≤ |Real.log ((1 - α * β) * R)| + B := by
    intro t
    rw [Real.log_mul (by positivity) (dg_fpPath_pos hα hβ hR hθ hx₀ t).ne']
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hlb t))
  have hsum : Summable fun t => β ^ t * Real.log ((1 - α * β) * R * x t) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right
        (|Real.log ((1 - α * β) * R)| + B)) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hlc t) (pow_nonneg hβ.le t)
  have htel : ∀ T, ∑ t ∈ Finset.range T, β ^ t * Real.log ((1 - α * β) * R * x t) =
      dg_fpV α β R θ x₀ - β ^ T * dg_fpV α β R θ (x T) := by
    intro T
    induction T with
    | zero => simp [x, dg_fpPath]
    | succ T ih =>
        rw [Finset.sum_range_succ, ih]
        have hf := dg_fpPath_feasible hα hβ hab hR hθ hx₀ T
        have hb := dg_fp_bellman_eq hα hβ hab hβ1 hR hθ (dg_fpPath_pos hα hβ hR hθ hx₀ T)
        unfold dg_fpRHS at hb
        rw [← hf.2] at hb
        rw [pow_succ]
        have : β ^ T * dg_fpV α β R θ (x T) = β ^ T * (Real.log ((1 - α * β) * R * x T) +
            β * dg_fpV α β R θ (x (T + 1))) := by rw [hb]
        linarith
  have hV : ∀ T, |dg_fpV α β R θ (x T)| ≤ dg_fpKappa α β * B + |dg_fpNu α β R θ| := by
    intro T
    have hκ : 0 < dg_fpKappa α β := by unfold dg_fpKappa; exact one_div_pos.mpr h1
    unfold dg_fpV
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_pos hκ]
    exact mul_le_mul_of_nonneg_left (hlb T) hκ.le
  have hz : Filter.Tendsto (fun T => β ^ T * dg_fpV α β R θ (x T)) Filter.atTop (nhds 0) := by
    have hβT := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
    refine squeeze_zero_norm (a := fun T => β ^ T * (dg_fpKappa α β * B + |dg_fpNu α β R θ|))
      (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ]
      exact mul_le_mul_of_nonneg_left (hV T) (pow_nonneg hβ.le T)
    · simpa using hβT.mul_const (dg_fpKappa α β * B + |dg_fpNu α β R θ|)
  have hlim : Filter.Tendsto (fun T => ∑ t ∈ Finset.range T,
      β ^ t * Real.log ((1 - α * β) * R * x t)) Filter.atTop (nhds (dg_fpV α β R θ x₀)) := by
    have := (tendsto_const_nhds (x := dg_fpV α β R θ x₀)).sub hz
    rw [sub_zero] at this
    exact this.congr fun T => (htel T).symm
  have := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  rw [← this]
  exact hsum.hasSum

/-- Along the policy path the stock converges to `x̄ = (θαβR)^{α/(1−α)}` (Miao, p. 757, "in the
steady state"), from any `x₀ > 0`; explicitly `ln x_t − ln x̄ = αᵗ (ln x₀ − ln x̄)`. -/
theorem dg_fp_path_tendsto {α β R θ x₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) :
    (∀ t, Real.log (dg_fpPath α β R θ x₀ t) - α / (1 - α) * Real.log (θ * α * β * R) =
      α ^ t * (Real.log x₀ - α / (1 - α) * Real.log (θ * α * β * R))) ∧
    Filter.Tendsto (dg_fpPath α β R θ x₀) Filter.atTop
      (nhds ((θ * α * β * R) ^ (α / (1 - α)))) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hlog : ∀ t, Real.log (dg_fpPath α β R θ x₀ t) - α / (1 - α) * Real.log (θ * α * β * R) =
      α ^ t * (Real.log x₀ - α / (1 - α) * Real.log (θ * α * β * R)) := by
    intro t
    induction t with
    | zero => simp [dg_fpPath]
    | succ t ih =>
        rw [dg_fpPath_log hα hβ hR hθ hx₀, pow_succ]
        have e : α * (Real.log (θ * α * β * R) + Real.log (dg_fpPath α β R θ x₀ t)) -
            α / (1 - α) * Real.log (θ * α * β * R) = α * (Real.log (dg_fpPath α β R θ x₀ t) -
            α / (1 - α) * Real.log (θ * α * β * R)) := by field_simp; ring
        rw [e, ih]
        ring
  refine ⟨hlog, ?_⟩
  have hαt := tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1
  have hL : Filter.Tendsto (fun t => Real.log (dg_fpPath α β R θ x₀ t)) Filter.atTop
      (nhds (α / (1 - α) * Real.log (θ * α * β * R))) := by
    have := (hαt.mul_const (Real.log x₀ - α / (1 - α) * Real.log (θ * α * β * R))).add_const
      (α / (1 - α) * Real.log (θ * α * β * R))
    rw [zero_mul, zero_add] at this
    refine this.congr fun t => ?_
    rw [← hlog t]
    ring
  have hE := (Real.continuous_exp.tendsto _).comp hL
  have hpos : 0 < θ * α * β * R := by positivity
  rw [Real.rpow_def_of_pos hpos, mul_comm]
  refine hE.congr fun t => ?_
  simp only [Function.comp_apply]
  exact Real.exp_log (dg_fpPath_pos hα hβ hR hθ hx₀ t)

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Great Fish War

Miao, §21.3, pp. 755–757, and Exercise 21.3, p. 771: the Levhari–Mirman (1980) model. The fish
stock follows `x_{t+1} = (x_t − c_{1t} − c_{2t})^α` (21.1) and country `i` maximises
`∑ β_iᵗ ln c_{it}`.

Markov perfect equilibrium. With value functions `V_i(x) = κ_i ln x + ν_i` the first-order
conditions (`dg_fish_foc_deriv`, `eq_21_2`) give the linear rules of the text
(`dg_fish_foc_solve`); coefficient matching gives `κ_i = 1/(1 − αβ_i)` (`dg_fish_mpe_kappa`); the
closed form `c_1 = αβ₂(1 − αβ₁)x/(1 − (1 − αβ₁)(1 − αβ₂))` (`dg_fish_mpe_closed_form`), the law
of motion `x_{t+1} = (αβ₁β₂x_t/(β₁ + β₂ − αβ₁β₂))^α` (`eq_21_1_mpe`) and the steady state
(`dg_fish_mpe_steady_state`). The pair of rules is a Markov perfect equilibrium: each rule is a
best response to the other among all feasible catch sequences with convergent utility, with
value `V_i(x₀)` (`dg_fish_mpe`).

Stackelberg. The follower's reaction to a catch `c₁` is `c₂ = (x − c₁)/(1 + αβ₂κ₂)`
(`dg_fish_follower_reaction`); the text prints `c₂ = αβ₂κ₂(x − c₁)/(1 + αβ₂κ₂)`, which violates
(21.2) (`dg_fish_follower_printed_false`). The misprint does not affect the leader: the leader's
rule is `c₁ = x/(1 + αβ₁κ₁)` (`dg_fish_leader_foc`), `κ₁ = 1/(1 − αβ₁)` and `c₁ = (1 − αβ₁)x`
(`dg_fish_leader`). Exercise 21.3: the follower's equilibrium catch is `c₂ = αβ₁(1 − αβ₂)x`
(`ex_21_3`).

The cooperative comparison is not carried out in the text; we add it for symmetric countries:
the planner catches `(1 − αβ)x`, split equally (`dg_fish_cooperative`), less than the MPE total
`2(1 − αβ)x/(2 − αβ)`, and the MPE steady-state stock is lower (`dg_fish_overfishing`).
-/

namespace Miao.DynamicGames

/-- (21.1) (Miao, p. 755): the fish stock evolves as `x_{t+1} = (x_t − c_{1t} − c_{2t})^α`. -/
noncomputable def dg_fishLaw (α x c₁ c₂ : ℝ) : ℝ := (x - c₁ - c₂) ^ α

/-- Under `V(x) = κ ln x + ν`, `V((x − c₁ − c₂)^α) = κα ln(x − c₁ − c₂) + ν`. -/
theorem dg_fish_V_law {α κ ν x c₁ c₂ : ℝ} (h : 0 < x - c₁ - c₂) :
    κ * Real.log (dg_fishLaw α x c₁ c₂) + ν = κ * α * Real.log (x - c₁ - c₂) + ν := by
  unfold dg_fishLaw
  rw [Real.log_rpow h]
  ring

/-- Miao, p. 756: the first-order condition of country 1. The derivative of
`c₁ ↦ ln c₁ + β₁(κ₁α ln(x − c₁ − c₂) + ν₁)` is `1/c₁ − αβ₁κ₁/(x − c₁ − c₂)`. -/
theorem dg_fish_foc_deriv {α β₁ κ₁ ν₁ x c₁ c₂ : ℝ} (hc : 0 < c₁) (hs : 0 < x - c₁ - c₂) :
    HasDerivAt (fun c => Real.log c + β₁ * (κ₁ * α * Real.log (x - c - c₂) + ν₁))
      (1 / c₁ - α * β₁ * κ₁ / (x - c₁ - c₂)) c₁ := by
  have h1 := Real.hasDerivAt_log hc.ne'
  have h2 : HasDerivAt (fun c => x - c - c₂) (-1) c₁ := by
    simpa using ((hasDerivAt_id c₁).const_sub x).sub_const c₂
  have h3 := (h2.log hs.ne').const_mul (κ₁ * α) |>.add_const ν₁ |>.const_mul β₁
  convert h1.add h3 using 1
  field_simp
  ring

/-- (21.2) (Miao, p. 756): the first-order condition of country 2. The derivative of
`c₂ ↦ ln c₂ + β₂(κ₂α ln(x − c₁ − c₂) + ν₂)` is `1/c₂ − αβ₂κ₂/(x − c₁ − c₂)`, so it vanishes iff
`1/c₂ = αβ₂κ₂/(x − c₁ − c₂)`. -/
theorem eq_21_2 {α β₂ κ₂ ν₂ x c₁ c₂ : ℝ} (hc : 0 < c₂) (hs : 0 < x - c₁ - c₂) :
    HasDerivAt (fun c => Real.log c + β₂ * (κ₂ * α * Real.log (x - c₁ - c) + ν₂))
      (1 / c₂ - α * β₂ * κ₂ / (x - c₁ - c₂)) c₂ ∧
    (1 / c₂ - α * β₂ * κ₂ / (x - c₁ - c₂) = 0 ↔ 1 / c₂ = α * β₂ * κ₂ / (x - c₁ - c₂)) := by
  refine ⟨?_, sub_eq_zero⟩
  have h1 := Real.hasDerivAt_log hc.ne'
  have h2 : HasDerivAt (fun c => x - c₁ - c) (-1) c₂ := by
    simpa using (hasDerivAt_id c₂).const_sub (x - c₁)
  have h3 := (h2.log hs.ne').const_mul (κ₂ * α) |>.add_const ν₂ |>.const_mul β₂
  convert h1.add h3 using 1
  field_simp
  ring

/-- Miao, p. 756 ("using the above two equations, we can solve"): for `κ₁, κ₂ > 0`, positive
catches with `x − c₁ − c₂ > 0` satisfy both first-order conditions iff
`c₁ = β₂κ₂x/((1 + αβ₁κ₁)β₂κ₂ + β₁κ₁)` and `c₂ = β₁κ₁x/((1 + αβ₁κ₁)β₂κ₂ + β₁κ₁)`. -/
theorem dg_fish_foc_solve {α β₁ β₂ κ₁ κ₂ x c₁ c₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : 0 < x - c₁ - c₂) :
    (1 / c₁ = α * β₁ * κ₁ / (x - c₁ - c₂) ∧ 1 / c₂ = α * β₂ * κ₂ / (x - c₁ - c₂)) ↔
      (c₁ = β₂ * κ₂ * x / ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁) ∧
        c₂ = β₁ * κ₁ * x / ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)) := by
  have hD : 0 < (1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁ := by positivity
  rw [div_eq_div_iff hc₁.ne' hs.ne', div_eq_div_iff hc₂.ne' hs.ne',
    eq_div_iff hD.ne', eq_div_iff hD.ne']
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : α * (c₁ * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)) = α * (β₂ * κ₂ * x) := by
        nlinarith
      exact mul_left_cancel₀ hα.ne' this
    · have : α * (c₂ * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)) = α * (β₁ * κ₁ * x) := by
        nlinarith
      exact mul_left_cancel₀ hα.ne' this
  · rintro ⟨h1, h2⟩
    constructor
    · have : (1 * (x - c₁ - c₂) - c₁ * (α * β₁ * κ₁)) * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)
          = 0 := by linear_combination (-(1 + α * β₁ * κ₁)) * h1 - h2
      have := (mul_eq_zero.mp this).resolve_right hD.ne'
      linarith
    · have : (1 * (x - c₁ - c₂) - c₂ * (α * β₂ * κ₂)) * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)
          = 0 := by linear_combination (-1 : ℝ) * h1 - (1 + α * β₂ * κ₂) * h2
      have := (mul_eq_zero.mp this).resolve_right hD.ne'
      linarith

/-- Miao, p. 756: substituting linear rules `c₁ = k₁x`, `c₂ = k₂x` into country 1's Bellman
equation `κ₁ ln x + ν₁ = ln(k₁x) + β₁(κ₁α ln((1 − k₁ − k₂)x) + ν₁)` (for all `x > 0`) forces
`κ₁ = 1/(1 − αβ₁)`; likewise for country 2. -/
theorem dg_fish_mpe_kappa {α β₁ κ₁ ν₁ k₁ k₂ : ℝ} (hab : α * β₁ < 1) (hk₁ : 0 < k₁)
    (hs : 0 < 1 - k₁ - k₂)
    (h : ∀ x : ℝ, 0 < x → κ₁ * Real.log x + ν₁ =
      Real.log (k₁ * x) + β₁ * (κ₁ * α * Real.log ((1 - k₁ - k₂) * x) + ν₁)) :
    κ₁ = 1 / (1 - α * β₁) :=
  dg_fp_kappa_forced hab hk₁ hs h

/-- The equilibrium catch rate `k = αβ_t(1 − αβ_o)/(1 − (1 − αβ_o)(1 − αβ_t))` of a country with
discount factor `β_o` whose rival has `β_t` (Miao, p. 757). -/
noncomputable def dg_fishK (α βo βt : ℝ) : ℝ :=
  α * βt * (1 - α * βo) / (1 - (1 - α * βo) * (1 - α * βt))

/-- The MPE saving rate `s = αβ₁β₂/(β₁ + β₂ − αβ₁β₂)`. -/
noncomputable def dg_fishS (α β₁ β₂ : ℝ) : ℝ := α * β₁ * β₂ / (β₁ + β₂ - α * β₁ * β₂)

/-- Miao, p. 757: with `κ_i = 1/(1 − αβ_i)` the solved first-order conditions are the MPE
`c₁ = αβ₂(1 − αβ₁)x/(1 − (1 − αβ₁)(1 − αβ₂))`, `c₂ = αβ₁(1 − αβ₂)x/(1 − (1 − αβ₁)(1 − αβ₂))`. -/
theorem dg_fish_mpe_closed_form {α β₁ β₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (h₁ : α * β₁ < 1) (h₂ : α * β₂ < 1) (x : ℝ) :
    β₂ * (1 / (1 - α * β₂)) * x / ((1 + α * β₁ * (1 / (1 - α * β₁))) * β₂ * (1 / (1 - α * β₂)) +
        β₁ * (1 / (1 - α * β₁))) = dg_fishK α β₁ β₂ * x ∧
    β₁ * (1 / (1 - α * β₁)) * x / ((1 + α * β₁ * (1 / (1 - α * β₁))) * β₂ * (1 / (1 - α * β₂)) +
        β₁ * (1 / (1 - α * β₁))) = dg_fishK α β₂ β₁ * x := by
  have e1 : 1 - α * β₁ ≠ 0 := by linarith
  have e2 : 1 - α * β₂ ≠ 0 := by linarith
  have hpos : 0 < β₁ + β₂ - α * β₁ * β₂ := by
    have := mul_pos hβ₂ (sub_pos.mpr h₁)
    nlinarith
  have hp' : β₁ + β₂ - α * β₁ * β₂ ≠ 0 := hpos.ne'
  have hΔ : 1 - (1 - α * β₁) * (1 - α * β₂) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  have hΔ' : 1 - (1 - α * β₂) * (1 - α * β₁) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  have hD : (1 + α * β₁ * (1 / (1 - α * β₁))) * β₂ * (1 / (1 - α * β₂)) +
      β₁ * (1 / (1 - α * β₁)) = (β₁ + β₂ - α * β₁ * β₂) / ((1 - α * β₁) * (1 - α * β₂)) := by
    field_simp; ring
  unfold dg_fishK
  rw [hD, hΔ, hΔ']
  have hα' : α ≠ 0 := hα.ne'
  obtain ⟨Q, hQ⟩ : ∃ Q, β₁ + β₂ - α * β₁ * β₂ = Q := ⟨_, rfl⟩
  rw [hQ] at hp' ⊢
  have e1' : 1 - β₁ * α ≠ 0 := by rwa [mul_comm]
  have e2' : 1 - β₂ * α ≠ 0 := by rwa [mul_comm]
  constructor <;> field_simp

/-- The catch rates are positive and leave a positive remainder:
`1 − k₁ − k₂ = αβ₁β₂/(β₁ + β₂ − αβ₁β₂)`, and each country's rule is the policy `(1 − αβ_i)` times
what the rival leaves: `(1 − αβ₁)(1 − k₂) = k₁`, `αβ₁(1 − k₂) = s`. -/
theorem dg_fish_rates {α β₁ β₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (h₁ : α * β₁ < 1) (h₂ : α * β₂ < 1) :
    0 < dg_fishK α β₁ β₂ ∧ 0 < dg_fishK α β₂ β₁ ∧
    1 - dg_fishK α β₁ β₂ - dg_fishK α β₂ β₁ = dg_fishS α β₁ β₂ ∧ 0 < dg_fishS α β₁ β₂ ∧
    (1 - α * β₁) * (1 - dg_fishK α β₂ β₁) = dg_fishK α β₁ β₂ ∧
    (1 - α * β₂) * (1 - dg_fishK α β₁ β₂) = dg_fishK α β₂ β₁ ∧
    α * β₁ * (1 - dg_fishK α β₂ β₁) = dg_fishS α β₁ β₂ ∧
    α * β₂ * (1 - dg_fishK α β₁ β₂) = dg_fishS α β₁ β₂ := by
  have e1 : 0 < 1 - α * β₁ := by linarith
  have e2 : 0 < 1 - α * β₂ := by linarith
  have hpos : 0 < β₁ + β₂ - α * β₁ * β₂ := by
    have := mul_pos hβ₂ (sub_pos.mpr h₁)
    nlinarith
  have hp' : β₁ + β₂ - α * β₁ * β₂ ≠ 0 := hpos.ne'
  have hα' : α ≠ 0 := hα.ne'
  have hΔ : 1 - (1 - α * β₁) * (1 - α * β₂) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  have hΔ' : 1 - (1 - α * β₂) * (1 - α * β₁) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  unfold dg_fishK dg_fishS
  rw [hΔ, hΔ']
  obtain ⟨Q, hQ⟩ : ∃ Q, β₁ + β₂ - α * β₁ * β₂ = Q := ⟨_, rfl⟩
  rw [hQ] at hp' hpos ⊢
  refine ⟨by positivity, by positivity, ?_, by positivity, ?_, ?_, ?_, ?_⟩ <;>
    field_simp <;> rw [← hQ] <;> ring

/-- (21.1) under the MPE (Miao, p. 757): `x_{t+1} = (αβ₁β₂x_t/(β₁ + β₂ − αβ₁β₂))^α`. -/
theorem eq_21_1_mpe {α β₁ β₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (h₁ : α * β₁ < 1) (h₂ : α * β₂ < 1) (x : ℝ) :
    dg_fishLaw α x (dg_fishK α β₁ β₂ * x) (dg_fishK α β₂ β₁ * x) =
      (α * β₁ * β₂ * x / (β₁ + β₂ - α * β₁ * β₂)) ^ α := by
  obtain ⟨-, -, h3, -⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
  unfold dg_fishLaw
  congr 1
  have : x - dg_fishK α β₁ β₂ * x - dg_fishK α β₂ β₁ * x =
      (1 - dg_fishK α β₁ β₂ - dg_fishK α β₂ β₁) * x := by ring
  rw [this, h3]
  unfold dg_fishS
  ring

/-- The Great Fish War MPE (Miao, pp. 756–757). Let `k₁ = dg_fishK α β₁ β₂`,
`k₂ = dg_fishK α β₂ β₁` and `V_i(x) = κ_i ln x + ν_i`, `κ_i = 1/(1 − αβ_i)`. Against `c₂ = k₂x`,
every feasible catch sequence of country 1 (`c_t > 0`, `x_t − c_t − k₂x_t > 0`, (21.1)) with
convergent discounted utility yields at most `V₁(x₀)`, and `c₁ = k₁x` attains `V₁(x₀)` along
`x_{t+1} = (sx_t)^α`; symmetrically for country 2. -/
theorem dg_fish_mpe {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (hβ₁1 : β₁ < 1) (hβ₂1 : β₂ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    let k₁ := dg_fishK α β₁ β₂
    let k₂ := dg_fishK α β₂ β₁
    let V₁ := dg_fpV α β₁ (1 - k₂) 1
    let V₂ := dg_fpV α β₂ (1 - k₁) 1
    let xs := dg_fpPath α β₁ (1 - k₂) 1 x₀
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ 0 < x t - c t - k₂ * x t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) (c t) (k₂ * x t)) →
      Summable (fun t => β₁ ^ t * Real.log (c t)) → ∑' t, β₁ ^ t * Real.log (c t) ≤ V₁ x₀) ∧
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ 0 < x t - k₁ * x t - c t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) (k₁ * x t) (c t)) →
      Summable (fun t => β₂ ^ t * Real.log (c t)) → ∑' t, β₂ ^ t * Real.log (c t) ≤ V₂ x₀) ∧
    (∀ t, xs (t + 1) = dg_fishLaw α (xs t) (k₁ * xs t) (k₂ * xs t)) ∧
    HasSum (fun t => β₁ ^ t * Real.log (k₁ * xs t)) (V₁ x₀) ∧
    HasSum (fun t => β₂ ^ t * Real.log (k₂ * xs t)) (V₂ x₀) ∧
    dg_fpKappa α β₁ = 1 / (1 - α * β₁) ∧ dg_fpKappa α β₂ = 1 / (1 - α * β₂) := by
  intro k₁ k₂ V₁ V₂ xs
  have h₁ : α * β₁ < 1 := by nlinarith
  have h₂ : α * β₂ < 1 := by nlinarith
  obtain ⟨hk₁, hk₂, h3, hs, h5, h6, h7, h8⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
  have hR₂ : 0 < 1 - k₂ := by simp only [k₂]; linarith
  have hR₁ : 0 < 1 - k₁ := by simp only [k₁]; linarith
  -- the two best-response problems have the same stock path
  have hpath : ∀ t, dg_fpPath α β₂ (1 - k₁) 1 x₀ t = xs t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        change (1 * α * β₂ * (1 - k₁) * dg_fpPath α β₂ (1 - k₁) 1 x₀ t) ^ α =
          (1 * α * β₁ * (1 - k₂) * xs t) ^ α
        rw [ih]
        congr 1
        have e : 1 * α * β₂ * (1 - k₁) = 1 * α * β₁ * (1 - k₂) := by
          simp only [k₁, k₂]; linarith
        rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro x c hx0 hfeas hlaw hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₁ h₁ hβ₁1 hR₂ one_pos x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · linarith [(hfeas t).2]
    · rw [hlaw t]; unfold dg_fishLaw dg_fpNext; congr 1; ring
  · intro x c hx0 hfeas hlaw hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₂ h₂ hβ₂1 hR₁ one_pos x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · linarith [(hfeas t).2]
    · rw [hlaw t]; unfold dg_fishLaw dg_fpNext; congr 1; ring
  · intro t
    change (1 * α * β₁ * (1 - k₂) * xs t) ^ α = _
    unfold dg_fishLaw
    congr 1
    have e : xs t - k₁ * xs t - k₂ * xs t = (1 - k₁ - k₂) * xs t := by ring
    rw [e, h3, ← h7]
    ring
  · have := dg_fp_policy_value hα hα1 hβ₁ h₁ hβ₁1 hR₂ one_pos hx₀
    convert this using 3 with t
    simp only [k₁, k₂, xs]
    rw [h5]
  · have := dg_fp_policy_value hα hα1 hβ₂ h₂ hβ₂1 hR₁ one_pos hx₀
    convert this using 3 with t
    rw [hpath]
    simp only [k₁, k₂, xs]
    rw [h6]

/-- Miao, p. 757 ("in the steady state"): under the MPE the stock converges, from any `x₀ > 0`,
to `x̄ = (αβ₁β₂/(β₁ + β₂ − αβ₁β₂))^{α/(1−α)}`. -/
theorem dg_fish_mpe_steady_state {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₁1 : β₁ < 1) (hβ₂1 : β₂ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Filter.Tendsto (dg_fpPath α β₁ (1 - dg_fishK α β₂ β₁) 1 x₀) Filter.atTop
      (nhds ((α * β₁ * β₂ / (β₁ + β₂ - α * β₁ * β₂)) ^ (α / (1 - α)))) := by
  have h₁ : α * β₁ < 1 := by nlinarith
  have h₂ : α * β₂ < 1 := by nlinarith
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
  have hR : 0 < 1 - dg_fishK α β₂ β₁ := by
    obtain ⟨hk₁, hk₂, h3, hs, -⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
    linarith
  have := (dg_fp_path_tendsto hα hα1 hβ₁ hR one_pos hx₀).2
  have e : 1 * α * β₁ * (1 - dg_fishK α β₂ β₁) = α * β₁ * β₂ / (β₁ + β₂ - α * β₁ * β₂) := by
    have h7' := h7
    unfold dg_fishS at h7'
    rw [← h7']
    ring
  rwa [e] at this

/-- Stackelberg, the follower (Miao, p. 757, from (21.2)): with `V₂(x) = κ₂ ln x + ν₂`, `κ₂ > 0`,
the follower's best reply to a catch `c₁ < x` is `c₂ = (x − c₁)/(1 + αβ₂κ₂)`, the unique
maximiser of `ln c₂ + β₂(κ₂α ln(x − c₁ − c₂) + ν₂)` on `0 < c₂ < x − c₁`. -/
theorem dg_fish_follower_reaction {α β₂ κ₂ ν₂ x c₁ c₂ : ℝ} (hα : 0 < α) (hβ₂ : 0 < β₂)
    (hκ₂ : 0 < κ₂) (hc₁ : c₁ < x) (hc₂ : 0 < c₂) (hc₂' : c₂ < x - c₁) :
    Real.log c₂ + β₂ * (κ₂ * α * Real.log (x - c₁ - c₂) + ν₂) ≤
      Real.log ((x - c₁) / (1 + α * β₂ * κ₂)) +
        β₂ * (κ₂ * α * Real.log (x - c₁ - (x - c₁) / (1 + α * β₂ * κ₂)) + ν₂) ∧
    (c₂ ≠ (x - c₁) / (1 + α * β₂ * κ₂) →
      Real.log c₂ + β₂ * (κ₂ * α * Real.log (x - c₁ - c₂) + ν₂) <
      Real.log ((x - c₁) / (1 + α * β₂ * κ₂)) +
        β₂ * (κ₂ * α * Real.log (x - c₁ - (x - c₁) / (1 + α * β₂ * κ₂)) + ν₂)) := by
  have hK : 0 < α * β₂ * κ₂ := by positivity
  have hm := dg_log_max (sub_pos.mpr hc₁) hK hc₂ hc₂'
  constructor
  · nlinarith [hm.1]
  · intro hne
    nlinarith [hm.2 hne]

/-- Miao, p. 757: the printed follower rule `c₂ = αβ₂κ₂(x − c₁)/(1 + αβ₂κ₂)` is wrong. For
`α = β₂ = 1/2`, `κ₂ = 1/(1 − αβ₂) = 4/3`, `x = 2`, `c₁ = 1` it gives `c₂ = 1/4`, which violates
(21.2) (`1/c₂ = 4 ≠ αβ₂κ₂/(x − c₁ − c₂) = 4/9`) and does strictly worse than the correct
reply `(x − c₁)/(1 + αβ₂κ₂) = 3/4`. -/
theorem dg_fish_follower_printed_false :
    let α : ℝ := 1 / 2
    let β₂ : ℝ := 1 / 2
    let κ₂ : ℝ := 4 / 3
    let x : ℝ := 2
    let c₁ : ℝ := 1
    let c₂ : ℝ := α * β₂ * κ₂ / (1 + α * β₂ * κ₂) * (x - c₁)
    κ₂ = 1 / (1 - α * β₂) ∧ c₂ = 1 / 4 ∧ 1 / c₂ ≠ α * β₂ * κ₂ / (x - c₁ - c₂) ∧
    (x - c₁) / (1 + α * β₂ * κ₂) = 3 / 4 ∧
    Real.log c₂ + β₂ * (κ₂ * α * Real.log (x - c₁ - c₂)) <
      Real.log ((x - c₁) / (1 + α * β₂ * κ₂)) +
        β₂ * (κ₂ * α * Real.log (x - c₁ - (x - c₁) / (1 + α * β₂ * κ₂))) := by
  intro α β₂ κ₂ x c₁ c₂
  have hc₂ : c₂ = 1 / 4 := by simp only [c₂, α, β₂, κ₂, x, c₁]; norm_num
  have hstar : (x - c₁) / (1 + α * β₂ * κ₂) = 3 / 4 := by
    simp only [α, β₂, κ₂, x, c₁]; norm_num
  refine ⟨by simp only [α, β₂, κ₂]; norm_num, hc₂, ?_, hstar, ?_⟩
  · rw [hc₂]; simp only [α, β₂, κ₂, x, c₁]; norm_num
  · have := (dg_fish_follower_reaction (α := α) (β₂ := β₂) (κ₂ := κ₂) (ν₂ := 0) (x := x)
      (c₁ := c₁) (c₂ := c₂) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hc₂]; norm_num) (by rw [hc₂]; norm_num)).2 (by rw [hc₂, hstar]; norm_num)
    simpa using this

/-- Stackelberg, the leader (Miao, p. 757): if the follower replies `c₂ = (x − c₁)/(1 + K₂)`,
`K₂ > 0`, then `x − c₁ − c₂ = K₂(x − c₁)/(1 + K₂)` and the leader's objective
`ln c₁ + β₁(κ₁α ln(x − c₁ − c₂) + ν₁)` has the unique maximiser `c₁ = x/(1 + αβ₁κ₁)`, the
first-order condition `1/c₁ = αβ₁κ₁/(x − c₁)`. The same holds for the printed follower rule,
which is also proportional to `x − c₁`. -/
theorem dg_fish_leader_foc {α β₁ κ₁ ν₁ K₂ x c₁ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁)
    (hκ₁ : 0 < κ₁) (hK₂ : 0 < K₂) (hc₁ : 0 < c₁) (hcx : c₁ < x) :
    (Real.log c₁ + β₁ * (κ₁ * α * Real.log (x - c₁ - (x - c₁) / (1 + K₂)) + ν₁) ≤
      Real.log (x / (1 + α * β₁ * κ₁)) + β₁ * (κ₁ * α * Real.log (x - x / (1 + α * β₁ * κ₁) -
        (x - x / (1 + α * β₁ * κ₁)) / (1 + K₂)) + ν₁)) ∧
    (c₁ ≠ x / (1 + α * β₁ * κ₁) →
      Real.log c₁ + β₁ * (κ₁ * α * Real.log (x - c₁ - (x - c₁) / (1 + K₂)) + ν₁) <
      Real.log (x / (1 + α * β₁ * κ₁)) + β₁ * (κ₁ * α * Real.log (x - x / (1 + α * β₁ * κ₁) -
        (x - x / (1 + α * β₁ * κ₁)) / (1 + K₂)) + ν₁)) := by
  have hx : 0 < x := hc₁.trans hcx
  have hK : 0 < α * β₁ * κ₁ := by positivity
  have hθ : 0 < K₂ / (1 + K₂) := by positivity
  have hrem : ∀ c, c < x → x - c - (x - c) / (1 + K₂) = K₂ / (1 + K₂) * (x - c) := by
    intro c _; field_simp; ring
  have hlog : ∀ c, c < x → Real.log (x - c - (x - c) / (1 + K₂)) =
      Real.log (K₂ / (1 + K₂)) + Real.log (x - c) := by
    intro c hc
    rw [hrem c hc, Real.log_mul hθ.ne' (by linarith)]
  have hstar : x / (1 + α * β₁ * κ₁) < x := div_lt_self hx (by linarith)
  have hm := dg_log_max hx hK hc₁ hcx
  rw [hlog c₁ hcx, hlog _ hstar]
  constructor
  · nlinarith [hm.1]
  · intro hne
    nlinarith [hm.2 hne]

/-- Stackelberg, the leader (Miao, p. 757): with the follower's equilibrium reply
`c₂ = (1 − αβ₂)(x − c₁)` (`K₂ = αβ₂/(1 − αβ₂)`), the leader's problem is the fishing problem with
`R = 1`, `θ = αβ₂`; its value is `κ₁ ln x + ν₁` with `κ₁ = 1/(1 − αβ₁)` and its rule is
`c₁ = (1 − αβ₁)x = x/(1 + αβ₁κ₁)`, optimal among all feasible sequences. -/
theorem dg_fish_leader {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₁1 : β₁ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∀ x : ℝ, 0 < x → x / (1 + α * β₁ * dg_fpKappa α β₁) = (1 - α * β₁) * x) ∧
    (∀ x c₁ : ℝ, c₁ < x → dg_fishLaw α x c₁ ((1 - α * β₂) * (x - c₁)) =
      dg_fpNext α 1 (α * β₂) x c₁) ∧
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ c t < x t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) (c t) ((1 - α * β₂) * (x t - c t))) →
      Summable (fun t => β₁ ^ t * Real.log (c t)) →
      ∑' t, β₁ ^ t * Real.log (c t) ≤ dg_fpV α β₁ 1 (α * β₂) x₀) ∧
    HasSum (fun t => β₁ ^ t * Real.log ((1 - α * β₁) * dg_fpPath α β₁ 1 (α * β₂) x₀ t))
      (dg_fpV α β₁ 1 (α * β₂) x₀) := by
  have h₁ : α * β₁ < 1 := by nlinarith
  have hθ : 0 < α * β₂ := by positivity
  have hlaw : ∀ x c₁ : ℝ, c₁ < x → dg_fishLaw α x c₁ ((1 - α * β₂) * (x - c₁)) =
      dg_fpNext α 1 (α * β₂) x c₁ := by
    intro x c₁ _
    unfold dg_fishLaw dg_fpNext
    congr 1
    ring
  refine ⟨?_, hlaw, ?_, ?_⟩
  · intro x _
    have : 1 + α * β₁ * dg_fpKappa α β₁ = 1 / (1 - α * β₁) := by
      rw [dg_fpKappa_eq h₁]; rfl
    rw [this]
    have : 1 - α * β₁ ≠ 0 := by linarith
    field_simp
  · intro x c hx0 hfeas hl hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₁ h₁ hβ₁1 one_pos hθ x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · rw [one_mul]; exact (hfeas t).2
    · rw [hl t, hlaw _ _ (hfeas t).2]
  · have := dg_fp_policy_value hα hα1 hβ₁ h₁ hβ₁1 one_pos hθ hx₀
    simpa using this

/-- **Exercise 21.3** (Miao, p. 771): country 2's equilibrium catch in the linear Stackelberg
equilibrium. Given the leader's rule `c₁ = (1 − αβ₁)x`, the follower's problem is the fishing
problem with `R = αβ₁`, `θ = 1`: its value is `κ₂ ln x + ν₂` with `κ₂ = 1/(1 − αβ₂)`, and its
catch `c₂ = αβ₁(1 − αβ₂)x` is optimal among all feasible sequences. This catch is the follower's
reaction `(x − c₁)/(1 + αβ₂κ₂)` at `c₁ = (1 − αβ₁)x`, and the stock then evolves as
`x_{t+1} = (α²β₁β₂x_t)^α`. -/
theorem ex_21_3 {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∀ x : ℝ, (x - (1 - α * β₁) * x) / (1 + α * β₂ * dg_fpKappa α β₂) =
      (1 - α * β₂) * (α * β₁) * x) ∧
    (∀ x : ℝ, dg_fishLaw α x ((1 - α * β₁) * x) ((1 - α * β₂) * (α * β₁) * x) =
      (α * α * β₁ * β₂ * x) ^ α) ∧
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ 0 < x t - (1 - α * β₁) * x t - c t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) ((1 - α * β₁) * x t) (c t)) →
      Summable (fun t => β₂ ^ t * Real.log (c t)) →
      ∑' t, β₂ ^ t * Real.log (c t) ≤ dg_fpV α β₂ (α * β₁) 1 x₀) ∧
    HasSum (fun t => β₂ ^ t * Real.log ((1 - α * β₂) * (α * β₁) *
      dg_fpPath α β₂ (α * β₁) 1 x₀ t)) (dg_fpV α β₂ (α * β₁) 1 x₀) ∧
    dg_fpKappa α β₂ = 1 / (1 - α * β₂) := by
  have h₂ : α * β₂ < 1 := by nlinarith
  have hR : 0 < α * β₁ := by positivity
  refine ⟨?_, ?_, ?_, dg_fp_policy_value hα hα1 hβ₂ h₂ hβ₂1 hR one_pos hx₀, rfl⟩
  · intro x
    have : 1 + α * β₂ * dg_fpKappa α β₂ = 1 / (1 - α * β₂) := by
      rw [dg_fpKappa_eq h₂]; rfl
    rw [this]
    have : 1 - α * β₂ ≠ 0 := by linarith
    field_simp
    ring
  · intro x
    unfold dg_fishLaw
    congr 1
    ring
  · intro x c hx0 hfeas hl hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₂ h₂ hβ₂1 hR one_pos x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · linarith [(hfeas t).2]
    · rw [hl t]; unfold dg_fishLaw dg_fpNext; congr 1; ring

/-- `ln c₁ + ln c₂ ≤ 2 ln((c₁ + c₂)/2)` for positive catches, with equality iff `c₁ = c₂`. -/
theorem dg_log_add_le {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    Real.log c₁ + Real.log c₂ ≤ 2 * Real.log ((c₁ + c₂) / 2) := by
  rw [← Real.log_mul h₁.ne' h₂.ne', ← Real.log_rpow (by positivity)]
  refine Real.log_le_log (mul_pos h₁ h₂) ?_
  rw [show ((c₁ + c₂) / 2) ^ (2 : ℝ) = ((c₁ + c₂) / 2) ^ (2 : ℕ) by norm_cast]
  nlinarith [sq_nonneg (c₁ - c₂)]

/-- The cooperative solution for symmetric countries (`β₁ = β₂ = β`; not carried out in the text).
With `W(x) = 2V(x) − 2 ln 2/(1 − β)`, `V` the value of the fishing problem with `R = θ = 1`,
every feasible pair satisfies `ln c₁ + ln c₂ + βW((x − c₁ − c₂)^α) ≤ W(x)`, with equality at
`c₁ = c₂ = (1 − αβ)x/2`: the planner catches `(1 − αβ)x` in total. -/
theorem dg_fish_cooperative {α β x c₁ c₂ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hx : 0 < x) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : 0 < x - c₁ - c₂) :
    let W : ℝ → ℝ := fun y => 2 * dg_fpV α β 1 1 y - 2 * Real.log 2 / (1 - β)
    Real.log c₁ + Real.log c₂ + β * W (dg_fishLaw α x c₁ c₂) ≤ W x ∧
    Real.log ((1 - α * β) * x / 2) + Real.log ((1 - α * β) * x / 2) +
      β * W (dg_fishLaw α x ((1 - α * β) * x / 2) ((1 - α * β) * x / 2)) = W x := by
  intro W
  have h1 : 0 < 1 - α * β := by linarith
  have hb : 1 - β ≠ 0 := by linarith
  have hlaw : ∀ a b : ℝ, dg_fishLaw α x a b = dg_fpNext α 1 1 x (a + b) := by
    intro a b; unfold dg_fishLaw dg_fpNext; congr 1; ring
  have hC : 0 < c₁ + c₂ := by linarith
  have hb1 := dg_fp_bellman hα hβ hab hβ1 one_pos one_pos hx hC (by linarith)
  have hb2 := dg_fp_bellman_eq hα hβ hab hβ1 one_pos one_pos hx
  have hlog2 := dg_log_add_le hc₁ hc₂
  have hl2 : Real.log ((c₁ + c₂) / 2) = Real.log (c₁ + c₂) - Real.log 2 :=
    Real.log_div hC.ne' two_ne_zero
  unfold dg_fpRHS at hb1 hb2
  simp only [W]
  rw [hlaw, hlaw]
  have e : (1 - α * β) * x / 2 + (1 - α * β) * x / 2 = (1 - α * β) * 1 * x := by ring
  rw [e]
  have hl3 : Real.log ((1 - α * β) * x / 2) = Real.log ((1 - α * β) * 1 * x) - Real.log 2 := by
    rw [mul_one]; exact Real.log_div (by positivity) two_ne_zero
  have hk : 2 * Real.log 2 / (1 - β) = 2 * Real.log 2 + β * (2 * Real.log 2 / (1 - β)) := by
    field_simp; ring
  constructor
  · nlinarith
  · rw [hl3]
    nlinarith

/-- Overfishing (supplementary to Miao, §21.3): with `β₁ = β₂ = β`, the MPE total catch
`(k₁ + k₂)x = 2(1 − αβ)x/(2 − αβ)` exceeds the cooperative catch `(1 − αβ)x`, and the MPE
saving rate `αβ/(2 − αβ)` is below the cooperative `αβ`, so the steady-state stock is lower. -/
theorem dg_fish_overfishing {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    dg_fishK α β β + dg_fishK α β β = 2 * (1 - α * β) / (2 - α * β) ∧
    1 - α * β < dg_fishK α β β + dg_fishK α β β ∧
    dg_fishS α β β = α * β / (2 - α * β) ∧ dg_fishS α β β < α * β ∧
    dg_fishS α β β ^ (α / (1 - α)) < (α * β) ^ (α / (1 - α)) := by
  have hab : α * β < 1 := by nlinarith
  have hab0 : 0 < α * β := by positivity
  have h2 : 0 < 2 - α * β := by linarith
  have hK : dg_fishK α β β = (1 - α * β) / (2 - α * β) := by
    unfold dg_fishK
    have : 1 - (1 - α * β) * (1 - α * β) = α * β * (2 - α * β) := by ring
    rw [this]
    field_simp
  have hS : dg_fishS α β β = α * β / (2 - α * β) := by
    unfold dg_fishS
    have : β + β - α * β * β = β * (2 - α * β) := by ring
    rw [this]
    field_simp
  have hlt : α * β / (2 - α * β) < α * β := by
    rw [div_lt_iff₀ h2]; nlinarith
  refine ⟨by rw [hK]; ring, ?_, hS, by rw [hS]; exact hlt, ?_⟩
  · rw [hK, ← two_mul, mul_div_assoc', lt_div_iff₀ h2]
    nlinarith
  · rw [hS]
    exact Real.rpow_lt_rpow (by positivity) hlt (div_pos hα (by linarith))

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Credible government policies: the one-period economy

Miao, §21.4.1, pp. 758–761 (after Stokey 1991 and Ljungqvist–Sargent 2004, Ch. 22).

* `cg_CE u`: competitive equilibria `(x, y)` with `u(x, x, y) = max_a u(a, x, y)`; `cg_IsRamsey`
  (a Ramsey plan maximises `r(x, y) = u(x, x, y)` over competitive equilibria) and `cg_IsNash`
  (competitive, with `y` a best response to `x`). The repeated-economy modules take the set `C`
  of competitive equilibria as a primitive, so that the examples can give it by a table.
* `cg_vN_le_vR`: `v^N ≤ v^R` (p. 759).
* Example 21.4.1 (Barro–Gordon): the household forecast, the Ramsey outcome `π = 0`, the unique
  Nash outcome `π = aλ`, `y = y_n` in both, and the time inconsistency of the Ramsey outcome.
* Example 21.4.2 (Stokey's discrete monetary policy): `(x_L, y_L)` is the Ramsey outcome,
  `(x_M, y_M)` the unique Nash outcome, and the Ramsey outcome is not time consistent. The
  actions are `Fin 3` with `0, 1, 2 = H, M, L`; `cg_r422 x y = r(x, y)`.
* Exercise 21.6 (a)–(b): `Fin 2` with `0, 1 = L, H`; the Ramsey plan is `(x_H, y_H)` and there is
  no pure-strategy Nash equilibrium. Parts (c)–(f) are in `CGExamples`.
-/

namespace Miao.DynamicGames

variable {X Y : Type*}

/-- Competitive equilibria of the one-period economy (Miao, p. 758): given `(x, y)`, the
representative household's choice `a = x` solves `max_a u(a, x, y)`. -/
def cg_CE (u : X → X → Y → ℝ) : Set (X × Y) := {q | ∀ a, u a q.1 q.2 ≤ u q.1 q.1 q.2}

/-- Miao, p. 758: `(x, y) ∈ C` iff `u(x, x, y) = max_{a ∈ X} u(a, x, y)`. -/
theorem cg_mem_CE (u : X → X → Y → ℝ) (x : X) (y : Y) :
    (x, y) ∈ cg_CE u ↔ ∀ a, u a x y ≤ u x x y := Iff.rfl

/-- A Ramsey plan (Miao, p. 759): `(x^R, y^R)` maximises `r` over competitive equilibria. -/
def cg_IsRamsey (C : Set (X × Y)) (r : X → Y → ℝ) (x : X) (y : Y) : Prop :=
  (x, y) ∈ C ∧ ∀ q ∈ C, r q.1 q.2 ≤ r x y

/-- A Nash equilibrium (Miao, p. 759): `(x^N, y^N) ∈ C` and `y^N` maximises `r(x^N, ·)`. -/
def cg_IsNash (C : Set (X × Y)) (r : X → Y → ℝ) (x : X) (y : Y) : Prop :=
  (x, y) ∈ C ∧ ∀ y', r x y' ≤ r x y

/-- Miao, p. 759: `v^N ≤ max_{(x, y) ∈ C, y = H(x)} r(x, y) ≤ max_{(x, y) ∈ C} r(x, y) = v^R`. -/
theorem cg_vN_le_vR {C : Set (X × Y)} {r : X → Y → ℝ} {xN xR : X} {yN yR : Y}
    (hN : cg_IsNash C r xN yN) (hR : cg_IsRamsey C r xR yR) : r xN yN ≤ r xR yR :=
  hR.2 (xN, yN) hN.1

/-- The government's objective in Example 21.4.1, `λ(y − y_n) − π²/2` with the Phillips curve
`y = y_n + a(π − π^e)`, as a function of the forecast `π^e` and the inflation rate `π`. -/
noncomputable def cg_bgGov (lam a yn infe infl : ℝ) : ℝ :=
  lam * ((yn + a * (infl - infe)) - yn) - infl ^ 2 / 2

/-- The household's payoff `−(π − ξ)²` from the forecast `ξ` in Example 21.4.1. -/
noncomputable def cg_bgHH (infl ξ : ℝ) : ℝ := -(infl - ξ) ^ 2

/-- The competitive equilibria `ξ = π^e = π` of Example 21.4.1. -/
def cg_bgC : Set (ℝ × ℝ) := {q | q.1 = q.2}

/-- **Example 21.4.1** (Barro–Gordon, Miao, pp. 759–760), the household: `ξ = π` uniquely
maximises `−(π − ξ)²`, so the competitive equilibria are `π^e = π`. -/
theorem example_21_4_1_household (infl ξ : ℝ) :
    cg_bgHH infl ξ ≤ cg_bgHH infl infl ∧ (cg_bgHH infl ξ = cg_bgHH infl infl → ξ = infl) := by
  unfold cg_bgHH
  refine ⟨by nlinarith [sq_nonneg (infl - ξ)], fun h => ?_⟩
  have : (infl - ξ) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

/-- **Example 21.4.1** (Miao, p. 760), the Ramsey plan: with `π^e = π` the government's best
choice is `π = π^e = 0`, with `y = y_n`. -/
theorem example_21_4_1_ramsey (lam a yn : ℝ) :
    cg_IsRamsey cg_bgC (cg_bgGov lam a yn) 0 0 ∧
      (∀ x y, cg_IsRamsey cg_bgC (cg_bgGov lam a yn) x y → x = 0 ∧ y = 0) ∧
      yn + a * (0 - 0) = yn := by
  refine ⟨⟨rfl, ?_⟩, fun x y h => ?_, by ring⟩
  · rintro ⟨x, y⟩ (hq : x = y)
    subst hq
    simp only [cg_bgGov]
    nlinarith [sq_nonneg x]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    have := hmax (0, 0) rfl
    simp only [cg_bgGov] at this
    have h2 : x ^ 2 = 0 := by nlinarith [sq_nonneg x]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    exact ⟨this, this⟩

/-- **Example 21.4.1** (Miao, p. 760), the Nash equilibrium: taking `π^e` as given the
government sets `π = aλ`, so the unique Nash outcome is `π^e = π = aλ`, with `y = y_n`. -/
theorem example_21_4_1_nash {lam a : ℝ} (yn : ℝ) :
    (∀ infe infl, cg_bgGov lam a yn infe infl ≤ cg_bgGov lam a yn infe (a * lam)) ∧
      cg_IsNash cg_bgC (cg_bgGov lam a yn) (a * lam) (a * lam) ∧
      (∀ x y, cg_IsNash cg_bgC (cg_bgGov lam a yn) x y → x = a * lam ∧ y = a * lam) ∧
      yn + a * (a * lam - a * lam) = yn := by
  have hbr : ∀ infe infl, cg_bgGov lam a yn infe infl ≤ cg_bgGov lam a yn infe (a * lam) := by
    intro infe infl
    simp only [cg_bgGov]
    nlinarith [sq_nonneg (infl - a * lam)]
  refine ⟨hbr, ⟨rfl, hbr _⟩, fun x y h => ?_, by ring⟩
  obtain ⟨hxy, hmax⟩ := h
  have hxy' : x = y := hxy
  subst hxy'
  have := hmax (a * lam)
  simp only [cg_bgGov] at this
  have h2 : (x - a * lam) ^ 2 = 0 := by nlinarith [sq_nonneg (x - a * lam)]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Example 21.4.1** (Miao, p. 760): the Ramsey outcome is not time consistent. After the
forecast `π^e = 0` the government gains by setting `π = aλ > 0`; and `v^N < v^R`. -/
theorem example_21_4_1_time_inconsistent {lam a : ℝ} (hl : 0 < lam) (ha : 0 < a) (yn : ℝ) :
    0 < a * lam ∧ cg_bgGov lam a yn 0 0 < cg_bgGov lam a yn 0 (a * lam) ∧
      cg_bgGov lam a yn (a * lam) (a * lam) < cg_bgGov lam a yn 0 0 := by
  have h := mul_pos ha hl
  refine ⟨h, ?_, ?_⟩ <;> simp only [cg_bgGov] <;> nlinarith

/-- The government's payoffs `r(x_i, y_j)` of Example 21.4.2 (Miao, p. 760), with
`0, 1, 2 = H, M, L`: rows are `x`, columns `y`. -/
noncomputable def cg_r422 (x y : Fin 3) : ℝ :=
  if x = 0 then (if y = 0 then 0 else if y = 1 then 7 else -1)
  else if x = 1 then (if y = 1 then 8 else -1)
  else (if y = 0 then 1 else if y = 1 then 30 else 97 / 10)

/-- The competitive equilibria `(x_H, y_H), (x_M, y_M), (x_L, y_L)` of Example 21.4.2. -/
def cg_C422 : Set (Fin 3 × Fin 3) := {q | q.1 = q.2}

/-- **Example 21.4.2** (Stokey 1991; Miao, pp. 760–761). `(x_L, y_L)` is the (unique) Ramsey
outcome, `(x_M, y_M)` the unique Nash outcome, and the Ramsey outcome is not time consistent:
given `x_L` the government gains by deviating to `y_M` (`30 > 9.7`). -/
theorem example_21_4_2 :
    cg_IsRamsey cg_C422 cg_r422 2 2 ∧
      (∀ x y, cg_IsRamsey cg_C422 cg_r422 x y → x = 2 ∧ y = 2) ∧
      cg_IsNash cg_C422 cg_r422 1 1 ∧
      (∀ x y, cg_IsNash cg_C422 cg_r422 x y → x = 1 ∧ y = 1) ∧
      cg_r422 2 2 < cg_r422 2 1 := by
  refine ⟨⟨rfl, ?_⟩, fun x y h => ?_, ⟨rfl, fun y' => ?_⟩, fun x y h => ?_, ?_⟩
  · rintro ⟨x, y⟩ (hq : x = y)
    subst hq
    fin_cases x <;> norm_num [cg_r422]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    have := hmax (2, 2) rfl
    fin_cases x
    · norm_num [cg_r422] at this
    · norm_num [cg_r422] at this
    · exact ⟨rfl, rfl⟩
  · fin_cases y' <;> norm_num [cg_r422]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    fin_cases x
    · have := hmax 1; norm_num [cg_r422] at this
    · exact ⟨rfl, rfl⟩
    · have := hmax 1; norm_num [cg_r422] at this
  · norm_num [cg_r422]

/-- The government's payoffs `u(x_i, x_i, y_j)` of Exercise 21.6 (Miao, p. 771), with
`0, 1 = L, H`: rows are `x`, columns `y`. -/
noncomputable def cg_r216 (x y : Fin 2) : ℝ :=
  if x = 0 then (if y = 0 then 0 else 1) else (if y = 0 then 15 else 10)

/-- The competitive equilibria `(x_L, y_L), (x_H, y_H)` of Exercise 21.6. -/
def cg_C216 : Set (Fin 2 × Fin 2) := {q | q.1 = q.2}

/-- **Exercise 21.6 (a)** (Miao, p. 771): the Ramsey plan is `(x_H, y_H)`, with value `10`. -/
theorem ex_21_6_a :
    cg_IsRamsey cg_C216 cg_r216 1 1 ∧
      (∀ x y, cg_IsRamsey cg_C216 cg_r216 x y → x = 1 ∧ y = 1) ∧ cg_r216 1 1 = 10 := by
  refine ⟨⟨rfl, ?_⟩, fun x y h => ?_, by norm_num [cg_r216]⟩
  · rintro ⟨x, y⟩ (hq : x = y)
    subst hq
    fin_cases x <;> norm_num [cg_r216]
  · obtain ⟨hxy, hmax⟩ := h
    have hxy' : x = y := hxy
    subst hxy'
    have := hmax (1, 1) rfl
    fin_cases x
    · norm_num [cg_r216] at this
    · exact ⟨rfl, rfl⟩

/-- **Exercise 21.6 (b)** (Miao, p. 771): the one-period economy has no pure-strategy Nash
equilibrium. -/
theorem ex_21_6_b : ∀ x y, ¬ cg_IsNash cg_C216 cg_r216 x y := by
  rintro x y ⟨hxy, hmax⟩
  have hxy' : x = y := hxy
  subst hxy'
  fin_cases x
  · have := hmax 1; norm_num [cg_r216] at this
  · have := hmax 0; norm_num [cg_r216] at this

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The infinitely repeated economy

Miao, §21.4.2, pp. 761–763: the one-period economy of §21.4.1 repeated forever.

* A history is a list `[(x₁, y₁), …, (x_{t-1}, y_{t-1})]` of past pairs, oldest first (the book's
  `(x^{t-1}, y^{t-1}) ∈ X^{t-1} × Y^{t-1}`, zipped). A strategy profile `σ = (σʰ, σᵍ)` is one map
  `CGProfile X Y = List (X × Y) → X × Y` (both components read the same history).
* `cg_cont σ h` is the continuation profile `σ|_h`, `cg_path σ` the induced outcome path (indexed
  from `0`: the book's period `t` is index `t - 1`), `cg_U δ r σ` the government's normalised
  discounted value `Uᵍ(σ) = (1 − δ) ∑ δ^{t-1} r(x_t, y_t)` and `cg_Ut δ r p t` the value from
  index `t` on of a path `p`.
* `cg_IsSPE δ r C σ` is Definition 21.4.1 (subgame perfection with only the government deviating;
  the household side must be a competitive equilibrium `C`), `cg_V δ r C` the set of SPE values.

The payoff `r` is bounded (`|r| ≤ M`, as for continuous `r` on the compact `X × Y` of the book)
and `0 ≤ δ < 1`. Proved here: the value recursion, the one-shot deviation principle
(`cg_isSPE_iff_oneShot`, the step behind "its proof follows from the definition"), Lemma 21.4.1,
SPE-ness of infinite repetition of a static Nash equilibrium (Example 21.4.3, first sentence),
and two bounds on SPE values used in §§21.4.3–21.4.4: SPE values lie in the range of `r` on `C`,
and they are at least any `c` with `c ≤ max_{y'} r(x, y')` for every competitive `(x, y)`
(`cg_V_lower`, the bound behind `v_min = min_y r(h(y), H(h(y)))`, p. 767).
-/

open Filter Topology

namespace Miao.DynamicGames

/-- A strategy profile of the repeated economy (Miao, p. 761): household and government actions
as functions of the history `[(x₁, y₁), …, (x_{t-1}, y_{t-1})]`. -/
abbrev CGProfile (X Y : Type*) := List (X × Y) → X × Y

variable {X Y : Type*}

/-- The continuation profile `σ|_(x^t, y^t)` (Miao, p. 762). -/
def cg_cont (σ : CGProfile X Y) (h : List (X × Y)) : CGProfile X Y := fun k => σ (h ++ k)

/-- Miao, p. 762: `σ|_h(1) = σ_{t+1}(h)` and `σ|_h(s + 1)(ξ^s, η^s) = σ_{t+s+1}(h, ξ^s, η^s)`. -/
theorem cg_cont_apply (σ : CGProfile X Y) (h k : List (X × Y)) : cg_cont σ h k = σ (h ++ k) :=
  rfl

theorem cg_cont_nil (σ : CGProfile X Y) : cg_cont σ [] = σ := rfl

theorem cg_cont_cont (σ : CGProfile X Y) (h k : List (X × Y)) :
    cg_cont (cg_cont σ h) k = cg_cont σ (h ++ k) := by
  funext l
  simp [cg_cont, List.append_assoc]

/-- The outcome path induced by a profile (Miao, p. 761), indexed from `0`. -/
def cg_path : CGProfile X Y → ℕ → X × Y
  | σ, 0 => σ []
  | σ, n + 1 => cg_path (cg_cont σ [σ []]) n

/-- The first `t` outcomes of a path, as a history. -/
def cg_prefix (p : ℕ → X × Y) (t : ℕ) : List (X × Y) := (List.range t).map p

theorem cg_prefix_succ (p : ℕ → X × Y) (t : ℕ) : cg_prefix p (t + 1) = cg_prefix p t ++ [p t] := by
  simp [cg_prefix, List.range_succ]

/-- After the first `t` outcomes of its own path, a profile continues along the shifted path. -/
theorem cg_path_cont_prefix (σ : CGProfile X Y) (t : ℕ) :
    cg_path (cg_cont σ (cg_prefix (cg_path σ) t)) = fun s => cg_path σ (t + s) := by
  induction t with
  | zero => funext s; simp [cg_prefix, cg_cont_nil]
  | succ t ih =>
    set ρ := cg_cont σ (cg_prefix (cg_path σ) t) with hρ
    have h0 : ρ [] = cg_path σ t := by
      have := congrFun ih 0
      rw [Nat.add_zero] at this
      exact this
    rw [cg_prefix_succ, ← cg_cont_cont, ← hρ, ← h0]
    funext s
    have := congrFun ih (s + 1)
    rw [show t + 1 + s = t + (s + 1) by omega, ← this]
    rfl

/-- Miao, p. 761: `(x_t(σ), y_t(σ)) = σ_t(x(σ)^{t-1}, y(σ)^{t-1})`. -/
theorem cg_path_spec (σ : CGProfile X Y) (t : ℕ) :
    cg_path σ t = σ (cg_prefix (cg_path σ) t) := by
  have := congrFun (cg_path_cont_prefix σ t) 0
  simpa [cg_path, cg_cont] using this.symm

/-- The normalised discounted value `(1 − δ) ∑_t δ^t r(p_t)` of an outcome path. -/
noncomputable def cg_pathValue (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) : ℝ :=
  (1 - δ) * ∑' t, δ ^ t * r (p t).1 (p t).2

/-- The government's value `Uᵍ(σ)` of a profile (Miao, p. 761). -/
noncomputable def cg_U (δ : ℝ) (r : X → Y → ℝ) (σ : CGProfile X Y) : ℝ :=
  cg_pathValue δ r (cg_path σ)

/-- The government's value `U_tᵍ(x, y)` from index `t` on (Miao, p. 766; the book's period
`t` is index `t - 1`). -/
noncomputable def cg_Ut (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) (t : ℕ) : ℝ :=
  cg_pathValue δ r (fun s => p (t + s))

/-- The household's value `Uʰ(σ) = (1 − δ) ∑ δ^{t-1} u(x_t, x_t, y_t)` (Miao, p. 761). -/
noncomputable def cg_Uh (δ : ℝ) (u : X → X → Y → ℝ) (σ : CGProfile X Y) : ℝ :=
  cg_pathValue δ (fun x y => u x x y) (cg_path σ)

/-- Miao, p. 761: with the benevolent government `r(x, y) = u(x, x, y)`, `Uʰ(σ) = Uᵍ(σ)`. -/
theorem cg_Uh_eq (δ : ℝ) (u : X → X → Y → ℝ) (σ : CGProfile X Y) :
    cg_Uh δ u σ = cg_U δ (fun x y => u x x y) σ := rfl

theorem cg_summable {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) :
    Summable (fun t => δ ^ t * r (p t).1 (p t).2) := by
  refine ((summable_geometric_of_lt_one hδ0 hδ1).mul_left M).of_norm_bounded (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM _ _) (pow_nonneg hδ0 t)

/-- The value of a path whose per-period payoffs are at most `b` is at most `b`. -/
theorem cg_pathValue_le {δ M b : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {p : ℕ → X × Y} (hb : ∀ t, r (p t).1 (p t).2 ≤ b) :
    cg_pathValue δ r p ≤ b := by
  have hg : Summable (fun t : ℕ => δ ^ t * b) :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right b
  have hle : ∑' t, δ ^ t * r (p t).1 (p t).2 ≤ ∑' t : ℕ, δ ^ t * b :=
    Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (hb t) (pow_nonneg hδ0 t))
      (cg_summable hδ0 hδ1 hM p) hg
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at hle
  have h1 : 0 < 1 - δ := by linarith
  unfold cg_pathValue
  calc (1 - δ) * ∑' t, δ ^ t * r (p t).1 (p t).2 ≤ (1 - δ) * ((1 - δ)⁻¹ * b) :=
        mul_le_mul_of_nonneg_left hle h1.le
    _ = b := by field_simp

/-- The value of a path whose per-period payoffs are at least `a` is at least `a`. -/
theorem cg_le_pathValue {δ M a : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {p : ℕ → X × Y} (ha : ∀ t, a ≤ r (p t).1 (p t).2) :
    a ≤ cg_pathValue δ r p := by
  have hg : Summable (fun t : ℕ => δ ^ t * a) :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right a
  have hle : ∑' t : ℕ, δ ^ t * a ≤ ∑' t, δ ^ t * r (p t).1 (p t).2 :=
    Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (ha t) (pow_nonneg hδ0 t))
      hg (cg_summable hδ0 hδ1 hM p)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at hle
  have h1 : 0 < 1 - δ := by linarith
  unfold cg_pathValue
  calc a = (1 - δ) * ((1 - δ)⁻¹ * a) := by field_simp
    _ ≤ (1 - δ) * ∑' t, δ ^ t * r (p t).1 (p t).2 := mul_le_mul_of_nonneg_left hle h1.le

/-- The value of a constant path is the per-period payoff. -/
theorem cg_pathValue_const {δ : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : X × Y) :
    cg_pathValue δ r (fun _ => q) = r q.1 q.2 := by
  unfold cg_pathValue
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
  have h1 : 1 - δ ≠ 0 := by linarith
  field_simp

/-- The value recursion `U = (1 − δ) r(p₀) + δ U(shifted path)`. -/
theorem cg_pathValue_succ {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) :
    cg_pathValue δ r p = (1 - δ) * r (p 0).1 (p 0).2 + δ * cg_pathValue δ r (fun s => p (s + 1))
    := by
  unfold cg_pathValue
  rw [(cg_summable hδ0 hδ1 hM p).tsum_eq_zero_add]
  have : ∀ b : ℕ, δ ^ (b + 1) * r (p (b + 1)).1 (p (b + 1)).2 =
      δ * (δ ^ b * r (p (b + 1)).1 (p (b + 1)).2) := fun b => by ring
  simp_rw [this]
  rw [tsum_mul_left]
  ring

/-- The recursion for `U_t`: `U_t = (1 − δ) r(x_t, y_t) + δ U_{t+1}`. -/
theorem cg_Ut_succ {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) (t : ℕ) :
    cg_Ut δ r p t = (1 - δ) * r (p t).1 (p t).2 + δ * cg_Ut δ r p (t + 1) := by
  unfold cg_Ut
  rw [cg_pathValue_succ hδ0 hδ1 hM]
  have : (fun s => p (t + (s + 1))) = fun s => p (t + 1 + s) := by
    funext s; congr 1; omega
  simp [this]

theorem cg_Ut_zero (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) : cg_Ut δ r p 0 = cg_pathValue δ r p :=
  by simp [cg_Ut]

/-- The value recursion for a profile: `Uᵍ(σ) = (1 − δ) r(σ₁) + δ Uᵍ(σ|_{σ₁})`. -/
theorem cg_U_rec {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) :
    cg_U δ r σ = (1 - δ) * r (σ []).1 (σ []).2 + δ * cg_U δ r (cg_cont σ [σ []]) := by
  unfold cg_U
  rw [cg_pathValue_succ hδ0 hδ1 hM]
  rfl

/-- The value recursion after a history `h`. -/
theorem cg_U_cont_rec {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (τ : CGProfile X Y) (h : List (X × Y)) :
    cg_U δ r (cg_cont τ h) =
      (1 - δ) * r (τ h).1 (τ h).2 + δ * cg_U δ r (cg_cont τ (h ++ [τ h])) := by
  have e : cg_cont τ h [] = τ h := by simp [cg_cont]
  have := cg_U_rec hδ0 hδ1 hM (cg_cont τ h)
  rw [cg_cont_cont, e] at this
  exact this

/-- Values of profiles are bounded by the payoff bound. -/
theorem cg_abs_U_le {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) : |cg_U δ r σ| ≤ M :=
  abs_le.2 ⟨cg_le_pathValue hδ0 hδ1 hM (fun _ => (abs_le.1 (hM _ _)).1),
    cg_pathValue_le hδ0 hδ1 hM (fun _ => (abs_le.1 (hM _ _)).2)⟩

/-- The value of the profile that repeats `q` after every history. -/
theorem cg_U_const {δ : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (q : X × Y) :
    cg_U δ r (fun _ => q) = r q.1 q.2 := by
  have hp : cg_path (fun _ : List (X × Y) => q) = fun _ => q := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  unfold cg_U
  rw [hp, cg_pathValue_const hδ0 hδ1]

/-- The government's deviation: households keep `σʰ`, the government plays `σ̂ᵍ = g`. -/
def cg_withGov (σ : CGProfile X Y) (g : List (X × Y) → Y) : CGProfile X Y :=
  fun h => ((σ h).1, g h)

/-- **Definition 21.4.1** (SPE, Miao, p. 762): after every history `(x^{t-1}, y^{t-1})`,
(i) the prescribed pair is a competitive equilibrium and (ii) no government strategy `σ̂ᵍ`
does better in the continuation economy. -/
def cg_IsSPE (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (σ : CGProfile X Y) : Prop :=
  ∀ h, σ h ∈ C ∧ ∀ g, cg_U δ r (cg_cont (cg_withGov σ g) h) ≤ cg_U δ r (cg_cont σ h)

/-- **Definition 21.4.1** (Miao, p. 762), unfolded. -/
theorem definition_21_4_1 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (σ : CGProfile X Y) :
    cg_IsSPE δ r C σ ↔ ∀ h, σ h ∈ C ∧
      ∀ g, cg_U δ r (cg_cont (cg_withGov σ g) h) ≤ cg_U δ r (cg_cont σ h) := Iff.rfl

/-- The one-shot condition at the root of a profile `ρ`: the first pair is competitive and no
one-period deviation `η` followed by `ρ`'s continuation pays. -/
def cg_OneShot (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (ρ : CGProfile X Y) : Prop :=
  ρ [] ∈ C ∧ ∀ η, (1 - δ) * r (ρ []).1 η + δ * cg_U δ r (cg_cont ρ [((ρ []).1, η)]) ≤ cg_U δ r ρ

/-- One-shot deviation principle: with bounded payoffs and `0 ≤ δ < 1`, `σ` is an SPE iff after
every history the one-shot condition holds. -/
theorem cg_isSPE_iff_oneShot {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) :
    cg_IsSPE δ r C σ ↔ ∀ h, cg_OneShot δ r C (cg_cont σ h) := by
  classical
  constructor
  · intro hS h
    have e : cg_cont σ h [] = σ h := by simp [cg_cont]
    refine ⟨by rw [e]; exact (hS h).1, fun η => ?_⟩
    rw [e, cg_cont_cont]
    set g : List (X × Y) → Y := fun k => if k = h then η else (σ k).2 with hg
    have h1 : cg_withGov σ g h = ((σ h).1, η) := by simp [cg_withGov, hg]
    have h2 : cg_cont (cg_withGov σ g) (h ++ [((σ h).1, η)]) =
        cg_cont σ (h ++ [((σ h).1, η)]) := by
      funext l
      simp [cg_cont, cg_withGov, hg]
    have := (hS h).2 g
    rw [cg_U_cont_rec hδ0 hδ1 hM, h1, h2] at this
    exact this
  · intro hO
    have e : ∀ h, cg_cont σ h [] = σ h := fun h => by simp [cg_cont]
    have hC : ∀ h, σ h ∈ C := fun h => by rw [← e]; exact (hO h).1
    have hos : ∀ h η, (1 - δ) * r (σ h).1 η + δ * cg_U δ r (cg_cont σ (h ++ [((σ h).1, η)]))
        ≤ cg_U δ r (cg_cont σ h) := fun h η => by
      have := (hO h).2 η
      rw [e, cg_cont_cont] at this
      exact this
    have key : ∀ n : ℕ, ∀ h g, cg_U δ r (cg_cont (cg_withGov σ g) h) ≤
        cg_U δ r (cg_cont σ h) + δ ^ n * (2 * M) := by
      intro n
      induction n with
      | zero =>
        intro h g
        have h1 := abs_le.1 (cg_abs_U_le hδ0 hδ1 hM (cg_cont (cg_withGov σ g) h))
        have h2 := abs_le.1 (cg_abs_U_le hδ0 hδ1 hM (cg_cont σ h))
        simp only [pow_zero, one_mul]
        linarith
      | succ n ih =>
        intro h g
        rw [cg_U_cont_rec hδ0 hδ1 hM]
        have h1 : cg_withGov σ g h = ((σ h).1, g h) := rfl
        have ih' := ih (h ++ [cg_withGov σ g h]) g
        rw [h1] at ih' ⊢
        have hos' := hos h (g h)
        have : δ * cg_U δ r (cg_cont (cg_withGov σ g) (h ++ [((σ h).1, g h)])) ≤
            δ * (cg_U δ r (cg_cont σ (h ++ [((σ h).1, g h)])) + δ ^ n * (2 * M)) :=
          mul_le_mul_of_nonneg_left ih' hδ0
        rw [pow_succ]
        nlinarith
    refine fun h => ⟨hC h, fun g => ?_⟩
    have ht : Tendsto (fun n : ℕ => cg_U δ r (cg_cont σ h) + δ ^ n * (2 * M)) atTop
        (𝓝 (cg_U δ r (cg_cont σ h) + 0 * (2 * M))) :=
      tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _)
    have := ge_of_tendsto' ht (fun n => key n h g)
    simpa using this

/-- Continuations of an SPE are SPEs. -/
theorem cg_IsSPE.cont {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ) (h : List (X × Y)) :
    cg_IsSPE δ r C (cg_cont σ h) := by
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM] at hσ ⊢
  intro k
  rw [cg_cont_cont]
  exact hσ (h ++ k)

/-- The root deviation inequality of an SPE. -/
theorem cg_IsSPE.root {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ) :
    cg_OneShot δ r C σ :=
  (cg_isSPE_iff_oneShot hδ0 hδ1 hM σ).1 hσ []

/-- **Lemma 21.4.1** (Miao, p. 762). With first-period outcome `(x, y) = σ₁`, `σ` is an SPE iff
(i) every continuation `σ|_(ξ, η)` is an SPE, (ii) `(x, y)` is a competitive equilibrium, and
(iii) `(1 − δ) r(x, y) + δ Uᵍ(σ|_(x, y)) ≥ (1 − δ) r(x, η) + δ Uᵍ(σ|_(x, η))` for all `η`. -/
theorem lemma_21_4_1 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (σ : CGProfile X Y) :
    cg_IsSPE δ r C σ ↔ (∀ ξ η, cg_IsSPE δ r C (cg_cont σ [(ξ, η)])) ∧ σ [] ∈ C ∧
      ∀ η, (1 - δ) * r (σ []).1 η + δ * cg_U δ r (cg_cont σ [((σ []).1, η)]) ≤
        (1 - δ) * r (σ []).1 (σ []).2 + δ * cg_U δ r (cg_cont σ [σ []]) := by
  rw [← cg_U_rec hδ0 hδ1 hM]
  constructor
  · intro hS
    exact ⟨fun ξ η => hS.cont hδ0 hδ1 hM _, (hS.root hδ0 hδ1 hM).1,
      (hS.root hδ0 hδ1 hM).2⟩
  · rintro ⟨hcont, hC, hdev⟩
    rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
    intro h
    cases h with
    | nil => exact ⟨hC, hdev⟩
    | cons q h' =>
      have e : cg_cont σ (q :: h') = cg_cont (cg_cont σ [q]) h' := by
        rw [cg_cont_cont]; rfl
      rw [e]
      exact (cg_isSPE_iff_oneShot hδ0 hδ1 hM _).1 (hcont q.1 q.2) h'

/-- Example 21.4.3 (Miao, p. 763), first sentence: infinite repetition of a one-period Nash
equilibrium `(x^N, y^N)` (competitive, and `y^N` a best response to `x^N`) is an SPE, with
value `r(x^N, y^N)`. -/
theorem cg_nash_repetition_spe {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xN : X} {yN : Y} (hC : (xN, yN) ∈ C)
    (hN : ∀ y', r xN y' ≤ r xN yN) :
    cg_IsSPE δ r C (fun _ => (xN, yN)) ∧ cg_U δ r (fun _ => (xN, yN)) = r xN yN := by
  refine ⟨?_, cg_U_const hδ0 hδ1 _⟩
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  intro h
  refine ⟨hC, fun η => ?_⟩
  have e : ∀ k, cg_cont (fun _ : List (X × Y) => (xN, yN)) k = fun _ => (xN, yN) :=
    fun k => rfl
  rw [e, e, cg_U_const hδ0 hδ1]
  have := hN η
  have h1 : 0 ≤ 1 - δ := by linarith
  nlinarith

/-- The set of SPE values `V = {Uᵍ(σ) : σ is an SPE}` (Miao, p. 764). -/
def cg_V (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) : Set ℝ :=
  {v | ∃ σ, cg_IsSPE δ r C σ ∧ cg_U δ r σ = v}

/-- SPE values are bounded by the payoff bound. -/
theorem cg_V_abs_le {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {v : ℝ} (hv : v ∈ cg_V δ r C) : |v| ≤ M := by
  obtain ⟨σ, -, rfl⟩ := hv
  exact cg_abs_U_le hδ0 hδ1 hM σ

/-- The SPE value set is bounded. -/
theorem cg_V_isBounded {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) : Bornology.IsBounded (cg_V δ r C) :=
  (isBounded_iff_forall_norm_le (E := ℝ)).2
    ⟨M, fun _ hv => by rw [Real.norm_eq_abs]; exact cg_V_abs_le hδ0 hδ1 hM hv⟩

/-- The path of an SPE stays in the competitive-equilibrium set. -/
theorem cg_IsSPE.path_mem {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ)
    (t : ℕ) : cg_path σ t ∈ C := by
  induction t generalizing σ with
  | zero => exact (hσ []).1
  | succ t ih => exact ih (hσ.cont hδ0 hδ1 hM _)

/-- Miao, p. 765, step 1 of the algorithm: SPE values lie in `[min_C r, max_C r]`; here, in
`[a, b]` whenever `a ≤ r ≤ b` on `C`. -/
theorem cg_V_subset_Icc {δ M a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hab : ∀ p ∈ C, a ≤ r p.1 p.2 ∧ r p.1 p.2 ≤ b) :
    cg_V δ r C ⊆ Set.Icc a b := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact ⟨cg_le_pathValue hδ0 hδ1 hM (fun t => (hab _ (hσ.path_mem hδ0 hδ1 hM t)).1),
    cg_pathValue_le hδ0 hδ1 hM (fun t => (hab _ (hσ.path_mem hδ0 hδ1 hM t)).2)⟩

/-- Miao, p. 767: the worst SPE value is at least `min_y r(h(y), H(h(y)))`. Here: if every
competitive `(x, y)` admits a deviation `y'` with `r(x, y') ≥ c`, every SPE value is `≥ c`. -/
theorem cg_V_lower {δ M c : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (hc : ∀ x y, (x, y) ∈ C → ∃ y', c ≤ r x y') :
    ∀ v ∈ cg_V δ r C, c ≤ v := by
  intro v hv
  have hne : (cg_V δ r C).Nonempty := ⟨v, hv⟩
  have hbdd : BddBelow (cg_V δ r C) :=
    ⟨-M, fun w hw => (abs_le.1 (cg_V_abs_le hδ0 hδ1 hM hw)).1⟩
  set m := sInf (cg_V δ r C)
  have key : ∀ w ∈ cg_V δ r C, (1 - δ) * c + δ * m ≤ w := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨y', hy'⟩ := hc _ _ (hσ []).1
    have hroot := (hσ.root hδ0 hδ1 hM).2 y'
    have hmem : cg_U δ r (cg_cont σ [((σ []).1, y')]) ∈ cg_V δ r C :=
      ⟨_, hσ.cont hδ0 hδ1 hM _, rfl⟩
    have h1 : m ≤ cg_U δ r (cg_cont σ [((σ []).1, y')]) := csInf_le hbdd hmem
    have h2 : (1 - δ) * c ≤ (1 - δ) * r (σ []).1 y' :=
      mul_le_mul_of_nonneg_left hy' (by linarith)
    have h3 : δ * m ≤ δ * cg_U δ r (cg_cont σ [((σ []).1, y')]) :=
      mul_le_mul_of_nonneg_left h1 hδ0
    linarith
  have hm : (1 - δ) * c + δ * m ≤ m := le_csInf hne key
  have hcm : c ≤ m := by
    by_contra hlt
    push Not at hlt
    nlinarith
  exact hcm.trans (csInf_le hbdd hv)

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive strategies

Miao, §21.4.5, pp. 769–771: strategies that use a state `v` (the promised continuation value) with
`x_t = zʰ(v_t)`, `y_t = zᵍ(v_t)`, `v_{t+1} = V(v_t, x_t, y_t)` (Definition 21.4.5), the trigger
strategy (Example 21.4.5) and the stick-and-carrot strategy (Example 21.4.6). The state map is
`Vf` here, since `V` names the SPE value set.

* `cg_recStrat zh zg Vf v` is the profile of a recursive strategy started at `v`; after a history
  it is the recursive strategy started at the state reached (`cg_recStrat_cont`), and its outcome
  path obeys the recursion of Definition 21.4.5 (`definition_21_4_5`).
* `cg_recStrat_value`: if the states move inside a bounded set `S` and satisfy promise keeping
  `s = (1 − δ) r(zʰ(s), zᵍ(s)) + δ V(s, zʰ(s), zᵍ(s))` on `S`, the state is the value.
* `cg_recursive_spe`: the corrected "if" half of the characterisation on p. 770. The book states
  conditions (i)–(iii) at the initial state only, and (ii) only for `V(v, zʰ(v), y)`; they must
  hold at every state of an invariant set, which must also be closed under the household-side
  deviations `V(s, ξ, η)` (every history is a subgame). The printed version is refuted in
  `CGExamples` (`cg_definition_21_4_5_counterexample`). The "only if" half holds as printed when
  states are promised values (`cg_recursive_spe_only_if`).
* `example_21_4_5`: the trigger strategy is an SPE with value `v^b` under the incentive constraint
  `(1 − δ) r(x^b, y') + δ v^N ≤ v^b`. The book's hypothesis `v^b > v^N` is neither sufficient
  (refuted in `CGExamples`) nor needed.
* `example_21_4_6`: the stick-and-carrot strategy is an SPE with value `ṽ`; besides the book's
  condition `ṽ ≥ (1 − δ) r(x*, y') + δṽ` it needs the carrot's own incentive constraint
  `v^R ≥ (1 − δ) r(x^R, y') + δṽ`, which the book omits (refuted in `CGExamples`).
-/

open Filter Topology

namespace Miao.DynamicGames

variable {X Y : Type*}

/-- The state reached after a history, from the initial state `v`. -/
def cg_recState (Vf : ℝ → X → Y → ℝ) (v : ℝ) (h : List (X × Y)) : ℝ :=
  h.foldl (fun s q => Vf s q.1 q.2) v

/-- The profile of the recursive strategy `(φ, v)` with `φ = (zʰ, zᵍ, V)` (Definition 21.4.5). -/
def cg_recStrat (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ) : CGProfile X Y :=
  fun h => (zh (cg_recState Vf v h), zg (cg_recState Vf v h))

theorem cg_recStrat_cont (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ)
    (h : List (X × Y)) :
    cg_cont (cg_recStrat zh zg Vf v) h = cg_recStrat zh zg Vf (cg_recState Vf v h) := by
  funext k
  simp [cg_cont, cg_recStrat, cg_recState, List.foldl_append]

theorem cg_recStrat_cont_single (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ)
    (q : X × Y) : cg_cont (cg_recStrat zh zg Vf v) [q] = cg_recStrat zh zg Vf (Vf v q.1 q.2) :=
  cg_recStrat_cont zh zg Vf v [q]

theorem cg_recState_mem {Vf : ℝ → X → Y → ℝ} {S : Set ℝ} (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (h : List (X × Y)) : ∀ v ∈ S, cg_recState Vf v h ∈ S := by
  induction h with
  | nil => exact fun v hv => hv
  | cons q h ih =>
    intro v hv
    exact ih _ (hinv v hv q.1 q.2)

/-- The state sequence `v_1 = v`, `v_{t+1} = V(v_t, zʰ(v_t), zᵍ(v_t))` (indexed from `0`). -/
def cg_recSeq (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) : ℝ → ℕ → ℝ
  | v, 0 => v
  | v, n + 1 => cg_recSeq zh zg Vf (Vf v (zh v) (zg v)) n

/-- **Definition 21.4.5** (recursive strategies, Miao, p. 769): the outcome path of `(φ, v)` is
`x_t = zʰ(v_t)`, `y_t = zᵍ(v_t)` with `v_1 = v` and `v_{t+1} = V(v_t, x_t, y_t)`. -/
theorem definition_21_4_5 (zh : ℝ → X) (zg : ℝ → Y) (Vf : ℝ → X → Y → ℝ) (v : ℝ) (n : ℕ) :
    cg_path (cg_recStrat zh zg Vf v) n =
        (zh (cg_recSeq zh zg Vf v n), zg (cg_recSeq zh zg Vf v n)) ∧
      cg_recSeq zh zg Vf v 0 = v ∧
      cg_recSeq zh zg Vf v (n + 1) = Vf (cg_recSeq zh zg Vf v n)
        (zh (cg_recSeq zh zg Vf v n)) (zg (cg_recSeq zh zg Vf v n)) := by
  refine ⟨?_, rfl, ?_⟩
  · induction n generalizing v with
    | zero => rfl
    | succ n ih =>
      have e : cg_cont (cg_recStrat zh zg Vf v) [cg_recStrat zh zg Vf v []] =
          cg_recStrat zh zg Vf (Vf v (zh v) (zg v)) :=
        cg_recStrat_cont_single zh zg Vf v _
      have : cg_path (cg_recStrat zh zg Vf v) (n + 1) =
          cg_path (cg_recStrat zh zg Vf (Vf v (zh v) (zg v))) n := by
        rw [← e]; rfl
      rw [this, ih]
      rfl
  · induction n generalizing v with
    | zero => rfl
    | succ n ih => exact ih _

/-- Under promise keeping on a bounded invariant set `S`, the state of a recursive strategy is its
value: `Uᵍ(σ_s) = s` for `s ∈ S`. -/
theorem cg_recStrat_value {δ M K : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {zh : ℝ → X} {zg : ℝ → Y} {Vf : ℝ → X → Y → ℝ} {S : Set ℝ}
    (hK : ∀ s ∈ S, |s| ≤ K) (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (hpk : ∀ s ∈ S, (1 - δ) * r (zh s) (zg s) + δ * Vf s (zh s) (zg s) = s) :
    ∀ s ∈ S, cg_U δ r (cg_recStrat zh zg Vf s) = s := by
  have hrec : ∀ s, cg_U δ r (cg_recStrat zh zg Vf s) = (1 - δ) * r (zh s) (zg s) +
      δ * cg_U δ r (cg_recStrat zh zg Vf (Vf s (zh s) (zg s))) := fun s => by
    rw [cg_U_rec hδ0 hδ1 hM, cg_recStrat_cont_single]
    rfl
  have key : ∀ n : ℕ, ∀ s ∈ S, |cg_U δ r (cg_recStrat zh zg Vf s) - s| ≤ δ ^ n * (M + K) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h1 := cg_abs_U_le hδ0 hδ1 hM (cg_recStrat zh zg Vf s)
      have h2 := hK s hs
      simp only [pow_zero, one_mul]
      calc |cg_U δ r (cg_recStrat zh zg Vf s) - s| ≤ |cg_U δ r (cg_recStrat zh zg Vf s)| + |s| :=
            abs_sub _ _
        _ ≤ M + K := add_le_add h1 h2
    | succ n ih =>
      intro s hs
      have hs' := hinv s hs (zh s) (zg s)
      have e : cg_U δ r (cg_recStrat zh zg Vf s) - s =
          δ * (cg_U δ r (cg_recStrat zh zg Vf (Vf s (zh s) (zg s))) - Vf s (zh s) (zg s)) := by
        rw [hrec s]
        have := hpk s hs
        linarith
      rw [e, abs_mul, abs_of_nonneg hδ0]
      calc δ * |cg_U δ r (cg_recStrat zh zg Vf (Vf s (zh s) (zg s))) - Vf s (zh s) (zg s)|
          ≤ δ * (δ ^ n * (M + K)) := mul_le_mul_of_nonneg_left (ih _ hs') hδ0
        _ = δ ^ (n + 1) * (M + K) := by ring
  intro s hs
  have ht : Tendsto (fun n : ℕ => δ ^ n * (M + K)) atTop (𝓝 (0 * (M + K))) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _
  have := ge_of_tendsto' ht (fun n => key n s hs)
  rw [zero_mul] at this
  have := abs_nonpos_iff.1 this
  linarith

/-- Miao, p. 770, "if" half of the SPE characterisation of recursive strategies, corrected: if on
a bounded set `S` of states, closed under every `V(s, ξ, η)`, (i) `(zʰ(s), zᵍ(s)) ∈ C`, promise
keeping holds and (iii) `(1 − δ) r(zʰ(s), y) + δ V(s, zʰ(s), y) ≤ s` for all `y`, then from every
`v ∈ S` the recursive strategy is an SPE with value `v`. -/
theorem cg_recursive_spe {δ M K : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {zh : ℝ → X} {zg : ℝ → Y} {Vf : ℝ → X → Y → ℝ}
    {S : Set ℝ} (hK : ∀ s ∈ S, |s| ≤ K) (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (hpk : ∀ s ∈ S, (1 - δ) * r (zh s) (zg s) + δ * Vf s (zh s) (zg s) = s)
    (hC : ∀ s ∈ S, (zh s, zg s) ∈ C)
    (hIC : ∀ s ∈ S, ∀ y', (1 - δ) * r (zh s) y' + δ * Vf s (zh s) y' ≤ s) :
    ∀ v ∈ S, cg_IsSPE δ r C (cg_recStrat zh zg Vf v) ∧ cg_U δ r (cg_recStrat zh zg Vf v) = v := by
  have hval := cg_recStrat_value hδ0 hδ1 hM hK hinv hpk
  intro v hv
  refine ⟨?_, hval v hv⟩
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  intro h
  rw [cg_recStrat_cont]
  set s := cg_recState Vf v h
  have hs : s ∈ S := cg_recState_mem hinv h v hv
  refine ⟨hC s hs, fun η => ?_⟩
  have e : cg_recStrat zh zg Vf s [] = (zh s, zg s) := rfl
  rw [e, cg_recStrat_cont_single, hval s hs, hval _ (hinv s hs _ _)]
  exact hIC s hs η

/-- Miao, p. 770, "only if" half: if the states of a recursive strategy are promised values
(promise keeping on a bounded invariant `S ∋ v`) and `(φ, v)` is an SPE, then `v ∈ V`,
(i) `(zʰ(v), zᵍ(v)) ∈ C`, (ii) every `V(v, ξ, η) ∈ V` and (iii) the incentive constraint holds. -/
theorem cg_recursive_spe_only_if {δ M K : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {zh : ℝ → X} {zg : ℝ → Y} {Vf : ℝ → X → Y → ℝ}
    {S : Set ℝ} (hK : ∀ s ∈ S, |s| ≤ K) (hinv : ∀ s ∈ S, ∀ ξ η, Vf s ξ η ∈ S)
    (hpk : ∀ s ∈ S, (1 - δ) * r (zh s) (zg s) + δ * Vf s (zh s) (zg s) = s) {v : ℝ}
    (hv : v ∈ S) (hspe : cg_IsSPE δ r C (cg_recStrat zh zg Vf v)) :
    v ∈ cg_V δ r C ∧ (zh v, zg v) ∈ C ∧ (∀ ξ η, Vf v ξ η ∈ cg_V δ r C) ∧
      ∀ y', (1 - δ) * r (zh v) y' + δ * Vf v (zh v) y' ≤ v := by
  have hval := cg_recStrat_value hδ0 hδ1 hM hK hinv hpk
  refine ⟨⟨_, hspe, hval v hv⟩, (hspe []).1, fun ξ η => ?_, fun y' => ?_⟩
  · refine ⟨_, hspe.cont hδ0 hδ1 hM [(ξ, η)], ?_⟩
    rw [cg_recStrat_cont_single]
    exact hval _ (hinv v hv ξ η)
  · have := (hspe.root hδ0 hδ1 hM).2 y'
    have e : cg_recStrat zh zg Vf v [] = (zh v, zg v) := rfl
    rw [e, cg_recStrat_cont_single, hval _ (hinv v hv _ _), hval v hv] at this
    exact this

open Classical in
/-- The household rule of the trigger strategy (Example 21.4.5). -/
noncomputable def cg_trigZh (vb : ℝ) (xb xN : X) : ℝ → X := fun v => if v = vb then xb else xN

open Classical in
/-- The government rule of the trigger strategy (Example 21.4.5). -/
noncomputable def cg_trigZg (vb : ℝ) (yb yN : Y) : ℝ → Y := fun v => if v = vb then yb else yN

open Classical in
/-- The state map of the trigger strategy (Example 21.4.5): `v^b` after `(v^b, x^b, y^b)`,
`v^N` otherwise. -/
noncomputable def cg_trigV (vb vN : ℝ) (xb : X) (yb : Y) : ℝ → X → Y → ℝ :=
  fun v x y => if v = vb ∧ x = xb ∧ y = yb then vb else vN

/-- The trigger strategy keeps its promises: on `{v^b, v^N}` the state is the value. -/
theorem cg_trigger_value {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (xb xN : X) (yb yN : Y) :
    ∀ s ∈ ({r xb yb, r xN yN} : Set ℝ), cg_U δ r (cg_recStrat (cg_trigZh (r xb yb) xb xN)
      (cg_trigZg (r xb yb) yb yN) (cg_trigV (r xb yb) (r xN yN) xb yb) s) = s := by
  classical
  refine cg_recStrat_value (K := |r xb yb| + |r xN yN|) hδ0 hδ1 hM ?_ ?_ ?_
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg (r xN yN)]
    · linarith [abs_nonneg (r xb yb)]
  · intro s _ ξ η
    unfold cg_trigV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    by_cases h : s = r xb yb
    · subst h
      simp [cg_trigZh, cg_trigZg, cg_trigV]
      ring
    · have hs' : s = r xN yN := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_trigZh, cg_trigZg, cg_trigV, h, false_and, ↓reduceIte]
      rw [← hs']
      ring

/-- **Example 21.4.5** (trigger strategy, Miao, p. 770), corrected. With a one-period Nash
equilibrium `(x^N, y^N)` and a competitive `(x^b, y^b)` satisfying the incentive constraint
`(1 − δ) r(x^b, y') + δ v^N ≤ v^b` for all `y'`, the trigger strategy (play `(x^b, y^b)` while the
state is `v^b`, revert to the Nash state `v^N` forever after any deviation) is an SPE with value
`v^b = r(x^b, y^b)`. The book assumes only `v^b > v^N`, which does not suffice
(`cg_example_21_4_5_counterexample`). -/
theorem example_21_4_5 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xb xN : X} {yb yN : Y} (hb : (xb, yb) ∈ C)
    (hN : (xN, yN) ∈ C) (hNash : ∀ y', r xN y' ≤ r xN yN)
    (hIC : ∀ y', (1 - δ) * r xb y' + δ * r xN yN ≤ r xb yb) :
    cg_IsSPE δ r C (cg_recStrat (cg_trigZh (r xb yb) xb xN) (cg_trigZg (r xb yb) yb yN)
        (cg_trigV (r xb yb) (r xN yN) xb yb) (r xb yb)) ∧
      cg_U δ r (cg_recStrat (cg_trigZh (r xb yb) xb xN) (cg_trigZg (r xb yb) yb yN)
        (cg_trigV (r xb yb) (r xN yN) xb yb) (r xb yb)) = r xb yb := by
  classical
  have h1 : 0 ≤ 1 - δ := by linarith
  refine cg_recursive_spe (K := |r xb yb| + |r xN yN|) (S := {r xb yb, r xN yN}) hδ0 hδ1 hM
    ?_ ?_ ?_ ?_ ?_ (r xb yb) (Or.inl rfl)
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg (r xN yN)]
    · linarith [abs_nonneg (r xb yb)]
  · intro s _ ξ η
    unfold cg_trigV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    by_cases h : s = r xb yb
    · subst h
      simp [cg_trigZh, cg_trigZg, cg_trigV]
      ring
    · have hs' : s = r xN yN := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_trigZh, cg_trigZg, cg_trigV, h, false_and, ↓reduceIte]
      rw [← hs']
      ring
  · intro s _
    by_cases h : s = r xb yb
    · simp only [cg_trigZh, cg_trigZg, h, ↓reduceIte]; exact hb
    · simp only [cg_trigZh, cg_trigZg, h, ↓reduceIte]; exact hN
  · intro s hs y'
    by_cases h : s = r xb yb
    · subst h
      by_cases hy : y' = yb
      · subst hy
        simp only [cg_trigZh, cg_trigV, and_self, ↓reduceIte]
        linarith
      · simp only [cg_trigZh, cg_trigV, hy, and_false, ↓reduceIte]
        exact hIC y'
    · have hs' : s = r xN yN := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_trigZh, cg_trigV, h, false_and, ↓reduceIte, ↓reduceIte]
      rw [hs']
      nlinarith [hNash y']

open Classical in
/-- The household rule of the stick-and-carrot strategy (Example 21.4.6). -/
noncomputable def cg_scZh (vR : ℝ) (xR xs : X) : ℝ → X := fun v => if v = vR then xR else xs

open Classical in
/-- The government rule of the stick-and-carrot strategy (Example 21.4.6). -/
noncomputable def cg_scZg (vR : ℝ) (yR ys : Y) : ℝ → Y := fun v => if v = vR then yR else ys

open Classical in
/-- The state map of the stick-and-carrot strategy (Example 21.4.6): `v^R` after the prescribed
pair, `ṽ` otherwise. -/
noncomputable def cg_scV (vR vt : ℝ) (xR xs : X) (yR ys : Y) : ℝ → X → Y → ℝ :=
  fun v x y => if x = cg_scZh vR xR xs v ∧ y = cg_scZg vR yR ys v then vR else vt

/-- The stick-and-carrot strategy keeps its promises: with `ṽ = (1 − δ) r(x*, y*) + δ v^R`, on
`{v^R, ṽ}` the state is the value. -/
theorem cg_stickCarrot_value {δ M : ℝ} {r : X → Y → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (xR xs : X) (yR ys : Y) :
    ∀ s ∈ ({r xR yR, (1 - δ) * r xs ys + δ * r xR yR} : Set ℝ),
      cg_U δ r (cg_recStrat (cg_scZh (r xR yR) xR xs) (cg_scZg (r xR yR) yR ys)
        (cg_scV (r xR yR) ((1 - δ) * r xs ys + δ * r xR yR) xR xs yR ys) s) = s := by
  classical
  set vR := r xR yR
  set vt := (1 - δ) * r xs ys + δ * r xR yR
  refine cg_recStrat_value (K := |vR| + |vt|) hδ0 hδ1 hM ?_ ?_ ?_
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg vt]
    · linarith [abs_nonneg vR]
  · intro s _ ξ η
    unfold cg_scV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) (cg_scZg vR yR ys s) = vR := by
      simp [cg_scV]
    rw [hV]
    by_cases h : s = vR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      ring
    · have hs' : s = vt := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      rw [hs']

/-- **Example 21.4.6** (stick and carrot, Abreu 1988; Miao, pp. 770–771), corrected. Let the stick
`(x*, y*)` and the carrot `(x^R, y^R)` be competitive, `ṽ = (1 − δ) r(x*, y*) + δ v^R` with
`v^R = r(x^R, y^R)`. If `ṽ ≥ (1 − δ) r(x*, y') + δṽ` for all `y'` (the book's condition) and
`v^R ≥ (1 − δ) r(x^R, y') + δṽ` for all `y'` (the carrot's incentive constraint, which the book
omits), the stick-and-carrot strategy started at `ṽ` is an SPE with value `ṽ`. -/
theorem example_21_4_6 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xR xs : X} {yR ys : Y} (hR : (xR, yR) ∈ C)
    (hs : (xs, ys) ∈ C)
    (hstick : ∀ y', (1 - δ) * r xs y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤
      (1 - δ) * r xs ys + δ * r xR yR)
    (hcarrot : ∀ y', (1 - δ) * r xR y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤ r xR yR) :
    cg_IsSPE δ r C (cg_recStrat (cg_scZh (r xR yR) xR xs) (cg_scZg (r xR yR) yR ys)
        (cg_scV (r xR yR) ((1 - δ) * r xs ys + δ * r xR yR) xR xs yR ys)
        ((1 - δ) * r xs ys + δ * r xR yR)) ∧
      cg_U δ r (cg_recStrat (cg_scZh (r xR yR) xR xs) (cg_scZg (r xR yR) yR ys)
        (cg_scV (r xR yR) ((1 - δ) * r xs ys + δ * r xR yR) xR xs yR ys)
        ((1 - δ) * r xs ys + δ * r xR yR)) = (1 - δ) * r xs ys + δ * r xR yR := by
  classical
  set vR := r xR yR
  set vt := (1 - δ) * r xs ys + δ * r xR yR with hvt
  refine cg_recursive_spe (K := |vR| + |vt|) (S := {vR, vt}) hδ0 hδ1 hM ?_ ?_ ?_ ?_ ?_ vt
    (Or.inr rfl)
  · intro s hs
    rcases hs with rfl | rfl
    · linarith [abs_nonneg vt]
    · linarith [abs_nonneg vR]
  · intro s _ ξ η
    unfold cg_scV
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro s hs
    have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) (cg_scZg vR yR ys s) = vR := by
      simp [cg_scV]
    rw [hV]
    by_cases h : s = vR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      ring
    · have hs' : s = vt := by
        rcases hs with h' | h'
        · exact absurd h' h
        · exact h'
      simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
      rw [hs']
  · intro s _
    by_cases h : s = vR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]; exact hR
    · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]; exact hs
  · intro s hs' y'
    by_cases hy : y' = cg_scZg vR yR ys s
    · have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) y' = vR := by
        simp [cg_scV, hy]
      rw [hV, hy]
      by_cases h : s = vR
      · simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
        linarith
      · have hs'' : s = vt := by
          rcases hs' with h' | h'
          · exact absurd h' h
          · exact h'
        simp only [cg_scZh, cg_scZg, h, ↓reduceIte]
        rw [hs'']
    · have hV : cg_scV vR vt xR xs yR ys s (cg_scZh vR xR xs s) y' = vt := by
        simp [cg_scV, hy]
      rw [hV]
      by_cases h : s = vR
      · simp only [cg_scZh, h, ↓reduceIte]
        exact hcarrot y'
      · have hs'' : s = vt := by
          rcases hs' with h' | h'
          · exact absurd h' h
          · exact h'
        simp only [cg_scZh, h, ↓reduceIte]
        rw [hs'']
        exact hstick y'

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The equilibrium value set

Miao, §21.4.3, pp. 764–766: the APS method for the credible-policy economy.

* `cg_Admissible`, `cg_B`, `cg_SelfGenerating`: Definitions 21.4.2–21.4.4.
* `lemma_21_4_2`: `B` is monotone and (for compact `X`, `Y`, closed `C` and continuous `r`)
  preserves compactness. The proof writes `B(W)` as the continuous image of the compact set
  `cg_K W` of tuples `((x, y), w₁, w₂)` with a single punishment value `w₂ ∈ W`
  (`cg_B_eq_image`, which needs only `W` compact).
* `lemma_21_4_3`: a bounded self-generating `W` has `B(W) ⊆ V`. The proof builds the recursive
  strategy of §21.4.5 whose states are the values in `W` (as in the book's proof).
* `theorem_21_4_1`: `V = B(V)`, `V` is bounded, and it contains every bounded fixed point.
  "Largest fixed point" needs the qualifier *bounded*: `B(ℝ) = ℝ` in Example 21.4.2
  (`cg_theorem_21_4_1_unbounded` in `CGExamples`).
* The algorithm on pp. 765–766: step 1 (`cg_aps_step1`), the characterisation of
  `B([w_min⁰, w_max⁰])` in step 2 (`cg_aps_step2`, `cg_aps_step2_max`), and step 3: the iterates
  `W_{j+1} = B(W_j)` decrease, are compact, contain `V`, and their intersection is `V`
  (`cg_aps_step3`). In the book's formula for `w¹_max` the bounds of the constraint must be the
  bounds `w⁰_max`, `w⁰_min` of `W₀`, not the unknowns `w¹_max`, `w¹_min`.
-/

open Filter Topology

namespace Miao.DynamicGames

variable {X Y : Type*}

/-- **Definition 21.4.2** (Miao, p. 764): `(x, y, w)` is admissible with respect to `W`. -/
def cg_Admissible (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) (x : X) (y : Y)
    (w : X × Y → ℝ) : Prop :=
  (x, y) ∈ C ∧ (∀ q, w q ∈ W) ∧
    ∀ y', (1 - δ) * r x y' + δ * w (x, y') ≤ (1 - δ) * r x y + δ * w (x, y)

/-- **Definition 21.4.3** (Miao, p. 764): `B(W)`, the values of admissible tuples. -/
def cg_B (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) : Set ℝ :=
  {v | ∃ x y w, cg_Admissible δ r C W x y w ∧ v = (1 - δ) * r x y + δ * w (x, y)}

/-- **Definition 21.4.4** (Miao, p. 764): `W` is self-generating if `W ⊆ B(W)`. -/
def cg_SelfGenerating (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) : Prop :=
  W ⊆ cg_B δ r C W

/-- **Definition 21.4.2** (Miao, p. 764), unfolded. -/
theorem definition_21_4_2 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) (x : X) (y : Y)
    (w : X × Y → ℝ) : cg_Admissible δ r C W x y w ↔ (x, y) ∈ C ∧ (∀ q, w q ∈ W) ∧
      ∀ y', (1 - δ) * r x y' + δ * w (x, y') ≤ (1 - δ) * r x y + δ * w (x, y) := Iff.rfl

/-- **Definition 21.4.3** (Miao, p. 764), unfolded. -/
theorem definition_21_4_3 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) (v : ℝ) :
    v ∈ cg_B δ r C W ↔
      ∃ x y w, cg_Admissible δ r C W x y w ∧ v = (1 - δ) * r x y + δ * w (x, y) := Iff.rfl

/-- **Definition 21.4.4** (Miao, p. 764), unfolded. -/
theorem definition_21_4_4 (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) :
    cg_SelfGenerating δ r C W ↔ W ⊆ cg_B δ r C W := Iff.rfl

theorem cg_B_mono (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) : Monotone (cg_B δ r C) := by
  intro W W' hWW' v ⟨x, y, w, ⟨hC, hw, hIC⟩, hv⟩
  exact ⟨x, y, w, ⟨hC, fun q => hWW' (hw q), hIC⟩, hv⟩

/-- Tuples `((x, y), w₁, w₂)` with `(x, y) ∈ C`, `w₁, w₂ ∈ W` and
`(1 − δ) r(x, y') + δ w₂ ≤ (1 − δ) r(x, y) + δ w₁` for all `y'`. -/
def cg_K (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (W : Set ℝ) : Set ((X × Y) × ℝ × ℝ) :=
  {q | q.1 ∈ C ∧ q.2.1 ∈ W ∧ q.2.2 ∈ W ∧
    ∀ y', (1 - δ) * r q.1.1 y' + δ * q.2.2 ≤ (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1}

theorem cg_K_mono (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) : Monotone (cg_K δ r C) := by
  intro W W' h q ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h h2, h h3, h4⟩

/-- For compact `W`, `B(W)` is the image of `cg_K W` under `((x, y), w₁, w₂) ↦ (1 − δ) r + δ w₁`:
a single punishment value (the minimum of `W`) suffices. -/
theorem cg_B_eq_image {δ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) {W : Set ℝ}
    (hW : IsCompact W) :
    cg_B δ r C W = (fun q : (X × Y) × ℝ × ℝ => (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1) ''
      cg_K δ r C W := by
  classical
  ext v
  constructor
  · rintro ⟨x, y, w, ⟨hC, hw, hIC⟩, rfl⟩
    have hne : W.Nonempty := ⟨_, hw (x, y)⟩
    refine ⟨((x, y), w (x, y), sInf W), ⟨hC, hw _, hW.sInf_mem hne, fun y' => ?_⟩, rfl⟩
    have h1 : sInf W ≤ w (x, y') := csInf_le hW.bddBelow (hw _)
    have h2 := hIC y'
    have h3 : δ * sInf W ≤ δ * w (x, y') := mul_le_mul_of_nonneg_left h1 hδ0
    dsimp only
    linarith
  · rintro ⟨⟨⟨x, y⟩, w₁, w₂⟩, ⟨hC, h1, h2, hIC⟩, rfl⟩
    refine ⟨x, y, fun q => if q = (x, y) then w₁ else w₂, ⟨hC, fun q => ?_, fun y' => ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      · exact h1
      · exact h2
    · by_cases hy : y' = y
      · subst hy; exact le_rfl
      · have : ((x, y') : X × Y) ≠ (x, y) := by simp [hy]
        simp only [this, ↓reduceIte]
        exact hIC y'
    · simp

/-- `cg_K W` is compact for compact `W`, compact `X`, `Y`, closed `C` and continuous `r`. -/
theorem cg_K_isCompact [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] {δ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hC : IsClosed C)
    (hr : Continuous (fun q : X × Y => r q.1 q.2)) {W : Set ℝ} (hW : IsCompact W) :
    IsCompact (cg_K δ r C W) := by
  have hrc : ∀ y', Continuous (fun q : (X × Y) × ℝ × ℝ => r q.1.1 y') := fun y' =>
    hr.comp (continuous_fst.fst.prodMk continuous_const)
  have hr2 : Continuous (fun q : (X × Y) × ℝ × ℝ => r q.1.1 q.1.2) :=
    hr.comp continuous_fst
  have hD : IsClosed {q : (X × Y) × ℝ × ℝ |
      ∀ y', (1 - δ) * r q.1.1 y' + δ * q.2.2 ≤ (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y' => isClosed_le
      ((continuous_const.mul (hrc y')).add (continuous_const.mul continuous_snd.snd))
      ((continuous_const.mul hr2).add (continuous_const.mul continuous_snd.fst))
  have hP : IsCompact (C ×ˢ (W ×ˢ W)) := hC.isCompact.prod (hW.prod hW)
  have : cg_K δ r C W = (C ×ˢ (W ×ˢ W)) ∩ {q : (X × Y) × ℝ × ℝ |
      ∀ y', (1 - δ) * r q.1.1 y' + δ * q.2.2 ≤ (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1} := by
    ext q
    simp only [cg_K, Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq]
    tauto
  rw [this]
  exact hP.inter_right hD

/-- **Lemma 21.4.2** (Miao, p. 764). The operator `B` is monotone and preserves compactness
(for compact `X`, `Y`, closed `C`, continuous `r` and `0 ≤ δ`). -/
theorem lemma_21_4_2 [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] {δ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hC : IsClosed C)
    (hr : Continuous (fun q : X × Y => r q.1 q.2)) :
    Monotone (cg_B δ r C) ∧ ∀ W, IsCompact W → IsCompact (cg_B δ r C W) := by
  refine ⟨cg_B_mono δ r C, fun W hW => ?_⟩
  rw [cg_B_eq_image hδ0 hW]
  exact (cg_K_isCompact hC hr hW).image
    ((continuous_const.mul (hr.comp continuous_fst)).add (continuous_const.mul continuous_snd.fst))

/-- `V ⊆ B(V)` (Miao, p. 765, "by Lemma 21.4.1"): an SPE value is generated by the first-period
outcome and the continuation values `w(ξ, η) = Uᵍ(σ|_(ξ, η))`. -/
theorem cg_V_subset_B {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) : cg_V δ r C ⊆ cg_B δ r C (cg_V δ r C) := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨hcont, hC, hdev⟩ := (lemma_21_4_1 hδ0 hδ1 hM σ).1 hσ
  refine ⟨(σ []).1, (σ []).2, fun q => cg_U δ r (cg_cont σ [q]),
    ⟨hC, fun q => ⟨_, hcont q.1 q.2, rfl⟩, hdev⟩, ?_⟩
  exact cg_U_rec hδ0 hδ1 hM σ

/-- Pasting: play `q` first, then `τ (ξ, η)` after the first-period outcome `(ξ, η)`. -/
def cg_paste (q : X × Y) (τ : X × Y → CGProfile X Y) : CGProfile X Y
  | [] => q
  | p :: h => τ p h

/-- If `W ⊆ V` then `B(W) ⊆ V` (Lemma 21.4.1, "if" half). -/
theorem cg_B_subset_V {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {W : Set ℝ} (hW : W ⊆ cg_V δ r C) : cg_B δ r C W ⊆ cg_V δ r C := by
  rintro _ ⟨x, y, w, ⟨hC, hw, hIC⟩, rfl⟩
  choose τ hτ hτv using fun q => hW (hw q)
  have hc : ∀ q, cg_cont (cg_paste (x, y) τ) [q] = τ q := fun q => rfl
  refine ⟨cg_paste (x, y) τ, ?_, ?_⟩
  · rw [lemma_21_4_1 hδ0 hδ1 hM]
    refine ⟨fun ξ η => by rw [hc]; exact hτ _, hC, fun η => ?_⟩
    have e : cg_paste (x, y) τ [] = (x, y) := rfl
    rw [e, hc, hc, hτv, hτv]
    exact hIC η
  · rw [cg_U_rec hδ0 hδ1 hM]
    have e : cg_paste (x, y) τ [] = (x, y) := rfl
    rw [e, hc, hτv]

/-- A bounded self-generating set is contained in `V` (the first half of Lemma 21.4.3's proof:
the recursive strategy whose states are the values in `W`). -/
theorem cg_selfGenerating_subset_V {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {W : Set ℝ} (hWb : Bornology.IsBounded W)
    (hSG : cg_SelfGenerating δ r C W) : W ⊆ cg_V δ r C := by
  classical
  intro v0 hv0
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.1 hWb
  have hc : ∀ s, s ∈ W → ∃ x y w, cg_Admissible δ r C W x y w ∧
      s = (1 - δ) * r x y + δ * w (x, y) := fun s hs => hSG hs
  choose zx zy zw hadm hval using hc
  let zh : ℝ → X := fun s => if hs : s ∈ W then zx s hs else zx v0 hv0
  let zg : ℝ → Y := fun s => if hs : s ∈ W then zy s hs else zy v0 hv0
  let Vf : ℝ → X → Y → ℝ := fun s ξ η => if hs : s ∈ W then zw s hs (ξ, η) else zw v0 hv0 (ξ, η)
  have hzh : ∀ s (hs : s ∈ W), zh s = zx s hs := fun s hs => by simp [zh, hs]
  have hzg : ∀ s (hs : s ∈ W), zg s = zy s hs := fun s hs => by simp [zg, hs]
  have hVf : ∀ s (hs : s ∈ W) ξ η, Vf s ξ η = zw s hs (ξ, η) := fun s hs ξ η => by simp [Vf, hs]
  have hspe := cg_recursive_spe (C := C) (K := K) (S := W) (zh := zh) (zg := zg) (Vf := Vf)
    hδ0 hδ1 hM (fun s hs => by have := hK s hs; rwa [Real.norm_eq_abs] at this)
    (fun s hs ξ η => by rw [hVf s hs]; exact (hadm s hs).2.1 _)
    (fun s hs => by rw [hzh s hs, hzg s hs, hVf s hs]; exact (hval s hs).symm)
    (fun s hs => by rw [hzh s hs, hzg s hs]; exact (hadm s hs).1)
    (fun s hs y' => by
      rw [hzh s hs, hVf s hs]
      have := (hadm s hs).2.2 y'
      rw [← hval s hs] at this
      exact this) v0 hv0
  exact ⟨_, hspe.1, hspe.2⟩

/-- **Lemma 21.4.3** (self-generation, Miao, p. 764). If `W ⊆ ℝ` is bounded and self-generating,
then `B(W) ⊆ V`. -/
theorem lemma_21_4_3 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {W : Set ℝ} (hWb : Bornology.IsBounded W)
    (hSG : cg_SelfGenerating δ r C W) : cg_B δ r C W ⊆ cg_V δ r C :=
  cg_B_subset_V hδ0 hδ1 hM (cg_selfGenerating_subset_V hδ0 hδ1 hM hWb hSG)

/-- **Theorem 21.4.1** (Miao, p. 765), corrected. `V = B(V)`, `V` is bounded, and `V` contains
every bounded fixed point of `B`: it is the largest *bounded* fixed point. (Without
boundedness the claim fails: `cg_theorem_21_4_1_unbounded`.) -/
theorem theorem_21_4_1 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) :
    cg_V δ r C = cg_B δ r C (cg_V δ r C) ∧ Bornology.IsBounded (cg_V δ r C) ∧
      ∀ W, Bornology.IsBounded W → cg_B δ r C W = W → W ⊆ cg_V δ r C := by
  refine ⟨Set.Subset.antisymm (cg_V_subset_B hδ0 hδ1 hM) (cg_B_subset_V hδ0 hδ1 hM le_rfl),
    cg_V_isBounded hδ0 hδ1 hM, fun W hWb hfix => ?_⟩
  have hSG : cg_SelfGenerating δ r C W := hfix.symm.subset
  exact hfix.symm.subset.trans (lemma_21_4_3 hδ0 hδ1 hM hWb hSG)

/-- A value generated by `V ∪ {v}` is an SPE value. -/
theorem cg_mem_V_of_mem_B_insert {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {v : ℝ}
    (hv : v ∈ cg_B δ r C (insert v (cg_V δ r C))) : v ∈ cg_V δ r C := by
  have hb : Bornology.IsBounded (insert v (cg_V δ r C)) :=
    (cg_V_isBounded hδ0 hδ1 hM).insert v
  have hSG : cg_SelfGenerating δ r C (insert v (cg_V δ r C)) := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact cg_B_mono δ r C (Set.subset_insert _ _) (cg_V_subset_B hδ0 hδ1 hM hw)
  exact lemma_21_4_3 hδ0 hδ1 hM hb hSG hv

/-- Miao, p. 765, step 1 of the algorithm: if `a ≤ r ≤ b` on `C` (e.g. `a = min_C r`,
`b = max_C r`), then `V ⊆ W₀ = [a, b]` and `B(W₀) ⊆ W₀`. -/
theorem cg_aps_step1 {δ M a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hab : ∀ q ∈ C, a ≤ r q.1 q.2 ∧ r q.1 q.2 ≤ b) :
    cg_V δ r C ⊆ Set.Icc a b ∧ cg_B δ r C (Set.Icc a b) ⊆ Set.Icc a b := by
  refine ⟨cg_V_subset_Icc hδ0 hδ1 hM hab, ?_⟩
  rintro _ ⟨x, y, w, ⟨hC, hw, -⟩, rfl⟩
  obtain ⟨h1, h2⟩ := hab _ hC
  obtain ⟨h3, h4⟩ := hw (x, y)
  have h5 : 0 ≤ 1 - δ := by linarith
  constructor <;> nlinarith

/-- Miao, p. 765, step 2 of the algorithm: for `a ≤ b`, `B([a, b])` is the set of
`(1 − δ) r(x, y) + δ w₁` over `(x, y) ∈ C`, `w₁, w₂ ∈ [a, b]` with
`(1 − δ) r(x, y) + δ w₁ ≥ (1 − δ) r(x, y') + δ w₂` for all `y'` (the problem defining `w¹_min`). -/
theorem cg_aps_step2 {δ a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (v : ℝ) :
    v ∈ cg_B δ r C (Set.Icc a b) ↔ ∃ x y w₁ w₂, (x, y) ∈ C ∧ w₁ ∈ Set.Icc a b ∧
      w₂ ∈ Set.Icc a b ∧ (∀ y', (1 - δ) * r x y' + δ * w₂ ≤ (1 - δ) * r x y + δ * w₁) ∧
      v = (1 - δ) * r x y + δ * w₁ := by
  rw [cg_B_eq_image hδ0 isCompact_Icc]
  constructor
  · rintro ⟨⟨⟨x, y⟩, w₁, w₂⟩, ⟨hC, h1, h2, hIC⟩, rfl⟩
    exact ⟨x, y, w₁, w₂, hC, h1, h2, hIC, rfl⟩
  · rintro ⟨x, y, w₁, w₂, hC, h1, h2, hIC, rfl⟩
    exact ⟨⟨⟨x, y⟩, w₁, w₂⟩, ⟨hC, h1, h2, hIC⟩, rfl⟩

/-- Miao, p. 765, step 2 of the algorithm: `w¹_max = max B([a, b])` solves
`max_{(x, y) ∈ C} (1 − δ) r(x, y) + δ b` subject to
`(1 − δ) r(x, y) + δ b ≥ (1 − δ) r(x, y') + δ a` for all `y'` (with the bounds `b = w⁰_max`,
`a = w⁰_min` of `W₀` in the constraint). -/
theorem cg_aps_step2_max {δ a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hab : a ≤ b) (m : ℝ) :
    IsGreatest (cg_B δ r C (Set.Icc a b)) m ↔
      IsGreatest {v | ∃ x y, (x, y) ∈ C ∧
        (∀ y', (1 - δ) * r x y' + δ * a ≤ (1 - δ) * r x y + δ * b) ∧
        v = (1 - δ) * r x y + δ * b} m := by
  set S := {v | ∃ x y, (x, y) ∈ C ∧
    (∀ y', (1 - δ) * r x y' + δ * a ≤ (1 - δ) * r x y + δ * b) ∧ v = (1 - δ) * r x y + δ * b}
  have hST : S ⊆ cg_B δ r C (Set.Icc a b) := by
    rintro _ ⟨x, y, hC, hIC, rfl⟩
    exact (cg_aps_step2 hδ0 _).2 ⟨x, y, b, a, hC, ⟨hab, le_rfl⟩, ⟨le_rfl, hab⟩, hIC, rfl⟩
  have hTS : ∀ t ∈ cg_B δ r C (Set.Icc a b), ∃ s ∈ S, t ≤ s := by
    intro t ht
    obtain ⟨x, y, w₁, w₂, hC, h1, h2, hIC, rfl⟩ := (cg_aps_step2 hδ0 _).1 ht
    refine ⟨_, ⟨x, y, hC, fun y' => ?_, rfl⟩, ?_⟩
    · have := hIC y'
      have : δ * a ≤ δ * w₂ := mul_le_mul_of_nonneg_left h2.1 hδ0
      have : δ * w₁ ≤ δ * b := mul_le_mul_of_nonneg_left h1.2 hδ0
      linarith
    · have : δ * w₁ ≤ δ * b := mul_le_mul_of_nonneg_left h1.2 hδ0
      linarith
  constructor
  · rintro ⟨hm, hub⟩
    obtain ⟨s, hs, hms⟩ := hTS m hm
    have : s = m := le_antisymm (hub (hST hs)) hms
    exact ⟨this ▸ hs, fun s hs => hub (hST hs)⟩
  · rintro ⟨hm, hub⟩
    refine ⟨hST hm, fun t ht => ?_⟩
    obtain ⟨s, hs, hts⟩ := hTS t ht
    exact hts.trans (hub hs)

/-- Miao, pp. 765–766, step 3 of the algorithm. Starting from `W₀ = [a, b]` with `a ≤ r ≤ b` on
`C`, the iterates `W_j = B^j(W₀)` decrease, contain `V`, are compact, and converge to `V`:
`⋂_j W_j = V` (for compact Hausdorff `X`, `Y`, closed `C`, continuous `r`). -/
theorem cg_aps_step3 [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [CompactSpace Y] [T2Space X] [T2Space Y] {δ M a b : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hC : IsClosed C)
    (hr : Continuous (fun q : X × Y => r q.1 q.2))
    (hab : ∀ q ∈ C, a ≤ r q.1 q.2 ∧ r q.1 q.2 ≤ b) :
    (∀ j, (cg_B δ r C)^[j + 1] (Set.Icc a b) ⊆ (cg_B δ r C)^[j] (Set.Icc a b)) ∧
      (∀ j, cg_V δ r C ⊆ (cg_B δ r C)^[j] (Set.Icc a b)) ∧
      (∀ j, IsCompact ((cg_B δ r C)^[j] (Set.Icc a b))) ∧
      ⋂ j, (cg_B δ r C)^[j] (Set.Icc a b) = cg_V δ r C := by
  set W : ℕ → Set ℝ := fun j => (cg_B δ r C)^[j] (Set.Icc a b) with hWdef
  have hWs : ∀ j, W (j + 1) = cg_B δ r C (W j) := fun j => by
    simp only [hWdef, Function.iterate_succ_apply']
  obtain ⟨hV0, hB0⟩ := cg_aps_step1 hδ0 hδ1 hM hab
  have hdec : ∀ j, W (j + 1) ⊆ W j := by
    intro j
    induction j with
    | zero => rw [hWs]; exact hB0
    | succ j ih =>
      calc W (j + 1 + 1) = cg_B δ r C (W (j + 1)) := hWs _
        _ ⊆ cg_B δ r C (W j) := cg_B_mono δ r C ih
        _ = W (j + 1) := (hWs j).symm
  have hVW : ∀ j, cg_V δ r C ⊆ W j := by
    intro j
    induction j with
    | zero => exact hV0
    | succ j ih =>
      rw [hWs, (theorem_21_4_1 hδ0 hδ1 hM).1]
      exact cg_B_mono δ r C ih
  have hcpt : ∀ j, IsCompact (W j) := by
    intro j
    induction j with
    | zero => exact isCompact_Icc
    | succ j ih => rw [hWs]; exact (lemma_21_4_2 hδ0 hC hr).2 _ ih
  refine ⟨hdec, hVW, hcpt, ?_⟩
  set Winf := ⋂ j, W j
  have hWinf_cpt : IsCompact Winf :=
    (hcpt 0).of_isClosed_subset (isClosed_iInter fun j => (hcpt j).isClosed)
      (Set.iInter_subset _ 0)
  have hf : Continuous (fun q : (X × Y) × ℝ × ℝ => (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1) :=
    (continuous_const.mul (hr.comp continuous_fst)).add (continuous_const.mul continuous_snd.fst)
  have h1 : cg_B δ r C Winf ⊆ Winf := by
    intro v hv
    refine Set.mem_iInter.2 fun j => hdec j ?_
    rw [hWs]
    exact cg_B_mono δ r C (Set.iInter_subset _ j) hv
  have h2 : Winf ⊆ cg_B δ r C Winf := by
    intro v hv
    have hvj : ∀ j, v ∈ W (j + 1) := fun j => Set.mem_iInter.1 hv (j + 1)
    set L : ℕ → Set ((X × Y) × ℝ × ℝ) := fun j =>
      cg_K δ r C (W j) ∩ (fun q : (X × Y) × ℝ × ℝ => (1 - δ) * r q.1.1 q.1.2 + δ * q.2.1) ⁻¹'
        {v}
    have hLc : ∀ j, IsCompact (L j) := fun j =>
      (cg_K_isCompact hC hr (hcpt j)).inter_right (isClosed_singleton.preimage hf)
    have hne : (⋂ j, L j).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed L
        (fun j => Set.inter_subset_inter_left _ (cg_K_mono δ r C (hdec j)))
        (fun j => ?_) (hLc 0) (fun j => (hLc j).isClosed)
      have := hvj j
      rw [hWs, cg_B_eq_image hδ0 (hcpt j)] at this
      obtain ⟨q, hq, hqv⟩ := this
      exact ⟨q, hq, hqv⟩
    obtain ⟨q, hq⟩ := hne
    have hqj : ∀ j, q ∈ L j := Set.mem_iInter.1 hq
    rw [cg_B_eq_image hδ0 hWinf_cpt]
    refine ⟨q, ⟨(hqj 0).1.1, Set.mem_iInter.2 fun j => (hqj j).1.2.1,
      Set.mem_iInter.2 fun j => (hqj j).1.2.2.1, (hqj 0).1.2.2.2⟩, (hqj 0).2⟩
  have hfix : cg_B δ r C Winf = Winf := Set.Subset.antisymm h1 h2
  have hbdd : Bornology.IsBounded Winf := hWinf_cpt.isBounded
  exact Set.Subset.antisymm ((theorem_21_4_1 hδ0 hδ1 hM).2.2 _ hbdd hfix)
    (Set.subset_iInter hVW)

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The best and the worst SPE values

Miao, §21.4.4, pp. 766–769 (after Abreu 1988 and Stokey 1991), and Exercise 21.4.

* `cg_follow p τ`: follow the path `p`; after the first deviation from it (by anyone) switch to
  the profile `τ`, started afresh. `cg_follow_spe`: if `τ` is an SPE and no one-period
  government deviation from `p` beats `(1 − δ) r(x_t, y') + δ Uᵍ(τ)`, this is an SPE with
  path `p`.
* `proposition_21_4_1`, corrected: with `v_min` the least SPE value, `p` is an SPE path iff for
  all `t`, `(x_t, y_t) ∈ C` and `U_t ≥ (1 − δ) r(x_t, y') + δ v_min` for all `y'`. The book omits
  `(x_t, y_t) ∈ C`, without which the claim is false (`cg_proposition_21_4_1_counterexample`).
* `cg_selfEnf p`: the self-enforcing strategy (restart `p` after any deviation from the ongoing
  path); `cg_SelfEnforcing`. `proposition_21_4_2`, corrected: `p` is self-enforcing iff for all
  `t`, `(x_t, y_t) ∈ C` and `U_t ≥ (1 − δ) r(x_t, y') + δ U_1` for all `y' ≠ y_t`. As printed
  (all `y'`, no `C`) it is false (`cg_proposition_21_4_2_counterexample`): at `y' = y_t` the
  condition asks `U_{t+1} ≥ U_1`, which a self-enforcing path need not satisfy.
* `proposition_21_4_3`: the path of a worst SPE is self-enforcing. `ex_21_4` collects the three.
* The computation of `v_min` and `v_max` on pp. 767–768: `cg_vmin_eq` (if
  `c = max_{y'} r(x*, y')` at a competitive `(x*, y*)`, `c` is the lower bound of `cg_V_lower`,
  and the binding continuation `v₁` is in `V`, then `c = v_min`), `cg_v1_formula`, `cg_vmax`
  (the best SPE is self-rewarding: `v_max = max r(x, y)` over competitive `(x, y)` with
  `r(x, y) ≥ (1 − δ) r(x, y') + δ v_min`), and `cg_four_equations` (the four-equation system with
  `v₁ = v_max`: its solutions are SPE values).
* `cg_example_21_4_6_selfEnforcing`: the stick-and-carrot path `(x*, y*), (x^R, y^R), …` is
  self-enforcing (Miao, p. 771, "This equilibrium is self-enforcing").
-/

namespace Miao.DynamicGames

variable {X Y : Type*}

open Classical in
/-- Follow the path `p` from index `t`; after the first deviation from it switch to `τ`. -/
noncomputable def cg_follow (p : ℕ → X × Y) (τ : CGProfile X Y) : ℕ → CGProfile X Y
  | t, [] => p t
  | t, q :: h => if q = p t then cg_follow p τ (t + 1) h else τ h

open Classical in
theorem cg_follow_cont_single (p : ℕ → X × Y) (τ : CGProfile X Y) (t : ℕ) (q : X × Y) :
    cg_cont (cg_follow p τ t) [q] = if q = p t then cg_follow p τ (t + 1) else τ := by
  funext h
  by_cases hq : q = p t
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_follow]
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_follow, hq]

theorem cg_follow_cont (p : ℕ → X × Y) (τ : CGProfile X Y) (h : List (X × Y)) :
    ∀ t, (∃ t', cg_cont (cg_follow p τ t) h = cg_follow p τ t') ∨
      ∃ h', cg_cont (cg_follow p τ t) h = cg_cont τ h' := by
  induction h with
  | nil => exact fun t => Or.inl ⟨t, rfl⟩
  | cons q h ih =>
    intro t
    have e : cg_cont (cg_follow p τ t) (q :: h) = cg_cont (cg_cont (cg_follow p τ t) [q]) h := by
      rw [cg_cont_cont]; rfl
    rw [e, cg_follow_cont_single]
    by_cases hq : q = p t
    · simp only [hq, ↓reduceIte]
      exact ih (t + 1)
    · simp only [hq, ↓reduceIte]
      exact Or.inr ⟨h, rfl⟩

theorem cg_follow_path (p : ℕ → X × Y) (τ : CGProfile X Y) (n : ℕ) :
    ∀ t, cg_path (cg_follow p τ t) n = p (t + n) := by
  induction n with
  | zero => exact fun t => rfl
  | succ n ih =>
    intro t
    have e : cg_path (cg_follow p τ t) (n + 1) =
        cg_path (cg_cont (cg_follow p τ t) [p t]) n := rfl
    rw [e, cg_follow_cont_single]
    simp only [↓reduceIte]
    rw [ih, show t + 1 + n = t + (n + 1) by omega]

theorem cg_follow_U (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) (τ : CGProfile X Y) (t : ℕ) :
    cg_U δ r (cg_follow p τ t) = cg_Ut δ r p t := by
  unfold cg_U cg_Ut
  congr 1
  funext n
  exact cg_follow_path p τ n t

/-- Following a path with an SPE punishment: if `τ` is an SPE, `p` is competitive, and for all
`t` and `η ≠ y_t`, `(1 − δ) r(x_t, η) + δ Uᵍ(τ) ≤ U_t(p)`, then `cg_follow p τ 0` is an SPE with
path `p`. -/
theorem cg_follow_spe {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) {p : ℕ → X × Y} {τ : CGProfile X Y} (hτ : cg_IsSPE δ r C τ)
    (hp : ∀ t, p t ∈ C)
    (hdev : ∀ t η, η ≠ (p t).2 → (1 - δ) * r (p t).1 η + δ * cg_U δ r τ ≤ cg_Ut δ r p t) :
    cg_IsSPE δ r C (cg_follow p τ 0) ∧ cg_path (cg_follow p τ 0) = p := by
  refine ⟨?_, funext fun n => by rw [cg_follow_path, zero_add]⟩
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  intro h
  rcases cg_follow_cont p τ h 0 with ⟨t, ht⟩ | ⟨h', ht⟩
  · rw [ht]
    have e : cg_follow p τ t [] = p t := rfl
    refine ⟨by rw [e]; exact hp t, fun η => ?_⟩
    rw [e, cg_follow_cont_single, cg_follow_U]
    by_cases hη : η = (p t).2
    · have hq : ((p t).1, η) = p t := by rw [hη]
      simp only [hq, ↓reduceIte]
      rw [cg_follow_U, cg_Ut_succ hδ0 hδ1 hM p t, hη]
    · have hq : ((p t).1, η) ≠ p t := by
        intro hq; apply hη; rw [← hq]
      simp only [hq, ↓reduceIte]
      exact hdev t η hη
  · rw [ht]
    exact (cg_isSPE_iff_oneShot hδ0 hδ1 hM τ).1 hτ h'

/-- **Proposition 21.4.1** (Miao, p. 766), corrected. Let `v_min` be the least SPE value. A path
`(x, y)` is an SPE path iff for all `t`, `(x_t, y_t)` is a competitive equilibrium and
`U_t(x, y) ≥ (1 − δ) r(x_t, y') + δ v_min` for all `y' ∈ Y`. (The book omits `(x_t, y_t) ∈ C`;
see `cg_proposition_21_4_1_counterexample`.) -/
theorem proposition_21_4_1 {δ M vmin : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin)
    (p : ℕ → X × Y) :
    (∃ σ, cg_IsSPE δ r C σ ∧ cg_path σ = p) ↔
      ∀ t, p t ∈ C ∧ ∀ y', (1 - δ) * r (p t).1 y' + δ * vmin ≤ cg_Ut δ r p t := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩ t
    refine ⟨hσ.path_mem hδ0 hδ1 hM t, fun y' => ?_⟩
    set ρ := cg_cont σ (cg_prefix (cg_path σ) t)
    have hρ : cg_IsSPE δ r C ρ := hσ.cont hδ0 hδ1 hM _
    have hpath := cg_path_cont_prefix σ t
    have h0 : ρ [] = cg_path σ t := by
      have := congrFun hpath 0
      rw [Nat.add_zero] at this
      exact this
    have hU : cg_U δ r ρ = cg_Ut δ r (cg_path σ) t := by
      unfold cg_U cg_Ut
      rw [hpath]
    have hroot := (hρ.root hδ0 hδ1 hM).2 y'
    rw [h0, hU] at hroot
    have hmem : cg_U δ r (cg_cont ρ [((cg_path σ t).1, y')]) ∈ cg_V δ r C :=
      ⟨_, hρ.cont hδ0 hδ1 hM _, rfl⟩
    have := mul_le_mul_of_nonneg_left (hmin.2 hmem) hδ0
    linarith
  · intro hp
    obtain ⟨τ, hτ, hτv⟩ := hmin.1
    refine ⟨cg_follow p τ 0, cg_follow_spe hδ0 hδ1 hM hτ (fun t => (hp t).1) ?_⟩
    intro t η _
    rw [hτv]
    exact (hp t).2 η

open Classical in
/-- The self-enforcing strategy of a path `p` (Miao, p. 767), from index `t`: play `p`; if anyone
deviates from the ongoing path, restart `p` from its beginning. -/
noncomputable def cg_selfEnf (p : ℕ → X × Y) : ℕ → CGProfile X Y
  | t, [] => p t
  | t, q :: h => if q = p t then cg_selfEnf p (t + 1) h else cg_selfEnf p 0 h

/-- A path is self-enforcing if its self-enforcing strategy is an SPE (Miao, p. 767). -/
def cg_SelfEnforcing (δ : ℝ) (r : X → Y → ℝ) (C : Set (X × Y)) (p : ℕ → X × Y) : Prop :=
  cg_IsSPE δ r C (cg_selfEnf p 0)

open Classical in
theorem cg_selfEnf_cont_single (p : ℕ → X × Y) (t : ℕ) (q : X × Y) :
    cg_cont (cg_selfEnf p t) [q] = if q = p t then cg_selfEnf p (t + 1) else cg_selfEnf p 0 := by
  funext h
  by_cases hq : q = p t
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_selfEnf]
  · simp only [hq, ↓reduceIte]
    simp [cg_cont, cg_selfEnf, hq]

theorem cg_selfEnf_cont (p : ℕ → X × Y) (h : List (X × Y)) :
    ∀ t, ∃ t', cg_cont (cg_selfEnf p t) h = cg_selfEnf p t' := by
  induction h with
  | nil => exact fun t => ⟨t, rfl⟩
  | cons q h ih =>
    intro t
    have e : cg_cont (cg_selfEnf p t) (q :: h) = cg_cont (cg_cont (cg_selfEnf p t) [q]) h := by
      rw [cg_cont_cont]; rfl
    rw [e, cg_selfEnf_cont_single]
    by_cases hq : q = p t
    · simp only [hq, ↓reduceIte]
      exact ih (t + 1)
    · simp only [hq, ↓reduceIte]
      exact ih 0

theorem cg_selfEnf_path (p : ℕ → X × Y) (n : ℕ) :
    ∀ t, cg_path (cg_selfEnf p t) n = p (t + n) := by
  induction n with
  | zero => exact fun t => rfl
  | succ n ih =>
    intro t
    have e : cg_path (cg_selfEnf p t) (n + 1) = cg_path (cg_cont (cg_selfEnf p t) [p t]) n := rfl
    rw [e, cg_selfEnf_cont_single]
    simp only [↓reduceIte]
    rw [ih, show t + 1 + n = t + (n + 1) by omega]

theorem cg_selfEnf_U (δ : ℝ) (r : X → Y → ℝ) (p : ℕ → X × Y) (t : ℕ) :
    cg_U δ r (cg_selfEnf p t) = cg_Ut δ r p t := by
  unfold cg_U cg_Ut
  congr 1
  funext n
  exact cg_selfEnf_path p n t

theorem cg_selfEnf_prefix (p : ℕ → X × Y) (t : ℕ) :
    cg_cont (cg_selfEnf p 0) (cg_prefix p t) = cg_selfEnf p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [cg_prefix_succ, ← cg_cont_cont, ih, cg_selfEnf_cont_single]
    simp

/-- The path of the self-enforcing strategy of `p` is `p`. -/
theorem cg_selfEnf_path_zero (p : ℕ → X × Y) : cg_path (cg_selfEnf p 0) = p :=
  funext fun n => by rw [cg_selfEnf_path, zero_add]

/-- **Proposition 21.4.2** (Miao, p. 767), corrected. The path `(x, y)` is a self-enforcing SPE
path iff for all `t`, `(x_t, y_t) ∈ C` and `U_t(x, y) ≥ (1 − δ) r(x_t, y') + δ U_1(x, y)` for all
`y' ≠ y_t`. (The book quantifies over all `y'` and omits `(x_t, y_t) ∈ C`; see
`cg_proposition_21_4_2_counterexample`.) -/
theorem proposition_21_4_2 {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (p : ℕ → X × Y) :
    cg_SelfEnforcing δ r C p ↔ ∀ t, p t ∈ C ∧
      ∀ y', y' ≠ (p t).2 → (1 - δ) * r (p t).1 y' + δ * cg_Ut δ r p 0 ≤ cg_Ut δ r p t := by
  unfold cg_SelfEnforcing
  rw [cg_isSPE_iff_oneShot hδ0 hδ1 hM]
  constructor
  · intro hO t
    have h := hO (cg_prefix p t)
    rw [cg_selfEnf_prefix] at h
    refine ⟨h.1, fun y' hy' => ?_⟩
    have := h.2 y'
    have e : cg_selfEnf p t [] = p t := rfl
    have hq : ((p t).1, y') ≠ p t := by
      intro hq; apply hy'; rw [← hq]
    rw [e, cg_selfEnf_cont_single] at this
    simp only [hq, ↓reduceIte] at this
    rwa [cg_selfEnf_U, cg_selfEnf_U] at this
  · intro hp h
    obtain ⟨t, ht⟩ := cg_selfEnf_cont p h 0
    rw [ht]
    have e : cg_selfEnf p t [] = p t := rfl
    refine ⟨by rw [e]; exact (hp t).1, fun η => ?_⟩
    rw [e, cg_selfEnf_cont_single, cg_selfEnf_U]
    by_cases hη : η = (p t).2
    · have hq : ((p t).1, η) = p t := by rw [hη]
      simp only [hq, ↓reduceIte]
      rw [cg_selfEnf_U, cg_Ut_succ hδ0 hδ1 hM p t, hη]
    · have hq : ((p t).1, η) ≠ p t := by
        intro hq; apply hη; rw [← hq]
      simp only [hq, ↓reduceIte]
      rw [cg_selfEnf_U]
      exact (hp t).2 η hη

/-- **Proposition 21.4.3** (Miao, p. 767). The path of an SPE that attains the worst value
`v_min` is self-enforcing. -/
theorem proposition_21_4_3 {δ M vmin : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin)
    {σ : CGProfile X Y} (hσ : cg_IsSPE δ r C σ) (hv : cg_U δ r σ = vmin) :
    cg_SelfEnforcing δ r C (cg_path σ) := by
  have h1 := (proposition_21_4_1 hδ0 hδ1 hM hmin (cg_path σ)).1 ⟨σ, hσ, rfl⟩
  have h0 : cg_Ut δ r (cg_path σ) 0 = vmin := by rw [cg_Ut_zero]; exact hv
  rw [proposition_21_4_2 hδ0 hδ1 hM]
  intro t
  refine ⟨(h1 t).1, fun y' _ => ?_⟩
  rw [h0]
  exact (h1 t).2 y'

/-- **Exercise 21.4** (Miao, p. 771): the three propositions of §21.4.4 (in their corrected
form). -/
theorem ex_21_4 {δ M vmin : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin) :
    (∀ p : ℕ → X × Y, (∃ σ, cg_IsSPE δ r C σ ∧ cg_path σ = p) ↔
      ∀ t, p t ∈ C ∧ ∀ y', (1 - δ) * r (p t).1 y' + δ * vmin ≤ cg_Ut δ r p t) ∧
    (∀ p : ℕ → X × Y, cg_SelfEnforcing δ r C p ↔ ∀ t, p t ∈ C ∧
      ∀ y', y' ≠ (p t).2 → (1 - δ) * r (p t).1 y' + δ * cg_Ut δ r p 0 ≤ cg_Ut δ r p t) ∧
    (∀ σ, cg_IsSPE δ r C σ → cg_U δ r σ = vmin → cg_SelfEnforcing δ r C (cg_path σ)) :=
  ⟨proposition_21_4_1 hδ0 hδ1 hM hmin, proposition_21_4_2 hδ0 hδ1 hM,
    fun _ hσ hv => proposition_21_4_3 hδ0 hδ1 hM hmin hσ hv⟩

/-- Miao, p. 767: computing `v_min`. If `(x*, y*)` is competitive, `c ≥ r(x*, y')` for all `y'`
(`c = r(x*, H(x*))`), every competitive `(x, y)` has a deviation `y'` with `r(x, y') ≥ c`
(`c = min_y r(h(y), H(h(y)))`), and the continuation `v₁` that makes the constraint bind,
`(1 − δ) r(x*, y*) + δ v₁ = c`, is an SPE value, then `c` is the least SPE value. -/
theorem cg_vmin_eq {δ M c v₁ : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xs : X} {ys : Y} (hs : (xs, ys) ∈ C)
    (hcle : ∀ y', r xs y' ≤ c) (hlow : ∀ x y, (x, y) ∈ C → ∃ y', c ≤ r x y')
    (hv1 : v₁ ∈ cg_V δ r C) (heq : (1 - δ) * r xs ys + δ * v₁ = c) :
    IsLeast (cg_V δ r C) c := by
  classical
  refine ⟨cg_mem_V_of_mem_B_insert hδ0 hδ1 hM ?_, cg_V_lower hδ0 hδ1 hM hlow⟩
  refine ⟨xs, ys, fun q => if q = (xs, ys) then v₁ else c,
    ⟨hs, fun q => ?_, fun y' => ?_⟩, ?_⟩
  · dsimp only
    split_ifs
    · exact Or.inr hv1
    · exact Or.inl rfl
  · by_cases hy : y' = ys
    · subst hy; exact le_rfl
    · have hq : ((xs, y') : X × Y) ≠ (xs, ys) := by simp [hy]
      simp only [hq, ↓reduceIte]
      have := mul_le_mul_of_nonneg_left (hcle y') (by linarith : (0 : ℝ) ≤ 1 - δ)
      linarith
  · simp only [↓reduceIte]
    exact heq.symm

/-- Miao, p. 768: solving `(1 − δ) r(h(y_min), y_min) + δ v₁ = (1 − δ) r(h(y_min), H(h(y_min)))
+ δ v_min` for `v₁` gives `v₁ = ((1 − δ)/δ)[r(h, H(h)) − r(h, y_min)] + v_min`. -/
theorem cg_v1_formula {δ rmin rdev v₁ vmin : ℝ} (hδ : δ ≠ 0) :
    (1 - δ) * rmin + δ * v₁ = (1 - δ) * rdev + δ * vmin ↔
      v₁ = (1 - δ) / δ * (rdev - rmin) + vmin := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Miao, pp. 767–768: the best SPE is self-rewarding. Every competitive `(x, y)` with
`r(x, y) ≥ (1 − δ) r(x, y') + δ v_min` for all `y'` gives an SPE value `r(x, y)` (its
infinite repetition, with the worst SPE as punishment), and a greatest SPE value `v_max`, when
it exists, is the largest such `r(x, y)`. -/
theorem cg_vmax {δ M vmin vmax : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) (hmin : IsLeast (cg_V δ r C) vmin) :
    {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧ v = r x y} ⊆
        cg_V δ r C ∧
      (IsGreatest (cg_V δ r C) vmax → IsGreatest
        {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧ v = r x y}
        vmax) := by
  classical
  have hF : {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧
      v = r x y} ⊆ cg_V δ r C := by
    rintro _ ⟨x, y, hC, hIC, rfl⟩
    refine cg_mem_V_of_mem_B_insert hδ0 hδ1 hM ⟨x, y, fun q => if q = (x, y) then r x y
      else vmin, ⟨hC, fun q => ?_, fun y' => ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr hmin.1
    · by_cases hy : y' = y
      · subst hy; exact le_rfl
      · have hq : ((x, y') : X × Y) ≠ (x, y) := by simp [hy]
        simp only [hq, ↓reduceIte]
        have := hIC y'
        linarith
    · simp only [↓reduceIte]
      ring
  refine ⟨hF, fun hmax => ⟨?_, fun v hv => hmax.2 (hF hv)⟩⟩
  obtain ⟨σ, hσ, hσv⟩ := hmax.1
  have hrec := cg_U_rec hδ0 hδ1 hM σ
  have hcont : cg_U δ r (cg_cont σ [σ []]) ≤ vmax :=
    hmax.2 ⟨_, hσ.cont hδ0 hδ1 hM _, rfl⟩
  have h1 : 0 < 1 - δ := by linarith
  have hge : vmax ≤ r (σ []).1 (σ []).2 := by
    have := mul_le_mul_of_nonneg_left hcont hδ0
    nlinarith
  have hfeas : ∀ y', (1 - δ) * r (σ []).1 y' + δ * vmin ≤ r (σ []).1 (σ []).2 := by
    intro y'
    have hroot := (hσ.root hδ0 hδ1 hM).2 y'
    have hmem : cg_U δ r (cg_cont σ [((σ []).1, y')]) ∈ cg_V δ r C :=
      ⟨_, hσ.cont hδ0 hδ1 hM _, rfl⟩
    have := mul_le_mul_of_nonneg_left (hmin.2 hmem) hδ0
    linarith
  have hmemF : r (σ []).1 (σ []).2 ∈
      {v | ∃ x y, (x, y) ∈ C ∧ (∀ y', (1 - δ) * r x y' + δ * vmin ≤ r x y) ∧ v = r x y} :=
    ⟨_, _, (hσ []).1, hfeas, rfl⟩
  have hle : r (σ []).1 (σ []).2 ≤ vmax := hmax.2 (hF hmemF)
  have : r (σ []).1 (σ []).2 = vmax := le_antisymm hle hge
  rw [← this]
  exact hmemF

/-- Miao, p. 768: the four equations for `v_max, v_min, y_max, y_min` when the worst SPE is
rewarded with `v₁ = v_max`. If `(x_min, y_min)`, `(x_max, y_max)` are competitive,
`v_min ≥ r(x_min, y')` for all `y'` (`v_min = r(h(y_min), H(h(y_min)))`),
`v_max = ((1 − δ)/δ)[v_min − r(x_min, y_min)] + v_min`, `v_max = r(x_max, y_max)` and
`r(x_max, y_max) ≥ (1 − δ) r(x_max, y') + δ v_min` for all `y'` (the fourth equation with `H`
the best response), then `v_min` and `v_max` are SPE values. -/
theorem cg_four_equations {δ M vmin vmax : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xmin xmax : X} {ymin ymax : Y}
    (hCmin : (xmin, ymin) ∈ C) (hCmax : (xmax, ymax) ∈ C) (hH : ∀ y', r xmin y' ≤ vmin)
    (h2 : vmax = (1 - δ) / δ * (vmin - r xmin ymin) + vmin) (h3 : vmax = r xmax ymax)
    (h4 : ∀ y', (1 - δ) * r xmax y' + δ * vmin ≤ r xmax ymax) :
    vmin ∈ cg_V δ r C ∧ vmax ∈ cg_V δ r C := by
  classical
  have hδ : δ ≠ 0 := hδ0.ne'
  have hv : (1 - δ) * r xmin ymin + δ * vmax = vmin := by
    rw [h2]; field_simp; ring
  set W : Set ℝ := {vmin, vmax}
  have hWb : Bornology.IsBounded W := (Set.finite_singleton vmax).insert vmin |>.isBounded
  have hSG : cg_SelfGenerating δ r C W := by
    intro v hvW
    rcases hvW with rfl | rfl
    · refine ⟨xmin, ymin, fun q => if q = (xmin, ymin) then vmax else v, ⟨hCmin, fun q => ?_,
        fun y' => ?_⟩, ?_⟩
      · dsimp only
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · by_cases hy : y' = ymin
        · subst hy; exact le_rfl
        · have hq : ((xmin, y') : X × Y) ≠ (xmin, ymin) := by simp [hy]
          simp only [hq, ↓reduceIte]
          have := mul_le_mul_of_nonneg_left (hH y') (by linarith : (0 : ℝ) ≤ 1 - δ)
          linarith
      · simp only [↓reduceIte]
        exact hv.symm
    · refine ⟨xmax, ymax, fun q => if q = (xmax, ymax) then v else vmin, ⟨hCmax, fun q => ?_,
        fun y' => ?_⟩, ?_⟩
      · dsimp only
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · by_cases hy : y' = ymax
        · subst hy; exact le_rfl
        · have hq : ((xmax, y') : X × Y) ≠ (xmax, ymax) := by simp [hy]
          simp only [hq, ↓reduceIte]
          have := h4 y'
          rw [h3]
          linarith
      · simp only [↓reduceIte]
        rw [h3]
        ring
  have hWV := cg_selfGenerating_subset_V hδ0.le hδ1 hM hWb hSG
  exact ⟨hWV (Or.inl rfl), hWV (Or.inr rfl)⟩

/-- Miao, p. 771: "This equilibrium is self-enforcing." Under the conditions of
`example_21_4_6`, the stick-and-carrot path `(x*, y*), (x^R, y^R), (x^R, y^R), …` is
self-enforcing. -/
theorem cg_example_21_4_6_selfEnforcing {δ M : ℝ} {r : X → Y → ℝ} {C : Set (X × Y)}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : ∀ x y, |r x y| ≤ M) {xR xs : X} {yR ys : Y}
    (hR : (xR, yR) ∈ C) (hs : (xs, ys) ∈ C)
    (hstick : ∀ y', (1 - δ) * r xs y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤
      (1 - δ) * r xs ys + δ * r xR yR)
    (hcarrot : ∀ y', (1 - δ) * r xR y' + δ * ((1 - δ) * r xs ys + δ * r xR yR) ≤ r xR yR) :
    cg_SelfEnforcing δ r C (fun t => if t = 0 then (xs, ys) else (xR, yR)) := by
  set p : ℕ → X × Y := fun t => if t = 0 then (xs, ys) else (xR, yR) with hp
  have hconst : ∀ t, cg_Ut δ r p (t + 1) = r xR yR := by
    intro t
    unfold cg_Ut
    have : (fun s => p (t + 1 + s)) = fun _ => (xR, yR) := by
      funext s; simp [hp]
    rw [this, cg_pathValue_const hδ0 hδ1]
  have h0 : cg_Ut δ r p 0 = (1 - δ) * r xs ys + δ * r xR yR := by
    rw [cg_Ut_succ hδ0 hδ1 hM p 0, hconst]
    simp [hp]
  rw [proposition_21_4_2 hδ0 hδ1 hM]
  intro t
  rcases t with _ | t
  · refine ⟨by simpa [hp] using hs, fun y' _ => ?_⟩
    rw [h0]
    simpa [hp] using hstick y'
  · refine ⟨by simpa [hp] using hR, fun y' _ => ?_⟩
    rw [h0, hconst]
    simpa [hp] using hcarrot y'

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stokey's discrete monetary policy economy, repeated

Miao, Example 21.4.4 (p. 769) and Exercise 21.5 (p. 771): the economy of Example 21.4.2
(`cg_r422`, `cg_C422`; actions `0, 1, 2 = H, M, L`) repeated forever.

* `cg_stokey_V`: at `δ = 0.9` the SPE value set is exactly `V = [7, 9.7]` (lower bound from
  `cg_V_lower`, upper bound `max_C r = 9.7`, and the interval is the value set of an explicit
  recursive strategy). So `v_min = 7`, `v_max = 9.7`; `cg_stokey_vmin_formula` checks the
  book's recipe `v_min = r(h(y), H(h(y)))` with the binding continuation `v₁ = 70/9 ∈ V`.
* `example_21_4_4`: the path `q = (x_H, y_H), (x_M, y_M), (x_M, y_M), …` is self-enforcing at
  `δ = 0.9`, and the strategy "play `(x_L, y_L)` forever; after any deviation start `q`" is an
  SPE whose path is the repeated Ramsey outcome. The book's figures `72`, `71.8`, `94.8`, `97`
  are the values multiplied by `1/(1 − δ) = 10` (`example_21_4_4_arith`).
* `ex_21_5`: at `δ = 0.88` the path `q` is still self-enforcing but the strategy above is not
  an SPE; in fact no SPE has the repeated Ramsey outcome as its path.
* Counterexamples to statements of §§21.4.3–21.4.5 as printed, all at `δ = 0.9`:
  `cg_theorem_21_4_1_unbounded` (`B(ℝ) = ℝ ⊄ V`), `cg_proposition_21_4_1_counterexample`
  (the path `(x_L, y_M)` forever satisfies the inequality of Proposition 21.4.1 but is not
  competitive), `cg_definition_21_4_5_counterexample` (a recursive strategy satisfying
  (i)–(iii) at `v` that is not an SPE), `cg_example_21_4_5_counterexample` (the trigger strategy
  for the Ramsey outcome with `v^b = 9.7 > v^N = 8` is not an SPE) and
  `cg_example_21_4_6_counterexample` (a stick-and-carrot strategy satisfying the book's condition
  that is not an SPE).
-/

namespace Miao.DynamicGames

theorem cg_r422_abs_le (x y : Fin 3) : |cg_r422 x y| ≤ 30 := by
  fin_cases x <;> fin_cases y <;> norm_num [cg_r422, abs_le]

theorem cg_C422_mem {x y : Fin 3} : (x, y) ∈ cg_C422 ↔ x = y := Iff.rfl

/-- The action of the recursive strategy generating `[7, 9.7]` at `δ = 0.9`. -/
noncomputable def cg_stokeyZ (v : ℝ) : Fin 3 := if v ≤ 36 / 5 then 0 else if v ≤ 93 / 10
  then 1 else 2

/-- The on-path next state of the recursive strategy generating `[7, 9.7]` at `δ = 0.9`. -/
noncomputable def cg_stokeyNext (v : ℝ) : ℝ :=
  if v ≤ 36 / 5 then v * 10 / 9 else if v ≤ 93 / 10 then (v - 8 / 10) * 10 / 9
  else (v - 97 / 100) * 10 / 9

/-- The state map of the recursive strategy generating `[7, 9.7]` at `δ = 0.9`: the next state on
path, the worst value `7` after any deviation. -/
noncomputable def cg_stokeyV (v : ℝ) (x y : Fin 3) : ℝ :=
  if x = cg_stokeyZ v ∧ y = cg_stokeyZ v then cg_stokeyNext v else 7

/-- Every `v ∈ [7, 9.7]` is the value of an SPE at `δ = 0.9`: the recursive strategy
`cg_stokeyZ`, `cg_stokeyV`. -/
theorem cg_stokey_recursive_spe :
    ∀ v ∈ Set.Icc (7 : ℝ) (97 / 10),
      cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat cg_stokeyZ cg_stokeyZ cg_stokeyV v) ∧
      cg_U (9 / 10) cg_r422 (cg_recStrat cg_stokeyZ cg_stokeyZ cg_stokeyV v) = v := by
  refine cg_recursive_spe (K := 10) (by norm_num) (by norm_num) cg_r422_abs_le ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  · intro s hs ξ η
    obtain ⟨hs1, hs2⟩ := hs
    unfold cg_stokeyV
    split_ifs
    · unfold cg_stokeyNext
      split_ifs with h1 h2 <;> constructor <;> linarith
    · constructor <;> norm_num
  · intro s _
    simp only [cg_stokeyV, and_self, ↓reduceIte]
    unfold cg_stokeyZ cg_stokeyNext
    split_ifs <;> norm_num [cg_r422]
  · intro s _
    exact rfl
  · intro s hs y'
    obtain ⟨hs1, hs2⟩ := hs
    unfold cg_stokeyV
    by_cases h1 : s ≤ 36 / 5
    · have hz : cg_stokeyZ s = 0 := by simp [cg_stokeyZ, h1]
      have hn : cg_stokeyNext s = s * 10 / 9 := by simp [cg_stokeyNext, h1]
      rw [hz, hn]
      fin_cases y' <;> norm_num [cg_r422] <;> linarith
    · by_cases h2 : s ≤ 93 / 10
      · have hz : cg_stokeyZ s = 1 := by simp [cg_stokeyZ, h1, h2]
        have hn : cg_stokeyNext s = (s - 8 / 10) * 10 / 9 := by simp [cg_stokeyNext, h1, h2]
        rw [hz, hn]
        fin_cases y' <;> norm_num [cg_r422] <;> linarith
      · have hz : cg_stokeyZ s = 2 := by simp [cg_stokeyZ, h1, h2]
        have hn : cg_stokeyNext s = (s - 97 / 100) * 10 / 9 := by simp [cg_stokeyNext, h1, h2]
        rw [hz, hn]
        fin_cases y' <;> norm_num [cg_r422] <;> linarith

/-- In Example 21.4.2 every SPE value is at least `7 = r(x_H, H(x_H)) = min_y r(h(y), H(h(y)))`
(any discount factor). -/
theorem cg_stokey_V_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r422 cg_C422, 7 ≤ v := by
  refine cg_V_lower hδ0 hδ1 cg_r422_abs_le ?_
  intro x y hxy
  rw [cg_C422_mem] at hxy
  subst hxy
  refine ⟨1, ?_⟩
  fin_cases x <;> norm_num [cg_r422]

/-- In Example 21.4.2 every SPE value is at most the Ramsey value `9.7` (any discount factor). -/
theorem cg_stokey_V_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r422 cg_C422, v ≤ 97 / 10 := by
  intro v hv
  refine (cg_V_subset_Icc (a := 0) hδ0 hδ1 cg_r422_abs_le ?_ hv).2
  rintro ⟨x, y⟩ (hxy : x = y)
  subst hxy
  fin_cases x <;> norm_num [cg_r422]

/-- Example 21.4.2 repeated with `δ = 0.9`: the SPE value set is `V = [7, 9.7]`. -/
theorem cg_stokey_V : cg_V (9 / 10) cg_r422 cg_C422 = Set.Icc 7 (97 / 10) := by
  ext v
  constructor
  · intro hv
    exact ⟨cg_stokey_V_ge (by norm_num) (by norm_num) v hv,
      cg_stokey_V_le (by norm_num) (by norm_num) v hv⟩
  · intro hv
    exact ⟨_, (cg_stokey_recursive_spe v hv).1, (cg_stokey_recursive_spe v hv).2⟩

/-- At `δ = 0.9`, `v_min = 7` and `v_max = 9.7` in Example 21.4.2. -/
theorem cg_stokey_vmin_vmax :
    IsLeast (cg_V (9 / 10) cg_r422 cg_C422) 7 ∧ IsGreatest (cg_V (9 / 10) cg_r422 cg_C422) (97 / 10)
    := by
  rw [cg_stokey_V]
  exact ⟨isLeast_Icc (by norm_num), isGreatest_Icc (by norm_num)⟩

/-- Miao, p. 767, in Example 21.4.2 at `δ = 0.9`: `v_min = r(h(y_H), H(h(y_H))) = r(x_H, y_M) = 7`;
the binding continuation `v₁ = 70/9` (from `0.1 · 0 + 0.9 v₁ = 7`) lies in `V`, so the recipe
`cg_vmin_eq` applies. -/
theorem cg_stokey_vmin_formula : IsLeast (cg_V (9 / 10) cg_r422 cg_C422) 7 := by
  refine cg_vmin_eq (xs := 0) (ys := 0) (v₁ := 70 / 9) (by norm_num) (by norm_num) cg_r422_abs_le
    rfl ?_ ?_ ?_ ?_
  · intro y'; fin_cases y' <;> norm_num [cg_r422]
  · intro x y hxy
    rw [cg_C422_mem] at hxy
    subst hxy
    refine ⟨1, ?_⟩
    fin_cases x <;> norm_num [cg_r422]
  · rw [cg_stokey_V]; constructor <;> norm_num
  · norm_num [cg_r422]

/-- The path `(x_H, y_H), (x_M, y_M), (x_M, y_M), …` of Example 21.4.4. -/
def cg_stokeyPath : ℕ → Fin 3 × Fin 3 := fun t => if t = 0 then (0, 0) else (1, 1)

theorem cg_stokeyPath_Ut {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ t, cg_Ut δ cg_r422 cg_stokeyPath (t + 1) = 8) ∧ cg_Ut δ cg_r422 cg_stokeyPath 0 = δ * 8 := by
  have h1 : ∀ t, cg_Ut δ cg_r422 cg_stokeyPath (t + 1) = 8 := by
    intro t
    unfold cg_Ut
    have : (fun s => cg_stokeyPath (t + 1 + s)) = fun _ => (1, 1) := by
      funext s; simp [cg_stokeyPath]
    rw [this, cg_pathValue_const hδ0 hδ1]
    norm_num [cg_r422]
  refine ⟨h1, ?_⟩
  rw [cg_Ut_succ hδ0 hδ1 cg_r422_abs_le, h1]
  norm_num [cg_stokeyPath, cg_r422]

/-- The path `q` of Example 21.4.4 is self-enforcing whenever the first-period deviation to `y_M`
does not pay, `(1 − δ) · 7 + δ · 8δ ≤ 8δ` (i.e. `δ ≥ 7/8`). -/
theorem cg_stokeyPath_selfEnforcing {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : (1 - δ) * 7 + δ * (δ * 8) ≤ δ * 8) :
    cg_SelfEnforcing δ cg_r422 cg_C422 cg_stokeyPath := by
  obtain ⟨h1, h0⟩ := cg_stokeyPath_Ut hδ0 hδ1
  have hd1 : 0 ≤ 1 - δ := by linarith
  rw [proposition_21_4_2 hδ0 hδ1 cg_r422_abs_le]
  intro t
  rcases t with _ | t
  · refine ⟨rfl, fun y' hy' => ?_⟩
    rw [h0]
    fin_cases y'
    · exact absurd rfl hy'
    · norm_num [cg_stokeyPath, cg_r422]; linarith
    · norm_num [cg_stokeyPath, cg_r422]; nlinarith
  · refine ⟨rfl, fun y' _ => ?_⟩
    rw [h0, h1]
    have hδ8 : δ * (δ * 8) ≤ 8 := by nlinarith
    fin_cases y' <;> norm_num [cg_stokeyPath, cg_r422] <;> nlinarith

/-- The Ramsey path `(x_L, y_L)` forever. -/
def cg_ramseyPath422 : ℕ → Fin 3 × Fin 3 := fun _ => (2, 2)

/-- **Example 21.4.4** (Miao, p. 769). At `δ = 0.9`: (a) the path
`q = (x_H, y_H), (x_M, y_M), …` is self-enforcing, with value `0.9 · 8 = 7.2`; (b) the strategy
"play the Ramsey outcome `(x_L, y_L)`; after any deviation from this or any ongoing path,
start `q`" is an SPE whose path is the Ramsey outcome forever. -/
theorem example_21_4_4 :
    cg_SelfEnforcing (9 / 10) cg_r422 cg_C422 cg_stokeyPath ∧
      cg_Ut (9 / 10) cg_r422 cg_stokeyPath 0 = 36 / 5 ∧
      cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0)
        ∧ cg_path (cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0) = cg_ramseyPath422
    := by
  have hse := cg_stokeyPath_selfEnforcing (δ := 9 / 10) (by norm_num) (by norm_num) (by norm_num)
  have h0 := (cg_stokeyPath_Ut (δ := 9 / 10) (by norm_num) (by norm_num)).2
  refine ⟨hse, by rw [h0]; norm_num, ?_⟩
  refine cg_follow_spe (by norm_num) (by norm_num) cg_r422_abs_le hse (fun _ => rfl) ?_
  intro t η hη
  rw [cg_selfEnf_U, h0]
  have hc : cg_Ut (9 / 10) cg_r422 cg_ramseyPath422 t = 97 / 10 := by
    unfold cg_Ut cg_ramseyPath422
    rw [cg_pathValue_const (by norm_num) (by norm_num)]
    norm_num [cg_r422]
  rw [hc]
  simp only [cg_ramseyPath422] at hη ⊢
  fin_cases η
  · norm_num [cg_r422]
  · norm_num [cg_r422]
  · exact absurd rfl hη

/-- **Example 21.4.4** (Miao, p. 769), the book's arithmetic (values multiplied by
`1/(1 − δ) = 10`): `0 + 0.9 · 8/(1 − 0.9) = 72`, `7 + 0.9 · 72 = 71.8 < 72`,
`30 + 0.9 · 72 = 94.8 < 97 = 9.7/(1 − 0.9)`; normalised, `7.2`, `7.18`, `9.48`, `9.7`. -/
theorem example_21_4_4_arith :
    (0 : ℝ) + 0.9 * 8 / (1 - 0.9) = 72 ∧ (7 : ℝ) + 0.9 * 72 = 71.8 ∧ (71.8 : ℝ) < 72 ∧
      (30 : ℝ) + 0.9 * 72 = 94.8 ∧ (9.7 : ℝ) / (1 - 0.9) = 97 ∧ (94.8 : ℝ) < 97 ∧
      (1 - 0.9 : ℝ) * 7 + 0.9 * 7.2 = 7.18 ∧ (1 - 0.9 : ℝ) * 30 + 0.9 * 7.2 = 9.48 := by
  norm_num

/-- **Exercise 21.5** (Miao, p. 771). At `δ = 0.88`: the path `q` of Example 21.4.4 is still
self-enforcing, but the strategy of Example 21.4.4 no longer supports the Ramsey outcome (the
deviation to `y_M` pays `0.12 · 30 + 0.88 · 7.04 = 9.7952 > 9.7`); indeed no SPE has the
repeated Ramsey outcome as its path (every SPE value is `≥ 7` and
`0.12 · 30 + 0.88 · 7 = 9.76 > 9.7`). -/
theorem ex_21_5 :
    cg_SelfEnforcing (22 / 25) cg_r422 cg_C422 cg_stokeyPath ∧
      ¬ cg_IsSPE (22 / 25) cg_r422 cg_C422
        (cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0) ∧
      ¬ ∃ σ, cg_IsSPE (22 / 25) cg_r422 cg_C422 σ ∧ cg_path σ = cg_ramseyPath422 := by
  have hδ0 : (0 : ℝ) ≤ 22 / 25 := by norm_num
  have hδ1 : (22 / 25 : ℝ) < 1 := by norm_num
  have hc : ∀ σ : CGProfile (Fin 3) (Fin 3), cg_path σ = cg_ramseyPath422 →
      cg_U (22 / 25) cg_r422 σ = 97 / 10 := by
    intro σ hσ
    unfold cg_U
    rw [hσ]
    unfold cg_ramseyPath422
    rw [cg_pathValue_const hδ0 hδ1]
    norm_num [cg_r422]
  refine ⟨cg_stokeyPath_selfEnforcing hδ0 hδ1 (by norm_num), fun hspe => ?_, ?_⟩
  · have hroot := (hspe.root hδ0 hδ1 cg_r422_abs_le).2 1
    have hpath := (cg_follow_path cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0 0)
    have e : cg_follow cg_ramseyPath422 (cg_selfEnf cg_stokeyPath 0) 0 [] = (2, 2) := rfl
    rw [e, cg_follow_cont_single] at hroot
    have hne : ((2, 1) : Fin 3 × Fin 3) ≠ cg_ramseyPath422 0 := by
      simp [cg_ramseyPath422]
    simp only [hne, ↓reduceIte] at hroot
    rw [cg_selfEnf_U, (cg_stokeyPath_Ut hδ0 hδ1).2, cg_follow_U] at hroot
    have hc' : cg_Ut (22 / 25) cg_r422 cg_ramseyPath422 0 = 97 / 10 := by
      unfold cg_Ut cg_ramseyPath422
      rw [cg_pathValue_const hδ0 hδ1]
      norm_num [cg_r422]
    rw [hc'] at hroot
    norm_num [cg_r422] at hroot
  · rintro ⟨σ, hσ, hpath⟩
    have hroot := (hσ.root hδ0 hδ1 cg_r422_abs_le).2 1
    have h0 : σ [] = (2, 2) := by
      have := congrFun hpath 0
      exact this
    have hmem : cg_U (22 / 25) cg_r422 (cg_cont σ [((σ []).1, 1)]) ∈
        cg_V (22 / 25) cg_r422 cg_C422 := ⟨_, hσ.cont hδ0 hδ1 cg_r422_abs_le _, rfl⟩
    have hge := cg_stokey_V_ge hδ0 hδ1 _ hmem
    rw [hc σ hpath] at hroot
    rw [h0] at hroot hge
    norm_num [cg_r422] at hroot
    linarith

/-- Theorem 21.4.1 needs boundedness: in Example 21.4.2 at `δ = 0.9`, `B(ℝ) = ℝ` (any value is
generated by `(x_M, y_M)` with a suitable reward and a severe enough punishment), yet
`ℝ ⊄ V`. So `V` is not the largest fixed point of `B`, only the largest bounded one. -/
theorem cg_theorem_21_4_1_unbounded :
    cg_B (9 / 10) cg_r422 cg_C422 Set.univ = Set.univ ∧
      ¬ (Set.univ : Set ℝ) ⊆ cg_V (9 / 10) cg_r422 cg_C422 := by
  refine ⟨Set.eq_univ_of_forall fun v => ?_, fun h => ?_⟩
  · refine ⟨1, 1, fun q => if q = (1, 1) then (v - 8 / 10) * 10 / 9
      else (v - 8 / 10) * 10 / 9 - 100, ⟨rfl, fun _ => trivial, fun y' => ?_⟩, ?_⟩
    · fin_cases y' <;> norm_num [cg_r422] <;> linarith
    · norm_num [cg_r422]
  · have := cg_stokey_V_le (δ := 9 / 10) (by norm_num) (by norm_num) 10 (h trivial)
    norm_num at this

/-- Proposition 21.4.1 as printed (without `(x_t, y_t) ∈ C`) is false: in Example 21.4.2 at
`δ = 0.9`, where `v_min = 7`, the path `(x_L, y_M)` forever satisfies
`U_t ≥ (1 − δ) r(x_t, y') + δ v_min` for all `t`, `y'`, but it is not an SPE path. -/
theorem cg_proposition_21_4_1_counterexample :
    IsLeast (cg_V (9 / 10) cg_r422 cg_C422) 7 ∧
      (∀ t y', (1 - 9 / 10) * cg_r422 ((fun _ => ((2 : Fin 3), (1 : Fin 3))) t : Fin 3 × Fin 3).1 y'
        + 9 / 10 * 7 ≤ cg_Ut (9 / 10) cg_r422 (fun _ => ((2 : Fin 3), (1 : Fin 3))) t) ∧
      ¬ ∃ σ, cg_IsSPE (9 / 10) cg_r422 cg_C422 σ ∧
        cg_path σ = fun _ => ((2 : Fin 3), (1 : Fin 3)) := by
  refine ⟨cg_stokey_vmin_vmax.1, fun t y' => ?_, ?_⟩
  · have : cg_Ut (9 / 10) cg_r422 (fun _ => ((2 : Fin 3), (1 : Fin 3))) t = 30 := by
      unfold cg_Ut
      rw [cg_pathValue_const (by norm_num) (by norm_num)]
      norm_num [cg_r422]
    rw [this]
    fin_cases y' <;> norm_num [cg_r422]
  · rintro ⟨σ, hσ, hpath⟩
    have := hσ.path_mem (by norm_num) (by norm_num) cg_r422_abs_le 0
    rw [hpath] at this
    exact absurd (cg_C422_mem.1 this) (by decide)

/-- The household rule of the recursive strategy in `cg_definition_21_4_5_counterexample`. -/
noncomputable def cg_cexZh (s : ℝ) : Fin 3 := if s = 8 then 1 else 0

/-- The state map of the recursive strategy in `cg_definition_21_4_5_counterexample`: `8` after a
household outcome `x_M`, `0` otherwise. -/
noncomputable def cg_cexV (_s : ℝ) (x _y : Fin 3) : ℝ := if x = 1 then 8 else 0

/-- The SPE characterisation of recursive strategies (Miao, p. 770) as printed is false: in
Example 21.4.2 at `δ = 0.9`, the recursive strategy with `zʰ(8) = x_M`, `zʰ(v) = x_H` otherwise,
`zᵍ ≡ y_M`, `V(v, x, y) = 8` if `x = x_M` and `0` otherwise, satisfies `v = 8 ∈ V` and
(i)–(iii) at `v`, but it is not an SPE: after the history `(x_H, y_M)` the state is `0` and the
prescribed `(x_H, y_M)` is not a competitive equilibrium. -/
theorem cg_definition_21_4_5_counterexample :
    (8 : ℝ) ∈ cg_V (9 / 10) cg_r422 cg_C422 ∧ (cg_cexZh 8, (1 : Fin 3)) ∈ cg_C422 ∧
      (∀ y, cg_cexV 8 (cg_cexZh 8) y ∈ cg_V (9 / 10) cg_r422 cg_C422) ∧
      (8 : ℝ) = (1 - 9 / 10) * cg_r422 (cg_cexZh 8) 1 + 9 / 10 * cg_cexV 8 (cg_cexZh 8) 1 ∧
      (∀ y, (1 - 9 / 10) * cg_r422 (cg_cexZh 8) y + 9 / 10 * cg_cexV 8 (cg_cexZh 8) y ≤ 8) ∧
      ¬ cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat cg_cexZh (fun _ => 1) cg_cexV 8) := by
  have h8 : cg_cexZh 8 = 1 := by simp [cg_cexZh]
  have h8V : (8 : ℝ) ∈ cg_V (9 / 10) cg_r422 cg_C422 := by
    rw [cg_stokey_V]; constructor <;> norm_num
  refine ⟨h8V, by rw [h8]; rfl, fun y => ?_, ?_, fun y => ?_, fun hspe => ?_⟩
  · rw [h8]; simpa [cg_cexV] using h8V
  · rw [h8]; norm_num [cg_cexV, cg_r422]
  · rw [h8]; fin_cases y <;> norm_num [cg_cexV, cg_r422]
  · have := (hspe [((0 : Fin 3), (1 : Fin 3))]).1
    have e : cg_recStrat cg_cexZh (fun _ => 1) cg_cexV 8 [((0 : Fin 3), (1 : Fin 3))] =
        ((0 : Fin 3), (1 : Fin 3)) := by
      simp [cg_recStrat, cg_recState, cg_cexV, cg_cexZh]
    rw [e] at this
    exact absurd (cg_C422_mem.1 this) (by decide)

/-- Example 21.4.5 as printed is false: in Example 21.4.2 at `δ = 0.9`, the Ramsey value
`v^b = 9.7` exceeds the Nash value `v^N = 8`, but the trigger strategy supporting
`(x_L, y_L)` is not an SPE (deviating to `y_M` pays `0.1 · 30 + 0.9 · 8 = 10.2 > 9.7`). -/
theorem cg_example_21_4_5_counterexample :
    cg_r422 1 1 < cg_r422 2 2 ∧ cg_IsNash cg_C422 cg_r422 1 1 ∧
      ¬ cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat (cg_trigZh (cg_r422 2 2) 2 1)
        (cg_trigZg (cg_r422 2 2) 2 1) (cg_trigV (cg_r422 2 2) (cg_r422 1 1) 2 2) (cg_r422 2 2))
    := by
  have hδ0 : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hδ1 : (9 / 10 : ℝ) < 1 := by norm_num
  refine ⟨by norm_num [cg_r422], (example_21_4_2).2.2.1, fun hspe => ?_⟩
  have hval := cg_trigger_value (r := cg_r422) hδ0 hδ1 cg_r422_abs_le 2 1 2 1
  have hroot := (hspe.root hδ0 hδ1 cg_r422_abs_le).2 1
  have e : cg_recStrat (cg_trigZh (cg_r422 2 2) 2 1) (cg_trigZg (cg_r422 2 2) 2 1)
      (cg_trigV (cg_r422 2 2) (cg_r422 1 1) 2 2) (cg_r422 2 2) [] = ((2 : Fin 3), (2 : Fin 3)) := by
    simp [cg_recStrat, cg_recState, cg_trigZh, cg_trigZg]
  rw [e, cg_recStrat_cont_single] at hroot
  have hV : cg_trigV (cg_r422 2 2) (cg_r422 1 1) (2 : Fin 3) (2 : Fin 3) (cg_r422 2 2) 2 1 =
      cg_r422 1 1 := by
    simp [cg_trigV]
  dsimp only at hroot
  rw [hV, hval _ (Or.inr rfl), hval _ (Or.inl rfl)] at hroot
  norm_num [cg_r422] at hroot

/-- Example 21.4.6 as printed is incomplete: in Example 21.4.2 at `δ = 0.9`, with the stick
`(x_H, y_H)` and the carrot `(x_L, y_L)`, `ṽ = 0.1 · 0 + 0.9 · 9.7 = 8.73` satisfies the book's
condition `ṽ ≥ (1 − δ) r(x*, y') + δṽ` for all `y'`, but the stick-and-carrot strategy is not
an SPE: in the carrot phase deviating to `y_M` pays `0.1 · 30 + 0.9 · 8.73 = 10.857 > 9.7`. -/
theorem cg_example_21_4_6_counterexample :
    (∀ y', (1 - 9 / 10) * cg_r422 0 y' + 9 / 10 * ((1 - 9 / 10) * cg_r422 0 0 + 9 / 10 *
      cg_r422 2 2) ≤ (1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2) ∧
      ¬ cg_IsSPE (9 / 10) cg_r422 cg_C422 (cg_recStrat (cg_scZh (cg_r422 2 2) 2 0)
        (cg_scZg (cg_r422 2 2) 2 0)
        (cg_scV (cg_r422 2 2) ((1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2) 2 0 2 0)
        ((1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2)) := by
  have hδ0 : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hδ1 : (9 / 10 : ℝ) < 1 := by norm_num
  refine ⟨fun y' => by fin_cases y' <;> norm_num [cg_r422], fun hspe => ?_⟩
  have hval := cg_stickCarrot_value (r := cg_r422) hδ0 hδ1 cg_r422_abs_le 2 0 2 0
  set vR := cg_r422 2 2 with hvR
  set vt := (1 - 9 / 10) * cg_r422 0 0 + 9 / 10 * cg_r422 2 2 with hvt
  have hne : vt ≠ vR := by rw [hvt, hvR]; norm_num [cg_r422]
  have hc := hspe.cont hδ0 hδ1 cg_r422_abs_le [((0 : Fin 3), (0 : Fin 3))]
  have hV1 : cg_cont (cg_recStrat (cg_scZh vR 2 0) (cg_scZg vR 2 0) (cg_scV vR vt 2 0 2 0) vt)
      [((0 : Fin 3), (0 : Fin 3))] =
      cg_recStrat (cg_scZh vR 2 0) (cg_scZg vR 2 0) (cg_scV vR vt 2 0 2 0) vR := by
    rw [cg_recStrat_cont_single]
    congr 1
    simp [cg_scV, cg_scZh, cg_scZg, hne]
  rw [hV1] at hc
  have hroot := (hc.root hδ0 hδ1 cg_r422_abs_le).2 1
  have e : cg_recStrat (cg_scZh vR 2 0) (cg_scZg vR 2 0) (cg_scV vR vt 2 0 2 0) vR [] =
      ((2 : Fin 3), (2 : Fin 3)) := by
    simp [cg_recStrat, cg_recState, cg_scZh, cg_scZg]
  rw [e, cg_recStrat_cont_single] at hroot
  have hV2 : cg_scV vR vt (2 : Fin 3) 0 (2 : Fin 3) 0 vR 2 1 = vt := by
    simp [cg_scV, cg_scZh, cg_scZg]
  dsimp only at hroot
  rw [hV2, hval _ (Or.inr rfl), hval _ (Or.inl rfl), hvt, hvR] at hroot
  norm_num [cg_r422] at hroot

/-- The payoff of the two-action game used in `cg_proposition_21_4_2_counterexample`:
`r(T, T) = 1`, `r(F, F) = 0`, `r(x, y) = −10` off the diagonal. -/
noncomputable def cg_rBool (x y : Bool) : ℝ := if x = y then (if x then 1 else 0) else -10

/-- The competitive equilibria `(T, T)`, `(F, F)` of the two-action game. -/
def cg_CBool : Set (Bool × Bool) := {q | q.1 = q.2}

/-- The path `(T, T), (F, F), (F, F), …` of the two-action game. -/
def cg_pBool : ℕ → Bool × Bool := fun t => if t = 0 then (true, true) else (false, false)

theorem cg_rBool_abs_le (x y : Bool) : |cg_rBool x y| ≤ 10 := by
  cases x <;> cases y <;> norm_num [cg_rBool, abs_le]

/-- Proposition 21.4.2 as printed (`U_t ≥ (1 − δ) r(x_t, y') + δ U_1` for all `y'`, including
`y' = y_t`) is false: in the two-action game with `δ = 1/2`, the path
`(T, T), (F, F), (F, F), …` is self-enforcing (`U_1 = 1/2`, `U_t = 0` for `t ≥ 2`, and every
deviation earns `−10`), but at `t = 2`, `y' = y_2 = F` the printed inequality reads
`0 ≥ 1/2 · 0 + 1/2 · 1/2`. -/
theorem cg_proposition_21_4_2_counterexample :
    cg_SelfEnforcing (1 / 2) cg_rBool cg_CBool cg_pBool ∧
      ¬ ∀ t y', (1 - 1 / 2) * cg_rBool (cg_pBool t).1 y' + 1 / 2 * cg_Ut (1 / 2) cg_rBool cg_pBool 0
        ≤ cg_Ut (1 / 2) cg_rBool cg_pBool t := by
  have hδ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hδ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have h1 : ∀ t, cg_Ut (1 / 2) cg_rBool cg_pBool (t + 1) = 0 := by
    intro t
    unfold cg_Ut
    have : (fun s => cg_pBool (t + 1 + s)) = fun _ => (false, false) := by
      funext s; simp [cg_pBool]
    rw [this, cg_pathValue_const hδ0 hδ1]
    simp [cg_rBool]
  have h0 : cg_Ut (1 / 2) cg_rBool cg_pBool 0 = 1 / 2 := by
    rw [cg_Ut_succ hδ0 hδ1 cg_rBool_abs_le, h1]
    norm_num [cg_pBool, cg_rBool]
  refine ⟨?_, fun h => ?_⟩
  · rw [proposition_21_4_2 hδ0 hδ1 cg_rBool_abs_le]
    intro t
    rcases t with _ | t
    · refine ⟨rfl, fun y' hy' => ?_⟩
      rw [h0]
      cases y'
      · norm_num [cg_pBool, cg_rBool]
      · simp [cg_pBool] at hy'
    · refine ⟨rfl, fun y' hy' => ?_⟩
      rw [h0, h1]
      cases y'
      · simp [cg_pBool] at hy'
      · norm_num [cg_pBool, cg_rBool]
  · have := h 1 false
    rw [h0, h1 0] at this
    norm_num [cg_pBool, cg_rBool] at this

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The repeated Barro–Gordon economy

Miao, Example 21.4.3, pp. 763–764: the one-period economy of Example 21.4.1 repeated, with the
government's objective `(1 − δ) ∑ δ^{t-1} [λ(y_t − y_n) − π_t²/2]` and `y_t = y_n + a(π_t − π^e_t)`,
so `r(π^e, π) = λa(π − π^e) − π²/2`.

* `example_21_4_3_best_deviation`: the most profitable one-period deviation is `ε = λa`.
* `example_21_4_3_range`: the trigger-strategy condition
  `−π²/2 ≥ (1 − δ)[λa(ε − π) − ε²/2] + δ(−(λa)²/2)` for all `ε` holds iff
  `(1 − 2δ)λa ≤ π ≤ λa`; the inequality factors as `(π − λa)(π − (1 − 2δ)λa) ≤ 0`. This holds
  for every `δ ∈ [0, 1)`; the book states it for `0 < δ < 0.5`, where the lower end is positive.
  `example_21_4_3_mono`: the range grows with `δ`.
* `example_21_4_3_nash`, `example_21_4_3`: the SPE statements. The general theory of
  `CGRepeated` needs bounded payoffs (as for the compact action sets of §21.4.1), so here
  inflation rates and forecasts lie in `[0, K]` with `K ≥ λa`; then infinite repetition of the
  Nash outcome `π = π^e = λa` is an SPE, and every `π ∈ [(1 − 2δ)λa, λa] ∩ [0, K]` is supported by
  the trigger strategy (revert to `λa` forever after a deviation), an instance of
  `example_21_4_5`.
-/

namespace Miao.DynamicGames

/-- Miao, p. 763: `r(π^e, π) = λ(y − y_n) − π²/2` with `y = y_n + a(π − π^e)` equals
`λa(π − π^e) − π²/2`. -/
theorem cg_bgGov_eq (lam a yn infe infl : ℝ) :
    cg_bgGov lam a yn infe infl = lam * a * (infl - infe) - infl ^ 2 / 2 := by
  unfold cg_bgGov; ring

/-- **Example 21.4.3** (Miao, p. 763): the most profitable one-period deviation from `π` is
`ε = λa`. -/
theorem example_21_4_3_best_deviation (lam a infl ε : ℝ) :
    lam * a * (ε - infl) - ε ^ 2 / 2 ≤ lam * a * (lam * a - infl) - (lam * a) ^ 2 / 2 := by
  nlinarith [sq_nonneg (ε - lam * a)]

/-- **Example 21.4.3** (Miao, pp. 763–764): the trigger-strategy condition
`−π²/2 ≥ (1 − δ)[λa(ε − π) − ε²/2] + δ(−(λa)²/2)` for all `ε` holds iff
`(1 − 2δ)λa ≤ π ≤ λa` (for every `δ ∈ [0, 1)` and `λa ≥ 0`). -/
theorem example_21_4_3_range {lam a δ infl : ℝ} (hla : 0 ≤ lam * a) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ ε, (1 - δ) * (lam * a * (ε - infl) - ε ^ 2 / 2) + δ * (-(lam * a) ^ 2 / 2) ≤
      -infl ^ 2 / 2) ↔ (1 - 2 * δ) * (lam * a) ≤ infl ∧ infl ≤ lam * a := by
  set L := lam * a with hL
  have hdL : 0 ≤ δ * L := mul_nonneg hδ0 hla
  constructor
  · intro h
    have h1 := h L
    have hprod : (infl - L) * (infl - (1 - 2 * δ) * L) ≤ 0 := by nlinarith
    constructor
    · by_contra hc
      push Not at hc
      have : 0 < (L - infl) * ((1 - 2 * δ) * L - infl) :=
        mul_pos (by nlinarith) (by linarith)
      nlinarith
    · by_contra hc
      push Not at hc
      have : 0 < (infl - L) * (infl - (1 - 2 * δ) * L) :=
        mul_pos (by linarith) (by nlinarith)
      nlinarith
  · rintro ⟨h1, h2⟩ ε
    have hb := example_21_4_3_best_deviation lam a infl ε
    rw [← hL] at hb
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ 1 - δ)
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-- **Example 21.4.3** (Miao, p. 764): "the range is larger for a larger `δ`". -/
theorem example_21_4_3_mono {L δ δ' : ℝ} (hL : 0 ≤ L) (hδ : δ ≤ δ') :
    (1 - 2 * δ') * L ≤ (1 - 2 * δ) * L := by nlinarith

/-- The Barro–Gordon payoff `r(π^e, π) = λa(π − π^e) − π²/2` on the action set `[0, K]`. -/
noncomputable def cg_bgR (lam a K : ℝ) (x y : Set.Icc (0 : ℝ) K) : ℝ :=
  lam * a * ((y : ℝ) - x) - (y : ℝ) ^ 2 / 2

/-- The competitive equilibria `π^e = π` on `[0, K]`. -/
def cg_bgCK (K : ℝ) : Set (Set.Icc (0 : ℝ) K × Set.Icc (0 : ℝ) K) := {q | (q.1 : ℝ) = q.2}

theorem cg_bgR_abs_le {lam a K : ℝ} (hla : 0 ≤ lam * a) (x y : Set.Icc (0 : ℝ) K) :
    |cg_bgR lam a K x y| ≤ lam * a * K + K ^ 2 / 2 := by
  obtain ⟨x, hx0, hxK⟩ := x
  obtain ⟨y, hy0, hyK⟩ := y
  unfold cg_bgR
  dsimp only
  rw [abs_le]
  have h1 : lam * a * (y - x) ≤ lam * a * K := mul_le_mul_of_nonneg_left (by linarith) hla
  have h2 : -(lam * a * K) ≤ lam * a * (y - x) := by
    have := mul_le_mul_of_nonneg_left (by linarith : -K ≤ y - x) hla
    linarith
  have h3 : y ^ 2 ≤ K ^ 2 := by nlinarith
  constructor <;> nlinarith [sq_nonneg y]

/-- **Example 21.4.3** (Miao, p. 763): "infinite repetition of the one-period Nash equilibrium
is an SPE". On `[0, K]` with `K ≥ λa > 0`, repeating `π^e = π = λa` is an SPE with value
`−(λa)²/2`. -/
theorem example_21_4_3_nash {lam a K δ : ℝ} (hl : 0 < lam) (ha : 0 < a) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (N : Set.Icc (0 : ℝ) K) (hN : (N : ℝ) = lam * a) :
    cg_IsSPE δ (cg_bgR lam a K) (cg_bgCK K) (fun _ => (N, N)) ∧
      cg_U δ (cg_bgR lam a K) (fun _ => (N, N)) = -(lam * a) ^ 2 / 2 := by
  have hla : 0 ≤ lam * a := (mul_pos hl ha).le
  have h := cg_nash_repetition_spe (C := cg_bgCK K) hδ0 hδ1 (cg_bgR_abs_le hla) (xN := N)
    (yN := N) rfl (fun y' => by
      unfold cg_bgR
      rw [hN]
      nlinarith [sq_nonneg ((y' : ℝ) - lam * a)])
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold cg_bgR
  rw [hN]
  ring

/-- **Example 21.4.3** (Miao, pp. 763–764). On `[0, K]` with `K ≥ λa > 0` and `δ ∈ [0, 1)`, every
`π ∈ [0, K]` with `(1 − 2δ)λa ≤ π ≤ λa` is supported by the trigger strategy (play
`π^e = π` while no one has deviated, revert to the Nash outcome `λa` forever after a deviation):
it is an SPE with value `−π²/2`. -/
theorem example_21_4_3 {lam a K δ : ℝ} (hl : 0 < lam) (ha : 0 < a) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (N : Set.Icc (0 : ℝ) K) (hN : (N : ℝ) = lam * a) (infl : Set.Icc (0 : ℝ) K)
    (h1 : (1 - 2 * δ) * (lam * a) ≤ infl) (h2 : (infl : ℝ) ≤ lam * a) :
    cg_IsSPE δ (cg_bgR lam a K) (cg_bgCK K)
        (cg_recStrat (cg_trigZh (cg_bgR lam a K infl infl) infl N)
          (cg_trigZg (cg_bgR lam a K infl infl) infl N)
          (cg_trigV (cg_bgR lam a K infl infl) (cg_bgR lam a K N N) infl infl)
          (cg_bgR lam a K infl infl)) ∧
      cg_U δ (cg_bgR lam a K)
        (cg_recStrat (cg_trigZh (cg_bgR lam a K infl infl) infl N)
          (cg_trigZg (cg_bgR lam a K infl infl) infl N)
          (cg_trigV (cg_bgR lam a K infl infl) (cg_bgR lam a K N N) infl infl)
          (cg_bgR lam a K infl infl)) = -(infl : ℝ) ^ 2 / 2 := by
  have hla : 0 ≤ lam * a := (mul_pos hl ha).le
  have hrange := (example_21_4_3_range (infl := (infl : ℝ)) hla hδ0 hδ1).2 ⟨h1, h2⟩
  have h := example_21_4_5 (C := cg_bgCK K) hδ0 hδ1 (cg_bgR_abs_le hla) (xb := infl) (yb := infl)
    (xN := N) (yN := N) rfl rfl (fun y' => by
      unfold cg_bgR
      rw [hN]
      nlinarith [sq_nonneg ((y' : ℝ) - lam * a)]) (fun y' => by
      have := hrange y'
      unfold cg_bgR
      rw [hN]
      nlinarith)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  unfold cg_bgR
  ring

end Miao.DynamicGames

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 21.6: a two-action credible-policy economy

Miao, Exercise 21.6 (c)–(f), pp. 771–772, for the economy `cg_r216`, `cg_C216` of
`CGOnePeriod` (`0, 1 = L, H`; competitive equilibria `(x_L, y_L)` and `(x_H, y_H)`; no
one-period Nash equilibrium, so Nash reversion is unavailable and punishments must come from
the worst SPE).

* `cg_ex216_V`: for `5/8 ≤ δ < 1` the SPE value set is `V = [1, 10]`; it is the value set of an
  explicit recursive strategy (`(x_L, y_L)` with reward `v/δ` below the threshold `15 − 14δ`,
  `(x_H, y_H)` with reward `(v − 10(1 − δ))/δ` above it, and the worst value `1` after any
  deviation).
* `ex_21_6_c`: the worst SPE value is `1 = min(max_y r(x_L, y), max_y r(x_H, y))`; every SPE
  attaining it starts with `(x_L, y_L)` and continues with value `1/δ`; the recursive strategy
  from the state `1` is such an SPE, its outcome path given by `definition_21_4_5`.
* `ex_21_6_d`: at `δ = 0.9` infinite repetition of the Ramsey outcome is an SPE path: play
  `(x_H, y_H)`, and after a deviation switch to the worst SPE (value `1`); the deviation pays
  `0.1 · 15 + 0.9 · 1 = 2.4 < 10`.
* `ex_21_6_e`: the best SPE value is `10` (for `5/8 ≤ δ < 1`).
* `ex_21_6_f`: if repetition of the Ramsey outcome is an SPE path then `δ > 5/14`, and it is one
  for every `δ ∈ [1/2, 1)` (stick-and-carrot between `10δ` and `10`). The bound `5/14` is what
  the deviation condition `10 ≥ 15(1 − δ) + δ v_min` gives with `v_min = 1`, but at `δ = 5/14`
  the value `1` is not an SPE value, so the threshold is not attained. Not formalised: the exact
  infimum of the set of such `δ` (it lies in `(5/14, 1/2]`).
-/

namespace Miao.DynamicGames

theorem cg_r216_abs_le (x y : Fin 2) : |cg_r216 x y| ≤ 15 := by
  fin_cases x <;> fin_cases y <;> norm_num [cg_r216, abs_le]

theorem cg_C216_mem {x y : Fin 2} : (x, y) ∈ cg_C216 ↔ x = y := Iff.rfl

/-- Every SPE value of Exercise 21.6 is at least `1` (any `δ ∈ [0, 1)`). -/
theorem cg_ex216_V_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r216 cg_C216, 1 ≤ v := by
  refine cg_V_lower hδ0 hδ1 cg_r216_abs_le ?_
  intro x y hxy
  rw [cg_C216_mem] at hxy
  subst hxy
  fin_cases x
  · exact ⟨1, by norm_num [cg_r216]⟩
  · exact ⟨0, by norm_num [cg_r216]⟩

/-- Every SPE value of Exercise 21.6 is at most the Ramsey value `10` (any `δ ∈ [0, 1)`). -/
theorem cg_ex216_V_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ cg_V δ cg_r216 cg_C216, v ≤ 10 := by
  intro v hv
  refine (cg_V_subset_Icc (a := 0) hδ0 hδ1 cg_r216_abs_le ?_ hv).2
  rintro ⟨x, y⟩ (hxy : x = y)
  subst hxy
  fin_cases x <;> norm_num [cg_r216]

/-- The action of the recursive strategy generating `[1, 10]`. -/
noncomputable def cg_ex216Z (δ v : ℝ) : Fin 2 := if v < 15 - 14 * δ then 0 else 1

/-- The on-path next state of the recursive strategy generating `[1, 10]`. -/
noncomputable def cg_ex216Next (δ v : ℝ) : ℝ :=
  if v < 15 - 14 * δ then v / δ else (v - (1 - δ) * 10) / δ

/-- The state map of the recursive strategy generating `[1, 10]`: the next state on path, the
worst value `1` after any deviation. -/
noncomputable def cg_ex216V (δ v : ℝ) (x y : Fin 2) : ℝ :=
  if x = cg_ex216Z δ v ∧ y = cg_ex216Z δ v then cg_ex216Next δ v else 1

/-- For `5/8 ≤ δ < 1`, every `v ∈ [1, 10]` is the value of an SPE of Exercise 21.6: the
recursive strategy `cg_ex216Z`, `cg_ex216V`. -/
theorem cg_ex216_recursive_spe {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    ∀ v ∈ Set.Icc (1 : ℝ) 10,
      cg_IsSPE δ cg_r216 cg_C216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) v) ∧
      cg_U δ cg_r216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) v) = v := by
  have hδ0 : 0 < δ := by linarith
  have hpk : ∀ s ∈ Set.Icc (1 : ℝ) 10, (1 - δ) * cg_r216 (cg_ex216Z δ s) (cg_ex216Z δ s) +
      δ * cg_ex216V δ s (cg_ex216Z δ s) (cg_ex216Z δ s) = s := by
    intro s _
    simp only [cg_ex216V, and_self, ↓reduceIte]
    unfold cg_ex216Z cg_ex216Next
    split_ifs
    · norm_num [cg_r216]; field_simp
    · norm_num [cg_r216]; field_simp; ring
  refine cg_recursive_spe (K := 10) hδ0.le hδ1 cg_r216_abs_le ?_ ?_ hpk ?_ ?_
  · intro s hs
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  · intro s hs ξ η
    obtain ⟨hs1, hs2⟩ := hs
    unfold cg_ex216V
    split_ifs
    · unfold cg_ex216Next
      split_ifs with h1
      · constructor
        · rw [le_div_iff₀ hδ0]; linarith
        · rw [div_le_iff₀ hδ0]; linarith
      · push Not at h1
        constructor
        · rw [le_div_iff₀ hδ0]; linarith
        · rw [div_le_iff₀ hδ0]; linarith
    · constructor <;> norm_num
  · intro s _
    exact rfl
  · intro s hs y'
    obtain ⟨hs1, hs2⟩ := hs
    by_cases hy : y' = cg_ex216Z δ s
    · rw [hy]
      exact le_of_eq (hpk s ⟨hs1, hs2⟩)
    · have hV : cg_ex216V δ s (cg_ex216Z δ s) y' = 1 := by simp [cg_ex216V, hy]
      rw [hV]
      by_cases h1 : s < 15 - 14 * δ
      · have hz : cg_ex216Z δ s = 0 := by simp [cg_ex216Z, h1]
        rw [hz] at hy ⊢
        fin_cases y'
        · exact absurd rfl hy
        · norm_num [cg_r216]; linarith
      · have hz : cg_ex216Z δ s = 1 := by simp [cg_ex216Z, h1]
        rw [hz] at hy ⊢
        push Not at h1
        fin_cases y'
        · norm_num [cg_r216]; linarith
        · exact absurd rfl hy

/-- For `5/8 ≤ δ < 1`, the SPE value set of Exercise 21.6 is `V = [1, 10]`. -/
theorem cg_ex216_V {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    cg_V δ cg_r216 cg_C216 = Set.Icc 1 10 := by
  have hδ0 : 0 ≤ δ := by linarith
  ext v
  constructor
  · intro hv
    exact ⟨cg_ex216_V_ge hδ0 hδ1 v hv, cg_ex216_V_le hδ0 hδ1 v hv⟩
  · intro hv
    exact ⟨_, (cg_ex216_recursive_spe hδ hδ1 v hv).1, (cg_ex216_recursive_spe hδ hδ1 v hv).2⟩

/-- **Exercise 21.6 (c)** (Miao, p. 772), for `5/8 ≤ δ < 1` (which includes the `δ = 0.9` of
part (d)). The worst SPE value is `1`. Every SPE attaining it starts with `(x_L, y_L)` and
continues with value `1/δ`. The recursive strategy from the state `1` attains it; its outcome
path is `(z(v_t), z(v_t))` with `v_1 = 1`, `v_2 = 1/δ` and `v_{t+1}` the on-path next state
(`definition_21_4_5`). -/
theorem ex_21_6_c {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    IsLeast (cg_V δ cg_r216 cg_C216) 1 ∧
      (∀ σ, cg_IsSPE δ cg_r216 cg_C216 σ → cg_U δ cg_r216 σ = 1 →
        σ [] = (0, 0) ∧ cg_U δ cg_r216 (cg_cont σ [σ []]) = 1 / δ) ∧
      cg_IsSPE δ cg_r216 cg_C216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) ∧
      cg_U δ cg_r216 (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) = 1 ∧
      cg_path (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) 0 = (0, 0) ∧
      cg_recSeq (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1 1 = 1 / δ := by
  have hδ0 : 0 < δ := by linarith
  have h1 : (1 : ℝ) < 15 - 14 * δ := by linarith
  have hz1 : cg_ex216Z δ 1 = 0 := by simp [cg_ex216Z, h1]
  refine ⟨?_, fun σ hσ hv => ?_, (cg_ex216_recursive_spe hδ hδ1 1 ⟨le_rfl, by norm_num⟩).1,
    (cg_ex216_recursive_spe hδ hδ1 1 ⟨le_rfl, by norm_num⟩).2, ?_, ?_⟩
  · rw [cg_ex216_V hδ hδ1]; exact isLeast_Icc (by norm_num)
  · have hrec := cg_U_rec hδ0.le hδ1 cg_r216_abs_le σ
    have hroot := (hσ.root hδ0.le hδ1 cg_r216_abs_le).2
    have hC : σ [] ∈ cg_C216 := (hσ []).1
    have hmem : ∀ q, cg_U δ cg_r216 (cg_cont σ [q]) ∈ cg_V δ cg_r216 cg_C216 :=
      fun q => ⟨_, hσ.cont hδ0.le hδ1 cg_r216_abs_le _, rfl⟩
    rcases h : σ [] with ⟨x, y⟩
    rw [h] at hC hrec hroot
    rw [cg_C216_mem] at hC
    subst hC
    obtain rfl | rfl : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    · refine ⟨rfl, ?_⟩
      rw [hv] at hrec
      norm_num [cg_r216] at hrec
      field_simp
      linarith
    · exfalso
      have := hroot 0
      have hge := cg_ex216_V_ge hδ0.le hδ1 _ (hmem ((1 : Fin 2), (0 : Fin 2)))
      rw [hv] at this
      norm_num [cg_r216] at this
      nlinarith
  · rw [(definition_21_4_5 _ _ _ 1 0).1]
    simp [cg_recSeq, hz1]
  · simp only [cg_recSeq, hz1, cg_ex216V, and_self, ↓reduceIte, cg_ex216Next, h1]

/-- The Ramsey outcome `(x_H, y_H)` forever. -/
def cg_ramseyPath216 : ℕ → Fin 2 × Fin 2 := fun _ => (1, 1)

theorem cg_ramseyPath216_Ut {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (t : ℕ) :
    cg_Ut δ cg_r216 cg_ramseyPath216 t = 10 := by
  unfold cg_Ut cg_ramseyPath216
  rw [cg_pathValue_const hδ0 hδ1]
  norm_num [cg_r216]

/-- For `5/8 ≤ δ < 1`, "play `(x_H, y_H)`; after any deviation switch to the worst SPE" is an
SPE whose path is the repeated Ramsey outcome. -/
theorem cg_ex216_ramsey_spe {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    cg_IsSPE δ cg_r216 cg_C216 (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) 0) ∧
      cg_path (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z δ) (cg_ex216Z δ) (cg_ex216V δ) 1) 0) = cg_ramseyPath216 := by
  have hδ0 : 0 ≤ δ := by linarith
  have hw := cg_ex216_recursive_spe hδ hδ1 1 ⟨le_rfl, by norm_num⟩
  refine cg_follow_spe hδ0 hδ1 cg_r216_abs_le hw.1 (fun _ => rfl) ?_
  intro t η hη
  rw [hw.2, cg_ramseyPath216_Ut hδ0 hδ1]
  simp only [cg_ramseyPath216] at hη ⊢
  fin_cases η
  · norm_num [cg_r216]; linarith
  · exact absurd rfl hη

/-- **Exercise 21.6 (d)** (Miao, p. 772). At `δ = 0.9` infinite repetition of the Ramsey outcome
is sustainable as an SPE: play `(x_H, y_H)`; after any deviation switch to the worst SPE (value
`1`); the deviation pays `0.1 · 15 + 0.9 · 1 = 2.4 < 10`. -/
theorem ex_21_6_d :
    cg_IsSPE (9 / 10) cg_r216 cg_C216 (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z (9 / 10)) (cg_ex216Z (9 / 10)) (cg_ex216V (9 / 10)) 1) 0) ∧
      cg_path (cg_follow cg_ramseyPath216
        (cg_recStrat (cg_ex216Z (9 / 10)) (cg_ex216Z (9 / 10)) (cg_ex216V (9 / 10)) 1) 0) =
        cg_ramseyPath216 ∧
      (1 - 9 / 10 : ℝ) * cg_r216 1 0 + 9 / 10 * 1 = 12 / 5 :=
  ⟨(cg_ex216_ramsey_spe (by norm_num) (by norm_num)).1,
    (cg_ex216_ramsey_spe (by norm_num) (by norm_num)).2, by norm_num [cg_r216]⟩

/-- **Exercise 21.6 (e)** (Miao, p. 772): the best SPE value is the Ramsey value `10` (for
`5/8 ≤ δ < 1`). -/
theorem ex_21_6_e {δ : ℝ} (hδ : 5 / 8 ≤ δ) (hδ1 : δ < 1) :
    IsGreatest (cg_V δ cg_r216 cg_C216) 10 := by
  rw [cg_ex216_V hδ hδ1]; exact isGreatest_Icc (by norm_num)

/-- At `δ = 5/14`, an SPE value below `10` is generated by `(x_L, y_L)` and the continuation
value `14v/5`. -/
theorem cg_ex216_step {v : ℝ} (hv : v ∈ cg_V (5 / 14) cg_r216 cg_C216) (hv10 : v < 10) :
    14 / 5 * v ∈ cg_V (5 / 14) cg_r216 cg_C216 := by
  have hδ0 : (0 : ℝ) ≤ 5 / 14 := by norm_num
  have hδ1 : (5 / 14 : ℝ) < 1 := by norm_num
  obtain ⟨x, y, w, ⟨hC, hw, hIC⟩, hvw⟩ := cg_V_subset_B hδ0 hδ1 cg_r216_abs_le hv
  rw [cg_C216_mem] at hC
  subst hC
  fin_cases x
  · have : 14 / 5 * v = w (0, 0) := by
      norm_num [cg_r216] at hvw
      linarith
    rw [this]
    exact hw _
  · exfalso
    have h1 := hIC 0
    have h2 := cg_ex216_V_ge hδ0 hδ1 _ (hw ((1 : Fin 2), (0 : Fin 2)))
    rw [← hvw] at h1
    norm_num [cg_r216] at h1
    linarith

/-- The stick-and-carrot recursive strategy on `{10δ, 10}` of Exercise 21.6 (f). -/
noncomputable def cg_ex216Z2 (v : ℝ) : Fin 2 := if v = 10 then 1 else 0

/-- Its state map: `10` after the prescribed pair, `10δ` otherwise. -/
noncomputable def cg_ex216V2 (δ v : ℝ) (x y : Fin 2) : ℝ :=
  if x = cg_ex216Z2 v ∧ y = cg_ex216Z2 v then 10 else 10 * δ

/-- **Exercise 21.6 (f)** (Miao, p. 772). If infinite repetition of the Ramsey outcome is an SPE
path then `δ > 5/14`; for every `δ ∈ [1/2, 1)` it is one (supported by the stick-and-carrot
strategy that punishes a deviation with one period of `(x_L, y_L)`, value `10δ`). -/
theorem ex_21_6_f :
    (∀ δ : ℝ, 0 ≤ δ → δ < 1 →
      (∃ σ, cg_IsSPE δ cg_r216 cg_C216 σ ∧ cg_path σ = cg_ramseyPath216) → 5 / 14 < δ) ∧
    (∀ δ : ℝ, 1 / 2 ≤ δ → δ < 1 →
      cg_IsSPE δ cg_r216 cg_C216 (cg_recStrat cg_ex216Z2 cg_ex216Z2 (cg_ex216V2 δ) 10) ∧
      cg_path (cg_recStrat cg_ex216Z2 cg_ex216Z2 (cg_ex216V2 δ) 10) = cg_ramseyPath216) := by
  constructor
  · rintro δ hδ0 hδ1 ⟨σ, hσ, hpath⟩
    have hU : cg_U δ cg_r216 σ = 10 := by
      have := cg_ramseyPath216_Ut hδ0 hδ1 0
      rw [cg_Ut_zero] at this
      unfold cg_U
      rw [hpath]
      exact this
    have h0 : σ [] = (1, 1) := congrFun hpath 0
    have hroot := (hσ.root hδ0 hδ1 cg_r216_abs_le).2 0
    have hmem : cg_U δ cg_r216 (cg_cont σ [((σ []).1, 0)]) ∈ cg_V δ cg_r216 cg_C216 :=
      ⟨_, hσ.cont hδ0 hδ1 cg_r216_abs_le _, rfl⟩
    have hge := cg_ex216_V_ge hδ0 hδ1 _ hmem
    rw [hU, h0] at hroot
    rw [h0] at hge hmem
    norm_num [cg_r216] at hroot
    by_contra hlt
    push Not at hlt
    have hδeq : δ = 5 / 14 := by nlinarith
    subst hδeq
    have hu1 : cg_U (5 / 14) cg_r216 (cg_cont σ [((1 : Fin 2), (0 : Fin 2))]) = 1 := by
      linarith
    rw [hu1] at hmem
    have h2 := cg_ex216_step hmem (by norm_num)
    have h3 := cg_ex216_step h2 (by norm_num)
    have h4 := cg_ex216_step h3 (by norm_num)
    have := cg_ex216_V_le hδ0 hδ1 _ h4
    norm_num at this
  · intro δ hδ hδ1
    have hδ0 : 0 ≤ δ := by linarith
    have hne : 10 * δ ≠ 10 := by intro h; linarith
    have hz10 : cg_ex216Z2 10 = 1 := by simp [cg_ex216Z2]
    have hzd : cg_ex216Z2 (10 * δ) = 0 := by simp [cg_ex216Z2, hne]
    have hspe := cg_recursive_spe (C := cg_C216) (K := 10) (S := {10 * δ, 10}) hδ0 hδ1
      cg_r216_abs_le (zh := cg_ex216Z2) (zg := cg_ex216Z2) (Vf := cg_ex216V2 δ) ?_ ?_ ?_ ?_ ?_
      10 (Or.inr rfl)
    · refine ⟨hspe.1, funext fun n => ?_⟩
      have hseq : ∀ m, cg_recSeq cg_ex216Z2 cg_ex216Z2 (cg_ex216V2 δ) 10 m = 10 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          have e : cg_ex216V2 δ 10 (cg_ex216Z2 10) (cg_ex216Z2 10) = 10 := by
            simp [cg_ex216V2]
          simp only [cg_recSeq, e]
          exact ih
      rw [(definition_21_4_5 _ _ _ 10 n).1, hseq, hz10]
      rfl
    · intro s hs
      rcases hs with rfl | rfl
      · rw [abs_le]; constructor <;> linarith
      · norm_num
    · intro s _ ξ η
      unfold cg_ex216V2
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro s hs
      simp only [cg_ex216V2, and_self, ↓reduceIte]
      rcases hs with rfl | rfl
      · rw [hzd]; norm_num [cg_r216]; ring
      · rw [hz10]; norm_num [cg_r216]; ring
    · intro s _
      exact rfl
    · have r00 : cg_r216 0 0 = 0 := by norm_num [cg_r216]
      have r01 : cg_r216 0 1 = 1 := by norm_num [cg_r216]
      have r10 : cg_r216 1 0 = 15 := by norm_num [cg_r216]
      have r11 : cg_r216 1 1 = 10 := by norm_num [cg_r216]
      intro s hs y'
      obtain rfl | rfl : y' = 0 ∨ y' = 1 := by fin_cases y' <;> simp
      · rcases hs with rfl | rfl
        · have : cg_ex216V2 δ (10 * δ) (cg_ex216Z2 (10 * δ)) 0 = 10 := by
            simp [cg_ex216V2, hzd]
          rw [this, hzd, r00]
          linarith
        · have : cg_ex216V2 δ 10 (cg_ex216Z2 10) 0 = 10 * δ := by simp [cg_ex216V2, hz10]
          rw [this, hz10, r10]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * δ - 1) (by linarith : (0 : ℝ) ≤ 1 - δ)]
      · rcases hs with rfl | rfl
        · have : cg_ex216V2 δ (10 * δ) (cg_ex216Z2 (10 * δ)) 1 = 10 * δ := by
            simp [cg_ex216V2, hzd]
          rw [this, hzd, r01]
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 10 * δ - 1)
            (by linarith : (0 : ℝ) ≤ 1 - δ)]
        · have : cg_ex216V2 δ 10 (cg_ex216Z2 10) 1 = 10 := by simp [cg_ex216V2, hz10]
          rw [this, hz10, r11]
          linarith

end Miao.DynamicGames

set_option linter.style.longLine false
#print axioms Miao.DynamicGames.rg_Prof
#print axioms Miao.DynamicGames.rg_Hist
#print axioms Miao.DynamicGames.rg_Strat
#print axioms Miao.DynamicGames.rg_upd
#print axioms Miao.DynamicGames.rg_upd_eq
#print axioms Miao.DynamicGames.rg_upd_self
#print axioms Miao.DynamicGames.rg_upd_ne
#print axioms Miao.DynamicGames.rg_upd_eq_self
#print axioms Miao.DynamicGames.rg_upd_player_eq
#print axioms Miao.DynamicGames.rg_cont
#print axioms Miao.DynamicGames.rg_dev
#print axioms Miao.DynamicGames.rg_hist
#print axioms Miao.DynamicGames.rg_path
#print axioms Miao.DynamicGames.rg_pathPay
#print axioms Miao.DynamicGames.rg_U
#print axioms Miao.DynamicGames.rg_cont_nil
#print axioms Miao.DynamicGames.rg_cont_cont
#print axioms Miao.DynamicGames.rg_cont_dev
#print axioms Miao.DynamicGames.rg_dev_self
#print axioms Miao.DynamicGames.rg_hist_cont
#print axioms Miao.DynamicGames.rg_path_cont
#print axioms Miao.DynamicGames.rg_summable
#print axioms Miao.DynamicGames.rg_pathPay_succ
#print axioms Miao.DynamicGames.rg_pathPay_mem
#print axioms Miao.DynamicGames.rg_abs_pathPay_le
#print axioms Miao.DynamicGames.rg_abs_U_le
#print axioms Miao.DynamicGames.rg_U_rec
#print axioms Miao.DynamicGames.rg_U_cont_rec
#print axioms Miao.DynamicGames.rg_U_subgame
#print axioms Miao.DynamicGames.rg_IsSPE
#print axioms Miao.DynamicGames.definition_21_1_1
#print axioms Miao.DynamicGames.rg_isSPE_cont
#print axioms Miao.DynamicGames.rg_IsOneShotDev
#print axioms Miao.DynamicGames.rg_IsProfitable
#print axioms Miao.DynamicGames.rg_oneShot
#print axioms Miao.DynamicGames.rg_oneShot_isOneShotDev
#print axioms Miao.DynamicGames.rg_cont_dev_after
#print axioms Miao.DynamicGames.definition_21_1_2
#print axioms Miao.DynamicGames.rg_oneShot_value
#print axioms Miao.DynamicGames.rg_oneShot_le_of_isSPE
#print axioms Miao.DynamicGames.rg_gain_le_of_noOneShot
#print axioms Miao.DynamicGames.proposition_21_1_1
#print axioms Miao.DynamicGames.rg_V
#print axioms Miao.DynamicGames.rg_Admissible
#print axioms Miao.DynamicGames.rg_B
#print axioms Miao.DynamicGames.definition_21_1_3
#print axioms Miao.DynamicGames.definition_21_1_4
#print axioms Miao.DynamicGames.rg_Bdd
#print axioms Miao.DynamicGames.rg_V_bdd
#print axioms Miao.DynamicGames.lemma_21_1_1
#print axioms Miao.DynamicGames.rg_state
#print axioms Miao.DynamicGames.rg_recStrat
#print axioms Miao.DynamicGames.rg_recStrat_spec
#print axioms Miao.DynamicGames.lemma_21_1_2
#print axioms Miao.DynamicGames.theorem_21_1_1
#print axioms Miao.DynamicGames.theorem_21_1_1_recursive
#print axioms Miao.DynamicGames.lemma_21_1_3
#print axioms Miao.DynamicGames.rg_IsStageNash
#print axioms Miao.DynamicGames.rg_stageNash_mem_V
#print axioms Miao.DynamicGames.rg_pdPay
#print axioms Miao.DynamicGames.rg_pdU
#print axioms Miao.DynamicGames.rg_pdW
#print axioms Miao.DynamicGames.rg_pd_upd
#print axioms Miao.DynamicGames.rg_pd_bound
#print axioms Miao.DynamicGames.example_21_1_1_DD
#print axioms Miao.DynamicGames.rg_pdWCC
#print axioms Miao.DynamicGames.example_21_1_1_CC
#print axioms Miao.DynamicGames.example_21_1_1
#print axioms Miao.DynamicGames.rg_pd_stageNash
#print axioms Miao.DynamicGames.rg_pd_V_nonempty
#print axioms Miao.DynamicGames.rg_feasible
#print axioms Miao.DynamicGames.rg_u_mem_feasible
#print axioms Miao.DynamicGames.rg_box
#print axioms Miao.DynamicGames.rg_box_convex
#print axioms Miao.DynamicGames.rg_box_isClosed
#print axioms Miao.DynamicGames.rg_mem_box
#print axioms Miao.DynamicGames.rg_closure_feasible_subset_box
#print axioms Miao.DynamicGames.rg_U_near_feasible
#print axioms Miao.DynamicGames.rg_U_mem_closure_feasible
#print axioms Miao.DynamicGames.rg_V_subset_closure_feasible
#print axioms Miao.DynamicGames.rg_closure_feasible_of_finite
#print axioms Miao.DynamicGames.rg_V_subset_feasible
#print axioms Miao.DynamicGames.rg_B_subset_of_convex
#print axioms Miao.DynamicGames.rg_BOn
#print axioms Miao.DynamicGames.rg_maximal_fixed_point
#print axioms Miao.DynamicGames.theorem_21_1_2
#print axioms Miao.DynamicGames.theorem_21_1_2_closure
#print axioms Miao.DynamicGames.rg_mem_B_iff_punish
#print axioms Miao.DynamicGames.ex_21_2
#print axioms Miao.DynamicGames.lemma_21_1_4
#print axioms Miao.DynamicGames.rg_box_isCompact
#print axioms Miao.DynamicGames.ex_21_1
#print axioms Miao.DynamicGames.proposition_21_1_2
#print axioms Miao.DynamicGames.rg_bdd_of_isCompact
#print axioms Miao.DynamicGames.theorem_21_1_3
#print axioms Miao.DynamicGames.theorem_21_1_3_hausdorff
#print axioms Miao.DynamicGames.rg_umin
#print axioms Miao.DynamicGames.rg_umax
#print axioms Miao.DynamicGames.rg_maxBox
#print axioms Miao.DynamicGames.rg_u_mem_maxBox
#print axioms Miao.DynamicGames.rg_maxBox_isCompact
#print axioms Miao.DynamicGames.rg_V_subset_maxBox
#print axioms Miao.DynamicGames.rg_B_maxBox_subset
#print axioms Miao.DynamicGames.rg_theorem_21_1_3_maxBox
#print axioms Miao.DynamicGames.rg_BCL
#print axioms Miao.DynamicGames.rg_BCL_eq
#print axioms Miao.DynamicGames.rg_cronshaw_luenberger
#print axioms Miao.DynamicGames.rg_Bstar
#print axioms Miao.DynamicGames.rg_Bstar_mono
#print axioms Miao.DynamicGames.rg_autState
#print axioms Miao.DynamicGames.rg_autStrat
#print axioms Miao.DynamicGames.rg_autState_append
#print axioms Miao.DynamicGames.rg_cont_autStrat
#print axioms Miao.DynamicGames.rg_autVal_rec
#print axioms Miao.DynamicGames.rg_aut_isSPE
#print axioms Miao.DynamicGames.rg_aut_ic_of_isSPE
#print axioms Miao.DynamicGames.rg_devBy
#print axioms Miao.DynamicGames.rg_devBy_self
#print axioms Miao.DynamicGames.rg_devBy_upd
#print axioms Miao.DynamicGames.rg_devBy_none
#print axioms Miao.DynamicGames.rg_simpleTrans
#print axioms Miao.DynamicGames.rg_simpleStrat
#print axioms Miao.DynamicGames.definition_21_1_5
#print axioms Miao.DynamicGames.rg_pathVal
#print axioms Miao.DynamicGames.rg_pathVal_succ
#print axioms Miao.DynamicGames.rg_simple_state_hist
#print axioms Miao.DynamicGames.rg_simple_val
#print axioms Miao.DynamicGames.rg_simple_payoff
#print axioms Miao.DynamicGames.rg_simple_reach
#print axioms Miao.DynamicGames.rg_proposition_21_1_3_if
#print axioms Miao.DynamicGames.proposition_21_1_3
#print axioms Miao.DynamicGames.rg_pathPay_const
#print axioms Miao.DynamicGames.rg_pdStick
#print axioms Miao.DynamicGames.rg_pdStick_val
#print axioms Miao.DynamicGames.rg_proposition_21_1_3_misprint_restart
#print axioms Miao.DynamicGames.rg_ownU
#print axioms Miao.DynamicGames.rg_ownQ
#print axioms Miao.DynamicGames.rg_proposition_21_1_3_misprint_own
#print axioms Miao.DynamicGames.rg_abreu_simple
#print axioms Miao.DynamicGames.DGPublicGame
#print axioms Miao.DynamicGames.DGPublicGame.mk
#print axioms Miao.DynamicGames.DGPublicGame.f
#print axioms Miao.DynamicGames.DGPublicGame.f_nonneg
#print axioms Miao.DynamicGames.DGPublicGame.f_sum
#print axioms Miao.DynamicGames.DGPublicGame.r
#print axioms Miao.DynamicGames.DGPublicGame.M
#print axioms Miao.DynamicGames.DGPublicGame.r_bound
#print axioms Miao.DynamicGames.dg_u
#print axioms Miao.DynamicGames.dg_cont
#print axioms Miao.DynamicGames.dg_dev
#print axioms Miao.DynamicGames.dg_ex
#print axioms Miao.DynamicGames.dg_U
#print axioms Miao.DynamicGames.dg_abs_u_le
#print axioms Miao.DynamicGames.dg_abs_avg_le
#print axioms Miao.DynamicGames.dg_abs_ex_le
#print axioms Miao.DynamicGames.dg_summable
#print axioms Miao.DynamicGames.dg_abs_U_le
#print axioms Miao.DynamicGames.dg_U_rec
#print axioms Miao.DynamicGames.dg_cont_append
#print axioms Miao.DynamicGames.dg_nonpos_of_le_mul_iSup
#print axioms Miao.DynamicGames.dg_avg_le_iSup
#print axioms Miao.DynamicGames.dg_IsPPE
#print axioms Miao.DynamicGames.dg_PPEPayoffs
#print axioms Miao.DynamicGames.dg_gen
#print axioms Miao.DynamicGames.dg_Admissible
#print axioms Miao.DynamicGames.dg_B
#print axioms Miao.DynamicGames.dg_oneShot_ppe
#print axioms Miao.DynamicGames.dg_ppe_subset_B
#print axioms Miao.DynamicGames.dg_sgAct
#print axioms Miao.DynamicGames.dg_sgNext
#print axioms Miao.DynamicGames.dg_sgPath
#print axioms Miao.DynamicGames.dg_sgStrat
#print axioms Miao.DynamicGames.dg_sg_spec
#print axioms Miao.DynamicGames.dg_sgStrat_cont
#print axioms Miao.DynamicGames.dg_sgPath_mem
#print axioms Miao.DynamicGames.dg_coord_bound
#print axioms Miao.DynamicGames.dg_sgStrat_U
#print axioms Miao.DynamicGames.dg_sgStrat_isPPE
#print axioms Miao.DynamicGames.dg_selfGeneration_ppe
#print axioms Miao.DynamicGames.dg_selfGenerating_subset_ppe
#print axioms Miao.DynamicGames.dg_ppe_isBounded
#print axioms Miao.DynamicGames.dg_factorization_ppe
#print axioms Miao.DynamicGames.dg_ppe_greatest_fixedPoint
#print axioms Miao.DynamicGames.dg_B_mono
#print axioms Miao.DynamicGames.dg_gen_continuous
#print axioms Miao.DynamicGames.dg_B_isCompact
#print axioms Miao.DynamicGames.dg_pdProbG
#print axioms Miao.DynamicGames.dg_pdF
#print axioms Miao.DynamicGames.dg_pdR
#print axioms Miao.DynamicGames.dg_pdM
#print axioms Miao.DynamicGames.dg_pdProbG_mem
#print axioms Miao.DynamicGames.dg_noisyPD
#print axioms Miao.DynamicGames.dg_noisyPD_u
#print axioms Miao.DynamicGames.dg_pdMatrix
#print axioms Miao.DynamicGames.example_21_1_2_payoffs
#print axioms Miao.DynamicGames.dg_noisyPD_u_matrix
#print axioms Miao.DynamicGames.dg_pdV
#print axioms Miao.DynamicGames.dg_pdV'
#print axioms Miao.DynamicGames.dg_pdW
#print axioms Miao.DynamicGames.example_21_1_2_DD_eq
#print axioms Miao.DynamicGames.example_21_1_2_CC_eq
#print axioms Miao.DynamicGames.example_21_1_2_DD_ic_iff
#print axioms Miao.DynamicGames.example_21_1_2_CC_ic_iff
#print axioms Miao.DynamicGames.example_21_1_2_interval
#print axioms Miao.DynamicGames.dg_noisyPD_gen
#print axioms Miao.DynamicGames.example_21_1_2
#print axioms Miao.DynamicGames.example_21_1_2_ppe
#print axioms Miao.DynamicGames.example_21_1_2_instance
#print axioms Miao.DynamicGames.example_21_1_2_printed_false
#print axioms Miao.DynamicGames.DGStochGame
#print axioms Miao.DynamicGames.DGStochGame.mk
#print axioms Miao.DynamicGames.DGStochGame.P
#print axioms Miao.DynamicGames.DGStochGame.P_nonneg
#print axioms Miao.DynamicGames.DGStochGame.P_sum
#print axioms Miao.DynamicGames.DGStochGame.u
#print axioms Miao.DynamicGames.DGStochGame.M
#print axioms Miao.DynamicGames.DGStochGame.u_bound
#print axioms Miao.DynamicGames.DGStochGame.δ
#print axioms Miao.DynamicGames.DGStochGame.δ_nonneg
#print axioms Miao.DynamicGames.DGStochGame.δ_lt_one
#print axioms Miao.DynamicGames.dg_shift
#print axioms Miao.DynamicGames.dg_mdev
#print axioms Miao.DynamicGames.dg_mex
#print axioms Miao.DynamicGames.dg_mU
#print axioms Miao.DynamicGames.dg_abs_mex_le
#print axioms Miao.DynamicGames.dg_msummable
#print axioms Miao.DynamicGames.dg_abs_mU_le
#print axioms Miao.DynamicGames.dg_mU_rec
#print axioms Miao.DynamicGames.dg_IsMPE
#print axioms Miao.DynamicGames.dg_IsStationaryMPE
#print axioms Miao.DynamicGames.dg_mV
#print axioms Miao.DynamicGames.dg_mV_bellman
#print axioms Miao.DynamicGames.definition_21_2_1_bellman_iff
#print axioms Miao.DynamicGames.dg_stationaryMPE_bellman
#print axioms Miao.DynamicGames.dg_SYmu
#print axioms Miao.DynamicGames.dg_SY
#print axioms Miao.DynamicGames.dg_SY_mono
#print axioms Miao.DynamicGames.dg_SY_isCompact
#print axioms Miao.DynamicGames.dg_pdStochGame
#print axioms Miao.DynamicGames.dg_pdStochGame_mpe
#print axioms Miao.DynamicGames.dg_log_max
#print axioms Miao.DynamicGames.dg_fpNext
#print axioms Miao.DynamicGames.dg_fpKappa
#print axioms Miao.DynamicGames.dg_fpNu
#print axioms Miao.DynamicGames.dg_fpV
#print axioms Miao.DynamicGames.dg_fpRHS
#print axioms Miao.DynamicGames.dg_fpRHS_eq
#print axioms Miao.DynamicGames.dg_fpKappa_eq
#print axioms Miao.DynamicGames.dg_fp_bellman_eq
#print axioms Miao.DynamicGames.dg_fp_bellman
#print axioms Miao.DynamicGames.dg_fp_bellman_unique
#print axioms Miao.DynamicGames.dg_fp_kappa_forced
#print axioms Miao.DynamicGames.dg_fp_telescope
#print axioms Miao.DynamicGames.dg_fp_optimal
#print axioms Miao.DynamicGames.dg_fpPath
#print axioms Miao.DynamicGames.dg_fpPath_pos
#print axioms Miao.DynamicGames.dg_fpPath_log
#print axioms Miao.DynamicGames.dg_fpPath_feasible
#print axioms Miao.DynamicGames.dg_fpPath_log_bound
#print axioms Miao.DynamicGames.dg_fp_policy_value
#print axioms Miao.DynamicGames.dg_fp_path_tendsto
#print axioms Miao.DynamicGames.dg_fishLaw
#print axioms Miao.DynamicGames.dg_fish_V_law
#print axioms Miao.DynamicGames.dg_fish_foc_deriv
#print axioms Miao.DynamicGames.eq_21_2
#print axioms Miao.DynamicGames.dg_fish_foc_solve
#print axioms Miao.DynamicGames.dg_fish_mpe_kappa
#print axioms Miao.DynamicGames.dg_fishK
#print axioms Miao.DynamicGames.dg_fishS
#print axioms Miao.DynamicGames.dg_fish_mpe_closed_form
#print axioms Miao.DynamicGames.dg_fish_rates
#print axioms Miao.DynamicGames.eq_21_1_mpe
#print axioms Miao.DynamicGames.dg_fish_mpe
#print axioms Miao.DynamicGames.dg_fish_mpe_steady_state
#print axioms Miao.DynamicGames.dg_fish_follower_reaction
#print axioms Miao.DynamicGames.dg_fish_follower_printed_false
#print axioms Miao.DynamicGames.dg_fish_leader_foc
#print axioms Miao.DynamicGames.dg_fish_leader
#print axioms Miao.DynamicGames.ex_21_3
#print axioms Miao.DynamicGames.dg_log_add_le
#print axioms Miao.DynamicGames.dg_fish_cooperative
#print axioms Miao.DynamicGames.dg_fish_overfishing
#print axioms Miao.DynamicGames.cg_CE
#print axioms Miao.DynamicGames.cg_mem_CE
#print axioms Miao.DynamicGames.cg_IsRamsey
#print axioms Miao.DynamicGames.cg_IsNash
#print axioms Miao.DynamicGames.cg_vN_le_vR
#print axioms Miao.DynamicGames.cg_bgGov
#print axioms Miao.DynamicGames.cg_bgHH
#print axioms Miao.DynamicGames.cg_bgC
#print axioms Miao.DynamicGames.example_21_4_1_household
#print axioms Miao.DynamicGames.example_21_4_1_ramsey
#print axioms Miao.DynamicGames.example_21_4_1_nash
#print axioms Miao.DynamicGames.example_21_4_1_time_inconsistent
#print axioms Miao.DynamicGames.cg_r422
#print axioms Miao.DynamicGames.cg_C422
#print axioms Miao.DynamicGames.example_21_4_2
#print axioms Miao.DynamicGames.cg_r216
#print axioms Miao.DynamicGames.cg_C216
#print axioms Miao.DynamicGames.ex_21_6_a
#print axioms Miao.DynamicGames.ex_21_6_b
#print axioms Miao.DynamicGames.CGProfile
#print axioms Miao.DynamicGames.cg_cont
#print axioms Miao.DynamicGames.cg_cont_apply
#print axioms Miao.DynamicGames.cg_cont_nil
#print axioms Miao.DynamicGames.cg_cont_cont
#print axioms Miao.DynamicGames.cg_path
#print axioms Miao.DynamicGames.cg_prefix
#print axioms Miao.DynamicGames.cg_prefix_succ
#print axioms Miao.DynamicGames.cg_path_cont_prefix
#print axioms Miao.DynamicGames.cg_path_spec
#print axioms Miao.DynamicGames.cg_pathValue
#print axioms Miao.DynamicGames.cg_U
#print axioms Miao.DynamicGames.cg_Ut
#print axioms Miao.DynamicGames.cg_Uh
#print axioms Miao.DynamicGames.cg_Uh_eq
#print axioms Miao.DynamicGames.cg_summable
#print axioms Miao.DynamicGames.cg_pathValue_le
#print axioms Miao.DynamicGames.cg_le_pathValue
#print axioms Miao.DynamicGames.cg_pathValue_const
#print axioms Miao.DynamicGames.cg_pathValue_succ
#print axioms Miao.DynamicGames.cg_Ut_succ
#print axioms Miao.DynamicGames.cg_Ut_zero
#print axioms Miao.DynamicGames.cg_U_rec
#print axioms Miao.DynamicGames.cg_U_cont_rec
#print axioms Miao.DynamicGames.cg_abs_U_le
#print axioms Miao.DynamicGames.cg_U_const
#print axioms Miao.DynamicGames.cg_withGov
#print axioms Miao.DynamicGames.cg_IsSPE
#print axioms Miao.DynamicGames.definition_21_4_1
#print axioms Miao.DynamicGames.cg_OneShot
#print axioms Miao.DynamicGames.cg_isSPE_iff_oneShot
#print axioms Miao.DynamicGames.cg_IsSPE.cont
#print axioms Miao.DynamicGames.cg_IsSPE.root
#print axioms Miao.DynamicGames.lemma_21_4_1
#print axioms Miao.DynamicGames.cg_nash_repetition_spe
#print axioms Miao.DynamicGames.cg_V
#print axioms Miao.DynamicGames.cg_V_abs_le
#print axioms Miao.DynamicGames.cg_V_isBounded
#print axioms Miao.DynamicGames.cg_IsSPE.path_mem
#print axioms Miao.DynamicGames.cg_V_subset_Icc
#print axioms Miao.DynamicGames.cg_V_lower
#print axioms Miao.DynamicGames.cg_recState
#print axioms Miao.DynamicGames.cg_recStrat
#print axioms Miao.DynamicGames.cg_recStrat_cont
#print axioms Miao.DynamicGames.cg_recStrat_cont_single
#print axioms Miao.DynamicGames.cg_recState_mem
#print axioms Miao.DynamicGames.cg_recSeq
#print axioms Miao.DynamicGames.definition_21_4_5
#print axioms Miao.DynamicGames.cg_recStrat_value
#print axioms Miao.DynamicGames.cg_recursive_spe
#print axioms Miao.DynamicGames.cg_recursive_spe_only_if
#print axioms Miao.DynamicGames.cg_trigZh
#print axioms Miao.DynamicGames.cg_trigZg
#print axioms Miao.DynamicGames.cg_trigV
#print axioms Miao.DynamicGames.cg_trigger_value
#print axioms Miao.DynamicGames.example_21_4_5
#print axioms Miao.DynamicGames.cg_scZh
#print axioms Miao.DynamicGames.cg_scZg
#print axioms Miao.DynamicGames.cg_scV
#print axioms Miao.DynamicGames.cg_stickCarrot_value
#print axioms Miao.DynamicGames.example_21_4_6
#print axioms Miao.DynamicGames.cg_Admissible
#print axioms Miao.DynamicGames.cg_B
#print axioms Miao.DynamicGames.cg_SelfGenerating
#print axioms Miao.DynamicGames.definition_21_4_2
#print axioms Miao.DynamicGames.definition_21_4_3
#print axioms Miao.DynamicGames.definition_21_4_4
#print axioms Miao.DynamicGames.cg_B_mono
#print axioms Miao.DynamicGames.cg_K
#print axioms Miao.DynamicGames.cg_K_mono
#print axioms Miao.DynamicGames.cg_B_eq_image
#print axioms Miao.DynamicGames.cg_K_isCompact
#print axioms Miao.DynamicGames.lemma_21_4_2
#print axioms Miao.DynamicGames.cg_V_subset_B
#print axioms Miao.DynamicGames.cg_paste
#print axioms Miao.DynamicGames.cg_B_subset_V
#print axioms Miao.DynamicGames.cg_selfGenerating_subset_V
#print axioms Miao.DynamicGames.lemma_21_4_3
#print axioms Miao.DynamicGames.theorem_21_4_1
#print axioms Miao.DynamicGames.cg_mem_V_of_mem_B_insert
#print axioms Miao.DynamicGames.cg_aps_step1
#print axioms Miao.DynamicGames.cg_aps_step2
#print axioms Miao.DynamicGames.cg_aps_step2_max
#print axioms Miao.DynamicGames.cg_aps_step3
#print axioms Miao.DynamicGames.cg_follow
#print axioms Miao.DynamicGames.cg_follow_cont_single
#print axioms Miao.DynamicGames.cg_follow_cont
#print axioms Miao.DynamicGames.cg_follow_path
#print axioms Miao.DynamicGames.cg_follow_U
#print axioms Miao.DynamicGames.cg_follow_spe
#print axioms Miao.DynamicGames.proposition_21_4_1
#print axioms Miao.DynamicGames.cg_selfEnf
#print axioms Miao.DynamicGames.cg_SelfEnforcing
#print axioms Miao.DynamicGames.cg_selfEnf_cont_single
#print axioms Miao.DynamicGames.cg_selfEnf_cont
#print axioms Miao.DynamicGames.cg_selfEnf_path
#print axioms Miao.DynamicGames.cg_selfEnf_U
#print axioms Miao.DynamicGames.cg_selfEnf_prefix
#print axioms Miao.DynamicGames.cg_selfEnf_path_zero
#print axioms Miao.DynamicGames.proposition_21_4_2
#print axioms Miao.DynamicGames.proposition_21_4_3
#print axioms Miao.DynamicGames.ex_21_4
#print axioms Miao.DynamicGames.cg_vmin_eq
#print axioms Miao.DynamicGames.cg_v1_formula
#print axioms Miao.DynamicGames.cg_vmax
#print axioms Miao.DynamicGames.cg_four_equations
#print axioms Miao.DynamicGames.cg_example_21_4_6_selfEnforcing
#print axioms Miao.DynamicGames.cg_r422_abs_le
#print axioms Miao.DynamicGames.cg_C422_mem
#print axioms Miao.DynamicGames.cg_stokeyZ
#print axioms Miao.DynamicGames.cg_stokeyNext
#print axioms Miao.DynamicGames.cg_stokeyV
#print axioms Miao.DynamicGames.cg_stokey_recursive_spe
#print axioms Miao.DynamicGames.cg_stokey_V_ge
#print axioms Miao.DynamicGames.cg_stokey_V_le
#print axioms Miao.DynamicGames.cg_stokey_V
#print axioms Miao.DynamicGames.cg_stokey_vmin_vmax
#print axioms Miao.DynamicGames.cg_stokey_vmin_formula
#print axioms Miao.DynamicGames.cg_stokeyPath
#print axioms Miao.DynamicGames.cg_stokeyPath_Ut
#print axioms Miao.DynamicGames.cg_stokeyPath_selfEnforcing
#print axioms Miao.DynamicGames.cg_ramseyPath422
#print axioms Miao.DynamicGames.example_21_4_4
#print axioms Miao.DynamicGames.example_21_4_4_arith
#print axioms Miao.DynamicGames.ex_21_5
#print axioms Miao.DynamicGames.cg_theorem_21_4_1_unbounded
#print axioms Miao.DynamicGames.cg_proposition_21_4_1_counterexample
#print axioms Miao.DynamicGames.cg_cexZh
#print axioms Miao.DynamicGames.cg_cexV
#print axioms Miao.DynamicGames.cg_definition_21_4_5_counterexample
#print axioms Miao.DynamicGames.cg_example_21_4_5_counterexample
#print axioms Miao.DynamicGames.cg_example_21_4_6_counterexample
#print axioms Miao.DynamicGames.cg_rBool
#print axioms Miao.DynamicGames.cg_CBool
#print axioms Miao.DynamicGames.cg_pBool
#print axioms Miao.DynamicGames.cg_rBool_abs_le
#print axioms Miao.DynamicGames.cg_proposition_21_4_2_counterexample
#print axioms Miao.DynamicGames.cg_bgGov_eq
#print axioms Miao.DynamicGames.example_21_4_3_best_deviation
#print axioms Miao.DynamicGames.example_21_4_3_range
#print axioms Miao.DynamicGames.example_21_4_3_mono
#print axioms Miao.DynamicGames.cg_bgR
#print axioms Miao.DynamicGames.cg_bgCK
#print axioms Miao.DynamicGames.cg_bgR_abs_le
#print axioms Miao.DynamicGames.example_21_4_3_nash
#print axioms Miao.DynamicGames.example_21_4_3
#print axioms Miao.DynamicGames.cg_r216_abs_le
#print axioms Miao.DynamicGames.cg_C216_mem
#print axioms Miao.DynamicGames.cg_ex216_V_ge
#print axioms Miao.DynamicGames.cg_ex216_V_le
#print axioms Miao.DynamicGames.cg_ex216Z
#print axioms Miao.DynamicGames.cg_ex216Next
#print axioms Miao.DynamicGames.cg_ex216V
#print axioms Miao.DynamicGames.cg_ex216_recursive_spe
#print axioms Miao.DynamicGames.cg_ex216_V
#print axioms Miao.DynamicGames.ex_21_6_c
#print axioms Miao.DynamicGames.cg_ramseyPath216
#print axioms Miao.DynamicGames.cg_ramseyPath216_Ut
#print axioms Miao.DynamicGames.cg_ex216_ramsey_spe
#print axioms Miao.DynamicGames.ex_21_6_d
#print axioms Miao.DynamicGames.ex_21_6_e
#print axioms Miao.DynamicGames.cg_ex216_step
#print axioms Miao.DynamicGames.cg_ex216Z2
#print axioms Miao.DynamicGames.cg_ex216V2
#print axioms Miao.DynamicGames.ex_21_6_f
