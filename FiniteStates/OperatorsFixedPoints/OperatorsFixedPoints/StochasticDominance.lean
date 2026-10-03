/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stochastic dominance

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.4 (pp. 62–64).

For distributions `φ, ψ` on a finite partially ordered set `X`, `ψ`
stochastically dominates `φ`, `φ ≼_F ψ`, if `∑ u φ ≤ ∑ u ψ` for every
increasing `u`, (2.9). Example 2.2.11 is proved in its general form: if two
random variables on a finite probability space satisfy `X ≤ Y` pointwise then
the law of `Y` dominates the law of `X`. Exercise 2.2.33 treats `X = {1, 2}`;
Lemma 2.2.5 relates dominance to the counter-CDFs, with the converse on totally
ordered sets proved by Abel summation (the book's proof is in its Appendix B);
Lemma 2.2.6 shows `≼_F` is a partial order, antisymmetry by induction along the
well-founded order on the finite set; Exercise 2.2.35 orders quantiles.
-/

open Finset

namespace SargentStachurski.OperatorsFixedPoints

variable {X : Type*} [Fintype X]

/-- A distribution on the finite set `X`. -/
structure IsDistribution (φ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  sum_eq_one : ∑ x, φ x = 1

/-- The law of a random variable `Z : Ω → X` on a finite probability space `(Ω, p)`. -/
def law {Ω : Type*} [Fintype Ω] [DecidableEq X] (p : Ω → ℝ) (Z : Ω → X) (x : X) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => Z ω = x), p ω

theorem law_isDistribution {Ω : Type*} [Fintype Ω] [DecidableEq X] {p : Ω → ℝ}
    (hp : IsDistribution p) (Z : Ω → X) : IsDistribution (law p Z) where
  nonneg x := sum_nonneg fun ω _ => hp.nonneg ω
  sum_eq_one := by
    rw [← hp.sum_eq_one]
    exact (sum_fiberwise univ Z p)

/-- `∑ u(x) law(x) = ∑_ω u(Z ω) p(ω)`. -/
theorem sum_mul_law {Ω : Type*} [Fintype Ω] [DecidableEq X] (p : Ω → ℝ) (Z : Ω → X) (u : X → ℝ) :
    ∑ x, u x * law p Z x = ∑ ω, u (Z ω) * p ω := by
  rw [← sum_fiberwise univ Z fun ω => u (Z ω) * p ω]
  refine sum_congr rfl fun x _ => ?_
  rw [law, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.1 hω).2]

-- Partially ordered state spaces
variable [PartialOrder X]

/-- First-order stochastic dominance (2.9), p. 62: `φ ≼_F ψ` iff `∑ u(x)φ(x) ≤ ∑ u(x)ψ(x)`
for every increasing `u`. -/
def FOSD (φ ψ : X → ℝ) : Prop := ∀ u : X → ℝ, Monotone u → ∑ x, u x * φ x ≤ ∑ x, u x * ψ x

/-- Example 2.2.11 (p. 63), in general: if `X ≤ Y` pointwise on a finite probability space, then
the law of `Y` stochastically dominates the law of `X`, since `u(X) ≤ u(Y)` pointwise for every
increasing `u`. The binomial case is `X = W₁ + ⋯ + W₁₀ ≤ W₁ + ⋯ + W₁₈ = Y`. -/
theorem fosd_law_of_le {Ω : Type*} [Fintype Ω] [DecidableEq X] {p : Ω → ℝ} (hp : IsDistribution p)
    {Z Z' : Ω → X} (hZ : ∀ ω, Z ω ≤ Z' ω) : FOSD (law p Z) (law p Z') := by
  unfold FOSD
  intro u hu
  rw [sum_mul_law, sum_mul_law]
  exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_right (hu (hZ ω)) (hp.nonneg ω)

open Classical in
/-- The counter-CDF `G_φ(y) = ∑_{x ≥ y} φ(x)` (p. 64). -/
noncomputable def ccdf (φ : X → ℝ) (y : X) : ℝ := ∑ x ∈ univ.filter (fun x => y ≤ x), φ x

omit [Fintype X] in
open Classical in
/-- The indicator of the upper set `{x : y ≤ x}` is increasing. -/
theorem monotone_upper_indicator (y : X) :
    Monotone fun x : X => if y ≤ x then (1 : ℝ) else 0 := fun a b hab => by
  dsimp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans hab) h2
  · norm_num
  · exact le_rfl

open Classical in
/-- `∑ 1{y ≤ x} φ(x) = G_φ(y)`. -/
theorem sum_upper_indicator_mul (φ : X → ℝ) (y : X) :
    ∑ x, (if y ≤ x then (1 : ℝ) else 0) * φ x = ccdf φ y := by
  rw [ccdf, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- Lemma 2.2.5 (i), p. 64: `φ ≼_F ψ` implies `G_φ ≤ G_ψ`. -/
theorem ccdf_le_of_fosd {φ ψ : X → ℝ} (h : FOSD φ ψ) (y : X) : ccdf φ y ≤ ccdf ψ y := by
  rw [← sum_upper_indicator_mul, ← sum_upper_indicator_mul]
  exact h _ (monotone_upper_indicator y)

/-- Lemma 2.2.6 (p. 64): `≼_F` is reflexive. -/
theorem fosd_refl (φ : X → ℝ) : FOSD φ φ := fun _ _ => le_rfl

/-- Exercise 2.2.34 (p. 64): `≼_F` is transitive. -/
theorem fosd_trans {φ ψ χ : X → ℝ} (h₁ : FOSD φ ψ) (h₂ : FOSD ψ χ) : FOSD φ χ := fun u hu =>
  (h₁ u hu).trans (h₂ u hu)

open Classical in
/-- A function on a finite poset is determined by its upper-set sums, by induction along the
well-founded order `>`: `φ(y) = G_φ(y) − ∑_{x > y} φ(x)`. -/
theorem eq_of_ccdf_eq {φ ψ : X → ℝ} (h : ∀ y, ccdf φ y = ccdf ψ y) : φ = ψ := by
  funext y
  induction y using WellFoundedGT.induction with
  | _ y ih =>
    have hsplit : ∀ χ : X → ℝ, ccdf χ y = χ y + ∑ x ∈ univ.filter (fun x => y < x), χ x := by
      intro χ
      rw [ccdf]
      have : univ.filter (fun x => y ≤ x) = insert y (univ.filter (fun x => y < x)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hx
          rcases hx.lt_or_eq with hlt | heq
          · exact Or.inr hlt
          · exact Or.inl heq.symm
        · rintro (rfl | hlt)
          · exact le_rfl
          · exact hlt.le
      rw [this, Finset.sum_insert]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false, not_false_eq_true]
    have htail : ∑ x ∈ univ.filter (fun x => y < x), φ x =
        ∑ x ∈ univ.filter (fun x => y < x), ψ x :=
      sum_congr rfl fun x hx => ih x (Finset.mem_filter.1 hx).2
    have := h y
    rw [hsplit φ, hsplit ψ, htail] at this
    linarith

/-- Lemma 2.2.6 (p. 64): `≼_F` is antisymmetric, hence a partial order. -/
theorem fosd_antisymm {φ ψ : X → ℝ} (h₁ : FOSD φ ψ) (h₂ : FOSD ψ φ) : φ = ψ :=
  eq_of_ccdf_eq fun y => le_antisymm (ccdf_le_of_fosd h₁ y) (ccdf_le_of_fosd h₂ y)

-- Totally ordered state spaces
variable {Y : Type*} [Fintype Y] [LinearOrder Y]

/-- Abel summation on `Fin n`: if `u` is increasing and nonnegative and every tail sum of `d`
is nonnegative, then `∑ u d ≥ 0`. -/
theorem sum_mul_nonneg_of_tails_nonneg : ∀ (n : ℕ) (u d : Fin n → ℝ), Monotone u →
    (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ ∑ j ∈ univ.filter (fun j => i ≤ j), d j) →
    0 ≤ ∑ i, u i * d i := by
  intro n
  induction n with
  | zero => intro u d _ _ _; simp
  | succ n ih =>
    intro u d hu hu0 htail
    -- `∑ u d = u 0 · D(0) + ∑_{i ≥ 1} (u i − u 0) d i`
    have hD0 : ∑ j, d j = ∑ j ∈ univ.filter (fun j => (0 : Fin (n + 1)) ≤ j), d j := by
      congr 1
      ext j
      simp
    have hsplit : ∑ i, u i * d i =
        u 0 * ∑ j, d j + ∑ i : Fin n, (u i.succ - u 0) * d i.succ := by
      simp only [Fin.sum_univ_succ, sub_mul, sum_sub_distrib, mul_sum, mul_add]
      ring
    rw [hsplit]
    refine add_nonneg (mul_nonneg (hu0 0) (hD0 ▸ htail 0)) ?_
    refine ih (fun i => u i.succ - u 0) (fun i => d i.succ) ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu (Fin.succ_le_succ_iff.2 hij)) _
    · intro i
      exact sub_nonneg.2 (hu (Fin.zero_le _))
    · intro i
      have := htail i.succ
      -- the tail of `d ∘ succ` from `i` is the tail of `d` from `succ i`
      have hreindex : ∑ j ∈ univ.filter (fun j : Fin (n + 1) => i.succ ≤ j), d j =
          ∑ j ∈ univ.filter (fun j : Fin n => i ≤ j), d j.succ := by
        refine (Finset.sum_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_).symm
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact Fin.succ_le_succ_iff.2 hj
        · intro a _ b _ hab
          exact Fin.succ_injective _ hab
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          refine ⟨j.pred (Fin.pos_iff_ne_zero.1 (lt_of_lt_of_le (Fin.succ_pos i) hj)), ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← Fin.succ_le_succ_iff, Fin.succ_pred]
            exact hj
          · exact Fin.succ_pred _ _
        · intro j _
          rfl
      rwa [hreindex] at this

open Classical in
/-- The counter-CDF is additive: `G_{ψ − φ} = G_ψ − G_φ`. -/
theorem ccdf_sub (φ ψ : Y → ℝ) (y : Y) : ccdf (fun x => ψ x - φ x) y = ccdf ψ y - ccdf φ y := by
  simp only [ccdf, sum_sub_distrib]

open Classical in
/-- Reindexing the counter-CDF through an order isomorphism with `Fin n`. -/
theorem ccdf_reindex (χ : Y → ℝ) (e : Fin (Fintype.card Y) ≃o Y) (i : Fin (Fintype.card Y)) :
    ccdf χ (e i) = ∑ j ∈ univ.filter (fun j => i ≤ j), χ (e j) := by
  unfold ccdf
  exact (Finset.sum_equiv e.toEquiv (fun j => by simp [Finset.mem_filter, e.le_iff_le])
    (fun _ _ => rfl)).symm

/-- Lemma 2.2.5 (ii), p. 64: on a totally ordered finite set, `G_φ ≤ G_ψ` implies `φ ≼_F ψ`,
for distributions `φ, ψ`. The increasing `u` is shifted by its minimum to be nonnegative, and
`d = ψ − φ` has nonnegative tail sums and total `0`. -/
theorem fosd_of_ccdf_le {φ ψ : Y → ℝ} (hφ : IsDistribution φ) (hψ : IsDistribution ψ)
    (h : ∀ y, ccdf φ y ≤ ccdf ψ y) : FOSD φ ψ := by
  unfold FOSD
  intro u hu
  rcases isEmpty_or_nonempty Y with hX | hX
  · simp
  -- transport to `Fin n`
  let e : Fin (Fintype.card Y) ≃o Y := Fintype.orderIsoFinOfCardEq Y rfl
  set m : Y := e 0 with hm
  have hmin : ∀ x, m ≤ x := fun x => by
    rw [hm, ← e.apply_symm_apply x, e.le_iff_le]
    exact Fin.zero_le _
  have hsum : ∑ x, (ψ x - φ x) = 0 := by
    rw [sum_sub_distrib, hψ.sum_eq_one, hφ.sum_eq_one, sub_self]
  -- `∑ (u − u m)(ψ − φ) ≥ 0`
  have key : 0 ≤ ∑ x, (u x - u m) * (ψ x - φ x) := by
    rw [← e.toEquiv.sum_comp]
    refine sum_mul_nonneg_of_tails_nonneg _ (fun i => u (e i) - u m) (fun i => ψ (e i) - φ (e i))
      ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu (e.le_iff_le.2 hij)) _
    · intro i
      exact sub_nonneg.2 (hu (hmin _))
    · intro i
      have h1 := ccdf_reindex (fun x => ψ x - φ x) e i
      rw [ccdf_sub] at h1
      have h2 : 0 ≤ ccdf ψ (e i) - ccdf φ (e i) := sub_nonneg.2 (h (e i))
      rw [h1] at h2
      simpa using h2
  have hexpand : ∑ x, (u x - u m) * (ψ x - φ x) = ∑ x, u x * ψ x - ∑ x, u x * φ x := by
    have h1 : ∑ x, (u x - u m) * (ψ x - φ x) =
        ∑ x, u x * (ψ x - φ x) - u m * ∑ x, (ψ x - φ x) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [h1, hsum, mul_zero, sub_zero, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  linarith

/-- The CDF `F_φ(x) = ∑_{x' ≤ x} φ(x')` on a totally ordered finite set (Vol. 1, p. 32). -/
noncomputable def cdf (φ : Y → ℝ) (x : Y) : ℝ := ∑ x' ∈ univ.filter (fun x' => x' ≤ x), φ x'

/-- Dominance reverses CDFs: `φ ≼_F ψ` implies `F_ψ ≤ F_φ`, since `−1{x' ≤ x}` is increasing. -/
theorem cdf_le_of_fosd {φ ψ : Y → ℝ} (h : FOSD φ ψ) (x : Y) : cdf ψ x ≤ cdf φ x := by
  have hmono : Monotone fun x' : Y => -(if x' ≤ x then (1 : ℝ) else 0) := fun a b hab => by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · norm_num
    · exact absurd (hab.trans h2) h1
    · exact le_rfl
  have := h _ hmono
  simp only [neg_mul, sum_neg_distrib, neg_le_neg_iff] at this
  have hc : ∀ χ : Y → ℝ, ∑ x', (if x' ≤ x then (1 : ℝ) else 0) * χ x' = cdf χ x := by
    intro χ
    rw [cdf, sum_filter]
    refine sum_congr rfl fun x' _ => ?_
    split_ifs <;> simp
  rwa [hc, hc] at this

/-- The `τ`-quantile set `{x : τ ≤ F_φ(x)}`. -/
noncomputable def quantileSet (φ : Y → ℝ) (τ : ℝ) : Finset Y := univ.filter fun x => τ ≤ cdf φ x

/-- The `τ`-quantile `Q_τ = min{x : F_φ(x) ≥ τ}` (Vol. 1, (1.24)), given the set is nonempty. -/
noncomputable def quantile (φ : Y → ℝ) (τ : ℝ) (h : (quantileSet φ τ).Nonempty) : Y :=
  (quantileSet φ τ).min' h

/-- Exercise 2.2.35 (p. 64): `φ ≼_F ψ` implies `Q_τ(Y) ≤ Q_τ(Y)`, since `F_ψ ≤ F_φ` makes
`ψ`'s quantile set a subset of `φ`'s. -/
theorem quantile_le_of_fosd {φ ψ : Y → ℝ} (h : FOSD φ ψ) {τ : ℝ} (hφ : (quantileSet φ τ).Nonempty)
    (hψ : (quantileSet ψ τ).Nonempty) : quantile φ τ hφ ≤ quantile ψ τ hψ := by
  have hsub : quantileSet ψ τ ⊆ quantileSet φ τ := by
    intro x hx
    simp only [quantileSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans (cdf_le_of_fosd h x)
  exact Finset.min'_subset hψ hsub

/-- Exercise 2.2.33 (p. 64): on `Y = {1, 2}`, `φ ≼_F ψ ↔ ψ(1) ≤ φ(1) ↔ φ(2) ≤ ψ(2)`, for
distributions. Here `Y = Fin 2` with `0 < 1` playing the roles of `1 < 2`. -/
theorem fosd_fin_two_iff {φ ψ : Fin 2 → ℝ} (hφ : IsDistribution φ) (hψ : IsDistribution ψ) :
    (FOSD φ ψ ↔ ψ 0 ≤ φ 0) ∧ (ψ 0 ≤ φ 0 ↔ φ 1 ≤ ψ 1) := by
  have hφs : φ 0 + φ 1 = 1 := by simpa [Fin.sum_univ_two] using hφ.sum_eq_one
  have hψs : ψ 0 + ψ 1 = 1 := by simpa [Fin.sum_univ_two] using hψ.sum_eq_one
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by constructor <;> intro <;> linarith⟩
  · -- take `u = 1{x = 1}`, increasing
    have hu : Monotone fun x : Fin 2 => if x = 1 then (1 : ℝ) else 0 := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have := h _ hu
    simp at this
    linarith
  · unfold FOSD
    intro u hu
    have h01 : u 0 ≤ u 1 := hu (by decide)
    have e1 : φ 1 = 1 - φ 0 := by linarith
    have e2 : ψ 1 = 1 - ψ 0 := by linarith
    have key := mul_nonneg (sub_nonneg.2 h01) (sub_nonneg.2 h)
    simp only [Fin.sum_univ_two]
    rw [e1, e2]
    nlinarith [key]


end SargentStachurski.OperatorsFixedPoints
