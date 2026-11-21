import CompleteMarkets.RDStiemke
import InternationalFinancialMarkets.Spanning
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import CompleteMarkets.BPAssetPricing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import StochasticDiscounting.AssetPricing
import StochasticDiscounting.PerronFrobenius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CompleteMarkets.BPLognormal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import RecursiveUtility.PALogNormal
import Mathlib.Analysis.MeanInequalities
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two-period asset trading: arbitrage and state prices

AKMM, §16.4, pp. 473–476 (with fn. 3). There are `S` states tomorrow and `N` assets; `D` is the
`S × N` payoff matrix and `p` the vector of asset prices. A portfolio `θ` costs `pᵀθ` today and
pays `Dθ` tomorrow; the payoff over both dates is `Wθ` with `W = [−pᵀ; D]` (16.11), indexed by
`Option S` (`none` is date 0).

* The two verbal definitions of an arbitrage and the "arbitrage-free" conditions of p. 474 are all
  equivalent to the `W`-form, `Wθ ≥ 0`, `Wθ ≠ 0` (`tp_isArbitrage_iff_book`,
  `tp_noArbitrage_iff_free`).
* The attainable set `M` (`tpAttainable`); an arbitrage is a nonzero nonnegative element of `M`
  (`tp_noArbitrage_iff_attainable`).
* Arrow securities have strictly positive prices (`tp_arrow_price_pos`); the law of one price
  (`tp_law_of_one_price`, `tp_loop_assets`) and (16.12) from it (`eq_16_12`).
* (16.13): the consumption prices `q̂ = (1, q)` are orthogonal to `M` (`eq_16_13`).
* **The fundamental theorem of asset pricing**: no arbitrage iff there are state prices
  `q ≫ 0` with `p = Dᵀq` (`tp_ftap`), proved from Stiemke's lemma (Miao's `rd_stiemke`).
* Completeness: markets are complete iff `rank D = S` (`tp_complete_iff_rank`, Obstfeld and
  Rogoff's `spans_iff_rank`); state prices are unique iff `rank D = S`
  (`tp_statePrices_unique_iff_rank`); for `N = S` they are `q = (Dᵀ)⁻¹p`
  (`tp_statePrices_inverse`), and for `N > S` they are computed from any invertible `S × S` block
  of `D` (`tp_statePrices_block`).

Departure: footnote 3's separation argument (separating `M` from the cone `K = ℝ₊^{S+1}`) does not
by itself give a functional that is strictly positive on `K ∖ {0}`; the proof here separates `M`
from the compact simplex in `K` (Stiemke's lemma). See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix

variable {S N : Type} [Fintype S] [Fintype N]

/-- AKMM, (16.11), p. 474: the `(S + 1) × N` matrix `W = [−pᵀ; D]` of payoffs today (`none`) and
in each state tomorrow (`some s`). -/
def tpW (p : N → ℝ) (D : Matrix S N ℝ) : Matrix (Option S) N ℝ :=
  Matrix.of fun k n => Option.elim k (-p n) fun s => D s n

omit [Fintype S] in
/-- The date-0 entry of `Wθ` is minus the cost of the portfolio. -/
theorem tp_W_none (p : N → ℝ) (D : Matrix S N ℝ) (θ : N → ℝ) :
    (tpW p D *ᵥ θ) none = -(p ⬝ᵥ θ) := by
  simp only [mulVec, dotProduct, tpW, Matrix.of_apply, Option.elim, neg_mul,
    Finset.sum_neg_distrib]

omit [Fintype S] in
/-- The state-`s` entry of `Wθ` is the portfolio payoff `(Dθ)(s)`. -/
theorem tp_W_some (p : N → ℝ) (D : Matrix S N ℝ) (θ : N → ℝ) (s : S) :
    (tpW p D *ᵥ θ) (some s) = (D *ᵥ θ) s := by
  simp only [mulVec, dotProduct, tpW, Matrix.of_apply, Option.elim]

/-- AKMM, p. 474: an arbitrage is a portfolio with `Wθ ≥ 0` and `Wθ ≠ 0`. -/
def tpIsArbitrage (p : N → ℝ) (D : Matrix S N ℝ) (θ : N → ℝ) : Prop :=
  (∀ k, 0 ≤ (tpW p D *ᵥ θ) k) ∧ tpW p D *ᵥ θ ≠ 0

/-- No arbitrage: no portfolio is an arbitrage. -/
def tpNoArbitrage (p : N → ℝ) (D : Matrix S N ℝ) : Prop := ∀ θ, ¬ tpIsArbitrage p D θ

/-- AKMM, p. 473: the book's first definition of a "free lunch": a portfolio that is free today,
`pᵀθ ≤ 0`, with `Dθ ≥ 0` and one strictly positive payoff, or one with `pᵀθ < 0` and `Dθ ≥ 0`. -/
def tpArbitrageBook (p : N → ℝ) (D : Matrix S N ℝ) (θ : N → ℝ) : Prop :=
  (p ⬝ᵥ θ ≤ 0 ∧ (∀ s, 0 ≤ (D *ᵥ θ) s) ∧ ∃ s, 0 < (D *ᵥ θ) s) ∨
    (p ⬝ᵥ θ < 0 ∧ ∀ s, 0 ≤ (D *ᵥ θ) s)

omit [Fintype S] in
/-- AKMM, pp. 473–474: the two definitions of an arbitrage agree. -/
theorem tp_isArbitrage_iff_book (p : N → ℝ) (D : Matrix S N ℝ) (θ : N → ℝ) :
    tpIsArbitrage p D θ ↔ tpArbitrageBook p D θ := by
  constructor
  · rintro ⟨hnn, hne⟩
    have h0 := hnn none
    rw [tp_W_none] at h0
    have hD : ∀ s, 0 ≤ (D *ᵥ θ) s := fun s => by simpa [tp_W_some] using hnn (some s)
    by_cases hp : p ⬝ᵥ θ < 0
    · exact Or.inr ⟨hp, hD⟩
    · refine Or.inl ⟨by linarith, hD, ?_⟩
      by_contra hcon
      push Not at hcon
      apply hne
      funext k
      cases k with
      | none => rw [tp_W_none]; simp only [Pi.zero_apply]; linarith
      | some s => rw [tp_W_some]; exact le_antisymm (hcon s) (hD s)
  · rintro (⟨hp, hD, s, hs⟩ | ⟨hp, hD⟩)
    · refine ⟨fun k => ?_, fun h => ?_⟩
      · cases k with
        | none => rw [tp_W_none]; linarith
        | some s => rw [tp_W_some]; exact hD s
      · have := congrFun h (some s)
        rw [tp_W_some] at this
        simp only [Pi.zero_apply] at this
        linarith
    · refine ⟨fun k => ?_, fun h => ?_⟩
      · cases k with
        | none => rw [tp_W_none]; linarith
        | some s => rw [tp_W_some]; exact hD s
      · have := congrFun h none
        rw [tp_W_none] at this
        simp only [Pi.zero_apply] at this
        linarith

/-- AKMM, p. 474: "markets are arbitrage-free if `Dθ ≥ 0` implies `pᵀθ ≥ 0` and `Dθ ≥ 0` with one
strict inequality implies `pᵀθ > 0`". -/
def tpArbitrageFree (p : N → ℝ) (D : Matrix S N ℝ) : Prop :=
  (∀ θ, (∀ s, 0 ≤ (D *ᵥ θ) s) → 0 ≤ p ⬝ᵥ θ) ∧
    ∀ θ, (∀ s, 0 ≤ (D *ᵥ θ) s) → (∃ s, 0 < (D *ᵥ θ) s) → 0 < p ⬝ᵥ θ

omit [Fintype S] in
/-- AKMM, p. 474: the arbitrage-free conditions are exactly the absence of arbitrage. -/
theorem tp_noArbitrage_iff_free (p : N → ℝ) (D : Matrix S N ℝ) :
    tpNoArbitrage p D ↔ tpArbitrageFree p D := by
  constructor
  · intro h
    refine ⟨fun θ hD => ?_, fun θ hD hs => ?_⟩
    · by_contra hc
      push Not at hc
      exact h θ ((tp_isArbitrage_iff_book p D θ).2 (Or.inr ⟨hc, hD⟩))
    · by_contra hc
      push Not at hc
      exact h θ ((tp_isArbitrage_iff_book p D θ).2 (Or.inl ⟨hc, hD, hs⟩))
  · rintro ⟨h1, h2⟩ θ hθ
    rcases (tp_isArbitrage_iff_book p D θ).1 hθ with ⟨hp, hD, hs⟩ | ⟨hp, hD⟩
    · linarith [h2 θ hD hs]
    · linarith [h1 θ hD]

/-- AKMM, p. 474: the set of attainable payoffs `M = {Wθ : θ ∈ ℝᴺ}`, a subspace of `ℝ^{S+1}`. -/
def tpAttainable (p : N → ℝ) (D : Matrix S N ℝ) : Submodule ℝ (Option S → ℝ) :=
  LinearMap.range (tpW p D).mulVecLin

omit [Fintype S] in
/-- AKMM, p. 474: there is an arbitrage iff `M` contains a nonzero nonnegative payoff. -/
theorem tp_noArbitrage_iff_attainable (p : N → ℝ) (D : Matrix S N ℝ) :
    tpNoArbitrage p D ↔ ∀ v ∈ tpAttainable p D, (∀ k, 0 ≤ v k) → v = 0 := by
  constructor
  · rintro h v ⟨θ, rfl⟩ hv
    by_contra hne
    exact h θ ⟨hv, hne⟩
  · rintro h θ ⟨hv, hne⟩
    exact hne (h _ ⟨θ, rfl⟩ hv)

/-- AKMM, p. 474: state prices for `(p, D)`: `q ≫ 0` with `p = Dᵀq`, i.e. (16.12)
`pⁿ = Σ_ω dⁿ(ω) q(ω)` for every asset. -/
def tpStatePrices (p : N → ℝ) (D : Matrix S N ℝ) (q : S → ℝ) : Prop :=
  (∀ s, 0 < q s) ∧ ∀ n, p n = ∑ s, D s n * q s

/-- AKMM, (16.13), p. 474: the consumption prices `q̂ = (1, q)`. -/
def tpQhat (q : S → ℝ) : Option S → ℝ := fun k => Option.elim k 1 q

/-- AKMM, (16.13), pp. 474–475: if `p = Dᵀq` then `q̂ = (1, q)` is orthogonal to every payoff
`Wθ`: `−pᵀθ + Σ_ω q(ω)(Dθ)(ω) = 0`. -/
theorem tp_qhat_orth {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : ∀ n, p n = ∑ s, D s n * q s) (θ : N → ℝ) :
    ∑ k, tpQhat q k * (tpW p D *ᵥ θ) k = 0 := by
  rw [Fintype.sum_option]
  simp only [tpQhat, Option.elim, tp_W_none, tp_W_some, one_mul]
  simp only [mulVec, dotProduct, hq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [neg_add_eq_zero]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun s _ => by ring

/-- AKMM, (16.13), p. 475: `q̂` is orthogonal to the set `M` of attainable payoffs. -/
theorem eq_16_13 {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : ∀ n, p n = ∑ s, D s n * q s) :
    ∀ x ∈ tpAttainable p D, ∑ k, tpQhat q k * x k = 0 := by
  rintro x ⟨θ, rfl⟩
  exact tp_qhat_orth hq θ

/-- AKMM, p. 475: state prices exclude arbitrage, since `pᵀθ = qᵀDθ` with `q ≫ 0`. -/
theorem tp_noArbitrage_of_statePrices {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) : tpNoArbitrage p D := by
  rintro θ ⟨hnn, hne⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  have hpos : 0 < (tpW p D *ᵥ θ) k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
  have hqh : ∀ k, 0 < tpQhat q k := fun k => by
    cases k with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using hq.1 s
  have : 0 < ∑ k, tpQhat q k * (tpW p D *ᵥ θ) k :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hqh j).le (hnn j))
      ⟨k, Finset.mem_univ k, mul_pos (hqh k) hpos⟩
  rw [tp_qhat_orth hq.2 θ] at this
  exact lt_irrefl 0 this

/-- **The fundamental theorem of asset pricing** (AKMM, pp. 475–476). Asset prices `p` admit no
arbitrage iff there are state prices `q ≫ 0` with `p = Dᵀq`. The hard direction is Stiemke's
lemma (`Miao.CompleteMarkets.rd_stiemke`) applied to `M`: a strictly positive `q̃` orthogonal to
`M`, normalised by `q̃₀ > 0`. -/
theorem tp_ftap (p : N → ℝ) (D : Matrix S N ℝ) :
    tpNoArbitrage p D ↔ ∃ q, tpStatePrices p D q := by
  classical
  constructor
  · intro h
    obtain ⟨qt, hpos, horth⟩ :=
      (Miao.CompleteMarkets.rd_stiemke (tpAttainable p D)).1
        ((tp_noArbitrage_iff_attainable p D).1 h)
    refine ⟨fun s => qt (some s) / qt none, fun s => div_pos (hpos _) (hpos _), fun n => ?_⟩
    have hn := horth (tpW p D *ᵥ Pi.single n 1) ⟨Pi.single n 1, rfl⟩
    rw [Fintype.sum_option] at hn
    simp only [tp_W_none, tp_W_some, mulVec_single_one, dotProduct_single, mul_one,
      Matrix.col_apply] at hn
    have h0 := hpos none
    have e : ∑ s, D s n * (qt (some s) / qt none) = (∑ s, qt (some s) * D s n) / qt none := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun s _ => by ring
    change p n = ∑ s, D s n * (qt (some s) / qt none)
    rw [e, eq_div_iff h0.ne']
    linarith
  · rintro ⟨q, hq⟩
    exact tp_noArbitrage_of_statePrices hq

omit [Fintype S] in
/-- AKMM, p. 474: under no arbitrage the price of an Arrow security (one unit in state `ω`, zero
otherwise) is strictly positive. -/
theorem tp_arrow_price_pos [Finite S] [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ}
    (h : tpNoArbitrage p D) {n : N} {ω : S} (hn : ∀ s, D s n = if s = ω then 1 else 0) :
    0 < p n := by
  have := Fintype.ofFinite S
  obtain ⟨q, hq⟩ := (tp_ftap p D).1 h
  rw [hq.2 n]
  simp only [hn, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact hq.1 ω

omit [Fintype S] in
/-- **The law of one price** (AKMM, p. 474). Under no arbitrage, two portfolios with identical
payoffs tomorrow have the same price today. -/
theorem tp_law_of_one_price [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} (h : tpNoArbitrage p D)
    {θ θ' : N → ℝ} (hD : D *ᵥ θ = D *ᵥ θ') : p ⬝ᵥ θ = p ⬝ᵥ θ' := by
  have := Fintype.ofFinite S
  obtain ⟨q, hq⟩ := (tp_ftap p D).1 h
  have e1 := tp_qhat_orth hq.2 θ
  have e2 := tp_qhat_orth hq.2 θ'
  rw [Fintype.sum_option] at e1 e2
  simp only [tpQhat, Option.elim, tp_W_none, tp_W_some, one_mul, hD] at e1 e2
  linarith

omit [Fintype S] in
/-- AKMM, p. 474: two assets with identical payoffs in every state trade at the same price. -/
theorem tp_loop_assets [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} (h : tpNoArbitrage p D)
    {n m : N} (hnm : ∀ s, D s n = D s m) : p n = p m := by
  classical
  have := tp_law_of_one_price h (θ := Pi.single n 1) (θ' := Pi.single m 1) (by
    funext s
    simp [hnm])
  simpa [dotProduct_single] using this

/-- AKMM, (16.12), p. 474: if the Arrow securities are traded, `a ω` paying one unit in state `ω`
at price `q ω`, the law of one price gives `pⁿ = Σ_ω dⁿ(ω) q(ω)` for every asset `n`: asset `n`
has the same payoff as the portfolio of `dⁿ(ω)` units of each Arrow security. -/
theorem eq_16_12 [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ}
    (h : tpNoArbitrage p D) (a : S → N) (ha : ∀ s ω, D s (a ω) = if s = ω then 1 else 0)
    (n : N) : p n = ∑ ω, D ω n * p (a ω) := by
  classical
  have hpay : D *ᵥ Pi.single n 1 = D *ᵥ (∑ ω, D ω n • Pi.single (a ω) 1) := by
    funext s
    rw [mulVec_sum]
    simp only [mulVec_smul, mulVec_single_one, Finset.sum_apply, Pi.smul_apply,
      Matrix.col_apply, ha, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  have := tp_law_of_one_price h hpay
  rw [dotProduct_single, mul_one, dotProduct_sum] at this
  rw [this]
  exact Finset.sum_congr rfl fun ω _ => by
    rw [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, mul_comm]

/-- AKMM, p. 472 and p. 475: markets are complete (every payoff `x ∈ ℝˢ` is `Dθ` for some
portfolio) iff `rank D = S` (Obstfeld and Rogoff's `spans_iff_rank`). -/
theorem tp_complete_iff_rank (D : Matrix S N ℝ) :
    Function.Surjective D.mulVec ↔ D.rank = Fintype.card S :=
  ObstfeldRogoff.InternationalFinancialMarkets.Spanning.spans_iff_rank D

/-- `rank D = S` iff `Dᵀ` is injective (rank–nullity). -/
theorem tp_rank_iff_transpose_injective (D : Matrix S N ℝ) :
    D.rank = Fintype.card S ↔ Function.Injective Dᵀ.mulVec := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  have hrn := LinearMap.finrank_range_add_finrank_ker Dᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hinj : Function.Injective Dᵀ.mulVec ↔ LinearMap.ker Dᵀ.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rfl
  rw [hinj, ← Submodule.finrank_eq_zero]
  omega

/-- AKMM, p. 475: given state prices `q`, they are the only state prices iff markets are complete,
`rank D = S`. If `Dᵀv = 0` with `v ≠ 0`, then `q + εv` are also state prices for small `ε > 0`. -/
theorem tp_statePrices_unique_iff_rank {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) :
    (∀ q', tpStatePrices p D q' → q' = q) ↔ D.rank = Fintype.card S := by
  rw [tp_rank_iff_transpose_injective]
  constructor
  · intro huniq a b hab
    by_contra hne
    set v : S → ℝ := a - b with hv
    have hv0 : v ≠ 0 := sub_ne_zero.2 hne
    have hDv : ∀ n, ∑ s, D s n * v s = 0 := fun n => by
      have := congrFun hab n
      simp only [mulVec, dotProduct, transpose_apply] at this
      simp only [hv, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, this, sub_self]
    set T : ℝ := ∑ s, |v s| / q s with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hq.1 s).le
    set ε : ℝ := 1 / (1 + T) with hε
    have hε0 : 0 < ε := by positivity
    have hεT : ε * T < 1 := by
      rw [hε, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
      linarith
    have hq' : tpStatePrices p D (fun s => q s + ε * v s) := by
      refine ⟨fun s => ?_, fun n => ?_⟩
      · have hs : |v s| / q s ≤ T :=
          Finset.single_le_sum (f := fun s => |v s| / q s)
            (fun s _ => div_nonneg (abs_nonneg _) (hq.1 s).le) (Finset.mem_univ s)
        have h1 : ε * (|v s| / q s) < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs hε0.le) hεT
        have h2 : ε * |v s| < q s := by
          rw [mul_div_assoc', div_lt_one (hq.1 s)] at h1
          exact h1
        have h3 : -(ε * |v s|) ≤ ε * v s := by
          rw [← mul_neg]
          exact mul_le_mul_of_nonneg_left (neg_abs_le _) hε0.le
        linarith
      · simp only [mul_add, Finset.sum_add_distrib, ← hq.2 n]
        have : ∑ s, D s n * (ε * v s) = ε * ∑ s, D s n * v s := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        rw [this, hDv n, mul_zero, add_zero]
    have := congrFun (huniq _ hq') 
    apply hv0
    funext s
    have hs := this s
    simp only [add_eq_left, mul_eq_zero] at hs
    rcases hs with h | h
    · exact absurd h hε0.ne'
    · exact h
  · intro hinj q' hq'
    apply hinj
    funext n
    simp only [mulVec, dotProduct, transpose_apply]
    rw [← (show p n = ∑ s, D s n * q' s from hq'.2 n), hq.2 n]

/-- AKMM, p. 475: with as many assets as states and `D` invertible, the state prices are
`q = (Dᵀ)⁻¹p`. -/
theorem tp_statePrices_inverse [DecidableEq S] {p : S → ℝ} {D : Matrix S S ℝ} {q : S → ℝ}
    (hD : IsUnit D.det) (hq : ∀ n, p n = ∑ s, D s n * q s) : q = (Dᵀ)⁻¹ *ᵥ p := by
  have hp : p = Dᵀ *ᵥ q := funext fun n => by
    simp only [hq n, mulVec, dotProduct, transpose_apply]
  have hDt : IsUnit Dᵀ.det := by rwa [det_transpose]
  rw [hp, mulVec_mulVec, nonsing_inv_mul _ hDt, one_mulVec]

omit [Fintype N] in
/-- AKMM, p. 475: with redundant assets (`N > S`), the state prices are computed from any
`S` assets `e : S → N` whose `S × S` payoff block `B` is invertible: `q = (Bᵀ)⁻¹ (p ∘ e)`. -/
theorem tp_statePrices_block [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (e : S → N) (hB : IsUnit (D.submatrix id e).det) (hq : ∀ n, p n = ∑ s, D s n * q s) :
    q = ((D.submatrix id e)ᵀ)⁻¹ *ᵥ (p ∘ e) :=
  tp_statePrices_inverse hB fun n => by simp only [Function.comp_apply, hq (e n),
    submatrix_apply, id]

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two examples of §16.4

AKMM, §16.4, pp. 476–477 and p. 480.

* **Example 1** (complete markets, a stock and a bond): `D = [δ₁ 1; δ₂ 1]` with `δ₁ > δ₂`, rank 2
  (`ex1_complete`); the state prices `q = (Dᵀ)⁻¹p = (pˢ − δ₂pᵇ, δ₁pᵇ − pˢ)/(δ₁ − δ₂)`
  (`ex1_statePrices_eq`, `ex1_statePrices_formula`); no arbitrage iff `δ₁pᵇ > pˢ > δ₂pᵇ`
  (`ex1_noArbitrage_iff`), equivalently the returns do not dominate each other
  (`ex1_returns_iff`), and then both prices are positive (`ex1_prices_pos`); every payoff `x` is
  bought by `θ = D⁻¹x` at cost `((pˢ − pᵇδ₂)x₁ + (pᵇδ₁ − pˢ)x₂)/(δ₁ − δ₂)` (`ex1_value`), which is
  positive on nonzero nonnegative `x` (`ex1_value_pos`).
* **Example 2** (incomplete markets, one stock): `D = (δ₁, δ₂)ᵀ` (`ex2_incomplete`); with
  `δ₁ > δ₂ > 0` no arbitrage iff `pˢ > 0` (`ex2_noArbitrage_iff`); with `δ₁ = 2`, `δ₂ = 0.5`,
  `pˢ = 1` the state prices are exactly `q(1) ∈ (0, 0.5)`, `q(2) = 2 − 4q(1)`
  (`ex2_statePrices_iff`); the two agents' subjective state prices `(1/4, 1)` and `(1/3, 2/3)`
  (p. 480) both price the stock at 1 yet differ (`ex2_disagreement`).

Departure: the book writes the bond price in the value map as `p_f`; it is `pᵇ`.
-/

namespace AKMM.AssetPrices

open Matrix

/-- AKMM, p. 476: Example 1's payoff matrix, a stock paying `δ₁, δ₂` and a bond paying 1. -/
def ex1D (δ₁ δ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![δ₁, 1; δ₂, 1]

/-- AKMM, p. 476: Example 1's prices `p = (pˢ, pᵇ)`. -/
def ex1p (ps pb : ℝ) : Fin 2 → ℝ := ![ps, pb]

/-- AKMM, p. 476: `rank D = S = 2` when `δ₁ ≠ δ₂`, so markets are complete. -/
theorem ex1_complete {δ₁ δ₂ : ℝ} (h : δ₁ ≠ δ₂) : (ex1D δ₁ δ₂).rank = 2 := by
  have hdet : (ex1D δ₁ δ₂).det = δ₁ - δ₂ := by
    simp [ex1D, det_fin_two_of]
  have hu : IsUnit (ex1D δ₁ δ₂) := by
    rw [isUnit_iff_isUnit_det, hdet]
    exact (sub_ne_zero.2 h).isUnit
  simpa using rank_of_isUnit _ hu

/-- AKMM, p. 476: the state prices of Example 1. -/
noncomputable def ex1q (δ₁ δ₂ ps pb : ℝ) : Fin 2 → ℝ :=
  ![(ps - δ₂ * pb) / (δ₁ - δ₂), (δ₁ * pb - ps) / (δ₁ - δ₂)]

/-- AKMM, p. 476: `q = (Dᵀ)⁻¹p` solves `p = Dᵀq`. -/
theorem ex1_statePrices_formula {δ₁ δ₂ : ℝ} (h : δ₁ ≠ δ₂) (ps pb : ℝ) :
    ∀ n, ex1p ps pb n = ∑ s, ex1D δ₁ δ₂ s n * ex1q δ₁ δ₂ ps pb s := by
  have h' : δ₁ - δ₂ ≠ 0 := sub_ne_zero.2 h
  intro n
  fin_cases n <;> simp [ex1p, ex1D, ex1q, Fin.sum_univ_two] <;> field_simp <;> ring

/-- AKMM, p. 476: any `q` with `p = Dᵀq` is the formula `(pˢ − δ₂pᵇ, δ₁pᵇ − pˢ)/(δ₁ − δ₂)`. -/
theorem ex1_statePrices_eq {δ₁ δ₂ ps pb : ℝ} (h : δ₁ ≠ δ₂) {q : Fin 2 → ℝ}
    (hq : ∀ n, ex1p ps pb n = ∑ s, ex1D δ₁ δ₂ s n * q s) : q = ex1q δ₁ δ₂ ps pb := by
  have h' : δ₁ - δ₂ ≠ 0 := sub_ne_zero.2 h
  have h0 : ps = δ₁ * q 0 + δ₂ * q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 0
  have h1 : pb = q 0 + q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 1
  funext s
  fin_cases s <;> simp only [ex1q, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> rw [eq_div_iff h', h0, h1] <;> ring

/-- AKMM, p. 476: with `δ₁ > δ₂`, Example 1 has no arbitrage iff `δ₁pᵇ > pˢ > δ₂pᵇ`. -/
theorem ex1_noArbitrage_iff {δ₁ δ₂ : ℝ} (h : δ₂ < δ₁) (ps pb : ℝ) :
    tpNoArbitrage (ex1p ps pb) (ex1D δ₁ δ₂) ↔ δ₂ * pb < ps ∧ ps < δ₁ * pb := by
  have hd : 0 < δ₁ - δ₂ := sub_pos.2 h
  rw [tp_ftap]
  constructor
  · rintro ⟨q, hq⟩
    rw [ex1_statePrices_eq h.ne' hq.2] at hq
    have h0 := hq.1 0
    have h1 := hq.1 1
    simp only [ex1q, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨by linarith [(div_pos_iff_of_pos_right hd).1 h0],
      by linarith [(div_pos_iff_of_pos_right hd).1 h1]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ex1q δ₁ δ₂ ps pb, fun s => ?_, ex1_statePrices_formula h.ne' ps pb⟩
    fin_cases s
    · exact div_pos (by simp; linarith) hd
    · exact div_pos (by simp; linarith) hd

/-- AKMM, p. 476: for positive prices the arbitrage restrictions are that neither return
dominates the other, `δ₁/pˢ > 1/pᵇ > δ₂/pˢ`. -/
theorem ex1_returns_iff {δ₁ δ₂ ps pb : ℝ} (hps : 0 < ps) (hpb : 0 < pb) :
    (δ₂ * pb < ps ∧ ps < δ₁ * pb) ↔ (δ₂ / ps < 1 / pb ∧ 1 / pb < δ₁ / ps) := by
  rw [div_lt_div_iff₀ hps hpb, div_lt_div_iff₀ hpb hps]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

/-- AKMM, p. 476: under no arbitrage both asset prices in Example 1 are positive (the payoffs are
positive). -/
theorem ex1_prices_pos {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ : δ₂ < δ₁) {ps pb : ℝ}
    (h : tpNoArbitrage (ex1p ps pb) (ex1D δ₁ δ₂)) : 0 < ps ∧ 0 < pb := by
  obtain ⟨q, hq0, hq⟩ := (tp_ftap _ _).1 h
  have h0 : ps = δ₁ * q 0 + δ₂ * q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 0
  have h1 : pb = q 0 + q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 1
  have a := hq0 0
  have b := hq0 1
  constructor
  · rw [h0]; nlinarith [mul_pos (hδ₂.trans hδ) a, mul_pos hδ₂ b]
  · rw [h1]; linarith

/-- AKMM, p. 477: the portfolio `θ = D⁻¹x` generating the payoff `x`. -/
noncomputable def ex1θ (δ₁ δ₂ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(x 0 - x 1) / (δ₁ - δ₂), (δ₁ * x 1 - δ₂ * x 0) / (δ₁ - δ₂)]

/-- AKMM, p. 477: every payoff `x ∈ ℝ²` is attained, `Dθ = x`, at the cost
`pᵀθ = pᵀD⁻¹x = ((pˢ − pᵇδ₂)x₁ + (pᵇδ₁ − pˢ)x₂)/(δ₁ − δ₂)`. -/
theorem ex1_value {δ₁ δ₂ : ℝ} (h : δ₁ ≠ δ₂) (ps pb : ℝ) (x : Fin 2 → ℝ) :
    ex1D δ₁ δ₂ *ᵥ ex1θ δ₁ δ₂ x = x ∧
      ex1p ps pb ⬝ᵥ ex1θ δ₁ δ₂ x =
        ((ps - pb * δ₂) * x 0 + (pb * δ₁ - ps) * x 1) / (δ₁ - δ₂) := by
  have h' : δ₁ - δ₂ ≠ 0 := sub_ne_zero.2 h
  refine ⟨funext fun s => ?_, ?_⟩
  · fin_cases s <;> simp [ex1D, ex1θ, mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring
  · simp [ex1p, ex1θ, dotProduct, Fin.sum_univ_two]
    field_simp
    ring

/-- AKMM, p. 477: under the arbitrage conditions the value of every nonnegative nonzero payoff is
strictly positive. -/
theorem ex1_value_pos {δ₁ δ₂ ps pb : ℝ} (h : δ₂ < δ₁) (h1 : δ₂ * pb < ps) (h2 : ps < δ₁ * pb)
    {x : Fin 2 → ℝ} (hx : ∀ s, 0 ≤ x s) (hne : x ≠ 0) :
    0 < ((ps - pb * δ₂) * x 0 + (pb * δ₁ - ps) * x 1) / (δ₁ - δ₂) := by
  have hd : 0 < δ₁ - δ₂ := sub_pos.2 h
  apply div_pos _ hd
  have hx0 := hx 0
  have hx1 := hx 1
  have hor : 0 < x 0 ∨ 0 < x 1 := by
    by_contra hc
    push Not at hc
    apply hne
    funext s
    fin_cases s
    · exact le_antisymm hc.1 hx0
    · exact le_antisymm hc.2 hx1
  rcases hor with h0 | h0
  · nlinarith [mul_nonneg (by linarith : 0 ≤ pb * δ₁ - ps) hx1]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ ps - pb * δ₂) hx0]

/-- AKMM, p. 477: Example 2's payoff matrix, a single stock paying `δ₁, δ₂`. -/
def ex2D (δ₁ δ₂ : ℝ) : Matrix (Fin 2) Unit ℝ := fun s _ => ![δ₁, δ₂] s

/-- AKMM, p. 478: with one asset and two states markets are incomplete. -/
theorem ex2_incomplete (δ₁ δ₂ : ℝ) : ¬ Function.Surjective (ex2D δ₁ δ₂).mulVec :=
  ObstfeldRogoff.InternationalFinancialMarkets.Spanning.not_spans_of_card_lt (by simp)

/-- AKMM, p. 478: with `δ₁ > δ₂ > 0`, no arbitrage requires (and only requires) a positive stock
price. -/
theorem ex2_noArbitrage_iff {δ₁ δ₂ : ℝ} (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (ps : ℝ) :
    tpNoArbitrage (fun _ => ps) (ex2D δ₁ δ₂) ↔ 0 < ps := by
  rw [tp_ftap]
  constructor
  · rintro ⟨q, hq0, hq⟩
    have h : ps = δ₁ * q 0 + δ₂ * q 1 := by simpa [ex2D, Fin.sum_univ_two] using hq ()
    rw [h]
    have := hq0 0
    have := hq0 1
    positivity
  · intro hps
    refine ⟨![ps / (2 * δ₁), ps / (2 * δ₂)], fun s => ?_, fun _ => ?_⟩
    · fin_cases s
      · exact div_pos hps (by positivity)
      · exact div_pos hps (by positivity)
    · simp [ex2D, Fin.sum_univ_two]
      field_simp
      ring

/-- AKMM, p. 478: with `δ₁ = 2`, `δ₂ = 0.5` and `pˢ = 1`, `q` are state prices iff
`q(1) ∈ (0, 0.5)` and `q(2) = 2 − 4q(1)`; in particular they are not unique. -/
theorem ex2_statePrices_iff (q : Fin 2 → ℝ) :
    tpStatePrices (fun _ => 1) (ex2D 2 (1 / 2)) q ↔
      (0 < q 0 ∧ q 0 < 1 / 2) ∧ q 1 = 2 - 4 * q 0 := by
  constructor
  · rintro ⟨hq0, hq⟩
    have h := hq ()
    simp [ex2D, Fin.sum_univ_two] at h
    have := hq0 1
    refine ⟨⟨hq0 0, by linarith⟩, by linarith⟩
  · rintro ⟨⟨a, b⟩, c⟩
    refine ⟨fun s => ?_, fun _ => ?_⟩
    · fin_cases s
      · exact a
      · simp only [Fin.mk_one, c]; linarith
    · simp [ex2D, Fin.sum_univ_two, c]
      ring

/-- AKMM, p. 480: in Example 2 agents `i` and `j` with subjective state prices `qᵢ = (1/4, 1)` and
`qⱼ = (1/3, 2/3)` agree on the stock price `2qᵢ(1) + 0.5qᵢ(2) = 2qⱼ(1) + 0.5qⱼ(2) = 1` but
disagree on the value of consumption in each state. -/
theorem ex2_disagreement :
    tpStatePrices (fun _ => 1) (ex2D 2 (1 / 2)) ![1 / 4, 1] ∧
      tpStatePrices (fun _ => 1) (ex2D 2 (1 / 2)) ![1 / 3, 2 / 3] ∧
        (![1 / 4, 1] : Fin 2 → ℝ) ≠ ![1 / 3, 2 / 3] := by
  refine ⟨(ex2_statePrices_iff _).2 ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩,
    (ex2_statePrices_iff _).2 ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, fun h => ?_⟩
  have := congrFun h 0
  norm_num at this

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal portfolios, the budget set in state prices and subjective state prices

AKMM, §16.4, pp. 473 and 477–480. A consumption plan is `c : Option S → ℝ` (`none` is date 0);
the budget set (16.10) is `{c : c ≤ y + Wθ for some θ}`, and `tpBudgetPos` adds `c ≥ 0`.

* (16.10) in the book's two-line form (`eq_16_10`).
* **Optimum ⇒ no arbitrage** (p. 477): with strictly increasing utility, an optimal plan rules
  out arbitrage (`tp_noArbitrage_of_optimal`).
* **No arbitrage ⇒ an optimum exists** (p. 477): with `y ≥ 0` and `c ≥ 0` the budget set is
  compact under no arbitrage (`tp_budgetPos_isCompact`: bounded by the state prices,
  `q̂ᵀc ≤ q̂ᵀy`, and closed as the projection of a compact set), so a continuous utility attains its
  maximum (`tp_exists_optimal`); together, `tp_exists_optimal_iff`. Without `c ≥ 0` the claim is
  false (`tp_no_optimal_without_nonneg`).
* **(16.14)**: every budget-feasible plan satisfies the single state-price budget constraint
  (`tp_budget_single`); the set (16.14) is the budget set with binding date-1 constraints
  (`eq_16_14`), and the printed claim that it equals (16.10) is false
  (`eq_16_14_counterexample`); with complete markets the budget set is the Arrow–Debreu budget set
  (`tp_budget_complete`).
* **First-order conditions and (16.15)**: at an interior optimum with differentiable `U`,
  `ψpⁿ = Σ_ω η(ω)dⁿ(ω)` (`tp_portfolio_foc`), so `qᵢ(ω) = (∂U/∂cᵢ,₁(ω))/(∂U/∂cᵢ,₀)` are state
  prices (`eq_16_15`); expected power utility gives `qᵢ(ω) = βπ(ω)(cᵢ,₁(ω)/cᵢ,₀)^{−γ}`
  (`tp_crra_marginal`, `tp_crra_statePrice`), `βπ(ω)` if `γ = 0` (`tp_riskNeutral_statePrice`).
* **Agreement** (p. 480): agents always agree on asset prices; with complete markets they agree on
  state prices (`tp_agreement_complete`).

Departures: the existence result needs `c ≥ 0` and `y ≥ 0` (the book's (16.10) has no consumption
constraint); the first-order conditions are derived at an interior optimum; (16.14) is corrected as
above. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix Filter Topology

variable {S N : Type} [Fintype S] [Fintype N]

/-- AKMM, (16.10), p. 473: the budget set `B(p, yᵢ) = {c : c ≤ y + Wθ for some θ ∈ ℝᴺ}`. -/
def tpBudget (p : N → ℝ) (D : Matrix S N ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | ∃ θ, ∀ k, c k ≤ y k + (tpW p D *ᵥ θ) k}

/-- The budget set with nonnegative consumption. -/
def tpBudgetPos (p : N → ℝ) (D : Matrix S N ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | (∀ k, 0 ≤ c k) ∧ c ∈ tpBudget p D y}

omit [Fintype S] in
/-- AKMM, (16.10), p. 473: the budget set in the book's form `cᵢ,₀ + pᵀθ ≤ yᵢ,₀`,
`cᵢ,₁(ω) ≤ yᵢ,₁(ω) + d(ω)ᵀθ`. -/
theorem eq_16_10 (p : N → ℝ) (D : Matrix S N ℝ) (y c : Option S → ℝ) :
    c ∈ tpBudget p D y ↔
      ∃ θ, c none + p ⬝ᵥ θ ≤ y none ∧ ∀ s, c (some s) ≤ y (some s) + (D *ᵥ θ) s := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, ?_, fun s => ?_⟩
    · have := hθ none
      rw [tp_W_none] at this
      linarith
    · simpa [tp_W_some] using hθ (some s)
  · rintro ⟨θ, h0, h1⟩
    refine ⟨θ, fun k => ?_⟩
    cases k with
    | none => rw [tp_W_none]; linarith
    | some s => rw [tp_W_some]; exact h1 s

omit [Fintype S] in
/-- AKMM, p. 477: if an optimal plan exists for a strictly increasing utility, there is no
arbitrage: an arbitrage added to the optimal portfolio would raise utility. -/
theorem tp_noArbitrage_of_optimal {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    {U : (Option S → ℝ) → ℝ} (hU : StrictMono U) {c : Option S → ℝ}
    (hc : c ∈ tpBudgetPos p D y) (hopt : ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) :
    tpNoArbitrage p D := by
  rintro θa ⟨hnn, hne⟩
  obtain ⟨hc0, θ, hθ⟩ := hc
  have hmem : c + tpW p D *ᵥ θa ∈ tpBudgetPos p D y := by
    refine ⟨fun k => add_nonneg (hc0 k) (hnn k), θ + θa, fun k => ?_⟩
    simp only [Pi.add_apply, mulVec_add]
    linarith [hθ k]
  have hlt : c < c + tpW p D *ᵥ θa := by
    refine lt_of_le_of_ne (fun k => le_add_of_nonneg_right (hnn k)) fun h => hne ?_
    have := congrArg (fun z => z - c) h
    simpa using this.symm
  exact absurd (hopt _ hmem) (not_le.2 (hU hlt))

omit [Fintype S] in
/-- AKMM, p. 477: under no arbitrage, with `y ≥ 0`, the budget set with `c ≥ 0` is compact. The
state prices `q̂ ≫ 0` (`tp_ftap`) bound every feasible plan: `q̂ₖcₖ ≤ q̂ᵀ(y + x) = q̂ᵀy` for the
attainable `x`, and the set is the projection of the compact set of pairs `(c, x)`. -/
theorem tp_budgetPos_isCompact [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} (h : tpNoArbitrage p D)
    {y : Option S → ℝ} (hy : ∀ k, 0 ≤ y k) : IsCompact (tpBudgetPos p D y) := by
  have := Fintype.ofFinite S
  obtain ⟨q, hq⟩ := (tp_ftap p D).1 h
  have hqh : ∀ k, 0 < tpQhat q k := fun k => by
    cases k with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using hq.1 s
  set V : ℝ := ∑ k, tpQhat q k * y k with hV
  set b : Option S → ℝ := fun k => V / tpQhat q k with hb
  set K : Set ((Option S → ℝ) × (Option S → ℝ)) :=
    {z | (∀ k, 0 ≤ z.1 k) ∧ (∀ k, z.1 k ≤ y k + z.2 k) ∧ z.2 ∈ tpAttainable p D} with hK
  have hbound : ∀ x ∈ tpAttainable p D, (∀ k, 0 ≤ y k + x k) → ∀ k, y k + x k ≤ b k := by
    intro x hx hnn k
    have horth := eq_16_13 hq.2 x hx
    have hsum : ∑ j, tpQhat q j * (y j + x j) = V := by
      simp only [mul_add, Finset.sum_add_distrib, horth, add_zero, hV]
    have hle : tpQhat q k * (y k + x k) ≤ V := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun j => tpQhat q j * (y j + x j))
        (fun j _ => mul_nonneg (hqh j).le (hnn j)) (Finset.mem_univ k)
    rw [hb, le_div_iff₀ (hqh k)]
    linarith
  have hKsub : K ⊆ Set.Icc 0 b ×ˢ Set.Icc (-y) b := by
    rintro ⟨c, x⟩ ⟨h0, h1, hx⟩
    have hnn : ∀ k, 0 ≤ y k + x k := fun k => (h0 k).trans (h1 k)
    have hb' := hbound x hx hnn
    refine ⟨⟨fun k => h0 k, fun k => (h1 k).trans (hb' k)⟩, fun k => ?_, fun k => ?_⟩
    · simp only [Pi.neg_apply]
      linarith [hnn k]
    · linarith [hb' k, hy k]
  have hKclosed : IsClosed K := by
    have e1 : IsClosed {z : (Option S → ℝ) × (Option S → ℝ) | ∀ k, 0 ≤ z.1 k} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le continuous_const (by fun_prop)
    have e2 : IsClosed {z : (Option S → ℝ) × (Option S → ℝ) | ∀ k, z.1 k ≤ y k + z.2 k} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le (by fun_prop) (by fun_prop)
    have e3 : IsClosed {z : (Option S → ℝ) × (Option S → ℝ) | z.2 ∈ tpAttainable p D} :=
      (Submodule.closed_of_finiteDimensional (tpAttainable p D)).preimage continuous_snd
    exact e1.inter (e2.inter e3)
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have heq : tpBudgetPos p D y = Prod.fst '' K := by
    ext c
    constructor
    · rintro ⟨h0, θ, hθ⟩
      exact ⟨(c, tpW p D *ᵥ θ), ⟨h0, hθ, θ, rfl⟩, rfl⟩
    · rintro ⟨⟨c', x⟩, ⟨h0, h1, θ, rfl⟩, rfl⟩
      exact ⟨h0, θ, h1⟩
  rw [heq]
  exact hKc.image continuous_fst

omit [Fintype S] in
/-- The endowment is budget feasible. -/
theorem tp_endowment_mem {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    (hy : ∀ k, 0 ≤ y k) : y ∈ tpBudgetPos p D y :=
  ⟨hy, 0, fun k => by simp⟩

omit [Fintype S] in
/-- AKMM, p. 477: if there is no arbitrage and the utility function is continuous, the agent's
problem has a solution (with `y ≥ 0` and `c ≥ 0`). -/
theorem tp_exists_optimal [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} (h : tpNoArbitrage p D)
    {y : Option S → ℝ} (hy : ∀ k, 0 ≤ y k) {U : (Option S → ℝ) → ℝ}
    (hU : ContinuousOn U (tpBudgetPos p D y)) :
    ∃ c ∈ tpBudgetPos p D y, ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c := by
  have := Fintype.ofFinite S
  obtain ⟨c, hc, hmax⟩ := (tp_budgetPos_isCompact h hy).exists_isMaxOn
    ⟨y, tp_endowment_mem hy⟩ hU
  exact ⟨c, hc, fun c' hc' => hmax hc'⟩

omit [Fintype S] in
/-- AKMM, p. 477: for a continuous, strictly increasing utility, an optimal plan exists iff there
is no arbitrage. -/
theorem tp_exists_optimal_iff [Finite S] {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    (hy : ∀ k, 0 ≤ y k) {U : (Option S → ℝ) → ℝ} (hUc : Continuous U) (hU : StrictMono U) :
    (∃ c ∈ tpBudgetPos p D y, ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) ↔ tpNoArbitrage p D := by
  have := Fintype.ofFinite S
  exact ⟨fun ⟨_, hc, hopt⟩ => tp_noArbitrage_of_optimal hU hc hopt,
    fun h => tp_exists_optimal h hy hUc.continuousOn⟩

/-- One state and one Arrow security. -/
def tpArrowOne : Matrix Unit Unit ℝ := Matrix.of fun _ _ => 1

/-- Two states and only a riskless bond. -/
def tpBondOnly : Matrix (Fin 2) Unit ℝ := Matrix.of fun _ _ => 1

/-- AKMM, p. 477, the need for `c ≥ 0`: one state, one Arrow security at price 1 (no arbitrage),
and the continuous, strictly increasing `U(c) = c₀ + 2c₁`; without a lower bound on consumption
the budget set (16.10) has no optimum. -/
theorem tp_no_optimal_without_nonneg :
    tpNoArbitrage (fun _ : Unit => (1 : ℝ)) tpArrowOne ∧
      ¬ ∃ c ∈ tpBudget (fun _ : Unit => (1 : ℝ)) tpArrowOne 0,
        ∀ c' ∈ tpBudget (fun _ : Unit => (1 : ℝ)) tpArrowOne 0,
          c' none + 2 * c' (some ()) ≤ c none + 2 * c (some ()) := by
  refine ⟨(tp_ftap _ _).2 ⟨fun _ => 1, fun _ => one_pos, fun _ => by simp [tpArrowOne]⟩, ?_⟩
  rintro ⟨c, ⟨θ, hθ⟩, hopt⟩
  have e0 : ∀ θ : Unit → ℝ,
      (tpW (fun _ : Unit => (1 : ℝ)) tpArrowOne *ᵥ θ) none = -θ () := by
    intro θ
    rw [tp_W_none]
    simp [dotProduct]
  have e1 : ∀ (θ : Unit → ℝ) (s : Unit),
      (tpW (fun _ : Unit => (1 : ℝ)) tpArrowOne *ᵥ θ) (some s) = θ () := by
    intro θ s
    rw [tp_W_some]
    simp [mulVec, dotProduct, tpArrowOne]
  have hmem : (fun k => c k + Option.elim k (-1) fun _ => 1) ∈
      tpBudget (fun _ : Unit => (1 : ℝ)) tpArrowOne 0 := by
    refine ⟨fun _ => θ () + 1, fun k => ?_⟩
    have := hθ k
    cases k with
    | none =>
      rw [e0] at this ⊢
      simp only [Pi.zero_apply, Option.elim] at this ⊢
      linarith
    | some s =>
      rw [e1] at this ⊢
      simp only [Pi.zero_apply, Option.elim] at this ⊢
      linarith
  have := hopt _ hmem
  simp only [Option.elim] at this
  linarith

/-- AKMM, p. 477: with state prices `q`, every budget-feasible plan satisfies the single budget
constraint `cᵢ,₀ − yᵢ,₀ + Σ_ω q(ω)(cᵢ,₁(ω) − yᵢ,₁(ω)) ≤ 0`. -/
theorem tp_budget_single {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    {y c : Option S → ℝ} (hc : c ∈ tpBudget p D y) :
    c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0 := by
  obtain ⟨θ, hθ⟩ := hc
  have horth := tp_qhat_orth hq.2 θ
  rw [Fintype.sum_option] at horth
  simp only [tpQhat, Option.elim, one_mul] at horth
  have h0 := hθ none
  have hle : ∑ s, q s * (c (some s) - y (some s)) ≤ ∑ s, q s * (tpW p D *ᵥ θ) (some s) :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (by linarith [hθ (some s)])
      (hq.1 s).le
  linarith

/-- AKMM, (16.14), p. 478, as a set: the plans with `c₀ − y₀ + Σ_ω q(ω)(c₁(ω) − y₁(ω)) ≤ 0` and
`c₁ − y₁ ∈ span(D)`. -/
def tpBudgetQ (D : Matrix S N ℝ) (q : S → ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0 ∧
    (fun s => c (some s) - y (some s)) ∈ LinearMap.range D.mulVecLin}

/-- AKMM, p. 473: the budget set with binding date-1 constraints, `c₁ = y₁ + Dθ` ("since the
utility function is strictly increasing, the budget equations will bind"). -/
def tpBudgetBind (p : N → ℝ) (D : Matrix S N ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | ∃ θ, c none + p ⬝ᵥ θ ≤ y none ∧ ∀ s, c (some s) = y (some s) + (D *ᵥ θ) s}

/-- AKMM, (16.14), p. 478, corrected: under no arbitrage, with state prices `q`, the budget set
with binding date-1 constraints is `{c : c₀ − y₀ + Σ_ω q(ω)(c₁(ω) − y₁(ω)) ≤ 0,
c₁ − y₁ ∈ span(D)}`. -/
theorem eq_16_14 {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    (y : Option S → ℝ) : tpBudgetBind p D y = tpBudgetQ D q y := by
  have key : ∀ θ : N → ℝ, ∑ s, q s * (D *ᵥ θ) s = p ⬝ᵥ θ := fun θ => by
    have := tp_qhat_orth hq.2 θ
    rw [Fintype.sum_option] at this
    simp only [tpQhat, Option.elim, one_mul, tp_W_none, tp_W_some] at this
    linarith
  ext c
  constructor
  · rintro ⟨θ, h0, h1⟩
    have hc1' : ∀ s, c (some s) - y (some s) = (D *ᵥ θ) s := fun s => by
      rw [h1 s]; ring
    refine ⟨?_, θ, (funext hc1').symm⟩
    simp only [hc1']
    rw [key]
    linarith
  · rintro ⟨h0, θ, hθ⟩
    have hc1 : ∀ s, c (some s) - y (some s) = (D *ᵥ θ) s := fun s => (congrFun hθ s).symm
    refine ⟨θ, ?_, fun s => by linarith [hc1 s]⟩
    rw [← key]
    simp only [← hc1] at h0 ⊢
    linarith

/-- AKMM, p. 478: the printed claim that (16.10) "can be rewritten as" (16.14) is false: with two
states and only a bond (`q = (1/2, 1/2)`), the plan that throws away one unit in state 1 is in
(16.10) but violates the span restriction of (16.14). -/
theorem eq_16_14_counterexample :
    tpStatePrices (fun _ : Unit => (1 : ℝ)) tpBondOnly (fun _ : Fin 2 => 1 / 2) ∧
      (fun k : Option (Fin 2) => Option.elim k 0 fun s => if s = 0 then -1 else 0) ∈
        tpBudget (fun _ : Unit => (1 : ℝ)) tpBondOnly 0 ∧
      (fun k : Option (Fin 2) => Option.elim k 0 fun s => if s = 0 then -1 else 0) ∉
        tpBudgetQ tpBondOnly (fun _ : Fin 2 => 1 / 2) 0 := by
  refine ⟨⟨fun _ => by norm_num, fun _ => by simp [tpBondOnly]⟩,
    ⟨0, fun k => ?_⟩, ?_⟩
  · cases k with
    | none => simp
    | some s =>
      simp only [Option.elim, Pi.zero_apply, mulVec_zero, zero_add]
      split_ifs <;> norm_num
  · rintro ⟨-, θ, hθ⟩
    have h0 := congrFun hθ 0
    have h1 := congrFun hθ 1
    simp [mulVec, dotProduct, tpBondOnly] at h0 h1
    linarith

/-- AKMM, p. 480: with complete markets (`D` onto `ℝˢ`), the span restriction does not bind and
the budget set (16.10) is the Arrow–Debreu budget set with date-0 numeraire and state prices
`q`. -/
theorem tp_budget_complete {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    (hD : Function.Surjective D.mulVec) (y : Option S → ℝ) :
    tpBudget p D y = {c | c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0} := by
  ext c
  refine ⟨fun hc => tp_budget_single hq hc, fun hc => ?_⟩
  obtain ⟨θ, hθ⟩ := hD fun s => c (some s) - y (some s)
  have hbind : c ∈ tpBudgetBind p D y := by
    rw [eq_16_14 hq]
    exact ⟨hc, θ, hθ⟩
  obtain ⟨θ', h0, h1⟩ := hbind
  exact (eq_16_10 p D y c).2 ⟨θ', h0, fun s => (h1 s).le⟩

/-- A continuous linear functional on `ℝᴷ` is `L v = Σₖ vₖ L(eₖ)`. -/
theorem tp_clm_apply {K : Type} [Fintype K] [DecidableEq K] (L : (K → ℝ) →L[ℝ] ℝ)
    (v : K → ℝ) : L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : Pi.single k (v k) = v k • (Pi.single k (1 : ℝ) : K → ℝ) := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- AKMM, p. 479: the first-order condition for the holdings of asset `n`,
`−ψᵢpⁿ + Σ_ω ηᵢ(ω)dⁿ(ω) = 0`, where `ψᵢ = ∂Uᵢ/∂cᵢ,₀` and `ηᵢ(ω) = ∂Uᵢ/∂cᵢ,₁(ω)`, at an interior
optimum `c ≫ 0` of a differentiable utility. -/
theorem tp_portfolio_foc [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    {U : (Option S → ℝ) → ℝ} {DU : (Option S → ℝ) →L[ℝ] ℝ} {c : Option S → ℝ}
    (hc : c ∈ tpBudget p D y) (hpos : ∀ k, 0 < c k)
    (hopt : ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) (hU : HasFDerivAt U DU c) (n : N) :
    DU (Pi.single none 1) * p n = ∑ s, DU (Pi.single (some s) 1) * D s n := by
  classical
  obtain ⟨θ, hθ⟩ := hc
  set v : Option S → ℝ := tpW p D *ᵥ Pi.single n 1 with hv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c + t • v ∈ tpBudgetPos p D y := by
    have hk : ∀ k, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c k + t * v k := fun k =>
      ((by fun_prop : Continuous fun t : ℝ => c k + t * v k).tendsto' 0 (c k)
        (by simp)).eventually (lt_mem_nhds (hpos k))
    filter_upwards [Filter.eventually_all.2 hk] with t ht
    refine ⟨fun k => by simpa using (ht k).le, θ + t • Pi.single n 1, fun k => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul, hv]
    linarith [hθ k]
  have hmax : IsLocalMax (fun t : ℝ => U (c + t • v)) 0 := by
    filter_upwards [hev] with t ht
    simpa using hopt _ ht
  have hU' : HasFDerivAt U DU (c + (0 : ℝ) • v) := by simpa using hU
  have hl : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  have h0 := hmax.hasDerivAt_eq_zero (hU'.comp_hasDerivAt (0 : ℝ) hl)
  rw [tp_clm_apply DU v, Fintype.sum_option] at h0
  simp only [hv, mulVec_single_one, Matrix.col_apply, tpW, Matrix.of_apply,
    Option.elim] at h0
  have hs : ∑ s, D s n * DU (Pi.single (some s) 1) = ∑ s, DU (Pi.single (some s) 1) * D s n :=
    Finset.sum_congr rfl fun s _ => mul_comm _ _
  linarith

/-- AKMM, (16.15), p. 479: at an interior optimum with positive marginal utilities, the subjective
state prices `qᵢ(ω) = (∂Uᵢ/∂cᵢ,₁(ω))/(∂Uᵢ/∂cᵢ,₀)` are state prices: `pⁿ = Σ_ω dⁿ(ω)qᵢ(ω)`. -/
theorem eq_16_15 [DecidableEq S] {p : N → ℝ} {D : Matrix S N ℝ} {y : Option S → ℝ}
    {U : (Option S → ℝ) → ℝ} {DU : (Option S → ℝ) →L[ℝ] ℝ} {c : Option S → ℝ}
    (hc : c ∈ tpBudget p D y) (hpos : ∀ k, 0 < c k)
    (hopt : ∀ c' ∈ tpBudgetPos p D y, U c' ≤ U c) (hU : HasFDerivAt U DU c)
    (hMU : ∀ k, 0 < DU (Pi.single k 1)) :
    tpStatePrices p D fun s => DU (Pi.single (some s) 1) / DU (Pi.single none 1) := by
  refine ⟨fun s => div_pos (hMU _) (hMU _), fun n => ?_⟩
  have h := tp_portfolio_foc hc hpos hopt hU n
  have h0 := (hMU none).ne'
  change p n = ∑ s, D s n * (DU (Pi.single (some s) 1) / DU (Pi.single none 1))
  have e : ∑ s, D s n * (DU (Pi.single (some s) 1) / DU (Pi.single none 1)) =
      (∑ s, DU (Pi.single (some s) 1) * D s n) / DU (Pi.single none 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, ← h]
  field_simp

/-- AKMM, p. 479: the marginal utility of the power felicity `x^{1−γ}/(1−γ)` is `x^{−γ}`. -/
theorem tp_crra_marginal {γ x : ℝ} (hγ : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun z => z ^ (1 - γ) / (1 - γ)) (x ^ (-γ)) x := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hx.ne')).div_const (1 - γ)
  convert this using 1
  rw [show (1 - γ - 1 : ℝ) = -γ by ring]
  field_simp

/-- AKMM, p. 479: with expected power utility, marginal utilities `c₀^{−γ}` and
`βπ(ω)c₁(ω)^{−γ}` give the state prices `qᵢ(ω) = βπ(ω)(cᵢ,₁(ω)/cᵢ,₀)^{−γ}`. -/
theorem tp_crra_statePrice {β pr γ c0 c1 : ℝ} (hc0 : 0 < c0) (hc1 : 0 < c1) :
    β * pr * c1 ^ (-γ) / c0 ^ (-γ) = β * pr * (c1 / c0) ^ (-γ) := by
  rw [Real.div_rpow hc1.le hc0.le, mul_div_assoc]

/-- AKMM, p. 479: a risk-neutral agent (`γ = 0`) has state prices `βπ(ω)`. -/
theorem tp_riskNeutral_statePrice (β pr c0 c1 : ℝ) :
    β * pr * (c1 / c0) ^ (-(0 : ℝ)) = β * pr := by
  simp

/-- AKMM, p. 480: agents agree on asset prices (both sets of subjective state prices price every
asset at `p`); with complete markets, `rank D = S`, they also agree on state prices. -/
theorem tp_agreement_complete {p : N → ℝ} {D : Matrix S N ℝ} {qi qj : S → ℝ}
    (hi : ∀ n, p n = ∑ s, D s n * qi s) (hj : ∀ n, p n = ∑ s, D s n * qj s)
    (hD : D.rank = Fintype.card S) : qi = qj := by
  apply (tp_rank_iff_transpose_injective D).1 hD
  funext n
  simp only [mulVec, dotProduct, transpose_apply]
  rw [← hi n, ← hj n]

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stochastic discount factor, risk premia and risk-neutral probabilities

AKMM, §16.4, pp. 480–482. The states have probabilities `π ≫ 0` summing to one; expectations and
covariances are Miao's `bp_E π` and `bp_Cov π` (`Miao.CompleteMarkets`).

* The SDF `M(ω) = q(ω)/π(ω)` (`sdfM`); `pⁿ = E[dⁿM]` (`sdf_price`) and `1 = E[RⁿM]`
  (`sdf_return`); the riskless bond `pᵇ = Σ_ω q(ω) = E[M] = 1/R_f` (`sdf_bond`).
* Risk-neutral pricing (16.16): with `M ≡ β`, `pᵇ = β` and `pⁿ = E[dⁿ]/R_f` (`eq_16_16`).
* The risk adjustment: `pⁿ = E[dⁿ]/R_f − (−Cov(dⁿ, M))` (`sdf_risk_adjustment`).
* (16.17), corrected: `1 = E[Rⁿ]E[M] + Cov(Rⁿ, M)` and `E[Rⁿ] − R_f = −Cov(Rⁿ, M)/E[M]`
  (`eq_16_17`); the printed `1 = E[RⁿM] + Cov(Rⁿ, M)` fails (`eq_16_17_printed_counterexample`).
* Risk-neutral probabilities (16.18): `π* = q/Σq` is positive and sums to one
  (`riskNeutral_pos`, `riskNeutral_sum`), `pⁿ = E*[dⁿ]/R_f` (`eq_16_18`); with complete markets
  `π*` is unique (`riskNeutral_unique_of_complete`), and when a riskless bond is traded `π*` is
  unique iff markets are complete (`riskNeutral_unique_iff`).

Departure: (16.17) is printed as `1 = E[RM] + Cov(R, M)`; and "`π*` is unique if markets are
complete, otherwise there may be many" is proved in the form above (with a bond, uniqueness of `π*`
is equivalent to completeness). See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix Miao.CompleteMarkets

variable {S N : Type} [Fintype S] [Fintype N]

/-- AKMM, p. 480: the stochastic discount factor `M(ω) = q(ω)/π(ω)`. -/
noncomputable def sdfM (q pr : S → ℝ) : S → ℝ := fun s => q s / pr s

omit [Fintype S] in
/-- `π(ω)M(ω) = q(ω)`. -/
theorem sdf_mul_M {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s) (s : S) : pr s * sdfM q pr s = q s := by
  have := (hpr s).ne'
  simp only [sdfM]
  field_simp

omit [Fintype N] in
/-- AKMM, p. 480: `pⁿ = Σ_ω dⁿ(ω)q(ω) = E[dⁿ(ω)M(ω)]`. -/
theorem sdf_price {p : N → ℝ} {D : Matrix S N ℝ} {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hq : ∀ n, p n = ∑ s, D s n * q s) (n : N) :
    p n = bp_E pr fun s => D s n * sdfM q pr s := by
  rw [hq n, bp_E]
  exact Finset.sum_congr rfl fun s _ => by rw [mul_left_comm, sdf_mul_M hpr]

omit [Fintype N] in
/-- AKMM, p. 480: the return `Rⁿ(ω) = dⁿ(ω)/pⁿ` satisfies `1 = E[Rⁿ(ω)M(ω)]`. -/
theorem sdf_return {p : N → ℝ} {D : Matrix S N ℝ} {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hq : ∀ n, p n = ∑ s, D s n * q s) {n : N} (hp : p n ≠ 0) :
    bp_E pr (fun s => D s n / p n * sdfM q pr s) = 1 := by
  have := eq_13_30 pr (sdfM q pr) (fun s => D s n) (p n) hp (by
    rw [sdf_price hpr hq n]
    exact Finset.sum_congr rfl fun s _ => by ring)
  rw [← this]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype N] in
/-- AKMM, p. 481: a riskless bond (payoff 1 in every state) costs `pᵇ = Σ_ω q(ω) = E[M]`, so
`R_f = 1/E[M]`. -/
theorem sdf_bond {p : N → ℝ} {D : Matrix S N ℝ} {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hq : ∀ n, p n = ∑ s, D s n * q s) {b : N} (hb : ∀ s, D s b = 1) :
    p b = ∑ s, q s ∧ p b = bp_E pr (sdfM q pr) := by
  refine ⟨by simp [hq b, hb], ?_⟩
  rw [sdf_price hpr hq b]
  simp [hb]

omit [Fintype N] in
/-- AKMM, (16.16), p. 480: if agents are risk neutral, `M(ω) = β` in every state, then the bond
price is `pᵇ = 1/R_f = E[M] = β` and every asset is priced by its expected payoff discounted at
the riskless rate, `pⁿ = E[dⁿ]/R_f` with `R_f = 1/β`. -/
theorem eq_16_16 {p : N → ℝ} {D : Matrix S N ℝ} {pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hpr1 : ∑ s, pr s = 1) {β : ℝ} (hβ : 0 < β) (hq : ∀ n, p n = ∑ s, D s n * (β * pr s))
    (n : N) :
    bp_E pr (sdfM (fun s => β * pr s) pr) = β ∧ p n = bp_E pr (fun s => D s n) / (1 / β) := by
  have hM : sdfM (fun s => β * pr s) pr = fun _ => β := funext fun s => by
    simp only [sdfM]
    field_simp [(hpr s).ne']
  refine ⟨by rw [hM, bp_E_const pr hpr1], ?_⟩
  rw [sdf_price hpr hq n, hM, div_div_eq_mul_div, div_one]
  simp only [bp_E, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- AKMM, p. 481: the risk adjustment. With `R_f = 1/E[M]`,
`pⁿ = E[dⁿ]E[M] + Cov(dⁿ, M) = E[dⁿ]/R_f − (−Cov(dⁿ, M))`. -/
theorem sdf_risk_adjustment {pr d M : S → ℝ} {pn : ℝ}
    (hp : pn = bp_E pr fun s => d s * M s) :
    pn = bp_E pr d * bp_E pr M + bp_Cov pr d M ∧
      pn = bp_E pr d / (1 / bp_E pr M) - -bp_Cov pr d M := by
  have h1 : pn = bp_E pr d * bp_E pr M + bp_Cov pr d M := by
    rw [hp, bp_Cov]
    ring
  refine ⟨h1, ?_⟩
  rw [h1]
  field_simp
  ring

/-- AKMM, (16.17), p. 481, corrected: from `1 = E[RM]`,
`1 = E[R]E[M] + Cov(R, M)` and, with `R_f = 1/E[M]`, `E[R] − R_f = −Cov(R, M)/E[M]`. -/
theorem eq_16_17 {pr R M : S → ℝ} (hM : bp_E pr M ≠ 0) (h : bp_E pr (fun s => R s * M s) = 1) :
    1 = bp_E pr R * bp_E pr M + bp_Cov pr R M ∧
      bp_E pr R - 1 / bp_E pr M = -bp_Cov pr R M / bp_E pr M := by
  have h1 : 1 = bp_E pr R * bp_E pr M + bp_Cov pr R M := by
    rw [bp_Cov, h]
    ring
  refine ⟨h1, ?_⟩
  field_simp
  linarith

/-- AKMM, (16.17), p. 481: the printed `1 = E[RM] + Cov(R, M)` is false. Two equally likely
states, state prices `q = (1/4, 1/2)` (`M = (1/2, 1)`), and the Arrow security for state 1 (price
`1/4`, return `R = (4, 0)`): `E[RM] = 1` but `Cov(R, M) = −1/2`. -/
theorem eq_16_17_printed_counterexample :
    bp_E (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun s => ![4, 0] s * ![1 / 2, 1] s) = 1 ∧
      bp_Cov (fun _ : Fin 2 => (1 / 2 : ℝ)) ![4, 0] ![1 / 2, 1] = -1 / 2 ∧
      bp_E (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun s => ![4, 0] s * ![1 / 2, 1] s) +
        bp_Cov (fun _ : Fin 2 => (1 / 2 : ℝ)) ![4, 0] ![1 / 2, 1] ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [bp_Cov, bp_E, Fin.sum_univ_two] <;> norm_num

/-- AKMM, p. 481: the risk-neutral probabilities `π*(ω) = q(ω)/Σ_{ω'} q(ω')`. -/
noncomputable def riskNeutral (q : S → ℝ) : S → ℝ := fun s => q s / ∑ s', q s'

/-- AKMM, p. 481: with `q ≫ 0` the risk-neutral probabilities are strictly positive. -/
theorem riskNeutral_pos [Nonempty S] {q : S → ℝ} (hq : ∀ s, 0 < q s) (s : S) :
    0 < riskNeutral q s :=
  div_pos (hq s) (Finset.sum_pos (fun s _ => hq s) Finset.univ_nonempty)

/-- AKMM, p. 481: the risk-neutral probabilities sum to one. -/
theorem riskNeutral_sum [Nonempty S] {q : S → ℝ} (hq : ∀ s, 0 < q s) :
    ∑ s, riskNeutral q s = 1 := by
  have h : 0 < ∑ s, q s := Finset.sum_pos (fun s _ => hq s) Finset.univ_nonempty
  simp only [riskNeutral, ← Finset.sum_div]
  exact div_self h.ne'

omit [Fintype N] in
/-- AKMM, (16.18), p. 481: with `1/R_f = Σ_ω q(ω)`, `pⁿ = Σ_ω dⁿ(ω)π*(ω)/R_f = E*[dⁿ]/R_f`. -/
theorem eq_16_18 [Nonempty S] {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) (n : N) :
    p n = bp_E (riskNeutral q) (fun s => D s n) / (1 / ∑ s, q s) := by
  have h : 0 < ∑ s, q s := Finset.sum_pos (fun s _ => hq.1 s) Finset.univ_nonempty
  rw [hq.2 n, bp_E, div_div_eq_mul_div, div_one, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by
    simp only [riskNeutral]
    field_simp

/-- AKMM, p. 482: with complete markets the risk-neutral probability is unique (it is computed
from the unique state prices). -/
theorem riskNeutral_unique_of_complete {p : N → ℝ} {D : Matrix S N ℝ} {q q' : S → ℝ}
    (hq : tpStatePrices p D q) (hq' : tpStatePrices p D q') (hD : D.rank = Fintype.card S) :
    riskNeutral q' = riskNeutral q := by
  rw [((tp_statePrices_unique_iff_rank hq).2 hD) q' hq']

/-- AKMM, p. 482: when a riskless bond is traded, the risk-neutral probability is unique iff
markets are complete. (The bond fixes `Σ_ω q(ω) = pᵇ`, so `π*` determines `q`.) -/
theorem riskNeutral_unique_iff {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) {b : N} (hb : ∀ s, D s b = 1) :
    (∀ q', tpStatePrices p D q' → riskNeutral q' = riskNeutral q) ↔
      D.rank = Fintype.card S := by
  rw [← tp_statePrices_unique_iff_rank hq]
  have hsum : ∀ q', tpStatePrices p D q' → ∑ s, q' s = p b := fun q' h => by
    simp [h.2 b, hb]
  constructor
  · intro h q' hq'
    funext s
    have hne : ∑ s, q s ≠ 0 :=
      (Finset.sum_pos (fun s _ => hq.1 s) ⟨s, Finset.mem_univ s⟩).ne'
    have e := congrFun (h q' hq') s
    simp only [riskNeutral] at e
    rw [hsum q' hq', ← hsum q hq] at e
    exact (div_left_inj' hne).1 e
  · intro h q' hq'
    rw [h q' hq']

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The endowment economy: planner, Arrow–Debreu equilibrium and the First Welfare Theorem

AKMM, §16.3, pp. 469–472. A finite set `I` of agents with utilities `Uᵢ` over consumption plans
`cᵢ : H → ℝ`, where `H` is the (finite) set of date–history pairs `(t, ωᵗ)`; the aggregate
endowment is `y`. Marginal utilities are the partial derivatives `∂Uᵢ/∂cᵢ(h) = DUᵢ(e_h)` of a
Fréchet derivative `DUᵢ`.

* **Planner** (16.1)/(16.6): at an optimum of `Σᵢ λᵢUᵢ(cᵢ)` subject to feasibility, the weighted
  marginal utilities are equal across agents, `λᵢ∂Uᵢ/∂cᵢ(h) = μ(h)` (`eq_16_1_pair`, `eq_16_1`),
  proved from optimality by moving consumption between two agents.
* **Envelope** (16.2): if the planner value `U_λ` is differentiable, `∂U_λ/∂y(h) = μ(h)`
  (`eq_16_2`), for the value function defined as a supremum (`en_plannerValue`); and (16.3)
  (`eq_16_3`).
* **Arrow–Debreu** (16.4)/(16.7): at an optimum on the budget set, `∂Uᵢ/∂cᵢ(h) = αᵢp⁰(h)`
  (`eq_16_4_pair`, `eq_16_4`), `αᵢ > 0` when marginal utilities are positive (`eq_16_4_pos`), and
  (16.5) (`eq_16_5`).
* **First Welfare Theorem** (p. 471): with `λᵢ = 1/αᵢ` the equilibrium satisfies the planner's
  conditions with `μ = p⁰` (`en_weights_match`), and with concave utilities the equilibrium
  allocation solves the planner problem with those weights (`en_fwt_planner`), hence is Pareto
  optimal (`en_fwt_pareto`). The gradient inequality for concave utilities is
  `en_concave_le_fderiv`.

Departures: finitely many agents and a finite set of date–history pairs (a finite horizon); the
first-order conditions are derived at an optimum with differentiable utilities and positive
prices; the welfare theorem is proved for concave utilities (and in Pareto form for strictly
increasing ones it is Miao's `theorem_13_3_1`, for expected utility on the infinite tree). See
`docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Filter Topology

variable {I H : Type} [Fintype I] [Fintype H]

/-- The derivative of `t ↦ U(c + t v)` at `0` is `DU v`. -/
theorem en_line_deriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → ℝ}
    {DU : E →L[ℝ] ℝ} {c : E} (hU : HasFDerivAt U DU c) (v : E) :
    HasDerivAt (fun t : ℝ => U (c + t • v)) (DU v) 0 := by
  have hU' : HasFDerivAt U DU (c + (0 : ℝ) • v) := by simpa using hU
  have hl : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  exact hU'.comp_hasDerivAt (0 : ℝ) hl

/-- AKMM, p. 470: a feasible allocation, `Σᵢ cᵢ(h) ≤ y(h)` for every date and history. -/
def enFeasible (c : I → H → ℝ) (y : H → ℝ) : Prop := ∀ h, ∑ i, c i h ≤ y h

/-- AKMM, p. 470: `c` solves the planner problem with weights `λ`. -/
def enPlannerOpt (lam : I → ℝ) (U : I → (H → ℝ) → ℝ) (y : H → ℝ) (c : I → H → ℝ) : Prop :=
  enFeasible c y ∧ ∀ c', enFeasible c' y → ∑ i, lam i * U i (c' i) ≤ ∑ i, lam i * U i (c i)

omit [Fintype H] in
/-- AKMM, (16.1) and (16.6), p. 470: at a planner optimum, for any two agents,
`λᵢ ∂Uᵢ/∂cᵢ(h) = λⱼ ∂Uⱼ/∂cⱼ(h)`. -/
theorem eq_16_1_pair [Finite H] [DecidableEq H] {lam : I → ℝ} {U : I → (H → ℝ) → ℝ}
    {DU : I → (H → ℝ) →L[ℝ] ℝ} {y : H → ℝ} {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c)
    (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i)) (i j : I) (h : H) :
    lam i * DU i (Pi.single h 1) = lam j * DU j (Pi.single h 1) := by
  have := Fintype.ofFinite H
  classical
  by_cases hij : i = j
  · rw [hij]
  set w : I → H → ℝ := fun k =>
    (if k = i then Pi.single h 1 else 0) - (if k = j then Pi.single h 1 else 0) with hw
  have hsum : ∀ h', ∑ k, w k h' = 0 := fun h' => by
    simp only [hw, Pi.sub_apply, Finset.sum_sub_distrib]
    simp [apply_ite (fun f : H → ℝ => f h')]
  have hmax : IsLocalMax (fun t : ℝ => ∑ k, lam k * U k (c k + t • w k)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero]
    refine hopt.2 _ fun h' => ?_
    have := hopt.1 h'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum h', mul_zero, add_zero]
    exact this
  have hd : HasDerivAt (fun t : ℝ => ∑ k, lam k * U k (c k + t • w k))
      (∑ k, lam k * DU k (w k)) 0 :=
    HasDerivAt.fun_sum fun k _ => (en_line_deriv (hU k) (w k)).const_mul (lam k)
  have h0 := hmax.hasDerivAt_eq_zero hd
  simp only [hw, map_sub, apply_ite (DU _), map_zero, mul_sub, Finset.sum_sub_distrib] at h0
  simp only [mul_ite, mul_zero] at h0
  rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j] at h0
  simp only [Finset.mem_univ, ↓reduceIte] at h0
  linarith

omit [Fintype H] in
/-- AKMM, (16.1), p. 470: the weighted marginal utility of every agent equals a Lagrange
multiplier `μ(h)` independent of the agent. -/
theorem eq_16_1 [Finite H] [DecidableEq H] [Nonempty I] {lam : I → ℝ}
    {U : I → (H → ℝ) → ℝ} {DU : I → (H → ℝ) →L[ℝ] ℝ} {y : H → ℝ} {c : I → H → ℝ}
    (hopt : enPlannerOpt lam U y c) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i)) :
    ∃ μ : H → ℝ, ∀ i h, lam i * DU i (Pi.single h 1) = μ h := by
  have := Fintype.ofFinite H
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  exact ⟨fun h => lam i₀ * DU i₀ (Pi.single h 1), fun i h => eq_16_1_pair hopt hU i i₀ h⟩

/-- AKMM, p. 470: the planner's value `U_λ(y) = sup {Σᵢ λᵢUᵢ(cᵢ) : c feasible for y}`. -/
noncomputable def en_plannerValue (lam : I → ℝ) (U : I → (H → ℝ) → ℝ) (y : H → ℝ) : ℝ :=
  sSup {v | ∃ c, enFeasible c y ∧ v = ∑ i, lam i * U i (c i)}

omit [Fintype H] in
/-- At a planner optimum, `U_λ(y) = Σᵢ λᵢUᵢ(cᵢ)`. -/
theorem en_plannerValue_eq {lam : I → ℝ} {U : I → (H → ℝ) → ℝ} {y : H → ℝ}
    {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c) :
    en_plannerValue lam U y = ∑ i, lam i * U i (c i) := by
  refine IsGreatest.csSup_eq ⟨⟨c, hopt.1, rfl⟩, ?_⟩
  rintro v ⟨c', hc', rfl⟩
  exact hopt.2 c' hc'

omit [Fintype H] in
/-- `U_λ(y′) ≥ Σᵢ λᵢUᵢ(cᵢ′)` for every allocation feasible at `y′` (when the values are bounded
above). -/
theorem en_plannerValue_ge {lam : I → ℝ} {U : I → (H → ℝ) → ℝ} {y : H → ℝ}
    (hb : BddAbove {v | ∃ c, enFeasible c y ∧ v = ∑ i, lam i * U i (c i)})
    {c : I → H → ℝ} (hc : enFeasible c y) :
    ∑ i, lam i * U i (c i) ≤ en_plannerValue lam U y :=
  le_csSup hb ⟨c, hc, rfl⟩

omit [Fintype H] in
/-- AKMM, (16.2), p. 470 (envelope theorem): if the planner's value `U_λ` is differentiable at
`y`, its derivative with respect to the endowment of `h` is the multiplier,
`∂U_λ(y)/∂y(h) = λᵢ ∂Uᵢ/∂cᵢ(h) = μ(h)`, for every agent `i`. (Giving `h` to agent `i` is
feasible for `y + t e_h`, so `U_λ(y + t e_h) − λᵢUᵢ(cᵢ + t e_h) − Σ_{k≠i}λₖUₖ(cₖ)` has a minimum
at `t = 0`.) -/
theorem eq_16_2 [Finite H] [DecidableEq H] {lam : I → ℝ} {U : I → (H → ℝ) → ℝ}
    {DU : I → (H → ℝ) →L[ℝ] ℝ} {y : H → ℝ} {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c)
    (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hb : ∀ y', BddAbove {v | ∃ c, enFeasible c y' ∧ v = ∑ i, lam i * U i (c i)})
    {DW : (H → ℝ) →L[ℝ] ℝ} (hW : HasFDerivAt (en_plannerValue lam U) DW y) (i : I) (h : H) :
    DW (Pi.single h 1) = lam i * DU i (Pi.single h 1) := by
  have := Fintype.ofFinite H
  classical
  set w : I → H → ℝ := fun k => if k = i then Pi.single h 1 else 0 with hw
  have hmin : IsLocalMin (fun t : ℝ => en_plannerValue lam U (y + t • Pi.single h 1) -
      ∑ k, lam k * U k (c k + t • w k)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero, en_plannerValue_eq hopt, sub_self, sub_nonneg]
    refine en_plannerValue_ge (hb _) fun h' => ?_
    have := hopt.1 h'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have e : ∑ k, w k h' = (Pi.single h 1 : H → ℝ) h' := by
      simp [hw, apply_ite (fun f : H → ℝ => f h')]
    rw [e]
    linarith
  have hd : HasDerivAt (fun t : ℝ => en_plannerValue lam U (y + t • Pi.single h 1) -
      ∑ k, lam k * U k (c k + t • w k)) (DW (Pi.single h 1) - ∑ k, lam k * DU k (w k)) 0 :=
    (en_line_deriv hW _).sub
      (HasDerivAt.fun_sum fun k _ => (en_line_deriv (hU k) (w k)).const_mul (lam k))
  have h0 := hmin.hasDerivAt_eq_zero hd
  simp only [hw, apply_ite (DU _), map_zero, mul_ite, mul_zero] at h0
  rw [Finset.sum_ite_eq' Finset.univ i] at h0
  simp only [Finset.mem_univ, ↓reduceIte] at h0
  linarith

/-- AKMM, (16.3), p. 470: the planner equalises every agent's marginal rate of substitution with
the planner's, `(∂Uᵢ/∂cᵢ(h′))/(∂Uᵢ/∂cᵢ(h)) = (∂U_λ/∂y(h′))/(∂U_λ/∂y(h))`. -/
theorem eq_16_3 {lam MUh MUh' DWh DWh' : ℝ} (hlam : lam ≠ 0)
    (h1 : DWh = lam * MUh) (h2 : DWh' = lam * MUh') : MUh' / MUh = DWh' / DWh := by
  rw [h1, h2, mul_div_mul_left _ _ hlam]

/-- AKMM, p. 470: the Arrow–Debreu budget set `{c : Σ p⁰c ≤ Σ p⁰yᵢ}`. -/
def enBudgetAD (p yi : H → ℝ) : Set (H → ℝ) := {c | ∑ h, p h * c h ≤ ∑ h, p h * yi h}

/-- AKMM, (16.4), p. 471: at an optimum on the Arrow–Debreu budget set, with positive prices,
`(∂Uᵢ/∂cᵢ(h))/p⁰(h)` is the same for all `h` (moving value between two histories). -/
theorem eq_16_4_pair [DecidableEq H] {p yi ci : H → ℝ} {U : (H → ℝ) → ℝ}
    {DU : (H → ℝ) →L[ℝ] ℝ} (hp : ∀ h, 0 < p h) (hci : ci ∈ enBudgetAD p yi)
    (hopt : ∀ c ∈ enBudgetAD p yi, U c ≤ U ci) (hU : HasFDerivAt U DU ci) (h h' : H) :
    DU (Pi.single h 1) / p h = DU (Pi.single h' 1) / p h' := by
  set v : H → ℝ := (1 / p h) • Pi.single h 1 - (1 / p h') • Pi.single h' 1 with hv
  have hpv : ∑ k, p k * v k = 0 := by
    simp only [hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field_simp [(hp h).ne', (hp h').ne']
    ring
  have hmax : IsLocalMax (fun t : ℝ => U (ci + t • v)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero]
    refine hopt _ ?_
    have := hci
    simp only [enBudgetAD, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib] at this ⊢
    have e : ∑ k, p k * (t * v k) = t * ∑ k, p k * v k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hpv, mul_zero, add_zero]
    exact this
  have h0 := hmax.hasDerivAt_eq_zero (en_line_deriv hU v)
  simp only [hv, map_sub, map_smul, smul_eq_mul] at h0
  rw [div_eq_inv_mul, div_eq_inv_mul]
  simp only [one_div] at h0
  linarith

/-- AKMM, (16.4), p. 471: `∂Uᵢ/∂cᵢ(h) = αᵢp⁰(h)` for a multiplier `αᵢ` independent of `h`. -/
theorem eq_16_4 [DecidableEq H] [Nonempty H] {p yi ci : H → ℝ} {U : (H → ℝ) → ℝ}
    {DU : (H → ℝ) →L[ℝ] ℝ} (hp : ∀ h, 0 < p h) (hci : ci ∈ enBudgetAD p yi)
    (hopt : ∀ c ∈ enBudgetAD p yi, U c ≤ U ci) (hU : HasFDerivAt U DU ci) :
    ∃ α : ℝ, ∀ h, DU (Pi.single h 1) = α * p h := by
  obtain ⟨h₀⟩ := ‹Nonempty H›
  refine ⟨DU (Pi.single h₀ 1) / p h₀, fun h => ?_⟩
  rw [← eq_16_4_pair hp hci hopt hU h h₀]
  field_simp [(hp h).ne']

omit [Fintype H] in
/-- AKMM, p. 471: when marginal utility is positive (the budget constraint binds) the multiplier
is strictly positive, `αᵢ > 0`. -/
theorem eq_16_4_pos {p MU : H → ℝ} {α : ℝ} (hp : ∀ h, 0 < p h) (h : H) (hMU : 0 < MU h)
    (hα : ∀ h, MU h = α * p h) : 0 < α := by
  have := hα h
  rw [this] at hMU
  exact pos_of_mul_pos_left hMU (hp h).le

omit [Fintype H] in
/-- AKMM, (16.5), p. 471: the agent's marginal rate of substitution equals the price ratio,
`(∂Uᵢ/∂cᵢ(h′))/(∂Uᵢ/∂cᵢ(h)) = p⁰(h′)/p⁰(h)`. -/
theorem eq_16_5 {p MU : H → ℝ} {α : ℝ} (hα0 : α ≠ 0) (hα : ∀ h, MU h = α * p h) (h h' : H) :
    MU h' / MU h = p h' / p h := by
  rw [hα, hα, mul_div_mul_left _ _ hα0]

omit [Fintype I] [Fintype H] in
/-- AKMM, (16.6)–(16.7), p. 471: with the weights `λᵢ = 1/αᵢ` the equilibrium conditions
`∂Uᵢ/∂cᵢ(h) = αᵢp⁰(h)` are the planner's conditions with `μ = p⁰`. -/
theorem en_weights_match {MU : I → H → ℝ} {α : I → ℝ} {p : H → ℝ} (hα0 : ∀ i, α i ≠ 0)
    (hα : ∀ i h, MU i h = α i * p h) : ∀ i h, 1 / α i * MU i h = p h := by
  intro i h
  rw [hα, ← mul_assoc, one_div_mul_cancel (hα0 i), one_mul]

/-- The gradient inequality for a concave differentiable function, `U(x) ≤ U(c) + DU(x − c)`. -/
theorem en_concave_le_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → ℝ} (hU : ConcaveOn ℝ Set.univ U) {DU : E →L[ℝ] ℝ} {c : E}
    (hD : HasFDerivAt U DU c) (x : E) : U x ≤ U c + DU (x - c) := by
  have hs := (en_line_deriv hD (x - c)).tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      U x - U c ≤ t⁻¹ • (U (c + (0 + t) • (x - c)) - U (c + (0 : ℝ) • (x - c))) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hcv := hU.2 (Set.mem_univ c) (Set.mem_univ x) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    have hpt : (1 - t) • c + t • x = c + t • (x - c) := by module
    rw [hpt, smul_eq_mul, smul_eq_mul] at hcv
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    linarith
  have := ge_of_tendsto hs hev
  linarith

/-- **First Welfare Theorem** (AKMM, pp. 471–472). In an Arrow–Debreu equilibrium with concave,
differentiable utilities, first-order conditions `∂Uᵢ/∂cᵢ = αᵢp⁰` with `αᵢ > 0`, nonnegative
prices and market clearing, the equilibrium allocation solves the planner problem with weights
`λᵢ = 1/αᵢ`. -/
theorem en_fwt_planner {U : I → (H → ℝ) → ℝ} {DU : I → (H → ℝ) →L[ℝ] ℝ} {c : I → H → ℝ}
    {y : H → ℝ} {p : H → ℝ} {α : I → ℝ} (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i))
    (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i)) (hα0 : ∀ i, 0 < α i)
    (hα : ∀ i v, DU i v = α i * ∑ h, p h * v h) (hp : ∀ h, 0 ≤ p h)
    (hclear : ∀ h, ∑ i, c i h = y h) :
    enPlannerOpt (fun i => 1 / α i) U y c := by
  refine ⟨fun h => (hclear h).le, fun c' hc' => ?_⟩
  have hi : ∀ i, 1 / α i * U i (c' i) ≤ 1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h) :=
    fun i => by
      have := en_concave_le_fderiv (hconc i) (hU i) (c' i)
      rw [hα i] at this
      have ha := hα0 i
      have : 1 / α i * U i (c' i) ≤ 1 / α i * (U i (c i) + α i * ∑ h, p h * (c' i - c i) h) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      rw [mul_add, ← mul_assoc, one_div_mul_cancel ha.ne', one_mul] at this
      simpa using this
  have hsum : ∑ i, ∑ h, p h * (c' i h - c i h) ≤ 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_nonpos fun h _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hclear h]
    exact mul_nonpos_of_nonneg_of_nonpos (hp h) (by linarith [hc' h])
  calc ∑ i, 1 / α i * U i (c' i)
      ≤ ∑ i, (1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ∑ i, 1 / α i * U i (c i) + ∑ i, ∑ h, p h * (c' i h - c i h) := Finset.sum_add_distrib
    _ ≤ ∑ i, 1 / α i * U i (c i) := by linarith

omit [Fintype H] in
/-- AKMM, p. 471: a solution of the planner problem with positive weights is Pareto optimal: no
feasible allocation makes every agent at least as well off and one strictly better off. -/
theorem en_fwt_pareto {lam : I → ℝ} (hlam : ∀ i, 0 < lam i) {U : I → (H → ℝ) → ℝ}
    {y : H → ℝ} {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c) :
    ¬ ∃ c', enFeasible c' y ∧ (∀ i, U i (c i) ≤ U i (c' i)) ∧ ∃ i, U i (c i) < U i (c' i) := by
  rintro ⟨c', hc', hle, i, hlt⟩
  have h1 := hopt.2 c' hc'
  have h2 : ∑ k, lam k * U k (c k) < ∑ k, lam k * U k (c' k) :=
    Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hlam k).le)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt (hlam i)⟩
  linarith

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequential and Arrow–Debreu equilibrium, and the representative agent

AKMM, §16.3, pp. 471–472 ("Preview": the three results under complete markets) and §16.4,
p. 482 (representative agent), in the two-period economy of §16.4: a finite set `I` of agents with
endowments `yᵢ : Option S → ℝ` (`none` is date 0) and utilities `Uᵢ`, `N` assets with payoffs `D`.

* Sequential-markets equilibrium (`eqSeq`, p. 472: optimality on (16.10), goods and asset market
  clearing) and Arrow–Debreu equilibrium with date-0 numeraire and state prices `q`
  (`eqAD`).
* With complete markets the two coincide: a sequential equilibrium with strictly increasing
  utilities is an Arrow–Debreu equilibrium at the state prices of `p` (`eq_seq_to_ad`), and an
  Arrow–Debreu equilibrium is a sequential equilibrium at `p = Dᵀq` with portfolios that
  replicate the net trades and clear the asset markets (`eq_ad_to_seq`).
* **Representative agent** (p. 482): with complete markets, concave differentiable utilities and
  the first-order conditions `∂Uᵢ = αᵢ q̂`, the planner's value `U_λ`, `λᵢ = 1/αᵢ`, is bounded
  (`eq_planner_bound`); `c = y`, `θ = 0` solves the representative agent's problem at the same
  prices (`eq_repAgent`); and `q(ω) = (∂U_λ/∂y₁(ω))/(∂U_λ/∂y₀)` (`eq_repAgent_statePrice`).

Departure: the book states the three results for the infinite-horizon sequential economy; they
are proved here in its two-period version (where the budget sets are those of §16.4). On an
infinite tree the sequential budget (16.8) without a debt limit admits Ponzi schemes (Miao's
`rd_ponzi_arb`), and the equivalence is Miao's `theorem_13_5_1_if` under debt constraints and the
transversality condition. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix

variable {I S N : Type} [Fintype I] [Fintype S] [Fintype N]

/-- AKMM, p. 478: the Arrow–Debreu budget set with date-0 numeraire, state prices `q` and
`c ≥ 0`. -/
def eqBudgetAD (q : S → ℝ) (y : Option S → ℝ) : Set (Option S → ℝ) :=
  {c | (∀ k, 0 ≤ c k) ∧ c none - y none + ∑ s, q s * (c (some s) - y (some s)) ≤ 0}

/-- AKMM, p. 472: a sequential-markets competitive equilibrium `(c, θ, p)` of the two-period
economy: optimality on the budget set (16.10) with `c ≥ 0`, goods-market clearing and
asset-market clearing (zero net supply). -/
def eqSeq (U : I → (Option S → ℝ) → ℝ) (y : I → Option S → ℝ) (D : Matrix S N ℝ)
    (c : I → Option S → ℝ) (θ : I → N → ℝ) (p : N → ℝ) : Prop :=
  (∀ i, (∀ k, 0 ≤ c i k) ∧ (∀ k, c i k ≤ y i k + (tpW p D *ᵥ θ i) k) ∧
    ∀ c' ∈ tpBudgetPos p D (y i), U i c' ≤ U i (c i)) ∧
  (∀ k, ∑ i, c i k = ∑ i, y i k) ∧ ∑ i, θ i = 0

/-- AKMM, p. 471: an Arrow–Debreu equilibrium `(c, q)` with date-0 numeraire and state prices
`q ≫ 0`. -/
def eqAD (U : I → (Option S → ℝ) → ℝ) (y : I → Option S → ℝ) (c : I → Option S → ℝ)
    (q : S → ℝ) : Prop :=
  (∀ s, 0 < q s) ∧ (∀ i, c i ∈ eqBudgetAD q (y i) ∧ ∀ c' ∈ eqBudgetAD q (y i), U i c' ≤ U i (c i)) ∧
  ∀ k, ∑ i, c i k = ∑ i, y i k

/-- With complete markets the budget set with `c ≥ 0` is the Arrow–Debreu one. -/
theorem eq_budgetPos_complete {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) (hD : Function.Surjective D.mulVec) (y : Option S → ℝ) :
    tpBudgetPos p D y = eqBudgetAD q y := by
  ext c
  simp only [tpBudgetPos, eqBudgetAD, tp_budget_complete hq hD y]
  rfl

/-- AKMM, p. 472, first result (sequential ⇒ Arrow–Debreu): with complete markets and strictly
increasing utilities, a sequential equilibrium `(c, θ, p)` is an Arrow–Debreu equilibrium at the
state prices `q` of `p` (which exist by `tp_ftap`, the agents' optima excluding arbitrage). -/
theorem eq_seq_to_ad [Nonempty I] {U : I → (Option S → ℝ) → ℝ} (hU : ∀ i, StrictMono (U i))
    {y : I → Option S → ℝ} {D : Matrix S N ℝ} (hD : Function.Surjective D.mulVec)
    {c : I → Option S → ℝ} {θ : I → N → ℝ} {p : N → ℝ} (hE : eqSeq U y D c θ p) :
    ∃ q, tpStatePrices p D q ∧ eqAD U y c q := by
  obtain ⟨hopt, hclear, -⟩ := hE
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hNA : tpNoArbitrage p D :=
    tp_noArbitrage_of_optimal (hU i₀) ⟨(hopt i₀).1, θ i₀, (hopt i₀).2.1⟩ (hopt i₀).2.2
  obtain ⟨q, hq⟩ := (tp_ftap p D).1 hNA
  refine ⟨q, hq, hq.1, fun i => ?_, hclear⟩
  rw [← eq_budgetPos_complete hq hD]
  exact ⟨⟨(hopt i).1, θ i, (hopt i).2.1⟩, (hopt i).2.2⟩

/-- AKMM, p. 472, first result (Arrow–Debreu ⇒ sequential): with complete markets an Arrow–Debreu
equilibrium `(c, q)` is a sequential equilibrium at the prices `p = Dᵀq`; every agent but `i₀`
holds a portfolio replicating its date-1 net trade and agent `i₀` holds minus their sum, which
replicates its own net trade by goods-market clearing. -/
theorem eq_ad_to_seq (i₀ : I) {U : I → (Option S → ℝ) → ℝ}
    {y : I → Option S → ℝ} {D : Matrix S N ℝ} (hD : Function.Surjective D.mulVec)
    {c : I → Option S → ℝ} {q : S → ℝ} (hE : eqAD U y c q) :
    ∃ θ : I → N → ℝ, eqSeq U y D c θ (fun n => ∑ s, D s n * q s) := by
  classical
  obtain ⟨hq0, hopt, hclear⟩ := hE
  set p : N → ℝ := fun n => ∑ s, D s n * q s with hp
  have hq : tpStatePrices p D q := ⟨hq0, fun n => rfl⟩
  set θ' : I → N → ℝ := fun i => Function.surjInv hD fun s => c i (some s) - y i (some s)
  have hθ' : ∀ i, D *ᵥ θ' i = fun s => c i (some s) - y i (some s) := fun i =>
    Function.surjInv_eq hD _
  set θ : I → N → ℝ := fun i => if i = i₀ then -∑ j ∈ Finset.univ.erase i₀, θ' j else θ' i
  have hθ : ∀ i, D *ᵥ θ i = fun s => c i (some s) - y i (some s) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp only [θ, ↓reduceIte, mulVec_neg, mulVec_sum, hθ']
      funext s
      have hs := hclear (some s)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _
        (Finset.mem_univ i)] at hs
      simp only [Pi.neg_apply, Finset.sum_apply]
      rw [Finset.sum_sub_distrib]
      linarith
    · simp only [θ, hi, ↓reduceIte, hθ']
  have hsum : ∑ i, θ i = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    simp only [θ, ↓reduceIte]
    rw [neg_add_eq_zero]
    exact Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  refine ⟨θ, fun i => ⟨(hopt i).1.1, fun k => ?_, ?_⟩, hclear, hsum⟩
  · have hbind : c i ∈ tpBudgetBind p D (y i) := by
      rw [eq_16_14 hq]
      exact ⟨(hopt i).1.2, θ i, hθ i⟩
    obtain ⟨θ₁, h0, h1⟩ := hbind
    have hpθ : p ⬝ᵥ θ₁ = p ⬝ᵥ θ i := by
      have e1 := tp_qhat_orth hq.2 θ₁
      have e2 := tp_qhat_orth hq.2 (θ i)
      rw [Fintype.sum_option] at e1 e2
      simp only [tpQhat, Option.elim, one_mul, tp_W_none, tp_W_some] at e1 e2
      have : D *ᵥ θ₁ = D *ᵥ θ i := funext fun s => by
        rw [hθ i]; simp only; linarith [h1 s]
      rw [this] at e1
      linarith
    cases k with
    | none => rw [tp_W_none]; linarith
    | some s => rw [tp_W_some, hθ i]; simp
  · rw [eq_budgetPos_complete hq hD]
    exact (hopt i).2

/-- AKMM, p. 482: under the hypotheses of the First Welfare Theorem (`en_fwt_planner`), every
allocation feasible for an aggregate bundle `y′` has weighted utility at most
`Σᵢ λᵢUᵢ(cᵢ) + Σ_h p(h)(y′(h) − y(h))`, `λᵢ = 1/αᵢ`. -/
theorem eq_planner_bound {H : Type} [Fintype H] {U : I → (H → ℝ) → ℝ}
    {DU : I → (H → ℝ) →L[ℝ] ℝ} {c : I → H → ℝ} {y : H → ℝ} {p : H → ℝ} {α : I → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i)) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hα0 : ∀ i, 0 < α i) (hα : ∀ i v, DU i v = α i * ∑ h, p h * v h) (hp : ∀ h, 0 ≤ p h)
    (hclear : ∀ h, ∑ i, c i h = y h) {y' : H → ℝ} {c' : I → H → ℝ} (hc' : enFeasible c' y') :
    ∑ i, 1 / α i * U i (c' i) ≤ ∑ i, 1 / α i * U i (c i) + ∑ h, p h * (y' h - y h) := by
  have hi : ∀ i, 1 / α i * U i (c' i) ≤ 1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h) :=
    fun i => by
      have := en_concave_le_fderiv (hconc i) (hU i) (c' i)
      rw [hα i] at this
      have ha := hα0 i
      have : 1 / α i * U i (c' i) ≤ 1 / α i * (U i (c i) + α i * ∑ h, p h * (c' i - c i) h) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      rw [mul_add, ← mul_assoc, one_div_mul_cancel ha.ne', one_mul] at this
      simpa using this
  have hsum : ∑ i, ∑ h, p h * (c' i h - c i h) ≤ ∑ h, p h * (y' h - y h) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun h _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hclear h]
    exact mul_le_mul_of_nonneg_left (by linarith [hc' h]) (hp h)
  calc ∑ i, 1 / α i * U i (c' i)
      ≤ ∑ i, (1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ∑ i, 1 / α i * U i (c i) + ∑ i, ∑ h, p h * (c' i h - c i h) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- **Representative agent** (AKMM, p. 482). With complete markets, concave differentiable
utilities whose derivatives at the equilibrium are `αᵢ q̂` (the first-order conditions (16.4) at
the consumption prices `q̂ = (1, q)`), `αᵢ > 0`, and goods-market clearing, the aggregate
endowment `c = y` with `θ = 0` solves the problem of the representative agent with utility
`U_λ = Σᵢ λᵢUᵢ` (the planner's value, `λᵢ = 1/αᵢ`) at the same asset prices. -/
theorem eq_repAgent [Nonempty I] {U : I → (Option S → ℝ) → ℝ}
    {DU : I → (Option S → ℝ) →L[ℝ] ℝ} {c : I → Option S → ℝ} {ybar : Option S → ℝ}
    {α : I → ℝ} {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ} (hq : tpStatePrices p D q)
    (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i)) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hα0 : ∀ i, 0 < α i) (hα : ∀ i v, DU i v = α i * ∑ h, tpQhat q h * v h)
    (hclear : ∀ h, ∑ i, c i h = ybar h) :
    ybar ∈ tpBudget p D ybar ∧
      ∀ c' ∈ tpBudget p D ybar, en_plannerValue (fun i => 1 / α i) U c' ≤
        en_plannerValue (fun i => 1 / α i) U ybar := by
  classical
  have hp : ∀ h, 0 ≤ tpQhat q h := fun h => by
    cases h with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using (hq.1 s).le
  have hopt := en_fwt_planner hconc hU hα0 hα hp hclear
  refine ⟨⟨0, fun k => by simp⟩, fun c' hc' => ?_⟩
  rw [en_plannerValue_eq hopt]
  have hval : ∑ h, tpQhat q h * (c' h - ybar h) ≤ 0 := by
    have := tp_budget_single hq hc'
    rw [Fintype.sum_option]
    simpa [tpQhat] using this
  obtain ⟨i₀⟩ := ‹Nonempty I›
  refine csSup_le ⟨_, fun i => if i = i₀ then c' else 0, fun h => ?_, rfl⟩ ?_
  · simp [apply_ite (fun f : Option S → ℝ => f h)]
  · rintro v ⟨c'', hc'', rfl⟩
    have := eq_planner_bound hconc hU hα0 hα hp hclear hc''
    linarith

/-- AKMM, p. 482: with the weights `λᵢ = 1/αᵢ`, the state prices are the representative agent's
marginal rates of substitution, `q(ω) = (∂U_λ(y)/∂y₁(ω))/(∂U_λ(y)/∂y₀)`, whenever `U_λ` is
differentiable at the aggregate endowment (the boundedness needed by (16.2) is
`eq_planner_bound`). -/
theorem eq_repAgent_statePrice [Nonempty I] [DecidableEq S]
    {U : I → (Option S → ℝ) → ℝ} {DU : I → (Option S → ℝ) →L[ℝ] ℝ} {c : I → Option S → ℝ}
    {ybar : Option S → ℝ} {α : I → ℝ} {q : S → ℝ} (hq : ∀ s, 0 < q s)
    (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i)) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hα0 : ∀ i, 0 < α i) (hα : ∀ i v, DU i v = α i * ∑ h, tpQhat q h * v h)
    (hclear : ∀ h, ∑ i, c i h = ybar h) {DW : (Option S → ℝ) →L[ℝ] ℝ}
    (hW : HasFDerivAt (en_plannerValue (fun i => 1 / α i) U) DW ybar) (s : S) :
    q s = DW (Pi.single (some s) 1) / DW (Pi.single none 1) := by
  classical
  have hp : ∀ h, 0 ≤ tpQhat q h := fun h => by
    cases h with
    | none => simp [tpQhat]
    | some s => simpa [tpQhat] using (hq s).le
  have hopt := en_fwt_planner hconc hU hα0 hα hp hclear
  have hb : ∀ y', BddAbove {v | ∃ c', enFeasible c' y' ∧
      v = ∑ i, 1 / α i * U i (c' i)} := fun y' =>
    ⟨_, by
      rintro v ⟨c', hc', rfl⟩
      exact eq_planner_bound hconc hU hα0 hα hp hclear hc'⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hMU : ∀ h, 1 / α i₀ * DU i₀ (Pi.single h 1) = tpQhat q h := fun h => by
    rw [hα i₀]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field_simp [(hα0 i₀).ne']
  rw [eq_16_2 hopt hU hb hW i₀, eq_16_2 hopt hU hb hW i₀, hMU, hMU]
  simp [tpQhat]

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic trading on a finite event tree: the fundamental theorem

AKMM, §16.5, pp. 482–483. A finite event tree (`DTree`): every node `h = ωᵗ` has at most one
parent (none at the root) and a depth `t`. Assets have ex-dividend prices `pₜ(ωᵗ)` and dividends
`dₜ(ωᵗ)`; a trading strategy `θ` generates the payoffs
`xₜ(ωᵗ) = Σₙ (pⁿₜ + dⁿₜ)θⁿₜ₋₁(ωᵗ⁻¹) − pⁿₜθⁿₜ(ωᵗ)`, with `θ₋₁ = 0` (`dtPayoff`).

* The payoffs are linear in the strategy (`dtPayoffLin`), and the deflated value of every payoff
  stream is the deflated pricing error summed over nodes (`dt_value_payoff`).
* An arbitrage is a strategy with payoffs `x ≥ 0`, `x ≠ 0` (`dtNoArbitrage`).
* **Dynamic fundamental theorem of asset pricing** (p. 483): no arbitrage iff there is a deflator
  `Q ≫ 0` with `Q(ωᵗ)pₜ(ωᵗ) = Σ_{ωᵗ⁺¹} Q(ωᵗ⁺¹)(pₜ₊₁ + dₜ₊₁)(ωᵗ⁺¹)` (`dt_ftap_deflator`, by
  Stiemke's lemma on the whole tree), iff there are one-step state prices
  `qₜ₊₁(ωₜ₊₁|ωᵗ) > 0` with the dynamic law of one price
  `pⁿₜ(ωᵗ) = Σ_{ωₜ₊₁}(dⁿₜ₊₁ + pⁿₜ₊₁)(ωᵗ⁺¹) qₜ₊₁(ωₜ₊₁|ωᵗ)` (`dt_ftap`); the deflator is the
  product of the one-step prices along the path (`dtDeflator`, `dt_deflator_parent`).
* With complete one-step markets at a node (the payoff matrix over the successors has full row
  rank) the one-step state prices at that node are unique (`dt_statePrices_unique`).
* The two-period economy of §16.4 is the tree of depth one (`dtTwoPeriod`).

Departure: a finite horizon. At terminal nodes the condition reads `p = 0` (assets bought at the
last date pay nothing). The infinite-horizon theorem (with Ponzi schemes and bubbles) is not
formalised; see Miao's `rd_ponzi_arb` and Theorems 13.4.1–13.4.2.
-/

namespace AKMM.AssetPrices

/-- A finite event tree: a parent map (`none` at the root) and a depth increasing by one from
parent to child. -/
structure DTree (Node : Type) where
  /-- The predecessor history `ωᵗ⁻¹` of `ωᵗ` (`none` at the root). -/
  parent : Node → Option Node
  /-- The date `t` of the node. -/
  depth : Node → ℕ
  /-- The date increases by one from a node to its successors. -/
  depth_parent : ∀ h g, parent h = some g → depth h = depth g + 1

/-- AKMM, §16.4 as a tree: the root `none` (date 0) and the `S` states `some s` at date 1. -/
def dtTwoPeriod (S : Type) : DTree (Option S) where
  parent := fun k => Option.elim k none fun _ => some none
  depth := fun k => Option.elim k 0 fun _ => 1
  depth_parent := by
    intro h g hg
    cases h with
    | none => simp at hg
    | some s =>
      simp only [Option.elim, Option.some.injEq] at hg
      subst hg
      rfl

variable {Node N : Type} [Fintype Node] [Fintype N]

/-- The holdings carried into node `h`: `θₜ₋₁(ωᵗ⁻¹)`, zero at the root. -/
def dtPrev (T : DTree Node) (θ : Node → N → ℝ) (h : Node) (n : N) : ℝ :=
  (T.parent h).elim 0 fun g => θ g n

/-- AKMM, p. 482: the payoffs generated by a trading strategy,
`xₜ(ωᵗ) = Σₙ (pⁿₜ(ωᵗ) + dⁿₜ(ωᵗ))θⁿₜ₋₁(ωᵗ⁻¹) − pⁿₜ(ωᵗ)θⁿₜ(ωᵗ)`. -/
def dtPayoff (T : DTree Node) (p d : Node → N → ℝ) (θ : Node → N → ℝ) : Node → ℝ :=
  fun h => ∑ n, ((p h n + d h n) * dtPrev T θ h n - p h n * θ h n)

/-- The payoff map is linear. -/
def dtPayoffLin (T : DTree Node) (p d : Node → N → ℝ) :
    (Node → N → ℝ) →ₗ[ℝ] (Node → ℝ) where
  toFun := dtPayoff T p d
  map_add' θ θ' := by
    funext h
    simp only [dtPayoff, dtPrev, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    cases T.parent h <;> simp <;> ring
  map_smul' a θ := by
    funext h
    simp only [dtPayoff, dtPrev, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    cases T.parent h <;> simp <;> ring

/-- AKMM, p. 483: an arbitrage is a trading strategy with nonnegative payoffs at every node, one
of them strictly positive. -/
def dtNoArbitrage (T : DTree Node) (p d : Node → N → ℝ) : Prop :=
  ∀ θ, ¬ ((∀ h, 0 ≤ dtPayoff T p d θ h) ∧ dtPayoff T p d θ ≠ 0)

/-- Sum over the successors of `h`. -/
theorem dt_sum_parent [DecidableEq Node] (T : DTree Node) (f : Node → Option Node → ℝ)
    (hf : ∀ h, f h none = 0) :
    ∑ h, f h (T.parent h) =
      ∑ g, ∑ h ∈ Finset.univ.filter (fun h => T.parent h = some g), f h (some g) := by
  have : ∀ h, f h (T.parent h) = ∑ g, if T.parent h = some g then f h (some g) else 0 := by
    intro h
    cases hp : T.parent h with
    | none => simp [hf]
    | some g0 => simp
  simp only [this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => (Finset.sum_filter _ _).symm

/-- The deflated value of the payoff stream of `θ` is
`Σ_h Σ_n θ(h, n)(Σ_{h' child of h} Q(h')(p + d)(h', n) − Q(h)p(h, n))`. -/
theorem dt_value_payoff [DecidableEq Node] (T : DTree Node) (p d : Node → N → ℝ)
    (Q : Node → ℝ) (θ : Node → N → ℝ) :
    ∑ h, Q h * dtPayoff T p d θ h =
      ∑ h, ∑ n, θ h n * (∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
        Q h' * (p h' n + d h' n) - Q h * p h n) := by
  simp only [dtPayoff, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · have := dt_sum_parent T (fun h o => ∑ n, Q h * ((p h n + d h n) * o.elim 0 fun g => θ g n))
      (fun h => by simp)
    simp only [dtPrev]
    rw [this]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Finset.sum_congr rfl fun h _ => by simp only [Option.elim]; ring
  · exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun n _ => by ring

/-- AKMM, p. 483, the fundamental theorem on a finite tree, deflator form: no arbitrage iff there
is `Q ≫ 0` with `Q(h)pⁿ(h) = Σ_{h' child of h} Q(h')(pⁿ(h') + dⁿ(h'))` at every node. -/
theorem dt_ftap_deflator [DecidableEq Node] (T : DTree Node) (p d : Node → N → ℝ) :
    dtNoArbitrage T p d ↔ ∃ Q : Node → ℝ, (∀ h, 0 < Q h) ∧ ∀ h n,
      Q h * p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
        Q h' * (p h' n + d h' n) := by
  classical
  have hst := Miao.CompleteMarkets.rd_stiemke (LinearMap.range (dtPayoffLin T p d))
  have hNA : dtNoArbitrage T p d ↔ ∀ v ∈ LinearMap.range (dtPayoffLin T p d),
      (∀ k, 0 ≤ v k) → v = 0 := by
    constructor
    · rintro h v ⟨θ, rfl⟩ hv
      by_contra hne
      exact h θ ⟨hv, hne⟩
    · rintro h θ ⟨hv, hne⟩
      exact hne (h _ ⟨θ, rfl⟩ hv)
  rw [hNA, hst]
  constructor
  · rintro ⟨Q, hQ, horth⟩
    refine ⟨Q, hQ, fun h n => ?_⟩
    have := horth _ ⟨fun h' n' => if h' = h ∧ n' = n then 1 else 0, rfl⟩
    change ∑ k, Q k * dtPayoff T p d _ k = 0 at this
    rw [dt_value_payoff] at this
    simp only [ite_mul, one_mul, zero_mul] at this
    rw [Finset.sum_eq_single h, Finset.sum_eq_single n] at this
    · simp only [and_self, ↓reduceIte] at this
      linarith
    · intro n' _ hn
      simp [hn]
    · simp
    · intro h' _ hh
      simp [hh]
    · simp
  · rintro ⟨Q, hQ, hpr⟩
    refine ⟨Q, hQ, ?_⟩
    rintro v ⟨θ, rfl⟩
    change ∑ k, Q k * dtPayoff T p d θ k = 0
    rw [dt_value_payoff]
    exact Finset.sum_eq_zero fun h _ => Finset.sum_eq_zero fun n _ => by rw [← hpr h n]; ring

/-- The deflator built from one-step state prices, `Q(ωᵗ) = Π_{s ≤ t} q(ωˢ)` (computed through
`k` generations). -/
def dtDeflatorAux (T : DTree Node) (q : Node → ℝ) : ℕ → Node → ℝ
  | 0, _ => 1
  | k + 1, h => (T.parent h).elim 1 fun g => dtDeflatorAux T q k g * q h

/-- The deflator `Q(ωᵗ)`, the product of the one-step state prices along the path to `ωᵗ`. -/
def dtDeflator (T : DTree Node) (q : Node → ℝ) (h : Node) : ℝ := dtDeflatorAux T q (T.depth h) h

omit [Fintype Node] in
/-- The deflator is positive when the one-step state prices are. -/
theorem dt_deflator_pos (T : DTree Node) {q : Node → ℝ} (hq : ∀ h, 0 < q h) (h : Node) :
    0 < dtDeflator T q h := by
  suffices ∀ k h, 0 < dtDeflatorAux T q k h from this _ _
  intro k
  induction k with
  | zero => intro h; simp [dtDeflatorAux]
  | succ k ih =>
    intro h
    simp only [dtDeflatorAux]
    cases T.parent h with
    | none => simp
    | some g => exact mul_pos (ih g) (hq h)

omit [Fintype Node] in
/-- `Q(ωᵗ⁺¹) = Q(ωᵗ) q(ωₜ₊₁|ωᵗ)`. -/
theorem dt_deflator_parent (T : DTree Node) (q : Node → ℝ) {h g : Node}
    (hg : T.parent h = some g) : dtDeflator T q h = dtDeflator T q g * q h := by
  simp only [dtDeflator, T.depth_parent h g hg, dtDeflatorAux, hg, Option.elim]

/-- **The dynamic fundamental theorem of asset pricing** (AKMM, p. 483). On a finite event tree
there is no arbitrage iff there are one-step state prices `qₜ₊₁(ωₜ₊₁|ωᵗ) > 0` (indexed by the
successor node) satisfying the law of one price
`pⁿₜ(ωᵗ) = Σ_{ωₜ₊₁}(dⁿₜ₊₁(ωᵗ⁺¹) + pⁿₜ₊₁(ωᵗ⁺¹)) qₜ₊₁(ωₜ₊₁|ωᵗ)` at every node. -/
theorem dt_ftap [DecidableEq Node] (T : DTree Node) (p d : Node → N → ℝ) :
    dtNoArbitrage T p d ↔ ∃ q : Node → ℝ, (∀ h, 0 < q h) ∧ ∀ h n,
      p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
        (d h' n + p h' n) * q h' := by
  rw [dt_ftap_deflator]
  constructor
  · rintro ⟨Q, hQ, hpr⟩
    refine ⟨fun h' => (T.parent h').elim 1 fun g => Q h' / Q g, fun h' => ?_, fun h n => ?_⟩
    · change 0 < (T.parent h').elim 1 fun g => Q h' / Q g
      cases T.parent h' with
      | none => simp
      | some g => exact div_pos (hQ h') (hQ g)
    · have e := hpr h n
      have hQh := (hQ h).ne'
      change p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
        (d h' n + p h' n) * (T.parent h').elim 1 (fun g => Q h' / Q g)
      have hs : ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
          (d h' n + p h' n) * (T.parent h').elim 1 (fun g => Q h' / Q g) =
          (∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
            Q h' * (p h' n + d h' n)) / Q h := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun h' hh' => ?_
        rw [(Finset.mem_filter.1 hh').2]
        simp only [Option.elim]
        ring
      rw [hs, ← e]
      field_simp
  · rintro ⟨q, hq, hpr⟩
    refine ⟨dtDeflator T q, dt_deflator_pos T hq, fun h n => ?_⟩
    rw [hpr h n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' hh' => ?_
    rw [dt_deflator_parent T q (Finset.mem_filter.1 hh').2]
    ring

/-- AKMM, p. 484: with complete one-step markets at the node `h` (the matrix of payoffs
`(d + p)(h', n)` over the successors `h'` of `h` has rank equal to their number), the one-step
state prices at `h` are unique. -/
theorem dt_statePrices_unique [DecidableEq Node] (T : DTree Node) (p d : Node → N → ℝ)
    (h : Node)
    (hrank : (Matrix.of fun (h' : {h' // T.parent h' = some h}) n => d h'.1 n + p h'.1 n).rank =
      Fintype.card {h' // T.parent h' = some h})
    {q q' : Node → ℝ}
    (hq : ∀ n, p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      (d h' n + p h' n) * q h')
    (hq' : ∀ n, p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      (d h' n + p h' n) * q' h')
    (h' : Node) (hh' : T.parent h' = some h) : q h' = q' h' := by
  have hinj := (tp_rank_iff_transpose_injective _).1 hrank
  have key : (fun h'' : {h' // T.parent h' = some h} => q h''.1) =
      fun h'' => q' h''.1 := by
    apply hinj
    funext n
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun h' => T.parent h' = some h))
      (fun x => by simp) (fun x => (d x n + p x n) * q x),
      ← Finset.sum_subtype (Finset.univ.filter (fun h' => T.parent h' = some h))
      (fun x => by simp) (fun x => (d x n + p x n) * q' x), ← hq n, ← hq' n]
  exact congrFun key ⟨h', hh'⟩

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality conditions and Euler equations with dynamic trading

AKMM, §16.5, pp. 483–485, on the finite event tree of `DynamicTree`. The sequential budget (16.8)
is `c ≤ y + x(θ)` with `x(θ)` the payoff stream of the strategy (`euBudget`).

* The first-order condition for holdings of asset `n` at `ωᵗ`,
  `ηₜ(ωᵗ)pⁿₜ(ωᵗ) = Σ_{ωᵗ⁺¹} ηₜ₊₁(ωᵗ⁺¹)(dⁿₜ₊₁ + pⁿₜ₊₁)(ωᵗ⁺¹)` with `η = ∂U/∂c`, proved from
  optimality at an interior optimum (`eu_foc`).
* (16.19): the subjective state prices `qᵢ,ₜ₊₁(ωₜ₊₁|ωᵗ) = (∂Uᵢ/∂cₜ₊₁(ωᵗ⁺¹))/(∂Uᵢ/∂cₜ(ωᵗ))`
  price every asset (`eq_16_19`), so an optimum excludes arbitrage (`eu_noArbitrage`).
* (16.20)–(16.21): with expected power utility the marginal utility is `πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{−γ}`
  (`eu_crra_partial`) and `qᵢ,ₜ₊₁(ωₜ₊₁|ωᵗ) = πₜ₊₁(ωₜ₊₁|ωᵗ)β(cₜ₊₁(ωᵗ⁺¹)/cₜ(ωᵗ))^{−γ}`
  (`eq_16_21`).
* (16.22)–(16.23): the return `Rⁿₜ₊₁ = (dⁿₜ₊₁ + pⁿₜ₊₁)/pⁿₜ` satisfies `Eₜ[Mₜ₊₁Rⁿₜ₊₁] = 1`
  with `M = q/πₜ₊₁(·|ωᵗ)` (`eq_16_23`), and the conditional risk premium is
  `Eₜ[Rⁿₜ₊₁] − R^f_{t+1} = −Covₜ(Mₜ₊₁, Rⁿₜ₊₁)/Eₜ[Mₜ₊₁]` (`eu_conditional_premium`).

Departures: (16.21) prints `cᵢ,ₜ₊₁(ωᵗ)` and `βᵗ⁺¹(ωᵗ⁺¹)`; the correct expression has
`cᵢ,ₜ₊₁(ωᵗ⁺¹)` and `βᵗ⁺¹`. The first-order conditions are derived at an interior optimum with
differentiable utility, on a finite tree. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Filter Topology Miao.CompleteMarkets

variable {Node N : Type} [Fintype Node] [Fintype N]

/-- AKMM, (16.8), p. 471: the sequential budget set `c ≤ y + x(θ)` on the tree. -/
def euBudget (T : DTree Node) (p d : Node → N → ℝ) (y : Node → ℝ) : Set (Node → ℝ) :=
  {c | ∃ θ, ∀ h, c h ≤ y h + dtPayoff T p d θ h}

/-- AKMM, p. 484: at an interior optimum `c ≫ 0` of a differentiable utility on the sequential
budget set (with `c ≥ 0`), the first-order condition for holding asset `n` at node `h` is
`η(h)pⁿ(h) = Σ_{h' child of h} η(h')(dⁿ(h') + pⁿ(h'))`, `η(h) = ∂U/∂c(h)`. -/
theorem eu_foc [DecidableEq Node] {T : DTree Node} {p d : Node → N → ℝ} {y : Node → ℝ}
    {U : (Node → ℝ) → ℝ} {DU : (Node → ℝ) →L[ℝ] ℝ} {c : Node → ℝ}
    (hc : c ∈ euBudget T p d y) (hpos : ∀ h, 0 < c h)
    (hopt : ∀ c' ∈ euBudget T p d y, (∀ h, 0 ≤ c' h) → U c' ≤ U c)
    (hU : HasFDerivAt U DU c) (h : Node) (n : N) :
    DU (Pi.single h 1) * p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      DU (Pi.single h' 1) * (p h' n + d h' n) := by
  classical
  obtain ⟨θ, hθ⟩ := hc
  set e : Node → N → ℝ := fun h' n' => if h' = h ∧ n' = n then 1 else 0 with he
  set v : Node → ℝ := dtPayoff T p d e with hv
  have hlin : ∀ t : ℝ, dtPayoff T p d (θ + t • e) = dtPayoff T p d θ + t • v := fun t => by
    have := (dtPayoffLin T p d).map_add θ (t • e)
    rw [(dtPayoffLin T p d).map_smul] at this
    exact this
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (c + t • v ∈ euBudget T p d y ∧ ∀ h, 0 ≤ (c + t • v) h) := by
    have hk : ∀ k, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c k + t * v k := fun k =>
      ((by fun_prop : Continuous fun t : ℝ => c k + t * v k).tendsto' 0 (c k)
        (by simp)).eventually (lt_mem_nhds (hpos k))
    filter_upwards [Filter.eventually_all.2 hk] with t ht
    refine ⟨⟨θ + t • e, fun k => ?_⟩, fun k => by simpa using (ht k).le⟩
    rw [hlin t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hθ k]
  have hmax : IsLocalMax (fun t : ℝ => U (c + t • v)) 0 := by
    filter_upwards [hev] with t ht
    simpa using hopt _ ht.1 ht.2
  have h0 := hmax.hasDerivAt_eq_zero (en_line_deriv hU v)
  rw [tp_clm_apply DU v] at h0
  have hval := dt_value_payoff T p d (fun k => DU (Pi.single k 1)) e
  simp only [← hv] at hval
  have hcomm : ∑ k, v k * DU (Pi.single k 1) = ∑ k, DU (Pi.single k 1) * v k :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hcomm, hval] at h0
  simp only [he, ite_mul, one_mul, zero_mul] at h0
  rw [Finset.sum_eq_single h, Finset.sum_eq_single n] at h0
  · simp only [and_self, ↓reduceIte] at h0
    linarith
  · intro n' _ hn
    simp [hn]
  · simp
  · intro h' _ hh
    simp [hh]
  · simp

/-- AKMM, (16.19), p. 484: with positive marginal utilities, the subjective state prices
`qᵢ(h') = (∂Uᵢ/∂c(h'))/(∂Uᵢ/∂c(h))` for each successor `h'` of `h` price every asset,
`pⁿ(h) = Σ_{h'}(dⁿ(h') + pⁿ(h'))qᵢ(h')`. -/
theorem eq_16_19 [DecidableEq Node] {T : DTree Node} {p d : Node → N → ℝ} {y : Node → ℝ}
    {U : (Node → ℝ) → ℝ} {DU : (Node → ℝ) →L[ℝ] ℝ} {c : Node → ℝ}
    (hc : c ∈ euBudget T p d y) (hpos : ∀ h, 0 < c h)
    (hopt : ∀ c' ∈ euBudget T p d y, (∀ h, 0 ≤ c' h) → U c' ≤ U c)
    (hU : HasFDerivAt U DU c) (hMU : ∀ h, 0 < DU (Pi.single h 1)) (h : Node) (n : N) :
    p h n = ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      (d h' n + p h' n) * (DU (Pi.single h' 1) / DU (Pi.single h 1)) := by
  have e := eu_foc hc hpos hopt hU h n
  have h0 := (hMU h).ne'
  have hs : ∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
      (d h' n + p h' n) * (DU (Pi.single h' 1) / DU (Pi.single h 1)) =
      (∑ h' ∈ Finset.univ.filter (fun h' => T.parent h' = some h),
        DU (Pi.single h' 1) * (p h' n + d h' n)) / DU (Pi.single h 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun h' _ => by ring
  rw [hs, ← e]
  field_simp

omit [Fintype Node] in
/-- AKMM, p. 483: if the individual problem has an interior solution with positive marginal
utilities, there is no arbitrage (the marginal utilities are a deflator, `dt_ftap_deflator`). -/
theorem eu_noArbitrage [Finite Node] [DecidableEq Node] {T : DTree Node} {p d : Node → N → ℝ}
    {y : Node → ℝ} {U : (Node → ℝ) → ℝ} {DU : (Node → ℝ) →L[ℝ] ℝ} {c : Node → ℝ}
    (hc : c ∈ euBudget T p d y) (hpos : ∀ h, 0 < c h)
    (hopt : ∀ c' ∈ euBudget T p d y, (∀ h, 0 ≤ c' h) → U c' ≤ U c)
    (hU : HasFDerivAt U DU c) (hMU : ∀ h, 0 < DU (Pi.single h 1)) : dtNoArbitrage T p d := by
  have := Fintype.ofFinite Node
  exact (dt_ftap_deflator T p d).2 ⟨fun h => DU (Pi.single h 1), hMU, eu_foc hc hpos hopt hU⟩

/-- AKMM, (16.20), p. 484: expected power utility `Σ_{t,ωᵗ} πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{1−γ}/(1−γ)` has
partial derivative `πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{−γ}` at `c ≫ 0`. -/
theorem eu_crra_partial (T : DTree Node) {pr : Node → ℝ} {β γ : ℝ} [DecidableEq Node]
    (hγ : γ ≠ 1) {c : Node → ℝ} (hc : ∀ h, 0 < c h) (h : Node) :
    HasDerivAt (fun x : ℝ => ∑ k, pr k * β ^ T.depth k *
        ((c k + x * if k = h then 1 else 0) ^ (1 - γ) / (1 - γ)))
      (pr h * β ^ T.depth h * c h ^ (-γ)) 0 := by
  have hk : ∀ k ∈ Finset.univ, HasDerivAt (fun x : ℝ => pr k * β ^ T.depth k *
      ((c k + x * if k = h then 1 else 0) ^ (1 - γ) / (1 - γ)))
      (if k = h then pr h * β ^ T.depth h * c h ^ (-γ) else 0) 0 := by
    intro k _
    by_cases hkh : k = h
    · subst hkh
      simp only [↓reduceIte, mul_one]
      have hd := tp_crra_marginal hγ (hc k)
      have hd0 : HasDerivAt (fun z => z ^ (1 - γ) / (1 - γ)) (c k ^ (-γ)) (c k + 0) := by
        simpa using hd
      exact (hd0.comp_const_add (c k) 0).const_mul _
    · simp only [hkh, ↓reduceIte, mul_zero, add_zero]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum hk
  simpa using this

/-- AKMM, (16.21), p. 484, corrected: with marginal utilities `πₜ(ωᵗ)βᵗcₜ(ωᵗ)^{−γ}`, the state
price of the successor `ωᵗ⁺¹` is `πₜ₊₁(ωₜ₊₁|ωᵗ)β(cₜ₊₁(ωᵗ⁺¹)/cₜ(ωᵗ))^{−γ}`, where
`πₜ₊₁(ωₜ₊₁|ωᵗ) = πₜ₊₁(ωᵗ⁺¹)/πₜ(ωᵗ)`. -/
theorem eq_16_21 {prt prt1 β γ ct ct1 : ℝ} (t : ℕ) (hpr : 0 < prt) (hβ : 0 < β) (hct : 0 < ct)
    (hct1 : 0 < ct1) :
    prt1 * β ^ (t + 1) * ct1 ^ (-γ) / (prt * β ^ t * ct ^ (-γ)) =
      prt1 / prt * β * (ct1 / ct) ^ (-γ) := by
  have h1 : 0 < ct ^ (-γ) := Real.rpow_pos_of_pos hct _
  have h2 : 0 < β ^ t := pow_pos hβ t
  rw [Real.div_rpow hct1.le hct.le, pow_succ]
  field_simp

/-- AKMM, (16.22)–(16.23), p. 484: at node `ωᵗ` with successor states `ω ∈ Ω`, conditional
probabilities `πc`, state prices `q` and payoffs `X = dⁿₜ₊₁ + pⁿₜ₊₁` with
`pⁿₜ = Σ_ω X(ω)q(ω)`, the return `R = X/pⁿₜ` and `M = q/πc` satisfy `Eₜ[MR] = 1`. -/
theorem eq_16_23 {Ω : Type} [Fintype Ω] {prc q X : Ω → ℝ} {pt : ℝ} (hpr : ∀ ω, 0 < prc ω)
    (hp : pt = ∑ ω, X ω * q ω) (hpt : pt ≠ 0) :
    bp_E prc (fun ω => sdfM q prc ω * (X ω / pt)) = 1 := by
  have h := sdf_return (D := Matrix.of fun ω (_ : Unit) => X ω) (p := fun _ => pt) hpr
    (fun _ => by simpa using hp) (n := ()) hpt
  rw [← h]
  exact Finset.sum_congr rfl fun ω _ => by simp only [Matrix.of_apply]; ring

/-- AKMM, p. 485: the conditional risk premium,
`Eₜ[Rⁿₜ₊₁] − R^f_{t+1} = −Covₜ(Mₜ₊₁, Rⁿₜ₊₁)/Eₜ[Mₜ₊₁]` with `R^f_{t+1} = 1/Eₜ[Mₜ₊₁]`, and
`Eₜ[M]Eₜ[Rⁿ] + Covₜ(M, Rⁿ) = 1`. -/
theorem eu_conditional_premium {Ω : Type} [Fintype Ω] {prc M R : Ω → ℝ}
    (hM : bp_E prc M ≠ 0) (h : bp_E prc (fun ω => M ω * R ω) = 1) :
    bp_E prc M * bp_E prc R + bp_Cov prc M R = 1 ∧
      bp_E prc R - 1 / bp_E prc M = -bp_Cov prc M R / bp_E prc M := by
  have h' : bp_E prc (fun ω => R ω * M ω) = 1 := by
    rw [← h]
    exact Finset.sum_congr rfl fun ω _ => by ring
  obtain ⟨e1, e2⟩ := eq_16_17 hM h'
  rw [bp_Cov_comm]
  exact ⟨by linarith, e2⟩

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The equity premium in the Mehra–Prescott economy

AKMM, §16.6, pp. 485–488 (with fns. 4–5). Endowment growth `G ∈ {G_L, G_H}` follows the
symmetric two-state chain `Π = [φ 1−φ; 1−φ φ]`; the stock is a claim to the endowment and the
stochastic discount factor is `M = βG^{−γ}`.

* The symmetric chain has the stationary distribution `(1/2, 1/2)`, the only one when `φ ≠ 1`
  (`mp_stationary_iff`).
* (16.24) in ratio form: `p = vy` turns `pₜ = Eₜ[Mₜ₊₁(yₜ₊₁ + pₜ₊₁)]` into
  `vₜ = Eₜ[βG^{1−γ}ₜ₊₁(1 + vₜ₊₁)]` (`mp_pd_step`).
* With `Aᵢⱼ = ΠᵢⱼGⱼ^{1−γ}`, when `ρ(βA) < 1`, `v = (I − βA)⁻¹βA𝟙` is the unique solution of
  `v = βA(1 + v)` (`mp_pd_unique`, from Sargent–Stachurski's Exercise 6.3.6, `isPDRatio_iff`) and
  equals the series of fn. 4, `Σ_{t≥1}(βA)ᵗ𝟙` (`mp_pd_series`); `ρ(βA) < 1` holds when every row
  sum of `βA` is below one (`mp_specRad_lt_one`).
* (16.25): `rˢᵢⱼ = Gⱼ(1 + vⱼ)/vᵢ − 1` (`eq_16_25`); (16.26)–(16.27): conditional and
  unconditional expected returns, the bond price `pᶠᵢ = Σⱼ ΠᵢⱼβGⱼ^{−γ}` and the riskless rate
  (`mpCondMean`, `mpUncondMean`, `mp_bond_price`, `mpRf`), and the equity premium
  (`mpEquityPremium`).
* Fn. 5: with `G_L = 1 + μ − δ`, `G_H = 1 + μ + δ` and `π = (1/2, 1/2)`, `E[G] − 1 = μ`,
  `σ²(G) = δ²` and the autocorrelation is `2φ − 1` (`fn5_mean`, `fn5_var`, `fn5_autocorr`).

Departure: (16.25) writes `gⱼ` for the gross growth rate `Gⱼ`. The claim of Figure 16.4 is in
`FigureClaims`.
-/

namespace AKMM.AssetPrices

open Matrix SargentStachurski.StochasticDiscounting

/-- AKMM, p. 486: the symmetric transition matrix `Π = [φ 1−φ; 1−φ φ]`. -/
def mpPi (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![φ, 1 - φ; 1 - φ, φ]

/-- AKMM, p. 486: the stationary distribution `π = Πᵀπ` of the symmetric chain is `(1/2, 1/2)`,
and it is the only one when `φ ≠ 1`. -/
theorem mp_stationary_iff {φ : ℝ} (hφ : φ ≠ 1) (pr : Fin 2 → ℝ) :
    ((mpPi φ)ᵀ *ᵥ pr = pr ∧ pr 0 + pr 1 = 1) ↔ pr = ![1 / 2, 1 / 2] := by
  have h1 : (1 : ℝ) - φ ≠ 0 := sub_ne_zero.2 (Ne.symm hφ)
  constructor
  · rintro ⟨hs, hsum⟩
    have e0 : φ * pr 0 + (1 - φ) * pr 1 = pr 0 := by
      simpa [mpPi, mulVec, dotProduct, Fin.sum_univ_two] using congrFun hs 0
    have hd : (1 - φ) * (pr 1 - pr 0) = 0 := by linarith
    have heq : pr 1 = pr 0 := by
      have := (mul_eq_zero.1 hd).resolve_left h1
      linarith
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨funext fun i => ?_, by norm_num⟩
    fin_cases i <;> simp [mpPi, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- AKMM, (16.24), p. 486: with `pₜ = vₜyₜ`, `yₜ₊₁ = Gₜ₊₁yₜ` and `Mₜ₊₁ = βG^{−γ}ₜ₊₁`,
`Mₜ₊₁(yₜ₊₁ + pₜ₊₁)/yₜ = βG^{1−γ}ₜ₊₁(1 + vₜ₊₁)`. -/
theorem mp_pd_step {β γ G y v' : ℝ} (hG : 0 < G) (hy : 0 < y) :
    β * G ^ (-γ) * (G * y + v' * (G * y)) / y = β * G ^ (1 - γ) * (1 + v') := by
  have e : G ^ (1 - γ) = G ^ (-γ) * G := by
    rw [sub_eq_neg_add, Real.rpow_add hG, Real.rpow_one]
  rw [e]
  field_simp

/-- AKMM, p. 486: the matrix `Aᵢⱼ = ΠᵢⱼGⱼ^{1−γ}`. -/
noncomputable def mpA (φ γ : ℝ) (G : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => mpPi φ i j * G j ^ (1 - γ)

/-- AKMM, p. 486: when `ρ(βA) < 1`, `v = (I − βA)⁻¹βA𝟙` is the unique solution of
`v = βA(1 + v)` (in finite states every solution is bounded). -/
theorem mp_pd_unique {φ γ β : ℝ} {G : Fin 2 → ℝ} (hρ : specRad (β • mpA φ γ G) < 1)
    (v : Fin 2 → ℝ) :
    v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i) ↔
      v = (1 - β • mpA φ γ G)⁻¹ *ᵥ ((β • mpA φ γ G) *ᵥ fun _ => 1) := by
  rw [← isPDRatio_iff hρ, IsPDRatio]
  have : (β • mpA φ γ G) *ᵥ (fun i => 1 + v i) =
      (β • mpA φ γ G) *ᵥ (fun _ => 1) + (β • mpA φ γ G) *ᵥ v := by
    rw [← mulVec_add]
    rfl
  rw [this]

/-- AKMM, fn. 4, p. 486: recursive substitution, `v = Σ_{t≥1}(βA)ᵗ𝟙`. -/
theorem mp_pd_series {φ γ β : ℝ} {G : Fin 2 → ℝ} (hρ : specRad (β • mpA φ γ G) < 1) :
    (1 - β • mpA φ γ G)⁻¹ *ᵥ ((β • mpA φ γ G) *ᵥ fun _ => 1) =
      ∑' t : ℕ, (β • mpA φ γ G) ^ (t + 1) *ᵥ fun _ => (1 : ℝ) :=
  pdRatio_eq_tsum hρ

/-- A sufficient condition for `ρ(βA) < 1`: every row sum `β Σⱼ ΠᵢⱼGⱼ^{1−γ}` is below one. -/
theorem mp_specRad_lt_one {φ γ β : ℝ} {G : Fin 2 → ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hβ : 0 ≤ β) (hG : ∀ j, 0 < G j) {C : ℝ} (hC : C < 1)
    (hrow : ∀ i, ∑ j, β * (mpPi φ i j * G j ^ (1 - γ)) ≤ C) :
    specRad (β • mpA φ γ G) < 1 := by
  refine lt_of_le_of_lt (specRad_le_of_rowsum_le _ (fun i j => ?_) fun i => ?_) hC
  · have hP : 0 ≤ mpPi φ i j := by
      fin_cases i <;> fin_cases j <;> simp [mpPi] <;> linarith
    simp only [Matrix.smul_apply, mpA, Matrix.of_apply, smul_eq_mul]
    exact mul_nonneg hβ (mul_nonneg hP (Real.rpow_pos_of_pos (hG j) _).le)
  · simpa [mpA] using hrow i

/-- AKMM, (16.25), p. 486: with `pᵢ = vᵢy` and `pⱼ' = vⱼGⱼy`, the stock return
`(yₜ₊₁ + pₜ₊₁ − pₜ)/pₜ` from state `i` to state `j` is `Gⱼ(1 + vⱼ)/vᵢ − 1`. -/
theorem eq_16_25 {y Gj vi vj : ℝ} (hy : 0 < y) (hvi : vi ≠ 0) :
    (Gj * y + vj * (Gj * y) - vi * y) / (vi * y) = Gj * (1 + vj) / vi - 1 := by
  field_simp

/-- AKMM, (16.26), p. 487: the conditional expected return `Eᵢ[rˢ] = Σⱼ Πᵢⱼrˢᵢⱼ`. -/
def mpCondMean (P : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ j, P i j * r i j

/-- AKMM, (16.26), p. 487: the unconditional expected return `E[rˢ] = Σᵢ πᵢEᵢ[rˢ]`. -/
def mpUncondMean (pr : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i, pr i * mpCondMean P r i

/-- AKMM, p. 487: the price of the one-period riskless bond, `pᶠᵢ = Eᵢ[M] = Σⱼ ΠᵢⱼβGⱼ^{−γ}`. -/
noncomputable def mpBond (φ β γ : ℝ) (G : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ j, mpPi φ i j * (β * G j ^ (-γ))

/-- AKMM, (16.27), p. 487: the riskless rate `rᶠᵢ = 1/pᶠᵢ − 1`. -/
noncomputable def mpRf (φ β γ : ℝ) (G : Fin 2 → ℝ) (i : Fin 2) : ℝ := 1 / mpBond φ β γ G i - 1

/-- AKMM, p. 487: the unconditional equity premium `E[rˢ] − E[rᶠ]`. -/
noncomputable def mpEquityPremium (φ β γ : ℝ) (G : Fin 2 → ℝ) (r : Fin 2 → Fin 2 → ℝ) : ℝ :=
  mpUncondMean ![1 / 2, 1 / 2] (mpPi φ) r - ∑ i, ![1 / 2, 1 / 2] i * mpRf φ β γ G i

/-- AKMM, p. 487: the bond price in closed form, `pᶠ₁ = β(φG_L^{−γ} + (1 − φ)G_H^{−γ})`,
`pᶠ₂ = β((1 − φ)G_L^{−γ} + φG_H^{−γ})`, and the bond is priced at `E[M]` and its gross return is
`1/pᶠᵢ`. -/
theorem mp_bond_price (φ β γ : ℝ) (G : Fin 2 → ℝ) :
    mpBond φ β γ G 0 = β * (φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ)) ∧
      mpBond φ β γ G 1 = β * ((1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ)) := by
  constructor <;> simp [mpBond, mpPi, Fin.sum_univ_two] <;> ring

/-- AKMM, fn. 5, p. 487: `E[Gₜ] = π₁G_L + π₂G_H`. -/
def fn5Mean (pr G : Fin 2 → ℝ) : ℝ := ∑ i, pr i * G i

/-- AKMM, fn. 5: `E[Gₜ²]`. -/
def fn5Second (pr G : Fin 2 → ℝ) : ℝ := ∑ i, pr i * G i ^ 2

/-- AKMM, fn. 5: `E[GₜGₜ₋₁] = Σᵢⱼ πᵢΠᵢⱼGᵢGⱼ`. -/
def fn5Cross (pr G : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i, ∑ j, pr i * P i j * G i * G j

/-- The growth states `G_L = 1 + μ − δ`, `G_H = 1 + μ + δ`. -/
def fn5G (μ δ : ℝ) : Fin 2 → ℝ := ![1 + μ - δ, 1 + μ + δ]

/-- AKMM, p. 487 and fn. 5: with the stationary `π = (1/2, 1/2)`, the mean net growth rate is
`E[Gₜ] − 1 = μ`. -/
theorem fn5_mean (μ δ : ℝ) : fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) - 1 = μ := by
  simp [fn5Mean, fn5G, Fin.sum_univ_two]
  ring

/-- AKMM, fn. 5: the variance `σ²(Gₜ − 1) = σ²(Gₜ) = E[Gₜ²] − E[Gₜ]² = δ²`. -/
theorem fn5_var (μ δ : ℝ) :
    fn5Second ![1 / 2, 1 / 2] (fn5G μ δ) - fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) ^ 2 = δ ^ 2 := by
  simp [fn5Second, fn5Mean, fn5G, Fin.sum_univ_two]
  ring

/-- AKMM, p. 487 and fn. 5: the autocorrelation
`(E[GₜGₜ₋₁] − E[Gₜ]²)/σ²(Gₜ)` of the symmetric chain is `2φ − 1` (so `φ` governs persistence). -/
theorem fn5_autocorr (μ δ φ : ℝ) (hδ : δ ≠ 0) :
    (fn5Cross ![1 / 2, 1 / 2] (fn5G μ δ) (mpPi φ) - fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) ^ 2) /
      (fn5Second ![1 / 2, 1 / 2] (fn5G μ δ) - fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) ^ 2) =
      2 * φ - 1 := by
  rw [fn5_var, div_eq_iff (pow_ne_zero 2 hδ)]
  simp [fn5Cross, fn5Mean, fn5G, mpPi, Fin.sum_univ_two]
  ring

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The lognormal model: the riskless rate and the consumption CAPM

AKMM, §16.7, pp. 488–490. Log endowment growth `g = log G ~ N(μ_g, σ_g²)` (16.28) and power
utility, so `log M = log β − γg`. Gaussian integrals are Miao's `bp_integral_exp_gaussian`.

* (16.29): `pᶠ = Eₜ[M] = βe^{−γμ_g + γ²σ_g²/2}` and `rᶠ = log(1/pᶠ) = −log β + γμ_g − γ²σ_g²/2`
  (`eq_16_29`).
* The two motives: `rᶠ` rises with `μ_g` and falls with `σ_g²` (`lg_rf_growth`,
  `lg_rf_precautionary`); in `γ` it increases exactly on `γ ≤ μ_g/σ_g²` and decreases beyond
  (`lg_rf_mono_iff`, `lg_rf_strictMonoOn`, `lg_rf_strictAntiOn`); with Table 16.1's
  `μ_g = 0.0175`, `σ_g = 0.0233`, `μ_g/σ_g² ∈ (32, 33)` (`lg_threshold_table`).
* The equity Euler equation with jointly lognormal `(g, rˢ)` gives
  `Eₜrˢ = −log β + γμ_g − γ²σ_g²/2 − σᵣ²/2 + γCovₜ(g, rˢ)` (`lg_equity_euler`) and **(16.30)**,
  `Eₜrˢ − rᶠ + σᵣ²/2 = γCovₜ(g, rˢ)` (`eq_16_30`); the Jensen term
  `log EₜRˢ = Eₜrˢ + σᵣ²/2` (`lg_jensen`).
* The numbers on p. 490: `σ_cσ_r = 0.0233 × 0.1836 ≈ 0.0043` (`lg_sd_product`); a premium of
  `0.07` needs `γ ≥ 16.36` even with perfect correlation (`lg_gamma_bound`), and `γ = 16` falls
  short (`lg_gamma_16_short`); with `β ≤ 1` and `γ ∈ [16, 48]` the riskless rate exceeds 1%
  (`lg_rf_high`).

Departures: the derivation of (16.30) mixes `μ_c, σ_c` with `μ_g, σ_g` (the same objects);
"`γ = 16`" understates the bound `γ ≥ 16.36` implied by Table 16.1. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open MeasureTheory ProbabilityTheory Miao.CompleteMarkets

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- AKMM, (16.29), p. 488: with `g ~ N(μ_g, σ_g²)`, the bond price is
`pᶠ = E[βe^{−γg}] = βe^{−γμ_g + γ²σ_g²/2}` and the riskless rate is
`rᶠ = log(1/pᶠ) = −log β + γμ_g − γ²σ_g²/2`. -/
theorem eq_16_29 {g : Ω → ℝ} {μ : ℝ} {v : NNReal} (hg : HasLaw g (gaussianReal μ v) P)
    {β : ℝ} (hβ : 0 < β) (γ : ℝ) :
    ∫ ω, β * Real.exp (-γ * g ω) ∂P = β * Real.exp (-γ * μ + γ ^ 2 * v / 2) ∧
      Real.log (1 / (β * Real.exp (-γ * μ + γ ^ 2 * v / 2))) =
        -Real.log β + γ * μ - γ ^ 2 * v / 2 := by
  have hm := gaussianReal_const_mul hg (-γ)
  have hE := bp_integral_exp_gaussian hm
  refine ⟨?_, ?_⟩
  · rw [integral_const_mul, hE]
    congr 2
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring
  · rw [one_div, Real.log_inv, Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

/-- The riskless rate (16.29) as a function of the parameters (`v = σ_g²`). -/
noncomputable def lgRf (β γ μ v : ℝ) : ℝ := -Real.log β + γ * μ - γ ^ 2 * v / 2

/-- AKMM, p. 488, the intertemporal smoothing motive: with `γ > 0`, higher expected growth
raises the riskless rate. -/
theorem lg_rf_growth {β γ μ₁ μ₂ v : ℝ} (hγ : 0 < γ) (h : μ₁ < μ₂) :
    lgRf β γ μ₁ v < lgRf β γ μ₂ v := by
  unfold lgRf
  nlinarith

/-- AKMM, p. 489, the precautionary motive: with `γ ≠ 0`, more volatile growth lowers the
riskless rate. -/
theorem lg_rf_precautionary {β γ μ v₁ v₂ : ℝ} (hγ : γ ≠ 0) (h : v₁ < v₂) :
    lgRf β γ μ v₂ < lgRf β γ μ v₁ := by
  unfold lgRf
  have : 0 < γ ^ 2 := by positivity
  nlinarith

/-- AKMM, p. 489: `∂rᶠ/∂γ = μ_g − γσ_g²`, positive iff `γ < μ_g/σ_g²`. -/
theorem lg_rf_mono_iff {β μ v : ℝ} (hv : 0 < v) (γ : ℝ) :
    HasDerivAt (fun γ' => lgRf β γ' μ v) (μ - γ * v) γ ∧ (0 < μ - γ * v ↔ γ < μ / v) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun γ' : ℝ => γ' * μ) μ γ := by
      simpa using (hasDerivAt_id γ).mul_const μ
    have h2 : HasDerivAt (fun γ' : ℝ => γ' ^ 2 * v / 2) (γ * v) γ := by
      have := ((hasDerivAt_pow 2 γ).mul_const v).div_const 2
      convert this using 1
      ring
    have h3 := (h1.sub h2).const_add (-Real.log β)
    have e : (fun γ' => lgRf β γ' μ v) = fun x => -Real.log β + (x * μ - x ^ 2 * v / 2) := by
      funext γ'
      simp only [lgRf]
      ring
    rw [e]
    exact h3
  · rw [lt_div_iff₀ hv, sub_pos]

/-- AKMM, p. 489: the riskless rate is strictly increasing in `γ` on `γ ≤ μ_g/σ_g²`. -/
theorem lg_rf_strictMonoOn {β μ v : ℝ} (hv : 0 < v) :
    StrictMonoOn (fun γ => lgRf β γ μ v) (Set.Iic (μ / v)) := by
  intro γ₁ h₁ γ₂ h₂ h12
  simp only [Set.mem_Iic, le_div_iff₀ hv] at h₁ h₂
  simp only [lgRf]
  have : 0 < μ - (γ₁ + γ₂) * v / 2 := by nlinarith
  nlinarith [mul_pos (sub_pos.2 h12) this]

/-- AKMM, p. 489: beyond `μ_g/σ_g²` the precautionary motive dominates and the riskless rate
decreases in `γ`. -/
theorem lg_rf_strictAntiOn {β μ v : ℝ} (hv : 0 < v) :
    StrictAntiOn (fun γ => lgRf β γ μ v) (Set.Ici (μ / v)) := by
  intro γ₁ h₁ γ₂ h₂ h12
  simp only [Set.mem_Ici, div_le_iff₀ hv] at h₁ h₂
  simp only [lgRf]
  have : μ - (γ₁ + γ₂) * v / 2 < 0 := by nlinarith
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 h12) this]

/-- AKMM, p. 489: with Table 16.1's `μ_g = 0.0175` and `σ_g = 0.0233` the threshold
`μ_g/σ_g²` lies in `(32, 33)`; the smoothing motive dominates below it. -/
theorem lg_threshold_table : 32 < (0.0175 : ℝ) / 0.0233 ^ 2 ∧ (0.0175 : ℝ) / 0.0233 ^ 2 < 33 := by
  constructor <;> rw [div_eq_mul_inv] <;> norm_num

/-- AKMM, p. 489: if `−γg + rˢ ~ N(−γμ_g + Eₜrˢ, γ²σ_g² + σᵣ² − 2γCov(g, rˢ))` (joint
lognormality) and `1 = Eₜ[βe^{−γg + rˢ}]`, then
`Eₜrˢ = −log β + γμ_g − γ²σ_g²/2 − σᵣ²/2 + γCovₜ(g, rˢ)`. -/
theorem lg_equity_euler {g r : Ω → ℝ} {β γ μg μr vg vr c : ℝ} (hβ : 0 < β)
    (hvar : 0 ≤ γ ^ 2 * vg + vr - 2 * γ * c)
    (hX : HasLaw (fun ω => -γ * g ω + r ω)
      (gaussianReal (-γ * μg + μr) ⟨γ ^ 2 * vg + vr - 2 * γ * c, hvar⟩) P)
    (heul : ∫ ω, β * Real.exp (-γ * g ω + r ω) ∂P = 1) :
    μr = -Real.log β + γ * μg - γ ^ 2 * vg / 2 - vr / 2 + γ * c := by
  have h : ∫ ω, Real.exp (-γ * g ω + r ω) * Real.exp (Real.log β) ∂P = 1 := by
    rw [Real.exp_log hβ]
    rw [← heul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have := bp_euler_gaussian hX _ h
  change -γ * μg + μr + (γ ^ 2 * vg + vr - 2 * γ * c) / 2 + Real.log β = 0 at this
  linarith

/-- **(16.30)** (AKMM, p. 489): the equity premium in the CCAPM,
`Eₜrˢ − rᶠ + σᵣ²/2 = γCovₜ(g, rˢ)`, with `rᶠ` from (16.29). -/
theorem eq_16_30 {g r : Ω → ℝ} {β γ μg μr vg vr c : ℝ} (hβ : 0 < β)
    (hvar : 0 ≤ γ ^ 2 * vg + vr - 2 * γ * c)
    (hX : HasLaw (fun ω => -γ * g ω + r ω)
      (gaussianReal (-γ * μg + μr) ⟨γ ^ 2 * vg + vr - 2 * γ * c, hvar⟩) P)
    (heul : ∫ ω, β * Real.exp (-γ * g ω + r ω) ∂P = 1) :
    μr - lgRf β γ μg vg + vr / 2 = γ * c := by
  have := lg_equity_euler hβ hvar hX heul
  unfold lgRf
  linarith

/-- AKMM, p. 489: the Jensen term, `log Eₜ[Rˢ] = Eₜrˢ + σᵣ²/2` for `rˢ = log Rˢ ~ N(Eₜrˢ, σᵣ²)`. -/
theorem lg_jensen {r : Ω → ℝ} {μr : ℝ} {vr : NNReal} (hr : HasLaw r (gaussianReal μr vr) P) :
    Real.log (∫ ω, Real.exp (r ω) ∂P) = μr + vr / 2 := by
  rw [bp_integral_exp_gaussian hr, Real.log_exp]

/-- AKMM, p. 490: `σ_cσ_r = 0.0233 × 0.1836 = 0.00427788`, which is `0.0043` to two significant
figures. -/
theorem lg_sd_product : (0.0233 : ℝ) * 0.1836 = 0.00427788 ∧
    |(0.0233 : ℝ) * 0.1836 - 0.0043| < 0.00003 := by
  constructor
  · norm_num
  · rw [abs_lt]
    constructor <;> norm_num

/-- AKMM, p. 490: since `Cov(g, rˢ) = ρσ_cσ_r ≤ σ_cσ_r`, a premium `γCov(g, rˢ) ≥ 0.07` with the
Table 16.1 volatilities needs `γ ≥ 16.36` (exact certificate:
`16.36 × 0.00427788 = 0.0699861… < 0.07`). -/
theorem lg_gamma_bound {γ ρ : ℝ} (hγ : 0 ≤ γ) (hρ : ρ ≤ 1)
    (h : 0.07 ≤ γ * (ρ * (0.0233 * 0.1836))) : (16.36 : ℝ) ≤ γ := by
  have h1 : γ * (ρ * (0.0233 * 0.1836)) ≤ γ * (0.0233 * 0.1836) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hγ
  by_contra hc
  push Not at hc
  nlinarith

/-- AKMM, p. 490: "risk aversion would need to be high, `γ = 16`" understates the bound: at
`γ = 16`, even with perfect correlation, `γσ_cσ_r = 0.0684… < 0.07`. -/
theorem lg_gamma_16_short : (16 : ℝ) * (0.0233 * 0.1836) < 0.07 := by norm_num

/-- AKMM, p. 490: with `β ≤ 1`, Table 16.1's `μ_g = 0.0175`, `σ_g = 0.0233` and any
`γ ∈ [16, 48]`, the riskless rate (16.29) exceeds its 1% sample mean. -/
theorem lg_rf_high {β γ : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1) (hγ1 : 16 ≤ γ) (hγ2 : γ ≤ 48) :
    0.01 < lgRf β γ 0.0175 (0.0233 ^ 2) := by
  have hlog : Real.log β ≤ 0 := Real.log_nonpos hβ0.le hβ
  unfold lgRf
  nlinarith [mul_nonneg (sub_nonneg.2 hγ1) (sub_nonneg.2 hγ2)]

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The excess volatility puzzle: iid growth and a constant price–dividend ratio

AKMM, §16.8, pp. 490–492, (16.31)–(16.32). Growth `G` is iid. In the finite-support version the
growth rate takes the values `G_k` with probabilities `w_k` each period (a Markov chain whose rows
are all `w`), and `a = βE[G^{1−γ}] = Σ_k w_kβG_k^{1−γ}`.

* Every solution of `vᵢ = Σ_k w_kβG_k^{1−γ}(1 + v_k)` is constant in the current state
  (`iid_pd_const`) and, for `a ≠ 1`, equals `a/(1 − a)` (`iid_pd_unique`, `iid_pd_solves`);
  (16.31), the series `Σ_{t≥1} aᵗ = a/(1 − a)` for `0 ≤ a < 1` (`eq_16_31`).
* (16.32): the log return is `rˢ = g + log((1 + v)/v)` (`eq_16_32`), so its variance equals the
  variance of log growth (`iid_return_var`).
* The lognormal case of the book: with `g ~ N(μ_g, σ_g²)`,
  `a = β exp((1 − γ)μ_g + (1 − γ)²σ_g²/2)` and the constant `v = a/(1 − a)` solves
  `v = E[βG^{1−γ}(1 + v)]` (`iid_lognormal_pd`).

Departure: the uniqueness argument is made for finitely many growth states (the book's growth is
lognormal; for it the constant solution is verified). See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Miao.CompleteMarkets MeasureTheory ProbabilityTheory

variable {K : Type} [Fintype K]

/-- AKMM, (16.31), p. 490: with iid growth the right side of
`vᵢ = Σ_k w_kβG_k^{1−γ}(1 + v_k)` does not depend on the current state, so every solution is
constant. -/
theorem iid_pd_const {w b v : K → ℝ} (hv : ∀ i, v i = ∑ k, w k * b k * (1 + v k)) (i j : K) :
    v i = v j := by
  rw [hv i, hv j]

/-- AKMM, p. 490: with `a = Σ_k w_k b_k ≠ 1` (`b_k = βG_k^{1−γ}`) the only solution
is the constant `a/(1 − a)`. -/
theorem iid_pd_unique {w b v : K → ℝ}
    (hv : ∀ i, v i = ∑ k, w k * b k * (1 + v k)) (ha : ∑ k, w k * b k ≠ 1) (i : K) :
    v i = (∑ k, w k * b k) / (1 - ∑ k, w k * b k) := by
  have hc : ∀ k, v k = v i := fun k => iid_pd_const hv k i
  have h := hv i
  simp only [hc] at h
  rw [← Finset.sum_mul] at h
  have h1 : (1 : ℝ) - ∑ k, w k * b k ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [eq_div_iff h1]
  linarith

/-- AKMM, p. 490: the constant `a/(1 − a)` solves the price–dividend equation. -/
theorem iid_pd_solves {w b : K → ℝ} (ha : ∑ k, w k * b k ≠ 1) (i : K) :
    (fun _ : K => (∑ k, w k * b k) / (1 - ∑ k, w k * b k)) i =
      ∑ k, w k * b k * (1 + (∑ k, w k * b k) / (1 - ∑ k, w k * b k)) := by
  have h1 : (1 : ℝ) - ∑ k, w k * b k ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [← Finset.sum_mul]
  field_simp
  ring

/-- AKMM, (16.31), p. 490: by recursive substitution
`v = Eₜ[βG^{1−γ}ₜ₊₁ + β²G^{1−γ}ₜ₊₁G^{1−γ}ₜ₊₂ + ⋯] = Σ_{t≥1} aᵗ`, which is `a/(1 − a)` for
`0 ≤ a < 1`. -/
theorem eq_16_31 {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) : ∑' t : ℕ, a ^ (t + 1) = a / (1 - a) := by
  simp only [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  ring

/-- AKMM, (16.32), p. 490: with a constant ratio `v > 0` the log return is
`rˢ = log(G(1 + v)/v) = g + log((1 + v)/v)`. -/
theorem eq_16_32 {G v : ℝ} (hG : 0 < G) (hv : 0 < v) :
    Real.log (G * ((1 + v) / v)) = Real.log G + Real.log ((1 + v) / v) :=
  Real.log_mul hG.ne' (div_pos (by linarith) hv).ne'

/-- AKMM, p. 490: since the second term of (16.32) is constant, the variance of the stock return
equals the variance of log growth. -/
theorem iid_return_var {w g : K → ℝ} (hw : ∑ k, w k = 1) (c : ℝ) :
    bp_Var w (fun k => g k + c) = bp_Var w g := by
  have hE : bp_E w (fun k => g k + c) = bp_E w g + c := by
    rw [bp_E_add, bp_E_const w hw]
  rw [bp_Var, bp_Var, bp_Cov_eq_dev w hw, bp_Cov_eq_dev w hw, hE]
  congr 1
  funext k
  ring

/-- AKMM, (16.31), p. 490, the lognormal case: with `g ~ N(μ_g, σ_g²)` and
`a = β exp((1 − γ)μ_g + (1 − γ)²σ_g²/2) ≠ 1`, the constant `v = a/(1 − a)` solves
`v = E[βe^{(1−γ)g}(1 + v)]`. -/
theorem iid_lognormal_pd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ}
    {μ : ℝ} {σ2 : NNReal} (hg : HasLaw g (gaussianReal μ σ2) P) (β γ : ℝ)
    (ha : β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) ≠ 1) :
    ∫ ω, β * Real.exp ((1 - γ) * g ω) *
        (1 + β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) /
          (1 - β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2))) ∂P =
      β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) /
        (1 - β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2)) := by
  set a := β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) with hadef
  have hm := gaussianReal_const_mul hg (1 - γ)
  have hE : ∫ ω, Real.exp ((1 - γ) * g ω) ∂P =
      Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) := by
    rw [bp_integral_exp_gaussian hm]
    congr 1
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [integral_mul_const, integral_const_mul, hE, ← hadef]
  field_simp
  ring

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin utility separates the riskless rate from risk aversion

AKMM, §16.7, p. 490: "with Epstein–Zin utility, the intertemporal smoothing motive in (16.29) is
governed by the inverse of the elasticity of intertemporal substitution instead of risk aversion
`γ`, while the parameter that enters the equity premium is still risk aversion". The lognormal
Epstein–Zin pricing formulas are Miao's (20.33) and (20.35) (`Miao.RecursiveUtility.eq_20_33`,
`eq_20_35`), whose utility `[(1 − β)C^{1−ρ} + β(E U^{1−γ})^{(1−ρ)/(1−γ)}]^{1/(1−ρ)}` has risk
aversion `γ` and EIS `1/ρ`, the book's Epstein–Zin utility.

* Under Epstein–Zin the riskless rate responds to expected growth with slope `ρ = 1/EIS`, whatever
  `γ` (`ez_rf_smoothing`); with power utility the slope is `γ` (`lg_power_smoothing`).
* With `ρ = γ` Epstein–Zin is power utility and (20.33) reduces to (16.29) (`ez_power_case`).
* The premium weights in (20.35) involve `γ` (`ez_premium_weights`).
-/

namespace AKMM.AssetPrices

/-- AKMM, p. 490: with power utility the smoothing motive in (16.29) has slope `γ`:
`rᶠ(μ′) − rᶠ(μ) = γ(μ′ − μ)`. -/
theorem lg_power_smoothing (β γ μ μ' v : ℝ) :
    lgRf β γ μ' v - lgRf β γ μ v = γ * (μ' - μ) := by
  unfold lgRf
  ring

/-- AKMM, p. 490: under Epstein–Zin utility (Miao's (20.33)), two economies that differ only in
expected consumption growth `E_tΔc` have riskless rates differing by `ρ(μ′ − μ)`, with `ρ` the
inverse EIS, independently of risk aversion `γ`. -/
theorem ez_rf_smoothing {β ρ γ rf rf' m0 m0' m1 m1' v00 v01 v11 : ℝ} (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hA : 0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + (1 - γ) / (1 - ρ) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * v11)
    (hB : 0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11)
    (hA' : 0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0'
      + (1 - γ) / (1 - ρ) * m1' + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * v11)
    (hB' : 0 = rf' + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0'
      + ((1 - γ) / (1 - ρ) - 1) * m1' + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11) :
    rf' - rf = ρ * (m0' - m0) := by
  have e := Miao.RecursiveUtility.eq_20_33 hρ hγ hA hB
  have e' := Miao.RecursiveUtility.eq_20_33 hρ hγ hA' hB'
  rw [e, e']
  ring

/-- AKMM, p. 490: when `ρ = γ` (EIS `= 1/γ`) Epstein–Zin utility is power utility, and Miao's
(20.33) is the book's (16.29), `rᶠ = −log β + γE_tΔc − γ²σ_c²/2`. -/
theorem ez_power_case {β γ rf m0 m1 v00 v01 v11 : ℝ} (hγ : γ ≠ 1)
    (hA : 0 = (1 - γ) / (1 - γ) * Real.log β - γ * ((1 - γ) / (1 - γ)) * m0
      + (1 - γ) / (1 - γ) * m1 + 1 / 2 * (γ * ((1 - γ) / (1 - γ))) ^ 2 * v00
      - γ * ((1 - γ) / (1 - γ)) * ((1 - γ) / (1 - γ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - γ)) ^ 2 * v11)
    (hB : 0 = rf + (1 - γ) / (1 - γ) * Real.log β - γ * ((1 - γ) / (1 - γ)) * m0
      + ((1 - γ) / (1 - γ) - 1) * m1 + 1 / 2 * (γ * ((1 - γ) / (1 - γ))) ^ 2 * v00
      - γ * ((1 - γ) / (1 - γ)) * ((1 - γ) / (1 - γ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - γ) - 1) ^ 2 * v11) :
    rf = lgRf β γ m0 v00 := by
  have e := Miao.RecursiveUtility.eq_20_33 hγ hγ hA hB
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  rw [e, lgRf]
  field_simp
  ring

/-- AKMM, p. 490: in the Epstein–Zin premium (Miao's (20.35)) the weights
`ρ(1 − γ)/(1 − ρ)` on `σ_ic` and `(γ − ρ)/(1 − ρ)` on `σ_iw` move with risk aversion `γ` for
fixed `ρ`: for `ρ < 1` the second is strictly increasing in `γ`. -/
theorem ez_premium_weights {ρ γ₁ γ₂ : ℝ} (hρ1 : ρ < 1) (h : γ₁ < γ₂) :
    (γ₁ - ρ) / (1 - ρ) < (γ₂ - ρ) / (1 - ρ) :=
  div_lt_div_of_pos_right (by linarith) (by linarith)

end AKMM.AssetPrices

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Figure 16.4: the equity premium puzzle

AKMM, §16.6, p. 488 and Figure 16.4. The figure plots the (mean riskless rate, equity premium)
pairs of the Mehra–Prescott economy (`MehraPrescott`) for `β ∈ [0, 1]` and `γ ∈ [0, 100]`, keeping
the equilibria with `E[rᶠ] < 4%`, and the text reads off it that "the equity premium is less than
0.1 percent". The growth process is fixed by Table 16.1: `G_{L,H} = 1 + μ ∓ δ` with `μ = 0.0175`,
`δ = 0.0233` and `2φ − 1 = 0.1069` (three moments, three parameters; `mpf_primitives`).

* The premium is an average of conditional covariances (`mpf_premium_cov`, from
  `mpf_cond_cov`): `E[rˢ] − E[rᶠ] = ½ Σᵢ φ(1 − φ)(G_L^{−γ} − G_H^{−γ})(G_H(1 + v_H) −
  G_L(1 + v_L))/(Eᵢ[G^{−γ}]vᵢ)`, for every symmetric chain.
* In the figure's range, `E[rᶠ] < 4%` forces `γ < 5/2` (`mpf_gamma_lt`), by convexity of
  `γ ↦ G^{−γ}` and the harmonic–arithmetic mean inequality.
* **Corrected claim**: on the whole region the equity premium is positive (for `γ > 0`) and below
  `0.17%` (`mpf_premium_bound`, via the scalar steps `mpf_core_*`): the two price–dividend ratios
  differ by less than `0.81%`, both exceed `0.94(1 + v_L)`, and the bond prices exceed `0.955`.
* **The printed bound fails**: at `β = 1`, `γ = 9/4` the equilibrium exists (`ρ(A) < 1`), the
  mean riskless rate is about `3.78%` and the premium about `0.103% > 0.1%`
  (`mpf_counterexample`, `mpf_fig_16_4_printed_false`), with `G^{−9/4}` enclosed to `10⁻⁷` by
  exact rational arithmetic (`mpf_ce_bounds`).

Everything is proved for the whole parametric region, not at grid points; the only numbers are the
text's primitives. Left open: the exact supremum of the premium on the region (between `0.103%`
and `0.17%`).
-/

namespace AKMM.AssetPrices

open Matrix SargentStachurski.StochasticDiscounting

/-- AKMM, (16.26)–(16.27), p. 487: the conditional equity premium in one state. With
transition probabilities `(p, q)`, stochastic discount factor `βbⱼ` (`bⱼ = Gⱼ^{−γ}`) and stock
payoffs `uⱼ = Gⱼ(1 + vⱼ)` priced by `v = βE[bu]`, the expected stock return minus the riskless
rate is `pq(b_L − b_H)(u_H − u_L)/(E[b]·v)`: minus the conditional covariance of the payoff with
the discount factor. -/
theorem mpf_cond_cov {p q β bL bH uL uH v : ℝ} (hpq : p + q = 1) (hβ : β ≠ 0)
    (he : p * bL + q * bH ≠ 0) (hv0 : v ≠ 0) (hv : v = β * (p * bL * uL + q * bH * uH)) :
    p * (uL / v - 1) + q * (uH / v - 1) - (1 / (β * (p * bL + q * bH)) - 1) =
      p * q * (bL - bH) * (uH - uL) / ((p * bL + q * bH) * v) := by
  have hq : q = 1 - p := by linarith
  subst hq
  rw [eq_div_iff (mul_ne_zero he hv0)]
  field_simp
  linear_combination -hv

/-- `G^{1−γ} = G·G^{−γ}`: the weights `Aᵢⱼ = ΠᵢⱼGⱼ^{1−γ}` of p. 486 are growth times the
marginal-utility ratio. -/
theorem mpf_rpow_one_sub {G : ℝ} (hG : 0 < G) (γ : ℝ) : G ^ (1 - γ) = G * G ^ (-γ) := by
  rw [sub_eq_add_neg, Real.rpow_add hG, Real.rpow_one]

/-- AKMM, p. 486: the two scalar equations of `v = βA(1 + v)`. -/
theorem mpf_pd_eqs {φ β γ : ℝ} {G v : Fin 2 → ℝ} (hG : ∀ j, 0 < G j)
    (hv : v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i)) :
    v 0 = β * (φ * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + (1 - φ) * G 1 ^ (-γ) * (G 1 * (1 + v 1))) ∧
      v 1 = β * ((1 - φ) * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + φ * G 1 ^ (-γ) * (G 1 * (1 + v 1)))
      := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, mpA, Matrix.of_apply,
    mpPi, smul_eq_mul, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1)] at h0 h1
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1
  constructor
  · linear_combination h0
  · linear_combination h1

/-- AKMM, p. 487: the bond prices `pᶠᵢ = β Σⱼ ΠᵢⱼGⱼ^{−γ}` (`mp_bond_price`). -/
theorem mpf_bond_eqs (φ β γ : ℝ) (G : Fin 2 → ℝ) :
    mpBond φ β γ G 0 = β * (φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ)) ∧
      mpBond φ β γ G 1 = β * ((1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ)) :=
  mp_bond_price φ β γ G

/-- AKMM, (16.26)–(16.27), p. 487, the equity premium of the Mehra–Prescott economy as an
average of conditional covariances: for any symmetric chain `φ ∈ [0, 1]`, any positive growth
states and any positive price–dividend ratio `v = βA(1 + v)`,
`E[rˢ] − E[rᶠ] = ½ Σᵢ φ(1 − φ)(G_L^{−γ} − G_H^{−γ})(G_H(1 + v_H) − G_L(1 + v_L))/(Eᵢ[G^{−γ}]vᵢ)`.
The sign of the premium is the sign of `(G_L^{−γ} − G_H^{−γ})(G_H(1 + v_H) − G_L(1 + v_L))`. -/
theorem mpf_premium_cov {φ β γ : ℝ} {G v : Fin 2 → ℝ} (hG : ∀ j, 0 < G j) (hβ : 0 < β)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hv0 : ∀ i, 0 < v i)
    (hv : v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i)) :
    mpEquityPremium φ β γ G (fun i j => G j * (1 + v j) / v i - 1) =
      ∑ i, ![1 / 2, 1 / 2] i * (φ * (1 - φ) * (G 0 ^ (-γ) - G 1 ^ (-γ)) *
        (G 1 * (1 + v 1) - G 0 * (1 + v 0)) / (mpBond φ 1 γ G i * v i)) := by
  obtain ⟨e0, e1⟩ := mpf_pd_eqs hG hv
  obtain ⟨b0, b1⟩ := mpf_bond_eqs φ β γ G
  obtain ⟨c0, c1⟩ := mpf_bond_eqs φ 1 γ G
  have p0 := Real.rpow_pos_of_pos (hG 0) (-γ)
  have p1 := Real.rpow_pos_of_pos (hG 1) (-γ)
  have h1φ : 0 ≤ 1 - φ := by linarith
  have hm := lt_min p0 p1
  have m0 := min_le_left (G 0 ^ (-γ)) (G 1 ^ (-γ))
  have m1 := min_le_right (G 0 ^ (-γ)) (G 1 ^ (-γ))
  have n0 : φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ) ≠ 0 := by
    have : 0 < φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ) := by
      nlinarith [mul_le_mul_of_nonneg_left m0 hφ0, mul_le_mul_of_nonneg_left m1 h1φ]
    exact this.ne'
  have n1 : (1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ) ≠ 0 := by
    have : 0 < (1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ) := by
      nlinarith [mul_le_mul_of_nonneg_left m1 hφ0, mul_le_mul_of_nonneg_left m0 h1φ]
    exact this.ne'
  have k0 := mpf_cond_cov (p := φ) (q := 1 - φ) (by ring) hβ.ne' n0 (hv0 0).ne' e0
  have k1 := mpf_cond_cov (p := 1 - φ) (q := φ) (uL := G 0 * (1 + v 0))
    (uH := G 1 * (1 + v 1)) (by ring) hβ.ne' n1 (hv0 1).ne'
    (by linear_combination e1)
  simp only [mpEquityPremium, mpUncondMean, mpCondMean, Fin.sum_univ_two, mpRf, b0, b1, c0, c1,
    mpPi]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, one_mul]
  linear_combination (1 / 2 : ℝ) * k0 + (1 / 2 : ℝ) * k1

/-- Figure 16.4, step 1 (scalar form): with `G^{−γ}` in the ranges of `γ ∈ [0, 5/2]`, a mean
riskless rate below 4% puts both bond prices above `0.955`. -/
theorem mpf_core_bond {β b0 b1 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb0 : 1 ≤ b0)
    (hb0' : b0 ≤ 10147 / 10000) (hb1 : 9048 / 10000 ≤ b1) (hb1' : b1 ≤ 1)
    (hrf : 1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
      1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1)) < 52 / 25) :
    955 / 1000 < β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) ∧
      β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) ≤
        β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) := by
  have hd : β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) -
      β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) = β * (1069 / 10000 * (b0 - b1)) := by
    ring
  have hx1 : 0 < β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) :=
    mul_pos hβ0 (by linarith)
  have hx0 : 0 < β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) :=
    mul_pos hβ0 (by linarith)
  have hgap : β * (1069 / 10000 * (b0 - b1)) ≤ 118 / 10000 := by nlinarith
  have hgap0 : 0 ≤ β * (1069 / 10000 * (b0 - b1)) := by
    have : 0 ≤ b0 - b1 := by linarith
    positivity
  refine ⟨?_, by linarith⟩
  by_contra h
  rw [not_lt] at h
  have i1 := one_div_le_one_div_of_le hx1 h
  have i0 := one_div_le_one_div_of_le hx0
    (show β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) ≤ 9668 / 10000 by linarith)
  have : (52 / 25 : ℝ) < 1 / (955 / 1000) + 1 / (9668 / 10000) := by norm_num
  linarith

/-- Figure 16.4, step 2 (scalar form): the two values of `1 + v` differ by at most `0.81%`,
from `(w_H − w_L)(1 − β(2φ − 1)a_H) = β(2φ − 1)(a_H − a_L)w_L`. -/
theorem mpf_core_ratio {β b0 b1 w0 w1 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb0 : 1 ≤ b0)
    (hb0' : b0 ≤ 10147 / 10000) (hb1 : 9048 / 10000 ≤ b1) (hb1' : b1 ≤ 1) (hw0 : 0 < w0)
    (hw : (w1 - w0) * (1 - β * (1069 / 10000) * (1301 / 1250) * b1) =
      β * (1069 / 10000) * (1301 / 1250 * b1 - 4971 / 5000 * b0) * w0) :
    w1 - w0 ≤ 81 / 10000 * w0 ∧ -(81 / 10000 * w0) ≤ w1 - w0 := by
  have hD : 8887 / 10000 ≤ 1 - β * (1069 / 10000) * (1301 / 1250) * b1 := by nlinarith
  have hc1 : β * (1301 / 1250 * b1 - 4971 / 5000 * b0) ≤ 466 / 10000 := by
    nlinarith [mul_nonneg hβ0.le (show (0 : ℝ) ≤ 466 / 10000 -
      (1301 / 1250 * b1 - 4971 / 5000 * b0) by linarith)]
  have hc2 : -(671 / 10000) ≤ β * (1301 / 1250 * b1 - 4971 / 5000 * b0) := by
    nlinarith [mul_nonneg hβ0.le (show (0 : ℝ) ≤ 671 / 10000 +
      (1301 / 1250 * b1 - 4971 / 5000 * b0) by linarith)]
  have hDp : (0 : ℝ) < 1 - β * (1069 / 10000) * (1301 / 1250) * b1 := by linarith
  have h2 := mul_le_mul_of_nonneg_left hD (by linarith : (0 : ℝ) ≤ 81 / 10000 * w0)
  constructor
  · by_contra h
    rw [not_le] at h
    have h1 := mul_lt_mul_of_pos_right h hDp
    have h3 := mul_le_mul_of_nonneg_right hc1 hw0.le
    linarith
  · by_contra h
    rw [not_le] at h
    have h1 := mul_lt_mul_of_pos_right h hDp
    have h3 := mul_le_mul_of_nonneg_right hc2 hw0.le
    linarith

/-- Figure 16.4, step 3 (scalar form): a price–dividend ratio `v = β Σⱼ Πᵢⱼbⱼuⱼ` is at least
`0.9417(1 + v_L)` when its bond price exceeds `0.955`. -/
theorem mpf_core_v {β b0 b1 p q x v w0 w1 : ℝ} (hβ0 : 0 < β) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hw0 : 0 < w0) (hwl : -(81 / 10000 * w0) ≤ w1 - w0)
    (hx : x = β * (p * b0 + q * b1)) (hx' : 955 / 1000 < x)
    (hv : v = β * (p * b0 * (4971 / 5000 * w0) + q * b1 * (1301 / 1250 * w1))) :
    9417 / 10000 * w0 ≤ v := by
  have hGw : 4971 / 5000 * (9919 / 10000 * w0) ≤ 1301 / 1250 * w1 := by linarith
  have h1 := mul_le_mul_of_nonneg_left hGw (mul_nonneg hq hb1)
  have h4 := mul_le_mul_of_nonneg_left h1 hβ0.le
  have h5 : 0 ≤ β * (p * b0 * w0) := by positivity
  have h2 : 4971 / 5000 * (9919 / 10000) * w0 * x ≤ v := by
    rw [hv, hx]
    linarith
  have h3 := mul_le_mul_of_nonneg_left hx'.le (by positivity : (0 : ℝ) ≤
    4971 / 5000 * (9919 / 10000) * w0)
  linarith

/-- Figure 16.4, step 4 (scalar form): the bound on one conditional premium. -/
theorem mpf_core_term {β d U e v x w0 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hd : 0 ≤ d)
    (hU0 : 0 ≤ U) (hU : U ≤ 5504 / 100000 * w0) (he : 0 < e) (hv : 0 < v) (hx : x = β * e)
    (hvw : 9417 / 10000 * w0 ≤ v) :
    11069 / 20000 * (1 - 11069 / 20000) * d * U / (e * v) ≤
      11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000) * (1 / x) := by
  have hxe : 11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000) *
      (1 / x) * (e * v) =
      11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000) * v / β := by
    rw [hx]
    field_simp
  rw [div_le_iff₀ (mul_pos he hv), hxe, le_div_iff₀ hβ0]
  have hp : 0 ≤ 11069 / 20000 * (1 - 11069 / 20000) * d := by positivity
  have q1 := mul_le_mul_of_nonneg_left hU hp
  have q2 := mul_le_mul_of_nonneg_left hvw (by positivity : (0 : ℝ) ≤
    11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000))
  have q3 := mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hp hU0)
  linear_combination q1 + q2 + q3

/-- Figure 16.4 (scalar form): on `γ ∈ [0, 5/2]`, `β ∈ (0, 1]`, with a mean riskless rate below
4%, the equity premium is below `0.17%`, and the stock payoff spread `G_H(1 + v_H) − G_L(1 + v_L)`
is positive. -/
theorem mpf_core {β b0 b1 v0 v1 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb0 : 1 ≤ b0)
    (hb0' : b0 ≤ 10147 / 10000) (hb1 : 9048 / 10000 ≤ b1) (hb1' : b1 ≤ 1) (hv0 : 0 < v0)
    (hv1 : 0 < v1)
    (e0 : v0 = β * (11069 / 20000 * b0 * (4971 / 5000 * (1 + v0)) +
      (1 - 11069 / 20000) * b1 * (1301 / 1250 * (1 + v1))))
    (e1 : v1 = β * ((1 - 11069 / 20000) * b0 * (4971 / 5000 * (1 + v0)) +
      11069 / 20000 * b1 * (1301 / 1250 * (1 + v1))))
    (hrf : 1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
      1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1)) < 52 / 25) :
    1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0)) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1)) < 17 / 10000 ∧
    0 < 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) := by
  obtain ⟨hx1', hx10⟩ := mpf_core_bond hβ0 hβ1 hb0 hb0' hb1 hb1' hrf
  have hx0' : 955 / 1000 < β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) := by linarith
  have hw : ((1 + v1) - (1 + v0)) * (1 - β * (1069 / 10000) * (1301 / 1250) * b1) =
      β * (1069 / 10000) * (1301 / 1250 * b1 - 4971 / 5000 * b0) * (1 + v0) := by
    linear_combination e1 - e0
  obtain ⟨hwu, hwl⟩ := mpf_core_ratio hβ0 hβ1 hb0 hb0' hb1 hb1' (by linarith) hw
  have hv0' := mpf_core_v hβ0 (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by linarith) hwl rfl hx0' e0
  have hv1' := mpf_core_v hβ0 (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by linarith) hwl rfl hx1' e1
  have hU : 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) ≤ 5504 / 100000 * (1 + v0) := by
    linarith
  have hU0 : 0 < 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) := by linarith
  have hd : 0 ≤ b0 - b1 := by linarith
  have hT0 := mpf_core_term (e := 11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) hβ0 hβ1 hd
    hU0.le hU (by linarith) hv0 rfl hv0'
  have hT1 := mpf_core_term (e := (1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) hβ0 hβ1 hd
    hU0.le hU (by linarith) hv1 rfl hv1'
  refine ⟨?_, hU0⟩
  set K := 11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) * (5504 / 100000) / (9417 / 10000)
    with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) (by norm_num)) (by norm_num)
  have hKu : K ≤ 11069 / 20000 * (1 - 11069 / 20000) * (1099 / 10000) * (5504 / 100000) /
      (9417 / 10000) := by
    rw [hK]
    gcongr
    linarith
  have hS := mul_le_mul_of_nonneg_left hrf.le hK0
  have : K * (1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1))) +
      K * (1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1))) =
      K * (1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
        1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1))) := by ring
  linarith

/-- The growth states of Figure 16.4: `fn5G μ δ` with Table 16.1's `μ = 0.0175`,
`δ = 0.0233`. -/
noncomputable def mpfG : Fin 2 → ℝ := fn5G (7 / 400) (233 / 10000)

/-- The persistence of Figure 16.4: `2φ − 1 = 0.1069` (Table 16.1's autocorrelation). -/
noncomputable def mpfPhi : ℝ := (1 + 1069 / 10000) / 2

/-- AKMM, p. 487, Table 16.1 and fn. 5: the growth process of Figure 16.4. The three
parameters `μ, δ, φ` are chosen by GMM to match three moments (exactly identified): with
`μ = 0.0175`, `δ = 0.0233`, `2φ − 1 = 0.1069`, the mean, standard deviation and autocorrelation
of consumption growth are those of Table 16.1. -/
theorem mpf_primitives :
    fn5Mean ![1 / 2, 1 / 2] mpfG - 1 = 7 / 400 ∧
      fn5Second ![1 / 2, 1 / 2] mpfG - fn5Mean ![1 / 2, 1 / 2] mpfG ^ 2 = (233 / 10000) ^ 2 ∧
      (fn5Cross ![1 / 2, 1 / 2] mpfG (mpPi mpfPhi) - fn5Mean ![1 / 2, 1 / 2] mpfG ^ 2) /
        (fn5Second ![1 / 2, 1 / 2] mpfG - fn5Mean ![1 / 2, 1 / 2] mpfG ^ 2) = 1069 / 10000 := by
  refine ⟨fn5_mean _ _, fn5_var _ _, ?_⟩
  rw [mpfG, fn5_autocorr _ _ mpfPhi (by norm_num), mpfPhi]
  norm_num

/-- The primitives of Figure 16.4: `G_L = 0.9942`, `G_H = 1.0408`, `φ = 0.55345`. -/
theorem mpf_values : mpfG 0 = 4971 / 5000 ∧ mpfG 1 = 1301 / 1250 ∧ mpfPhi = 11069 / 20000 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [mpfG, fn5G, mpfPhi]

/-- `(x^{5/2})² = x⁵`. -/
theorem mpf_sq_rpow {x : ℝ} (hx : 0 < x) : (x ^ (5 / 2 : ℝ)) ^ 2 = x ^ 5 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- For `γ ∈ [0, 5/2]`: `1 ≤ G_L^{−γ} ≤ 1.0147` (`G_L = 0.9942 < 1`). -/
theorem mpf_GL_bounds {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 5 / 2) :
    1 ≤ (4971 / 5000 : ℝ) ^ (-γ) ∧ (4971 / 5000 : ℝ) ^ (-γ) ≤ 10147 / 10000 := by
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num)
    (by linarith), le_trans (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show -(5 / 2 : ℝ) ≤ -γ by linarith)) ?_⟩
  have hy := mpf_sq_rpow (show (0 : ℝ) < 4971 / 5000 by norm_num)
  have hyp : 0 < (4971 / 5000 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num)]
  have : (10000 / 10147 : ℝ) ≤ (4971 / 5000 : ℝ) ^ (5 / 2 : ℝ) := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h hyp.le (by norm_num : (2 : ℕ) ≠ 0)
    rw [hy] at this
    norm_num at this
  calc ((4971 / 5000 : ℝ) ^ (5 / 2 : ℝ))⁻¹ ≤ (10000 / 10147 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) this
    _ = 10147 / 10000 := by norm_num

/-- For `γ ∈ [0, 5/2]`: `0.9048 ≤ G_H^{−γ} ≤ 1` (`G_H = 1.0408 > 1`). -/
theorem mpf_GH_bounds {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 5 / 2) :
    9048 / 10000 ≤ (1301 / 1250 : ℝ) ^ (-γ) ∧ (1301 / 1250 : ℝ) ^ (-γ) ≤ 1 := by
  refine ⟨le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (show -(5 / 2 : ℝ) ≤ -γ by linarith)),
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)⟩
  have hy := mpf_sq_rpow (show (0 : ℝ) < 1301 / 1250 by norm_num)
  have hyp : 0 < (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num)]
  have : (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) ≤ 10000 / 9048 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
    rw [hy] at this
    norm_num at this
  calc (9048 / 10000 : ℝ) = (10000 / 9048 : ℝ)⁻¹ := by norm_num
    _ ≤ ((1301 / 1250 : ℝ) ^ (5 / 2 : ℝ))⁻¹ := inv_anti₀ hyp this

/-- `γ ↦ x^{−γ}` is convex: on `[5/2, 100]` it lies below the chord (weighted AM–GM). -/
theorem mpf_rpow_convex {x γ : ℝ} (hx : 0 < x) (h0 : 5 / 2 ≤ γ) (h1 : γ ≤ 100) :
    x ^ (-γ) ≤ (100 - γ) / (195 / 2) * x ^ (-(5 / 2) : ℝ) +
      (γ - 5 / 2) / (195 / 2) * x ^ (-100 : ℝ) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (100 - γ) / (195 / 2))
    (w₂ := (γ - 5 / 2) / (195 / 2)) (p₁ := x ^ (-(5 / 2) : ℝ)) (p₂ := x ^ (-100 : ℝ))
    (by apply div_nonneg <;> linarith) (by apply div_nonneg <;> linarith)
    (Real.rpow_pos_of_pos hx _).le (Real.rpow_pos_of_pos hx _).le (by field_simp; ring)
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx] at h
  convert h using 2
  field_simp
  ring

/-- The chord endpoints: `G_L^{−5/2} + G_H^{−5/2} ≤ 1.9196` and
`G_L^{−100} + G_H^{−100} ≤ 1.8084`. -/
theorem mpf_far_bounds :
    (4971 / 5000 : ℝ) ^ (-(5 / 2) : ℝ) + (1301 / 1250 : ℝ) ^ (-(5 / 2) : ℝ) ≤ 19196 / 10000 ∧
      (4971 / 5000 : ℝ) ^ (-100 : ℝ) + (1301 / 1250 : ℝ) ^ (-100 : ℝ) ≤ 18084 / 10000 := by
  have hL := (mpf_GL_bounds (γ := 5 / 2) (by norm_num) le_rfl).2
  have hy := mpf_sq_rpow (show (0 : ℝ) < 1301 / 1250 by norm_num)
  have hyp : 0 < (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hH : (1301 / 1250 : ℝ) ^ (-(5 / 2) : ℝ) ≤ 9049 / 10000 := by
    rw [Real.rpow_neg (by norm_num)]
    have : (10000 / 9049 : ℝ) ≤ (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) := by
      by_contra h
      rw [not_le] at h
      have := pow_lt_pow_left₀ h hyp.le (by norm_num : (2 : ℕ) ≠ 0)
      rw [hy] at this
      norm_num at this
    calc ((1301 / 1250 : ℝ) ^ (5 / 2 : ℝ))⁻¹ ≤ (10000 / 9049 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) this
      _ = 9049 / 10000 := by norm_num
  refine ⟨by linarith, ?_⟩
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
  norm_num

/-- AKMM, (16.27), p. 487: the mean riskless rate `E[rᶠ] = ½ Σᵢ 1/pᶠᵢ − 1`. -/
theorem mpf_rf_mean {φ β γ : ℝ} {G : Fin 2 → ℝ} :
    ∑ i, ![1 / 2, 1 / 2] i * mpRf φ β γ G i =
      (1 / (β * (φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ))) +
        1 / (β * ((1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ)))) / 2 - 1 := by
  obtain ⟨b0, b1⟩ := mpf_bond_eqs φ β γ G
  simp only [Fin.sum_univ_two, mpRf, b0, b1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The harmonic–arithmetic mean inequality `4/(x + y) ≤ 1/x + 1/y`. -/
theorem mpf_amhm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 4 / (x + y) ≤ 1 / x + 1 / y := by
  rw [div_add_div _ _ hx.ne' hy.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (x - y)]

/-- AKMM, Figure 16.4, p. 488: the region of the figure. For `β ∈ (0, 1]` and `γ ≤ 100`, a mean
riskless rate below 4% forces `γ < 5/2`: on `[5/2, 100]`, `G_L^{−γ} + G_H^{−γ} ≤ 1.9196` by
convexity, so the mean bond price is at most `0.9598` and `E[rᶠ] ≥ 1/0.9598 − 1 > 4%` (the mean of
`1/pᶠᵢ` is at least `1` over the mean of `pᶠᵢ`). -/
theorem mpf_gamma_lt {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ1 : γ ≤ 100)
    (hrf : ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi β γ mpfG i < 1 / 25) : γ < 5 / 2 := by
  obtain ⟨g0, g1, gφ⟩ := mpf_values
  rw [mpf_rf_mean, g0, g1, gφ] at hrf
  by_contra hγ
  rw [not_lt] at hγ
  set b0 := (4971 / 5000 : ℝ) ^ (-γ) with hb0
  set b1 := (1301 / 1250 : ℝ) ^ (-γ) with hb1
  have p0 : 0 < b0 := Real.rpow_pos_of_pos (by norm_num) _
  have p1 : 0 < b1 := Real.rpow_pos_of_pos (by norm_num) _
  have c0 := mpf_rpow_convex (x := 4971 / 5000) (by norm_num) hγ hγ1
  have c1 := mpf_rpow_convex (x := 1301 / 1250) (by norm_num) hγ hγ1
  obtain ⟨f1, f2⟩ := mpf_far_bounds
  have w1 : 0 ≤ (100 - γ) / (195 / 2) := by apply div_nonneg <;> linarith
  have w2 : 0 ≤ (γ - 5 / 2) / (195 / 2) := by apply div_nonneg <;> linarith
  have k1 := mul_le_mul_of_nonneg_left f1 w1
  have k2 := mul_le_mul_of_nonneg_left f2 w2
  have hsum : b0 + b1 ≤ 19196 / 10000 := by
    have : (100 - γ) / (195 / 2) + (γ - 5 / 2) / (195 / 2) = 1 := by field_simp; ring
    nlinarith
  have x0 : 0 < β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) := by positivity
  have x1 : 0 < β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) := by positivity
  have hm := mpf_amhm x0 x1
  have hxy : β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) +
      β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) ≤ 19196 / 10000 := by nlinarith
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (by positivity) hxy
  norm_num at this
  linarith

/-- **AKMM, Figure 16.4, p. 488 (corrected).** In the Mehra–Prescott economy with the growth
process of Table 16.1, for every `β ∈ (0, 1]`, `γ ∈ [0, 100]` and positive price–dividend ratio
`v = βA(1 + v)` with mean riskless rate below 4%, the equity premium is below `0.17%`, and it is
positive when `γ > 0`. (The printed bound `0.1%` fails: `mpf_counterexample`.) -/
theorem mpf_premium_bound {β γ : ℝ} {v : Fin 2 → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 100) (hv0 : ∀ i, 0 < v i)
    (hv : v = (β • mpA mpfPhi γ mpfG) *ᵥ (fun i => 1 + v i))
    (hrf : ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi β γ mpfG i < 1 / 25) :
    mpEquityPremium mpfPhi β γ mpfG (fun i j => mpfG j * (1 + v j) / v i - 1) < 17 / 10000 ∧
      (0 < γ → 0 < mpEquityPremium mpfPhi β γ mpfG (fun i j => mpfG j * (1 + v j) / v i - 1))
      := by
  have hγ := mpf_gamma_lt hβ0 hβ1 hγ1 hrf
  obtain ⟨g0, g1, gφ⟩ := mpf_values
  have hG : ∀ j, 0 < mpfG j := by
    intro j; fin_cases j <;> simp [g0, g1]
  obtain ⟨e0, e1⟩ := mpf_pd_eqs hG hv
  rw [mpf_premium_cov hG hβ0 (by rw [gφ]; norm_num) (by rw [gφ]; norm_num) hv0 hv]
  obtain ⟨c0, c1⟩ := mpf_bond_eqs mpfPhi 1 γ mpfG
  rw [mpf_rf_mean] at hrf
  simp only [Fin.sum_univ_two, c0, c1, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [g0, g1, gφ] at e0 e1 hrf ⊢
  obtain ⟨l0, l1⟩ := mpf_GL_bounds hγ0 hγ.le
  obtain ⟨h0, h1⟩ := mpf_GH_bounds hγ0 hγ.le
  have hrf' : 1 / (β * (11069 / 20000 * (4971 / 5000 : ℝ) ^ (-γ) +
      (1 - 11069 / 20000) * (1301 / 1250 : ℝ) ^ (-γ))) +
      1 / (β * ((1 - 11069 / 20000) * (4971 / 5000 : ℝ) ^ (-γ) +
        11069 / 20000 * (1301 / 1250 : ℝ) ^ (-γ))) < 52 / 25 := by linarith
  obtain ⟨hlt, hU⟩ := mpf_core hβ0 hβ1 l0 l1 h0 h1 (hv0 0) (hv0 1) e0 e1 hrf'
  refine ⟨by linarith, fun hγp => ?_⟩
  have hb : (1301 / 1250 : ℝ) ^ (-γ) < (4971 / 5000 : ℝ) ^ (-γ) := by
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg (x := 4971 / 5000) (z := -γ)
      (by norm_num) (by norm_num) (by linarith)
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := 1301 / 1250) (z := -γ)
      (by norm_num) (by linarith)
    linarith
  have hd : 0 < (4971 / 5000 : ℝ) ^ (-γ) - (1301 / 1250 : ℝ) ^ (-γ) := by linarith
  have p0 : 0 < (4971 / 5000 : ℝ) ^ (-γ) := by linarith
  have p1 : 0 < (1301 / 1250 : ℝ) ^ (-γ) := by linarith
  have q0 := hv0 0
  have q1 := hv0 1
  positivity

/-- `(x^{9/4})⁴ = x⁹`. -/
theorem mpf_pow4_rpow {x : ℝ} (hx : 0 < x) : (x ^ (9 / 4 : ℝ)) ^ 4 = x ^ 9 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- Enclosures of `G_L^{−9/4}` and `G_H^{−9/4}` to `10⁻⁷`. -/
theorem mpf_ce_bounds :
    10131740 / 10000000 ≤ (4971 / 5000 : ℝ) ^ (-(9 / 4) : ℝ) ∧
      (4971 / 5000 : ℝ) ^ (-(9 / 4) : ℝ) ≤ 10131741 / 10000000 ∧
      9139524 / 10000000 ≤ (1301 / 1250 : ℝ) ^ (-(9 / 4) : ℝ) ∧
      (1301 / 1250 : ℝ) ^ (-(9 / 4) : ℝ) ≤ 9139525 / 10000000 := by
  have hL := mpf_pow4_rpow (show (0 : ℝ) < 4971 / 5000 by norm_num)
  have hH := mpf_pow4_rpow (show (0 : ℝ) < 1301 / 1250 by norm_num)
  have pL : 0 < (4971 / 5000 : ℝ) ^ (9 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have pH : 0 < (1301 / 1250 : ℝ) ^ (9 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
  have a1 : (4971 / 5000 : ℝ) ^ (9 / 4 : ℝ) ≤ 10000000 / 10131740 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [hL] at this
    norm_num at this
  have a2 : 10000000 / 10131741 ≤ (4971 / 5000 : ℝ) ^ (9 / 4 : ℝ) := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h pL.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hL] at this
    norm_num at this
  have a3 : (1301 / 1250 : ℝ) ^ (9 / 4 : ℝ) ≤ 10000000 / 9139524 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [hH] at this
    norm_num at this
  have a4 : 10000000 / 9139525 ≤ (1301 / 1250 : ℝ) ^ (9 / 4 : ℝ) := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h pH.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hH] at this
    norm_num at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (10131740 / 10000000 : ℝ) = (10000000 / 10131740 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := inv_anti₀ pL a1
  · calc ((4971 / 5000 : ℝ) ^ (9 / 4 : ℝ))⁻¹ ≤ (10000000 / 10131741 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) a2
      _ = _ := by norm_num
  · calc (9139524 / 10000000 : ℝ) = (10000000 / 9139524 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := inv_anti₀ pH a3
  · calc ((1301 / 1250 : ℝ) ^ (9 / 4 : ℝ))⁻¹ ≤ (10000000 / 9139525 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) a4
      _ = _ := by norm_num

/-- The counterexample of Figure 16.4 (scalar form): the premium at `γ = 9/4`, `β = 1`
exceeds `0.1%`. -/
theorem mpf_ce_ep {b0 b1 D n0 n1 v0 v1 : ℝ} (l0 : 10131740 / 10000000 ≤ b0)
    (u0 : b0 ≤ 10131741 / 10000000) (l1 : 9139524 / 10000000 ≤ b1)
    (u1 : b1 ≤ 9139525 / 10000000) (hDp : 0 < D)
    (hn0 : n0 = 1 - 1069 / 10000 * (1301 / 1250 * b1))
    (hn1 : n1 = 1 - 1069 / 10000 * (4971 / 5000 * b0))
    (d0l : 87983 / 100000 ≤ n0 - D) (d0u : n0 - D ≤ 87984 / 100000)
    (d1l : 87384 / 100000 ≤ n1 - D) (d1u : n1 - D ≤ 87385 / 100000)
    (w0 : 1 + v0 = n0 / D) (w1 : 1 + v1 = n1 / D) (v0e : v0 = (n0 - D) / D)
    (v1e : v1 = (n1 - D) / D) :
    1 / 1000 < 1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0)) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1)) := by
  have e0p : 0 < 11069 / 20000 * b0 + (1 - 11069 / 20000) * b1 := by linarith
  have e1p : 0 < (1 - 11069 / 20000) * b0 + 11069 / 20000 * b1 := by linarith
  have hX : 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) =
      (1301 / 1250 * n1 - 4971 / 5000 * n0) / D := by
    rw [w0, w1]; ring
  have hXv : 1301 / 1250 * n1 - 4971 / 5000 * n0 = 466 / 10000 -
      1069 / 10000 * (4971 / 5000) * (1301 / 1250) * (b0 - b1) := by
    rw [hn0, hn1]; ring
  have hXl : 3562 / 100000 ≤ 1301 / 1250 * n1 - 4971 / 5000 * n0 := by rw [hXv]; linarith
  have t0 : 11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
      ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0) =
      11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * n1 - 4971 / 5000 * n0) /
      ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * (n0 - D)) := by
    rw [hX, v0e]
    field_simp
  have t1 : 11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
      (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1) =
      11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * n1 - 4971 / 5000 * n0) /
      (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * (n1 - D)) := by
    rw [hX, v1e]
    field_simp
  rw [t0, t1]
  have hdl : 9922 / 100000 ≤ b0 - b1 := by linarith
  have hnum : 11069 / 20000 * (1 - 11069 / 20000) * (9922 / 100000) * (3562 / 100000) ≤
      11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * n1 - 4971 / 5000 * n0) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul hdl hXl (by norm_num) (by linarith))
      (by norm_num : (0 : ℝ) ≤ 11069 / 20000 * (1 - 11069 / 20000))
    linear_combination this
  have den0 : (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * (n0 - D) ≤
      96887 / 100000 * (87984 / 100000) :=
    mul_le_mul (by linarith) d0u (by linarith) (by norm_num)
  have den1 : ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * (n1 - D) ≤
      95826 / 100000 * (87385 / 100000) :=
    mul_le_mul (by linarith) d1u (by linarith) (by norm_num)
  have f0 := div_le_div₀ (by positivity) hnum (by positivity) den0
  have f1 := div_le_div₀ (by positivity) hnum (by positivity) den1
  have : (1 / 1000 : ℝ) < 1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (9922 / 100000) *
      (3562 / 100000) / (96887 / 100000 * (87984 / 100000))) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (9922 / 100000) * (3562 / 100000) /
      (95826 / 100000 * (87385 / 100000))) := by norm_num
  linarith

/-- The counterexample of Figure 16.4 (scalar form): at `γ = 9/4`, `β = 1`, the vector
`vᵢ = nᵢ/D − 1` (Cramer's rule for `(I − A)(1 + v) = 𝟙`) is positive and solves `v = A(1 + v)`; the
mean riskless rate is below 4% and the equity premium above `0.1%`. -/
theorem mpf_ce_core {b0 b1 D v0 v1 : ℝ} (l0 : 10131740 / 10000000 ≤ b0)
    (u0 : b0 ≤ 10131741 / 10000000) (l1 : 9139524 / 10000000 ≤ b1)
    (u1 : b1 ≤ 9139525 / 10000000)
    (hD : D = 1 - 11069 / 20000 * (4971 / 5000 * b0 + 1301 / 1250 * b1) +
      1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1))
    (hv0 : v0 = (1 - 1069 / 10000 * (1301 / 1250 * b1)) / D - 1)
    (hv1 : v1 = (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1) :
    0 < v0 ∧ 0 < v1 ∧
    v0 = 1 * (11069 / 20000 * b0 * (4971 / 5000 * (1 + v0)) +
      (1 - 11069 / 20000) * b1 * (1301 / 1250 * (1 + v1))) ∧
    v1 = 1 * ((1 - 11069 / 20000) * b0 * (4971 / 5000 * (1 + v0)) +
      11069 / 20000 * b1 * (1301 / 1250 * (1 + v1))) ∧
    1 / (1 * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
      1 / (1 * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1)) < 52 / 25 ∧
    1 / 1000 < 1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0)) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1)) := by
  have pp := mul_le_mul l0 l1 (by norm_num) (by linarith)
  have qq := mul_le_mul u0 u1 (by linarith) (by norm_num)
  have hDl : 18476 / 1000000 ≤ D := by rw [hD]; linarith
  have hDp : 0 < D := by linarith
  set n0 := 1 - 1069 / 10000 * (1301 / 1250 * b1) with hn0
  set n1 := 1 - 1069 / 10000 * (4971 / 5000 * b0) with hn1
  have d0 : n0 - D = 11069 / 20000 * (4971 / 5000 * b0) + (1 - 11069 / 20000) *
      (1301 / 1250 * b1) - 1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1) := by
    rw [hD, hn0]; ring
  have d1 : n1 - D = 11069 / 20000 * (1301 / 1250 * b1) + (1 - 11069 / 20000) *
      (4971 / 5000 * b0) - 1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1) := by
    rw [hD, hn1]; ring
  have d0l : 87983 / 100000 ≤ n0 - D := by rw [d0]; linarith
  have d0u : n0 - D ≤ 87984 / 100000 := by rw [d0]; linarith
  have d1l : 87384 / 100000 ≤ n1 - D := by rw [d1]; linarith
  have d1u : n1 - D ≤ 87385 / 100000 := by rw [d1]; linarith
  have w0 : 1 + v0 = n0 / D := by rw [hv0]; ring
  have w1 : 1 + v1 = n1 / D := by rw [hv1]; ring
  have v0e : v0 = (n0 - D) / D := by rw [hv0]; field_simp
  have v1e : v1 = (n1 - D) / D := by rw [hv1]; field_simp
  have v0p : 0 < v0 := by rw [v0e]; exact div_pos (by linarith) hDp
  have v1p : 0 < v1 := by rw [v1e]; exact div_pos (by linarith) hDp
  have key0 : n0 - D = 11069 / 20000 * b0 * (4971 / 5000 * n0) +
      (1 - 11069 / 20000) * b1 * (1301 / 1250 * n1) := by rw [hD, hn0, hn1]; ring
  have key1 : n1 - D = (1 - 11069 / 20000) * b0 * (4971 / 5000 * n0) +
      11069 / 20000 * b1 * (1301 / 1250 * n1) := by rw [hD, hn0, hn1]; ring
  refine ⟨v0p, v1p, ?_, ?_, ?_, mpf_ce_ep l0 u0 l1 u1 hDp hn0 hn1 d0l d0u d1l d1u w0 w1 v0e v1e⟩
  · rw [w0, w1, v0e, key0]; field_simp
  · rw [w0, w1, v1e, key1]; field_simp
  · rw [one_mul, one_mul]
    have i0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 968866 / 1000000)
      (show 968866 / 1000000 ≤ 11069 / 20000 * b0 + (1 - 11069 / 20000) * b1 by linarith)
    have i1 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 958259 / 1000000)
      (show 958259 / 1000000 ≤ (1 - 11069 / 20000) * b0 + 11069 / 20000 * b1 by linarith)
    have : 1 / (968866 / 1000000 : ℝ) + 1 / (958259 / 1000000) < 52 / 25 := by norm_num
    linarith

/-- AKMM, p. 486: the two scalar equations give `v = βA(1 + v)`. -/
theorem mpf_pd_of_eqs {φ β γ : ℝ} {G v : Fin 2 → ℝ} (hG : ∀ j, 0 < G j)
    (e0 : v 0 = β * (φ * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + (1 - φ) * G 1 ^ (-γ) *
      (G 1 * (1 + v 1))))
    (e1 : v 1 = β * ((1 - φ) * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + φ * G 1 ^ (-γ) *
      (G 1 * (1 + v 1)))) :
    v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i) := by
  funext i
  fin_cases i
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, mpA, Matrix.of_apply,
      mpPi, smul_eq_mul, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1), Fin.zero_eta]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination e0
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, mpA, Matrix.of_apply,
      mpPi, smul_eq_mul, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1),
      Fin.mk_one]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination e1

/-- **AKMM, Figure 16.4, p. 488: the printed bound fails.** With the growth process of
Table 16.1, at `β = 1`, `γ = 9/4` (inside the figure's range) the price–dividend ratio
`v = (I − A)⁻¹A𝟙` exists (`ρ(A) < 1`, so by `mp_pd_unique` it is the only solution), the mean
riskless rate is below 4% (about 3.78%) and the equity premium exceeds `0.1%` (about 0.103%). -/
theorem mpf_counterexample :
    ∃ v : Fin 2 → ℝ, specRad ((1 : ℝ) • mpA mpfPhi (9 / 4) mpfG) < 1 ∧ (∀ i, 0 < v i) ∧
      v = ((1 : ℝ) • mpA mpfPhi (9 / 4) mpfG) *ᵥ (fun i => 1 + v i) ∧
      ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi 1 (9 / 4) mpfG i < 1 / 25 ∧
      1 / 1000 < mpEquityPremium mpfPhi 1 (9 / 4) mpfG
        (fun i j => mpfG j * (1 + v j) / v i - 1) := by
  obtain ⟨g0, g1, gφ⟩ := mpf_values
  have hG : ∀ j, 0 < mpfG j := by
    intro j; fin_cases j <;> simp [g0, g1]
  obtain ⟨l0, u0, l1, u1⟩ := mpf_ce_bounds
  set b0 := (4971 / 5000 : ℝ) ^ (-(9 / 4) : ℝ) with hb0
  set b1 := (1301 / 1250 : ℝ) ^ (-(9 / 4) : ℝ) with hb1
  set D := 1 - 11069 / 20000 * (4971 / 5000 * b0 + 1301 / 1250 * b1) +
      1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1) with hD
  obtain ⟨p0, p1, e0, e1, hr, hep⟩ := mpf_ce_core (v0 := (1 - 1069 / 10000 * (1301 / 1250 * b1))
    / D - 1) (v1 := (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1) l0 u0 l1 u1 hD rfl rfl
  set v : Fin 2 → ℝ := ![(1 - 1069 / 10000 * (1301 / 1250 * b1)) / D - 1,
    (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1] with hvdef
  have hv0 : ∀ i, 0 < v i := by
    intro i; fin_cases i
    · exact p0
    · exact p1
  have hv : v = ((1 : ℝ) • mpA mpfPhi (9 / 4) mpfG) *ᵥ (fun i => 1 + v i) := by
    apply mpf_pd_of_eqs hG
    · rw [g0, g1, gφ]; exact e0
    · rw [g0, g1, gφ]; exact e1
  refine ⟨v, ?_, hv0, hv, ?_, ?_⟩
  · refine mp_specRad_lt_one (φ := mpfPhi) (γ := 9 / 4) (β := 1) (G := mpfG) (C := 99 / 100)
      (by rw [gφ]; norm_num) (by rw [gφ]; norm_num)
      (by norm_num) hG (by norm_num) (fun i => ?_)
    fin_cases i
    · simp only [Fin.sum_univ_two, mpPi, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1)]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, g0, g1, gφ, Fin.zero_eta]
      rw [← hb0, ← hb1]
      linarith
    · simp only [Fin.sum_univ_two, mpPi, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1)]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, g0, g1, gφ, Fin.mk_one]
      rw [← hb0, ← hb1]
      linarith
  · rw [mpf_rf_mean, g0, g1, gφ]
    linarith
  · rw [mpf_premium_cov hG one_pos (by rw [gφ]; norm_num) (by rw [gφ]; norm_num) hv0 hv]
    obtain ⟨c0, c1⟩ := mpf_bond_eqs mpfPhi 1 (9 / 4) mpfG
    simp only [Fin.sum_univ_two, c0, c1, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hva : v 0 = (1 - 1069 / 10000 * (1301 / 1250 * b1)) / D - 1 := rfl
    have hvb : v 1 = (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1 := rfl
    rw [g0, g1, gφ, ← hb0, ← hb1, hva, hvb]
    linarith

/-- **AKMM, Figure 16.4, p. 488, as printed, is false**: it is not true that every equilibrium
of the figure's range (`β ∈ (0, 1]`, `γ ∈ [0, 100]`) with mean riskless rate below 4% has an equity
premium below `0.1%`. -/
theorem mpf_fig_16_4_printed_false :
    ¬ ∀ (β γ : ℝ) (v : Fin 2 → ℝ), 0 < β → β ≤ 1 → 0 ≤ γ → γ ≤ 100 → (∀ i, 0 < v i) →
      v = (β • mpA mpfPhi γ mpfG) *ᵥ (fun i => 1 + v i) →
      ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi β γ mpfG i < 1 / 25 →
      mpEquityPremium mpfPhi β γ mpfG (fun i j => mpfG j * (1 + v j) / v i - 1) < 1 / 1000 := by
  intro h
  obtain ⟨v, -, hv0, hv, hrf, hep⟩ := mpf_counterexample
  have := h 1 (9 / 4) v one_pos le_rfl (by norm_num) (by norm_num) hv0 hv hrf
  linarith

end AKMM.AssetPrices

set_option linter.style.longLine false
#print axioms AKMM.AssetPrices.tpW
#print axioms AKMM.AssetPrices.tp_W_none
#print axioms AKMM.AssetPrices.tp_W_some
#print axioms AKMM.AssetPrices.tpIsArbitrage
#print axioms AKMM.AssetPrices.tpNoArbitrage
#print axioms AKMM.AssetPrices.tpArbitrageBook
#print axioms AKMM.AssetPrices.tp_isArbitrage_iff_book
#print axioms AKMM.AssetPrices.tpArbitrageFree
#print axioms AKMM.AssetPrices.tp_noArbitrage_iff_free
#print axioms AKMM.AssetPrices.tpAttainable
#print axioms AKMM.AssetPrices.tp_noArbitrage_iff_attainable
#print axioms AKMM.AssetPrices.tpStatePrices
#print axioms AKMM.AssetPrices.tpQhat
#print axioms AKMM.AssetPrices.tp_qhat_orth
#print axioms AKMM.AssetPrices.eq_16_13
#print axioms AKMM.AssetPrices.tp_noArbitrage_of_statePrices
#print axioms AKMM.AssetPrices.tp_ftap
#print axioms AKMM.AssetPrices.tp_arrow_price_pos
#print axioms AKMM.AssetPrices.tp_law_of_one_price
#print axioms AKMM.AssetPrices.tp_loop_assets
#print axioms AKMM.AssetPrices.eq_16_12
#print axioms AKMM.AssetPrices.tp_complete_iff_rank
#print axioms AKMM.AssetPrices.tp_rank_iff_transpose_injective
#print axioms AKMM.AssetPrices.tp_statePrices_unique_iff_rank
#print axioms AKMM.AssetPrices.tp_statePrices_inverse
#print axioms AKMM.AssetPrices.tp_statePrices_block
#print axioms AKMM.AssetPrices.ex1D
#print axioms AKMM.AssetPrices.ex1p
#print axioms AKMM.AssetPrices.ex1_complete
#print axioms AKMM.AssetPrices.ex1q
#print axioms AKMM.AssetPrices.ex1_statePrices_formula
#print axioms AKMM.AssetPrices.ex1_statePrices_eq
#print axioms AKMM.AssetPrices.ex1_noArbitrage_iff
#print axioms AKMM.AssetPrices.ex1_returns_iff
#print axioms AKMM.AssetPrices.ex1_prices_pos
#print axioms AKMM.AssetPrices.ex1θ
#print axioms AKMM.AssetPrices.ex1_value
#print axioms AKMM.AssetPrices.ex1_value_pos
#print axioms AKMM.AssetPrices.ex2D
#print axioms AKMM.AssetPrices.ex2_incomplete
#print axioms AKMM.AssetPrices.ex2_noArbitrage_iff
#print axioms AKMM.AssetPrices.ex2_statePrices_iff
#print axioms AKMM.AssetPrices.ex2_disagreement
#print axioms AKMM.AssetPrices.tpBudget
#print axioms AKMM.AssetPrices.tpBudgetPos
#print axioms AKMM.AssetPrices.eq_16_10
#print axioms AKMM.AssetPrices.tp_noArbitrage_of_optimal
#print axioms AKMM.AssetPrices.tp_budgetPos_isCompact
#print axioms AKMM.AssetPrices.tp_endowment_mem
#print axioms AKMM.AssetPrices.tp_exists_optimal
#print axioms AKMM.AssetPrices.tp_exists_optimal_iff
#print axioms AKMM.AssetPrices.tpArrowOne
#print axioms AKMM.AssetPrices.tpBondOnly
#print axioms AKMM.AssetPrices.tp_no_optimal_without_nonneg
#print axioms AKMM.AssetPrices.tp_budget_single
#print axioms AKMM.AssetPrices.tpBudgetQ
#print axioms AKMM.AssetPrices.tpBudgetBind
#print axioms AKMM.AssetPrices.eq_16_14
#print axioms AKMM.AssetPrices.eq_16_14_counterexample
#print axioms AKMM.AssetPrices.tp_budget_complete
#print axioms AKMM.AssetPrices.tp_clm_apply
#print axioms AKMM.AssetPrices.tp_portfolio_foc
#print axioms AKMM.AssetPrices.eq_16_15
#print axioms AKMM.AssetPrices.tp_crra_marginal
#print axioms AKMM.AssetPrices.tp_crra_statePrice
#print axioms AKMM.AssetPrices.tp_riskNeutral_statePrice
#print axioms AKMM.AssetPrices.tp_agreement_complete
#print axioms AKMM.AssetPrices.sdfM
#print axioms AKMM.AssetPrices.sdf_mul_M
#print axioms AKMM.AssetPrices.sdf_price
#print axioms AKMM.AssetPrices.sdf_return
#print axioms AKMM.AssetPrices.sdf_bond
#print axioms AKMM.AssetPrices.eq_16_16
#print axioms AKMM.AssetPrices.sdf_risk_adjustment
#print axioms AKMM.AssetPrices.eq_16_17
#print axioms AKMM.AssetPrices.eq_16_17_printed_counterexample
#print axioms AKMM.AssetPrices.riskNeutral
#print axioms AKMM.AssetPrices.riskNeutral_pos
#print axioms AKMM.AssetPrices.riskNeutral_sum
#print axioms AKMM.AssetPrices.eq_16_18
#print axioms AKMM.AssetPrices.riskNeutral_unique_of_complete
#print axioms AKMM.AssetPrices.riskNeutral_unique_iff
#print axioms AKMM.AssetPrices.en_line_deriv
#print axioms AKMM.AssetPrices.enFeasible
#print axioms AKMM.AssetPrices.enPlannerOpt
#print axioms AKMM.AssetPrices.eq_16_1_pair
#print axioms AKMM.AssetPrices.eq_16_1
#print axioms AKMM.AssetPrices.en_plannerValue
#print axioms AKMM.AssetPrices.en_plannerValue_eq
#print axioms AKMM.AssetPrices.en_plannerValue_ge
#print axioms AKMM.AssetPrices.eq_16_2
#print axioms AKMM.AssetPrices.eq_16_3
#print axioms AKMM.AssetPrices.enBudgetAD
#print axioms AKMM.AssetPrices.eq_16_4_pair
#print axioms AKMM.AssetPrices.eq_16_4
#print axioms AKMM.AssetPrices.eq_16_4_pos
#print axioms AKMM.AssetPrices.eq_16_5
#print axioms AKMM.AssetPrices.en_weights_match
#print axioms AKMM.AssetPrices.en_concave_le_fderiv
#print axioms AKMM.AssetPrices.en_fwt_planner
#print axioms AKMM.AssetPrices.en_fwt_pareto
#print axioms AKMM.AssetPrices.eqBudgetAD
#print axioms AKMM.AssetPrices.eqSeq
#print axioms AKMM.AssetPrices.eqAD
#print axioms AKMM.AssetPrices.eq_budgetPos_complete
#print axioms AKMM.AssetPrices.eq_seq_to_ad
#print axioms AKMM.AssetPrices.eq_ad_to_seq
#print axioms AKMM.AssetPrices.eq_planner_bound
#print axioms AKMM.AssetPrices.eq_repAgent
#print axioms AKMM.AssetPrices.eq_repAgent_statePrice
#print axioms AKMM.AssetPrices.DTree
#print axioms AKMM.AssetPrices.DTree.mk
#print axioms AKMM.AssetPrices.DTree.parent
#print axioms AKMM.AssetPrices.DTree.depth
#print axioms AKMM.AssetPrices.DTree.depth_parent
#print axioms AKMM.AssetPrices.dtTwoPeriod
#print axioms AKMM.AssetPrices.dtPrev
#print axioms AKMM.AssetPrices.dtPayoff
#print axioms AKMM.AssetPrices.dtPayoffLin
#print axioms AKMM.AssetPrices.dtNoArbitrage
#print axioms AKMM.AssetPrices.dt_sum_parent
#print axioms AKMM.AssetPrices.dt_value_payoff
#print axioms AKMM.AssetPrices.dt_ftap_deflator
#print axioms AKMM.AssetPrices.dtDeflatorAux
#print axioms AKMM.AssetPrices.dtDeflator
#print axioms AKMM.AssetPrices.dt_deflator_pos
#print axioms AKMM.AssetPrices.dt_deflator_parent
#print axioms AKMM.AssetPrices.dt_ftap
#print axioms AKMM.AssetPrices.dt_statePrices_unique
#print axioms AKMM.AssetPrices.euBudget
#print axioms AKMM.AssetPrices.eu_foc
#print axioms AKMM.AssetPrices.eq_16_19
#print axioms AKMM.AssetPrices.eu_noArbitrage
#print axioms AKMM.AssetPrices.eu_crra_partial
#print axioms AKMM.AssetPrices.eq_16_21
#print axioms AKMM.AssetPrices.eq_16_23
#print axioms AKMM.AssetPrices.eu_conditional_premium
#print axioms AKMM.AssetPrices.mpPi
#print axioms AKMM.AssetPrices.mp_stationary_iff
#print axioms AKMM.AssetPrices.mp_pd_step
#print axioms AKMM.AssetPrices.mpA
#print axioms AKMM.AssetPrices.mp_pd_unique
#print axioms AKMM.AssetPrices.mp_pd_series
#print axioms AKMM.AssetPrices.mp_specRad_lt_one
#print axioms AKMM.AssetPrices.eq_16_25
#print axioms AKMM.AssetPrices.mpCondMean
#print axioms AKMM.AssetPrices.mpUncondMean
#print axioms AKMM.AssetPrices.mpBond
#print axioms AKMM.AssetPrices.mpRf
#print axioms AKMM.AssetPrices.mpEquityPremium
#print axioms AKMM.AssetPrices.mp_bond_price
#print axioms AKMM.AssetPrices.fn5Mean
#print axioms AKMM.AssetPrices.fn5Second
#print axioms AKMM.AssetPrices.fn5Cross
#print axioms AKMM.AssetPrices.fn5G
#print axioms AKMM.AssetPrices.fn5_mean
#print axioms AKMM.AssetPrices.fn5_var
#print axioms AKMM.AssetPrices.fn5_autocorr
#print axioms AKMM.AssetPrices.eq_16_29
#print axioms AKMM.AssetPrices.lgRf
#print axioms AKMM.AssetPrices.lg_rf_growth
#print axioms AKMM.AssetPrices.lg_rf_precautionary
#print axioms AKMM.AssetPrices.lg_rf_mono_iff
#print axioms AKMM.AssetPrices.lg_rf_strictMonoOn
#print axioms AKMM.AssetPrices.lg_rf_strictAntiOn
#print axioms AKMM.AssetPrices.lg_threshold_table
#print axioms AKMM.AssetPrices.lg_equity_euler
#print axioms AKMM.AssetPrices.eq_16_30
#print axioms AKMM.AssetPrices.lg_jensen
#print axioms AKMM.AssetPrices.lg_sd_product
#print axioms AKMM.AssetPrices.lg_gamma_bound
#print axioms AKMM.AssetPrices.lg_gamma_16_short
#print axioms AKMM.AssetPrices.lg_rf_high
#print axioms AKMM.AssetPrices.iid_pd_const
#print axioms AKMM.AssetPrices.iid_pd_unique
#print axioms AKMM.AssetPrices.iid_pd_solves
#print axioms AKMM.AssetPrices.eq_16_31
#print axioms AKMM.AssetPrices.eq_16_32
#print axioms AKMM.AssetPrices.iid_return_var
#print axioms AKMM.AssetPrices.iid_lognormal_pd
#print axioms AKMM.AssetPrices.lg_power_smoothing
#print axioms AKMM.AssetPrices.ez_rf_smoothing
#print axioms AKMM.AssetPrices.ez_power_case
#print axioms AKMM.AssetPrices.ez_premium_weights
#print axioms AKMM.AssetPrices.mpf_cond_cov
#print axioms AKMM.AssetPrices.mpf_rpow_one_sub
#print axioms AKMM.AssetPrices.mpf_pd_eqs
#print axioms AKMM.AssetPrices.mpf_bond_eqs
#print axioms AKMM.AssetPrices.mpf_premium_cov
#print axioms AKMM.AssetPrices.mpf_core_bond
#print axioms AKMM.AssetPrices.mpf_core_ratio
#print axioms AKMM.AssetPrices.mpf_core_v
#print axioms AKMM.AssetPrices.mpf_core_term
#print axioms AKMM.AssetPrices.mpf_core
#print axioms AKMM.AssetPrices.mpfG
#print axioms AKMM.AssetPrices.mpfPhi
#print axioms AKMM.AssetPrices.mpf_primitives
#print axioms AKMM.AssetPrices.mpf_values
#print axioms AKMM.AssetPrices.mpf_sq_rpow
#print axioms AKMM.AssetPrices.mpf_GL_bounds
#print axioms AKMM.AssetPrices.mpf_GH_bounds
#print axioms AKMM.AssetPrices.mpf_rpow_convex
#print axioms AKMM.AssetPrices.mpf_far_bounds
#print axioms AKMM.AssetPrices.mpf_rf_mean
#print axioms AKMM.AssetPrices.mpf_amhm
#print axioms AKMM.AssetPrices.mpf_gamma_lt
#print axioms AKMM.AssetPrices.mpf_premium_bound
#print axioms AKMM.AssetPrices.mpf_pow4_rpow
#print axioms AKMM.AssetPrices.mpf_ce_bounds
#print axioms AKMM.AssetPrices.mpf_ce_ep
#print axioms AKMM.AssetPrices.mpf_ce_core
#print axioms AKMM.AssetPrices.mpf_pd_of_eqs
#print axioms AKMM.AssetPrices.mpf_counterexample
#print axioms AKMM.AssetPrices.mpf_fig_16_4_printed_false
