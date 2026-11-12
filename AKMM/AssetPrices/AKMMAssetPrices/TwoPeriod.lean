/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDStiemke
import InternationalFinancialMarkets.Spanning
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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
