/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDStatePrices
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Complete markets, Theorem 13.4.3 and Exercise 13.8

Miao, §13.4, pp. 430–432, and Exercise 13.8, p. 454.

* `rd_payoffMatrix f h` is the `J × S` payoff matrix `D_{t+1}(sᵗ)`. Rank `S` is equivalent to
  spanning every one-period payoff vector (`rd_rank_iff_span`) and to injectivity of
  `x ↦ D x` (`rd_rank_iff_injective`).
* `rd_CompletePrinted`: the book's definition of dynamically complete markets (every bounded
  `x` is the net cash flow of some strategy from date 1 on). Without any restriction on the
  strategy it is satisfied whenever prices are positive, by rolling one security over
  (`rd_completePrinted_of_pos`). So Exercise 13.8's "only if" is false as printed
  (`ex_13_8_counterexample`: one riskless bond, two states), and so is Theorem 13.4.3 with this
  definition (`theorem_13_4_3_counterexample`: two non-proportional state price processes).
* `rd_Complete`: completeness for finite-horizon payoffs replicated by strategies that are
  liquidated at the horizon. **Exercise 13.8** corrected (`ex_13_8`): markets are complete in
  this sense iff `D_{t+1}(sᵗ)` has rank `S` at every node; the "if" direction of the printed
  statement holds too (`ex_13_8_printed_if`).
* **Theorem 13.4.3** (`theorem_13_4_3`): with rank `S` at every node and no arbitrage on
  `R(Θ_DC)`, a state price process exists and is unique up to a positive factor; the one-period
  ratios are `x_{t+1} = (DᵀD)⁻¹ Dᵀ p_t` (`theorem_13_4_3_formula`).
* Arrow securities (p. 431): the payoff matrix is the identity, so markets are complete
  (`rd_arrow_rank`), and the Arrow prices are the ratios of state prices,
  `q⁰_{t+1}(sᵗ⁺¹) = Q_t(s_{t+1} | sᵗ) q⁰_t(sᵗ)` (`rd_arrow_statePrice`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

omit [Fintype S] [Fintype J] in
/-- The `J × S` payoff matrix `D_{t+1}(sᵗ)`: entry `(j, s)` is `f_{j,t+1}(sᵗ, s)`. -/
def rd_payoffMatrix (f : List S → J → ℝ) (h : List S) : Matrix J S ℝ :=
  Matrix.of fun j s => f (s :: h) j

omit [Fintype S] in
/-- `(D_{t+1}(sᵗ))ᵀ v` is the vector of payoffs `f_{t+1}(sᵗ, s) · v`. -/
theorem rd_payoffMatrix_transpose_mulVec (f : List S → J → ℝ) (h : List S) (v : J → ℝ)
    (s : S) : Matrix.mulVec (rd_payoffMatrix f h).transpose v s = f (s :: h) ⬝ᵥ v := by
  simp [rd_payoffMatrix, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype J] in
/-- `D_{t+1}(sᵗ) x` is the vector of the prices `∑ₛ xₛ f_{t+1}(sᵗ, s)`. -/
theorem rd_payoffMatrix_mulVec (f : List S → J → ℝ) (h : List S) (x : S → ℝ) (j : J) :
    Matrix.mulVec (rd_payoffMatrix f h) x j = ∑ s, x s * f (s :: h) j := by
  simp [rd_payoffMatrix, Matrix.mulVec, dotProduct, mul_comm]

/-- Rank `S` iff the securities span every one-period payoff vector at `sᵗ`. -/
theorem rd_rank_iff_span (f : List S → J → ℝ) (h : List S) :
    (rd_payoffMatrix f h).rank = Fintype.card S ↔
      ∀ z : S → ℝ, ∃ v : J → ℝ, ∀ s, f (s :: h) ⬝ᵥ v = z s := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  set M := (rd_payoffMatrix f h).transpose
  have hsurj : (∀ z : S → ℝ, ∃ v : J → ℝ, ∀ s, f (s :: h) ⬝ᵥ v = z s) ↔
      LinearMap.range M.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    constructor
    · intro H z
      obtain ⟨v, hv⟩ := H z
      exact ⟨v, funext fun s => by
        rw [Matrix.mulVecLin_apply, rd_payoffMatrix_transpose_mulVec, hv]⟩
    · intro H z
      obtain ⟨v, hv⟩ := H z
      exact ⟨v, fun s => by
        rw [← rd_payoffMatrix_transpose_mulVec, ← Matrix.mulVecLin_apply, hv]⟩
  rw [hsurj]
  constructor
  · intro hr
    exact Submodule.eq_top_of_finrank_eq (by rw [hr, Module.finrank_pi])
  · intro ht
    rw [ht, finrank_top, Module.finrank_pi]

omit [Fintype J] in
/-- Rank `S` iff `x ↦ D_{t+1}(sᵗ) x` is injective (the form used in Theorem 13.4.3). -/
theorem rd_rank_iff_injective (f : List S → J → ℝ) (h : List S) :
    (rd_payoffMatrix f h).rank = Fintype.card S ↔
      Function.Injective (Matrix.mulVec (rd_payoffMatrix f h)) := by
  rw [Matrix.rank]
  set M := rd_payoffMatrix f h
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_pi] at hrn
  have hinj : Function.Injective M.mulVec ↔ LinearMap.ker M.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rfl
  rw [hinj, ← Submodule.finrank_eq_zero]
  omega

/-- Book's definition of complete markets (Miao, pp. 430–431): for every bounded process `x`
there is a strategy with `f_t · θ_{t−1} − p_t · θ_t = x_t` at all nodes of date `t ≥ 1`. -/
def rd_CompletePrinted (p f : List S → J → ℝ) : Prop :=
  ∀ x : List S → ℝ, rd_Bdd x →
    ∃ θ : List S → J → ℝ, ∀ s h, f (s :: h) ⬝ᵥ θ h - p (s :: h) ⬝ᵥ θ (s :: h) = x (s :: h)

/-- Complete markets for finite-horizon payoffs: every bounded `x` vanishing after `T` is the net
cash flow, from date 1 on, of a strategy liquidated from date `T` on. -/
def rd_Complete (p f : List S → J → ℝ) : Prop :=
  ∀ x : List S → ℝ, rd_Bdd x → ∀ T : ℕ, (∀ g, T < g.length → x g = 0) →
    ∃ θ : List S → J → ℝ, (∀ g, T ≤ g.length → θ g = 0) ∧
      ∀ s h, f (s :: h) ⬝ᵥ θ h - p (s :: h) ⬝ᵥ θ (s :: h) = x (s :: h)

omit [Fintype S] in
/-- Rolling security `j₀` over: the strategy that finances any `x` from date 1 on. -/
noncomputable def rd_rollover [DecidableEq J] (p f : List S → J → ℝ) (x : List S → ℝ) (j0 : J) :
    List S → J → ℝ
  | [] => 0
  | s :: h => ((f (s :: h) ⬝ᵥ rd_rollover p f x j0 h - x (s :: h)) / p (s :: h) j0) •
      Pi.single j0 1

omit [Fintype S] in
/-- With strictly positive prices, the book's completeness condition always holds: the payoff
`x` is financed by rolling one security over. -/
theorem rd_completePrinted_of_pos [Nonempty J] (p f : List S → J → ℝ)
    (hp : ∀ h j, 0 < p h j) : rd_CompletePrinted p f := by
  classical
  intro x _
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  refine ⟨rd_rollover p f x j0, fun s h => ?_⟩
  simp only [rd_rollover, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  rw [div_mul_cancel₀ _ (hp _ j0).ne']
  ring

/-- **Exercise 13.8** (Miao, p. 454), the "if" direction of the printed statement: rank `S` at
every node (with positive prices) gives completeness in the book's sense. -/
theorem ex_13_8_printed_if [Nonempty J] (p f : List S → J → ℝ) (hp : ∀ h j, 0 < p h j)
    (_hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) : rd_CompletePrinted p f :=
  rd_completePrinted_of_pos p f hp

/-- **Exercise 13.8** (Miao, p. 454), counterexample to the printed "only if": with two states
and one riskless bond (price and payoff `1`), markets are complete in the book's sense but the
payoff matrix has rank `1 < 2`. -/
theorem ex_13_8_counterexample :
    rd_CompletePrinted (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) ∧
      ∀ h, (rd_payoffMatrix (S := Bool) (J := Unit) (fun _ _ => 1) h).rank ≠ Fintype.card Bool
    := by
  refine ⟨rd_completePrinted_of_pos _ _ fun _ _ => one_pos, fun h => ?_⟩
  have := Matrix.rank_le_card_height (rd_payoffMatrix (S := Bool) (J := Unit) (fun _ _ => 1) h)
  simp only [Fintype.card_unit] at this
  simp only [Fintype.card_bool]
  omega

omit [Fintype S] in
/-- Backward construction of a replicating strategy, `n` periods before liquidation. -/
noncomputable def rd_backward (p : List S → J → ℝ) (sol : List S → (S → ℝ) → J → ℝ)
    (x : List S → ℝ) : ℕ → List S → J → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun g => sol g fun s => x (s :: g) + p (s :: g) ⬝ᵥ rd_backward p sol x n (s :: g)

/-- **Exercise 13.8** (Miao, p. 454), corrected: markets are complete for finite-horizon payoffs
(`rd_Complete`) iff the payoff matrix `D_{t+1}(sᵗ)` has rank `S` at every node `sᵗ`. -/
theorem ex_13_8 (p f : List S → J → ℝ) :
    rd_Complete p f ↔ ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S := by
  classical
  simp only [rd_rank_iff_span]
  constructor
  · intro H h z
    set x : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: g' => if g' = h then z s else 0
    have hx : rd_Bdd x := by
      refine ⟨∑ s, |z s|, fun g => ?_⟩
      have h0 : 0 ≤ ∑ s, |z s| := Finset.sum_nonneg fun s _ => abs_nonneg _
      cases g with
      | nil => simpa [x] using h0
      | cons s g' =>
        simp only [x]
        split_ifs
        · exact Finset.single_le_sum (f := fun s => |z s|) (fun s _ => abs_nonneg _)
            (Finset.mem_univ s)
        · simpa using h0
    obtain ⟨θ, hθT, hθ⟩ := H x hx (h.length + 1) (fun g hg => by
      cases g with
      | nil => rfl
      | cons s g' =>
        have : g' ≠ h := by
          rintro rfl
          simp at hg
        simp [x, this])
    refine ⟨θ h, fun s => ?_⟩
    have := hθ s h
    rw [hθT (s :: h) (by simp)] at this
    simpa [x] using this
  · intro H x _ T hxT
    choose sol hsol using H
    refine ⟨fun g => rd_backward p sol x (T - g.length) g, fun g hg => ?_, fun s h => ?_⟩
    · simp only [Nat.sub_eq_zero_of_le hg, rd_backward]
    · simp only [List.length_cons]
      by_cases hT : h.length < T
      · have e : T - h.length = (T - (h.length + 1)) + 1 := by omega
        rw [e, rd_backward, hsol]
        ring
      · push Not at hT
        rw [Nat.sub_eq_zero_of_le hT, Nat.sub_eq_zero_of_le (by omega)]
        simp only [rd_backward, dotProduct_zero, sub_zero]
        exact (hxT (s :: h) (by simp; omega)).symm

omit [Fintype J] in
/-- The one-period ratio vector of a state price process, `x_{t+1}(sᵗ)_s = q⁰(sᵗ, s)/q⁰(sᵗ)`,
solves `D_{t+1}(sᵗ) x_{t+1}(sᵗ) = p_t(sᵗ)` (the proof of Theorem 13.4.3). -/
theorem rd_ratio_solves {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (h : List S) :
    Matrix.mulVec (rd_payoffMatrix f h) (fun s => q (s :: h) / q h) = p h := by
  funext j
  rw [rd_payoffMatrix_mulVec, hq.2 h j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype J] in
/-- Uniqueness in Theorem 13.4.3: with rank `S` at every node, any two state price processes are
proportional, `q′ = (q′(s⁰)/q(s⁰)) q`. -/
theorem rd_statePrice_unique {p f : List S → J → ℝ}
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) {q q' : List S → ℝ}
    (hq : rd_StatePrice p f q) (hq' : rd_StatePrice p f q') (h : List S) :
    q' h = q' [] / q [] * q h := by
  have hr : ∀ g s, q' (s :: g) / q' g = q (s :: g) / q g := by
    intro g s
    have := (rd_rank_iff_injective f g).1 (hrank g)
      ((rd_ratio_solves hq' g).trans (rd_ratio_solves hq g).symm)
    exact congrFun this s
  have key : ∀ g, q' g / q g = q' [] / q [] := by
    intro g
    induction g with
    | nil => rfl
    | cons s g ih =>
      rw [← ih]
      have := hr g s
      have h1 := (hq.1 g).ne'
      have h2 := (hq.1 (s :: g)).ne'
      have h3 := (hq'.1 g).ne'
      field_simp at this ⊢
      linarith
  rw [← key h]
  field_simp [(hq.1 h).ne']

/-- **Theorem 13.4.3** (Miao, p. 431). If the payoff matrix has rank `S` at every node and there
is no arbitrage on `R(Θ_DC(p, f))` (debt limits `D̄ ≥ 0`), then a state price process exists and
it is unique up to a positive scaling factor. -/
theorem theorem_13_4_3 (p f : List S → J → ℝ) {Dbar : List S → ℝ}
    (hD : ∀ h, 0 ≤ Dbar h) (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S)
    (hna : ¬ rd_ArbOn p f (rd_Rec (rd_ThetaDC f Dbar))) :
    (∃ q, rd_StatePrice p f q) ∧
      ∀ q q', rd_StatePrice p f q → rd_StatePrice p f q' → ∀ h, q' h = q' [] / q [] * q h := by
  classical
  refine ⟨(theorem_13_4_2 p f hD).1 fun h => ?_, fun q q' hq hq' h =>
    rd_statePrice_unique hrank hq hq' h⟩
  refine rd_noArbOn_noOneArbOn p f _ ?_ hna h
  intro θ hθ g
  rw [rd_rec_DC f hD] at hθ ⊢
  exact rd_loc_mem_recDC f hθ g

/-- **Theorem 13.4.3**, the formula in the proof (Miao, p. 431): with rank `S`, `DᵀD` is
invertible and the ratio vector is `x_{t+1}(sᵗ) = (DᵀD)⁻¹ Dᵀ p_t(sᵗ)`. -/
theorem theorem_13_4_3_formula [DecidableEq S] {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (h : List S)
    (hrank : (rd_payoffMatrix f h).rank = Fintype.card S) :
    IsUnit ((rd_payoffMatrix f h).transpose * rd_payoffMatrix f h) ∧
      (fun s => q (s :: h) / q h) =
        Matrix.mulVec ((rd_payoffMatrix f h).transpose * rd_payoffMatrix f h)⁻¹
          (Matrix.mulVec (rd_payoffMatrix f h).transpose (p h)) := by
  set D := rd_payoffMatrix f h
  have hinj := (rd_rank_iff_injective f h).1 hrank
  have hunit : IsUnit (D.transpose * D) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    apply hinj
    have hz : Matrix.mulVec (D.transpose * D) (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have : Matrix.mulVec D (v - w) ⬝ᵥ Matrix.mulVec D (v - w) = 0 := by
      have e : (v - w) ⬝ᵥ Matrix.mulVec (D.transpose * D) (v - w) =
          Matrix.mulVec D (v - w) ⬝ᵥ Matrix.mulVec D (v - w) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rw [← e, hz, dotProduct_zero]
    rw [dotProduct_self_eq_zero, Matrix.mulVec_sub, sub_eq_zero] at this
    exact this
  refine ⟨hunit, ?_⟩
  have hx := rd_ratio_solves hq h
  rw [← hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    show rd_payoffMatrix f h = D from rfl,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), Matrix.one_mulVec]

/-- **Theorem 13.4.3**, counterexample with the book's completeness condition: two states, one
riskless bond (price and payoff `1`). Markets are complete in the book's sense and there is no
arbitrage on `R(Θ_DC)` (limit `0`), yet the state price processes built from the ratios
`(1/2, 1/2)` and `(1/3, 2/3)` are not proportional. -/
theorem theorem_13_4_3_counterexample :
    rd_CompletePrinted (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) ∧
      ¬ rd_ArbOn (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1)
        (rd_Rec (rd_ThetaDC (fun _ _ => 1) (fun _ => 0))) ∧
      rd_StatePrice (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1)
        (rd_qOf fun _ _ => 1 / 2) ∧
      rd_StatePrice (S := Bool) (J := Unit) (fun _ _ => 1) (fun _ _ => 1)
        (rd_qOf fun _ s => if s then 1 / 3 else 2 / 3) ∧
      ¬ ∃ a : ℝ, ∀ h, rd_qOf (S := Bool) (fun _ s => if s then 1 / 3 else 2 / 3) h =
        a * rd_qOf (S := Bool) (fun _ _ => 1 / 2) h := by
  refine ⟨rd_completePrinted_of_pos _ _ fun _ _ => one_pos, ?_,
    rd_statePrice_qOf (fun _ _ => by norm_num) fun _ _ => by norm_num,
    rd_statePrice_qOf (fun _ s => by split_ifs <;> norm_num) fun _ _ => by norm_num, ?_⟩
  · rw [rd_rec_DC _ (fun _ => le_rfl)]
    rintro ⟨θ, hθ, hnn, g, hg⟩
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul,
      Set.mem_ofPred_eq] at hθ
    have h0 : ∀ g, θ g () = 0 := by
      intro g
      induction g with
      | nil =>
        have := hnn []
        simp only [rd_net, rd_fz, rd_prev, dotProduct, Finset.univ_unique, Finset.sum_singleton,
          Pi.zero_apply, mul_zero, one_mul, zero_sub] at this
        linarith [hθ [] true]
      | cons s g ih =>
        have := hnn (s :: g)
        simp only [rd_net, rd_fz, rd_prev, dotProduct, Finset.univ_unique, Finset.sum_singleton,
          one_mul, ih, zero_sub] at this
        linarith [hθ (s :: g) true]
    cases g with
    | nil => simp [rd_net, rd_prev, dotProduct, h0] at hg
    | cons s g => simp [rd_net, rd_fz, rd_prev, dotProduct, h0] at hg
  · rintro ⟨a, ha⟩
    have h0 := ha []
    have h1 := ha [true]
    simp only [rd_qOf, ↓reduceIte] at h0 h1
    norm_num at h0 h1
    rw [← h0] at h1
    norm_num at h1

/-- Arrow securities complete the market: their payoff matrix is the identity, of rank `S`
(Miao, p. 431). -/
theorem rd_arrow_rank [DecidableEq S] (h : List S) :
    (rd_payoffMatrix (rd_arrowPayoff (S := S)) h).rank = Fintype.card S := by
  have : rd_payoffMatrix (rd_arrowPayoff (S := S)) h = 1 := by
    ext j s
    simp [rd_payoffMatrix, rd_arrowPayoff, Matrix.one_apply]
  rw [this, Matrix.rank_one]

/-- Miao, p. 432: with Arrow securities priced at `Q_t(s′ | sᵗ)`, the state price equation
(13.16) is the relation `q⁰_{t+1}(sᵗ, s′) = Q_t(s′ | sᵗ) q⁰_t(sᵗ)`. -/
theorem rd_arrow_statePrice [DecidableEq S] (Q : List S → S → ℝ) (q : List S → ℝ)
    (hq : ∀ h, 0 < q h) :
    rd_StatePrice Q rd_arrowPayoff q ↔ ∀ h s, q (s :: h) = Q h s * q h := by
  have e : ∀ h s, (q h)⁻¹ * ∑ s', q (s' :: h) * rd_arrowPayoff (s' :: h) s =
      (q h)⁻¹ * q (s :: h) := by
    intro h s
    simp [rd_arrowPayoff]
  constructor
  · rintro ⟨-, H⟩ h s
    rw [H h s, e]
    field_simp [(hq h).ne']
  · intro H
    refine ⟨hq, fun h s => ?_⟩
    rw [e, H]
    field_simp [(hq h).ne']

end Miao.CompleteMarkets
