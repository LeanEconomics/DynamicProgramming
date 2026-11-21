/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDSecurities
import CompleteMarkets.RDStiemke
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# No one-period arbitrage and state prices

Miao, §13.4, pp. 429–430.

* `rd_StatePrice p f q`: `q` is a strictly positive state price process satisfying the
  no-arbitrage pricing equation (13.16), `p_t = (1/q⁰_t) ∑_{sᵗ⁺¹|sᵗ} q⁰_{t+1} f_{t+1}`.
* **Theorem 13.4.2** for debt constraints (`theorem_13_4_2`): no one-period arbitrage on
  `R(Θ_DC)` at every node iff a state price process exists. The proof applies Stiemke's Lemma
  at each node to the `J × (S + 1)` matrix `[−p, f(·, 1), …, f(·, S)]` and chains the ratios.
* For borrowing constraints the book's "iff" is false as printed: if every security pays zero at
  some node, `R(Θ_BC)` admits no one-period arbitrage but (13.16) fails
  (`theorem_13_4_2_BC_counterexample`). With positive prices, nonnegative payoffs and a nonzero
  payoff at every node it is true (`theorem_13_4_2_BC`).
* (13.17)–(13.18): the state price deflator `rd_deflator`, the stochastic discount factor
  `rd_SDF`, and the pricing formula (`eq_13_18`); the normalisation `q⁰(s⁰) = 1`
  (`eq_13_17_normalize`), and "π need not lie in L¹" (`rd_statePrice_not_L1`).
* Short sales (p. 430): with `R(Θ_SC) = {θ ≥ 0}`, (13.16) need not hold
  (`rd_SC_no_statePrice`), but it holds as an inequality (`rd_SC_inequality`, which with
  positive prices is in fact automatic).
* Multi-period securities (pp. 425–426): a claim paying at distance `n + 1` is priced as the
  one-period payoff given by its next-period price (`rd_multiperiod_price`,
  `rd_twoPeriodBond`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

/-- **(13.16)**: `q` is a strictly positive state price process for `(p, f)`:
`p_t(sᵗ) = (1/q⁰_t(sᵗ)) ∑_{sᵗ⁺¹|sᵗ} q⁰_{t+1}(sᵗ⁺¹) f_{t+1}(sᵗ⁺¹)`. -/
def rd_StatePrice (p f : List S → J → ℝ) (q : List S → ℝ) : Prop :=
  (∀ h, 0 < q h) ∧ ∀ h j, p h j = (q h)⁻¹ * ∑ s, q (s :: h) * f (s :: h) j

omit [Fintype J] in
/-- (13.16) multiplied out: `q⁰_t p_t = ∑ q⁰_{t+1} f_{t+1}`. -/
theorem rd_statePrice_mul {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (h : List S) (j : J) : q h * p h j = ∑ s, q (s :: h) * f (s :: h) j := by
  rw [hq.2 h j, ← mul_assoc, mul_inv_cancel₀ (hq.1 h).ne', one_mul]

/-- (13.16) applied to a portfolio: `q⁰_t (p_t · v) = ∑ q⁰_{t+1} (f_{t+1} · v)`. -/
theorem rd_statePrice_dot {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (h : List S) (v : J → ℝ) : q h * (p h ⬝ᵥ v) = ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ v) := by
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, rd_statePrice_mul hq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype S] in
/-- The process obtained by chaining one-period ratios `r(sᵗ, s)` from `q(s⁰) = 1`. -/
def rd_qOf (r : List S → S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => rd_qOf r h * r h s

omit [Fintype S] in
theorem rd_qOf_pos {r : List S → S → ℝ} (hr : ∀ h s, 0 < r h s) (h : List S) :
    0 < rd_qOf r h := by
  induction h with
  | nil => exact one_pos
  | cons s h ih => exact mul_pos ih (hr h s)

omit [Fintype J] in
/-- A state price process built from ratios satisfying the one-period pricing equation. -/
theorem rd_statePrice_qOf {p f : List S → J → ℝ} {r : List S → S → ℝ} (hr : ∀ h s, 0 < r h s)
    (hp : ∀ h j, p h j = ∑ s, r h s * f (s :: h) j) : rd_StatePrice p f (rd_qOf r) := by
  refine ⟨rd_qOf_pos hr, fun h j => ?_⟩
  rw [hp h j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [rd_qOf]
  field_simp [(rd_qOf_pos hr h).ne']

/-- Positive state prices rule out one-period arbitrage at every node, on any set of
strategies. -/
theorem rd_noOneArb_of_statePrice {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (h : List S) (v : J → ℝ) : ¬ rd_OneArb p f h v := by
  rintro ⟨hp, hf, hs⟩
  have key := rd_statePrice_dot hq h v
  have hnn : 0 ≤ ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ v) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hq.1 _).le (hf s)
  rcases hs with hs | ⟨s, hs⟩
  · have : q h * (p h ⬝ᵥ v) < 0 := mul_neg_of_pos_of_neg (hq.1 h) hs
    linarith
  · have : 0 < ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ v) :=
      Finset.sum_pos' (fun s _ => mul_nonneg (hq.1 _).le (hf s))
        ⟨s, Finset.mem_univ s, mul_pos (hq.1 _) hs⟩
    have : q h * (p h ⬝ᵥ v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hq.1 h).le hp
    linarith

omit [Fintype S] [Fintype J] in
/-- The rows of the matrix `[−p, f(·, 1), …, f(·, S)]ᵀ` of the proof of Theorem 13.4.2, indexed
by `Option S` (`none` is the price row). -/
def rd_arbRow (p f : List S → J → ℝ) (h : List S) : Option S → J → ℝ
  | none => -p h
  | some s => f (s :: h)

/-- Stiemke's Lemma at one node: no one-period arbitrage portfolio at `h` iff there are positive
`q₀, q₁, …, q_S` with `q₀ p = ∑ₛ qₛ f(s :: h)`. -/
theorem rd_node_stiemke (p f : List S → J → ℝ) (h : List S) :
    (¬ ∃ v, rd_OneArb p f h v) ↔
      ∃ Q : Option S → ℝ, (∀ k, 0 < Q k) ∧ ∀ j, Q none * p h j = ∑ s, Q (some s) * f (s :: h) j
    := by
  classical
  set A : Matrix (Option S) J ℝ := Matrix.of (rd_arbRow p f h)
  have hAn : ∀ v, A.mulVec v none = -(p h ⬝ᵥ v) := fun v => by
    simp [A, rd_arbRow, Matrix.mulVec, dotProduct]
  have hAs : ∀ v s, A.mulVec v (some s) = f (s :: h) ⬝ᵥ v := fun v s => by
    simp [A, rd_arbRow, Matrix.mulVec, dotProduct]
  have hst := rd_stiemke (LinearMap.range A.mulVecLin)
  have lhs : (¬ ∃ v, rd_OneArb p f h v) ↔
      ∀ w ∈ LinearMap.range A.mulVecLin, (∀ k, 0 ≤ w k) → w = 0 := by
    constructor
    · rintro hno w ⟨v, rfl⟩ hnn
      simp only [Matrix.mulVecLin_apply] at hnn ⊢
      by_contra hne
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
      have hpos : 0 < A.mulVec v k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
      have h0 := hnn none
      rw [hAn] at h0
      refine hno ⟨v, by linarith, fun s => ?_, ?_⟩
      · have := hnn (some s)
        rwa [hAs] at this
      · cases k with
        | none =>
          rw [hAn] at hpos
          left
          linarith
        | some s =>
          rw [hAs] at hpos
          exact Or.inr ⟨s, hpos⟩
    · rintro H ⟨v, hp, hf, hs⟩
      have hnn : ∀ k, 0 ≤ A.mulVec v k := by
        intro k
        cases k with
        | none => rw [hAn]; linarith
        | some s => rw [hAs]; exact hf s
      have h0 := H (A.mulVec v) ⟨v, rfl⟩ hnn
      rcases hs with hs | ⟨s, hs⟩
      · have := congrFun h0 none
        rw [hAn] at this
        simp only [Pi.zero_apply] at this
        linarith
      · have := congrFun h0 (some s)
        rw [hAs] at this
        simp only [Pi.zero_apply] at this
        linarith
  rw [lhs, hst]
  constructor
  · rintro ⟨Q, hQ, hQL⟩
    refine ⟨Q, hQ, fun j => ?_⟩
    have := hQL (A.mulVec (Pi.single j 1)) ⟨_, rfl⟩
    rw [Fintype.sum_option, hAn] at this
    simp only [hAs, dotProduct_single, mul_one] at this
    linarith
  · rintro ⟨Q, hQ, hQp⟩
    refine ⟨Q, hQ, ?_⟩
    rintro w ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Fintype.sum_option, hAn]
    simp only [hAs]
    have e : ∑ s, Q (some s) * (f (s :: h) ⬝ᵥ v) = (fun j => Q none * p h j) ⬝ᵥ v := by
      simp only [hQp, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
    rw [e]
    simp only [dotProduct]
    rw [mul_neg, Finset.mul_sum, neg_add_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **Theorem 13.4.2** (Miao, p. 429), debt constraints. With debt limits `D̄ ≥ 0`, the pair
`(p, f)` admits no one-period arbitrage on `R(Θ_DC(p, f))` at any node iff there is a strictly
positive state price process satisfying (13.16). -/
theorem theorem_13_4_2 (p f : List S → J → ℝ) {Dbar : List S → ℝ}
    (hD : ∀ h, 0 ≤ Dbar h) :
    (∀ h, ¬ rd_OneArbOn p f (rd_Rec (rd_ThetaDC f Dbar)) h) ↔ ∃ q, rd_StatePrice p f q := by
  classical
  rw [rd_rec_DC f hD]
  constructor
  · intro H
    have hnode : ∀ h, ∃ Q : Option S → ℝ, (∀ k, 0 < Q k) ∧
        ∀ j, Q none * p h j = ∑ s, Q (some s) * f (s :: h) j := by
      intro h
      refine (rd_node_stiemke p f h).1 ?_
      rintro ⟨v, hv⟩
      refine H h ⟨rd_loc v h, fun g s => ?_, by simpa [rd_loc] using hv⟩
      by_cases hg : g = h
      · subst hg
        simpa [rd_loc] using hv.2.1 s
      · simp [rd_loc, hg]
    choose Q hQ hQp using hnode
    refine ⟨rd_qOf fun h s => Q h (some s) / Q h none,
      rd_statePrice_qOf (fun h s => div_pos (hQ h _) (hQ h _)) fun h j => ?_⟩
    have hn := (hQ h none).ne'
    have e : ∑ s, Q h (some s) / Q h none * f (s :: h) j =
        (Q h none)⁻¹ * ∑ s, Q h (some s) * f (s :: h) j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e, ← hQp h j, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · rintro ⟨q, hq⟩ h ⟨θ, -, hθ⟩
    exact rd_noOneArb_of_statePrice hq h _ hθ

/-- Miao, p. 429 (correction): Theorem 13.4.2 for borrowing constraints is false as printed. With
one security paying nothing (price `1`), `R(Θ_BC)` admits no one-period arbitrage at any node,
but no state price process satisfies (13.16). -/
theorem theorem_13_4_2_BC_counterexample :
    (∀ h, ¬ rd_OneArbOn (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 0)
        (rd_Rec (rd_ThetaBC (fun _ _ => 1) (fun _ => 0))) h) ∧
      ¬ ∃ q, rd_StatePrice (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 0) q := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [rd_rec_BC _ (fun _ => le_rfl)]
    rintro ⟨θ, hθ, hp, -, hs⟩
    have := hθ h
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul,
      zero_mul] at this hp hs
    rcases hs with hs | ⟨_, hs⟩ <;> linarith
  · rintro ⟨q, -, hq⟩
    have := hq [] ()
    simp at this

/-- **Theorem 13.4.2** (Miao, p. 429), borrowing constraints, corrected. If prices are strictly
positive, payoffs are nonnegative and at every node some security has a nonzero payoff in some
successor state, then `(p, f)` admits no one-period arbitrage on `R(Θ_BC(p, f))` at any node iff
there is a strictly positive state price process satisfying (13.16). -/
theorem theorem_13_4_2_BC (p f : List S → J → ℝ) {Bbar : List S → ℝ}
    (hB : ∀ h, 0 ≤ Bbar h) (hp : ∀ h j, 0 < p h j) (hf : ∀ h s j, 0 ≤ f (s :: h) j)
    (hnz : ∀ h, ∃ s j, f (s :: h) j ≠ 0) :
    (∀ h, ¬ rd_OneArbOn p f (rd_Rec (rd_ThetaBC p Bbar)) h) ↔ ∃ q, rd_StatePrice p f q := by
  classical
  rw [rd_rec_BC p hB]
  constructor
  · intro H
    have hnode : ∀ h, ∃ r : S → ℝ, (∀ s, 0 < r s) ∧ ∀ j, p h j = ∑ s, r s * f (s :: h) j := by
      intro h
      set F : Matrix S J ℝ := Matrix.of fun s j => f (s :: h) j
      set P : Matrix Unit J ℝ := Matrix.of fun _ j => p h j
      set L : Submodule ℝ (S → ℝ) := (LinearMap.ker P.mulVecLin).map F.mulVecLin
      have hFv : ∀ v s, (F.mulVec v) s = f (s :: h) ⬝ᵥ v := fun v s => by
        simp [F, Matrix.mulVec, dotProduct]
      have hPv : ∀ v, P.mulVec v = 0 ↔ p h ⬝ᵥ v = 0 := fun v => by
        constructor
        · intro e
          have := congrFun e ()
          simpa [P, Matrix.mulVec, dotProduct] using this
        · intro e
          funext u
          simpa [P, Matrix.mulVec, dotProduct] using e
      have hno : ∀ w ∈ L, (∀ k, 0 ≤ w k) → w = 0 := by
        rintro w ⟨v, hv, rfl⟩ hnn
        rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, hPv] at hv
        by_contra hne
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
        have hpos : 0 < (F.mulVec v) k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
        refine H h ⟨rd_loc v h, fun g => ?_, ?_⟩
        · by_cases hg : g = h
          · subst hg
            simp [rd_loc, hv]
          · simp [rd_loc, hg]
        · refine ⟨by simp [rd_loc, hv], fun s => ?_, Or.inr ⟨k, ?_⟩⟩
          · have := hnn s
            simpa [rd_loc, hFv] using this
          · simpa [rd_loc, hFv] using hpos
      obtain ⟨r, hr, hrL⟩ := (rd_stiemke L).1 hno
      set g : J → ℝ := fun j => ∑ s, r s * f (s :: h) j
      have hgv : ∀ v, p h ⬝ᵥ v = 0 → g ⬝ᵥ v = 0 := by
        intro v hv
        have := hrL (F.mulVec v) ⟨v, by
          rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, hPv]; exact hv, rfl⟩
        simp only [hFv, dotProduct, Finset.mul_sum] at this
        rw [Finset.sum_comm] at this
        simp only [g, dotProduct, Finset.sum_mul]
        rw [← this]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
      obtain ⟨s0, j0, hj0⟩ := hnz h
      have hg0 : 0 < g j0 := Finset.sum_pos' (fun s _ => mul_nonneg (hr s).le (hf h s j0))
        ⟨s0, Finset.mem_univ _, mul_pos (hr s0) (lt_of_le_of_ne (hf h s0 j0) (Ne.symm hj0))⟩
      have hgj : ∀ j, g j * p h j0 = g j0 * p h j := by
        intro j
        by_cases hj : j = j0
        · rw [hj]
        have := hgv (p h j0 • Pi.single j 1 - p h j • Pi.single j0 1) (by
          simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
          ring)
        simp only [dotProduct_sub, dotProduct_smul, dotProduct_single, mul_one,
          smul_eq_mul] at this
        linarith
      set lam := g j0 / p h j0
      have hlam : 0 < lam := div_pos hg0 (hp h j0)
      refine ⟨fun s => r s / lam, fun s => div_pos (hr s) hlam, fun j => ?_⟩
      have hj := hgj j
      have e : ∑ s, r s / lam * f (s :: h) j = g j / lam := by
        simp only [g, div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e]
      have hp0 := (hp h j0).ne'
      have hg0' := hg0.ne'
      simp only [lam]
      field_simp
      linarith
    choose r hr hrp using hnode
    exact ⟨_, rd_statePrice_qOf hr hrp⟩
  · rintro ⟨q, hq⟩ h ⟨θ, hθ, hp1, hf1, hs⟩
    have h0 : p h ⬝ᵥ θ h = 0 := le_antisymm hp1 (hθ h)
    have key := rd_statePrice_dot hq h (θ h)
    rw [h0, mul_zero] at key
    rcases hs with hs | ⟨s, hs⟩
    · linarith
    · have : 0 < ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ θ h) :=
        Finset.sum_pos' (fun s _ => mul_nonneg (hq.1 _).le (hf1 s))
          ⟨s, Finset.mem_univ s, mul_pos (hq.1 _) hs⟩
      linarith

omit [Fintype J] in
/-- Miao, p. 430: only the ratios `q⁰_{t+1}/q⁰_t` are restricted, so positive multiples of a
state price process are state price processes. -/
theorem rd_statePrice_smul {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {a : ℝ} (ha : 0 < a) : rd_StatePrice p f (fun h => a * q h) := by
  refine ⟨fun h => mul_pos ha (hq.1 h), fun h j => ?_⟩
  rw [hq.2 h j]
  simp only [mul_assoc, ← Finset.mul_sum, mul_inv]
  field_simp

omit [Fintype J] in
/-- **(13.17)** normalisation (Miao, p. 430): every state price process can be normalised to
`q⁰(s⁰) = 1`. -/
theorem eq_13_17_normalize {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q) :
    rd_StatePrice p f (fun h => (q [])⁻¹ * q h) ∧ (fun h => (q [])⁻¹ * q h) [] = 1 :=
  ⟨rd_statePrice_smul hq (inv_pos.2 (hq.1 [])), inv_mul_cancel₀ (hq.1 []).ne'⟩

/-- **(13.17)** The state price deflator `π_t(sᵗ) = q⁰_t(sᵗ) / Pr(sᵗ)`. -/
noncomputable def rd_deflator (T : RDTree S) (q : List S → ℝ) (h : List S) : ℝ := q h / T.Pr h

/-- The stochastic discount factor `M_{t+1} = π_{t+1}/π_t` (set to `1` at the root). -/
noncomputable def rd_SDF (T : RDTree S) (q : List S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => rd_deflator T q (s :: h) / rd_deflator T q h

omit [Fintype J] in
/-- **(13.18)** (Miao, p. 430). Under (13.16), `p_t = (1/π_t) E_t[π_{t+1} f_{t+1}]
= E_t[M_{t+1} f_{t+1}]`. -/
theorem eq_13_18 (T : RDTree S) {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (h : List S) (j : J) :
    p h j = (rd_deflator T q h)⁻¹ * rd_condE T (fun g => rd_deflator T q g * f g j) h 1 ∧
      p h j = rd_condE T (fun g => rd_SDF T q g * f g j) h 1 := by
  have hPr := fun g => (T.pos g).ne'
  have hqh := (hq.1 h).ne'
  rw [rd_condE_one, rd_condE_one, hq.2 h j]
  simp only [rd_condPr, rd_deflator, rd_SDF, Finset.mul_sum]
  constructor
  · refine Finset.sum_congr rfl fun s _ => ?_
    field_simp [hPr (s :: h), hPr h]
  · refine Finset.sum_congr rfl fun s _ => ?_
    field_simp [hPr (s :: h), hPr h]

/-- Miao, p. 430: "Theorem 13.4.2 does not imply that `π` or `q⁰` lies in `L¹`." With one
riskless bond of price and payoff `1` in a deterministic economy, the state price process is
constant (`q⁰ ≡ 1` after normalisation) and not summable. -/
theorem rd_statePrice_not_L1 :
    rd_StatePrice (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1) ∧
      ¬ rd_L1 (S := Unit) (fun _ => 1) := by
  refine ⟨⟨fun _ => one_pos, fun _ _ => by simp⟩, fun hL => ?_⟩
  have := rd_L1_tendsto hL
  have e : (fun t => rd_dsum (S := Unit) (fun _ => (1 : ℝ)) [] t) = fun _ => 1 := by
    funext t
    have := rd_dsum_Pr (rd_uniformTree Unit) [] t
    simpa [rd_uniformTree] using this
  rw [e] at this
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

/-- Miao, p. 430 (short sales): the no-arbitrage pricing equation (13.16) need not hold under
short-sales constraints. Two securities with the same payoff `1` and prices `1` and `2` admit no
one-period arbitrage on `R(Θ_SC) = {θ ≥ 0}`, but no state price process exists. -/
theorem rd_SC_no_statePrice :
    (∀ h, ¬ rd_OneArbOn (S := Unit) (J := Bool) (fun _ j => if j then 2 else 1) (fun _ _ => 1)
        (rd_Rec (rd_ThetaSC (fun _ _ => 0))) h) ∧
      ¬ ∃ q, rd_StatePrice (S := Unit) (J := Bool) (fun _ j => if j then 2 else 1)
        (fun _ _ => 1) q := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [rd_rec_SC (fun _ _ => le_rfl)]
    rintro ⟨θ, hθ, hp, hf, hs⟩
    have h1 := hθ h true
    have h2 := hθ h false
    simp only [dotProduct, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, one_mul] at hp hf hs
    rcases hs with hs | ⟨_, hs⟩ <;> linarith
  · rintro ⟨q, -, hq⟩
    have h1 := hq [] true
    have h2 := hq [] false
    simp only [↓reduceIte, Bool.false_eq_true] at h1 h2
    rw [← h2] at h1
    norm_num at h1

/-- Miao, p. 430 (short sales): with strictly positive prices, (13.16) holds as an inequality,
`q⁰_t p_t ≥ ∑ q⁰_{t+1} f_{t+1}`, for some strictly positive `q⁰`; and any such `q⁰` rules out
one-period arbitrage on `R(Θ_SC)` (short-sales limits `h̄ ≥ 0`). -/
theorem rd_SC_inequality (p f : List S → J → ℝ) {hbar : List S → J → ℝ}
    (hh : ∀ h j, 0 ≤ hbar h j) (hp : ∀ h j, 0 < p h j) :
    (∃ q : List S → ℝ, (∀ h, 0 < q h) ∧ ∀ h j, ∑ s, q (s :: h) * f (s :: h) j ≤ q h * p h j) ∧
      ∀ q : List S → ℝ, (∀ h, 0 < q h) →
        (∀ h j, ∑ s, q (s :: h) * f (s :: h) j ≤ q h * p h j) →
        ∀ h, ¬ rd_OneArbOn p f (rd_Rec (rd_ThetaSC hbar)) h := by
  rw [rd_rec_SC hh]
  refine ⟨?_, fun q hq hqp h => ?_⟩
  · set A : List S → ℝ := fun h => ∑ j, ∑ s, |f (s :: h) j| / p h j
    have hA : ∀ h, 0 ≤ A h := fun h => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hp h j).le
    set r : List S → S → ℝ := fun h _ => 1 / (1 + A h)
    have hr : ∀ h s, 0 < r h s := fun h _ => div_pos one_pos (by linarith [hA h])
    refine ⟨rd_qOf r, rd_qOf_pos hr, fun h j => ?_⟩
    simp only [rd_qOf, mul_assoc, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (rd_qOf_pos hr h).le
    have hpj := hp h j
    have hsum : ∑ s, |f (s :: h) j| / p h j ≤ A h :=
      Finset.single_le_sum (f := fun j => ∑ s, |f (s :: h) j| / p h j)
        (fun j _ => Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hp h j).le)
        (Finset.mem_univ j)
    have h1 : ∑ s, r h s * f (s :: h) j ≤ 1 / (1 + A h) * ∑ s, |f (s :: h) j| := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (le_abs_self _) (hr h s).le
    have e2 : ∑ s, |f (s :: h) j| = (∑ s, |f (s :: h) j| / p h j) * p h j := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    have h2 : ∑ s, |f (s :: h) j| ≤ A h * p h j := by
      rw [e2]
      exact mul_le_mul_of_nonneg_right hsum hpj.le
    have hA1 : 0 < 1 + A h := by linarith [hA h]
    calc ∑ s, r h s * f (s :: h) j ≤ 1 / (1 + A h) * ∑ s, |f (s :: h) j| := h1
      _ ≤ 1 / (1 + A h) * (A h * p h j) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ p h j := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA1]
          nlinarith [hA h]
  · rintro ⟨θ, hθ, hp1, hf1, hs⟩
    have hge : 0 ≤ p h ⬝ᵥ θ h :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hp h j).le (hθ h j)
    have h0 : p h ⬝ᵥ θ h = 0 := le_antisymm hp1 hge
    have key : ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ θ h) ≤ q h * (p h ⬝ᵥ θ h) := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun j _ => ?_
      have := mul_le_mul_of_nonneg_right (hqp h j) (hθ h j)
      rw [Finset.sum_mul] at this
      calc ∑ s, q (s :: h) * (f (s :: h) j * θ h j)
          = ∑ s, q (s :: h) * f (s :: h) j * θ h j :=
            Finset.sum_congr rfl fun s _ => by ring
        _ ≤ q h * p h j * θ h j := this
        _ = q h * (p h j * θ h j) := by ring
    rw [h0, mul_zero] at key
    rcases hs with hs | ⟨s, hs⟩
    · linarith
    · have : 0 < ∑ s, q (s :: h) * (f (s :: h) ⬝ᵥ θ h) :=
        Finset.sum_pos' (fun s _ => mul_nonneg (hq _).le (hf1 s))
          ⟨s, Finset.mem_univ s, mul_pos (hq _) hs⟩
      linarith

/-- Miao, pp. 425–426 (multi-period securities). Pricing a claim `X` paid at distance `n + 1`
from `sᵗ` with state prices equals pricing the one-period payoff given, at each successor, by the
claim's price there. This is how the two-period bond and the call option are described by
one-period payoffs. -/
theorem rd_multiperiod_price {q : List S → ℝ} (hq : ∀ h, 0 < q h) (X : List S → ℝ)
    (h : List S) (n : ℕ) :
    (q h)⁻¹ * rd_dsum (fun g => q g * X g) h (n + 1) =
      (q h)⁻¹ * ∑ s, q (s :: h) * ((q (s :: h))⁻¹ * rd_dsum (fun g => q g * X g) (s :: h) n) := by
  rw [rd_dsum_succ]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, mul_inv_cancel₀ (hq _).ne', one_mul]

/-- Miao, pp. 425–426: the two-period riskless bond (one unit at every node two periods ahead)
has the price of the one-period payoff `q_{1,t+1}`, the one-period bond price at `t + 1`. -/
theorem rd_twoPeriodBond {q : List S → ℝ} (hq : ∀ h, 0 < q h) (h : List S) :
    (q h)⁻¹ * rd_dsum q h 2 =
      (q h)⁻¹ * ∑ s, q (s :: h) * ((q (s :: h))⁻¹ * ∑ s', q (s' :: s :: h)) := by
  have := rd_multiperiod_price hq (fun _ => 1) h 1
  simp only [mul_one] at this
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rd_dsum_succ]
  simp [rd_dsum_zero]

end Miao.CompleteMarkets
