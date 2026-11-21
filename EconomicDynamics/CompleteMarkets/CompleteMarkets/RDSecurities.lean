/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDTree
import Mathlib.Data.Matrix.Mul

/-!
# Sequential trading: securities, budgets, portfolio constraints and arbitrage

Miao, §13.4, pp. 424–429.

`J` securities are traded at every node. `p h : J → ℝ` is the price vector at node `h` and
`f (s :: h) : J → ℝ` is the payoff, at the successor `s :: h`, of the securities bought at `h`.
A trading strategy is `θ : List S → J → ℝ`, and `θm1` is the initial portfolio `θ_{−1}`.

* `rd_Budget` is the budget constraint (13.11); `eq_13_11` gives the book's two lines
  (13.11a) and (13.11b). `rd_fz` and `rd_prev` are the payoff and the portfolio carried into a
  node (at the root, (13.11b) values `θ_{−1}` at `p₀`).
* Arrow securities: `rd_arrowPayoff` and the budget (13.12), `eq_13_12`.
* Ponzi schemes `rd_Ponzi`, arbitrage `rd_Arb`, one-period arbitrage `rd_OneArb`: a Ponzi scheme
  is an arbitrage (`rd_ponzi_arb`); no arbitrage implies no one-period arbitrage
  (`rd_noArb_noOneArb`, also on the recession sets, `rd_noArbOn_noOneArbOn`); the converse
  fails (`rd_oneArb_converse_fails`: a riskless bond rolled over forever).
* The debt (13.13), borrowing (13.14) and short-sales (13.15) constraints `rd_ThetaDC`,
  `rd_ThetaBC`, `rd_ThetaSC`, the recession set `rd_Rec`, and its three computations
  `rd_rec_DC`, `rd_rec_BC`, `rd_rec_SC` (pp. 429–430).
* **Theorem 13.4.1** (`theorem_13_4_1`, Exercise 13.3 `ex_13_3`): an agent with strictly
  increasing utility who has an optimum has no arbitrage on the recession set. The proof adds
  the arbitrage to the optimal strategy and consumes the (truncated) surplus, which keeps
  consumption bounded.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J : Type*} [Fintype S] [Fintype J]

omit [Fintype S] in
/-- The payoff vector received at a node: `f_t(sᵗ)` for `t > 0`, and `p₀(s⁰)` at the root, as in
(13.11b). -/
def rd_fz (p f : List S → J → ℝ) : List S → J → ℝ
  | [] => p []
  | s :: h => f (s :: h)

omit [Fintype S] in
/-- The portfolio carried into a node: `θ_{t−1}(sᵗ⁻)`, and `θ_{−1}` at the root. -/
def rd_prev (θ : List S → J → ℝ) (θm1 : J → ℝ) : List S → J → ℝ
  | [] => θm1
  | _ :: h => θ h

/-- The net cash flow of a strategy at a node: `f_t · θ_{t−1} − p_t · θ_t`. -/
def rd_net (p f : List S → J → ℝ) (θm1 : J → ℝ) (θ : List S → J → ℝ) (h : List S) : ℝ :=
  rd_fz p f h ⬝ᵥ rd_prev θ θm1 h - p h ⬝ᵥ θ h

/-- The sequential budget constraints (13.11). -/
def rd_Budget (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ) (c : List S → ℝ)
    (θ : List S → J → ℝ) : Prop :=
  ∀ h, c h + p h ⬝ᵥ θ h ≤ rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h

omit [Fintype S] in
/-- **(13.11)** (Miao, p. 425). The budget constraints are (13.11a) at every node `sᵗ`,
`t > 0`, and (13.11b) at the root. -/
theorem eq_13_11 (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ) (c : List S → ℝ)
    (θ : List S → J → ℝ) :
    rd_Budget p f y θm1 c θ ↔
      (∀ s h, c (s :: h) + p (s :: h) ⬝ᵥ θ (s :: h) ≤ f (s :: h) ⬝ᵥ θ h + y (s :: h)) ∧
        c [] + p [] ⬝ᵥ θ [] ≤ p [] ⬝ᵥ θm1 + y [] := by
  constructor
  · intro hB
    exact ⟨fun s h => hB (s :: h), hB []⟩
  · rintro ⟨h1, h0⟩ h
    cases h with
    | nil => exact h0
    | cons s h => exact h1 s h

omit [Fintype S] in
/-- The budget constraint says consumption is at most net cash flow plus endowment. -/
theorem rd_budget_iff_net (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (c : List S → ℝ) (θ : List S → J → ℝ) :
    rd_Budget p f y θm1 c θ ↔ ∀ h, c h ≤ rd_net p f θm1 θ h + y h := by
  refine forall_congr' fun h => ?_
  rw [rd_net]
  constructor <;> intro H <;> linarith

omit [Fintype S] [Fintype J] in
/-- The carried-in portfolio is additive. -/
theorem rd_prev_add (θ θ' : List S → J → ℝ) (a b : J → ℝ) (h : List S) :
    rd_prev (θ + θ') (a + b) h = rd_prev θ a h + rd_prev θ' b h := by
  cases h with
  | nil => rfl
  | cons s h => rfl

omit [Fintype S] [Fintype J] in
/-- The carried-in portfolio scales. -/
theorem rd_prev_smul (r : ℝ) (θ : List S → J → ℝ) (a : J → ℝ) (h : List S) :
    rd_prev (r • θ) (r • a) h = r • rd_prev θ a h := by
  cases h with
  | nil => rfl
  | cons s h => rfl

omit [Fintype S] in
/-- Net cash flows are additive in the strategy. -/
theorem rd_net_add (p f : List S → J → ℝ) (θ θ' : List S → J → ℝ) (a b : J → ℝ)
    (h : List S) : rd_net p f (a + b) (θ + θ') h = rd_net p f a θ h + rd_net p f b θ' h := by
  simp only [rd_net, rd_prev_add, dotProduct_add, Pi.add_apply]
  ring

omit [Fintype S] in
/-- **Arrow securities** (Miao, p. 425). The `S` Arrow securities bought at `h` pay one unit at
`(h, s)` for the security indexed by `s`, and zero elsewhere. -/
def rd_arrowPayoff [DecidableEq S] : List S → S → ℝ
  | [] => fun _ => 0
  | s :: _ => fun j => if j = s then 1 else 0

omit [Fintype S] in
/-- The holding of Arrow securities carried into a node: `a_{t−1}(sᵗ⁻, sₜ)`, and the initial
holding `a_{−1}(s⁰)` at the root. -/
def rd_arrowIn (a : List S → S → ℝ) (a0 : ℝ) : List S → ℝ
  | [] => a0
  | s :: h => a h s

/-- The budget constraint (13.12) with Arrow securities, prices `Q(s′ | sᵗ)` and holdings
`a_t(sᵗ, s′)`. -/
def rd_ArrowBudget (Q : List S → S → ℝ) (y : List S → ℝ) (a0 : ℝ) (c : List S → ℝ)
    (a : List S → S → ℝ) : Prop :=
  ∀ h, c h + ∑ s', Q h s' * a h s' ≤ rd_arrowIn a a0 h + y h

/-- **(13.12)** (Miao, p. 425). With the `S` Arrow securities as the traded securities
(`J = S`, payoffs `rd_arrowPayoff`, prices `Q`), the sequential budget (13.11) is (13.12), the
initial Arrow holding being the value `a_{−1}(s⁰) = Q(· | s⁰) · θ_{−1}`. -/
theorem eq_13_12 [DecidableEq S] (Q : List S → S → ℝ) (y : List S → ℝ) (θm1 : S → ℝ)
    (c : List S → ℝ) (a : List S → S → ℝ) :
    rd_Budget Q rd_arrowPayoff y θm1 c a ↔ rd_ArrowBudget Q y (Q [] ⬝ᵥ θm1) c a := by
  refine forall_congr' fun h => ?_
  cases h with
  | nil => rfl
  | cons s h =>
    simp [rd_fz, rd_prev, rd_arrowIn, rd_arrowPayoff, dotProduct]

/-- A **Ponzi scheme** (Miao, p. 426): `p₀ · Δ₀ < 0` and `p_t · Δ_t = f_t · Δ_{t−1}` for `t > 0`. -/
def rd_Ponzi (p f : List S → J → ℝ) (Δ : List S → J → ℝ) : Prop :=
  p [] ⬝ᵥ Δ [] < 0 ∧ ∀ s h, p (s :: h) ⬝ᵥ Δ (s :: h) = f (s :: h) ⬝ᵥ Δ h

/-- An **arbitrage opportunity** (Miao, p. 428): `p₀ · θ₀ ≤ 0`, `f_t · θ_{t−1} − p_t · θ_t ≥ 0`,
with at least one strict inequality (the net cash flow with `θ_{−1} = 0`). -/
def rd_Arb (p f : List S → J → ℝ) (θ : List S → J → ℝ) : Prop :=
  (∀ h, 0 ≤ rd_net p f 0 θ h) ∧ ∃ h, 0 < rd_net p f 0 θ h

/-- An arbitrage within a set of trading strategies. -/
def rd_ArbOn (p f : List S → J → ℝ) (Θ' : Set (List S → J → ℝ)) : Prop :=
  ∃ θ ∈ Θ', rd_Arb p f θ

/-- A **one-period arbitrage** portfolio at `h` (Miao, p. 428): `p_t · v ≤ 0`,
`f_{t+1}(s :: h) · v ≥ 0` for all `s`, with at least one strict inequality. -/
def rd_OneArb (p f : List S → J → ℝ) (h : List S) (v : J → ℝ) : Prop :=
  p h ⬝ᵥ v ≤ 0 ∧ (∀ s, 0 ≤ f (s :: h) ⬝ᵥ v) ∧ (p h ⬝ᵥ v < 0 ∨ ∃ s, 0 < f (s :: h) ⬝ᵥ v)

/-- A one-period arbitrage at `h` by a strategy in `Θ'`. -/
def rd_OneArbOn (p f : List S → J → ℝ) (Θ' : Set (List S → J → ℝ)) (h : List S) : Prop :=
  ∃ θ ∈ Θ', rd_OneArb p f h (θ h)

omit [Fintype S] in
/-- Miao, p. 428: "By definition, a Ponzi scheme is an arbitrage opportunity." -/
theorem rd_ponzi_arb (p f : List S → J → ℝ) (Δ : List S → J → ℝ) (hΔ : rd_Ponzi p f Δ) :
    rd_Arb p f Δ := by
  have hn : ∀ h, rd_net p f 0 Δ h = if h = [] then -(p [] ⬝ᵥ Δ []) else 0 := by
    intro h
    cases h with
    | nil => simp [rd_net, rd_fz, rd_prev]
    | cons s h =>
      simp only [rd_net, rd_fz, rd_prev, hΔ.2 s h, sub_self, reduceCtorEq, ↓reduceIte]
  refine ⟨fun h => ?_, [], ?_⟩
  · rw [hn]
    split_ifs
    · linarith [hΔ.1]
    · exact le_rfl
  · rw [hn]
    simp only [↓reduceIte]
    linarith [hΔ.1]

omit [Fintype S] [Fintype J] in
/-- The strategy that holds `v` at the node `h` only. -/
def rd_loc [DecidableEq S] (v : J → ℝ) (h : List S) : List S → J → ℝ :=
  fun g => if g = h then v else 0

omit [Fintype S] in
/-- A one-period arbitrage at `h`, held at `h` only, is an arbitrage opportunity. -/
theorem rd_arb_loc [DecidableEq S] (p f : List S → J → ℝ) (h : List S) (v : J → ℝ)
    (hv : rd_OneArb p f h v) : rd_Arb p f (rd_loc v h) := by
  obtain ⟨hp, hf, hs⟩ := hv
  have hprev : ∀ g, g ≠ h → rd_net p f 0 (rd_loc v h) g =
      rd_fz p f g ⬝ᵥ rd_prev (rd_loc v h) 0 g := by
    intro g hg
    simp [rd_net, rd_loc, hg]
  have hat : rd_net p f 0 (rd_loc v h) h = -(p h ⬝ᵥ v) := by
    cases h with
    | nil => simp [rd_net, rd_loc, rd_prev]
    | cons s g =>
      have : g ≠ s :: g := fun e => by simpa using congrArg List.length e
      simp [rd_net, rd_loc, rd_prev, this]
  have hchild : ∀ s, rd_net p f 0 (rd_loc v h) (s :: h) = f (s :: h) ⬝ᵥ v := by
    intro s
    have : s :: h ≠ h := fun e => by simpa using congrArg List.length e
    rw [hprev _ this]
    simp [rd_fz, rd_prev, rd_loc]
  refine ⟨fun g => ?_, ?_⟩
  · by_cases hg : g = h
    · rw [hg, hat]
      linarith
    · rw [hprev g hg]
      cases g with
      | nil => simp [rd_prev]
      | cons s g' =>
        by_cases hg' : g' = h
        · subst hg'
          simpa [rd_fz, rd_prev, rd_loc] using hf s
        · simp [rd_prev, rd_loc, hg']
  · rcases hs with hs | ⟨s, hs⟩
    · exact ⟨h, by rw [hat]; linarith⟩
    · exact ⟨s :: h, by rw [hchild]; exact hs⟩

omit [Fintype S] in
/-- Miao, p. 428: "If there is no arbitrage, then there is no one-period arbitrage at any
node." -/
theorem rd_noArb_noOneArb (p f : List S → J → ℝ)
    (hna : ¬ ∃ θ, rd_Arb p f θ) (h : List S) : ¬ rd_OneArbOn p f Set.univ h := by
  classical
  rintro ⟨θ, -, hθ⟩
  exact hna ⟨_, rd_arb_loc p f h _ hθ⟩

omit [Fintype S] in
/-- The same on any set of strategies that contains the localisation of its members (as the
recession sets of `Θ_DC`, `Θ_BC`, `Θ_SC` do): no arbitrage on `Θ'` implies no one-period
arbitrage on `Θ'`. -/
theorem rd_noArbOn_noOneArbOn [DecidableEq S] (p f : List S → J → ℝ)
    (Θ' : Set (List S → J → ℝ)) (hloc : ∀ θ ∈ Θ', ∀ h, rd_loc (θ h) h ∈ Θ')
    (hna : ¬ rd_ArbOn p f Θ') (h : List S) : ¬ rd_OneArbOn p f Θ' h := by
  rintro ⟨θ, hθ, harb⟩
  exact hna ⟨_, hloc θ hθ h, rd_arb_loc p f h _ harb⟩

/-- Miao, p. 428: "The converse may not be true." A riskless bond with price and payoff `1`
admits no one-period arbitrage at any node, but rolling over one unit of debt forever is an
arbitrage (a Ponzi scheme). -/
theorem rd_oneArb_converse_fails :
    (∀ h, ¬ rd_OneArbOn (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) Set.univ h) ∧
      ∃ θ, rd_Arb (S := Unit) (J := Unit) (fun _ _ => 1) (fun _ _ => 1) θ := by
  refine ⟨fun h => ?_, fun _ _ => -1, rd_ponzi_arb _ _ _ ?_⟩
  · rintro ⟨θ, -, hp, hf, hs⟩
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, one_mul] at hp hf hs
    have h1 := hf ()
    rcases hs with hs | ⟨_, hs⟩ <;> linarith
  · simp [rd_Ponzi, dotProduct]

/-- The **debt constraints** (13.13): `f_{t+1}(sᵗ⁺¹) · θ_t(sᵗ) ≥ −D̄_{t+1}(sᵗ⁺¹)`. -/
def rd_ThetaDC (f : List S → J → ℝ) (Dbar : List S → ℝ) : Set (List S → J → ℝ) :=
  {θ | ∀ h s, -Dbar (s :: h) ≤ f (s :: h) ⬝ᵥ θ h}

/-- The **borrowing constraints** (13.14): `p_t(sᵗ) · θ_t(sᵗ) ≥ −B̄_t(sᵗ)`. -/
def rd_ThetaBC (p : List S → J → ℝ) (Bbar : List S → ℝ) : Set (List S → J → ℝ) :=
  {θ | ∀ h, -Bbar h ≤ p h ⬝ᵥ θ h}

omit [Fintype S] [Fintype J] in
/-- The **short-sales constraints** (13.15): `θ_t(sᵗ) ≥ −h̄_t(sᵗ)`. -/
def rd_ThetaSC (hbar : List S → J → ℝ) : Set (List S → J → ℝ) :=
  {θ | ∀ h j, -hbar h j ≤ θ h j}

omit [Fintype S] [Fintype J] in
/-- The **recession set** `R(Θᵃ) = {θ : Θᵃ + λθ ⊂ Θᵃ, ∀ λ > 0}` (Miao, p. 428). -/
def rd_Rec (Θa : Set (List S → J → ℝ)) : Set (List S → J → ℝ) :=
  {θ | ∀ lam : ℝ, 0 < lam → ∀ θ' ∈ Θa, θ' + lam • θ ∈ Θa}

/-- If `−D ≤ λx` for all `λ > 0` then `x ≥ 0`. -/
theorem rd_nonneg_of_forall_lam {D x : ℝ} (hD : ∀ lam : ℝ, 0 < lam → -D ≤ lam * x) :
    0 ≤ x := by
  by_contra hx
  push Not at hx
  have hpos : 0 < (|D| + 1) / (-x) := div_pos (by positivity) (by linarith)
  have := hD _ hpos
  have hx0 : x ≠ 0 := hx.ne
  have e : (|D| + 1) / (-x) * x = -(|D| + 1) := by
    field_simp
  rw [e] at this
  linarith [le_abs_self D]

omit [Fintype S] in
/-- Miao, p. 429: `R(Θ_DC(p, f)) = {θ : f_{t+1} · θ_t ≥ 0}` (debt limits `D̄ ≥ 0`). -/
theorem rd_rec_DC (f : List S → J → ℝ) {Dbar : List S → ℝ} (hD : ∀ h, 0 ≤ Dbar h) :
    rd_Rec (rd_ThetaDC f Dbar) = {θ | ∀ h s, 0 ≤ f (s :: h) ⬝ᵥ θ h} := by
  ext θ
  simp only [rd_Rec, rd_ThetaDC, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  constructor
  · intro H h s
    refine rd_nonneg_of_forall_lam (D := Dbar (s :: h)) fun lam hlam => ?_
    have := H lam hlam 0 (fun h' s' => by simpa using hD (s' :: h')) h s
    simpa using this
  · intro H lam hlam θ' hθ' h s
    have := mul_nonneg hlam.le (H h s)
    linarith [hθ' h s]

omit [Fintype S] in
/-- Miao, p. 429: `R(Θ_BC(p, f)) = {θ : p_t · θ_t ≥ 0}` (borrowing limits `B̄ ≥ 0`). -/
theorem rd_rec_BC (p : List S → J → ℝ) {Bbar : List S → ℝ} (hB : ∀ h, 0 ≤ Bbar h) :
    rd_Rec (rd_ThetaBC p Bbar) = {θ | ∀ h, 0 ≤ p h ⬝ᵥ θ h} := by
  ext θ
  simp only [rd_Rec, rd_ThetaBC, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  constructor
  · intro H h
    refine rd_nonneg_of_forall_lam (D := Bbar h) fun lam hlam => ?_
    have := H lam hlam 0 (fun h' => by simpa using hB h') h
    simpa using this
  · intro H lam hlam θ' hθ' h
    have := mul_nonneg hlam.le (H h)
    linarith [hθ' h]

omit [Fintype S] [Fintype J] in
/-- Miao, p. 430: `R(Θ_SC(p, f)) = {θ : θ_t ≥ 0}` (short-sales limits `h̄ ≥ 0`). -/
theorem rd_rec_SC {hbar : List S → J → ℝ} (hh : ∀ h j, 0 ≤ hbar h j) :
    rd_Rec (rd_ThetaSC hbar) = {θ | ∀ h j, 0 ≤ θ h j} := by
  ext θ
  simp only [rd_Rec, rd_ThetaSC, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro H h j
    refine rd_nonneg_of_forall_lam (D := hbar h j) fun lam hlam => ?_
    have := H lam hlam 0 (fun h' j' => by simpa using hh h' j') h j
    simpa using this
  · intro H lam hlam θ' hθ' h j
    have := mul_nonneg hlam.le (H h j)
    linarith [hθ' h j]

omit [Fintype S] in
/-- The recession set of the debt constraints contains the localisations of its members. -/
theorem rd_loc_mem_recDC [DecidableEq S] (f : List S → J → ℝ) {θ : List S → J → ℝ}
    (hθ : ∀ h s, 0 ≤ f (s :: h) ⬝ᵥ θ h) (h : List S) :
    ∀ g s, 0 ≤ f (s :: g) ⬝ᵥ rd_loc (θ h) h g := by
  intro g s
  by_cases hg : g = h
  · subst hg
    simpa [rd_loc] using hθ g s
  · simp [rd_loc, hg]

omit [Fintype S] in
/-- The recession set of the borrowing constraints contains the localisations of its
members. -/
theorem rd_loc_mem_recBC [DecidableEq S] (p : List S → J → ℝ) {θ : List S → J → ℝ}
    (hθ : ∀ h, 0 ≤ p h ⬝ᵥ θ h) (h : List S) : ∀ g, 0 ≤ p g ⬝ᵥ rd_loc (θ h) h g := by
  intro g
  by_cases hg : g = h
  · subst hg
    simpa [rd_loc] using hθ g
  · simp [rd_loc, hg]

/-- Agent `i`'s sequential problem: bounded nonnegative consumption, the budget (13.11), and a
strategy in the admissible set `Θa`. -/
def rd_SeqFeas (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (Θa : Set (List S → J → ℝ)) (c : List S → ℝ) (θ : List S → J → ℝ) : Prop :=
  rd_LinfPos c ∧ rd_Budget p f y θm1 c θ ∧ θ ∈ Θa

omit [Fintype S] [Fintype J] in
/-- `(c, θ)` solves the problem of maximising `U` over the plans satisfying `Feas`. -/
def rd_Solves {X : Type*} (U : (List S → ℝ) → ℝ) (Feas : (List S → ℝ) → X → Prop)
    (c : List S → ℝ) (θ : X) : Prop :=
  Feas c θ ∧ ∀ c' θ', Feas c' θ' → U c' ≤ U c

omit [Fintype S] in
/-- **Theorem 13.4.1** (Miao, p. 429). If `U` is strictly increasing and agent `i`'s problem of
maximising `U` subject to (13.11) and `θ ∈ Θᵃ(p, f)` has a solution, then there is no arbitrage
opportunity on the recession set `R(Θᵃ(p, f))`. -/
theorem theorem_13_4_1 (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (Θa : Set (List S → J → ℝ)) {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U)
    {c : List S → ℝ} {θ : List S → J → ℝ} (hsol : rd_Solves U (rd_SeqFeas p f y θm1 Θa) c θ) :
    ¬ rd_ArbOn p f (rd_Rec Θa) := by
  rintro ⟨θ', hrec, hnn, h0, hpos⟩
  obtain ⟨⟨⟨M, hM⟩, hc0⟩, hB, hΘ⟩ := hsol.1
  set c'' : List S → ℝ := fun h => c h + min (rd_net p f 0 θ' h) 1 with hc''
  have hmin0 : ∀ h, 0 ≤ min (rd_net p f 0 θ' h) 1 := fun h => le_min (hnn h) zero_le_one
  have hfeas : rd_SeqFeas p f y θm1 Θa c'' (θ + θ') := by
    refine ⟨⟨⟨M + 1, fun h => ?_⟩, fun h => add_nonneg (hc0 h) (hmin0 h)⟩, ?_, ?_⟩
    · rw [hc'', abs_le]
      have h1 := min_le_right (rd_net p f 0 θ' h) 1
      have := abs_le.1 (hM h)
      constructor <;> linarith [hmin0 h]
    · rw [rd_budget_iff_net]
      intro h
      have hn := rd_net_add p f θ θ' θm1 0 h
      rw [add_zero] at hn
      rw [hn]
      have := (rd_budget_iff_net p f y θm1 c θ).1 hB h
      have := min_le_left (rd_net p f 0 θ' h) 1
      simp only [hc'']
      linarith
    · simpa using hrec 1 one_pos θ hΘ
  have hlt : U c < U c'' := by
    refine hU c c'' hsol.1.1 hfeas.1 (fun h => le_add_of_nonneg_right (hmin0 h)) ?_
    intro he
    have := congrFun he h0
    simp only [hc'', left_eq_add] at this
    have : 0 < min (rd_net p f 0 θ' h0) 1 := lt_min hpos one_pos
    linarith
  exact absurd (hsol.2 c'' (θ + θ') hfeas) (not_le.2 hlt)

omit [Fintype S] in
/-- **Exercise 13.3** (Miao, p. 452): prove Theorem 13.4.1. -/
theorem ex_13_3 (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ)
    (Θa : Set (List S → J → ℝ)) {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U)
    {c : List S → ℝ} {θ : List S → J → ℝ} (hsol : rd_Solves U (rd_SeqFeas p f y θm1 Θa) c θ) :
    ¬ rd_ArbOn p f (rd_Rec Θa) :=
  theorem_13_4_1 p f y θm1 Θa hU hsol

end Miao.CompleteMarkets
