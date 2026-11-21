/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.RGCompact
import DynamicGames.RGPrisoners

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
