/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
