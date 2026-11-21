/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.DGNoisyPD

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
