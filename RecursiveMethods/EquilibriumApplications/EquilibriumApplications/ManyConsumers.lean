/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SequenceSupport
import EquilibriumApplications.WelfareSecond

/-!
# An economy with many consumers: preferences, technology and production sets

SLP §16.7, pp. 495–497. Goods are `ℝˡ` (`Fin l → ℝ`), capital `ℝᵖ` (`Fin p → ℝ`). The commodity
space is `S = BddSeq (Fin l → ℝ)` (bounded sequences with the sup norm; on `ℝˡ` Lean's norm is the
max norm, equivalent to the book's Euclidean norm) and the consumption set is `C = S₊ˡ`
(`mcCons`).

* **Preferences** (pp. 495–496, recalling §5.11): `ManyConsumersAggregator W β` is (W1)–(W5)
  (`IsAggregator` of Exercise 15.10 gives continuity, `W ≥ 0`, (W1)–(W3); `mono` is (W4),
  `concave` is (W5)). Consumer `i`'s utility is a bounded continuous nonnegative fixed point
  `uᵢ(c) = Wᵢ(c₀, uᵢ(₁c))` (`IsAggregatorFixedPoint`); its existence and uniqueness is
  Exercise 5.11d (Chapter 5 project), taken as given here. From the fixed-point equation:
  `mc_utility_concave` ((W5) ⇒ concave), `mc_utility_mono` ((W4) ⇒ increasing),
  `mc_utility_zero` (`u(0) = 0`), `mc_utility_strict`.
* **Technology** (p. 496): `ManyConsumersTech Φ` is (T1)–(T7), with (T1) SLP's continuity
  (nonempty values, upper and lower hemicontinuity in sequential form); `mcM Φ` is the set `M`.
* **The production set** (p. 496): `mcProdSet Φ k̂` is `Y(k̂)` (bounded capital paths, as in the
  book); `mcProdSetUnb Φ k̂` is the corrected `Y′(k̂)` (capital paths need not be bounded).
* **Exercise 16.7a** (p. 497): `ex_16_7a_convex` (convex), `ex_16_7a_trunc` (Assumption 15.6),
  `ex_16_7a_interior` (an interior point when `k̂ ∈ int M`); also `zero_mem_mcProdSet`,
  `mcProdSet_disposal` (free disposal) and `mcProdSet_combo` (`aY(κ) + bY(κ′) ⊆ Y(aκ + bκ′)`).
* **The welfare theorems** (p. 497): `mc_assumptions` (Assumptions 15.1–15.7, one firm),
  `mc_localNonsatiation`, `mc_welfare` (Theorems 15.3, 15.4 and 15.6 apply).

**Corrections.**
* p. 496: `Φ` maps `ℝᵖ₊` into `ℝˡ₊ × ℝᵖ₊` (field `nonneg`; (T1)–(T7) are imposed for `κ ≥ 0`)
  and `M ⊆ ℝᵖ₊`; the book writes `Φ : ℝᵖ → ℝˡ × ℝᵖ`.
* Exercise 16.7a: "`Y(k̂)` is closed" is false (`ex_16_7a_counterexample` in
  `ManyConsumersExample`); it holds for `Y′(k̂)` (`ex_16_7a_closed` in `ManyConsumersClosed`).
* p. 497: (W1)–(W5) do not give the nonsatiation hypotheses of Theorems 15.3, 15.4 and 15.6:
  `W ≡ 0` satisfies (W1)–(W5) and its fixed point `u ≡ 0` is not locally nonsatiated
  (`mc_nonsatiation_counterexample`). With nonsatiation in current consumption,
  `W(x + ε𝟙, z) > W(x, z)` for `ε > 0`, the theorems apply (`mc_welfare`). That Pareto optima
  *are* competitive equilibrium allocations further needs the cheaper-point condition of the Remark
  after Theorem 15.4 (`remark_cheaper_point`); `mc_competitiveEq_of_pos` (in `ManyConsumersBerge`)
  gives it when every consumer's bundle has positive value.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ}

/-! ### Preferences (pp. 495–496) -/

/-- The consumption set `C = S₊ˡ` of §16.7: bounded sequences in `ℝˡ₊`. -/
abbrev mcCons (l : ℕ) : Set (BddSeq (Fin l → ℝ)) := seqSet (Ici (0 : Fin l → ℝ))

/-- An aggregator on `ℝˡ₊ × ℝ₊` with properties (W1)–(W5) of §5.11 (pp. 114–116): `agg` is
continuity, `W ≥ 0`, (W1) `W(0, 0) = 0`, (W2) boundedness of `W(·, z)` and (W3) the modulus `β`
in `z` (`IsAggregator`, Exercise 15.10); `mono` is (W4) and `concave` is (W5). -/
structure ManyConsumersAggregator (W : (Fin l → ℝ) → ℝ → ℝ) (β : ℝ) : Prop where
  agg : IsAggregator (Ici (0 : Fin l → ℝ)) W β
  mono : ∀ x x' : Fin l → ℝ, ∀ z z' : ℝ, 0 ≤ x → x ≤ x' → 0 ≤ z → z ≤ z' → W x z ≤ W x' z'
  concave : ConcaveOn ℝ (Ici (0 : Fin l → ℝ) ×ˢ Ici (0 : ℝ)) fun q => W q.1 q.2

/-- The constant sequence `(a, a, a, …)`. -/
noncomputable def mcConst {E : Type*} [NormedAddCommGroup E] (a : E) : BddSeq E :=
  BddSeq.mk (fun _ => a) ‖a‖ fun _ => le_rfl

/-- Coordinates of the constant sequence. -/
@[simp] theorem mcConst_apply {E : Type*} [NormedAddCommGroup E] (a : E) (t : ℕ) :
    mcConst a t = a := rfl

/-- The norm of the constant sequence is at most `‖a‖`. -/
theorem norm_mcConst_le {E : Type*} [NormedAddCommGroup E] (a : E) : ‖mcConst a‖ ≤ ‖a‖ :=
  lp.norm_le_of_forall_le (norm_nonneg a) fun _ => le_rfl

/-- Coordinates of a difference of bounded sequences. -/
theorem mc_sub_apply {E : Type*} [NormedAddCommGroup E] (x y : BddSeq E) (t : ℕ) :
    (x - y) t = x t - y t := by
  rw [lp.coeFn_sub]; rfl

/-- Coordinates of a sum of bounded sequences. -/
theorem mc_add_apply {E : Type*} [NormedAddCommGroup E] (x y : BddSeq E) (t : ℕ) :
    (x + y) t = x t + y t := by
  rw [lp.coeFn_add]; rfl

/-- **Concavity of `uᵢ`** (Exercise 5.11d under (W5)): the fixed point of `T_W` satisfies
`θu(x) + (1 − θ)u(x′) ≤ u(θx + (1 − θ)x′)` on `C`. -/
theorem mc_utility_concave {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ} (hW : ManyConsumersAggregator W β)
    {v : BddSeq (Fin l → ℝ) → ℝ} (hv : IsAggregatorFixedPoint (Ici 0) W v) :
    ∀ x ∈ mcCons l, ∀ x' ∈ mcCons l, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ * v x + (1 - θ) * v x' ≤ v (θ • x + (1 - θ) • x') := by
  intro x hx x' hx' θ h0 h1
  obtain ⟨B, hB⟩ := hv.bounded
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x hx)
  have hlim : Tendsto (fun k : ℕ => θ * v x + (1 - θ) * v x' - 4 * B * β ^ k) atTop
      (𝓝 (θ * v x + (1 - θ) * v x')) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hW.agg.beta_pos.le
      hW.agg.beta_lt_one).const_mul (4 * B)).const_sub (θ * v x + (1 - θ) * v x')
  exact le_of_tendsto' hlim fun k =>
    aggregator_concave_approx (convex_Ici 0) hW.agg hW.concave hv hB0 hB k x hx x' hx' θ h0 h1

/-- The monotonicity inequality for `u_W`, up to `2Bβᵏ`, by induction on `k`. -/
theorem mc_utility_mono_approx {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ}
    (hW : ManyConsumersAggregator W β) {v : BddSeq (Fin l → ℝ) → ℝ}
    (hv : IsAggregatorFixedPoint (Ici 0) W v) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ mcCons l, |v x| ≤ B) (k : ℕ) :
    ∀ x ∈ mcCons l, ∀ x' ∈ mcCons l, (∀ t, x t ≤ x' t) → v x ≤ v x' + 2 * B * β ^ k := by
  have hβ0 := hW.agg.beta_pos.le
  induction k with
  | zero =>
    intro x hx x' hx' _
    have e1 := abs_le.1 (hB x hx)
    have e2 := abs_le.1 (hB x' hx')
    rw [pow_zero, mul_one]
    linarith
  | succ k ih =>
    intro x hx x' hx' hle
    have hsx := seqShift_mem_seqSet hx
    have hsx' := seqShift_mem_seqSet hx'
    have ih' := ih _ hsx _ hsx' fun t => by rw [seqShift_apply, seqShift_apply]; exact hle (t + 1)
    rw [hv.fixed x hx, hv.fixed x' hx']
    set z := v (seqShift x)
    set z' := v (seqShift x')
    have hz0 : 0 ≤ z := hv.nonneg _ hsx
    have hz0' : 0 ≤ z' := hv.nonneg _ hsx'
    have h1 : W (x 0) z ≤ W (x' 0) z := hW.mono _ _ _ _ (hx 0) (hle 0) hz0 le_rfl
    have hpos : 0 ≤ β * (2 * B * β ^ k) := by positivity
    have h2 : W (x' 0) z ≤ W (x' 0) z' + β * (2 * B * β ^ k) := by
      rcases le_total z z' with h | h
      · have := hW.mono _ _ _ _ (hx' 0) le_rfl hz0 h
        linarith
      · have hl := (abs_le.1 (hW.agg.lipschitz (x' 0) (hx' 0) z hz0 z' hz0')).2
        rw [abs_of_nonneg (sub_nonneg.2 h)] at hl
        have h3 := mul_le_mul_of_nonneg_left (show z - z' ≤ 2 * B * β ^ k by linarith) hβ0
        linarith
    rw [pow_succ]
    nlinarith

/-- **Monotonicity of `uᵢ`** (Exercise 5.11d under (W4)): `x ≤ x′` in `C` implies
`u(x) ≤ u(x′)`. -/
theorem mc_utility_mono {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ} (hW : ManyConsumersAggregator W β)
    {v : BddSeq (Fin l → ℝ) → ℝ} (hv : IsAggregatorFixedPoint (Ici 0) W v) {x x' : BddSeq _}
    (hx : x ∈ mcCons l) (hx' : x' ∈ mcCons l) (hle : ∀ t, x t ≤ x' t) : v x ≤ v x' := by
  obtain ⟨B, hB⟩ := hv.bounded
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x hx)
  have hlim : Tendsto (fun k : ℕ => v x' + 2 * B * β ^ k) atTop (𝓝 (v x')) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hW.agg.beta_pos.le
      hW.agg.beta_lt_one).const_mul (2 * B)).const_add (v x')
  exact ge_of_tendsto' hlim fun k => mc_utility_mono_approx hW hv hB0 hB k x hx x' hx' hle

/-- `u_W(0) = 0` under (W1) and (W3): `u(0) = W(0, u(0))` and `|W(0, z) − W(0, 0)| ≤ β|z|`. -/
theorem mc_utility_zero {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator (Ici (0 : Fin l → ℝ)) W β) {v : BddSeq (Fin l → ℝ) → ℝ}
    (hv : IsAggregatorFixedPoint (Ici 0) W v) : v 0 = 0 := by
  have h0 : (0 : BddSeq (Fin l → ℝ)) ∈ mcCons l := fun t => by
    change (0 : Fin l → ℝ) ≤ (0 : BddSeq (Fin l → ℝ)) t
    rw [lp.coeFn_zero]; rfl
  have hs : seqShift (0 : BddSeq (Fin l → ℝ)) = 0 := map_zero _
  have hfix := hv.fixed 0 h0
  rw [hs, show (0 : BddSeq (Fin l → ℝ)) 0 = 0 by rw [lp.coeFn_zero]; rfl] at hfix
  have hl := hW.lipschitz 0 self_mem_Ici (v 0) (hv.nonneg 0 h0) 0
    le_rfl
  rw [hW.zero, sub_zero, sub_zero, ← hfix] at hl
  have hv0 := hv.nonneg 0 h0
  rw [abs_of_nonneg hv0] at hl
  nlinarith [hW.beta_lt_one]

/-- **Strict monotonicity** along `x ↦ x + ε𝟙`: if `W(x + ε𝟙, z) > W(x, z)` for `ε > 0` then
`u(x + ε𝟙) > u(x)` on `C`. -/
theorem mc_utility_strict {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ} (hW : ManyConsumersAggregator W β)
    (hstrict : ∀ x : Fin l → ℝ, ∀ z ε : ℝ, 0 ≤ x → 0 ≤ z → 0 < ε → W x z < W (x + fun _ => ε) z)
    {v : BddSeq (Fin l → ℝ) → ℝ} (hv : IsAggregatorFixedPoint (Ici 0) W v) {x : BddSeq _}
    (hx : x ∈ mcCons l) {ε : ℝ} (hε : 0 < ε) : v x < v (x + mcConst fun _ => ε) := by
  have hxe : x + mcConst (fun _ => ε) ∈ mcCons l := fun t => by
    change (0 : Fin l → ℝ) ≤ (x + mcConst fun _ => ε : BddSeq (Fin l → ℝ)) t
    rw [mc_add_apply, mcConst_apply]
    exact add_nonneg (hx t) fun _ => hε.le
  have hsx := seqShift_mem_seqSet hx
  have hsxe := seqShift_mem_seqSet hxe
  rw [hv.fixed x hx, hv.fixed _ hxe, mc_add_apply, mcConst_apply]
  have hmono : v (seqShift x) ≤ v (seqShift (x + mcConst fun _ => ε)) :=
    mc_utility_mono hW hv hsx hsxe fun t => by
      rw [seqShift_apply, seqShift_apply, mc_add_apply, mcConst_apply]
      exact le_add_of_nonneg_right fun _ => hε.le
  calc W (x 0) (v (seqShift x)) < W (x 0 + fun _ => ε) (v (seqShift x)) :=
        hstrict _ _ _ (hx 0) (hv.nonneg _ hsx) hε
    _ ≤ W (x 0 + fun _ => ε) (v (seqShift (x + mcConst fun _ => ε))) :=
        hW.mono _ _ _ _ (add_nonneg (hx 0) fun _ => hε.le) le_rfl (hv.nonneg _ hsx) hmono

/-! ### Technology (p. 496) -/

/-- The set `M = {κ ∈ ℝᵖ₊ : (0, κ) ∈ Φ(κ)}` of (T6). -/
def mcM (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) : Set (Fin p → ℝ) :=
  {κ | 0 ≤ κ ∧ ((0 : Fin l → ℝ), κ) ∈ Φ κ}

/-- The technology `Φ : ℝᵖ₊ → ℝˡ₊ × ℝᵖ₊` of §16.7 with (T1)–(T7) (p. 496). `nonneg` records the
corrected codomain `ℝˡ₊ × ℝᵖ₊` (the book writes `ℝᵖ → ℝˡ × ℝᵖ`). (T1), continuity, is SLP's
(§3.1): `nonempty` values, `uhc` (every `qₙ ∈ Φ(κₙ)`, `κₙ → κ`, has a subsequence converging into
`Φ(κ)`) and `lhc` (every `q ∈ Φ(κ)` is a limit of `qₙ ∈ Φ(κₙ)`, `n` large); `compact` and
`convex` are (T2); `disposal` is (T3); `mono` is (T4); `graph_convex` is (T5); `int_nonempty`
is (T6);
`interior_pos` is (T7). -/
structure ManyConsumersTech (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) : Prop where
  nonneg : ∀ κ, 0 ≤ κ → ∀ q ∈ Φ κ, 0 ≤ q.1 ∧ 0 ≤ q.2
  nonempty : ∀ κ, 0 ≤ κ → (Φ κ).Nonempty
  uhc : ∀ κs : ℕ → Fin p → ℝ, ∀ κ, (∀ n, 0 ≤ κs n) → Tendsto κs atTop (𝓝 κ) →
    ∀ qs : ℕ → (Fin l → ℝ) × (Fin p → ℝ), (∀ n, qs n ∈ Φ (κs n)) →
      ∃ q ∈ Φ κ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (qs ∘ φ) atTop (𝓝 q)
  lhc : ∀ κs : ℕ → Fin p → ℝ, ∀ κ, (∀ n, 0 ≤ κs n) → Tendsto κs atTop (𝓝 κ) → ∀ q ∈ Φ κ,
    ∃ qs : ℕ → (Fin l → ℝ) × (Fin p → ℝ), (∀ᶠ n in atTop, qs n ∈ Φ (κs n)) ∧
      Tendsto qs atTop (𝓝 q)
  compact : ∀ κ, 0 ≤ κ → IsCompact (Φ κ)
  convex : ∀ κ, 0 ≤ κ → Convex ℝ (Φ κ)
  disposal : ∀ κ, 0 ≤ κ → ∀ γ y, (γ, y) ∈ Φ κ → ∀ γ' y', 0 ≤ γ' → γ' ≤ γ → 0 ≤ y' → y' ≤ y →
    (γ', y') ∈ Φ κ
  mono : ∀ κ κ', 0 ≤ κ' → κ' ≤ κ → Φ κ' ⊆ Φ κ
  graph_convex : ∀ κ κ', 0 ≤ κ → 0 ≤ κ' → ∀ q ∈ Φ κ, ∀ q' ∈ Φ κ', ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    θ • q + (1 - θ) • q' ∈ Φ (θ • κ + (1 - θ) • κ')
  int_nonempty : (interior (mcM Φ)).Nonempty
  interior_pos : ∀ κ ∈ interior (mcM Φ), ∃ γ : Fin l → ℝ, (∀ m, 0 < γ m) ∧ (γ, κ) ∈ Φ κ

variable {Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))}

/-- `(0, 0) ∈ Φ(κ)` for every `κ ≥ 0` (nonempty values and (T3)). -/
theorem ManyConsumersTech.zero_mem (hΦ : ManyConsumersTech Φ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) :
    ((0 : Fin l → ℝ), (0 : Fin p → ℝ)) ∈ Φ κ := by
  obtain ⟨q, hq⟩ := hΦ.nonempty κ hκ
  have h := hΦ.nonneg κ hκ q hq
  exact hΦ.disposal κ hκ q.1 q.2 hq 0 0 le_rfl h.1 le_rfl h.2

/-! ### The production set `Y(k̂)` (p. 496) -/

/-- The production set `Y(k̂) = {c ∈ S₊ˡ : ∃ k ∈ S₊ᵖ, k₀ = k̂, (c_t, k_{t+1}) ∈ Φ(k_t) ∀t}`
(p. 496): consumption sequences feasible from `k̂` along a *bounded* capital path. -/
def mcProdSet (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) (kh : Fin p → ℝ) :
    Set (BddSeq (Fin l → ℝ)) :=
  {c | (∀ t, 0 ≤ c t) ∧ ∃ k : BddSeq (Fin p → ℝ), (∀ t, 0 ≤ k t) ∧ k 0 = kh ∧
    ∀ t, (c t, k (t + 1)) ∈ Φ (k t)}

/-- The corrected production set `Y′(k̂)`: as `Y(k̂)`, but the capital path `k ∈ (ℝᵖ₊)^∞` may be
unbounded (fix (i) of the NOTE to Exercise 16.7a). -/
def mcProdSetUnb (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) (kh : Fin p → ℝ) :
    Set (BddSeq (Fin l → ℝ)) :=
  {c | (∀ t, 0 ≤ c t) ∧ ∃ k : ℕ → Fin p → ℝ, (∀ t, 0 ≤ k t) ∧ k 0 = kh ∧
    ∀ t, (c t, k (t + 1)) ∈ Φ (k t)}

/-- `Y(k̂) ⊆ Y′(k̂)`. -/
theorem mcProdSet_subset_unb (kh : Fin p → ℝ) : mcProdSet Φ kh ⊆ mcProdSetUnb Φ kh :=
  fun _ ⟨hc, k, hk0, hkk, hk⟩ => ⟨hc, k, hk0, hkk, hk⟩

/-- `Y(k̂) ⊆ C`. -/
theorem mcProdSet_subset_cons (kh : Fin p → ℝ) : mcProdSet Φ kh ⊆ mcCons l :=
  fun _ hc t => hc.1 t

/-- `0 ∈ Y(k̂)` for `k̂ ≥ 0` (capital path `(k̂, 0, 0, …)`). -/
theorem zero_mem_mcProdSet (hΦ : ManyConsumersTech Φ) {kh : Fin p → ℝ} (hkh : 0 ≤ kh) :
    (0 : BddSeq (Fin l → ℝ)) ∈ mcProdSet Φ kh := by
  refine ⟨fun t => by rw [lp.coeFn_zero]; rfl,
    BddSeq.mk (fun t => if t = 0 then kh else 0) ‖kh‖ fun t => by split_ifs <;> simp,
    fun t => ?_, by simp, fun t => ?_⟩
  · simp only [BddSeq.mk_apply]
    split_ifs
    exacts [hkh, le_rfl]
  · simp only [BddSeq.mk_apply, add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
    rw [lp.coeFn_zero]
    split_ifs
    exacts [hΦ.zero_mem hkh, hΦ.zero_mem le_rfl]

/-- **Free disposal** in `Y(k̂)` (from (T3)): `0 ≤ c′ ≤ c ∈ Y(k̂)` implies `c′ ∈ Y(k̂)`. -/
theorem mcProdSet_disposal (hΦ : ManyConsumersTech Φ) {kh : Fin p → ℝ} {c c' : BddSeq _}
    (hc : c ∈ mcProdSet Φ kh) (h0 : ∀ t, 0 ≤ c' t) (hle : ∀ t, c' t ≤ c t) :
    c' ∈ mcProdSet Φ kh := by
  obtain ⟨-, k, hk0, hkk, hk⟩ := hc
  exact ⟨h0, k, hk0, hkk, fun t => hΦ.disposal _ (hk0 t) _ _ (hk t) _ _ (h0 t) (hle t)
    (hΦ.nonneg _ (hk0 t) _ (hk t)).2 le_rfl⟩

/-- **Exercise 16.7a**, convexity: `Y(k̂)` is convex (from (T5)). -/
theorem ex_16_7a_convex (hΦ : ManyConsumersTech Φ) (kh : Fin p → ℝ) :
    Convex ℝ (mcProdSet Φ kh) := by
  rintro c ⟨hc0, k, hk0, hkk, hk⟩ c' ⟨hc0', k', hk0', hkk', hk'⟩ a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  refine ⟨fun t => ?_, a • k + (1 - a) • k', fun t => ?_, ?_, fun t => ?_⟩
  · rw [seq_coord_combo]; exact add_nonneg (smul_nonneg ha (hc0 t)) (smul_nonneg hb (hc0' t))
  · rw [seq_coord_combo]; exact add_nonneg (smul_nonneg ha (hk0 t)) (smul_nonneg hb (hk0' t))
  · rw [seq_coord_combo, hkk, hkk', Convex.combo_self hab]
  · rw [seq_coord_combo, seq_coord_combo, seq_coord_combo]
    have := hΦ.graph_convex (k t) (k' t) (hk0 t) (hk0' t) _ (hk t) _ (hk' t) a ha (by linarith)
    simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

/-- Combinations of plans feasible from `κ` and from `κ′` are feasible from the combination of
the initial capitals (T5): `aY(κ) + bY(κ′) ⊆ Y(aκ + bκ′)`. -/
theorem mcProdSet_combo (hΦ : ManyConsumersTech Φ) {κ κ' : Fin p → ℝ} {c c' : BddSeq _}
    (hc : c ∈ mcProdSet Φ κ) (hc' : c' ∈ mcProdSet Φ κ') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • c + b • c' ∈ mcProdSet Φ (a • κ + b • κ') := by
  obtain ⟨hc0, k, hk0, hkk, hk⟩ := hc
  obtain ⟨hc0', k', hk0', hkk', hk'⟩ := hc'
  obtain rfl : b = 1 - a := by linarith
  refine ⟨fun t => ?_, a • k + (1 - a) • k', fun t => ?_, ?_, fun t => ?_⟩
  · rw [seq_coord_combo]; exact add_nonneg (smul_nonneg ha (hc0 t)) (smul_nonneg hb (hc0' t))
  · rw [seq_coord_combo]; exact add_nonneg (smul_nonneg ha (hk0 t)) (smul_nonneg hb (hk0' t))
  · rw [seq_coord_combo, hkk, hkk']
  · rw [seq_coord_combo, seq_coord_combo, seq_coord_combo]
    have := hΦ.graph_convex (k t) (k' t) (hk0 t) (hk0' t) _ (hk t) _ (hk' t) a ha (by linarith)
    simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

/-- **Exercise 16.7a**, Assumption 15.6: every truncation `cᵀ` of `c ∈ Y(k̂)` lies in `Y(k̂)`
(same capital path; `(0, k_{t+1}) ∈ Φ(k_t)` by (T3)). -/
theorem ex_16_7a_trunc (hΦ : ManyConsumersTech Φ) (kh : Fin p → ℝ) :
    SeqTruncClosed (mcProdSet Φ kh) := by
  intro c hc
  exact Eventually.of_forall fun T => mcProdSet_disposal hΦ hc
    (fun t => by rw [seqTrunc_apply]; split_ifs; exacts [hc.1 t, le_rfl])
    fun t => by rw [seqTrunc_apply]; split_ifs; exacts [le_rfl, hc.1 t]

/-- **Exercise 16.7a**, interior point: for `k̂ ∈ int M`, (T7) gives `γ ≫ 0` with
`(γ, k̂) ∈ Φ(k̂)`, and the constant plan `c_t = γ/2` (capital `k_t = k̂`) is interior to `Y(k̂)`. -/
theorem ex_16_7a_interior (hΦ : ManyConsumersTech Φ) {kh : Fin p → ℝ}
    (hk : kh ∈ interior (mcM Φ)) : (interior (mcProdSet Φ kh)).Nonempty := by
  obtain ⟨γ, hγ, hγk⟩ := hΦ.interior_pos kh hk
  have hkM : kh ∈ mcM Φ := interior_subset hk
  set V : Set (Fin l → ℝ) := Set.pi univ fun m => Ioo 0 (γ m) with hVdef
  have hV : IsOpen V := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hγV : (1 / 2 : ℝ) • γ ∈ V := mem_univ_pi.2 fun m => by
    simp only [Pi.smul_apply, smul_eq_mul, mem_Ioo]
    constructor <;> linarith [hγ m]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hV _ hγV
  refine ⟨mcConst ((1 / 2 : ℝ) • γ), mem_interior_iff_mem_nhds.2
    (Metric.mem_nhds_iff.2 ⟨r, hr, fun c' hc' => ?_⟩)⟩
  have hct : ∀ t, c' t ∈ V := fun t => hball (by
    rw [Metric.mem_ball, dist_eq_norm] at hc' ⊢
    calc ‖c' t - (1 / 2 : ℝ) • γ‖ = ‖(c' - mcConst ((1 / 2 : ℝ) • γ)) t‖ := by
          rw [mc_sub_apply, mcConst_apply]
      _ ≤ ‖c' - mcConst ((1 / 2 : ℝ) • γ)‖ := norm_seq_coord_le _ _
      _ < r := hc')
  have hct' : ∀ t m, 0 < c' t m ∧ c' t m < γ m := fun t m => mem_univ_pi.1 (hct t) m
  refine ⟨fun t m => (hct' t m).1.le, mcConst kh, fun _ => hkM.1, rfl, fun t => ?_⟩
  exact hΦ.disposal kh hkM.1 γ kh hγk (c' t) kh (fun m => (hct' t m).1.le)
    (fun m => (hct' t m).2.le) hkM.1 le_rfl

/-! ### Assumptions 15.1–15.7 and the welfare theorems (p. 497) -/

/-- The aggregate technology of a single firm is its production set. -/
theorem mc_aggTech_unit {S : Type*} [NormedAddCommGroup S] (A : Set S) :
    aggTech (fun _ : Unit => A) = A := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- **The welfare-theorem hypotheses** (p. 497). With aggregators satisfying (W1)–(W5) and
`(T1)–(T7)`, `k̂ ∈ int M`, the economy `(C, u₁, …, u_I, Y(k̂))` (one firm) satisfies Assumptions
15.1–15.7. -/
theorem mc_assumptions {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {kh : Fin p → ℝ} (hk : kh ∈ interior (mcM Φ)) :
    Assumption15_1 (fun _ : ι => mcCons l) ∧ Assumption15_2 (fun _ : ι => mcCons l) u ∧
    Assumption15_3 (fun _ : ι => mcCons l) u ∧ Assumption15_4 (fun _ : Unit => mcProdSet Φ kh) ∧
    Assumption15_5 (BddSeq (Fin l → ℝ)) (fun _ : Unit => mcProdSet Φ kh) ∧
    Assumption15_6 (fun _ : ι => mcCons l) (fun _ : Unit => mcProdSet Φ kh) ∧
    Assumption15_7 (fun _ : ι => mcCons l) u := by
  have h10 := fun i => ex_15_10c (convex_Ici 0) le_rfl (hW i).agg (hW i).concave (hu i)
  refine ⟨fun _ => convex_seqSet (convex_Ici 0), fun i => (h10 i).1, fun i => (h10 i).2.1, ?_,
    ?_, ⟨fun _ => (ex_15_10a (convex_Ici 0) le_rfl).2, fun _ => ex_16_7a_trunc hΦ kh⟩,
    fun i => (h10 i).2.2⟩
  · change Convex ℝ (aggTech _)
    rw [mc_aggTech_unit]; exact ex_16_7a_convex hΦ kh
  · left
    rw [mc_aggTech_unit]; exact ex_16_7a_interior hΦ hk

omit [Fintype ι] in
/-- Under (W1)–(W5) and nonsatiation in current consumption (`W(x + ε𝟙, z) > W(x, z)`), the
consumers are locally nonsatiated: `c + (1/(n+1))𝟙 → c` with strictly higher utility. -/
theorem mc_localNonsatiation {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i))
    (hstrict : ∀ i, ∀ x : Fin l → ℝ, ∀ z ε : ℝ, 0 ≤ x → 0 ≤ z → 0 < ε →
      W i x z < W i (x + fun _ => ε) z)
    {u : ι → BddSeq (Fin l → ℝ) → ℝ} (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) :
    LocalNonsatiation (fun _ : ι => mcCons l) u := by
  intro i x hx
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨fun n => x + mcConst fun _ => 1 / ((n : ℝ) + 1), fun n t => ?_, ?_,
    fun n => mc_utility_strict (hW i) (hstrict i) (hu i) hx (hε n)⟩
  · change (0 : Fin l → ℝ) ≤ (x + mcConst fun _ => 1 / ((n : ℝ) + 1) : BddSeq (Fin l → ℝ)) t
    rw [mc_add_apply, mcConst_apply]
    exact add_nonneg (hx t) fun _ => (hε n).le
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_sub_cancel_left]
    exact (norm_mcConst_le _).trans
      ((pi_norm_le_iff_of_nonneg (hε n).le).2 fun _ => by rw [Real.norm_of_nonneg (hε n).le])

/-- **The welfare theorems for §16.7**, corrected (NOTE to p. 497). Under (W1)–(W5),
nonsatiation in current consumption (`hstrict`), (T1)–(T7) and `k̂ ∈ int M`:
(a) every competitive equilibrium allocation is Pareto optimal (Theorem 15.3);
(b) every Pareto optimum is supported by some `φ ≠ 0` (Theorem 15.4), and also by a `ψ` without
weight at infinity, `ψ(x) = Σ_t ψ_t(x_t)` (Theorem 15.6). -/
theorem mc_welfare [Nonempty ι] {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i))
    (hstrict : ∀ i, ∀ x : Fin l → ℝ, ∀ z ε : ℝ, 0 ≤ x → 0 ≤ z → 0 < ε →
      W i x z < W i (x + fun _ => ε) z)
    {u : ι → BddSeq (Fin l → ℝ) → ℝ} (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i))
    (hΦ : ManyConsumersTech Φ) {kh : Fin p → ℝ} (hk : kh ∈ interior (mcM Φ))
    (c : ι → BddSeq (Fin l → ℝ)) (y : Unit → BddSeq (Fin l → ℝ)) :
    ((∃ φ, CompetitiveEq (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y φ) →
      ParetoOptimal (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y) ∧
    (ParetoOptimal (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y →
      (∃ φ : StrongDual ℝ (BddSeq (Fin l → ℝ)), φ ≠ 0 ∧
        SupportsAllocation (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y φ) ∧
      ∃ ψ : StrongDual ℝ (BddSeq (Fin l → ℝ)),
        SupportsAllocation (fun _ : ι => mcCons l) u (fun _ : Unit => mcProdSet Φ kh) c y ψ ∧
        ∀ x : BddSeq (Fin l → ℝ), HasSum (fun t => coordFunctional ψ t (x t)) (ψ x)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := mc_assumptions hW hu hΦ hk
  have hLNS := mc_localNonsatiation hW hstrict hu
  refine ⟨fun ⟨φ, hφ⟩ => theorem_15_3 hLNS hφ, fun hPO => ?_⟩
  have hns : ∀ i, ∃ xh ∈ mcCons l, u i (c i) < u i xh :=
    exists_better_of_localNonsatiation hLNS hPO.1.1
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨xh, hxh, hlt⟩ := hns i0
  obtain ⟨φ, hφ0, hφ⟩ := theorem_15_4 h1 h2 h3 h4 h5 hPO hxh hlt
  obtain ⟨ψ, r3, r4, -, hsum⟩ := theorem_15_6_of_supporting h1 h2 h6 h7 hPO hns
    ⟨φ, hφ0, hφ.1, hφ.2⟩
  exact ⟨⟨φ, hφ0, hφ⟩, ψ, ⟨r3, r4⟩, hsum⟩

/-- **The nonsatiation NOTE** (p. 497): (W1)–(W5) do not imply nonsatiation. `W ≡ 0` satisfies
(W1)–(W5) (any `β ∈ (0, 1)`), `u ≡ 0` is its fixed point, and local nonsatiation fails (no
consumption plan is better than any other). -/
theorem mc_nonsatiation_counterexample :
    ManyConsumersAggregator (fun (_ : Fin l → ℝ) (_ : ℝ) => (0 : ℝ)) (1 / 2) ∧
    IsAggregatorFixedPoint (Ici (0 : Fin l → ℝ)) (fun _ _ => 0) (fun _ => 0) ∧
    ¬ LocalNonsatiation (fun _ : Unit => mcCons l) (fun _ _ => (0 : ℝ)) := by
  refine ⟨⟨⟨by norm_num, by norm_num, continuousOn_const, rfl, fun _ _ => ⟨0, fun _ _ => by simp⟩,
    fun _ _ _ _ => le_rfl, fun _ _ _ _ _ _ => by simp⟩, fun _ _ _ _ _ _ _ _ => le_rfl,
    concaveOn_const _ ((convex_Ici 0).prod (convex_Ici 0))⟩,
    ⟨⟨0, fun _ _ => by simp⟩, continuousOn_const, fun _ _ => le_rfl, fun _ _ => rfl⟩, ?_⟩
  intro h
  obtain ⟨zs, -, -, hlt⟩ := h () 0 fun t => by
    change (0 : Fin l → ℝ) ≤ (0 : BddSeq (Fin l → ℝ)) t
    rw [lp.coeFn_zero]; rfl
  exact lt_irrefl _ (hlt 0)

end StokeyLucasPrescott.EquilibriumApplications
