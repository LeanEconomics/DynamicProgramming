/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDComplete

/-!
# Radner equilibrium, the transversality condition and natural debt limits

Miao, §13.4, pp. 427–435.

* Radner equilibrium with debt constraints (**Definition 13.4.1**, `rd_RadnerDC`) and with
  borrowing constraints (`rd_RadnerBC`); summing the budget equalities gives the goods-market
  condition of Definition 13.4.1 (`rd_goods_clearing`), which with zero supply is the
  feasibility condition (13.2) (`definition_13_4_1`).
* The present-value budget inequalities (13.19)–(13.20) (`eq_13_19`, `eq_13_19_E`, `eq_13_20`),
  the transversality condition (13.21) (`rd_TVC`), and the limits (13.22) (`eq_13_22`) and
  (13.23) (`eq_13_23`). (13.23) needs the transversality condition *conditional on* `sᵗ`; the
  date-0 condition (13.21) does not imply it (see `eq_13_23_counterexample` in `RDCounter`).
  A lower bound on the date-`T` value that vanishes in the limit is enough for (13.22)
  (`rd_AD_of_lowerTail`); bounded borrowing or debt limits supply one (`rd_AD_of_BC`,
  `rd_AD_of_DC`).
* The Arrow–Debreu equilibrium of §13.3 in this setting (`rd_ADEqm`, Definition 13.3.1, with the
  budget (13.5) `rd_ADBudget`), Pareto optimality (`rd_ParetoOptimal`) and the First Welfare
  Theorem in this setting (`rd_first_welfare`, Theorem 13.3.1 re-proved here as needed for §13.4).
* The competitive equilibrium with transversality condition (**Definition 13.4.2**,
  `rd_CETVC`). Its allocation is an Arrow–Debreu equilibrium allocation (`definition_13_4_2`),
  hence Pareto optimal (`rd_cetvc_pareto`). Conversely an Arrow–Debreu equilibrium with
  positive prices in `L¹` is a competitive equilibrium with transversality condition once the
  securities have rank `S` and are priced by its state prices (`rd_ad_cetvc`); this is the
  step of the claim on pp. 433–434 that follows the Second Welfare Theorem. The strategy is
  built by replication (`rd_repl`).
* The natural debt limit (13.24) (`eq_13_24`, `rd_naturalDebt_nonbinding`) and the natural
  borrowing limit (`rd_naturalBorrowing`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J ι : Type*} [Fintype S] [Fintype J] [Fintype ι]

omit [Fintype S] in
/-- A consumption-only problem: `c` maximises `U` over the plans satisfying `Feas`. -/
def rd_SolvesC (U : (List S → ℝ) → ℝ) (Feas : (List S → ℝ) → Prop) (c : List S → ℝ) : Prop :=
  Feas c ∧ ∀ c', Feas c' → U c' ≤ U c

/-- The budget constraint (13.11) holding with equality. -/
def rd_BudgetEq (p f : List S → J → ℝ) (y : List S → ℝ) (θm1 : J → ℝ) (c : List S → ℝ)
    (θ : List S → J → ℝ) : Prop :=
  ∀ h, c h + p h ⬝ᵥ θ h = rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h

/-- **Definition 13.4.1** (Miao, p. 427). A Radner equilibrium with debt constraints: every
agent solves (13.1) subject to (13.11) and (13.13), and markets clear,
`∑ᵢ cⁱ_t = ȳ_t + θ̄_{−1} · (f_t − p_t)`, `∑ᵢ θⁱ_t = θ̄_{−1}` (at the root `f₀ = p₀` as in
(13.11b)). -/
def rd_RadnerDC (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (θm1 : ι → J → ℝ)
    (p f : List S → J → ℝ) (Dbar : ι → List S → ℝ) (c : ι → List S → ℝ)
    (θ : ι → List S → J → ℝ) : Prop :=
  (∀ i, rd_Solves (U i) (rd_SeqFeas p f (y i) (θm1 i) (rd_ThetaDC f (Dbar i))) (c i) (θ i)) ∧
    (∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i) ∧
    ∀ h, ∑ i, θ i h = ∑ i, θm1 i

/-- A Radner equilibrium with borrowing constraints (13.14) (Miao, p. 428). -/
def rd_RadnerBC (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (θm1 : ι → J → ℝ)
    (p f : List S → J → ℝ) (Bbar : ι → List S → ℝ) (c : ι → List S → ℝ)
    (θ : ι → List S → J → ℝ) : Prop :=
  (∀ i, rd_Solves (U i) (rd_SeqFeas p f (y i) (θm1 i) (rd_ThetaBC p (Bbar i))) (c i) (θ i)) ∧
    (∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i) ∧
    ∀ h, ∑ i, θ i h = ∑ i, θm1 i

omit [Fintype S] [Fintype J] in
/-- The carried-in portfolios sum to the carried-in aggregate portfolio. -/
theorem rd_prev_sum (θ : ι → List S → J → ℝ) (θm1 : ι → J → ℝ) (h : List S) :
    ∑ i, rd_prev (θ i) (θm1 i) h = rd_prev (∑ i, θ i) (∑ i, θm1 i) h := by
  cases h with
  | nil => rfl
  | cons s h => simp [rd_prev]

omit [Fintype S] in
/-- Miao, p. 427: summing the budget equalities with `∑ᵢ θⁱ_t = θ̄_{−1}` gives the goods-market
clearing condition of Definition 13.4.1. -/
theorem rd_goods_clearing (p f : List S → J → ℝ) (y : ι → List S → ℝ) (θm1 : ι → J → ℝ)
    (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ)
    (hB : ∀ i, rd_BudgetEq p f (y i) (θm1 i) (c i) (θ i))
    (hθ : ∀ h, ∑ i, θ i h = ∑ i, θm1 i) (h : List S) :
    ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i := by
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hB i h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [← dotProduct_sum] at hsum
  rw [rd_prev_sum] at hsum
  have hprev : rd_prev (∑ i, θ i) (∑ i, θm1 i) h = ∑ i, θm1 i := by
    cases h with
    | nil => rfl
    | cons s g =>
      simp only [rd_prev]
      rw [← hθ g]
      simp
  rw [hprev, ← hθ h] at hsum
  rw [sub_dotProduct, ← hθ h]
  linarith

omit [Fintype S] [Fintype J] [Fintype ι] in
/-- **Definition 13.4.1**, remark (Miao, p. 428): when the security supply is zero, the
market-clearing condition is identical with the feasibility condition (13.2). -/
theorem definition_13_4_1 [Fintype J] [Fintype ι] (p f : List S → J → ℝ)
    (y : ι → List S → ℝ) (θm1 : ι → J → ℝ) (c : ι → List S → ℝ) (h0 : ∑ i, θm1 i = 0) :
    (∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ i, θm1 i) ↔
      ∀ h, ∑ i, c i h = ∑ i, y i h := by
  simp [h0]

/-- **(13.19)** (Miao, p. 432), in state prices `q⁰ = π Pr`. If `q` satisfies (13.16) and the
budget (13.11) holds, then at every node `sᵗ` and horizon `T`,
`∑_{j ≤ T} ∑ q c + ∑_{sᵗ⁺ᵀ} q (p · θ) ≤ q⁰_t (f_t · θ_{t−1}) + ∑_{j ≤ T} ∑ q y`. -/
theorem eq_13_19 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (h : List S) (T : ℕ) :
    ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * c g) h j +
        rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T ≤
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) h j := by
  have hpt : ∀ g, q g * c g + q g * (p g ⬝ᵥ θ g) ≤
      q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g) + q g * y g := by
    intro g
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hB g) (hq.1 g).le
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, rd_dsum_zero]
    exact hpt h
  | succ T ih =>
    rw [Finset.sum_range_succ (fun j => rd_dsum (fun g => q g * c g) h j) (T + 1),
      Finset.sum_range_succ (fun j => rd_dsum (fun g => q g * y g) h j) (T + 1)]
    have hV : rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T =
        rd_dsum (fun g => q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g)) h (T + 1) := by
      rw [rd_dsum_succ']
      exact rd_dsum_congr (fun g => rd_statePrice_dot hq g (θ g)) h T
    have hstep := rd_dsum_mono hpt h (T + 1)
    rw [rd_dsum_add, rd_dsum_add] at hstep
    linarith

/-- **(13.19)** in the book's form (Miao, p. 432), with conditional expectations and the
deflator `π = q⁰ / Pr`: `∑_{j≤T} E_t[π c] + E_t[π_{t+T} p_{t+T} · θ_{t+T}] ≤
π_t f_t · θ_{t−1} + ∑_{j≤T} E_t[π y]`. -/
theorem eq_13_19_E (T : RDTree S) {p f : List S → J → ℝ} {pd : List S → ℝ}
    (hq : rd_StatePrice p f (fun g => pd g * T.Pr g)) {y : List S → ℝ} {θm1 : J → ℝ}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) (h : List S)
    (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), rd_condE T (fun g => pd g * c g) h j +
        rd_condE T (fun g => pd g * (p g ⬝ᵥ θ g)) h n ≤
      pd h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑ j ∈ Finset.range (n + 1), rd_condE T (fun g => pd g * y g) h j := by
  have key := eq_13_19 hq hB h n
  have hP := T.pos h
  have e : ∀ X : List S → ℝ, ∀ j, rd_condE T (fun g => pd g * X g) h j =
      (T.Pr h)⁻¹ * rd_dsum (fun g => pd g * T.Pr g * X g) h j := by
    intro X j
    rw [rd_condE]
    congr 1
    exact rd_dsum_congr (fun g => by ring) h j
  simp only [e, ← Finset.mul_sum]
  have key' := mul_le_mul_of_nonneg_left key (inv_pos.2 hP).le
  rw [mul_add, mul_add] at key'
  have : (T.Pr h)⁻¹ * (pd h * T.Pr h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h)) =
      pd h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) := by
    field_simp
  linarith

/-- **(13.20)** (Miao, p. 432): (13.19) at the root,
`∑_{t≤T} E[π c] + E[π_T p_T · θ_T] ≤ π₀ p₀ · θ_{−1} + ∑_{t≤T} E[π y]`. -/
theorem eq_13_20 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), rd_dsum (fun g => q g * c g) [] t +
        rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑ t ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) [] t :=
  eq_13_19 hq hB [] T

/-- The transversality condition (13.21), `lim_{T→∞} E[π_T p_T · θ_T] = 0`, in state prices.
(The book prints `T → 0`.) -/
def rd_TVC (q : List S → ℝ) (p : List S → J → ℝ) (θ : List S → J → ℝ) : Prop :=
  Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T) atTop (𝓝 0)

/-- The limit of (13.19) at a node under a vanishing lower bound on the date-`T` value: if
`∑ q (p · θ)` over `sᵗ⁺ᵀ | sᵗ` is at least `−e_T` with `e_T → 0`, then
`∑_j ∑ q c ≤ q_t f_t · θ_{t−1} + ∑_j ∑ q y`. -/
theorem rd_AD_of_lowerTail_at {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ}
    {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) (h : List S) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hlow : ∀ T, -e T ≤ rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T)
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    ∑' j, rd_dsum (fun g => q g * c g) h j ≤
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) + ∑' j, rd_dsum (fun g => q g * y g) h j := by
  have hA := hc.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hY := hy.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun T => q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
      ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) h j + e T) atTop
      (𝓝 (q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑' j, rd_dsum (fun g => q g * y g) h j + 0)) :=
    (tendsto_const_nhds.add hY).add he
  rw [add_zero] at hR
  refine le_of_tendsto_of_tendsto' hA hR fun T => ?_
  have := eq_13_19 hq hB h T
  have := hlow T
  simp only [Function.comp_apply]
  linarith

/-- **(13.22)** under a vanishing lower bound on the date-`T` value. -/
theorem rd_AD_of_lowerTail {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ}
    {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hlow : ∀ T, -e T ≤ rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T)
    (hc : Summable fun t => rd_dsum (fun g => q g * c g) [] t)
    (hy : Summable fun t => rd_dsum (fun g => q g * y g) [] t) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t :=
  rd_AD_of_lowerTail_at hq hB [] he hlow hc hy

/-- **(13.22)** (Miao, p. 433): under the transversality condition (13.21), the limit of (13.20)
is the present-value budget `E ∑ πc ≤ π₀ p₀ · θ_{−1} + E ∑ πy`. -/
theorem eq_13_22 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (hT : rd_TVC q p θ)
    (hc : Summable fun t => rd_dsum (fun g => q g * c g) [] t)
    (hy : Summable fun t => rd_dsum (fun g => q g * y g) [] t) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t := by
  refine rd_AD_of_lowerTail hq hB (e := fun T => |rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) [] T|)
    ?_ (fun T => neg_abs_le _) hc hy
  simpa using hT.abs

/-- **(13.23)** (Miao, p. 433): at a node `sᵗ`, under the transversality condition *conditional on
`sᵗ`*, `E_t ∑ π c ≤ π_t f_t · θ_{t−1} + E_t ∑ π y`. -/
theorem eq_13_23 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (h : List S)
    (hT : Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T) atTop (𝓝 0))
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    ∑' j, rd_dsum (fun g => q g * c g) h j ≤
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) + ∑' j, rd_dsum (fun g => q g * y g) h j := by
  refine rd_AD_of_lowerTail_at hq hB h
    (e := fun T => |rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T|) ?_ (fun T => neg_abs_le _) hc hy
  simpa using hT.abs

/-- A process whose date sums are absolutely summable has summable subtree sums at every node. -/
theorem rd_summable_subtree {F : List S → ℝ}
    (hF : Summable fun t => rd_dsum (fun g => |F g|) [] t) (h : List S) :
    Summable fun j => rd_dsum F h j := by
  refine Summable.of_norm_bounded ((summable_nat_add_iff h.length).2 hF) fun j => ?_
  rw [Real.norm_eq_abs, add_comm]
  exact (rd_abs_dsum_le _ _ _).trans (rd_dsum_le_root (fun g => abs_nonneg _) h j)

/-- **(13.22)** for a borrowing-constrained plan: if `p · θ ≥ −B` with `B` bounded and `q ∈ L¹`,
the budget (13.11) implies the present-value budget (13.22). -/
theorem rd_AD_of_BC {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (hL : rd_L1 q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) {Bbar : List S → ℝ} (hBb : rd_Bdd Bbar)
    (hθ : θ ∈ rd_ThetaBC p Bbar) (hc : rd_Bdd c) (hy : rd_Bdd y) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t := by
  refine rd_AD_of_lowerTail hq hB (e := fun T => rd_dsum (fun g => q g * Bbar g) [] T)
    (rd_L1_mul_tendsto hL hBb) (fun T => ?_) (rd_L1_mul hL hc) (rd_L1_mul hL hy)
  rw [← rd_dsum_neg]
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [← mul_neg]
  exact mul_le_mul_of_nonneg_left (hθ g) (hq.1 g).le

/-- **(13.22)** for a debt-constrained plan: if `f · θ ≥ −D` with `D` bounded and `q ∈ L¹`, the
budget (13.11) implies the present-value budget (13.22). -/
theorem rd_AD_of_DC {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    (hL : rd_L1 q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) {Dbar : List S → ℝ} (hDb : rd_Bdd Dbar)
    (hθ : θ ∈ rd_ThetaDC f Dbar) (hc : rd_Bdd c) (hy : rd_Bdd y) :
    ∑' t, rd_dsum (fun g => q g * c g) [] t ≤
      q [] * (p [] ⬝ᵥ θm1) + ∑' t, rd_dsum (fun g => q g * y g) [] t := by
  have hlim := (rd_L1_mul_tendsto hL hDb).comp (tendsto_add_atTop_nat 1)
  refine rd_AD_of_lowerTail hq hB (e := fun T => rd_dsum (fun g => q g * Dbar g) [] (T + 1))
    hlim (fun T => ?_) (rd_L1_mul hL hc) (rd_L1_mul hL hy)
  rw [← rd_dsum_neg, rd_dsum_succ']
  refine rd_dsum_mono (fun g => ?_) _ _
  rw [rd_statePrice_dot hq g]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← mul_neg]
  exact mul_le_mul_of_nonneg_left (hθ g s) (hq.1 _).le

/-- The Arrow–Debreu budget (13.5): `∑ₜ ∑_{sᵗ} q⁰ c ≤ ∑ₜ ∑_{sᵗ} q⁰ y`. -/
def rd_ADBudget (q y c : List S → ℝ) : Prop :=
  ∑' t, rd_dsum (fun g => q g * c g) [] t ≤ ∑' t, rd_dsum (fun g => q g * y g) [] t

/-- Definition 13.3.1 in this setting: an Arrow–Debreu equilibrium `(q⁰, c)` with `q⁰ ∈ L¹`,
each `cⁱ` maximising `Uⁱ` over `L^∞₊` subject to (13.5), and (13.2). -/
def rd_ADEqm (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (q : List S → ℝ)
    (c : ι → List S → ℝ) : Prop :=
  rd_L1 q ∧ (∀ i, rd_SolvesC (U i) (fun c' => rd_LinfPos c' ∧ rd_ADBudget q (y i) c') (c i)) ∧
    ∀ h, ∑ i, c i h = ∑ i, y i h

/-- Feasible allocations (13.2) in `(L^∞₊)ᴵ`. -/
def rd_Feasible (y : ι → List S → ℝ) (c : ι → List S → ℝ) : Prop :=
  (∀ i, rd_LinfPos (c i)) ∧ ∀ h, ∑ i, c i h = ∑ i, y i h

/-- Pareto optimality (Miao, p. 417). -/
def rd_ParetoOptimal (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (c : ι → List S → ℝ) :
    Prop :=
  rd_Feasible y c ∧ ¬ ∃ c', rd_Feasible y c' ∧ (∀ i, U i (c i) ≤ U i (c' i)) ∧
    ∃ i, U i (c i) < U i (c' i)

/-- Raising consumption at the root by `ε` raises the date-sum value by `q(s⁰) ε`. -/
theorem rd_tsum_add_root {q c : List S → ℝ}
    (hc : Summable fun t => rd_dsum (fun g => q g * c g) [] t) (ε : ℝ) :
    ∑' t, rd_dsum (fun g => q g * (c g + if g = [] then ε else 0)) [] t =
      ∑' t, rd_dsum (fun g => q g * c g) [] t + q [] * ε := by
  classical
  have e : ∀ t, rd_dsum (fun g => q g * (c g + if g = [] then ε else 0)) [] t =
      rd_dsum (fun g => q g * c g) [] t + if t = 0 then q [] * ε else 0 := by
    intro t
    have : (fun g => q g * (c g + if g = [] then ε else 0)) =
        fun g => q g * c g + if g = [] then q [] * ε else 0 := by
      funext g
      split_ifs with hg
      · rw [hg]; ring
      · ring
    rw [this, rd_dsum_add, rd_dsum_ite]
    simp only [List.length_nil, eq_comm]
  simp only [e]
  rw [Summable.tsum_add hc ⟨_, hasSum_ite_eq 0 (q [] * ε)⟩, tsum_ite_eq]

/-- Theorem 13.3.1 (First Welfare Theorem) in this setting (Miao, p. 421), used on p. 433:
with strictly increasing utilities, positive state prices in `L¹` and bounded endowments, an
Arrow–Debreu equilibrium allocation is Pareto optimal. -/
theorem rd_first_welfare {U : ι → (List S → ℝ) → ℝ} {y : ι → List S → ℝ} {q : List S → ℝ}
    {c : ι → List S → ℝ} (hU : ∀ i, rd_StrictIncr (U i)) (hq : ∀ h, 0 < q h)
    (hy : ∀ i, rd_Bdd (y i)) (hAD : rd_ADEqm U y q c) : rd_ParetoOptimal U y c := by
  classical
  obtain ⟨hL, hopt, hclear⟩ := hAD
  refine ⟨⟨fun i => (hopt i).1.1, hclear⟩, ?_⟩
  rintro ⟨c', ⟨hc'f, hc'c⟩, hweak, i0, hstrict⟩
  have hs : ∀ i, Summable fun t => rd_dsum (fun g => q g * c' i g) [] t :=
    fun i => rd_L1_mul hL (hc'f i).1
  have hsy : ∀ i, Summable fun t => rd_dsum (fun g => q g * y i g) [] t :=
    fun i => rd_L1_mul hL (hy i)
  have hge : ∀ i, ∑' t, rd_dsum (fun g => q g * y i g) [] t ≤
      ∑' t, rd_dsum (fun g => q g * c' i g) [] t := by
    intro i
    by_contra hlt
    push Not at hlt
    set ε := (∑' t, rd_dsum (fun g => q g * y i g) [] t -
      ∑' t, rd_dsum (fun g => q g * c' i g) [] t) / q []
    have hε : 0 < ε := div_pos (by linarith) (hq [])
    set c'' : List S → ℝ := fun g => c' i g + if g = [] then ε else 0
    have hc'' : rd_LinfPos c'' := by
      obtain ⟨⟨M, hM⟩, h0⟩ := hc'f i
      refine ⟨⟨M + ε, fun g => ?_⟩, fun g => ?_⟩
      · simp only [c'']
        refine (abs_add_le _ _).trans (add_le_add (hM g) ?_)
        split_ifs <;> simp [abs_of_pos hε, hε.le]
      · simp only [c'']
        split_ifs <;> linarith [h0 g]
    have hbud : rd_ADBudget q (y i) c'' := by
      rw [rd_ADBudget, rd_tsum_add_root (hs i)]
      simp only [ε]
      rw [mul_div_cancel₀ _ (hq []).ne']
      linarith
    have hlt2 : U i (c' i) < U i c'' := by
      refine hU i _ _ (hc'f i) hc'' (fun g => ?_) ?_
      · simp only [c'']
        split_ifs <;> linarith
      · intro he
        have := congrFun he []
        simp only [c'', ↓reduceIte] at this
        linarith
    exact absurd ((hopt i).2 c'' ⟨hc'', hbud⟩) (not_le.2 ((hweak i).trans_lt hlt2))
  have hgt : ∑' t, rd_dsum (fun g => q g * y i0 g) [] t <
      ∑' t, rd_dsum (fun g => q g * c' i0 g) [] t := by
    by_contra hle
    push Not at hle
    exact absurd ((hopt i0).2 (c' i0) ⟨hc'f i0, hle⟩) (not_le.2 hstrict)
  have htot : ∑ i, ∑' t, rd_dsum (fun g => q g * y i g) [] t <
      ∑ i, ∑' t, rd_dsum (fun g => q g * c' i g) [] t :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i0, Finset.mem_univ _, hgt⟩
  have hswap : ∀ x : ι → List S → ℝ, (∀ i, Summable fun t => rd_dsum (fun g => q g * x i g) [] t) →
      ∑ i, ∑' t, rd_dsum (fun g => q g * x i g) [] t =
        ∑' t, rd_dsum (fun g => q g * ∑ i, x i g) [] t := by
    intro x hx
    rw [← Summable.tsum_finsetSum fun i _ => hx i]
    refine tsum_congr fun t => ?_
    rw [← rd_dsum_finsetSum]
    exact rd_dsum_congr (fun g => by rw [Finset.mul_sum]) _ _
  rw [hswap _ hsy, hswap _ hs] at htot
  simp only [hc'c] at htot
  exact lt_irrefl _ htot

/-- **Definition 13.4.2** (Miao, p. 433). A competitive equilibrium with transversality
condition `((cⁱ, θⁱ), π, p) ∈ (L^∞₊)ᴵ × Θᴵ × L¹₊₊ × (L^∞₊)ᴶ` (here `π ∈ L¹` means
`q⁰ = π Pr ∈ L¹`): (i) each `(cⁱ, θⁱ)` maximises (13.1) subject to (13.11) and (13.21);
(ii) each `cⁱ` maximises (13.1) subject to (13.22); (iii) `(π, p)` satisfies (13.18)
(equivalently (13.16) for `q⁰ = π Pr`, `eq_13_18`); (iv) (13.2) and `∑ᵢ θⁱ_t = θ̄_{−1}`. -/
def rd_CETVC (T : RDTree S) (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ)
    (θm1 : ι → J → ℝ) (f : List S → J → ℝ) (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ)
    (pd : List S → ℝ) (p : List S → J → ℝ) : Prop :=
  (∀ i, rd_LinfPos (c i)) ∧ rd_L1 (fun g => pd g * T.Pr g) ∧ (∀ h, 0 < pd h) ∧
    (∀ h j, 0 ≤ p h j) ∧ (∀ j, rd_Bdd fun h => p h j) ∧
    (∀ i, rd_Solves (U i) (fun c' θ' => rd_LinfPos c' ∧ rd_Budget p f (y i) (θm1 i) c' θ' ∧
      rd_TVC (fun g => pd g * T.Pr g) p θ') (c i) (θ i)) ∧
    (∀ i, rd_SolvesC (U i) (fun c' => rd_LinfPos c' ∧
      ∑' t, rd_dsum (fun g => pd g * T.Pr g * c' g) [] t ≤
        pd [] * T.Pr [] * (p [] ⬝ᵥ θm1 i) + ∑' t, rd_dsum (fun g => pd g * T.Pr g * y i g) [] t)
      (c i)) ∧
    rd_StatePrice p f (fun g => pd g * T.Pr g) ∧
    (∀ h, ∑ i, c i h = ∑ i, y i h) ∧ ∀ h, ∑ i, θ i h = ∑ i, θm1 i

/-- **Definition 13.4.2**, remark (Miao, p. 433): with zero initial holdings, the allocation of a
competitive equilibrium with transversality condition is an Arrow–Debreu equilibrium allocation
with state prices `q⁰ = π Pr` ((13.22) is (13.5) when `θ_{−1} = 0`). -/
theorem definition_13_4_2 (T : RDTree S) {U : ι → (List S → ℝ) → ℝ} {y : ι → List S → ℝ}
    {f : List S → J → ℝ} {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ} {pd : List S → ℝ}
    {p : List S → J → ℝ} (hE : rd_CETVC T U y (fun _ => 0) f c θ pd p) :
    rd_ADEqm U y (fun g => pd g * T.Pr g) c := by
  obtain ⟨-, hL, -, -, -, -, hii, -, hclear, -⟩ := hE
  refine ⟨hL, fun i => ?_, hclear⟩
  simp only [dotProduct_zero, mul_zero, zero_add] at hii
  exact hii i

/-- Miao, p. 433: "and hence is Pareto optimal" (via `rd_first_welfare`). -/
theorem rd_cetvc_pareto (T : RDTree S) {U : ι → (List S → ℝ) → ℝ} {y : ι → List S → ℝ}
    {f : List S → J → ℝ} {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ} {pd : List S → ℝ}
    {p : List S → J → ℝ} (hU : ∀ i, rd_StrictIncr (U i)) (hy : ∀ i, rd_Bdd (y i))
    (hE : rd_CETVC T U y (fun _ => 0) f c θ pd p) : rd_ParetoOptimal U y c :=
  rd_first_welfare hU (fun h => mul_pos (hE.2.2.1 h) (T.pos h)) hy (definition_13_4_2 T hE)

/-- The present value, at `sᵗ`, of `q x` over the strict descendants of `sᵗ`. -/
noncomputable def rd_W (q x : List S → ℝ) (h : List S) : ℝ :=
  ∑' j, rd_dsum (fun g => q g * x g) h (j + 1)

/-- The subtree sum splits into successors: `W(sᵗ) = ∑ₛ (q x (sᵗ, s) + W(sᵗ, s))`. -/
theorem rd_W_rec {q x : List S → ℝ}
    (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t) (h : List S) :
    rd_W q x h = ∑ s, (q (s :: h) * x (s :: h) + rd_W q x (s :: h)) := by
  rw [rd_W]
  simp only [rd_dsum_succ]
  rw [Summable.tsum_finsetSum fun s _ => rd_summable_subtree hs (s :: h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [(rd_summable_subtree hs (s :: h)).tsum_eq_zero_add, rd_dsum_zero, rd_W]

/-- The date sums of `W` are tails of the summable date sums of `q x`. -/
theorem rd_W_dsum {q x : List S → ℝ}
    (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t) (T : ℕ) :
    rd_dsum (rd_W q x) [] T = ∑' j, rd_dsum (fun g => q g * x g) [] (j + (T + 1)) := by
  rw [rd_dsum]
  simp only [List.append_nil, rd_W]
  rw [← Summable.tsum_finsetSum fun l _ =>
    (summable_nat_add_iff 1).2 (rd_summable_subtree hs l)]
  refine tsum_congr fun j => ?_
  rw [show j + (T + 1) = T + (j + 1) by ring, rd_dsum_add_len, rd_dsum]
  simp only [List.append_nil]

/-- The date sums of `W` vanish in the limit. -/
theorem rd_W_tendsto {q x : List S → ℝ}
    (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t) :
    Tendsto (fun T => rd_dsum (rd_W q x) [] T) atTop (𝓝 0) := by
  simp only [rd_W_dsum hs]
  exact (tendsto_sum_nat_add fun t => rd_dsum (fun g => q g * x g) [] t).comp
    (tendsto_add_atTop_nat 1)

/-- The replicating portfolio at `sᵗ`: `D (DᵀD)⁻¹ z` with `z_s = x(sᵗ, s) + W(sᵗ, s)/q(sᵗ, s)`.
-/
noncomputable def rd_repl [DecidableEq S] (f : List S → J → ℝ) (q x : List S → ℝ)
    (h : List S) : J → ℝ :=
  Matrix.mulVec (rd_payoffMatrix f h *
      (Matrix.transpose (rd_payoffMatrix f h) * rd_payoffMatrix f h)⁻¹)
    fun s => x (s :: h) + rd_W q x (s :: h) / q (s :: h)

/-- With rank `S`, `D (DᵀD)⁻¹` is a right inverse of `Dᵀ`: the replicating portfolio pays
`z_s` in each successor state. -/
theorem rd_repl_payoff [DecidableEq S] (f : List S → J → ℝ) (q x : List S → ℝ) (h : List S)
    (hrank : (rd_payoffMatrix f h).rank = Fintype.card S) (s : S) :
    f (s :: h) ⬝ᵥ rd_repl f q x h = x (s :: h) + rd_W q x (s :: h) / q (s :: h) := by
  set D := rd_payoffMatrix f h
  have hdet : IsUnit (D.transpose * D).det := by
    have := (theorem_13_4_3_formula (p := fun g j => ∑ s', f (s' :: g) j)
      (q := fun _ => 1) ⟨fun _ => one_pos, fun g j => by simp⟩ h hrank).1
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  rw [← rd_payoffMatrix_transpose_mulVec, rd_repl, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    show rd_payoffMatrix f h = D from rfl, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The replicating portfolio costs `W(sᵗ)/q(sᵗ)`: `q (p · θ) = W`. -/
theorem rd_repl_value [DecidableEq S] {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S)
    {x : List S → ℝ} (hs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t)
    (h : List S) : q h * (p h ⬝ᵥ rd_repl f q x h) = rd_W q x h := by
  rw [rd_statePrice_dot hq, rd_W_rec hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rd_repl_payoff f q x h (hrank h), mul_add, mul_div_cancel₀ _ (hq.1 _).ne']

/-- The replicating strategy finances `c` from `y` when `c` satisfies the Arrow–Debreu budget:
it satisfies (13.11) with `θ_{−1} = 0` (with equality at every node after the root) and the
transversality condition (13.21). -/
theorem rd_repl_budget [DecidableEq S] {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) (hL : rd_L1 q)
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) {c y : List S → ℝ}
    (hc : rd_Bdd c) (hy : rd_Bdd y) (hbud : rd_ADBudget q y c) :
    rd_Budget p f y 0 c (rd_repl f q fun g => c g - y g) ∧
      rd_TVC q p (rd_repl f q fun g => c g - y g) ∧
      ∀ s g, c (s :: g) + p (s :: g) ⬝ᵥ rd_repl f q (fun g => c g - y g) (s :: g) =
        f (s :: g) ⬝ᵥ rd_repl f q (fun g => c g - y g) g + y (s :: g) := by
  set x : List S → ℝ := fun g => c g - y g
  have hxs : Summable fun t => rd_dsum (fun g => |q g * x g|) [] t :=
    rd_L1_mul_abs hL (rd_bdd_sub hc hy)
  have hpv : ∀ h, p h ⬝ᵥ rd_repl f q x h = rd_W q x h / q h := fun h => by
    rw [← rd_repl_value hq hrank hxs h, mul_div_cancel_left₀ _ (hq.1 h).ne']
  have hcons : ∀ s g, c (s :: g) + p (s :: g) ⬝ᵥ rd_repl f q x (s :: g) =
      f (s :: g) ⬝ᵥ rd_repl f q x g + y (s :: g) := by
    intro s g
    rw [hpv, rd_repl_payoff f q x g (hrank g)]
    simp only [x]
    ring
  refine ⟨fun h => ?_, ?_, hcons⟩
  · cases h with
    | nil =>
      rw [hpv]
      simp only [rd_fz, rd_prev, dotProduct_zero, zero_add]
      rw [rd_ADBudget] at hbud
      have hsum : ∑' t, rd_dsum (fun g => q g * x g) [] t = q [] * x [] + rd_W q x [] := by
        rw [(rd_summable_subtree hxs []).tsum_eq_zero_add, rd_dsum_zero, rd_W]
      have hsub : ∑' t, rd_dsum (fun g => q g * x g) [] t =
          ∑' t, rd_dsum (fun g => q g * c g) [] t - ∑' t, rd_dsum (fun g => q g * y g) [] t := by
        rw [← Summable.tsum_sub (rd_L1_mul hL hc) (rd_L1_mul hL hy)]
        refine tsum_congr fun t => ?_
        rw [← rd_dsum_sub]
        exact rd_dsum_congr (fun g => by simp only [x]; ring) _ _
      have hq0 := hq.1 []
      have hW : rd_W q x [] / q [] ≤ -(x []) := by
        rw [div_le_iff₀ hq0]
        linarith
      simp only [x] at hW
      linarith
    | cons s g => exact (hcons s g).le
  · have e : (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ rd_repl f q x g)) [] T) =
        fun T => rd_dsum (rd_W q x) [] T :=
      funext fun T => rd_dsum_congr (fun g => rd_repl_value hq hrank hxs g) [] T
    rw [rd_TVC, e]
    exact rd_W_tendsto hxs

/-- With market clearing, the replicating strategies sum to zero. -/
theorem rd_repl_sum_zero [DecidableEq S] (f : List S → J → ℝ) {q : List S → ℝ} (hL : rd_L1 q)
    {c y : ι → List S → ℝ} (hcb : ∀ i, rd_Bdd (c i)) (hy : ∀ i, rd_Bdd (y i))
    (hclear : ∀ h, ∑ i, c i h = ∑ i, y i h) (h : List S) :
    ∑ i, rd_repl f q (fun g => c i g - y i g) h = 0 := by
  have hxs : ∀ i, Summable fun t => rd_dsum (fun g => |q g * (c i g - y i g)|) [] t :=
    fun i => rd_L1_mul_abs hL (rd_bdd_sub (hcb i) (hy i))
  have hW0 : ∀ g, ∑ i, rd_W q (fun g => c i g - y i g) g = 0 := by
    intro g
    simp only [rd_W]
    rw [← Summable.tsum_finsetSum fun i _ =>
      (summable_nat_add_iff 1).2 (rd_summable_subtree (hxs i) g)]
    have : ∀ j, ∑ i, rd_dsum (fun g => q g * (c i g - y i g)) g (j + 1) = 0 := by
      intro j
      rw [← rd_dsum_finsetSum]
      have : (fun g => ∑ i, q g * (c i g - y i g)) = fun _ => 0 := by
        funext g
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hclear g, sub_self, mul_zero]
      rw [this]
      simp [rd_dsum]
    simp only [this, tsum_zero]
  simp only [rd_repl]
  rw [← Matrix.mulVec_sum]
  refine (congrArg _ ?_).trans (Matrix.mulVec_zero _)
  funext s
  simp only [Finset.sum_apply, Pi.zero_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hclear (s :: h), sub_self, zero_add, div_eq_mul_inv, ← Finset.sum_mul, hW0, zero_mul]

/-- Miao, pp. 433–434 (the step after the Second Welfare Theorem in the claim that Pareto optima
are supported): an Arrow–Debreu equilibrium `(q⁰, c)` with `q⁰ > 0` in `L¹`, bounded endowments,
zero initial holdings, securities of rank `S` at every node priced by `q⁰` through (13.16), and
`p ∈ (L^∞₊)ᴶ`, is a competitive equilibrium with transversality condition, with deflator
`π = q⁰/Pr` and replicating strategies `θⁱ` with `f_t · θⁱ_{t−1} − p_t · θⁱ_t = cⁱ_t − yⁱ_t`. -/
theorem rd_ad_cetvc [DecidableEq S] (T : RDTree S) {U : ι → (List S → ℝ) → ℝ}
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} {p f : List S → J → ℝ}
    (hAD : rd_ADEqm U y q c) (hy : ∀ i, rd_Bdd (y i)) (hq : rd_StatePrice p f q)
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) (hp0 : ∀ h j, 0 ≤ p h j)
    (hpb : ∀ j, rd_Bdd fun h => p h j) :
    rd_CETVC T U y (fun _ => 0) f c (fun i => rd_repl f q fun g => c i g - y i g)
      (fun g => q g / T.Pr g) p := by
  obtain ⟨hL, hopt, hclear⟩ := hAD
  have hqpd : ∀ g, q g / T.Pr g * T.Pr g = q g := fun g => div_mul_cancel₀ _ (T.pos g).ne'
  simp only [rd_CETVC, hqpd]
  have hcb : ∀ i, rd_Bdd (c i) := fun i => (hopt i).1.1.1
  -- every plan satisfying (13.11) and (13.21) satisfies the Arrow–Debreu budget
  have hseqAD : ∀ i c' θ', rd_LinfPos c' → rd_Budget p f (y i) 0 c' θ' → rd_TVC q p θ' →
      rd_ADBudget q (y i) c' := by
    intro i c' θ' hc' hB hT
    have := eq_13_22 hq hB hT (rd_L1_mul hL hc'.1) (rd_L1_mul hL (hy i))
    simpa [rd_ADBudget] using this
  have hfeas : ∀ i, rd_LinfPos (c i) ∧ rd_Budget p f (y i) 0 (c i)
      (rd_repl f q fun g => c i g - y i g) ∧ rd_TVC q p (rd_repl f q fun g => c i g - y i g) :=
    fun i => ⟨(hopt i).1.1, (rd_repl_budget hq hL hrank (hcb i) (hy i) (hopt i).1.2).1,
      (rd_repl_budget hq hL hrank (hcb i) (hy i) (hopt i).1.2).2.1⟩
  refine ⟨fun i => (hopt i).1.1, hL, fun h => div_pos (hq.1 h) (T.pos h), hp0, hpb,
    fun i => ⟨hfeas i, fun c' θ' ⟨hc', hB, hT⟩ => (hopt i).2 c' ⟨hc', hseqAD i c' θ' hc' hB hT⟩⟩,
    fun i => ⟨⟨(hopt i).1.1, by simpa [rd_ADBudget] using (hopt i).1.2⟩,
      fun c' ⟨hc', hb⟩ => (hopt i).2 c' ⟨hc', by simpa [rd_ADBudget] using hb⟩⟩,
    hq, hclear, fun h => ?_⟩
  simp only [Finset.sum_const_zero]
  exact rd_repl_sum_zero f hL hcb hy hclear h

/-- **(13.24)** (Miao, p. 434): under (13.23)'s hypotheses and `c ≥ 0`, agent `i`'s debt cannot
exceed the present value of current and future endowments,
`f_t · θ_{t−1} ≥ −(1/π_t) E_t ∑_j π_{t+j} y_{t+j}`. -/
theorem eq_13_24 {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (hc0 : ∀ g, 0 ≤ c g) (h : List S)
    (hT : Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T) atTop (𝓝 0))
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    -((q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j) ≤
      rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by
  have key := eq_13_23 hq hB h hT hc hy
  have hnn : 0 ≤ ∑' j, rd_dsum (fun g => q g * c g) h j :=
    tsum_nonneg fun j => rd_dsum_nonneg (fun g => mul_nonneg (hq.1 g).le (hc0 g)) h j
  have hqh := hq.1 h
  have h1 : -∑' j, rd_dsum (fun g => q g * y g) h j ≤ q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) := by
    linarith
  calc -((q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j)
      = (q h)⁻¹ * -∑' j, rd_dsum (fun g => q g * y g) h j := by ring
    _ ≤ (q h)⁻¹ * (q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hqh.le)
    _ = rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by field_simp

/-- The natural debt limit `D̄_t = (1/π_t) E_t ∑_j π_{t+j} y_{t+j}` (Miao, p. 434), in state
prices. -/
noncomputable def rd_naturalDebtLimit (q y : List S → ℝ) (h : List S) : ℝ :=
  (q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j

/-- Miao, p. 435: under the natural debt limit, the debt constraint never binds when optimal
consumption is strictly positive (the inequality (13.24) is strict). -/
theorem rd_naturalDebt_nonbinding {p f : List S → J → ℝ} {q : List S → ℝ}
    (hq : rd_StatePrice p f q) {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ}
    {θ : List S → J → ℝ} (hB : rd_Budget p f y θm1 c θ) (hc0 : ∀ g, 0 ≤ c g) (h : List S)
    (hcpos : 0 < c h)
    (hT : Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T) atTop (𝓝 0))
    (hc : Summable fun j => rd_dsum (fun g => q g * c g) h j)
    (hy : Summable fun j => rd_dsum (fun g => q g * y g) h j) :
    -rd_naturalDebtLimit q y h < rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by
  have key := eq_13_23 hq hB h hT hc hy
  have hnn : q h * c h ≤ ∑' j, rd_dsum (fun g => q g * c g) h j := by
    have := hc.le_tsum 0 (fun j _ => rd_dsum_nonneg (fun g => mul_nonneg (hq.1 g).le (hc0 g)) h j)
    rwa [rd_dsum_zero] at this
  have hpos : 0 < q h * c h := mul_pos (hq.1 h) hcpos
  have hqh := hq.1 h
  have h1 : -∑' j, rd_dsum (fun g => q g * y g) h j < q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) := by
    linarith
  rw [rd_naturalDebtLimit]
  calc -((q h)⁻¹ * ∑' j, rd_dsum (fun g => q g * y g) h j)
      = (q h)⁻¹ * -∑' j, rd_dsum (fun g => q g * y g) h j := by ring
    _ < (q h)⁻¹ * (q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h)) :=
        mul_lt_mul_of_pos_left h1 (inv_pos.2 hqh)
    _ = rd_fz p f h ⬝ᵥ rd_prev θ θm1 h := by field_simp

/-- The natural borrowing limit (Miao, p. 435): by (13.18), `θ_{t−1} · p_{t−1} =
(1/π_{t−1}) E_{t−1}[π_t f_t · θ_{t−1}]`, and by (13.24) at each successor this is at least
`−(1/π_{t−1}) ∑ₛ E_t ∑_j π_{t+j} y_{t+j}`. -/
theorem rd_naturalBorrowing {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_Budget p f y θm1 c θ) (hc0 : ∀ g, 0 ≤ c g) (g : List S)
    (hT : ∀ s, Tendsto (fun T => rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) (s :: g) T) atTop (𝓝 0))
    (hc : ∀ s, Summable fun j => rd_dsum (fun g => q g * c g) (s :: g) j)
    (hy : ∀ s, Summable fun j => rd_dsum (fun g => q g * y g) (s :: g) j) :
    q g * (p g ⬝ᵥ θ g) = ∑ s, q (s :: g) * (f (s :: g) ⬝ᵥ θ g) ∧
      -(q g)⁻¹ * ∑ s, ∑' j, rd_dsum (fun g => q g * y g) (s :: g) j ≤ p g ⬝ᵥ θ g := by
  refine ⟨rd_statePrice_dot hq g (θ g), ?_⟩
  have hqg := hq.1 g
  have hb : ∀ s, -∑' j, rd_dsum (fun g => q g * y g) (s :: g) j ≤
      q (s :: g) * (f (s :: g) ⬝ᵥ θ g) := by
    intro s
    have := eq_13_24 hq hB hc0 (s :: g) (hT s) (hc s) (hy s)
    simp only [rd_fz, rd_prev] at this
    have hqs := hq.1 (s :: g)
    have := mul_le_mul_of_nonneg_left this hqs.le
    rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hqs.ne', one_mul] at this
    exact this
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hb s
  rw [Finset.sum_neg_distrib, ← rd_statePrice_dot hq g] at hsum
  calc -(q g)⁻¹ * ∑ s, ∑' j, rd_dsum (fun g => q g * y g) (s :: g) j
      = (q g)⁻¹ * -∑ s, ∑' j, rd_dsum (fun g => q g * y g) (s :: g) j := by ring
    _ ≤ (q g)⁻¹ * (q g * (p g ⬝ᵥ θ g)) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hqg.le)
    _ = p g ⬝ᵥ θ g := by field_simp

end Miao.CompleteMarkets
