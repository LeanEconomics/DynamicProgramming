/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDImpatience

/-!
# Equivalence of equilibria: Theorem 13.5.1

Miao, §13.5, pp. 435–439. All assets are in zero supply and `θⁱ_{−1} = 0`.

* `rd_RadnerBCnb`, `rd_RadnerDCnb`: Radner equilibria with nonbinding *bounded* borrowing or debt
  limits (bounded limits are what makes Example 13.5.1 a counterexample).
* **Theorem 13.5.1, "if"** (`theorem_13_5_1_if`, corrected). Under complete markets and
  Assumption 13.5.1, a competitive equilibrium with transversality condition `(c, θ, π, p)` yields
  a Radner equilibrium with nonbinding bounded borrowing constraints and one with nonbinding
  bounded debt constraints, with the same allocation and prices but with the *replicating*
  strategies `θ̃ⁱ` (`p_t · θ̃ⁱ_t = (1/q⁰_t) ∑_{s^τ ≻ sᵗ} q⁰ (cⁱ − yⁱ)`). The book's statement with
  the given `θ` is false: the date-0 transversality condition (13.21) allows a zero-cost position
  that is a bubble on one branch and a Ponzi scheme on another (`theorem_13_5_1_counterexample`
  in `RDCounter`). The bound on `p_t · θ̃ⁱ_t` is the book's scaling argument
  (`rd_impatience_bound`), applied to the Arrow–Debreu problem (ii).
* **Theorem 13.5.1, "only if"** (`theorem_13_5_1_onlyIf`), for the discounted expected utility
  (13.1) with differentiable concave `uⁱ` and consumption bounded away from zero (the book's
  sketch uses separation and Mackey continuity, citing Magill and Quinzii): the Euler equations
  give a common state price process `q⁰ = βᵗ Pr u′(c)/u′(c₀)` in `L¹`, the bounded limits give the
  transversality condition, and concavity gives optimality in the Arrow–Debreu budget set.
* `rd_budget_binds`: with strictly increasing utility the budget constraints bind at an optimum.
* `rd_pv_eq`: the equality version of (13.19).
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S J ι : Type*} [Fintype S] [Fintype J] [Fintype ι]

/-- A Radner equilibrium with nonbinding bounded borrowing constraints (zero initial holdings). -/
def rd_RadnerBCnb (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (p f : List S → J → ℝ)
    (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ) : Prop :=
  ∃ Bbar : ι → List S → ℝ, (∀ i, rd_Bdd (Bbar i)) ∧ (∀ i h, 0 ≤ Bbar i h) ∧
    rd_RadnerBC U y (fun _ => 0) p f Bbar c θ ∧ ∀ i h, -Bbar i h < p h ⬝ᵥ θ i h

/-- A Radner equilibrium with nonbinding bounded debt constraints (zero initial holdings). -/
def rd_RadnerDCnb (U : ι → (List S → ℝ) → ℝ) (y : ι → List S → ℝ) (p f : List S → J → ℝ)
    (c : ι → List S → ℝ) (θ : ι → List S → J → ℝ) : Prop :=
  ∃ Dbar : ι → List S → ℝ, (∀ i, rd_Bdd (Dbar i)) ∧ (∀ i h, 0 ≤ Dbar i h) ∧
    rd_RadnerDC U y (fun _ => 0) p f Dbar c θ ∧ ∀ i h s, -Dbar i (s :: h) < f (s :: h) ⬝ᵥ θ i h

omit [Fintype J] [Fintype S] in
/-- The scaled-down plan of the proof of Theorem 13.5.1: `cₜ + (1 − α) Vₜ` at `sᵗ` and `α c` on
the strict successors. -/
theorem rd_scaled_plan_le [DecidableEq S] (c ybar : List S → ℝ) (α V : ℝ) (h : List S)
    (hV : ybar h ≤ (1 - α) * V) (g : List S) :
    rd_impPlan c ybar 1 α h g ≤
      (if g = h then c h + (1 - α) * V else if h <:+ g then α * c g else c g) := by
  simp only [rd_impPlan]
  split_ifs <;> linarith

/-- The book's bound from the uniform lower bound on impatience (Miao, pp. 437–438), in the
Arrow–Debreu problem: if `cⁱ` maximises an increasing `Uⁱ` over `L^∞₊` subject to (13.5) with
`q⁰ ∈ L¹`, `cⁱ ≥ 0` and `yⁱ ≥ 0` bounded, and `α` is given by Assumption 13.5.1 for `κ = 1`,
then the value `Vₜ = (1/q⁰ₜ) ∑_{s^τ ≻ sᵗ} q⁰ (cⁱ − yⁱ)` satisfies `(1 − α) Vₜ < ȳₜ`. -/
theorem rd_impatience_bound [DecidableEq S] {U : (List S → ℝ) → ℝ} (hU : rd_Mono U)
    {ybar : List S → ℝ} (hy0 : ∀ g, 0 ≤ ybar g) {q y c : List S → ℝ} (hq : ∀ h, 0 < q h)
    (hL : rd_L1 q) (hyb : rd_LinfPos y) (hc : rd_LinfPos c)
    (hopt : rd_SolvesC U (fun c' => rd_LinfPos c' ∧ rd_ADBudget q y c') c)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hA : ∀ h, U c < U (rd_impPlan c ybar 1 α h)) (hybb : rd_Bdd ybar) (h : List S) :
    (1 - α) * (rd_W q (fun g => c g - y g) h / q h) < ybar h := by
  by_contra hcon
  push Not at hcon
  set V := rd_W q (fun g => c g - y g) h / q h
  set ĉ : List S → ℝ := fun g => if g = h then c h + (1 - α) * V else if h <:+ g then α * c g
    else c g
  obtain ⟨⟨M, hM⟩, hc0⟩ := hc
  have hĉ : rd_LinfPos ĉ := by
    refine ⟨⟨M + |(1 - α) * V|, fun g => ?_⟩, fun g => ?_⟩
    · simp only [ĉ]
      split_ifs with h1 h2
      · subst h1
        exact (abs_add_le _ _).trans (add_le_add (hM _) le_rfl)
      · rw [abs_mul, abs_of_pos hα0]
        nlinarith [hM g, abs_nonneg (c g), abs_nonneg ((1 - α) * V)]
      · linarith [hM g, abs_nonneg ((1 - α) * V)]
    · simp only [ĉ]
      split_ifs with h1
      · subst h1
        linarith [hc0 g, hy0 g]
      · exact mul_nonneg hα0.le (hc0 g)
      · exact hc0 g
  have hplan : rd_LinfPos (rd_impPlan c ybar 1 α h) := by
    obtain ⟨Yb, hYb⟩ := hybb
    refine ⟨⟨M + Yb, fun g => ?_⟩, fun g => ?_⟩
    · simp only [rd_impPlan]
      split_ifs with h1
      · subst h1
        rw [one_mul]
        exact (abs_add_le _ _).trans (add_le_add (hM _) (hYb _))
      · rw [abs_mul, abs_of_pos hα0]
        nlinarith [hM g, abs_nonneg (c g), abs_nonneg (ybar g), hYb g]
      · linarith [hM g, (abs_nonneg _).trans (hYb g)]
    · simp only [rd_impPlan]
      split_ifs
      · linarith [hc0 h, hy0 h]
      · exact mul_nonneg hα0.le (hc0 g)
      · exact hc0 g
  have hle : U (rd_impPlan c ybar 1 α h) ≤ U ĉ :=
    hU _ _ hplan hĉ (rd_scaled_plan_le c ybar α V h hcon)
  -- `ĉ` is affordable
  have hcb : rd_Bdd c := ⟨M, hM⟩
  have hxs : Summable fun t => rd_dsum (fun g => |q g * (c g - y g)|) [] t :=
    rd_L1_mul_abs hL (rd_bdd_sub hcb hyb.1)
  have hbud : rd_ADBudget q y ĉ := by
    have hbc := (hopt.1).2
    rw [rd_ADBudget] at hbc ⊢
    set G : List S → ℝ := fun g => q g * (ĉ g - c g)
    have hGs : Summable fun t => rd_dsum (fun g => |G g|) [] t :=
      rd_L1_mul_abs hL (rd_bdd_sub hĉ.1 hcb)
    have hsplit : ∑' t, rd_dsum (fun g => q g * ĉ g) [] t =
        ∑' t, rd_dsum (fun g => q g * c g) [] t + ∑' t, rd_dsum G [] t := by
      rw [← Summable.tsum_add (rd_L1_mul hL hcb)
        (Summable.of_norm_bounded hGs fun t => by
          rw [Real.norm_eq_abs]; exact rd_abs_dsum_le _ _ _)]
      refine tsum_congr fun t => ?_
      rw [← rd_dsum_add]
      exact rd_dsum_congr (fun g => by simp only [G]; ring) _ _
    have hGsupp : ∀ g, ¬ h <:+ g → G g = 0 := by
      intro g hg
      have hne : g ≠ h := by
        rintro rfl
        exact hg List.suffix_rfl
      simp [G, ĉ, hne, hg]
    have hGsum : Summable fun t => rd_dsum G [] t :=
      Summable.of_norm_bounded hGs fun t => by
        rw [Real.norm_eq_abs]; exact rd_abs_dsum_le _ _ _
    rw [rd_tsum_subtree hGsupp hGsum, (rd_summable_subtree hGs h).tsum_eq_zero_add,
      rd_dsum_zero] at hsplit
    have hGh : G h = (1 - α) * rd_W q (fun g => c g - y g) h := by
      simp only [G, ĉ, ↓reduceIte, V]
      field_simp [(hq h).ne']
      ring
    have hGj : ∀ j, rd_dsum G h (j + 1) = -(1 - α) * rd_dsum (fun g => q g * c g) h (j + 1) := by
      intro j
      rw [← rd_dsum_const_mul]
      unfold rd_dsum
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [rd_mem_paths] at hl
      have hne : l ++ h ≠ h := fun e => by
        have := congrArg List.length e
        simp only [List.length_append] at this
        omega
      simp only [G, ĉ, hne, ↓reduceIte, List.suffix_append]
      ring
    have hcs := rd_summable_subtree (rd_L1_mul_abs hL hcb) h
    have hys := rd_summable_subtree (rd_L1_mul_abs hL hyb.1) h
    have hW : rd_W q (fun g => c g - y g) h = ∑' j, rd_dsum (fun g => q g * c g) h (j + 1) -
        ∑' j, rd_dsum (fun g => q g * y g) h (j + 1) := by
      rw [rd_W, ← Summable.tsum_sub ((summable_nat_add_iff 1).2 hcs)
        ((summable_nat_add_iff 1).2 hys)]
      refine tsum_congr fun j => ?_
      rw [← rd_dsum_sub]
      exact rd_dsum_congr (fun g => by ring) _ _
    have hrest : ∑' j, rd_dsum G h (j + 1) =
        -(1 - α) * ∑' j, rd_dsum (fun g => q g * c g) h (j + 1) := by
      simp only [hGj]
      exact tsum_mul_left
    have hy0' : 0 ≤ ∑' j, rd_dsum (fun g => q g * y g) h (j + 1) :=
      tsum_nonneg fun j => rd_dsum_nonneg (fun g => mul_nonneg (hq g).le (hyb.2 g)) _ _
    rw [hGh, hrest, hW] at hsplit
    nlinarith
  have hfin := hopt.2 ĉ ⟨hĉ, hbud⟩
  linarith [hA h]

/-- **Theorem 13.5.1, "if"** (Miao, pp. 435–438), corrected. Suppose markets are complete (rank
`S` at every node), utilities are increasing and satisfy Assumption 13.5.1 on `[0, ȳ]`,
endowments are bounded and nonnegative, assets are in zero supply and `θⁱ_{−1} = 0`. If
`(c, θ, π, p)` is a competitive equilibrium with transversality condition, then `(c, θ̃, p)` is a
Radner equilibrium with nonbinding bounded borrowing constraints, and also one with nonbinding
bounded debt constraints, where `θ̃ⁱ` is the replicating strategy of `cⁱ − yⁱ`. -/
theorem theorem_13_5_1_if [DecidableEq S] (T : RDTree S) {U : ι → (List S → ℝ) → ℝ}
    (hU : ∀ i, rd_Mono (U i)) {y : ι → List S → ℝ} (hy : ∀ i, rd_LinfPos (y i))
    (hA : ∀ i, rd_Assumption1351 (U i) fun g => ∑ k, y k g) {f : List S → J → ℝ}
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) {c : ι → List S → ℝ}
    {θ : ι → List S → J → ℝ} {pd : List S → ℝ} {p : List S → J → ℝ}
    (hE : rd_CETVC T U y (fun _ => 0) f c θ pd p) :
    rd_RadnerBCnb U y p f c (fun i => rd_repl f (fun g => pd g * T.Pr g) fun g => c i g - y i g) ∧
      rd_RadnerDCnb U y p f c
        (fun i => rd_repl f (fun g => pd g * T.Pr g) fun g => c i g - y i g) := by
  classical
  obtain ⟨hc, hL, hpd, -, -, -, hii, hsp, hclear, -⟩ := hE
  set q : List S → ℝ := fun g => pd g * T.Pr g
  have hq : ∀ h, 0 < q h := fun h => mul_pos (hpd h) (T.pos h)
  set θ' : ι → List S → J → ℝ := fun i => rd_repl f q fun g => c i g - y i g
  have hii' : ∀ i, rd_SolvesC (U i) (fun c' => rd_LinfPos c' ∧ rd_ADBudget q (y i) c') (c i) := by
    intro i
    simpa [rd_ADBudget] using hii i
  have hAD : ∀ i, rd_ADBudget q (y i) (c i) := fun i => (hii' i).1.2
  have hrb := fun i => rd_repl_budget hsp hL hrank (hc i).1 (hy i).1 (hAD i)
  set ybar : List S → ℝ := fun g => ∑ k, y k g
  have hy0 : ∀ g, 0 ≤ ybar g := fun g => Finset.sum_nonneg fun k _ => (hy k).2 g
  choose My hMy using fun i => (hy i).1
  set Y := ∑ k, |My k|
  have hyY : ∀ g, ybar g ≤ Y := fun g => Finset.sum_le_sum fun k _ =>
    (le_abs_self _).trans ((hMy k g).trans (le_abs_self _))
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hybb : rd_Bdd ybar := ⟨Y, fun g => by rw [abs_of_nonneg (hy0 g)]; exact hyY g⟩
  have hcy : ∀ i g, c i g ≤ ybar g := by
    intro i g
    rw [show ybar g = ∑ k, c k g from (hclear g).symm]
    exact Finset.single_le_sum (f := fun k => c k g) (fun k _ => (hc k).2 g) (Finset.mem_univ i)
  choose α hα0 hα1 hαA using fun i => hA i 1 one_pos
  have hval : ∀ i h, p h ⬝ᵥ θ' i h = rd_W q (fun g => c i g - y i g) h / q h := by
    intro i h
    rw [← rd_repl_value hsp hrank (rd_L1_mul_abs hL (rd_bdd_sub (hc i).1 (hy i).1)) h,
      mul_div_cancel_left₀ _ (hq h).ne']
  have hup : ∀ i h, p h ⬝ᵥ θ' i h < Y / (1 - α i) := by
    intro i h
    have := rd_impatience_bound (hU i) hy0 hq hL (hy i) (hc i) (hii' i) (hα0 i) (hα1 i)
      (fun h => hαA i h (c i) (hc i) (hcy i)) hybb h
    rw [← hval] at this
    have h1 : 0 < 1 - α i := by linarith [hα1 i]
    rw [lt_div_iff₀ h1]
    linarith [hyY h]
  set Bsum := ∑ k, Y / (1 - α k)
  have hUb0 : ∀ k, 0 ≤ Y / (1 - α k) := fun k => div_nonneg hY0 (by linarith [hα1 k])
  have hsum0 : ∀ h, ∑ k, p h ⬝ᵥ θ' k h = 0 := by
    intro h
    rw [← dotProduct_sum]
    have := rd_repl_sum_zero f hL (fun i => (hc i).1) (fun i => (hy i).1) hclear h
    simp only [θ', ← Finset.sum_apply] at this ⊢
    rw [show (∑ k, rd_repl f q fun g => c k g - y k g) h = 0 by simpa using this]
    simp
  have hlow : ∀ i h, -Bsum ≤ p h ⬝ᵥ θ' i h := by
    intro i h
    have := hsum0 h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
    have hle : ∑ k ∈ Finset.univ.erase i, p h ⬝ᵥ θ' k h ≤ Bsum :=
      (Finset.sum_le_sum fun k _ => (hup k h).le).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun k _ _ => hUb0 k)
    linarith
  have hBs0 : 0 ≤ Bsum := Finset.sum_nonneg fun k _ => hUb0 k
  have hθsum : ∀ h, ∑ i, θ' i h = ∑ _i : ι, (0 : J → ℝ) := by
    intro h
    rw [Finset.sum_const_zero]
    exact rd_repl_sum_zero f hL (fun i => (hc i).1) (fun i => (hy i).1) hclear h
  have hgoods : ∀ h, ∑ i, c i h = ∑ i, y i h + (rd_fz p f h - p h) ⬝ᵥ ∑ _i : ι, (0 : J → ℝ) := by
    intro h
    simp [hclear h]
  have hyB : ∀ i h, y i h ≤ Y := fun i h => (le_abs_self _).trans ((hMy i h).trans
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |My k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ i))))
  refine ⟨⟨fun _ _ => Bsum + 1, fun _ => ⟨|Bsum + 1|, fun _ => le_rfl⟩, fun _ _ => by linarith,
    ⟨fun i => ⟨⟨hc i, (hrb i).1, fun h => by linarith [hlow i h]⟩, fun c' θ'' ⟨hc', hB', hθ''⟩ =>
      (hii' i).2 c' ⟨hc', by
        have := rd_AD_of_BC hsp hL hB' (Bbar := fun _ => Bsum + 1)
          ⟨|Bsum + 1|, fun _ => le_rfl⟩ hθ'' hc'.1 (hy i).1
        simpa [rd_ADBudget] using this⟩⟩, hgoods, hθsum⟩,
    fun i h => by linarith [hlow i h]⟩,
    ⟨fun _ _ => Bsum + Y + 1, fun _ => ⟨|Bsum + Y + 1|, fun _ => le_rfl⟩, fun _ _ => by linarith,
    ⟨fun i => ⟨⟨hc i, (hrb i).1, fun h s => ?_⟩, fun c' θ'' ⟨hc', hB', hθ''⟩ =>
      (hii' i).2 c' ⟨hc', by
        have := rd_AD_of_DC hsp hL hB' (Dbar := fun _ => Bsum + Y + 1)
          ⟨|Bsum + Y + 1|, fun _ => le_rfl⟩ hθ'' hc'.1 (hy i).1
        simpa [rd_ADBudget] using this⟩⟩, hgoods, hθsum⟩, fun i h s => ?_⟩⟩
  · have e := (hrb i).2.2 s h
    have := hlow i (s :: h)
    linarith [(hc i).2 (s :: h), hyB i (s :: h)]
  · have e := (hrb i).2.2 s h
    have := hlow i (s :: h)
    linarith [(hc i).2 (s :: h), hyB i (s :: h)]

omit [Fintype S] in
/-- With strictly increasing utility the budget constraints (13.11) bind at an optimum. -/
theorem rd_budget_binds {U : (List S → ℝ) → ℝ} (hU : rd_StrictIncr U)
    {p f : List S → J → ℝ} {y : List S → ℝ} {θm1 : J → ℝ} {Θa : Set (List S → J → ℝ)}
    {c : List S → ℝ} {θ : List S → J → ℝ} (hsol : rd_Solves U (rd_SeqFeas p f y θm1 Θa) c θ) :
    rd_BudgetEq p f y θm1 c θ := by
  classical
  intro h
  obtain ⟨⟨⟨M, hM⟩, hc0⟩, hB, hΘ⟩ := hsol.1
  by_contra hne
  have hlt : c h + p h ⬝ᵥ θ h < rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h :=
    lt_of_le_of_ne (hB h) hne
  set e := rd_fz p f h ⬝ᵥ rd_prev θ θm1 h + y h - (c h + p h ⬝ᵥ θ h)
  have he : 0 < e := by simp only [e]; linarith
  set c' : List S → ℝ := fun g => c g + if g = h then e else 0
  have hc' : rd_SeqFeas p f y θm1 Θa c' θ := by
    refine ⟨⟨⟨M + e, fun g => ?_⟩, fun g => ?_⟩, fun g => ?_, hΘ⟩
    · simp only [c']
      refine (abs_add_le _ _).trans (add_le_add (hM g) ?_)
      split_ifs <;> simp [abs_of_pos he, he.le]
    · simp only [c']
      split_ifs <;> linarith [hc0 g]
    · simp only [c']
      split_ifs with hg
      · subst hg
        simp only [e]
        linarith
      · linarith [hB g]
  have := hU c c' hsol.1.1 hc'.1 (fun g => by simp only [c']; split_ifs <;> linarith) (by
    intro hcc
    have := congrFun hcc h
    simp only [c', ↓reduceIte] at this
    linarith)
  exact absurd (hsol.2 c' θ hc') (not_le.2 this)

/-- (13.19) with equality when the budget constraints bind. -/
theorem rd_pv_eq {p f : List S → J → ℝ} {q : List S → ℝ} (hq : rd_StatePrice p f q)
    {y : List S → ℝ} {θm1 : J → ℝ} {c : List S → ℝ} {θ : List S → J → ℝ}
    (hB : rd_BudgetEq p f y θm1 c θ) (h : List S) (T : ℕ) :
    ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * c g) h j +
        rd_dsum (fun g => q g * (p g ⬝ᵥ θ g)) h T =
      q h * (rd_fz p f h ⬝ᵥ rd_prev θ θm1 h) +
        ∑ j ∈ Finset.range (T + 1), rd_dsum (fun g => q g * y g) h j := by
  have hpt : ∀ g, q g * c g + q g * (p g ⬝ᵥ θ g) =
      q g * (rd_fz p f g ⬝ᵥ rd_prev θ θm1 g) + q g * y g := by
    intro g
    rw [← mul_add, ← mul_add, hB g]
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
    have hstep := congrArg (fun F => F) (rd_dsum_congr hpt h (T + 1))
    rw [rd_dsum_add, rd_dsum_add] at hstep
    linarith

/-- The gradient inequality makes the marginal utility decreasing. -/
theorem rd_gradIneq_antitone {u u' : ℝ → ℝ} (hg : rd_GradIneq u u') {x z : ℝ} (hx : 0 < x)
    (hxz : x ≤ z) : u' z ≤ u' x := by
  have hz : 0 < z := lt_of_lt_of_le hx hxz
  have h1 := hg x hx z hz.le
  have h2 := hg z hz x hx.le
  rcases lt_or_eq_of_le hxz with hlt | heq
  · nlinarith
  · rw [heq]

/-- **Theorem 13.5.1, "only if"** (Miao, pp. 435, 438–439), for discounted expected utility
(13.1): with `uⁱ` strictly increasing, differentiable with positive derivative and concave
(gradient inequality), complete markets, `p ∈ (L^∞₊)ᴶ`, consumption bounded away from zero, zero
supply and `θⁱ_{−1} = 0`, a Radner equilibrium with nonbinding bounded borrowing constraints is a
competitive equilibrium with transversality condition, with the state price deflator
`π = q⁰/Pr`, `q⁰ = βᵗ Pr u′(c)/u′(c₀)` of any agent. -/
theorem theorem_13_5_1_onlyIf [Nonempty ι] (T : RDTree S)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {u u' : ι → ℝ → ℝ}
    (hu : ∀ i, StrictMonoOn (u i) (Set.Ici 0)) (hd : ∀ i x, 0 < x → HasDerivAt (u i) (u' i x) x)
    (hu'pos : ∀ i x, 0 < x → 0 < u' i x) (hgrad : ∀ i, rd_GradIneq (u i) (u' i))
    {y : ι → List S → ℝ} (hy : ∀ i, rd_LinfPos (y i)) {p f : List S → J → ℝ}
    (hrank : ∀ h, (rd_payoffMatrix f h).rank = Fintype.card S) (hp0 : ∀ h j, 0 ≤ p h j)
    (hpb : ∀ j, rd_Bdd fun h => p h j) {c : ι → List S → ℝ} {θ : ι → List S → J → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hcε : ∀ i h, ε ≤ c i h)
    (hR : rd_RadnerBCnb (fun i => rd_EU T β (u i)) y p f c θ) :
    ∃ pd, rd_CETVC T (fun i => rd_EU T β (u i)) y (fun _ => 0) f c θ pd p := by
  classical
  obtain ⟨Bbar, hBb, -, ⟨hsol, hgoods, hθsum⟩, hslack⟩ := hR
  have hcpos : ∀ i h, 0 < c i h := fun i h => lt_of_lt_of_le hε (hcε i h)
  -- Euler equations for every agent at every node
  have heul : ∀ i h j, rd_Phi T β (u' i) p f (c i) h (Pi.single j 1) = 0 := by
    intro i h j
    refine rd_euler_eq T hβ0 hβ1 (hu i).monotoneOn (hd i) (hsol i) h (hcpos i h)
      (fun s => hcpos i (s :: h)) _ ?_
    have : Tendsto (fun e : ℝ => p h ⬝ᵥ θ i h + e * (p h ⬝ᵥ Pi.single j 1)) (𝓝 0)
        (𝓝 (p h ⬝ᵥ θ i h)) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (p h ⬝ᵥ Pi.single j 1)).const_add _
    filter_upwards [this.eventually (lt_mem_nhds (hslack i h))] with e he
    exact rd_BC_feas (hsol i).1.2.2 h _ e he.le
  set qi : ι → List S → ℝ := fun i h => β ^ h.length * T.Pr h * u' i (c i h) / u' i (c i [])
  have hqi : ∀ i, rd_StatePrice p f (qi i) := fun i =>
    rd_statePrice_of_euler T hβ0 (fun h => hu'pos i _ (hcpos i h)) (heul i)
  have hqi0 : ∀ i, qi i [] = 1 := fun i => by
    simp [qi, T.root, (hu'pos i _ (hcpos i [])).ne']
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  set q := qi i0
  have hq := hqi i0
  have hqeq : ∀ i, qi i = q := fun i => funext fun h => by
    rw [rd_statePrice_unique hrank hq (hqi i) h, hqi0, hqi0 i0, div_one, one_mul]
  -- `q⁰ ∈ L¹`
  set K := u' i0 ε / u' i0 (c i0 [])
  have hL : rd_L1 q := by
    refine Summable.of_nonneg_of_le (fun t => rd_dsum_nonneg (fun g => abs_nonneg _) _ _)
      (fun t => ?_) ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left K)
    have : ∀ g, |q g| ≤ β ^ g.length * (K * T.Pr g) := by
      intro g
      have hpos := (hq.1 g)
      rw [abs_of_pos hpos]
      simp only [qi, K]
      have hm := rd_gradIneq_antitone (hgrad i0) hε (hcε i0 g)
      have hu0 := hu'pos i0 _ (hcpos i0 [])
      rw [div_le_iff₀ hu0]
      have : β ^ g.length * T.Pr g * u' i0 (c i0 g) ≤ β ^ g.length * T.Pr g * u' i0 ε :=
        mul_le_mul_of_nonneg_left hm (mul_nonneg (pow_nonneg hβ0.le _) (T.pos g).le)
      calc β ^ g.length * T.Pr g * u' i0 (c i0 g) ≤ β ^ g.length * T.Pr g * u' i0 ε := this
        _ = β ^ g.length * (u' i0 ε / u' i0 (c i0 []) * T.Pr g) * u' i0 (c i0 []) := by
          field_simp
    refine (rd_dsum_mono this [] t).trans ?_
    rw [rd_dsum_pow, rd_dsum_const_mul, rd_dsum_Pr, T.root]
    linarith
  -- bounded values `p · θⁱ`
  choose Bm hBm using hBb
  set Bsum := ∑ k, |Bm k|
  have hpθ : ∀ i, rd_Bdd fun h => p h ⬝ᵥ θ i h := by
    intro i
    refine ⟨Bsum, fun h => abs_le.2 ⟨?_, ?_⟩⟩
    · have h1 := hslack i h
      have h2 := (le_abs_self _).trans ((hBm i h).trans (le_abs_self (Bm i)))
      have h3 := Finset.single_le_sum (f := fun k => |Bm k|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ i)
      linarith
    · have hs : ∑ k, p h ⬝ᵥ θ k h = 0 := by
        rw [← dotProduct_sum]
        have := hθsum h
        simp only [Finset.sum_const_zero] at this
        rw [show ∑ k, θ k h = 0 by simpa using this, dotProduct_zero]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
      have : ∀ k, -|Bm k| ≤ p h ⬝ᵥ θ k h := fun k => by
        have h1 := hslack k h
        have h2 := (le_abs_self _).trans ((hBm k h).trans (le_abs_self (Bm k)))
        linarith
      have hle : -∑ k ∈ Finset.univ.erase i, |Bm k| ≤ ∑ k ∈ Finset.univ.erase i,
          p h ⬝ᵥ θ k h := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun k _ => this k
      have hsub : ∑ k ∈ Finset.univ.erase i, |Bm k| ≤ Bsum :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun k _ _ => abs_nonneg _
      linarith
  have hTVC : ∀ i, rd_TVC q p (θ i) := fun i => rd_L1_mul_tendsto hL (hpθ i)
  have hBeq : ∀ i, rd_BudgetEq p f (y i) 0 (c i) (θ i) := fun i =>
    rd_budget_binds (rd_eq_13_1 T hβ0 hβ1 (hu i)) (hsol i)
  -- the Arrow–Debreu budget holds with equality
  have hADeq : ∀ i, ∑' t, rd_dsum (fun g => q g * c i g) [] t =
      ∑' t, rd_dsum (fun g => q g * y i g) [] t := by
    intro i
    have hcs := rd_L1_mul hL (hsol i).1.1.1
    have hys := rd_L1_mul hL (hy i).1
    have hA := hcs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have hY := (hys.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub (hTVC i)
    rw [sub_zero] at hY
    refine tendsto_nhds_unique hA (hY.congr fun T' => ?_)
    have := rd_pv_eq hq (hBeq i) [] T'
    simp only [rd_fz, rd_prev, dotProduct_zero, mul_zero, zero_add, Function.comp_apply] at this ⊢
    linarith
  -- optimality in the Arrow–Debreu budget set
  have hii : ∀ i, ∀ c', rd_LinfPos c' → rd_ADBudget q (y i) c' →
      rd_EU T β (u i) c' ≤ rd_EU T β (u i) (c i) := by
    intro i c' hc' hb
    have hu0 := hu'pos i _ (hcpos i [])
    have hcs := rd_L1_mul hL (hsol i).1.1.1
    have hc's := rd_L1_mul hL hc'.1
    refine rd_suff_core T hβ0 hβ1 (hu i).monotoneOn (hgrad i) (hsol i).1.1 hc' (hcpos i)
      (τ := fun n => u' i (c i []) * ∑ t ∈ Finset.range (n + 1),
        (rd_dsum (fun g => q g * c' g) [] t - rd_dsum (fun g => q g * c i g) [] t))
      (L := u' i (c i []) * (∑' t, rd_dsum (fun g => q g * c' g) [] t -
        ∑' t, rd_dsum (fun g => q g * c i g) [] t))
      ?_ ?_ fun n => le_of_eq ?_
    · refine Tendsto.const_mul _ ?_
      rw [← Summable.tsum_sub hc's hcs]
      exact (hc's.sub hcs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    · rw [rd_ADBudget, ← hADeq i] at hb
      exact mul_nonpos_of_nonneg_of_nonpos hu0.le (by linarith)
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← rd_dsum_sub, ← rd_dsum_const_mul]
      refine rd_dsum_congr (fun g => ?_) _ _
      rw [← hqeq i]
      simp only [qi]
      field_simp
  refine ⟨fun g => q g / T.Pr g, ?_⟩
  have hqpd : ∀ g, q g / T.Pr g * T.Pr g = q g := fun g => div_mul_cancel₀ _ (T.pos g).ne'
  simp only [rd_CETVC, hqpd]
  refine ⟨fun i => (hsol i).1.1, hL, fun h => div_pos (hq.1 h) (T.pos h), hp0, hpb,
    fun i => ⟨⟨(hsol i).1.1, (hsol i).1.2.1, hTVC i⟩, fun c' θ' ⟨hc', hB, hT⟩ => hii i c' hc' ?_⟩,
    fun i => ⟨⟨(hsol i).1.1, ?_⟩, fun c' ⟨hc', hb⟩ => hii i c' hc' ?_⟩, hq, fun h => ?_, hθsum⟩
  · have := eq_13_22 hq hB hT (rd_L1_mul hL hc'.1) (rd_L1_mul hL (hy i).1)
    simpa [rd_ADBudget] using this
  · rw [hADeq i]
    simp
  · simpa [rd_ADBudget] using hb
  · simpa using hgoods h

end Miao.CompleteMarkets
