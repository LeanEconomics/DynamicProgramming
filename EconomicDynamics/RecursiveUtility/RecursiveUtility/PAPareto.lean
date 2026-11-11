/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PALongRunRiskPricing
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.Convex.Function

/-!
# Pareto optimality with recursive utility: the utility possibility set

Miao, *Economic Dynamics in Discrete Time*, §20.5 (pp. 729–731), Lemma 20.5.1, Definition 20.5.1,
the Negishi problem (20.58)–(20.59) and Lemma 20.5.2.

The economy: `n` agents, consumption plans in `ι → ℝ` (`ι` finite: the dates and states of a
finite event tree, or the continuation plans from date 1 on), consumption set `C = {c ≥ 0}`,
aggregate endowment `e ≥ 0`, utilities `U i : (ι → ℝ) → ℝ`. The feasible allocations are
`pa_feasible e` (`C(e)`), the plain utility possibility set is `pa_U0 U e`
(`U₀(e) = {(U¹(c¹), …, Uⁿ(cⁿ)) : c ∈ C(e)}`), and its comprehensive hull is `pa_U0bar U e`
(`{u : u ≤ U(c) for some c ∈ C(e)}`). The simplex `Δⁿ` is `pa_simplex n`, and the value of the
Negishi problem (20.58) is `pa_Vhat`.

* Definition 20.5.1: `definition_20_5_1` (Pareto optimality, `pa_ParetoOptimal`).
* Lemma 20.5.1: the hull is convex, closed and satisfies free disposal when the utilities are
  concave and continuous (`lemma_20_5_1`); the plain set is closed (compact) but does not
  satisfy free disposal in general (`lemma_20_5_1_plain_closed`,
  `lemma_20_5_1_counterexample`).
* Lemma 20.5.2: for a convex, closed, comprehensive, nonempty set with bounded support values,
  `v ∈ U ↔ ∀ θ ∈ Δⁿ, θ · v ≤ V̂(θ)` (`pa_mem_iff_support`, proved by the separation theorem as
  in the text), and so `v ∈ Ū₀(e) ↔ min_θ (V̂(e, θ) − θ · v) ≥ 0` (`lemma_20_5_2`); with the
  plain set `U₀(e)` the "if" direction fails (`lemma_20_5_2_counterexample`).

Departure (see `docs/PA-corrections.md`): Lemma 20.5.1's free disposal, and hence Lemma 20.5.2,
hold for the comprehensive set `Ū₀(e) = U₀(e) − ℝⁿ₊`, not for `U₀(e)` itself; Lemma 20.5.1 also
needs concave, continuous utilities (convexity, closedness), which the text leaves implicit.
-/

namespace Miao.RecursiveUtility

open Set
open scoped Pointwise

/-- The simplex of Pareto weights `Δⁿ = {θ ∈ ℝⁿ₊ : ∑ θᵢ = 1}` (Miao, p. 730). -/
def pa_simplex (n : ℕ) : Set (Fin n → ℝ) := {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1}

/-- The weighted sum `θ · v = ∑ θᵢ vᵢ`. -/
def pa_dot {n : ℕ} (θ v : Fin n → ℝ) : ℝ := ∑ i, θ i * v i

/-- The support value `V̂(θ) = sup_{z ∈ U} θ · z` of a utility possibility set. -/
noncomputable def pa_Vhat {n : ℕ} (U : Set (Fin n → ℝ)) (θ : Fin n → ℝ) : ℝ :=
  sSup ((pa_dot θ) '' U)

/-- Free disposal: `u ≤ u' ∈ U ⟹ u ∈ U` (Miao, Lemma 20.5.1). -/
def pa_FreeDisposal {n : ℕ} (U : Set (Fin n → ℝ)) : Prop := ∀ u u', u ≤ u' → u' ∈ U → u ∈ U

/-- The feasible allocations `C(e) = {(c¹, …, cⁿ) : cⁱ ≥ 0, ∑ cⁱ ≤ e}` (Miao, p. 730). -/
def pa_feasible {n : ℕ} {ι : Type*} (e : ι → ℝ) : Set (Fin n → ι → ℝ) :=
  {c | (∀ i, 0 ≤ c i) ∧ ∑ i, c i ≤ e}

/-- The utility profile `(U¹(c¹), …, Uⁿ(cⁿ))`. -/
def pa_uvec {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (c : Fin n → ι → ℝ) : Fin n → ℝ :=
  fun i => U i (c i)

/-- The utility possibility set `U₀(e)` (Miao, p. 730). -/
def pa_U0 {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (e : ι → ℝ) : Set (Fin n → ℝ) :=
  pa_uvec U '' pa_feasible e

/-- The comprehensive utility possibility set `Ū₀(e) = {u : ∃ c ∈ C(e), u ≤ U(c)}`. -/
def pa_U0bar {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (e : ι → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ c ∈ pa_feasible e, u ≤ pa_uvec U c}

/-- Pareto optimality for an abstract set of feasible allocations and utility functions. -/
def pa_ParetoOptimal {α : Type*} {n : ℕ} (F : Set α) (U : Fin n → α → ℝ) (c : α) : Prop :=
  c ∈ F ∧ ¬ ∃ c' ∈ F, (∀ i, U i c ≤ U i c') ∧ ∃ j, U j c < U j c'

/-- **Definition 20.5.1** (Miao, p. 730). An allocation `c ∈ C(e)` is Pareto optimal iff there
is no feasible `ĉ` with `Uⁱ(ĉⁱ) ≥ Uⁱ(cⁱ)` for all `i` and `Uʲ(ĉʲ) > Uʲ(cʲ)` for some `j`. -/
theorem definition_20_5_1 {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (e : ι → ℝ)
    (c : Fin n → ι → ℝ) :
    pa_ParetoOptimal (pa_feasible e) (fun i c => U i (c i)) c ↔ c ∈ pa_feasible e ∧
      ¬ ∃ ĉ ∈ pa_feasible e, (∀ i, U i (c i) ≤ U i (ĉ i)) ∧ ∃ j, U j (c j) < U j (ĉ j) :=
  Iff.rfl

/-- Miao, (20.58)–(20.59), p. 730: a solution of the Negishi problem with strictly positive
weights is Pareto optimal. -/
theorem pa_negishi_pareto {α : Type*} {n : ℕ} {F : Set α} {U : Fin n → α → ℝ} {θ : Fin n → ℝ}
    (hθ : ∀ i, 0 < θ i) {c : α} (hc : c ∈ F)
    (hmax : ∀ c' ∈ F, ∑ i, θ i * U i c' ≤ ∑ i, θ i * U i c) : pa_ParetoOptimal F U c := by
  refine ⟨hc, ?_⟩
  rintro ⟨c', hc', hle, j, hj⟩
  have : ∑ i, θ i * U i c < ∑ i, θ i * U i c' :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hle i) (hθ i).le)
      ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (hθ j)⟩
  linarith [hmax c' hc']

theorem pa_feasible_isCompact {n : ℕ} {ι : Type*} [Finite ι] (e : ι → ℝ) :
    IsCompact (pa_feasible (n := n) e) := by
  have := Fintype.ofFinite ι
  have hclosed : IsClosed (pa_feasible (n := n) e) := by
    have h1 : IsClosed {c : Fin n → ι → ℝ | ∀ i, 0 ≤ c i} := by
      have : {c : Fin n → ι → ℝ | ∀ i, 0 ≤ c i} = ⋂ i, {c | 0 ≤ c i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {c : Fin n → ι → ℝ | ∑ i, c i ≤ e} :=
      isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_Icc (0 : Fin n → ι → ℝ) (fun _ => e)).subset ?_
  rintro c ⟨h0, hs⟩
  refine ⟨fun i => h0 i, fun i => ?_⟩
  calc c i ≤ ∑ j, c j := Finset.single_le_sum (f := c) (fun j _ => h0 j) (Finset.mem_univ i)
    _ ≤ e := hs

theorem pa_feasible_convex {n : ℕ} {ι : Type*} (e : ι → ℝ) :
    Convex ℝ (pa_feasible (n := n) e) := by
  rintro c ⟨hc0, hcs⟩ d ⟨hd0, hds⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply]
    exact add_nonneg (smul_nonneg ha (hc0 i)) (smul_nonneg hb (hd0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum]
    calc a • ∑ i, c i + b • ∑ i, d i ≤ a • e + b • e :=
          add_le_add (smul_le_smul_of_nonneg_left hcs ha) (smul_le_smul_of_nonneg_left hds hb)
      _ = e := by rw [← add_smul, hab, one_smul]

theorem pa_zero_feasible {n : ℕ} {ι : Type*} {e : ι → ℝ} (he : 0 ≤ e) :
    (0 : Fin n → ι → ℝ) ∈ pa_feasible e :=
  ⟨fun _ => le_rfl, by simpa using he⟩

/-- Miao, Lemma 20.5.1, p. 730: the plain utility possibility set `U₀(e)` is closed (indeed
compact) when the utilities are continuous. -/
theorem lemma_20_5_1_plain_closed {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hU : ∀ i, Continuous (U i)) (e : ι → ℝ) : IsCompact (pa_U0 U e) :=
  (pa_feasible_isCompact e).image (continuous_pi fun i => (hU i).comp (continuous_apply i))

/-- For `θ ≥ 0` and continuous utilities the support values of `Ū₀(e)` are bounded above. -/
theorem pa_U0bar_bdd {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hU : ∀ i, Continuous (U i)) (e : ι → ℝ) {θ : Fin n → ℝ} (hθ : ∀ i, 0 ≤ θ i) :
    BddAbove ((pa_dot θ) '' pa_U0bar U e) := by
  obtain ⟨M, hM⟩ := ((pa_feasible_isCompact (n := n) e).image
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hU i).comp (continuous_apply i)) :
      Continuous fun c : Fin n → ι → ℝ => ∑ i, θ i * U i (c i))).isBounded.bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨u, ⟨c, hc, hu⟩, rfl⟩
  calc pa_dot θ u ≤ ∑ i, θ i * U i (c i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu i) (hθ i)
    _ ≤ M := hM ⟨c, hc, rfl⟩

/-- **Lemma 20.5.1** (Miao, p. 730), corrected. If each `Uⁱ` is concave on `C` and continuous and
`e ≥ 0`, the comprehensive utility possibility set `Ū₀(e)` is convex, closed, satisfies free
disposal and is nonempty, and each `θ ≥ 0` has bounded support values on it. -/
theorem lemma_20_5_1 {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (U i)) (hU : ∀ i, Continuous (U i)) {e : ι → ℝ}
    (he : 0 ≤ e) :
    Convex ℝ (pa_U0bar U e) ∧ IsClosed (pa_U0bar U e) ∧ pa_FreeDisposal (pa_U0bar U e) ∧
      (pa_U0bar U e).Nonempty ∧
      ∀ θ : Fin n → ℝ, (∀ i, 0 ≤ θ i) → BddAbove ((pa_dot θ) '' pa_U0bar U e) := by
  refine ⟨?_, ?_, ?_, ⟨_, 0, pa_zero_feasible he, le_rfl⟩, ?_⟩
  · rintro u ⟨c, hc, hu⟩ v ⟨d, hd, hv⟩ a b ha hb hab
    refine ⟨a • c + b • d, pa_feasible_convex e hc hd ha hb hab, fun i => ?_⟩
    have hci : c i ∈ Set.Ici (0 : ι → ℝ) := hc.1 i
    have hdi : d i ∈ Set.Ici (0 : ι → ℝ) := hd.1 i
    have := (hconc i).2 hci hdi ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pa_uvec] at this ⊢
    calc a * u i + b * v i ≤ a * U i (c i) + b * U i (d i) :=
          add_le_add (mul_le_mul_of_nonneg_left (hu i) ha) (mul_le_mul_of_nonneg_left (hv i) hb)
      _ ≤ U i (a • c i + b • d i) := this
  · have hK := (pa_feasible_isCompact (n := n) e).image
      (continuous_pi fun i => (hU i).comp (continuous_apply i) : Continuous (pa_uvec U))
    have hN : IsClosed {d : Fin n → ℝ | d ≤ 0} := isClosed_le continuous_id continuous_const
    have heq : pa_U0bar U e = pa_uvec U '' pa_feasible e + {d : Fin n → ℝ | d ≤ 0} := by
      ext u
      simp only [pa_U0bar, Set.mem_ofPred_eq, Set.mem_add, Set.mem_image]
      constructor
      · rintro ⟨c, hc, hu⟩
        exact ⟨pa_uvec U c, ⟨c, hc, rfl⟩, u - pa_uvec U c, fun i => by
          simp only [Pi.sub_apply, Pi.zero_apply]; linarith [hu i], by abel⟩
      · rintro ⟨_, ⟨c, hc, rfl⟩, d, hd, rfl⟩
        exact ⟨c, hc, fun i => by
          have := hd i
          simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
          linarith⟩
    rw [heq]
    exact hN.add_left_of_isCompact hK
  · rintro u u' huu' ⟨c, hc, hu'⟩
    exact ⟨c, hc, huu'.trans hu'⟩
  · exact fun θ hθ => pa_U0bar_bdd hU e hθ

/-- Miao, Lemma 20.5.1 (counterexample to the printed statement): the plain set `U₀(e)` need
not satisfy free disposal. One agent, one good, `U(c) = c`, `e = 1`: `U₀(e) = [0, 1]` and
`−1 ≤ 0 ∈ U₀(e)` but `−1 ∉ U₀(e)`. -/
theorem lemma_20_5_1_counterexample :
    ¬ pa_FreeDisposal (pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1)) := by
  intro h
  have h0 : (0 : Fin 1 → ℝ) ∈ pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1) :=
    ⟨0, ⟨fun _ => le_rfl, fun _ => by simp⟩, rfl⟩
  obtain ⟨c, hc, hcu⟩ := h (fun _ => -1) 0 (fun _ => by norm_num) h0
  have h1 := congrFun hcu 0
  have h2 := hc.1 0 ()
  simp only [pa_uvec, Pi.zero_apply] at h1 h2
  linarith

/-- The linear functional of a continuous linear map on `ℝⁿ` in coordinates. -/
theorem pa_clm_apply {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (z : Fin n → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  have := f.toLinearMap.pi_apply_eq_sum_univ z
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- Miao, Lemma 20.5.2 (p. 731), abstract form, proved by the separation theorem as in the text:
for a convex, closed, nonempty set `U ⊆ ℝⁿ` with free disposal whose support values are
bounded, `v ∈ U` iff `θ · v ≤ V̂(θ)` for every `θ ∈ Δⁿ`. -/
theorem pa_mem_iff_support {n : ℕ} {U : Set (Fin n → ℝ)} (hconv : Convex ℝ U)
    (hclosed : IsClosed U) (hfd : pa_FreeDisposal U) (hne : U.Nonempty)
    (hbdd : ∀ θ ∈ pa_simplex n, BddAbove ((pa_dot θ) '' U)) (v : Fin n → ℝ) :
    v ∈ U ↔ ∀ θ ∈ pa_simplex n, pa_dot θ v ≤ pa_Vhat U θ := by
  constructor
  · intro hv θ hθ
    exact le_csSup (hbdd θ hθ) ⟨v, hv, rfl⟩
  · intro hsupp
    by_contra hv
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hconv hclosed hv
    set w : Fin n → ℝ := fun i => f (Pi.single i 1) with hw
    have hf : ∀ z, f z = pa_dot w z := fun z => by rw [pa_clm_apply]; rfl
    obtain ⟨a, ha⟩ := hne
    -- free disposal forces `w ≥ 0`
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i
      by_contra hi
      push Not at hi
      have hmem : ∀ t : ℝ, 0 ≤ t → a - t • Pi.single i 1 ∈ U := fun t ht =>
        hfd _ a (fun j => by
          by_cases hj : j = i
          · subst hj; simp [ht]
          · simp [hj]) ha
      have key := hfu _ (hmem ((u - f a) / (-w i) + 1) (by
        have : 0 < u - f a := by linarith [hfu a ha]
        have : 0 < -w i := by linarith
        positivity))
      rw [map_sub, map_smul, smul_eq_mul] at key
      have hpos : 0 < -w i := by linarith
      have : ((u - f a) / -w i + 1) * f (Pi.single i 1) = -(u - f a) + w i := by
        rw [show f (Pi.single i 1) = w i from rfl]
        have hwne : w i ≠ 0 := by linarith
        field_simp
      linarith
    have hW : 0 < ∑ i, w i := by
      rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw0 i).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ i, w i = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw0 j).1 h.symm i (Finset.mem_univ i)
        have h1 := hfu a ha
        rw [hf, pa_dot] at h1 hux
        simp only [hz, zero_mul, Finset.sum_const_zero] at h1 hux
        linarith
    set θ : Fin n → ℝ := fun i => w i / ∑ j, w j with hθdef
    have hθ : θ ∈ pa_simplex n := ⟨fun i => div_nonneg (hw0 i) hW.le, by
      simp only [hθdef, ← Finset.sum_div, div_self hW.ne']⟩
    have hdot : ∀ z, pa_dot θ z = f z / ∑ j, w j := fun z => by
      rw [hf, pa_dot, pa_dot, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hθdef]; ring
    have hsup : pa_Vhat U θ ≤ u / ∑ j, w j := by
      unfold pa_Vhat
      refine csSup_le ⟨_, a, ha, rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [hdot]
      exact (div_le_div_iff_of_pos_right hW).2 (hfu z hz).le
    have := hsupp θ hθ
    rw [hdot] at this
    have : f v / ∑ j, w j ≤ u / ∑ j, w j := this.trans hsup
    rw [div_le_div_iff_of_pos_right hW] at this
    linarith

/-- **Lemma 20.5.2** (Miao, p. 731), corrected to the comprehensive set: with concave, continuous
utilities and `e ≥ 0`, `v ∈ Ū₀(e)` iff `min_{θ ∈ Δⁿ} (V̂(e, θ) − θ · v) ≥ 0`, i.e.
`θ · v ≤ V̂(e, θ)` for all `θ ∈ Δⁿ`, where `V̂(e, θ)` is the value of (20.58). -/
theorem lemma_20_5_2 {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (U i)) (hU : ∀ i, Continuous (U i)) {e : ι → ℝ}
    (he : 0 ≤ e) (v : Fin n → ℝ) :
    v ∈ pa_U0bar U e ↔ ∀ θ ∈ pa_simplex n, 0 ≤ pa_Vhat (pa_U0bar U e) θ - pa_dot θ v := by
  obtain ⟨hc, hcl, hfd, hne, hb⟩ := lemma_20_5_1 hconc hU he
  rw [pa_mem_iff_support hc hcl hfd hne (fun θ hθ => hb θ hθ.1)]
  exact forall₂_congr fun θ _ => sub_nonneg.symm

/-- The support value of the comprehensive set is the Negishi value (20.58):
`V̂(θ) = sup_{c ∈ C(e)} ∑ θᵢ Uⁱ(cⁱ)` for `θ ≥ 0`. -/
theorem pa_Vhat_U0bar {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hU : ∀ i, Continuous (U i)) {e : ι → ℝ} (he : 0 ≤ e) {θ : Fin n → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) :
    pa_Vhat (pa_U0bar U e) θ = sSup ((fun c => ∑ i, θ i * U i (c i)) '' pa_feasible e) := by
  have hcpt := (pa_feasible_isCompact (n := n) e).image
    (continuous_finsetSum _ fun i _ => continuous_const.mul ((hU i).comp (continuous_apply i)) :
      Continuous fun c : Fin n → ι → ℝ => ∑ i, θ i * U i (c i))
  have hbdd := hcpt.isBounded.bddAbove
  unfold pa_Vhat
  apply le_antisymm
  · refine csSup_le ⟨_, pa_uvec U 0, ⟨0, pa_zero_feasible he, le_rfl⟩, rfl⟩ ?_
    rintro _ ⟨u, ⟨c, hc, hu⟩, rfl⟩
    exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu i) (hθ i)).trans
      (le_csSup hbdd ⟨c, hc, rfl⟩)
  · refine csSup_le ⟨_, 0, pa_zero_feasible he, rfl⟩ ?_
    rintro _ ⟨c, hc, rfl⟩
    exact le_csSup (pa_U0bar_bdd hU e hθ) ⟨pa_uvec U c, ⟨c, hc, le_rfl⟩, rfl⟩

/-- Miao, Lemma 20.5.2 (counterexample to the printed statement with the plain set `U₀(e)`):
one agent, `U(c) = c`, `e = 1`; `v = −1` satisfies (20.62) but `v ∉ U₀(e)`. -/
theorem lemma_20_5_2_counterexample :
    (∀ θ ∈ pa_simplex 1, pa_dot θ (fun _ => -1) ≤
        pa_Vhat (pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1)) θ) ∧
      (fun _ => -1) ∉ pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1) := by
  have h0 : (0 : Fin 1 → ℝ) ∈ pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1) :=
    ⟨0, ⟨fun _ => le_rfl, fun _ => by simp⟩, rfl⟩
  have hbdd : ∀ θ : Fin 1 → ℝ, BddAbove ((pa_dot θ) ''
      pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1)) := fun θ =>
    ((lemma_20_5_1_plain_closed (fun _ => continuous_apply ()) _).image
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).isBounded
      |>.bddAbove
  refine ⟨fun θ hθ => ?_, ?_⟩
  · have hθ0 := hθ.1 0
    refine le_trans ?_ (le_csSup (hbdd θ) ⟨0, h0, rfl⟩)
    simp only [pa_dot, Fin.sum_univ_one, Pi.zero_apply, mul_zero]
    linarith
  · rintro ⟨c, hc, hcu⟩
    have h1 := congrFun hcu 0
    have h2 := hc.1 0 ()
    simp only [pa_uvec, Pi.zero_apply] at h1 h2
    linarith

end Miao.RecursiveUtility
