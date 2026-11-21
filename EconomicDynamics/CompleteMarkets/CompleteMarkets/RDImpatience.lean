/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.RDEx134
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Assumption 13.5.1: uniform lower bound on impatience

Miao, §13.5, p. 437.

* `rd_impPlan c ȳ κ α sᵗ`: the plan that adds `κ ȳ_t(sᵗ)` at `sᵗ` and scales consumption by `α`
  at every strict successor `s^τ | sᵗ`.
* `rd_Assumption1351Printed`: Assumption 13.5.1 as printed (for every `κ > 0` some `α ∈ (0, 1)`,
  independent of the node, makes the modified plan strictly preferred for *every* consumption
  plan). The book's remark that discounted expected utility satisfies it is false as printed:
  with `u = √·` the gain `√(c + κ) − √c` vanishes for large `c` while the loss
  `(1 − √α) √c` grows (`assumption_13_5_1_printed_fails`).
* `rd_Assumption1351`: the assumption for consumption plans in the order interval `[0, ȳ]`
  (Magill–Quinzii's formulation, and all that the proof of Theorem 13.5.1 uses). Continuous,
  strictly increasing discounted expected utility satisfies it when `ȳ` is bounded and bounded
  away from zero (`assumption_13_5_1`), by compactness of `[0, sup ȳ]`.
* `rd_tsum_subtree`, `rd_EU_sub_subtree`: sums of processes supported on the subtree of a node.
-/

namespace Miao.CompleteMarkets

open Filter Topology

variable {S : Type*} [Fintype S]

omit [Fintype S] in
/-- The plan of Assumption 13.5.1: `cₜ(sᵗ) + κ ȳₜ(sᵗ)` at `sᵗ`, `α c_τ(s^τ)` for `s^τ | sᵗ`,
`τ > t`, and unchanged elsewhere. -/
def rd_impPlan [DecidableEq S] (c ybar : List S → ℝ) (κ α : ℝ) (h : List S) : List S → ℝ :=
  fun g => if g = h then c h + κ * ybar h else if h <:+ g then α * c g else c g

/-- Assumption 13.5.1 as printed (Miao, p. 437), for every consumption plan in `L^∞₊`. -/
def rd_Assumption1351Printed [DecidableEq S] (U : (List S → ℝ) → ℝ) (ybar : List S → ℝ) :
    Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∀ h c, rd_LinfPos c → U c < U (rd_impPlan c ybar κ α h)

/-- **Assumption 13.5.1** (uniform lower bound on impatience; Miao, p. 437), for consumption
plans in the order interval `[0, ȳ]`. -/
def rd_Assumption1351 [DecidableEq S] (U : (List S → ℝ) → ℝ) (ybar : List S → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∀ h c, rd_LinfPos c → (∀ g, c g ≤ ybar g) → U c < U (rd_impPlan c ybar κ α h)

omit [Fintype S] in
/-- The book's form implies the corrected one. -/
theorem rd_assumption1351_of_printed [DecidableEq S] {U : (List S → ℝ) → ℝ}
    {ybar : List S → ℝ} (hU : rd_Assumption1351Printed U ybar) : rd_Assumption1351 U ybar := by
  intro κ hκ
  obtain ⟨α, h0, h1, H⟩ := hU κ hκ
  exact ⟨α, h0, h1, fun h c hc _ => H h c hc⟩

/-- A process supported on the subtree of `sᵗ` has total sum equal to its subtree sum. -/
theorem rd_tsum_subtree {G : List S → ℝ} {h : List S} (hG : ∀ g, ¬ h <:+ g → G g = 0)
    (hs : Summable fun t => rd_dsum G [] t) : ∑' t, rd_dsum G [] t = ∑' j, rd_dsum G h j := by
  rw [← hs.sum_add_tsum_nat_add h.length,
    Finset.sum_eq_zero fun t ht => rd_dsum_subtree_early hG (Finset.mem_range.1 ht), zero_add]
  exact tsum_congr fun j => by rw [add_comm]; exact rd_dsum_subtree hG j

/-- At distance `j` from `sᵗ`, a factor `β^{len}` is the constant `β^{t+j}`. -/
theorem rd_dsum_pow_at (β : ℝ) (F : List S → ℝ) (h : List S) (j : ℕ) :
    rd_dsum (fun g => β ^ g.length * F g) h j = β ^ (h.length + j) * rd_dsum F h j := by
  rw [rd_dsum, rd_dsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [rd_mem_paths] at hl
  simp [hl, add_comm]

/-- The change in (13.1) from a change of consumption on the subtree of `sᵗ`. -/
theorem rd_EU_sub_subtree (T : RDTree S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) {c c' : List S → ℝ} (hc : rd_LinfPos c)
    (hc' : rd_LinfPos c') (h : List S) (hsupp : ∀ g, ¬ h <:+ g → c' g = c g) :
    rd_EU T β u c' - rd_EU T β u c =
      ∑' j, β ^ (h.length + j) * rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h j := by
  obtain ⟨K, hK⟩ := rd_abs_u_le hu hc
  obtain ⟨K', hK'⟩ := rd_abs_u_le hu hc'
  have hs := (rd_EU_summable T hβ0 hβ1 u hK').sub (rd_EU_summable T hβ0 hβ1 u hK)
  rw [rd_EU, rd_EU, ← Summable.tsum_sub (rd_EU_summable T hβ0 hβ1 u hK')
    (rd_EU_summable T hβ0 hβ1 u hK)]
  set G : List S → ℝ := fun g => β ^ g.length * (T.Pr g * (u (c' g) - u (c g)))
  have e : ∀ t, β ^ t * rd_dsum (fun g => T.Pr g * u (c' g)) [] t -
      β ^ t * rd_dsum (fun g => T.Pr g * u (c g)) [] t = rd_dsum G [] t := by
    intro t
    rw [← mul_sub, ← rd_dsum_sub, ← rd_dsum_pow]
    exact rd_dsum_congr (fun g => by ring) _ _
  simp only [e] at hs ⊢
  rw [rd_tsum_subtree (fun g hg => by simp [G, hsupp g hg]) hs]
  exact tsum_congr fun j => rd_dsum_pow_at β _ h j

/-- **Assumption 13.5.1**, the remark "This assumption is satisfied by the continuous discounted
expected utility" (Miao, p. 437), for plans in `[0, ȳ]`: if `u` is continuous and strictly
increasing on `[0, ∞)`, `0 < β < 1` and `m ≤ ȳ ≤ Y` with `m > 0`, then (13.1) satisfies the
uniform lower bound on impatience. -/
theorem assumption_13_5_1 [DecidableEq S] (T : RDTree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {u : ℝ → ℝ} (hu : StrictMonoOn u (Set.Ici 0)) (hcont : ContinuousOn u (Set.Ici 0))
    {ybar : List S → ℝ} {m Y : ℝ} (hm : 0 < m) (hym : ∀ g, m ≤ ybar g)
    (hyY : ∀ g, ybar g ≤ Y) : rd_Assumption1351 (rd_EU T β u) ybar := by
  intro κ hκ
  set K := Set.Icc (0 : ℝ) Y
  have hY : m ≤ Y := (hym []).trans (hyY [])
  have hKc : IsCompact K := isCompact_Icc
  have hKsub : K ⊆ Set.Ici 0 := fun x hx => hx.1
  -- the minimal gain on `[0, Y]`
  have hγc : ContinuousOn (fun x => u (x + κ * m) - u x) K := by
    refine ContinuousOn.sub ?_ (hcont.mono hKsub)
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun x hx => ?_
    exact Set.mem_Ici.2 (by have := hx.1; positivity)
  obtain ⟨x0, hx0, hmin⟩ := hKc.exists_isMinOn ⟨0, le_rfl, by linarith⟩ hγc
  set g0 := u (x0 + κ * m) - u x0
  have hg0 : 0 < g0 := by
    have := hu (Set.mem_Ici.2 hx0.1) (Set.mem_Ici.2 (by have := hx0.1; positivity))
      (by linarith [mul_pos hκ hm] : x0 < x0 + κ * m)
    simp only [g0]
    linarith
  -- uniform continuity on `[0, Y]`
  set ε0 := g0 * (1 - β) / (2 * β)
  have hε0 : 0 < ε0 := div_pos (mul_pos hg0 (by linarith)) (by linarith)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hcont.mono hKsub)) ε0 hε0
  set r := min (1 / 2 : ℝ) (δ / (2 * (Y + 1)))
  have hY1 : 0 < Y + 1 := by linarith
  have hr0 : 0 < r := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hrδ : r * Y < δ := by
    have h1 : r ≤ δ / (2 * (Y + 1)) := min_le_right _ _
    have h2 : δ / (2 * (Y + 1)) * Y < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    nlinarith [hm.le.trans hY]
  refine ⟨1 - r, by linarith, by linarith, fun h c hc hcy => ?_⟩
  set c' := rd_impPlan c ybar κ (1 - r) h
  have hc0 := hc.2
  have hcK : ∀ g, c g ∈ K := fun g => ⟨hc0 g, (hcy g).trans (hyY g)⟩
  have hc' : rd_LinfPos c' := by
    obtain ⟨⟨M, hM⟩, -⟩ := hc
    refine ⟨⟨M + κ * Y, fun g => ?_⟩, fun g => ?_⟩
    · simp only [c', rd_impPlan]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM g)
      split_ifs with h1 h2
      · subst h1
        rw [abs_le]
        have := abs_le.1 (hM g)
        constructor <;> nlinarith [hym g, hyY g, hc0 g]
      · rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - r)]
        nlinarith [hM g, abs_nonneg (c g), mul_pos hκ hm]
      · nlinarith [hM g, mul_pos hκ hm]
    · simp only [c', rd_impPlan]
      split_ifs
      · nlinarith [hym h, hc0 h]
      · exact mul_nonneg (by linarith) (hc0 g)
      · exact hc0 g
  have hsupp : ∀ g, ¬ h <:+ g → c' g = c g := by
    intro g hg
    have hne : g ≠ h := by
      rintro rfl
      exact hg List.suffix_rfl
    simp [c', rd_impPlan, hne, hg]
  rw [← sub_pos, rd_EU_sub_subtree T hβ0.le hβ1 hu.monotoneOn hc hc' h hsupp]
  set F : ℕ → ℝ := fun j =>
    β ^ (h.length + j) * rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h j
  have hsF : Summable F := by
    obtain ⟨K1, hK1⟩ := rd_abs_u_le hu.monotoneOn hc
    obtain ⟨K2, hK2⟩ := rd_abs_u_le hu.monotoneOn hc'
    refine Summable.of_norm_bounded (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left
      (β ^ h.length * ((K1 + K2) * T.Pr h)))) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le _), pow_add]
    have := rd_abs_dsum_Pr_le T (X := fun g => u (c' g) - u (c g)) (K := K1 + K2)
      (fun g => (abs_sub _ _).trans (by linarith [hK1 g, hK2 g])) h j
    calc β ^ h.length * β ^ j * |rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h j|
        ≤ β ^ h.length * β ^ j * ((K1 + K2) * T.Pr h) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = β ^ h.length * ((K1 + K2) * T.Pr h) * β ^ j := by ring
  rw [hsF.tsum_eq_zero_add]
  -- the gain at `sᵗ`
  have hF0 : β ^ h.length * T.Pr h * g0 ≤ F 0 := by
    simp only [F, add_zero, rd_dsum_zero]
    have hval : c' h = c h + κ * ybar h := by simp [c', rd_impPlan]
    rw [hval]
    have h1 : u (c h + κ * m) ≤ u (c h + κ * ybar h) :=
      hu.monotoneOn (Set.mem_Ici.2 (by have := hc0 h; positivity))
        (Set.mem_Ici.2 (by have := hc0 h; nlinarith [hym h])) (by nlinarith [hym h])
    have h2 := hmin (hcK h)
    simp only [Set.mem_ofPred_eq] at h2
    have : g0 ≤ u (c h + κ * ybar h) - u (c h) := by
      simp only [g0]
      linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (pow_nonneg hβ0.le h.length)
      (T.pos h).le)
    linarith
  -- the losses at the strict successors
  have hFs : ∀ j, -(β ^ h.length * T.Pr h * ε0 * β ^ (j + 1)) ≤ F (j + 1) := by
    intro j
    simp only [F]
    have hd : -(ε0 * T.Pr h) ≤ rd_dsum (fun g => T.Pr g * (u (c' g) - u (c g))) h (j + 1) := by
      rw [← rd_dsum_Pr T h (j + 1), ← rd_dsum_const_mul, ← rd_dsum_neg]
      unfold rd_dsum
      refine Finset.sum_le_sum fun l hl => ?_
      rw [rd_mem_paths] at hl
      have hne : l ++ h ≠ h := fun e => by
        have := congrArg List.length e
        simp only [List.length_append] at this
        omega
      have hval : c' (l ++ h) = (1 - r) * c (l ++ h) := by
        simp [c', rd_impPlan, hne, List.suffix_append]
      dsimp only
      rw [hval]
      have hmem : (1 - r) * c (l ++ h) ∈ K :=
        ⟨mul_nonneg (by linarith) (hc0 _), by nlinarith [(hcK (l ++ h)).2, hc0 (l ++ h)]⟩
      have hdist : dist ((1 - r) * c (l ++ h)) (c (l ++ h)) < δ := by
        rw [Real.dist_eq, show (1 - r) * c (l ++ h) - c (l ++ h) = -(r * c (l ++ h)) by ring,
          abs_neg, abs_of_nonneg (mul_nonneg hr0.le (hc0 _))]
        nlinarith [(hcK (l ++ h)).2]
      have := hδu _ hmem _ (hcK _) hdist
      rw [Real.dist_eq, abs_lt] at this
      have hP := (T.pos (l ++ h)).le
      nlinarith [this.1]
    have := mul_le_mul_of_nonneg_left hd (pow_nonneg hβ0.le (h.length + (j + 1)))
    calc -(β ^ h.length * T.Pr h * ε0 * β ^ (j + 1))
        = β ^ (h.length + (j + 1)) * -(ε0 * T.Pr h) := by ring
      _ ≤ _ := this
  have hgeo : ∑' j, -(β ^ h.length * T.Pr h * ε0 * β ^ (j + 1)) =
      -(β ^ h.length * T.Pr h * ε0 * (β / (1 - β))) := by
    rw [tsum_neg, tsum_mul_left]
    congr 2
    simp only [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]
    ring
  have hsum := Summable.tsum_le_tsum hFs
    (by
      have := ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left
        (β ^ h.length * T.Pr h * ε0 * β)).neg
      refine this.congr fun j => ?_
      ring)
    ((summable_nat_add_iff 1).2 hsF)
  rw [hgeo] at hsum
  have hkey : β ^ h.length * T.Pr h * ε0 * (β / (1 - β)) = β ^ h.length * T.Pr h * (g0 / 2) := by
    have hb1 : 1 - β ≠ 0 := by linarith
    simp only [ε0]
    field_simp
  rw [hkey] at hsum
  have hpos : 0 < β ^ h.length * T.Pr h * (g0 / 2) :=
    mul_pos (mul_pos (pow_pos hβ0 _) (T.pos h)) (by linarith)
  nlinarith

/-- Miao, p. 437 (correction): Assumption 13.5.1 as printed fails for continuous discounted
expected utility. In a deterministic economy with `β = 1/2`, `u = √·` and `ȳ ≡ 1`, for `κ = 1`
and any `α ∈ (0, 1)` the constant plan `c ≡ (1 − √α)⁻²` is weakly preferred to the modified
plan at the root. -/
theorem assumption_13_5_1_printed_fails :
    ¬ rd_Assumption1351Printed (rd_EU (rd_uniformTree Unit) (1 / 2) Real.sqrt) fun _ => 1 := by
  intro H
  obtain ⟨α, hα0, hα1, hα⟩ := H 1 one_pos
  set a := Real.sqrt α
  have ha0 : 0 < a := Real.sqrt_pos.2 hα0
  have ha1 : a < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hα0.le hα1
  set M := (1 / (1 - a)) ^ 2
  have hM0 : 0 < M := by positivity
  have h1a : 0 < 1 - a := by linarith
  have hsM : Real.sqrt M = 1 / (1 - a) := Real.sqrt_sq (by positivity)
  set c : List Unit → ℝ := fun _ => M
  have hc : rd_LinfPos c := ⟨⟨M, fun _ => by simp [c, abs_of_pos hM0]⟩, fun _ => hM0.le⟩
  have hlt := hα [] c hc
  set c' := rd_impPlan c (fun _ => 1) 1 α []
  have hc' : rd_LinfPos c' := by
    refine ⟨⟨M + 1, fun g => ?_⟩, fun g => ?_⟩
    · simp only [c', rd_impPlan, c, List.nil_suffix, ↓reduceIte]
      split_ifs
      · rw [abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_pos (mul_pos hα0 hM0)]
        nlinarith
    · simp only [c', rd_impPlan, c, List.nil_suffix, ↓reduceIte]
      split_ifs <;> positivity
  have hsupp : ∀ g, ¬ ([] : List Unit) <:+ g → c' g = c g := fun g hg =>
    absurd (List.nil_suffix) hg
  set T := rd_uniformTree Unit
  have hd := rd_EU_sub_subtree T (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun x _ y _ hxy => Real.sqrt_le_sqrt hxy) hc hc' [] hsupp
  set G : List Unit → ℝ := fun g => T.Pr g * (Real.sqrt (c' g) - Real.sqrt (c g))
  have hsαM : Real.sqrt (α * M) = a / (1 - a) := by
    rw [Real.sqrt_mul hα0.le, hsM]
    ring
  have hG0 : rd_dsum G [] 0 = Real.sqrt (M + 1) - Real.sqrt M := by
    simp [rd_dsum_zero, G, c', rd_impPlan, c, T.root]
  have hGs : ∀ j, rd_dsum G [] (j + 1) = -1 := by
    intro j
    have : rd_dsum G [] (j + 1) = rd_dsum (fun g => -1 * T.Pr g) [] (j + 1) := by
      unfold rd_dsum
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [rd_mem_paths] at hl
      have hne : l ++ [] ≠ [] := by
        intro e
        rw [List.append_nil] at e
        rw [e] at hl
        simp at hl
      simp only [G, c', rd_impPlan, c, hne, ↓reduceIte, List.nil_suffix, hsαM, hsM]
      field_simp
      ring
    rw [this, rd_dsum_const_mul, rd_dsum_Pr, T.root, mul_one]
  simp only [List.length_nil, zero_add] at hd
  have hsF : Summable fun j => (1 / 2 : ℝ) ^ j * rd_dsum G [] j := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun j => (1 / 2 : ℝ) ^ (j + 1) * rd_dsum G [] (j + 1)) =
        fun j => -((1 / 2) * (1 / 2 : ℝ) ^ j) := by
      funext j
      rw [hGs]
      simp [pow_succ]
      ring
    rw [this]
    exact ((summable_geometric_two).mul_left (1 / 2)).neg
  rw [hsF.tsum_eq_zero_add] at hd
  have hrest : ∑' j, (1 / 2 : ℝ) ^ (j + 1) * rd_dsum G [] (j + 1) = -1 := by
    have : (fun j => (1 / 2 : ℝ) ^ (j + 1) * rd_dsum G [] (j + 1)) =
        fun j => -((1 / 2) * (1 / 2 : ℝ) ^ j) := by
      funext j
      rw [hGs]
      simp [pow_succ]
      ring
    rw [this, tsum_neg, tsum_mul_left, tsum_geometric_two]
    norm_num
  rw [hrest] at hd
  simp only [pow_zero, one_mul, hG0] at hd
  have hle : Real.sqrt (M + 1) ≤ Real.sqrt M + 1 := by
    rw [Real.sqrt_le_left]
    · nlinarith [Real.sq_sqrt hM0.le, Real.sqrt_nonneg M]
    · positivity
  have : rd_EU T (1 / 2) Real.sqrt c' ≤ rd_EU T (1 / 2) Real.sqrt c := by
    linarith
  exact absurd hlt (not_lt.2 this)

end Miao.CompleteMarkets
