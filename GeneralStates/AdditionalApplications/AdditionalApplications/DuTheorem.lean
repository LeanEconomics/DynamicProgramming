/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.BanachLattice
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Module

/-!
# Concavity, convexity and Du's theorem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.1.3 (pp. 131–132).

`E` is a Banach lattice and `V = [a, b]`. An order preserving self-map `S` of `[a, b]` satisfies
*Du's conditions* if either (a) `S` is concave and `Sa ≥ a + ε(b − a)` or (b) `S` is convex and
`Sb ≤ b − ε(b − a)`, for some `ε ∈ (0, 1)`.

* **Theorem 4.1.10 (Du)**: Du's conditions imply global stability on `[a, b]`. The book cites
  Du (1990); the proof here squeezes the orbits of `a` and `b` together at rate `(1 − ε)ᵏ`, and uses
  completeness and the lattice norm.
* **Lemma 4.1.9**: if `Sa − a` (or `b − Sb`) is interior to the positive cone, Du's conditions
  hold.
* **Theorem 4.1.11**: a regular ADP on `[a, b]` whose policy operators satisfy Du's conditions
  satisfies the fundamental optimality properties, with convergence of VFI, OPI and HPI, if
  (a) `E` is countably Dedekind complete, (b) `𝕋` is finite, or (c) the Bellman operator satisfies
  Du's conditions.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E]

/-- `F` is globally stable on `U`: a unique fixed point in `U` attracting every orbit from `U`. -/
def GloballyStableOn (F : E → E) (U : Set E) : Prop :=
  ∃ u ∈ U, F u = u ∧ (∀ w ∈ U, F w = w → w = u) ∧
    ∀ v ∈ U, Tendsto (fun k => F^[k] v) atTop (𝓝 u)

/-- Du's conditions (p. 131) for a self-map `F` of `[a, b]`. -/
def DuConditions (a b : E) (F : E → E) : Prop :=
  (ConcaveOn ℝ (Icc a b) F ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a + ε • (b - a) ≤ F a) ∨
    (ConvexOn ℝ (Icc a b) F ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ F b ≤ b - ε • (b - a))

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] in
/-- Points of `[l, h]` are at most `h − l` apart. -/
theorem abs_sub_le_of_mem_Icc {l h x y : E} (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    |x - y| ≤ h - l := by
  rw [abs]
  refine sup_le (sub_le_sub hx.2 hy.1) ?_
  rw [neg_sub]
  exact sub_le_sub hy.2 hx.1

omit [NormedSpace ℝ E] [PosSMulMono ℝ E] in
theorem norm_sub_le_of_mem_Icc {l h x y : E} (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    ‖x - y‖ ≤ ‖h - l‖ :=
  norm_le_norm_of_abs_le_abs ((abs_sub_le_of_mem_Icc hx hy).trans_eq
    (abs_of_nonneg (sub_nonneg.2 (hx.1.trans hx.2))).symm)

omit [NormedAddCommGroup E] [IsOrderedAddMonoid E] [HasSolidNorm E] [NormedSpace ℝ E]
  [PosSMulMono ℝ E] in
theorem iterate_mem_Icc {a b : E} {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) {v : E} (hv : v ∈ Icc a b) (k : ℕ) :
    F^[k] v ∈ Icc (F^[k] a) (F^[k] b) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hv.1.trans hv.2⟩
  have hb : b ∈ Icc a b := ⟨hv.1.trans hv.2, le_rfl⟩
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
    exact ⟨hmono (hmaps.iterate k ha) (hmaps.iterate k hv) ih.1,
      hmono (hmaps.iterate k hv) (hmaps.iterate k hb) ih.2⟩

variable [CompleteSpace E]

/-- **Theorem 4.1.10 (Du)** (p. 131), concave case: an order preserving concave self-map of
`[a, b]` with `Sa ≥ a + ε(b − a)` for some `ε ∈ (0, 1]` is globally stable on `[a, b]`. -/
theorem du_concave {a b : E} (hab : a ≤ b) {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) (hconc : ConcaveOn ℝ (Icc a b) F) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hFa : a + ε • (b - a) ≤ F a) : GloballyStableOn F (Icc a b) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  set q : ℕ → ℝ := fun k => (1 - ε) ^ k with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => pow_nonneg (by linarith) k
  have hq1 : ∀ k, q k ≤ 1 := fun k => pow_le_one₀ (by linarith) (by linarith)
  -- `Fᵏa ≥ a + (1 − qₖ)(Fᵏb − a)`
  have key : ∀ k, a + (1 - q k) • (F^[k] b - a) ≤ F^[k] a := by
    intro k
    induction k with
    | zero => simp [hq]
    | succ k ih =>
      set w := F^[k] b
      set u := F^[k] a
      have hw := hmaps.iterate k hb
      have hu := hmaps.iterate k ha
      have hFw := (hmaps hw).2
      set z := q k • a + (1 - q k) • w
      have hz : z ∈ Icc a b := (convex_Icc a b) ha hw (hq0 k) (by linarith [hq1 k]) (by ring)
      have hzu : z ≤ u := by
        have : z = a + (1 - q k) • (w - a) := by simp only [z]; module
        rw [this]
        exact ih
      have hqs : q (k + 1) = q k * (1 - ε) := by simp only [hq]; ring
      rw [iterate_succ_apply', iterate_succ_apply', hqs]
      have hid : q k • (a + ε • (b - a)) + (1 - q k) • F w =
          (a + (1 - q k * (1 - ε)) • (F w - a)) + (q k * ε) • (b - F w) := by module
      calc a + (1 - q k * (1 - ε)) • (F w - a)
          ≤ (a + (1 - q k * (1 - ε)) • (F w - a)) + (q k * ε) • (b - F w) :=
            le_add_of_nonneg_right (smul_nonneg (mul_nonneg (hq0 k) hε.le) (sub_nonneg.2 hFw))
        _ = q k • (a + ε • (b - a)) + (1 - q k) • F w := hid.symm
        _ ≤ q k • F a + (1 - q k) • F w :=
            add_le_add (smul_le_smul_of_nonneg_left hFa (hq0 k)) le_rfl
        _ ≤ F z := hconc.2 ha hw (hq0 k) (by linarith [hq1 k]) (by ring)
        _ ≤ F u := hmono hz hu hzu
  -- the orbits of `a` and `b` are `qₖ(b − a)` apart
  have gap : ∀ k, ‖F^[k] b - F^[k] a‖ ≤ q k * ‖b - a‖ := by
    intro k
    have hwb := (hmaps.iterate k hb).2
    have h1 : F^[k] b - F^[k] a ≤ q k • (b - a) := by
      have h2 : F^[k] b - F^[k] a ≤ F^[k] b - (a + (1 - q k) • (F^[k] b - a)) :=
        sub_le_sub le_rfl (key k)
      have h3 : F^[k] b - (a + (1 - q k) • (F^[k] b - a)) = q k • (F^[k] b - a) := by module
      rw [h3] at h2
      exact h2.trans (smul_le_smul_of_nonneg_left (sub_le_sub_right hwb a) (hq0 k))
    have h0 : 0 ≤ F^[k] b - F^[k] a := sub_nonneg.2 (iterate_mem_Icc hmaps hmono ha k).2
    have := norm_le_norm_of_abs_le_abs (a := F^[k] b - F^[k] a) (b := q k • (b - a))
      (by rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _))
    rwa [norm_smul, Real.norm_of_nonneg (hq0 k)] at this
  have hqlim : Tendsto (fun k => q k * ‖b - a‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const
      ‖b - a‖
  have hzero : ∀ x : E, (∀ k, ‖x‖ ≤ q k * ‖b - a‖) → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (ge_of_tendsto' hqlim hx)
  -- points of `[Fᵏa, Fᵏb]` are within `qₖ‖b − a‖` of each other
  have hsq : ∀ k {x y : E}, x ∈ Icc (F^[k] a) (F^[k] b) → y ∈ Icc (F^[k] a) (F^[k] b) →
      ‖x - y‖ ≤ q k * ‖b - a‖ := fun k _ _ hx hy => (norm_sub_le_of_mem_Icc hx hy).trans (gap k)
  have hmem : ∀ k j, F^[k + j] a ∈ Icc (F^[k] a) (F^[k] b) := fun k j => by
    rw [iterate_add_apply]
    exact iterate_mem_Icc hmaps hmono (hmaps.iterate j ha) k
  -- the orbit of `a` is Cauchy
  have hcauchy : CauchySeq fun k => F^[k] a := by
    refine Metric.cauchySeq_iff'.2 fun δ hδ => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hqlim.eventually (gt_mem_nhds hδ))
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [dist_eq_norm]
    exact (hsq N (hmem N j) (iterate_mem_Icc hmaps hmono ha N)).trans_lt (hN N le_rfl)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  have huk : ∀ k, u ∈ Icc (F^[k] a) (F^[k] b) := fun k =>
    isClosed_Icc.mem_of_tendsto (hu.comp (tendsto_add_atTop_nat k))
      (Eventually.of_forall fun j => by
        simp only [Function.comp_apply]
        rw [add_comm]
        exact hmem k j)
  have huI : u ∈ Icc a b := huk 0
  have hfix : F u = u := by
    refine sub_eq_zero.1 (hzero _ fun k => ?_)
    have hFu : F u ∈ Icc (F^[k + 1] a) (F^[k + 1] b) := by
      rw [iterate_succ_apply', iterate_succ_apply']
      exact ⟨hmono (hmaps.iterate k ha) huI (huk k).1, hmono huI (hmaps.iterate k hb) (huk k).2⟩
    have hqk : q (k + 1) ≤ q k := pow_le_pow_of_le_one (by linarith) (by linarith) k.le_succ
    exact (hsq (k + 1) hFu (huk (k + 1))).trans
      (mul_le_mul_of_nonneg_right hqk (norm_nonneg _))
  refine ⟨u, huI, hfix, fun w hw hwfix => sub_eq_zero.1 (hzero _ fun k => ?_), fun v hv => ?_⟩
  · have := iterate_mem_Icc hmaps hmono hw k
    rw [iterate_fixed hwfix] at this
    exact hsq k this (huk k)
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => hsq k (iterate_mem_Icc hmaps hmono hv k) (huk k)) hqlim)

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem neg_mem_Icc_iff' {a b w : E} : -w ∈ Icc a b ↔ w ∈ Icc (-b) (-a) := by
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨neg_le.1 h2, le_neg.1 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_neg.2 h2, neg_le.2 h1⟩

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] [Lattice E]
  [IsOrderedAddMonoid E] in
theorem iterate_reflect (F : E → E) (k : ℕ) (w : E) :
    (fun x => -F (-x))^[k] w = -F^[k] (-w) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, ih, neg_neg]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
/-- Global stability of the reflection `w ↦ −F(−w)` on `[−b, −a]` gives global stability of `F`
on `[a, b]`. -/
theorem globallyStableOn_of_reflect {a b : E} {F : E → E}
    (h : GloballyStableOn (fun w => -F (-w)) (Icc (-b) (-a))) : GloballyStableOn F (Icc a b) := by
  obtain ⟨u, hu, hfix, huniq, hlim⟩ := h
  refine ⟨-u, neg_mem_Icc_iff'.2 hu, ?_, fun w hw hwfix => ?_, fun v hv => ?_⟩
  · have := congrArg Neg.neg hfix
    simpa using this
  · have := huniq (-w) (neg_mem_Icc_iff'.1 (by rwa [neg_neg])) (by simp [hwfix])
    rw [← this, neg_neg]
  · have := (hlim (-v) (neg_mem_Icc_iff'.1 (by rwa [neg_neg]))).neg
    simpa [iterate_reflect] using this

/-- **Theorem 4.1.10 (Du)** (p. 131), convex case: an order preserving convex self-map of `[a, b]`
with `Sb ≤ b − ε(b − a)` for some `ε ∈ (0, 1]` is globally stable on `[a, b]`. -/
theorem du_convex {a b : E} (hab : a ≤ b) {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) (hconv : ConvexOn ℝ (Icc a b) F) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hFb : F b ≤ b - ε • (b - a)) : GloballyStableOn F (Icc a b) := by
  have hmem : ∀ w ∈ Icc (-b) (-a), -w ∈ Icc a b := fun w hw => neg_mem_Icc_iff'.2 hw
  refine globallyStableOn_of_reflect (du_concave (neg_le_neg hab) ?_ ?_ ?_ hε hε1 ?_)
  · intro w hw
    exact neg_mem_Icc_iff'.1 (by rw [neg_neg]; exact hmaps (hmem w hw))
  · intro u hu w hw huw
    exact neg_le_neg (hmono (hmem w hw) (hmem u hu) (neg_le_neg huw))
  · refine ⟨convex_Icc _ _, fun u hu w hw s t hs ht hst => ?_⟩
    have := hconv.2 (hmem u hu) (hmem w hw) hs ht hst
    have h2 : -(s • u + t • w) = s • -u + t • -w := by rw [neg_add, smul_neg, smul_neg]
    change s • -F (-u) + t • -F (-w) ≤ -F (-(s • u + t • w))
    rw [h2, smul_neg, smul_neg, ← neg_add]
    exact neg_le_neg this
  · rw [neg_neg]
    have : -b + ε • (-a - -b) = -(b - ε • (b - a)) := by module
    rw [this]
    exact neg_le_neg hFb

/-- **Theorem 4.1.10 (Du)** (p. 131): an order preserving self-map of `[a, b]` satisfying Du's
conditions is globally stable on `[a, b]`. -/
theorem theorem_4_1_10 {a b : E} (hab : a ≤ b) {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) (hdu : DuConditions a b F) : GloballyStableOn F (Icc a b) := by
  rcases hdu with ⟨hconc, ε, hε, hε1, hFa⟩ | ⟨hconv, ε, hε, hε1, hFb⟩
  · exact du_concave hab hmaps hmono hconc hε hε1.le hFa
  · exact du_convex hab hmaps hmono hconv hε hε1.le hFb

omit [CompleteSpace E] [HasSolidNorm E] [PosSMulMono ℝ E] in
/-- **Lemma 4.1.9** (p. 131), (a'): if `Sa − a` is interior to the positive cone, then
`Sa ≥ a + ε(b − a)` for some `ε ∈ (0, 1)`. -/
theorem lemma_4_1_9_concave {a b : E} {F : E → E} (h : F a - a ∈ interior {x : E | 0 ≤ x}) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a + ε • (b - a) ≤ F a := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h)
  set ε := min (1 / 2) (r / (2 * (‖b - a‖ + 1)))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨ε, hε, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  have hmem : F a - a - ε • (b - a) ∈ Metric.ball (F a - a) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hε.le]
    calc ε * ‖b - a‖ ≤ r / (2 * (‖b - a‖ + 1)) * ‖b - a‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ < r := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (b - a)]
  have h0 : 0 ≤ F a - a - ε • (b - a) := hball hmem
  rw [sub_sub, sub_nonneg] at h0
  exact h0

omit [CompleteSpace E] [HasSolidNorm E] [PosSMulMono ℝ E] in
/-- **Lemma 4.1.9** (p. 131), (b'): if `b − Sb` is interior to the positive cone, then
`Sb ≤ b − ε(b − a)` for some `ε ∈ (0, 1)`. -/
theorem lemma_4_1_9_convex {a b : E} {F : E → E} (h : b - F b ∈ interior {x : E | 0 ≤ x}) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ F b ≤ b - ε • (b - a) := by
  obtain ⟨ε, hε, hε1, hle⟩ := lemma_4_1_9_concave (a := F b) (b := F b + (b - a))
    (F := fun _ => b) h
  refine ⟨ε, hε, hε1, ?_⟩
  have : F b + ε • (F b + (b - a) - F b) = F b + ε • (b - a) := by abel_nf
  rw [this] at hle
  rw [le_sub_iff_add_le]
  exact hle

omit [CompleteSpace E] [HasSolidNorm E] [PosSMulMono ℝ E] in
/-- **Lemma 4.1.9** (p. 131): an order preserving `S` that is concave with `a ≪ Sa`, or convex with
`Sb ≪ b`, satisfies Du's conditions. -/
theorem lemma_4_1_9 {a b : E} {F : E → E}
    (h : (ConcaveOn ℝ (Icc a b) F ∧ F a - a ∈ interior {x : E | 0 ≤ x}) ∨
      (ConvexOn ℝ (Icc a b) F ∧ b - F b ∈ interior {x : E | 0 ≤ x})) : DuConditions a b F := by
  rcases h with ⟨hc, hi⟩ | ⟨hc, hi⟩
  · exact Or.inl ⟨hc, lemma_4_1_9_concave hi⟩
  · exact Or.inr ⟨hc, lemma_4_1_9_convex hi⟩

/-! ### Optimality theory on order intervals -/

open scoped Classical in
/-- A self-map of the subtype `[a, b]`, extended by the identity to `E`. -/
noncomputable def extendIcc {a b : E} (S : Icc a b → Icc a b) (v : E) : E :=
  if h : v ∈ Icc a b then (S ⟨v, h⟩ : E) else v

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E] [IsOrderedAddMonoid E] in
theorem extendIcc_apply {a b : E} (S : Icc a b → Icc a b) (v : Icc a b) :
    extendIcc S v = S v := by
  simp [extendIcc, v.2]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E] [IsOrderedAddMonoid E] in
theorem extendIcc_iterate {a b : E} (S : Icc a b → Icc a b) (k : ℕ) (v : Icc a b) :
    (extendIcc S)^[k] v = (S^[k] v : E) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, extendIcc_apply, ih, iterate_succ_apply]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [IsOrderedAddMonoid E] in
/-- A globally stable extension makes the subtype map globally stable. -/
theorem globallyStable_of_extendIcc {a b : E} {S : Icc a b → Icc a b}
    (h : GloballyStableOn (extendIcc S) (Icc a b)) : GloballyStable S := by
  obtain ⟨u, hu, hfix, huniq, hlim⟩ := h
  refine ⟨⟨u, hu⟩, Subtype.ext ?_, fun w hw => Subtype.ext (huniq w w.2 ?_), fun v => ?_⟩
  · rw [← extendIcc_apply S ⟨u, hu⟩]
    exact hfix
  · rw [extendIcc_apply, hw]
  · refine tendsto_subtype_rng.2 ?_
    simp only [← extendIcc_iterate]
    exact hlim v v.2

/-- **Theorem 4.1.10** for a self-map of the subtype `[a, b]`. -/
theorem theorem_4_1_10_subtype {a b : E} (hab : a ≤ b) {S : Icc a b → Icc a b}
    (hS : Monotone S) (hdu : DuConditions a b (extendIcc S)) : GloballyStable S := by
  refine globallyStable_of_extendIcc (theorem_4_1_10 hab (fun v hv => ?_) (fun v hv w hw h => ?_)
    hdu)
  · rw [show v = ((⟨v, hv⟩ : Icc a b) : E) from rfl, extendIcc_apply]
    exact (S ⟨v, hv⟩).2
  · rw [show v = ((⟨v, hv⟩ : Icc a b) : E) from rfl, show w = ((⟨w, hw⟩ : Icc a b) : E) from rfl,
      extendIcc_apply, extendIcc_apply]
    exact hS h

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E] [IsOrderedAddMonoid E] in
/-- Order intervals of a countably Dedekind complete space are countably Dedekind complete. -/
theorem countablyDedekindComplete_Icc {a b : E} (hE : CountablyDedekindComplete E) :
    CountablyDedekindComplete (Icc a b) := by
  intro A hne hc
  obtain ⟨x₀, hx₀⟩ := hne
  have h := hE (Subtype.val '' A) ⟨x₀.1, x₀, hx₀, rfl⟩ (hc.image _)
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨s, hs⟩ := h.1 ⟨b, by rintro _ ⟨x, -, rfl⟩; exact x.2.2⟩
    have hsI : s ∈ Icc a b :=
      ⟨x₀.2.1.trans (hs.1 ⟨x₀, hx₀, rfl⟩), hs.2 (by rintro _ ⟨x, -, rfl⟩; exact x.2.2)⟩
    exact ⟨⟨s, hsI⟩, fun x hx => hs.1 ⟨x, hx, rfl⟩, fun w hw =>
      hs.2 (by rintro _ ⟨x, hx, rfl⟩; exact hw hx)⟩
  · obtain ⟨i, hi⟩ := h.2 ⟨a, by rintro _ ⟨x, -, rfl⟩; exact x.2.1⟩
    have hiI : i ∈ Icc a b :=
      ⟨hi.2 (by rintro _ ⟨x, -, rfl⟩; exact x.2.1), (hi.1 ⟨x₀, hx₀, rfl⟩).trans x₀.2.2⟩
    exact ⟨⟨i, hiI⟩, fun x hx => hi.1 ⟨x, hx, rfl⟩, fun w hw =>
      hi.2 (by rintro _ ⟨x, hx, rfl⟩; exact hw hx)⟩

/-- **Theorem 4.1.11** (p. 132): let `(V, 𝕋)` be a regular ADP on `V = [a, b]` whose policy
operators satisfy Du's conditions. If (a) `E` is countably Dedekind complete, (b) `𝕋` is finite,
or (c) the Bellman operator also satisfies Du's conditions, then (i) the fundamental optimality
properties hold and (ii) VFI, OPI and HPI all converge. -/
theorem theorem_4_1_11 {a b : E} (hab : a ≤ b) {P : Type*} (A : ADP (Icc a b) P)
    (hr : A.Regular) (hdu : ∀ σ, DuConditions a b (extendIcc (A.T σ)))
    (hcase : CountablyDedekindComplete E ∨ A.IsFinite ∨
      DuConditions a b (extendIcc A.bellman)) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar := by
  have hgs : A.IsGloballyStable := fun σ => theorem_4_1_10_subtype hab (A.mono σ) (hdu σ)
  refine ⟨hgs.wellPosed, ?_⟩
  rcases hcase with hE | hfin | hT
  · exact ADP.theorem_3_1_4 hr hgs ⟨⟨b, hab, le_rfl⟩, fun σ => (A.T σ _).2.2⟩
      (countablyDedekindComplete_Icc hE)
  · exact ADP.corollary_3_1_3 hr hgs hfin
  · obtain ⟨w, hw, -, -⟩ := theorem_4_1_10_subtype hab (ADP.Regular.bellman_monotone A hr) hT
    exact ADP.theorem_3_1_2 hr hgs hw

end BanachLattice

end SargentStachurski.AdditionalApplications
