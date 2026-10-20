/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.SequenceAssumptions
import ParetoOptimaEquilibria.SequenceInfinity

/-!
# Exercise 15.11: Assumption 15.7 and limits of truncated utilities

SLP §15.4, p. 465, with `S = ℓ∞ = BddSeq ℝ`.

* **Exercise 15.11(a)** (`ex_15_11a`): `u(x) = inf_t x_t` on `X = {x : 0 ≤ x_t ≤ 1}` violates
  Assumption 15.7 (while `X` satisfies 15.1 and 15.6).
* **Exercise 15.11(b)**, "if" (`ex_15_11b_if`): `u(x) = lim_T u(xᵀ)` for all `x ∈ X` implies 15.7.
* **Exercise 15.11(b)**, corrected (`ex_15_11b_liminf`): if `X` is convex, satisfies 15.6, and `u`
  is continuous on `X`, then 15.7 holds iff `liminf_T u(xᵀ) ≥ u(x)` for every `x ∈ X` (in the
  form: `c < u(x)` implies `c < u(xᵀ)` for all large `T`).

**Corrections.**
* The "only if" of Exercise 15.11(b) is false (`ex_15_11b_counterexample`): on `X = ℓ∞`,
  `u(x) = Σ_t (1/2)ᵗ x_t − d(x)`, `d(x) = dist(x, seqC00) = limsup_t |x_t|`, satisfies 15.1–15.3,
  15.6 and 15.7, but `u(1ᵀ) → 2 ≠ 1 = u(1)`.
* The manual's "partial converse" (15.7 implies that `lim_T u(xᵀ)` exists and is `≥ u(x)`) is
  false (`ex_15_11b_manual_counterexample`): `u(x) = Σ_t (1/2)ᵗ x_t − d(x) − g(x)`, with
  `g(x) = sup_t (x_{2t+1} − x_{2t+2})⁺` (`oddDrop`), satisfies 15.1–15.3, 15.6 and 15.7, but
  `u(1ᵀ)` oscillates (`g(1ᵀ) = 1` for odd `T`, `0` for even `T`). The manual's existence step
  applies 15.7 to the pair `(x^{T̂}, x̂)`, which says nothing about `u(xᵀ)`. The manual's
  inequality `liminf_T u(xᵀ) ≥ u(x)` is correct (`ex_15_11b_liminf`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set
open scoped ENNReal

/-! ### Exercise 15.11(a) -/

/-- The utility `u(x) = inf_t x_t`. -/
noncomputable def infUtility (x : BddSeq ℝ) : ℝ := ⨅ t, x t

/-- **Exercise 15.11(a)**: `u(x) = inf_t x_t` on `X = {x ∈ ℓ∞ : 0 ≤ x_t ≤ 1}` does not satisfy
Assumption 15.7 (`x = 1`, `x′ = 1/2`, `u(xᵀ) = 0`), although `X` satisfies 15.1 and 15.6. -/
theorem ex_15_11a :
    Convex ℝ (seqSet (Icc (0 : ℝ) 1)) ∧ SeqTruncClosed (seqSet (Icc (0 : ℝ) 1)) ∧
    ¬ SeqTailInsensitive (seqSet (Icc (0 : ℝ) 1)) infUtility := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨(ex_15_10a (convex_Icc 0 1) h0).1, (ex_15_10a (convex_Icc 0 1) h0).2, fun h => ?_⟩
  have hx : oneSeq ∈ seqSet (Icc (0 : ℝ) 1) := fun t => by simp [oneSeq]
  have hx' : (1 / 2 : ℝ) • oneSeq ∈ seqSet (Icc (0 : ℝ) 1) := fun t => by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; simp [oneSeq]; norm_num
  have hu1 : infUtility oneSeq = 1 := by simp [infUtility, oneSeq]
  have hu2 : infUtility ((1 / 2 : ℝ) • oneSeq) = 1 / 2 := by
    unfold infUtility
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    simp [oneSeq]
  obtain ⟨T, hT⟩ := (h oneSeq hx _ hx' (by rw [hu1, hu2]; norm_num)).exists
  have hmem := seqTrunc_mem_seqSet h0 hx T
  have hle : infUtility (seqTrunc T oneSeq) ≤ 0 := by
    have hb : BddBelow (range fun t => seqTrunc T oneSeq t) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩
    calc infUtility (seqTrunc T oneSeq) ≤ seqTrunc T oneSeq (T + 1) := ciInf_le hb (T + 1)
      _ = 0 := by simp [seqTrunc_apply]
  have := hT hmem
  rw [hu2] at this
  linarith

/-! ### Exercise 15.11(b) -/

/-- **Exercise 15.11(b)**, "if": `u(x) = lim_T u(xᵀ)` for every `x ∈ X` implies 15.7. -/
theorem ex_15_11b_if {A : Set (BddSeq ℝ)} {v : BddSeq ℝ → ℝ}
    (h : ∀ x ∈ A, Tendsto (fun T => v (seqTrunc T x)) atTop (𝓝 (v x))) : SeqTailInsensitive A v :=
  SeqTailInsensitive.of_tendsto h

/-- **Exercise 15.11(b)**, corrected: for `X` convex and closed under truncation far out (15.6),
and `u` continuous on `X`, Assumption 15.7 holds iff `liminf_T u(xᵀ) ≥ u(x)` for all `x ∈ X`.
(The "⇒" is the manual's inequality; the manual's claim that the limit exists is false, see
`ex_15_11b_manual_counterexample`.) -/
theorem ex_15_11b_liminf {A : Set (BddSeq ℝ)} {v : BddSeq ℝ → ℝ} (hA : SeqTruncClosed A)
    (hconv : Convex ℝ A) (hv : ContinuousOn v A) :
    SeqTailInsensitive A v ↔ ∀ x ∈ A, ∀ c < v x, ∀ᶠ T in atTop, c < v (seqTrunc T x) := by
  refine ⟨fun h x hx c hc => ?_, SeqTailInsensitive.of_liminf⟩
  by_cases hmin : ∀ y ∈ A, c < v y
  · exact (hA x hx).mono fun T hT => hmin _ hT
  simp only [not_forall, not_lt, exists_prop] at hmin
  obtain ⟨y, hy, hyc⟩ := hmin
  set g : ℝ → ℝ := fun θ => v (θ • x + (1 - θ) • y) with hg
  have hseg : ∀ θ ∈ Icc (0 : ℝ) 1, θ • x + (1 - θ) • y ∈ A := fun θ hθ =>
    hconv hx hy hθ.1 (by linarith [hθ.2]) (by ring)
  have hgc : ContinuousOn g (Icc 0 1) :=
    hv.comp (((continuous_id.smul continuous_const).add
      ((continuous_const.sub continuous_id).smul continuous_const)).continuousOn) hseg
  have hg0 : g 0 = v y := by simp [hg]
  have hg1 : g 1 = v x := by simp [hg]
  obtain ⟨θ, hθ, hgθ⟩ := intermediate_value_Icc zero_le_one hgc
    (⟨hg0 ▸ hyc, hg1 ▸ hc.le⟩ : c ∈ Icc (g 0) (g 1))
  have hx' := hseg θ hθ
  have hlt : v (θ • x + (1 - θ) • y) < v x := by
    change g θ < v x
    rw [hgθ]; exact hc
  refine ((h x hx _ hx' hlt).and (hA x hx)).mono fun T hT => ?_
  have := hT.1 hT.2
  rwa [show v (θ • x + (1 - θ) • y) = c from hgθ] at this

/-- The utility `u(x) = Σ_t (1/2)ᵗ x_t − d(x)` with `d(x) = dist(x, seqC00) = limsup_t |x_t|`. -/
noncomputable def tailPenalizedUtility (x : BddSeq ℝ) : ℝ := halfSum x - tailDist x

/-- The concavity inequality for `σ − d − f` with `f` convex. -/
theorem concave_halfSum_sub {f : BddSeq ℝ → ℝ}
    (hf : ∀ x x' : BddSeq ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      f (θ • x + (1 - θ) • x') ≤ θ * f x + (1 - θ) * f x') (x x' : BddSeq ℝ) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (halfSum x - tailDist x - f x) + (1 - θ) * (halfSum x' - tailDist x' - f x') ≤
      halfSum (θ • x + (1 - θ) • x') - tailDist (θ • x + (1 - θ) • x') -
        f (θ • x + (1 - θ) • x') := by
  have h1' := tailDist_convex x x' h0 h1
  have h2 := hf x x' θ h0 h1
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  linarith

/-- **The "only if" of Exercise 15.11(b) is false.** On `X = ℓ∞`, `u(x) = Σ_t (1/2)ᵗ x_t − d(x)`
satisfies 15.1, 15.2 (it is concave), 15.3, 15.6 and 15.7, but `u(1ᵀ) ↛ u(1)`. -/
theorem ex_15_11b_counterexample :
    Convex ℝ (univ : Set (BddSeq ℝ)) ∧ SeqTruncClosed (univ : Set (BddSeq ℝ)) ∧
    SeqSemistrictQC univ tailPenalizedUtility ∧ ContinuousOn tailPenalizedUtility univ ∧
    SeqTailInsensitive univ tailPenalizedUtility ∧
    ¬ ∀ x ∈ (univ : Set (BddSeq ℝ)),
      Tendsto (fun T => tailPenalizedUtility (seqTrunc T x)) atTop
        (𝓝 (tailPenalizedUtility x)) := by
  have htr : ∀ x T, tailPenalizedUtility (seqTrunc T x) = halfSum (seqTrunc T x) := fun x T => by
    simp [tailPenalizedUtility, tailDist_of_mem (seqTrunc_mem_seqC00 T x)]
  refine ⟨convex_univ, fun _ _ => Eventually.of_forall fun _ => mem_univ _,
    SeqSemistrictQC.of_concave fun x _ x' _ θ h0 h1 => ?_,
    (halfSum.continuous.sub continuous_tailDist).continuousOn,
    SeqTailInsensitive.of_liminf fun x _ c hc => ?_, fun h => ?_⟩
  · simpa [tailPenalizedUtility] using
      concave_halfSum_sub (f := fun _ => 0) (fun _ _ _ _ _ => by simp) x x' h0.le h1.le
  · have hc' : c < halfSum x := hc.trans_le (sub_le_self _ (tailDist_nonneg x))
    exact ((tendsto_halfSum_seqTrunc x).eventually (lt_mem_nhds hc')).mono fun T hT => by
      rw [htr]; exact hT
  · have h1 := h oneSeq (mem_univ _)
    simp only [htr] at h1
    have h2 := tendsto_nhds_unique (tendsto_halfSum_seqTrunc oneSeq) h1
    rw [tailPenalizedUtility, tailDist_oneSeq] at h2
    linarith

/-- The "odd drop" `g(x) = sup_t (x_{2t+1} − x_{2t+2})⁺`. -/
noncomputable def oddDrop (x : BddSeq ℝ) : ℝ := ⨆ t : ℕ, max 0 (x (2 * t + 1) - x (2 * t + 2))

/-- The terms of `oddDrop` are bounded by `2‖x‖`. -/
theorem oddDrop_term_le_norm (x : BddSeq ℝ) (t : ℕ) :
    max 0 (x (2 * t + 1) - x (2 * t + 2)) ≤ 2 * ‖x‖ := by
  have h1 : |x (2 * t + 1)| ≤ ‖x‖ := by simpa using norm_seq_coord_le x (2 * t + 1)
  have h2 : |x (2 * t + 2)| ≤ ‖x‖ := by simpa using norm_seq_coord_le x (2 * t + 2)
  refine max_le (by positivity) ?_
  linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]

/-- The terms of `oddDrop` are bounded above. -/
theorem oddDrop_bddAbove (x : BddSeq ℝ) :
    BddAbove (range fun t : ℕ => max 0 (x (2 * t + 1) - x (2 * t + 2))) :=
  ⟨2 * ‖x‖, by rintro _ ⟨t, rfl⟩; exact oddDrop_term_le_norm x t⟩

/-- Each term is at most `oddDrop x`. -/
theorem oddDrop_term_le (x : BddSeq ℝ) (t : ℕ) :
    max 0 (x (2 * t + 1) - x (2 * t + 2)) ≤ oddDrop x :=
  le_ciSup (oddDrop_bddAbove x) t

/-- `g ≥ 0`. -/
theorem oddDrop_nonneg (x : BddSeq ℝ) : 0 ≤ oddDrop x :=
  (le_max_left _ _).trans (oddDrop_term_le x 0)

/-- `g` is convex. -/
theorem oddDrop_convex (x x' : BddSeq ℝ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    oddDrop (θ • x + (1 - θ) • x') ≤ θ * oddDrop x + (1 - θ) * oddDrop x' := by
  refine ciSup_le fun t => ?_
  rw [seq_coord_combo, seq_coord_combo]
  simp only [smul_eq_mul]
  have e1 := oddDrop_term_le x t
  have e2 := oddDrop_term_le x' t
  have h1θ : 0 ≤ 1 - θ := by linarith
  refine max_le (by positivity [oddDrop_nonneg x, oddDrop_nonneg x']) ?_
  have f1 : x (2 * t + 1) - x (2 * t + 2) ≤ oddDrop x := (le_max_right _ _).trans e1
  have f2 : x' (2 * t + 1) - x' (2 * t + 2) ≤ oddDrop x' := (le_max_right _ _).trans e2
  nlinarith [mul_le_mul_of_nonneg_left f1 h0, mul_le_mul_of_nonneg_left f2 h1θ]

/-- `g` is `2`-Lipschitz, hence continuous. -/
theorem continuous_oddDrop : Continuous oddDrop := by
  refine (LipschitzWith.of_le_add_mul 2 fun x y => ?_).continuous
  refine ciSup_le fun t => ?_
  have h1 : |(x - y) (2 * t + 1)| ≤ ‖x - y‖ := by simpa using norm_seq_coord_le (x - y) (2 * t + 1)
  have h2 : |(x - y) (2 * t + 2)| ≤ ‖x - y‖ := by simpa using norm_seq_coord_le (x - y) (2 * t + 2)
  rw [lp.coeFn_sub, Pi.sub_apply] at h1 h2
  have e := oddDrop_term_le y t
  rw [dist_eq_norm]
  refine max_le (by have := oddDrop_nonneg y; positivity) ?_
  have := (le_max_right 0 (y (2 * t + 1) - y (2 * t + 2))).trans e
  push_cast
  linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]

/-- Truncation raises `g` by at most `‖x_T‖`: `g(xᵀ) ≤ g(x) + ‖x_T‖`. -/
theorem oddDrop_seqTrunc_le (x : BddSeq ℝ) (T : ℕ) :
    oddDrop (seqTrunc T x) ≤ oddDrop x + ‖x T‖ := by
  refine ciSup_le fun t => ?_
  simp only [seqTrunc_apply]
  have e := oddDrop_term_le x t
  have hn := norm_nonneg (x T)
  have hg := oddDrop_nonneg x
  by_cases ha : 2 * t + 2 ≤ T
  · simp only [show 2 * t + 1 ≤ T by omega, ha, ↓reduceIte]; linarith
  · simp only [ha, ↓reduceIte]
    by_cases hb : 2 * t + 1 ≤ T
    · simp only [hb, ↓reduceIte]
      have hT : 2 * t + 1 = T := by omega
      rw [hT, sub_zero]
      refine max_le (by positivity) ?_
      linarith [le_abs_self (x T), Real.norm_eq_abs (x T)]
    · simp only [hb, ↓reduceIte, sub_zero, max_self]; positivity

/-- `g(1ᵀ) = 1` for odd `T` and `0` for even `T`. -/
theorem oddDrop_seqTrunc_one (k : ℕ) :
    oddDrop (seqTrunc (2 * k) oneSeq) = 0 ∧ oddDrop (seqTrunc (2 * k + 1) oneSeq) = 1 := by
  have hone : ∀ t, oneSeq t = 1 := fun t => rfl
  constructor
  · refine le_antisymm (ciSup_le fun t => ?_) (oddDrop_nonneg _)
    simp only [seqTrunc_apply, hone]
    refine max_le le_rfl ?_
    split_ifs <;> first | omega | norm_num
  · refine le_antisymm (ciSup_le fun t => ?_) ?_
    · simp only [seqTrunc_apply, hone]
      refine max_le zero_le_one ?_
      split_ifs <;> norm_num
    · refine le_trans ?_ (oddDrop_term_le _ k)
      simp only [seqTrunc_apply, hone]
      simp only [le_refl, show ¬ 2 * k + 2 ≤ 2 * k + 1 by omega, ↓reduceIte]
      norm_num

/-- The utility `u(x) = Σ_t (1/2)ᵗ x_t − d(x) − g(x)`. -/
noncomputable def oscillatingUtility (x : BddSeq ℝ) : ℝ := halfSum x - tailDist x - oddDrop x

/-- **The manual's "partial converse" to Exercise 15.11(b) is false.** On `X = ℓ∞`,
`u = σ − d − g` satisfies 15.1, 15.2 (it is concave), 15.3, 15.6 and 15.7, but `lim_T u(1ᵀ)` does
not exist. (In particular the "only if" of the exercise fails for this `u` too.) -/
theorem ex_15_11b_manual_counterexample :
    Convex ℝ (univ : Set (BddSeq ℝ)) ∧ SeqTruncClosed (univ : Set (BddSeq ℝ)) ∧
    SeqSemistrictQC univ oscillatingUtility ∧ ContinuousOn oscillatingUtility univ ∧
    SeqTailInsensitive univ oscillatingUtility ∧
    ¬ ∀ x ∈ (univ : Set (BddSeq ℝ)), ∃ L, Tendsto (fun T => oscillatingUtility (seqTrunc T x)) atTop
      (𝓝 L) ∧ oscillatingUtility x ≤ L := by
  have htr : ∀ x T, oscillatingUtility (seqTrunc T x) =
      halfSum (seqTrunc T x) - oddDrop (seqTrunc T x) := fun x T => by
    simp [oscillatingUtility, tailDist_of_mem (seqTrunc_mem_seqC00 T x)]
  refine ⟨convex_univ, fun _ _ => Eventually.of_forall fun _ => mem_univ _,
    SeqSemistrictQC.of_concave fun x _ x' _ θ h0 h1 =>
      concave_halfSum_sub oddDrop_convex x x' h0.le h1.le,
    ((halfSum.continuous.sub continuous_tailDist).sub continuous_oddDrop).continuousOn,
    SeqTailInsensitive.of_liminf fun x _ c hc => ?_, fun h => ?_⟩
  · set ε := (oscillatingUtility x - c) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have h1 := (tendsto_halfSum_seqTrunc x).eventually
      (lt_mem_nhds (sub_lt_self (halfSum x) hεpos))
    filter_upwards [h1, eventually_norm_lt_tailDist_add x hεpos] with T hT1 hT2
    rw [htr]
    have := oddDrop_seqTrunc_le x T
    unfold oscillatingUtility at hε
    linarith
  · obtain ⟨L, hL, -⟩ := h oneSeq (mem_univ _)
    simp only [htr] at hL
    have hg : Tendsto (fun T => oddDrop (seqTrunc T oneSeq)) atTop (𝓝 (halfSum oneSeq - L)) :=
      ((tendsto_halfSum_seqTrunc oneSeq).sub hL).congr fun T => by ring
    have hev : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
    have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
    have e0 := tendsto_nhds_unique (hg.comp hev)
      (tendsto_const_nhds.congr fun k => (oddDrop_seqTrunc_one k).1.symm)
    have e1 := tendsto_nhds_unique (hg.comp hodd)
      (tendsto_const_nhds.congr fun k => (oddDrop_seqTrunc_one k).2.symm)
    linarith

end StokeyLucasPrescott.ParetoOptimaEquilibria
