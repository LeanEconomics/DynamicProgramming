/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.Concavity

/-!
# Learning by doing

SLP §5.6, pp. 107–109: unit cost `γ(Q)` falls with cumulative experience `Q`; output in a period
is `q = y − Q`, where `y` is next period's experience. Exercises 5.6a and 5.6b both have the
return `F(Q, y) = R(y − Q) − (y − Q)γ(Q)`: revenue `R(q) = qφ(q)` for the monopolist and
consumer surplus `R(q) = S(q)` for the planner. This module treats a general `R`.

The state space is `X = [0, ∞)` and, as in the manual, output is bounded by `q̄`:
`Γ(Q) = [Q, Q + q̄]`. (The manual's reason, that output above `q̄` never pays, ignores the
learning gain from it; the bound is an assumption of the model here.)

* `lbd_assumption43`, `lbd_assumption44`, `lbd_exists`: Theorem 4.6 applies, so there is a
  unique bounded continuous solution `v` of the functional equation, and `v = v*`.
* `lbd_not_a46`, `lbd_not_a47`: Assumptions 4.6 and 4.7 fail, so Theorems 4.7 and 4.8 do not
  apply. (`F(Q, Q) = 0` for every `Q`, so `F` is never strictly concave.)
* `lbd_argmax_pos`: with a nondecreasing continuation value, producing nothing is never optimal.
* `lbd_strictMono`: `v` is strictly increasing (another argument: `T` maps nondecreasing
  functions into strictly increasing ones, then Corollary 1 to Theorem 3.2).
* `lbd_policy_exceeds`: any optimal output exceeds the output `q̃` that maximizes the current
  return. The manual argues from a first-order condition that needs `v` differentiable, which
  Theorem 4.11 cannot supply here (concavity fails). The proof here uses only the convexity of
  `γ`: one more unit of output lowers future costs at a rate bounded below, while it costs
  nothing to first order at `q̃`.
* `unique_interior_max`: a return with strictly decreasing derivative, positive at `0` and
  negative at `q̄`, has a unique maximizer in `(0, q̄)`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- The state space `X = [0, ∞)` of cumulative experience. -/
abbrev ExpStock := ↥(Ici (0 : ℝ))

variable {R γ : ℝ → ℝ} {qbar β : ℝ}

/-- The hypotheses used for the learning-by-doing problem with return `R(q) − qγ(Q)`. -/
structure LBDHyp (R γ : ℝ → ℝ) (qbar β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  qbar_pos : 0 < qbar
  R_cont : ContinuousOn R (Icc 0 qbar)
  R_zero : R 0 = 0
  γ_cont : ContinuousOn γ (Ici 0)
  γ_anti : StrictAntiOn γ (Ici 0)
  γ_nonneg : ∀ Q, 0 ≤ Q → 0 ≤ γ Q
  /-- Some output `q₀ ≤ q̄` earns a positive return even at the highest cost `γ(0)`. -/
  profit : ∃ q₀ ∈ Ioc 0 qbar, q₀ * γ 0 < R q₀

/-- `Γ(Q) = [Q, Q + q̄]`. -/
def lbdΓ (qbar : ℝ) (Q : ExpStock) : Set ExpStock := {y | Q.1 ≤ y.1 ∧ y.1 ≤ Q.1 + qbar}

/-- `F(Q, y) = R(y − Q) − (y − Q)γ(Q)`. -/
def lbdF (R γ : ℝ → ℝ) (p : ExpStock × ExpStock) : ℝ :=
  R (p.2.1 - p.1.1) - (p.2.1 - p.1.1) * γ p.1.1

theorem lbd_γ_le (h : LBDHyp R γ qbar β) (Q : ExpStock) : γ Q.1 ≤ γ 0 :=
  h.γ_anti.antitoneOn (mem_Ici.2 le_rfl) Q.2 Q.2

/-- Assumption 4.3 holds for `Γ(Q) = [Q, Q + q̄]`. -/
theorem lbd_assumption43 (h : LBDHyp R γ qbar β) : Assumption43 (lbdΓ qbar) := by
  have hemb := (isClosed_Ici (a := (0 : ℝ))).isClosedEmbedding_subtypeVal
  have hself : ∀ Q : ExpStock, Q ∈ lbdΓ qbar Q := fun Q => ⟨le_rfl, by linarith [h.qbar_pos]⟩
  refine ⟨fun Q => ⟨Q, hself Q⟩, fun Q => hemb.isCompact_preimage isCompact_Icc,
    fun Q => ⟨⟨Q, hself Q⟩, fun y hy Qs hQs => ?_⟩,
    fun Q => ⟨⟨Q, hself Q⟩, fun Qs hQs ys hys => ?_⟩⟩
  · -- l.h.c.: shift `y` with `Q`
    have hy0 : 0 ≤ y.1 - Q.1 := sub_nonneg.2 hy.1
    refine ⟨0, fun n => ⟨(Qs n).1 + (y.1 - Q.1), mem_Ici.2 (add_nonneg (Qs n).2 hy0)⟩,
      fun n _ => ⟨by simp only; linarith, by simp only; linarith [hy.2]⟩, ?_⟩
    have := ((continuous_subtype_val.tendsto Q).comp hQs).add_const (y.1 - Q.1)
    rw [show Q.1 + (y.1 - Q.1) = y.1 by ring] at this
    exact tendsto_subtype_rng.2 this
  · -- u.h.c.: the `yₙ` lie in a compact set, and `Γ` has a closed graph
    have hval := (continuous_subtype_val.tendsto Q).comp hQs
    obtain ⟨B, hB⟩ := hval.bddAbove_range
    have hK : ∀ n, ys n ∈ Subtype.val ⁻¹' Icc (0 : ℝ) (B + qbar) := fun n =>
      ⟨(ys n).2, (hys n).2.trans (by linarith [show (Qs n).1 ≤ B from hB ⟨n, rfl⟩])⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := (hemb.isCompact_preimage isCompact_Icc).tendsto_subseq hK
    have hyl := (continuous_subtype_val.tendsto y).comp hlim
    have hQl := hval.comp hφ.tendsto_atTop
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto hQl hyl (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hyl (hQl.add_const qbar)
        (Eventually.of_forall fun n => (hys (φ n)).2)

/-- Assumption 4.4 holds: on the graph `q = y − Q ∈ [0, q̄]`, so `F` is bounded and continuous. -/
theorem lbd_assumption44 (h : LBDHyp R γ qbar β) : Assumption44 (lbdΓ qbar) (lbdF R γ) β := by
  have hq : ∀ p ∈ graph (lbdΓ qbar), p.2.1 - p.1.1 ∈ Icc 0 qbar := fun p hp =>
    ⟨sub_nonneg.2 hp.1, by linarith [hp.2]⟩
  have hγc : Continuous fun p : ExpStock × ExpStock => γ p.1.1 :=
    h.γ_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2
  have hqc : Continuous fun p : ExpStock × ExpStock => p.2.1 - p.1.1 :=
    (continuous_subtype_val.comp continuous_snd).sub (continuous_subtype_val.comp continuous_fst)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn h.R_cont
  refine ⟨(h.R_cont.comp hqc.continuousOn hq).sub (hqc.mul hγc).continuousOn,
    ⟨B + qbar * γ 0, fun p hp => ?_⟩, h.β_pos, h.β_lt⟩
  have h1 := hB _ (hq p hp)
  rw [Real.norm_eq_abs] at h1
  have hγ0 := h.γ_nonneg _ p.1.2
  have hγ1 := lbd_γ_le h p.1
  have hq' := hq p hp
  have h2 : |(p.2.1 - p.1.1) * γ p.1.1| ≤ qbar * γ 0 := by
    rw [abs_mul, abs_of_nonneg hq'.1, abs_of_nonneg hγ0]
    exact mul_le_mul hq'.2 hγ1 hγ0 h.qbar_pos.le
  simp only [lbdF]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- **Exercises 5.6a–b.** There is a unique bounded continuous `v` satisfying the functional
equation; it is the supremum function, and the policy correspondence is nonempty and u.h.c. -/
theorem lbd_exists (h : LBDHyp R γ qbar β) :
    ∃ v : ExpStock →ᵇ ℝ, bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v ∧
      (∀ w, bellman (lbd_assumption43 h) (lbd_assumption44 h) w = w → w = v) ∧
      (fun x => (v x : EReal)) = vstar (lbdΓ qbar) (curryF (lbdF R γ)) β ∧
      ∀ x, (argmax (obj (lbdF R γ) β v) (lbdΓ qbar) x).Nonempty ∧
        IsUHC (argmax (obj (lbdF R γ) β v) (lbdΓ qbar)) x := by
  have : Nonempty ExpStock := ⟨⟨0, mem_Ici.2 le_rfl⟩⟩
  obtain ⟨v, hv, huniq, -, hG⟩ := theorem_4_6 (lbd_assumption43 h) (lbd_assumption44 h)
  exact ⟨v, hv, huniq, fixedPoint_eq_vstar _ _ hv, fun x => ⟨(hG x).1, (hG x).2.2⟩⟩

/-- **Exercise 5.6a.** Assumption 4.6 fails: `Γ` is not monotone. -/
theorem lbd_not_a46 (hq : 0 < qbar) :
    ¬ ∀ Q Q' : ExpStock, Q ≤ Q' → lbdΓ qbar Q ⊆ lbdΓ qbar Q' := by
  intro hmono
  have h0 : (⟨0, mem_Ici.2 le_rfl⟩ : ExpStock) ≤ ⟨qbar, mem_Ici.2 hq.le⟩ := hq.le
  have := hmono _ _ h0 (show (⟨0, mem_Ici.2 le_rfl⟩ : ExpStock) ∈ lbdΓ qbar ⟨0, _⟩ from
    ⟨le_rfl, by simp only; linarith⟩)
  exact absurd this.1 (by simp only [not_le]; exact hq)

/-- **Exercise 5.6a.** Assumption 4.7 fails: `F(Q, Q) = 0` for every `Q`, so `F` is not strictly
concave between `(0, 0)` and `(1, 1)`. -/
theorem lbd_not_a47 (h : LBDHyp R γ qbar β) :
    ¬ Assumption47 (convex_Ici 0) (lbdΓ qbar) (lbdF R γ) := by
  intro h47
  have hself : ∀ Q : ExpStock, Q ∈ lbdΓ qbar Q := fun Q => ⟨le_rfl, by linarith [h.qbar_pos]⟩
  set a : ExpStock := ⟨0, mem_Ici.2 le_rfl⟩
  set b : ExpStock := ⟨1, mem_Ici.2 zero_le_one⟩
  have hne : a ≠ b := fun he => by
    have := congrArg Subtype.val he
    simp [a, b] at this
  have := (h47 a a b b (hself a) (hself b) (1 / 2) (by norm_num) (by norm_num)).2 hne
  simp [lbdF, h.R_zero] at this

/-- With a nondecreasing continuation value `w`, producing nothing is never optimal: every
maximizer `y` at `Q` has `y > Q`. -/
theorem lbd_argmax_pos (h : LBDHyp R γ qbar β) {w : ExpStock → ℝ} (hw : Monotone w)
    {Q y : ExpStock} (hy : y ∈ lbdΓ qbar Q)
    (hmax : ∀ z ∈ lbdΓ qbar Q, lbdF R γ (Q, z) + β * w z ≤ lbdF R γ (Q, y) + β * w y) :
    Q.1 < y.1 := by
  obtain ⟨q₀, ⟨hq0, hq0'⟩, hprof⟩ := h.profit
  by_contra hle
  push Not at hle
  have hyQ : y = Q := Subtype.ext (le_antisymm hle hy.1)
  subst hyQ
  set z : ExpStock := ⟨y.1 + q₀, mem_Ici.2 (by linarith [y.2.out])⟩
  have hz : z ∈ lbdΓ qbar y := ⟨by simp only [z]; linarith, by simp only [z]; linarith⟩
  have h1 := hmax z hz
  have hwz : w y ≤ w z := hw (show y.1 ≤ z.1 by simp only [z]; linarith)
  have hγ := lbd_γ_le h y
  simp only [lbdF, z, sub_self, h.R_zero, zero_mul, add_sub_cancel_left] at h1
  nlinarith [h.β_pos]

/-- **Exercises 5.6a–b.** `v` is strictly increasing: `T` maps nondecreasing functions into
strictly increasing ones (copy the optimal output from `Q` at `Q' > Q`: the cost is lower and
the continuation no smaller). -/
theorem lbd_strictMono (h : LBDHyp R γ qbar β) {v : ExpStock →ᵇ ℝ}
    (hv : bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v) : StrictMono v := by
  set C' : Set (ExpStock →ᵇ ℝ) := {f | Monotone f}
  set C'' : Set (ExpStock →ᵇ ℝ) := {f | StrictMono f}
  have hclosed : IsClosed C' := by
    have : C' = ⋂ x, ⋂ y, ⋂ (_ : x ≤ y), {f : ExpStock →ᵇ ℝ | f x ≤ f y} := by
      ext f; simp [C', Monotone]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const x) (continuous_eval_const y)
  have hmaps : MapsTo (bellman (lbd_assumption43 h) (lbd_assumption44 h)) C' C'' :=
    fun f hf Q Q' hQQ' => by
      obtain ⟨y, hy, hval, hmax⟩ :=
        exists_bellman_argmax (lbd_assumption43 h) (lbd_assumption44 h) f Q
      obtain ⟨-, -, -, hmax'⟩ :=
        exists_bellman_argmax (lbd_assumption43 h) (lbd_assumption44 h) f Q'
      have hpos := lbd_argmax_pos h hf hy fun z hz => hval ▸ hmax z hz
      have hQQ'' : Q.1 < Q'.1 := hQQ'
      set y' : ExpStock := ⟨y.1 + (Q'.1 - Q.1), mem_Ici.2 (by linarith [y.2.out])⟩
      have hy' : y' ∈ lbdΓ qbar Q' :=
        ⟨by simp only [y']; linarith [hy.1], by simp only [y']; linarith [hy.2]⟩
      have h1 := hmax' y' hy'
      have hγ : γ Q'.1 < γ Q.1 := h.γ_anti Q.2 Q'.2 hQQ''
      have hfy : f y ≤ f y' := hf (show y.1 ≤ y'.1 by simp only [y']; linarith)
      have hcost : (y.1 - Q.1) * γ Q'.1 < (y.1 - Q.1) * γ Q.1 :=
        mul_lt_mul_of_pos_left hγ (by linarith)
      change bellman _ _ f Q < bellman _ _ f Q'
      rw [hval]
      have e : y'.1 - Q'.1 = y.1 - Q.1 := by simp only [y']; ring
      simp only [lbdF, e] at h1 ⊢
      nlinarith [h.β_pos]
  have hne : C'.Nonempty := ⟨0, fun _ _ _ => le_rfl⟩
  exact (corollary_1 (bellman_contraction (lbd_assumption43 h) (lbd_assumption44 h)) hv hne
    hclosed (fun f hf => (hmaps hf).monotone) hmaps).2

/-- **Exercises 5.6a–b.** Let `q̃ ∈ (0, q̄)` be the unique maximizer of the current return
`R(q) − qγ(Q)` on `[0, q̄]`, with `R` differentiable at `q̃`, and let `γ` be convex. Then every
optimal choice `y*` has output `y* − Q > q̃`. -/
theorem lbd_policy_exceeds (h : LBDHyp R γ qbar β) (hγc : ConvexOn ℝ (Ici 0) γ)
    {v : ExpStock →ᵇ ℝ} (hv : bellman (lbd_assumption43 h) (lbd_assumption44 h) v = v)
    {Q : ExpStock} {qt R' : ℝ} (hqt : qt ∈ Ioo 0 qbar)
    (hqmax : ∀ q ∈ Icc 0 qbar, q ≠ qt → R q - q * γ Q.1 < R qt - qt * γ Q.1)
    (hR : HasDerivAt R R' qt) {ystar : ExpStock}
    (hys : ystar ∈ argmax (obj (lbdF R γ) β v) (lbdΓ qbar) Q) :
    qt < ystar.1 - Q.1 := by
  have h43 := lbd_assumption43 h
  have h44 := lbd_assumption44 h
  have hvm := lbd_strictMono h hv
  have hle : ∀ z ∈ lbdΓ qbar Q, obj (lbdF R γ) β v (Q, z) ≤ obj (lbdF R γ) β v (Q, ystar) :=
    fun z hz => by
      rw [hys.2]; exact le_maxValue (continuousOn_obj h44 v.continuous) (h43.compact Q) hz
  have hq := hys.1
  set ψ : ℝ → ℝ := fun q => R q - q * γ Q.1
  -- (1) `q* ≥ q̃`
  have hge : qt ≤ ystar.1 - Q.1 := by
    by_contra hlt
    push Not at hlt
    set z : ExpStock := ⟨Q.1 + qt, mem_Ici.2 (by linarith [Q.2.out, hqt.1])⟩
    have hz : z ∈ lbdΓ qbar Q := ⟨by simp only [z]; linarith [hqt.1],
      by simp only [z]; linarith [hqt.2]⟩
    have h1 := hqmax (ystar.1 - Q.1) ⟨by linarith [hq.1], by linarith [hq.2]⟩ hlt.ne
    have h2 : v ystar < v z := hvm (show ystar.1 < z.1 by simp only [z]; linarith)
    have h3 := hle z hz
    simp only [obj, lbdF, z, add_sub_cancel_left] at h3
    nlinarith [h.β_pos]
  -- (2) `q* ≠ q̃`
  refine lt_of_le_of_ne hge fun heq => ?_
  have hyst : ystar.1 = Q.1 + qt := by linarith
  -- the first-order condition at the interior maximum `q̃`
  have hψ : HasDerivAt ψ (R' - γ Q.1) qt := by
    have := hR.sub ((hasDerivAt_id' qt).mul_const (γ Q.1))
    rwa [one_mul] at this
  have hloc : IsLocalMax ψ qt := by
    filter_upwards [Icc_mem_nhds hqt.1 hqt.2] with q hq'
    rcases eq_or_ne q qt with rfl | hne
    · exact le_rfl
    · exact (hqmax q hq' hne).le
  have hfoc : R' - γ Q.1 = 0 := hloc.hasDerivAt_eq_zero hψ
  rw [hfoc] at hψ
  -- the optimal output at `y*` is positive
  obtain ⟨y₁, hy₁, hy₁v, hy₁max⟩ := exists_bellman_argmax h43 h44 v ystar
  rw [hv] at hy₁v hy₁max
  have hq₁ := lbd_argmax_pos h hvm.monotone hy₁ fun z hz => hy₁v ▸ hy₁max z hz
  set q₁ := y₁.1 - ystar.1
  -- the cost falls at a rate at least `s₀ = γ(y*) − γ(y* + 1) > 0`
  set s₀ := γ ystar.1 - γ (ystar.1 + 1)
  have hs₀ : 0 < s₀ := sub_pos.2 (h.γ_anti ystar.2 (mem_Ici.2 (by linarith [ystar.2.out]))
    (by linarith))
  have hcost : ∀ ε, 0 < ε → ε ≤ 1 → s₀ * ε ≤ γ ystar.1 - γ (ystar.1 + ε) := fun ε hε hε1 => by
    have := hγc.2 (mem_Ici.2 ystar.2.out) (mem_Ici.2 (by linarith [ystar.2.out] :
      (0 : ℝ) ≤ ystar.1 + 1)) (sub_nonneg.2 hε1) hε.le (by ring)
    simp only [smul_eq_mul] at this
    rw [show (1 - ε) * ystar.1 + ε * (ystar.1 + 1) = ystar.1 + ε by ring] at this
    simp only [s₀]
    nlinarith
  -- so `v(y* + ε) − v(y*) ≥ q₁ s₀ ε`
  have hvgain : ∀ ε (hε : 0 < ε), ε ≤ 1 →
      v ystar + q₁ * (s₀ * ε) ≤ v ⟨ystar.1 + ε, mem_Ici.2 (by linarith [ystar.2.out])⟩ :=
    fun ε hε hε1 => by
      set yε : ExpStock := ⟨ystar.1 + ε, mem_Ici.2 (by linarith [ystar.2.out])⟩
      set y₁ε : ExpStock := ⟨y₁.1 + ε, mem_Ici.2 (by linarith [y₁.2.out])⟩
      obtain ⟨-, -, -, hmaxε⟩ := exists_bellman_argmax h43 h44 v yε
      rw [hv] at hmaxε
      have hmem : y₁ε ∈ lbdΓ qbar yε :=
        ⟨by simp only [y₁ε, yε]; linarith [hy₁.1], by simp only [y₁ε, yε]; linarith [hy₁.2]⟩
      have h1 := hmaxε y₁ε hmem
      have h2 : v y₁ ≤ v y₁ε := hvm.monotone (show y₁.1 ≤ y₁ε.1 by simp only [y₁ε]; linarith)
      have h3 := hcost ε hε hε1
      have e : y₁ε.1 - yε.1 = q₁ := by simp only [y₁ε, yε, q₁]; ring
      simp only [lbdF, e] at h1 hy₁v
      have h4 : q₁ * (s₀ * ε) ≤ q₁ * (γ ystar.1 - γ (ystar.1 + ε)) :=
        mul_le_mul_of_nonneg_left h3 (by simp only [q₁]; linarith)
      simp only [yε] at h1 ⊢
      nlinarith [h.β_pos]
  -- pick `ε` small enough that the current return falls by less than half the gain
  set c := β * q₁ * s₀ / 2
  have hc : 0 < c := by
    have : 0 < q₁ := by simp only [q₁]; linarith
    exact div_pos (mul_pos (mul_pos h.β_pos this) hs₀) two_pos
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (ψ (qt + t) - ψ qt)) (𝓝[>] 0) (𝓝 0) :=
    (hasDerivAt_iff_tendsto_slope_zero.1 hψ).mono_left
      (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), -c < t⁻¹ • (ψ (qt + t) - ψ qt) ∧ 0 < t ∧ t < 1 ∧
      t < qbar - qt := by
    refine (hslope.eventually (lt_mem_nhds (neg_lt_zero.2 hc))).and
      ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ))).and ?_)
    have h1 : (0 : ℝ) < min 1 (qbar - qt) := lt_min one_pos (by linarith [hqt.2])
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h1)] with t ht
    exact ⟨ht.trans_le (min_le_left _ _), ht.trans_le (min_le_right _ _)⟩
  obtain ⟨ε, hslp, hε, hε1, hεq⟩ := hev.exists
  have hψε : -c * ε < ψ (qt + ε) - ψ qt := by
    rw [smul_eq_mul] at hslp
    have := mul_lt_mul_of_pos_left hslp hε
    rwa [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_comm] at this
  -- the larger output `q̃ + ε` beats `y*`
  set z : ExpStock := ⟨ystar.1 + ε, mem_Ici.2 (by linarith [ystar.2.out])⟩
  have hz : z ∈ lbdΓ qbar Q := ⟨by simp only [z]; linarith [hq.1],
    by simp only [z]; linarith [hqt.2]⟩
  have h1 := hle z hz
  have h2 : v ystar + q₁ * (s₀ * ε) ≤ v z := hvgain ε hε hε1.le
  have ez : z.1 - Q.1 = qt + ε := by simp only [z]; linarith
  have ey : ystar.1 - Q.1 = qt := by linarith
  simp only [obj, lbdF, ez, ey] at h1
  simp only [ψ] at hψε
  have hq₁0 : 0 < q₁ := by simp only [q₁]; linarith
  have hβ2 := mul_le_mul_of_nonneg_left h2 h.β_pos.le
  have hcε : c * ε = β * (q₁ * (s₀ * ε)) / 2 := by simp only [c]; ring
  have hpos : 0 < β * (q₁ * (s₀ * ε)) := mul_pos h.β_pos (mul_pos hq₁0 (mul_pos hs₀ hε))
  nlinarith

/-- A function with strictly decreasing derivative on `[0, q̄]`, positive at `0` and negative at
`q̄`, has a unique maximizer `q̃ ∈ (0, q̄)` on `[0, q̄]`, where its derivative vanishes. -/
theorem unique_interior_max {ψ ψ' : ℝ → ℝ} (hq : 0 < qbar) (hc : ContinuousOn ψ (Icc 0 qbar))
    (hd : ∀ q ∈ Ioo 0 qbar, HasDerivAt ψ (ψ' q) q) (hc' : ContinuousOn ψ' (Icc 0 qbar))
    (hanti : StrictAntiOn ψ' (Icc 0 qbar)) (h0 : 0 < ψ' 0) (h1 : ψ' qbar < 0) :
    ∃ qt ∈ Ioo 0 qbar, ψ' qt = 0 ∧ ∀ q ∈ Icc 0 qbar, q ≠ qt → ψ q < ψ qt := by
  obtain ⟨qt, hqt, hzero⟩ := intermediate_value_Icc' hq.le hc' ⟨h1.le, h0.le⟩
  have hqt0 : qt ≠ 0 := fun he => by rw [he] at hzero; linarith
  have hqt1 : qt ≠ qbar := fun he => by rw [he] at hzero; linarith
  have hqt' : qt ∈ Ioo 0 qbar := ⟨lt_of_le_of_ne hqt.1 (Ne.symm hqt0), lt_of_le_of_ne hqt.2 hqt1⟩
  refine ⟨qt, hqt', hzero, fun q hq' hne => ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' hlt
      (hc.mono (Icc_subset_Icc hq'.1 hqt.2))
      (fun x hx => hd x ⟨hq'.1.trans_lt hx.1, hx.2.trans hqt'.2⟩)
    have hpos : 0 < ψ' ξ := by
      have := hanti ⟨hq'.1.trans hξ.1.le, (hξ.2.trans hqt'.2).le⟩ hqt hξ.2
      linarith
    rw [hslope] at hpos
    have := (div_pos_iff_of_pos_right (by linarith : 0 < qt - q)).1 hpos
    linarith
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' hgt
      (hc.mono (Icc_subset_Icc hqt.1 hq'.2))
      (fun x hx => hd x ⟨hqt'.1.trans hx.1, hx.2.trans_le hq'.2⟩)
    have hneg : ψ' ξ < 0 := by
      have := hanti hqt ⟨(hqt.1.trans hξ.1.le), (hξ.2.trans_le hq'.2).le⟩ hξ.1
      linarith
    rw [hslope] at hneg
    have := (div_neg_iff.1 hneg)
    rcases this with ⟨-, h2⟩ | ⟨h2, -⟩
    · linarith
    · linarith

end StokeyLucasPrescott.DeterministicApplications
