/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.BoundedReturns

/-!
# An (s, S) inventory problem

SLP §5.14, pp. 118–122: a manager sells up to one unit per period at price `p`, can order `y`
units for delivery next period at cost `c₀ + c₁y`, and discounts at `β = 1/(1 + r)`; `βp > c₁ > 0`,
`c₀ > 0`. With stock `x`, sales are `min{x, 1}` and the stock left is `z(x) = max{x − 1, 0}`, so
(1) reads `v(x) = p·min{x, 1} + max{βv(z), sup_{y > 0} [−c₀ − c₁y + βv(z + y)]}`.

* **Exercise 5.14a** (`ex_5_14a`): the operator `T` of (1) maps `C(ℝ₊)` into itself (the supremum
  over `y > 0` equals a maximum over a compact interval, `ordSup_eq`), satisfies Blackwell's
  conditions, and has a unique fixed point `v`, with `0 ≤ v ≤ p/(1 − β)`; and an optimal ordering
  policy exists (`ex_5_14a_policy`): at every `x` either not ordering is optimal or some `y > 0`
  attains the supremum.
* **Exercise 5.14b**: `r_n = −c₀ − c₁n + β(1 − βⁿ)p/(1 − β)` and
  `Y_n = r_n/(1 − βⁿ) = −(c₀ + c₁n)/(1 − βⁿ) + βp/(1 − β)` (`Yn_eq`); `Y_n → −∞`
  (`tendsto_Yn`), so some finite `N ≥ 1` maximizes `Y_n` (`ex_5_14b`). The maximizers do not
  depend on `p` (`argmax_Yn_indep_p`), and `N` rises with the fixed cost `c₀`
  (`argmax_Yn_mono_c0`, increasing differences).
* **Exercise 5.14c** (`ex_5_14c`): if `Y_N > 0`, then `A = (1 − β)Y_N/(βp − c₁)` lies in `(0, 1)`;
  in fact `A < 1` for every `N ≥ 1`.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- Inventories `x ≥ 0`. -/
abbrev Stock := ↥(Ici (0 : ℝ))

/-- `f` on stocks extended to `ℝ` by `f(max{x, 0})`. -/
def sext (f : Stock → ℝ) (x : ℝ) : ℝ := f ⟨max x 0, mem_Ici.2 (le_max_right _ _)⟩

theorem sext_of_nonneg (f : Stock → ℝ) {x : ℝ} (hx : 0 ≤ x) : sext f x = f ⟨x, hx⟩ := by
  simp only [sext, max_eq_left hx]

theorem continuous_sext {f : Stock → ℝ} (hf : Continuous f) : Continuous (sext f) :=
  hf.comp ((continuous_id.max continuous_const).subtype_mk _)

theorem abs_sext_le (f : Stock →ᵇ ℝ) (x : ℝ) : |sext f x| ≤ ‖f‖ := by
  unfold sext
  simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _

/-- The stock left after sales, `z(x) = max{x − 1, 0}`. -/
def leftover (x : ℝ) : ℝ := max (x - 1) 0

variable {p c₀ c₁ β : ℝ}

/-- The value of ordering `y`: `−c₀ − c₁y + βf(z + y)`. -/
def orderVal (c₀ c₁ β : ℝ) (f : Stock → ℝ) (z y : ℝ) : ℝ := -c₀ - c₁ * y + β * sext f (z + y)

/-- `sup_{y > 0} [−c₀ − c₁y + βf(z + y)]`. -/
noncomputable def ordSup (c₀ c₁ β : ℝ) (f : Stock → ℝ) (z : ℝ) : ℝ :=
  sSup (orderVal c₀ c₁ β f z '' Ioi 0)

/-- The hypotheses of SLP §5.14. -/
structure InvHyp (p c₀ c₁ β : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  c₀_pos : 0 < c₀
  c₁_pos : 0 < c₁
  margin : c₁ < β * p

theorem InvHyp.p_pos (h : InvHyp p c₀ c₁ β) : 0 < p := by
  by_contra hp; push Not at hp; nlinarith [h.β_pos, h.c₁_pos, h.margin]

theorem orderVal_le (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) {z y : ℝ} (hy : 0 ≤ y) :
    orderVal c₀ c₁ β f z y ≤ -c₀ + β * ‖f‖ := by
  have := abs_sext_le f (z + y)
  have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) h.β_pos.le
  simp only [orderVal]
  nlinarith [h.c₁_pos]

theorem bddAbove_ordSup (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) :
    BddAbove (orderVal c₀ c₁ β f z '' Ioi 0) :=
  ⟨-c₀ + β * ‖f‖, by rintro _ ⟨y, hy, rfl⟩; exact orderVal_le h f (le_of_lt hy)⟩

/-- The order horizon `Y = 2β‖f‖/c₁ + 1`: larger orders never beat not ordering. -/
noncomputable def horizon (c₁ β : ℝ) (f : Stock →ᵇ ℝ) : ℝ := 2 * β * ‖f‖ / c₁ + 1

theorem horizon_pos (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) : 0 < horizon c₁ β f := by
  unfold horizon
  have : 0 ≤ 2 * β * ‖f‖ / c₁ := div_nonneg (by nlinarith [h.β_pos, norm_nonneg f]) h.c₁_pos.le
  linarith

theorem orderVal_beyond (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) {y : ℝ}
    (hy : horizon c₁ β f < y) : orderVal c₀ c₁ β f z y < β * sext f z := by
  have h1 := abs_sext_le f (z + y)
  have h2 := abs_sext_le f z
  have hY : 2 * β * ‖f‖ < c₁ * y := by
    have h3 : 2 * β * ‖f‖ / c₁ < y := by unfold horizon at hy; linarith
    rw [div_lt_iff₀ h.c₁_pos] at h3
    linarith
  simp only [orderVal]
  nlinarith [h.β_pos, le_abs_self (sext f (z + y)), neg_abs_le (sext f z), h.c₀_pos]

/-- The supremum over `y > 0` together with not ordering equals a maximum over the compact
`[0, Y]` together with not ordering. -/
theorem ordSup_eq (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) :
    max (β * sext f z) (ordSup c₀ c₁ β f z) =
      max (β * sext f z) (sSup (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f))) := by
  have hY := horizon_pos h f
  have hc : ContinuousOn (orderVal c₀ c₁ β f z) (Icc 0 (horizon c₁ β f)) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).add (continuous_const.mul
      ((continuous_sext f.continuous).comp (continuous_const.add continuous_id)))).continuousOn
  have hbdd : BddAbove (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f)) :=
    (isCompact_Icc.image_of_continuousOn hc).bddAbove
  have h0 : orderVal c₀ c₁ β f z 0 < β * sext f z := by
    simp only [orderVal, add_zero, mul_zero, sub_zero]; linarith [h.c₀_pos]
  refine le_antisymm (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_)
  · -- `sup_{y > 0} ≤ max{no order, max over [0, Y]}`
    refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases le_or_gt y (horizon c₁ β f) with hyY | hyY
    · exact (le_csSup hbdd ⟨y, ⟨le_of_lt hy, hyY⟩, rfl⟩).trans (le_max_right _ _)
    · exact (orderVal_beyond h f z hyY).le.trans (le_max_left _ _)
  · -- the maximum over `[0, Y]` is attained; at `0` it is beaten by not ordering
    obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hY.le) hc
    have heq : sSup (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f)) = orderVal c₀ c₁ β f z y :=
      (IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmax hu⟩)
    rw [heq]
    rcases eq_or_lt_of_le hy.1 with hy0 | hypos
    · rw [← hy0]; exact h0.le.trans (le_max_left _ _)
    · exact (le_csSup (bddAbove_ordSup h f z) ⟨y, hypos, rfl⟩).trans (le_max_right _ _)

/-- The right side of (1) as a function on stocks. -/
noncomputable def invRHS (p c₀ c₁ β : ℝ) (f : Stock → ℝ) (x : Stock) : ℝ :=
  p * min x.1 1 + max (β * sext f (leftover x.1)) (ordSup c₀ c₁ β f (leftover x.1))

theorem continuous_invRHS (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) :
    Continuous (invRHS p c₀ c₁ β f) := by
  -- the maximum over the compact `[0, Y]` is continuous in `z` (Theorem 3.6)
  set Y := horizon c₁ β f
  have hY := horizon_pos h f
  set G : ℝ × ℝ → ℝ := fun q => orderVal c₀ c₁ β f q.1 q.2
  have hG : Continuous G :=
    (continuous_const.sub (continuous_const.mul continuous_snd)).add (continuous_const.mul
      ((continuous_sext f.continuous).comp (continuous_fst.add continuous_snd)))
  have hM : Continuous fun z : ℝ => maxValue G (fun _ => Icc 0 Y) z :=
    (theorem_3_6 hG.continuousOn (fun _ => isCompact_Icc)
      (fun z => ⟨⟨0, le_rfl, hY.le⟩, fun y hy xs _ => ⟨0, fun _ => y, fun _ _ => hy,
        tendsto_const_nhds⟩⟩)
      (fun z => ⟨⟨0, le_rfl, hY.le⟩, fun xs _ ys hys => by
        obtain ⟨y, hy, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hys
        exact ⟨y, hy, φ, hφ, hlim⟩⟩)).1
  have heq : invRHS p c₀ c₁ β f = fun x : Stock => p * min x.1 1 +
      max (β * sext f (leftover x.1)) (maxValue G (fun _ => Icc 0 Y) (leftover x.1)) := by
    funext x
    simp only [invRHS]
    rw [ordSup_eq h f]
    rfl
  rw [heq]
  have hl : Continuous fun x : Stock => leftover x.1 :=
    (continuous_subtype_val.sub continuous_const).max continuous_const
  exact (continuous_const.mul (continuous_subtype_val.min continuous_const)).add
    ((continuous_const.mul ((continuous_sext f.continuous).comp hl)).max (hM.comp hl))

theorem abs_invRHS_le (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (x : Stock) :
    |invRHS p c₀ c₁ β f x| ≤ p + β * ‖f‖ := by
  have hp := h.p_pos
  have h1 : 0 ≤ p * min x.1 1 := mul_nonneg hp.le (le_min x.2.out zero_le_one)
  have h2 : p * min x.1 1 ≤ p := mul_le_of_le_one_right hp.le (min_le_right _ _)
  have h3 := abs_sext_le f (leftover x.1)
  have hs : ordSup c₀ c₁ β f (leftover x.1) ≤ -c₀ + β * ‖f‖ :=
    csSup_le ⟨_, 1, by norm_num, rfl⟩
      (by rintro _ ⟨y, hy, rfl⟩; exact orderVal_le h f (le_of_lt hy))
  have hb := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h3) h.β_pos.le
  have hlow : -‖f‖ ≤ sext f (leftover x.1) := by
    have := neg_abs_le (sext f (leftover x.1)); linarith
  have hb' := mul_le_mul_of_nonneg_left hlow h.β_pos.le
  have hnf : 0 ≤ β * ‖f‖ := mul_nonneg h.β_pos.le (norm_nonneg f)
  simp only [invRHS]
  rw [abs_le]
  constructor
  · have := le_max_left (β * sext f (leftover x.1)) (ordSup c₀ c₁ β f (leftover x.1))
    linarith
  · have := max_le hb (hs.trans (by linarith [h.c₀_pos]))
    linarith

/-- The operator `T` of (1) on `C(ℝ₊)`. -/
noncomputable def invT (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) : Stock →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (invRHS p c₀ c₁ β f) (continuous_invRHS h f)
    (p + β * ‖f‖) fun x => by rw [Real.norm_eq_abs]; exact abs_invRHS_le h f x

theorem invT_apply (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (x : Stock) :
    invT h f x = invRHS p c₀ c₁ β f x := rfl

theorem ordSup_mono (h : InvHyp p c₀ c₁ β) {f g : Stock →ᵇ ℝ} (hfg : f ≤ g) (z : ℝ) :
    ordSup c₀ c₁ β f z ≤ ordSup c₀ c₁ β g z := by
  refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  refine le_trans ?_ (le_csSup (bddAbove_ordSup h g z) ⟨y, hy, rfl⟩)
  have hle : f ⟨max (z + y) 0, mem_Ici.2 (le_max_right _ _)⟩ ≤
      g ⟨max (z + y) 0, mem_Ici.2 (le_max_right _ _)⟩ := hfg _
  have := mul_le_mul_of_nonneg_left hle h.β_pos.le
  change -c₀ - c₁ * y + β * f ⟨max (z + y) 0, _⟩ ≤ -c₀ - c₁ * y + β * g ⟨max (z + y) 0, _⟩
  linarith

theorem ordSup_add_const (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (a : ℝ) (z : ℝ) :
    ordSup c₀ c₁ β ⇑(f + const Stock a) z = ordSup c₀ c₁ β f z + β * a := by
  have hval : ∀ y, orderVal c₀ c₁ β ⇑(f + const Stock a) z y =
      orderVal c₀ c₁ β f z y + β * a := fun y => by
    simp only [orderVal, sext, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply]
    ring
  have hbdd := bddAbove_ordSup h f z
  have hne : (orderVal c₀ c₁ β f z '' Ioi 0).Nonempty := ⟨_, 1, by norm_num, rfl⟩
  unfold ordSup
  refine le_antisymm (csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [hval]
    linarith [le_csSup hbdd ⟨y, hy, rfl⟩]
  · have hbdd' := bddAbove_ordSup h (f + const Stock a) z
    have : sSup (orderVal c₀ c₁ β f z '' Ioi 0) ≤
        sSup (orderVal c₀ c₁ β ⇑(f + const Stock a) z '' Ioi 0) - β * a := by
      refine csSup_le hne ?_
      rintro _ ⟨y, hy, rfl⟩
      have := le_csSup hbdd' ⟨y, hy, rfl⟩
      rw [hval] at this
      linarith
    linarith

/-- `T` is a contraction of modulus `β` (Blackwell). -/
theorem invT_contraction (h : InvHyp p c₀ c₁ β) : IsContraction (invT h) β := by
  refine ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun f g hfg x => ?_) (fun f a ha x => ?_)⟩
  · change invRHS p c₀ c₁ β f x ≤ invRHS p c₀ c₁ β g x
    simp only [invRHS]
    have h1 : β * sext f (leftover x.1) ≤ β * sext g (leftover x.1) :=
      mul_le_mul_of_nonneg_left (hfg _) h.β_pos.le
    have h2 := ordSup_mono h hfg (leftover x.1)
    have := max_le_max h1 h2
    linarith
  · change invRHS p c₀ c₁ β ⇑(f + const Stock a) x ≤ invRHS p c₀ c₁ β f x + β * a
    have e : sext ⇑(f + const Stock a) (leftover x.1) = sext f (leftover x.1) + a := by
      simp [sext]
    unfold invRHS
    rw [ordSup_add_const h f a, e, mul_add, max_add_add_right]
    linarith

/-- **Exercise 5.14a.** (1) has a unique solution `v ∈ C(ℝ₊)`, and `0 ≤ v ≤ p/(1 − β)`. -/
theorem ex_5_14a (h : InvHyp p c₀ c₁ β) :
    ∃ v : Stock →ᵇ ℝ, (∀ x, v x = invRHS p c₀ c₁ β v x) ∧
      (∀ w : Stock →ᵇ ℝ, (∀ x, w x = invRHS p c₀ c₁ β w x) → w = v) ∧
      ∀ x, 0 ≤ v x ∧ v x ≤ p / (1 - β) := by
  have : Nonempty (Stock →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (invT_contraction h)
  have h1β : 0 < 1 - β := by linarith [h.β_lt]
  set S : Set (Stock →ᵇ ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ p / (1 - β)}
  have hclosed : IsClosed S := by
    have : S = ⋂ x, {f : Stock →ᵇ ℝ | f x ∈ Icc 0 (p / (1 - β))} := by ext f; simp [S]
    rw [this]
    exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)
  have hmaps : MapsTo (invT h) S S := fun f hf x => by
    rw [invT_apply]
    simp only [invRHS]
    have hp := h.p_pos
    have hz := hf ⟨max (leftover x.1) 0, mem_Ici.2 (le_max_right _ _)⟩
    have h0 : 0 ≤ p * min x.1 1 := mul_nonneg hp.le (le_min x.2.out zero_le_one)
    have h1 : p * min x.1 1 ≤ p := mul_le_of_le_one_right hp.le (min_le_right _ _)
    have hs : ordSup c₀ c₁ β f (leftover x.1) ≤ -c₀ + β * (p / (1 - β)) := by
      refine csSup_le ⟨_, 1, by norm_num, rfl⟩ ?_
      rintro _ ⟨y, hy, rfl⟩
      have h3 := mul_le_mul_of_nonneg_left
        (hf ⟨max (leftover x.1 + y) 0, mem_Ici.2 (le_max_right _ _)⟩).2 h.β_pos.le
      have h4 := mul_pos h.c₁_pos (mem_Ioi.1 hy)
      change -c₀ - c₁ * y + β * f ⟨max (leftover x.1 + y) 0, _⟩ ≤ _
      linarith
    have hm1 := le_max_left (β * sext f (leftover x.1)) (ordSup c₀ c₁ β f (leftover x.1))
    have hz0 : 0 ≤ sext f (leftover x.1) := hz.1
    have hz1 : sext f (leftover x.1) ≤ p / (1 - β) := hz.2
    have hb : β * sext f (leftover x.1) ≤ β * (p / (1 - β)) :=
      mul_le_mul_of_nonneg_left hz1 h.β_pos.le
    have hm2 := max_le hb (hs.trans (by linarith [h.c₀_pos]))
    have hbp : p + β * (p / (1 - β)) = p / (1 - β) := by field_simp; ring
    have hβz := mul_nonneg h.β_pos.le hz0
    exact ⟨by linarith, by linarith⟩
  have hvS : v ∈ S := (corollary_1 (S' := S) (S'' := S) (invT_contraction h) hv
    ⟨0, fun _ => ⟨le_rfl, div_nonneg h.p_pos.le h1β.le⟩⟩ hclosed hmaps hmaps).1
  refine ⟨v, fun x => (DFunLike.congr_fun hv x).symm, fun w hw => ?_, hvS⟩
  exact huniq w (by ext x; exact (hw x).symm)

/-- **Exercise 5.14a.** An optimal ordering policy exists: at every stock either not ordering is
optimal, or some order `y > 0` attains the supremum (and beats not ordering). -/
theorem ex_5_14a_policy (h : InvHyp p c₀ c₁ β) (f : Stock →ᵇ ℝ) (z : ℝ) :
    ordSup c₀ c₁ β f z ≤ β * sext f z ∨
      ∃ y > 0, orderVal c₀ c₁ β f z y = ordSup c₀ c₁ β f z := by
  rcases le_or_gt (ordSup c₀ c₁ β f z) (β * sext f z) with hle | hlt
  · exact Or.inl hle
  right
  have hY := horizon_pos h f
  have hc : ContinuousOn (orderVal c₀ c₁ β f z) (Icc 0 (horizon c₁ β f)) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).add (continuous_const.mul
      ((continuous_sext f.continuous).comp (continuous_const.add continuous_id)))).continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hY.le) hc
  have heq : sSup (orderVal c₀ c₁ β f z '' Icc 0 (horizon c₁ β f)) = orderVal c₀ c₁ β f z y :=
    (IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmax hu⟩)
  have hE := ordSup_eq h f z
  rw [max_eq_right hlt.le, heq] at hE
  have hpos : 0 < y := by
    rcases eq_or_lt_of_le hy.1 with hy0 | hp
    · exfalso
      have h0 : orderVal c₀ c₁ β f z 0 < β * sext f z := by
        simp only [orderVal, add_zero, mul_zero, sub_zero]; linarith [h.c₀_pos]
      rw [← hy0] at hE
      have := le_max_right (β * sext f z) (orderVal c₀ c₁ β f z 0)
      rw [max_eq_left h0.le] at hE
      linarith
    · exact hp
  refine ⟨y, hpos, le_antisymm (le_csSup (bddAbove_ordSup h f z) ⟨y, hpos, rfl⟩) ?_⟩
  have := le_max_right (β * sext f z) (orderVal c₀ c₁ β f z y)
  rw [← hE] at this
  rcases le_total (β * sext f z) (orderVal c₀ c₁ β f z y) with h1 | h1
  · rw [max_eq_right h1] at hE; linarith
  · rw [max_eq_left h1] at hE; linarith

/-! ### Exercise 5.14b–c: the cycle values -/

/-- `r_n = −c₀ − c₁n + β(1 − βⁿ)p/(1 − β)`. -/
noncomputable def rn (p c₀ c₁ β : ℝ) (n : ℕ) : ℝ :=
  -c₀ - c₁ * n + β * (1 - β ^ n) / (1 - β) * p

/-- `Y_n = r_n/(1 − βⁿ)`. -/
noncomputable def Yn (p c₀ c₁ β : ℝ) (n : ℕ) : ℝ := rn p c₀ c₁ β n / (1 - β ^ n)

theorem one_sub_pow_pos (h : InvHyp p c₀ c₁ β) {n : ℕ} (hn : 1 ≤ n) : 0 < 1 - β ^ n := by
  have := pow_lt_one₀ h.β_pos.le h.β_lt (by omega : n ≠ 0)
  linarith

/-- **Exercise 5.14b.** `Y_n = −(c₀ + c₁n)/(1 − βⁿ) + βp/(1 − β)`. -/
theorem Yn_eq (h : InvHyp p c₀ c₁ β) {n : ℕ} (hn : 1 ≤ n) :
    Yn p c₀ c₁ β n = -(c₀ + c₁ * n) / (1 - β ^ n) + β * p / (1 - β) := by
  have h1 := one_sub_pow_pos h hn
  have h2 : 0 < 1 - β := by linarith [h.β_lt]
  simp only [Yn, rn]
  field_simp
  ring

/-- **Exercise 5.14b.** `Y_n → −∞`. -/
theorem tendsto_Yn (h : InvHyp p c₀ c₁ β) : Tendsto (Yn p c₀ c₁ β) atTop atBot := by
  have h2 : 0 < 1 - β := by linarith [h.β_lt]
  -- `Y_n ≤ −c₁n + βp/(1 − β)` since `0 < 1 − βⁿ ≤ 1`
  have hle : ∀ n : ℕ, 1 ≤ n → Yn p c₀ c₁ β n ≤ -(c₁ * n) + β * p / (1 - β) := fun n hn => by
    rw [Yn_eq h hn]
    have h1 := one_sub_pow_pos h hn
    have hb : 1 - β ^ n ≤ 1 := by linarith [pow_nonneg h.β_pos.le n]
    have hnum : 0 ≤ c₀ + c₁ * n :=
      add_nonneg h.c₀_pos.le (mul_nonneg h.c₁_pos.le (Nat.cast_nonneg n))
    have : c₀ + c₁ * n ≤ (c₀ + c₁ * n) / (1 - β ^ n) := by
      rw [le_div_iff₀ h1]; nlinarith
    have : c₁ * n ≤ (c₀ + c₁ * n) / (1 - β ^ n) := by linarith [h.c₀_pos]
    rw [neg_div]
    linarith
  have hlin : Tendsto (fun n : ℕ => -(c₁ * n) + β * p / (1 - β)) atTop atBot := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop h.c₁_pos
    exact tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp this)
  exact tendsto_atBot_mono' atTop (eventually_atTop.2 ⟨1, hle⟩) hlin

/-- **Exercise 5.14b.** There is a finite `N ≥ 1` with `Y_N ≥ Y_n` for all `n ≥ 1`. -/
theorem ex_5_14b (h : InvHyp p c₀ c₁ β) :
    ∃ N, 1 ≤ N ∧ ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_Yn h).eventually_lt_atBot (Yn p c₀ c₁ β 1))
  -- maximize over the finite set `{1, …, max K 1}`
  obtain ⟨N, hN, hmax⟩ := (Finset.Icc 1 (max K 1)).exists_max_image (Yn p c₀ c₁ β)
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, le_max_right _ _⟩⟩
  refine ⟨N, (Finset.mem_Icc.1 hN).1, fun n hn => ?_⟩
  rcases le_or_gt n (max K 1) with hnK | hnK
  · exact hmax n (Finset.mem_Icc.2 ⟨hn, hnK⟩)
  · exact (hK n (le_of_max_le_left hnK.le)).le.trans
      (hmax 1 (Finset.mem_Icc.2 ⟨le_rfl, le_max_right _ _⟩))

/-- **Exercise 5.14b.** The optimal cycle does not depend on the price `p`. -/
theorem argmax_Yn_indep_p {p' : ℝ} (h : InvHyp p c₀ c₁ β) (h' : InvHyp p' c₀ c₁ β) {N : ℕ}
    (hN : 1 ≤ N) (hmax : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N) :
    ∀ n, 1 ≤ n → Yn p' c₀ c₁ β n ≤ Yn p' c₀ c₁ β N := fun n hn => by
  have := hmax n hn
  rw [Yn_eq h hn, Yn_eq h hN] at this
  rw [Yn_eq h' hn, Yn_eq h' hN]
  linarith

/-- **Exercise 5.14b.** A larger fixed cost calls for a longer cycle: if `N` is optimal for `c₀`
and `N'` for `c₀' > c₀`, then `N ≤ N'` unless both are optimal for both (increasing differences:
`1/(1 − βⁿ)` falls with `n`). -/
theorem argmax_Yn_mono_c0 {c₀' : ℝ} (h : InvHyp p c₀ c₁ β) (h' : InvHyp p c₀' c₁ β) (hc : c₀ < c₀')
    {N N' : ℕ} (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hmax : ∀ n, 1 ≤ n → Yn p c₀ c₁ β n ≤ Yn p c₀ c₁ β N)
    (hmax' : ∀ n, 1 ≤ n → Yn p c₀' c₁ β n ≤ Yn p c₀' c₁ β N') : N ≤ N' := by
  by_contra hlt
  push Not at hlt
  have e1 := hmax N' hN'
  have e2 := hmax' N hN
  rw [Yn_eq h hN', Yn_eq h hN] at e1
  rw [Yn_eq h' hN, Yn_eq h' hN'] at e2
  -- adding the two optimality conditions leaves `(c₀' − c₀)(1/(1 − β^{N'}) − 1/(1 − β^N)) ≤ 0`
  have hA := one_sub_pow_pos h hN
  have hB := one_sub_pow_pos h hN'
  have hpow : β ^ N < β ^ N' := pow_lt_pow_right_of_lt_one₀ h.β_pos h.β_lt hlt
  have hlt' : 1 / (1 - β ^ N) < 1 / (1 - β ^ N') := one_div_lt_one_div_of_lt hB (by linarith)
  have key : (c₀' - c₀) * (1 / (1 - β ^ N')) ≤ (c₀' - c₀) * (1 / (1 - β ^ N)) := by
    have e : ∀ a b : ℝ, -(a + b) / (1 - β ^ N) = -(a + b) * (1 / (1 - β ^ N)) := fun a b => by
      ring
    have e' : ∀ a b : ℝ, -(a + b) / (1 - β ^ N') = -(a + b) * (1 / (1 - β ^ N')) := fun a b => by
      ring
    rw [e, e'] at e1 e2
    nlinarith
  have := mul_lt_mul_of_pos_left hlt' (by linarith : 0 < c₀' - c₀)
  linarith

/-- **Exercise 5.14c.** With `Y_N > 0`, `A = (1 − β)Y_N/(βp − c₁) ∈ (0, 1)`; `A < 1` holds for
every `N ≥ 1`, because `1 − β^N ≤ N(1 − β)` and `c₀ > 0`. -/
theorem ex_5_14c (h : InvHyp p c₀ c₁ β) {N : ℕ} (hN : 1 ≤ N) (hY : 0 < Yn p c₀ c₁ β N) :
    0 < (1 - β) * Yn p c₀ c₁ β N / (β * p - c₁) ∧
      (1 - β) * Yn p c₀ c₁ β N / (β * p - c₁) < 1 := by
  have h2 : 0 < 1 - β := by linarith [h.β_lt]
  have hm : 0 < β * p - c₁ := by linarith [h.margin]
  refine ⟨div_pos (mul_pos h2 hY) hm, ?_⟩
  rw [div_lt_one hm, Yn_eq h hN]
  have h1 := one_sub_pow_pos h hN
  -- `1 − β^N ≤ N(1 − β)` (Bernoulli)
  have hbern : 1 - β ^ N ≤ N * (1 - β) := by
    have := one_add_mul_le_pow (show -2 ≤ -(1 - β) by linarith [h.β_pos]) N
    rw [show (1 : ℝ) + -(1 - β) = β by ring] at this
    linarith
  have hkey : c₁ * (1 - β ^ N) < (1 - β) * (c₀ + c₁ * N) := by nlinarith [h.c₀_pos, h.c₁_pos]
  have e : (1 - β) * (-(c₀ + c₁ * N) / (1 - β ^ N) + β * p / (1 - β)) =
      (1 - β) * -(c₀ + c₁ * N) / (1 - β ^ N) + β * p := by
    field_simp
  rw [e]
  have : (1 - β) * -(c₀ + c₁ * N) / (1 - β ^ N) < -c₁ := by
    rw [div_lt_iff₀ h1]; nlinarith
  linarith

end StokeyLucasPrescott.DeterministicApplications
