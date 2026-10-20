/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorSecurities

/-!
# Pricing securities: the envelope condition and the pricing equations (Ex 16.2(d), (g))

SLP §16.2, pp. 483–484, in the finite-shock setting of `ManySectorSecurities`.

* `ms_bs_envelope`: the one-dimensional Benveniste–Scheinkman lemma (Theorem 4.10): a concave
  function with a differentiable minorant touching it at `0` is differentiable at `0`, with the
  minorant's derivative.
* `ms_sec_fixed_concave`: with `U` concave, the solution of (1) is concave in `A` on each slice
  `{A ≥ q(s)B − c(s)}` of `D`.
* **Exercise 16.2(d), corrected** (`ex_16_2d`): if `b*` is optimal at `A = 0` in state `ŝ` and
  consumption `c(ŝ) − q(ŝ)b*` is positive, then `w(·, ŝ)` is differentiable at `0` with
  `w₁(0, ŝ) = U′(c(ŝ) − q(ŝ) b*) = U′(c(ŝ) + δ*(0))`; and (`ex_16_2d_iff`) this equals `U′(c(ŝ))`
  iff `b* = 0`.
* `ms_sec_foc`: the first-order condition for (1) at an interior optimum `b = 0`.
* **The pricing equations (2) and (3)** (`ex_16_2_eq2`; `ex_16_2g` with return
  `R = f(s′) + q(s′)`): if `b = 0` is optimal at `A = 0` in every state ("in equilibrium
  `A = b = 0`"), then `q(s) U′(c(s)) = β Σ_{z′} π(s, z′) U′(c(s′)) R(s, z′)`.
* **Counterexample to (d) as stated** (`ex_16_2d_counterexample`): in a constant-state economy with
  a riskless bond (`R = 1`) and a price `q ≠ β` (not the equilibrium price (2)), `b = 0` is not
  optimal at `A = 0`, and for every optimal `b*` with positive consumption `w₁(0) ≠ U′(c)`.

**Corrections (NOTE to Ex 16.2d).** `w₁(0, x̂, ẑ) = U′[c(x̂, ẑ)]` holds only if `b = 0` is optimal
at `A = 0`, i.e. when `q` is the equilibrium price; in general `w₁(0) = U′(c + δ*(0))`. Concavity of
`w(·, s)` and positive consumption at the optimum are also needed (and proved/assumed here). The
derivation of (2) on p. 483 is therefore a consistency condition: (2) is necessary for no trade.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped BoundedContinuousFunction

/-! ### The Benveniste–Scheinkman lemma -/

/-- **Benveniste–Scheinkman, one dimension**: if `W` is concave on `(−r, r)`, `L ≤ W` there,
`L(0) = W(0)` and `L′(0) = d`, then `W′(0) = d`. (Squeeze of the difference quotients: for
`h > 0`, `(L(h) − L(0))/h ≤ (W(h) − W(0))/h ≤ (W(0) − W(−h))/h ≤ (L(0) − L(−h))/h`.) -/
theorem ms_bs_envelope {W L : ℝ → ℝ} {d r : ℝ} (hr : 0 < r) (hW : ConcaveOn ℝ (Ioo (-r) r) W)
    (hL : ∀ A ∈ Ioo (-r) r, L A ≤ W A) (h0 : L 0 = W 0) (hd : HasDerivAt L d 0) :
    HasDerivAt W d 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hd ⊢
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.tendsto' 0 0 neg_zero).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun x hx => by
        rw [mem_compl_singleton_iff, neg_ne_zero]; exact (mem_Ioi.1 hx).ne'⟩
  have hneg' : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.tendsto' 0 0 neg_zero).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun x hx => by
        rw [mem_compl_singleton_iff, neg_ne_zero]; exact (mem_Iio.1 hx).ne⟩
  rw [← nhdsLT_sup_nhdsGT]
  refine Tendsto.sup ?_ ?_
  · -- `h < 0`
    have hup : Tendsto (slope L 0) (𝓝[<] 0) (𝓝 d) :=
      hd.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
    have hlow : Tendsto (fun h => slope L 0 (-h)) (𝓝[<] 0) (𝓝 d) := hd.comp hneg'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show -r < 0 by linarith)] with h hh
      have hhm : h ∈ Ioo (-r) r := ⟨hh.1, by linarith [hh.2]⟩
      have hhm' : -h ∈ Ioo (-r) r := ⟨by linarith [hh.2], by linarith [hh.1]⟩
      have hc := hW.slope_anti_adjacent hhm hhm' hh.2 (by linarith [hh.2])
      have hl := hL (-h) hhm'
      rw [slope_def_field, slope_def_field]
      have e1 : (W (-h) - W 0) / (-h - 0) ≤ (W 0 - W h) / (0 - h) := hc
      have hpos : 0 < -h := by linarith [hh.2]
      calc (L (-h) - L 0) / (-h - 0) ≤ (W (-h) - W 0) / (-h - 0) := by
            apply div_le_div_of_nonneg_right _ (by linarith); linarith
        _ ≤ (W 0 - W h) / (0 - h) := e1
        _ = (W h - W 0) / (h - 0) := by
            rw [show (0 : ℝ) - h = -(h - 0) by ring, div_neg, ← neg_div, neg_sub]
    · filter_upwards [Ioo_mem_nhdsLT (show -r < 0 by linarith)] with h hh
      have hhm : h ∈ Ioo (-r) r := ⟨hh.1, by linarith [hh.2]⟩
      have hl := hL h hhm
      rw [slope_def_field, slope_def_field]
      exact div_le_div_of_nonpos_of_le (by linarith [hh.2]) (by linarith)
  · -- `h > 0`
    have hlow : Tendsto (slope L 0) (𝓝[>] 0) (𝓝 d) :=
      hd.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    have hup : Tendsto (fun h => slope L 0 (-h)) (𝓝[>] 0) (𝓝 d) := hd.comp hneg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hr] with h hh
      have hhm : h ∈ Ioo (-r) r := ⟨by linarith [hh.1], hh.2⟩
      have hl := hL h hhm
      rw [slope_def_field, slope_def_field]
      apply div_le_div_of_nonneg_right _ (by linarith [hh.1])
      linarith
    · filter_upwards [Ioo_mem_nhdsGT hr] with h hh
      have hhm : h ∈ Ioo (-r) r := ⟨by linarith [hh.1], hh.2⟩
      have hhm' : -h ∈ Ioo (-r) r := ⟨by linarith [hh.2], by linarith [hh.1]⟩
      have hc := hW.slope_anti_adjacent hhm' hhm (by linarith [hh.1]) hh.1
      have hl := hL (-h) hhm'
      rw [slope_def_field, slope_def_field]
      have e1 : (W h - W 0) / (h - 0) ≤ (W 0 - W (-h)) / (0 - -h) := hc
      calc (W h - W 0) / (h - 0) ≤ (W 0 - W (-h)) / (0 - -h) := e1
        _ ≤ (L 0 - L (-h)) / (0 - -h) := by
            apply div_le_div_of_nonneg_right _ (by linarith [hh.1]); linarith
        _ = (L (-h) - L 0) / (-h - 0) := by
            rw [show (0 : ℝ) - -h = -(-h - 0) by ring, div_neg, ← neg_div, neg_sub]

/-- With `U` strictly concave and differentiable on `(0, ∞)`, `U′` is strictly decreasing. -/
theorem ms_dU_strictAnti {U dU : ℝ → ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hd : ∀ x, 0 < x → HasDerivAt U (dU x) x) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    dU y < dU x := by
  set m := (x + y) / 2
  have hxm : x < m := by simp only [m]; linarith
  have hmy : m < y := by simp only [m]; linarith
  have hs := (strictConcaveOn_iff_slope_strict_anti_adjacent.1 hU).2 (mem_Ici.2 hx.le)
    (mem_Ici.2 (by linarith)) hxm hmy
  have h1 := hU.concaveOn.le_slope_of_hasDerivAt (mem_Ici.2 (by linarith : (0 : ℝ) ≤ m))
    (mem_Ici.2 (by linarith)) hmy (hd y (by linarith))
  have h2 := hU.concaveOn.slope_le_of_hasDerivAt (mem_Ici.2 hx.le)
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ m)) hxm (hd x hx)
  rw [slope_def_field] at h1 h2
  linarith

/-! ### Concavity of the solution of (1) -/

variable {Sx : Type*} [TopologicalSpace Sx] {Zf : Type*} [Fintype Zf]
  {U : ℝ → ℝ} {c q : Sx → ℝ} {R π : Sx → Zf → ℝ} {nxt : Sx → Zf → Sx} {B β : ℝ}

/-- `w(·, s)` is concave on the slice `{A ≥ q(s)B − c(s)}` of `D`, for every `s`. -/
def MsSecConcave (c q : Sx → ℝ) (B : ℝ) (w : ℝ × Sx → ℝ) : Prop :=
  ∀ s (A₁ A₂ θ : ℝ), q s * B - c s ≤ A₁ → q s * B - c s ≤ A₂ → 0 ≤ θ → θ ≤ 1 →
    θ * w (A₁, s) + (1 - θ) * w (A₂, s) ≤ w (θ * A₁ + (1 - θ) * A₂, s)

/-- The operator of (1) preserves concavity in `A` when `U` is concave on `ℝ₊`. -/
theorem msSecT_concave (D : MsSecData U c q R π nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {w : ℝ × Sx → ℝ} (hw : Continuous w) (hcv : MsSecConcave c q B w) :
    MsSecConcave c q B (msSecT U c q R π nxt B β w) := by
  intro s A₁ A₂ θ h1 h2 h0 hθ
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hq := D.q_pos s
  obtain ⟨r₁, hr₁, e₁⟩ := msSecT_attained D hw (A₁, s)
  obtain ⟨r₂, hr₂, e₂⟩ := msSecT_attained D hw (A₂, s)
  set b₁ := msSecB c q B A₁ s r₁
  set b₂ := msSecB c q B A₂ s r₂
  obtain ⟨f₁, g₁⟩ := msSecB_feasible D h1 hr₁
  obtain ⟨f₂, g₂⟩ := msSecB_feasible D h2 hr₂
  set A := θ * A₁ + (1 - θ) * A₂
  set b := θ * b₁ + (1 - θ) * b₂
  have hA : q s * B - c s ≤ A := by nlinarith
  have hbB : B ≤ b := by nlinarith
  have hbf : q s * b ≤ c s + A := by
    simp only [b, A]
    nlinarith [mul_le_mul_of_nonneg_left g₁ h0, mul_le_mul_of_nonneg_left g₂ hθ']
  obtain ⟨r, hr, hrb⟩ := msSecB_surj D hA hbB hbf
  have hge := msSecT_ge D hw (A, s) hr
  rw [hrb] at hge
  have hUc := hU.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c s + A₁ - q s * b₁))
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c s + A₂ - q s * b₂)) h0 hθ' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcons : θ * (c s + A₁ - q s * b₁) + (1 - θ) * (c s + A₂ - q s * b₂) = c s + A - q s * b := by
    simp only [b, A]; ring
  rw [hcons] at hUc
  have hsum : θ * ∑ z', π s z' * w (b₁ * R s z', nxt s z') +
      (1 - θ) * ∑ z', π s z' * w (b₂ * R s z', nxt s z') ≤
      ∑ z', π s z' * w (b * R s z', nxt s z') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    have hc := hcv (nxt s z') (b₁ * R s z') (b₂ * R s z') θ (ms_sec_next_mem D s f₁ z')
      (ms_sec_next_mem D s f₂ z') h0 hθ
    have e : θ * (b₁ * R s z') + (1 - θ) * (b₂ * R s z') = b * R s z' := by simp only [b]; ring
    rw [e] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (D.π_nonneg s z')]
  rw [e₁, e₂]
  simp only [msSecObj] at hge ⊢
  nlinarith [mul_le_mul_of_nonneg_left hsum D.beta_pos.le]

/-- **The solution of (1) is concave in `A`** on each slice of `D` (as the limit of iterates
`Tⁿ(0)`, each concave), when `U` is concave on `ℝ₊`. -/
theorem ms_sec_fixed_concave (D : MsSecData U c q R π nxt B β) (hU : ConcaveOn ℝ (Ici 0) U) :
    MsSecConcave c q B ⇑(ContractingWith.fixedPoint (α := ℝ × Sx →ᵇ ℝ) (msSecTB D)
      (ms_secTB_contracting D)) := by
  have hit : ∀ m, MsSecConcave c q B ((msSecTB D)^[m] 0) := by
    intro m
    induction m with
    | zero =>
      intro s A₁ A₂ θ _ _ _ _
      simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact msSecT_concave D hU (BoundedContinuousFunction.continuous _) ih
  have hlim := (ms_secTB_contracting D).tendsto_iterate_fixedPoint 0
  intro s A₁ A₂ θ h1 h2 h0 hθ
  have ev : ∀ p, Tendsto (fun n => (msSecTB D)^[n] 0 p) atTop
      (𝓝 (ContractingWith.fixedPoint (α := ℝ × Sx →ᵇ ℝ) (msSecTB D)
        (ms_secTB_contracting D) p)) := fun p =>
    ((continuous_eval_const p).tendsto _).comp hlim
  exact le_of_tendsto_of_tendsto' (((ev (A₁, s)).const_mul θ).add ((ev (A₂, s)).const_mul
    (1 - θ))) (ev _) fun n => hit n s A₁ A₂ θ h1 h2 h0 hθ

/-! ### Exercise 16.2(d) -/

/-- **Exercise 16.2(d), corrected (envelope condition)**: let `w` satisfy (1) and be concave in `A`.
If `c(ŝ) > 0`, `b*` is optimal at `(0, ŝ)` and consumption `c(ŝ) − q(ŝ) b*` is positive, then
`w(·, ŝ)` is differentiable at `0` with `w₁(0, ŝ) = U′(c(ŝ) − q(ŝ) b*)`. -/
theorem ex_16_2d (D : MsSecData U c q R π nxt B β) {dU : ℝ → ℝ}
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) (hcv : MsSecConcave c q B w) {s : Sx}
    {b : ℝ} (hb : B ≤ b) (hopt : w (0, s) = msSecObj U c q R π nxt β w 0 s b)
    (hcons : 0 < c s - q s * b) :
    HasDerivAt (fun A => w (A, s)) (dU (c s - q s * b)) 0 := by
  have hq := D.q_pos s
  have hm1 : 0 < c s - q s * B := by nlinarith [D.B_neg]
  set r := min (c s - q s * B) (c s - q s * b) with hr
  have hr0 : 0 < r := lt_min hm1 hcons
  have hsl : ∀ A ∈ Ioo (-r) r, q s * B - c s ≤ A := fun A hA => by
    linarith [hA.1, min_le_left (c s - q s * B) (c s - q s * b)]
  have hfe : ∀ A ∈ Ioo (-r) r, q s * b ≤ c s + A := fun A hA => by
    linarith [hA.1, min_le_right (c s - q s * B) (c s - q s * b)]
  set L : ℝ → ℝ := fun A => msSecObj U c q R π nxt β w A s b with hL
  have hcvW : ConcaveOn ℝ (Ioo (-r) r) fun A => w (A, s) := by
    refine ⟨convex_Ioo _ _, fun x hx y hy a a' ha ha' haa => ?_⟩
    obtain rfl : a' = 1 - a := by linarith
    simpa only [smul_eq_mul] using hcv s x y a (hsl x hx) (hsl y hy) ha (by linarith)
  have hLd : HasDerivAt L (dU (c s - q s * b)) 0 := by
    have hin : HasDerivAt (fun A : ℝ => c s + A - q s * b) 1 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (c s)).sub_const _
    have hU' : HasDerivAt U (dU (c s - q s * b)) (c s + 0 - q s * b) := by
      rw [add_zero]; exact hdU _ hcons
    have := (hU'.comp (0 : ℝ) hin).add_const
      (β * ∑ z', π s z' * w (b * R s z', nxt s z'))
    simpa [hL, msSecObj, Function.comp_def] using this
  exact ms_bs_envelope hr0 hcvW (fun A hA => (hw A s (hsl A hA)).1 b hb (hfe A hA))
    (by exact hopt.symm) hLd

/-- `U′(c − q b*) = U′(c)` iff `b* = 0` (for `U` strictly concave, `q > 0`, positive
consumption): so `w₁(0) = U′(c)` iff there is no trade at `A = 0`. -/
theorem ex_16_2d_iff {dU : ℝ → ℝ} (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {cs qs b : ℝ} (hc : 0 < cs) (hq : 0 < qs)
    (hcons : 0 < cs - qs * b) : dU (cs - qs * b) = dU cs ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    rcases lt_or_gt_of_ne hb with hlt | hgt
    · have := ms_dU_strictAnti hU hdU hc (by nlinarith : cs < cs - qs * b)
      linarith
    · have := ms_dU_strictAnti hU hdU hcons (by nlinarith : cs - qs * b < cs)
      linarith
  · rintro rfl
    rw [mul_zero, sub_zero]

/-- **The first-order condition for (1)**: if `b = 0` is optimal at `(0, s)` with `c(s) > 0`, and
each `w(·, s′)` has derivative `D(z′)` at `0`, then
`q(s) U′(c(s)) = β Σ π(s, z′) D(z′) R(s, z′)`. -/
theorem ms_sec_foc (D : MsSecData U c q R π nxt B β) {dU : ℝ → ℝ}
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) {s : Sx} (hc : 0 < c s)
    (hopt : w (0, s) = msSecObj U c q R π nxt β w 0 s 0) {Dw : Zf → ℝ}
    (hD : ∀ z', HasDerivAt (fun A => w (A, nxt s z')) (Dw z') 0) :
    q s * dU (c s) = β * ∑ z', π s z' * (Dw z' * R s z') := by
  have hq := D.q_pos s
  have hdom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg]
  set Ψ : ℝ → ℝ := fun b => msSecObj U c q R π nxt β w 0 s b with hΨ
  have hmax : IsLocalMax Ψ 0 := by
    have h1 : ∀ᶠ b in 𝓝 (0 : ℝ), B < b := (tendsto_id).eventually_const_lt D.B_neg
    have h2 : ∀ᶠ b in 𝓝 (0 : ℝ), q s * b < c s + 0 := by
      have : Tendsto (fun b : ℝ => q s * b) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (q s)
      exact this.eventually_lt_const (by linarith)
    filter_upwards [h1, h2] with b hb1 hb2
    have := (hw 0 s hdom).1 b hb1.le hb2.le
    simp only [hΨ]
    rw [← hopt]
    exact this
  have hin : HasDerivAt (fun b : ℝ => c s + 0 - q s * b) (-(q s)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (q s)).const_sub (c s + 0)
  have hU' : HasDerivAt U (dU (c s)) (c s + 0 - q s * 0) := by
    simp only [add_zero, mul_zero, sub_zero]; exact hdU _ hc
  have hsum : HasDerivAt (fun b : ℝ => ∑ z', π s z' * w (b * R s z', nxt s z'))
      (∑ z', π s z' * (Dw z' * R s z')) 0 := by
    refine HasDerivAt.fun_sum fun z' _ => HasDerivAt.const_mul _ ?_
    have hinner : HasDerivAt (fun b : ℝ => b * R s z') (R s z') 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (R s z')
    have hD' : HasDerivAt (fun A => w (A, nxt s z')) (Dw z') (0 * R s z') := by
      rw [zero_mul]; exact hD z'
    exact hD'.comp (0 : ℝ) hinner
  have hΨd : HasDerivAt Ψ (dU (c s) * -(q s) + β * ∑ z', π s z' * (Dw z' * R s z')) 0 := by
    have hΨeq : Ψ = (fun b => U (c s + 0 - q s * b)) +
        fun b => β * ∑ z', π s z' * w (b * R s z', nxt s z') := by
      funext b; rfl
    rw [hΨeq]
    exact (hU'.comp (0 : ℝ) hin).add (hsum.const_mul β)
  have := hmax.hasDerivAt_eq_zero hΨd
  linarith

/-- **The pricing equation (2)** (p. 483), and in general for any return `R`: if `c > 0` everywhere
and `b = 0` is optimal at `A = 0` in every state (no trade, "in equilibrium `A = b = 0`"), then
`U′[c(s)] q(s) = β Σ_{z′} π(s, z′) U′(c[s′]) R(s, z′)` in every state. With `R(s, z′) = f(z′)` this
is (2). -/
theorem ex_16_2_eq2 (D : MsSecData U c q R π nxt B β)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) (hcv : MsSecConcave c q B w) (hc : ∀ s, 0 < c s)
    (hopt : ∀ s, w (0, s) = msSecObj U c q R π nxt β w 0 s 0) (s : Sx) :
    q s * dU (c s) = β * ∑ z', π s z' * (dU (c (nxt s z')) * R s z') := by
  refine ms_sec_foc D hdU hw (hc s) (hopt s) fun z' => ?_
  have hq := D.q_pos (nxt s z')
  have hpos : 0 < c (nxt s z') - q (nxt s z') * 0 := by
    rw [mul_zero, sub_zero]; exact hc _
  have := ex_16_2d D hdU hw hcv D.B_neg.le (hopt _) hpos
  rwa [mul_zero, sub_zero] at this

/-- **Exercise 16.2(g)**: for an asset paying the dividend `f(s′)` each period with ex-dividend
price `q`, the consumer's equation (1′) has return `R(s, z′) = f(s′) + q(s′)`, and no trade in
every state gives (3): `U′[c(s)] q(s) = β Σ_{z′} π(s, z′) U′(c[s′]) {f[s′] + q[s′]}`. -/
theorem ex_16_2g {f : Sx → ℝ}
    (D : MsSecData U c q (fun s z' => f (nxt s z') + q (nxt s z')) π nxt B β)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q (fun s z' => f (nxt s z') + q (nxt s z')) π nxt B β w)
    (hcv : MsSecConcave c q B w) (hc : ∀ s, 0 < c s)
    (hopt : ∀ s, w (0, s) =
      msSecObj U c q (fun s z' => f (nxt s z') + q (nxt s z')) π nxt β w 0 s 0) (s : Sx) :
    dU (c s) * q s = β * ∑ z', π s z' * (dU (c (nxt s z')) * (f (nxt s z') + q (nxt s z'))) := by
  rw [mul_comm]
  exact ex_16_2_eq2 D hdU hw hcv hc hopt s

/-- **Counterexample to Ex 16.2(d) as stated**: a constant state, a riskless bond (`R = 1`) and a
price `q ≠ β` (so `q` does not satisfy (2), which here reads `q = β`). For any solution `w` of (1),
concave in `A`: `b = 0` is **not** optimal at `A = 0`; and for every optimal `b*` with positive
consumption, `w₁(0) ≠ U′(c)`. -/
theorem ex_16_2d_counterexample {c₀ q₀ : ℝ}
    (D : MsSecData U (fun _ : Unit => c₀) (fun _ => q₀) (fun _ (_ : Unit) => (1 : ℝ))
      (fun _ (_ : Unit) => (1 : ℝ)) (fun s (_ : Unit) => s) B β)
    (hU : StrictConcaveOn ℝ (Ici 0) U) {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x)
    (hdUpos : ∀ x, 0 < x → 0 < dU x) (hc : 0 < c₀) (hqβ : q₀ ≠ β) {w : ℝ × Unit → ℝ}
    (hw : MsSecBellman U (fun _ => c₀) (fun _ => q₀) (fun _ (_ : Unit) => (1 : ℝ))
      (fun _ (_ : Unit) => (1 : ℝ)) (fun s (_ : Unit) => s) B β w)
    (hcv : MsSecConcave (fun _ => c₀) (fun _ => q₀) B w) :
    w (0, ()) ≠ msSecObj U (fun _ => c₀) (fun _ => q₀) (fun _ (_ : Unit) => (1 : ℝ))
        (fun _ (_ : Unit) => (1 : ℝ)) (fun s (_ : Unit) => s) β w 0 () 0 ∧
      ∀ b, B ≤ b → q₀ * b ≤ c₀ + 0 →
        w (0, ()) = msSecObj U (fun _ => c₀) (fun _ => q₀) (fun _ (_ : Unit) => (1 : ℝ))
          (fun _ (_ : Unit) => (1 : ℝ)) (fun s (_ : Unit) => s) β w 0 () b → 0 < c₀ - q₀ * b →
        ¬ HasDerivAt (fun A => w (A, ())) (dU c₀) 0 := by
  have hq := D.q_pos ()
  have hnot : w (0, ()) ≠ msSecObj U (fun _ => c₀) (fun _ => q₀) (fun _ (_ : Unit) => (1 : ℝ))
      (fun _ (_ : Unit) => (1 : ℝ)) (fun s (_ : Unit) => s) β w 0 () 0 := by
    intro h0
    have hpos : 0 < c₀ - q₀ * 0 := by rw [mul_zero, sub_zero]; exact hc
    have hder := ex_16_2d D hdU hw hcv (s := ()) D.B_neg.le h0 hpos
    simp only [mul_zero, sub_zero] at hder
    have hfoc := ms_sec_foc D hdU hw (s := ()) hc h0 (Dw := fun _ => dU c₀) fun _ => hder
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, one_mul] at hfoc
    have hpos := hdUpos c₀ hc
    exact hqβ (mul_right_cancel₀ hpos.ne' (by linarith))
  refine ⟨hnot, fun b hb _ hopt hcons hd => ?_⟩
  have hder := ex_16_2d D hdU hw hcv (s := ()) hb hopt hcons
  have heq := hder.unique hd
  have hb0 := (ex_16_2d_iff hU hdU hc hq hcons).1 heq
  subst hb0
  exact hnot hopt

end StokeyLucasPrescott.EquilibriumApplications
