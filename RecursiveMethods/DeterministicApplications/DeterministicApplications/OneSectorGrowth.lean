/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.Concavity

/-!
# The one-sector model of optimal growth

SLP §5.1, pp. 103–105: `max Σ βᵗU[f(x_t) − x_{t+1}]` subject to `0 ≤ x_{t+1} ≤ f(x_t)`, on the
set `X = [0, x̄]` of maintainable capital stocks.

* `GrowthHyp`: (U1)–(U3) and (T1)–(T3) on `X`.
* `growthΓ`, `growthF`: `Γ(x) = [0, f(x)]` and `F(x, y) = U(f(x) − y)` on `X`.
* `growth_assumption43`, `growth_assumption44`, `growth_a45`, `growth_a46` (Ex 5.1a–b):
  Assumptions 4.3–4.6 hold, and with them Assumptions 4.1–4.2 (`growth_assumption41`,
  `growth_assumption42`).
* `ex_5_1ab`: there is a unique bounded continuous `v` satisfying (2). It is `v*`, it is strictly
  increasing, and the policy correspondence is nonempty and u.h.c.
* `growth_a47`, `growth_a48`, `ex_5_1c` (Ex 5.1c): with `U` strictly concave and `f` strictly
  concave, Assumptions 4.7–4.8 hold, `v` is strictly concave and the policy is a continuous
  function. `ex_5_1c_weak_counterexample`: with `f` only weakly concave, as (T4) allows,
  Assumption 4.7 can fail.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- (U1)–(U3) and (T1)–(T3) of SLP §5.1 (p. 104), on `X = [0, x̄]`. The second half of (T2),
`f(x) < x` for `x > x̄`, only explains why the state space can be cut down to `X`; the analysis
on `X` does not use it, and leaving it out lets `f(k) = k` (Section 5.2) fit as well. -/
structure GrowthHyp (U f : ℝ → ℝ) (β xbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  xbar_pos : 0 < xbar
  f_maintain : ∀ x ∈ Icc 0 xbar, x ≤ f x ∧ f x ≤ xbar
  f_mono : StrictMonoOn f (Ici 0)

variable {U f : ℝ → ℝ} {β xbar : ℝ}

/-- `Γ(x) = [0, f(x)]` on `X = [0, x̄]`. -/
def growthΓ (f : ℝ → ℝ) (xbar : ℝ) (x : Icc (0 : ℝ) xbar) : Set (Icc (0 : ℝ) xbar) :=
  {y | y.1 ≤ f x.1}

/-- `F(x, y) = U(f(x) − y)`. -/
def growthF (U f : ℝ → ℝ) (xbar : ℝ) (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar) : ℝ :=
  U (f p.1.1 - p.2.1)

theorem growth_f_nonneg (h : GrowthHyp U f β xbar) (x : Icc (0 : ℝ) xbar) : 0 ≤ f x.1 :=
  x.2.1.trans (h.f_maintain x.1 x.2).1

theorem continuous_growth_f (h : GrowthHyp U f β xbar) :
    Continuous fun x : Icc (0 : ℝ) xbar => f x.1 :=
  h.f_cont.comp_continuous continuous_subtype_val fun x => x.2.1

/-- Assumption 4.3 (Ex 5.1a–b, via Exercise 3.13): `Γ` is nonempty, compact-valued and
continuous. -/
theorem growth_assumption43 (h : GrowthHyp U f β xbar) : Assumption43 (growthΓ f xbar) := by
  have hcf := continuous_growth_f h
  have hclosed : ∀ x, IsClosed (growthΓ f xbar x) := fun x =>
    isClosed_le continuous_subtype_val continuous_const
  refine ⟨fun x => ⟨⟨0, le_rfl, h.xbar_pos.le⟩, growth_f_nonneg h x⟩,
    fun x => (hclosed x).isCompact, fun x => ⟨⟨⟨0, le_rfl, h.xbar_pos.le⟩, growth_f_nonneg h x⟩,
      fun y hy xs hxs => ?_⟩, fun x => ⟨⟨⟨0, le_rfl, h.xbar_pos.le⟩, growth_f_nonneg h x⟩,
      fun xs hxs ys hys => ?_⟩⟩
  · -- l.h.c.: `yₙ = min{y, f(xₙ)}`
    refine ⟨0, fun n => ⟨min y.1 (f (xs n).1), le_min y.2.1 (growth_f_nonneg h _),
      (min_le_left _ _).trans y.2.2⟩,
      fun n _ => show min y.1 (f (xs n).1) ≤ f (xs n).1 from min_le_right _ _, ?_⟩
    have hlim := (tendsto_const_nhds (x := y.1)).min ((hcf.tendsto x).comp hxs)
    rw [min_eq_left hy] at hlim
    exact tendsto_subtype_rng.2 hlim
  · -- u.h.c.: `X` is compact and `{(x, y) : y ≤ f(x)}` is closed
    obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
    refine ⟨y, ?_, φ, hφ, hlim⟩
    exact le_of_tendsto_of_tendsto ((continuous_subtype_val.tendsto y).comp hlim)
      ((hcf.tendsto x).comp (hxs.comp hφ.tendsto_atTop))
      (Eventually.of_forall fun n => hys (φ n))

/-- Assumption 4.4 (Ex 5.1a–b): `F` is bounded and continuous on the graph and `0 < β < 1`. -/
theorem growth_assumption44 (h : GrowthHyp U f β xbar) :
    Assumption44 (growthΓ f xbar) (growthF U f xbar) β := by
  have hcf := continuous_growth_f h
  have hcons : ∀ p ∈ graph (growthΓ f xbar), f p.1.1 - p.2.1 ∈ Icc 0 xbar := fun p hp =>
    ⟨sub_nonneg.2 hp, by linarith [p.2.2.1, (h.f_maintain p.1.1 p.1.2).2]⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.U_cont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) xbar ⊆ Ici 0))
  refine ⟨?_, ⟨B, fun p hp => (Real.norm_eq_abs _).symm.le.trans (hB _ (hcons p hp))⟩,
    h.β_pos, h.β_lt⟩
  refine h.U_cont.comp (((hcf.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).continuousOn) fun p hp => (hcons p hp).1

/-- Assumption 4.5: `F(·, y)` is strictly increasing. -/
theorem growth_a45 (h : GrowthHyp U f β xbar) (x x' y : Icc (0 : ℝ) xbar) (hxx' : x < x')
    (hy : y ∈ growthΓ f xbar x) : growthF U f xbar (x, y) < growthF U f xbar (x', y) := by
  have hfx : f x.1 < f x'.1 := h.f_mono x.2.1 x'.2.1 hxx'
  have hy' : y.1 ≤ f x.1 := hy
  change U (f x.1 - y.1) < U (f x'.1 - y.1)
  exact h.U_mono (show f x.1 - y.1 ∈ Set.Ici 0 from sub_nonneg.2 hy')
    (show f x'.1 - y.1 ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith) (by linarith)

/-- Assumption 4.6: `Γ` is monotone. -/
theorem growth_a46 (h : GrowthHyp U f β xbar) (x x' : Icc (0 : ℝ) xbar) (hxx' : x ≤ x') :
    growthΓ f xbar x ⊆ growthΓ f xbar x' := fun _ hy =>
  hy.trans (h.f_mono.monotoneOn x.2.1 x'.2.1 hxx')

theorem growth_assumption41 (h : GrowthHyp U f β xbar) : Assumption41 (growthΓ f xbar) :=
  (growth_assumption43 h).nonempty

theorem growth_assumption42 (h : GrowthHyp U f β xbar) :
    Assumption42 (growthΓ f xbar) (curryF (growthF U f xbar)) β :=
  assumption42_of_44 (growth_assumption44 h)

/-- **Exercise 5.1a–b.** Under (U1)–(U3) and (T1)–(T3) there is a unique bounded continuous
solution `v` of (2). It is the supremum function of (1), it is strictly increasing, the policy
correspondence `G` is nonempty and u.h.c., and plans generated by `G` are optimal. -/
theorem ex_5_1ab (h : GrowthHyp U f β xbar) :
    ∃ v : Icc (0 : ℝ) xbar →ᵇ ℝ,
      bellman (growth_assumption43 h) (growth_assumption44 h) v = v ∧
      (∀ w, bellman (growth_assumption43 h) (growth_assumption44 h) w = w → w = v) ∧
      (fun x => (v x : EReal)) = vstar (growthΓ f xbar) (curryF (growthF U f xbar)) β ∧
      StrictMono v ∧
      ∀ x, (argmax (obj (growthF U f xbar) β v) (growthΓ f xbar) x).Nonempty ∧
        IsUHC (argmax (obj (growthF U f xbar) β v) (growthΓ f xbar)) x := by
  have : Nonempty (Icc (0 : ℝ) xbar) := ⟨⟨0, le_rfl, h.xbar_pos.le⟩⟩
  obtain ⟨v, hv, huniq, -, hG⟩ := theorem_4_6 (growth_assumption43 h) (growth_assumption44 h)
  exact ⟨v, hv, huniq, fixedPoint_eq_vstar _ _ hv,
    theorem_4_7 _ _ (growth_a45 h) (growth_a46 h) hv, fun x => ⟨(hG x).1, (hG x).2.2⟩⟩

/-! ### Exercise 5.1c: concavity -/

/-- Assumption 4.7 holds when `U` is concave and strictly increasing and `f` is strictly
concave. -/
theorem growth_a47 (h : GrowthHyp U f β xbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : StrictConcaveOn ℝ (Ici 0) f) :
    Assumption47 (convex_Icc 0 xbar) (growthΓ f xbar) (growthF U f xbar) := by
  intro x y x' y' hy hy' θ h0 h1
  set c := f x.1 - y.1
  set c' := f x'.1 - y'.1
  have hc : 0 ≤ c := sub_nonneg.2 hy
  have hc' : 0 ≤ c' := sub_nonneg.2 hy'
  have h1' : 0 ≤ 1 - θ := by linarith
  -- `θU(c) + (1 − θ)U(c′) ≤ U(θc + (1 − θ)c′)`
  have hUc := hU.2 (mem_Ici.2 hc) (mem_Ici.2 hc') h0.le h1' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcomb : 0 ≤ θ * c + (1 - θ) * c' := by positivity
  have hfw := hf.concaveOn.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) h0.le h1' (by ring)
  simp only [smul_eq_mul] at hfw
  have harg : θ * c + (1 - θ) * c' ≤
      f (θ * x.1 + (1 - θ) * x'.1) - (θ * y.1 + (1 - θ) * y'.1) := by
    simp only [c, c']; linarith
  have hmono : U (θ * c + (1 - θ) * c') ≤ U (f (θ * x.1 + (1 - θ) * x'.1) -
      (θ * y.1 + (1 - θ) * y'.1)) :=
    h.U_mono.monotoneOn (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg)) harg
  simp only [growthF, cmb, smul_eq_mul]
  refine ⟨hUc.trans hmono, fun hne => ?_⟩
  -- `x ≠ x′`: strict concavity of `f` makes the argument strictly larger
  have hne' : x.1 ≠ x'.1 := fun he => hne (Subtype.ext he)
  have hfs : θ * f x.1 + (1 - θ) * f x'.1 < f (θ * x.1 + (1 - θ) * x'.1) := by
    have := hf.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) hne' h0 (show (0 : ℝ) < 1 - θ by linarith)
      (show θ + (1 - θ) = 1 by ring)
    simpa only [smul_eq_mul] using this
  have harg' : θ * c + (1 - θ) * c' <
      f (θ * x.1 + (1 - θ) * x'.1) - (θ * y.1 + (1 - θ) * y'.1) := by
    simp only [c, c']; linarith
  exact hUc.trans_lt (h.U_mono (mem_Ici.2 hcomb) (mem_Ici.2 (hcomb.trans harg'.le)) harg')

/-- Assumption 4.8 holds when `f` is concave. -/
theorem growth_a48 (hf : ConcaveOn ℝ (Ici 0) f) :
    Assumption48 (convex_Icc 0 xbar) (growthΓ f xbar) := by
  intro x y x' y' hy hy' θ h0 h1
  have hfw := hf.2 (mem_Ici.2 x.2.1) (mem_Ici.2 x'.2.1) h0 (by linarith : 0 ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hfw
  change θ * y.1 + (1 - θ) * y'.1 ≤ f (θ * x.1 + (1 - θ) * x'.1)
  have : (0 : ℝ) ≤ 1 - θ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (show y.1 ≤ f x.1 from hy) h0,
    mul_le_mul_of_nonneg_left (show y'.1 ≤ f x'.1 from hy') this]

/-- **Exercise 5.1c.** With `U` strictly concave (U4) and `f` strictly concave, `v` is strictly
concave and the optimal policy is a continuous function. -/
theorem ex_5_1c [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : StrictConcaveOn ℝ (Ici 0) f)
    {v : Icc (0 : ℝ) xbar →ᵇ ℝ}
    (hv : bellman (growth_assumption43 h) (growth_assumption44 h) v = v) :
    IsStrictConcaveS (convex_Icc 0 xbar) v ∧
      UniqueArgmax (growthΓ f xbar) (obj (growthF U f xbar) β v) ∧
      Continuous (argmaxFn (growthΓ f xbar) (obj (growthF U f xbar) β v)) := by
  obtain ⟨h1, h2, -, h4⟩ := theorem_4_8 (growth_assumption43 h) (growth_assumption44 h)
    (growth_a47 h hU.concaveOn hf) (growth_a48 hf.concaveOn) hv
  exact ⟨h1, h2, h4⟩

/-- **Exercise 5.1c with a weakly concave `f`.** (T4) only asks `f` to be weakly concave, and
then Assumption 4.7 can fail. Take `x̄ = 2`, `f(k) = min{2k, 1 + k/2}` and `U(c) = √c`; these
satisfy (T2)–(T4) and (U2)–(U4). The points `(0.1, 0.1)` and `(0.2, 0.3)` give the same
consumption `0.1`, and `f` is linear between `0.1` and `0.2`. So
`F(θ(x, y) + (1 − θ)(x′, y′)) = θF(x, y) + (1 − θ)F(x′, y′)` with `x ≠ x′`. -/
theorem ex_5_1c_weak_counterexample :
    let f : ℝ → ℝ := fun k => min (2 * k) (1 + k / 2)
    let U : ℝ → ℝ := fun c => √c
    (f 0 = 0 ∧ (∀ x ∈ Icc (0 : ℝ) 2, x ≤ f x ∧ f x ≤ 2) ∧ (∀ x, 2 < x → f x < x) ∧
      StrictMonoOn f (Ici 0) ∧ ConcaveOn ℝ (Ici 0) f) ∧
    (StrictMonoOn U (Ici 0) ∧ StrictConcaveOn ℝ (Ici 0) U) ∧
    ¬ Assumption47 (convex_Icc 0 2) (growthΓ f 2) (growthF U f 2) := by
  intro f U
  refine ⟨⟨by simp [f], fun x hx => ⟨?_, ?_⟩, fun x hx => ?_, fun a _ b _ hab => ?_, ?_⟩,
    ⟨fun a ha b _ hab => Real.sqrt_lt_sqrt ha hab, Real.strictConcaveOn_sqrt⟩, fun h47 => ?_⟩
  · simp only [f, le_min_iff]; constructor <;> linarith [hx.1, hx.2]
  · exact (min_le_right _ _).trans (by linarith [hx.2])
  · exact (min_le_right _ _).trans_lt (by linarith)
  · simp only [f]
    rcases le_total (2 * a) (1 + a / 2) with h1 | h1 <;>
      rcases le_total (2 * b) (1 + b / 2) with h2 | h2 <;>
      simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith
  · exact (concaveOn_id (convex_Ici 0) |>.smul (by norm_num : (0 : ℝ) ≤ 2)).inf
      ((concaveOn_const 1 (convex_Ici 0)).add ((concaveOn_id (convex_Ici 0)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2))) |>.congr fun x _ => by
          simp only [f, Pi.inf_apply, smul_eq_mul, id, Pi.add_apply]; ring_nf
  · set x : Icc (0 : ℝ) 2 := ⟨0.1, by norm_num, by norm_num⟩
    set x' : Icc (0 : ℝ) 2 := ⟨0.2, by norm_num, by norm_num⟩
    set y : Icc (0 : ℝ) 2 := ⟨0.1, by norm_num, by norm_num⟩
    set y' : Icc (0 : ℝ) 2 := ⟨0.3, by norm_num, by norm_num⟩
    have hy : y ∈ growthΓ f 2 x := by
      change (0.1 : ℝ) ≤ min (2 * 0.1) (1 + 0.1 / 2); norm_num
    have hy' : y' ∈ growthΓ f 2 x' := by
      change (0.3 : ℝ) ≤ min (2 * 0.2) (1 + 0.2 / 2); norm_num
    have hne : x ≠ x' := fun he => by
      have := congrArg Subtype.val he; norm_num [x, x'] at this
    have := (h47 x y x' y' hy hy' (1 / 2) (by norm_num) (by norm_num)).2 hne
    simp only [growthF, cmb, U, f, smul_eq_mul, x, x', y, y'] at this
    norm_num at this
    linarith

end StokeyLucasPrescott.DeterministicApplications
