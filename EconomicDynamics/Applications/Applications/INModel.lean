/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INSsPolicy
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The inventory model of §8.5: setting, Bellman operator, finite-horizon problems

Miao, §8.5, pp. 262–270. The demand `z` is iid with distribution `φ` (a probability measure on
`ℝ` concentrated on `[0, ∞)` with finite mean); `L(y) = βEΦ(y − z)` is the expected holding and
storage cost; ordering `d > 0` costs `c + pd`.

* `INModel`: the primitives `(β, c, p, L, φ)`; `INModel.Assumption851`: the standing hypotheses
  (Assumption 8.5.1 plus the model's sign conditions); `INModel.Assumption852`: `L`
  differentiable.
* `INModel.TT f y x = c·1_{y>x} + p(y − x) + L(y) + β∫ f(y − z) dφ` (the book's `T(y, x, f)`,
  p. 273), `INModel.T f x = inf_{y ≥ x} TT f y x` (the Bellman operator, p. 263),
  `INModel.fn n = Tⁿ 0` ((8.22)), `INModel.Gf f y = L(y) + py + β∫ f(y − z) dφ` and
  `INModel.G n = Gf (f_{n−1})` (p. 265), `INModel.Sn n`, `INModel.sn n` (the smallest minimiser
  and the smallest solution of (8.23)).
* `eq_8_20`: the change of variables `y_t = x_t + d_t` that turns (8.19) into (8.20), for a
  sample path and any horizon; `in_L_convex`: `L = βEΦ(· − z)` is convex when `Φ` is.
* `INModel.TT_eq`: `T(y, x, f) = c·1_{y>x} + Gf f y − px`.
* `INModel.good_fn`: every `f_n` is continuous, nonnegative, c-convex and satisfies
  `f(w) ≤ c + pa + f(w + a)` (`a ≥ 0`); the latter gives integrability (`int_of_good`) and
  continuity (`cont_integral`) of `y ↦ ∫ f(y − z) dφ`.
* **Lemma 8.5.3** (`lemma_8_5_3`): every `G_n` is c-convex; with `G_n` continuous and coercive
  (`G_cont`, `G_coercive`), **Lemma 8.5.2** applies (`lemma_8_5_2_fn`), giving (8.23)
  (`eq_8_23`) and (8.26) (`eq_8_26`).
* `eq_8_22_split`: the "mixed stopping and control" form of (8.22).

**Departures.** (1) Assumption 8.5.1 as printed (`L` convex and coercive) does not make
`G_1(y) = L(y) + py` attain its minimum (counterexample in `INExercises`); we add
`L(y) + py → ∞` as `y → −∞` (`G1_coercive`). (2) The book leaves implicit that the demand is
nonnegative with finite mean (needed for `Ef_n(y − z)` to be finite, since `f_n(x)` grows
like `−px` as `x → −∞`), that `c, p ≥ 0` (`C ≥ 0`, p. 262) and `L ≥ 0` (`L : ℝ → ℝ₊`).
-/

namespace Miao.Applications

open MeasureTheory Filter Topology

/-- Miao, p. 263: a c-convex function stays c-convex under pointwise equality. -/
theorem in_cconvex_congr {c : ℝ} {f g : ℝ → ℝ} (hf : in_CConvex c f) (hfg : ∀ x, f x = g x) :
    in_CConvex c g := by
  have : f = g := funext hfg
  exact this ▸ hf

/-- Miao, (8.18)–(8.20), pp. 262–263: along any sample path with `x_{t+1} = y_t − z_{t+1}`,
the discounted holding and ordering costs of (8.19) equal `Φ(x₀) − β^T Φ(x_T)` plus the
discounted costs `βΦ(y_t − z_{t+1}) + C(y_t − x_t)` of (8.20); taking expectations of
`βΦ(y_t − z_{t+1})` gives `L(y_t)`. -/
theorem eq_8_20 (β : ℝ) (Φ C : ℝ → ℝ) (x y z : ℕ → ℝ) (hx : ∀ t, x (t + 1) = y t - z (t + 1))
    (T : ℕ) :
    ∑ t ∈ Finset.range T, β ^ t * (Φ (x t) + C (y t - x t)) =
      Φ (x 0) - β ^ T * Φ (x T) +
        ∑ t ∈ Finset.range T, β ^ t * (β * Φ (y t - z (t + 1)) + C (y t - x t)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, ← hx T, pow_succ]
    ring

/-- Miao, p. 263: `L(y) = βEΦ(y − z)` is convex when `Φ` is convex (and integrable along
translates), as Assumption 8.5.1 requires. -/
theorem in_L_convex {β : ℝ} (hβ : 0 ≤ β) {Φ : ℝ → ℝ} (φ : Measure ℝ) (hΦ : ConvexOn ℝ Set.univ Φ)
    (hint : ∀ y, Integrable (fun z => Φ (y - z)) φ) :
    ConvexOn ℝ Set.univ (fun y => β * ∫ z, Φ (y - z) ∂φ) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hpt : ∀ z, Φ (a * u + b * v - z) ≤ a * Φ (u - z) + b * Φ (v - z) := by
    intro z
    have e : a * u + b * v - z = a * (u - z) + b * (v - z) := by
      have : a * z + b * z = z := by rw [← add_mul, hab, one_mul]
      linarith
    rw [e]
    exact hΦ.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hi : Integrable (fun z => a * Φ (u - z) + b * Φ (v - z)) φ :=
    ((hint u).const_mul a).add ((hint v).const_mul b)
  have hle := integral_mono (hint (a * u + b * v)) hi hpt
  rw [integral_add ((hint u).const_mul a) ((hint v).const_mul b), integral_const_mul,
    integral_const_mul] at hle
  nlinarith [mul_le_mul_of_nonneg_left hle hβ]

/-- The inventory model of Miao §8.5 (p. 262): discount factor `β`, fixed and proportional
ordering costs `c`, `p`, expected holding cost `L`, demand distribution `φ`. -/
structure INModel where
  /-- discount factor -/
  β : ℝ
  /-- fixed ordering cost -/
  c : ℝ
  /-- proportional ordering cost -/
  p : ℝ
  /-- expected holding and storage cost `L(y) = βEΦ(y − z)` -/
  L : ℝ → ℝ
  /-- distribution of the demand `z` -/
  φ : Measure ℝ

namespace INModel

/-- The standing hypotheses of §8.5: **Assumption 8.5.1** (Miao, p. 263; `L ≥ 0` convex and
coercive) together with `β ∈ (0, 1)`, `c, p ≥ 0` (so that `C ≥ 0`), demand `z ≥ 0` with finite
mean, and the added coercivity `L(y) + py → ∞` as `y → −∞` (see the module docstring). -/
structure Assumption851 (M : INModel) : Prop where
  β_pos : 0 < M.β
  β_lt : M.β < 1
  c_nonneg : 0 ≤ M.c
  p_nonneg : 0 ≤ M.p
  prob : IsProbabilityMeasure M.φ
  demand_nonneg : ∀ᵐ z ∂M.φ, 0 ≤ z
  demand_int : Integrable (fun z => z) M.φ
  L_nonneg : ∀ y, 0 ≤ M.L y
  L_convex : ConvexOn ℝ Set.univ M.L
  L_coercive : in_Coercive M.L
  G1_coercive : Tendsto (fun y => M.L y + M.p * y) atBot atTop

/-- **Assumption 8.5.2** (Miao, p. 270): `L` is differentiable. -/
def Assumption852 (M : INModel) : Prop := Differentiable ℝ M.L

variable (M : INModel)

/-- The book's `T(y, x, f) = C(y − x) + L(y) + βEf(y − z)` (Miao, p. 273), with
`C(y − x) = c·1_{y>x} + p(y − x)`. -/
noncomputable def TT (f : ℝ → ℝ) (y x : ℝ) : ℝ :=
  in_fix M.c x y + M.p * (y - x) + M.L y + M.β * ∫ z, f (y - z) ∂M.φ

/-- The Bellman operator (Miao, p. 263): `Tf(x) = min_{y ≥ x} L(y) + c·1_{y>x} + p(y − x) +
βEf(y − z)`. -/
noncomputable def T (f : ℝ → ℝ) (x : ℝ) : ℝ := ⨅ y : Set.Ici x, M.TT f y x

/-- The finite-horizon value functions `f_n = Tⁿ f₀`, `f₀ = 0` (Miao, (8.22), p. 265). -/
noncomputable def fn : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => M.T (fn n)

/-- `Gf f y = L(y) + py + βEf(y − z)` (Miao, p. 265). -/
noncomputable def Gf (f : ℝ → ℝ) (y : ℝ) : ℝ := M.L y + M.p * y + M.β * ∫ z, f (y - z) ∂M.φ

/-- The book's `G_n = L(y) + py + βEf_{n−1}(y − z)`, `n ≥ 1` (Miao, p. 265). -/
noncomputable def G (n : ℕ) : ℝ → ℝ := M.Gf (M.fn (n - 1))

/-- The book's `S_n`: the smallest global minimiser of `G_n` (Miao, p. 265). -/
noncomputable def Sn (n : ℕ) : ℝ := in_Sbar (M.G n)

/-- The book's `s_n`: the smallest solution of (8.23) (Miao, p. 265 and Lemma 8.5.2). -/
noncomputable def sn (n : ℕ) : ℝ := in_sbar M.c (M.G n)

theorem fn_zero : M.fn 0 = fun _ => 0 := rfl

theorem fn_succ (n : ℕ) : M.fn (n + 1) = M.T (M.fn n) := rfl

theorem G_succ (n : ℕ) : M.G (n + 1) = M.Gf (M.fn n) := rfl

/-- `T(y, x, f) = c·1_{y>x} + Gf f y − px`. -/
theorem TT_eq (f : ℝ → ℝ) (y x : ℝ) : M.TT f y x = in_fix M.c x y + M.Gf f y - M.p * x := by
  unfold TT Gf; ring

/-- The class of functions preserved by `T`: continuous, nonnegative, c-convex, and
`f(w) ≤ c + pa + f(w + a)` for `a ≥ 0` (ordering `a` more never costs more than `c + pa`). -/
def Good (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ w a, 0 ≤ a → f w ≤ M.c + M.p * a + f (w + a)) ∧
    in_CConvex M.c f

variable {M}

/-- Integrability of `z ↦ f(y − z)` for a continuous nonnegative `f` with
`f(w) ≤ c + pa + f(w + a)`: on `z ≥ 0` it is bounded by `c + pz + f(y)`. -/
theorem int_of_P (hA : M.Assumption851) {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hP : ∀ w a, 0 ≤ a → f w ≤ M.c + M.p * a + f (w + a)) (y : ℝ) :
    Integrable (fun z => f (y - z)) M.φ := by
  have := hA.prob
  refine Integrable.mono' (g := fun z => M.c + M.p * z + f y)
    (((integrable_const M.c).add (hA.demand_int.const_mul M.p)).add (integrable_const (f y)))
    (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
  filter_upwards [hA.demand_nonneg] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
  have := hP (y - z) z hz
  simp only [sub_add_cancel] at this
  exact this

/-- Continuity of `y ↦ ∫ f(y − z) dφ` (dominated convergence). -/
theorem cont_integral (hA : M.Assumption851) {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) (hP : ∀ w a, 0 ≤ a → f w ≤ M.c + M.p * a + f (w + a)) :
    Continuous (fun y => ∫ z, f (y - z) ∂M.φ) := by
  have := hA.prob
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated (bound := fun z => M.c + M.p * (2 + z) + f (y₀ + 1)) ?_ ?_
    ?_ ?_
  · exact Eventually.of_forall fun y =>
      (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have hnb : ∀ᶠ y in 𝓝 y₀, y ∈ Set.Ioo (y₀ - 1) (y₀ + 1) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hnb] with y hy
    filter_upwards [hA.demand_nonneg] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
    have h1 := hP (y - z) (y₀ + 1 - y + z) (by linarith [hy.2])
    have e : y - z + (y₀ + 1 - y + z) = y₀ + 1 := by ring
    rw [e] at h1
    have : M.p * (y₀ + 1 - y + z) ≤ M.p * (2 + z) :=
      mul_le_mul_of_nonneg_left (by linarith [hy.1]) hA.p_nonneg
    linarith
  · exact ((integrable_const M.c).add ((((integrable_const (2 : ℝ)).add
      hA.demand_int)).const_mul M.p)).add (integrable_const _)
  · exact Eventually.of_forall fun z =>
      (hf.comp (continuous_id.sub continuous_const)).continuousAt

/-- Miao, p. 271 (proof of Lemma 8.5.5): if `f(w) ≤ c + pa + f(w + a)` for `a ≥ 0` then
`Gf f(y) − Gf f(x) ≥ L(y) − L(x) − c` for `x ≤ y`. -/
theorem Gf_diff (hA : M.Assumption851) {f : ℝ → ℝ}
    (hP : ∀ w a, 0 ≤ a → f w ≤ M.c + M.p * a + f (w + a))
    (hint : ∀ y, Integrable (fun z => f (y - z)) M.φ) {x y : ℝ} (hxy : x ≤ y) :
    M.L y - M.L x - M.c ≤ M.Gf f y - M.Gf f x := by
  have := hA.prob
  have hpt : ∀ z, -(M.c + M.p * (y - x)) ≤ f (y - z) - f (x - z) := by
    intro z
    have h1 := hP (x - z) (y - x) (sub_nonneg.2 hxy)
    have e : x - z + (y - x) = y - z := by ring
    rw [e] at h1
    linarith
  have hi : Integrable (fun z => f (y - z) - f (x - z)) M.φ := (hint y).sub (hint x)
  have hI := integral_mono (integrable_const _) hi hpt
  rw [integral_sub (hint y) (hint x)] at hI
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hI
  unfold Gf
  have hβ := hA.β_pos
  have hβ1 := hA.β_lt
  have hpy : 0 ≤ M.p * (y - x) := mul_nonneg hA.p_nonneg (sub_nonneg.2 hxy)
  have := mul_le_mul_of_nonneg_left hI hβ.le
  nlinarith [hA.c_nonneg]

/-- `G = Gf f` is coercive for `f ≥ 0` (it dominates `L(y) + py`). -/
theorem Gf_coercive (hA : M.Assumption851) {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x) :
    in_Coercive (M.Gf f) := by
  have := hA.prob
  have hge : ∀ y, M.L y + M.p * y ≤ M.Gf f y := by
    intro y
    unfold Gf
    have := mul_nonneg hA.β_pos.le (integral_nonneg (μ := M.φ) fun z => h0 (y - z))
    linarith
  refine ⟨tendsto_atTop_mono hge hA.G1_coercive, tendsto_atTop_mono' _ ?_ hA.L_coercive.2⟩
  filter_upwards [eventually_ge_atTop 0] with y hy
  have := mul_nonneg hA.p_nonneg hy
  linarith [hge y]

/-- `L` is continuous (a convex function on `ℝ`). -/
theorem L_cont (hA : M.Assumption851) : Continuous M.L := by
  have := hA.L_convex.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.1 this

/-- `Gf f` is continuous for a continuous nonnegative `f` with the `P`-property. -/
theorem Gf_cont (hA : M.Assumption851) {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hP : ∀ w a, 0 ≤ a → f w ≤ M.c + M.p * a + f (w + a)) : Continuous (M.Gf f) :=
  ((L_cont hA).add (continuous_const.mul continuous_id)).add
    (continuous_const.mul (cont_integral hA hf h0 hP))

/-- Miao, p. 270, end of the proof of Lemma 8.5.3: `Gf f` is c-convex when `f` is. -/
theorem Gf_cconvex (hA : M.Assumption851) {f : ℝ → ℝ} (hcc : in_CConvex M.c f)
    (hint : ∀ y, Integrable (fun z => f (y - z)) M.φ) : in_CConvex M.c (M.Gf f) := by
  have := hA.prob
  have h1 := in_cconvex_add_smul (in_cconvex_zero_of_convexOn hA.L_convex)
    (in_cconvex_affine M.p 0) zero_le_one zero_le_one
  have h2 := in_cconvex_add_smul h1 (in_cconvex_integral M.φ hcc hint) zero_le_one
    hA.β_pos.le
  have h3 := in_cconvex_mono (c' := M.c) (by
    have := mul_le_of_le_one_left hA.c_nonneg hA.β_lt.le
    linarith) h2
  exact in_cconvex_congr h3 fun x => by unfold Gf; ring

/-- The (s, S) structure of `T f` for a good `f`: with `G = Gf f`, `S` its smallest minimiser
and `s` the smallest solution of `G(s) ≤ c + G(S)`, `Tf(x) = −px + G(max(x, s))`. -/
theorem T_eq (hA : M.Assumption851) {f : ℝ → ℝ} (hf : M.Good f) (x : ℝ) :
    M.T f x = -M.p * x + M.Gf f (max x (in_sbar M.c (M.Gf f))) := by
  obtain ⟨hcont, h0, hP, hcc⟩ := hf
  have hint := int_of_P hA hcont h0 hP
  have hGc := Gf_cont hA hcont h0 hP
  have hGco := Gf_coercive hA h0
  have hS := (in_Sbar_isLeast hGc hGco).1
  have hs := in_sbar_isLeast hA.c_nonneg hGc hGco
  have hcc' := Gf_cconvex hA hcc hint
  have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
  have hB : BddBelow (Set.range fun y : Set.Ici x => M.TT f y x) := by
    refine ⟨M.Gf f (in_Sbar (M.Gf f)) - M.p * x, ?_⟩
    rintro _ ⟨y, rfl⟩
    simp only [TT_eq]
    linarith [in_fix_nonneg hA.c_nonneg x y, hS y]
  have hmem : in_ssPolicy (in_sbar M.c (M.Gf f)) (in_Sbar (M.Gf f)) x ∈ Set.Ici x := by
    unfold in_ssPolicy; split_ifs with h
    · exact Set.mem_Ici.2 (h.trans (in_ss_le hA.c_nonneg hs))
    · exact Set.mem_Ici.2 le_rfl
  have hv := in_ss_policy_value hA.c_nonneg hGc hs x
  unfold T
  refine le_antisymm ((ciInf_le hB ⟨_, hmem⟩).trans_eq ?_) (le_ciInf fun y => ?_)
  · rw [TT_eq, ← hv]; ring
  · rw [TT_eq]
    have := lemma_8_5_2 hA.c_nonneg hGc hcc' hS hs y.2
    rw [hv] at this
    linarith

/-- The minimum in `T f` is attained by the (s, S) rule. -/
theorem T_attained (hA : M.Assumption851) {f : ℝ → ℝ} (hf : M.Good f) (x : ℝ) :
    M.T f x = M.TT f (in_ssPolicy (in_sbar M.c (M.Gf f)) (in_Sbar (M.Gf f)) x) x := by
  obtain ⟨hcont, h0, hP, hcc⟩ := hf
  have hGc := Gf_cont hA hcont h0 hP
  have hs := in_sbar_isLeast hA.c_nonneg hGc (Gf_coercive hA h0)
  rw [T_eq hA ⟨hcont, h0, hP, hcc⟩, TT_eq, ← in_ss_policy_value hA.c_nonneg hGc hs x]
  ring

/-- `T f(x) ≤ T(y, x, f)` for `y ≥ x` (for `f ≥ 0`). -/
theorem T_le_TT (hA : M.Assumption851) {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x) {x y : ℝ}
    (hxy : x ≤ y) : M.T f x ≤ M.TT f y x := by
  have := hA.prob
  refine ciInf_le ⟨0, ?_⟩ (⟨y, hxy⟩ : Set.Ici x)
  rintro _ ⟨y', rfl⟩
  unfold TT
  have h1 := in_fix_nonneg hA.c_nonneg x y'
  have h2 := mul_nonneg hA.p_nonneg (sub_nonneg.2 (Set.mem_Ici.1 y'.2))
  have h3 := hA.L_nonneg y'
  have h4 := mul_nonneg hA.β_pos.le (integral_nonneg (μ := M.φ) fun z => h0 ((y' : ℝ) - z))
  linarith

/-- `T` preserves the class `Good`. -/
theorem good_T (hA : M.Assumption851) {f : ℝ → ℝ} (hf : M.Good f) : M.Good (M.T f) := by
  obtain ⟨hcont, h0, hP, hcc⟩ := hf
  have hint := int_of_P hA hcont h0 hP
  have hGc := Gf_cont hA hcont h0 hP
  have hGco := Gf_coercive hA h0
  have hS := (in_Sbar_isLeast hGc hGco).1
  have hs := in_sbar_isLeast hA.c_nonneg hGc hGco
  have hGcc := Gf_cconvex hA hcc hint
  have heq := T_eq hA ⟨hcont, h0, hP, hcc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show M.T f = fun x => -M.p * x + M.Gf f (max x (in_sbar M.c (M.Gf f))) from funext heq]
    exact (continuous_const.mul continuous_id).add
      (hGc.comp (continuous_id.max continuous_const))
  · intro x
    rw [T_attained hA ⟨hcont, h0, hP, hcc⟩]
    have := hA.prob
    unfold TT
    set y := in_ssPolicy (in_sbar M.c (M.Gf f)) (in_Sbar (M.Gf f)) x
    have hy : x ≤ y := by
      unfold y in_ssPolicy; split_ifs with h
      · exact h.trans (in_ss_le hA.c_nonneg hs)
      · exact le_rfl
    have h1 := in_fix_nonneg hA.c_nonneg x y
    have h2 := mul_nonneg hA.p_nonneg (sub_nonneg.2 hy)
    have h3 := hA.L_nonneg y
    have h4 := mul_nonneg hA.β_pos.le (integral_nonneg (μ := M.φ) fun z => h0 (y - z))
    linarith
  · intro w a ha
    rw [heq, heq]
    have := in_ss_P hA.c_nonneg hGcc hS hs (w := w) ha
    linarith
  · have h1 := in_cconvex_add_smul (in_cconvex_affine (-M.p) 0)
      (in_ss_cconvex_max hA.c_nonneg hGcc hS hs) zero_le_one zero_le_one
    exact in_cconvex_congr (in_cconvex_mono (by linarith) h1) fun x => by rw [heq]; ring

/-- Every finite-horizon value function `f_n` is good (the induction of Lemma 8.5.3). -/
theorem good_fn (hA : M.Assumption851) : ∀ n, M.Good (M.fn n)
  | 0 => by
    refine ⟨continuous_const, fun _ => le_rfl, fun w a ha => ?_, ?_⟩
    · simp only [fn_zero, add_zero]
      exact add_nonneg hA.c_nonneg (mul_nonneg hA.p_nonneg ha)
    · exact in_cconvex_mono hA.c_nonneg (in_cconvex_congr (in_cconvex_affine 0 0)
        fun x => by simp [fn_zero])
  | n + 1 => good_T hA (good_fn hA n)

/-- Integrability of `z ↦ f_n(y − z)`. -/
theorem int_fn (hA : M.Assumption851) (n : ℕ) (y : ℝ) :
    Integrable (fun z => M.fn n (y - z)) M.φ :=
  int_of_P hA (good_fn hA n).1 (good_fn hA n).2.1 (good_fn hA n).2.2.1 y

/-- `G_n` is continuous (`n ≥ 0`; `G_0 = G_1`). -/
theorem G_cont (hA : M.Assumption851) (n : ℕ) : Continuous (M.G n) :=
  Gf_cont hA (good_fn hA _).1 (good_fn hA _).2.1 (good_fn hA _).2.2.1

/-- `G_n` is coercive. -/
theorem G_coercive (hA : M.Assumption851) (n : ℕ) : in_Coercive (M.G n) :=
  Gf_coercive hA (good_fn hA _).2.1

/-- **Lemma 8.5.3** (Miao, p. 269). Under Assumption 8.5.1, `G_n` is c-convex for all `n ≥ 1`. -/
theorem lemma_8_5_3 (hA : M.Assumption851) (n : ℕ) : in_CConvex M.c (M.G n) :=
  Gf_cconvex hA (good_fn hA _).2.2.2 (int_fn hA _)

/-- `S_n` is the smallest global minimiser of `G_n`. -/
theorem Sn_isLeast (hA : M.Assumption851) (n : ℕ) :
    IsLeast {x | ∀ y, M.G n x ≤ M.G n y} (M.Sn n) :=
  in_Sbar_isLeast (G_cont hA n) (G_coercive hA n)

/-- `s_n` is the smallest `x` with `G_n(x) ≤ c + G_n(S_n)`. -/
theorem sn_isLeast (hA : M.Assumption851) (n : ℕ) :
    IsLeast {x | M.G n x ≤ M.c + M.G n (M.Sn n)} (M.sn n) :=
  in_sbar_isLeast hA.c_nonneg (G_cont hA n) (G_coercive hA n)

/-- Miao, (8.23), p. 265: `G_n(s_n) = c + G_n(S_n)` with `s_n ≤ S_n`, and `s_n < S_n` when
`c > 0`. -/
theorem eq_8_23 (hA : M.Assumption851) (n : ℕ) :
    M.G n (M.sn n) = M.c + M.G n (M.Sn n) ∧ M.sn n ≤ M.Sn n ∧
      (0 < M.c → M.sn n < M.Sn n) :=
  ⟨in_ss_eq (sn_isLeast hA n) (G_cont hA n).continuousAt,
    in_ss_le hA.c_nonneg (sn_isLeast hA n),
    fun hc => in_ss_lt_of_pos hc (sn_isLeast hA n) (G_cont hA n).continuousAt⟩

/-- Miao, (8.26), p. 270: `f_n(x) = −px + G_n(s_n)` for `x ≤ s_n` and `−px + G_n(x)` for
`x > s_n` (`n ≥ 1`). -/
theorem eq_8_26 (hA : M.Assumption851) (n : ℕ) (x : ℝ) :
    M.fn (n + 1) x = if x ≤ M.sn (n + 1) then -M.p * x + M.G (n + 1) (M.sn (n + 1))
      else -M.p * x + M.G (n + 1) x := by
  rw [fn_succ, T_eq hA (good_fn hA n)]
  change -M.p * x + M.G (n + 1) (max x (M.sn (n + 1))) = _
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (not_le.1 h).le]

/-- **Lemma 8.5.2** for the finite-horizon problem (Miao, p. 268): the (s_n, S_n) policy is
optimal in (8.22): it attains `f_n(x)` and beats every `y ≥ x`. -/
theorem lemma_8_5_2_fn (hA : M.Assumption851) (n : ℕ) (x : ℝ) :
    M.fn (n + 1) x = M.TT (M.fn n) (in_ssPolicy (M.sn (n + 1)) (M.Sn (n + 1)) x) x ∧
      ∀ y, x ≤ y → M.TT (M.fn n) (in_ssPolicy (M.sn (n + 1)) (M.Sn (n + 1)) x) x ≤
        M.TT (M.fn n) y x := by
  refine ⟨T_attained hA (good_fn hA n) x, fun y hy => ?_⟩
  rw [TT_eq, TT_eq]
  have := lemma_8_5_2 hA.c_nonneg (G_cont hA (n + 1)) (lemma_8_5_3 hA (n + 1))
    (Sn_isLeast hA (n + 1)).1 (sn_isLeast hA (n + 1)) hy
  change in_fix M.c x _ + M.G (n + 1) _ ≤ in_fix M.c x y + M.G (n + 1) y at this
  rw [G_succ] at this
  linarith

/-- Miao, (8.22), p. 265, second form: `f_n(x) = min {L(x) + βEf_{n−1}(x − z),
min_{y ≥ x} L(y) + c + p(y − x) + βEf_{n−1}(y − z)}` (no order versus order). -/
theorem eq_8_22_split (hA : M.Assumption851) (n : ℕ) (x : ℝ) :
    M.fn (n + 1) x = min (M.L x + M.β * ∫ z, M.fn n (x - z) ∂M.φ)
      (⨅ y : Set.Ici x, (M.L y + M.c + M.p * (y - x) + M.β * ∫ z, M.fn n (y - z) ∂M.φ)) := by
  have := hA.prob
  have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
  have h0 := (good_fn hA n).2.1
  have hB : BddBelow (Set.range fun y : Set.Ici x =>
      M.L y + M.c + M.p * (y - x) + M.β * ∫ z, M.fn n (y - z) ∂M.φ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := mul_nonneg hA.p_nonneg (sub_nonneg.2 (Set.mem_Ici.1 y.2))
    have h4 := mul_nonneg hA.β_pos.le (integral_nonneg (μ := M.φ) fun z => h0 ((y : ℝ) - z))
    linarith [hA.L_nonneg y, hA.c_nonneg]
  have hT : M.fn (n + 1) x ≤ M.TT (M.fn n) x x := T_le_TT hA h0 le_rfl
  refine le_antisymm (le_min ?_ (le_ciInf fun y => ?_)) ?_
  · unfold TT at hT; rw [in_fix_self] at hT; linarith
  · have := T_le_TT hA h0 (Set.mem_Ici.1 y.2) (f := M.fn n)
    unfold TT at this
    rw [fn_succ]
    linarith [in_fix_le hA.c_nonneg x y]
  · obtain ⟨heq, -⟩ := lemma_8_5_2_fn hA n x
    rw [heq]
    set y := in_ssPolicy (M.sn (n + 1)) (M.Sn (n + 1)) x
    unfold TT
    rcases eq_or_lt_of_le (show x ≤ y by
      unfold y in_ssPolicy; split_ifs with h
      · exact h.trans (eq_8_23 hA (n + 1)).2.1
      · exact le_rfl) with h | h
    · rw [← h, in_fix_self]
      simp only [sub_self, mul_zero, add_zero, zero_add]
      exact min_le_left _ _
    · rw [in_fix_of_lt _ h]
      refine (min_le_right _ _).trans ?_
      have := ciInf_le hB (⟨y, h.le⟩ : Set.Ici x)
      simp only at this
      linarith

end INModel

end Miao.Applications
