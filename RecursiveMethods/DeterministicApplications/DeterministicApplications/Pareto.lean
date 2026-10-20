/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.RecursivePreferences

/-!
# A Pareto problem with recursive preferences

SLP §5.13, pp. 117–118: two agents share one unit of a single good each period; agent `i` has
aggregator `W_i` with (W1)–(W3) and utility `u_i` (Exercise 5.11d). One good means `l = 1`;
`cst c` is the bundle `c`. With `I_i = [u_i(0), u_i(1)] = [0, b_i]`,
`(Tf)(x) = max {W₁[c, f(y)] : c ∈ [0, 1], y ∈ I₂, W₂(1 − c, y) ≥ x}`.

Assume both aggregators are nondecreasing (W4) and `W₂` is strictly increasing in each argument.

* `isLHC_of_approx`: a correspondence is l.h.c. at `x` when every point of `Γ(x)` is a limit of
  points that stay feasible near `x` (a Slater condition). `pareto_lhc`, `pareto_uhc`: the
  constraint set is continuous.
* **Exercise 5.13a** (`ex_5_13a`): `T` maps the continuous functions `I₂ → I₁` into themselves
  and is a contraction of modulus `β₁`; so it has a unique fixed point `v`.
* **Exercise 5.13b** (`ex_5_13b`): `v = v*`: for `x ∈ I₂`,
  `v(x) = sup{u₁(c) : 0 ≤ c_t ≤ 1, u₂(1 − c) ≥ x}`, and the supremum is attained by the plan
  that follows the maximizers of `T`. `v` is the Pareto frontier.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicApplications

/-- A correspondence is l.h.c. at `x` if every `w ∈ Γ(x)` is approximated by points that remain
feasible for all `x'` near `x`. -/
theorem isLHC_of_approx {X Y : Type*} [MetricSpace X] [MetricSpace Y] {Γ : X → Set Y} {x : X}
    (hne : (Γ x).Nonempty)
    (h : ∀ w ∈ Γ x, ∀ ε > 0, ∃ w', dist w' w < ε ∧ ∀ᶠ x' in 𝓝 x, w' ∈ Γ x') :
    IsLHC Γ x := by
  refine ⟨hne, fun w hw xs hxs => ?_⟩
  choose w' hw'd hw'ev using fun k : ℕ => h w hw (1 / ((k : ℝ) + 1)) (by positivity)
  have hN : ∀ k, ∃ N, ∀ n ≥ N, w' k ∈ Γ (xs n) := fun k =>
    eventually_atTop.1 (hxs.eventually (hw'ev k))
  choose N hN using hN
  classical
  set K : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  refine ⟨N 0, fun n => w' (K n), fun n hn => hN (K n) n
    (Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (Nat.zero_le n) hn), ?_⟩
  have hK : Tendsto K atTop atTop := tendsto_atTop_atTop.2 fun k =>
    ⟨max k (N k), fun n hn => Nat.le_findGreatest (le_of_max_le_left hn)
      (le_of_max_le_right hn)⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hw'd (K n)).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hK)

/-- The bundle with `c` units of the single good. -/
def cst (c : ℝ) : Fin 1 → ℝ := fun _ => c

theorem cst_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cst c := fun _ => hc

theorem cst_le {c c' : ℝ} (h : c ≤ c') : cst c ≤ cst c' := fun _ => h

variable {W₁ W₂ : (Fin 1 → ℝ) → ℝ → ℝ} {β₁ β₂ M₁ M₂ : ℝ}

/-- The hypotheses of SLP §5.13 used here. -/
structure ParetoHyp (W₁ W₂ : (Fin 1 → ℝ) → ℝ → ℝ) (β₁ β₂ M₁ M₂ : ℝ) : Prop where
  h1 : AggHyp W₁ β₁ M₁
  h2 : AggHyp W₂ β₂ M₂
  mono1 : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W₁ x z ≤ W₁ x' z'
  mono2 : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W₂ x z ≤ W₂ x' z'
  strict2c : ∀ c c' z, 0 ≤ c → c < c' → W₂ (cst c) z < W₂ (cst c') z
  strict2z : ∀ c z z', 0 ≤ c → z < z' → W₂ (cst c) z < W₂ (cst c) z'

/-- The constant sequence `1`. -/
def oneSeq : Seq 1 := ⟨BoundedContinuousFunction.const ℕ (cst 1), fun _ _ => zero_le_one⟩

theorem shiftSeq_one : shiftSeq oneSeq = oneSeq := Subtype.ext (by ext t i; rfl)

/-- The fixed-point equations `u(0) = 0` and `u(1) = W(1, u(1))`, and monotonicity: `0 ≤ u(1)`. -/
theorem utility_one {W : (Fin 1 → ℝ) → ℝ → ℝ} {β M : ℝ} (h : AggHyp W β M)
    (hmono : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W x z ≤ W x' z') {u : Seq 1 →ᵇ ℝ}
    (hu : opTW h u = u) : u oneSeq = W (cst 1) (u oneSeq) ∧ 0 ≤ u oneSeq ∧
      ∀ c, u zeroSeq ≤ u c := by
  obtain ⟨u', hu', huniq, hz, -⟩ := ex_5_11d h
  have hu'' := huniq u hu
  subst hu''
  have hfe := (DFunLike.congr_fun hu oneSeq).symm
  rw [opTW_apply, shiftSeq_one] at hfe
  refine ⟨hfe, ?_, fun c => ex_5_11d_mono h hmono hu fun t => c.2 t⟩
  rw [← hz]
  exact ex_5_11d_mono h hmono hu fun t => oneSeq.2 t

/-! ### The operator -/

variable {u₁ u₂ : Seq 1 →ᵇ ℝ}

/-- `I₂ = [0, b₂]`, `b₂ = u₂(1)`. -/
abbrev I2 (u₂ : Seq 1 →ᵇ ℝ) := ↥(Icc (0 : ℝ) (u₂ oneSeq))

/-- The constraint set `{(c, y) : 0 ≤ c ≤ 1, W₂(1 − c, y) ≥ x}`. -/
def paretoΦ (W₂ : (Fin 1 → ℝ) → ℝ → ℝ) (u₂ : Seq 1 →ᵇ ℝ) (x : I2 u₂) : Set (ℝ × I2 u₂) :=
  {w | w.1 ∈ Icc (0 : ℝ) 1 ∧ x.1 ≤ W₂ (cst (1 - w.1)) w.2.1}

/-- The objective `W₁(c, f(y))`. -/
def paretoObj (W₁ : (Fin 1 → ℝ) → ℝ → ℝ) (f : I2 u₂ → ℝ) (q : I2 u₂ × (ℝ × I2 u₂)) : ℝ :=
  W₁ (cst q.2.1) (f q.2.2)

theorem continuous_cst : Continuous cst := continuous_pi fun _ => continuous_id

theorem pareto_top_mem (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) (x : I2 u₂) :
    ((0 : ℝ), (⟨u₂ oneSeq, (utility_one h.h2 h.mono2 hu₂).2.1, le_rfl⟩ : I2 u₂)) ∈
      paretoΦ W₂ u₂ x := by
  refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
  simp only [sub_zero]
  rw [← (utility_one h.h2 h.mono2 hu₂).1]
  exact x.2.2

theorem pareto_compact (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (x : I2 u₂) :
    IsCompact (paretoΦ W₂ u₂ x) := by
  have : CompactSpace (I2 u₂) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hc : Continuous fun w : ℝ × I2 u₂ => W₂ (cst (1 - w.1)) w.2.1 :=
    h.h2.cont.comp ((continuous_cst.comp (continuous_const.sub continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  refine (isCompact_Icc.prod (isCompact_univ (X := I2 u₂))).of_isClosed_subset ?_
    fun w hw => ⟨hw.1, mem_univ _⟩
  exact ((isClosed_Icc.preimage continuous_fst)).inter (isClosed_le continuous_const hc)

theorem pareto_uhc (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) (x : I2 u₂) :
    IsUHC (paretoΦ W₂ u₂) x := by
  have : CompactSpace (I2 u₂) := isCompact_iff_compactSpace.1 isCompact_Icc
  refine ⟨⟨_, pareto_top_mem h hu₂ x⟩, fun xs hxs ws hws => ?_⟩
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_Icc.prod (isCompact_univ (X := I2 u₂))).tendsto_subseq
    (x := ws) fun n => ⟨(hws n).1, mem_univ _⟩
  have hc : Continuous fun w : ℝ × I2 u₂ => W₂ (cst (1 - w.1)) w.2.1 :=
    h.h2.cont.comp ((continuous_cst.comp (continuous_const.sub continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨w, ⟨hw.1, ?_⟩, φ, hφ, hlim⟩
  exact le_of_tendsto_of_tendsto (((continuous_subtype_val.tendsto x).comp hxs).comp
    hφ.tendsto_atTop) ((hc.tendsto w).comp hlim) (Eventually.of_forall fun n => (hws (φ n)).2)

theorem pareto_lhc (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) (x : I2 u₂) :
    IsLHC (paretoΦ W₂ u₂) x := by
  refine isLHC_of_approx ⟨_, pareto_top_mem h hu₂ x⟩ fun w hw ε hε => ?_
  have hc : Continuous fun w : ℝ × I2 u₂ => W₂ (cst (1 - w.1)) w.2.1 :=
    h.h2.cont.comp ((continuous_cst.comp (continuous_const.sub continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  -- a strictly feasible point stays feasible near `x`
  have hstrict : ∀ w' : ℝ × I2 u₂, w'.1 ∈ Icc (0 : ℝ) 1 → x.1 < W₂ (cst (1 - w'.1)) w'.2.1 →
      ∀ᶠ x' in 𝓝 x, w' ∈ paretoΦ W₂ u₂ x' := fun w' hw'1 hw' => by
    have := ((continuous_subtype_val.tendsto x).eventually (gt_mem_nhds hw'))
    filter_upwards [this] with x' hx'
    exact ⟨hw'1, hx'.le⟩
  rcases lt_or_eq_of_le hw.2 with hlt | heq
  · exact ⟨w, by simpa using hε, hstrict w hw.1 hlt⟩
  rcases eq_or_lt_of_le hw.1.1 with hc0 | hcpos
  · -- `c = 0`: raise `y` unless it is already at the top
    have hb : (0 : ℝ) ≤ u₂ oneSeq := (utility_one h.h2 h.mono2 hu₂).2.1
    rcases eq_or_lt_of_le w.2.2.2 with htop | hylt
    · refine ⟨w, by simpa using hε, Eventually.of_forall fun x' => ⟨hw.1, ?_⟩⟩
      rw [← hc0, sub_zero, htop, ← (utility_one h.h2 h.mono2 hu₂).1]
      exact x'.2.2
    · set δ := min (ε / 2) (u₂ oneSeq - w.2.1)
      have hδ : 0 < δ := lt_min (by linarith) (by linarith)
      set y' : I2 u₂ := ⟨w.2.1 + δ, by linarith [w.2.2.1], by
        linarith [min_le_right (ε / 2) (u₂ oneSeq - w.2.1)]⟩
      refine ⟨(w.1, y'), ?_, hstrict (w.1, y') hw.1 ?_⟩
      · rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq]
        simp only [y', add_sub_cancel_left, abs_of_pos hδ]
        exact max_lt hε (lt_of_le_of_lt (min_le_left _ _) (by linarith))
      · rw [heq]
        exact h.strict2z _ _ _ (by linarith [hw.1.2]) (by simp [y', hδ])
  · -- `c > 0`: give agent 2 a little more
    set δ := min (ε / 2) w.1
    have hδ : 0 < δ := lt_min (by linarith) hcpos
    refine ⟨(w.1 - δ, w.2), ?_, hstrict (w.1 - δ, w.2) ⟨by linarith [min_le_right (ε / 2) w.1],
      by linarith [hw.1.2]⟩ ?_⟩
    · rw [Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
      exact max_lt (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hε
    · rw [heq]
      exact h.strict2c _ _ _ (by linarith [hw.1.2]) (by linarith)

theorem continuous_paretoObj (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) {f : I2 u₂ → ℝ}
    (hf : Continuous f) : Continuous (paretoObj (u₂ := u₂) W₁ f) :=
  h.h1.cont.comp ((continuous_cst.comp (continuous_fst.comp continuous_snd)).prodMk
    (hf.comp (continuous_snd.comp continuous_snd)))

theorem abs_paretoObj_le (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (f : I2 u₂ →ᵇ ℝ)
    {q : I2 u₂ × (ℝ × I2 u₂)} (hq : q.2.1 ∈ Icc (0 : ℝ) 1) :
    |paretoObj W₁ f q| ≤ M₁ + β₁ * ‖f‖ := by
  have h1 := h.h1.lip _ (cst_nonneg hq.1) (f q.2.2) 0
  have h2 := h.h1.bdd _ (cst_nonneg hq.1)
  have h3 : |f q.2.2| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm q.2.2
  rw [sub_zero] at h1
  have := abs_sub_abs_le_abs_sub (W₁ (cst q.2.1) (f q.2.2)) (W₁ (cst q.2.1) 0)
  simp only [paretoObj]
  nlinarith [h.h1.β_pos]

/-- `(Tf)(x) = max {W₁[c, f(y)] : (c, y) ∈ Φ(x)}`. -/
noncomputable def paretoT (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (f : I2 u₂ →ᵇ ℝ) : I2 u₂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => maxValue (paretoObj W₁ f) (paretoΦ W₂ u₂) x)
    (theorem_3_6 (continuous_paretoObj h f.continuous).continuousOn (pareto_compact h)
      (pareto_lhc h hu₂) (pareto_uhc h hu₂)).1 (M₁ + β₁ * ‖f‖) fun x => by
        obtain ⟨w, hw, hval, -⟩ := exists_argmax (continuous_paretoObj h f.continuous).continuousOn
          (pareto_compact h x) ⟨_, pareto_top_mem h hu₂ x⟩
        rw [← hval, Real.norm_eq_abs]
        exact abs_paretoObj_le h f hw.1

theorem exists_paretoT_argmax (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (f : I2 u₂ →ᵇ ℝ) (x : I2 u₂) :
    ∃ w ∈ paretoΦ W₂ u₂ x, paretoT h hu₂ f x = W₁ (cst w.1) (f w.2) ∧
      ∀ w' ∈ paretoΦ W₂ u₂ x, W₁ (cst w'.1) (f w'.2) ≤ paretoT h hu₂ f x := by
  obtain ⟨w, hw, hval, hmax⟩ := exists_argmax (continuous_paretoObj h f.continuous).continuousOn
    (pareto_compact h x) ⟨_, pareto_top_mem h hu₂ x⟩
  exact ⟨w, hw, hval.symm, fun w' hw' => (hmax w' hw').trans_eq hval⟩

theorem paretoT_contraction (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂) :
    IsContraction (paretoT h hu₂) β₁ := by
  refine ⟨h.h1.β_pos, h.h1.β_lt, fun f g => (dist_le (mul_nonneg h.h1.β_pos.le
    dist_nonneg)).2 fun x => ?_⟩
  obtain ⟨w, hw, hval, hmax⟩ := exists_paretoT_argmax h hu₂ f x
  obtain ⟨w', hw', hval', hmax'⟩ := exists_paretoT_argmax h hu₂ g x
  have e1 := hmax w' hw'
  have e2 := hmax' w hw
  have l1 := h.h1.lip _ (cst_nonneg hw.1.1) (f w.2) (g w.2)
  have l2 := h.h1.lip _ (cst_nonneg hw'.1.1) (f w'.2) (g w'.2)
  have d1 := mul_le_mul_of_nonneg_left (show |f w.2 - g w.2| ≤ dist f g by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := f) (g := g) w.2) h.h1.β_pos.le
  have d2 := mul_le_mul_of_nonneg_left (show |f w'.2 - g w'.2| ≤ dist f g by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := f) (g := g) w'.2) h.h1.β_pos.le
  rw [Real.dist_eq, abs_le]
  rw [abs_le] at l1 l2
  constructor <;> linarith [l1.1, l1.2, l2.1, l2.2]

/-- **Exercise 5.13a.** `T` maps the continuous functions `I₂ → I₁ = [0, b₁]` into themselves and
is a contraction; it has a unique fixed point there. -/
theorem ex_5_13a (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₁ : opTW h.h1 u₁ = u₁)
    (hu₂ : opTW h.h2 u₂ = u₂) :
    IsContraction (paretoT h hu₂) β₁ ∧
      (∀ f : I2 u₂ →ᵇ ℝ, (∀ y, f y ∈ Icc 0 (u₁ oneSeq)) →
        ∀ x, paretoT h hu₂ f x ∈ Icc 0 (u₁ oneSeq)) ∧
      ∃ v : I2 u₂ →ᵇ ℝ, paretoT h hu₂ v = v ∧ (∀ y, v y ∈ Icc 0 (u₁ oneSeq)) ∧
        ∀ w, paretoT h hu₂ w = w → w = v := by
  have hmaps : ∀ f : I2 u₂ →ᵇ ℝ, (∀ y, f y ∈ Icc 0 (u₁ oneSeq)) →
      ∀ x, paretoT h hu₂ f x ∈ Icc 0 (u₁ oneSeq) := fun f hf x => by
    obtain ⟨w, hw, hval, -⟩ := exists_paretoT_argmax h hu₂ f x
    rw [hval]
    have h0 : W₁ 0 0 = 0 := h.h1.zero
    refine ⟨?_, ?_⟩
    · have := h.mono1 0 (cst w.1) 0 (f w.2) le_rfl (cst_nonneg hw.1.1) (hf _).1
      rw [h0] at this
      exact this
    · rw [(utility_one h.h1 h.mono1 hu₁).1]
      exact h.mono1 _ _ _ _ (cst_nonneg hw.1.1) (cst_le hw.1.2) (hf _).2
  have : Nonempty (I2 u₂ →ᵇ ℝ) := ⟨0⟩
  obtain ⟨v, hv, huniq, -⟩ := theorem_3_2 (paretoT_contraction h hu₂)
  set S : Set (I2 u₂ →ᵇ ℝ) := {f | ∀ y, f y ∈ Icc 0 (u₁ oneSeq)}
  have hclosed : IsClosed S := by
    have : S = ⋂ y, {f : I2 u₂ →ᵇ ℝ | f y ∈ Icc 0 (u₁ oneSeq)} := by ext f; simp [S]
    rw [this]
    exact isClosed_iInter fun y => isClosed_Icc.preimage (continuous_eval_const y)
  have hb : 0 ≤ u₁ oneSeq := (utility_one h.h1 h.mono1 hu₁).2.1
  have hvS : v ∈ S := (corollary_1 (S' := S) (S'' := S) (paretoT_contraction h hu₂) hv
    ⟨0, fun _ => ⟨le_rfl, hb⟩⟩ hclosed (fun f hf => hmaps f hf) (fun f hf => hmaps f hf)).1
  exact ⟨paretoT_contraction h hu₂, hmaps, v, hv, hvS, huniq⟩

/-! ### Exercise 5.13b: the fixed point is the Pareto frontier -/

/-- `1 − c` for a sequence with `c_t ≤ 1`. -/
def oneMinus (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) : Seq 1 :=
  ⟨BoundedContinuousFunction.const ℕ (cst 1) - c.1, fun t => sub_nonneg.2 (hc t)⟩

theorem shiftSeq_oneMinus (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) :
    shiftSeq (oneMinus c hc) = oneMinus (shiftSeq c) fun t => hc (t + 1) :=
  Subtype.ext (by ext t i; rfl)

theorem head_oneMinus (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) :
    (oneMinus c hc).1 0 = cst (1 - c.1 0 0) := by
  ext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  rfl

theorem head_eq_cst (c : Seq 1) (t : ℕ) : c.1 t = cst (c.1 t 0) := by
  ext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  rfl

theorem utility_zero {W : (Fin 1 → ℝ) → ℝ → ℝ} {β M : ℝ} (h : AggHyp W β M) {u : Seq 1 →ᵇ ℝ}
    (hu : opTW h u = u) : u zeroSeq = 0 := by
  obtain ⟨u', -, huniq, hz, -⟩ := ex_5_11d h
  rw [huniq u hu]; exact hz

/-- Utilities of allocations with `c_t ≤ 1` lie in `I = [0, u(1)]`. -/
theorem utility_range {W : (Fin 1 → ℝ) → ℝ → ℝ} {β M : ℝ} (h : AggHyp W β M)
    (hmono : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W x z ≤ W x' z') {u : Seq 1 →ᵇ ℝ}
    (hu : opTW h u = u) (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) : u c ∈ Icc 0 (u oneSeq) :=
  ⟨(utility_zero h hu) ▸ (utility_one h hmono hu).2.2 c, ex_5_11d_mono h hmono hu hc⟩

theorem oneMinus_le (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) (t : ℕ) :
    (oneMinus c hc).1 t ≤ cst 1 := fun i => by
  have := c.2 t i
  simp only [Pi.zero_apply] at this
  change (1 : ℝ) - c.1 t i ≤ 1
  linarith

/-- **Exercise 5.13b (upper half).** Every allocation with `c_t ≤ 1` that gives agent 2 at least
`x` gives agent 1 at most `v(x)`. -/
theorem pareto_le_value (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₁ : opTW h.h1 u₁ = u₁)
    (hu₂ : opTW h.h2 u₂ = u₂) {v : I2 u₂ →ᵇ ℝ} (hv : paretoT h hu₂ v = v) (x : I2 u₂)
    (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1) (hx : x.1 ≤ u₂ (oneMinus c hc)) : u₁ c ≤ v x := by
  set K := ‖u₁‖ + ‖v‖
  have hfe₁ : ∀ c, u₁ c = W₁ (c.1 0) (u₁ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₁ c).symm
  have hfe₂ : ∀ c, u₂ c = W₂ (c.1 0) (u₂ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₂ c).symm
  have hstep : ∀ n : ℕ, ∀ (x : I2 u₂) (c : Seq 1) (hc : ∀ t, c.1 t ≤ cst 1),
      x.1 ≤ u₂ (oneMinus c hc) → u₁ c - v x ≤ β₁ ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro x c hc _
      have h1 := abs_apply_le_norm u₁ c
      have h2 : |v x| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm x
      have h3 := le_abs_self (u₁ c)
      have h4 := neg_abs_le (v x)
      rw [pow_zero, one_mul]
      simp only [K]
      linarith
    | succ n ih =>
      intro x c hc hx
      have hsc : ∀ t, (shiftSeq c).1 t ≤ cst 1 := fun t => hc (t + 1)
      set y : I2 u₂ := ⟨u₂ (oneMinus (shiftSeq c) hsc), utility_range h.h2 h.mono2 hu₂ _
        (oneMinus_le _ hsc)⟩
      have hc0 : c.1 0 0 ∈ Icc (0 : ℝ) 1 := ⟨c.2 0 0, hc 0 0⟩
      have hmem : (c.1 0 0, y) ∈ paretoΦ W₂ u₂ x := by
        refine ⟨hc0, ?_⟩
        have e := hfe₂ (oneMinus c hc)
        rw [head_oneMinus, shiftSeq_oneMinus] at e
        rw [e] at hx
        exact hx
      have hvx : W₁ (cst (c.1 0 0)) (v y) ≤ v x := by
        obtain ⟨-, -, -, hmax⟩ := exists_paretoT_argmax h hu₂ v x
        rw [hv] at hmax
        exact hmax _ hmem
      have hIH := ih y (shiftSeq c) hsc le_rfl
      rw [hfe₁ c, head_eq_cst c 0]
      rcases le_total (u₁ (shiftSeq c)) (v y) with hle | hlt
      · have := h.mono1 _ _ _ _ (cst_nonneg hc0.1) le_rfl hle
        have : 0 ≤ β₁ ^ (n + 1) * K :=
          mul_nonneg (pow_nonneg h.h1.β_pos.le _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        linarith
      · have hl := h.h1.lip _ (cst_nonneg hc0.1) (u₁ (shiftSeq c)) (v y)
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hl
        have := le_abs_self (W₁ (cst (c.1 0 0)) (u₁ (shiftSeq c)) - W₁ (cst (c.1 0 0)) (v y))
        have hb := mul_le_mul_of_nonneg_left hIH h.h1.β_pos.le
        rw [pow_succ]
        nlinarith
  have hlim : Tendsto (fun n => β₁ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.h1.β_pos.le h.h1.β_lt).mul_const K
  have := ge_of_tendsto' hlim fun n => hstep n x c hc hx
  linarith

/-- The maximizers of `T` at the fixed point. -/
noncomputable def paretoPol (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) : ℝ × I2 u₂ :=
  (exists_paretoT_argmax h hu₂ v x).choose

/-- The allocation that follows the maximizers: `c_t` is the first component of the maximizer at
`x_t`, and `x_{t+1}` the second. -/
noncomputable def paretoPlan (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) : Seq 1 :=
  ⟨BoundedContinuousFunction.mkOfDiscrete
      (fun t => cst (paretoPol h hu₂ v ((fun y => (paretoPol h hu₂ v y).2)^[t] x)).1) 2
      fun s t => by
        have hb : ∀ u : ℕ, ‖cst (paretoPol h hu₂ v ((fun y => (paretoPol h hu₂ v y).2)^[u] x)).1‖
            ≤ 1 := fun u => by
          have hm : (paretoPol h hu₂ v ((fun y => (paretoPol h hu₂ v y).2)^[u] x)).1 ∈
              Icc (0 : ℝ) 1 := (exists_paretoT_argmax h hu₂ v
            ((fun y => (paretoPol h hu₂ v y).2)^[u] x)).choose_spec.1.1
          refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
          rw [Real.norm_eq_abs, abs_le]
          simp only [cst]
          exact ⟨by linarith [hm.1], hm.2⟩
        exact (dist_le_norm_add_norm _ _).trans (by linarith [hb s, hb t]),
    fun t => cst_nonneg ((exists_paretoT_argmax h hu₂ v
      ((fun y => (paretoPol h hu₂ v y).2)^[t] x)).choose_spec.1.1.1)⟩

theorem paretoPlan_le (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) (t : ℕ) : (paretoPlan h hu₂ v x).1 t ≤ cst 1 :=
  cst_le ((exists_paretoT_argmax h hu₂ v
    ((fun y => (paretoPol h hu₂ v y).2)^[t] x)).choose_spec.1.1.2)

theorem shiftSeq_paretoPlan (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) :
    shiftSeq (paretoPlan h hu₂ v x) = paretoPlan h hu₂ v (paretoPol h hu₂ v x).2 :=
  Subtype.ext (by
    ext t i
    simp only [shiftSeq_apply, paretoPlan, BoundedContinuousFunction.mkOfDiscrete_apply,
      Function.iterate_succ_apply])

theorem head_paretoPlan (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₂ : opTW h.h2 u₂ = u₂)
    (v : I2 u₂ →ᵇ ℝ) (x : I2 u₂) :
    (paretoPlan h hu₂ v x).1 0 = cst (paretoPol h hu₂ v x).1 := rfl

/-- **Exercise 5.13b.** The fixed point of `T` is the Pareto frontier:
`v(x) = max{u₁(c) : 0 ≤ c_t ≤ 1, u₂(1 − c) ≥ x}`, attained by the allocation that follows the
maximizers of `T`. -/
theorem ex_5_13b (h : ParetoHyp W₁ W₂ β₁ β₂ M₁ M₂) (hu₁ : opTW h.h1 u₁ = u₁)
    (hu₂ : opTW h.h2 u₂ = u₂) {v : I2 u₂ →ᵇ ℝ} (hv : paretoT h hu₂ v = v) (x : I2 u₂) :
    IsGreatest {r | ∃ c : Seq 1, ∃ hc : ∀ t, c.1 t ≤ cst 1,
      x.1 ≤ u₂ (oneMinus c hc) ∧ r = u₁ c} (v x) ∧
    v x = sSup {r | ∃ c : Seq 1, ∃ hc : ∀ t, c.1 t ≤ cst 1,
      x.1 ≤ u₂ (oneMinus c hc) ∧ r = u₁ c} := by
  have hfe₁ : ∀ c, u₁ c = W₁ (c.1 0) (u₁ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₁ c).symm
  have hfe₂ : ∀ c, u₂ c = W₂ (c.1 0) (u₂ (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu₂ c).symm
  have hspec : ∀ y : I2 u₂, paretoPol h hu₂ v y ∈ paretoΦ W₂ u₂ y ∧
      v y = W₁ (cst (paretoPol h hu₂ v y).1) (v (paretoPol h hu₂ v y).2) := fun y => by
    have := (exists_paretoT_argmax h hu₂ v y).choose_spec
    exact ⟨this.1, (DFunLike.congr_fun hv y).symm.trans this.2.1⟩
  -- the plan attains `v`
  have hval : ∀ n : ℕ, ∀ y : I2 u₂,
      |u₁ (paretoPlan h hu₂ v y) - v y| ≤ β₁ ^ n * (‖u₁‖ + ‖v‖) := by
    intro n
    induction n with
    | zero =>
      intro y
      have h1 := abs_apply_le_norm u₁ (paretoPlan h hu₂ v y)
      have h2 : |v y| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using v.norm_coe_le_norm y
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    | succ n ih =>
      intro y
      rw [hfe₁, head_paretoPlan, shiftSeq_paretoPlan, (hspec y).2]
      refine (h.h1.lip _ (cst_nonneg (hspec y).1.1.1) _ _).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih _) h.h1.β_pos.le
  -- and it gives agent 2 at least `x`
  have hfeas : ∀ n : ℕ, ∀ y : I2 u₂, y.1 - u₂ (oneMinus (paretoPlan h hu₂ v y)
      (paretoPlan_le h hu₂ v y)) ≤ β₂ ^ n * (2 * ‖u₂‖) := by
    intro n
    induction n with
    | zero =>
      intro y
      have h1 := abs_apply_le_norm u₂ (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y))
      have h2 : y.1 ≤ ‖u₂‖ := y.2.2.trans ((le_abs_self _).trans (abs_apply_le_norm u₂ oneSeq))
      rw [pow_zero, one_mul]
      linarith [neg_abs_le (u₂ (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y)))]
    | succ n ih =>
      intro y
      set y' := (paretoPol h hu₂ v y).2
      have hcons := (hspec y).1.2
      have hc0 := (hspec y).1.1
      have hshift : shiftSeq (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y)) =
          oneMinus (paretoPlan h hu₂ v y') (paretoPlan_le h hu₂ v y') :=
        Subtype.ext (by ext t i; rfl)
      have e := hfe₂ (oneMinus (paretoPlan h hu₂ v y) (paretoPlan_le h hu₂ v y))
      rw [head_oneMinus, hshift] at e
      rw [e]
      have hIH := ih y'
      set z := u₂ (oneMinus (paretoPlan h hu₂ v y') (paretoPlan_le h hu₂ v y'))
      have hhead : (paretoPlan h hu₂ v y).1 0 0 = (paretoPol h hu₂ v y).1 := rfl
      rw [hhead]
      have hc1 : 0 ≤ cst (1 - (paretoPol h hu₂ v y).1) := cst_nonneg (by linarith [hc0.2])
      rcases le_total y'.1 z with hle | hlt
      · have := h.mono2 _ _ _ _ hc1 le_rfl hle
        have : 0 ≤ β₂ ^ (n + 1) * (2 * ‖u₂‖) :=
          mul_nonneg (pow_nonneg h.h2.β_pos.le _) (by positivity)
        linarith
      · have hl := h.h2.lip _ hc1 y'.1 z
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hl
        have := le_abs_self (W₂ (cst (1 - (paretoPol h hu₂ v y).1)) y'.1 -
          W₂ (cst (1 - (paretoPol h hu₂ v y).1)) z)
        have hb := mul_le_mul_of_nonneg_left hIH h.h2.β_pos.le
        rw [pow_succ]
        nlinarith
  have hlim : ∀ K : ℝ, ∀ {b : ℝ}, 0 < b → b < 1 → Tendsto (fun n => b ^ n * K) atTop (𝓝 0) :=
    fun K b hb0 hb1 => by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).mul_const K
  have hattain : u₁ (paretoPlan h hu₂ v x) = v x := by
    have := ge_of_tendsto' (hlim _ h.h1.β_pos h.h1.β_lt) fun n => hval n x
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  have hfx : x.1 ≤ u₂ (oneMinus (paretoPlan h hu₂ v x) (paretoPlan_le h hu₂ v x)) := by
    have := ge_of_tendsto' (hlim _ h.h2.β_pos h.h2.β_lt) fun n => hfeas n x
    linarith
  have hG : IsGreatest {r | ∃ c : Seq 1, ∃ hc : ∀ t, c.1 t ≤ cst 1,
      x.1 ≤ u₂ (oneMinus c hc) ∧ r = u₁ c} (v x) :=
    ⟨⟨_, paretoPlan_le h hu₂ v x, hfx, hattain.symm⟩, by
      rintro _ ⟨c, hc, hcx, rfl⟩
      exact pareto_le_value h hu₁ hu₂ hv x c hc hcx⟩
  exact ⟨hG, hG.csSup_eq.symm⟩

end StokeyLucasPrescott.DeterministicApplications
