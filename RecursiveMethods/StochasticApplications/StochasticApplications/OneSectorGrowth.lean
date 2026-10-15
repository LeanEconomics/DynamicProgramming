/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.PolicyKernels

/-!
# The one-sector model of optimal growth under uncertainty

SLP §10.1, pp. 288–290: `sup E Σ βᵗ U[z_t f(x_t) − x_{t+1}]` subject to
`0 ≤ x_{t+1} ≤ z_t f(x_t)`, on the capital stocks `X = [0, x̄]` and the shocks `Z = [1, z̄]`
(Assumption (Z1)), where `x̄ = z̄ f(x̄)`. The shocks follow any Markov transition `Q` with the
Feller property: this covers the i.i.d. shocks of (Z2) (`Q(z, ·) = λ`) and the Markov shocks of
(Z3), so parts (a)–(c) are proved once for both, as Exercise 10.1f asks.

* `GrowthHyp`: (U1)–(U3), (T1)–(T3), (Z1) and `z̄ f(x̄) ≤ x̄`; concavity, (U4) and (T4), is
  assumed where it is used.
* `growthΓ`, `growthF`, `growthModel`: `Γ(x, z) = {y ∈ X : y ≤ z f(x)}` and
  `F(x, y, z) = U[z f(x) − y]` in the first formulation of Chapter 9.
* `growth_boundedDP`: the hypotheses of §9.2 hold.
* `exists_measurableSelection_Icc`: a compact-valued u.h.c. correspondence into an interval has a
  measurable selection (its largest element).
* **Exercise 10.1a** (`ex_10_1a`): the feasible plans, and the value of a plan as the convergent
  sum `Σ βᵗ ∫ U[z_t f(x_t) − x_{t+1}] dμᵗ`.
* **Exercise 10.1b** (`ex_10_1b`): there is a unique bounded continuous solution `v` of (2), its
  policy correspondence `G` is nonempty, compact-valued and u.h.c., `v = v*`, some plan generated
  by `G` is optimal, and every optimal plan follows `G` almost surely (Theorem 9.4, corrected).
* **Exercise 10.1c** (`ex_10_1c`): `v(·, z)` is strictly increasing and strictly concave and `G`
  is a continuous function `g`. (T4) only asks for `f` concave, and then Assumption 9.10 (strict
  concavity of `F` in `x`) fails, so Theorem 9.8 does not apply. The conclusion holds anyway
  (`growth_strictConcave`): along a chord on which `v(·, z)` were affine, consumption would be
  constant, so the chord would be carried to affine chords of `v(·, z′)` with `β` times the rise;
  the supremum of the rises would satisfy `S ≤ βS`.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

/-- (U1)–(U3), (T1)–(T3) and (Z1) of SLP §§5.1 and 10.1. The book takes `x̄ = z̄ f(x̄)` (p. 289);
only `z̄ f(x̄) ≤ x̄` is used, which says that `X = [0, x̄]` is never left. -/
structure GrowthHyp (U f : ℝ → ℝ) (β xbar zbar : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  U_cont : ContinuousOn U (Ici 0)
  U_mono : StrictMonoOn U (Ici 0)
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  f_mono : StrictMonoOn f (Ici 0)
  zbar_gt : 1 < zbar
  xbar_pos : 0 < xbar
  xbar_maintain : zbar * f xbar ≤ xbar

variable {U f : ℝ → ℝ} {β xbar zbar : ℝ}

/-- `Γ(x, z) = {y ∈ [0, x̄] : y ≤ z f(x)}`. -/
def growthΓ (f : ℝ → ℝ) (xbar zbar : ℝ) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    Set (Icc (0 : ℝ) xbar) :=
  {y | y.1 ≤ s.2.1 * f s.1.1}

/-- `F(x, y, z) = U[z f(x) − y]`, with consumption clamped at `0` off the graph of `Γ`. -/
def growthF (U f : ℝ → ℝ) (xbar zbar : ℝ)
    (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) : ℝ :=
  U (max (p.2.2.1 * f p.1.1 - p.2.1.1) 0)

/-- The growth model in the first formulation of Chapter 9. -/
abbrev growthModel (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) (U f : ℝ → ℝ)
    (β xbar : ℝ) : Model (Icc (0 : ℝ) xbar) (Icc (0 : ℝ) xbar) (Icc (1 : ℝ) zbar) :=
  Model.first Q (growthΓ f xbar zbar) (growthF U f xbar zbar) β

theorem GrowthHyp.f_nonneg (h : GrowthHyp U f β xbar zbar) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have := h.f_mono.monotoneOn (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0) hx hx
  rwa [h.f_zero] at this

theorem GrowthHyp.zf_nonneg (h : GrowthHyp U f β xbar zbar)
    (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) : 0 ≤ s.2.1 * f s.1.1 :=
  mul_nonneg (by linarith [s.2.2.1]) (h.f_nonneg s.1.2.1)

/-- Output never exceeds `x̄`: `z f(x) ≤ z̄ f(x̄) = x̄`. -/
theorem GrowthHyp.zf_le (h : GrowthHyp U f β xbar zbar)
    (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) : s.2.1 * f s.1.1 ≤ xbar := by
  have h1 : f s.1.1 ≤ f xbar := h.f_mono.monotoneOn s.1.2.1 h.xbar_pos.le s.1.2.2
  calc s.2.1 * f s.1.1 ≤ zbar * f xbar :=
        mul_le_mul s.2.2.2 h1 (h.f_nonneg s.1.2.1) (by linarith [h.zbar_gt])
    _ ≤ xbar := h.xbar_maintain

theorem GrowthHyp.continuous_zf (h : GrowthHyp U f β xbar zbar) :
    Continuous fun s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar => s.2.1 * f s.1.1 :=
  (continuous_subtype_val.comp continuous_snd).mul
    (h.f_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun s => s.1.2.1)

theorem GrowthHyp.continuous_F (h : GrowthHyp U f β xbar zbar) :
    Continuous (growthF U f xbar zbar) :=
  h.U_cont.comp_continuous ((((continuous_subtype_val.comp continuous_snd.snd).mul
    (h.f_cont.comp_continuous (continuous_subtype_val.comp continuous_fst) fun p => p.1.2.1)).sub
    (continuous_subtype_val.comp continuous_snd.fst)).max continuous_const)
    fun _ => mem_Ici.2 (le_max_right _ _)

theorem GrowthHyp.bddF (h : GrowthHyp U f β xbar zbar) :
    ∃ B, ∀ p, |growthF U f xbar zbar p| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous_F.continuousOn
  exact ⟨B, fun p => by simpa [Real.norm_eq_abs] using hB p (mem_univ _)⟩

/-- On the graph, `F(x, y, z) = U[z f(x) − y]`. -/
theorem growthF_of_mem {x y : Icc (0 : ℝ) xbar} {z : Icc (1 : ℝ) zbar}
    (hy : y ∈ growthΓ f xbar zbar (x, z)) :
    growthF U f xbar zbar (x, y, z) = U (z.1 * f x.1 - y.1) := by
  have : 0 ≤ z.1 * f x.1 - y.1 := sub_nonneg.2 hy
  simp only [growthF, max_eq_left this]

/-- The correspondence `s ↦ {y ∈ [0, x̄] : y ≤ c(s)}`, for continuous `c ≥ 0`, is l.h.c. -/
theorem isLHC_Icc_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsLHC (fun s => {y : Icc (0 : ℝ) xbar | y.1 ≤ c s}) s := by
  refine ⟨⟨⟨0, le_rfl, hx⟩, h0 s⟩, fun y hy xs hxs => ?_⟩
  refine ⟨0, fun n => ⟨min y.1 (c (xs n)), le_min y.2.1 (h0 _), (min_le_left _ _).trans y.2.2⟩,
    fun n _ => show min y.1 (c (xs n)) ≤ c (xs n) from min_le_right _ _, ?_⟩
  have hlim := (tendsto_const_nhds (x := y.1)).min ((hc.tendsto s).comp hxs)
  rw [min_eq_left hy] at hlim
  exact tendsto_subtype_rng.2 hlim

/-- The correspondence `s ↦ {y ∈ [0, x̄] : y ≤ c(s)}`, for continuous `c ≥ 0`, is u.h.c. -/
theorem isUHC_Icc_le {S : Type*} [MetricSpace S] {c : S → ℝ} (hc : Continuous c)
    (h0 : ∀ s, 0 ≤ c s) (hx : 0 ≤ xbar) (s : S) :
    IsUHC (fun s => {y : Icc (0 : ℝ) xbar | y.1 ≤ c s}) s := by
  refine ⟨⟨⟨0, le_rfl, hx⟩, h0 s⟩, fun xs hxs ys hys => ?_⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ys) fun _ => mem_univ _
  refine ⟨y, ?_, φ, hφ, hlim⟩
  exact le_of_tendsto_of_tendsto ((continuous_subtype_val.tendsto y).comp hlim)
    ((hc.tendsto s).comp (hxs.comp hφ.tendsto_atTop)) (Eventually.of_forall fun n => hys (φ n))

/-- The hypotheses of §9.2 hold for the growth model (Exercise 10.1b; Exercise 10.1f for Markov
shocks): `Γ` is nonempty, compact-valued and continuous, `F` is bounded and continuous, and
Lemma 9.5 applies because `Z` is compact and `Q` is Feller. -/
theorem growth_boundedDP (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    BoundedDP (growthModel Q U f β xbar) :=
  ⟨fun s => ⟨⟨0, le_rfl, h.xbar_pos.le⟩, h.zf_nonneg s⟩,
    fun _ => IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const),
    isLHC_Icc_le h.continuous_zf h.zf_nonneg h.xbar_pos.le,
    isUHC_Icc_le h.continuous_zf h.zf_nonneg h.xbar_pos.le, h.continuous_F.continuousOn,
    ⟨h.bddF.choose, fun p _ => h.bddF.choose_spec p⟩, h.β_pos, h.β_lt,
    continuous_fst.snd.continuousOn, contExp_first Q _ _ β (lemma_9_5_compact Q hQ)⟩

/-- **Measurable selection into an interval.** A nonempty, compact-valued, u.h.c. correspondence
`G : S ⇉ [a, b]` has a measurable selection: `g(s) = max G(s)`, since
`{s : max G(s) ≥ x} = {s : G(s) ∩ [x, ∞) ≠ ∅}` is closed. -/
theorem exists_measurableSelection_Icc {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] {a b : ℝ} {G : S → Set (Icc a b)} (hu : ∀ s, IsUHC G s)
    (hc : ∀ s, IsCompact (G s)) : ∃ g : S → Icc a b, Measurable g ∧ ∀ s, g s ∈ G s := by
  set m : S → ℝ := fun s => sSup (Subtype.val '' G s)
  have hmem : ∀ s, m s ∈ Subtype.val '' G s := fun s =>
    ((hc s).image continuous_subtype_val).sSup_mem ((hu s).1.image _)
  have hle : ∀ s, ∀ y ∈ G s, y.1 ≤ m s := fun s y hy =>
    le_csSup ((hc s).image continuous_subtype_val).bddAbove ⟨y, hy, rfl⟩
  have hmeas : Measurable m := by
    refine measurable_of_Ici fun x => (IsSeqClosed.isClosed fun ss s hss hlim => ?_).measurableSet
    choose ys hys hysv using fun n => hmem (ss n)
    obtain ⟨y, hy, φ, hφ, hylim⟩ := (hu s).2 ss hlim ys hys
    have hx : x ≤ y.1 := ge_of_tendsto ((continuous_subtype_val.tendsto y).comp hylim)
      (Eventually.of_forall fun n => by
        change x ≤ (ys (φ n)).1
        rw [hysv]
        exact hss (φ n))
    exact hx.trans (hle s y hy)
  have hgm : ∀ s, m s ∈ Icc a b := fun s => by
    obtain ⟨y, -, hy⟩ := hmem s
    rw [← hy]
    exact y.2
  refine ⟨fun s => ⟨m s, hgm s⟩, hmeas.subtype_mk, fun s => ?_⟩
  obtain ⟨y, hy, hyv⟩ := hmem s
  have : (⟨m s, hgm s⟩ : Icc a b) = y := Subtype.ext hyv.symm
  change (⟨m s, hgm s⟩ : Icc a b) ∈ G s
  rw [this]
  exact hy

/-- **Exercise 10.1a.** A plan is feasible if and only if each `π_t` is measurable and
`0 ≤ x_{t+1} ≤ z_t f(x_t)`. The expectation in (1) is the convergent sum
`Σ βᵗ ∫ U[z_t f(x_t) − x_{t+1}] μᵗ(z₀, dzᵗ)`. -/
theorem ex_10_1a (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q]
    (s₀ : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) (π : Plan (Icc (0 : ℝ) xbar) (Icc (1 : ℝ) zbar)) :
    (IsFeasible (growthModel Q U f β xbar) s₀ π ↔ (∀ t, Measurable (π t)) ∧
      ∀ t hz, 0 ≤ (π t hz).1 ∧ (π t hz).1 ≤ (state (growthModel Q U f β xbar) s₀ π t hz).2.1 *
        f (state (growthModel Q U f β xbar) s₀ π t hz).1.1) ∧
    (IsFeasible (growthModel Q U f β xbar) s₀ π →
      Summable (fun t => β ^ t * ∫ hz, U ((state (growthModel Q U f β xbar) s₀ π t hz).2.1 *
        f (state (growthModel Q U f β xbar) s₀ π t hz).1.1 - (π t hz).1) ∂hist Q t s₀.2) ∧
      planValue (growthModel Q U f β xbar) s₀ π =
        ((∑' t, β ^ t * ∫ hz, U ((state (growthModel Q U f β xbar) s₀ π t hz).2.1 *
          f (state (growthModel Q U f β xbar) s₀ π t hz).1.1 - (π t hz).1) ∂hist Q t s₀.2 :
            ℝ) : EReal)) := by
  set M := growthModel Q U f β xbar
  refine ⟨⟨fun hπ => ⟨hπ.1, fun t hz => ⟨(π t hz).2.1, hπ.2 t hz⟩⟩,
    fun hπ => ⟨hπ.1, fun t hz => (hπ.2 t hz).2⟩⟩, fun hπ => ?_⟩
  obtain ⟨B, hB⟩ := h.bddF
  have hK : ∀ t hz, |ret M s₀ π t hz| ≤ B := fun t hz => hB _
  have hsum : Summable fun t => M.β ^ t * B :=
    (summable_geometric_of_lt_one h.β_pos.le h.β_lt).mul_right _
  have heq : (fun t => M.β ^ t * ∫ hz, ret M s₀ π t hz ∂hist M.Q t s₀.2) =
      fun t => β ^ t * ∫ hz, U ((state M s₀ π t hz).2.1 * f (state M s₀ π t hz).1.1 -
        (π t hz).1) ∂hist Q t s₀.2 := by
    funext t
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun hz => ?_)
    exact growthF_of_mem (hπ.2 t hz)
  refine ⟨heq ▸ summable_terms M h.β_pos.le s₀ π hK hsum, ?_⟩
  rw [planValue_eq_uR M h.β_pos.le s₀ π hK hsum, uR, heq]

/-- **Exercise 10.1b.** There is a unique bounded continuous `v` satisfying (2), and the policy
correspondence `G` is nonempty, compact-valued and u.h.c. The pair `(v, G)` solves the sequence
problem: `v = v*`, a plan generated by a measurable selection `g` from `G` is optimal from every
`s₀`, and every optimal plan takes its actions in `G` almost surely. -/
theorem ex_10_1b (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q) :
    ∃ v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ,
      bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v ∧
      (∀ w, bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w = w → w = v) ∧
      (∀ s, (policy (growthModel Q U f β xbar) v s).Nonempty ∧
        IsCompact (policy (growthModel Q U f β xbar) v s) ∧
        IsUHC (policy (growthModel Q U f β xbar) v) s) ∧
      (∀ s, vStar (growthModel Q U f β xbar) s = v s) ∧
      (∃ g : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → Icc (0 : ℝ) xbar, Measurable g ∧
        (∀ s, g s ∈ policy (growthModel Q U f β xbar) v s) ∧
        ∀ s₀, IsFeasible (growthModel Q U f β xbar) s₀
            (genPlan (growthModel Q U f β xbar) s₀ fun _ => g) ∧
          planValue (growthModel Q U f β xbar) s₀
            (genPlan (growthModel Q U f β xbar) s₀ fun _ => g) =
            vStar (growthModel Q U f β xbar) s₀) ∧
      ∀ s₀ π, IsFeasible (growthModel Q U f β xbar) s₀ π →
        planValue (growthModel Q U f β xbar) s₀ π = vStar (growthModel Q U f β xbar) s₀ →
        π 0 Fin.elim0 ∈ policy (growthModel Q U f β xbar) v s₀ ∧
          ∀ t, ∀ᵐ hz ∂hist Q t s₀.2,
            π t hz ∈ policy (growthModel Q U f β xbar) v
              (state (growthModel Q U f β xbar) s₀ π t hz) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  obtain ⟨v, hv, huniq, -, hG⟩ := ex_9_7b M hb
  obtain ⟨g, hgm, hgG⟩ := exists_measurableSelection_Icc (fun s => (hG s).2.2)
    fun s => (hG s).2.1
  have hφm : Measurable M.φ := measurable_snd.fst
  have hFm : Measurable M.F := h.continuous_F.measurable
  have hopt := fun s₀ => bounded_vStar M hb hφm hFm hv (g := fun _ => g) (fun _ => hgm)
    (fun _ => hgG) s₀
  refine ⟨v, hv, huniq, hG, fun s => (hopt s).2.2, ⟨g, hgm, hgG, fun s₀ =>
    ⟨genPlan_feasible M hφm s₀ (fun _ => hgm) (fun _ s => (hgG s).1), ?_⟩⟩,
    fun s₀ π hπ hopt' => bounded_theorem_9_4 M hb hφm hFm hv (fun s => (hopt s).2.2) hπ hopt'⟩
  rw [(hopt s₀).2.1, (hopt s₀).2.2]

/-! ### Exercise 10.1c: monotonicity, concavity and the policy function -/

/-- **Exercise 10.1c** (monotonicity, Theorem 9.7): `v(·, z)` is strictly increasing. -/
theorem growth_strictMono (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    (z : Icc (1 : ℝ) zbar) : StrictMono fun x => v (x, z) := by
  refine theorem_9_7 Q _ _ β (growth_boundedDP h Q hQ) (fun x x' y z hxx' hy => ?_)
    (fun x x' z hxx' y hy => ?_) hv z
  · have hy' : y.1 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 < f x'.1 := h.f_mono x.2.1 x'.2.1 hxx'
    have hz : 0 < z.1 := by linarith [z.2.1]
    have hlt : z.1 * f x.1 < z.1 * f x'.1 := mul_lt_mul_of_pos_left hfx hz
    rw [growthF_of_mem hy, growthF_of_mem (show y.1 ≤ z.1 * f x'.1 by linarith)]
    exact h.U_mono (show z.1 * f x.1 - y.1 ∈ Ici 0 from sub_nonneg.2 hy')
      (show z.1 * f x'.1 - y.1 ∈ Ici 0 by simp only [mem_Ici]; linarith) (by linarith)
  · have hy' : y.1 ≤ z.1 * f x.1 := hy
    have hfx : f x.1 ≤ f x'.1 := h.f_mono.monotoneOn x.2.1 x'.2.1 hxx'
    exact hy'.trans (mul_le_mul_of_nonneg_left hfx (by linarith [z.2.1]))

/-- With `f` concave, `θ z f(x₀) + (1 − θ) z f(x₁) ≤ z f(θx₀ + (1 − θ)x₁)`. -/
theorem growth_zf_cmb (hf : ConcaveOn ℝ (Ici 0) f) (x₀ x₁ : Icc (0 : ℝ) xbar)
    (z : Icc (1 : ℝ) zbar) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (z.1 * f x₀.1) + (1 - θ) * (z.1 * f x₁.1) ≤
      z.1 * f (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁).1 := by
  have hc := hf.2 x₀.2.1 x₁.2.1 h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  simp only [cmb, smul_eq_mul]
  have hz : 0 ≤ z.1 := by linarith [z.2.1]
  nlinarith [mul_le_mul_of_nonneg_left hc hz]

theorem cmb_val {x₀ x₁ : Icc (0 : ℝ) xbar} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁).1 = θ * x₀.1 + (1 - θ) * x₁.1 := by
  simp [cmb]

/-- Assumption 9.11: the graph of `Γ(·, z)` is convex. -/
theorem growth_mem_cmb (hf : ConcaveOn ℝ (Ici 0) f) {x₀ x₁ y₀ y₁ : Icc (0 : ℝ) xbar}
    {z : Icc (1 : ℝ) zbar} (hy₀ : y₀ ∈ growthΓ f xbar zbar (x₀, z))
    (hy₁ : y₁ ∈ growthΓ f xbar zbar (x₁, z)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁ ∈
      growthΓ f xbar zbar (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁, z) := by
  have hc := growth_zf_cmb hf x₀ x₁ z h0 h1
  have e0 : y₀.1 ≤ z.1 * f x₀.1 := hy₀
  have e1 : y₁.1 ≤ z.1 * f x₁.1 := hy₁
  change (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 ≤ _
  rw [cmb_val]
  nlinarith

/-- The return is concave on the graph: with `cᵢ = z f(xᵢ) − yᵢ`,
`θU(c₀) + (1 − θ)U(c₁) ≤ U(θc₀ + (1 − θ)c₁) ≤ F(x_θ, y_θ, z)`. -/
theorem growth_F_cmb (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) {x₀ x₁ y₀ y₁ : Icc (0 : ℝ) xbar} {z : Icc (1 : ℝ) zbar}
    (hy₀ : y₀ ∈ growthΓ f xbar zbar (x₀, z)) (hy₁ : y₁ ∈ growthΓ f xbar zbar (x₁, z)) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * U (z.1 * f x₀.1 - y₀.1) + (1 - θ) * U (z.1 * f x₁.1 - y₁.1) ≤
        U (θ * (z.1 * f x₀.1 - y₀.1) + (1 - θ) * (z.1 * f x₁.1 - y₁.1)) ∧
      U (θ * (z.1 * f x₀.1 - y₀.1) + (1 - θ) * (z.1 * f x₁.1 - y₁.1)) ≤
        growthF U f xbar zbar (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁,
          cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁, z) := by
  have e0 : 0 ≤ z.1 * f x₀.1 - y₀.1 := sub_nonneg.2 hy₀
  have e1 : 0 ≤ z.1 * f x₁.1 - y₁.1 := sub_nonneg.2 hy₁
  have hc := growth_zf_cmb hf x₀ x₁ z h0 h1
  have hθ : 0 ≤ θ * (z.1 * f x₀.1 - y₀.1) + (1 - θ) * (z.1 * f x₁.1 - y₁.1) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  refine ⟨?_, ?_⟩
  · have := hU.2 e0 e1 h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
    simpa only [smul_eq_mul] using this
  · rw [growthF_of_mem (growth_mem_cmb hf hy₀ hy₁ h0 h1)]
    simp only [cmb_val] at hc ⊢
    refine h.U_mono.monotoneOn hθ ?_ ?_
    · simp only [mem_Ici]; nlinarith
    · nlinarith

/-- `T` maps functions concave in `x` to functions concave in `x`. -/
theorem growth_bellman_concave (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {w : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hw : ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => w (x, z)) (z : Icc (1 : ℝ) zbar) :
    IsConcaveS (convex_Icc 0 xbar) fun x =>
      bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  intro x₀ x₁ θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M hb w (x₀, z)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M hb w (x₁, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁, z)
  have hyθ := growth_mem_cmb hf hy₀ hy₁ h0 h1
  have hF := growth_F_cmb h hU hf hy₀ hy₁ h0 h1
  have hE := expV_comb M hb (fun _ _ _ _ _ _ _ _ => rfl) hw hy₀ hy₁ h0 h1 hyθ
  have hm := hmax _ hyθ
  have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
  simp only [rhs] at hv₀ hv₁ hm
  dsimp only
  rw [hv₀, hv₁]
  change θ * (growthF U f xbar zbar (x₀, y₀, z) + _) +
    (1 - θ) * (growthF U f xbar zbar (x₁, y₁, z) + _) ≤ _
  rw [growthF_of_mem hy₀, growthF_of_mem hy₁]
  change _ ≤ bellman M hb w (cmb (convex_Icc 0 xbar) h0 h1 x₀ x₁, z)
  change _ ≤ M.β * _ at hβE
  linarith [hF.1, hF.2]

/-- **Exercise 10.1c** (concavity): with `U` and `f` concave, `v(·, z)` is concave. -/
theorem growth_concave (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v) :
    ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => v (x, z) :=
  (corollary_1 (S' := {w | ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => w (x, z)})
    (S'' := {w | ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => w (x, z)})
    (bellman_contraction _ (growth_boundedDP h Q hQ)) hv ⟨0, fun _ _ _ _ _ _ => by simp⟩
    (isClosed_concaveX _) (fun _ hw => growth_bellman_concave h hU hf Q hQ hw)
    fun _ hw => growth_bellman_concave h hU hf Q hQ hw).1

/-- `z′ ↦ v(y, z′)` is integrable. -/
theorem integrable_section_v {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] {S : Type*} [TopologicalSpace S] (μ : Measure Z)
    [IsFiniteMeasure μ] (v : S × Z →ᵇ ℝ) (y : S) : Integrable (fun z' => v (y, z')) μ :=
  integrable_of_abs_le (v.continuous.comp (Continuous.prodMk_right y)).measurable fun _ => by
    rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm _

/-- **The step of the chord argument.** If `v(·, z)` is affine on a chord `[a, b]`, then
consumption is the same at `a` and `b`, the optimal `y_a < y_b`, `v(·, z′)` is affine on
`[y_a, y_b]` for `Q(z, ·)`-almost every `z′`, and
`v(b, z) − v(a, z) = β ∫ [v(y_b, z′) − v(y_a, z′)] Q(z, dz′)`. -/
theorem growth_flat_step (h : GrowthHyp U f β xbar zbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    (hvc : ∀ z, IsConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) {a b : Icc (0 : ℝ) xbar}
    {z : Icc (1 : ℝ) zbar} (hab : a < b) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (heq : v (cmb (convex_Icc 0 xbar) h0.le h1.le a b, z) = θ * v (a, z) + (1 - θ) * v (b, z)) :
    ∃ ya yb : Icc (0 : ℝ) xbar, ya < yb ∧
      (∀ᵐ z' ∂Q z, v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') =
        θ * v (ya, z') + (1 - θ) * v (yb, z')) ∧
      v (b, z) - v (a, z) = β * ∫ z', (v (yb, z') - v (ya, z')) ∂Q z := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  obtain ⟨ya, hya, hva, -⟩ := exists_bellman_argmax M hb v (a, z)
  obtain ⟨yb, hyb, hvb, -⟩ := exists_bellman_argmax M hb v (b, z)
  obtain ⟨-, -, -, hmax⟩ :=
    exists_bellman_argmax M hb v (cmb (convex_Icc 0 xbar) h0.le h1.le a b, z)
  rw [hv] at hva hvb hmax
  have hyθ := growth_mem_cmb hf hya hyb h0.le h1.le
  have hm := hmax _ hyθ
  have hF := growth_F_cmb h hU.concaveOn hf hya hyb h0.le h1.le
  have hint := integrable_section_v (Q z) v
  have hpt : ∀ z', θ * v (ya, z') + (1 - θ) * v (yb, z') ≤
      v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') := fun z' =>
    hvc z' ya yb θ h0.le h1.le
  -- the expected values
  set Ea := ∫ z', v (ya, z') ∂Q z
  set Eb := ∫ z', v (yb, z') ∂Q z
  set Eθ := ∫ z', v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') ∂Q z
  have hI : Integrable (fun z' => θ * v (ya, z') + (1 - θ) * v (yb, z')) (Q z) :=
    ((hint ya).const_mul θ).add ((hint yb).const_mul (1 - θ))
  have hgapE : ∫ z', (v (cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z') -
      (θ * v (ya, z') + (1 - θ) * v (yb, z'))) ∂Q z = Eθ - (θ * Ea + (1 - θ) * Eb) := by
    rw [integral_sub (hint _) hI,
      integral_add ((hint ya).const_mul θ) ((hint yb).const_mul (1 - θ)), integral_const_mul,
      integral_const_mul]
  have hE0 : 0 ≤ Eθ - (θ * Ea + (1 - θ) * Eb) := by
    rw [← hgapE]
    exact integral_nonneg fun z' => sub_nonneg.2 (hpt z')
  -- the returns
  set ca := z.1 * f a.1 - ya.1
  set cb := z.1 * f b.1 - yb.1
  have hca : 0 ≤ ca := sub_nonneg.2 hya
  have hcb : 0 ≤ cb := sub_nonneg.2 hyb
  have hFa : growthF U f xbar zbar (a, ya, z) = U ca := growthF_of_mem hya
  have hFb : growthF U f xbar zbar (b, yb, z) = U cb := growthF_of_mem hyb
  simp only [rhs, expV] at hva hvb hm
  change v (a, z) = growthF U f xbar zbar (a, ya, z) + β * Ea at hva
  change v (b, z) = growthF U f xbar zbar (b, yb, z) + β * Eb at hvb
  change growthF U f xbar zbar (cmb (convex_Icc 0 xbar) h0.le h1.le a b,
    cmb (convex_Icc 0 xbar) h0.le h1.le ya yb, z) + β * Eθ ≤ _ at hm
  rw [hFa] at hva
  rw [hFb] at hvb
  have hβ := h.β_pos
  -- both gaps vanish
  have hgapF : θ * U ca + (1 - θ) * U cb = U (θ * ca + (1 - θ) * cb) := by
    have := hF.2
    nlinarith [hF.1, mul_nonneg hβ.le hE0]
  have hceq : ca = cb := by
    by_contra hne
    have := hU.2 (show ca ∈ Ici 0 from hca) (show cb ∈ Ici 0 from hcb) hne h0
      (by linarith : (0 : ℝ) < 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    linarith
  have hEeq : Eθ - (θ * Ea + (1 - θ) * Eb) = 0 := by
    have := hF.2
    nlinarith [hF.1]
  refine ⟨ya, yb, ?_, ?_, ?_⟩
  · have hfab : f a.1 < f b.1 := h.f_mono a.2.1 b.2.1 hab
    have hz : 0 < z.1 := by linarith [z.2.1]
    have := mul_lt_mul_of_pos_left hfab hz
    change ya.1 < yb.1
    have : z.1 * f a.1 - ya.1 = z.1 * f b.1 - yb.1 := hceq
    linarith
  · have hzero := (integral_eq_zero_iff_of_nonneg (fun z' => sub_nonneg.2 (hpt z'))
      ((hint _).sub hI)).1 (by rw [hgapE, hEeq])
    filter_upwards [hzero] with z' hz'
    simp only [Pi.zero_apply] at hz'
    linarith
  · rw [integral_sub (hint yb) (hint ya), hva, hvb, hceq]
    ring

/-- **Exercise 10.1c** (strict concavity, for `f` only concave as in (T4)): `v(·, z)` is strictly
concave. If `v(·, z)` were affine on some chord, let `S` be the supremum of the rises
`v(b, z) − v(a, z) > 0` over such chords; `growth_flat_step` bounds each rise by `βS`. -/
theorem growth_strictConcave (h : GrowthHyp U f β xbar zbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    (z : Icc (1 : ℝ) zbar) : IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z) := by
  have hvc := growth_concave h hU.concaveOn hf Q hQ hv
  have hmono := growth_strictMono h Q hQ hv
  set D : Set ℝ := {d | ∃ a b : Icc (0 : ℝ) xbar, ∃ z : Icc (1 : ℝ) zbar, ∃ θ : ℝ,
    ∃ h0 : 0 < θ, ∃ h1 : θ < 1, a < b ∧
      v (cmb (convex_Icc 0 xbar) h0.le h1.le a b, z) = θ * v (a, z) + (1 - θ) * v (b, z) ∧
      d = v (b, z) - v (a, z)}
  have hD : D = ∅ := by
    by_contra hne
    obtain ⟨d₀, hd₀⟩ := nonempty_iff_ne_empty.2 hne
    have hbdd : BddAbove D := ⟨2 * ‖v‖, by
      rintro _ ⟨a, b, z, θ, h0, h1, -, -, rfl⟩
      have := v.dist_le_two_norm (b, z) (a, z)
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this⟩
    have hle : ∀ d ∈ D, d ≤ β * sSup D := by
      rintro _ ⟨a, b, z, θ, h0, h1, hab, heq, rfl⟩
      obtain ⟨ya, yb, hlt, hae, hdiff⟩ := growth_flat_step h hU hf Q hQ hv hvc hab h0 h1 heq
      rw [hdiff]
      refine mul_le_mul_of_nonneg_left ?_ h.β_pos.le
      have hint := integrable_section_v (Q z) v
      have := integral_mono_ae ((hint yb).sub (hint ya)) (integrable_const (sSup D))
        (hae.mono fun z' hz' => le_csSup hbdd ⟨ya, yb, z', θ, h0, h1, hlt, hz', rfl⟩)
      simpa using this
    have hS : sSup D ≤ β * sSup D := csSup_le ⟨d₀, hd₀⟩ hle
    have hpos : 0 < d₀ := by
      obtain ⟨a, b, z, θ, h0, h1, hab, -, rfl⟩ := hd₀
      exact sub_pos.2 (hmono z hab)
    have := lt_of_lt_of_le hpos (le_csSup hbdd hd₀)
    nlinarith [h.β_lt]
  intro x x' hne θ h0 h1
  refine lt_of_le_of_ne (hvc z x x' θ h0.le h1.le) fun heq => ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmem : v (x', z) - v (x, z) ∈ D := ⟨x, x', z, θ, h0, h1, hlt, heq.symm, rfl⟩
    rw [hD] at hmem
    exact hmem
  · have h0' : 0 < 1 - θ := by linarith
    have h1' : 1 - θ < 1 := by linarith
    have hc : cmb (convex_Icc 0 xbar) h0'.le h1'.le x' x =
        cmb (convex_Icc 0 xbar) h0.le h1.le x x' := by
      ext1
      rw [cmb_val, cmb_val]
      ring
    dsimp only at heq
    have hmem : v (x, z) - v (x', z) ∈ D := ⟨x', x, z, 1 - θ, h0', h1', hlt, by
      rw [hc, ← heq]; ring, rfl⟩
    rw [hD] at hmem
    exact hmem

/-- `y ↦ ∫ v(y, z′) μ(dz′)` is strictly concave when each `v(·, z′)` is. -/
theorem strictConcave_integral {μ : Measure (Icc (1 : ℝ) zbar)} [IsProbabilityMeasure μ]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : ∀ z, IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) :
    IsStrictConcaveS (convex_Icc 0 xbar) fun y => ∫ z', v (y, z') ∂μ := by
  intro x x' hne θ h0 h1
  have hint := integrable_section_v μ v
  dsimp only
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint x).const_mul θ) ((hint x').const_mul _)]
  exact integral_lt_integral_of_lt (((hint x).const_mul θ).add ((hint x').const_mul _))
    (hint _) fun z' => hv z' x x' hne θ h0 h1

/-- With `U` concave and `W` strictly concave, `y ↦ U(c − y) + βW(y)` has at most one maximizer
on `{y ∈ [0, x̄] : y ≤ c}`. -/
theorem growth_argmax_unique (hU : ConcaveOn ℝ (Ici 0) U) (hβ : 0 < β)
    {W : Icc (0 : ℝ) xbar → ℝ} (hW : IsStrictConcaveS (convex_Icc 0 xbar) W) {c : ℝ}
    {y₁ y₂ : Icc (0 : ℝ) xbar} (h₁ : y₁.1 ≤ c) (h₂ : y₂.1 ≤ c)
    (hm₁ : ∀ y : Icc (0 : ℝ) xbar, y.1 ≤ c →
      U (max (c - y.1) 0) + β * W y ≤ U (max (c - y₁.1) 0) + β * W y₁)
    (hm₂ : ∀ y : Icc (0 : ℝ) xbar, y.1 ≤ c →
      U (max (c - y.1) 0) + β * W y ≤ U (max (c - y₂.1) 0) + β * W y₂) : y₁ = y₂ := by
  by_contra hne
  have hh0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hh1 : (1 / 2 : ℝ) < 1 := by norm_num
  set m := cmb (convex_Icc 0 xbar) hh0.le hh1.le y₁ y₂
  have hmv : m.1 = 1 / 2 * y₁.1 + (1 - 1 / 2) * y₂.1 := cmb_val _ _
  have hmc : m.1 ≤ c := by rw [hmv]; linarith
  have hWm := hW y₁ y₂ hne (1 / 2) hh0 hh1
  have hUm := hU.2 (show c - y₁.1 ∈ Ici 0 from sub_nonneg.2 h₁)
    (show c - y₂.1 ∈ Ici 0 from sub_nonneg.2 h₂) hh0.le hh0.le (by norm_num)
  simp only [smul_eq_mul] at hUm
  have e : 1 / 2 * (c - y₁.1) + 1 / 2 * (c - y₂.1) = c - m.1 := by rw [hmv]; ring
  rw [e] at hUm
  have h1' := hm₁ m hmc
  have h12 := hm₁ y₂ h₂
  have h21 := hm₂ y₁ h₁
  rw [max_eq_left (sub_nonneg.2 hmc), max_eq_left (sub_nonneg.2 h₁)] at h1'
  rw [max_eq_left (sub_nonneg.2 h₁), max_eq_left (sub_nonneg.2 h₂)] at h12 h21
  nlinarith [mul_lt_mul_of_pos_left hWm hβ]

/-- The objective of (2): `U[z f(x) − y] + β ∫ v(y, z′) Q(z, dz′)`. -/
theorem growth_objG (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    (v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → ℝ) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar)
    (y : Icc (0 : ℝ) xbar) :
    objG (growthModel Q U f β xbar) v (s, y) =
      U (max (s.2.1 * f s.1.1 - y.1) 0) + β * ∫ z', v (y, z') ∂Q s.2 := rfl

/-- **Exercise 10.1c.** With `U` strictly concave (U4) and `f` concave (T4), `v(·, z)` is strictly
increasing and strictly concave, and the policy correspondence is a continuous single-valued
function `g`. -/
theorem ex_10_1c [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar zbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v) :
    (∀ z, StrictMono fun x => v (x, z)) ∧
      (∀ z, IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) ∧
      UniqueArgmax (growthΓ f xbar zbar) (objG (growthModel Q U f β xbar) v) ∧
      (∀ s, policy (growthModel Q U f β xbar) v s =
        {argmaxFn (growthΓ f xbar zbar) (objG (growthModel Q U f β xbar) v) s}) ∧
      Continuous (argmaxFn (growthΓ f xbar zbar) (objG (growthModel Q U f β xbar) v)) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  have hsc := growth_strictConcave h hU hf Q hQ hv
  have hUA : UniqueArgmax (growthΓ f xbar zbar) (objG M v) := by
    refine ⟨hb.nonempty, hb.compact, hb.lhc, hb.uhc, continuousOn_objG M hb v,
      fun s y₁ hy₁ y₂ hy₂ => ?_⟩
    have hle := fun y (hy : y ∈ growthΓ f xbar zbar s) =>
      le_maxValue (continuousOn_objG M hb v) (hb.compact s) hy
    refine growth_argmax_unique hU.concaveOn h.β_pos
      (W := fun y => ∫ z', v (y, z') ∂Q s.2) (strictConcave_integral hsc) hy₁.1 hy₂.1
      (fun y hy => ?_) (fun y hy => ?_)
    · have := hle y hy
      rw [← hy₁.2, growth_objG, growth_objG] at this
      exact this
    · have := hle y hy
      rw [← hy₂.2, growth_objG, growth_objG] at this
      exact this
  refine ⟨growth_strictMono h Q hQ hv, hsc, hUA, fun s => ?_, hUA.continuous_argmaxFn⟩
  rw [policy_eq_argmax M hb hv]
  exact hUA.argmax_eq s

end StokeyLucasPrescott.StochasticApplications
