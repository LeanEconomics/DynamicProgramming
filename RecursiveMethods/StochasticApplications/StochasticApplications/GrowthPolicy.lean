/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.OneSectorGrowth

/-!
# The one-sector growth model: the policy function, differentiability, Markov shocks

SLP §10.1, Exercise 10.1d–f, pp. 289–290.

* **Exercise 10.1d** (`ex_10_1d`). With i.i.d. shocks (`Q(z, ·) = λ`, which is Feller:
  `isFeller_const`), `g(x, z) = h[z f(x)]`, where `h` is the continuous policy function of the
  problem in output `s = z f(x)`: `max_{0 ≤ y ≤ s} U(s − y) + β ∫ v(y, z′) λ(dz′)` (`outΓ`,
  `outH`). Both `h` and consumption `s − h(s)` are nondecreasing (by exchange arguments, using
  the strict concavity of `U` and of `v(·, z′)`), so `g` and `c = z f(x) − g` are nondecreasing in
  both arguments. **Correction:** they need not be strictly increasing. With
  `U(c) = 1 − e^{−c}`, `f(x) = 2x/(1 + x)`, `z̄ = 2`, `x̄ = 3`, `β = 1/10` — which satisfy
  (U1)–(U4), (T1)–(T4) and (Z1) — `v(x, z) − v(0, z) ≤ 4x`, so saving is never worth its cost
  at low output: `G(x, z) = {0}` for `x ≤ 1/10`, for any Feller `Q` (`ex_10_1d_counterexample`,
  `ex_10_1d_not_strictMono`). The manual's proof uses the first-order condition, which fails
  at the corner `g = 0`.
* **Exercise 10.1e** (`ex_10_1e`): if `c = z f(x) − g(x, z) > 0`, `U` is differentiable at `c`
  and `f` at an interior `x`, then `v_x = U′(c) z f′(x)`; for interior `z`, `v_z = U′(c) f(x)`.
  Only `c > 0` is needed, not `g > 0`. Both follow from Benveniste–Scheinkman (Theorem 4.10):
  in `x` because `v(·, z)` is concave, in `z` because, with i.i.d. shocks, `v(x, ·)` is concave
  (`growth_concave_z`).
* **Exercise 10.1f** (`ex_10_1f`): with a Feller `Q`, parts (a)–(c) hold (they are proved for
  any Feller `Q`), and `v_x = U′(c) z f′(x)` still holds (`growth_hasDerivAt_x`). If `Q` is
  monotone, `v(x, ·)` is nondecreasing, and strictly increasing for `x > 0`. That `g` is then
  increasing in `z` is not established: the manual compares `∫ v′(g, z′) Q(z, dz′)` across
  different measures `Q(z, ·)`, `Q(ẑ, ·)`, which concavity of `v(·, z′)` does not order.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {U f : ℝ → ℝ} {β xbar zbar : ℝ}

/-- I.i.d. shocks (Assumption (Z2)): `Q(z, ·) = λ` has the Feller property. -/
theorem isFeller_const {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] (lam : Measure Z) :
    IsFeller (Kernel.const Z lam) := fun f _ _ => by
  have : markovOpR (Kernel.const Z lam) f = fun _ => ∫ z', f z' ∂lam := by
    funext z
    simp [markovOpR, Kernel.const_apply]
  rw [this]
  exact continuous_const

/-- `y ↦ ∫ v(y, z′) μ(dz′)` is continuous. -/
theorem continuous_integral_section {S Z : Type*} [TopologicalSpace S] [FirstCountableTopology S]
    [TopologicalSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (v : S × Z →ᵇ ℝ) : Continuous fun y => ∫ z', v (y, z') ∂μ :=
  continuous_of_dominated (bound := fun _ => ‖v‖)
    (fun y => (v.continuous.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ => v.norm_coe_le_norm _) (integrable_const _)
    (Eventually.of_forall fun z' => v.continuous.comp (Continuous.prodMk_left z'))

/-- **The exchange inequality.** For `φ` strictly concave, `p < q < t` and `p + t = q + r`,
`φ(p) + φ(t) < φ(q) + φ(r)`. -/
theorem strictConcave_exchange {S : Set ℝ} {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ S φ)
    {p q r t : ℝ} (hp : p ∈ S) (ht : t ∈ S) (hpq : p < q) (hqt : q < t) (hsum : p + t = q + r) :
    φ p + φ t < φ q + φ r := by
  have hpt : 0 < t - p := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (t - q) / (t - p) := ⟨_, rfl⟩
  have hat : a * (t - p) = t - q := by rw [ha]; exact div_mul_cancel₀ _ hpt.ne'
  have ha0 : 0 < a := by rw [ha]; exact div_pos (by linarith) hpt
  have ha1 : 0 < 1 - a := by
    have : a * (t - p) < 1 * (t - p) := by rw [hat]; linarith
    linarith [lt_of_mul_lt_mul_right this hpt.le]
  have hq : a • p + (1 - a) • t = q := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * hat
  have hr : (1 - a) • p + a • t = r := by
    simp only [smul_eq_mul]; linear_combination hat + hsum
  have h1 := hφ.2 hp ht (hpq.trans hqt).ne ha0 ha1 (by ring)
  have h2 := hφ.2 hp ht (hpq.trans hqt).ne ha1 ha0 (by ring)
  rw [hq] at h1
  rw [hr] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- A strictly concave function on `S` is strictly concave on `S ⊆ E` after extension. -/
theorem strictConcaveOn_liftS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    {hS : Convex ℝ S} {W : S → ℝ} (hW : IsStrictConcaveS hS W) :
    StrictConcaveOn ℝ S (liftS W) := by
  refine ⟨hS, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hmem : a • x + (1 - a) • y ∈ S := hS hx hy ha.le hb.le hab
  rw [liftS_of_mem W hx, liftS_of_mem W hy, liftS_of_mem W hmem, smul_eq_mul, smul_eq_mul]
  exact hW ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxy (congrArg Subtype.val h)) a ha (by linarith)

/-! ### Exercise 10.1d: the policy function under i.i.d. shocks -/

/-- `Γ′(s) = {y ∈ X : y ≤ s}`: the constraint of the problem in output `s`. -/
def outΓ (xbar : ℝ) (s : Icc (0 : ℝ) xbar) : Set (Icc (0 : ℝ) xbar) := {y | y.1 ≤ s.1}

/-- The objective `U(s − y) + β ∫ v(y, z′) λ(dz′)` of the problem in output. -/
noncomputable def outH (U : ℝ → ℝ) (β : ℝ) (lam : Measure (Icc (1 : ℝ) zbar))
    (v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → ℝ) (p : Icc (0 : ℝ) xbar × Icc (0 : ℝ) xbar) :
    ℝ :=
  U (max (p.1.1 - p.2.1) 0) + β * ∫ z', v (p.2, z') ∂lam

/-- Output `s(x, z) = z f(x)`, a point of `X`. -/
def outS (h : GrowthHyp U f β xbar zbar) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    Icc (0 : ℝ) xbar :=
  ⟨s.2.1 * f s.1.1, h.zf_nonneg s, h.zf_le s⟩

/-- The problem in output has a unique maximizer `h(s)`, continuous in `s` (Theorem 3.6). -/
theorem outH_uniqueArgmax (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : ∀ z, IsStrictConcaveS (convex_Icc 0 xbar) fun x => v (x, z)) :
    UniqueArgmax (outΓ xbar) (outH U β lam v) := by
  have hc : Continuous (outH U β lam v) :=
    (h.U_cont.comp_continuous (((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).max continuous_const)
      fun _ => mem_Ici.2 (le_max_right _ _)).add
      (continuous_const.mul ((continuous_integral_section lam v).comp continuous_snd))
  have hcpt : ∀ s, IsCompact (outΓ xbar s) := fun _ =>
    IsClosed.isCompact (isClosed_le continuous_subtype_val continuous_const)
  refine ⟨fun s => ⟨⟨0, le_rfl, h.xbar_pos.le⟩, s.2.1⟩, hcpt,
    isLHC_Icc_le continuous_subtype_val (fun s => s.2.1) h.xbar_pos.le,
    isUHC_Icc_le continuous_subtype_val (fun s => s.2.1) h.xbar_pos.le, hc.continuousOn,
    fun s y₁ hy₁ y₂ hy₂ => ?_⟩
  have hle := fun y (hy : y ∈ outΓ xbar s) => le_maxValue hc.continuousOn (hcpt s) hy
  refine growth_argmax_unique hU h.β_pos (W := fun y => ∫ z', v (y, z') ∂lam)
    (strictConcave_integral hv) hy₁.1 hy₂.1 (fun y hy => ?_) (fun y hy => ?_)
  · have := hle y hy
    rw [← hy₁.2] at this
    exact this
  · have := hle y hy
    rw [← hy₂.2] at this
    exact this

/-- Under i.i.d. shocks the maximization in (2) is the problem in output at `s = z f(x)`. -/
theorem growth_argmax_eq_out (h : GrowthHyp U f β xbar zbar) (lam : Measure (Icc (1 : ℝ) zbar))
    (v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar → ℝ) (s : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar) :
    argmax (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (growthΓ f xbar zbar) s =
      argmax (outH U β lam v) (outΓ xbar) (outS h s) := by
  have hobj : ∀ y, objG (growthModel (Kernel.const _ lam) U f β xbar) v (s, y) =
      outH U β lam v (outS h s, y) := fun y => by
    rw [growth_objG, Kernel.const_apply]
    rfl
  simp only [argmax, maxValue, hobj]
  rfl

/-- **Exercise 10.1d.** Under i.i.d. shocks, with (U4) strict and (T4), the policy function is
`g(x, z) = h[z f(x)]` with `h` continuous, and `h` and consumption `s − h(s)` are
nondecreasing; hence `g` and `c(x, z) = z f(x) − g(x, z)` are nondecreasing in `x` and in `z`.
(They need not be strictly increasing: `ex_10_1d_not_strictMono`.) -/
theorem ex_10_1d [Nonempty (Icc (0 : ℝ) xbar)] (h : GrowthHyp U f β xbar zbar)
    (hU : StrictConcaveOn ℝ (Ici 0) U) (hf : ConcaveOn ℝ (Ici 0) f)
    (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v) :
    (∀ s, argmaxFn (growthΓ f xbar zbar) (objG (growthModel (Kernel.const _ lam) U f β xbar) v) s =
      argmaxFn (outΓ xbar) (outH U β lam v) (outS h s)) ∧
    Continuous (argmaxFn (outΓ xbar) (outH U β lam v)) ∧
    Monotone (argmaxFn (outΓ xbar) (outH U β lam v)) ∧
    Monotone (fun s => s.1 - (argmaxFn (outΓ xbar) (outH U β lam v) s).1) ∧
    (∀ z, Monotone fun x => argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)) ∧
    (∀ x, Monotone fun z => argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)) ∧
    (∀ z, Monotone fun x => z.1 * f x.1 - (argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)).1) ∧
    (∀ x, Monotone fun z => z.1 * f x.1 - (argmaxFn (growthΓ f xbar zbar)
      (objG (growthModel (Kernel.const _ lam) U f β xbar) v) (x, z)).1) := by
  set M := growthModel (Kernel.const _ lam) U f β xbar
  obtain ⟨-, hsc, hUA, -, -⟩ := ex_10_1c h hU hf _ (isFeller_const lam) hv
  have hO := outH_uniqueArgmax h hU.concaveOn lam hsc
  set hs := argmaxFn (outΓ xbar) (outH U β lam v)
  -- `g = h ∘ s`
  have hgs : ∀ s, argmaxFn (growthΓ f xbar zbar) (objG M v) s = hs (outS h s) := fun s => by
    have h1 := hUA.argmax_eq s
    rw [growth_argmax_eq_out h lam v s, hO.argmax_eq] at h1
    exact (Set.singleton_eq_singleton_iff.1 h1).symm
  have hmem : ∀ s, (hs s).1 ≤ s.1 := fun s => (hO.argmaxFn_mem s).1
  have hopt : ∀ s y, y ∈ outΓ xbar s → outH U β lam v (s, y) ≤ outH U β lam v (s, hs s) :=
    fun s y hy => by
      rw [(hO.argmaxFn_mem s).2]
      exact le_maxValue hO.cont (hO.compact s) hy
  have hval : ∀ s y, y.1 ≤ s.1 →
      outH U β lam v (s, y) = U (s.1 - y.1) + β * ∫ z', v (y, z') ∂lam := fun s y hy => by
    simp only [outH, max_eq_left (sub_nonneg.2 hy)]
  have hlt_of : ∀ s s' : Icc (0 : ℝ) xbar, s ≤ s' → s ≠ s' → s.1 < s'.1 := fun s s' hle hne =>
    lt_of_le_of_ne hle fun heq => hne (Subtype.ext heq)
  -- `h` is nondecreasing
  have hmono : Monotone hs := by
    intro s s' hss'
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hlt' : (hs s').1 < (hs s).1 := hlt
    have hss : s.1 < s'.1 := hlt_of s s' hss' fun heq => by subst heq; exact lt_irrefl _ hlt
    have h1 := hopt s (hs s') (show (hs s').1 ≤ s.1 by linarith [hmem s])
    have h2 := hopt s' (hs s) (show (hs s).1 ≤ s'.1 by linarith [hmem s])
    rw [hval s _ (by linarith [hmem s]), hval s _ (hmem s)] at h1
    rw [hval s' _ (by linarith [hmem s]), hval s' _ (hmem s')] at h2
    have := strictConcave_exchange hU (p := s.1 - (hs s).1) (q := s.1 - (hs s').1)
      (r := s'.1 - (hs s).1) (t := s'.1 - (hs s').1) (sub_nonneg.2 (hmem s))
      (sub_nonneg.2 (hmem s')) (by linarith) (by linarith) (by ring)
    linarith
  -- consumption `s − h(s)` is nondecreasing
  have hW := strictConcaveOn_liftS (strictConcave_integral (μ := lam) hsc)
  have hWv : ∀ y : Icc (0 : ℝ) xbar, liftS (fun y => ∫ z', v (y, z') ∂lam) y.1 =
      ∫ z', v (y, z') ∂lam := fun y => liftS_of_mem _ y.2
  have hcons : Monotone fun s => s.1 - (hs s).1 := by
    intro s s' hss'
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hss : s.1 < s'.1 := hlt_of s s' hss' fun heq => by subst heq; exact lt_irrefl _ hlt
    have hy := (hs s).2
    have hy' := (hs s').2
    have hms := hmem s
    have hms' := hmem s'
    -- `y₁ = s − c′` at `s`, `y₂ = s′ − c` at `s′`
    have hy0 := (hs s).2.1
    have hy0' := (hs s').2.1
    set y₁ : Icc (0 : ℝ) xbar := ⟨s.1 - (s'.1 - (hs s').1), by
      constructor <;> linarith [s.2.2]⟩
    set y₂ : Icc (0 : ℝ) xbar := ⟨s'.1 - (s.1 - (hs s).1), by
      constructor <;> linarith [s'.2.2]⟩
    have h1 := hopt s y₁ (show y₁.1 ≤ s.1 by simp only [y₁]; linarith)
    have h2 := hopt s' y₂ (show y₂.1 ≤ s'.1 by simp only [y₂]; linarith)
    rw [hval s _ (show y₁.1 ≤ s.1 by simp only [y₁]; linarith), hval s _ hms] at h1
    rw [hval s' _ (show y₂.1 ≤ s'.1 by simp only [y₂]; linarith), hval s' _ hms'] at h2
    have e1 : s.1 - y₁.1 = s'.1 - (hs s').1 := by simp only [y₁]; ring
    have e2 : s'.1 - y₂.1 = s.1 - (hs s).1 := by simp only [y₂]; ring
    rw [e1] at h1
    rw [e2] at h2
    have hex := strictConcave_exchange hW (p := (hs s).1) (q := y₁.1) (r := y₂.1)
      (t := (hs s').1) (hs s).2 (hs s').2 (by simp only [y₁]; linarith)
      (by simp only [y₁]; linarith) (by simp only [y₁, y₂]; ring)
    rw [hWv, hWv, hWv, hWv] at hex
    nlinarith [h.β_pos]
  -- composition with `s(x, z) = z f(x)`
  have hsx : ∀ z, Monotone fun x => outS h (x, z) := fun z x x' hxx' => by
    change z.1 * f x.1 ≤ z.1 * f x'.1
    exact mul_le_mul_of_nonneg_left (h.f_mono.monotoneOn x.2.1 x'.2.1 hxx')
      (by linarith [z.2.1])
  have hsz : ∀ x, Monotone fun z => outS h (x, z) := fun x z z' hzz' => by
    change z.1 * f x.1 ≤ z'.1 * f x.1
    exact mul_le_mul_of_nonneg_right hzz' (h.f_nonneg x.2.1)
  refine ⟨hgs, hO.continuous_argmaxFn, hmono, hcons, fun z x x' hxx' => ?_,
    fun x z z' hzz' => ?_, fun z x x' hxx' => ?_, fun x z z' hzz' => ?_⟩
  · simp only [hgs]; exact hmono (hsx z hxx')
  · simp only [hgs]; exact hmono (hsz x hzz')
  · simp only [hgs]; exact hcons (hsx z hxx')
  · simp only [hgs]; exact hcons (hsz x hzz')

/-! ### The corner counterexample -/

/-- `U(c) = 1 − e^{−c}`. -/
noncomputable def cexU (c : ℝ) : ℝ := 1 - Real.exp (-c)

/-- `f(x) = 2x/(1 + x)`. -/
noncomputable def cexf (x : ℝ) : ℝ := 2 * x / (1 + x)

/-- The example satisfies (U1)–(U3), (T1)–(T3) and (Z1), with `x̄ = 3 = 2 f(3)`. -/
theorem cex_hyp : GrowthHyp cexU cexf (1 / 10) 3 2 where
  β_pos := by norm_num
  β_lt := by norm_num
  U_cont := (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousOn
  U_mono := fun c _ c' _ hcc' => by
    simp only [cexU]
    have := Real.exp_lt_exp.2 (neg_lt_neg hcc')
    linarith
  f_cont := ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by
    have : (0 : ℝ) ≤ x := hx
    exact (by linarith : (0 : ℝ) < 1 + x).ne'
  f_zero := by simp [cexf]
  f_mono := fun x hx x' hx' hxx' => by
    have hx0 : (0 : ℝ) ≤ x := hx
    have hx0' : (0 : ℝ) ≤ x' := hx'
    simp only [cexf]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  zbar_gt := by norm_num
  xbar_pos := by norm_num
  xbar_maintain := by norm_num [cexf]

/-- (U4): `U(c) = 1 − e^{−c}` is strictly concave. -/
theorem cexU_strictConcave : StrictConcaveOn ℝ (Ici 0) cexU := by
  refine ⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have := strictConvexOn_exp.2 (mem_univ (-x)) (mem_univ (-y))
    (fun h => hxy (neg_inj.1 h)) ha hb hab
  simp only [smul_eq_mul, cexU] at this ⊢
  have e : a * -x + b * -y = -(a * x + b * y) := by ring
  rw [e] at this
  linarith

/-- (T4): `f(x) = 2x/(1 + x)` is concave on `[0, ∞)`. -/
theorem cexf_concave : ConcaveOn ℝ (Ici 0) cexf := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul, cexf]
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 + y := by linarith
  have h3 : (0 : ℝ) < 1 + (a * x + (1 - a) * y) := by nlinarith
  rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀
    (mul_pos h1 h2) h3]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]

/-- In the example, `v(x, z) − v(0, z) ≤ 4x`: the set of such functions is closed and mapped into
itself by `T`, since `U(c) − U(0) ≤ c`, `βK = 2/5 ≤ 1` and `z f(x) ≤ 4x`. -/
theorem cex_lipschitz (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (growthModel Q cexU cexf (1 / 10) 3) (growth_boundedDP cex_hyp Q hQ) v = v)
    (x : Icc (0 : ℝ) 3) (z : Icc (1 : ℝ) 2) :
    v (x, z) - v (⟨0, le_rfl, by norm_num⟩, z) ≤ 4 * x.1 := by
  set M := growthModel Q cexU cexf (1 / 10) 3
  have hb := growth_boundedDP cex_hyp Q hQ
  obtain ⟨x0, hx0⟩ : ∃ x0 : Icc (0 : ℝ) 3, x0 = ⟨0, le_rfl, by norm_num⟩ := ⟨_, rfl⟩
  rw [← hx0]
  set C : Set (Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ) :=
    {w | ∀ x z, w (x, z) - w (x0, z) ≤ 4 * x.1}
  have hclosed : IsClosed C := by
    have : C = ⋂ x, ⋂ z, {w : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ |
        w (x, z) - w (x0, z) ≤ 4 * x.1} := by
      ext w; simp only [C, mem_ofPred_eq, mem_iInter]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun z =>
      isClosed_le ((continuous_eval_const _).sub (continuous_eval_const _)) continuous_const
  have hmaps : MapsTo (bellman M hb) C C := by
    intro w hw x z
    obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb w (x, z)
    obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (x0, z)
    have h0 : x0 ∈ M.Γ (x0, z) := by
      change x0.1 ≤ z.1 * cexf x0.1
      simp [hx0, cexf]
    have hm := hmax x0 h0
    have hint := integrable_section_v (Q z) w
    have hE : ∫ z', w (y, z') ∂Q z - ∫ z', w (x0, z') ∂Q z ≤ 4 * y.1 := by
      rw [← integral_sub (hint y) (hint x0)]
      have := integral_mono (μ := Q z) ((hint y).sub (hint x0)) (integrable_const (4 * y.1))
        fun z' => hw y z'
      simpa using this
    simp only [rhs, expV] at hval hm
    change bellman M hb w (x, z) =
      growthF cexU cexf 3 2 (x, y, z) + 1 / 10 * ∫ z', w (y, z') ∂Q z at hval
    change growthF cexU cexf 3 2 (x0, x0, z) + 1 / 10 * ∫ z', w (x0, z') ∂Q z ≤
      bellman M hb w (x0, z) at hm
    rw [growthF_of_mem hy] at hval
    have hF0 : growthF cexU cexf 3 2 (x0, x0, z) = 0 := by simp [growthF, hx0, cexU, cexf]
    rw [hF0] at hm
    have hyz : y.1 ≤ z.1 * cexf x.1 := hy
    have hUc : cexU (z.1 * cexf x.1 - y.1) ≤ z.1 * cexf x.1 - y.1 := by
      simp only [cexU]
      linarith [Real.add_one_le_exp (-(z.1 * cexf x.1 - y.1))]
    have hfx : cexf x.1 ≤ 2 * x.1 := by
      simp only [cexf]
      exact div_le_self (by linarith [x.2.1]) (by linarith [x.2.1])
    have hzf : z.1 * cexf x.1 ≤ 4 * x.1 := by
      have := mul_le_mul z.2.2 hfx (by simp only [cexf]; have := x.2.1; positivity)
        (by norm_num)
      linarith
    change bellman M hb w (x, z) - bellman M hb w (x0, z) ≤ 4 * x.1
    linarith [y.2.1]
  have hzero : (0 : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ) ∈ C := fun x _ => by
    simp only [coe_zero, Pi.zero_apply, sub_self]
    linarith [x.2.1]
  exact (corollary_1 (bellman_contraction M hb) hv ⟨0, hzero⟩ hclosed hmaps hmaps).1 x z

/-- **Exercise 10.1d, corrected.** In the example, for any Feller `Q` (i.i.d. shocks included),
the only optimal choice at `x ≤ 1/10` is `y = 0`: the marginal utility `e^{−s} ≥ 3/5` of
consumption exceeds the bound `βK = 2/5` on the marginal value of capital. -/
theorem ex_10_1d_counterexample (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (growthModel Q cexU cexf (1 / 10) 3) (growth_boundedDP cex_hyp Q hQ) v = v)
    {x : Icc (0 : ℝ) 3} (hx : x.1 ≤ 1 / 10) (z : Icc (1 : ℝ) 2) {y : Icc (0 : ℝ) 3}
    (hy : y ∈ policy (growthModel Q cexU cexf (1 / 10) 3) v (x, z)) : y.1 = 0 := by
  set M := growthModel Q cexU cexf (1 / 10) 3
  have hb := growth_boundedDP cex_hyp Q hQ
  obtain ⟨x0, hx0⟩ : ∃ x0 : Icc (0 : ℝ) 3, x0 = ⟨0, le_rfl, by norm_num⟩ := ⟨_, rfl⟩
  have hL := fun z' => cex_lipschitz Q hQ hv y z'
  rw [← hx0] at hL
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb v (x, z)
  have h0 : x0 ∈ M.Γ (x, z) := by
    change x0.1 ≤ z.1 * cexf x.1
    rw [hx0]
    exact mul_nonneg (by linarith [z.2.1]) (by simp only [cexf]; have := x.2.1; positivity)
  have hm := hmax x0 h0
  rw [hv] at hm
  have hyv := hy.2
  have hint := integrable_section_v (Q z) v
  have hE : ∫ z', v (y, z') ∂Q z - ∫ z', v (x0, z') ∂Q z ≤ 4 * y.1 := by
    rw [← integral_sub (hint y) (hint x0)]
    have := integral_mono (μ := Q z) ((hint y).sub (hint x0)) (integrable_const (4 * y.1)) hL
    simpa using this
  simp only [rhs, expV] at hm hyv
  change growthF cexU cexf 3 2 (x, x0, z) + 1 / 10 * ∫ z', v (x0, z') ∂Q z ≤ v (x, z) at hm
  change v (x, z) = growthF cexU cexf 3 2 (x, y, z) + 1 / 10 * ∫ z', v (y, z') ∂Q z at hyv
  have hx00 : x0.1 = 0 := by rw [hx0]
  rw [growthF_of_mem h0, hx00, sub_zero] at hm
  rw [growthF_of_mem hy.1] at hyv
  -- output `s = z f(x) ≤ 2/5`
  set s := z.1 * cexf x.1
  have hfx : cexf x.1 ≤ 2 * x.1 := by
    simp only [cexf]
    exact div_le_self (by linarith [x.2.1]) (by linarith [x.2.1])
  have hs : s ≤ 2 / 5 := by
    have := mul_le_mul z.2.2 hfx (by simp only [cexf]; have := x.2.1; positivity) (by norm_num)
    linarith
  simp only [cexU] at hm hyv
  have hes : 3 / 5 ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
  have hey : 1 + y.1 ≤ Real.exp y.1 := by linarith [Real.add_one_le_exp y.1]
  have hsplit : Real.exp (-(s - y.1)) = Real.exp y.1 * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit] at hyv
  have hpos := Real.exp_pos (-s)
  have k1 := mul_nonneg hpos.le (sub_nonneg.2 hey)
  have k2 := mul_nonneg y.2.1 (sub_nonneg.2 hes)
  have : y.1 ≤ 0 := by linarith
  linarith [y.2.1]

/-- **Exercise 10.1d, corrected.** In the example no selection `g` from `G` is strictly increasing
in `x`: `g(0, z) = g(1/10, z) = 0`. -/
theorem ex_10_1d_not_strictMono (Q : Kernel (Icc (1 : ℝ) 2) (Icc (1 : ℝ) 2)) [IsMarkovKernel Q]
    (hQ : IsFeller Q) {v : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 →ᵇ ℝ}
    (hv : bellman (growthModel Q cexU cexf (1 / 10) 3) (growth_boundedDP cex_hyp Q hQ) v = v)
    {g : Icc (0 : ℝ) 3 × Icc (1 : ℝ) 2 → Icc (0 : ℝ) 3}
    (hg : ∀ s, g s ∈ policy (growthModel Q cexU cexf (1 / 10) 3) v s) (z : Icc (1 : ℝ) 2) :
    ¬ StrictMono fun x => g (x, z) := by
  intro hmono
  have hlt : (⟨0, le_rfl, by norm_num⟩ : Icc (0 : ℝ) 3) < ⟨1 / 10, by norm_num, by norm_num⟩ :=
    show (0 : ℝ) < 1 / 10 by norm_num
  have := hmono hlt
  have h1 := ex_10_1d_counterexample Q hQ hv (x := ⟨0, le_rfl, by norm_num⟩)
    (show (0 : ℝ) ≤ 1 / 10 by norm_num) z (hg _)
  have h2 := ex_10_1d_counterexample Q hQ hv (x := ⟨1 / 10, by norm_num, by norm_num⟩)
    (show (1 / 10 : ℝ) ≤ 1 / 10 by norm_num) z (hg _)
  have : (g (⟨0, le_rfl, by norm_num⟩, z)).1 < (g (⟨1 / 10, by norm_num, by norm_num⟩, z)).1 :=
    this
  linarith

/-! ### Exercise 10.1e–f: differentiability and Markov shocks -/

/-- Benveniste–Scheinkman (Theorem 4.10) on the line. -/
theorem hasDerivAt_of_concaveOn_of_le {S : Set ℝ} {V L : ℝ → ℝ} {x₀ d : ℝ}
    (hV : ConcaveOn ℝ S V) (hS : S ∈ 𝓝 x₀) (hL : HasDerivAt L d x₀) (heq : L x₀ = V x₀)
    (hle : ∀ᶠ x in 𝓝 x₀, L x ≤ V x) : HasDerivAt V d x₀ := by
  have := (theorem_4_10 hV hS hL.hasFDerivAt heq hle).hasDerivAt
  simpa using this

/-- The return to any feasible `y` is at most the value: `U[z f(x) − y] + βE v(y, ·) ≤ v(x, z)`. -/
theorem growth_rhs_le (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    {x y : Icc (0 : ℝ) xbar} {z : Icc (1 : ℝ) zbar} (hy : y ∈ growthΓ f xbar zbar (x, z)) :
    U (z.1 * f x.1 - y.1) + β * ∫ z', v (y, z') ∂Q z ≤ v (x, z) := by
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax _ (growth_boundedDP h Q hQ) v (x, z)
  have := hmax y hy
  rw [hv] at this
  simp only [rhs, expV] at this
  change growthF U f xbar zbar (x, y, z) + β * _ ≤ _ at this
  rwa [growthF_of_mem hy] at this

/-- At an optimal `y`, `v(x, z) = U[z f(x) − y] + βE v(y, ·)`. -/
theorem growth_eq_of_policy {Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)}
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ} {x y : Icc (0 : ℝ) xbar}
    {z : Icc (1 : ℝ) zbar} (hy : y ∈ policy (growthModel Q U f β xbar) v (x, z)) :
    v (x, z) = U (z.1 * f x.1 - y.1) + β * ∫ z', v (y, z') ∂Q z := by
  have := hy.2
  simp only [rhs, expV] at this
  change v (x, z) = growthF U f xbar zbar (x, y, z) + β * _ at this
  rwa [growthF_of_mem hy.1] at this

/-- **Exercise 10.1e–f** (`v_x`). With `U` and `f` concave and any Feller `Q`: if `y₀` is optimal
at `(x₀, z₀)` with `x₀ < x̄` and consumption `c = z₀ f(x₀) − y₀ > 0`, `U` is differentiable at
`c` and `f` at `x₀`, then `v_x(x₀, z₀) = U′(c) z₀ f′(x₀)`. -/
theorem growth_hasDerivAt_x (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar))
    [IsMarkovKernel Q] (hQ : IsFeller Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v)
    {x₀ y₀ : Icc (0 : ℝ) xbar} {z₀ : Icc (1 : ℝ) zbar} (hx₀ : x₀.1 < xbar)
    (hy₀ : y₀ ∈ policy (growthModel Q U f β xbar) v (x₀, z₀)) (hc : y₀.1 < z₀.1 * f x₀.1)
    {U' f' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 - y₀.1)) (hf' : HasDerivAt f f' x₀.1) :
    HasDerivAt (liftS fun x => v (x, z₀)) (U' * (z₀.1 * f')) x₀.1 := by
  have hvc := growth_concave h hU hf Q hQ hv z₀
  have hx0 : 0 < x₀.1 := by
    rcases x₀.2.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, h.f_zero, mul_zero] at hc
      linarith [y₀.2.1]
  have hS : Icc (0 : ℝ) xbar ∈ 𝓝 x₀.1 := Icc_mem_nhds hx0 hx₀
  have hL : HasDerivAt (fun x => U (z₀.1 * f x - y₀.1) + β * ∫ z', v (y₀, z') ∂Q z₀)
      (U' * (z₀.1 * f')) x₀.1 :=
    (hU'.comp x₀.1 ((hf'.const_mul z₀.1).sub_const y₀.1)).add_const _
  refine hasDerivAt_of_concaveOn_of_le (concaveOn_liftS hvc) hS hL ?_ ?_
  · rw [liftS_of_mem _ x₀.2]
    exact (growth_eq_of_policy hy₀).symm
  · have hev : ∀ᶠ x in 𝓝 x₀.1, y₀.1 < z₀.1 * f x :=
      (hf'.continuousAt.const_mul z₀.1).eventually (lt_mem_nhds hc)
    filter_upwards [hev, hS] with x hx hxS
    rw [liftS_of_mem _ hxS]
    exact growth_rhs_le h Q hQ hv (x := ⟨x, hxS⟩) hx.le

/-- Under i.i.d. shocks `v(x, ·)` is concave: the expectation does not depend on `z`, and the
constraint `y ≤ z f(x)` and the return `U[z f(x) − y]` are concave in `(z, y)`. -/
theorem growth_concave_z (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v) (x : Icc (0 : ℝ) xbar) :
    IsConcaveS (convex_Icc 1 zbar) fun z => v (x, z) := by
  set M := growthModel (Kernel.const _ lam) U f β xbar
  have hb := growth_boundedDP h _ (isFeller_const lam)
  have hvc := growth_concave h hU hf _ (isFeller_const lam) hv
  intro z₀ z₁ θ h0 h1
  obtain ⟨y₀, hy₀, hv₀, -⟩ := exists_bellman_argmax M hb v (x, z₀)
  obtain ⟨y₁, hy₁, hv₁, -⟩ := exists_bellman_argmax M hb v (x, z₁)
  rw [hv] at hv₀ hv₁
  have e₀ := growth_eq_of_policy (show y₀ ∈ policy M v (x, z₀) from ⟨hy₀, hv₀⟩)
  have e₁ := growth_eq_of_policy (show y₁ ∈ policy M v (x, z₁) from ⟨hy₁, hv₁⟩)
  rw [Kernel.const_apply] at e₀ e₁
  have hzθ : (cmb (convex_Icc 1 zbar) h0 h1 z₀ z₁).1 = θ * z₀.1 + (1 - θ) * z₁.1 := by
    simp [cmb]
  have hyθv := cmb_val (x₀ := y₀) (x₁ := y₁) h0 h1
  have c₀ : 0 ≤ z₀.1 * f x.1 - y₀.1 := sub_nonneg.2 hy₀
  have c₁ : 0 ≤ z₁.1 * f x.1 - y₁.1 := sub_nonneg.2 hy₁
  have hyθ : cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁ ∈
      growthΓ f xbar zbar (x, cmb (convex_Icc 1 zbar) h0 h1 z₀ z₁) := by
    change (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 ≤ _
    rw [hyθv, hzθ]
    have : 0 ≤ 1 - θ := by linarith
    nlinarith [mul_nonneg h0 c₀, mul_nonneg this c₁]
  have hle := growth_rhs_le h _ (isFeller_const lam) hv hyθ
  rw [Kernel.const_apply] at hle
  have hUc := hU.2 c₀ c₁ h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hUc
  have harg : θ * (z₀.1 * f x.1 - y₀.1) + (1 - θ) * (z₁.1 * f x.1 - y₁.1) =
      (cmb (convex_Icc 1 zbar) h0 h1 z₀ z₁).1 * f x.1 -
        (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁).1 := by
    rw [hyθv, hzθ]; ring
  rw [harg] at hUc
  have hint := integrable_section_v lam v
  have hE : θ * ∫ z', v (y₀, z') ∂lam + (1 - θ) * ∫ z', v (y₁, z') ∂lam ≤
      ∫ z', v (cmb (convex_Icc 0 xbar) h0 h1 y₀ y₁, z') ∂lam := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint y₀).const_mul θ) ((hint y₁).const_mul _)]
    exact integral_mono (((hint y₀).const_mul θ).add ((hint y₁).const_mul _)) (hint _)
      fun z' => hvc z' y₀ y₁ θ h0 h1
  have hβE := mul_le_mul_of_nonneg_left hE h.β_pos.le
  dsimp only
  rw [e₀, e₁]
  nlinarith

/-- **Exercise 10.1e** (`v_z`, i.i.d. shocks): `v_z(x₀, z₀) = U′(c) f(x₀)` at an interior `z₀`
when `c = z₀ f(x₀) − y₀ > 0` for an optimal `y₀`. -/
theorem growth_hasDerivAt_z (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v)
    {x₀ y₀ : Icc (0 : ℝ) xbar} {z₀ : Icc (1 : ℝ) zbar} (hz₁ : 1 < z₀.1) (hz₂ : z₀.1 < zbar)
    (hy₀ : y₀ ∈ policy (growthModel (Kernel.const _ lam) U f β xbar) v (x₀, z₀))
    (hc : y₀.1 < z₀.1 * f x₀.1) {U' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 - y₀.1)) :
    HasDerivAt (liftS fun z => v (x₀, z)) (U' * f x₀.1) z₀.1 := by
  have hvc := growth_concave_z h hU hf lam hv x₀
  have hS : Icc (1 : ℝ) zbar ∈ 𝓝 z₀.1 := Icc_mem_nhds hz₁ hz₂
  have hL : HasDerivAt (fun z => U (z * f x₀.1 - y₀.1) + β * ∫ z', v (y₀, z') ∂lam)
      (U' * f x₀.1) z₀.1 := by
    have := (hU'.comp z₀.1 (((hasDerivAt_id' z₀.1).mul_const (f x₀.1)).sub_const y₀.1)).add_const
      (β * ∫ z', v (y₀, z') ∂lam)
    simpa using this
  refine hasDerivAt_of_concaveOn_of_le (concaveOn_liftS hvc) hS hL ?_ ?_
  · rw [liftS_of_mem _ z₀.2]
    have := growth_eq_of_policy hy₀
    rw [Kernel.const_apply] at this
    exact this.symm
  · have hev : ∀ᶠ z in 𝓝 z₀.1, y₀.1 < z * f x₀.1 :=
      (continuous_id'.mul continuous_const).continuousAt.eventually (lt_mem_nhds hc)
    filter_upwards [hev, hS] with z hz hzS
    rw [liftS_of_mem _ hzS]
    have := growth_rhs_le h _ (isFeller_const lam) hv (x := x₀) (z := ⟨z, hzS⟩) hz.le
    rw [Kernel.const_apply] at this
    exact this

/-- **Exercise 10.1e.** Under i.i.d. shocks, with `U` and `f` concave: if `y₀` is optimal at an
interior `(x₀, z₀)` with consumption `c = z₀ f(x₀) − y₀ > 0`, `U` differentiable at `c` and `f`
at `x₀`, then `v_x(x₀, z₀) = U′(c) z₀ f′(x₀)` and `v_z(x₀, z₀) = U′(c) f(x₀)`. -/
theorem ex_10_1e (h : GrowthHyp U f β xbar zbar) (hU : ConcaveOn ℝ (Ici 0) U)
    (hf : ConcaveOn ℝ (Ici 0) f) (lam : Measure (Icc (1 : ℝ) zbar)) [IsProbabilityMeasure lam]
    {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel (Kernel.const _ lam) U f β xbar)
      (growth_boundedDP h _ (isFeller_const lam)) v = v)
    {x₀ y₀ : Icc (0 : ℝ) xbar} {z₀ : Icc (1 : ℝ) zbar} (hx₀ : x₀.1 < xbar) (hz₁ : 1 < z₀.1)
    (hz₂ : z₀.1 < zbar)
    (hy₀ : y₀ ∈ policy (growthModel (Kernel.const _ lam) U f β xbar) v (x₀, z₀))
    (hc : y₀.1 < z₀.1 * f x₀.1) {U' f' : ℝ} (hU' : HasDerivAt U U' (z₀.1 * f x₀.1 - y₀.1))
    (hf' : HasDerivAt f f' x₀.1) :
    HasDerivAt (liftS fun x => v (x, z₀)) (U' * (z₀.1 * f')) x₀.1 ∧
      HasDerivAt (liftS fun z => v (x₀, z)) (U' * f x₀.1) z₀.1 :=
  ⟨growth_hasDerivAt_x h hU hf _ (isFeller_const lam) hv hx₀ hy₀ hc hU' hf',
    growth_hasDerivAt_z h hU hf lam hv hz₁ hz₂ hy₀ hc hU'⟩

/-- With `Q` monotone, `T` maps functions nondecreasing in `z` to functions nondecreasing in `z`,
strictly increasing in `z` at `x > 0`. -/
theorem growth_bellman_mono_z (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q) {w : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hw : ∀ x, Monotone fun z => w (x, z)) (x : Icc (0 : ℝ) xbar) {z z' : Icc (1 : ℝ) zbar}
    (hzz' : z < z') :
    bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z) ≤
        bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z') ∧
      (0 < x.1 → bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z) <
        bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) w (x, z')) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M hb w (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M hb w (x, z')
  have hyz : y.1 ≤ z.1 * f x.1 := hy
  have hzz : z.1 < z'.1 := hzz'
  have hzle : z.1 * f x.1 ≤ z'.1 * f x.1 := mul_le_mul_of_nonneg_right hzz.le (h.f_nonneg x.2.1)
  have hy' : y ∈ M.Γ (x, z') := show y.1 ≤ z'.1 * f x.1 from hyz.trans hzle
  have hm := hmax y hy'
  have hE := expV_mono_z M hb hQm w hy hzz'.le (hw y)
  have hEβ := mul_le_mul_of_nonneg_left hE h.β_pos.le
  simp only [rhs] at hval hm
  change bellman M hb w (x, z) = growthF U f xbar zbar (x, y, z) + M.β * _ at hval
  change growthF U f xbar zbar (x, y, z') + M.β * _ ≤ _ at hm
  rw [growthF_of_mem hy] at hval
  rw [growthF_of_mem hy'] at hm
  have hUle : U (z.1 * f x.1 - y.1) ≤ U (z'.1 * f x.1 - y.1) :=
    h.U_mono.monotoneOn (mem_Ici.2 (sub_nonneg.2 hyz)) (mem_Ici.2 (sub_nonneg.2 (hyz.trans hzle)))
      (by linarith)
  refine ⟨by rw [hval]; linarith, fun hx => ?_⟩
  have hfx : 0 < f x.1 := by
    have := h.f_mono (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0) x.2.1 hx
    rwa [h.f_zero] at this
  have hzlt : z.1 * f x.1 < z'.1 * f x.1 := mul_lt_mul_of_pos_right hzz hfx
  have hUlt := h.U_mono (mem_Ici.2 (sub_nonneg.2 hyz)) (mem_Ici.2 (sub_nonneg.2 (hyz.trans hzle)))
    (by linarith : z.1 * f x.1 - y.1 < z'.1 * f x.1 - y.1)
  rw [hval]
  linarith

/-- **Exercise 10.1f.** With Markov shocks (Z3), parts (a)–(c) hold (`ex_10_1a`–`ex_10_1c` are
proved for any Feller `Q`), and so does the formula for `v_x` (`growth_hasDerivAt_x`). If `Q` is
monotone, `v(x, ·)` is nondecreasing, and strictly increasing when `x > 0` (at `x = 0` output
is `0` for every `z`). -/
theorem ex_10_1f (h : GrowthHyp U f β xbar zbar)
    (Q : Kernel (Icc (1 : ℝ) zbar) (Icc (1 : ℝ) zbar)) [IsMarkovKernel Q] (hQ : IsFeller Q)
    (hQm : IsMonotoneTF Q) {v : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ}
    (hv : bellman (growthModel Q U f β xbar) (growth_boundedDP h Q hQ) v = v) :
    (∀ x, Monotone fun z => v (x, z)) ∧
      ∀ x : Icc (0 : ℝ) xbar, 0 < x.1 → StrictMono fun z => v (x, z) := by
  set M := growthModel Q U f β xbar
  have hb := growth_boundedDP h Q hQ
  set C' : Set (Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar →ᵇ ℝ) :=
    {w | ∀ x, Monotone fun z => w (x, z)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar)
      (ι := {q : Icc (0 : ℝ) xbar × Icc (1 : ℝ) zbar × Icc (1 : ℝ) zbar // q.2.1 ≤ q.2.2})
      (fun q => (q.1.1, q.1.2.1)) (fun q => (q.1.1, q.1.2.2))
    convert this using 1
    ext w
    exact ⟨fun hw q => hw q.1.1 q.2, fun hw x z z' hzz' => hw ⟨(x, z, z'), hzz'⟩⟩
  have hmono : ∀ w ∈ C', ∀ x, Monotone fun z => bellman M hb w (x, z) :=
    fun w hw x z z' hzz' => by
      rcases hzz'.lt_or_eq with hlt | heq
      · exact (growth_bellman_mono_z h Q hQ hQm hw x hlt).1
      · rw [heq]
  have hv' := (corollary_1 (S' := C')
    (S'' := {w | ∀ x : Icc (0 : ℝ) xbar, 0 < x.1 → StrictMono fun z => w (x, z)})
    (bellman_contraction M hb) hv ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed hmono
    fun w hw x hx z z' hzz' => (growth_bellman_mono_z h Q hQ hQm hw x hzz').2 hx)
  exact ⟨hv'.1, hv'.2⟩

end StokeyLucasPrescott.StochasticApplications
