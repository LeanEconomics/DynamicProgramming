/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.SpectralGap
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Markov semigroups and the resolvent equations (MT §20.3.1–20.3.2, Theorem 20.3.1)

Meyn and Tweedie, pp. 524–526.

* `MarkovSemigroup X`: a minimal Markovian semigroup `{Pᵗ}` — a Markov kernel `K(t, x) = Pᵗ(x, ·)`,
  jointly measurable in `(t, x)`, with `P⁰ = I` and `P^{s+t} = PˢPᵗ` (`P_add`); `act`: `Pᵗg`;
  `act_add`: the semigroup property on bounded functions.
* `resolvent` (20.24): `U_α g = ∫₀^∞ e^{−αt}Pᵗg dt`, with `measurable_resolvent`,
  `abs_resolvent_le` (`|U_α g| ≤ M/α`) and `act_resolvent` (`PˢU_α g = e^{αs}∫_s^∞ e^{−αu}Pᵘg du`).
* `expLaw`, `resolventKernel`, `isMarkovKernel_resolventKernel`, `integral_resolventKernel`
  (p. 525): the sampled chain `Φ^α` has the Markov kernel `R_α = ∫ Pᵗ αe^{−αt} dt`, acting as
  `αU_α`.
* **Theorem 20.3.1 (i)** (`theorem_20_3_1_i`, (20.29)): `U_α = U_β + (β − α)U_βU_α
  = U_β + (β − α)U_αU_β` on bounded measurable functions (core: `resolvent_resolvent`).
* **Theorem 20.3.1 (ii)** (`theorem_20_3_1_ii`, (20.30)): `U_α g` is in the domain of the
  extended generator, `AU_α g = αU_α g − g`, in the semigroup form `IsExtGenerator`:
  `PᵀU_α g − U_α g = ∫₀ᵀ Pˢ(αU_α g − g) ds`.
* Real analysis used: `setIntegral_Ioi_comp_add`, `integral_triangle_swap` (Fubini on
  `{0 < s < u}`), `integral_Ioo_exp_mul`, `integrable_triangle`.

**Hypotheses and scope.** The book defines the extended generator through local martingales of
the process `Φ` (20.28). Mathlib has no construction of a continuous-time Markov process from a
semigroup (nor CADLAG path spaces), so `IsExtGenerator` is the semigroup (Dynkin) form: the mean
of `M_T` vanishes from every initial state, which with the Markov property is exactly the martingale
property of (20.28). The equations are proved for bounded measurable `g`, as in the book. The
non-explosion and CADLAG assumptions of §20.3.1 concern paths and are not needed here.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ### Real-analysis lemmas: Laplace transforms on `(0, ∞)` -/

/-- Translation on half-lines: `∫_{t > 0} f(s + t) dt = ∫_{u > s} f(u) du`. -/
theorem setIntegral_Ioi_comp_add (f : ℝ → ℝ) (s : ℝ) :
    ∫ t in Ioi 0, f (s + t) = ∫ u in Ioi s, f u := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) s).setIntegral_preimage_emb
    (measurableEmbedding_addLeft s) f (Ioi s)
  have hpre : (fun t => s + t) ⁻¹' Ioi s = Ioi 0 := by
    ext t; simp only [mem_preimage, mem_Ioi]; constructor <;> intro h <;> linarith
  rw [hpre] at h
  exact h

/-- **The triangle swap**: `∫_{s>0} a(s) ∫_{u>s} ψ(u) du ds = ∫_{u>0} (∫_{0<s<u} a(s) ds) ψ(u) du`,
given integrability of `(s, u) ↦ 1{s < u} a(s) ψ(u)` on `(0, ∞)²`. -/
theorem integral_triangle_swap {a ψ : ℝ → ℝ}
    (hint : Integrable (fun p : ℝ × ℝ => (Iio p.2).indicator a p.1 * ψ p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) :
    ∫ s in Ioi 0, a s * ∫ u in Ioi s, ψ u =
      ∫ u in Ioi 0, (∫ s in Ioo 0 u, a s) * ψ u := by
  have hL : ∀ s ∈ Ioi (0 : ℝ), a s * ∫ u in Ioi s, ψ u =
      ∫ u in Ioi 0, (Iio u).indicator a s * ψ u := fun s hs => by
    rw [← integral_const_mul]
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Ioi s
    · have hu0 : u ∈ Ioi (0 : ℝ) := lt_trans (mem_Ioi.1 hs) hu
      rw [indicator_of_mem hu, indicator_of_mem hu0, indicator_of_mem (mem_Iio.2 hu)]
    · rw [indicator_of_notMem hu]
      by_cases hu0 : u ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hu0, indicator_of_notMem (fun h => hu (mem_Iio.1 h)), zero_mul]
      · rw [indicator_of_notMem hu0]
  have hR : ∀ u ∈ Ioi (0 : ℝ), (∫ s in Ioo 0 u, a s) * ψ u =
      ∫ s in Ioi 0, (Iio u).indicator a s * ψ u := fun u hu => by
    rw [integral_mul_const, ← Ioi_inter_Iio, setIntegral_indicator measurableSet_Iio]
  rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_congr_fun measurableSet_Ioi hR]
  exact integral_integral_swap hint


/-- `∫_{0<s<u} e^{cs} ds = (e^{cu} − 1)/c` for `c ≠ 0`, `u ≥ 0`. -/
theorem integral_Ioo_exp_mul {c u : ℝ} (hc : c ≠ 0) (hu : 0 ≤ u) :
    ∫ s in Ioo 0 u, Real.exp (c * s) = (Real.exp (c * u) - 1) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu]
  have hd : ∀ s ∈ uIcc 0 u, HasDerivAt (fun s => Real.exp (c * s) / c) (Real.exp (c * s)) s :=
    fun s _ => by
      have := ((hasDerivAt_id s).const_mul c).exp.div_const c
      simp only [id_eq, mul_one] at this
      convert this using 1
      field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _),
    mul_zero, Real.exp_zero, sub_div]

/-- Bounded measurable functions are integrable for finite measures. -/
theorem integrable_of_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {g : X → ℝ} (hg : Measurable g) {M : ℝ} (hgb : ∀ x, |g x| ≤ M) : Integrable g μ :=
  (integrable_const M).mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x)

/-! ### Markov semigroups -/

/-- **A Markov semigroup** `{Pᵗ : t ≥ 0}` (MT §20.3.1, p. 524), given minimally: a Markov kernel
`K(t, x) = Pᵗ(x, ·)`, jointly measurable in `(t, x)`, with `P⁰ = I` and the semigroup property
`P^{s+t} = PˢPᵗ` for `s, t ≥ 0` (values at `t < 0` are irrelevant). -/
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- The transition kernel `(t, x) ↦ Pᵗ(x, ·)`. -/
  K : Kernel (ℝ × X) X
  /-- Each `Pᵗ(x, ·)` is a probability. -/
  isMarkovKernel : IsMarkovKernel K
  /-- `P⁰(x, ·) = δₓ`. -/
  zero_eq : ∀ x, K (0, x) = Measure.dirac x
  /-- `P^{s+t}(x, ·) = ∫ Pˢ(x, dy) Pᵗ(y, ·)`. -/
  add_eq : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x, K (s + t, x) = (K (s, x)).bind fun y => K (t, y)

variable {X : Type*} [MeasurableSpace X]

namespace MarkovSemigroup

/-- The kernel `Pᵗ`. -/
noncomputable def P (S : MarkovSemigroup X) (t : ℝ) : Kernel X X :=
  Kernel.comap S.K (fun x => (t, x)) (measurable_const.prodMk measurable_id)

/-- `Pᵗ(x, ·) = K(t, x)`. -/
theorem P_apply (S : MarkovSemigroup X) (t : ℝ) (x : X) : S.P t x = S.K (t, x) := rfl

/-- Each `Pᵗ` is a Markov kernel. -/
theorem isMarkovKernel_P (S : MarkovSemigroup X) (t : ℝ) : IsMarkovKernel (S.P t) :=
  ⟨fun x => by rw [P_apply]; exact S.isMarkovKernel.isProbabilityMeasure _⟩

/-- **The semigroup property** `P^{s+t} = PˢPᵗ` as kernels ("first `Pˢ`, then `Pᵗ`"). -/
theorem P_add (S : MarkovSemigroup X) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.P (s + t) = S.P t ∘ₖ S.P s := by
  ext x : 1
  rw [Kernel.comp_apply, P_apply, P_apply, S.add_eq s t hs ht x]
  rfl

/-- The action `Pᵗg(x) = ∫ g(y) Pᵗ(x, dy)` on bounded measurable functions. -/
noncomputable def act (S : MarkovSemigroup X) (t : ℝ) (g : X → ℝ) (x : X) : ℝ :=
  ∫ y, g y ∂S.K (t, x)

/-- `(t, x) ↦ Pᵗg(x)` is jointly measurable. -/
theorem measurable_act (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) :
    Measurable fun p : ℝ × X => S.act p.1 g p.2 :=
  (StronglyMeasurable.integral_kernel (κ := S.K) hg.stronglyMeasurable).measurable

/-- `|Pᵗg| ≤ M` when `|g| ≤ M`. -/
theorem abs_act_le (S : MarkovSemigroup X) {g : X → ℝ} {M : ℝ} (hgb : ∀ x, |g x| ≤ M)
    (t : ℝ) (x : X) : |S.act t g x| ≤ M := by
  have := S.isMarkovKernel
  rw [act, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_const M) (Eventually.of_forall fun y => ?_)).trans
    ?_
  · rw [Real.norm_eq_abs]; exact hgb y
  · rw [integral_const, probReal_univ, one_smul]

/-- **The semigroup property on functions**: `Pˢ(Pᵗg) = P^{s+t}g`. -/
theorem act_add (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    ∫ y, S.act t g y ∂S.K (s, x) = S.act (s + t) g x := by
  have := S.isMarkovKernel
  have := S.isMarkovKernel_P
  rw [act, show S.K (s + t, x) = S.P (s + t) x from rfl, S.P_add hs ht,
    Kernel.integral_comp (integrable_of_abs_le hg hgb)]
  rfl

/-- **The resolvent** (20.24), MT p. 525: `U_α g(x) = ∫₀^∞ e^{−αt} Pᵗg(x) dt`. -/
noncomputable def resolvent (S : MarkovSemigroup X) (α : ℝ) (g : X → ℝ) (x : X) : ℝ :=
  ∫ t in Ioi 0, Real.exp (-α * t) * S.act t g x

/-- `t ↦ e^{−αt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => Real.exp (-α * t)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith) 0

/-- `∫_{t > c} e^{−αt} dt = e^{−αc}/α`. -/
theorem integral_exp_neg_Ioi' {α : ℝ} (hα : 0 < α) (c : ℝ) :
    ∫ t in Ioi c, Real.exp (-α * t) = Real.exp (-α * c) / α := by
  rw [integral_exp_mul_Ioi (by linarith) c, div_neg, neg_div, neg_neg]

/-- The integrand of `U_α g(x)` is integrable on `(0, ∞)`. -/
theorem integrableOn_resolvent (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α : ℝ} (hα : 0 < α) (x : X) :
    IntegrableOn (fun t => Real.exp (-α * t) * S.act t g x) (Ioi 0) := by
  refine ((integrableOn_exp_neg hα).mul_const M).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      ((S.measurable_act hg).comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (S.abs_act_le hgb t x) (Real.exp_pos _).le

/-- `U_α g` is measurable. -/
theorem measurable_resolvent (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) (α : ℝ) :
    Measurable (S.resolvent α g) := by
  have hF : StronglyMeasurable (Function.uncurry fun (t : ℝ) (x : X) =>
      Real.exp (-α * t) * S.act t g x) :=
    ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)).mul
      (S.measurable_act hg)).stronglyMeasurable
  exact (hF.integral_prod_left (μ := volume.restrict (Ioi 0))).measurable

/-- `|U_α g| ≤ M/α`. -/
theorem abs_resolvent_le (S : MarkovSemigroup X) {g : X → ℝ} {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α : ℝ} (hα : 0 < α) (x : X) : |S.resolvent α g x| ≤ M / α := by
  rw [resolvent, ← Real.norm_eq_abs]
  calc ‖∫ t in Ioi 0, Real.exp (-α * t) * S.act t g x‖
      ≤ ∫ t in Ioi 0, Real.exp (-α * t) * M := by
        refine norm_integral_le_of_norm_le ((integrableOn_exp_neg hα).mul_const M)
          (Eventually.of_forall fun t => ?_)
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (S.abs_act_le hgb t x) (Real.exp_pos _).le
    _ = M / α := by
        rw [integral_mul_const, integral_exp_neg_Ioi' hα, mul_zero, Real.exp_zero]; ring

/-- **`PˢU_α g`** (MT p. 526): `∫ U_α g(y) Pˢ(x, dy) = e^{αs} ∫_{u > s} e^{−αu} Pᵘg(x) du`. -/
theorem act_resolvent (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α : ℝ} (hα : 0 < α) {s : ℝ} (hs : 0 ≤ s) (x : X) :
    ∫ y, S.resolvent α g y ∂S.K (s, x) =
      Real.exp (α * s) * ∫ u in Ioi s, Real.exp (-α * u) * S.act u g x := by
  have := S.isMarkovKernel
  have hmeas : Measurable fun p : X × ℝ => Real.exp (-α * p.2) * S.act p.2 g p.1 :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_snd)).mul
      ((S.measurable_act hg).comp (measurable_snd.prodMk measurable_fst))
  have hint : Integrable (Function.uncurry fun (y : X) (t : ℝ) =>
      Real.exp (-α * t) * S.act t g y) ((S.K (s, x)).prod (volume.restrict (Ioi 0))) := by
    refine ((integrable_const M).mul_prod (integrableOn_exp_neg hα)).mono'
      hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    change ‖Real.exp (-α * p.2) * S.act p.2 g p.1‖ ≤ M * Real.exp (-α * p.2)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (S.abs_act_le hgb _ _) (Real.exp_pos _).le
  rw [show (fun y => S.resolvent α g y) = fun y => ∫ t in Ioi 0, Real.exp (-α * t) * S.act t g y
    from rfl, integral_integral_swap hint]
  have h1 : ∀ t ∈ Ioi (0 : ℝ), ∫ y, Real.exp (-α * t) * S.act t g y ∂S.K (s, x) =
      Real.exp (α * s) * (Real.exp (-α * (s + t)) * S.act (s + t) g x) := fun t ht => by
    rw [integral_const_mul, S.act_add hg hgb hs (le_of_lt ht), ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    setIntegral_Ioi_comp_add (fun u => Real.exp (-α * u) * S.act u g x) s]

/-- The triangle integrand of the resolvent equation is integrable on `(0, ∞)²`. -/
theorem integrable_triangle (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α : ℝ} (hα : 0 < α) {a : ℝ → ℝ} (ha : Measurable a)
    {B : ℝ → ℝ} (hB : IntegrableOn B (Ioi 0))
    (hbound : ∀ s, 0 < s → |a s| * Real.exp (-α * s) / α ≤ B s) (x : X) :
    Integrable (fun p : ℝ × ℝ => (Iio p.2).indicator a p.1 *
      (Real.exp (-α * p.2) * S.act p.2 g x))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgb x)
  have hind : Measurable fun p : ℝ × ℝ => (Iio p.2).indicator a p.1 := by
    have : (fun p : ℝ × ℝ => (Iio p.2).indicator a p.1) =
        fun p => if p.1 < p.2 then a p.1 else 0 := by
      funext p; rw [indicator_apply]; rfl
    rw [this]
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (ha.comp measurable_fst)
      measurable_const
  have hψ : Measurable fun u : ℝ => Real.exp (-α * u) * S.act u g x :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      ((S.measurable_act hg).comp (measurable_id.prodMk measurable_const))
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (Iio p.2).indicator a p.1 *
      (Real.exp (-α * p.2) * S.act p.2 g x))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    (hind.mul (hψ.comp measurable_snd)).aestronglyMeasurable
  have hsec : ∀ s : ℝ, ∀ u, ‖(Iio u).indicator a s * (Real.exp (-α * u) * S.act u g x)‖ ≤
      (Ioi s).indicator (fun u => M * |a s| * Real.exp (-α * u)) u := fun s u => by
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    by_cases hu : s < u
    · rw [indicator_of_mem (mem_Iio.2 hu), indicator_of_mem (mem_Ioi.2 hu)]
      have h1 := mul_le_mul_of_nonneg_left (S.abs_act_le hgb u x)
        (mul_nonneg (abs_nonneg (a s)) (Real.exp_pos (-α * u)).le)
      linarith
    · rw [indicator_of_notMem (fun h => hu (mem_Iio.1 h)), abs_zero, zero_mul,
        indicator_of_notMem (fun h => hu (mem_Ioi.1 h))]
  have hIs : ∀ s : ℝ, Integrable ((Ioi s).indicator fun u => M * |a s| * Real.exp (-α * u))
      (volume.restrict (Ioi 0)) := fun s =>
    (IntegrableOn.integrable_indicator (((integrableOn_exp_mul_Ioi (by linarith : -α < 0)
      s).const_mul (M * |a s|) : IntegrableOn (fun u => M * |a s| * Real.exp (-α * u))
      (Ioi s) volume)) measurableSet_Ioi).restrict
  rw [integrable_prod_iff hm]
  refine ⟨hm.prodMk_left.mono fun s hs => Integrable.mono' (hIs s) hs
    (Eventually.of_forall fun u => hsec s u), ?_⟩
  · refine Integrable.mono' (g := fun s => M * B s) (hB.const_mul M)
      hm.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ u, ‖(Iio u).indicator a s * (Real.exp (-α * u) * S.act u g x)‖ ∂volume.restrict (Ioi 0)
        ≤ ∫ u, (Ioi s).indicator (fun u => M * |a s| * Real.exp (-α * u)) u
            ∂volume.restrict (Ioi 0) := by
          exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hIs s)
            (Eventually.of_forall fun u => hsec s u)
      _ = M * (|a s| * Real.exp (-α * s) / α) := by
          rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
            Ioi_inter_Ioi, sup_eq_left.2 (le_of_lt (mem_Ioi.1 hs)), integral_const_mul,
            integral_exp_neg_Ioi' hα]
          ring
      _ ≤ M * B s := mul_le_mul_of_nonneg_left (hbound s hs) hM

/-- The core of the resolvent equation: `(α − β) U_β U_α g = U_β g − U_α g`. -/
theorem resolvent_resolvent (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : X) :
    (α - β) * S.resolvent β (S.resolvent α g) x = S.resolvent β g x - S.resolvent α g x := by
  rcases eq_or_ne α β with rfl | hne
  · rw [sub_self, zero_mul, sub_self]
  have hab : α - β ≠ 0 := sub_ne_zero.2 hne
  set ψ : ℝ → ℝ := fun u => Real.exp (-α * u) * S.act u g x with hψ
  -- `U_β U_α g(x) = ∫_{s>0} e^{(α−β)s} ∫_{u>s} ψ(u) du ds`
  have h1 : S.resolvent β (S.resolvent α g) x =
      ∫ s in Ioi 0, Real.exp ((α - β) * s) * ∫ u in Ioi s, ψ u := by
    rw [resolvent]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [act, S.act_resolvent hg hgb hα (le_of_lt hs) x, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  -- the triangle swap
  have hint := S.integrable_triangle hg hgb hα
    (a := fun s => Real.exp ((α - β) * s))
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
    (B := fun s => Real.exp (-β * s) / α) ((integrableOn_exp_neg hβ).div_const α)
    (fun s _ => by
      rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      exact le_of_eq (by congr 2; ring)) x
  have h2 := integral_triangle_swap (a := fun s => Real.exp ((α - β) * s)) (ψ := ψ) hint
  rw [h1, h2]
  have h3 : ∀ u ∈ Ioi (0 : ℝ), (∫ s in Ioo 0 u, Real.exp ((α - β) * s)) * ψ u =
      (Real.exp (-β * u) * S.act u g x - Real.exp (-α * u) * S.act u g x) / (α - β) :=
    fun u hu => by
      rw [integral_Ioo_exp_mul hab (le_of_lt hu), hψ]
      field_simp
      rw [sub_mul, ← Real.exp_add]
      ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi h3, integral_div,
    integral_sub (S.integrableOn_resolvent hg hgb hβ x) (S.integrableOn_resolvent hg hgb hα x)]
  rw [mul_div_cancel₀ _ hab]
  rfl

/-- **Theorem 20.3.1 (i), the resolvent equations** (20.29), MT p. 526: for `α, β > 0` and
bounded measurable `g`, `U_α g = U_β g + (β − α)U_βU_α g = U_β g + (β − α)U_αU_β g`. -/
theorem theorem_20_3_1_i (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : X) :
    S.resolvent α g x = S.resolvent β g x + (β - α) * S.resolvent β (S.resolvent α g) x ∧
      S.resolvent α g x = S.resolvent β g x + (β - α) * S.resolvent α (S.resolvent β g) x := by
  have h1 := S.resolvent_resolvent hg hgb hα hβ x
  have h2 := S.resolvent_resolvent hg hgb hβ hα x
  constructor <;> linarith

/-- **The extended generator in semigroup form** (MT p. 526): `Ah = k` when
`Pᵀh(x) − h(x) = ∫₀ᵀ Pˢk(x) ds` for all `T ≥ 0` and `x`, i.e. the process (20.28)
`M_T = h(Φ_T) − h(Φ_0) − ∫₀ᵀ k(Φ_s) ds` has `E_x[M_T] = 0` for every initial state (with the
Markov property, this is the martingale property of `M`). -/
def IsExtGenerator (S : MarkovSemigroup X) (h k : X → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ x, S.act T h x - h x = ∫ s in Ioc 0 T, S.act s k x

/-- Bounded measurable functions are integrable on bounded intervals. -/
theorem integrableOn_Ioc_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ u, |f u| ≤ M) (a b : ℝ) : IntegrableOn f (Ioc a b) :=
  (integrableOn_const (C := M) measure_Ioc_lt_top.ne).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hb u)

/-- **Theorem 20.3.1 (ii)** (20.30), MT p. 526: for `α > 0` and bounded measurable `g`, `U_α g`
is in the domain of the extended generator, with `AU_α g = αU_α g − g`. -/
theorem theorem_20_3_1_ii (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) {α : ℝ} (hα : 0 < α) :
    S.IsExtGenerator (S.resolvent α g) (fun y => α * S.resolvent α g y - g y) := by
  have := S.isMarkovKernel
  intro T hT x
  set φ : ℝ → ℝ := fun u => S.act u g x with hφ
  set ψ : ℝ → ℝ := fun u => Real.exp (-α * u) * φ u with hψ
  have hφm : Measurable φ := (S.measurable_act hg).comp (measurable_id.prodMk measurable_const)
  have hψi : IntegrableOn ψ (Ioi 0) := S.integrableOn_resolvent hg hgb hα x
  have hhm := S.measurable_resolvent hg α
  have hhb := S.abs_resolvent_le hgb hα
  -- (A), (B)
  have hA : S.act T (S.resolvent α g) x = Real.exp (α * T) * ∫ u in Ioi T, ψ u :=
    S.act_resolvent hg hgb hα hT x
  have hB : S.resolvent α g x = ∫ u in Ioi 0, ψ u := rfl
  have hactm : Measurable fun s => S.act s (S.resolvent α g) x :=
    (S.measurable_act hhm).comp (measurable_id.prodMk measurable_const)
  have hbd : ∀ u, |α * S.act u (S.resolvent α g) x| ≤ |α| * (M / α) := fun u => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (S.abs_act_le hhb u x) (abs_nonneg α)
  have hI1 : IntegrableOn (fun s => α * S.act s (S.resolvent α g) x) (Ioc 0 T) :=
    integrableOn_Ioc_of_abs_le (hactm.const_mul α) hbd 0 T
  have hI2 : IntegrableOn φ (Ioc 0 T) :=
    integrableOn_Ioc_of_abs_le hφm (fun u => S.abs_act_le hgb u x) 0 T
  have hC' : ∀ s ∈ Ioc (0 : ℝ) T, S.act s (fun y => α * S.resolvent α g y - g y) x =
      α * S.act s (S.resolvent α g) x - φ s := fun s hs => by
    rw [act, integral_sub ((integrable_of_abs_le hhm hhb).const_mul α)
      (integrable_of_abs_le hg hgb), integral_const_mul]
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioc hC', integral_sub hI1 hI2]
  -- (E): the first integral as a triangle integral
  set a : ℝ → ℝ := (Iic T).indicator (fun s => α * Real.exp (α * s)) with ha
  have hE : ∫ s in Ioc 0 T, α * S.act s (S.resolvent α g) x =
      ∫ s in Ioi 0, a s * ∫ u in Ioi s, ψ u := by
    rw [← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    by_cases hsT : s ∈ Iic T
    · rw [indicator_of_mem hsT, ha, indicator_of_mem hsT, act,
        S.act_resolvent hg hgb hα (le_of_lt hs) x]
      ring
    · rw [indicator_of_notMem hsT, ha, indicator_of_notMem hsT, zero_mul]
  have ham : Measurable a := (measurable_const.mul (Real.continuous_exp.measurable.comp
    (measurable_const.mul measurable_id))).indicator measurableSet_Iic
  have hfin : (volume.restrict (Ioi (0 : ℝ))) (Iic T) ≠ ∞ := by
    rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi]; exact measure_Ioc_lt_top.ne
  have hBi : Integrable ((Iic T).indicator fun _ => (1 : ℝ)) (volume.restrict (Ioi 0)) :=
    (integrableOn_const hfin).integrable_indicator measurableSet_Iic
  have hint := S.integrable_triangle hg hgb hα ham (B := (Iic T).indicator fun _ => 1) hBi
    (fun s _ => by
      by_cases hsT : s ∈ Iic T
      · rw [ha, indicator_of_mem hsT, indicator_of_mem hsT, abs_of_pos (by positivity),
          mul_assoc, ← Real.exp_add, show α * s + -α * s = 0 by ring, Real.exp_zero, mul_one,
          div_self hα.ne']
      · rw [ha, indicator_of_notMem hsT, indicator_of_notMem hsT, abs_zero, zero_mul,
          zero_div]) x
  rw [hE, integral_triangle_swap (a := a) (ψ := ψ) hint, hA, hB]
  have hIoc : IntegrableOn ψ (Ioc 0 T) := hψi.mono_set Ioc_subset_Ioi_self
  have hIoiT : IntegrableOn ψ (Ioi T) := hψi.mono_set (Ioi_subset_Ioi hT)
  have hsplit : ∀ f : ℝ → ℝ, IntegrableOn f (Ioc 0 T) → IntegrableOn f (Ioi T) →
      ∫ u in Ioi 0, f u = (∫ u in Ioc 0 T, f u) + ∫ u in Ioi T, f u := fun f h1 h2 => by
    rw [← Ioc_union_Ioi_eq_Ioi hT, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      h1 h2]
  -- the inner integrals
  have hc1 : ∀ u ∈ Ioc (0 : ℝ) T, (∫ s in Ioo 0 u, a s) * ψ u = φ u - ψ u := fun u hu => by
    have : ∫ s in Ioo 0 u, a s = ∫ s in Ioo 0 u, α * Real.exp (α * s) :=
      setIntegral_congr_fun measurableSet_Ioo fun s hs => by
        rw [ha, indicator_of_mem (mem_Iic.2 (le_trans (le_of_lt hs.2) hu.2))]
    have h2 : α * ((Real.exp (α * u) - 1) / α) = Real.exp (α * u) - 1 := by field_simp
    rw [this, integral_const_mul, integral_Ioo_exp_mul hα.ne' (le_of_lt hu.1), h2, hψ]
    change (Real.exp (α * u) - 1) * (Real.exp (-α * u) * φ u) = φ u - Real.exp (-α * u) * φ u
    rw [sub_mul, one_mul, ← mul_assoc, ← Real.exp_add, show α * u + -α * u = 0 by ring,
      Real.exp_zero, one_mul]
  have hc2 : ∀ u ∈ Ioi T, (∫ s in Ioo 0 u, a s) * ψ u = (Real.exp (α * T) - 1) * ψ u :=
    fun u hu => by
      have : ∫ s in Ioo 0 u, a s = ∫ s in Ioo 0 T, α * Real.exp (α * s) := by
        rw [ha, setIntegral_indicator measurableSet_Iic,
          show Ioo 0 u ∩ Iic T = Ioc 0 T by
            ext s; simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
            constructor
            · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
            · rintro ⟨h1, h3⟩; exact ⟨⟨h1, lt_of_le_of_lt h3 (mem_Ioi.1 hu)⟩, h3⟩,
          integral_Ioc_eq_integral_Ioo]
      rw [this, integral_const_mul, integral_Ioo_exp_mul hα.ne' hT]
      field_simp
  have hcI1 : IntegrableOn (fun u => (∫ s in Ioo 0 u, a s) * ψ u) (Ioc 0 T) :=
    (hI2.sub hIoc).congr_fun (fun u hu => (hc1 u hu).symm) measurableSet_Ioc
  have hcI2 : IntegrableOn (fun u => (∫ s in Ioo 0 u, a s) * ψ u) (Ioi T) :=
    IntegrableOn.congr_fun (hIoiT.const_mul (Real.exp (α * T) - 1) :
      IntegrableOn (fun u => (Real.exp (α * T) - 1) * ψ u) (Ioi T) volume)
      (fun u hu => (hc2 u hu).symm) measurableSet_Ioi
  rw [hsplit _ hcI1 hcI2, hsplit ψ hIoc hIoiT, setIntegral_congr_fun measurableSet_Ioc hc1,
    setIntegral_congr_fun measurableSet_Ioi hc2, integral_sub hI2 hIoc, integral_const_mul]
  ring

/-- The exponential law of rate `α` on `(0, ∞)`, density `αe^{−αt}`: the law of the sampling
intervals `α⁻¹A_k` of a Poisson process of rate `α` (MT p. 525). -/
noncomputable def expLaw (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ((α * Real.exp (-α * t)).toNNReal : ℝ≥0∞)

/-- The exponential law is a probability. -/
theorem isProbabilityMeasure_expLaw {α : ℝ} (hα : 0 < α) : IsProbabilityMeasure (expLaw α) := by
  constructor
  rw [expLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_neg hα).const_mul α)
    (Eventually.of_forall fun t => (mul_pos hα (Real.exp_pos (-α * t))).le)
  simp_rw [ENNReal.ofReal] at h
  rw [← h, integral_const_mul, integral_exp_neg_Ioi' hα, mul_zero, Real.exp_zero,
    mul_one_div_cancel hα.ne', Real.toNNReal_one, ENNReal.coe_one]

/-- **The transition kernel of the sampled chain** `Φ^α` (MT p. 525): `R_α(x, ·) = ∫ Pᵗ(x, ·)
αe^{−αt} dt`, a Markov kernel. -/
noncomputable def resolventKernel (S : MarkovSemigroup X) (α : ℝ) : Kernel X X :=
  S.K ∘ₖ (Kernel.const X (expLaw α) ×ₖ Kernel.id)

/-- `R_α` is a Markov kernel. -/
theorem isMarkovKernel_resolventKernel (S : MarkovSemigroup X) {α : ℝ} (hα : 0 < α) :
    IsMarkovKernel (S.resolventKernel α) := by
  have := S.isMarkovKernel
  have := isProbabilityMeasure_expLaw hα
  rw [resolventKernel]
  infer_instance

/-- **The sampled chain has kernel `αU_α`** (MT p. 525): `∫ g dR_α(x, ·) = αU_α g(x)`. -/
theorem integral_resolventKernel (S : MarkovSemigroup X) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ} (hgb : ∀ x, |g x| ≤ M) {α : ℝ} (hα : 0 < α) (x : X) :
    ∫ y, g y ∂S.resolventKernel α x = α * S.resolvent α g x := by
  have := S.isMarkovKernel
  have := isMarkovKernel_resolventKernel S hα
  have := isProbabilityMeasure_expLaw hα
  rw [resolventKernel, Kernel.integral_comp (by
      rw [← resolventKernel]; exact integrable_of_abs_le hg hgb),
    Kernel.prod_apply, Kernel.const_apply, Kernel.id_apply, Measure.prod_dirac,
    integral_map (φ := fun t : ℝ => (t, x)) (measurable_id.prodMk measurable_const).aemeasurable
      (f := fun p : ℝ × X => ∫ y, g y ∂S.K p)
      (StronglyMeasurable.integral_kernel (κ := S.K) hg.stronglyMeasurable).aestronglyMeasurable,
    expLaw, integral_withDensity_eq_integral_smul (by fun_prop), resolvent,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (mul_pos hα (Real.exp_pos _)).le]
  rw [mul_assoc]
  rfl

end MarkovSemigroup

end MeynTweedie.Epilogue
