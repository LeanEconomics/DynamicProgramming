/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.SIBounded
import IncompleteMarkets.SIWCRealIntervals

/-!
# §8.3.2, Case 1: Proposition 8.3.1 (a unique stable stationary distribution)

Copied from `EconomicDynamics/Applications` (module `SIStationary`), namespace renamed.

Miao, §8.3.2, pp. 254–256. Let `βR < 1`, `y_min < y_max`, the relative risk aversion be below
`γ` for large `c`, and income be iid with `μ([a, b]) ≥ α(b − a)` on `[y_min, y_max]` (`α > 0`).

* `kernel xf`: the transition function `P` of `x_{t+1} = Râ(x_t) + y_{t+1} − rb` on
  `[x_min, x_f]` (`P(x, A) = μ{y : Râ(x) + y − rb ∈ A}` for `A ⊆ [x_min, x_f]`, `kernel_apply`);
  on `[x_min, x_max]` the clamp in its definition is never active (`mapsTo_Icc`).
* `isMonotoneTF_kernel`, `isFeller_kernel`: `P` is monotone and Feller ("we can easily verify",
  p. 255), from Lemma 8.3.1 (`â` nondecreasing and continuous).
* `phi`: `φₙ(x, y)` (p. 255), the cash on hand after `n` periods of constant income `y`;
  `phi_mono` (increasing in `x` and `y`), `phi_mem`, `continuousOn_phi`.
* `kpow_ge`: **the displayed bounds of p. 255**,
  `Pⁿ(x, [φₙ(x, a), φₙ(x, b)]) ≥ μ([a, b])ⁿ ≥ αⁿ(b − a)ⁿ` for `[a, b] ⊆ [y_min, y_max]`,
  in particular `[a, b] = [y_max − δ, y_max]` and `[y_min, y_min + δ]` (`kpow_ge_real`).
* `next_low_lt`, `phi_low_tendsto`: with income `y_min` forever, cash on hand falls strictly and
  `φₙ(x_f, y_min) ↓ x_min`. This is what the book's "a similar argument applies to `x₀ = x_max`"
  needs; it is proved from the Euler equation (`βR < 1`).
* `mixing`: the mixing condition (Assumption 12.1 of SLP, Miao's Theorems 3.3.5–3.3.6) at
  `x̄ = x_min + (y_max − y_min)/2`.
* **Proposition 8.3.1** (`proposition_8_3_1`): `P` on `[x_min, x_max]` has a unique invariant
  probability measure `λ*`, and `T*ⁿλ₀ ⇒ λ*` for every initial distribution `λ₀` (SLP Theorem
  12.12, `SIWC.theorem_12_12_real`).

**Departures.** (1) The book takes `x̄ = lim φₙ(x_min, Ey)`; any `x̄` strictly between
`x_min = lim φₙ(x_max, y_min)` and `φ₁(x_min, y_max − δ) ≥ y_max − δ − rb` works, and we take
the midpoint, which avoids the limit `ξ` and the comparison `ξ > x̄`. (2) The book says
`φₙ(x_min, y_max)` is strictly increasing; it is only nondecreasing (`phi_high_monotone`): if
`y_max − rb ≤ x̂` (Lemma 8.3.2) then `φ₂ = φ₁` (`phi_two_eq_one`). (3) The continuity of the
stationary distribution in `(R, b)` is not formalised: it needs the policy `â` to be jointly
continuous in `(x, R, b)`, which the book's assumption (a solution `V` for each parameter) does
not provide, and the state space `[x_min, x_max]` itself moves with `(R, b)`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- The clamp of `Râ(x) + y − rb` to `[x_min, x_f]`. -/
noncomputable def kmap (xf : ℝ) (p : Set.Icc M.xmin xf × ℝ) : Set.Icc M.xmin xf :=
  ⟨max M.xmin (min xf (M.next (S.sav p.1) p.2)),
    ⟨le_max_left _ _, max_le (p.1.2.1.trans p.1.2.2) (min_le_left _ _)⟩⟩

theorem continuous_kmap (xf : ℝ) : Continuous (S.kmap xf) := by
  have hs : Continuous fun x : Set.Icc M.xmin xf => S.sav x :=
    S.continuousOn_sav.comp_continuous continuous_subtype_val fun x => Set.mem_Ici.2 x.2.1
  refine Continuous.subtype_mk ?_ _
  refine continuous_const.max (continuous_const.min ?_)
  simp only [SIModel.next]
  exact ((continuous_const.mul (hs.comp continuous_fst)).add continuous_snd).sub continuous_const

theorem continuous_kmap_y (xf : ℝ) (x : Set.Icc M.xmin xf) :
    Continuous fun y => S.kmap xf (x, y) :=
  (S.continuous_kmap xf).comp (Continuous.prodMk_right x)

/-- The **transition function** `P(x, ·)` of `x_{t+1} = Râ(x_t) + y_{t+1} − rb` on
`[x_min, x_f]` (Miao, p. 255). -/
noncomputable def kernel (xf : ℝ) : Kernel (Set.Icc M.xmin xf) (Set.Icc M.xmin xf) where
  toFun x := M.law.map fun y => S.kmap xf (x, y)
  measurable' := Measure.measurable_of_measurable_coe _ fun A hA => by
    have : ∀ x, (M.law.map fun y => S.kmap xf (x, y)) A =
        M.law (Prod.mk x ⁻¹' (S.kmap xf ⁻¹' A)) := fun x =>
      Measure.map_apply (S.continuous_kmap_y xf x).measurable hA
    simp_rw [this]
    exact measurable_measure_prodMk_left ((S.continuous_kmap xf).measurable hA)

theorem kernel_eq (xf : ℝ) (x : Set.Icc M.xmin xf) :
    S.kernel xf x = M.law.map fun y => S.kmap xf (x, y) := rfl

/-- `P(x, A) = μ{y : clamp(Râ(x) + y − rb) ∈ A}`. -/
theorem kernel_apply (xf : ℝ) (x : Set.Icc M.xmin xf) {A : Set (Set.Icc M.xmin xf)}
    (hA : MeasurableSet A) : S.kernel xf x A = M.law {y | S.kmap xf (x, y) ∈ A} :=
  Measure.map_apply (S.continuous_kmap_y xf x).measurable hA

theorem isMarkovKernel_kernel (xf : ℝ) : IsMarkovKernel (S.kernel xf) where
  isProbabilityMeasure x := by
    rw [kernel_eq]
    infer_instance

/-- `(Tf)(x) = ∫ f(clamp(Râ(x) + y − rb)) μ(dy)`. -/
theorem markovOpR_kernel (xf : ℝ) {f : Set.Icc M.xmin xf → ℝ} (hf : Measurable f)
    (x : Set.Icc M.xmin xf) :
    SIWC.markovOpR (S.kernel xf) f x = ∫ y, f (S.kmap xf (x, y)) ∂M.law := by
  rw [SIWC.markovOpR, kernel_eq, integral_map (S.continuous_kmap_y xf x).measurable.aemeasurable
    hf.aestronglyMeasurable]

theorem kmap_mono (xf : ℝ) {x x' : Set.Icc M.xmin xf} (hxx : x ≤ x') (y : ℝ) :
    S.kmap xf (x, y) ≤ S.kmap xf (x', y) := by
  have h1 := S.sav_mono (Set.mem_Ici.2 x.2.1) (Set.mem_Ici.2 x'.2.1) hxx
  have h2 : M.next (S.sav x) y ≤ M.next (S.sav x') y := by
    simp only [SIModel.next]; nlinarith [M.R_pos]
  change max M.xmin (min xf (M.next (S.sav x) y)) ≤ max M.xmin (min xf (M.next (S.sav x') y))
  exact max_le_max le_rfl (min_le_min le_rfl h2)

/-- `P` is **monotone** (Miao, p. 255). -/
theorem isMonotoneTF_kernel (xf : ℝ) : SIWC.IsMonotoneTF (S.kernel xf) := by
  intro f hf ⟨C, hC⟩ hmono x x' hxx
  rw [S.markovOpR_kernel xf hf, S.markovOpR_kernel xf hf]
  refine integral_mono ?_ ?_ fun y => hmono (S.kmap_mono xf hxx y)
  · exact Integrable.of_bound (hf.comp (S.continuous_kmap_y xf x).measurable).aestronglyMeasurable
      C (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC _)
  · exact Integrable.of_bound (hf.comp (S.continuous_kmap_y xf x').measurable).aestronglyMeasurable
      C (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC _)

/-- `P` has the **Feller property** (Miao, p. 255). -/
theorem isFeller_kernel (xf : ℝ) : SIWC.IsFeller (S.kernel xf) := by
  intro f hf ⟨C, hC⟩
  have heq : SIWC.markovOpR (S.kernel xf) f = fun x => ∫ y, f (S.kmap xf (x, y)) ∂M.law :=
    funext (S.markovOpR_kernel xf hf.measurable)
  rw [heq]
  have hc := hf.comp (S.continuous_kmap xf)
  exact continuous_of_dominated (bound := fun _ => C)
    (fun x => (hc.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun _ => Eventually.of_forall fun _ => by rw [Real.norm_eq_abs]; exact hC _)
    (integrable_const _) (Eventually.of_forall fun y => hc.comp (Continuous.prodMk_left y))

/-! ### The paths `φₙ(x, y)` -/

/-- `φₙ(x, y)` (Miao, p. 255): cash on hand at the start of period `n` from `x` when income is
`y` every period and `â` is followed: `φ₀ = x`, `φₙ₊₁ = Râ(φₙ) + y − rb`. -/
noncomputable def phi (y x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => M.next (S.sav (phi y x n)) y

theorem phi_zero (y x : ℝ) : S.phi y x 0 = x := rfl

theorem phi_succ (y x : ℝ) (n : ℕ) : S.phi y x (n + 1) = M.next (S.sav (S.phi y x n)) y := rfl

theorem phi_ge {y x : ℝ} (hy : M.ymin ≤ y) (hx : M.xmin ≤ x) (n : ℕ) : M.xmin ≤ S.phi y x n := by
  induction n with
  | zero => exact hx
  | succ n ih => exact M.next_ge (S.sav_mem _ ih).1 hy

/-- `φₙ(x, y) ≥ y − rb` for `n ≥ 1`. -/
theorem phi_succ_ge {y x : ℝ} (hy : M.ymin ≤ y) (hx : M.xmin ≤ x) (n : ℕ) :
    y - M.r * M.b ≤ S.phi y x (n + 1) := by
  have := mul_nonneg M.R_pos.le (S.sav_mem _ (S.phi_ge hy hx n)).1
  rw [phi_succ]; simp only [SIModel.next]; linarith

/-- `φₙ(x, y)` is nondecreasing in `x` and in `y` (Miao, p. 255). -/
theorem phi_mono {y y' x x' : ℝ} (hy : M.ymin ≤ y) (hx : M.xmin ≤ x) (hyy : y ≤ y')
    (hxx : x ≤ x') (n : ℕ) : S.phi y x n ≤ S.phi y' x' n := by
  induction n with
  | zero => exact hxx
  | succ n ih =>
    have h1 := S.sav_mono (Set.mem_Ici.2 (S.phi_ge hy hx n))
      (Set.mem_Ici.2 ((S.phi_ge hy hx n).trans ih)) ih
    rw [phi_succ, phi_succ]; simp only [SIModel.next]; nlinarith [M.R_pos]

/-- `φₙ(x, y) ∈ [x_min, x_f]` for `x ∈ [x_min, x_f]`, `y ∈ [y_min, y_max]`, when `x_f ≥ x_min`
is a fixed point of `x ↦ Râ(x) + y_max − rb`. -/
theorem phi_mem {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf) {x y : ℝ}
    (hx : x ∈ Set.Icc M.xmin xf) (hy : y ∈ Set.Icc M.ymin M.ymax) (n : ℕ) :
    S.phi y x n ∈ Set.Icc M.xmin xf := by
  induction n with
  | zero => exact hx
  | succ n ih => exact S.mapsTo_Icc hxf hfix ih hy

/-- `y ↦ φₙ(x, y)` is continuous on `[y_min, ∞)`. -/
theorem continuousOn_phi {x : ℝ} (hx : M.xmin ≤ x) (n : ℕ) :
    ContinuousOn (fun y => S.phi y x n) (Set.Ici M.ymin) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have h1 : ContinuousOn (fun y => S.sav (S.phi y x n)) (Set.Ici M.ymin) :=
      S.continuousOn_sav.comp ih fun y hy => Set.mem_Ici.2 (S.phi_ge hy hx n)
    simp only [phi_succ, SIModel.next]
    exact ((continuousOn_const.mul h1).add continuousOn_id).sub continuousOn_const

/-- The book's claim that `φₙ(x_min, y_max)` increases: it is nondecreasing. -/
theorem phi_high_monotone : Monotone (S.phi M.ymax M.xmin) := by
  have hy : M.ymin ≤ M.ymax := M.ymin_le_ymax
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero =>
    have := M.next_ge (S.sav_mem M.xmin le_rfl).1 hy
    exact this
  | succ n ih =>
    rw [phi_succ, phi_succ (n := n + 1)]
    have h1 := S.sav_mono (Set.mem_Ici.2 (S.phi_ge hy le_rfl n))
      (Set.mem_Ici.2 (S.phi_ge hy le_rfl (n + 1))) ih
    simp only [SIModel.next]; nlinarith [M.R_pos]

/-- **"Strictly increasing" is false in general** (p. 256): if the borrowing constraint binds
at `φ₁(x_min, y_max) = y_max − rb + Râ(x_min)` and at `x_min`, then `φ₂ = φ₁`. -/
theorem phi_two_eq_one (h0 : S.sav M.xmin = 0) (h1 : S.sav (S.phi M.ymax M.xmin 1) = 0) :
    S.phi M.ymax M.xmin 2 = S.phi M.ymax M.xmin 1 := by
  rw [phi_succ, h1, phi_succ, phi_zero, h0]

/-! ### Lower bounds on `Pⁿ` (Miao, p. 255) -/

/-- If `P(x₀, B₀) ≥ p` and `P(z, Bₙ₊₁) ≥ p` for all `z ∈ Bₙ`, then `Pⁿ⁺¹(x₀, Bₙ) ≥ pⁿ⁺¹`
(adapted from `RecursiveMethods/ConvergenceApplications`, `kpow_succ_ge_pow`). -/
theorem si_kpow_succ_ge_pow {X : Type*} [MeasurableSpace X] (κ : Kernel X X) {B : ℕ → Set X}
    (hB : ∀ n, MeasurableSet (B n)) {p : ℝ≥0∞} {x₀ : X} (h0 : p ≤ κ x₀ (B 0))
    (hstep : ∀ n, ∀ z ∈ B n, p ≤ κ z (B (n + 1))) (n : ℕ) :
    p ^ (n + 1) ≤ SIWC.kpow κ (n + 1) x₀ (B n) := by
  induction n with
  | zero => simpa [SIWC.kpow_one] using h0
  | succ n ih =>
    rw [SIWC.kpow_add κ (n + 1) 1, SIWC.kpow_one, Kernel.comp_apply' _ _ _ (hB (n + 1))]
    calc p ^ (n + 1 + 1) = p * p ^ (n + 1) := pow_succ' _ _
      _ ≤ p * SIWC.kpow κ (n + 1) x₀ (B n) := by gcongr
      _ = ∫⁻ z, (B n).indicator (fun _ => p) z ∂(SIWC.kpow κ (n + 1) x₀) :=
          (lintegral_indicator_const (hB n) p).symm
      _ ≤ ∫⁻ z, κ z (B (n + 1)) ∂(SIWC.kpow κ (n + 1) x₀) := lintegral_mono fun z => by
          by_cases hz : z ∈ B n
          · rw [Set.indicator_of_mem hz]; exact hstep n z hz
          · rw [Set.indicator_of_notMem hz]; exact zero_le

/-- The clamp keeps a value between two bounds in `[x_min, x_f]`. -/
theorem si_clamp_mem {lo xf L U w : ℝ} (hL : L ≤ xf) (hU : lo ≤ U) (hw : w ∈ Set.Icc L U) :
    L ≤ max lo (min xf w) ∧ max lo (min xf w) ≤ U :=
  ⟨le_max_of_le_right (le_min hL hw.1), max_le hU ((min_le_right _ _).trans hw.2)⟩

/-- **The bounds of p. 255**: for `x₀ ∈ [x_min, x_f]` and `[a, b] ⊆ [y_min, y_max]`,
`Pⁿ⁺¹(x₀, [φₙ₊₁(x₀, a), φₙ₊₁(x₀, b)]) ≥ μ([a, b])ⁿ⁺¹`. -/
theorem kpow_ge {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf)
    (x₀ : Set.Icc M.xmin xf) {a b : ℝ} (ha : M.ymin ≤ a) (hab : a ≤ b) (hb : b ≤ M.ymax)
    (n : ℕ) :
    M.law (Set.Icc a b) ^ (n + 1) ≤ SIWC.kpow (S.kernel xf) (n + 1) x₀
      {z | S.phi a x₀ (n + 1) ≤ z.1 ∧ z.1 ≤ S.phi b x₀ (n + 1)} := by
  have haI : a ∈ Set.Icc M.ymin M.ymax := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Set.Icc M.ymin M.ymax := ⟨ha.trans hab, hb⟩
  have hmeas : ∀ m, MeasurableSet {z : Set.Icc M.xmin xf |
      S.phi a x₀ (m + 1) ≤ z.1 ∧ z.1 ≤ S.phi b x₀ (m + 1)} := fun m =>
    measurable_subtype_coe measurableSet_Icc
  -- one step from any `z` in the band
  have hstep : ∀ m, ∀ z : Set.Icc M.xmin xf, S.phi a x₀ m ≤ z.1 → z.1 ≤ S.phi b x₀ m →
      M.law (Set.Icc a b) ≤ S.kernel xf z
        {w | S.phi a x₀ (m + 1) ≤ w.1 ∧ w.1 ≤ S.phi b x₀ (m + 1)} := by
    intro m z hza hzb
    rw [S.kernel_apply xf z (hmeas m)]
    refine measure_mono fun y hy => ?_
    have hza' := S.phi_ge ha x₀.2.1 m
    have h1 := S.sav_mono (Set.mem_Ici.2 hza') (Set.mem_Ici.2 z.2.1) hza
    have h2 := S.sav_mono (Set.mem_Ici.2 z.2.1)
      (Set.mem_Ici.2 (z.2.1.trans hzb)) hzb
    have hw : M.next (S.sav z) y ∈ Set.Icc (S.phi a x₀ (m + 1)) (S.phi b x₀ (m + 1)) := by
      rw [phi_succ, phi_succ]
      simp only [SIModel.next]
      constructor <;> nlinarith [M.R_pos, hy.1, hy.2]
    exact si_clamp_mem (S.phi_mem hxf hfix x₀.2 haI (m + 1)).2
      (S.phi_mem hxf hfix x₀.2 hbI (m + 1)).1 hw
  refine si_kpow_succ_ge_pow (S.kernel xf) hmeas ?_ (fun m z hz => hstep (m + 1) z hz.1 hz.2) n
  exact hstep 0 x₀ le_rfl le_rfl

/-- The bounds of p. 255 with `μ([a, b]) ≥ α(b − a)`: for `n ≥ 1`,
`Pⁿ(x₀, [φₙ(x₀, a), φₙ(x₀, b)]) ≥ αⁿ(b − a)ⁿ`; in particular (`a, b = y_max − δ, y_max` and
`y_min, y_min + δ`) the two displayed inequalities with `αⁿδⁿ`. -/
theorem kpow_ge_real {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf)
    {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b))
    (x₀ : Set.Icc M.xmin xf) {a b : ℝ} (ha : M.ymin ≤ a) (hab : a ≤ b) (hb : b ≤ M.ymax)
    {n : ℕ} (hn : 1 ≤ n) :
    (α * (b - a)) ^ n ≤ (SIWC.kpow (S.kernel xf) n x₀).real
      {z | S.phi a x₀ n ≤ z.1 ∧ z.1 ≤ S.phi b x₀ n} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := S.isMarkovKernel_kernel xf
  have := SIWC.ex_8_4a (S.kernel xf) (m + 1)
  have h0 : 0 ≤ α * (b - a) := mul_nonneg hα.le (by linarith)
  have h1 : ENNReal.ofReal (α * (b - a)) ≤ M.law (Set.Icc a b) :=
    ENNReal.ofReal_le_of_le_toReal (hμ a b ha hab hb)
  have h2 := S.kpow_ge hxf hfix x₀ ha hab hb m
  rw [measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _),
    ENNReal.ofReal_pow h0]
  exact (pow_le_pow_left' h1 _).trans h2

/-! ### Income `y_min` forever -/

/-- With `βR < 1`, at the lowest income cash on hand falls strictly:
`Râ(x) + y_min − rb < x` for `x > x_min`. -/
theorem next_low_lt (hβR : M.β * M.R < 1) {x : ℝ} (hx : M.xmin < x) :
    M.next (S.sav x) M.ymin < x := by
  have hx0 : M.xmin ≤ x := hx.le
  rcases (S.sav_mem x hx0).1.lt_or_eq with hpos | hz
  · by_contra hcon
    push Not at hcon
    have he' := (S.euler hx0).2 hpos
    have he : S.dV x = M.β * M.R * S.D (S.sav x) := by rw [S.envelope x hx0]; exact he'
    have hD := S.D_le_low (S.sav_mem x hx0).1
    have h1 := S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hx0.trans hcon))
      hcon
    have hdV := S.dV_pos hx0
    have hβR0 : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
    have : S.dV x ≤ M.β * M.R * S.dV x :=
      he.le.trans (mul_le_mul_of_nonneg_left (hD.trans h1) hβR0.le)
    nlinarith
  · rw [← hz, M.next_ymin, mul_zero, zero_add]; exact hx

/-- `Râ(x) + y_min − rb ≤ x` for `x ≥ x_min` (`βR < 1`). -/
theorem next_low_le (hβR : M.β * M.R < 1) {x : ℝ} (hx : M.xmin ≤ x) :
    M.next (S.sav x) M.ymin ≤ x := by
  rcases hx.lt_or_eq with hlt | heq
  · exact (S.next_low_lt hβR hlt).le
  · subst heq
    rw [(S.sav_xmin hβR).1, M.next_ymin, mul_zero, zero_add]

/-- With `βR < 1` and income `y_min` forever, cash on hand decreases to `x_min`:
`φₙ(x, y_min) ↓ x_min`. -/
theorem phi_low_tendsto (hβR : M.β * M.R < 1) {x : ℝ} (hx : M.xmin ≤ x) :
    Antitone (S.phi M.ymin x) ∧ Tendsto (S.phi M.ymin x) atTop (𝓝 M.xmin) := by
  have hge := S.phi_ge le_rfl hx
  have hanti : Antitone (S.phi M.ymin x) := antitone_nat_of_succ_le fun n => by
    rw [phi_succ]; exact S.next_low_le hβR (hge n)
  refine ⟨hanti, ?_⟩
  have hbdd : BddBelow (Set.range (S.phi M.ymin x)) := ⟨M.xmin, by
    rintro _ ⟨n, rfl⟩; exact hge n⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, S.phi M.ymin x n
  have hL : M.xmin ≤ L := le_ciInf hge
  have hT : Tendsto (fun n => M.next (S.sav (S.phi M.ymin x n)) M.ymin) atTop
      (𝓝 (M.next (S.sav L) M.ymin)) :=
    ((M.continuous_next M.ymin).continuousAt.tendsto.comp
      ((S.continuousOn_sav L (Set.mem_Ici.2 hL)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => Set.mem_Ici.2 (hge n)⟩)))
  have hS : Tendsto (fun n => S.phi M.ymin x (n + 1)) atTop (𝓝 L) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hfix : M.next (S.sav L) M.ymin = L := tendsto_nhds_unique hT hS
  rcases hL.lt_or_eq with hlt | heq
  · exact absurd hfix (S.next_low_lt hβR hlt).ne
  · rw [← heq] at hlim; exact hlim

/-! ### The mixing condition and Proposition 8.3.1 -/

/-- **The mixing condition** (Miao, p. 255; SLP Assumption 12.1) on `[x_min, x_f]`, `x_f` a
fixed point of `x ↦ Râ(x) + y_max − rb`: with `x̄ = x_min + (y_max − y_min)/2` there are
`N ≥ 1` and `ε > 0` with `Pᴺ(x_min, [x̄, x_f]) ≥ ε` and `Pᴺ(x_f, [x_min, x̄]) ≥ ε`. -/
theorem mixing (hβR : M.β * M.R < 1) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b))
    {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf) :
    ∃ (c : Set.Icc M.xmin xf) (ε : ℝ) (N : ℕ), 0 < ε ∧ 1 ≤ N ∧
      ε ≤ (SIWC.kpow (S.kernel xf) N ⟨M.xmin, Set.left_mem_Icc.2 hxf⟩).real (Set.Ici c) ∧
      ε ≤ (SIWC.kpow (S.kernel xf) N ⟨xf, Set.right_mem_Icc.2 hxf⟩).real (Set.Iic c) := by
  set Δ := (M.ymax - M.ymin) / 2
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  set cbar := M.xmin + Δ
  -- `N`: from `x_f` with income `y_min`, cash on hand drops below `x̄`
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((S.phi_low_tendsto hβR hxf).2.eventually
    (gt_mem_nhds (show M.xmin < cbar by simp only [cbar]; linarith)))
  set N := N₀ + 1
  have hN : S.phi M.ymin xf N < cbar := hN₀ N (by omega)
  -- `δ`: by continuity in `y`
  have hcw : ContinuousWithinAt (fun y => S.phi y xf N) (Set.Ici M.ymin) M.ymin :=
    S.continuousOn_phi hxf N M.ymin (Set.mem_Ici.2 le_rfl)
  have hev : {y | S.phi y xf N < cbar} ∈ 𝓝[≥] M.ymin :=
    hcw.tendsto.eventually (gt_mem_nhds hN)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  set δ := min (u - M.ymin) Δ
  have hδ : 0 < δ := lt_min (by linarith) hΔ
  have hδΔ : δ ≤ Δ := min_le_right _ _
  have hδu : M.ymin + δ ≤ u := by have := min_le_left (u - M.ymin) Δ; linarith
  have hδy : δ ≤ M.ymax - M.ymin := by simp only [Δ] at hδΔ; linarith
  -- the lower end
  have hlow : cbar ≤ S.phi (M.ymax - δ) M.xmin N := by
    have := S.phi_succ_ge (y := M.ymax - δ) (x := M.xmin) (by linarith) le_rfl N₀
    simp only [cbar, SIModel.xmin, Δ] at this ⊢
    simp only [Δ] at hδΔ
    linarith
  have hhighI : M.ymax - δ ∈ Set.Icc M.ymin M.ymax := ⟨by linarith, by linarith⟩
  have hcmem : cbar ∈ Set.Icc M.xmin xf := ⟨by simp only [cbar]; linarith,
    hlow.trans (S.phi_mem hxf hfix (Set.left_mem_Icc.2 hxf) hhighI N).2⟩
  refine ⟨⟨cbar, hcmem⟩, (α * δ) ^ N, N, pow_pos (mul_pos hα hδ) N, by omega, ?_, ?_⟩
  · have h := S.kpow_ge_real hxf hfix hα hμ ⟨M.xmin, Set.left_mem_Icc.2 hxf⟩
      (a := M.ymax - δ) (b := M.ymax) (by linarith) (by linarith) le_rfl (n := N) (by omega)
    rw [show M.ymax - (M.ymax - δ) = δ by ring] at h
    have := S.isMarkovKernel_kernel xf
    have := SIWC.ex_8_4a (S.kernel xf) N
    refine h.trans (measureReal_mono fun z hz => ?_)
    exact hlow.trans hz.1
  · have h := S.kpow_ge_real hxf hfix hα hμ ⟨xf, Set.right_mem_Icc.2 hxf⟩
      (a := M.ymin) (b := M.ymin + δ) le_rfl (by linarith) (by linarith) (n := N) (by omega)
    rw [show M.ymin + δ - M.ymin = δ by ring] at h
    have := S.isMarkovKernel_kernel xf
    have := SIWC.ex_8_4a (S.kernel xf) N
    refine h.trans (measureReal_mono fun z hz => ?_)
    have : S.phi (M.ymin + δ) xf N < cbar := hsub ⟨by linarith, hδu⟩
    exact hz.2.trans this.le

/-- **Proposition 8.3.1** (Schechtman and Escudero (1977), Clarida (1987), Aiyagari (1994);
Miao, p. 254). Let `βR < 1`, `y_min < y_max`, `−cu′′(c)/u′(c) < γ` for large `c` (`γ > 0`), and
let `y_t` be iid with law `μ` satisfying `μ([a, b]) ≥ α(b − a)` for `[a, b] ⊆ [y_min, y_max]`.
Then the cash-on-hand process `x_{t+1} = Râ(x_t) + y_{t+1} − rb` has a unique stationary
distribution `λ*` on `[x_min, x_max]`, and it is stable: `T*ⁿλ₀ ⇒ λ*` for every `λ₀`. -/
theorem proposition_8_3_1 (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b)) :
    ∃ lam : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure lam ∧
      SIWC.adjointOp (S.kernel S.xmax) lam = lam ∧
      (∀ ν : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure ν →
        SIWC.adjointOp (S.kernel S.xmax) ν = ν → ν = lam) ∧
      ∀ lam₀ : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure lam₀ →
        SIWC.ConvWeak (fun n => (SIWC.adjointOp (S.kernel S.xmax))^[n] lam₀) lam := by
  obtain ⟨hgt, ⟨hmem, -⟩, -, -⟩ := S.ex_8_9 hβR hddu hγ0 hγ hy
  have hxf : M.xmin ≤ S.xmax := hgt.le
  have := S.isMarkovKernel_kernel S.xmax
  obtain ⟨c, ε, N, hε, hN, hbot, htop⟩ := S.mixing hβR hy hα hμ hxf hmem.2
  exact SIWC.theorem_12_12_real hxf (S.kernel S.xmax) (S.isMonotoneTF_kernel _)
    (S.isFeller_kernel _) hε hN hbot htop

end SIModel.Solution

end Miao.IncompleteMarkets
