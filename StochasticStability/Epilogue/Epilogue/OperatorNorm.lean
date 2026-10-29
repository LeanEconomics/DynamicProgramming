/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.GeometricErgodicTheorem

/-!
# The operator norm `|||·|||_V` (MT §16.1.1)

Meyn and Tweedie, Chapter 16 introduction and §16.1.1, pp. 392–396. For `V : X → [1, ∞)` and two
transition kernels the `V`-norm distance (16.1) is

  `|||P₁ − P₂|||_V = sup_x ‖P₁(x, ·) − P₂(x, ·)‖_V / V(x)`,

`vOpNorm V P₁ P₂`, valued in `[0, ∞]`, with the `f`-norm `fNorm` of Chapter 14. The outer product
`1 ⊗ μ` is `Kernel.const X μ`, and `vErgDist V P μ n = |||Pⁿ − 1 ⊗ μ|||_V`.

**The space `L∞_V`.** `vNormFn V f = |f|_V = sup_x |f(x)|/V(x)`; `vNormFn_add_le` and
`vNormFn_smul` (it is a seminormed space of functions), `ofReal_abs_le_vNormFn_mul`,
`vNormFn_le`.

**Results.**
* **Lemma 16.1.1** (`lemma_16_1_1`, `lemma_16_1_1_bounded`, p. 395): when `P₁(x, V)` and
  `P₂(x, V)` are finite, `|||P₁ − P₂|||_V = sup_{|g|_V ≤ 1} |P₁ g − P₂ g|_V`, and
  `|P₁ g − P₂ g|_V ≤ |||P₁ − P₂|||_V |g|_V`: `P₁ − P₂` is a bounded operator on `L∞_V` with
  operator norm `|||P₁ − P₂|||_V`.
* `lintegral_le_fNorm_add`: `μ(f) ≤ ‖μ − ν‖_f + ν(f)` for finite measures (by truncation), so a
  finite `V`-norm distance to `μ` with `μ(V) < ∞` forces `Pⁿ(x, V) < ∞`
  (`lintegral_pow_le_vErgDist`, the bound (16.15)).
* `vOpNorm_comp_le`, `vErgDist_add_le`: **the submultiplicativity** used in Proposition 16.1.3,
  `|||P^{n+m} − 1 ⊗ μ|||_V ≤ |||Pⁿ − 1 ⊗ μ|||_V |||Pᵐ − 1 ⊗ μ|||_V` for invariant `μ`, from
  `(P^{n+m} − 1 ⊗ μ) = (Pᵐ − 1 ⊗ μ)(Pⁿ − 1 ⊗ μ)`.
* `vErgDist_zero_le`, `lintegral_ne_top_of_vErgDist_zero`: `|||P⁰ − 1 ⊗ μ|||_V ≤ 1 + μ(V)`, and
  it is finite only if `μ(V) < ∞`.
* **Proposition 16.1.3** (`proposition_16_1_3`, p. 396): if `|||P − 1 ⊗ μ|||_V < ∞` and
  `|||P^{n₀} − 1 ⊗ μ|||_V < 1`, then `Σ rⁿ |||Pⁿ − 1 ⊗ μ|||_V < ∞` for some `r > 1`;
  `vErgDist_le_geometric` is the bound `|||Pⁿ − 1 ⊗ μ|||_V ≤ K tⁿ`, `t < 1`, behind it.
* **Theorem 16.1.2** (`theorem_16_1_2`, p. 395): (V4) for a petite set and an everywhere finite
  `V` gives (16.12), `Σ rⁿ |||Pⁿ − 1 ⊗ μ|||_V < ∞`, for every invariant probability `μ`;
  `vErgDist_le_of_driftV4` is the bound `|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ`.

**Hypotheses.** The book takes `∞ > V ≥ 1` and works with signed measures of finite `V`-variation,
so that `π(V) < ∞` is implicit whenever `|||Pⁿ − 1 ⊗ π|||_V` is used. Since `fNorm` restricts to
test functions integrable for both measures, `μ(V) < ∞` is an explicit hypothesis of the
submultiplicativity and of Proposition 16.1.3.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The space `L∞_V` and the norm `|||·|||_V` -/

/-- The weighted sup norm `|f|_V = sup_x |f(x)| / V(x)` of the space `L∞_V` (MT Lemma 16.1.1,
p. 395). -/
noncomputable def vNormFn (V : X → ℝ≥0∞) (f : X → ℝ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal |f x| / V x

/-- **The `V`-norm distance** (16.1), MT p. 392:
`|||P₁ − P₂|||_V = sup_x ‖P₁(x, ·) − P₂(x, ·)‖_V / V(x)`. -/
noncomputable def vOpNorm (V : X → ℝ≥0∞) (P₁ P₂ : Kernel X X) : ℝ≥0∞ :=
  ⨆ x, fNorm V (P₁ x) (P₂ x) / V x

/-- `|||Pⁿ − 1 ⊗ μ|||_V`, the distance of (16.2), where `1 ⊗ μ` is the kernel `(x, A) ↦ μ(A)`
(MT p. 392). -/
noncomputable abbrev vErgDist (V : X → ℝ≥0∞) (P : Kernel X X) (μ : Measure X) (n : ℕ) : ℝ≥0∞ :=
  vOpNorm V (P ^ n) (Kernel.const X μ)

omit [MeasurableSpace X] in
/-- `|f(x)| ≤ |f|_V V(x)`. -/
theorem ofReal_abs_le_vNormFn_mul {V : X → ℝ≥0∞} (f : X → ℝ) {x : X} (h0 : V x ≠ 0)
    (ht : V x ≠ ∞) : ENNReal.ofReal |f x| ≤ vNormFn V f * V x :=
  (ENNReal.div_le_iff h0 ht).1 (le_iSup (fun y => ENNReal.ofReal |f y| / V y) x)

omit [MeasurableSpace X] in
/-- `|f|_V ≤ c` when `|f| ≤ c V`. -/
theorem vNormFn_le {V : X → ℝ≥0∞} {f : X → ℝ} {c : ℝ≥0∞}
    (h : ∀ x, ENNReal.ofReal |f x| ≤ c * V x) : vNormFn V f ≤ c :=
  iSup_le fun x => ENNReal.div_le_of_le_mul (h x)

omit [MeasurableSpace X] in
/-- `|f|_V ≤ 1` exactly when `|f| ≤ V`. -/
theorem vNormFn_le_one_iff {V : X → ℝ≥0∞} (hV0 : ∀ x, V x ≠ 0) (hVt : ∀ x, V x ≠ ∞)
    (f : X → ℝ) : vNormFn V f ≤ 1 ↔ ∀ x, ENNReal.ofReal |f x| ≤ V x := by
  refine ⟨fun h x => ?_, fun h => vNormFn_le fun x => by rw [one_mul]; exact h x⟩
  calc ENNReal.ofReal |f x| ≤ vNormFn V f * V x := ofReal_abs_le_vNormFn_mul f (hV0 x) (hVt x)
    _ ≤ 1 * V x := mul_le_mul' h le_rfl
    _ = V x := one_mul _

omit [MeasurableSpace X] in
/-- `L∞_V` is closed under addition: `|f + g|_V ≤ |f|_V + |g|_V`. -/
theorem vNormFn_add_le {V : X → ℝ≥0∞} (hV0 : ∀ x, V x ≠ 0) (hVt : ∀ x, V x ≠ ∞)
    (f g : X → ℝ) : vNormFn V (f + g) ≤ vNormFn V f + vNormFn V g := by
  refine vNormFn_le fun x => ?_
  calc ENNReal.ofReal |(f + g) x| ≤ ENNReal.ofReal (|f x| + |g x|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |f x| + ENNReal.ofReal |g x| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ vNormFn V f * V x + vNormFn V g * V x :=
        add_le_add (ofReal_abs_le_vNormFn_mul f (hV0 x) (hVt x))
          (ofReal_abs_le_vNormFn_mul g (hV0 x) (hVt x))
    _ = (vNormFn V f + vNormFn V g) * V x := (add_mul _ _ _).symm

omit [MeasurableSpace X] in
/-- `L∞_V` is closed under scalar multiplication: `|c f|_V = |c| |f|_V`. -/
theorem vNormFn_smul (V : X → ℝ≥0∞) (c : ℝ) (f : X → ℝ) :
    vNormFn V (fun x => c * f x) = ENNReal.ofReal |c| * vNormFn V f := by
  unfold vNormFn
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun x => ?_
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg c), mul_div_assoc]

/-- `|||P₁ − P₂|||_V` bounds each row: `‖P₁(x, ·) − P₂(x, ·)‖_V ≤ |||P₁ − P₂|||_V V(x)`. -/
theorem fNorm_le_vOpNorm_mul {V : X → ℝ≥0∞} (P₁ P₂ : Kernel X X) {x : X} (h0 : V x ≠ 0)
    (ht : V x ≠ ∞) : fNorm V (P₁ x) (P₂ x) ≤ vOpNorm V P₁ P₂ * V x :=
  (ENNReal.div_le_iff h0 ht).1 (le_iSup (fun y => fNorm V (P₁ y) (P₂ y) / V y) x)

/-- `|||P₁ − P₂|||_V ≤ c` when every row satisfies `‖P₁(x, ·) − P₂(x, ·)‖_V ≤ c V(x)`. -/
theorem vOpNorm_le {V : X → ℝ≥0∞} {P₁ P₂ : Kernel X X} {c : ℝ≥0∞}
    (h : ∀ x, fNorm V (P₁ x) (P₂ x) ≤ c * V x) : vOpNorm V P₁ P₂ ≤ c :=
  iSup_le fun x => ENNReal.div_le_of_le_mul (h x)

/-- The row bound for `|||Pⁿ − 1 ⊗ μ|||_V`. -/
theorem fNorm_pow_le_vErgDist_mul {V : X → ℝ≥0∞} (P : Kernel X X) (μ : Measure X) (n : ℕ)
    {x : X} (h0 : V x ≠ 0) (ht : V x ≠ ∞) :
    fNorm V ((P ^ n) x) μ ≤ vErgDist V P μ n * V x := by
  have h := fNorm_le_vOpNorm_mul (V := V) (P ^ n) (Kernel.const X μ) h0 ht
  rwa [Kernel.const_apply] at h

/-! ### Lemma 16.1.1 -/

/-- The defining bound with a multiple of `V`: if `|h| ≤ c V`, `c < ∞`, then
`|μ(h) − ν(h)| ≤ c ‖μ − ν‖_V`. -/
theorem ofReal_abs_integral_sub_le_mul_fNorm {V : X → ℝ≥0∞} {μ ν : Measure X} {h : X → ℝ}
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hm : Measurable h) (hb : ∀ x, ENNReal.ofReal |h x| ≤ c * V x)
    (hμ : Integrable h μ) (hν : Integrable h ν) :
    ENNReal.ofReal |∫ x, h x ∂μ - ∫ x, h x ∂ν| ≤ c * fNorm V μ ν := by
  rcases eq_or_ne c 0 with rfl | hc0
  · have h0 : ∀ x, h x = 0 := fun x => by
      have := hb x
      rw [zero_mul] at this
      exact abs_nonpos_iff.1 (ENNReal.ofReal_eq_zero.1 (le_antisymm this zero_le))
    simp [h0]
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  set h' : X → ℝ := fun x => h x / c.toReal with hh'
  have htest : IsFTest V μ ν h' := by
    refine ⟨hm.div_const _, fun x => ?_, hμ.div_const _, hν.div_const _⟩
    rw [hh', abs_div, abs_of_pos hcr, ENNReal.ofReal_div_of_pos hcr, ENNReal.ofReal_toReal hc]
    exact ENNReal.div_le_of_le_mul' (hb x)
  have hkey := ofReal_abs_integral_sub_le_fNorm htest
  have heq : ∫ x, h x ∂μ - ∫ x, h x ∂ν = c.toReal * (∫ x, h' x ∂μ - ∫ x, h' x ∂ν) := by
    rw [hh', integral_div, integral_div, ← sub_div, mul_div_cancel₀ _ hcr.ne']
  rw [heq, abs_mul, abs_of_pos hcr, ENNReal.ofReal_mul hcr.le, ENNReal.ofReal_toReal hc]
  exact mul_le_mul' le_rfl hkey

/-- **Lemma 16.1.1, the bound** (MT p. 395): when `P₁(x, V)` and `P₂(x, V)` are finite, `P₁ − P₂`
maps `L∞_V` to itself with `|P₁ g − P₂ g|_V ≤ |||P₁ − P₂|||_V |g|_V`. -/
theorem lemma_16_1_1_bounded {V : X → ℝ≥0∞} (hV0 : ∀ x, V x ≠ 0) (hVt : ∀ x, V x ≠ ∞)
    {P₁ P₂ : Kernel X X} (h₁ : ∀ x, ∫⁻ y, V y ∂P₁ x ≠ ∞) (h₂ : ∀ x, ∫⁻ y, V y ∂P₂ x ≠ ∞)
    {g : X → ℝ} (hg : Measurable g) (hgV : vNormFn V g ≠ ∞) :
    vNormFn V (fun x => ∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x) ≤ vOpNorm V P₁ P₂ * vNormFn V g := by
  have hb : ∀ y, ENNReal.ofReal |g y| ≤ vNormFn V g * V y := fun y =>
    ofReal_abs_le_vNormFn_mul g (hV0 y) (hVt y)
  have hint : ∀ (m : Measure X), ∫⁻ y, V y ∂m ≠ ∞ → Integrable g m := fun m hm =>
    integrable_of_ofReal_abs_le (f := fun y => vNormFn V g * V y) hg hb (by
      rw [lintegral_const_mul' _ _ hgV]; exact ENNReal.mul_ne_top hgV hm)
  refine vNormFn_le fun x => ?_
  calc ENNReal.ofReal |∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x|
      ≤ vNormFn V g * fNorm V (P₁ x) (P₂ x) :=
        ofReal_abs_integral_sub_le_mul_fNorm hgV hg hb (hint _ (h₁ x)) (hint _ (h₂ x))
    _ ≤ vNormFn V g * (vOpNorm V P₁ P₂ * V x) :=
        mul_le_mul' le_rfl (fNorm_le_vOpNorm_mul P₁ P₂ (hV0 x) (hVt x))
    _ = vOpNorm V P₁ P₂ * vNormFn V g * V x := by ring

/-- **Lemma 16.1.1** (MT p. 395): when `P₁(x, V)` and `P₂(x, V)` are finite,
`|||P₁ − P₂|||_V = sup_{|g|_V ≤ 1} |P₁ g − P₂ g|_V`, the operator norm of `P₁ − P₂` on
`L∞_V`. -/
theorem lemma_16_1_1 {V : X → ℝ≥0∞} (hV0 : ∀ x, V x ≠ 0) (hVt : ∀ x, V x ≠ ∞)
    {P₁ P₂ : Kernel X X} (h₁ : ∀ x, ∫⁻ y, V y ∂P₁ x ≠ ∞) (h₂ : ∀ x, ∫⁻ y, V y ∂P₂ x ≠ ∞) :
    vOpNorm V P₁ P₂ = ⨆ (g : X → ℝ) (_ : Measurable g ∧ vNormFn V g ≤ 1),
      vNormFn V (fun x => ∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x) := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup₂_le fun g hg => ?_)
  · refine ENNReal.div_le_of_le_mul (fNorm_le fun g hg => ?_)
    have hg1 : vNormFn V g ≤ 1 := (vNormFn_le_one_iff hV0 hVt g).2 hg.2.1
    calc ENNReal.ofReal |∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x|
        ≤ vNormFn V (fun x => ∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x) * V x :=
          ofReal_abs_le_vNormFn_mul (fun x => ∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x) (hV0 x) (hVt x)
      _ ≤ (⨆ (g : X → ℝ) (_ : Measurable g ∧ vNormFn V g ≤ 1),
            vNormFn V (fun x => ∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x)) * V x :=
          mul_le_mul' (le_iSup₂_of_le g ⟨hg.1, hg1⟩ le_rfl) le_rfl
  · calc vNormFn V (fun x => ∫ y, g y ∂P₁ x - ∫ y, g y ∂P₂ x)
        ≤ vOpNorm V P₁ P₂ * vNormFn V g :=
          lemma_16_1_1_bounded hV0 hVt h₁ h₂ hg.1 (ne_top_of_le_ne_top ENNReal.one_ne_top hg.2)
      _ ≤ vOpNorm V P₁ P₂ * 1 := mul_le_mul' le_rfl hg.2
      _ = vOpNorm V P₁ P₂ := mul_one _

/-! ### Truncation -/

/-- **Truncation**: `μ(f) ≤ ‖μ − ν‖_f + ν(f)` for finite measures and measurable `f ≥ 0` (test
the norm with `min(f, k)` and let `k → ∞`). -/
theorem lintegral_le_fNorm_add {f : X → ℝ≥0∞} (hf : Measurable f) (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫⁻ x, f x ∂μ ≤ fNorm f μ ν + ∫⁻ x, f x ∂ν := by
  have hk : ∀ k : ℕ, ∫⁻ x, min (f x) k ∂μ ≤ fNorm f μ ν + ∫⁻ x, f x ∂ν := by
    intro k
    have hfin : ∀ x, min (f x) (k : ℝ≥0∞) ≠ ∞ := fun x =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) (min_le_right _ _)
    set g : X → ℝ := fun x => (min (f x) (k : ℝ≥0∞)).toReal with hgdef
    have hgm : Measurable g := (hf.min measurable_const).ennreal_toReal
    have hg0 : ∀ x, 0 ≤ g x := fun x => ENNReal.toReal_nonneg
    have hgk : ∀ x, ‖g x‖ ≤ k := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
      have := ENNReal.toReal_mono (ENNReal.natCast_ne_top k) (min_le_right (f x) (k : ℝ≥0∞))
      simpa using this
    have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable g m := fun m _ =>
      Integrable.of_bound hgm.aestronglyMeasurable k (Eventually.of_forall hgk)
    have hgle : ∀ x, ENNReal.ofReal |g x| ≤ f x := fun x => by
      rw [abs_of_nonneg (hg0 x), hgdef, ENNReal.ofReal_toReal (hfin x)]
      exact min_le_left _ _
    have hkey := ofReal_abs_integral_sub_le_fNorm (⟨hgm, hgle, hint μ, hint ν⟩ :
      IsFTest f μ ν g)
    have hlint : ∀ (m : Measure X) [IsFiniteMeasure m],
        ∫⁻ x, min (f x) (k : ℝ≥0∞) ∂m = ENNReal.ofReal (∫ x, g x ∂m) := fun m _ => by
      rw [ofReal_integral_eq_lintegral_ofReal (hint m) (Eventually.of_forall hg0)]
      refine lintegral_congr fun x => ?_
      rw [hgdef, ENNReal.ofReal_toReal (hfin x)]
    have hb0 : 0 ≤ ∫ x, g x ∂ν := integral_nonneg hg0
    rw [hlint μ]
    calc ENNReal.ofReal (∫ x, g x ∂μ)
        ≤ ENNReal.ofReal (|∫ x, g x ∂μ - ∫ x, g x ∂ν| + ∫ x, g x ∂ν) := by
          refine ENNReal.ofReal_le_ofReal ?_
          linarith [le_abs_self (∫ x, g x ∂μ - ∫ x, g x ∂ν)]
      _ = ENNReal.ofReal |∫ x, g x ∂μ - ∫ x, g x ∂ν| + ENNReal.ofReal (∫ x, g x ∂ν) :=
          ENNReal.ofReal_add (abs_nonneg _) hb0
      _ ≤ fNorm f μ ν + ∫⁻ x, f x ∂ν := by
          refine add_le_add hkey ?_
          rw [← hlint ν]
          exact lintegral_mono fun x => min_le_left _ _
  have hsup : ∀ x, ⨆ k : ℕ, min (f x) (k : ℝ≥0∞) = f x := fun x => by
    refine le_antisymm (iSup_le fun k => min_le_left _ _) ?_
    rcases eq_or_ne (f x) ∞ with h | h
    · rw [h]
      refine le_of_forall_lt fun c hc => ?_
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hc.ne
      exact hk.trans_le (le_iSup_of_le k (by simp))
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt h
      exact le_iSup_of_le k (le_min le_rfl hk.le)
  have hmono : Monotone fun (k : ℕ) (x : X) => min (f x) (k : ℝ≥0∞) := fun i j hij x =>
    min_le_min le_rfl (Nat.cast_le.2 hij)
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, ⨆ k : ℕ, min (f x) (k : ℝ≥0∞) ∂μ := by simp_rw [hsup]
    _ = ⨆ k : ℕ, ∫⁻ x, min (f x) (k : ℝ≥0∞) ∂μ :=
        lintegral_iSup (fun k => hf.min measurable_const) hmono
    _ ≤ fNorm f μ ν + ∫⁻ x, f x ∂ν := iSup_le hk

/-- **(16.15)**: `Pⁿ(x, V) ≤ |||Pⁿ − 1 ⊗ μ|||_V V(x) + μ(V)`. -/
theorem lintegral_pow_le_vErgDist {V : X → ℝ≥0∞} (hV : Measurable V) (P : Kernel X X)
    [IsMarkovKernel P] (μ : Measure X) [IsFiniteMeasure μ] (n : ℕ) {x : X} (h0 : V x ≠ 0)
    (ht : V x ≠ ∞) :
    ∫⁻ y, V y ∂(P ^ n) x ≤ vErgDist V P μ n * V x + ∫⁻ y, V y ∂μ := by
  have := isMarkovKernel_pow P n
  exact (lintegral_le_fNorm_add hV _ _).trans
    (add_le_add (fNorm_pow_le_vErgDist_mul P μ n h0 ht) le_rfl)

/-! ### `n = 0` -/

/-- `|||P⁰ − 1 ⊗ μ|||_V ≤ 1 + μ(V)` for `V ≥ 1`. -/
theorem vErgDist_zero_le {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (P : Kernel X X) (μ : Measure X) : vErgDist V P μ 0 ≤ 1 + ∫⁻ y, V y ∂μ := by
  refine vOpNorm_le fun x => ?_
  have hV0 : V x ≠ 0 := (zero_lt_one.trans_le (hV1 x)).ne'
  rw [Kernel.const_apply, pow_zero_apply]
  calc fNorm V (Measure.dirac x) μ ≤ ∫⁻ y, V y ∂Measure.dirac x + ∫⁻ y, V y ∂μ :=
        fNorm_le_add V _ _
    _ = V x + ∫⁻ y, V y ∂μ := by rw [lintegral_dirac' x hV]
    _ ≤ V x + (∫⁻ y, V y ∂μ) * V x := add_le_add le_rfl (le_mul_of_one_le_right' (hV1 x))
    _ = (1 + ∫⁻ y, V y ∂μ) * V x := by ring

/-- `|||P⁰ − 1 ⊗ μ|||_V < ∞` forces `μ(V) < ∞` (when `V` is finite somewhere). -/
theorem lintegral_ne_top_of_vErgDist_zero {V : X → ℝ≥0∞} (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) {x₀ : X} (hx₀ : V x₀ ≠ ∞) (P : Kernel X X) (μ : Measure X)
    [IsFiniteMeasure μ] (h : vErgDist V P μ 0 ≠ ∞) : ∫⁻ y, V y ∂μ ≠ ∞ := by
  have hV0 : V x₀ ≠ 0 := (zero_lt_one.trans_le (hV1 x₀)).ne'
  have h1 := fNorm_pow_le_vErgDist_mul (V := V) P μ 0 hV0 hx₀
  rw [pow_zero_apply, fNorm_comm] at h1
  have h2 := lintegral_le_fNorm_add hV μ (Measure.dirac x₀)
  rw [lintegral_dirac' x₀ hV] at h2
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top h hx₀, hx₀⟩)
    (h2.trans (add_le_add h1 le_rfl))

/-! ### Submultiplicativity -/

/-- **The composition bound** behind Proposition 16.1.3 (MT p. 396): for `μ` invariant for `Q₂`,
with `μ(V) < ∞` and finite distances,
`|||Q₁Q₂ − 1 ⊗ μ|||_V ≤ |||Q₁ − 1 ⊗ μ|||_V |||Q₂ − 1 ⊗ μ|||_V`, where `Q₁Q₂` is "first `Q₁`,
then `Q₂`". The proof is `(Q₁Q₂ − 1 ⊗ μ) g = (Q₁ − 1 ⊗ μ) h` with
`h = (Q₂ − 1 ⊗ μ) g`, since `μ(h) = 0`. -/
theorem vOpNorm_comp_le {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {Q₁ Q₂ : Kernel X X} [IsMarkovKernel Q₁] [IsMarkovKernel Q₂]
    {μ : Measure X} [IsProbabilityMeasure μ] (hinv : Q₂ ∘ₘ μ = μ) (hμV : ∫⁻ y, V y ∂μ ≠ ∞)
    (h₁ : vOpNorm V Q₁ (Kernel.const X μ) ≠ ∞) (h₂ : vOpNorm V Q₂ (Kernel.const X μ) ≠ ∞) :
    vOpNorm V (Q₂ ∘ₖ Q₁) (Kernel.const X μ) ≤
      vOpNorm V Q₁ (Kernel.const X μ) * vOpNorm V Q₂ (Kernel.const X μ) := by
  set A₁ := vOpNorm V Q₁ (Kernel.const X μ)
  set A₂ := vOpNorm V Q₂ (Kernel.const X μ)
  have hV0 : ∀ x, V x ≠ 0 := fun x => (zero_lt_one.trans_le (hV1 x)).ne'
  have hrow : ∀ (Q : Kernel X X) (y : X),
      fNorm V (Q y) μ ≤ vOpNorm V Q (Kernel.const X μ) * V y := fun Q y => by
    have h := fNorm_le_vOpNorm_mul (V := V) Q (Kernel.const X μ) (hV0 y) (hVt y)
    rwa [Kernel.const_apply] at h
  have hQV : ∀ (Q : Kernel X X) [IsMarkovKernel Q], vOpNorm V Q (Kernel.const X μ) ≠ ∞ →
      ∀ y, ∫⁻ z, V z ∂Q y ≠ ∞ := fun Q _ hQ y =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hQ (hVt y), hμV⟩)
      ((lintegral_le_fNorm_add hV _ _).trans (add_le_add (hrow Q y) le_rfl))
  refine vOpNorm_le fun x => ?_
  rw [Kernel.const_apply]
  refine fNorm_le fun g hg => ?_
  have hgQ : ∀ y, Integrable g (Q₂ y) := fun y =>
    integrable_of_ofReal_abs_le hg.1 hg.2.1 (hQV Q₂ h₂ y)
  set c : ℝ := ∫ z, g z ∂μ with hc
  set h : X → ℝ := fun y => ∫ z, g z ∂Q₂ y - c with hh
  have hhm : Measurable h :=
    (StronglyMeasurable.integral_kernel (κ := Q₂) hg.1.stronglyMeasurable).measurable.sub_const _
  have hhb : ∀ y, ENNReal.ofReal |h y| ≤ A₂ * V y := fun y =>
    (ofReal_abs_integral_sub_le_fNorm ⟨hg.1, hg.2.1, hgQ y, hg.2.2.2⟩).trans (hrow Q₂ y)
  have hhint : ∀ (m : Measure X), ∫⁻ y, V y ∂m ≠ ∞ → Integrable h m := fun m hm =>
    integrable_of_ofReal_abs_le (f := fun y => A₂ * V y) hhm hhb (by
      rw [lintegral_const_mul' _ _ h₂]; exact ENNReal.mul_ne_top h₂ hm)
  have hF : (fun y => ∫ z, g z ∂Q₂ y) = fun y => h y + c := by
    funext y; rw [hh]; ring
  have hFint : ∀ (m : Measure X), ∫⁻ y, V y ∂m ≠ ∞ →
      Integrable (fun y => ∫ z, g z ∂Q₂ y) m := fun m hm => by
    rw [hF]
    have : IsFiniteMeasure m := by
      refine ⟨lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hm)⟩
      calc m univ = ∫⁻ _, 1 ∂m := (lintegral_one).symm
        _ ≤ ∫⁻ y, V y ∂m := lintegral_mono hV1
    exact (hhint m hm).add (integrable_const c)
  -- the two integrals of `h`
  have hint1 : ∫ y, h y ∂Q₁ x = ∫ z, g z ∂(Q₂ ∘ₖ Q₁) x - c := by
    rw [Kernel.integral_comp hg.2.2.1, hh, integral_sub (hFint _ (hQV Q₁ h₁ x))
      (integrable_const c), integral_const, probReal_univ, one_smul]
  have hint2 : ∫ y, h y ∂μ = 0 := by
    have hcomp := integral_comp_kernel_of_integrable Q₂ μ hg.1 (by rw [hinv]; exact hg.2.2.2)
    rw [hinv] at hcomp
    rw [hh, integral_sub (hFint μ hμV) (integrable_const c), integral_const, probReal_univ,
      one_smul, ← hcomp, hc, sub_self]
  have hdiff : ∫ z, g z ∂(Q₂ ∘ₖ Q₁) x - ∫ z, g z ∂μ = ∫ y, h y ∂Q₁ x - ∫ y, h y ∂μ := by
    rw [hint1, hint2, sub_zero]
  rw [hdiff]
  calc ENNReal.ofReal |∫ y, h y ∂Q₁ x - ∫ y, h y ∂μ| ≤ A₂ * fNorm V (Q₁ x) μ :=
        ofReal_abs_integral_sub_le_mul_fNorm h₂ hhm hhb (hhint _ (hQV Q₁ h₁ x)) (hhint μ hμV)
    _ ≤ A₂ * (A₁ * V x) := mul_le_mul' le_rfl (hrow Q₁ x)
    _ = A₁ * A₂ * V x := by ring

/-- **Submultiplicativity** (MT p. 396): for invariant `μ` with `μ(V) < ∞`,
`|||P^{m+n} − 1 ⊗ μ|||_V ≤ |||Pᵐ − 1 ⊗ μ|||_V |||Pⁿ − 1 ⊗ μ|||_V` when both are finite. -/
theorem vErgDist_add_le {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hinv : IsInvariant P μ) (hμV : ∫⁻ y, V y ∂μ ≠ ∞) {m n : ℕ}
    (hm : vErgDist V P μ m ≠ ∞) (hn : vErgDist V P μ n ≠ ∞) :
    vErgDist V P μ (m + n) ≤ vErgDist V P μ m * vErgDist V P μ n := by
  have := isMarkovKernel_pow P m
  have := isMarkovKernel_pow P n
  unfold vErgDist
  rw [pow_add_eq]
  exact vOpNorm_comp_le hV hV1 hVt (hinv.pow n) hμV hm hn

/-- All the distances are finite when `|||P − 1 ⊗ μ|||_V` is (and `μ(V) < ∞`). -/
theorem vErgDist_ne_top {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hinv : IsInvariant P μ) (hμV : ∫⁻ y, V y ∂μ ≠ ∞)
    (h1 : vErgDist V P μ 1 ≠ ∞) (n : ℕ) : vErgDist V P μ n ≠ ∞ := by
  induction n with
  | zero =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hμV⟩)
      (vErgDist_zero_le hV hV1 P μ)
  | succ n ih =>
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ih h1)
      (vErgDist_add_le hV hV1 hVt hinv hμV ih h1)

/-! ### Proposition 16.1.3 -/

/-- `|||P^{n₀ k + i} − 1 ⊗ μ|||_V ≤ |||Pⁱ − 1 ⊗ μ|||_V γᵏ` with `γ = |||P^{n₀} − 1 ⊗ μ|||_V`. -/
theorem vErgDist_mul_add_le {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hinv : IsInvariant P μ) (hμV : ∫⁻ y, V y ∂μ ≠ ∞)
    (hfin : ∀ n, vErgDist V P μ n ≠ ∞) (n₀ i k : ℕ) :
    vErgDist V P μ (n₀ * k + i) ≤ vErgDist V P μ i * vErgDist V P μ n₀ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : n₀ * (k + 1) + i = (n₀ * k + i) + n₀ := by ring
    rw [he, pow_succ, ← mul_assoc]
    exact (vErgDist_add_le hV hV1 hVt hinv hμV (hfin _) (hfin _)).trans
      (mul_le_mul' ih le_rfl)

/-- **The geometric bound** behind Proposition 16.1.3: if `|||P − 1 ⊗ μ|||_V < ∞` and
`|||P^{n₀} − 1 ⊗ μ|||_V < 1`, then `|||Pⁿ − 1 ⊗ μ|||_V ≤ K tⁿ` for some `t < 1`, `K < ∞`. -/
theorem vErgDist_le_geometric {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hinv : IsInvariant P μ) (hμV : ∫⁻ y, V y ∂μ ≠ ∞)
    (h1 : vErgDist V P μ 1 ≠ ∞) {n₀ : ℕ} (hn₀ : 0 < n₀) (hγ : vErgDist V P μ n₀ < 1) :
    ∃ t : ℝ≥0∞, t < 1 ∧ 0 < t ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n, vErgDist V P μ n ≤ K * t ^ n := by
  have hfin := vErgDist_ne_top hV hV1 hVt hinv hμV h1
  set γ := vErgDist V P μ n₀
  set γ' := max γ 2⁻¹ with hγ'
  have hγ'1 : γ' < 1 := max_lt hγ (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  have hγ'0 : γ' ≠ 0 := (lt_of_lt_of_le (by norm_num) (le_max_right γ 2⁻¹)).ne'
  have hγ't : γ' ≠ ∞ := (hγ'1.trans ENNReal.one_lt_top).ne
  have hn₀r : (0 : ℝ) < 1 / n₀ := by positivity
  set t := γ' ^ (1 / n₀ : ℝ) with ht
  have htn : t ^ n₀ = γ' := by
    rw [ht, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    field_simp
    exact ENNReal.rpow_one γ'
  have ht1 : t < 1 := ENNReal.rpow_lt_one hγ'1 hn₀r
  have ht0 : 0 < t := ENNReal.rpow_pos (pos_iff_ne_zero.2 hγ'0) hγ't
  set K := ∑ i ∈ Finset.range n₀, vErgDist V P μ i with hK
  have hKt : K ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => hfin i
  refine ⟨t, ht1, ht0, K * γ'⁻¹, ENNReal.mul_ne_top hKt (ENNReal.inv_ne_top.2 hγ'0), fun n => ?_⟩
  have hdec : n = n₀ * (n / n₀) + n % n₀ := (Nat.div_add_mod n n₀).symm
  have hlt : n % n₀ < n₀ := Nat.mod_lt n hn₀
  have hAi : vErgDist V P μ (n % n₀) ≤ K :=
    Finset.single_le_sum (f := fun i => vErgDist V P μ i) (fun _ _ => zero_le)
      (Finset.mem_range.2 hlt)
  have hpow : γ' ^ (n / n₀) * γ' ≤ t ^ n := by
    calc γ' ^ (n / n₀) * γ' = t ^ (n₀ * (n / n₀)) * t ^ n₀ := by rw [pow_mul, htn]
      _ ≤ t ^ (n₀ * (n / n₀)) * t ^ (n % n₀) :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' ht1.le hlt.le)
      _ = t ^ n := by rw [← pow_add, ← hdec]
  calc vErgDist V P μ n = vErgDist V P μ (n₀ * (n / n₀) + n % n₀) := by rw [← hdec]
    _ ≤ vErgDist V P μ (n % n₀) * γ ^ (n / n₀) :=
        vErgDist_mul_add_le hV hV1 hVt hinv hμV hfin n₀ (n % n₀) (n / n₀)
    _ ≤ K * γ' ^ (n / n₀) := mul_le_mul' hAi (pow_le_pow_left₀ zero_le (le_max_left _ _) _)
    _ = K * γ'⁻¹ * (γ' ^ (n / n₀) * γ') := by
        rw [mul_comm (γ' ^ (n / n₀)) γ', ← mul_assoc, mul_assoc K, ENNReal.inv_mul_cancel hγ'0 hγ't,
          mul_one]
    _ ≤ K * γ'⁻¹ * t ^ n := mul_le_mul' le_rfl hpow

/-- A geometric bound `aₙ ≤ K tⁿ`, `t < 1`, gives `Σ rⁿ aₙ < ∞` for some `r > 1`. -/
theorem exists_tsum_mul_pow_ne_top {a : ℕ → ℝ≥0∞} {t K : ℝ≥0∞} (ht : t < 1) (hK : K ≠ ∞)
    (h : ∀ n, a n ≤ K * t ^ n) : ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * a n ≠ ∞ := by
  obtain ⟨r, hr, hrt, htr⟩ := exists_one_lt_mul_lt_one ht
  refine ⟨r, hr, hrt, ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n =>
    mul_le_mul' le_rfl (h n))⟩
  have he : ∀ n, r ^ n * (K * t ^ n) = K * (t * r) ^ n := fun n => by rw [mul_pow]; ring
  simp_rw [he]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top hK (ENNReal.inv_ne_top.2 (tsub_pos_of_lt htr).ne')

/-- **Proposition 16.1.3** (MT p. 396): if `μ` is an invariant probability with `μ(V) < ∞`,
`|||P − 1 ⊗ μ|||_V < ∞` and `|||P^{n₀} − 1 ⊗ μ|||_V < 1` for some `n₀ ≥ 1`, then
`Σₙ rⁿ |||Pⁿ − 1 ⊗ μ|||_V < ∞` for some `r > 1`. -/
theorem proposition_16_1_3 {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVt : ∀ x, V x ≠ ∞) {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hinv : IsInvariant P μ) (hμV : ∫⁻ y, V y ∂μ ≠ ∞)
    (h1 : vErgDist V P μ 1 ≠ ∞) {n₀ : ℕ} (hn₀ : 0 < n₀) (hγ : vErgDist V P μ n₀ < 1) :
    ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist V P μ n ≠ ∞ := by
  obtain ⟨t, ht1, -, K, hK, hb⟩ := vErgDist_le_geometric hV hV1 hVt hinv hμV h1 hn₀ hγ
  exact exists_tsum_mul_pow_ne_top ht1 hK hb

/-! ### Theorem 16.1.2 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The rate in Theorem 16.1.2**: under (V4) for a petite set and an everywhere finite `V ≥ 1`,
every invariant probability `μ` has `μ(V) < ∞` and `|||Pⁿ − 1 ⊗ μ|||_V ≤ R r⁻ⁿ` for some `r > 1`,
`R < ∞` (from (15.4), Theorem 15.4.1). -/
theorem vErgDist_le_of_driftV4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) :
    ∫⁻ y, V y ∂μ ≠ ∞ ∧ ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∃ R : ℝ≥0∞, R ≠ ∞ ∧
      ∀ n, vErgDist V P μ n ≤ R * r⁻¹ ^ n := by
  have := nonempty_of_isProbabilityMeasure μ
  inhabit X
  obtain ⟨-, hgeo⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC h (hVt default)
  obtain ⟨hμV, r, hr, hrt, R, hR, hbd⟩ := hgeo μ hμ
  refine ⟨hμV, r, hr, hrt, R, hR, fun n => vOpNorm_le fun x => ?_⟩
  rw [Kernel.const_apply]
  have hr0 : r ^ n ≠ 0 := pow_ne_zero n (zero_lt_one.trans hr).ne'
  have hrt' : r ^ n ≠ ∞ := ENNReal.pow_ne_top hrt
  have h1 : r ^ n * fNorm V ((P ^ n) x) μ ≤ R * V x :=
    (ENNReal.le_tsum (f := fun k => r ^ k * fNorm V ((P ^ k) x) μ) n).trans (hbd x)
  calc fNorm V ((P ^ n) x) μ = (r ^ n)⁻¹ * (r ^ n * fNorm V ((P ^ n) x) μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hr0 hrt', one_mul]
    _ ≤ (r ^ n)⁻¹ * (R * V x) := mul_le_mul' le_rfl h1
    _ = R * r⁻¹ ^ n * V x := by rw [ENNReal.inv_pow]; ring

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.1.2** (MT p. 395): for a `ψ`-irreducible aperiodic chain with (V4) for a petite
set `C` and an everywhere finite `V ≥ 1`, every invariant probability `μ` has
`Σₙ rⁿ |||Pⁿ − 1 ⊗ μ|||_V < ∞` (16.12) for some `r > 1`; in particular
`|||Pⁿ − 1 ⊗ μ|||_V → 0`. -/
theorem theorem_16_1_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {V : X → ℝ≥0∞}
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (hVt : ∀ x, V x ≠ ∞) {ρ b : ℝ≥0∞} (hρ : ρ < 1)
    (hb : b ≠ ∞) {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) :
    (∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist V P μ n ≠ ∞) ∧
      Tendsto (vErgDist V P μ) atTop (𝓝 0) := by
  obtain ⟨-, r, hr, hrt, R, hR, hbd⟩ := vErgDist_le_of_driftV4 hψ hap hV hV1 hVt hρ hb hC h μ hμ
  have hr1 : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr
  refine ⟨exists_tsum_mul_pow_ne_top hr1 hR hbd, ?_⟩
  have hlim : Tendsto (fun n => R * r⁻¹ ^ n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
      (Or.inr hR)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hbd

end MeynTweedie.Epilogue
