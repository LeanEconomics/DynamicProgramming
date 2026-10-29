/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.FNormErgodicTheorem
import LimitTheorems.KendallTheorem

/-!
# Geometrically weighted sums along the path (MT §15.1–15.2)

Meyn and Tweedie, §15.1.1 and §15.2.1, pp. 364–365 and 373. This module is the infrastructure of
Chapter 15: the generating functions of hitting times evaluated at `r ≥ 1`.

**Powers with exponent in `ℕ ∪ {∞}`.** `tpow r t = rᵗ`, with `r^∞ = ∞`; `tpow_add`,
`tpow_mono`, `tpow_sq`, `tpow_eq_one_add` (`rᵗ = 1 + (r − 1) Σ_{k<t} rᵏ` for `r > 1`) and
`tpow_le_one_add` (`rᵗ ≤ 1 + (r − 1)/(κ − 1) κᵗ` for `1 < r ≤ κ`, the bound that replaces the
book's use of Jensen's inequality on p. 374).

**The quantities of the chapter.** For measurable `B` and `f : X → [0, ∞]`:
* `kendallMoment P B r x = E_x[r^{τ_B}]` ((15.2), the Kendall property);
* `geomSum P B r f x = E_x[Σ_{k=0}^{τ_B − 1} f(Φ_k) rᵏ]` ((15.22), (15.36));
* `geomTaboo P B r f x = U_B^{(r)}(x, f) = E_x[Σ_{k=1}^{τ_B} f(Φ_k) rᵏ]` ((15.12), (15.23));
* `geomG P B r f x = G_B^{(r)}(x, f) = E_x[Σ_{k=0}^{σ_B} f(Φ_k) rᵏ]` ((15.29)).
At `r = 1` they are the Chapter 14 quantities (`geomSum_one`, `geomTaboo_one`, `geomG_one`).

**Identities.**
* `geomTaboo_eq`: `U_B^{(r)} = r P G_B^{(r)}` (the first step, (15.31));
* `geomG_eq`: `G_B^{(r)} = I + I_{Bᶜ} U_B^{(r)}` (the definition on p. 376);
* `kendallMoment_eq_one_add`: `E_x[r^{τ_B}] = 1 + (r − 1) E_x[Σ_{k<τ_B} rᵏ]`;
* `kendallMoment_le_geomTaboo`: `E_x[r^{τ_B}] ≤ U_B^{(r)}(x, f)` for `f ≥ 1` (p. 368);
* `geomSum_le_add_geomTaboo`, `geomTaboo_le_geomSum_add`: the two sums differ by the end terms.

**The strong Markov property with geometric weights.**
* `lintegral_weight_shiftAt`: `E[w(ζ) H ∘ θ^ζ; A, ζ < ∞] = E[w(ζ) E_{Φ_ζ}[H]; A, ζ < ∞]` for
  `A ∩ {ζ = n} ∈ 𝓕ₙ`;
* `sumBefore_le_shift_weighted`, `lintegral_sumBefore_le_weighted`: the bound
  `E_x[Σ_{k<T} G_k] ≤ E_x[Σ_{k<ζ} G_k] + E_x[w(ζ) E_{Φ_ζ}[Σ_{k<T} G_k]; ζ < ∞]` for weights with
  `G_{t+j} = w(t) G_j ∘ θᵗ` (as `rᵏ f(Φ_k)`);
* `geomTaboo_le_add_mul`, `geomSum_le_add_mul`: through a set `A`,
  `U_B^{(r)}(x, f) ≤ U_A^{(r)}(x, f) + (sup_A U_B^{(r)}) E_x[r^{τ_A}]`, and the same for the sums
  from time `0`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### Powers with exponent in `ℕ ∪ {∞}` -/

/-- `rᵗ` for `t ∈ ℕ ∪ {∞}`, with `r^∞ = ∞` (the convention for `E_x[r^{τ}]`, `r > 1`). -/
noncomputable def tpow (r : ℝ≥0∞) (t : WithTop ℕ) : ℝ≥0∞ :=
  WithTop.recTopCoe (C := fun _ => ℝ≥0∞) ∞ (fun n : ℕ => r ^ n) t

/-- `r^∞ = ∞`. -/
theorem tpow_top (r : ℝ≥0∞) : tpow r ⊤ = ∞ := rfl

/-- `rⁿ` for a natural `n`. -/
theorem tpow_coe (r : ℝ≥0∞) (n : ℕ) : tpow r (n : WithTop ℕ) = r ^ n := rfl

/-- `rⁿ` for a natural `n`, written with `WithTop.some`. -/
theorem tpow_some (r : ℝ≥0∞) (n : ℕ) : tpow r (WithTop.some n) = r ^ n := rfl

/-- `rᵗ ≥ 1` for `r ≥ 1`. -/
theorem one_le_tpow {r : ℝ≥0∞} (hr : 1 ≤ r) (t : WithTop ℕ) : 1 ≤ tpow r t := by
  cases t with
  | top => exact le_top
  | coe n => exact one_le_pow₀ hr

/-- `t ↦ rᵗ` is monotone for `r ≥ 1`. -/
theorem tpow_mono {r : ℝ≥0∞} (hr : 1 ≤ r) {s t : WithTop ℕ} (h : s ≤ t) : tpow r s ≤ tpow r t := by
  cases t with
  | top => exact le_top
  | coe n =>
    cases s with
    | top => exact absurd h (WithTop.not_top_le_coe n)
    | coe m => exact pow_le_pow_right₀ hr (WithTop.coe_le_coe.1 h)

/-- `r ↦ rᵗ` is monotone. -/
theorem tpow_mono_left {r s : ℝ≥0∞} (h : r ≤ s) (t : WithTop ℕ) : tpow r t ≤ tpow s t := by
  cases t with
  | top => exact le_top
  | coe n => exact pow_le_pow_left₀ zero_le h n

/-- `r^{s + t} = rˢ rᵗ` for `r ≥ 1`. -/
theorem tpow_add {r : ℝ≥0∞} (hr : 1 ≤ r) (s t : WithTop ℕ) :
    tpow r (s + t) = tpow r s * tpow r t := by
  have hne : ∀ u, tpow r u ≠ 0 := fun u => (zero_lt_one.trans_le (one_le_tpow hr u)).ne'
  cases s with
  | top => rw [WithTop.top_add, tpow_top, ENNReal.top_mul (hne t)]
  | coe m =>
    cases t with
    | top => rw [WithTop.add_top, tpow_top, ENNReal.mul_top (hne _)]
    | coe n => rw [← WithTop.coe_add, tpow_some, tpow_some, tpow_some, pow_add]

/-- `(r²)ᵗ = (rᵗ)²`. -/
theorem tpow_sq (r : ℝ≥0∞) (t : WithTop ℕ) : tpow (r ^ 2) t = tpow r t ^ 2 := by
  cases t with
  | top => rw [tpow_top, tpow_top, ENNReal.top_pow two_ne_zero]
  | coe n => rw [tpow_some, tpow_some, ← pow_mul, ← pow_mul, mul_comm]

/-- The geometric sum `rⁿ = 1 + (r − 1) Σ_{k<n} rᵏ` in `[0, ∞]`, for `r ≥ 1`. -/
theorem pow_eq_one_add_sum {r : ℝ≥0∞} (hr : 1 ≤ r) (n : ℕ) :
    r ^ n = 1 + (r - 1) * ∑ k ∈ range n, r ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ← add_assoc, ← ih, pow_succ]
    calc r ^ n * r = r ^ n * (1 + (r - 1)) := by rw [add_tsub_cancel_of_le hr]
      _ = r ^ n + (r - 1) * r ^ n := by ring

/-- `Σ_k 1 = ∞` in `[0, ∞]` for terms bounded below by `1`. -/
theorem tsum_eq_top_of_one_le {g : ℕ → ℝ≥0∞} (hg : ∀ k, 1 ≤ g k) : ∑' k, g k = ∞ := by
  refine top_le_iff.1 ?_
  calc ∞ = ∑' _ : ℕ, (1 : ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' k, g k := ENNReal.tsum_le_tsum hg

/-- **`rᵗ = 1 + (r − 1) Σ_{k<t} rᵏ`** for `r > 1` and `t ∈ ℕ ∪ {∞}`. -/
theorem tpow_eq_one_add {r : ℝ≥0∞} (hr : 1 < r) (t : WithTop ℕ) :
    tpow r t = 1 + (r - 1) * ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < t}.indicator (fun k => r ^ k) k
    := by
  cases t with
  | top =>
    have hs : ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < ⊤}.indicator (fun k => r ^ k) k = ∞ := by
      refine tsum_eq_top_of_one_le fun k => ?_
      rw [indicator_of_mem (show k ∈ {k : ℕ | (k : WithTop ℕ) < ⊤} from WithTop.coe_lt_top k)]
      exact one_le_pow₀ hr.le
    rw [tpow_top, hs, ENNReal.mul_top (tsub_pos_iff_lt.2 hr).ne', add_top]
  | coe n =>
    rw [tpow_some, pow_eq_one_add_sum hr.le n, tsum_eq_sum (s := range n) fun k hk =>
      indicator_of_notMem (show k ∉ {k : ℕ | (k : WithTop ℕ) < WithTop.some n} from fun h =>
        hk (Finset.mem_range.2 (WithTop.coe_lt_coe.1 h))) _]
    congr 2
    refine Finset.sum_congr rfl fun k hk => (indicator_of_mem
      (show k ∈ {k : ℕ | (k : WithTop ℕ) < WithTop.some n} from
        WithTop.coe_lt_coe.2 (Finset.mem_range.1 hk)) _).symm

/-- `ω ↦ r^{τ(ω)}` is measurable when every `{n < τ}` is an event (`r > 1`). -/
theorem measurable_tpow_comp {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → WithTop ℕ}
    (hτ : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < τ ω}) {r : ℝ≥0∞} (hr : 1 < r) :
    Measurable fun ω => tpow r (τ ω) := by
  have h : (fun ω => tpow r (τ ω)) =
      fun ω => 1 + (r - 1) * sumBefore τ (fun k _ => r ^ k) ω := funext fun ω => by
    rw [tpow_eq_one_add hr, sumBefore_eq_tsum]
  rw [h]
  exact measurable_const.add (measurable_const.mul (measurable_sumBefore hτ fun _ =>
    measurable_const))

/-- **`rᵗ ≤ 1 + (r − 1)/(κ − 1) κᵗ`** for `1 < r ≤ κ < ∞`: `r^{τ}` is close to `1` uniformly when
`κ^{τ}` is bounded and `r ↓ 1` (it replaces Jensen's inequality on p. 374). -/
theorem tpow_le_one_add {r κ : ℝ≥0∞} (hr : 1 < r) (hrκ : r ≤ κ) (hκ : κ ≠ ∞) (t : WithTop ℕ) :
    tpow r t ≤ 1 + (r - 1) / (κ - 1) * tpow κ t := by
  have hκ1 : 1 < κ := hr.trans_le hrκ
  have hκ0 : κ - 1 ≠ 0 := (tsub_pos_iff_lt.2 hκ1).ne'
  have hκt : κ - 1 ≠ ∞ := ENNReal.sub_ne_top hκ
  set Sr := ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < t}.indicator (fun k => r ^ k) k
  set Sκ := ∑' k : ℕ, {k : ℕ | (k : WithTop ℕ) < t}.indicator (fun k => κ ^ k) k
  have hS : Sr ≤ Sκ := ENNReal.tsum_le_tsum fun k =>
    indicator_le_indicator (pow_le_pow_left₀ zero_le hrκ k)
  rw [tpow_eq_one_add hr, tpow_eq_one_add hκ1]
  refine add_le_add le_rfl ?_
  calc (r - 1) * Sr ≤ (r - 1) * Sκ := mul_le_mul' le_rfl hS
    _ = (r - 1) / (κ - 1) * ((κ - 1) * Sκ) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hκ0 hκt]
    _ ≤ (r - 1) / (κ - 1) * (1 + (κ - 1) * Sκ) := mul_le_mul' le_rfl le_add_self

/-! ### The generating functions of hitting times -/

/-- **`E_x[r^{τ_A}]`**, MT (15.2), p. 362 (with `r^∞ = ∞`). -/
noncomputable def kendallMoment (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (r : ℝ≥0∞)
    (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, tpow r (firstReturn A ω) ∂pathKernel P x

/-- **`E_x[Σ_{k=0}^{τ_B − 1} f(Φ_k) rᵏ]`**, MT (15.22) and (15.36), pp. 373 and 381. -/
noncomputable def geomSum (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => r ^ k * f (ω k)) ω ∂pathKernel P x

/-- **`U_B^{(r)}(x, f) = E_x[Σ_{k=1}^{τ_B} f(Φ_k) rᵏ]`**, MT (15.12) and (15.23), pp. 365 and
373. -/
noncomputable def geomTaboo (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, sumBefore (firstReturn B) (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω ∂pathKernel P x

/-- **`G_B^{(r)}(x, f) = E_x[Σ_{k=0}^{σ_B} f(Φ_k) rᵏ]`**, MT (15.29), p. 376. -/
noncomputable def geomG (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ ω, sumBefore (fun ω => firstHit B ω + 1) (fun k ω => r ^ k * f (ω k)) ω ∂pathKernel P x

/-- The path sum `Σ_{k<τ_B} f(Φ_k) rᵏ` is measurable. -/
theorem measurable_sumBefore_geom {B : Set X} (hB : MeasurableSet B) (r : ℝ≥0∞) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (sumBefore (firstReturn B) fun k (ω : ℕ → X) => r ^ k * f (ω k)) :=
  measurable_sumBefore (measurableSet_lt_firstReturn hB) fun k =>
    measurable_const.mul (hf.comp (measurable_pi_apply k))

/-- The path sum `Σ_{k=1}^{τ_B} f(Φ_k) rᵏ` is measurable. -/
theorem measurable_sumBefore_geomTaboo {B : Set X} (hB : MeasurableSet B) (r : ℝ≥0∞)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (sumBefore (firstReturn B) fun k (ω : ℕ → X) => r ^ (k + 1) * f (ω (k + 1))) :=
  measurable_sumBefore (measurableSet_lt_firstReturn hB) fun k =>
    measurable_const.mul (hf.comp (measurable_pi_apply (k + 1)))

/-- The path sum `Σ_{k=0}^{σ_B} f(Φ_k) rᵏ` is measurable. -/
theorem measurable_sumBefore_geomG {B : Set X} (hB : MeasurableSet B) (r : ℝ≥0∞)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (sumBefore (fun ω : ℕ → X => firstHit B ω + 1) fun k ω => r ^ k * f (ω k)) :=
  measurable_sumBefore (measurableSet_lt_firstHit_add_one hB) fun k =>
    measurable_const.mul (hf.comp (measurable_pi_apply k))

/-- `x ↦ E_x[r^{τ_A}]` is measurable (`r > 1`). -/
theorem measurable_kendallMoment (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : 1 < r) : Measurable (kendallMoment P A r) :=
  (measurable_tpow_comp (measurableSet_lt_firstReturn hA) hr).lintegral_kernel

/-- `x ↦ E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` is measurable. -/
theorem measurable_geomSum (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (geomSum P B r f) :=
  (measurable_sumBefore_geom hB r hf).lintegral_kernel

/-- `x ↦ U_B^{(r)}(x, f)` is measurable. -/
theorem measurable_geomTaboo (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (geomTaboo P B r f) :=
  (measurable_sumBefore_geomTaboo hB r hf).lintegral_kernel

/-- `x ↦ G_B^{(r)}(x, f)` is measurable. -/
theorem measurable_geomG (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (geomG P B r f) :=
  (measurable_sumBefore_geomG hB r hf).lintegral_kernel

/-! ### The case `r = 1` -/

/-- At `r = 1`, `geomSum` is the sum of Chapter 14: `E_x[Σ_{k<τ_B} f(Φ_k)]`. -/
theorem geomSum_one (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (f : X → ℝ≥0∞) :
    geomSum P B 1 f = fSumReturn P B f := by
  funext x
  simp only [geomSum, fSumReturn, one_pow, one_mul]

/-- At `r = 1`, `U_B^{(1)} = U_B`. -/
theorem geomTaboo_one (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (f : X → ℝ≥0∞) :
    geomTaboo P B 1 f = tabooPotFn P B f := by
  funext x
  simp only [geomTaboo, tabooPotFn, one_pow, one_mul]

/-- At `r = 1`, `G_B^{(1)} = G_B`. -/
theorem geomG_one (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (f : X → ℝ≥0∞) :
    geomG P B 1 f = gKernelFn P B f := by
  funext x
  simp only [geomG, gKernelFn, one_pow, one_mul]

/-! ### Monotonicity -/

/-- `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` is monotone in `r`. -/
theorem geomSum_mono_r (P : Kernel X X) [IsMarkovKernel P] (B : Set X) {r s : ℝ≥0∞}
    (hrs : r ≤ s) (f : X → ℝ≥0∞) (x : X) : geomSum P B r f x ≤ geomSum P B s f x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k _ =>
    mul_le_mul' (pow_le_pow_left₀ zero_le hrs k) le_rfl) ω

/-- `U_B^{(r)}(x, f)` is monotone in `r`. -/
theorem geomTaboo_mono_r (P : Kernel X X) [IsMarkovKernel P] (B : Set X) {r s : ℝ≥0∞}
    (hrs : r ≤ s) (f : X → ℝ≥0∞) (x : X) : geomTaboo P B r f x ≤ geomTaboo P B s f x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k _ =>
    mul_le_mul' (pow_le_pow_left₀ zero_le hrs (k + 1)) le_rfl) ω

/-- `G_B^{(r)}(x, f)` is monotone in `r`. -/
theorem geomG_mono_r (P : Kernel X X) [IsMarkovKernel P] (B : Set X) {r s : ℝ≥0∞}
    (hrs : r ≤ s) (f : X → ℝ≥0∞) (x : X) : geomG P B r f x ≤ geomG P B s f x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k _ =>
    mul_le_mul' (pow_le_pow_left₀ zero_le hrs k) le_rfl) ω

/-- `E_x[r^{τ_A}]` is monotone in `r`. -/
theorem kendallMoment_mono_r (P : Kernel X X) [IsMarkovKernel P] (A : Set X) {r s : ℝ≥0∞}
    (hrs : r ≤ s) (x : X) : kendallMoment P A r x ≤ kendallMoment P A s x :=
  lintegral_mono fun _ => tpow_mono_left hrs _

/-- `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` is monotone in `f`. -/
theorem geomSum_mono_f (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    {f g : X → ℝ≥0∞} (hfg : f ≤ g) (x : X) : geomSum P B r f x ≤ geomSum P B r g x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k ω => mul_le_mul' le_rfl (hfg (ω k))) ω

/-- `U_B^{(r)}(x, f)` is monotone in `f`. -/
theorem geomTaboo_mono_f (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    {f g : X → ℝ≥0∞} (hfg : f ≤ g) (x : X) : geomTaboo P B r f x ≤ geomTaboo P B r g x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k ω => mul_le_mul' le_rfl (hfg (ω (k + 1)))) ω

/-- `G_B^{(r)}(x, f)` is monotone in `f`. -/
theorem geomG_mono_f (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    {f g : X → ℝ≥0∞} (hfg : f ≤ g) (x : X) : geomG P B r f x ≤ geomG P B r g x :=
  lintegral_mono fun ω => sumBefore_mono _ (fun k ω => mul_le_mul' le_rfl (hfg (ω k))) ω

/-- `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` decreases when `B` increases. -/
theorem geomSum_anti_set (P : Kernel X X) [IsMarkovKernel P] {B B' : Set X} (h : B ⊆ B')
    (r : ℝ≥0∞) (f : X → ℝ≥0∞) (x : X) : geomSum P B' r f x ≤ geomSum P B r f x :=
  lintegral_mono fun ω => sumBefore_mono_time (firstReturn_anti h) _ ω

/-- `E_x[Σ_{k<τ_B} c f(Φ_k) rᵏ] = c E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]`. -/
theorem geomSum_const_mul (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (r c : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    geomSum P B r (fun y => c * f y) x = c * geomSum P B r f x := by
  rw [geomSum, geomSum, ← lintegral_const_mul c (measurable_sumBefore_geom hB r hf)]
  refine lintegral_congr fun ω => ?_
  rw [← sumBefore_const_mul]
  exact sumBefore_congr _ fun k _ => by ring

/-! ### Identities -/

/-- **The first step, (15.31)**: `U_B^{(r)}(x, f) = r ∫ P(x, dy) G_B^{(r)}(y, f)`. -/
theorem geomTaboo_eq (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    geomTaboo P B r f x = r * ∫⁻ y, geomG P B r f y ∂P x := by
  have hm := measurable_sumBefore_geomG hB r hf
  have hm' : Measurable fun ω : ℕ → X => sumBefore (fun ω => firstHit B ω + 1)
      (fun k ω => r ^ k * f (ω k)) (shift 1 ω) := hm.comp (measurable_shift 1)
  unfold geomG geomTaboo
  rw [← lintegral_shift_one P x hm, ← lintegral_const_mul r hm']
  refine lintegral_congr fun ω => ?_
  have h := firstReturn_eq_firstHit_shift B ω
  rw [← sumBefore_const_mul]
  unfold sumBefore
  refine tsum_congr fun k => ?_
  simp only [Set.indicator_apply, mem_ofPred_eq, ← h, shift]
  split_ifs
  · rw [add_comm 1 k, pow_succ]; ring
  · rfl

/-- **`G_B^{(r)}(x, f) = f(x) + 1_{Bᶜ}(x) U_B^{(r)}(x, f)`** (MT p. 376). -/
theorem geomG_eq (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    geomG P B r f x = f x + Bᶜ.indicator (geomTaboo P B r f) x := by
  have := isMarkovKernel_pathKernel P
  have hm : MeasurableSet {ω : ℕ → X | ω 0 ∈ B} := measurable_pi_apply 0 hB
  unfold geomG
  simp_rw [sumBefore_add_one, pow_zero, one_mul]
  rw [lintegral_add_left (f := fun ω : ℕ → X => f (ω 0)) (hf.comp (measurable_pi_apply 0)),
    lintegral_coord_zero P x hf]
  refine congrArg (f x + ·) ?_
  by_cases hx : x ∈ B
  · have hnull : pathKernel P x {ω | ω 0 ∈ B}ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hm, pathKernel_zero_mem P x hB, indicator_of_mem hx,
        Pi.one_apply]
    rw [indicator_of_notMem (show x ∉ Bᶜ from fun h => h hx)]
    have hae : (fun ω => sumBefore (firstHit B)
        (fun k (ω : ℕ → X) => r ^ (k + 1) * f (ω (k + 1))) ω) =ᵐ[pathKernel P x] fun _ => 0 := by
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro h0
      apply hω
      change sumBefore (firstHit B) (fun k (ω : ℕ → X) => r ^ (k + 1) * f (ω (k + 1))) ω = 0
      rw [sumBefore_eq_of_eq (τ' := fun _ => WithTop.some 0) ((firstHit_eq_zero_iff B ω).2 h0)]
      simp [sumBefore]
    rw [lintegral_congr_ae hae, lintegral_zero]
  · have hnull : pathKernel P x {ω | ω 0 ∈ B} = 0 := by
      rw [pathKernel_zero_mem P x hB, indicator_of_notMem hx]
    rw [indicator_of_mem (show x ∈ Bᶜ from hx), geomTaboo]
    refine lintegral_congr_ae (measure_mono_null (fun ω hω => ?_) hnull)
    by_contra h0
    exact hω (sumBefore_eq_of_eq (firstHit_eq_firstReturn B (show ω 0 ∉ B from h0)) _)

/-- On `B`, `G_B^{(r)}(x, f) = f(x)`. -/
theorem geomG_of_mem (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) {x : X} (hx : x ∈ B) :
    geomG P B r f x = f x := by
  rw [geomG_eq P hB r hf, indicator_of_notMem (show x ∉ Bᶜ from fun h => h hx), add_zero]

/-- `f(x) ≤ G_B^{(r)}(x, f)`. -/
theorem le_geomG (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) : f x ≤ geomG P B r f x := by
  rw [geomG_eq P hB r hf]; exact le_self_add

/-- `G_B^{(r)}(x, f) ≤ f(x) + U_B^{(r)}(x, f)`. -/
theorem geomG_le (P : Kernel X X) [IsMarkovKernel P] {B : Set X} (hB : MeasurableSet B)
    (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    geomG P B r f x ≤ f x + geomTaboo P B r f x := by
  rw [geomG_eq P hB r hf]; exact add_le_add le_rfl (indicator_le_self _ _ x)

/-- **`E_x[r^{τ_B}] = 1 + (r − 1) E_x[Σ_{k<τ_B} rᵏ]`** for `r > 1`. -/
theorem kendallMoment_eq_one_add (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {r : ℝ≥0∞} (hr : 1 < r) (x : X) :
    kendallMoment P B r x = 1 + (r - 1) * geomSum P B r (fun _ => 1) x := by
  have := isMarkovKernel_pathKernel P
  have hm : Measurable (sumBefore (firstReturn B) fun k (_ : ℕ → X) => r ^ k) :=
    measurable_sumBefore (measurableSet_lt_firstReturn hB) fun _ => measurable_const
  have h : ∀ ω, tpow r (firstReturn B ω) =
      1 + (r - 1) * sumBefore (firstReturn B) (fun k _ => r ^ k) ω := fun ω => by
    rw [tpow_eq_one_add hr, sumBefore_eq_tsum]
  rw [kendallMoment, lintegral_congr h, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul _ hm, geomSum]
  simp_rw [mul_one]

/-- `E_x[r^{τ_B}] ≤ 1 + (r − 1) E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` for `f ≥ 1`. -/
theorem kendallMoment_le_one_add (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {r : ℝ≥0∞} (hr : 1 < r) {f : X → ℝ≥0∞} (hf1 : ∀ y, 1 ≤ f y)
    (x : X) : kendallMoment P B r x ≤ 1 + (r - 1) * geomSum P B r f x := by
  rw [kendallMoment_eq_one_add P hB hr]
  exact add_le_add le_rfl (mul_le_mul' le_rfl (geomSum_mono_f P B r hf1 x))

omit [MeasurableSpace X] in
/-- `Σ_{k<∞} F_k = Σ_k F_k`. -/
theorem sumBefore_top_eq {Ω : Type*} (F : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    sumBefore (fun _ => (⊤ : WithTop ℕ)) F ω = ∑' k, F k ω := by
  rw [sumBefore_eq_tsum]
  exact tsum_congr fun k => indicator_of_mem
    (show k ∈ {k : ℕ | (k : WithTop ℕ) < ⊤} from WithTop.coe_lt_top k) _

omit [MeasurableSpace X] in
/-- Pathwise: `r^{τ_B} ≤ Σ_{k=1}^{τ_B} f(Φ_k) rᵏ` for `r, f ≥ 1`. -/
theorem tpow_le_sumBefore_geomTaboo (B : Set X) {r : ℝ≥0∞} (hr : 1 ≤ r) {f : X → ℝ≥0∞}
    (hf1 : ∀ y, 1 ≤ f y) (ω : ℕ → X) :
    tpow r (firstReturn B ω) ≤
      sumBefore (firstReturn B) (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω := by
  cases h : firstReturn B ω with
  | top =>
    rw [tpow_top, sumBefore_eq_of_eq (τ' := fun _ => ⊤) h, sumBefore_top_eq]
    refine (tsum_eq_top_of_one_le fun k => ?_).symm.le
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) (hf1 _)
  | coe t =>
    have ht1 : 1 ≤ t := by
      have := one_le_firstReturn B ω; rw [h] at this; exact WithTop.coe_le_coe.1 this
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [tpow_some, sumBefore_of_eq' h]
    calc r ^ (s + 1) ≤ r ^ (s + 1) * f (ω (s + 1)) := le_mul_of_one_le_right' (hf1 _)
      _ ≤ ∑ k ∈ range (s + 1), r ^ (k + 1) * f (ω (k + 1)) :=
          Finset.single_le_sum (f := fun k => r ^ (k + 1) * f (ω (k + 1))) (fun _ _ => zero_le)
            (Finset.self_mem_range_succ s)

/-- **`E_x[r^{τ_B}] ≤ U_B^{(r)}(x, f)`** for `r, f ≥ 1` (MT p. 368). -/
theorem kendallMoment_le_geomTaboo (P : Kernel X X) [IsMarkovKernel P] (B : Set X)
    {r : ℝ≥0∞} (hr : 1 ≤ r) {f : X → ℝ≥0∞} (hf1 : ∀ y, 1 ≤ f y) (x : X) :
    kendallMoment P B r x ≤ geomTaboo P B r f x :=
  lintegral_mono fun ω => tpow_le_sumBefore_geomTaboo B hr hf1 ω

omit [MeasurableSpace X] in
/-- Pathwise: `Σ_{k<τ_B} f(Φ_k) rᵏ ≤ f(Φ₀) + Σ_{k=1}^{τ_B} f(Φ_k) rᵏ`. -/
theorem sumBefore_geom_le_add (B : Set X) (r : ℝ≥0∞) (f : X → ℝ≥0∞) (ω : ℕ → X) :
    sumBefore (firstReturn B) (fun k ω => r ^ k * f (ω k)) ω ≤
      f (ω 0) + sumBefore (firstReturn B) (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω := by
  rw [sumBefore_eq_tsum, sumBefore_eq_tsum, tsum_eq_zero_add' ENNReal.summable]
  refine add_le_add ?_ (ENNReal.tsum_le_tsum fun k => ?_)
  · refine (indicator_le_self _ _ 0).trans (le_of_eq ?_)
    simp only [pow_zero, one_mul]
  · by_cases hk : ((k + 1 : ℕ) : WithTop ℕ) < firstReturn B ω
    · have hk' : (k : WithTop ℕ) < firstReturn B ω :=
        lt_of_le_of_lt (by exact_mod_cast Nat.le_succ k) hk
      rw [indicator_of_mem (show k + 1 ∈ {k : ℕ | (k : WithTop ℕ) < firstReturn B ω} from hk),
        indicator_of_mem (show k ∈ {k : ℕ | (k : WithTop ℕ) < firstReturn B ω} from hk')]
    · rw [indicator_of_notMem (show k + 1 ∉ {k : ℕ | (k : WithTop ℕ) < firstReturn B ω} from hk)]
      exact zero_le

/-- **`E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] ≤ f(x) + U_B^{(r)}(x, f)`**. -/
theorem geomSum_le_add_geomTaboo (P : Kernel X X) [IsMarkovKernel P] (B : Set X) (r : ℝ≥0∞)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    geomSum P B r f x ≤ f x + geomTaboo P B r f x := by
  have := isMarkovKernel_pathKernel P
  rw [← lintegral_coord_zero P x hf, geomTaboo,
    ← lintegral_add_left (f := fun ω : ℕ → X => f (ω 0)) (hf.comp (measurable_pi_apply 0))]
  exact lintegral_mono fun ω => sumBefore_geom_le_add B r f ω

omit [MeasurableSpace X] in
/-- Pathwise: `Σ_{k=1}^{τ_B} f(Φ_k) rᵏ ≤ Σ_{k<τ_B} f(Φ_k) rᵏ + M r^{τ_B}` when `f ≤ M` on `B`. -/
theorem sumBefore_geomTaboo_le (B : Set X) {r : ℝ≥0∞} (f : X → ℝ≥0∞) {M : ℝ≥0∞}
    (hM : ∀ y ∈ B, f y ≤ M) (ω : ℕ → X) :
    sumBefore (firstReturn B) (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω ≤
      sumBefore (firstReturn B) (fun k ω => r ^ k * f (ω k)) ω + M * tpow r (firstReturn B ω) := by
  cases h : firstReturn B ω with
  | top =>
    refine le_trans ?_ le_self_add
    rw [sumBefore_eq_of_eq (τ' := fun _ => ⊤) h, sumBefore_eq_of_eq (τ' := fun _ => ⊤) h,
      sumBefore_top_eq, sumBefore_top_eq,
      tsum_eq_zero_add' (f := fun k : ℕ => r ^ k * f (ω k)) ENNReal.summable]
    exact le_add_self
  | coe t =>
    rw [sumBefore_of_eq' h, sumBefore_of_eq' h, tpow_some]
    have hmem : ω t ∈ B := mem_of_firstReturn_eq h
    calc ∑ k ∈ range t, r ^ (k + 1) * f (ω (k + 1))
        ≤ ∑ k ∈ range (t + 1), r ^ k * f (ω k) := by
          rw [Finset.sum_range_succ']; exact le_self_add
      _ = ∑ k ∈ range t, r ^ k * f (ω k) + r ^ t * f (ω t) := Finset.sum_range_succ _ _
      _ ≤ ∑ k ∈ range t, r ^ k * f (ω k) + M * r ^ t := by
          rw [mul_comm M]; exact add_le_add le_rfl (mul_le_mul' le_rfl (hM _ hmem))

/-- **`U_B^{(r)}(x, f) ≤ E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] + M E_x[r^{τ_B}]`** when `f ≤ M` on `B`
(`r > 1`). -/
theorem geomTaboo_le_geomSum_add (P : Kernel X X) [IsMarkovKernel P] {B : Set X}
    (hB : MeasurableSet B) {r : ℝ≥0∞} (hr : 1 < r) {f : X → ℝ≥0∞} (hf : Measurable f)
    {M : ℝ≥0∞} (hM : ∀ y ∈ B, f y ≤ M) (x : X) :
    geomTaboo P B r f x ≤ geomSum P B r f x + M * kendallMoment P B r x := by
  rw [geomTaboo, geomSum, kendallMoment, ← lintegral_const_mul M
    (measurable_tpow_comp (measurableSet_lt_firstReturn hB) hr),
    ← lintegral_add_left (measurable_sumBefore_geom hB r hf)]
  exact lintegral_mono fun ω => sumBefore_geomTaboo_le B f hM ω

/-! ### The strong Markov property with geometric weights -/

/-- **The strong Markov property with a weight depending on `ζ`**: for a stopping time `ζ`, a set
`A` with `A ∩ {ζ = n} ∈ 𝓕ₙ` for all `n`, weights `w` and measurable `H ≥ 0`,
`E_μ[w(ζ) H ∘ θ^ζ; A ∩ {ζ < ∞}] = E_μ[w(ζ) E_{Φ_ζ}[H]; A ∩ {ζ < ∞}]`. -/
theorem lintegral_weight_shiftAt (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {τ : (ℕ → X) → WithTop ℕ} {A : Set (ℕ → X)}
    (hA : ∀ n : ℕ, MeasurableSet[natFilt n] (A ∩ {ω | τ ω = n})) (w : ℕ → ℝ≥0∞)
    {H : (ℕ → X) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, w (τ ω).untopA * H (shiftAt τ ω) ∂pathMeasure P μ =
      ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, w (τ ω).untopA *
        ∫⁻ ω', H ω' ∂pathKernel P (stoppedState τ ω) ∂pathMeasure P μ := by
  have := isMarkovKernel_pathKernel P
  have hm : ∀ n : ℕ, MeasurableSet (A ∩ {ω | τ ω = n}) := fun n =>
    (natFilt (X := X)).le n _ (hA n)
  rw [inter_ne_top_eq_iUnion, lintegral_iUnion hm (pairwise_disjoint_inter_eq τ A),
    lintegral_iUnion hm (pairwise_disjoint_inter_eq τ A)]
  refine tsum_congr fun n => ?_
  have hun : ∀ ω ∈ A ∩ {ω | τ ω = n}, (τ ω).untopA = n := fun ω hω => by
    rw [show τ ω = (n : WithTop ℕ) from hω.2]; rfl
  calc ∫⁻ ω in A ∩ {ω | τ ω = n}, w (τ ω).untopA * H (shiftAt τ ω) ∂pathMeasure P μ
      = ∫⁻ ω in A ∩ {ω | τ ω = n}, w n * H (shift n ω) ∂pathMeasure P μ :=
        setLIntegral_congr_fun (hm n) fun ω hω => by rw [hun ω hω, shiftAt_of_eq hω.2]
    _ = w n * ∫⁻ ω in A ∩ {ω | τ ω = n}, H (shift n ω) ∂pathMeasure P μ :=
        lintegral_const_mul _ (hH.comp (measurable_shift n))
    _ = w n * ∫⁻ ω in A ∩ {ω | τ ω = n}, ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ := by
        rw [markov_lintegral P μ (hA n) hH]
    _ = ∫⁻ ω in A ∩ {ω | τ ω = n}, w n * ∫⁻ ω', H ω' ∂pathKernel P (ω n) ∂pathMeasure P μ :=
        (lintegral_const_mul _ (hH.lintegral_kernel.comp (measurable_pi_apply n))).symm
    _ = _ := setLIntegral_congr_fun (hm n) fun ω hω => by
        rw [hun ω hω, stoppedState_of_eq hω.2]

omit [MeasurableSpace X] in
/-- **Pathwise splitting with weights.** If `T ω ≤ t + T(θᵗω)` and `G_{t+j}(ω) = c G_j(θᵗω)`,
then `Σ_{k<T} G_k(ω) ≤ Σ_{k<t} G_k(ω) + c Σ_{k<T} G_k(θᵗω)`. -/
theorem sumBefore_le_shift_weighted {T : (ℕ → X) → WithTop ℕ} {G : ℕ → (ℕ → X) → ℝ≥0∞}
    {c : ℝ≥0∞} {ω : ℕ → X} {t : ℕ} (hT : T ω ≤ (t : WithTop ℕ) + T (shift t ω))
    (hG : ∀ j, G (t + j) ω = c * G j (shift t ω)) :
    sumBefore T G ω ≤ ∑ k ∈ range t, G k ω + c * sumBefore T G (shift t ω) := by
  have h1 := sumBefore_mono_time (τ := fun _ => T ω)
    (τ' := fun _ => (t : WithTop ℕ) + T (shift t ω)) (fun _ => hT) (fun k (_ : ℕ → X) => G k ω) ω
  rw [sumBefore_eq_tsum, sumBefore_eq_tsum, tsum_indicator_lt_add] at h1
  rw [sumBefore_eq_tsum T G ω, sumBefore_eq_tsum T G (shift t ω), ← ENNReal.tsum_mul_left]
  refine h1.trans (add_le_add le_rfl (le_of_eq (tsum_congr fun j => ?_)))
  by_cases hj : (j : WithTop ℕ) < T (shift t ω)
  · rw [indicator_of_mem (show j ∈ {j : ℕ | (j : WithTop ℕ) < T (shift t ω)} from hj),
      indicator_of_mem (show j ∈ {j : ℕ | (j : WithTop ℕ) < T (shift t ω)} from hj), hG]
  · rw [indicator_of_notMem (show j ∉ {j : ℕ | (j : WithTop ℕ) < T (shift t ω)} from hj),
      indicator_of_notMem (show j ∉ {j : ℕ | (j : WithTop ℕ) < T (shift t ω)} from hj), mul_zero]

/-- **The strong Markov bound for weighted sums.** Let `ζ` be a stopping time, `T` a random time
with `T ≤ t + T ∘ θᵗ`, and `G` a weighted process with `G_{t+j} = w(t) G_j ∘ θᵗ`. Then
`E_x[Σ_{k<T} G_k] ≤ E_x[Σ_{k<ζ} G_k] + E_x[w(ζ) E_{Φ_ζ}[Σ_{k<T} G_k]; ζ < ∞]`. -/
theorem lintegral_sumBefore_le_weighted (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {ζ : (ℕ → X) → WithTop ℕ} (hζ : IsStoppingTime (natFilt (X := X)) ζ)
    {T : (ℕ → X) → WithTop ℕ} (hTm : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < T ω})
    (hT : ∀ ω (t : ℕ), T ω ≤ (t : WithTop ℕ) + T (shift t ω)) {G : ℕ → (ℕ → X) → ℝ≥0∞}
    (hGm : ∀ k, Measurable (G k)) {w : ℕ → ℝ≥0∞}
    (hG : ∀ ω (t j : ℕ), G (t + j) ω = w t * G j (shift t ω)) :
    ∫⁻ ω, sumBefore T G ω ∂pathKernel P x ≤ ∫⁻ ω, sumBefore ζ G ω ∂pathKernel P x +
      ∫⁻ ω in {ω | ζ ω ≠ ⊤}, w (ζ ω).untopA *
        ∫⁻ ω', sumBefore T G ω' ∂pathKernel P (stoppedState ζ ω) ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have hH : Measurable (sumBefore T G) := measurable_sumBefore hTm hGm
  have hζm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < ζ ω} :=
    fun n => (natFilt (X := X)).le n _ (measurableSet_lt_of_isStoppingTime hζ n)
  have hS : Measurable (sumBefore ζ G) := measurable_sumBefore hζm hGm
  have hT0 := measurableSet_ne_top hζ
  have hpt : ∀ ω, sumBefore T G ω ≤ sumBefore ζ G ω +
      {ω | ζ ω ≠ ⊤}.indicator (fun ω => w (ζ ω).untopA * sumBefore T G (shiftAt ζ ω)) ω :=
    fun ω => by
    cases h : ζ ω with
    | top =>
      rw [indicator_of_notMem (show ω ∉ {ω | ζ ω ≠ ⊤} from by simp [h]), add_zero,
        sumBefore_eq_of_eq (τ := ζ) (τ' := fun _ => ⊤) h]
      exact sumBefore_le_top T _ ω
    | coe t =>
      rw [indicator_of_mem (show ω ∈ {ω | ζ ω ≠ ⊤} from by simp [h]), shiftAt_of_eq h,
        sumBefore_of_eq' h]
      have ht : (ζ ω).untopA = t := by rw [h]; rfl
      rw [ht]
      exact sumBefore_le_shift_weighted (hT ω t) (hG ω t)
  have hA : ∀ n : ℕ, MeasurableSet[natFilt n] (univ ∩ {ω : ℕ → X | ζ ω = n}) := fun n => by
    rw [univ_inter]; exact hζ.measurableSet_eq_of_countable n
  have h := lintegral_weight_shiftAt P (Measure.dirac x) hA w hH
  rw [pathMeasure_dirac, univ_inter] at h
  calc ∫⁻ ω, sumBefore T G ω ∂pathKernel P x
      ≤ ∫⁻ ω, (sumBefore ζ G ω + {ω | ζ ω ≠ ⊤}.indicator
          (fun ω => w (ζ ω).untopA * sumBefore T G (shiftAt ζ ω)) ω) ∂pathKernel P x :=
        lintegral_mono hpt
    _ = ∫⁻ ω, sumBefore ζ G ω ∂pathKernel P x + ∫⁻ ω in {ω | ζ ω ≠ ⊤},
          w (ζ ω).untopA * sumBefore T G (shiftAt ζ ω) ∂pathKernel P x := by
        rw [lintegral_add_left hS, lintegral_indicator hT0]
    _ = _ := by rw [h]

omit [MeasurableSpace X] in
/-- `G_{t+j}(ω) = rᵗ G_j(θᵗω)` for `G_k(ω) = rᵏ f(ω_k)`. -/
theorem geom_shift_weight (r : ℝ≥0∞) (f : X → ℝ≥0∞) (ω : ℕ → X) (t j : ℕ) :
    r ^ (t + j) * f (ω (t + j)) = r ^ t * (r ^ j * f (shift t ω j)) := by
  rw [pow_add, mul_assoc]; rfl

omit [MeasurableSpace X] in
/-- `G_{t+j}(ω) = rᵗ G_j(θᵗω)` for `G_k(ω) = r^{k+1} f(ω_{k+1})`. -/
theorem geomTaboo_shift_weight (r : ℝ≥0∞) (f : X → ℝ≥0∞) (ω : ℕ → X) (t j : ℕ) :
    r ^ (t + j + 1) * f (ω (t + j + 1)) = r ^ t * (r ^ (j + 1) * f (shift t ω (j + 1))) := by
  rw [add_assoc, pow_add, mul_assoc]; rfl

/-- **The strong Markov bound for `U^{(r)}`** at a stopping time `ζ`. -/
theorem geomTaboo_le_stopping (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {ζ : (ℕ → X) → WithTop ℕ} (hζ : IsStoppingTime (natFilt (X := X)) ζ) {B : Set X}
    (hB : MeasurableSet B) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    geomTaboo P B r f x ≤
      ∫⁻ ω, sumBefore ζ (fun k ω => r ^ (k + 1) * f (ω (k + 1))) ω ∂pathKernel P x +
      ∫⁻ ω in {ω | ζ ω ≠ ⊤}, tpow r (ζ ω) * geomTaboo P B r f (stoppedState ζ ω)
        ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have h := lintegral_sumBefore_le_weighted P x hζ (measurableSet_lt_firstReturn hB)
    (firstReturn_le_add_shift B) (G := fun k ω => r ^ (k + 1) * f (ω (k + 1)))
    (fun k => measurable_const.mul (hf.comp (measurable_pi_apply (k + 1)))) (w := fun t => r ^ t)
    (fun ω t j => geomTaboo_shift_weight r f ω t j)
  refine h.trans (add_le_add le_rfl (le_of_eq (setLIntegral_congr_fun
    (measurableSet_ne_top hζ) fun ω hω => ?_)))
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
  rw [← ht]
  rfl

/-- **The strong Markov bound for `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]`** at a stopping time `ζ`. -/
theorem geomSum_le_stopping (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {ζ : (ℕ → X) → WithTop ℕ} (hζ : IsStoppingTime (natFilt (X := X)) ζ) {B : Set X}
    (hB : MeasurableSet B) (r : ℝ≥0∞) {f : X → ℝ≥0∞} (hf : Measurable f) :
    geomSum P B r f x ≤
      ∫⁻ ω, sumBefore ζ (fun k ω => r ^ k * f (ω k)) ω ∂pathKernel P x +
      ∫⁻ ω in {ω | ζ ω ≠ ⊤}, tpow r (ζ ω) * geomSum P B r f (stoppedState ζ ω)
        ∂pathKernel P x := by
  have := isMarkovKernel_pathKernel P
  have h := lintegral_sumBefore_le_weighted P x hζ (measurableSet_lt_firstReturn hB)
    (firstReturn_le_add_shift B) (G := fun k ω => r ^ k * f (ω k))
    (fun k => measurable_const.mul (hf.comp (measurable_pi_apply k))) (w := fun t => r ^ t)
    (fun ω t j => geom_shift_weight r f ω t j)
  refine h.trans (add_le_add le_rfl (le_of_eq (setLIntegral_congr_fun
    (measurableSet_ne_top hζ) fun ω hω => ?_)))
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
  rw [← ht]
  rfl

/-- `∫_{ζ<∞} rᶻ g ≤ M E_x[rᶻ]` when `g ≤ M` on `{ζ < ∞}`. -/
theorem setLIntegral_tpow_mul_le (P : Kernel X X) [IsMarkovKernel P] (x : X)
    {ζ : (ℕ → X) → WithTop ℕ} (hζ : IsStoppingTime (natFilt (X := X)) ζ)
    {r : ℝ≥0∞} (hr : 1 < r) {g : (ℕ → X) → ℝ≥0∞} {M : ℝ≥0∞}
    (hg : ∀ ω, ζ ω ≠ ⊤ → g ω ≤ M) :
    ∫⁻ ω in {ω | ζ ω ≠ ⊤}, tpow r (ζ ω) * g ω ∂pathKernel P x ≤
      M * ∫⁻ ω, tpow r (ζ ω) ∂pathKernel P x := by
  have hζm : ∀ n : ℕ, MeasurableSet {ω : ℕ → X | (n : WithTop ℕ) < ζ ω} :=
    fun n => (natFilt (X := X)).le n _ (measurableSet_lt_of_isStoppingTime hζ n)
  have hm := measurable_tpow_comp hζm hr
  calc ∫⁻ ω in {ω | ζ ω ≠ ⊤}, tpow r (ζ ω) * g ω ∂pathKernel P x
      ≤ ∫⁻ ω in {ω | ζ ω ≠ ⊤}, M * tpow r (ζ ω) ∂pathKernel P x :=
        setLIntegral_mono' (measurableSet_ne_top hζ) fun ω hω => by
          rw [mul_comm M]; exact mul_le_mul' le_rfl (hg ω hω)
    _ ≤ ∫⁻ ω, M * tpow r (ζ ω) ∂pathKernel P x := setLIntegral_le_lintegral _ _
    _ = M * ∫⁻ ω, tpow r (ζ ω) ∂pathKernel P x := lintegral_const_mul M hm

/-- **Through a set `A`**: if `U_B^{(r)} ≤ M` on `A`, then
`U_B^{(r)}(x, f) ≤ U_A^{(r)}(x, f) + M E_x[r^{τ_A}]` (the strong Markov property at `τ_A`). -/
theorem geomTaboo_le_add_mul (P : Kernel X X) [IsMarkovKernel P] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {r : ℝ≥0∞} (hr : 1 < r) {f : X → ℝ≥0∞}
    (hf : Measurable f) {M : ℝ≥0∞} (hM : ∀ y ∈ A, geomTaboo P B r f y ≤ M) (x : X) :
    geomTaboo P B r f x ≤ geomTaboo P A r f x + M * kendallMoment P A r x :=
  (geomTaboo_le_stopping P x (proposition_3_4_4 hA).1 hB r hf).trans
    (add_le_add le_rfl (setLIntegral_tpow_mul_le P x (proposition_3_4_4 hA).1 hr
      fun _ hω => hM _ (stoppedState_firstReturn_mem A hω)))

/-- **Through a set `A`**: if `E_y[Σ_{k<τ_B} f(Φ_k) rᵏ] ≤ M` on `A`, then
`E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] ≤ E_x[Σ_{k<τ_A} f(Φ_k) rᵏ] + M E_x[r^{τ_A}]`. -/
theorem geomSum_le_add_mul (P : Kernel X X) [IsMarkovKernel P] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {r : ℝ≥0∞} (hr : 1 < r) {f : X → ℝ≥0∞}
    (hf : Measurable f) {M : ℝ≥0∞} (hM : ∀ y ∈ A, geomSum P B r f y ≤ M) (x : X) :
    geomSum P B r f x ≤ geomSum P A r f x + M * kendallMoment P A r x :=
  (geomSum_le_stopping P x (proposition_3_4_4 hA).1 hB r hf).trans
    (add_le_add le_rfl (setLIntegral_tpow_mul_le P x (proposition_3_4_4 hA).1 hr
      fun _ hω => hM _ (stoppedState_firstReturn_mem A hω)))

end MeynTweedie.LimitTheorems
