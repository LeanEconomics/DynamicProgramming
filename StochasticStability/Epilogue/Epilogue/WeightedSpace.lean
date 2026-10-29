/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.VUniformErgodic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# The Banach space `L∞_V` and kernels as bounded operators (MT §20.1.1)

Meyn and Tweedie, §20.1.1, pp. 510–512. The spectral theory of the Epilogue takes place in the
complex Banach space `L∞_V` of measurable `f : X → ℂ` with `sup_x |f(x)|/V(x) < ∞`, on which a
kernel `P` with `PV ≤ cV` acts as a bounded operator. This module builds that space and the
operators.

* `bmSub`, `BM X`: the bounded measurable complex functions, a closed subspace of `ℓ^∞(X)`
  (`isClosed_bmSub`), hence a Banach space (`completeSpace_BM`). Multiplication by `V` is an
  isometry from `BM X` onto `L∞_V`, so `BM X` is `L∞_V` in the weighted coordinates `g = f/V`.
* `WeightOK V κ`: `V` measurable, `V ≥ 1`, `κV ≤ cV`. `kFun`, `kOp V κ`: the kernel acting on
  `BM X` as `g ↦ V⁻¹ κ(gV)`, a continuous linear map (`kOp_apply`).
* `kOp_comp`, `kOp_id`, `kOp_pow`: kernels compose as operators (`P ∘ₖ Q` acts as `Q̃ P̃`), and
  `Pⁿ` acts as the `n`-th power of `P̃`.
* `weightOK_const`, `kOp_const_apply`: the outer product `1 ⊗ π` (`Kernel.const X π`) acts as
  `g ↦ π(gV)/V`; `kOp_const_mul_kOp` (`ΠP = Π` for invariant `π`), `kOp_mul_kOp_const`
  (`PΠ = Π`), `kOp_const_mul_self` (`Π² = Π`).
* `norm_kOp_sub_le`, `fNorm_le_norm_kOp_sub`, `vErgDist_le_norm`, `norm_le_vErgDist`: the operator
  norm of `κ₁ − κ₂` on `L∞_V` and the distance `|||κ₁ − κ₂|||_V` of Chapter 16 are equivalent,
  `|||Pⁿ − 1 ⊗ π|||_V ≤ ‖P̃ⁿ − Π‖ ≤ 2 |||Pⁿ − 1 ⊗ π|||_V` (Lemma 16.1.1 for complex functions).
* `weightOK_of_vErgDist`: finite `|||P⁰ − 1 ⊗ π|||_V` and `|||P − 1 ⊗ π|||_V` make `V` admissible
  for `P` and `1 ⊗ π`.

**Hypotheses.** The book takes `L∞_V` complex without comment; the Chapter 16 norms use real test
functions, which costs the factor `2` in `norm_le_vErgDist`.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- The bounded measurable complex functions on `X`, a closed subspace of `ℓ^∞(X)`. -/
def bmSub (X : Type*) [MeasurableSpace X] : Submodule ℂ (lp (fun _ : X => ℂ) ∞) where
  carrier := {f | Measurable (⇑f : X → ℂ)}
  add_mem' {f g} hf hg := by
    change Measurable (⇑(f + g) : X → ℂ)
    rw [lp.coeFn_add]; exact hf.add hg
  zero_mem' := by
    change Measurable (⇑(0 : lp (fun _ : X => ℂ) ∞) : X → ℂ)
    rw [lp.coeFn_zero]; exact measurable_const
  smul_mem' c f hf := by
    change Measurable (⇑(c • f) : X → ℂ)
    rw [lp.coeFn_smul]; exact hf.const_smul c

/-- The Banach space of bounded measurable complex functions with the sup norm. -/
abbrev BM (X : Type*) [MeasurableSpace X] := ↥(bmSub X)

/-- The function underlying an element of `BM X`. -/
def bmFun (g : BM X) : X → ℂ := ⇑(g : lp (fun _ : X => ℂ) ∞)

/-- Elements of `BM X` are measurable. -/
theorem measurable_bmFun (g : BM X) : Measurable (bmFun g) := g.2

/-- `|g(x)| ≤ ‖g‖`. -/
theorem norm_bmFun_le (g : BM X) (x : X) : ‖bmFun g x‖ ≤ ‖g‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero (g : lp (fun _ : X => ℂ) ∞) x

/-- `‖g‖ ≤ C` when `|g| ≤ C`. -/
theorem norm_le_of_bmFun_le {g : BM X} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖bmFun g x‖ ≤ C) :
    ‖g‖ ≤ C :=
  lp.norm_le_of_forall_le (f := (g : lp (fun _ : X => ℂ) ∞)) hC h

/-- Extensionality in `BM X`. -/
theorem bm_ext {g h : BM X} (hgh : ∀ x, bmFun g x = bmFun h x) : g = h :=
  Subtype.ext (lp.ext (funext hgh))

/-- `bmFun` is additive. -/
theorem bmFun_add (g h : BM X) (x : X) : bmFun (g + h) x = bmFun g x + bmFun h x := by
  change ⇑((g : lp (fun _ : X => ℂ) ∞) + (h : lp (fun _ : X => ℂ) ∞)) x = _
  rw [lp.coeFn_add]; rfl

/-- `bmFun` commutes with scalars. -/
theorem bmFun_smul (c : ℂ) (g : BM X) (x : X) : bmFun (c • g) x = c * bmFun g x := by
  change ⇑(c • (g : lp (fun _ : X => ℂ) ∞)) x = _
  rw [lp.coeFn_smul]; rfl

/-- `bmFun` is subtractive. -/
theorem bmFun_sub (g h : BM X) (x : X) : bmFun (g - h) x = bmFun g x - bmFun h x := by
  change ⇑((g : lp (fun _ : X => ℂ) ∞) - (h : lp (fun _ : X => ℂ) ∞)) x = _
  rw [lp.coeFn_sub]; rfl

/-- `bmFun 0 = 0`. -/
theorem bmFun_zero (x : X) : bmFun (0 : BM X) x = 0 := by
  change ⇑(0 : lp (fun _ : X => ℂ) ∞) x = _
  rw [lp.coeFn_zero]; rfl

/-- The element of `BM X` given by a bounded measurable function. -/
noncomputable def mkBM (f : X → ℂ) (hm : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : BM X :=
  ⟨⟨f, memℓp_infty ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩⟩, hm⟩

/-- `bmFun (mkBM f) = f`. -/
theorem bmFun_mkBM (f : X → ℂ) (hm : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (x : X) :
    bmFun (mkBM f hm C hC) x = f x := rfl

/-- `BM X` is closed in `ℓ^∞(X)`: uniform limits of measurable functions are measurable. -/
theorem isClosed_bmSub : IsClosed (bmSub X : Set (lp (fun _ : X => ℂ) ∞)) := by
  refine IsSeqClosed.isClosed fun f g hf hlim => ?_
  change Measurable (⇑g : X → ℂ)
  refine measurable_of_tendsto_metrizable (f := fun n => (⇑(f n) : X → ℂ)) (fun n => hf n) ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (tendsto_iff_norm_sub_tendsto_zero.1 hlim))
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero (f n - g) x
  rwa [lp.coeFn_sub] at this

/-- `BM X` is a Banach space. -/
theorem completeSpace_BM : CompleteSpace (BM X) :=
  isClosed_bmSub.completeSpace_coe


/-! ### Kernels acting on `L∞_V` -/

/-- The weights admissible for a kernel `κ`: `V` measurable, `V ≥ 1` and `κV ≤ cV` for some
`c ≥ 0`, so that `κ` is a bounded operator on `L∞_V`. -/
def WeightOK (V : X → ℝ) (κ : Kernel X X) : Prop :=
  Measurable V ∧ (∀ x, 1 ≤ V x) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∀ x, ∫⁻ y, ENNReal.ofReal (V y) ∂κ x ≤ ENNReal.ofReal (c * V x)

/-- The constant `c` of an admissible weight. -/
noncomputable def weightConst {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) : ℝ :=
  Classical.choose h.2.2

/-- The defining property of `weightConst`. -/
theorem weightConst_spec {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) :
    0 ≤ weightConst h ∧
      ∀ x, ∫⁻ y, ENNReal.ofReal (V y) ∂κ x ≤ ENNReal.ofReal (weightConst h * V x) :=
  Classical.choose_spec h.2.2

/-- The action of `κ` in weighted coordinates, `x ↦ V(x)⁻¹ ∫ f(y) V(y) κ(x, dy)`: under
`f ↦ f V` it is the action `g ↦ κg` on `L∞_V`. -/
noncomputable def kFun (V : X → ℝ) (κ : Kernel X X) (f : X → ℂ) (x : X) : ℂ :=
  ((V x : ℂ))⁻¹ * ∫ y, f y * (V y : ℂ) ∂κ x

/-- An admissible weight is positive. -/
theorem WeightOK.pos {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) (x : X) : 0 < V x :=
  lt_of_lt_of_le one_pos (h.2.1 x)

/-- `V` is `κ(x, ·)`-integrable. -/
theorem WeightOK.integrable_V {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) (x : X) :
    Integrable V (κ x) :=
  integrable_of_ofReal_abs_le (f := fun y => ENNReal.ofReal (V y)) h.1
    (fun y => by rw [abs_of_pos (h.pos y)]) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((weightConst_spec h).2 x))

/-- `∫ V dκ(x, ·) ≤ c V(x)`. -/
theorem WeightOK.integral_V_le {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) (x : X) :
    ∫ y, V y ∂κ x ≤ weightConst h * V x := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => (h.pos y).le)
    h.1.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (weightConst_spec h).1 (h.pos x).le)
    ((weightConst_spec h).2 x)

/-- A bounded measurable `f` has `f V` integrable for `κ(x, ·)`. -/
theorem WeightOK.integrable {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) {f : X → ℂ}
    (hm : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : X) :
    Integrable (fun y => f y * (V y : ℂ)) (κ x) := by
  refine Integrable.mono' ((h.integrable_V x).const_mul C)
    (hm.mul (Complex.measurable_ofReal.comp h.1)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.pos y).le]
  exact mul_le_mul_of_nonneg_right (hC y) (h.pos y).le

/-- `|κf|_V ≤ c sup|f|` in weighted coordinates. -/
theorem WeightOK.norm_kFun_le {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) {f : X → ℂ}
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) (x : X) :
    ‖kFun V κ f x‖ ≤ weightConst h * C := by
  have hVx := h.pos x
  have hI : ‖∫ y, f y * (V y : ℂ) ∂κ x‖ ≤ C * (weightConst h * V x) := by
    calc ‖∫ y, f y * (V y : ℂ) ∂κ x‖ ≤ ∫ y, C * V y ∂κ x := by
          refine norm_integral_le_of_norm_le ((h.integrable_V x).const_mul C)
            (Eventually.of_forall fun y => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.pos y).le]
          exact mul_le_mul_of_nonneg_right (hC y) (h.pos y).le
      _ = C * ∫ y, V y ∂κ x := integral_const_mul C _
      _ ≤ C * (weightConst h * V x) := mul_le_mul_of_nonneg_left (h.integral_V_le x) hC0
  rw [kFun, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hVx.le]
  calc (V x)⁻¹ * ‖∫ y, f y * (V y : ℂ) ∂κ x‖ ≤ (V x)⁻¹ * (C * (weightConst h * V x)) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hVx.le)
    _ = weightConst h * C := by field_simp

/-- `κf` is measurable. -/
theorem WeightOK.measurable_kFun {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) {f : X → ℂ}
    (hm : Measurable f) : Measurable (kFun V κ f) := by
  have hF : StronglyMeasurable (fun y => f y * (V y : ℂ)) :=
    (hm.mul (Complex.measurable_ofReal.comp h.1)).stronglyMeasurable
  exact ((Complex.measurable_ofReal.comp h.1).inv).mul
    (StronglyMeasurable.integral_kernel (κ := κ) hF).measurable

/-- The kernel operator as a linear map on `BM X`. -/
noncomputable def kOpLin {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) :
    BM X →ₗ[ℂ] BM X where
  toFun g := mkBM (kFun V κ (bmFun g)) (h.measurable_kFun (measurable_bmFun g))
    (weightConst h * ‖g‖) (h.norm_kFun_le (norm_nonneg g) (norm_bmFun_le g))
  map_add' g g' := bm_ext fun x => by
    simp only [bmFun_mkBM, bmFun_add, kFun, add_mul]
    rw [integral_add (h.integrable (measurable_bmFun g) (norm_bmFun_le g) x)
      (h.integrable (measurable_bmFun g') (norm_bmFun_le g') x), mul_add]
  map_smul' c g := bm_ext fun x => by
    simp only [bmFun_mkBM, bmFun_smul, kFun, RingHom.id_apply, mul_assoc]
    rw [integral_const_mul]; ring

/-- **The operator of a kernel on `L∞_V`**, in the weighted coordinates `BM X` (the bounded
measurable functions `g = f/V`): `g ↦ V⁻¹ κ(gV)`. It is `0` when `V` is not admissible. -/
noncomputable def kOp (V : X → ℝ) (κ : Kernel X X) : BM X →L[ℂ] BM X := by
  classical
  exact if h : WeightOK V κ then
    (kOpLin h).mkContinuous (weightConst h) fun g => norm_le_of_bmFun_le
      (mul_nonneg (weightConst_spec h).1 (norm_nonneg g))
      (h.norm_kFun_le (norm_nonneg g) (norm_bmFun_le g))
  else 0

/-- The action of `kOp`. -/
theorem kOp_apply {V : X → ℝ} {κ : Kernel X X} (h : WeightOK V κ) (g : BM X) (x : X) :
    bmFun (kOp V κ g) x = kFun V κ (bmFun g) x := by
  simp only [kOp, h, ↓reduceDIte]; rfl

/-! ### Composition, identity and powers -/

/-- Admissible weights compose: `(P ∘ₖ Q) V ≤ c_P c_Q V`. -/
theorem WeightOK.comp {V : X → ℝ} {P Q : Kernel X X} (hP : WeightOK V P) (hQ : WeightOK V Q) :
    WeightOK V (P ∘ₖ Q) := by
  refine ⟨hP.1, hP.2.1, weightConst hP * weightConst hQ,
    mul_nonneg (weightConst_spec hP).1 (weightConst_spec hQ).1, fun x => ?_⟩
  have hm : Measurable fun y => ENNReal.ofReal (V y) := ENNReal.measurable_ofReal.comp hP.1
  rw [Kernel.lintegral_comp _ _ _ hm]
  calc ∫⁻ b, ∫⁻ y, ENNReal.ofReal (V y) ∂P b ∂Q x
      ≤ ∫⁻ b, ENNReal.ofReal (weightConst hP) * ENNReal.ofReal (V b) ∂Q x := by
        refine lintegral_mono fun b => ?_
        rw [← ENNReal.ofReal_mul (weightConst_spec hP).1]
        exact (weightConst_spec hP).2 b
    _ = ENNReal.ofReal (weightConst hP) * ∫⁻ b, ENNReal.ofReal (V b) ∂Q x :=
        lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (weightConst hP) * ENNReal.ofReal (weightConst hQ * V x) :=
        mul_le_mul' le_rfl ((weightConst_spec hQ).2 x)
    _ = ENNReal.ofReal (weightConst hP * weightConst hQ * V x) := by
        rw [← ENNReal.ofReal_mul (weightConst_spec hP).1, mul_assoc]

/-- **Composition of kernels is composition of operators**: `P ∘ₖ Q` ("first `Q`, then `P`")
acts as `Q̃ ∘ P̃` on functions. -/
theorem kOp_comp {V : X → ℝ} {P Q : Kernel X X} [IsSFiniteKernel P] [IsSFiniteKernel Q]
    (hP : WeightOK V P) (hQ : WeightOK V Q) : kOp V (P ∘ₖ Q) = kOp V Q * kOp V P := by
  ext1 g
  refine bm_ext fun x => ?_
  change bmFun (kOp V (P ∘ₖ Q) g) x = bmFun (kOp V Q (kOp V P g)) x
  rw [kOp_apply (hP.comp hQ), kOp_apply hQ, kFun, kFun,
    Kernel.integral_comp ((hP.comp hQ).integrable (measurable_bmFun g) (norm_bmFun_le g) x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change _ = bmFun (kOp V P g) y * _
  rw [kOp_apply hP, kFun]
  have : (V y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hP.pos y).ne'
  field_simp

/-- The identity kernel is admissible. -/
theorem weightOK_id {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) :
    WeightOK V (Kernel.id : Kernel X X) :=
  ⟨hV, hV1, 1, zero_le_one, fun x => by
    rw [Kernel.id_apply, lintegral_dirac' x (f := fun y => ENNReal.ofReal (V y))
      (ENNReal.measurable_ofReal.comp hV), one_mul]⟩

/-- The identity kernel acts as the identity operator. -/
theorem kOp_id {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) :
    kOp V (Kernel.id : Kernel X X) = 1 := by
  ext1 g
  refine bm_ext fun x => ?_
  have hW := weightOK_id (X := X) hV hV1
  change bmFun (kOp V Kernel.id g) x = bmFun g x
  rw [kOp_apply hW, kFun, Kernel.id_apply,
    integral_dirac' (fun y => bmFun g y * (V y : ℂ)) x ((measurable_bmFun g).mul
      (Complex.measurable_ofReal.comp hV)).stronglyMeasurable]
  have : (V x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hW.pos x).ne'
  field_simp

/-- `Pⁿ` is admissible and acts as the `n`-th power of the operator of `P`. -/
theorem kOp_pow {V : X → ℝ} {P : Kernel X X} [IsMarkovKernel P] (hP : WeightOK V P) (n : ℕ) :
    WeightOK V (P ^ n) ∧ kOp V (P ^ n) = kOp V P ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ⟨weightOK_id hP.1 hP.2.1, kOp_id hP.1 hP.2.1⟩
  | succ n ih =>
    have := isMarkovKernel_pow P n
    have hc : P ^ (n + 1) = (P ^ n) ∘ₖ P := pow_succ P n
    rw [hc, kOp_comp ih.1 hP, ih.2, pow_succ']
    exact ⟨ih.1.comp hP, rfl⟩

/-! ### The kernel `1 ⊗ π` -/

/-- `1 ⊗ π` is admissible when `π(V) < ∞`. -/
theorem weightOK_const {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (π : Measure X)
    (hπ : ∫⁻ y, ENNReal.ofReal (V y) ∂π ≠ ∞) : WeightOK V (Kernel.const X π) :=
  ⟨hV, hV1, (∫⁻ y, ENNReal.ofReal (V y) ∂π).toReal, ENNReal.toReal_nonneg, fun x => by
    rw [Kernel.const_apply, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hπ]
    exact le_mul_of_one_le_right' (ENNReal.one_le_ofReal.2 (hV1 x))⟩

/-- `(1 ⊗ π) g = π(gV)/V` in weighted coordinates. -/
theorem kOp_const_apply {V : X → ℝ} {π : Measure X} (h : WeightOK V (Kernel.const X π))
    (g : BM X) (x : X) :
    bmFun (kOp V (Kernel.const X π) g) x = ((V x : ℂ))⁻¹ * ∫ y, bmFun g y * (V y : ℂ) ∂π := by
  rw [kOp_apply h, kFun, Kernel.const_apply]

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `(1 ⊗ π) P = 1 ⊗ π` for invariant `π`. -/
theorem kOp_const_mul_kOp [IsMarkovKernel P] [IsProbabilityMeasure π] (hP : WeightOK V P)
    (hPi : WeightOK V (Kernel.const X π)) (hinv : IsInvariant P π) :
    kOp V (Kernel.const X π) * kOp V P = kOp V (Kernel.const X π) := by
  rw [← kOp_comp hP hPi, Kernel.comp_const]
  exact congrArg (fun m => kOp V (Kernel.const X m)) hinv

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `P (1 ⊗ π) = 1 ⊗ π` for a Markov kernel `P`. -/
theorem kOp_mul_kOp_const [IsMarkovKernel P] [IsProbabilityMeasure π] (hP : WeightOK V P)
    (hPi : WeightOK V (Kernel.const X π)) :
    kOp V P * kOp V (Kernel.const X π) = kOp V (Kernel.const X π) := by
  rw [← kOp_comp hPi hP, Kernel.const_comp']

variable {V : X → ℝ} {π : Measure X} in
/-- `(1 ⊗ π)² = 1 ⊗ π`. -/
theorem kOp_const_mul_self [IsProbabilityMeasure π] (hPi : WeightOK V (Kernel.const X π)) :
    kOp V (Kernel.const X π) * kOp V (Kernel.const X π) = kOp V (Kernel.const X π) := by
  rw [← kOp_comp hPi hPi, Kernel.const_comp']


/-! ### The operator norm and `|||·|||_V` -/

/-- A real weight as an `[0, ∞]`-valued weight, as in Chapter 16. -/
noncomputable abbrev eW (V : X → ℝ) : X → ℝ≥0∞ := fun x => ENNReal.ofReal (V x)

/-- The real-part estimate behind `norm_kOp_sub_le`. -/
theorem abs_integral_sub_le_of_fNorm {V : X → ℝ} {μ ν : Measure X} {H : X → ℝ}
    (hm : Measurable H) {c D : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : ∀ y, |H y| ≤ c * V y)
    (hμ : Integrable H μ) (hν : Integrable H ν) (hd : fNorm (eW V) μ ν ≤ ENNReal.ofReal D) :
    |∫ y, H y ∂μ - ∫ y, H y ∂ν| ≤ c * D := by
  have hb' : ∀ y, ENNReal.ofReal |H y| ≤ ENNReal.ofReal c * eW V y := fun y => by
    rw [← ENNReal.ofReal_mul hc]; exact ENNReal.ofReal_le_ofReal (hb y)
  have h := ofReal_abs_integral_sub_le_mul_fNorm ENNReal.ofReal_ne_top hm hb' hμ hν
  have h2 : ENNReal.ofReal |∫ y, H y ∂μ - ∫ y, H y ∂ν| ≤ ENNReal.ofReal (c * D) := by
    rw [ENNReal.ofReal_mul hc]; exact h.trans (mul_le_mul' le_rfl hd)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hD)).1 h2

/-- **Operator norm from `V`-norms**: if `‖κ₁(x, ·) − κ₂(x, ·)‖_V ≤ D V(x)` for all `x`, the
operator `κ₁ − κ₂` on `L∞_V` has norm at most `2D` (the factor `2` comes from splitting complex
functions into real and imaginary parts). -/
theorem norm_kOp_sub_le {V : X → ℝ} {κ₁ κ₂ : Kernel X X} (h₁ : WeightOK V κ₁)
    (h₂ : WeightOK V κ₂) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ x, fNorm (eW V) (κ₁ x) (κ₂ x) ≤ ENNReal.ofReal (D * V x)) :
    ‖kOp V κ₁ - kOp V κ₂‖ ≤ 2 * D := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  refine norm_le_of_bmFun_le (by positivity) fun x => ?_
  have hVx := h₁.pos x
  change ‖bmFun (kOp V κ₁ g - kOp V κ₂ g) x‖ ≤ _
  rw [bmFun_sub, kOp_apply h₁, kOp_apply h₂, kFun, kFun, ← mul_sub]
  set F : X → ℂ := fun y => bmFun g y * (V y : ℂ) with hFdef
  have hF1 := h₁.integrable (measurable_bmFun g) (norm_bmFun_le g) x
  have hF2 := h₂.integrable (measurable_bmFun g) (norm_bmFun_le g) x
  have hFb : ∀ y, ‖F y‖ ≤ ‖g‖ * V y := fun y => by
    rw [hFdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h₁.pos y).le]
    exact mul_le_mul_of_nonneg_right (norm_bmFun_le g y) (h₁.pos y).le
  have hFm : Measurable F := (measurable_bmFun g).mul (Complex.measurable_ofReal.comp h₁.1)
  have hre : |∫ y, (F y).re ∂κ₁ x - ∫ y, (F y).re ∂κ₂ x| ≤ ‖g‖ * (D * V x) :=
    abs_integral_sub_le_of_fNorm (Complex.measurable_re.comp hFm) (norm_nonneg g)
      (mul_nonneg hD hVx.le) (fun y => (Complex.abs_re_le_norm _).trans (hFb y)) hF1.re hF2.re
      (hd x)
  have him : |∫ y, (F y).im ∂κ₁ x - ∫ y, (F y).im ∂κ₂ x| ≤ ‖g‖ * (D * V x) :=
    abs_integral_sub_le_of_fNorm (Complex.measurable_im.comp hFm) (norm_nonneg g)
      (mul_nonneg hD hVx.le) (fun y => (Complex.abs_im_le_norm _).trans (hFb y)) hF1.im hF2.im
      (hd x)
  have e1 : ∫ y, (F y).re ∂κ₁ x = (∫ y, F y ∂κ₁ x).re := integral_re hF1
  have e2 : ∫ y, (F y).re ∂κ₂ x = (∫ y, F y ∂κ₂ x).re := integral_re hF2
  have e3 : ∫ y, (F y).im ∂κ₁ x = (∫ y, F y ∂κ₁ x).im := integral_im hF1
  have e4 : ∫ y, (F y).im ∂κ₂ x = (∫ y, F y ∂κ₂ x).im := integral_im hF2
  rw [e1, e2, ← Complex.sub_re] at hre
  rw [e3, e4, ← Complex.sub_im] at him
  have hz := Complex.norm_le_abs_re_add_abs_im (∫ y, F y ∂κ₁ x - ∫ y, F y ∂κ₂ x)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hVx.le]
  calc (V x)⁻¹ * ‖∫ y, F y ∂κ₁ x - ∫ y, F y ∂κ₂ x‖
      ≤ (V x)⁻¹ * (2 * (‖g‖ * (D * V x))) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hVx.le)
    _ = 2 * D * ‖g‖ := by field_simp

/-- **`V`-norms from the operator norm**: `‖κ₁(x, ·) − κ₂(x, ·)‖_V ≤ ‖κ₁ − κ₂‖ V(x)`. -/
theorem fNorm_le_norm_kOp_sub {V : X → ℝ} {κ₁ κ₂ : Kernel X X} (h₁ : WeightOK V κ₁)
    (h₂ : WeightOK V κ₂) (x : X) :
    fNorm (eW V) (κ₁ x) (κ₂ x) ≤ ENNReal.ofReal (‖kOp V κ₁ - kOp V κ₂‖ * V x) := by
  refine fNorm_le fun H hH => ?_
  obtain ⟨hm, hb, hi1, hi2⟩ := hH
  have hb' : ∀ y, |H y| ≤ V y := fun y =>
    (ENNReal.ofReal_le_ofReal_iff (h₁.pos y).le).1 (hb y)
  set f : X → ℂ := fun y => ((H y / V y : ℝ) : ℂ) with hfdef
  have hfm : Measurable f := Complex.measurable_ofReal.comp (hm.div h₁.1)
  have hfb : ∀ y, ‖f y‖ ≤ 1 := fun y => by
    rw [hfdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (h₁.pos y)]
    exact (div_le_one (h₁.pos y)).2 (hb' y)
  set g := mkBM f hfm 1 hfb
  have hg : ‖g‖ ≤ 1 := norm_le_of_bmFun_le zero_le_one hfb
  have hfV : ∀ y, bmFun g y * (V y : ℂ) = (H y : ℂ) := fun y => by
    rw [bmFun_mkBM, hfdef]
    have : (V y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h₁.pos y).ne'
    push_cast
    field_simp
  have hkey : bmFun (kOp V κ₁ g - kOp V κ₂ g) x =
      (V x : ℂ)⁻¹ * ((∫ y, H y ∂κ₁ x - ∫ y, H y ∂κ₂ x : ℝ) : ℂ) := by
    rw [bmFun_sub, kOp_apply h₁, kOp_apply h₂, kFun, kFun, ← mul_sub]
    simp_rw [hfV]
    rw [integral_complex_ofReal, integral_complex_ofReal, Complex.ofReal_sub]
  have hle : ‖bmFun (kOp V κ₁ g - kOp V κ₂ g) x‖ ≤ ‖kOp V κ₁ - kOp V κ₂‖ := by
    refine (norm_bmFun_le _ x).trans ?_
    change ‖(kOp V κ₁ - kOp V κ₂) g‖ ≤ _
    calc ‖(kOp V κ₁ - kOp V κ₂) g‖ ≤ ‖kOp V κ₁ - kOp V κ₂‖ * ‖g‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖kOp V κ₁ - kOp V κ₂‖ * 1 :=
          mul_le_mul_of_nonneg_left hg (norm_nonneg (kOp V κ₁ - kOp V κ₂))
      _ = _ := mul_one _
  have hVx := h₁.pos x
  rw [hkey, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hVx] at hle
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_left hle hVx.le
  rwa [← mul_assoc, mul_inv_cancel₀ hVx.ne', one_mul, mul_comm] at this

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `|||Pⁿ − 1 ⊗ π|||_V ≤ ‖P̃ⁿ − Π‖`. -/
theorem vErgDist_le_norm [IsMarkovKernel P] (hP : WeightOK V P)
    (hPi : WeightOK V (Kernel.const X π)) (n : ℕ) :
    vErgDist (eW V) P π n ≤ ENNReal.ofReal ‖kOp V P ^ n - kOp V (Kernel.const X π)‖ := by
  refine vOpNorm_le fun x => ?_
  have h := fNorm_le_norm_kOp_sub (kOp_pow hP n).1 hPi x
  rw [(kOp_pow hP n).2] at h
  exact h.trans (le_of_eq (ENNReal.ofReal_mul (ContinuousLinearMap.opNorm_nonneg _)))

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- `‖P̃ⁿ − Π‖ ≤ 2D` when `|||Pⁿ − 1 ⊗ π|||_V ≤ D`. -/
theorem norm_le_vErgDist [IsMarkovKernel P] (hP : WeightOK V P)
    (hPi : WeightOK V (Kernel.const X π)) (n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hd : vErgDist (eW V) P π n ≤ ENNReal.ofReal D) :
    ‖kOp V P ^ n - kOp V (Kernel.const X π)‖ ≤ 2 * D := by
  rw [← (kOp_pow hP n).2]
  refine norm_kOp_sub_le (kOp_pow hP n).1 hPi hD fun x => ?_
  rw [Kernel.const_apply, ENNReal.ofReal_mul hD]
  exact (fNorm_pow_le_vErgDist_mul P π n (ENNReal.ofReal_pos.2 (hP.pos x)).ne'
    ENNReal.ofReal_ne_top).trans (mul_le_mul' hd le_rfl)

variable {V : X → ℝ} {P : Kernel X X} {π : Measure X} in
/-- Finite distances `|||P⁰ − 1 ⊗ π|||_V` and `|||P − 1 ⊗ π|||_V` make `V` admissible for
`P` and for `1 ⊗ π`: `π(V) < ∞` and `PV ≤ (|||P − 1 ⊗ π|||_V + π(V)) V` (16.15). -/
theorem weightOK_of_vErgDist [IsMarkovKernel P] [IsProbabilityMeasure π] (hV : Measurable V)
    (hV1 : ∀ x, 1 ≤ V x) (h0 : vErgDist (eW V) P π 0 ≠ ∞) (h1 : vErgDist (eW V) P π 1 ≠ ∞) :
    WeightOK V P ∧ WeightOK V (Kernel.const X π) := by
  have := nonempty_of_isProbabilityMeasure π
  inhabit X
  have hVm : Measurable (eW V) := ENNReal.measurable_ofReal.comp hV
  have hV1' : ∀ x, 1 ≤ eW V x := fun x => ENNReal.one_le_ofReal.2 (hV1 x)
  have hπ := lintegral_ne_top_of_vErgDist_zero hVm hV1' (x₀ := default) ENNReal.ofReal_ne_top
    P π h0
  refine ⟨⟨hV, hV1, (vErgDist (eW V) P π 1 + ∫⁻ y, eW V y ∂π).toReal, ENNReal.toReal_nonneg,
    fun x => ?_⟩, weightOK_const hV hV1 π hπ⟩
  have h := lintegral_pow_le_vErgDist hVm P π 1 (x := x)
    (ENNReal.ofReal_pos.2 (lt_of_lt_of_le one_pos (hV1 x))).ne' ENNReal.ofReal_ne_top
  rw [pow_one] at h
  refine h.trans ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ENNReal.add_ne_top.2
    ⟨h1, hπ⟩), add_mul]
  exact add_le_add le_rfl (le_mul_of_one_le_right' (hV1' x))

end MeynTweedie.Epilogue
