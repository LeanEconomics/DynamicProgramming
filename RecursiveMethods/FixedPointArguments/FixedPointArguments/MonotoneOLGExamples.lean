/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FixedPointArguments.MonotoneOLG

/-!
# A concrete OLG economy for §17.5: the counterexample to Proposition 5 as stated

SLP p. 530. The economy:

* labour disutility `H(l) = −l − log(1 − l)` on `[0, 1)` (`L = 1`), so `H'(l) = l/(1 − l)`,
  `H''(l) = 1/(1 − l)²` and `ζ(l) = l²/(1 − l)`;
* utility `V(y) = log(1 + y)`, so `V'(y) = 1/(1 + y)`, `V''(y) = −1/(1 + y)²`,
  `φ(y) = y/(1 + y)` and relative risk aversion `y/(1 + y) ≤ 1`;
* the one-point state space `X = [1, 1]` with `π(x, ·) = δ₁`; `K = 3` (`KC = 3/2 > 1`).

Results:

* `monoCexH_assumption17_1H`, `monoCexV_assumption17_1V`, `monoCex_assumption17_1`: Assumption 17.1.
* `monoCexV_assumption17_4`: Assumption 17.4. `monoCexπ_assumption17_3`: Assumption 17.3.
* `monoCex_fixedPoint_unique_pos`: the fixed points of `T` with `h > 0` are all equal (they solve
  `ζ(n) = φ(n)`, i.e. `n² + 2n − 1 = 0`).
* **`proposition_5_counterexample`**: in this economy all hypotheses of Proposition 5 hold, the
  iterates from `ε_K` and from `B` converge to the same `f` (the book's condition `f = g`), and yet
  `f` is not the unique fixed point of `T` (the zero function is another). So the book's
  conclusion "this function is the unique fixed point of `T`" is false, not merely vacuous.
-/

namespace StokeyLucasPrescott.FixedPointArguments

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-- `H(l) = −l − log(1 − l)`. -/
noncomputable def monoCexH (l : ℝ) : ℝ := -l - Real.log (1 - l)

/-- `H'(l) = l/(1 − l)`. -/
noncomputable def monoCexH' (l : ℝ) : ℝ := l / (1 - l)

/-- `H''(l) = 1/(1 − l)²`. -/
noncomputable def monoCexH'' (l : ℝ) : ℝ := 1 / (1 - l) ^ 2

/-- `V(y) = log(1 + y)`. -/
noncomputable def monoCexV (y : ℝ) : ℝ := Real.log (1 + y)

/-- `V'(y) = 1/(1 + y)`. -/
noncomputable def monoCexV' (y : ℝ) : ℝ := (1 + y)⁻¹

/-- `V''(y) = −1/(1 + y)²`. -/
noncomputable def monoCexV'' (y : ℝ) : ℝ := -((1 + y) ^ 2)⁻¹

/-- `H' = l/(1 − l)` is the derivative of `H`. -/
theorem hasDerivAt_monoCexH {l : ℝ} (hl : l < 1) : HasDerivAt monoCexH (monoCexH' l) l := by
  have h1 : (1 : ℝ) - l ≠ 0 := by linarith
  have h := (hasDerivAt_id' l).neg.sub (((hasDerivAt_id' l).const_sub 1).log h1)
  refine h.congr_deriv ?_
  rw [monoCexH']
  field_simp
  ring

/-- `H'' = 1/(1 − l)²` is the derivative of `H'`. -/
theorem hasDerivAt_monoCexH' {l : ℝ} (hl : l < 1) : HasDerivAt monoCexH' (monoCexH'' l) l := by
  have h1 : (1 : ℝ) - l ≠ 0 := by linarith
  have h := (hasDerivAt_id' l).div ((hasDerivAt_id' l).const_sub 1) h1
  refine h.congr_deriv ?_
  rw [monoCexH'']
  field_simp
  ring

/-- `H(l) = −l − log(1 − l)` satisfies the labour half of **Assumption 17.1** with `L = 1`. -/
theorem monoCexH_assumption17_1H : MonoAssumption17_1H monoCexH monoCexH' monoCexH'' 1 := by
  have hd : ∀ l ∈ Ico (0 : ℝ) 1, HasDerivAt monoCexH (monoCexH' l) l :=
    fun l hl => hasDerivAt_monoCexH hl.2
  have hcont : ContinuousOn monoCexH (Ico 0 1) := fun l hl =>
    (hd l hl).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Ico (0 : ℝ) 1), deriv monoCexH x = monoCexH' x :=
    fun x hx => by
    rw [interior_Ico] at hx
    exact (hd x (Ioo_subset_Ico_self hx)).deriv
  refine ⟨one_pos, fun l hl => (hd l hl).hasDerivWithinAt,
    fun l hl => (hasDerivAt_monoCexH' hl.2).hasDerivWithinAt, ?_, ?_, ?_, ?_,
    by simp [monoCexH'], ?_⟩
  · refine ContinuousOn.div continuousOn_const (by fun_prop) fun l hl => ?_
    have : (1 : ℝ) - l ≠ 0 := by linarith [hl.2]
    positivity
  · intro l hl
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - l by linarith [hl.2])
    rw [monoCexH]
    linarith
  · refine strictMonoOn_of_deriv_pos (convex_Ico 0 1) hcont fun x hx => ?_
    rw [hderiv x hx, monoCexH']
    rw [interior_Ico] at hx
    exact div_pos hx.1 (by linarith [hx.2])
  · refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ico 0 1) hcont fun x hx y hy hxy => ?_
    rw [hderiv x hx, hderiv y hy, monoCexH', monoCexH']
    rw [interior_Ico] at hx hy
    rw [div_lt_div_iff₀ (by linarith [hx.2]) (by linarith [hy.2])]
    nlinarith
  · have h1 : Tendsto (fun l : ℝ => 1 - l) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun l : ℝ => 1 - l) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        rw [sub_self] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      · filter_upwards [self_mem_nhdsWithin] with l hl
        exact sub_pos.2 (mem_Iio.1 hl)
    have h2 : Tendsto (fun l : ℝ => (1 - l)⁻¹) (𝓝[<] 1) atTop :=
      tendsto_inv_nhdsGT_zero.comp h1
    have := Tendsto.pos_mul_atTop one_pos (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) h2
    refine this.congr fun l => ?_
    simp [monoCexH', div_eq_mul_inv]

/-- `V' = 1/(1 + y)` is the derivative of `V`. -/
theorem hasDerivAt_monoCexV {y : ℝ} (hy : 0 ≤ y) : HasDerivAt monoCexV (monoCexV' y) y := by
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith
  have h := ((hasDerivAt_id' y).const_add 1).log h1
  refine h.congr_deriv ?_
  rw [monoCexV']
  field_simp

/-- `V'' = −1/(1 + y)²` is the derivative of `V'`. -/
theorem hasDerivAt_monoCexV' {y : ℝ} (hy : 0 ≤ y) : HasDerivAt monoCexV' (monoCexV'' y) y := by
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith
  have h := ((hasDerivAt_id' y).const_add 1).inv h1
  refine h.congr_deriv ?_
  rw [monoCexV'']
  field_simp

/-- `V(y) = log(1 + y)` satisfies the utility half of **Assumption 17.1**. -/
theorem monoCexV_assumption17_1V : MonoAssumption17_1V monoCexV monoCexV' monoCexV'' := by
  have hcont : ContinuousOn monoCexV (Ici 0) := fun y hy =>
    (hasDerivAt_monoCexV hy).continuousAt.continuousWithinAt
  refine ⟨fun y hy => (hasDerivAt_monoCexV hy).hasDerivWithinAt,
    fun y hy => (hasDerivAt_monoCexV' hy).hasDerivWithinAt, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_)
    have : (1 : ℝ) + y ≠ 0 := by linarith [mem_Ici.1 hy]
    positivity
  · intro y hy
    exact Real.log_nonneg (by linarith [mem_Ici.1 hy])
  · intro x hx y hy hxy
    exact Real.log_lt_log (by linarith [mem_Ici.1 hx]) (by linarith)
  · refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) hcont fun x hx y hy hxy => ?_
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_monoCexV (le_of_lt hx)).deriv, (hasDerivAt_monoCexV (le_of_lt hy)).deriv,
      monoCexV',
      monoCexV']
    exact inv_strictAntiOn (by rw [mem_Ioi]; linarith [mem_Ioi.1 hx])
      (by rw [mem_Ioi]; linarith [mem_Ioi.1 hy]) (by linarith)

/-- The economy satisfies **Assumption 17.1**. -/
theorem monoCex_assumption17_1 :
    MonoAssumption17_1 monoCexH monoCexH' monoCexH'' monoCexV monoCexV' monoCexV'' 1 :=
  ⟨monoCexH_assumption17_1H, monoCexV_assumption17_1V⟩

/-- Relative risk aversion of `log(1 + y)` is `y/(1 + y)`. -/
theorem monoRRA_monoCexV {y : ℝ} (hy : 0 ≤ y) :
    monoRRA monoCexV' monoCexV'' y = y / (1 + y) := by
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith
  rw [monoRRA, monoCexV', monoCexV'']
  field_simp

/-- `V(y) = log(1 + y)` satisfies **Assumption 17.4** (relative risk aversion `y/(1+y) ≤ 1`). -/
theorem monoCexV_assumption17_4 : MonoAssumption17_4 monoCexV' monoCexV'' := fun y hy => by
  rw [monoRRA_monoCexV hy, div_le_one (by linarith)]
  linarith

/-- The one-point state space `X = [1, 1]`. -/
abbrev monoCexX : Type := Icc (1 : ℝ) 1

/-- The unique point of `X`. -/
def monoCexX₁ : monoCexX := ⟨1, le_rfl, le_rfl⟩

/-- `π(x, ·) = δ₁`. -/
noncomputable abbrev monoCexπ : Kernel monoCexX monoCexX :=
  Kernel.const monoCexX (Measure.dirac monoCexX₁)

/-- `π(x, ·) = δ₁` satisfies **Assumption 17.3** (`π(x, ·)` does not depend on `x`). -/
theorem monoCexπ_assumption17_3 : MonoAssumption17_3 monoCexπ := fun ε hε =>
  ⟨1, one_pos, fun x x' _ n A _ => by simp [monoCexπ, hε.le]⟩

/-- In the example, a fixed point `h > 0` of `T` has `h(1) = ζ(n)` with `n² + 2n − 1 = 0`,
`n ∈ (0, 1)`. -/
theorem monoCex_fixedPoint_root {h : monoCexX →ᵇ ℝ}
    (hfix : monoOLGOp monoCexπ monoCexH' monoCexV' 1 h = h)
    (hpos : 0 < h monoCexX₁) :
    let n := monoZetaInv monoCexH' 1 (h monoCexX₁)
    n ∈ Ioo 0 1 ∧ n ^ 2 + 2 * n - 1 = 0 ∧ monoZeta monoCexH' n = h monoCexX₁ := by
  intro n
  have hA := monoCex_assumption17_1
  have hn := hA.hH.zetaInv_mem (h monoCexX₁)
  have hζ : monoZeta monoCexH' n = h monoCexX₁ := hA.hH.zeta_zetaInv hpos.le
  have hn0 : 0 < n := by
    rcases hn.1.eq_or_lt with e | e
    · have : monoZeta monoCexH' n = 0 := by rw [show n = 0 from e.symm, monoZeta_zero]
      linarith
    · exact e
  have happ := monoOLGOp_apply hA one_pos monoCexπ_assumption17_3 h monoCexX₁
  rw [hfix] at happ
  simp only [monoCexπ, Kernel.const_apply, integral_dirac] at happ
  have hx1 : (monoCexX₁ : ℝ) = 1 := rfl
  rw [hx1, one_mul] at happ
  -- `ζ(n) = φ(n)`
  have heq : monoZeta monoCexH' n = monoPhi monoCexV' n := hζ.trans happ
  have h1n : (1 : ℝ) - n ≠ 0 := by linarith [hn.2]
  have h1n' : (1 : ℝ) + n ≠ 0 := by linarith
  simp only [monoZeta, monoPhi, monoCexH', monoCexV'] at heq
  field_simp at heq
  exact ⟨⟨hn0, hn.2⟩, by linear_combination heq, hζ⟩

/-- In the example, all fixed points of `T` with `h(1) > 0` coincide. -/
theorem monoCex_fixedPoint_unique_pos {h k : monoCexX →ᵇ ℝ}
    (hh : monoOLGOp monoCexπ monoCexH' monoCexV' 1 h = h)
    (hk : monoOLGOp monoCexπ monoCexH' monoCexV' 1 k = k)
    (hhpos : 0 < h monoCexX₁) (hkpos : 0 < k monoCexX₁) : h = k := by
  obtain ⟨hn, hroot, hζ⟩ := monoCex_fixedPoint_root hh hhpos
  obtain ⟨kn, kroot, kζ⟩ := monoCex_fixedPoint_root hk hkpos
  have e : monoZetaInv monoCexH' 1 (h monoCexX₁) = monoZetaInv monoCexH' 1 (k monoCexX₁) := by
    have : (monoZetaInv monoCexH' 1 (h monoCexX₁) - monoZetaInv monoCexH' 1 (k monoCexX₁)) *
        (monoZetaInv monoCexH' 1 (h monoCexX₁) + monoZetaInv monoCexH' 1 (k monoCexX₁) + 2) = 0 :=
          by
      linear_combination hroot - kroot
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · linarith [hn.1, kn.1]
  have : h monoCexX₁ = k monoCexX₁ := by rw [← hζ, ← kζ, e]
  ext x
  have hx : x = monoCexX₁ := Subsingleton.elim _ _
  rw [hx, this]

/-- **Counterexample to Proposition 5 as stated** (SLP p. 530). In the economy above all the
hypotheses of Proposition 5 hold (Assumptions 17.1, 17.3, 17.4; `KC = 3/2 > 1` for `K = 3`),
the iterates of `T` from `f₀ ≡ ε_K` and from `g₀ ≡ B` converge to one and the same function
`f`
(the book's hypothesis `f = g`), and yet `f` is *not* the unique fixed point of `T`. -/
theorem proposition_5_counterexample :
    MonoAssumption17_1 monoCexH monoCexH' monoCexH'' monoCexV monoCexV' monoCexV'' 1 ∧
      MonoAssumption17_3 monoCexπ ∧
      MonoAssumption17_4 monoCexV' monoCexV'' ∧ 1 < 3 * (1 * monoCexV' (1 * 1)) ∧
      ∃ f : monoCexX →ᵇ ℝ,
        Tendsto (fun n => (monoOLGOp monoCexπ monoCexH' monoCexV' 1)^[n]
          (const _ (monoEpsK monoCexH' 1 3))) atTop (𝓝 f) ∧
        Tendsto (fun n => (monoOLGOp monoCexπ monoCexH' monoCexV' 1)^[n]
          (const _ (monoB 1 1 monoCexH' monoCexV' 1 3))) atTop (𝓝 f) ∧
        ¬ ∀ h, monoOLGOp monoCexπ monoCexH' monoCexV' 1 h = h → h = f := by
  have hA := monoCex_assumption17_1
  have hK : 1 < 3 * (1 * monoCexV' (1 * 1)) := by norm_num [monoCexV']
  obtain ⟨hε, -, -, -, -, -, -, -, f, hf, g, hg, hTf, hTg, hfl, hgl, -, -⟩ :=
    proposition_5 hA one_pos le_rfl monoCexπ_assumption17_3 monoCexV_assumption17_4 hK
  have hfg : f = g := monoCex_fixedPoint_unique_pos hTf hTg
    (lt_of_lt_of_le hε (hf monoCexX₁).1) (lt_of_lt_of_le hε (hg monoCexX₁).1)
  rw [← hfg] at hgl
  exact ⟨hA, monoCexπ_assumption17_3, monoCexV_assumption17_4, hK, f, hfl, hgl,
    proposition_5_literal_false hA one_pos le_rfl monoCexπ_assumption17_3
      monoCexV_assumption17_4 hK
      hfl hgl⟩

end StokeyLucasPrescott.FixedPointArguments
