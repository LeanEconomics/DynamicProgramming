/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDP.ConstantReturns

/-!
# Constant returns to scale: concavity, monotonicity, differentiability

SLP §9.3, pp. 272–273, Exercises 9.9 and 9.10b–c, with `X ⊆ ℝˡ` a convex cone.

* `ex_9_9_concave`: `M` preserves concavity in `x` on `H(S)`.
* `ex_9_9_quasiconcave_false`: `M` does **not** preserve quasi-concavity. With `Z = ℝ`,
  `Q(z, ·) = ½δ₀ + ½δ₁`, and `f(x, z) = max(s(z)u, 2s(z)u)`, `u = x₁ − x₂`, `s(0) = 1`,
  `s(1) = −1` and `s` continuous, every section `f(·, z)` is quasi-concave and `f ∈ H(S)`, but
  `(Mf)(x, z) = |x₁ − x₂|/2`.
* **Exercise 9.10b** (`ex_9_10b`): if `F(·, ·, z)` is concave on `A_z`, strictly for
  non-proportional `x, x′`, and `A_z` is convex, then `v(·, z)` is concave, and strictly so along
  non-proportional pairs (as in Exercise 4.8c). Homogeneous functions are linear along rays, so
  this is the strongest form of strict concavity available.
* **Exercise 9.10c**: `v(·, z)` is strictly increasing under Assumptions 9.8–9.9
  (`ex_9_10c_mono`); and at `x₀ ∈ int X` with `g(x₀, z₀) ∈ int Γ(x₀, z₀)`, `v(·, z₀)` is
  differentiable with `vᵢ(x₀, z₀) = Fᵢ[x₀, g(x₀, z₀), z₀]` (`ex_9_10c_diff`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StokeyLucasPrescott.StochasticDP

variable {l : ℕ} {XS : Set (Fin l → ℝ)} {hX : IsCone XS}
variable {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]

/-- **Exercise 9.9 (concavity).** If `f ∈ H(S)` is concave in `x` for each shock, so is `Mf`. -/
theorem ex_9_9_concave (hC : Convex ℝ XS) (Q : Kernel Z Z) [IsMarkovKernel Q]
    {f : XS × Z → ℝ} (hf : InHS hX f) (hconc : ∀ z', IsConcaveS hC fun x => f (x, z'))
    (z : Z) : IsConcaveS hC fun x => mop Q f (x, z) := by
  intro x x' θ h0 h1
  have i0 := integrable_section_HS Q hf x z
  have i1 := integrable_section_HS Q hf x' z
  have iθ := integrable_section_HS Q hf (cmb hC h0 h1 x x') z
  simp only [mop]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i0.const_mul θ)
    (i1.const_mul _)]
  exact integral_mono ((i0.const_mul θ).add (i1.const_mul _)) iθ
    fun z' => hconc z' x x' θ h0 h1

/-! ### The counterexample to quasi-concavity -/

/-- `f` is quasi-concave on the convex set `S`. -/
def IsQuasiConcaveS {S : Set (Fin l → ℝ)} (hS : Convex ℝ S) (f : S → ℝ) : Prop :=
  ∀ x x' (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1), min (f x) (f x') ≤ f (cmb hS h0 h1 x x')

/-- `φ(u) = max(u, 2u)`: increasing and homogeneous of degree one. -/
noncomputable def qcPhi (u : ℝ) : ℝ := max u (2 * u)

/-- A continuous sign switch with `s(0) = 1`, `s(1) = −1`. -/
noncomputable def qcSign (z : ℝ) : ℝ := max (-1) (min 1 (1 - 2 * z))

/-- The counterexample `f(x, z) = φ(s(z)(x₁ − x₂))` on the cone `ℝ²`. -/
noncomputable def qcF (p : ↥(univ : Set (Fin 2 → ℝ)) × ℝ) : ℝ :=
  qcPhi (qcSign p.2 * (p.1.1 0 - p.1.1 1))

/-- The two-point shock distribution `½δ₀ + ½δ₁`. -/
noncomputable def twoPoint : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

theorem isProbabilityMeasure_twoPoint : IsProbabilityMeasure twoPoint :=
  ⟨by simp [twoPoint, ← two_mul, ENNReal.mul_inv_cancel]⟩

theorem isCone_univ : IsCone (univ : Set (Fin 2 → ℝ)) := fun _ _ _ _ => mem_univ _

theorem integral_twoPoint {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    ∫ z, g z ∂twoPoint = (g 0 + g 1) / 2 := by
  have hi : ∀ a : ℝ, Integrable g (Measure.dirac a) := fun a =>
    integrable_of_abs_le hg.measurable hB
  rw [twoPoint, integral_smul_measure, integral_add_measure (hi 0) (hi 1),
    integral_dirac' _ _ hg.stronglyMeasurable, integral_dirac' _ _ hg.stronglyMeasurable]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem qcPhi_mono : Monotone qcPhi := fun a b h => max_le_max h (by linarith)

theorem abs_qcPhi_le (u : ℝ) : |qcPhi u| ≤ 2 * |u| := by
  simp only [qcPhi]
  rcases le_total 0 u with hu | hu
  · rw [max_eq_right (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg hu]
  · rw [max_eq_left (by linarith), abs_of_nonpos hu]
    linarith [abs_nonneg u]

theorem abs_qcSign_le (z : ℝ) : |qcSign z| ≤ 1 := by
  simp only [qcSign, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- **Correction to Exercise 9.9.** `M` does not preserve quasi-concavity: `qcF ∈ H(S)` and each
`qcF(·, z)` is quasi-concave, but `(M qcF)(·, z) = |x₁ − x₂|/2` is not. -/
theorem ex_9_9_quasiconcave_false :
    InHS isCone_univ qcF ∧ (∀ z, IsQuasiConcaveS convex_univ fun x => qcF (x, z)) ∧
      ¬∀ z, IsQuasiConcaveS convex_univ fun x => mop (Kernel.const ℝ twoPoint) qcF (x, z) := by
  have hs : Continuous qcSign :=
    continuous_const.max (continuous_const.min (continuous_const.sub
      (continuous_const.mul continuous_id)))
  have hlin : Continuous fun p : ↥(univ : Set (Fin 2 → ℝ)) × ℝ =>
      qcSign p.2 * (p.1.1 0 - p.1.1 1) :=
    (hs.comp continuous_snd).mul
      (((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)).sub
        ((continuous_apply 1).comp (continuous_subtype_val.comp continuous_fst)))
  have hphi : Continuous qcPhi := continuous_id.max (continuous_const.mul continuous_id)
  have hcont : Continuous qcF := hphi.comp hlin
  have hhom : ∀ x z (a : ℝ) (ha : 0 ≤ a), qcF (csmul isCone_univ ha x, z) = a * qcF (x, z) := by
    intro x z a ha
    simp only [qcF, qcPhi, csmul, Pi.smul_apply, smul_eq_mul]
    rw [mul_max_of_nonneg _ _ ha]
    congr 1 <;> ring
  have hbd : ∀ p, |qcF p| ≤ 4 * ‖p.1.1‖ := by
    intro p
    have h0 := norm_le_pi_norm p.1.1 0
    have h1 := norm_le_pi_norm p.1.1 1
    rw [Real.norm_eq_abs] at h0 h1
    have hs1 := abs_qcSign_le p.2
    calc |qcF p| ≤ 2 * |qcSign p.2 * (p.1.1 0 - p.1.1 1)| := abs_qcPhi_le _
      _ = 2 * (|qcSign p.2| * |p.1.1 0 - p.1.1 1|) := by rw [abs_mul]
      _ ≤ 2 * (1 * (|p.1.1 0| + |p.1.1 1|)) := by
          gcongr
          exact abs_sub _ _
      _ ≤ 4 * ‖p.1.1‖ := by linarith
  refine ⟨⟨hcont, hhom, 4, hbd⟩, fun z x x' θ h0 h1 => ?_, fun h => ?_⟩
  · have hl : qcSign z * ((cmb convex_univ h0 h1 x x').1 0 - (cmb convex_univ h0 h1 x x').1 1) =
        θ * (qcSign z * (x.1 0 - x.1 1)) + (1 - θ) * (qcSign z * (x'.1 0 - x'.1 1)) := by
      simp only [cmb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change min (qcPhi _) (qcPhi _) ≤ qcPhi _
    rw [hl, ← qcPhi_mono.map_min]
    refine qcPhi_mono ?_
    rcases le_total (qcSign z * (x.1 0 - x.1 1)) (qcSign z * (x'.1 0 - x'.1 1)) with hab | hab
    · rw [min_eq_left hab]; nlinarith
    · rw [min_eq_right hab]; nlinarith
  · have := isProbabilityMeasure_twoPoint
    have hmop : ∀ x : (univ : Set (Fin 2 → ℝ)),
        mop (Kernel.const ℝ twoPoint) qcF (x, 0) = (qcF (x, 0) + qcF (x, 1)) / 2 := fun x => by
      rw [mop, Kernel.const_apply]
      exact integral_twoPoint (hcont.comp (Continuous.prodMk_right x)) (B := 4 * ‖x.1‖)
        fun z => hbd (x, z)
    have hq := h 0 ⟨fun i => if i = 0 then 1 else 0, mem_univ _⟩
      ⟨fun i => if i = 0 then 0 else 1, mem_univ _⟩ (1 / 2) (by norm_num) (by norm_num)
    simp only [hmop] at hq
    have s0 : qcSign 0 = 1 := by norm_num [qcSign]
    have s1 : qcSign 1 = -1 := by norm_num [qcSign]
    simp [qcF, qcPhi, s0, s1, cmb] at hq
    norm_num at hq

/-! ### Exercise 9.10b–c -/

/-- `x` and `x′` are not proportional. -/
def NonProp (x x' : XS) : Prop :=
  (∀ a : ℝ, 0 ≤ a → x.1 ≠ a • x'.1) ∧ ∀ a : ℝ, 0 ≤ a → x'.1 ≠ a • x.1

/-- `F(·, ·, z)` is concave on `A_z`, strictly for non-proportional `x, x′` (Exercise 4.8c). -/
def ConcaveCRS (hC : Convex ℝ XS) (Γ : XS × Z → Set XS) (F : XS × XS × Z → ℝ) : Prop :=
  ∀ z x y x' y', y ∈ Γ (x, z) → y' ∈ Γ (x', z) → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
    θ * F (x, y, z) + (1 - θ) * F (x', y', z) ≤
      F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y', z) ∧
    (NonProp x x' → θ * F (x, y, z) + (1 - θ) * F (x', y', z) <
      F (cmb hC h0.le h1.le x x', cmb hC h0.le h1.le y y', z))

variable {Γ : XS × Z → Set XS} {F : XS × XS × Z → ℝ} {β α B : ℝ}
variable (Q : Kernel Z Z) [IsMarkovKernel Q]

theorem cmb_one (hC : Convex ℝ XS) (x x' : XS) :
    cmb hC zero_le_one le_rfl x x' = x := Subtype.ext (by simp [cmb])

theorem cmb_zero (hC : Convex ℝ XS) (x x' : XS) :
    cmb hC le_rfl zero_le_one x x' = x' := Subtype.ext (by simp [cmb])

/-- `T` maps functions concave in `x` to functions concave in `x`, strictly along
non-proportional pairs. -/
theorem crsT_concave (hC : Convex ℝ XS) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC XS Q) (hF : ConcaveCRS hC Γ F)
    (h911 : Assumption911 hC hC (Model.first Q Γ F β)) {f : XS × Z → ℝ} (hf : InHS hX f)
    (hconc : ∀ z, IsConcaveS hC fun x => f (x, z)) (z : Z) (x x' : XS) (θ : ℝ) (h0 : 0 < θ)
    (h1 : θ < 1) :
    θ * crsT Q Γ F β f (x, z) + (1 - θ) * crsT Q Γ F β f (x', z) ≤
      crsT Q Γ F β f (cmb hC h0.le h1.le x x', z) ∧
    (NonProp x x' → θ * crsT Q Γ F β f (x, z) + (1 - θ) * crsT Q Γ F β f (x', z) <
      crsT Q Γ F β f (cmb hC h0.le h1.le x x', z)) := by
  obtain ⟨y, hy, hv, -⟩ := exists_crsT_argmax Q h919 h920 hQ hf (x, z)
  obtain ⟨y', hy', hv', -⟩ := exists_crsT_argmax Q h919 h920 hQ hf (x', z)
  obtain ⟨-, -, -, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hf (cmb hC h0.le h1.le x x', z)
  have hyθ := h911 z x y x' y' hy hy' θ h0.le h1.le
  have hE := mul_le_mul_of_nonneg_left
    (ex_9_9_concave hC Q hf hconc z y y' θ h0.le h1.le) h920.β_pos.le
  have hm := hmax _ hyθ
  have hFc := hF z x y x' y' hy hy' θ h0 h1
  dsimp only at hv hv' hm
  rw [hv, hv']
  exact ⟨by nlinarith [hFc.1], fun hnp => by nlinarith [hFc.2 hnp]⟩

/-- **Exercise 9.10b.** If `F(·, ·, z)` is concave on `A_z`, strictly for non-proportional
`x, x′`, and `A_z` is convex, then the fixed point `v(·, z)` is concave, and strictly so along
non-proportional pairs. -/
theorem ex_9_10b (hC : Convex ℝ XS) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC XS Q) (hF : ConcaveCRS hC Γ F)
    (h911 : Assumption911 hC hC (Model.first Q Γ F β)) {v : XS × Z → ℝ} (hvH : InHS hX v)
    (hv : crsT Q Γ F β v = v) :
    (∀ z, IsConcaveS hC fun x => v (x, z)) ∧
      ∀ z x x', NonProp x x' → ∀ (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1),
        θ * v (x, z) + (1 - θ) * v (x', z) < v (cmb hC h0.le h1.le x x', z) := by
  obtain ⟨w, hwH, hw, huniq, hrate, -⟩ := ex_9_10a Q h919 h920 hQ
  obtain rfl := huniq v hvH hv
  set T := crsT Q Γ F β
  have hfull : ∀ f : XS × Z → ℝ, InHS hX f → (∀ z, IsConcaveS hC fun x => f (x, z)) →
      ∀ z, IsConcaveS hC fun x => T f (x, z) := by
    intro f hf hconc z x x' θ h0 h1
    rcases h0.eq_or_lt with rfl | h0'
    · rw [cmb_zero]; simp
    rcases h1.eq_or_lt with rfl | h1'
    · rw [cmb_one]; simp
    exact (crsT_concave Q hC h919 h920 hQ hF h911 hf hconc z x x' θ h0' h1').1
  have hTH : ∀ f, InHS hX f → InHS hX (T f) := fun f hf => crsT_mapsTo Q h919 h920 hQ hf
  have hiter : ∀ n, InHS hX (T^[n] 0) ∧ ∀ z, IsConcaveS hC fun x => T^[n] 0 (x, z) := by
    intro n
    induction n with
    | zero => exact ⟨inHS_zero, fun z x x' θ _ _ => by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hTH _ ih.1, hfull _ ih.1 ih.2⟩
  -- pointwise convergence of the iterates
  have hpt : ∀ p : XS × Z, Tendsto (fun n => T^[n] 0 p) atTop (𝓝 (v p)) := by
    intro p
    have hαβ : 0 ≤ α * β := mul_nonneg h919.α_pos.le h920.β_pos.le
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => ?_) (((tendsto_pow_atTop_nhds_zero_of_lt_one hαβ h919.αβ_lt).mul_const
        (hnormS XS (0 - v) * ‖p.1.1‖)).trans_eq (by simp)))
    rw [Real.dist_eq]
    have := abs_le_hnormS' (inHS_sub (hiter n).1 hvH) p
    simp only [Pi.sub_apply] at this
    refine this.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrate 0 inHS_zero n) (norm_nonneg _)
  have hconc : ∀ z, IsConcaveS hC fun x => v (x, z) := fun z x x' θ h0 h1 =>
    le_of_tendsto_of_tendsto' (((hpt (x, z)).const_mul θ).add ((hpt (x', z)).const_mul _))
      (hpt _) fun n => (hiter n).2 z x x' θ h0 h1
  refine ⟨hconc, fun z x x' hnp θ h0 h1 => ?_⟩
  have := (crsT_concave Q hC h919 h920 hQ hF h911 hvH hconc z x x' θ h0 h1).2 hnp
  change θ * T v (x, z) + (1 - θ) * T v (x', z) < T v (cmb hC h0.le h1.le x x', z) at this
  rwa [hw] at this

omit [OpensMeasurableSpace Z] in
/-- **Exercise 9.10c (monotonicity).** Under Assumptions 9.8 and 9.9, `v(·, z)` is strictly
increasing. -/
theorem ex_9_10c_mono (h919 : Assume919 hX Γ β α) (h920 : Assume920 hX Γ F β B)
    (hQ : PreservesBC XS Q)
    (h98 : ∀ x x' y z, x < x' → y ∈ Γ (x, z) → F (x, y, z) < F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → Γ (x, z) ⊆ Γ (x', z)) {v : XS × Z → ℝ} (hvH : InHS hX v)
    (hv : crsT Q Γ F β v = v) (z : Z) : StrictMono fun x => v (x, z) := by
  intro x x' hxx'
  obtain ⟨y, hy, hval, -⟩ := exists_crsT_argmax Q h919 h920 hQ hvH (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_crsT_argmax Q h919 h920 hQ hvH (x', z)
  rw [congrFun hv] at hval hmax
  have := hmax y (h99 x x' z hxx'.le hy)
  dsimp only at hval this ⊢
  rw [hval]
  linarith [h98 x x' y z hxx' hy]

/-- **Exercise 9.10c (differentiability).** Under the hypotheses of Exercise 9.10b, if
`x₀ ∈ int X`, `y₀ ∈ G(x₀, z₀)` lies in the interior of `Γ(x₀, z₀)`, and `F(·, y₀, z₀)` has
derivative `DF` at `x₀`, then `v(·, z₀)` is differentiable at `x₀` with derivative `DF`. -/
theorem ex_9_10c_diff (hC : Convex ℝ XS) (h919 : Assume919 hX Γ β α)
    (h920 : Assume920 hX Γ F β B) (hQ : PreservesBC XS Q) (hF : ConcaveCRS hC Γ F)
    (h911 : Assumption911 hC hC (Model.first Q Γ F β)) {v : XS × Z → ℝ} (hvH : InHS hX v)
    (hv : crsT Q Γ F β v = v) {x₀ : XS} {z₀ : Z} (hint : XS ∈ 𝓝 x₀.1) {y₀ : XS}
    (hy₀ : y₀ ∈ argmax (objG (Model.first Q Γ F β) v) Γ (x₀, z₀))
    (hg : y₀.1 ∈ interior (Subtype.val '' Γ (x₀, z₀))) {DF : (Fin l → ℝ) →L[ℝ] ℝ}
    (hFd : HasFDerivAt (liftS fun x => F (x, y₀, z₀)) DF x₀.1) :
    HasFDerivAt (liftS fun x => v (x, z₀)) DF x₀.1 := by
  have hvc := (ex_9_10b Q hC h919 h920 hQ hF h911 hvH hv).1 z₀
  set c := β * mop Q v (y₀, z₀)
  set W : (Fin l → ℝ) → ℝ := fun x => liftS (fun x => F (x, y₀, z₀)) x + c
  have hW : HasFDerivAt W DF x₀.1 := hFd.add_const c
  have hvx : ∀ s, v s = maxValue (objG (Model.first Q Γ F β) v) Γ s := fun s =>
    (congrFun hv s).symm
  have heq : W x₀.1 = liftS (fun x => v (x, z₀)) x₀.1 := by
    simp only [W, liftS_of_mem _ x₀.2, Subtype.coe_eta]
    rw [hvx (x₀, z₀), ← hy₀.2, objG_first]
  have hle : ∀ᶠ x in 𝓝 x₀.1, W x ≤ liftS (fun x => v (x, z₀)) x := by
    have h1 := eventually_mem_Γ (Model.first Q Γ F β) h919.lhc h911 hg
    rw [nhds_subtype, eventually_comap] at h1
    filter_upwards [h1, hint] with x hx hxS
    simp only [W, liftS_of_mem _ hxS]
    rw [hvx (⟨x, hxS⟩, z₀)]
    have := le_maxValue (continuousOn_objG_crs Q h920 hQ hvH) (h919.compact _)
      (hx ⟨x, hxS⟩ rfl)
    rwa [objG_first] at this
  exact theorem_4_10 (concaveOn_liftS hvc) hint hW heq hle

end StokeyLucasPrescott.StochasticDP
