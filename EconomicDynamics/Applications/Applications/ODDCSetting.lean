/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.BRContraction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Group.Integral

/-!
# Discrete choice: the Bellman equation of Rust's replacement problem

Miao, §8.2, pp. 234–235. The state `s ≥ 0` is the accumulated utilization of a durable good. If
the durable is maintained, utilization grows by an exponential increment with rate `λ > 0`, so
the next state has density `λ exp(−λ(s′ − s))` on `(s, ∞)`; replacing costs `P_b − P_s` and
restarts from `s = 0`. The Bellman equation is (`od_DCBellman`)
`V(s) = max{−c(s) + β ∫_s^∞ V(s′) λe^{−λ(s′ − s)} ds′,
  −(P_b − P_s) − c(0) + β ∫_0^∞ V(s′) λe^{−λs′} ds′}`.
We write the expectation as `E f(s) = ∫_{x > 0} f(s + x) λe^{−λx} dx` (`od_dcE`), which is the
book's integral (`od_dcE_book`); `od_dcM` and `od_dcR` are the maintenance and replacement
values.

* `od_dc_exists`: for bounded continuous `c` and `β ∈ (0, 1)`, the Bellman operator `od_dcT` is
  a contraction of `C(ℝ)` (Blackwell's conditions), so the Bellman equation has a bounded
  continuous solution.
* `od_dc_unique`: two bounded continuous solutions agree on `[0, ∞)`.
* `od_dc_antitone` (p. 235, Figure 8.2): if `c` is increasing on `[0, ∞)`, `V` is decreasing (and
  continuous) on `[0, ∞)`.

The book's `c` is defined on `[0, ∞)`; here `c` is a bounded continuous function on `ℝ` (any
such function on `[0, ∞)` extends), and only its values on `[0, ∞)` enter the equation on
`[0, ∞)`.
-/

namespace Miao.Applications

open MeasureTheory Real BoundedContinuousFunction

/-- The exponential density `λe^{−λx}`. -/
noncomputable def od_dcp (lam x : ℝ) : ℝ := lam * exp (-(lam * x))

/-- The expectation of `f` at the next state, `E f(s) = ∫_{x > 0} f(s + x) λe^{−λx} dx`. -/
noncomputable def od_dcE (lam : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, f (s + x) * od_dcp lam x

/-- The value of maintaining the durable, `−c(s) + β E V(s)`. -/
noncomputable def od_dcM (c : ℝ → ℝ) (lam β : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  -c s + β * od_dcE lam f s

/-- The value of replacing the durable, `−(P_b − P_s) − c(0) + β E V(0)`; it does not depend
on the state. -/
noncomputable def od_dcR (c : ℝ → ℝ) (lam β Pb Ps : ℝ) (f : ℝ → ℝ) : ℝ :=
  -(Pb - Ps) - c 0 + β * od_dcE lam f 0

/-- The Bellman equation of the discrete choice problem (Miao, p. 234) on `[0, ∞)`. -/
def od_DCBellman (c : ℝ → ℝ) (lam β Pb Ps : ℝ) (V : ℝ → ℝ) : Prop :=
  ∀ s, 0 ≤ s → V s = max (od_dcM c lam β V s) (od_dcR c lam β Pb Ps V)

theorem od_dcp_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 < od_dcp lam x :=
  mul_pos hlam (exp_pos _)

theorem od_dcp_continuous (lam : ℝ) : Continuous (od_dcp lam) := by
  unfold od_dcp; fun_prop

theorem od_dcp_integrable {lam : ℝ} (hlam : 0 < lam) : IntegrableOn (od_dcp lam) (Set.Ioi 0) := by
  have : od_dcp lam = fun x => lam * exp (-lam * x) := by
    funext x; simp only [od_dcp, neg_mul]
  rw [this]
  exact (exp_neg_integrableOn_Ioi 0 hlam).const_mul lam

/-- The density integrates to one. -/
theorem od_dcp_integral {lam : ℝ} (hlam : 0 < lam) : ∫ x in Set.Ioi 0, od_dcp lam x = 1 := by
  have h := integral_exp_mul_Ioi (a := -lam) (by linarith) 0
  simp only [mul_zero, exp_zero] at h
  unfold od_dcp
  rw [integral_const_mul]
  simp only [← neg_mul]
  rw [h]
  field_simp

theorem od_dcE_integrable {lam : ℝ} (hlam : 0 < lam) (f : ℝ →ᵇ ℝ) (s : ℝ) :
    IntegrableOn (fun x => f (s + x) * od_dcp lam x) (Set.Ioi 0) := by
  refine Integrable.mono' ((od_dcp_integrable hlam).const_mul ‖f‖) ?_ ?_
  · exact ((f.continuous.comp (continuous_const.add continuous_id)).mul
      (od_dcp_continuous lam)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_of_nonneg (od_dcp_pos hlam x).le]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (od_dcp_pos hlam x).le

/-- The expectation of a constant is the constant. -/
theorem od_dcE_const {lam : ℝ} (hlam : 0 < lam) (a s : ℝ) : od_dcE lam (fun _ => a) s = a := by
  unfold od_dcE
  rw [integral_const_mul, od_dcp_integral hlam, mul_one]

/-- The expectation is monotone: `E f(t) ≤ E g(s)` if `f(t + x) ≤ g(s + x)` for `x > 0`. -/
theorem od_dcE_mono' {lam : ℝ} (hlam : 0 < lam) {f g : ℝ →ᵇ ℝ} {s t : ℝ}
    (hfg : ∀ x, 0 < x → f (t + x) ≤ g (s + x)) : od_dcE lam f t ≤ od_dcE lam g s :=
  setIntegral_mono_on (od_dcE_integrable hlam f t) (od_dcE_integrable hlam g s) measurableSet_Ioi
    fun x hx => mul_le_mul_of_nonneg_right (hfg x hx) (od_dcp_pos hlam x).le

/-- The expectation is monotone in the values on `(s, ∞)`. -/
theorem od_dcE_mono {lam : ℝ} (hlam : 0 < lam) {f g : ℝ →ᵇ ℝ} {s : ℝ}
    (hfg : ∀ x, 0 < x → f (s + x) ≤ g (s + x)) : od_dcE lam f s ≤ od_dcE lam g s :=
  od_dcE_mono' hlam hfg

/-- `E(f + a) = E f + a`. -/
theorem od_dcE_add_const {lam : ℝ} (hlam : 0 < lam) (f : ℝ →ᵇ ℝ) (a s : ℝ) :
    od_dcE lam (fun y => f y + a) s = od_dcE lam f s + a := by
  unfold od_dcE
  have : (fun x => (f (s + x) + a) * od_dcp lam x) =
      fun x => f (s + x) * od_dcp lam x + a * od_dcp lam x := by funext x; ring
  rw [this, integral_add (od_dcE_integrable hlam f s) ((od_dcp_integrable hlam).const_mul a),
    integral_const_mul, od_dcp_integral hlam, mul_one]

/-- `|E f(s) − E g(s)| ≤ D` when `|f − g| ≤ D` on `(s, ∞)`. -/
theorem od_dcE_abs_sub_le {lam : ℝ} (hlam : 0 < lam) (f g : ℝ →ᵇ ℝ) {s D : ℝ}
    (hD : ∀ x, 0 < x → |f (s + x) - g (s + x)| ≤ D) : |od_dcE lam f s - od_dcE lam g s| ≤ D := by
  unfold od_dcE
  rw [← integral_sub (od_dcE_integrable hlam f s) (od_dcE_integrable hlam g s)]
  have hi : IntegrableOn (fun x => f (s + x) * od_dcp lam x - g (s + x) * od_dcp lam x)
      (Set.Ioi 0) := (od_dcE_integrable hlam f s).sub (od_dcE_integrable hlam g s)
  calc |∫ x in Set.Ioi 0, (f (s + x) * od_dcp lam x - g (s + x) * od_dcp lam x)|
      ≤ ∫ x in Set.Ioi 0, |f (s + x) * od_dcp lam x - g (s + x) * od_dcp lam x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in Set.Ioi 0, D * od_dcp lam x := by
        refine setIntegral_mono_on hi.abs ((od_dcp_integrable hlam).const_mul D)
          measurableSet_Ioi fun x hx => ?_
        rw [← sub_mul, abs_mul, abs_of_pos (od_dcp_pos hlam x)]
        exact mul_le_mul_of_nonneg_right (hD x hx) (od_dcp_pos hlam x).le
    _ = D := by rw [integral_const_mul, od_dcp_integral hlam, mul_one]

/-- `|E f(s)| ≤ ‖f‖`. -/
theorem od_dcE_abs_le {lam : ℝ} (hlam : 0 < lam) (f : ℝ →ᵇ ℝ) (s : ℝ) :
    |od_dcE lam f s| ≤ ‖f‖ := by
  have h := od_dcE_abs_sub_le hlam f 0 (s := s) (D := ‖f‖) fun x _ => by
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, sub_zero]
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
  have h0 : od_dcE lam (⇑(0 : ℝ →ᵇ ℝ)) s = 0 := by
    simp [od_dcE]
  rwa [h0, sub_zero] at h

/-- `s ↦ E f(s)` is continuous for bounded continuous `f`. -/
theorem od_dcE_continuous {lam : ℝ} (hlam : 0 < lam) (f : ℝ →ᵇ ℝ) :
    Continuous (od_dcE lam f) := by
  refine continuous_of_dominated (bound := fun x => ‖f‖ * od_dcp lam x) (fun s => ?_)
    (fun s => Filter.Eventually.of_forall fun x => ?_) ((od_dcp_integrable hlam).const_mul _)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((f.continuous.comp (continuous_const.add continuous_id)).mul
      (od_dcp_continuous lam)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_of_nonneg (od_dcp_pos hlam x).le]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (od_dcp_pos hlam x).le
  · exact (f.continuous.comp (continuous_id.add continuous_const)).mul continuous_const

/-- Miao, p. 234: `E f(s)` is the book's integral `∫_s^∞ f(s′) λe^{−λ(s′ − s)} ds′`. -/
theorem od_dcE_book (lam : ℝ) (f : ℝ → ℝ) (s : ℝ) :
    od_dcE lam f s = ∫ s' in Set.Ioi s, f s' * (lam * exp (-(lam * (s' - s)))) := by
  unfold od_dcE
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun y => (Set.Ioi s).indicator (fun s' => f s' * (lam * exp (-(lam * (s' - s))))) y) s]
  congr 1
  funext x
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx),
      Set.indicator_of_mem (Set.mem_Ioi.2 (by linarith : s < s + x))]
    simp only [od_dcp, add_sub_cancel_left]
  · rw [Set.indicator_of_notMem (by simpa using hx),
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith [not_lt.1 hx])]

/-- If `f` is decreasing on `[0, ∞)`, so is `E f`. -/
theorem od_dcE_antitoneOn {lam : ℝ} (hlam : 0 < lam) {f : ℝ →ᵇ ℝ}
    (hf : AntitoneOn f (Set.Ici 0)) : AntitoneOn (od_dcE lam f) (Set.Ici 0) :=
  fun s hs t _ hst => od_dcE_mono' hlam fun x hx =>
    hf (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 hs]))
      (Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 hs])) (by linarith)

/-- The Bellman operator of the discrete choice problem on `C(ℝ)`. -/
noncomputable def od_dcT {lam : ℝ} (hlam : 0 < lam) (c : ℝ →ᵇ ℝ) (β Pb Ps : ℝ) (f : ℝ →ᵇ ℝ) :
    ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => max (od_dcM c lam β f s) (od_dcR c lam β Pb Ps f))
    ((c.continuous.neg.add (continuous_const.mul (od_dcE_continuous hlam f))).max
      continuous_const)
    (|Pb - Ps| + ‖c‖ + |β| * ‖f‖) fun s => by
      rw [Real.norm_eq_abs]
      have hE : ∀ t, |β * od_dcE lam f t| ≤ |β| * ‖f‖ := fun t => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (od_dcE_abs_le hlam f t) (abs_nonneg _)
      have hc : ∀ t, |c t| ≤ ‖c‖ := fun t => by
        rw [← Real.norm_eq_abs]; exact c.norm_coe_le_norm t
      have h1 : |od_dcM c lam β f s| ≤ |Pb - Ps| + ‖c‖ + |β| * ‖f‖ := by
        unfold od_dcM
        have := abs_add_le (-c s) (β * od_dcE lam f s)
        rw [abs_neg] at this
        linarith [hc s, hE s, abs_nonneg (Pb - Ps)]
      have h2 : |od_dcR c lam β Pb Ps f| ≤ |Pb - Ps| + ‖c‖ + |β| * ‖f‖ := by
        unfold od_dcR
        have h3 := abs_add_le (-(Pb - Ps) - c 0) (β * od_dcE lam f 0)
        have h4 := abs_sub (-(Pb - Ps)) (c 0)
        rw [abs_neg] at h4
        linarith [hc 0, hE 0]
      exact abs_max_le_max_abs_abs.trans (max_le h1 h2)

theorem od_dcT_apply {lam : ℝ} (hlam : 0 < lam) (c : ℝ →ᵇ ℝ) (β Pb Ps : ℝ) (f : ℝ →ᵇ ℝ)
    (s : ℝ) : od_dcT hlam c β Pb Ps f s = max (od_dcM c lam β f s) (od_dcR c lam β Pb Ps f) :=
  rfl

/-- The Bellman operator is a contraction of modulus `β` (Blackwell's conditions). -/
theorem od_dcT_contraction {lam : ℝ} (hlam : 0 < lam) (c : ℝ →ᵇ ℝ) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (Pb Ps : ℝ) : br_IsContraction (od_dcT hlam c β Pb Ps) β := by
  refine ⟨hβ0, hβ1, br_blackwell hβ0.le (fun f g hfg s => ?_) (fun f a ha s => ?_)⟩
  · change od_dcT hlam c β Pb Ps f s ≤ od_dcT hlam c β Pb Ps g s
    rw [od_dcT_apply, od_dcT_apply]
    unfold od_dcM od_dcR
    exact max_le_max
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (od_dcE_mono hlam fun x _ => hfg _) hβ0.le))
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (od_dcE_mono hlam fun x _ => hfg _) hβ0.le))
  · change od_dcT hlam c β Pb Ps (f + const ℝ a) s ≤ od_dcT hlam c β Pb Ps f s + β * a
    rw [od_dcT_apply, od_dcT_apply]
    have hE : ∀ t, od_dcE lam (⇑(f + const ℝ a)) t = od_dcE lam f t + a := fun t => by
      rw [← od_dcE_add_const hlam f a t]; rfl
    unfold od_dcM od_dcR
    rw [hE, hE]
    have hβa : 0 ≤ β * a := mul_nonneg hβ0.le ha
    rcases le_total (-c s + β * od_dcE lam f s) (-(Pb - Ps) - c 0 + β * od_dcE lam f 0)
      with h | h
    · rw [max_eq_right h]; exact max_le (by nlinarith) (by nlinarith)
    · rw [max_eq_left h]; exact max_le (by nlinarith) (by nlinarith)

/-- Miao, p. 235 ("by the dynamic programming theory with bounded reward"): for bounded continuous
`c`, `λ > 0` and `β ∈ (0, 1)`, the Bellman equation has a bounded continuous solution, the fixed
point of the contraction `od_dcT`. -/
theorem od_dc_exists {lam : ℝ} (hlam : 0 < lam) (c : ℝ →ᵇ ℝ) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (Pb Ps : ℝ) :
    ∃ V : ℝ →ᵇ ℝ, od_dcT hlam c β Pb Ps V = V ∧ od_DCBellman c lam β Pb Ps V := by
  obtain ⟨V, hV, -, -⟩ := br_theorem_3_2 (od_dcT_contraction hlam c hβ0 hβ1 Pb Ps)
  refine ⟨V, hV, fun s _ => ?_⟩
  rw [← od_dcT_apply hlam c β Pb Ps V s, hV]

/-- Miao, p. 235: the bounded continuous solution is unique on `[0, ∞)`. -/
theorem od_dc_unique {lam : ℝ} (hlam : 0 < lam) {c : ℝ → ℝ} {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {Pb Ps : ℝ} {V₁ V₂ : ℝ →ᵇ ℝ} (h₁ : od_DCBellman c lam β Pb Ps V₁)
    (h₂ : od_DCBellman c lam β Pb Ps V₂) : ∀ s, 0 ≤ s → V₁ s = V₂ s := by
  have hbdd : BddAbove (Set.range fun s : Set.Ici (0 : ℝ) => |V₁ s - V₂ s|) :=
    ⟨dist V₁ V₂, by
      rintro _ ⟨s, rfl⟩
      change |V₁ s - V₂ s| ≤ _
      rw [← Real.dist_eq]; exact dist_coe_le_dist _⟩
  set D := ⨆ s : Set.Ici (0 : ℝ), |V₁ s - V₂ s|
  have hle : ∀ s, 0 ≤ s → |V₁ s - V₂ s| ≤ D := fun s hs =>
    le_ciSup hbdd (⟨s, hs⟩ : Set.Ici (0 : ℝ))
  have hE : ∀ s, 0 ≤ s → |od_dcE lam V₁ s - od_dcE lam V₂ s| ≤ D := fun s hs =>
    od_dcE_abs_sub_le hlam V₁ V₂ fun x hx => hle _ (by linarith)
  have hstep : ∀ s, 0 ≤ s → |V₁ s - V₂ s| ≤ β * D := fun s hs => by
    rw [h₁ s hs, h₂ s hs]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · unfold od_dcM
      rw [show -c s + β * od_dcE lam V₁ s - (-c s + β * od_dcE lam V₂ s) =
        β * (od_dcE lam V₁ s - od_dcE lam V₂ s) by ring, abs_mul, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left (hE s hs) hβ0.le
    · unfold od_dcR
      rw [show -(Pb - Ps) - c 0 + β * od_dcE lam V₁ 0 - (-(Pb - Ps) - c 0 + β * od_dcE lam V₂ 0)
        = β * (od_dcE lam V₁ 0 - od_dcE lam V₂ 0) by ring, abs_mul, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left (hE 0 le_rfl) hβ0.le
  have hD : D ≤ β * D := ciSup_le fun s => hstep s s.2
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hle 0 le_rfl)
  have hDz : D = 0 := by nlinarith
  intro s hs
  have := hle s hs
  rw [hDz] at this
  linarith [abs_nonneg (V₁ s - V₂ s), abs_sub_lt_iff.1 (lt_of_le_of_lt this zero_lt_one),
    abs_le.1 this]

/-- **Figure 8.2** (Miao, p. 235): if `c` is increasing on `[0, ∞)`, every bounded continuous
solution of the Bellman equation is decreasing on `[0, ∞)` (Closed Subspace Theorem). -/
theorem od_dc_antitone {lam : ℝ} (hlam : 0 < lam) {c : ℝ →ᵇ ℝ} (hc : MonotoneOn c (Set.Ici 0))
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pb Ps : ℝ} {V : ℝ →ᵇ ℝ}
    (hV : od_DCBellman c lam β Pb Ps V) : AntitoneOn V (Set.Ici 0) := by
  obtain ⟨V₀, hV₀, hB₀⟩ := od_dc_exists hlam c hβ0 hβ1 Pb Ps
  set S' : Set (ℝ →ᵇ ℝ) := {f | AntitoneOn f (Set.Ici 0)}
  have hclosed : IsClosed S' := by
    have : S' = ⋂ x ∈ Set.Ici (0 : ℝ), ⋂ y ∈ Set.Ici (0 : ℝ), ⋂ (_ : x ≤ y),
        {f : ℝ →ᵇ ℝ | f y ≤ f x} := by
      ext f; simp [S', AntitoneOn]
    rw [this]
    exact isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const y) (continuous_eval_const x)
  have hne : S'.Nonempty := ⟨0, fun _ _ _ _ _ => le_rfl⟩
  have hmaps : Set.MapsTo (od_dcT hlam c β Pb Ps) S' S' := fun f hf x hx y hy hxy => by
    change od_dcT hlam c β Pb Ps f y ≤ od_dcT hlam c β Pb Ps f x
    rw [od_dcT_apply, od_dcT_apply]
    unfold od_dcM
    exact max_le_max (add_le_add (neg_le_neg (hc hx hy hxy))
      (mul_le_mul_of_nonneg_left (od_dcE_antitoneOn hlam hf hx hy hxy) hβ0.le)) le_rfl
  have hV₀m : AntitoneOn V₀ (Set.Ici 0) :=
    (br_corollary_1 (od_dcT_contraction hlam c hβ0 hβ1 Pb Ps) hV₀ hne hclosed hmaps hmaps).1
  have heq := od_dc_unique hlam hβ0 hβ1 hV hB₀
  intro x hx y hy hxy
  rw [heq x hx, heq y hy]
  exact hV₀m hx hy hxy

end Miao.Applications
