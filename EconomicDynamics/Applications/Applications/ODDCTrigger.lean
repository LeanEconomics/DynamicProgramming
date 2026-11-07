/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.ODDCSetting
import Mathlib.Topology.Order.IntermediateValue

/-!
# Discrete choice: the replacement trigger and the boundary conditions (8.2)

Miao, §8.2, pp. 235–236. Throughout `λ > 0`, `β ∈ (0, 1)`, `P_b > P_s`, `c` is bounded,
continuous and strictly increasing on `[0, ∞)`, and `V` is the bounded continuous solution of the
Bellman equation (decreasing on `[0, ∞)` by `od_dc_antitone`).

* `od_dc_no_replace_zero` (p. 235): at `s = 0` maintaining beats replacing by `P_b − P_s > 0`.
* `od_dcM_strictAntiOn`: the maintenance value is strictly decreasing on `[0, ∞)`, while the
  replacement value `od_dcR` does not depend on `s`; so there is at most one indifference point.
* `od_dc_trigger` (pp. 235–236): if `s*` is an indifference point, then `s* > 0`, maintaining is
  strictly optimal on `[0, s*)` and replacing is strictly optimal on `(s*, ∞)`, `V = −c(s*)/(1 − β)`
  on `[s*, ∞)`, and `s*` is the only indifference point (in particular the smallest).
* `eq_8_2` (p. 236): the chain `V(0) = −c(0) + β∫V λe^{−λs′}`, `V(s*) = −(P_b − P_s) + V(0)`,
  `V(s*) = −c(s*) + βV(s*)`, hence (8.2): `V(s*) = −c(s*)/(1 − β)`,
  `V(0) = (P_b − P_s) − c(s*)/(1 − β)`.

**Correction (existence of `s*`).** The book takes "the smaller value `s*` such that the decision
maker is indifferent" for granted. It exists when the cost rises by more than the net replacement
price, `c(s₁) − c(0) > P_b − P_s` for some `s₁` (`od_dc_trigger_exists`, by the intermediate value
theorem), but not when `c(s) − c(0) ≤ D < (1 − β)(P_b − P_s)` for all `s`: then maintaining is
strictly optimal at every `s ≥ 0` and the durable is never replaced (`od_dc_no_trigger`).
-/

namespace Miao.Applications

open MeasureTheory Real BoundedContinuousFunction

variable {lam β Pb Ps : ℝ} {c : ℝ →ᵇ ℝ} {V : ℝ →ᵇ ℝ}

/-- Miao, p. 235 ("since `P_b > P_s`, it is never optimal to replace the new durable when
`s = 0`"): `R < M(0)` and `V(0) = M(0)`. -/
theorem od_dc_no_replace_zero (hPb : Ps < Pb) (hV : od_DCBellman c lam β Pb Ps V) :
    od_dcR c lam β Pb Ps V < od_dcM c lam β V 0 ∧ V 0 = od_dcM c lam β V 0 := by
  have h : od_dcR c lam β Pb Ps V < od_dcM c lam β V 0 := by
    unfold od_dcR od_dcM; linarith
  exact ⟨h, by rw [hV 0 le_rfl, max_eq_left h.le]⟩

/-- The maintenance value is strictly decreasing on `[0, ∞)`. -/
theorem od_dcM_strictAntiOn (hlam : 0 < lam) (hβ0 : 0 < β) (hc : StrictMonoOn c (Set.Ici 0))
    (hV : AntitoneOn V (Set.Ici 0)) : StrictAntiOn (od_dcM c lam β V) (Set.Ici 0) := by
  intro s hs t ht hst
  unfold od_dcM
  have h1 := hc hs ht hst
  have h2 := od_dcE_antitoneOn hlam hV hs ht hst.le
  nlinarith [mul_le_mul_of_nonneg_left h2 hβ0.le]

/-- Miao, pp. 235–236: the replacement trigger. If `s* ≥ 0` is an indifference point, then
`s* > 0`; on `[0, s*)` maintaining is strictly optimal and `V = M`; on `(s*, ∞)` replacing is
strictly optimal; `V = R` on `[s*, ∞)`; and `s*` is the only indifference point in `[0, ∞)`. -/
theorem od_dc_trigger (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    0 < ss ∧
      (∀ s, 0 ≤ s → s < ss → od_dcR c lam β Pb Ps V < od_dcM c lam β V s ∧
        V s = od_dcM c lam β V s) ∧
      (∀ s, ss < s → od_dcM c lam β V s < od_dcR c lam β Pb Ps V) ∧
      (∀ s, ss ≤ s → V s = od_dcR c lam β Pb Ps V) ∧
      (∀ t, 0 ≤ t → od_dcM c lam β V t = od_dcR c lam β Pb Ps V → t = ss) := by
  have hanti := od_dcM_strictAntiOn hlam hβ0 hc (od_dc_antitone hlam hc.monotoneOn hβ0 hβ1 hV)
  have h0 := (od_dc_no_replace_zero hPb hV).1
  have hpos : 0 < ss := by
    rcases hss.lt_or_eq with h | h
    · exact h
    · rw [← h] at hind; linarith
  have hlt : ∀ s, 0 ≤ s → s < ss → od_dcR c lam β Pb Ps V < od_dcM c lam β V s := fun s hs h => by
    rw [← hind]; exact hanti hs hss h
  have hgt : ∀ s, ss < s → od_dcM c lam β V s < od_dcR c lam β Pb Ps V := fun s h => by
    rw [← hind]; exact hanti hss (by simp only [Set.mem_Ici]; linarith) h
  refine ⟨hpos, fun s hs h => ⟨hlt s hs h, by rw [hV s hs, max_eq_left (hlt s hs h).le]⟩, hgt,
    fun s h => ?_, fun t ht htind => ?_⟩
  · rcases h.lt_or_eq with h | h
    · rw [hV s (by linarith), max_eq_right (hgt s h).le]
    · rw [← h, hV ss hss, hind, max_self]
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · linarith [hlt t ht h]
    · linarith [hgt t h]

/-- **(8.2)** (Miao, p. 236), with the chain of equalities leading to it: at the trigger `s*`,
`V(0) = −c(0) + β ∫ V λe^{−λs′}`, `V(s*) = −(P_b − P_s) + V(0)`, `V(s*) = −c(s*) + βV(s*)`, so
`V(s*) = −c(s*)/(1 − β)` and `V(0) = (P_b − P_s) − c(s*)/(1 − β)`. -/
theorem eq_8_2 (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : StrictMonoOn c (Set.Ici 0)) (hV : od_DCBellman c lam β Pb Ps V) {ss : ℝ} (hss : 0 ≤ ss)
    (hind : od_dcM c lam β V ss = od_dcR c lam β Pb Ps V) :
    V 0 = -c 0 + β * ∫ s' in Set.Ioi 0, V s' * (lam * exp (-(lam * s'))) ∧
      V ss = -(Pb - Ps) + V 0 ∧ V ss = -c ss + β * V ss ∧
      V ss = -c ss / (1 - β) ∧ V 0 = (Pb - Ps) - c ss / (1 - β) := by
  obtain ⟨-, -, -, hR, -⟩ := od_dc_trigger hlam hβ0 hβ1 hPb hc hV hss hind
  have hV0 := (od_dc_no_replace_zero hPb hV).2
  have h1 : V 0 = -c 0 + β * ∫ s' in Set.Ioi 0, V s' * (lam * exp (-(lam * s'))) := by
    rw [hV0, od_dcM, od_dcE_book]
    simp only [sub_zero]
  have h2 : V ss = -(Pb - Ps) + V 0 := by
    rw [hR ss le_rfl, hV0, od_dcR, od_dcM]; ring
  have hE : od_dcE lam V ss = V ss := by
    have : od_dcE lam V ss = od_dcE lam (fun _ => od_dcR c lam β Pb Ps V) ss :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => by
        simp only
        rw [hR (ss + x) (by linarith [Set.mem_Ioi.1 hx])]
    rw [this, od_dcE_const hlam, ← hR ss le_rfl]
  have h3 : V ss = -c ss + β * V ss := by
    conv_rhs => rw [← hE]
    exact (hR ss le_rfl).trans hind.symm
  have hne : 1 - β ≠ 0 := by linarith
  have h4 : V ss = -c ss / (1 - β) := by
    rw [eq_div_iff hne]; linarith
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [neg_div] at h4
  linarith

/-- Miao, p. 235 (existence of the trigger): if `c(s₁) − c(0) > P_b − P_s` for some `s₁ ≥ 0`,
then there is an indifference point `s* ∈ (0, s₁)`. -/
theorem od_dc_trigger_exists (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : MonotoneOn c (Set.Ici 0)) (hV : od_DCBellman c lam β Pb Ps V) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hjump : Pb - Ps < c s₁ - c 0) :
    ∃ ss ∈ Set.Ioo 0 s₁, od_dcM c lam β V ss = od_dcR c lam β Pb Ps V := by
  set g := fun s => od_dcM c lam β V s - od_dcR c lam β Pb Ps V
  have hg : Continuous g :=
    (c.continuous.neg.add (continuous_const.mul (od_dcE_continuous hlam V))).sub continuous_const
  have hg0 : 0 < g 0 := by
    have := (od_dc_no_replace_zero hPb hV).1; simp only [g]; linarith
  have hE : od_dcE lam V s₁ ≤ od_dcE lam V 0 :=
    od_dcE_antitoneOn hlam (od_dc_antitone hlam hc hβ0 hβ1 hV) (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 hs₁) hs₁
  have hg1 : g s₁ < 0 := by
    simp only [g, od_dcM, od_dcR]
    nlinarith [mul_le_mul_of_nonneg_left hE hβ0.le]
  obtain ⟨ss, hss, hgss⟩ := intermediate_value_Icc' hs₁ hg.continuousOn
    (⟨hg1.le, hg0.le⟩ : (0 : ℝ) ∈ Set.Icc (g s₁) (g 0))
  refine ⟨ss, ⟨?_, ?_⟩, by simp only [g] at hgss; linarith⟩
  · rcases hss.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hgss; linarith
  · rcases hss.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hgss; linarith

/-- Miao, p. 235, counterexample to the existence of the trigger: if the cost rises by at most
`D < (1 − β)(P_b − P_s)` on `[0, ∞)`, maintaining is strictly optimal at every `s ≥ 0`; there is
no indifference point and the durable is never replaced. -/
theorem od_dc_no_trigger (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) (hPb : Ps < Pb)
    (hc : MonotoneOn c (Set.Ici 0)) (hV : od_DCBellman c lam β Pb Ps V) {D : ℝ}
    (hD : ∀ s, 0 ≤ s → c s - c 0 ≤ D) (hDlt : D < (1 - β) * (Pb - Ps)) :
    ∀ s, 0 ≤ s → od_dcR c lam β Pb Ps V < od_dcM c lam β V s := by
  have hanti := od_dc_antitone hlam hc hβ0 hβ1 hV
  have hbdd : BddBelow (Set.range fun s : Set.Ici (0 : ℝ) => V s) :=
    ⟨-‖V‖, by
      rintro _ ⟨s, rfl⟩
      have := (abs_le.1 ((Real.norm_eq_abs _).symm ▸ V.norm_coe_le_norm s)).1
      exact this⟩
  set m := ⨅ s : Set.Ici (0 : ℝ), V s
  have hm : ∀ s, 0 ≤ s → m ≤ V s := fun s hs => ciInf_le hbdd (⟨s, hs⟩ : Set.Ici (0 : ℝ))
  have hEm : ∀ s, 0 ≤ s → m ≤ od_dcE lam V s := fun s hs => by
    have h := od_dcE_mono' hlam (f := const ℝ m) (g := V) (s := s) (t := s) fun x hx =>
      hm _ (by linarith)
    have hc' : od_dcE lam (⇑(const ℝ m)) s = m := od_dcE_const hlam m s
    linarith
  have hE0 : od_dcE lam V 0 ≤ V 0 := by
    have h := od_dcE_mono' hlam (f := V) (g := const ℝ (V 0)) (s := 0) (t := 0) fun x hx =>
      hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith)) (by linarith)
    have hc' : od_dcE lam (⇑(const ℝ (V 0))) 0 = V 0 := od_dcE_const hlam (V 0) 0
    linarith
  have hV0 := (od_dc_no_replace_zero hPb hV).2
  have hup : (1 - β) * V 0 ≤ -c 0 := by
    rw [hV0] at hE0 ⊢; unfold od_dcM at hE0 ⊢; nlinarith [mul_le_mul_of_nonneg_left hE0 hβ0.le]
  have hlow : ∀ s, 0 ≤ s → -(c 0 + D) + β * m ≤ V s := fun s hs => by
    rw [hV s hs]
    refine le_trans ?_ (le_max_left _ _)
    unfold od_dcM
    nlinarith [hD s hs, mul_le_mul_of_nonneg_left (hEm s hs) hβ0.le]
  have hmlow : -(c 0 + D) + β * m ≤ m := le_ciInf fun s => hlow s s.2
  have hgap : (1 - β) * (V 0 - m) ≤ D := by nlinarith
  have hpos : 0 < 1 - β := by linarith
  intro s hs
  unfold od_dcR od_dcM
  have hkey : β * (V 0 - m) ≤ β / (1 - β) * D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; nlinarith
  have hDD : D + β / (1 - β) * D < Pb - Ps := by
    have : D + β / (1 - β) * D = D / (1 - β) := by field_simp; ring
    rw [this, div_lt_iff₀ hpos]; linarith
  nlinarith [hD s hs, mul_le_mul_of_nonneg_left (hEm s hs) hβ0.le,
    mul_le_mul_of_nonneg_left hE0 hβ0.le]

end Miao.Applications
