/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalAbsCont

/-!
# A Choquet–Deny maximum principle for Blackwell's renewal theorem (MT §14.5)

Meyn and Tweedie, Theorem 14.5.1 (p. 354), quoted from Feller. This module holds the
real-analysis core of our proof: an asymptotic form of the Choquet–Deny lemma, proved by a
maximum principle that needs no compactness.

* `IsNonLattice Γ`: `Γ` is not concentrated on a lattice `hℤ`, `h > 0` (the hypothesis of
  Theorem 14.5.1). `IsSupportPoint Γ y`: every closed interval around `y` has positive mass.
* `measure_not_isSupportPoint`: the points outside the support form a `Γ`-null set.
* `eventually_sub_le_of_harmonic` (the maximum principle): let `Z` be bounded and uniformly
  continuous, and suppose that for every `j`, `Z(t) = ∫ Z(t − x + 1) P_j(dx) + R_j(t)` with
  `R_j(t) → 0`. If every interval around `1 + j y` has `P_j`-mass bounded below uniformly in
  `j < k`, then `limsup (Z(t) − Z(t − y)) ≤ 0`. If `w(t) = Z(t) − Z(t − y)` had limsup `M > 0`,
  then at one time `t`, `w(t − j y) ≥ M/2` for all `j < k`. That would give
  `Z(t) − Z(t − k y) ≥ k M/2`, which exceeds `2 sup |Z|` once `k` is large.
* `tendsto_sub_of_harmonic`: then `Z(t) − Z(t − y) → 0`.
* `tendsto_sub_of_isNonLattice`: the `a` with `Z(t) − Z(t − a) → 0` form a closed additive
  subgroup of `ℝ`. If it contains the support of a non-lattice `Γ` on `(0, ∞)`, it is all of `ℝ`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- `Γ` is **non-lattice** (MT Theorem 14.5.1): for no `h > 0` is `Γ` concentrated on `hℤ`. -/
def IsNonLattice (Γ : Measure ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → Γ (AddSubgroup.zmultiples h : Set ℝ)ᶜ ≠ 0

/-- `y` is a **support point** of `Γ`: every interval `[y − r, y + r]`, `r > 0`, has positive
mass. -/
def IsSupportPoint (Γ : Measure ℝ) (y : ℝ) : Prop := ∀ r : ℝ, 0 < r → 0 < Γ (Icc (y - r) (y + r))

/-- The points outside the support of `Γ` form a `Γ`-null set. -/
theorem measure_not_isSupportPoint (Γ : Measure ℝ) : Γ {x | ¬ IsSupportPoint Γ x} = 0 := by
  refine measure_null_of_locally_null _ fun x hx => ?_
  have hx' : ¬ IsSupportPoint Γ x := hx
  have h : ∃ r : ℝ, 0 < r ∧ Γ (Icc (x - r) (x + r)) = 0 := by
    by_contra hne
    exact hx' fun r hr => pos_iff_ne_zero.2 fun h0 => hne ⟨r, hr, h0⟩
  obtain ⟨r, hr, h0⟩ := h
  exact ⟨Icc (x - r) (x + r), mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith)
    (by linarith)), h0⟩

/-- A uniformly continuous `Z` is continuous. -/
theorem continuous_of_unifCont {Z : ℝ → ℝ}
    (hZuc : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ a b, |a - b| ≤ r → |Z a - Z b| ≤ η) :
    Continuous Z := by
  refine Metric.continuous_iff.2 fun b e he => ?_
  obtain ⟨r, hr, hrZ⟩ := hZuc (e / 2) (half_pos he)
  refine ⟨r, hr, fun a ha => ?_⟩
  rw [Real.dist_eq] at ha ⊢
  exact lt_of_le_of_lt (hrZ a b ha.le) (half_lt_self he)

/-- **The maximum principle**: for a bounded, uniformly continuous `Z` with
`Z(t) = ∫ Z(t − x + 1) P_j(dx) + R_j(t)` and `R_j(t) → 0` for every `j`, and with the
intervals around `1 + j y` charged uniformly in `j < k`, `Z(t) − Z(t − y) ≤ ε` eventually. -/
theorem eventually_sub_le_of_harmonic {Z : ℝ → ℝ} {B : ℝ} (hZB : ∀ t, |Z t| ≤ B)
    (hZuc : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ a b, |a - b| ≤ r → |Z a - Z b| ≤ η)
    (P : ℕ → Measure ℝ) [hP : ∀ j, IsProbabilityMeasure (P j)] (R : ℕ → ℝ → ℝ)
    (hZeq : ∀ j t, Z t = ∫ x, Z (t - x + 1) ∂P j + R j t)
    (hR : ∀ j, Tendsto (R j) atTop (𝓝 0)) {y : ℝ}
    (hy : ∀ r : ℝ, 0 < r → ∀ k : ℕ, ∃ q : ℝ, 0 < q ∧
      ∀ j < k, q ≤ (P j).real (Icc (1 + j * y - r) (1 + j * y + r)))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, Z t - Z (t - y) ≤ ε := by
  set w : ℝ → ℝ := fun t => Z t - Z (t - y) with hw
  have hZc : Continuous Z := continuous_of_unifCont hZuc
  have hwc : Continuous w := hZc.sub (hZc.comp (continuous_id.sub continuous_const))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hZB 0)
  have hwB : ∀ t, |w t| ≤ 2 * B := fun t => abs_le.2
    ⟨by linarith [(abs_le.1 (hZB t)).1, (abs_le.1 (hZB (t - y))).2],
      by linarith [(abs_le.1 (hZB t)).2, (abs_le.1 (hZB (t - y))).1]⟩
  have hwuc : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ a b, |a - b| ≤ r → |w a - w b| ≤ η :=
    fun η hη => by
      obtain ⟨r, hr, hrZ⟩ := hZuc (η / 2) (half_pos hη)
      refine ⟨r, hr, fun a b hab => ?_⟩
      have h1 := hrZ a b hab
      have h2 := hrZ (a - y) (b - y) (by rw [show a - y - (b - y) = a - b by ring]; exact hab)
      change |Z a - Z (a - y) - (Z b - Z (b - y))| ≤ η
      rw [show Z a - Z (a - y) - (Z b - Z (b - y)) = (Z a - Z b) - (Z (a - y) - Z (b - y)) by
        ring]
      refine (abs_sub _ _).trans ?_
      linarith
  have hZint : ∀ j s, Integrable (fun x => Z (s - x + 1)) (P j) := fun j s =>
    Integrable.mono' (integrable_const B)
      (hZc.comp ((continuous_const.sub continuous_id).add continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hZB _)
  have hwint : ∀ j s, Integrable (fun x => w (s - x + 1)) (P j) := fun j s =>
    Integrable.mono' (integrable_const (2 * B))
      (hwc.comp ((continuous_const.sub continuous_id).add continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hwB _)
  have hweq : ∀ j t, w t = ∫ x, w (t - x + 1) ∂P j + (R j t - R j (t - y)) := fun j t => by
    have e1 := hZeq j t
    have e2 := hZeq j (t - y)
    have e3 : ∫ x, w (t - x + 1) ∂P j =
        ∫ x, Z (t - x + 1) ∂P j - ∫ x, Z (t - y - x + 1) ∂P j := by
      rw [← integral_sub (hZint j t) (hZint j (t - y))]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change Z (t - x + 1) - Z (t - x + 1 - y) = Z (t - x + 1) - Z (t - y - x + 1)
      rw [show t - x + 1 - y = t - y - x + 1 by ring]
    rw [e3]
    change Z t - Z (t - y) = _
    linarith
  -- the limsup `M` of `w`
  have hbdd : IsBoundedUnder (· ≤ ·) atTop w :=
    isBoundedUnder_of ⟨2 * B, fun t => (abs_le.1 (hwB t)).2⟩
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop w :=
    isCoboundedUnder_le_of_le atTop (fun t => (abs_le.1 (hwB t)).1)
  set M := limsup w atTop with hM
  by_cases hMε : M < ε
  · filter_upwards [eventually_lt_of_limsup_lt hMε hbdd] with t ht
    exact ht.le
  exfalso
  have hMpos : 0 < M := lt_of_lt_of_le hε (not_lt.1 hMε)
  -- the number of steps `k`, the radius `r`, the mass `q` and the slack `δ`
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * B / M)
  have hk' : 2 * B < k * (M / 2) := by
    rw [div_lt_iff₀ hMpos] at hk
    linarith
  obtain ⟨r, hr, hrw⟩ := hwuc (M / 4) (by linarith)
  obtain ⟨q, hq, hqP⟩ := hy r hr k
  set C : ℝ := 2 * B with hC
  have hC0 : 0 ≤ C := by linarith
  set δ : ℝ := M / 4 * q / (2 * (3 + C)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ' : 3 * δ + C * δ = M / 4 * q / 2 := by
    rw [hδdef]
    field_simp
  -- a time `T` after which `w < M + δ`
  obtain ⟨T, hT⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt
    (lt_add_of_pos_right M hδ) hbdd)
  have hfreq : ∃ᶠ t in atTop, M - δ < w t :=
    frequently_lt_of_lt_limsup hcobdd (sub_lt_self M hδ)
  have hsub : Tendsto (fun t : ℝ => t - y) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-y) tendsto_id).congr fun t => (sub_eq_add_neg t y).symm
  have hshift : Tendsto (fun t : ℝ => t + 1 - T) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1 - T) tendsto_id).congr fun t => by
      change t + (1 - T) = t + 1 - T
      ring
  have hev : ∀ j ∈ Finset.range k, ∀ᶠ t in atTop, |R j t - R j (t - y)| ≤ δ ∧
      (P j).real (Ioi (t + 1 - T)) ≤ δ ∧ 1 + j * y + r ≤ t + 1 - T := fun j _ => by
    have h1 : Tendsto (fun t => R j t - R j (t - y)) atTop (𝓝 0) := by
      have h := (hR j).sub ((hR j).comp hsub)
      rw [sub_zero] at h
      exact h
    have h2 : Tendsto (fun s : ℝ => P j (Ioi s)) atTop (𝓝 0) := by
      have hanti : Antitone fun s : ℝ => Ioi s := fun a b hab => Ioi_subset_Ioi hab
      have hI : ⋂ s : ℝ, Ioi s = ∅ := by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        exact lt_irrefl x (mem_iInter.1 hx x)
      have h := tendsto_measure_iInter_atTop (μ := P j)
        (fun s => measurableSet_Ioi.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rwa [hI, measure_empty] at h
    filter_upwards [(Metric.tendsto_nhds.1 h1) δ hδ,
      (ENNReal.tendsto_nhds_zero.1 (h2.comp hshift)) (ENNReal.ofReal δ)
        (ENNReal.ofReal_pos.2 hδ), eventually_ge_atTop (j * y + r + T)] with t ht1 ht2 ht3
    refine ⟨?_, ENNReal.toReal_le_of_le_ofReal hδ.le ht2, by linarith⟩
    rw [Real.dist_eq, sub_zero] at ht1
    exact ht1.le
  obtain ⟨t, ht1, ht2, ht3⟩ := (hfreq.and_eventually
    (((eventually_all_finset (Finset.range k)).2 hev).and (eventually_ge_atTop T))).exists
  -- the key claim: `w(t − j y) ≥ M/2` for `j < k`
  have hkey : ∀ j < k, M / 2 ≤ w (t - j * y) := fun j hj => by
    obtain ⟨hRj, hPj, hBl⟩ := ht2 j (Finset.mem_range.2 hj)
    by_contra hcon
    push Not at hcon
    set Bl : Set ℝ := Icc (1 + j * y - r) (1 + j * y + r) with hBldef
    set I : Set ℝ := Ioi (t + 1 - T) with hIdef
    have hsmall : ∀ x ∈ Bl, w (t - x + 1) < 3 * M / 4 := fun x hx => by
      have h := hrw (t - x + 1) (t - j * y) (by
        rw [show t - x + 1 - (t - j * y) = 1 + j * y - x by ring, abs_le]
        constructor <;> linarith [hx.1, hx.2])
      linarith [(abs_le.1 h).2]
    set h : ℝ → ℝ := fun x => (M + δ) + C * I.indicator 1 x - M / 4 * Bl.indicator 1 x
      with hhdef
    have hle : ∀ x, w (t - x + 1) ≤ h x := fun x => by
      by_cases hxI : x ∈ I
      · have hxB : x ∉ Bl := fun hxB => by
          have h1 : x ≤ t + 1 - T := by linarith [hxB.2]
          exact (not_lt.2 h1) hxI
        change w (t - x + 1) ≤ (M + δ) + C * I.indicator 1 x - M / 4 * Bl.indicator 1 x
        rw [indicator_of_mem hxI, indicator_of_notMem hxB, Pi.one_apply, mul_one, mul_zero,
          sub_zero]
        linarith [(abs_le.1 (hwB (t - x + 1))).2]
      · have hTx : T ≤ t - x + 1 := by
          have h1 : x ≤ t + 1 - T := not_lt.1 hxI
          linarith
        have hw1 := hT (t - x + 1) hTx
        change w (t - x + 1) ≤ (M + δ) + C * I.indicator 1 x - M / 4 * Bl.indicator 1 x
        rw [indicator_of_notMem hxI, mul_zero, add_zero]
        by_cases hxB : x ∈ Bl
        · rw [indicator_of_mem hxB, Pi.one_apply, mul_one]
          linarith [hsmall x hxB]
        · rw [indicator_of_notMem hxB, mul_zero, sub_zero]
          exact hw1.le
    have hIi : Integrable (fun x => C * I.indicator 1 x) (P j) :=
      ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi).const_mul C
    have hBi : Integrable (fun x => M / 4 * Bl.indicator 1 x) (P j) :=
      ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul (M / 4)
    have hAi : Integrable (fun x => (M + δ) + C * I.indicator 1 x) (P j) :=
      (integrable_const (M + δ)).add hIi
    have hhint : Integrable h (P j) := hAi.sub hBi
    have hih : ∫ x, h x ∂P j = (M + δ) + C * (P j).real I - M / 4 * (P j).real Bl := by
      change ∫ x, ((M + δ) + C * I.indicator 1 x - M / 4 * Bl.indicator 1 x) ∂P j = _
      rw [integral_sub hAi hBi,
        integral_add (integrable_const (M + δ)) hIi, integral_const, integral_const_mul,
        integral_const_mul, integral_indicator_one measurableSet_Ioi,
        integral_indicator_one measurableSet_Icc, probReal_univ, one_smul]
    have hmono := integral_mono (hwint j t) hhint hle
    have heq := hweq j t
    have hqB := hqP j hj
    have hCI : C * (P j).real I ≤ C * δ := mul_le_mul_of_nonneg_left hPj hC0
    have hMB : M / 4 * q ≤ M / 4 * (P j).real Bl :=
      mul_le_mul_of_nonneg_left hqB (by linarith)
    have hRj' := (abs_le.1 hRj).2
    have hMq : 0 < M / 4 * q := by positivity
    linarith
  -- the telescoping sum
  have htel : ∀ n : ℕ, ∑ j ∈ Finset.range n, w (t - j * y) = Z t - Z (t - n * y) := by
    intro n
    induction n with
    | zero => rw [Finset.sum_range_zero, Nat.cast_zero, zero_mul, sub_zero, sub_self]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      change Z t - Z (t - n * y) + (Z (t - n * y) - Z (t - n * y - y)) =
        Z t - Z (t - (n + 1) * y)
      rw [show t - n * y - y = t - (n + 1) * y by ring]
      ring
  have hsum : (k : ℝ) * (M / 2) ≤ ∑ j ∈ Finset.range k, w (t - j * y) := by
    have h := Finset.sum_le_sum (s := Finset.range k) (f := fun _ : ℕ => M / 2)
      (g := fun j : ℕ => w (t - j * y)) fun j hj => hkey j (Finset.mem_range.1 hj)
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [htel k] at hsum
  linarith [(abs_le.1 (hZB t)).2, (abs_le.1 (hZB (t - k * y))).1]

/-- **`Z(t) − Z(t − y) → 0`** under the hypotheses of the maximum principle
(`eventually_sub_le_of_harmonic`), applied to `Z` and to `−Z`. -/
theorem tendsto_sub_of_harmonic {Z : ℝ → ℝ} {B : ℝ} (hZB : ∀ t, |Z t| ≤ B)
    (hZuc : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ a b, |a - b| ≤ r → |Z a - Z b| ≤ η)
    (P : ℕ → Measure ℝ) [hP : ∀ j, IsProbabilityMeasure (P j)] (R : ℕ → ℝ → ℝ)
    (hZeq : ∀ j t, Z t = ∫ x, Z (t - x + 1) ∂P j + R j t)
    (hR : ∀ j, Tendsto (R j) atTop (𝓝 0)) {y : ℝ}
    (hy : ∀ r : ℝ, 0 < r → ∀ k : ℕ, ∃ q : ℝ, 0 < q ∧
      ∀ j < k, q ≤ (P j).real (Icc (1 + j * y - r) (1 + j * y + r))) :
    Tendsto (fun t => Z t - Z (t - y)) atTop (𝓝 0) := by
  have hZB' : ∀ t, |(fun s => -Z s) t| ≤ B := fun t => by
    change |-Z t| ≤ B
    rw [abs_neg]
    exact hZB t
  have hZuc' : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
      ∀ a b, |a - b| ≤ r → |(fun s => -Z s) a - (fun s => -Z s) b| ≤ η := fun η hη => by
    obtain ⟨r, hr, hrZ⟩ := hZuc η hη
    refine ⟨r, hr, fun a b hab => ?_⟩
    change |-Z a - -Z b| ≤ η
    rw [neg_sub_neg, abs_sub_comm]
    exact hrZ a b hab
  have hZeq' : ∀ j t, (fun s => -Z s) t =
      ∫ x, (fun s => -Z s) (t - x + 1) ∂P j + (fun s => -R j s) t := fun j t => by
    change -Z t = ∫ x, -Z (t - x + 1) ∂P j + -R j t
    rw [integral_neg, hZeq j t]
    ring
  have hR' : ∀ j, Tendsto (fun s => -R j s) atTop (𝓝 0) := fun j => by
    have h := (hR j).neg
    rw [neg_zero] at h
    exact h
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [eventually_sub_le_of_harmonic hZB hZuc P R hZeq hR hy (half_pos hε),
    eventually_sub_le_of_harmonic hZB' hZuc' P (fun j s => -R j s) hZeq' hR' hy (half_pos hε)]
    with t h1 h2
  change -Z t - -Z (t - y) ≤ ε / 2 at h2
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-- **Translation invariance at infinity**: if `Z` is uniformly continuous and
`Z(t) − Z(t − y) → 0` for every support point `y` of a non-lattice `Γ` on `(0, ∞)`, then
`Z(t) − Z(t − a) → 0` for every `a ∈ ℝ`. The admissible `a` form a closed subgroup of `ℝ`;
it is not cyclic, so it is dense, hence everything. -/
theorem tendsto_sub_of_isNonLattice {Γ : Measure ℝ} (hΓpos : 0 < Γ (Ioi 0))
    (hnl : IsNonLattice Γ) {Z : ℝ → ℝ}
    (hZuc : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ a b, |a - b| ≤ r → |Z a - Z b| ≤ η)
    (hsupp : ∀ y, IsSupportPoint Γ y → Tendsto (fun t => Z t - Z (t - y)) atTop (𝓝 0))
    (a : ℝ) : Tendsto (fun t => Z t - Z (t - a)) atTop (𝓝 0) := by
  have hshift : ∀ c : ℝ, Tendsto (fun t : ℝ => t - c) atTop atTop := fun c =>
    (tendsto_atTop_add_const_right atTop (-c) tendsto_id).congr fun t => (sub_eq_add_neg t c).symm
  set G : AddSubgroup ℝ :=
    { carrier := {a | Tendsto (fun t => Z t - Z (t - a)) atTop (𝓝 0)}
      add_mem' := fun {b c} hb hc => by
        have h := hb.add (hc.comp (hshift b))
        rw [add_zero] at h
        refine h.congr fun t => ?_
        change Z t - Z (t - b) + (Z (t - b) - Z (t - b - c)) = Z t - Z (t - (b + c))
        rw [show t - b - c = t - (b + c) by ring]
        ring
      zero_mem' := tendsto_const_nhds.congr fun t => by
        change (0 : ℝ) = Z t - Z (t - 0)
        rw [sub_zero, sub_self]
      neg_mem' := fun {b} hb => by
        have h := (hb.comp (hshift (-b))).neg
        rw [neg_zero] at h
        refine h.congr fun t => ?_
        change -(Z (t - -b) - Z (t - -b - b)) = Z t - Z (t - -b)
        rw [show t - -b - b = t by ring]
        ring } with hG
  have hmem : ∀ b, b ∈ G ↔ Tendsto (fun t => Z t - Z (t - b)) atTop (𝓝 0) := fun b => Iff.rfl
  -- `G` is closed
  have hclosed : IsClosed (G : Set ℝ) := by
    refine isClosed_of_closure_subset fun b hb => ?_
    refine (hmem b).2 (Metric.tendsto_nhds.2 fun ε hε => ?_)
    obtain ⟨r, hr, hrZ⟩ := hZuc (ε / 3) (by linarith)
    obtain ⟨c, hc, hbc⟩ := Metric.mem_closure_iff.1 hb r hr
    filter_upwards [(Metric.tendsto_nhds.1 ((hmem c).1 hc)) (ε / 3) (by linarith)] with t ht
    rw [Real.dist_eq, sub_zero] at ht ⊢
    have h1 := hrZ (t - b) (t - c) (by
      rw [show t - b - (t - c) = c - b by ring, abs_sub_comm]
      rw [Real.dist_eq] at hbc
      exact hbc.le)
    calc |Z t - Z (t - b)| = |(Z t - Z (t - c)) - (Z (t - b) - Z (t - c))| := by ring_nf
      _ ≤ |Z t - Z (t - c)| + |Z (t - b) - Z (t - c)| := abs_sub _ _
      _ < ε := by linarith
  -- the points of `G`ᶜ are not support points
  have hnull : ∀ S : AddSubgroup ℝ, G = S → Γ (S : Set ℝ)ᶜ = 0 := fun S hS =>
    measure_mono_null (fun x hx hsx => hx (hS ▸ (hmem x).2 (hsupp x hsx)))
      (measure_not_isSupportPoint Γ)
  rcases AddSubgroup.dense_or_cyclic G with hd | ⟨c, hc⟩
  · have huniv : (G : Set ℝ) = univ := by rw [← hclosed.closure_eq, hd.closure_eq]
    have ha : a ∈ (G : Set ℝ) := by
      rw [huniv]
      exact mem_univ a
    exact (hmem a).1 ha
  · exfalso
    rw [← AddSubgroup.zmultiples_eq_closure] at hc
    have h0 := hnull _ hc
    rcases lt_trichotomy c 0 with hneg | hzero | hpos
    · rw [← AddSubgroup.zmultiples_neg] at h0
      exact hnl (-c) (neg_pos.2 hneg) h0
    · subst hzero
      refine hΓpos.ne' (measure_mono_null (show Ioi (0 : ℝ) ⊆
        ((AddSubgroup.zmultiples (0 : ℝ) : Set ℝ))ᶜ from fun x hx hxz => ?_) h0)
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hxz
      rw [smul_zero] at hn
      exact (ne_of_gt (mem_Ioi.1 hx)) hn.symm
    · exact hnl c hpos h0

end MeynTweedie.FErgodicity
