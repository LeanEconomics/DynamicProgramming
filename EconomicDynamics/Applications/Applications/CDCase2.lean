/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.CDEuler

/-!
# Deterministic income, Case 2 (`βR > 1`)

Miao, §8.3.1, Case 2, p. 246. Income is constant, `y_t = y`, and `x₀ ≥ y − rb` (`a₀ ≥ −b`).
For every optimal plan:

* `cd2_never_binding`: the borrowing constraint never binds, `â_{t+1} > 0`;
* `cd2_c_strictMono`: consumption is strictly increasing;
* `cd2_c_tendsto`, `cd2_x_tendsto`, `cd2_s_tendsto`: `c_t, x_t, â_{t+1} → ∞`.

The book argues with the envelope condition `V′(x) = u′(c)` and strict concavity of `V`, which
it assumes; we argue in sequence space with the Euler inequality (8.7), which every optimal plan
satisfies (`eq_8_7`). The book's limit argument (`u′(c*) = βRu′(c*)` at a finite limit `c*`)
uses continuity of `u′`; we use instead that `u′(c_t) = (βR)^{−t}u′(c_0) → 0` while `u′` is
bounded below on bounded sets. The statements are conditional on an optimal plan existing.
-/

namespace Miao.Applications

open Filter Topology

/-- Cash on hand stays above `y − rb` along a feasible plan from `x₀ ≥ y − rb`. -/
theorem cd2_w_le_x {R b y x₀ : ℝ} (hR : 0 ≤ R) {c x : ℕ → ℝ}
    (h : cd_Feasible R b (fun _ => y) x₀ c x) (hx₀ : y - (R - 1) * b ≤ x₀) :
    ∀ t, y - (R - 1) * b ≤ x t := by
  intro t
  cases t with
  | zero => rw [h.1.1]; exact hx₀
  | succ t =>
    rw [h.1.2 t]
    have := mul_nonneg hR (sub_nonneg.2 (h.2 t).2)
    linarith

/-- Miao, p. 246: if `βR > 1` the borrowing constraint is never binding along an optimal plan:
`c_t < x_t`, i.e. `â_{t+1} > 0`. -/
theorem cd2_never_binding (U : cd_Utility) {β R b y x₀ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hx₀ : y - (R - 1) * b ≤ x₀) {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b (fun _ => y) x₀ c x) : ∀ t, c t < x t := by
  have hE := eq_8_7 U hβ hR h
  have hf := h.1
  intro t
  by_contra hb
  have heq : c t = x t := le_antisymm (hf.2 t).2 (not_lt.1 hb)
  have hx1 : x (t + 1) = y - (R - 1) * b := by rw [hf.1.2 t, heq]; ring
  have hc1 : c (t + 1) ≤ y - (R - 1) * b := hx1 ▸ (hf.2 (t + 1)).2
  have hpos := U.du_pos _ (hf.2 (t + 1)).1
  have h1 : U.du (c (t + 1)) < U.du (c t) := by nlinarith [(hE t).1]
  have h2 : c t < c (t + 1) := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with h' | h'
    · exact absurd h1 (not_lt.2 (U.du_anti (Set.mem_Ioi.2 (hf.2 _).1)
        (Set.mem_Ioi.2 (hf.2 _).1) h').le)
    · rw [h'] at h1; exact lt_irrefl _ h1
  have h3 := cd2_w_le_x hR.le hf hx₀ t
  linarith

/-- Miao, p. 246: `u′(c_t) = βRu′(c_{t+1}) > u′(c_{t+1})`, so `c_t < c_{t+1}`. -/
theorem cd2_c_strictMono (U : cd_Utility) {β R b y x₀ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hx₀ : y - (R - 1) * b ≤ x₀) {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b (fun _ => y) x₀ c x) : StrictMono c := by
  have hE := eq_8_7 U hβ hR h
  have hf := h.1
  refine strictMono_nat_of_lt_succ fun t => ?_
  have heq := (hE t).2 (cd2_never_binding U hβ hR hβR hx₀ h t)
  have hpos := U.du_pos _ (hf.2 (t + 1)).1
  have h1 : U.du (c (t + 1)) < U.du (c t) := by nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h' | h'
  · exact absurd h1 (not_lt.2 (U.du_anti (Set.mem_Ioi.2 (hf.2 _).1)
      (Set.mem_Ioi.2 (hf.2 _).1) h').le)
  · rw [h'] at h1; exact lt_irrefl _ h1

/-- Miao, p. 246: `lim c_t = ∞`. -/
theorem cd2_c_tendsto (U : cd_Utility) {β R b y x₀ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hx₀ : y - (R - 1) * b ≤ x₀) {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b (fun _ => y) x₀ c x) : Tendsto c atTop atTop := by
  have hE := eq_8_7 U hβ hR h
  have hf := h.1
  have hmono := cd2_c_strictMono U hβ hR hβR hx₀ h
  -- `u′(c_t) = (βR)⁻ᵗ u′(c_0)`
  have hdu : ∀ t, U.du (c t) = (β * R)⁻¹ ^ t * U.du (c 0) := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      have heq := (hE t).2 (cd2_never_binding U hβ hR hβR hx₀ h t)
      have hne : β * R ≠ 0 := by positivity
      rw [pow_succ, mul_comm ((β * R)⁻¹ ^ t), mul_assoc, ← ih, heq]
      field_simp
  refine tendsto_atTop_atTop_of_monotone hmono.monotone fun M => ?_
  by_contra hall
  push Not at hall
  set M' := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : ∀ t, U.du M' ≤ U.du (c t) := fun t => by
    have h1 : c t ≤ M' := (hall t).le.trans (le_max_left _ _)
    rcases h1.lt_or_eq with h' | h'
    · exact (U.du_anti (Set.mem_Ioi.2 (hf.2 t).1) (Set.mem_Ioi.2 hM') h').le
    · rw [h']
  have hρ0 : 0 ≤ (β * R)⁻¹ := by positivity
  have hρ1 : (β * R)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβR
  have hlim : Tendsto (fun t : ℕ => (β * R)⁻¹ ^ t * U.du (c 0)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (U.du (c 0))
  obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds (U.du_pos M' hM'))).exists
  have := hle t
  rw [hdu t] at this
  linarith

/-- Miao, p. 246: `lim x_t = ∞`. -/
theorem cd2_x_tendsto (U : cd_Utility) {β R b y x₀ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hx₀ : y - (R - 1) * b ≤ x₀) {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b (fun _ => y) x₀ c x) : Tendsto x atTop atTop :=
  tendsto_atTop_mono (fun t => (h.1.2 t).2) (cd2_c_tendsto U hβ hR hβR hx₀ h)

/-- Miao, p. 246: `lim â_{t+1} = ∞` (`â_{t+1} = (x_{t+1} − y + rb)/R`). -/
theorem cd2_s_tendsto (U : cd_Utility) {β R b y x₀ : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hx₀ : y - (R - 1) * b ≤ x₀) {c x : ℕ → ℝ}
    (h : cd_Optimal U β R b (fun _ => y) x₀ c x) :
    Tendsto (fun t => x t - c t) atTop atTop := by
  have hx := (cd2_x_tendsto U hβ hR hβR hx₀ h).comp (tendsto_add_atTop_nat 1)
  have e : ∀ t, x t - c t = (x (t + 1) - (y - (R - 1) * b)) / R := fun t => by
    rw [h.1.1.2 t]; field_simp; ring
  simp only [e]
  exact (tendsto_atTop_add_const_right _ _ hx).atTop_div_const hR

end Miao.Applications
