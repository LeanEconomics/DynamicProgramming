/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.SIPolicies
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# §8.3.2, Case 1 (`βR < 1`): Lemma 8.3.3, `x_max` and Exercise 8.9

Copied from `EconomicDynamics/Applications` (module `SIBounded`), namespace renamed.

Miao, §8.3.2, pp. 252–254, and Exercise 9, p. 289.

* **Footnote 2** (p. 253, `footnote_2`): if `−cu′′(c)/u′(c) ≤ γ` for `c > c₀ > 0`, then
  `u′(c)/u′(c₀) ≥ (c₀/c)^γ` for `c > c₀`; it follows from `c ↦ u′(c)c^γ` being nondecreasing on
  `[c₀, ∞)` (`footnote_2_mono`).
* `cons_unbounded` (p. 253): if `βR < 1` and `â` is unbounded, then `c(x) → ∞`.
* **(8.16)** (`eq_8_16`): with `m = Râ(x) + y_min − rb` and `M = Râ(x) + y_max − rb`,
  `V′(M) ≤ E V′(x′) ≤ V′(M)(1 + (y_max − y_min)/c(m))^γ` once `c(m) ≥ c₀`.
* **Lemma 8.3.3** (Schechtman–Escudero; `lemma_8_3_3`): if `βR < 1` and the relative risk
  aversion is below `γ` for large `c`, there is `x*` with `x_{t+1} < x_t` whenever `x_t > x*`
  (for every income `y ≤ y_max`, `lemma_8_3_3_all`).
* **Exercise 8.9** (`ex_8_9`): if moreover `y_min < y_max`, the smallest critical value
  `x_max` (`Solution.xmax`) exists; `x_max > x_min`, and `x_max` is the largest solution of
  `Râ(x) + y_max − rb = x`. The interval `[x_min, x_max]` is invariant (`mapsTo_Icc`, p. 254).

**Correction** (`eq_8_16_identity_false`). The proof of Lemma 8.3.3 says "by definition,
`c(y_max − rb + Râ) = c(y_min − rb + Râ) + y_max − y_min`". This is false: by Lemma 8.3.1 only
`≤` holds (`cons_high_le`), and the inequality is strict whenever `y_min < y_max` and the
borrowing constraint does not bind at `m`, which is the situation of the proof (`â → ∞`).
The `≤` suffices for (8.16). Also, the contradiction in the proof that `c(x) → ∞` is
`u′(c̄) = βRu′(c̄)` (printed `c̄ = βRc̄`).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

namespace SIModel

variable (M : SIModel)

theorem next_ymin (s : ℝ) : M.next s M.ymin = M.R * s + M.xmin := by
  simp only [next, xmin]; ring

theorem next_ymax_sub (s : ℝ) : M.next s M.ymax - M.next s M.ymin = M.ymax - M.ymin := by
  simp only [next]; ring

/-- Footnote 2, the monotone form: if `−cu′′(c)/u′(c) ≤ γ` for `c > c₀ > 0`, then `u′(c)c^γ`
is nondecreasing on `[c₀, ∞)`. -/
theorem footnote_2_mono {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ) :
    MonotoneOn (fun c => M.du c * c ^ γ) (Set.Ici c₀) := by
  have hd : ∀ c, 0 < c → HasDerivAt (fun c => M.du c * c ^ γ)
      (ddu c * c ^ γ + M.du c * (γ * c ^ (γ - 1))) c := fun c hc =>
    (hddu c hc).mul (Real.hasDerivAt_rpow_const (Or.inl hc.ne'))
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici c₀)
    (f' := fun c => ddu c * c ^ γ + M.du c * (γ * c ^ (γ - 1))) (fun c hc => ?_)
    (fun c hc => ?_) (fun c hc => ?_)
  · exact (hd c (hc₀.trans_le hc)).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hc
    exact (hd c (hc₀.trans hc)).hasDerivWithinAt
  · rw [interior_Ici] at hc
    have hc0 : 0 < c := hc₀.trans hc
    have hdu := M.du_pos c hc0
    have h1 := hγ c hc
    rw [div_le_iff₀ hdu] at h1
    have hP : 0 < c ^ γ := Real.rpow_pos_of_pos hc0 γ
    rw [Real.rpow_sub_one hc0.ne']
    have e : ddu c * c ^ γ + M.du c * (γ * (c ^ γ / c)) =
        (c ^ γ / c) * (c * ddu c + γ * M.du c) := by
      field_simp
    rw [e]
    exact mul_nonneg (div_nonneg hP.le hc0.le) (by linarith)

/-- **Footnote 2** (Miao, p. 253): if `−cu′′(c)/u′(c) ≤ γ` for all `c > c₀ > 0`, then
`u′(c)/u′(c₀) ≥ (c₀/c)^γ` for all `c > c₀`. -/
theorem footnote_2 {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ) {c : ℝ}
    (hc : c₀ < c) : (c₀ / c) ^ γ ≤ M.du c / M.du c₀ := by
  have hm := M.footnote_2_mono hddu hc₀ hγ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hc.le) hc.le
  simp only at hm
  have hc0 : 0 < c := hc₀.trans hc
  rw [Real.div_rpow hc₀.le hc0.le, div_le_div_iff₀ (Real.rpow_pos_of_pos hc0 γ)
    (M.du_pos c₀ hc₀)]
  linarith

/-- From footnote 2: `u′(c) ≤ u′(c′)(c′/c)^γ` for `c₀ ≤ c ≤ c′`. -/
theorem du_le_rpow {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ) {c c' : ℝ}
    (hc : c₀ ≤ c) (hcc : c ≤ c') : M.du c ≤ M.du c' * (c' / c) ^ γ := by
  have hm := M.footnote_2_mono hddu hc₀ hγ (Set.mem_Ici.2 hc) (Set.mem_Ici.2 (hc.trans hcc)) hcc
  simp only at hm
  have hc0 : 0 < c := hc₀.trans_le hc
  have hP : 0 < c ^ γ := Real.rpow_pos_of_pos hc0 γ
  rw [Real.div_rpow (hc0.le.trans hcc) hc0.le, ← mul_div_assoc, le_div_iff₀ hP]
  exact hm

/-- `(1 + t)^γ ≤ e^{γt}` for `t ≥ 0`, `γ ≥ 0`. -/
theorem si_one_add_rpow_le {t γ : ℝ} (ht : 0 ≤ t) (hγ : 0 ≤ γ) :
    (1 + t) ^ γ ≤ Real.exp (γ * t) := by
  calc (1 + t) ^ γ ≤ (Real.exp t) ^ γ :=
        Real.rpow_le_rpow (by linarith) (by linarith [Real.add_one_le_exp t]) hγ
    _ = Real.exp (γ * t) := by rw [← Real.exp_mul, mul_comm]

end SIModel

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- `E V′(x′) ≤ V′(Rs + y_min − rb)`. -/
theorem D_le_low {s : ℝ} (hs : 0 ≤ s) : S.D s ≤ S.dV (M.next s M.ymin) := by
  have : S.D s ≤ ∫ _y, S.dV (M.next s M.ymin) ∂M.law := by
    refine integral_mono_ae (S.integrable_dV hs) (integrable_const _) ?_
    filter_upwards [M.supp] with y hy
    refine S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 (M.next_ge hs le_rfl))
      (Set.mem_Ici.2 (M.next_ge hs hy.1)) ?_
    simp only [SIModel.next]; linarith [hy.1]
  simpa using this

/-- `V′(Rs + y_max − rb) ≤ E V′(x′)`. -/
theorem high_le_D {s : ℝ} (hs : 0 ≤ s) : S.dV (M.next s M.ymax) ≤ S.D s := by
  have : ∫ _y, S.dV (M.next s M.ymax) ∂M.law ≤ S.D s := by
    refine integral_mono_ae (integrable_const _) (S.integrable_dV hs) ?_
    filter_upwards [M.ae_next hs] with y hy
    exact S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hy.1)
      (Set.mem_Ici.2 (hy.1.trans hy.2)) hy.2
  simpa using this

/-- `â` unbounded gives `â(x) > K` for all large `x`. -/
theorem sav_eventually_gt (hunb : ∀ K, ∃ x, M.xmin ≤ x ∧ K < S.sav x) (K : ℝ) :
    ∃ X, M.xmin ≤ X ∧ ∀ x, X ≤ x → K < S.sav x := by
  obtain ⟨X, hX, hK⟩ := hunb K
  exact ⟨X, hX, fun x hx => hK.trans_le (S.sav_mono (Set.mem_Ici.2 hX)
    (Set.mem_Ici.2 (hX.trans hx)) hx)⟩

/-- Miao, p. 253: if `βR < 1` and `â` is unbounded, then `c(x) → ∞`: for every `C`, `c(x) > C`
for all large `x`. -/
theorem cons_unbounded (hβR : M.β * M.R < 1) (hunb : ∀ K, ∃ x, M.xmin ≤ x ∧ K < S.sav x)
    (C : ℝ) : ∃ X, M.xmin ≤ X ∧ ∀ x, X ≤ x → C < S.cons x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, M.xmin ≤ x → S.cons x ≤ C := ⟨C, fun x hx => by
    obtain ⟨x', hx', hc'⟩ := hcon x hx
    exact (S.cons_mono (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hx')) hx').trans hc'⟩
  have hne : (S.cons '' Set.Ici M.xmin).Nonempty := ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.2
    le_rfl)⟩
  have hbdd : BddAbove (S.cons '' Set.Ici M.xmin) := ⟨C, by
    rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  set cbar := sSup (S.cons '' Set.Ici M.xmin)
  have hle : ∀ x, M.xmin ≤ x → S.cons x ≤ cbar := fun x hx =>
    le_csSup hbdd (Set.mem_image_of_mem _ (Set.mem_Ici.2 hx))
  have hcbar : 0 < cbar := (S.cons_pos le_rfl).trans_le (hle _ le_rfl)
  have hβR0 : 0 ≤ M.β * M.R := (mul_pos M.β_pos M.R_pos).le
  have hlt : M.β * M.R * M.du cbar < M.du cbar := by
    have := M.du_pos cbar hcbar; nlinarith
  have hcont : Tendsto (fun w => M.β * M.R * M.du w) (𝓝 cbar) (𝓝 (M.β * M.R * M.du cbar)) :=
    (((M.du_cont _ (Set.mem_Ioi.2 hcbar)).continuousAt (Ioi_mem_nhds hcbar)).tendsto).const_mul _
  obtain ⟨z, hz, hz0⟩ := ((hcont.eventually_lt_const hlt).filter_mono nhdsWithin_le_nhds |>.and
    (Ioo_mem_nhdsLT hcbar) : ∀ᶠ w in 𝓝[<] cbar, _ ∧ w ∈ Set.Ioo 0 cbar).exists
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hzx⟩ := exists_lt_of_lt_csSup hne hz0.2
  obtain ⟨X, hX, hXK⟩ := S.sav_eventually_gt hunb (max 0 ((x₁ - M.xmin) / M.R))
  have hs := hXK X le_rfl
  have hs0 : 0 < S.sav X := lt_of_le_of_lt (le_max_left _ _) hs
  have hsx : (x₁ - M.xmin) / M.R < S.sav X := lt_of_le_of_lt (le_max_right _ _) hs
  set m := M.next (S.sav X) M.ymin
  have hm : x₁ ≤ m := by
    rw [show m = M.R * S.sav X + M.xmin from M.next_ymin _, ← sub_le_iff_le_add]
    rw [div_lt_iff₀ M.R_pos] at hsx
    linarith
  have hmx : M.xmin ≤ m := M.next_ge hs0.le le_rfl
  have he := (S.euler hX).2 hs0
  have hD := S.D_le_low hs0.le
  rw [S.envelope m hmx] at hD
  have hcm : z < S.cons m := hzx.trans_le (S.cons_mono (Set.mem_Ici.2 hx₁) (Set.mem_Ici.2 hmx) hm)
  have h1 := M.du_anti (Set.mem_Ioi.2 hz0.1) (Set.mem_Ioi.2 (hz0.1.trans hcm)) hcm
  have h2 := M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos hX)) (Set.mem_Ioi.2 hcbar)
    (hle X hX)
  have h3 : M.β * M.R * S.D (S.sav X) ≤ M.β * M.R * M.du z :=
    mul_le_mul_of_nonneg_left (hD.trans h1.le) hβR0
  linarith

/-- Lemma 8.3.1 at `m ≤ M`: `c(Rs + y_max − rb) ≤ c(Rs + y_min − rb) + y_max − y_min`. -/
theorem cons_high_le {s : ℝ} (hs : 0 ≤ s) :
    S.cons (M.next s M.ymax) ≤ S.cons (M.next s M.ymin) + (M.ymax - M.ymin) := by
  have h := (S.cons_sub_bounds (M.next_ge hs le_rfl) (by
    have := M.next_ymax_sub s; linarith [M.ymin_le_ymax] : M.next s M.ymin ≤ M.next s M.ymax)).2
  rw [M.next_ymax_sub] at h
  linarith

/-- **The identity on p. 253 is false**: if `y_min < y_max` and the borrowing constraint does not
bind at `m = Rs + y_min − rb`, then `c(Rs + y_max − rb) < c(m) + y_max − y_min` strictly. -/
theorem eq_8_16_identity_false {s : ℝ} (hs : 0 ≤ s) (hy : M.ymin < M.ymax)
    (hpos : 0 < S.sav (M.next s M.ymin)) :
    S.cons (M.next s M.ymax) < S.cons (M.next s M.ymin) + (M.ymax - M.ymin) := by
  have hlt : M.next s M.ymin < M.next s M.ymax := by
    have := M.next_ymax_sub s; linarith
  have h := (S.sav_lt_of_pos (M.next_ge hs le_rfl) hlt hpos).1
  have e := M.next_ymax_sub s
  simp only [cons_eq]
  linarith

/-- **(8.16)** (Miao, p. 253), corrected: with `m = Rs + y_min − rb`, `M = Rs + y_max − rb`, and
`c(m) ≥ c₀` (where the relative risk aversion is `≤ γ` above `c₀`),
`V′(M) ≤ E V′(Rs + y − rb) ≤ V′(M)(1 + (y_max − y_min)/c(m))^γ`. -/
theorem eq_8_16 {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ c₀ : ℝ} (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ)
    {s : ℝ} (hs : 0 ≤ s) (hcm : c₀ ≤ S.cons (M.next s M.ymin)) :
    S.dV (M.next s M.ymax) ≤ S.D s ∧
      S.D s ≤ S.dV (M.next s M.ymax) *
        (1 + (M.ymax - M.ymin) / S.cons (M.next s M.ymin)) ^ γ := by
  refine ⟨S.high_le_D hs, ?_⟩
  set m := M.next s M.ymin
  set Mx := M.next s M.ymax
  have hmx : M.xmin ≤ m := M.next_ge hs le_rfl
  have hmM : m ≤ Mx := by have := M.next_ymax_sub s; linarith [M.ymin_le_ymax]
  have hMx : M.xmin ≤ Mx := hmx.trans hmM
  have hcm0 : 0 < S.cons m := hc₀.trans_le hcm
  have hcmM : S.cons m ≤ S.cons Mx := S.cons_mono (Set.mem_Ici.2 hmx) (Set.mem_Ici.2 hMx) hmM
  have h1 := M.du_le_rpow hddu hc₀ hγ hcm hcmM
  have h2 : S.cons Mx / S.cons m ≤ 1 + (M.ymax - M.ymin) / S.cons m := by
    rw [div_le_iff₀ hcm0, add_mul, div_mul_cancel₀ _ hcm0.ne', one_mul]
    exact S.cons_high_le hs
  have h3 := Real.rpow_le_rpow (div_nonneg (hcm0.le.trans hcmM) hcm0.le) h2 hγ0
  have hD := S.D_le_low hs
  rw [S.envelope m hmx] at hD
  rw [S.envelope Mx hMx]
  calc S.D s ≤ M.du (S.cons m) := hD
    _ ≤ M.du (S.cons Mx) * (S.cons Mx / S.cons m) ^ γ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (M.du_pos _ (hcm0.trans_le hcmM)).le

/-- **Lemma 8.3.3** (Schechtman and Escudero (1977); Miao, p. 252). Let `βR < 1`, and let
`−cu′′(c)/u′(c) < γ` for all `c` sufficiently large, for some `γ > 0`. Then there is `x*`
such that `x_t > x*` implies `x_{t+1} < x_t`: `Râ(x) + y_max − rb < x` for every `x > x*`. -/
theorem lemma_8_3_3 (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → M.next (S.sav x) M.ymax < x := by
  by_cases hbdd : ∃ K, ∀ x, M.xmin ≤ x → S.sav x ≤ K
  · obtain ⟨K, hK⟩ := hbdd
    refine ⟨max M.xmin (M.next K M.ymax), le_max_left _ _, fun x hx => ?_⟩
    have hx0 : M.xmin ≤ x := (le_max_left _ _).trans hx.le
    have h1 := hK x hx0
    have h2 : M.next (S.sav x) M.ymax ≤ M.next K M.ymax := by
      simp only [SIModel.next]
      nlinarith [M.R_pos]
    exact h2.trans_lt ((le_max_right _ _).trans_lt hx)
  push Not at hbdd
  have hunb : ∀ K, ∃ x, M.xmin ≤ x ∧ K < S.sav x := fun K => by
    obtain ⟨x, hx, h⟩ := hbdd K; exact ⟨x, hx, h⟩
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1 hγ
  set c₀ := max c₁ 1
  have hc₀ : 0 < c₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hγ' : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ := fun c hc =>
    (hc₁ c ((le_max_left _ _).trans hc.le)).le
  have hβR0 : 0 < M.β * M.R := mul_pos M.β_pos M.R_pos
  set ε := (1 - M.β * M.R) / (2 * (M.β * M.R))
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hεβ : M.β * M.R * (1 + ε) < 1 := by
    have key : ∀ p : ℝ, 0 < p → p * (1 + (1 - p) / (2 * p)) = (1 + p) / 2 := fun p hp => by
      field_simp; ring
    have : M.β * M.R * (1 + ε) = (1 + M.β * M.R) / 2 := key _ hβR0
    rw [this]; linarith
  set L := Real.log (1 + ε)
  have hL : 0 < L := Real.log_pos (by linarith)
  set Δ := M.ymax - M.ymin
  have hΔ : 0 ≤ Δ := sub_nonneg.2 M.ymin_le_ymax
  set C₁ := max (c₀ + 1) (γ * Δ / L + 1)
  obtain ⟨X₂, hX₂, hcX₂⟩ := S.cons_unbounded hβR hunb C₁
  obtain ⟨X₃, hX₃, hsX₃⟩ := S.sav_eventually_gt hunb (max 0 ((X₂ - M.xmin) / M.R))
  refine ⟨X₃, hX₃, fun x hx => ?_⟩
  have hx0 : M.xmin ≤ x := hX₃.trans hx.le
  have hsK := hsX₃ x hx.le
  have hs0 : 0 < S.sav x := lt_of_le_of_lt (le_max_left _ _) hsK
  have hsX : (X₂ - M.xmin) / M.R < S.sav x := lt_of_le_of_lt (le_max_right _ _) hsK
  set s := S.sav x
  set m := M.next s M.ymin
  set Mx := M.next s M.ymax
  have hm : X₂ ≤ m := by
    rw [show m = M.R * s + M.xmin from M.next_ymin _, ← sub_le_iff_le_add]
    rw [div_lt_iff₀ M.R_pos] at hsX
    linarith
  have hcm : C₁ < S.cons m := hcX₂ m hm
  have hcm0 : c₀ ≤ S.cons m := by
    have : c₀ + 1 ≤ C₁ := le_max_left _ _
    linarith
  have hcmpos : 0 < S.cons m := hc₀.trans_le hcm0
  obtain ⟨-, hD⟩ := S.eq_8_16 hddu hc₀ hγ0.le hγ' hs0.le hcm0
  have hpow : (1 + Δ / S.cons m) ^ γ ≤ 1 + ε := by
    refine (SIModel.si_one_add_rpow_le (div_nonneg hΔ hcmpos.le) hγ0.le).trans ?_
    rw [← Real.exp_log (show 0 < 1 + ε by linarith)]
    refine Real.exp_le_exp.2 ?_
    have hC : γ * Δ / L < S.cons m := by
      have : γ * Δ / L + 1 ≤ C₁ := le_max_right _ _
      linarith
    rw [div_lt_iff₀ hL] at hC
    rw [mul_div_assoc', div_le_iff₀ hcmpos]
    linarith
  have hmx : M.xmin ≤ m := M.next_ge hs0.le le_rfl
  have hMx : M.xmin ≤ Mx := hmx.trans (by
    have := M.next_ymax_sub s; linarith [M.ymin_le_ymax] : m ≤ Mx)
  have hdVM := S.dV_pos hMx
  have he' := (S.euler hx0).2 hs0
  have he : S.dV x = M.β * M.R * S.D s := by rw [S.envelope x hx0]; exact he'
  have key : S.dV x < S.dV Mx := by
    rw [he]
    calc M.β * M.R * S.D s ≤ M.β * M.R * (S.dV Mx * (1 + ε)) :=
          mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_left hpow hdVM.le))
            hβR0.le
      _ = (M.β * M.R * (1 + ε)) * S.dV Mx := by ring
      _ < 1 * S.dV Mx := mul_lt_mul_of_pos_right hεβ hdVM
      _ = S.dV Mx := one_mul _
  by_contra hcon
  push Not at hcon
  have := S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hMx) hcon
  linarith

/-- Lemma 8.3.3 for every income realisation: `x_{t+1} = Râ(x_t) + y − rb < x_t` for all
`y ≤ y_max`. -/
theorem lemma_8_3_3_all (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → ∀ y, y ≤ M.ymax → M.next (S.sav x) y < x := by
  obtain ⟨xs, hxs, h⟩ := S.lemma_8_3_3 hβR hddu hγ0 hγ
  refine ⟨xs, hxs, fun x hx y hy => lt_of_le_of_lt ?_ (h x hx)⟩
  simp only [SIModel.next]; linarith

/-- The fixed points of the highest-income map `x ↦ Râ(x) + y_max − rb` in `[x_min, ∞)`. -/
def fixHigh : Set ℝ := {x | M.xmin ≤ x ∧ M.next (S.sav x) M.ymax = x}

/-- `x_max` (Miao, p. 254): the largest fixed point of `x ↦ Râ(x) + y_max − rb`. -/
noncomputable def xmax : ℝ := sSup S.fixHigh

/-- `x ↦ Râ(x) + y_max − rb − x` is continuous on `[x_min, ∞)`. -/
theorem continuousOn_gap : ContinuousOn (fun x => M.next (S.sav x) M.ymax - x)
    (Set.Ici M.xmin) :=
  ((M.continuous_next M.ymax).comp_continuousOn S.continuousOn_sav).sub continuousOn_id

/-- **Exercise 8.9** (Miao, p. 289). Let `βR < 1`, the relative risk aversion be below `γ > 0`
for large `c`, and `y_min < y_max`. Then `x_max` is the largest solution of
`Râ(x) + y_max − rb = x` in `[x_min, ∞)`, `x_max > x_min`, every `x > x_max` has
`Râ(x) + y_max − rb < x`, and `x_max` is the smallest critical value `x*` of Lemma 8.3.3. -/
theorem ex_8_9 (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) :
    M.xmin < S.xmax ∧ IsGreatest S.fixHigh S.xmax ∧
      (∀ x, S.xmax < x → M.next (S.sav x) M.ymax < x) ∧
      IsLeast {xs | M.xmin ≤ xs ∧ ∀ x, xs < x → M.next (S.sav x) M.ymax < x} S.xmax := by
  obtain ⟨xs, hxs, hcrit⟩ := S.lemma_8_3_3 hβR hddu hγ0 hγ
  set h : ℝ → ℝ := fun x => M.next (S.sav x) M.ymax - x
  have hcont := S.continuousOn_gap
  have hh0 : 0 < h M.xmin := by
    have := mul_nonneg M.R_pos.le (S.sav_mem M.xmin le_rfl).1
    have e : h M.xmin = M.R * S.sav M.xmin + (M.ymax - M.ymin) := by
      simp only [h, SIModel.next, SIModel.xmin]; ring
    rw [e]
    linarith
  have hneg : ∀ x, xs < x → h x < 0 := fun x hx => by
    have := hcrit x hx; simp only [h]; linarith
  have hbdd : BddAbove S.fixHigh := ⟨xs, fun x hx => by
    by_contra hcon
    push Not at hcon
    have := hcrit x hcon
    rw [hx.2] at this
    exact lt_irrefl _ this⟩
  have hzero : ∀ a b, M.xmin ≤ a → a ≤ b → 0 ≤ h a → h b < 0 → ∃ z ∈ S.fixHigh, a ≤ z := by
    intro a b ha hab hha hhb
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hab
      (hcont.mono fun w hw => Set.mem_Ici.2 (ha.trans hw.1)) ⟨hhb.le, hha⟩
    refine ⟨z, ⟨ha.trans hz.1, ?_⟩, hz.1⟩
    linarith
  obtain ⟨z₀, hz₀, -⟩ := hzero M.xmin (xs + 1) le_rfl (by linarith) hh0.le (hneg _ (by linarith))
  have hne : S.fixHigh.Nonempty := ⟨z₀, hz₀⟩
  have hclosed : IsClosed S.fixHigh := by
    have : S.fixHigh = Set.Ici M.xmin ∩ h ⁻¹' {0} := by
      ext x
      simp only [fixHigh, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage,
        Set.mem_singleton_iff, h, sub_eq_zero]
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hmem : S.xmax ∈ S.fixHigh := hclosed.csSup_mem hne hbdd
  have hgt : M.xmin < S.xmax := by
    rcases hmem.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have h2 := hmem.2
      rw [← heq] at h2
      have : h M.xmin = 0 := by simp only [h]; linarith
      linarith
  have habove : ∀ x, S.xmax < x → M.next (S.sav x) M.ymax < x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hx0 : M.xmin ≤ x := hgt.le.trans hx.le
    obtain ⟨z, hz, hxz⟩ := hzero x (max x xs + 1) hx0 (by linarith [le_max_left x xs])
      (by simp only [h]; linarith) (hneg _ (by linarith [le_max_right x xs]))
    have := le_csSup hbdd hz
    change z ≤ S.xmax at this
    linarith
  refine ⟨hgt, ⟨hmem, fun x hx => le_csSup hbdd hx⟩, habove, ⟨⟨hgt.le, habove⟩, ?_⟩⟩
  rintro xs' ⟨-, hxs'⟩
  by_contra hcon
  push Not at hcon
  have := hxs' _ hcon
  rw [hmem.2] at this
  exact lt_irrefl _ this

/-- Miao, p. 254: if `x_f ≥ x_min` is a fixed point of `x ↦ Râ(x) + y_max − rb`, the interval
`[x_min, x_f]` is invariant: `x ∈ [x_min, x_f]` and `y ∈ [y_min, y_max]` give
`Râ(x) + y − rb ∈ [x_min, x_f]`. With `x_f = x_max` this is the long-run interval. -/
theorem mapsTo_Icc {xf : ℝ} (hxf : M.xmin ≤ xf) (hfix : M.next (S.sav xf) M.ymax = xf) {x y : ℝ}
    (hx : x ∈ Set.Icc M.xmin xf) (hy : y ∈ Set.Icc M.ymin M.ymax) :
    M.next (S.sav x) y ∈ Set.Icc M.xmin xf := by
  refine ⟨M.next_ge (S.sav_mem x hx.1).1 hy.1, ?_⟩
  have h1 := S.sav_mono (Set.mem_Ici.2 hx.1) (Set.mem_Ici.2 hxf) hx.2
  have h2 : M.next (S.sav x) y ≤ M.next (S.sav xf) M.ymax := by
    simp only [SIModel.next]
    nlinarith [M.R_pos, hy.2]
  rwa [hfix] at h2

end SIModel.Solution

end Miao.IncompleteMarkets
