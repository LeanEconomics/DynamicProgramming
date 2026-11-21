/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.SIBounded

/-!
# §8.3.2, Cases 2 and 3 (`βR > 1`, `βR = 1`): Proposition 8.3.2 and Lemma 8.3.4

Miao, §8.3.2, pp. 256–259.

**Case 2, `βR > 1`.**
* `eq_8_7` (module `SIEuler`) is the one-step supermartingale inequality
  `E_t M_{t+1} ≤ M_t` for `M_t = βᵗRᵗu′(c_t)` (p. 257). The Supermartingale Convergence Theorem
  on the path space is not formalised; `supermartingale_limit` proves its consequence used in
  the text: if `M_t` converges and `βR > 1`, then `u′(c_t) → 0` and `c_t → ∞`, hence
  `x_t ≥ c_t → ∞`.
* **Proposition 8.3.2** (Sotomayor): (i) `proposition_8_3_2_i`, `â(x) → ∞`; (ii)
  `proposition_8_3_2_ii`, with the relative risk aversion below `γ` for large `c`, there is `x̃`
  with `x_{t+1} > x_t` whenever `x_t > x̃` (for every income `y ≥ y_min`). The proof of (ii)
  needs `c(x) → ∞` (`cons_unbounded_gt`, "a similar argument in the proof of Lemma 8.3.3").

**Case 3, `βR = 1`.**
* `limit_of_converge` (p. 258): along any path `x_{t+1} = Râ(x_t) + y_{t+1} − rb`, if `x_t`
  converges then so does `y_t`; hence (`not_converge`) `x_t` cannot converge if `y_t` is
  infinitely often near `y_min` and infinitely often near `y_max`.
* `sotomayor_bounds` (p. 259): where the constraint does not bind,
  `Râ(x) + y_min − rb ≤ x ≤ Râ(x) + y_max − rb`; `sotomayor_fall`: if
  `x > Râ(x) + y_min − rb` then `x_{t+1} < x_t` with positive probability.
* **Lemma 8.3.4** (Sotomayor; `lemma_8_3_4`): there is no `x̃` with `x = Râ(x) + y_min − rb`
  for all `x > x̃`.

**Corrections.** (1) The display in the proof of Proposition 8.3.2(ii) has the ratio
`(c(y_max − rb + Râ)/c(y_min − rb + Râ))^γ`, which is `≥ 1`; footnote 2 gives the reciprocal
`(c(m)/c(M))^γ ≤ 1`, which tends to `1` (`proposition_8_3_2_ii`). (2) Case 3: "the set of
sample paths for which there are infinitely many `t` with `y_{t+1} = y_min` has probability
one" requires `μ({y_min}) > 0`; with a density it has probability zero. The argument works with
"`y_{t+1} ≤ y_min + δ` infinitely often" (`not_converge`). (3) Lemma 8.3.4 needs income to be
non-degenerate, `μ((y_min, ∞)) > 0`; this is the hypothesis `hnd`.
-/

namespace Miao.Applications

open MeasureTheory Filter Topology

namespace SIModel

variable (M : SIModel)

/-- Miao, p. 257: if `M_t = (βR)ᵗu′(c_t)` converges (the Supermartingale Convergence Theorem),
`c_t > 0` and `βR > 1`, then `u′(c_t) → 0` and `c_t → ∞`; with `x_t ≥ c_t`, also `x_t → ∞`. -/
theorem supermartingale_limit (hβR : 1 < M.β * M.R) {c x : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    (hxc : ∀ t, c t ≤ x t) {L : ℝ}
    (hM : Tendsto (fun t => (M.β * M.R) ^ t * M.du (c t)) atTop (𝓝 L)) :
    Tendsto (fun t => M.du (c t)) atTop (𝓝 0) ∧ Tendsto c atTop atTop ∧
      Tendsto x atTop atTop := by
  have hq : Tendsto (fun t => ((M.β * M.R) ^ t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hβR)
  have hdu : Tendsto (fun t => M.du (c t)) atTop (𝓝 0) := by
    have h := hq.mul hM
    rw [zero_mul] at h
    refine h.congr fun t => ?_
    have : (M.β * M.R) ^ t ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
  have hc' : Tendsto c atTop atTop := by
    refine tendsto_atTop.2 fun C => ?_
    have hC : 0 < M.du (max C 1) := M.du_pos _ (lt_of_lt_of_le one_pos (le_max_right _ _))
    filter_upwards [hdu.eventually (gt_mem_nhds hC)] with t ht
    by_contra hcon
    push Not at hcon
    have := M.du_anti.antitoneOn (Set.mem_Ioi.2 (hc t))
      (Set.mem_Ioi.2 (lt_of_lt_of_le one_pos (le_max_right C 1)))
      (hcon.le.trans (le_max_left _ _))
    linarith
  exact ⟨hdu, hc', tendsto_atTop_mono hxc hc'⟩

end SIModel

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

/-- **Proposition 8.3.2 (i)** (Sotomayor (1984); Miao, p. 257). If `βR > 1` then
`lim_{x → ∞} â(x) = ∞`. -/
theorem proposition_8_3_2_i (hβR : 1 < M.β * M.R) (K : ℝ) :
    ∃ X, M.xmin ≤ X ∧ ∀ x, X ≤ x → K < S.sav x := by
  refine S.sav_eventually_gt (fun K => ?_) K
  by_contra hcon
  push Not at hcon
  have hk : 0 ≤ K := (S.sav_mem M.xmin le_rfl).1.trans (hcon M.xmin le_rfl)
  set z₀ := M.next K M.ymax
  have hz₀ : M.xmin ≤ z₀ := M.next_ge hk M.ymin_le_ymax
  have he : M.β * M.R * S.D (S.sav z₀) ≤ S.dV z₀ := by
    rw [S.envelope z₀ hz₀]; exact S.euler_le hz₀
  have h1 := S.D_strictAnti.antitoneOn (Set.mem_Ici.2 (S.sav_mem z₀ hz₀).1) (Set.mem_Ici.2 hk)
    (hcon z₀ hz₀)
  have h2 := S.high_le_D hk
  have hpos := S.dV_pos hz₀
  have hβR0 : 0 ≤ M.β * M.R := by linarith
  have : M.β * M.R * S.dV z₀ ≤ S.dV z₀ :=
    (mul_le_mul_of_nonneg_left (h2.trans h1) hβR0).trans he
  nlinarith

/-- Miao, p. 258 ("a similar argument in the proof of Lemma 8.3.3"): if `βR > 1`, then
`c(x) → ∞`. -/
theorem cons_unbounded_gt (hβR : 1 < M.β * M.R) (C : ℝ) :
    ∃ X, M.xmin ≤ X ∧ ∀ x, X ≤ x → C < S.cons x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, M.xmin ≤ x → S.cons x ≤ C := ⟨C, fun x hx => by
    obtain ⟨x', hx', hc'⟩ := hcon x hx
    exact (S.cons_mono (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hx')) hx').trans hc'⟩
  have hne : (S.cons '' Set.Ici M.xmin).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.2 le_rfl)⟩
  have hbdd : BddAbove (S.cons '' Set.Ici M.xmin) := ⟨C, by
    rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  set cbar := sSup (S.cons '' Set.Ici M.xmin)
  have hle : ∀ x, M.xmin ≤ x → S.cons x ≤ cbar := fun x hx =>
    le_csSup hbdd (Set.mem_image_of_mem _ (Set.mem_Ici.2 hx))
  have hcbar : 0 < cbar := (S.cons_pos le_rfl).trans_le (hle _ le_rfl)
  have hlt : M.du cbar < M.β * M.R * M.du cbar := by
    have := M.du_pos cbar hcbar; nlinarith
  have hcont : Tendsto M.du (𝓝 cbar) (𝓝 (M.du cbar)) :=
    ((M.du_cont _ (Set.mem_Ioi.2 hcbar)).continuousAt (Ioi_mem_nhds hcbar)).tendsto
  obtain ⟨z, hz, hz0⟩ := ((hcont.eventually_lt_const hlt).filter_mono nhdsWithin_le_nhds |>.and
    (Ioo_mem_nhdsLT hcbar) : ∀ᶠ w in 𝓝[<] cbar, _ ∧ w ∈ Set.Ioo 0 cbar).exists
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hzx⟩ := exists_lt_of_lt_csSup hne hz0.2
  obtain ⟨X, hX, hXK⟩ := S.proposition_8_3_2_i hβR 0
  set x := max X x₁
  have hx : M.xmin ≤ x := hX.trans (le_max_left _ _)
  have hs0 : 0 < S.sav x := hXK x (le_max_left _ _)
  have he := (S.euler hx).2 hs0
  set Mx := M.next (S.sav x) M.ymax
  have hMx : M.xmin ≤ Mx := M.next_ge hs0.le M.ymin_le_ymax
  have hD := S.high_le_D hs0.le
  rw [S.envelope Mx hMx] at hD
  have hcx : z < S.cons x := hzx.trans_le (S.cons_mono (Set.mem_Ici.2 hx₁) (Set.mem_Ici.2 hx)
    (le_max_right _ _))
  have h1 := M.du_anti (Set.mem_Ioi.2 hz0.1) (Set.mem_Ioi.2 (hz0.1.trans hcx)) hcx
  have h2 := M.du_anti.antitoneOn (Set.mem_Ioi.2 (S.cons_pos hMx)) (Set.mem_Ioi.2 hcbar)
    (hle Mx hMx)
  have hβR0 : 0 ≤ M.β * M.R := by linarith
  have h3 : M.β * M.R * M.du cbar ≤ M.β * M.R * S.D (S.sav x) :=
    mul_le_mul_of_nonneg_left (h2.trans hD) hβR0
  linarith

/-- **Proposition 8.3.2 (ii)** (Sotomayor (1984); Miao, p. 257). Let `βR > 1` and
`−cu′′(c)/u′(c) < γ` for all `c` sufficiently large (`γ > 0`). Then there is `x̃` such that
`x_t > x̃` implies `x_{t+1} > x_t`: `x < Râ(x) + y_min − rb` for all `x > x̃`. -/
theorem proposition_8_3_2_ii (hβR : 1 < M.β * M.R) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xt, M.xmin ≤ xt ∧ ∀ x, xt < x → x < M.next (S.sav x) M.ymin := by
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1 hγ
  set c₀ := max c₁ 1
  have hc₀ : 0 < c₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hγ' : ∀ c, c₀ < c → -c * ddu c / M.du c ≤ γ := fun c hc =>
    (hc₁ c ((le_max_left _ _).trans hc.le)).le
  set L := Real.log (M.β * M.R)
  have hL : 0 < L := Real.log_pos hβR
  set Δ := M.ymax - M.ymin
  have hΔ : 0 ≤ Δ := sub_nonneg.2 M.ymin_le_ymax
  set C₁ := max (c₀ + 1) (γ * Δ / L + 1)
  obtain ⟨X₂, hX₂, hcX₂⟩ := S.cons_unbounded_gt hβR C₁
  obtain ⟨X₃, hX₃, hsX₃⟩ := S.proposition_8_3_2_i hβR (max 0 ((X₂ - M.xmin) / M.R))
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
  have hmx : M.xmin ≤ m := M.next_ge hs0.le le_rfl
  have hmM : m ≤ Mx := by have := M.next_ymax_sub s; linarith
  have hMx : M.xmin ≤ Mx := hmx.trans hmM
  have hcmM : S.cons m ≤ S.cons Mx := S.cons_mono (Set.mem_Ici.2 hmx) (Set.mem_Ici.2 hMx) hmM
  have hcMpos : 0 < S.cons Mx := hcmpos.trans_le hcmM
  -- footnote 2: `u′(c(M)) ≥ u′(c(m)) (c(m)/c(M))^γ`
  have hfoot := M.footnote_2_mono hddu hc₀ hγ' (Set.mem_Ici.2 hcm0)
    (Set.mem_Ici.2 (hcm0.trans hcmM)) hcmM
  simp only at hfoot
  have hratio : M.du (S.cons m) * (S.cons m / S.cons Mx) ^ γ ≤ M.du (S.cons Mx) := by
    rw [Real.div_rpow hcmpos.le hcMpos.le, ← mul_div_assoc,
      div_le_iff₀ (Real.rpow_pos_of_pos hcMpos γ)]
    exact hfoot
  -- `(c(m)/c(M))^γ ≥ e^{−γΔ/c(m)} > 1/(βR)`
  have hq : S.cons m / (S.cons m + Δ) ≤ S.cons m / S.cons Mx :=
    div_le_div_of_nonneg_left hcmpos.le hcMpos (S.cons_high_le hs0.le)
  have hpow1 : (S.cons m / (S.cons m + Δ)) ^ γ ≤ (S.cons m / S.cons Mx) ^ γ :=
    Real.rpow_le_rpow (div_nonneg hcmpos.le (by linarith)) hq hγ0.le
  have he1 : S.cons m / (S.cons m + Δ) = (1 + Δ / S.cons m)⁻¹ := by
    field_simp
  have hexp : Real.exp (-(γ * (Δ / S.cons m))) ≤ (S.cons m / (S.cons m + Δ)) ^ γ := by
    rw [he1, Real.inv_rpow (by positivity), Real.exp_neg]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) γ)
      (SIModel.si_one_add_rpow_le (div_nonneg hΔ hcmpos.le) hγ0.le)
  have hgt : (M.β * M.R)⁻¹ < Real.exp (-(γ * (Δ / S.cons m))) := by
    rw [← Real.exp_log (show 0 < M.β * M.R by linarith), ← Real.exp_neg]
    refine Real.exp_lt_exp.2 (neg_lt_neg ?_)
    have hC : γ * Δ / L < S.cons m := by
      have : γ * Δ / L + 1 ≤ C₁ := le_max_right _ _
      linarith
    rw [div_lt_iff₀ hL] at hC
    rw [mul_div_assoc', div_lt_iff₀ hcmpos]
    linarith
  have hdum := M.du_pos _ hcmpos
  have he' := (S.euler hx0).2 hs0
  have he : S.dV x = M.β * M.R * S.D s := by rw [S.envelope x hx0]; exact he'
  have hD := S.high_le_D hs0.le
  have hMx' : S.dV Mx = M.du (S.cons Mx) := S.envelope Mx hMx
  have hm' : S.dV m = M.du (S.cons m) := S.envelope m hmx
  rw [hMx'] at hD
  have hne : M.β * M.R ≠ 0 := by linarith
  have key : S.dV m < S.dV x := by
    rw [he, hm']
    have h1 : M.du (S.cons m) * (M.β * M.R)⁻¹ < M.du (S.cons m) * (S.cons m / S.cons Mx) ^ γ :=
      mul_lt_mul_of_pos_left (hgt.trans_le (hexp.trans hpow1)) hdum
    have h2 : M.du (S.cons m) = M.β * M.R * (M.du (S.cons m) * (M.β * M.R)⁻¹) := by
      rw [mul_comm (M.du _) _, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h2]
    exact mul_lt_mul_of_pos_left (h1.trans_le (hratio.trans hD)) (by linarith)
  by_contra hcon
  push Not at hcon
  have := S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hmx) (Set.mem_Ici.2 hx0) hcon
  linarith

/-- Proposition 8.3.2 (ii) for every income realisation `y ≥ y_min`:
`x < Râ(x) + y_min − rb ≤ x_{t+1}`. -/
theorem proposition_8_3_2_ii_all (hβR : 1 < M.β * M.R) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xt, M.xmin ≤ xt ∧ ∀ x, xt < x → ∀ y, M.ymin ≤ y → x < M.next (S.sav x) y := by
  obtain ⟨xt, hxt, h⟩ := S.proposition_8_3_2_ii hβR hddu hγ0 hγ
  refine ⟨xt, hxt, fun x hx y hy => (h x hx).trans_le ?_⟩
  simp only [SIModel.next]; linarith

/-! ### Case 3: `βR = 1` -/

/-- Miao, p. 258: along a path `x_{t+1} = Râ(x_t) + y_{t+1} − rb` with `x_t ≥ x_min`, if
`x_t → x_∞` then `y_t → x_∞ − Râ(x_∞) + rb` (`â` is continuous). -/
theorem limit_of_converge {x y : ℕ → ℝ} (hx : ∀ t, M.xmin ≤ x t)
    (hrec : ∀ t, x (t + 1) = M.next (S.sav (x t)) (y (t + 1))) {L : ℝ}
    (hL : Tendsto x atTop (𝓝 L)) :
    Tendsto (fun t => y (t + 1)) atTop (𝓝 (L - M.R * S.sav L + M.r * M.b)) := by
  have hLm : M.xmin ≤ L := ge_of_tendsto' hL hx
  have hs : Tendsto (fun t => S.sav (x t)) atTop (𝓝 (S.sav L)) :=
    (S.continuousOn_sav L (Set.mem_Ici.2 hLm)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hL, Eventually.of_forall fun t => Set.mem_Ici.2 (hx t)⟩)
  have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have h2 := (h1.sub (hs.const_mul M.R)).add_const (M.r * M.b)
  refine h2.congr fun t => ?_
  rw [hrec t]; simp only [SIModel.next]; ring

/-- Miao, p. 258, corrected: if income is infinitely often within `δ` of `y_min` and infinitely
often within `δ` of `y_max`, with `2δ < y_max − y_min`, then cash on hand does not converge. -/
theorem not_converge {x y : ℕ → ℝ} (hx : ∀ t, M.xmin ≤ x t)
    (hrec : ∀ t, x (t + 1) = M.next (S.sav (x t)) (y (t + 1))) {δ : ℝ}
    (hδ : 2 * δ < M.ymax - M.ymin) (hlow : ∃ᶠ t in atTop, y (t + 1) ≤ M.ymin + δ)
    (hhigh : ∃ᶠ t in atTop, M.ymax - δ ≤ y (t + 1)) (L : ℝ) : ¬ Tendsto x atTop (𝓝 L) := by
  intro hL
  have hy := S.limit_of_converge hx hrec hL
  set ℓ := L - M.R * S.sav L + M.r * M.b
  have hl : ℓ ≤ M.ymin + δ := le_of_tendsto_of_frequently hy hlow
  have hh : M.ymax - δ ≤ ℓ := ge_of_tendsto_of_frequently hy hhigh
  linarith

/-- Miao, p. 259 (`βR = 1`): where the borrowing constraint does not bind,
`Râ(x) + y_min − rb ≤ x ≤ Râ(x) + y_max − rb`. -/
theorem sotomayor_bounds (hβR : M.β * M.R = 1) {x : ℝ} (hx : M.xmin ≤ x)
    (hpos : 0 < S.sav x) :
    M.next (S.sav x) M.ymin ≤ x ∧ x ≤ M.next (S.sav x) M.ymax := by
  have he' := (S.euler hx).2 hpos
  have he : S.dV x = S.D (S.sav x) := by rw [S.envelope x hx, ← one_mul (S.D _), ← hβR]; exact he'
  have hm : M.xmin ≤ M.next (S.sav x) M.ymin := M.next_ge hpos.le le_rfl
  have hM : M.xmin ≤ M.next (S.sav x) M.ymax := M.next_ge hpos.le M.ymin_le_ymax
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 := S.dV_strictAnti (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hm) hcon
    have h2 := S.D_le_low hpos.le
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 := S.dV_strictAnti (Set.mem_Ici.2 hM) (Set.mem_Ici.2 hx) hcon
    have h2 := S.high_le_D hpos.le
    linarith

/-- Miao, p. 259: if `x > Râ(x) + y_min − rb`, then `x_{t+1} = Râ(x) + y_{t+1} − rb < x_t` with
positive probability (under `μ([a, b]) ≥ α(b − a)`, `y_min < y_max`). -/
theorem sotomayor_fall (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b))
    {x : ℝ} (hlt : M.next (S.sav x) M.ymin < x) :
    0 < M.law {y | M.next (S.sav x) y < x} := by
  set ε := min ((x - M.next (S.sav x) M.ymin) / 2) (M.ymax - M.ymin)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have h1 := hμ M.ymin (M.ymin + ε) le_rfl (by linarith) (by
    have := min_le_right ((x - M.next (S.sav x) M.ymin) / 2) (M.ymax - M.ymin); linarith)
  have hpos : 0 < M.law.real (Set.Icc M.ymin (M.ymin + ε)) := by
    have : 0 < α * (M.ymin + ε - M.ymin) := mul_pos hα (by linarith)
    linarith
  have hne : M.law (Set.Icc M.ymin (M.ymin + ε)) ≠ 0 := fun h0 => by
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  refine (pos_iff_ne_zero.2 hne).trans_le (measure_mono ?_)
  intro y hy'
  have hε2 : ε ≤ (x - M.next (S.sav x) M.ymin) / 2 := min_le_left _ _
  have e : M.next (S.sav x) y = M.next (S.sav x) M.ymin + (y - M.ymin) := by
    simp only [SIModel.next]; ring
  change M.next (S.sav x) y < x
  linarith [hy'.2]

/-- **Lemma 8.3.4** (Sotomayor (1984); Miao, p. 259). Let `βR = 1` and income be
non-degenerate, `μ((y_min, ∞)) > 0`. Then there is no `x̃` with `x = Râ(x) + y_min − rb` for
all `x > x̃`. -/
theorem lemma_8_3_4 (hβR : M.β * M.R = 1) (hnd : 0 < M.law (Set.Ioi M.ymin)) :
    ¬ ∃ xt, ∀ x, xt < x → x = M.next (S.sav x) M.ymin := by
  rintro ⟨xt, hxt⟩
  set x := max xt M.xmin + 1
  have hx : xt < x := by simp only [x]; linarith [le_max_left xt M.xmin]
  have hx0 : M.xmin < x := by simp only [x]; linarith [le_max_right xt M.xmin]
  have hfix := hxt x hx
  have hs0 : 0 < S.sav x := by
    by_contra hcon
    push Not at hcon
    have hz : S.sav x = 0 := le_antisymm hcon (S.sav_mem x hx0.le).1
    rw [hz, M.next_ymin, mul_zero, zero_add] at hfix
    linarith
  set s := S.sav x
  have he' := (S.euler hx0.le).2 hs0
  have he : S.dV x = S.D s := by
    rw [S.envelope x hx0.le, ← one_mul (S.D _), ← hβR]; exact he'
  set m := M.next s M.ymin
  have hmx : M.xmin ≤ m := M.next_ge hs0.le le_rfl
  -- `E V′(Rs + y − rb) < V′(m)`, strictly
  have hlt : S.D s < S.dV m := by
    have hint := (integrable_const (S.dV m)).sub (S.integrable_dV hs0.le)
    have hnn : 0 ≤ᵐ[M.law] fun y => S.dV m - S.dV (M.next s y) := by
      filter_upwards [M.supp] with y hy
      refine sub_nonneg.2 (S.dV_strictAnti.antitoneOn (Set.mem_Ici.2 hmx)
        (Set.mem_Ici.2 (M.next_ge hs0.le hy.1)) ?_)
      simp only [m, SIModel.next]; linarith [hy.1]
    have hpos : 0 < ∫ y, (S.dV m - S.dV (M.next s y)) ∂M.law := by
      refine (integral_pos_iff_support_of_nonneg_ae hnn hint).2
        (hnd.trans_le (measure_mono fun y hy => ?_))
      have hlt' : m < M.next s y := by
        simp only [m, SIModel.next]; linarith [Set.mem_Ioi.1 hy]
      exact (sub_pos.2 (S.dV_strictAnti (Set.mem_Ici.2 hmx)
        (Set.mem_Ici.2 (hmx.trans hlt'.le)) hlt')).ne'
    rw [integral_sub (integrable_const _) (S.integrable_dV hs0.le)] at hpos
    simp only [integral_const, probReal_univ, one_smul] at hpos
    change 0 < S.dV m - S.D s at hpos
    linarith
  have : S.dV x = S.dV m := by rw [← hfix]
  linarith

end SIModel.Solution

end Miao.Applications
