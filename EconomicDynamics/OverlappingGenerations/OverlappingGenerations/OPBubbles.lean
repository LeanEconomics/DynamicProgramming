/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OPEfficiency

/-!
# Asset price bubbles in the Diamond model

Miao, §16.3, pp. 551–555 (Tirole 1985). The initial old hold an unbacked government debt `B₁`
that is rolled over forever; `b_t = B_t/N_t`.

* Capital-market clearing (16.18) `g_n(k_{t+1} + b_{t+1}) = s(w_t, R_{t+1})` and no arbitrage
  (16.19) `g_nb_{t+1} = R_tb_t` (`eq_16_18`, `eq_16_19`); the bubble equilibrium
  (`OPIsBubbleEqm`); with `b = 0` it is the Diamond equilibrium (`op_bubble_zero`); a positive
  initial bubble stays positive (`op_bubble_pos`); combining the two equations,
  `g_nk_{t+1} = s(w_t, R_{t+1}) − R_tb_t` (`op_bubble_k_law`).
* The bubbly steady state has `R(k) = g_n`: the golden rule `k = k_G`, with
  `b* = s(w(k_G), g_n)/g_n − k_G` (`op_bubbly_steady`, `op_bubbly_steady_golden`).
  (The text's `g_b(b + k)` is a misprint for `g_n(b + k)`.)
* The locus `Δk_t = 0`: `b = [s(w(k), R(k)) − g_nk]/R(k)` (`opKLocus`, `op_k_locus`); it
  vanishes exactly at the Diamond steady states (`op_kLocus_zero_iff`); it is positive where
  `G(k) > k` and negative where `G(k) < k` (`op_kLocus_pos`, `op_kLocus_neg`), so (with the
  corrected Diamond conditions) positive on `(0, k_D)`, negative beyond.
* Its slope at a zero: `db/dk = (−s_wkf″ + s_Rf″ − g_n)/R(k)` (`op_kLocus_hasDerivAt`).
  **Correction:** the text divides by `R²(k)` (`op_kLocus_slope_printed`). Under the Diamond
  conditions `db/dk(k_D) < 0` (`op_kLocus_slope_neg`).
* The vector fields: with `s_R ≥ 0`, `k_{t+1} > k_t ⟺ b_t < b(k_t)` (`op_k_increase_iff`,
  `op_k_decrease_iff`, `op_k_stationary_iff`); `b_{t+1} − b_t = (R_t/g_n − 1)b_t`
  (`op_b_diff`), `b_{t+1} > b_t ⟺ k_t < k_G` (`op_b_increase_iff`), and `Δb = 0` is the line
  `k = k_G` (`op_b_stationary_iff`). The text's middle step replaces `R(k_{t+1})` by `R(k_t)`;
  this is valid as an equivalence when `s_R ≥ 0`, which the proof uses.
* A bubbly steady state exists iff `k_G < k_D` iff `R_D < g_n`: the bubbleless economy is
  dynamically inefficient (`op_bubbly_exists_iff`).

The saddle-point property of the bubbly steady state is proved for the linearised system in
Exercise 16.9 (`ex_16_9_saddle`). Not formalised: the global claims read off Figure 16.13 (the
nonlinear saddle path `b₁ = b(k₁)` and convergence to `k_D` for `b₁ < b(k₁)`), and the
literature survey on p. 555.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, (16.18), p. 552: `N_ts_t = B_{t+1} + K_{t+1}` in per capita terms is
`g_n(k_{t+1} + b_{t+1}) = s_t`. -/
theorem eq_16_18 {N N' sv B' K' b' k' gn : ℝ} (hN : N ≠ 0) (hcm : N * sv = B' + K')
    (hB' : B' = b' * N') (hK' : K' = k' * N') (hN' : N' = gn * N) :
    gn * (k' + b') = sv := by
  rw [hB', hK', hN'] at hcm
  have : N * (gn * (k' + b') - sv) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hN
  linarith

/-- Miao, (16.19), p. 552: no arbitrage `B_{t+1} = R_tB_t` in per capita terms is
`g_nb_{t+1} = R_tb_t`. -/
theorem eq_16_19 {N N' B B' b b' R gn : ℝ} (hN : N ≠ 0) (h : B' = R * B) (hB : B = b * N)
    (hB' : B' = b' * N') (hN' : N' = gn * N) : gn * b' = R * b := by
  rw [hB', hB, hN'] at h
  have : N * (gn * b' - R * b) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hN
  linarith

/-- An equilibrium with a bubble (Miao, p. 552): `(k_t, b_t)` with `k_t > 0` satisfying (16.18)
and (16.19), where `w_t = w(k_t)`, `R_t = R(k_t)`. -/
def OPIsBubbleEqm (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn : ℝ) (k b : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ gn * (k (t + 1) + b (t + 1)) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) ∧
    gn * b (t + 1) = opRate fp (k t) * b t

/-- Miao, p. 552: "if `b_t = 0`, then (16.19) is redundant and (16.18) reduces to (16.16)": a
bubble equilibrium with `b₁ = 0` has `b_t = 0` for all `t` and is a Diamond equilibrium. -/
theorem op_bubble_zero {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k b : ℕ → ℝ} (hgn : 0 < gn)
    (h : OPIsBubbleEqm s f fp gn k b) (hb0 : b 0 = 0) :
    (∀ t, b t = 0) ∧ OPIsDiamondEqm s f fp gn k := by
  have hb : ∀ t, b t = 0 := by
    intro t
    induction t with
    | zero => exact hb0
    | succ t ih =>
      have := (h t).2.2
      rw [ih, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hgn.ne'
  refine ⟨hb, (op_diamondEqm_iff hgn).2 fun t => ⟨(h t).1, ?_⟩⟩
  have := (h t).2.1
  rwa [hb (t + 1), add_zero] at this

/-- A positive initial bubble stays positive (`R_t > 0`). -/
theorem op_bubble_pos {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k b : ℕ → ℝ} (hgn : 0 < gn)
    (hfp : ∀ k, 0 < k → 0 < fp k) (h : OPIsBubbleEqm s f fp gn k b) (hb0 : 0 < b 0) :
    ∀ t, 0 < b t := by
  intro t
  induction t with
  | zero => exact hb0
  | succ t ih =>
    have he := (h t).2.2
    have hR : 0 < opRate fp (k t) := by simp only [opRate]; linarith [hfp _ (h t).1]
    have : 0 < gn * b (t + 1) := by rw [he]; exact mul_pos hR ih
    exact pos_of_mul_pos_right this hgn.le

/-- Combining (16.18) and (16.19): `g_nk_{t+1} = s(w_t, R_{t+1}) − R_tb_t`. -/
theorem op_bubble_k_law {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k b : ℕ → ℝ}
    (h : OPIsBubbleEqm s f fp gn k b) (t : ℕ) :
    gn * k (t + 1) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) - opRate fp (k t) * b t := by
  have h1 := (h t).2.1
  have h2 := (h t).2.2
  linarith

/-- Miao, pp. 552–553: in a steady state with `b ≠ 0`, `g_n = R(k) = f′(k) + 1` and
`b* = s(w(k), g_n)/g_n − k`. -/
theorem op_bubbly_steady {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k b : ℝ} (hgn : 0 < gn)
    (h1 : gn * (k + b) = s (opWage f fp k) (opRate fp k)) (h2 : gn * b = opRate fp k * b)
    (hb : b ≠ 0) : opRate fp k = gn ∧ fp k = gn - 1 ∧ b = s (opWage f fp k) gn / gn - k := by
  have hR : opRate fp k = gn := by
    have : (gn - opRate fp k) * b = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hb
    linarith
  refine ⟨hR, by simp only [opRate] at hR; linarith, ?_⟩
  rw [← hR] at h1 ⊢
  rw [eq_sub_iff_add_eq, eq_div_iff (by rw [hR]; exact hgn.ne'), add_comm, mul_comm]
  rw [hR] at h1 ⊢
  exact h1

/-- Miao, p. 553: "the bubbly steady state capital stock is equal to the Golden Rule capital
stock". -/
theorem op_bubbly_steady_golden {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k b kG : ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hk : 0 < k) (hkG : 0 < kG) (hG : fp kG = gn - 1)
    (h1 : gn * (k + b) = s (opWage f fp k) (opRate fp k)) (h2 : gn * b = opRate fp k * b)
    (hb : b ≠ 0) : k = kG ∧ b = s (opWage f fp kG) gn / gn - kG := by
  obtain ⟨-, hfk, hbk⟩ := op_bubbly_steady hgn h1 h2 hb
  have hkk : k = kG := op_golden_rule_unique hanti hk hkG hfk hG
  subst hkk
  exact ⟨rfl, hbk⟩

/-! ### The locus `Δk_t = 0` -/

/-- The locus `Δk_t = 0` of Figure 16.11: `b(k) = [s(w(k), R(k)) − g_nk]/R(k)`. -/
noncomputable def opKLocus (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn k : ℝ) : ℝ :=
  (s (opWage f fp k) (opRate fp k) - gn * k) / opRate fp k

/-- Miao, p. 553: on the locus `k_{t+1} = k_t`,
`0 = [s(w(k_t), R(k_t)) − R(k_t)b_t]/g_n − k_t`, i.e. `b_t = b(k_t)`. -/
theorem op_k_locus {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k b : ℝ} (hgn : 0 < gn)
    (hR : 0 < opRate fp k) :
    (s (opWage f fp k) (opRate fp k) - opRate fp k * b) / gn - k = 0 ↔
      b = opKLocus s f fp gn k := by
  unfold opKLocus
  rw [sub_eq_zero, div_eq_iff hgn.ne', eq_div_iff hR.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 553: "this curve crosses the horizontal axis at ... the Diamond steady state":
`b(k) = 0` iff `g_nk = s(w(k), R(k))`, the steady-state condition of (16.16). -/
theorem op_kLocus_zero_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k : ℝ}
    (hR : 0 < opRate fp k) :
    opKLocus s f fp gn k = 0 ↔ gn * k = s (opWage f fp k) (opRate fp k) := by
  unfold opKLocus
  rw [div_eq_zero_iff, or_iff_left hR.ne']
  constructor <;> intro h <;> linarith

/-- With `s_R ≥ 0`: where `G(k) > k`, `s(w(k), R(k)) > g_nk`; where `G(k) < k`, `<`. -/
theorem op_S_vs_G {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn k : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k)
    (hG : 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    (k < G k → gn * k < s (opWage f fp k) (opRate fp k)) ∧
      (G k < k → s (opWage f fp k) (opRate fp k) < gn * k) := by
  have hR1 : ∀ x, 0 < x → opRate fp x ∈ Set.Ioi 1 := fun x hx => by
    simp [opRate, hfp x hx]
  constructor
  · intro h
    have hfa := hanti (show k ∈ Set.Ioi 0 from hk)
      (show G k ∈ Set.Ioi 0 from hG.1) h
    have := hmono (hR1 _ hG.1) (hR1 _ hk) (by simp only [opRate]; linarith)
    nlinarith [hG.2]
  · intro h
    have hfa := hanti (show G k ∈ Set.Ioi 0 from hG.1)
      (show k ∈ Set.Ioi 0 from hk) h
    have := hmono (hR1 _ hk) (hR1 _ hG.1) (by simp only [opRate]; linarith)
    nlinarith [hG.2]

/-- The locus `b(k)` is positive where `G(k) > k` (e.g. on `(0, k_D)`), the substance of
"`db/dk(0) > 0`" (Miao, p. 553). -/
theorem op_kLocus_pos {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn k : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k)
    (hG : 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) (h : k < G k) :
    0 < opKLocus s f fp gn k := by
  have := (op_S_vs_G hgn hmono hanti hfp hk hG).1 h
  unfold opKLocus
  exact div_pos (by linarith) (by simp only [opRate]; linarith [hfp k hk])

/-- The locus `b(k)` is negative where `G(k) < k` (e.g. on `(k_D, ∞)`). -/
theorem op_kLocus_neg {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn k : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k)
    (hG : 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) (h : G k < k) :
    opKLocus s f fp gn k < 0 := by
  have := (op_S_vs_G hgn hmono hanti hfp hk hG).2 h
  unfold opKLocus
  exact div_neg_of_neg_of_pos (by linarith) (by simp only [opRate]; linarith [hfp k hk])

/-- Miao, p. 553: at a zero of the locus (`k = k_D`),
`db/dk = (−s_wkf″(k) + s_Rf″(k) − g_n)/R(k)`. -/
theorem op_kLocus_hasDerivAt {s : ℝ → ℝ → ℝ} {f fp fpp : ℝ → ℝ} {gn k sw sR : ℝ}
    (hs : HasFDerivAt (fun p : ℝ × ℝ => s p.1 p.2)
      (sw • ContinuousLinearMap.fst ℝ ℝ ℝ + sR • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (opWage f fp k, opRate fp k))
    (hf : HasDerivAt f (fp k) k) (hfpk : HasDerivAt fp (fpp k) k) (hR : opRate fp k ≠ 0)
    (hzero : s (opWage f fp k) (opRate fp k) = gn * k) :
    HasDerivAt (opKLocus s f fp gn) ((-sw * k * fpp k + sR * fpp k - gn) / opRate fp k) k := by
  have hw := op_wage_hasDerivAt hf hfpk
  have hRd : HasDerivAt (opRate fp) (fpp k) k := by
    unfold opRate; exact hfpk.const_add 1
  have hg := hs.comp_hasDerivAt k (hw.prodMk hRd)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at hg
  have hN := hg.sub ((hasDerivAt_id' k).const_mul gn)
  have hq := hN.div hRd hR
  unfold opKLocus
  convert hq using 1
  · rfl
  · simp only [Pi.sub_apply, Function.comp_apply]
    rw [hzero]
    field_simp
    ring

/-- **Correction** (Miao, p. 553): the printed slope has denominator `R²(k)`; the slope is
`(−s_wkf″ + s_Rf″ − g_n)/R(k)`, which differs from the printed value whenever the numerator is
nonzero (since `R > 1`). -/
theorem op_kLocus_slope_printed {num R : ℝ} (hnum : num ≠ 0) (hR : 1 < R) :
    num / R ≠ num / R ^ 2 := by
  intro h
  have hR0 : R ≠ 0 := by linarith
  field_simp at h
  have : num * (R - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact hnum h'
  · linarith

/-- Miao, p. 553: "Under the Diamond conditions ... `db/dk(k_D) < 0`": with `s_R ≥ 0`, `f″ < 0`
and `0 < G′(k_D) = −s_wk_Df″/(g_n − s_Rf″) < 1`, the numerator `−s_wk_Df″ + s_Rf″ − g_n` is
negative. -/
theorem op_kLocus_slope_neg {gn kD sw sR fpp : ℝ} (hgn : 0 < gn) (hsR : 0 ≤ sR) (hfpp : fpp < 0)
    (hG1 : -sw * kD * fpp / (gn - sR * fpp) < 1) : -sw * kD * fpp + sR * fpp - gn < 0 := by
  have hd : 0 < gn - sR * fpp := by nlinarith
  rw [div_lt_one hd] at hG1
  linarith

/-! ### Vector fields -/

/-- Miao, p. 554: with `s_R ≥ 0`, `k_{t+1} > k_t ⟺ b_t < b(k_t)` (the arrows of
Figure 16.11), where `g_nk_{t+1} = s(w(k_t), R(k_{t+1})) − R(k_t)b_t`. -/
theorem op_k_increase_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k k' b : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k) (hk' : 0 < k')
    (heq : gn * k' = s (opWage f fp k) (opRate fp k') - opRate fp k * b) :
    k < k' ↔ b < opKLocus s f fp gn k := by
  have hR1 : ∀ x, 0 < x → opRate fp x ∈ Set.Ioi 1 := fun x hx => by
    simp [opRate, hfp x hx]
  have hR0 : 0 < opRate fp k := lt_trans one_pos (hR1 k hk)
  unfold opKLocus
  rw [lt_div_iff₀ hR0]
  constructor
  · intro h
    have hfa := hanti (show k ∈ Set.Ioi 0 from hk) (show k' ∈ Set.Ioi 0 from hk') h
    have := hmono (hR1 _ hk') (hR1 _ hk) (by simp only [opRate]; linarith)
    nlinarith
  · intro h
    by_contra h'
    push Not at h'
    have hfa := hanti.antitoneOn (show k' ∈ Set.Ioi 0 from hk')
      (show k ∈ Set.Ioi 0 from hk) h'
    have := hmono (hR1 _ hk) (hR1 _ hk') (by simp only [opRate]; linarith)
    nlinarith

/-- With `s_R ≥ 0`, `k_{t+1} < k_t ⟺ b_t > b(k_t)`. -/
theorem op_k_decrease_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k k' b : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k) (hk' : 0 < k')
    (heq : gn * k' = s (opWage f fp k) (opRate fp k') - opRate fp k * b) :
    k' < k ↔ opKLocus s f fp gn k < b := by
  have hR1 : ∀ x, 0 < x → opRate fp x ∈ Set.Ioi 1 := fun x hx => by
    simp [opRate, hfp x hx]
  have hR0 : 0 < opRate fp k := lt_trans one_pos (hR1 k hk)
  unfold opKLocus
  rw [div_lt_iff₀ hR0]
  constructor
  · intro h
    have hfa := hanti (show k' ∈ Set.Ioi 0 from hk') (show k ∈ Set.Ioi 0 from hk) h
    have := hmono (hR1 _ hk) (hR1 _ hk') (by simp only [opRate]; linarith)
    nlinarith
  · intro h
    by_contra h'
    push Not at h'
    have hfa := hanti.antitoneOn (show k ∈ Set.Ioi 0 from hk)
      (show k' ∈ Set.Ioi 0 from hk') h'
    have := hmono (hR1 _ hk') (hR1 _ hk) (by simp only [opRate]; linarith)
    nlinarith

/-- With `s_R ≥ 0`, `k_{t+1} = k_t ⟺ b_t = b(k_t)`: the locus `Δk = 0`. -/
theorem op_k_stationary_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k k' b : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k) (hk' : 0 < k')
    (heq : gn * k' = s (opWage f fp k) (opRate fp k') - opRate fp k * b) :
    k' = k ↔ b = opKLocus s f fp gn k := by
  have h1 := op_k_increase_iff hgn hmono hanti hfp hk hk' heq
  have h2 := op_k_decrease_iff hgn hmono hanti hfp hk hk' heq
  constructor
  · intro h
    rcases lt_trichotomy b (opKLocus s f fp gn k) with hb | hb | hb
    · exact absurd (h1.2 hb) (by rw [h]; exact lt_irrefl k)
    · exact hb
    · exact absurd (h2.2 hb) (by rw [h]; exact lt_irrefl k)
  · intro h
    rcases lt_trichotomy k' k with hk2 | hk2 | hk2
    · exact absurd (h2.1 hk2) (by rw [h]; exact lt_irrefl _)
    · exact hk2
    · exact absurd (h1.1 hk2) (by rw [h]; exact lt_irrefl _)

/-- Miao, p. 554: `b_{t+1} − b_t = (R_t/g_n − 1)b_t`. -/
theorem op_b_diff {gn R b b' : ℝ} (hgn : 0 < gn) (heq : gn * b' = R * b) :
    b' - b = (R / gn - 1) * b := by
  field_simp
  linarith

/-- Miao, p. 554: `b_{t+1} > b_t ⟺ R_t/g_n − 1 > 0 ⟺ k_t < k_G` (for `b_t > 0`). -/
theorem op_b_increase_iff {fp : ℝ → ℝ} {gn k kG b b' : ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hk : 0 < k) (hkG : 0 < kG) (hG : fp kG = gn - 1)
    (hb : 0 < b) (heq : gn * b' = opRate fp k * b) :
    (b < b' ↔ 0 < opRate fp k / gn - 1) ∧ (b < b' ↔ k < kG) := by
  have hd := op_b_diff hgn heq
  have h1 : b < b' ↔ 0 < opRate fp k / gn - 1 := by
    constructor
    · intro h
      have : 0 < (opRate fp k / gn - 1) * b := by linarith
      exact pos_of_mul_pos_left this hb.le
    · intro h
      have := mul_pos h hb
      linarith
  refine ⟨h1, h1.trans ?_⟩
  rw [sub_pos, one_lt_div hgn]
  simp only [opRate]
  rw [show gn < 1 + fp k ↔ fp kG < fp k by rw [hG]; constructor <;> intro h <;> linarith]
  exact hanti.lt_iff_gt hkG hk

/-- Miao, p. 554: the locus `Δb_t = 0` (for `b_t > 0`) is the vertical line `k = k_G`. -/
theorem op_b_stationary_iff {fp : ℝ → ℝ} {gn k kG b b' : ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hk : 0 < k) (hkG : 0 < kG) (hG : fp kG = gn - 1)
    (hb : 0 < b) (heq : gn * b' = opRate fp k * b) : b' = b ↔ k = kG := by
  have hd := op_b_diff hgn heq
  constructor
  · intro h
    rw [h, sub_self] at hd
    have h0 := (mul_eq_zero.1 hd.symm).resolve_right hb.ne'
    rw [sub_eq_zero, div_eq_one_iff_eq hgn.ne'] at h0
    simp only [opRate] at h0
    exact op_golden_rule_unique hanti hk hkG (by linarith) hG
  · intro h
    rw [h] at heq
    simp only [opRate, hG] at heq
    have : gn * (b' - b) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hgn.ne'
    linarith

/-- Miao, p. 554: "for a bubbly steady state to exist, we must have `k_G < k_D` or `R_D < g_n`.
That is, the bubbleless equilibrium must be dynamically inefficient." With `s_R ≥ 0`, `G` the
Diamond law with unique positive steady state `k_D` (`G > id` below, `G < id` above), a
steady-state bubble `b > 0` at `k_G` exists iff `k_G < k_D`, iff `R(k_D) < g_n`. -/
theorem op_bubbly_exists_iff {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn kG kD : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp kG)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hkG : 0 < kG) (hkD : 0 < kD) (hGR : fp kG = gn - 1)
    (hG : 0 < G kG ∧ gn * G kG = s (opWage f fp kG) (opRate fp (G kG)))
    (hfixD : G kD = kD) (hbelow : ∀ k, 0 < k → k < kD → k < G k)
    (habove : ∀ k, kD < k → G k < k) :
    ((∃ b, 0 < b ∧ gn * (kG + b) = s (opWage f fp kG) (opRate fp kG)) ↔ kG < kD) ∧
      (kG < kD ↔ opRate fp kD < gn) := by
  have hSG := op_S_vs_G hgn hmono hanti hfp hkG hG
  have hRG : opRate fp kG = gn := by simp only [opRate, hGR]; ring
  refine ⟨⟨?_, fun h => ?_⟩, ?_⟩
  · rintro ⟨b, hb, hbe⟩
    by_contra h
    push Not at h
    have hle : G kG ≤ kG := by
      rcases h.lt_or_eq with h' | h'
      · exact (habove kG h').le
      · rw [← h', hfixD]
    rcases hle.lt_or_eq with h' | h'
    · have := hSG.2 h'
      nlinarith
    · have : s (opWage f fp kG) (opRate fp kG) = gn * kG := by
        have e := hG.2
        rw [h'] at e
        linarith
      nlinarith
  · have := hSG.1 (hbelow kG hkG h)
    refine ⟨s (opWage f fp kG) (opRate fp kG) / gn - kG, ?_, ?_⟩
    · rw [sub_pos, lt_div_iff₀ hgn]; linarith
    · field_simp; ring
  · simp only [opRate]
    rw [show 1 + fp kD < gn ↔ fp kD < fp kG by rw [hGR]; constructor <;> intro h <;> linarith]
    exact (hanti.lt_iff_gt hkD hkG).symm

end Miao.OverlappingGenerations
