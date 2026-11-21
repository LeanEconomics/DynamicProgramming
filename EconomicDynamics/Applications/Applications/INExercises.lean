/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INUnique
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Inventory: counterexamples and Exercises 8.6–8.7

Miao, §8.5, pp. 263–275, and Exercises 6–7, p. 288. The exercises refer to "the inventory
model in Section 8.4"; §8.4 is Consumption/Portfolio Choice, so this is a misprint for §8.5.

* `assumption_8_5_1_counterexample`: `L(y) = √(1 + y²)/2` is nonnegative, convex, coercive and
  differentiable (Assumptions 8.5.1–8.5.2 as printed), but with `p = 1` the function
  `G_1(y) = L(y) + py` has no minimiser, so `S_1` does not exist.
* `eq_8_27_ii_counterexample`: (8.27)(ii) "each `G_n` is differentiable" fails when the demand
  distribution has an atom: with `β = 1/2`, `c = 1`, `p = 0`, `L(y) = y²` and demand `z ≡ 0`,
  `G_2(y) = y² + (max(y, −1))²/2` is not differentiable at `s_1 = −1`.
* `Glim_decomp`: `G(y) = H(y) + βpEz + βEV(y − z)` with `H(y) = L(y) + p(1 − β)y` and
  `V(x) = f(x) + px`.
* **Exercise 8.6** (`ex_8_6`): for the infinite-horizon (s, S) policy, `G(x) = H(x) + βpEz +
  β(c + min G)` for `x ≤ s`, so `s` solves `L(s) + p(1 − β)s + βpEz = (1 − β)(c + min G)`, and
  `S` minimises `G`; for exponential demand `Ez = 1/λ`.
* **Exercise 8.7** (`ex_8_7`): with `c = 0`, `s_n = S_n`, every limit point `s` of `{s_n}` is a
  limit point of `{S_n}` and a minimiser of `G`, the (s, s) policy is optimal, and every
  minimiser `S` of `G` (so every such `s`) solves `p(1 − β) + L′(S) = 0` (`ex_8_7_H`: `S`
  minimises `H(y) = L(y) + p(1 − β)y`).

**Departures.** Exercise 8.6 asks to "characterize `s` and `S`" without a definite claim; we
prove the characterization above (the mean of the exponential law is not computed here: the
formula is stated with `Ez = ∫ z dφ`).
-/

namespace Miao.Applications

namespace INModel

open MeasureTheory Filter Topology

variable {M : INModel}

/-- **Assumption 8.5.1 is too weak** (Miao, p. 263): `L(y) = √(1 + y²)/2` is nonnegative,
convex, coercive and differentiable, but `L(y) + y` (the book's `G_1` with `p = 1`) has no
minimiser: `G_1(y − 1) < G_1(y)` for every `y`. -/
theorem assumption_8_5_1_counterexample :
    let L : ℝ → ℝ := fun y => Real.sqrt (1 + y ^ 2) / 2
    (∀ y, 0 ≤ L y) ∧ ConvexOn ℝ Set.univ L ∧ in_Coercive L ∧ Differentiable ℝ L ∧
      ¬ ∃ S, ∀ y, L S + 1 * S ≤ L y + 1 * y := by
  intro L
  have hsq : ∀ y : ℝ, Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 := fun y =>
    Real.sq_sqrt (by positivity)
  have hge : ∀ y : ℝ, |y| ≤ Real.sqrt (1 + y ^ 2) := fun y => by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  refine ⟨fun y => by positivity, ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩, ⟨?_, ?_⟩,
    fun y => ?_, ?_⟩
  · simp only [L, smul_eq_mul]
    have hu := hsq u
    have hv := hsq v
    have hsu := Real.sqrt_nonneg (1 + u ^ 2)
    have hsv := Real.sqrt_nonneg (1 + v ^ 2)
    have hcs : 1 + u * v ≤ Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + v ^ 2) := by
      have h1 : (1 + u * v) ^ 2 ≤ (Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + v ^ 2)) ^ 2 := by
        rw [mul_pow, hu, hv]; nlinarith [sq_nonneg (u - v)]
      exact abs_le_of_sq_le_sq' h1 (mul_nonneg hsu hsv) |>.2
    have key : Real.sqrt (1 + (a * u + b * v) ^ 2) ≤
        a * Real.sqrt (1 + u ^ 2) + b * Real.sqrt (1 + v ^ 2) := by
      rw [Real.sqrt_le_left (add_nonneg (mul_nonneg ha hsu) (mul_nonneg hb hsv))]
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg ha hb, mul_le_mul_of_nonneg_left hcs (mul_nonneg ha hb)]
    linarith
  · refine tendsto_atBot_atTop.2 fun c => ⟨-2 * |c|, fun y hy => ?_⟩
    have := hge y
    simp only [L]
    rw [abs_of_nonpos (by linarith [abs_nonneg c])] at this
    linarith [le_abs_self c]
  · refine tendsto_atTop_atTop.2 fun c => ⟨2 * |c|, fun y hy => ?_⟩
    have := hge y
    simp only [L]
    rw [abs_of_nonneg (by linarith [abs_nonneg c])] at this
    linarith [le_abs_self c]
  · have h1 : DifferentiableAt ℝ (fun y : ℝ => 1 + y ^ 2) y :=
      (differentiableAt_const _).add (differentiableAt_id.pow 2)
    exact (h1.sqrt (by positivity)).div_const 2
  · rintro ⟨S, hS⟩
    have h := hS (S - 1)
    simp only [L] at h
    have : Real.sqrt (1 + (S - 1) ^ 2) ≤ Real.sqrt (1 + S ^ 2) + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [hsq S, hge S, le_abs_self S, neg_abs_le S, Real.sqrt_nonneg (1 + S ^ 2)]
    linarith

/-- The model of `eq_8_27_ii_counterexample`: `β = 1/2`, `c = 1`, `p = 0`, `L(y) = y²`,
demand `0`. -/
noncomputable def cex827 : INModel where
  β := 1 / 2
  c := 1
  p := 0
  L := fun y => y ^ 2
  φ := Measure.dirac 0

theorem cex827_A : cex827.Assumption851 where
  β_pos := by norm_num [cex827]
  β_lt := by norm_num [cex827]
  c_nonneg := by norm_num [cex827]
  p_nonneg := by simp [cex827]
  prob := by unfold cex827; infer_instance
  demand_nonneg := by simp [cex827]
  demand_int := by unfold cex827; exact integrable_dirac (by simp)
  L_nonneg := fun y => by simp only [cex827]; positivity
  L_convex := by simpa [cex827] using (even_two.convexOn_pow (𝕜 := ℝ))
  L_coercive := by
    simp only [cex827]
    refine ⟨tendsto_atBot_atTop.2 fun b => ⟨-|b| - 1, fun y hy => ?_⟩,
      tendsto_atTop_atTop.2 fun b => ⟨|b| + 1, fun y hy => ?_⟩⟩
    · nlinarith [le_abs_self b, abs_nonneg b]
    · nlinarith [le_abs_self b, abs_nonneg b]
  G1_coercive := by
    simp only [cex827, zero_mul, add_zero]
    refine tendsto_atBot_atTop.2 fun b => ⟨-|b| - 1, fun y hy => ?_⟩
    nlinarith [le_abs_self b, abs_nonneg b]

/-- **(8.27)(ii) fails for distributions with atoms** (Miao, p. 270): in `cex827`
(`β = 1/2`, `c = 1`, `p = 0`, `L(y) = y²`, demand `z ≡ 0`), `S_1 = 0`, `s_1 = −1` and
`G_2(y) = y² + (max(y, −1))²/2`, which is not differentiable at `y = −1`. Assumptions
8.5.1–8.5.2 hold. -/
theorem eq_8_27_ii_counterexample :
    cex827.Assumption851 ∧ cex827.Assumption852 ∧ cex827.Sn 1 = 0 ∧ cex827.sn 1 = -1 ∧
      ¬ DifferentiableAt ℝ (cex827.G 2) (-1) := by
  have hA := cex827_A
  have hB : cex827.Assumption852 := by
    unfold Assumption852 cex827; exact (differentiable_id).pow 2
  have hG1 : ∀ y, cex827.G 1 y = y ^ 2 := fun y => by rw [G_one]; simp [cex827]
  have hS : cex827.Sn 1 = 0 := by
    have h1 := (Sn_isLeast hA 1).1 0
    rw [hG1, hG1] at h1
    nlinarith [sq_nonneg (cex827.Sn 1)]
  have hs : cex827.sn 1 = -1 := by
    have h := sn_isLeast hA 1
    have hc : cex827.c = 1 := rfl
    rw [hS, hc] at h
    have h' : IsLeast {x | cex827.G 1 x ≤ 1 + cex827.G 1 0} (-1) := by
      refine ⟨?_, fun x hx => ?_⟩
      · simp only [Set.mem_ofPred_eq, hG1]; norm_num
      · simp only [Set.mem_ofPred_eq, hG1] at hx
        nlinarith
    exact h.unique h'
  have hf1 : ∀ x, cex827.fn 1 x = (max x (-1)) ^ 2 := fun x => by
    rw [fn_eq hA 0 x, hs, hG1]; simp [cex827]
  have hG2 : ∀ y, cex827.G 2 y = y ^ 2 + 1 / 2 * (max y (-1)) ^ 2 := fun y => by
    rw [G_succ]
    change y ^ 2 + 0 * y + 1 / 2 * ∫ z, cex827.fn 1 (y - z) ∂(Measure.dirac 0) = _
    rw [integral_dirac, sub_zero, hf1]
    ring
  refine ⟨hA, hB, hS, hs, fun hd => ?_⟩
  have hL : HasDerivWithinAt (cex827.G 2) (-2) (Set.Iic (-1)) (-1) := by
    have h : HasDerivAt (fun y : ℝ => y ^ 2 + 1 / 2) (-2) (-1) := by
      simpa using ((hasDerivAt_pow 2 (-1 : ℝ)).add_const (1 / 2))
    refine h.hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · rw [hG2, max_eq_right (Set.mem_Iic.1 hy)]; norm_num
    · rw [hG2]; norm_num
  have hR : HasDerivWithinAt (cex827.G 2) (-3) (Set.Ici (-1)) (-1) := by
    have h : HasDerivAt (fun y : ℝ => 3 / 2 * y ^ 2) (-3) (-1) := by
      convert ((hasDerivAt_pow 2 (-1 : ℝ)).const_mul (3 / 2)) using 1
      norm_num
    refine h.hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · rw [hG2, max_eq_left (Set.mem_Ici.1 hy)]; ring
    · rw [hG2]; norm_num
  have e1 := (uniqueDiffWithinAt_Iic (-1 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hL
  have e2 := (uniqueDiffWithinAt_Ici (-1 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hR
  linarith

/-- `V(x) = f(x) + px` has integrable translates. -/
theorem int_V (hA : M.Assumption851) (y : ℝ) :
    Integrable (fun z => M.f (y - z) + M.p * (y - z)) M.φ := by
  have := hA.prob
  have h : Integrable (fun z => M.p * y - M.p * z) M.φ :=
    (integrable_const _).sub (hA.demand_int.const_mul M.p)
  refine ((int_f hA y).add h).congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  ring

/-- `G(y) = H(y) + βpEz + βEV(y − z)`, `H(y) = L(y) + p(1 − β)y`, `V(x) = f(x) + px`. -/
theorem Glim_decomp (hA : M.Assumption851) (y : ℝ) :
    M.Glim y = M.L y + M.p * (1 - M.β) * y + M.β * M.p * (∫ z, z ∂M.φ) +
      M.β * ∫ z, (M.f (y - z) + M.p * (y - z)) ∂M.φ := by
  have := hA.prob
  have h : Integrable (fun z => M.p * (y - z)) M.φ :=
    ((integrable_const y).sub hA.demand_int).const_mul M.p
  rw [integral_add (int_f hA y) h, integral_const_mul, integral_sub (integrable_const y)
    hA.demand_int]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold Glim Gf
  ring

/-- **Exercise 8.7**, key step (Miao, p. 288): with no fixed cost, every minimiser `S` of `G`
minimises `H(y) = L(y) + p(1 − β)y`. -/
theorem ex_8_7_H (hA : M.Assumption851) (hc : M.c = 0) {S : ℝ}
    (hS : ∀ y, M.Glim S ≤ M.Glim y) (y : ℝ) :
    M.L S + M.p * (1 - M.β) * S ≤ M.L y + M.p * (1 - M.β) * y := by
  have := hA.prob
  set m := M.Glim S
  set H : ℝ → ℝ := fun y => M.L y + M.p * (1 - M.β) * y
  set Ez := ∫ z, z ∂M.φ
  have hfix : ∀ x y, in_fix M.c x y = 0 := fun x y => by simp [in_fix, hc]
  -- facts about `V(w) = f(w) + pw`
  have V1 : ∀ w, m ≤ M.f w + M.p * w := by
    intro w
    have : Nonempty (Set.Ici w) := ⟨⟨w, Set.mem_Ici.2 le_rfl⟩⟩
    rw [proposition_8_5_2 hA w]
    have : m - M.p * w ≤ M.T M.f w := le_ciInf fun y => by
      rw [TT_eq, hfix]; change _ ≤ 0 + M.Glim y - _; linarith [hS y]
    linarith
  have V2 : ∀ w, w ≤ S → M.f w + M.p * w ≤ m := by
    intro w hw
    have := f_le_TT hA hw
    rw [TT_eq, hfix] at this
    change M.f w ≤ 0 + M.Glim S - M.p * w at this
    linarith
  have V3 : ∀ w, M.f w + M.p * w ≤ M.Glim w := by
    intro w
    have := f_le_TT hA (le_refl w)
    rw [TT_eq, hfix] at this
    change M.f w ≤ 0 + M.Glim w - M.p * w at this
    linarith
  have hdec := Glim_decomp hA
  have hGS : M.Glim S = H S + M.β * M.p * Ez + M.β * m := by
    rw [hdec S]
    have : ∫ z, (M.f (S - z) + M.p * (S - z)) ∂M.φ = m := by
      have h : (fun z => M.f (S - z) + M.p * (S - z)) =ᵐ[M.φ] fun _ => m := by
        filter_upwards [hA.demand_nonneg] with z hz
        exact le_antisymm (V2 _ (by linarith)) (V1 _)
      rw [integral_congr_ae h]; simp
    rw [this]
  rcases le_or_gt y S with hy | hy
  · have : ∫ z, (M.f (y - z) + M.p * (y - z)) ∂M.φ = m := by
      have h : (fun z => M.f (y - z) + M.p * (y - z)) =ᵐ[M.φ] fun _ => m := by
        filter_upwards [hA.demand_nonneg] with z hz
        exact le_antisymm (V2 _ (by linarith)) (V1 _)
      rw [integral_congr_ae h]; simp
    have h1 := hS y
    rw [hdec y, this] at h1
    change M.Glim S ≤ H y + M.β * M.p * Ez + M.β * m at h1
    rw [hGS] at h1
    linarith
  by_contra hcon
  push Not at hcon
  have hHcv : ConvexOn ℝ Set.univ H :=
    hA.L_convex.add ((convexOn_id convex_univ).smul
      (mul_nonneg hA.p_nonneg (sub_nonneg.2 hA.β_lt.le)))
  have hHle : ∀ w, S ≤ w → w ≤ y → H w ≤ H S := by
    intro w hSw hwy
    rcases eq_or_lt_of_le hSw with h | h
    · rw [h]
    have key := hHcv.secant_mono (Set.mem_univ S) (Set.mem_univ w) (Set.mem_univ y)
      (ne_of_gt h) (ne_of_gt hy) hwy
    have hneg : (H y - H S) / (y - S) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    have := key.trans_lt hneg
    rw [div_neg_iff] at this
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  obtain ⟨w₀, hw₀, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc S y)).exists_isMaxOn
    (Set.nonempty_Icc.2 hy.le) (Glim_cont hA).continuousOn
  set Δ := M.Glim w₀ - m
  have hbound : ∀ w, S ≤ w → w ≤ y → M.Glim w - m ≤ H w - H S + M.β * Δ := by
    intro w hSw hwy
    have hI : ∫ z, (M.f (w - z) + M.p * (w - z)) ∂M.φ ≤ m + Δ := by
      have := integral_mono_ae (int_V hA w) (integrable_const (m + Δ)) (by
        filter_upwards [hA.demand_nonneg] with z hz
        rcases le_or_gt (w - z) S with h | h
        · have := V2 _ h
          have h0 : M.Glim S ≤ M.Glim w₀ := hmax (Set.left_mem_Icc.2 hy.le)
          have : 0 ≤ Δ := by simp only [Δ, m]; linarith
          linarith
        · have := V3 (w - z)
          have h0 : M.Glim (w - z) ≤ M.Glim w₀ :=
            hmax (show w - z ∈ Set.Icc S y from ⟨h.le, by linarith⟩)
          simp only [Δ]
          linarith)
      simpa using this
    rw [hdec w]
    change H w + M.β * M.p * Ez + M.β * _ - m ≤ _
    have := mul_le_mul_of_nonneg_left hI hA.β_pos.le
    have hm : m = H S + M.β * M.p * Ez + M.β * m := hGS
    nlinarith
  have hΔ : Δ ≤ 0 := by
    have h := hbound w₀ hw₀.1 hw₀.2
    have := hHle w₀ hw₀.1 hw₀.2
    have hβ := hA.β_lt
    nlinarith
  have := hbound y hy.le le_rfl
  have := hS y
  nlinarith [hA.β_pos]

/-- **Exercise 8.7** (Miao, p. 288). Suppose there is no fixed cost, `c = 0`. Then `s_n = S_n`
for every `n`; every minimiser `S` of `G` satisfies `p(1 − β) + L′(S) = 0` (Assumption
8.5.2); and every limit point `s` of `{s_n}` is a limit point of `{S_n}` and a minimiser of
`G`, so `s = S` and the (s, s) policy (order up to `s` whenever `x ≤ s`) is optimal. -/
theorem ex_8_7 (hA : M.Assumption851) (hB : M.Assumption852) (hc : M.c = 0) :
    (∀ n, M.sn n = M.Sn n) ∧
    (∀ S, (∀ y, M.Glim S ≤ M.Glim y) → M.p * (1 - M.β) + deriv M.L S = 0) ∧
    ∀ s, in_IsLimitPoint M.sn s → in_IsLimitPoint M.Sn s ∧ (∀ y, M.Glim s ≤ M.Glim y) ∧
      M.p * (1 - M.β) + deriv M.L s = 0 ∧
      ∀ x, M.f x = M.TT M.f (in_ssPolicy s s x) x ∧
        ∀ y, x ≤ y → M.TT M.f (in_ssPolicy s s x) x ≤ M.TT M.f y x := by
  have hsS : ∀ n, M.sn n = M.Sn n := fun n => by
    unfold sn Sn; rw [hc]; exact in_sbar_eq_of_zero (G_cont hA n) (G_coercive hA n)
  have hFOC : ∀ S, (∀ y, M.Glim S ≤ M.Glim y) → M.p * (1 - M.β) + deriv M.L S = 0 := by
    intro S hS
    have hmin : IsLocalMin (fun y => M.L y + M.p * (1 - M.β) * y) S :=
      (show IsMinOn (fun y => M.L y + M.p * (1 - M.β) * y) Set.univ S from
        fun y _ => ex_8_7_H hA hc hS y).isLocalMin Filter.univ_mem
    have hd : HasDerivAt (fun y => M.L y + M.p * (1 - M.β) * y)
        (deriv M.L S + M.p * (1 - M.β)) S := by
      have := (hB S).hasDerivAt.add ((hasDerivAt_id' S).const_mul (M.p * (1 - M.β)))
      rwa [mul_one] at this
    have := hmin.hasDerivAt_eq_zero hd
    linarith
  refine ⟨hsS, hFOC, fun s hs => ?_⟩
  have hsS' : M.sn = M.Sn := funext hsS
  have hlim : in_IsLimitPoint M.Sn s := hsS' ▸ hs
  have hmin := (proposition_8_5_3 hA).2.2.1 s hlim
  exact ⟨hlim, hmin, hFOC s hmin, ex_8_4_policy hA hs hmin le_rfl⟩

/-- **Exercise 8.6** (Miao, p. 288), the characterization of `s` and `S` (for any demand
distribution, in particular the exponential one, whose mean `Ez` is `1/λ`): for a limit point
`s` of `{s_n}` and a minimiser `S ≥ s` of `G` (the infinite-horizon (s, S) policy),
`G(x) = L(x) + p(1 − β)x + βpEz + β(c + G(S))` for all `x ≤ s`; hence `s` solves
`L(s) + p(1 − β)s + βpEz = (1 − β)(c + G(S))`, and `S` minimises `G`. -/
theorem ex_8_6 (hA : M.Assumption851) {s S : ℝ} (hs : in_IsLimitPoint M.sn s)
    (hS : ∀ y, M.Glim S ≤ M.Glim y) (hsS : s ≤ S) :
    (∀ x, x ≤ s → M.Glim x = M.L x + M.p * (1 - M.β) * x + M.β * M.p * (∫ z, z ∂M.φ) +
      M.β * (M.c + M.Glim S)) ∧
    M.L s + M.p * (1 - M.β) * s + M.β * M.p * (∫ z, z ∂M.φ) = (1 - M.β) * (M.c + M.Glim S) := by
  have := hA.prob
  have hGs := (proposition_8_5_3 hA).2.2.2.2.2 s S hs hS
  have hV : ∀ w, w ≤ s → M.f w + M.p * w = M.c + M.Glim S := by
    intro w hw
    have h := (ex_8_4_policy hA hs hS hsS w).1
    rw [TT_eq] at h
    change M.f w = in_fix M.c w (in_ssPolicy s S w) + M.Glim (in_ssPolicy s S w) - M.p * w at h
    unfold in_ssPolicy at h
    simp only [hw, ↓reduceIte] at h
    rcases eq_or_lt_of_le (hw.trans hsS) with h' | h'
    · rw [h', in_fix_self] at h
      have hss : s = S := le_antisymm hsS (h' ▸ hw)
      rw [hss] at hGs
      have : M.c = 0 := by linarith
      rw [this, h']; linarith
    · rw [in_fix_of_lt _ h'] at h; linarith
  have hx : ∀ x, x ≤ s → M.Glim x = M.L x + M.p * (1 - M.β) * x + M.β * M.p * (∫ z, z ∂M.φ) +
      M.β * (M.c + M.Glim S) := by
    intro x hxs
    rw [Glim_decomp hA x]
    have : ∫ z, (M.f (x - z) + M.p * (x - z)) ∂M.φ = M.c + M.Glim S := by
      have h : (fun z => M.f (x - z) + M.p * (x - z)) =ᵐ[M.φ] fun _ => M.c + M.Glim S := by
        filter_upwards [hA.demand_nonneg] with z hz
        exact hV _ (by linarith)
      rw [integral_congr_ae h]; simp
    rw [this]
  refine ⟨hx, ?_⟩
  have := hx s le_rfl
  rw [hGs] at this
  linarith

end INModel

end Miao.Applications
