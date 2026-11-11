/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.WNDuran
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Example 7.3.2, Exercise 7.3 and the log AK model

Miao §7.3.2, pp. 216–217, and Exercise 7.3, p. 228. Technology `F(x) = Ax + x^α`, `A > 1`,
`α ∈ (0, 1)`, `Γ(x) = [0, F(x)]` on `X = ℝ₊` (`wn_Rp`, `wn_Γ`), `u(x, y) = (F(x) − y)^γ`
(`wn_u`), weights `ϕ_M(x) = M + F(x)^γ` (`wn_phi`; the book's weight is `M = 1`).

* `example_7_3_2_first_step`: the first step of the printed chain is right (the sup over
  `y ∈ [0, F(x)]` of `ϕ(y)/ϕ(x)` is `r(F(x))`, `r(z) = (1 + F(z)^γ)/(1 + z^γ)`), and
  `example_7_3_2_limit`: `r(z) → A^γ` as `z → ∞` (the last equality is right).
* The middle step `r(z) ≤ lim r = A^γ` is FALSE: `example_7_3_2_counterexample`
  (`A = (21/20)²`, `α = γ = 1/2`: some `x, y` have `ϕ(y)/ϕ(x) = 49/40 > 21/20 = A^γ`),
  `example_7_3_2_7_27_fails` (with `β = 40/49`, `βA^γ = 6/7 < 1` but no `θ < 1` satisfies
  (7.27)), and `example_7_3_2_fails`: whenever `γ + α > 1`, `ϕ(y)/ϕ(x) > A^γ` for some `x, y`.
* The corrected bound `wn_ratio_le`: `(M + F(z)^γ)/(M + z^γ) ≤ A^γ + M^{α−1}` for `M > 0`, giving
  (7.27) for `ϕ_M` with `θ = β(A^γ + M^{α−1})` (`example_7_3_2`, which also has (7.28):
  `T0 = F^γ < ϕ_M`). The book's own weight (`M = 1`) works when `β(A^γ + 1) < 1`; under the
  book's assumption `βA^γ < 1` a large `M` works (`wn_exists_M`).
* `ex_7_3`: if `βA^γ < 1`, the Bellman equation has exactly one solution in the book's space
  `C_ϕ(ℝ₊)`, `ϕ = 1 + F^γ` (all `C_{ϕ_M}` are the same space).
* `wn_log_ak_7_27_fails`, `wn_log_ak_7_27_never`: for `u = ln(Ax − y)` and
  `ϕ(x) = 1 + |ln(Ax)|`, at every state `x > 0` and for every `β > 0` the sup in (7.27) over
  `y ∈ (0, Ax]` is `+∞`, so (7.27) fails for every `θ`.
-/

namespace Miao.InfiniteHorizonDP

open Filter Topology

/-- The state space `X = ℝ₊` of Example 7.3.2. -/
abbrev wn_Rp : Type := Set.Ici (0 : ℝ)

/-- Miao, p. 216: the production function `F(x) = Ax + x^α`. -/
noncomputable def wn_F (A α x : ℝ) : ℝ := A * x + x ^ α

/-- Miao, p. 216: the weight `ϕ_M(x) = M + F(x)^γ` (the book's weight is `M = 1`). -/
noncomputable def wn_phi (M A α γ x : ℝ) : ℝ := M + wn_F A α x ^ γ

/-- Miao, p. 216 (and Exercise 7.3): `Γ(x) = [0, F(x)]` on `ℝ₊`. -/
def wn_Γ (A α : ℝ) (x : wn_Rp) : Set wn_Rp := {y | (y : ℝ) ≤ wn_F A α x}

/-- Miao, p. 216: `u(x, y) = (F(x) − y)^γ`. -/
noncomputable def wn_u (A α γ : ℝ) (p : wn_Rp × wn_Rp) : ℝ := (wn_F A α p.1 - p.2) ^ γ

variable {A α γ : ℝ}

theorem wn_F_nonneg (hA : 0 ≤ A) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ wn_F A α x :=
  add_nonneg (mul_nonneg hA hx) (Real.rpow_nonneg hx α)

theorem wn_F_mono (hA : 0 ≤ A) (hα : 0 ≤ α) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    wn_F A α x ≤ wn_F A α y :=
  add_le_add (mul_le_mul_of_nonneg_left hxy hA) (Real.rpow_le_rpow hx hxy hα)

theorem wn_F_continuous (hα : 0 ≤ α) : Continuous (wn_F A α) :=
  (continuous_const.mul continuous_id).add (Real.continuous_rpow_const hα)

theorem wn_rpow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (a + b) ^ γ ≤ a ^ γ + b ^ γ := by
  have h := NNReal.coe_le_coe.2 (NNReal.rpow_add_le_add_rpow ⟨a, ha⟩ ⟨b, hb⟩ hγ0 hγ1)
  simp only [NNReal.coe_rpow, NNReal.coe_add] at h
  exact h

/-- `w^α ≤ M^α + M^{α−1}w` for `M > 0`, `w ≥ 0`, `α ∈ [0, 1]`. -/
theorem wn_rpow_le_young {M w : ℝ} (hM : 0 < M) (hw : 0 ≤ w) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    w ^ α ≤ M ^ α + M ^ (α - 1) * w := by
  have h0 : 0 ≤ M ^ (α - 1) * w := mul_nonneg (Real.rpow_nonneg hM.le _) hw
  rcases le_or_gt w M with h | h
  · have := Real.rpow_le_rpow hw h hα0
    linarith
  · have hwpos : 0 < w := hM.trans h
    have h1 : w ^ α = w ^ (α - 1) * w := by
      rw [Real.rpow_sub_one hwpos.ne', div_mul_cancel₀ _ hwpos.ne']
    have h2 : w ^ (α - 1) ≤ M ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hM h.le (by linarith)
    have h3 := mul_le_mul_of_nonneg_right h2 hw
    have h4 := Real.rpow_nonneg hM.le α
    linarith

/-- Corrected middle step of Example 7.3.2 (Miao, p. 216): for `M > 0` and `z ≥ 0`,
`(M + F(z)^γ)/(M + z^γ) ≤ A^γ + M^{α−1}`. -/
theorem wn_ratio_le {M : ℝ} (hA : 1 ≤ A) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hM : 0 < M) {z : ℝ} (hz : 0 ≤ z) :
    (M + wn_F A α z ^ γ) / (M + z ^ γ) ≤ A ^ γ + M ^ (α - 1) := by
  have hw : 0 ≤ z ^ γ := Real.rpow_nonneg hz γ
  have hsub : wn_F A α z ^ γ ≤ (A * z) ^ γ + (z ^ α) ^ γ :=
    wn_rpow_add_le (mul_nonneg (by linarith) hz) (Real.rpow_nonneg hz α) hγ0 hγ1
  rw [Real.mul_rpow (by linarith) hz] at hsub
  have hzz : (z ^ α) ^ γ = (z ^ γ) ^ α := by
    rw [← Real.rpow_mul hz, ← Real.rpow_mul hz, mul_comm]
  have hy := wn_rpow_le_young hM hw hα0 hα1
  have hAγ : 1 ≤ A ^ γ := Real.one_le_rpow hA hγ0
  have hMα : M ^ (α - 1) * M = M ^ α := by
    rw [Real.rpow_sub_one hM.ne', div_mul_cancel₀ _ hM.ne']
  have hAM : M ≤ A ^ γ * M := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Example 7.3.2** (Miao, p. 216), first step of the printed chain: for `x ≥ 0` and
`y ∈ [0, F(x)]`, `ϕ_M(y)/ϕ_M(x) ≤ (M + F(z)^γ)/(M + z^γ)` with `z = F(x)`, with equality at
`y = F(x)`. -/
theorem example_7_3_2_first_step {M : ℝ} (hA : 0 ≤ A) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hM : 0 < M)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ wn_F A α x) :
    wn_phi M A α γ y / wn_phi M A α γ x ≤
        (M + wn_F A α (wn_F A α x) ^ γ) / (M + wn_F A α x ^ γ) ∧
      wn_phi M A α γ (wn_F A α x) / wn_phi M A α γ x =
        (M + wn_F A α (wn_F A α x) ^ γ) / (M + wn_F A α x ^ γ) := by
  refine ⟨div_le_div_of_nonneg_right ?_ (by
    have := Real.rpow_nonneg (wn_F_nonneg (α := α) hA hx) γ
    unfold wn_phi; linarith), rfl⟩
  unfold wn_phi
  have := Real.rpow_le_rpow (wn_F_nonneg (α := α) hA hy) (wn_F_mono hA hα hy hyx) hγ
  linarith

/-- **Example 7.3.2** (Miao, p. 216), last step of the printed chain:
`lim_{z → ∞} (1 + F(z)^γ)/(1 + z^γ) = A^γ`. -/
theorem example_7_3_2_limit (hA : 0 < A) (hα1 : α < 1) (hγ : 0 < γ) :
    Tendsto (fun z => (1 + wn_F A α z ^ γ) / (1 + z ^ γ)) atTop (𝓝 (A ^ γ)) := by
  have h1 : Tendsto (fun z : ℝ => z ^ (-γ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hγ
  have h2 : Tendsto (fun z : ℝ => z ^ (α - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)
    simpa only [neg_sub] using this
  have h3 : Tendsto (fun z : ℝ => (A + z ^ (α - 1)) ^ γ) atTop (𝓝 (A ^ γ)) := by
    have hc : ContinuousAt (fun t : ℝ => (A + t) ^ γ) 0 :=
      ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr hγ.le).continuousAt
    have := hc.tendsto.comp h2
    simpa only [Function.comp_def, add_zero] using this
  have h4 := (h1.add h3).div (h1.add (tendsto_const_nhds (x := (1 : ℝ)))) (by norm_num)
  rw [zero_add, zero_add, div_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  have hF : wn_F A α z = z * (A + z ^ (α - 1)) := by
    rw [wn_F, mul_add, Real.rpow_sub_one hz.ne', mul_div_cancel₀ _ hz.ne', mul_comm]
  have hpos : 0 ≤ A + z ^ (α - 1) := by positivity
  simp only [Pi.div_apply]
  rw [hF, Real.mul_rpow hz.le hpos, Real.rpow_neg hz.le]
  have hw : 0 < z ^ γ := Real.rpow_pos_of_pos hz γ
  field_simp

/-- **Example 7.3.2, counterexample** (Miao, p. 216). The middle step
`r(z) ≤ lim_{z→∞} r(z) = A^γ` of the printed chain is false: with `A = (21/20)² = 441/400`,
`α = γ = 1/2` (so `A^γ = 21/20`), some `x ≥ 0` has `F(x) = 1`, and for `y = 1 ∈ [0, F(x)]`,
`ϕ(y)/ϕ(x) = (1 + √(841/400))/2 = 49/40 > 21/20`. -/
theorem example_7_3_2_counterexample :
    (441 / 400 : ℝ) ^ (1 / 2 : ℝ) = 21 / 20 ∧ (21 / 20 : ℝ) < 49 / 40 ∧
      ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ y ≤ wn_F (441 / 400) (1 / 2) x ∧
        wn_phi 1 (441 / 400) (1 / 2) (1 / 2) y / wn_phi 1 (441 / 400) (1 / 2) (1 / 2) x =
          49 / 40 := by
  have hs : ∀ q : ℝ, 0 ≤ q → (q ^ 2) ^ (1 / 2 : ℝ) = q := fun q hq => by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hq]
  have hA : (441 / 400 : ℝ) ^ (1 / 2 : ℝ) = 21 / 20 := by
    rw [(by norm_num : (441 / 400 : ℝ) = (21 / 20) ^ 2), hs _ (by norm_num)]
  refine ⟨hA, by norm_num, ?_⟩
  have hF0 : wn_F (441 / 400) (1 / 2) 0 = 0 := by
    rw [wn_F, Real.zero_rpow (by norm_num)]; ring
  have hF1 : wn_F (441 / 400) (1 / 2) 1 = (29 / 20) ^ 2 := by
    rw [wn_F, Real.one_rpow]; norm_num
  obtain ⟨x, hx, hFx⟩ : (1 : ℝ) ∈ wn_F (441 / 400) (1 / 2) '' Set.Icc 0 1 :=
    intermediate_value_Icc zero_le_one (wn_F_continuous (by norm_num)).continuousOn
      ⟨by rw [hF0]; norm_num, by rw [hF1]; norm_num⟩
  refine ⟨x, 1, hx.1, zero_le_one, hFx.ge, ?_⟩
  rw [wn_phi, wn_phi, hF1, hFx, hs _ (by norm_num), Real.one_rpow]
  norm_num

/-- **Example 7.3.2, counterexample** (Miao, p. 216): with the parameters of
`example_7_3_2_counterexample` and `β = 40/49`, the book's assumption `βA^γ < 1` holds
(`βA^γ = 6/7`), yet no `θ < 1` satisfies (7.27) for the book's weight `ϕ = 1 + F^γ`. -/
theorem example_7_3_2_7_27_fails :
    (40 / 49 : ℝ) * (441 / 400) ^ (1 / 2 : ℝ) < 1 ∧
      ¬ ∃ θ < 1, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y ≤ wn_F (441 / 400) (1 / 2) x →
        (40 / 49 : ℝ) * (wn_phi 1 (441 / 400) (1 / 2) (1 / 2) y /
          wn_phi 1 (441 / 400) (1 / 2) (1 / 2) x) ≤ θ := by
  obtain ⟨hA, -, x, y, hx, hy, hyx, hr⟩ := example_7_3_2_counterexample
  refine ⟨by rw [hA]; norm_num, fun ⟨θ, hθ, h⟩ => ?_⟩
  have := h x y hx hy hyx
  rw [hr] at this
  norm_num at this
  linarith

/-- **Example 7.3.2, counterexample** (Miao, p. 216): whenever `γ + α > 1` (with `A > 1`,
`α ∈ (0, 1)`, `γ ∈ (0, 1]`) the printed bound `sup_{y ∈ [0, F(x)]} ϕ(y)/ϕ(x) ≤ A^γ` fails
for the book's weight: `F(z)^γ − (Az)^γ ≥ γ(A + 1)^{γ−1}z^{γ+α−1} → ∞`. -/
theorem example_7_3_2_fails (hA : 1 < A) (hα0 : 0 < α) (hα1 : α < 1) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hsum : 1 < γ + α) :
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ y ≤ wn_F A α x ∧
      A ^ γ < wn_phi 1 A α γ y / wn_phi 1 A α γ x := by
  set p := γ + α - 1
  have hp : 0 < p := by simp only [p]; linarith
  set K := γ * (A + 1) ^ (γ - 1)
  have hK : 0 < K := mul_pos hγ0 (Real.rpow_pos_of_pos (by linarith) _)
  have ht : Tendsto (fun z : ℝ => K * z ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).const_mul_atTop hK
  obtain ⟨z, hzK, hz1⟩ := ((ht.eventually (eventually_gt_atTop (A ^ γ - 1))).and
    (eventually_ge_atTop 1)).exists
  have hz0 : 0 < z := by linarith
  -- `a = Az`, `b = z^α`, `c = F(z) = a + b`
  set a := A * z
  set b := z ^ α
  set c := wn_F A α z
  have ha : 0 < a := mul_pos (by linarith) hz0
  have hb : 0 < b := Real.rpow_pos_of_pos hz0 α
  have hc : c = a + b := rfl
  have hcpos : 0 < c := by linarith
  -- Bernoulli: `a^γ ≤ c^γ − γ b c^{γ−1}`
  have hbern : (a / c) ^ γ ≤ 1 + γ * (-(b / c)) := by
    have h := rpow_one_add_le_one_add_mul_self (s := -(b / c))
      (by rw [neg_le_neg_iff, div_le_one hcpos]; linarith) hγ0.le hγ1
    have he : 1 + -(b / c) = a / c := by field_simp; linarith
    rwa [he] at h
  have hac : a ^ γ = c ^ γ * (a / c) ^ γ := by
    rw [← Real.mul_rpow hcpos.le (div_nonneg ha.le hcpos.le), mul_div_cancel₀ _ hcpos.ne']
  have hcγ : c ^ γ = c ^ (γ - 1) * c := by
    rw [Real.rpow_sub_one hcpos.ne', div_mul_cancel₀ _ hcpos.ne']
  have hgap : γ * b * c ^ (γ - 1) ≤ c ^ γ - a ^ γ := by
    have hcγpos : 0 < c ^ γ := Real.rpow_pos_of_pos hcpos γ
    have h1 := mul_le_mul_of_nonneg_left hbern hcγpos.le
    have h2 : c ^ γ * (γ * (b / c)) = γ * b * c ^ (γ - 1) := by
      rw [hcγ]; field_simp
    nlinarith
  -- `c ≤ (A + 1)z`, so `c^{γ−1} ≥ ((A + 1)z)^{γ−1}`
  have hbz : b ≤ z := by
    have h := Real.rpow_le_rpow_of_exponent_le hz1 hα1.le
    rwa [Real.rpow_one] at h
  have hcz : c ≤ (A + 1) * z := by rw [hc]; simp only [a]; nlinarith
  have hcpow : ((A + 1) * z) ^ (γ - 1) ≤ c ^ (γ - 1) :=
    Real.rpow_le_rpow_of_nonpos hcpos hcz (by linarith)
  have hKz : K * z ^ p = γ * b * ((A + 1) * z) ^ (γ - 1) := by
    simp only [K, b, p]
    rw [Real.mul_rpow (by linarith) hz0.le]
    have : z ^ (γ + α - 1) = z ^ α * z ^ (γ - 1) := by
      rw [← Real.rpow_add hz0]; ring_nf
    rw [this]; ring
  have hlow : K * z ^ p ≤ c ^ γ - a ^ γ := by
    rw [hKz]
    refine le_trans ?_ hgap
    exact mul_le_mul_of_nonneg_left hcpow (mul_nonneg hγ0.le hb.le)
  -- `x` with `F(x) = z`
  have hF0 : wn_F A α 0 = 0 := by rw [wn_F, Real.zero_rpow hα0.ne']; ring
  have hFz : z ≤ wn_F A α z := by
    simp only [wn_F]; nlinarith [Real.rpow_pos_of_pos hz0 α]
  obtain ⟨x, hx, hFx⟩ : z ∈ wn_F A α '' Set.Icc 0 z :=
    intermediate_value_Icc hz0.le (wn_F_continuous hα0.le).continuousOn
      ⟨by rw [hF0]; exact hz0.le, hFz⟩
  refine ⟨x, z, hx.1, hz0.le, hFx.ge, ?_⟩
  have hzγ : 0 < z ^ γ := Real.rpow_pos_of_pos hz0 γ
  have haγ : a ^ γ = A ^ γ * z ^ γ := Real.mul_rpow (by linarith) hz0.le
  rw [wn_phi, wn_phi, hFx, lt_div_iff₀ (by linarith)]
  nlinarith

/-- `Γ(x) = [0, F(x)]` is compact-valued. -/
theorem wn_Γ_compact (x : wn_Rp) : IsCompact (wn_Γ A α x) := by
  rw [Subtype.isCompact_iff]
  have h : ((↑) : wn_Rp → ℝ) '' wn_Γ A α x = Set.Icc 0 (wn_F A α x) := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · intro hr
      exact ⟨⟨r, hr.1⟩, hr.2, rfl⟩
  rw [h]
  exact isCompact_Icc

/-- `Γ(x) = [0, F(x)]` is lower hemicontinuous. -/
theorem wn_Γ_lhc (hA : 0 ≤ A) (hα : 0 ≤ α) (x : wn_Rp) : IsLHC (wn_Γ A α) x := by
  refine ⟨⟨⟨0, Set.self_mem_Ici⟩, wn_F_nonneg hA x.2⟩, fun y hy xs hxs => ?_⟩
  refine ⟨0, fun n => ⟨min (wn_F A α (xs n)) y, le_min (wn_F_nonneg hA (xs n).2) y.2⟩,
    fun n _ => by exact min_le_left (wn_F A α (xs n)) (y : ℝ), ?_⟩
  rw [tendsto_subtype_rng]
  have hF : Tendsto (fun n => wn_F A α (xs n)) atTop (𝓝 (wn_F A α x)) :=
    ((wn_F_continuous hα).tendsto _).comp ((continuous_subtype_val.tendsto x).comp hxs)
  have h := hF.min (tendsto_const_nhds (x := (y : ℝ)))
  rwa [min_eq_right hy] at h

/-- `Γ(x) = [0, F(x)]` is upper hemicontinuous. -/
theorem wn_Γ_uhc (hA : 0 ≤ A) (hα : 0 ≤ α) (x : wn_Rp) : IsUHC (wn_Γ A α) x := by
  refine ⟨⟨⟨0, Set.self_mem_Ici⟩, wn_F_nonneg hA x.2⟩, fun xs hxs ys hys => ?_⟩
  have hF : Tendsto (fun n => wn_F A α (xs n)) atTop (𝓝 (wn_F A α x)) :=
    ((wn_F_continuous hα).tendsto _).comp ((continuous_subtype_val.tendsto x).comp hxs)
  obtain ⟨B, hB⟩ := hF.bddAbove_range
  have hmem : ∀ n, (ys n : ℝ) ∈ Set.Icc 0 B := fun n =>
    ⟨(ys n).2, (hys n).trans (hB ⟨n, rfl⟩)⟩
  obtain ⟨y, hy, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨⟨y, hy.1⟩, ?_, φ, hφ, ?_⟩
  · exact le_of_tendsto_of_tendsto hlim (hF.comp hφ.tendsto_atTop)
      (Eventually.of_forall fun n => hys (φ n))
  · rw [tendsto_subtype_rng]
    exact hlim

theorem wn_u_continuous (hα : 0 ≤ α) (hγ : 0 ≤ γ) : Continuous (wn_u A α γ) :=
  (((wn_F_continuous hα).comp (continuous_subtype_val.comp continuous_fst)).sub
    (continuous_subtype_val.comp continuous_snd)).rpow_const fun _ => Or.inr hγ

/-- **Example 7.3.2** (Miao, p. 216), condition (7.28): `T0(x) = sup_{y ∈ [0, F(x)]} (F(x) − y)^γ
= F(x)^γ < ϕ_M(x)` for `M > 0`. -/
theorem example_7_3_2_T0 {M β : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (hM : 0 < M) (x : wn_Rp) :
    wn_duranT (wn_u A α γ) (wn_Γ A α) β 0 x = wn_F A α x ^ γ ∧
      wn_F A α x ^ γ < wn_phi M A α γ x := by
  refine ⟨IsGreatest.csSup_eq ⟨⟨⟨0, Set.self_mem_Ici⟩, wn_F_nonneg hA x.2, ?_⟩, ?_⟩, ?_⟩
  · simp [wn_u]
  · rintro _ ⟨y, hy, rfl⟩
    have hy0 : (0 : ℝ) ≤ y := y.2
    simp only [wn_u, Pi.zero_apply, mul_zero, add_zero]
    exact Real.rpow_le_rpow (sub_nonneg.2 hy) (by linarith) hγ.le
  · unfold wn_phi
    linarith

/-- **Example 7.3.2** (Miao, p. 216), corrected. With the weight `ϕ_M = M + F^γ`, `M > 0`,
condition (7.27) holds with `θ = β(A^γ + M^{α−1})`, and (7.28) holds: `T0 = F^γ ≤ ϕ_M`. For the
book's weight (`M = 1`) this is `θ = β(A^γ + 1)`; under `βA^γ < 1`, `θ < 1` for large `M`
(`wn_exists_M`). The book's `θ = βA^γ` is not valid (`example_7_3_2_7_27_fails`). -/
theorem example_7_3_2 {M β : ℝ} (hA : 1 < A) (hα0 : 0 < α) (hα1 : α < 1) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hβ : 0 ≤ β) (hM : 0 < M) :
    (∀ x : wn_Rp, ∀ y ∈ wn_Γ A α x,
      β * (wn_phi M A α γ y / wn_phi M A α γ x) ≤ β * (A ^ γ + M ^ (α - 1))) ∧
      ∀ x : wn_Rp, |wn_duranT (wn_u A α γ) (wn_Γ A α) β 0 x| ≤ 1 * wn_phi M A α γ x := by
  refine ⟨fun x y hy => mul_le_mul_of_nonneg_left ?_ hβ, fun x => ?_⟩
  · have hx : (0 : ℝ) ≤ x := x.2
    have hy0 : (0 : ℝ) ≤ y := y.2
    exact (example_7_3_2_first_step (M := M) (γ := γ) (by linarith) hα0.le hγ0.le hM hx hy0
      hy).1.trans (wn_ratio_le hA.le hα0.le hα1.le hγ0.le hγ1 hM
        (wn_F_nonneg (by linarith) hx))
  · obtain ⟨h1, h2⟩ := example_7_3_2_T0 (A := A) (α := α) (M := M) (β := β) (by linarith) hγ0 hM x
    rw [h1, abs_of_nonneg (Real.rpow_nonneg (wn_F_nonneg (by linarith) x.2) _), one_mul]
    exact h2.le

/-- Miao, p. 216: if `βA^γ < 1` (`α < 1`), some `M ≥ 1` has `β(A^γ + M^{α−1}) < 1`. -/
theorem wn_exists_M {β : ℝ} (hα1 : α < 1) (hθ : β * A ^ γ < 1) :
    ∃ M : ℝ, 1 ≤ M ∧ β * (A ^ γ + M ^ (α - 1)) < 1 := by
  have h2 : Tendsto (fun z : ℝ => z ^ (α - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)
    simpa only [neg_sub] using this
  have ht : Tendsto (fun M : ℝ => β * (A ^ γ + M ^ (α - 1))) atTop (𝓝 (β * (A ^ γ + 0))) :=
    (tendsto_const_nhds.add h2).const_mul β
  rw [add_zero] at ht
  obtain ⟨M, hM1, hM2⟩ := ((ht.eventually (gt_mem_nhds hθ)).and (eventually_ge_atTop 1)).exists
  exact ⟨M, hM2, hM1⟩

/-- **Exercise 7.3** (Miao, p. 228; the conclusion of Example 7.3.2). With
`Γ(K) = [0, AK + K^α]`, `A > 1`, `α ∈ (0, 1)`, `u = C^γ`, `γ ∈ (0, 1]`, `β > 0` and
`βA^γ < 1`, the Bellman equation `V = TV` has exactly one solution in `C_ϕ(ℝ₊)` for the book's
weight `ϕ = 1 + F^γ`. The proof runs Duran's argument with `ϕ_M = M + F^γ` for a large `M`
(the same space, since `ϕ ≤ ϕ_M ≤ Mϕ` for `M ≥ 1`). -/
theorem ex_7_3 {β : ℝ} (hA : 1 < A) (hα0 : 0 < α) (hα1 : α < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hβ : 0 < β) (hθ : β * A ^ γ < 1) :
    ∃! V, wn_InC (fun x : wn_Rp => wn_phi 1 A α γ x) V ∧
      wn_duranT (wn_u A α γ) (wn_Γ A α) β V = V := by
  obtain ⟨M, hM1, hMθ⟩ := wn_exists_M (A := A) (γ := γ) hα1 hθ
  have hM : 0 < M := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hFγ : ∀ x : wn_Rp, 0 ≤ wn_F A α x ^ γ := fun x =>
    Real.rpow_nonneg (wn_F_nonneg hA0 x.2) _
  have hcont : ∀ M' : ℝ, Continuous fun x : wn_Rp => wn_phi M' A α γ x := fun M' =>
    continuous_const.add (((wn_F_continuous hα0.le).comp continuous_subtype_val).rpow_const
      fun _ => Or.inr hγ0.le)
  have hpos : ∀ x : wn_Rp, 0 < wn_phi M A α γ x := fun x => by
    unfold wn_phi; linarith [hFγ x]
  obtain ⟨h727, h728⟩ := example_7_3_2 (M := M) hA hα0 hα1 hγ0 hγ1 hβ.le hM
  have hθ0 : 0 ≤ β * (A ^ γ + M ^ (α - 1)) :=
    mul_nonneg hβ.le (add_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hM.le _))
  have hfix := wn_duran_fixed_point (wn_u_continuous (A := A) hα0.le hγ0.le)
    ⟨wn_Γ_compact, wn_Γ_lhc hA0 hα0.le, wn_Γ_uhc hA0 hα0.le⟩ hβ.le (hcont M) hpos hθ0 hMθ
    (fun x => (eq_7_27_iff wn_Γ_compact (fun x => (wn_Γ_lhc hA0 hα0.le x).1) hβ.le (hcont M)
      hpos _ x).2 (h727 x)) ⟨1, h728⟩
  -- `ϕ ≤ ϕ_M ≤ Mϕ`
  have hle1 : ∀ x : wn_Rp, wn_phi 1 A α γ x ≤ 1 * wn_phi M A α γ x := fun x => by
    unfold wn_phi; linarith
  have hle2 : ∀ x : wn_Rp, wn_phi M A α γ x ≤ M * wn_phi 1 A α γ x := fun x => by
    unfold wn_phi; nlinarith [hFγ x]
  have hnn1 : ∀ x : wn_Rp, 0 ≤ wn_phi 1 A α γ x := fun x => by unfold wn_phi; linarith [hFγ x]
  have hnnM : ∀ x : wn_Rp, 0 ≤ wn_phi M A α γ x := fun x => (hpos x).le
  obtain ⟨V, ⟨hV, hVfix⟩, huniq⟩ := hfix
  exact ⟨V, ⟨wn_inC_of_le hnnM hle2 hV, hVfix⟩, fun W ⟨hW, hWfix⟩ =>
    huniq W ⟨wn_inC_of_le hnn1 hle1 hW, hWfix⟩⟩

/-- Miao, p. 217 (log AK model). For `u(x, y) = ln(Ax − y)` and `ϕ(x) = 1 + |ln(Ax)|`, at every
state `x > 0`, for every `β > 0` and every `θ`, some `y ∈ (0, Ax]` has `βϕ(y)/ϕ(x) > θ`: the
sup in (7.27) is `+∞` (`ϕ(y) → ∞` as `y → 0`). -/
theorem wn_log_ak_7_27_fails {β : ℝ} (hA : 0 < A) (hβ : 0 < β) (θ : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ y, 0 < y ∧ y ≤ A * x ∧
      θ < β * ((1 + |Real.log (A * y)|) / (1 + |Real.log (A * x)|)) := by
  set D := 1 + |Real.log (A * x)|
  have hD : 0 < D := by positivity
  set N := max (max (θ * D / β) (-Real.log (A * (A * x)))) 0 + 1
  have hN0 : 0 < N := by positivity
  have hN1 : θ * D / β < N := by
    have := le_max_left (θ * D / β) (-Real.log (A * (A * x)))
    have := le_max_left (max (θ * D / β) (-Real.log (A * (A * x)))) 0
    linarith
  have hN2 : -Real.log (A * (A * x)) < N := by
    have := le_max_right (θ * D / β) (-Real.log (A * (A * x)))
    have := le_max_left (max (θ * D / β) (-Real.log (A * (A * x)))) 0
    linarith
  refine ⟨Real.exp (-N) / A, div_pos (Real.exp_pos _) hA, ?_, ?_⟩
  · rw [div_le_iff₀ hA, mul_comm (A * x) A, ← Real.le_log_iff_exp_le (by positivity)]
    linarith
  · rw [mul_div_cancel₀ _ hA.ne', Real.log_exp, abs_neg, abs_of_pos hN0, ← mul_div_assoc,
      lt_div_iff₀ hD]
    rw [div_lt_iff₀ hβ] at hN1
    nlinarith

/-- Miao, p. 217: "condition (7.27) can never be satisfied" for the log AK model with
`ϕ(x) = 1 + |ln(Ax)|`: for every `β > 0`, every `θ` and every state `x > 0`, the bound
`βϕ(y)/ϕ(x) ≤ θ` fails for some `y ∈ (0, Ax]`. -/
theorem wn_log_ak_7_27_never {β : ℝ} (hA : 0 < A) (hβ : 0 < β) :
    ¬ ∃ θ : ℝ, ∃ x : ℝ, 0 < x ∧ ∀ y, 0 < y → y ≤ A * x →
      β * ((1 + |Real.log (A * y)|) / (1 + |Real.log (A * x)|)) ≤ θ := by
  rintro ⟨θ, x, hx, h⟩
  obtain ⟨y, hy0, hy1, hy⟩ := wn_log_ak_7_27_fails hA hβ θ hx
  exact absurd (h y hy0 hy1) (not_le.2 hy)

end Miao.InfiniteHorizonDP
