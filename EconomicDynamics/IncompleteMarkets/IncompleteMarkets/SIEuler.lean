/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.SIModel

/-!
# §8.3.2: interior consumption and the Euler inequality from the Bellman equation

Copied from `EconomicDynamics/Applications` (module `SIEuler`), namespace renamed.

Miao, §8.3, p. 239, (8.7), in the stationary form used in §8.3.2 (pp. 249–259). For a solution
`(V, â)` of the Bellman equation (`SIModel.Solution`), and every `x ≥ x_min`:

* `cons_pos`: **consumption is interior**, `c(x) = x − â(x) > 0` (the Inada condition
  `u′(0+) = ∞` against the bounded marginal continuation value `βR V′(x_min)`);
* `euler`: **the Euler inequality** `u′(c(x)) ≥ βR E V′(Râ(x) + y − rb)`, with equality if
  `â(x) > 0`; it is derived from the maximisation in the Bellman equation by one-sided
  difference quotients (mean value bounds for `u` and `V`, continuity of `D`), not assumed;
* `eq_8_7`: the same with `E V′(x′) = E u′(c(x′))` (envelope condition): this is (8.7),
  `u′(c_t) ≥ βR E_t u′(c_{t+1})`, with equality if `â_{t+1} > 0`;
* `dV_pos`, `D_pos`: `V′ > 0` and `D > 0`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology

namespace SIModel.Solution

variable {M : SIModel} (S : M.Solution)

theorem cons_eq (x : ℝ) : S.cons x = x - S.sav x := rfl

/-- The Bellman objective at the optimum: `V(x) = u(c(x)) + βW(â(x))`. -/
theorem bellman' {x : ℝ} (hx : M.xmin ≤ x) : S.V x = M.u (x - S.sav x) + M.β * S.W (S.sav x) :=
  S.bellman x hx

/-- The Bellman inequality: `u(x − s) + βW(s) ≤ V(x)` for `s ∈ [0, x]`. -/
theorem bellman_le' {x : ℝ} (hx : M.xmin ≤ x) {s : ℝ} (hs : s ∈ Set.Icc 0 x) :
    M.u (x - s) + M.β * S.W s ≤ S.V x :=
  S.bellman_le x hx s hs

/-- **Consumption is interior** (Miao, p. 240): `c(x) = x − â(x) > 0` for `x ≥ x_min`. -/
theorem cons_pos {x : ℝ} (hx : M.xmin ≤ x) : 0 < S.cons x := by
  have hx0 : 0 < x := M.xmin_pos.trans_le hx
  obtain ⟨hs0, hsx⟩ := S.sav_mem x hx
  rw [cons_eq]
  rcases hsx.lt_or_eq with hlt | heq
  · exact sub_pos.2 hlt
  exfalso
  set K := M.β * M.R * S.dV M.xmin
  obtain ⟨c, hcK, hc⟩ : ∃ c, K < M.du c ∧ c ∈ Set.Ioo 0 x :=
    ((M.inada_zero.eventually (eventually_gt_atTop K)).and (Ioo_mem_nhdsGT hx0)).exists
  have hsmem : x - c ∈ Set.Icc 0 x := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hle := S.bellman_le' hx hsmem
  rw [S.bellman' hx, heq, sub_self, show x - (x - c) = c by ring] at hle
  have hW := (S.W_sub_bounds hsmem.1 hsmem.2).2
  rw [show x - (x - c) = c by ring] at hW
  have hD := S.D_le hsmem.1
  have hu := (M.tangent_u le_rfl hc.1).1
  rw [sub_zero] at hu
  have hβ := M.β_pos
  have hR := M.R_pos
  have e1 : M.β * (S.W x - S.W (x - c)) ≤ M.β * (M.R * c * S.dV M.xmin) := by
    refine mul_le_mul_of_nonneg_left (hW.trans ?_) hβ.le
    exact mul_le_mul_of_nonneg_left hD (mul_nonneg hR.le hc.1.le)
  have e2 : c * K < c * M.du c := mul_lt_mul_of_pos_left hcK hc.1
  have e3 : c * K = M.β * (M.R * c * S.dV M.xmin) := by simp only [K]; ring
  nlinarith

/-- The Euler inequality from right difference quotients: `βR D(â(x)) ≤ u′(c(x))`. -/
theorem euler_le {x : ℝ} (hx : M.xmin ≤ x) : M.β * M.R * S.D (S.sav x) ≤ M.du (S.cons x) := by
  obtain ⟨hs0, hsx⟩ := S.sav_mem x hx
  have hc := S.cons_pos hx
  rw [cons_eq] at hc ⊢
  set s₀ := S.sav x
  have hsx' : s₀ < x := by linarith
  have hβ := M.β_pos
  have hV := S.bellman' hx
  have hduc : ContinuousAt (fun s => M.du (x - s)) s₀ :=
    ((M.du_cont _ (Set.mem_Ioi.2 hc)).continuousAt (Ioi_mem_nhds hc)).comp
      (continuous_const.sub continuous_id).continuousAt
  have hDw : ContinuousWithinAt S.D (Set.Ici 0) s₀ := S.D_continuousOn s₀ (Set.mem_Ici.2 hs0)
  have hf : Tendsto (fun s => M.du (x - s) - M.β * M.R * S.D s) (𝓝[>] s₀)
      (𝓝 (M.du (x - s₀) - M.β * M.R * S.D s₀)) :=
    (hduc.tendsto.mono_left nhdsWithin_le_nhds).sub
      (((hDw.mono fun t ht => Set.mem_Ici.2 (hs0.trans (Set.mem_Ioi.1 ht).le)).tendsto
        ).const_mul _)
  have hev : ∀ᶠ s in 𝓝[>] s₀, 0 ≤ M.du (x - s) - M.β * M.R * S.D s := by
    filter_upwards [Ioo_mem_nhdsGT hsx'] with s hs
    have hsm : s ∈ Set.Icc 0 x := ⟨hs0.trans hs.1.le, hs.2.le⟩
    have hle := S.bellman_le' hx hsm
    rw [hV] at hle
    have hW := (S.W_sub_bounds hs0 hs.1.le).1
    have hu := (M.tangent_u (c := x - s) (c' := x - s₀) (by linarith [hs.2])
      (by linarith [hs.1])).2 (by linarith [hs.2])
    have hpos : 0 < s - s₀ := sub_pos.2 hs.1
    have key : (s - s₀) * (M.β * M.R * S.D s) ≤ (s - s₀) * M.du (x - s) := by
      have e1 : M.β * (M.R * (s - s₀) * S.D s) ≤ M.β * (S.W s - S.W s₀) :=
        mul_le_mul_of_nonneg_left hW hβ.le
      have e2 : x - s₀ - (x - s) = s - s₀ := by ring
      rw [e2] at hu
      nlinarith
    have := le_of_mul_le_mul_left key hpos
    linarith
  have := ge_of_tendsto hf hev
  linarith

/-- The Euler equation from left difference quotients: if `â(x) > 0` then
`u′(c(x)) ≤ βR D(â(x))`. -/
theorem euler_ge {x : ℝ} (hx : M.xmin ≤ x) (hpos : 0 < S.sav x) :
    M.du (S.cons x) ≤ M.β * M.R * S.D (S.sav x) := by
  obtain ⟨hs0, hsx⟩ := S.sav_mem x hx
  have hc := S.cons_pos hx
  rw [cons_eq] at hc ⊢
  set s₀ := S.sav x
  have hβ := M.β_pos
  have hV := S.bellman' hx
  have hduc : ContinuousAt (fun s => M.du (x - s)) s₀ :=
    ((M.du_cont _ (Set.mem_Ioi.2 hc)).continuousAt (Ioi_mem_nhds hc)).comp
      (continuous_const.sub continuous_id).continuousAt
  have hDc : ContinuousAt S.D s₀ :=
    (S.D_continuousOn s₀ (Set.mem_Ici.2 hs0)).continuousAt (Ici_mem_nhds hpos)
  have hf : Tendsto (fun s => M.du (x - s) - M.β * M.R * S.D s) (𝓝[<] s₀)
      (𝓝 (M.du (x - s₀) - M.β * M.R * S.D s₀)) :=
    ((hduc.tendsto.sub (hDc.tendsto.const_mul _))).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] s₀, M.du (x - s) - M.β * M.R * S.D s ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT hpos] with s hs
    have hsm : s ∈ Set.Icc 0 x := ⟨hs.1.le, (hs.2.trans_le hsx).le⟩
    have hle := S.bellman_le' hx hsm
    rw [hV] at hle
    have hW := (S.W_sub_bounds hs.1.le hs.2.le).2
    have hu := (M.tangent_u (c := x - s₀) (c' := x - s) hc.le (by linarith [hs.2])).1
    have hpos' : 0 < s₀ - s := sub_pos.2 hs.2
    have key : (s₀ - s) * M.du (x - s) ≤ (s₀ - s) * (M.β * M.R * S.D s) := by
      have e1 : M.β * (S.W s₀ - S.W s) ≤ M.β * (M.R * (s₀ - s) * S.D s) :=
        mul_le_mul_of_nonneg_left hW hβ.le
      have e2 : x - s - (x - s₀) = s₀ - s := by ring
      rw [e2] at hu
      nlinarith
    have := le_of_mul_le_mul_left key hpos'
    linarith
  have := le_of_tendsto hf hev
  linarith

/-- **The Euler inequality** (Miao, (8.7), p. 239, stationary form): for `x ≥ x_min`,
`βR E V′(Râ(x) + y − rb) ≤ u′(c(x))`, with equality if `â(x) > 0`. Derived from the Bellman
equation. -/
theorem euler {x : ℝ} (hx : M.xmin ≤ x) :
    M.β * M.R * S.D (S.sav x) ≤ M.du (S.cons x) ∧
      (0 < S.sav x → M.du (S.cons x) = M.β * M.R * S.D (S.sav x)) :=
  ⟨S.euler_le hx, fun h => le_antisymm (S.euler_ge hx h) (S.euler_le hx)⟩

/-- `V′(x) = u′(c(x)) > 0` for `x ≥ x_min`. -/
theorem dV_pos {x : ℝ} (hx : M.xmin ≤ x) : 0 < S.dV x := by
  rw [S.envelope x hx]
  exact M.du_pos _ (S.cons_pos hx)

/-- `D(s) > 0` for `s ≥ 0`. -/
theorem D_pos {s : ℝ} (hs : 0 ≤ s) : 0 < S.D s := by
  refine si_integral_pos (S.integrable_dV hs) ?_
  filter_upwards [M.ae_next hs] with y hy
  exact S.dV_pos hy.1

/-- The envelope condition along next period's cash on hand:
`D(s) = E u′(c(Rs + y − rb))`. -/
theorem D_eq {s : ℝ} (hs : 0 ≤ s) : S.D s = ∫ y, M.du (S.cons (M.next s y)) ∂M.law := by
  refine integral_congr_ae ?_
  filter_upwards [M.ae_next hs] with y hy
  exact S.envelope _ hy.1

/-- **(8.7)** (Miao, p. 239), for iid income: `u′(c_t) ≥ βR E_t u′(c_{t+1})`, with equality if
`â_{t+1} > 0`, where `c_{t+1} = c(Râ(x_t) + y_{t+1} − rb)`. -/
theorem eq_8_7 {x : ℝ} (hx : M.xmin ≤ x) :
    M.β * M.R * ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law ≤ M.du (S.cons x) ∧
      (0 < S.sav x →
        M.du (S.cons x) = M.β * M.R * ∫ y, M.du (S.cons (M.next (S.sav x) y)) ∂M.law) := by
  rw [← S.D_eq (S.sav_mem x hx).1]
  exact S.euler hx

end SIModel.Solution

end Miao.IncompleteMarkets
