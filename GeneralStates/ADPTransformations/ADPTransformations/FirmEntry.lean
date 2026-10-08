/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.Semiconjugacy
import ADPTransformations.BMOperators
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Firm entry

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.2.1.3 (pp. 163–166).

Firm value solves (5.18), `v(z, f) = max{s(z) − f, β(z) ∫∫ v(z', f')φ(df')Q(z, dz')}`, with an
exogenous state `z` (kernel `Q`), an iid fixed cost `f ≥ 0` (distribution `φ`) and a state-dependent
discount factor `β(z) ≥ 0`. Here the cost is a nonnegative measurable function `c` of a draw from
`φ` on any measurable space.

* `S = G ∘ F` on `bX` and `T = F ∘ G` on `bZ`, with `(Fv)(z) = ∫ v(z, f)φ(df)` and
  `(Gw)(z, f) = max{s(z) − f, β(z) ∫ w(z')Q(z, dz')}`: **Lemma 5.2.6**.
* **Lemma 5.2.5**: under Assumption 5.2.1, `T` is strongly order stable on `bZ`. Condition (iii),
  `sup_z 𝔼_z ∏_{t<n} β(Z_t) < 1`, is stated as `sup_z (Kⁿ𝟙)(z) < 1` for the discount operator
  `(Kh)(z) = β(z) ∫ h(z')Q(z, dz')` (the two agree by Lemma 6.1.4); then `T` is an order contraction
  of modulus `K` (Theorem 4.1.4).
* **Lemma 5.2.8**: `G` preserves increasing and decreasing limits (dominated convergence; the
  book proves the increasing case).
* **Proposition 5.2.7**: (5.18) has a unique solution `v̄ ∈ bX`, and `w ≼ Tw ⟹ GTⁿw ↑ v̄`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPTransformations

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

namespace BM

variable {X : Type*} [MeasurableSpace X]

/-- **Lemma A.1.3** in `bX`: `fₙ ↑ w` gives pointwise convergence. -/
theorem tendsto_of_isLUB {f : ℕ → BM X} {w : BM X} (hf : Monotone f) (hl : IsLUB (range f) w)
    (x : X) : Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x)) := by
  have hbdd : ∀ y, BddAbove (range fun n => (f n).toFun y) := fun y =>
    ⟨w.toFun y, by rintro _ ⟨n, rfl⟩; exact hl.1 ⟨n, rfl⟩ y⟩
  let g : BM X := ⟨fun y => ⨆ n, (f n).toFun y, Measurable.iSup fun n => (f n).measurable',
    ⟨‖f 0‖ + ‖w‖, fun y => abs_le.2 ⟨by
      have h1 := le_ciSup (hbdd y) 0
      have h2 := abs_le.1 (abs_le_norm (f 0) y)
      have h3 := norm_nonneg w
      linarith, by
      have h1 : (⨆ n, (f n).toFun y) ≤ w.toFun y := ciSup_le fun n => hl.1 ⟨n, rfl⟩ y
      have h2 := abs_le.1 (abs_le_norm w y)
      have h3 := norm_nonneg (f 0)
      linarith⟩⟩⟩
  have hgw : g = w := le_antisymm (fun y => ciSup_le fun n => hl.1 ⟨n, rfl⟩ y)
    (hl.2 (by rintro _ ⟨n, rfl⟩; exact fun y => le_ciSup (hbdd y) n))
  have hx : w.toFun x = ⨆ n, (f n).toFun x := by rw [← hgw]
  rw [hx]
  exact tendsto_atTop_ciSup (fun a b h => hf h x) (hbdd x)

/-- **Lemma A.1.3** in `bX`: `fₙ ↓ w` gives pointwise convergence. -/
theorem tendsto_of_isGLB {f : ℕ → BM X} {w : BM X} (hf : Antitone f) (hl : IsGLB (range f) w)
    (x : X) : Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x)) := by
  have hbdd : ∀ y, BddBelow (range fun n => (f n).toFun y) := fun y =>
    ⟨w.toFun y, by rintro _ ⟨n, rfl⟩; exact hl.1 ⟨n, rfl⟩ y⟩
  let g : BM X := ⟨fun y => ⨅ n, (f n).toFun y, Measurable.iInf fun n => (f n).measurable',
    ⟨‖f 0‖ + ‖w‖, fun y => abs_le.2 ⟨by
      have h1 : w.toFun y ≤ ⨅ n, (f n).toFun y := le_ciInf fun n => hl.1 ⟨n, rfl⟩ y
      have h2 := abs_le.1 (abs_le_norm w y)
      have h3 := norm_nonneg (f 0)
      linarith, by
      have h1 := ciInf_le (hbdd y) 0
      have h2 := abs_le.1 (abs_le_norm (f 0) y)
      have h3 := norm_nonneg w
      linarith⟩⟩⟩
  have hgw : g = w := le_antisymm
    (hl.2 (by rintro _ ⟨n, rfl⟩; exact fun y => ciInf_le (hbdd y) n))
    (fun y => le_ciInf fun n => hl.1 ⟨n, rfl⟩ y)
  have hx : w.toFun x = ⨅ n, (f n).toFun x := by rw [← hgw]
  rw [hx]
  exact tendsto_atTop_ciInf (fun a b h => hf h x) (hbdd x)

/-- Pointwise increasing convergence is `↑` in `bX`. -/
theorem isLUB_of_tendsto {f : ℕ → BM X} {w : BM X} (hf : Monotone f)
    (h : ∀ x, Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x))) : IsLUB (range f) w :=
  ⟨by rintro _ ⟨n, rfl⟩ x; exact Monotone.ge_of_tendsto (fun a b hab => hf hab x) (h x) n,
    fun _ hu x => le_of_tendsto' (h x) fun n => hu ⟨n, rfl⟩ x⟩

/-- Pointwise decreasing convergence is `↓` in `bX`. -/
theorem isGLB_of_tendsto {f : ℕ → BM X} {w : BM X} (hf : Antitone f)
    (h : ∀ x, Tendsto (fun n => (f n).toFun x) atTop (𝓝 (w.toFun x))) : IsGLB (range f) w :=
  ⟨by rintro _ ⟨n, rfl⟩ x; exact Antitone.le_of_tendsto (fun a b hab => hf hab x) (h x) n,
    fun _ hu x => ge_of_tendsto' (h x) fun n => hu ⟨n, rfl⟩ x⟩

/-- Integrals against a Markov kernel commute with `↑` and `↓` limits (dominated convergence). -/
theorem tendsto_markov {P : Kernel X X} [IsMarkovKernel P] {f : ℕ → BM X} {w : BM X} {B : ℝ}
    (hB : ∀ n y, |(f n).toFun y| ≤ B)
    (h : ∀ y, Tendsto (fun n => (f n).toFun y) atTop (𝓝 (w.toFun y))) (x : X) :
    Tendsto (fun n => (markovCLM P (f n)).toFun x) atTop (𝓝 ((markovCLM P w).toFun x)) := by
  simp only [markovCLM_apply, markovOp]
  exact tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (f n).measurable'.aestronglyMeasurable) (integrable_const B)
    (fun n => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB n y)
    (Eventually.of_forall h)

end BM

/-- The firm entry model of §5.2.1.3. -/
structure FirmEntry (Z Ef : Type*) [MeasurableSpace Z] [MeasurableSpace Ef] where
  /-- the exogenous kernel -/
  Q : Kernel Z Z
  [Q_markov : IsMarkovKernel Q]
  /-- the distribution of the fixed-cost draw -/
  φ : Measure Ef
  [φ_prob : IsProbabilityMeasure φ]
  /-- the fixed cost -/
  c : Ef → ℝ
  c_meas : Measurable c
  c_nonneg : ∀ f, 0 ≤ c f
  /-- the entry profit `s` -/
  s : BM Z
  /-- the discount factor `β(z) ≥ 0` -/
  β : BM Z
  β_nonneg : 0 ≤ β

namespace FirmEntry

attribute [local instance] FirmEntry.Q_markov FirmEntry.φ_prob

variable {Z Ef : Type*} [MeasurableSpace Z] [MeasurableSpace Ef] (M : FirmEntry Z Ef)

theorem integrable_section (v : BM (Z × Ef)) (z : Z) :
    Integrable (fun f => v.toFun (z, f)) M.φ :=
  Integrable.of_bound (v.measurable'.comp measurable_prodMk_left).aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun f => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)

/-- `(Fv)(z) = ∫ v(z, f)φ(df)`. -/
noncomputable def F (v : BM (Z × Ef)) : BM Z :=
  ⟨fun z => ∫ f, v.toFun (z, f) ∂M.φ,
    (v.measurable'.stronglyMeasurable.integral_prod_right' (ν := M.φ)).measurable,
    ⟨‖v‖, fun z => by
      have := norm_integral_le_of_norm_le_const (μ := M.φ) (f := fun f => v.toFun (z, f))
        (C := ‖v‖) (Eventually.of_forall fun f => by
          rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
      simpa using this⟩⟩

/-- `(Gw)(z, f) = max{s(z) − c(f), β(z) ∫ w(z')Q(z, dz')}`. -/
noncomputable def G (w : BM Z) : BM (Z × Ef) :=
  ⟨fun x => max (M.s.toFun x.1 - M.c x.2) (M.β.toFun x.1 * (BM.markovCLM M.Q w).toFun x.1),
    ((M.s.measurable'.comp measurable_fst).sub (M.c_meas.comp measurable_snd)).max
      ((M.β.measurable'.comp measurable_fst).mul
        ((BM.markovCLM M.Q w).measurable'.comp measurable_fst)),
    ⟨‖M.s‖ + ‖M.β‖ * ‖w‖, fun x => by
      have hb : |M.β.toFun x.1 * (BM.markovCLM M.Q w).toFun x.1| ≤ ‖M.β‖ * ‖w‖ := by
        rw [abs_mul, BM.markovCLM_apply]
        exact mul_le_mul (BM.abs_le_norm _ _) (abs_markovOp_le M.Q (BM.abs_le_norm w) _)
          (abs_nonneg _) (norm_nonneg _)
      have hs := abs_le.1 (BM.abs_le_norm M.s x.1)
      have hc := M.c_nonneg x.2
      have hb' := abs_le.1 hb
      have hn := norm_nonneg M.s
      refine abs_le.2 ⟨?_, max_le (by linarith) (by linarith)⟩
      exact (by linarith : -(‖M.s‖ + ‖M.β‖ * ‖w‖) ≤ _).trans (le_max_right _ _)⟩⟩

/-- The firm value operator `S = G ∘ F` on `bX`. -/
noncomputable def S (v : BM (Z × Ef)) : BM (Z × Ef) := M.G (M.F v)

/-- The low-dimensional operator `T = F ∘ G` on `bZ`. -/
noncomputable def T (w : BM Z) : BM Z := M.F (M.G w)

/-- `S` is the operator of (5.18):
`(Sv)(z, f) = max{s(z) − c(f), β(z) ∫∫ v(z', f')φ(df')Q(z, dz')}`. -/
theorem S_apply (v : BM (Z × Ef)) (x : Z × Ef) :
    (M.S v).toFun x = max (M.s.toFun x.1 - M.c x.2)
      (M.β.toFun x.1 * ∫ z', (∫ f', v.toFun (z', f') ∂M.φ) ∂(M.Q x.1)) := rfl

/-- `(Tw)(z) = ∫ max{s(z) − c(f), β(z) ∫ w(z')Q(z, dz')} φ(df)`. -/
theorem T_apply (w : BM Z) (z : Z) :
    (M.T w).toFun z = ∫ f, max (M.s.toFun z - M.c f)
      (M.β.toFun z * ∫ z', w.toFun z' ∂(M.Q z)) ∂M.φ := rfl

theorem F_mono : Monotone M.F := fun _ _ h z =>
  integral_mono (M.integrable_section _ z) (M.integrable_section _ z) fun f => h (z, f)

theorem G_mono : Monotone M.G := fun _ _ h x =>
  max_le_max le_rfl (mul_le_mul_of_nonneg_left (BM.markovCLM_isPositive M.Q |>.mono h x.1)
    (M.β_nonneg x.1))

/-- **Lemma 5.2.6** (p. 165): `(bX, S)` and `(bZ, T)` are strongly semiconjugate under the order
preserving maps `F, G`. -/
theorem lemma_5_2_6 : IsStronglySemiconj M.S M.T M.F M.G ∧ Monotone M.F ∧ Monotone M.G :=
  ⟨⟨fun _ => rfl, fun _ => rfl⟩, M.F_mono, M.G_mono⟩

/-- The discount operator `(Kh)(z) = β(z) ∫ h(z')Q(z, dz')` of (6.10). -/
noncomputable def K : BM Z →L[ℝ] BM Z := (BM.mulCLM M.β).comp (BM.markovCLM M.Q)

theorem K_isPositive : BanachLattice.IsPositiveOp M.K := fun h hh =>
  BM.mulCLM_isPositive M.β_nonneg _ (BM.markovCLM_isPositive M.Q h hh)

/-- `|Tw₁ − Tw₂| ≤ K|w₁ − w₂|` (proof of Lemma 5.2.5). -/
theorem abs_T_sub_le (w₁ w₂ : BM Z) : |M.T w₁ - M.T w₂| ≤ M.K |w₁ - w₂| := fun z => by
  have hpt : ∀ f, |(M.G w₁).toFun (z, f) - (M.G w₂).toFun (z, f)| ≤ (M.K |w₁ - w₂|).toFun z :=
    fun f => by
      refine (abs_max_sub_max_le _ _ _).trans ?_
      change |M.β.toFun z * _ - M.β.toFun z * _| ≤
        M.β.toFun z * (BM.markovCLM M.Q |w₁ - w₂|).toFun z
      rw [← mul_sub, abs_mul, abs_of_nonneg (M.β_nonneg z)]
      refine mul_le_mul_of_nonneg_left ?_ (M.β_nonneg z)
      have h1 := (BM.markovCLM_isPositive M.Q).abs_le (w₁ - w₂) z
      rw [map_sub] at h1
      exact h1
  change |∫ f, (M.G w₁).toFun (z, f) ∂M.φ - ∫ f, (M.G w₂).toFun (z, f) ∂M.φ| ≤ _
  rw [← integral_sub (M.integrable_section _ z) (M.integrable_section _ z)]
  have := norm_integral_le_of_norm_le_const (μ := M.φ)
    (f := fun f => (M.G w₁).toFun (z, f) - (M.G w₂).toFun (z, f))
    (C := (M.K |w₁ - w₂|).toFun z) (Eventually.of_forall fun f => by
      rw [Real.norm_eq_abs]; exact hpt f)
  simpa using this

/-- Assumption 5.2.1 (iii), in operator form: `sup_z (Kⁿ𝟙)(z) ≤ λ < 1` for some `n ≥ 1`. -/
def DiscountCondition : Prop :=
  ∃ n, 0 < n ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ z, ((M.K ^ n) (BM.const 1)).toFun z ≤ lam

theorem K_isDiscountOperator (hA : M.DiscountCondition) : BanachLattice.IsDiscountOperator M.K := by
  obtain ⟨n, hn, lam, hlam0, hlam1, hK⟩ := hA
  refine ⟨map_zero _, fun h hh => M.K_isPositive h hh, fun u hu v _ huv => M.K_isPositive.mono huv,
    n, hn, lam, hlam0, hlam1, fun u _ v _ => ?_⟩
  rw [← FunLike.coe_pow_eq_iterate, ← map_sub]
  refine BM.norm_le (mul_nonneg hlam0 (norm_nonneg _)) fun z => ?_
  have hpos := M.K_isPositive.iterate n
  have h1 := hpos.abs_le (u - v) z
  have h2 : |u - v| ≤ ‖u - v‖ • BM.const 1 := fun y => by
    simp only [BM.abs_apply, BM.smul_apply, BM.const_apply, mul_one]
    exact BM.abs_le_norm _ y
  have h3 := hpos.mono h2 z
  rw [map_smul] at h3
  simp only [BM.abs_apply, BM.smul_apply] at h1 h3
  calc |((M.K ^ n) (u - v)).toFun z| ≤ ((M.K ^ n) |u - v|).toFun z := h1
    _ ≤ ‖u - v‖ * ((M.K ^ n) (BM.const 1)).toFun z := h3
    _ ≤ ‖u - v‖ * lam := mul_le_mul_of_nonneg_left (hK z) (norm_nonneg _)
    _ = lam * ‖u - v‖ := mul_comm _ _

/-- **Lemma 5.2.5** (p. 165): under Assumption 5.2.1, `T` is strongly order stable on `bZ`. -/
theorem lemma_5_2_5 (hA : M.DiscountCondition) : StronglyOrderStable M.T := by
  have : Nonempty (BM Z) := ⟨0⟩
  have hι : BanachLattice.IsIsoOrderEmbedding (id : BM Z → BM Z) :=
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩
  have hgs := (BanachLattice.theorem_4_1_4 hι ⟨M.K_isDiscountOperator hA,
    fun v w => M.abs_T_sub_le v w⟩).1
  exact stronglyOrderStable_of_globallyStable (M.F_mono.comp M.G_mono) hgs

theorem tendsto_G {f : ℕ → BM Z} {w : BM Z} {B : ℝ} (hB : ∀ n y, |(f n).toFun y| ≤ B)
    (h : ∀ y, Tendsto (fun n => (f n).toFun y) atTop (𝓝 (w.toFun y))) (x : Z × Ef) :
    Tendsto (fun n => (M.G (f n)).toFun x) atTop (𝓝 ((M.G w).toFun x)) :=
  tendsto_const_nhds.max ((BM.tendsto_markov hB h x.1).const_mul _)

/-- **Lemma 5.2.8** (p. 166): `G` is order continuous, and it also preserves decreasing
limits. -/
theorem lemma_5_2_8 : OrderContinuous M.G ∧ OrderContinuousDown M.G := by
  refine ⟨fun f w hf hl => ?_, fun f w hf hl => ?_⟩
  · have hpt := BM.tendsto_of_isLUB hf hl
    have hB : ∀ n y, |(f n).toFun y| ≤ ‖f 0‖ + ‖w‖ := fun n y => abs_le.2
      ⟨by linarith [abs_le.1 (BM.abs_le_norm (f 0) y), hf (Nat.zero_le n) y, norm_nonneg w],
        by linarith [abs_le.1 (BM.abs_le_norm w y), hl.1 ⟨n, rfl⟩ y, norm_nonneg (f 0)]⟩
    exact BM.isLUB_of_tendsto (M.G_mono.comp hf) (M.tendsto_G hB hpt)
  · have hpt := BM.tendsto_of_isGLB hf hl
    have hB : ∀ n y, |(f n).toFun y| ≤ ‖f 0‖ + ‖w‖ := fun n y => abs_le.2
      ⟨by linarith [abs_le.1 (BM.abs_le_norm w y), hl.1 ⟨n, rfl⟩ y, norm_nonneg (f 0)],
        by linarith [abs_le.1 (BM.abs_le_norm (f 0) y), hf (Nat.zero_le n) y, norm_nonneg w]⟩
    exact BM.isGLB_of_tendsto (M.G_mono.comp_antitone hf) (M.tendsto_G hB hpt)

/-- **Proposition 5.2.7** (p. 166): under Assumption 5.2.1, the firm valuation equation (5.18) has
a unique solution `v̄` in `bX`, and `w ≼ Tw ⟹ GTⁿw ↑ v̄` for `w ∈ bZ`. -/
theorem proposition_5_2_7 (hA : M.DiscountCondition) :
    ∃ vbar, M.S vbar = vbar ∧ (∀ v, M.S v = v → v = vbar) ∧
      ∀ w, w ≤ M.T w → IncreasesTo (fun n => M.G (M.T^[n] w)) vbar := by
  have hT := M.lemma_5_2_5 hA
  obtain ⟨wbar, hwbar, -, -, -⟩ := id hT
  obtain ⟨h, hF, hG⟩ := M.lemma_5_2_6
  obtain ⟨hGu, hGd⟩ := M.lemma_5_2_8
  obtain ⟨hS, hfix, hconv⟩ := h.theorem_5_2_3 hF hG hGu hGd hT hwbar
  obtain ⟨u, hu, huniq, -, -⟩ := hS
  refine ⟨M.G wbar, hfix, fun v hv => (huniq v hv).trans (huniq _ hfix).symm, hconv⟩

end FirmEntry

end SargentStachurski.ADPTransformations
