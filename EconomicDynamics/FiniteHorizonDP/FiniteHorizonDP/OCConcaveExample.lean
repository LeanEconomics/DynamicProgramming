/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.OCConcave

/-!
# Theorem 6.4.3: the policy correspondence need not be single-valued

Miao, §6.4, p. 177. The book concludes from strict concavity of `V_t(·, z)` that `G_t` is
single-valued. Assumption 6.4.10 is strict only in `x`, so the objective
`u_t(x, z, a) + β E V_{t+1}(φ(x, a, z, z′), z′)` need not be strictly concave in `a`.

`theorem_6_4_3_counterexample`: `X = (−∞, 0]`, `A = Γ(x, z) = [0, 1]`, `Z` a single point,
`φ(x, a, z, z′) = x`, `u_t(x, z, a) = u_T(x, z) = −x²`, `β = 1/2`, `T = 1`. Assumptions
6.4.1–6.4.12 and 5.1.2 all hold, but `G_0(0, z) = [0, 1]`. Hence `theorem_6_4_3` adds that
`φ(x, ·, z, z′)` is one-to-one on `A`.

`isLHC_const`, `isUHC_const`: a constant nonempty compact correspondence is continuous.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

/-- A constant nonempty correspondence is lower hemicontinuous. -/
theorem isLHC_const {S Y : Type*} [MetricSpace S] [MetricSpace Y] {K : Set Y} (hK : K.Nonempty)
    (s : S) : IsLHC (fun _ : S => K) s :=
  ⟨hK, fun y hy _ _ => ⟨0, fun _ => y, fun _ _ => hy, tendsto_const_nhds⟩⟩

/-- A constant nonempty compact correspondence is upper hemicontinuous. -/
theorem isUHC_const {S Y : Type*} [MetricSpace S] [MetricSpace Y] {K : Set Y} (hK : K.Nonempty)
    (hc : IsCompact K) (s : S) : IsUHC (fun _ : S => K) s :=
  ⟨hK, fun _ _ _ hys => hc.tendsto_subseq hys⟩

/-- The model of the counterexample to single-valuedness of `G_t`. -/
noncomputable def oc_flatModel : OCModel ℝ ℝ Unit :=
  ⟨Set.Iic 0, Set.Icc 0 1, Kernel.const Unit (Measure.dirac ()), fun _ _ => Set.Icc 0 1,
    fun x _ _ _ => x, fun _ x _ _ => -x ^ 2, fun x _ => -x ^ 2, 1 / 2, 1⟩

theorem oc_negSq_comb {x y θ η : ℝ} (hs : θ + η = 1) :
    -(θ * x + η * y) ^ 2 - (θ * -x ^ 2 + η * -y ^ 2) = θ * η * (x - y) ^ 2 := by
  have : η = 1 - θ := by linarith
  subst this
  ring

theorem oc_negSq_strict : StrictConcaveOn ℝ (Set.Iic (0 : ℝ)) fun x => -x ^ 2 := by
  refine ⟨convex_Iic 0, fun x _ y _ hne θ η hθ hη hs => ?_⟩
  simp only [smul_eq_mul]
  have h := oc_negSq_comb (x := x) (y := y) hs
  have : 0 < θ * η * (x - y) ^ 2 := by
    have := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
    positivity
  linarith

/-- **Counterexample to Theorem 6.4.3 as printed** (Miao, p. 177): Assumptions 6.4.1–6.4.12 and
5.1.2 hold, but the policy correspondence `G_0(0, z) = [0, 1]` is not single-valued. -/
theorem theorem_6_4_3_counterexample :
    ∃ M : OCModel ℝ ℝ Unit, IsMarkovKernel M.Q ∧ M.Assumption641 ∧ M.Assumption642 ∧
      M.Assumption643ii ∧ M.Assumption644 ∧ M.Assumption645 ∧ M.Assumption646 ∧
      M.Assumption647 ∧ M.Assumption648 ∧ M.Assumption649 ∧ M.Assumption6410 ∧
      M.Assumption6411 ∧ M.Assumption6412 ∧ 0 < M.β ∧ M.β < 1 ∧ 0 < M.T ∧
      ¬ (M.G 0 0 ()).Subsingleton := by
  have hX : oc_flatModel.X = Set.Iic 0 := rfl
  have hA : oc_flatModel.A = Set.Icc 0 1 := rfl
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
  have h644 : oc_flatModel.Assumption644 :=
    ⟨fun _ _ _ => subset_rfl, fun s => ⟨isCompact_Icc, isLHC_const hne s,
      isUHC_const hne isCompact_Icc s⟩⟩
  have h6410 : oc_flatModel.Assumption6410 := by
    refine ⟨fun _ => oc_negSq_strict, fun t _ z x _ x' _ a _ a' _ θ η hθ hη hs => ?_⟩
    change θ * -x ^ 2 + η * -x' ^ 2 ≤ -(θ • x + η • x') ^ 2 ∧
      (x ≠ x' → θ * -x ^ 2 + η * -x' ^ 2 < -(θ • x + η • x') ^ 2)
    simp only [smul_eq_mul]
    have h := oc_negSq_comb (x := x) (y := x') hs
    refine ⟨by nlinarith [sq_nonneg (x - x'), mul_pos hθ hη], fun hxx => ?_⟩
    have := sq_pos_of_ne_zero (sub_ne_zero.2 hxx)
    nlinarith [mul_pos (mul_pos hθ hη) this]
  have hMk : IsMarkovKernel oc_flatModel.Q := by
    change IsMarkovKernel (Kernel.const Unit (Measure.dirac ()))
    infer_instance
  refine ⟨oc_flatModel, hMk, ⟨convex_Iic 0, measurableSet_Iic⟩, ⟨convex_Icc 0 1,
    measurableSet_Icc⟩, ⟨inferInstance, inferInstance, fun f _ _ => continuous_of_discreteTopology⟩,
    h644, ⟨fun x hx _ _ _ _ => hx, continuous_fst.continuousOn⟩,
    ⟨fun _ _ => (continuous_fst.pow 2).neg.continuousOn, (continuous_fst.pow 2).neg.continuousOn⟩,
    ⟨fun _ => ?_, fun _ _ _ _ _ => ?_⟩, fun _ _ _ _ _ _ => subset_rfl,
    fun _ _ _ _ _ _ _ _ h => h, h6410, fun _ _ _ _ _ a ha a' ha' θ η hθ hη hs =>
      (convex_Icc 0 1) ha ha' hθ.le hη.le hs, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => le_rfl,
    by norm_num [oc_flatModel], by norm_num [oc_flatModel], by norm_num [oc_flatModel], ?_⟩
  · intro x hx y hy hxy
    change -x ^ 2 < -y ^ 2
    have hy' : y ≤ 0 := hy
    nlinarith
  · intro x hx y hy hxy
    change -x ^ 2 < -y ^ 2
    have hy' : y ≤ 0 := hy
    nlinarith
  · -- every action is optimal at `t = 0`
    have hconst : ∀ a, oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () a =
        oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0 := fun _ => rfl
    have hV : oc_flatModel.V 0 0 () = oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0 := by
      rw [oc_flatModel.V_succ_apply (by norm_num [oc_flatModel])]
      have : oc_flatModel.obj 0 (oc_flatModel.V (0 + 1)) 0 () '' oc_flatModel.Γ 0 () =
          {oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0} := by
        rw [show oc_flatModel.obj 0 (oc_flatModel.V (0 + 1)) 0 () =
          fun _ => oc_flatModel.obj 0 (oc_flatModel.V 1) 0 () 0 from funext hconst]
        exact hne.image_const _
      rw [this, csSup_singleton]
    have hmem : ∀ a ∈ Set.Icc (0 : ℝ) 1, a ∈ oc_flatModel.G 0 0 () := fun a ha =>
      ⟨ha, by rw [hV]; exact hconst a⟩
    intro hsub
    have := hsub (hmem 0 ⟨le_rfl, zero_le_one⟩) (hmem 1 ⟨zero_le_one, le_rfl⟩)
    norm_num at this

end Miao.FiniteHorizonDP
