/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.BRConcave
import InfiniteHorizonDP.OCConcaveExample

/-!
# Theorem 7.3.3: two counterexamples

Miao, §7.3.1, p. 209. Both models are deterministic (`Z` a single point), with `X = A = [0, 1]`
and `β = 1/10`.

* `theorem_7_3_3_counterexample`: **without Assumption 6.4.11, `V(·, z)` need not be concave.**
  `Γ(x, z) = {0, 1}`, `φ(x, a, z, z′) = a`, `u(x, z, a) = 4x − x²/2 − (x − a)²`. All the
  hypotheses the book lists for Theorem 7.3.3 hold (5.1.2, 6.4.1–6.4.5, 6.4.8, 6.4.9, 6.4.12,
  7.3.1, 7.3.2, 7.3.3), but the solution of (7.19) is
  `V(x) = 4x − 3x²/2 + max(0, 2x − 11/18)` (`br_cexV`), which has a convex kink at `x = 11/36`:
  `V(11/36) < (V(0) + V(11/18))/2`.
* `theorem_7_3_3_policy_counterexample`: **`G` need not be single-valued** even with Assumption
  6.4.11. `Γ(x, z) = [0, 1]`, `φ(x, a, z, z′) = x`, `u(x, z, a) = 4x − x²/2`: neither `u` nor `φ`
  depends on `a`, every feasible action is optimal, and `G(x, z) = A`. (As in Chapter 6,
  `theorem_6_4_3_counterexample`.)
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

/-- The reward `u(x, z, a) = 4x − x²/2 − (x − a)²` of the first counterexample. -/
noncomputable def br_cexU (x a : ℝ) : ℝ := 4 * x - x ^ 2 / 2 - (x - a) ^ 2

/-- The model of `theorem_7_3_3_counterexample`. -/
noncomputable def br_cexModel : OCModel ℝ ℝ Unit :=
  ⟨Set.Icc 0 1, Set.Icc 0 1, Kernel.const Unit (Measure.dirac ()), fun _ _ => {0, 1},
    fun _ a _ _ => a, fun _ x _ a => br_cexU x a, fun _ _ => 0, 1 / 10, 0⟩

/-- The solution `V(x) = 4x − 3x²/2 + max(0, 2x − 11/18)` of the first counterexample. -/
noncomputable def br_cexW (x : ℝ) : ℝ := 4 * x - 3 / 2 * x ^ 2 + max 0 (2 * x - 11 / 18)

theorem br_cexU_comb {x x' a a' θ η : ℝ} (hs : θ + η = 1) :
    br_cexU (θ * x + η * x') (θ * a + η * a') - (θ * br_cexU x a + η * br_cexU x' a') =
      θ * η * ((x - x') ^ 2 / 2 + ((x - a) - (x' - a')) ^ 2) := by
  have : η = 1 - θ := by linarith
  subst this
  simp only [br_cexU]
  ring

theorem br_cex_a733 {u : ℝ → ℝ → ℝ} (hu : ∀ {x x' a a' θ η : ℝ}, θ + η = 1 →
      u (θ * x + η * x') (θ * a + η * a') - (θ * u x a + η * u x' a') =
        θ * η * ((x - x') ^ 2 / 2 + ((x - a) - (x' - a')) ^ 2))
    {x x' a a' θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hs : θ + η = 1) :
    θ * u x a + η * u x' a' ≤ u (θ * x + η * x') (θ * a + η * a') ∧
      (x ≠ x' → θ * u x a + η * u x' a' < u (θ * x + η * x') (θ * a + η * a')) := by
  have h := hu (x := x) (x' := x') (a := a) (a' := a') hs
  have hθη : 0 < θ * η := mul_pos hθ hη
  refine ⟨by nlinarith [sq_nonneg (x - x'), sq_nonneg ((x - a) - (x' - a'))], fun hne => ?_⟩
  have := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
  nlinarith [sq_nonneg ((x - a) - (x' - a')), mul_pos hθη this]

theorem br_cexModel_markov : IsMarkovKernel br_cexModel.Q := by
  change IsMarkovKernel (Kernel.const Unit (Measure.dirac ()))
  infer_instance

theorem br_cex_a645 : br_cexModel.Assumption645 :=
  ⟨fun _ _ _ ha _ _ => ha, (continuous_fst.comp continuous_snd).continuousOn⟩

theorem br_cex_a644 : br_cexModel.Assumption644 := by
  have hne : ({0, 1} : Set ℝ).Nonempty := ⟨0, by simp⟩
  have hc : IsCompact ({0, 1} : Set ℝ) := (Set.toFinite _).isCompact
  refine ⟨fun _ _ _ a ha => ?_, fun s => ⟨hc, isLHC_const hne s, isUHC_const hne hc s⟩⟩
  rcases ha with rfl | rfl
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩

theorem br_cex_a731 : Assumption731 br_cexModel := by
  refine ⟨Continuous.continuousOn (by unfold br_cexModel br_cexU; fun_prop), 10,
    fun x hx _ a ha => ?_⟩
  change |br_cexU x a| ≤ 10
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha0, ha1⟩ := ha
  simp only [br_cexU]
  rw [abs_le]
  constructor <;> nlinarith

/-- The fixed point of the first counterexample, as a bounded continuous function. -/
noncomputable def br_cexV : ↥br_cexModel.X × Unit →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => br_cexW p.1)
    (by unfold br_cexW; fun_prop) 8 fun p => by
      obtain ⟨h0, h1⟩ := p.1.2
      rw [Real.norm_eq_abs, abs_le]
      simp only [br_cexW]
      constructor <;> nlinarith [le_max_left 0 (2 * (p.1 : ℝ) - 11 / 18),
        max_le (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 2 * (p.1 : ℝ) - 11 / 18 ≤ 2)]

theorem br_cexV_apply (p : ↥br_cexModel.X × Unit) : br_cexV p = br_cexW p.1 := rfl

/-- `V = br_cexV` solves the Bellman equation (7.19) of the first counterexample. -/
theorem br_cexV_fixed (h : br_Standing (br_ctrlMDP br_cexModel br_cex_a645.1)) :
    br_T h br_cexV = br_cexV := by
  have : IsMarkovKernel br_cexModel.Q := br_cexModel_markov
  ext ⟨x, z⟩
  have hobj : ∀ a : ↥br_cexModel.A, br_obj (br_ctrlMDP br_cexModel br_cex_a645.1) br_cexV
      ((x, z), a) = br_cexU x a + 1 / 10 * br_cexW a := fun a => by
    rw [br_obj_ctrl_next br_cex_a645]
    change br_cexU x a + 1 / 10 * ∫ z', br_cexV _ ∂(Measure.dirac ()) = _
    rw [integral_dirac]
    rfl
  have hW0 : br_cexW 0 = 0 := by norm_num [br_cexW]
  have hW1 : br_cexW 1 = 35 / 9 := by norm_num [br_cexW, max_def]
  rw [br_T_apply, br_cexV_apply]
  have hx := x.2
  obtain ⟨hx0, hx1⟩ := hx
  have hgr : IsGreatest ((fun a => br_obj (br_ctrlMDP br_cexModel br_cex_a645.1) br_cexV
      ((x, z), a)) '' (br_ctrlMDP br_cexModel br_cex_a645.1).Γ (x, z)) (br_cexW x) := by
    constructor
    · by_cases hk : 2 * (x : ℝ) - 11 / 18 ≤ 0
      · refine ⟨⟨0, le_rfl, zero_le_one⟩, Or.inl rfl, ?_⟩
        dsimp only
        rw [hobj, hW0]
        simp only [br_cexU, br_cexW, max_eq_left hk]
        ring
      · refine ⟨⟨1, zero_le_one, le_rfl⟩, Or.inr rfl, ?_⟩
        dsimp only
        rw [hobj, hW1]
        simp only [br_cexU, br_cexW, max_eq_right (le_of_lt (not_le.1 hk))]
        ring
    · rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [hobj]
      rcases ha with ha | ha
      · rw [ha, hW0]
        simp only [br_cexU, br_cexW]
        nlinarith [le_max_left 0 (2 * (x : ℝ) - 11 / 18)]
      · rw [ha, hW1]
        simp only [br_cexU, br_cexW]
        nlinarith [le_max_right 0 (2 * (x : ℝ) - 11 / 18)]
  exact hgr.csSup_eq

/-- **Counterexample to Theorem 7.3.3 as printed** (Miao, p. 209): the hypotheses the book lists
(Assumptions 5.1.2, 6.4.1–6.4.5, 6.4.8, 6.4.9, 6.4.12, 7.3.1, 7.3.2, 7.3.3) hold and Assumption
6.4.11 fails, and the solution `V` of the Bellman equation (7.19) is not concave in `x`. -/
theorem theorem_7_3_3_counterexample :
    ∃ M : OCModel ℝ ℝ Unit, ∃ h645 : M.Assumption645, IsMarkovKernel M.Q ∧ M.Assumption641 ∧
      M.Assumption642 ∧ M.Assumption643ii ∧ M.Assumption644 ∧ M.Assumption648 ∧
      M.Assumption649 ∧ M.Assumption6412 ∧ Assumption731 M ∧ Assumption732 M ∧
      Assumption733 M ∧ 0 < M.β ∧ M.β < 1 ∧ br_Standing (br_ctrlMDP M h645.1) ∧
      ¬ M.Assumption6411 ∧
      ∀ h : br_Standing (br_ctrlMDP M h645.1), ∀ v : ↥M.X × Unit →ᵇ ℝ, br_T h v = v →
        ¬ ConcaveOn ℝ M.X fun x => br_ext v x () := by
  have hMk := br_cexModel_markov
  have h643 : br_cexModel.Assumption643ii :=
    ⟨inferInstance, inferInstance, fun f _ _ => continuous_of_discreteTopology⟩
  have hS := br_ctrl_standing (br_cexModel.expCont_compact h643.2.2 br_cex_a645)
    (fun _ _ => trivial) br_cex_a644 br_cex_a645 br_cex_a731
  refine ⟨br_cexModel, br_cex_a645, hMk, ⟨convex_Icc 0 1, measurableSet_Icc⟩,
    ⟨convex_Icc 0 1, measurableSet_Icc⟩, h643, br_cex_a644, fun _ _ _ _ _ _ => subset_rfl,
    fun _ _ _ _ => monotoneOn_const, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => le_rfl,
    br_cex_a731, ?_, ?_, by norm_num [br_cexModel], by norm_num [br_cexModel], hS, ?_, ?_⟩
  · intro z a ha x hx y hy hxy
    change br_cexU x a < br_cexU y a
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    obtain ⟨ha0, ha1⟩ := ha
    simp only [br_cexU]
    nlinarith [mul_pos (sub_pos.2 hxy) (sub_pos.2 hxy)]
  · intro z x _ x' _ a _ a' _ θ η hθ hη hs
    simp only [smul_eq_mul]
    exact br_cex_a733 (u := br_cexU) (fun hs => br_cexU_comb hs) hθ hη hs
  · intro h6411
    have := h6411 () 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ 0 (Or.inl rfl) 1
      (Or.inr rfl) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    change (1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * 1 ∈ ({0, 1} : Set ℝ) at this
    norm_num at this
  · intro h v hv hconc
    have hvW : v = br_cexV := br_fixed_unique h ⟨by norm_num [br_ctrlMDP, br_ctrlCP,
      ControlProblem.toMDP, br_cexModel], by norm_num [br_ctrlMDP, br_ctrlCP,
      ControlProblem.toMDP, br_cexModel]⟩ (br_cexV_fixed h) hv
    subst hvW
    have hm : (0 : ℝ) ∈ br_cexModel.X := ⟨le_rfl, zero_le_one⟩
    have hm' : (11 / 18 : ℝ) ∈ br_cexModel.X := ⟨by norm_num, by norm_num⟩
    have := hconc.2 hm hm' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    dsimp only at this
    have hmid : (1 / 2 : ℝ) • (0 : ℝ) + (1 / 2 : ℝ) • (11 / 18 : ℝ) ∈ br_cexModel.X :=
      ⟨by norm_num, by norm_num⟩
    rw [br_ext_mem _ hm, br_ext_mem _ hm', br_ext_mem _ hmid, br_cexV_apply, br_cexV_apply,
      br_cexV_apply] at this
    simp only [smul_eq_mul, br_cexW] at this
    norm_num [max_def] at this

/-- The model of `theorem_7_3_3_policy_counterexample`. -/
noncomputable def br_flatModel : OCModel ℝ ℝ Unit :=
  ⟨Set.Icc 0 1, Set.Icc 0 1, Kernel.const Unit (Measure.dirac ()), fun _ _ => Set.Icc 0 1,
    fun x _ _ _ => x, fun _ x _ _ => 4 * x - x ^ 2 / 2, fun _ _ => 0, 1 / 10, 0⟩

theorem br_flat_a645 : br_flatModel.Assumption645 :=
  ⟨fun _ hx _ _ _ _ => hx, continuous_fst.continuousOn⟩

/-- **Counterexample to the single-valuedness of `G` in Theorem 7.3.3** (Miao, p. 209): all the
book's hypotheses hold (Assumptions 5.1.2, 6.4.1–6.4.5, 6.4.8, 6.4.9, 6.4.12, 7.3.1–7.3.3), and
Assumption 6.4.11 as well, but at every state every feasible action is optimal, so `G` is not
single-valued. Here `φ(x, ·, z, z′)` is not one-to-one. -/
theorem theorem_7_3_3_policy_counterexample :
    ∃ M : OCModel ℝ ℝ Unit, ∃ h645 : M.Assumption645, IsMarkovKernel M.Q ∧ M.Assumption641 ∧
      M.Assumption642 ∧ M.Assumption643ii ∧ M.Assumption644 ∧ M.Assumption648 ∧
      M.Assumption649 ∧ M.Assumption6411 ∧ M.Assumption6412 ∧ Assumption731 M ∧
      Assumption732 M ∧ Assumption733 M ∧ 0 < M.β ∧ M.β < 1 ∧
      br_Standing (br_ctrlMDP M h645.1) ∧ ¬ M.PhiInjA ∧
      ∀ h : br_Standing (br_ctrlMDP M h645.1), ∀ v : ↥M.X × Unit →ᵇ ℝ, br_T h v = v →
        ∀ s, ¬ (br_G (br_ctrlMDP M h645.1) v s).Subsingleton := by
  have hMk : IsMarkovKernel br_flatModel.Q := by
    change IsMarkovKernel (Kernel.const Unit (Measure.dirac ()))
    infer_instance
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, le_rfl, zero_le_one⟩
  have h643 : br_flatModel.Assumption643ii :=
    ⟨inferInstance, inferInstance, fun f _ _ => continuous_of_discreteTopology⟩
  have h644 : br_flatModel.Assumption644 :=
    ⟨fun _ _ _ => subset_rfl, fun s => ⟨isCompact_Icc, isLHC_const hne s,
      isUHC_const hne isCompact_Icc s⟩⟩
  have h731 : Assumption731 br_flatModel := by
    refine ⟨Continuous.continuousOn (by unfold br_flatModel; fun_prop), 10,
      fun x hx _ a _ => ?_⟩
    change |4 * x - x ^ 2 / 2| ≤ 10
    obtain ⟨hx0, hx1⟩ := hx
    rw [abs_le]
    constructor <;> nlinarith
  have hS := br_ctrl_standing (br_flatModel.expCont_compact h643.2.2 br_flat_a645)
    (fun _ _ => trivial) h644 br_flat_a645 h731
  refine ⟨br_flatModel, br_flat_a645, hMk, ⟨convex_Icc 0 1, measurableSet_Icc⟩,
    ⟨convex_Icc 0 1, measurableSet_Icc⟩, h643, h644, fun _ _ _ _ _ _ => subset_rfl,
    fun _ _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ a ha a' ha' θ η hθ hη hs =>
      (convex_Icc 0 1) ha ha' hθ.le hη.le hs, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => le_rfl,
    h731, ?_, ?_, by norm_num [br_flatModel], by norm_num [br_flatModel], hS, ?_, ?_⟩
  · intro z a _ x hx y hy hxy
    change 4 * x - x ^ 2 / 2 < 4 * y - y ^ 2 / 2
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    nlinarith
  · intro z x _ x' _ a _ a' _ θ η hθ hη hs
    change θ * (4 * x - x ^ 2 / 2) + η * (4 * x' - x' ^ 2 / 2) ≤
        4 * (θ • x + η • x') - (θ • x + η • x') ^ 2 / 2 ∧
      (x ≠ x' → θ * (4 * x - x ^ 2 / 2) + η * (4 * x' - x' ^ 2 / 2) <
        4 * (θ • x + η • x') - (θ • x + η • x') ^ 2 / 2)
    simp only [smul_eq_mul]
    have : η = 1 - θ := by linarith
    subst this
    have hq : 4 * (θ * x + (1 - θ) * x') - (θ * x + (1 - θ) * x') ^ 2 / 2 -
        (θ * (4 * x - x ^ 2 / 2) + (1 - θ) * (4 * x' - x' ^ 2 / 2)) =
        θ * (1 - θ) * (x - x') ^ 2 / 2 := by ring
    have hθη : 0 < θ * (1 - θ) := mul_pos hθ hη
    refine ⟨by nlinarith [sq_nonneg (x - x')], fun hne => ?_⟩
    have := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
    nlinarith [mul_pos hθη this]
  · intro hinj
    have := hinj () () 0 ⟨le_rfl, zero_le_one⟩ (show (0 : ℝ) ∈ Set.Icc 0 1 from
      ⟨le_rfl, zero_le_one⟩) (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) rfl
    norm_num at this
  · intro h v _ s hsub
    have : IsMarkovKernel br_flatModel.Q := hMk
    have hobj : ∀ a b : ↥br_flatModel.A, br_obj (br_ctrlMDP br_flatModel br_flat_a645.1) v
        (s, a) = br_obj (br_ctrlMDP br_flatModel br_flat_a645.1) v (s, b) := fun a b => by
      obtain ⟨x, z⟩ := s
      rw [br_obj_ctrl_next br_flat_a645, br_obj_ctrl_next br_flat_a645]
      rfl
    have hmem : ∀ a : ↥br_flatModel.A, a ∈ br_G (br_ctrlMDP br_flatModel br_flat_a645.1) v s :=
      fun a => by
        obtain ⟨b, hb, hval, -⟩ := br_exists_argmax h v s
        refine ⟨a.2, ?_⟩
        rw [← br_T_apply h, hval, hobj a b]
    have := congrArg Subtype.val (hsub (hmem ⟨0, le_rfl, zero_le_one⟩)
      (hmem ⟨1, zero_le_one, le_rfl⟩))
    norm_num at this

end Miao.InfiniteHorizonDP
