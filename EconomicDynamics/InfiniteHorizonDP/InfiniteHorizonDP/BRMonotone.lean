/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.BRControl

/-!
# Theorem 7.3.2: monotonicity

Miao, §7.3.1, p. 208. Under Assumptions 6.4.8 (`Γ(·, z)` increasing), 6.4.9 (`φ(·, a, z, z′)`
increasing) and 7.3.2 (`u(·, z, a)` strictly increasing), the solution `V(·, z)` of the Bellman
equation (7.19) is strictly increasing on `X`.

The proof is the book's: the set `C′(S)` of bounded continuous functions increasing in `x` is
closed (`br_isClosed_mono`) and `T` maps `C′(S)` into the strictly increasing functions `C″(S)`
(`br_T_strictMono`, the argument of Theorem 6.4.2: with `a*` attaining `(Tf)(x, z)` and
`x < x′`, `a* ∈ Γ(x′, z)` and
`(Tf)(x, z) = u(x, z, a*) + β E f < u(x′, z, a*) + β E f′ ≤ (Tf)(x′, z)`), so the Closed
Subspace Theorem (`br_corollary_1`) puts the fixed point in `C″(S)`.

The order on `E` is any partial order (componentwise on `ℝ^{n_x}`), and `X` carries the induced
order. The standing hypotheses `br_Standing` of the control process carry Assumptions 6.4.3–6.4.5
and 7.3.1 (`br_ctrl_standing`); Assumptions 6.4.1–6.4.2 are not used. The book's "increasing"
(for `C′`) is read as nondecreasing, as the closedness of `C′` requires.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

variable {E F Z : Type*} [MeasurableSpace Z] [MetricSpace E] [MetricSpace F] [MetricSpace Z]

/-- **Assumption 7.3.2** (Miao, p. 208): for each `(z, a) ∈ Z × A`, `u(·, z, a) : X → ℝ` is
strictly increasing. -/
def Assumption732 [Preorder E] (M : OCModel E F Z) : Prop :=
  ∀ z, ∀ a ∈ M.A, StrictMonoOn (fun x => M.u 0 x z a) M.X

/-- The sets of bounded continuous functions with `f(a_i) ≤ f(b_i)` (when `p i`) are closed. -/
theorem br_isClosed_le {X ι : Type*} [TopologicalSpace X] (p : ι → Prop) (a b : ι → X) :
    IsClosed {f : X →ᵇ ℝ | ∀ i, p i → f (a i) ≤ f (b i)} := by
  convert br_isClosed_comb p (fun _ => 1) (fun _ => 0) a a b using 1
  ext f
  simp only [Set.mem_ofPred_eq, one_mul, zero_mul, add_zero]

omit [MeasurableSpace Z] in
/-- The set `C′(S)` of bounded continuous functions increasing in `x` is closed (Miao, p. 208). -/
theorem br_isClosed_mono {X : Set E} [Preorder E] :
    IsClosed {f : ↥X × Z →ᵇ ℝ | ∀ z, Monotone fun x : ↥X => f (x, z)} := by
  convert br_isClosed_le (X := ↥X × Z) (ι := ↥X × ↥X × Z) (fun i => i.1 ≤ i.2.1)
    (fun i => (i.1, i.2.2)) (fun i => (i.2.1, i.2.2)) using 1
  ext f
  exact ⟨fun hf i hi => hf i.2.2 hi, fun hf z x x' hxx' => hf (x, x', z) hxx'⟩

variable [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F] [BorelSpace Z]
  [SecondCountableTopology F] [SecondCountableTopology Z] {M : OCModel E F Z}

/-- The integrands `z′ ↦ f(φ(x, a, z, z′), z′)` of bounded continuous `f` are integrable. -/
theorem br_integrable_next [IsMarkovKernel M.Q] (h645 : M.Assumption645) (f : ↥M.X × Z →ᵇ ℝ)
    (x : ↥M.X) (a : ↥M.A) (z : Z) :
    Integrable (fun z' => f (br_next M h645.1 x a z z')) (M.Q z) :=
  integrable_of_abs_le (f.continuous.measurable.comp (br_measurable_next h645 x a z)) fun _ => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _

/-- The objective of (7.20): `u(x, z, a) + β ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)`. -/
theorem br_obj_ctrl_next [IsMarkovKernel M.Q] (h645 : M.Assumption645) (f : ↥M.X × Z →ᵇ ℝ)
    (x : ↥M.X) (z : Z) (a : ↥M.A) :
    br_obj (br_ctrlMDP M h645.1) f ((x, z), a) =
      M.u 0 x z a + M.β * ∫ z', f (br_next M h645.1 x a z z') ∂M.Q z := by
  simp only [br_obj]
  rw [br_integral_ctrl h645 f.continuous.measurable]
  rfl

/-- **`T` maps `C′(S)` into `C″(S)`** (Miao, p. 208, "by an argument similar to that in the proof
of Theorem 6.4.2"): if `f(·, z)` is increasing for every `z`, `(Tf)(·, z)` is strictly
increasing. -/
theorem br_T_strictMono [IsMarkovKernel M.Q] [PartialOrder E] (h645 : M.Assumption645)
    (h648 : M.Assumption648) (h649 : M.Assumption649) (h732 : Assumption732 M) (hβ : 0 ≤ M.β)
    (h : br_Standing (br_ctrlMDP M h645.1)) {f : ↥M.X × Z →ᵇ ℝ}
    (hf : ∀ z, Monotone fun x : ↥M.X => f (x, z)) (z : Z) :
    StrictMono fun x : ↥M.X => br_T h f (x, z) := by
  intro x x' hxx'
  obtain ⟨a, ha, hval, -⟩ := br_exists_argmax h f (x, z)
  have ha' : a ∈ (br_ctrlMDP M h645.1).Γ (x', z) := h648 z x x.2 x' x'.2 hxx'.le ha
  change br_T h f (x, z) < br_T h f (x', z)
  rw [hval]
  refine lt_of_lt_of_le ?_ (br_obj_le_T h f ha')
  rw [br_obj_ctrl_next h645, br_obj_ctrl_next h645]
  have hu : M.u 0 x z a < M.u 0 x' z a := h732 z a a.2 x.2 x'.2 (Subtype.coe_lt_coe.2 hxx')
  have hc : ∫ z', f (br_next M h645.1 x a z z') ∂M.Q z ≤
      ∫ z', f (br_next M h645.1 x' a z z') ∂M.Q z := by
    refine integral_mono (br_integrable_next h645 f x a z) (br_integrable_next h645 f x' a z)
      fun z' => hf z' ?_
    exact Subtype.mk_le_mk.2 (h649 a a.2 z z' x.2 x'.2 hxx'.le)
  linarith [mul_le_mul_of_nonneg_left hc hβ]

/-- **Theorem 7.3.2 (Monotonicity)** (Miao, p. 208). Under Assumptions 5.1.2, 6.4.3–6.4.5 and
7.3.1 (`br_Standing`, given by `br_ctrl_standing`), 6.4.8, 6.4.9 and 7.3.2, the solution `V` of
the Bellman equation (7.19) has `V(·, z) : X → ℝ` strictly increasing for each `z ∈ Z`. -/
theorem theorem_7_3_2 [IsMarkovKernel M.Q] [PartialOrder E] (h645 : M.Assumption645)
    (h648 : M.Assumption648) (h649 : M.Assumption649) (h732 : Assumption732 M)
    (h512 : 0 < M.β ∧ M.β < 1) (h : br_Standing (br_ctrlMDP M h645.1)) {v : ↥M.X × Z →ᵇ ℝ}
    (hv : br_T h v = v) (z : Z) : StrictMono fun x : ↥M.X => v (x, z) := by
  have hmaps : Set.MapsTo (br_T h) {f | ∀ z, Monotone fun x : ↥M.X => f (x, z)}
      {f | ∀ z, StrictMono fun x : ↥M.X => f (x, z)} := fun f hf =>
    br_T_strictMono h645 h648 h649 h732 h512.1.le h hf
  have h0 : (0 : ↥M.X × Z →ᵇ ℝ) ∈ {f | ∀ z, Monotone fun x : ↥M.X => f (x, z)} :=
    fun _ _ _ _ => le_rfl
  exact (br_corollary_1 (br_T_contraction h h512) hv ⟨0, h0⟩
    br_isClosed_mono (fun f hf z => (hmaps hf z).monotone) hmaps).2 z

end Miao.InfiniteHorizonDP
