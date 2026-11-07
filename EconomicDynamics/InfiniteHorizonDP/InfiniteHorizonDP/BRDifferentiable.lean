/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.BRConcave
import InfiniteHorizonDP.BRInteriorPoints
import InfiniteHorizonDP.SLPEnvelope

/-!
# Theorem 7.3.4: differentiability (the Euler class)

Miao, §7.3.1, pp. 209–210, with `X, A ⊆ ℝⁿ` (`n` arbitrary; the actions are next-period states).

* `Assumption734`: `u(·, z, ·)` is continuously differentiable on `int(X × A)`.
* `Assumption735`: `φ(x, a, z, z′) = a` (the Euler class); then the Bellman equation (7.19) is
  (7.21) (`eq_7_21`).
* `p210_neighborhood`: "there is some open neighborhood `D` of `x₀` such that
  `g(x₀, z₀) ∈ Γ(x, z₀)` for all `x ∈ D`", from `g(x₀, z₀) ∈ int Γ(x₀, z₀)`.
* **Theorem 7.3.4** (`theorem_7_3_4`): `V(·, z₀)` is differentiable at `x₀` with
  `V_x(x₀, z₀) = u_x(x₀, z₀, g(x₀, z₀))` (7.22) (`eq_7_22`), by Benveniste–Scheinkman (SLP
  Theorem 4.10) applied to `W(x) = u(x, z₀, g(x₀, z₀)) + β ∫ V(g(x₀, z₀), z′) Q(z₀, dz′)`.

**Corrections.** (1) The neighborhood claim does not follow from Assumption 6.4.4 (continuity of
`Γ`) as the proof says; it needs `Γ(·, z₀)` convex-valued — Assumption 6.4.11, which is among the
hypotheses — together with lower hemicontinuity (`br_eventually_mem_of_mem_interior`), and only
`g(x₀, z₀) ∈ Γ(x, z₀)` (not `∈ int Γ(x, z₀)`) is needed. (2) The hypotheses omit what makes `V`
and `g` exist: Assumption 7.3.1 (`u` bounded and continuous, in `br_Standing`) and the half of
Assumption 6.4.5 saying that `φ = a` maps `X × A` into `X` (`A ⊆ X`). Strict concavity of `V` and
single-valuedness of `G` come from Theorem 7.3.3 for affine `φ` (`theorem_7_3_3_affine`;
`φ = a` is affine and one-to-one in `a`), so Assumptions 6.4.8, 6.4.9, 6.4.12 and 7.3.2 are not
needed. (3) The book prints `g : X × Z → ℝ`; `g` maps into `A ⊆ ℝⁿ`. (4) "Continuously
differentiable at `x₀`" is proved as differentiability at `x₀` with derivative (7.22); the
derivative `x ↦ u_x(x, z₀, g(x, z₀))` is continuous wherever the interiority conditions hold on
an open set (`g` is continuous by Theorem 7.3.3 and `u_x` by Assumption 7.3.4).
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

variable {E F Z : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace Z]

/-- **Assumption 7.3.4** (Miao, p. 209): for each `z ∈ Z`, `u(·, z, ·)` is continuously
differentiable on the interior of `X × A`. -/
def Assumption734 (M : OCModel E F Z) : Prop :=
  ∀ z, ContDiffOn ℝ 1 (fun p : E × F => M.u 0 p.1 z p.2) (interior (M.X ×ˢ M.A))

/-- **Assumption 7.3.5** (Miao, p. 209): `φ(x, a, z, z′) = a` (the Euler class). -/
def Assumption735 (M : OCModel E E Z) : Prop := ∀ x a z z', M.φ x a z z' = a

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace Z] in
/-- **(7.21)** (Miao, p. 210): under Assumption 7.3.5 the right side of the Bellman equation
(7.19) is `sup_{x′ ∈ Γ(x, z)} u(x, z, x′) + β ∫ V(x′, z′) Q(z, dz′)`. -/
theorem eq_7_21 {M : OCModel E E Z} (h735 : Assumption735 M) (f : E → Z → ℝ) (x : E) (z : Z) :
    M.bellman 0 f x z =
      sSup ((fun x' => M.u 0 x z x' + M.β * ∫ z', f x' z' ∂M.Q z) '' M.Γ x z) := by
  have h' : ∀ x a z z', M.φ x a z z' = a := h735
  rw [OCModel.bellman]
  congr 2
  funext a
  simp only [OCModel.obj, OCModel.cont, h']

omit [NormedSpace ℝ F] [MetricSpace Z] in
/-- `φ = a` is affine and one-to-one in `a`. -/
theorem br_euler_affine {M : OCModel E E Z} (h735 : Assumption735 M) :
    M.PhiAffine ∧ M.PhiInjA :=
  ⟨fun z z' x _ x' _ a _ a' _ θ η _ _ _ => by simp only [h735 _ _ z z'],
    fun z z' x _ a _ a' _ he => by simpa only [h735 _ _ z z'] using he⟩

variable {n : ℕ} {M : OCModel (Fin n → ℝ) (Fin n → ℝ) Z}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Miao, p. 210: **if `g₀ ∈ int Γ(x₀, z₀)`, then `g₀ ∈ Γ(x, z₀)` for all `x ∈ X` near `x₀`**,
because `Γ(·, z₀)` is lower hemicontinuous (Assumption 6.4.4) and convex-valued
(Assumption 6.4.11). -/
theorem p210_neighborhood [MeasurableSpace (Fin n → ℝ)] (h644 : M.Assumption644)
    (h6411 : M.Assumption6411) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M.X) {z₀ : Z} {g₀ : Fin n → ℝ}
    (hg : g₀ ∈ interior (M.Γ x₀ z₀)) :
    ∀ᶠ x in 𝓝 x₀, x ∈ M.X → g₀ ∈ M.Γ x z₀ := by
  set x₀' : ↥M.X := ⟨x₀, hx₀⟩
  have hconv : ∀ x : ↥M.X, Convex ℝ (M.Γ x z₀) := fun x => by
    intro a ha a' ha' θ η hθ hη hs
    rcases hθ.lt_or_eq with hθ' | rfl
    · rcases hη.lt_or_eq with hη' | rfl
      · have := h6411 z₀ x x.2 x x.2 a ha a' ha' θ η hθ' hη' hs
        rwa [← add_smul, hs, one_smul] at this
      · simp only [add_zero] at hs
        subst hs
        simpa using ha
    · simp only [zero_add] at hs
      subst hs
      simpa using ha'
  have hlhc : IsLHC (fun x : ↥M.X => M.Γ x z₀) x₀' := by
    obtain ⟨hne, hl⟩ := (h644.2 ⟨(x₀, z₀), hx₀, Set.mem_univ _⟩).2.1
    refine ⟨hne, fun y hy xs hxs => ?_⟩
    obtain ⟨N, ys, hys, hlim⟩ := hl y hy (fun k => ⟨((xs k : Fin n → ℝ), z₀), (xs k).2,
      Set.mem_univ _⟩) (by
        rw [tendsto_subtype_rng]
        exact ((continuous_subtype_val.tendsto _).comp hxs).prodMk_nhds tendsto_const_nhds)
    exact ⟨N, ys, hys, hlim⟩
  have hseq : ∀ xs : ℕ → ↥M.X, Tendsto xs atTop (𝓝 x₀') → ∀ᶠ k in atTop, g₀ ∈ M.Γ (xs k) z₀ :=
    fun xs hxs => br_eventually_mem_of_mem_interior hconv hlhc hg hxs
  have h1 : ∀ᶠ x : ↥M.X in 𝓝 x₀', g₀ ∈ M.Γ (x : Fin n → ℝ) z₀ :=
    (eventually_iff_seq_eventually (l := 𝓝 x₀') (p := fun x : ↥M.X => g₀ ∈ M.Γ x z₀)).2 hseq
  rw [nhds_subtype, eventually_comap] at h1
  filter_upwards [h1] with x hx hxX
  exact hx ⟨x, hxX⟩ rfl

variable [BorelSpace Z] [SecondCountableTopology Z]

/-- **Theorem 7.3.4 (Differentiability)** (Miao, p. 210), for `X, A ⊆ ℝⁿ`. Under Assumptions
5.1.2, 6.4.1–6.4.4, 6.4.11 and 7.3.3–7.3.5, with Assumptions 6.4.5 (`A ⊆ X`) and 7.3.1 (in
`br_Standing`) added, let `V` solve (7.21) and `g` be its policy function. If `x₀ ∈ int X` and
`g(x₀, z₀) ∈ int Γ(x₀, z₀)`, then `V(·, z₀)` is differentiable at `x₀` with
`V_x(x₀, z₀) = u_x(x₀, z₀, g(x₀, z₀))` (7.22). -/
theorem theorem_7_3_4 [IsMarkovKernel M.Q] [Nonempty ↥M.A] (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h644 : M.Assumption644) (h645 : M.Assumption645)
    (h6411 : M.Assumption6411) (h733 : Assumption733 M) (h734 : Assumption734 M)
    (h735 : Assumption735 M) (h512 : 0 < M.β ∧ M.β < 1) (h : br_Standing (br_ctrlMDP M h645.1))
    {v : ↥M.X × Z →ᵇ ℝ} (hv : br_T h v = v) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ interior M.X) {z₀ : Z}
    (hg : (br_policy h645 v (⟨x₀, interior_subset hx₀⟩, z₀) : Fin n → ℝ) ∈
      interior (M.Γ x₀ z₀)) :
    HasFDerivAt (fun x => br_ext v x z₀)
      (fderiv ℝ (fun x => M.u 0 x z₀ (br_policy h645 v (⟨x₀, interior_subset hx₀⟩, z₀))) x₀)
      x₀ := by
  set x₀' : ↥M.X := ⟨x₀, interior_subset hx₀⟩
  set g₀ := br_policy h645 v (x₀', z₀)
  obtain ⟨haff, hinj⟩ := br_euler_affine h735
  obtain ⟨hconc, hpol⟩ := theorem_7_3_3_affine h641 h642 h644 h645 h6411 h733 haff h512 h hv
  have hG := (hpol hinj).1 (x₀', z₀)
  have hg₀ : g₀ ∈ br_G (br_ctrlMDP M h645.1) v (x₀', z₀) := by rw [hG]; exact rfl
  -- the continuation value does not depend on the current state
  have hnext : ∀ x : ↥M.X, ∀ z', br_next M h645.1 x g₀ z₀ z' = br_next M h645.1 x₀' g₀ z₀ z' :=
    fun x z' => Prod.ext (Subtype.ext (by simp only [br_next, h735 _ _ z₀ z'])) rfl
  set c := M.β * ∫ z', v (br_next M h645.1 x₀' g₀ z₀ z') ∂M.Q z₀
  set W : (Fin n → ℝ) → ℝ := fun x => M.u 0 x z₀ g₀ + c
  have hX : M.X ∈ 𝓝 x₀ := mem_interior_iff_mem_nhds.1 hx₀
  have hA : (g₀ : Fin n → ℝ) ∈ interior M.A :=
    interior_mono (h644.1 x₀ (interior_subset hx₀) z₀) hg
  have hdiff : DifferentiableAt ℝ (fun x => M.u 0 x z₀ g₀) x₀ := by
    have hmem : ((x₀, (g₀ : Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ)) ∈
        interior (M.X ×ˢ M.A) := by rw [interior_prod_eq]; exact ⟨hx₀, hA⟩
    have hd := ((h734 z₀).contDiffAt (isOpen_interior.mem_nhds hmem)).differentiableAt
      one_ne_zero
    have hpair : DifferentiableAt ℝ (fun x : Fin n → ℝ => (x, (g₀ : Fin n → ℝ))) x₀ := by
      fun_prop
    exact hd.comp x₀ hpair
  have hW : HasFDerivAt W (fderiv ℝ (fun x => M.u 0 x z₀ g₀) x₀) x₀ :=
    hdiff.hasFDerivAt.add_const c
  have hvx : ∀ s, v s = br_T h v s := fun s => by rw [hv]
  have heq : W x₀ = br_ext v x₀ z₀ := by
    rw [br_ext_mem v (interior_subset hx₀), hvx]
    have := hg₀.2
    rw [br_obj_ctrl_next h645] at this
    exact this
  have hle : ∀ᶠ x in 𝓝 x₀, W x ≤ br_ext v x z₀ := by
    filter_upwards [p210_neighborhood h644 h6411 (interior_subset hx₀) hg, hX] with x hx hxX
    rw [br_ext_mem v hxX, hvx]
    have := br_obj_le_T h v (s := (⟨x, hxX⟩, z₀)) (a := g₀) (hx hxX)
    rw [br_obj_ctrl_next h645] at this
    simp only [hnext] at this
    exact this
  exact theorem_4_10 (hconc z₀).concaveOn hX hW heq hle

/-- **(7.22)** (Miao, p. 210): `V_x(x₀, z₀) = u_x(x₀, z₀, g(x₀, z₀))`. -/
theorem eq_7_22 [IsMarkovKernel M.Q] [Nonempty ↥M.A] (h641 : M.Assumption641)
    (h642 : M.Assumption642) (h644 : M.Assumption644) (h645 : M.Assumption645)
    (h6411 : M.Assumption6411) (h733 : Assumption733 M) (h734 : Assumption734 M)
    (h735 : Assumption735 M) (h512 : 0 < M.β ∧ M.β < 1) (h : br_Standing (br_ctrlMDP M h645.1))
    {v : ↥M.X × Z →ᵇ ℝ} (hv : br_T h v = v) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ interior M.X) {z₀ : Z}
    (hg : (br_policy h645 v (⟨x₀, interior_subset hx₀⟩, z₀) : Fin n → ℝ) ∈
      interior (M.Γ x₀ z₀)) :
    fderiv ℝ (fun x => br_ext v x z₀) x₀ =
      fderiv ℝ (fun x => M.u 0 x z₀ (br_policy h645 v (⟨x₀, interior_subset hx₀⟩, z₀))) x₀ :=
  (theorem_7_3_4 h641 h642 h644 h645 h6411 h733 h734 h735 h512 h hv hx₀ hg).fderiv

end Miao.InfiniteHorizonDP
