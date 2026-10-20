/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.Lemma95
import StochasticApplications.Contraction
import StochasticApplications.Maximum

/-!
# Bounded returns: Theorem 9.6 and Exercise 9.7b

SLP §9.2, pp. 259–264 and 268–270. The operator
`(Tf)(x, z) = sup_{y ∈ Γ(x, z)} {F(x, y, z) + β ∫ f[φ(x, y, z′), z′] Q(z, dz′)}` (`bellman`) on
the bounded continuous functions `C(S)`, `S = X × Z`, for the second formulation; the first
formulation is `φ(x, y, z′) = y` (`Model.first`), so one proof covers Theorem 9.6 and
Exercise 9.7b.

`BoundedDP` collects the hypotheses: Assumption 9.6 (`Γ` nonempty, compact-valued and
continuous), Assumption 9.7 (`F` bounded and continuous on the graph `A`, `0 < β < 1`),
Assumption 9.17 (`φ` continuous on `D × Z`), and the conclusion of Lemma 9.5′ — that
`(x, y, z) ↦ ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on `D × Z` for bounded continuous `f`
(`ContExp`). It follows from Assumption 9.5 by Lemma 9.5′ (`contExp_of_preservesBC`), and in the
first formulation from Assumption 9.5 on `X × Z` by Lemma 9.5 (`contExp_first`). The metric
spaces `X`, `Y`, `Z` stand for the book's Borel sets in Euclidean spaces (Assumptions 9.4 and
9.16; convexity is used from Theorem 9.8 on).

* `bellman_mono`, `bellman_add_const`, `blackwell`: `T` is monotone and discounts, so it is a
  contraction of modulus `β` (Theorem 3.3).
* `ex_9_7b`: `T` has a unique fixed point `v ∈ C(S)`, `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the policy
  correspondence `G` is nonempty, compact-valued and u.h.c.; `theorem_9_6` is the first
  formulation.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- `D = {(x, y) : y ∈ Γ(x, z) for some z}`, the domain of the law of motion. -/
def domD (M : Model X Y Z) : Set (X × Y) := {w | ∃ z, w.2 ∈ M.Γ (w.1, z)}

/-- The graph `A = {(x, y, z) : y ∈ Γ(x, z)}`. -/
def graphA (M : Model X Y Z) : Set (X × Y × Z) := {p | p.2.1 ∈ M.Γ (p.1, p.2.2)}

/-- The conclusion of Lemma 9.5′: `(x, y, z) ↦ ∫ f[φ(x, y, z′), z′] Q(z, dz′)` is continuous on
`D × Z` for every bounded continuous `f`. -/
def ContExp (M : Model X Y Z) : Prop :=
  ∀ f : X × Z → ℝ, Continuous f → (∃ B, ∀ p, |f p| ≤ B) →
    ContinuousOn (fun q : (X × Y) × Z => ∫ z', f (M.φ (q.1.1, q.1.2, z'), z') ∂M.Q q.2)
      (domD M ×ˢ univ)

/-- The hypotheses of §9.2: Assumptions 9.6, 9.7 and 9.17, and Lemma 9.5′. -/
structure BoundedDP (M : Model X Y Z) : Prop where
  nonempty : ∀ s, (M.Γ s).Nonempty
  compact : ∀ s, IsCompact (M.Γ s)
  lhc : ∀ s, IsLHC M.Γ s
  uhc : ∀ s, IsUHC M.Γ s
  contF : ContinuousOn M.F (graphA M)
  bddF : ∃ B, ∀ p ∈ graphA M, |M.F p| ≤ B
  β_pos : 0 < M.β
  β_lt : M.β < 1
  contφ : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ)
  contExp : ContExp M

omit [MetricSpace X] [MetricSpace Y] [MetricSpace Z] in
theorem mem_domD (M : Model X Y Z) {s : X × Z} {y : Y} (hy : y ∈ M.Γ s) : (s.1, y) ∈ domD M :=
  ⟨s.2, hy⟩

/-- **Lemma 9.5′ gives `ContExp`** under Assumptions 9.5 (on `D × Z`) and 9.17. -/
theorem contExp_of_preservesBC (M : Model X Y Z)
    (hφ : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ))
    (hQ : PreservesBC (domD M) M.Q) : ContExp M := fun _ hf ⟨_, hB⟩ =>
  lemma_9_5' (domD M) hφ M.Q hQ hf hB

/-- In the first formulation, `ContExp` follows from Assumption 9.5 on `X × Z` (Lemma 9.5). -/
theorem contExp_first (Q : Kernel Z Z) (Γ : X × Z → Set X) (F : X × X × Z → ℝ) (β : ℝ)
    (hQ : PreservesBC X Q) : ContExp (Model.first Q Γ F β) := fun f hf hB =>
  ((hQ f hf hB).comp (continuous_fst.snd.prodMk continuous_snd)).continuousOn

variable (M : Model X Y Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- The objective `(s, y) ↦ F(x, y, z) + β ∫ f[φ(x, y, z′), z′] Q(z, dz′)` on the graph. -/
noncomputable def objG (f : X × Z → ℝ) (p : (X × Z) × Y) : ℝ := rhs M f p.1 p.2

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
theorem continuousOn_objG (h : BoundedDP M) (f : X × Z →ᵇ ℝ) :
    ContinuousOn (objG M f) (graph M.Γ) := by
  have hF : ContinuousOn (fun p : (X × Z) × Y => M.F (p.1.1, p.2, p.1.2)) (graph M.Γ) :=
    h.contF.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd)).continuousOn
      fun p hp => hp
  have hE : ContinuousOn (fun p : (X × Z) × Y => expV M f p.1 p.2) (graph M.Γ) :=
    (h.contExp f f.continuous ⟨‖f‖, fun p => f.norm_coe_le_norm p⟩).comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd).continuousOn
      fun p hp => ⟨mem_domD M hp, mem_univ _⟩
  exact hF.add (continuousOn_const.mul hE)

omit [IsMarkovKernel M.Q] [OpensMeasurableSpace Z] in
/-- The integrand `z′ ↦ f[φ(x, y, z′), z′]` is continuous for `y ∈ Γ(x, z)`. -/
theorem continuous_integrand (h : BoundedDP M) (f : X × Z →ᵇ ℝ) {s : X × Z} {y : Y}
    (hy : y ∈ M.Γ s) : Continuous fun z' => f (M.φ (s.1, y, z'), z') := by
  have hφ : Continuous fun z' : Z => M.φ (s.1, y, z') :=
    h.contφ.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨mem_domD M hy, mem_univ _⟩
  exact f.continuous.comp (hφ.prodMk continuous_id)

theorem integrable_integrand (h : BoundedDP M) (f : X × Z →ᵇ ℝ) {s : X × Z} {y : Y}
    (hy : y ∈ M.Γ s) (z : Z) : Integrable (fun z' => f (M.φ (s.1, y, z'), z')) (M.Q z) :=
  integrable_of_abs_le (continuous_integrand M h f hy).measurable fun _ =>
    by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _

omit [MetricSpace Y] [OpensMeasurableSpace Z] in
theorem abs_expV_le (f : X × Z →ᵇ ℝ) (s : X × Z) (y : Y) : |expV M f s y| ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := M.Q s.2) (C := ‖f‖)
    (f := fun z' => f (M.φ (s.1, y, z'), z'))
    (Eventually.of_forall fun z' => f.norm_coe_le_norm _)
  rw [expV]
  simpa [Real.norm_eq_abs, measureReal_def] using this

omit [OpensMeasurableSpace Z] in
theorem bound_maxValueG (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (s : X × Z) :
    ‖maxValue (objG M f) M.Γ s‖ ≤ h.bddF.choose + M.β * ‖f‖ := by
  obtain ⟨y, hy, hval, -⟩ := exists_argmax (continuousOn_objG M h f) (h.compact s) (h.nonempty s)
  rw [← hval, Real.norm_eq_abs, objG, rhs]
  refine (abs_add_le _ _).trans (add_le_add (h.bddF.choose_spec (s.1, y, s.2) hy) ?_)
  rw [abs_mul, abs_of_pos h.β_pos]
  exact mul_le_mul_of_nonneg_left (abs_expV_le M f s y) h.β_pos.le

/-- The operator `T` on `C(S)` (Exercise 9.7b; Theorem 9.6 when `φ(x, y, z′) = y`): `Tf` is
bounded and continuous by the Theorem of the Maximum. -/
noncomputable def bellman (h : BoundedDP M) (f : X × Z →ᵇ ℝ) : X × Z →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => maxValue (objG M f) M.Γ s)
    (theorem_3_6 (continuousOn_objG M h f) h.compact h.lhc h.uhc).1
    (h.bddF.choose + M.β * ‖f‖) (bound_maxValueG M h f)

omit [OpensMeasurableSpace Z] in
theorem bellman_apply (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (s : X × Z) :
    bellman M h f s = maxValue (objG M f) M.Γ s := rfl

omit [OpensMeasurableSpace Z] in
/-- `Tf(s) = F(x, y, z) + β ∫ f[φ(x, y, z′), z′] Q(z, dz′)` at a maximizer `y`. -/
theorem exists_bellman_argmax (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (s : X × Z) :
    ∃ y ∈ M.Γ s, bellman M h f s = rhs M f s y ∧ ∀ y' ∈ M.Γ s, rhs M f s y' ≤ bellman M h f s := by
  obtain ⟨y, hy, hval, hmax⟩ := exists_argmax (continuousOn_objG M h f) (h.compact s)
    (h.nonempty s)
  exact ⟨y, hy, hval.symm, fun y' hy' => (hmax y' hy').trans_eq hval⟩

/-- `T` is monotone (Theorem 3.3a). -/
theorem bellman_mono (h : BoundedDP M) {f g : X × Z →ᵇ ℝ} (hfg : f ≤ g) :
    bellman M h f ≤ bellman M h g := fun s => by
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M h f s
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h g s
  change bellman M h f s ≤ bellman M h g s
  rw [hval]
  refine le_trans ?_ (hmax y hy)
  have hE : expV M f s y ≤ expV M g s y :=
    integral_mono (integrable_integrand M h f hy _) (integrable_integrand M h g hy _)
      fun z' => hfg _
  simp only [rhs]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE h.β_pos.le)

theorem expV_add_const (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (a : ℝ) {s : X × Z} {y : Y}
    (hy : y ∈ M.Γ s) : expV M ⇑(f + const (X × Z) a) s y = expV M f s y + a := by
  have heq : ∀ z', (f + const (X × Z) a) (M.φ (s.1, y, z'), z') =
      f (M.φ (s.1, y, z'), z') + a := fun _ => rfl
  simp only [expV, heq]
  rw [integral_add (integrable_integrand M h f hy _) (integrable_const a)]
  simp

/-- `T(f + a) = Tf + βa` (discounting, Theorem 3.3b, with equality). -/
theorem bellman_add_const (h : BoundedDP M) (f : X × Z →ᵇ ℝ) (a : ℝ) :
    bellman M h (f + const (X × Z) a) = bellman M h f + const (X × Z) (M.β * a) := by
  ext s
  obtain ⟨y, hy, hval, hmax⟩ := exists_bellman_argmax M h f s
  obtain ⟨y', hy', hval', hmax'⟩ := exists_bellman_argmax M h (f + const (X × Z) a) s
  simp only [BoundedContinuousFunction.add_apply, const_apply]
  have e1 := expV_add_const M h f a hy
  have e2 := expV_add_const M h f a hy'
  have i1 := hmax y' hy'
  have i2 := hmax' y hy
  simp only [rhs] at hval hval' i1 i2
  rw [e1] at i2
  rw [e2] at hval'
  refine le_antisymm ?_ ?_
  · rw [hval']; nlinarith
  · rw [hval]; nlinarith

/-- **Blackwell's sufficient conditions** (Theorem 3.3) on the bounded continuous functions on
any topological space. -/
theorem blackwell {S : Type*} [TopologicalSpace S] {T : (S →ᵇ ℝ) → (S →ᵇ ℝ)} {β : ℝ}
    (hβ : 0 ≤ β) (hmono : ∀ f g, f ≤ g → T f ≤ T g)
    (hdisc : ∀ f a, 0 ≤ a → T (f + const S a) ≤ T f + const S (β * a)) (f g : S →ᵇ ℝ) :
    dist (T f) (T g) ≤ β * dist f g := by
  have hle : ∀ f g : S →ᵇ ℝ, f ≤ g + const S (dist f g) := fun f g x => by
    change f x ≤ (g + const S (dist f g)) x
    rw [BoundedContinuousFunction.add_apply, const_apply]
    have := dist_coe_le_dist (f := f) (g := g) x
    rw [Real.dist_eq] at this
    linarith [le_abs_self (f x - g x)]
  have h1 : ∀ f g : S →ᵇ ℝ, ∀ x, T f x ≤ T g x + β * dist f g := fun f g x => by
    have : T f x ≤ (T g + const S (β * dist f g)) x :=
      (hmono _ _ (hle f g)).trans (hdisc g _ dist_nonneg) x
    rwa [BoundedContinuousFunction.add_apply, const_apply] at this
  refine (dist_le (mul_nonneg hβ dist_nonneg)).2 fun x => ?_
  rw [Real.dist_eq, abs_le]
  have a := h1 f g x
  have b := h1 g f x
  rw [dist_comm] at b
  constructor <;> linarith

/-- `T` is a contraction of modulus `β`. -/
theorem bellman_contraction (h : BoundedDP M) : IsContraction (bellman M h) M.β :=
  ⟨h.β_pos, h.β_lt, blackwell h.β_pos.le (fun _ _ => bellman_mono M h)
    (fun f a _ => (bellman_add_const M h f a).le)⟩

omit [OpensMeasurableSpace Z] in
/-- At a fixed point, the policy correspondence `G` is the argmax correspondence of `T`. -/
theorem policy_eq_argmax (h : BoundedDP M) {v : X × Z →ᵇ ℝ} (hv : bellman M h v = v) :
    policy M v = argmax (objG M v) M.Γ := by
  funext s
  ext y
  change y ∈ M.Γ s ∧ v s = rhs M v s y ↔ y ∈ M.Γ s ∧ objG M v (s, y) = maxValue (objG M v) M.Γ s
  rw [← bellman_apply M h, hv, objG, eq_comm]

/-- **Exercise 9.7b** (Theorem 9.6 for the second formulation). `T : C(S) → C(S)` has a unique
fixed point `v`, `‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and the policy correspondence `G` is nonempty,
compact-valued and u.h.c. -/
theorem ex_9_7b (h : BoundedDP M) :
    ∃ v : X × Z →ᵇ ℝ, bellman M h v = v ∧ (∀ w, bellman M h w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellman M h)^[n] v₀) v ≤ M.β ^ n * dist v₀ v) ∧
      ∀ s, (policy M v s).Nonempty ∧ IsCompact (policy M v s) ∧ IsUHC (policy M v) s := by
  obtain ⟨v, hv, huniq, hrate⟩ := theorem_3_2 (bellman_contraction M h)
  refine ⟨v, hv, huniq, hrate, ?_⟩
  rw [policy_eq_argmax M h hv]
  exact (theorem_3_6 (continuousOn_objG M h v) h.compact h.lhc h.uhc).2

/-- **Theorem 9.6** (first formulation). Under Assumptions 9.4–9.7 — with Assumption 9.5 in the
form `M : C(X × Z) → C(X × Z)` (Lemma 9.5) — `T` has a unique fixed point `v ∈ C(S)`,
`‖Tⁿv₀ − v‖ ≤ βⁿ‖v₀ − v‖`, and `G` is nonempty, compact-valued and u.h.c. -/
theorem theorem_9_6 (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X) (F : X × X × Z → ℝ)
    (β : ℝ) (hΓne : ∀ s, (Γ s).Nonempty) (hΓc : ∀ s, IsCompact (Γ s)) (hΓl : ∀ s, IsLHC Γ s)
    (hΓu : ∀ s, IsUHC Γ s) (hF : ContinuousOn F (graphA (Model.first Q Γ F β)))
    (hFb : ∃ B, ∀ p ∈ graphA (Model.first Q Γ F β), |F p| ≤ B) (hβ : 0 < β) (hβ1 : β < 1)
    (hQ : PreservesBC X Q) :
    ∃ h : BoundedDP (Model.first Q Γ F β), ∃ v : X × Z →ᵇ ℝ,
      bellman (Model.first Q Γ F β) h v = v ∧
      (∀ w, bellman (Model.first Q Γ F β) h w = w → w = v) ∧
      (∀ v₀ (n : ℕ), dist ((bellman (Model.first Q Γ F β) h)^[n] v₀) v ≤ β ^ n * dist v₀ v) ∧
      ∀ s, (policy (Model.first Q Γ F β) v s).Nonempty ∧
        IsCompact (policy (Model.first Q Γ F β) v s) ∧
        IsUHC (policy (Model.first Q Γ F β) v) s := by
  have h : BoundedDP (Model.first Q Γ F β) :=
    ⟨hΓne, hΓc, hΓl, hΓu, hF, hFb, hβ, hβ1, continuous_fst.snd.continuousOn,
      contExp_first Q Γ F β hQ⟩
  exact ⟨h, ex_9_7b (Model.first Q Γ F β) h⟩

end StokeyLucasPrescott.StochasticApplications
