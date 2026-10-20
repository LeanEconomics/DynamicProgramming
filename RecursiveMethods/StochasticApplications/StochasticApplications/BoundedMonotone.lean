/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.BoundedOptimal

/-!
# Bounded returns: monotonicity (Theorems 9.7 and 9.11, Exercises 9.7c and 9.7g)

SLP §9.2, pp. 264–270. Each proof is the book's: by Corollary 1 to the Contraction Mapping
Theorem, it suffices that `T` maps the closed set of functions nondecreasing in the relevant
argument into the strictly increasing ones. The order on `X` (or `Z`) is any partial order —
the book's `ℝˡ` with the coordinatewise order is a special case.

* **Exercise 9.7c** (`ex_9_7c`): with Assumption 9.8 (`F(·, y, z)` strictly increasing),
  Assumption 9.9 (`Γ(·, z)` increasing) and `φ(·, y, z′)` nondecreasing, `v(·, z)` is strictly
  increasing. **Theorem 9.7** (`theorem_9_7`) is the first formulation.
* **Exercise 9.7g** (`ex_9_7g`): with Assumptions 9.13–9.15 (`F(x, y, ·)` strictly increasing,
  `Γ(x, ·)` increasing, `Q` monotone), `v(x, ·)` is strictly increasing. **Correction:** in the
  second formulation the integrand `f[φ(x, y, z′), z′]` must be nondecreasing in `z′`, which needs
  `φ(x, y, ·)` nondecreasing (the solutions manual adds this) *and* `f` nondecreasing in `x`; we
  add the hypotheses of part (c), so that `T` maps the functions nondecreasing in both `x` and
  `z` into those strictly increasing in both. **Theorem 9.11** (`theorem_9_11`) is the first
  formulation, where `φ(x, y, z′) = y` and only monotonicity in `z` is needed.
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (M : Model X Y Z) [IsMarkovKernel M.Q] [OpensMeasurableSpace Z]

/-- A set of bounded continuous functions cut out by pointwise inequalities is closed. -/
theorem isClosed_pointwise_le {S ι : Type*} [TopologicalSpace S] (a b : ι → S) :
    IsClosed {f : S →ᵇ ℝ | ∀ i, f (a i) ≤ f (b i)} := by
  have : {f : S →ᵇ ℝ | ∀ i, f (a i) ≤ f (b i)} = ⋂ i, {f : S →ᵇ ℝ | f (a i) ≤ f (b i)} := by
    ext f; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (continuous_eval_const _) (continuous_eval_const _)

/-- `T` maps functions nondecreasing in `x` to functions strictly increasing in `x`. -/
theorem bellman_strictMono_x [PartialOrder X] (h : BoundedDP M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z')) {f : X × Z →ᵇ ℝ}
    (hf : ∀ z, Monotone fun x => f (x, z)) (z : Z) :
    StrictMono fun x => bellman M h f (x, z) := by
  intro x x' hxx'
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M h f (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h f (x', z)
  have hy' : y ∈ M.Γ (x', z) := h99 x x' z hxx'.le hy
  have hE : expV M f (x, z) y ≤ expV M f (x', z) y :=
    integral_mono (integrable_integrand M h f hy _) (integrable_integrand M h f hy' _)
      fun z' => hf z' (hφx y z' hxx'.le)
  change bellman M h f (x, z) < bellman M h f (x', z)
  rw [hval]
  refine lt_of_lt_of_le ?_ (hmax y hy')
  simp only [rhs]
  exact add_lt_add_of_lt_of_le (h98 x x' y z hxx' hy)
    (mul_le_mul_of_nonneg_left hE h.β_pos.le)

/-- **Exercise 9.7c.** Under §9.2's hypotheses, Assumptions 9.8 and 9.9, and `φ(·, y, z′)`
nondecreasing, the fixed point `v(·, z)` is strictly increasing for each `z`. -/
theorem ex_9_7c [PartialOrder X] (h : BoundedDP M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z')) {v : X × Z →ᵇ ℝ}
    (hv : bellman M h v = v) (z : Z) : StrictMono fun x => v (x, z) := by
  set C' : Set (X × Z →ᵇ ℝ) := {f | ∀ z, Monotone fun x => f (x, z)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := X × Z) (ι := {q : X × X × Z // q.1 ≤ q.2.1})
      (fun q => (q.1.1, q.1.2.2)) (fun q => (q.1.2.1, q.1.2.2))
    convert this using 1
    ext f
    exact ⟨fun hf q => hf q.1.2.2 q.2, fun hf z x x' hxx' => hf ⟨(x, x', z), hxx'⟩⟩
  have hmaps := fun (f : X × Z →ᵇ ℝ) (hf : f ∈ C') =>
    bellman_strictMono_x M h h98 h99 hφx hf
  have hv' := (corollary_1 (S' := C') (S'' := {f | ∀ z, StrictMono fun x => f (x, z)})
    (bellman_contraction M h) hv ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed
    (fun f hf z => (hmaps f hf z).monotone) hmaps).2
  exact hv' z

/-- **Theorem 9.7** (first formulation). Under Assumptions 9.4–9.9, `v(·, z)` is strictly
increasing for each `z`. -/
theorem theorem_9_7 [PartialOrder X] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X)
    (F : X × X × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h98 : ∀ x x' y z, x < x' → y ∈ Γ (x, z) → F (x, y, z) < F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → Γ (x, z) ⊆ Γ (x', z)) {v : X × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) (z : Z) : StrictMono fun x => v (x, z) :=
  ex_9_7c (Model.first Q Γ F β) h h98 h99 (fun _ _ => monotone_const) hv z

omit [IsMarkovKernel M.Q] in
/-- With `Q` monotone, the expected continuation value is nondecreasing in `z` when the integrand
is nondecreasing in `z′`. -/
theorem expV_mono_z [Preorder Z] (h : BoundedDP M) (hQ : IsMonotoneTF M.Q) (f : X × Z →ᵇ ℝ)
    {x : X} {y : Y} {z₁ z₂ : Z} (hy : y ∈ M.Γ (x, z₁)) (hz : z₁ ≤ z₂)
    (hk : Monotone fun z' => f (M.φ (x, y, z'), z')) :
    expV M f (x, z₁) y ≤ expV M f (x, z₂) y :=
  hQ _ (continuous_integrand M h f hy).measurable ⟨‖f‖, fun _ => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _⟩ hk hz

/-- `T` maps functions whose integrands are nondecreasing in `z′` to functions strictly
increasing in `z`. -/
theorem bellman_strictMono_z [Preorder Z] (h : BoundedDP M)
    (h913 : ∀ x y z z', z < z' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x, y, z'))
    (h914 : ∀ x z z', z ≤ z' → M.Γ (x, z) ⊆ M.Γ (x, z')) (hQ : IsMonotoneTF M.Q)
    {f : X × Z →ᵇ ℝ} (hk : ∀ x y, Monotone fun z' => f (M.φ (x, y, z'), z')) (x : X) :
    StrictMono fun z => bellman M h f (x, z) := by
  intro z z' hzz'
  obtain ⟨y, hy, hval, -⟩ := exists_bellman_argmax M h f (x, z)
  obtain ⟨-, -, -, hmax⟩ := exists_bellman_argmax M h f (x, z')
  have hy' : y ∈ M.Γ (x, z') := h914 x z z' hzz'.le hy
  change bellman M h f (x, z) < bellman M h f (x, z')
  rw [hval]
  refine lt_of_lt_of_le ?_ (hmax y hy')
  simp only [rhs]
  exact add_lt_add_of_lt_of_le (h913 x y z z' hzz' hy)
    (mul_le_mul_of_nonneg_left (expV_mono_z M h hQ f hy hzz'.le (hk x y)) h.β_pos.le)

/-- **Theorem 9.11** (first formulation). Under Assumptions 9.4–9.7 and 9.13–9.15, `v(x, ·)` is
strictly increasing for each `x`. -/
theorem theorem_9_11 [PartialOrder Z] (Q : Kernel Z Z) [IsMarkovKernel Q] (Γ : X × Z → Set X)
    (F : X × X × Z → ℝ) (β : ℝ) (h : BoundedDP (Model.first Q Γ F β))
    (h913 : ∀ x y z z', z < z' → y ∈ Γ (x, z) → F (x, y, z) < F (x, y, z'))
    (h914 : ∀ x z z', z ≤ z' → Γ (x, z) ⊆ Γ (x, z')) (hQ : IsMonotoneTF Q) {v : X × Z →ᵇ ℝ}
    (hv : bellman (Model.first Q Γ F β) h v = v) (x : X) : StrictMono fun z => v (x, z) := by
  set M := Model.first Q Γ F β
  set C' : Set (X × Z →ᵇ ℝ) := {f | ∀ x, Monotone fun z => f (x, z)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := X × Z) (ι := {q : X × Z × Z // q.2.1 ≤ q.2.2})
      (fun q => (q.1.1, q.1.2.1)) (fun q => (q.1.1, q.1.2.2))
    convert this using 1
    ext f
    exact ⟨fun hf q => hf q.1.1 q.2, fun hf x z z' hzz' => hf ⟨(x, z, z'), hzz'⟩⟩
  have hmaps := fun (f : X × Z →ᵇ ℝ) (hf : f ∈ C') =>
    bellman_strictMono_z M h h913 h914 hQ (f := f) (fun _ y => hf y)
  have hv' := (corollary_1 (S' := C') (S'' := {f | ∀ x, StrictMono fun z => f (x, z)})
    (bellman_contraction M h) hv ⟨0, fun _ _ _ _ => le_rfl⟩ hclosed
    (fun f hf x => (hmaps f hf x).monotone) hmaps).2
  exact hv' x

/-- **Exercise 9.7g** (corrected). Under §9.2's hypotheses, Assumptions 9.13–9.15, the
hypotheses of part (c), and `φ(x, y, ·)` nondecreasing, `v(x, ·)` is strictly increasing for each
`x` (and `v(·, z)` for each `z`). -/
theorem ex_9_7g [PartialOrder X] [PartialOrder Z] (h : BoundedDP M)
    (h98 : ∀ x x' y z, x < x' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x', y, z))
    (h99 : ∀ x x' z, x ≤ x' → M.Γ (x, z) ⊆ M.Γ (x', z))
    (hφx : ∀ y z', Monotone fun x => M.φ (x, y, z'))
    (h913 : ∀ x y z z', z < z' → y ∈ M.Γ (x, z) → M.F (x, y, z) < M.F (x, y, z'))
    (h914 : ∀ x z z', z ≤ z' → M.Γ (x, z) ⊆ M.Γ (x, z')) (hQ : IsMonotoneTF M.Q)
    (hφz : ∀ x y, Monotone fun z' => M.φ (x, y, z')) {v : X × Z →ᵇ ℝ}
    (hv : bellman M h v = v) :
    (∀ x, StrictMono fun z => v (x, z)) ∧ ∀ z, StrictMono fun x => v (x, z) := by
  set C' : Set (X × Z →ᵇ ℝ) := {f | Monotone (f : X × Z → ℝ)}
  have hclosed : IsClosed C' := by
    have := isClosed_pointwise_le (S := X × Z) (ι := {q : (X × Z) × (X × Z) // q.1 ≤ q.2})
      (fun q => q.1.1) (fun q => q.1.2)
    convert this using 1
    ext f
    exact ⟨fun hf q => hf q.2, fun hf p p' hpp' => hf ⟨(p, p'), hpp'⟩⟩
  have hjoint : ∀ f : X × Z →ᵇ ℝ, (∀ x, StrictMono fun z => f (x, z)) →
      (∀ z, StrictMono fun x => f (x, z)) → Monotone (f : X × Z → ℝ) := by
    intro f hz hx p p' hpp'
    exact ((hx p.2).monotone hpp'.1).trans ((hz p'.1).monotone hpp'.2)
  have hmaps : ∀ f ∈ C', bellman M h f ∈
      {g : X × Z →ᵇ ℝ | (∀ x, StrictMono fun z => g (x, z)) ∧
        ∀ z, StrictMono fun x => g (x, z)} := fun f hf =>
    ⟨bellman_strictMono_z M h h913 h914 hQ
        (fun x y z₁ z₂ hz => hf (Prod.mk_le_mk.2 ⟨hφz x y hz, hz⟩)),
      bellman_strictMono_x M h h98 h99 hφx
        fun z x x' hxx' => hf (Prod.mk_le_mk.2 ⟨hxx', le_rfl⟩)⟩
  exact (corollary_1 (S' := C') (bellman_contraction M h) hv ⟨0, fun _ _ _ => le_rfl⟩ hclosed
    (fun f hf => hjoint _ (hmaps f hf).1 (hmaps f hf).2) hmaps).2

end StokeyLucasPrescott.StochasticApplications
