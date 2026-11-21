/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.BRContraction
import InfiniteHorizonDP.IHVerification
import InfiniteHorizonDP.SLPMaximum
import InfiniteHorizonDP.SLPLemma95

/-!
# Bounded rewards: the Bellman operator and Theorem 7.2.1

Miao, §7.2, pp. 204–205. The Markov decision model `(S, 𝒮), (A, 𝒜), Γ, P, u, β` of Chapter 5
(`MDP`), stationary (`P = P 0`, `u = u 0`), with `S` and `A` metric spaces.

* `Assumption721`, `Assumption722`, `Assumption723`: Assumptions 7.2.1–7.2.3 (`u` bounded and
  continuous; `Γ` nonempty, compact-valued and continuous; `∫ f(s′) P(s, a; ds′)` continuous in
  `(s, a)` for bounded continuous `f`). `br_Standing` collects them with `P` a stochastic kernel.
* `br_obj M f (s, a) = u(s, a) + β ∫ f(s′) P(s, a; ds′)` and the **Bellman operator**
  `br_T h : C(S) → C(S)` of (7.16), `(Tf)(s) = max_{a ∈ Γ(s)} br_obj M f (s, a)` (`eq_7_16`);
  `Tf` is bounded, and continuous by the Theorem of the Maximum (SLP Theorem 3.6); the maximum
  is attained (`br_exists_argmax`).
* `br_T_mono`, `br_T_add_const`, `br_T_contraction`: Blackwell's conditions, so `T` is a
  contraction of modulus `β` (Assumption 5.1.2).
* `br_bellman_iff`: for `f ∈ C(S)`, `f` solves the Bellman equation (7.2) of §7.1 (`ih_Bellman`,
  with the extended integral) iff `Tf = f`; `br_ih_G_eq`: at a fixed point the policy
  correspondence `G` of §7.1 (`ih_G`) is the argmax correspondence `br_G`.
* **Theorem 7.2.1** (`theorem_7_2_1`): the Bellman equation (7.2) has exactly one solution
  `V ∈ C(S)`, and `G` is nonempty, compact-valued and upper hemicontinuous.

**Departures and misprints.** (7.16) is printed with the integral against `dz′` and the text says
"the Bellman equation (7.19)": the integral is against `ds′` and the equation is (7.2). The sup
norm is printed `sup_{s ∈ X}` (read `S`), and "`Tf` is continuous in `(x, z)`" means continuous
in `s` (`S` is general here). Assumptions 6.4.1–6.4.2 (convex Borel `S`, `A`) are not used: `S`
and `A` are any metric spaces, with any σ-algebras for which the open sets of `S` are measurable.
Only `0 < β < 1` from Assumption 5.1.2 is used, and Assumption 7.2.3 is used only on `C(S)`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

variable {S A : Type*} [MetricSpace S] [MetricSpace A] [MeasurableSpace S] [MeasurableSpace A]

/-- **Assumption 7.2.1** (Miao, p. 204): the reward function `u : S × A → ℝ` is bounded and
continuous. -/
def Assumption721 (M : MDP S A) : Prop := Continuous (M.u 0) ∧ ∃ B, ∀ p, |M.u 0 p| ≤ B

/-- **Assumption 7.2.2** (Miao, p. 204): `Γ : S → A` is nonempty, compact-valued and continuous
(`IsLHC` includes nonemptiness). -/
def Assumption722 (M : MDP S A) : Prop := ∀ s, IsCompact (M.Γ s) ∧ IsLHC M.Γ s ∧ IsUHC M.Γ s

/-- **Assumption 7.2.3** (Miao, p. 204): `∫ f(s′) P(s, a; ds′)` is continuous in `(s, a)` for
every bounded continuous `f : S → ℝ`. -/
def Assumption723 (M : MDP S A) : Prop :=
  ∀ f : S → ℝ, Continuous f → (∃ B, ∀ s, |f s| ≤ B) →
    Continuous fun p : S × A => ∫ s', f s' ∂M.P 0 p

/-- The standing hypotheses of §7.2: `P` is a stochastic kernel and Assumptions 7.2.1–7.2.3
hold. -/
structure br_Standing (M : MDP S A) : Prop where
  markov : M.IsMarkov
  a721 : Assumption721 M
  a722 : Assumption722 M
  a723 : Assumption723 M

/-- The objective of (7.16): `u(s, a) + β ∫ f(s′) P(s, a; ds′)`. -/
noncomputable def br_obj (M : MDP S A) (f : S → ℝ) (p : S × A) : ℝ :=
  M.u 0 p + M.β * ∫ s', f s' ∂M.P 0 p

/-- The policy correspondence of `f`: the maximizers in (7.16). -/
def br_G (M : MDP S A) (f : S → ℝ) (s : S) : Set A := argmax (br_obj M f) M.Γ s

/-- `|∫ f dμ| ≤ C` for a probability measure and `|f| ≤ C`. -/
theorem br_abs_integral_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := C) (f := f)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf x)
  simpa [Real.norm_eq_abs, probReal_univ] using this

variable {M : MDP S A}

/-- The objective of (7.16) is continuous for `f ∈ C(S)`. -/
theorem br_continuous_obj (h : br_Standing M) (f : S →ᵇ ℝ) : Continuous (br_obj M f) :=
  h.a721.1.add (continuous_const.mul (h.a723 f f.continuous ⟨‖f‖, fun s => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s⟩))

theorem br_abs_obj_le (h : br_Standing M) (f : S →ᵇ ℝ) (p : S × A) :
    |br_obj M f p| ≤ h.a721.2.choose + |M.β| * ‖f‖ := by
  have := h.markov 0
  refine (abs_add_le _ _).trans (add_le_add (h.a721.2.choose_spec p) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (br_abs_integral_le fun s => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s) (abs_nonneg _)

theorem br_bound_maxValue (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) :
    ‖maxValue (br_obj M f) M.Γ s‖ ≤ h.a721.2.choose + |M.β| * ‖f‖ := by
  obtain ⟨a, -, hval, -⟩ := exists_argmax (br_continuous_obj h f).continuousOn
    (h.a722 s).1 (h.a722 s).2.1.1
  rw [← hval, Real.norm_eq_abs]
  exact br_abs_obj_le h f (s, a)

/-- **The Bellman operator (7.16)** (Miao, p. 205) on `C(S)`:
`(Tf)(s) = sup_{a ∈ Γ(s)} u(s, a) + β ∫ f(s′) P(s, a; ds′)`. `Tf` is bounded, and continuous by
the Theorem of the Maximum, so `T : C(S) → C(S)`. -/
noncomputable def br_T (h : br_Standing M) (f : S →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (maxValue (br_obj M f) M.Γ)
    (theorem_3_6 (br_continuous_obj h f).continuousOn (fun s => (h.a722 s).1)
      (fun s => (h.a722 s).2.1) fun s => (h.a722 s).2.2).1
    (h.a721.2.choose + |M.β| * ‖f‖) (br_bound_maxValue h f)

theorem br_T_apply (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) :
    br_T h f s = maxValue (br_obj M f) M.Γ s := rfl

/-- **(7.16)** (Miao, p. 205): `(Tf)(s) = sup_{a ∈ Γ(s)} u(s, a) + β ∫ f(s′) P(s, a; ds′)`. -/
theorem eq_7_16 (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) :
    br_T h f s = sSup ((fun a => M.u 0 (s, a) + M.β * ∫ s', f s' ∂M.P 0 (s, a)) '' M.Γ s) :=
  rfl

/-- Miao, p. 205: "the maximum is attained". -/
theorem br_exists_argmax (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) :
    ∃ a ∈ M.Γ s, br_T h f s = br_obj M f (s, a) ∧
      ∀ a' ∈ M.Γ s, br_obj M f (s, a') ≤ br_T h f s := by
  obtain ⟨a, ha, hval, hmax⟩ := exists_argmax (br_continuous_obj h f).continuousOn
    (h.a722 s).1 (h.a722 s).2.1.1
  exact ⟨a, ha, hval.symm, fun a' ha' => (hmax a' ha').trans_eq hval⟩

theorem br_obj_le_T (h : br_Standing M) (f : S →ᵇ ℝ) {s : S} {a : A} (ha : a ∈ M.Γ s) :
    br_obj M f (s, a) ≤ br_T h f s :=
  le_maxValue (br_continuous_obj h f).continuousOn (h.a722 s).1 ha

/-- The policy correspondence of `f ∈ C(S)` is nonempty, compact-valued and u.h.c. (the
Theorem of the Maximum). -/
theorem br_G_props (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) :
    (br_G M f s).Nonempty ∧ IsCompact (br_G M f s) ∧ IsUHC (br_G M f) s :=
  (theorem_3_6 (br_continuous_obj h f).continuousOn (fun s => (h.a722 s).1)
    (fun s => (h.a722 s).2.1) fun s => (h.a722 s).2.2).2 s

theorem br_mem_G (h : br_Standing M) {f : S →ᵇ ℝ} {s : S} {a : A} :
    a ∈ br_G M f s ↔ a ∈ M.Γ s ∧ br_obj M f (s, a) = br_T h f s := Iff.rfl

variable [OpensMeasurableSpace S]

/-- Bounded continuous functions are integrable against `P(s, a; ·)`. -/
theorem br_integrable (h : br_Standing M) (f : S →ᵇ ℝ) (p : S × A) : Integrable f (M.P 0 p) := by
  have := h.markov 0
  exact integrable_of_abs_le f.continuous.measurable fun s => by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm s

/-- `T` is monotone (Blackwell's first condition). -/
theorem br_T_mono (h : br_Standing M) (hβ : 0 ≤ M.β) {f g : S →ᵇ ℝ} (hfg : f ≤ g) :
    br_T h f ≤ br_T h g := fun s => by
  obtain ⟨a, ha, hval, -⟩ := br_exists_argmax h f s
  change br_T h f s ≤ br_T h g s
  rw [hval]
  refine le_trans ?_ (br_obj_le_T h g ha)
  have hE : ∫ s', f s' ∂M.P 0 (s, a) ≤ ∫ s', g s' ∂M.P 0 (s, a) :=
    integral_mono (br_integrable h f _) (br_integrable h g _) fun s' => hfg s'
  simp only [br_obj]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE hβ)

/-- `T(f + a) = Tf + βa` (discounting, Blackwell's second condition, with equality). -/
theorem br_T_add_const (h : br_Standing M) (f : S →ᵇ ℝ) (c : ℝ) :
    br_T h (f + const S c) = br_T h f + const S (M.β * c) := by
  ext s
  have := h.markov 0
  have hobj : ∀ a, br_obj M ⇑(f + const S c) (s, a) = br_obj M f (s, a) + M.β * c := fun a => by
    have e : ∀ s', (f + const S c) s' = f s' + c := fun _ => rfl
    simp only [br_obj, e]
    rw [integral_add (br_integrable h f _) (integrable_const c)]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  obtain ⟨a, ha, hval, hmax⟩ := br_exists_argmax h f s
  obtain ⟨a', ha', hval', hmax'⟩ := br_exists_argmax h (f + const S c) s
  simp only [BoundedContinuousFunction.add_apply, const_apply]
  have i1 := hmax a' ha'
  have i2 := hmax' a ha
  rw [hobj] at hval' i2
  refine le_antisymm ?_ ?_
  · rw [hval']; linarith
  · rw [hval]; linarith

/-- **`T` is a contraction** (Miao, p. 205: "We use Assumption 5.1.2 to verify that the
conditions in the Blackwell Theorem are satisfied so that `T` is a contraction"). -/
theorem br_T_contraction (h : br_Standing M) (h512 : Assumption512 M) :
    br_IsContraction (br_T h) M.β :=
  ⟨h512.1, h512.2, br_blackwell h512.1.le (fun _ _ => br_T_mono h h512.1.le)
    (fun f c _ => (br_T_add_const h f c).le)⟩

/-- A fixed point of `T` is unique. -/
theorem br_fixed_unique (h : br_Standing M) (h512 : Assumption512 M) {V W : S →ᵇ ℝ}
    (hV : br_T h V = V) (hW : br_T h W = W) : W = V := by
  obtain ⟨v, hv, huniq, -⟩ := br_theorem_3_2 (br_T_contraction h h512)
  rw [huniq V hV, huniq W hW]

omit [MeasurableSpace S] [OpensMeasurableSpace S] in
/-- `C(S)` is a Banach space (Miao, p. 205, by SLP Theorem 3.1). -/
theorem br_completeSpace : CompleteSpace (S →ᵇ ℝ) := inferInstance

/-- The right side of (7.2) at `f ∈ C(S)`, in the extended reals of §7.1, is the objective of
(7.16). -/
theorem br_bellmanVal_coe (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) (a : A) :
    ih_bellmanVal M (fun s => (f s : EReal)) s a = ((br_obj M f (s, a) : ℝ) : EReal) := by
  rw [ih_bellmanVal, ih_eint_coe (br_integrable h f (s, a)), br_obj, EReal.coe_add,
    EReal.coe_mul]

omit [OpensMeasurableSpace S] in
/-- `(Tf)(s)` is the supremum of (7.16) in the extended reals. -/
theorem br_T_coe_iSup (h : br_Standing M) (f : S →ᵇ ℝ) (s : S) :
    ((br_T h f s : ℝ) : EReal) = ⨆ a ∈ M.Γ s, ((br_obj M f (s, a) : ℝ) : EReal) := by
  obtain ⟨a, ha, hval, hmax⟩ := br_exists_argmax h f s
  refine le_antisymm ?_ (iSup₂_le fun a' ha' => EReal.coe_le_coe_iff.2 (hmax a' ha'))
  rw [hval]
  exact le_iSup₂_of_le (f := fun a (_ : a ∈ M.Γ s) => ((br_obj M f (s, a) : ℝ) : EReal)) a ha
    le_rfl

/-- `f ∈ C(S)` solves the Bellman equation (7.2) (Miao, p. 196, with the extended integral of
§7.1) if and only if it is a fixed point of `T` (Miao, p. 205: "the solution to the Bellman
equation is a fixed point of `T` in that `V = TV`"). -/
theorem br_bellman_iff (h : br_Standing M) (f : S →ᵇ ℝ) :
    ih_Bellman M (fun s => (f s : EReal)) ↔ br_T h f = f := by
  have key : ∀ s, (⨆ a ∈ M.Γ s, ih_bellmanVal M (fun s => (f s : EReal)) s a) =
      ((br_T h f s : ℝ) : EReal) := fun s => by
    rw [br_T_coe_iSup h f s]
    simp only [br_bellmanVal_coe h f s]
  constructor
  · intro hB
    ext s
    have := hB s
    rw [key s] at this
    exact (EReal.coe_injective this).symm
  · intro hT s
    rw [key s, hT]

/-- At a fixed point of `T`, the policy correspondence `G` of §7.1 is the argmax correspondence
of (7.16). -/
theorem br_ih_G_eq (h : br_Standing M) {V : S →ᵇ ℝ} (hV : br_T h V = V) :
    ih_G M (fun s => (V s : EReal)) = br_G M V := by
  funext s
  ext a
  simp only [ih_G, Set.mem_ofPred_eq, br_bellmanVal_coe h V s a, EReal.coe_eq_coe_iff]
  rw [br_mem_G h, hV]

/-- **Theorem 7.2.1 (Existence)** (Miao, p. 205). Under Assumptions 5.1.2 and 7.2.1–7.2.3 (with
`P` a stochastic kernel), there is exactly one solution `V ∈ C(S)` of the Bellman equation (7.2),
and the associated policy correspondence `G` is nonempty, compact-valued and upper
hemicontinuous. -/
theorem theorem_7_2_1 (h : br_Standing M) (h512 : Assumption512 M) :
    ∃ V : S →ᵇ ℝ, ih_Bellman M (fun s => (V s : EReal)) ∧
      (∀ W : S →ᵇ ℝ, ih_Bellman M (fun s => (W s : EReal)) → W = V) ∧
      ∀ s, (ih_G M (fun s => (V s : EReal)) s).Nonempty ∧
        IsCompact (ih_G M (fun s => (V s : EReal)) s) ∧
        IsUHC (ih_G M fun s => (V s : EReal)) s := by
  obtain ⟨V, hV, huniq, -⟩ := br_theorem_3_2 (br_T_contraction h h512)
  refine ⟨V, (br_bellman_iff h V).2 hV, fun W hW => huniq W ((br_bellman_iff h W).1 hW),
    fun s => ?_⟩
  rw [br_ih_G_eq h hV]
  exact br_G_props h V s

end Miao.InfiniteHorizonDP
