/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.BROptimal
import InfiniteHorizonDP.OCLemma641
import InfiniteHorizonDP.MDPOptimalControl

/-!
# The infinite-horizon optimal control model and Theorem 7.3.1

Miao, §7.3 and §7.3.1, pp. 207–208. The primitives `(X, A, Z, Q, Γ, φ, u, β)` are those of the
optimal control model of §6.4 (`OCModel`; the infinite-horizon problem uses the date-0 reward
`u 0` at every date, and ignores the horizon and terminal reward fields). The state space is
`S = X × Z` (the type `↥X × Z`) and the action space `A` (the type `↥A`).

* `br_ctrlCP`, `br_ctrlMDP`: the model as a control problem of §5.2.4 and as a stationary Markov
  decision process (Miao, pp. 154, 207); its kernel moves `(x, z)` to `(φ(x, a, z, z′), z′)`,
  `z′ ~ Q(z, ·)` (`br_integral_ctrl`). `br_next`, `br_ext` (a function on `X × Z` extended by `0`
  to the ambient space).
* `Assumption731`: Assumption 7.3.1 (`u` bounded and continuous on `X × Z × A`).
* `br_ctrl_a721`, `br_ctrl_a722`, `br_ctrl_a723`: Assumptions 7.3.1, 6.4.4 and Lemma 6.4.1 give
  Assumptions 7.2.1–7.2.3 for this process (`br_ctrl_standing`).
* **(7.19)–(7.20)** (`eq_7_19`, `eq_7_20`): the operator `T` of Theorem 7.2.1 for this process is
  `(Tf)(x, z) = sup_{a ∈ Γ(x, z)} u(x, z, a) + β ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)`, the
  operator of (6.29) (`OCModel.bellman`) at `f`.
* **Theorem 7.3.1** (`theorem_7_3_1`), "using Lemma 6.4.1 and Theorem 7.2.1", for any class `P`
  of functions on which Lemma 6.4.1 holds and which contains the bounded functions; the two
  cases of Assumption 6.4.3 are `theorem_7_3_1_compact` and `theorem_7_3_1_countable`.

`E`, `F`, `Z` are metric spaces with their Borel sets, `F` and `Z` second countable (the book's
Borel sets of Euclidean spaces). Assumptions 6.4.1–6.4.2 (convexity) are not used here.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

variable {E F Z : Type*} [MeasurableSpace Z]

/-- The **infinite-horizon control model** of Miao §7.3 as a control problem (§5.2.4), on the
state space `X × Z` and the action space `A`, with the stationary reward `u = u 0` and the law of
motion `x′ = φ(x, a, z, z′)`. `hX` is the first half of Assumption 6.4.5. -/
noncomputable def br_ctrlCP [MeasurableSpace E] [MeasurableSpace F] (M : OCModel E F Z)
    (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) : ControlProblem ↥M.X Z ↥M.A where
  Q := M.Q
  φ := fun _ p => ⟨M.φ p.1 p.2.1 p.2.2.1 p.2.2.2, hX _ p.1.2 _ p.2.1.2 _ _⟩
  Γ := fun s => {a | (a : F) ∈ M.Γ s.1 s.2}
  u := fun _ p => M.u 0 p.1 p.2.1 p.2.2
  uT := fun _ => 0
  β := M.β

/-- The control model as a **stationary Markov decision process** (Miao, pp. 154, 207). -/
noncomputable def br_ctrlMDP [MeasurableSpace E] [MeasurableSpace F] (M : OCModel E F Z)
    (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) : MDP (↥M.X × Z) ↥M.A :=
  (br_ctrlCP M hX).toMDP

/-- The next state `(φ(x, a, z, z′), z′)`. -/
def br_next (M : OCModel E F Z) (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X)
    (x : ↥M.X) (a : ↥M.A) (z z' : Z) : ↥M.X × Z :=
  (⟨M.φ x a z z', hX _ x.2 _ a.2 _ _⟩, z')

/-- A function on `X × Z` extended by `0` to `E × Z`. -/
noncomputable def br_ext {X : Set E} (f : ↥X × Z → ℝ) (x : E) (z : Z) : ℝ := by
  classical exact if hx : x ∈ X then f (⟨x, hx⟩, z) else 0

omit [MeasurableSpace Z] in
theorem br_ext_mem {X : Set E} (f : ↥X × Z → ℝ) {x : E} (hx : x ∈ X) (z : Z) :
    br_ext f x z = f (⟨x, hx⟩, z) := by
  simp only [br_ext, hx, ↓reduceDIte]

omit [MeasurableSpace Z] in
theorem br_ext_val {X : Set E} (f : ↥X × Z → ℝ) (x : ↥X) (z : Z) : br_ext f x z = f (x, z) :=
  br_ext_mem f x.2 z

/-- The control process is stationary. -/
theorem br_ctrl_stationary [MeasurableSpace E] [MeasurableSpace F] (M : OCModel E F Z)
    (hX : ∀ x ∈ M.X, ∀ a ∈ M.A, ∀ z z', M.φ x a z z' ∈ M.X) : (br_ctrlMDP M hX).IsStationary :=
  fun _ => ⟨rfl, rfl⟩

/-- **Assumption 7.3.1** (Miao, p. 207): `u : X × Z × A → ℝ` is bounded and continuous. -/
def Assumption731 [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace Z]
    (M : OCModel E F Z) : Prop :=
  ContinuousOn (fun p : E × Z × F => M.u 0 p.1 p.2.1 p.2.2) (M.X ×ˢ Set.univ ×ˢ M.A) ∧
    ∃ B, ∀ x ∈ M.X, ∀ z, ∀ a ∈ M.A, |M.u 0 x z a| ≤ B

/-- The state `(x, z)` as a point of the subtype `X ×ˢ Z` of §6.4. -/
def br_toXZ {X : Set E} (s : ↥X × Z) : ↥(X ×ˢ (Set.univ : Set Z)) :=
  ⟨(s.1, s.2), s.1.2, Set.mem_univ _⟩

variable [MetricSpace E] [MetricSpace F] [MetricSpace Z]

omit [MeasurableSpace Z] in
theorem br_continuous_toXZ {X : Set E} : Continuous (br_toXZ (X := X) (Z := Z)) :=
  ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

omit [MeasurableSpace Z] in
/-- A continuous function on `X × Z`, extended by `0`, is continuous on `X × Z`. -/
theorem br_continuousOn_ext {X : Set E} {f : ↥X × Z → ℝ} (hf : Continuous f) :
    ContinuousOn (fun p : E × Z => br_ext f p.1 p.2) (X ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (hf.comp (((continuous_subtype_val.fst).subtype_mk fun q => q.2.1).prodMk
    continuous_subtype_val.snd)).congr fun q => ?_
  simp only [Function.comp_apply, Set.domRestrict_apply]
  rw [br_ext_mem f q.2.1]

variable {M : OCModel E F Z}

/-- Assumption 6.4.4 gives Assumption 7.2.2 for the control process: the correspondence
`(x, z) ↦ {a ∈ A : a ∈ Γ(x, z)}` on `X × Z` is nonempty, compact-valued and continuous. -/
theorem br_ctrl_a722' (h644 : M.Assumption644) (s : ↥M.X × Z) :
    IsCompact {a : ↥M.A | (a : F) ∈ M.Γ s.1 s.2} ∧
      IsLHC (fun s : ↥M.X × Z => {a : ↥M.A | (a : F) ∈ M.Γ s.1 s.2}) s ∧
      IsUHC (fun s : ↥M.X × Z => {a : ↥M.A | (a : F) ∈ M.Γ s.1 s.2}) s := by
  have hA : ∀ s : ↥M.X × Z, M.Γ s.1 s.2 ⊆ M.A := fun s => h644.1 _ s.1.2 _
  have hι : ∀ {xs : ℕ → ↥M.X × Z} {s}, Tendsto xs atTop (𝓝 s) →
      Tendsto (fun n => br_toXZ (xs n)) atTop (𝓝 (br_toXZ s)) := fun hxs =>
    (br_continuous_toXZ.tendsto _).comp hxs
  refine ⟨?_, ?_, ?_⟩
  · rw [Subtype.isCompact_iff]
    convert (h644.2 (br_toXZ s)).1 using 1
    ext y
    exact ⟨fun ⟨a, ha, hay⟩ => hay ▸ ha, fun hy => ⟨⟨y, hA s hy⟩, hy, rfl⟩⟩
  · obtain ⟨⟨y, hy⟩, hl⟩ := (h644.2 (br_toXZ s)).2.1
    refine ⟨⟨⟨y, hA s hy⟩, hy⟩, fun a ha xs hxs => ?_⟩
    obtain ⟨N, ys, hys, hlim⟩ := hl a ha _ (hι hxs)
    classical
    refine ⟨N, fun n => if hn : ys n ∈ M.A then ⟨ys n, hn⟩ else a, fun n hn => ?_, ?_⟩
    · have h1 : ys n ∈ M.A := hA (xs n) (hys n hn)
      simp only [h1, ↓reduceDIte]
      exact hys n hn
    · rw [tendsto_subtype_rng]
      refine hlim.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      have h1 : ys n ∈ M.A := hA (xs n) (hys n hn)
      simp only [h1, ↓reduceDIte]
  · obtain ⟨⟨y, hy⟩, hu⟩ := (h644.2 (br_toXZ s)).2.2
    refine ⟨⟨⟨y, hA s hy⟩, hy⟩, fun xs hxs ys hys => ?_⟩
    obtain ⟨y, hy, φ, hφ, hlim⟩ := hu _ (hι hxs) (fun n => (ys n : F)) hys
    refine ⟨⟨y, hA s hy⟩, hy, φ, hφ, ?_⟩
    rw [tendsto_subtype_rng]
    exact hlim

theorem br_continuous_next (h645 : M.Assumption645) (x : ↥M.X) (a : ↥M.A) (z : Z) :
    Continuous fun z' => br_next M h645.1 x a z z' := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_id
  refine h645.2.comp_continuous (continuous_const.prodMk (continuous_const.prodMk
    (continuous_const.prodMk continuous_id))) fun z' => ?_
  exact ⟨x.2, a.2, Set.mem_univ _⟩

variable [MeasurableSpace E] [MeasurableSpace F]

/-- Assumption 7.3.1 gives Assumption 7.2.1 for the control process. -/
theorem br_ctrl_a721 (h645 : M.Assumption645) (h731 : Assumption731 M) :
    Assumption721 (br_ctrlMDP M h645.1) := by
  obtain ⟨hc, B, hB⟩ := h731
  refine ⟨?_, B, fun p => hB _ p.1.1.2 _ _ p.2.2⟩
  exact hc.comp_continuous ((continuous_subtype_val.comp continuous_fst.fst).prodMk
    (continuous_fst.snd.prodMk (continuous_subtype_val.comp continuous_snd))) fun p =>
    ⟨p.1.1.2, Set.mem_univ _, p.2.2⟩

/-- Assumption 6.4.4 gives Assumption 7.2.2 for the control process. -/
theorem br_ctrl_a722 (h645 : M.Assumption645) (h644 : M.Assumption644) :
    Assumption722 (br_ctrlMDP M h645.1) := br_ctrl_a722' h644

variable [BorelSpace E] [BorelSpace F] [BorelSpace Z] [SecondCountableTopology F]
  [SecondCountableTopology Z]


/-- Assumption 6.4.5 makes the law of motion of the control process measurable. -/
theorem br_measurable_ctrlφ (h645 : M.Assumption645) (t : ℕ) :
    Measurable ((br_ctrlCP M h645.1).φ t) := by
  refine Continuous.measurable (Continuous.subtype_mk ?_ _)
  refine h645.2.comp_continuous (Continuous.prodMk
    (continuous_subtype_val.comp continuous_fst) (Continuous.prodMk
      (continuous_subtype_val.comp continuous_snd.fst) continuous_snd.snd)) fun p => ?_
  exact ⟨p.1.2, p.2.1.2, Set.mem_univ _⟩

theorem br_measurable_next (h645 : M.Assumption645) (x : ↥M.X) (a : ↥M.A) (z : Z) :
    Measurable fun z' => br_next M h645.1 x a z z' :=
  ((br_measurable_ctrlφ h645 0).comp (measurable_const.prodMk (measurable_const.prodMk
    (measurable_const.prodMk measurable_id)))).prodMk measurable_id

/-- The control process has stochastic kernels. -/
theorem br_ctrl_markov [IsMarkovKernel M.Q] (h645 : M.Assumption645) :
    (br_ctrlMDP M h645.1).IsMarkov := by
  have : IsMarkovKernel (br_ctrlCP M h645.1).Q := ‹IsMarkovKernel M.Q›
  exact controlMDP_isMarkov (br_ctrlCP M h645.1) (br_measurable_ctrlφ h645)

/-- The kernel of the control process (Miao, p. 154): `∫ f dP((x, z), a; ·) =
∫ f(φ(x, a, z, z′), z′) Q(z, dz′)`. -/
theorem br_integral_ctrl [IsMarkovKernel M.Q] (h645 : M.Assumption645) {f : ↥M.X × Z → ℝ}
    (hf : Measurable f) (x : ↥M.X) (z : Z) (a : ↥M.A) :
    ∫ s', f s' ∂(br_ctrlMDP M h645.1).P 0 ((x, z), a) =
      ∫ z', f (br_next M h645.1 x a z z') ∂M.Q z := by
  have : IsMarkovKernel (br_ctrlCP M h645.1).Q := ‹IsMarkovKernel M.Q›
  change ∫ s', f s' ∂controlKernel (br_ctrlCP M h645.1) 0 ((x, z), a) = _
  rw [controlKernel_apply (br_ctrlCP M h645.1) (br_measurable_ctrlφ h645 0) x z a,
    integral_map (show Measurable fun z' => ((br_ctrlCP M h645.1).φ 0 (x, a, z, z'), z') from
      br_measurable_next h645 x a z).aemeasurable hf.aestronglyMeasurable]
  rfl

/-- The same integral in the notation of §6.4: `M.cont (br_ext f) x a z`. -/
theorem br_integral_ctrl_cont [IsMarkovKernel M.Q] (h645 : M.Assumption645) {f : ↥M.X × Z → ℝ}
    (hf : Measurable f) (x : ↥M.X) (z : Z) (a : ↥M.A) :
    ∫ s', f s' ∂(br_ctrlMDP M h645.1).P 0 ((x, z), a) = M.cont (br_ext f) x a z := by
  rw [br_integral_ctrl h645 hf]
  simp only [OCModel.cont, br_next]
  congr 1
  funext z'
  rw [br_ext_mem f]

/-- **Lemma 6.4.1 gives Assumption 7.2.3** for the control process, for any class `P` on which
Lemma 6.4.1 holds and which contains the bounded functions. -/
theorem br_ctrl_a723 [IsMarkovKernel M.Q] {P : (E → Z → ℝ) → Prop} (hE : M.ExpCont P)
    (hPb : ∀ f : E → Z → ℝ, (∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B) → P f)
    (h645 : M.Assumption645) : Assumption723 (br_ctrlMDP M h645.1) := by
  intro f hf ⟨B, hB⟩
  have e : (fun p : (↥M.X × Z) × ↥M.A => ∫ s', f s' ∂(br_ctrlMDP M h645.1).P 0 p) =
      fun p => M.cont (br_ext f) p.1.1 p.2 p.1.2 := by
    funext p
    obtain ⟨⟨x, z⟩, a⟩ := p
    exact br_integral_ctrl_cont h645 hf.measurable x z a
  rw [e]
  have hP : P (br_ext f) := hPb _ ⟨B, fun x hx z => by rw [br_ext_mem f hx]; exact hB _⟩
  refine (hE _ hP (br_continuousOn_ext hf)).1.comp_continuous
    ((continuous_subtype_val.comp continuous_fst.fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst.snd)) fun p => ?_
  exact ⟨p.1.1.2, p.2.2, Set.mem_univ _⟩

/-- The standing hypotheses of §7.2 hold for the control process under Assumptions 6.4.3 (in
the form of Lemma 6.4.1), 6.4.4, 6.4.5 and 7.3.1. -/
theorem br_ctrl_standing [IsMarkovKernel M.Q] {P : (E → Z → ℝ) → Prop} (hE : M.ExpCont P)
    (hPb : ∀ f : E → Z → ℝ, (∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B) → P f)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h731 : Assumption731 M) :
    br_Standing (br_ctrlMDP M h645.1) :=
  ⟨br_ctrl_markov h645, br_ctrl_a721 h645 h731, br_ctrl_a722 h645 h644,
    br_ctrl_a723 hE hPb h645⟩

/-- The objective of (7.20) is the objective of (6.29) at date `0`. -/
theorem br_obj_ctrl [IsMarkovKernel M.Q] (h645 : M.Assumption645) (f : ↥M.X × Z →ᵇ ℝ)
    (x : ↥M.X) (z : Z) (a : ↥M.A) :
    br_obj (br_ctrlMDP M h645.1) f ((x, z), a) = M.obj 0 (br_ext f) x z a := by
  simp only [br_obj, OCModel.obj]
  rw [br_integral_ctrl_cont h645 f.continuous.measurable]
  rfl

/-- **The Bellman operator (7.20)** (Miao, p. 207): for `f ∈ C(S)`,
`(Tf)(x, z) = sup_{a ∈ Γ(x, z)} u(x, z, a) + β ∫ f(φ(x, a, z, z′), z′) Q(z, dz′)`, the right side
of (6.29) at `f` (`OCModel.bellman`). -/
theorem eq_7_20 [IsMarkovKernel M.Q] (h645 : M.Assumption645) (h644 : M.Assumption644)
    (h : br_Standing (br_ctrlMDP M h645.1)) (f : ↥M.X × Z →ᵇ ℝ) (x : ↥M.X) (z : Z) :
    br_T h f (x, z) = M.bellman 0 (br_ext f) x z := by
  rw [br_T_apply, maxValue, OCModel.bellman]
  congr 1
  ext r
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (br_obj_ctrl h645 f x z a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, h644.1 _ x.2 _ ha⟩, ha, br_obj_ctrl h645 f x z _⟩

/-- **The Bellman equation (7.19)** (Miao, p. 207): a fixed point `V` of `T` satisfies
`V(x, z) = sup_{a ∈ Γ(x, z)} u(x, z, a) + β ∫ V(φ(x, a, z, z′), z′) Q(z, dz′)`. -/
theorem eq_7_19 [IsMarkovKernel M.Q] (h645 : M.Assumption645) (h644 : M.Assumption644)
    (h : br_Standing (br_ctrlMDP M h645.1)) {v : ↥M.X × Z →ᵇ ℝ} (hv : br_T h v = v) (x : ↥M.X)
    (z : Z) : v (x, z) = M.bellman 0 (br_ext v) x z := by
  rw [← eq_7_20 h645 h644 h, hv]

/-- **Theorem 7.3.1 (Existence)** (Miao, p. 208). Let Lemma 6.4.1 hold on a class `P` containing
the bounded functions (Assumption 6.4.3: `theorem_7_3_1_compact`, `theorem_7_3_1_countable`),
and let Assumptions 5.1.2, 6.4.4, 6.4.5 and 7.3.1 hold. Then the Bellman equation (7.19) has
exactly one solution `V ∈ C(S)`, and the policy correspondence `G` is nonempty, compact-valued
and u.h.c. (By Lemma 6.4.1 and Theorem 7.2.1, applied to the control process.) -/
theorem theorem_7_3_1 [IsMarkovKernel M.Q] {P : (E → Z → ℝ) → Prop} (hE : M.ExpCont P)
    (hPb : ∀ f : E → Z → ℝ, (∃ B, ∀ x ∈ M.X, ∀ z, |f x z| ≤ B) → P f)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h731 : Assumption731 M)
    (h512 : 0 < M.β ∧ M.β < 1) :
    br_Standing (br_ctrlMDP M h645.1) ∧ ∃ V : ↥M.X × Z →ᵇ ℝ,
      (∀ x z, V (x, z) = M.bellman 0 (br_ext V) x z) ∧
      (∀ W : ↥M.X × Z →ᵇ ℝ, (∀ x z, W (x, z) = M.bellman 0 (br_ext W) x z) → W = V) ∧
      ∀ s, (br_G (br_ctrlMDP M h645.1) V s).Nonempty ∧
        IsCompact (br_G (br_ctrlMDP M h645.1) V s) ∧ IsUHC (br_G (br_ctrlMDP M h645.1) V) s := by
  have h := br_ctrl_standing hE hPb h644 h645 h731
  obtain ⟨V, hV, huniq, -⟩ := br_theorem_3_2 (br_T_contraction h h512)
  have hfix : ∀ W : ↥M.X × Z →ᵇ ℝ, (∀ x z, W (x, z) = M.bellman 0 (br_ext W) x z) →
      br_T h W = W := fun W hW => by
    ext ⟨x, z⟩
    rw [eq_7_20 h645 h644 h, ← hW]
  exact ⟨h, V, eq_7_19 h645 h644 h hV, fun W hW => huniq W (hfix W hW),
    br_G_props h V⟩

/-- **Theorem 7.3.1**, case (ii) of Assumption 6.4.3 (`Z` compact, `Q` Feller). -/
theorem theorem_7_3_1_compact [IsMarkovKernel M.Q] (h643 : M.Assumption643ii)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h731 : Assumption731 M)
    (h512 : 0 < M.β ∧ M.β < 1) :
    br_Standing (br_ctrlMDP M h645.1) ∧ ∃ V : ↥M.X × Z →ᵇ ℝ,
      (∀ x z, V (x, z) = M.bellman 0 (br_ext V) x z) ∧
      (∀ W : ↥M.X × Z →ᵇ ℝ, (∀ x z, W (x, z) = M.bellman 0 (br_ext W) x z) → W = V) ∧
      ∀ s, (br_G (br_ctrlMDP M h645.1) V s).Nonempty ∧
        IsCompact (br_G (br_ctrlMDP M h645.1) V s) ∧ IsUHC (br_G (br_ctrlMDP M h645.1) V) s := by
  have : CompactSpace Z := h643.1
  exact theorem_7_3_1 (M.expCont_compact h643.2.2 h645) (fun _ _ => trivial) h644 h645 h731 h512

/-- **Theorem 7.3.1**, case (i) of Assumption 6.4.3 (`Z` countable and discrete). -/
theorem theorem_7_3_1_countable [IsMarkovKernel M.Q] (h643 : OCModel.Assumption643i Z)
    (h644 : M.Assumption644) (h645 : M.Assumption645) (h731 : Assumption731 M)
    (h512 : 0 < M.β ∧ M.β < 1) :
    br_Standing (br_ctrlMDP M h645.1) ∧ ∃ V : ↥M.X × Z →ᵇ ℝ,
      (∀ x z, V (x, z) = M.bellman 0 (br_ext V) x z) ∧
      (∀ W : ↥M.X × Z →ᵇ ℝ, (∀ x z, W (x, z) = M.bellman 0 (br_ext W) x z) → W = V) ∧
      ∀ s, (br_G (br_ctrlMDP M h645.1) V s).Nonempty ∧
        IsCompact (br_G (br_ctrlMDP M h645.1) V s) ∧ IsUHC (br_G (br_ctrlMDP M h645.1) V) s := by
  have : DiscreteTopology Z := h643.2.1
  have : DiscreteMeasurableSpace Z := h643.2.2
  exact theorem_7_3_1 (M.expCont_countable h645) (fun _ h => h) h644 h645 h731 h512

end Miao.InfiniteHorizonDP
