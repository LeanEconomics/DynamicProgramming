/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalOperator

/-!
# Exercise 18.9: a continuum of shocks (SLP p. 560)

Exercise 18.9 asks how the assumptions or arguments must be modified when the shock space `Ξ`
is a closed bounded interval. Here `Ξ` is any nonempty compact metric space with its Borel
σ-algebra (a closed bounded interval is one). The modified assumptions (`ContModel`) are:
* each shock `ξ` has a technology `tech ξ` satisfying Assumptions 18.1 and 18.2 (a
  `GlobalModel`), with common `β`, `θ`, `U`, and `k̄(ξ) ≤ B`;
* `ψ(k, ξ)` and `f′(k, ξ)` are **jointly continuous** on `[0, B] × Ξ`;
* the transition `κ(ξ, ·)` is a probability measure with the **Feller property**:
  `ξ ↦ ∫ g dκ(ξ)` is continuous for every continuous `g`.

The sum in (9) becomes an integral,
  `RHS_ξ(y) = β(1 − θ) ∫ f′(y, ξ′) U′[ψ(y, ξ′) − h(ξ′, y)] κ(ξ, dξ′)`,
and the set `F` is modified to `F₊` (`IsInFc`): `h` is jointly continuous on `[0, B] × Ξ`,
`0 ≤ h < ψ`, and `h(ξ, ·)` and `ψ(·, ξ) − h(ξ, ·)` are nondecreasing.

* `IsInFc.isEulerRHS`: for `h ∈ F₊` the right side is finite and continuous in `y`.
* `ex_18_9_spec_KT`: `T` is well defined (in Kuhn–Tucker form); `(Th)(k, ξ)` is an interior
  solution of the integral Euler equation or a zero-saving corner.
* `ex_18_9_spec`: under the integral cross-state condition `CrossState` the corner is excluded,
  and `(Th)(k, ξ)` is the unique interior solution.
* `ex_18_9` (**Exercise 18.9**): `T` maps `F₊` into `F₊`. Joint continuity of `Th` in `(k, ξ)`
  uses the Feller property and the continuity of the crossing point (`GlobalCrossing`).
* `ex_18_9_mono`: `T` is monotone on `F₊`.

**Why `F₊` (strictly positive consumption) instead of `0 ≤ h ≤ ψ`.** With a finite shock
space, zero consumption in a reachable state makes the right side of (9) infinite. With a
continuum this fails: if `ψ(y, ·) − h(·, y)` vanishes only on a null set, the integral can stay
finite (for `U = √`, `U′(c) = c^{-1/2}` is integrable near a simple zero). The Inada blow-up
that drives the finite-shock argument then breaks. Excluding zero consumption also excludes the
degenerate fixed point `h = ψ` of the finite case (`StochModel.Ts_psi`).

**Existence of a fixed point** is proved by monotone iteration from `0` (`F₊` itself is not
closed). The limit is a fixed point once consumption along the iterates has a uniform floor
(`GlobalContinuumFixed`), and an auxiliary planner provides that floor for every `ContModel`
(`GlobalContinuumFloor`). Under the Feller property alone the fixed point is Borel in the shock
(`ContModel.ex_18_9_borel_existence`). Under the strong Feller property it lies in `F₊`
(`ContModel.ex_18_9_existence`).
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology MeasureTheory

variable (Ξ : Type) [MetricSpace Ξ] [CompactSpace Ξ] [Nonempty Ξ] [MeasurableSpace Ξ]
  [BorelSpace Ξ] in
/-- **The continuum-shock model** (Exercise 18.9): per-shock technologies satisfying
Assumptions 18.1 and 18.2, jointly continuous `ψ` and `f′`, and a Feller probability
transition `κ`. -/
structure ContModel where
  tech : Ξ → GlobalModel
  β : ℝ
  θ : ℝ
  U : ℝ → ℝ
  U' : ℝ → ℝ
  B : ℝ
  κ : Ξ → Measure Ξ
  tech_β : ∀ ξ, (tech ξ).β = β
  tech_θ : ∀ ξ, (tech ξ).θ = θ
  tech_U : ∀ ξ, (tech ξ).U = U
  tech_U' : ∀ ξ, (tech ξ).U' = U'
  kbar_le : ∀ ξ, (tech ξ).kbar ≤ B
  κ_prob : ∀ ξ, IsProbabilityMeasure (κ ξ)
  κ_feller : ∀ g : Ξ → ℝ, Continuous g → Continuous fun ξ => ∫ x, g x ∂(κ ξ)
  psi_cont : ContinuousOn (fun p : ℝ × Ξ => (tech p.2).psi p.1) (Icc 0 B ×ˢ univ)
  f'_cont : ContinuousOn (fun p : ℝ × Ξ => (tech p.2).f' p.1) (Icc 0 B ×ˢ univ)

namespace ContModel

variable {Ξ : Type} [MetricSpace Ξ] [CompactSpace Ξ] [Nonempty Ξ] [MeasurableSpace Ξ]
  [BorelSpace Ξ] (C : ContModel Ξ)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `B > 0`. -/
theorem B_pos : 0 < C.B :=
  (C.tech (Classical.arbitrary Ξ)).kbar_pos.trans_le (C.kbar_le _)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The common marginal utility is a marginal utility. -/
theorem isMarginalUtility : IsMarginalUtility C.U' := by
  rw [← C.tech_U' (Classical.arbitrary Ξ)]; exact (C.tech _).isMarginalUtility

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `β(1 − θ) > 0`. -/
theorem coef_pos : 0 < C.β * (1 - C.θ) := by
  rw [← C.tech_β (Classical.arbitrary Ξ), ← C.tech_θ (Classical.arbitrary Ξ)]
  exact (C.tech _).euler_coef_pos

omit [CompactSpace Ξ] [BorelSpace Ξ] [Nonempty Ξ] in
/-- `ψ(·, ξ)` maps `[0, B]` into `(0, B]`. -/
theorem psi_le_B (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) : (C.tech ξ).psi k ≤ C.B := by
  rcases le_or_gt k (C.tech ξ).kbar with h | h
  · exact ((C.tech ξ).psi_le_kbar ⟨hk.1, h⟩).trans (C.kbar_le ξ)
  · exact ((C.tech ξ).psi_lt k h).le.trans hk.2

/-- **The set `F₊`** (`F` of p. 559 with positive consumption): `h` jointly continuous on
`[0, B] × Ξ`, `0 ≤ h < ψ`, `h(ξ, ·)` and `ψ(·, ξ) − h(ξ, ·)` nondecreasing. -/
structure IsInFc (h : Ξ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × Ξ => h p.2 p.1) (Icc 0 C.B ×ˢ univ)
  nonneg : ∀ ξ, ∀ k ∈ Icc 0 C.B, 0 ≤ h ξ k
  lt_psi : ∀ ξ, ∀ k ∈ Icc 0 C.B, h ξ k < (C.tech ξ).psi k
  mono : ∀ ξ, MonotoneOn (h ξ) (Icc 0 C.B)
  mono_sub : ∀ ξ, MonotoneOn (fun k => (C.tech ξ).psi k - h ξ k) (Icc 0 C.B)

/-- The integrand of the right side of the Euler equation: `f′(y, x) U′[ψ(y, x) − h(x, y)]`. -/
noncomputable def G (h : Ξ → ℝ → ℝ) (y : ℝ) (x : Ξ) : ℝ :=
  (C.tech x).f' y * C.U' ((C.tech x).psi y - h x y)

/-- The right side of the Euler equation with a continuum of shocks:
`β(1 − θ) ∫ f′(y, x) U′[ψ(y, x) − h(x, y)] κ(ξ, dx)`. -/
noncomputable def Rc (h : Ξ → ℝ → ℝ) (ξ : Ξ) (y : ℝ) : ℝ :=
  C.β * (1 - C.θ) * ∫ x, C.G h y x ∂(C.κ ξ)

/-- **The operator `T`** with a continuum of shocks: the crossing point of `y ↦ U′[ψ(k, ξ) − y]`
and `Rc h ξ` (the right side is finite on `F₊`, so `Z ≡ False`). -/
noncomputable def Tc (h : Ξ → ℝ → ℝ) (ξ : Ξ) (k : ℝ) : ℝ :=
  eulerCross C.U' (fun _ => False) (C.Rc h ξ) ((C.tech ξ).psi k)

variable {C}

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The integrand is jointly continuous on `[0, B] × Ξ` for `h ∈ F₊`. -/
theorem IsInFc.G_continuousOn {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) :
    ContinuousOn (fun p : ℝ × Ξ => C.G h p.1 p.2) (Icc 0 C.B ×ˢ univ) := by
  have hc : ContinuousOn (fun p : ℝ × Ξ => (C.tech p.2).psi p.1 - h p.2 p.1)
      (Icc 0 C.B ×ˢ univ) := C.psi_cont.sub hh.cont
  have hU : ContinuousOn (fun p : ℝ × Ξ => C.U' ((C.tech p.2).psi p.1 - h p.2 p.1))
      (Icc 0 C.B ×ˢ univ) :=
    C.isMarginalUtility.cont.comp hc fun p hp => by
      simp only [mem_Ioi, sub_pos]
      exact hh.lt_psi p.2 p.1 hp.1
  exact C.f'_cont.mul hU

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- For fixed `y ∈ [0, B]` the integrand is continuous in the shock. -/
theorem IsInFc.G_continuous {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) {y : ℝ} (hy : y ∈ Icc 0 C.B) :
    Continuous fun x => C.G h y x :=
  hh.G_continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨hy, mem_univ _⟩

/-- For fixed `y ∈ [0, B]` the integrand is integrable. -/
theorem IsInFc.G_integrable {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) {y : ℝ} (hy : y ∈ Icc 0 C.B)
    (ξ : Ξ) : Integrable (fun x => C.G h y x) (C.κ ξ) := by
  have := C.κ_prob ξ
  exact (hh.G_continuous hy).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The right side is continuous in `y` on `[0, B]` (continuity of a parametric integral over the
compact `Ξ`). -/
theorem IsInFc.Rc_continuousOn {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) :
    ContinuousOn (C.Rc h ξ) (Icc 0 C.B) := by
  have := C.κ_prob ξ
  have hB := C.B_pos.le
  set g : ℝ → Ξ → ℝ := fun y x => C.G h (projIcc 0 C.B hB y) x
  have hg : Continuous (Function.uncurry g) :=
    hh.G_continuousOn.comp_continuous
      ((continuous_subtype_val.comp ((continuous_projIcc (h := hB)).comp continuous_fst)).prodMk
        continuous_snd) fun p => ⟨(projIcc 0 C.B hB p.1).2, mem_univ _⟩
  have hi := continuous_parametric_integral_of_continuous (μ := C.κ ξ) hg isCompact_univ
  have hc : Continuous fun y => C.β * (1 - C.θ) * ∫ x in univ, g y x ∂(C.κ ξ) :=
    continuous_const.mul hi
  refine hc.continuousOn.congr fun y hy => ?_
  simp only [Rc, g, Measure.restrict_univ, projIcc_of_mem hB hy]

/-- For `h ∈ F₊` the right side of the integral Euler equation is an `IsEulerRHS` on `[0, B]`
(finite, nonincreasing and continuous). -/
theorem IsInFc.isEulerRHS {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) :
    IsEulerRHS C.B (fun _ => False) (C.Rc h ξ) where
  zero_anti _ _ _ _ _ hz := hz
  anti y y' hy' hyy hyB _ := by
    have hyK : y ∈ Icc 0 C.B := ⟨hy'.trans hyy, hyB⟩
    have hy'K : y' ∈ Icc 0 C.B := ⟨hy', hyy.trans hyB⟩
    refine mul_le_mul_of_nonneg_left (integral_mono (hh.G_integrable hyK ξ)
      (hh.G_integrable hy'K ξ) fun x => ?_) C.coef_pos.le
    have hc' : 0 < (C.tech x).psi y' - h x y' := by linarith [hh.lt_psi x y' hy'K]
    have hcc : (C.tech x).psi y' - h x y' ≤ (C.tech x).psi y - h x y :=
      hh.mono_sub x hy'K hyK hyy
    have hU := C.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc
    have hf : (C.tech x).f' y ≤ (C.tech x).f' y' :=
      (C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 hy') (mem_Ici.2 hyK.1) hyy
    exact mul_le_mul hf hU (C.isMarginalUtility.pos _ (hc'.trans_le hcc)).le
      ((C.tech x).f'_pos hy').le
  cont y hy _ := ⟨Eventually.of_forall fun _ hz => hz, hh.Rc_continuousOn ξ y hy⟩
  blowup _ _ hz := hz.elim

/-- **Exercise 18.9, Kuhn–Tucker form.** For `h ∈ F₊`, a current shock `ξ` and `k ∈ [0, B]`,
either `y = (Th)(k, ξ) < ψ(k, ξ)` solves the integral Euler equation, or `y = 0` is a zero-saving
corner with `RHS(0) ≤ U′(ψ(k, ξ))`. -/
theorem ex_18_9_spec_KT {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) {k : ℝ}
    (hk : k ∈ Icc 0 C.B) :
    (C.Tc h ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.Tc h ξ k) = C.Rc h ξ (C.Tc h ξ k)) ∨
    (C.Tc h ξ k = 0 ∧ C.Rc h ξ 0 ≤ C.U' ((C.tech ξ).psi k)) := by
  have hP := (C.tech ξ).psi_pos hk.1
  rcases eulerCross_spec_KT C.isMarginalUtility (hh.isEulerRHS ξ) hP (C.psi_le_B ξ hk) with
    ⟨h1, -, h3⟩ | ⟨-, h2⟩ | ⟨h1, -, h3⟩
  · exact Or.inl ⟨h1, h3⟩
  · exact (h2 0 le_rfl hP).elim
  · exact Or.inr ⟨h1, h3⟩

variable (C)

/-- The integral **cross-state condition**:
`U′(ψ(0, ξ)) < β(1 − θ) ∫ f′(0, x) U′(ψ(0, x)) κ(ξ, dx)` for every `ξ`. -/
def CrossState : Prop :=
  ∀ ξ, C.U' ((C.tech ξ).psi 0) <
    C.β * (1 - C.θ) * ∫ x, (C.tech x).f' 0 * C.U' ((C.tech x).psi 0) ∂(C.κ ξ)

omit [CompactSpace Ξ] [BorelSpace Ξ] [Nonempty Ξ] in
/-- The least element `h ≡ 0` of `F₊`. -/
theorem isInFc_zero : C.IsInFc fun _ _ => 0 where
  cont := continuousOn_const
  nonneg _ _ _ := le_rfl
  lt_psi ξ k hk := (C.tech ξ).psi_pos hk.1
  mono _ := fun _ _ _ _ _ => le_rfl
  mono_sub ξ := fun a ha b hb hab => by
    simp only [sub_zero]
    exact (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab

variable {C}

/-- **Exercise 18.9, equation form.** Under the cross-state condition, `(Th)(k, ξ)` is the
unique `y ∈ [0, ψ(k, ξ))` solving the integral Euler equation. -/
theorem ex_18_9_spec (hCS : C.CrossState) {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (ξ : Ξ) {k : ℝ}
    (hk : k ∈ Icc 0 C.B) :
    C.Tc h ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.Tc h ξ k) = C.Rc h ξ (C.Tc h ξ k) ∧
      ∀ y, 0 ≤ y → y < (C.tech ξ).psi k →
        C.U' ((C.tech ξ).psi k - y) = C.Rc h ξ y → y = C.Tc h ξ k := by
  have hP := (C.tech ξ).psi_pos hk.1
  have hPB := C.psi_le_B ξ hk
  have h0K : (0 : ℝ) ∈ Icc 0 C.B := ⟨le_rfl, C.B_pos.le⟩
  have h0 : EulerBelow C.U' (fun _ => False) (C.Rc h ξ) ((C.tech ξ).psi k) 0 := by
    right
    have := C.κ_prob ξ
    have hz : (fun x => (C.tech x).f' 0 * C.U' ((C.tech x).psi 0)) =
        fun x => C.G (fun _ _ => 0) 0 x := by
      funext x; simp [G]
    have hint : Integrable (fun x => (C.tech x).f' 0 * C.U' ((C.tech x).psi 0)) (C.κ ξ) := by
      rw [hz]; exact (C.isInFc_zero).G_integrable h0K ξ
    have hle : ∫ x, (C.tech x).f' 0 * C.U' ((C.tech x).psi 0) ∂(C.κ ξ) ≤
        ∫ x, C.G h 0 x ∂(C.κ ξ) := by
      refine integral_mono hint (hh.G_integrable h0K ξ) fun x => ?_
      have hc : 0 < (C.tech x).psi 0 - h x 0 := by linarith [hh.lt_psi x 0 h0K]
      have hle' : (C.tech x).psi 0 - h x 0 ≤ (C.tech x).psi 0 := by
        linarith [hh.nonneg x 0 h0K]
      exact mul_le_mul_of_nonneg_left
        (C.isMarginalUtility.strictAnti.antitoneOn hc ((C.tech x).psi_pos le_rfl) hle')
        ((C.tech x).f'_pos le_rfl).le
    have hψ := (C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.1) hk.1
    have h2 : C.U' ((C.tech ξ).psi k) ≤ C.U' ((C.tech ξ).psi 0) :=
      C.isMarginalUtility.strictAnti.antitoneOn ((C.tech ξ).psi_pos le_rfl)
        ((C.tech ξ).psi_pos hk.1) hψ
    have h3 := mul_le_mul_of_nonneg_left hle C.coef_pos.le
    have h4 := hCS ξ
    simp only [Rc, sub_zero]
    linarith
  rcases eulerCross_spec C.isMarginalUtility (hh.isEulerRHS ξ) hP hPB h0 with
    ⟨h1, -, h3⟩ | ⟨-, h2⟩
  · exact ⟨h1, h3, fun y hy0 hyP heq =>
      (eulerCross_unique C.isMarginalUtility (hh.isEulerRHS ξ) hPB hy0 hyP (fun hz => hz)
        heq).symm⟩
  · exact (h2 0 le_rfl hP).elim

/-- **Exercise 18.9: `T` maps `F₊` into `F₊`.** Joint continuity of `Th` in `(k, ξ)` comes from
the Feller property (the right side moves continuously with the current shock) and the
`1`-Lipschitz dependence of the crossing point on current resources `ψ(k, ξ)`. -/
theorem ex_18_9 {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h) : C.IsInFc fun ξ k => C.Tc h ξ k where
  cont := by
    intro p hp
    have hk : p.1 ∈ Icc 0 C.B := hp.1
    set P0 := (C.tech p.2).psi p.1 with hP0def
    have hP0 : 0 < P0 := (C.tech p.2).psi_pos hk.1
    have hP0B : P0 ≤ C.B := C.psi_le_B p.2 hk
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hev := eventually_abs_eulerCross_sub_le (u := C.U') (l := 𝓝 p.2)
      (Zs := fun _ _ => False) (Rs := fun ξ => C.Rc h ξ) C.isMarginalUtility
      (hh.isEulerRHS p.2) (fun ξ => hh.isEulerRHS ξ) hP0 hP0B
      (fun y hy0 hyP => ⟨fun hz => hz.elim, fun _ => ⟨Eventually.of_forall fun _ hz => hz,
        tendsto_const_nhds.mul ((C.κ_feller _
          (hh.G_continuous ⟨hy0, hyP.le.trans hP0B⟩)).tendsto p.2)⟩⟩) (half_pos hε)
    obtain ⟨δ1, hδ1, hball⟩ := Metric.mem_nhds_iff.1 hev
    obtain ⟨δ2, hδ2, hψ⟩ := Metric.continuousWithinAt_iff.1 (C.psi_cont p hp) (ε / 2)
      (half_pos hε)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun q hq hd => ?_⟩
    have hqp : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hd2 : dist q.2 p.2 < δ1 := lt_of_le_of_lt hqp (hd.trans_le (min_le_left _ _))
    have e1 : |eulerCross C.U' (fun _ => False) (C.Rc h q.2) P0 - C.Tc h p.2 p.1| ≤ ε / 2 :=
      hball hd2
    have e2 := hψ hq (hd.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at e2
    have e3 := abs_eulerCross_sub_le C.isMarginalUtility (hh.isEulerRHS q.2) hP0B
      (C.psi_le_B q.2 hq.1)
    rw [Real.dist_eq]
    change |C.Tc h q.2 q.1 - C.Tc h p.2 p.1| < ε
    have := abs_sub_le (C.Tc h q.2 q.1) (eulerCross C.U' (fun _ => False) (C.Rc h q.2) P0)
      (C.Tc h p.2 p.1)
    simp only [Tc, ← hP0def] at this e1 e3 ⊢
    linarith
  nonneg ξ k hk := eulerCross_nonneg
  lt_psi ξ k hk := by
    rcases ex_18_9_spec_KT hh ξ hk with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · rw [h1]; exact (C.tech ξ).psi_pos hk.1
  mono ξ a ha b hb hab := eulerCross_mono' C.isMarginalUtility (hh.isEulerRHS ξ)
    ((C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab)
    (C.psi_le_B ξ hb)
  mono_sub ξ a ha b hb hab := by
    have := eulerCross_le_add_sub C.isMarginalUtility (hh.isEulerRHS ξ)
      ((C.tech ξ).psi_strictMonoOn.monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab)
      (C.psi_le_B ξ hb)
    simp only [Tc] at this ⊢
    linarith

/-- **`T` is monotone on `F₊`** with a continuum of shocks (the analogue of Exercise 18.7). -/
theorem ex_18_9_mono {h h' : Ξ → ℝ → ℝ} (hh : C.IsInFc h) (hh' : C.IsInFc h')
    (hle : ∀ ξ, ∀ k ∈ Icc 0 C.B, h ξ k ≤ h' ξ k) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.Tc h ξ k ≤ C.Tc h' ξ k := by
  have hPB := C.psi_le_B ξ hk
  refine eulerCross_mono_rhs' (fun _ _ _ hz => hz) (fun y hy0 hyP _ _ => ?_)
  have hyK : y ∈ Icc 0 C.B := ⟨hy0, hyP.le.trans hPB⟩
  refine mul_le_mul_of_nonneg_left (integral_mono (hh.G_integrable hyK ξ)
    (hh'.G_integrable hyK ξ) fun x => ?_) C.coef_pos.le
  have hc' : 0 < (C.tech x).psi y - h' x y := by linarith [hh'.lt_psi x y hyK]
  have hcc : (C.tech x).psi y - h' x y ≤ (C.tech x).psi y - h x y := by
    linarith [hle x y hyK]
  exact mul_le_mul_of_nonneg_left
    (C.isMarginalUtility.strictAnti.antitoneOn hc' (hc'.trans_le hcc) hcc)
    ((C.tech x).f'_pos hy0).le

end ContModel

end StokeyLucasPrescott.EquilibriaWithDistortions
