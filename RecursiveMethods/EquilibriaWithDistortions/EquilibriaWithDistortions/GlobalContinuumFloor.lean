/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalContinuumFixed

/-!
# Exercise 18.9: existence of an equilibrium for any continuum of technologies (SLP p. 560)

Exercise 18.9 asks how the stochastic argument of pp. 558–560 changes when the shock space `Ξ`
is a closed bounded interval. `GlobalContinuum` sets up the model (`ContModel`: a compact metric
`Ξ`, jointly continuous technologies satisfying Assumptions 18.1–18.2 shock by shock, a Feller
transition `κ`) and shows that `T` maps `F₊` into itself monotonically. `GlobalContinuumFixed`
shows that the monotone limit `lfp = sup_n Tⁿ0` is a fixed point once consumption along the
iterates has a uniform floor (`ConsFloor`). This module proves that floor **with no extra
hypothesis on the technologies**, so existence holds for every `ContModel`.

The floor comes from an **auxiliary planner** with the concave technology
`Φ(k, ξ) = θ f(0, ξ) + (1 − θ) f(k, ξ) ≤ ψ(k, ξ)`, the continuum version of the argument in
`GlobalStochasticNondegenerate` (finite shocks):
`V(k, ξ) = max_{0 ≤ z ≤ Φ(k, ξ)} U(Φ(k, ξ) − z) + β ∫ V(z, x) κ(ξ, dx)`.

* `Phi` and its properties (`Phi_le_psi`, `Phi_sub_gt`, `Phi_concave`, `Phi_cont`).
* The Bellman operator `plBellOp` on bounded continuous functions on `K × Ξ` (continuity in the
  shock from the Feller property and uniform continuity on the compact `K × Ξ`, `EV_continuous`);
  it is a `β`-contraction (`plBellOp_contracting`) with fixed point `Vstar`, which is concave in
  saving (`isConc_Vstar`). An optimal saving `pz` (`pz_spec`), with consumption `pc`.
* `exists_pc_lb`: the planner's consumption is bounded below by **one positive constant** on
  `K × Ξ`. This uses concavity of `V*`, the bound `‖V*‖`, `Φ ≥ p > 0` and the Inada condition,
  and needs no continuity of the policy.
* `IsInFc.Tc_floor` (**the floor is invariant**): if `h ∈ F₊` leaves at least the planner's
  consumption, so does `T h`. Raising the planner's saving by `δ`, comparing with saving
  `pz(x, z)` tomorrow pointwise in `x`, and letting `δ → 0` by dominated convergence gives the
  planner's Euler inequality with the agent's after-tax return, `U′(c(ξ, k)) ≥ RHS(y₀)` at
  `y₀ = ψ(k, ξ) − c(ξ, k)`. The integrand is a continuous minorant built from `h`, so no
  measurability of the planner's policy in the shock is needed.
* `Tit_floor`, `consFloor`, `lfpc_floor`: the floor holds for every `Tⁿ0` and for `lfp`.
* `ex_18_9_borel_existence`, `ex_18_9_borel_euler_KT`, `ex_18_9_borel_euler` (Feller property
  only): `lfp` is a fixed point of `T` with consumption bounded away from zero, continuous and
  monotone in `k`, Borel in `ξ`, the least supersolution in `F₊`. It solves the integral Euler
  equation at every `(k, ξ)`, in Kuhn–Tucker form, and as an equation under the cross-state
  condition.
* **`ex_18_9_existence`** (Exercise 18.9): under the strong Feller property, `lfp ∈ F₊` is the
  least fixed point of `T`, with consumption bounded away from zero; `ex_18_9_existence_euler`
  adds the Euler equation under the cross-state condition.

**Correction (p. 560).** For the continuum, as for finitely many shocks, existence does not follow
from Schauder's Theorem on `F` (which gives the degenerate `ψ`); it follows from monotone
iteration from `0` with the planner's consumption floor. No anchor at a steady state and no
closeness of the technologies is needed. The uniform anchor of `GlobalContinuumFixed` is a
sufficient condition only.

**Not proved.** Continuity of `lfp` in the shock under the Feller property alone. `lfp` is a
monotone limit of continuous functions, hence lower semicontinuous, and the Feller property moves
the right side of (9) continuously only for continuous integrands. For `κ(ξ) = δ_ξ` continuity
would mean that the least deterministic equilibrium depends continuously on the technology,
which nothing here gives. The strong Feller property is used only for this continuity.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

namespace ContModel

open Set Filter Topology MeasureTheory BoundedContinuousFunction

variable {Ξ : Type} [MetricSpace Ξ] [CompactSpace Ξ] [Nonempty Ξ] [MeasurableSpace Ξ]
  [BorelSpace Ξ] (C : ContModel Ξ)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `0 < β`. -/
theorem β_pos : 0 < C.β := by
  rw [← C.tech_β (Classical.arbitrary Ξ)]; exact (C.tech _).β_pos

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `β < 1`. -/
theorem β_lt_one : C.β < 1 := by
  rw [← C.tech_β (Classical.arbitrary Ξ)]; exact (C.tech _).β_lt_one

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `0 < θ`. -/
theorem θ_pos : 0 < C.θ := by
  rw [← C.tech_θ (Classical.arbitrary Ξ)]; exact (C.tech _).θ_pos

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `θ < 1`. -/
theorem θ_lt_one : C.θ < 1 := by
  rw [← C.tech_θ (Classical.arbitrary Ξ)]; exact (C.tech _).θ_lt_one

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The common utility is continuous on `[0, ∞)`. -/
theorem U_cont : ContinuousOn C.U (Ici 0) := by
  rw [← C.tech_U (Classical.arbitrary Ξ)]; exact (C.tech _).U_cont

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The common utility is strictly increasing on `[0, ∞)`. -/
theorem U_strictMono : StrictMonoOn C.U (Ici 0) := by
  rw [← C.tech_U (Classical.arbitrary Ξ)]; exact (C.tech _).U_strictMono

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The common utility is strictly concave on `[0, ∞)`. -/
theorem U_strictConcave : StrictConcaveOn ℝ (Ici 0) C.U := by
  rw [← C.tech_U (Classical.arbitrary Ξ)]; exact (C.tech _).U_strictConcave

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `U′` is the derivative of the common utility on `(0, ∞)`. -/
theorem U_deriv {c : ℝ} (hc : 0 < c) : HasDerivAt C.U (C.U' c) c := by
  rw [← C.tech_U (Classical.arbitrary Ξ), ← C.tech_U' (Classical.arbitrary Ξ)]
  exact (C.tech _).U_deriv c hc

/-! ### The auxiliary planner's technology -/

/-- The technology of the auxiliary planner: `Φ(k, ξ) = θ f(0, ξ) + (1 − θ) f(k, ξ)`. -/
noncomputable def Phi (ξ : Ξ) (k : ℝ) : ℝ := C.θ * (C.tech ξ).f 0 + (1 - C.θ) * (C.tech ξ).f k

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- `f = ψ + θ k f′`. -/
theorem f_eq (ξ : Ξ) (k : ℝ) :
    (C.tech ξ).f k = (C.tech ξ).psi k + C.θ * k * (C.tech ξ).f' k := by
  simp only [GlobalModel.psi, C.tech_θ ξ]; ring

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- `Φ ≤ ψ` on `[0, ∞)`. -/
theorem Phi_le_psi (ξ : Ξ) {k : ℝ} (hk : 0 ≤ k) : C.Phi ξ k ≤ (C.tech ξ).psi k := by
  have hθ := C.tech_θ ξ
  have hθ0 : 0 < C.θ := hθ ▸ (C.tech ξ).θ_pos
  have e : (C.tech ξ).psi k - C.Phi ξ k =
      C.θ * ((C.tech ξ).f k - (C.tech ξ).f 0 - k * (C.tech ξ).f' k) := by
    simp only [GlobalModel.psi, Phi, hθ]; ring
  rcases hk.eq_or_lt with h0 | hpos
  · rw [← h0] at e ⊢
    have : (C.tech ξ).psi 0 - C.Phi ξ 0 = 0 := by rw [e]; ring
    linarith
  · have h1 := (C.tech ξ).f'_mul_lt_sub le_rfl hpos
    have : 0 ≤ (C.tech ξ).psi k - C.Phi ξ k := by
      rw [e]; exact mul_nonneg hθ0.le (by linarith)
    linarith

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `Φ(b, ξ) − Φ(a, ξ) > (1 − θ)(b − a) f′(b, ξ)` for `0 ≤ a < b`. -/
theorem Phi_sub_gt (ξ : Ξ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (1 - C.θ) * (b - a) * (C.tech ξ).f' b < C.Phi ξ b - C.Phi ξ a := by
  have h1 := (C.tech ξ).f'_mul_lt_sub ha hab
  have h2 : 0 < 1 - C.θ := by linarith [C.θ_lt_one]
  have : C.Phi ξ b - C.Phi ξ a = (1 - C.θ) * ((C.tech ξ).f b - (C.tech ξ).f a) := by
    simp only [Phi]; ring
  rw [this, mul_assoc]
  exact mul_lt_mul_of_pos_left (by linarith) h2

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `Φ(·, ξ)` is nondecreasing on `[0, ∞)`. -/
theorem Phi_le (ξ : Ξ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : C.Phi ξ a ≤ C.Phi ξ b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · have h1 := C.Phi_sub_gt ξ ha h
    have : 0 < (1 - C.θ) * (b - a) * (C.tech ξ).f' b :=
      mul_pos (mul_pos (by linarith [C.θ_lt_one]) (by linarith))
        ((C.tech ξ).f'_pos (ha.trans h.le))
    linarith

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- `Φ(0, ξ) = f(0, ξ) = ψ(0, ξ)`. -/
theorem Phi_zero (ξ : Ξ) : C.Phi ξ 0 = (C.tech ξ).psi 0 := by
  rw [(C.tech ξ).psi_zero]; simp only [Phi]; ring

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- `Φ(·, ξ)` is continuous on `[0, ∞)`. -/
theorem Phi_continuousOn (ξ : Ξ) : ContinuousOn (C.Phi ξ) (Ici 0) :=
  continuousOn_const.add (continuousOn_const.mul (C.tech ξ).f_cont)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `Φ(·, ξ)` is concave on `[0, ∞)`. -/
theorem Phi_concave (ξ : Ξ) : ConcaveOn ℝ (Ici 0) (C.Phi ξ) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hf := (C.tech ξ).f_strictConcave.concaveOn.2 hx hy ha hb hab
  have h2 : 0 ≤ 1 - C.θ := by linarith [C.θ_lt_one]
  simp only [smul_eq_mul] at hf ⊢
  simp only [Phi]
  have := mul_le_mul_of_nonneg_left hf h2
  have e : a * (C.θ * (C.tech ξ).f 0 + (1 - C.θ) * (C.tech ξ).f x) +
      b * (C.θ * (C.tech ξ).f 0 + (1 - C.θ) * (C.tech ξ).f y) =
      (a + b) * (C.θ * (C.tech ξ).f 0) +
        (1 - C.θ) * (a * (C.tech ξ).f x + b * (C.tech ξ).f y) := by ring
  rw [e, hab, one_mul]
  linarith

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- `Φ` maps `K = [0, B]` into `(0, B]`. -/
theorem Phi_le_B (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) : C.Phi ξ k ≤ C.B :=
  (C.Phi_le_psi ξ hk.1).trans (C.psi_le_B ξ hk)

omit [BorelSpace Ξ] in
/-- `Φ` is bounded below by a positive constant on `[0, ∞) × Ξ`. -/
theorem exists_Phi_lb : ∃ p > 0, ∀ ξ, ∀ k, 0 ≤ k → p ≤ C.Phi ξ k := by
  obtain ⟨p, hp, hpψ⟩ := C.exists_psi_zero_lb
  exact ⟨p, hp, fun ξ k hk => by
    have := C.Phi_le ξ le_rfl hk
    rw [C.Phi_zero] at this
    linarith [hpψ ξ]⟩

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `Φ` is positive on `[0, ∞) × Ξ`. -/
theorem Phi_pos (ξ : Ξ) {k : ℝ} (hk : 0 ≤ k) : 0 < C.Phi ξ k := by
  have := C.Phi_le ξ le_rfl hk
  rw [C.Phi_zero] at this
  linarith [(C.tech ξ).psi_pos le_rfl]

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `Φ` is jointly continuous on `[0, B] × Ξ`. -/
theorem Phi_cont : ContinuousOn (fun p : ℝ × Ξ => C.Phi p.2 p.1) (Icc 0 C.B ×ˢ univ) := by
  have h0 : Continuous fun p : ℝ × Ξ => (C.tech p.2).psi 0 :=
    (C.psi_continuous_shock ⟨le_rfl, C.B_pos.le⟩).comp continuous_snd
  have h1 : ContinuousOn (fun p : ℝ × Ξ => C.θ * (C.tech p.2).psi 0 + (1 - C.θ) *
      ((C.tech p.2).psi p.1 + C.θ * p.1 * (C.tech p.2).f' p.1)) (Icc 0 C.B ×ˢ univ) :=
    (continuous_const.mul h0).continuousOn.add (continuousOn_const.mul (C.psi_cont.add
      ((continuousOn_const.mul continuousOn_fst).mul C.f'_cont)))
  refine h1.congr fun p _ => ?_
  simp only [Phi, ← f_eq, (C.tech p.2).psi_zero]

/-! ### The auxiliary planner's Bellman equation -/

/-- The value functions of the auxiliary planner: bounded continuous functions on `K × Ξ`. -/
abbrev VS : Type := (Icc (0 : ℝ) C.B × Ξ) →ᵇ ℝ

/-- A value function evaluated at saving `z` (clamped to `K`) and shock `x`. -/
noncomputable def vE (V : C.VS) (z : ℝ) (x : Ξ) : ℝ := V (projIcc 0 C.B C.B_pos.le z, x)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `vE V` is jointly continuous. -/
theorem vE_continuous (V : C.VS) : Continuous fun p : ℝ × Ξ => C.vE V p.1 p.2 :=
  V.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `vE V z` is continuous in the shock. -/
theorem vE_continuous_shock (V : C.VS) (z : ℝ) : Continuous fun x => C.vE V z x :=
  (C.vE_continuous V).comp (continuous_const.prodMk continuous_id)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `|V(z, x)| ≤ ‖V‖`. -/
theorem abs_vE_le (V : C.VS) (z : ℝ) (x : Ξ) : |C.vE V z x| ≤ ‖V‖ :=
  V.norm_coe_le_norm _

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `|V(z, x) − W(z, x)| ≤ d(V, W)`. -/
theorem abs_vE_sub_le (V W : C.VS) (z : ℝ) (x : Ξ) : |C.vE V z x - C.vE W z x| ≤ dist V W := by
  have := V.dist_coe_le_dist (g := W) (projIcc 0 C.B C.B_pos.le z, x)
  rwa [Real.dist_eq] at this

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `vE V` on `K`. -/
theorem vE_of_mem (V : C.VS) {z : ℝ} (hz : z ∈ Icc 0 C.B) (x : Ξ) :
    C.vE V z x = V (⟨z, hz⟩, x) := by
  simp only [vE, projIcc_of_mem _ hz]

/-- The expected continuation value `∫ V(z, x) κ(ξ, dx)`. -/
noncomputable def EV (V : C.VS) (ξ : Ξ) (z : ℝ) : ℝ := ∫ x, C.vE V z x ∂(C.κ ξ)

/-- `x ↦ V(z, x)` is integrable. -/
theorem integrable_vE (V : C.VS) (z : ℝ) (ξ : Ξ) : Integrable (fun x => C.vE V z x) (C.κ ξ) := by
  have := C.κ_prob ξ
  exact (C.vE_continuous_shock V z).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [CompactSpace Ξ] [Nonempty Ξ] [BorelSpace Ξ] in
/-- A pointwise bound `g ≤ g′ + D` integrates against the probability `κ(ξ)`. -/
theorem integral_le_add {g g' : Ξ → ℝ} {ξ : Ξ} (hg : Integrable g (C.κ ξ))
    (hg' : Integrable g' (C.κ ξ)) {D : ℝ} (h : ∀ x, g x ≤ g' x + D) :
    ∫ x, g x ∂(C.κ ξ) ≤ ∫ x, g' x ∂(C.κ ξ) + D := by
  have := C.κ_prob ξ
  calc ∫ x, g x ∂(C.κ ξ) ≤ ∫ x, (g' x + D) ∂(C.κ ξ) :=
        integral_mono hg (hg'.add (integrable_const D)) h
    _ = ∫ x, g' x ∂(C.κ ξ) + D := by rw [integral_add hg' (integrable_const D)]; simp

/-- `EV V ≤ EV W + d(V, W)`. -/
theorem EV_le_add (V W : C.VS) (ξ : Ξ) (z : ℝ) : C.EV V ξ z ≤ C.EV W ξ z + dist V W :=
  C.integral_le_add (C.integrable_vE V z ξ) (C.integrable_vE W z ξ) fun x => by
    linarith [(abs_le.1 (C.abs_vE_sub_le V W z x)).2]

/-- `(ξ, z) ↦ EV V ξ z` is jointly continuous (the Feller property and uniform continuity of
`V` on the compact `K × Ξ`). -/
theorem EV_continuous (V : C.VS) : Continuous fun q : Ξ × ℝ => C.EV V q.1 q.2 := by
  rw [Metric.continuous_iff]
  rintro ⟨ξ0, z0⟩ ε hε
  obtain ⟨δ1, hδ1, hu⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous V.continuous) (ε / 4) (by linarith)
  obtain ⟨δ2, hδ2, hF⟩ := Metric.continuous_iff.1
    (C.κ_feller _ (C.vE_continuous_shock V z0)) ξ0 (ε / 4) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun ⟨ξ, z⟩ hd => ?_⟩
  rw [Prod.dist_eq] at hd
  have hdξ : dist ξ ξ0 < δ2 := (le_max_left _ _).trans_lt (hd.trans_le (min_le_right _ _))
  have hdz : dist z z0 < δ1 := (le_max_right _ _).trans_lt (hd.trans_le (min_le_left _ _))
  have h1 : ∀ x, |C.vE V z x - C.vE V z0 x| < ε / 4 := fun x => by
    have hpd : dist ((projIcc 0 C.B C.B_pos.le z, x) : Icc (0 : ℝ) C.B × Ξ)
        (projIcc 0 C.B C.B_pos.le z0, x) < δ1 := by
      rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq]
      refine max_lt ((abs_projIcc_sub_projIcc C.B_pos.le).trans_lt ?_) hδ1
      rwa [← Real.dist_eq]
    have := hu hpd
    rwa [Real.dist_eq] at this
  have e1 := C.integral_le_add (C.integrable_vE V z ξ) (C.integrable_vE V z0 ξ)
    (D := ε / 4) fun x => by linarith [(abs_lt.1 (h1 x)).2]
  have e2 := C.integral_le_add (C.integrable_vE V z0 ξ) (C.integrable_vE V z ξ)
    (D := ε / 4) fun x => by linarith [(abs_lt.1 (h1 x)).1]
  have e3 := hF ξ hdξ
  rw [Real.dist_eq] at e3 ⊢
  change |C.EV V ξ z - C.EV V ξ0 z0| < ε
  simp only [EV] at e1 e2 e3 ⊢
  rw [abs_lt] at e3 ⊢
  constructor <;> linarith [e3.1, e3.2]

/-- The clamp of `t` to `[0, 1]`. -/
noncomputable def clampUnit (t : ℝ) : ℝ := max 0 (min 1 t)

/-- `clampUnit` is the identity on `[0, 1]`. -/
theorem clampUnit_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampUnit t = t := by
  simp only [clampUnit, min_eq_right ht.2, max_eq_right ht.1]

/-- `0 ≤ clampUnit t ≤ 1`. -/
theorem clampUnit_mem (t : ℝ) : clampUnit t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The planner's objective at `(k, ξ)` when saving `z`: `U(Φ(k, ξ) − z) + β EV(ξ, z)`. -/
noncomputable def obj (V : C.VS) (ξ : Ξ) (k z : ℝ) : ℝ :=
  C.U (C.Phi ξ k - z) + C.β * C.EV V ξ z

/-- The **Bellman operator** of the auxiliary planner, pointwise:
`(PV)(k, ξ) = max_{0 ≤ z ≤ Φ(k, ξ)} U(Φ(k, ξ) − z) + β ∫ V(z, x) κ(ξ, dx)`, with `z = t Φ(k, ξ)`,
`t ∈ [0, 1]`. -/
noncomputable def plBell (V : C.VS) (ξ : Ξ) (k : ℝ) : ℝ :=
  sSup ((fun t => C.obj V ξ k (clampUnit t * C.Phi ξ k)) '' Icc 0 1)

/-- The objective is jointly continuous in `((k, ξ), t)`. -/
theorem obj_continuous (V : C.VS) :
    Continuous fun q : (Icc (0 : ℝ) C.B × Ξ) × ℝ =>
      C.obj V q.1.2 q.1.1 (clampUnit q.2 * C.Phi q.1.2 q.1.1) := by
  have hP : Continuous fun q : (Icc (0 : ℝ) C.B × Ξ) × ℝ => C.Phi q.1.2 q.1.1 :=
    C.Phi_cont.comp_continuous ((continuous_subtype_val.comp (continuous_fst.comp
      continuous_fst)).prodMk (continuous_snd.comp continuous_fst))
      fun q => ⟨q.1.1.2, mem_univ _⟩
  have hc : Continuous clampUnit := continuous_const.max (continuous_const.min continuous_id)
  have hz : Continuous fun q : (Icc (0 : ℝ) C.B × Ξ) × ℝ => clampUnit q.2 * C.Phi q.1.2 q.1.1 :=
    (hc.comp continuous_snd).mul hP
  refine Continuous.add ?_ (continuous_const.mul
    ((C.EV_continuous V).comp ((continuous_snd.comp continuous_fst).prodMk hz)))
  refine C.U_cont.comp_continuous (hP.sub hz) fun q => mem_Ici.2 ?_
  have h1 := (clampUnit_mem q.2).2
  have h2 := C.Phi_pos q.1.2 q.1.1.2.1
  nlinarith

/-- `PV` is continuous on `K × Ξ`. -/
theorem plBell_continuous (V : C.VS) :
    Continuous fun p : Icc (0 : ℝ) C.B × Ξ => C.plBell V p.2 p.1 :=
  isCompact_Icc.continuous_sSup (C.obj_continuous V)

/-- **The Bellman operator** `P` on `VS`. -/
noncomputable def plBellOp (V : C.VS) : C.VS :=
  BoundedContinuousFunction.mkOfCompact ⟨fun p => C.plBell V p.2 p.1, C.plBell_continuous V⟩

/-- The values of the objective over `t ∈ [0, 1]` form a compact set. -/
theorem obj_image_isCompact (V : C.VS) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    IsCompact ((fun t => C.obj V ξ k (clampUnit t * C.Phi ξ k)) '' Icc 0 1) :=
  isCompact_Icc.image ((C.obj_continuous V).comp
    (Continuous.prodMk_right (Y := ℝ) ((⟨k, hk⟩, ξ) : Icc (0 : ℝ) C.B × Ξ)) :)

/-- Every feasible saving `z ∈ [0, Φ(k, ξ)]` gives at most `(PV)(k, ξ)`. -/
theorem obj_le_plBell (V : C.VS) (ξ : Ξ) {k z : ℝ} (hk : k ∈ Icc 0 C.B)
    (hz : z ∈ Icc 0 (C.Phi ξ k)) : C.obj V ξ k z ≤ C.plBell V ξ k := by
  have hP := C.Phi_pos ξ hk.1
  refine le_csSup (C.obj_image_isCompact V ξ hk).bddAbove ⟨z / C.Phi ξ k,
    ⟨div_nonneg hz.1 hP.le, div_le_one_of_le₀ hz.2 hP.le⟩, ?_⟩
  simp only
  rw [clampUnit_of_mem ⟨div_nonneg hz.1 hP.le, div_le_one_of_le₀ hz.2 hP.le⟩,
    div_mul_cancel₀ _ hP.ne']

/-- The maximum in `(PV)(k, ξ)` is attained. -/
theorem exists_plBell_eq (V : C.VS) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    ∃ z ∈ Icc 0 (C.Phi ξ k), C.obj V ξ k z = C.plBell V ξ k := by
  obtain ⟨t, -, hteq⟩ := (C.obj_image_isCompact V ξ hk).sSup_mem
    ((nonempty_Icc.2 zero_le_one).image _)
  have hP := C.Phi_pos ξ hk.1
  exact ⟨clampUnit t * C.Phi ξ k, ⟨mul_nonneg (clampUnit_mem t).1 hP.le,
    mul_le_of_le_one_left hP.le (clampUnit_mem t).2⟩, hteq⟩

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- `(PV)(k, ξ) ≤ c` when every feasible saving gives at most `c`. -/
theorem plBell_le (V : C.VS) (ξ : Ξ) {k c : ℝ} (hk : k ∈ Icc 0 C.B)
    (h : ∀ z ∈ Icc 0 (C.Phi ξ k), C.obj V ξ k z ≤ c) : C.plBell V ξ k ≤ c := by
  have hP := C.Phi_pos ξ hk.1
  refine csSup_le ((nonempty_Icc.2 zero_le_one).image _) (forall_mem_image.2 fun t _ => ?_)
  exact h _ ⟨mul_nonneg (clampUnit_mem t).1 hP.le, mul_le_of_le_one_left hP.le (clampUnit_mem t).2⟩

/-- The objective moves by at most `β d(V, W)`. -/
theorem obj_le_obj_add (V W : C.VS) (ξ : Ξ) (k z : ℝ) :
    C.obj V ξ k z ≤ C.obj W ξ k z + C.β * dist V W := by
  have := mul_le_mul_of_nonneg_left (C.EV_le_add V W ξ z) C.β_pos.le
  simp only [obj]
  linarith

/-- `P` is a contraction with modulus `β`. -/
theorem dist_plBellOp_le (V W : C.VS) :
    dist (C.plBellOp V) (C.plBellOp W) ≤ C.β * dist V W := by
  have h0 : 0 ≤ C.β * dist V W := mul_nonneg C.β_pos.le dist_nonneg
  refine (BoundedContinuousFunction.dist_le h0).2 fun p => ?_
  have h1 : C.plBell V p.2 p.1 ≤ C.plBell W p.2 p.1 + C.β * dist V W :=
    C.plBell_le V p.2 p.1.2 fun z hz => (C.obj_le_obj_add V W p.2 p.1 z).trans
      (add_le_add_left (C.obj_le_plBell W p.2 p.1.2 hz) _)
  have h2 : C.plBell W p.2 p.1 ≤ C.plBell V p.2 p.1 + C.β * dist V W := by
    rw [dist_comm]
    exact C.plBell_le W p.2 p.1.2 fun z hz => (C.obj_le_obj_add W V p.2 p.1 z).trans
      (add_le_add_left (C.obj_le_plBell V p.2 p.1.2 hz) _)
  rw [Real.dist_eq, abs_le]
  change -(C.β * dist V W) ≤ C.plBell V p.2 p.1 - C.plBell W p.2 p.1 ∧
    C.plBell V p.2 p.1 - C.plBell W p.2 p.1 ≤ C.β * dist V W
  constructor <;> linarith

/-- `P` is a contracting map. -/
theorem plBellOp_contracting : ContractingWith ⟨C.β, C.β_pos.le⟩ C.plBellOp :=
  ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact C.β_lt_one),
    LipschitzWith.of_dist_le_mul fun V W => C.dist_plBellOp_le V W⟩

/-- **The planner's value function**: the fixed point of `P`. -/
noncomputable def Vstar : C.VS :=
  ContractingWith.fixedPoint C.plBellOp C.plBellOp_contracting

/-- The Bellman equation `V*(k, ξ) = (PV*)(k, ξ)` on `K`. -/
theorem vE_Vstar (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.vE C.Vstar k ξ = C.plBell C.Vstar ξ k := by
  have h : C.plBellOp C.Vstar = C.Vstar := C.plBellOp_contracting.fixedPoint_isFixedPt
  calc C.vE C.Vstar k ξ = C.Vstar (⟨k, hk⟩, ξ) := C.vE_of_mem _ hk ξ
    _ = C.plBellOp C.Vstar (⟨k, hk⟩, ξ) := by rw [h]
    _ = C.plBell C.Vstar ξ k := rfl

/-! ### Concavity of the planner's value function -/

/-- Every shock's value function is concave in saving on `K`. -/
def IsConc (V : C.VS) : Prop := ∀ x, ConcaveOn ℝ (Icc 0 C.B) (fun z => C.vE V z x)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- The zero value function is concave. -/
theorem isConc_zero : C.IsConc 0 := fun x => by
  have : (fun z => C.vE 0 z x) = fun _ => 0 := rfl
  rw [this]
  exact concaveOn_const 0 (convex_Icc 0 C.B)

variable {C} in
/-- The expected continuation value of a concave value function is concave. -/
theorem IsConc.concave_EV {V : C.VS} (hV : C.IsConc V) (ξ : Ξ) {zx zy a b : ℝ}
    (hzx : zx ∈ Icc 0 C.B) (hzy : zy ∈ Icc 0 C.B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * C.EV V ξ zx + b * C.EV V ξ zy ≤ C.EV V ξ (a * zx + b * zy) := by
  have i1 := (C.integrable_vE V zx ξ).const_mul a
  have i2 := (C.integrable_vE V zy ξ).const_mul b
  simp only [EV]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  refine integral_mono (i1.add i2) (C.integrable_vE V _ ξ) fun x => ?_
  have := (hV x).2 hzx hzy ha hb hab
  simp only [smul_eq_mul] at this
  exact this

variable {C} in
/-- `P` preserves concavity (`Φ` and `U` are concave and `U` is increasing). -/
theorem IsConc.plBellOp {V : C.VS} (hV : C.IsConc V) : C.IsConc (C.plBellOp V) := by
  intro ξ
  refine ⟨convex_Icc 0 C.B, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a * x + b * y ∈ Icc 0 C.B := convex_Icc 0 C.B hx hy ha hb hab
  have e : ∀ {k : ℝ} (hk : k ∈ Icc 0 C.B), C.vE (C.plBellOp V) k ξ = C.plBell V ξ k :=
    fun hk => C.vE_of_mem _ hk ξ
  change a * C.vE (C.plBellOp V) x ξ + b * C.vE (C.plBellOp V) y ξ ≤
    C.vE (C.plBellOp V) (a * x + b * y) ξ
  rw [e hx, e hy, e hxy]
  obtain ⟨zx, hzx, hzxe⟩ := C.exists_plBell_eq V ξ hx
  obtain ⟨zy, hzy, hzye⟩ := C.exists_plBell_eq V ξ hy
  rw [← hzxe, ← hzye]
  have hPc := (C.Phi_concave ξ).2 (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) ha hb hab
  simp only [smul_eq_mul] at hPc
  have hzxK : zx ∈ Icc 0 C.B := ⟨hzx.1, hzx.2.trans (C.Phi_le_B ξ hx)⟩
  have hzyK : zy ∈ Icc 0 C.B := ⟨hzy.1, hzy.2.trans (C.Phi_le_B ξ hy)⟩
  have hfeas : a * zx + b * zy ∈ Icc 0 (C.Phi ξ (a * x + b * y)) := by
    refine ⟨by nlinarith [hzx.1, hzy.1], le_trans ?_ hPc⟩
    nlinarith [hzx.2, hzy.2]
  refine le_trans ?_ (C.obj_le_plBell V ξ hxy hfeas)
  have hcx : 0 ≤ C.Phi ξ x - zx := by linarith [hzx.2]
  have hcy : 0 ≤ C.Phi ξ y - zy := by linarith [hzy.2]
  have hU1 := C.U_strictConcave.concaveOn.2 (mem_Ici.2 hcx) (mem_Ici.2 hcy) ha hb hab
  simp only [smul_eq_mul] at hU1
  have hU2 : C.U (a * (C.Phi ξ x - zx) + b * (C.Phi ξ y - zy)) ≤
      C.U (C.Phi ξ (a * x + b * y) - (a * zx + b * zy)) :=
    C.U_strictMono.monotoneOn (mem_Ici.2 (by nlinarith))
      (mem_Ici.2 (by nlinarith)) (by nlinarith)
  have hG := hV.concave_EV ξ hzxK hzyK ha hb hab
  have hβG := mul_le_mul_of_nonneg_left hG C.β_pos.le
  simp only [obj]
  nlinarith

/-- The iterates `Pⁿ0` are concave. -/
theorem isConc_iterate (n : ℕ) : C.IsConc (C.plBellOp^[n] 0) := by
  induction n with
  | zero => exact C.isConc_zero
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.plBellOp

/-- **The planner's value function is concave** in saving, for every shock. -/
theorem isConc_Vstar : C.IsConc C.Vstar := by
  intro ξ
  refine ⟨convex_Icc 0 C.B, fun x hx y hy a b ha hb hab => ?_⟩
  have ht := C.plBellOp_contracting.tendsto_iterate_fixedPoint 0
  have hev : ∀ z, Tendsto (fun n => C.vE (C.plBellOp^[n] 0) z ξ) atTop
      (𝓝 (C.vE C.Vstar z ξ)) := fun z =>
    ((continuous_eval_const (projIcc 0 C.B C.B_pos.le z, ξ)).tendsto _).comp ht
  exact le_of_tendsto_of_tendsto' ((tendsto_const_nhds.smul (hev x)).add
    (tendsto_const_nhds.smul (hev y))) (hev _) fun n => (C.isConc_iterate n ξ).2 hx hy ha hb hab

/-! ### The planner's policy and a uniform lower bound on its consumption -/

/-- An optimal saving of the planner at `(k, ξ)` (`0` outside `K`). -/
noncomputable def pz (ξ : Ξ) (k : ℝ) : ℝ :=
  if hk : k ∈ Icc 0 C.B then Classical.choose (C.exists_plBell_eq C.Vstar ξ hk) else 0

/-- `pz ξ k` is feasible and optimal. -/
theorem pz_spec (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.pz ξ k ∈ Icc 0 (C.Phi ξ k) ∧ C.obj C.Vstar ξ k (C.pz ξ k) = C.plBell C.Vstar ξ k := by
  simp only [pz, hk, ↓reduceDIte]
  exact Classical.choose_spec (C.exists_plBell_eq C.Vstar ξ hk)

/-- The planner's consumption `Φ(k, ξ) − pz(ξ, k)`. -/
noncomputable def pc (ξ : Ξ) (k : ℝ) : ℝ := C.Phi ξ k - C.pz ξ k

/-- The planner's saving lies in `K`. -/
theorem pz_mem (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) : C.pz ξ k ∈ Icc 0 C.B :=
  ⟨(C.pz_spec ξ hk).1.1, (C.pz_spec ξ hk).1.2.trans (C.Phi_le_B ξ hk)⟩

/-- **The planner's consumption is bounded below by a positive constant**, uniformly on
`K × Ξ`. If consumption `c` were below `min{c₁, p/2}` (with `p ≤ Φ` and `U′ > 4βM/p` on
`(0, c₁)`, `M = ‖V*‖`), consuming `t ∈ (c, min{c₁, p/2})` instead would lose at most
`β (t − c) 4M/p` in expected value (concavity of `V*`, saving at least `p/2`) and gain more than
`U′(t)(t − c)`. -/
theorem exists_pc_lb : ∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ C.pc ξ k := by
  obtain ⟨p, hp, hpΦ⟩ := C.exists_Phi_lb
  set M := ‖C.Vstar‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  obtain ⟨c1, hc1, hball⟩ := Metric.mem_nhdsWithin_iff.1
    (C.isMarginalUtility.inada.eventually_gt_atTop (4 * C.β * M / p))
  refine ⟨min c1 (p / 2), lt_min hc1 (half_pos hp), fun ξ k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨⟨hz0, hzP⟩, hzeq⟩ := C.pz_spec ξ hk
  have hzK := C.pz_mem ξ hk
  set c := C.pc ξ k with hcdef
  set z := C.pz ξ k with hzdef
  have hcz : c = C.Phi ξ k - z := rfl
  have hc0 : 0 ≤ c := by rw [hcz]; linarith
  have hm1 := min_le_left c1 (p / 2)
  have hm2 := min_le_right c1 (p / 2)
  set t := (c + min c1 (p / 2)) / 2 with htdef
  have hct : c < t := by linarith
  have ht1 : t < c1 := by linarith
  have ht2 : t ≤ p / 2 := by linarith
  have htpos : 0 < t := by linarith
  have hPp : p ≤ C.Phi ξ k := hpΦ ξ k hk.1
  set z' := C.Phi ξ k - t with hz'def
  have hz'p : p / 2 ≤ z' := by linarith
  have hz'z : z' < z := by linarith
  have h1 := C.obj_le_plBell C.Vstar ξ hk (z := z') ⟨by linarith, by linarith⟩
  rw [← hzeq] at h1
  simp only [obj] at h1
  rw [show C.Phi ξ k - z' = t by rw [hz'def]; ring, ← hcz] at h1
  have hsl : ∀ x, C.vE C.Vstar z x ≤ C.vE C.Vstar z' x + (z - z') * (2 * M / z') := by
    intro x
    have hs := (C.isConc_Vstar x).slope_anti_adjacent (x := 0) (y := z') (z := z)
      ⟨le_rfl, C.B_pos.le⟩ hzK (by linarith) hz'z
    have hb1 := abs_le.1 (C.abs_vE_le C.Vstar z' x)
    have hb2 := abs_le.1 (C.abs_vE_le C.Vstar 0 x)
    rw [sub_zero, div_le_div_iff₀ (by linarith) (by linarith)] at hs
    have hz'0 : 0 < z' := by linarith
    have hq : (z - z') * (2 * M / z') * z' = (z - z') * (2 * M) := by field_simp
    have hkey : (C.vE C.Vstar z x - C.vE C.Vstar z' x) * z' ≤ (z - z') * (2 * M) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * M -
        (C.vE C.Vstar z' x - C.vE C.Vstar 0 x)) (by linarith : (0 : ℝ) ≤ z - z')]
    have : (C.vE C.Vstar z x - C.vE C.Vstar z' x) * z' ≤ (z - z') * (2 * M / z') * z' := by
      rw [hq]; exact hkey
    have := le_of_mul_le_mul_right this hz'0
    linarith
  have hEV : C.EV C.Vstar ξ z ≤ C.EV C.Vstar ξ z' + (z - z') * (2 * M / z') :=
    C.integral_le_add (C.integrable_vE _ z ξ) (C.integrable_vE _ z' ξ) hsl
  have hzz : z - z' = t - c := by rw [hz'def, hcz]; ring
  have hD : 2 * M / z' ≤ 4 * M / p := by
    rw [div_le_div_iff₀ (by linarith) hp]
    nlinarith
  have hD' : (z - z') * (2 * M / z') ≤ (t - c) * (4 * M / p) := by
    rw [hzz]; exact mul_le_mul_of_nonneg_left hD (by linarith)
  have hsU := C.U_strictConcave.lt_slope_of_hasDerivAt (mem_Ici.2 hc0) (mem_Ici.2 htpos.le) hct
    (C.U_deriv htpos)
  rw [slope_def_field, lt_div_iff₀ (by linarith)] at hsU
  have hβ := C.β_pos
  have h2 : C.β * (C.EV C.Vstar ξ z - C.EV C.Vstar ξ z') ≤ C.β * ((t - c) * (4 * M / p)) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ.le
  have e : C.β * ((t - c) * (4 * M / p)) = (4 * C.β * M / p) * (t - c) := by ring
  have key : C.U' t * (t - c) < (4 * C.β * M / p) * (t - c) := by nlinarith
  have hUt := lt_of_mul_lt_mul_right key (by linarith)
  have : 4 * C.β * M / p < C.U' t := hball ⟨by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]; exact ht1, htpos⟩
  linarith

/-- The planner's consumption is positive on `K × Ξ`. -/
theorem pc_pos (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) : 0 < C.pc ξ k := by
  obtain ⟨c, hc, h⟩ := C.exists_pc_lb
  exact hc.trans_le (h ξ k hk)

omit [CompactSpace Ξ] [BorelSpace Ξ] in
/-- For `y ∈ [0, B]`, `Φ(y, ·)` is continuous. -/
theorem Phi_continuous_shock {y : ℝ} (hy : y ∈ Icc 0 C.B) : Continuous fun x => C.Phi x y :=
  C.Phi_cont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hy, mem_univ _⟩

/-! ### The planner's consumption is a floor for the iterates -/

variable {C} in
/-- **The floor is invariant under `T`.** If `h ∈ F₊` leaves at least the planner's consumption,
`ψ − h ≥ c`, then so does `T h`. At `y₀ = ψ(k, ξ) − c(ξ, k) ≥ z = pz(ξ, k)` the right side of the
integral Euler equation is at most `U′(c(ξ, k))`. This is the planner's Euler inequality with the
agent's after-tax return, obtained by raising the planner's saving by `δ`, comparing with the
planner's value at the shock `x` and saving `pz(x, z)` (pointwise in `x`, so no measurability of
the planner's policy in the shock is needed), and letting `δ → 0` by dominated convergence. -/
theorem IsInFc.Tc_floor {h : Ξ → ℝ → ℝ} (hh : C.IsInFc h)
    (hfl : ∀ x, ∀ k ∈ Icc 0 C.B, C.pc x k ≤ (C.tech x).psi k - h x k) (ξ : Ξ) {k : ℝ}
    (hk : k ∈ Icc 0 C.B) : C.pc ξ k ≤ (C.tech ξ).psi k - C.Tc h ξ k := by
  have hzK := C.pz_mem ξ hk
  obtain ⟨⟨hz0, hzP⟩, hzeq⟩ := C.pz_spec ξ hk
  have hPψ := C.Phi_le_psi ξ hk.1
  have hc := C.pc_pos ξ hk
  have hPB := C.psi_le_B ξ hk
  have hΦB := C.Phi_le_B ξ hk
  have := C.κ_prob ξ
  set z := C.pz ξ k with hzdef
  set c := C.pc ξ k with hcdef
  have hcz : c = C.Phi ξ k - z := rfl
  set y0 := (C.tech ξ).psi k - c with hy0
  have hzy : z ≤ y0 := by rw [hy0, hcz]; linarith
  have hy0K : y0 ∈ Icc 0 C.B := ⟨hz0.trans hzy, by linarith⟩
  set w : Ξ → ℝ := fun x => (C.tech x).psi y0 - h x y0 with hwdef
  have hw : ∀ x, C.pc x z ≤ w x := fun x => (hfl x z hzK).trans (hh.mono_sub x hzK hy0K hzy)
  have hwpos : ∀ x, 0 < w x := fun x => (C.pc_pos x hzK).trans_le (hw x)
  have hwc : Continuous w := (C.psi_continuous_shock hy0K).sub
    (hh.cont.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨hy0K, mem_univ _⟩)
  set n : ℝ → Ξ → ℝ := fun δ x =>
    (C.tech x).f' (y0 + δ) * C.U' (w x + (C.Phi x (z + δ) - C.Phi x z)) with hndef
  have hθ1 : 0 < 1 - C.θ := by linarith [C.θ_lt_one]
  have hu := C.isMarginalUtility
  have hrng : ∀ δ, 0 < δ → δ < c →
      z + δ ∈ Icc 0 C.B ∧ z + δ ≤ C.Phi ξ k ∧ y0 + δ ∈ Icc 0 C.B := by
    intro δ hδ hδc
    exact ⟨⟨by linarith, by linarith⟩, by linarith, ⟨by linarith, by linarith⟩⟩
  have hargpos : ∀ δ, 0 ≤ δ → ∀ x, 0 < w x + (C.Phi x (z + δ) - C.Phi x z) := fun δ hδ x => by
    have := C.Phi_le x hzK.1 (show z ≤ z + δ by linarith)
    linarith [hwpos x]
  have hn_cont : ∀ δ, 0 < δ → δ < c → Continuous (n δ) := by
    intro δ hδ hδc
    obtain ⟨h1, -, h3⟩ := hrng δ hδ hδc
    have harg : Continuous fun x => w x + (C.Phi x (z + δ) - C.Phi x z) :=
      hwc.add ((C.Phi_continuous_shock h1).sub (C.Phi_continuous_shock hzK))
    exact (C.f'_continuous_shock h3).mul
      (hu.cont.comp_continuous harg fun x => mem_Ioi.2 (hargpos δ hδ.le x))
  -- the planner's Euler inequality, perturbed by `δ`
  have hstep : ∀ δ, 0 < δ → δ < c →
      C.β * (1 - C.θ) * ∫ x, n δ x ∂(C.κ ξ) ≤ C.U' (c - δ) := by
    intro δ hδ hδc
    obtain ⟨hzδK, hzδP, hyδK⟩ := hrng δ hδ hδc
    have h1 := C.obj_le_plBell C.Vstar ξ hk (z := z + δ) ⟨by linarith, hzδP⟩
    rw [← hzeq] at h1
    simp only [obj] at h1
    rw [show C.Phi ξ k - (z + δ) = c - δ by rw [hcz]; ring, ← hcz] at h1
    have hpt : ∀ x, (1 - C.θ) * δ * n δ x ≤ C.vE C.Vstar (z + δ) x - C.vE C.Vstar z x := by
      intro x
      obtain ⟨⟨hp0, hpP⟩, hpeq⟩ := C.pz_spec x hzK
      have hΦle := C.Phi_le x hzK.1 (show z ≤ z + δ by linarith)
      have hb := C.obj_le_plBell C.Vstar x hzδK (z := C.pz x z) ⟨hp0, hpP.trans hΦle⟩
      rw [← C.vE_Vstar x hzδK] at hb
      have h2 : C.U (C.Phi x (z + δ) - C.pz x z) - C.U (C.Phi x z - C.pz x z) ≤
          C.vE C.Vstar (z + δ) x - C.vE C.Vstar z x := by
        rw [C.vE_Vstar x hzK, ← hpeq]
        simp only [obj] at hb ⊢
        linarith
      have ha : 0 < C.Phi x z - C.pz x z := C.pc_pos x hzK
      have hgap := C.Phi_sub_gt x hzK.1 (show z < z + δ by linarith)
      rw [show z + δ - z = δ by ring] at hgap
      have hgap0 : 0 < (1 - C.θ) * δ * (C.tech x).f' (z + δ) :=
        mul_pos (mul_pos hθ1 hδ) ((C.tech x).f'_pos hzδK.1)
      have hb' : C.Phi x z - C.pz x z < C.Phi x (z + δ) - C.pz x z := by linarith
      have hsl := C.U_strictConcave.lt_slope_of_hasDerivAt (mem_Ici.2 ha.le)
        (mem_Ici.2 (ha.trans hb').le) hb' (C.U_deriv (ha.trans hb'))
      rw [slope_def_field, lt_div_iff₀ (by linarith)] at hsl
      have hUp := hu.pos _ (ha.trans hb')
      have e : C.Phi x (z + δ) - C.pz x z - (C.Phi x z - C.pz x z) =
          C.Phi x (z + δ) - C.Phi x z := by ring
      rw [e] at hsl
      have h3 : (1 - C.θ) * δ * (C.tech x).f' (z + δ) * C.U' (C.Phi x (z + δ) - C.pz x z) ≤
          C.U (C.Phi x (z + δ) - C.pz x z) - C.U (C.Phi x z - C.pz x z) := by
        nlinarith [mul_le_mul_of_nonneg_left hgap.le hUp.le]
      have hf : (C.tech x).f' (y0 + δ) ≤ (C.tech x).f' (z + δ) :=
        (C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 hzδK.1) (mem_Ici.2 hyδK.1)
          (by linarith)
      have hpcw : C.Phi x (z + δ) - C.pz x z ≤ w x + (C.Phi x (z + δ) - C.Phi x z) := by
        have := hw x
        simp only [pc] at this
        linarith
      have hU := hu.strictAnti.antitoneOn (ha.trans hb') ((ha.trans hb').trans_le hpcw) hpcw
      have h4 : n δ x ≤ (C.tech x).f' (z + δ) * C.U' (C.Phi x (z + δ) - C.pz x z) :=
        mul_le_mul hf hU (hu.pos _ ((ha.trans hb').trans_le hpcw)).le
          ((C.tech x).f'_pos hzδK.1).le
      have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hθ1.le hδ.le)
      calc (1 - C.θ) * δ * n δ x
          ≤ (1 - C.θ) * δ * ((C.tech x).f' (z + δ) * C.U' (C.Phi x (z + δ) - C.pz x z)) := h5
        _ = (1 - C.θ) * δ * (C.tech x).f' (z + δ) * C.U' (C.Phi x (z + δ) - C.pz x z) := by
          ring
        _ ≤ _ := h3.trans h2
    have hint : Integrable (n δ) (C.κ ξ) := (hn_cont δ hδ hδc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have hI : (1 - C.θ) * δ * ∫ x, n δ x ∂(C.κ ξ) ≤
        C.EV C.Vstar ξ (z + δ) - C.EV C.Vstar ξ z := by
      rw [← integral_const_mul]
      simp only [EV]
      rw [← integral_sub (C.integrable_vE _ _ ξ) (C.integrable_vE _ _ ξ)]
      exact integral_mono (hint.const_mul _)
        ((C.integrable_vE _ _ ξ).sub (C.integrable_vE _ _ ξ)) hpt
    have hcδ : 0 < c - δ := by linarith
    have h4 := C.U_strictConcave.slope_lt_of_hasDerivAt (mem_Ici.2 hcδ.le) (mem_Ici.2 hc.le)
      (show c - δ < c by linarith) (C.U_deriv hcδ)
    rw [slope_def_field, show c - (c - δ) = δ by ring, div_lt_iff₀ hδ] at h4
    have hβI := mul_le_mul_of_nonneg_left hI C.β_pos.le
    have : δ * (C.β * (1 - C.θ) * ∫ x, n δ x ∂(C.κ ξ)) ≤ δ * C.U' (c - δ) := by nlinarith
    exact le_of_mul_le_mul_left this hδ
  -- the limit `δ → 0`
  have hδlim : ∀ a : ℝ, 0 ≤ a → Tendsto (fun δ : ℝ => a + δ) (𝓝[>] 0) (𝓝[Ici 0] a) := by
    intro a ha
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun δ hδ =>
      mem_Ici.2 (by linarith [mem_Ioi.1 hδ])⟩
    exact ((continuous_const.add continuous_id).tendsto' 0 a (add_zero a)).mono_left
      nhdsWithin_le_nhds
  have hlim : ∀ x, Tendsto (fun δ => n δ x) (𝓝[>] 0) (𝓝 (C.G h y0 x)) := by
    intro x
    have hf := ((C.tech x).f'_continuousOn y0 (mem_Ici.2 hy0K.1)).tendsto.comp
      (hδlim y0 hy0K.1)
    have hP := (((C.Phi_continuousOn x) z (mem_Ici.2 hzK.1)).tendsto.comp
      (hδlim z hzK.1)).sub_const (C.Phi x z)
    rw [sub_self] at hP
    have harg := (tendsto_const_nhds : Tendsto (fun _ : ℝ => w x) (𝓝[>] 0) (𝓝 (w x))).add hP
    rw [add_zero] at harg
    have hU := (hu.cont.continuousAt (Ioi_mem_nhds (hwpos x))).tendsto.comp harg
    exact hf.mul hU
  have hbnd : ∀ δ, 0 < δ → ∀ x, |n δ x| ≤ (C.tech x).f' 0 * C.U' (w x) := by
    intro δ hδ x
    have hpos := hargpos δ hδ.le x
    have hf0 := (C.tech x).f'_pos (show (0 : ℝ) ≤ y0 + δ by linarith [hy0K.1])
    rw [abs_of_pos (mul_pos hf0 (hu.pos _ hpos))]
    have hf : (C.tech x).f' (y0 + δ) ≤ (C.tech x).f' 0 :=
      (C.tech x).f'_strictAntiOn.antitoneOn (mem_Ici.2 le_rfl)
        (mem_Ici.2 (by linarith [hy0K.1])) (by linarith [hy0K.1])
    have hd : w x ≤ w x + (C.Phi x (z + δ) - C.Phi x z) := by
      have := C.Phi_le x hzK.1 (show z ≤ z + δ by linarith)
      linarith
    exact mul_le_mul hf (hu.strictAnti.antitoneOn (hwpos x) hpos hd) (hu.pos _ hpos).le
      ((C.tech x).f'_pos le_rfl).le
  have hbnd_int : Integrable (fun x => (C.tech x).f' 0 * C.U' (w x)) (C.κ ξ) :=
    ((C.f'_continuous_shock ⟨le_rfl, C.B_pos.le⟩).mul (hu.cont.comp_continuous hwc
      fun x => mem_Ioi.2 (hwpos x))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hI : Tendsto (fun δ => ∫ x, n δ x ∂(C.κ ξ)) (𝓝[>] 0) (𝓝 (∫ x, C.G h y0 x ∂(C.κ ξ))) :=
    tendsto_integral_filter_of_dominated_convergence _
      (by filter_upwards [Ioo_mem_nhdsGT hc] with δ hδ
          exact (hn_cont δ hδ.1 hδ.2).aestronglyMeasurable)
      (by filter_upwards [Ioo_mem_nhdsGT hc] with δ hδ
          exact ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hbnd δ hδ.1 x)
      hbnd_int (ae_of_all _ hlim)
  have hL : Tendsto (fun δ => C.β * (1 - C.θ) * ∫ x, n δ x ∂(C.κ ξ)) (𝓝[>] 0)
      (𝓝 (C.Rc h ξ y0)) := tendsto_const_nhds.mul hI
  have hRt : Tendsto (fun δ : ℝ => C.U' (c - δ)) (𝓝[>] 0) (𝓝 (C.U' c)) := by
    have h1 : Tendsto (fun δ : ℝ => c - δ) (𝓝[>] 0) (𝓝 c) :=
      ((continuous_const.sub continuous_id).tendsto' 0 c (sub_zero c)).mono_left
        nhdsWithin_le_nhds
    exact (hu.cont.continuousAt (Ioi_mem_nhds hc)).tendsto.comp h1
  have hR : C.Rc h ξ y0 ≤ C.U' c := le_of_tendsto_of_tendsto hL hRt (by
    filter_upwards [Ioo_mem_nhdsGT hc] with δ hδ
    exact hstep δ hδ.1 hδ.2)
  have hnb : ¬ EulerBelow C.U' (fun _ => False) (C.Rc h ξ) ((C.tech ξ).psi k) y0 := by
    rintro (hz | hlt)
    · exact hz
    · rw [show (C.tech ξ).psi k - y0 = c by rw [hy0]; ring] at hlt
      exact absurd hR (not_le.2 hlt)
  have := eulerCross_le_of_not_below hu (hh.isEulerRHS ξ) hPB hy0K.1 hnb
  change C.Tc h ξ k ≤ y0 at this
  linarith

/-- Every iterate `Tⁿ0` leaves at least the planner's consumption. -/
theorem Tit_floor (n : ℕ) :
    ∀ ξ, ∀ k ∈ Icc 0 C.B, C.pc ξ k ≤ (C.tech ξ).psi k - C.Tit n ξ k := by
  induction n with
  | zero =>
    intro ξ k hk
    have h1 := (C.pz_spec ξ hk).1.1
    have h2 := C.Phi_le_psi ξ hk.1
    change C.Phi ξ k - C.pz ξ k ≤ (C.tech ξ).psi k - 0
    linarith
  | succ n ih =>
    intro ξ k hk
    rw [Tit_succ]
    exact (C.isInFc_Tit n).Tc_floor ih ξ hk

/-- **The consumption floor always holds**: with no hypothesis beyond `ContModel`, consumption
along the iterates `Tⁿ0` is bounded below by one positive constant. -/
theorem consFloor : C.ConsFloor := by
  obtain ⟨c, hc, h⟩ := C.exists_pc_lb
  exact ⟨c, hc, fun n ξ k hk => (h ξ k hk).trans (C.Tit_floor n ξ k hk)⟩

/-- Consumption at the least fixed point is at least the planner's consumption. -/
theorem lfpc_floor (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.pc ξ k ≤ (C.tech ξ).psi k - C.lfpc ξ k := by
  have : C.lfpc ξ k ≤ (C.tech ξ).psi k - C.pc ξ k :=
    le_of_tendsto' (C.tendsto_Tit ξ hk) fun n => by linarith [C.Tit_floor n ξ k hk]
  linarith

/-! ### Existence with no added hypothesis on the technologies -/

/-- **Exercise 18.9, a Borel equilibrium (Feller property only, no extra hypothesis).**
`lfp = lim Tⁿ0` is a fixed point of `T` on `[0, B] × Ξ` with consumption bounded away from zero;
`lfp(ξ, ·)` is continuous, `lfp` and `ψ − lfp` are nondecreasing in `k`, and `lfp(·, k)` is
Borel. It lies below every supersolution in `F₊`. -/
theorem ex_18_9_borel_existence :
    (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc C.lfpc ξ k = C.lfpc ξ k) ∧
      (∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - C.lfpc ξ k) ∧
      (∀ ξ, ContinuousOn (C.lfpc ξ) (Icc 0 C.B)) ∧
      (∀ ξ, MonotoneOn (C.lfpc ξ) (Icc 0 C.B)) ∧
      (∀ ξ, MonotoneOn (fun k => (C.tech ξ).psi k - C.lfpc ξ k) (Icc 0 C.B)) ∧
      (∀ k ∈ Icc 0 C.B, Measurable fun ξ => C.lfpc ξ k) ∧
      ∀ h, C.IsInFc h → (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k ≤ h ξ k) →
        ∀ ξ, ∀ k ∈ Icc 0 C.B, C.lfpc ξ k ≤ h ξ k :=
  C.ex_18_9_borel_equilibrium C.consFloor

/-- **The Borel equilibrium solves the Euler equation** (Feller property only): in Kuhn–Tucker
form at every `(k, ξ)`. -/
theorem ex_18_9_borel_euler_KT (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    (C.lfpc ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.lfpc ξ k) = C.Rc C.lfpc ξ (C.lfpc ξ k)) ∨
    (C.lfpc ξ k = 0 ∧ C.Rc C.lfpc ξ 0 ≤ C.U' ((C.tech ξ).psi k)) :=
  C.lfpc_euler_KT C.consFloor ξ hk

/-- Under the cross-state condition (Feller property only) the Borel equilibrium solves the
integral Euler equation as an equation at every `(k, ξ)`. -/
theorem ex_18_9_borel_euler (hCS : C.CrossState) (ξ : Ξ) {k : ℝ} (hk : k ∈ Icc 0 C.B) :
    C.lfpc ξ k < (C.tech ξ).psi k ∧
      C.U' ((C.tech ξ).psi k - C.lfpc ξ k) = C.Rc C.lfpc ξ (C.lfpc ξ k) :=
  C.lfpc_euler C.consFloor hCS ξ hk

/-- **Exercise 18.9: existence of an equilibrium in `F₊`** with a continuum of shocks and any
jointly continuous family of technologies. Under the strong Feller property, `T` has a fixed
point `h ∈ F₊` with consumption bounded away from zero; it is the least supersolution in `F₊`,
hence the least fixed point. -/
theorem ex_18_9_existence (hSF : C.StrongFeller) :
    ∃ h, C.IsInFc h ∧ (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k = h ξ k) ∧
      (∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - h ξ k) ∧
      ∀ h', C.IsInFc h' → (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h' ξ k ≤ h' ξ k) →
        ∀ ξ, ∀ k ∈ Icc 0 C.B, h ξ k ≤ h' ξ k :=
  C.ex_18_9_exists_equilibrium C.consFloor hSF

/-- **Exercise 18.9, equilibrium in equation form**: under the strong Feller property and the
cross-state condition, some `h ∈ F₊` with consumption bounded away from zero solves the integral
Euler equation at every `(k, ξ)`. -/
theorem ex_18_9_existence_euler (hSF : C.StrongFeller) (hCS : C.CrossState) :
    ∃ h, C.IsInFc h ∧ (∀ ξ, ∀ k ∈ Icc 0 C.B, C.Tc h ξ k = h ξ k) ∧
      (∃ c > 0, ∀ ξ, ∀ k ∈ Icc 0 C.B, c ≤ (C.tech ξ).psi k - h ξ k) ∧
      ∀ ξ, ∀ k ∈ Icc 0 C.B, C.U' ((C.tech ξ).psi k - h ξ k) = C.Rc h ξ (h ξ k) :=
  C.ex_18_9_equilibrium C.consFloor hSF hCS

end ContModel

end StokeyLucasPrescott.EquilibriaWithDistortions
