/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.Basics
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Martingales and Klein's predetermined processes

Copied from `EconomicDynamics/RationalExpectations` (module `KleinMartingales`), namespace renamed.

Miao, §2.3.2, pp. 55–56, in the abstract setting of `Basics` (a `CondExpSystem 𝕜 V`).

* `IsMartingaleProc` (Definition 2.3.2): `E_t X_{t+1} = X_t`.
* `IsMartingaleDiffProc` (Definition 2.3.2): `E_t X_{t+1} = 0`.
* `IsPredeterminedKlein E ξ X` (Definition 2.3.4): the prediction error
  `X_{t+1} − E_t X_{t+1}` is the given process `ξ_{t+1}`, `ξ` is a martingale difference, and
  `X₀` is `F₀`-measurable (`E₀X₀ = X₀`). "Exogenously given" is modelled by `ξ` being a parameter.
* `predError_isMartingaleDiff`: the prediction error of any process is automatically a martingale
  difference, so clause (a) of Definition 2.3.4 only says that `ξ` is given in advance.
* `isPredeterminedKlein_zero_iff` (p. 56): with `ξ = 0` the definition is Blanchard and Kahn's
  (`IsPredeterminedBK`) together with `E₀X₀ = X₀`.
* `isStableProc_of_uniformly_bounded` (p. 56, "it is stable if it is uniformly bounded"); in the
  abstract setting stability means bounded norms (`E|X|` for `V = L¹`), so a uniform bound on the
  norms is stability itself. The `L¹` reading (`|X_t| ≤ M` a.s. gives `E|X_t| ≤ M`) belongs to the
  concrete `L¹` instance and is not formalised here.
* `example_mdiff_not_stable` (p. 56, "a martingale difference process may not be stable"): an
  abstract `CondExpSystem` on `ℓ^∞(ℕ)`, `E_t` = truncation to the coordinates `≤ t` (a
  filtration in which coordinate `t` is revealed at date `t`), with the adapted martingale
  difference `X_t = t·e_t`, `‖X_t‖ = t`. In a finite-dimensional `V` such an example is
  impossible for adapted processes, so an infinite-dimensional space is needed; this one is
  abstract and is not `L¹` of a probability space.

The white-noise claims of p. 56 (Definition 2.3.3, "a white noise process is stable", "(2.2) gives
a white noise", "a white noise may not satisfy (2.2)") are second-moment statements and are not
formalised in this module.
-/

namespace Miao.LinearQuadratic

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 2.3.2** (Miao, p. 55): `{X_t}` is a martingale if `E_t X_{t+1} = X_t`. -/
def IsMartingaleProc {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) : Prop :=
  ∀ t i, E.E t (X (t + 1) i) = X t i

/-- **Definition 2.3.2** (Miao, p. 55): `{X_t}` is a martingale difference process if
`E_t X_{t+1} = 0`. -/
def IsMartingaleDiffProc {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) : Prop :=
  ∀ t i, E.E t (X (t + 1) i) = 0

/-- **Definition 2.3.4** (Miao, p. 56): `{X_t}` is predetermined (backward-looking) with the
exogenously given prediction error `{ξ_t}` if (a) `ξ_{t+1} = X_{t+1} − E_t X_{t+1}` and `ξ` is a
martingale difference process, and (b) `X₀` is `F₀`-measurable. -/
def IsPredeterminedKlein {ι : Type*} (E : CondExpSystem 𝕜 V) (ξ X : ℕ → ι → V) : Prop :=
  (∀ t i, X (t + 1) i - E.E t (X (t + 1) i) = ξ (t + 1) i) ∧ IsMartingaleDiffProc E ξ ∧
    ∀ i, E.E 0 (X 0 i) = X 0 i

/-- Miao, Definition 2.3.4 (p. 56): the prediction error `X_{t+1} − E_t X_{t+1}` of any process is
a martingale difference (law of iterated expectations), so in clause (a) the content is that the
prediction error is given exogenously. -/
theorem predError_isMartingaleDiff {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) :
    IsMartingaleDiffProc E (fun t i => X t i - E.E (t - 1) (X t i)) := by
  intro t i
  simp only [Nat.add_sub_cancel, map_sub, E.idem, sub_self]

/-- Miao, p. 56 ("When `ξ_{t+1} = 0`, we obtain the Blanchard and Kahn (1980) definition"):
predetermined with zero prediction error is `E_t X_{t+1} = X_{t+1}` (`IsPredeterminedBK`) with an
`F₀`-measurable `X₀`. -/
theorem isPredeterminedKlein_zero_iff {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) :
    IsPredeterminedKlein E 0 X ↔ IsPredeterminedBK E X ∧ ∀ i, E.E 0 (X 0 i) = X 0 i := by
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨fun t i => (sub_eq_zero.1 (h1 t i)).symm, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨fun t i => by rw [h1 t i, sub_self]; rfl, fun t i => map_zero _, h3⟩

/-- A martingale is a martingale difference after subtracting its lag (Miao, p. 55):
`E_t (X_{t+1} − X_t) = 0` for an adapted martingale. -/
theorem IsMartingaleProc.diff {ι : Type*} {E : CondExpSystem 𝕜 V} {X : ℕ → ι → V}
    (hX : IsMartingaleProc E X) (had : IsAdaptedV E X) :
    IsMartingaleDiffProc E (fun t i => X t i - X (t - 1) i) := by
  intro t i
  simp only [Nat.add_sub_cancel, map_sub, hX t i, had t i, sub_self]

/-- Miao, p. 56: "A martingale difference process … is stable if it is uniformly bounded." In the
abstract setting stability (Definition 2.3.1) is a bound on the norms, so a uniform bound on the
norms gives stability (no martingale property is needed). -/
theorem isStableProc_of_uniformly_bounded {ι : Type*} {X : ℕ → ι → V} {M : ℝ}
    (h : ∀ t i, ‖X t i‖ ≤ M) : IsStableProc X :=
  ⟨max M 0 + 1, by positivity, fun t i => (h t i).trans_lt (by linarith [le_max_left M 0])⟩

/-! ### A martingale difference that is not stable -/

/-- The truncation `f ↦ f·1_{[0,t]}` on `ℓ^∞(ℕ)`, the conditional expectation of the example. -/
noncomputable def klM_trunc (t : ℕ) : lp (fun _ : ℕ => ℂ) ⊤ →L[ℂ] lp (fun _ : ℕ => ℂ) ⊤ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => if n ≤ t then f n else 0, memℓp_infty_iff.2 ⟨‖f‖, by
        rintro _ ⟨n, rfl⟩
        change ‖(if n ≤ t then f n else 0)‖ ≤ ‖f‖
        split_ifs
        · exact lp.norm_apply_le_norm ENNReal.top_ne_zero f n
        · simp⟩⟩
      map_add' := fun f g => by
        refine lp.ext (funext fun n => ?_)
        simp only [lp.coeFn_add, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c f => by
        refine lp.ext (funext fun n => ?_)
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
    1 fun f => by
      rw [one_mul]
      refine lp.norm_le_of_forall_le (norm_nonneg f) fun n => ?_
      change ‖(if n ≤ t then f n else 0)‖ ≤ ‖f‖
      split_ifs
      · exact lp.norm_apply_le_norm ENNReal.top_ne_zero f n
      · simp

theorem klM_trunc_apply (t : ℕ) (f : lp (fun _ : ℕ => ℂ) ⊤) (n : ℕ) :
    klM_trunc t f n = if n ≤ t then f n else 0 := rfl

/-- The truncations form a `CondExpSystem` on `ℓ^∞(ℕ)` (coordinate `t` revealed at date `t`). -/
noncomputable def klM_truncSystem : CondExpSystem ℂ (lp (fun _ : ℕ => ℂ) ⊤) where
  E := klM_trunc
  norm_le t := LinearMap.mkContinuous_norm_le _ zero_le_one _
  tower_le s t h := by
    refine ContinuousLinearMap.ext fun f => lp.ext (funext fun n => ?_)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, klM_trunc_apply]
    split_ifs <;> first | rfl | omega
  tower_ge s t h := by
    refine ContinuousLinearMap.ext fun f => lp.ext (funext fun n => ?_)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, klM_trunc_apply]
    split_ifs <;> first | rfl | omega

/-- Miao, p. 56: "A martingale difference process may not be stable." In the `CondExpSystem` of
truncations on `ℓ^∞(ℕ)`, `X_t = t·e_t` is adapted and a martingale difference
(`E_t X_{t+1} = 0`), but `‖X_t‖ = t`, so it is not stable. -/
theorem example_mdiff_not_stable :
    ∃ X : ℕ → Fin 1 → lp (fun _ : ℕ => ℂ) ⊤, IsAdaptedV klM_truncSystem X ∧
      IsMartingaleDiffProc klM_truncSystem X ∧ ¬ IsStableProc X := by
  refine ⟨fun t _ => lp.single ⊤ t (t : ℂ), fun t i => ?_, fun t i => ?_, ?_⟩
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rfl
    · rw [lp.single_apply_ne ⊤ t _ (by omega)]
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rw [lp.single_apply_ne ⊤ (t + 1) _ (by omega)]
      rfl
    · rfl
  · rintro ⟨M, -, hM⟩
    obtain ⟨t, ht⟩ := exists_nat_gt M
    have h := hM t 0
    rw [lp.norm_single ENNReal.zero_lt_top, Complex.norm_natCast] at h
    linarith

end Miao.LinearQuadratic
