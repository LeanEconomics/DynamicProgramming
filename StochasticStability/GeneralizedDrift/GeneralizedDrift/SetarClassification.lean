/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.MixedDrift
import GeneralizedDrift.SETAR
import GeneralizedDrift.SetarMarginRecurrence
import GeneralizedDrift.SetarNullMargins

/-!
# The scalar SETAR model: a complete classification (MT Appendix B.2)

Meyn and Tweedie, Appendix B, pp. 538–542. §B.1, the glossary of the drift conditions (V1)–(V4)
and of the transience/nullity criterion, collects results proved in Chapters 8, 9, 11, 14 and 15
and needs no proofs. §B.2 assembles the classification of the scalar SETAR model
`Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)` for `Xₙ₋₁ ∈ Rⱼ` (`setarKernel Γ φ θ r`), drawn in Figures
B.1–B.3. Book indexing: regime `1` is `0 : Fin (m + 1)`, regime `M` is `Fin.last m`.

**The three regions** of the `(θ(1), θ(M), φ(1), φ(M))` parameter space:
* `SetarInterior`: (11.36)–(11.40);
* `SetarMargin`: the margins (11.45)–(11.49);
* `SetarExterior`: (9.46)–(9.51).

**Results.**
* `setar_regions_cover`, `setar_regions_disjoint`: every parameter lies in exactly one region;
  Figures B.1–B.3 are a partition of the parameter space.
* `setar_classification` (STEPS 1–4, pp. 541–542): under (SETAR1)–(SETAR3) (noises with
  densities positive on `ℝ`, zero mean, finite variances in the end regimes) the model is a
  `μ_Leb`-irreducible T-chain whose compact sets are small (STEP 1, Proposition 6.3.6); it is
  regular, hence positive Harris, in the interior (STEP 2, Proposition 11.4.5); Harris recurrent
  and null on the margins (STEP 4, Propositions 11.5.4 and 11.5.5); and transient in the exterior
  (STEP 3, Proposition 9.5.4).
* `setar_isAperiodic`: under (SETAR2) the model is aperiodic (every set of positive Lebesgue
  measure is reached in one step from every point).
* `setar_real_driftV4_36`, `setar_geometric_36`: in the region (11.36) the linear test function
  `V = 1 + a x⁺ + b x⁻` satisfies (V4), and the chain is geometrically ergodic:
  `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` (Theorem 15.0.1).

**Corrections.**
* STEP 2 says that in the interior the linear test functions of Proposition 11.4.5 satisfy the
  stronger condition (V4). This fails at a unit-slope end, i.e. on (11.37)–(11.39): for
  `V = c + a x⁺ + b x⁻` and `θ(M) = 1`, `PV(x) ≥ V(x) + aφ(M)` for large `x`, so no bound
  `PV ≤ ρV + L` with `ρ < 1` holds (`setar_not_linear_driftV4_top`, and
  `setar_not_linear_driftV4_bot` for `θ(1) = 1`). (V4) with linear test functions holds on
  (11.36) (`setar_real_driftV4_36`).

**Hypotheses.** As in the copied Chapters 9 and 11 results: the noises are integrable with mean
zero in every regime, and have finite variances in the end regimes (needed only for the margins,
Proposition 11.5.4).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

variable {m : ℕ}

/-! ### The regions of the parameter space -/

/-- **The interior** (11.36)–(11.40) of the SETAR parameter space (Figures B.1–B.3). -/
def SetarInterior (φ θ : Fin (m + 1) → ℝ) : Prop :=
  (θ 0 < 1 ∧ θ (Fin.last m) < 1 ∧ θ 0 * θ (Fin.last m) < 1) ∨
    (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ 0 < φ 0) ∨
    (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0) ∨
    (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ 0 < φ 0) ∨
    (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧ 0 < φ (Fin.last m) + θ (Fin.last m) * φ 0)

/-- **The margins** (11.45)–(11.49) of the SETAR parameter space (Figures B.2–B.3). -/
def SetarMargin (φ θ : Fin (m + 1) → ℝ) : Prop :=
  (θ 0 < 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0) ∨
    (θ 0 = 1 ∧ θ (Fin.last m) < 1 ∧ φ 0 = 0) ∨
    (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) = 0 ∧ 0 ≤ φ 0) ∨
    (θ 0 = 1 ∧ θ (Fin.last m) = 1 ∧ φ (Fin.last m) < 0 ∧ φ 0 = 0) ∨
    (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧ φ (Fin.last m) + θ (Fin.last m) * φ 0 = 0)

/-- **The exterior** (9.46)–(9.51) of the SETAR parameter space (Figures B.1–B.3). -/
def SetarExterior (φ θ : Fin (m + 1) → ℝ) : Prop :=
  1 < θ 0 ∨ 1 < θ (Fin.last m) ∨
    (θ 0 = 1 ∧ θ (Fin.last m) ≤ 1 ∧ φ 0 < 0) ∨
    (θ 0 ≤ 1 ∧ θ (Fin.last m) = 1 ∧ 0 < φ (Fin.last m)) ∨
    (θ 0 < 0 ∧ 1 < θ 0 * θ (Fin.last m)) ∨
    (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧ φ (Fin.last m) + θ (Fin.last m) * φ 0 < 0)

/-- **The regions cover the parameter space** (Figures B.1–B.3). -/
theorem setar_regions_cover (φ θ : Fin (m + 1) → ℝ) :
    SetarInterior φ θ ∨ SetarMargin φ θ ∨ SetarExterior φ θ := by
  unfold SetarInterior SetarMargin SetarExterior
  rcases lt_trichotomy (θ 0) 1 with ha | ha | ha <;>
    rcases lt_trichotomy (θ (Fin.last m)) 1 with hc | hc | hc
  · rcases lt_or_ge (θ 0 * θ (Fin.last m)) 1 with hp | hp
    · exact Or.inl (Or.inl ⟨ha, hc, hp⟩)
    · have h0 : θ 0 < 0 := by
        by_contra h0
        push Not at h0
        rcases le_or_gt (θ (Fin.last m)) 0 with hc0 | hc0
        · nlinarith
        · nlinarith
      rcases eq_or_lt_of_le hp with he | hgt
      · rcases lt_trichotomy (φ (Fin.last m) + θ (Fin.last m) * φ 0) 0 with h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, he.symm, h⟩))))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, he.symm, h⟩)))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, he.symm, h⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, hgt⟩))))))
  · rcases lt_trichotomy (φ (Fin.last m)) 0 with h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨ha, hc, h⟩)))
    · exact Or.inr (Or.inl (Or.inl ⟨ha, hc, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha.le, hc, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · rcases lt_trichotomy (φ 0) 0 with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hc.le, h⟩))))
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨ha, hc, h⟩)))
    · exact Or.inl (Or.inr (Or.inl ⟨ha, hc, h⟩))
  · rcases lt_or_ge (φ 0) 0 with hp | hp
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hc.le, hp⟩))))
    rcases lt_trichotomy (φ (Fin.last m)) 0 with hq | hq | hq
    · rcases eq_or_lt_of_le hp with hp0 | hp0
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hc, hq, hp0.symm⟩)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hc, hq, hp0⟩))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨ha, hc, hq, hp⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha.le, hc, hq⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inl ha))

/-- **The regions are disjoint** (Figures B.1–B.3): no parameter is in two of the interior, the
margins and the exterior. -/
theorem setar_regions_disjoint (φ θ : Fin (m + 1) → ℝ) :
    ¬ (SetarInterior φ θ ∧ SetarMargin φ θ) ∧ ¬ (SetarInterior φ θ ∧ SetarExterior φ θ) ∧
      ¬ (SetarMargin φ θ ∧ SetarExterior φ θ) := by
  unfold SetarInterior SetarMargin SetarExterior
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩,
      ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3⟩⟩ <;>
      nlinarith
  · rintro ⟨⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩,
      g | g | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3⟩⟩ <;>
      nlinarith
  · rintro ⟨⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩,
      g | g | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3⟩⟩ <;>
      nlinarith

/-! ### The classification -/

variable (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **The complete classification of the scalar SETAR model** (MT Appendix B.2, Figures
B.1–B.3, STEPS 1–4): under (SETAR1)–(SETAR3) — regime noises with densities positive on `ℝ`
(`Γⱼ` equivalent to Lebesgue measure), integrable with mean zero, and with finite variances in
the end regimes — the model is a `μ_Leb`-irreducible T-chain with every compact set small, and
* in the interior it is regular, hence positive Harris, and every compact set is regular;
* on the margins it is Harris recurrent and null;
* in the exterior it is transient. -/
theorem setar_classification (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j)) (hW0 : ∀ j, ∫ w, w ∂Γ j = 0)
    (hW2₀ : Integrable (fun w => w ^ 2) (Γ 0))
    (hW2M : Integrable (fun w => w ^ 2) (Γ (Fin.last m))) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    (IsMaximalIrreducibility (setarKernel Γ φ θ r) volume ∧ IsTChain (setarKernel Γ φ θ r) ∧
      ∀ K : Set ℝ, IsCompact K → IsSmall (setarKernel Γ φ θ r) K) ∧
    (SetarInterior φ θ → IsRegularChain (setarKernel Γ φ θ r) volume ∧
      IsPositiveHarris (setarKernel Γ φ θ r) volume ∧
      ∀ K : Set ℝ, IsCompact K → IsRegularSet (setarKernel Γ φ θ r) volume K) ∧
    (SetarMargin φ θ → IsHarris (setarKernel Γ φ θ r) volume ∧
      IsNull (setarKernel Γ φ θ r) volume) ∧
    (SetarExterior φ θ → IsTransientChain (setarKernel Γ φ θ r) volume) := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, hsmall, hT⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  refine ⟨⟨hψ, hT, hsmall⟩, fun hI => ?_, fun hM => ?_, fun hE => ?_⟩
  · obtain ⟨hK, hreg⟩ := proposition_11_4_5 Γ φ θ r h1 h2 hW hW0 hI
    exact ⟨hreg, hreg.isPositiveHarris hψ, hK⟩
  · exact ⟨(proposition_11_5_4 Γ φ θ r h1 h2 hW hW0 hW2₀ hW2M hM).1,
      proposition_11_5_5_all Γ φ θ r h1 h2 hW hW0 hM⟩
  · exact proposition_9_5_4 Γ φ θ r h1 h2 (hW 0) (hW (Fin.last m)) (hW0 0) (hW0 (Fin.last m)) hE

/-! ### Aperiodicity -/

variable (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **The SETAR model is aperiodic** under (SETAR2): every set of positive Lebesgue measure is
reached in one step from every point, so no point of a class `Dᵢ` of a `d`-cycle with `d ≥ 2`
can move into `Dᵢ₊₁` with probability one while `Dᵢ` has positive measure. -/
theorem setar_isAperiodic (h2 : ∀ j, volume ≪ Γ j) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsAperiodic (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  set P := setarKernel Γ φ θ r
  have hstep : ∀ x {A : Set ℝ}, MeasurableSet A → 0 < volume A → 0 < P x A :=
    fun x A hA hpos => by
    rw [setarKernel_apply' Γ φ θ r x hA]
    refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
    have := h2 (setarRegime r x) h0
    rwa [show {w : ℝ | φ (setarRegime r x) + θ (setarRegime r x) * x + w ∈ A} =
      (fun w => (φ (setarRegime r x) + θ (setarRegime r x) * x) + w) ⁻¹' A from rfl,
      measure_preimage_add] at this
  refine ⟨one_pos, ⟨fun _ => univ, ⟨fun _ => MeasurableSet.univ,
    fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ x _ => measure_univ,
    by simp only [iUnion_const, compl_univ, measure_empty]⟩⟩,
    fun d' D' hd' hD' => ?_⟩
  by_contra hlt
  push Not at hlt
  have : NeZero d' := ⟨hd'.ne'⟩
  have : Fact (1 < d') := ⟨hlt⟩
  have hcov : volume (⋃ i, D' i) ≠ 0 := by
    intro h0
    have hu : volume (univ : Set ℝ) ≤ volume (⋃ i, D' i) + volume (⋃ i, D' i)ᶜ := by
      rw [← union_compl_self (⋃ i, D' i)]; exact measure_union_le _ _
    rw [h0, hD'.null_compl, add_zero, Real.volume_univ] at hu
    exact absurd hu (by simp)
  obtain ⟨i, hi⟩ : ∃ i, 0 < volume (D' i) := by
    by_contra h
    push Not at h
    exact hcov (measure_iUnion_null fun i => nonpos_iff_eq_zero.1 (h i))
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hi.ne'
  have hne : i ≠ i + 1 := fun h => by
    have h' := congrArg (fun t => t - i) h
    simp at h'
  have hsum : P x (D' i) + P x (D' (i + 1)) ≤ 1 := by
    rw [← measure_union (hD'.disjoint i (i + 1) hne) (hD'.measurableSet _)]
    exact prob_le_one
  rw [hD'.step i x hx] at hsum
  have h0 : P x (D' i) = 0 := by
    have h' : P x (D' i) + 1 ≤ 0 + 1 := by rwa [zero_add]
    exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h')
  exact (hstep x (hD'.measurableSet i) hi).ne' h0

/-! ### Geometric ergodicity in the region (11.36) -/

variable (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **The real form of (V4) on (11.36)** (STEP 2, MT p. 541): if `θ(1) < 1`, `θ(M) < 1` and
`θ(1)θ(M) < 1`, then for slopes `a, b > 0` as in Proposition 11.4.5, `V = 1 + a x⁺ + b x⁻`
satisfies `PV ≤ ρV + K 1_{[−R, R]}` with `ρ < 1`. -/
theorem setar_real_driftV4_36 (hW : ∀ j, Integrable (fun w => w) (Γ j))
    (hθ : θ 0 < 1 ∧ θ (Fin.last m) < 1 ∧ θ 0 * θ (Fin.last m) < 1) :
    ∃ a b ρ R K : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ K ∧ ∀ x,
      Integrable (fun y => 1 + pwLin a b y) (setarKernel Γ φ θ r x) ∧
      ∫ y, (1 + pwLin a b y) ∂setarKernel Γ φ θ r x ≤
        ρ * (1 + pwLin a b x) + (Icc (-R) R).indicator (fun _ => K) x := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨a, b, ha, hb, hM, h1⟩ := setar_interior_slopes hθ.1 hθ.2.1 hθ.2.2
  set M := Fin.last m
  set sM := a * max (θ M) 0 + b * max (-θ M) 0 with hsM
  set s1 := b * max (θ 0) 0 + a * max (-θ 0) 0 with hs1
  have hsM0 : 0 ≤ sM := by positivity
  have hs10 : 0 ≤ s1 := by positivity
  set ρ0 := max (sM / a) (s1 / b) with hρ0
  have hρ01 : ρ0 < 1 := max_lt ((div_lt_one ha).2 hM) ((div_lt_one hb).2 h1)
  have hρ00 : 0 ≤ ρ0 := le_max_of_le_left (div_nonneg hsM0 ha.le)
  set ρ := (1 + ρ0) / 2 with hρ
  have hgap : 0 < ρ - ρ0 := by rw [hρ]; linarith
  have hsMa : sM ≤ ρ0 * a := by
    have := le_max_left (sM / a) (s1 / b); rwa [div_le_iff₀ ha] at this
  have hs1b : s1 ≤ ρ0 * b := by
    have := le_max_right (sM / a) (s1 / b); rwa [div_le_iff₀ hb] at this
  set E : Fin (m + 1) → ℝ := fun j => (a + b) * ∫ w, |w| ∂Γ j with hEdef
  have hE0 : ∀ j, 0 ≤ E j := fun j => mul_nonneg (by linarith)
    (integral_nonneg fun w => abs_nonneg w)
  set cM := (a + b) * |φ M| + E M
  set c1 := (a + b) * |φ 0| + E 0
  set R := max (setarBound r) (max ((1 + cM) / ((ρ - ρ0) * a)) ((1 + c1) / ((ρ - ρ0) * b)))
    with hR
  have hR1 : setarBound r ≤ R := le_max_left _ _
  have hRM : (1 + cM) / ((ρ - ρ0) * a) ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR0 : (1 + c1) / ((ρ - ρ0) * b) ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith [one_le_setarBound r]) hR1
  set K := 1 + ∑ j, ((a + b) * (|φ j| + |θ j| * R) + E j) with hKdef
  have hKsum : 0 ≤ ∑ j, ((a + b) * (|φ j| + |θ j| * R) + E j) :=
    Finset.sum_nonneg fun j _ => add_nonneg (mul_nonneg (by linarith)
      (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hRpos.le))) (hE0 j)
  refine ⟨a, b, ρ, R, K, ha, hb, by positivity, by rw [hρ]; linarith, by linarith, fun x => ?_⟩
  obtain ⟨hint, hle⟩ := setar_pwLin_step Γ φ θ r ha.le hb.le hW x
  have hint1 : Integrable (fun y => 1 + pwLin a b y) (setarKernel Γ φ θ r x) :=
    (integrable_const 1).add hint
  refine ⟨hint1, ?_⟩
  have hsplit : ∫ y, (1 + pwLin a b y) ∂setarKernel Γ φ θ r x =
      1 + ∫ y, pwLin a b y ∂setarKernel Γ φ θ r x := by
    rw [integral_add (integrable_const 1) hint, integral_const, probReal_univ, one_smul]
  rw [hsplit]
  have hV0 : 0 ≤ pwLin a b x := pwLin_nonneg ha.le hb.le x
  by_cases hx : x ∈ Icc (-R) R
  · rw [indicator_of_mem hx]
    have hxa : |x| ≤ R := abs_le.2 hx
    set j := setarRegime r x
    have hb1 : pwLin a b (φ j + θ j * x) ≤ (a + b) * (|φ j| + |θ j| * R) := by
      refine (pwLin_le_abs ha.le hb.le _).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      calc |φ j + θ j * x| ≤ |φ j| + |θ j| * |x| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |φ j| + |θ j| * R := by gcongr
    have hterm : (a + b) * (|φ j| + |θ j| * R) + E j ≤
        ∑ j, ((a + b) * (|φ j| + |θ j| * R) + E j) :=
      Finset.single_le_sum (f := fun j => (a + b) * (|φ j| + |θ j| * R) + E j)
        (fun i _ => add_nonneg (mul_nonneg (by linarith) (add_nonneg (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) hRpos.le))) (hE0 i)) (Finset.mem_univ j)
    have : 0 ≤ ρ * (1 + pwLin a b x) := by positivity
    simp only [hEdef] at hterm
    linarith
  · rw [indicator_of_notMem hx, add_zero]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · -- the bottom regime
      have hxb : x < -setarBound r := by linarith
      have hreg : setarRegime r x = 0 := setarRegime_of_lt r hxb
      rw [hreg] at hle
      have hx0 : x ≤ 0 := by linarith
      have hlip := pwLin_lipschitz ha.le hb.le (φ 0 + θ 0 * x) (θ 0 * x)
      rw [add_sub_cancel_right] at hlip
      have hmul := pwLin_mul_of_nonpos a b (θ 0) hx0
      have hVx : pwLin a b x = b * -x := by
        unfold pwLin; rw [max_eq_right hx0, max_eq_left (by linarith : 0 ≤ -x)]; ring
      rw [hVx]
      have hxR : (1 + c1) / ((ρ - ρ0) * b) ≤ -x := by linarith
      rw [div_le_iff₀ (mul_pos hgap hb)] at hxR
      have hs : s1 * -x ≤ ρ0 * b * -x := mul_le_mul_of_nonneg_right hs1b (by linarith)
      rw [hs1] at hs
      have hE : E 0 = (a + b) * ∫ w, |w| ∂Γ 0 := rfl
      nlinarith [hE0 0]
    · -- the top regime
      have hxb : setarBound r < x := by linarith
      have hreg : setarRegime r x = M := setarRegime_of_bound_lt r hxb
      rw [hreg] at hle
      have hx0 : 0 ≤ x := by linarith [one_le_setarBound r]
      have hlip := pwLin_lipschitz ha.le hb.le (φ M + θ M * x) (θ M * x)
      rw [add_sub_cancel_right] at hlip
      have hmul := pwLin_mul_of_nonneg a b (θ M) hx0
      have hVx : pwLin a b x = a * x := by
        unfold pwLin; rw [max_eq_left hx0, max_eq_right (by linarith : -x ≤ 0)]; ring
      rw [hVx]
      have hxR : (1 + cM) / ((ρ - ρ0) * a) ≤ x := by linarith
      rw [div_le_iff₀ (mul_pos hgap ha)] at hxR
      have hs : sM * x ≤ ρ0 * a * x := mul_le_mul_of_nonneg_right hsMa hx0
      rw [hsM] at hs
      have hE : E M = (a + b) * ∫ w, |w| ∂Γ M := rfl
      nlinarith [hE0 M]

variable (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **(V4) and geometric ergodicity on (11.36)** (STEP 2, MT p. 541): under (SETAR1)–(SETAR2),
if `θ(1) < 1`, `θ(M) < 1` and `θ(1)θ(M) < 1`, then for some `a, b > 0` the function
`V = 1 + a x⁺ + b x⁻` satisfies (V4) with a compact (petite) test set, the chain is positive,
`π(V) < ∞`, and for some `r > 1`, `R < ∞`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for every `x`
(Theorem 15.0.1). -/
theorem setar_geometric_36 (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hW : ∀ j, Integrable (fun w => w) (Γ j))
    (hθ : θ 0 < 1 ∧ θ (Fin.last m) < 1 ∧ θ 0 * θ (Fin.last m) < 1) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (∃ ρ c : ℝ≥0∞, ρ < 1 ∧ c ≠ ∞ ∧ ∃ C : Set ℝ, IsCompact C ∧
        DriftV4 (setarKernel Γ φ θ r) (fun x => ENNReal.ofReal (1 + pwLin a b x)) ρ c C) ∧
      IsPositive (setarKernel Γ φ θ r) volume ∧
      ∀ (π : Measure ℝ) [IsProbabilityMeasure π], IsInvariant (setarKernel Γ φ θ r) π →
        ∫⁻ x, ENNReal.ofReal (1 + pwLin a b x) ∂π ≠ ∞ ∧ ∃ r' : ℝ≥0∞, 1 < r' ∧ r' ≠ ∞ ∧
          ∃ R : ℝ≥0∞, R ≠ ∞ ∧ ∀ x, ∑' n, r' ^ n * fNorm (fun x => ENNReal.ofReal (1 + pwLin a b x))
            ((setarKernel Γ φ θ r ^ n : Kernel ℝ ℝ) x) π ≤
              R * ENNReal.ofReal (1 + pwLin a b x) := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, hsmall, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  obtain ⟨a, b, ρ, R, K, ha, hb, hρ0, hρ1, hK0, hdr⟩ := setar_real_driftV4_36 Γ φ θ r hW hθ
  set V : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 + pwLin a b x) with hVdef
  have hVm : Measurable V := ENNReal.measurable_ofReal.comp (measurable_const.add
    (measurable_pwLin a b))
  have hV1 : ∀ x, 1 ≤ V x := fun x => by
    rw [hVdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [pwLin_nonneg ha.le hb.le x])
  have hdrift : DriftV4 (setarKernel Γ φ θ r) V (ENNReal.ofReal ρ) (ENNReal.ofReal K)
      (Icc (-R) R) := by
    intro x
    obtain ⟨hint, hle⟩ := hdr x
    have hnn : 0 ≤ 1 + pwLin a b x := by linarith [pwLin_nonneg ha.le hb.le x]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by
      change (0 : ℝ) ≤ 1 + pwLin a b y
      linarith [pwLin_nonneg ha.le hb.le y])]
    refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
    have hind : 0 ≤ (Icc (-R) R).indicator (fun _ => K) x := indicator_nonneg (fun _ _ => hK0) x
    rw [ENNReal.ofReal_add (mul_nonneg hρ0 hnn) hind, ENNReal.ofReal_mul hρ0]
    congr 1
    by_cases hx : x ∈ Icc (-R) R <;> simp [hx]
  have hρ1' : ENNReal.ofReal ρ < 1 := by rw [← ENNReal.ofReal_one]; exact
    (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hρ1
  have hpet : IsPetite (setarKernel Γ φ θ r) (Icc (-R) R) := (hsmall _ isCompact_Icc).isPetite
  obtain ⟨hpos, hgeo⟩ := geometric_ergodic_of_driftV4 hψ (setar_isAperiodic Γ φ θ r h2) hVm hV1
    hρ1' ENNReal.ofReal_ne_top hpet hdrift (x₀ := 0) ENNReal.ofReal_ne_top
  exact ⟨a, b, ha, hb, ⟨_, _, hρ1', ENNReal.ofReal_ne_top, _, isCompact_Icc, hdrift⟩, hpos,
    fun π _ hπ => hgeo π hπ⟩

/-! ### The correction to STEP 2 -/

variable (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Linear test functions do not satisfy (V4) at a unit-slope top end** (correction to STEP 2,
MT p. 541): if `θ(M) = 1` and the noises have mean zero, then for `V = c + a x⁺ + b x⁻`
(`a > 0`, `b ≥ 0`) there are no `ρ < 1` and `L` with `PV ≤ ρV + L`, since
`PV(x) ≥ V(x) + aφ(M)` for large `x`. This covers (11.38) and (11.39). -/
theorem setar_not_linear_driftV4_top (hW : ∀ j, Integrable (fun w => w) (Γ j))
    (hW0 : ∀ j, ∫ w, w ∂Γ j = 0) (hθM : θ (Fin.last m) = 1) {a b c : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) :
    ¬ ∃ ρ L : ℝ, ρ < 1 ∧ ∀ x, ∫ y, (c + pwLin a b y) ∂setarKernel Γ φ θ r x ≤
      ρ * (c + pwLin a b x) + L := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  rintro ⟨ρ, L, hρ, h⟩
  set M := Fin.last m
  set Q := (ρ * c + L - c - a * φ M) / ((1 - ρ) * a) with hQ
  set x := max (setarBound r) Q + 1 with hxdef
  have hm1 := le_max_left (setarBound r) Q
  have hm2 := le_max_right (setarBound r) Q
  have hx1 : setarBound r < x := by rw [hxdef]; linarith
  have hx2 : Q < x := by rw [hxdef]; linarith
  have hx0 : 0 ≤ x := by linarith [one_le_setarBound r]
  have hreg : setarRegime r x = M := setarRegime_of_bound_lt r hx1
  obtain ⟨hint, -⟩ := setar_pwLin_step Γ φ θ r ha.le hb hW x
  have hlow : c + a * (φ M + x) ≤ ∫ y, (c + pwLin a b y) ∂setarKernel Γ φ θ r x := by
    rw [integral_add (integrable_const c) hint, integral_const, probReal_univ, one_smul,
      setarKernel_eq_map, integral_map (measurable_const_add _).aemeasurable
        (measurable_pwLin a b).aestronglyMeasurable, hreg, hθM, one_mul,
      integral_pwLin_shift_pos (Γ M) (hW M) (hW0 M)]
    have : 0 ≤ (a + b) * ∫ w, max (-(φ M + x) + -w) 0 ∂Γ M :=
      mul_nonneg (by linarith) (integral_nonneg fun w => le_max_right _ _)
    linarith
  have hVx : pwLin a b x = a * x := by
    unfold pwLin; rw [max_eq_left hx0, max_eq_right (by linarith : -x ≤ 0)]; ring
  have hup := h x
  rw [hVx] at hup
  rw [hQ, div_lt_iff₀ (mul_pos (by linarith) ha)] at hx2
  nlinarith

variable (Γ : Fin (m + 1) → Measure ℝ) [∀ j, IsProbabilityMeasure (Γ j)]
  (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) in
/-- **Linear test functions do not satisfy (V4) at a unit-slope bottom end** (correction to
STEP 2, MT p. 541): if `θ(1) = 1` and the noises have mean zero, then for
`V = c + a x⁺ + b x⁻` (`a ≥ 0`, `b > 0`) there are no `ρ < 1` and `L` with `PV ≤ ρV + L`. This
covers (11.37) and (11.39). -/
theorem setar_not_linear_driftV4_bot (hW : ∀ j, Integrable (fun w => w) (Γ j))
    (hW0 : ∀ j, ∫ w, w ∂Γ j = 0) (hθ0 : θ 0 = 1) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ¬ ∃ ρ L : ℝ, ρ < 1 ∧ ∀ x, ∫ y, (c + pwLin a b y) ∂setarKernel Γ φ θ r x ≤
      ρ * (c + pwLin a b x) + L := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  rintro ⟨ρ, L, hρ, h⟩
  set Q := (ρ * c + L - c + b * φ 0) / ((1 - ρ) * b) with hQ
  set y := max (setarBound r) Q + 1 with hydef
  set x := -y with hxdef
  have hm1 := le_max_left (setarBound r) Q
  have hm2 := le_max_right (setarBound r) Q
  have hy1 : setarBound r < y := by rw [hydef]; linarith
  have hy2 : Q < y := by rw [hydef]; linarith
  have hx1 : x < -setarBound r := by rw [hxdef]; linarith
  have hx0 : x ≤ 0 := by rw [hxdef]; linarith [one_le_setarBound r]
  have hreg : setarRegime r x = 0 := setarRegime_of_lt r hx1
  obtain ⟨hint, -⟩ := setar_pwLin_step Γ φ θ r ha hb.le hW x
  have hlow : c - b * (φ 0 + x) ≤ ∫ y, (c + pwLin a b y) ∂setarKernel Γ φ θ r x := by
    rw [integral_add (integrable_const c) hint, integral_const, probReal_univ, one_smul,
      setarKernel_eq_map, integral_map (measurable_const_add _).aemeasurable
        (measurable_pwLin a b).aestronglyMeasurable, hreg, hθ0, one_mul,
      integral_pwLin_shift_neg (Γ 0) (hW 0) (hW0 0)]
    have : 0 ≤ (a + b) * ∫ w, max (φ 0 + x + w) 0 ∂Γ 0 :=
      mul_nonneg (by linarith) (integral_nonneg fun w => le_max_right _ _)
    linarith
  have hVx : pwLin a b x = b * -x := by
    unfold pwLin; rw [max_eq_right hx0, max_eq_left (by linarith : 0 ≤ -x)]; ring
  have hup := h x
  rw [hVx] at hup
  rw [hQ, div_lt_iff₀ (mul_pos (by linarith) hb)] at hy2
  have hxy : -x = y := by rw [hxdef, neg_neg]
  rw [hxy] at hup
  nlinarith

end MeynTweedie.GeneralizedDrift
