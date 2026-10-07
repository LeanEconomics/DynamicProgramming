/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Feller
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Certainty equivalents

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.4 (pp. 225–230).

`L∞` is represented by functions `Z : Ω → ℝ` that are a.e. strongly measurable and essentially
bounded (`IsLInf`); a functional on `L∞` is a map on functions whose axioms are imposed on `L∞`.
Monotonicity in the a.e. order makes it constant on a.e. classes.

* Risk measures (R1)–(R2) and certainty equivalents (C1)–(C2); **Exercise 7.2.5**: `ℰ` is a
  certainty equivalent iff `−ℰ` is a risk measure, and convex combinations of certainty
  equivalents are certainty equivalents.
* Convex and coherent risk measures; concave and coherent certainty equivalents; a coherent
  certainty equivalent is superadditive.
* Examples: the mean `𝔼` (coherent); the pessimistic certainty equivalent
  `ℰ_p(Z) = sup{a : ℙ{Z < a} = 0} = ess inf Z` (coherent); the entropic certainty equivalent
  `ℰ^θ(Z) = θ⁻¹ ln 𝔼 exp(θZ)`, `θ ≠ 0` ((7.21) is `θ = −γ`); the Kreps–Porteus expectation
  `𝒦(Z) = (𝔼 Z^{1−γ})^{1/(1−γ)}` fails cash invariance (a two-point example with `γ = 2`).
* Continuity (§7.2.4.3): **Example 7.2.1** (`𝔼`) and **Exercise 7.2.6** (`ℰ^θ`).

The dual representation (Theorem 7.2.9, Föllmer–Schied) and its instances (7.22), and the quantile
and CVaR certainty equivalents with Example 7.2.2, are not formalised; see the corrections file.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.RecursiveDecisionProcesses

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- `Z ∈ L∞(Ω, ℱ, ℙ)`: `Z` is a.e. strongly measurable and `|Z| ≤ N` almost surely. -/
def IsLInf (Z : Ω → ℝ) : Prop := AEStronglyMeasurable Z P ∧ ∃ N, ∀ᵐ ω ∂P, |Z ω| ≤ N

/-- A **risk measure** (§7.2.4): (R1) monotonicity, `Z ≤ Z'` a.s. implies `ℛ(Z') ≤ ℛ(Z)`, and (R2)
cash invariance, `ℛ(Z + a) = ℛ(Z) − a`. -/
structure IsRiskMeasure (R : (Ω → ℝ) → ℝ) : Prop where
  mono : ∀ Z Z', IsLInf P Z → IsLInf P Z' → Z ≤ᵐ[P] Z' → R Z' ≤ R Z
  cash : ∀ Z, IsLInf P Z → ∀ a : ℝ, R (fun ω => Z ω + a) = R Z - a

/-- A **certainty equivalent** (§7.2.4): (C1) monotonicity, `Z ≤ Z'` a.s. implies
`ℰ(Z) ≤ ℰ(Z')`, and (C2) cash invariance, `ℰ(Z + a) = ℰ(Z) + a`. -/
structure IsCertEquiv (E : (Ω → ℝ) → ℝ) : Prop where
  mono : ∀ Z Z', IsLInf P Z → IsLInf P Z' → Z ≤ᵐ[P] Z' → E Z ≤ E Z'
  cash : ∀ Z, IsLInf P Z → ∀ a : ℝ, E (fun ω => Z ω + a) = E Z + a

variable {P}

theorem IsLInf.add_const {Z : Ω → ℝ} (hZ : IsLInf P Z) (a : ℝ) : IsLInf P fun ω => Z ω + a := by
  obtain ⟨hm, N, hN⟩ := hZ
  refine ⟨hm.add aestronglyMeasurable_const, N + |a|, ?_⟩
  filter_upwards [hN] with ω hω
  exact (abs_add_le _ _).trans (add_le_add hω le_rfl)

theorem IsLInf.const_mul {Z : Ω → ℝ} (hZ : IsLInf P Z) (c : ℝ) : IsLInf P fun ω => c * Z ω := by
  obtain ⟨hm, N, hN⟩ := hZ
  refine ⟨hm.const_mul c, |c| * N, ?_⟩
  filter_upwards [hN] with ω hω
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg c)

theorem IsLInf.add {Z Z' : Ω → ℝ} (hZ : IsLInf P Z) (hZ' : IsLInf P Z') :
    IsLInf P fun ω => Z ω + Z' ω := by
  obtain ⟨hm, N, hN⟩ := hZ
  obtain ⟨hm', N', hN'⟩ := hZ'
  refine ⟨hm.add hm', N + N', ?_⟩
  filter_upwards [hN, hN'] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem isLInf_const (a : ℝ) : IsLInf P fun _ => a :=
  ⟨aestronglyMeasurable_const, |a|, Eventually.of_forall fun _ => le_rfl⟩

theorem IsLInf.integrable [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ : IsLInf P Z) : Integrable Z P :=
  Integrable.of_bound hZ.1 hZ.2.choose (by simpa [Real.norm_eq_abs] using hZ.2.choose_spec)

/-- **Exercise 7.2.5 (i)** (p. 226): `ℰ` is a certainty equivalent iff `ℛ = −ℰ` is a risk
measure. -/
theorem exercise_7_2_5_i (E : (Ω → ℝ) → ℝ) :
    IsCertEquiv P E ↔ IsRiskMeasure P fun Z => -E Z := by
  constructor
  · rintro ⟨hm, hc⟩
    exact ⟨fun Z Z' hZ hZ' h => neg_le_neg (hm Z Z' hZ hZ' h), fun Z hZ a => by
      rw [hc Z hZ a]
      ring⟩
  · rintro ⟨hm, hc⟩
    exact ⟨fun Z Z' hZ hZ' h => neg_le_neg_iff.1 (hm Z Z' hZ hZ' h), fun Z hZ a => by
      have := hc Z hZ a
      linarith⟩

/-- **Exercise 7.2.5 (ii)** (p. 226): a convex combination of certainty equivalents is a certainty
equivalent. -/
theorem exercise_7_2_5_ii {E₀ E₁ : (Ω → ℝ) → ℝ} (h₀ : IsCertEquiv P E₀) (h₁ : IsCertEquiv P E₁)
    {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    IsCertEquiv P fun Z => lam * E₀ Z + (1 - lam) * E₁ Z := by
  refine ⟨fun Z Z' hZ hZ' h => ?_, fun Z hZ a => ?_⟩
  · exact add_le_add (mul_le_mul_of_nonneg_left (h₀.mono Z Z' hZ hZ' h) hl0)
      (mul_le_mul_of_nonneg_left (h₁.mono Z Z' hZ hZ' h) (sub_nonneg.2 hl1))
  · rw [h₀.cash Z hZ a, h₁.cash Z hZ a]
    ring

variable (P)

/-- A convex risk measure (p. 226). -/
def IsConvexRisk (R : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z Z', IsLInf P Z → IsLInf P Z' → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    R (fun ω => lam * Z ω + (1 - lam) * Z' ω) ≤ lam * R Z + (1 - lam) * R Z'

/-- A concave certainty equivalent (p. 226). -/
def IsConcaveCE (E : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z Z', IsLInf P Z → IsLInf P Z' → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    lam * E Z + (1 - lam) * E Z' ≤ E (fun ω => lam * Z ω + (1 - lam) * Z' ω)

/-- Positive homogeneity: `F(λZ) = λF(Z)` for `λ > 0` (p. 227). -/
def IsPosHomogeneous (F : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z, IsLInf P Z → ∀ lam : ℝ, 0 < lam → F (fun ω => lam * Z ω) = lam * F Z

/-- A coherent risk measure: convex and positively homogeneous (p. 227). -/
def IsCoherentRisk (R : (Ω → ℝ) → ℝ) : Prop :=
  IsRiskMeasure P R ∧ IsConvexRisk P R ∧ IsPosHomogeneous P R

/-- A coherent certainty equivalent: concave and positively homogeneous (p. 227). -/
def IsCoherentCE (E : (Ω → ℝ) → ℝ) : Prop :=
  IsCertEquiv P E ∧ IsConcaveCE P E ∧ IsPosHomogeneous P E

variable {P}

/-- `ℛ` is a convex (coherent) risk measure iff `ℰ = −ℛ` is a concave (coherent) certainty
equivalent (p. 226). -/
theorem isCoherentRisk_neg_iff (E : (Ω → ℝ) → ℝ) :
    IsCoherentRisk P (fun Z => -E Z) ↔ IsCoherentCE P E := by
  refine and_congr (exercise_7_2_5_i E).symm (and_congr ?_ ?_)
  · refine forall_congr' fun Z => forall_congr' fun Z' => forall_congr' fun hZ =>
      forall_congr' fun hZ' => forall_congr' fun lam => forall_congr' fun _ =>
        forall_congr' fun _ => ?_
    constructor <;> intro h <;> linarith
  · refine forall_congr' fun Z => forall_congr' fun hZ => forall_congr' fun lam =>
      forall_congr' fun _ => ?_
    constructor <;> intro h <;> linarith

/-- A coherent certainty equivalent is superadditive: `ℰ(Z) + ℰ(Z') ≤ ℰ(Z + Z')` (p. 227). -/
theorem IsCoherentCE.superadditive {E : (Ω → ℝ) → ℝ} (h : IsCoherentCE P E) {Z Z' : Ω → ℝ}
    (hZ : IsLInf P Z) (hZ' : IsLInf P Z') : E Z + E Z' ≤ E fun ω => Z ω + Z' ω := by
  have hc := h.2.1 Z Z' hZ hZ' (1 / 2) (by norm_num) (by norm_num)
  have hh := h.2.2 _ ((hZ.const_mul (1 / 2)).add (hZ'.const_mul (1 - 1 / 2))) 2 two_pos
  have heq : (fun ω => 2 * ((1 / 2) * Z ω + (1 - 1 / 2) * Z' ω)) = fun ω => Z ω + Z' ω :=
    funext fun ω => by ring
  rw [heq] at hh
  rw [hh]
  linarith

/-! ### The mean -/

variable (P) in
/-- The risk-neutral certainty equivalent `ℰ(Z) = 𝔼 Z` (p. 228). -/
noncomputable def meanCE (Z : Ω → ℝ) : ℝ := ∫ ω, Z ω ∂P

variable [IsProbabilityMeasure P]

/-- `𝔼` is a coherent certainty equivalent (p. 228). -/
theorem meanCE_isCoherent : IsCoherentCE P (meanCE P) := by
  refine ⟨⟨fun Z Z' hZ hZ' h => integral_mono_ae hZ.integrable hZ'.integrable h,
    fun Z hZ a => ?_⟩, fun Z Z' hZ hZ' lam _ _ => le_of_eq ?_, fun Z hZ lam _ => ?_⟩
  · rw [meanCE, meanCE, integral_add hZ.integrable (integrable_const a), integral_const,
      probReal_univ, one_smul]
  · rw [meanCE, meanCE, meanCE, integral_add ((hZ.const_mul lam).integrable)
      ((hZ'.const_mul (1 - lam)).integrable), integral_const_mul, integral_const_mul]
  · rw [meanCE, meanCE, integral_const_mul]

variable (P) in
/-- `IsContinuousCE`: `ℰ(Zₙ) → ℰ(Z)` whenever `Zₙ → Z` almost surely with `|Zₙ| ≤ M`
(§7.2.4.3). -/
def IsContinuousCE (E : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (Zs : ℕ → Ω → ℝ) (Z : Ω → ℝ) (M : ℝ), (∀ n, AEStronglyMeasurable (Zs n) P) →
    (∀ n, ∀ᵐ ω ∂P, |Zs n ω| ≤ M) → IsLInf P Z →
    (∀ᵐ ω ∂P, Tendsto (fun n => Zs n ω) atTop (𝓝 (Z ω))) →
    Tendsto (fun n => E (Zs n)) atTop (𝓝 (E Z))

/-- **Example 7.2.1** (p. 229): `𝔼` is continuous (dominated convergence). -/
theorem example_7_2_1 : IsContinuousCE P (meanCE P) := fun Zs Z M hm hb _ hlim =>
  tendsto_integral_of_dominated_convergence (fun _ => M) hm (integrable_const M)
    (fun n => by simpa [Real.norm_eq_abs] using hb n) hlim

/-! ### The pessimistic certainty equivalent -/

variable (P) in
/-- The pessimistic certainty equivalent `ℰ_p(Z) = sup{a : ℙ{Z < a} = 0}` (p. 228). -/
noncomputable def pessCE (Z : Ω → ℝ) : ℝ := sSup {a : ℝ | P {ω | Z ω < a} = 0}

omit [IsProbabilityMeasure P] in
theorem mem_pess_iff {Z : Ω → ℝ} {a : ℝ} : P {ω | Z ω < a} = 0 ↔ ∀ᵐ ω ∂P, a ≤ Z ω := by
  rw [ae_iff]
  simp only [not_le]

omit [IsProbabilityMeasure P] in
theorem pess_nonempty {Z : Ω → ℝ} (hZ : IsLInf P Z) : {a : ℝ | P {ω | Z ω < a} = 0}.Nonempty := by
  obtain ⟨-, N, hN⟩ := hZ
  exact ⟨-N, mem_pess_iff.2 (hN.mono fun ω hω => neg_le_of_abs_le hω)⟩

theorem pess_bddAbove {Z : Ω → ℝ} (hZ : IsLInf P Z) : BddAbove {a : ℝ | P {ω | Z ω < a} = 0} := by
  obtain ⟨-, N, hN⟩ := hZ
  refine ⟨N, fun a ha => ?_⟩
  obtain ⟨ω, h1, h2⟩ := ((mem_pess_iff.1 ha).and hN).exists
  exact h1.trans (le_of_abs_le h2)

omit [IsProbabilityMeasure P] in
/-- `Z ≥ ℰ_p(Z)` almost surely. -/
theorem ae_pess_le {Z : Ω → ℝ} (hZ : IsLInf P Z) : ∀ᵐ ω ∂P, pessCE P Z ≤ Z ω := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, pessCE P Z - 1 / (n + 1) ≤ Z ω := fun n => by
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup (pess_nonempty hZ)
      (sub_lt_self (pessCE P Z) (Nat.one_div_pos_of_nat (n := n)))
    exact (mem_pess_iff.1 ha).mono fun ω hω => hlt.le.trans hω
  filter_upwards [ae_all_iff.2 hn] with ω hω
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [hω n]

theorem le_pess {Z : Ω → ℝ} (hZ : IsLInf P Z) {a : ℝ} (ha : ∀ᵐ ω ∂P, a ≤ Z ω) : a ≤ pessCE P Z :=
  le_csSup (pess_bddAbove hZ) (mem_pess_iff.2 ha)

/-- The pessimistic certainty equivalent is a coherent certainty equivalent (p. 228). -/
theorem pessCE_isCoherent : IsCoherentCE P (pessCE P) := by
  refine ⟨⟨fun Z Z' hZ hZ' h => le_pess hZ' ((ae_pess_le hZ).mp (h.mono fun ω h1 h2 =>
    h2.trans h1)), fun Z hZ a => le_antisymm ?_ ?_⟩, fun Z Z' hZ hZ' lam hl0 hl1 => ?_,
    fun Z hZ lam hl => le_antisymm ?_ ?_⟩
  · -- `ℰ_p(Z + a) ≤ ℰ_p(Z) + a`
    have h := ae_pess_le (hZ.add_const a)
    have : pessCE P (fun ω => Z ω + a) - a ≤ pessCE P Z :=
      le_pess hZ (h.mono fun ω hω => by linarith)
    linarith
  · exact le_pess (hZ.add_const a) ((ae_pess_le hZ).mono fun ω hω => by linarith)
  · refine le_pess ((hZ.const_mul lam).add (hZ'.const_mul (1 - lam))) ?_
    filter_upwards [ae_pess_le hZ, ae_pess_le hZ'] with ω h1 h2
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hl0)
      (mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hl1))
  · have h := ae_pess_le (hZ.const_mul lam)
    have : pessCE P (fun ω => lam * Z ω) / lam ≤ pessCE P Z :=
      le_pess hZ (h.mono fun ω hω => by rw [div_le_iff₀ hl]; linarith)
    rwa [div_le_iff₀ hl, mul_comm] at this
  · exact le_pess (hZ.const_mul lam) ((ae_pess_le hZ).mono fun ω hω =>
      mul_le_mul_of_nonneg_left hω hl.le)

/-! ### The entropic certainty equivalent -/

variable (P) in
/-- The entropic certainty equivalent `ℰ^θ(Z) = θ⁻¹ ln 𝔼 exp(θZ)`; (7.21) is `θ = −γ`. -/
noncomputable def entropicCE (θ : ℝ) (Z : Ω → ℝ) : ℝ := θ⁻¹ * Real.log (∫ ω, Real.exp (θ * Z ω) ∂P)

theorem integrable_exp {Z : Ω → ℝ} (hZ : IsLInf P Z) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * Z ω)) P := by
  obtain ⟨hm, N, hN⟩ := hZ
  refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable (hm.const_mul θ))
    (Real.exp (|θ| * N)) ?_
  filter_upwards [hN] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg θ)

theorem integral_exp_pos' {Z : Ω → ℝ} (hZ : IsLInf P Z) (θ : ℝ) :
    0 < ∫ ω, Real.exp (θ * Z ω) ∂P :=
  integral_exp_pos (integrable_exp hZ θ)

/-- The entropic certainty equivalent is a certainty equivalent for every `θ ≠ 0`. -/
theorem entropicCE_isCertEquiv {θ : ℝ} (hθ : θ ≠ 0) : IsCertEquiv P (entropicCE P θ) := by
  refine ⟨fun Z Z' hZ hZ' h => ?_, fun Z hZ a => ?_⟩
  · rcases lt_or_gt_of_ne hθ with hneg | hpos
    · have hle : ∫ ω, Real.exp (θ * Z' ω) ∂P ≤ ∫ ω, Real.exp (θ * Z ω) ∂P :=
        integral_mono_ae (integrable_exp hZ' θ) (integrable_exp hZ θ)
          (h.mono fun ω hω => Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hω hneg.le))
      exact mul_le_mul_of_nonpos_left (Real.log_le_log (integral_exp_pos' hZ' θ) hle)
        (inv_nonpos.2 hneg.le)
    · have hle : ∫ ω, Real.exp (θ * Z ω) ∂P ≤ ∫ ω, Real.exp (θ * Z' ω) ∂P :=
        integral_mono_ae (integrable_exp hZ θ) (integrable_exp hZ' θ)
          (h.mono fun ω hω => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hpos.le))
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (integral_exp_pos' hZ θ) hle)
        (inv_nonneg.2 hpos.le)
  · have heq : ∫ ω, Real.exp (θ * (Z ω + a)) ∂P =
        Real.exp (θ * a) * ∫ ω, Real.exp (θ * Z ω) ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      change Real.exp (θ * (Z ω + a)) = Real.exp (θ * a) * Real.exp (θ * Z ω)
      rw [← Real.exp_add]
      ring_nf
    rw [entropicCE, heq, Real.log_mul (Real.exp_pos _).ne' (integral_exp_pos' hZ θ).ne',
      Real.log_exp, entropicCE]
    field_simp
    ring

/-- **Exercise 7.2.6** (p. 230): the entropic certainty equivalent is continuous. -/
theorem exercise_7_2_6 (θ : ℝ) : IsContinuousCE P (entropicCE P θ) := by
  intro Zs Z M hm hb hZ hlim
  have hint : Tendsto (fun n => ∫ ω, Real.exp (θ * Zs n ω) ∂P) atTop
      (𝓝 (∫ ω, Real.exp (θ * Z ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (|θ| * M))
      (fun n => Real.continuous_exp.comp_aestronglyMeasurable ((hm n).const_mul θ))
      (integrable_const _) (fun n => ?_) ?_
    · filter_upwards [hb n] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg θ)
    · filter_upwards [hlim] with ω hω
      exact (Real.continuous_exp.tendsto _).comp (hω.const_mul θ)
  exact (hint.log (integral_exp_pos' hZ θ).ne').const_mul θ⁻¹

/-! ### Kreps–Porteus expectations -/

variable (P) in
/-- The Kreps–Porteus expectation `𝒦(Z) = (𝔼 Z^{1−γ})^{1/(1−γ)}` (p. 229). -/
noncomputable def kpExp (γ : ℝ) (Z : Ω → ℝ) : ℝ := (∫ ω, Z ω ^ (1 - γ) ∂P) ^ (1 - γ)⁻¹

/-- The Kreps–Porteus expectation fails cash invariance (p. 229): with `γ = 2`, `Ω = {0, 1}`
uniform and `Z = (1, 2)`, `𝒦(Z + 1) = 12/5 ≠ 7/3 = 𝒦(Z) + 1`. -/
theorem kpExp_not_cash_invariant :
    ∃ (Q : Measure Bool) (_ : IsProbabilityMeasure Q) (Z : Bool → ℝ) (a : ℝ),
      IsLInf Q Z ∧ kpExp Q 2 (fun ω => Z ω + a) ≠ kpExp Q 2 Z + a := by
  let Q : Measure Bool := (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) •
    Measure.dirac false
  have hQ : IsProbabilityMeasure Q := ⟨by
    simp only [Q, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.add_halves]⟩
  have hint : ∀ f : Bool → ℝ, ∫ ω, f ω ∂Q = f true / 2 + f false / 2 := fun f => by
    have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac true) :=
      (integrable_dirac (f := f) (by simp)).smul_measure (by simp)
    have h2 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac false) :=
      (integrable_dirac (f := f) (by simp)).smul_measure (by simp)
    rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  refine ⟨Q, hQ, fun ω => if ω then 1 else 2, 1,
    ⟨(measurable_of_countable _).aestronglyMeasurable, 2, ?_⟩, ?_⟩
  · exact Eventually.of_forall fun ω => by cases ω <;> norm_num
  · simp only [kpExp, hint]
    norm_num [Real.rpow_neg_one]

end SargentStachurski.RecursiveDecisionProcesses
