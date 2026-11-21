/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.KUStochastic
import RecursiveUtility.KUKoopmans
import RecursiveUtility.SSEpsteinZin
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Epstein–Zin preferences (§20.2.1, (20.3)–(20.5))

Miao §20.2.1, pp. 685–687.

* `ku_kpCE`: the Kreps–Porteus conditional certainty equivalent
  `M_t(x) = (E_t[x^{1−γ}])^{1/(1−γ)}`; `ku_kpCE_eq_kpR` identifies it at a node with the
  Sargent–Stachurski operator `SS.kpR`; `ku_kpCE_isCE`: it is a conditional certainty equivalent
  (Definition 20.2.3) on positive random variables; `ku_kpCE_mono`, `ku_kpCE_strictMono`.
* `eq_20_3`: with the CES aggregator, (20.2) is the Epstein–Zin recursion (20.3);
  `ku_ez_dynConsistent`: an Epstein–Zin utility with positive values is dynamically consistent.
* `ku_ez_rra`: the relative risk aversion of the certainty equivalent is `γ`; `ku_ez_eis`: the
  EIS of the aggregator is `1/ρ` (via `SS.ces_eis`).
* `ku_ez_expected_power`, `ku_ez_expected_power_sum`: for `γ = ρ`, `V_t = U_t^{1−ρ}` is the
  time-additive expected power utility.
* `ku_ez_markov`, `ku_ez_markov_homogeneous`: for stationary Markov consumption `c_t = c(s_t)`
  and irreducible `P`, (20.3) has a unique positive Markov solution `U_t = v(s_t)`, and it is
  homogeneous of degree one ("scale-invariant", p. 686).
* `ku_expCE`, `ku_expCE_isCE`, `ku_expCE_translation`, `eq_20_4`: Weil's exponential certainty
  equivalent, its translation invariance, and (20.4).
* `ku_ces_limit`, `eq_20_5`: as `ρ → 1` the CES aggregator tends to `x^{1−β}y^β`, and then
  `V_t = log U_t` satisfies (20.5).
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-- Miao, p. 686: the Kreps–Porteus conditional certainty equivalent
`M_t(x) = (E_t[x^{1−γ}])^{1/(1−γ)}`. -/
noncomputable def ku_kpCE (P : Matrix S S ℝ) (γ : ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) :
    (ℕ → S) → ℝ :=
  fun ω => ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω ^ (1 - γ)⁻¹

theorem ku_kpCE_eq_kpR (P : Matrix S S ℝ) (γ : ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) (ω : ℕ → S) :
    ku_kpCE P γ t x ω = SS.kpR (1 - γ) P (fun s' => x (Function.update ω (t + 1) s')) (ω t) := by
  simp [ku_kpCE, ku_E, SS.kpR, Matrix.mulVec, dotProduct]

theorem ku_E_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {x : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω)
    (t : ℕ) (ω : ℕ → S) : 0 < ku_E P t x ω := by
  have := hP.mulVec_pos (f := fun s' => x (Function.update ω (t + 1) s')) (fun _ => hx _) (ω t)
  simpa [ku_E, Matrix.mulVec, dotProduct] using this

theorem ku_kpCE_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) (γ : ℝ) {x : (ℕ → S) → ℝ}
    (hx : ∀ ω, 0 < x ω) (t : ℕ) (ω : ℕ → S) : 0 < ku_kpCE P γ t x ω :=
  Real.rpow_pos_of_pos (ku_E_pos hP (fun ω => Real.rpow_pos_of_pos (hx ω) _) t ω) _

/-- Miao, p. 686: the Kreps–Porteus certainty equivalent is a conditional certainty equivalent
(Definition 20.2.3) on positive random variables. -/
theorem ku_kpCE_isCE {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1) :
    definition_20_2_3 (Set.Ioi 0) (ku_kpCE P γ) := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  intro t
  refine ⟨fun x hx => ?_, ?_, fun α hα _ => ?_⟩
  · have hm : ku_Meas (t + 1) fun ω => x ω ^ (1 - γ) := fun ω ω' h => by
      change x ω ^ (1 - γ) = x ω' ^ (1 - γ)
      rw [hx ω ω' h]
    intro ω ω' h
    simp only [ku_kpCE]
    rw [ku_E_meas P hm ω ω' h]
  · intro x hx
    refine ContinuousAt.continuousWithinAt (continuousAt_pi.2 fun ω => ?_)
    have hpos : ∀ s', 0 < x (Function.update ω (t + 1) s') := fun s' => hx.2 _
    have hin : ContinuousAt (fun y : (ℕ → S) → ℝ =>
        ∑ s', P (ω t) s' * y (Function.update ω (t + 1) s') ^ (1 - γ)) x :=
      tendsto_finsetSum _ fun s' _ => by
        have hc : ContinuousAt (fun y : (ℕ → S) → ℝ => y (Function.update ω (t + 1) s')) x :=
          (continuous_apply _).continuousAt
        exact (continuousAt_const.mul (hc.rpow_const (Or.inl (hpos s').ne'))).tendsto
    have hS : 0 < ∑ s', P (ω t) s' * x (Function.update ω (t + 1) s') ^ (1 - γ) :=
      ku_E_pos hP (x := fun ω' => x ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hx.2 ω') _) t ω
    exact hin.rpow_const (Or.inl hS.ne')
  · funext ω
    simp only [ku_kpCE, ku_E]
    rw [← Finset.sum_mul, hP.rowsum, one_mul]
    exact Real.rpow_rpow_inv (le_of_lt hα) h1

/-- The Kreps–Porteus certainty equivalent is monotone with respect to successors of positive
probability, on positive random variables. -/
theorem ku_kpCE_mono {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1) (t : ℕ)
    {x y : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω) (hy : ∀ ω, 0 < y ω) (ω : ℕ → S)
    (hxy : ∀ s', 0 < P (ω t) s' →
      y (Function.update ω (t + 1) s') ≤ x (Function.update ω (t + 1) s')) :
    ku_kpCE P γ t y ω ≤ ku_kpCE P γ t x ω := by
  have hSx := ku_E_pos hP (x := fun ω' => x ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hx ω') _)
    t ω
  have hSy := ku_E_pos hP (x := fun ω' => y ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hy ω') _)
    t ω
  simp only [ku_kpCE]
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hγ) : (1 : ℝ) - γ ≠ 0) with hneg | hpos
  · have h1 : ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω ≤ ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω :=
      Finset.sum_le_sum fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (hy _) (hxy s' h0) hneg.le) h0.le
    exact Real.rpow_le_rpow_of_nonpos hSx h1 (inv_lt_zero.2 hneg).le
  · have h1 : ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω ≤ ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω :=
      Finset.sum_le_sum fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hy _).le (hxy s' h0) hpos.le) h0.le
    exact Real.rpow_le_rpow hSy.le h1 (inv_pos.2 hpos).le

/-- The Kreps–Porteus certainty equivalent is strictly monotone with respect to successors of
positive probability, on positive random variables. -/
theorem ku_kpCE_strictMono {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1)
    (t : ℕ) {x y : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω) (hy : ∀ ω, 0 < y ω) (ω : ℕ → S)
    (hxy : ∀ s', 0 < P (ω t) s' →
      y (Function.update ω (t + 1) s') ≤ x (Function.update ω (t + 1) s'))
    (hs : ∃ s', 0 < P (ω t) s' ∧
      y (Function.update ω (t + 1) s') < x (Function.update ω (t + 1) s')) :
    ku_kpCE P γ t y ω < ku_kpCE P γ t x ω := by
  obtain ⟨s₁, hp₁, hlt₁⟩ := hs
  have hSx := ku_E_pos hP (x := fun ω' => x ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hx ω') _)
    t ω
  have hSy := ku_E_pos hP (x := fun ω' => y ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hy ω') _)
    t ω
  simp only [ku_kpCE]
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hγ) : (1 : ℝ) - γ ≠ 0) with hneg | hpos
  · have h1 : ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω < ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω :=
      Finset.sum_lt_sum (fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (hy _) (hxy s' h0) hneg.le) h0.le)
        ⟨s₁, Finset.mem_univ _, mul_lt_mul_of_pos_left
          (Real.rpow_lt_rpow_of_neg (hy _) hlt₁ hneg) hp₁⟩
    exact Real.rpow_lt_rpow_of_neg hSx h1 (inv_lt_zero.2 hneg)
  · have h1 : ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω < ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω :=
      Finset.sum_lt_sum (fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hy _).le (hxy s' h0) hpos.le) h0.le)
        ⟨s₁, Finset.mem_univ _, mul_lt_mul_of_pos_left
          (Real.rpow_lt_rpow (hy _).le hlt₁ hpos) hp₁⟩
    exact Real.rpow_lt_rpow hSy.le h1 (inv_pos.2 hpos)

/-- `W(x, y) = ((1 − β)x^{1−ρ} + βy^{1−ρ})^{1/(1−ρ)}` is strictly increasing in `y > 0`. -/
theorem ku_ces_strictMonoOn {β ρ : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ}
    (hx : 0 < x) : StrictMonoOn (ku_ces β ρ x) (Set.Ioi 0) := by
  intro y hy y' hy' hlt
  have hy0 : (0 : ℝ) < y := hy
  have hb : 0 < 1 - β := by linarith
  have hxa := Real.rpow_pos_of_pos hx (1 - ρ)
  have hya := Real.rpow_pos_of_pos hy0 (1 - ρ)
  have hya' := Real.rpow_pos_of_pos (hy0.trans hlt) (1 - ρ)
  unfold ku_ces
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hρ) : (1 : ℝ) - ρ ≠ 0) with hneg | hpos
  · have h1 : y' ^ (1 - ρ) < y ^ (1 - ρ) := Real.rpow_lt_rpow_of_neg hy0 hlt hneg
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by nlinarith) (inv_lt_zero.2 hneg)
  · have h1 : y ^ (1 - ρ) < y' ^ (1 - ρ) := Real.rpow_lt_rpow hy0.le hlt hpos
    exact Real.rpow_lt_rpow (by positivity) (by nlinarith) (inv_pos.2 hpos)

/-- Miao, (20.3), p. 686: with the CES aggregator `W` and the Kreps–Porteus certainty
equivalent,
`W(c_t, M_t(U_{t+1})) = [(1 − β)c_t^{1−ρ} + β(E_t[U_{t+1}^{1−γ}])^{(1−ρ)/(1−γ)}]^{1/(1−ρ)}`
for positive `U_{t+1}`; so (20.2) is the Epstein–Zin recursion (20.3). -/
theorem eq_20_3 {P : Matrix S S ℝ} (hP : SS.IsMarkov P) (β ρ γ : ℝ) {x : ℝ} {t : ℕ}
    {V : (ℕ → S) → ℝ} (hV : ∀ ω, 0 < V ω) (ω : ℕ → S) :
    ku_ces β ρ x (ku_kpCE P γ t V ω) =
      ((1 - β) * x ^ (1 - ρ) +
        β * ku_E P t (fun ω' => V ω' ^ (1 - γ)) ω ^ ((1 - ρ) / (1 - γ))) ^ (1 - ρ)⁻¹ := by
  have hE := ku_E_pos hP (x := fun ω' => V ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hV ω') _)
    t ω
  rw [ku_ces, ku_kpCE, ← Real.rpow_mul hE.le, div_eq_inv_mul]

/-- Miao, p. 684 and (20.3): an Epstein–Zin utility with positive values and `F₀`-measurable
`U₀` is dynamically consistent (Definition 20.2.2). -/
theorem ku_ez_dynConsistent {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {s₀ : S} {β ρ γ : ℝ}
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (ku_ces β ρ) (ku_kpCE P γ)) (hC : ∀ c ∈ C, ∀ t ω, 0 < c t ω)
    (hU : ∀ c ∈ C, ∀ t ω, 0 < U c t ω) (h0 : ∀ c ∈ C, ku_Meas 0 (U c 0)) :
    definition_20_2_2 P s₀ C U :=
  ku_dynConsistent_of_eq_20_2 hP.nonneg hrec (Set.Ioi 0) (Set.Ioi 0)
    (fun c hc t ω => ku_ces_strictMonoOn hρ hβ0 hβ1 (hC c hc t ω)) (fun c hc t ω => hU c hc t ω)
    (fun t _ ω hx => ku_kpCE_pos hP γ hx t ω)
    (fun t _ _ ω hx hy h => ku_kpCE_mono hP hγ t hx hy ω h)
    (fun t _ _ ω hx hy h hs => ku_kpCE_strictMono hP hγ t hx hy ω h hs) h0

/-! ### Risk aversion, intertemporal substitution and the case `γ = ρ` -/

/-- Miao, p. 686: the relative risk aversion of the Kreps–Porteus certainty equivalent is `γ`: for
the vNM index `v(x) = x^{1−γ}`, `v'(x) = (1 − γ)x^{−γ}`, `v''(x) = −γ(1 − γ)x^{−γ−1}` and
`−xv''(x)/v'(x) = γ`. -/
theorem ku_ez_rra {γ x : ℝ} (hγ : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun x => x ^ (1 - γ)) ((1 - γ) * x ^ (-γ)) x ∧
      HasDerivAt (fun x => (1 - γ) * x ^ (-γ)) ((1 - γ) * (-γ * x ^ (-γ - 1))) x ∧
      -x * ((1 - γ) * (-γ * x ^ (-γ - 1))) / ((1 - γ) * x ^ (-γ)) = γ := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  refine ⟨?_, (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul _, ?_⟩
  · have := Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hx.ne')
    rwa [show (1 : ℝ) - γ - 1 = -γ by ring] at this
  · have e : x ^ (-γ - 1) = x ^ (-γ) * x⁻¹ := by
      rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]
    have hxg : 0 < x ^ (-γ) := Real.rpow_pos_of_pos hx _
    rw [e]
    field_simp

/-- Miao, p. 686: the EIS of the Epstein–Zin aggregator is `1/ρ`:
`log(W_x/W_y) = log((1 − β)/β) + ρ log(y/x)`, so `log(y/x) = (log(W_x/W_y) − log((1 − β)/β))/ρ`
has derivative `1/ρ` in `log(W_x/W_y)` (Sargent–Stachurski `SS.ces_eis` with `α = 1 − ρ`). -/
theorem ku_ez_eis {β ρ x y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hρ0 : ρ ≠ 0)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ Wx Wy : ℝ, HasDerivAt (fun x' => ku_ces β ρ x' y) Wx x ∧
      HasDerivAt (fun y' => ku_ces β ρ x y') Wy y ∧ 0 < Wx ∧ 0 < Wy ∧
      Real.log (Wx / Wy) = Real.log ((1 - β) / β) + ρ * Real.log (y / x) ∧
      (Real.log (Wx / Wy) - Real.log ((1 - β) / β)) / ρ = Real.log (y / x) ∧
      ∀ m, HasDerivAt (fun m => (m - Real.log ((1 - β) / β)) / ρ) (1 / ρ) m := by
  obtain ⟨Wx, Wy, h1, h2, h3, h4, h5⟩ :=
    SS.ces_eis (α := 1 - ρ) hβ0 hβ1 (sub_ne_zero.2 (Ne.symm hρ)) hx hy
  rw [show (1 : ℝ) - (1 - ρ) = ρ by ring] at h5
  refine ⟨Wx, Wy, h1, h2, h3, h4, h5, ?_, fun m => ?_⟩
  · rw [h5]
    field_simp
    ring
  · simpa using ((hasDerivAt_id m).sub_const (Real.log ((1 - β) / β))).div_const ρ

/-- Miao, p. 686: for `γ = ρ` the Epstein–Zin utility is the time-additive expected power
utility: `V_t = U_t^{1−ρ}` satisfies `V_t = (1 − β)c_t^{1−ρ} + βE_t[V_{t+1}]`. -/
theorem ku_ez_expected_power {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ : ℝ} (hρ : ρ ≠ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (ku_ces β ρ) (ku_kpCE P ρ)) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C)
    (hcpos : ∀ t ω, 0 < c t ω) (hU : ∀ t ω, 0 < U c t ω) (t : ℕ) (ω : ℕ → S) :
    U c t ω ^ (1 - ρ) =
      (1 - β) * c t ω ^ (1 - ρ) + β * ku_E P t (fun ω' => U c (t + 1) ω' ^ (1 - ρ)) ω := by
  have hE := ku_E_pos hP (x := fun ω' => U c (t + 1) ω' ^ (1 - ρ))
    (fun ω' => Real.rpow_pos_of_pos (hU _ ω') _) t ω
  rw [hrec c hc t ω, ku_ces_rpow hρ hβ0 hβ1 (hcpos t ω).le
    (ku_kpCE_pos hP ρ (hU (t + 1)) t ω).le, ku_kpCE,
    Real.rpow_inv_rpow hE.le (sub_ne_zero.2 (Ne.symm hρ))]

/-- Miao, p. 686: for `γ = ρ` and bounded `c^{1−ρ}`, `U^{1−ρ}`,
`U_t^{1−ρ} = E_t[∑_{s≥t} β^{s−t}(1 − β)c_s^{1−ρ}]`. -/
theorem ku_ez_expected_power_sum {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ : ℝ}
    (hρ : ρ ≠ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (ku_ces β ρ) (ku_kpCE P ρ)) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C)
    (hcpos : ∀ t ω, 0 < c t ω) (hU : ∀ t ω, 0 < U c t ω) {B R : ℝ}
    (hr : ∀ t ω, |(1 - β) * c t ω ^ (1 - ρ)| ≤ R) (hVb : ∀ t ω, |U c t ω ^ (1 - ρ)| ≤ B)
    (t : ℕ) (ω : ℕ → S) :
    HasSum (fun k => β ^ k * ku_Eiter P t k (fun ω' => (1 - β) * c (t + k) ω' ^ (1 - ρ)) ω)
      (U c t ω ^ (1 - ρ)) :=
  ku_additive_sum hP hβ0 hβ1 (r := fun t ω => (1 - β) * c t ω ^ (1 - ρ))
    (V := fun t ω => U c t ω ^ (1 - ρ)) hr hVb
    (fun t ω => ku_ez_expected_power hP hρ hβ0 hβ1.le hrec hc hcpos hU t ω) t ω

/-! ### Stationary Markov consumption: existence, uniqueness and homogeneity -/

/-- Miao, (20.3), p. 686: for stationary Markov consumption `c_t = c(s_t) > 0` and an irreducible
Markov chain, (20.3) has a unique positive Markov solution `U_t = v(s_t)`: `v` is the unique
positive fixed point of the Epstein–Zin Koopmans operator (Sargent–Stachurski Proposition 7.2.3,
`SS.globallyStableOn_ez`). -/
theorem ku_ez_markov [DecidableEq S] [Nonempty S] {P : Matrix S S ℝ} (hP : SS.IsMarkov P)
    (hirr : SS.Irreducible P) {c : S → ℝ} (hc : ∀ s, 0 < c s) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) :
    ∃ v : S → ℝ, (∀ s, 0 < v s) ∧ (∀ s, v s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P v s)) ∧
      (∀ w : S → ℝ, (∀ s, 0 < w s) →
        (∀ s, w s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P w s)) → w = v) ∧
      ∀ t ω, v (ω t) = ku_ces β ρ (c (ω t)) (ku_kpCE P γ t (fun ω' => v (ω' (t + 1))) ω) := by
  have hb : 0 < 1 - β := by linarith
  obtain ⟨v, hv, hfix, huniq, _⟩ := SS.globallyStableOn_ez hP hirr
    (h := fun s => (1 - β) * c s ^ (1 - ρ))
    (fun s => mul_pos hb (Real.rpow_pos_of_pos (hc s) _)) hβ0 hβ1
    (sub_ne_zero.2 (Ne.symm hρ)) (sub_ne_zero.2 (Ne.symm hγ))
  have hK : ∀ w : S → ℝ, ∀ s, SS.ezK (fun s => (1 - β) * c s ^ (1 - ρ)) (fun _ => β) (1 - ρ)
      (1 - γ) P w s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P w s) := fun _ _ => rfl
  refine ⟨v, hv, fun s => ?_, fun w hw hwfix => huniq w hw ?_, fun t ω => ?_⟩
  · rw [← hK]
    exact (congrFun hfix s).symm
  · funext s
    rw [hK]
    exact (hwfix s).symm
  · rw [ku_kpCE_eq_kpR]
    simp only [Function.update_self]
    rw [← hK]
    exact (congrFun hfix _).symm

/-- The CES aggregator is homogeneous of degree one. -/
theorem ku_ces_homog {β ρ : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {l x y : ℝ}
    (hl : 0 < l) (hx : 0 ≤ x) (hy : 0 ≤ y) : ku_ces β ρ (l * x) (l * y) = l * ku_ces β ρ x y := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 ≤ 1 - β := by linarith
  have h2 := Real.rpow_nonneg hx (1 - ρ)
  have h3 := Real.rpow_nonneg hy (1 - ρ)
  unfold ku_ces
  rw [Real.mul_rpow hl.le hx, Real.mul_rpow hl.le hy,
    show (1 - β) * (l ^ (1 - ρ) * x ^ (1 - ρ)) + β * (l ^ (1 - ρ) * y ^ (1 - ρ)) =
      l ^ (1 - ρ) * ((1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ)) by ring,
    Real.mul_rpow (Real.rpow_nonneg hl.le _) (by positivity), Real.rpow_rpow_inv hl.le h1]

/-- Miao, p. 686: Epstein–Zin utility is scale-invariant (homothetic): for stationary Markov
consumption the solution for `λc` is `λ` times the solution for `c`. -/
theorem ku_ez_markov_homogeneous [DecidableEq S] [Nonempty S] {P : Matrix S S ℝ}
    (hP : SS.IsMarkov P) (hirr : SS.Irreducible P) {c : S → ℝ} (hc : ∀ s, 0 < c s)
    {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {v : S → ℝ}
    (hv : ∀ s, 0 < v s) (hvfix : ∀ s, v s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P v s)) {l : ℝ}
    (hl : 0 < l) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hwfix : ∀ s, w s = ku_ces β ρ (l * c s) (SS.kpR (1 - γ) P w s)) : w = l • v := by
  obtain ⟨u, _, _, huniq, _⟩ := ku_ez_markov hP hirr (c := fun s => l * c s)
    (fun s => mul_pos hl (hc s)) hβ0 hβ1 hρ hγ
  have hlv : ∀ s, 0 < (l • v) s := fun s => by simpa using mul_pos hl (hv s)
  have hK : SS.kpR (1 - γ) P (l • v) = l • SS.kpR (1 - γ) P v :=
    SS.posHomogeneous_kpR (sub_ne_zero.2 (Ne.symm hγ)) hP v hv l hl.le hlv
  have hfix' : ∀ s, (l • v) s = ku_ces β ρ (l * c s) (SS.kpR (1 - γ) P (l • v) s) := by
    intro s
    rw [hK, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      ku_ces_homog hρ hβ0.le hβ1.le hl (hc s).le (SS.kpR_pos hP hv s).le, ← hvfix s]
  rw [huniq w hw hwfix, huniq _ hlv hfix']

/-! ### Weil's exponential certainty equivalent and (20.4) -/

/-- Miao, p. 686: Weil's exponential certainty equivalent `M_t(x) = −(1/γ) log E_t[exp(−γx)]`. -/
noncomputable def ku_expCE (P : Matrix S S ℝ) (γ : ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) :
    (ℕ → S) → ℝ :=
  fun ω => -(1 / γ) * Real.log (ku_E P t (fun ω' => Real.exp (-γ * x ω')) ω)

/-- Miao, p. 686: the exponential certainty equivalent is a conditional certainty equivalent on
all real random variables. -/
theorem ku_expCE_isCE {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 0) :
    definition_20_2_3 Set.univ (ku_expCE P γ) := by
  intro t
  refine ⟨fun x hx => ?_, ?_, fun α _ _ => ?_⟩
  · have hm : ku_Meas (t + 1) fun ω => Real.exp (-γ * x ω) := fun ω ω' h => by
      change Real.exp (-γ * x ω) = Real.exp (-γ * x ω')
      rw [hx ω ω' h]
    intro ω ω' h
    simp only [ku_expCE]
    rw [ku_E_meas P hm ω ω' h]
  · refine Continuous.continuousOn (continuous_pi fun ω => ?_)
    refine continuous_const.mul (Continuous.log ?_ fun x => ?_)
    · exact continuous_finsetSum _ fun s' _ => continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _)))
    · exact (ku_E_pos hP (x := fun ω' => Real.exp (-γ * x ω')) (fun _ => Real.exp_pos _)
        t ω).ne'
  · funext ω
    simp only [ku_expCE, ku_E]
    rw [← Finset.sum_mul, hP.rowsum, one_mul, Real.log_exp]
    field_simp

/-- Miao, p. 686: the exponential certainty equivalent is translation invariant:
`M_t(x + a) = M_t(x) + a` for `F_t`-measurable `a`. -/
theorem ku_expCE_translation {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 0)
    (t : ℕ) (x : (ℕ → S) → ℝ) {a : (ℕ → S) → ℝ} (ha : ku_Meas t a) (ω : ℕ → S) :
    ku_expCE P γ t (x + a) ω = ku_expCE P γ t x ω + a ω := by
  have hE := ku_E_pos hP (x := fun ω' => Real.exp (-γ * x ω')) (fun _ => Real.exp_pos _) t ω
  have e : ku_E P t (fun ω' => Real.exp (-γ * (x + a) ω')) ω =
      Real.exp (-γ * a ω) * ku_E P t (fun ω' => Real.exp (-γ * x ω')) ω := by
    simp only [ku_E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have h1 : a (Function.update ω (t + 1) s') = a ω :=
      ha _ _ fun s hs => by rw [Function.update_of_ne (by omega)]
    rw [Pi.add_apply, h1, mul_add, Real.exp_add]
    ring
  simp only [ku_expCE]
  rw [e, Real.log_mul (Real.exp_pos _).ne' hE.ne', Real.log_exp]
  field_simp
  ring

/-- Miao, (20.4), p. 686: with the CES aggregator and Weil's certainty equivalent, (20.2) reads
`U_t = [(1 − β)c_t^{1−ρ} + β(−(1/γ) log E_t exp(−γU_{t+1}))^{1−ρ}]^{1/(1−ρ)}`. -/
theorem eq_20_4 (P : Matrix S S ℝ) (β ρ γ : ℝ) (C : Set (ℕ → (ℕ → S) → ℝ))
    (U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ) :
    eq_20_2 C U (ku_ces β ρ) (ku_expCE P γ) ↔
      ∀ c ∈ C, ∀ t ω, U c t ω = ((1 - β) * c t ω ^ (1 - ρ) +
        β * (-(1 / γ) * Real.log (ku_E P t (fun ω' => Real.exp (-γ * U c (t + 1) ω')) ω)) ^
          (1 - ρ)) ^ (1 - ρ)⁻¹ :=
  Iff.rfl

/-! ### The limit `ρ → 1` and (20.5) -/

/-- Miao, p. 686: as `ρ → 1` the CES aggregator tends to the Cobb–Douglas aggregator
`x^{1−β}y^β`. -/
theorem ku_ces_limit {β x y : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun ρ => ku_ces β ρ x y) (𝓝[≠] 1) (𝓝 (x ^ (1 - β) * y ^ β)) := by
  have hh : HasDerivAt (fun r : ℝ => (1 - β) * x ^ r + β * y ^ r)
      ((1 - β) * (x ^ (0 : ℝ) * Real.log x) + β * (y ^ (0 : ℝ) * Real.log y)) (0 : ℝ) :=
    ((Real.hasStrictDerivAt_const_rpow hx 0).hasDerivAt.const_mul _).add
      ((Real.hasStrictDerivAt_const_rpow hy 0).hasDerivAt.const_mul _)
  have h0 : (1 - β) * x ^ (0 : ℝ) + β * y ^ (0 : ℝ) = 1 := by simp
  have hg := hh.log (by rw [h0]; exact one_ne_zero)
  rw [h0, div_one, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul] at hg
  have hslope := hg.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at hslope
  rw [h0, Real.log_one] at hslope
  simp only [sub_zero] at hslope
  have hr : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ρ hρ => ?_⟩
    · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact sub_ne_zero.2 (Ne.symm hρ)
  have hlim := (Real.continuous_exp.tendsto _).comp (hslope.comp hr)
  have hval : Real.exp ((1 - β) * Real.log x + β * Real.log y) = x ^ (1 - β) * y ^ β := by
    rw [Real.exp_add, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, mul_comm (1 - β),
      mul_comm β]
  rw [← hval]
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ρ hρ => ?_)
  have hpos : 0 < (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) := by
    have h1 := Real.rpow_pos_of_pos hx (1 - ρ)
    have h2 := Real.rpow_pos_of_pos hy (1 - ρ)
    rcases lt_or_eq_of_le hβ1 with h | h
    · have : 0 < 1 - β := by linarith
      positivity
    · rw [h]
      linarith
  simp only [Function.comp_def]
  rw [ku_ces, Real.rpow_def_of_pos hpos, mul_comm]

/-- Miao, (20.5), p. 686: with the limiting aggregator `W(x, y) = x^{1−β}y^β` and the
Kreps–Porteus certainty equivalent, `V_t = log U_t` satisfies
`V_t = (1 − β) log c_t + β/(1 − γ) log E_t exp((1 − γ)V_{t+1})`. -/
theorem eq_20_5 {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β γ : ℝ}
    {C : Set (ℕ → (ℕ → S) → ℝ)} {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (fun x y => x ^ (1 - β) * y ^ β) (ku_kpCE P γ))
    {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C) (hcpos : ∀ t ω, 0 < c t ω) (hU : ∀ t ω, 0 < U c t ω)
    (t : ℕ) (ω : ℕ → S) :
    Real.log (U c t ω) = (1 - β) * Real.log (c t ω) + β / (1 - γ) *
      Real.log (ku_E P t (fun ω' => Real.exp ((1 - γ) * Real.log (U c (t + 1) ω'))) ω) := by
  have hE := ku_E_pos hP (x := fun ω' => U c (t + 1) ω' ^ (1 - γ))
    (fun ω' => Real.rpow_pos_of_pos (hU _ ω') _) t ω
  have e : (fun ω' => Real.exp ((1 - γ) * Real.log (U c (t + 1) ω'))) =
      fun ω' => U c (t + 1) ω' ^ (1 - γ) := funext fun ω' => by
    rw [Real.rpow_def_of_pos (hU _ ω'), mul_comm]
  rw [hrec c hc t ω, e, Real.log_mul (Real.rpow_pos_of_pos (hcpos t ω) _).ne'
    (Real.rpow_pos_of_pos (ku_kpCE_pos hP γ (hU (t + 1)) t ω) _).ne',
    Real.log_rpow (hcpos t ω), Real.log_rpow (ku_kpCE_pos hP γ (hU (t + 1)) t ω), ku_kpCE,
    Real.log_rpow hE]
  ring

end Miao.RecursiveUtility
