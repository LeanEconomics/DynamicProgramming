/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.SpectralRadius

/-!
# The spectral subradius of a stochastic matrix

Morton and Wecker (1977); Bray (2019a), the quantity `λ(Q)` ("second-largest eigenvalue
modulus") that governs the asymptotic speed of relative value iteration.

Let `Δ` subtract the value at a reference state, `(Δv)(s) = v(s) − v(s₀)` (`deltaMat`), and let
`Q` be a stochastic matrix. The **subradius** is `λ(Q) = ρ(ΔQ)` (`subradius`).

* `mem_spectrum_deltaQ_iff`: the nonzero eigenvalues of `ΔQ` are exactly the eigenvalues of `Q`
  other than `1`, together with `1` itself iff `Q` has a non-constant fixed vector. A stochastic
  matrix has no Jordan block at `1`, which the proof uses.
* `spectralRadius_deltaQ`: hence, when the only fixed vectors of `Q` are the constants (one
  closed class), `λ(Q) = max{|μ| : μ an eigenvalue of Q, μ ≠ 1}` — Bray's second-largest
  eigenvalue modulus.
* `sp_pow_mulVec_le`: for every `γ > λ(Q)` there is `C` with `sp(Qᵏd) ≤ Cγᵏ sp(d)`.
* `subradius_le_dobrushin`: `λ(Q)` is at most any bound on the Dobrushin coefficient.
-/

open Filter Topology Matrix Finset

namespace DPExtensions.RelativeValueIteration

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The differencing matrix `Δ`: `(Δv)(s) = v(s) − v(s₀)`. -/
def deltaMat (s₀ : S) : Matrix S S ℝ :=
  fun i j => (if i = j then 1 else 0) - (if j = s₀ then 1 else 0)

/-- A stochastic matrix. -/
def IsStochastic (Q : Matrix S S ℝ) : Prop := (∀ i j, 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j = 1

/-- The spectral subradius `λ(Q) = ρ(ΔQ)`. -/
noncomputable def subradius (Q : Matrix S S ℝ) (s₀ : S) : ℝ := specRad (deltaMat s₀ * Q)

theorem deltaMat_mulVec (s₀ : S) (v : S → ℝ) : deltaMat s₀ *ᵥ v = fun s => v s - v s₀ := by
  funext s
  simp [deltaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul]

theorem cdelta_mulVec (s₀ : S) (w : S → ℂ) :
    complexify (deltaMat s₀) *ᵥ w = fun s => w s - w s₀ := by
  funext s
  simp [complexify, deltaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul,
    apply_ite (Complex.ofReal)]

omit [DecidableEq S] in
theorem mulVec_const {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (c : ℝ) :
    Q *ᵥ (fun _ => c) = fun _ => c := by
  funext s
  simp only [mulVec, dotProduct, ← sum_mul, hQ.2 s, one_mul]

omit [DecidableEq S] in
theorem cmulVec_const {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (c : ℂ) :
    complexify Q *ᵥ (fun _ => c) = fun _ => c := by
  funext s
  have h : ∑ j, (Q s j : ℂ) = 1 := by exact_mod_cast hQ.2 s
  simp only [mulVec, dotProduct, complexify_apply, ← sum_mul, h, one_mul]

omit [DecidableEq S] in
theorem norm_cmulVec_le {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (w : S → ℂ) :
    ‖complexify Q *ᵥ w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun s => ?_
  simp only [mulVec, dotProduct, complexify_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖(Q s j : ℂ) * w j‖ ≤ ∑ j, Q s j * ‖w‖ := sum_le_sum fun j _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hQ.1 s j)]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (hQ.1 s j)
    _ = ‖w‖ := by rw [← sum_mul, hQ.2 s, one_mul]

omit [DecidableEq S] in
/-- A stochastic matrix has no Jordan block at `1`: `Qv = v + c` with `v(s₀) = 0` forces
`c = 0`. -/
theorem no_jordan_one {Q : Matrix S S ℝ} (hQ : IsStochastic Q) {v : S → ℂ} {c : ℂ} (s₀ : S)
    (hv0 : v s₀ = 0) (hv : complexify Q *ᵥ v = fun s => v s + c) : c = 0 := by
  classical
  have hconst : ∀ k : ℕ, (complexify Q ^ k) *ᵥ (fun _ => c) = fun _ => c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, cmulVec_const hQ, ih]
  have hpow : ∀ k : ℕ, (complexify Q ^ k) *ᵥ v = fun s => v s + k * c := by
    intro k
    induction k with
    | zero => funext s; simp
    | succ k ih =>
      rw [pow_succ, ← mulVec_mulVec, hv,
        show (fun s => v s + c) = v + fun _ => c from rfl, mulVec_add, ih, hconst]
      funext s
      simp only [Pi.add_apply]
      push_cast
      ring
  have hb : ∀ k : ℕ, ‖(k : ℂ) * c‖ ≤ ‖v‖ := by
    intro k
    have h1 : ‖(complexify Q ^ k) *ᵥ v‖ ≤ ‖v‖ := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← mulVec_mulVec]
        exact (norm_cmulVec_le hQ _).trans ih
    have h2 := (norm_le_pi_norm ((complexify Q ^ k) *ᵥ v) s₀).trans h1
    simp only [hpow, hv0, zero_add] at h2
    exact h2
  by_contra hc
  obtain ⟨k, hk⟩ := exists_nat_gt (‖v‖ / ‖c‖)
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  have := hb k
  rw [norm_mul, Complex.norm_natCast] at this
  rw [div_lt_iff₀ hc'] at hk
  linarith

theorem complexify_deltaQ_mulVec (Q : Matrix S S ℝ) (s₀ : S) (w : S → ℂ) :
    complexify (deltaMat s₀ * Q) *ᵥ w =
      fun s => (complexify Q *ᵥ w) s - (complexify Q *ᵥ w) s₀ := by
  rw [complexify_mul, ← mulVec_mulVec, cdelta_mulVec]

/-- **The eigenvalues of `ΔQ`**: for `μ ≠ 0`, `μ` is an eigenvalue of `ΔQ` iff it is an
eigenvalue of `Q` other than `1`, or `μ = 1` and `Q` has a non-constant fixed vector. -/
theorem mem_spectrum_deltaQ_iff {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S) {μ : ℂ}
    (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ (complexify (deltaMat s₀ * Q)) ↔
      (μ ∈ spectrum ℂ (complexify Q) ∧ μ ≠ 1) ∨
        (μ = 1 ∧ ∃ v : S → ℂ, complexify Q *ᵥ v = v ∧ ∃ i j, v i ≠ v j) := by
  rw [mem_spectrum_iff_eigenpair, mem_spectrum_iff_eigenpair]
  constructor
  · rintro ⟨e, he, h⟩
    rw [complexify_deltaQ_mulVec] at h
    set w := complexify Q *ᵥ e with hw
    have hs : ∀ s, w s - w s₀ = μ * e s := fun s => by
      have := congrFun h s
      simpa using this
    have he0 : e s₀ = 0 := by
      have := hs s₀
      rw [sub_self] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hμ
    set c := w s₀
    have hwe : w = fun s => μ * e s + c := funext fun s => by linear_combination hs s
    by_cases h1 : μ = 1
    · subst h1
      have hc : c = 0 := no_jordan_one hQ s₀ he0 (by rw [← hw, hwe]; funext s; simp)
      refine Or.inr ⟨rfl, e, ?_, ?_⟩
      · rw [← hw, hwe, hc]
        funext s
        simp
      · obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
          by_contra hall
          push Not at hall
          exact he (funext hall)
        exact ⟨s, s₀, by rw [he0]; exact hs'⟩
    · refine Or.inl ⟨⟨fun s => e s + c / (μ - 1), ?_, ?_⟩, h1⟩
      · intro hu
        have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.2 h1
        have h2 := congrFun hu s₀
        simp only [he0, zero_add, Pi.zero_apply, div_eq_zero_iff, hμ1, or_false] at h2
        apply he
        funext s
        have h3 := congrFun hu s
        simp only [h2, zero_div, add_zero, Pi.zero_apply] at h3
        exact h3
      · have e1 : (fun s => e s + c / (μ - 1)) = e + fun _ => c / (μ - 1) := rfl
        rw [e1, mulVec_add, cmulVec_const hQ, ← hw, hwe]
        funext s
        have hμ1 : μ - 1 ≠ 0 := sub_ne_zero.2 h1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
  · rintro (⟨⟨u, hu, h⟩, h1⟩ | ⟨rfl, v, hv, i, j, hij⟩)
    · refine ⟨fun s => u s - u s₀, fun hz => hu ?_, ?_⟩
      · -- `u` would be constant, hence a fixed vector, forcing `μ = 1`
        have hc : u = fun _ => u s₀ := funext fun s => by
          have := congrFun hz s
          simpa [sub_eq_zero] using this
        have hfix := cmulVec_const hQ (u s₀)
        rw [← hc, h] at hfix
        by_contra hne
        have hu0 : u s₀ ≠ 0 := by
          intro h0
          apply hne
          rw [hc, h0]
          rfl
        have := congrFun hfix s₀
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact h1 (mul_right_cancel₀ hu0 (this.trans (one_mul _).symm))
      · rw [complexify_deltaQ_mulVec]
        have e1 : (fun s => u s - u s₀) = u + fun _ => -u s₀ := by
          funext s
          simp [sub_eq_add_neg]
        rw [e1, mulVec_add, cmulVec_const hQ, h]
        funext s
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · refine ⟨fun s => v s - v s₀, fun hz => hij ?_, ?_⟩
      · have hi := congrFun hz i
        have hj := congrFun hz j
        simp only [Pi.zero_apply, sub_eq_zero] at hi hj
        rw [hi, hj]
      · rw [complexify_deltaQ_mulVec]
        have e1 : (fun s => v s - v s₀) = v + fun _ => -v s₀ := by
          funext s
          simp [sub_eq_add_neg]
        rw [e1, mulVec_add, cmulVec_const hQ, hv]
        funext s
        simp only [Pi.add_apply, one_smul]
        ring

/-- **The subradius is the second-largest eigenvalue modulus**: when the only fixed vectors of
`Q` are the constants, `ρ(ΔQ) = sup{|μ| : μ an eigenvalue of Q, μ ≠ 1}`. -/
theorem spectralRadius_deltaQ {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    (hfix : ∀ v : S → ℂ, complexify Q *ᵥ v = v → ∀ i j, v i = v j) :
    spectralRadius ℂ (complexify (deltaMat s₀ * Q)) =
      ⨆ μ ∈ spectrum ℂ (complexify Q), ⨆ (_ : μ ≠ 1), (‖μ‖₊ : ENNReal) := by
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => iSup_le fun h1 => ?_)
  · rcases eq_or_ne μ 0 with h0 | h0
    · simp [h0]
    · rcases (mem_spectrum_deltaQ_iff hQ s₀ h0).1 hμ with ⟨hs, h1⟩ | ⟨rfl, v, hv, i, j, hij⟩
      · exact le_iSup₂_of_le μ hs (le_iSup_of_le h1 le_rfl)
      · exact absurd (hfix v hv i j) hij
  · rcases eq_or_ne μ 0 with h0 | h0
    · simp [h0]
    · exact le_iSup₂_of_le μ ((mem_spectrum_deltaQ_iff hQ s₀ h0).2 (Or.inl ⟨hμ, h1⟩)) le_rfl

theorem sp_deltaMat_mulVec [Nonempty S] (s₀ : S) (v : S → ℝ) :
    sp (deltaMat s₀ *ᵥ v) = sp v := by
  rw [deltaMat_mulVec]
  have := sp_add_const v (-v s₀)
  simpa [sub_eq_add_neg] using this

theorem norm_deltaMat_mulVec_le [Nonempty S] (s₀ : S) (v : S → ℝ) :
    ‖deltaMat s₀ *ᵥ v‖ ≤ sp v :=
  (pi_norm_le_iff_of_nonneg (sp_nonneg v)).2 fun s => by
    rw [deltaMat_mulVec, Real.norm_eq_abs]
    exact abs_sub_le_sp v s s₀

omit [DecidableEq S] in
theorem sp_le_two_norm [Nonempty S] (v : S → ℝ) : sp v ≤ 2 * ‖v‖ :=
  sp_le fun x y => by
    have h1 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm v x)
    have h2 := abs_le.1 ((Real.norm_eq_abs _).symm ▸ norm_le_pi_norm v y)
    linarith [h1.2, h2.1]

theorem deltaQ_pow_mulVec {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S) (v : S → ℝ)
    (k : ℕ) : (deltaMat s₀ * Q) ^ k *ᵥ (deltaMat s₀ *ᵥ v) = deltaMat s₀ *ᵥ (Q ^ k *ᵥ v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec]
    have e : Q *ᵥ (deltaMat s₀ *ᵥ v) = Q *ᵥ v + fun _ => -v s₀ := by
      rw [deltaMat_mulVec, show (fun s => v s - v s₀) = v + fun _ => -v s₀ by
        funext s; simp [sub_eq_add_neg], mulVec_add, mulVec_const hQ]
    rw [e, mulVec_add, deltaMat_mulVec (s₀ := s₀) (fun _ => -v s₀)]
    have e2 : deltaMat s₀ *ᵥ (Q *ᵥ v) + (fun s => (fun _ : S => -v s₀) s - -v s₀) =
        deltaMat s₀ *ᵥ (Q *ᵥ v) := by
      funext s
      simp
    rw [e2, ih, pow_succ, ← mulVec_mulVec]

/-- **The subradius governs the span**: for every `γ > λ(Q)` there is `C` with
`sp(Qᵏd) ≤ Cγᵏ sp(d)` for all `k`. -/
theorem sp_pow_mulVec_le [Nonempty S] {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    {γ : ℝ} (hγ : subradius Q s₀ < γ) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (d : S → ℝ), sp (Q ^ k *ᵥ d) ≤ C * γ ^ k * sp d := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_pow_le (deltaMat s₀ * Q) hγ
  have hγ0 : 0 < γ := (specRad_nonneg _).trans_lt hγ
  refine ⟨2 * C, by positivity, fun k d => ?_⟩
  calc sp (Q ^ k *ᵥ d) = sp (deltaMat s₀ *ᵥ (Q ^ k *ᵥ d)) := (sp_deltaMat_mulVec s₀ _).symm
    _ ≤ 2 * ‖deltaMat s₀ *ᵥ (Q ^ k *ᵥ d)‖ := sp_le_two_norm _
    _ = 2 * ‖(deltaMat s₀ * Q) ^ k *ᵥ (deltaMat s₀ *ᵥ d)‖ := by rw [deltaQ_pow_mulVec hQ]
    _ ≤ 2 * (‖(deltaMat s₀ * Q) ^ k‖ * ‖deltaMat s₀ *ᵥ d‖) :=
        mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) zero_le_two
    _ ≤ 2 * (C * γ ^ k * sp d) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul (hC k) (norm_deltaMat_mulVec_le s₀ d) (norm_nonneg _) (by positivity)
    _ = 2 * C * γ ^ k * sp d := by ring

/-- **The subradius is at most the Dobrushin coefficient.** -/
theorem subradius_le_dobrushin [Nonempty S] {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    {α : ℝ} (hα : ∀ i j, 1 - ∑ t, min (Q i t) (Q j t) ≤ α) : subradius Q s₀ ≤ α := by
  have hα0 : 0 ≤ α := by
    have h := hα s₀ s₀
    simp only [min_self, hQ.2 s₀, sub_self] at h
    exact h
  have hstep : ∀ d : S → ℝ, sp (Q *ᵥ d) ≤ α * sp d := fun d =>
    sp_le fun i j => by
      have h := dobrushin (hQ.2 i) (hQ.2 j) d
      have hs := mul_le_mul_of_nonneg_right (hα i j) (sp_nonneg d)
      simp only [mulVec, dotProduct]
      linarith
  have hpow : ∀ (k : ℕ) (d : S → ℝ), sp (Q ^ k *ᵥ d) ≤ α ^ k * sp d := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
      intro d
      rw [pow_succ', ← mulVec_mulVec, pow_succ']
      calc sp (Q *ᵥ (Q ^ k *ᵥ d)) ≤ α * sp (Q ^ k *ᵥ d) := hstep _
        _ ≤ α * (α ^ k * sp d) := mul_le_mul_of_nonneg_left (ih d) hα0
        _ = α * α ^ k * sp d := by ring
  refine specRad_le_of_norm_pow_le _ zero_lt_two hα0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(deltaMat s₀ * Q) ^ k *ᵥ w‖ ≤ 2 * α ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    linarith [norm_nonneg w]
  -- `(ΔQ)ᵏ⁺¹ w = (ΔQ)ᵏ⁺¹ Δw`, since `ΔQ` kills constants
  have hconst : (deltaMat s₀ * Q) *ᵥ (fun _ => w s₀) = 0 := by
    rw [← mulVec_mulVec, mulVec_const hQ, deltaMat_mulVec]
    funext s
    simp
  have e : (deltaMat s₀ * Q) ^ (k + 1) *ᵥ w =
      (deltaMat s₀ * Q) ^ (k + 1) *ᵥ (deltaMat s₀ *ᵥ w) := by
    have hw : w = deltaMat s₀ *ᵥ w + fun _ => w s₀ := by
      rw [deltaMat_mulVec]
      funext s
      simp
    have h2 : (deltaMat s₀ * Q) ^ (k + 1) *ᵥ (fun _ => w s₀) = 0 := by
      rw [pow_succ, ← mulVec_mulVec, hconst, mulVec_zero]
    conv_lhs => rw [hw]
    rw [mulVec_add, h2, add_zero]
  rw [e, deltaQ_pow_mulVec hQ]
  calc ‖deltaMat s₀ *ᵥ (Q ^ (k + 1) *ᵥ w)‖ ≤ sp (Q ^ (k + 1) *ᵥ w) :=
        norm_deltaMat_mulVec_le s₀ _
    _ ≤ α ^ (k + 1) * sp w := hpow _ w
    _ ≤ α ^ (k + 1) * (2 * ‖w‖) := mul_le_mul_of_nonneg_left (sp_le_two_norm w) (by positivity)
    _ = 2 * α ^ (k + 1) * ‖w‖ := by ring

end DPExtensions.RelativeValueIteration
