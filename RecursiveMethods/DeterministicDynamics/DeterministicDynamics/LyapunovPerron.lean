/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.Dichotomy

/-!
# The Lyapunov–Perron construction

The analytic core of Theorem 6.6 (SLP §6.3, p. 147). Let `ℝⁿ` carry projections `P + Q = I`, and
let `B` invert `A` on the range of `Q`, with `‖AᵏPz‖ ≤ Kaᵏ‖z‖`, `‖BᵏQz‖ ≤ Kcᵏ‖z‖`, `a < γ`,
`cγ < 1` (`LPData`). For a perturbation `r` with `r(0) = 0` and Lipschitz constant `ε` small
(`K ε (1/(γ − a) + c/(1 − cγ)) ≤ ½`), every `ξ` gives a solution of
`z_{t+1} = Az_t + r(z_t)` with `Pz₀ = Pξ` and `‖z_t‖ ≤ 2K‖ξ‖γᵗ` (`lyapunov_perron`):

`z_t = AᵗPξ + Σ_{j<t} A^{t−1−j}P r(z_j) − Σ_{i≥0} B^{i+1}Q r(z_{t+i})`.

The right side is a contraction on sequences with `sup γ⁻ᵗ‖z_t‖ < ∞` (bounded sequences
`w_t = γ⁻ᵗz_t`), with constant `½`.
-/

open Set Filter Topology BoundedContinuousFunction
open scoped Matrix NNReal

namespace StokeyLucasPrescott.DeterministicDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dichotomy data. -/
structure LPData (A B : Matrix ι ι ℝ) (P Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (K a c γ : ℝ) : Prop where
  PQ : ∀ z, P z + Q z = z
  PP : ∀ z, P (P z) = P z
  PB : ∀ k z, P ((B ^ (k + 1)) *ᵥ Q z) = 0
  AB : ∀ k z, A *ᵥ ((B ^ (k + 1)) *ᵥ Q z) = (B ^ k) *ᵥ Q z
  K_nn : 0 ≤ K
  a_nn : 0 ≤ a
  aγ : a < γ
  c_pos : 0 < c
  cγ : c * γ < 1
  bA : ∀ k z, ‖(A ^ k) *ᵥ P z‖ ≤ K * a ^ k * ‖z‖
  bB : ∀ k z, ‖(B ^ k) *ᵥ Q z‖ ≤ K * c ^ k * ‖z‖

/-- `Σ_{j<t} a^{t−1−j}γʲ ≤ γᵗ/(γ − a)`. -/
theorem geom_head {a γ : ℝ} (ha : 0 ≤ a) (haγ : a < γ) (t : ℕ) :
    ∑ j ∈ Finset.range t, a ^ (t - 1 - j) * γ ^ j ≤ γ ^ t / (γ - a) := by
  have hγ : 0 < γ := ha.trans_lt haγ
  induction t with
  | zero => simpa using haγ.le
  | succ t ih =>
    have e : ∑ j ∈ Finset.range (t + 1), a ^ (t + 1 - 1 - j) * γ ^ j =
        a * ∑ j ∈ Finset.range t, a ^ (t - 1 - j) * γ ^ j + γ ^ t := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.1 hj
        rw [show t + 1 - 1 - j = (t - 1 - j) + 1 by omega, pow_succ]; ring
      · simp
    rw [e]
    have := mul_le_mul_of_nonneg_left ih ha
    have key : a * (γ ^ t / (γ - a)) + γ ^ t = γ ^ (t + 1) / (γ - a) := by
      have : γ - a ≠ 0 := by linarith
      field_simp; ring
    linarith

variable {A B : Matrix ι ι ℝ} {P Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {K a c γ : ℝ}

/-- The head sum `Σ_{j<t} A^{t−1−j}P u_j`. -/
noncomputable def lpHead (A : Matrix ι ι ℝ) (P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (u : ℕ → ι → ℝ)
    (t : ℕ) : ι → ℝ :=
  ∑ j ∈ Finset.range t, (A ^ (t - 1 - j)) *ᵥ P (u j)

/-- The tail sum `Σ_{i≥0} B^{i+1}Q u_{t+i}`. -/
noncomputable def lpTail (B : Matrix ι ι ℝ) (Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (u : ℕ → ι → ℝ)
    (t : ℕ) : ι → ℝ :=
  ∑' i, (B ^ (i + 1)) *ᵥ Q (u (t + i))

theorem lpHead_succ (u : ℕ → ι → ℝ) (t : ℕ) :
    lpHead A P u (t + 1) = A *ᵥ lpHead A P u t + P (u t) := by
  simp only [lpHead, Finset.sum_range_succ, Matrix.mulVec_sum]
  rw [show t + 1 - 1 - t = 0 by omega, pow_zero, Matrix.one_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [Matrix.mulVec_mulVec, ← pow_succ', show t + 1 - 1 - j = t - 1 - j + 1 by omega]

theorem summable_lpTail (hD : LPData A B P Q K a c γ) {u : ℕ → ι → ℝ} {M : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (t : ℕ) :
    Summable fun i => (B ^ (i + 1)) *ᵥ Q (u (t + i)) := by
  have hγ : 0 < γ := hD.a_nn.trans_lt hD.aγ
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg hD.c_pos.le hγ.le) hD.cγ).mul_left
      (K * c * M * γ ^ t)) fun i => ?_
  refine (hD.bB (i + 1) _).trans ?_
  have := hu (t + i)
  have hK := hD.K_nn
  have hc := hD.c_pos
  calc K * c ^ (i + 1) * ‖u (t + i)‖ ≤ K * c ^ (i + 1) * (M * γ ^ (t + i)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = K * c * M * γ ^ t * (c * γ) ^ i := by rw [pow_add, pow_succ, mul_pow]; ring

theorem norm_lpTail_le (hD : LPData A B P Q K a c γ) {u : ℕ → ι → ℝ} {M : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (t : ℕ) :
    ‖lpTail B Q u t‖ ≤ K * c * M * γ ^ t / (1 - c * γ) := by
  have hγ : 0 < γ := hD.a_nn.trans_lt hD.aγ
  have hcγ := hD.cγ
  have hs := summable_lpTail hD hu t
  have hg := (summable_geometric_of_lt_one (mul_nonneg hD.c_pos.le hγ.le) hcγ).mul_left
    (K * c * M * γ ^ t)
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  refine (hs.norm.tsum_le_tsum (fun i => ?_) hg).trans ?_
  · refine (hD.bB (i + 1) _).trans ?_
    have := hu (t + i)
    have hK := hD.K_nn
    have hc := hD.c_pos
    calc K * c ^ (i + 1) * ‖u (t + i)‖ ≤ K * c ^ (i + 1) * (M * γ ^ (t + i)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = K * c * M * γ ^ t * (c * γ) ^ i := by rw [pow_add, pow_succ, mul_pow]; ring
  · rw [tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hD.c_pos.le hγ.le) hcγ]
    rw [div_eq_mul_inv]

theorem norm_lpHead_le (hD : LPData A B P Q K a c γ) {u : ℕ → ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (t : ℕ) :
    ‖lpHead A P u t‖ ≤ K * M * γ ^ t / (γ - a) := by
  have hK := hD.K_nn
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range t, ‖(A ^ (t - 1 - j)) *ᵥ P (u j)‖
      ≤ ∑ j ∈ Finset.range t, K * M * (a ^ (t - 1 - j) * γ ^ j) :=
        Finset.sum_le_sum fun j _ => (hD.bA _ _).trans (by
          have h1 := mul_le_mul_of_nonneg_left (hu j)
            (mul_nonneg hK (pow_nonneg hD.a_nn (t - 1 - j)))
          linarith [show K * a ^ (t - 1 - j) * (M * γ ^ j) =
            K * M * (a ^ (t - 1 - j) * γ ^ j) by ring])
    _ = K * M * ∑ j ∈ Finset.range t, a ^ (t - 1 - j) * γ ^ j := by rw [Finset.mul_sum]
    _ ≤ K * M * (γ ^ t / (γ - a)) :=
        mul_le_mul_of_nonneg_left (geom_head hD.a_nn hD.aγ t) (mul_nonneg hK hM)
    _ = K * M * γ ^ t / (γ - a) := by ring

theorem lpHead_sub (u u' : ℕ → ι → ℝ) (t : ℕ) :
    lpHead A P u t - lpHead A P u' t = lpHead A P (u - u') t := by
  simp only [lpHead, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub, Matrix.mulVec_sub]

theorem lpTail_sub (hD : LPData A B P Q K a c γ) {u u' : ℕ → ι → ℝ} {M M' : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (hu' : ∀ j, ‖u' j‖ ≤ M' * γ ^ j) (t : ℕ) :
    lpTail B Q u t - lpTail B Q u' t = lpTail B Q (u - u') t := by
  simp only [lpTail]
  rw [← (summable_lpTail hD hu t).tsum_sub (summable_lpTail hD hu' t)]
  simp only [Pi.sub_apply, map_sub, Matrix.mulVec_sub]

omit [DecidableEq ι] in
theorem mulVec_tsum (M : Matrix ι ι ℝ) {f : ℕ → ι → ℝ} (hf : Summable f) :
    M *ᵥ (∑' i, f i) = ∑' i, M *ᵥ f i := by
  classical
  have := (LinearMap.toContinuousLinearMap (Matrix.toLin' M)).map_tsum hf
  simpa [Matrix.toLin'_apply] using this

omit [Fintype ι] [DecidableEq ι] in
theorem linearMap_tsum [Finite ι] (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {f : ℕ → ι → ℝ} (hf : Summable f) :
    L (∑' i, f i) = ∑' i, L (f i) :=
  (LinearMap.toContinuousLinearMap L).map_tsum hf

theorem lpTail_succ (hD : LPData A B P Q K a c γ) {u : ℕ → ι → ℝ} {M : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (t : ℕ) :
    A *ᵥ lpTail B Q u t = Q (u t) + lpTail B Q u (t + 1) := by
  have hs := summable_lpTail hD hu t
  rw [lpTail, mulVec_tsum A hs]
  simp only [hD.AB]
  have hs' : Summable fun i => (B ^ i) *ᵥ Q (u (t + i)) := by
    rw [← summable_nat_add_iff 1]
    refine (summable_lpTail hD hu (t + 1)).congr fun i => ?_
    rw [show t + (i + 1) = t + 1 + i by ring]
  rw [hs'.tsum_eq_zero_add]
  simp only [pow_zero, Matrix.one_mulVec, add_zero, lpTail]
  congr 1
  refine tsum_congr fun i => ?_
  rw [show t + (i + 1) = t + 1 + i by ring]

/-! ### The fixed point -/

/-- `u_j = r(γʲw_j)`. -/
noncomputable def lpU (γ : ℝ) (r : (ι → ℝ) → ι → ℝ) (w : ℕ → ι → ℝ) (j : ℕ) : ι → ℝ :=
  r (γ ^ j • w j)

/-- The right side of the integral equation. -/
noncomputable def lpZ (A B : Matrix ι ι ℝ) (P Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ)
    (r : (ι → ℝ) → ι → ℝ) (ξ : ι → ℝ) (w : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  (A ^ t) *ᵥ P ξ + lpHead A P (lpU γ r w) t - lpTail B Q (lpU γ r w) t

/-- **The Lyapunov–Perron theorem.** -/
theorem lyapunov_perron (hD : LPData A B P Q K a c γ) {r : (ι → ℝ) → ι → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hr0 : r 0 = 0) (hr : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖)
    (hsmall : K * ε * (1 / (γ - a) + c / (1 - c * γ)) ≤ 1 / 2) (ξ : ι → ℝ) :
    ∃ z : ℕ → ι → ℝ, (∀ t, z (t + 1) = A *ᵥ z t + r (z t)) ∧ P (z 0) = P ξ ∧
      (∀ t, ‖z t‖ ≤ 2 * K * ‖ξ‖ * γ ^ t) ∧
      (∀ M, (∀ j, ‖r (z j)‖ ≤ M * γ ^ j) → ‖Q (z 0)‖ ≤ K * c * M / (1 - c * γ)) ∧
      ∀ t, z t = (A ^ t) *ᵥ P ξ + lpHead A P (fun j => r (z j)) t -
        lpTail B Q (fun j => r (z j)) t := by
  have hγ : 0 < γ := hD.a_nn.trans_lt hD.aγ
  have hγa : 0 < γ - a := by linarith [hD.aγ]
  have hcγ : 0 < 1 - c * γ := by linarith [hD.cγ]
  have hK := hD.K_nn
  have hc := hD.c_pos
  set Λ := 1 / (γ - a) + c / (1 - c * γ)
  have hΛ : 0 ≤ Λ := by positivity
  -- bounds on the nonlinear terms
  have hu : ∀ (w : ℕ →ᵇ (ι → ℝ)) j, ‖lpU γ r w j‖ ≤ ε * ‖w‖ * γ ^ j := fun w j => by
    have := hr (γ ^ j • w j) 0
    rw [hr0, sub_zero, sub_zero, norm_smul, Real.norm_of_nonneg (pow_nonneg hγ.le j)] at this
    refine this.trans ?_
    have h1 := mul_le_mul_of_nonneg_left (w.norm_coe_le_norm j) (pow_nonneg hγ.le j)
    have h2 := mul_le_mul_of_nonneg_left h1 hε
    linarith [show ε * (γ ^ j * ‖w‖) = ε * ‖w‖ * γ ^ j by ring]
  have hud : ∀ (w w' : ℕ →ᵇ (ι → ℝ)) j,
      ‖(lpU γ r w - lpU γ r w') j‖ ≤ ε * dist w w' * γ ^ j := fun w w' j => by
    have := hr (γ ^ j • w j) (γ ^ j • w' j)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg hγ.le j)] at this
    refine this.trans ?_
    have h1 : ‖w j - w' j‖ ≤ dist w w' := by
      rw [← dist_eq_norm]; exact w.dist_coe_le_dist j
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (pow_nonneg hγ.le j)) hε
    linarith [show ε * (γ ^ j * dist w w') = ε * dist w w' * γ ^ j by ring]
  -- the head and tail terms are `O(γᵗ)`
  have hzbound : ∀ (u : ℕ → ι → ℝ) (M : ℝ), 0 ≤ M → (∀ j, ‖u j‖ ≤ M * γ ^ j) → ∀ t,
      ‖lpHead A P u t - lpTail B Q u t‖ ≤ K * M * Λ * γ ^ t := fun u M hM hu t => by
    have h1 := norm_lpHead_le hD hM hu t
    have h2 := norm_lpTail_le hD hu t
    refine (norm_sub_le _ _).trans ?_
    have e : K * M * Λ * γ ^ t = K * M * γ ^ t / (γ - a) + K * c * M * γ ^ t / (1 - c * γ) := by
      simp only [Λ]; field_simp
    linarith
  -- the operator on weighted sequences
  have hΦb : ∀ (w : ℕ →ᵇ (ι → ℝ)) t,
      ‖(γ ^ t)⁻¹ • lpZ A B P Q γ r ξ w t‖ ≤ K * ‖ξ‖ + K * (ε * ‖w‖) * Λ := fun w t => by
    have hγt := pow_pos hγ t
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hγt.le), inv_mul_le_iff₀ hγt]
    have h1 : ‖(A ^ t) *ᵥ P ξ‖ ≤ K * ‖ξ‖ * γ ^ t := by
      refine (hD.bA t ξ).trans ?_
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.a_nn hD.aγ.le t)
        (mul_nonneg hK (norm_nonneg ξ))
      linarith [show K * ‖ξ‖ * a ^ t = K * a ^ t * ‖ξ‖ by ring]
    have h2 := hzbound (lpU γ r w) (ε * ‖w‖) (mul_nonneg hε (norm_nonneg _)) (hu w) t
    simp only [lpZ, add_sub_assoc]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  set Φ : (ℕ →ᵇ (ι → ℝ)) → (ℕ →ᵇ (ι → ℝ)) := fun w =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun t => (γ ^ t)⁻¹ • lpZ A B P Q γ r ξ w t) _ (hΦb w)
  have hΦapply : ∀ w t, Φ w t = (γ ^ t)⁻¹ • lpZ A B P Q γ r ξ w t := fun _ _ => rfl
  have hlip : ∀ w w', dist (Φ w) (Φ w') ≤ (1 / 2) * dist w w' := fun w w' => by
    refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t => ?_
    rw [hΦapply, hΦapply, dist_eq_norm, ← smul_sub]
    have hγt := pow_pos hγ t
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hγt.le), inv_mul_le_iff₀ hγt]
    have e : lpZ A B P Q γ r ξ w t - lpZ A B P Q γ r ξ w' t =
        lpHead A P (lpU γ r w - lpU γ r w') t - lpTail B Q (lpU γ r w - lpU γ r w') t := by
      simp only [lpZ]
      rw [← lpHead_sub, ← lpTail_sub hD (hu w) (hu w')]
      abel
    rw [e]
    have h := hzbound _ (ε * dist w w') (mul_nonneg hε dist_nonneg) (hud w w') t
    have : K * (ε * dist w w') * Λ ≤ 1 / 2 * dist w w' := by
      have := mul_le_mul_of_nonneg_right hsmall (dist_nonneg (x := w) (y := w'))
      nlinarith
    nlinarith [pow_pos hγ t]
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) Φ :=
    ⟨by norm_num,
      LipschitzWith.of_dist_le_mul fun w w' => by
        simpa using hlip w w'⟩
  set w := ContractingWith.fixedPoint Φ hcontr
  have hw : Φ w = w := ContractingWith.fixedPoint_isFixedPt hcontr
  set z : ℕ → ι → ℝ := lpZ A B P Q γ r ξ w
  have hzw : ∀ t, z t = γ ^ t • w t := fun t => by
    have := DFunLike.congr_fun hw t
    rw [hΦapply] at this
    rw [← this, smul_smul, mul_inv_cancel₀ (pow_pos hγ t).ne', one_smul]
  have hU : lpU γ r w = fun j => r (z j) := by funext j; rw [lpU, hzw]
  have huw := hu w
  rw [hU] at huw
  -- the norm of the fixed point
  have hwn : ‖w‖ ≤ 2 * K * ‖ξ‖ := by
    have h1 := ContractingWith.dist_fixedPoint_le hcontr 0
    rw [dist_comm, dist_zero_right, dist_zero_left] at h1
    have h2 : ‖Φ 0‖ ≤ K * ‖ξ‖ := by
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_
      have := hΦb 0 t
      rw [hΦapply]
      simpa using this
    have : (1 : ℝ) - ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [this] at h1
    linarith
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → ι → ℝ, u = fun j => r (z j) := ⟨_, rfl⟩
  have hz_def : ∀ t, z t = (A ^ t) *ᵥ P ξ + lpHead A P u t - lpTail B Q u t := fun t => by
    rw [hu_def, ← hU]; rfl
  rw [← hu_def] at huw
  have hPtail : ∀ t, P (lpTail B Q u t) = 0 := fun t => by
    rw [lpTail, linearMap_tsum P (summable_lpTail hD huw t)]
    simp only [hD.PB, tsum_zero]
  have hQP : Q (P ξ) = 0 := by
    have := hD.PQ (P ξ); rw [hD.PP] at this; exact add_eq_left.1 this
  have hz0 : z 0 = P ξ - lpTail B Q u 0 := by
    rw [hz_def]; simp [lpHead]
  refine ⟨z, fun t => ?_, ?_, fun t => ?_, fun M hM => ?_, fun t => by rw [hz_def, hu_def]⟩
  · -- the recursion
    have hut : r (z t) = u t := by rw [hu_def]
    rw [hut]
    conv_rhs => rw [← hD.PQ (u t)]
    rw [hz_def (t + 1), hz_def t, lpHead_succ, Matrix.mulVec_sub, Matrix.mulVec_add,
      lpTail_succ hD huw t, pow_succ', ← Matrix.mulVec_mulVec]
    abel
  · -- `Pz₀ = Pξ`
    rw [hz0, map_sub, hD.PP, hPtail, sub_zero]
  · -- decay
    rw [hzw, norm_smul, Real.norm_of_nonneg (pow_nonneg hγ.le t)]
    have h1 := mul_le_mul_of_nonneg_left ((w.norm_coe_le_norm t).trans hwn)
      (pow_nonneg hγ.le t)
    linarith [show γ ^ t * (2 * K * ‖ξ‖) = 2 * K * ‖ξ‖ * γ ^ t by ring]
  · -- the unstable part of `z₀`
    have hM' : ∀ j, ‖u j‖ ≤ M * γ ^ j := fun j => by rw [hu_def]; exact hM j
    have hQt : Q (lpTail B Q u 0) = lpTail B Q u 0 := by
      have := hD.PQ (lpTail B Q u 0); rw [hPtail, zero_add] at this; exact this
    rw [hz0, map_sub, hQP, hQt, zero_sub, norm_neg]
    have := norm_lpTail_le hD hM' 0
    simpa using this

theorem norm_head_sub_tail_le (hD : LPData A B P Q K a c γ) {u : ℕ → ι → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (t : ℕ) :
    ‖lpHead A P u t - lpTail B Q u t‖ ≤
      K * M * (1 / (γ - a) + c / (1 - c * γ)) * γ ^ t := by
  have hγa : 0 < γ - a := by linarith [hD.aγ]
  have hcγ : 0 < 1 - c * γ := by linarith [hD.cγ]
  have h1 := norm_lpHead_le hD hM hu t
  have h2 := norm_lpTail_le hD hu t
  refine (norm_sub_le _ _).trans ?_
  have e : K * M * (1 / (γ - a) + c / (1 - c * γ)) * γ ^ t =
      K * M * γ ^ t / (γ - a) + K * c * M * γ ^ t / (1 - c * γ) := by field_simp
  linarith

theorem proj_lpTail (hD : LPData A B P Q K a c γ) {u : ℕ → ι → ℝ} {M : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ M * γ ^ j) (t : ℕ) :
    P (lpTail B Q u t) = 0 ∧ Q (lpTail B Q u t) = lpTail B Q u t := by
  have hP : P (lpTail B Q u t) = 0 := by
    rw [lpTail, linearMap_tsum P (summable_lpTail hD hu t)]
    simp only [hD.PB, tsum_zero]
  refine ⟨hP, ?_⟩
  have := hD.PQ (lpTail B Q u t); rw [hP, zero_add] at this; exact this

/-- **Lipschitz dependence on `ξ`.** Two solutions of the integral equation, through `ξ` and `ξ'`,
satisfy `‖z_t − z'_t‖ ≤ 2K‖ξ − ξ'‖γᵗ`; and the unstable parts of `z₀`, `z'₀` differ by at most
`KcM/(1 − cγ)` when `‖r(z_j) − r(z'_j)‖ ≤ Mγʲ`. -/
theorem lp_lipschitz (hD : LPData A B P Q K a c γ) {r : (ι → ℝ) → ι → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hr0 : r 0 = 0) (hr : ∀ x y, ‖r x - r y‖ ≤ ε * ‖x - y‖)
    (hsmall : K * ε * (1 / (γ - a) + c / (1 - c * γ)) ≤ 1 / 2) {ξ ξ' : ι → ℝ}
    {z z' : ℕ → ι → ℝ} {C : ℝ} (hzb : ∀ t, ‖z t‖ ≤ C * γ ^ t) (hzb' : ∀ t, ‖z' t‖ ≤ C * γ ^ t)
    (hz : ∀ t, z t = (A ^ t) *ᵥ P ξ + lpHead A P (fun j => r (z j)) t -
      lpTail B Q (fun j => r (z j)) t)
    (hz' : ∀ t, z' t = (A ^ t) *ᵥ P ξ' + lpHead A P (fun j => r (z' j)) t -
      lpTail B Q (fun j => r (z' j)) t) :
    (∀ t, ‖z t - z' t‖ ≤ 2 * K * ‖ξ - ξ'‖ * γ ^ t) ∧
      ∀ M, (∀ j, ‖r (z j) - r (z' j)‖ ≤ M * γ ^ j) →
        ‖Q (z 0) - Q (z' 0)‖ ≤ K * c * M / (1 - c * γ) := by
  have hγ : 0 < γ := hD.a_nn.trans_lt hD.aγ
  have hK := hD.K_nn
  set Λ := 1 / (γ - a) + c / (1 - c * γ)
  have hΛ : 0 ≤ Λ := by
    have : 0 < γ - a := by linarith [hD.aγ]
    have : 0 < 1 - c * γ := by linarith [hD.cγ]
    have := hD.c_pos
    positivity
  set u : ℕ → ι → ℝ := fun j => r (z j)
  set u' : ℕ → ι → ℝ := fun j => r (z' j)
  have hub : ∀ j, ‖u j‖ ≤ (ε * C) * γ ^ j := fun j => by
    have h1 := hr (z j) 0
    rw [sub_zero, hr0, sub_zero] at h1
    have := mul_le_mul_of_nonneg_left (hzb j) hε
    simp only [u]; linarith [show ε * (C * γ ^ j) = ε * C * γ ^ j by ring]
  have hub' : ∀ j, ‖u' j‖ ≤ (ε * C) * γ ^ j := fun j => by
    have h1 := hr (z' j) 0
    rw [sub_zero, hr0, sub_zero] at h1
    have := mul_le_mul_of_nonneg_left (hzb' j) hε
    simp only [u']; linarith [show ε * (C * γ ^ j) = ε * C * γ ^ j by ring]
  have hdiff : ∀ t, z t - z' t = (A ^ t) *ᵥ P (ξ - ξ') +
      (lpHead A P (u - u') t - lpTail B Q (u - u') t) := fun t => by
    rw [hz t, hz' t, ← lpHead_sub, ← lpTail_sub hD hub hub', map_sub, Matrix.mulVec_sub]
    abel
  -- the weighted sup of the difference
  set d : ℕ → ℝ := fun t => (γ ^ t)⁻¹ * ‖z t - z' t‖
  have hdb : ∀ t, d t ≤ 2 * C := fun t => by
    simp only [d]
    rw [inv_mul_le_iff₀ (pow_pos hγ t)]
    have := norm_sub_le (z t) (z' t)
    linarith [hzb t, hzb' t]
  have hbdd : BddAbove (Set.range d) := ⟨2 * C, by rintro _ ⟨t, rfl⟩; exact hdb t⟩
  set D := ⨆ t, d t
  have hdD : ∀ t, d t ≤ D := fun t => le_ciSup hbdd t
  have hD0 : 0 ≤ D := (by positivity : 0 ≤ d 0).trans (hdD 0)
  have hzz : ∀ t, ‖z t - z' t‖ ≤ D * γ ^ t := fun t => by
    have := hdD t
    simp only [d] at this
    rwa [inv_mul_le_iff₀ (pow_pos hγ t), mul_comm] at this
  have hud : ∀ j, ‖(u - u') j‖ ≤ (ε * D) * γ ^ j := fun j => by
    have := hr (z j) (z' j)
    have := mul_le_mul_of_nonneg_left (hzz j) hε
    simp only [Pi.sub_apply, u, u']
    linarith [show ε * (D * γ ^ j) = ε * D * γ ^ j by ring]
  have hstep : ∀ t, d t ≤ K * ‖ξ - ξ'‖ + D / 2 := fun t => by
    simp only [d]
    rw [inv_mul_le_iff₀ (pow_pos hγ t), hdiff t]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(A ^ t) *ᵥ P (ξ - ξ')‖ ≤ K * ‖ξ - ξ'‖ * γ ^ t := by
      refine (hD.bA t _).trans ?_
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.a_nn hD.aγ.le t)
        (mul_nonneg hK (norm_nonneg (ξ - ξ')))
      linarith [show K * ‖ξ - ξ'‖ * a ^ t = K * a ^ t * ‖ξ - ξ'‖ by ring]
    have h2 := norm_head_sub_tail_le hD (mul_nonneg hε hD0) hud t
    have h3 : K * (ε * D) * Λ ≤ D / 2 := by
      have := mul_le_mul_of_nonneg_right hsmall hD0
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hγ.le t)
    nlinarith
  have hDle : D ≤ 2 * K * ‖ξ - ξ'‖ := by
    have : D ≤ K * ‖ξ - ξ'‖ + D / 2 := ciSup_le hstep
    linarith
  refine ⟨fun t => (hzz t).trans ?_, fun M hM => ?_⟩
  · exact mul_le_mul_of_nonneg_right hDle (pow_nonneg hγ.le t)
  · have hM' : ∀ j, ‖(u - u') j‖ ≤ M * γ ^ j := fun j => by
      simp only [Pi.sub_apply, u, u']; exact hM j
    have hQP : Q (P (ξ - ξ')) = 0 := by
      have := hD.PQ (P (ξ - ξ')); rw [hD.PP] at this; exact add_eq_left.1 this
    have e : Q (z 0) - Q (z' 0) = -lpTail B Q (u - u') 0 := by
      rw [← map_sub, hdiff 0]
      simp only [lpHead, Finset.range_zero, Finset.sum_empty, zero_sub, pow_zero,
        Matrix.one_mulVec, map_add, map_neg, hQP, (proj_lpTail hD hM' 0).2, zero_add]
    rw [e, norm_neg]
    have := norm_lpTail_le hD hM' 0
    simpa using this

end StokeyLucasPrescott.DeterministicDynamics
