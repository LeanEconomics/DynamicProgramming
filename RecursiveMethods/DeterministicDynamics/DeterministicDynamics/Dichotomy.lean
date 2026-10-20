/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.RealSplitting

/-!
# Exponential dichotomy of a real matrix

SLP §6.3, pp. 146–148, the estimates behind Theorem 6.6. With `ℝⁿ = E_s ⊕ E_u`
(`RealSplitting`) and the projections `P_s`, `Q_u` (`projS`, `projU`), which commute with `A`:

* `stable_bound`: there is `a < 1` with `‖AᵏP_s z‖ ≤ K aᵏ‖z‖`. Take `a` between the largest
  characteristic root inside the unit circle and `1`; the generalized eigenspaces of `A` and of
  `a⁻¹A` agree (`mem_maxGen_smul`), so `a⁻ᵏAᵏP_s z → 0`, and a bound on a basis is uniform
  (`uniform_bound_of_basis`).
* `M = A + P_s` is invertible (`isUnit_shift`): `A + I` is invertible on `E_s`, `A` on `E_u`.
  On `E_u`, `B = M⁻¹` inverts `A` (`inv_left`, `inv_right`, `inv_mem`).
* `unstable_bound`: for every `c > 1`, `‖BᵏQ_u z‖ ≤ K cᵏ‖z‖`. On the complex unstable subspace
  `M` acts as `A`, so the generalized eigenspace of `A` at `μ`, `|μ| ≥ 1`, lies in that of
  `M⁻¹` at `μ⁻¹`, and `c⁻ᵏM⁻ᵏ → 0` there.
-/

open Set Filter Topology Module
open scoped Matrix ComplexConjugate

namespace StokeyLucasPrescott.DeterministicDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bounds on a basis are uniform bounds. -/
theorem uniform_bound_of_basis (T : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (h : ∀ i, ∃ C, ∀ k, ‖T k (Pi.single i 1)‖ ≤ C) :
    ∃ K, 0 ≤ K ∧ ∀ k z, ‖T k z‖ ≤ K * ‖z‖ := by
  choose C hC using h
  refine ⟨∑ i, max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun k z => ?_⟩
  have hz : z = ∑ i, z i • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  calc ‖T k z‖ = ‖∑ i, z i • T k (Pi.single i 1)‖ := by
        conv_lhs => rw [hz]
        rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i, ‖z i • T k (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖z‖ * max (C i) 0 := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm z i) ((hC i k).trans (le_max_left _ _))
          (norm_nonneg _) (norm_nonneg _)
    _ = (∑ i, max (C i) 0) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]

omit [DecidableEq ι] in
/-- A convergent sequence of vectors is bounded. -/
theorem exists_bound_of_tendsto {u : ℕ → ι → ℝ} {L : ι → ℝ} (h : Tendsto u atTop (𝓝 L)) :
    ∃ C, ∀ k, ‖u k‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.norm.bddAbove_range
  exact ⟨C, fun k => hC ⟨k, rfl⟩⟩

/-- Scaling an operator scales its generalized eigenvalues. -/
theorem mem_maxGen_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (g : Module.End ℂ V)
    {c ν : ℂ} {w : V} (hw : w ∈ g.maxGenEigenspace ν) :
    w ∈ (c • g).maxGenEigenspace (c * ν) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  have e : c • g - (c * ν) • (1 : Module.End ℂ V) = c • (g - ν • 1) := by
    rw [smul_sub, smul_smul]
  rw [e, smul_pow, LinearMap.smul_apply, hk, smul_zero]

/-! ### The projections -/

/-- The projection onto `E_s` along `E_u`. -/
noncomputable def projS (A : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (stableR A).projection (unstableR A) (isCompl_stableR_unstableR A)

/-- The projection onto `E_u` along `E_s`. -/
noncomputable def projU (A : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (unstableR A).projection (stableR A) (isCompl_stableR_unstableR A).symm

theorem projS_add_projU (A : Matrix ι ι ℝ) (z : ι → ℝ) : projS A z + projU A z = z :=
  Submodule.projection_add_projection_eq_self _ z

theorem projS_mem (A : Matrix ι ι ℝ) (z : ι → ℝ) : projS A z ∈ stableR A :=
  Submodule.projection_apply_mem _ z

theorem projU_mem (A : Matrix ι ι ℝ) (z : ι → ℝ) : projU A z ∈ unstableR A :=
  Submodule.projection_apply_mem _ z

theorem projS_of_mem (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ stableR A) : projS A z = z :=
  Submodule.projection_apply_left _ ⟨z, hz⟩

theorem projS_of_mem_unstable (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A) :
    projS A z = 0 :=
  Submodule.projection_apply_right _ ⟨z, hz⟩

theorem projU_of_mem (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A) : projU A z = z :=
  Submodule.projection_apply_left _ ⟨z, hz⟩

theorem projU_of_mem_stable (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ stableR A) :
    projU A z = 0 :=
  Submodule.projection_apply_right _ ⟨z, hz⟩

theorem projS_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : projS A (A *ᵥ z) = A *ᵥ projS A z := by
  conv_lhs => rw [← projS_add_projU A z, Matrix.mulVec_add, map_add]
  rw [projS_of_mem A (stableR_invariant A (projS_mem A z)),
    projS_of_mem_unstable A (unstableR_invariant A (projU_mem A z)), add_zero]

theorem projU_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : projU A (A *ᵥ z) = A *ᵥ projU A z := by
  conv_lhs => rw [← projS_add_projU A z, Matrix.mulVec_add, map_add]
  rw [projU_of_mem_stable A (stableR_invariant A (projS_mem A z)),
    projU_of_mem A (unstableR_invariant A (projU_mem A z)), zero_add]

theorem pow_mulVec_mem_stableR (A : Matrix ι ι ℝ) (k : ℕ) {z : ι → ℝ} (hz : z ∈ stableR A) :
    (A ^ k) *ᵥ z ∈ stableR A := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact stableR_invariant A ih

/-! ### The stable estimate -/

/-- A complex vector in `S` whose `a⁻¹`-scaled orbit decays, when `a` exceeds every root inside
the unit circle. -/
theorem tendsto_scaled_of_stable (A : Matrix ι ι ℝ) {a : ℝ} (ha : 0 < a)
    (hroot : ∀ μ ∈ (A.charpoly.map Complex.ofRealHom).roots, ‖μ‖ < 1 → ‖μ‖ < a)
    {w : ι → ℂ} (hw : w ∈ stableSubspace (cplxEnd A)) :
    Tendsto (fun t => ((((a⁻¹ : ℝ) : ℂ) • cplxEnd A) ^ t) w) atTop (𝓝 0) := by
  set f := cplxEnd A
  have hcp : LinearMap.charpoly f = A.charpoly.map Complex.ofRealHom := by
    simp only [f, cplxEnd]
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  suffices hle : stableSubspace f ≤ convSubspace ((((a⁻¹ : ℝ) : ℂ)) • f) from hle hw
  refine iSup₂_le fun μ hμ => ?_
  by_cases hr : μ ∈ (LinearMap.charpoly f).roots
  · intro v hv
    have hμa : ‖((a⁻¹ : ℝ) : ℂ) * μ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha),
        inv_mul_lt_iff₀ ha, mul_one]
      exact hroot μ (hcp ▸ hr) hμ
    exact tendsto_of_mem_maxGenEigenspace hμa (mem_maxGen_smul f hv)
  · have : f.maxGenEigenspace μ = ⊥ := by
      rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_eq_zero fun h =>
        hr ((Polynomial.mem_roots f.charpoly_monic.ne_zero).2 h)
    rw [this]; exact bot_le

theorem scaled_pow_cplx (A : Matrix ι ι ℝ) (s : ℝ) (t : ℕ) (z : ι → ℝ) :
    ((((s : ℂ)) • cplxEnd A) ^ t) (cplx z) = cplx (s ^ t • (A ^ t) *ᵥ z) := by
  rw [smul_pow, LinearMap.smul_apply, cplxEnd_pow_cplx]
  funext i; simp [cplx, Matrix.mulVec, dotProduct]

/-- **The stable estimate.** -/
theorem stable_bound (A : Matrix ι ι ℝ) :
    ∃ a, 0 < a ∧ a < 1 ∧ ∃ K, 0 ≤ K ∧ ∀ k z, ‖(A ^ k) *ᵥ projS A z‖ ≤ K * a ^ k * ‖z‖ := by
  set T := ((A.charpoly.map Complex.ofRealHom).roots.filter fun μ => ‖μ‖ < 1).toFinset
  set ρ : ℝ := ((T.sup fun μ => ‖μ‖₊ : NNReal) : ℝ)
  have hρ0 : 0 ≤ ρ := NNReal.coe_nonneg _
  have hρ1 : ρ < 1 := by
    have : (T.sup fun μ => ‖μ‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by norm_num)]
      intro μ hμ
      have := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hμ)).2
      exact_mod_cast this
    exact_mod_cast this
  set a := (ρ + 1) / 2
  have ha0 : 0 < a := by simp only [a]; linarith
  have ha1 : a < 1 := by simp only [a]; linarith
  have hroot : ∀ μ ∈ (A.charpoly.map Complex.ofRealHom).roots, ‖μ‖ < 1 → ‖μ‖ < a :=
    fun μ hμ h1 => by
      have hT : μ ∈ T := Multiset.mem_toFinset.2 (Multiset.mem_filter.2 ⟨hμ, h1⟩)
      have : ‖μ‖₊ ≤ T.sup fun μ => ‖μ‖₊ := Finset.le_sup (f := fun μ => ‖μ‖₊) hT
      have : ‖μ‖ ≤ ρ := by exact_mod_cast this
      simp only [a]; linarith
  set L : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := fun k =>
    (a⁻¹) ^ k • (Matrix.toLin' (A ^ k) ∘ₗ projS A)
  have hL : ∀ k z, L k z = (a⁻¹) ^ k • (A ^ k) *ᵥ projS A z := fun k z => by
    simp only [L, LinearMap.smul_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
  obtain ⟨K, hK0, hK⟩ := uniform_bound_of_basis L fun i => by
    have hs : cplx (projS A (Pi.single i 1)) ∈ stableSubspace (cplxEnd A) := projS_mem A _
    have h := tendsto_scaled_of_stable A ha0 hroot hs
    simp only [scaled_pow_cplx] at h
    obtain ⟨C, hC⟩ := exists_bound_of_tendsto (tendsto_cplx_iff.1 h)
    exact ⟨C, fun k => by rw [hL]; exact hC k⟩
  refine ⟨a, ha0, ha1, K, hK0, fun k z => ?_⟩
  have h1 := hK k z
  rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.2 ha0) k), inv_pow,
    inv_mul_le_iff₀ (pow_pos ha0 k)] at h1
  linarith

/-! ### The unstable estimate -/

theorem cplxEnd_mul (M N : Matrix ι ι ℝ) : cplxEnd (M * N) = cplxEnd M * cplxEnd N := by
  rw [cplxEnd, cplxEnd, cplxEnd, Matrix.map_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

theorem cplxEnd_one : cplxEnd (1 : Matrix ι ι ℝ) = 1 := by
  rw [cplxEnd, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]; rfl

theorem cplxEnd_add (M N : Matrix ι ι ℝ) : cplxEnd (M + N) = cplxEnd M + cplxEnd N := by
  rw [cplxEnd, cplxEnd, cplxEnd, Matrix.map_add _ (map_add _), map_add]

/-- The matrix of `P_s`. -/
noncomputable def projSm (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := LinearMap.toMatrix' (projS A)

theorem projSm_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : projSm A *ᵥ z = projS A z :=
  LinearMap.toMatrix'_mulVec _ z

/-- The shift `M = A + P_s`. -/
noncomputable def shiftM (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := A + projSm A

theorem shiftM_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    shiftM A *ᵥ z = A *ᵥ z + projS A z := by
  rw [shiftM, Matrix.add_mulVec, projSm_mulVec]

/-- A stable vector with `As = −s` is zero. -/
theorem stable_neg_eigen (A : Matrix ι ι ℝ) {s : ι → ℝ} (hs : s ∈ stableR A)
    (hA : A *ᵥ s = -s) : s = 0 := by
  have hpow : ∀ t, (A ^ t) *ᵥ s = (-1 : ℝ) ^ t • s := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hA, pow_succ']
      rw [mul_smul]; simp
  have h := (mem_stableR_iff A s).1 hs
  simp only [hpow] at h
  have hn := h.norm
  simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_zero] at hn
  exact norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds hn)

/-- **`M = A + P_s` is invertible.** -/
theorem isUnit_shift (A : Matrix ι ι ℝ) : IsUnit (shiftM A) := by
  refine Matrix.mulVec_injective_iff_isUnit.1 fun z z' hzz' => ?_
  rw [← sub_eq_zero]
  set y := z - z'
  have hy : shiftM A *ᵥ y = 0 := by
    simp only [y, Matrix.mulVec_sub, hzz', sub_self]
  rw [shiftM_mulVec] at hy
  -- the stable and unstable parts of `Ay + P_s y = 0`
  have hu : A *ᵥ projU A y = 0 := by
    have := congrArg (projU A) hy
    rw [map_add, projU_mulVec, projU_of_mem_stable A (projS_mem A y), add_zero, map_zero] at this
    exact this
  have hs : A *ᵥ projS A y = -projS A y := by
    have := congrArg (projS A) hy
    rw [map_add, projS_mulVec, projS_of_mem A (projS_mem A y), map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have h1 := unstableR_ker A (projU_mem A y) hu
  have h2 := stable_neg_eigen A (projS_mem A y) hs
  rw [← projS_add_projU A y, h1, h2, add_zero]

/-- `B = M⁻¹`. -/
noncomputable def invB (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := (shiftM A)⁻¹

theorem shiftM_invB (A : Matrix ι ι ℝ) : shiftM A * invB A = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_shift A))

theorem invB_shiftM (A : Matrix ι ι ℝ) : invB A * shiftM A = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_shift A))

theorem shiftM_of_unstable (A : Matrix ι ι ℝ) {v : ι → ℝ} (hv : v ∈ unstableR A) :
    shiftM A *ᵥ v = A *ᵥ v := by
  rw [shiftM_mulVec, projS_of_mem_unstable A hv, add_zero]

/-- `B` maps `E_u` into itself. -/
theorem inv_mem (A : Matrix ι ι ℝ) {v : ι → ℝ} (hv : v ∈ unstableR A) :
    invB A *ᵥ v ∈ unstableR A := by
  set y := invB A *ᵥ v
  have hy : shiftM A *ᵥ y = v := by
    simp only [y, Matrix.mulVec_mulVec, shiftM_invB, Matrix.one_mulVec]
  rw [shiftM_mulVec] at hy
  have hs : A *ᵥ projS A y = -projS A y := by
    have := congrArg (projS A) hy
    rw [map_add, projS_mulVec, projS_of_mem A (projS_mem A y), projS_of_mem_unstable A hv]
      at this
    exact eq_neg_of_add_eq_zero_left this
  have h2 := stable_neg_eigen A (projS_mem A y) hs
  rw [← projS_add_projU A y, h2, zero_add]
  exact projU_mem A y

/-- On `E_u`, `A(Bv) = v`. -/
theorem inv_right (A : Matrix ι ι ℝ) {v : ι → ℝ} (hv : v ∈ unstableR A) :
    A *ᵥ (invB A *ᵥ v) = v := by
  rw [← shiftM_of_unstable A (inv_mem A hv), Matrix.mulVec_mulVec, shiftM_invB,
    Matrix.one_mulVec]

/-- On `E_u`, `B(Av) = v`. -/
theorem inv_left (A : Matrix ι ι ℝ) {v : ι → ℝ} (hv : v ∈ unstableR A) :
    invB A *ᵥ (A *ᵥ v) = v := by
  rw [← shiftM_of_unstable A hv, Matrix.mulVec_mulVec, invB_shiftM, Matrix.one_mulVec]

/-- The complexified `P_s` vanishes on the complex unstable subspace. -/
theorem cplx_projS_unstable (A : Matrix ι ι ℝ) {w : ι → ℂ}
    (hw : w ∈ unstableSubspace (cplxEnd A)) : cplxEnd (projSm A) w = 0 := by
  set U := unstableSubspace (cplxEnd A)
  have hre : (fun i => (w i).re) ∈ unstableR A := by
    rw [mem_unstableR]
    have : cplx (fun i => (w i).re) = (1 / 2 : ℂ) • (w + conjV w) := by
      funext i; simp only [cplx, Pi.smul_apply, Pi.add_apply, conjV, smul_eq_mul]
      rw [Complex.add_conj]; push_cast; ring
    rw [this]
    exact U.smul_mem _ (U.add_mem hw (conjV_mem_unstable A hw))
  have him : (fun i => (w i).im) ∈ unstableR A := by
    rw [mem_unstableR]
    have : cplx (fun i => (w i).im) = (-Complex.I / 2) • (w - conjV w) := by
      funext i; simp only [cplx, Pi.smul_apply, Pi.sub_apply, conjV, smul_eq_mul]
      rw [Complex.sub_conj]
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination ((w i).im : ℂ) * this
    rw [this]
    exact U.smul_mem _ (U.sub_mem hw (conjV_mem_unstable A hw))
  have hsplit : w = cplx (fun i => (w i).re) + Complex.I • cplx (fun i => (w i).im) := by
    funext i
    simp only [cplx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have h0 : ∀ x ∈ unstableR A, cplxEnd (projSm A) (cplx x) = 0 := fun x hx => by
    rw [← cplx_mulVec, projSm_mulVec, projS_of_mem_unstable A hx]
    funext i; simp [cplx]
  rw [hsplit, map_add, map_smul, h0 _ hre, h0 _ him, smul_zero, add_zero]

/-- On the complex unstable subspace, the generalized eigenvectors of `A` at `μ` are generalized
eigenvectors of `M⁻¹` at `μ⁻¹`. -/
theorem mem_maxGen_invB (A : Matrix ι ι ℝ) {μ : ℂ} (hμ : 1 ≤ ‖μ‖) {v : ι → ℂ}
    (hv : v ∈ (cplxEnd A).maxGenEigenspace μ) :
    v ∈ (cplxEnd (invB A)).maxGenEigenspace μ⁻¹ := by
  set f := cplxEnd A
  set h := cplxEnd (shiftM A)
  set g := cplxEnd (invB A)
  have hμ0 : μ ≠ 0 := by intro h0; rw [h0, norm_zero] at hμ; linarith
  have hU : f.maxGenEigenspace μ ≤ unstableSubspace f :=
    le_biSup (fun μ => f.maxGenEigenspace μ) (show μ ∈ {μ : ℂ | 1 ≤ ‖μ‖} from hμ)
  have hhf : ∀ u ∈ unstableSubspace f, h u = f u := fun u hu => by
    simp only [h, shiftM, cplxEnd_add, LinearMap.add_apply, cplx_projS_unstable A hu, add_zero]
    rfl
  -- `(h − μ)ᵏ = (f − μ)ᵏ` on `U`
  have hpow : ∀ k, ∀ u ∈ unstableSubspace f,
      ((h - μ • (1 : Module.End ℂ (ι → ℂ))) ^ k) u = ((f - μ • 1) ^ k) u := fun k => by
    induction k with
    | zero => intro u _; rfl
    | succ k ih =>
      intro u hu
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
      have e : (h - μ • (1 : Module.End ℂ (ι → ℂ))) u = (f - μ • 1) u := by
        simp only [LinearMap.sub_apply, hhf u hu]
      rw [e]
      exact ih _ ((unstableSubspace f).sub_mem (unstable_invariant f hu)
        ((unstableSubspace f).smul_mem μ hu))
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  have hk' : ((h - μ • (1 : Module.End ℂ (ι → ℂ))) ^ k) v = 0 := by rw [hpow k v (hU hv), hk]
  -- `g − μ⁻¹ = (−μ⁻¹ g)(h − μ)` and the factors commute
  have hgh : g * h = 1 := by simp only [g, h, ← cplxEnd_mul, invB_shiftM, cplxEnd_one]
  have hhg : h * g = 1 := by simp only [g, h, ← cplxEnd_mul, shiftM_invB, cplxEnd_one]
  have hfac : g - μ⁻¹ • (1 : Module.End ℂ (ι → ℂ)) =
      ((-μ⁻¹) • g) * (h - μ • 1) := by
    simp only [_root_.mul_sub, _root_.smul_mul_assoc, _root_.mul_smul_comm, _root_.mul_one, hgh,
      _root_.smul_smul]
    simp only [_root_.mul_neg, mul_inv_cancel₀ hμ0, _root_.neg_smul, _root_.one_smul,
      _root_.sub_neg_eq_add]
    module
  have hcomm : Commute ((-μ⁻¹) • g) (h - μ • (1 : Module.End ℂ (ι → ℂ))) := by
    refine Commute.smul_left ?_ _
    refine (Commute.sub_right ?_ (Commute.smul_right (Commute.one_right g) μ))
    exact (hgh.trans hhg.symm)
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  rw [hfac, hcomm.mul_pow, Module.End.mul_apply, hk', map_zero]

/-- **The unstable estimate**: for every `c > 1`, `‖BᵏQ_u z‖ ≤ K cᵏ‖z‖`. -/
theorem unstable_bound (A : Matrix ι ι ℝ) {c : ℝ} (hc : 1 < c) :
    ∃ K, 0 ≤ K ∧ ∀ k z, ‖(invB A ^ k) *ᵥ projU A z‖ ≤ K * c ^ k * ‖z‖ := by
  have hc0 : 0 < c := by linarith
  set g := cplxEnd (invB A)
  have hconv : unstableSubspace (cplxEnd A) ≤ convSubspace ((((c⁻¹ : ℝ) : ℂ)) • g) := by
    refine iSup₂_le fun μ hμ v hv => ?_
    have hμ' : 1 ≤ ‖μ‖ := hμ
    have h1 := mem_maxGen_smul g (c := ((c⁻¹ : ℝ) : ℂ)) (mem_maxGen_invB A hμ' hv)
    refine tendsto_of_mem_maxGenEigenspace ?_ h1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc0)]
    have hμ0 : 0 < ‖μ‖ := by linarith
    rw [← mul_inv, inv_lt_one₀ (mul_pos hc0 hμ0)]
    nlinarith
  set L : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := fun k =>
    (c⁻¹) ^ k • (Matrix.toLin' (invB A ^ k) ∘ₗ projU A)
  have hL : ∀ k z, L k z = (c⁻¹) ^ k • (invB A ^ k) *ᵥ projU A z := fun k z => by
    simp only [L, LinearMap.smul_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
  obtain ⟨K, hK0, hK⟩ := uniform_bound_of_basis L fun i => by
    have hs : cplx (projU A (Pi.single i 1)) ∈ unstableSubspace (cplxEnd A) := projU_mem A _
    have h := hconv hs
    rw [mem_convSubspace] at h
    simp only [g, scaled_pow_cplx] at h
    obtain ⟨C, hC⟩ := exists_bound_of_tendsto (tendsto_cplx_iff.1 h)
    exact ⟨C, fun k => by rw [hL]; exact hC k⟩
  refine ⟨K, hK0, fun k z => ?_⟩
  have h1 := hK k z
  rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.2 hc0) k), inv_pow,
    inv_mul_le_iff₀ (pow_pos hc0 k)] at h1
  linarith

end StokeyLucasPrescott.DeterministicDynamics
