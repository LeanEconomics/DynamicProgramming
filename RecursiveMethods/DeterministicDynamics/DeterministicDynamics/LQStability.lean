/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.LinearQuadratic
import DeterministicDynamics.EulerLinear

/-!
# Global stability of linear–quadratic problems (Theorem 6.8)

SLP §6.4, pp. 151–153. The book diagonalizes `A` by a Jordan decomposition `A = B⁻¹ΛB` and
shows that the block `B₂₁` is nonsingular. Here the same steps run through the stable subspace
of `A` acting on `ℂ²ˡ` (`LinearSystems`):

* `finrank_stableSubspace`: the stable subspace has dimension equal to the number of
  characteristic roots (with multiplicity) inside the unit circle, since generalized
  eigenspaces are independent and each has dimension equal to the root's multiplicity.
* `hom_euler_eq_zero`: a solution `d` of the homogeneous Euler equations with `d₀ = 0` and
  `d_t → 0` is zero. With `g_t = d_t'(F_xx d_t + F_xy d_{t+1})`, the Euler equations give
  `2βᵗq(d_t, d_{t+1}) = βᵗg_t − βᵗ⁺¹g_{t+1}`; the sum telescopes to `0`, and `q < 0` off zero.
  This is the book's argument that `B₂₁` is nonsingular (two convergent Euler paths from the
  same `x₀` would both be optimal), without passing through optimality.
* `stable_inr_zero`: so the projection `(z₁, z₀) ↦ z₀` is injective on the stable subspace
  (the real and imaginary parts of a complex stable vector are real stable vectors). With
  `l` roots inside the unit circle the dimensions match, so it is onto: from every `z₀` there is
  a `z₁` with `(z₁, z₀)` stable (`exists_stable_start`).
* **Theorem 6.8** (`theorem_6_8`): from every `x₀` there is a unique optimal plan; it satisfies
  the Euler equations (2) and converges to `x̄`.
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ} {P Q R : Matrix (Fin l) (Fin l) ℝ} {a b : Fin l → ℝ} {c₀ β : ℝ}

/-! ### The dimension of the stable subspace -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The generalized eigenspaces are independent, so their dimensions add. -/
theorem finrank_biSup_maxGenEigenspace (f : Module.End ℂ V) (T : Finset ℂ) :
    finrank ℂ ↥(⨆ μ ∈ T, f.maxGenEigenspace μ) = ∑ μ ∈ T, finrank ℂ (f.maxGenEigenspace μ) := by
  refine Finset.induction_on T (by simp) ?_
  intro a T ha ih
  rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
  have hdis : Disjoint (f.maxGenEigenspace a) (⨆ μ ∈ T, f.maxGenEigenspace μ) := by
    have := (Module.End.independent_maxGenEigenspace f).disjoint_biSup (y := (T : Set ℂ))
      (by simpa using ha)
    simpa using this
  have := Submodule.finrank_sup_add_finrank_inf_eq (f.maxGenEigenspace a)
    (⨆ μ ∈ T, f.maxGenEigenspace μ)
  rw [hdis.eq_bot, finrank_bot, add_zero] at this
  exact this

/-- **The dimension of the stable subspace** is the number of characteristic roots, with
multiplicity, inside the unit circle. -/
theorem finrank_stableSubspace (f : Module.End ℂ V) :
    finrank ℂ (stableSubspace f) = (f.charpoly.roots.filter fun μ => ‖μ‖ < 1).card := by
  set T := (f.charpoly.roots.filter fun μ => ‖μ‖ < 1).toFinset
  have hT : ∀ μ, μ ∈ T ↔ μ ∈ f.charpoly.roots ∧ ‖μ‖ < 1 := fun μ => by
    simp [T]
  have hbot : ∀ μ, μ ∉ f.charpoly.roots → f.maxGenEigenspace μ = ⊥ := fun μ hμ => by
    rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_eq_zero fun h =>
      hμ ((Polynomial.mem_roots f.charpoly_monic.ne_zero).2 h)
  have heq : stableSubspace f = ⨆ μ ∈ T, f.maxGenEigenspace μ := by
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => ?_)
    · by_cases hr : μ ∈ f.charpoly.roots
      · exact le_biSup (fun μ => f.maxGenEigenspace μ) ((hT μ).2 ⟨hr, hμ⟩)
      · rw [hbot μ hr]; exact bot_le
    · exact le_biSup (fun μ => f.maxGenEigenspace μ) (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from
        ((hT μ).1 hμ).2)
  rw [heq, finrank_biSup_maxGenEigenspace, ← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [LinearMap.finrank_maxGenEigenspace_eq,
    Multiset.count_filter_of_pos (p := fun μ : ℂ => ‖μ‖ < 1) ((hT μ).1 hμ).2,
    Polynomial.count_roots]

/-! ### Real and imaginary parts -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_cplxEnd_apply (A : Matrix ι ι ℝ) (V : ι → ℂ) (i : ι) :
    (cplxEnd A V i).re = (A *ᵥ fun j => (V j).re) i := by
  simp [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Complex.re_sum]

theorem im_cplxEnd_apply (A : Matrix ι ι ℝ) (V : ι → ℂ) (i : ι) :
    (cplxEnd A V i).im = (A *ᵥ fun j => (V j).im) i := by
  simp [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Complex.im_sum]

theorem re_cplxEnd_pow (A : Matrix ι ι ℝ) (t : ℕ) (W : ι → ℂ) (i : ι) :
    ((cplxEnd A ^ t) W i).re = ((A ^ t) *ᵥ fun j => (W j).re) i := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, re_cplxEnd_apply, pow_succ', ← Matrix.mulVec_mulVec,
      show (fun j => ((cplxEnd A ^ t) W j).re) = (A ^ t) *ᵥ (fun j => (W j).re) from funext ih]

theorem im_cplxEnd_pow (A : Matrix ι ι ℝ) (t : ℕ) (W : ι → ℂ) (i : ι) :
    ((cplxEnd A ^ t) W i).im = ((A ^ t) *ᵥ fun j => (W j).im) i := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, im_cplxEnd_apply, pow_succ', ← Matrix.mulVec_mulVec,
      show (fun j => ((cplxEnd A ^ t) W j).im) = (A ^ t) *ᵥ (fun j => (W j).im) from funext ih]

/-- The real part of a complex stable vector is a real stable vector. -/
theorem tendsto_re_of_stable (A : Matrix ι ι ℝ) {W : ι → ℂ}
    (hW : W ∈ stableSubspace (cplxEnd A)) :
    Tendsto (fun t => (A ^ t) *ᵥ fun j => (W j).re) atTop (𝓝 0) := by
  have h := (tendsto_iff_mem_stable (cplxEnd A) W).2 hW
  rw [tendsto_pi_nhds] at h ⊢
  intro i
  have := (Complex.continuous_re.tendsto 0).comp (h i)
  simpa [Function.comp_def, re_cplxEnd_pow] using this

theorem tendsto_im_of_stable (A : Matrix ι ι ℝ) {W : ι → ℂ}
    (hW : W ∈ stableSubspace (cplxEnd A)) :
    Tendsto (fun t => (A ^ t) *ᵥ fun j => (W j).im) atTop (𝓝 0) := by
  have h := (tendsto_iff_mem_stable (cplxEnd A) W).2 hW
  rw [tendsto_pi_nhds] at h ⊢
  intro i
  have := (Complex.continuous_im.tendsto 0).comp (h i)
  simpa [Function.comp_def, im_cplxEnd_pow] using this

/-! ### The Euler equations in stacked form -/

theorem eulerA_mulVec_inl (V : Fin l ⊕ Fin l → ℝ) (i : Fin l) :
    (eulerA P Q R β *ᵥ V) (Sum.inl i) =
      (eulerJ P Q R β *ᵥ (V ∘ Sum.inl) + eulerK Q β *ᵥ (V ∘ Sum.inr)) i := by
  simp [eulerA, Matrix.fromBlocks_mulVec]

theorem eulerA_mulVec_inr (V : Fin l ⊕ Fin l → ℝ) (i : Fin l) :
    (eulerA P Q R β *ᵥ V) (Sum.inr i) = V (Sum.inl i) := by
  simp [eulerA, Matrix.fromBlocks_mulVec]

/-- Along an orbit `V_t = AᵗZ`, the second blocks `d_t` solve `d_{t+2} = Jd_{t+1} + Kd_t`. -/
theorem orbit_rec (Z : Fin l ⊕ Fin l → ℝ) (t : ℕ) :
    (fun i => ((eulerA P Q R β ^ (t + 2)) *ᵥ Z) (Sum.inr i)) =
      eulerJ P Q R β *ᵥ (fun i => ((eulerA P Q R β ^ (t + 1)) *ᵥ Z) (Sum.inr i)) +
        eulerK Q β *ᵥ (fun i => ((eulerA P Q R β ^ t) *ᵥ Z) (Sum.inr i)) := by
  have hs : ∀ n, (eulerA P Q R β ^ (n + 1)) *ᵥ Z = eulerA P Q R β *ᵥ ((eulerA P Q R β ^ n) *ᵥ Z) :=
    fun n => by rw [pow_succ', ← Matrix.mulVec_mulVec]
  have h1 : (fun i => ((eulerA P Q R β ^ (t + 1)) *ᵥ Z) (Sum.inr i)) =
      (eulerA P Q R β ^ t *ᵥ Z) ∘ Sum.inl := by
    funext i; rw [hs, eulerA_mulVec_inr]; rfl
  funext i
  rw [h1]
  change ((eulerA P Q R β ^ (t + 1 + 1)) *ᵥ Z) (Sum.inr i) = _
  rw [hs (t + 1), eulerA_mulVec_inr, hs t, eulerA_mulVec_inl]
  rfl

/-- The recursion `z₂ = Jz₁ + Kz₀` is the homogeneous Euler equation
`F'_xy z₀ + F_yy z₁ + β(F_xx z₁ + F_xy z₂) = 0`. -/
theorem euler_of_rec (hQ : Q.det ≠ 0) (hβ : β ≠ 0) {z₀ z₁ z₂ : Fin l → ℝ}
    (h : z₂ = eulerJ P Q R β *ᵥ z₁ + eulerK Q β *ᵥ z₀) :
    Qᵀ *ᵥ z₀ + R *ᵥ z₁ + β • (P *ᵥ z₁ + Q *ᵥ z₂) = 0 := by
  rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, fxy_mul_eulerJ hQ,
    fxy_mul_eulerK hQ]
  simp only [Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, smul_add,
    smul_neg, smul_smul, mul_inv_cancel₀ hβ, inv_mul_cancel₀ hβ, one_smul]
  abel

/-- **Two convergent Euler paths from the same point coincide**: a solution of the homogeneous
Euler equations with `d₀ = 0` and `d_t → 0` is zero. -/
theorem hom_euler_eq_zero (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ P Q R u v < 0) (hβ0 : 0 < β)
    (hβ1 : β < 1) {d : ℕ → Fin l → ℝ} (hd0 : d 0 = 0) (hdt : Tendsto d atTop (𝓝 0))
    (he : ∀ t, Qᵀ *ᵥ d t + R *ᵥ d (t + 1) + β • (P *ᵥ d (t + 1) + Q *ᵥ d (t + 2)) = 0) :
    ∀ t, d t = 0 := by
  set g : ℕ → ℝ := fun t => d t ⬝ᵥ (P *ᵥ d t + Q *ᵥ d (t + 1))
  set q : ℕ → ℝ := fun t => lqQ P Q R (d t) (d (t + 1))
  -- `2q_t = g_t − βg_{t+1}`
  have hkey : ∀ t, 2 * q t = g t - β * g (t + 1) := fun t => by
    have h := congrArg (d (t + 1) ⬝ᵥ ·) (he t)
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h
    have e : d (t + 1) ⬝ᵥ (Qᵀ *ᵥ d t) = d t ⬝ᵥ (Q *ᵥ d (t + 1)) := by
      rw [dotProduct_comm, dot_transpose]
    simp only [q, g, lqQ, dotProduct_add]
    rw [e] at h
    linarith
  -- `2Σ_{t<N} βᵗq_t = −β^N g_N`
  set S : ℕ → ℝ := fun N => ∑ t ∈ Finset.range N, β ^ t * q t
  have hg0 : g 0 = 0 := by simp [g, hd0]
  have hS : ∀ N, 2 * S N = -(β ^ N * g N) := fun N => by
    induction N with
    | zero => simp [S, hg0]
    | succ N ih =>
      simp only [S, Finset.sum_range_succ, mul_add] at ih ⊢
      rw [ih, show 2 * (β ^ N * q N) = β ^ N * (2 * q N) by ring, hkey, pow_succ]
      ring
  have hgt : Tendsto g atTop (𝓝 0) := by
    have hc : Continuous fun p : (Fin l → ℝ) × (Fin l → ℝ) => p.1 ⬝ᵥ (P *ᵥ p.1 + Q *ᵥ p.2) := by
      unfold dotProduct; fun_prop
    have hp : Tendsto (fun t => (d t, d (t + 1))) atTop (𝓝 (0, 0)) :=
      hdt.prodMk_nhds (hdt.comp (tendsto_add_atTop_nat 1))
    have h := (hc.tendsto (0, 0)).comp hp
    simp only [Function.comp_def, Matrix.mulVec_zero, add_zero, dotProduct_zero] at h
    exact h
  have hSt : Tendsto S atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul hgt).neg.div_const 2
    simp only [mul_zero, neg_zero, zero_div] at h
    refine h.congr fun N => ?_
    linarith [hS N]
  have hq : ∀ t, q t ≤ 0 := fun t => by
    by_cases h0 : (d t, d (t + 1)) = 0
    · obtain ⟨h1, h2⟩ := Prod.mk_eq_zero.1 h0
      simp only [q, h1, h2]; exact lqQ_zero_left.le
    · exact (hneg _ _ h0).le
  have hanti : Antitone S := antitone_nat_of_succ_le fun N => by
    simp only [S, Finset.sum_range_succ]
    nlinarith [hq N, pow_pos hβ0 N]
  have hS0 : ∀ N, S N = 0 := fun N => by
    have h1 := hanti.le_of_tendsto hSt N
    have h2 : S N ≤ 0 := Finset.sum_nonpos fun t _ =>
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0.le t) (hq t)
    linarith
  have hq0 : ∀ t, q t = 0 := fun t => by
    have h := hS0 (t + 1)
    simp only [S, Finset.sum_range_succ] at h
    have h' := hS0 t
    simp only [S] at h'
    rw [h', zero_add] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero t hβ0.ne')
  have hpair : ∀ t, (d t, d (t + 1)) = 0 := fun t => by
    by_contra hne
    exact (hneg _ _ hne).ne (hq0 t)
  intro t
  rcases t with _ | t
  · exact hd0
  · exact (Prod.mk_eq_zero.1 (hpair t)).2

/-- **A real stable vector with zero second block is zero.** -/
theorem stable_real_inr_zero (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ P Q R u v < 0)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : Q.det ≠ 0) {Z : Fin l ⊕ Fin l → ℝ}
    (hZ : ∀ i, Z (Sum.inr i) = 0)
    (ht : Tendsto (fun t => (eulerA P Q R β ^ t) *ᵥ Z) atTop (𝓝 0)) : Z = 0 := by
  set d : ℕ → Fin l → ℝ := fun t i => ((eulerA P Q R β ^ t) *ᵥ Z) (Sum.inr i)
  have hd0 : d 0 = 0 := by funext i; simp [d, hZ]
  have hdt : Tendsto d atTop (𝓝 0) := by
    rw [tendsto_pi_nhds] at ht ⊢
    exact fun i => ht (Sum.inr i)
  have hzero := hom_euler_eq_zero (P := P) (Q := Q) (R := R) hneg hβ0 hβ1 hd0 hdt
    fun t => euler_of_rec hQ hβ0.ne' (orbit_rec Z t)
  have h1 : ∀ i, Z (Sum.inl i) = 0 := fun i => by
    have := congrFun (hzero 1) i
    simp only [d, pow_one, eulerA_mulVec_inr] at this
    exact this
  funext j
  rcases j with i | i
  · exact h1 i
  · exact hZ i

/-- **A complex stable vector with zero second block is zero.** -/
theorem stable_inr_zero (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ P Q R u v < 0)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : Q.det ≠ 0) {W : Fin l ⊕ Fin l → ℂ}
    (hW : W ∈ stableSubspace (cplxEnd (eulerA P Q R β))) (h0 : ∀ i, W (Sum.inr i) = 0) :
    W = 0 := by
  have hre := stable_real_inr_zero hneg hβ0 hβ1 hQ (Z := fun j => (W j).re)
    (fun i => by simp [h0 i]) (tendsto_re_of_stable _ hW)
  have him := stable_real_inr_zero hneg hβ0 hβ1 hQ (Z := fun j => (W j).im)
    (fun i => by simp [h0 i]) (tendsto_im_of_stable _ hW)
  funext j
  exact Complex.ext (congrFun hre j) (congrFun him j)

/-- **From every `z₀` there is a `z₁` with `(z₁, z₀)` in the stable subspace**, when `A` has `l`
characteristic roots inside the unit circle. This is the book's `B₂₁` nonsingular. -/
theorem exists_stable_start (hneg : ∀ u v : Fin l → ℝ, (u, v) ≠ 0 → lqQ P Q R u v < 0)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : Q.det ≠ 0)
    (hroots : (((eulerA P Q R β).charpoly.map Complex.ofRealHom).roots.filter
      fun μ => ‖μ‖ < 1).card = l) (z₀ : Fin l → ℝ) :
    ∃ z₁ : Fin l → ℝ,
      Tendsto (fun t => (eulerA P Q R β ^ t) *ᵥ Sum.elim z₁ z₀) atTop (𝓝 0) := by
  set f := cplxEnd (eulerA P Q R β)
  set S := stableSubspace f
  set proj : S →ₗ[ℂ] (Fin l → ℂ) := (LinearMap.funLeft ℂ ℂ Sum.inr).comp S.subtype
  have hcp : LinearMap.charpoly f = (eulerA P Q R β).charpoly.map Complex.ofRealHom := by
    simp only [f, cplxEnd]
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  have hdim : finrank ℂ S = finrank ℂ (Fin l → ℂ) := by
    rw [Module.finrank_fin_fun, finrank_stableSubspace, hcp, hroots]
  have hinj : Function.Injective proj := by
    refine (injective_iff_map_eq_zero proj).2 fun w hw => Subtype.ext ?_
    exact stable_inr_zero hneg hβ0 hβ1 hQ w.2 fun i => congrFun hw i
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    (cplx z₀)
  refine ⟨fun i => ((w : Fin l ⊕ Fin l → ℂ) (Sum.inl i)).re, ?_⟩
  have e : Sum.elim (fun i => ((w : Fin l ⊕ Fin l → ℂ) (Sum.inl i)).re) z₀ =
      fun j => ((w : Fin l ⊕ Fin l → ℂ) j).re := by
    funext j
    rcases j with i | i
    · rfl
    · have := congrFun hw i
      simp only [proj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.funLeft_apply,
        cplx] at this
      simp [this]
  rw [e]
  exact tendsto_re_of_stable _ w.2

/-! ### Theorem 6.8 -/

/-- The stationary point `x̄ = −(F'_xy + F_yy + βF_xx + βF_xy)⁻¹(F̄_y + βF̄_x)`. -/
noncomputable def lqBar (P Q R : Matrix (Fin l) (Fin l) ℝ) (a b : Fin l → ℝ) (β : ℝ) :
    Fin l → ℝ :=
  -((Qᵀ + R + β • P + β • Q)⁻¹ *ᵥ (b + β • a))

theorem lqBar_stationary (hS : (Qᵀ + R + β • P + β • Q).det ≠ 0) :
    lqFy Q R b (lqBar P Q R a b β) (lqBar P Q R a b β) +
      β • lqFx P Q a (lqBar P Q R a b β) (lqBar P Q R a b β) = 0 := by
  have e : ∀ x, lqFy Q R b x x + β • lqFx P Q a x x =
      (b + β • a) + (Qᵀ + R + β • P + β • Q) *ᵥ x := fun x => by
    simp only [lqFy, lqFx, Matrix.add_mulVec, Matrix.smul_mulVec, smul_add]
    abel
  rw [e, lqBar, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hS), Matrix.one_mulVec, add_neg_cancel]

/-- **Theorem 6.8.** Let `F` be a strictly concave quadratic on `ℝˡ × ℝˡ`, `Γ(x) = ℝˡ`,
`0 < β < 1`, with `F_xy` and `F'_xy + F_yy + βF_xx + βF_xy` nonsingular, and suppose `A` has `l`
characteristic roots (with multiplicity) inside the unit circle. Then from every `x₀` there is a
unique optimal plan; it satisfies the Euler equations (2) and converges to `x̄`. -/
theorem theorem_6_8 (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hconc : StrictConcaveOn ℝ univ (lqF P Q R a b c₀)) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hQ : Q.det ≠ 0) (hS : (Qᵀ + R + β • P + β • Q).det ≠ 0)
    (hroots : (((eulerA P Q R β).charpoly.map Complex.ofRealHom).roots.filter
      fun μ => ‖μ‖ < 1).card = l) (x₀ : Fin l → ℝ) :
    ∃ xs : ℕ → Fin l → ℝ, xs 0 = x₀ ∧
      total (fun x y => lqF P Q R a b c₀ (x, y)) β xs =
        vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β x₀ ∧
      (∀ t, lqFy Q R b (xs t) (xs (t + 1)) + β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) = 0) ∧
      Tendsto xs atTop (𝓝 (lqBar P Q R a b β)) ∧
      ∀ y : ℕ → Fin l → ℝ, y 0 = x₀ →
        total (fun x y => lqF P Q R a b c₀ (x, y)) β y =
          vstar (fun _ => univ) (fun x y => lqF P Q R a b c₀ (x, y)) β x₀ → y = xs := by
  set xbar := lqBar P Q R a b β
  obtain ⟨z₁, hz⟩ := exists_stable_start (fun u v huv => lqQ_neg hconc huv) hβ0 hβ1 hQ hroots
    (x₀ - xbar)
  set Z := Sum.elim z₁ (x₀ - xbar)
  set z : ℕ → Fin l → ℝ := fun t i => ((eulerA P Q R β ^ t) *ᵥ Z) (Sum.inr i)
  set xs : ℕ → Fin l → ℝ := fun t => xbar + z t
  have hx0 : xs 0 = x₀ := by
    funext i; simp [xs, z, Z, xbar]
  have hzt : Tendsto z atTop (𝓝 0) := by
    rw [tendsto_pi_nhds] at hz ⊢
    exact fun i => hz (Sum.inr i)
  have hconv : Tendsto xs atTop (𝓝 xbar) := by
    have := hzt.const_add xbar
    rwa [add_zero] at this
  have heuler : ∀ t, lqFy Q R b (xs t) (xs (t + 1)) +
      β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) = 0 := fun t => by
    have hhom := euler_of_rec hQ hβ0.ne' (orbit_rec (P := P) (Q := Q) (R := R) (β := β) Z t)
    have e : lqFy Q R b (xs t) (xs (t + 1)) + β • lqFx P Q a (xs (t + 1)) (xs (t + 2)) =
        (lqFy Q R b xbar xbar + β • lqFx P Q a xbar xbar) +
          (Qᵀ *ᵥ z t + R *ᵥ z (t + 1) + β • (P *ᵥ z (t + 1) + Q *ᵥ z (t + 2))) := by
      simp only [xs, lqFy, lqFx, Matrix.mulVec_add, smul_add]
      abel
    rw [e, lqBar_stationary hS, zero_add]
    exact hhom
  have hopt := lq_sufficient (c₀ := c₀) hP hR hconc hβ0 hβ1 heuler hconv
  rw [hx0] at hopt
  refine ⟨xs, hx0, hopt, heuler, hconv, fun y hy0 hyopt => ?_⟩
  rw [← hx0] at hy0 hyopt hopt
  exact lq_unique hP hR hconc hβ0 hβ1 hconv hopt hy0 hyopt

end StokeyLucasPrescott.DeterministicDynamics
