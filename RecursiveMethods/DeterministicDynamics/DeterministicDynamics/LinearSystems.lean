/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Linear systems

SLP §6.3, pp. 143–147: `x_{t+1} = a₀ + Ax_t`, with `I − A` nonsingular and stationary point
`x̄ = (I − A)⁻¹a₀`, so that `z_t = x_t − x̄` solves `z_{t+1} = Az_t`.

The book argues through the Jordan form, which is not in Mathlib. Here the key fact is proved
for any operator `f` on a finite-dimensional complex normed space:
`fᵗz → 0` iff `z` lies in the **stable subspace**, the sum of the generalized eigenspaces of the
eigenvalues `|μ| < 1` (`tendsto_iff_mem_stable`).

* If `|μ| < 1`, `fᵗv → 0` on the generalized eigenspace of `μ`, by induction on the nilpotency
  index of `f − μ`. Each step solves `a_{t+1} = μa_t + e_t` with `e_t → 0`
  (`tendsto_zero_of_rec`).
* Conversely, the vectors with `fᵗz → 0` form an invariant subspace. If it met the unstable part,
  it would contain an eigenvector of an eigenvalue `|μ| ≥ 1`, along which `fᵗz = μᵗz`.

Then:

* **Theorem 6.3** (`theorem_6_3`): `x_t → x̄` from every `x₀` iff every characteristic root of `A`
  has absolute value less than one.
* **Theorem 6.4** (`theorem_6_4`), as stated in the book: if `A = B⁻¹ΛB` with `Λ` upper triangular
  (a Jordan matrix is one), its first `m` diagonal entries less than one in absolute value and
  the rest not, then `x_t → x̄` iff `x₀ = x̄ + B⁻¹w₀` with `w₀ᵢ = 0` for `i ≥ m`
  (`triangular_tendsto_iff`).
* (9) (`solution_eq`): `x_t = x̄ + B⁻¹ΛᵗB(x₀ − x̄)`.
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

/-! ### A perturbed geometric recursion -/

/-- If `b_{t+1} ≤ rb_t + c_t` with `0 ≤ r < 1`, `b ≥ 0` and `c_t → 0`, then `b_t → 0`. -/
theorem tendsto_zero_of_le_rec {b c : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb0 : ∀ t, 0 ≤ b t) (hc : Tendsto c atTop (𝓝 0)) (hrec : ∀ t, b (t + 1) ≤ r * b t + c t) :
    Tendsto b atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hc) (ε / 2 * (1 - r)) (by
    have : 0 < 1 - r := by linarith
    positivity)
  -- `b_t ≤ r^{t − T}b_T + ε/2` for `t ≥ T`
  have hbound : ∀ k, b (T + k) ≤ r ^ k * b T + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hcT : c (T + k) ≤ ε / 2 * (1 - r) := by
        have := hT (T + k) (by omega)
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans this.le
      have := hrec (T + k)
      rw [show T + (k + 1) = T + k + 1 by ring]
      calc b (T + k + 1) ≤ r * b (T + k) + c (T + k) := this
        _ ≤ r * (r ^ k * b T + ε / 2) + ε / 2 * (1 - r) := by
          have := mul_le_mul_of_nonneg_left ih hr0
          linarith
        _ = r ^ (k + 1) * b T + ε / 2 := by ring
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 / (b T + 1) by
    have := hb0 T; positivity) hr1
  refine ⟨T + K, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = T + k := ⟨t - T, by omega⟩
  have hk : r ^ k ≤ r ^ K := pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have h1 : r ^ k * b T < ε / 2 := by
    have hbT := hb0 T
    have : r ^ k * b T ≤ r ^ K * (b T + 1) := by
      have := pow_nonneg hr0 k
      nlinarith
    calc r ^ k * b T ≤ r ^ K * (b T + 1) := this
      _ < ε / 2 / (b T + 1) * (b T + 1) := mul_lt_mul_of_pos_right hK (by linarith)
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hb0 _)]
  linarith [hbound k]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- If `a_{t+1} = μa_t + e_t` with `|μ| < 1` and `e_t → 0`, then `a_t → 0`. -/
theorem tendsto_zero_of_rec {a e : ℕ → V} {μ : ℂ} (hμ : ‖μ‖ < 1) (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ t, a (t + 1) = μ • a t + e t) : Tendsto a atTop (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_zero_of_le_rec (norm_nonneg μ) hμ
    (fun t => norm_nonneg _) (tendsto_zero_iff_norm_tendsto_zero.1 he) fun t => ?_)
  rw [hrec, ← norm_smul]
  exact norm_add_le _ _

/-! ### The stable subspace -/

/-- The **stable subspace**: the generalized eigenspaces of the eigenvalues with `|μ| < 1`. -/
noncomputable def stableSubspace (f : End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | ‖μ‖ < 1}, f.maxGenEigenspace μ

/-- The **unstable subspace**: the generalized eigenspaces of the eigenvalues with `|μ| ≥ 1`. -/
noncomputable def unstableSubspace (f : End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | 1 ≤ ‖μ‖}, f.maxGenEigenspace μ

/-- The vectors whose orbits converge to zero. -/
noncomputable def convSubspace (f : End ℂ V) : Submodule ℂ V where
  carrier := {z | Tendsto (fun t => (f ^ t) z) atTop (𝓝 0)}
  add_mem' {x y} hx hy := by
    simp only [mem_ofPred_eq, map_add] at hx hy ⊢
    simpa using hx.add hy
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [mem_ofPred_eq, map_smul] at hx ⊢
    simpa using hx.const_smul c

theorem mem_convSubspace {f : End ℂ V} {z : V} :
    z ∈ convSubspace f ↔ Tendsto (fun t => (f ^ t) z) atTop (𝓝 0) := Iff.rfl

/-- On the generalized eigenspace of `|μ| < 1`, orbits converge to zero. -/
theorem tendsto_of_mem_maxGenEigenspace {f : End ℂ V} {μ : ℂ} (hμ : ‖μ‖ < 1) {v : V}
    (hv : v ∈ f.maxGenEigenspace μ) : Tendsto (fun t => (f ^ t) v) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ v).1 hv
  set N := f - μ • (1 : End ℂ V)
  have hcomm : ∀ t, N * f ^ t = f ^ t * N := fun t =>
    ((Commute.sub_left (Commute.refl f) (Commute.smul_left (Commute.one_left f) μ)).pow_right t).eq
  induction k generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply] at hk; subst hk; simp
  | succ k ih =>
    have hNv : (N ^ k) (N v) = 0 := by rw [← Module.End.mul_apply, ← pow_succ]; exact hk
    have hNv' := ih (Module.End.mem_maxGenEigenspace f μ (N v) |>.2 ⟨k, hNv⟩) hNv
    refine tendsto_zero_of_rec hμ hNv' fun t => ?_
    have h1 : ∀ w, f w = μ • w + N w := fun w => by simp [N]
    calc (f ^ (t + 1)) v = f ((f ^ t) v) := by rw [pow_succ', Module.End.mul_apply]
      _ = μ • (f ^ t) v + N ((f ^ t) v) := h1 _
      _ = μ • (f ^ t) v + (f ^ t) (N v) := by
        rw [← Module.End.mul_apply, hcomm t, Module.End.mul_apply]

/-- Along an eigenvector of `|μ| ≥ 1`, the orbit does not converge to zero. -/
theorem not_tendsto_of_eigen {f : End ℂ V} {μ : ℂ} (hμ : 1 ≤ ‖μ‖) {v : V} (hv : f v = μ • v)
    (hv0 : v ≠ 0) : ¬ Tendsto (fun t => (f ^ t) v) atTop (𝓝 0) := by
  intro h
  have hpow : ∀ t, (f ^ t) v = μ ^ t • v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have hn := (tendsto_zero_iff_norm_tendsto_zero.1 h)
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have : ∀ t, ‖v‖ ≤ ‖(f ^ t) v‖ := fun t => by
    rw [hpow, norm_smul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hμ)
  have := ge_of_tendsto' hn this
  linarith

theorem stable_le_conv (f : End ℂ V) : stableSubspace f ≤ convSubspace f :=
  iSup₂_le fun _ hμ _ hv => tendsto_of_mem_maxGenEigenspace hμ hv

theorem stable_sup_unstable [FiniteDimensional ℂ V] (f : End ℂ V) :
    stableSubspace f ⊔ unstableSubspace f = ⊤ := by
  refine eq_top_iff.2 ((Module.End.iSup_maxGenEigenspace_eq_top f).symm.le.trans
    (iSup_le fun μ => ?_))
  rcases lt_or_ge ‖μ‖ 1 with h | h
  · exact le_sup_of_le_left (le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from h))
  · exact le_sup_of_le_right (le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | 1 ≤ ‖μ‖} from h))

theorem disjoint_stable_unstable (f : End ℂ V) :
    Disjoint (stableSubspace f) (unstableSubspace f) :=
  (Module.End.independent_maxGenEigenspace f).disjoint_biSup_biSup
    (Set.disjoint_left.2 fun μ h1 h2 => by
      simp only [mem_ofPred_eq] at h1 h2; linarith)

theorem unstable_invariant (f : End ℂ V) {z : V} (hz : z ∈ unstableSubspace f) :
    f z ∈ unstableSubspace f := by
  have : unstableSubspace f ≤ (unstableSubspace f).comap f := iSup₂_le fun μ hμ v hv =>
    (le_biSup (fun μ => f.maxGenEigenspace μ) hμ)
      (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hv)
  exact this hz

/-- **Orbits converge to zero exactly on the stable subspace.** -/
theorem tendsto_iff_mem_stable [FiniteDimensional ℂ V] (f : End ℂ V) (z : V) :
    Tendsto (fun t => (f ^ t) z) atTop (𝓝 0) ↔ z ∈ stableSubspace f := by
  refine ⟨fun hz => ?_, fun hz => stable_le_conv f hz⟩
  -- the convergent vectors meet the unstable subspace only in zero
  set W := convSubspace f ⊓ unstableSubspace f
  have hWinv : ∀ w ∈ W, f w ∈ W := fun w hw => ⟨by
    change Tendsto _ _ _
    have := (mem_convSubspace.1 hw.1).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, pow_succ, Module.End.mul_apply] using this,
    unstable_invariant f hw.2⟩
  have hW : W = ⊥ := by
    by_contra hne
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hWinv)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hfw : f w = μ • (w : V) := by
      have := Module.End.mem_eigenspace_iff.1 hw.1
      rw [Subtype.ext_iff] at this
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hstab : ‖μ‖ < 1 := by
      by_contra hge
      exact not_tendsto_of_eigen (not_lt.1 hge) hfw hw0 (mem_convSubspace.1 w.2.1)
    have hs : (w : V) ∈ stableSubspace f := le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hstab)
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hfw))
    exact hw0 ((Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs w.2.2)
  -- split `z` along stable ⊕ unstable
  have hztop : z ∈ stableSubspace f ⊔ unstableSubspace f := by
    rw [stable_sup_unstable]; exact Submodule.mem_top
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.1 hztop
  have huc : u ∈ convSubspace f := by
    have := (convSubspace f).sub_mem hz (stable_le_conv f hs)
    simpa using this
  have hu0 : u = 0 := by
    have : u ∈ W := ⟨huc, hu⟩
    rw [hW] at this
    exact (Submodule.mem_bot ℂ).1 this
  simpa [hu0] using hs

/-- If every eigenvalue lies inside the unit disc, the stable subspace is everything. -/
theorem stable_eq_top [FiniteDimensional ℂ V] (f : End ℂ V)
    (h : ∀ μ, f.HasEigenvalue μ → ‖μ‖ < 1) : stableSubspace f = ⊤ := by
  have hu : unstableSubspace f = ⊥ := by
    by_contra hne
    have : Nontrivial (unstableSubspace f) := Submodule.nontrivial_iff_ne_bot.2 hne
    have hinv : ∀ w ∈ unstableSubspace f, f w ∈ unstableSubspace f := fun w hw =>
      unstable_invariant f hw
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hinv)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hfw : f w = μ • (w : V) := by
      have := Module.End.mem_eigenspace_iff.1 hw.1
      rw [Subtype.ext_iff] at this
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hstab := h μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hfw, hw0⟩)
    have hs : (w : V) ∈ stableSubspace f := le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hstab)
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hfw))
    exact hw0 ((Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs w.2)
  have := stable_sup_unstable f
  rwa [hu, sup_bot_eq] at this

/-! ### Matrices -/

variable {ι : Type*}

/-- A real vector as a complex vector. -/
def cplx (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

theorem cplx_sub (x y : ι → ℝ) : cplx (x - y) = cplx x - cplx y := by
  funext i; simp [cplx]

theorem cplx_add (x y : ι → ℝ) : cplx (x + y) = cplx x + cplx y := by
  funext i; simp [cplx]

theorem tendsto_cplx_iff {y : ℕ → ι → ℝ} :
    Tendsto (fun t => cplx (y t)) atTop (𝓝 0) ↔ Tendsto y atTop (𝓝 0) := by
  simp only [tendsto_pi_nhds, cplx, Pi.zero_apply]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · have := (Complex.continuous_re.tendsto 0).comp h
    simpa [Function.comp_def] using this
  · have := (Complex.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using this

variable [Fintype ι] [DecidableEq ι]

/-- `A` acting on `ℂⁿ`. -/
noncomputable def cplxEnd (A : Matrix (ι) (ι) ℝ) : End ℂ (ι → ℂ) :=
  Matrix.toLin' (A.map Complex.ofRealHom)

theorem cplxEnd_pow_cplx (A : Matrix (ι) (ι) ℝ) (t : ℕ) (z : ι → ℝ) :
    (cplxEnd A ^ t) (cplx z) = cplx ((A ^ t) *ᵥ z) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← Matrix.mulVec_mulVec]
    funext i
    simp only [cplxEnd, Matrix.toLin'_apply, cplx]
    exact (RingHom.map_mulVec Complex.ofRealHom A _ i).symm

/-- The characteristic roots of `A` are the eigenvalues of `A` on `ℂⁿ`. -/
theorem hasEigenvalue_cplxEnd_iff (A : Matrix (ι) (ι) ℝ) (μ : ℂ) :
    (cplxEnd A).HasEigenvalue μ ↔ (A.charpoly.map Complex.ofRealHom).IsRoot μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, cplxEnd, Matrix.charpoly_toLin',
    Matrix.charpoly_map]

/-- The stationary point `x̄ = (I − A)⁻¹a₀` and the deviations `x_t − x̄ = Aᵗ(x₀ − x̄)`. -/
theorem deviation_eq (A : Matrix (ι) (ι) ℝ) (a₀ : ι → ℝ) (hI : IsUnit (1 - A).det)
    {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = a₀ + A *ᵥ x t) (t : ℕ) :
    x t - (1 - A)⁻¹ *ᵥ a₀ = (A ^ t) *ᵥ (x 0 - (1 - A)⁻¹ *ᵥ a₀) := by
  set xbar := (1 - A)⁻¹ *ᵥ a₀
  have hbar : xbar = a₀ + A *ᵥ xbar := by
    have h1 : (1 - A) *ᵥ xbar = a₀ := by
      simp only [xbar, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hI, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]; abel
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx t, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
    conv_lhs => rw [hbar]
    rw [Matrix.mulVec_sub]
    abel

/-- **Theorem 6.3.** `x_t → x̄` from every `x₀` if and only if every characteristic root of `A` is
less than one in absolute value. -/
theorem theorem_6_3 (A : Matrix (ι) (ι) ℝ) (a₀ : ι → ℝ) (hI : IsUnit (1 - A).det) :
    (∀ x : ℕ → ι → ℝ, (∀ t, x (t + 1) = a₀ + A *ᵥ x t) →
      Tendsto x atTop (𝓝 ((1 - A)⁻¹ *ᵥ a₀))) ↔
    ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1 := by
  set xbar := (1 - A)⁻¹ *ᵥ a₀
  -- convergence from `x₀` is convergence of `Aᵗ(x₀ − x̄)` to zero
  have hconv : ∀ x : ℕ → ι → ℝ, (∀ t, x (t + 1) = a₀ + A *ᵥ x t) →
      (Tendsto x atTop (𝓝 xbar) ↔
        Tendsto (fun t => (A ^ t) *ᵥ (x 0 - xbar)) atTop (𝓝 0)) := fun x hx => by
    rw [← tendsto_sub_nhds_zero_iff, show (fun t => x t - xbar) =
      fun t => (A ^ t) *ᵥ (x 0 - xbar) from funext (deviation_eq A a₀ hI hx)]
  -- every `z` is the initial deviation of some solution
  have hsol : ∀ z : ι → ℝ, ∃ x : ℕ → ι → ℝ, (∀ t, x (t + 1) = a₀ + A *ᵥ x t) ∧
      x 0 - xbar = z := fun z => by
    refine ⟨fun t => Nat.rec (xbar + z) (fun _ y => a₀ + A *ᵥ y) t, fun t => rfl, ?_⟩
    simp
  constructor
  · intro h μ hμ
    by_contra hge
    push Not at hge
    obtain ⟨w, hw⟩ := ((hasEigenvalue_cplxEnd_iff A μ).2 hμ).exists_hasEigenvector
    have hfw : cplxEnd A w = μ • w := Module.End.mem_eigenspace_iff.1 hw.1
    -- real and imaginary parts
    set r : ι → ℝ := fun i => (w i).re
    set q : ι → ℝ := fun i => (w i).im
    have hwrq : w = cplx r + Complex.I • cplx q := by
      funext i
      simp only [r, q, cplx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im _).symm
    have hreal : ∀ z : ι → ℝ, Tendsto (fun t => (A ^ t) *ᵥ z) atTop (𝓝 0) := fun z => by
      obtain ⟨x, hx, hx0⟩ := hsol z
      have := (hconv x hx).1 (h x hx)
      rwa [hx0] at this
    have hc : Tendsto (fun t => (cplxEnd A ^ t) w) atTop (𝓝 0) := by
      have h1 := tendsto_cplx_iff.2 (hreal r)
      have h2 := (tendsto_cplx_iff.2 (hreal q)).const_smul Complex.I
      rw [smul_zero] at h2
      have := h1.add h2
      rw [add_zero] at this
      refine this.congr fun t => ?_
      rw [hwrq, map_add, map_smul, cplxEnd_pow_cplx, cplxEnd_pow_cplx]
    exact not_tendsto_of_eigen hge hfw hw.2 hc
  · intro h x hx
    rw [hconv x hx]
    have htop := stable_eq_top (cplxEnd A) fun μ hμ => h μ ((hasEigenvalue_cplxEnd_iff A μ).1 hμ)
    have := (tendsto_iff_mem_stable (cplxEnd A) (cplx (x 0 - xbar))).2
      (by rw [htop]; exact Submodule.mem_top)
    simp only [cplxEnd_pow_cplx] at this
    exact tendsto_cplx_iff.1 this

variable {n : ℕ}

/-! ### Triangular systems and Theorem 6.4 -/

/-- One step of an upper triangular system, coordinate by coordinate. -/
theorem triangular_step (Λ : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (Λ *ᵥ v) i = Λ i i * v i + ∑ j ∈ Finset.univ.erase i, Λ i j * v j := by
  simp only [Matrix.mulVec, dotProduct]
  exact (Finset.add_sum_erase _ (fun j => Λ i j * v j) (Finset.mem_univ i)).symm

/-- Coordinates beyond `k` stay zero. -/
theorem triangular_invariant (Λ : Matrix (Fin n) (Fin n) ℂ) (hΛ : ∀ i j, j < i → Λ i j = 0)
    {k : ℕ} {w : Fin n → ℂ} (hw : ∀ j : Fin n, k ≤ j.val → w j = 0) (t : ℕ) :
    ∀ j : Fin n, k ≤ j.val → ((Λ ^ t) *ᵥ w) j = 0 := by
  induction t with
  | zero => intro j hj; simpa using hw j hj
  | succ t ih =>
    intro j hj
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l j with hlj | hjl
    · rw [hΛ j l hlj, zero_mul]
    · have := ih l (hj.trans (Fin.le_def.1 hjl))
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this, mul_zero]

/-- **The triangular case.** If `Λ` is upper triangular, with `|Λᵢᵢ| < 1` for `i < m` and
`|Λᵢᵢ| ≥ 1` otherwise, then `Λᵗw → 0` iff `wᵢ = 0` for every `i ≥ m`. -/
theorem triangular_tendsto_iff (Λ : Matrix (Fin n) (Fin n) ℂ) (hΛ : ∀ i j, j < i → Λ i j = 0)
    (m : ℕ) (hs : ∀ i : Fin n, i.val < m → ‖Λ i i‖ < 1)
    (hu : ∀ i : Fin n, m ≤ i.val → 1 ≤ ‖Λ i i‖) (w : Fin n → ℂ) :
    Tendsto (fun t => (Λ ^ t) *ᵥ w) atTop (𝓝 0) ↔ ∀ i : Fin n, m ≤ i.val → w i = 0 := by
  set W : ℕ → Fin n → ℂ := fun t => (Λ ^ t) *ᵥ w
  have hrec : ∀ t i, W (t + 1) i = Λ i i * W t i + ∑ j ∈ Finset.univ.erase i, Λ i j * W t j :=
    fun t i => by
      simp only [W]
      rw [pow_succ', ← Matrix.mulVec_mulVec, triangular_step]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hjm, hj⟩ := hcon
    set S := Finset.univ.filter fun l : Fin n => w l ≠ 0
    have hS : S.Nonempty := ⟨j, by simp [S, hj]⟩
    set J := S.max' hS
    have hJS : J ∈ S := S.max'_mem hS
    have hwJ : w J ≠ 0 := (Finset.mem_filter.1 hJS).2
    have hjJ : j ≤ J := S.le_max' j (by simp [S, hj])
    have hbeyond : ∀ l : Fin n, J.val + 1 ≤ l.val → w l = 0 := fun l hl => by
      by_contra hl0
      have := S.le_max' l (by simp [S, hl0])
      have : l.val ≤ J.val := this
      omega
    have hinv := triangular_invariant Λ hΛ hbeyond
    -- the `J`-th coordinate is `Λ_JJᵗ w_J`
    have hJ : ∀ t, W t J = Λ J J ^ t * w J := by
      intro t
      induction t with
      | zero => simp [W]
      | succ t ih =>
        rw [hrec, ih, Finset.sum_eq_zero, add_zero, pow_succ]
        · ring
        · intro l hl
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlJ | hJl
          · rw [hΛ J l hlJ, zero_mul]
          · rw [show W t l = 0 from hinv t l hJl, mul_zero]
    have hcoord : Tendsto (fun t => W t J) atTop (𝓝 0) := by
      have := ((continuous_apply J).tendsto 0).comp h
      simpa [Function.comp_def] using this
    have hpos : 0 < ‖w J‖ := norm_pos_iff.2 hwJ
    have hge : ∀ t, ‖w J‖ ≤ ‖W t J‖ := fun t => by
      rw [hJ, norm_mul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_pow₀ (hu J (hjm.trans (Fin.le_def.1 hjJ))))
    have := ge_of_tendsto' (tendsto_zero_iff_norm_tendsto_zero.1 hcoord) hge
    linarith
  · intro hw
    have hinv := triangular_invariant Λ hΛ hw
    -- downward induction on the coordinates
    have key : ∀ d : ℕ, ∀ i : Fin n, n ≤ i.val + d → Tendsto (fun t => W t i) atTop (𝓝 0) := by
      intro d
      induction d with
      | zero => intro i hi; exact absurd i.2 (by omega)
      | succ d ih =>
        intro i hi
        rcases le_or_gt m i.val with hmi | him
        · simp only [show ∀ t, W t i = 0 from fun t => hinv t i hmi]
          exact tendsto_const_nhds
        · refine tendsto_zero_of_rec (hs i him) ?_ fun t => by rw [hrec, smul_eq_mul]
          rw [show (0 : ℂ) = ∑ j ∈ Finset.univ.erase i, 0 by simp]
          refine tendsto_finsetSum _ fun j hj => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hij
          · simp only [hΛ i j hji, zero_mul]
            exact tendsto_const_nhds
          · have := (ih j (by have : i.val < j.val := hij; omega)).const_mul (Λ i j)
            rwa [mul_zero] at this
    exact tendsto_pi_nhds.2 fun i => key n i (by omega)

theorem map_pow_mulVec_cplx (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) (z : Fin n → ℝ) :
    ((A.map Complex.ofRealHom) ^ t) *ᵥ cplx z = cplx ((A ^ t) *ᵥ z) := by
  have := cplxEnd_pow_cplx A t z
  rw [cplxEnd, ← Matrix.toLin'_pow, Matrix.toLin'_apply] at this
  exact this

theorem conj_pow (B Λ : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) (t : ℕ) :
    (B⁻¹ * Λ * B) ^ t = B⁻¹ * Λ ^ t * B := by
  induction t with
  | zero => simp [Matrix.nonsing_inv_mul _ hB]
  | succ t ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

/-- **(9).** `x_t = x̄ + B⁻¹ΛᵗB(x₀ − x̄)`. -/
theorem solution_eq (A : Matrix (Fin n) (Fin n) ℝ) (a₀ : Fin n → ℝ) (hI : IsUnit (1 - A).det)
    (B Λ : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det)
    (hA : A.map Complex.ofRealHom = B⁻¹ * Λ * B) {x : ℕ → Fin n → ℝ}
    (hx : ∀ t, x (t + 1) = a₀ + A *ᵥ x t) (t : ℕ) :
    cplx (x t) = cplx ((1 - A)⁻¹ *ᵥ a₀) +
      B⁻¹ *ᵥ ((Λ ^ t) *ᵥ (B *ᵥ cplx (x 0 - (1 - A)⁻¹ *ᵥ a₀))) := by
  have h := congrArg cplx (deviation_eq A a₀ hI hx t)
  rw [← map_pow_mulVec_cplx, hA, conj_pow B Λ hB, cplx_sub] at h
  simp only [Matrix.mulVec_mulVec] at h ⊢
  rw [Matrix.mul_assoc] at h
  rw [← h]
  abel

/-- **Theorem 6.4.** Let `A = B⁻¹ΛB` with `Λ` upper triangular (for instance a Jordan matrix),
`|Λᵢᵢ| < 1` for `i < m` and `|Λᵢᵢ| ≥ 1` for `i ≥ m`. Then `x_t → x̄` iff `x₀ = x̄ + B⁻¹w₀` with
`w₀ᵢ = 0` for every `i ≥ m`. -/
theorem theorem_6_4 (A : Matrix (Fin n) (Fin n) ℝ) (a₀ : Fin n → ℝ) (hI : IsUnit (1 - A).det)
    (B Λ : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det)
    (hA : A.map Complex.ofRealHom = B⁻¹ * Λ * B) (hΛ : ∀ i j, j < i → Λ i j = 0) (m : ℕ)
    (hs : ∀ i : Fin n, i.val < m → ‖Λ i i‖ < 1) (hu : ∀ i : Fin n, m ≤ i.val → 1 ≤ ‖Λ i i‖)
    {x : ℕ → Fin n → ℝ} (hx : ∀ t, x (t + 1) = a₀ + A *ᵥ x t) :
    Tendsto x atTop (𝓝 ((1 - A)⁻¹ *ᵥ a₀)) ↔
      ∃ w₀ : Fin n → ℂ, (∀ i : Fin n, m ≤ i.val → w₀ i = 0) ∧
        cplx (x 0) = cplx ((1 - A)⁻¹ *ᵥ a₀) + B⁻¹ *ᵥ w₀ := by
  set xbar := (1 - A)⁻¹ *ᵥ a₀
  set z₀ := cplx (x 0 - xbar)
  have hB' : B *ᵥ (B⁻¹ *ᵥ z₀) = z₀ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
  have hcont : ∀ M : Matrix (Fin n) (Fin n) ℂ, Continuous fun v : Fin n → ℂ => M *ᵥ v :=
    fun M => continuous_const.matrix_mulVec continuous_id
  have step1 : Tendsto x atTop (𝓝 xbar) ↔
      Tendsto (fun t => (Λ ^ t) *ᵥ (B *ᵥ z₀)) atTop (𝓝 0) := by
    rw [← tendsto_sub_nhds_zero_iff, show (fun t => x t - xbar) =
      fun t => (A ^ t) *ᵥ (x 0 - xbar) from funext (deviation_eq A a₀ hI hx),
      ← tendsto_cplx_iff]
    simp only [← map_pow_mulVec_cplx, hA, conj_pow B Λ hB]
    constructor
    · intro h
      have := ((hcont B).tendsto 0).comp h
      simpa [Function.comp_def, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hB] using this
    · intro h
      have := ((hcont B⁻¹).tendsto 0).comp h
      simpa [Function.comp_def, Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
  rw [step1, triangular_tendsto_iff Λ hΛ m hs hu]
  constructor
  · intro h
    refine ⟨B *ᵥ z₀, h, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
    simp only [z₀, cplx_sub]
    abel
  · rintro ⟨w₀, hw₀, hx0⟩
    have : z₀ = B⁻¹ *ᵥ w₀ := by
      simp only [z₀, cplx_sub, hx0]
      abel
    rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    exact hw₀

end StokeyLucasPrescott.DeterministicDynamics
