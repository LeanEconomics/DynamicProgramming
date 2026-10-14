/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.LQStability

/-!
# The real stable and unstable subspaces of a real matrix

SLP §6.3, pp. 146–148. For a real matrix `A`, the complex stable and unstable subspaces of `A`
acting on `ℂⁿ` (`LinearSystems`) are closed under complex conjugation, because conjugation maps
the generalized eigenspace of `μ` onto that of `μ̄` (`conjV_mem_maxGenEigenspace`). Hence the
real vectors split.

* `stableR A`: the real vectors with `Aᵗz → 0`; `unstableR A`: the real vectors lying in the
  complex unstable subspace. Both are `A`-invariant (`stableR_invariant`,
  `unstableR_invariant`).
* `isCompl_stableR_unstableR`: `ℝⁿ = E_s ⊕ E_u`. A real `z` splits in `ℂⁿ` as `s + u`; taking
  conjugates and using uniqueness of the splitting, `s` and `u` are real.
* `finrank_stableR`: `dim E_s` is the number of characteristic roots (with multiplicity) inside
  the unit circle. A real basis of `E_s` stays independent over `ℂ` (`linearIndependent_cplx`),
  so `dim_ℝ E_s ≤ dim_ℂ S` and `dim_ℝ E_u ≤ dim_ℂ U`, and both sides add up to `n`.
* `unstableR_ker`: `A` is injective on `E_u` (an eigenvalue `0` would be stable).
-/

open Set Filter Topology Module
open scoped Matrix ComplexConjugate

namespace StokeyLucasPrescott.DeterministicDynamics

variable {ι : Type*}

/-- Componentwise complex conjugation. -/
def conjV (w : ι → ℂ) : ι → ℂ := fun i => conj (w i)

theorem conjV_conjV (w : ι → ℂ) : conjV (conjV w) = w := by
  funext i; simp [conjV]

theorem conjV_add (w w' : ι → ℂ) : conjV (w + w') = conjV w + conjV w' := by
  funext i; simp [conjV]

theorem conjV_sub (w w' : ι → ℂ) : conjV (w - w') = conjV w - conjV w' := by
  funext i; simp [conjV]

theorem conjV_smul (c : ℂ) (w : ι → ℂ) : conjV (c • w) = conj c • conjV w := by
  funext i; simp [conjV]

theorem conjV_zero : conjV (0 : ι → ℂ) = 0 := by funext i; simp [conjV]

theorem conjV_cplx (z : ι → ℝ) : conjV (cplx z) = cplx z := by
  funext i; simp [conjV, cplx]

/-- A conjugation-fixed complex vector is real. -/
theorem eq_cplx_re {w : ι → ℂ} (hw : conjV w = w) : w = cplx fun i => (w i).re := by
  funext i
  have := congrFun hw i
  simp only [conjV] at this
  exact (Complex.conj_eq_iff_re.1 this).symm

variable [Fintype ι] [DecidableEq ι]

theorem cplxEnd_conjV (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    cplxEnd A (conjV w) = conjV (cplxEnd A w) := by
  funext i
  simp [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, conjV, map_sum]

theorem pow_sub_conjV (A : Matrix ι ι ℝ) (μ : ℂ) (k : ℕ) (w : ι → ℂ) :
    ((cplxEnd A - conj μ • (1 : Module.End ℂ (ι → ℂ))) ^ k) (conjV w) =
      conjV (((cplxEnd A - μ • (1 : Module.End ℂ (ι → ℂ))) ^ k) w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, cplxEnd_conjV,
      conjV_sub, conjV_smul]

/-- Conjugation maps the generalized eigenspace of `μ` into that of `μ̄`. -/
theorem conjV_mem_maxGenEigenspace (A : Matrix ι ι ℝ) {μ : ℂ} {w : ι → ℂ}
    (hw : w ∈ (cplxEnd A).maxGenEigenspace μ) :
    conjV w ∈ (cplxEnd A).maxGenEigenspace (conj μ) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
  exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [pow_sub_conjV, hk, conjV_zero]⟩

/-- A union of generalized eigenspaces over a conjugation-closed set of eigenvalues is closed
under conjugation. -/
theorem conjV_mem_biSup (A : Matrix ι ι ℝ) {s : Set ℂ} (hs : ∀ μ ∈ s, conj μ ∈ s) {w : ι → ℂ}
    (hw : w ∈ ⨆ μ ∈ s, (cplxEnd A).maxGenEigenspace μ) :
    conjV w ∈ ⨆ μ ∈ s, (cplxEnd A).maxGenEigenspace μ := by
  refine Submodule.iSup_induction _ (motive := fun x => conjV x ∈ _) hw (fun μ x hx => ?_)
    (by rw [conjV_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by rw [conjV_add]; exact Submodule.add_mem _ hx hy)
  refine Submodule.iSup_induction _ (motive := fun x => conjV x ∈ _) hx (fun hμ y hy => ?_)
    (by rw [conjV_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by rw [conjV_add]; exact Submodule.add_mem _ hx hy)
  exact (le_biSup (fun μ => (cplxEnd A).maxGenEigenspace μ) (hs μ hμ))
    (conjV_mem_maxGenEigenspace A hy)

theorem conjV_mem_stable (A : Matrix ι ι ℝ) {w : ι → ℂ}
    (hw : w ∈ stableSubspace (cplxEnd A)) : conjV w ∈ stableSubspace (cplxEnd A) :=
  conjV_mem_biSup A (fun μ hμ => by simpa using hμ) hw

theorem conjV_mem_unstable (A : Matrix ι ι ℝ) {w : ι → ℂ}
    (hw : w ∈ unstableSubspace (cplxEnd A)) : conjV w ∈ unstableSubspace (cplxEnd A) :=
  conjV_mem_biSup A (fun μ hμ => by simpa using hμ) hw

/-! ### The real subspaces -/

/-- `ℝⁿ → ℂⁿ` as a real-linear map. -/
def cplxL : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) where
  toFun := cplx
  map_add' := cplx_add
  map_smul' c z := by funext i; simp [cplx, Complex.real_smul]

/-- The real stable subspace `E_s = {z : Aᵗz → 0}`. -/
noncomputable def stableR (A : Matrix ι ι ℝ) : Submodule ℝ (ι → ℝ) :=
  ((stableSubspace (cplxEnd A)).restrictScalars ℝ).comap cplxL

/-- The real unstable subspace `E_u`. -/
noncomputable def unstableR (A : Matrix ι ι ℝ) : Submodule ℝ (ι → ℝ) :=
  ((unstableSubspace (cplxEnd A)).restrictScalars ℝ).comap cplxL

theorem mem_stableR {A : Matrix ι ι ℝ} {z : ι → ℝ} :
    z ∈ stableR A ↔ cplx z ∈ stableSubspace (cplxEnd A) := Iff.rfl

theorem mem_unstableR {A : Matrix ι ι ℝ} {z : ι → ℝ} :
    z ∈ unstableR A ↔ cplx z ∈ unstableSubspace (cplxEnd A) := Iff.rfl

/-- `z ∈ E_s` iff `Aᵗz → 0`. -/
theorem mem_stableR_iff (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    z ∈ stableR A ↔ Tendsto (fun t => (A ^ t) *ᵥ z) atTop (𝓝 0) := by
  rw [mem_stableR, ← tendsto_iff_mem_stable, ← tendsto_cplx_iff]
  simp only [cplxEnd_pow_cplx]

theorem cplx_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : cplx (A *ᵥ z) = cplxEnd A (cplx z) := by
  have := cplxEnd_pow_cplx A 1 z
  simpa using this.symm

theorem stableR_invariant (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ stableR A) :
    A *ᵥ z ∈ stableR A := by
  rw [mem_stableR_iff] at hz ⊢
  have := hz.comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, pow_succ, Matrix.mulVec_mulVec] using this

theorem unstableR_invariant (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A) :
    A *ᵥ z ∈ unstableR A := by
  rw [mem_unstableR, cplx_mulVec]
  exact unstable_invariant _ hz

/-- **`ℝⁿ = E_s ⊕ E_u`.** -/
theorem isCompl_stableR_unstableR (A : Matrix ι ι ℝ) : IsCompl (stableR A) (unstableR A) := by
  set f := cplxEnd A
  refine ⟨Submodule.disjoint_def.2 fun z hs hu => ?_, codisjoint_iff.2 ?_⟩
  · have h0 := (Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs hu
    funext i
    have := congrFun h0 i
    simpa [cplxL, cplx] using this
  · refine eq_top_iff.2 fun z _ => ?_
    have hz : cplx z ∈ stableSubspace f ⊔ unstableSubspace f := by
      rw [stable_sup_unstable]; exact Submodule.mem_top
    obtain ⟨s, hs, u, hu, hsu⟩ := Submodule.mem_sup.1 hz
    -- conjugating the splitting gives another splitting, so `s` and `u` are real
    have hcs := conjV_mem_stable A hs
    have hcu := conjV_mem_unstable A hu
    have hsplit : conjV s + conjV u = s + u := by rw [← conjV_add, hsu, conjV_cplx]
    have hd : s - conjV s = conjV u - u := by
      rw [sub_eq_sub_iff_add_eq_add, ← hsplit, add_comm]
    have hmem : s - conjV s ∈ stableSubspace f ⊓ unstableSubspace f :=
      ⟨Submodule.sub_mem _ hs hcs, hd ▸ Submodule.sub_mem _ hcu hu⟩
    rw [(disjoint_stable_unstable f).eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
    have hs' := eq_cplx_re hmem.symm
    have hu' : conjV u = u := by
      have := hsplit; rw [← hmem] at this; exact add_left_cancel this
    have hu'' := eq_cplx_re hu'
    refine Submodule.mem_sup.2 ⟨fun i => (s i).re, ?_, fun i => (u i).re, ?_, ?_⟩
    · rw [mem_stableR, ← hs']; exact hs
    · rw [mem_unstableR, ← hu'']; exact hu
    · funext i
      have := congrFun hsu i
      simp only [Pi.add_apply, cplx] at this
      have := congrArg Complex.re this
      simpa using this

omit [Fintype ι] [DecidableEq ι] in
/-- Real vectors independent over `ℝ` are independent over `ℂ`. -/
theorem linearIndependent_cplx {κ : Type*} [Finite κ] {v : κ → ι → ℝ}
    (hv : LinearIndependent ℝ v) : LinearIndependent ℂ fun k => cplx (v k) := by
  have : Fintype κ := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc k
  have hre : ∀ i, ∑ k, (c k).re * v k i = 0 := fun i => by
    have := congrArg Complex.re (congrFun hc i)
    simpa [cplx, Finset.sum_apply, Complex.re_sum, Complex.mul_re] using this
  have him : ∀ i, ∑ k, (c k).im * v k i = 0 := fun i => by
    have := congrArg Complex.im (congrFun hc i)
    simpa [cplx, Finset.sum_apply, Complex.im_sum, Complex.mul_im] using this
  have h1 := hv (fun k => (c k).re) (by funext i; simpa [Finset.sum_apply] using hre i) k
  have h2 := hv (fun k => (c k).im) (by funext i; simpa [Finset.sum_apply] using him i) k
  exact Complex.ext h1 h2

omit [Fintype ι] [DecidableEq ι] in
/-- `dim_ℝ` of a real subspace is at most `dim_ℂ` of a complex subspace containing its
complexification. -/
theorem finrank_le_of_cplx [Finite ι] {E : Submodule ℝ (ι → ℝ)} {S : Submodule ℂ (ι → ℂ)}
    (h : ∀ z ∈ E, cplx z ∈ S) : finrank ℝ E ≤ finrank ℂ S := by
  set b := Module.finBasis ℝ E
  have hli : LinearIndependent ℂ fun k => (⟨cplx (b k), h _ (b k).2⟩ : S) := by
    refine LinearIndependent.of_comp S.subtype ?_
    exact linearIndependent_cplx (v := fun k => ((b k : E) : ι → ℝ))
      (b.linearIndependent.map' E.subtype (Submodule.ker_subtype E))
  simpa using hli.fintype_card_le_finrank

/-- **`dim E_s` is the number of characteristic roots inside the unit circle.** -/
theorem finrank_stableR (A : Matrix ι ι ℝ) :
    finrank ℝ (stableR A) =
      ((A.charpoly.map Complex.ofRealHom).roots.filter fun μ => ‖μ‖ < 1).card := by
  set f := cplxEnd A
  have hcp : LinearMap.charpoly f = A.charpoly.map Complex.ofRealHom := by
    simp only [f, cplxEnd]
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  have h1 := finrank_le_of_cplx (E := stableR A) (S := stableSubspace f) fun z hz => hz
  have h2 := finrank_le_of_cplx (E := unstableR A) (S := unstableSubspace f) fun z hz => hz
  have hR := Submodule.finrank_add_eq_of_isCompl (isCompl_stableR_unstableR A)
  have hC : finrank ℂ (stableSubspace f) + finrank ℂ (unstableSubspace f) = Fintype.card ι := by
    rw [Submodule.finrank_add_eq_of_isCompl
      ⟨disjoint_stable_unstable f, codisjoint_iff.2 (stable_sup_unstable f)⟩]
    simp
  simp only [Module.finrank_fintype_fun_eq_card] at hR
  rw [← hcp, ← finrank_stableSubspace]
  omega

/-- `A` is injective on `E_u`: an eigenvector of `0` lies in the stable subspace. -/
theorem unstableR_ker (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A)
    (h0 : A *ᵥ z = 0) : z = 0 := by
  set f := cplxEnd A
  have hf : f (cplx z) = 0 := by rw [← cplx_mulVec, h0]; funext i; simp [cplx]
  have hs : cplx z ∈ stableSubspace f := by
    refine le_biSup (fun μ => f.maxGenEigenspace μ) (show (0 : ℂ) ∈ {μ : ℂ | ‖μ‖ < 1} by simp) ?_
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simpa using hf⟩
  exact (Submodule.disjoint_def.1 (isCompl_stableR_unstableR A).disjoint) z hs hz

end StokeyLucasPrescott.DeterministicDynamics
