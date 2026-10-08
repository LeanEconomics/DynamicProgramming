/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.AsymptoticEndogenous

/-!
# When is endogenous value iteration strictly faster?

Bray (2019b, *Management Science*), Proposition 5, Lemma 4 and Corollaries 2–4.

Write `F_x` for the exogenous transition matrix (`FxMat`), `F_y(σ, x)` for the endogenous
transition matrix within exogenous state `x` (`FyMat`) and `Ω` for the demeaning matrix on `Y`
(`omegaMat`).

* `spectrum_exo_subset` (**Bray, Lemma 4**): every eigenvalue of `Δ_X F_x` is an eigenvalue of
  `ΔP_σ`, so `σ(F_x) ≤ σ(P_σ)` (`subradius_FxMat_le`): the chain as a whole mixes no faster than
  its exogenous part.
* `endoRadius_le_of_vecNorm` (**Bray, Prop 5**): for any vector norm `N` on `ℂ^Y`, if `c` bounds
  the `N`-operator norm of `ΩF_y(σ, x)` for every `x`, then `ρ(ΛP_σ) ≤ c`. Hence if
  `σ(F_x) > c`, endogenous iteration is strictly faster (`endoRadius_lt_subradius_of_vecNorm`,
  `endo_strictly_faster`, `endo_eval_strictly_faster`).
* **Bray, Cor 2**: `c` may be the largest absolute row sum of `ΩF_y(σ, x)`
  (`endoRadius_le_rowSum`, the `ℓ∞` norm) or the Hajnal (Dobrushin) coefficient of `F_y(σ, x)`
  (`endoRadius_le_hajnal`).
* `endoRadius_lt_of_nonergodic_scrambling` (**Bray, Cor 3**): if `F_x` is not ergodic (it has a
  non-constant fixed vector or an eigenvalue `μ ≠ 1` with `|μ| = 1`) and every `F_y(σ, x)` is
  scrambling, endogenous iteration is strictly faster.
* `endoRadius_le_subradius_Fy` (**Bray, Cor 4**): if `F_y(σ, x) = G` for every `x`, then
  `ρ(ΛP_σ) ≤ σ(G)`, so endogenous iteration is strictly faster when `σ(F_x) > σ(G)`
  (`endoRadius_lt_of_Fy_const`).
-/

open Filter Topology Matrix Finset

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace DPExtensions.RelativeValueIteration

/-! ### Spectral radii from eigenvalue bounds -/

/-- If every eigenvalue of `B` has modulus at most `c`, then `ρ(B) ≤ c`. -/
theorem specRad_le_of_eigen {S : Type*} [Fintype S] (B : Matrix S S ℝ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ (μ : ℂ) (e : S → ℂ), e ≠ 0 → complexify B *ᵥ e = μ • e → ‖μ‖ ≤ c) :
    specRad B ≤ c := by
  classical
  have hle : spectralRadius ℂ (complexify B) ≤ ENNReal.ofReal c := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun μ hμ => ?_
    obtain ⟨e, he, hμe⟩ := (mem_spectrum_iff_eigenpair _ μ).1 hμ
    rw [ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top hc]
    simpa using h μ e he hμe
  exact ENNReal.toReal_le_of_le_ofReal hc hle

/-- Every eigenvalue of `B` has modulus at most `ρ(B)`. -/
theorem norm_le_specRad {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] (B : Matrix S S ℝ)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify B)) : ‖μ‖ ≤ specRad B := by
  have h : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (complexify B) := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun μ _ => (‖μ‖₊ : ENNReal)) μ hμ
  have := ENNReal.toReal_mono (spectralRadius_complexify_ne_top B) h
  simpa [specRad] using this

/-- Spectral radii are monotone under inclusion of spectra. -/
theorem specRad_mono_of_spectrum {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] [Nonempty T] (B : Matrix S S ℝ) (C : Matrix T T ℝ)
    (h : ∀ μ, μ ∈ spectrum ℂ (complexify B) → μ ∈ spectrum ℂ (complexify C)) :
    specRad B ≤ specRad C := by
  refine ENNReal.toReal_mono (spectralRadius_complexify_ne_top C) ?_
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  exact iSup₂_le fun μ hμ => le_iSup₂ (f := fun μ _ => (‖μ‖₊ : ENNReal)) μ (h μ hμ)

/-- The rows of a power of a stochastic matrix are probability vectors. -/
theorem IsStochastic.pow {S : Type*} [Fintype S] [DecidableEq S] {Q : Matrix S S ℝ}
    (hQ : IsStochastic Q) (k : ℕ) : IsStochastic (Q ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_zero, one_apply]
      split_ifs <;> norm_num
    · simp [one_apply]
  | succ k ih =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_succ, mul_apply]
      exact sum_nonneg fun t _ => mul_nonneg (ih.1 i t) (hQ.1 t j)
    · rw [pow_succ]
      simp only [mul_apply]
      rw [sum_comm]
      simp only [← mul_sum, hQ.2, mul_one]
      exact ih.2 i

/-- A stochastic matrix that is not
ergodic — with a non-constant fixed vector, or an eigenvalue `μ ≠ 1` of modulus one — has
subradius at least one. -/
theorem one_le_subradius_of_nonergodic {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {Q : Matrix S S ℝ} (hQ : IsStochastic Q) (s₀ : S)
    (h : (∃ μ ∈ spectrum ℂ (complexify Q), μ ≠ 1 ∧ ‖μ‖ = 1) ∨
      ∃ v : S → ℂ, complexify Q *ᵥ v = v ∧ ∃ i j, v i ≠ v j) :
    1 ≤ subradius Q s₀ := by
  rcases h with ⟨μ, hμ, h1, hn⟩ | hv
  · have h0 : μ ≠ 0 := by
      rintro rfl
      simp at hn
    rw [← hn]
    exact norm_le_specRad _ ((mem_spectrum_deltaQ_iff hQ s₀ h0).2 (Or.inl ⟨hμ, h1⟩))
  · have := norm_le_specRad _ ((mem_spectrum_deltaQ_iff hQ s₀ one_ne_zero).2 (Or.inr ⟨rfl, hv⟩))
    simpa [subradius] using this

/-! ### Vector norms on `ℂ^Y` -/

/-- `N` is a norm on `ℂ^Y`. -/
def IsVecNorm {Y : Type*} (N : (Y → ℂ) → ℝ) : Prop :=
  (∀ u v, N (u + v) ≤ N u + N v) ∧ (∀ (a : ℂ) u, N (a • u) = ‖a‖ * N u) ∧
    ∀ u, N u = 0 → u = 0

namespace IsVecNorm

variable {Y : Type*} {N : (Y → ℂ) → ℝ}

theorem zero (hN : IsVecNorm N) : N 0 = 0 := by
  have := hN.2.1 0 0
  simpa using this

theorem nonneg (hN : IsVecNorm N) (u : Y → ℂ) : 0 ≤ N u := by
  have h1 := hN.1 u ((-1 : ℂ) • u)
  rw [hN.2.1, show u + (-1 : ℂ) • u = 0 by simp, hN.zero] at h1
  simp only [norm_neg, norm_one, one_mul] at h1
  linarith

theorem pos (hN : IsVecNorm N) {u : Y → ℂ} (hu : u ≠ 0) : 0 < N u :=
  lt_of_le_of_ne (hN.nonneg u) fun h => hu (hN.2.2 u h.symm)

theorem sum_le (hN : IsVecNorm N) {ι : Type*} (s : Finset ι) (g : ι → Y → ℂ) :
    N (∑ i ∈ s, g i) ≤ ∑ i ∈ s, N (g i) :=
  Finset.le_sum_of_subadditive N hN.zero.le hN.1 s g

theorem smul_real (hN : IsVecNorm N) {r : ℝ} (hr : 0 ≤ r) (u : Y → ℂ) :
    N ((r : ℂ) • u) = r * N u := by
  rw [hN.2.1, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The sup norm. -/
theorem sup_norm [Fintype Y] : IsVecNorm fun u : Y → ℂ => ‖u‖ :=
  ⟨norm_add_le, fun a u => norm_smul a u, fun _ h => norm_eq_zero.1 h⟩

end IsVecNorm

namespace ExoMDP

variable {X Y A : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The demeaning matrix `Ω = I − ιι′/Y` on the endogenous state. -/
noncomputable def omegaMat : Matrix Y Y ℝ := fun y y' =>
  (if y = y' then 1 else 0) - (Fintype.card Y : ℝ)⁻¹

theorem comega_mulVec (u : Y → ℂ) :
    complexify (omegaMat : Matrix Y Y ℝ) *ᵥ u = fun y => u y - (∑ y', u y') / Fintype.card Y := by
  funext y
  simp [complexify, omegaMat, mulVec, dotProduct, sub_mul, sum_sub_distrib, ite_mul,
    apply_ite Complex.ofReal, ← mul_sum, div_eq_inv_mul]

theorem clamMat_mulVec (w : X × Y → ℂ) :
    complexify (lamMat : Matrix (X × Y) (X × Y) ℝ) *ᵥ w =
      fun s => w s - (∑ y, w (s.1, y)) / Fintype.card Y := by
  funext s
  simp only [mulVec, dotProduct, complexify_apply, lamMat, Complex.ofReal_sub, sub_mul,
    sum_sub_distrib, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  congr 1
  rw [Fintype.sum_prod_type, sum_eq_single s.1
    (fun x _ hx => sum_eq_zero fun y _ => by simp [Ne.symm hx]) (by simp)]
  simp only [ite_true, ← mul_sum]
  push_cast
  rw [div_eq_inv_mul]

variable (E : ExoMDP X Y A)

/-- The exogenous transition matrix `F_x`. -/
def FxMat : Matrix X X ℝ := E.Fx

omit [DecidableEq X] [DecidableEq Y] in
theorem FxMat_isStochastic : IsStochastic E.FxMat := ⟨E.Fx_nonneg, E.Fx_sum⟩

/-- The endogenous transition matrix `F_y(σ, x)` within exogenous state `x`. -/
def FyMat (σ : X × Y → A) (x : X) : Matrix Y Y ℝ := fun y y' => E.Fy x y (σ (x, y)) y'

omit [DecidableEq X] [DecidableEq Y] in
theorem FyMat_isStochastic (σ : X × Y → A) (x : X) : IsStochastic (E.FyMat σ x) :=
  ⟨fun _ _ => E.Fy_nonneg _ _ _ _, fun _ => E.Fy_sum _ _ _⟩

omit [DecidableEq X] [DecidableEq Y] in
theorem Pmat_apply (σ : X × Y → A) (s t : X × Y) :
    E.toMDP.Pmat σ s t = E.FxMat s.1 t.1 * E.FyMat σ s.1 s.2 t.2 := rfl

omit [DecidableEq X] [DecidableEq Y] in
theorem cPmat_mulVec_lift (σ : X × Y → A) (v : X → ℂ) :
    complexify (E.toMDP.Pmat σ) *ᵥ (fun s => v s.1) =
      fun s => (complexify E.FxMat *ᵥ v) s.1 := by
  funext s
  simp only [mulVec, dotProduct, complexify_apply, Pmat_apply, Fintype.sum_prod_type]
  refine sum_congr rfl fun x' _ => ?_
  have h : ∑ y', ((E.FyMat σ s.1 s.2 y' : ℝ) : ℂ) = 1 := by
    exact_mod_cast (E.FyMat_isStochastic σ s.1).2 s.2
  push_cast
  rw [← sum_mul, ← mul_sum, h, mul_one]

/-- **Bray, Lemma 4**: every eigenvalue of `Δ_X F_x` is an eigenvalue of `ΔP_σ`. -/
theorem spectrum_exo_subset [Nonempty Y] (σ : X × Y → A) (s₀ : X × Y) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify (deltaMat s₀.1 * E.FxMat))) :
    μ ∈ spectrum ℂ (complexify (deltaMat s₀ * E.toMDP.Pmat σ)) := by
  obtain ⟨v, hv, hμv⟩ := (mem_spectrum_iff_eigenpair _ μ).1 hμ
  refine (mem_spectrum_iff_eigenpair _ μ).2 ⟨fun s => v s.1, fun h => hv ?_, ?_⟩
  · funext x
    exact congrFun h (x, Classical.arbitrary Y)
  · rw [complexify_deltaQ_mulVec, E.cPmat_mulVec_lift]
    funext s
    have := congrFun hμv s.1
    rw [complexify_deltaQ_mulVec] at this
    simpa using this

/-- **The chain mixes no faster than its exogenous part**: `σ(F_x) ≤ σ(P_σ)`. -/
theorem subradius_FxMat_le [Nonempty X] [Nonempty Y] (σ : X × Y → A) (s₀ : X × Y) :
    subradius E.FxMat s₀.1 ≤ subradius (E.toMDP.Pmat σ) s₀ :=
  specRad_mono_of_spectrum _ _ fun _ hμ => E.spectrum_exo_subset σ s₀ hμ

/-- `ΛP_σ` acts on each exogenous slice through `ΩF_y(σ, x)`. -/
theorem clamP_mulVec (σ : X × Y → A) (v : X × Y → ℂ) (s : X × Y) :
    (complexify (lamMat * E.toMDP.Pmat σ) *ᵥ v) s =
      ∑ x', (E.FxMat s.1 x' : ℂ) *
        (complexify (omegaMat * E.FyMat σ s.1) *ᵥ fun y => v (x', y)) s.2 := by
  have hP : ∀ x y, (complexify (E.toMDP.Pmat σ) *ᵥ v) (x, y) =
      ∑ x', (E.FxMat x x' : ℂ) * (complexify (E.FyMat σ x) *ᵥ fun y' => v (x', y')) y := by
    intro x y
    simp only [mulVec, dotProduct, complexify_apply, Pmat_apply, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun x' _ => sum_congr rfl fun y' _ => ?_
    push_cast
    ring
  obtain ⟨x, y⟩ := s
  rw [complexify_mul, ← mulVec_mulVec, clamMat_mulVec, complexify_mul]
  simp only [← mulVec_mulVec, comega_mulVec, hP, mul_sub, sum_sub_distrib]
  congr 1
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun x' _ => ?_
  rw [← mul_sum, mul_div_assoc]

/-- **Bray, Prop 5**: for any vector norm `N` on `ℂ^Y`, if `c` bounds the `N`-operator norm of
`ΩF_y(σ, x)` for every exogenous state `x`, then `ρ(ΛP_σ) ≤ c`. -/
theorem endoRadius_le_of_vecNorm [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    {N : (Y → ℂ) → ℝ} (hN : IsVecNorm N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x u, N (complexify (omegaMat * E.FyMat σ x) *ᵥ u) ≤ c * N u) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  unfold endoRadius
  refine specRad_le_of_eigen _ hc0 fun μ e he heig => ?_
  obtain ⟨x₀, -, hmax⟩ := exists_max_image univ (fun x => N fun y => e (x, y)) univ_nonempty
  have hpos : 0 < N fun y => e (x₀, y) := by
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      exact he (funext fun s => by
        by_contra hs
        exact h ⟨s, hs⟩)
    have h1 : 0 < N fun y => e (s.1, y) := hN.pos fun h => hs (by simpa using congrFun h s.2)
    exact h1.trans_le (hmax s.1 (mem_univ _))
  have hrow : (μ • fun y => e (x₀, y)) = ∑ x', (E.FxMat x₀ x' : ℂ) •
      (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y)) := by
    funext y
    have := congrFun heig (x₀, y)
    rw [E.clamP_mulVec] at this
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this ⊢
    exact this.symm
  have hst := E.FxMat_isStochastic
  have key : ‖μ‖ * N (fun y => e (x₀, y)) ≤ c * N (fun y => e (x₀, y)) := by
    rw [← hN.2.1, hrow]
    calc N (∑ x', (E.FxMat x₀ x' : ℂ) •
          (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y)))
        ≤ ∑ x', N ((E.FxMat x₀ x' : ℂ) •
          (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y))) := hN.sum_le _ _
      _ = ∑ x', E.FxMat x₀ x' *
          N (complexify (omegaMat * E.FyMat σ x₀) *ᵥ fun y => e (x', y)) :=
          sum_congr rfl fun x' _ => hN.smul_real (hst.1 x₀ x') _
      _ ≤ ∑ x', E.FxMat x₀ x' * (c * N fun y => e (x₀, y)) := sum_le_sum fun x' _ =>
          mul_le_mul_of_nonneg_left ((hc x₀ _).trans
            (mul_le_mul_of_nonneg_left (hmax x' (mem_univ _)) hc0)) (hst.1 x₀ x')
      _ = c * N (fun y => e (x₀, y)) := by rw [← sum_mul, hst.2 x₀, one_mul]
  exact le_of_mul_le_mul_right key hpos

/-- **Bray, Prop 5 (strict form)**: if `σ(F_x)` exceeds a bound `c` on the `N`-operator norms of
`ΩF_y(σ, x)`, then `ρ(ΛP_σ) < σ(P_σ)`. -/
theorem endoRadius_lt_subradius_of_vecNorm [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    (s₀ : X × Y) {N : (Y → ℂ) → ℝ} (hN : IsVecNorm N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x u, N (complexify (omegaMat * E.FyMat σ x) *ᵥ u) ≤ c * N u)
    (hlt : c < subradius E.FxMat s₀.1) :
    endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀ :=
  (E.endoRadius_le_of_vecNorm σ hN hc0 hc).trans_lt (hlt.trans_le (E.subradius_FxMat_le σ s₀))

/-- **Endogenous value iteration is strictly faster** (Bray, Prop 5.1): if `ρ(ΛP_{σ*}) <
σ(P_{σ*})`, endogenous values converge at rate `βγ` for some `γ` strictly below `σ(P_{σ*})`. -/
theorem endo_strictly_faster [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {σs : X × Y → A}
    (hstrict : ∀ s, σs s ∈ E.Γ s ∧ ∀ a ∈ E.Γ s, a ≠ σs s →
      E.toMDP.Q (E.toMDP.vstar hβ) s a < E.toMDP.Q (E.toMDP.vstar hβ) s (σs s))
    (s₀ : X × Y) (hlt : endoRadius (E.toMDP.Pmat σs) < subradius (E.toMDP.Pmat σs) s₀)
    (v : X × Y → ℝ) :
    ∃ γ < subradius (E.toMDP.Pmat σs) s₀, ∃ C N, ∀ k,
      spy (fun s => E.toMDP.T^[N + k] v s - E.toMDP.vstar hβ s) ≤ C * (E.β * γ) ^ k := by
  obtain ⟨γ, h1, h2⟩ := exists_between hlt
  exact ⟨γ, h2, E.endo_asymptotic_rate hβ hstrict h1 v⟩

/-- **Endogenous policy evaluation is strictly faster** (Bray, Prop 5.2). -/
theorem endo_eval_strictly_faster [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (σ : X × Y → A)
    (s₀ : X × Y) (hlt : endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀) :
    ∃ γ < subradius (E.toMDP.Pmat σ) s₀, ∃ C, 0 ≤ C ∧ ∀ (n : ℕ) (v : X × Y → ℝ),
      spy (fun s => (E.toMDP.Tσ σ)^[n] v s - E.toMDP.vσ hβ σ s) ≤
        C * (E.β * γ) ^ n * spy (fun s => v s - E.toMDP.vσ hβ σ s) := by
  obtain ⟨γ, h1, h2⟩ := exists_between hlt
  exact ⟨γ, h2, E.endo_policy_eval_le hβ σ h1⟩

/-- **Bray, Cor 2(c)**: the largest absolute row sum of `ΩF_y(σ, x)` bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_rowSum [Nonempty X] [Nonempty Y] (σ : X × Y → A) {c : ℝ}
    (hc : ∀ x y, ∑ y', |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'| ≤ c) :
    endoRadius (E.toMDP.Pmat σ) ≤ c := by
  have hc0 : 0 ≤ c := (sum_nonneg fun _ _ => abs_nonneg _).trans
    (hc (Classical.arbitrary X) (Classical.arbitrary Y))
  refine E.endoRadius_le_of_vecNorm σ IsVecNorm.sup_norm hc0 fun x u => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc0 (norm_nonneg u))).2 fun y => ?_
  simp only [mulVec, dotProduct, complexify_apply]
  calc ‖∑ y', ((omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y' : ℂ) * u y'‖
      ≤ ∑ y', |(omegaMat * E.FyMat σ x : Matrix Y Y ℝ) y y'| * ‖u‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun y' _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u y') (abs_nonneg _))
    _ ≤ c * ‖u‖ := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right (hc x y) (norm_nonneg u)

omit [DecidableEq X] [DecidableEq Y] in
/-- One step of `P_σ` contracts the within-`x` span by the Hajnal coefficient of `F_y(σ, ·)`. -/
theorem spy_Pmat_mulVec_le [Nonempty X] [Nonempty Y] (σ : X × Y → A) {α : ℝ}
    (hα : ∀ x y y', 1 - ∑ y'', min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤ α)
    (d : X × Y → ℝ) : spy (E.toMDP.Pmat σ *ᵥ d) ≤ α * spy d := by
  have hα0 : 0 ≤ α := by
    have h := hα (Classical.arbitrary X) (Classical.arbitrary Y) (Classical.arbitrary Y)
    simp only [min_self, (E.FyMat_isStochastic σ _).2, sub_self] at h
    exact h
  have hst := E.FxMat_isStochastic
  refine sup'_le _ _ fun x _ => sp_le fun y y' => ?_
  have hP : ∀ y, (E.toMDP.Pmat σ *ᵥ d) (x, y) =
      ∑ x', E.FxMat x x' * ∑ y'', E.FyMat σ x y y'' * d (x', y'') := fun y => by
    simp only [mulVec, dotProduct, Pmat_apply, Fintype.sum_prod_type, mul_sum]
    exact sum_congr rfl fun x' _ => sum_congr rfl fun y'' _ => by ring
  rw [hP, hP, ← sum_sub_distrib]
  calc ∑ x', (E.FxMat x x' * ∑ y'', E.FyMat σ x y y'' * d (x', y'') -
        E.FxMat x x' * ∑ y'', E.FyMat σ x y' y'' * d (x', y''))
      ≤ ∑ x', E.FxMat x x' * (α * spy d) := sum_le_sum fun x' _ => by
        rw [← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (hst.1 x x')
        have hd := dobrushin ((E.FyMat_isStochastic σ x).2 y) ((E.FyMat_isStochastic σ x).2 y')
          fun y'' => d (x', y'')
        have hs := sp_nonneg fun y'' => d (x', y'')
        have hc := mul_le_mul_of_nonneg_right (hα x y y') hs
        have hsy := mul_le_mul_of_nonneg_left (sp_le_spy d x') hα0
        linarith
    _ = α * spy d := by rw [← sum_mul, hst.2 x, one_mul]

/-- **Bray, Cor 2(e)**: the Hajnal (Dobrushin) coefficient of `F_y(σ, ·)` bounds `ρ(ΛP_σ)`. -/
theorem endoRadius_le_hajnal [Nonempty X] [Nonempty Y] (σ : X × Y → A) {α : ℝ}
    (hα : ∀ x y y', 1 - ∑ y'', min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤ α) :
    endoRadius (E.toMDP.Pmat σ) ≤ α := by
  have hα0 : 0 ≤ α := by
    have h := hα (Classical.arbitrary X) (Classical.arbitrary Y) (Classical.arbitrary Y)
    simp only [min_self, (E.FyMat_isStochastic σ _).2, sub_self] at h
    exact h
  have hpow : ∀ (k : ℕ) (d : X × Y → ℝ), spy (E.toMDP.Pmat σ ^ k *ᵥ d) ≤ α ^ k * spy d := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
      intro d
      rw [pow_succ', ← mulVec_mulVec, pow_succ']
      calc spy (E.toMDP.Pmat σ *ᵥ (E.toMDP.Pmat σ ^ k *ᵥ d))
          ≤ α * spy (E.toMDP.Pmat σ ^ k *ᵥ d) := E.spy_Pmat_mulVec_le σ hα _
        _ ≤ α * (α ^ k * spy d) := mul_le_mul_of_nonneg_left (ih d) hα0
        _ = α * α ^ k * spy d := by ring
  unfold endoRadius
  refine specRad_le_of_norm_pow_le _ zero_lt_two hα0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(lamMat * E.toMDP.Pmat σ) ^ k *ᵥ w‖ ≤ 2 * α ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    linarith [norm_nonneg w]
  have e : (lamMat * E.toMDP.Pmat σ) ^ (k + 1) *ᵥ w = endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) := by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec,
      lamF_pow_endo (E.Pmat_preservesLift σ), mulVec_mulVec, ← pow_succ]
  rw [e]
  calc ‖endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w)‖ ≤ spy (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) :=
        norm_endo_le _
    _ ≤ α ^ (k + 1) * spy w := hpow _ _
    _ ≤ α ^ (k + 1) * (2 * ‖w‖) :=
        mul_le_mul_of_nonneg_left ((spy_le_sp w).trans (sp_le_two_norm w)) (pow_nonneg hα0 _)
    _ = 2 * α ^ (k + 1) * ‖w‖ := by ring

omit [DecidableEq X] [DecidableEq Y] in
/-- **Scrambling matrices have Hajnal coefficient below one** (Hajnal, 1958): if any two rows of
each `F_y(σ, x)` overlap, a single `α < 1` bounds every endogenous Dobrushin coefficient. -/
theorem exists_hajnal_lt_one [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    (hs : ∀ x y y', ∃ y'', 0 < min (E.FyMat σ x y y'') (E.FyMat σ x y' y'')) :
    ∃ α < 1, ∀ x y y', 1 - ∑ y'', min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤ α := by
  set f : X × Y × Y → ℝ := fun p =>
    1 - ∑ y'', min (E.FyMat σ p.1 p.2.1 y'') (E.FyMat σ p.1 p.2.2 y'')
  refine ⟨univ.sup' univ_nonempty f, ?_, fun x y y' => le_sup' f (mem_univ (x, y, y'))⟩
  rw [sup'_lt_iff]
  rintro ⟨x, y, y'⟩ -
  obtain ⟨y'', hy''⟩ := hs x y y'
  have hst := E.FyMat_isStochastic σ x
  have : min (E.FyMat σ x y y'') (E.FyMat σ x y' y'') ≤
      ∑ t, min (E.FyMat σ x y t) (E.FyMat σ x y' t) :=
    single_le_sum (f := fun t => min (E.FyMat σ x y t) (E.FyMat σ x y' t))
      (fun t _ => le_min (hst.1 _ _) (hst.1 _ _)) (mem_univ y'')
  simp only [f]
  linarith

/-- **Bray, Cor 3**: if `F_x` is not ergodic and every `F_y(σ, x)` is scrambling, then
`ρ(ΛP_σ) < σ(P_σ)`: endogenous iteration is strictly faster. -/
theorem endoRadius_lt_of_nonergodic_scrambling [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    (s₀ : X × Y)
    (hx : (∃ μ ∈ spectrum ℂ (complexify E.FxMat), μ ≠ 1 ∧ ‖μ‖ = 1) ∨
      ∃ v : X → ℂ, complexify E.FxMat *ᵥ v = v ∧ ∃ i j, v i ≠ v j)
    (hs : ∀ x y y', ∃ y'', 0 < min (E.FyMat σ x y y'') (E.FyMat σ x y' y'')) :
    endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀ := by
  obtain ⟨α, hα1, hα⟩ := E.exists_hajnal_lt_one σ hs
  calc endoRadius (E.toMDP.Pmat σ) ≤ α := E.endoRadius_le_hajnal σ hα
    _ < 1 := hα1
    _ ≤ subradius E.FxMat s₀.1 := one_le_subradius_of_nonergodic E.FxMat_isStochastic s₀.1 hx
    _ ≤ subradius (E.toMDP.Pmat σ) s₀ := E.subradius_FxMat_le σ s₀

/-- When `F_y(σ, x) = G` for every `x`, `P_σ = F_x ⊗ G`, so `P_σᵏ = F_xᵏ ⊗ Gᵏ`. -/
theorem Pmat_pow_mulVec_of_Fy_const (σ : X × Y → A) {G : Matrix Y Y ℝ}
    (hG : ∀ x, E.FyMat σ x = G) (j : ℕ) (w : X × Y → ℝ) (x : X) (y : Y) :
    (E.toMDP.Pmat σ ^ j *ᵥ w) (x, y) =
      ∑ x', (E.FxMat ^ j) x x' * (G ^ j *ᵥ fun y' => w (x', y')) y := by
  have hexp : ∀ (M : Matrix (X × Y) (X × Y) ℝ) (u : X × Y → ℝ) (s : X × Y),
      (M *ᵥ u) s = ∑ t, M s t * u t := fun _ _ _ => rfl
  have hexpY : ∀ (M : Matrix Y Y ℝ) (u : Y → ℝ) (y : Y), (M *ᵥ u) y = ∑ t, M y t * u t :=
    fun _ _ _ => rfl
  induction j generalizing x y with
  | zero => simp [one_apply]
  | succ j ih =>
    rw [pow_succ' (E.toMDP.Pmat σ), ← mulVec_mulVec, hexp, Fintype.sum_prod_type,
      pow_succ' E.FxMat, pow_succ' G]
    simp only [← mulVec_mulVec]
    simp only [Pmat_apply, hG, ih, mul_apply, hexpY G, mul_sum, sum_mul]
    calc _ = ∑ x1, ∑ x', ∑ y1, E.FxMat x x1 * G y y1 *
            ((E.FxMat ^ j) x1 x' * (G ^ j *ᵥ fun y' => w (x', y')) y1) :=
          sum_congr rfl fun x1 _ => sum_comm
      _ = ∑ x', ∑ x1, ∑ y1, E.FxMat x x1 * G y y1 *
            ((E.FxMat ^ j) x1 x' * (G ^ j *ᵥ fun y' => w (x', y')) y1) := sum_comm
      _ = ∑ x', ∑ y1, ∑ x1, E.FxMat x x1 * G y y1 *
            ((E.FxMat ^ j) x1 x' * (G ^ j *ᵥ fun y' => w (x', y')) y1) :=
          sum_congr rfl fun x' _ => sum_comm
      _ = _ := sum_congr rfl fun x' _ => sum_congr rfl fun y1 _ =>
          sum_congr rfl fun x1 _ => by ring

/-- **Bray, Cor 4**: if `F_y(σ, x) = G` for every `x`, then `ρ(ΛP_σ) ≤ σ(G)`. -/
theorem endoRadius_le_subradius_Fy [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    {G : Matrix Y Y ℝ} (hG : ∀ x, E.FyMat σ x = G) (y₀ : Y) :
    endoRadius (E.toMDP.Pmat σ) ≤ subradius G y₀ := by
  have hGs : IsStochastic G := by
    rw [← hG (Classical.arbitrary X)]
    exact E.FyMat_isStochastic σ _
  refine le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_
  obtain ⟨C, hC0, hC⟩ := sp_pow_mulVec_le hGs y₀ hγ
  have hγ0 : 0 ≤ γ := (specRad_nonneg _).trans hγ.le
  unfold endoRadius
  refine specRad_le_of_norm_pow_le _ (K := 1 + 2 * C) (by positivity) hγ0 fun k => ?_
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  change ‖(lamMat * E.toMDP.Pmat σ) ^ k *ᵥ w‖ ≤ (1 + 2 * C) * γ ^ k * ‖w‖
  rcases k with _ | k
  · simp only [pow_zero, one_mulVec, mul_one]
    nlinarith [norm_nonneg w]
  have e : (lamMat * E.toMDP.Pmat σ) ^ (k + 1) *ᵥ w = endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) := by
    rw [pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, lamMat_mulVec,
      lamF_pow_endo (E.Pmat_preservesLift σ), mulVec_mulVec, ← pow_succ]
  rw [e]
  have hst := E.FxMat_isStochastic.pow (k + 1)
  have hspy : spy (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) ≤ C * γ ^ (k + 1) * (2 * ‖w‖) := by
    refine sup'_le _ _ fun x _ => sp_le fun y y' => ?_
    rw [E.Pmat_pow_mulVec_of_Fy_const σ hG, E.Pmat_pow_mulVec_of_Fy_const σ hG,
      ← sum_sub_distrib]
    calc ∑ x', ((E.FxMat ^ (k + 1)) x x' * (G ^ (k + 1) *ᵥ fun y' => w (x', y')) y -
          (E.FxMat ^ (k + 1)) x x' * (G ^ (k + 1) *ᵥ fun y' => w (x', y')) y')
        ≤ ∑ x', (E.FxMat ^ (k + 1)) x x' * (C * γ ^ (k + 1) * (2 * ‖w‖)) :=
          sum_le_sum fun x' _ => by
            rw [← mul_sub]
            refine mul_le_mul_of_nonneg_left ?_ (hst.1 x x')
            refine (sub_le_sp _ y y').trans ((hC _ _).trans ?_)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (sp_le_two_norm _).trans ?_
            have : ‖fun y' => w (x', y')‖ ≤ ‖w‖ :=
              (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun y' => norm_le_pi_norm w (x', y')
            linarith
      _ = C * γ ^ (k + 1) * (2 * ‖w‖) := by rw [← sum_mul, hst.2 x, one_mul]
  calc ‖endo (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w)‖ ≤ spy (E.toMDP.Pmat σ ^ (k + 1) *ᵥ w) :=
        norm_endo_le _
    _ ≤ C * γ ^ (k + 1) * (2 * ‖w‖) := hspy
    _ ≤ (1 + 2 * C) * γ ^ (k + 1) * ‖w‖ := by
        nlinarith [mul_nonneg (pow_nonneg hγ0 (k + 1)) (norm_nonneg w)]

/-- **Bray, Cor 4 (strict form)**: if `F_y(σ, x) = G` for every `x` and `σ(F_x) > σ(G)`, then
`ρ(ΛP_σ) < σ(P_σ)`. -/
theorem endoRadius_lt_of_Fy_const [Nonempty X] [Nonempty Y] (σ : X × Y → A)
    {G : Matrix Y Y ℝ} (hG : ∀ x, E.FyMat σ x = G) (s₀ : X × Y)
    (hlt : subradius G s₀.2 < subradius E.FxMat s₀.1) :
    endoRadius (E.toMDP.Pmat σ) < subradius (E.toMDP.Pmat σ) s₀ :=
  (E.endoRadius_le_subradius_Fy σ hG s₀.2).trans_lt (hlt.trans_le (E.subradius_FxMat_le σ s₀))

end ExoMDP

end DPExtensions.RelativeValueIteration
