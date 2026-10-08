/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.PowerAffine
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Certainty equivalent operators

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.3.1.1–§7.3.1.3
(pp. 232–236).

* A certainty equivalent operator on `V` is an order-preserving self-map fixing the
  constants. Example 7.3.1 and Exercise 7.3.1: a linear operator (a matrix) is a
  certainty equivalent on `ℝ^X` iff it is a Markov matrix.
* The entropic operator `R_θ v = θ⁻¹ log P exp(θv)` (Example 7.3.2, Exercise 7.3.2),
  the Kreps–Porteus operator `R_γ v = (Pv^γ)^{1/γ}` on `(0, ∞)^X` (Example 7.3.3,
  Exercise 7.3.3) and the quantile operator `R_τ` (Exercise 7.3.4).
* Exercises 7.3.5 and 7.3.6; the properties of §7.3.1.2: positive homogeneity,
  super- and subadditivity and constant-subadditivity; Example 7.3.4; Example 7.3.5,
  the Kreps–Porteus operator is subadditive for `γ ≥ 1` and superadditive for
  `γ ≤ 1`, by a level-set argument: with `a = (Pv^γ)^{1/γ}` and `b = (Pw^γ)^{1/γ}`,
  `(v + w)/(a + b)` is a convex combination of `v/a` and `w/b`, both on the unit
  level set of the convex or concave map `u ↦ Pu^γ`. The book cites Minkowski's
  inequality and Bullen (2003).
* Exercises 7.3.7–7.3.9: the quantile and entropic operators are
  constant-subadditive (indeed translation equivariant), and constant-subadditive
  operators are nonexpansive in the supremum norm.
* (7.17) and Example 7.3.6 (Exercise 7.3.10): the entropic operator is concave for
  `θ < 0`, from the convexity of log-sum-exp, proved by the weighted
  arithmetic–geometric mean inequality. The book cites Föllmer and Knispel (2011).
* Exercise 7.3.11 and Lemma 7.3.1: subadditive (superadditive) positively
  homogeneous operators are convex (concave), so `R_γ` is convex for `γ ≥ 1` and concave for
  `γ ≤ 1`.
* Exercises 7.3.12–7.3.13: the entropic and Kreps–Porteus operators are monotone
  increasing when `P` is.
-/

open Matrix Finset Filter Topology Function Set

namespace SargentStachurski.NonlinearValuation

variable {X : Type*} [Fintype X]

/-! ### Definition and the linear case -/

/-- A certainty equivalent operator on `V` (§7.3.1.1): an order-preserving self-map of `V` that
fixes every constant function in `V`. -/
structure IsCertEquiv (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop where
  mapsTo : MapsTo R V V
  mono : ∀ v ∈ V, ∀ w ∈ V, v ≤ w → R v ≤ R w
  const : ∀ c : ℝ, (fun _ : X => c) ∈ V → R (fun _ => c) = fun _ => c

/-- Example 7.3.1 (p. 232): conditional expectation `v ↦ Pv` under a Markov matrix is a certainty
equivalent operator on `ℝ^X`. -/
theorem IsMarkov.isCertEquiv {P : Matrix X X ℝ} (hP : IsMarkov P) :
    IsCertEquiv (fun v => P *ᵥ v) Set.univ :=
  ⟨fun _ _ => mem_univ _, fun _ _ _ _ h => hP.mulVec_le_mulVec h, fun c _ => hP.mulVec_const c⟩

/-- Exercise 7.3.1 (p. 233): a linear operator `v ↦ Mv` is a certainty equivalent operator on `ℝ^X`
iff `M` is a Markov matrix. -/
theorem isCertEquiv_mulVec_iff (M : Matrix X X ℝ) :
    IsCertEquiv (fun v => M *ᵥ v) Set.univ ↔ IsMarkov M := by
  classical
  refine ⟨fun h => ⟨fun x x' => ?_, fun x => ?_⟩, fun h => h.isCertEquiv⟩
  · have h1 := h.mono 0 (mem_univ _) (Pi.single x' 1) (mem_univ _)
      (fun y => by rw [Pi.single_apply]; split_ifs <;> norm_num) x
    simpa [mulVec, dotProduct, Pi.single_apply] using h1
  · have h1 := congrFun (h.const 1 (mem_univ _)) x
    simpa [mulVec, dotProduct] using h1

/-- A Markov matrix maps strictly positive functions to strictly positive functions. -/
theorem IsMarkov.mulVec_pos {P : Matrix X X ℝ} (hP : IsMarkov P) {f : X → ℝ}
    (hf : ∀ x, 0 < f x) (x : X) : 0 < (P *ᵥ f) x := by
  obtain ⟨x', hx'⟩ : ∃ x', 0 < P x x' := by
    by_contra hcon
    have : ∑ x', P x x' ≤ 0 := sum_nonpos fun x' _ => not_lt.1 fun h => hcon ⟨x', h⟩
    linarith [hP.rowsum x]
  calc 0 < P x x' * f x' := mul_pos hx' (hf x')
    _ ≤ ∑ y, P x y * f y := single_le_sum (fun y _ => mul_nonneg (hP.nonneg x y) (hf y).le)
        (mem_univ x')

/-! ### Exercises 7.3.5 and 7.3.6 -/

omit [Fintype X] in
/-- Exercise 7.3.5 (p. 233): a certainty equivalent on `V ⊆ ℝ^X₊` containing the nonnegative
constants maps `0` to `0` and nonnegative functions to nonnegative functions. -/
theorem IsCertEquiv.zero_and_nonneg {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    (hR : IsCertEquiv R V) (h0 : (fun _ : X => (0 : ℝ)) ∈ V) :
    R 0 = 0 ∧ ∀ v ∈ V, 0 ≤ v → 0 ≤ R v := by
  have hR0 : R 0 = 0 := hR.const 0 h0
  exact ⟨hR0, fun v hv hv0 => by simpa [hR0] using hR.mono 0 h0 v hv hv0⟩

omit [Fintype X] in
/-- Exercise 7.3.6 (p. 234): convex combinations of certainty equivalent operators on `ℝ^X` are
certainty equivalent operators. -/
theorem IsCertEquiv.convex_comb {Ra Rb : (X → ℝ) → (X → ℝ)} (ha : IsCertEquiv Ra Set.univ)
    (hb : IsCertEquiv Rb Set.univ) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    IsCertEquiv (fun v => l • Ra v + (1 - l) • Rb v) Set.univ := by
  refine ⟨fun _ _ => mem_univ _, fun v _ w _ hvw x => ?_, fun c _ => ?_⟩
  · have h1 := ha.mono v (mem_univ _) w (mem_univ _) hvw x
    have h2 := hb.mono v (mem_univ _) w (mem_univ _) hvw x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · rw [ha.const c (mem_univ _), hb.const c (mem_univ _)]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-! ### Properties (§7.3.1.2) -/

/-- Positive homogeneity on `V`: `R(λv) = λRv` for `λ ≥ 0` with `λv ∈ V`. -/
def PosHomogeneous (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ c : ℝ, 0 ≤ c → c • v ∈ V → R (c • v) = c • R v

/-- Superadditivity on `V`: `R(v + w) ≥ Rv + Rw`. -/
def Superadditive (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, v + w ∈ V → R v + R w ≤ R (v + w)

/-- Subadditivity on `V`: `R(v + w) ≤ Rv + Rw`. -/
def Subadditive (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, v + w ∈ V → R (v + w) ≤ R v + R w

/-- Constant-subadditivity on `V`: `R(v + λ𝟙) ≤ Rv + λ𝟙` for `λ ≥ 0`. -/
def ConstSubadditive (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ c : ℝ, 0 ≤ c → v + (fun _ => c) ∈ V → R (v + fun _ => c) ≤ R v + fun _ => c

/-- Example 7.3.4 (p. 234): `R = P` is positively homogeneous, superadditive and subadditive. -/
theorem mulVec_properties (P : Matrix X X ℝ) :
    PosHomogeneous (fun v => P *ᵥ v) Set.univ ∧ Superadditive (fun v => P *ᵥ v) Set.univ ∧
      Subadditive (fun v => P *ᵥ v) Set.univ :=
  ⟨fun v _ c _ _ => mulVec_smul P c v, fun v _ w _ _ => (mulVec_add P v w).ge,
    fun v _ w _ _ => (mulVec_add P v w).le⟩

/-- Exercise 7.3.9 (p. 234): a constant-subadditive certainty equivalent on `ℝ^X` is nonexpansive in
the supremum norm. -/
theorem nonexpansive_of_constSubadditive {R : (X → ℝ) → (X → ℝ)}
    (hR : IsCertEquiv R Set.univ) (hc : ConstSubadditive R Set.univ) (v w : X → ℝ) :
    ‖R v - R w‖ ≤ ‖v - w‖ := by
  have key : ∀ v w : X → ℝ, ∀ x, R v x - R w x ≤ ‖v - w‖ := by
    intro v w x
    have hle : v ≤ w + fun _ => ‖v - w‖ := fun y => by
      have := norm_le_pi_norm (v - w) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (v y - w y)]
    have h1 := hR.mono v (mem_univ _) _ (mem_univ _) hle x
    have h2 := hc w (mem_univ _) ‖v - w‖ (norm_nonneg _) (mem_univ _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨key v w x, by rw [norm_sub_rev]; exact key w v x⟩

omit [Fintype X] in
/-- Exercise 7.3.11 (i) (p. 235): on a convex cone, a subadditive positively homogeneous operator is
convex. -/
theorem convexOn_of_subadditive {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)} (hV : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ c : ℝ, 0 < c → c • v ∈ V) (hh : PosHomogeneous R V)
    (hs : Subadditive R V) : ConvexOn ℝ V R := by
  refine ⟨hV, fun u hu w hw a b ha hb hab => ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h1 := hs (a • u) (hcone u hu a ha') (b • w) (hcone w hw b hb') (hV hu hw ha hb hab)
      rwa [hh u hu a ha (hcone u hu a ha'), hh w hw b hb (hcone w hw b hb')] at h1
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

omit [Fintype X] in
/-- Exercise 7.3.11 (ii) (p. 235): on a convex cone, a superadditive positively homogeneous operator
is concave. -/
theorem concaveOn_of_superadditive {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)} (hV : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ c : ℝ, 0 < c → c • v ∈ V) (hh : PosHomogeneous R V)
    (hs : Superadditive R V) : ConcaveOn ℝ V R := by
  refine ⟨hV, fun u hu w hw a b ha hb hab => ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h1 := hs (a • u) (hcone u hu a ha') (b • w) (hcone w hw b hb') (hV hu hw ha hb hab)
      rwa [hh u hu a ha (hcone u hu a ha'), hh w hw b hb (hcone w hw b hb')] at h1
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-! ### The entropic certainty equivalent (Example 7.3.2) -/

/-- The entropic certainty equivalent `(R_θ v)(x) = θ⁻¹ log ∑ exp(θv(x'))P(x, x')`
(Example 7.3.2). -/
noncomputable def entR (θ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * v x')) x)

/-- Exercise 7.3.8, in the stronger form of translation equivariance: `R_θ(v + c) = R_θ v + c`. -/
theorem entR_add_const {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) (v : X → ℝ)
    (c : ℝ) : entR θ P (v + fun _ => c) = entR θ P v + fun _ => c := by
  funext x
  have hpos := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) x
  have h1 : (P *ᵥ fun x' => Real.exp (θ * (v x' + c))) =
      Real.exp (θ * c) • (P *ᵥ fun x' => Real.exp (θ * v x')) := by
    rw [← mulVec_smul]
    congr 1
    funext x'
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Real.exp_add]
    ring
  change θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * (v x' + c))) x) =
    θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * v x')) x) + c
  rw [h1, Pi.smul_apply, smul_eq_mul, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  field_simp
  ring

/-- Exercise 7.3.2 (p. 233): `R_θ` is a certainty equivalent operator on `ℝ^X` for `θ ≠ 0`. -/
theorem isCertEquiv_entR {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    IsCertEquiv (entR θ P) Set.univ := by
  refine ⟨fun _ _ => mem_univ _, fun v _ w _ hvw x => ?_, fun c _ => ?_⟩
  · have hv := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) x
    have hw := hP.mulVec_pos (f := fun x' => Real.exp (θ * w x')) (fun _ => Real.exp_pos _) x
    unfold entR
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · have h1 : (P *ᵥ fun x' => Real.exp (θ * w x')) x ≤ (P *ᵥ fun x' => Real.exp (θ * v x')) x :=
        hP.mulVec_le_mulVec (fun y => Real.exp_le_exp.2 (by nlinarith [hvw y])) x
      exact mul_le_mul_of_nonpos_left (Real.log_le_log hw h1) (inv_lt_zero.2 hneg).le
    · have h1 : (P *ᵥ fun x' => Real.exp (θ * v x')) x ≤ (P *ᵥ fun x' => Real.exp (θ * w x')) x :=
        hP.mulVec_le_mulVec (fun y => Real.exp_le_exp.2 (by nlinarith [hvw y])) x
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hv h1) (inv_pos.2 hpos).le
  · funext x
    simp only [entR, hP.mulVec_const, Real.log_exp]
    field_simp

/-- Exercise 7.3.8 (p. 234): `R_θ` is constant-subadditive. -/
theorem constSubadditive_entR {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConstSubadditive (entR θ P) Set.univ := fun v _ c _ _ => (entR_add_const hθ hP v c).le

/-- Convexity of log-sum-exp: `log ∑ q e^{αa + (1−α)b} ≤ α log ∑ q e^a + (1 − α) log ∑ q e^b` for
weights `q ≥ 0` with a positive entry, by the weighted AM–GM inequality. -/
theorem log_sum_exp_le {q : X → ℝ} (hq : ∀ x, 0 ≤ q x) (hq1 : ∃ x, 0 < q x) (a b : X → ℝ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Real.log (∑ x, q x * Real.exp (α * a x + (1 - α) * b x)) ≤
      α * Real.log (∑ x, q x * Real.exp (a x)) +
        (1 - α) * Real.log (∑ x, q x * Real.exp (b x)) := by
  obtain ⟨x₀, hx₀⟩ := hq1
  have hpos : ∀ f : X → ℝ, 0 < ∑ x, q x * Real.exp (f x) := fun f =>
    lt_of_lt_of_le (mul_pos hx₀ (Real.exp_pos _))
      (single_le_sum (fun x _ => mul_nonneg (hq x) (Real.exp_pos _).le) (mem_univ x₀))
  set A := ∑ x, q x * Real.exp (a x) with hA
  set B := ∑ x, q x * Real.exp (b x) with hB
  have hA0 := hpos a
  have hB0 := hpos b
  -- `∑ q (e^a)^α (e^b)^{1−α} ≤ A^α B^{1−α}`
  have hterm : ∀ x, Real.exp (α * a x + (1 - α) * b x) =
      Real.exp (a x) ^ α * Real.exp (b x) ^ (1 - α) := fun x => by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hamgm : ∀ x, (Real.exp (a x) / A) ^ α * (Real.exp (b x) / B) ^ (1 - α) ≤
      α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B) := fun x =>
    Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith) (by positivity) (by positivity)
      (by ring)
  have hsum : ∑ x, q x * Real.exp (α * a x + (1 - α) * b x) ≤ A ^ α * B ^ (1 - α) := by
    have h1 : ∑ x, q x * ((Real.exp (a x) / A) ^ α * (Real.exp (b x) / B) ^ (1 - α)) ≤
        ∑ x, q x * (α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B)) :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hamgm x) (hq x)
    have h2 : ∑ x, q x * (α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B)) = 1 := by
      have : ∑ x, q x * (α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B)) =
          α * (A / A) + (1 - α) * (B / B) := by
        rw [hA, hB, sum_div, sum_div, mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun x _ => by ring
      rw [this, div_self hA0.ne', div_self hB0.ne']
      ring
    have h3 : ∑ x, q x * ((Real.exp (a x) / A) ^ α * (Real.exp (b x) / B) ^ (1 - α)) =
        (∑ x, q x * Real.exp (α * a x + (1 - α) * b x)) / (A ^ α * B ^ (1 - α)) := by
      rw [sum_div]
      refine sum_congr rfl fun x _ => ?_
      rw [hterm, Real.div_rpow (Real.exp_pos _).le hA0.le,
        Real.div_rpow (Real.exp_pos _).le hB0.le]
      ring
    rw [h3, h2, div_le_one (by positivity)] at h1
    exact h1
  have hS0 : 0 < ∑ x, q x * Real.exp (α * a x + (1 - α) * b x) := hpos _
  calc Real.log (∑ x, q x * Real.exp (α * a x + (1 - α) * b x))
      ≤ Real.log (A ^ α * B ^ (1 - α)) := Real.log_le_log hS0 hsum
    _ = α * Real.log A + (1 - α) * Real.log B := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA0, Real.log_rpow hB0]

/-- (7.17) and Example 7.3.6, Exercise 7.3.10 (p. 235): for `θ < 0` the entropic certainty
equivalent is concave on `ℝ^X`. -/
theorem concaveOn_entR {θ : ℝ} (hθ : θ < 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConcaveOn ℝ Set.univ (entR θ P) := by
  refine ⟨convex_univ, fun u _ w _ a b ha hb hab x => ?_⟩
  have hrow : ∃ x', 0 < P x x' := by
    by_contra hcon
    have : ∑ x', P x x' ≤ 0 := sum_nonpos fun x' _ => not_lt.1 fun h => hcon ⟨x', h⟩
    linarith [hP.rowsum x]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have h1 := log_sum_exp_le (q := P x) (hP.nonneg x) hrow (fun x' => θ * u x')
    (fun x' => θ * w x') ha (by linarith)
  simp only [entR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
  have h2 : ∀ x', θ * (a * u x' + (1 - a) * w x') = a * (θ * u x') + (1 - a) * (θ * w x') :=
    fun x' => by ring
  simp only [h2]
  have hθ' : θ⁻¹ < 0 := inv_lt_zero.2 hθ
  nlinarith [mul_le_mul_of_nonpos_left h1 hθ'.le]

/-! ### The Kreps–Porteus certainty equivalent (Example 7.3.3) -/

/-- The Kreps–Porteus certainty equivalent `(R_γ v)(x) = (∑ v(x')^γ P(x, x'))^{1/γ}` (7.16). -/
noncomputable def kpR (γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => (P *ᵥ fun x' => v x' ^ γ) x ^ γ⁻¹

theorem kpR_pos {γ : ℝ} {P : Matrix X X ℝ} (hP : IsMarkov P) {v : X → ℝ} (hv : v ∈ posCone X)
    (x : X) : 0 < kpR γ P v x :=
  Real.rpow_pos_of_pos (hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') _) x) _

/-- Exercise 7.3.3 (p. 233): `R_γ` is a certainty equivalent operator on `(0, ∞)^X` for `γ ≠ 0`. -/
theorem isCertEquiv_kpR {γ : ℝ} (hγ : γ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    IsCertEquiv (kpR γ P) (posCone X) := by
  refine ⟨fun v hv x => kpR_pos hP hv x, fun v hv w hw hvw x => ?_, fun c hc => ?_⟩
  · have hpv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
    have hpw := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hw x') γ) x
    unfold kpR
    rcases lt_or_gt_of_ne hγ with hneg | hpos
    · have h1 : (P *ᵥ fun x' => w x' ^ γ) x ≤ (P *ᵥ fun x' => v x' ^ γ) x :=
        hP.mulVec_le_mulVec (fun y => Real.rpow_le_rpow_of_nonpos (hv y) (hvw y) hneg.le) x
      exact Real.rpow_le_rpow_of_nonpos hpw h1 (inv_lt_zero.2 hneg).le
    · have h1 : (P *ᵥ fun x' => v x' ^ γ) x ≤ (P *ᵥ fun x' => w x' ^ γ) x :=
        hP.mulVec_le_mulVec (fun y => Real.rpow_le_rpow (hv y).le (hvw y) hpos.le) x
      exact Real.rpow_le_rpow hpv.le h1 (inv_pos.2 hpos).le
  · funext x
    have hc0 : 0 < c := hc x
    simp only [kpR, hP.mulVec_const]
    exact Real.rpow_rpow_inv hc0.le hγ

/-- `R_γ` is positively homogeneous on `(0, ∞)^X`. -/
theorem posHomogeneous_kpR {γ : ℝ} (hγ : γ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    PosHomogeneous (kpR γ P) (posCone X) := by
  intro v hv c hc _
  funext x
  have hpv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  simp only [kpR, Pi.smul_apply, smul_eq_mul]
  have h1 : (P *ᵥ fun x' => (c * v x') ^ γ) = c ^ γ • (P *ᵥ fun x' => v x' ^ γ) := by
    rw [← mulVec_smul]
    congr 1
    funext x'
    rw [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hc (hv x').le]
  rw [h1, Pi.smul_apply, smul_eq_mul, Real.mul_rpow (Real.rpow_nonneg hc _) hpv.le,
    Real.rpow_rpow_inv hc hγ]

/-- On the unit level set: `∑ q (a⁻¹ v)^γ = 1` when `a = (∑ q v^γ)^{1/γ}`. -/
theorem sum_rpow_normalize {γ : ℝ} (hγ : γ ≠ 0) {q v : X → ℝ}
    (hS : 0 < ∑ x, q x * v x ^ γ) :
    ∑ x, q x * ((∑ y, q y * v y ^ γ) ^ γ⁻¹)⁻¹ ^ γ * v x ^ γ = 1 := by
  have ha : 0 < (∑ y, q y * v y ^ γ) ^ γ⁻¹ := Real.rpow_pos_of_pos hS _
  have h1 : ((∑ y, q y * v y ^ γ) ^ γ⁻¹)⁻¹ ^ γ = (∑ y, q y * v y ^ γ)⁻¹ := by
    rw [Real.inv_rpow ha.le, Real.rpow_inv_rpow hS.le hγ]
  rw [h1]
  have : ∑ x, q x * (∑ y, q y * v y ^ γ)⁻¹ * v x ^ γ =
      (∑ y, q y * v y ^ γ)⁻¹ * ∑ x, q x * v x ^ γ := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [this, inv_mul_cancel₀ hS.ne']

/-- The level-set inequality behind Example 7.3.5. For `φ(t) = t^γ` convex on `(0, ∞)` and
`a = (∑ q v^γ)^{1/γ}`, `b = (∑ q w^γ)^{1/γ}`: `∑ q (v + w)^γ ≤ (a + b)^γ`; for `φ` concave the
reverse. -/
theorem sum_rpow_add_le {γ : ℝ} (hγ : γ ≠ 0) (hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ γ)
    {q v w : X → ℝ} (hq : ∀ x, 0 ≤ q x) (hv : ∀ x, 0 < v x) (hw : ∀ x, 0 < w x)
    (hSv : 0 < ∑ x, q x * v x ^ γ) (hSw : 0 < ∑ x, q x * w x ^ γ) :
    ∑ x, q x * (v x + w x) ^ γ ≤
      ((∑ x, q x * v x ^ γ) ^ γ⁻¹ + (∑ x, q x * w x ^ γ) ^ γ⁻¹) ^ γ := by
  set a := (∑ x, q x * v x ^ γ) ^ γ⁻¹ with hadef
  set b := (∑ x, q x * w x ^ γ) ^ γ⁻¹ with hbdef
  have ha : 0 < a := Real.rpow_pos_of_pos hSv _
  have hb : 0 < b := Real.rpow_pos_of_pos hSw _
  have hab : 0 < a + b := by linarith
  -- convex combination of the normalised points
  have hcomb : ∀ x, (a + b)⁻¹ * (v x + w x) =
      a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := fun x => by
    field_simp
  have hpt : ∀ x, ((a + b)⁻¹ * (v x + w x)) ^ γ ≤
      a / (a + b) * (a⁻¹ * v x) ^ γ + b / (a + b) * (b⁻¹ * w x) ^ γ := fun x => by
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw x))
      (by positivity) (by positivity) (by field_simp)
  have hnv := sum_rpow_normalize hγ hSv
  have hnw := sum_rpow_normalize hγ hSw
  rw [← hadef] at hnv
  rw [← hbdef] at hnw
  have hsum' : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ ≤
      a / (a + b) * (∑ x, q x * a⁻¹ ^ γ * v x ^ γ) +
        b / (a + b) * (∑ x, q x * b⁻¹ ^ γ * w x ^ γ) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    have := mul_le_mul_of_nonneg_left (hpt x) (hq x)
    rw [Real.mul_rpow (inv_pos.2 ha).le (hv x).le, Real.mul_rpow (inv_pos.2 hb).le (hw x).le]
      at this
    linarith
  have hsum : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ ≤ a / (a + b) * 1 + b / (a + b) * 1 := by
    rwa [hnv, hnw] at hsum'
  have h1 : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ =
      (a + b)⁻¹ ^ γ * ∑ x, q x * (v x + w x) ^ γ := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by
      rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv x) (hw x)).le]; ring
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2, Real.inv_rpow hab.le] at hsum
  have h3 : 0 < (a + b) ^ γ := Real.rpow_pos_of_pos hab _
  rwa [inv_mul_le_iff₀ h3, mul_one] at hsum

/-- The concave counterpart of `sum_rpow_add_le`. -/
theorem le_sum_rpow_add {γ : ℝ} (hγ : γ ≠ 0) (hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ γ)
    {q v w : X → ℝ} (hq : ∀ x, 0 ≤ q x) (hv : ∀ x, 0 < v x) (hw : ∀ x, 0 < w x)
    (hSv : 0 < ∑ x, q x * v x ^ γ) (hSw : 0 < ∑ x, q x * w x ^ γ) :
    ((∑ x, q x * v x ^ γ) ^ γ⁻¹ + (∑ x, q x * w x ^ γ) ^ γ⁻¹) ^ γ ≤
      ∑ x, q x * (v x + w x) ^ γ := by
  set a := (∑ x, q x * v x ^ γ) ^ γ⁻¹ with hadef
  set b := (∑ x, q x * w x ^ γ) ^ γ⁻¹ with hbdef
  have ha : 0 < a := Real.rpow_pos_of_pos hSv _
  have hb : 0 < b := Real.rpow_pos_of_pos hSw _
  have hab : 0 < a + b := by linarith
  have hcomb : ∀ x, (a + b)⁻¹ * (v x + w x) =
      a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := fun x => by
    field_simp
  have hpt : ∀ x, a / (a + b) * (a⁻¹ * v x) ^ γ + b / (a + b) * (b⁻¹ * w x) ^ γ ≤
      ((a + b)⁻¹ * (v x + w x)) ^ γ := fun x => by
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw x))
      (by positivity) (by positivity) (by field_simp)
  have hnv := sum_rpow_normalize hγ hSv
  have hnw := sum_rpow_normalize hγ hSw
  rw [← hadef] at hnv
  rw [← hbdef] at hnw
  have hsum' : a / (a + b) * (∑ x, q x * a⁻¹ ^ γ * v x ^ γ) +
        b / (a + b) * (∑ x, q x * b⁻¹ ^ γ * w x ^ γ) ≤
      ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    have := mul_le_mul_of_nonneg_left (hpt x) (hq x)
    rw [Real.mul_rpow (inv_pos.2 ha).le (hv x).le, Real.mul_rpow (inv_pos.2 hb).le (hw x).le]
      at this
    linarith
  have hsum : a / (a + b) * 1 + b / (a + b) * 1 ≤ ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ := by
    rwa [hnv, hnw] at hsum'
  have h1 : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ =
      (a + b)⁻¹ ^ γ * ∑ x, q x * (v x + w x) ^ γ := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by
      rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv x) (hw x)).le]; ring
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2, Real.inv_rpow hab.le] at hsum
  have h3 : 0 < (a + b) ^ γ := Real.rpow_pos_of_pos hab _
  rwa [le_inv_mul_iff₀ h3, mul_one] at hsum

/-- `t ↦ t^γ` is convex on `(0, ∞)` for `γ < 0`. -/
theorem convexOn_rpow_of_neg {γ : ℝ} (hγ : γ < 0) : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ γ := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    (fun t ht =>
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).continuousAt.continuousWithinAt)
    (by
      rw [interior_Ioi]
      exact fun t ht =>
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).differentiableAt.differentiableWithinAt)
    ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  rw [Real.deriv_rpow_const, Real.deriv_rpow_const]
  have h1 : t ^ (γ - 1) ≤ s ^ (γ - 1) := Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  nlinarith

/-- Example 7.3.5 (p. 234): the Kreps–Porteus operator is subadditive on `(0, ∞)^X` for `γ ≥ 1`. -/
theorem subadditive_kpR {γ : ℝ} (hγ : 1 ≤ γ) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    Subadditive (kpR γ P) (posCone X) := by
  intro v hv w hw _ x
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ γ :=
    (convexOn_rpow hγ).subset Ioi_subset_Ici_self (convex_Ioi 0)
  have hSv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  have hSw := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hw x') γ) x
  have h1 := sum_rpow_add_le hγ0.ne' hφ (hP.nonneg x) hv hw hSv hSw
  have h0 : 0 ≤ ∑ x', P x x' * (v x' + w x') ^ γ :=
    sum_nonneg fun x' _ => mul_nonneg (hP.nonneg x x')
      (Real.rpow_nonneg (add_pos (hv x') (hw x')).le _)
  have h2 := Real.rpow_le_rpow h0 h1 (inv_nonneg.2 hγ0.le)
  rw [Real.rpow_rpow_inv (by positivity) hγ0.ne'] at h2
  simpa [kpR, mulVec, dotProduct] using h2

/-- Example 7.3.5 (p. 234): the Kreps–Porteus operator is superadditive on `(0, ∞)^X` for `γ ≤ 1`,
`γ ≠ 0`. -/
theorem superadditive_kpR {γ : ℝ} (hγ0 : γ ≠ 0) (hγ : γ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) : Superadditive (kpR γ P) (posCone X) := by
  intro v hv w hw _ x
  have hSv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  have hSw := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hw x') γ) x
  have hsum0 : 0 < ∑ x', P x x' * (v x' + w x') ^ γ := by
    have := hP.mulVec_pos (f := fun x' => (v x' + w x') ^ γ)
      (fun x' => Real.rpow_pos_of_pos (add_pos (hv x') (hw x')) γ) x
    simpa [mulVec, dotProduct] using this
  have hab : 0 < (∑ x', P x x' * v x' ^ γ) ^ γ⁻¹ + (∑ x', P x x' * w x' ^ γ) ^ γ⁻¹ := by
    have h1 : 0 < ∑ x', P x x' * v x' ^ γ := by simpa [mulVec, dotProduct] using hSv
    have h2 : 0 < ∑ x', P x x' * w x' ^ γ := by simpa [mulVec, dotProduct] using hSw
    positivity
  rcases lt_or_gt_of_ne hγ0 with hneg | hpos
  · have h1 := sum_rpow_add_le hγ0 (convexOn_rpow_of_neg hneg) (hP.nonneg x) hv hw
      (by simpa [mulVec, dotProduct] using hSv) (by simpa [mulVec, dotProduct] using hSw)
    have h2 := Real.rpow_le_rpow_of_nonpos hsum0 h1 (inv_lt_zero.2 hneg).le
    rw [Real.rpow_rpow_inv hab.le hγ0] at h2
    simpa [kpR, mulVec, dotProduct] using h2
  · have hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ γ :=
      (Real.concaveOn_rpow hpos.le hγ).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h1 := le_sum_rpow_add hγ0 hφ (hP.nonneg x) hv hw
      (by simpa [mulVec, dotProduct] using hSv) (by simpa [mulVec, dotProduct] using hSw)
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hab.le _) h1 (inv_nonneg.2 hpos.le)
    rw [Real.rpow_rpow_inv hab.le hγ0] at h2
    simpa [kpR, mulVec, dotProduct] using h2

omit [Fintype X] in
/-- `(0, ∞)^X` is closed under positive scaling. -/
theorem smul_mem_posCone {v : X → ℝ} (hv : v ∈ posCone X) {c : ℝ} (hc : 0 < c) :
    c • v ∈ posCone X := fun x => by simpa using mul_pos hc (hv x)

/-- **Lemma 7.3.1** (p. 235): the Kreps–Porteus operator is convex on `(0, ∞)^X` when `γ ≥ 1`. -/
theorem convexOn_kpR {γ : ℝ} (hγ : 1 ≤ γ) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConvexOn ℝ (posCone X) (kpR γ P) :=
  convexOn_of_subadditive convex_posCone (fun _ hv _ hc => smul_mem_posCone hv hc)
    (posHomogeneous_kpR (by linarith) hP) (subadditive_kpR hγ hP)

/-- **Lemma 7.3.1** (p. 235): the Kreps–Porteus operator is concave on `(0, ∞)^X` when `γ ≤ 1`,
`γ ≠ 0`. -/
theorem concaveOn_kpR {γ : ℝ} (hγ0 : γ ≠ 0) (hγ : γ ≤ 1) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConcaveOn ℝ (posCone X) (kpR γ P) :=
  concaveOn_of_superadditive convex_posCone (fun _ hv _ hc => smul_mem_posCone hv hc)
    (posHomogeneous_kpR hγ0 hP) (superadditive_kpR hγ0 hγ hP)

/-! ### The quantile certainty equivalent (Exercise 7.3.4) -/

/-- The conditional distribution function `y ↦ ∑ 1{v(x') ≤ y} P(x, x')`. -/
noncomputable def condCdf (P : Matrix X X ℝ) (v : X → ℝ) (x : X) (y : ℝ) : ℝ :=
  ∑ x', if v x' ≤ y then P x x' else 0

open Classical in
/-- The quantile certainty equivalent of Exercise 7.3.4: the smallest value `y` of `v` with
`∑ 1{v(x') ≤ y} P(x, x') ≥ τ`. For `τ ∈ (0, 1]` and Markov `P` it is the least real `y` with that
property (`isLeast_quantR`). -/
noncomputable def quantR (τ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ := fun x =>
  if h : ((univ.filter fun x' => τ ≤ condCdf P v x (v x')).image v).Nonempty then
    ((univ.filter fun x' => τ ≤ condCdf P v x (v x')).image v).min' h else 0

/-- For `τ ∈ (0, 1]`, `P` Markov and `X` nonempty, `R_τ v(x)` is the least `y` with
`∑ 1{v(x') ≤ y} P(x, x') ≥ τ`, the minimum in Exercise 7.3.4. -/
theorem isLeast_quantR [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) (v : X → ℝ) (x : X) :
    IsLeast {y | τ ≤ condCdf P v x y} (quantR τ P v x) := by
  classical
  set S := (univ.filter fun x' => τ ≤ condCdf P v x (v x')).image v with hS
  have hne : S.Nonempty := by
    obtain ⟨xm, -, hxm⟩ := exists_max_image univ v univ_nonempty
    refine ⟨v xm, mem_image.2 ⟨xm, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩⟩
    have : condCdf P v x (v xm) = 1 := by
      rw [condCdf, ← hP.rowsum x]
      exact sum_congr rfl fun x' _ => by simp [hxm x' (mem_univ _)]
    linarith
  have hq : quantR τ P v x = S.min' hne := by
    unfold quantR
    split_ifs with h
    · rfl
    · exact absurd hne h
  rw [hq]
  constructor
  · obtain ⟨x₀, hx₀, he⟩ := mem_image.1 (S.min'_mem hne)
    rw [← he]
    exact (mem_filter.1 hx₀).2
  · intro y hy
    -- some `x''` with `v x'' ≤ y`, else the cdf at `y` is zero
    have hex : (univ.filter fun x' => v x' ≤ y).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have : condCdf P v x y = 0 := sum_eq_zero fun x' _ => by
        have : ¬ v x' ≤ y := fun h => by
          have : x' ∈ univ.filter fun x' => v x' ≤ y := mem_filter.2 ⟨mem_univ x', h⟩
          rw [hcon] at this
          exact absurd this (Finset.notMem_empty _)
        simp [this]
      change τ ≤ condCdf P v x y at hy
      linarith
    obtain ⟨x₁, hx₁, hmax⟩ := exists_max_image _ v hex
    have hx₁y : v x₁ ≤ y := (mem_filter.1 hx₁).2
    have hcdf : condCdf P v x (v x₁) = condCdf P v x y := by
      refine sum_congr rfl fun x' _ => ?_
      by_cases h : v x' ≤ y
      · simp [h, hmax x' (mem_filter.2 ⟨mem_univ _, h⟩)]
      · have : ¬ v x' ≤ v x₁ := fun h' => h (h'.trans hx₁y)
        simp [h, this]
    have hmem : v x₁ ∈ S := mem_image.2 ⟨x₁, mem_filter.2 ⟨mem_univ _, by rw [hcdf]; exact hy⟩,
      rfl⟩
    exact (S.min'_le _ hmem).trans hx₁y

/-- Exercise 7.3.4 (p. 233): for `τ ∈ (0, 1]` and `P` Markov, `R_τ` is a certainty equivalent
operator on `ℝ^X`. -/
theorem isCertEquiv_quantR [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) : IsCertEquiv (quantR τ P) Set.univ := by
  refine ⟨fun _ _ => mem_univ _, fun v _ w _ hvw x => ?_, fun c _ => ?_⟩
  · obtain ⟨hw1, -⟩ := isLeast_quantR hτ0 hτ1 hP w x
    refine (isLeast_quantR hτ0 hτ1 hP v x).2 ?_
    change τ ≤ condCdf P v x (quantR τ P w x)
    refine hw1.trans (sum_le_sum fun x' _ => ?_)
    by_cases h : w x' ≤ quantR τ P w x
    · simp [h, (hvw x').trans h]
    · by_cases h' : v x' ≤ quantR τ P w x
      · simp [h, h', hP.nonneg x x']
      · simp [h, h']
  · funext x
    have hcdf : ∀ y, condCdf P (fun _ => c) x y = if c ≤ y then 1 else 0 := fun y => by
      by_cases h : c ≤ y
      · simp [condCdf, h, hP.rowsum x]
      · simp [condCdf, h]
    obtain ⟨h1, h2⟩ := isLeast_quantR hτ0 hτ1 hP (fun _ => c) x
    have hle : quantR τ P (fun _ => c) x ≤ c := h2 (by
      change τ ≤ condCdf P (fun _ => c) x c
      rw [hcdf]
      simp only [le_refl, ↓reduceIte]
      exact hτ1)
    have hge : c ≤ quantR τ P (fun _ => c) x := by
      change τ ≤ condCdf P (fun _ => c) x _ at h1
      rw [hcdf] at h1
      by_contra hlt
      simp only [hlt, ↓reduceIte] at h1
      linarith
    exact le_antisymm hle hge

/-- Exercise 7.3.7, in the stronger form of translation equivariance: `R_τ(v + c) = R_τ v + c`. -/
theorem quantR_add_const [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) (v : X → ℝ) (c : ℝ) :
    quantR τ P (v + fun _ => c) = quantR τ P v + fun _ => c := by
  funext x
  have hcdf : ∀ y, condCdf P (v + fun _ => c) x y = condCdf P v x (y - c) := fun y =>
    sum_congr rfl fun x' _ => by
      by_cases h : v x' ≤ y - c
      · have : v x' + c ≤ y := by linarith
        simp [h, this]
      · have : ¬ v x' + c ≤ y := fun h' => h (by linarith)
        simp [h, this]
  obtain ⟨h1, h2⟩ := isLeast_quantR hτ0 hτ1 hP (v + fun _ => c) x
  obtain ⟨g1, g2⟩ := isLeast_quantR hτ0 hτ1 hP v x
  change τ ≤ condCdf P (v + fun _ => c) x _ at h1
  change τ ≤ condCdf P v x _ at g1
  simp only [Pi.add_apply]
  apply le_antisymm
  · refine h2 ?_
    change τ ≤ condCdf P (v + fun _ => c) x _
    rw [hcdf, add_sub_cancel_right]
    exact g1
  · have : quantR τ P v x ≤ quantR τ P (v + fun _ => c) x - c :=
      g2 (by change τ ≤ condCdf P v x _; rw [← hcdf]; exact h1)
    linarith

/-- Exercise 7.3.7 (p. 234): `R_τ` is constant-subadditive. -/
theorem constSubadditive_quantR [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : ConstSubadditive (quantR τ P) Set.univ :=
  fun v _ c _ _ => (quantR_add_const hτ0 hτ1 hP v c).le

/-! ### Monotone increasing certainty equivalents (§7.3.1.3) -/

/-- A matrix maps increasing functions to increasing functions (Vol. 1, §3.2.1.3). -/
def MonotoneKernel [Preorder X] (P : Matrix X X ℝ) : Prop :=
  ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h)

/-- A monotone kernel maps decreasing functions to decreasing functions. -/
theorem MonotoneKernel.antitone [Preorder X] {P : Matrix X X ℝ} (hP : MonotoneKernel P)
    {h : X → ℝ} (hh : Antitone h) : Antitone (P *ᵥ h) := by
  have := hP (-h) fun x y hxy => neg_le_neg (hh hxy)
  intro x y hxy
  have h1 := this hxy
  rw [mulVec_neg] at h1
  exact neg_le_neg_iff.1 h1

/-- Exercise 7.3.12 (p. 235): the entropic certainty equivalent maps increasing functions to
increasing functions when `P` is monotone increasing, for every `θ ≠ 0`. -/
theorem monotone_entR [Preorder X] {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hPm : MonotoneKernel P) {v : X → ℝ} (hv : Monotone v) : Monotone (entR θ P v) := by
  intro x y hxy
  have hpx := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) x
  have hpy := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) y
  unfold entR
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hanti : Antitone fun x' => Real.exp (θ * v x') := fun a b hab =>
      Real.exp_le_exp.2 (by nlinarith [hv hab])
    have h1 := hPm.antitone hanti hxy
    exact mul_le_mul_of_nonpos_left (Real.log_le_log hpy h1) (inv_lt_zero.2 hneg).le
  · have hmono : Monotone fun x' => Real.exp (θ * v x') := fun a b hab =>
      Real.exp_le_exp.2 (by nlinarith [hv hab])
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpx (hPm _ hmono hxy)) (inv_pos.2 hpos).le

/-- Exercise 7.3.13 (p. 236): the Kreps–Porteus certainty equivalent maps increasing positive
functions to increasing functions when `P` is monotone increasing, for every `γ ≠ 0`. -/
theorem monotone_kpR [Preorder X] {γ : ℝ} (hγ : γ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hPm : MonotoneKernel P) {v : X → ℝ} (hv0 : v ∈ posCone X) (hv : Monotone v) :
    Monotone (kpR γ P v) := by
  intro x y hxy
  have hpx := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv0 x') γ) x
  have hpy := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv0 x') γ) y
  unfold kpR
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · have hanti : Antitone fun x' => v x' ^ γ := fun a b hab =>
      Real.rpow_le_rpow_of_nonpos (hv0 a) (hv hab) hneg.le
    exact Real.rpow_le_rpow_of_nonpos hpy (hPm.antitone hanti hxy) (inv_lt_zero.2 hneg).le
  · have hmono : Monotone fun x' => v x' ^ γ := fun a b hab =>
      Real.rpow_le_rpow (hv0 a).le (hv hab) hpos.le
    exact Real.rpow_le_rpow hpx.le (hPm _ hmono hxy) (inv_pos.2 hpos).le

end SargentStachurski.NonlinearValuation
