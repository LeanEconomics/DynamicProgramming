/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NonlinearValuation.CertaintyEquivalents

/-!
# Aggregators, Koopmans operators and lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.3.1.4–§7.3.3.2
(pp. 236–242).

* Aggregators (§7.3.1.4): Leontief, Uzawa, CES, additive and CES–Uzawa; the
  additive aggregator is the CES aggregator with `α = 1`.
* Koopmans operators `K = A ∘ R` (7.18) are order-preserving self-maps; the
  risk-sensitive and Epstein–Zin operators (Examples 7.3.7–7.3.8) and the time
  additive operator (Remark 7.3.1).
* Exercise 7.3.14: the CES aggregator has elasticity of intertemporal substitution
  `1/(1 − α)`: `log(U_c/U_y) = log((1 − β)/β) + (1 − α) log(y/c)`.
* Example 7.3.9 and Exercise 7.3.15: time additive lifetime value
  `(I − βP)⁻¹r = ∑ (βP)ᵗr`, the finite-horizon value `Kᵐw = ∑_{t<m}(βP)ᵗr + (βP)ᵐw` and
  its convergence.
* Lemma 7.3.2: fixed points of globally stable Koopmans operators that preserve
  increasing functions are increasing.
* Blackwell aggregators (7.19), Exercise 7.3.17 and Proposition 7.3.3: with a
  constant-subadditive certainty equivalent, `K` is a contraction; hence
  Proposition 7.2.2 (risk-sensitive preferences), Exercise 7.3.18 and quantile
  preferences (7.20) with Exercise 7.3.19.
* Uzawa aggregation (§7.3.3): with conditional expectations, `K v = r + Lv` is
  globally stable when `ρ(L) < 1`, its fixed point is the lifetime value (7.22), and
  for `b, r ≫ 0` and `P` irreducible there is no positive fixed point when
  `ρ(L) ≥ 1`; Exercise 7.3.20; Proposition 7.3.4 via Du's theorem.
-/

open Matrix Finset Filter Topology Function Set

namespace SargentStachurski.NonlinearValuation

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X]

/-! ### Aggregators -/

/-- An aggregator on `V` (§7.3.1.4): `x ↦ A(x, v(x))` maps `V` into `V`, and `y ↦ A(x, y)` is
increasing on a set `D` containing the values of the functions in `V`. -/
structure IsAggregator (Agg : X → ℝ → ℝ) (V : Set (X → ℝ)) (D : Set ℝ) : Prop where
  values : ∀ v ∈ V, ∀ x, v x ∈ D
  mapsTo : ∀ v ∈ V, (fun x => Agg x (v x)) ∈ V
  mono : ∀ x, MonotoneOn (Agg x) D

/-- The Leontief aggregator `A(x, y) = min{r(x), βy}`. -/
def leontief (r : X → ℝ) (β : ℝ) : X → ℝ → ℝ := fun x y => min (r x) (β * y)

/-- The Uzawa aggregator `A(x, y) = r(x) + b(x)y`. -/
def uzawa (r b : X → ℝ) : X → ℝ → ℝ := fun x y => r x + b x * y

/-- The CES aggregator `A(x, y) = (r(x)^α + βy^α)^{1/α}`. -/
noncomputable def cesAgg (r : X → ℝ) (β α : ℝ) : X → ℝ → ℝ :=
  fun x y => (r x ^ α + β * y ^ α) ^ α⁻¹

/-- The additive aggregator `A(x, y) = r(x) + βy`. -/
def additive (r : X → ℝ) (β : ℝ) : X → ℝ → ℝ := fun x y => r x + β * y

/-- The CES–Uzawa aggregator `A(x, y) = (r(x)^α + b(x)y^α)^{1/α}`. -/
noncomputable def cesUzawa (r b : X → ℝ) (α : ℝ) : X → ℝ → ℝ :=
  fun x y => (r x ^ α + b x * y ^ α) ^ α⁻¹

omit [Fintype X] in
/-- The additive aggregator is the Uzawa aggregator with constant `b ≡ β`. -/
theorem additive_eq_uzawa (r : X → ℝ) (β : ℝ) : additive r β = uzawa r fun _ => β := rfl

omit [Fintype X] in
/-- The additive aggregator is the CES aggregator with `α = 1` (p. 236). -/
theorem additive_eq_cesAgg (r : X → ℝ) (β : ℝ) : cesAgg r β 1 = additive r β := by
  funext x y
  simp [cesAgg, additive]

omit [Fintype X] in
theorem isAggregator_leontief (r : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    IsAggregator (leontief r β) Set.univ Set.univ :=
  ⟨fun _ _ _ => mem_univ _, fun _ _ => mem_univ _, fun _ _ _ _ _ hyz =>
    min_le_min le_rfl (mul_le_mul_of_nonneg_left hyz hβ)⟩

omit [Fintype X] in
theorem isAggregator_uzawa (r : X → ℝ) {b : X → ℝ} (hb : ∀ x, 0 ≤ b x) :
    IsAggregator (uzawa r b) Set.univ Set.univ :=
  ⟨fun _ _ _ => mem_univ _, fun _ _ => mem_univ _, fun x _ _ _ _ hyz =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hyz (hb x))⟩

omit [Fintype X] in
theorem isAggregator_additive (r : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    IsAggregator (additive r β) Set.univ Set.univ :=
  isAggregator_uzawa r fun _ => hβ

omit [Fintype X] in
/-- The CES–Uzawa aggregator is an aggregator on `(0, ∞)^X` for `r ≫ 0`, `b ≥ 0`, `α ≠ 0`. -/
theorem isAggregator_cesUzawa {r b : X → ℝ} (hr : ∀ x, 0 < r x) (hb : ∀ x, 0 ≤ b x) {α : ℝ}
    (hα : α ≠ 0) : IsAggregator (cesUzawa r b α) (posCone X) (Ioi 0) := by
  have hbase : ∀ x, ∀ y : ℝ, 0 < y → 0 < r x ^ α + b x * y ^ α := fun x y hy =>
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (hr x) _)
      (mul_nonneg (hb x) (Real.rpow_nonneg hy.le _))
  refine ⟨fun v hv x => hv x, fun v hv x => Real.rpow_pos_of_pos (hbase x _ (hv x)) _,
    fun x y hy z hz hyz => ?_⟩
  have hy' : (0 : ℝ) < y := hy
  have hz' : (0 : ℝ) < z := hz
  unfold cesUzawa
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : z ^ α ≤ y ^ α := Real.rpow_le_rpow_of_nonpos hy' hyz hneg.le
    exact Real.rpow_le_rpow_of_nonpos (hbase x z hz')
      (by nlinarith [hb x]) (inv_lt_zero.2 hneg).le
  · have h1 : y ^ α ≤ z ^ α := Real.rpow_le_rpow hy'.le hyz hpos.le
    exact Real.rpow_le_rpow (hbase x y hy').le (by nlinarith [hb x]) (inv_pos.2 hpos).le

omit [Fintype X] in
/-- The CES aggregator is an aggregator on `(0, ∞)^X` for `r ≫ 0`, `β ≥ 0`, `α ≠ 0` (p. 236). -/
theorem isAggregator_cesAgg {r : X → ℝ} (hr : ∀ x, 0 < r x) {β : ℝ} (hβ : 0 ≤ β) {α : ℝ}
    (hα : α ≠ 0) : IsAggregator (cesAgg r β α) (posCone X) (Ioi 0) :=
  isAggregator_cesUzawa (b := fun _ => β) hr (fun _ => hβ) hα

/-! ### Koopmans operators -/

/-- The Koopmans operator `K = A ∘ R` (7.18): `(Kv)(x) = A(x, (Rv)(x))`. -/
def koopmans (Agg : X → ℝ → ℝ) (R : (X → ℝ) → (X → ℝ)) (v : X → ℝ) : X → ℝ :=
  fun x => Agg x (R v x)

omit [Fintype X] in
/-- A Koopmans operator is an order-preserving self-map of `V` (p. 237). -/
theorem koopmans_mapsTo_monotoneOn {Agg : X → ℝ → ℝ} {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    {D : Set ℝ} (hA : IsAggregator Agg V D) (hR : IsCertEquiv R V) :
    MapsTo (koopmans Agg R) V V ∧ MonotoneOn (koopmans Agg R) V :=
  ⟨fun _ hv => hA.mapsTo _ (hR.mapsTo hv), fun v hv w hw hvw x =>
    hA.mono x (hA.values _ (hR.mapsTo hv) x) (hA.values _ (hR.mapsTo hw) x)
      (hR.mono v hv w hw hvw x)⟩

/-- Example 7.3.7 (p. 237): the risk-sensitive Koopmans operator (7.10) is `A_ADD ∘ R_θ`. -/
theorem koopmans_additive_entR (r : X → ℝ) (β θ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X) :
    koopmans (additive r β) (entR θ P) v x =
      r x + β * (θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * v x')) x)) := rfl

/-- Example 7.3.8 (p. 237): the Epstein–Zin Koopmans operator (7.13) is `A_CES ∘ R_γ`. -/
theorem koopmans_cesAgg_kpR (r : X → ℝ) (β α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X) :
    koopmans (cesAgg r β α) (kpR γ P) v x =
      (r x ^ α + β * ((P *ᵥ fun x' => v x' ^ γ) x ^ γ⁻¹) ^ α) ^ α⁻¹ := rfl

/-- Remark 7.3.1 (p. 237): the time additive Koopmans operator is `v ↦ r + βPv`. -/
theorem koopmans_additive_mulVec (r : X → ℝ) (β : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) :
    koopmans (additive r β) (fun v => P *ᵥ v) v = r + β • (P *ᵥ v) := rfl

/-! ### Exercise 7.3.14: the elasticity of intertemporal substitution -/

/-- Exercise 7.3.14 (p. 237): for `U(c, y) = ((1 − β)c^α + βy^α)^{1/α}` with `c, y > 0`,
`0 < β < 1` and `α ≠ 0`, the partial derivatives satisfy
`log(U_c/U_y) = log((1 − β)/β) + (1 − α) log(y/c)`, so `d log(y/c)/d log(U_c/U_y) = 1/(1 − α)`. -/
theorem ces_eis {β α c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα : α ≠ 0) (hc : 0 < c)
    (hy : 0 < y) :
    ∃ Uc Uy : ℝ, HasDerivAt (fun c' => ((1 - β) * c' ^ α + β * y ^ α) ^ α⁻¹) Uc c ∧
      HasDerivAt (fun y' => ((1 - β) * c ^ α + β * y' ^ α) ^ α⁻¹) Uy y ∧ 0 < Uc ∧ 0 < Uy ∧
      Real.log (Uc / Uy) = Real.log ((1 - β) / β) + (1 - α) * Real.log (y / c) := by
  have hβ1' : 0 < 1 - β := by linarith
  set S := (1 - β) * c ^ α + β * y ^ α with hS
  have hca : 0 < c ^ α := Real.rpow_pos_of_pos hc _
  have hya : 0 < y ^ α := Real.rpow_pos_of_pos hy _
  have hSpos : 0 < S := by positivity
  have hdc : HasDerivAt (fun c' => (1 - β) * c' ^ α + β * y ^ α) ((1 - β) * (α * c ^ (α - 1))) c :=
    ((Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul (1 - β)).add_const _
  have hdy : HasDerivAt (fun y' => (1 - β) * c ^ α + β * y' ^ α) (β * (α * y ^ (α - 1))) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul β).const_add _
  have hUc := hdc.rpow_const (p := α⁻¹) (Or.inl hSpos.ne')
  have hUy := hdy.rpow_const (p := α⁻¹) (Or.inl hSpos.ne')
  refine ⟨_, _, hUc, hUy, ?_, ?_, ?_⟩
  · have e : (1 - β) * (α * c ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1) =
        (1 - β) * c ^ (α - 1) * S ^ (α⁻¹ - 1) := by field_simp
    rw [e]
    have := Real.rpow_pos_of_pos hc (α - 1)
    have := Real.rpow_pos_of_pos hSpos (α⁻¹ - 1)
    positivity
  · have e : β * (α * y ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1) = β * y ^ (α - 1) * S ^ (α⁻¹ - 1) := by
      field_simp
    rw [e]
    have := Real.rpow_pos_of_pos hy (α - 1)
    have := Real.rpow_pos_of_pos hSpos (α⁻¹ - 1)
    positivity
  · have hSa := Real.rpow_pos_of_pos hSpos (α⁻¹ - 1)
    have hc1 := Real.rpow_pos_of_pos hc (α - 1)
    have hy1 := Real.rpow_pos_of_pos hy (α - 1)
    have e : (1 - β) * (α * c ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1) /
        (β * (α * y ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1)) =
        ((1 - β) / β) * (c ^ (α - 1) / y ^ (α - 1)) := by
      field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_div hc1.ne' hy1.ne',
      Real.log_rpow hc, Real.log_rpow hy, Real.log_div hy.ne' hc.ne']
    ring

/-! ### Lifetime value (§7.3.1.7) -/

variable [DecidableEq X]

/-- Exercise 7.3.15 (i)–(ii) (p. 238): the `m`-period time additive value with terminal condition
`w` is `Kᵐw = ∑_{t<m} (βP)ᵗr + (βP)ᵐw`. -/
theorem iterate_additive_eq (r : X → ℝ) (β : ℝ) (P : Matrix X X ℝ) (w : X → ℝ) (m : ℕ) :
    (koopmans (additive r β) fun v => P *ᵥ v)^[m] w =
      (∑ t ∈ range m, (β • P) ^ t *ᵥ r) + (β • P) ^ m *ᵥ w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iterate_succ_apply', ih, koopmans_additive_mulVec, sum_range_succ', pow_zero, one_mulVec,
      mulVec_add, mulVec_sum, smul_add, smul_sum]
    have h1 : ∀ (u : X → ℝ) (t : ℕ), β • (P *ᵥ ((β • P) ^ t *ᵥ u)) = (β • P) ^ (t + 1) *ᵥ u :=
      fun u t => by rw [← smul_mulVec, mulVec_mulVec, ← pow_succ']
    simp only [h1]
    abel

variable [Nonempty X]

/-- Example 7.3.9 and Exercise 7.3.15 (iii) (p. 238): for `P` Markov and `0 ≤ β < 1`, the time
additive Koopmans operator is globally stable on `ℝ^X`, with fixed point
`(I − βP)⁻¹r = ∑ (βP)ᵗr`, and `Kᵐw → (I − βP)⁻¹r` for every terminal condition `w`. -/
theorem additive_lifetimeValue {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (r : X → ℝ) :
    GloballyStable (koopmans (additive r β) fun v => P *ᵥ v) ∧
      IsFixedPt (koopmans (additive r β) fun v => P *ᵥ v) ((1 - β • P)⁻¹ *ᵥ r) ∧
      (1 - β • P)⁻¹ *ᵥ r = ∑' t : ℕ, (β • P) ^ t *ᵥ r ∧
      ∀ w, Tendsto (fun m => (koopmans (additive r β) fun v => P *ᵥ v)^[m] w) atTop
        (𝓝 ((1 - β • P)⁻¹ *ᵥ r)) := by
  have hρ : specRad (β • P) < 1 := by rw [specRad_smul_isMarkov hP hβ0]; exact hβ1
  have hK : (koopmans (additive r β) fun v => P *ᵥ v) = affineOp (β • P) r := by
    funext v
    rw [koopmans_additive_mulVec, affineOp, smul_mulVec, add_comm]
  rw [hK]
  have hst := globallyStable_affineOp hρ r
  have hfix := isFixedPt_affineOp_inv hρ r
  obtain ⟨u, hu, huniq, hconv⟩ := hst
  have hu' : (1 - β • P)⁻¹ *ᵥ r = u := huniq _ hfix
  refine ⟨⟨u, hu, huniq, hconv⟩, hfix, inv_mulVec_eq_tsum hρ r, fun w => ?_⟩
  rw [hu']
  exact hconv w

omit [DecidableEq X] [Nonempty X] [Fintype X] in
/-- **Lemma 7.3.2** (p. 239), abstract form: if `K` is globally stable on `V`, `V` contains an
increasing function, and `K` maps increasing functions in `V` to increasing functions, then the
fixed point of `K` is increasing. -/
theorem monotone_of_globallyStableOn [Preorder X] {K : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    (hst : GloballyStableOn K V) (hmaps : MapsTo K V V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ V)
    (hm₀ : Monotone v₀) (hinv : ∀ v ∈ V, Monotone v → Monotone (K v)) {u : X → ℝ}
    (hu : u ∈ V) (hfix : IsFixedPt K u) : Monotone u := by
  obtain ⟨u', -, -, huniq, hconv⟩ := hst
  rw [huniq u hu hfix]
  have hmono : ∀ k, Monotone (K^[k] v₀) ∧ K^[k] v₀ ∈ V := by
    intro k
    induction k with
    | zero => exact ⟨hm₀, hv₀⟩
    | succ k ih =>
      rw [iterate_succ_apply']
      exact ⟨hinv _ ih.2 ih.1, hmaps ih.2⟩
  intro x y hxy
  have hlim := tendsto_pi_nhds.1 (hconv v₀ hv₀)
  exact le_of_tendsto_of_tendsto' (hlim x) (hlim y) fun k => (hmono k).1 hxy

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- **Lemma 7.3.2** (p. 239): if `K = A ∘ R` is globally stable on `V`, `V` contains an increasing
function, (i) `A(x, y) ≤ A(x', y)` for `x ≤ x'`, and (ii) `R` maps increasing functions in `V` to
increasing functions, then the lifetime value `v*` is increasing. -/
theorem monotone_koopmans_fixedPt [Preorder X] {Agg : X → ℝ → ℝ} {R : (X → ℝ) → (X → ℝ)}
    {V : Set (X → ℝ)} {D : Set ℝ} (hA : IsAggregator Agg V D) (hR : IsCertEquiv R V)
    (hst : GloballyStableOn (koopmans Agg R) V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ V) (hm₀ : Monotone v₀)
    (hAx : ∀ x x', x ≤ x' → ∀ y ∈ D, Agg x y ≤ Agg x' y)
    (hRm : ∀ v ∈ V, Monotone v → Monotone (R v)) {u : X → ℝ} (hu : u ∈ V)
    (hfix : IsFixedPt (koopmans Agg R) u) : Monotone u := by
  refine monotone_of_globallyStableOn hst (koopmans_mapsTo_monotoneOn hA hR).1 hv₀ hm₀
    (fun v hv hm x x' hxx' => ?_) hu hfix
  have hD := hA.values _ (hR.mapsTo hv)
  exact (hA.mono x (hD x) (hD x') (hRm v hv hm hxx')).trans (hAx x x' hxx' _ (hD x'))

/-! ### A Blackwell-type condition (§7.3.2) -/

omit [DecidableEq X] [Nonempty X] in
/-- A Blackwell aggregator (7.19): `A(x, y + λ) ≤ A(x, y) + βλ` for `λ ≥ 0`, with `0 ≤ β < 1`. -/
def IsBlackwellAgg (Agg : X → ℝ → ℝ) (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧ ∀ x y c, 0 ≤ c → Agg x (y + c) ≤ Agg x y + β * c

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 7.3.17 (p. 240): the additive aggregator is a Blackwell aggregator for `0 ≤ β < 1`. -/
theorem isBlackwellAgg_additive (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsBlackwellAgg (additive r β) β :=
  ⟨hβ0, hβ1, fun x y c _ => by simp only [additive]; linarith⟩

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 7.3.17 (p. 240): the Leontief aggregator is a Blackwell aggregator for `0 ≤ β < 1`. -/
theorem isBlackwellAgg_leontief (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsBlackwellAgg (leontief r β) β := by
  refine ⟨hβ0, hβ1, fun x y c hc => ?_⟩
  simp only [leontief]
  rcases le_total (r x) (β * y) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by nlinarith)

omit [DecidableEq X] [Nonempty X] in
/-- **Proposition 7.3.3** (p. 240): if `A` is a Blackwell aggregator, increasing in `y`, and `R` is
a constant-subadditive certainty equivalent on `ℝ^X`, then `K = A ∘ R` is a contraction of
modulus `β` on `ℝ^X` in the supremum norm. -/
theorem isContractionOn_koopmans {Agg : X → ℝ → ℝ} {β : ℝ} (hA : IsBlackwellAgg Agg β)
    (hmono : ∀ x, Monotone (Agg x)) {R : (X → ℝ) → (X → ℝ)} (hR : IsCertEquiv R Set.univ)
    (hc : ConstSubadditive R Set.univ) : IsContractionOn (koopmans Agg R) Set.univ β := by
  refine isContractionOn_of_blackwell hA.1 hA.2.1
    (fun v w hvw x => hmono x (hR.mono v (mem_univ _) w (mem_univ _) hvw x)) fun u c hc0 x => ?_
  have h1 := hc u (mem_univ _) c hc0 (mem_univ _) x
  calc koopmans Agg R (u + fun _ => c) x = Agg x (R (u + fun _ => c) x) := rfl
    _ ≤ Agg x (R u x + c) := hmono x (by simpa using h1)
    _ ≤ Agg x (R u x) + β * c := hA.2.2 x _ c hc0

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Proposition 7.3.3: under its hypotheses `K` is globally stable on `ℝ^X`. -/
theorem globallyStable_koopmans [Finite X] {Agg : X → ℝ → ℝ} {β : ℝ} (hA : IsBlackwellAgg Agg β)
    (hmono : ∀ x, Monotone (Agg x)) {R : (X → ℝ) → (X → ℝ)} (hR : IsCertEquiv R Set.univ)
    (hc : ConstSubadditive R Set.univ) : GloballyStable (koopmans Agg R) := by
  have := Fintype.ofFinite X
  exact (isContractionOn_koopmans hA hmono hR hc).globallyStable_univ

omit [DecidableEq X] [Nonempty X] in
/-- **Proposition 7.2.2** (p. 224), proved on p. 240: for `0 ≤ β < 1` and `θ ≠ 0` the risk-sensitive
Koopmans operator `K_θ` is globally stable on `ℝ^X`. -/
theorem globallyStable_riskSensitive {P : Matrix X X ℝ} (hP : IsMarkov P) {θ : ℝ} (hθ : θ ≠ 0)
    (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GloballyStable (koopmans (additive r β) (entR θ P)) :=
  globallyStable_koopmans (isBlackwellAgg_additive r hβ0 hβ1)
    (fun _ _ _ hyz => by simp only [additive]; nlinarith) (isCertEquiv_entR hθ hP)
    (constSubadditive_entR hθ hP)

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 7.3.18 (p. 240): with the Leontief aggregator, `0 ≤ β < 1`, and a constant-subadditive
certainty equivalent on `ℝ^X`, `K = A_MIN ∘ R` is globally stable. -/
theorem globallyStable_leontief [Finite X] (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {R : (X → ℝ) → (X → ℝ)} (hR : IsCertEquiv R Set.univ) (hc : ConstSubadditive R Set.univ) :
    GloballyStable (koopmans (leontief r β) R) :=
  globallyStable_koopmans (isBlackwellAgg_leontief r hβ0 hβ1)
    (fun _ _ _ hyz => min_le_min le_rfl (mul_le_mul_of_nonneg_left hyz hβ0)) hR hc

omit [DecidableEq X] in
/-- Quantile preferences (7.20) (p. 241): for `0 ≤ β < 1` and `τ ∈ (0, 1]`, `K_τ = A_ADD ∘ R_τ` is
globally stable on `ℝ^X`. -/
theorem globallyStable_quantile {P : Matrix X X ℝ} (hP : IsMarkov P) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GloballyStable (koopmans (additive r β) (quantR τ P)) :=
  globallyStable_koopmans (isBlackwellAgg_additive r hβ0 hβ1)
    (fun _ _ _ hyz => by simp only [additive]; nlinarith) (isCertEquiv_quantR hτ0 hτ1 hP)
    (constSubadditive_quantR hτ0 hτ1 hP)

omit [DecidableEq X] in
/-- Exercise 7.3.19 (p. 241): `A_MIN ∘ R_τ` is globally stable on `ℝ^X`. -/
theorem globallyStable_leontief_quantile {P : Matrix X X ℝ} (hP : IsMarkov P) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GloballyStable (koopmans (leontief r β) (quantR τ P)) :=
  globallyStable_leontief r hβ0 hβ1 (isCertEquiv_quantR hτ0 hτ1 hP)
    (constSubadditive_quantR hτ0 hτ1 hP)

/-! ### Uzawa aggregation (§7.3.3) -/

omit [Nonempty X] [DecidableEq X] in
/-- With `R = P`, the Uzawa Koopmans operator is `Kv = r + Lv`, `L(x, x') = b(x)P(x, x')`
(§7.3.3.1). -/
theorem koopmans_uzawa_mulVec (r b : X → ℝ) (P : Matrix X X ℝ) (v : X → ℝ) :
    koopmans (uzawa r b) (fun v => P *ᵥ v) v =
      affineOp (Matrix.of fun x x' => b x * P x x') r v := by
  classical
  funext x
  simp only [koopmans, uzawa, affineOp, Pi.add_apply, mulVec, dotProduct, Matrix.of_apply,
    mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- §7.3.3.1 (p. 241): if `ρ(L) < 1` the Uzawa Koopmans operator with conditional expectations is
globally stable on `ℝ^X`, and its fixed point is the lifetime value (7.22),
`(I − L)⁻¹r = ∑ₜ Lᵗr`. -/
theorem uzawa_lifetimeValue (r b : X → ℝ) (P : Matrix X X ℝ)
    (hρ : specRad (Matrix.of fun x x' => b x * P x x') < 1) :
    GloballyStable (koopmans (uzawa r b) fun v => P *ᵥ v) ∧
      IsFixedPt (koopmans (uzawa r b) fun v => P *ᵥ v)
        ((1 - Matrix.of fun x x' => b x * P x x')⁻¹ *ᵥ r) ∧
      (1 - Matrix.of fun x x' => b x * P x x')⁻¹ *ᵥ r =
        ∑' t : ℕ, (Matrix.of fun x x' => b x * P x x') ^ t *ᵥ r := by
  have hK : (koopmans (uzawa r b) fun v => P *ᵥ v) =
      affineOp (Matrix.of fun x x' => b x * P x x') r :=
    funext (koopmans_uzawa_mulVec r b P)
  rw [hK]
  exact ⟨globallyStable_affineOp hρ r, isFixedPt_affineOp_inv hρ r, inv_mulVec_eq_tsum hρ r⟩

omit [Nonempty X] in
/-- Exercise 7.3.20 (p. 242): `L(x, x') = b(x)P(x, x')` is irreducible when `b ≫ 0` and `P` is
irreducible. -/
theorem irreducible_uzawa {b : X → ℝ} (hb : ∀ x, 0 < b x) {P : Matrix X X ℝ}
    (hP : Irreducible P) : Irreducible (Matrix.of fun x x' => b x * P x x') :=
  hP.of_pos_mul (c := fun x _ => b x) fun x _ => hb x

/-- §7.3.3.1 (p. 242): if `b ≫ 0`, `P` is irreducible, `r ≫ 0` and `ρ(L) ≥ 1`, then `Kv = r + Lv`
has no fixed point in `(0, ∞)^X`, by Lemma 6.1.4 (here via Theorem 7.1.4 with `θ = 1`). -/
theorem uzawa_no_pos_fixedPt {b : X → ℝ} (hb : ∀ x, 0 < b x) {P : Matrix X X ℝ}
    (hP : Irreducible P) {r : X → ℝ} (hr : ∀ x, 0 < r x)
    (hρ : 1 ≤ specRad (Matrix.of fun x x' => b x * P x x')) {v : X → ℝ} (hv : v ∈ posCone X) :
    ¬ IsFixedPt (koopmans (uzawa r b) fun v => P *ᵥ v) v := by
  intro hfix
  have hL := irreducible_uzawa hb hP
  have hAv := mulVec_pos_of_row hL.1 hL.exists_pos_row hv
  have hG : IsFixedPt (powG (Matrix.of fun x x' => b x * P x x') r 1) v := by
    funext x
    have h1 := congrFun hfix x
    rw [koopmans_uzawa_mulVec] at h1
    simp only [powG_apply, inv_one, Real.rpow_one]
    rw [← h1, affineOp, Pi.add_apply, add_comm]
  have := specRad_rpow_lt_one_of_isFixedPt hL hr one_ne_zero hv hG
  rw [inv_one, Real.rpow_one] at this
  linarith

/-- The nonnegative cone `ℝ^X₊`. -/
def nonnegCone (X : Type*) : Set (X → ℝ) := {v | ∀ x, 0 ≤ v x}

/-- **Proposition 7.3.4** (p. 242): let `Kv = r + b ⊙ Rv` with `b ≥ 0`, `r ≫ 0` and `R` a concave
certainty equivalent on `ℝ^X₊`. If `b ⊙ Rv ≤ c + Lv` on `ℝ^X₊` for some `c` and some `L ≥ 0` with
`ρ(L) < 1`, then `K` is globally stable on `[0, v̄]`, `v̄ = (I − L)⁻¹(r + c)`. -/
theorem globallyStableOn_uzawa_concave {R : (X → ℝ) → (X → ℝ)}
    (hR : IsCertEquiv R (nonnegCone X)) (hRc : ConcaveOn ℝ (nonnegCone X) R) {b r c : X → ℝ}
    (hb : ∀ x, 0 ≤ b x) (hr : ∀ x, 0 < r x) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (ha : ∀ v ∈ nonnegCone X, ∀ x, b x * R v x ≤ c x + (L *ᵥ v) x) :
    GloballyStableOn (koopmans (uzawa r b) R) (Set.Icc 0 ((1 - L)⁻¹ *ᵥ (r + c))) := by
  set vbar := (1 - L)⁻¹ *ᵥ (r + c) with hvbar
  have h0 : (0 : X → ℝ) ∈ nonnegCone X := fun _ => le_rfl
  have hR0 : R 0 = 0 := hR.const 0 h0
  -- `c ≥ 0`, from (a) at `v = 0`
  have hc : ∀ x, 0 ≤ c x := fun x => by
    have := ha 0 h0 x
    rw [hR0, mulVec_zero] at this
    simpa using this
  have hvbar_eq : vbar = (r + c) + L *ᵥ vbar := inv_mulVec_eq_add hρ (r + c)
  have hvbar0 : ∀ x, 0 ≤ vbar x := fun x => by
    rw [hvbar, inv_mulVec_eq_tsum hρ, Pi.tsum_apply (summable_pow_mulVec hρ _)]
    exact tsum_nonneg fun t => sum_nonneg fun x' _ =>
      mul_nonneg (pow_nonneg_entries hL t x x') (add_nonneg (hr x').le (hc x'))
  have hsub : Set.Icc (0 : X → ℝ) vbar ⊆ nonnegCone X := fun z hz x => hz.1 x
  have hvbarmem : vbar ∈ nonnegCone X := hvbar0
  have hmono : MonotoneOn (koopmans (uzawa r b) R) (nonnegCone X) := fun u hu w hw huw x =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (hR.mono u hu w hw huw x) (hb x))
  have hK0 : koopmans (uzawa r b) R 0 = r := by
    funext x
    simp [koopmans, uzawa, hR0]
  have hKbar : koopmans (uzawa r b) R vbar ≤ vbar := fun x => by
    have h1 := ha vbar hvbarmem x
    have h2 := congrFun hvbar_eq x
    simp only [Pi.add_apply] at h2
    change r x + b x * R vbar x ≤ vbar x
    linarith
  have hmaps : MapsTo (koopmans (uzawa r b) R) (Set.Icc 0 vbar) (Set.Icc 0 vbar) := by
    intro z hz
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := hmono h0 (hsub hz) hz.1 x
      rw [hK0] at this
      exact (hr x).le.trans this
    · exact (hmono (hsub hz) hvbarmem hz.2 x).trans (hKbar x)
  have hconc : ConcaveOn ℝ (Set.Icc 0 vbar) (koopmans (uzawa r b) R) := by
    refine ⟨convex_Icc _ _, fun u hu w hw a a' ha ha' haa' x => ?_⟩
    have h1 := hRc.2 (hsub hu) (hsub hw) ha ha' haa' x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [koopmans, uzawa, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h2 := mul_le_mul_of_nonneg_left h1 (hb x)
    have h3 : a * r x + a' * r x = r x := by rw [← add_mul, haa', one_mul]
    nlinarith
  refine du_concave_of_lt (v₁ := 0) (fun x => hvbar0 x) hmaps (hmono.mono hsub) hconc fun x => ?_
  rw [hK0]
  exact hr x

end SargentStachurski.NonlinearValuation
