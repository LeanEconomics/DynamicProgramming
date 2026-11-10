/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.POPareto
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Time 0 trading

Miao, §13.3, pp. 418–424: Arrow–Debreu state prices, equilibrium, first-order conditions, risk
sharing, the Negishi method, the two welfare theorems and asset pricing.

* `po_cost q x = Σ_{t, sᵗ} q⁰_t(sᵗ) x_t(sᵗ)`; it is well defined for `q ∈ L¹`, `x ∈ L∞`
  (`eq_13_5`). `po_ADEquilibrium E y q c` is Definition 13.3.1.
* (13.6) (`eq_13_6`) is derived by moving consumption between a node and the root along the
  budget line; the multiplier is `μᵢ = uⁱ'(cⁱ₀(s₀))` under `q⁰₀(s₀) = 1`. (13.7)–(13.10)
  (`eq_13_7`–`eq_13_10`) follow. The equilibrium allocation solves the planner's problem with
  `λᵢ = μᵢ⁻¹` (`po_AD_solves_planner`), and the planner's shadow prices are `q⁰`
  (`po_AD_shadow_price`). The text omits that these need interior consumption,
  differentiability, and (for (13.8)–(13.10)) nodes of positive probability.
* Example 13.3.1 (`example_13_3_1`, `example_13_3_1_shares`, marginal utility `po_crra_hasDerivAt`).
  The printed `c^{1−γ}/(1−γ)` needs `γ ≠ 1`; the computation uses only `u'(c) = c^{−γ}`, which
  covers `γ = 1` (log utility) as well.
* The Negishi algorithm: scale invariance (`po_negishi_scale`), `q⁰₀(s₀) = 1` iff
  `μ₁ = u¹'(c¹₀(s₀))` (`po_negishi_q0`), the direction of step 3 (`po_negishi_step3`) and the
  fact that a stopping point is an equilibrium (`po_negishi_fixed_point`). Convergence of the
  iteration (step 4) is not claimed by the text and not formalised.
* **Theorem 13.3.1** (`theorem_13_3_1`): First Welfare Theorem, under strict monotonicity only.
* **Theorem 13.3.2** (`theorem_13_3_2`): Second Welfare Theorem. Correction: as printed (with the
  economy's endowments) it is false (`theorem_13_3_2_counterexample`); it holds with the
  endowments relocated to the allocation (equivalently, after lump-sum transfers). The proof here
  is not the book's Hahn–Banach/Yosida–Hewitt outline: under differentiability and uniformly
  interior consumption, the planner's first-order conditions give the prices directly, and they
  lie in `L¹`. Strict concavity is not needed.
* Asset pricing: `po_assetPrice` (pp. 423–424), well defined for `q ∈ L¹` and `d ∈ L∞`
  (`po_assetPrice_summable`), at the root (`po_assetPrice_root`) and with (13.7) substituted
  (`po_assetPrice_eq`).
-/

namespace Miao.CompleteMarkets

open Filter Topology

/-- Miao, (13.5), p. 419: the value `Σ_t Σ_{sᵗ} q⁰_t(sᵗ) x_t(sᵗ)` of a plan `x` at the
Arrow–Debreu state prices `q⁰`. -/
noncomputable def po_cost {S : Type*} (q x : List S → ℝ) : ℝ :=
  ∑' h, q h * x h

/-- Miao, (13.5), p. 419 ("For this budget constraint to be well-defined, we need `q⁰` to be in
`L¹`"): for `q ∈ L¹` and `x ∈ L∞` the series `Σ q⁰_t(sᵗ) x_t(sᵗ)` converges absolutely. -/
theorem eq_13_5 {S : Type*} {q x : List S → ℝ} (hq : q ∈ po_L1 S) (hx : x ∈ po_Linfty S) :
    Summable fun h => q h * x h := by
  obtain ⟨B, hB⟩ := hx
  refine Summable.of_norm_bounded ((show Summable fun h => |q h| from hq).mul_right B)
    fun h => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB ⟨h, rfl⟩) (abs_nonneg _)

/-- **Definition 13.3.1** (Miao, p. 419). An Arrow–Debreu equilibrium: state prices `q⁰ ∈ L¹`
and a feasible allocation `c ∈ (L∞₊)ᴵ` such that each `cⁱ` maximises `Uⁱ` over the plans in
`L∞₊` satisfying the budget constraint (13.5) at the endowment `yⁱ`. -/
def po_ADEquilibrium {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (y : ι → List S → ℝ) (q : List S → ℝ) (c : ι → List S → ℝ) : Prop :=
  q ∈ po_L1 S ∧ po_Feasible y c ∧ ∀ i, po_cost q (c i) ≤ po_cost q (y i) ∧
    ∀ x ∈ po_Lplus S, po_cost q x ≤ po_cost q (y i) → po_U E i x ≤ po_U E i (c i)

/-- Miao, (13.5): changing a plan at one node changes its value by the price times the change. -/
theorem po_cost_update {S : Type*} [DecidableEq S] {q x : List S → ℝ} (hq : q ∈ po_L1 S)
    (hx : x ∈ po_Linfty S) (h : List S) (v : ℝ) :
    po_cost q (Function.update x h v) = po_cost q x + q h * (v - x h) := by
  unfold po_cost
  have : (fun k => q k * Function.update x h v k) =
      Function.update (fun k => q k * x k) h (q h * v) := by
    funext k
    by_cases hk : k = h
    · subst hk; simp
    · simp [hk]
  rw [this, po_tsum_update _ (eq_13_5 hq hx)]
  ring

/-- Miao, (13.5) and (13.2): the values of the agents' plans add up to the value of the sum. -/
theorem po_sum_cost {ι S : Type*} [Fintype ι] {q : List S → ℝ} (hq : q ∈ po_L1 S)
    {x : ι → List S → ℝ} (hx : ∀ i, x i ∈ po_Linfty S) :
    ∑ i, po_cost q (x i) = po_cost q (fun h => ∑ i, x i h) := by
  unfold po_cost
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun i _ => eq_13_5 hq (hx i)]

/-- The tangent-line inequality for a concave felicity function:
`u(x) ≤ u(c) + u'(c)(x − c)` for `c > 0`, `x ≥ 0`. -/
theorem po_tangent {u : ℝ → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u) {c x : ℝ} (hc : 0 < c)
    (hx : 0 ≤ x) (hd : DifferentiableAt ℝ u c) : u x ≤ u c + deriv u c * (x - c) := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · have := hconc.deriv_le_slope (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hc.le) hlt hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst heq; simp
  · have := hconc.slope_le_deriv (Set.mem_Ici.mpr hc.le) (Set.mem_Ici.mpr hx) hgt hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith

/-- Miao, §13.3: a concave felicity function, strictly increasing on `[0, ∞)`, has positive
marginal utility at every positive consumption level where it is differentiable. -/
theorem po_deriv_pos {u : ℝ → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : StrictMonoOn u (Set.Ici 0)) {x : ℝ} (hx : 0 < x) (hd : DifferentiableAt ℝ u x) :
    0 < deriv u x := by
  have h1 := po_tangent hconc hx (by linarith : (0 : ℝ) ≤ x + 1) hd
  have h2 : u x < u (x + 1) :=
    hmono (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  nlinarith

/-- Miao, §13.3, the sufficiency of the first-order conditions: if `uⁱ` is concave, `cⁱ` is
interior, and `βᵗ Pr(sᵗ) uⁱ'(cⁱ_t(sᵗ)) = μ q⁰_t(sᵗ)` at every node (13.6), then for every
`x ∈ L∞₊`, `Uⁱ(x) − Uⁱ(cⁱ) ≤ μ (q⁰ · x − q⁰ · cⁱ)`. -/
theorem po_utility_gain_le {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.u i)) {c : List S → ℝ} (hc : c ∈ po_Lplus S)
    (hpos : ∀ h, 0 < c h) (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c h)) {q : List S → ℝ}
    (hq : q ∈ po_L1 S) (μ : ℝ) (hfoc : ∀ h, po_w E h * deriv (E.u i) (c h) = μ * q h)
    {x : List S → ℝ} (hx : x ∈ po_Lplus S) :
    po_U E i x - po_U E i c ≤ μ * (po_cost q x - po_cost q c) := by
  unfold po_U po_cost
  have hsx := eq_13_5 hq (po_Lplus_subset_Linfty hx)
  have hsc := eq_13_5 hq (po_Lplus_subset_Linfty hc)
  rw [← (eq_13_1 E i hx).tsum_sub (eq_13_1 E i hc), ← hsx.tsum_sub hsc, ← tsum_mul_left]
  refine ((eq_13_1 E i hx).sub (eq_13_1 E i hc)).tsum_le_tsum (fun h => ?_)
    ((hsx.sub hsc).mul_left μ)
  have ht := po_tangent hconc (hpos h) (hx.1 h) (hdiff h)
  have hw := po_w_nonneg E h
  have : po_w E h * E.u i (x h) ≤ po_w E h * (E.u i (c h) + deriv (E.u i) (c h) * (x h - c h)) :=
    mul_le_mul_of_nonneg_left ht hw
  have e : po_w E h * (deriv (E.u i) (c h) * (x h - c h)) = μ * (q h * x h - q h * c h) := by
    rw [← mul_assoc, hfoc h]; ring
  nlinarith

/-- Miao, §13.3: an interior plan satisfying (13.6) with `μ ≥ 0` and an exactly binding budget
constraint maximises `Uⁱ` over the budget set (the first-order conditions are sufficient). -/
theorem po_optimal_of_foc {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.u i)) {c y : List S → ℝ} (hc : c ∈ po_Lplus S)
    (hpos : ∀ h, 0 < c h) (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c h)) {q : List S → ℝ}
    (hq : q ∈ po_L1 S) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfoc : ∀ h, po_w E h * deriv (E.u i) (c h) = μ * q h) (hbud : po_cost q c = po_cost q y)
    {x : List S → ℝ} (hx : x ∈ po_Lplus S) (hxb : po_cost q x ≤ po_cost q y) :
    po_U E i x ≤ po_U E i c := by
  have := po_utility_gain_le E i hconc hc hpos hdiff hq μ hfoc hx
  have : μ * (po_cost q x - po_cost q c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hμ (by linarith)
  linarith

/-- Miao, (13.6), p. 419. At an Arrow–Debreu equilibrium with `q⁰₀(s₀) = 1`, if agent `i`'s
consumption is interior and `uⁱ` is differentiable there, then
`βᵗ uⁱ'(cⁱ_t(sᵗ)) Pr(sᵗ) = μᵢ q⁰_t(sᵗ)` at every node, with `μᵢ = uⁱ'(cⁱ₀(s₀))` (the text's "by
normalization"). Derived by buying `ε` more units at `sᵗ` and `ε q⁰_t(sᵗ)` fewer at `s₀`, which
leaves the budget unchanged; utility is maximal at `ε = 0`. -/
theorem eq_13_6 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (i : ι) (hpos : ∀ h, 0 < c i h)
    (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c i h)) (h : List S) :
    po_w E h * deriv (E.u i) (c i h) = deriv (E.u i) (c i []) * q h := by
  classical
  by_cases hh : h = []
  · subst hh; rw [po_w_root, hq0]; ring
  obtain ⟨hq, hfeas, hopt⟩ := hE
  set a := c i h
  set b := c i []
  set φ : ℝ → ℝ := fun e => po_w E h * E.u i (a + e) + E.u i (b - e * q h) with hφ
  have hci := hfeas.1 i
  have hmax : IsLocalMax φ 0 := by
    have hr : 0 < min a (b / (|q h| + 1)) := lt_min (hpos h) (by
      have := hpos []; positivity)
    filter_upwards [Ioo_mem_nhds (neg_neg_iff_pos.mpr hr) hr] with e he
    obtain ⟨he1, he2⟩ := he
    have hea : |e| < a := (abs_lt.mpr ⟨he1, he2⟩).trans_le (min_le_left _ _)
    have heb : |e| < b / (|q h| + 1) := (abs_lt.mpr ⟨he1, he2⟩).trans_le (min_le_right _ _)
    have hnn1 : 0 ≤ a + e := by linarith [neg_abs_le e]
    have hnn2 : 0 ≤ b - e * q h := by
      have h1 : |e * q h| ≤ |e| * (|q h| + 1) := by
        rw [abs_mul]; nlinarith [abs_nonneg e, abs_nonneg (q h)]
      have h2 : |e| * (|q h| + 1) < b := (lt_div_iff₀ (by positivity)).mp heb
      linarith [le_abs_self (e * q h)]
    set x1 := Function.update (c i) h (a + e)
    have hx1 : x1 ∈ po_Lplus S := po_update_mem hci h hnn1
    set x2 := Function.update x1 [] (b - e * q h)
    have hx2 : x2 ∈ po_Lplus S := po_update_mem hx1 [] hnn2
    have hx1r : x1 [] = b := by simp [x1, Ne.symm hh, b]
    have hcost : po_cost q x2 = po_cost q (c i) := by
      simp only [x2, x1]
      rw [po_cost_update hq (po_Lplus_subset_Linfty hx1), hx1r,
        po_cost_update hq (po_Lplus_subset_Linfty hci), hq0]
      ring
    have hU := (hopt i).2 x2 hx2 (hcost ▸ (hopt i).1)
    simp only [x2] at hU
    rw [po_U_update E i hx1, hx1r, po_U_update E i hci, po_w_root] at hU
    simp only [hφ, add_zero, zero_mul, sub_zero]
    linarith
  have hderiv : HasDerivAt φ (po_w E h * deriv (E.u i) a - q h * deriv (E.u i) b) 0 := by
    have h1 : HasDerivAt (fun e => E.u i (a + e)) (deriv (E.u i) a) 0 :=
      HasDerivAt.comp_const_add a 0 (by simpa using (hdiff h).hasDerivAt)
    have hl : HasDerivAt (fun e : ℝ => b - e * q h) (-q h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (q h)).const_sub b
    have h2 : HasDerivAt (fun e => E.u i (b - e * q h)) (deriv (E.u i) b * -q h) 0 := by
      have hb : HasDerivAt (E.u i) (deriv (E.u i) b) (b - 0 * q h) := by
        simpa using (hdiff []).hasDerivAt
      exact hb.comp 0 hl
    have := (h1.const_mul (po_w E h)).add h2
    convert this using 1
    ring
  have := hmax.hasDerivAt_eq_zero hderiv
  linarith

/-- Miao, (13.7), p. 419: the Arrow–Debreu state price
`q⁰_t(sᵗ) = βᵗ uⁱ'(cⁱ_t(sᵗ)) Pr(sᵗ) / uⁱ'(cⁱ₀(s₀))`. -/
theorem eq_13_7 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (i : ι) (hpos : ∀ h, 0 < c i h)
    (hdiff : ∀ h, DifferentiableAt ℝ (E.u i) (c i h)) (hμ : deriv (E.u i) (c i []) ≠ 0)
    (h : List S) :
    q h = E.β ^ h.length * deriv (E.u i) (c i h) * E.P.pr h / deriv (E.u i) (c i []) := by
  have := eq_13_6 E hE hq0 i hpos hdiff h
  unfold po_w at this
  field_simp
  linarith

/-- Miao, (13.8), p. 419: at a node of positive probability,
`uⁱ'(cⁱ_t(sᵗ)) μⱼ = uʲ'(cʲ_t(sᵗ)) μᵢ`, i.e. `uⁱ'(cⁱ_t) / uʲ'(cʲ_t) = μᵢ / μⱼ`, with
`μᵢ = uⁱ'(cⁱ₀(s₀))`. -/
theorem eq_13_8 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {h : List S} (hw : 0 < po_w E h)
    (i j : ι) :
    deriv (E.u i) (c i h) * deriv (E.u j) (c j []) =
        deriv (E.u j) (c j h) * deriv (E.u i) (c i []) ∧
      (deriv (E.u j) (c j h) ≠ 0 → deriv (E.u j) (c j []) ≠ 0 →
        deriv (E.u i) (c i h) / deriv (E.u j) (c j h) =
          deriv (E.u i) (c i []) / deriv (E.u j) (c j [])) := by
  have hi := eq_13_6 E hE hq0 i (hpos i) (hdiff i) h
  have hj := eq_13_6 E hE hq0 j (hpos j) (hdiff j) h
  have key : deriv (E.u i) (c i h) * deriv (E.u j) (c j []) =
      deriv (E.u j) (c j h) * deriv (E.u i) (c i []) := by
    have : po_w E h * (deriv (E.u i) (c i h) * deriv (E.u j) (c j [])) =
        po_w E h * (deriv (E.u j) (c j h) * deriv (E.u i) (c i [])) := by
      rw [← mul_assoc, hi, ← mul_assoc, hj]; ring
    exact mul_left_cancel₀ hw.ne' this
  refine ⟨key, fun h1 h2 => ?_⟩
  rw [div_eq_div_iff h1 h2]
  linarith

/-- Miao, (13.9), p. 419: `cⁱ_t(sᵗ) = (uⁱ')⁻¹(u¹'(c¹_t(sᵗ)) μᵢ / μ₁)` at nodes of positive
probability, `(uⁱ')⁻¹` the inverse of the marginal utility on `(0, ∞)`. -/
theorem eq_13_9 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) {h : List S} (hw : 0 < po_w E h)
    (i i₁ : ι) (hμ₁ : deriv (E.u i₁) (c i₁ []) ≠ 0) :
    c i h = Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
      (deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ []))) := by
  have key := (eq_13_8 E hE hq0 hpos hdiff hw i i₁).1
  have h1 : deriv (E.u i) (c i h) =
      deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ [])) := by
    field_simp
    linarith
  have hex : ∃ a ∈ Set.Ioi (0 : ℝ), deriv (E.u i) a =
      deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ [])) :=
    ⟨c i h, hpos i h, h1⟩
  exact hinj i (hpos i h) (Function.invFunOn_mem hex) (h1.trans (Function.invFunOn_eq hex).symm)

/-- Miao, (13.10), p. 419: by feasibility,
`Σᵢ (uⁱ')⁻¹(u¹'(c¹_t(sᵗ)) μᵢ / μ₁) = Σᵢ yⁱ_t(sᵗ)`, the analogue of (13.4) with `λᵢ = μᵢ⁻¹`. -/
theorem eq_13_10 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h))
    (hinj : ∀ k, Set.InjOn (deriv (E.u k)) (Set.Ioi 0)) {h : List S} (hw : 0 < po_w E h)
    (i₁ : ι) (hμ₁ : deriv (E.u i₁) (c i₁ []) ≠ 0) :
    ∑ i, Function.invFunOn (deriv (E.u i)) (Set.Ioi 0)
      (deriv (E.u i₁) (c i₁ h) * (deriv (E.u i) (c i []) / deriv (E.u i₁) (c i₁ []))) =
        ∑ i, y i h := by
  rw [← hE.2.1.2 h]
  exact Finset.sum_congr rfl fun i _ => (eq_13_9 E hE hq0 hpos hdiff hinj hw i i₁ hμ₁).symm

/-- Miao, p. 420 ("the shadow prices `ξ_t(sᵗ)` for the associated planning problem … equal the
Arrow–Debreu state prices"): with `λᵢ = μᵢ⁻¹`, `λᵢ βᵗ Pr(sᵗ) uⁱ'(cⁱ_t(sᵗ)) = q⁰_t(sᵗ)` for every
agent and node, so the planner's multiplier on (13.2) at `sᵗ` is `q⁰_t(sᵗ)`. -/
theorem po_AD_shadow_price {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) (hμ : ∀ i, deriv (E.u i) (c i []) ≠ 0)
    (i : ι) (h : List S) :
    (deriv (E.u i) (c i []))⁻¹ * (po_w E h * deriv (E.u i) (c i h)) = q h := by
  rw [eq_13_6 E hE hq0 i (hpos i) (hdiff i) h, ← mul_assoc, inv_mul_cancel₀ (hμ i), one_mul]

/-- Miao, §13.2–13.3: sufficiency for the planner's problem. If `c` is feasible and interior,
each `uⁱ` is concave, and `λᵢ βᵗ Pr(sᵗ) uⁱ'(cⁱ_t(sᵗ)) = ξ_t(sᵗ)` for all `i` and nodes, with
`λ > 0` and `ξ ∈ L¹`, then `c` solves the planner's problem with weights `λ`. -/
theorem po_planner_of_foc {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y c : ι → List S → ℝ}
    (hc : po_Feasible y c) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    {ξ : List S → ℝ} (hξ : ξ ∈ po_L1 S)
    (hfoc : ∀ i h, lam i * (po_w E h * deriv (E.u i) (c i h)) = ξ h) :
    po_SolvesPlanner E y lam c := by
  refine ⟨hc, fun d hd => ?_⟩
  have hgain : ∀ i, lam i * po_U E i (d i) - lam i * po_U E i (c i) ≤
      po_cost ξ (d i) - po_cost ξ (c i) := by
    intro i
    have hf : ∀ h, po_w E h * deriv (E.u i) (c i h) = (lam i)⁻¹ * ξ h := by
      intro h
      rw [← hfoc i h, ← mul_assoc, inv_mul_cancel₀ (hlam i).ne', one_mul]
    have := po_utility_gain_le E i (hconc i) (hc.1 i) (hpos i) (hdiff i) hξ _ hf (hd.1 i)
    have := mul_le_mul_of_nonneg_left this (hlam i).le
    rw [← mul_assoc, mul_inv_cancel₀ (hlam i).ne', one_mul] at this
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hgain i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    po_sum_cost hξ fun i => po_Lplus_subset_Linfty (hd.1 i),
    po_sum_cost hξ fun i => po_Lplus_subset_Linfty (hc.1 i)] at hsum
  have : (fun h => ∑ i, d i h) = fun h => ∑ i, c i h := funext fun h => by rw [hd.2, hc.2]
  rw [this, sub_self] at hsum
  linarith

/-- Miao, p. 419 ("an Arrow–Debreu equilibrium allocation is a particular Pareto optimal
allocation, one that sets the Pareto weights `λᵢ = μᵢ⁻¹`"): an interior equilibrium allocation
with concave felicity functions solves the planner's problem with `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹`. -/
theorem po_AD_solves_planner {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y : ι → List S → ℝ} {q : List S → ℝ}
    {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c) (hq0 : q [] = 1)
    (hpos : ∀ i h, 0 < c i h) (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) :
    po_SolvesPlanner E y (fun i => (deriv (E.u i) (c i []))⁻¹) c := by
  have hμ : ∀ i, 0 < deriv (E.u i) (c i []) := fun i =>
    po_deriv_pos (hconc i) (E.u_mono i) (hpos i []) (hdiff i [])
  exact po_planner_of_foc E hconc hE.2.1 hpos hdiff (fun i => inv_pos.mpr (hμ i)) hE.1
    fun i h => po_AD_shadow_price E hE hq0 hpos hdiff (fun k => (hμ k).ne') i h

/-- Miao, Example 13.3.1: with `u(c) = c^{1−γ}/(1−γ)` (`γ > 0`, `γ ≠ 1`), marginal utility is
`u'(c) = c^{−γ}`. -/
theorem po_crra_hasDerivAt {γ : ℝ} (hγ : γ ≠ 1) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun x : ℝ => x ^ (1 - γ) / (1 - γ)) (c ^ (-γ)) c := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  convert this using 1
  rw [show (1 : ℝ) - γ - 1 = -γ by ring]
  field_simp

/-- **Example 13.3.1** (Risk sharing, Miao, p. 420). With CRRA marginal utility `c^{−γ}`,
`γ > 0`, the first-order condition (13.8) `(cⁱ)^{−γ} μⱼ = (cʲ)^{−γ} μᵢ` gives
`cⁱ = cʲ (μᵢ/μⱼ)^{−1/γ}` (consumption is perfectly correlated), and with `Σᵢ cⁱ = ȳ`,
`cⁱ = μᵢ^{−1/γ} / Σⱼ μⱼ^{−1/γ} · ȳ` (a constant share of the aggregate endowment). -/
theorem example_13_3_1 {ι : Type*} [Fintype ι] {γ : ℝ} (hγ : 0 < γ) {μ c : ι → ℝ}
    (hμ : ∀ i, 0 < μ i) (hc : ∀ i, 0 < c i)
    (hfoc : ∀ i j, c i ^ (-γ) * μ j = c j ^ (-γ) * μ i) {Y : ℝ} (hY : ∑ i, c i = Y) :
    (∀ i j, c i = c j * (μ i / μ j) ^ (-1 / γ)) ∧
      ∀ i, c i = μ i ^ (-1 / γ) / (∑ j, μ j ^ (-1 / γ)) * Y := by
  have hpow : ∀ x : ℝ, 0 < x → (x ^ (-γ)) ^ (-1 / γ) = x := by
    intro x hx
    rw [← Real.rpow_mul hx.le, show -γ * (-1 / γ) = 1 by field_simp, Real.rpow_one]
  have h1 : ∀ i j, c i = c j * (μ i / μ j) ^ (-1 / γ) := by
    intro i j
    have e : c i ^ (-γ) = c j ^ (-γ) * (μ i / μ j) := by
      field_simp [(hμ j).ne']
      linarith [hfoc i j]
    have := congrArg (fun z => z ^ (-1 / γ)) e
    rw [hpow _ (hc i), Real.mul_rpow (Real.rpow_nonneg (hc j).le _)
      (div_pos (hμ i) (hμ j)).le, hpow _ (hc j)] at this
    exact this
  refine ⟨h1, fun i => ?_⟩
  have hm : ∀ j, 0 < μ j ^ (-1 / γ) := fun j => Real.rpow_pos_of_pos (hμ j) _
  have hK : ∀ j, c j = c i / μ i ^ (-1 / γ) * μ j ^ (-1 / γ) := by
    intro j
    rw [h1 j i, Real.div_rpow (hμ j).le (hμ i).le]
    field_simp [(hm i).ne']
  have hsum : Y = c i / μ i ^ (-1 / γ) * ∑ j, μ j ^ (-1 / γ) := by
    rw [← hY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hK j
  have hpos : 0 < ∑ j, μ j ^ (-1 / γ) :=
    Finset.sum_pos (fun j _ => hm j) ⟨i, Finset.mem_univ _⟩
  have hmi := (hm i).ne'
  have hT := hpos.ne'
  set M := μ i ^ (-1 / γ)
  set T := ∑ j, μ j ^ (-1 / γ)
  rw [hsum]
  field_simp

/-- Miao, Example 13.3.1, p. 420, in the economy: at an Arrow–Debreu equilibrium with
`q⁰₀(s₀) = 1`, interior consumption and CRRA marginal utility `uⁱ'(c) = c^{−γ}` for all agents,
every agent consumes the constant share `μᵢ^{−1/γ} / Σⱼ μⱼ^{−1/γ}` of the aggregate endowment at
every node of positive probability, with `μᵢ = (cⁱ₀(s₀))^{−γ}`. -/
theorem example_13_3_1_shares {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {γ : ℝ} (hγ : 0 < γ) (hu : ∀ i x, 0 < x → deriv (E.u i) x = x ^ (-γ))
    {y : ι → List S → ℝ} {q : List S → ℝ} {c : ι → List S → ℝ} (hE : po_ADEquilibrium E y q c)
    (hq0 : q [] = 1) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {h : List S} (hw : 0 < po_w E h)
    (i : ι) :
    c i h = (c i [] ^ (-γ)) ^ (-1 / γ) / (∑ j, (c j [] ^ (-γ)) ^ (-1 / γ)) * ∑ j, y j h := by
  have hfoc : ∀ i j, c i h ^ (-γ) * c j [] ^ (-γ) = c j h ^ (-γ) * c i [] ^ (-γ) := by
    intro i j
    have := (eq_13_8 E hE hq0 hpos hdiff hw i j).1
    rwa [hu i _ (hpos i h), hu j _ (hpos j []), hu j _ (hpos j h), hu i _ (hpos i [])] at this
  exact (example_13_3_1 hγ (fun j => Real.rpow_pos_of_pos (hpos j []) _) (fun j => hpos j h)
    hfoc (hE.2.1.2 h)).2 i

/-- Miao, p. 421 ("Multiplying all of the `μᵢ`'s by a positive scalar changes the scale of the
price system"): if `(μ, q⁰)` satisfy (13.6) then so do `(kμ, q⁰/k)`, and the right side of
(13.9) depends only on the ratios `μᵢ/μ₁`. -/
theorem po_negishi_scale {ι S : Type*} [Fintype S] (E : POEconomy ι S) {c : ι → List S → ℝ}
    {μ : ι → ℝ} {q : List S → ℝ}
    (hfoc : ∀ i h, po_w E h * deriv (E.u i) (c i h) = μ i * q h) {k : ℝ} (hk : k ≠ 0) :
    (∀ i h, po_w E h * deriv (E.u i) (c i h) = (k * μ i) * (q h / k)) ∧
      ∀ i i₁, k * μ i / (k * μ i₁) = μ i / μ i₁ := by
  refine ⟨fun i h => by rw [hfoc i h]; field_simp, fun i i₁ => ?_⟩
  rw [mul_div_mul_left _ _ hk]

/-- Miao, p. 421 ("According to the above algorithm, `q⁰₀(s₀) ≠ 1` in general"): by (13.6) at
the root, `q⁰₀(s₀) μ₁ = u¹'(c¹₀(s₀))`, so `q⁰₀(s₀) = 1` iff the fixed `μ₁` equals
`u¹'(c¹₀(s₀))`. -/
theorem po_negishi_q0 {ι S : Type*} [Fintype S] (E : POEconomy ι S) {c : ι → List S → ℝ}
    {μ : ι → ℝ} {q : List S → ℝ}
    (hfoc : ∀ i h, po_w E h * deriv (E.u i) (c i h) = μ i * q h) (i₁ : ι) (hμ : μ i₁ ≠ 0) :
    q [] = 1 ↔ μ i₁ = deriv (E.u i₁) (c i₁ []) := by
  have := hfoc i₁ []
  rw [po_w_root, one_mul] at this
  rw [this]
  constructor
  · intro h; rw [h, mul_one]
  · intro h
    exact mul_left_cancel₀ hμ (h.symm.trans (mul_one _).symm)

/-- Miao, p. 421, step 3 of the Negishi algorithm: given `u¹'(c¹_t(sᵗ)) = v > 0`, (13.9) sets
`uⁱ'(cⁱ_t(sᵗ)) = (μᵢ/μ₁) v`; with strictly decreasing marginal utility, raising `μᵢ` lowers
`cⁱ_t(sᵗ)` (and so the cost of agent `i`'s plan), which is why `μᵢ` is raised when cost exceeds
the value of the endowment. -/
theorem po_negishi_step3 {u : ℝ → ℝ} (hanti : StrictAntiOn (deriv u) (Set.Ioi 0)) {a b m m' v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hm : m < m') (hua : deriv u a = m * v)
    (hub : deriv u b = m' * v) : b < a := by
  have hlt : deriv u a < deriv u b := by
    rw [hua, hub]; exact mul_lt_mul_of_pos_right hm hv
  by_contra hge
  push Not at hge
  rcases hge.lt_or_eq with hab | hab
  · exact absurd (hanti ha hb hab) (not_lt.mpr hlt.le)
  · rw [hab] at hlt; exact lt_irrefl _ hlt

/-- Miao, p. 421, the Negishi algorithm at convergence: if the candidate allocation is feasible
and interior, the prices `q⁰ ∈ L¹` satisfy (13.6) for every agent with `μᵢ > 0`, the felicity
functions are concave, and every budget constraint (13.5) holds with equality, then `(c, q⁰)` is
an Arrow–Debreu equilibrium. -/
theorem po_negishi_fixed_point {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y c : ι → List S → ℝ}
    (hc : po_Feasible y c) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) {q : List S → ℝ} (hq : q ∈ po_L1 S)
    {μ : ι → ℝ} (hμ : ∀ i, 0 < μ i)
    (hfoc : ∀ i h, po_w E h * deriv (E.u i) (c i h) = μ i * q h)
    (hbud : ∀ i, po_cost q (c i) = po_cost q (y i)) : po_ADEquilibrium E y q c :=
  ⟨hq, hc, fun i => ⟨(hbud i).le, fun _ hx hxb =>
    po_optimal_of_foc E i (hconc i) (hc.1 i) (hpos i) (hdiff i) hq (hμ i).le (hfoc i) (hbud i)
      hx hxb⟩⟩

/-- Miao, proof of Theorem 13.3.1: local nonsatiation. If `x ∈ L∞₊` costs strictly less than the
endowment, a slightly larger plan at the root is still affordable and strictly better. -/
theorem po_local_nonsatiation {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    {q x : List S → ℝ} (hq : q ∈ po_L1 S) (hx : x ∈ po_Lplus S) {b : ℝ}
    (hlt : po_cost q x < b) :
    ∃ x' ∈ po_Lplus S, po_cost q x' ≤ b ∧ po_U E i x < po_U E i x' := by
  classical
  set ε := (b - po_cost q x) / (|q []| + 1)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hnn : 0 ≤ x [] + ε := by linarith [hx.1 []]
  refine ⟨Function.update x [] (x [] + ε), po_update_mem hx [] hnn, ?_, ?_⟩
  · rw [po_cost_update hq (po_Lplus_subset_Linfty hx), add_sub_cancel_left]
    have h1 : q [] * ε ≤ |q []| * ε := mul_le_mul_of_nonneg_right (le_abs_self _) hε.le
    have h2 : (|q []| + 1) * ε = b - po_cost q x := by
      simp only [ε]; field_simp
    nlinarith
  · rw [po_U_update E i hx, po_w_root, one_mul]
    have := E.u_mono i (Set.mem_Ici.mpr (hx.1 [])) (Set.mem_Ici.mpr hnn) (by linarith)
    linarith

/-- **Theorem 13.3.1** (First Welfare Theorem, Miao, p. 421). If each `uⁱ` is strictly
increasing and `(c, q⁰)` is an Arrow–Debreu equilibrium, then `c` is Pareto optimal. (The
endowments are in `L∞₊`, so that their values are defined.) -/
theorem theorem_13_3_1 {ι S : Type*} [Fintype ι] [Fintype S] (E : POEconomy ι S)
    {y : ι → List S → ℝ} (hy : ∀ i, y i ∈ po_Lplus S) {q : List S → ℝ} {c : ι → List S → ℝ}
    (hE : po_ADEquilibrium E y q c) : po_ParetoOptimal E y c := by
  obtain ⟨hq, hc, hopt⟩ := hE
  refine ⟨hc, ?_⟩
  rintro ⟨d, hd, hle, i₀, hlt⟩
  have hge : ∀ i, po_cost q (y i) ≤ po_cost q (d i) := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨x', hx', hx'b, hx'U⟩ := po_local_nonsatiation E i hq (hd.1 i) hcon
    have := (hopt i).2 x' hx' hx'b
    linarith [hle i]
  have hgt : po_cost q (y i₀) < po_cost q (d i₀) := by
    by_contra hcon
    push Not at hcon
    have := (hopt i₀).2 (d i₀) (hd.1 i₀) hcon
    linarith
  have hsum : ∑ i, po_cost q (y i) < ∑ i, po_cost q (d i) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i₀, Finset.mem_univ _, hgt⟩
  rw [po_sum_cost hq fun i => po_Lplus_subset_Linfty (hy i),
    po_sum_cost hq fun i => po_Lplus_subset_Linfty (hd.1 i)] at hsum
  have : (fun h => ∑ i, d i h) = fun h => ∑ i, y i h := funext hd.2
  rw [this] at hsum
  exact lt_irrefl _ hsum

/-- Miao, §13.2–13.3: a Pareto optimal interior allocation with concave, differentiable felicity
functions satisfies the planner's first-order conditions with strictly positive weights. -/
theorem po_pareto_foc {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i)) {y c : ι → List S → ℝ}
    (hpo : po_ParetoOptimal E y c) (hpos : ∀ i h, 0 < c i h)
    (hdiff : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h)) :
    ∃ lam : ι → ℝ, (∀ i, 0 < lam i) ∧ po_SolvesPlanner E y lam c ∧
      ∀ h, 0 < po_w E h → ∀ i j, lam i * deriv (E.u i) (c i h) = lam j * deriv (E.u j) (c j h) := by
  obtain ⟨lam, hlam, hne, hpl⟩ := po_planner_of_pareto E hconc hpo
  have hfoc : ∀ h, 0 < po_w E h → ∀ i j,
      lam i * deriv (E.u i) (c i h) = lam j * deriv (E.u j) (c j h) := fun h hw i j =>
    po_planner_foc_ratio E hpl h hw (fun k => hpos k h) (fun k => hdiff k h) i j
  obtain ⟨j, hj⟩ : ∃ j, lam j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hjpos : 0 < lam j := lt_of_le_of_ne (hlam j) (Ne.symm hj)
  refine ⟨lam, fun i => ?_, hpl, hfoc⟩
  have e := hfoc [] (by rw [po_w_root]; exact one_pos) i j
  have hdj := po_deriv_pos (hconc j) (E.u_mono j) (hpos j []) (hdiff j [])
  have hdi := po_deriv_pos (hconc i) (E.u_mono i) (hpos i []) (hdiff i [])
  rcases (hlam i).lt_or_eq with h | h
  · exact h
  · rw [← h, zero_mul] at e
    nlinarith

/-- **Theorem 13.3.2** (Second Welfare Theorem, Miao, p. 421), corrected. Let each `uⁱ` be
concave on `[0, ∞)` and differentiable on `(0, ∞)`, and let `c` be a Pareto optimal allocation
that is uniformly interior (`cⁱ_t(sᵗ) ≥ δ > 0`). Then there are state prices `q⁰ ∈ L¹` with
`q⁰₀(s₀) = 1` such that `(c, q⁰)` is an Arrow–Debreu equilibrium of the economy in which agent
`i`'s endowment is `cⁱ` (equivalently: after lump-sum transfers). As printed, with the original
endowments, the theorem is false (`theorem_13_3_2_counterexample`). -/
theorem theorem_13_3_2 {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty ι] (E : POEconomy ι S)
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (E.u i))
    (hdiff : ∀ i x, 0 < x → DifferentiableAt ℝ (E.u i) x) {y c : ι → List S → ℝ}
    (hpo : po_ParetoOptimal E y c) {δ : ℝ} (hδ : 0 < δ) (hint : ∀ i h, δ ≤ c i h) :
    ∃ q : List S → ℝ, q [] = 1 ∧ po_ADEquilibrium E c q c := by
  have hpos : ∀ i h, 0 < c i h := fun i h => hδ.trans_le (hint i h)
  have hd : ∀ i h, DifferentiableAt ℝ (E.u i) (c i h) := fun i h => hdiff i _ (hpos i h)
  obtain ⟨lam, hlam, -, hfoc⟩ := po_pareto_foc E hconc hpo hpos hd
  set j : ι := Classical.arbitrary ι
  set m := deriv (E.u j) (c j [])
  have hm : 0 < m := po_deriv_pos (hconc j) (E.u_mono j) (hpos j []) (hd j [])
  set q : List S → ℝ := fun h => po_w E h * deriv (E.u j) (c j h) / m with hqdef
  have hq0 : q [] = 1 := by simp only [hqdef, po_w_root, one_mul]; exact div_self hm.ne'
  have hdpos : ∀ h, 0 < deriv (E.u j) (c j h) := fun h =>
    po_deriv_pos (hconc j) (E.u_mono j) (hpos j h) (hd j h)
  have hdle : ∀ h, deriv (E.u j) (c j h) ≤ deriv (E.u j) δ := fun h =>
    ((hconc j).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
      (fun x hx => hdiff j x hx) (Set.mem_Ioi.mpr hδ) (Set.mem_Ioi.mpr (hpos j h)) (hint j h)
  have hqnn : ∀ h, 0 ≤ q h := fun h =>
    div_nonneg (mul_nonneg (po_w_nonneg E h) (hdpos h).le) hm.le
  have hq : q ∈ po_L1 S := by
    change Summable fun h => |q h|
    simp only [abs_of_nonneg (hqnn _)]
    refine Summable.of_nonneg_of_le hqnn (fun h => ?_)
      ((po_summable_w E).mul_right (deriv (E.u j) δ / m))
    simp only [hqdef]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hdle h) hm.le)
      (po_w_nonneg E h)
  have hfoc' : ∀ i h, po_w E h * deriv (E.u i) (c i h) = (lam j * m / lam i) * q h := by
    intro i h
    rcases (po_w_nonneg E h).lt_or_eq with hw | hw
    · have e := hfoc h hw i j
      simp only [hqdef]
      field_simp [(hlam i).ne', hm.ne']
      rw [← e]
      ring
    · simp only [hqdef, ← hw, zero_mul, zero_div, mul_zero]
  refine ⟨q, hq0, hq, ⟨hpo.1.1, fun _ => rfl⟩, fun i => ⟨le_rfl, fun x hx hxb => ?_⟩⟩
  exact po_optimal_of_foc E i (hconc i) (hpo.1.1 i) (hpos i) (hd i) hq
    (div_pos (mul_pos (hlam j) hm) (hlam i)).le (hfoc' i) rfl hx hxb

/-- Miao, Theorem 13.3.2 as printed is false. In `po_exampleEconomy` (two agents, `uⁱ = √·`),
let agent `0` own one unit at every node and agent `1` nothing. The allocation giving everything
to agent `1` is Pareto optimal, but it is not an Arrow–Debreu equilibrium allocation at any
prices: agent `0` could always afford her endowment, which she prefers to nothing. -/
theorem theorem_13_3_2_counterexample :
    let y : Fin 2 → List Bool → ℝ := fun i _ => if i = 0 then 1 else 0
    let c : Fin 2 → List Bool → ℝ := fun i _ => if i = 0 then 0 else 1
    po_ParetoOptimal po_exampleEconomy y c ∧ ¬ ∃ q, po_ADEquilibrium po_exampleEconomy y q c := by
  intro y c
  have h0 : (fun _ : List Bool => (0 : ℝ)) ∈ po_Lplus Bool :=
    ⟨fun _ => le_rfl, 0, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have h1 : (fun _ : List Bool => (1 : ℝ)) ∈ po_Lplus Bool :=
    ⟨fun _ => zero_le_one, 1, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩
  have hcmem : ∀ i, c i ∈ po_Lplus Bool := fun i => by
    by_cases hi : i = 0
    · simp only [c, hi, ↓reduceIte]; exact h0
    · simp only [c, hi, ↓reduceIte]; exact h1
  have hfeas : po_Feasible y c := ⟨hcmem, fun h => by simp [c, y, Fin.sum_univ_two]⟩
  refine ⟨?_, ?_⟩
  · have hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (po_exampleEconomy.u i) := fun i =>
      (po_exampleEconomy_assumption i).2.2.2.1.concaveOn
    have hcont : ∀ i, ContinuousOn (po_exampleEconomy.u i) (Set.Ici 0) := fun i =>
      (po_exampleEconomy_assumption i).2.1
    refine (proposition_13_2_1 po_exampleEconomy hconc hcont y c).mpr
      ⟨fun i => if i = 0 then 0 else 1, fun i => by by_cases hi : i = 0 <;> simp [hi], ?_,
        hfeas, fun d hd => ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
    · simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, zero_mul, zero_add, one_mul,
        show (1 : Fin 2) ≠ 0 by decide]
      refine po_U_mono _ 1 (hd.1 1) (hcmem 1) fun h => ?_
      have := hd.2 h
      simp only [Fin.sum_univ_two, y, c, Fin.isValue, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide] at this ⊢
      linarith [(hd.1 0).1 h]
  · rintro ⟨q, -, -, hopt⟩
    classical
    have hy0 : y 0 = fun _ => 1 := rfl
    have hc0 : c 0 = fun _ => 0 := rfl
    have hle := (hopt 0).2 (fun _ => 1) h1 (by rw [hy0])
    rw [hc0] at hle
    have hup := po_U_update po_exampleEconomy 0 h0 [] 1
    have hmono := po_U_mono po_exampleEconomy 0 (po_update_mem h0 [] zero_le_one) h1
      (fun h => by by_cases hh : h = [] <;> simp [hh])
    rw [po_w_root, one_mul] at hup
    have : po_exampleEconomy.u 0 0 < po_exampleEconomy.u 0 1 :=
      po_exampleEconomy.u_mono 0 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one)
        zero_lt_one
    linarith

/-- Miao, pp. 423–424: the date-`t` price at node `sᵗ` of an asset with payoffs `d`,
`p_t(sᵗ) = q⁰_t(sᵗ)⁻¹ Σ_{j ≥ 1} Σ_{s^{t+j} | sᵗ} q⁰_{t+j}(s^{t+j}) d_{t+j}(s^{t+j})`. -/
noncomputable def po_assetPrice {S : Type*} [Fintype S] (q d : List S → ℝ) (h : List S) : ℝ :=
  (q h)⁻¹ * ∑' j : ℕ, ∑ f : Fin (j + 1) → S, q (List.ofFn f ++ h) * d (List.ofFn f ++ h)

/-- Miao, p. 424 ("it is important that `q⁰ ∈ L¹` for the above prices to be well-defined"):
for `q⁰ ∈ L¹` and `d ∈ L∞` the series defining the asset price converges. -/
theorem po_assetPrice_summable {S : Type*} [Fintype S] {q d : List S → ℝ} (hq : q ∈ po_L1 S)
    (hd : d ∈ po_Linfty S) (h : List S) :
    Summable fun j : ℕ => ∑ f : Fin (j + 1) → S, q (List.ofFn f ++ h) * d (List.ofFn f ++ h) := by
  set ι' : (Σ j : ℕ, Fin (j + 1) → S) → List S := fun x => List.ofFn x.2 ++ h
  have hinj : Function.Injective ι' := by
    rintro ⟨j, f⟩ ⟨j', f'⟩ he
    simp only [ι', List.append_cancel_right_eq] at he
    have := List.ofFn_inj'.mp he
    simp only [Sigma.mk.injEq, add_left_inj] at this
    obtain ⟨rfl, hf⟩ := this
    rw [heq_eq_eq] at hf
    rw [hf]
  have hs := ((eq_13_5 hq hd).comp_injective hinj).sigma
  simp only [Function.comp_def, ι', tsum_fintype] at hs
  exact hs

/-- Miao, p. 423: at the root, with `q⁰₀(s₀) = 1`, the date-zero price is
`p₀ = Σ_{j ≥ 1} Σ_{sʲ} q⁰_j(sʲ) d_j(sʲ)`. -/
theorem po_assetPrice_root {S : Type*} [Fintype S] {q : List S → ℝ} (hq0 : q [] = 1)
    (d : List S → ℝ) :
    po_assetPrice q d [] =
      ∑' j : ℕ, ∑ f : Fin (j + 1) → S, q (List.ofFn f) * d (List.ofFn f) := by
  simp [po_assetPrice, hq0]

/-- Miao, p. 424 ("For the discounted expected utility (13.1), `q⁰_t` is given in (13.7)"):
substituting (13.7), `p_t(sᵗ) = Σ_{j ≥ 1} Σ_{s^{t+j}|sᵗ} βʲ Pr(s^{t+j} | sᵗ)
(u'(c_{t+j}(s^{t+j})) / u'(c_t(sᵗ))) d_{t+j}(s^{t+j})`. -/
theorem po_assetPrice_eq {ι S : Type*} [Fintype S] (E : POEconomy ι S) (i : ι)
    {q d c : List S → ℝ} (hq : ∀ g, q g = po_w E g * deriv (E.u i) (c g) / deriv (E.u i) (c []))
    (hμ : deriv (E.u i) (c []) ≠ 0) {h : List S} (hpr : 0 < E.P.pr h)
    (hdh : deriv (E.u i) (c h) ≠ 0) :
    po_assetPrice q d h = ∑' j : ℕ, ∑ f : Fin (j + 1) → S,
      E.β ^ (j + 1) * po_condPr E.P (List.ofFn f ++ h) h *
        (deriv (E.u i) (c (List.ofFn f ++ h)) / deriv (E.u i) (c h)) * d (List.ofFn f ++ h) := by
  unfold po_assetPrice
  rw [← tsum_mul_left]
  congr 1
  funext j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hq, hq]
  unfold po_w po_condPr
  rw [List.length_append, List.length_ofFn, pow_add]
  have hβ : E.β ^ h.length ≠ 0 := pow_ne_zero _ E.β_pos.ne'
  field_simp

end Miao.CompleteMarkets
