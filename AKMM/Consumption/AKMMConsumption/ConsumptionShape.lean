/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.BorrowingConstraints
import LeanEconomics.Analysis.PowerMean
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The shape of the consumption function under a borrowing limit (Figure 11.2)

AKMM, §11.3.4, pp. 304–306, Figure 11.2: with a borrowing limit `aₜ₊₁ ≥ −a` the consumption
function has slope `1` below the kink `a*` where the limit stops binding, is concave above it,
its slope tends to `r/(1 + r)` as wealth grows and lies between `r/(1 + r)` and `1`, and a
tighter limit `a₂ < a₁` makes the household constrained on a wider range, lowers consumption,
raises the MPC, and leaves consumption unchanged at high wealth.

## The model

Income is i.i.d. with finitely many values `yᵢ ≥ d + a > 0` (`d > 0`), so the state is cash in
hand `x = aₜ + yₜ ≥ d` and the budget is `c + aₜ₊₁/R = x`, `aₜ₊₁ ≥ −a`. The household lives
`n` more periods and eats its cash in the last (`cfn_cons 0 = id`). With `n + 1` periods left its
consumption `c` at `x` solves the Kuhn–Tucker conditions of (11.32)–(11.33),

  `c ≤ x + a/R`,  `c ≤ θ·M(cₙ(R(x − c) + yᵢ))`,  with equality in the second if `c < x + a/R`,

where `M` is the certainty equivalent of the Euler equation (`CfnHousehold.KKT`). For quadratic
utility with `βR = 1`, the book's case, `M` is the expectation and `θ = 1`, and the conditions
are exactly (11.33), `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}` (`cfn_kkt_iff_min`, `cfn_quadratic_kkt_iff`);
for CRRA utility `M` is the power mean with exponent `−σ` and `θ = (βR)^{−1/σ}`, and the second
condition is the Euler inequality `u′(c) ≥ βREu′(cₙ)` (`cfn_crra_euler_iff`). All that is used
of `M` is that it is monotone, normalised, concave and continuous on positive vectors
(`cfn_IsMean`; `cfn_isMean_expect`, `cfn_isMean_powerMean`, the latter from LeanEconomics'
Carroll–Kimball power mean).

## Results

* The Kuhn–Tucker conditions have exactly one solution at every `x ≥ d` (`cfn_kkt_exists`,
  `cfn_kkt_unique`), so the consumption functions `cfn_cons n` are well defined (`cfn_cons_kkt`).
* **Figure 11.2, shape.** Every `cfn_cons n` is concave (`cfn_cons_concave`), nondecreasing with
  slopes in `[κₙ, 1]` (`cfn_cons_slope_bounds`), the constraint binds on an initial interval of
  cash in hand where the slope is exactly `1` (`cfn_binding_initial`), and
  `κₙx ≤ cₙ(x) ≤ κₙ(x + hₙ)` (`cfn_cons_good`), where `κₙ` is the perfect-foresight MPC with `n`
  periods left (`cfn_kappa`).
* **The slope tends to `κₙ`** as wealth grows (`cfn_slope_tendsto`), and `κₙ → 1 − 1/(θR)` as the
  horizon grows (`cfn_kappa_tendsto`); for `βR = 1` this is `r/(1 + r)` (`cfn_kappa_tendsto_r`,
  `cfn_fig_11_2_slope`), and for CRRA it is the MPC (11.16) `1 − R⁻¹(βR)^{1/σ}`
  (`cfn_crra_kappa_limit`).
* **A tighter limit** `a₂ ≤ a₁` (with `r ≥ 0`): consumption is lower everywhere
  (`cfn_tight_le`), the household is constrained wherever the loose one is (`cfn_tight_binds`),
  the two consumption functions coincide for large wealth (`cfn_tight_eventually_eq`), and one
  period before the end the tight MPC is at least the loose MPC on every interval
  (`cfn_tight_mpc_last`).

Departures: the book's household lives for ever; here the horizon is finite and the infinite
horizon is reached only through `κₙ → r/(1 + r)`. Consumption functions are defined by the
Kuhn–Tucker conditions (as the book does with (11.33)); their sufficiency for optimality is not
re-proved. Concavity is proved weakly; "strictly concave" in the intermediate range is not. The
MPC comparison for a tighter limit is proved pointwise only one period before the end; with
more periods left the proved statements are the three above (lower consumption, wider
constrained range, coincidence at high wealth).
-/

namespace AKMM.Consumption

open Filter Topology

/-! ### The certainty equivalent -/

/-- The properties of the Euler equation's certainty equivalent `M` that the argument uses, on
vectors of positive next-period consumptions: monotone, normalised (`M` of a constant is the
constant), concave, continuous. The expectation (quadratic utility) and the power mean with a
negative exponent (CRRA) are instances. -/
def cfn_IsMean {ι : Type*} (M : (ι → ℝ) → ℝ) : Prop :=
  (∀ z z' : ι → ℝ, (∀ i, 0 < z i) → (∀ i, z i ≤ z' i) → M z ≤ M z') ∧
  (∀ k : ℝ, 0 < k → M (fun _ => k) = k) ∧
  (∀ z z' : ι → ℝ, (∀ i, 0 < z i) → (∀ i, 0 < z' i) → ∀ μ ν : ℝ, 0 ≤ μ → 0 ≤ ν → μ + ν = 1 →
    μ * M z + ν * M z' ≤ M (fun i => μ * z i + ν * z' i)) ∧
  (∀ z : ι → ℝ, (∀ i, 0 < z i) → ContinuousAt M z)

/-- A monotone, normalised `M` is at least `k` on vectors bounded below by `k > 0`. -/
theorem cfn_mean_ge {ι : Type*} {M : (ι → ℝ) → ℝ} (hM : cfn_IsMean M) {k : ℝ} (hk : 0 < k)
    {z : ι → ℝ} (hz : ∀ i, k ≤ z i) : k ≤ M z := by
  have h := hM.1 (fun _ => k) z (fun _ => hk) hz
  rwa [hM.2.1 k hk] at h

/-- A monotone, normalised `M` is at most `k` on positive vectors bounded above by `k`. -/
theorem cfn_mean_le {ι : Type*} {M : (ι → ℝ) → ℝ} (hM : cfn_IsMean M) {k : ℝ}
    {z : ι → ℝ} (hz0 : ∀ i, 0 < z i) (hz : ∀ i, z i ≤ k) [Nonempty ι] : M z ≤ k := by
  have hk : 0 < k := lt_of_lt_of_le (hz0 (Classical.arbitrary ι)) (hz _)
  have h := hM.1 z (fun _ => k) hz0 hz
  rwa [hM.2.1 k hk] at h

/-- **The expectation is a certainty equivalent** (quadratic utility). -/
theorem cfn_isMean_expect {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : cfn_IsMean (fun z : ι → ℝ => ∑ i, w i * z i) := by
  refine ⟨fun z z' _ hzz => Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hzz i) (hw i),
    fun k _ => by
      change ∑ i, w i * k = k
      rw [← Finset.sum_mul, hw1, one_mul], fun z z' _ _ μ ν _ _ _ => ?_,
    fun z _ => ?_⟩
  · simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    exact le_of_eq (by congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring)
  · exact (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).continuousAt

/-- **The power mean with a negative exponent is a certainty equivalent** (CRRA utility), by
LeanEconomics' Carroll–Kimball power-mean concavity (`powerMean_concave`). -/
theorem cfn_isMean_powerMean {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {p : ℝ} (hp : p < 0) :
    cfn_IsMean (LeanEconomics.powerMean w p) := by
  refine ⟨fun z z' hz hzz => LeanEconomics.powerMean_mono hp hw hw1 hz
      (fun i => lt_of_lt_of_le (hz i) (hzz i)) hzz, fun k hk => ?_,
    fun z z' hz hz' μ ν hμ hν hμν => LeanEconomics.powerMean_concave hp hw hw1 hz hz' hμ hν hμν,
    fun z hz => ?_⟩
  · have hs : ∑ i, w i * k ^ p = k ^ p := by rw [← Finset.sum_mul, hw1, one_mul]
    simp only [LeanEconomics.powerMean, hs]
    rw [← Real.rpow_mul hk.le, mul_one_div_cancel hp.ne, Real.rpow_one]
  · have hS : 0 < ∑ i, w i * z i ^ p := LeanEconomics.sum_rpow_pos hw hw1 hz
    have hi : ∀ i, ContinuousAt (fun z : ι → ℝ => w i * z i ^ p) z := fun i =>
      continuousAt_const.mul ((continuous_apply i).continuousAt.rpow_const (Or.inl (hz i).ne'))
    have hsum : ContinuousAt (fun z : ι → ℝ => ∑ i, w i * z i ^ p) z :=
      tendsto_finsetSum _ (fun i _ => hi i)
    exact hsum.rpow_const (Or.inl hS.ne')

/-! ### The household -/

/-- AKMM, pp. 304–306: the household of Figure 11.2. `M` and `θ` are the Euler equation's
certainty equivalent and its factor, `R = 1 + r`, `b` the borrowing limit `a`, `d` the lowest
cash in hand, `y` the i.i.d. income values with probabilities `w` and upper bound `ymax`. -/
structure CfnHousehold (ι : Type*) where
  M : (ι → ℝ) → ℝ
  θ : ℝ
  R : ℝ
  b : ℝ
  d : ℝ
  y : ι → ℝ
  ymax : ℝ
  w : ι → ℝ

namespace CfnHousehold

variable {ι : Type*} (H : CfnHousehold ι)

/-- The standing assumptions: `M` a certainty equivalent, `θ > 0`, `R ≥ 1` (`r ≥ 0`), `a ≥ 0`,
`d > 0`, `d + a ≤ yᵢ ≤ ymax`, and `w` a probability vector. -/
def Valid [Fintype ι] : Prop :=
  cfn_IsMean H.M ∧ 0 < H.θ ∧ 1 ≤ H.R ∧ 0 ≤ H.b ∧ 0 < H.d ∧ (∀ i, H.d + H.b ≤ H.y i) ∧
    (∀ i, H.y i ≤ H.ymax) ∧ (∀ i, 0 ≤ H.w i) ∧ ∑ i, H.w i = 1

/-- The right-hand side of the Euler condition at end-of-period saving `s = aₜ₊₁/R`, given next
period's consumption function `cn`: `θ·M(cn(Rs + yᵢ))`. -/
noncomputable def cont (cn : ℝ → ℝ) (s : ℝ) : ℝ := H.θ * H.M (fun i => cn (H.R * s + H.y i))

/-- **AKMM, (11.32)–(11.33).** The Kuhn–Tucker conditions for consumption `c` at cash in hand
`x`: the borrowing limit `c ≤ x + a/R`, the Euler inequality, and the Euler equation where the
limit is slack. -/
def KKT (cn : ℝ → ℝ) (x c : ℝ) : Prop :=
  c ≤ x + H.b / H.R ∧ c ≤ H.cont cn (x - c) ∧ (c < x + H.b / H.R → c = H.cont cn (x - c))

/-- One step of backward induction: the solution of the Kuhn–Tucker conditions. -/
noncomputable def step (cn : ℝ → ℝ) (x : ℝ) : ℝ := Classical.epsilon (fun c => H.KKT cn x c)

/-- The consumption function with `n` periods left after this one; in the last period the
household eats its cash in hand. -/
noncomputable def cons : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | n + 1 => H.step (cons n)

/-- The perfect-foresight MPC with `n` periods left: `κ₀ = 1`, `κₙ₊₁ = θRκₙ/(1 + θRκₙ)`. -/
noncomputable def kappa : ℕ → ℝ
  | 0 => 1
  | n + 1 => H.θ * H.R * kappa n / (1 + H.θ * H.R * kappa n)

/-- Human wealth at the highest income with `n` periods left: `h₀ = 0`, `hₙ₊₁ = (ymax + hₙ)/R`. -/
noncomputable def hw : ℕ → ℝ
  | 0 => 0
  | n + 1 => (H.ymax + hw n) / H.R

/-- The properties carried along the induction: positive, nondecreasing, slopes at most `1`,
concave, and between the lines `κx` and `κ(x + h)`. -/
def Good (κ h : ℝ) (cn : ℝ → ℝ) : Prop :=
  (∀ x, H.d ≤ x → 0 < cn x) ∧ MonotoneOn cn (Set.Ici H.d) ∧
  (∀ x x', H.d ≤ x → x ≤ x' → cn x' - cn x ≤ x' - x) ∧ ConcaveOn ℝ (Set.Ici H.d) cn ∧
  (∀ x, H.d ≤ x → κ * x ≤ cn x ∧ cn x ≤ κ * (x + h))

end CfnHousehold

open CfnHousehold

variable {ι : Type*} [Fintype ι] {H : CfnHousehold ι}

/-- Saving at least `−a/R` keeps next period's cash in hand above `d`. -/
theorem cfn_arg_ge (hV : H.Valid) {s : ℝ} (hs : -(H.b / H.R) ≤ s) (i : ι) :
    H.d ≤ H.R * s + H.y i := by
  obtain ⟨-, -, hR, -, -, hy, -⟩ := hV
  have hR0 : 0 < H.R := by linarith
  have h1 : -H.b ≤ H.R * s := by
    have := mul_le_mul_of_nonneg_left hs hR0.le
    rwa [mul_neg, mul_div_cancel₀ _ hR0.ne'] at this
  linarith [hy i]

omit [Fintype ι] in
/-- A good function is continuous on `[d, ∞)`: it is `1`-Lipschitz. -/
theorem cfn_good_continuousOn {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) :
    ContinuousOn cn (Set.Ici H.d) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx x' hx' => ?_).continuousOn
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x x' with hxx | hxx
  · have h1 := hg.2.2.1 x x' hx hxx
    have h2 := hg.2.1 hx hx' hxx
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · have h1 := hg.2.2.1 x' x hx' hxx
    have h2 := hg.2.1 hx' hx hxx
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h1

/-- The Euler right-hand side is nondecreasing in saving. -/
theorem cfn_cont_mono (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {s₁ s₂ : ℝ}
    (hs₁ : -(H.b / H.R) ≤ s₁) (h12 : s₁ ≤ s₂) : H.cont cn s₁ ≤ H.cont cn s₂ := by
  have hR : 0 ≤ H.R := by linarith [hV.2.2.1]
  have hs₂ : -(H.b / H.R) ≤ s₂ := le_trans hs₁ h12
  refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => hg.1 _ (cfn_arg_ge hV hs₁ i))
    (fun i => hg.2.1 (cfn_arg_ge hV hs₁ i) (cfn_arg_ge hV hs₂ i) ?_)) hV.2.1.le
  nlinarith

/-- The Euler right-hand side is concave in saving (Carroll–Kimball). -/
theorem cfn_cont_concave (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn)
    {s₁ s₂ μ ν : ℝ} (hs₁ : -(H.b / H.R) ≤ s₁) (hs₂ : -(H.b / H.R) ≤ s₂) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (hμν : μ + ν = 1) :
    μ * H.cont cn s₁ + ν * H.cont cn s₂ ≤ H.cont cn (μ * s₁ + ν * s₂) := by
  have hm : -(H.b / H.R) ≤ μ * s₁ + ν * s₂ := by
    have e1 := mul_le_mul_of_nonneg_left hs₁ hμ
    have e2 := mul_le_mul_of_nonneg_left hs₂ hν
    have e3 : -(H.b / H.R) = μ * -(H.b / H.R) + ν * -(H.b / H.R) := by
      linear_combination (H.b / H.R) * hμν
    linarith
  have hpos : ∀ s, -(H.b / H.R) ≤ s → ∀ i, 0 < cn (H.R * s + H.y i) :=
    fun s hs i => hg.1 _ (cfn_arg_ge hV hs i)
  have hconc : ∀ i, μ * cn (H.R * s₁ + H.y i) + ν * cn (H.R * s₂ + H.y i)
      ≤ cn (H.R * (μ * s₁ + ν * s₂) + H.y i) := by
    intro i
    have := hg.2.2.2.1.2 (Set.mem_Ici.2 (cfn_arg_ge hV hs₁ i))
      (Set.mem_Ici.2 (cfn_arg_ge hV hs₂ i)) hμ hν hμν
    simp only [smul_eq_mul] at this
    have he : μ * (H.R * s₁ + H.y i) + ν * (H.R * s₂ + H.y i)
        = H.R * (μ * s₁ + ν * s₂) + H.y i := by linear_combination H.y i * hμν
    rwa [he] at this
  have hcomb := hV.1.2.2.1 _ _ (hpos s₁ hs₁) (hpos s₂ hs₂) μ ν hμ hν hμν
  have hmono := hV.1.1 _ _ (fun i => by
      have := hpos s₁ hs₁ i; have := hpos s₂ hs₂ i
      rcases eq_or_lt_of_le hμ with h0 | h0
      · have : ν = 1 := by linarith
        subst h0; simp only [zero_mul, zero_add, this, one_mul]; linarith
      · positivity) hconc
  simp only [cont]
  have hθ := hV.2.1
  nlinarith [mul_le_mul_of_nonneg_left (le_trans hcomb hmono) hθ.le]

/-- The lower bound of the Euler right-hand side from a linear lower bound on `cn`. -/
theorem cfn_cont_ge (hV : H.Valid) {κ h : ℝ} (hκ : 0 < κ) {cn : ℝ → ℝ} (hg : H.Good κ h cn)
    {s : ℝ} (hs : 0 < s) : H.θ * κ * H.R * s ≤ H.cont cn s := by
  obtain ⟨hM, hθ, hR, hb, hd, hy, -⟩ := id hV
  have hR0 : 0 < H.R := by linarith
  have hbR : -(H.b / H.R) ≤ s := by
    have : 0 ≤ H.b / H.R := div_nonneg hb hR0.le
    linarith
  have hk : 0 < κ * H.R * s := by positivity
  have hz : ∀ i, κ * H.R * s ≤ cn (H.R * s + H.y i) := by
    intro i
    have h1 := (hg.2.2.2.2 _ (cfn_arg_ge hV hbR i)).1
    have hyi : 0 ≤ H.y i := by linarith [hy i]
    nlinarith
  have := cfn_mean_ge hM hk hz
  simp only [cont]
  nlinarith

/-- The upper bound of the Euler right-hand side from `cn ≤ κ(x + h)`. -/
theorem cfn_cont_le (hV : H.Valid) {κ h : ℝ} (hκ0 : 0 ≤ κ) {cn : ℝ → ℝ} (hg : H.Good κ h cn)
    {s : ℝ} (hs : -(H.b / H.R) ≤ s) : H.cont cn s ≤ H.θ * (κ * (H.R * s + H.ymax + h)) := by
  have hz : ∀ i, cn (H.R * s + H.y i) ≤ κ * (H.R * s + H.ymax + h) := by
    intro i
    have h1 := (hg.2.2.2.2 _ (cfn_arg_ge hV hs i)).2
    have := hV.2.2.2.2.2.2.1 i
    nlinarith
  have hne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := hV.1.2.1 1 one_pos
    have h2 := hV.1.2.1 2 two_pos
    have : (fun _ : ι => (1 : ℝ)) = fun _ => 2 := funext fun i => isEmptyElim i
    rw [this] at h1
    linarith
  exact mul_le_mul_of_nonneg_left
    (cfn_mean_le hV.1 (fun i => hg.1 _ (cfn_arg_ge hV hs i)) hz) hV.2.1.le

omit [Fintype ι] in
/-- Unfolding `R(x − c) ≥ −a` from `c ≤ x + a/R`. -/
theorem cfn_save_ge {x c : ℝ} (hc : c ≤ x + H.b / H.R) :
    -(H.b / H.R) ≤ x - c := by linarith

/-- **The Kuhn–Tucker conditions have a solution** at every `x ≥ d`, by the intermediate value
theorem: the Euler gap `c − θM(cn(R(x − c) + yᵢ))` is continuous and negative at small `c`. -/
theorem cfn_kkt_exists (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) (x : ℝ) :
    ∃ c, H.KKT cn x c := by
  set top := x + H.b / H.R with htop
  by_cases hF : top ≤ H.cont cn (x - top)
  · exact ⟨top, le_rfl, hF, fun h => absurd h (lt_irrefl _)⟩
  push Not at hF
  have hd := hV.2.2.2.2.1
  set c₀ := min top (H.θ * cn H.d) with hc₀
  have hc₀top : c₀ ≤ top := min_le_left _ _
  -- the Euler right-hand side is at least `θ·cn(d)`
  have hlow : ∀ c, c ≤ top → H.θ * cn H.d ≤ H.cont cn (x - c) := by
    intro c hc
    have hs := cfn_save_ge hc
    have h1 : cn H.d ≤ H.M (fun i => cn (H.R * (x - c) + H.y i)) :=
      cfn_mean_ge hV.1 (hg.1 _ le_rfl) fun i => hg.2.1 (Set.mem_Ici.2 le_rfl)
        (Set.mem_Ici.2 (cfn_arg_ge hV hs i)) (cfn_arg_ge hV hs i)
    exact mul_le_mul_of_nonneg_left h1 hV.2.1.le
  have hF0 : c₀ - H.cont cn (x - c₀) ≤ 0 := by
    have := hlow c₀ hc₀top
    have : c₀ ≤ H.θ * cn H.d := min_le_right _ _
    linarith
  -- continuity of the Euler gap on `[c₀, top]`
  have hcont : ContinuousOn (fun c => c - H.cont cn (x - c)) (Set.Icc c₀ top) := by
    have hcn := cfn_good_continuousOn hg
    have hv : ContinuousOn (fun c => fun i => cn (H.R * (x - c) + H.y i)) (Set.Icc c₀ top) := by
      refine continuousOn_pi.2 fun i => ?_
      refine hcn.comp (f := fun c => H.R * (x - c) + H.y i) (by fun_prop) fun c hc => ?_
      exact Set.mem_Ici.2 (cfn_arg_ge hV (cfn_save_ge hc.2) i)
    refine continuousOn_id.sub (continuousOn_const.mul fun c hc => ?_)
    exact (hV.1.2.2.2 _ fun i => hg.1 _ (cfn_arg_ge hV (cfn_save_ge hc.2) i)
      ).comp_continuousWithinAt (hv c hc)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hc₀top hcont
    ⟨hF0, by linarith⟩
  have hceq : c = H.cont cn (x - c) := by linarith
  exact ⟨c, hc.2, le_of_eq hceq, fun _ => hceq⟩

/-- **The Kuhn–Tucker conditions have at most one solution.** -/
theorem cfn_kkt_unique (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c c' : ℝ}
    (hc : H.KKT cn x c) (hc' : H.KKT cn x c') : c = c' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hint : c < x + H.b / H.R := lt_of_lt_of_le hlt hc'.1
    have := hc.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge hc'.1) (by linarith : x - c' ≤ x - c)
    linarith [hc'.2.1]
  · have hint : c' < x + H.b / H.R := lt_of_lt_of_le hlt hc.1
    have := hc'.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge hc.1) (by linarith : x - c ≤ x - c')
    linarith [hc.2.1]

/-- The step function solves the Kuhn–Tucker conditions. -/
theorem cfn_step_kkt (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) (x : ℝ) :
    H.KKT cn x (H.step cn x) :=
  Classical.epsilon_spec (cfn_kkt_exists hV hg x)

/-- Any solution of the Kuhn–Tucker conditions is the step function's value. -/
theorem cfn_step_eq_of_kkt (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x c : ℝ}
    (hc : H.KKT cn x c) : H.step cn x = c :=
  cfn_kkt_unique hV hg (cfn_step_kkt hV hg x) hc

/-- **Consumption and saving are both nondecreasing in cash in hand** under any rule solving the
Kuhn–Tucker conditions. -/
theorem cfn_kkt_mono (hV : H.Valid) {κ h : ℝ} {cn : ℝ → ℝ} (hg : H.Good κ h cn) {x₁ x₂ c₁ c₂ : ℝ}
    (h₁ : H.KKT cn x₁ c₁) (h₂ : H.KKT cn x₂ c₂) (hx : x₁ ≤ x₂) : c₁ ≤ c₂ ∧ x₁ - c₁ ≤ x₂ - c₂ := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hint : c₂ < x₂ + H.b / H.R := by linarith [h₁.1]
    have := h₂.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge h₁.1) (by linarith : x₁ - c₁ ≤ x₂ - c₂)
    linarith [h₁.2.1]
  · by_contra hlt
    push Not at hlt
    have hint : c₁ < x₁ + H.b / H.R := by linarith [h₂.1]
    have := h₁.2.2 hint
    have hm := cfn_cont_mono hV hg (cfn_save_ge h₂.1) hlt.le
    linarith [h₂.2.1]

/-- **The induction step.** If next period's consumption function is good with `(κ, h)`, this
period's is good with `(θRκ/(1 + θRκ), (ymax + h)/R)`. -/
theorem cfn_step_good (hV : H.Valid) {κ h : ℝ} (hκ : 0 < κ) {cn : ℝ → ℝ} (hg : H.Good κ h cn) :
    H.Good (H.θ * H.R * κ / (1 + H.θ * H.R * κ)) ((H.ymax + h) / H.R) (H.step cn) := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hθ := hV.2.1
  have hd := hV.2.2.2.2.1
  have hb := hV.2.2.2.1
  set q := H.θ * H.R * κ with hq
  have hq0 : 0 < q := by positivity
  have hK := fun x (_ : H.d ≤ x) => cfn_step_kkt hV hg x
  have hκ1 : q / (1 + q) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- the sandwich
  have hsand : ∀ x, H.d ≤ x → q / (1 + q) * x ≤ H.step cn x ∧
      H.step cn x ≤ q / (1 + q) * (x + (H.ymax + h) / H.R) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hK x hx
    constructor
    · rcases le_or_gt (x - H.step cn x) 0 with hs | hs
      · have : q / (1 + q) * x ≤ x := by
          have := mul_le_mul_of_nonneg_right hκ1 (by linarith : 0 ≤ x); linarith
        linarith
      · have hint : H.step cn x < x + H.b / H.R := by
          have : 0 ≤ H.b / H.R := div_nonneg hb hR0.le
          linarith
        have he := h3 hint
        have hge := cfn_cont_ge hV hκ hg hs
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        rw [← he] at hge
        nlinarith
    · have hle := cfn_cont_le hV hκ.le hg (cfn_save_ge h1)
      have hc := le_trans h2 hle
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have he : H.θ * (κ * (H.R * (x - H.step cn x) + H.ymax + h))
          = q * (x - H.step cn x + (H.ymax + h) / H.R) := by
        rw [hq]; field_simp; ring
      rw [he] at hc
      nlinarith
  refine ⟨fun x hx => ?_, fun x hx x' hx' hxx => ?_, fun x x' hx hxx => ?_, ?_, hsand⟩
  · have := (hsand x hx).1
    have : 0 < q / (1 + q) * x := mul_pos (div_pos hq0 (by linarith)) (by linarith)
    linarith
  · exact (cfn_kkt_mono hV hg (hK x hx) (hK x' hx') hxx).1
  · have := (cfn_kkt_mono hV hg (hK x hx) (hK x' (le_trans hx hxx)) hxx).2
    linarith
  · refine ⟨convex_Ici _, fun x hx x' hx' μ ν hμ hν hμν => ?_⟩
    simp only [smul_eq_mul]
    have hx0 : H.d ≤ x := hx
    have hx0' : H.d ≤ x' := hx'
    have hm : H.d ≤ μ * x + ν * x' := by nlinarith
    obtain ⟨a1, a2, -⟩ := hK x hx0
    obtain ⟨b1, b2, -⟩ := hK x' hx0'
    obtain ⟨m1, -, m3⟩ := hK _ hm
    by_contra hlt
    push Not at hlt
    have hsa := cfn_save_ge a1
    have hsb := cfn_save_ge b1
    have hsm : μ * (x - H.step cn x) + ν * (x' - H.step cn x')
        < μ * x + ν * x' - H.step cn (μ * x + ν * x') := by nlinarith
    have e1 := mul_le_mul_of_nonneg_left hsa hμ
    have e2 := mul_le_mul_of_nonneg_left hsb hν
    have e3 : -(H.b / H.R) = μ * -(H.b / H.R) + ν * -(H.b / H.R) := by
      linear_combination (H.b / H.R) * hμν
    have hint : H.step cn (μ * x + ν * x') < μ * x + ν * x' + H.b / H.R := by linarith
    have he := m3 hint
    have hconc := cfn_cont_concave hV hg hsa hsb hμ hν hμν
    have hmono := cfn_cont_mono hV hg (by linarith) hsm.le
    nlinarith

/-- `0 < κₙ ≤ 1`. -/
theorem cfn_kappa_pos (hV : H.Valid) (n : ℕ) : 0 < H.kappa n ∧ H.kappa n ≤ 1 := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hθ := hV.2.1
  induction n with
  | zero => simp only [kappa]; norm_num
  | succ n ih =>
    simp only [kappa]
    have hq : 0 < H.θ * H.R * H.kappa n := by have := ih.1; positivity
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩

/-- **Every consumption function is good**: positive, nondecreasing, slopes at most `1`, concave,
and `κₙx ≤ cₙ(x) ≤ κₙ(x + hₙ)`. -/
theorem cfn_cons_good (hV : H.Valid) (n : ℕ) : H.Good (H.kappa n) (H.hw n) (H.cons n) := by
  induction n with
  | zero =>
    have hd := hV.2.2.2.2.1
    refine ⟨fun x hx => by simp only [cons]; linarith, fun x _ x' _ h => h,
      fun x x' _ _ => by simp only [cons]; linarith, ?_, fun x _ => ?_⟩
    · exact (LinearMap.id : ℝ →ₗ[ℝ] ℝ).concaveOn (convex_Ici _)
    · simp only [cons, kappa, hw]; constructor <;> linarith
  | succ n ih =>
    simp only [cons, kappa, hw]
    exact cfn_step_good hV (cfn_kappa_pos hV n).1 ih

/-- `cₙ₊₁` solves the Kuhn–Tucker conditions (11.32)–(11.33) given `cₙ`. -/
theorem cfn_cons_kkt (hV : H.Valid) (n : ℕ) (x : ℝ) :
    H.KKT (H.cons n) x (H.cons (n + 1) x) :=
  cfn_step_kkt hV (cfn_cons_good hV n) x

/-- The borrowing limit: `cₙ(x) ≤ x + a/R`. -/
theorem cfn_cons_le (hV : H.Valid) (n : ℕ) (x : ℝ) :
    H.cons n x ≤ x + H.b / H.R := by
  cases n with
  | zero =>
    simp only [cons]
    have : 0 ≤ H.b / H.R := div_nonneg hV.2.2.2.1 (by linarith [hV.2.2.1])
    linarith
  | succ n => exact (cfn_cons_kkt hV n x).1

/-- **Figure 11.2: the consumption function is concave** in cash in hand (Carroll–Kimball). -/
theorem cfn_cons_concave (hV : H.Valid) (n : ℕ) : ConcaveOn ℝ (Set.Ici H.d) (H.cons n) :=
  (cfn_cons_good hV n).2.2.2.1

/-! ### Slopes -/

/-- A concave function above the line `κx` has every slope at least `κ`. -/
theorem cfn_slope_ge_of_concave {f : ℝ → ℝ} {d κ : ℝ} (hf : ConcaveOn ℝ (Set.Ici d) f)
    (hlow : ∀ x, d ≤ x → κ * x ≤ f x) {x x' : ℝ} (hx : d ≤ x) (hxx : x < x') :
    κ ≤ (f x' - f x) / (x' - x) := by
  by_contra hlt
  push Not at hlt
  set σ := (f x' - f x) / (x' - x) with hσ
  set z := max (x' + 1) ((f x' - σ * x' + 1) / (κ - σ)) with hz
  have hz1 : x' < z := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hκσ : 0 < κ - σ := by linarith
  have hslope := hf.slope_anti_adjacent (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 (by linarith : d ≤ z)) hxx hz1
  rw [← hσ, div_le_iff₀ (by linarith)] at hslope
  have hfz := hlow z (by linarith)
  have hz2 : (f x' - σ * x' + 1) / (κ - σ) ≤ z := le_max_right _ _
  rw [div_le_iff₀ hκσ] at hz2
  nlinarith

/-- A concave function below the line `κ(x + K)` has slopes eventually at most `κ + ε`. -/
theorem cfn_slope_le_eventually {f : ℝ → ℝ} {d κ K : ℝ} (hf : ConcaveOn ℝ (Set.Ici d) f)
    (hup : ∀ x, d ≤ x → f x ≤ κ * (x + K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ X, ∀ x x', X ≤ x → x < x' → (f x' - f x) / (x' - x) ≤ κ + ε := by
  set C := κ * (K + d) - f d with hC
  refine ⟨d + 1 + |C| / ε, fun x x' hx hxx => ?_⟩
  have hCε : 0 ≤ |C| / ε := div_nonneg (abs_nonneg _) hε.le
  have hdx : d < x := by linarith
  have hslope := hf.slope_anti_adjacent (Set.mem_Ici.2 le_rfl)
    (Set.mem_Ici.2 (by linarith : d ≤ x')) hdx hxx
  refine le_trans hslope ?_
  rw [div_le_iff₀ (by linarith)]
  have hfx := hup x hdx.le
  have h1 : |C| ≤ ε * (x - d - 1) := by
    have : |C| / ε ≤ x - d - 1 := by linarith
    rw [div_le_iff₀ hε] at this; linarith
  have h2 : C ≤ |C| := le_abs_self C
  nlinarith

/-- **Figure 11.2: the MPC lies between `κₙ` and `1`.** Every slope of the consumption function
on `[d, ∞)` is at least the perfect-foresight MPC `κₙ` and at most `1`. -/
theorem cfn_cons_slope_bounds (hV : H.Valid) (n : ℕ) {x x' : ℝ} (hx : H.d ≤ x) (hxx : x < x') :
    H.kappa n ≤ (H.cons n x' - H.cons n x) / (x' - x) ∧
      (H.cons n x' - H.cons n x) / (x' - x) ≤ 1 := by
  have hg := cfn_cons_good hV n
  refine ⟨cfn_slope_ge_of_concave hg.2.2.2.1 (fun y hy => (hg.2.2.2.2 y hy).1) hx hxx, ?_⟩
  rw [div_le_one (by linarith)]
  exact hg.2.2.1 x x' hx hxx.le

/-- **Figure 11.2: the slope tends to `κₙ` as wealth grows.** For every `ε > 0` all slopes of
`cₙ` beyond some wealth level are within `ε` of the perfect-foresight MPC `κₙ`. -/
theorem cfn_slope_tendsto (hV : H.Valid) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X, ∀ x x', X ≤ x → x < x' →
      |(H.cons n x' - H.cons n x) / (x' - x) - H.kappa n| ≤ ε := by
  have hg := cfn_cons_good hV n
  obtain ⟨X, hX⟩ := cfn_slope_le_eventually hg.2.2.2.1 (fun y hy => (hg.2.2.2.2 y hy).2) hε
  refine ⟨max X H.d, fun x x' hx hxx => ?_⟩
  have h1 := hX x x' (le_trans (le_max_left _ _) hx) hxx
  have h2 := cfn_slope_ge_of_concave hg.2.2.2.1 (fun y hy => (hg.2.2.2.2 y hy).1)
    (le_trans (le_max_right _ _) hx) hxx
  rw [abs_le]; constructor <;> linarith

/-- **Figure 11.2: the binding region is an initial interval**, on which the slope is `1`. If the
borrowing limit binds at `x'` (`c = x' + a/R`) it binds at every `x ∈ [d, x']`. -/
theorem cfn_binding_initial (hV : H.Valid) (n : ℕ) {x x' : ℝ} (hxx : x ≤ x')
    (hbind : H.cons (n + 1) x' = x' + H.b / H.R) :
    H.cons (n + 1) x = x + H.b / H.R ∧ H.cons (n + 1) x' - H.cons (n + 1) x = x' - x := by
  have h1 := cfn_kkt_mono hV (cfn_cons_good hV n) (cfn_cons_kkt hV n x)
    (cfn_cons_kkt hV n _) hxx
  have h2 := (cfn_cons_kkt hV n x).1
  have h3 : H.cons (n + 1) x = x + H.b / H.R := by linarith [h1.2]
  exact ⟨h3, by rw [h3, hbind]; ring⟩

/-! ### The perfect-foresight MPC and the infinite horizon -/

omit [Fintype ι] in
/-- The closed form `κₙ = (1 − ρ)/(1 − ρⁿ⁺¹)`, `ρ = 1/(θR) < 1`. -/
theorem cfn_kappa_eq (hθR : 1 < H.θ * H.R) (n : ℕ) :
    H.kappa n = (1 - 1 / (H.θ * H.R)) / (1 - (1 / (H.θ * H.R)) ^ (n + 1)) := by
  set ρ := 1 / (H.θ * H.R) with hρ
  have hθR0 : 0 < H.θ * H.R := by linarith
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hθR0]; exact hθR
  have hpow : ∀ k : ℕ, ρ ^ (k + 1) < 1 := fun k => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hθR : H.θ * H.R = 1 / ρ := by rw [hρ, one_div_one_div]
  induction n with
  | zero => simp only [kappa, zero_add, pow_one]; rw [div_self (by linarith)]
  | succ n ih =>
    simp only [kappa]
    rw [ih, hθR]
    have h1 := hpow n
    have h2 := hpow (n + 1)
    have h3 : 0 < 1 - ρ ^ (n + 1) := by linarith
    have h4 : 0 < 1 - ρ ^ (n + 1 + 1) := by linarith
    have hA : 0 < 1 - ρ := by linarith
    have h5 : 0 < 1 / ρ * ((1 - ρ) / (1 - ρ ^ (n + 1))) :=
      mul_pos (by positivity) (div_pos hA h3)
    rw [div_eq_div_iff (by linarith) h4.ne']
    field_simp
    ring

omit [Fintype ι] in
/-- **As the horizon grows the perfect-foresight MPC tends to `1 − 1/(θR)`.** -/
theorem cfn_kappa_tendsto (hθR : 1 < H.θ * H.R) :
    Tendsto H.kappa atTop (𝓝 (1 - 1 / (H.θ * H.R))) := by
  have hθR0 : 0 < H.θ * H.R := by linarith
  have hρ0 : 0 ≤ 1 / (H.θ * H.R) := by positivity
  have hρ1 : 1 / (H.θ * H.R) < 1 := by rw [div_lt_one hθR0]; exact hθR
  have hp : Tendsto (fun n : ℕ => (1 / (H.θ * H.R)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x := 1 - 1 / (H.θ * H.R))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp) (by norm_num)
  simp only [sub_zero, div_one] at h
  exact h.congr fun n => (cfn_kappa_eq hθR n).symm

omit [Fintype ι] in
/-- **AKMM, p. 305 (`βR = 1`): the limiting MPC is `r/(1 + r)`.** With `θ = 1` and `R = 1 + r`,
`r > 0`, `κₙ → r/(1 + r)`. -/
theorem cfn_kappa_tendsto_r (hθ : H.θ = 1) {r : ℝ} (hr : 0 < r)
    (hR : H.R = 1 + r) : Tendsto H.kappa atTop (𝓝 (r / (1 + r))) := by
  have h := cfn_kappa_tendsto (by rw [hθ, hR]; linarith)
  have he : 1 - 1 / (H.θ * H.R) = r / (1 + r) := by
    rw [hθ, hR, one_mul]; field_simp; ring
  rwa [he] at h

/-- **Figure 11.2 (`βR = 1`): for large wealth and a long horizon the slope is `r/(1 + r)`.**
For every `ε > 0` there is a horizon `N` such that for every `n ≥ N`, all slopes of `cₙ` beyond
some wealth level are within `ε` of `r/(1 + r)`. -/
theorem cfn_fig_11_2_slope (hV : H.Valid) (hθ : H.θ = 1) {r : ℝ} (hr : 0 < r) (hR : H.R = 1 + r)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∃ X, ∀ x x', X ≤ x → x < x' →
      |(H.cons n x' - H.cons n x) / (x' - x) - r / (1 + r)| ≤ ε := by
  have h := cfn_kappa_tendsto_r hθ hr hR
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨X, hX⟩ := cfn_slope_tendsto hV n (by linarith : 0 < ε / 2)
  refine ⟨X, fun x x' hx hxx => ?_⟩
  have h1 := hX x x' hx hxx
  have h2 := hN n hn
  rw [Real.dist_eq] at h2
  calc |(H.cons n x' - H.cons n x) / (x' - x) - r / (1 + r)|
      ≤ |(H.cons n x' - H.cons n x) / (x' - x) - H.kappa n| + |H.kappa n - r / (1 + r)| :=
        abs_sub_le _ _ _
    _ ≤ ε := by linarith

/-- The perfect-foresight MPC stays above its limit: `1 − 1/(θR) < κₙ`. -/
theorem cfn_kappa_gt (hV : H.Valid) (n : ℕ) : 1 - 1 / (H.θ * H.R) < H.kappa n := by
  have hθR0 : 0 < H.θ * H.R := mul_pos hV.2.1 (by linarith [hV.2.2.1])
  induction n with
  | zero =>
    simp only [kappa]
    have : 0 < 1 / (H.θ * H.R) := by positivity
    linarith
  | succ n ih =>
    simp only [kappa]
    have hq : H.θ * H.R - 1 < H.θ * H.R * H.kappa n := by
      have := mul_lt_mul_of_pos_left ih hθR0
      rw [mul_sub, mul_one, mul_one_div_cancel hθR0.ne'] at this
      exact this
    have hq0 : 0 < 1 + H.θ * H.R * H.kappa n := by
      have := (cfn_kappa_pos hV n).1; positivity
    rw [show 1 - 1 / (H.θ * H.R) = (H.θ * H.R - 1) / (H.θ * H.R) by
        rw [sub_div, div_self hθR0.ne'],
      div_lt_div_iff₀ hθR0 hq0]
    nlinarith

/-- **The impatience condition for a target** (`θ ≥ 1`, i.e. `βR ≤ 1`): `R(1 − κₙ) < 1`. -/
theorem cfn_R_one_sub_kappa_lt (hV : H.Valid) (hθ1 : 1 ≤ H.θ) (n : ℕ) :
    H.R * (1 - H.kappa n) < 1 := by
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  cases n with
  | zero => simp only [kappa]; norm_num
  | succ n =>
    have hgt := cfn_kappa_gt hV n
    have hθR0 : 0 < H.θ * H.R := mul_pos hV.2.1 hR0
    have hk0 := (cfn_kappa_pos hV n).1
    simp only [kappa]
    have hq0 : 0 < 1 + H.θ * H.R * H.kappa n := by positivity
    have h1 : 1 - H.θ * H.R * H.kappa n / (1 + H.θ * H.R * H.kappa n)
        = 1 / (1 + H.θ * H.R * H.kappa n) := by field_simp; ring
    rw [h1, mul_one_div, div_lt_one hq0]
    have h2 : H.θ * H.R - 1 < H.θ * H.R * H.kappa n := by
      have := mul_lt_mul_of_pos_left hgt hθR0
      rw [mul_sub, mul_one, mul_one_div_cancel hθR0.ne'] at this
      exact this
    nlinarith

/-! ### A tighter borrowing limit -/

/-- The household with the tighter borrowing limit `a₂`. -/
def CfnHousehold.tighten (H : CfnHousehold ι) (b₂ : ℝ) : CfnHousehold ι := { H with b := b₂ }

/-- The tighter household satisfies the standing assumptions. -/
theorem cfn_tighten_valid (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) :
    (H.tighten b₂).Valid := by
  obtain ⟨hM, hθ, hR, -, hd, hy, hymax, hw, hw1⟩ := hV
  exact ⟨hM, hθ, hR, hb₂, hd, fun i => by simp only [CfnHousehold.tighten]; linarith [hy i],
    hymax, hw, hw1⟩

/-- **AKMM, p. 306: a tighter limit lowers consumption everywhere.** -/
theorem cfn_tight_le (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : (H.tighten b₂).cons n x ≤ H.cons n x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  induction n generalizing x with
  | zero => simp only [cons]; rfl
  | succ n ih =>
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n x
    have hg := cfn_cons_good hV n
    have hR0 : 0 < H.R := by linarith [hV.2.2.1]
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set c₂ := (H.tighten b₂).cons (n + 1) x
    have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
    have hs₂ : -(H.b / H.R) ≤ x - c₂ := by
      have := hK₂.1; simp only [CfnHousehold.tighten] at this; linarith
    have hint : c < x + H.b / H.R := by
      have := hK₂.1; simp only [CfnHousehold.tighten] at this; linarith
    have he := hK.2.2 hint
    have hm := cfn_cont_mono hV hg hs₂ (by linarith : x - c₂ ≤ x - c)
    -- next period the tight household consumes less
    have hle : (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - c₂)
        ≤ H.cont (H.cons n) (x - c₂) := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => ?_) fun i => ih ?_) hV.2.1.le
      · exact (cfn_cons_good hV₂ n).1 _ (cfn_arg_ge hV₂ (by
          have := hK₂.1; simp only [CfnHousehold.tighten] at this ⊢; linarith) i)
      · exact cfn_arg_ge hV hs₂ i
    linarith [hK₂.2.1]

/-- **The shift bound.** With `Δ = a₁ − a₂` more cash the tight household consumes at least as
much as the loose one (`r ≥ 0`). -/
theorem cfn_tight_shift (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) {x : ℝ}
    (hx : H.d ≤ x) : H.cons n x ≤ (H.tighten b₂).cons n (x + (H.b - b₂)) := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR1 := hV.2.2.1
  have hR0 : 0 < H.R := by linarith
  induction n generalizing x with
  | zero => simp only [cons]; linarith
  | succ n ih =>
    set Δ := H.b - b₂ with hΔ
    have hΔ0 : 0 ≤ Δ := by linarith
    have hxΔ : H.d ≤ x + Δ := by linarith
    have hK := cfn_cons_kkt hV n x
    have hK₂ := cfn_cons_kkt hV₂ n (x + Δ)
    have hg₂ := cfn_cons_good hV₂ n
    by_contra hlt
    push Not at hlt
    set c := H.cons (n + 1) x
    set c₂ := (H.tighten b₂).cons (n + 1) (x + Δ)
    have hs : -(H.b / H.R) ≤ x - c := cfn_save_ge hK.1
    -- the tight household saves more than the loose one plus `Δ`, hence is unconstrained
    have hΔR : Δ / H.R ≤ Δ := div_le_self hΔ0 hR1
    have hbR : H.b / H.R = b₂ / H.R + Δ / H.R := by rw [hΔ]; ring
    have hK1 := hK.1
    have hint : c₂ < x + Δ + (H.tighten b₂).b / H.R := by
      simp only [CfnHousehold.tighten]; linarith
    have he := hK₂.2.2 hint
    -- compare the Euler right-hand sides
    have hge : H.cont (H.cons n) (x - c) ≤ (H.tighten b₂).cont ((H.tighten b₂).cons n)
        (x + Δ - c₂) := by
      simp only [cont, CfnHousehold.tighten]
      refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => (cfn_cons_good hV n).1 _
        (cfn_arg_ge hV hs i)) fun i => ?_) hV.2.1.le
      have hsi := cfn_arg_ge hV hs i
      have htd : (H.tighten b₂).d = H.d := rfl
      refine le_trans (ih hsi) (hg₂.2.1 (Set.mem_Ici.2 (by rw [htd]; linarith))
        (Set.mem_Ici.2 ?_) ?_)
      · have : H.R * (x - c) + Δ ≤ H.R * (x + Δ - c₂) := by nlinarith
        rw [htd]; linarith
      · have : H.R * (x - c) + Δ ≤ H.R * (x + Δ - c₂) := by nlinarith
        linarith
    linarith [hK.2.1]

/-- **AKMM, p. 306: with a tighter limit the household is constrained on a wider range.** Wherever
the loose limit binds, so does the tight one. -/
theorem cfn_tight_binds (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) (x : ℝ)
    (hbind : H.cons (n + 1) x = x + H.b / H.R) :
    (H.tighten b₂).cons (n + 1) x = x + b₂ / H.R := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hK := (cfn_cons_kkt hV n x).2.1
  rw [hbind, show x - (x + H.b / H.R) = -(H.b / H.R) by ring] at hK
  -- the corner Euler inequality carries over through the shift bound
  have hcorner : H.cont (H.cons n) (-(H.b / H.R)) ≤ (H.tighten b₂).cont
      ((H.tighten b₂).cons n) (-(b₂ / H.R)) := by
    simp only [cont, CfnHousehold.tighten]
    refine mul_le_mul_of_nonneg_left (hV.1.1 _ _ (fun i => (cfn_cons_good hV n).1 _
      (cfn_arg_ge hV le_rfl i)) fun i => ?_) hV.2.1.le
    have h1 := cfn_tight_shift hV hb₂ hb n (cfn_arg_ge hV le_rfl i)
    have he : H.R * -(H.b / H.R) + H.y i + (H.b - b₂) = H.R * -(b₂ / H.R) + H.y i := by
      field_simp; ring
    rw [he] at h1
    exact h1
  have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
  have he2 : x - (x + (H.tighten b₂).b / (H.tighten b₂).R) = -(b₂ / H.R) := by
    simp only [CfnHousehold.tighten]; ring
  have hkkt : (H.tighten b₂).KKT ((H.tighten b₂).cons n) x
      (x + (H.tighten b₂).b / (H.tighten b₂).R) := by
    refine ⟨le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
    rw [he2]
    have : x + (H.tighten b₂).b / (H.tighten b₂).R = x + b₂ / H.R := rfl
    rw [this]
    linarith
  exact cfn_step_eq_of_kkt hV₂ (cfn_cons_good hV₂ n) hkkt

/-- **AKMM, p. 306: "as wealth keeps growing, the two consumption functions converge".** They
coincide above some wealth level. -/
theorem cfn_tight_eventually_eq (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) (n : ℕ) :
    ∃ X, H.d ≤ X ∧ ∀ x, X ≤ x → (H.tighten b₂).cons n x = H.cons n x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  induction n with
  | zero => exact ⟨H.d, le_rfl, fun x _ => rfl⟩
  | succ n ih =>
    obtain ⟨X', hX'd, hX'⟩ := ih
    have hg := cfn_cons_good hV (n + 1)
    set κ := H.kappa (n + 1) with hκ
    have hκ1 : κ < 1 := by
      simp only [hκ, kappa]
      have := (cfn_kappa_pos hV n).1
      have : 0 < H.θ * H.R * H.kappa n := mul_pos (mul_pos hV.2.1 hR0) this
      rw [div_lt_one (by linarith)]; linarith
    set h := H.hw (n + 1)
    -- saving exceeds `S` once cash in hand exceeds `X`
    set S := |X'| / H.R + 1 with hS
    set X := max H.d ((S + κ * |h|) / (1 - κ)) with hX
    refine ⟨X, le_max_left _ _, fun x hx => ?_⟩
    have hxd : H.d ≤ x := le_trans (le_max_left _ _) hx
    have hup := (hg.2.2.2.2 x hxd).2
    have hsave : S ≤ x - H.cons (n + 1) x := by
      have h1 : (S + κ * |h|) / (1 - κ) ≤ x := le_trans (le_max_right _ _) hx
      rw [div_le_iff₀ (by linarith)] at h1
      have := (cfn_kappa_pos hV (n + 1)).1
      nlinarith [le_abs_self h, mul_le_mul_of_nonneg_left (le_abs_self h) this.le]
    have hS1 : 1 ≤ S := by
      have : 0 ≤ |X'| / H.R := by positivity
      linarith
    have hK := cfn_cons_kkt hV n x
    have hbR : 0 ≤ b₂ / H.R := div_nonneg hb₂ hR0.le
    have hint : H.cons (n + 1) x < x + b₂ / H.R := by linarith
    have hint₁ : H.cons (n + 1) x < x + H.b / H.R := by
      have : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
      linarith
    have he := hK.2.2 hint₁
    refine cfn_step_eq_of_kkt hV₂ (cfn_cons_good hV₂ n) ⟨?_, ?_, fun _ => ?_⟩
    · simp only [CfnHousehold.tighten]; exact hint.le
    · have : (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - H.cons (n + 1) x)
          = H.cont (H.cons n) (x - H.cons (n + 1) x) := by
        simp only [cont, CfnHousehold.tighten]
        congr 2
        funext i
        refine hX' _ ?_
        have : |X'| ≤ H.R * (x - H.cons (n + 1) x) - H.R := by
          have h2 := mul_le_mul_of_nonneg_left hsave hR0.le
          rw [hS, mul_add, mul_div_cancel₀ _ hR0.ne', mul_one] at h2
          linarith
        have hyi : 0 ≤ H.y i := by linarith [hV.2.2.2.2.2.1 i, hV.2.2.2.2.1, hV.2.2.2.1]
        linarith [le_abs_self X']
      rw [this, ← he]
    · have : (H.tighten b₂).cont ((H.tighten b₂).cons n) (x - H.cons (n + 1) x)
          = H.cont (H.cons n) (x - H.cons (n + 1) x) := by
        simp only [cont, CfnHousehold.tighten]
        congr 2
        funext i
        refine hX' _ ?_
        have : |X'| ≤ H.R * (x - H.cons (n + 1) x) - H.R := by
          have h2 := mul_le_mul_of_nonneg_left hsave hR0.le
          rw [hS, mul_add, mul_div_cancel₀ _ hR0.ne', mul_one] at h2
          linarith
        have hyi : 0 ≤ H.y i := by linarith [hV.2.2.2.2.2.1 i, hV.2.2.2.2.1, hV.2.2.2.1]
        linarith [le_abs_self X']
      rw [this, ← he]

/-- **AKMM, p. 306: a tighter limit raises the MPC**, one period before the end (the two-period
problem): on every interval of cash in hand the tight household's consumption rises at least as
much as the loose household's. -/
theorem cfn_tight_mpc_last (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b) {x x' : ℝ}
    (hx : H.d ≤ x) (hxx : x ≤ x') :
    H.cons 1 x' - H.cons 1 x ≤ (H.tighten b₂).cons 1 x' - (H.tighten b₂).cons 1 x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hx' : H.d ≤ x' := le_trans hx hxx
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have hg := cfn_cons_good hV 0
  have hlip := hg.2.2.1 x x' hx hxx
  have hle := cfn_tight_le hV hb₂ hb 1 hx
  by_cases hbind : (H.tighten b₂).cons 1 x' = x' + b₂ / H.R
  · -- the tight household is constrained at `x'`, hence at `x`
    have h := cfn_binding_initial hV₂ 0 hxx (by simpa only [CfnHousehold.tighten] using hbind)
    have := (cfn_cons_good hV 1).2.2.1 x x' hx hxx
    linarith [h.2]
  · -- the tight household is unconstrained at `x'`, so it consumes as the loose one does
    have hK₂ := cfn_cons_kkt hV₂ 0 x'
    have hint : (H.tighten b₂).cons 1 x' < x' + b₂ / H.R := by
      have := hK₂.1; simp only [CfnHousehold.tighten] at this
      exact lt_of_le_of_ne this hbind
    have he := hK₂.2.2 (by simpa only [CfnHousehold.tighten] using hint)
    have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
    have heq : H.cons 1 x' = (H.tighten b₂).cons 1 x' := by
      exact cfn_step_eq_of_kkt hV hg ⟨by linarith, le_of_eq (he.trans rfl),
        fun _ => he.trans rfl⟩
    linarith

/-- **Correction to AKMM, p. 306** ("for unconstrained households, consumption falls across the
board"). One period before the end a tighter limit does not lower the consumption of a household
it leaves unconstrained at all: there the two consumption functions coincide. Together with
`cfn_tight_eventually_eq` (such cash in hand exists) the fall is only weak. -/
theorem cfn_tight_eq_unconstrained_last (hV : H.Valid) {b₂ : ℝ} (hb₂ : 0 ≤ b₂) (hb : b₂ ≤ H.b)
    {x : ℝ} (hint : (H.tighten b₂).cons 1 x < x + b₂ / H.R) :
    (H.tighten b₂).cons 1 x = H.cons 1 x := by
  have hV₂ := cfn_tighten_valid hV hb₂ hb
  have hR0 : 0 < H.R := by linarith [hV.2.2.1]
  have he := (cfn_cons_kkt hV₂ 0 x).2.2 (by simpa only [CfnHousehold.tighten] using hint)
  have hbb : b₂ / H.R ≤ H.b / H.R := div_le_div_of_nonneg_right hb hR0.le
  exact (cfn_step_eq_of_kkt hV (cfn_cons_good hV 0) ⟨by linarith, le_of_eq (he.trans rfl),
    fun _ => he.trans rfl⟩).symm

/-! ### Instances: quadratic and CRRA utility -/

omit [Fintype ι] in
/-- **(11.33) in compound form.** The Kuhn–Tucker conditions say exactly
`c = min{x + a/R, θM(cn(R(x − c) + yᵢ))}`. -/
theorem cfn_kkt_iff_min (H : CfnHousehold ι) (cn : ℝ → ℝ) (x c : ℝ) :
    H.KKT cn x c ↔ c = min (x + H.b / H.R) (H.cont cn (x - c)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases lt_or_eq_of_le h1 with hlt | heq
    · rw [← h3 hlt, min_eq_right (h3 hlt ▸ h1)]
    · rw [min_eq_left (heq ▸ h2), heq]
  · intro h
    refine ⟨(le_of_eq h).trans (min_le_left _ _), (le_of_eq h).trans (min_le_right _ _),
      fun hlt => ?_⟩
    rcases min_choice (x + H.b / H.R) (H.cont cn (x - c)) with hm | hm
    · rw [hm] at h; linarith
    · rw [hm] at h; exact h

/-- The household with quadratic utility and `βR = 1` (the book's case): `M` is the expectation
and `θ = 1`. -/
def cfn_quadratic (w y : ι → ℝ) (R b d ymax : ℝ) : CfnHousehold ι :=
  { M := fun z => ∑ i, w i * z i, θ := 1, R := R, b := b, d := d, y := y, ymax := ymax, w := w }

/-- **AKMM, (11.33), p. 305.** For quadratic utility with `βR = 1` the Kuhn–Tucker conditions are
`cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}` (with `x = yₜ + aₜ`). -/
theorem cfn_quadratic_kkt_iff (w y : ι → ℝ) (R b d ymax : ℝ) (cn : ℝ → ℝ) (x c : ℝ) :
    (cfn_quadratic w y R b d ymax).KKT cn x c ↔
      c = min (x + b / R) (∑ i, w i * cn (R * (x - c) + y i)) := by
  rw [cfn_kkt_iff_min]
  simp only [cont, cfn_quadratic, one_mul]

/-- The quadratic household satisfies the standing assumptions. -/
theorem cfn_quadratic_valid {w y : ι → ℝ} {R b d ymax : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hR : 1 ≤ R) (hb : 0 ≤ b) (hd : 0 < d) (hy : ∀ i, d + b ≤ y i)
    (hymax : ∀ i, y i ≤ ymax) : (cfn_quadratic w y R b d ymax).Valid :=
  ⟨cfn_isMean_expect hw hw1, one_pos, hR, hb, hd, hy, hymax, hw, hw1⟩

/-- The CRRA household: `M` is the power mean with exponent `−σ`, `θ = (βR)^{−1/σ}`. -/
noncomputable def cfn_crra (β σ : ℝ) (w y : ι → ℝ) (R b d ymax : ℝ) : CfnHousehold ι :=
  { M := LeanEconomics.powerMean w (-σ), θ := (β * R) ^ (-(1 / σ)), R := R, b := b, d := d,
    y := y, ymax := ymax, w := w }

/-- The CRRA household satisfies the standing assumptions. -/
theorem cfn_crra_valid {β σ : ℝ} {w y : ι → ℝ} {R b d ymax : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hR : 1 ≤ R) (hb : 0 ≤ b) (hd : 0 < d)
    (hy : ∀ i, d + b ≤ y i) (hymax : ∀ i, y i ≤ ymax) :
    (cfn_crra β σ w y R b d ymax).Valid :=
  ⟨cfn_isMean_powerMean hw hw1 (neg_neg_of_pos hσ),
    Real.rpow_pos_of_pos (mul_pos hβ (by linarith)) _, hR, hb, hd, hy, hymax, hw, hw1⟩

/-- **The CRRA Euler inequality.** For positive `c` and next-period consumptions `zᵢ`,
`c ≤ (βR)^{−1/σ}M₋σ(z)` iff `u′(c) = c^{−σ} ≥ βR Σᵢ wᵢ zᵢ^{−σ} = βR E u′(z)`, with equality iff
equality. -/
theorem cfn_crra_euler_iff {β σ R : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hR : 0 < R) {w z : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hz : ∀ i, 0 < z i) {c : ℝ} (hc : 0 < c) :
    (c ≤ (β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z ↔
      β * R * ∑ i, w i * z i ^ (-σ) ≤ c ^ (-σ)) ∧
    (c = (β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z ↔
      c ^ (-σ) = β * R * ∑ i, w i * z i ^ (-σ)) := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hP := LeanEconomics.powerMean_pos (p := -σ) hw hw1 hz
  have hK : 0 < (β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z :=
    mul_pos (Real.rpow_pos_of_pos hβR _) hP
  have hpow : ((β * R) ^ (-(1 / σ)) * LeanEconomics.powerMean w (-σ) z) ^ (-σ)
      = β * R * ∑ i, w i * z i ^ (-σ) := by
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hβR _).le hP.le, ← Real.rpow_mul hβR.le,
      LeanEconomics.powerMean_rpow (neg_ne_zero.2 hσ.ne') hw hw1 hz]
    congr 1
    rw [show -(1 / σ) * -σ = 1 by field_simp, Real.rpow_one]
  constructor
  · rw [← hpow, Real.rpow_le_rpow_iff_of_neg hK hc (neg_neg_of_pos hσ)]
  · rw [← hpow]
    constructor
    · intro h; rw [← h]
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := Real.rpow_lt_rpow_of_neg hc hlt (neg_neg_of_pos hσ); linarith
      · have := Real.rpow_lt_rpow_of_neg hK hlt (neg_neg_of_pos hσ); linarith

/-- For CRRA, `θ = (βR)^{−1/σ} ≥ 1` iff `βR ≤ 1` (the discount rate is at least the interest
rate). -/
theorem cfn_crra_theta_ge_one_iff {β σ R : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hR : 0 < R) :
    1 ≤ (β * R) ^ (-(1 / σ)) ↔ β * R ≤ 1 := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hs : -(1 / σ) < 0 := neg_neg_of_pos (by positivity)
  constructor
  · intro h
    by_contra hgt
    push Not at hgt
    have := Real.rpow_lt_one_of_one_lt_of_neg hgt hs
    linarith
  · intro h
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hβR h hs.le

/-- **For CRRA the limiting MPC is (11.16)**: `1 − 1/(θR) = 1 − R⁻¹(βR)^{1/σ}` (`cd_mpc`). -/
theorem cfn_crra_kappa_limit {β σ : ℝ} {w y : ι → ℝ} {R b d ymax : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    1 - 1 / ((cfn_crra β σ w y R b d ymax).θ * (cfn_crra β σ w y R b d ymax).R) =
      cd_mpc β R σ := by
  simp only [cfn_crra, cd_mpc]
  have hβR : 0 < β * R := mul_pos hβ hR
  rw [Real.rpow_neg hβR.le, one_div, mul_inv, inv_inv]
  ring

/-- **A concrete instance**: the quadratic household with income `1` or `3` with equal
probability, `R = 1.02`, `a = 1/2`, `d = 1/2`, satisfies the standing assumptions, so every
theorem above applies to it. -/
theorem cfn_example_valid :
    (cfn_quadratic (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 3] (102 / 100) (1 / 2) (1 / 2) 3).Valid := by
  refine cfn_quadratic_valid (fun _ => by norm_num) (by simp) (by norm_num) (by norm_num)
    (by norm_num) (fun i => ?_) (fun i => ?_)
  · fin_cases i <;> norm_num
  · fin_cases i <;> norm_num

end AKMM.Consumption
