/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.KUKoopmans
import RecursiveUtility.SSCertaintyEquivalents
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The Chew–Dekel risk aggregator (§20.2.1, (20.6))

Miao §20.2.1, pp. 687–691: static preferences over consumption `c : S → ℝ₊` on a finite state
space with probabilities `p`, their certainty equivalents, the Allais paradox, the Chew–Dekel
class (20.6) and its members, and their recursive versions.

* `ku_ce_unique`, `ku_ce_exists`, `ku_ce_counterexample`: if `U` is strictly increasing along
  constants the certainty equivalent `μ` with `U(μ, …, μ) = U(c)` is unique; it exists when in
  addition `U` is monotone and continuous along constants; without continuity it may not exist,
  although the book's "If `U` is strictly increasing, then there is a unique `μ`" says it does.
* `ku_allais`, `ku_allais_u0`, `ku_allais_paradox`: under expected utility `a₁ ≽ a₂` iff
  `a₃ ≽ a₄` (the printed display, with `u(0) = 0`, lacks the `≥`); hence `a₁ ≻ a₂` and `a₄ ≻ a₃`
  cannot both hold.
* `eq_20_6`: the Chew–Dekel equation `μ = ∑ p(s)M(c(s), μ)`.
* Expected utility `M(c, m) = c^αm^{1−α}/α + m(1 − 1/α)`: properties (i)–(iv)
  (`ku_euM_i`, `ku_euM_ii`, `ku_euM_iii`, `ku_euM_iv`) and `μ = (∑ p c^α)^{1/α}`
  (`ku_euM_ce`). Property (iv) holds as `M(kc, km) = kM(c, m)`; as printed, `M(kc, m) = kM(c, m)`,
  it fails (`ku_euM_iv_misprint`).
* Weighted utility: `ku_wM_i`, `ku_wM_ce` (`μ = (∑ p c^{γ+α}/∑ p c^γ)^{1/α} = (∑ p̂ c^α)^{1/α}`),
  `ku_wM_params` (the parameter implications), `ku_wM_local` (`∂M/∂c = 1` and
  `∂²M/∂c² = (α + 2γ − 1)/m` at `c = m`, so (i) or (ii) gives local concavity), and
  `ku_wM_params_not_necessary` (`γ = 0`, `α = 1/2` is increasing and concave though neither (i)
  nor (ii) holds: the conditions are sufficient, not necessary).
* Disappointment aversion: `ku_gulM_i`, `ku_gulM_zero` (`δ = 0` is expected utility),
  `ku_gulM_ce` (`μ^α = ∑ p c^α − δ ∑ p 1(c < μ)(μ^α − c^α)`), `ku_gulM_ce_hat` (`= ∑ p̂ c^α` with
  `p̂(s) = p(s)(1 + δ1(c(s) < μ))/(1 + δ∑ p 1(c < μ))`; the printed `p̂` omits the factor `p(s)`,
  `ku_gulM_hat_misprint`).
* `ku_recWeighted_ce`, `ku_recWeighted`, `ku_recGul`: the recursive weighted and disappointment
  aversion utilities use the static certainty equivalents at each node, with `p = π(·|s_t)`.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-! ### Certainty equivalents and the Allais paradox -/

omit [Fintype S] in
/-- Miao, p. 688: if `m ↦ U(m, …, m)` is strictly increasing, the certainty equivalent is unique. -/
theorem ku_ce_unique {U : (S → ℝ) → ℝ} (hU : StrictMono fun m : ℝ => U fun _ => m)
    {c : S → ℝ} {μ μ' : ℝ} (h : U (fun _ => μ) = U c) (h' : U (fun _ => μ') = U c) : μ = μ' :=
  hU.injective (h.trans h'.symm)

omit [Fintype S] in
/-- Miao, p. 688: if `U` is monotone and continuous along constants, the certainty equivalent
`μ` with `U(μ, …, μ) = U(c)` exists, between `min c` and `max c`. -/
theorem ku_ce_exists [Finite S] [Nonempty S] {U : (S → ℝ) → ℝ} (hmono : Monotone U)
    (hcont : Continuous fun m : ℝ => U fun _ => m) (c : S → ℝ) :
    ∃ μ, U (fun _ => μ) = U c := by
  have := Fintype.ofFinite S
  set m₀ := Finset.univ.inf' Finset.univ_nonempty c
  set m₁ := Finset.univ.sup' Finset.univ_nonempty c
  have h0 : (fun _ : S => m₀) ≤ c := fun s => Finset.inf'_le _ (Finset.mem_univ s)
  have h1 : c ≤ fun _ : S => m₁ := fun s => Finset.le_sup' c (Finset.mem_univ s)
  have h01 : m₀ ≤ m₁ := (h0 (Classical.arbitrary S)).trans (h1 (Classical.arbitrary S))
  obtain ⟨μ, _, hμ⟩ := intermediate_value_Icc h01 hcont.continuousOn ⟨hmono h0, hmono h1⟩
  exact ⟨μ, hμ⟩

/-- Counterexample (Miao, p. 688): a utility strictly increasing in each state need not have a
certainty equivalent. With two states and `f(x) = x + 1` for `x > 0`, `f(x) = x` otherwise,
`U(c) = f(c₁) + f(c₂)` is strictly increasing, but `U(1, 0) = 2 ≠ 2f(μ)` for every `μ`. -/
theorem ku_ce_counterexample :
    let f : ℝ → ℝ := fun x => if 0 < x then x + 1 else x
    let U : (Bool → ℝ) → ℝ := fun c => ∑ b, f (c b)
    (∀ c c' : Bool → ℝ, c ≤ c' → c ≠ c' → U c < U c') ∧
      ¬ ∃ μ, U (fun _ => μ) = U fun b => if b then 1 else 0 := by
  intro f U
  have hf : StrictMono f := by
    intro x y hxy
    simp only [f]
    split_ifs <;> linarith
  refine ⟨fun c c' hle hne => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, c b ≠ c' b := by
      by_contra h
      push Not at h
      exact hne (funext h)
    exact Finset.sum_lt_sum (fun i _ => hf.monotone (hle i))
      ⟨b, Finset.mem_univ _, hf (lt_of_le_of_ne (hle b) hb)⟩
  · rintro ⟨μ, hμ⟩
    simp only [U, f, Fintype.univ_bool] at hμ
    norm_num at hμ
    split_ifs at hμ with h <;> linarith

/-- Miao, p. 687: the Allais choices under expected utility. With `u₁ = u(1M)`, `u₅ = u(5M)`,
`u₀ = u(0)`: `a₁ ≽ a₂` iff `a₃ ≽ a₄`. -/
theorem ku_allais (u₁ u₅ u₀ : ℝ) :
    (0.1 * u₅ + 0.89 * u₁ + 0.01 * u₀ ≤ u₁) ↔ (0.1 * u₅ + 0.9 * u₀ ≤ 0.11 * u₁ + 0.89 * u₀) := by
  constructor <;> intro h <;> linarith

/-- Miao, p. 687 (corrected display): with `u(0) = 0`,
`u(1M) ≥ 0.1u(5M) + 0.89u(1M)` iff `0.11u(1M) ≥ 0.1u(5M)`. -/
theorem ku_allais_u0 (u₁ u₅ : ℝ) : (0.1 * u₅ + 0.89 * u₁ ≤ u₁) ↔ (0.1 * u₅ ≤ 0.11 * u₁) := by
  constructor <;> intro h <;> linarith

/-- Miao, p. 688: the Allais paradox: no expected utility gives `a₁ ≻ a₂` and `a₄ ≻ a₃`. -/
theorem ku_allais_paradox (u₁ u₅ u₀ : ℝ) :
    ¬ ((0.1 * u₅ + 0.89 * u₁ + 0.01 * u₀ < u₁) ∧
      (0.11 * u₁ + 0.89 * u₀ < 0.1 * u₅ + 0.9 * u₀)) := by
  rintro ⟨h1, h2⟩
  linarith

/-! ### The Chew–Dekel class -/

/-- A probability-weighted sum of positive numbers is positive. -/
theorem ku_wsum_pos {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {f : S → ℝ}
    (hf : ∀ s, 0 < f s) : 0 < ∑ s, p s * f s := by
  obtain ⟨s, hs⟩ : ∃ s, 0 < p s := by
    by_contra h
    push Not at h
    have : ∑ s, p s = 0 := Finset.sum_eq_zero fun s _ => le_antisymm (h s) (hp s)
    linarith
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hp i) (hf i).le)
    ⟨s, Finset.mem_univ _, mul_pos hs (hf s)⟩

/-- Miao, (20.6), p. 688: `μ` is the Chew–Dekel certainty equivalent of `c` for the risk aggregator
`M`: `μ = ∑ p(s)M(c(s), μ)`. -/
def eq_20_6 (p : S → ℝ) (M : ℝ → ℝ → ℝ) (c : S → ℝ) (μ : ℝ) : Prop :=
  μ = ∑ s, p s * M (c s) μ

/-- The expected-utility risk aggregator `M(c, m) = c^αm^{1−α}/α + m(1 − 1/α)` (p. 689). -/
noncomputable def ku_euM (α c m : ℝ) : ℝ := c ^ α * m ^ (1 - α) / α + m * (1 - 1 / α)

/-- Miao, p. 689, property (i): `M(m, m) = m`. -/
theorem ku_euM_i {α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) : ku_euM α m m = m := by
  unfold ku_euM
  rw [← Real.rpow_add hm, add_sub_cancel, Real.rpow_one]
  field_simp
  ring

/-- Miao, p. 689, property (ii): `M` is (strictly) increasing in `c`. -/
theorem ku_euM_ii {α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) :
    StrictMonoOn (fun c => ku_euM α c m) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hmα := Real.rpow_pos_of_pos hm (1 - α)
  simp only [ku_euM]
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : y ^ α < x ^ α := Real.rpow_lt_rpow_of_neg hx0 hxy hneg
    have h2 : x ^ α * m ^ (1 - α) / α < y ^ α * m ^ (1 - α) / α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_neg_right (mul_lt_mul_of_pos_right h1 hmα) (inv_lt_zero.2 hneg)
    linarith
  · have h1 : x ^ α < y ^ α := Real.rpow_lt_rpow hx0.le hxy hpos
    have h2 : x ^ α * m ^ (1 - α) / α < y ^ α * m ^ (1 - α) / α :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h1 hmα) hpos
    linarith

/-- Miao, p. 689, property (iii): for `α ≤ 1`, `M` is concave in `c`. -/
theorem ku_euM_iii {α m : ℝ} (hα : α ≠ 0) (hα1 : α ≤ 1) (hm : 0 < m) :
    ConcaveOn ℝ (Set.Ioi 0) (fun c => ku_euM α c m) := by
  have hmα := Real.rpow_pos_of_pos hm (1 - α)
  have e : (fun c => ku_euM α c m) = fun c => (m ^ (1 - α) / α) • c ^ α + m * (1 - 1 / α) := by
    funext c
    simp only [ku_euM, smul_eq_mul]
    ring
  rw [e]
  refine ConcaveOn.add_const ?_ _
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have hK : 0 ≤ -(m ^ (1 - α) / α) := by
      have : m ^ (1 - α) / α < 0 := div_neg_of_pos_of_neg hmα hneg
      linarith
    have h1 := (SS.convexOn_rpow_of_neg hneg).smul hK
    have h2 := neg_concaveOn_iff.2 h1
    convert h2 using 1
    funext c
    simp
  · exact ((Real.concaveOn_rpow hpos.le hα1).subset Set.Ioi_subset_Ici_self
      (convex_Ioi 0)).smul (div_pos hmα hpos).le

/-- Miao, p. 689, property (iv) (corrected): linear homogeneity `M(kc, km) = kM(c, m)`. -/
theorem ku_euM_iv {α k c m : ℝ} (hk : 0 < k) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    ku_euM α (k * c) (k * m) = k * ku_euM α c m := by
  unfold ku_euM
  rw [Real.mul_rpow hk.le hc, Real.mul_rpow hk.le hm,
    show k ^ α * c ^ α * (k ^ (1 - α) * m ^ (1 - α)) =
      (k ^ α * k ^ (1 - α)) * (c ^ α * m ^ (1 - α)) by ring,
    ← Real.rpow_add hk, add_sub_cancel, Real.rpow_one]
  ring

/-- Miao, p. 689 (misprint): property (iv) as printed, `M(kc, m) = kM(c, m)`, fails for the
expected-utility aggregator (`α = −1`, `k = 2`, `c = m = 1`). -/
theorem ku_euM_iv_misprint : ku_euM (-1) (2 * 1) 1 ≠ 2 * ku_euM (-1) 1 1 := by
  unfold ku_euM
  rw [mul_one, Real.rpow_neg_one, Real.one_rpow, Real.one_rpow]
  norm_num

/-- Miao, p. 689: for the expected-utility aggregator, (20.6) holds iff
`μ = (∑ p(s)c(s)^α)^{1/α}`. -/
theorem ku_euM_ce {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {α : ℝ} (hα : α ≠ 0)
    {c : S → ℝ} (hc : ∀ s, 0 < c s) {μ : ℝ} (hμ : 0 < μ) :
    eq_20_6 p (ku_euM α) c μ ↔ μ = (∑ s, p s * c s ^ α) ^ α⁻¹ := by
  set A := ∑ s, p s * c s ^ α
  have hA : 0 < A :=
    ku_wsum_pos hp hp1 fun s => Real.rpow_pos_of_pos (hc s) _
  have hb := Real.rpow_pos_of_pos hμ α
  have e1 : μ ^ (1 - α) = μ / μ ^ α := by rw [Real.rpow_sub hμ, Real.rpow_one]
  have hsum : ∑ s, p s * ku_euM α (c s) μ = μ / μ ^ α * A / α + μ * (1 - 1 / α) := by
    have : ∀ s, p s * ku_euM α (c s) μ =
        μ / μ ^ α / α * (p s * c s ^ α) + μ * (1 - 1 / α) * p s := fun s => by
      simp only [ku_euM, e1]
      ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, A]
    ring
  unfold eq_20_6
  rw [hsum]
  constructor
  · intro h
    have h2 : μ ^ α = A := by
      have h4 : μ * (1 - 1 / α) = μ - μ / α := by ring
      have h3 : μ / α = μ / μ ^ α * A / α := by linarith
      field_simp at h3
      linarith
    rw [← h2, Real.rpow_rpow_inv hμ.le hα]
  · intro h
    have h2 : μ ^ α = A := by rw [h, Real.rpow_inv_rpow hA.le hα]
    rw [h2]
    field_simp
    ring

/-! ### Weighted utility -/

/-- Chew's weighted-utility risk aggregator
`M(c, m) = (c/m)^γ c^αm^{1−α}/α + m(1 − (c/m)^γ/α)` (p. 689). -/
noncomputable def ku_wM (γ α c m : ℝ) : ℝ :=
  (c / m) ^ γ * c ^ α * m ^ (1 - α) / α + m * (1 - (c / m) ^ γ / α)

/-- Miao, p. 689: property (i) for weighted utility, `M(m, m) = m`. -/
theorem ku_wM_i {γ α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) : ku_wM γ α m m = m := by
  unfold ku_wM
  rw [div_self hm.ne', Real.one_rpow, one_mul, ← Real.rpow_add hm, add_sub_cancel,
    Real.rpow_one]
  field_simp
  ring

/-- With `γ = 0` weighted utility is expected utility. -/
theorem ku_wM_zero (α c m : ℝ) : ku_wM 0 α c m = ku_euM α c m := by
  simp [ku_wM, ku_euM]

/-- Miao, p. 689: for weighted utility, (20.6) holds iff
`μ = (∑ p c^{γ+α}/∑ p c^γ)^{1/α}`, and this equals `(∑ p̂ c^α)^{1/α}` with
`p̂(s) = p(s)c(s)^γ/∑ p c^γ`. -/
theorem ku_wM_ce {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {γ α : ℝ} (hα : α ≠ 0)
    {c : S → ℝ} (hc : ∀ s, 0 < c s) {μ : ℝ} (hμ : 0 < μ) :
    (eq_20_6 p (ku_wM γ α) c μ ↔
      μ = ((∑ s, p s * c s ^ (γ + α)) / ∑ s, p s * c s ^ γ) ^ α⁻¹) ∧
      (∑ s, p s * c s ^ (γ + α)) / (∑ s, p s * c s ^ γ) =
        ∑ s, (p s * c s ^ γ / ∑ s', p s' * c s' ^ γ) * c s ^ α := by
  have hpos : ∀ e : ℝ, 0 < ∑ s, p s * c s ^ e := fun e =>
    ku_wsum_pos hp hp1 fun s => Real.rpow_pos_of_pos (hc s) _
  set A := ∑ s, p s * c s ^ (γ + α)
  set B := ∑ s, p s * c s ^ γ
  have hA := hpos (γ + α)
  have hB : 0 < B := hpos γ
  have ha := Real.rpow_pos_of_pos hμ (-γ)
  have hb := Real.rpow_pos_of_pos hμ (-α)
  have e1 : ∀ s, (c s / μ) ^ γ = c s ^ γ * μ ^ (-γ) := fun s => by
    rw [Real.div_rpow (hc s).le hμ.le, Real.rpow_neg hμ.le, div_eq_mul_inv]
  have e2 : μ ^ (1 - α) = μ * μ ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hμ, Real.rpow_one]
  have e3 : ∀ s, c s ^ γ * c s ^ α = c s ^ (γ + α) := fun s => (Real.rpow_add (hc s) _ _).symm
  have hsum : ∑ s, p s * ku_wM γ α (c s) μ =
      μ ^ (-γ) * μ * μ ^ (-α) * A / α + μ - μ * μ ^ (-γ) * B / α := by
    simp only [ku_wM, e1, e2]
    have : ∀ s, p s * (c s ^ γ * μ ^ (-γ) * c s ^ α * (μ * μ ^ (-α)) / α +
        μ * (1 - c s ^ γ * μ ^ (-γ) / α)) =
        μ ^ (-γ) * μ * μ ^ (-α) / α * (p s * (c s ^ γ * c s ^ α)) + μ * p s -
          μ * μ ^ (-γ) / α * (p s * c s ^ γ) := fun s => by ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, e3,
      hp1, A, B]
    ring
  refine ⟨?_, ?_⟩
  · unfold eq_20_6
    rw [hsum]
    have key : μ = μ ^ (-γ) * μ * μ ^ (-α) * A / α + μ - μ * μ ^ (-γ) * B / α ↔
        μ ^ (-α) * A = B := by
      constructor
      · intro h
        have h1 : μ ^ (-γ) * μ * (μ ^ (-α) * A - B) / α =
            (μ ^ (-γ) * μ * μ ^ (-α) * A / α + μ - μ * μ ^ (-γ) * B / α) - μ := by ring
        rw [← h, sub_self] at h1
        rcases div_eq_zero_iff.1 h1 with h2 | h2
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · rcases mul_eq_zero.1 h3 with h4 | h4
            · exact absurd h4 ha.ne'
            · exact absurd h4 hμ.ne'
          · linarith
        · exact absurd h2 hα
      · intro h
        have : μ ^ (-γ) * μ * μ ^ (-α) * A = μ * μ ^ (-γ) * B := by rw [← h]; ring
        rw [this]
        ring
    rw [key]
    have hma : μ ^ (-α) = (μ ^ α)⁻¹ := Real.rpow_neg hμ.le α
    have hmα := Real.rpow_pos_of_pos hμ α
    constructor
    · intro h
      have h2 : μ ^ α = A / B := by
        rw [hma] at h
        field_simp at h
        rw [eq_div_iff hB.ne']
        linarith
      rw [← h2, Real.rpow_rpow_inv hμ.le hα]
    · intro h
      have h2 : μ ^ α = A / B := by rw [h, Real.rpow_inv_rpow (div_pos hA hB).le hα]
      rw [hma, h2]
      field_simp
      exact div_self hA.ne'
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← e3 s]
    ring

/-- Miao, p. 689: the parameter conditions for weighted utility: (i) `0 < γ < 1`, `α + γ < 0`
implies `α < 0`; (ii) `γ < 0`, `0 < α + γ < 1` implies `α > 0`; both imply `α + 2γ < 1`. -/
theorem ku_wM_params {γ α : ℝ} :
    ((0 < γ ∧ γ < 1 ∧ α + γ < 0) → α < 0 ∧ α + 2 * γ < 1) ∧
      ((γ < 0 ∧ 0 < α + γ ∧ α + γ < 1) → 0 < α ∧ α + 2 * γ < 1) := by
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨by linarith, by linarith⟩,
    fun ⟨h1, h2, h3⟩ => ⟨by linarith, by linarith⟩⟩

/-- The weighted aggregator in power form, `M(c, m) = c^{γ+α}m^{1−α−γ}/α + m − c^γm^{1−γ}/α`. -/
theorem ku_wM_eq {γ α c m : ℝ} (hc : 0 < c) (hm : 0 < m) :
    ku_wM γ α c m = c ^ (γ + α) * m ^ (1 - α - γ) / α + m - c ^ γ * m ^ (1 - γ) / α := by
  unfold ku_wM
  have e1 : (c / m) ^ γ = c ^ γ * m ^ (-γ) := by
    rw [Real.div_rpow hc.le hm.le, Real.rpow_neg hm.le, div_eq_mul_inv]
  have e2 : c ^ (γ + α) = c ^ γ * c ^ α := Real.rpow_add hc _ _
  have e3 : m ^ (1 - α - γ) = m ^ (-γ) * m ^ (1 - α) := by
    rw [← Real.rpow_add hm]; ring_nf
  have e4 : m ^ (1 - γ) = m * m ^ (-γ) := by
    rw [sub_eq_add_neg, Real.rpow_add hm, Real.rpow_one]
  rw [e1, e2, e3, e4]
  ring

/-- Miao, p. 689: near `c = m` the weighted aggregator has slope `1` and curvature
`(α + 2γ − 1)/m`; so (i) or (ii) (which give `α + 2γ < 1`, `ku_wM_params`) makes `M` increasing
and strictly concave in `c` near `m`. -/
theorem ku_wM_local {γ α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) :
    ∃ D : ℝ → ℝ, (∀ c, 0 < c → HasDerivAt (fun c => ku_wM γ α c m) (D c) c) ∧ D m = 1 ∧
      HasDerivAt D ((α + 2 * γ - 1) / m) m := by
  let D : ℝ → ℝ := fun c => ((γ + α) * c ^ (γ + α - 1) * m ^ (1 - α - γ) -
    γ * c ^ (γ - 1) * m ^ (1 - γ)) / α
  refine ⟨D, fun c hc => ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun c => c ^ (γ + α) * m ^ (1 - α - γ) / α + m -
        c ^ γ * m ^ (1 - γ) / α) (D c) c := by
      have ha := ((Real.hasDerivAt_rpow_const (p := γ + α) (Or.inl hc.ne')).mul_const
        (m ^ (1 - α - γ))).div_const α
      have hb := ((Real.hasDerivAt_rpow_const (p := γ) (Or.inl hc.ne')).mul_const
        (m ^ (1 - γ))).div_const α
      convert (ha.add_const m).sub hb using 1
      simp only [D]
      ring
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hc] with x hx
    exact ku_wM_eq hx hm
  · have e1 : m ^ (γ + α - 1) * m ^ (1 - α - γ) = 1 := by
      rw [← Real.rpow_add hm, show γ + α - 1 + (1 - α - γ) = 0 by ring, Real.rpow_zero]
    have e2 : m ^ (γ - 1) * m ^ (1 - γ) = 1 := by
      rw [← Real.rpow_add hm, show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero]
    simp only [D]
    rw [mul_assoc (γ + α), e1, mul_assoc γ, e2]
    field_simp
    ring
  · have ha := ((Real.hasDerivAt_rpow_const (p := γ + α - 1) (Or.inl hm.ne')).const_mul
      (γ + α)).mul_const (m ^ (1 - α - γ))
    have hb := ((Real.hasDerivAt_rpow_const (p := γ - 1) (Or.inl hm.ne')).const_mul γ).mul_const
      (m ^ (1 - γ))
    convert (ha.sub hb).div_const α using 1
    have e1 : m ^ (γ + α - 1 - 1) * m ^ (1 - α - γ) = m⁻¹ := by
      rw [← Real.rpow_add hm, show γ + α - 1 - 1 + (1 - α - γ) = -1 by ring, Real.rpow_neg_one]
    have e2 : m ^ (γ - 1 - 1) * m ^ (1 - γ) = m⁻¹ := by
      rw [← Real.rpow_add hm, show γ - 1 - 1 + (1 - γ) = -1 by ring, Real.rpow_neg_one]
    calc (α + 2 * γ - 1) / m
        = ((γ + α) * (γ + α - 1) * (m ^ (γ + α - 1 - 1) * m ^ (1 - α - γ)) -
            γ * (γ - 1) * (m ^ (γ - 1 - 1) * m ^ (1 - γ))) / α := by
          rw [e1, e2]
          field_simp
          ring
      _ = _ := by ring

/-- Miao, p. 689: the conditions (i)–(ii) are not necessary for `M` to be increasing and concave
near `m`: `γ = 0`, `α = 1/2` satisfies neither, yet `M(·, m)` is increasing and concave on
`(0, ∞)`. -/
theorem ku_wM_params_not_necessary {m : ℝ} (hm : 0 < m) :
    ¬ ((0 < (0 : ℝ) ∧ (0 : ℝ) < 1 ∧ (1 / 2 : ℝ) + 0 < 0) ∨
        ((0 : ℝ) < 0 ∧ 0 < (1 / 2 : ℝ) + 0 ∧ (1 / 2 : ℝ) + 0 < 1)) ∧
      StrictMonoOn (fun c => ku_wM 0 (1 / 2) c m) (Set.Ioi 0) ∧
      ConcaveOn ℝ (Set.Ioi 0) (fun c => ku_wM 0 (1 / 2) c m) := by
  have e : (fun c => ku_wM 0 (1 / 2) c m) = fun c => ku_euM (1 / 2) c m :=
    funext fun c => ku_wM_zero _ c m
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [e]; exact ku_euM_ii (by norm_num) hm
  · rw [e]; exact ku_euM_iii (by norm_num) (by norm_num) hm

/-! ### Disappointment aversion -/

/-- Gul's disappointment-aversion risk aggregator (p. 690). -/
noncomputable def ku_gulM (α δ c m : ℝ) : ℝ :=
  if m ≤ c then ku_euM α c m else ku_euM α c m + δ * ((c ^ α * m ^ (1 - α) - m) / α)

/-- Miao, p. 690: property (i), `M(m, m) = m`. -/
theorem ku_gulM_i {α δ m : ℝ} (hα : α ≠ 0) (hm : 0 < m) : ku_gulM α δ m m = m := by
  simp only [ku_gulM, le_refl, ↓reduceIte]
  exact ku_euM_i hα hm

/-- Miao, p. 690: with `δ = 0` disappointment aversion is expected utility. -/
theorem ku_gulM_zero (α c m : ℝ) : ku_gulM α 0 c m = ku_euM α c m := by
  simp [ku_gulM]

/-- Miao, p. 690: for disappointment aversion, (20.6) holds iff
`μ^α = ∑ p c^α − δ ∑ p 1(c < μ)(μ^α − c^α)`. -/
theorem ku_gulM_ce {p : S → ℝ} (hp1 : ∑ s, p s = 1) {α δ : ℝ} (hα : α ≠ 0) (c : S → ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    eq_20_6 p (ku_gulM α δ) c μ ↔
      μ ^ α = ∑ s, p s * c s ^ α -
        δ * ∑ s, p s * (if c s < μ then 1 else 0) * (μ ^ α - c s ^ α) := by
  have hb := Real.rpow_pos_of_pos hμ (-α)
  have hmα := Real.rpow_pos_of_pos hμ α
  have hma : μ ^ (-α) * μ ^ α = 1 := by
    rw [← Real.rpow_add hμ, neg_add_cancel, Real.rpow_zero]
  have e2 : μ ^ (1 - α) = μ * μ ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hμ, Real.rpow_one]
  have hterm : ∀ s, p s * ku_gulM α δ (c s) μ =
      μ * μ ^ (-α) / α * (p s * c s ^ α) + μ * (1 - 1 / α) * p s +
        δ * μ / α * (μ ^ (-α) * (p s * (if c s < μ then 1 else 0) * c s ^ α) -
          p s * (if c s < μ then 1 else 0)) := fun s => by
    simp only [ku_gulM, ku_euM, e2]
    by_cases h : μ ≤ c s
    · simp only [h, ↓reduceIte, not_lt.2 h]
      ring
    · simp only [h, ↓reduceIte, not_le.1 h]
      ring
  unfold eq_20_6
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1]
  set A := ∑ s, p s * c s ^ α
  set I := ∑ s, p s * (if c s < μ then 1 else 0)
  set J := ∑ s, p s * (if c s < μ then 1 else 0) * c s ^ α
  have hJ : ∑ s, p s * (if c s < μ then 1 else 0) * (μ ^ α - c s ^ α) = μ ^ α * I - J := by
    simp only [I, J, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hJ, Real.rpow_neg hμ.le]
  set q := μ ^ α
  have key : μ * q⁻¹ / α * A + μ * (1 - 1 / α) * 1 + δ * μ / α * (q⁻¹ * J - I) - μ =
      μ / (α * q) * (A - q + δ * (J - q * I)) := by
    field_simp
    ring
  have hne : μ / (α * q) ≠ 0 := div_ne_zero hμ.ne' (mul_ne_zero hα hmα.ne')
  constructor
  · intro h
    have h1 : μ / (α * q) * (A - q + δ * (J - q * I)) = 0 := by rw [← key]; linarith
    have h2 := (mul_eq_zero.1 h1).resolve_left hne
    linarith
  · intro h
    have h1 : A - q + δ * (J - q * I) = 0 := by linarith
    have h2 := key
    rw [h1, mul_zero] at h2
    linarith

/-- Miao, p. 690 (corrected): the disappointment-aversion certainty equivalent is
`μ^α = ∑ p̂(s)c(s)^α` with `p̂(s) = p(s)(1 + δ1(c(s) < μ))/(1 + δ∑ p 1(c < μ))`, for `δ ≥ 0`. -/
theorem ku_gulM_ce_hat {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {α δ : ℝ}
    (hα : α ≠ 0) (hδ : 0 ≤ δ) (c : S → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    eq_20_6 p (ku_gulM α δ) c μ ↔
      μ ^ α = ∑ s, p s * (1 + δ * (if c s < μ then 1 else 0)) /
        (1 + δ * ∑ s', p s' * (if c s' < μ then 1 else 0)) * c s ^ α := by
  rw [ku_gulM_ce hp1 hα c hμ]
  set I := ∑ s', p s' * (if c s' < μ then (1 : ℝ) else 0)
  have hI : 0 ≤ I := Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (by split_ifs <;> norm_num)
  have hD : 0 < 1 + δ * I := by nlinarith
  have e : ∑ s, p s * (1 + δ * (if c s < μ then 1 else 0)) / (1 + δ * I) * c s ^ α =
      (∑ s, p s * c s ^ α + δ * ∑ s, p s * (if c s < μ then 1 else 0) * c s ^ α) /
        (1 + δ * I) := by
    have h1 : ∀ s, p s * (1 + δ * (if c s < μ then 1 else 0)) / (1 + δ * I) * c s ^ α =
        (p s * c s ^ α + δ * (p s * (if c s < μ then 1 else 0) * c s ^ α)) / (1 + δ * I) :=
      fun s => by ring
    simp only [h1]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e2 : ∑ s, p s * (if c s < μ then 1 else 0) * (μ ^ α - c s ^ α) =
      μ ^ α * I - ∑ s, p s * (if c s < μ then 1 else 0) * c s ^ α := by
    simp only [I, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, e2, eq_div_iff hD.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 690 (misprint): with the printed weights `p̂(s) = (1 + δ1)/(1 + δ∑ p1)` (no factor
`p(s)`), the formula `μ^α = ∑ p̂ c^α` fails: for two equally likely states, `δ = 0` and `c ≡ 1`,
`μ = 1` solves (20.6) but `∑ p̂ c^α = 2`. -/
theorem ku_gulM_hat_misprint {α : ℝ} (hα : α ≠ 0) :
    eq_20_6 (fun _ : Bool => (1 / 2 : ℝ)) (ku_gulM α 0) (fun _ => 1) 1 ∧
      (1 : ℝ) ^ α ≠ ∑ s : Bool, (1 + 0 * (if (1 : ℝ) < 1 then 1 else 0)) /
        (1 + 0 * ∑ _s : Bool, (1 / 2 : ℝ) * (if (1 : ℝ) < 1 then 1 else 0)) *
          (fun _ => (1 : ℝ)) s ^ α := by
  refine ⟨?_, ?_⟩
  · unfold eq_20_6
    simp only [ku_gulM_i hα one_pos, Fintype.univ_bool, Finset.mem_singleton,
      Finset.sum_insert, Finset.sum_singleton, Bool.true_eq_false, not_false_eq_true]
    norm_num
  · simp

/-! ### Recursive weighted and disappointment-aversion utility -/

/-- Miao, p. 690: the conditional certainty equivalent of recursive weighted utility at a node,
`(M_t[U^α])^{1/α}` with `M_t(x) = ∑ (π U^γ/∑ π U^γ) x`, is the static weighted-utility
certainty equivalent for `p = π(·|s_t)`: it solves (20.6). -/
theorem ku_recWeighted_ce {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {γ α : ℝ}
    (hα : α ≠ 0) {u : S → ℝ} (hu : ∀ s, 0 < u s) :
    eq_20_6 p (ku_wM γ α) u
      ((∑ s, (p s * u s ^ γ / ∑ s', p s' * u s' ^ γ) * u s ^ α) ^ α⁻¹) := by
  have hpos : ∀ e : ℝ, 0 < ∑ s, p s * u s ^ e := fun e =>
    ku_wsum_pos hp hp1 fun s => Real.rpow_pos_of_pos (hu s) _
  have h := ku_wM_ce hp hp1 (γ := γ) hα hu (μ := ((∑ s, p s * u s ^ (γ + α)) /
    ∑ s, p s * u s ^ γ) ^ α⁻¹) (Real.rpow_pos_of_pos (div_pos (hpos _) (hpos _)) _)
  rw [← h.2]
  exact h.1.2 rfl

/-- Miao, p. 690: recursive weighted utility
`U_t = [(1 − β)c_t^{1−ρ} + β(M_t[U_{t+1}^α])^{(1−ρ)/α}]^{1/(1−ρ)}` is the CES aggregator applied to
the certainty equivalent `(M_t[U_{t+1}^α])^{1/α}`. -/
theorem ku_recWeighted {β ρ α x m : ℝ} (hm : 0 ≤ m) :
    ku_ces β ρ x (m ^ α⁻¹) = ((1 - β) * x ^ (1 - ρ) + β * m ^ ((1 - ρ) / α)) ^ (1 - ρ)⁻¹ := by
  rw [ku_ces, ← Real.rpow_mul hm, div_eq_inv_mul]

/-- Miao, p. 691: in recursive disappointment-aversion utility, `μ_t` solves
`μ_t^α = ∑ π U_{t+1}^α − δ∑_{Δ_{t+1}} π(μ_t^α − U_{t+1}^α)`, `Δ_{t+1} = {μ_t > U_{t+1}}`, iff it is
the static Gul certainty equivalent (20.6) at the node with `p = π(·|s_t)`. -/
theorem ku_recGul {p : S → ℝ} (hp1 : ∑ s, p s = 1) {α δ : ℝ} (hα : α ≠ 0) (u : S → ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    (μ ^ α = ∑ s, p s * u s ^ α -
        δ * ∑ s ∈ Finset.univ.filter (fun s => u s < μ), p s * (μ ^ α - u s ^ α)) ↔
      eq_20_6 p (ku_gulM α δ) u μ := by
  rw [ku_gulM_ce hp1 hα u hμ, Finset.sum_filter]
  have e : ∀ s, (if u s < μ then p s * (μ ^ α - u s ^ α) else 0) =
      p s * (if u s < μ then 1 else 0) * (μ ^ α - u s ^ α) := fun s => by
    split_ifs <;> ring
  simp only [e]

end Miao.RecursiveUtility
