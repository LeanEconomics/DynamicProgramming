/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.RealIntervals
import ConvergenceApplications.Parameters

/-!
# Industry investment under uncertainty

SLP §13.4, pp. 395–397, Exercise 13.4. The policy `g` of the §10.4 problem is taken as given,
with the properties of Exercise 10.4(d, e) (`IndustryPolicy`): `g` is continuous on
`X × Z`, `X = (0, ∞)`, `Z = [z̲, z̄]`, maps `X × Z` into `X`; (i) `g(·, z)` is strictly increasing
with slope `< 1`; (ii) `g(x, ·)` is nondecreasing. The shocks follow a monotone Feller Markov
kernel `Q` on `Z` with the mixing condition (2), `Qᴺ(z, (u, v]) ≥ α(v − u)` (`IndustryMixing`).
Positivity of `z̲` is never used.

## The shock process (p. 395)

* `industryMixing_Ici`, `industryMixing_Iic`: (2) gives Assumption 12.1 for `Q` at any `c ∈ Z`.
* `industry_shock_stable`: for `z̲ < z̄`, `Q` has a unique invariant `μ*` and `T*ⁿμ ⇒ μ*`.

## The policy function (p. 396)

* `IndustryPolicy.fixedPoint_unique`, `IndustryPolicy.xlo_le_xhi`: fixed points of `g(·, z)` are
  unique, and `x̲ ≤ x̄`.
* `industry_exists_xlo_xhi` (corrected existence): if `g(x₁, z̲) ≥ x₁` and `g(x₂, z̄) ≤ x₂` for
  some `x₁, x₂ > 0`, then `x̲` and `x̄` exist (intermediate value theorem).
* `industry_Xhat_invariant`: `X̂ = [x̲, x̄]` is invariant. More generally `IndustryRect` packages
  an invariant rectangle `[a, b] × Z` (`g(a, z̲) ≥ a`, `g(b, z̄) ≤ b`), e.g. any `[a, b] ⊇ X̂`
  (`industryRect_of_fixed`).
* `IndustryPolicy.tendsto_iterate`: `g(·, z)ⁿ(x₀) → p` for every `x₀ > 0` if `p` is the fixed
  point; `IndustryPolicy.iterate_mono`, `IndustryPolicy.continuousOn_iterate`.

## Exercise 13.4a (p. 396)

* `indKernel` (on any invariant rectangle, in particular `Ŝ = X̂ × Z`): `P̂(s, ·)` is the image of
  `δ_s ⊗ Q(z, ·)` under `(s, z′) ↦ (g(x, z), z′)`; `ex_13_4_transition`: it is a Markov kernel
  with `P̂((x, z), A × B) = 1{g(x, z) ∈ A} Q(z, B)`.
* `ex_13_4a_monotone`, `ex_13_4a_feller`: `P̂` is monotone and Feller (the latter via Lemma 12.14).

## Exercise 13.4b (p. 397), which the book leaves unproved

* `industry_Q_high_pos`, `industry_Q_low_pos` (the remark on p. 396): `Q(z̄, (u, z̄]) > 0` for
  `u < z̄`, and `Q(z̲, [z̲, u)) > 0` for `u > z̲`.
* `industry_Q_high_local`, `industry_Q_low_local`: by Feller, `Q(z, (z̄ − η, z̄]) ≥ c > 0` for all
  `z` near `z̄` (and the mirror image).
* `indKernel_highRun`, `indKernel_lowRun`: runs of `m` high (low) shocks have probability bounded
  below, and along them `x` is pushed up (down) by at least `g(·, z̄ − η)ᵐ` (`g(·, z̲ + η)ᵐ`).
* `indKernel_from_bot`, `indKernel_from_top`, `IndustryRect.bot_reach`, `IndustryRect.top_reach`:
  `N` steps of (2) bring `z` near `z̄` (`z̲`), then a run of `M` high (low) shocks.
* `ex_13_4b_rect`, `ex_13_4b_rect_stable`: Assumption 12.1 and Theorem 12.12 on a rectangle, for
  any `s*` reachable from both ends.
* `ex_13_4b`: Assumption 12.1 on `Ŝ` at `s* = ((x̲ + x̄)/2, (z̲ + z̄)/2)` (both for `x̲ < x̄` and
  for `x̲ = x̄`); `ex_13_4b_stable`: unique invariant `λ*` on `Ŝ` with `T*ⁿλ ⇒ λ*` for all `λ`.

## Exercise 13.4c (p. 397)

* `ex_13_4c_path_bounds`, `ex_13_4c_gap`, `ex_13_4c_squeeze_path`: along any shock path
  `g(·, z̲)ᵗ(x₀) ≤ xₜ ≤ g(·, z̄)ᵗ(x₀)`, the gap to `X̂` shrinks, and `xₜ ∈ (x̲ − δ, x̄ + δ)` from
  some `T` on, uniformly in the shocks.
* `kpow_indKernel_squeeze`, `ex_13_4c_squeeze_kernel`: the same for `Pⁿ(s, ·)`.
* `ex_13_4c_rect` (`x̲ < x̄`, via Theorem 12.12 on larger rectangles), `ex_13_4c_rect_degenerate`
  (`x̲ = x̄`, direct argument), `ex_13_4c_rect_all`: `T*ⁿλ ⇒ λ*` for `λ` on any `[a, b] × Z ⊇ Ŝ`.
* `ex_13_4c_degenerate_no_assumption`: if `x̲ = x̄ = p` and `a < p < b`, Assumption 12.1 fails on
  `[a, b] × Z` for every `s*`, so the degenerate case really needs the separate argument.
* `indSKernel`: the transition function `P` on the full state space `S = (0, ∞) × Z`;
  `kpow_indSKernel_indSIncl`: it restricts to `P̂` on invariant rectangles.
* `ex_13_4c`: **`T*ⁿλ ⇒ λ*` (extended by zero off `Ŝ`) for every probability measure `λ` on
  `S`**; `ex_13_4c_unique`: `λ*` is the unique invariant probability measure of `P` on `S`.

## Corrections

* **Existence of `x̲`, `x̄`** (p. 396). (i)–(ii) give uniqueness of the fixed points and `x̲ ≤ x̄`,
  not existence. `industry_no_fixedPoint_half`: `g(x, z) = x/2` satisfies all the hypotheses and
  has no positive fixed point (capital shrinks to `0 ∉ X`, as the NOTE says). The NOTE's repair
  (a condition such as `lim_{x↓0} g(x, z̲)/x > 1`) is not enough on its own:
  `industry_no_fixedPoint_above`: `g(x, z) = x + 1/(1 + x)` satisfies all the hypotheses with
  `g(x, z) > x` everywhere, so a condition at the top (`g(x₂, z̄) ≤ x₂` for some `x₂ > 0`) is also
  needed. With both, `industry_exists_xlo_xhi`.
* **The remark on Exercise 13.4c** ("`0 ≤ xₜ₊₁ − x̄ < xₜ − x̄` whenever `xₜ > x̄`"). The lower
  bound is false: `ex_13_4c_remark_counterexample` (`g(x, z) = (x + z)/2`, `Z = [1, 3]`,
  `x̄ = 3`, `x₀ = 4`, `z₀ = 1`, `x₁ = 5/2 < x̄`). What holds is `xₜ₊₁ − x̄ < xₜ − x̄` together
  with `xₜ₊₁ > x̲` (`ex_13_4c_gap`): the path may jump into `X̂`, where it stays.
* Exercise 13.4b asks for `> ε`; `≥ ε` is proved, which is equivalent (halve `ε`) and is the
  form of Assumption 12.1 used by `theorem_12_12_prod`.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BoundedContinuousFunction

variable {zlo zhi : ℝ}

/-! ### The shock process -/

/-- The mixing condition (2), p. 395: for some `N ≥ 1` and `α > 0`,
`Qᴺ(z, (u, v]) ≥ α(v − u)` for every `z ∈ Z` and `z̲ ≤ u ≤ v ≤ z̄`. -/
def IndustryMixing (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) (N : ℕ) (α : ℝ) : Prop :=
  1 ≤ N ∧ 0 < α ∧ ∀ (z : Icc zlo zhi) (u v : ℝ), zlo ≤ u → u ≤ v → v ≤ zhi →
    α * (v - u) ≤ (kpow Q N z).real {w | u < (w : ℝ) ∧ (w : ℝ) ≤ v}

variable {Q : Kernel (Icc zlo zhi) (Icc zlo zhi)} {N : ℕ} {α : ℝ}

/-- (2) bounds `Qᴺ(z, [c, z̄])` below by `α(z̄ − c)`. -/
theorem industryMixing_Ici [IsMarkovKernel Q] (hQ : IndustryMixing Q N α) (z c : Icc zlo zhi) :
    α * (zhi - c) ≤ (kpow Q N z).real (Ici c) := by
  have := ex_8_4a Q N
  exact (hQ.2.2 z c zhi c.2.1 c.2.2 le_rfl).trans (measureReal_mono fun w hw => hw.1.le)

/-- (2) bounds `Qᴺ(z, [z̲, c])` below by `α(c − z̲)`. -/
theorem industryMixing_Iic [IsMarkovKernel Q] (hQ : IndustryMixing Q N α) (z c : Icc zlo zhi) :
    α * (c - zlo) ≤ (kpow Q N z).real (Iic c) := by
  have := ex_8_4a Q N
  exact (hQ.2.2 z zlo c le_rfl c.2.1 c.2.2).trans (measureReal_mono fun w hw => hw.2)

/-- **The shock process** (p. 395). If `z̲ < z̄` and `Q` is monotone, Feller and satisfies (2),
then `Q` satisfies Assumption 12.1 at the midpoint `c` of `Z` with `ε = α(z̄ − z̲)/2`, so it has a
unique invariant probability measure `μ*` and `T*ⁿμ ⇒ μ*` for every `μ` (Theorem 12.12). -/
theorem industry_shock_stable (hz : zlo < zhi) [IsMarkovKernel Q] (hM : IsMonotoneTF Q)
    (hF : IsFeller Q) (hQ : IndustryMixing Q N α) :
    ∃ μ : Measure (Icc zlo zhi), IsProbabilityMeasure μ ∧ adjointOp Q μ = μ ∧
      (∀ ν : Measure (Icc zlo zhi), IsProbabilityMeasure ν → adjointOp Q ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc zlo zhi), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp Q)^[n] lam₀) μ := by
  set c : Icc zlo zhi := ⟨(zlo + zhi) / 2, by constructor <;> linarith⟩
  refine theorem_12_12_real hz.le Q hM hF (c := c) (ε := α * ((zhi - zlo) / 2))
    (mul_pos hQ.2.1 (by linarith)) hQ.1 ?_ ?_
  · calc α * ((zhi - zlo) / 2) = α * (zhi - (zlo + zhi) / 2) := by ring
      _ ≤ _ := industryMixing_Ici hQ _ c
  · calc α * ((zhi - zlo) / 2) = α * ((zlo + zhi) / 2 - zlo) := by ring
      _ ≤ _ := industryMixing_Iic hQ _ c

/-! ### The policy function -/

/-- The properties of the policy `g` of the §10.4 problem established in Exercise 10.4(d, e)
(p. 395), on `X × Z` with `X = (0, ∞)`: `g` is continuous and maps `X × Z` into `X`; (i) for each
`z`, `g(·, z)` is strictly increasing with slope strictly less than one; (ii) for each `x`,
`g(x, ·)` is nondecreasing. -/
structure IndustryPolicy (g : ℝ → ℝ → ℝ) (zlo zhi : ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ioi 0 ×ˢ Icc zlo zhi)
  pos : ∀ x z, 0 < x → z ∈ Icc zlo zhi → 0 < g x z
  strictMono_x : ∀ x x' z, 0 < x → x < x' → z ∈ Icc zlo zhi → g x z < g x' z
  slope_lt : ∀ x x' z, 0 < x → x < x' → z ∈ Icc zlo zhi → g x' z - g x z < x' - x
  mono_z : ∀ x z z', 0 < x → zlo ≤ z → z ≤ z' → z' ≤ zhi → g x z ≤ g x z'

variable {g : ℝ → ℝ → ℝ}

namespace IndustryPolicy

variable (hg : IndustryPolicy g zlo zhi)
include hg

/-- `g(·, z)` is nondecreasing on `X`. -/
theorem mono_x {x x' z : ℝ} (hx : 0 < x) (hxx : x ≤ x') (hz : z ∈ Icc zlo zhi) :
    g x z ≤ g x' z := by
  rcases hxx.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hg.strictMono_x x x' z hx hlt hz).le

/-- `g` is nondecreasing in `(x, z)` jointly. -/
theorem mono {x x' z z' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (hz : z ∈ Icc zlo zhi)
    (hz' : z' ∈ Icc zlo zhi) (hzz : z ≤ z') : g x z ≤ g x' z' :=
  (hg.mono_x hx hxx hz).trans (hg.mono_z x' z z' (hx.trans_le hxx) hz.1 hzz hz'.2)

/-- `g(x, z) − x` is strictly decreasing in `x`. -/
theorem sub_strictAnti {x x' z : ℝ} (hx : 0 < x) (hxx : x < x') (hz : z ∈ Icc zlo zhi) :
    g x' z - x' < g x z - x := by
  linarith [hg.slope_lt x x' z hx hxx hz]

/-- `g(·, z)` is continuous on `X`. -/
theorem continuousOn_x {z : ℝ} (hz : z ∈ Icc zlo zhi) : ContinuousOn (fun x => g x z) (Ioi 0) :=
  hg.cont.comp (continuousOn_id.prodMk continuousOn_const) fun _ hx => ⟨hx, hz⟩

/-- Uniqueness of the fixed point of `g(·, z)` (NOTE p. 396). -/
theorem fixedPoint_unique {x x' z : ℝ} (hx : 0 < x) (hx' : 0 < x') (hz : z ∈ Icc zlo zhi)
    (hfx : g x z = x) (hfx' : g x' z = x') : x = x' := by
  rcases lt_trichotomy x x' with h | h | h
  · have := hg.sub_strictAnti hx h hz; linarith
  · exact h
  · have := hg.sub_strictAnti hx' h hz; linarith

/-- `x̲ ≤ x̄` (NOTE p. 396): `g(x̲, z̄) ≥ g(x̲, z̲) = x̲`. -/
theorem xlo_le_xhi {xlo xhi : ℝ} (hz : zlo ≤ zhi) (hlo : 0 < xlo) (hhi : 0 < xhi)
    (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) : xlo ≤ xhi := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := hg.sub_strictAnti hhi hlt ⟨hz, le_rfl⟩
  have h2 := hg.mono_z xlo zlo zhi hlo le_rfl hz le_rfl
  linarith

/-- Below a fixed point `p` of `g(·, z)`, `g(x, z) ≥ x`; above it, `g(x, z) ≤ x`. -/
theorem le_self_of_le_fixed {x p z : ℝ} (hx : 0 < x) (hxp : x ≤ p) (hz : z ∈ Icc zlo zhi)
    (hp : g p z = p) : x ≤ g x z := by
  rcases hxp.eq_or_lt with rfl | hlt
  · exact hp.ge
  · have := hg.sub_strictAnti hx hlt hz; linarith

/-- Above a fixed point `p` of `g(·, z)`, `g(x, z) ≤ x`. -/
theorem le_self_of_fixed_le {x p z : ℝ} (hp0 : 0 < p) (hpx : p ≤ x) (hz : z ∈ Icc zlo zhi)
    (hp : g p z = p) : g x z ≤ x := by
  rcases hpx.eq_or_lt with rfl | hlt
  · exact hp.le
  · have := hg.sub_strictAnti hp0 hlt hz; linarith

/-- Existence of a fixed point of `g(·, z)` by the intermediate value theorem, given points
`x₁, x₂ > 0` with `g(x₁, z) ≥ x₁` and `g(x₂, z) ≤ x₂`. -/
theorem exists_fixedPoint {x₁ x₂ z : ℝ} (hz : z ∈ Icc zlo zhi) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (h₁ : x₁ ≤ g x₁ z) (h₂ : g x₂ z ≤ x₂) : ∃ p, 0 < p ∧ g p z = p := by
  have h12 : x₁ ≤ x₂ := by
    by_contra hlt
    rw [not_le] at hlt
    have := hg.sub_strictAnti hx₂ hlt hz; linarith
  have hc : ContinuousOn (fun x => g x z - x) (Icc x₁ x₂) :=
    ((hg.continuousOn_x hz).sub continuousOn_id).mono fun x hx => hx₁.trans_le hx.1
  obtain ⟨p, hp, hp0⟩ := intermediate_value_Icc' h12 hc
    (show (0 : ℝ) ∈ Icc (g x₂ z - x₂) (g x₁ z - x₁) from ⟨by linarith, by linarith⟩)
  have : g p z - p = 0 := hp0
  exact ⟨p, hx₁.trans_le hp.1, by linarith⟩

end IndustryPolicy

/-- **Corrected existence of `x̲` and `x̄`** (NOTE p. 396). Under (i)–(ii), if `g(x₁, z̲) ≥ x₁` for
some `x₁ > 0` and `g(x₂, z̄) ≤ x₂` for some `x₂ > 0`, there are `x̲, x̄ > 0` with `x̲ = g(x̲, z̲)`
and `x̄ = g(x̄, z̄)`; they are unique and `x̲ ≤ x̄`. -/
theorem industry_exists_xlo_xhi (hg : IndustryPolicy g zlo zhi) (hz : zlo ≤ zhi) {x₁ x₂ : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (h₁ : x₁ ≤ g x₁ zlo) (h₂ : g x₂ zhi ≤ x₂) :
    ∃ xlo xhi, 0 < xlo ∧ 0 < xhi ∧ g xlo zlo = xlo ∧ g xhi zhi = xhi ∧ xlo ≤ xhi ∧
      (∀ x, 0 < x → g x zlo = x → x = xlo) ∧ (∀ x, 0 < x → g x zhi = x → x = xhi) := by
  have hzlo : zlo ∈ Icc zlo zhi := ⟨le_rfl, hz⟩
  have hzhi : zhi ∈ Icc zlo zhi := ⟨hz, le_rfl⟩
  obtain ⟨xlo, hlo, hflo⟩ := hg.exists_fixedPoint hzlo hx₁ hx₂ h₁
    ((hg.mono_z x₂ zlo zhi hx₂ le_rfl hz le_rfl).trans h₂)
  obtain ⟨xhi, hhi, hfhi⟩ := hg.exists_fixedPoint hzhi hx₁ hx₂
    (h₁.trans (hg.mono_z x₁ zlo zhi hx₁ le_rfl hz le_rfl)) h₂
  exact ⟨xlo, xhi, hlo, hhi, hflo, hfhi, hg.xlo_le_xhi hz hlo hhi hflo hfhi,
    fun x hx hfx => hg.fixedPoint_unique hx hlo hzlo hfx hflo,
    fun x hx hfx => hg.fixedPoint_unique hx hhi hzhi hfx hfhi⟩

/-- **Counterexample to the existence claim** (p. 396), too little capital: `g(x, z) = x/2`
satisfies (i), (ii), continuity and `g(X × Z) ⊆ X`, but `g(·, z)` has no fixed point in
`X = (0, ∞)` for any `z`. -/
theorem industry_no_fixedPoint_half (zlo zhi : ℝ) :
    IndustryPolicy (fun x _ => x / 2) zlo zhi ∧ ∀ x : ℝ, 0 < x → x / 2 ≠ x := by
  refine ⟨⟨(continuous_fst.div_const 2).continuousOn, fun x _ hx _ => by positivity,
    fun x x' _ _ h _ => by linarith, fun x x' _ _ h _ => by linarith,
    fun _ _ _ _ _ _ _ => le_rfl⟩, fun x hx h => by linarith⟩

/-- **Counterexample to the existence claim** (p. 396), too much capital: `g(x, z) = x + 1/(1 + x)`
satisfies (i), (ii), continuity and `g(X × Z) ⊆ X`, but `g(x, z) > x` for every `x > 0`, so again
`g(·, z)` has no fixed point. So a condition at the top (`g(x, z̄) ≤ x` for some `x`) is missing
as well as the one at the bottom named in the NOTE. -/
theorem industry_no_fixedPoint_above (zlo zhi : ℝ) :
    IndustryPolicy (fun x _ => x + 1 / (1 + x)) zlo zhi ∧
      ∀ x : ℝ, 0 < x → x + 1 / (1 + x) ≠ x := by
  refine ⟨⟨?_, fun x _ hx _ => by positivity, fun x x' _ hx h _ => ?_, fun x x' _ hx h _ => ?_,
    fun _ _ _ _ _ _ _ => le_rfl⟩, fun x hx h => ?_⟩
  · refine ContinuousOn.add continuousOn_fst (ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuousOn_fst) fun p hp => ?_)
    have : (0 : ℝ) < p.1 := hp.1
    positivity
  · have hx' : 0 < 1 + x' := by linarith
    have hx1 : 0 < 1 + x := by linarith
    have h1 : 1 / (1 + x) - 1 / (1 + x') = (x' - x) / ((1 + x) * (1 + x')) := by
      rw [div_sub_div _ _ hx1.ne' hx'.ne']; ring
    have h2 : (x' - x) / ((1 + x) * (1 + x')) < x' - x := by
      rw [div_lt_iff₀ (mul_pos hx1 hx')]
      have : 0 < (1 + x) * (1 + x') - 1 := by nlinarith
      nlinarith [mul_pos (sub_pos.2 h) this]
    linarith
  · have : 1 / (1 + x') - 1 / (1 + x) < 0 := by
      have : 1 / (1 + x') < 1 / (1 + x) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
      linarith
    linarith
  · have : 0 < 1 / (1 + x) := by positivity
    linarith

/-! ### The joint process on an invariant rectangle -/

/-- A rectangle `[a, b] × Z` (`0 < a ≤ b`, `z̲ < z̄`) that the law of motion `x′ = g(x, z)` maps
into itself in `x`: `g(a, z̲) ≥ a` and `g(b, z̄) ≤ b`. `Ŝ = X̂ × Z` (`a = x̲`, `b = x̄`) is one; so
is every `[a, b] × Z` with `0 < a ≤ x̲` and `x̄ ≤ b` (`industryRect_of_fixed`). -/
structure IndustryRect (g : ℝ → ℝ → ℝ) (zlo zhi a b : ℝ) : Prop where
  policy : IndustryPolicy g zlo zhi
  z_lt : zlo < zhi
  a_pos : 0 < a
  a_le_b : a ≤ b
  a_le : a ≤ g a zlo
  le_b : g b zhi ≤ b

variable {a b : ℝ}

/-- `[a, b] × Z` is an invariant rectangle whenever `0 < a ≤ x̲ ≤ x̄ ≤ b`. -/
theorem industryRect_of_fixed (hg : IndustryPolicy g zlo zhi) (hz : zlo < zhi) {xlo xhi : ℝ}
    (hlo : 0 < xlo) (hloh : xlo ≤ xhi) (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi)
    (ha : 0 < a) (hax : a ≤ xlo) (hxb : xhi ≤ b) : IndustryRect g zlo zhi a b :=
  ⟨hg, hz, ha, hax.trans (hloh.trans hxb), hg.le_self_of_le_fixed ha hax ⟨le_rfl, hz.le⟩ hflo,
    hg.le_self_of_fixed_le (hlo.trans_le hloh) hxb ⟨hz.le, le_rfl⟩ hfhi⟩

namespace IndustryRect

variable (h : IndustryRect g zlo zhi a b)
include h

/-- `g` maps `[a, b] × Z` into `[a, b]`. -/
theorem mem_g {x z : ℝ} (hx : x ∈ Icc a b) (hz : z ∈ Icc zlo zhi) : g x z ∈ Icc a b :=
  ⟨h.a_le.trans (h.policy.mono h.a_pos hx.1 ⟨le_rfl, h.z_lt.le⟩ hz hz.1),
    (h.policy.mono (h.a_pos.trans_le hx.1) hx.2 hz ⟨h.z_lt.le, le_rfl⟩ hz.2).trans h.le_b⟩

/-- `(x, z) ↦ g(x, z)` is continuous on the rectangle. -/
theorem continuous_gOf : Continuous fun s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) => g s.1.1 s.1.2 :=
  h.policy.cont.comp_continuous continuous_subtype_val fun s =>
    ⟨h.a_pos.trans_le s.2.1.1, s.2.1.2, s.2.2.2⟩

end IndustryRect

/-- **`X̂ = [x̲, x̄]` is invariant** (NOTE p. 396): `x̲ = g(x̲, z̲) ≤ g(x, z) ≤ g(x̄, z̄) = x̄` for
`x ∈ X̂`, `z ∈ Z`. -/
theorem industry_Xhat_invariant (hg : IndustryPolicy g zlo zhi) (hz : zlo < zhi) {xlo xhi : ℝ}
    (hlo : 0 < xlo) (hloh : xlo ≤ xhi) (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) {x z : ℝ}
    (hx : x ∈ Icc xlo xhi) (hz' : z ∈ Icc zlo zhi) : g x z ∈ Icc xlo xhi :=
  (industryRect_of_fixed hg hz hlo hloh hflo hfhi hlo le_rfl le_rfl).mem_g hx hz'

/-- The shock coordinate `z` of a state `s = (x, z)` of the rectangle. -/
def indZ (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) : Icc zlo zhi := ⟨s.1.2, s.2.1.2, s.2.2.2⟩

/-- The shock coordinate is continuous. -/
theorem continuous_indZ : Continuous (indZ (a := a) (b := b) (zlo := zlo) (zhi := zhi)) :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _

/-- The law of motion: from `s = (x, z)` and next period's shock `z′`, the state
`(g(x, z), z′)`. -/
def indNext (h : IndustryRect g zlo zhi a b) (p : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) × Icc zlo zhi) :
    Icc ((a, zlo) : ℝ × ℝ) (b, zhi) :=
  ⟨(g p.1.1.1 p.1.1.2, p.2.1), ⟨(h.mem_g ⟨p.1.2.1.1, p.1.2.2.1⟩ (indZ p.1).2).1, p.2.2.1⟩,
    ⟨(h.mem_g ⟨p.1.2.1.1, p.1.2.2.1⟩ (indZ p.1).2).2, p.2.2.2⟩⟩

/-- The law of motion is continuous. -/
theorem continuous_indNext (h : IndustryRect g zlo zhi a b) : Continuous (indNext h) :=
  ((h.continuous_gOf.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- `z′ ↦ (g(x, z), z′)` is measurable. -/
theorem measurable_indNext_left (h : IndustryRect g zlo zhi a b)
    (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) : Measurable fun w => indNext h (s, w) :=
  (continuous_indNext h).measurable.comp measurable_prodMk_left

/-- **The transition function `P̂`** (p. 396, Theorem 9.13) on the rectangle `[a, b] × Z`:
`P̂(s, ·)` is the law of `(g(x, z), z′)` with `z′ ∼ Q(z, ·)`, built as the image of
`δ_s ⊗ Q(z, ·)` under the law of motion. -/
noncomputable def indKernel (h : IndustryRect g zlo zhi a b)
    (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) :
    Kernel (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :=
  Kernel.map (Kernel.id ×ₖ Q.comap indZ continuous_indZ.measurable) (indNext h)

variable (h : IndustryRect g zlo zhi a b)

/-- `P̂` is a Markov kernel. -/
theorem isMarkovKernel_indKernel [IsMarkovKernel Q] : IsMarkovKernel (indKernel h Q) :=
  Kernel.IsMarkovKernel.map _ (continuous_indNext h).measurable

/-- `P̂(s, ·) = Q(z, ·) ∘ (z′ ↦ (g(x, z), z′))⁻¹`. -/
theorem indKernel_apply [IsMarkovKernel Q] (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    indKernel h Q s = (Q (indZ s)).map fun w => indNext h (s, w) := by
  rw [indKernel, Kernel.map_apply _ (continuous_indNext h).measurable, Kernel.prod_apply,
    Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (continuous_indNext h).measurable measurable_prodMk_left]
  rfl

/-- Lebesgue integrals against `P̂(s, ·)` are integrals against `Q(z, ·)`. -/
theorem lintegral_indKernel [IsMarkovKernel Q] (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi))
    {f : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, f t ∂indKernel h Q s = ∫⁻ w, f (indNext h (s, w)) ∂Q (indZ s) := by
  rw [indKernel_apply, lintegral_map hf (measurable_indNext_left h s)]

/-- `(T̂f)(x, z) = ∫ f(g(x, z), z′) Q(z, dz′)`. -/
theorem markovOpR_indKernel [IsMarkovKernel Q] {f : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) → ℝ}
    (hf : Measurable f) (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    markovOpR (indKernel h Q) f s = ∫ w, f (indNext h (s, w)) ∂Q (indZ s) := by
  rw [markovOpR, indKernel_apply, integral_map (measurable_indNext_left h s).aemeasurable
    hf.aestronglyMeasurable]

/-- **Exercise 13.4** (the transition function, p. 396): `P̂` is a Markov kernel with
`P̂((x, z), A × B) = 1{g(x, z) ∈ A} Q(z, B)`. -/
theorem ex_13_4_transition [IsMarkovKernel Q] {A : Set ℝ} (hA : MeasurableSet A)
    {B : Set (Icc zlo zhi)} (hB : MeasurableSet B) (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    IsMarkovKernel (indKernel h Q) ∧
      indKernel h Q s {t | t.1.1 ∈ A ∧ indZ t ∈ B} =
        A.indicator 1 (g s.1.1 s.1.2) * Q (indZ s) B := by
  refine ⟨isMarkovKernel_indKernel h, ?_⟩
  have hm : MeasurableSet {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) | t.1.1 ∈ A ∧ indZ t ∈ B} :=
    ((measurable_fst.comp measurable_subtype_coe) hA).inter (continuous_indZ.measurable hB)
  rw [indKernel_apply, Measure.map_apply (measurable_indNext_left h s) hm]
  by_cases hg : g s.1.1 s.1.2 ∈ A
  · rw [indicator_of_mem hg, Pi.one_apply, one_mul]
    congr 1
    ext w
    exact ⟨fun hw => hw.2, fun hw => ⟨hg, hw⟩⟩
  · rw [indicator_of_notMem hg, zero_mul]
    convert measure_empty (μ := Q (indZ s))
    ext w
    exact ⟨fun hw => hg hw.1, fun hw => hw.elim⟩

/-- **Exercise 13.4a** (monotone): `P̂` is monotone. -/
theorem ex_13_4a_monotone [IsMarkovKernel Q] (hM : IsMonotoneTF Q) :
    IsMonotoneTF (indKernel h Q) := by
  intro f hf ⟨M, hMb⟩ hmono s s' hss'
  rw [markovOpR_indKernel h hf, markovOpR_indKernel h hf]
  have hnext : ∀ w, indNext h (s, w) ≤ indNext h (s', w) := fun w =>
    ⟨h.policy.mono (h.a_pos.trans_le s.2.1.1) hss'.1 (indZ s).2 (indZ s').2 hss'.2, le_rfl⟩
  have hint : ∀ (t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) (z : Icc zlo zhi),
      Integrable (fun w => f (indNext h (t, w))) (Q z) := fun t z =>
    integrable_of_bounded (hf.comp (measurable_indNext_left h t)) fun w => hMb _
  calc ∫ w, f (indNext h (s, w)) ∂Q (indZ s) ≤ ∫ w, f (indNext h (s', w)) ∂Q (indZ s) :=
        integral_mono (hint s _) (hint s' _) fun w => hmono (hnext w)
    _ ≤ ∫ w, f (indNext h (s', w)) ∂Q (indZ s') :=
        hM (fun w => f (indNext h (s', w))) (hf.comp (measurable_indNext_left h s'))
          ⟨M, fun w => hMb _⟩ (fun w w' hww' => hmono ⟨le_rfl, hww'⟩) hss'.2

/-- **Exercise 13.4a** (Feller): `P̂` has the Feller property. `P̂f(x, z) = ∫ F(g(x, z), z′)
Q(z, dz′)` with `F` bounded continuous on `ℝ × Z`, which is continuous by Lemma 12.14. -/
theorem ex_13_4a_feller [IsMarkovKernel Q] (hF : IsFeller Q) : IsFeller (indKernel h Q) := by
  intro f hf ⟨M, hMb⟩
  set Fb : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * M) fun x y => by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by simp only [ContinuousMap.coe_mk]; linarith [hMb x, hMb y])
  set F : ℝ × Icc zlo zhi →ᵇ ℝ := Fb.compContinuous
    ⟨fun p => ⟨((projIcc a b h.a_le_b p.1 : ℝ), (p.2 : ℝ)),
      ⟨(projIcc a b h.a_le_b p.1).2.1, p.2.2.1⟩, ⟨(projIcc a b h.a_le_b p.1).2.2, p.2.2.2⟩⟩,
      ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hrepr : markovOpR (indKernel h Q) f = fun s => ∫ w, F (g s.1.1 s.1.2, w) ∂Q (indZ s) := by
    funext s
    rw [markovOpR_indKernel h hf.measurable]
    congr 1
    funext w
    have hmem := h.mem_g ⟨s.2.1.1, s.2.2.1⟩ (indZ s).2
    change f _ = f _
    congr 1
    exact Subtype.ext (Prod.ext (congrArg Subtype.val (projIcc_of_mem h.a_le_b hmem)).symm rfl)
  rw [hrepr]
  exact (lemma_12_14_cont Q hF F).1.comp (h.continuous_gOf.prodMk continuous_indZ)

/-! ### Exercise 13.4b: shocks near the endpoints -/

/-- Remark (p. 396): by monotonicity, (2) forces `Q(z̄, (u, z̄]) > 0` for every `u < z̄`. Otherwise
`Q(z, (u, z̄]) ≤ Q(z̄, (u, z̄]) = 0` for every `z` (dominance) and so `Qᴺ(z, (u, z̄]) = 0`. -/
theorem industry_Q_high_pos [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hQ : IndustryMixing Q N α)
    (hz : zlo < zhi) {u : ℝ} (hu : u < zhi) :
    0 < Q ⟨zhi, hz.le, le_rfl⟩ {w | u < (w : ℝ)} := by
  set U : Set (Icc zlo zhi) := {w | u < (w : ℝ)}
  have hU : MeasurableSet U := measurableSet_lt measurable_const measurable_subtype_coe
  rw [pos_iff_ne_zero]
  intro h0
  have hall : ∀ w, Q w U = 0 := fun w => by
    have := ((ex_12_11 Q).2.1 hM ⟨zhi, hz.le, le_rfl⟩ w w.2.2).real_le hU
      (fun x y hxy (hx : u < (x : ℝ)) => show u < (y : ℝ) from lt_of_lt_of_le hx hxy)
    rw [measureReal_def (Q ⟨zhi, hz.le, le_rfl⟩), h0, ENNReal.toReal_zero] at this
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm this measureReal_nonneg)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := hQ.1; omega⟩
  have := ex_8_4a Q (n + 1)
  have hk : kpow Q (n + 1) ⟨zlo, le_rfl, hz.le⟩ U = 0 := by
    rw [kpow_add, kpow_one, Kernel.comp_apply' _ _ _ hU]
    simp [hall]
  have hmix := hQ.2.2 ⟨zlo, le_rfl, hz.le⟩ (max u zlo) zhi (le_max_right _ _)
    (max_le hu.le hz.le) le_rfl
  have hsub := measureReal_mono (μ := kpow Q (n + 1) ⟨zlo, le_rfl, hz.le⟩)
    (show {w : Icc zlo zhi | max u zlo < (w : ℝ) ∧ (w : ℝ) ≤ zhi} ⊆ U from
      fun w hw => (le_max_left _ _).trans_lt hw.1)
  rw [measureReal_def _ U, hk, ENNReal.toReal_zero] at hsub
  have hpos : 0 < α * (zhi - max u zlo) := mul_pos hQ.2.1 (sub_pos.2 (max_lt hu hz))
  linarith

/-- The mirror image: `Q(z̲, [z̲, u)) > 0` for every `u > z̲`. -/
theorem industry_Q_low_pos [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hQ : IndustryMixing Q N α)
    (hz : zlo < zhi) {u : ℝ} (hu : zlo < u) :
    0 < Q ⟨zlo, le_rfl, hz.le⟩ {w | (w : ℝ) < u} := by
  set L : Set (Icc zlo zhi) := {w | (w : ℝ) < u}
  have hL : MeasurableSet L := measurableSet_lt measurable_subtype_coe measurable_const
  rw [pos_iff_ne_zero]
  intro h0
  have hall : ∀ w, Q w L = 0 := fun w => by
    have := ((ex_12_11 Q).2.1 hM w ⟨zlo, le_rfl, hz.le⟩ w.2.1).real_le hL.compl
      (fun x y hxy hx (hy : (y : ℝ) < u) => hx (show (x : ℝ) < u from
        lt_of_le_of_lt (show (x : ℝ) ≤ y from hxy) hy))
    rw [probReal_compl_eq_one_sub hL, probReal_compl_eq_one_sub hL,
      measureReal_def (Q ⟨zlo, le_rfl, hz.le⟩), h0, ENNReal.toReal_zero] at this
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1
      (le_antisymm (by linarith) measureReal_nonneg)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := hQ.1; omega⟩
  have := ex_8_4a Q (n + 1)
  have hk : kpow Q (n + 1) ⟨zlo, le_rfl, hz.le⟩ L = 0 := by
    rw [kpow_add, kpow_one, Kernel.comp_apply' _ _ _ hL]
    simp [hall]
  set v := min ((zlo + u) / 2) zhi
  have hmix := hQ.2.2 ⟨zlo, le_rfl, hz.le⟩ zlo v le_rfl (le_min (by linarith) hz.le)
    (min_le_right _ _)
  have hsub := measureReal_mono (μ := kpow Q (n + 1) ⟨zlo, le_rfl, hz.le⟩)
    (show {w : Icc zlo zhi | zlo < (w : ℝ) ∧ (w : ℝ) ≤ v} ⊆ L from
      fun w hw => lt_of_le_of_lt (hw.2.trans (min_le_left _ _)) (by linarith))
  rw [measureReal_def _ L, hk, ENNReal.toReal_zero] at hsub
  have hpos : 0 < α * (v - zlo) := mul_pos hQ.2.1 (sub_pos.2 (lt_min (by linarith) hz))
  linarith

/-- From `Q(z̄, (z̄ − η/2, z̄]) > 0` and the Feller property: for every `η > 0` there are
`η′ > 0` and `c > 0` with `Q(z, (z̄ − η, z̄]) ≥ c` for all `z > z̄ − η′`. (Apply Feller to a
continuous `f` with `1_{(z̄ − η/2, z̄]} ≤ f ≤ 1_{(z̄ − η, z̄]}`.) -/
theorem industry_Q_high_local [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) (hz : zlo < zhi) {η : ℝ} (hη : 0 < η) :
    ∃ η' > 0, ∃ c : ℝ≥0∞, c ≠ 0 ∧
      ∀ z : Icc zlo zhi, zhi - η' < (z : ℝ) → c ≤ Q z {w | zhi - η < (w : ℝ)} := by
  set f : Icc zlo zhi → ℝ := fun w => max 0 (min 1 (((w : ℝ) - (zhi - η)) * (2 / η)))
  have hfc : Continuous f := continuous_const.max (continuous_const.min
    ((continuous_subtype_val.sub continuous_const).mul continuous_const))
  have hfb : ∀ w, |f w| ≤ 1 := fun w => by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  set U : Set (Icc zlo zhi) := {w | zhi - η < (w : ℝ)}
  set V : Set (Icc zlo zhi) := {w | zhi - η / 2 < (w : ℝ)}
  have hU : MeasurableSet U := measurableSet_lt measurable_const measurable_subtype_coe
  have hV : MeasurableSet V := measurableSet_lt measurable_const measurable_subtype_coe
  have hfU : ∀ w, f w ≤ U.indicator 1 w := fun w => by
    by_cases hw : w ∈ U
    · rw [indicator_of_mem hw, Pi.one_apply]; exact max_le zero_le_one (min_le_left _ _)
    · rw [indicator_of_notMem hw]
      have hw' : (w : ℝ) - (zhi - η) ≤ 0 := by
        simp only [U, mem_ofPred_eq, not_lt] at hw; linarith
      exact max_le le_rfl ((min_le_right _ _).trans
        (mul_nonpos_of_nonpos_of_nonneg hw' (by positivity)))
  have hfV : ∀ w, V.indicator 1 w ≤ f w := fun w => by
    by_cases hw : w ∈ V
    · rw [indicator_of_mem hw, Pi.one_apply]
      have hw' : zhi - η / 2 < (w : ℝ) := hw
      refine le_max_of_le_right (le_min le_rfl ?_)
      calc (1 : ℝ) = η / 2 * (2 / η) := by field_simp
        _ ≤ ((w : ℝ) - (zhi - η)) * (2 / η) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · rw [indicator_of_notMem hw]; exact le_max_left _ _
  have hint : ∀ z, Integrable f (Q z) := fun z => integrable_of_bounded hfc.measurable hfb
  have hTU : ∀ z, markovOpR Q f z ≤ (Q z).real U := fun z => by
    rw [← integral_indicator_one hU]
    exact integral_mono (hint z) ((integrable_const 1).indicator hU) hfU
  set ztop : Icc zlo zhi := ⟨zhi, hz.le, le_rfl⟩
  have hTpos : 0 < markovOpR Q f ztop := by
    have h1 : (Q ztop).real V ≤ markovOpR Q f ztop := by
      rw [← integral_indicator_one hV]
      exact integral_mono ((integrable_const 1).indicator hV) (hint _) hfV
    have h2 : 0 < (Q ztop).real V :=
      ENNReal.toReal_pos (industry_Q_high_pos hM hQ hz (by linarith)).ne' (measure_ne_top _ _)
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 (hF f hfc ⟨1, hfb⟩) ztop _ (half_pos hTpos)
  refine ⟨δ, hδ, ENNReal.ofReal (markovOpR Q f ztop / 2),
    (ENNReal.ofReal_pos.2 (half_pos hTpos)).ne', fun z hzδ => ?_⟩
  have hd : dist z ztop < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    constructor <;> simp only [ztop] <;> linarith [z.2.2]
  have h1 := hball z hd
  rw [Real.dist_eq, abs_lt] at h1
  apply ENNReal.ofReal_le_of_le_toReal
  rw [← measureReal_def]
  linarith [hTU z, h1.1]

/-- The mirror image: for every `η > 0` there are `η′ > 0` and `c > 0` with
`Q(z, [z̲, z̲ + η)) ≥ c` for all `z < z̲ + η′`. -/
theorem industry_Q_low_local [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) (hz : zlo < zhi) {η : ℝ} (hη : 0 < η) :
    ∃ η' > 0, ∃ c : ℝ≥0∞, c ≠ 0 ∧
      ∀ z : Icc zlo zhi, (z : ℝ) < zlo + η' → c ≤ Q z {w | (w : ℝ) < zlo + η} := by
  set f : Icc zlo zhi → ℝ := fun w => max 0 (min 1 ((zlo + η - (w : ℝ)) * (2 / η)))
  have hfc : Continuous f := continuous_const.max (continuous_const.min
    ((continuous_const.sub continuous_subtype_val).mul continuous_const))
  have hfb : ∀ w, |f w| ≤ 1 := fun w => by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  set U : Set (Icc zlo zhi) := {w | (w : ℝ) < zlo + η}
  set V : Set (Icc zlo zhi) := {w | (w : ℝ) < zlo + η / 2}
  have hU : MeasurableSet U := measurableSet_lt measurable_subtype_coe measurable_const
  have hV : MeasurableSet V := measurableSet_lt measurable_subtype_coe measurable_const
  have hfU : ∀ w, f w ≤ U.indicator 1 w := fun w => by
    by_cases hw : w ∈ U
    · rw [indicator_of_mem hw, Pi.one_apply]; exact max_le zero_le_one (min_le_left _ _)
    · rw [indicator_of_notMem hw]
      have hw' : zlo + η - (w : ℝ) ≤ 0 := by
        simp only [U, mem_ofPred_eq, not_lt] at hw; linarith
      exact max_le le_rfl ((min_le_right _ _).trans
        (mul_nonpos_of_nonpos_of_nonneg hw' (by positivity)))
  have hfV : ∀ w, V.indicator 1 w ≤ f w := fun w => by
    by_cases hw : w ∈ V
    · rw [indicator_of_mem hw, Pi.one_apply]
      have hw' : (w : ℝ) < zlo + η / 2 := hw
      refine le_max_of_le_right (le_min le_rfl ?_)
      calc (1 : ℝ) = η / 2 * (2 / η) := by field_simp
        _ ≤ (zlo + η - (w : ℝ)) * (2 / η) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · rw [indicator_of_notMem hw]; exact le_max_left _ _
  have hint : ∀ z, Integrable f (Q z) := fun z => integrable_of_bounded hfc.measurable hfb
  have hTU : ∀ z, markovOpR Q f z ≤ (Q z).real U := fun z => by
    rw [← integral_indicator_one hU]
    exact integral_mono (hint z) ((integrable_const 1).indicator hU) hfU
  set zbot : Icc zlo zhi := ⟨zlo, le_rfl, hz.le⟩
  have hTpos : 0 < markovOpR Q f zbot := by
    have h1 : (Q zbot).real V ≤ markovOpR Q f zbot := by
      rw [← integral_indicator_one hV]
      exact integral_mono ((integrable_const 1).indicator hV) (hint _) hfV
    have h2 : 0 < (Q zbot).real V :=
      ENNReal.toReal_pos (industry_Q_low_pos hM hQ hz (by linarith)).ne' (measure_ne_top _ _)
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 (hF f hfc ⟨1, hfb⟩) zbot _ (half_pos hTpos)
  refine ⟨δ, hδ, ENNReal.ofReal (markovOpR Q f zbot / 2),
    (ENNReal.ofReal_pos.2 (half_pos hTpos)).ne', fun z hzδ => ?_⟩
  have hd : dist z zbot < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    constructor <;> simp only [zbot] <;> linarith [z.2.1]
  have h1 := hball z hd
  rw [Real.dist_eq, abs_lt] at h1
  apply ENNReal.ofReal_le_of_le_toReal
  rw [← measureReal_def]
  linarith [hTU z, h1.1]

/-! ### Iterates of `g(·, z)` -/

namespace IndustryPolicy

variable (hg : IndustryPolicy g zlo zhi)
include hg

/-- `g(·, z)ᵐ` is positive and nondecreasing on `X`. -/
theorem iterate_mono {z : ℝ} (hz : z ∈ Icc zlo zhi) (m : ℕ) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    0 < (fun x => g x z)^[m] x ∧ (fun x => g x z)^[m] x ≤ (fun x => g x z)^[m] y := by
  induction m with
  | zero => exact ⟨hx, hxy⟩
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact ⟨hg.pos _ _ ih.1 hz, hg.mono_x ih.1 ih.2 hz⟩

/-- `z ↦ g(·, z)ᴹ(x₀)` is continuous on `Z` (and positive). -/
theorem continuousOn_iterate {x₀ : ℝ} (hx₀ : 0 < x₀) (M : ℕ) :
    ContinuousOn (fun z => (fun x => g x z)^[M] x₀) (Icc zlo zhi) ∧
      ∀ z ∈ Icc zlo zhi, 0 < (fun x => g x z)^[M] x₀ := by
  induction M with
  | zero => exact ⟨continuousOn_const, fun _ _ => hx₀⟩
  | succ M ih =>
    simp only [Function.iterate_succ_apply']
    exact ⟨hg.cont.comp (ih.1.prodMk continuousOn_id) fun z hz => ⟨ih.2 z hz, hz⟩,
      fun z hz => hg.pos _ _ (ih.2 z hz) hz⟩

/-- **Global stability of `g(·, z)`.** If `p > 0` is a fixed point of `g(·, z)`, the iterates
`g(·, z)ⁿ(x₀)` converge to `p` from every `x₀ > 0` (monotonically: up from below, down from
above; the limit is a fixed point by continuity, hence `p` by uniqueness). -/
theorem tendsto_iterate {z p x₀ : ℝ} (hz : z ∈ Icc zlo zhi) (hp : 0 < p) (hfp : g p z = p)
    (hx₀ : 0 < x₀) : Tendsto (fun n => (fun x => g x z)^[n] x₀) atTop (𝓝 p) := by
  set F := fun x => g x z
  set u := fun n => F^[n] x₀
  have hsucc : ∀ n, u (n + 1) = F (u n) := fun n => Function.iterate_succ_apply' F n x₀
  have hlim : ∀ L, 0 < L → Tendsto u atTop (𝓝 L) → L = p := fun L hL hu => by
    have h1 : Tendsto (fun n => F (u n)) atTop (𝓝 (F L)) :=
      (((hg.continuousOn_x hz).continuousAt (Ioi_mem_nhds hL)).tendsto).comp hu
    have h2 : Tendsto (fun n => F (u n)) atTop (𝓝 L) := by
      simp_rw [← hsucc]; exact hu.comp (tendsto_add_atTop_nat 1)
    exact hg.fixedPoint_unique hL hp hz (tendsto_nhds_unique h1 h2) hfp
  rcases le_total x₀ p with hle | hle
  · have hmem : ∀ n, x₀ ≤ u n ∧ u n ≤ p := by
      intro n
      induction n with
      | zero => exact ⟨le_rfl, hle⟩
      | succ n ih =>
        rw [hsucc]
        have h0 : 0 < u n := hx₀.trans_le ih.1
        exact ⟨ih.1.trans (hg.le_self_of_le_fixed h0 ih.2 hz hfp),
          (hg.mono_x h0 ih.2 hz).trans hfp.le⟩
    have hmono : Monotone u := monotone_nat_of_le_succ fun n => by
      rw [hsucc]; exact hg.le_self_of_le_fixed (hx₀.trans_le (hmem n).1) (hmem n).2 hz hfp
    have hbdd : BddAbove (range u) := ⟨p, by rintro _ ⟨n, rfl⟩; exact (hmem n).2⟩
    have hT := tendsto_atTop_ciSup hmono hbdd
    rwa [hlim _ (hx₀.trans_le ((hmem 0).1.trans (le_ciSup hbdd 0))) hT] at hT
  · have hmem : ∀ n, p ≤ u n ∧ u n ≤ x₀ := by
      intro n
      induction n with
      | zero => exact ⟨hle, le_rfl⟩
      | succ n ih =>
        rw [hsucc]
        exact ⟨hfp.ge.trans (hg.mono_x hp ih.1 hz),
          (hg.le_self_of_fixed_le hp ih.1 hz hfp).trans ih.2⟩
    have hanti : Antitone u := antitone_nat_of_succ_le fun n => by
      rw [hsucc]; exact hg.le_self_of_fixed_le hp (hmem n).1 hz hfp
    have hbdd : BddBelow (range u) := ⟨p, by rintro _ ⟨n, rfl⟩; exact (hmem n).1⟩
    have hT := tendsto_atTop_ciInf hanti hbdd
    rwa [hlim _ (hp.trans_le (le_ciInf fun n => (hmem n).1)) hT] at hT

end IndustryPolicy

/-! ### Exercise 13.4b: runs of high and low shocks -/

/-- The `z`-marginal of `P̂ⁿ(s, ·)` is `Qⁿ(z, ·)`. -/
theorem kpow_indKernel_indZ [IsMarkovKernel Q] (n : ℕ) (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi))
    {B : Set (Icc zlo zhi)} (hB : MeasurableSet B) :
    kpow (indKernel h Q) n s (indZ ⁻¹' B) = kpow Q n (indZ s) B := by
  have := isMarkovKernel_indKernel h (Q := Q)
  induction n generalizing s with
  | zero =>
    change Kernel.id s _ = Kernel.id (indZ s) B
    rw [Kernel.id_apply, Kernel.id_apply, Measure.dirac_apply' _ (continuous_indZ.measurable hB),
      Measure.dirac_apply' _ hB]
    rfl
  | succ n ih =>
    change (kpow (indKernel h Q) n ∘ₖ indKernel h Q) s _ = (kpow Q n ∘ₖ Q) (indZ s) B
    rw [Kernel.comp_apply' _ _ _ (continuous_indZ.measurable hB), Kernel.comp_apply' _ _ _ hB,
      lintegral_indKernel h s (Kernel.measurable_coe _ (continuous_indZ.measurable hB))]
    simp only [ih]
    rfl

/-- **Runs of high shocks.** Let `G = g(·, z̄ − η)`. For every `m` there are `η_m > 0` and
`c_m > 0` such that from any `s = (x, z)` with `z > z̄ − η_m`, with probability at least `c_m`
the next `m` shocks all exceed `z̄ − η`, and then `x_m ≥ Gᵐ(x)`. -/
theorem indKernel_highRun [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) {η : ℝ} (hη : 0 < η) (hηz : η ≤ zhi - zlo) (m : ℕ) :
    ∃ η' > 0, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi), zhi - η' < s.1.2 →
      c ≤ kpow (indKernel h Q) m s
        {t | (fun x => g x (zhi - η))^[m] s.1.1 ≤ t.1.1 ∧ zhi - η < t.1.2} := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have hzη : zhi - η ∈ Icc zlo zhi := ⟨by linarith, by linarith⟩
  have hmeas : ∀ C : ℝ, MeasurableSet
      {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) | C ≤ t.1.1 ∧ zhi - η < t.1.2} := fun C =>
    (measurableSet_le measurable_const (measurable_fst.comp measurable_subtype_coe)).inter
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_subtype_coe))
  induction m with
  | zero =>
    refine ⟨η, hη, 1, one_ne_zero, fun s hs => ?_⟩
    change 1 ≤ Kernel.id s _
    rw [Kernel.id_apply, Measure.dirac_apply_of_mem]
    exact ⟨le_rfl, hs⟩
  | succ m ih =>
    obtain ⟨ηm, hηm, cm, hcm, hrun⟩ := ih
    obtain ⟨η₁, hη₁, c₁, hc₁, hloc⟩ := industry_Q_high_local hM hF hQ h.z_lt hηm
    refine ⟨min η₁ η, lt_min hη₁ hη, cm * c₁, mul_ne_zero hcm hc₁, fun s hs => ?_⟩
    have hs1 : zhi - η₁ < s.1.2 := lt_of_le_of_lt (by linarith [min_le_left η₁ η]) hs
    have hs2 : zhi - η ≤ s.1.2 := by linarith [min_le_right η₁ η]
    have hx0 : 0 < s.1.1 := h.a_pos.trans_le s.2.1.1
    change cm * c₁ ≤ (kpow (indKernel h Q) m ∘ₖ indKernel h Q) s _
    rw [Kernel.comp_apply' _ _ _ (hmeas _),
      lintegral_indKernel h s (Kernel.measurable_coe _ (hmeas _))]
    have hW : MeasurableSet {w : Icc zlo zhi | zhi - ηm < (w : ℝ)} :=
      measurableSet_lt measurable_const measurable_subtype_coe
    calc cm * c₁ ≤ cm * Q (indZ s) {w | zhi - ηm < (w : ℝ)} := mul_le_mul_right (hloc _ hs1) cm
      _ = ∫⁻ w, {w : Icc zlo zhi | zhi - ηm < (w : ℝ)}.indicator (fun _ => cm) w ∂Q (indZ s) := by
          rw [lintegral_indicator_const hW]
      _ ≤ _ := lintegral_mono fun w => by
          by_cases hw : w ∈ {w : Icc zlo zhi | zhi - ηm < (w : ℝ)}
          · rw [indicator_of_mem hw]
            refine (hrun (indNext h (s, w)) hw).trans (measure_mono fun u hu => ⟨?_, hu.2⟩)
            refine le_trans ?_ hu.1
            rw [Function.iterate_succ_apply]
            exact (h.policy.iterate_mono hzη m (h.policy.pos _ _ hx0 hzη)
              (h.policy.mono_z _ _ _ hx0 hzη.1 hs2 s.2.2.2)).2
          · rw [indicator_of_notMem hw]; exact zero_le

/-- **Runs of low shocks** (the mirror image of `indKernel_highRun`), with `G = g(·, z̲ + η)`. -/
theorem indKernel_lowRun [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) {η : ℝ} (hη : 0 < η) (hηz : η ≤ zhi - zlo) (m : ℕ) :
    ∃ η' > 0, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ∀ s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi), s.1.2 < zlo + η' →
      c ≤ kpow (indKernel h Q) m s
        {t | t.1.1 ≤ (fun x => g x (zlo + η))^[m] s.1.1 ∧ t.1.2 < zlo + η} := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have hzη : zlo + η ∈ Icc zlo zhi := ⟨by linarith, by linarith⟩
  have hmeas : ∀ C : ℝ, MeasurableSet
      {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) | t.1.1 ≤ C ∧ t.1.2 < zlo + η} := fun C =>
    (measurableSet_le (measurable_fst.comp measurable_subtype_coe) measurable_const).inter
      (measurableSet_lt (measurable_snd.comp measurable_subtype_coe) measurable_const)
  induction m with
  | zero =>
    refine ⟨η, hη, 1, one_ne_zero, fun s hs => ?_⟩
    change 1 ≤ Kernel.id s _
    rw [Kernel.id_apply, Measure.dirac_apply_of_mem]
    exact ⟨le_rfl, hs⟩
  | succ m ih =>
    obtain ⟨ηm, hηm, cm, hcm, hrun⟩ := ih
    obtain ⟨η₁, hη₁, c₁, hc₁, hloc⟩ := industry_Q_low_local hM hF hQ h.z_lt hηm
    refine ⟨min η₁ η, lt_min hη₁ hη, cm * c₁, mul_ne_zero hcm hc₁, fun s hs => ?_⟩
    have hs1 : s.1.2 < zlo + η₁ := lt_of_lt_of_le hs (by linarith [min_le_left η₁ η])
    have hs2 : s.1.2 ≤ zlo + η := by linarith [min_le_right η₁ η]
    have hx0 : 0 < s.1.1 := h.a_pos.trans_le s.2.1.1
    change cm * c₁ ≤ (kpow (indKernel h Q) m ∘ₖ indKernel h Q) s _
    rw [Kernel.comp_apply' _ _ _ (hmeas _),
      lintegral_indKernel h s (Kernel.measurable_coe _ (hmeas _))]
    have hW : MeasurableSet {w : Icc zlo zhi | (w : ℝ) < zlo + ηm} :=
      measurableSet_lt measurable_subtype_coe measurable_const
    calc cm * c₁ ≤ cm * Q (indZ s) {w | (w : ℝ) < zlo + ηm} := mul_le_mul_right (hloc _ hs1) cm
      _ = ∫⁻ w, {w : Icc zlo zhi | (w : ℝ) < zlo + ηm}.indicator (fun _ => cm) w ∂Q (indZ s) := by
          rw [lintegral_indicator_const hW]
      _ ≤ _ := lintegral_mono fun w => by
          by_cases hw : w ∈ {w : Icc zlo zhi | (w : ℝ) < zlo + ηm}
          · rw [indicator_of_mem hw]
            refine (hrun (indNext h (s, w)) hw).trans (measure_mono fun u hu => ⟨?_, hu.2⟩)
            refine le_trans hu.1 ?_
            rw [Function.iterate_succ_apply]
            exact (h.policy.iterate_mono hzη m (h.policy.pos _ _ hx0 (indZ s).2)
              (h.policy.mono_z _ _ _ hx0 s.2.1.2 hs2 hzη.2)).2
          · rw [indicator_of_notMem hw]; exact zero_le

/-- The bottom `s̲ = (a, z̲)` of the rectangle. -/
def indBot (h : IndustryRect g zlo zhi a b) : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) :=
  ⟨(a, zlo), left_mem_Icc.2 ⟨h.a_le_b, h.z_lt.le⟩⟩

/-- The top `s̄ = (b, z̄)` of the rectangle. -/
def indTop (h : IndustryRect g zlo zhi a b) : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) :=
  ⟨(b, zhi), right_mem_Icc.2 ⟨h.a_le_b, h.z_lt.le⟩⟩

/-- **From the bottom.** If `x* ≤ g(·, z̄ − η)ᴹ(a)` with `0 < η ≤ z̄ − z*`, then
`P̂^{N+M}(s̲, [s*, s̄]) ≥ ε > 0`: in `N` steps the shock exceeds `z̄ − η_M` with probability at
least `α · min(η_M, z̄ − z̲)` by (2), and then a run of `M` high shocks follows. -/
theorem indKernel_from_bot [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) (sstar : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) {η : ℝ} (hη : 0 < η)
    (hηz : η ≤ zhi - sstar.1.2) (M : ℕ)
    (hreach : sstar.1.1 ≤ (fun x => g x (zhi - η))^[M] a) :
    ∃ ε > 0, ε ≤ (kpow (indKernel h Q) (N + M) (indBot h)).real (Ici sstar) := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have := ex_8_4a (indKernel h Q) (N + M)
  have hzs := sstar.2.1.2
  have hzη : zhi - η ∈ Icc zlo zhi := ⟨by linarith, by linarith⟩
  obtain ⟨ηM, hηM, cM, hcM, hrun⟩ := indKernel_highRun h hM hF hQ hη (by linarith) M
  set u := max (zhi - ηM) zlo
  have hW : MeasurableSet {w : Icc zlo zhi | zhi - ηM < (w : ℝ)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have hmix := hQ.2.2 (indZ (indBot h)) u zhi (le_max_right _ _)
    (max_le (by linarith) h.z_lt.le) le_rfl
  have := ex_8_4a Q N
  have hq : ENNReal.ofReal (α * (zhi - u)) ≤
      kpow Q N (indZ (indBot h)) {w | zhi - ηM < (w : ℝ)} := by
    apply ENNReal.ofReal_le_of_le_toReal
    rw [← measureReal_def]
    exact hmix.trans (measureReal_mono fun w hw => (le_max_left _ _).trans_lt hw.1)
  have hpos : 0 < α * (zhi - u) := mul_pos hQ.2.1 (sub_pos.2 (max_lt (by linarith) h.z_lt))
  have hmain : cM * ENNReal.ofReal (α * (zhi - u)) ≤
      kpow (indKernel h Q) (N + M) (indBot h) (Ici sstar) := by
    rw [kpow_add, Kernel.comp_apply' _ _ _ measurableSet_Ici]
    calc cM * ENNReal.ofReal (α * (zhi - u))
        ≤ cM * kpow (indKernel h Q) N (indBot h) (indZ ⁻¹' {w | zhi - ηM < (w : ℝ)}) := by
          rw [kpow_indKernel_indZ h N _ hW]; exact mul_le_mul_right hq _
      _ = ∫⁻ t, (indZ ⁻¹' {w : Icc zlo zhi | zhi - ηM < (w : ℝ)}).indicator (fun _ => cM) t
            ∂kpow (indKernel h Q) N (indBot h) := by
          rw [lintegral_indicator_const (continuous_indZ.measurable hW)]
      _ ≤ _ := lintegral_mono fun t => by
          by_cases ht : t ∈ indZ ⁻¹' {w : Icc zlo zhi | zhi - ηM < (w : ℝ)}
          · rw [indicator_of_mem ht]
            refine (hrun t ht).trans (measure_mono fun v hv => ?_)
            exact ⟨hreach.trans ((h.policy.iterate_mono hzη M h.a_pos t.2.1.1).2.trans hv.1),
              by linarith [hv.2]⟩
          · rw [indicator_of_notMem ht]; exact zero_le
  have hfin := ne_top_of_le_ne_top (measure_ne_top _ _) hmain
  refine ⟨(cM * ENNReal.ofReal (α * (zhi - u))).toReal,
    ENNReal.toReal_pos (mul_ne_zero hcM (ENNReal.ofReal_pos.2 hpos).ne') hfin, ?_⟩
  rw [measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmain

/-- **From the top** (the mirror image): if `g(·, z̲ + η)ᴹ(b) ≤ x*` with `0 < η ≤ z* − z̲`, then
`P̂^{N+M}(s̄, [s̲, s*]) ≥ ε > 0`. -/
theorem indKernel_from_top [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) (sstar : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) {η : ℝ} (hη : 0 < η)
    (hηz : η ≤ sstar.1.2 - zlo) (M : ℕ)
    (hreach : (fun x => g x (zlo + η))^[M] b ≤ sstar.1.1) :
    ∃ ε > 0, ε ≤ (kpow (indKernel h Q) (N + M) (indTop h)).real (Iic sstar) := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have := ex_8_4a (indKernel h Q) (N + M)
  have hzs := sstar.2.2.2
  have hzη : zlo + η ∈ Icc zlo zhi := ⟨by linarith, by linarith⟩
  obtain ⟨ηM, hηM, cM, hcM, hrun⟩ := indKernel_lowRun h hM hF hQ hη (by linarith) M
  set v := min (zlo + ηM / 2) zhi
  have hW : MeasurableSet {w : Icc zlo zhi | (w : ℝ) < zlo + ηM} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hmix := hQ.2.2 (indZ (indTop h)) zlo v le_rfl (le_min (by linarith) h.z_lt.le)
    (min_le_right _ _)
  have := ex_8_4a Q N
  have hq : ENNReal.ofReal (α * (v - zlo)) ≤
      kpow Q N (indZ (indTop h)) {w | (w : ℝ) < zlo + ηM} := by
    apply ENNReal.ofReal_le_of_le_toReal
    rw [← measureReal_def]
    exact hmix.trans (measureReal_mono fun w hw =>
      lt_of_le_of_lt (hw.2.trans (min_le_left _ _)) (by linarith))
  have hpos : 0 < α * (v - zlo) := mul_pos hQ.2.1 (sub_pos.2 (lt_min (by linarith) h.z_lt))
  have hmain : cM * ENNReal.ofReal (α * (v - zlo)) ≤
      kpow (indKernel h Q) (N + M) (indTop h) (Iic sstar) := by
    rw [kpow_add, Kernel.comp_apply' _ _ _ measurableSet_Iic]
    calc cM * ENNReal.ofReal (α * (v - zlo))
        ≤ cM * kpow (indKernel h Q) N (indTop h) (indZ ⁻¹' {w | (w : ℝ) < zlo + ηM}) := by
          rw [kpow_indKernel_indZ h N _ hW]; exact mul_le_mul_right hq _
      _ = ∫⁻ t, (indZ ⁻¹' {w : Icc zlo zhi | (w : ℝ) < zlo + ηM}).indicator (fun _ => cM) t
            ∂kpow (indKernel h Q) N (indTop h) := by
          rw [lintegral_indicator_const (continuous_indZ.measurable hW)]
      _ ≤ _ := lintegral_mono fun t => by
          by_cases ht : t ∈ indZ ⁻¹' {w : Icc zlo zhi | (w : ℝ) < zlo + ηM}
          · rw [indicator_of_mem ht]
            refine (hrun t ht).trans (measure_mono fun v hv => ?_)
            exact ⟨hv.1.trans (((h.policy.iterate_mono hzη M (h.a_pos.trans_le t.2.1.1)
              t.2.2.1).2).trans hreach), by linarith [hv.2]⟩
          · rw [indicator_of_notMem ht]; exact zero_le
  have hfin := ne_top_of_le_ne_top (measure_ne_top _ _) hmain
  refine ⟨(cM * ENNReal.ofReal (α * (v - zlo))).toReal,
    ENNReal.toReal_pos (mul_ne_zero hcM (ENNReal.ofReal_pos.2 hpos).ne') hfin, ?_⟩
  rw [measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmain

/-! ### Exercise 13.4b: Assumption 12.1 -/

namespace IndustryRect

variable (h : IndustryRect g zlo zhi a b)
include h

/-- The iterates `g(·, z)ⁿ(a)` increase in `n` (as `a ≤ g(a, z̲) ≤ g(a, z)`). -/
theorem iterate_bot_mono {z : ℝ} (hz : z ∈ Icc zlo zhi) :
    Monotone fun n => (fun x => g x z)^[n] a :=
  monotone_nat_of_le_succ fun n => by
    change (fun x => g x z)^[n] a ≤ (fun x => g x z)^[n + 1] a
    rw [Function.iterate_succ_apply]
    exact (h.policy.iterate_mono hz n h.a_pos
      (h.a_le.trans (h.policy.mono_z a zlo z h.a_pos le_rfl hz.1 hz.2))).2

/-- The iterates `g(·, z)ⁿ(b)` decrease in `n` (as `g(b, z) ≤ g(b, z̄) ≤ b`). -/
theorem iterate_top_anti {z : ℝ} (hz : z ∈ Icc zlo zhi) :
    Antitone fun n => (fun x => g x z)^[n] b :=
  antitone_nat_of_succ_le fun n => by
    have hb : 0 < b := h.a_pos.trans_le h.a_le_b
    change (fun x => g x z)^[n + 1] b ≤ (fun x => g x z)^[n] b
    rw [Function.iterate_succ_apply]
    exact (h.policy.iterate_mono hz n (h.policy.pos b z hb hz)
      ((h.policy.mono_z b z zhi hb hz.1 hz.2 le_rfl).trans h.le_b)).2

/-- **Reaching up.** If `x* < x̄`, then `g(·, z̄ − η)ᴹ(a) ≥ x*` for some `M` and some `η > 0` as
small as we like: `g(·, z̄)ⁿ(a) → x̄` (`tendsto_iterate`), and `g(·, z)ᴹ(a)` is continuous in
`z`. -/
theorem bot_reach {xhi : ℝ} (hxhi : 0 < xhi) (hfhi : g xhi zhi = xhi) {xs zs : ℝ}
    (hxs : xs < xhi) (hzs : zlo ≤ zs) (hzs' : zs < zhi) :
    ∃ M η, 0 < η ∧ η ≤ zhi - zs ∧ xs ≤ (fun x => g x (zhi - η))^[M] a := by
  have hzhi : zhi ∈ Icc zlo zhi := ⟨h.z_lt.le, le_rfl⟩
  obtain ⟨M, hM⟩ := ((h.policy.tendsto_iterate hzhi hxhi hfhi h.a_pos).eventually
    (lt_mem_nhds hxs)).exists
  have hc := (h.policy.continuousOn_iterate h.a_pos M).1 zhi hzhi
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hc _ (sub_pos.2 hM)
  have hη : 0 < min (δ / 2) (zhi - zs) := lt_min (half_pos hδ) (sub_pos.2 hzs')
  refine ⟨M, min (δ / 2) (zhi - zs), hη, min_le_right _ _, ?_⟩
  have h1 := min_le_left (δ / 2) (zhi - zs)
  have h2 := min_le_right (δ / 2) (zhi - zs)
  have hmem : zhi - min (δ / 2) (zhi - zs) ∈ Icc zlo zhi := ⟨by linarith, by linarith⟩
  have hd : dist (zhi - min (δ / 2) (zhi - zs)) zhi < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have := hball hmem hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

/-- **Reaching down** (the mirror image): if `x̲ < x*`, then `g(·, z̲ + η)ᴹ(b) ≤ x*` for some
`M` and some small `η > 0`. -/
theorem top_reach {xlo : ℝ} (hxlo : 0 < xlo) (hflo : g xlo zlo = xlo) {xs zs : ℝ}
    (hxs : xlo < xs) (hzs : zlo < zs) (hzs' : zs ≤ zhi) :
    ∃ M η, 0 < η ∧ η ≤ zs - zlo ∧ (fun x => g x (zlo + η))^[M] b ≤ xs := by
  have hzlo : zlo ∈ Icc zlo zhi := ⟨le_rfl, h.z_lt.le⟩
  have hb : 0 < b := h.a_pos.trans_le h.a_le_b
  obtain ⟨M, hM⟩ := ((h.policy.tendsto_iterate hzlo hxlo hflo hb).eventually
    (gt_mem_nhds hxs)).exists
  have hc := (h.policy.continuousOn_iterate hb M).1 zlo hzlo
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hc _ (sub_pos.2 hM)
  have hη : 0 < min (δ / 2) (zs - zlo) := lt_min (half_pos hδ) (sub_pos.2 hzs)
  refine ⟨M, min (δ / 2) (zs - zlo), hη, min_le_right _ _, ?_⟩
  have h1 := min_le_left (δ / 2) (zs - zlo)
  have h2 := min_le_right (δ / 2) (zs - zlo)
  have hmem : zlo + min (δ / 2) (zs - zlo) ∈ Icc zlo zhi := ⟨by linarith, by linarith⟩
  have hd : dist (zlo + min (δ / 2) (zs - zlo)) zlo < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have := hball hmem hd
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.2]

end IndustryRect

/-- **Exercise 13.4b on a rectangle.** Let `s* = (x*, z*)` be a point of `[a, b] × Z` that is
reachable from below (`x* ≤ g(·, z̄ − η)ᴹ(a)` for some `M`, `0 < η ≤ z̄ − z*`) and from above
(`g(·, z̲ + η)ᴹ(b) ≤ x*`, `0 < η ≤ z* − z̲`). Then Assumption 12.1 holds at `s*`: there are
`N′ ≥ 1` and `ε > 0` with `P̂^{N′}(s̲, [s*, s̄]) ≥ ε` and `P̂^{N′}(s̄, [s̲, s*]) ≥ ε`. -/
theorem ex_13_4b_rect [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) (sstar : Icc ((a, zlo) : ℝ × ℝ) (b, zhi))
    (hbot : ∃ M η, 0 < η ∧ η ≤ zhi - sstar.1.2 ∧ sstar.1.1 ≤ (fun x => g x (zhi - η))^[M] a)
    (htop : ∃ M η, 0 < η ∧ η ≤ sstar.1.2 - zlo ∧ (fun x => g x (zlo + η))^[M] b ≤ sstar.1.1) :
    ∃ N' : ℕ, ∃ ε > 0, 1 ≤ N' ∧ ε ≤ (kpow (indKernel h Q) N' (indBot h)).real (Ici sstar) ∧
      ε ≤ (kpow (indKernel h Q) N' (indTop h)).real (Iic sstar) := by
  obtain ⟨M₁, η₁, hη₁, hη₁z, h₁⟩ := hbot
  obtain ⟨M₂, η₂, hη₂, hη₂z, h₂⟩ := htop
  have hz₁ : zhi - η₁ ∈ Icc zlo zhi := ⟨by linarith [sstar.2.1.2], by linarith⟩
  have hz₂ : zlo + η₂ ∈ Icc zlo zhi := ⟨by linarith, by linarith [sstar.2.2.2]⟩
  obtain ⟨ε₁, hε₁, hb⟩ := indKernel_from_bot h hM hF hQ sstar hη₁ hη₁z (max M₁ M₂)
    (h₁.trans (h.iterate_bot_mono hz₁ (le_max_left _ _)))
  obtain ⟨ε₂, hε₂, ht⟩ := indKernel_from_top h hM hF hQ sstar hη₂ hη₂z (max M₁ M₂)
    ((h.iterate_top_anti hz₂ (le_max_right _ _)).trans h₂)
  exact ⟨N + max M₁ M₂, min ε₁ ε₂, lt_min hε₁ hε₂, by have := hQ.1; omega,
    (min_le_left _ _).trans hb, (min_le_right _ _).trans ht⟩

/-- **Theorem 12.12 on a rectangle**: under the hypotheses of `ex_13_4b_rect`, `P̂` has a unique
invariant probability measure `λ*` on `[a, b] × Z`, and `T*ⁿλ ⇒ λ*` for every `λ`. -/
theorem ex_13_4b_rect_stable [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) (sstar : Icc ((a, zlo) : ℝ × ℝ) (b, zhi))
    (hbot : ∃ M η, 0 < η ∧ η ≤ zhi - sstar.1.2 ∧ sstar.1.1 ≤ (fun x => g x (zhi - η))^[M] a)
    (htop : ∃ M η, 0 < η ∧ η ≤ sstar.1.2 - zlo ∧ (fun x => g x (zlo + η))^[M] b ≤ sstar.1.1) :
    ∃ μ : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (indKernel h Q) μ = μ ∧
      (∀ ν : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)), IsProbabilityMeasure ν →
        adjointOp (indKernel h Q) ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp (indKernel h Q))^[n] lam₀) μ := by
  obtain ⟨N', ε, hε, hN', hb, ht⟩ := ex_13_4b_rect h hM hF hQ sstar hbot htop
  have := isMarkovKernel_indKernel h (Q := Q)
  exact theorem_12_12_prod ⟨h.a_le_b, h.z_lt.le⟩ (indKernel h Q) (ex_13_4a_monotone h hM)
    (ex_13_4a_feller h hF) hε hN' hb ht

/-- The point `s* = ((x̲ + x̄)/2, (z̲ + z̄)/2)` of `Ŝ = [x̲, x̄] × Z`. -/
noncomputable def indMid {xlo xhi : ℝ} (h : IndustryRect g zlo zhi xlo xhi) :
    Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi) :=
  ⟨((xlo + xhi) / 2, (zlo + zhi) / 2), ⟨by linarith [h.a_le_b], by linarith [h.z_lt]⟩,
    ⟨by linarith [h.a_le_b], by linarith [h.z_lt]⟩⟩

/-- **Exercise 13.4b.** On `Ŝ = [x̲, x̄] × Z` (`x̲ = g(x̲, z̲)`, `x̄ = g(x̄, z̄)`), Assumption 12.1
holds at `s* = ((x̲ + x̄)/2, (z̲ + z̄)/2)`: there are `N′ ≥ 1` and `ε > 0` with
`P̂^{N′}(s̲, [s*, s̄]) ≥ ε` and `P̂^{N′}(s̄, [s̲, s*]) ≥ ε`. If `x̲ < x̄`, runs of high shocks carry
`x` from `x̲` above `x*` and runs of low shocks carry it from `x̄` below `x*`; if `x̲ = x̄` only
the shock has to move, which (2) provides. -/
theorem ex_13_4b {xlo xhi : ℝ} (h : IndustryRect g zlo zhi xlo xhi) (hflo : g xlo zlo = xlo)
    (hfhi : g xhi zhi = xhi) [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α) :
    ∃ N' : ℕ, ∃ ε > 0, 1 ≤ N' ∧
      ε ≤ (kpow (indKernel h Q) N' (indBot h)).real (Ici (indMid h)) ∧
      ε ≤ (kpow (indKernel h Q) N' (indTop h)).real (Iic (indMid h)) := by
  have hz := h.z_lt
  refine ex_13_4b_rect h hM hF hQ (indMid h) ?_ ?_
  · rcases h.a_le_b.eq_or_lt with heq | hlt
    · refine ⟨0, (zhi - zlo) / 2, by linarith,
        show (zhi - zlo) / 2 ≤ zhi - (zlo + zhi) / 2 by linarith, ?_⟩
      change (xlo + xhi) / 2 ≤ xlo
      linarith
    · exact h.bot_reach (h.a_pos.trans hlt) hfhi
        (show (xlo + xhi) / 2 < xhi by linarith) (show zlo ≤ (zlo + zhi) / 2 by linarith)
        (show (zlo + zhi) / 2 < zhi by linarith)
  · rcases h.a_le_b.eq_or_lt with heq | hlt
    · refine ⟨0, (zhi - zlo) / 2, by linarith,
        show (zhi - zlo) / 2 ≤ (zlo + zhi) / 2 - zlo by linarith, ?_⟩
      change xhi ≤ (xlo + xhi) / 2
      linarith
    · exact h.top_reach h.a_pos hflo
        (show xlo < (xlo + xhi) / 2 by linarith) (show zlo < (zlo + zhi) / 2 by linarith)
        (show (zlo + zhi) / 2 ≤ zhi by linarith)

/-- **Exercise 13.4b**, conclusion (p. 397, via Theorem 12.12): `P̂` has a unique invariant
probability measure `λ*` on `Ŝ`, and `T*ⁿλ ⇒ λ*` for every probability measure `λ` on `Ŝ`. -/
theorem ex_13_4b_stable {xlo xhi : ℝ} (h : IndustryRect g zlo zhi xlo xhi)
    (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) [IsMarkovKernel Q] (hM : IsMonotoneTF Q)
    (hF : IsFeller Q) (hQ : IndustryMixing Q N α) :
    ∃ μ : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi)), IsProbabilityMeasure μ ∧
      adjointOp (indKernel h Q) μ = μ ∧
      (∀ ν : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi)), IsProbabilityMeasure ν →
        adjointOp (indKernel h Q) ν = ν → ν = μ) ∧
      ∀ lam₀ : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi)), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp (indKernel h Q))^[n] lam₀) μ := by
  obtain ⟨N', ε, hε, hN', hb, ht⟩ := ex_13_4b h hflo hfhi hM hF hQ
  have := isMarkovKernel_indKernel h (Q := Q)
  exact theorem_12_12_prod ⟨h.a_le_b, h.z_lt.le⟩ (indKernel h Q) (ex_13_4a_monotone h hM)
    (ex_13_4a_feller h hF) hε hN' hb ht

/-! ### Exercise 13.4c -/

/-- The inclusion of `[x̲, x̄] × Z` into a larger rectangle `[a, b] × Z`. -/
def indIncl {xlo xhi : ℝ} (hax : a ≤ xlo) (hxb : xhi ≤ b)
    (s : Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi)) : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) :=
  ⟨s.1, ⟨hax.trans s.2.1.1, s.2.1.2⟩, ⟨s.2.2.1.trans hxb, s.2.2.2⟩⟩

/-- The inclusion of rectangles is continuous. -/
theorem continuous_indIncl {xlo xhi : ℝ} (hax : a ≤ xlo) (hxb : xhi ≤ b) :
    Continuous (indIncl (zlo := zlo) (zhi := zhi) hax hxb) :=
  continuous_subtype_val.subtype_mk _

/-- `P̂` on the larger rectangle restricts to `P̂` on the smaller one:
`P_R(ι s, ·) = P̂(s, ·) ∘ ι⁻¹`. -/
theorem indKernel_indIncl {xlo xhi : ℝ} (hS : IndustryRect g zlo zhi xlo xhi)
    (hR : IndustryRect g zlo zhi a b) (hax : a ≤ xlo) (hxb : xhi ≤ b) [IsMarkovKernel Q]
    (s : Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi)) :
    indKernel hR Q (indIncl hax hxb s) = (indKernel hS Q s).map (indIncl hax hxb) := by
  rw [indKernel_apply, indKernel_apply,
    Measure.map_map (continuous_indIncl hax hxb).measurable (measurable_indNext_left hS s)]
  rfl

/-- `T*_R(λ ∘ ι⁻¹) = (T̂*λ) ∘ ι⁻¹`. -/
theorem adjointOp_indIncl {xlo xhi : ℝ} (hS : IndustryRect g zlo zhi xlo xhi)
    (hR : IndustryRect g zlo zhi a b) (hax : a ≤ xlo) (hxb : xhi ≤ b) [IsMarkovKernel Q]
    (lam : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi))) :
    adjointOp (indKernel hR Q) (lam.map (indIncl hax hxb)) =
      (adjointOp (indKernel hS Q) lam).map (indIncl hax hxb) := by
  have hι := (continuous_indIncl (zlo := zlo) (zhi := zhi) hax hxb).measurable
  ext A hA
  rw [adjointOp_apply _ _ hA, Measure.map_apply hι hA, adjointOp_apply _ _ (hι hA),
    lintegral_map (Kernel.measurable_coe _ hA) hι]
  refine lintegral_congr fun s => ?_
  rw [indKernel_indIncl hS hR hax hxb, Measure.map_apply hι hA]

/-- **Exercise 13.4c on compact sets of initial capital, `x̲ < x̄`.** Every rectangle
`[a, b] × Z` with `0 < a ≤ x̲` and `x̄ ≤ b` satisfies Assumption 12.1 (at
`s* = ((x̲ + x̄)/2, (z̲ + z̄)/2)`), and its unique invariant probability measure is `λ*` (the
invariant measure of `P̂` on `Ŝ`) extended by zero. Hence `T*ⁿλ ⇒ λ*` for every initial
distribution `λ` concentrated on such a rectangle, i.e. with initial capital bounded and bounded
away from zero. -/
theorem ex_13_4c_rect {xlo xhi : ℝ} (hS : IndustryRect g zlo zhi xlo xhi)
    (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) (hlt : xlo < xhi)
    (hR : IndustryRect g zlo zhi a b) (hax : a ≤ xlo) (hxb : xhi ≤ b) [IsMarkovKernel Q]
    (hM : IsMonotoneTF Q) (hF : IsFeller Q) (hQ : IndustryMixing Q N α)
    {lamStar : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi))} [IsProbabilityMeasure lamStar]
    (hinv : adjointOp (indKernel hS Q) lamStar = lamStar) :
    (∀ ν : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)), IsProbabilityMeasure ν →
        adjointOp (indKernel hR Q) ν = ν → ν = lamStar.map (indIncl hax hxb)) ∧
      ∀ lam₀ : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)), IsProbabilityMeasure lam₀ →
        ConvWeak (fun n => (adjointOp (indKernel hR Q))^[n] lam₀)
          (lamStar.map (indIncl hax hxb)) := by
  have hz := hR.z_lt
  set sstar : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) :=
    ⟨((xlo + xhi) / 2, (zlo + zhi) / 2), ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨μ, -, -, huniq, hconv⟩ := ex_13_4b_rect_stable hR hM hF hQ sstar
    (hR.bot_reach (hS.a_pos.trans hlt) hfhi (show (xlo + xhi) / 2 < xhi by linarith)
      (show zlo ≤ (zlo + zhi) / 2 by linarith) (show (zlo + zhi) / 2 < zhi by linarith))
    (hR.top_reach hS.a_pos hflo (show xlo < (xlo + xhi) / 2 by linarith)
      (show zlo < (zlo + zhi) / 2 by linarith) (show (zlo + zhi) / 2 ≤ zhi by linarith))
  have hprob : IsProbabilityMeasure (lamStar.map (indIncl hax hxb)) := inferInstance
  have heq : lamStar.map (indIncl hax hxb) = μ :=
    huniq _ hprob (by rw [adjointOp_indIncl hS hR hax hxb, hinv])
  rw [heq]
  exact ⟨huniq, hconv⟩

/-- **Squeezing, for the transition function.** `P̂ⁿ((x, z), ·)` is concentrated on
`[g(·, z̲)ⁿ(x), g(·, z̄)ⁿ(x)] × Z`. -/
theorem kpow_indKernel_squeeze [IsMarkovKernel Q] (n : ℕ) (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    kpow (indKernel h Q) n s
      {t | (fun x => g x zlo)^[n] s.1.1 ≤ t.1.1 ∧ t.1.1 ≤ (fun x => g x zhi)^[n] s.1.1} = 1 := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have hzlo : zlo ∈ Icc zlo zhi := ⟨le_rfl, h.z_lt.le⟩
  have hzhi : zhi ∈ Icc zlo zhi := ⟨h.z_lt.le, le_rfl⟩
  have hmeas : ∀ C D : ℝ, MeasurableSet
      {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) | C ≤ t.1.1 ∧ t.1.1 ≤ D} := fun C D =>
    (measurableSet_le measurable_const (measurable_fst.comp measurable_subtype_coe)).inter
      (measurableSet_le (measurable_fst.comp measurable_subtype_coe) measurable_const)
  induction n generalizing s with
  | zero =>
    change Kernel.id s _ = 1
    rw [Kernel.id_apply, Measure.dirac_apply_of_mem]
    exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have := ex_8_4a (indKernel h Q) (n + 1)
    refine le_antisymm prob_le_one ?_
    change 1 ≤ (kpow (indKernel h Q) n ∘ₖ indKernel h Q) s _
    rw [Kernel.comp_apply' _ _ _ (hmeas _ _),
      lintegral_indKernel h s (Kernel.measurable_coe _ (hmeas _ _))]
    have hx0 : 0 < s.1.1 := h.a_pos.trans_le s.2.1.1
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Q (indZ s) := by rw [lintegral_const, measure_univ, one_mul]
      _ ≤ _ := lintegral_mono fun w => by
          refine (ih (indNext h (s, w))).ge.trans (measure_mono fun u hu => ⟨?_, ?_⟩)
          · refine le_trans ?_ hu.1
            rw [Function.iterate_succ_apply]
            exact (h.policy.iterate_mono hzlo n (h.policy.pos _ _ hx0 hzlo)
              (h.policy.mono_z _ _ _ hx0 le_rfl (indZ s).2.1 (indZ s).2.2)).2
          · refine hu.2.trans ?_
            rw [Function.iterate_succ_apply]
            exact (h.policy.iterate_mono hzhi n (h.policy.pos _ _ hx0 (indZ s).2)
              (h.policy.mono_z _ _ _ hx0 (indZ s).2.1 (indZ s).2.2 le_rfl)).2

/-- **Mass is squeezed onto `X̂`** (Exercise 13.4c remark, transition-function form). For every
starting state `s = (x, z)` of an invariant rectangle and every `δ > 0`, from some `T` on,
`P̂ⁿ(s, (x̲ − δ, x̄ + δ) × Z) = 1`. -/
theorem ex_13_4c_squeeze_kernel [IsMarkovKernel Q] {xlo xhi : ℝ} (hlo : 0 < xlo) (hhi : 0 < xhi)
    (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T, ∀ n ≥ T, kpow (indKernel h Q) n s {t | xlo - δ < t.1.1 ∧ t.1.1 < xhi + δ} = 1 := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have hx0 : 0 < s.1.1 := h.a_pos.trans_le s.2.1.1
  have h1 := (h.policy.tendsto_iterate ⟨le_rfl, h.z_lt.le⟩ hlo hflo hx0).eventually
    (lt_mem_nhds (show xlo - δ < xlo by linarith))
  have h2 := (h.policy.tendsto_iterate ⟨h.z_lt.le, le_rfl⟩ hhi hfhi hx0).eventually
    (gt_mem_nhds (show xhi < xhi + δ by linarith))
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨T, fun n hn => ?_⟩
  have := ex_8_4a (indKernel h Q) n
  refine le_antisymm prob_le_one ((kpow_indKernel_squeeze h n s).ge.trans
    (measure_mono fun t ht => ⟨?_, ?_⟩))
  · exact lt_of_lt_of_le (hT n hn).1 ht.1
  · exact lt_of_le_of_lt ht.2 (hT n hn).2

/-- **Squeezing along a shock path** (Exercise 13.4c remark). Whatever the shocks
`zₜ ∈ Z`, the path `xₜ₊₁ = g(xₜ, zₜ)` from `x₀ > 0` satisfies
`g(·, z̲)ᵗ(x₀) ≤ xₜ ≤ g(·, z̄)ᵗ(x₀)`. -/
theorem ex_13_4c_path_bounds (hg : IndustryPolicy g zlo zhi) {x z : ℕ → ℝ}
    (hz : ∀ n, z n ∈ Icc zlo zhi) (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = g (x n) (z n))
    (n : ℕ) :
    0 < x n ∧ (fun y => g y zlo)^[n] (x 0) ≤ x n ∧ x n ≤ (fun y => g y zhi)^[n] (x 0) := by
  induction n with
  | zero => exact ⟨hx0, le_rfl, le_rfl⟩
  | succ n ih =>
    obtain ⟨h0, hl, hu⟩ := ih
    have hzlo : zlo ∈ Icc zlo zhi := ⟨le_rfl, (hz n).1.trans (hz n).2⟩
    have hzhi : zhi ∈ Icc zlo zhi := ⟨(hz n).1.trans (hz n).2, le_rfl⟩
    have hl0 := (hg.iterate_mono hzlo n hx0 le_rfl).1
    rw [hx, Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨hg.pos _ _ h0 (hz n),
      (hg.mono_x hl0 hl hzlo).trans (hg.mono_z _ _ _ h0 le_rfl (hz n).1 (hz n).2),
      (hg.mono_z _ _ _ h0 (hz n).1 (hz n).2 le_rfl).trans (hg.mono_x h0 hu hzhi)⟩

/-- **The gap to `X̂` shrinks** (Exercise 13.4c remark, corrected). If `xₜ > x̄` then
`xₜ₊₁ − x̄ < xₜ − x̄` and `xₜ₊₁ > x̲`; if `xₜ < x̲` then `x̲ − xₜ₊₁ < x̲ − xₜ` and `xₜ₊₁ < x̄`; if
`xₜ ∈ X̂` then `xₜ₊₁ ∈ X̂`. -/
theorem ex_13_4c_gap (hg : IndustryPolicy g zlo zhi) {xlo xhi : ℝ} (hlo : 0 < xlo)
    (hloh : xlo ≤ xhi) (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) {x z : ℝ}
    (hz : z ∈ Icc zlo zhi) :
    (xhi < x → g x z - xhi < x - xhi ∧ xlo < g x z) ∧
      (0 < x → x < xlo → xlo - g x z < xlo - x ∧ g x z < xhi) ∧
      (x ∈ Icc xlo xhi → g x z ∈ Icc xlo xhi) := by
  have hzlo : zlo ∈ Icc zlo zhi := ⟨le_rfl, hz.1.trans hz.2⟩
  have hzhi : zhi ∈ Icc zlo zhi := ⟨hz.1.trans hz.2, le_rfl⟩
  have hhi : 0 < xhi := hlo.trans_le hloh
  refine ⟨fun hx => ⟨?_, ?_⟩, fun hx0 hx => ⟨?_, ?_⟩, fun hx => ?_⟩
  · have h1 := hg.slope_lt xhi x zhi hhi hx hzhi
    have h2 := hg.mono_z x z zhi (hhi.trans hx) hz.1 hz.2 le_rfl
    linarith
  · have h1 := hg.strictMono_x xhi x z hhi hx hz
    have h2 := hg.mono hlo hloh hzlo hz hz.1
    linarith
  · have h1 := hg.slope_lt x xlo zlo hx0 hx hzlo
    have h2 := hg.mono_z x zlo z hx0 le_rfl hz.1 hz.2
    linarith
  · have h1 := hg.strictMono_x x xlo z hx0 hx hz
    have h2 := hg.mono hlo hloh hz hzhi hz.2
    linarith
  · exact ⟨hflo.ge.trans (hg.mono hlo hx.1 hzlo hz hz.1),
      (hg.mono (hlo.trans_le hx.1) hx.2 hz hzhi hz.2).trans hfhi.le⟩

/-- **Uniform convergence to `X̂` along shock paths** (Exercise 13.4c remark). For `x₀ > 0` and
`δ > 0` there is `T` such that every path `xₜ₊₁ = g(xₜ, zₜ)` from `x₀`, whatever the shocks
`zₜ ∈ Z`, lies in `(x̲ − δ, x̄ + δ)` from `T` on. -/
theorem ex_13_4c_squeeze_path (hg : IndustryPolicy g zlo zhi) (hz : zlo ≤ zhi) {xlo xhi : ℝ}
    (hlo : 0 < xlo) (hhi : 0 < xhi) (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi)
    {x₀ δ : ℝ} (hx₀ : 0 < x₀) (hδ : 0 < δ) :
    ∃ T, ∀ x z : ℕ → ℝ, (∀ n, z n ∈ Icc zlo zhi) → x 0 = x₀ →
      (∀ n, x (n + 1) = g (x n) (z n)) → ∀ n ≥ T, xlo - δ < x n ∧ x n < xhi + δ := by
  have h1 := (hg.tendsto_iterate ⟨le_rfl, hz⟩ hlo hflo hx₀).eventually
    (lt_mem_nhds (show xlo - δ < xlo by linarith))
  have h2 := (hg.tendsto_iterate ⟨hz, le_rfl⟩ hhi hfhi hx₀).eventually
    (gt_mem_nhds (show xhi < xhi + δ by linarith))
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨T, fun x z hzs hx0 hx n hn => ?_⟩
  obtain ⟨-, hl, hu⟩ := ex_13_4c_path_bounds hg hzs (hx0 ▸ hx₀) hx n
  rw [hx0] at hl hu
  exact ⟨lt_of_lt_of_le (hT n hn).1 hl, lt_of_le_of_lt hu (hT n hn).2⟩

/-- **Counterexample to the remark on Exercise 13.4c** (`0 ≤ xₜ₊₁ − x̄` whenever `xₜ > x̄`):
`g(x, z) = (x + z)/2` on `Z = [1, 3]` satisfies (i), (ii), with `x̲ = 1`, `x̄ = 3`; from
`x₀ = 4 > x̄` the low shock `z₀ = 1` gives `x₁ = 5/2 < x̄`. The gap shrinks (`ex_13_4c_gap`),
but the path can jump into `X̂` rather than approach it from above. -/
theorem ex_13_4c_remark_counterexample :
    IndustryPolicy (fun x z => (x + z) / 2) 1 3 ∧ (1 + 1) / 2 = (1 : ℝ) ∧ (3 + 3) / 2 = (3 : ℝ) ∧
      (3 : ℝ) < 4 ∧ (4 + 1) / 2 - 3 < (0 : ℝ) := by
  refine ⟨⟨((continuous_fst.add continuous_snd).div_const 2).continuousOn,
    fun x z hx hz => by linarith [hz.1], fun x x' z _ h _ => by linarith,
    fun x x' z _ h _ => by linarith, fun x z z' _ _ h _ => by linarith⟩,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Iterates of `g(·, z)` started strictly below (above) a fixed point stay strictly below
(above) it. -/
theorem IndustryPolicy.iterate_lt_fixed (hg : IndustryPolicy g zlo zhi) {z p x : ℝ}
    (hz : z ∈ Icc zlo zhi) (hp : g p z = p) (hx : 0 < x) (n : ℕ) :
    (x < p → (fun y => g y z)^[n] x < p) ∧ (p < x → 0 < p → p < (fun y => g y z)^[n] x) := by
  induction n with
  | zero => exact ⟨id, fun h _ => h⟩
  | succ n ih =>
    have h0 := (hg.iterate_mono hz n hx le_rfl).1
    simp only [Function.iterate_succ_apply']
    exact ⟨fun hxp => hp ▸ hg.strictMono_x _ _ _ h0 (ih.1 hxp) hz,
      fun hpx hp0 => hp ▸ hg.strictMono_x _ _ _ hp0 (ih.2 hpx hp0) hz⟩

/-- **Why `x̲ < x̄` matters for Exercise 13.4c on larger rectangles.** If `x̲ = x̄ = p` and
`a < p < b`, Assumption 12.1 fails on `[a, b] × Z` for every `s*` and `N`: from `s̲` the capital
stays below `p` (`xₙ ≤ g(·, z̄)ⁿ(a) < p`) and from `s̄` it stays above `p`. So Theorem 12.12
cannot be applied on larger rectangles in the degenerate case, and the convergence there needs a
different argument (the capital converges to `p` deterministically). -/
theorem ex_13_4c_degenerate_no_assumption [IsMarkovKernel Q] {p : ℝ} (hp : 0 < p)
    (hflo : g p zlo = p) (hfhi : g p zhi = p) (hap : a < p) (hpb : p < b)
    (sstar : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) (n : ℕ) :
    kpow (indKernel h Q) n (indBot h) (Ici sstar) = 0 ∨
      kpow (indKernel h Q) n (indTop h) (Iic sstar) = 0 := by
  have := isMarkovKernel_indKernel h (Q := Q)
  have := ex_8_4a (indKernel h Q) n
  have hzlo : zlo ∈ Icc zlo zhi := ⟨le_rfl, h.z_lt.le⟩
  have hzhi : zhi ∈ Icc zlo zhi := ⟨h.z_lt.le, le_rfl⟩
  have hmeas : ∀ C D : ℝ, MeasurableSet
      {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) | C ≤ t.1.1 ∧ t.1.1 ≤ D} := fun C D =>
    (measurableSet_le measurable_const (measurable_fst.comp measurable_subtype_coe)).inter
      (measurableSet_le (measurable_fst.comp measurable_subtype_coe) measurable_const)
  have hnull : ∀ (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi))
      {A : Set (Icc ((a, zlo) : ℝ × ℝ) (b, zhi))},
      (∀ t ∈ A, ¬ ((fun x => g x zlo)^[n] s.1.1 ≤ t.1.1 ∧
        t.1.1 ≤ (fun x => g x zhi)^[n] s.1.1)) → kpow (indKernel h Q) n s A = 0 := by
    intro s A hA
    have h1 := kpow_indKernel_squeeze h n s (Q := Q)
    refine measure_mono_null (t := {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) |
      (fun x => g x zlo)^[n] s.1.1 ≤ t.1.1 ∧ t.1.1 ≤ (fun x => g x zhi)^[n] s.1.1}ᶜ)
      (fun t ht => hA t ht) ?_
    rw [prob_compl_eq_zero_iff (hmeas _ _)]
    exact h1
  rcases le_or_gt p sstar.1.1 with hs | hs
  · left
    refine hnull _ fun t ht hmem => ?_
    have := (h.policy.iterate_lt_fixed hzhi hfhi h.a_pos n).1 hap
    have ht' : sstar.1.1 ≤ t.1.1 := ht.1
    exact absurd (lt_of_le_of_lt hmem.2 this) (not_lt.2 (hs.trans ht'))
  · right
    refine hnull _ fun t ht hmem => ?_
    have := (h.policy.iterate_lt_fixed hzlo hflo (hp.trans hpb) n).2 hpb hp
    have ht' : t.1.1 ≤ sstar.1.1 := ht.1
    exact absurd (this.trans_le hmem.1) (not_lt.2 (ht'.trans hs.le))

/-- The `z`-marginal of `P̂ⁿ(s, ·)` is `Qⁿ(z, ·)` (as an image measure). -/
theorem kpow_indKernel_map_indZ [IsMarkovKernel Q] (n : ℕ)
    (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    (kpow (indKernel h Q) n s).map indZ = kpow Q n (indZ s) :=
  Measure.ext fun B hB => by
    rw [Measure.map_apply continuous_indZ.measurable hB, kpow_indKernel_indZ h n s hB]

/-- The embedding `w ↦ (p, w)` of `Z` onto `{p} × Z`. -/
def indDeg {p : ℝ} (w : Icc zlo zhi) : Icc ((p, zlo) : ℝ × ℝ) (p, zhi) :=
  ⟨(p, w.1), ⟨le_rfl, w.2.1⟩, ⟨le_rfl, w.2.2⟩⟩

/-- `w ↦ (p, w)` is continuous. -/
theorem continuous_indDeg {p : ℝ} : Continuous (indDeg (zlo := zlo) (zhi := zhi) (p := p)) :=
  (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- In the degenerate case `x̲ = x̄ = p`, `P̂` on `{p} × Z` is `Q` carried by `w ↦ (p, w)`. -/
theorem indKernel_indDeg {p : ℝ} (hS : IndustryRect g zlo zhi p p) (hflo : g p zlo = p)
    (hfhi : g p zhi = p) [IsMarkovKernel Q] (w : Icc zlo zhi) :
    indKernel hS Q (indDeg w) = (Q w).map indDeg := by
  rw [indKernel_apply]
  change Measure.map _ (Q w) = _
  congr 1
  funext w'
  have hp : 0 < p := hS.a_pos
  have hgp : g p w = p :=
    le_antisymm ((hS.policy.mono_z p w zhi hp w.2.1 w.2.2 le_rfl).trans hfhi.le)
      (hflo.symm.le.trans (hS.policy.mono_z p zlo w hp le_rfl w.2.1 w.2.2))
  exact Subtype.ext (Prod.ext hgp rfl)

/-- In the degenerate case, `T̂*(μ ∘ j⁻¹) = (T*_Q μ) ∘ j⁻¹` for `j(w) = (p, w)`. -/
theorem adjointOp_indDeg {p : ℝ} (hS : IndustryRect g zlo zhi p p) (hflo : g p zlo = p)
    (hfhi : g p zhi = p) [IsMarkovKernel Q] (μ : Measure (Icc zlo zhi)) :
    adjointOp (indKernel hS Q) (μ.map indDeg) = (adjointOp Q μ).map indDeg := by
  have hd := (continuous_indDeg (zlo := zlo) (zhi := zhi) (p := p)).measurable
  ext A hA
  rw [adjointOp_apply _ _ hA, Measure.map_apply hd hA, adjointOp_apply _ _ (hd hA),
    lintegral_map (Kernel.measurable_coe _ hA) hd]
  refine lintegral_congr fun w => ?_
  rw [indKernel_indDeg hS hflo hfhi, Measure.map_apply hd hA]

/-- **Exercise 13.4c on compact sets of initial capital, `x̲ = x̄ = p`.** Here Assumption 12.1
fails on larger rectangles (`ex_13_4c_degenerate_no_assumption`), so a direct argument is used:
`λ* = μ* ∘ (w ↦ (p, w))⁻¹` with `μ*` the invariant measure of `Q`; from any `s ∈ [a, b] × Z` the
capital converges to `p` uniformly over shock paths (`kpow_indKernel_squeeze`), `f` is uniformly
continuous on the compact rectangle, and the shock converges weakly to `μ*`. Hence
`T*ⁿλ ⇒ λ*` for every `λ` on `[a, b] × Z`, `0 < a ≤ p ≤ b`. -/
theorem ex_13_4c_rect_degenerate {p : ℝ} (hS : IndustryRect g zlo zhi p p) (hflo : g p zlo = p)
    (hfhi : g p zhi = p) (hR : IndustryRect g zlo zhi a b) (hap : a ≤ p) (hpb : p ≤ b)
    [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q) (hQ : IndustryMixing Q N α)
    {lamStar : Measure (Icc ((p, zlo) : ℝ × ℝ) (p, zhi))} [IsProbabilityMeasure lamStar]
    (hinv : adjointOp (indKernel hS Q) lamStar = lamStar)
    (lam₀ : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi))) [IsProbabilityMeasure lam₀] :
    ConvWeak (fun n => (adjointOp (indKernel hR Q))^[n] lam₀) (lamStar.map (indIncl hap hpb)) := by
  have := isMarkovKernel_indKernel hR (Q := Q)
  have := isMarkovKernel_indKernel hS (Q := Q)
  have hp : 0 < p := hS.a_pos
  obtain ⟨μ, hμ, hfix, -, hconvQ⟩ := industry_shock_stable hR.z_lt hM hF hQ
  obtain ⟨μS, -, -, huniqS, -⟩ := ex_13_4b_stable hS hflo hfhi hM hF hQ
  have hd := (continuous_indDeg (zlo := zlo) (zhi := zhi) (p := p)).measurable
  have hι := (continuous_indIncl (zlo := zlo) (zhi := zhi) hap hpb).measurable
  have hlam : lamStar = μ.map indDeg := by
    rw [huniqS lamStar inferInstance hinv,
      huniqS (μ.map indDeg) inferInstance (by rw [adjointOp_indDeg hS hflo hfhi, hfix])]
  subst hlam
  intro f
  set FB : Icc zlo zhi →ᵇ ℝ := f.compContinuous
    ⟨fun w => indIncl hap hpb (indDeg w), (continuous_indIncl hap hpb).comp continuous_indDeg⟩
  set G : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) →ᵇ ℝ := FB.compContinuous ⟨indZ, continuous_indZ⟩
  have hlim : ∫ s, f s ∂(μ.map indDeg).map (indIncl hap hpb) = ∫ w, FB w ∂μ := by
    rw [Measure.map_map hι hd, integral_map (hι.comp hd).aemeasurable
      f.continuous.aestronglyMeasurable]
    rfl
  rw [hlim]
  -- pointwise convergence of `Tⁿf`
  have : CompactSpace (Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :=
    isCompact_iff_compactSpace.1 isCompact_Icc
  have hf_uc := CompactSpace.uniformContinuous_of_continuous f.continuous
  have hpt : ∀ s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi),
      Tendsto (fun n => ∫ t, f t ∂kpow (indKernel hR Q) n s) atTop (𝓝 (∫ w, FB w ∂μ)) := by
    intro s
    have hG : ∀ n, ∫ t, G t ∂kpow (indKernel hR Q) n s = ∫ w, FB w ∂kpow Q n (indZ s) := fun n => by
      rw [← kpow_indKernel_map_indZ hR n s, integral_map continuous_indZ.measurable.aemeasurable
        FB.continuous.aestronglyMeasurable]
      rfl
    have hQlim := hconvQ (Measure.dirac (indZ s)) inferInstance FB
    simp only [iterate_dirac] at hQlim
    have hdiff : Tendsto (fun n => ∫ t, f t ∂kpow (indKernel hR Q) n s -
        ∫ t, G t ∂kpow (indKernel hR Q) n s) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1 hf_uc (ε / 2) (half_pos hε)
      have hx0 : 0 < s.1.1 := hR.a_pos.trans_le s.2.1.1
      have h1 := (hR.policy.tendsto_iterate ⟨le_rfl, hR.z_lt.le⟩ hp hflo hx0).eventually
        (lt_mem_nhds (show p - δ < p by linarith))
      have h2 := (hR.policy.tendsto_iterate ⟨hR.z_lt.le, le_rfl⟩ hp hfhi hx0).eventually
        (gt_mem_nhds (show p < p + δ by linarith))
      obtain ⟨T, hT⟩ := eventually_atTop.1 (h1.and h2)
      refine ⟨T, fun n hn => ?_⟩
      have := ex_8_4a (indKernel hR Q) n
      have hmeas : MeasurableSet {t : Icc ((a, zlo) : ℝ × ℝ) (b, zhi) |
          (fun x => g x zlo)^[n] s.1.1 ≤ t.1.1 ∧ t.1.1 ≤ (fun x => g x zhi)^[n] s.1.1} :=
        (measurableSet_le measurable_const (measurable_fst.comp measurable_subtype_coe)).inter
          (measurableSet_le (measurable_fst.comp measurable_subtype_coe) measurable_const)
      have hae : ∀ᵐ t ∂kpow (indKernel hR Q) n s, (fun x => g x zlo)^[n] s.1.1 ≤ t.1.1 ∧
          t.1.1 ≤ (fun x => g x zhi)^[n] s.1.1 :=
        mem_ae_iff.2 ((prob_compl_eq_zero_iff hmeas).2 (kpow_indKernel_squeeze hR n s))
      have hbd : ∀ᵐ t ∂kpow (indKernel hR Q) n s, ‖f t - G t‖ ≤ ε / 2 := by
        filter_upwards [hae] with t ht
        have hdist : dist t (indIncl hap hpb (indDeg (indZ t))) < δ := by
          rw [Subtype.dist_eq, Prod.dist_eq]
          change max (dist t.1.1 p) (dist t.1.2 t.1.2) < δ
          rw [dist_self, Real.dist_eq]
          refine max_lt (abs_lt.2 ⟨?_, ?_⟩) hδ
          · linarith [(hT n hn).1, ht.1]
          · linarith [(hT n hn).2, ht.2]
        have := hδf hdist
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        exact this.le
      have hint := norm_integral_le_of_norm_le_const hbd
      rw [probReal_univ, mul_one, integral_sub (f.integrable _) (G.integrable _)] at hint
      rw [dist_zero_right]
      linarith
    have := hdiff.add (hQlim.congr fun n => (hG n).symm)
    simp only [sub_add_cancel] at this
    simpa using this
  -- dominated convergence over `λ₀`
  have hrw : ∀ n, ∫ s, f s ∂(adjointOp (indKernel hR Q))^[n] lam₀ =
      ∫ s, markovOpR (kpow (indKernel hR Q) n) f s ∂lam₀ := fun n => by
    have := ex_8_4a (indKernel hR Q) n
    rw [adjointOp_iterate, integral_markovOpR]
  simp_rw [hrw]
  have hlim' := tendsto_integral_of_dominated_convergence (μ := lam₀) (fun _ => ‖f‖)
    (F := fun n s => markovOpR (kpow (indKernel hR Q) n) f s)
    (fun n => by
      have := ex_8_4a (indKernel hR Q) n
      exact (theorem_8_1_cor (kpow (indKernel hR Q) n) f.continuous.measurable
        (bcf_abs_le_norm f)).1.aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun s => by
      have := ex_8_4a (indKernel hR Q) n
      rw [Real.norm_eq_abs]
      exact (theorem_8_1_cor (kpow (indKernel hR Q) n) f.continuous.measurable
        (bcf_abs_le_norm f)).2 s)
    (Eventually.of_forall hpt)
  simpa using hlim'

/-- **Exercise 13.4c on every invariant rectangle** `[a, b] × Z ⊇ Ŝ` (`0 < a ≤ x̲`, `x̄ ≤ b`),
both cases `x̲ < x̄` (`ex_13_4c_rect`) and `x̲ = x̄` (`ex_13_4c_rect_degenerate`): `T*ⁿλ ⇒ λ*`
(extended by zero off `Ŝ`) for every probability measure `λ` on the rectangle. -/
theorem ex_13_4c_rect_all {xlo xhi : ℝ} (hS : IndustryRect g zlo zhi xlo xhi)
    (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) (hR : IndustryRect g zlo zhi a b)
    (hax : a ≤ xlo) (hxb : xhi ≤ b) [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α)
    {lamStar : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi))} [IsProbabilityMeasure lamStar]
    (hinv : adjointOp (indKernel hS Q) lamStar = lamStar)
    (lam₀ : Measure (Icc ((a, zlo) : ℝ × ℝ) (b, zhi))) [IsProbabilityMeasure lam₀] :
    ConvWeak (fun n => (adjointOp (indKernel hR Q))^[n] lam₀) (lamStar.map (indIncl hax hxb)) := by
  rcases hS.a_le_b.eq_or_lt with heq | hlt
  · subst heq
    exact ex_13_4c_rect_degenerate hS hflo hfhi hR hax hxb hM hF hQ hinv lam₀
  · exact (ex_13_4c_rect hS hflo hfhi hlt hR hax hxb hM hF hQ hinv).2 lam₀ inferInstance

/-! ### Exercise 13.4c on the full state space `S = X × Z` -/

/-- The shock coordinate of a state of `S = (0, ∞) × Z`. -/
def indSZ (p : Ioi (0 : ℝ) ×ˢ Icc zlo zhi) : Icc zlo zhi := ⟨p.1.2, p.2.2⟩

/-- The shock coordinate on `S` is continuous. -/
theorem continuous_indSZ : Continuous (indSZ (zlo := zlo) (zhi := zhi)) :=
  (continuous_snd.comp continuous_subtype_val).subtype_mk _

/-- The law of motion on `S`: `((x, z), z′) ↦ (g(x, z), z′)`. -/
def indSNext (hg : IndustryPolicy g zlo zhi) (q : (Ioi (0 : ℝ) ×ˢ Icc zlo zhi) × Icc zlo zhi) :
    Ioi (0 : ℝ) ×ˢ Icc zlo zhi :=
  ⟨(g q.1.1.1 q.1.1.2, q.2.1), hg.pos _ _ q.1.2.1 q.1.2.2, q.2.2⟩

/-- The law of motion on `S` is continuous. -/
theorem continuous_indSNext (hg : IndustryPolicy g zlo zhi) : Continuous (indSNext hg) :=
  (((hg.cont.comp_continuous continuous_subtype_val fun p => p.2).comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- **The transition function `P` on the full state space** `S = X × Z`, `X = (0, ∞)`
(p. 397): `P(s, ·)` is the law of `(g(x, z), z′)` with `z′ ∼ Q(z, ·)`. -/
noncomputable def indSKernel (hg : IndustryPolicy g zlo zhi)
    (Q : Kernel (Icc zlo zhi) (Icc zlo zhi)) :
    Kernel (Ioi (0 : ℝ) ×ˢ Icc zlo zhi) (Ioi (0 : ℝ) ×ˢ Icc zlo zhi) :=
  Kernel.map (Kernel.id ×ₖ Q.comap indSZ continuous_indSZ.measurable) (indSNext hg)

/-- `P` is a Markov kernel on `S`. -/
theorem isMarkovKernel_indSKernel (hg : IndustryPolicy g zlo zhi) [IsMarkovKernel Q] :
    IsMarkovKernel (indSKernel hg Q) :=
  Kernel.IsMarkovKernel.map _ (continuous_indSNext hg).measurable

/-- `P(s, ·) = Q(z, ·) ∘ (z′ ↦ (g(x, z), z′))⁻¹`. -/
theorem indSKernel_apply (hg : IndustryPolicy g zlo zhi) [IsMarkovKernel Q]
    (s : Ioi (0 : ℝ) ×ˢ Icc zlo zhi) :
    indSKernel hg Q s = (Q (indSZ s)).map fun w => indSNext hg (s, w) := by
  rw [indSKernel, Kernel.map_apply _ (continuous_indSNext hg).measurable, Kernel.prod_apply,
    Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (continuous_indSNext hg).measurable measurable_prodMk_left]
  rfl

/-- The inclusion of a rectangle `[a, b] × Z` (`a > 0`) into `S`. -/
def indSIncl (ha : 0 < a) (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) : Ioi (0 : ℝ) ×ˢ Icc zlo zhi :=
  ⟨s.1, ha.trans_le s.2.1.1, s.2.1.2, s.2.2.2⟩

/-- The inclusion of a rectangle into `S` is continuous. -/
theorem continuous_indSIncl (ha : 0 < a) :
    Continuous (indSIncl (zlo := zlo) (zhi := zhi) (b := b) ha) :=
  continuous_subtype_val.subtype_mk _

/-- `P` restricts to `P̂` on every invariant rectangle: `P(ι s, ·) = P_R(s, ·) ∘ ι⁻¹`. -/
theorem indSKernel_indSIncl [IsMarkovKernel Q] (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    indSKernel h.policy Q (indSIncl h.a_pos s) = (indKernel h Q s).map (indSIncl h.a_pos) := by
  rw [indSKernel_apply, indKernel_apply,
    Measure.map_map (continuous_indSIncl h.a_pos).measurable (measurable_indNext_left h s)]
  rfl

/-- `Pⁿ(ι s, ·) = P_Rⁿ(s, ·) ∘ ι⁻¹`. -/
theorem kpow_indSKernel_indSIncl [IsMarkovKernel Q] (n : ℕ)
    (s : Icc ((a, zlo) : ℝ × ℝ) (b, zhi)) :
    kpow (indSKernel h.policy Q) n (indSIncl h.a_pos s) =
      (kpow (indKernel h Q) n s).map (indSIncl h.a_pos) := by
  have hι := (continuous_indSIncl (zlo := zlo) (zhi := zhi) (b := b) h.a_pos).measurable
  have := isMarkovKernel_indKernel h (Q := Q)
  have := isMarkovKernel_indSKernel h.policy (Q := Q)
  induction n generalizing s with
  | zero =>
    change Kernel.id _ = (Kernel.id s).map _
    rw [Kernel.id_apply, Kernel.id_apply, Measure.map_dirac' hι]
  | succ n ih =>
    ext A hA
    change (kpow (indSKernel h.policy Q) n ∘ₖ indSKernel h.policy Q) _ A =
      ((kpow (indKernel h Q) n ∘ₖ indKernel h Q) s).map _ A
    rw [Measure.map_apply hι hA, Kernel.comp_apply' _ _ _ hA, Kernel.comp_apply' _ _ _ (hι hA),
      indSKernel_indSIncl h, lintegral_map (Kernel.measurable_coe _ hA) hι]
    refine lintegral_congr fun t => ?_
    rw [ih t, Measure.map_apply hι hA]

/-- **Exercise 13.4c** (p. 397). Let `λ*` be the invariant measure of `P̂` on `Ŝ = X̂ × Z`
(`ex_13_4b_stable`), extended by zero to `S = X × Z`, `X = (0, ∞)`. Then `T*ⁿλ ⇒ λ*` for every
probability measure `λ` on `S`, where `T*` is the adjoint of the transition function `P` of
`g` and `Q` on `S`. Proof: each `s ∈ S` lies in an invariant rectangle `[a, b] × Z ⊇ Ŝ`, on which
`Pⁿ(s, ·) ⇒ λ*` (`ex_13_4c_rect_all` with `λ₀ = δ_s`); then dominated convergence in `s`. -/
theorem ex_13_4c {xlo xhi : ℝ} (hS : IndustryRect g zlo zhi xlo xhi) (hflo : g xlo zlo = xlo)
    (hfhi : g xhi zhi = xhi) [IsMarkovKernel Q] (hM : IsMonotoneTF Q) (hF : IsFeller Q)
    (hQ : IndustryMixing Q N α)
    {lamStar : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi))} [IsProbabilityMeasure lamStar]
    (hinv : adjointOp (indKernel hS Q) lamStar = lamStar)
    (lam₀ : Measure (Ioi (0 : ℝ) ×ˢ Icc zlo zhi)) [IsProbabilityMeasure lam₀] :
    ConvWeak (fun n => (adjointOp (indSKernel hS.policy Q))^[n] lam₀)
      (lamStar.map (indSIncl hS.a_pos)) := by
  have := isMarkovKernel_indSKernel hS.policy (Q := Q)
  intro f
  have hpt : ∀ s : Ioi (0 : ℝ) ×ˢ Icc zlo zhi,
      Tendsto (fun n => markovOpR (kpow (indSKernel hS.policy Q) n) f s) atTop
        (𝓝 (∫ t, f t ∂lamStar.map (indSIncl hS.a_pos))) := by
    intro s
    have hR := industryRect_of_fixed (a := min s.1.1 xlo) (b := max s.1.1 xhi) hS.policy hS.z_lt
      hS.a_pos hS.a_le_b hflo hfhi (lt_min s.2.1 hS.a_pos) (min_le_right _ _) (le_max_right _ _)
    have := isMarkovKernel_indKernel hR (Q := Q)
    set s' : Icc ((min s.1.1 xlo, zlo) : ℝ × ℝ) (max s.1.1 xhi, zhi) :=
      ⟨s.1, ⟨min_le_left _ _, s.2.2.1⟩, ⟨le_max_left _ _, s.2.2.2⟩⟩
    have hι := (continuous_indSIncl (zlo := zlo) (zhi := zhi) (b := max s.1.1 xhi)
      hR.a_pos).measurable
    set F : Icc ((min s.1.1 xlo, zlo) : ℝ × ℝ) (max s.1.1 xhi, zhi) →ᵇ ℝ :=
      f.compContinuous ⟨indSIncl hR.a_pos, continuous_indSIncl hR.a_pos⟩
    have hconv := ex_13_4c_rect_all hS hflo hfhi hR (min_le_right _ _) (le_max_right _ _) hM hF
      hQ hinv (Measure.dirac s') F
    simp only [iterate_dirac] at hconv
    have hlhs : ∀ n, markovOpR (kpow (indSKernel hS.policy Q) n) f s =
        ∫ t, F t ∂kpow (indKernel hR Q) n s' := fun n => by
      change ∫ z', f z' ∂kpow (indSKernel hS.policy Q) n (indSIncl hR.a_pos s') = _
      rw [kpow_indSKernel_indSIncl hR n s',
        integral_map hι.aemeasurable f.continuous.aestronglyMeasurable]
      rfl
    have hrhs : ∫ t, F t ∂lamStar.map (indIncl (min_le_right s.1.1 xlo) (le_max_right s.1.1 xhi))
        = ∫ t, f t ∂lamStar.map (indSIncl hS.a_pos) := by
      have hι' := (continuous_indIncl (zlo := zlo) (zhi := zhi) (min_le_right s.1.1 xlo)
        (le_max_right s.1.1 xhi)).measurable
      rw [integral_map hι'.aemeasurable F.continuous.aestronglyMeasurable,
        integral_map (continuous_indSIncl hS.a_pos).measurable.aemeasurable
          f.continuous.aestronglyMeasurable]
      rfl
    rw [← hrhs]
    exact hconv.congr fun n => (hlhs n).symm
  have hrw : ∀ n, ∫ s, f s ∂(adjointOp (indSKernel hS.policy Q))^[n] lam₀ =
      ∫ s, markovOpR (kpow (indSKernel hS.policy Q) n) f s ∂lam₀ := fun n => by
    have := ex_8_4a (indSKernel hS.policy Q) n
    rw [adjointOp_iterate, integral_markovOpR]
  simp_rw [hrw]
  have hlim' := tendsto_integral_of_dominated_convergence (μ := lam₀) (fun _ => ‖f‖)
    (F := fun n s => markovOpR (kpow (indSKernel hS.policy Q) n) f s)
    (fun n => by
      have := ex_8_4a (indSKernel hS.policy Q) n
      exact (theorem_8_1_cor (kpow (indSKernel hS.policy Q) n) f.continuous.measurable
        (bcf_abs_le_norm f)).1.aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun s => by
      have := ex_8_4a (indSKernel hS.policy Q) n
      rw [Real.norm_eq_abs]
      exact (theorem_8_1_cor (kpow (indSKernel hS.policy Q) n) f.continuous.measurable
        (bcf_abs_le_norm f)).2 s)
    (Eventually.of_forall hpt)
  simpa using hlim'

/-- **Exercise 13.4c**, invariant measure on `S`: `λ*` extended by zero is the unique invariant
probability measure of `P` on `S = X × Z` (invariance by `indSKernel_indSIncl`, uniqueness from
the global convergence of `ex_13_4c`). -/
theorem ex_13_4c_unique {xlo xhi : ℝ} (hS : IndustryRect g zlo zhi xlo xhi)
    (hflo : g xlo zlo = xlo) (hfhi : g xhi zhi = xhi) [IsMarkovKernel Q] (hM : IsMonotoneTF Q)
    (hF : IsFeller Q) (hQ : IndustryMixing Q N α)
    {lamStar : Measure (Icc ((xlo, zlo) : ℝ × ℝ) (xhi, zhi))} [IsProbabilityMeasure lamStar]
    (hinv : adjointOp (indKernel hS Q) lamStar = lamStar) :
    adjointOp (indSKernel hS.policy Q) (lamStar.map (indSIncl hS.a_pos)) =
        lamStar.map (indSIncl hS.a_pos) ∧
      ∀ ν : Measure (Ioi (0 : ℝ) ×ˢ Icc zlo zhi), IsProbabilityMeasure ν →
        adjointOp (indSKernel hS.policy Q) ν = ν → ν = lamStar.map (indSIncl hS.a_pos) := by
  have := isMarkovKernel_indSKernel hS.policy (Q := Q)
  have hι := (continuous_indSIncl (zlo := zlo) (zhi := zhi) (b := xhi) hS.a_pos).measurable
  refine ⟨?_, fun ν hν hνinv => ?_⟩
  · conv_rhs => rw [← hinv]
    ext A hA
    rw [adjointOp_apply _ _ hA, Measure.map_apply hι hA, adjointOp_apply _ _ (hι hA),
      lintegral_map (Kernel.measurable_coe _ hA) hι]
    refine lintegral_congr fun s => ?_
    rw [indSKernel_indSIncl hS, Measure.map_apply hι hA]
  · have hconst : ConvWeak (fun n => (adjointOp (indSKernel hS.policy Q))^[n] ν) ν := fun f => by
      simp only [Function.iterate_fixed hνinv]; exact tendsto_const_nhds
    exact convWeak_unique hconst (ex_13_4c hS hflo hfhi hM hF hQ hinv ν)

end StokeyLucasPrescott.ConvergenceApplications
