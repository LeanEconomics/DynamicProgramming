/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# §17.3.1: recursive competitive equilibrium with aggregate shocks (Definition 17.3.1)

Miao, §17.3.1, pp. 579–581. The Aiyagari economy with aggregate productivity `z`:
`Y = zF(K, L)`, the joint process `(z_t, l_t)` is Markov with transition `Q(·, ·; z, l)` (a kernel
on `Z × L`), the individual state is `(a, l)` and the aggregate state is `(λ, z)`, `λ` a measure
on `ℝ × L`.

* `BWAggEconomy`: the primitives, with `F_K`, `F_L` the partial derivatives of `F`, and the
  marginal transition `π(z′ | z) = Q({z′} × L; z, l)` of the aggregate shock, which is required not
  to depend on `l` (the aggregate shock is an exogenous Markov chain).
* `BWAggEconomy.Bellman`: condition (i), the household's Bellman equation with `λ′ = G(λ, z; z′)`.
* `BWRecEqm`: **Definition 17.3.1**, (i) the Bellman equation, (ii) the firm's first-order
  conditions `zF_K(K, L) = r + δ`, `zF_L(K, L) = w`, (iii) market clearing `K = ∫ a dλ`,
  `L = ∫ l dλ` (built into `bw_aggK`, `bw_aggL`), (iv) the law of motion
  `π(z′|z) G(λ, z; z′)(A × B) = ∫ 1_A(g(a, l; λ, z)) Q(z′, B; z, l) dλ` (corrected, see below).
* `bw_book_law_mass`, `bw_book_law_not_prob`: **the book's (iv) as printed**,
  `G(λ, z; z′)(A × B) = ∫ 1_A(g) Q(z′, B; z, l) dλ`, gives `G(λ, z; z′)` total mass
  `π(z′|z)`; so `G`
  is not a probability measure whenever `π(z′|z) < 1`. The corrected law divides by `π(z′|z)`
  (`bw_law_isProb`: then `G(λ, z; z′)` has mass one).
* `bw_law_indep`: with independent shocks, `Q(z′, B; z, l) = π(z′|z)Q_l(B, l)`, the law of motion
  does not depend on `z′` (Miao, p. 580).
* `bw_next_capital_indep`: tomorrow's capital `K′ = ∫ a dG(λ, z; z′)` never depends on `z′`
  ("capital is predetermined", p. 582), with or without independence.
* `bw_sequential_of_recursive`: a recursive equilibrium induces a sequential competitive
  equilibrium (p. 580): prices `w_t = z_tF_L(K_t, L_t)`, `r_t = z_tF_K(K_t, L_t) − δ`,
  `λ_{t+1} = G(λ_t, z_t; z_{t+1})`, and feasible individual
  choices `a_{t+1} = g(a_t, l_t; λ_t, z_t)`.
* `bw_recEqm_example`: a concrete recursive equilibrium (linear technology, linear utility,
  `β(1 + r) = 1`), so Definition 17.3.1 is not vacuous.

The existence of a recursive equilibrium in general is "an open question" (p. 581); Miao (2006)
and Kubler–Schmedders (2002) are cited, not formalised.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **Aiyagari economy with aggregate shocks** (Miao, §17.3.1, p. 579). -/
structure BWAggEconomy (Z L : Type*) [MeasurableSpace Z] [MeasurableSpace L] where
  β : ℝ
  u : ℝ → ℝ
  F : ℝ → ℝ → ℝ
  FK : ℝ → ℝ → ℝ
  FL : ℝ → ℝ → ℝ
  δ : ℝ
  zval : Z → ℝ
  lab : L → ℝ
  Q : Kernel (Z × L) (Z × L)
  πz : Z → Z → ℝ≥0∞
  hasDerivAt_K : ∀ K Lb, HasDerivAt (fun k => F k Lb) (FK K Lb) K
  hasDerivAt_L : ∀ K Lb, HasDerivAt (fun l => F K l) (FL K Lb) Lb
  marg : ∀ z l z', Q (z, l) ({z'} ×ˢ Set.univ) = πz z z'

variable {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L]

/-- Aggregate capital `K = ∫ a dλ` (Definition 17.3.1 (iii)). -/
noncomputable def bw_aggK (lam : Measure (ℝ × L)) : ℝ := ∫ p, p.1 ∂lam

/-- Aggregate labour `L = ∫ l dλ` (Definition 17.3.1 (iii)). -/
noncomputable def bw_aggL (lab : L → ℝ) (lam : Measure (ℝ × L)) : ℝ := ∫ p, lab p.2 ∂lam

namespace BWAggEconomy

/-- Definition 17.3.1 (i) (Miao, pp. 579–580): given `G`, `r`, `w`, the functions `g` and `V`
solve `V(a, l; λ, z) = max_{a′} u(c) + β ∫ V(a′, l′; λ′, z′) Q(dz′, dl′; z, l)` subject to
`c + a′ = (1 + r(λ, z))a + w(λ, z)l`, `a′ ≥ 0`, `c ≥ 0`, `λ′ = G(λ, z; z′)`. -/
def Bellman (A : BWAggEconomy Z L) (V g : ℝ → L → Measure (ℝ × L) → Z → ℝ)
    (G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)) (r w : Measure (ℝ × L) → Z → ℝ) : Prop :=
  ∀ a l lam z, 0 ≤ a →
    g a l lam z ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l) ∧
    (∀ a', 0 ≤ a' → Integrable (fun p : Z × L => V a' p.2 (G lam z p.1) p.1) (A.Q (z, l))) ∧
    V a l lam z = A.u ((1 + r lam z) * a + w lam z * A.lab l - g a l lam z) +
      A.β * ∫ p, V (g a l lam z) p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ∧
    ∀ a' ∈ Set.Icc 0 ((1 + r lam z) * a + w lam z * A.lab l),
      A.u ((1 + r lam z) * a + w lam z * A.lab l - a') +
        A.β * ∫ p, V a' p.2 (G lam z p.1) p.1 ∂(A.Q (z, l)) ≤ V a l lam z

/-- Definition 17.3.1 (iv) **as printed** (Miao, p. 580):
`G(λ, z; z′)(A × B) = ∫ 1_A(g(a, l; λ, z)) Q(z′, B; z, l) λ(da, dl)`. -/
def BookLaw (A : BWAggEconomy Z L) (g : ℝ → L → Measure (ℝ × L) → Z → ℝ)
    (G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)) : Prop :=
  ∀ lam z z' (S : Set ℝ) (B : Set L), MeasurableSet S → MeasurableSet B →
    G lam z z' (S ×ˢ B) =
      ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * A.Q (z, p.2) ({z'} ×ˢ B) ∂lam

/-- Definition 17.3.1 (iv), corrected: the distribution tomorrow conditional on `z′`,
`π(z′|z) G(λ, z; z′)(A × B) = ∫ 1_A(g(a, l; λ, z)) Q(z′, B; z, l) λ(da, dl)`. -/
def Law (A : BWAggEconomy Z L) (g : ℝ → L → Measure (ℝ × L) → Z → ℝ)
    (G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)) : Prop :=
  ∀ lam z z' (S : Set ℝ) (B : Set L), MeasurableSet S → MeasurableSet B →
    G lam z z' (S ×ˢ B) * A.πz z z' =
      ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * A.Q (z, p.2) ({z'} ×ˢ B) ∂lam

end BWAggEconomy

/-- **Definition 17.3.1** (Miao, pp. 579–580). A **recursive competitive equilibrium** with
aggregate shocks: a value function `V(a, l; λ, z)`, a policy `g(a, l; λ, z)`, a law of motion
`G(λ, z; z′)` and pricing functions `r(λ, z)`, `w(λ, z)` such that (i) `g`, `V` solve the Bellman
equation, (ii) firms maximise profits, `zF_K(K, L) = r(λ, z) + δ`, `zF_L(K, L) = w(λ, z)`,
(iii) markets clear, `K = ∫ a dλ`, `L = ∫ l dλ`, and (iv) `G` is generated by `g` (corrected
form `BWAggEconomy.Law`). -/
structure BWRecEqm (A : BWAggEconomy Z L) where
  V : ℝ → L → Measure (ℝ × L) → Z → ℝ
  g : ℝ → L → Measure (ℝ × L) → Z → ℝ
  G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)
  r : Measure (ℝ × L) → Z → ℝ
  w : Measure (ℝ × L) → Z → ℝ
  bellman : A.Bellman V g G r w
  firmK : ∀ lam z, A.zval z * A.FK (bw_aggK lam) (bw_aggL A.lab lam) = r lam z + A.δ
  firmL : ∀ lam z, A.zval z * A.FL (bw_aggK lam) (bw_aggL A.lab lam) = w lam z
  law : A.Law g G

/-- **Correction to Definition 17.3.1 (iv).** Under the book's law of motion as printed, for a
probability measure `λ`, `G(λ, z; z′)` has total mass `π(z′|z)`. -/
theorem bw_book_law_mass {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.BookLaw g G)
    (lam : Measure (ℝ × L)) [IsProbabilityMeasure lam] (z z' : Z) :
    G lam z z' Set.univ = A.πz z z' := by
  have h := hG lam z z' Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rw [Set.univ_prod_univ] at h
  rw [h]
  simp [A.marg]

/-- **Counterexample to Definition 17.3.1 (iv) as printed.** Whenever the aggregate shock moves
to `z′` with probability `π(z′|z) < 1`, the book's `G(λ, z; z′)` is not a probability measure. -/
theorem bw_book_law_not_prob {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.BookLaw g G)
    (lam : Measure (ℝ × L)) [IsProbabilityMeasure lam] {z z' : Z} (hz : A.πz z z' < 1) :
    ¬ IsProbabilityMeasure (G lam z z') := by
  intro hP
  have := bw_book_law_mass hG lam z z'
  rw [measure_univ] at this
  rw [← this] at hz
  exact lt_irrefl _ hz

/-- With the corrected law (iv), `G(λ, z; z′)` is a probability measure whenever
`0 < π(z′|z) < ∞` and `λ` is. -/
theorem bw_law_isProb {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G)
    (lam : Measure (ℝ × L)) [IsProbabilityMeasure lam] {z z' : Z} (h0 : A.πz z z' ≠ 0)
    (htop : A.πz z z' ≠ ∞) : G lam z z' Set.univ = 1 := by
  have h := hG lam z z' Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rw [Set.univ_prod_univ] at h
  simp only [Set.indicator_univ, Pi.one_apply, one_mul, A.marg, lintegral_const,
    measure_univ, mul_one] at h
  have := (ENNReal.mul_left_inj h0 htop).1 (h.trans (one_mul _).symm)
  exact this

/-- The corrected law (iv) with `0 < π(z′|z) < ∞` gives the a-marginal of tomorrow's distribution,
`G(λ, z; z′)(A × L) = ∫ 1_A(g) dλ`, which does not involve `z′`. -/
theorem bw_law_marginal {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G)
    (lam : Measure (ℝ × L)) {z z' : Z} (h0 : A.πz z z' ≠ 0) (htop : A.πz z z' ≠ ∞) {S : Set ℝ}
    (hS : MeasurableSet S) :
    G lam z z' (S ×ˢ Set.univ) = ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) ∂lam := by
  have h := hG lam z z' S Set.univ hS MeasurableSet.univ
  simp only [A.marg] at h
  rw [lintegral_mul_const' _ _ htop] at h
  exact (ENNReal.mul_left_inj h0 htop).1 h

/-- Miao, p. 582: **capital is predetermined**. Tomorrow's aggregate capital
`K′ = ∫ a dG(λ, z; z′)` is the same for all `z′` with `0 < π(z′|z) < ∞`, so the law of motion of
`K` does not depend on `z′`. -/
theorem bw_next_capital_indep {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G)
    (lam : Measure (ℝ × L)) {z z₁ z₂ : Z} (h1 : A.πz z z₁ ≠ 0) (h1' : A.πz z z₁ ≠ ∞)
    (h2 : A.πz z z₂ ≠ 0) (h2' : A.πz z z₂ ≠ ∞) :
    (G lam z z₁).map Prod.fst = (G lam z z₂).map Prod.fst ∧
      bw_aggK (G lam z z₁) = bw_aggK (G lam z z₂) := by
  have hmap : (G lam z z₁).map Prod.fst = (G lam z z₂).map Prod.fst := by
    ext S hS
    rw [Measure.map_apply measurable_fst hS, Measure.map_apply measurable_fst hS,
      ← Set.prod_univ, bw_law_marginal hG lam h1 h1' hS, bw_law_marginal hG lam h2 h2' hS]
  refine ⟨hmap, ?_⟩
  have e : ∀ m : Measure (ℝ × L), bw_aggK m = ∫ x, x ∂(m.map Prod.fst) := fun m =>
    (integral_map (f := fun x : ℝ => x) measurable_fst.aemeasurable
      aestronglyMeasurable_id).symm
  rw [e, e, hmap]

/-- Miao, p. 580: if the aggregate and the idiosyncratic shocks are independent,
`Q(z′, B; z, l) = π(z′|z) Q_l(B, l)`, then the law of motion does not depend on `z′`:
`G(λ, z; z′)(A × B) = ∫ 1_A(g) Q_l(B, l) dλ` for every `z′` with `0 < π(z′|z) < ∞`. -/
theorem bw_law_indep {A : BWAggEconomy Z L} {g : ℝ → L → Measure (ℝ × L) → Z → ℝ}
    {G : Measure (ℝ × L) → Z → Z → Measure (ℝ × L)} (hG : A.Law g G) (Ql : Kernel L L)
    (hind : ∀ z l z' B, A.Q (z, l) ({z'} ×ˢ B) = A.πz z z' * Ql l B)
    (lam : Measure (ℝ × L)) {z z' : Z} (h0 : A.πz z z' ≠ 0) (htop : A.πz z z' ≠ ∞) {S : Set ℝ}
    {B : Set L} (hS : MeasurableSet S) (hB : MeasurableSet B) :
    G lam z z' (S ×ˢ B) = ∫⁻ p, S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * Ql p.2 B ∂lam := by
  have h := hG lam z z' S B hS hB
  simp only [hind] at h
  have : (fun p : ℝ × L => S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * (A.πz z z' * Ql p.2 B))
      = fun p => (S.indicator (1 : ℝ → ℝ≥0∞) (g p.1 p.2 lam z) * Ql p.2 B) * A.πz z z' := by
    funext p; ring
  rw [this, lintegral_mul_const' _ _ htop] at h
  exact (ENNReal.mul_left_inj h0 htop).1 h

/-- The path of distributions `λ_{t+1} = G(λ_t, z_t; z_{t+1})` generated by a recursive equilibrium
along the aggregate shock path `z`. -/
noncomputable def bw_distPath {A : BWAggEconomy Z L} (E : BWRecEqm A) (zs : ℕ → Z)
    (lam₀ : Measure (ℝ × L)) : ℕ → Measure (ℝ × L)
  | 0 => lam₀
  | t + 1 => E.G (bw_distPath E zs lam₀ t) (zs t) (zs (t + 1))

/-- An individual's asset path `a_{t+1} = g(a_t, l_t; λ_t, z_t)`. -/
noncomputable def bw_assetPath {A : BWAggEconomy Z L} (E : BWRecEqm A) (zs : ℕ → Z) (ls : ℕ → L)
    (lam₀ : Measure (ℝ × L)) (a₀ : ℝ) : ℕ → ℝ
  | 0 => a₀
  | t + 1 => E.g (bw_assetPath E zs ls lam₀ a₀ t) (ls t) (bw_distPath E zs lam₀ t) (zs t)

/-- Miao, pp. 580–581: **a recursive equilibrium induces a sequential competitive equilibrium**.
Along any shock path, with `λ_t` the distribution path and `K_t = ∫ a dλ_t`, `L_t = ∫ l dλ_t`:
`w_t = z_tF_L(K_t, L_t)`, `r_t = z_tF_K(K_t, L_t) − δ`, `λ_{t+1} = G(λ_t, z_t; z_{t+1})`; and an
individual starting from `a₀ ≥ 0` has `a_t ≥ 0`, nonnegative consumption
`c_t = (1 + r_t)a_t + w_tl_t − a_{t+1} ≥ 0`, and `a_{t+1} = g(a_t, l_t; λ_t, z_t)` attains the
Bellman equation at each date. -/
theorem bw_sequential_of_recursive {A : BWAggEconomy Z L} (E : BWRecEqm A) (zs : ℕ → Z)
    (ls : ℕ → L) (lam₀ : Measure (ℝ × L)) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (t : ℕ) :
    let lam := bw_distPath E zs lam₀
    let a := bw_assetPath E zs ls lam₀ a₀
    E.w (lam t) (zs t) = A.zval (zs t) * A.FL (bw_aggK (lam t)) (bw_aggL A.lab (lam t)) ∧
    E.r (lam t) (zs t) = A.zval (zs t) * A.FK (bw_aggK (lam t)) (bw_aggL A.lab (lam t)) - A.δ ∧
    lam (t + 1) = E.G (lam t) (zs t) (zs (t + 1)) ∧
    0 ≤ a t ∧ a (t + 1) = E.g (a t) (ls t) (lam t) (zs t) ∧
    0 ≤ (1 + E.r (lam t) (zs t)) * a t + E.w (lam t) (zs t) * A.lab (ls t) - a (t + 1) ∧
    E.V (a t) (ls t) (lam t) (zs t) =
      A.u ((1 + E.r (lam t) (zs t)) * a t + E.w (lam t) (zs t) * A.lab (ls t) - a (t + 1)) +
        A.β * ∫ p, E.V (a (t + 1)) p.2 (E.G (lam t) (zs t) p.1) p.1 ∂(A.Q (zs t, ls t)) := by
  intro lam a
  have hnn : ∀ s, 0 ≤ a s := by
    intro s
    induction s with
    | zero => exact ha₀
    | succ s ih => exact ((E.bellman _ (ls s) (lam s) (zs s) ih).1).1
  have hB := E.bellman (a t) (ls t) (lam t) (zs t) (hnn t)
  refine ⟨(E.firmL _ _).symm, by linarith [E.firmK (lam t) (zs t)], rfl, hnn t, rfl, ?_, hB.2.2.1⟩
  have := hB.1.2
  change 0 ≤ (1 + E.r (lam t) (zs t)) * a t + E.w (lam t) (zs t) * A.lab (ls t) -
    E.g (a t) (ls t) (lam t) (zs t)
  linarith

/-- The concrete economy of `bw_recEqm_example`: one aggregate and one idiosyncratic state,
`β = 1/2`, `u(c) = c`, `F(K, L) = (3/2)K + L`, `δ = 1/2`. -/
noncomputable def bw_aggExample : BWAggEconomy Unit Unit where
  β := 1 / 2
  u := fun c => c
  F := fun K Lb => 3 / 2 * K + Lb
  FK := fun _ _ => 3 / 2
  FL := fun _ _ => 1
  δ := 1 / 2
  zval := fun _ => 1
  lab := fun _ => 1
  Q := Kernel.const _ (Measure.dirac ((), ()))
  πz := fun _ _ => 1
  hasDerivAt_K := fun K Lb => by
    have := (HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_id K)).add_const Lb
    simpa using this
  hasDerivAt_L := fun K Lb => by
    have := HasDerivAt.const_add (3 / 2 * K) (hasDerivAt_id Lb)
    simpa using this
  marg := fun z l z' => by simp [Kernel.const_apply]

theorem bw_aggExample_Q (x : Unit × Unit) : bw_aggExample.Q x = Measure.dirac ((), ()) := by
  simp [bw_aggExample, Kernel.const_apply]

/-- **Definition 17.3.1 is not vacuous**: in `bw_aggExample`, `V(a) = 2a + 2`, `g(a) = a`,
`G(λ, z; z′) = λ`, `r = 1`, `w = 1` is a recursive competitive equilibrium (`β(1 + r) = 1`). -/
noncomputable def bw_recEqm_example : BWRecEqm bw_aggExample where
  V := fun a _ _ _ => 2 * a + 2
  g := fun a _ _ _ => a
  G := fun lam _ _ => lam
  r := fun _ _ => 1
  w := fun _ _ => 1
  bellman := by
    intro a l lam z ha
    simp only [bw_aggExample_Q, integral_dirac]
    refine ⟨⟨ha, ?_⟩, fun a' _ => Integrable.of_finite, ?_, fun a' _ => ?_⟩
    · simp only [bw_aggExample]; linarith
    · simp only [bw_aggExample]; ring
    · simp only [bw_aggExample]; linarith
  firmK := fun _ _ => by simp only [bw_aggExample]; norm_num
  firmL := fun _ _ => by simp only [bw_aggExample]; norm_num
  law := by
    intro lam z z' S B hS hB
    simp only [bw_aggExample_Q]
    simp only [bw_aggExample, mul_one]
    have key : ∀ p : ℝ × Unit, S.indicator (1 : ℝ → ℝ≥0∞) p.1 *
        Measure.dirac ((), ()) ({()} ×ˢ B) = (S ×ˢ B).indicator 1 p := by
      rintro ⟨x, ⟨⟩⟩
      by_cases hx : x ∈ S <;> by_cases hb : () ∈ B <;>
        simp [Set.indicator, Measure.dirac_apply, Set.mem_prod, hx, hb]
    rw [lintegral_congr key, lintegral_indicator_one (hS.prod hB)]

end Miao.IncompleteMarkets
