/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import IncompleteMarkets.CDBudget

/-!
# §17.1.1: the income fluctuation problem of the Aiyagari model

Miao, §17.1.1, pp. 560–562. An agent with asset holdings `a_t ≥ −b` and labour endowment shock
`l_t ∈ [l_min, l_max]` (a Markov process with transition function `Q`) takes the interest rate
`r` and the wage `w` as given and maximises `E Σ βᵗ u(c_t)` subject to
`c_t + a_{t+1} = (1 + r)a_t + wl_t` (17.1)–(17.2).

* `ay_Budget`, `eq_17_2`: the budget (17.2) is the budget (8.3) of §8.3 with gross return
  `1 + r` and income `wl_t`.
* `ay_natural_limit`: Theorem 8.3.1 (in its corrected converse form, `theorem_8_3_1_converse`)
  gives the natural borrowing constraint `a_t ≥ −wl_min/r` for `r > 0`.
* `ay_phi`, `eq_17_3b`, `eq_17_3a`: the borrowing limit `φ` of (17.3b) and the constraint
  `a_t ≥ −φ` of (17.3a), which is at least as tight as both `−b` and the natural limit.
* `ay_cash_on_hand`: cash on hand `x_t = (1 + r)a_t + wl_t + φ`, `â_t = a_t + φ`:
  `c_t + â_{t+1} = x_t`, `x_{t+1} = (1 + r)â_{t+1} + wl_{t+1} − rφ`, `â_{t+1} ∈ [0, x_t]`.
* `ay_BellmanCoh` (the Bellman equation in cash on hand, p. 561), `ay_Bellman` (17.4) and
  `eq_17_4`: a solution in cash on hand gives a solution of (17.4) with
  `g(a, l) = A(x, l) − φ`.
* `ay_P`, `ay_P_apply`: the transition function `P(A × B, (a, l)) = 1_{g(a,l) ∈ A} Q(B, l)`
  of the joint process `(a_t, l_t)` (p. 562), a Markov kernel; `ay_lamSeq`, `ay_lamSeq_succ`:
  the sequence of distributions `λ_{t+1}(A × B) = ∫ P(A × B, (a, l)) dλ_t`.
* `ay_Stationary` and `eq_17_7`: the stationarity condition (17.7) on rectangles is equivalent
  to `λ* = λ*P` (`T*λ* = λ*`).
* `ay_stationary_fst`, `ay_stationary_snd`, `ay_stationary_snd_iid`, `ay_Ea`, `ay_Ea_eq_mean`:
  under (17.7) the asset marginal of `λ*` is the image of `λ*` under `g`, so the long-run average
  assets `Ea = ∫ g dλ*` equal the mean of current assets; the labour marginal is `Q`-invariant
  (and equals the iid law when `Q` does not depend on `l`).

**Departures.** (1) (17.3b) defines `φ` for `r > 0` and `r < 0` only; `ay_phi` sets `φ = b`
for `r = 0` as well. (2) The book's Theorem 8.3.1 needs a support hypothesis (the income process
can stay low with positive probability), as corrected in the Chapter 8 project; `ay_natural_limit`
carries it. (3) `eq_17_4` needs `1 + r ≥ 0` so that `a ≥ −φ` implies `x ≥ wl − rφ`.
(4) The joint state is `(a, l) ∈ ℝ × ℝ` with the policy `g` a function of the pair.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Miao, (17.2), p. 560: the budget constraint `c_t + a_{t+1} = (1 + r)a_t + wl_t`. -/
def ay_Budget (r w : ℝ) (l c a : ℕ → ℝ) : Prop :=
  ∀ t, c t + a (t + 1) = (1 + r) * a t + w * l t

/-- Miao, (17.2), p. 560: the budget (17.2) is the budget (8.3) of §8.3 with gross return
`R = 1 + r` and income `y_t = wl_t`. -/
theorem eq_17_2 (r w : ℝ) (l c a : ℕ → ℝ) :
    ay_Budget r w l c a ↔ cd_Budget (1 + r) (fun t => w * l t) c a := Iff.rfl

/-- Miao, p. 560, the natural borrowing constraint: by Theorem 8.3.1, for `r > 0` the
no-Ponzi-scheme condition `lim a_t/(1 + r)ᵗ ≥ 0` and nonnegative consumption imply
`a_t ≥ −wl_min/r` almost surely. The support hypothesis `hsupp` (the corrected hypothesis of
`theorem_8_3_1_converse`): the labour shock can stay near `l_min` for any number of periods after
any event of positive probability. -/
theorem ay_natural_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r w lmin lmax : ℝ}
    (hr : 0 < r) (hw : 0 ≤ w) (hlmin : 0 ≤ lmin) {l c a : ℕ → Ω → ℝ}
    (hl : ∀ t ω, lmin ≤ l t ω ∧ l t ω ≤ lmax) (hc : ∀ t ω, 0 ≤ c t ω)
    (hbud : ∀ ω, ay_Budget r w (fun t => l t ω) (fun t => c t ω) (fun t => a t ω))
    (hNP : ∀ᵐ ω ∂μ, cd_NoPonzi (1 + r) (fun t => a t ω))
    (hsupp : ∀ t (ε δ : ℝ) (N : ℕ), 0 < ε → 0 < δ →
      0 < μ {ω | a t ω < -(w * lmin) / r - ε} →
      0 < μ ({ω | a t ω < -(w * lmin) / r - ε} ∩
        {ω | ∀ k < N, w * l (t + k) ω ≤ w * lmin + δ})) :
    ∀ t, ∀ᵐ ω ∂μ, -(w * lmin) / r ≤ a t ω := by
  have hr' : (1 + r) - 1 = r := by ring
  have h := theorem_8_3_1_converse μ (R := 1 + r) (ymin := w * lmin) (ymax := w * lmax)
    (y := fun t ω => w * l t ω) (c := c) (a := a) (by linarith) (mul_nonneg hw hlmin)
    (fun t ω => ⟨mul_le_mul_of_nonneg_left (hl t ω).1 hw,
      mul_le_mul_of_nonneg_left (hl t ω).2 hw⟩) hc hbud hNP
    (fun t ε δ N hε hδ hpos => by rw [hr'] at hpos ⊢; exact hsupp t ε δ N hε hδ hpos)
  rw [hr'] at h
  exact h

/-- Miao, (17.3b), p. 560: the borrowing limit `φ = min{b, wl_min/r}` for `r > 0` and `φ = b`
for `r < 0` (and, as a convention not in the book, for `r = 0`). -/
noncomputable def ay_phi (b w lmin r : ℝ) : ℝ := if 0 < r then min b (w * lmin / r) else b

/-- Miao, (17.3b), p. 560: `φ ≤ b`; for `r > 0`, `φ = min{b, wl_min/r} ≤ wl_min/r`; for
`r < 0`, `φ = b`. -/
theorem eq_17_3b (b w lmin r : ℝ) :
    ay_phi b w lmin r ≤ b ∧
      (0 < r → ay_phi b w lmin r = min b (w * lmin / r) ∧ ay_phi b w lmin r ≤ w * lmin / r) ∧
      (r < 0 → ay_phi b w lmin r = b) := by
  refine ⟨?_, fun hr => ?_, fun hr => ?_⟩
  · unfold ay_phi
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  · have h : ay_phi b w lmin r = min b (w * lmin / r) := by
      unfold ay_phi; simp only [hr, ↓reduceIte]
    exact ⟨h, h ▸ min_le_right _ _⟩
  · unfold ay_phi; simp only [not_lt.2 hr.le, ↓reduceIte]

/-- Miao, (17.3a), p. 560: the constraint `a ≥ −φ` implies `a ≥ −b` and, for `r > 0`, the
natural borrowing constraint `a ≥ −wl_min/r`, so it may be imposed in their place. -/
theorem eq_17_3a {b w lmin r a : ℝ} (ha : -ay_phi b w lmin r ≤ a) :
    -b ≤ a ∧ (0 < r → -(w * lmin) / r ≤ a) := by
  obtain ⟨h1, h2, -⟩ := eq_17_3b b w lmin r
  refine ⟨by linarith, fun hr => ?_⟩
  have := (h2 hr).2
  rw [neg_div]
  linarith

/-- Miao, p. 561: with cash on hand `x = (1 + r)a + wl + φ` and `â′ = a′ + φ`, the budget
`c + a′ = (1 + r)a + wl` becomes `c + â′ = x`; next period's cash on hand is
`x′ = (1 + r)â′ + wl′ − rφ`; the constraints `a′ ≥ −φ`, `c ≥ 0` become `â′ ∈ [0, x]`. -/
theorem ay_cash_on_hand {r w φ a a' l l' c : ℝ} (hbud : c + a' = (1 + r) * a + w * l) :
    c + (a' + φ) = (1 + r) * a + w * l + φ ∧
      (1 + r) * a' + w * l' + φ = (1 + r) * (a' + φ) + w * l' - r * φ ∧
      (-φ ≤ a' ↔ 0 ≤ a' + φ) ∧ (0 ≤ c ↔ a' + φ ≤ (1 + r) * a + w * l + φ) := by
  refine ⟨by linarith, by ring, ⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-- Miao, p. 561: the **Bellman equation in cash on hand**
`V(x, l) = max_{â′ ∈ [0, x]} u(x − â′) + β ∫ V((1 + r)â′ + wl′ − rφ, l′) Q(dl′, l)`, attained at
the policy `â′ = A(x, l)`, on the states `x ≥ wl − rφ` (from `a ≥ −φ`), `l ∈ [l_min, l_max]`. -/
def ay_BellmanCoh (u : ℝ → ℝ) (β r w φ lmin lmax : ℝ) (Q : Kernel ℝ ℝ)
    (W A : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, w * p.2 - r * φ ≤ p.1 → p.2 ∈ Set.Icc lmin lmax →
    A p ∈ Set.Icc 0 p.1 ∧
    W p = u (p.1 - A p) + β * ∫ l', W ((1 + r) * A p + w * l' - r * φ, l') ∂Q p.2 ∧
    ∀ s ∈ Set.Icc 0 p.1, u (p.1 - s) + β * ∫ l', W ((1 + r) * s + w * l' - r * φ, l') ∂Q p.2
      ≤ W p

/-- Miao, (17.4), p. 561: the Bellman equation in assets
`V(a, l) = max_{a′ ≥ −φ} u(c) + β ∫ V(a′, l′) Q(dl′, l)`, `c = (1 + r)a + wl − a′ ≥ 0`, attained
at the policy `a′ = g(a, l)`, on the states `a ≥ −φ`, `l ∈ [l_min, l_max]`. -/
def ay_Bellman (u : ℝ → ℝ) (β r w φ lmin lmax : ℝ) (Q : Kernel ℝ ℝ) (V g : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, -φ ≤ p.1 → p.2 ∈ Set.Icc lmin lmax →
    g p ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2) ∧
    V p = u ((1 + r) * p.1 + w * p.2 - g p) + β * ∫ l', V (g p, l') ∂Q p.2 ∧
    ∀ a' ∈ Set.Icc (-φ) ((1 + r) * p.1 + w * p.2),
      u ((1 + r) * p.1 + w * p.2 - a') + β * ∫ l', V (a', l') ∂Q p.2 ≤ V p

/-- Miao, (17.4), p. 561: a solution `(V, A)` of the Bellman equation in cash on hand gives a
solution of (17.4): `V(a, l) = V((1 + r)a + wl + φ, l)` with policy `g(a, l) = A(x, l) − φ`
(for `1 + r ≥ 0`). -/
theorem eq_17_4 {u : ℝ → ℝ} {β r w φ lmin lmax : ℝ} {Q : Kernel ℝ ℝ} {W A : ℝ × ℝ → ℝ}
    (hr : 0 ≤ 1 + r) (hW : ay_BellmanCoh u β r w φ lmin lmax Q W A) :
    ay_Bellman u β r w φ lmin lmax Q (fun p => W ((1 + r) * p.1 + w * p.2 + φ, p.2))
      (fun p => A ((1 + r) * p.1 + w * p.2 + φ, p.2) - φ) := by
  intro p ha hl
  set x := (1 + r) * p.1 + w * p.2 + φ with hx
  have hxlo : w * p.2 - r * φ ≤ x := by
    have := mul_le_mul_of_nonneg_left ha hr
    simp only [hx]; nlinarith
  obtain ⟨hA, hV, hmax⟩ := hW (x, p.2) hxlo hl
  have hint : ∀ s : ℝ, (fun l' => W ((1 + r) * (s - φ) + w * l' + φ, l')) =
      fun l' => W ((1 + r) * s + w * l' - r * φ, l') := fun s => by
    funext l'
    rw [show (1 + r) * (s - φ) + w * l' + φ = (1 + r) * s + w * l' - r * φ by ring]
  refine ⟨⟨by linarith [hA.1], by linarith [hA.2]⟩, ?_, fun a' ha' => ?_⟩
  · simp only
    rw [hint, hV]
    congr 2
    ring
  · have hs : a' + φ ∈ Set.Icc 0 x := ⟨by linarith [ha'.1], by linarith [ha'.2]⟩
    have h := hmax (a' + φ) hs
    have h2 := hint (a' + φ)
    simp only [add_sub_cancel_right] at h2
    simp only
    rw [h2, show (1 + r) * p.1 + w * p.2 - a' = x - (a' + φ) by ring]
    exact h

/-- Miao, p. 562: the **transition function** of the joint process `(a_t, l_t)`,
`P(·, (a, l)) = δ_{g(a,l)} ⊗ Q(·, l)`. -/
noncomputable def ay_P (Q : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) (hg : Measurable g) :
    Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  Kernel.deterministic g hg ×ₖ Kernel.comap Q Prod.snd measurable_snd

/-- Miao, p. 562: `P(A × B, (a, l)) = 1_{g(a,l) ∈ A} Q(B, l)`. -/
theorem ay_P_apply (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (p : ℝ × ℝ) {A B : Set ℝ} (hA : MeasurableSet A) :
    ay_P Q g hg p (A ×ˢ B) = A.indicator 1 (g p) * Q p.2 B := by
  rw [ay_P, Kernel.prod_apply_prod, Kernel.deterministic_apply' hg p hA, Kernel.comap_apply]
  rfl

/-- Miao, p. 562: `P` is a Markov kernel (a transition function). -/
theorem ay_P_markov (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    IsMarkovKernel (ay_P Q g hg) := by
  unfold ay_P; infer_instance

/-- Miao, p. 562: the sequence of distributions `λ_{t+1} = ∫ P(·, (a, l)) dλ_t`. -/
noncomputable def ay_lamSeq (Q : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (lam0 : Measure (ℝ × ℝ)) (t : ℕ) : Measure (ℝ × ℝ) :=
  (fun m : Measure (ℝ × ℝ) => m.bind (ay_P Q g hg))^[t] lam0

/-- Miao, p. 562: `λ_{t+1}(A × B) = ∫ P(A × B, (a, l)) dλ_t(a, l)
= ∫ 1_{g(a,l) ∈ A} Q(B, l) dλ_t(a, l)`. -/
theorem ay_lamSeq_succ (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) (lam0 : Measure (ℝ × ℝ)) (t : ℕ) {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ay_lamSeq Q g hg lam0 (t + 1) (A ×ˢ B) =
      ∫⁻ p, A.indicator 1 (g p) * Q p.2 B ∂ay_lamSeq Q g hg lam0 t := by
  rw [ay_lamSeq, Function.iterate_succ_apply',
    Measure.bind_apply (hA.prod hB) (ay_P Q g hg).aemeasurable]
  exact lintegral_congr fun p => ay_P_apply Q hg p hA

/-- Miao, (17.7), p. 563: `λ*` is a **stationary distribution**:
`λ*(A × B) = ∫ 1_{g(a,l) ∈ A} Q(B, l) dλ*(a, l)` for all Borel `A`, `B`. -/
def ay_Stationary (Q : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) (lam : Measure (ℝ × ℝ)) : Prop :=
  ∀ A B : Set ℝ, MeasurableSet A → MeasurableSet B →
    lam (A ×ˢ B) = ∫⁻ p, A.indicator 1 (g p) * Q p.2 B ∂lam

/-- Miao, (17.7), p. 563: for a probability measure `λ*`, (17.7) on rectangles is equivalent to
invariance under the transition function, `λ* = ∫ P(·, (a, l)) dλ*` (rectangles generate the
Borel sets of `ℝ × ℝ` and form a π-system). -/
theorem eq_17_7 (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (lam : Measure (ℝ × ℝ)) [IsProbabilityMeasure lam] :
    ay_Stationary Q g lam ↔ lam.bind (ay_P Q g hg) = lam := by
  have hrect : ∀ A B : Set ℝ, MeasurableSet A → MeasurableSet B →
      lam.bind (ay_P Q g hg) (A ×ˢ B) = ∫⁻ p, A.indicator 1 (g p) * Q p.2 B ∂lam :=
    fun A B hA hB => by
      rw [Measure.bind_apply (hA.prod hB) (ay_P Q g hg).aemeasurable]
      exact lintegral_congr fun p => ay_P_apply Q hg p hA
  constructor
  · intro hst
    have hC : ∀ s ∈ Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s}
        {t : Set ℝ | MeasurableSet t}, lam s = lam.bind (ay_P Q g hg) s := by
      rintro s ⟨A, hA, B, hB, rfl⟩
      rw [hrect A B hA hB, hst A B hA hB]
    refine (ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod hC ?_).symm
    rw [← Set.univ_prod_univ, hrect _ _ MeasurableSet.univ MeasurableSet.univ,
      hst _ _ MeasurableSet.univ MeasurableSet.univ]
  · intro h A B hA hB
    rw [← hrect A B hA hB, h]

/-- Miao, p. 562: under (17.7) the asset marginal of `λ*` is the image of `λ*` under the policy
`g`: `λ*(A × ℝ) = λ*{(a, l) : g(a, l) ∈ A}`. -/
theorem ay_stationary_fst {Q : Kernel ℝ ℝ} [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) {lam : Measure (ℝ × ℝ)} (hst : ay_Stationary Q g lam) :
    lam.map Prod.fst = lam.map g := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, Measure.map_apply hg hA, ← Set.prod_univ,
    hst A Set.univ hA MeasurableSet.univ, ← lintegral_indicator_one (hg hA)]
  refine lintegral_congr fun p => ?_
  rw [measure_univ, mul_one]
  rfl

/-- Miao, p. 563: under (17.7) the labour marginal of `λ*` is invariant under `Q`. -/
theorem ay_stationary_snd {Q : Kernel ℝ ℝ} [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    {lam : Measure (ℝ × ℝ)} (hst : ay_Stationary Q g lam) :
    (lam.map Prod.snd).bind Q = lam.map Prod.snd := by
  ext B hB
  rw [Measure.bind_apply hB Q.aemeasurable, Measure.map_apply measurable_snd hB,
    lintegral_map (Q.measurable_coe hB) measurable_snd, ← Set.univ_prod,
    hst Set.univ B MeasurableSet.univ hB]
  refine lintegral_congr fun p => ?_
  simp

/-- Miao, p. 563: with iid shocks (`Q(·, l) = ν` for every `l`) the labour marginal of a
stationary `λ*` is `ν`, so aggregate labour `∫ l dλ*` is the mean of `l_t`. -/
theorem ay_stationary_snd_iid {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ × ℝ → ℝ}
    {lam : Measure (ℝ × ℝ)} [IsProbabilityMeasure lam]
    (hst : ay_Stationary (Kernel.const ℝ ν) g lam) :
    lam.map Prod.snd = ν ∧ ∫ p, p.2 ∂lam = ∫ l, l ∂ν := by
  have hm : lam.map Prod.snd = ν := by
    ext B hB
    rw [Measure.map_apply measurable_snd hB, ← Set.univ_prod,
      hst Set.univ B MeasurableSet.univ hB]
    simp
  refine ⟨hm, ?_⟩
  have h : ∫ x, x ∂(lam.map Prod.snd) = ∫ p, p.2 ∂lam :=
    integral_map measurable_snd.aemeasurable aestronglyMeasurable_id
  rw [← h, hm]

/-- Miao, p. 562: the long-run average assets `Ea(r, w) = ∫ g(a, l) dλ*(a, l)`. -/
noncomputable def ay_Ea (g : ℝ × ℝ → ℝ) (lam : Measure (ℝ × ℝ)) : ℝ := ∫ p, g p ∂lam

/-- Miao, p. 562: under (17.7), `Ea = ∫ g dλ*` is also the mean of current assets
`∫ a dλ*(a, l)`. -/
theorem ay_Ea_eq_mean {Q : Kernel ℝ ℝ} [IsMarkovKernel Q] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) {lam : Measure (ℝ × ℝ)} (hst : ay_Stationary Q g lam) :
    ∫ p, p.1 ∂lam = ay_Ea g lam := by
  have h1 : ∫ x, x ∂(lam.map Prod.fst) = ∫ p, p.1 ∂lam :=
    integral_map measurable_fst.aemeasurable aestronglyMeasurable_id
  have h2 : ∫ x, x ∂(lam.map g) = ∫ p, g p ∂lam :=
    integral_map hg.aemeasurable aestronglyMeasurable_id
  rw [ay_Ea, ← h1, ← h2, ay_stationary_fst hg hst]

end Miao.IncompleteMarkets
