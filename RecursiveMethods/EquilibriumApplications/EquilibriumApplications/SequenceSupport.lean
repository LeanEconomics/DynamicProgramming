/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.SequenceAssumptions
import EquilibriumApplications.SequenceInfinity

/-!
# Theorem 15.6: supporting prices without weight at infinity

SLP §15.4, pp. 466–467. The commodity space is `S = BddSeq E`; `ψ = seqRegularPart φ` is the
regular part of `φ ∈ S*` given by Lemma 15.5, `ψ(x) = lim_T φ(xᵀ) = Σ_t ψ_t(x_t)`.

* **Theorem 15.6** (`theorem_15_6`, p. 466): let `[(xᵢ⁰), (yⱼ⁰)]` be feasible, let
  Assumptions 15.1, 15.2, 15.6 and 15.7 hold, let `φ ∈ S*` satisfy
  (4) `x ∈ Xᵢ, uᵢ(x) ≥ uᵢ(xᵢ⁰) ⇒ φ(x) ≥ φ(xᵢ⁰)` and (5) `y ∈ Yⱼ ⇒ φ(y) ≤ φ(yⱼ⁰)`, and let every
  consumer have `x̂ᵢ ∈ Xᵢ` with `uᵢ(x̂ᵢ) > uᵢ(xᵢ⁰)`. Then (4) and (5) hold for `ψ`, and
  `ψ(xᵢ⁰) = φ(xᵢ⁰)`, `ψ(yⱼ⁰) = φ(yⱼ⁰)`. Steps 1 and 2 of the proof are
  `seq_support_step1_consumer`, `seq_support_step1_firm` and `seq_support_step2`.
* `theorem_15_6_of_supporting`: the same with the conclusion of Theorem 15.4 as hypothesis — a
  Pareto optimum and `φ ≠ 0` with (3)–(4) of Theorem 15.4 — giving `ψ` with (3)–(4), no weight at
  infinity, and the inner-product form `ψ(x) = Σ_t ψ_t(x_t)`. It composes with Theorem 15.4.
* `theorem_15_6_competitiveEq`: if in addition 15.3 holds and every consumer has a `ψ`-cheaper
  point (the Remark after Theorem 15.4, applied to `ψ`), then `[(xᵢ⁰), (yⱼ⁰), ψ]` is a competitive
  equilibrium, and `ψ ≠ 0` (`seqRegularPart_ne_zero_of_cheaper`).

**Corrections.**
* Theorem 15.6 does not assert `ψ ≠ 0`, and `ψ = 0` can happen (`theorem_15_6_counterexample`):
  in an economy satisfying all of Assumptions 15.1–15.7 (`S = ℓ∞`, one consumer with
  `X = c00`, `u(x) = Σ_t (1/2)ᵗ x_t`, one firm with `Y = {y ≤ 0}`), the Pareto optimum `0` with a
  nonsatiated consumer is supported by some `φ ≠ 0` (Theorem 15.4's conclusion) whose regular part
  is `ψ = 0`, although a nonzero price system without weight at infinity (`σ = u`) also supports
  it. So "ψ is an equilibrium price system" needs the cheaper-point condition for `ψ`, which the
  book adds in its summary.
* The proof's claim "by 15.1 and 15.2, `uᵢ(x^θ) > uᵢ(xᵢ⁰)`" needs care when `uᵢ(x̂ᵢ) = uᵢ(x)`;
  the transcription's NOTE repairs it with quasi-concavity from 15.3. A case split avoids 15.3
  altogether: if `uᵢ(x) > uᵢ(xᵢ⁰)` apply 15.6–15.7 to `x` itself; if `uᵢ(x) = uᵢ(xᵢ⁰)` then
  `uᵢ(x̂ᵢ) > uᵢ(x)` and 15.2 applies. Assumptions 15.3–15.5 are not used (except 15.3 for the
  equilibrium corollary).
* The nonsatiation point `x̂ᵢ` is needed for every consumer `i`, not just one as in
  Theorem 15.4.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `θ x̂ + (1 − θ) x → x` as `θ → 0⁺`, staying in `A` for `θ ∈ (0, 1)`. -/
theorem seq_tendsto_segment {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {A : Set S}
    (hA : Convex ℝ A) {a b : S} (ha : a ∈ A) (hb : b ∈ A) :
    Tendsto (fun θ : ℝ => θ • a + (1 - θ) • b) (𝓝[>] 0) (𝓝[A] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun θ : ℝ => θ • a + (1 - θ) • b :=
      (continuous_id.smul continuous_const).add ((continuous_const.sub continuous_id).smul
        continuous_const)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with θ hθ
    exact hA ha hb hθ.1.le (by linarith [hθ.2]) (by ring)

/-- **Theorem 15.6, Step 1, consumers** ((6), p. 466): `x ∈ Xᵢ`, `uᵢ(x) ≥ uᵢ(xᵢ⁰)` imply
`ψ(x) ≥ φ(xᵢ⁰)`. Uses 15.1, 15.2, 15.6, 15.7 and the nonsatiation point `x̂ᵢ` (not 15.3). -/
theorem seq_support_step1_consumer {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    {φ : StrongDual ℝ (BddSeq E)} {x₀ : BddSeq E} (hA : Convex ℝ A) (hqc : SeqSemistrictQC A v)
    (htc : SeqTruncClosed A) (hti : SeqTailInsensitive A v) (hx₀ : x₀ ∈ A)
    (hsup : ∀ z ∈ A, v x₀ ≤ v z → φ x₀ ≤ φ z) {xh : BddSeq E} (hxh : xh ∈ A)
    (hns : v x₀ < v xh) : ∀ z ∈ A, v x₀ ≤ v z → φ x₀ ≤ seqRegularPart φ z := by
  have key : ∀ w ∈ A, v x₀ < v w → φ x₀ ≤ seqRegularPart φ w := fun w hw hlt =>
    ge_of_tendsto (tendsto_apply_seqTrunc φ w)
      ((hti.eventually htc hw hx₀ hlt).mono fun _ hT => hsup _ hT.1 hT.2.le)
  intro z hz hle
  rcases hle.lt_or_eq with hlt | heq
  · exact key z hz hlt
  · have hzxh : v z < v xh := heq ▸ hns
    have hlim : Tendsto (fun θ : ℝ => θ * seqRegularPart φ xh + (1 - θ) * seqRegularPart φ z)
        (𝓝[>] 0) (𝓝 (seqRegularPart φ z)) := by
      have hc : Continuous fun θ : ℝ =>
          θ * seqRegularPart φ xh + (1 - θ) * seqRegularPart φ z :=
        (continuous_id.mul continuous_const).add ((continuous_const.sub continuous_id).mul
          continuous_const)
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with θ hθ
    have hmem : θ • xh + (1 - θ) • z ∈ A := hA hxh hz hθ.1.le (by linarith [hθ.2]) (by ring)
    have hv : v x₀ < v (θ • xh + (1 - θ) • z) := heq ▸ hqc xh hxh z hz hzxh θ hθ.1 hθ.2
    have := key _ hmem hv
    rwa [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this

/-- **Theorem 15.6, Step 1, firms** ((7), p. 466): `y ∈ Yⱼ` implies `ψ(y) ≤ φ(yⱼ⁰)`. -/
theorem seq_support_step1_firm {B : Set (BddSeq E)} {φ : StrongDual ℝ (BddSeq E)}
    {y₀ : BddSeq E} (htc : SeqTruncClosed B) (hsup : ∀ w ∈ B, φ w ≤ φ y₀) :
    ∀ w ∈ B, seqRegularPart φ w ≤ φ y₀ := fun w hw =>
  le_of_tendsto (tendsto_apply_seqTrunc φ w) ((htc w hw).mono fun _ hT => hsup _ hT)

/-- **Theorem 15.6, Step 2** (p. 467): from `ψ(xᵢ⁰) ≥ φ(xᵢ⁰)`, `ψ(yⱼ⁰) ≤ φ(yⱼ⁰)` and
`Σᵢ xᵢ⁰ = Σⱼ yⱼ⁰`, all these inequalities are equalities. -/
theorem seq_support_step2 {ι κ : Type*} [Fintype ι] [Fintype κ] {φ ψ : StrongDual ℝ (BddSeq E)}
    {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (hfeas : ∑ i, x₀ i - ∑ j, y₀ j = 0)
    (hx : ∀ i, φ (x₀ i) ≤ ψ (x₀ i)) (hy : ∀ j, ψ (y₀ j) ≤ φ (y₀ j)) :
    (∀ i, ψ (x₀ i) = φ (x₀ i)) ∧ ∀ j, ψ (y₀ j) = φ (y₀ j) := by
  have hsum : ∑ i, x₀ i = ∑ j, y₀ j := sub_eq_zero.1 hfeas
  have htot : ∑ i, (ψ (x₀ i) - φ (x₀ i)) + ∑ j, (φ (y₀ j) - ψ (y₀ j)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← map_sum,
      ← map_sum, hsum]
    ring
  have ha : ∀ i ∈ Finset.univ, 0 ≤ ψ (x₀ i) - φ (x₀ i) := fun i _ => sub_nonneg.2 (hx i)
  have hb : ∀ j ∈ Finset.univ, 0 ≤ φ (y₀ j) - ψ (y₀ j) := fun j _ => sub_nonneg.2 (hy j)
  have hA0 := Finset.sum_nonneg ha
  have hB0 := Finset.sum_nonneg hb
  have hA : ∑ i, (ψ (x₀ i) - φ (x₀ i)) = 0 := by linarith
  have hB : ∑ j, (φ (y₀ j) - ψ (y₀ j)) = 0 := by linarith
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hA i (Finset.mem_univ i)
    linarith
  · have := (Finset.sum_eq_zero_iff_of_nonneg hb).1 hB j (Finset.mem_univ j)
    linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Theorem 15.6** (p. 466). Let `[(xᵢ⁰), (yⱼ⁰)]` be feasible, let Assumptions 15.1, 15.2, 15.6
and 15.7 hold, let `φ ∈ S*` satisfy (4) and (5), and let every consumer `i` have `x̂ᵢ ∈ Xᵢ` with
`uᵢ(x̂ᵢ) > uᵢ(xᵢ⁰)`. Then `ψ = seqRegularPart φ` (Lemma 15.5) satisfies (4) and (5), and agrees
with `φ` on every `xᵢ⁰` and `yⱼ⁰`. (Assumptions 15.3–15.5 are not needed.) -/
theorem theorem_15_6 {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ} {Y : κ → Set (BddSeq E)}
    {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h6 : Assumption15_6 X Y) (h7 : Assumption15_7 X u) (hfeas : Feasible X Y x₀ y₀)
    (φ : StrongDual ℝ (BddSeq E))
    (h4 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h5 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → seqRegularPart φ (x₀ i) ≤ seqRegularPart φ z) ∧
    (∀ j, ∀ w ∈ Y j, seqRegularPart φ w ≤ seqRegularPart φ (y₀ j)) ∧
    (∀ i, seqRegularPart φ (x₀ i) = φ (x₀ i)) ∧ ∀ j, seqRegularPart φ (y₀ j) = φ (y₀ j) := by
  have s6 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ seqRegularPart φ z := fun i => by
    obtain ⟨xh, hxh, hlt⟩ := hns i
    exact seq_support_step1_consumer (h1 i) (h2 i) (h6.1 i) (h7 i) (hfeas.1 i) (h4 i) hxh hlt
  have s7 : ∀ j, ∀ w ∈ Y j, seqRegularPart φ w ≤ φ (y₀ j) := fun j =>
    seq_support_step1_firm (h6.2 j) (h5 j)
  obtain ⟨ex, ey⟩ := seq_support_step2 (φ := φ) (ψ := seqRegularPart φ) hfeas.2.2
    (fun i => s6 i _ (hfeas.1 i) le_rfl) (fun j => s7 j _ (hfeas.2.1 j))
  exact ⟨fun i z hz hle => (ex i).trans_le (s6 i z hz hle),
    fun j w hw => (s7 j w hw).trans_eq (ey j).symm, ex, ey⟩

/-- **Theorem 15.6, composed with the conclusion of Theorem 15.4.** For a Pareto optimum
satisfying 15.1, 15.2, 15.6 and 15.7 with every consumer nonsatiated, if some `φ ∈ S*`, `φ ≠ 0`,
satisfies (3)–(4) of Theorem 15.4, then some `ψ ∈ S*` satisfies (3)–(4), has no weight at infinity
(`ψ(x) = lim_T ψ(xᵀ)`) and has the inner-product form `ψ(x) = Σ_t ψ_t(x_t)`. (It need not be
nonzero: `theorem_15_6_counterexample`.) -/
theorem theorem_15_6_of_supporting {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h6 : Assumption15_6 X Y) (h7 : Assumption15_7 X u)
    (hPO : ParetoOptimal X u Y x₀ y₀) (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh)
    (hφ : ∃ φ : StrongDual ℝ (BddSeq E), φ ≠ 0 ∧
      (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z) ∧
      ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j)) :
    ∃ ψ : StrongDual ℝ (BddSeq E),
      (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → ψ (x₀ i) ≤ ψ z) ∧
      (∀ j, ∀ w ∈ Y j, ψ w ≤ ψ (y₀ j)) ∧
      (∀ x, Tendsto (fun T => ψ (seqTrunc T x)) atTop (𝓝 (ψ x))) ∧
      ∀ x : BddSeq E, HasSum (fun t => coordFunctional ψ t (x t)) (ψ x) := by
  obtain ⟨φ, -, h3, h4⟩ := hφ
  obtain ⟨r4, r5, -, -⟩ := theorem_15_6 h1 h2 h6 h7 hPO.1 φ h3 h4 hns
  refine ⟨seqRegularPart φ, r4, r5, fun x => ?_, fun x => ?_⟩
  · simpa [seqRegularPart_seqRegularPart] using tendsto_apply_seqTrunc (seqRegularPart φ) x
  · simpa [seqRegularPart_seqRegularPart] using hasSum_seqRegularPart (seqRegularPart φ) x

/-- The Remark after Theorem 15.4 (p. 456), for one consumer: if `ψ` satisfies (3) at `x⁰`,
`u` is continuous on the convex set `A`, and some `w ∈ A` has `ψ(w) < ψ(x⁰)`, then `x⁰` maximises
`u` on the budget set `{z ∈ A : ψ(z) ≤ ψ(x⁰)}`. -/
theorem seq_budget_max_of_cheaper {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {A : Set S} {v : S → ℝ} {ψ : StrongDual ℝ S} {x₀ : S} (hA : Convex ℝ A)
    (hv : ContinuousOn v A) (h3 : ∀ z ∈ A, v x₀ ≤ v z → ψ x₀ ≤ ψ z) {w : S} (hw : w ∈ A)
    (hcheap : ψ w < ψ x₀) : ∀ z ∈ A, ψ z ≤ ψ x₀ → v z ≤ v x₀ := by
  intro z hz hbud
  by_contra hcon
  have hlim := ((hv z hz).tendsto).comp (seq_tendsto_segment hA hw hz)
  obtain ⟨θ, hθ, hvθ⟩ := ((show ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 1 from
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)).and
    (hlim.eventually (lt_mem_nhds (not_le.1 hcon)))).exists
  have hmem : θ • w + (1 - θ) • z ∈ A := hA hw hz hθ.1.le (by linarith [hθ.2]) (by ring)
  have := h3 _ hmem hvθ.le
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  nlinarith [hθ.1, hθ.2]

/-- **Theorem 15.6 with the Remark**: under the hypotheses of `theorem_15_6`, Assumption 15.3, and
a `ψ`-cheaper point `x′ᵢ ∈ Xᵢ` (`ψ(x′ᵢ) < ψ(xᵢ⁰)`) for every consumer, `[(xᵢ⁰), (yⱼ⁰), ψ]` is a
competitive equilibrium with a price system without weight at infinity. -/
theorem theorem_15_6_competitiveEq {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u) (h6 : Assumption15_6 X Y)
    (h7 : Assumption15_7 X u) (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h4 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h5 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh)
    (hcheap : ∀ i, ∃ w ∈ X i, seqRegularPart φ w < seqRegularPart φ (x₀ i)) :
    CompetitiveEq X u Y x₀ y₀ (seqRegularPart φ) := by
  obtain ⟨r4, r5, -, -⟩ := theorem_15_6 h1 h2 h6 h7 hfeas φ h4 h5 hns
  refine ⟨hfeas, fun i => ?_, r5⟩
  obtain ⟨w, hw, hlt⟩ := hcheap i
  exact seq_budget_max_of_cheaper (h1 i) (h3 i) (r4 i) hw hlt

/-- With a cheaper point for some consumer, `ψ ≠ 0`. -/
theorem seqRegularPart_ne_zero_of_cheaper {φ : StrongDual ℝ (BddSeq E)} {w x : BddSeq E}
    (h : seqRegularPart φ w < seqRegularPart φ x) : seqRegularPart φ ≠ 0 := fun h0 => by
  rw [h0] at h
  simp at h

/-! ### `ψ` can vanish -/

/-- `σ(y) ≤ 0` for `y ≤ 0`. -/
theorem halfSum_nonpos {y : BddSeq ℝ} (hy : ∀ t, y t ≤ 0) : halfSum y ≤ 0 :=
  tsum_nonpos fun t => mul_nonpos_of_nonneg_of_nonpos (by positivity) (hy t)

/-- **Theorem 15.6 does not give `ψ ≠ 0`.** On `S = ℓ∞`, take one consumer with `X = c00` and
`u = σ` (`σ(x) = Σ_t (1/2)ᵗ x_t`), one firm with `Y = {y : y_t ≤ 0 ∀ t}`, and the allocation
`x⁰ = y⁰ = 0`. Assumptions 15.1–15.7 hold, the allocation is Pareto optimal, the consumer is
nonsatiated, and some `φ ≠ 0` satisfies (3)–(4) of Theorem 15.4, but its regular part is `ψ = 0`.
Yet `σ ≠ 0`, which has no weight at infinity, also satisfies (3)–(4). -/
theorem theorem_15_6_counterexample :
    ∃ (X : Unit → Set (BddSeq ℝ)) (u : Unit → BddSeq ℝ → ℝ) (Y : Unit → Set (BddSeq ℝ))
      (x₀ : Unit → BddSeq ℝ) (y₀ : Unit → BddSeq ℝ) (φ : StrongDual ℝ (BddSeq ℝ)),
      Assumption15_1 X ∧ Assumption15_2 X u ∧ Assumption15_3 X u ∧ Assumption15_4 Y ∧
      Assumption15_5 (BddSeq ℝ) Y ∧ Assumption15_6 X Y ∧ Assumption15_7 X u ∧
      ParetoOptimal X u Y x₀ y₀ ∧ (∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) ∧
      φ ≠ 0 ∧ (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z) ∧
      (∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j)) ∧ seqRegularPart φ = 0 ∧
      (halfSum ≠ 0 ∧ (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → halfSum (x₀ i) ≤ halfSum z) ∧
        (∀ j, ∀ w ∈ Y j, halfSum w ≤ halfSum (y₀ j)) ∧ seqRegularPart halfSum = halfSum) := by
  obtain ⟨φ, hφ1, hφ0, hφone⟩ := exists_seq_functional_at_infinity
  set Ycone : Set (BddSeq ℝ) := {y | ∀ t, y t ≤ 0} with hYcone
  have hagg : aggTech (fun _ : Unit => Ycone) = Ycone := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy ()
    · intro hw
      exact ⟨fun _ => w, fun _ => hw, by simp⟩
  have hYconv : Convex ℝ Ycone := fun y hy y' hy' a b ha hb _ t => by
    rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
    nlinarith [hy t, hy' t]
  have hsingle : halfSum (lp.single ∞ 0 1) = 1 := by rw [halfSum_single]; norm_num
  refine ⟨fun _ => (seqC00 ℝ : Set (BddSeq ℝ)), fun _ => halfSum, fun _ => Ycone, fun _ => 0,
    fun _ => 0, φ, fun _ => (seqC00 ℝ).convex, fun _ z _ z' _ hlt θ h0 h1 => ?_,
    fun _ => halfSum.continuous.continuousOn, ?_, ?_, ⟨fun _ x hx => ?_, fun _ y hy => ?_⟩,
    fun _ => SeqTailInsensitive.of_tendsto fun x _ => tendsto_halfSum_seqTrunc x, ⟨⟨fun _ => ?_,
    fun _ => ?_, by simp⟩, ?_⟩, fun _ => ⟨lp.single ∞ 0 1, ?_, ?_⟩, ?_, fun _ z hz _ => ?_,
    fun _ w hw => ?_, seqRegularPart_eq_zero_of_seqC00 hφ0, ?_, fun _ z _ hz => hz,
    fun _ w hw => ?_, ?_⟩
  · change halfSum z' < halfSum z at hlt
    change halfSum z' < halfSum (θ • z + (1 - θ) • z')
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  · change Convex ℝ (aggTech fun _ : Unit => Ycone)
    rw [hagg]; exact hYconv
  · left
    rw [hagg]
    refine ⟨-oneSeq, mem_interior.2 ⟨Metric.ball (-oneSeq) 1, fun y hy t => ?_,
      Metric.isOpen_ball, Metric.mem_ball_self one_pos⟩⟩
    have h := (norm_seq_coord_le (y - -oneSeq) t).trans_lt (by rwa [← dist_eq_norm])
    rw [lp.coeFn_sub, lp.coeFn_neg, Pi.sub_apply, Pi.neg_apply] at h
    have h' := (abs_lt.1 (by simpa using h)).2
    simp [oneSeq] at h'
    linarith
  · exact Eventually.of_forall fun T => seqTrunc_mem_seqC00 T x
  · refine Eventually.of_forall fun T t => ?_
    rw [seqTrunc_apply]; split_ifs
    · exact hy t
    · exact le_rfl
  · exact (seqC00 ℝ).zero_mem
  · exact fun t => le_rfl
  · rintro ⟨x', y', ⟨hx', hy', hxy⟩, -, i, hi⟩
    simp only [Finset.univ_unique, Finset.sum_singleton] at hxy
    have he : x' () = y' () := sub_eq_zero.1 hxy
    have := halfSum_nonpos (y := x' ()) fun t => he ▸ hy' () t
    simp only [map_zero] at hi
    exact absurd hi (not_lt.2 (by cases i; exact this))
  · exact (eventually_gt_atTop 0).mono fun s hs => by
      rw [lp.single_apply, Pi.single_eq_of_ne (ne_of_gt hs)]
  · simp [hsingle]
  · intro h0
    have := congrArg (fun f : StrongDual ℝ (BddSeq ℝ) => f oneSeq) h0
    simp [hφone] at this
  · simp [hφ0 z hz]
  · simp [seq_apply_nonpos_of_nonpos hφ1 hφone hw]
  · intro h0
    have := congrArg (fun f : StrongDual ℝ (BddSeq ℝ) => f (lp.single ∞ 0 1)) h0
    simp [hsingle] at this
  · simpa using halfSum_nonpos hw
  · ext x
    exact tendsto_nhds_unique (tendsto_apply_seqTrunc halfSum x) (tendsto_halfSum_seqTrunc x)

end StokeyLucasPrescott.EquilibriumApplications
