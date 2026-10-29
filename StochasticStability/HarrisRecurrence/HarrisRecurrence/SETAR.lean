/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.StochasticComparison
import HarrisRecurrence.TChainModels

/-!
# Proposition 9.5.4: transience of SETAR models (MT §9.5.2)

Meyn and Tweedie, Proposition 9.5.4, p. 222, with the exterior regions (9.46)–(9.51) of the
parameter space. Book indexing: regime `1` is `0 : Fin (m + 1)`, regime `M` is `Fin.last m`.

**Method.** Every region is handled pathwise on the noise path space (`pathKernel_recursion`):
far from the thresholds (`|x| > ρ = 1 + Σ|rᵢ|`, `setarBound`) the chain follows one of the two
end linear models, and on a set of noise paths of positive probability it never returns to
`[−ρ, ρ]`; Theorem 8.3.6 then gives transience, with `volume` as the maximal irreducibility
measure (Proposition 6.3.6).
* `escape_of_lower_recursion`: a deterministic lower bound
  `gₙ ≥ Aₙ(x − Σ_{k ≤ n} c_k/A_k)` for a linear lower recursion `gₙ₊₁ ≥ λₙ₊₁gₙ − cₙ₊₁`.
* `ae_bdd_weighted_sum` (first moments and `Σ 1/A_k < ∞`), `ae_bdd_partialSum_of_neg` (strong
  law, negative drift) and `ae_tendsto_blockSum` (strong law for the two-step blocks
  `(W₂ᵢ₊₁, W₂ᵢ₊₂)`, which are pairwise independent and identically distributed) make the
  correction terms a.s. bounded; `exists_measure_pos_forall_le` turns this into one level `k`
  on a set of positive probability; `hitProb_recursion_lt_one` gives `L(x, [−ρ, ρ]) < 1`.

**Results.**
* `proposition_9_5_4_46`, `proposition_9_5_4_47`: (9.46) `θ(1) > 1`, (9.47) `θ(M) > 1`,
  geometric escape (`Aₙ = θⁿ`).
* `proposition_9_5_4_48`, `proposition_9_5_4_49`: (9.48) `θ(1) = 1`, `φ(1) < 0`, and (9.49)
  `θ(M) = 1`, `φ(M) > 0`, a random walk with drift away from the thresholds.
* `proposition_9_5_4_50`: (9.50) `θ(1) < 0`, `θ(1)θ(M) > 1`, alternating escape of the signed
  path `(−1)ⁿXₙ` with multipliers `|θ(M)|, |θ(1)|`.
* `proposition_9_5_4_51`: (9.51) `θ(1) < 0`, `θ(1)θ(M) = 1`, `φ(M) + θ(M)φ(1) < 0`: the
  two-step chain is exactly the random walk `X₂ₙ = x + Tₙ` with drift
  `φ(1) + θ(1)φ(M) = θ(1)(φ(M) + θ(M)φ(1)) > 0`, and the odd steps stay far left since
  `W₂ₙ₊₁(M)/n → 0`.
* `proposition_9_5_4`: transience under any of (9.46)–(9.51).

**Hypotheses.** (SETAR2) as `Γ j ≪ volume` and `volume ≪ Γ j` (as in Proposition 6.3.6) and
zero-mean integrable noise in the two end regimes (part of (SETAR1)). The book's (SETAR3)
(finite variances in the end regimes), used in its proof of (9.51) through the test function
of Theorem 8.4.2, is not needed: the pathwise argument uses first moments only. The
monotonicity of the thresholds is not used. In (9.48) and (9.49) the side conditions
`θ(M) ≤ 1`, `θ(1) ≤ 1` are not used.

**Corrections.** The book's proof of (9.51) is replaced by the pathwise two-step argument; the
book's proofs of (9.46)–(9.50) ("by comparison with random walk", "the same argument for the
two step chain") are made precise by `escape_of_lower_recursion`.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-- **A uniform level for a.s. bounded sequences**: if `fₙ(ω)` is bounded above for a.e. `ω`,
some level `k` bounds every `fₙ` on a set of positive measure. -/
theorem exists_measure_pos_forall_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n))
    (hb : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ n, f n ω ≤ B) :
    ∃ k : ℕ, MeasurableSet {ω | ∀ n, f n ω ≤ k} ∧ 0 < μ {ω | ∀ n, f n ω ≤ k} := by
  set G : ℕ → Set Ω := fun k => {ω | ∀ n, f n ω ≤ k}
  have hGm : ∀ k, MeasurableSet (G k) := fun k => by
    simp only [G, ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_le (hf n) measurable_const
  have hUm : MeasurableSet (⋃ k, G k) := MeasurableSet.iUnion hGm
  have hae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k, G k := hb.mono fun ω ⟨B, hB⟩ => by
    refine mem_iUnion.2 ⟨⌈B⌉₊, fun n => (hB n).trans (Nat.le_ceil B)⟩
  have h1 : μ (⋃ k, G k) = 1 := (prob_compl_eq_zero_iff hUm).1 (ae_iff.1 hae)
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion (h1 ▸ one_pos)
  exact ⟨k, hGm k, hk⟩

variable {X : Type*} [MeasurableSpace X] {W : Type*} [MeasurableSpace W] in
/-- **Escape on a set of noise paths of positive measure**: if every noise path in `G` drives the
recursion from `x` around `C` forever, then `L(x, C) < 1`. -/
theorem hitProb_recursion_lt_one (Γ : Measure W) [IsProbabilityMeasure Γ] {F : X × W → X}
    (hF : Measurable F) {C : Set X} (hC : MeasurableSet C) {G : Set (ℕ → W)}
    (hG : MeasurableSet G) (hGpos : 0 < (Measure.infinitePi fun _ : ℕ => Γ) G) {x : X}
    (hx : ∀ ω ∈ G, ∀ n, 1 ≤ n → orbit F x ω n ∉ C) :
    haveI := isMarkovKernel_recursionKernel Γ hF
    hitProb (recursionKernel Γ F) C x < 1 := by
  have := isMarkovKernel_recursionKernel Γ hF
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  have hmeas : Measurable fun (ω : ℕ → W) (n : ℕ) => orbit F x ω n :=
    measurable_pi_iff.2 fun n => by
      simp_rw [orbit_eq_controlMap]
      exact (measurable_controlMap_right hF n x).comp
        (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  rw [hitProb, ← pathKernel_recursion Γ hF x,
    Measure.map_apply hmeas (measurableSet_firstReturn_ne_top hC)]
  have hsub : (fun (ω : ℕ → W) (n : ℕ) => orbit F x ω n) ⁻¹'
      {ω' | firstReturn C ω' ≠ ⊤} ⊆ Gᶜ := by
    intro ω hω hωG
    simp only [mem_preimage, mem_ofPred_eq, ne_eq, firstReturn_eq_top_iff, not_forall] at hω
    obtain ⟨n, hn, hnC⟩ := hω
    exact hnC (hx ω hωG n hn)
  calc μ _ ≤ μ Gᶜ := measure_mono hsub
    _ = 1 - μ G := prob_compl_eq_one_sub hG
    _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hGpos.ne'

/-- **Pathwise escape from a linear lower recursion**: if `gₙ₊₁ ≥ λₙ₊₁gₙ − cₙ₊₁` whenever
`gₙ > ρ`, with `Aₙ₊₁ ≤ λₙ₊₁Aₙ`, `A₀ = 1`, `Aₙ ≥ a > 0`, and `a(x − Σ_{k ≤ n} c_k/A_k) > ρ` for
every `n`, then `gₙ ≥ Aₙ(x − Σ_{k ≤ n} c_k/A_k) > ρ` for every `n`. -/
theorem escape_of_lower_recursion {g A lam c : ℕ → ℝ} {a ρ x : ℝ} (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hA0 : A 0 = 1) (hA : ∀ n, a ≤ A n) (hAs : ∀ n, A (n + 1) ≤ lam (n + 1) * A n)
    (hlam : ∀ n, 0 ≤ lam (n + 1)) (hg0 : g 0 = x)
    (hstep : ∀ n, ρ < g n → lam (n + 1) * g n - c (n + 1) ≤ g (n + 1))
    (hx : ∀ n, ρ < a * (x - ∑ k ∈ Finset.range n, c (k + 1) / A (k + 1))) :
    ∀ n, ρ < g n := by
  set P : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, c (k + 1) / A (k + 1)
  have hpos : ∀ n, 0 < x - P n := fun n => by
    have := hx n
    by_contra h
    push Not at h
    have : a * (x - P n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le h
    linarith
  have hgt : ∀ n, ρ < A n * (x - P n) := fun n =>
    lt_of_lt_of_le (hx n) (mul_le_mul_of_nonneg_right (hA n) (hpos n).le)
  have key : ∀ n, A n * (x - P n) ≤ g n := by
    intro n
    induction n with
    | zero => simp [P, hA0, hg0]
    | succ n ih =>
      have hgn : ρ < g n := lt_of_lt_of_le (hgt n) ih
      have h1 := hstep n hgn
      have hAn1 : 0 < A (n + 1) := lt_of_lt_of_le ha (hA (n + 1))
      have hP : P (n + 1) = P n + c (n + 1) / A (n + 1) := Finset.sum_range_succ _ _
      have h2 : lam (n + 1) * (A n * (x - P n)) ≤ lam (n + 1) * g n :=
        mul_le_mul_of_nonneg_left ih (hlam n)
      have h3 : A (n + 1) * (x - P n) ≤ lam (n + 1) * A n * (x - P n) :=
        mul_le_mul_of_nonneg_right (hAs n) (hpos n).le
      have e : A (n + 1) * (x - P (n + 1)) = A (n + 1) * (x - P n) - c (n + 1) := by
        rw [hP]; field_simp; ring
      rw [e]
      nlinarith
  exact fun n => lt_of_lt_of_le (hgt n) (key n)

variable {V : Type*} [MeasurableSpace V] in
/-- **Weighted noise sums are a.s. bounded**: if `h_k ≥ 0` has `∫ h_k dΓ ≤ M < ∞` for every `k`
and `Σ 1/A_k < ∞`, then `Σ_{k ≤ n} h_k(ω_k)/A_k` is bounded in `n` for a.e. noise path `ω`. -/
theorem ae_bdd_weighted_sum (Γ : Measure V) [IsProbabilityMeasure Γ] {h : ℕ → V → ℝ}
    (hh : ∀ k, Measurable (h k)) (h0 : ∀ k v, 0 ≤ h k v) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbound : ∀ k, ∫⁻ v, ENNReal.ofReal (h k v) ∂Γ ≤ M) {A : ℕ → ℝ} (hA : ∀ k, 0 < A k)
    (hs : Summable fun k => 1 / A (k + 1)) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Γ), ∃ B : ℝ, ∀ n,
      ∑ k ∈ Finset.range n, h (k + 1) (ω (k + 1)) / A (k + 1) ≤ B := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  have hterm : ∀ k, Measurable fun ω : ℕ → V =>
      ENNReal.ofReal (h (k + 1) (ω (k + 1)) / A (k + 1)) := fun k =>
    (((hh _).comp (measurable_pi_apply _)).div_const _).ennreal_ofReal
  set Z : (ℕ → V) → ℝ≥0∞ := fun ω => ∑' k, ENNReal.ofReal (h (k + 1) (ω (k + 1)) / A (k + 1))
  have hZm : Measurable Z := Measurable.tsum hterm
  have hlin : ∀ k, ∫⁻ ω, ENNReal.ofReal (h (k + 1) (ω (k + 1)) / A (k + 1)) ∂μ ≤
      ENNReal.ofReal (1 / A (k + 1)) * M := by
    intro k
    have e : ∀ ω : ℕ → V, ENNReal.ofReal (h (k + 1) (ω (k + 1)) / A (k + 1)) =
        ENNReal.ofReal (1 / A (k + 1)) * ENNReal.ofReal (h (k + 1) (ω (k + 1))) := fun ω => by
      rw [← ENNReal.ofReal_mul (by have := hA (k + 1); positivity)]; congr 1; ring
    have hm : Measurable fun ω : ℕ → V => ENNReal.ofReal (h (k + 1) (ω (k + 1))) :=
      ((hh (k + 1)).comp (measurable_pi_apply (k + 1))).ennreal_ofReal
    simp_rw [e]
    rw [lintegral_const_mul _ hm]
    refine mul_le_mul_right ?_ _
    rw [← lintegral_map (f := fun v => ENNReal.ofReal (h (k + 1) v)) (hh _).ennreal_ofReal
      (measurable_pi_apply (k + 1)), Measure.infinitePi_map_eval]
    exact hbound _
  have hZ : ∫⁻ ω, Z ω ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun k => (hterm k).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlin)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => by have := hA (k + 1); positivity) hs]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  filter_upwards [ae_lt_top hZm hZ] with ω hω
  refine ⟨(Z ω).toReal, fun n => ?_⟩
  have hle : ENNReal.ofReal (∑ k ∈ Finset.range n, h (k + 1) (ω (k + 1)) / A (k + 1)) ≤ Z ω := by
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => div_nonneg (h0 _ _) (hA _).le]
    exact ENNReal.sum_le_tsum _
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 hle

variable {V : Type*} [MeasurableSpace V] in
/-- **Random walk with negative drift is a.s. bounded above**: if `E c(W) < 0`, then
`Σ_{k ≤ n} c(ω_k)` is bounded above in `n` for a.e. noise path (strong law). -/
theorem ae_bdd_partialSum_of_neg (Γ : Measure V) [IsProbabilityMeasure Γ] {c : V → ℝ}
    (hc : Measurable c) (hint : Integrable c Γ) (hneg : ∫ v, c v ∂Γ < 0) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Γ), ∃ B : ℝ, ∀ n,
      ∑ k ∈ Finset.range n, c (ω (k + 1)) ≤ B := by
  filter_upwards [ae_tendsto_partialSum Γ hc hint] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω.eventually (gt_mem_nhds hneg))
  set S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, c (ω (k + 1))
  refine ⟨∑ j ∈ Finset.range (N + 1), |S j|, fun n => ?_⟩
  have hB0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), |S j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  rcases le_or_gt n N with hn | hn
  · exact (le_abs_self (S n)).trans (Finset.single_le_sum (f := fun j => |S j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  · have h1 := hN n hn.le
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have : S n < 0 := by
      have := (div_lt_iff₀ hnpos).1 h1; simpa [S] using this
    linarith

variable {V : Type*} [MeasurableSpace V] in
/-- **The strong law for two-step blocks**: `(1/n) Σ_{i < n} c(ω_{2i+1}, ω_{2i+2}) → E c(ω₁, ω₂)`
for a.e. noise path; the blocks are pairwise independent and identically distributed. -/
theorem ae_tendsto_blockSum (Γ : Measure V) [IsProbabilityMeasure Γ] {c : V × V → ℝ}
    (hc : Measurable c)
    (hint : Integrable (fun ω : ℕ → V => c (ω 1, ω 2)) (Measure.infinitePi fun _ : ℕ => Γ)) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => Γ),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, c (ω (2 * i + 1), ω (2 * i + 2))) / n)
        atTop (𝓝 (∫ ω, c (ω 1, ω 2) ∂(Measure.infinitePi fun _ : ℕ => Γ))) := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  have hiid : iIndepFun (fun i (ω : ℕ → V) => ω i) μ :=
    iIndepFun_infinitePi (P := fun _ => Γ) (X := fun _ w => w) fun _ => measurable_id
  set pair : ℕ → (ℕ → V) → V × V := fun i ω => (ω (2 * i + 1), ω (2 * i + 2))
  have hpm : ∀ i, Measurable (pair i) := fun i =>
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hlaw : ∀ i, μ.map (pair i) = Γ.prod Γ := fun i => by
    have := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply (2 * i + 1)).aemeasurable
      (measurable_pi_apply (2 * i + 2)).aemeasurable).1 (hiid.indepFun (by omega))
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval] at this
    exact this
  set Y : ℕ → (ℕ → V) → ℝ := fun i ω => c (pair i ω)
  have hYm : ∀ i, Measurable (Y i) := fun i => hc.comp (hpm i)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i =>
    ⟨(hYm _).aemeasurable, (hYm _).aemeasurable, by
      change μ.map (c ∘ pair i) = μ.map (c ∘ pair 0)
      rw [← Measure.map_map hc (hpm i), ← Measure.map_map hc (hpm 0), hlaw, hlaw]⟩
  have hind : Pairwise fun i j => IndepFun (Y i) (Y j) μ := by
    intro i j hij
    set S : Finset ℕ := {2 * i + 1, 2 * i + 2}
    set T : Finset ℕ := {2 * j + 1, 2 * j + 2}
    have hST : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [S, T, Finset.mem_insert, Finset.mem_singleton] at ha hb
      omega
    have h := hiid.indepFun_finset S T hST fun k => measurable_pi_apply k
    have h1 : Measurable fun r : S → V =>
        c (r ⟨2 * i + 1, by simp [S]⟩, r ⟨2 * i + 2, by simp [S]⟩) :=
      hc.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    have h2 : Measurable fun r : T → V =>
        c (r ⟨2 * j + 1, by simp [T]⟩, r ⟨2 * j + 2, by simp [T]⟩) :=
      hc.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    exact h.comp h1 h2
  have hY0 : Integrable (Y 0) μ := by simpa [Y, pair] using hint
  have hE : ∫ ω, Y 0 ω ∂μ = ∫ ω, c (ω 1, ω 2) ∂μ := by simp [Y, pair]
  have hslln := strong_law_ae Y hY0 hind hident
  rw [hE] at hslln
  filter_upwards [hslln] with ω hω
  refine hω.congr fun n => ?_
  simp only [smul_eq_mul, Y, pair]
  rw [div_eq_inv_mul]

/-- A sequence that is eventually `≤ 0` is bounded above. -/
theorem exists_bdd_of_eventually_nonpos {f : ℕ → ℝ} (h : ∀ᶠ n in atTop, f n ≤ 0) :
    ∃ B : ℝ, ∀ n, f n ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨∑ j ∈ Finset.range (N + 1), |f j|, fun n => ?_⟩
  have hB0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), |f j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  rcases le_or_gt n N with hn | hn
  · exact (le_abs_self (f n)).trans (Finset.single_le_sum (f := fun j => |f j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  · linarith [hN n hn.le]

/-! ### The SETAR model far from the thresholds -/

/-- The threshold bound `ρ = 1 + Σᵢ |rᵢ|`: beyond `±ρ` the chain is in an end regime. -/
noncomputable def setarBound {m : ℕ} (r : Fin m → ℝ) : ℝ := 1 + ∑ i, |r i|

/-- `ρ ≥ 1`. -/
theorem one_le_setarBound {m : ℕ} (r : Fin m → ℝ) : 1 ≤ setarBound r :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- `|rᵢ| < ρ`. -/
theorem abs_lt_setarBound {m : ℕ} (r : Fin m → ℝ) (i : Fin m) : |r i| < setarBound r := by
  have := Finset.single_le_sum (f := fun j => |r j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  simp only [setarBound]; linarith

/-- Above `ρ` the regime is the last one. -/
theorem setarRegime_of_gt {m : ℕ} (r : Fin m → ℝ) {x : ℝ} (hx : setarBound r < x) :
    setarRegime r x = Fin.last m := by
  rw [setarRegime_eq_iff]
  refine ⟨fun i _ => ?_, fun h => absurd h (by simp)⟩
  linarith [le_abs_self (r i), abs_lt_setarBound r i]

/-- Below `−ρ` the regime is the first one. -/
theorem setarRegime_of_lt {m : ℕ} (r : Fin m → ℝ) {x : ℝ} (hx : x < -setarBound r) :
    setarRegime r x = 0 := by
  rw [setarRegime_eq_iff]
  refine ⟨fun i hi => absurd hi (by simp), fun h => ?_⟩
  linarith [neg_abs_le (r ⟨((0 : Fin (m + 1)) : ℕ), h⟩),
    abs_lt_setarBound r ⟨((0 : Fin (m + 1)) : ℕ), h⟩]

/-- Above `ρ` the SETAR step is the last linear model. -/
theorem setarStep_of_gt {m : ℕ} (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) {x : ℝ}
    (hx : setarBound r < x) (w : Fin (m + 1) → ℝ) :
    setarStep φ θ r (x, w) = φ (Fin.last m) + θ (Fin.last m) * x + w (Fin.last m) := by
  simp only [setarStep, setarRegime_of_gt r hx]

/-- Below `−ρ` the SETAR step is the first linear model. -/
theorem setarStep_of_lt {m : ℕ} (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ) {x : ℝ}
    (hx : x < -setarBound r) (w : Fin (m + 1) → ℝ) :
    setarStep φ θ r (x, w) = φ 0 + θ 0 * x + w 0 := by
  simp only [setarStep, setarRegime_of_lt r hx]

/-- **Transience of SETAR from pathwise escape**: under (SETAR2) (`volume` is then a maximal
irreducibility measure, Proposition 6.3.6), if from every `x` in a set `D` of positive length
every noise path in a set `G` of positive probability keeps `|Xₙ| > ρ` for `n ≥ 1`, then the
chain is transient (Theorem 8.3.6 with `C = [−ρ, ρ]`). -/
theorem setar_transient_of_escape {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j) {D : Set ℝ} (hD : MeasurableSet D)
    (hDpos : 0 < volume D) {G : Set (ℕ → Fin (m + 1) → ℝ)} (hG : MeasurableSet G)
    (hGpos : 0 < (Measure.infinitePi fun _ : ℕ => Measure.pi Γ) G)
    (hesc : ∀ x ∈ D, ∀ ω ∈ G, ∀ n, 1 ≤ n →
      setarBound r < |orbit (setarStep φ θ r) x ω n|) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  have := isMarkovKernel_setarKernel Γ φ θ r
  obtain ⟨_, hψ, -, -⟩ := proposition_6_3_6 Γ φ θ r h1 h2
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  refine (theorem_8_3_6_ii _ hψ).2 ⟨Icc (-ρ) ρ, D, measurableSet_Icc, hD, ?_, hDpos,
    fun x hx => ?_⟩
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_pos.2 (by linarith)
  · exact hitProb_recursion_lt_one (Measure.pi Γ) (measurable_setarStep φ θ r) measurableSet_Icc
      hG hGpos fun ω hω n hn hC => by
        have h3 := hesc x hx ω hω n hn
        have h4 := abs_le.2 (mem_Icc.1 hC)
        linarith

/-- The `n`-th noise vector's `j`-th coordinate is measurable on the noise path space. -/
theorem measurable_noise {m : ℕ} (i : ℕ) (j : Fin (m + 1)) :
    Measurable fun ω : ℕ → Fin (m + 1) → ℝ => ω i j :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- `E|c + W(j)| < ∞` for an integrable regime noise. -/
theorem setar_noise_lintegral_ne_top {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] {j : Fin (m + 1)} (hint : Integrable (fun w : ℝ => w) (Γ j))
    (c : ℝ) : ∫⁻ v, ENNReal.ofReal |c + v j| ∂Measure.pi Γ ≠ ⊤ := by
  have hm : Measurable fun w : ℝ => ENNReal.ofReal |c + w| :=
    (continuous_abs.measurable.comp (measurable_const.add measurable_id)).ennreal_ofReal
  rw [(measurePreserving_eval Γ j).lintegral_comp hm]
  exact ((integrable_const c).add hint).abs.lintegral_lt_top.ne

/-- **Proposition 9.5.4, region (9.47)** `θ(M) > 1`: from far right the chain follows the last
linear model and `Xₙ ≥ θ(M)ⁿ(x − Σ_{k ≤ n} |φ(M) + W_k(M)|θ(M)^{−k})` escapes to `+∞`. -/
theorem proposition_9_5_4_47 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint : Integrable (fun w : ℝ => w) (Γ (Fin.last m))) (hθ : 1 < θ (Fin.last m)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  set L := Fin.last m
  set t := θ L
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  set μ := Measure.infinitePi fun _ : ℕ => Measure.pi Γ
  have ht0 : 0 < t := by linarith
  have hs : Summable fun k : ℕ => 1 / t ^ (k + 1) := by
    have := (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / t)
      ((div_lt_one ht0).2 hθ)).mul_left (1 / t)
    refine this.congr fun k => ?_
    rw [pow_succ, div_pow, one_pow]; field_simp
  have hbdd := ae_bdd_weighted_sum (Measure.pi Γ) (h := fun _ v => |φ L + v L|)
    (fun _ => continuous_abs.measurable.comp (measurable_const.add (measurable_pi_apply L)))
    (fun _ _ => abs_nonneg _) (setar_noise_lintegral_ne_top Γ hint (φ L)) (fun _ => le_rfl)
    (A := fun k => t ^ k) (fun k => pow_pos ht0 k) hs
  obtain ⟨k, hGm, hGpos⟩ := exists_measure_pos_forall_le μ
    (f := fun n ω => ∑ i ∈ Finset.range n, |φ L + ω (i + 1) L| / t ^ (i + 1))
    (fun n => Finset.measurable_sum _ fun i _ =>
      (continuous_abs.measurable.comp (measurable_const.add (measurable_noise (i + 1) L))).div_const
        _) hbdd
  refine setar_transient_of_escape Γ φ θ r h1 h2 (D := Ioi (ρ + k)) measurableSet_Ioi
    (by simp) hGm hGpos fun x hx ω hω n _ => ?_
  rw [mem_Ioi] at hx
  have hstep : ∀ n, ρ < orbit (setarStep φ θ r) x ω n →
      t * orbit (setarStep φ θ r) x ω n - |φ L + ω (n + 1) L| ≤
        orbit (setarStep φ θ r) x ω (n + 1) := fun n hn => by
    rw [orbit_succ, setarStep_of_gt φ θ r hn]
    linarith [neg_abs_le (φ L + ω (n + 1) L)]
  have hxk : ∀ n, ρ < 1 * (x - ∑ i ∈ Finset.range n, |φ L + ω (i + 1) L| / t ^ (i + 1)) :=
    fun n => by have := hω n; linarith
  have hesc := escape_of_lower_recursion (g := fun n => orbit (setarStep φ θ r) x ω n)
    (A := fun n => t ^ n) (lam := fun _ => t) (c := fun n => |φ L + ω n L|) (by linarith)
    one_pos (pow_zero t) (fun n => one_le_pow₀ hθ.le) (fun n => (pow_succ' t n).le)
    (fun _ => ht0.le) rfl hstep hxk n
  exact lt_of_lt_of_le hesc (le_abs_self _)

/-- **Proposition 9.5.4, region (9.46)** `θ(1) > 1`: the mirror image of (9.47), escaping to
`−∞` from far left. -/
theorem proposition_9_5_4_46 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint : Integrable (fun w : ℝ => w) (Γ 0)) (hθ : 1 < θ 0) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  set t := θ 0
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  set μ := Measure.infinitePi fun _ : ℕ => Measure.pi Γ
  have ht0 : 0 < t := by linarith
  have hs : Summable fun k : ℕ => 1 / t ^ (k + 1) := by
    have := (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / t)
      ((div_lt_one ht0).2 hθ)).mul_left (1 / t)
    refine this.congr fun k => ?_
    rw [pow_succ, div_pow, one_pow]; field_simp
  have hbdd := ae_bdd_weighted_sum (Measure.pi Γ) (h := fun _ v => |φ 0 + v 0|)
    (fun _ => continuous_abs.measurable.comp (measurable_const.add (measurable_pi_apply 0)))
    (fun _ _ => abs_nonneg _) (setar_noise_lintegral_ne_top Γ hint (φ 0)) (fun _ => le_rfl)
    (A := fun k => t ^ k) (fun k => pow_pos ht0 k) hs
  obtain ⟨k, hGm, hGpos⟩ := exists_measure_pos_forall_le μ
    (f := fun n ω => ∑ i ∈ Finset.range n, |φ 0 + ω (i + 1) 0| / t ^ (i + 1))
    (fun n => Finset.measurable_sum _ fun i _ =>
      (continuous_abs.measurable.comp (measurable_const.add (measurable_noise (i + 1) 0))).div_const
        _) hbdd
  refine setar_transient_of_escape Γ φ θ r h1 h2 (D := Iio (-(ρ + k))) measurableSet_Iio
    (by simp) hGm hGpos fun x hx ω hω n _ => ?_
  rw [mem_Iio] at hx
  have hstep : ∀ n, ρ < -orbit (setarStep φ θ r) x ω n →
      t * -orbit (setarStep φ θ r) x ω n - |φ 0 + ω (n + 1) 0| ≤
        -orbit (setarStep φ θ r) x ω (n + 1) := fun n hn => by
    rw [orbit_succ, setarStep_of_lt φ θ r (by linarith)]
    linarith [le_abs_self (φ 0 + ω (n + 1) 0)]
  have hxk : ∀ n, ρ < 1 * (-x - ∑ i ∈ Finset.range n, |φ 0 + ω (i + 1) 0| / t ^ (i + 1)) :=
    fun n => by have := hω n; linarith
  have hesc := escape_of_lower_recursion (g := fun n => -orbit (setarStep φ θ r) x ω n)
    (A := fun n => t ^ n) (lam := fun _ => t) (c := fun n => |φ 0 + ω n 0|) (by linarith)
    one_pos (pow_zero t) (fun n => one_le_pow₀ hθ.le) (fun n => (pow_succ' t n).le)
    (fun _ => ht0.le) rfl hstep hxk n
  exact lt_of_lt_of_le hesc (neg_le_abs _)

/-- An integrable regime noise is integrable as a coordinate of the noise vector. -/
theorem setar_integrable_noise {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] {j : Fin (m + 1)}
    (hint : Integrable (fun w : ℝ => w) (Γ j)) :
    Integrable (fun v : Fin (m + 1) → ℝ => v j) (Measure.pi Γ) :=
  ((measurePreserving_eval Γ j).integrable_comp aestronglyMeasurable_id).2 hint

/-- `E[W(j)]` computed on the noise vector. -/
theorem setar_integral_noise {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (j : Fin (m + 1)) :
    ∫ v, v j ∂Measure.pi Γ = ∫ w, w ∂Γ j := by
  have e := integral_map (μ := Measure.pi Γ) (φ := Function.eval j)
    (measurable_pi_apply j).aemeasurable (f := fun w : ℝ => w) aestronglyMeasurable_id
  rw [(measurePreserving_eval Γ j).map_eq] at e
  exact e.symm

/-- **Proposition 9.5.4, region (9.48)** `θ(1) = 1`, `φ(1) < 0`: from far left the chain is a
random walk with negative drift `φ(1)`, whose partial sums are a.s. bounded above (strong law);
it escapes to `−∞`. Only `θ(1) = 1`, `φ(1) < 0` and `E W(1) = 0` are used. -/
theorem proposition_9_5_4_48 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint : Integrable (fun w : ℝ => w) (Γ 0)) (hmean : ∫ w, w ∂Γ 0 = 0) (hθ : θ 0 = 1)
    (hφ : φ 0 < 0) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  set μ := Measure.infinitePi fun _ : ℕ => Measure.pi Γ
  have hcm : Measurable fun v : Fin (m + 1) → ℝ => φ 0 + v 0 :=
    measurable_const.add (measurable_pi_apply 0)
  have hci : Integrable (fun v : Fin (m + 1) → ℝ => φ 0 + v 0) (Measure.pi Γ) :=
    (integrable_const _).add (setar_integrable_noise Γ hint)
  have hneg : ∫ v, (φ 0 + v 0) ∂Measure.pi Γ < 0 := by
    rw [integral_add (integrable_const _) (setar_integrable_noise Γ hint), integral_const,
      setar_integral_noise, hmean]
    simpa using hφ
  have hbdd := ae_bdd_partialSum_of_neg (Measure.pi Γ) hcm hci hneg
  obtain ⟨k, hGm, hGpos⟩ := exists_measure_pos_forall_le μ
    (f := fun n ω => ∑ i ∈ Finset.range n, (φ 0 + ω (i + 1) 0))
    (fun n => Finset.measurable_sum _ fun i _ =>
      measurable_const.add (measurable_noise (i + 1) 0)) hbdd
  refine setar_transient_of_escape Γ φ θ r h1 h2 (D := Iio (-(ρ + k))) measurableSet_Iio
    (by simp) hGm hGpos fun x hx ω hω n _ => ?_
  rw [mem_Iio] at hx
  have hstep : ∀ n, ρ < -orbit (setarStep φ θ r) x ω n →
      1 * -orbit (setarStep φ θ r) x ω n - (φ 0 + ω (n + 1) 0) ≤
        -orbit (setarStep φ θ r) x ω (n + 1) := fun n hn => by
    rw [orbit_succ, setarStep_of_lt φ θ r (by linarith), hθ]
    linarith
  have hxk : ∀ n, ρ < 1 * (-x - ∑ i ∈ Finset.range n, (φ 0 + ω (i + 1) 0) / (1 : ℝ)) :=
    fun n => by have := hω n; simp only [div_one]; linarith
  have hesc := escape_of_lower_recursion (g := fun n => -orbit (setarStep φ θ r) x ω n)
    (A := fun _ => 1) (lam := fun _ => 1) (c := fun n => φ 0 + ω n 0) (by linarith)
    one_pos rfl (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => zero_le_one) rfl hstep hxk n
  exact lt_of_lt_of_le hesc (neg_le_abs _)

/-- **Proposition 9.5.4, region (9.49)** `θ(M) = 1`, `φ(M) > 0`: the mirror image of (9.48),
a random walk with positive drift escaping to `+∞`. -/
theorem proposition_9_5_4_49 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint : Integrable (fun w : ℝ => w) (Γ (Fin.last m))) (hmean : ∫ w, w ∂Γ (Fin.last m) = 0)
    (hθ : θ (Fin.last m) = 1) (hφ : 0 < φ (Fin.last m)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  set L := Fin.last m
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  set μ := Measure.infinitePi fun _ : ℕ => Measure.pi Γ
  have hcm : Measurable fun v : Fin (m + 1) → ℝ => -φ L - v L :=
    measurable_const.sub (measurable_pi_apply L)
  have hci : Integrable (fun v : Fin (m + 1) → ℝ => -φ L - v L) (Measure.pi Γ) :=
    (integrable_const _).sub (setar_integrable_noise Γ hint)
  have hneg : ∫ v, (-φ L - v L) ∂Measure.pi Γ < 0 := by
    rw [integral_sub (integrable_const _) (setar_integrable_noise Γ hint), integral_const,
      setar_integral_noise, hmean]
    simpa using hφ
  have hbdd := ae_bdd_partialSum_of_neg (Measure.pi Γ) hcm hci hneg
  obtain ⟨k, hGm, hGpos⟩ := exists_measure_pos_forall_le μ
    (f := fun n ω => ∑ i ∈ Finset.range n, (-φ L - ω (i + 1) L))
    (fun n => Finset.measurable_sum _ fun i _ =>
      measurable_const.sub (measurable_noise (i + 1) L)) hbdd
  refine setar_transient_of_escape Γ φ θ r h1 h2 (D := Ioi (ρ + k)) measurableSet_Ioi
    (by simp) hGm hGpos fun x hx ω hω n _ => ?_
  rw [mem_Ioi] at hx
  have hstep : ∀ n, ρ < orbit (setarStep φ θ r) x ω n →
      1 * orbit (setarStep φ θ r) x ω n - (-φ L - ω (n + 1) L) ≤
        orbit (setarStep φ θ r) x ω (n + 1) := fun n hn => by
    rw [orbit_succ, setarStep_of_gt φ θ r hn, hθ]
    linarith
  have hxk : ∀ n, ρ < 1 * (x - ∑ i ∈ Finset.range n, (-φ L - ω (i + 1) L) / (1 : ℝ)) :=
    fun n => by have := hω n; simp only [div_one]; linarith
  have hesc := escape_of_lower_recursion (g := fun n => orbit (setarStep φ θ r) x ω n)
    (A := fun _ => 1) (lam := fun _ => 1) (c := fun n => -φ L - ω n L) (by linarith)
    one_pos rfl (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => zero_le_one) rfl hstep hxk n
  exact lt_of_lt_of_le hesc (le_abs_self _)

/-- **Proposition 9.5.4, region (9.50)** `θ(1) < 0`, `θ(1)θ(M) > 1`: from far right the chain
alternates between the two end regimes with growing amplitude; the signed path
`(−1)ⁿXₙ` satisfies a linear lower recursion with multipliers `|θ(M)|, |θ(1)|, …`. -/
theorem proposition_9_5_4_50 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint0 : Integrable (fun w : ℝ => w) (Γ 0))
    (hintL : Integrable (fun w : ℝ => w) (Γ (Fin.last m))) (hθ0 : θ 0 < 0)
    (hθ : 1 < θ 0 * θ (Fin.last m)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  set L := Fin.last m
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  set μ := Measure.infinitePi fun _ : ℕ => Measure.pi Γ
  have hθL : θ L < 0 := by
    by_contra h; push Not at h; nlinarith
  set q := θ 0 * θ L
  have hq0 : 0 < q := by linarith
  have hL0 : 0 < |θ L| := abs_pos.2 hθL.ne
  have habs : |θ 0| * |θ L| = q := by rw [← abs_mul, abs_of_pos hq0]
  set a := min 1 |θ L|
  have ha : 0 < a := lt_min one_pos hL0
  set A : ℕ → ℝ := fun n => if Even n then q ^ (n / 2) else |θ L| * q ^ (n / 2)
  set lam : ℕ → ℝ := fun n => if Even n then |θ 0| else |θ L|
  set h : ℕ → (Fin (m + 1) → ℝ) → ℝ := fun n v => if Even n then |φ 0 + v 0| else |φ L + v L|
  have hApos : ∀ n, 0 < A n := fun n => by
    simp only [A]; split_ifs
    · exact pow_pos hq0 _
    · exact mul_pos hL0 (pow_pos hq0 _)
  have hA0 : A 0 = 1 := by simp [A]
  have hA : ∀ n, a ≤ A n := fun n => by
    simp only [A]; split_ifs
    · exact (min_le_left _ _).trans (one_le_pow₀ hθ.le)
    · exact (min_le_right _ _).trans (le_mul_of_one_le_right hL0.le (one_le_pow₀ hθ.le))
  have hAs : ∀ n, A (n + 1) ≤ lam (n + 1) * A n := by
    intro n
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have he : Even (j + j) := ⟨j, rfl⟩
      have ho : ¬ Even (j + j + 1) := Nat.not_even_iff_odd.2 ⟨j, by ring⟩
      simp only [A, lam, he, ho, ↓reduceIte]
      rw [show (j + j + 1) / 2 = j by omega, show (j + j) / 2 = j by omega]
    · have ho : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.2 ⟨j, rfl⟩
      have he : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
      simp only [A, lam, he, ho, ↓reduceIte]
      have e : |θ 0| * (|θ L| * q ^ j) = q ^ j * q := by rw [← mul_assoc, habs, mul_comm]
      rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1) / 2 = j by omega, pow_succ,
        e]
  have hlam : ∀ n, 0 ≤ lam (n + 1) := fun n => by
    simp only [lam]; split_ifs <;> exact abs_nonneg _
  have hs : Summable fun k => 1 / A (k + 1) := by
    have hg := summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / q)
      ((div_lt_one hq0).2 hθ)
    refine Summable.even_add_odd ?_ ?_
    · have e : (fun k => 1 / A (2 * k + 1)) = fun k => 1 / |θ L| * (1 / q) ^ k := by
        funext k
        have ho : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.2 ⟨k, rfl⟩
        simp only [A, ho, ↓reduceIte]
        rw [show (2 * k + 1) / 2 = k by omega, div_pow, one_pow]
        field_simp
      exact e ▸ hg.mul_left _
    · have e : (fun k => 1 / A (2 * k + 1 + 1)) = fun k => 1 / q * (1 / q) ^ k := by
        funext k
        have he : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
        simp only [A, he, ↓reduceIte]
        rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, div_pow, one_pow, pow_succ]
        field_simp
      exact e ▸ hg.mul_left _
  have hhm : ∀ k, Measurable (h k) := fun k => by
    by_cases hk : Even k
    · simp only [h, hk, ↓reduceIte]
      exact continuous_abs.measurable.comp (measurable_const.add (measurable_pi_apply _))
    · simp only [h, hk, ↓reduceIte]
      exact continuous_abs.measurable.comp (measurable_const.add (measurable_pi_apply _))
  have h0 : ∀ k v, 0 ≤ h k v := fun k v => by simp only [h]; split_ifs <;> exact abs_nonneg _
  have hM : ∫⁻ v, ENNReal.ofReal |φ 0 + v 0| ∂Measure.pi Γ +
      ∫⁻ v, ENNReal.ofReal |φ L + v L| ∂Measure.pi Γ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨setar_noise_lintegral_ne_top Γ hint0 _,
      setar_noise_lintegral_ne_top Γ hintL _⟩
  have hbound : ∀ k, ∫⁻ v, ENNReal.ofReal (h k v) ∂Measure.pi Γ ≤
      ∫⁻ v, ENNReal.ofReal |φ 0 + v 0| ∂Measure.pi Γ +
        ∫⁻ v, ENNReal.ofReal |φ L + v L| ∂Measure.pi Γ := fun k => by
    by_cases hk : Even k
    · simp only [h, hk, ↓reduceIte]; exact le_self_add
    · simp only [h, hk, ↓reduceIte]; exact le_add_self
  have hbdd := ae_bdd_weighted_sum (Measure.pi Γ) hhm h0 hM hbound hApos hs
  obtain ⟨k, hGm, hGpos⟩ := exists_measure_pos_forall_le μ
    (f := fun n ω => ∑ i ∈ Finset.range n, h (i + 1) (ω (i + 1)) / A (i + 1))
    (fun n => Finset.measurable_sum _ fun i _ =>
      ((hhm (i + 1)).comp (measurable_pi_apply (i + 1))).div_const _) hbdd
  refine setar_transient_of_escape Γ φ θ r h1 h2 (D := Ioi (ρ / a + k)) measurableSet_Ioi
    (by simp) hGm hGpos fun x hx ω hω n _ => ?_
  rw [mem_Ioi] at hx
  set g : ℕ → ℝ := fun n => (-1) ^ n * orbit (setarStep φ θ r) x ω n
  have hstep : ∀ n, ρ < g n → lam (n + 1) * g n - h (n + 1) (ω (n + 1)) ≤ g (n + 1) := by
    intro n hn
    rcases Nat.even_or_odd n with hn' | hn'
    · have ho : ¬ Even (n + 1) := Nat.not_even_iff_odd.2 hn'.add_one
      simp only [g, lam, h, ho, ↓reduceIte] at hn ⊢
      rw [hn'.neg_one_pow, one_mul] at hn
      rw [hn'.neg_one_pow, one_mul, hn'.add_one.neg_one_pow, orbit_succ,
        setarStep_of_gt φ θ r hn, abs_of_neg hθL]
      linarith [le_abs_self (φ L + ω (n + 1) L)]
    · have he : Even (n + 1) := hn'.add_one
      simp only [g, lam, h, he, ↓reduceIte] at hn ⊢
      rw [hn'.neg_one_pow] at hn
      rw [hn'.neg_one_pow, he.neg_one_pow, one_mul, orbit_succ,
        setarStep_of_lt φ θ r (by linarith), abs_of_neg hθ0]
      linarith [neg_abs_le (φ 0 + ω (n + 1) 0)]
  have hxk : ∀ n, ρ < a * (x - ∑ i ∈ Finset.range n, h (i + 1) (ω (i + 1)) / A (i + 1)) := by
    intro n
    have hk := hω n
    have : ρ / a < x - ∑ i ∈ Finset.range n, h (i + 1) (ω (i + 1)) / A (i + 1) := by
      linarith
    rw [div_lt_iff₀ ha] at this
    linarith
  have hesc := escape_of_lower_recursion (g := g) (A := A) (lam := lam)
    (c := fun n => h n (ω n)) (by linarith) ha hA0 hA hAs hlam (by simp [g]) hstep hxk n
  have habsg : |g n| = |orbit (setarStep φ θ r) x ω n| := by
    simp only [g]; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← habsg]
  exact lt_of_lt_of_le hesc (le_abs_self _)

/-- **Proposition 9.5.4, region (9.51)** `θ(1) < 0`, `θ(1)θ(M) = 1`, `φ(M) + θ(M)φ(1) < 0`: from
far right the two-step chain is a random walk `X₂ₙ = x + T_n` with drift
`d = φ(1) + θ(1)φ(M) > 0` (block strong law), while the odd steps
`X₂ₙ₊₁ = φ(M) − |θ(M)|X₂ₙ + W₂ₙ₊₁(M)` stay far left because `W₂ₙ₊₁(M)/n → 0`. -/
theorem proposition_9_5_4_51 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint0 : Integrable (fun w : ℝ => w) (Γ 0))
    (hintL : Integrable (fun w : ℝ => w) (Γ (Fin.last m))) (hmean0 : ∫ w, w ∂Γ 0 = 0)
    (hmeanL : ∫ w, w ∂Γ (Fin.last m) = 0) (hθ0 : θ 0 < 0)
    (hθ : θ 0 * θ (Fin.last m) = 1) (hφ : φ (Fin.last m) + θ (Fin.last m) * φ 0 < 0) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  set L := Fin.last m
  set ρ := setarBound r
  have hρ := one_le_setarBound r
  set μ := Measure.infinitePi fun _ : ℕ => Measure.pi Γ
  have hθL : θ L < 0 := by
    by_contra h; push Not at h; nlinarith
  have hL0 : 0 < |θ L| := abs_pos.2 hθL.ne
  have habsL : |θ L| = -θ L := abs_of_neg hθL
  set d := φ 0 + θ 0 * φ L
  have hdd : d = φ 0 + θ 0 * φ L := rfl
  have hd : 0 < d := by
    have h3 := mul_pos_of_neg_of_neg hθ0 hφ
    have e : θ 0 * (φ L + θ L * φ 0) = d := by linear_combination φ 0 * hθ
    linarith
  -- coordinates of the noise path
  have hIc : ∀ (i : ℕ) (j : Fin (m + 1)), Integrable (fun w : ℝ => w) (Γ j) →
      Integrable (fun ω : ℕ → Fin (m + 1) → ℝ => ω i j) μ := fun i j hj => by
    have h3 : Integrable (fun v : Fin (m + 1) → ℝ => v j) (μ.map fun ω => ω i) := by
      rw [Measure.infinitePi_map_eval]; exact setar_integrable_noise Γ hj
    exact (integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 h3
  have hIi : ∀ (i : ℕ) (j : Fin (m + 1)), ∫ ω, ω i j ∂μ = ∫ w, w ∂Γ j := fun i j => by
    have h3 := integral_map (μ := μ) (φ := fun ω => ω i) (measurable_pi_apply i).aemeasurable
      (f := fun v : Fin (m + 1) → ℝ => v j) (measurable_pi_apply j).aestronglyMeasurable
    rw [Measure.infinitePi_map_eval] at h3
    rw [← h3, setar_integral_noise]
  -- the two-step increments and the odd noises
  set ξ : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) → ℝ := fun p => d + θ 0 * p.1 L + p.2 0
  have hξm : Measurable ξ :=
    (measurable_const.add (((measurable_pi_apply L).comp measurable_fst).const_mul _)).add
      ((measurable_pi_apply 0).comp measurable_snd)
  have hξi : Integrable (fun ω : ℕ → Fin (m + 1) → ℝ => ξ (ω 1, ω 2)) μ :=
    ((integrable_const d).add ((hIc 1 L hintL).const_mul _)).add (hIc 2 0 hint0)
  have hEξ : ∫ ω, ξ (ω 1, ω 2) ∂μ = d := by
    have i3 : Integrable (fun ω : ℕ → Fin (m + 1) → ℝ => θ 0 * ω 1 L) μ :=
      (hIc 1 L hintL).const_mul _
    have i1 : Integrable (fun ω : ℕ → Fin (m + 1) → ℝ => d + θ 0 * ω 1 L) μ :=
      (integrable_const d).add i3
    have i2 : Integrable (fun ω : ℕ → Fin (m + 1) → ℝ => ω 2 0) μ := hIc 2 0 hint0
    simp only [ξ]
    rw [integral_add i1 i2, integral_add (integrable_const d) i3, integral_const,
      integral_const_mul, hIi, hIi, hmean0, hmeanL]
    simp
  have hY : Measurable fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) => p.1 L :=
    (measurable_pi_apply L).comp measurable_fst
  have hYi : Integrable (fun ω : ℕ → Fin (m + 1) → ℝ => (ω 1, ω 2).1 L) μ := hIc 1 L hintL
  have hEY : ∫ ω, (ω 1, ω 2).1 L ∂μ = 0 := by simp only; rw [hIi, hmeanL]
  have hT := ae_tendsto_blockSum (Measure.pi Γ) hξm hξi
  have hU := ae_tendsto_blockSum (Measure.pi Γ) hY hYi
  rw [hEξ] at hT
  rw [hEY] at hU
  set T : ℕ → (ℕ → Fin (m + 1) → ℝ) → ℝ := fun n ω =>
    ∑ i ∈ Finset.range n, ξ (ω (2 * i + 1), ω (2 * i + 2))
  have hTm : ∀ n, Measurable (T n) := fun n => Finset.measurable_sum _ fun i _ =>
    hξm.comp ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
  have hbdd : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ n,
      max (-T n ω) (ω (2 * n + 1) L - |θ L| * T n ω) ≤ B := by
    filter_upwards [hT, hU] with ω hTω hUω
    refine exists_bdd_of_eventually_nonpos ?_
    set ε := |θ L| * d / 8
    have hε : 0 < ε := by positivity
    set U : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ω (2 * i + 1) L
    have hUω' : Tendsto (fun n : ℕ => U n / n) atTop (𝓝 0) := hUω
    have e1 := hTω.eventually (lt_mem_nhds (by linarith : d / 2 < d))
    have e2 := hUω'.eventually (gt_mem_nhds hε)
    have e3 := hUω'.eventually (lt_mem_nhds (neg_lt_zero.2 hε))
    filter_upwards [e1, e2, e3, (tendsto_add_atTop_nat 1).eventually e2,
      eventually_ge_atTop 1] with n hT1 hUa hUb hUa' hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hTn : d / 2 * n < T n ω := (lt_div_iff₀ hnpos).1 hT1
    have hUn : -ε * n < U n := (lt_div_iff₀ hnpos).1 hUb
    have hUn1 : U (n + 1) < ε * (n + 1) := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).1 hUa'
      push_cast at this; exact this
    have hUs : U (n + 1) = U n + ω (2 * n + 1) L := Finset.sum_range_succ _ _
    have key : |θ L| * (d / 2 * n) < |θ L| * T n ω := mul_lt_mul_of_pos_left hTn hL0
    have hεn : ε * (n + 1) + ε * n ≤ |θ L| * (d / 2 * n) := by
      simp only [ε]
      nlinarith [mul_nonneg (mul_pos hL0 hd).le (by linarith : (0 : ℝ) ≤ 2 * n - 1)]
    have hdn : 0 < d / 2 * n := by positivity
    refine max_le (by linarith) ?_
    linarith
  obtain ⟨k, hGm, hGpos⟩ := exists_measure_pos_forall_le μ
    (f := fun n ω => max (-T n ω) (ω (2 * n + 1) L - |θ L| * T n ω))
    (fun n => ((hTm n).neg).max ((measurable_noise _ L).sub ((hTm n).const_mul _))) hbdd
  refine setar_transient_of_escape Γ φ θ r h1 h2
    (D := Ioi (max (ρ + k) ((ρ + k + |φ L|) / |θ L|))) measurableSet_Ioi
    (by simp) hGm hGpos fun x hx ω hω n hn => ?_
  rw [mem_Ioi, max_lt_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [div_lt_iff₀ hL0, habsL] at hx2
  have hk : ∀ n, -T n ω ≤ k ∧ ω (2 * n + 1) L + θ L * T n ω ≤ k := fun n => by
    have := max_le_iff.1 (hω n)
    rw [habsL] at this
    exact ⟨this.1, by linarith [this.2]⟩
  set o := orbit (setarStep φ θ r) x ω
  have hgt : ∀ n, o (2 * n) = x + T n ω → ρ < o (2 * n) := fun n h => by
    rw [h]; linarith [(hk n).1]
  have hodd : ∀ n, o (2 * n) = x + T n ω →
      o (2 * n + 1) = φ L + θ L * (x + T n ω) + ω (2 * n + 1) L := fun n h => by
    simp only [o]; rw [orbit_succ, setarStep_of_gt φ θ r (hgt n h)]; rw [h]
  have hlt : ∀ n, o (2 * n) = x + T n ω → o (2 * n + 1) < -ρ := fun n h => by
    rw [hodd n h, mul_add]
    have := (hk n).2
    have := le_abs_self (φ L)
    have e : x * -θ L = -(θ L * x) := by ring
    rw [e] at hx2
    linarith
  have claim : ∀ n, o (2 * n) = x + T n ω := by
    intro n
    induction n with
    | zero => simp [o, T]
    | succ n ih =>
      have hTs : T (n + 1) ω = T n ω + (d + θ 0 * ω (2 * n + 1) L + ω (2 * n + 2) 0) :=
        Finset.sum_range_succ _ _
      have hl := hlt n ih
      have ho := hodd n ih
      simp only [o] at hl ho ⊢
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, orbit_succ, setarStep_of_lt φ θ r hl, ho,
        hTs, show 2 * n + 1 + 1 = 2 * n + 2 by ring]
      linear_combination (x + T n ω) * hθ - hdd
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by ring]
    exact lt_of_lt_of_le (hgt j (claim j)) (le_abs_self _)
  · have := hlt j (claim j)
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

/-- **Proposition 9.5.4** (MT p. 222): the SETAR model is transient in the exterior of the
parameter space, i.e. under any of (9.46)–(9.51) (book indexing: regime `1` is `0`, regime `M`
is `Fin.last m`). Hypotheses: (SETAR2) as in Proposition 6.3.6 and zero-mean integrable noise
in the two end regimes; the book's (SETAR3) (finite variances) is not needed. -/
theorem proposition_9_5_4 {m : ℕ} (Γ : Fin (m + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (Γ j)] (φ θ : Fin (m + 1) → ℝ) (r : Fin m → ℝ)
    (h1 : ∀ j, Γ j ≪ volume) (h2 : ∀ j, volume ≪ Γ j)
    (hint0 : Integrable (fun w : ℝ => w) (Γ 0))
    (hintL : Integrable (fun w : ℝ => w) (Γ (Fin.last m))) (hmean0 : ∫ w, w ∂Γ 0 = 0)
    (hmeanL : ∫ w, w ∂Γ (Fin.last m) = 0)
    (hext : 1 < θ 0 ∨ 1 < θ (Fin.last m) ∨
      (θ 0 = 1 ∧ θ (Fin.last m) ≤ 1 ∧ φ 0 < 0) ∨
      (θ 0 ≤ 1 ∧ θ (Fin.last m) = 1 ∧ 0 < φ (Fin.last m)) ∨
      (θ 0 < 0 ∧ 1 < θ 0 * θ (Fin.last m)) ∨
      (θ 0 < 0 ∧ θ 0 * θ (Fin.last m) = 1 ∧ φ (Fin.last m) + θ (Fin.last m) * φ 0 < 0)) :
    haveI := isMarkovKernel_setarKernel Γ φ θ r
    IsTransientChain (setarKernel Γ φ θ r) volume := by
  rcases hext with h | h | ⟨h, -, h'⟩ | ⟨-, h, h'⟩ | ⟨h, h'⟩ | ⟨h, h', h''⟩
  · exact proposition_9_5_4_46 Γ φ θ r h1 h2 hint0 h
  · exact proposition_9_5_4_47 Γ φ θ r h1 h2 hintL h
  · exact proposition_9_5_4_48 Γ φ θ r h1 h2 hint0 hmean0 h h'
  · exact proposition_9_5_4_49 Γ φ θ r h1 h2 hintL hmeanL h h'
  · exact proposition_9_5_4_50 Γ φ θ r h1 h2 hint0 hintL h h'
  · exact proposition_9_5_4_51 Γ φ θ r h1 h2 hint0 hintL hmean0 hmeanL h h' h''

end MeynTweedie.HarrisRecurrence
