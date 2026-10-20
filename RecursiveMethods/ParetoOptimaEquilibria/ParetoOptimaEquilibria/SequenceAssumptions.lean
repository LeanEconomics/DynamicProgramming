/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ParetoOptimaEquilibria.SequencePrices

/-!
# Assumptions 15.6 and 15.7, and Exercise 15.10

SLP §15.4, p. 465. The commodity space is `S = BddSeq E` (bounded sequences in a real normed
space `E`), consumption sets `Xᵢ ⊆ S`, production sets `Yⱼ ⊆ S`.

* `SeqTruncClosed A`: `x ∈ A` implies `xᵀ ∈ A` for all `T` large enough.
  **Assumption 15.6** (`Assumption15_6`): every `Xᵢ` and every `Yⱼ` is `SeqTruncClosed`.
* `SeqTailInsensitive A v`: if `x, x′ ∈ A` and `v(x) > v(x′)` then `v(xᵀ) > v(x′)` for all `T` large
  enough (with `xᵀ ∈ A`). **Assumption 15.7** (`Assumption15_7`): every `(Xᵢ, uᵢ)` is
  `SeqTailInsensitive`.
* `SeqSemistrictQC A v`: one consumer's Assumption 15.2 (`assumption15_2_iff_seq`).
* `SeqTailInsensitive.of_tendsto`, `SeqTailInsensitive.of_liminf`: `v(xᵀ) → v(x)`, or just
  `liminf_T v(xᵀ) ≥ v(x)`, implies 15.7.
* **Exercise 15.10(a)** (`ex_15_10a`): for `C ⊆ E` convex with `0 ∈ C`, the set `seqSet C` of
  bounded sequences in `C` satisfies 15.1 and 15.6.
* **Exercise 15.10(b)** (`discountedUtility`, `u(x) = Σ_t βᵗ U(x_t)`): for `U` bounded on `C`,
  `u` satisfies 15.7 (`ex_15_10b_tail`), and 15.3 if `U` is continuous on `C`
  (`ex_15_10b_continuousOn`); with `U` concave, also 15.2 (`ex_15_10b`).
* **Exercise 15.10(c)** (`IsAggregator`, `IsAggregatorFixedPoint`, `seqShift`): a bounded
  continuous fixed point `u_W(x) = W(x₀, u_W(₁x))` of `T_W` satisfies 15.3 and 15.7 under
  (W1)–(W3) (`ex_15_10c_tail`), and 15.2 too when `W` is concave (`ex_15_10c`); since `W ≥ 0`,
  concavity already makes `W` increasing in its second argument
  (`seq_monotoneOn_of_concave_nonneg`), so (W4) is not needed.

**Corrections.**
* Exercise 15.10(b) is false for Assumption 15.2: `C = [0, 2]`, `U(c) = c²` (bounded,
  continuous, increasing, so 15.2 holds for `U` on `C`), `β = 1/2`, `x = (2, 0, 0, …)`,
  `x′ = (0, 2, 0, …)`: `u(x) = 4 > u(x′) = 2` but `u((x + x′)/2) = u(1, 1, 0, …) = 3/2`
  (`ex_15_10b_counterexample`). Concavity of `U` repairs it (`ex_15_10b`). Continuity of `U` is
  not needed for 15.7.
* Exercise 15.10(c) is false for Assumption 15.2 with an aggregator in the sense of §5.11
  ((W1)–(W3) only): `W(c, z) = min(c, 2)² + z/2` (`ex_15_10c_counterexample`). It is true if
  `W` is also concave, (W5) (`ex_15_10c`); the manual uses this silently via Exercise 5.11d.
  The transcription's NOTE asks for (W4) and (W5); (W5) alone suffices, because a nonnegative
  concave function on `[0, ∞)` is nondecreasing. Here `C ⊆ E` is any convex set containing `0`
  (the book: `C = ℝⁿ₊`), and the fixed point `u_W` is taken as given (any bounded, continuous,
  nonnegative fixed point, as in §5.11; its existence is Exercise 5.11d), not constructed.
* The manual's proof of 15.3 in (b) needs uniform continuity of `U`, which is not assumed; the
  proof here uses dominated convergence instead.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology
open scoped ENNReal

/-- One consumer's **Assumption 15.2** (semistrict quasi-concavity on `A`). -/
def SeqSemistrictQC {V : Type*} [AddCommGroup V] [Module ℝ V] (A : Set V) (v : V → ℝ) : Prop :=
  ∀ z ∈ A, ∀ z' ∈ A, v z' < v z → ∀ θ : ℝ, 0 < θ → θ < 1 → v z' < v (θ • z + (1 - θ) • z')

/-- Assumption 15.2 is `SeqSemistrictQC` for every consumer. -/
theorem assumption15_2_iff_seq {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι : Type*}
    (X : ι → Set S) (u : ι → S → ℝ) : Assumption15_2 X u ↔ ∀ i, SeqSemistrictQC (X i) (u i) :=
  Iff.rfl

/-- The concavity inequality implies `SeqSemistrictQC`. -/
theorem SeqSemistrictQC.of_concave {V : Type*} [AddCommGroup V] [Module ℝ V] {A : Set V}
    {v : V → ℝ}
    (h : ∀ z ∈ A, ∀ z' ∈ A, ∀ θ : ℝ, 0 < θ → θ < 1 →
      θ * v z + (1 - θ) * v z' ≤ v (θ • z + (1 - θ) • z')) : SeqSemistrictQC A v :=
  fun z hz z' hz' hlt θ h0 h1 => by
    have := h z hz z' hz' θ h0 h1
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `A` is closed under truncations far enough out (one set's part of Assumption 15.6). -/
def SeqTruncClosed (A : Set (BddSeq E)) : Prop := ∀ x ∈ A, ∀ᶠ T in atTop, seqTrunc T x ∈ A

/-- One consumer's **Assumption 15.7**: if `v(x) > v(x′)` then `v(xᵀ) > v(x′)` for all `T` large
enough (and such that `xᵀ ∈ A`, since `v` only matters on `A`). -/
def SeqTailInsensitive (A : Set (BddSeq E)) (v : BddSeq E → ℝ) : Prop :=
  ∀ x ∈ A, ∀ x' ∈ A, v x' < v x → ∀ᶠ T in atTop, seqTrunc T x ∈ A → v x' < v (seqTrunc T x)

/-- **Assumption 15.6** (p. 465): truncations of consumption and production plans far enough out
are again consumption and production plans. -/
def Assumption15_6 {ι κ : Type*} (X : ι → Set (BddSeq E)) (Y : κ → Set (BddSeq E)) : Prop :=
  (∀ i, SeqTruncClosed (X i)) ∧ ∀ j, SeqTruncClosed (Y j)

/-- **Assumption 15.7** (p. 465): sufficiently distant consumption matters little. -/
def Assumption15_7 {ι : Type*} (X : ι → Set (BddSeq E)) (u : ι → BddSeq E → ℝ) : Prop :=
  ∀ i, SeqTailInsensitive (X i) (u i)

/-- Under `SeqTruncClosed`, `SeqTailInsensitive` gives `v(xᵀ) > v(x′)` for all large `T`. -/
theorem SeqTailInsensitive.eventually {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    (hv : SeqTailInsensitive A v) (hA : SeqTruncClosed A) {x x' : BddSeq E} (hx : x ∈ A)
    (hx' : x' ∈ A) (hlt : v x' < v x) :
    ∀ᶠ T in atTop, seqTrunc T x ∈ A ∧ v x' < v (seqTrunc T x) :=
  ((hA x hx).and (hv x hx x' hx' hlt)).mono fun _ h => ⟨h.1, h.2 h.1⟩

/-- `liminf_T v(xᵀ) ≥ v(x)` (in the form `∀ c < v(x), eventually c < v(xᵀ)`) implies 15.7. -/
theorem SeqTailInsensitive.of_liminf {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    (h : ∀ x ∈ A, ∀ c < v x, ∀ᶠ T in atTop, c < v (seqTrunc T x)) : SeqTailInsensitive A v :=
  fun x hx _ _ hlt => (h x hx _ hlt).mono fun _ h' _ => h'

/-- `v(xᵀ) → v(x)` for every `x ∈ A` implies 15.7 (the "if" of Exercise 15.11(b)). -/
theorem SeqTailInsensitive.of_tendsto {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    (h : ∀ x ∈ A, Tendsto (fun T => v (seqTrunc T x)) atTop (𝓝 (v x))) : SeqTailInsensitive A v :=
  SeqTailInsensitive.of_liminf fun x hx _ hc => (h x hx).eventually (lt_mem_nhds hc)

/-! ### Exercise 15.10(a) -/

/-- The set `C × C × ⋯` of bounded sequences with every term in `C`. -/
def seqSet (C : Set E) : Set (BddSeq E) := {x | ∀ t, x t ∈ C}

/-- Coordinates of a linear combination. -/
theorem seq_coord_combo (a b : ℝ) (x y : BddSeq E) (t : ℕ) :
    (a • x + b • y) t = a • x t + b • y t := by
  rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul]; rfl

/-- `seqSet C` is convex when `C` is. -/
theorem convex_seqSet {C : Set E} (hC : Convex ℝ C) : Convex ℝ (seqSet C) :=
  fun x hx y hy a b ha hb hab t => by
    rw [seq_coord_combo]; exact hC (hx t) (hy t) ha hb hab

/-- Truncations of sequences in `C` stay in `C` when `0 ∈ C`. -/
theorem seqTrunc_mem_seqSet {C : Set E} (h0 : (0 : E) ∈ C) {x : BddSeq E} (hx : x ∈ seqSet C)
    (T : ℕ) : seqTrunc T x ∈ seqSet C := fun t => by
  rw [seqTrunc_apply]; split_ifs
  · exact hx t
  · exact h0

/-- **Exercise 15.10(a)**: `Xᵢ = C × C × ⋯` satisfies Assumptions 15.1 and 15.6. -/
theorem ex_15_10a {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    Convex ℝ (seqSet C) ∧ SeqTruncClosed (seqSet C) :=
  ⟨convex_seqSet hC, fun _ hx => Eventually.of_forall (seqTrunc_mem_seqSet h0 hx)⟩

/-! ### Exercise 15.10(b) -/

/-- The **discounted utility** `u(x) = Σ_t βᵗ U(x_t)`. -/
noncomputable def discountedUtility (β : ℝ) (U : E → ℝ) (x : BddSeq E) : ℝ :=
  ∑' t, β ^ t * U (x t)

omit [NormedSpace ℝ E] in
/-- The terms `βᵗ U(x_t)` are bounded by `M βᵗ` on `C × C × ⋯`. -/
theorem norm_discounted_term_le {β : ℝ} (hβ0 : 0 ≤ β) {C : Set E} {U : E → ℝ} {M : ℝ}
    (hU : ∀ c ∈ C, |U c| ≤ M) {x : BddSeq E} (hx : x ∈ seqSet C) (t : ℕ) :
    ‖β ^ t * U (x t)‖ ≤ M * β ^ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hU _ (hx t)) (pow_nonneg hβ0 t)

omit [NormedSpace ℝ E] in
/-- The discounted utility series converges on `C × C × ⋯`. -/
theorem summable_discounted {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} {U : E → ℝ}
    {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) {x : BddSeq E} (hx : x ∈ seqSet C) :
    Summable fun t => β ^ t * U (x t) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M)
    (norm_discounted_term_le hβ0 hU hx)

/-- For `U` bounded on `C ∋ 0`: `u(xᵀ) → u(x)` (dominated convergence). -/
theorem tendsto_discountedUtility_seqTrunc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E}
    (h0 : (0 : E) ∈ C) {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) {x : BddSeq E}
    (hx : x ∈ seqSet C) :
    Tendsto (fun T => discountedUtility β U (seqTrunc T x)) atTop
      (𝓝 (discountedUtility β U x)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) (fun t => ?_)
    (Eventually.of_forall fun T t => norm_discounted_term_le hβ0 hU (seqTrunc_mem_seqSet h0 hx T) t)
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop t).mono fun T hT => ?_)
  simp [seqTrunc_apply, hT]

/-- **Exercise 15.10(b)**, Assumption 15.7: for `U` bounded on `C ∋ 0` and `0 ≤ β < 1`, the
discounted utility satisfies 15.7. (Continuity of `U` is not needed.) -/
theorem ex_15_10b_tail {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} (h0 : (0 : E) ∈ C)
    {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) :
    SeqTailInsensitive (seqSet C) (discountedUtility β U) :=
  SeqTailInsensitive.of_tendsto fun _ hx => tendsto_discountedUtility_seqTrunc hβ0 hβ1 h0 hU hx

omit [NormedSpace ℝ E] in
/-- Evaluation at a coordinate is continuous on `BddSeq E`. -/
theorem continuous_seq_coord (t : ℕ) : Continuous fun y : BddSeq E => y t :=
  LipschitzWith.continuous (K := 1) <| LipschitzWith.of_dist_le_mul fun y z => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact norm_seq_coord_le _ t

omit [NormedSpace ℝ E] in
/-- **Exercise 15.10(b)**, Assumption 15.3: for `U` bounded and continuous on `C`, the
discounted utility is continuous on `C × C × ⋯` in the sup norm (dominated convergence; the
manual's argument needs uniform continuity of `U`). -/
theorem ex_15_10b_continuousOn {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} {U : E → ℝ}
    {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) (hUc : ContinuousOn U C) :
    ContinuousOn (discountedUtility β U) (seqSet C) := by
  intro x hx
  refine tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) (fun t => ?_)
    (eventually_nhdsWithin_of_forall fun y hy t => norm_discounted_term_le hβ0 hU hy t)
  refine tendsto_const_nhds.mul ((hUc (x t) (hx t)).tendsto.comp ?_)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => hy t⟩
  exact ((continuous_seq_coord t).tendsto x).mono_left nhdsWithin_le_nhds

/-- The concavity inequality for the discounted utility of a concave `U`. -/
theorem discountedUtility_concave {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E}
    {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) (hUcv : ConcaveOn ℝ C U) {x x' : BddSeq E}
    (hx : x ∈ seqSet C) (hx' : x' ∈ seqSet C) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * discountedUtility β U x + (1 - θ) * discountedUtility β U x' ≤
      discountedUtility β U (θ • x + (1 - θ) • x') := by
  have hmem : θ • x + (1 - θ) • x' ∈ seqSet C :=
    convex_seqSet hUcv.1 hx hx' h0 (by linarith) (by ring)
  have hs := summable_discounted hβ0 hβ1 hU hx
  have hs' := summable_discounted hβ0 hβ1 hU hx'
  unfold discountedUtility
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hs.mul_left θ).tsum_add (hs'.mul_left (1 - θ))]
  refine ((hs.mul_left θ).add (hs'.mul_left (1 - θ))).tsum_le_tsum (fun t => ?_)
    (summable_discounted hβ0 hβ1 hU hmem)
  have hc := hUcv.2 (hx t) (hx' t) h0 (by linarith : 0 ≤ 1 - θ) (by ring)
  rw [seq_coord_combo]
  simp only [smul_eq_mul] at hc
  have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
  nlinarith [mul_le_mul_of_nonneg_left hc hb]

/-- **Exercise 15.10(b)**, corrected: for `U` bounded, continuous and **concave** on a set
`C ∋ 0`, and `0 ≤ β < 1`, the discounted utility satisfies Assumptions 15.2, 15.3 and 15.7. -/
theorem ex_15_10b {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} (h0 : (0 : E) ∈ C)
    {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) (hUc : ContinuousOn U C)
    (hUcv : ConcaveOn ℝ C U) :
    SeqSemistrictQC (seqSet C) (discountedUtility β U) ∧
      ContinuousOn (discountedUtility β U) (seqSet C) ∧
      SeqTailInsensitive (seqSet C) (discountedUtility β U) :=
  ⟨SeqSemistrictQC.of_concave fun _ hx _ hx' _ h0' h1' =>
      discountedUtility_concave hβ0 hβ1 hU hUcv hx hx' h0'.le h1'.le,
    ex_15_10b_continuousOn hβ0 hβ1 hU hUc, ex_15_10b_tail hβ0 hβ1 h0 hU⟩

/-- The utilities of `x = (2, 0, 0, …)`, `x′ = (0, 2, 0, …)` and `(x + x′)/2 = (1, 1, 0, …)` for
`β = 1/2` and any `U` with `U(0) = 0`. -/
theorem discountedUtility_half_values (U : ℝ → ℝ) (hU0 : U 0 = 0) :
    discountedUtility (1 / 2) U (lp.single ∞ 0 2) = U 2 ∧
    discountedUtility (1 / 2) U (lp.single ∞ 1 2) = U 2 / 2 ∧
    discountedUtility (1 / 2) U ((1 / 2 : ℝ) • lp.single ∞ 0 2 +
      (1 - 1 / 2 : ℝ) • lp.single ∞ 1 2) = U 1 + U 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold discountedUtility
    rw [tsum_eq_single 0]
    · simp
    · intro t ht; simp [ht, hU0]
  · unfold discountedUtility
    rw [tsum_eq_single 1]
    · simp; ring
    · intro t ht; simp [ht, hU0]
  · unfold discountedUtility
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [seq_coord_combo, Finset.sum_range_succ, Pi.single_apply]; ring_nf
    · intro t ht
      have h0 : t ≠ 0 := fun h => ht (by simp [h])
      have h1 : t ≠ 1 := fun h => ht (by simp [h])
      simp [seq_coord_combo, h0, h1, hU0]

/-- **Exercise 15.10(b) is false for Assumption 15.2.** With `C = [0, 2]`, `U(c) = c²` (bounded
and continuous on `C`, and satisfying 15.2 on `C`) and `β = 1/2`, the discounted utility does not
satisfy 15.2. -/
theorem ex_15_10b_counterexample :
    (∀ c ∈ Set.Icc (0 : ℝ) 2, |c ^ 2| ≤ 4) ∧ ContinuousOn (fun c : ℝ => c ^ 2) (Set.Icc 0 2) ∧
    SeqSemistrictQC (Set.Icc (0 : ℝ) 2) (fun c => c ^ 2) ∧
    ¬ SeqSemistrictQC (seqSet (Set.Icc (0 : ℝ) 2)) (discountedUtility (1 / 2) fun c => c ^ 2) := by
  refine ⟨fun c hc => ?_, (continuous_pow 2).continuousOn, fun c hc c' hc' hlt θ h0 h1 => ?_,
    fun h => ?_⟩
  · rw [abs_of_nonneg (sq_nonneg c)]; nlinarith [hc.1, hc.2]
  · have hcc : c' < c := lt_of_pow_lt_pow_left₀ 2 hc.1 hlt
    have : c' < θ • c + (1 - θ) • c' := by simp only [smul_eq_mul]; nlinarith
    exact pow_lt_pow_left₀ this hc'.1 two_ne_zero
  · obtain ⟨h1, h2, h3⟩ := discountedUtility_half_values (fun c : ℝ => c ^ 2) (by norm_num)
    have hx : (lp.single ∞ 0 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Icc (0 : ℝ) 2) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have hx' : (lp.single ∞ 1 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Icc (0 : ℝ) 2) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have := h _ hx _ hx' (by rw [h1, h2]; norm_num) (1 / 2) (by norm_num) (by norm_num)
    rw [h2, h3] at this
    norm_num at this

/-! ### Exercise 15.10(c) -/

/-- The **seqShift** `₁x = (x₁, x₂, …)`. -/
noncomputable def seqShift : BddSeq E →L[ℝ] BddSeq E :=
  LinearMap.mkContinuous
    { toFun := fun x => BddSeq.mk (fun t => x (t + 1)) ‖x‖ fun t => norm_seq_coord_le x _
      map_add' := fun x y => by ext t; simp
      map_smul' := fun c x => by ext t; simp }
    1 fun x => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg x) fun t => norm_seq_coord_le x _

/-- Coordinates of the seqShift. -/
theorem seqShift_apply (x : BddSeq E) (t : ℕ) : seqShift x t = x (t + 1) := rfl

/-- Shifting a truncation: `₁(x^{T+1}) = (₁x)ᵀ`. -/
theorem seqShift_seqTrunc_succ (T : ℕ) (x : BddSeq E) :
    seqShift (seqTrunc (T + 1) x) = seqTrunc T (seqShift x) := by
  ext t
  simp only [seqShift_apply, seqTrunc_apply]
  split_ifs <;> first | rfl | omega

/-- The seqShift maps `C × C × ⋯` into itself. -/
theorem seqShift_mem_seqSet {C : Set E} {x : BddSeq E} (hx : x ∈ seqSet C) :
    seqShift x ∈ seqSet C :=
  fun t => hx (t + 1)

/-- An **aggregator function** on `C × ℝ₊` in the sense of §5.11 (pp. 114–116): continuous,
nonnegative, (W1) `W(0, 0) = 0`, (W2) `W(·, z)` bounded on `C`, (W3) `W` is a contraction of
modulus `β ∈ (0, 1)` in `z`. -/
structure IsAggregator (C : Set E) (W : E → ℝ → ℝ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  continuousOn : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (C ×ˢ Set.Ici 0)
  zero : W 0 0 = 0
  bounded : ∀ z : ℝ, 0 ≤ z → ∃ B, ∀ c ∈ C, |W c z| ≤ B
  nonneg : ∀ c ∈ C, ∀ z : ℝ, 0 ≤ z → 0 ≤ W c z
  lipschitz : ∀ c ∈ C, ∀ z : ℝ, 0 ≤ z → ∀ z' : ℝ, 0 ≤ z' → |W c z - W c z'| ≤ β * |z - z'|

/-- `v` is a **fixed point of `T_W`** in the space of §5.11: bounded, continuous (sup norm) and
nonnegative on `C × C × ⋯`, with `v(x) = W(x₀, v(₁x))`. -/
structure IsAggregatorFixedPoint (C : Set E) (W : E → ℝ → ℝ) (v : BddSeq E → ℝ) : Prop where
  bounded : ∃ B, ∀ x ∈ seqSet C, |v x| ≤ B
  continuousOn : ContinuousOn v (seqSet C)
  nonneg : ∀ x ∈ seqSet C, 0 ≤ v x
  fixed : ∀ x ∈ seqSet C, v x = W (x 0) (v (seqShift x))

/-- The truncation bound of Exercise 5.11d: `|v(x) − v(xᵀ)| ≤ 2Bβᵀ`. -/
theorem aggregator_seqTrunc_bound {C : Set E} (h0 : (0 : E) ∈ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β) {v : BddSeq E → ℝ} (hv : IsAggregatorFixedPoint C W v) {B : ℝ}
    (hB : ∀ x ∈ seqSet C, |v x| ≤ B) (T : ℕ) :
    ∀ x ∈ seqSet C, |v x - v (seqTrunc T x)| ≤ 2 * B * β ^ T := by
  induction T with
  | zero =>
    intro x hx
    have h1 := hB x hx
    have h2 := hB _ (seqTrunc_mem_seqSet h0 hx 0)
    rw [pow_zero, mul_one]
    calc |v x - v (seqTrunc 0 x)| ≤ |v x| + |v (seqTrunc 0 x)| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  | succ T ih =>
    intro x hx
    have htx := seqTrunc_mem_seqSet h0 hx (T + 1)
    have hsx := seqShift_mem_seqSet hx
    rw [hv.fixed x hx, hv.fixed _ htx, seqShift_seqTrunc_succ]
    have h00 : seqTrunc (T + 1) x 0 = x 0 := by simp [seqTrunc_apply]
    rw [h00]
    calc |W (x 0) (v (seqShift x)) - W (x 0) (v (seqTrunc T (seqShift x)))|
        ≤ β * |v (seqShift x) - v (seqTrunc T (seqShift x))| :=
          hW.lipschitz _ (hx 0) _ (hv.nonneg _ hsx) _
            (hv.nonneg _ (seqTrunc_mem_seqSet h0 hsx T))
      _ ≤ β * (2 * B * β ^ T) := mul_le_mul_of_nonneg_left (ih _ hsx) hW.beta_pos.le
      _ = 2 * B * β ^ (T + 1) := by ring

/-- **Exercise 15.10(c)**, Assumptions 15.3 and 15.7, under (W1)–(W3) only. -/
theorem ex_15_10c_tail {C : Set E} (h0 : (0 : E) ∈ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β) {v : BddSeq E → ℝ} (hv : IsAggregatorFixedPoint C W v) :
    ContinuousOn v (seqSet C) ∧ SeqTailInsensitive (seqSet C) v := by
  refine ⟨hv.continuousOn, SeqTailInsensitive.of_tendsto fun x hx => ?_⟩
  obtain ⟨B, hB⟩ := hv.bounded
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_)
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hW.beta_pos.le
      hW.beta_lt_one).const_mul (2 * B))
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact aggregator_seqTrunc_bound h0 hW hv hB T x hx

/-- A nonnegative concave function on `[0, ∞)` is nondecreasing. -/
theorem seq_monotoneOn_of_concave_nonneg {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (h0 : ∀ z, 0 ≤ z → 0 ≤ f z) : MonotoneOn f (Set.Ici 0) := by
  intro a ha b hb hab
  rcases hab.lt_or_eq with hlt | rfl
  · by_contra hgt
    have hgt' : f b < f a := not_le.1 hgt
    have hfb := h0 b (Set.mem_Ici.1 hb)
    -- go far beyond `b`, where the chord through `a`, `b` forces `f < 0`
    set z := b + (f b + 1) * (b - a) / (f a - f b) with hz
    have hpos : 0 < (f b + 1) * (b - a) / (f a - f b) :=
      div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have hbz : b < z := by rw [hz]; linarith
    have hz0 : 0 ≤ z := by linarith [Set.mem_Ici.1 hb]
    have hadj := hf.slope_anti_adjacent ha (Set.mem_Ici.2 hz0) hlt hbz
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at hadj
    have hzb : z - b = (f b + 1) * (b - a) / (f a - f b) := by rw [hz]; ring
    rw [hzb] at hadj
    have hne : f a - f b ≠ 0 := (sub_pos.2 hgt').ne'
    have key : (f b - f a) * ((f b + 1) * (b - a) / (f a - f b)) = -((f b + 1) * (b - a)) := by
      field_simp
      ring
    have hfz := h0 z hz0
    nlinarith
  · exact le_rfl

/-- `W(c, ·)` is nondecreasing on `ℝ₊` when `W` is a concave aggregator. -/
theorem aggregator_monotone {C : Set E} {W : E → ℝ → ℝ} {β : ℝ} (hW : IsAggregator C W β)
    (hW5 : ConcaveOn ℝ (C ×ˢ Set.Ici 0) fun p : E × ℝ => W p.1 p.2) {c : E} (hc : c ∈ C) :
    MonotoneOn (W c) (Set.Ici 0) := by
  refine seq_monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
    (hW.nonneg c hc)
  have h := hW5.2 (x := (c, z)) (y := (c, z')) ⟨hc, hz⟩ ⟨hc, hz'⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk] at h
  rwa [Convex.combo_self hab] at h

/-- The concavity inequality for `v`, up to `4Bβᵏ`, by induction on `k`. -/
theorem aggregator_concave_approx {C : Set E} (hC : Convex ℝ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β)
    (hW5 : ConcaveOn ℝ (C ×ˢ Set.Ici 0) fun p : E × ℝ => W p.1 p.2) {v : BddSeq E → ℝ}
    (hv : IsAggregatorFixedPoint C W v) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ seqSet C, |v x| ≤ B) (k : ℕ) :
    ∀ x ∈ seqSet C, ∀ x' ∈ seqSet C, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ * v x + (1 - θ) * v x' - 4 * B * β ^ k ≤ v (θ • x + (1 - θ) • x') := by
  induction k with
  | zero =>
    intro x hx x' hx' θ h0 h1
    have hm := convex_seqSet hC hx hx' h0 (by linarith : 0 ≤ 1 - θ) (by ring)
    have e1 := abs_le.1 (hB x hx)
    have e2 := abs_le.1 (hB x' hx')
    have e3 := abs_le.1 (hB _ hm)
    nlinarith
  | succ k ih =>
    intro x hx x' hx' θ h0 h1
    have h1θ : 0 ≤ 1 - θ := by linarith
    have hm := convex_seqSet hC hx hx' h0 h1θ (by ring)
    have hsx := seqShift_mem_seqSet hx
    have hsx' := seqShift_mem_seqSet hx'
    set c := θ • x 0 + (1 - θ) • x' 0 with hc
    set z := θ * v (seqShift x) + (1 - θ) * v (seqShift x') with hz
    set w := v (seqShift (θ • x + (1 - θ) • x')) with hw
    have hshift : seqShift (θ • x + (1 - θ) • x') = θ • seqShift x + (1 - θ) • seqShift x' := by
      rw [map_add, map_smul, map_smul]
    have hwz : z - 4 * B * β ^ k ≤ w := by
      rw [hw, hshift]; exact ih _ hsx _ hsx' θ h0 h1
    have hcC : c ∈ C := hC (hx 0) (hx' 0) h0 h1θ (by ring)
    have hz0 : 0 ≤ z := by
      have := hv.nonneg _ hsx; have := hv.nonneg _ hsx'; positivity
    have hw0 : 0 ≤ w := hv.nonneg _ (seqShift_mem_seqSet hm)
    have hWw : W c z - β * (4 * B * β ^ k) ≤ W c w := by
      rcases le_total z w with hle | hle
      · have := aggregator_monotone hW hW5 hcC hz0 hw0 hle
        have : 0 ≤ β * (4 * B * β ^ k) := by
          have := hW.beta_pos.le; positivity
        linarith
      · have hl := hW.lipschitz c hcC z hz0 w hw0
        rw [abs_of_nonneg (sub_nonneg.2 hle)] at hl
        have h2 := (abs_le.1 hl).2
        have h3 := mul_le_mul_of_nonneg_left (show z - w ≤ 4 * B * β ^ k by linarith)
          hW.beta_pos.le
        linarith
    have hcv := hW5.2 (x := (x 0, v (seqShift x))) (y := (x' 0, v (seqShift x')))
      ⟨hx 0, hv.nonneg _ hsx⟩ ⟨hx' 0, hv.nonneg _ hsx'⟩ h0 h1θ (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hcv
    have hvm : v (θ • x + (1 - θ) • x') = W c w := by
      rw [hv.fixed _ hm, seq_coord_combo]
    rw [hvm, hv.fixed x hx, hv.fixed x' hx']
    have : W c z = W (θ • x 0 + (1 - θ) • x' 0) (θ * v (seqShift x) + (1 - θ) * v (seqShift x')) :=
      rfl
    rw [pow_succ]
    nlinarith

/-- **Exercise 15.10(c)**, corrected: if the aggregator `W` is also concave on `C × ℝ₊`
(property (W5) of §5.11, used silently by the manual via Exercise 5.11d; (W4) is not needed), the
fixed point `u_W` satisfies Assumptions 15.2, 15.3 and 15.7. -/
theorem ex_15_10c {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β)
    (hW5 : ConcaveOn ℝ (C ×ˢ Set.Ici 0) fun p : E × ℝ => W p.1 p.2) {v : BddSeq E → ℝ}
    (hv : IsAggregatorFixedPoint C W v) :
    SeqSemistrictQC (seqSet C) v ∧ ContinuousOn v (seqSet C) ∧ SeqTailInsensitive (seqSet C) v := by
  refine ⟨SeqSemistrictQC.of_concave fun x hx x' hx' θ h0' h1' => ?_, ex_15_10c_tail h0 hW hv⟩
  obtain ⟨B, hB⟩ := hv.bounded
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x hx)
  have hlim : Tendsto (fun k : ℕ => θ * v x + (1 - θ) * v x' - 4 * B * β ^ k) atTop
      (𝓝 (θ * v x + (1 - θ) * v x')) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hW.beta_pos.le
      hW.beta_lt_one).const_mul (4 * B)).const_sub (θ * v x + (1 - θ) * v x')
  exact le_of_tendsto' hlim
    fun k => aggregator_concave_approx hC hW hW5 hv hB0 hB k x hx x' hx' θ h0'.le h1'.le

/-- **Exercise 15.10(c) is false for Assumption 15.2** with an aggregator in the sense of §5.11
((W1)–(W3) only): on `C = ℝ₊`, `W(c, z) = min(c, 2)² + z/2` is an aggregator with modulus `1/2`,
`u_W(x) = Σ_t (1/2)ᵗ min(x_t, 2)²` is its bounded continuous fixed point, and `u_W` violates 15.2
at `x = (2, 0, …)`, `x′ = (0, 2, 0, …)`, `θ = 1/2`. -/
theorem ex_15_10c_counterexample :
    IsAggregator (Set.Ici (0 : ℝ)) (fun c z => min c 2 ^ 2 + z / 2) (1 / 2) ∧
    IsAggregatorFixedPoint (Set.Ici (0 : ℝ)) (fun c z => min c 2 ^ 2 + z / 2)
      (discountedUtility (1 / 2) fun c => min c 2 ^ 2) ∧
    ¬ SeqSemistrictQC (seqSet (Set.Ici (0 : ℝ)))
      (discountedUtility (1 / 2) fun c => min c 2 ^ 2) := by
  have hU : ∀ c ∈ Set.Ici (0 : ℝ), |min c 2 ^ 2| ≤ 4 := fun c hc => by
    have h1 : 0 ≤ min c 2 := le_min hc (by norm_num)
    have h2 : min c 2 ≤ 2 := min_le_right _ _
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hβ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hβ1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨⟨by norm_num, by norm_num, ?_, by norm_num, fun z _ => ⟨4 + |z / 2|, fun c hc => ?_⟩,
    fun c hc z hz => by positivity, fun c _ z _ z' _ => ?_⟩, ⟨⟨8, fun x hx => ?_⟩, ?_,
    fun x hx => ?_, fun x hx => ?_⟩, fun h => ?_⟩
  · exact (((continuous_fst.min continuous_const).pow 2).add
      (continuous_snd.div_const 2)).continuousOn
  · exact (abs_add_le _ _).trans (by linarith [hU c hc])
  · rw [show min c 2 ^ 2 + z / 2 - (min c 2 ^ 2 + z' / 2) = (1 / 2) * (z - z') by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  · have hs := summable_discounted hβ0 hβ1 hU hx
    have h := norm_tsum_le_tsum_norm hs.norm
    refine h.trans ?_
    calc ∑' t, ‖(1 / 2 : ℝ) ^ t * min (x t) 2 ^ 2‖ ≤ ∑' t, 4 * (1 / 2 : ℝ) ^ t :=
          hs.norm.tsum_le_tsum (norm_discounted_term_le hβ0 hU hx)
            ((summable_geometric_of_lt_one hβ0 hβ1).mul_left 4)
      _ = 8 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  · exact ex_15_10b_continuousOn hβ0 hβ1 hU
      ((continuous_id.min continuous_const).pow 2).continuousOn
  · exact tsum_nonneg fun t => by positivity
  · have hs := summable_discounted hβ0 hβ1 hU hx
    unfold discountedUtility
    have e : ∑' b, (1 / 2 : ℝ) ^ (b + 1) * min (x (b + 1)) 2 ^ 2 =
        (∑' t, (1 / 2 : ℝ) ^ t * min (seqShift x t) 2 ^ 2) / 2 := by
      rw [← tsum_div_const]
      exact tsum_congr fun b => by rw [seqShift_apply]; ring
    rw [hs.tsum_eq_zero_add, e, pow_zero, one_mul]
  · obtain ⟨h1, h2, h3⟩ := discountedUtility_half_values (fun c : ℝ => min c 2 ^ 2)
      (by norm_num)
    have hx : (lp.single ∞ 0 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Ici (0 : ℝ)) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have hx' : (lp.single ∞ 1 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Ici (0 : ℝ)) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have := h _ hx _ hx' (by rw [h1, h2]; norm_num) (1 / 2) (by norm_num) (by norm_num)
    rw [h2, h3] at this
    norm_num at this

end StokeyLucasPrescott.ParetoOptimaEquilibria
