/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.Concavity

/-!
# Recursive preferences

SLP §5.11, pp. 114–116. `L` is the space of bounded sequences `c = (c₀, c₁, …)` in `ℝˡ₊` with the
sup norm (`Seq l`; on `ℝˡ` Lean's norm is the max norm, equivalent to the book's Euclidean
norm), and `S = C(L)` is the space of bounded continuous `u : L → ℝ`. `₁c = (c₁, c₂, …)` is the
shift (`shiftSeq`) and `cⁿ = (c₀, …, cₙ, 0, 0, …)` the truncation (`trunc`).

* **Exercise 5.11a, c** (`ex_5_11a`, `ex_5_11c`): `(Tu)(c) = U(c₀) + βu(₁c)` is a contraction on
  `S`, and its fixed point is `û(c) = Σ βᵗU(c_t)`; so `û` is bounded (by `M/(1 − β)`) and
  continuous.
* **Exercise 5.11b**: `S` is complete (`ex_5_11b_complete`); but `u(cⁿ) → u(c)` fails for some
  `u ∈ S` (`ex_5_11b_counterexample`: `u(c) = min{1, dist(c, sequences that are eventually 0)}`
  has `u(1) = 1` and `u(1ⁿ) = 0`). The manual's example `inf_t c_t` is not bounded, so it is not
  in `S`.
* **Exercise 5.11d** (`ex_5_11d`): for an aggregator `W` with (W1)–(W3), `T_W u(c) = W[c₀, u(₁c)]`
  has a unique fixed point `u_W`, with `|u_W(c) − u_W(cⁿ)| ≤ βⁿ⁺¹‖u_W‖ ≤ βⁿ‖u_W‖`; (W4) makes `u_W`
  increasing (`ex_5_11d_mono`); (W5) makes it concave (`ex_5_11d_concave`). For (W5) monotonicity
  of `W` is not needed: a nonnegative concave function on `[0, ∞)` is nondecreasing
  (`monotoneOn_of_concave_nonneg`).
* **Exercise 5.11e** (`ex_5_11e`): raising `c_{it}` by `h ≥ 0` changes utility at the rate
  `[∏_{s < t} W_z(c_s, u_W(ₛ₊₁c))] · W_{x_i}(c_t, u_W(ₜ₊₁c))`. The marginal rate of substitution
  between `c_{it}` and `c_{j,t+k}` is the ratio of two such rates, with the product
  `∏_{s=t}^{t+k−1} W_z(c_s, u_W(ₛ₊₁c))`; the manual's formula keeps a single `W_z` factor.
-/

open Set Filter Topology BoundedContinuousFunction

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ}

/-- The set of bounded sequences in `ℝˡ₊`. -/
def seqSet (l : ℕ) : Set (ℕ →ᵇ (Fin l → ℝ)) := {c | ∀ t, 0 ≤ c t}

/-- `L`: bounded sequences in `ℝˡ₊`. -/
abbrev Seq (l : ℕ) := ↥(seqSet l)

theorem convex_seqSet : Convex ℝ (seqSet l) := fun c hc c' hc' a b ha hb _ t => by
  simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.coe_smul]
  exact add_nonneg (smul_nonneg ha (hc t)) (smul_nonneg hb (hc' t))

/-- The shift `₁c = (c₁, c₂, …)`. -/
def shiftSeq (c : Seq l) : Seq l :=
  ⟨c.1.compContinuous ⟨fun t => t + 1, continuous_of_discreteTopology⟩, fun t => c.2 (t + 1)⟩

@[simp] theorem shiftSeq_apply (c : Seq l) (t : ℕ) : (shiftSeq c).1 t = c.1 (t + 1) := rfl

theorem continuous_shiftSeq : Continuous (shiftSeq (l := l)) := by
  refine (LipschitzWith.of_dist_le' (K := 1) fun c c' => ?_).continuous
  rw [one_mul]
  change dist (shiftSeq c).1 (shiftSeq c').1 ≤ dist c.1 c'.1
  exact (dist_le dist_nonneg).2 fun t => dist_coe_le_dist (t + 1)

theorem continuous_head : Continuous fun c : Seq l => c.1 0 :=
  (continuous_eval_const 0).comp continuous_subtype_val

theorem abs_apply_le_norm (u : Seq l →ᵇ ℝ) (c : Seq l) : |u c| ≤ ‖u‖ := by
  simpa [Real.norm_eq_abs] using u.norm_coe_le_norm c

/-- The zero sequence. -/
def zeroSeq : Seq l := ⟨0, fun _ => le_rfl⟩

theorem shiftSeq_zero : shiftSeq (zeroSeq (l := l)) = zeroSeq := Subtype.ext (by ext; rfl)

/-- The truncation `cⁿ = (c₀, …, cₙ, 0, 0, …)`. -/
noncomputable def trunc (n : ℕ) (c : Seq l) : Seq l :=
  ⟨BoundedContinuousFunction.mkOfDiscrete (fun t => if t ≤ n then c.1 t else 0) (2 * ‖c.1‖)
    fun s t => by
      have h0 : ∀ u, ‖(if u ≤ n then c.1 u else 0)‖ ≤ ‖c.1‖ := fun u => by
        split_ifs
        · exact c.1.norm_coe_le_norm u
        · simp
      exact (dist_le_norm_add_norm _ _).trans (by linarith [h0 s, h0 t]),
    fun t => by
      change 0 ≤ (if t ≤ n then c.1 t else 0)
      split_ifs
      · exact c.2 t
      · exact le_rfl⟩

theorem trunc_apply (n : ℕ) (c : Seq l) (t : ℕ) :
    (trunc n c).1 t = if t ≤ n then c.1 t else 0 := rfl

theorem head_trunc (n : ℕ) (c : Seq l) : (trunc n c).1 0 = c.1 0 := by
  simp [trunc_apply]

theorem shiftSeq_trunc_zero (c : Seq l) : shiftSeq (trunc 0 c) = zeroSeq :=
  Subtype.ext (by ext t i; simp [trunc_apply, zeroSeq])

theorem shiftSeq_trunc_succ (n : ℕ) (c : Seq l) :
    shiftSeq (trunc (n + 1) c) = trunc n (shiftSeq c) :=
  Subtype.ext (by ext t i; simp [trunc_apply])

/-! ### Exercise 5.11a–c: additive preferences -/

variable {U : (Fin l → ℝ) → ℝ} {β M : ℝ}

/-- `(Tu)(c) = U(c₀) + βu(₁c)`. -/
noncomputable def opTU (U : (Fin l → ℝ) → ℝ) (hU : Continuous U) (hM : ∀ x, 0 ≤ x → |U x| ≤ M)
    (hβ : 0 ≤ β) (u : Seq l →ᵇ ℝ) : Seq l →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun c => U (c.1 0) + β * u (shiftSeq c))
    ((hU.comp continuous_head).add (continuous_const.mul (u.continuous.comp continuous_shiftSeq)))
    (M + β * ‖u‖) fun c => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add (hM _ (c.2 0)) ?_)
      rw [abs_mul, abs_of_nonneg hβ]
      exact mul_le_mul_of_nonneg_left (abs_apply_le_norm u (shiftSeq c)) hβ

theorem opTU_contraction (hU : Continuous U) (hM : ∀ x, 0 ≤ x → |U x| ≤ M) (hβ0 : 0 < β)
    (hβ1 : β < 1) : IsContraction (opTU (l := l) U hU hM hβ0.le) β := by
  refine ⟨hβ0, hβ1, fun u u' => (dist_le (mul_nonneg hβ0.le dist_nonneg)).2 fun c => ?_⟩
  change dist (U (c.1 0) + β * u (shiftSeq c)) (U (c.1 0) + β * u' (shiftSeq c)) ≤ _
  rw [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos hβ0]
  exact mul_le_mul_of_nonneg_left (by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := u) (g := u') (shiftSeq c)) hβ0.le

/-- **Exercises 5.11a and 5.11c.** `T` has a unique fixed point `û ∈ S`, and
`û(c) = Σ βᵗU(c_t)`: so `u(c) = Σ βᵗU(c_t)` is bounded and continuous on `L`. -/
theorem ex_5_11c (hU : Continuous U) (hM : ∀ x, 0 ≤ x → |U x| ≤ M) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ uhat : Seq l →ᵇ ℝ, opTU U hU hM hβ0.le uhat = uhat ∧
      (∀ w, opTU U hU hM hβ0.le w = w → w = uhat) ∧
      ∀ c, HasSum (fun t => β ^ t * U (c.1 t)) (uhat c) := by
  obtain ⟨u, hu, huniq, -⟩ := theorem_3_2 (opTU_contraction (l := l) hU hM hβ0 hβ1)
  refine ⟨u, hu, huniq, fun c => ?_⟩
  -- unroll the fixed point: `û(c) = Σ_{t<n} βᵗU(c_t) + βⁿû(ₙc)`
  have hfe : ∀ c, u c = U (c.1 0) + β * u (shiftSeq c) := fun c =>
    (DFunLike.congr_fun hu c).symm
  have hunroll : ∀ (n : ℕ) (c : Seq l), u c = ∑ t ∈ Finset.range n, β ^ t * U (c.1 t) +
      β ^ n * u ((shiftSeq)^[n] c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [hfe c, ih (shiftSeq c), Finset.sum_range_succ', Function.iterate_succ_apply]
      simp only [shiftSeq_apply]
      have e : β * ∑ t ∈ Finset.range n, β ^ t * U (c.1 (t + 1)) =
          ∑ t ∈ Finset.range n, β ^ (t + 1) * U (c.1 (t + 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [pow_zero, one_mul, pow_succ, ← e]
      ring
  have hsum : Summable fun t => β ^ t * U (c.1 t) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right M)
      fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le t)]
        exact mul_le_mul_of_nonneg_left (hM _ (c.2 t)) (pow_nonneg hβ0.le t)
  have hrest : Tendsto (fun n => β ^ n * u ((shiftSeq)^[n] c)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => ‖u‖ * β ^ n) (fun n => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le n), mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_apply_le_norm u _) (pow_nonneg hβ0.le n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul ‖u‖
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range n, β ^ t * U (c.1 t)) atTop (𝓝 (u c)) := by
    have := (tendsto_const_nhds (x := u c)).sub hrest
    rw [sub_zero] at this
    exact this.congr fun n => by rw [hunroll n c]; ring
  rw [← tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim]
  exact hsum.hasSum

/-- **Exercise 5.11a.** `|u(c)| ≤ M/(1 − β)`. -/
theorem ex_5_11a (hβ0 : 0 < β) (hβ1 : β < 1) (hM : ∀ x, 0 ≤ x → |U x| ≤ M) {c : Seq l}
    {s : ℝ} (hs : HasSum (fun t => β ^ t * U (c.1 t)) s) : |s| ≤ M / (1 - β) := by
  have hg := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left M
  have := hasSum_le (fun t => (show β ^ t * U (c.1 t) ≤ M * β ^ t by
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hM _ (c.2 t)))
      (pow_nonneg hβ0.le t))) hs hg
  have := hasSum_le (fun t => (show -(M * β ^ t) ≤ β ^ t * U (c.1 t) by
    have := neg_abs_le (U (c.1 t)) |>.trans' (neg_le_neg (hM _ (c.2 t)))
    nlinarith [pow_nonneg hβ0.le t])) hg.neg hs
  rw [abs_le, ← div_eq_mul_inv] at *
  constructor <;> linarith

/-- **Exercise 5.11b.** `S` is complete. -/
theorem ex_5_11b_complete : CompleteSpace (Seq l →ᵇ ℝ) := inferInstance

/-- The sequences that are eventually zero. -/
def eventuallyZero (l : ℕ) : Set (Seq l) := {e | ∃ N, ∀ t, N < t → e.1 t = 0}

/-- **Exercise 5.11b.** `u(cⁿ) → u(c)` can fail: `u(c) = min{1, dist(c, eventually zero)}` is in
`S`, and the constant sequence `1` has `|u(1) − u(1ⁿ)| = 1` for every `n`. -/
theorem ex_5_11b_counterexample (hl : 0 < l) :
    ∃ u : Seq l →ᵇ ℝ, ∃ c : Seq l, ∀ n, |u c - u (trunc n c)| = 1 := by
  have : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  set u : Seq l →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun c => min (Metric.infDist c (eventuallyZero l)) 1)
    ((Metric.continuous_infDist_pt _).min continuous_const) 1 fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min Metric.infDist_nonneg zero_le_one)]
      exact min_le_right _ _
  set c : Seq l := ⟨BoundedContinuousFunction.const ℕ 1, fun _ => zero_le_one⟩
  have hne : (eventuallyZero l).Nonempty := ⟨zeroSeq, 0, fun _ _ => rfl⟩
  have hc : u c = 1 := by
    change min (Metric.infDist c (eventuallyZero l)) 1 = 1
    refine min_eq_right ((Metric.le_infDist hne).2 fun e ⟨N, hN⟩ => ?_)
    have h1 := dist_coe_le_dist (f := c.1) (g := e.1) (N + 1)
    rw [hN (N + 1) (Nat.lt_succ_self N)] at h1
    have h2 : dist (c.1 (N + 1)) 0 = 1 := by
      rw [dist_zero_right]
      change ‖fun _ : Fin l => (1 : ℝ)‖ = 1
      rw [pi_norm_const, norm_one]
    rw [h2] at h1
    exact h1
  have htr : ∀ n, u (trunc n c) = 0 := fun n => by
    change min (Metric.infDist (trunc n c) (eventuallyZero l)) 1 = 0
    rw [Metric.infDist_zero_of_mem (show trunc n c ∈ eventuallyZero l from
      ⟨n, fun t ht => by simp [trunc_apply, not_le.2 ht]⟩)]
    simp
  exact ⟨u, c, fun n => by rw [hc, htr]; simp⟩

/-! ### Exercise 5.11d: aggregator functions -/

variable {W : (Fin l → ℝ) → ℝ → ℝ}

/-- (W1)–(W3), with `W(x, ·)` given on all of `ℝ` (for `z ≥ 0` this is the book's `W`). -/
structure AggHyp (W : (Fin l → ℝ) → ℝ → ℝ) (β M : ℝ) : Prop where
  β_pos : 0 < β
  β_lt : β < 1
  cont : Continuous fun p : (Fin l → ℝ) × ℝ => W p.1 p.2
  zero : W 0 0 = 0
  bdd : ∀ x, 0 ≤ x → |W x 0| ≤ M
  lip : ∀ x, 0 ≤ x → ∀ z z', |W x z - W x z'| ≤ β * |z - z'|

/-- `(T_W u)(c) = W[c₀, u(₁c)]`. -/
noncomputable def opTW (h : AggHyp W β M) (u : Seq l →ᵇ ℝ) : Seq l →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun c => W (c.1 0) (u (shiftSeq c)))
    (h.cont.comp (continuous_head.prodMk (u.continuous.comp continuous_shiftSeq)))
    (M + β * ‖u‖) fun c => by
      rw [Real.norm_eq_abs]
      have h1 := h.lip _ (c.2 0) (u (shiftSeq c)) 0
      have h2 := h.bdd _ (c.2 0)
      have h3 : |u (shiftSeq c)| ≤ ‖u‖ := by
        simpa [Real.norm_eq_abs] using u.norm_coe_le_norm (shiftSeq c)
      rw [sub_zero] at h1
      have := abs_sub_abs_le_abs_sub (W (c.1 0) (u (shiftSeq c))) (W (c.1 0) 0)
      nlinarith [h.β_pos]

theorem opTW_apply (h : AggHyp W β M) (u : Seq l →ᵇ ℝ) (c : Seq l) :
    opTW h u c = W (c.1 0) (u (shiftSeq c)) := rfl

theorem opTW_contraction (h : AggHyp W β M) : IsContraction (opTW (l := l) h) β := by
  refine ⟨h.β_pos, h.β_lt, fun u u' => (dist_le (mul_nonneg h.β_pos.le dist_nonneg)).2 fun c => ?_⟩
  rw [opTW_apply, opTW_apply, Real.dist_eq]
  exact (h.lip _ (c.2 0) _ _).trans (mul_le_mul_of_nonneg_left (by
    simpa [Real.dist_eq] using dist_coe_le_dist (f := u) (g := u') (shiftSeq c)) h.β_pos.le)

/-- **Exercise 5.11d.** `T_W` has a unique fixed point `u_W ∈ S`, `u_W(0) = 0`, and
`|u_W(c) − u_W(cⁿ)| ≤ βⁿ⁺¹‖u_W‖ ≤ βⁿ‖u_W‖`. -/
theorem ex_5_11d (h : AggHyp W β M) :
    ∃ uW : Seq l →ᵇ ℝ, opTW h uW = uW ∧ (∀ w, opTW h w = w → w = uW) ∧ uW zeroSeq = 0 ∧
      ∀ n c, |uW c - uW (trunc n c)| ≤ β ^ (n + 1) * ‖uW‖ ∧
        β ^ (n + 1) * ‖uW‖ ≤ β ^ n * ‖uW‖ := by
  obtain ⟨u, hu, huniq, -⟩ := theorem_3_2 (opTW_contraction (l := l) h)
  have hfe : ∀ c, u c = W (c.1 0) (u (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu c).symm
  -- `u(0) = W(0, u(0))` forces `u(0) = 0`
  have hz : u zeroSeq = 0 := by
    have h1 : u zeroSeq = W 0 (u zeroSeq) := by
      have := hfe zeroSeq
      rwa [shiftSeq_zero] at this
    have h2 := h.lip 0 le_rfl (u zeroSeq) 0
    rw [h.zero, sub_zero, sub_zero, ← h1] at h2
    have hb : 0 < 1 - β := by linarith [h.β_lt]
    have h3 : |u zeroSeq| * (1 - β) ≤ 0 := by nlinarith
    have h4 := abs_nonneg (u zeroSeq)
    exact abs_eq_zero.1 (le_antisymm (by nlinarith) h4)
  have hnorm : ∀ c, |u c| ≤ ‖u‖ := abs_apply_le_norm u
  have hbound : ∀ n c, |u c - u (trunc n c)| ≤ β ^ (n + 1) * ‖u‖ := by
    intro n
    induction n with
    | zero =>
      intro c
      rw [hfe c, hfe (trunc 0 c), head_trunc, shiftSeq_trunc_zero, hz, zero_add, pow_one]
      refine (h.lip _ (c.2 0) _ _).trans ?_
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left (hnorm _) h.β_pos.le
    | succ n ih =>
      intro c
      rw [hfe c, hfe (trunc (n + 1) c), head_trunc, shiftSeq_trunc_succ, pow_succ']
      refine (h.lip _ (c.2 0) _ _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih _) h.β_pos.le
  refine ⟨u, hu, huniq, hz, fun n c => ⟨hbound n c, ?_⟩⟩
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg h.β_pos.le n)
    h.β_lt.le) (norm_nonneg _)

/-- **Exercise 5.11d.** Under (W4), `W` increasing, `u_W` is increasing: `c ≤ c'` termwise
implies `u_W(c) ≤ u_W(c')`. -/
theorem ex_5_11d_mono (h : AggHyp W β M)
    (hW4 : ∀ x x' z z', 0 ≤ x → x ≤ x' → z ≤ z' → W x z ≤ W x' z') {uW : Seq l →ᵇ ℝ}
    (hu : opTW h uW = uW) {c c' : Seq l} (hcc' : ∀ t, c.1 t ≤ c'.1 t) : uW c ≤ uW c' := by
  have : Nonempty (Seq l →ᵇ ℝ) := ⟨0⟩
  set C' : Set (Seq l →ᵇ ℝ) := {u | ∀ c c' : Seq l, (∀ t, c.1 t ≤ c'.1 t) → u c ≤ u c'}
  have hclosed : IsClosed C' := by
    have : C' = ⋂ c, ⋂ c', ⋂ (_ : ∀ t, c.1 t ≤ c'.1 t), {u : Seq l →ᵇ ℝ | u c ≤ u c'} := by
      ext u; simp [C']
    rw [this]
    exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
      isClosed_le (continuous_eval_const c) (continuous_eval_const c')
  have hmaps : MapsTo (opTW h) C' C' := fun u hu c c' hcc => by
    rw [opTW_apply, opTW_apply]
    exact hW4 _ _ _ _ (c.2 0) (hcc 0) (hu _ _ fun t => hcc (t + 1))
  exact (corollary_1 (S' := C') (S'' := C') (opTW_contraction h) hu
    ⟨0, fun _ _ _ => le_rfl⟩ hclosed hmaps hmaps).1 c c' hcc'

/-- A nonnegative concave function on `[0, ∞)` is nondecreasing. -/
theorem monotoneOn_of_concave_nonneg {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ (Ici 0) φ)
    (h0 : ∀ z, 0 ≤ z → 0 ≤ φ z) : MonotoneOn φ (Ici 0) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  by_contra hgt
  push Not at hgt
  -- the chord slope `s < 0` from `a` to `b` bounds `φ` beyond `b`
  set s := (φ b - φ a) / (b - a)
  have hs : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  set z := b + (φ b + 1) / (-s)
  have hz : b < z := lt_add_of_pos_right _ (div_pos (by linarith [h0 b hb]) (by linarith))
  have hadj := hφ.slope_anti_adjacent ha (mem_Ici.2 (by linarith [hb.out] : (0 : ℝ) ≤ z))
    hlt hz
  rw [div_le_iff₀ (by linarith)] at hadj
  have hs0 : s ≠ 0 := hs.ne
  have : (φ b + 1) / -s * s = -(φ b + 1) := by field_simp
  have hzb : z - b = (φ b + 1) / -s := by simp only [z]; ring
  rw [hzb] at hadj
  have := h0 z (by linarith [hb.out])
  nlinarith

/-- **Exercise 5.11d.** Under (W5), `W` concave on `ℝˡ₊ × ℝ₊`, with `W ≥ 0` there, `u_W` is
nonnegative and concave. -/
theorem ex_5_11d_concave (h : AggHyp W β M)
    (hW5 : ConcaveOn ℝ ({x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0) fun p => W p.1 p.2)
    (hnn : ∀ x z, 0 ≤ x → 0 ≤ z → 0 ≤ W x z) {uW : Seq l →ᵇ ℝ} (hu : opTW h uW = uW) :
    (∀ c, 0 ≤ uW c) ∧ IsConcaveS convex_seqSet uW := by
  have : Nonempty (Seq l →ᵇ ℝ) := ⟨0⟩
  -- `W(x, ·)` is nondecreasing on `[0, ∞)`
  have hWz : ∀ x, 0 ≤ x → MonotoneOn (W x) (Ici 0) := fun x hx => by
    refine monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
      fun z hz => hnn x z hx hz
    have := hW5.2 (show (x, z) ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from ⟨hx, hz⟩)
      (show (x, z') ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from ⟨hx, hz'⟩) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
    exact this
  set C : Set (Seq l →ᵇ ℝ) := {u | (∀ c, 0 ≤ u c) ∧ IsConcaveS convex_seqSet u}
  have hclosed : IsClosed C := by
    have : C = (⋂ c, {u : Seq l →ᵇ ℝ | 0 ≤ u c}) ∩ {u | IsConcaveS convex_seqSet u} := by
      ext u; simp [C]
    rw [this]
    exact (isClosed_iInter fun c => isClosed_le continuous_const (continuous_eval_const c)).inter
      (isClosed_concave convex_seqSet)
  have hshift : ∀ (c c' : Seq l) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1),
      shiftSeq (cmb convex_seqSet h0 h1 c c') =
        cmb convex_seqSet h0 h1 (shiftSeq c) (shiftSeq c') := fun c c' θ h0 h1 =>
    Subtype.ext (by ext t i; rfl)
  have hmaps : MapsTo (opTW h) C C := fun u ⟨hu0, huc⟩ => by
    refine ⟨fun c => hnn _ _ (c.2 0) (hu0 _), fun c c' θ h0 h1 => ?_⟩
    rw [opTW_apply, opTW_apply, opTW_apply, hshift]
    have hc := huc (shiftSeq c) (shiftSeq c') θ h0 h1
    have hmid : 0 ≤ θ * u (shiftSeq c) + (1 - θ) * u (shiftSeq c') :=
      add_nonneg (mul_nonneg h0 (hu0 _)) (mul_nonneg (by linarith) (hu0 _))
    have hWc := hW5.2 (show (c.1 0, u (shiftSeq c)) ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from
      ⟨c.2 0, hu0 _⟩) (show (c'.1 0, u (shiftSeq c')) ∈ {x : Fin l → ℝ | 0 ≤ x} ×ˢ Set.Ici 0 from
      ⟨c'.2 0, hu0 _⟩) h0 (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hWc
    have hhead : (cmb convex_seqSet h0 h1 c c').1 0 = θ • c.1 0 + (1 - θ) • c'.1 0 := rfl
    rw [hhead]
    refine hWc.trans (hWz _ ?_ (mem_Ici.2 hmid) (mem_Ici.2 (hu0 _)) hc)
    exact (convex_seqSet c.2 c'.2 h0 (by linarith) (by ring) : _) 0
  exact (corollary_1 (S' := C) (S'' := C) (opTW_contraction h) hu
    ⟨0, fun _ => le_rfl, fun _ _ _ _ _ => by simp⟩ hclosed hmaps hmaps).1

/-! ### Exercise 5.11e: marginal rates of substitution -/

/-- `c` with `h⁺ = max{h, 0}` added to good `i` in period `t`. -/
noncomputable def bump (c : Seq l) (t : ℕ) (i : Fin l) (h : ℝ) : Seq l :=
  ⟨c.1 + BoundedContinuousFunction.mkOfDiscrete
      (fun s => if s = t then Pi.single i (max h 0) else (0 : Fin l → ℝ))
      (2 * ‖(Pi.single i (max h 0) : Fin l → ℝ)‖) fun s s' => by
        refine (dist_le_norm_add_norm _ _).trans ?_
        have : ∀ u, ‖(if u = t then Pi.single i (max h 0) else (0 : Fin l → ℝ))‖ ≤
            ‖(Pi.single i (max h 0) : Fin l → ℝ)‖ := fun u => by
          split_ifs <;> simp
        linarith [this s, this s'],
    fun s => by
      change 0 ≤ c.1 s + (if s = t then Pi.single i (max h 0) else (0 : Fin l → ℝ))
      refine add_nonneg (c.2 s) ?_
      split_ifs
      · intro j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      · exact le_rfl⟩

theorem shiftSeq_bump_zero (c : Seq l) (i : Fin l) (h : ℝ) :
    shiftSeq (bump c 0 i h) = shiftSeq c :=
  Subtype.ext (by ext s j; simp [bump])

theorem shiftSeq_bump_succ (c : Seq l) (t : ℕ) (i : Fin l) (h : ℝ) :
    shiftSeq (bump c (t + 1) i h) = bump (shiftSeq c) t i h :=
  Subtype.ext (by ext s j; simp [bump])

theorem head_bump_zero (c : Seq l) (i : Fin l) (h : ℝ) :
    (bump c 0 i h).1 0 = c.1 0 + Pi.single i (max h 0) := by
  simp [bump]

theorem head_bump_succ (c : Seq l) (t : ℕ) (i : Fin l) (h : ℝ) :
    (bump c (t + 1) i h).1 0 = c.1 0 := by
  simp [bump]

/-- **Exercise 5.11e.** Raising good `i` in period `t` by `h ≥ 0` changes `u_W` at the rate
`[∏_{s<t} W_z(c_s, u_W(ₛ₊₁c))] · W_{x_i}(c_t, u_W(ₜ₊₁c))`. The marginal rate of substitution
between `c_{it}` and `c_{j,t+k}` is the ratio of two such rates. -/
theorem ex_5_11e (h : AggHyp W β M) {uW : Seq l →ᵇ ℝ} (hu : opTW h uW = uW) (t : ℕ)
    (i : Fin l) (c : Seq l) {Wz : ℕ → ℝ} {Wx : ℝ}
    (hz : ∀ s < t, HasDerivAt (W (c.1 s)) (Wz s) (uW ((shiftSeq)^[s + 1] c)))
    (hx : HasDerivAt (fun h => W (c.1 t + Pi.single i h) (uW ((shiftSeq)^[t + 1] c))) Wx 0) :
    HasDerivWithinAt (fun h => uW (bump c t i h)) ((∏ s ∈ Finset.range t, Wz s) * Wx)
      (Ici 0) 0 := by
  have hfe : ∀ c, uW c = W (c.1 0) (uW (shiftSeq c)) := fun c =>
    (DFunLike.congr_fun hu c).symm
  induction t generalizing c Wz with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, one_mul]
    refine hx.hasDerivWithinAt.congr (fun h (hh : 0 ≤ h) => ?_) ?_
    · rw [hfe, head_bump_zero, shiftSeq_bump_zero, max_eq_left hh]; rfl
    · rw [hfe, head_bump_zero, shiftSeq_bump_zero, max_self]; rfl
  | succ t ih =>
    -- one level of the recursion: `u_W(c + h e_{i,t+1}) = W(c₀, u_W(₁c + h e_{i,t}))`
    have hshift : ∀ s, (shiftSeq c).1 s = c.1 (s + 1) := fun s => rfl
    have hit : ∀ s, (shiftSeq)^[s + 1] (shiftSeq c) = (shiftSeq)^[s + 2] c := fun s => by
      rw [← Function.iterate_succ_apply]
    have hinner := ih (shiftSeq c) (Wz := fun s => Wz (s + 1))
      (fun s hs => by rw [hshift, hit]; exact hz (s + 1) (by omega))
      (by rw [hshift, hit]; exact hx)
    have houter : HasDerivAt (W (c.1 0)) (Wz 0) (uW (bump (shiftSeq c) t i 0)) := by
      have e : bump (shiftSeq c) t i 0 = (shiftSeq)^[0 + 1] c := Subtype.ext (by
        ext s j; simp [bump])
      rw [e]; exact hz 0 (by omega)
    have := houter.comp_hasDerivWithinAt (0 : ℝ) hinner
    rw [Finset.prod_range_succ']
    refine (this.congr (fun h _ => ?_) ?_).congr_deriv (by ring)
    · simp only [Function.comp_apply]; rw [hfe, head_bump_succ, shiftSeq_bump_succ]
    · simp only [Function.comp_apply]; rw [hfe, head_bump_succ, shiftSeq_bump_succ]

end StokeyLucasPrescott.DeterministicDynamics
