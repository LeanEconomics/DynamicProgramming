/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INFinite
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The infinite-horizon inventory problem: Propositions 8.5.1–8.5.3

Miao, §8.5, pp. 270–275. `INModel.f x = sup_n f_n(x)` and `INModel.Glim = Gf f`, i.e.
`G(x) = px + L(x) + βEf(x − z)`.

* `diff_bound`: for every `B`, `0 ≤ f_{k+2} − f_{k+1} ≤ β^k K` on `(−∞, B]` (the book's
  contraction estimate, p. 273, started at `n = 1`); `tail_bound`: `0 ≤ f − f_{n+1} ≤ β^n K`
  on `(−∞, B]`.
* **Proposition 8.5.1** (`proposition_8_5_1`): `f_n ↑ f` and `G_n ↑ G`, uniformly on every
  finite interval, and `f`, `G` are continuous. Also `good_f`: `f` is continuous, nonnegative,
  c-convex and `f(w) ≤ c + pa + f(w + a)`.
* **Proposition 8.5.2** (`proposition_8_5_2`): `f` satisfies the Bellman equation (8.21).
* **Proposition 8.5.3 = Exercise 8.4** (`proposition_8_5_3`, `ex_8_4`): `s_n`, `S_n` have
  convergent subsequences; every limit point of `S_n` minimises `G`; a unique minimiser forces
  `S_n` to converge; `G` is c-convex; every limit point `s` of `s_n` has `G(s) = c + G(S)` for
  every minimiser `S` of `G`; for such `s ≤ S` the (s, S) policy is optimal for (8.21)
  (`ex_8_4_policy`), and `s < S` automatically when `c > 0` (`ex_8_4_lt`).

**Departures.** (1) The book's iteration `max|f_{n+1} − f_n| ≤ βⁿ max|f_1|` (p. 274) uses that
`f_n − f_{n−1}` is constant left of `−A`, which fails for `n = 1` (`f₁(x) = −px + G₁(s₁)`
while `f₀ = 0`); we start the iteration at `f₂ − f₁`. (2) In Proposition 8.5.3 a limit point
`s` of `{s_n}` and a limit point `S` of `{S_n}` need not satisfy `s ≤ S` when `c = 0` (both are
then minimisers of `G`, possibly different), and `d(x) = S − x ≥ 0` requires `s ≤ S`; we prove
the policy statement for `s ≤ S`, which holds automatically when `c > 0` (`ex_8_4_lt`) and can
be arranged when `c = 0` by taking `S = s`. (3) Proposition 8.5.2's limit interchange
("tedious") is done with the uniform estimate `tail_bound`, so no compactness argument is
needed; Assumption 8.5.2 is not used.
-/

namespace Miao.Applications

namespace INModel

open MeasureTheory Filter Topology

variable (M : INModel)

/-- The infinite-horizon value function `f(x) = lim_n f_n(x) = sup_n f_n(x)` (Miao, p. 272). -/
noncomputable def f (x : ℝ) : ℝ := ⨆ n, M.fn n x

/-- `G(x) = px + L(x) + βEf(x − z)` (Miao, p. 275). -/
noncomputable def Glim : ℝ → ℝ := M.Gf M.f

variable {M}

/-- `f_n(w) = −pw + G_n(s_n)` for `w ≤ 2s_1 − S_1` (`n ≥ 1`), by Lemma 8.5.6 and (8.26). -/
theorem fn_left (hA : M.Assumption851) (n : ℕ) {w : ℝ} (hw : w ≤ 2 * M.sn 1 - M.Sn 1) :
    M.fn (n + 1) w = -M.p * w + M.G (n + 1) (M.sn (n + 1)) := by
  rw [fn_eq hA, max_eq_right (hw.trans (lemma_8_5_6_le hA (n + 1)))]

/-- Miao, p. 273: for every `B`, `0 ≤ f_{k+2}(w) − f_{k+1}(w) ≤ β^k K` for `w ≤ B`. -/
theorem diff_bound (hA : M.Assumption851) (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ k w, w ≤ B → M.fn (k + 2) w - M.fn (k + 1) w ≤ M.β ^ k * K := by
  have := hA.prob
  obtain ⟨Bm, hBm⟩ := lemma_8_5_5 hA
  set a₀ := 2 * M.sn 1 - M.Sn 1
  set B' := max B (max Bm a₀)
  have hg : Continuous fun w => M.fn 2 w - M.fn 1 w := (good_fn hA 2).1.sub (good_fn hA 1).1
  obtain ⟨wm, -, hwm⟩ := (isCompact_Icc : IsCompact (Set.Icc a₀ B')).exists_isMaxOn
    (Set.nonempty_Icc.2 (le_max_right _ _ |>.trans (le_max_right _ _))) hg.continuousOn
  set K := max 0 (M.fn 2 wm - M.fn 1 wm)
  have hbase : ∀ w, w ≤ B' → M.fn 2 w - M.fn 1 w ≤ K := by
    intro w hw
    rcases le_or_gt a₀ w with h | h
    · exact (hwm ⟨h, hw⟩).trans (le_max_right _ _)
    · have e : M.fn 2 w - M.fn 1 w = M.fn 2 a₀ - M.fn 1 a₀ := by
        rw [fn_left hA 1 h.le, fn_left hA 0 h.le, fn_left hA 1 le_rfl, fn_left hA 0 le_rfl]
        ring
      rw [e]
      exact (hwm ⟨le_rfl, (le_max_right _ _).trans (le_max_right _ _)⟩).trans
        (le_max_right _ _)
  have hall : ∀ k w, w ≤ B' → M.fn (k + 2) w - M.fn (k + 1) w ≤ M.β ^ k * K := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hbase w hw
    | succ k ih =>
      intro x hx
      obtain ⟨heq, -⟩ := lemma_8_5_2_fn hA (k + 1) x
      set y := in_ssPolicy (M.sn (k + 2)) (M.Sn (k + 2)) x
      have hxy : x ≤ y := by
        unfold y in_ssPolicy; split_ifs with h
        · exact h.trans (eq_8_23 hA (k + 2)).2.1
        · exact le_rfl
      have hyB : y ≤ B' := by
        unfold y in_ssPolicy; split_ifs
        · exact (hBm _).trans ((le_max_left _ _).trans (le_max_right _ _))
        · exact hx
      have h1 : M.fn (k + 3) x ≤ M.TT (M.fn (k + 2)) y x :=
        T_le_TT hA (good_fn hA (k + 2)).2.1 hxy
      have hI : ∫ z, (M.fn (k + 2) (y - z) - M.fn (k + 1) (y - z)) ∂M.φ ≤ M.β ^ k * K := by
        have := integral_mono_ae ((int_fn hA _ y).sub (int_fn hA _ y))
          (integrable_const (M.β ^ k * K)) (by
            filter_upwards [hA.demand_nonneg] with z hz
            exact ih (y - z) (by linarith))
        simpa using this
      rw [integral_sub (int_fn hA _ y) (int_fn hA _ y)] at hI
      have e : M.TT (M.fn (k + 2)) y x - M.TT (M.fn (k + 1)) y x =
          M.β * ((∫ z, M.fn (k + 2) (y - z) ∂M.φ) - ∫ z, M.fn (k + 1) (y - z) ∂M.φ) := by
        unfold TT; ring
      have := mul_le_mul_of_nonneg_left hI hA.β_pos.le
      rw [pow_succ]
      change M.fn (k + 3) x - M.fn (k + 1 + 1) x ≤ _
      rw [heq]
      nlinarith
  refine ⟨K, le_max_left _ _, fun k w hw => hall k w (hw.trans (le_max_left _ _))⟩

/-- Partial sums of the geometric bound: `f_{n+1+j}(w) − f_{n+1}(w) ≤ βⁿK(1 − β^j)/(1 − β)`. -/
theorem partial_bound (hA : M.Assumption851) {B K : ℝ}
    (hD : ∀ k w, w ≤ B → M.fn (k + 2) w - M.fn (k + 1) w ≤ M.β ^ k * K) (n : ℕ) {w : ℝ}
    (hw : w ≤ B) :
    ∀ j, M.fn (n + 1 + j) w - M.fn (n + 1) w ≤ M.β ^ n * K / (1 - M.β) * (1 - M.β ^ j) := by
  have h1 : 0 < 1 - M.β := sub_pos.2 hA.β_lt
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have := hD (n + j) w hw
    have e1 : n + j + 2 = n + 1 + (j + 1) := by ring
    have e2 : n + j + 1 = n + 1 + j := by ring
    rw [e1, e2] at this
    have e : M.β ^ n * K / (1 - M.β) * (1 - M.β ^ (j + 1)) =
        M.β ^ n * K / (1 - M.β) * (1 - M.β ^ j) + M.β ^ (n + j) * K := by
      field_simp
      ring
    rw [e]
    linarith

/-- For every `B` there is `K ≥ 0` with `f_m(w) ≤ f_{n+1}(w) + βⁿK` for all `m, n` and
`w ≤ B`. -/
theorem fn_le_bound (hA : M.Assumption851) (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ n w, w ≤ B → ∀ m, M.fn m w ≤ M.fn (n + 1) w + M.β ^ n * K := by
  obtain ⟨K, hK, hD⟩ := diff_bound hA B
  have h1 : 0 < 1 - M.β := sub_pos.2 hA.β_lt
  have hmono : ∀ w, Monotone fun n => M.fn n w :=
    fun w => monotone_nat_of_le_succ fun n => fn_mono hA n w
  refine ⟨K / (1 - M.β), div_nonneg hK h1.le, fun n w hw m => ?_⟩
  have hpos : 0 ≤ M.β ^ n * (K / (1 - M.β)) :=
    mul_nonneg (pow_nonneg hA.β_pos.le _) (div_nonneg hK h1.le)
  rcases le_or_gt m (n + 1) with hm | hm
  · linarith [hmono w hm]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm.le
    have := partial_bound hA hD n hw j
    have hj : 0 ≤ M.β ^ n * (K / (1 - M.β)) * M.β ^ j :=
      mul_nonneg hpos (pow_nonneg hA.β_pos.le _)
    rw [mul_div_assoc] at this
    nlinarith

/-- `n ↦ f_n(x)` is bounded above. -/
theorem fn_bddAbove (hA : M.Assumption851) (x : ℝ) : BddAbove (Set.range fun n => M.fn n x) := by
  obtain ⟨K, -, hK⟩ := fn_le_bound hA x
  exact ⟨M.fn 1 x + M.β ^ 0 * K, by rintro _ ⟨m, rfl⟩; exact hK 0 x le_rfl m⟩

/-- Each `f_n(x)` increases to the finite limit `f(x)` (Miao, Proposition 8.5.1). -/
theorem fn_tendsto (hA : M.Assumption851) (x : ℝ) :
    Tendsto (fun n => M.fn n x) atTop (𝓝 (M.f x)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => fn_mono hA n x) (fn_bddAbove hA x)

/-- `f_n ≤ f`. -/
theorem fn_le_f (hA : M.Assumption851) (n : ℕ) (x : ℝ) : M.fn n x ≤ M.f x :=
  le_ciSup (fn_bddAbove hA x) n

/-- Miao, p. 274 (proof of Proposition 8.5.1): for every `B` there is `K ≥ 0` with
`0 ≤ f(w) − f_{n+1}(w) ≤ βⁿK` for `w ≤ B`. -/
theorem tail_bound (hA : M.Assumption851) (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ n w, w ≤ B → M.f w - M.fn (n + 1) w ≤ M.β ^ n * K := by
  obtain ⟨K, hK, hle⟩ := fn_le_bound hA B
  refine ⟨K, hK, fun n w hw => ?_⟩
  have : M.f w ≤ M.fn (n + 1) w + M.β ^ n * K := ciSup_le (hle n w hw)
  linarith

/-- A geometric bound gives uniform convergence (shifted by `k`). -/
theorem unif_of_bound {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    {s : Set ℝ} (k : ℕ) (hb : ∀ n x, x ∈ s → |g x - F (n + k) x| ≤ β ^ n * K) :
    TendstoUniformlyOn F g atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun n => β ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (N + k)] with n hn x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : N + k + m = (N + m) + k := by ring
  rw [e, Real.dist_eq] at *
  exact (hb _ x hx).trans_lt (hN _ (by omega))

/-- `f` is continuous, nonnegative, c-convex and `f(w) ≤ c + pa + f(w + a)` (limits of the
corresponding properties of `f_n`; continuity by local uniform convergence). -/
theorem good_f (hA : M.Assumption851) : M.Good M.f := by
  refine ⟨?_, fun x => (fn_le_f hA 0 x).trans' le_rfl, fun w a ha => ?_, fun x a b ha hb => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨K, -, hK⟩ := tail_bound hA (x₀ + 1)
    have hU : TendstoUniformlyOn M.fn M.f atTop (Set.Iio (x₀ + 1)) :=
      unif_of_bound (K := K) hA.β_pos.le hA.β_lt 1 fun n x hx => by
        rw [abs_of_nonneg (by linarith [fn_le_f hA (n + 1) x])]
        exact hK n x (Set.mem_Iio.1 hx).le
    exact (hU.continuousOn (Eventually.of_forall fun n => (good_fn hA n).1.continuousOn).frequently)
      |>.continuousAt (Iio_mem_nhds (by linarith))
  · exact le_of_tendsto_of_tendsto' (fn_tendsto hA w) ((fn_tendsto hA (w + a)).const_add _)
      fun n => (good_fn hA n).2.2.1 w a ha
  · have ht : Tendsto (fun n => M.c + M.fn n (x + a) - M.fn n x -
        a * ((M.fn n x - M.fn n (x - b)) / b)) atTop
        (𝓝 (M.c + M.f (x + a) - M.f x - a * ((M.f x - M.f (x - b)) / b))) :=
      (((fn_tendsto hA (x + a)).const_add _).sub (fn_tendsto hA x)).sub
        ((((fn_tendsto hA x).sub (fn_tendsto hA (x - b))).div_const b).const_mul a)
    exact ge_of_tendsto' ht fun n => (good_fn hA n).2.2.2 x a b ha hb

/-- Integrability of `z ↦ f(y − z)`. -/
theorem int_f (hA : M.Assumption851) (y : ℝ) : Integrable (fun z => M.f (y - z)) M.φ :=
  int_of_P hA (good_f hA).1 (good_f hA).2.1 (good_f hA).2.2.1 y

/-- `G` is continuous. -/
theorem Glim_cont (hA : M.Assumption851) : Continuous M.Glim :=
  Gf_cont hA (good_f hA).1 (good_f hA).2.1 (good_f hA).2.2.1

/-- `G` is coercive. -/
theorem Glim_coercive (hA : M.Assumption851) : in_Coercive M.Glim :=
  Gf_coercive hA (good_f hA).2.1

/-- `G` is c-convex (Miao, Proposition 8.5.3). -/
theorem Glim_cconvex (hA : M.Assumption851) : in_CConvex M.c M.Glim :=
  Gf_cconvex hA (good_f hA).2.2.2 (int_f hA)

/-- `G_n ≤ G`. -/
theorem G_le_Glim (hA : M.Assumption851) (n : ℕ) (x : ℝ) : M.G n x ≤ M.Glim x := by
  have := hA.prob
  unfold G Glim Gf
  have := integral_mono (int_fn hA (n - 1) x) (int_f hA x) fun z => fn_le_f hA _ (x - z)
  have := mul_le_mul_of_nonneg_left this hA.β_pos.le
  linarith

/-- For every `B` there is `K ≥ 0` with `0 ≤ G(x) − G_{n+2}(x) ≤ βⁿK` for `x ≤ B`. -/
theorem G_tail_bound (hA : M.Assumption851) (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ n x, x ≤ B → M.Glim x - M.G (n + 2) x ≤ M.β ^ n * K := by
  have := hA.prob
  obtain ⟨K, hK, hT⟩ := tail_bound hA B
  refine ⟨K, hK, fun n x hx => ?_⟩
  have hI : ∫ z, (M.f (x - z) - M.fn (n + 1) (x - z)) ∂M.φ ≤ M.β ^ n * K := by
    have := integral_mono_ae ((int_f hA x).sub (int_fn hA _ x))
      (integrable_const (M.β ^ n * K)) (by
        filter_upwards [hA.demand_nonneg] with z hz
        exact hT n (x - z) (by linarith))
    simpa using this
  rw [integral_sub (int_f hA x) (int_fn hA _ x)] at hI
  have e : M.Glim x - M.G (n + 2) x =
      M.β * ((∫ z, M.f (x - z) ∂M.φ) - ∫ z, M.fn (n + 1) (x - z) ∂M.φ) := by
    change M.Gf M.f x - M.Gf (M.fn (n + 1)) x = _
    unfold Gf; ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hI hA.β_pos.le
  have h2 : M.β * (M.β ^ n * K) ≤ M.β ^ n * K := by
    have := mul_nonneg (pow_nonneg hA.β_pos.le n) hK
    nlinarith [hA.β_lt]
  linarith

/-- `n ↦ G_n(x)` is monotone. -/
theorem G_mono (hA : M.Assumption851) (x : ℝ) : Monotone fun n => M.G n x := by
  have := hA.prob
  intro n m hnm
  have hmono : Monotone fun k => M.fn k (x - 0) := monotone_nat_of_le_succ fun k => fn_mono hA k _
  simp only [G, Gf]
  have := integral_mono (int_fn hA (n - 1) x) (int_fn hA (m - 1) x) fun z =>
    (monotone_nat_of_le_succ fun k => fn_mono hA k (x - z)) (Nat.sub_le_sub_right hnm 1)
  have := mul_le_mul_of_nonneg_left this hA.β_pos.le
  linarith

/-- **Proposition 8.5.1** (Miao, p. 272). Under Assumption 8.5.1, `{f_n(x)}` and `{G_n(x)}`
converge monotonically to finite limits `f(x)`, `G(x)`; the convergence is uniform on every
finite interval; `f` and `G` are continuous. -/
theorem proposition_8_5_1 (hA : M.Assumption851) :
    (∀ x, Monotone (fun n => M.fn n x) ∧ Tendsto (fun n => M.fn n x) atTop (𝓝 (M.f x))) ∧
    (∀ x, Monotone (fun n => M.G n x) ∧ Tendsto (fun n => M.G n x) atTop (𝓝 (M.Glim x))) ∧
    (∀ u v, TendstoUniformlyOn M.fn M.f atTop (Set.Icc u v)) ∧
    (∀ u v, TendstoUniformlyOn M.G M.Glim atTop (Set.Icc u v)) ∧
    Continuous M.f ∧ Continuous M.Glim := by
  have hUG : ∀ u v, TendstoUniformlyOn M.G M.Glim atTop (Set.Icc u v) := fun u v => by
    obtain ⟨K, -, hK⟩ := G_tail_bound hA v
    exact unif_of_bound hA.β_pos.le hA.β_lt 2 fun n x hx => by
      rw [abs_of_nonneg (by linarith [G_le_Glim hA (n + 2) x])]
      exact hK n x hx.2
  refine ⟨fun x => ⟨monotone_nat_of_le_succ fun n => fn_mono hA n x, fn_tendsto hA x⟩,
    fun x => ⟨G_mono hA x, ?_⟩, fun u v => ?_, hUG, (good_f hA).1, Glim_cont hA⟩
  · exact (hUG x x).tendsto_at (Set.left_mem_Icc.2 le_rfl)
  · obtain ⟨K, -, hK⟩ := tail_bound hA v
    exact unif_of_bound hA.β_pos.le hA.β_lt 1 fun n x hx => by
      rw [abs_of_nonneg (by linarith [fn_le_f hA (n + 1) x])]
      exact hK n x hx.2

/-- `f(x) ≤ T(y, x, f)` for `y ≥ x` (half of Proposition 8.5.2). -/
theorem f_le_TT (hA : M.Assumption851) {x y : ℝ} (hxy : x ≤ y) : M.f x ≤ M.TT M.f y x := by
  have := hA.prob
  have h : ∀ n, M.fn (n + 1) x ≤ M.TT M.f y x := fun n => by
    refine (T_le_TT hA (good_fn hA n).2.1 hxy).trans ?_
    unfold TT
    have := integral_mono (int_fn hA n y) (int_f hA y) fun z => fn_le_f hA n (y - z)
    have := mul_le_mul_of_nonneg_left this hA.β_pos.le
    linarith
  exact le_of_tendsto' ((tendsto_add_atTop_iff_nat 1).2 (fn_tendsto hA x)) h

/-- **Proposition 8.5.2** (Miao, p. 274). Under Assumption 8.5.1, the limit `f` satisfies the
Bellman equation (8.21): `f(x) = min_{y ≥ x} L(y) + C(y − x) + βEf(y − z)`. -/
theorem proposition_8_5_2 (hA : M.Assumption851) (x : ℝ) : M.f x = M.T M.f x := by
  have := hA.prob
  have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
  refine le_antisymm (le_ciInf fun y => f_le_TT hA y.2) ?_
  obtain ⟨Bm, hBm⟩ := lemma_8_5_5 hA
  obtain ⟨K, -, hK⟩ := tail_bound hA (max x Bm)
  have hbd : ∀ n, M.T M.f x ≤ M.f x + M.β ^ n * K := by
    intro n
    obtain ⟨heq, -⟩ := lemma_8_5_2_fn hA (n + 1) x
    set y := in_ssPolicy (M.sn (n + 2)) (M.Sn (n + 2)) x
    have hxy : x ≤ y := by
      unfold y in_ssPolicy; split_ifs with h
      · exact h.trans (eq_8_23 hA (n + 2)).2.1
      · exact le_rfl
    have hyB : y ≤ max x Bm := by
      unfold y in_ssPolicy; split_ifs
      · exact (hBm _).trans (le_max_right _ _)
      · exact le_max_left _ _
    have h1 : M.T M.f x ≤ M.TT M.f y x := T_le_TT hA (good_f hA).2.1 hxy
    have hI : ∫ z, (M.f (y - z) - M.fn (n + 1) (y - z)) ∂M.φ ≤ M.β ^ n * K := by
      have := integral_mono_ae ((int_f hA y).sub (int_fn hA _ y))
        (integrable_const (M.β ^ n * K)) (by
          filter_upwards [hA.demand_nonneg] with z hz
          exact hK n (y - z) (by linarith))
      simpa using this
    rw [integral_sub (int_f hA y) (int_fn hA _ y)] at hI
    have e : M.TT M.f y x = M.TT (M.fn (n + 1)) y x +
        M.β * ((∫ z, M.f (y - z) ∂M.φ) - ∫ z, M.fn (n + 1) (y - z) ∂M.φ) := by
      unfold TT; ring
    have h2 := mul_le_mul_of_nonneg_left hI hA.β_pos.le
    have h3 : M.β * (M.β ^ n * K) ≤ M.β ^ n * K := by
      have := mul_nonneg (pow_nonneg hA.β_pos.le n) (show 0 ≤ K by
        have := hK 0 x (le_max_left _ _); nlinarith [fn_le_f hA 1 x])
      nlinarith [hA.β_lt]
    have h4 := fn_le_f hA (n + 2) x
    rw [heq] at h4
    linarith
  have ht : Tendsto (fun n => M.f x + M.β ^ n * K) atTop (𝓝 (M.f x)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hA.β_pos.le hA.β_lt).mul_const K
      |>.const_add (M.f x))
  exact ge_of_tendsto' ht hbd

/-- A limit point of a real sequence: the limit of some subsequence `x ∘ φ`, `φ → ∞`. -/
def in_IsLimitPoint (x : ℕ → ℝ) (l : ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ Tendsto (x ∘ φ) atTop (𝓝 l)

/-- `G_{φ(k)}(y_k) → G(y*)` when `φ → ∞`, `y_k → y*` and `y_k ≤ B`. -/
theorem G_comp_tendsto (hA : M.Assumption851) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {y : ℕ → ℝ} {y' B : ℝ} (hy : Tendsto y atTop (𝓝 y')) (hB : ∀ k, y k ≤ B) :
    Tendsto (fun k => M.G (φ k) (y k)) atTop (𝓝 (M.Glim y')) := by
  obtain ⟨K, -, hK⟩ := G_tail_bound hA B
  have h1 : Tendsto (fun k => M.Glim (y k)) atTop (𝓝 (M.Glim y')) :=
    ((Glim_cont hA).tendsto y').comp hy
  have h2 : Tendsto (fun k => M.β ^ (φ k - 2) * K) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hA.β_pos.le hA.β_lt).comp
      ((tendsto_sub_atTop_nat 2).comp hφ)).mul_const K
    simpa using this
  have h3 : Tendsto (fun k => M.Glim (y k) - M.G (φ k) (y k)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
    · exact Eventually.of_forall fun k => by linarith [G_le_Glim hA (φ k) (y k)]
    · filter_upwards [hφ.eventually (eventually_ge_atTop 2)] with k hk
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hk
      have := hK n (y k) (hB k)
      rw [hn, add_comm 2 n] at *
      simpa using this
  simpa using h1.sub h3

/-- `G_n(S_n) → min G`. -/
theorem G_Sn_tendsto (hA : M.Assumption851) {S : ℝ} (hS : ∀ y, M.Glim S ≤ M.Glim y) :
    Tendsto (fun n => M.G n (M.Sn n)) atTop (𝓝 (M.Glim S)) := by
  obtain ⟨Bm, hBm⟩ := lemma_8_5_5 hA
  obtain ⟨K, -, hK⟩ := G_tail_bound hA Bm
  have h2 : Tendsto (fun n => M.Glim S - M.β ^ (n - 2) * K) atTop (𝓝 (M.Glim S)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hA.β_pos.le hA.β_lt).comp
      (tendsto_sub_atTop_nat 2)).mul_const K
    simpa using this.const_sub (M.Glim S)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have := hK m (M.Sn (2 + m)) (hBm _)
    rw [add_comm 2 m] at *
    simp only [Nat.add_sub_cancel]
    linarith [hS (M.Sn (m + 2))]
  · exact Eventually.of_forall fun n =>
      ((Sn_isLeast hA n).1 S).trans (G_le_Glim hA n S)

/-- **Proposition 8.5.3** (Miao, p. 275), first part (**Exercise 8.4**). Under Assumption
8.5.1: `{s_n}` and `{S_n}` have convergent subsequences; every limit point of `{S_n}` minimises
`G(x) = px + L(x) + βEf(x − z)`; if `G` has a unique minimiser then `{S_n}` converges to it;
`G` is c-convex; and every limit point `s` of `{s_n}` satisfies `G(s) = c + G(S)` for every
minimiser `S` of `G` (in particular every limit point of `{S_n}`). -/
theorem proposition_8_5_3 (hA : M.Assumption851) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l, Tendsto (M.sn ∘ φ) atTop (𝓝 l)) ∧
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l, Tendsto (M.Sn ∘ φ) atTop (𝓝 l)) ∧
    (∀ S, in_IsLimitPoint M.Sn S → ∀ y, M.Glim S ≤ M.Glim y) ∧
    (∀ S, (∀ y, M.Glim S ≤ M.Glim y) → (∀ S', (∀ y, M.Glim S' ≤ M.Glim y) → S' = S) →
      Tendsto M.Sn atTop (𝓝 S)) ∧
    in_CConvex M.c M.Glim ∧
    (∀ s S, in_IsLimitPoint M.sn s → (∀ y, M.Glim S ≤ M.Glim y) →
      M.Glim s = M.c + M.Glim S) := by
  obtain ⟨Bm, hBm⟩ := lemma_8_5_5 hA
  set a₀ := 2 * M.sn 1 - M.Sn 1
  have hsI : ∀ n, M.sn n ∈ Set.Icc a₀ Bm := fun n =>
    ⟨lemma_8_5_6_le hA n, (eq_8_23 hA n).2.1.trans (hBm n)⟩
  have hSI : ∀ n, M.Sn n ∈ Set.Icc a₀ Bm := fun n =>
    ⟨(hsI n).1.trans (eq_8_23 hA n).2.1, hBm n⟩
  -- limit points of `S_n` minimise `G`
  have hlimS : ∀ S, in_IsLimitPoint M.Sn S → ∀ y, M.Glim S ≤ M.Glim y := by
    rintro S ⟨φ, hφ, hS⟩ y
    have h1 := G_comp_tendsto hA hφ hS (fun k => hBm (φ k))
    have h2 : Tendsto (fun k => M.G (φ k) y) atTop (𝓝 (M.Glim y)) :=
      G_comp_tendsto hA hφ tendsto_const_nhds (B := y) fun _ => le_rfl
    exact le_of_tendsto_of_tendsto' h1 h2 fun k => (Sn_isLeast hA (φ k)).1 y
  refine ⟨?_, ?_, hlimS, fun S hS huniq => ?_, Glim_cconvex hA, fun s S ⟨φ, hφ, hs⟩ hS => ?_⟩
  · obtain ⟨l, -, φ, hφ, hl⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc a₀ Bm) hsI
    exact ⟨φ, hφ, l, hl⟩
  · obtain ⟨l, -, φ, hφ, hl⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc a₀ Bm) hSI
    exact ⟨φ, hφ, l, hl⟩
  · refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨l, -, ψ, hψ, hl⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc a₀ Bm)
      (fun n => hSI (ns n))
    refine ⟨ψ, ?_⟩
    have hlim : in_IsLimitPoint M.Sn l := ⟨ns ∘ ψ, hns.comp hψ.tendsto_atTop, hl⟩
    rw [← huniq l (hlimS l hlim)]
    exact hl
  · have h1 := G_comp_tendsto hA hφ hs (fun k => (hsI (φ k)).2)
    have h2 : Tendsto (fun k => M.c + M.G (φ k) (M.Sn (φ k))) atTop (𝓝 (M.c + M.Glim S)) :=
      ((G_Sn_tendsto hA hS).comp hφ).const_add _
    have e : (fun k => M.G (φ k) (M.sn (φ k))) = fun k => M.c + M.G (φ k) (M.Sn (φ k)) :=
      funext fun k => (eq_8_23 hA (φ k)).1
    change Tendsto (fun k => M.G (φ k) (M.sn (φ k))) _ _ at h1
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2

/-- **Exercise 8.4** (Miao, p. 288): the proof of Proposition 8.5.3 (first part). -/
theorem ex_8_4 (hA : M.Assumption851) :
    (∀ S, in_IsLimitPoint M.Sn S → ∀ y, M.Glim S ≤ M.Glim y) ∧ in_CConvex M.c M.Glim :=
  ⟨(proposition_8_5_3 hA).2.2.1, Glim_cconvex hA⟩

/-- For a limit point `s` of `{s_n}`, `G(x) ≥ c + G(S)` for all `x ≤ s` (ordering up to `S` is
optimal there), `S` a minimiser of `G`. -/
theorem Glim_ge_of_le (hA : M.Assumption851) {s S : ℝ} (hs : in_IsLimitPoint M.sn s)
    (hS : ∀ y, M.Glim S ≤ M.Glim y) {x : ℝ} (hx : x ≤ s) : M.c + M.Glim S ≤ M.Glim x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, (proposition_8_5_3 hA).2.2.2.2.2 s S hs hS]
  by_contra hcon
  push Not at hcon
  obtain ⟨φ, hφ, hsφ⟩ := hs
  have hG : Tendsto (fun n => M.G n x) atTop (𝓝 (M.Glim x)) :=
    G_comp_tendsto hA tendsto_id tendsto_const_nhds (B := x) fun _ => le_rfl
  have hev : ∀ᶠ n in atTop, M.G n x < M.c + M.G n (M.Sn n) := by
    have := (hG.sub ((G_Sn_tendsto hA hS).const_add M.c)).eventually
      (gt_mem_nhds (sub_neg.2 hcon))
    filter_upwards [this] with n hn
    linarith
  have h1 : ∀ᶠ k in atTop, M.sn (φ k) ≤ x := by
    filter_upwards [hφ.eventually hev] with k hk
    exact (sn_isLeast hA (φ k)).2 hk.le
  have h2 : ∀ᶠ k in atTop, x < M.sn (φ k) := hsφ.eventually (lt_mem_nhds h)
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  linarith

/-- Proposition 8.5.3: when `c > 0`, every limit point `s` of `{s_n}` lies strictly below every
minimiser `S` of `G`. -/
theorem ex_8_4_lt (hA : M.Assumption851) (hc : 0 < M.c) {s S : ℝ}
    (hs : in_IsLimitPoint M.sn s) (hS : ∀ y, M.Glim S ≤ M.Glim y) : s < S := by
  by_contra h
  push Not at h
  have := Glim_ge_of_le hA hs hS h
  linarith

/-- **Proposition 8.5.3** (Miao, p. 275), the policy (**Exercise 8.4**): for a limit point `s`
of `{s_n}` and a minimiser `S ≥ s` of `G` (e.g. a limit point of `{S_n}`; `S ≥ s` is automatic
when `c > 0`), the (s, S) policy `d(x) = S − x` for `x ≤ s`, `d(x) = 0` for `x > s`, is optimal
for the infinite-horizon problem: it attains the minimum in the Bellman equation (8.21). -/
theorem ex_8_4_policy (hA : M.Assumption851) {s S : ℝ} (hs : in_IsLimitPoint M.sn s)
    (hS : ∀ y, M.Glim S ≤ M.Glim y) (hsS : s ≤ S) (x : ℝ) :
    M.f x = M.TT M.f (in_ssPolicy s S x) x ∧
      ∀ y, x ≤ y → M.TT M.f (in_ssPolicy s S x) x ≤ M.TT M.f y x := by
  have hGs := (proposition_8_5_3 hA).2.2.2.2.2 s S hs hS
  have hc := hA.c_nonneg
  have hGc := Glim_cont hA
  have hGcc := Glim_cconvex hA
  have hmin : ∀ y, M.Glim (in_Sbar M.Glim) ≤ M.Glim y :=
    (in_Sbar_isLeast hGc (Glim_coercive hA)).1
  have hmS : M.Glim (in_Sbar M.Glim) = M.Glim S := le_antisymm (hmin S) (hS _)
  have hsb := in_sbar_isLeast hc hGc (Glim_coercive hA)
  rw [hmS] at hsb
  have hsbs : in_sbar M.c M.Glim ≤ s := hsb.2 (le_of_eq hGs)
  have hopt : ∀ y, x ≤ y → M.TT M.f (in_ssPolicy s S x) x ≤ M.TT M.f y x := by
    intro y hxy
    rw [TT_eq, TT_eq]
    change in_fix M.c x _ + M.Glim _ - _ ≤ in_fix M.c x y + M.Glim y - _
    unfold in_ssPolicy
    split_ifs with hx
    · rcases eq_or_lt_of_le (hx.trans hsS) with h | h
      · rw [h, in_fix_self]
        linarith [in_fix_nonneg hc S y, hS y]
      · rw [in_fix_of_lt _ h]
        rcases eq_or_lt_of_le hxy with h' | h'
        · rw [← h', in_fix_self]
          linarith [Glim_ge_of_le hA hs hS hx]
        · rw [in_fix_of_lt _ h']
          linarith [hS y]
    · push Not at hx
      rcases eq_or_lt_of_le hxy with h' | h'
      · rw [h']
      · rw [in_fix_self, in_fix_of_lt _ h']
        linarith [in_ss_key hc hGcc hS hsb (hsbs.trans hx.le) hxy]
  refine ⟨?_, hopt⟩
  have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
  have hmem : in_ssPolicy s S x ∈ Set.Ici x := by
    unfold in_ssPolicy; split_ifs with h
    · exact Set.mem_Ici.2 (h.trans hsS)
    · exact Set.mem_Ici.2 le_rfl
  have hB : BddBelow (Set.range fun y : Set.Ici x => M.TT M.f y x) :=
    ⟨M.TT M.f (in_ssPolicy s S x) x, by rintro _ ⟨y, rfl⟩; exact hopt y y.2⟩
  rw [proposition_8_5_2 hA x]
  unfold T
  exact le_antisymm (ciInf_le hB ⟨_, hmem⟩) (le_ciInf fun y => hopt y y.2)

end INModel

end Miao.Applications
