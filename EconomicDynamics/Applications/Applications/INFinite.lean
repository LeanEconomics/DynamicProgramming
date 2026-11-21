/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INModel
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Finite-horizon inventory problems: bounds on `s_n`, `S_n` (Lemmas 8.5.4–8.5.6)

Miao, §8.5, pp. 264–272.

* **Figure 8.5** (`fig_8_5`): the one-period problem, `G_1(y) = L(y) + py` (`G_one`).
* `fn_mono`: `f_n ≤ f_{n+1}` (`T` is monotone and `f₀ = 0 ≤ f₁`).
* (8.27)(i) (`eq_8_27`): `f_n` has derivative `−p` left of `s_n` and `−p + G′_n(x)` right of
  `s_n` (where `G_n` is differentiable), with these one-sided derivatives at `s_n`.
* **Exercise 8.3** (`ex_8_3`): `G_n` is strictly decreasing on `(−∞, S_1]` for every `n`
  (the difference form of the book's hint "`G′_n(x) < 0` for `x < S_1`"), hence
  **Lemma 8.5.4** (`lemma_8_5_4`): `S_1 ≤ S_n`.
* **Lemma 8.5.5** (`lemma_8_5_5`): `S_n ≤ M` for a bound `M` independent of `n`, via
  `G_n(x + a) − G_n(x) ≥ L(x + a) − L(x) − c` (`eq_p271`).
* **Lemma 8.5.6** (`lemma_8_5_6`): `2s_1 − S_1 < s_n` when `c > 0`, via the slope bound
  `G_n(x) − G_n(x′) ≥ c(x′ − x)/(S_1 − s_1)` for `x < x′ ≤ s_1` (`lemma_8_5_6_slope`).
  For `c = 0` only `2s_1 − S_1 ≤ s_n` holds (`lemma_8_5_6_le`); the strict inequality fails
  (`lemma_8_5_6_counterexample`: `c = p = 0`, `L(y) = y²`, demand `0`).

**Departures.** (1) All proofs are derivative-free: the book's derivative hints for Lemmas
8.5.4 and 8.5.6 are replaced by difference quotients, so Assumption 8.5.2 is not needed for
these lemmas (and they hold for every `n ≥ 1`, with `S_0 = S_1` by our convention
`G_0 = G_1`). (2) Lemma 8.5.6 is false for `c = 0` (above). (3) The book's proof of Lemma 8.5.6
writes "`f′_n(x) ≤ −c` for `x ≤ s_1`"; what is used is only that `f_n` is nonincreasing there.
-/

namespace Miao.Applications

namespace INModel

open MeasureTheory Filter Topology

variable {M : INModel}

/-- `G_1(y) = L(y) + py` (Miao, p. 264). -/
theorem G_one (y : ℝ) : M.G 1 y = M.L y + M.p * y := by
  simp [G, Gf, fn_zero]

/-- `G_0 = G_1` (our convention, `0 − 1 = 0` in `ℕ`). -/
theorem G_zero : M.G 0 = M.G 1 := rfl

/-- `Gf f(y) = G_1(y) + βEf(y − z)`. -/
theorem Gf_eq_G_one (f : ℝ → ℝ) (y : ℝ) :
    M.Gf f y = M.G 1 y + M.β * ∫ z, f (y - z) ∂M.φ := by
  rw [G_one]; rfl

/-- `G_1 = L + p·id` is convex. -/
theorem G_one_convex (hA : M.Assumption851) : ConvexOn ℝ Set.univ (M.G 1) := by
  have : M.G 1 = fun y => M.L y + M.p * y := funext G_one
  rw [this]
  exact hA.L_convex.add (convexOn_id convex_univ |>.smul hA.p_nonneg)

/-- `G_1` is strictly decreasing on `(−∞, S_1]` (convex, `S_1` its smallest minimiser). -/
theorem G_one_strictAnti (hA : M.Assumption851) {x y : ℝ} (hxy : x < y) (hy : y ≤ M.Sn 1) :
    M.G 1 y < M.G 1 x := by
  have hS := Sn_isLeast hA 1
  have hx : M.G 1 (M.Sn 1) < M.G 1 x := by
    by_contra h
    push Not at h
    have : M.Sn 1 ≤ x := hS.2 fun y' => h.trans (hS.1 y')
    linarith
  rcases eq_or_lt_of_le hy with h | h
  · rw [h]; exact hx
  · have key := (G_one_convex hA).secant_mono (Set.mem_univ x) (Set.mem_univ y)
      (Set.mem_univ (M.Sn 1)) (ne_of_gt hxy) (ne_of_gt (hxy.trans h)) h.le
    have hneg : (M.G 1 (M.Sn 1) - M.G 1 x) / (M.Sn 1 - x) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    have := key.trans_lt hneg
    rw [div_neg_iff] at this
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith

/-- **Figure 8.5** (Miao, p. 264), the one-period problem with `c > 0`: `S = S_1` minimises
`L(y) + py`; `L(S) + c + pS = L(s) + ps`; for `x < s` ordering up to `S` is strictly better;
for `x > s` and `y ≥ x` not ordering is strictly better. -/
theorem fig_8_5 (hA : M.Assumption851) (hc : 0 < M.c) :
    (∀ y, M.L (M.Sn 1) + M.p * M.Sn 1 ≤ M.L y + M.p * y) ∧
      M.L (M.Sn 1) + M.c + M.p * M.Sn 1 = M.L (M.sn 1) + M.p * M.sn 1 ∧
      (∀ x, x < M.sn 1 → M.L (M.Sn 1) + M.c + M.p * M.Sn 1 < M.L x + M.p * x) ∧
      ∀ x y, M.sn 1 < x → x ≤ y → M.L x + M.p * x < M.L y + M.c + M.p * y := by
  have hS := Sn_isLeast hA 1
  have hs := sn_isLeast hA 1
  have h23 := eq_8_23 hA 1
  simp only [G_one] at hS hs h23
  refine ⟨fun y => hS.1 y, by linarith [h23.1], fun x hx => ?_, fun x y hx hxy => ?_⟩
  · have := in_ss_gt (sn_isLeast hA 1) hx
    simp only [G_one] at this
    linarith
  · rcases le_or_gt x (M.Sn 1) with hxS | hxS
    · have := G_one_strictAnti hA hx hxS
      have hy := (Sn_isLeast hA 1).1 y
      have he := (eq_8_23 hA 1).1
      simp only [G_one] at this hy he
      linarith
    · -- beyond `S_1` the convex `G_1` is nondecreasing
      have hmono : M.G 1 x ≤ M.G 1 y := by
        rcases eq_or_lt_of_le hxy with h | h
        · rw [h]
        have key := (G_one_convex hA).secant_mono (Set.mem_univ (M.Sn 1)) (Set.mem_univ x)
          (Set.mem_univ y) (ne_of_gt hxS) (ne_of_gt (hxS.trans h)) hxy
        have h0 := (Sn_isLeast hA 1).1 y
        rw [div_le_div_iff₀ (by linarith) (by linarith)] at key
        nlinarith
      simp only [G_one] at hmono
      linarith

/-- `f_n ≤ f_{n+1}` (Miao, p. 274: "`{f_n(x)}` is an increasing sequence"). -/
theorem fn_mono (hA : M.Assumption851) : ∀ n x, M.fn n x ≤ M.fn (n + 1) x
  | 0, x => (good_fn hA 1).2.1 x
  | n + 1, x => by
    have := hA.prob
    have ih := fn_mono hA n
    have : Nonempty (Set.Ici x) := ⟨⟨x, Set.mem_Ici.2 le_rfl⟩⟩
    change M.T (M.fn n) x ≤ M.T (M.fn (n + 1)) x
    refine ciInf_mono ⟨0, ?_⟩ fun y => ?_
    · rintro _ ⟨y, rfl⟩
      have := T_le_TT hA (good_fn hA n).2.1 (Set.mem_Ici.1 y.2) (x := x)
      exact ((good_fn hA (n + 1)).2.1 x).trans (M.fn_succ n ▸ this)
    · unfold TT
      have := integral_mono (int_fn hA n (y : ℝ)) (int_fn hA (n + 1) (y : ℝ))
        fun z => ih ((y : ℝ) - z)
      have := mul_le_mul_of_nonneg_left this hA.β_pos.le
      linarith

/-- `f_n(x) = −px + G_n(max(x, s_n))` (`n ≥ 1`). -/
theorem fn_eq (hA : M.Assumption851) (n : ℕ) (x : ℝ) :
    M.fn (n + 1) x = -M.p * x + M.G (n + 1) (max x (M.sn (n + 1))) :=
  T_eq hA (good_fn hA n) x

/-- Miao, (8.27)(i), p. 270: `f_n` is differentiable off `s_n`, with `f′_n = −p` for
`x < s_n` and `f′_n = −p + G′_n(x)` for `x > s_n` (where `G_n` is differentiable); at `s_n`
the left derivative is `−p` and the right derivative is `−p + G′_n(s_n)` (`n ≥ 1`). -/
theorem eq_8_27 (hA : M.Assumption851) (n : ℕ) :
    (∀ x, x < M.sn (n + 1) → HasDerivAt (M.fn (n + 1)) (-M.p) x) ∧
    (∀ x, M.sn (n + 1) < x → DifferentiableAt ℝ (M.G (n + 1)) x →
      HasDerivAt (M.fn (n + 1)) (-M.p + deriv (M.G (n + 1)) x) x) ∧
    HasDerivWithinAt (M.fn (n + 1)) (-M.p) (Set.Iic (M.sn (n + 1))) (M.sn (n + 1)) ∧
    (DifferentiableAt ℝ (M.G (n + 1)) (M.sn (n + 1)) →
      HasDerivWithinAt (M.fn (n + 1)) (-M.p + deriv (M.G (n + 1)) (M.sn (n + 1)))
        (Set.Ici (M.sn (n + 1))) (M.sn (n + 1))) := by
  set s := M.sn (n + 1)
  have hlin : ∀ x K, HasDerivAt (fun y => -M.p * y + K) (-M.p) x := fun x K => by
    simpa using (HasDerivAt.const_mul (-M.p) (hasDerivAt_id x)).add_const K
  refine ⟨fun x hx => ?_, fun x hx hd => ?_, ?_, fun hd => ?_⟩
  · refine (hlin x (M.G (n + 1) s)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [fn_eq hA, max_eq_right (Set.mem_Iio.1 hy).le]
  · have h := (HasDerivAt.const_mul (-M.p) (hasDerivAt_id x)).add hd.hasDerivAt
    simp only [mul_one] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [fn_eq hA, max_eq_left (Set.mem_Ioi.1 hy).le]
    rfl
  · refine (hlin s (M.G (n + 1) s)).hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · rw [fn_eq hA, max_eq_right (Set.mem_Iic.1 hy)]
    · rw [fn_eq hA, max_self]
  · have h := (HasDerivAt.const_mul (-M.p) (hasDerivAt_id s)).add hd.hasDerivAt
    simp only [mul_one] at h
    refine h.hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · rw [fn_eq hA, max_eq_left (Set.mem_Ici.1 hy)]; rfl
    · rw [fn_eq hA, max_self]; rfl

/-- **Exercise 8.3** (Miao, p. 288), the key step of Lemma 8.5.4: for every `n`, `G_n` is
strictly decreasing on `(−∞, S_1]` (the book's hint: `G′_n(x) < 0` for `x < S_1`), and `f_n` is
nonincreasing there. -/
theorem ex_8_3 (hA : M.Assumption851) :
    ∀ n, (∀ x y, x < y → y ≤ M.Sn 1 → M.G (n + 1) y < M.G (n + 1) x) ∧
      AntitoneOn (M.fn n) (Set.Iic (M.Sn 1))
  | 0 => ⟨fun _ _ hxy hy => G_one_strictAnti hA hxy hy, fun _ _ _ _ _ => le_rfl⟩
  | n + 1 => by
    have := hA.prob
    obtain ⟨ih, -⟩ := ex_8_3 hA n
    have hanti : AntitoneOn (M.fn (n + 1)) (Set.Iic (M.Sn 1)) := by
      intro x hx y hy hxy
      have h1 : AntitoneOn (fun w => M.G (n + 1) (max w (M.sn (n + 1)))) (Set.Iic (M.Sn 1)) :=
        in_ss_antitoneOn fun a ha b hb hab => by
          rcases eq_or_lt_of_le hab with h | h
          · rw [h]
          · exact (ih a b h hb).le
      rw [fn_eq hA, fn_eq hA]
      have := h1 hx hy hxy
      simp only at this
      nlinarith [mul_le_mul_of_nonneg_left hxy hA.p_nonneg]
    refine ⟨fun x y hxy hy => ?_, hanti⟩
    rw [G_succ, Gf_eq_G_one, Gf_eq_G_one]
    have h1 := G_one_strictAnti hA hxy hy
    have h2 : ∫ z, M.fn (n + 1) (y - z) ∂M.φ ≤ ∫ z, M.fn (n + 1) (x - z) ∂M.φ := by
      refine integral_mono_ae (int_fn hA _ y) (int_fn hA _ x) ?_
      filter_upwards [hA.demand_nonneg] with z hz
      exact hanti (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 (by linarith)) (by linarith)
    have := mul_le_mul_of_nonneg_left h2 hA.β_pos.le
    linarith

/-- **Lemma 8.5.4** (Miao, p. 270). Under Assumption 8.5.1, `S_1 ≤ S_n` for all `n`
(Assumption 8.5.2 is not needed). -/
theorem lemma_8_5_4 (hA : M.Assumption851) (n : ℕ) : M.Sn 1 ≤ M.Sn n := by
  rcases n with _ | n
  · exact le_rfl
  by_contra h
  push Not at h
  have := (ex_8_3 hA n).1 _ _ h le_rfl
  have := (Sn_isLeast hA (n + 1)).1 (M.Sn 1)
  linarith

/-- Miao, p. 271 (proof of Lemma 8.5.5): `G_n(x + a) − G_n(x) ≥ L(x + a) − L(x) − c` for
`a ≥ 0`. -/
theorem eq_p271 (hA : M.Assumption851) (n : ℕ) {x a : ℝ} (ha : 0 ≤ a) :
    M.L (x + a) - M.L x - M.c ≤ M.G n (x + a) - M.G n x :=
  Gf_diff hA (good_fn hA _).2.2.1 (int_fn hA _) (by linarith)

/-- **Lemma 8.5.5** (Miao, p. 271). Under Assumption 8.5.1, `S_n ≤ M < ∞` for all `n`. -/
theorem lemma_8_5_5 (hA : M.Assumption851) : ∃ B, ∀ n, M.Sn n ≤ B := by
  obtain ⟨ζ, hζ⟩ := in_exists_min (L_cont hA) hA.L_coercive
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (hA.L_coercive.2.eventually (eventually_ge_atTop (M.L ζ + M.c)))
  refine ⟨max R ζ, fun n => ?_⟩
  by_contra h
  push Not at h
  have hd := eq_p271 hA n (x := ζ) (a := M.Sn n - ζ) (by linarith [le_max_right R ζ])
  rw [add_sub_cancel] at hd
  have hL := hR (M.Sn n) (by linarith [le_max_left R ζ])
  have hmin : ∀ y, M.G n ζ ≤ M.G n y := fun y => by
    linarith [(Sn_isLeast hA n).1 y]
  have := (Sn_isLeast hA n).2 hmin
  linarith [le_max_right R ζ]

/-- Miao, p. 272 (proof of Lemma 8.5.6): for `c > 0` and `x < x′ ≤ s_1`,
`G_n(x) − G_n(x′) ≥ c(x′ − x)/(S_1 − s_1)`, i.e. `G′_n ≤ −c/(S_1 − s_1)` on `(−∞, s_1]`. -/
theorem lemma_8_5_6_slope (hA : M.Assumption851) (hc : 0 < M.c) (n : ℕ) {x x' : ℝ}
    (hxx : x < x') (hx' : x' ≤ M.sn 1) :
    M.c / (M.Sn 1 - M.sn 1) * (x' - x) ≤ M.G (n + 1) x - M.G (n + 1) x' := by
  have := hA.prob
  obtain ⟨h23, hle, hlt⟩ := eq_8_23 hA 1
  have hlt := hlt hc
  have hD : 0 < M.Sn 1 - M.sn 1 := sub_pos.2 hlt
  -- the slope of the convex `G_1`
  have hcv := G_one_convex hA
  have k1 := hcv.secant_mono (Set.mem_univ x') (Set.mem_univ x) (Set.mem_univ (M.Sn 1))
    (ne_of_lt hxx) (ne_of_gt (lt_of_le_of_lt hx' hlt)) (by linarith)
  have k2 := hcv.secant_mono (Set.mem_univ (M.Sn 1)) (Set.mem_univ x') (Set.mem_univ (M.sn 1))
    (ne_of_lt (lt_of_le_of_lt hx' hlt)) (ne_of_lt hlt) hx'
  have e1 : (M.G 1 (M.Sn 1) - M.G 1 x') / (M.Sn 1 - x') =
      (M.G 1 x' - M.G 1 (M.Sn 1)) / (x' - M.Sn 1) := by
    rw [← neg_div_neg_eq]; ring_nf
  have e2 : (M.G 1 (M.sn 1) - M.G 1 (M.Sn 1)) / (M.sn 1 - M.Sn 1) =
      -(M.c / (M.Sn 1 - M.sn 1)) := by
    rw [h23]
    have hne : M.sn 1 - M.Sn 1 ≠ 0 := by linarith
    have hne' : M.Sn 1 - M.sn 1 ≠ 0 := by linarith
    field_simp
    ring
  have hslope : (M.G 1 x - M.G 1 x') / (x - x') ≤ -(M.c / (M.Sn 1 - M.sn 1)) := by
    rw [← e2]; exact k1.trans (e1 ▸ k2)
  rw [div_le_iff_of_neg (by linarith)] at hslope
  -- `βEf_n` is nonincreasing on `(−∞, s_1]`
  have hanti := (ex_8_3 hA n).2
  have hI : ∫ z, M.fn n (x' - z) ∂M.φ ≤ ∫ z, M.fn n (x - z) ∂M.φ := by
    refine integral_mono_ae (int_fn hA _ x') (int_fn hA _ x) ?_
    filter_upwards [hA.demand_nonneg] with z hz
    exact hanti (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 (by linarith)) (by linarith)
  rw [G_succ, Gf_eq_G_one, Gf_eq_G_one]
  have := mul_le_mul_of_nonneg_left hI hA.β_pos.le
  nlinarith

/-- **Lemma 8.5.6** (Miao, p. 272). Under Assumption 8.5.1 and `c > 0`, `2s_1 − S_1 < s_n` for
all `n` (Assumption 8.5.2 is not needed). -/
theorem lemma_8_5_6 (hA : M.Assumption851) (hc : 0 < M.c) (n : ℕ) :
    2 * M.sn 1 - M.Sn 1 < M.sn n := by
  obtain ⟨-, -, hlt⟩ := eq_8_23 hA 1
  have hlt := hlt hc
  rcases n with _ | n
  · change 2 * M.sn 1 - M.Sn 1 < M.sn 1; linarith
  by_contra h
  push Not at h
  set x := M.sn (n + 1)
  have hx : M.G (n + 1) x ≤ M.c + M.G (n + 1) (M.Sn (n + 1)) := (sn_isLeast hA (n + 1)).1
  have hD : 0 < M.Sn 1 - M.sn 1 := sub_pos.2 hlt
  have hsl := lemma_8_5_6_slope hA hc n (x := x) (x' := M.sn 1) (by linarith) le_rfl
  have hk : M.c ≤ M.c / (M.Sn 1 - M.sn 1) * (M.sn 1 - x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  have hs1 := (ex_8_3 hA n).1 _ _ hlt le_rfl
  have hmin := (Sn_isLeast hA (n + 1)).1 (M.Sn 1)
  linarith

/-- Lemma 8.5.6, non-strict form valid for every `c ≥ 0`: `2s_1 − S_1 ≤ s_n`. -/
theorem lemma_8_5_6_le (hA : M.Assumption851) (n : ℕ) : 2 * M.sn 1 - M.Sn 1 ≤ M.sn n := by
  rcases eq_or_lt_of_le hA.c_nonneg with hc | hc
  · have h1 : M.sn 1 = M.Sn 1 := by
      unfold sn Sn; rw [← hc]; exact in_sbar_eq_of_zero (G_cont hA 1) (G_coercive hA 1)
    have hn : M.sn n = M.Sn n := by
      unfold sn Sn; rw [← hc]; exact in_sbar_eq_of_zero (G_cont hA n) (G_coercive hA n)
    rw [h1, hn]
    linarith [lemma_8_5_4 hA n]
  · exact (lemma_8_5_6 hA hc n).le

/-- The model of `lemma_8_5_6_counterexample`: `β = 1/2`, `c = p = 0`, `L(y) = y²`, demand `0`. -/
noncomputable def cex856 : INModel where
  β := 1 / 2
  c := 0
  p := 0
  L := fun y => y ^ 2
  φ := Measure.dirac 0

theorem cex856_A : cex856.Assumption851 where
  β_pos := by norm_num [cex856]
  β_lt := by norm_num [cex856]
  c_nonneg := by simp [cex856]
  p_nonneg := by simp [cex856]
  prob := by unfold cex856; infer_instance
  demand_nonneg := by simp [cex856]
  demand_int := by unfold cex856; exact integrable_dirac (by simp)
  L_nonneg := fun y => by simp only [cex856]; positivity
  L_convex := by simpa [cex856] using (even_two.convexOn_pow (𝕜 := ℝ))
  L_coercive := by
    simp only [cex856]
    refine ⟨tendsto_atBot_atTop.2 fun b => ⟨-|b| - 1, fun y hy => ?_⟩,
      tendsto_atTop_atTop.2 fun b => ⟨|b| + 1, fun y hy => ?_⟩⟩
    · nlinarith [le_abs_self b, abs_nonneg b]
    · nlinarith [le_abs_self b, abs_nonneg b]
  G1_coercive := by
    simp only [cex856, zero_mul, add_zero]
    refine tendsto_atBot_atTop.2 fun b => ⟨-|b| - 1, fun y hy => ?_⟩
    nlinarith [le_abs_self b, abs_nonneg b]

/-- **Lemma 8.5.6 fails for `c = 0`** (Miao, p. 272): with `c = p = 0`, `L(y) = y²` and demand
`z = 0`, `s_1 = S_1 = s_2 = 0`, so `2s_1 − S_1 < s_2` is false. -/
theorem lemma_8_5_6_counterexample :
    cex856.Assumption851 ∧ ¬ (2 * cex856.sn 1 - cex856.Sn 1 < cex856.sn 2) := by
  have hA := cex856_A
  refine ⟨hA, ?_⟩
  have hc : cex856.c = 0 := rfl
  have hsS : ∀ n, cex856.sn n = cex856.Sn n := fun n => by
    unfold sn Sn; rw [hc]; exact in_sbar_eq_of_zero (G_cont hA n) (G_coercive hA n)
  have hGge : ∀ n y, y ^ 2 ≤ cex856.G n y := fun n y => by
    have h0 := (good_fn hA (n - 1)).2.1
    unfold G Gf
    have : 0 ≤ cex856.β * ∫ z, cex856.fn (n - 1) (y - z) ∂cex856.φ :=
      mul_nonneg hA.β_pos.le (integral_nonneg (μ := cex856.φ) fun z => h0 (y - z))
    simp only [cex856] at this ⊢
    linarith
  have hf1 : cex856.fn 1 0 = 0 := by
    refine le_antisymm ?_ ((good_fn hA 1).2.1 0)
    have := T_le_TT hA (good_fn hA 0).2.1 (le_refl (0 : ℝ))
    rw [← fn_succ] at this
    refine this.trans_eq ?_
    simp [TT, in_fix, cex856, fn_zero]
  have hG0 : ∀ n, n ≤ 2 → cex856.G n 0 = 0 := by
    intro n hn
    interval_cases n
    · rw [G_zero, G_one]; simp [cex856]
    · rw [G_one]; simp [cex856]
    · rw [G_succ]
      change (0 : ℝ) ^ 2 + 0 * 0 + 1 / 2 * ∫ z, cex856.fn 1 (0 - z) ∂(Measure.dirac 0) = 0
      rw [integral_dirac, sub_zero, hf1]
      norm_num
  have hS0 : ∀ n, n ≤ 2 → cex856.Sn n = 0 := by
    intro n hn
    have h1 := (Sn_isLeast hA n).1 0
    rw [hG0 n hn] at h1
    have := hGge n (cex856.Sn n)
    have : cex856.Sn n ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  rw [hsS 1, hsS 2, hS0 1 (by norm_num), hS0 2 (by norm_num)]
  norm_num

end INModel

end Miao.Applications
