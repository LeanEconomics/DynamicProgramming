/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.INInfinite

/-!
# Uniqueness for the inventory Bellman equation: Proposition 8.5.4

Miao, §8.5, p. 275. The book omits the proof ("nontrivial", Iglehart 1963); we give one.

A *solution* of (8.21) is a function `F` with every `z ↦ F(y − z)` integrable and
`F(x) = inf_{y ≥ x} T(y, x, F)` (`IsGLB`, so the infimum need not be attained).

* `P_of_bellman`: a solution satisfies `F(w) ≤ c + pa + F(w + a)` for `a ≥ 0`.
* `dominate`: for any such function, orders above `max(x, R)` are dominated by orders in
  `[x, max(x, R)]`, where `R` depends only on `L` and `c` (if `x ≥ ζ = argmin L` not ordering
  is as good; if `x < ζ` ordering up to `ζ` is as good). This also explains Lemma 8.5.5.
* **Proposition 8.5.4** (`proposition_8_5_4`): a solution that is bounded on finite intervals
  and bounded below on some `(−∞, y₀]` equals `f`. The proof compares `F` and `f` on
  `(−∞, B]`: `f − F ≤ β(f − F)⁺` using near-optimal orders of `F` (which may be taken
  `≤ B`), and `F − f ≤ β(F − f)⁺` using the optimal (s, S) policy of `f`; both differences are
  bounded above on `(−∞, B]` because `F(x) + px` and `f(x) + px` are bounded there.

**Departure.** The book does not say in which sense `F` solves (8.21); we require `EF(y − z)`
to exist (integrability), as (8.21) needs, and read "min" as "inf". Upper boundedness on finite
intervals is not used.
-/

namespace Miao.Applications

namespace INModel

open MeasureTheory Filter Topology

variable {M : INModel}

/-- A solution of (8.21) satisfies `F(w) ≤ c + pa + F(w + a)` for `a ≥ 0`. -/
theorem P_of_bellman (hA : M.Assumption851) {F : ℝ → ℝ}
    (hbell : ∀ x, IsGLB (Set.range fun y : Set.Ici x => M.TT F y x) (F x)) {w a : ℝ}
    (ha : 0 ≤ a) : F w ≤ M.c + M.p * a + F (w + a) := by
  have hlb : F w - M.c - M.p * a ∈ lowerBounds (Set.range fun y : Set.Ici (w + a) =>
      M.TT F y (w + a)) := by
    rintro _ ⟨y, rfl⟩
    have hy : w ≤ (y : ℝ) := by linarith [Set.mem_Ici.1 y.2]
    have h1 : F w ≤ M.TT F y w := (hbell w).1 ⟨⟨y, hy⟩, rfl⟩
    have h2 := in_fix_le hA.c_nonneg w y
    have h3 := in_fix_nonneg hA.c_nonneg (w + a) y
    unfold TT at h1 ⊢
    nlinarith
  have := (hbell (w + a)).2 hlb
  linarith

/-- `L` is nondecreasing to the right of a minimiser `ζ`. -/
theorem L_mono_right (hA : M.Assumption851) {ζ : ℝ} (hζ : ∀ y, M.L ζ ≤ M.L y) {x y : ℝ}
    (hζx : ζ ≤ x) (hxy : x ≤ y) : M.L x ≤ M.L y := by
  rcases eq_or_lt_of_le hζx with h | h
  · rw [← h]; exact hζ y
  rcases eq_or_lt_of_le hxy with h' | h'
  · rw [h']
  have key := hA.L_convex.secant_mono (Set.mem_univ ζ) (Set.mem_univ x) (Set.mem_univ y)
    (ne_of_gt h) (ne_of_gt (h.trans h')) hxy
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at key
  nlinarith [hζ x]

/-- Domination of large orders: for `F` with the `P`-property, every order `y > max(x, R)`
is beaten by some `y′ ∈ [x, max(x, R)]`. -/
theorem dominate (hA : M.Assumption851) {F : ℝ → ℝ}
    (hP : ∀ w a, 0 ≤ a → F w ≤ M.c + M.p * a + F (w + a))
    (hint : ∀ y, Integrable (fun z => F (y - z)) M.φ) {ζ R : ℝ} (hζ : ∀ y, M.L ζ ≤ M.L y)
    (hζR : ζ ≤ R) (hR : ∀ y, R ≤ y → M.L ζ + M.c ≤ M.L y) {x y : ℝ} (hxy : x ≤ y) :
    ∃ y', x ≤ y' ∧ y' ≤ max x R ∧ M.TT F y' x ≤ M.TT F y x := by
  rcases le_or_gt y (max x R) with h | h
  · exact ⟨y, hxy, h, le_rfl⟩
  have hxy' : x < y := lt_of_le_of_lt (le_max_left _ _) h
  have hRy : R < y := lt_of_le_of_lt (le_max_right _ _) h
  rcases le_or_gt ζ x with hζx | hζx
  · refine ⟨x, le_rfl, le_max_left _ _, ?_⟩
    rw [TT_eq, TT_eq, in_fix_self, in_fix_of_lt _ hxy']
    have := Gf_diff hA hP hint hxy
    have := L_mono_right hA hζ hζx hxy
    linarith
  · refine ⟨ζ, hζx.le, hζR.trans (le_max_right _ _), ?_⟩
    rw [TT_eq, TT_eq, in_fix_of_lt _ hζx, in_fix_of_lt _ hxy']
    have := Gf_diff hA hP hint (hζR.trans hRy.le)
    have := hR y hRy.le
    linarith

/-- **Proposition 8.5.4** (Miao, p. 275). Under Assumption 8.5.1, if `F` solves the Bellman
equation (8.21), is bounded on every finite interval and `inf_{x ≤ y₀} F(x) > −∞` for some
`y₀`, then `F = f`. -/
theorem proposition_8_5_4 (hA : M.Assumption851) {F : ℝ → ℝ}
    (hint : ∀ y, Integrable (fun z => F (y - z)) M.φ)
    (hbell : ∀ x, IsGLB (Set.range fun y : Set.Ici x => M.TT F y x) (F x))
    (hbdd : ∀ u v, BddBelow (F '' Set.Icc u v) ∧ BddAbove (F '' Set.Icc u v))
    (hlow : ∃ y₀, BddBelow (F '' Set.Iic y₀)) : F = M.f := by
  have := hA.prob
  have hP : ∀ w a, 0 ≤ a → F w ≤ M.c + M.p * a + F (w + a) := fun w a ha =>
    P_of_bellman hA hbell ha
  obtain ⟨ζ, hζ⟩ := in_exists_min (L_cont hA) hA.L_coercive
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1
    (hA.L_coercive.2.eventually (eventually_ge_atTop (M.L ζ + M.c)))
  set R := max R₀ ζ
  have hR : ∀ y, R ≤ y → M.L ζ + M.c ≤ M.L y := fun y hy => hR₀ y ((le_max_left _ _).trans hy)
  have hζR : ζ ≤ R := le_max_right _ _
  have hgf := good_f hA
  -- the (s, S) policy of `f`
  obtain ⟨φ, hφ, s, hs⟩ := (proposition_8_5_3 hA).1
  have hslim : in_IsLimitPoint M.sn s := ⟨φ, hφ.tendsto_atTop, hs⟩
  set Sb := in_Sbar M.Glim
  have hSb : ∀ y, M.Glim Sb ≤ M.Glim y := (in_Sbar_isLeast (Glim_cont hA) (Glim_coercive hA)).1
  set S := max s Sb
  have hS : ∀ y, M.Glim S ≤ M.Glim y := by
    rcases le_or_gt s Sb with h | h
    · rw [show S = Sb from max_eq_right h]; exact hSb
    · rw [show S = s from max_eq_left h.le]
      rcases eq_or_lt_of_le hA.c_nonneg with hc | hc
      · have := (proposition_8_5_3 hA).2.2.2.2.2 s Sb hslim hSb
        rw [← hc, zero_add] at this
        rw [this]; exact hSb
      · exact absurd (ex_8_4_lt hA hc hslim hSb) (not_lt.2 h.le)
  have hsS : s ≤ S := le_max_left _ _
  have m1 : ∀ y, M.G 1 (M.Sn 1) ≤ M.L y + M.p * y := fun y => by
    rw [← G_one]; exact (Sn_isLeast hA 1).1 y
  funext x
  set B := max x (max R S)
  have hRB : R ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hSB : S ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  -- a lower bound for `F` on `(−∞, B]`
  obtain ⟨y₀, ℓ₀, hℓ₀⟩ := hlow
  obtain ⟨ℓ₁, hℓ₁⟩ := (hbdd y₀ B).1
  set ℓ := min ℓ₀ ℓ₁
  have hFℓ : ∀ w, w ≤ B → ℓ ≤ F w := fun w hw => by
    rcases le_or_gt w y₀ with h | h
    · exact (min_le_left _ _).trans (hℓ₀ ⟨w, Set.mem_Iic.2 h, rfl⟩)
    · exact (min_le_right _ _).trans (hℓ₁ ⟨w, ⟨h.le, hw⟩, rfl⟩)
  have hFint : ∀ y, y ≤ B → ℓ ≤ ∫ z, F (y - z) ∂M.φ := fun y hy => by
    have := integral_mono_ae (integrable_const ℓ) (hint y) (by
      filter_upwards [hA.demand_nonneg] with z hz
      exact hFℓ (y - z) (by linarith))
    simpa using this
  have hFlow : ∀ w, w ≤ B → M.G 1 (M.Sn 1) + M.β * ℓ ≤ F w + M.p * w := by
    intro w hw
    have hlb : M.G 1 (M.Sn 1) + M.β * ℓ - M.p * w ∈
        lowerBounds (Set.range fun y : Set.Ici w => M.TT F y w) := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', hwy', hy'R, hle⟩ := dominate hA hP hint hζ hζR hR (Set.mem_Ici.1 y.2)
      refine le_trans ?_ hle
      have hy'B : y' ≤ B := hy'R.trans (max_le hw hRB)
      rw [TT_eq]
      unfold Gf
      have := mul_le_mul_of_nonneg_left (hFint y' hy'B) hA.β_pos.le
      linarith [in_fix_nonneg hA.c_nonneg w y', m1 y']
    linarith [(hbell w).2 hlb]
  have hFup : ∀ w, w ≤ B → F w + M.p * w ≤ M.c + M.Gf F B := by
    intro w hw
    have : F w ≤ M.TT F B w := (hbell w).1 ⟨⟨B, hw⟩, rfl⟩
    rw [TT_eq] at this
    linarith [in_fix_le hA.c_nonneg w B]
  have hfup : ∀ w, w ≤ B → M.f w + M.p * w ≤ M.c + M.Glim B := by
    intro w hw
    have := f_le_TT hA hw
    rw [TT_eq] at this
    change M.f w ≤ in_fix M.c w B + M.Glim B - M.p * w at this
    linarith [in_fix_le hA.c_nonneg w B]
  have hflow : ∀ w, M.Glim S ≤ M.f w + M.p * w := by
    intro w
    have := (ex_8_4_policy hA hslim hS hsS w).1
    rw [TT_eq] at this
    change M.f w = in_fix M.c w _ + M.Glim _ - M.p * w at this
    linarith [in_fix_nonneg hA.c_nonneg w (in_ssPolicy s S w), hS (in_ssPolicy s S w)]
  have hβ0 := hA.β_pos.le
  have hβpow : Tendsto (fun k : ℕ => M.β ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hA.β_lt
  -- `f − F ≤ 0` on `(−∞, B]`
  set E₀ := max 0 (M.c + M.Glim B - (M.G 1 (M.Sn 1) + M.β * ℓ))
  have hE₀ : ∀ k, ∀ w, w ≤ B → M.f w - F w ≤ M.β ^ k * E₀ := by
    intro k
    induction k with
    | zero =>
      intro w hw
      simp only [pow_zero, one_mul]
      exact (by linarith [hfup w hw, hFlow w hw] : M.f w - F w ≤ _ ).trans (le_max_right _ _)
    | succ k ih =>
      intro w hw
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨_, ⟨y, rfl⟩, -, hlt⟩ := (hbell w).exists_between (lt_add_of_pos_right (F w) hε)
      obtain ⟨y', hwy', hy'R, hle⟩ := dominate hA hP hint hζ hζR hR (Set.mem_Ici.1 y.2)
      have hy'B : y' ≤ B := hy'R.trans (max_le hw hRB)
      have h1 := f_le_TT hA hwy'
      have hI : ∫ z, (M.f (y' - z) - F (y' - z)) ∂M.φ ≤ M.β ^ k * E₀ := by
        have := integral_mono_ae ((int_f hA y').sub (hint y'))
          (integrable_const (M.β ^ k * E₀)) (by
            filter_upwards [hA.demand_nonneg] with z hz
            exact ih (y' - z) (by linarith))
        simpa using this
      rw [integral_sub (int_f hA y') (hint y')] at hI
      have e : M.TT M.f y' w - M.TT F y' w =
          M.β * ((∫ z, M.f (y' - z) ∂M.φ) - ∫ z, F (y' - z) ∂M.φ) := by unfold TT; ring
      have := mul_le_mul_of_nonneg_left hI hβ0
      rw [pow_succ]
      nlinarith
  -- `F − f ≤ 0` on `(−∞, B]`
  set E₁ := max 0 (M.c + M.Gf F B - M.Glim S)
  have hE₁ : ∀ k, ∀ w, w ≤ B → F w - M.f w ≤ M.β ^ k * E₁ := by
    intro k
    induction k with
    | zero =>
      intro w hw
      simp only [pow_zero, one_mul]
      exact (by linarith [hFup w hw, hflow w] : F w - M.f w ≤ _ ).trans (le_max_right _ _)
    | succ k ih =>
      intro w hw
      obtain ⟨heq, -⟩ := ex_8_4_policy hA hslim hS hsS w
      set y := in_ssPolicy s S w
      have hwy : w ≤ y := by
        unfold y in_ssPolicy; split_ifs with h
        · exact h.trans hsS
        · exact le_rfl
      have hyB : y ≤ B := by
        unfold y in_ssPolicy; split_ifs
        · exact hSB
        · exact hw
      have h1 : F w ≤ M.TT F y w := (hbell w).1 ⟨⟨y, hwy⟩, rfl⟩
      have hI : ∫ z, (F (y - z) - M.f (y - z)) ∂M.φ ≤ M.β ^ k * E₁ := by
        have := integral_mono_ae ((hint y).sub (int_f hA y))
          (integrable_const (M.β ^ k * E₁)) (by
            filter_upwards [hA.demand_nonneg] with z hz
            exact ih (y - z) (by linarith))
        simpa using this
      rw [integral_sub (hint y) (int_f hA y)] at hI
      have e : M.TT F y w - M.TT M.f y w =
          M.β * ((∫ z, F (y - z) ∂M.φ) - ∫ z, M.f (y - z) ∂M.φ) := by unfold TT; ring
      have := mul_le_mul_of_nonneg_left hI hβ0
      rw [pow_succ]
      nlinarith
  have hx : x ≤ B := le_max_left _ _
  have h1 : M.f x - F x ≤ 0 :=
    ge_of_tendsto' (by simpa using hβpow.mul_const E₀) fun k => hE₀ k x hx
  have h2 : F x - M.f x ≤ 0 :=
    ge_of_tendsto' (by simpa using hβpow.mul_const E₁) fun k => hE₁ k x hx
  linarith

end INModel

end Miao.Applications
