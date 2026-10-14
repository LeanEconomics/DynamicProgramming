/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.TwoCycle

/-!
# The cyclical example: the two-cycle at `β = 0.1`, `α = 0.8`, `θ = 0.75`

SLP Exercise 6.7f–g, p. 158. Here `a = αθ = 3/5`, `b = α(1 − θ) = 1/5`, `β = 1/10`.

* **The Euler equations as polynomials** (`euler_iff_poly`). For `x, y ∈ (0, 1)`,
  `F_y(x, y) + βF_x(y, x) = 0` iff `P(x, y) = b⁵x³y² − (βa)⁵(1 − x)(1 − y)⁴ = 0`. Multiply by
  `y^{2/5}(1 − y)^{4/5}` and raise to the fifth power.
* **Exercise 6.7f (correction).** `(0.29, 0.18)` is not a two-cycle: no two-cycle has
  `x ∈ [0.28, 0.30]` and `y ∈ [0.17, 0.19]` (`ex_6_7f_book_box`). The two Euler equations force
  `x(1 − x)³ = y(1 − y)³`, which fails on that box.
  The optimal two-cycle has `x ∈ (0.483, 0.485)` and `y ∈ (0.087, 0.088)`; numerically it is
  `(0.4838, 0.0876)` (`ex_6_7f`). Its existence comes from the intermediate value theorem along
  the curve `P(x, y) = 0` (`polyRoot`), and its optimality from Exercise 6.7e.
* **Exercise 6.7g** (`ex_6_7g`). Linearize the stacked map `(k_{t+1}, k_t) ↦ (k_{t+3}, k_{t+2})`
  at the cycle. With the Euler equations, `J₁ = (1 − x)[(b − 1)/(1 − y) + (a − 1)/y]/b` and
  `K₁ = −a(1 − x)/(bx)`, and symmetrically for `J₂`, `K₂`. The two-step matrix has determinant
  `K₁K₂ = β⁻² = 100` and trace `16 + 5X + 5Y + 4XY > 101`, where `X = (1 − x)/x` and
  `Y = (1 − y)/y`. So its characteristic roots are real, one in `(0, 1)` (about `0.855`) and one
  above `1` (about `117`): one root is less than one in absolute value.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Filter Topology Real

/-- The Euler equation `F_y(x, y) + βF_x(y, x) = 0` as a polynomial:
`P(x, y) = (1/5)⁵x³y² − (3/50)⁵(1 − x)(1 − y)⁴`. -/
noncomputable def cycP (x y : ℝ) : ℝ :=
  (1 / 5) ^ 5 * x ^ 3 * y ^ 2 - (3 / 50) ^ 5 * (1 - x) * (1 - y) ^ 4

/-- `t^{k/5} = (t^{1/5})^k` for `t > 0`. -/
theorem rpow_fifth {t : ℝ} (ht : 0 < t) (k : ℕ) :
    t ^ ((k : ℝ) / 5) = (t ^ ((1 : ℝ) / 5)) ^ k := by
  rw [← rpow_natCast (t ^ ((1 : ℝ) / 5)), ← rpow_mul ht.le]
  congr 1; ring

/-- `(t^{1/5})⁵ = t` for `t > 0`. -/
theorem fifth_pow {t : ℝ} (ht : 0 < t) : (t ^ ((1 : ℝ) / 5)) ^ 5 = t := by
  rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num

/-- **The Euler equation as a polynomial.** For `x, y ∈ (0, 1)`,
`F_y(x, y) + βF_x(y, x) = 0 ↔ P(x, y) = 0` (`a = 3/5`, `b = 1/5`, `β = 1/10`). -/
theorem euler_iff_poly {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0 ↔ cycP x y = 0 := by
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  set u := x ^ ((1 : ℝ) / 5)
  set w := y ^ ((1 : ℝ) / 5)
  set r := (1 - x) ^ ((1 : ℝ) / 5)
  set s := (1 - y) ^ ((1 : ℝ) / 5)
  have hu : 0 < u := rpow_pos_of_pos hx.1 _
  have hw : 0 < w := rpow_pos_of_pos hy.1 _
  have hr : 0 < r := rpow_pos_of_pos hx1 _
  have hs : 0 < s := rpow_pos_of_pos hy1 _
  -- the four powers in terms of fifth roots
  have e1 : x ^ (3 / 5 : ℝ) = u ^ 3 := by
    rw [show (3 / 5 : ℝ) = ((3 : ℕ) : ℝ) / 5 by norm_num, rpow_fifth hx.1]
  have e2 : (1 - y) ^ (1 / 5 - 1 : ℝ) = (s ^ 4)⁻¹ := by
    rw [show (1 / 5 - 1 : ℝ) = -(((4 : ℕ) : ℝ) / 5) by norm_num, rpow_neg hy1.le,
      rpow_fifth hy1]
  have e3 : y ^ (3 / 5 - 1 : ℝ) = (w ^ 2)⁻¹ := by
    rw [show (3 / 5 - 1 : ℝ) = -(((2 : ℕ) : ℝ) / 5) by norm_num, rpow_neg hy.1.le,
      rpow_fifth hy.1]
  have e4 : (1 - x) ^ (1 / 5 : ℝ) = r := rfl
  have hE : cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x =
      (3 / 50 * r * s ^ 4 - 1 / 5 * u ^ 3 * w ^ 2) / (w ^ 2 * s ^ 4) := by
    simp only [cdFy, cdFx, e1, e2, e3, e4]
    field_simp
    ring
  have hx5 := fifth_pow hx.1
  have hy5 := fifth_pow hy.1
  have hr5 := fifth_pow hx1
  have hs5 := fifth_pow hy1
  rw [hE, div_eq_zero_iff, or_iff_left (by positivity), sub_eq_zero]
  -- `L = R ↔ L⁵ = R⁵` for positive `L`, `R`
  have hL : 0 < 1 / 5 * u ^ 3 * w ^ 2 := by positivity
  have hR : 0 < 3 / 50 * r * s ^ 4 := by positivity
  have h5 : (3 / 50 * r * s ^ 4) ^ 5 = (1 / 5 * u ^ 3 * w ^ 2) ^ 5 ↔ cycP x y = 0 := by
    have eR : (3 / 50 * r * s ^ 4) ^ 5 = (3 / 50) ^ 5 * r ^ 5 * (s ^ 5) ^ 4 := by ring
    have eL : (1 / 5 * u ^ 3 * w ^ 2) ^ 5 = (1 / 5) ^ 5 * (u ^ 5) ^ 3 * (w ^ 5) ^ 2 := by ring
    rw [eR, eL, hx5, hy5, hr5, hs5, cycP]
    constructor <;> intro h <;> linarith
  rw [← h5]
  exact (pow_left_inj₀ hR.le hL.le (by norm_num : (5 : ℕ) ≠ 0)).symm

/-! ### The curve `P(x, y) = 0` -/

theorem cycP_strictMono_y {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {y y' : ℝ} (hy : 0 ≤ y)
    (hyy' : y < y') (hy' : y' ≤ 1) : cycP x y < cycP x y' := by
  have hx3 : 0 < x ^ 3 := pow_pos hx.1 3
  have h1 : y ^ 2 < y' ^ 2 := by nlinarith
  have h2 : (1 - y') ^ 4 < (1 - y) ^ 4 := by
    have : 0 ≤ 1 - y' := by linarith
    exact pow_lt_pow_left₀ (by linarith) this (by norm_num)
  have h3 : 0 < 1 - x := by linarith [hx.2]
  simp only [cycP]
  nlinarith [mul_lt_mul_of_pos_left h1 hx3, mul_lt_mul_of_pos_left h2 h3]

/-- `P(y, x)` rises with `y ∈ [0, 1]` (for `x ∈ (0, 1)`). -/
theorem cycP_mono_x {x y y' : ℝ} (hy : 0 ≤ y) (hyy' : y ≤ y') : cycP y x ≤ cycP y' x := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h1 : y ^ 3 ≤ y' ^ 3 := pow_le_pow_left₀ hy hyy' 3
  have h4 : 0 ≤ (1 - x) ^ 4 := by positivity
  simp only [cycP]
  nlinarith [mul_le_mul_of_nonneg_right h1 hx2, mul_le_mul_of_nonneg_right hyy' h4]

/-- The root `y = φ(x)` of `P(x, ·)` in `[0, 1]`. -/
noncomputable def polyRoot (x : ℝ) : ℝ := sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ cycP x y}

theorem continuous_cycP : Continuous fun p : ℝ × ℝ => cycP p.1 p.2 := by
  unfold cycP; fun_prop

theorem polyRoot_spec {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    polyRoot x ∈ Ioo (0 : ℝ) 1 ∧ cycP x (polyRoot x) = 0 := by
  set S := {y | y ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ cycP x y}
  have hP0 : cycP x 0 < 0 := by simp only [cycP]; nlinarith [hx.1, hx.2]
  have hP1 : 0 < cycP x 1 := by simp only [cycP]; have := pow_pos hx.1 3; nlinarith
  have hne : S.Nonempty := ⟨1, ⟨by norm_num, le_rfl⟩, hP1.le⟩
  have hbdd : BddBelow S := ⟨0, fun y hy => hy.1.1⟩
  have hcl : IsClosed S := by
    have hc : Continuous fun y => cycP x y := by unfold cycP; fun_prop
    exact isClosed_Icc.inter (isClosed_le continuous_const hc)
  have hmem : polyRoot x ∈ S := hcl.csInf_mem hne hbdd
  -- the intermediate value theorem on `[0, φ(x)]`
  have hc : ContinuousOn (fun y => cycP x y) (Icc 0 (polyRoot x)) := by
    unfold cycP; fun_prop
  obtain ⟨y₀, hy₀, hy₀P⟩ := intermediate_value_Icc hmem.1.1 hc ⟨hP0.le, hmem.2⟩
  have hy₀S : y₀ ∈ S := ⟨⟨hy₀.1, hy₀.2.trans hmem.1.2⟩, hy₀P.ge⟩
  have hle : polyRoot x ≤ y₀ := csInf_le hbdd hy₀S
  have heq : y₀ = polyRoot x := le_antisymm hy₀.2 hle
  have hroot : cycP x (polyRoot x) = 0 := by rw [← heq]; exact hy₀P
  refine ⟨⟨lt_of_le_of_ne hmem.1.1 fun h => ?_, lt_of_le_of_ne hmem.1.2 fun h => ?_⟩, hroot⟩
  · rw [← h] at hroot; linarith
  · rw [h] at hroot; linarith

theorem polyRoot_le {x y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hP : 0 ≤ cycP x y) : polyRoot x ≤ y :=
  csInf_le ⟨0, fun _ h => h.1.1⟩ ⟨hy, hP⟩

theorem lt_polyRoot {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hP : cycP x y < 0) : y < polyRoot x := by
  obtain ⟨hφ, hroot⟩ := polyRoot_spec hx
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [he] at hroot; linarith
  · have := cycP_strictMono_y hx hφ.1.le hlt hy.2; linarith

theorem continuousAt_polyRoot {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt polyRoot x₀ := by
  obtain ⟨hφ, hroot⟩ := polyRoot_spec hx₀
  have hI : ∀ᶠ x in 𝓝 x₀, x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hx₀.1 hx₀.2
  have hcy : ∀ y, ContinuousAt (fun x => cycP x y) x₀ := fun y => by
    unfold cycP; fun_prop
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases lt_or_ge c 0 with hc0 | hc0
    · filter_upwards [hI] with x hx
      exact hc0.trans (polyRoot_spec hx).1.1
    · set c' := (c + polyRoot x₀) / 2
      have hc' : c < c' ∧ c' < polyRoot x₀ := ⟨by simp only [c']; linarith,
        by simp only [c']; linarith⟩
      have hneg : cycP x₀ c' < 0 := by
        have := cycP_strictMono_y hx₀ (by linarith) hc'.2 hφ.2.le; linarith
      filter_upwards [hI, (hcy c').eventually (gt_mem_nhds hneg)] with x hx hxc
      exact hc'.1.trans (lt_polyRoot hx ⟨by linarith, by linarith [hφ.2]⟩ hxc)
  · rcases lt_or_ge 1 c with hc1 | hc1
    · filter_upwards [hI] with x hx
      exact (polyRoot_spec hx).1.2.trans hc1
    · set c' := (c + polyRoot x₀) / 2
      have hc' : polyRoot x₀ < c' ∧ c' < c := ⟨by simp only [c']; linarith,
        by simp only [c']; linarith⟩
      have hpos : 0 < cycP x₀ c' := by
        have := cycP_strictMono_y hx₀ hφ.1.le hc'.1 (by linarith); linarith
      filter_upwards [(hcy c').eventually (lt_mem_nhds hpos)] with x hxc
      exact (polyRoot_le ⟨by linarith [hφ.1], by linarith⟩ hxc.le).trans_lt hc'.2

/-! ### Exercise 6.7f -/

/-- A two-cycle `(x, y)`, `x ≠ y`, in `(0, 1)` gives `x(1 − x)³ = y(1 − y)³`. -/
theorem cycle_q_eq {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1)
    (h1 : cycP x y = 0) (h2 : cycP y x = 0) : x * (1 - x) ^ 3 = y * (1 - y) ^ 3 := by
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  simp only [cycP] at h1 h2
  -- cross-multiply the two equations and cancel `x²y²(1 − x)(1 − y)`
  have hc : x ^ 3 * y ^ 2 * ((1 - y) * (1 - x) ^ 4) = y ^ 3 * x ^ 2 * ((1 - x) * (1 - y) ^ 4) := by
    have e1 : (1 / 5 : ℝ) ^ 5 * x ^ 3 * y ^ 2 = (3 / 50) ^ 5 * (1 - x) * (1 - y) ^ 4 := by
      linarith
    have e2 : (1 / 5 : ℝ) ^ 5 * y ^ 3 * x ^ 2 = (3 / 50) ^ 5 * (1 - y) * (1 - x) ^ 4 := by
      linarith
    linear_combination (5 : ℝ) ^ 5 * ((1 - y) * (1 - x) ^ 4) * e1 -
      (5 : ℝ) ^ 5 * ((1 - x) * (1 - y) ^ 4) * e2
  have hpos : 0 < x ^ 2 * y ^ 2 * (1 - x) * (1 - y) :=
    mul_pos (mul_pos (mul_pos (pow_pos hx.1 2) (pow_pos hy.1 2)) hx1) hy1
  have : (x * (1 - x) ^ 3) * (x ^ 2 * y ^ 2 * (1 - x) * (1 - y)) =
      (y * (1 - y) ^ 3) * (x ^ 2 * y ^ 2 * (1 - x) * (1 - y)) := by nlinarith [hc]
  exact mul_right_cancel₀ hpos.ne' this

/-- **Exercise 6.7f (correction).** There is no two-cycle with `x ∈ [0.28, 0.30]` and
`y ∈ [0.17, 0.19]`; in particular `(0.29, 0.18)` is not one. -/
theorem ex_6_7f_book_box {x y : ℝ} (hx : x ∈ Icc (0.28 : ℝ) 0.30) (hy : y ∈ Icc (0.17 : ℝ) 0.19) :
    ¬ (cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0 ∧
      cdFy (3 / 5) (1 / 5) y x + 1 / 10 * cdFx (3 / 5) (1 / 5) x y = 0) := by
  rintro ⟨h1, h2⟩
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hq := cycle_q_eq hxI hyI ((euler_iff_poly hxI hyI).1 h1) ((euler_iff_poly hyI hxI).1 h2)
  -- `x(1 − x)³ ≥ 0.1029 > 0.101 ≥ y(1 − y)³` on the box
  have hqx : 0.1029 ≤ x * (1 - x) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2), hx.1, hx.2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)) (sub_nonneg.2 hx.2)]
  have hqy : y * (1 - y) ^ 3 ≤ 0.101 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2), hy.1, hy.2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)) (sub_nonneg.2 hy.1)]
  linarith

/-- **Exercise 6.7f.** For `β = 0.1`, `α = 0.8`, `θ = 0.75` there is an optimal two-cycle
`(x, y)` with `0.483 ≤ x ≤ 0.485` and `0.087 < y < 0.088`. -/
theorem ex_6_7f : ∃ x y : ℝ, x ∈ Icc (0.483 : ℝ) 0.485 ∧ y ∈ Ioo (0.087 : ℝ) 0.088 ∧
    cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0 ∧
    cdFy (3 / 5) (1 / 5) y x + 1 / 10 * cdFx (3 / 5) (1 / 5) x y = 0 ∧
    total (fun k y => cdF (3 / 5) (1 / 5) k y) (1 / 10) (cyc x y) =
      vstar cdΓ (fun k y => cdF (3 / 5) (1 / 5) k y) (1 / 10) x := by
  have hI : ∀ x ∈ Icc (0.483 : ℝ) 0.485, x ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set G : ℝ → ℝ := fun x => cycP (polyRoot x) x
  have hGc : ContinuousOn G (Icc 0.483 0.485) := fun x hx =>
    ((continuous_cycP.continuousAt).comp ((continuousAt_polyRoot (hI x hx)).prodMk
      continuousAt_id)).continuousWithinAt
  -- the sign of `G` at the ends, through brackets for the root
  have hG1 : G 0.483 ≤ 0 := by
    have hb : polyRoot 0.483 ≤ 0.08786 :=
      polyRoot_le ⟨by norm_num, by norm_num⟩ (by norm_num [cycP])
    have h0 := (polyRoot_spec (hI 0.483 ⟨le_rfl, by norm_num⟩)).1.1.le
    exact (cycP_mono_x h0 hb).trans (by norm_num [cycP])
  have hG2 : 0 ≤ G 0.485 := by
    have hb : 0.08725 < polyRoot 0.485 :=
      lt_polyRoot (hI 0.485 ⟨by norm_num, le_rfl⟩) ⟨by norm_num, by norm_num⟩
        (by norm_num [cycP])
    exact (show (0 : ℝ) ≤ cycP 0.08725 0.485 by norm_num [cycP]).trans
      (cycP_mono_x (by norm_num) hb.le)
  obtain ⟨x, hx, hGx⟩ := intermediate_value_Icc (by norm_num) hGc ⟨hG1, hG2⟩
  have hxI := hI x hx
  obtain ⟨hyI, hPxy⟩ := polyRoot_spec hxI
  set y := polyRoot x
  -- bounds on `y`
  have hyhi : y ≤ 0.08786 := by
    refine polyRoot_le ⟨by norm_num, by norm_num⟩ ?_
    exact (show (0 : ℝ) ≤ cycP 0.483 0.08786 by norm_num [cycP]).trans
      (cycP_mono_x (by norm_num) hx.1)
  have hylo : 0.08725 < y := by
    refine lt_polyRoot hxI ⟨by norm_num, by norm_num⟩ ?_
    exact lt_of_le_of_lt (cycP_mono_x (by linarith [hx.1]) hx.2) (by norm_num [cycP])
  have e1 := (euler_iff_poly hxI hyI).2 hPxy
  have e2 := (euler_iff_poly hyI hxI).2 hGx
  refine ⟨x, y, hx, ⟨by linarith, by linarith⟩, e1, e2, ?_⟩
  exact (ex_6_7e (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxI
    hyI).2 ⟨e1, e2⟩

/-! ### Exercise 6.7g -/

/-- The linearized Euler equation along a path: with `z = k − k̄`,
`z_{t+2} = Jz_{t+1} + Kz_t`, where `J = −(F_yy(p, q) + βF_xx(q, r))/(βF_xy(q, r))` and
`K = −F_xy(p, q)/(βF_xy(q, r))` at `(p, q, r) = (k_t, k_{t+1}, k_{t+2})`. -/
noncomputable def linJ (a b β p q r : ℝ) : ℝ :=
  -(cdFyy a b p q + β * cdFxx a b q r) / (β * cdFxy a b q r)

noncomputable def linK (a b β p q r : ℝ) : ℝ := -cdFxy a b p q / (β * cdFxy a b q r)

/-- Along a path satisfying the Euler equation `F_y(p, q) + βF_x(q, r) = 0`,
`J = (1 − r)[(b − 1)/(1 − q) + (a − 1)/q]/b` and `K = −a(1 − r)/(bp)`. -/
theorem linJK_eq {a b β p q r : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ : 0 < β)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (he : cdFy a b p q + β * cdFx a b q r = 0) :
    linJ a b β p q r = (1 - r) * ((b - 1) / (1 - q) + (a - 1) / q) / b ∧
      linK a b β p q r = -(a * (1 - r) / (b * p)) := by
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  have hr1 : 0 < 1 - r := by linarith [hr.2]
  -- `Q = aq^{a−1}(1 − r)^b` and the Euler equation `bp^a(1 − q)^{b−1} = βQ`
  set Q := a * q ^ (a - 1) * (1 - r) ^ b
  have hQ : 0 < Q := mul_pos (mul_pos ha (rpow_pos_of_pos hq.1 _)) (rpow_pos_of_pos hr1 _)
  have hE : b * p ^ a * (1 - q) ^ (b - 1) = β * Q := by
    simp only [cdFy, cdFx] at he; simp only [Q]; linarith
  have r1 : (1 - q) ^ (b - 2) = (1 - q) ^ (b - 1) / (1 - q) := by
    rw [eq_div_iff hq1.ne', ← rpow_add_one hq1.ne']; congr 1; ring
  have r2 : q ^ (a - 2) = q ^ (a - 1) / q := by
    rw [eq_div_iff hq.1.ne', ← rpow_add_one hq.1.ne']; congr 1; ring
  have r3 : p ^ (a - 1) = p ^ a / p := by
    rw [eq_div_iff hp.1.ne', ← rpow_add_one hp.1.ne']; congr 1; ring
  have r4 : (1 - r) ^ (b - 1) = (1 - r) ^ b / (1 - r) := by
    rw [eq_div_iff hr1.ne', ← rpow_add_one hr1.ne']; congr 1; ring
  have hyy : cdFyy a b p q = (b - 1) / (1 - q) * (β * Q) := by
    rw [← hE]; simp only [cdFyy, r1]; field_simp
  have hxx : cdFxx a b q r = (a - 1) / q * Q := by
    simp only [cdFxx, Q, r2]; field_simp
  have hxyqr : cdFxy a b q r = -(b / (1 - r) * Q) := by
    simp only [cdFxy, Q, r4]; field_simp
  have hxypq : cdFxy a b p q = -(a / p * (β * Q)) := by
    rw [← hE]; simp only [cdFxy, r3]; field_simp
  constructor
  · rw [linJ, hyy, hxx, hxyqr]; field_simp
  · rw [linK, hxypq, hxyqr]; field_simp

/-- **Exercise 6.7g.** At the two-cycle of Exercise 6.7f, the stacked map
`(k_{t+1}, k_t) ↦ (k_{t+3}, k_{t+2})` has the linearization
`M = [[J₂, K₂], [1, 0]]·[[J₁, K₁], [1, 0]]` (`J₁ = J(x, y, x)`, `J₂ = J(y, x, y)`, and likewise
for `K`). Its characteristic roots are real, one in `(0, 1)` and one greater than `1`: exactly
one root is less than one in absolute value. -/
theorem ex_6_7g {x y : ℝ} (hx : x ∈ Icc (0.483 : ℝ) 0.485) (hy : y ∈ Ioo (0.087 : ℝ) 0.088)
    (e1 : cdFy (3 / 5) (1 / 5) x y + 1 / 10 * cdFx (3 / 5) (1 / 5) y x = 0)
    (e2 : cdFy (3 / 5) (1 / 5) y x + 1 / 10 * cdFx (3 / 5) (1 / 5) x y = 0) :
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![linJ (3 / 5) (1 / 5) (1 / 10) y x y, linK (3 / 5) (1 / 5) (1 / 10) y x y; 1, 0] *
        !![linJ (3 / 5) (1 / 5) (1 / 10) x y x, linK (3 / 5) (1 / 5) (1 / 10) x y x; 1, 0]
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ < 1 ∧ 1 < μ₂ ∧ quadRoot M.trace M.det μ₁ ∧
      quadRoot M.trace M.det μ₂ ∧ ∀ μ, quadRoot M.trace M.det μ → μ = μ₁ ∨ μ = μ₂ := by
  intro M
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨hJ1, hK1⟩ := linJK_eq (by norm_num) (by norm_num) (by norm_num) hxI hyI hxI e1
  obtain ⟨hJ2, hK2⟩ := linJK_eq (by norm_num) (by norm_num) (by norm_num) hyI hxI hyI e2
  -- `det M = K₁K₂ = β⁻² = 100`, `tr M = J₁J₂ + K₁ + K₂`
  have hdet : M.det = linK (3 / 5) (1 / 5) (1 / 10) x y x * linK (3 / 5) (1 / 5) (1 / 10) y x y :=
    by simp only [M, Matrix.det_mul, Matrix.det_fin_two_of]; ring
  have htr : M.trace = linJ (3 / 5) (1 / 5) (1 / 10) y x y * linJ (3 / 5) (1 / 5) (1 / 10) x y x +
      linK (3 / 5) (1 / 5) (1 / 10) y x y + linK (3 / 5) (1 / 5) (1 / 10) x y x := by
    simp [M, Matrix.trace_fin_two]
  have hK12 : linK (3 / 5) (1 / 5) (1 / 10) x y x * linK (3 / 5) (1 / 5) (1 / 10) y x y = 100 := by
    have hxy0 : cdFxy (3 / 5) (1 / 5) x y ≠ 0 := by
      simp only [cdFxy]
      have : 0 < x ^ ((3 : ℝ) / 5 - 1) * (1 - y) ^ ((1 : ℝ) / 5 - 1) :=
        mul_pos (rpow_pos_of_pos hxI.1 _) (rpow_pos_of_pos (by linarith [hyI.2]) _)
      intro h; nlinarith
    have hyx0 : cdFxy (3 / 5) (1 / 5) y x ≠ 0 := by
      simp only [cdFxy]
      have : 0 < y ^ ((3 : ℝ) / 5 - 1) * (1 - x) ^ ((1 : ℝ) / 5 - 1) :=
        mul_pos (rpow_pos_of_pos hyI.1 _) (rpow_pos_of_pos (by linarith [hxI.2]) _)
      intro h; nlinarith
    simp only [linK]
    field_simp
    norm_num
  rw [hdet, hK12]
  -- `X = (1 − x)/x ≥ 1` and `Y = (1 − y)/y ≥ 10`, so `tr M > 101`
  have htr' : 101 < M.trace := by
    rw [htr, hJ1, hJ2, hK1, hK2]
    have hX : 1 ≤ (1 - x) / x := by rw [le_div_iff₀ hxI.1]; linarith [hx.2]
    have hY : 10 ≤ (1 - y) / y := by rw [le_div_iff₀ hyI.1]; linarith [hy.2]
    have e : ∀ u v : ℝ, 0 < u → 0 < v → u < 1 → v < 1 →
        (1 - u) * ((1 / 5 - 1) / (1 - v) + (3 / 5 - 1) / v) / (1 / 5) *
          ((1 - v) * ((1 / 5 - 1) / (1 - u) + (3 / 5 - 1) / u) / (1 / 5)) +
        -(3 / 5 * (1 - u) / (1 / 5 * u)) + -(3 / 5 * (1 - v) / (1 / 5 * v)) =
        16 + 5 * ((1 - u) / u) + 5 * ((1 - v) / v) + 4 * ((1 - u) / u) * ((1 - v) / v) :=
      fun u v hu hv hu1 hv1 => by
        have : 0 < 1 - u := by linarith
        have : 0 < 1 - v := by linarith
        field_simp
        ring
    rw [e y x hyI.1 hxI.1 hyI.2 hxI.2]
    nlinarith
  -- `p(1) = 1 − tr + 100 < 0 < p(0)`: one root in `(0, 1)`, one above `1`
  set s := M.trace
  have hd : 4 * 100 ≤ s ^ 2 := by nlinarith
  set q := Real.sqrt (s ^ 2 - 4 * 100)
  have hq : q ^ 2 = s ^ 2 - 4 * 100 := Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqc : (q : ℂ) ^ 2 = (s : ℂ) ^ 2 - 4 * 100 := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hq
    push_cast at this
    exact this
  have hroot : ∀ r : ℝ, r = (s + q) / 2 ∨ r = (s - q) / 2 → quadRoot s 100 r := by
    rintro r (rfl | rfl) <;> simp only [quadRoot] <;> push_cast <;>
      linear_combination (1 / 4 : ℂ) * hqc
  have hfact : (1 - (s - q) / 2) * (1 - (s + q) / 2) = 1 - s + 100 := by nlinarith
  have hqs : q < s := by
    have : q ^ 2 < s ^ 2 := by rw [hq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) this
  refine ⟨(s - q) / 2, (s + q) / 2, by linarith, ?_, ?_, hroot _ (Or.inr rfl),
    hroot _ (Or.inl rfl), fun μ hμ => ?_⟩
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith
  · obtain ⟨r, rfl, hr⟩ := quadRoot_real hd hμ
    rcases hr with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

end StokeyLucasPrescott.DeterministicDynamics
