/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDP.UnboundedReturns
import DeterministicDP.Assumption42

/-!
# A quadratic investment problem

SLP §4.4, pp. 95–97. A firm with capital `x` earns `ax − bx²/2` and pays `c(y − x)²/2` to move
its capital to `y`; it discounts at `δ ∈ (0, 1)`. So `X = Γ(x) = ℝ` and
`F(x, y) = ax − bx²/2 − c(y − x)²/2` (`quadF`), with `a, b, c > 0`.

* `quad_opT`: `T` maps the quadratic `px − qx²/2 + r` (`q ≥ 0`) to the quadratic with
  coefficients (6)–(8), attained at `y = (δp + cx)/(δq + c)`.
* `quad_iterate`: `Tⁿv̂ = αₙx − βₙx²/2 + γₙ` for `v̂ = a²/(2b(1 − δ))`.
* `tendsto_qs`, `tendsto_ps`, `tendsto_rs`: `βₙ → β` with `b < β < b + c`, `αₙ → α` and
  `γₙ → γ` (`tendsto_linear_recursion` handles (7)–(8)).
* `quad_vstar`: `v* = αx − βx²/2 + γ` (Theorem 4.14).
* `quad_policy_optimal`: the linear policy `g(x) = (δα + cx)/(δβ + c)` is optimal (Theorem 4.5).
-/

open Filter Topology

namespace StokeyLucasPrescott.DeterministicDP

/-- If `e_{n+1} ≤ δeₙ + εₙ` with `0 ≤ δ < 1`, `eₙ ≥ 0` and `εₙ → 0`, then `eₙ → 0`. -/
theorem tendsto_zero_of_le_contract {e ε : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (he : ∀ n, 0 ≤ e n) (hrec : ∀ n, e (n + 1) ≤ δ * e n + ε n)
    (hε : Tendsto ε atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hε).2 (η * (1 - δ) / 2) (by
    have : 0 < 1 - δ := by linarith
    positivity))
  -- from `N` on, `e_{N+k} ≤ δᵏ e_N + η/2`
  have hk : ∀ k, e (N + k) ≤ δ ^ k * e N + η / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have h1 := hrec (N + k)
      have h2 := hN (N + k) (by omega)
      calc e (N + (k + 1)) ≤ δ * e (N + k) + ε (N + k) := h1
        _ ≤ δ * (δ ^ k * e N + η / 2) + η * (1 - δ) / 2 := by
            gcongr
        _ = δ ^ (k + 1) * e N + η / 2 := by ring
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const (e N)
  rw [zero_mul] at hpow
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 hpow).2 (η / 2) (half_pos hη))
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he _)]
  have := hK (K + k) (by omega)
  rw [add_assoc] at *
  have := hk (K + k)
  linarith

/-- The linear recursion `x_{n+1} = uₙ + κₙxₙ` with `uₙ → u`, `κₙ → κ`, `0 ≤ κₙ ≤ δ < 1`
converges to `u/(1 − κ)`. -/
theorem tendsto_linear_recursion {x u κ : ℕ → ℝ} {u₀ κ₀ δ : ℝ} (hδ1 : δ < 1)
    (hκ : ∀ n, 0 ≤ κ n ∧ κ n ≤ δ) (hrec : ∀ n, x (n + 1) = u n + κ n * x n)
    (hu : Tendsto u atTop (𝓝 u₀)) (hκlim : Tendsto κ atTop (𝓝 κ₀)) :
    Tendsto x atTop (𝓝 (u₀ / (1 - κ₀))) := by
  have hδ0 : 0 ≤ δ := (hκ 0).1.trans (hκ 0).2
  have hκ₀ : κ₀ ≤ δ := le_of_tendsto' hκlim fun n => (hκ n).2
  set L := u₀ / (1 - κ₀)
  have hL : L = u₀ + κ₀ * L := by
    have : 1 - κ₀ ≠ 0 := by linarith
    simp only [L]; field_simp; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_zero_of_le_contract hδ0 hδ1 (fun n => norm_nonneg _) (fun n => ?_)
    (ε := fun n => |u n - u₀| + |κ n - κ₀| * |L|) ?_
  · simp only [Real.norm_eq_abs]
    rw [hrec n]
    have e : u n + κ n * x n - L = (u n - u₀) + κ n * (x n - L) + (κ n - κ₀) * L := by
      linear_combination (-1 : ℝ) * hL
    rw [e]
    calc |(u n - u₀) + κ n * (x n - L) + (κ n - κ₀) * L|
        ≤ |u n - u₀| + |κ n * (x n - L)| + |(κ n - κ₀) * L| := abs_add_three _ _ _
      _ ≤ |u n - u₀| + δ * |x n - L| + |κ n - κ₀| * |L| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hκ n).1]
          gcongr
          exact (hκ n).2
      _ = δ * |x n - L| + (|u n - u₀| + |κ n - κ₀| * |L|) := by ring
  · have h1 := (hu.sub_const u₀).abs
    have h2 := ((hκlim.sub_const κ₀).abs).mul_const |L|
    simpa using h1.add h2

variable {a b c δ : ℝ}

/-- `F(x, y) = ax − bx²/2 − c(y − x)²/2`. -/
noncomputable def quadF (a b c : ℝ) (x y : ℝ) : ℝ := a * x - b * x ^ 2 / 2 - c * (y - x) ^ 2 / 2

/-- `Γ(x) = ℝ`. -/
def quadΓ (_ : ℝ) : Set ℝ := Set.univ

/-- The quadratic `px − qx²/2 + r`. -/
noncomputable def quadFn (p q r : ℝ) (x : ℝ) : EReal := ((p * x - q * x ^ 2 / 2 + r : ℝ) : EReal)

/-- (6): `β' = b + δβc/(δβ + c)`. -/
noncomputable def nextQ (b c δ q : ℝ) : ℝ := b + δ * q * c / (δ * q + c)

/-- (7): `α' = a + δαc/(δβ + c)`. -/
noncomputable def nextP (a c δ p q : ℝ) : ℝ := a + δ * p * c / (δ * q + c)

/-- (8): `γ' = δγ + (δα)²/(2(δβ + c))`. -/
noncomputable def nextR (c δ p q r : ℝ) : ℝ := δ * r + (δ * p) ^ 2 / (2 * (δ * q + c))

/-- The objective as a function of `y` is the value at `y* = (δp + cx)/(δq + c)` minus
`(c + δq)(y − y*)²/2`. -/
theorem quad_objective (p q r x y : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hq : 0 ≤ q) :
    quadF a b c x y + δ * (p * y - q * y ^ 2 / 2 + r) =
      nextP a c δ p q * x - nextQ b c δ q * x ^ 2 / 2 + nextR c δ p q r -
        (δ * q + c) / 2 * (y - (δ * p + c * x) / (δ * q + c)) ^ 2 := by
  have hne : δ * q + c ≠ 0 := by positivity
  simp only [quadF, nextP, nextQ, nextR]
  field_simp
  ring

/-- `T` maps `px − qx²/2 + r` (`q ≥ 0`) to the quadratic with coefficients (6)–(8). -/
theorem quad_opT (p q r : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hq : 0 ≤ q) :
    opT quadΓ (quadF a b c) δ (quadFn p q r) =
      quadFn (nextP a c δ p q) (nextQ b c δ q) (nextR c δ p q r) := by
  funext x
  have hpos : 0 ≤ (δ * q + c) / 2 := by positivity
  refine le_antisymm (iSup₂_le fun y _ => ?_) ?_
  · rw [quadFn, quadFn, ← EReal.coe_mul, ← EReal.coe_add, quad_objective p q r x y hc hδ hq]
    exact EReal.coe_le_coe_iff.2 (by nlinarith [sq_nonneg (y - (δ * p + c * x) / (δ * q + c))])
  · refine le_trans ?_ (le_biSup _ (Set.mem_univ ((δ * p + c * x) / (δ * q + c))))
    rw [quadFn, quadFn, ← EReal.coe_mul, ← EReal.coe_add,
      quad_objective p q r x _ hc hδ hq]
    simp

/-- `F(x, y) ≤ a²/(2b)`. -/
theorem quadF_le (hb : 0 < b) (hc : 0 < c) (x y : ℝ) : quadF a b c x y ≤ a ^ 2 / (2 * b) := by
  simp only [quadF]
  have e : a ^ 2 / (2 * b) - (a * x - b * x ^ 2 / 2) = (b * x - a) ^ 2 / (2 * b) := by
    field_simp; ring
  have : 0 ≤ (b * x - a) ^ 2 / (2 * b) := by positivity
  nlinarith [sq_nonneg (y - x)]

/-- The coefficient sequences, from `v̂ = a²/(2b(1 − δ))`. -/
noncomputable def qs (b c δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => nextQ b c δ (qs b c δ n)

noncomputable def ps (a b c δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => nextP a c δ (ps a b c δ n) (qs b c δ n)

noncomputable def rs (a b c δ : ℝ) : ℕ → ℝ
  | 0 => a ^ 2 / (2 * b * (1 - δ))
  | n + 1 => nextR c δ (ps a b c δ n) (qs b c δ n) (rs a b c δ n)

variable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
include ha hb hc hδ0 hδ1

omit ha hδ1 in
theorem qs_nonneg (n : ℕ) : 0 ≤ qs b c δ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [qs, nextQ]; positivity

omit ha hb hδ1 in
theorem nextQ_mono {q q' : ℝ} (hq : 0 ≤ q) (hqq' : q ≤ q') : nextQ b c δ q ≤ nextQ b c δ q' := by
  simp only [nextQ]
  have h1 : 0 < δ * q + c := by positivity
  have h2 : 0 < δ * q' + c := by have : 0 ≤ q' := hq.trans hqq'; positivity
  rw [add_le_add_iff_left, div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_left hqq' (by positivity : (0 : ℝ) ≤ δ * c ^ 2)]

omit ha hb hδ1 in
theorem nextQ_lt (q : ℝ) (hq : 0 ≤ q) : nextQ b c δ q < b + c := by
  simp only [nextQ]
  have h1 : 0 < δ * q + c := by positivity
  rw [add_lt_add_iff_left, div_lt_iff₀ h1]
  nlinarith

omit ha hδ1 in
theorem qs_mono : Monotone (qs b c δ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero =>
    change (0 : ℝ) ≤ nextQ b c δ 0
    simp only [nextQ, mul_zero, zero_mul, zero_div, add_zero]
    exact hb.le
  | succ n ih => exact nextQ_mono hc hδ0 (qs_nonneg hb hc hδ0 n) ih

omit ha hδ1 in
/-- (6): `βₙ → β` with `b < β < b + c`, and `β` solves `β = b + δβc/(δβ + c)`. -/
theorem tendsto_qs : ∃ Q, Tendsto (qs b c δ) atTop (𝓝 Q) ∧ nextQ b c δ Q = Q ∧ b < Q ∧
    Q < b + c := by
  have hbdd : ∀ n, qs b c δ n ≤ b + c := fun n => by
    cases n with
    | zero => change (0 : ℝ) ≤ b + c; positivity
    | succ n => exact (nextQ_lt hc hδ0 _ (qs_nonneg hb hc hδ0 n)).le
  have hlim := tendsto_atTop_ciSup (qs_mono hb hc hδ0) ⟨b + c, by
    rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  set Q := ⨆ n, qs b c δ n
  have hQ0 : 0 ≤ Q := (qs_nonneg hb hc hδ0 0).trans (le_ciSup ⟨b + c, by
    rintro _ ⟨n, rfl⟩; exact hbdd n⟩ 0)
  have hfix : nextQ b c δ Q = Q := by
    have hcont : ContinuousAt (nextQ b c δ) Q := by
      have e : nextQ b c δ = fun q => b + δ * q * c / (δ * q + c) := rfl
      rw [e]
      exact continuousAt_const.add (((continuousAt_const.mul continuousAt_id).mul
        continuousAt_const).div ((continuousAt_const.mul continuousAt_id).add
          continuousAt_const) (by change δ * Q + c ≠ 0; positivity))
    exact tendsto_nhds_unique (hcont.tendsto.comp hlim)
      (hlim.comp (tendsto_add_atTop_nat 1))
  refine ⟨Q, hlim, hfix, ?_, ?_⟩
  · have hQpos : 0 < Q := by
      have h1 : b ≤ Q := by
        have := le_ciSup (f := qs b c δ) ⟨b + c, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩ 1
        have e1 : qs b c δ 1 = b := by change nextQ b c δ 0 = b; simp [nextQ]
        rwa [e1] at this
      linarith
    rw [← hfix]
    simp only [nextQ]
    have : 0 < δ * Q * c / (δ * Q + c) := by positivity
    linarith
  · rw [← hfix]; exact nextQ_lt hc hδ0 Q hQ0

omit ha hδ1 in
/-- `Tⁿv̂ = αₙx − βₙx²/2 + γₙ`. -/
theorem quad_iterate (n : ℕ) :
    (opT quadΓ (quadF a b c) δ)^[n] (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) =
      quadFn (ps a b c δ n) (qs b c δ n) (rs a b c δ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, quad_opT _ _ _ hc hδ0.le (qs_nonneg hb hc hδ0 n)]
    rfl

omit ha in
/-- (7)–(8): `αₙ → α` and `γₙ → γ`, solving `α = a + δαc/(δβ + c)` and
`γ = δγ + (δα)²/(2(δβ + c))`. -/
theorem tendsto_ps_rs : ∃ Q P R, Tendsto (qs b c δ) atTop (𝓝 Q) ∧ nextQ b c δ Q = Q ∧ b < Q ∧
    Q < b + c ∧ Tendsto (ps a b c δ) atTop (𝓝 P) ∧ nextP a c δ P Q = P ∧
    Tendsto (rs a b c δ) atTop (𝓝 R) ∧ nextR c δ P Q R = R := by
  obtain ⟨Q, hQ, hfix, hbQ, hQbc⟩ := tendsto_qs hb hc hδ0
  have hQ0 : 0 ≤ Q := by linarith
  set κ : ℕ → ℝ := fun n => δ * c / (δ * qs b c δ n + c)
  have hκ : ∀ n, 0 ≤ κ n ∧ κ n ≤ δ := fun n => by
    have h1 : 0 < δ * qs b c δ n + c := by have := qs_nonneg hb hc hδ0 n; positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ h1]
    have := qs_nonneg hb hc hδ0 n
    nlinarith [mul_nonneg (mul_nonneg hδ0.le hδ0.le) this]
  have hκlim : Tendsto κ atTop (𝓝 (δ * c / (δ * Q + c))) :=
    tendsto_const_nhds.div ((hQ.const_mul δ).add_const c) (by positivity)
  have hP := tendsto_linear_recursion hδ1 hκ (u := fun _ => a) (x := ps a b c δ)
    (fun n => by simp only [ps, nextP, κ]; ring) tendsto_const_nhds hκlim
  set P := a / (1 - δ * c / (δ * Q + c))
  have hPfix : nextP a c δ P Q = P := by
    have hne : δ * Q + c ≠ 0 := by positivity
    have hne2 : 1 - δ * c / (δ * Q + c) ≠ 0 := by
      have : δ * c / (δ * Q + c) < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith
      linarith
    have e : δ * P * c / (δ * Q + c) = (δ * c / (δ * Q + c)) * P := by ring
    simp only [nextP]
    rw [e]
    have h2 : P * (1 - δ * c / (δ * Q + c)) = a := div_mul_cancel₀ a hne2
    linear_combination (-1 : ℝ) * h2
  -- (8) with `κₙ = δ`
  have hd : Tendsto (fun n => (δ * ps a b c δ n) ^ 2 / (2 * (δ * qs b c δ n + c))) atTop
      (𝓝 ((δ * P) ^ 2 / (2 * (δ * Q + c)))) :=
    ((hP.const_mul δ).pow 2).div (((hQ.const_mul δ).add_const c).const_mul 2) (by positivity)
  have hR := tendsto_linear_recursion hδ1 (κ := fun _ => δ) (fun _ => ⟨hδ0.le, le_rfl⟩)
    (x := rs a b c δ) (fun n => by simp only [rs, nextR]; ring) hd tendsto_const_nhds
  refine ⟨Q, P, (δ * P) ^ 2 / (2 * (δ * Q + c)) / (1 - δ), hQ, hfix, hbQ, hQbc, hP, hPfix, hR,
    ?_⟩
  have hne : (1 - δ) ≠ 0 := by linarith
  simp only [nextR]
  field_simp
  ring

/-- **p. 96.** `v*(x) = αx − βx²/2 + γ` with the limits of (6)–(8). -/
theorem quad_vstar : ∃ P Q R, b < Q ∧ Q < b + c ∧ nextQ b c δ Q = Q ∧ nextP a c δ P Q = P ∧
    nextR c δ P Q R = R ∧ vstar quadΓ (quadF a b c) δ = quadFn P Q R := by
  obtain ⟨Q, P, R, hQ, hQfix, hbQ, hQbc, hP, hPfix, hR, hRfix⟩ :=
    tendsto_ps_rs hb hc hδ0 hδ1
  refine ⟨P, Q, R, hbQ, hQbc, hQfix, hPfix, hRfix, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have h42 : Assumption42 quadΓ (quadF a b c) δ :=
    assumption42_of_bddAbove (quadF_le hb hc) hδ0.le hδ1
  -- `Tv̂ ≤ v̂`
  have hTv : opT quadΓ (quadF a b c) δ (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) ≤
      quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ))) := by
    have e := quad_iterate hb hc hδ0 (a := a) 1
    rw [Function.iterate_one] at e
    rw [e]
    intro x
    have e1 : ps a b c δ 1 = a := by change nextP a c δ 0 0 = a; simp [nextP]
    have e2 : qs b c δ 1 = b := by change nextQ b c δ 0 = b; simp [nextQ]
    have e3 : rs a b c δ 1 = δ * (a ^ 2 / (2 * b * (1 - δ))) := by
      change nextR c δ 0 0 (a ^ 2 / (2 * b * (1 - δ))) = _; simp [nextR]
    simp only [quadFn, e1, e2, e3]
    refine EReal.coe_le_coe_iff.2 ?_
    have h2 : a * x - b * x ^ 2 / 2 ≤ a ^ 2 / (2 * b) := by
      have := quadF_le (a := a) hb hc x x
      simpa [quadF] using this
    have key : δ * (a ^ 2 / (2 * b * (1 - δ))) + a ^ 2 / (2 * b) = a ^ 2 / (2 * b * (1 - δ)) := by
      field_simp; ring
    linarith
  -- the iterates decrease to the quadratic limit
  have hlimfun : limitFn quadΓ (quadF a b c) δ (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) =
      quadFn P Q R := by
    funext x
    have hconv : Tendsto (fun n => (opT quadΓ (quadF a b c) δ)^[n]
        (quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ)))) x) atTop (𝓝 (quadFn P Q R x)) := by
      simp only [quad_iterate hb hc hδ0 (a := a)]
      exact EReal.tendsto_coe.2 (((hP.mul_const x).sub ((hQ.mul_const (x ^ 2)).div_const 2)).add
        hR)
    exact tendsto_nhds_unique (tendsto_iterate hδ0.le hTv x) hconv
  rw [← hlimfun]
  refine (theorem_4_14 (Γ := quadΓ) hδ0 (fun x => ⟨0, Set.mem_univ _⟩) h42 (fun x₀ x hx => ?_)
    (fun x₀ x hx => ?_) ?_).symm
  · -- (2): `δⁿv̂ → 0`
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).mul_const
      (a ^ 2 / (2 * b * (1 - δ)))
    rw [zero_mul] at h
    have : Tendsto (fun n => ((δ ^ n : ℝ) : EReal) *
        quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ))) (x n)) atTop (𝓝 0) := by
      refine (EReal.tendsto_coe.2 h).congr fun n => ?_
      simp [quadFn, EReal.coe_mul]
    exact this.limsup_eq.le
  · -- (3): `u(x) ≤ v̂(x₀)`
    have hps : ∀ n, (partialSum (quadF a b c) δ x n : EReal) ≤
        ((a ^ 2 / (2 * b * (1 - δ)) : ℝ) : EReal) := fun n => by
      refine EReal.coe_le_coe_iff.2 ?_
      calc partialSum (quadF a b c) δ x n
          ≤ ∑ t ∈ Finset.range (n + 1), δ ^ t * (a ^ 2 / (2 * b)) :=
            Finset.sum_le_sum fun t _ =>
              mul_le_mul_of_nonneg_left (quadF_le hb hc _ _) (pow_nonneg hδ0.le t)
        _ = (a ^ 2 / (2 * b)) * ∑ t ∈ Finset.range (n + 1), δ ^ t := by
            rw [Finset.mul_sum]; congr 1; funext t; ring
        _ ≤ (a ^ 2 / (2 * b)) * ∑' t, δ ^ t := mul_le_mul_of_nonneg_left
            ((summable_geometric_of_lt_one hδ0.le hδ1).sum_le_tsum _ fun t _ =>
              pow_nonneg hδ0.le t) (by positivity)
        _ = a ^ 2 / (2 * b * (1 - δ)) := by
            rw [tsum_geometric_of_lt_one hδ0.le hδ1]; field_simp
    have : quadFn 0 0 (a ^ 2 / (2 * b * (1 - δ))) x₀ =
        ((a ^ 2 / (2 * b * (1 - δ)) : ℝ) : EReal) := by
      simp [quadFn]
    rw [this]
    exact le_of_tendsto' (tendsto_total h42 hx) hps
  · -- the limit is a fixed point
    rw [hlimfun, quad_opT _ _ _ hc hδ0.le (by linarith), hPfix, hQfix, hRfix]

/-- **p. 96.** The linear policy `g(x) = (δα + cx)/(δβ + c)` generates optimal plans. -/
theorem quad_policy_optimal (x₀ : ℝ) :
    ∃ P Q : ℝ, ∀ x : ℕ → ℝ, x 0 = x₀ → (∀ t, x (t + 1) = (δ * P + c * x t) / (δ * Q + c)) →
      total (quadF a b c) δ x = vstar quadΓ (quadF a b c) δ x₀ := by
  obtain ⟨P, Q, R, hbQ, -, hQfix, hPfix, hRfix, hvs⟩ := quad_vstar ha hb hc hδ0 hδ1
  refine ⟨P, Q, fun x hx0 hx => ?_⟩
  have hQ0 : 0 < Q := by linarith
  have hne : δ * Q + c ≠ 0 := by positivity
  have h42 : Assumption42 quadΓ (quadF a b c) δ :=
    assumption42_of_bddAbove (quadF_le hb hc) hδ0.le hδ1
  refine theorem_4_5 hδ0.le h42 ⟨hx0, fun _ => Set.mem_univ _⟩ (fun t => ?_) ?_
  · -- (9): the value at the maximizer
    rw [hvs, quadFn, quadFn, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    have h := quad_objective (a := a) (b := b) P Q R (x t) (x (t + 1)) hc hδ0.le hQ0.le
    have hz : x (t + 1) - (δ * P + c * x t) / (δ * Q + c) = 0 := by rw [hx t]; ring
    rw [hz, hPfix, hQfix, hRfix] at h
    rw [h]
    ring
  · -- (11): the plan contracts towards `P/Q`, so it stays bounded
    set s := c / (δ * Q + c)
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    set xbar := P / Q
    have hstep : ∀ t, x (t + 1) - xbar = s * (x t - xbar) := fun t => by
      rw [hx t]; simp only [s, xbar]; field_simp; ring
    have hdist : ∀ t, |x t - xbar| ≤ |x₀ - xbar| := by
      intro t
      induction t with
      | zero => rw [hx0]
      | succ t ih =>
        rw [hstep, abs_mul, abs_of_nonneg hs0]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs1).trans ih
    set M := |xbar| + |x₀ - xbar|
    have hxM : ∀ t, |x t| ≤ M := fun t => by
      have := hdist t
      calc |x t| = |(x t - xbar) + xbar| := by ring_nf
        _ ≤ |x t - xbar| + |xbar| := abs_add_le _ _
        _ ≤ M := by simp only [M]; linarith
    set K := |P| * M + Q * M ^ 2 / 2 + |R|
    have hbound : ∀ t, ((δ ^ t : ℝ) : EReal) * vstar quadΓ (quadF a b c) δ (x t) ≤
        ((K * δ ^ t : ℝ) : EReal) := fun t => by
      rw [hvs, quadFn, ← EReal.coe_mul]
      refine EReal.coe_le_coe_iff.2 ?_
      have hPx : |P * x t| ≤ |P| * M := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hxM t) (abs_nonneg P)
      have h1 : P * x t ≤ |P| * M := (le_abs_self _).trans hPx
      have h2 : 0 ≤ Q * x t ^ 2 / 2 := by positivity
      have h3 : P * x t - Q * x t ^ 2 / 2 + R ≤ K := by
        simp only [K]
        have : 0 ≤ Q * M ^ 2 / 2 := by positivity
        linarith [le_abs_self R]
      rw [mul_comm K]
      exact mul_le_mul_of_nonneg_left h3 (pow_nonneg hδ0.le t)
    have hzero : Tendsto (fun t => ((K * δ ^ t : ℝ) : EReal)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).const_mul K
      simpa using EReal.tendsto_coe.2 this
    exact (limsup_le_limsup (Eventually.of_forall hbound)).trans hzero.limsup_eq.le

end StokeyLucasPrescott.DeterministicDP
