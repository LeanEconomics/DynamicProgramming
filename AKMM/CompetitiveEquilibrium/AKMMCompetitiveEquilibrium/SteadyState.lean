/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCompetitiveEquilibrium.Sequential

/-!
# Recursive steady-state equilibria

AKMM, §5.4.1, pp. 147–149. Both steady-state problems of the section have the form
`V(x) = max_{x′} u(mx + y − nx′) + βV(x′)`: the endowment economy with `m = 1`, `n = q`
(Definition 7) and the growth economy with `m = 1 − δ + r`, `n = 1`, `y = weᵢ` (Definition 8).
The Bellman equation is imposed on the natural domain `{x : (m − n)x + y ∈ S}` (consumption
when holdings are kept constant lies in the set `S` where `u` is defined, e.g. `(0, ∞)`); with
`m = 1` this is the natural borrowing limit.

* The general problem (`SSBellman`): with `βm = n` and `u` concave, `g(x) = x` and
  `V(x) = u((m − n)x + y)/(1 − β)` solve it (`ss_value`); conversely a stationary point of an
  optimal policy, with `u′ ≠ 0` there and `S` open, forces `βm = n` (`ss_rate`). The proof
  compares the optimum with saving `ε` once and then holding the new level forever, which the
  Bellman equation itself prices; no envelope theorem is needed.
* Definition 7 (`IsSSEquilibriumEndow`): `q = β` (`definition_7_q_eq_beta`); the functional Euler
  equation at a stationary point gives `q = β` (`ss_functional_euler_q`) and `g(a) = a` solves it
  (`ss_functional_euler_id`); every asset distribution with `∫ aᵢ di = 0` is an equilibrium,
  with `Vᵢ(a) = u(a(1 − q) + yᵢ)/(1 − β)` (`definition_7_any_distribution`).
* Definition 8 (`IsSSEquilibriumGrowth`): `β(1 − δ + r) = 1` (`definition_8_rate`), not
  `β = 1 − δ + r` as printed (`definition_8_printed_counterexample`); with Cobb–Douglas
  technology `K* = (αA/(1/β − 1 + δ))^{1/(1−α)}` (`definition_8_capital`); every capital
  distribution adding up to `K*` is an equilibrium, with `gᵢ(k) = k` and
  `Vᵢ(k) = u(k(r − δ) + weᵢ)/(1 − β)` (`definition_8_any_distribution`).
-/

namespace AKMM.CompetitiveEquilibrium

open MeasureTheory Filter Topology

variable {I : Type*} [MeasurableSpace I]

/-- The steady-state Bellman equation `V(x) = max_{x′} u(mx + y − nx′) + βV(x′)` on the domain
`{x : (m − n)x + y ∈ S}`, with `g` attaining the maximum and consumption in `S`. -/
def SSBellman (u : ℝ → ℝ) (S : Set ℝ) (β m n y : ℝ) (V g : ℝ → ℝ) : Prop :=
  ∀ x, (m - n) * x + y ∈ S →
    ((m - n) * g x + y ∈ S ∧ m * x + y - n * g x ∈ S ∧
        V x = u (m * x + y - n * g x) + β * V (g x)) ∧
      ∀ x', (m - n) * x' + y ∈ S → m * x + y - n * x' ∈ S →
        u (m * x + y - n * x') + β * V x' ≤ V x

/-- **AKMM, pp. 148–149: the steady-state value and policy.** If `0 ≤ β < 1`, `βm = n` and `u`
is concave on the convex set `S`, then `g(x) = x` and `V(x) = u((m − n)x + y)/(1 − β)` solve the
steady-state Bellman equation. -/
theorem ss_value {u : ℝ → ℝ} {S : Set ℝ} {β m n y : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hmn : β * m = n) (hu : ConcaveOn ℝ S u) :
    SSBellman u S β m n y (fun x => u ((m - n) * x + y) / (1 - β)) id := by
  have h1 : (0 : ℝ) < 1 - β := by linarith
  intro x hx
  have hc : m * x + y - n * x = (m - n) * x + y := by ring
  refine ⟨⟨hx, by rw [id, hc]; exact hx, ?_⟩, fun x' hx' hc1 => ?_⟩
  · simp only [id, hc]; field_simp; ring
  · have hcomb : (1 - β) • (m * x + y - n * x') + β • ((m - n) * x' + y) = (m - n) * x + y := by
      simp only [smul_eq_mul]; rw [← hmn]; ring
    have := hu.2 hc1 hx' h1.le hβ0 (by ring)
    rw [hcomb] at this
    simp only [smul_eq_mul] at this
    simp only
    rw [le_div_iff₀ h1]
    have e : (u (m * x + y - n * x') + β * (u ((m - n) * x' + y) / (1 - β))) * (1 - β) =
        (1 - β) * u (m * x + y - n * x') + β * u ((m - n) * x' + y) := by
      field_simp
    rw [e]
    exact this

/-- **AKMM, pp. 148–149: a stationary point forces `βm = n`.** Suppose `V, g` solve the
steady-state Bellman equation, `S` is open, `0 ≤ β < 1`, `x*` lies in the domain with
`g(x*) = x*`, and `u` is differentiable at `c* = (m − n)x* + y` with `u′(c*) ≠ 0`. Then
`βm = n`. -/
theorem ss_rate {u : ℝ → ℝ} {S : Set ℝ} {β m n y du xs : ℝ} {V g : ℝ → ℝ}
    (hb : SSBellman u S β m n y V g) (hS : IsOpen S) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hx : (m - n) * xs + y ∈ S) (hg : g xs = xs) (hd : HasDerivAt u du ((m - n) * xs + y))
    (hdu : du ≠ 0) : β * m = n := by
  have h1 : (0 : ℝ) < 1 - β := by linarith
  set cs := (m - n) * xs + y with hcs
  -- the value at `x*`
  have hV : V xs = u cs / (1 - β) := by
    have h := ((hb xs hx).1).2.2
    rw [hg, show m * xs + y - n * xs = cs by rw [hcs]; ring] at h
    field_simp; linarith
  -- keeping any holdings `x` forever gives `V(x) ≥ u((m − n)x + y)/(1 − β)`
  have hkeep : ∀ x, (m - n) * x + y ∈ S → u ((m - n) * x + y) / (1 - β) ≤ V x := by
    intro x hxS
    have e : m * x + y - n * x = (m - n) * x + y := by ring
    have := (hb x hxS).2 x hxS (by rw [e]; exact hxS)
    rw [e] at this
    rw [div_le_iff₀ h1]; linarith
  -- deviation: move to `x* + ε` once and stay
  let φ : ℝ → ℝ := fun ε => u (cs - n * ε) + β / (1 - β) * u (cs + (m - n) * ε)
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), cs - n * ε ∈ S ∧ cs + (m - n) * ε ∈ S := by
    have c1 : ContinuousAt (fun ε : ℝ => cs - n * ε) 0 :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
    have c2 : ContinuousAt (fun ε : ℝ => cs + (m - n) * ε) 0 :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
    exact (c1.eventually_mem (hS.mem_nhds (by simpa using hx))).and
      (c2.eventually_mem (hS.mem_nhds (by simpa using hx)))
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hev] with ε hε
    have ed : (m - n) * (xs + ε) + y = cs + (m - n) * ε := by rw [hcs]; ring
    have ec : m * xs + y - n * (xs + ε) = cs - n * ε := by rw [hcs]; ring
    have hB := (hb xs hx).2 (xs + ε) (by rw [ed]; exact hε.2) (by rw [ec]; exact hε.1)
    have hK := hkeep (xs + ε) (by rw [ed]; exact hε.2)
    rw [ed] at hK
    rw [ec] at hB
    have h0 : φ 0 = V xs := by
      rw [hV]; simp only [φ, mul_zero, sub_zero, add_zero]; field_simp; ring
    change φ ε ≤ φ 0
    rw [h0]
    have e : β / (1 - β) * u (cs + (m - n) * ε) = β * (u (cs + (m - n) * ε) / (1 - β)) := by
      ring
    simp only [φ]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hK hβ0]
  have hφ : HasDerivAt φ (du * (-n) + β / (1 - β) * (du * (m - n))) 0 := by
    have hA : HasDerivAt (fun ε => u (cs - n * ε)) (du * (-n)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => cs - n * ε) (-n) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul n).const_sub cs
      have hu : HasDerivAt u du (cs - n * 0) := by simpa using hd
      exact hu.comp 0 hin
    have hB : HasDerivAt (fun ε => u (cs + (m - n) * ε)) (du * (m - n)) 0 := by
      have hin : HasDerivAt (fun ε : ℝ => cs + (m - n) * ε) (m - n) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (m - n)).const_add cs
      have hu : HasDerivAt u du (cs + (m - n) * 0) := by simpa using hd
      exact hu.comp 0 hin
    exact hA.add (hB.const_mul _)
  have hz := hmax.hasDerivAt_eq_zero hφ
  have h2 : du * (β * m - n) = 0 := by
    field_simp at hz
    linear_combination hz
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hdu
  · linarith

/-! ### Definition 7: the endowment economy -/

/-- **AKMM, Definition 7, p. 147.** A recursive steady-state equilibrium of the endowment
economy: a price `q`, and for each consumer `Vᵢ, gᵢ` solving
`Vᵢ(a) = max_{a′} u(a + yᵢ − qa′) + βVᵢ(a′)` (on the natural domain), holdings `aᵢ*` in the
domain with `gᵢ(aᵢ*) = aᵢ*`, and `∫ gᵢ(aᵢ*) di = 0`. -/
def IsSSEquilibriumEndow (μ : Measure I) (u : ℝ → ℝ) (S : Set ℝ) (β : ℝ) (y : I → ℝ) (q : ℝ)
    (V g : I → ℝ → ℝ) (as : I → ℝ) : Prop :=
  (∀ i, SSBellman u S β 1 q (y i) (V i) (g i)) ∧ (∀ i, (1 - q) * as i + y i ∈ S) ∧
    (∀ i, g i (as i) = as i) ∧ ∫ i, g i (as i) ∂μ = 0

/-- **AKMM, p. 148: `q = β`.** In a steady-state equilibrium with `S` open, `0 ≤ β < 1` and
`u′ ≠ 0` at each consumer's steady consumption `(1 − q)aᵢ* + yᵢ`, the price is `q = β`. -/
theorem definition_7_q_eq_beta {μ : Measure I} {u du : ℝ → ℝ} {S : Set ℝ} {β q : ℝ}
    {y : I → ℝ} {V g : I → ℝ → ℝ} {as : I → ℝ}
    (he : IsSSEquilibriumEndow μ u S β y q V g as) (hS : IsOpen S) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hd : ∀ c ∈ S, HasDerivAt u (du c) c) (hdu : ∀ c ∈ S, du c ≠ 0) (i : I) : q = β := by
  obtain ⟨hb, hdom, hfix, _⟩ := he
  have h := ss_rate (hb i) hS hβ0 hβ1 (hdom i) (hfix i) (hd _ (hdom i)) (hdu _ (hdom i))
  linarith

/-- **AKMM, p. 148: the functional Euler equation at a stationary point.** If
`qu′(a + y − qg(a)) = βu′(g(a) + y − qg(g(a)))` holds at `a = a*` with `g(a*) = a*` and
`u′(a*(1 − q) + y) ≠ 0`, then `q = β`. -/
theorem ss_functional_euler_q {du g : ℝ → ℝ} {q β y as : ℝ} (hfix : g as = as)
    (heul : q * du (as + y - q * g as) = β * du (g as + y - q * g (g as)))
    (hdu : du (as * (1 - q) + y) ≠ 0) : q = β := by
  rw [hfix, hfix] at heul
  have e : as + y - q * as = as * (1 - q) + y := by ring
  rw [e] at heul
  exact mul_right_cancel₀ hdu heul

/-- **AKMM, p. 148: `g(a) = a` solves the functional Euler equation when `q = β`.** -/
theorem ss_functional_euler_id {du : ℝ → ℝ} {β y : ℝ} (a : ℝ) :
    β * du (a + y - β * id a) = β * du (id a + y - β * id (id a)) := by
  simp

/-- **AKMM, p. 148: the asset distribution is indeterminate.** For `0 ≤ β < 1`, `u` concave on
the convex set `S` and any holdings `aᵢ*` with `∫ aᵢ* di = 0` and `(1 − β)aᵢ* + yᵢ ∈ S`,
`q = β`, `gᵢ(a) = a` and `Vᵢ(a) = u(a(1 − q) + yᵢ)/(1 − β)` form a steady-state equilibrium. -/
theorem definition_7_any_distribution {μ : Measure I} {u : ℝ → ℝ} {S : Set ℝ} {β : ℝ}
    {y : I → ℝ} {as : I → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hu : ConcaveOn ℝ S u)
    (hdom : ∀ i, (1 - β) * as i + y i ∈ S) (hclear : ∫ i, as i ∂μ = 0) :
    IsSSEquilibriumEndow μ u S β y β
      (fun i a => u (a * (1 - β) + y i) / (1 - β)) (fun _ => id) as := by
  refine ⟨fun i => ?_, hdom, fun _ => rfl, hclear⟩
  have h := ss_value (y := y i) hβ0 hβ1 (by ring : β * 1 = β) hu
  have e : (fun x => u ((1 - β) * x + y i) / (1 - β)) = fun a => u (a * (1 - β) + y i) / (1 - β) :=
    by funext a; ring_nf
  rwa [e] at h

/-! ### Definition 8: the growth economy -/

/-- **AKMM, Definition 8, p. 149.** A recursive steady-state equilibrium of the growth economy
with labour `eᵢ`: prices `r, w`, for each consumer `Vᵢ, gᵢ` solving
`Vᵢ(k) = max_{k′} u((1 − δ + r)k + weᵢ − k′) + βVᵢ(k′)` (on the natural domain), `(K*, 1)`
maximizing `F(K, L) − rK − wL` over `K, L ≥ 0` with `∫ kᵢ* di = K*`, and `gᵢ(kᵢ*) = kᵢ*`
with `kᵢ*` in the domain. -/
def IsSSEquilibriumGrowth (μ : Measure I) (u : ℝ → ℝ) (S : Set ℝ) (β δ : ℝ)
    (F : ℝ → ℝ → ℝ) (e : I → ℝ) (r w : ℝ) (V g : I → ℝ → ℝ) (ks : I → ℝ) (Ks : ℝ) : Prop :=
  (∀ i, SSBellman u S β (1 - δ + r) 1 (w * e i) (V i) (g i)) ∧
    (∀ K L, 0 ≤ K → 0 ≤ L → F K L - r * K - w * L ≤ F Ks 1 - r * Ks - w * 1) ∧
    ∫ i, ks i ∂μ = Ks ∧ (∀ i, (1 - δ + r - 1) * ks i + w * e i ∈ S) ∧ ∀ i, g i (ks i) = ks i

/-- **AKMM, p. 149, corrected: `β(1 − δ + r) = 1`.** In a steady-state equilibrium with `S`
open, `0 ≤ β < 1` and `u′ ≠ 0` on `S`, the gross return satisfies `β(1 − δ + r) = 1`. The book
prints `β = 1 − δ + r`. -/
theorem definition_8_rate {μ : Measure I} {u du : ℝ → ℝ} {S : Set ℝ} {β δ r w Ks : ℝ}
    {F : ℝ → ℝ → ℝ} {e : I → ℝ} {V g : I → ℝ → ℝ} {ks : I → ℝ}
    (he : IsSSEquilibriumGrowth μ u S β δ F e r w V g ks Ks) (hS : IsOpen S) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hd : ∀ c ∈ S, HasDerivAt u (du c) c) (hdu : ∀ c ∈ S, du c ≠ 0) (i : I) :
    β * (1 - δ + r) = 1 := by
  obtain ⟨hb, _, _, hdom, hfix⟩ := he
  exact ss_rate (hb i) hS hβ0 hβ1 (hdom i) (hfix i) (hd _ (hdom i)) (hdu _ (hdom i))

/-- **AKMM, p. 149: the policy and value functions; the distribution is indeterminate.** If
`0 ≤ β < 1`, `β(1 − δ + r) = 1`, `u` is concave on the convex set `S`, `(K*, 1)` solves the
firm's problem and `kᵢ*` is any distribution with `∫ kᵢ* di = K*` and
`k(r − δ) + weᵢ ∈ S` at `kᵢ*`, then `gᵢ(k) = k` and `Vᵢ(k) = u(k(r − δ) + weᵢ)/(1 − β)` form a
steady-state equilibrium. -/
theorem definition_8_any_distribution {μ : Measure I} {u : ℝ → ℝ} {S : Set ℝ} {β δ r w Ks : ℝ}
    {F : ℝ → ℝ → ℝ} {e : I → ℝ} {ks : I → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrate : β * (1 - δ + r) = 1) (hu : ConcaveOn ℝ S u)
    (hfirm : ∀ K L, 0 ≤ K → 0 ≤ L → F K L - r * K - w * L ≤ F Ks 1 - r * Ks - w * 1)
    (hclear : ∫ i, ks i ∂μ = Ks) (hdom : ∀ i, (1 - δ + r - 1) * ks i + w * e i ∈ S) :
    IsSSEquilibriumGrowth μ u S β δ F e r w
      (fun i k => u (k * (r - δ) + w * e i) / (1 - β)) (fun _ => id) ks Ks := by
  refine ⟨fun i => ?_, hfirm, hclear, hdom, fun _ => rfl⟩
  have h := ss_value (y := w * e i) hβ0 hβ1 hrate hu
  have e1 : (fun x => u ((1 - δ + r - 1) * x + w * e i) / (1 - β)) =
      fun k => u (k * (r - δ) + w * e i) / (1 - β) := by funext k; ring_nf
  rwa [e1] at h

/-- **AKMM, p. 149: the steady-state capital stock.** With `F(K, 1) = AK^α`, `0 < α < 1`,
`A > 0`, `0 < β`, the conditions `β(1 − δ + r) = 1` and `r = αAK^{α−1}` with `K > 0` give
`K = (αA/(1/β − 1 + δ))^{1/(1−α)}`. -/
theorem definition_8_capital {A α β δ r K : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hK : 0 < K) (hrate : β * (1 - δ + r) = 1) (hr : r = α * A * K ^ (α - 1)) :
    K = (α * A / (1 / β - 1 + δ)) ^ (1 - α)⁻¹ := by
  have hr' : r = 1 / β - 1 + δ := by field_simp; linarith
  have hrpos : 0 < r := by rw [hr]; exact mul_pos (mul_pos hα0 hA) (Real.rpow_pos_of_pos hK _)
  rw [← hr']
  have e : α * A / r = K ^ (1 - α) := by
    rw [hr, show (1 : ℝ) - α = -(α - 1) by ring, Real.rpow_neg hK.le]
    have := (Real.rpow_pos_of_pos hK (α - 1)).ne'
    have := (mul_pos hα0 hA).ne'
    field_simp
  rw [e, Real.rpow_rpow_inv hK.le (by linarith)]

/-- **AKMM, p. 149: the printed condition `β = 1 − δ + r` is false.** With `u = log` on
`(0, ∞)`, `β = 1/2`, `δ = 1`, `F(K, L) = 4K^{1/2}L^{1/2}`, `r = w = 2`, `K* = 1` and every
consumer holding `kᵢ* = 1` with `eᵢ = 1`, `gᵢ(k) = k` and `Vᵢ(k) = 2 log(k + 2)` form a
steady-state equilibrium (Definition 8), and `1 − δ + r = 2 ≠ β`. -/
theorem definition_8_printed_counterexample {μ : Measure I} [IsProbabilityMeasure μ] :
    IsSSEquilibriumGrowth μ Real.log (Set.Ioi 0) (1 / 2) 1
      (fun K L => 4 * K ^ (1 / 2 : ℝ) * L ^ (1 - 1 / 2 : ℝ)) (fun _ => 1) 2 2
      (fun i k => Real.log (k * (2 - 1) + 2 * (fun _ : I => (1 : ℝ)) i) / (1 - 1 / 2))
      (fun _ => id) (fun _ => 1) 1 ∧ (1 - 1 + 2 : ℝ) ≠ 1 / 2 := by
  refine ⟨?_, by norm_num⟩
  have hfirm := (growth_firm_optimal (A := 4) (α := 1 / 2) (K := 1) (L := 1) (by norm_num)
    (by norm_num) (by norm_num) one_pos one_pos)
  simp only [Real.one_rpow, mul_one] at hfirm
  norm_num at hfirm
  refine definition_8_any_distribution (by norm_num) (by norm_num) (by norm_num)
    (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi) (fun K L hK hL => ?_) (by simp)
    (fun i => by norm_num)
  have := hfirm.2 K L hK hL
  simp only [cdProfit] at this
  norm_num
  linarith

end AKMM.CompetitiveEquilibrium
