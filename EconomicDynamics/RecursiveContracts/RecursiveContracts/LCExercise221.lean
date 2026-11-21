/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.LCLagrangian
import RecursiveContracts.LCZhang
import RecursiveContracts.LCAutarky

/-!
# Exercise 22.1 and the alternative characterisation (Miao §22.1.3, pp. 780–781, 797–798)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1.3 and Exercise 22.1 (Zhang 2012),
deterministic endowments `y_t > 0` with bounded `y` and `u(y)`. Utility `u` is strictly
increasing on `(0, ∞)` with inverse `g : ℝ → (0, ∞)`, and concave with a positive, decreasing
derivative `du` (supporting-line form `u(z) ≤ u(c) + du(c)(z − c)`).

* `lc_optimal_of_marginal`: a feasible nondecreasing bounded plan whose incentive constraint
  binds at date 0 and at every date at which consumption changes is optimal (Lagrangian
  sufficiency with `μ_t = 1/u'(c_t)`).
* `ex_22_1a`: decreasing endowments: constant consumption with `u(c) = (1 − β) U_d(y₀)`.
* `ex_22_1b`: increasing endowments: autarky.
* `ex_22_1c`: in general `c_t = max{c_{t-1}, h(y_t)}`, `c₀ = h(y₀)`, with
  `h = u⁻¹(inf_{τ ≥ 1} Σ_{t<τ} β^t u(y_t) / Σ_{t<τ} β^t)` is optimal.
* `lc_d_tau`, `lc_h_isGLB`: the book's `d_i(τ)` and `h = inf_τ d(τ)` (p. 780–781).
* `lc_c0_strictMono`, `lc_c0_gt_h`: the initial consumption solving the binding participation
  constraint is unique, equals `h(y₀)` when `v₀ = U_d(y₀)`, and exceeds it when `v₀ > U_d(y₀)`.

Corrections. In Exercise 22.1(c) the minimum over `τ` need not exist: for `u(y) = (1, 0, 0, …)`
the averages strictly decrease (`lc_ex_22_1c_min_not_attained`), so `min` must be read as `inf`
(as in the main text, p. 781). And `h` depends on the date (the whole future endowment path),
not on `y_t = θᵢ` alone: `lc_h_depends_on_future` gives two dates with the same endowment and
different `h`.
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- The increments of a sequence, `α₀ = μ₀`, `α_{t+1} = μ_{t+1} − μ_t`. -/
def lc_incr (μ : ℕ → ℝ) : ℕ → ℝ
  | 0 => μ 0
  | t + 1 => μ (t + 1) - μ t

/-- (22.10) inverted: the cumulative sums of the increments are `μ`. -/
theorem lc_cumMult_incr (μ : ℕ → ℝ) (t : ℕ) : lc_cumMult (lc_incr μ) t = μ t := by
  induction t with
  | zero => simp [lc_cumMult, lc_incr]
  | succ t ih =>
    rw [(eq_22_10 _).2, ih]
    simp [lc_incr]

/-- The inverse of a strictly increasing utility is strictly increasing. -/
theorem lc_g_strictMono {u g : ℝ → ℝ} (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a)
    (humono : StrictMonoOn u (Set.Ioi 0)) : StrictMono g := by
  intro a b hab
  by_contra h
  push Not at h
  have := humono.monotoneOn (hgpos b) (hgpos a) h
  rw [hug, hug] at this
  linarith

/-- `V_t(x) = V_0(x_{t+·})`. -/
theorem lc_detValue_shift (β : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    lc_detValue β x t = lc_detValue β (fun j => x (t + j)) 0 := by
  simp [lc_detValue]

/-- Miao, p. 780 (sufficiency in the form used by Zhang): a feasible, nondecreasing, bounded
plan whose incentive constraint binds at date 0 and at every date at which consumption changes
is optimal; the multipliers are `μ_t = 1/u'(c_t)`. -/
theorem lc_optimal_of_marginal {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} {y : ℕ → ℝ}
    (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) (du : ℝ → ℝ)
    (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) {cs : ℕ → ℝ}
    (hcs : lc_detFeasible β u y (lc_detU β u y 0) cs) (hmono : Monotone cs)
    (hbind0 : lc_detValue β (fun s => u (cs s)) 0 = lc_detU β u y 0)
    (hbind : ∀ t, cs (t + 1) ≠ cs t →
      lc_detValue β (fun s => u (cs s)) (t + 1) = lc_detU β u y (t + 1))
    {c : ℕ → ℝ} (hc : lc_detFeasible β u y (lc_detU β u y 0) c) :
    lc_detPrincipal β y c ≤ lc_detPrincipal β y cs := by
  have hpos := hcs.1
  obtain ⟨K, hK⟩ := hcs.2.1
  set μ : ℕ → ℝ := fun t => (du (cs t))⁻¹ with hμ
  have hμmono : ∀ t, μ t ≤ μ (t + 1) := by
    intro t
    have h := hduanti (hpos t) (hpos (t + 1)) (hmono (Nat.le_succ t))
    exact inv_anti₀ (hdupos _ (hpos _)) h
  have hα : ∀ t, 0 ≤ lc_incr μ t := by
    intro t
    cases t with
    | zero => exact (inv_pos.mpr (hdupos _ (hpos 0))).le
    | succ t => simp only [lc_incr]; linarith [hμmono t]
  have hKpos : 0 < K := lt_of_lt_of_le (hpos 0) ((le_abs_self _).trans (hK 0).1)
  refine lc_lagrangian_sufficiency hβ0 hβ1 hyb hcs (lc_incr μ) hα le_rfl (fun t => ?_)
    (by simp) (Kμ := (du K)⁻¹) (fun t => ?_) (fun t z hz => ?_) hc
  · cases t with
    | zero => rw [hbind0, sub_self, mul_zero]
    | succ t =>
      by_cases h : cs (t + 1) = cs t
      · simp only [lc_incr, hμ, h, sub_self, zero_mul]
      · rw [hbind t h, sub_self, mul_zero]
  · rw [lc_cumMult_incr]
    have hle : cs t ≤ K := (le_abs_self _).trans (hK t).1
    exact inv_anti₀ (hdupos K hKpos) (hduanti (hpos t) hKpos hle)
  · rw [lc_cumMult_incr, add_zero]
    have h := hsupp (cs t) (hpos t) z hz
    have hd := hdupos _ (hpos t)
    have : μ t * u z ≤ μ t * u (cs t) + (z - cs t) := by
      have := mul_le_mul_of_nonneg_left h (inv_pos.mpr hd).le
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] at this
      exact this
    linarith

/-- **Exercise 22.1(a)** (Miao, p. 797). If endowments decrease (`y₀ ≥ y₁ ≥ ⋯`), the optimal
contract has constant consumption with `u(c_t) = (1 − β) U_d(y₀)`. -/
theorem ex_22_1a {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} {y : ℕ → ℝ}
    (hy0 : ∀ t, 0 < y t) (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) (hyd : Antitone y)
    (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (humono : StrictMonoOn u (Set.Ioi 0))
    (du : ℝ → ℝ) (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) :
    let cbar := g ((1 - β) * lc_detU β u y 0)
    u cbar = (1 - β) * lc_detU β u y 0 ∧
      lc_detFeasible β u y (lc_detU β u y 0) (fun _ => cbar) ∧
      ∀ c, lc_detFeasible β u y (lc_detU β u y 0) c →
        lc_detPrincipal β y c ≤ lc_detPrincipal β y (fun _ => cbar) := by
  intro cbar
  have h1 : 0 < 1 - β := by linarith
  obtain ⟨K, hK⟩ := hyb
  have hx : ∀ t, |u (y t)| ≤ K := fun t => (hK t).2
  have hU : ∀ t, lc_detU β u y t ≤ lc_detU β u y 0 := by
    have hstep : ∀ t, lc_detU β u y (t + 1) ≤ lc_detU β u y t := by
      intro t
      unfold lc_detU lc_detValue
      refine Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 j))
        (lc_summable_geom hβ0 hβ1 (x := fun j => u (y (t + 1 + j))) (fun _ => hx _))
        (lc_summable_geom hβ0 hβ1 (x := fun j => u (y (t + j))) (fun _ => hx _))
      exact humono.monotoneOn (hy0 _) (hy0 _) (hyd (by omega))
    intro t
    exact (antitone_nat_of_succ_le hstep) (Nat.zero_le t)
  have hucbar : u cbar = (1 - β) * lc_detU β u y 0 := hug _
  have hV : ∀ t, lc_detValue β (fun _ => u cbar) t = lc_detU β u y 0 := by
    intro t
    rw [lc_detValue_const hβ0 hβ1, hucbar]
    field_simp
  have hfeas : lc_detFeasible β u y (lc_detU β u y 0) (fun _ => cbar) :=
    ⟨fun _ => hgpos _, ⟨max |cbar| |u cbar|, fun _ => ⟨le_max_left _ _, le_max_right _ _⟩⟩,
      fun t => by rw [hV]; exact hU t, by rw [hV]⟩
  refine ⟨hucbar, hfeas, fun c hc => ?_⟩
  exact lc_optimal_of_marginal hβ0 hβ1 ⟨K, hK⟩ du hdupos hduanti hsupp hfeas
    (fun _ _ _ => le_rfl) (hV 0) (fun t h => (h rfl).elim) hc

/-- **Exercise 22.1(b)** (Miao, p. 797). If endowments increase (`y₀ ≤ y₁ ≤ ⋯`), autarky is the
optimal contract. -/
theorem ex_22_1b {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} {y : ℕ → ℝ}
    (hy0 : ∀ t, 0 < y t) (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K) (hyi : Monotone y)
    (du : ℝ → ℝ) (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) :
    lc_detFeasible β u y (lc_detU β u y 0) y ∧
      ∀ c, lc_detFeasible β u y (lc_detU β u y 0) c →
        lc_detPrincipal β y c ≤ lc_detPrincipal β y y := by
  have hfeas : lc_detFeasible β u y (lc_detU β u y 0) y :=
    ⟨hy0, hyb, fun _ => le_rfl, le_rfl⟩
  exact ⟨hfeas, fun c hc => lc_optimal_of_marginal hβ0 hβ1 hyb du hdupos hduanti hsupp hfeas
    hyi rfl (fun _ _ => rfl) hc⟩

/-- **Exercise 22.1(c)** (Miao, p. 798), and (22.11) (p. 780) in the deterministic case. With
`h_t = u⁻¹(m_t)`, `m_t = inf_{τ ≥ 1} Σ_{j<τ} β^j u(y_{t+j}) / Σ_{j<τ} β^j` (`lc_m`), the plan
`c₀ = h₀`, `c_t = max{c_{t-1}, h_t}` is feasible and optimal. -/
theorem ex_22_1c {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} {y : ℕ → ℝ}
    (hyb : ∃ K, ∀ t, |y t| ≤ K ∧ |u (y t)| ≤ K)
    (hgpos : ∀ a, 0 < g a) (hug : ∀ a, u (g a) = a) (humono : StrictMonoOn u (Set.Ioi 0))
    (du : ℝ → ℝ) (hdupos : ∀ c, 0 < c → 0 < du c) (hduanti : AntitoneOn du (Set.Ioi 0))
    (hsupp : ∀ c, 0 < c → ∀ z, 0 < z → u z ≤ u c + du c * (z - c)) :
    let h : ℕ → ℝ := fun t => g (lc_m β (fun s => u (y s)) t)
    let c : ℕ → ℝ := fun t => g (lc_run (lc_m β (fun s => u (y s))) 0 t)
    c 0 = h 0 ∧ (∀ t, c (t + 1) = max (c t) (h (t + 1))) ∧
      lc_detFeasible β u y (lc_detU β u y 0) c ∧
      ∀ c', lc_detFeasible β u y (lc_detU β u y 0) c' →
        lc_detPrincipal β y c' ≤ lc_detPrincipal β y c := by
  intro h c
  obtain ⟨K, hK⟩ := hyb
  set x : ℕ → ℝ := fun s => u (y s) with hxdef
  have hx : ∀ t, |x t| ≤ K := fun t => (hK t).2
  set m := lc_m β x
  set a := lc_run m 0
  have hm := lc_m_abs_le hβ0 hx
  have ha := lc_run_abs_le m hm 0
  have hgmono := (lc_g_strictMono hgpos hug humono).monotone
  have hua : ∀ t, u (c t) = a t := fun t => hug _
  have hasucc : ∀ t, a (t + 1) = max (a t) (m (t + 1)) := by
    intro t; change lc_run m 0 (t + 1) = max (lc_run m 0 t) (m (t + 1)); rw [lc_run_succ, zero_add]
  have hsplit : ∀ t j, a (t + j) = max (a t) (lc_run m t j) := by
    intro t j
    change lc_run m 0 (t + j) = max (lc_run m 0 t) (lc_run m t j)
    rw [lc_run_add, zero_add]
  have hVc : ∀ t, lc_detValue β (fun s => u (c s)) t = lc_detValue β (fun j => a (t + j)) 0 := by
    intro t; rw [lc_detValue_shift]; simp only [hua]
  have hIC : ∀ t, lc_detU β u y t ≤ lc_detValue β (fun s => u (c s)) t := by
    intro t
    rw [hVc, lc_detU, ← lc_zhang_identity hβ0 hβ1 hx t]
    exact lc_detValue_mono hβ0 hβ1 (lc_run_abs_le m hm t) (fun j => ha _)
      (fun j => by change lc_run m t j ≤ a (t + j); rw [hsplit]; exact le_max_right _ _) 0
  have hbindt : ∀ t, a t = m t → lc_detValue β (fun s => u (c s)) t = lc_detU β u y t := by
    intro t hat
    rw [hVc, lc_detU, ← lc_zhang_identity hβ0 hβ1 hx t]
    unfold lc_detValue
    refine tsum_congr fun j => ?_
    simp only [zero_add]
    rw [hsplit, max_eq_right (by rw [hat]; simpa using (lc_run_ge m t j).2)]
  have hc0 : c 0 = h 0 := rfl
  have hcsucc : ∀ t, c (t + 1) = max (c t) (h (t + 1)) := by
    intro t
    simp only [c, h]
    rw [← hgmono.map_max]
    change g (a (t + 1)) = _
    rw [hasucc]
  have hfeas : lc_detFeasible β u y (lc_detU β u y 0) c := by
    refine ⟨fun t => hgpos _, ⟨max (g K) K, fun t => ⟨?_, ?_⟩⟩, hIC, hIC 0⟩
    · rw [abs_of_pos (hgpos _)]
      exact (hgmono (abs_le.mp (ha t)).2).trans (le_max_left _ _)
    · rw [hua]; exact (ha t).trans (le_max_right _ _)
  refine ⟨hc0, hcsucc, hfeas, fun c' hc' => ?_⟩
  refine lc_optimal_of_marginal hβ0 hβ1 ⟨K, hK⟩ du hdupos hduanti hsupp hfeas
    (hgmono.comp (lc_run_mono m 0)) (hbindt 0 rfl) (fun t hne => hbindt (t + 1) ?_) hc'
  rcases max_choice (a t) (m (t + 1)) with he | he
  · exfalso
    apply hne
    change g (a (t + 1)) = g (a t)
    rw [hasucc, he]
  · rw [hasucc, he]

/-- Miao, p. 780, the definition of `d_i(τ)` in the deterministic case: the constant consumption
`d = u⁻¹(A_t(τ))` on `[t, t+τ)` makes the incentive constraints at `t` and `t + τ` bind:
`Σ_{j<τ} β^j u(d) = U_d(y_t) − β^τ U_d(y_{t+τ})`. -/
theorem lc_d_tau {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} (hug : ∀ a, u (g a) = a)
    {y : ℕ → ℝ} {K : ℝ} (hx : ∀ t, |u (y t)| ≤ K) (t τ : ℕ) (hτ : 1 ≤ τ) :
    ∑ j ∈ Finset.range τ, β ^ j * u (g (lc_A β (fun s => u (y s)) t τ)) =
      lc_detU β u y t - β ^ τ * lc_detU β u y (t + τ) := by
  rw [hug, ← Finset.sum_mul]
  have hB := lc_B_ge_one hβ0 hτ
  have := lc_detValue_split hβ0 hβ1 hx t τ
  unfold lc_detU
  rw [this]
  change lc_B β τ * (lc_S β (fun s => u (y s)) t τ / lc_B β τ) = _
  field_simp
  simp [lc_S]

/-- Miao, p. 780, the definition of `d_i(τ)` in the Markov model of §22.1 for a deterministic
date `τ ≥ 1`: the constant consumption `d` with
`u(d) = Σ_{t<τ} β^t E[u(y_t) | y₀ = θᵢ] / Σ_{t<τ} β^t` satisfies
`E[Σ_{t<τ} β^t u(d) | y₀ = θᵢ] = U_d(θᵢ) − E[β^τ U_d(y_τ) | y₀ = θᵢ]`. -/
theorem lc_d_markov {ι : Type*} [Fintype ι] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {u g : ℝ → ℝ} (hug : ∀ a, u (g a) = a)
    (r : ι → ℝ) (i : ι) (τ : ℕ) (hτ : 1 ≤ τ) :
    ∑ t ∈ Finset.range τ, β ^ t * u (g ((∑ t ∈ Finset.range τ,
        β ^ t * (lc_condExp pl)^[t] r i) / lc_B β τ)) =
      lc_autarky β pl r i - β ^ τ * (lc_condExp pl)^[τ] (lc_autarky β pl r) i := by
  rw [hug, ← Finset.sum_mul, lc_autarky_split hβ0 hβ1 hpl r τ i]
  have hB := lc_B_ge_one hβ0 hτ
  change lc_B β τ * _ = _
  field_simp
  ring

/-- Miao, p. 781: `h = inf_{τ ≥ 1} d(τ)`: `u⁻¹(m_t)` is the greatest lower bound of the levels
`d_t(τ) = u⁻¹(A_t(τ))`, `τ ≥ 1`. -/
theorem lc_h_isGLB {β : ℝ} (hβ0 : 0 ≤ β) {u g : ℝ → ℝ} (hgpos : ∀ a, 0 < g a)
    (hug : ∀ a, u (g a) = a) (hgu : ∀ c, 0 < c → g (u c) = c)
    (humono : StrictMonoOn u (Set.Ioi 0)) {x : ℕ → ℝ} {K : ℝ} (hx : ∀ t, |x t| ≤ K) (t : ℕ) :
    IsGLB (Set.range fun τ : ℕ => g (lc_A β x t (τ + 1))) (g (lc_m β x t)) := by
  have hgmono := (lc_g_strictMono hgpos hug humono).monotone
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨τ, rfl⟩
    exact hgmono (lc_m_le_A hβ0 hx t (by omega))
  · rcases le_or_gt b 0 with hb0 | hb0
    · exact hb0.trans (hgpos _).le
    · have : u b ≤ lc_m β x t := le_ciInf fun τ => by
        have := humono.monotoneOn hb0 (hgpos _) (hb ⟨τ, rfl⟩)
        rwa [hug] at this
      rw [← hgu b hb0]
      exact hgmono this

/-- The consumption path from an initial utility level `z`:
`a₀ = z`, `a_{t+1} = max{a_t, m_{t+1}}` (Miao, p. 781). -/
def lc_zpath (m : ℕ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => z
  | t + 1 => max (lc_zpath m z t) (m (t + 1))

theorem lc_zpath_abs_le (m : ℕ → ℝ) {M : ℝ} (hm : ∀ t, |m t| ≤ M) (z : ℝ) (t : ℕ) :
    |lc_zpath m z t| ≤ max |z| M := by
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    simp only [lc_zpath]
    rcases max_choice (lc_zpath m z t) (m (t + 1)) with h | h <;> rw [h]
    · exact ih
    · exact (hm _).trans (le_max_right _ _)

/-- Miao, p. 781: "one can solve for a unique solution for `c₀`": the agent's value
`F(z) = Σ_t β^t a_t` of the path from initial utility `z` is strictly increasing in `z`, and
`F(m₀) = U_d(y₀)`. Hence the binding participation constraint `F(z) = v₀` has at most one
solution, `c₀ = u⁻¹(z)`. -/
theorem lc_c0_strictMono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) :
    StrictMono (fun z => lc_detValue β (lc_zpath (lc_m β x) z) 0) ∧
      lc_detValue β (lc_zpath (lc_m β x) (lc_m β x 0)) 0 = lc_detValue β x 0 := by
  have hm := lc_m_abs_le hβ0 hx
  refine ⟨fun z z' hzz' => ?_, ?_⟩
  · have hmono : ∀ t, lc_zpath (lc_m β x) z t ≤ lc_zpath (lc_m β x) z' t := by
      intro t
      induction t with
      | zero => exact hzz'.le
      | succ t ih => exact max_le_max ih le_rfl
    set B := max (max |z| |z'|) M
    have hb : ∀ w, |w| ≤ max |z| |z'| → ∀ t, |lc_zpath (lc_m β x) w t| ≤ B := fun w hw t =>
      (lc_zpath_abs_le (lc_m β x) hm w t).trans (max_le_max hw le_rfl)
    have hbz := hb z (le_max_left _ _)
    have hbz' := hb z' (le_max_right _ _)
    have h1 := lc_detValue_mono hβ0 hβ1 hbz hbz' hmono 1
    simp only
    rw [lc_detValue_split0 hβ0 hβ1 hbz 1, lc_detValue_split0 hβ0 hβ1 hbz' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one]
    change z + _ < z' + _
    nlinarith [mul_le_mul_of_nonneg_left h1 hβ0]
  · rw [← lc_zhang_identity hβ0 hβ1 hx 0]
    congr 1
    funext t
    induction t with
    | zero => rfl
    | succ t ih => simp only [lc_zpath, lc_run_succ, ih, zero_add]

/-- Miao, p. 781: "`c₀(v₀, θᵢ) > h(θᵢ)` when `v₀ > U_d(θᵢ)`" (deterministic case): if the path
from initial utility `z` delivers more than `U_d(y₀)`, then `z > m₀`, so `c₀ = u⁻¹(z) > h(y₀)`. -/
theorem lc_c0_gt_h {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u g : ℝ → ℝ} (hgpos : ∀ a, 0 < g a)
    (hug : ∀ a, u (g a) = a) (humono : StrictMonoOn u (Set.Ioi 0)) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (z : ℝ)
    (hz : lc_detValue β x 0 < lc_detValue β (lc_zpath (lc_m β x) z) 0) :
    lc_m β x 0 < z ∧ g (lc_m β x 0) < g z := by
  obtain ⟨hmono, h0⟩ := lc_c0_strictMono hβ0 hβ1 hx
  have : lc_m β x 0 < z := by
    by_contra h
    push Not at h
    have := hmono.monotone h
    linarith
  exact ⟨this, lc_g_strictMono hgpos hug humono this⟩

/-- Correction to **Exercise 22.1(c)** (Miao, p. 798): the minimum over `τ ≥ 1` need not be
attained. For `u(y) = (1, 0, 0, …)` (e.g. `u = log`, `y = (e, 1, 1, …)`) and `0 < β < 1` the
averages `A₀(τ) = 1/B_τ` strictly decrease, so no `τ` minimises them; `min` must be `inf`. -/
theorem lc_ex_22_1c_min_not_attained {β : ℝ} (hβ0 : 0 < β) :
    let x : ℕ → ℝ := fun t => if t = 0 then 1 else 0
    (∀ τ, 1 ≤ τ → lc_A β x 0 (τ + 1) < lc_A β x 0 τ) ∧
      ¬ ∃ τ, 1 ≤ τ ∧ ∀ τ', 1 ≤ τ' → lc_A β x 0 τ ≤ lc_A β x 0 τ' := by
  intro x
  have hS : ∀ τ, 1 ≤ τ → lc_S β x 0 τ = 1 := by
    intro τ hτ
    unfold lc_S
    simp only [zero_add, x, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range τ) 0 (fun j => β ^ j)]
    simp [Finset.mem_range.mpr (by omega : 0 < τ)]
  have hdec : ∀ τ, 1 ≤ τ → lc_A β x 0 (τ + 1) < lc_A β x 0 τ := by
    intro τ hτ
    unfold lc_A
    rw [hS τ hτ, hS (τ + 1) (by omega)]
    have hB := lc_B_ge_one hβ0.le hτ
    have hB' : lc_B β (τ + 1) = lc_B β τ + β ^ τ := by
      unfold lc_B; rw [Finset.sum_range_succ]
    rw [hB']
    have := pow_pos hβ0 τ
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  refine ⟨hdec, ?_⟩
  rintro ⟨τ, hτ, hmin⟩
  have := hmin (τ + 1) (by omega)
  linarith [hdec τ hτ]

/-- Correction to the notation `h(θᵢ)` (Miao, pp. 780–781 and Exercise 22.1(c)): in the
deterministic model the minimum consumption level depends on the whole future endowment path,
not on the current endowment alone. For `u(y) = (1, 0, 1, 1, …)` and `0 < β < 1`,
`u(y₀) = u(y₂)` but `m₀ ≤ 1/(1 + β) < 1 = m₂`. -/
theorem lc_h_depends_on_future {β : ℝ} (hβ0 : 0 < β) :
    let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1
    x 0 = x 2 ∧ lc_m β x 0 < lc_m β x 2 := by
  intro x
  have hx : ∀ t, |x t| ≤ 1 := fun t => by simp only [x]; split_ifs <;> simp
  refine ⟨rfl, ?_⟩
  have h2 : lc_m β x 2 = 1 := by
    have : ∀ τ, lc_A β x 2 (τ + 1) = 1 := by
      intro τ
      have hB := lc_B_ge_one hβ0.le (by omega : 1 ≤ τ + 1)
      unfold lc_A
      have : lc_S β x 2 (τ + 1) = lc_B β (τ + 1) := by
        unfold lc_S lc_B
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : 2 + j ≠ 1 := by omega
        simp only [x, hj, ↓reduceIte, mul_one]
      rw [this, div_self (by linarith)]
    unfold lc_m
    simp only [this, ciInf_const]
  have h0 : lc_m β x 0 ≤ 1 / (1 + β) := by
    have := lc_m_le_A hβ0.le hx 0 (by omega : 1 ≤ 2)
    have hA : lc_A β x 0 2 = 1 / (1 + β) := by
      simp [lc_A, lc_S, lc_B, Finset.sum_range_succ, x]
    rwa [hA] at this
  rw [h2]
  refine lt_of_le_of_lt h0 ?_
  rw [div_lt_one (by linarith)]
  linarith

end Miao.RecursiveContracts
