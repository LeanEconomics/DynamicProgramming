/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.HMKalman
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Life-cycle saving with learning: Example 10.2.1 and Exercise 10.6(b)–(d)

Miao, Example 10.2.1, p. 342, and Exercise 10.6, p. 346. The household has wealth
`W = Rs_t + exp(y_t)` and chooses `s_{t+1}` (consumption `c_t = W − s_{t+1}`, the budget (10.15)).
Its beliefs about the hidden income component are summarised by the forecast `x̂_{t|t−1}`; the
next forecast is `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})` ((10.16) with `A = ρ`, `G = 1`,
the setting of Exercise 10.6 with `α = β = 0`) and the next signal is
`y_{t+1} | yᵗ ~ N(x̂_{t+1|t}, Ω_{t+1|t})` (`ex_10_6_a_predictive`).

* `hm_gV u β R ρ K Ω T feas k` is the value function `V_t(s_t, y_t, x̂_{t|t−1})` of
  Example 10.2.1 at date `t = T − k`, with `V_{T+1} = 0`, utility `u`, gains `K_t`, innovation
  variances `Ω_t`, and feasible savings `feas k` (`s_{t+1} ≥ 0` in the book); the maximum is a
  `sSup`. `example_10_2_1` is the book's Bellman equation, `example_10_2_1_terminal` the last date.
* (b) `T = 1`, CARA utility `u(c) = −exp(−γc)/γ`, `s_{t+1} ≥ 0`: `V₁ = u(W)` and
  `V₀ = u(W − s*) − (β/γ)N exp(−γRs*)` with `s* = max(0, (γW + log(βRN))/(γ(1 + R)))`,
  `N = E[exp(−γ exp(y₁)) | y₀] = ∫ exp(−γe^{y′}) dN(x̂_{1|0}, Ω_{1|0})` (`ex_10_6_b_terminal`,
  `ex_10_6_b`).
* (c) Any finite `T`. With the borrowing constraint at every date the value is not of closed form
  (already for `T = 1` the policy has the kink of (b)); we solve the problem with
  `s_{T+1} ≥ 0` only (borrowing allowed before `T`, the usual CARA setting). Then
  `V_t = −(1/γ) φ_k(x̂_{t+1|t}) exp(−γ a_k W)`, `k = T − t`, with `a₀ = 1`,
  `a_{k+1} = a_kR/(1 + a_kR)` (so `1/a_k = Σ_{j≤k} R⁻ʲ`), `φ₀ = 1`,
  `φ_{k+1}(m) = (βa_kR N_k(m))^{1/(1+a_kR)}(1 + 1/(a_kR))`,
  `N_k(m) = ∫ exp(−γa_ke^{y′}) φ_k(ρm + ρK(y′ − m)) dN(m, Ω)`, and the optimal saving is
  `s_{t+1} = (γW + log(βa_kR N_k))/(γ(1 + a_kR))` (`ex_10_6_c`, `ex_10_6_c_policy`, `hm_a_inv`).
  The `φ_k` are continuous, positive and bounded, so every expectation is finite and positive
  (`hm_phi_props`, `hm_N_props`).
* (d) With `x̂_{t|t}` as the state: `x̂_{t+1|t} = ρx̂_{t|t}`, `y_{t+1} ~ N(ρx̂_{t|t}, Ω_{t+1|t})`
  and
  `x̂_{t+1|t+1} = ρx̂_{t|t} + K_{t+1}(y_{t+1} − ρx̂_{t|t})`; the Bellman equation `hm_gVf` in this
  state has the same value, `V^f_t(s, y, x̂_{t|t−1} + K_t(y − x̂_{t|t−1})) = V_t(s, y, x̂_{t|t−1})`
  (`ex_10_6_d`).
-/

namespace Miao.PartialInformation

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Miao, Exercise 10.6: CARA utility `u(c) = −exp(−γc)/γ`. -/
noncomputable def hm_cara (γ c : ℝ) : ℝ := -Real.exp (-γ * c) / γ

/-- Miao, Example 10.2.1, p. 342: the value `V_t(s, y, x̂_{t|t−1})` with `k = T − t` periods left
after date `t`; `V_{T+1} = 0`; savings `s′ ∈ feas k`; `c = Rs + exp(y) − s′`; the next forecast
`m = ρx̂ + ρK_t(y − x̂)` and `y′ ~ N(m, Ω_{t+1})`. -/
noncomputable def hm_gV (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, s, y, _ => sSup ((fun s' => u (R * s + Real.exp y - s')) '' feas 0)
  | k + 1, s, y, xh => sSup ((fun s' => u (R * s + Real.exp y - s') + β *
      ∫ y', hm_gV u β R ρ K Om T feas k s' y' (ρ * xh + ρ * K (T - (k + 1)) * (y - xh))
        ∂gaussianReal (ρ * xh + ρ * K (T - (k + 1)) * (y - xh)) (Om (T - k))) '' feas (k + 1))

/-- The book's `V_t(s_t, y_t, x̂_{t|t−1})` for horizon `T`. -/
noncomputable def hm_bookGV (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (t : ℕ) (s y xh : ℝ) : ℝ :=
  hm_gV u β R ρ K Om T feas (T - t) s y xh

/-- **Example 10.2.1** (Miao, p. 342), the Bellman equation: for `t < T`,
`V_t(s, y, x̂_{t|t−1}) = max_{s′} u(Rs + exp(y) − s′) + βE[V_{t+1}(s′, y′, x̂_{t+1|t})]` with
`x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y − x̂_{t|t−1})` (10.16) and `y′ ~ N(x̂_{t+1|t}, Ω_{t+1|t})`. -/
theorem example_10_2_1 (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (t : ℕ) (ht : t < T) (s y xh : ℝ) :
    hm_bookGV u β R ρ K Om T feas t s y xh = sSup ((fun s' => u (R * s + Real.exp y - s') + β *
      ∫ y', hm_bookGV u β R ρ K Om T feas (t + 1) s' y' (ρ * xh + ρ * K t * (y - xh))
        ∂gaussianReal (ρ * xh + ρ * K t * (y - xh)) (Om (t + 1))) '' feas (T - t)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt ht
  have h1 : t + k + 1 - t = k + 1 := by omega
  have h2 : t + k + 1 - (t + 1) = k := by omega
  have h3 : t + k + 1 - (k + 1) = t := by omega
  have h4 : t + k + 1 - k = t + 1 := by omega
  simp only [hm_bookGV, h1, h2, hm_gV, h3, h4]

/-- **Example 10.2.1** (Miao, p. 342), last date: `V_T(s, y, x̂) = max_{s′} u(Rs + exp(y) − s′)`
since `V_{T+1} = 0`. -/
theorem example_10_2_1_terminal (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (s y xh : ℝ) :
    hm_bookGV u β R ρ K Om T feas T s y xh =
      sSup ((fun s' => u (R * s + Real.exp y - s')) '' feas 0) := by
  simp [hm_bookGV, hm_gV]

/-- The tangent-line bound `exp x₀ (1 + (x − x₀)) ≤ exp x`. -/
theorem hm_exp_tangent (x x0 : ℝ) : Real.exp x0 * (1 + (x - x0)) ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - x0)
  calc Real.exp x0 * (1 + (x - x0)) ≤ Real.exp x0 * Real.exp (x - x0) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = Real.exp x := by rw [← Real.exp_add]; ring_nf

/-- The (negated, scaled) CARA objective `f(s′) = exp(−γ(W − s′)) + c exp(−γbs′)`. -/
noncomputable def hm_f (γ c b W s : ℝ) : ℝ :=
  Real.exp (-γ * (W - s)) + c * Real.exp (-γ * b * s)

/-- Convexity of `f`: `f(s₀) + γ(s − s₀)(exp(−γ(W − s₀)) − cb exp(−γbs₀)) ≤ f(s)`. -/
theorem hm_f_tangent (γ c b W s0 s : ℝ) (hc : 0 ≤ c) :
    hm_f γ c b W s0 + γ * (s - s0) * (Real.exp (-γ * (W - s0)) - c * b *
      Real.exp (-γ * b * s0)) ≤ hm_f γ c b W s := by
  have h1 := hm_exp_tangent (-γ * (W - s)) (-γ * (W - s0))
  have h2 := mul_le_mul_of_nonneg_left (hm_exp_tangent (-γ * b * s) (-γ * b * s0)) hc
  unfold hm_f
  nlinarith [h1, h2]

/-- Miao, Exercise 10.6(c), the one-period CARA problem without constraint: for `γ, c, b > 0`,
`s* = (γW + log(cb))/(γ(1 + b))` minimises `f` and
`f(s*) = exp(−γ(b/(1 + b))W)(cb)^{1/(1+b)}(1 + 1/b)`. -/
theorem hm_f_min {γ c b : ℝ} (hγ : 0 < γ) (hc : 0 < c) (hb : 0 < b) (W : ℝ) :
    (∀ s, hm_f γ c b W ((γ * W + Real.log (c * b)) / (γ * (1 + b))) ≤ hm_f γ c b W s) ∧
      hm_f γ c b W ((γ * W + Real.log (c * b)) / (γ * (1 + b))) =
        Real.exp (-γ * (b / (1 + b)) * W) * (c * b) ^ (1 / (1 + b)) * (1 + 1 / b) := by
  set s0 := (γ * W + Real.log (c * b)) / (γ * (1 + b)) with hs0
  have hcb : 0 < c * b := mul_pos hc hb
  have h1b : 0 < 1 + b := by linarith
  have key : Real.exp (-γ * (W - s0)) = c * b * Real.exp (-γ * b * s0) := by
    rw [← Real.exp_log hcb, ← Real.exp_add]
    congr 1
    rw [hs0]
    field_simp
    ring
  refine ⟨fun s => ?_, ?_⟩
  · have := hm_f_tangent γ c b W s0 s hc.le
    rw [key, sub_self, mul_zero, add_zero] at this
    exact this
  · have hval : hm_f γ c b W s0 = Real.exp (-γ * (W - s0)) * (1 + 1 / b) := by
      unfold hm_f
      rw [key]
      field_simp
    rw [hval, Real.rpow_def_of_pos hcb, ← Real.exp_add]
    congr 2
    rw [hs0]
    field_simp
    ring

/-- Miao, Exercise 10.6(b), the one-period CARA problem with `s′ ≥ 0`: the minimiser of `f` on
`[0, ∞)` is `max(0, s*)`. -/
theorem hm_f_min_nonneg {γ c b : ℝ} (hγ : 0 < γ) (hc : 0 < c) (hb : 0 < b) (W s : ℝ)
    (hs : 0 ≤ s) :
    hm_f γ c b W (max 0 ((γ * W + Real.log (c * b)) / (γ * (1 + b)))) ≤ hm_f γ c b W s := by
  by_cases h : 0 ≤ (γ * W + Real.log (c * b)) / (γ * (1 + b))
  · rw [max_eq_right h]
    exact (hm_f_min hγ hc hb W).1 s
  · push Not at h
    rw [max_eq_left h.le]
    have hcb : 0 < c * b := mul_pos hc hb
    have hneg : γ * W + Real.log (c * b) < 0 := by
      have hd : 0 < γ * (1 + b) := by positivity
      by_contra hn
      push Not at hn
      exact absurd h (not_lt.2 (div_nonneg hn hd.le))
    have hle : c * b ≤ Real.exp (-γ * (W - 0)) := by
      have : Real.log (c * b) < -γ * (W - 0) := by linarith
      exact ((Real.log_lt_iff_lt_exp hcb).1 this).le
    have ht := hm_f_tangent γ c b W 0 s hc.le
    have h0 : Real.exp (-γ * b * 0) = 1 := by simp
    rw [h0, mul_one] at ht
    have : 0 ≤ γ * (s - 0) * (Real.exp (-γ * (W - 0)) - c * b) :=
      mul_nonneg (mul_nonneg hγ.le (by linarith)) (by linarith)
    linarith

/-- The marginal-utility weights `a₀ = 1`, `a_{k+1} = a_kR/(1 + a_kR)`. -/
noncomputable def hm_a (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => hm_a R k * R / (1 + hm_a R k * R)

theorem hm_a_pos {R : ℝ} (hR : 0 < R) : ∀ k, 0 < hm_a R k
  | 0 => one_pos
  | k + 1 => by
    have := hm_a_pos hR k
    simp only [hm_a]
    positivity

/-- Miao, Exercise 10.6(c): `1/a_k = Σ_{j=0}^{k} R⁻ʲ` (the annuity factor). -/
theorem hm_a_inv {R : ℝ} (hR : 0 < R) :
    ∀ k, 1 / hm_a R k = ∑ j ∈ Finset.range (k + 1), R⁻¹ ^ j
  | 0 => by simp [hm_a]
  | k + 1 => by
    have ih := hm_a_inv hR k
    have ha := hm_a_pos hR k
    rw [Finset.sum_range_succ']
    simp only [pow_succ, ← Finset.sum_mul, ← ih, pow_zero]
    simp only [hm_a]
    field_simp

/-- The continuation factors `φ_k` of the CARA value function (Exercise 10.6(c)). -/
noncomputable def hm_phi (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun m => (β * hm_a R k * R * ∫ y', Real.exp (-γ * hm_a R k * Real.exp y') *
      hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m)) ∂gaussianReal m (Om (T - k))) ^
      (1 / (1 + hm_a R k * R)) * (1 + 1 / (hm_a R k * R))

/-- `N_k(m) = E[exp(−γa_k e^{y′}) φ_k(x̂′)]` with `y′ ~ N(m, Ω_{T−k})`. -/
noncomputable def hm_N (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ) (m : ℝ) : ℝ :=
  ∫ y', Real.exp (-γ * hm_a R k * Real.exp y') *
    hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m)) ∂gaussianReal m (Om (T - k))

theorem hm_phi_succ (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ) (m : ℝ) :
    hm_phi γ β R ρ K Om T (k + 1) m = (β * hm_a R k * R * hm_N γ β R ρ K Om T k m) ^
      (1 / (1 + hm_a R k * R)) * (1 + 1 / (hm_a R k * R)) := rfl

/-- If `φ_k` is continuous, positive and bounded by `B`, then `N_k` is continuous, positive and
bounded by `B`. -/
theorem hm_N_props {γ β R ρ : ℝ} (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ) (hγ : 0 < γ)
    (hR : 0 < R) (hc : Continuous (hm_phi γ β R ρ K Om T k))
    (hpos : ∀ m, 0 < hm_phi γ β R ρ K Om T k m) (B : ℝ)
    (hB : ∀ m, hm_phi γ β R ρ K Om T k m ≤ B) :
    Continuous (hm_N γ β R ρ K Om T k) ∧ (∀ m, 0 < hm_N γ β R ρ K Om T k m) ∧
      ∀ m, hm_N γ β R ρ K Om T k m ≤ B := by
  have ha := hm_a_pos hR k
  set a := hm_a R k
  set φ := hm_phi γ β R ρ K Om T k
  set g : ℝ → ℝ → ℝ := fun m y' => Real.exp (-γ * a * Real.exp y') *
    φ (ρ * m + ρ * K (T - k) * (y' - m)) with hg
  have gc : Continuous (fun p : ℝ × ℝ => g p.1 p.2) := by
    simp only [hg]
    fun_prop
  have gpos : ∀ m y', 0 < g m y' := fun m y' => mul_pos (Real.exp_pos _) (hpos _)
  have gle : ∀ m y', g m y' ≤ B := by
    intro m y'
    have e1 : Real.exp (-γ * a * Real.exp y') ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.exp_pos y'
      have : 0 < γ * a * Real.exp y' := by positivity
      linarith
    calc g m y' ≤ 1 * φ (ρ * m + ρ * K (T - k) * (y' - m)) :=
          mul_le_mul_of_nonneg_right e1 (hpos _).le
      _ ≤ B := by rw [one_mul]; exact hB _
  have gm : ∀ m, Continuous (g m) := fun m => gc.comp (Continuous.prodMk_right m)
  have gint : ∀ m (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (g m) μ := by
    intro m μ _
    refine (integrable_const B).mono' (gm m).aestronglyMeasurable (ae_of_all _ (fun y' => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (gpos m y')]
    exact gle m y'
  have hN : ∀ m, hm_N γ β R ρ K Om T k m = ∫ y', g m y' ∂gaussianReal m (Om (T - k)) :=
    fun m => rfl
  refine ⟨?_, fun m => ?_, fun m => ?_⟩
  · have e : ∀ m, hm_N γ β R ρ K Om T k m = ∫ u, g m (u + m) ∂gaussianReal 0 (Om (T - k)) := by
      intro m
      have hμ : gaussianReal m (Om (T - k)) = (gaussianReal 0 (Om (T - k))).map (· + m) := by
        rw [gaussianReal_map_add_const, zero_add]
      rw [hN, hμ, integral_map (measurable_add_const m).aemeasurable
        (gm m).aestronglyMeasurable]
    rw [show hm_N γ β R ρ K Om T k = fun m => ∫ u, g m (u + m) ∂gaussianReal 0 (Om (T - k)) from
      funext e]
    refine continuous_of_dominated (bound := fun _ => B) (fun m => ?_) (fun m => ?_)
      (integrable_const B) (ae_of_all _ (fun u => ?_))
    · exact ((gm m).comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · refine ae_of_all _ (fun u => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (gpos m _)]
      exact gle m _
    · exact gc.comp (continuous_id.prodMk (continuous_const.add continuous_id))
  · rw [hN, integral_pos_iff_support_of_nonneg (fun y' => (gpos m y').le) (gint m _)]
    have : Function.support (g m) = Set.univ :=
      Set.eq_univ_of_forall (fun y' => (gpos m y').ne')
    rw [this, measure_univ]
    exact one_pos
  · rw [hN]
    calc ∫ y', g m y' ∂gaussianReal m (Om (T - k)) ≤ ∫ _, B ∂gaussianReal m (Om (T - k)) :=
          integral_mono (gint m _) (integrable_const B) (fun y' => gle m y')
      _ = B := by simp

/-- Miao, Exercise 10.6(c): every `φ_k` is continuous, positive and bounded. -/
theorem hm_phi_props {γ β R ρ : ℝ} (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ) (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 0 < R) :
    ∀ k, Continuous (hm_phi γ β R ρ K Om T k) ∧ (∀ m, 0 < hm_phi γ β R ρ K Om T k m) ∧
      ∃ B, ∀ m, hm_phi γ β R ρ K Om T k m ≤ B
  | 0 => ⟨continuous_const, fun _ => one_pos, 1, fun _ => le_rfl⟩
  | k + 1 => by
    obtain ⟨hc, hpos, B, hB⟩ := hm_phi_props K Om T hγ hβ hR k
    obtain ⟨Nc, Npos, NB⟩ := hm_N_props K Om T k hγ hR hc hpos B hB
    have ha := hm_a_pos hR k
    have hp : 0 < 1 / (1 + hm_a R k * R) := by positivity
    have hq : 0 < 1 + 1 / (hm_a R k * R) := by positivity
    have hbase : ∀ m, 0 < β * hm_a R k * R * hm_N γ β R ρ K Om T k m :=
      fun m => by have := Npos m; positivity
    refine ⟨?_, fun m => ?_, (β * hm_a R k * R * B) ^ (1 / (1 + hm_a R k * R)) *
      (1 + 1 / (hm_a R k * R)), fun m => ?_⟩
    · have : Continuous (fun m => (β * hm_a R k * R * hm_N γ β R ρ K Om T k m) ^
          (1 / (1 + hm_a R k * R)) * (1 + 1 / (hm_a R k * R))) :=
        ((continuous_const.mul Nc).rpow_const (fun _ => Or.inr hp.le)).mul continuous_const
      exact this
    · rw [hm_phi_succ]
      exact mul_pos (Real.rpow_pos_of_pos (hbase m) _) hq
    · rw [hm_phi_succ]
      refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hbase m).le ?_ hp.le) hq.le
      have := NB m
      have : 0 < β * hm_a R k * R := by positivity
      exact mul_le_mul_of_nonneg_left (NB m) this.le

/-- The closed form `−(1/γ) φ_k(x̂_{t+1|t}) exp(−γa_k(Rs + exp y))` at date `t = T − k`. -/
noncomputable def hm_closed (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ)
    (s y xh : ℝ) : ℝ :=
  -(1 / γ) * hm_phi γ β R ρ K Om T k (ρ * xh + ρ * K (T - k) * (y - xh)) *
    Real.exp (-γ * hm_a R k * (R * s + Real.exp y))

/-- At the last date, with `s_{T+1} ≥ 0`, the household consumes its wealth:
`V_T = u(Rs + exp y)`. -/
theorem hm_terminal {γ β R ρ : ℝ} (hγ : 0 < γ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (hf : feas 0 = Set.Ici 0) (s y xh : ℝ) :
    hm_gV (hm_cara γ) β R ρ K Om T feas 0 s y xh = hm_cara γ (R * s + Real.exp y) := by
  simp only [hm_gV, hf]
  refine IsGreatest.csSup_eq ⟨⟨0, Set.mem_Ici.2 le_rfl, by simp⟩, ?_⟩
  rintro _ ⟨s', hs', rfl⟩
  simp only [hm_cara]
  have : Real.exp (-γ * (R * s + Real.exp y)) ≤ Real.exp (-γ * (R * s + Real.exp y - s')) := by
    apply Real.exp_le_exp.2
    have := Set.mem_Ici.1 hs'
    nlinarith
  exact div_le_div_of_nonneg_right (by linarith) hγ.le

/-- The expectation of a closed-form continuation value:
`E[V_k(s′, y′, m)] = −(1/γ) exp(−γa_kRs′) N_k(m)`. -/
theorem hm_int_closed {γ β R ρ : ℝ} (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ)
    (V : ℝ → ℝ → ℝ → ℝ) (hV : ∀ s y xh, V s y xh = hm_closed γ β R ρ K Om T k s y xh)
    (s' m : ℝ) :
    ∫ y', V s' y' m ∂gaussianReal m (Om (T - k)) =
      -(1 / γ) * Real.exp (-γ * (hm_a R k * R) * s') * hm_N γ β R ρ K Om T k m := by
  simp only [hV, hm_closed]
  have e : (fun y' => -(1 / γ) * hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m)) *
      Real.exp (-γ * hm_a R k * (R * s' + Real.exp y'))) = fun y' =>
      (-(1 / γ) * Real.exp (-γ * (hm_a R k * R) * s')) * (Real.exp (-γ * hm_a R k * Real.exp y') *
        hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m))) := by
    funext y'
    rw [show -γ * hm_a R k * (R * s' + Real.exp y') =
      -γ * (hm_a R k * R) * s' + -γ * hm_a R k * Real.exp y' by ring, Real.exp_add]
    ring
  rw [e, integral_const_mul]
  rfl

/-- The CARA Bellman objective in terms of `f`. -/
theorem hm_obj_eq (γ β N b W s' : ℝ) (hγ : γ ≠ 0) :
    hm_cara γ (W - s') + β * (-(1 / γ) * Real.exp (-γ * b * s') * N) =
      -(1 / γ) * hm_f γ (β * N) b W s' := by
  unfold hm_cara hm_f
  field_simp
  ring

/-- One step of backward induction for Exercise 10.6(c): if `V_k` has the closed form then the
maximisation at date `T − (k + 1)` (no constraint) is solved by
`s* = (γW + log(βN_k a_kR))/(γ(1 + a_kR))` with the closed form at `k + 1` as value. -/
theorem hm_step {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (T k : ℕ) (V : ℝ → ℝ → ℝ → ℝ)
    (hV : ∀ s y xh, V s y xh = hm_closed γ β R ρ K Om T k s y xh) (s y xh : ℝ) :
    let m := ρ * xh + ρ * K (T - (k + 1)) * (y - xh)
    let obj := fun s' => hm_cara γ (R * s + Real.exp y - s') + β *
      ∫ y', V s' y' m ∂gaussianReal m (Om (T - k))
    let sstar := (γ * (R * s + Real.exp y) +
      Real.log (β * hm_N γ β R ρ K Om T k m * (hm_a R k * R))) / (γ * (1 + hm_a R k * R))
    IsGreatest (obj '' Set.univ) (hm_closed γ β R ρ K Om T (k + 1) s y xh) ∧
      obj sstar = hm_closed γ β R ρ K Om T (k + 1) s y xh := by
  intro m obj sstar
  obtain ⟨hc, hpos, B, hB⟩ := hm_phi_props K Om T hγ hβ hR k
  obtain ⟨-, Npos, -⟩ := hm_N_props K Om T k hγ hR hc hpos B hB
  have ha := hm_a_pos hR k
  have hb : 0 < hm_a R k * R := mul_pos ha hR
  have hcN : 0 < β * hm_N γ β R ρ K Om T k m := mul_pos hβ (Npos m)
  have hobj : ∀ s', obj s' = -(1 / γ) * hm_f γ (β * hm_N γ β R ρ K Om T k m) (hm_a R k * R)
      (R * s + Real.exp y) s' := by
    intro s'
    simp only [obj]
    rw [hm_int_closed K Om T k V hV s' m, hm_obj_eq _ _ _ _ _ _ hγ.ne']
  obtain ⟨hmin, hval⟩ := hm_f_min hγ hcN hb (R * s + Real.exp y)
  have hstar : obj sstar = hm_closed γ β R ρ K Om T (k + 1) s y xh := by
    rw [hobj, hval, hm_closed, hm_phi_succ]
    simp only [hm_a]
    rw [show β * hm_N γ β R ρ K Om T k m * (hm_a R k * R) =
      β * hm_a R k * R * hm_N γ β R ρ K Om T k m by ring]
    ring
  refine ⟨⟨⟨sstar, Set.mem_univ _, hstar⟩, ?_⟩, hstar⟩
  rintro _ ⟨s', -, rfl⟩
  rw [← hstar, hobj, hobj]
  have hγ' : -(1 / γ) < 0 := by
    have : 0 < 1 / γ := by positivity
    linarith
  exact mul_le_mul_of_nonpos_left (hmin s') hγ'.le

/-- **Exercise 10.6(c)** (Miao, p. 346): with CARA utility, `α = β = 0`, and the borrowing
constraint only at the last date (`s_{T+1} ≥ 0`), the value function at date `t = T − k` is
`V_t(s, y, x̂_{t|t−1}) = −(1/γ) φ_k(x̂_{t+1|t}) exp(−γa_k(Rs + exp y))`. -/
theorem ex_10_6_c {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (T : ℕ) :
    ∀ k s y xh, hm_gV (hm_cara γ) β R ρ K Om T
      (fun k => if k = 0 then Set.Ici 0 else Set.univ) k s y xh =
        hm_closed γ β R ρ K Om T k s y xh
  | 0, s, y, xh => by
    rw [hm_terminal hγ K Om T _ (by simp) s y xh]
    simp only [hm_closed, hm_phi, hm_a, hm_cara]
    ring_nf
  | k + 1, s, y, xh => by
    have ih := ex_10_6_c (ρ := ρ) hγ hβ hR K Om T k
    have h := (hm_step hγ hβ hR K Om T k _ ih s y xh).1
    simp only [hm_gV, Nat.add_one_ne_zero, ↓reduceIte]
    exact h.csSup_eq

/-- **Exercise 10.6(c)** (Miao, p. 346), the policy: at date `t = T − (k + 1)` the optimal
saving is `s_{t+1} = (γW + log(βN_k(x̂_{t+1|t}) a_kR))/(γ(1 + a_kR))`, `W = Rs + exp y`. -/
theorem ex_10_6_c_policy {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (T k : ℕ) (s y xh : ℝ) :
    let V := hm_gV (hm_cara γ) β R ρ K Om T (fun k => if k = 0 then Set.Ici 0 else Set.univ)
    let m := ρ * xh + ρ * K (T - (k + 1)) * (y - xh)
    let sstar := (γ * (R * s + Real.exp y) +
      Real.log (β * hm_N γ β R ρ K Om T k m * (hm_a R k * R))) / (γ * (1 + hm_a R k * R))
    V (k + 1) s y xh = hm_cara γ (R * s + Real.exp y - sstar) +
      β * ∫ y', V k sstar y' m ∂gaussianReal m (Om (T - k)) := by
  intro V m sstar
  simp only [V]
  have ih := ex_10_6_c (ρ := ρ) hγ hβ hR K Om T k
  rw [ex_10_6_c (ρ := ρ) hγ hβ hR K Om T (k + 1)]
  exact (hm_step hγ hβ hR K Om T k _ ih s y xh).2.symm

/-- **Exercise 10.6(b)** (Miao, p. 346), the last date of the `T = 1` problem: `V₁ = u(Rs + exp y)`
(`s₂ = 0`). -/
theorem ex_10_6_b_terminal {γ β R ρ : ℝ} (hγ : 0 < γ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0)
    (s y xh : ℝ) :
    hm_bookGV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 1 s y xh =
      hm_cara γ (R * s + Real.exp y) :=
  hm_terminal hγ K Om 1 (fun _ => Set.Ici 0) rfl s y xh

/-- **Exercise 10.6(b)** (Miao, p. 346): with `T = 1`, CARA utility and `s_{t+1} ≥ 0`, the date-0
value is `V₀ = u(W − s*) − (β/γ) N exp(−γRs*)` with `W = Rs + exp(y)`,
`N = ∫ exp(−γe^{y′}) dN(x̂_{1|0}, Ω_{1|0})` and `s* = max(0, (γW + log(βNR))/(γ(1 + R)))`;
`s*` is the optimal saving. -/
theorem ex_10_6_b {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (s y xh : ℝ) :
    let m := ρ * xh + ρ * K 0 * (y - xh)
    let N := ∫ y', Real.exp (-γ * Real.exp y') ∂gaussianReal m (Om 1)
    let sstar := max 0 ((γ * (R * s + Real.exp y) + Real.log (β * N * R)) / (γ * (1 + R)))
    0 < N ∧ 0 ≤ sstar ∧
      hm_bookGV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 0 s y xh =
        hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) ∧
      ∀ s', 0 ≤ s' → hm_cara γ (R * s + Real.exp y - s') +
          β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) ≤
        hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) := by
  intro m N sstar
  obtain ⟨hc, hpos, B, hB⟩ := hm_phi_props (β := β) (ρ := ρ) K Om 1 hγ hβ hR 0
  obtain ⟨-, Npos, -⟩ := hm_N_props K Om 1 0 hγ hR hc hpos B hB
  have hNN : hm_N γ β R ρ K Om 1 0 m = N := by
    simp only [hm_N, hm_a, hm_phi, mul_one, Nat.sub_zero]
    rfl
  have hN : 0 < N := hNN ▸ Npos m
  have hV0 : ∀ s y xh, hm_gV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 0 s y xh =
      hm_closed γ β R ρ K Om 1 0 s y xh := by
    intro s y xh
    rw [hm_terminal hγ K Om 1 (fun _ => Set.Ici 0) rfl s y xh]
    simp only [hm_closed, hm_phi, hm_a, hm_cara]
    ring_nf
  have hint : ∀ s', ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) =
      -(1 / γ) * Real.exp (-γ * R * s') * N := by
    intro s'
    have := hm_int_closed (γ := γ) (β := β) (ρ := ρ) K Om 1 0
      (fun s y xh => hm_cara γ (R * s + Real.exp y)) (fun s y xh => by
        rw [← hm_terminal hγ K Om 1 (fun _ => Set.Ici 0) rfl s y xh]; exact hV0 s y xh) s' m
    simp only [hm_a, one_mul, Nat.sub_zero] at this
    rw [this, hNN]
  have hobj : ∀ s', hm_cara γ (R * s + Real.exp y - s') +
      β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) =
      -(1 / γ) * hm_f γ (β * N) R (R * s + Real.exp y) s' := by
    intro s'
    rw [hint, hm_obj_eq _ _ _ _ _ _ hγ.ne']
  have hcN : 0 < β * N := mul_pos hβ hN
  have hval : hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) =
      -(1 / γ) * hm_f γ (β * N) R (R * s + Real.exp y) sstar := by
    rw [← hobj, hint]
    ring
  have hle : ∀ s', 0 ≤ s' → hm_cara γ (R * s + Real.exp y - s') +
      β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) ≤
      hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) := by
    intro s' hs'
    rw [hobj, hval]
    have hγ' : -(1 / γ) < 0 := by
      have : 0 < 1 / γ := by positivity
      linarith
    refine mul_le_mul_of_nonpos_left ?_ hγ'.le
    have := hm_f_min_nonneg hγ hcN hR (R * s + Real.exp y) s' hs'
    simp only [sstar]
    rw [show β * N * R = β * N * R from rfl]
    exact this
  refine ⟨hN, le_max_left _ _, ?_, hle⟩
  have hset : hm_bookGV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 0 s y xh =
      sSup ((fun s' => hm_cara γ (R * s + Real.exp y - s') +
        β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1)) '' Set.Ici 0) := by
    simp only [hm_bookGV, Nat.sub_zero, hm_gV, zero_add]
    congr 1
    refine Set.image_congr (fun s' _ => ?_)
    congr 2
    refine integral_congr_ae (ae_of_all _ (fun y' => ?_))
    exact hm_terminal (β := β) (ρ := ρ) hγ K Om 1 (fun _ => Set.Ici 0) rfl s' y' m
  rw [hset]
  refine IsGreatest.csSup_eq ⟨⟨sstar, Set.mem_Ici.2 (le_max_left _ _), ?_⟩, ?_⟩
  · exact (hobj sstar).trans hval.symm
  · rintro _ ⟨s', hs', rfl⟩
    exact hle s' hs'

/-- Miao, Exercise 10.6(d): the Bellman equation with the filtered state `x̂_{t|t}`:
`x̂_{t+1|t} = ρx̂_{t|t}`, `y′ ~ N(ρx̂_{t|t}, Ω_{t+1|t})`,
`x̂_{t+1|t+1} = ρx̂_{t|t} + K_{t+1}(y′ − ρx̂_{t|t})`. -/
noncomputable def hm_gVf (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, s, y, _ => sSup ((fun s' => u (R * s + Real.exp y - s')) '' feas 0)
  | k + 1, s, y, xf => sSup ((fun s' => u (R * s + Real.exp y - s') + β *
      ∫ y', hm_gVf u β R ρ K Om T feas k s' y' (ρ * xf + K (T - k) * (y' - ρ * xf))
        ∂gaussianReal (ρ * xf) (Om (T - k))) '' feas (k + 1))

/-- **Exercise 10.6(d)** (Miao, p. 346): the Bellman equation in `x̂_{t|t}` has the same value as
the one in `x̂_{t|t−1}`: `V^f_t(s, y, x̂_{t|t−1} + K_t(y − x̂_{t|t−1})) = V_t(s, y, x̂_{t|t−1})`. -/
theorem ex_10_6_d (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) :
    ∀ k s y xh, hm_gVf u β R ρ K Om T feas k s y (xh + K (T - k) * (y - xh)) =
      hm_gV u β R ρ K Om T feas k s y xh
  | 0, s, y, xh => by simp only [hm_gVf, hm_gV]
  | k + 1, s, y, xh => by
    have ih := ex_10_6_d u β R ρ K Om T feas k
    have hm : ρ * (xh + K (T - (k + 1)) * (y - xh)) = ρ * xh + ρ * K (T - (k + 1)) * (y - xh) := by
      ring
    simp only [hm_gVf, hm_gV, hm, ih]

end Miao.PartialInformation
