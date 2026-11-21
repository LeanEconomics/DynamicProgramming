/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSovereignDefault.UniqueEquilibrium

/-!
# The limit of the finite-horizon game

AKMM, Appendix 24.A.1, pp. 899 and 901: the computation starts from "the solution in the final
period of a finite horizon model", `V₀^R(B, Y) = u(Y − δB)`, `V₀^D(Y) = u(Y − φ(Y))`,
`q₀(B′, Y) = 0`, `B̂₀(B, Y) = 0` and `D̂₀ = 1` iff `V₀^D > V₀^R` ("In the last period of the
finite horizon game, the sovereign has no access to credit markets and consumes all available
resources"), and "By using as initial guesses the equilibrium functions in the last period (T)
of a finite-horizon economy, we are finding the equilibrium that is the limit of the finite
horizon game as `T → ∞`." Beyond the text we prove this in the continuous-debt one-period
setting of `UniqueEquilibrium` (departure D10: `δ = 1`, `ψ = 0`, `B′ ≤ B̄` with saving).

* **The finite-horizon game** (`IsFHEqm`): stage `n` is the period with `n` periods left; stage
  `0` is the book's terminal period, stage `n + 1` solves (24.9)–(24.12) with the stage-`n`
  objects as continuation. The objects of stage `n` do not depend on the horizon `T ≥ n`, so
  the `T`-period game's equilibrium is the first `T + 1` stages of one sequence.
* **Uniqueness** by backward induction (`fh_unique`; no hypothesis on `u` is needed, and no
  replication argument: each stage is determined by the next).
* **Existence** (`fh_exists`, for `u` nondecreasing, uniformly continuous and satiated,
  `φ ≥ 0`): each stage's repayment set is a closed down-set, so prices come from debt
  capacities, the objective is upper semicontinuous in `B′`, and satiation bounds savings
  (`fh_attain`).
* **Convergence as `T → ∞`** to the unique Markov perfect equilibrium. With `ψ = 0` the
  default value is exogenous, and the comparison is on `V^R − V^D`. The finite-horizon
  differences never exceed the equilibrium one (`fh_upper`); conversely the equilibrium
  difference is bounded by the finite-horizon one after a debt reduction `g_n` plus an error
  `e_n = βⁿe₀` (`fh_lower`). A slope condition on `u` below the consumption the sovereign can
  reach turns the error into a further debt reduction `e_n/κ`, so the shift obeys
  `g_{n+1} = (g_n + e_n/κ)/(1 + r)`, a contraction of modulus `1/(1 + r)` moving with `n`.
  The general lemma (`fh_moving_contraction`): if `Φ` is a contraction and `Φ_n → Φ`
  uniformly, the iterates `x_{n+1} = Φ_n(x_n)` converge to the fixed point of `Φ`. So
  `g_n → 0`, and:
  - default sets converge (`fh_default_sets`): the sovereign defaults more with a finite
    horizon, and repays the equilibrium's repaid debts after a reduction `x_n → 0`;
  - debt capacities converge (`fh_capacity_tendsto`);
  - values `V`, `V^R`, `V^D` converge uniformly (`fh_values_tendsto`);
  - prices and default rules converge at every debt where the equilibrium default rule is
    locally constant to the right (`fh_price_tendsto`), i.e. everywhere except at the
    capacities, where the finite-horizon prices stay below (`q_{n+1} ≤ q`); and
    `q(B′ + x_n) ≤ q_{n+1}(B′)`.
* The concrete economy `ue_example` meets every hypothesis (`fh_example_limit`).

The slope condition (`κ(c′ − c) ≤ u(c′) − u(c)` for `c ≤ c′ ≤ c̄` with
`Y + B̄/(1 + r) ≤ c̄`) is beyond the book; it holds for `u = min(c, c̄)`.
-/

namespace AKMM.SovereignDefault

open Finset Filter Topology SargentStachurski.RecursiveDecisionProcesses

/-- **A perturbed linear recursion converges**: if `0 ≤ dₙ`, `d_{n+1} ≤ ρ dₙ + εₙ` with
`0 ≤ ρ < 1` and `εₙ → 0`, then `dₙ → 0`. -/
theorem fh_scalar {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {d ε : ℕ → ℝ} (hd0 : ∀ n, 0 ≤ d n)
    (hrec : ∀ n, d (n + 1) ≤ ρ * d n + ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have h1ρ : 0 < 1 - ρ := by linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hε.eventually (Iio_mem_nhds
    (by positivity : (0 : ℝ) < η * (1 - ρ) / 2)))
  have hk : ∀ k, d (N₁ + k) ≤ ρ ^ k * d N₁ + η / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have h2 := hrec (N₁ + k)
      have h3 : ε (N₁ + k) < η * (1 - ρ) / 2 := hN₁ (N₁ + k) (by omega)
      rw [show N₁ + (k + 1) = N₁ + k + 1 by ring, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left ih hρ0]
  have ht : Tendsto (fun k : ℕ => ρ ^ k * d N₁) atTop (𝓝 (0 * d N₁)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _
  rw [zero_mul] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ht.eventually (Iio_mem_nhds (half_pos hη)))
  refine ⟨N₁ + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N₁ + k := ⟨n - N₁, by omega⟩
  have h1 := hk k
  have h2 : ρ ^ k * d N₁ < η / 2 := hK k (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 _)]
  linarith

/-- **A contraction with a moving map** (the joint argument for the finite-horizon limit): let
`Φ` be a contraction of modulus `ρ < 1` with fixed point `x⋆`, and `Φₙ → Φ` uniformly,
`dist (Φₙ x) (Φ x) ≤ εₙ → 0`. Then the iterates `x_{n+1} = Φₙ(xₙ)` converge to `x⋆`. -/
theorem fh_moving_contraction {X : Type*} [MetricSpace X] (Φ : X → X) (Φs : ℕ → X → X)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ ρ * dist x y)
    {xs : X} (hfix : Φ xs = xs) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hunif : ∀ n x, dist (Φs n x) (Φ x) ≤ ε n) {x : ℕ → X} (hx : ∀ n, x (n + 1) = Φs n (x n)) :
    Tendsto x atTop (𝓝 xs) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine fh_scalar hρ0 hρ1 (fun n => dist_nonneg) (fun n => ?_) hε
  calc dist (x (n + 1)) xs = dist (Φs n (x n)) (Φ xs) := by rw [hx, hfix]
    _ ≤ dist (Φs n (x n)) (Φ (x n)) + dist (Φ (x n)) (Φ xs) := dist_triangle _ _ _
    _ ≤ ε n + ρ * dist (x n) xs := add_le_add (hunif n _) (hΦ _ _)
    _ = ρ * dist (x n) xs + ε n := by ring

/-- The repayment indicator `1{a < c}` is `0` exactly when `c ≤ a`. -/
theorem fh_ite_zero (a c : ℝ) : (if a < c then (1 : ℝ) else 0) = 0 ↔ c ≤ a := by
  by_cases h : a < c
  · simp only [h, ↓reduceIte, one_ne_zero, false_iff, not_le]
  · simp only [h, ↓reduceIte, true_iff]
    exact not_lt.1 h

/-- The indicator `1{a < c}` lies in `[0, 1]`. -/
theorem fh_ite_mem (a c : ℝ) :
    0 ≤ 1 - (if a < c then (1 : ℝ) else 0) ∧ 1 - (if a < c then (1 : ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

/-- Revenue is bounded by `B̄/(1 + r)` when the price lies in `[0, (1 + r)⁻¹]`. -/
theorem fh_rev_le {p b' bmax s : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (hp1 : p ≤ s) (hb : b' ≤ bmax)
    (hbm : 0 ≤ bmax) : p * b' ≤ bmax * s := by
  rcases le_total 0 b' with h | h
  · nlinarith
  · nlinarith

variable {Y : Type*} [Fintype Y]

variable (M : UEModel Y) (T : ℕ) (V VR : ℕ → ℝ → Y → ℝ) (VD : ℕ → Y → ℝ)
  (D Bh q : ℕ → ℝ → Y → ℝ) in
/-- **The finite-horizon game** (AKMM, App. 24.A.1, p. 899; with one-period debt `δ = 1`,
`ψ = 0` and a continuum of debt levels `B′ ≤ B̄`, departure D10). Stage `n` has `n` periods
left; the game of horizon `T` has stages `0, …, T`. Stage `0` is the book's last period:
`V₀^R(B, Y) = u(Y − B)`, `V₀^D(Y) = u(Y − φ(Y))`, `q₀ = 0`, `B̂₀ = 0`. Stage `n + 1` satisfies
(24.9)–(24.12) with the stage-`n` objects as continuation: `V^D_{n+1} = u(Y − φ) + βE V^D_n`,
`q_{n+1}(B′, Y) = (1 + r)⁻¹ E[1 − D̂_n(B′, Y′)]`, and `V^R_{n+1}` the maximum of
`u(Y − B + q_{n+1}(B′, Y)B′) + βE V_n(B′, Y′)` over `B′ ≤ B̄`, attained by `B̂_{n+1}`. At every
stage `V_n = max(V^D_n, V^R_n)` and `D̂_n` is optimal (ties repaid). -/
structure IsFHEqm : Prop where
  /-- (24.9) at every stage. -/
  eq_24_9 : ∀ n ≤ T, ∀ b y, V n b y = max (VD n y) (VR n b y)
  /-- The default rule is optimal at every stage (ties repaid). -/
  default_opt : ∀ n ≤ T, ∀ b y, D n b y = if VR n b y < VD n y then 1 else 0
  /-- The last period: `V₀^D(Y) = u(Y − φ(Y))`. -/
  term_VD : ∀ y, VD 0 y = M.u (M.inc y - M.φ (M.inc y))
  /-- The last period: `V₀^R(B, Y) = u(Y − B)`. -/
  term_VR : ∀ b y, VR 0 b y = M.u (M.inc y - b)
  /-- The last period: `q₀ = 0`. -/
  term_q : ∀ b' y, q 0 b' y = 0
  /-- The last period: `B̂₀ = 0`. -/
  term_B : ∀ b y, Bh 0 b y = 0
  /-- (24.10) at `ψ = 0`, stage `n + 1`. -/
  eq_24_10 : ∀ n < T, ∀ y, VD (n + 1) y = M.defaultRHS (VD n) y
  /-- (24.11), stage `n + 1`: `V^R_{n+1}` bounds the objective ... -/
  eq_24_11 : ∀ n < T, ∀ b y b', b' ≤ M.bmax → M.obj (q (n + 1)) (V n) b y b' ≤ VR (n + 1) b y
  /-- (24.12) at `δ = 1`, stage `n + 1`. -/
  eq_24_12 : ∀ n < T, ∀ b' y, b' ≤ M.bmax →
    q (n + 1) b' y = (1 + M.r)⁻¹ * ∑ j, M.P y j * (1 - D n b' j)
  /-- The borrowing rule is feasible. -/
  borrow_le : ∀ n < T, ∀ b y, Bh (n + 1) b y ≤ M.bmax
  /-- ... and attains the maximum in (24.11). -/
  borrow_opt : ∀ n < T, ∀ b y, M.obj (q (n + 1)) (V n) b y (Bh (n + 1) b y) = VR (n + 1) b y

namespace UEModel

variable (M : UEModel Y)

/-- The objective depends on the price only at the chosen debt. -/
theorem fh_obj_congr {q₁ q₂ V : ℝ → Y → ℝ} {b : ℝ} {y : Y} {b' : ℝ} (h : q₁ b' y = q₂ b' y) :
    M.obj q₁ V b y b' = M.obj q₂ V b y b' := by
  unfold obj
  rw [h]

/-- **Uniqueness of the finite-horizon equilibrium** (backward induction): two equilibria of
the game of horizon `T` have the same values, default rules and prices at every stage. -/
theorem fh_unique {T : ℕ} {V₁ VR₁ D₁ Bh₁ q₁ V₂ VR₂ D₂ Bh₂ q₂ : ℕ → ℝ → Y → ℝ}
    {VD₁ VD₂ : ℕ → Y → ℝ} (h₁ : IsFHEqm M T V₁ VR₁ VD₁ D₁ Bh₁ q₁)
    (h₂ : IsFHEqm M T V₂ VR₂ VD₂ D₂ Bh₂ q₂) :
    ∀ n ≤ T, V₁ n = V₂ n ∧ VR₁ n = VR₂ n ∧ VD₁ n = VD₂ n ∧ D₁ n = D₂ n ∧
      ∀ b' y, b' ≤ M.bmax → q₁ n b' y = q₂ n b' y := by
  intro n
  induction n with
  | zero =>
    intro hT
    have hVD : VD₁ 0 = VD₂ 0 := funext fun y => by rw [h₁.term_VD, h₂.term_VD]
    have hVR : VR₁ 0 = VR₂ 0 := funext fun b => funext fun y => by rw [h₁.term_VR, h₂.term_VR]
    refine ⟨funext fun b => funext fun y => by
        rw [h₁.eq_24_9 0 hT, h₂.eq_24_9 0 hT, hVD, hVR], hVR, hVD,
      funext fun b => funext fun y => by rw [h₁.default_opt 0 hT, h₂.default_opt 0 hT, hVD, hVR],
      fun b' y _ => by rw [h₁.term_q, h₂.term_q]⟩
  | succ n ih =>
    intro hT
    have hnT : n < T := hT
    obtain ⟨hV, _, hVDn, hD, _⟩ := ih hnT.le
    have hVD : VD₁ (n + 1) = VD₂ (n + 1) := funext fun y => by
      rw [h₁.eq_24_10 n hnT, h₂.eq_24_10 n hnT, hVDn]
    have hq : ∀ b' y, b' ≤ M.bmax → q₁ (n + 1) b' y = q₂ (n + 1) b' y := fun b' y hb' => by
      rw [h₁.eq_24_12 n hnT b' y hb', h₂.eq_24_12 n hnT b' y hb', hD]
    have hVR : VR₁ (n + 1) = VR₂ (n + 1) := funext fun b => funext fun y => le_antisymm (by
        rw [← h₁.borrow_opt n hnT b y, M.fh_obj_congr (hq _ y (h₁.borrow_le n hnT b y)), hV]
        exact h₂.eq_24_11 n hnT b y _ (h₁.borrow_le n hnT b y)) (by
        rw [← h₂.borrow_opt n hnT b y, ← M.fh_obj_congr (hq _ y (h₂.borrow_le n hnT b y)), ← hV]
        exact h₁.eq_24_11 n hnT b y _ (h₂.borrow_le n hnT b y))
    refine ⟨funext fun b => funext fun y => by
        rw [h₁.eq_24_9 _ hT, h₂.eq_24_9 _ hT, hVD, hVR], hVR, hVD,
      funext fun b => funext fun y => by rw [h₁.default_opt _ hT, h₂.default_opt _ hT, hVD, hVR],
      hq⟩

/-- In a finite-horizon equilibrium the price lies in `[0, (1 + r)⁻¹]`. -/
theorem fh_q_mem {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ}
    (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n < T) {b' : ℝ} (hb' : b' ≤ M.bmax)
    (y : Y) : 0 ≤ q (n + 1) b' y ∧ q (n + 1) b' y ≤ (1 + M.r)⁻¹ := by
  rw [h.eq_24_12 n hn b' y hb']
  exact M.ue_price_mem (a := fun b j => 1 - D n b j) (fun j => by
    rw [h.default_opt n hn.le]; exact fh_ite_mem _ _) y

/-- In a Markov perfect equilibrium the price lies in `[0, (1 + r)⁻¹]`. -/
theorem fh_mpe_q_mem {V VR D Bh q : ℝ → Y → ℝ} {VD : Y → ℝ} (h : IsOneMPE M V VR VD D Bh q)
    {b' : ℝ} (hb' : b' ≤ M.bmax) (y : Y) : 0 ≤ q b' y ∧ q b' y ≤ (1 + M.r)⁻¹ := by
  rw [h.eq_24_12 b' y hb']
  exact M.ue_price_mem (a := fun b j => 1 - D b j) (fun j => by
    rw [h.default_opt]; exact fh_ite_mem _ _) y

/-- At every stage of the finite-horizon game debt `B ≤ 0` is repaid. -/
theorem fh_repay_nonpos (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {T : ℕ}
    {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ}
    (hn : n ≤ T) {b : ℝ} (hb : b ≤ 0) (y : Y) : VD n y ≤ VR n b y := by
  cases n with
  | zero => rw [h.term_VD, h.term_VR]; exact hu (by linarith [hφ y])
  | succ n =>
    have hnT : n < T := hn
    have h1 := h.eq_24_11 n hnT b y 0 M.bmax_nonneg
    have h2 : M.u (M.inc y - M.φ (M.inc y)) ≤ M.u (M.inc y - b + q (n + 1) 0 y * 0) :=
      hu (by linarith [hφ y])
    have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun j =>
      (by rw [h.eq_24_9 n hnT.le]; exact le_max_left _ _ : VD n j ≤ V n 0 j)) y) M.β_nonneg
    rw [h.eq_24_10 n hnT]
    unfold obj at h1
    unfold defaultRHS
    linarith

/-- At every stage the repayment value is nonincreasing in debt. -/
theorem fh_VR_antitone (hu : Monotone M.u) {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n ≤ T) {b b'' : ℝ}
    (hbb : b ≤ b'') (y : Y) : VR n b'' y ≤ VR n b y := by
  cases n with
  | zero => rw [h.term_VR, h.term_VR]; exact hu (by linarith)
  | succ n =>
    have hnT : n < T := hn
    exact M.ue_VR_antitone hu (fun b y ε hε => ⟨Bh (n + 1) b y, h.borrow_le n hnT b y, by
      rw [h.borrow_opt n hnT b y]; linarith⟩) (h.eq_24_11 n hnT) hbb y

/-- **A modulus uniform in the stage**: if `|c − c′| < η` implies `|u(c) − u(c′)| < ε`, then at
every stage reducing debt by `h < η` raises `V^R` by less than `ε`. -/
theorem fh_VR_mod {ε η : ℝ} (hη : ∀ c c' : ℝ, dist c c' < η → dist (M.u c) (M.u c') < ε)
    {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q)
    {n : ℕ} (hn : n ≤ T) {b h' : ℝ} (h0 : 0 ≤ h') (hlt : h' < η) (y : Y) :
    VR n (b - h') y ≤ VR n b y + ε := by
  have hd : ∀ c : ℝ, dist (c + h') c < η := fun c => by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg h0]; exact hlt
  cases n with
  | zero =>
    rw [h.term_VR, h.term_VR]
    have h1 := hη _ _ (hd (M.inc y - b))
    rw [Real.dist_eq] at h1
    rw [show M.inc y - (b - h') = M.inc y - b + h' by ring]
    linarith [(abs_lt.1 h1).2]
  | succ n =>
    have hnT : n < T := hn
    set bh := Bh (n + 1) (b - h') y
    rw [← h.borrow_opt n hnT (b - h') y]
    have h2 := h.eq_24_11 n hnT b y bh (h.borrow_le n hnT _ y)
    have h1 := hη _ _ (hd (M.inc y - b + q (n + 1) bh y * bh))
    rw [Real.dist_eq] at h1
    unfold obj at h2 ⊢
    rw [show M.inc y - (b - h') + q (n + 1) bh y * bh =
      M.inc y - b + q (n + 1) bh y * bh + h' by ring]
    linarith [(abs_lt.1 h1).2]

/-- **The slope of the repayment value**: if `κ(c′ − c) ≤ u(c′) − u(c)` for `c ≤ c′ ≤ c̄` and
`Y + B̄/(1 + r) ≤ c̄` (consumption under repayment with debt `B ≥ 0` never exceeds `c̄`), then at
every stage reducing a debt `B` by `h ≤ B` raises `V^R` by at least `κh`. -/
theorem fh_VR_slope {κ cbar : ℝ}
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n ≤ T) {b h' : ℝ}
    (h0 : 0 ≤ h') (hbh : 0 ≤ b - h') (y : Y) : VR n b y + κ * h' ≤ VR n (b - h') y := by
  have hs : 0 ≤ M.bmax * (1 + M.r)⁻¹ :=
    mul_nonneg M.bmax_nonneg (inv_nonneg.2 (by linarith [M.r_pos]))
  cases n with
  | zero =>
    rw [h.term_VR, h.term_VR]
    have h1 := hslope (M.inc y - b) (M.inc y - (b - h')) (by linarith) (by linarith [hcap y])
    rw [show M.inc y - (b - h') - (M.inc y - b) = h' by ring] at h1
    linarith
  | succ n =>
    have hnT : n < T := hn
    set bh := Bh (n + 1) b y
    have hbh' : bh ≤ M.bmax := h.borrow_le n hnT b y
    rw [← h.borrow_opt n hnT b y]
    have h2 := h.eq_24_11 n hnT (b - h') y bh hbh'
    have hq := M.fh_q_mem h hnT hbh' y
    have hrev := fh_rev_le (inv_nonneg.2 (by linarith [M.r_pos])) hq.1 hq.2 hbh' M.bmax_nonneg
    have h1 := hslope (M.inc y - b + q (n + 1) bh y * bh) (M.inc y - (b - h') +
      q (n + 1) bh y * bh) (by linarith) (by linarith [hcap y])
    rw [show M.inc y - (b - h') + q (n + 1) bh y * bh - (M.inc y - b + q (n + 1) bh y * bh) = h'
      by ring] at h1
    unfold obj at h2 ⊢
    linarith

/-- **The one-step comparison** (replication with an error): if repayment under `a₁` implies
repayment under `a₂` after a debt reduction `x`, and the continuation differences
`W − W^D` satisfy `W₁(B′) − W₁^D ≤ W₂(B′ − x) − W₂^D + e`, then issuing `B̂ − x` at the second
prices with debt `B − x/(1 + r)` does as well as issuing `B̂` at the first with debt `B`, up to
`βe` and the difference of the continuation default values. -/
theorem fh_compare (hu : Monotone M.u) {q₁ q₂ a₁ a₂ W₁ W₂ : ℝ → Y → ℝ} {WD₁ WD₂ : Y → ℝ}
    {x e : ℝ} (hx : 0 ≤ x) (hq₁ : ∀ b' y, b' ≤ M.bmax → q₁ b' y = M.price a₁ b' y)
    (hq₂ : ∀ b' y, b' ≤ M.bmax → q₂ b' y = M.price a₂ b' y)
    (ha₁ : ∀ b' j, 0 ≤ a₁ b' j ∧ a₁ b' j ≤ 1) (hneg₁ : ∀ b' j, b' ≤ 0 → a₁ b' j = 1)
    (hneg₂ : ∀ b' j, b' ≤ 0 → a₂ b' j = 1)
    (hdom : ∀ b' j, b' ≤ M.bmax → a₁ b' j ≤ a₂ (b' - x) j)
    (hW : ∀ b' j, W₁ b' j - WD₁ j ≤ W₂ (b' - x) j - WD₂ j + e) {b bh : ℝ} (y : Y)
    (hbh : bh ≤ M.bmax) :
    M.obj q₁ W₁ b y bh - M.β * ∑ j, M.P y j * WD₁ j ≤
      M.obj q₂ W₂ (b - x * (1 + M.r)⁻¹) y (bh - x) - M.β * ∑ j, M.P y j * WD₂ j +
        M.β * e := by
  have hrev := M.ue_revenue hx hq₁ hq₂ ha₁ hneg₁ hneg₂ hdom hbh y
  have hU := hu (show M.inc y - b + q₁ bh y * bh ≤
    M.inc y - (b - x * (1 + M.r)⁻¹) + q₂ (bh - x) y * (bh - x) by linarith)
  have hs : ∑ j, M.P y j * W₁ bh j - ∑ j, M.P y j * WD₁ j ≤
      ∑ j, M.P y j * W₂ (bh - x) j - ∑ j, M.P y j * WD₂ j + e := by
    have h1 := ue_sum_mono M.markov (fun j => hW bh j) y
    have h2 := ue_sum_add M.markov (fun j => W₂ (bh - x) j - WD₂ j) e y
    simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib] at h1 h2
    linarith
  have hs2 := mul_le_mul_of_nonneg_left hs M.β_nonneg
  unfold obj
  nlinarith [hs2]

/-- **The finite horizon never repays more than the equilibrium**: at every stage
`V^R_n − V^D_n ≤ V^R − V^D`. -/
theorem fh_upper (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y))
    {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q)
    {Vs VRs Ds Bhs qs : ℝ → Y → ℝ} {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∀ n b y, VR n b y - VD n y ≤ VRs b y - VDs y := by
  intro n
  induction n with
  | zero =>
    intro b y
    have h0 := hfh 0
    rw [h0.term_VR, h0.term_VD]
    have h1 := hs.eq_24_11 b y 0 M.bmax_nonneg
    have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun j =>
      (by rw [hs.eq_24_9]; exact le_max_left _ _ : VDs j ≤ Vs 0 j)) y) M.β_nonneg
    have h4 := hs.eq_24_10 y
    unfold obj at h1
    unfold defaultRHS at h4
    simp only [mul_zero, add_zero] at h1
    linarith
  | succ n ih =>
    intro b y
    have h := hfh (n + 1)
    have hn : n < n + 1 := Nat.lt_succ_self n
    have hdom : ∀ b' j, b' ≤ M.bmax → 1 - D n b' j ≤ 1 - Ds (b' - 0) j := by
      intro b' j _
      rw [sub_zero, h.default_opt n hn.le, hs.default_opt]
      have := ih b' j
      split_ifs <;> first | (norm_num; done) | (exfalso; linarith)
    have hW : ∀ b' j, V n b' j - VD n j ≤ Vs (b' - 0) j - VDs j + 0 := by
      intro b' j
      rw [sub_zero, add_zero, h.eq_24_9 n hn.le, hs.eq_24_9]
      have := ih b' j
      rcases le_total (VD n j) (VR n b' j) with h1 | h1
      · rw [max_eq_right h1]; linarith [le_max_right (VDs j) (VRs b' j)]
      · rw [max_eq_left h1]; linarith [le_max_left (VDs j) (VRs b' j)]
    have hneg₁ : ∀ b' j, b' ≤ 0 → 1 - D n b' j = 1 := fun b' j hb => by
      rw [h.default_opt n hn.le, (fh_ite_zero _ _).2 (M.fh_repay_nonpos hu hφ h hn.le hb j),
        sub_zero]
    have hneg₂ : ∀ b' j, b' ≤ 0 → 1 - Ds b' j = 1 := fun b' j hb => by
      rw [hs.default_opt, (fh_ite_zero _ _).2 (M.ue_repay_nonpos hu hφ hs.eq_24_11
        (fun b y => by rw [hs.eq_24_9]; exact le_max_left _ _) hs.eq_24_10 hb j), sub_zero]
    have hc := M.fh_compare hu le_rfl (q₁ := q (n + 1)) (q₂ := qs)
      (a₁ := fun b j => 1 - D n b j) (a₂ := fun b j => 1 - Ds b j) (W₁ := V n) (W₂ := Vs)
      (WD₁ := VD n) (WD₂ := VDs) (e := 0) (b := b)
      (fun b' y hb' => h.eq_24_12 n hn b' y hb') (fun b' y hb' => hs.eq_24_12 b' y hb')
      (fun b' j => by rw [h.default_opt n hn.le]; exact fh_ite_mem _ _) hneg₁ hneg₂ hdom hW y
      (h.borrow_le n hn b y)
    rw [h.borrow_opt n hn b y] at hc
    simp only [zero_mul, sub_zero, mul_zero, add_zero] at hc
    have h2 := hs.eq_24_11 b y (Bh (n + 1) b y) (h.borrow_le n hn b y)
    rw [h.eq_24_10 n hn, hs.eq_24_10 y]
    unfold defaultRHS
    linarith

/-- The debt-reduction sequence of the lower bound: `g₀ = B̄/(1 + r)` and
`g_{n+1} = (gₙ + βⁿe₀/κ)/(1 + r)`. -/
noncomputable def fhShift (e₀ κ : ℝ) : ℕ → ℝ
  | 0 => M.bmax * (1 + M.r)⁻¹
  | n + 1 => (fhShift e₀ κ n + M.β ^ n * e₀ / κ) * (1 + M.r)⁻¹

/-- The debt reductions are nonnegative. -/
theorem fh_shift_nonneg {e₀ κ : ℝ} (he₀ : 0 ≤ e₀) (hκ : 0 < κ) (n : ℕ) :
    0 ≤ M.fhShift e₀ κ n := by
  have hρ : 0 ≤ (1 + M.r)⁻¹ := inv_nonneg.2 (by linarith [M.r_pos])
  induction n with
  | zero => exact mul_nonneg M.bmax_nonneg hρ
  | succ n ih =>
    exact mul_nonneg (add_nonneg ih (div_nonneg (mul_nonneg (pow_nonneg M.β_nonneg n) he₀)
      hκ.le)) hρ

/-- **The debt reductions vanish**: `g_{n+1} = Φₙ(gₙ)` with `Φₙ(g) = (g + βⁿe₀/κ)/(1 + r)`,
which converges uniformly to the contraction `Φ(g) = g/(1 + r)` with fixed point `0`
(`fh_moving_contraction`). -/
theorem fh_shift_tendsto (e₀ κ : ℝ) : Tendsto (M.fhShift e₀ κ) atTop (𝓝 0) := by
  set ρ := (1 + M.r)⁻¹ with hρdef
  have hρ0 : 0 ≤ ρ := inv_nonneg.2 (by linarith [M.r_pos])
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by linarith [M.r_pos])
  have hε : Tendsto (fun n : ℕ => |ρ * (M.β ^ n * e₀ / κ)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ρ * (M.β ^ n * e₀ / κ)) atTop (𝓝 (ρ * (0 * e₀ / κ))) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one).mul_const e₀).div_const
        κ).const_mul ρ
    rw [zero_mul, zero_div, mul_zero] at h1
    simpa using h1.abs
  refine fh_moving_contraction (fun z => ρ * z) (fun n z => ρ * z + ρ * (M.β ^ n * e₀ / κ))
    hρ0 hρ1 (fun a c => ?_) (mul_zero ρ) hε (fun n z => ?_) (fun n => ?_)
  · rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hρ0]
  · rw [Real.dist_eq, add_sub_cancel_left]
  · change (M.fhShift e₀ κ n + M.β ^ n * e₀ / κ) * ρ = _
    ring

/-- **The base of the lower bound**: with `V ≤ K` in the equilibrium,
`V^R − V^D ≤ V^R_0(B − B̄/(1 + r)) − V^D_0 + β(|K| + ‖V^D‖)`. -/
theorem fh_base (hu : Monotone M.u) {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ}
    (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ} {VDs : Y → ℝ}
    (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ e₀, 0 ≤ e₀ ∧ ∀ b y, VRs b y - VDs y ≤
      VR 0 (b - M.bmax * (1 + M.r)⁻¹) y - VD 0 y + e₀ := by
  obtain ⟨K, hK⟩ := hs.bdd
  refine ⟨M.β * (|K| + ‖VDs‖), mul_nonneg M.β_nonneg (add_nonneg (abs_nonneg K)
    (norm_nonneg _)), fun b y => ?_⟩
  have h0 := hfh 0
  rw [h0.term_VR, h0.term_VD, ← hs.borrow_opt b y]
  set bh := Bhs b y
  have hbh : bh ≤ M.bmax := hs.borrow_le b y
  have hq := M.fh_mpe_q_mem hs hbh y
  have hrev := fh_rev_le (inv_nonneg.2 (by linarith [M.r_pos])) hq.1 hq.2 hbh M.bmax_nonneg
  have hU := hu (show M.inc y - b + qs bh y * bh ≤ M.inc y - (b - M.bmax * (1 + M.r)⁻¹) by
    linarith)
  have hS := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun j => hK bh j) y) M.β_nonneg
  have hlow : -‖VDs‖ ≤ ∑ j, M.P y j * VDs j := ue_le_sum M.markov (fun j => by
    have h1 := norm_le_pi_norm VDs j
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (VDs j)]) y
  have hS2 := mul_le_mul_of_nonneg_left hlow M.β_nonneg
  have hKa := mul_le_mul_of_nonneg_left (le_abs_self K) M.β_nonneg
  rw [hs.eq_24_10 y]
  unfold obj defaultRHS
  nlinarith

/-- **The domination step** (an error turned into a debt reduction): if
`V^R − V^D ≤ V^R_n(B − g) − V^D_n + e` everywhere, then every debt the equilibrium repays is
repaid at stage `n` after the reduction `g + e/κ` (by the slope `fh_VR_slope`, or because debt
`≤ 0` is always repaid). -/
theorem fh_dom (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ} (hκ : 0 < κ)
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {T : ℕ} {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (h : IsFHEqm M T V VR VD D Bh q) {n : ℕ} (hn : n ≤ T)
    {VRs : ℝ → Y → ℝ} {VDs : Y → ℝ} {g e : ℝ} (he : 0 ≤ e)
    (hL : ∀ b y, VRs b y - VDs y ≤ VR n (b - g) y - VD n y + e) {b : ℝ} {j : Y}
    (hb : VDs j ≤ VRs b j) : VD n j ≤ VR n (b - (g + e / κ)) j := by
  rcases lt_or_ge (b - (g + e / κ)) 0 with hneg | hpos
  · exact M.fh_repay_nonpos hu hφ h hn hneg.le j
  · have h1 := hL b j
    have h2 := M.fh_VR_slope hslope hcap h hn (b := b - g) (h' := e / κ) (div_nonneg he hκ.le)
      (by linarith) j
    rw [show κ * (e / κ) = e by field_simp, show b - g - e / κ = b - (g + e / κ) by ring] at h2
    linarith

/-- **The lower bound**: at every stage
`V^R − V^D ≤ V^R_n(B − gₙ) − V^D_n + βⁿe₀`, with the debt reductions `gₙ = fhShift e₀ κ n`. The
induction step is the one-step comparison (`fh_compare`) with the domination of `fh_dom`. -/
theorem fh_lower (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ} (hκ : 0 < κ)
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) {e₀ : ℝ} (he₀ : 0 ≤ e₀)
    (hbase : ∀ b y, VRs b y - VDs y ≤ VR 0 (b - M.bmax * (1 + M.r)⁻¹) y - VD 0 y + e₀) :
    ∀ n b y, VRs b y - VDs y ≤ VR n (b - M.fhShift e₀ κ n) y - VD n y + M.β ^ n * e₀ := by
  intro n
  induction n with
  | zero => intro b y; rw [pow_zero, one_mul]; exact hbase b y
  | succ n ih =>
    intro b y
    have h := hfh (n + 1)
    have hn : n < n + 1 := Nat.lt_succ_self n
    set g := M.fhShift e₀ κ n with hgdef
    set e := M.β ^ n * e₀ with hedef
    have hg : 0 ≤ g := M.fh_shift_nonneg he₀ hκ n
    have he : 0 ≤ e := mul_nonneg (pow_nonneg M.β_nonneg n) he₀
    set x := g + e / κ with hxdef
    have hx : 0 ≤ x := add_nonneg hg (div_nonneg he hκ.le)
    have hdom : ∀ b' j, b' ≤ M.bmax → 1 - Ds b' j ≤ 1 - D n (b' - x) j := by
      intro b' j _
      rw [hs.default_opt, h.default_opt n hn.le]
      by_cases hd : VRs b' j < VDs j
      · simp only [hd, ↓reduceIte, sub_self]
        exact (fh_ite_mem _ _).1
      · rw [(fh_ite_zero _ _).2 (not_lt.1 hd),
          (fh_ite_zero _ _).2 (M.fh_dom hu hφ hκ hslope hcap h hn.le he ih (not_lt.1 hd))]
    have hW : ∀ b' j, Vs b' j - VDs j ≤ V n (b' - x) j - VD n j + e := by
      intro b' j
      rw [hs.eq_24_9, h.eq_24_9 n hn.le]
      have h1 := ih b' j
      have h2 := M.fh_VR_antitone hu h hn.le (show b' - x ≤ b' - g by
        linarith [div_nonneg he hκ.le]) j
      have h3 := le_max_left (VD n j) (VR n (b' - x) j)
      have h4 := le_max_right (VD n j) (VR n (b' - x) j)
      rcases le_total (VDs j) (VRs b' j) with h5 | h5
      · rw [max_eq_right h5]; linarith
      · rw [max_eq_left h5]; linarith
    have hneg₁ : ∀ b' j, b' ≤ 0 → 1 - Ds b' j = 1 := fun b' j hb => by
      rw [hs.default_opt, (fh_ite_zero _ _).2 (M.ue_repay_nonpos hu hφ hs.eq_24_11
        (fun b y => by rw [hs.eq_24_9]; exact le_max_left _ _) hs.eq_24_10 hb j), sub_zero]
    have hneg₂ : ∀ b' j, b' ≤ 0 → 1 - D n b' j = 1 := fun b' j hb => by
      rw [h.default_opt n hn.le, (fh_ite_zero _ _).2 (M.fh_repay_nonpos hu hφ h hn.le hb j),
        sub_zero]
    have hc := M.fh_compare hu hx (q₁ := qs) (q₂ := q (n + 1))
      (a₁ := fun b j => 1 - Ds b j) (a₂ := fun b j => 1 - D n b j) (W₁ := Vs) (W₂ := V n)
      (WD₁ := VDs) (WD₂ := VD n) (e := e) (b := b)
      (fun b' y hb' => hs.eq_24_12 b' y hb') (fun b' y hb' => h.eq_24_12 n hn b' y hb')
      (fun b' j => by rw [hs.default_opt]; exact fh_ite_mem _ _) hneg₁ hneg₂ hdom hW y
      (hs.borrow_le b y)
    rw [hs.borrow_opt b y] at hc
    have h2 := h.eq_24_11 n hn (b - x * (1 + M.r)⁻¹) y (Bhs b y - x)
      (by linarith [hs.borrow_le b y])
    have hsh : M.fhShift e₀ κ (n + 1) = x * (1 + M.r)⁻¹ := rfl
    rw [hsh, h.eq_24_10 n hn, hs.eq_24_10 y, pow_succ]
    unfold defaultRHS
    have : M.β ^ n * M.β * e₀ = M.β * e := by rw [hedef]; ring
    rw [this]
    linarith

/-- **The default values converge**: `|V^D_n − V^D| ≤ βⁿ‖V^D_0 − V^D‖`. -/
theorem fh_VD_bound {V VR D Bh q : ℕ → ℝ → Y → ℝ} {VD : ℕ → Y → ℝ}
    (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {VDs : Y → ℝ}
    (hVDs : ∀ y, VDs y = M.defaultRHS VDs y) :
    ∀ n y, |VD n y - VDs y| ≤ M.β ^ n * ‖fun y => VD 0 y - VDs y‖ := by
  intro n
  induction n with
  | zero =>
    intro y
    rw [pow_zero, one_mul]
    have := norm_le_pi_norm (fun y => VD 0 y - VDs y) y
    rwa [Real.norm_eq_abs] at this
  | succ n ih =>
    intro y
    have h := hfh (n + 1)
    have hd : VD (n + 1) y - VDs y = M.β * ∑ j, M.P y j * (VD n j - VDs j) := by
      rw [h.eq_24_10 n (Nat.lt_succ_self n), hVDs y]
      unfold defaultRHS
      simp only [mul_sub, sum_sub_distrib]
      ring
    have hs : |∑ j, M.P y j * (VD n j - VDs j)| ≤ M.β ^ n * ‖fun y => VD 0 y - VDs y‖ :=
      calc |∑ j, M.P y j * (VD n j - VDs j)| ≤ ∑ j, |M.P y j * (VD n j - VDs j)| :=
            abs_sum_le_sum_abs _ _
        _ = ∑ j, M.P y j * |VD n j - VDs j| := by
            refine sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (M.markov.nonneg y j)]
        _ ≤ _ := ue_sum_le M.markov ih y
    rw [hd, abs_mul, abs_of_nonneg M.β_nonneg, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hs M.β_nonneg]

/-- **The default sets converge** (AKMM, p. 901, beyond the text): with a finite horizon the
sovereign defaults at least as often (`D̂_n = 0 ⇒ D̂ = 0`), and every debt `B` the equilibrium
repays is repaid at stage `n` after a debt reduction `xₙ → 0`. -/
theorem fh_default_sets (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ}
    (hκ : 0 < κ) (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ n b y, Ds b y = 0 → D n (b - x n) y = 0) ∧ ∀ n b y, D n b y = 0 → Ds b y = 0 := by
  obtain ⟨e₀, he₀, hbase⟩ := M.fh_base hu hfh hs
  have hL := M.fh_lower hu hφ hκ hslope hcap hfh hs he₀ hbase
  have hU := M.fh_upper hu hφ hfh hs
  refine ⟨fun n => M.fhShift e₀ κ n + M.β ^ n * e₀ / κ, fun n => add_nonneg
    (M.fh_shift_nonneg he₀ hκ n) (div_nonneg (mul_nonneg (pow_nonneg M.β_nonneg n) he₀) hκ.le),
    ?_, fun n b y hb => ?_, fun n b y hb => ?_⟩
  · have h1 := (M.fh_shift_tendsto e₀ κ).add (((tendsto_pow_atTop_nhds_zero_of_lt_one
      M.β_nonneg M.β_lt_one).mul_const e₀).div_const κ)
    simpa using h1
  · have h := hfh n
    rw [hs.default_opt] at hb
    rw [h.default_opt n le_rfl]
    exact (fh_ite_zero _ _).2 (M.fh_dom hu hφ hκ hslope hcap h le_rfl
      (mul_nonneg (pow_nonneg M.β_nonneg n) he₀) (hL n) ((fh_ite_zero _ _).1 hb))
  · have h := hfh n
    rw [h.default_opt n le_rfl] at hb
    rw [hs.default_opt]
    have := hU n b y
    exact (fh_ite_zero _ _).2 (by linarith [(fh_ite_zero _ _).1 hb])

/-- The debt capacity of a repayment value: the largest debt in `[0, B̄]` that is repaid. -/
noncomputable def fhCap (VR : ℝ → Y → ℝ) (VD : Y → ℝ) (j : Y) : ℝ :=
  sSup {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD j ≤ VR b j}

/-- **The debt capacities converge** (AKMM, p. 901, beyond the text): the finite-horizon
capacity `b̄ₙ(Y)` lies in `[b̄(Y) − xₙ, b̄(Y)]` with `xₙ → 0`, so `b̄ₙ(Y) → b̄(Y)`. -/
theorem fh_capacity_tendsto (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ}
    (hκ : 0 < κ) (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ n j, M.fhCap VRs VDs j - x n ≤ M.fhCap (VR n) (VD n) j ∧
        M.fhCap (VR n) (VD n) j ≤ M.fhCap VRs VDs j) ∧
      ∀ j, Tendsto (fun n => M.fhCap (VR n) (VD n) j) atTop (𝓝 (M.fhCap VRs VDs j)) := by
  obtain ⟨x, hx0, hx, hdom, hrev⟩ := M.fh_default_sets hu hφ hκ hslope hcap hfh hs
  have hbound : ∀ n j, M.fhCap VRs VDs j - x n ≤ M.fhCap (VR n) (VD n) j ∧
      M.fhCap (VR n) (VD n) j ≤ M.fhCap VRs VDs j := by
    intro n j
    have h := hfh n
    have hzn : ∀ b, (D n b j = 0 ↔ VD n j ≤ VR n b j) := fun b => by
      rw [h.default_opt n le_rfl]; exact fh_ite_zero _ _
    have hzs : ∀ b, (Ds b j = 0 ↔ VDs j ≤ VRs b j) := fun b => by
      rw [hs.default_opt]; exact fh_ite_zero _ _
    have h0n : (0 : ℝ) ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD n j ≤ VR n b j} :=
      ⟨le_rfl, M.bmax_nonneg, M.fh_repay_nonpos hu hφ h le_rfl le_rfl j⟩
    have h0s : (0 : ℝ) ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VDs j ≤ VRs b j} :=
      ⟨le_rfl, M.bmax_nonneg, M.ue_repay_nonpos hu hφ hs.eq_24_11
        (fun b y => by rw [hs.eq_24_9]; exact le_max_left _ _) hs.eq_24_10 le_rfl j⟩
    have hbs : BddAbove {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VDs j ≤ VRs b j} :=
      ⟨M.bmax, fun b hb => hb.2.1⟩
    have hbn : BddAbove {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD n j ≤ VR n b j} :=
      ⟨M.bmax, fun b hb => hb.2.1⟩
    constructor
    · have : M.fhCap VRs VDs j ≤ M.fhCap (VR n) (VD n) j + x n := by
        unfold fhCap
        refine csSup_le ⟨0, h0s⟩ fun b hb => ?_
        rcases le_total (b - x n) 0 with h1 | h1
        · linarith [le_csSup hbn h0n]
        · have hm : b - x n ∈ {b | 0 ≤ b ∧ b ≤ M.bmax ∧ VD n j ≤ VR n b j} :=
            ⟨h1, by linarith [hb.2.1, hx0 n], (hzn _).1 (hdom n b j ((hzs b).2 hb.2.2))⟩
          linarith [le_csSup hbn hm]
      linarith
    · exact csSup_le_csSup hbs ⟨0, h0n⟩ fun b hb =>
        ⟨hb.1, hb.2.1, (hzs b).1 (hrev n b j ((hzn b).2 hb.2.2))⟩
  refine ⟨x, hx0, hx, hbound, fun j => ?_⟩
  have hl : Tendsto (fun n => M.fhCap VRs VDs j - x n) atTop (𝓝 (M.fhCap VRs VDs j - 0)) :=
    tendsto_const_nhds.sub hx
  rw [sub_zero] at hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => (hbound n j).1) (fun n => (hbound n j).2)

/-- **The values converge uniformly** (AKMM, p. 901, beyond the text): `V^D_n → V^D`,
`V^R_n → V^R` and `V_n → V` uniformly in `(B, Y)`. -/
theorem fh_values_tendsto (hu : Monotone M.u) (huc : UniformContinuous M.u)
    (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ} (hκ : 0 < κ)
    (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ b y, |VD n y - VDs y| ≤ ε ∧ |VR n b y - VRs b y| ≤ ε ∧
      |V n b y - Vs b y| ≤ ε := by
  intro ε hε
  obtain ⟨e₀, he₀, hbase⟩ := M.fh_base hu hfh hs
  have hL := M.fh_lower hu hφ hκ hslope hcap hfh hs he₀ hbase
  have hU := M.fh_upper hu hφ hfh hs
  have hB := M.fh_VD_bound hfh hs.eq_24_10
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuous_iff.1 huc (ε / 3) (by linarith)
  set C := ‖fun y => VD 0 y - VDs y‖
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one
  have t1 : ∀ᶠ n in atTop, M.fhShift e₀ κ n < η :=
    (M.fh_shift_tendsto e₀ κ).eventually (Iio_mem_nhds hη)
  have t2 : ∀ᶠ n in atTop, M.β ^ n * e₀ < ε / 3 := by
    have h1 := hpow.mul_const e₀
    rw [zero_mul] at h1
    exact h1.eventually (Iio_mem_nhds (by linarith))
  have t3 : ∀ᶠ n in atTop, M.β ^ n * C < ε / 3 := by
    have h1 := hpow.mul_const C
    rw [zero_mul] at h1
    exact h1.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((t1.and t2).and t3)
  refine ⟨N, fun n hn b y => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN n hn
  have h := hfh n
  have hVD : |VD n y - VDs y| ≤ ε / 3 := (hB n y).trans h3.le
  have hm := M.fh_VR_mod (fun c c' hc => hηu hc) h le_rfl (b := b)
    (M.fh_shift_nonneg he₀ hκ n) h1 y
  have hu1 := hU n b y
  have hl1 := hL n b y
  have hVR : |VR n b y - VRs b y| ≤ ε := by
    rw [abs_le] at hVD ⊢
    constructor <;> linarith
  refine ⟨by linarith, hVR, ?_⟩
  rw [h.eq_24_9 n le_rfl, hs.eq_24_9]
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by linarith) hVR)

/-- **The prices and default rules converge** (AKMM, p. 901, beyond the text): the
finite-horizon prices lie between `q(B′ + xₙ)` and `q(B′)` with `xₙ → 0`; wherever the
equilibrium default rule is constant on some `[B, B + η]` (everywhere except at the
capacities), the default rules and prices of the finite-horizon game are eventually those of
the equilibrium. -/
theorem fh_price_tendsto (hu : Monotone M.u) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {κ cbar : ℝ}
    (hκ : 0 < κ) (hslope : ∀ c c', c ≤ c' → c' ≤ cbar → κ * (c' - c) ≤ M.u c' - M.u c)
    (hcap : ∀ y, M.inc y + M.bmax * (1 + M.r)⁻¹ ≤ cbar) {V VR D Bh q : ℕ → ℝ → Y → ℝ}
    {VD : ℕ → Y → ℝ} (hfh : ∀ T, IsFHEqm M T V VR VD D Bh q) {Vs VRs Ds Bhs qs : ℝ → Y → ℝ}
    {VDs : Y → ℝ} (hs : IsOneMPE M Vs VRs VDs Ds Bhs qs) :
    ∃ x : ℕ → ℝ, (∀ n, 0 ≤ x n) ∧ Tendsto x atTop (𝓝 0) ∧
      (∀ n b' y, b' ≤ M.bmax → q (n + 1) b' y ≤ qs b' y) ∧
      (∀ n b' y, b' + x n ≤ M.bmax → qs (b' + x n) y ≤ q (n + 1) b' y) ∧
      ∀ b, (∃ η > 0, ∀ j, Ds (b + η) j = Ds b j) →
        ∀ᶠ n in atTop, (∀ j, D n b j = Ds b j) ∧ ∀ y, b ≤ M.bmax → q (n + 1) b y = qs b y := by
  obtain ⟨x, hx0, hx, hdom, hrev⟩ := M.fh_default_sets hu hφ hκ hslope hcap hfh hs
  have h01 : ∀ a c : ℝ, (if a < c then (1 : ℝ) else 0) = 0 ∨ (if a < c then (1 : ℝ) else 0) = 1 :=
    fun a c => by split_ifs <;> simp
  have hanti : ∀ {b b'' : ℝ}, b ≤ b'' → ∀ j, VRs b'' j ≤ VRs b j := fun hbb j =>
    M.ue_VR_antitone hu (M.ue_mpe_sup hs) hs.eq_24_11 hbb j
  have hDmono : ∀ {b b'' : ℝ}, b ≤ b'' → ∀ j, Ds b j ≤ Ds b'' j := fun hbb j => by
    rw [hs.default_opt, hs.default_opt]
    have := hanti hbb j
    split_ifs <;> first | (norm_num; done) | (exfalso; linarith)
  have hDle : ∀ n b j, Ds b j ≤ D n b j := fun n b j => by
    rcases h01 (VR n b j) (VD n j) with h | h
    · have h' : D n b j = 0 := by rw [(hfh n).default_opt n le_rfl]; exact h
      rw [h', hrev n b j h']
    · have h' : D n b j = 1 := by rw [(hfh n).default_opt n le_rfl]; exact h
      rw [h', hs.default_opt]
      linarith [(fh_ite_mem (VRs b j) (VDs j)).1]
  have hDle2 : ∀ n b j, D n b j ≤ Ds (b + x n) j := fun n b j => by
    rcases h01 (VRs (b + x n) j) (VDs j) with h | h
    · have h' : Ds (b + x n) j = 0 := by rw [hs.default_opt]; exact h
      have := hdom n (b + x n) j h'
      rw [add_sub_cancel_right] at this
      rw [this, h']
    · have h' : Ds (b + x n) j = 1 := by rw [hs.default_opt]; exact h
      rw [h', (hfh n).default_opt n le_rfl]
      linarith [(fh_ite_mem (VR n b j) (VD n j)).1]
  have hprice : ∀ n b' y, b' ≤ M.bmax → q (n + 1) b' y = M.price (fun b j => 1 - D n b j) b' y :=
    fun n b' y hb' => (hfh (n + 1)).eq_24_12 n (Nat.lt_succ_self n) b' y hb'
  have hprices : ∀ b' y, b' ≤ M.bmax → qs b' y = M.price (fun b j => 1 - Ds b j) b' y :=
    fun b' y hb' => hs.eq_24_12 b' y hb'
  refine ⟨x, hx0, hx, fun n b' y hb' => ?_, fun n b' y hb' => ?_, fun b ⟨η, hη, hloc⟩ => ?_⟩
  · rw [hprice n b' y hb', hprices b' y hb']
    exact M.ue_price_mono (fun j => by linarith [hDle n b' j]) y
  · rw [hprice n b' y (by linarith [hx0 n]), hprices _ y hb']
    exact M.ue_price_mono (fun j => by linarith [hDle2 n b' j]) y
  · filter_upwards [hx.eventually (Iio_mem_nhds hη)] with n hn
    have hD : ∀ j, D n b j = Ds b j := fun j => by
      have h1 := hDle n b j
      have h2 := hDle2 n b j
      have h3 := hDmono (show b + x n ≤ b + η by linarith) j
      have h4 := hloc j
      linarith
    refine ⟨hD, fun y hb => ?_⟩
    rw [hprice n b y hb, hprices b y hb]
    unfold price
    simp only [hD]

/-- **Optimal borrowing exists against a continuation continuous in debt** (the finite-horizon
version of `ue_attain`): at the prices of nonnegative capacities, with `W` continuous in debt
and savings beyond `K₀` useless (`W(B′) ≤ W(−K₀)` for `B′ ≤ −K₀`), the objective attains its
maximum over `B′ ≤ B̄`. -/
theorem fh_attain (hu : Monotone M.u) (huc : UniformContinuous M.u) {bt : Y → ℝ}
    (hbt : ∀ j, 0 ≤ bt j) {W : ℝ → Y → ℝ} (hWc : ∀ j, Continuous fun b => W b j) {K₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (hWs : ∀ b' j, b' ≤ -K₀ → W b' j ≤ W (-K₀) j) (b : ℝ) (y : Y) :
    ∃ b', b' ≤ M.bmax ∧ ∀ b'', b'' ≤ M.bmax →
      M.obj (M.price (ue_thr bt)) W b y b'' ≤ M.obj (M.price (ue_thr bt)) W b y b' := by
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  have hqneg : ∀ b' y, b' ≤ 0 → M.price (ue_thr bt) b' y = (1 + M.r)⁻¹ := fun b' y hb' =>
    M.ue_price_one (fun j => ue_thr_nonpos hbt hb' j) y
  have hred : ∀ b', b' ≤ -K₀ →
      M.obj (M.price (ue_thr bt)) W b y b' ≤ M.obj (M.price (ue_thr bt)) W b y (-K₀) := by
    intro b' hb'
    unfold obj
    rw [hqneg b' y (by linarith), hqneg (-K₀) y (by linarith)]
    have h1 : M.u (M.inc y - b + (1 + M.r)⁻¹ * b') ≤ M.u (M.inc y - b + (1 + M.r)⁻¹ * -K₀) :=
      hu (by linarith [mul_le_mul_of_nonneg_left hb' (inv_nonneg.2 hr1.le)])
    have h2 : ∑ j, M.P y j * W b' j ≤ ∑ j, M.P y j * W (-K₀) j :=
      ue_sum_mono M.markov (fun j => hWs b' j hb') y
    nlinarith [mul_le_mul_of_nonneg_left h2 M.β_nonneg]
  have hrev : ∀ b', M.price (ue_thr bt) b' y * b' = (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') := by
    intro b'
    unfold price ue_thr
    rw [mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 1
    split_ifs with h
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 h), one_mul, inf_eq_left.2 h]
    · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_Iic.1 h')), zero_mul,
        inf_eq_right.2 (by linarith [hbt j, not_le.1 h])]
  have hsc : ∀ (c : ℝ) {f : ℝ → ℝ}, 0 ≤ c → UpperSemicontinuous f →
      UpperSemicontinuous fun x => c * f x := fun c f hc hf =>
    (continuous_const.mul continuous_id).comp_upperSemicontinuous hf
      (fun a b h => mul_le_mul_of_nonneg_left h hc)
  have ht : ∀ j, UpperSemicontinuous fun b' : ℝ =>
      b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b' := fun j =>
    continuous_id.upperSemicontinuous.inf (isClosed_Iic.upperSemicontinuous_indicator (hbt j))
  have hR : UpperSemicontinuous fun b' : ℝ => (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b') :=
    hsc _ (inv_nonneg.2 hr1.le)
      (upperSemicontinuous_sum fun j _ => hsc _ (M.markov.nonneg y j) (ht j))
  have hgc : Continuous fun z : ℝ => M.inc y - b + z := continuous_const.add continuous_id
  have hU : UpperSemicontinuous fun b' : ℝ => M.u (M.inc y - b + (1 + M.r)⁻¹ *
      ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) :=
    (huc.continuous.comp hgc).comp_upperSemicontinuous hR (fun a c h => hu (by linarith))
  have hC : Continuous fun b' : ℝ => M.β * ∑ j, M.P y j * W b' j :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul (hWc j))
  have husc : UpperSemicontinuous fun b' => M.obj (M.price (ue_thr bt)) W b y b' := by
    have heq : (fun b' => M.obj (M.price (ue_thr bt)) W b y b') = fun b' =>
        M.u (M.inc y - b + (1 + M.r)⁻¹ *
          ∑ j, M.P y j * (b' ⊓ (Set.Iic (bt j)).indicator (fun _ => bt j) b')) +
        M.β * ∑ j, M.P y j * W b' j := funext fun b' => by
      unfold obj
      rw [hrev b']
    rw [heq]
    exact hU.add hC.upperSemicontinuous
  obtain ⟨bs, hbs, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (⟨0, by linarith, M.bmax_nonneg⟩ : (Set.Icc (-K₀) M.bmax).Nonempty) isCompact_Icc
    (husc.upperSemicontinuousOn _)
  refine ⟨bs, hbs.2, fun b'' hb'' => ?_⟩
  rcases le_total (-K₀) b'' with h | h
  · exact isMaxOn_iff.1 hmax _ ⟨h, hb''⟩
  · exact (hred _ h).trans (isMaxOn_iff.1 hmax _ ⟨le_rfl, by linarith [M.bmax_nonneg]⟩)

/-- The constructed default values: `V^D_0 = u(Y − φ(Y))`, `V^D_{n+1} = u(Y − φ) + βE V^D_n`. -/
noncomputable def fhVD : ℕ → Y → ℝ
  | 0 => fun y => M.u (M.inc y - M.φ (M.inc y))
  | n + 1 => fun y => M.defaultRHS (fhVD n) y

/-- The constructed repayment values: `V^R_0(B, Y) = u(Y − B)` and `V^R_{n+1}` the supremum of
the objective at the prices `(1 + r)⁻¹E[1 − D̂_n]` with continuation `max(V^D_n, V^R_n)`. -/
noncomputable def fhVR : ℕ → ℝ → Y → ℝ
  | 0 => fun b y => M.u (M.inc y - b)
  | n + 1 => M.VRsup (M.price fun b' j => 1 - (if fhVR n b' j < M.fhVD n j then 1 else 0))
      (fun b y => max (M.fhVD n y) (fhVR n b y))

/-- The constructed values `V_n = max(V^D_n, V^R_n)`. -/
noncomputable def fhV (n : ℕ) (b : ℝ) (y : Y) : ℝ := max (M.fhVD n y) (M.fhVR n b y)

/-- The constructed default rules (ties repaid). -/
noncomputable def fhD (n : ℕ) (b : ℝ) (y : Y) : ℝ :=
  if M.fhVR n b y < M.fhVD n y then 1 else 0

/-- The constructed prices: `q₀ = 0`, `q_{n+1} = (1 + r)⁻¹E[1 − D̂_n]`. -/
noncomputable def fhq : ℕ → ℝ → Y → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => M.price fun b' j => 1 - M.fhD n b' j

/-- The best value with `n` periods left: `U_0 = ū`, `U_{n+1} = ū + βUₙ`. -/
noncomputable def fhU (ub : ℝ) : ℕ → ℝ
  | 0 => ub
  | n + 1 => ub + M.β * fhU ub n

/-- **The stages of the constructed sequence**: values bounded by `Uₙ`, which a sovereign with
savings `K₀` attains; `V^R_n` continuous and nonincreasing in debt; debt `≤ 0` repaid. -/
theorem fh_stage (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) {K₀ : ℝ}
    (hcons : ∀ j, cbar ≤ M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀) (hK₀ : 0 ≤ K₀) (n : ℕ) :
    (∀ b j, M.fhV n b j ≤ M.fhU (M.u cbar) n) ∧ (∀ j, M.fhU (M.u cbar) n ≤ M.fhVR n (-K₀) j) ∧
      (∀ j, Continuous fun b => M.fhVR n b j) ∧
      (∀ b b' j, b ≤ b' → M.fhVR n b' j ≤ M.fhVR n b j) ∧
      ∀ b j, b ≤ 0 → M.fhVD n j ≤ M.fhVR n b j := by
  have hub := M.ue_u_le hu hsat
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  induction n with
  | zero =>
    refine ⟨fun b j => max_le (hub _) (hub _), fun j => ?_,
      fun j => huc.continuous.comp (continuous_const.sub continuous_id),
      fun b b' j h => hu (by linarith), fun b j hb => hu (by linarith [hφ j])⟩
    have h1 : cbar ≤ M.inc j - -K₀ := by
      have := hcons j
      nlinarith [mul_nonneg (inv_nonneg.2 hr1.le) hK₀]
    exact le_of_eq (hsat _ h1).symm
  | succ n ih =>
    obtain ⟨ia, ib, ic, id, ie⟩ := ih
    have hR : M.fhVR (n + 1) = M.VRsup (M.fhq (n + 1)) (M.fhV n) := rfl
    have hVD1 : ∀ j, M.fhVD (n + 1) j = M.defaultRHS (M.fhVD n) j := fun j => rfl
    have hU1 : M.fhU (M.u cbar) (n + 1) = M.u cbar + M.β * M.fhU (M.u cbar) n := rfl
    have hle : ∀ b y b', b' ≤ M.bmax → M.obj (M.fhq (n + 1)) (M.fhV n) b y b' ≤
        M.VRsup (M.fhq (n + 1)) (M.fhV n) b y := fun b y _ hb' => M.ue_VRsup_le hub ia b y hb'
    have hsup := M.ue_VRsup_sup (M.fhq (n + 1)) (M.fhV n)
    have hVDW : ∀ b j, M.fhVD n j ≤ M.fhV n b j := fun b j => le_max_left _ _
    refine ⟨fun b j => ?_, fun j => ?_, fun j => ?_, fun b b' j h => ?_, fun b j hb => ?_⟩
    · change max (M.fhVD (n + 1) j) (M.fhVR (n + 1) b j) ≤ _
      rw [hR, hVD1, hU1]
      refine max_le ?_ (M.ue_VRsup_ub hub ia b j)
      unfold defaultRHS
      have := mul_le_mul_of_nonneg_left (ue_sum_le M.markov (fun i => (hVDW 0 i).trans
        (ia 0 i)) j) M.β_nonneg
      linarith [hub (M.inc j - M.φ (M.inc j))]
    · rw [hR, hU1]
      have h1 := hle (-K₀) j (-K₀) (by linarith [M.bmax_nonneg])
      have hq : M.fhq (n + 1) (-K₀) j = (1 + M.r)⁻¹ := by
        change M.price (fun b' j => 1 - M.fhD n b' j) (-K₀) j = _
        exact M.ue_price_one (fun i => by
          change 1 - (if M.fhVR n (-K₀) i < M.fhVD n i then 1 else 0) = 1
          rw [(fh_ite_zero _ _).2 (ie (-K₀) i (by linarith)), sub_zero]) j
      have h2 : M.obj (M.fhq (n + 1)) (M.fhV n) (-K₀) j (-K₀) =
          M.u cbar + M.β * ∑ i, M.P j i * M.fhV n (-K₀) i := by
        unfold obj
        rw [hq, hsat _ (hcons j)]
      have h3 : M.β * M.fhU (M.u cbar) n ≤ M.β * ∑ i, M.P j i * M.fhV n (-K₀) i :=
        mul_le_mul_of_nonneg_left (ue_le_sum M.markov (fun i => (ib i).trans
          (le_max_right _ _ : M.fhVR n (-K₀) i ≤ M.fhV n (-K₀) i)) j) M.β_nonneg
      linarith
    · rw [hR]
      refine Metric.continuous_iff.2 fun b₀ ε hε => ?_
      obtain ⟨η, hη, hmod⟩ := M.ue_modulus huc hsup hle (half_pos hε)
      refine ⟨η, hη, fun b₁ hb₁ => ?_⟩
      rw [Real.dist_eq] at hb₁ ⊢
      have hb₁' := abs_lt.1 hb₁
      rw [abs_lt]
      rcases le_total b₁ b₀ with h | h
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₀ j (b₀ - b₁) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
      · have h1 := M.ue_VR_antitone hu hsup hle h j
        have h2 := hmod b₁ j (b₁ - b₀) (by linarith) (by linarith)
        rw [sub_sub_cancel] at h2
        constructor <;> linarith
    · rw [hR]
      exact M.ue_VR_antitone hu hsup hle h j
    · rw [hR, hVD1]
      have h1 := hle b j 0 M.bmax_nonneg
      have h2 : M.u (M.inc j - M.φ (M.inc j)) ≤ M.u (M.inc j - b + M.fhq (n + 1) 0 j * 0) :=
        hu (by linarith [hφ j])
      have h3 := mul_le_mul_of_nonneg_left (ue_sum_mono M.markov (fun i => hVDW 0 i) j)
        M.β_nonneg
      unfold obj at h1
      unfold defaultRHS
      linarith

/-- **The constructed repayment sets are thresholds**: if `V^R_n` is continuous and
nonincreasing in debt and debt `≤ 0` is repaid, then on `B′ ≤ B̄` the repayment indicator of
stage `n` is `1{B′ ≤ b̄(Y′)}` for capacities `b̄ ≥ 0`. -/
theorem fh_thr {n : ℕ} (ic : ∀ j, Continuous fun b => M.fhVR n b j)
    (id : ∀ b b' j, b ≤ b' → M.fhVR n b' j ≤ M.fhVR n b j)
    (ie : ∀ b j, b ≤ 0 → M.fhVD n j ≤ M.fhVR n b j) :
    ∃ bt : Y → ℝ, (∀ j, 0 ≤ bt j) ∧ ∀ b' j, b' ≤ M.bmax → 1 - M.fhD n b' j = ue_thr bt b' j := by
  refine ⟨fun j => sSup {b | 0 ≤ b ∧ b ≤ M.bmax ∧ M.fhVD n j ≤ M.fhVR n b j}, fun j =>
    le_csSup ⟨M.bmax, fun b hb => hb.2.1⟩ ⟨le_rfl, M.bmax_nonneg, ie 0 j le_rfl⟩,
    fun b' j hb' => ?_⟩
  set S := {b | 0 ≤ b ∧ b ≤ M.bmax ∧ M.fhVD n j ≤ M.fhVR n b j} with hS
  change 1 - (if M.fhVR n b' j < M.fhVD n j then (1 : ℝ) else 0) = if b' ≤ sSup S then 1 else 0
  have hne : S.Nonempty := ⟨0, le_rfl, M.bmax_nonneg, ie 0 j le_rfl⟩
  have hbdd : BddAbove S := ⟨M.bmax, fun b hb => hb.2.1⟩
  have hcl : IsClosed S := (isClosed_le continuous_const continuous_id).inter
    ((isClosed_le continuous_id continuous_const).inter (isClosed_le continuous_const (ic j)))
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  by_cases h : b' ≤ sSup S
  · have h1 : M.fhVD n j ≤ M.fhVR n b' j := hmem.2.2.trans (id b' (sSup S) j h)
    simp only [h, ↓reduceIte, not_lt.2 h1, sub_zero]
  · have hpos : 0 < b' := lt_of_le_of_lt hmem.1 (not_le.1 h)
    have hlt : M.fhVR n b' j < M.fhVD n j := by
      by_contra hc
      exact h (le_csSup hbdd ⟨hpos.le, hb', not_lt.1 hc⟩)
    simp only [h, hlt, ↓reduceIte, sub_self]

/-- **Existence of the finite-horizon equilibrium** (AKMM, App. 24.A.1, p. 899, beyond the
text): with `u` nondecreasing, uniformly continuous and satiated and `φ ≥ 0`, there is one
sequence of stage objects that is an equilibrium of the game of every horizon `T` (each stage
by backward induction, optimal borrowing by `fh_attain`). With `fh_unique`, the game of
horizon `T` has exactly these values, default rules and prices. -/
theorem fh_exists (hu : Monotone M.u) (huc : UniformContinuous M.u) {cbar : ℝ}
    (hsat : ∀ c, cbar ≤ c → M.u c = M.u cbar) (hφ : ∀ y, 0 ≤ M.φ (M.inc y)) :
    ∃ (V VR : ℕ → ℝ → Y → ℝ) (VD : ℕ → Y → ℝ) (D Bh q : ℕ → ℝ → Y → ℝ),
      ∀ T, IsFHEqm M T V VR VD D Bh q := by
  have hub := M.ue_u_le hu hsat
  have hr1 : 0 < 1 + M.r := by linarith [M.r_pos]
  set K₀ := max 0 ((cbar + ‖M.inc‖) * (1 + M.r) / M.r) with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_left _ _
  have hcons : ∀ j, cbar ≤ M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ := fun j => by
    have hj : -‖M.inc‖ ≤ M.inc j := by
      have h1 := norm_le_pi_norm M.inc j
      rw [Real.norm_eq_abs] at h1
      linarith [neg_abs_le (M.inc j)]
    have h2 : (cbar + ‖M.inc‖) * (1 + M.r) / M.r ≤ K₀ := le_max_right _ _
    rw [div_le_iff₀ M.r_pos] at h2
    have h3 : cbar + ‖M.inc‖ ≤ K₀ * M.r / (1 + M.r) := by
      rw [le_div_iff₀ hr1]
      linarith
    have h4 : M.inc j - -K₀ + (1 + M.r)⁻¹ * -K₀ = M.inc j + K₀ * M.r / (1 + M.r) := by
      field_simp
      ring
    rw [h4]
    linarith
  have hst := M.fh_stage hu huc hsat hφ hcons hK₀0
  have hatt : ∀ n b y, ∃ b', b' ≤ M.bmax ∧
      M.obj (M.fhq (n + 1)) (M.fhV n) b y b' = M.fhVR (n + 1) b y := by
    intro n b y
    obtain ⟨ia, ib, ic, id, ie⟩ := hst n
    obtain ⟨bt, hbt0, hbt⟩ := M.fh_thr ic id ie
    have hWc : ∀ j, Continuous fun b => M.fhV n b j := fun j => continuous_const.max (ic j)
    have hWs : ∀ b' j, b' ≤ -K₀ → M.fhV n b' j ≤ M.fhV n (-K₀) j := fun b' j _ =>
      (ia b' j).trans ((ib j).trans (le_max_right _ _))
    obtain ⟨bs, hbs, hmax⟩ := M.fh_attain hu huc hbt0 hWc hK₀0 hWs b y
    have hobj : ∀ b'', b'' ≤ M.bmax → M.obj (M.fhq (n + 1)) (M.fhV n) b y b'' =
        M.obj (M.price (ue_thr bt)) (M.fhV n) b y b'' := fun b'' hb'' => M.fh_obj_congr (by
      change M.price (fun b' j => 1 - M.fhD n b' j) b'' y = M.price (ue_thr bt) b'' y
      unfold price
      simp only [hbt b'' _ hb''])
    refine ⟨bs, hbs, ?_⟩
    change _ = M.VRsup (M.fhq (n + 1)) (M.fhV n) b y
    refine le_antisymm (M.ue_VRsup_le hub ia b y hbs) (ciSup_le fun b'' => ?_)
    rw [hobj _ (min_le_right _ _), hobj _ hbs]
    exact hmax _ (min_le_right _ _)
  choose Bh' hBh hBhopt using hatt
  refine ⟨M.fhV, M.fhVR, M.fhVD, M.fhD, fun n => match n with
    | 0 => fun _ _ => 0
    | k + 1 => Bh' k, M.fhq, fun T => ?_⟩
  exact { eq_24_9 := fun _ _ _ _ => rfl
          default_opt := fun _ _ _ _ => rfl
          term_VD := fun _ => rfl
          term_VR := fun _ _ => rfl
          term_q := fun _ _ => rfl
          term_B := fun _ _ => rfl
          eq_24_10 := fun _ _ _ => rfl
          eq_24_11 := fun n _ b y _ hb' => M.ue_VRsup_le hub (hst n).1 b y hb'
          eq_24_12 := fun _ _ _ _ _ => rfl
          borrow_le := fun n _ b y => hBh n b y
          borrow_opt := fun n _ b y => hBhopt n b y }

end UEModel

/-- The example `ue_example` meets the slope condition of the convergence theorems: with
`u = min(c, 3)`, `κ = 1`, `c̄ = 3`, and `Y + B̄/(1 + r) ≤ 2 + 4/5 ≤ 3`. -/
theorem fh_example_hyp :
    (∀ c c', c ≤ c' → c' ≤ 3 → 1 * (c' - c) ≤ ue_example.u c' - ue_example.u c) ∧
      ∀ y, ue_example.inc y + ue_example.bmax * (1 + ue_example.r)⁻¹ ≤ 3 := by
  constructor
  · intro c c' h h'
    change 1 * (c' - c) ≤ min c' 3 - min c 3
    rw [min_eq_left h', min_eq_left (h.trans h')]
    linarith
  · intro y
    change (if y then (2 : ℝ) else 1) + 1 * (1 + 1 / 4)⁻¹ ≤ 3
    split_ifs <;> norm_num

/-- **The limit of the finite-horizon game in a concrete economy** (AKMM, App. 24.A.1, p. 901,
beyond the text): in `ue_example` the finite-horizon game has an equilibrium for every horizon,
the infinite-horizon game has a unique Markov perfect equilibrium (`ue_example_exists_unique`),
and as the horizon grows the finite-horizon values converge to the equilibrium values
uniformly and the debt capacities converge to the equilibrium capacities. -/
theorem fh_example_limit :
    ∃ (V VR : ℕ → ℝ → Bool → ℝ) (VD : ℕ → Bool → ℝ) (D Bh q : ℕ → ℝ → Bool → ℝ)
      (Vs VRs : ℝ → Bool → ℝ) (VDs : Bool → ℝ) (Ds Bhs qs : ℝ → Bool → ℝ),
      (∀ T, IsFHEqm ue_example T V VR VD D Bh q) ∧
      IsOneMPE ue_example Vs VRs VDs Ds Bhs qs ∧
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ b y, |VD n y - VDs y| ≤ ε ∧ |VR n b y - VRs b y| ≤ ε ∧
        |V n b y - Vs b y| ≤ ε) ∧
      ∀ j, Tendsto (fun n => ue_example.fhCap (VR n) (VD n) j) atTop
        (𝓝 (ue_example.fhCap VRs VDs j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := ue_example_hyp
  obtain ⟨hsl, hcap⟩ := fh_example_hyp
  obtain ⟨V, VR, VD, D, Bh, q, hfh⟩ := ue_example.fh_exists h1 h2 h3 h4
  obtain ⟨Vs, VRs, VDs, Ds, Bhs, qs, hs⟩ := ue_example.ue_mpe_exists h1 h2 h3 h4
  obtain ⟨_, _, _, _, hc⟩ := ue_example.fh_capacity_tendsto h1 h4 one_pos hsl hcap hfh hs
  exact ⟨V, VR, VD, D, Bh, q, Vs, VRs, VDs, Ds, Bhs, qs, hfh, hs,
    ue_example.fh_values_tendsto h1 h2 h4 one_pos hsl hcap hfh hs, hc⟩

end AKMM.SovereignDefault
