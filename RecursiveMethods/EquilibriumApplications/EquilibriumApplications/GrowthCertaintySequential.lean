/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyPlanner
import EquilibriumApplications.GrowthCertaintyOptimum

/-!
# The one-sector model under certainty: recursive competitive equilibrium (Ex 16.1(f)–(g))

SLP §16.1, pp. 479–481. With `(g, c)` the planner's policy (`GrowthCertaintyPlanner`), `q` the
corrected price (4), `ψ` the solution of the firm's equation (1) and `Ω` that of the household's
equation (2) (Exercise 16.1(e)), this file proves (R3) and (R4) and that the resulting sequential
allocation is the one-big-market allocation of Exercise 16.1(a)–(c).

* `gc_telescope_le`, `gc_nonpos_of_partial_le`, `gc_concave_le_tangent`: the Euler-equation /
  transversality argument (concavity + telescoping), used three times.
* Firm: `gcFirmV` (value of a capital plan at the prices `Qₙ`), `gc_firm_value_ge` (`ψ` dominates
  every feasible plan), `gc_firm_value_eq` (`ψ` is the value of the policy path),
  `gc_firm_euler_optimal` (the planner's path `z_n = gⁿ(k)` is optimal for a firm with `z₀ = k`).
* **(R3)** (`ex_16_1f_R3`): `h(k, k) = g(k)`, and `ψ(k, k) = c(k) + q(k) ψ(g(k), g(k))`
  (`gc_firm_value_walras`, Walras' law on p. 480).
* Household: `gcHhV`, `gc_hh_value_ge`, `gc_hh_value_eq`, `gc_hh_euler_optimal` (the plan
  `a_n = ψ(kₙ, kₙ)`, consuming `c(kₙ)`, is optimal).
* **(R4)** (`ex_16_1f_R4`): `ω(k, ψ(k, k)) = ψ(g(k), g(k))`.
* `GcRecursiveEq`: the definition (R1)–(R4) of a recursive competitive equilibrium (p. 479–480);
  `ex_16_1f`: `(g, q, ψ, h, Ω, ω)` is one.
* **Exercise 16.1(g)** (`ex_16_1g`): from `z₀ = k̂`, `a₀ = ψ(k̂, k̂)` the firms' capital is
  `z_t = g^t(k̂) = k_t`, households hold `a_t = ψ(k_t, k_t)` (one firm each), and consumption and
  output are `x_t = a_t − q(k_t)a_{t+1} = c(k_t) = f(k_t) − z_{t+1} = y_t`; and (`ex_16_1g_planner`)
  this sequence is the unique optimum `x⁰` of Exercise 16.1(a) (Euler + transversality, Thm 4.15).

**Corrections.**
* The exercise needs `U`, `f` differentiable, an interior planner solution and the state space
  `k > 0` (`K = [a, k_max]`, `a > 0`): all in `GrowthCertaintyPlanner`.
* The manual's (f) uses the envelope condition `ψ_z = f′` and the sufficiency of the household's
  Euler equation without comment; here neither is needed: optimality of the candidate plans is
  proved directly by concavity and telescoping, and single-valuedness of `h`, `ω` (Ex 16.1e) turns
  "is a maximiser" into (R3)–(R4).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped BoundedContinuousFunction

/-! ### The Euler-equation / transversality argument -/

/-- **Telescoping**: if `Xₙ ≤ αₙ dₙ − βₙ d_{n+1}` with `α_{n+1} = βₙ` and `d₀ = 0`, then
`Σ_{n<N} Xₙ ≤ −α_N d_N`. -/
theorem gc_telescope_le {X α γ d : ℕ → ℝ} (hX : ∀ n, X n ≤ α n * d n - γ n * d (n + 1))
    (hαγ : ∀ n, α (n + 1) = γ n) (hd0 : d 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, X n ≤ -(α N * d N) := by
  induction N with
  | zero => simp [hd0]
  | succ N ih =>
    rw [Finset.sum_range_succ, hαγ]
    linarith [hX N]

/-- If the partial sums `Σ_{n ≤ N} Xₙ` are bounded by `B_N → 0`, the sum is `≤ 0`. -/
theorem gc_nonpos_of_partial_le {X : ℕ → ℝ} {V : ℝ} (hX : HasSum X V) {B : ℕ → ℝ}
    (hB : Tendsto B atTop (𝓝 0)) (h : ∀ N, ∑ n ∈ Finset.range (N + 1), X n ≤ B N) : V ≤ 0 :=
  le_of_tendsto_of_tendsto' (hX.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hB h

/-- **The tangent-line inequality** for a concave function on `ℝ₊` differentiable at `x > 0`:
`φ(y) ≤ φ(x) + φ′(x)(y − x)` for `y ≥ 0`. -/
theorem gc_concave_le_tangent {φ : ℝ → ℝ} {φ' x y : ℝ} (hc : ConcaveOn ℝ (Ici 0) φ) (hx : 0 < x)
    (hy : 0 ≤ y) (hd : HasDerivAt φ φ' x) : φ y ≤ φ x + φ' * (y - x) := by
  rcases lt_trichotomy y x with hlt | heq | hgt
  · have := hc.le_slope_of_hasDerivAt (mem_Ici.2 hy) (mem_Ici.2 hx.le) hlt hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst heq; simp
  · have := hc.slope_le_of_hasDerivAt (mem_Ici.2 hx.le) (mem_Ici.2 hy) hgt hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-! ### Set-up -/

variable {U f g c dU df : ℝ → ℝ} {β a kmax : ℝ}

/-- A state `k ∈ K = [a, k_max]` as a capital stock in `[0, k_max]`. -/
def gcKtoZ (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax) :
    Icc (0 : ℝ) kmax :=
  ⟨k, H.a_pos.le.trans k.2.1, k.2.2⟩

/-- The planner's path `kₙ = gⁿ(k)` as a capital plan for the firm. -/
def gcKPath (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax) (n : ℕ) :
    Icc (0 : ℝ) kmax :=
  gcKtoZ H ((gcGK H)^[n] k)

/-- `g(k) ∈ K` as a real number. -/
theorem gcGK_val (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax) :
    ((gcGK H k : Icc a kmax) : ℝ) = g k := rfl

/-- One step along the planner's path. -/
theorem gcKPath_succ (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    (n : ℕ) : gcKPath H k (n + 1) = gcKPath H (gcGK H k) n := by
  simp only [gcKPath, Function.iterate_succ_apply]

/-- `k_{n+1} = g(kₙ)`. -/
theorem gcKPath_succ_val (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    (n : ℕ) : (gcKPath H k (n + 1) : ℝ) = g ((gcGK H)^[n] k) := by
  simp only [gcKPath, gcKtoZ, Function.iterate_succ_apply']
  rfl

/-- The firm data of (1) from the planner (with a chosen bound `M`). -/
noncomputable def gcPlannerM (H : GrowthCertaintyPlanner U f g c dU df β a kmax) : ℝ :=
  Classical.choose (gc_planner_firmData H)

/-- The firm data of (1) from the planner. -/
theorem gcPlannerD (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    GcFirmData f (gcGK H) (gcQK β dU c g) β (gcPlannerM H) :=
  Classical.choose_spec (gc_planner_firmData H)

/-- `f` is strictly concave on `[0, k_max]`. -/
theorem gc_planner_f_strictConcave_Icc (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    StrictConcaveOn ℝ (Icc 0 kmax) f :=
  H.f_strictConcave.subset (fun _ hz => hz.1) (convex_Icc 0 kmax)

/-- `U′(c)` is bounded on `K`. -/
theorem gc_planner_dUc_bdd (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    ∃ Dm, 0 ≤ Dm ∧ ∀ k ∈ Icc a kmax, dU (c k) ≤ Dm := by
  obtain ⟨k₁, hk₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 H.a_le)
    (gc_planner_dUc_continuousOn H)
  exact ⟨dU (c k₁), (gc_planner_dUc_pos H hk₁).le, fun k hk => hmax hk⟩

/-! ### The firm's plans -/

/-- A capital plan `w` for a firm is feasible if `0 ≤ w_{n+1} ≤ f(wₙ)`. -/
def GcFirmFeasible (f : ℝ → ℝ) (w : ℕ → Icc (0 : ℝ) kmax) : Prop := ∀ n, (w (n + 1) : ℝ) ≤ f (w n)

/-- The value `Σₙ Qₙ(k) [f(wₙ) − w_{n+1}]` of a capital plan at the equilibrium prices. -/
noncomputable def gcFirmV (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    (w : ℕ → Icc (0 : ℝ) kmax) : ℝ :=
  ∑' n, gcDisc (gcGK H) (gcQK β dU c g) n k * (f (w n) - w (n + 1))

/-- The terms of a feasible plan lie in `[0, M βⁿ k_max]`. -/
theorem gc_firm_term_mem (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    {w : ℕ → Icc (0 : ℝ) kmax} (hw : GcFirmFeasible f w) (n : ℕ) :
    0 ≤ gcDisc (gcGK H) (gcQK β dU c g) n k * (f (w n) - w (n + 1)) ∧
      gcDisc (gcGK H) (gcQK β dU c g) n k * (f (w n) - w (n + 1)) ≤
        gcPlannerM H * β ^ n * kmax := by
  have D := gcPlannerD H
  have hQ := gcDisc_pos D n k
  have h1 : 0 ≤ f (w n) - w (n + 1) := by linarith [hw n]
  have h2 : f (w n) - w (n + 1) ≤ kmax := by linarith [(D.f_mem (w n)).2, (w (n + 1)).2.1]
  refine ⟨mul_nonneg hQ.le h1, ?_⟩
  calc gcDisc (gcGK H) (gcQK β dU c g) n k * (f (w n) - w (n + 1))
      ≤ gcDisc (gcGK H) (gcQK β dU c g) n k * kmax := mul_le_mul_of_nonneg_left h2 hQ.le
    _ ≤ gcPlannerM H * β ^ n * kmax :=
        mul_le_mul_of_nonneg_right (D.prod_le k n) D.kmax_nonneg

/-- The value of a feasible plan is a convergent series. -/
theorem gc_firm_summable (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    {w : ℕ → Icc (0 : ℝ) kmax} (hw : GcFirmFeasible f w) :
    Summable fun n => gcDisc (gcGK H) (gcQK β dU c g) n k * (f (w n) - w (n + 1)) :=
  Summable.of_nonneg_of_le (fun n => (gc_firm_term_mem H k hw n).1)
    (fun n => (gc_firm_term_mem H k hw n).2)
    (((summable_geometric_of_lt_one H.beta_pos.le H.beta_lt_one).mul_left (gcPlannerM H)).mul_right
      kmax)

/-- `Q_N ψ → 0` along any path, for bounded `ψ`. -/
theorem gc_firm_remainder (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    (ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ) (k : Icc a kmax) (w : ℕ → Icc (0 : ℝ) kmax) :
    Tendsto (fun N => gcDisc (gcGK H) (gcQK β dU c g) N k * ψ ((gcGK H)^[N] k, w N)) atTop
      (𝓝 0) := by
  have : Nonempty (Icc a kmax) := ⟨k⟩
  have D := gcPlannerD H
  have hlim : Tendsto (fun N : ℕ => gcPlannerM H * β ^ N * ‖ψ‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one H.beta_pos.le H.beta_lt_one).const_mul
      (gcPlannerM H)).mul_const ‖ψ‖
  refine squeeze_zero_norm (fun N => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gcDisc_pos D N k)]
  exact mul_le_mul (D.prod_le k N) (by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _)
    (abs_nonneg _) (mul_nonneg (le_of_lt (GcFirmData.M_pos D (a := a))) (pow_nonneg
      H.beta_pos.le N))

/-- **`ψ` dominates every feasible plan** (from (1), by induction and `Q_N ψ → 0`). -/
theorem gc_firm_value_ge (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (k : Icc a kmax) {w : ℕ → Icc (0 : ℝ) kmax} (hw : GcFirmFeasible f w) :
    gcFirmV H k w ≤ ψ (k, w 0) := by
  have D := gcPlannerD H
  have key : ∀ N, ∑ n ∈ Finset.range N, gcDisc (gcGK H) (gcQK β dU c g) n k *
      (f (w n) - w (n + 1)) + gcDisc (gcGK H) (gcQK β dU c g) N k * ψ ((gcGK H)^[N] k, w N) ≤
      ψ (k, w 0) := by
    intro N
    induction N with
    | zero => simp [gcDisc_zero]
    | succ N ih =>
      have hb := (hψ ((gcGK H)^[N] k, w N)).1 (w (N + 1)) (hw N)
      rw [Finset.sum_range_succ, gcDisc_succ', Function.iterate_succ_apply']
      have hQ := gcDisc_pos D N k
      nlinarith [mul_le_mul_of_nonneg_left hb hQ.le]
  have hl := ((gc_firm_summable H k hw).hasSum.tendsto_sum_nat).add (gc_firm_remainder H ψ k w)
  rw [add_zero] at hl
  exact le_of_tendsto' hl key

/-- The firm's policy path from `(k, z)`: `z₀ = z`, `z_{n+1} = h(kₙ, zₙ)`. -/
noncomputable def gcFirmPath (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (k : Icc a kmax) (z : Icc (0 : ℝ) kmax) : ℕ → Icc (0 : ℝ) kmax
  | 0 => z
  | n + 1 => gcFirmPolicy hψ ((gcGK H)^[n] k, gcFirmPath H hψ k z n)

/-- The policy path is feasible. -/
theorem gcFirmPath_feasible (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (k : Icc a kmax) (z : Icc (0 : ℝ) kmax) : GcFirmFeasible f (gcFirmPath H hψ k z) := fun _ =>
  (gcFirmPolicy_spec hψ _).1

/-- **`ψ` is the value of the policy path**. -/
theorem gc_firm_value_eq (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (k : Icc a kmax) (z : Icc (0 : ℝ) kmax) : ψ (k, z) = gcFirmV H k (gcFirmPath H hψ k z) := by
  set w := gcFirmPath H hψ k z with hw
  have key : ∀ N, ∑ n ∈ Finset.range N, gcDisc (gcGK H) (gcQK β dU c g) n k *
      (f (w n) - w (n + 1)) + gcDisc (gcGK H) (gcQK β dU c g) N k * ψ ((gcGK H)^[N] k, w N) =
      ψ (k, z) := by
    intro N
    induction N with
    | zero => simp [gcDisc_zero, hw, gcFirmPath]
    | succ N ih =>
      have hb := (gcFirmPolicy_spec hψ ((gcGK H)^[N] k, w N)).2
      have hw1 : w (N + 1) = gcFirmPolicy hψ ((gcGK H)^[N] k, w N) := rfl
      rw [Finset.sum_range_succ, gcDisc_succ', Function.iterate_succ_apply', hw1]
      rw [← hw1] at hb ⊢
      rw [← ih, hb]
      ring
  have hl := ((gc_firm_summable H k (gcFirmPath_feasible H hψ k z)).hasSum.tendsto_sum_nat).add
    (gc_firm_remainder H ψ k w)
  rw [add_zero] at hl
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun N => (key N).symm) hl

/-- The value of a plan, one period ahead: `V_k(w) = f(w₀) − w₁ + q(k) V_{g(k)}(w₁, w₂, …)`. -/
theorem gc_firm_value_shift (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    {w : ℕ → Icc (0 : ℝ) kmax} (hw : GcFirmFeasible f w) :
    gcFirmV H k w =
      f (w 0) - w 1 + gcQK β dU c g k * gcFirmV H (gcGK H k) (fun n => w (n + 1)) := by
  rw [gcFirmV, (gc_firm_summable H k hw).tsum_eq_zero_add, gcDisc_zero, one_mul, gcFirmV,
    ← tsum_mul_left]
  congr 1
  congr 1
  ext n
  rw [gcDisc_succ]
  ring

/-- **The planner's path is optimal for a firm starting with `z₀ = k`** (Euler equation
`q(kₙ) f′(k_{n+1}) = 1`, concavity of `f`, and the transversality bound `Q_N k_{N+1} → 0`). -/
theorem gc_firm_euler_optimal (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    (k : Icc a kmax) {w : ℕ → Icc (0 : ℝ) kmax} (hw : GcFirmFeasible f w)
    (hw0 : (w 0 : ℝ) = k) : gcFirmV H k w ≤ gcFirmV H k (gcKPath H k) := by
  have D := gcPlannerD H
  have hkf : GcFirmFeasible f (gcKPath H k) := fun n => by
    rw [gcKPath_succ_val]
    set kn := (gcGK H)^[n] k
    have := H.c_pos kn kn.2
    rw [H.c_eq kn kn.2] at this
    change g kn ≤ f kn
    linarith
  set Q := fun n => gcDisc (gcGK H) (gcQK β dU c g) n k with hQ
  set kp := gcKPath H k
  set X : ℕ → ℝ := fun n => Q n * ((f (w n) - w (n + 1)) - (f (kp n) - kp (n + 1))) with hX
  have hsum : HasSum X (gcFirmV H k w - gcFirmV H k kp) := by
    have := (gc_firm_summable H k hw).hasSum.sub (gc_firm_summable H k hkf).hasSum
    refine this.congr_fun fun n => ?_
    simp only [hX, hQ]
    ring
  have hkpos : ∀ n, 0 < (kp n : ℝ) := fun n => H.a_pos.trans_le ((gcGK H)^[n] k).2.1
  have hXle : ∀ n, X n ≤ (Q n * df (kp n)) * ((w n : ℝ) - kp n) -
      Q n * ((w (n + 1) : ℝ) - kp (n + 1)) := fun n => by
    have ht := gc_concave_le_tangent H.f_strictConcave.concaveOn (hkpos n) (w n).2.1
      (H.df_deriv _ (hkpos n))
    have hQn := gcDisc_pos D n k
    simp only [hX]
    nlinarith [mul_le_mul_of_nonneg_left ht hQn.le]
  have hαγ : ∀ n, Q (n + 1) * df (kp (n + 1)) = Q n := fun n => by
    simp only [hQ]
    rw [gcDisc_succ', gcKPath_succ_val, mul_assoc]
    have := gc_planner_q_mul_df H ((gcGK H)^[n] k).2
    change gcDisc _ _ n k * (gcQ β dU c g ((gcGK H)^[n] k) * df (g ((gcGK H)^[n] k))) = _
    rw [this, mul_one]
  have hle := gc_telescope_le hXle hαγ (by simp [hw0, kp, gcKPath, gcKtoZ])
  have hV := gc_nonpos_of_partial_le hsum (B := fun N => gcPlannerM H * β ^ N * kmax) (by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one H.beta_pos.le H.beta_lt_one).const_mul
      (gcPlannerM H)).mul_const kmax) fun N => by
    refine (hle (N + 1)).trans ?_
    rw [hαγ]
    have h1 := (w (N + 1)).2.1
    have h2 := (kp (N + 1)).2.2
    have hQN := gcDisc_pos D N k
    calc -(Q N * ((w (N + 1) : ℝ) - kp (N + 1))) ≤ Q N * kmax := by nlinarith
      _ ≤ gcPlannerM H * β ^ N * kmax := mul_le_mul_of_nonneg_right (D.prod_le k N)
          D.kmax_nonneg
  linarith

/-- **(R3)**: `h(k, k) = g(k)` for every `k ∈ K`, and `ψ(k, k) = c(k) + q(k) ψ(g(k), g(k))`. -/
theorem ex_16_1f_R3 (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) (k : Icc a kmax) :
    gcFirmPolicy hψ (k, gcKtoZ H k) = gcKtoZ H (gcGK H k) ∧
      ψ (k, gcKtoZ H k) = c k + gcQK β dU c g k * ψ (gcGK H k, gcKtoZ H (gcGK H k)) := by
  have D := gcPlannerD H
  have hq := D.q_pos k
  have hgk : (gcKtoZ H (gcGK H k) : ℝ) ≤ f (gcKtoZ H k) := by
    have := H.c_pos k k.2
    rw [H.c_eq k k.2] at this
    change g k ≤ f k
    linarith
  -- every feasible choice is weakly worse than `z′ = g(k)`
  have hbest : ∀ z' : Icc (0 : ℝ) kmax, (z' : ℝ) ≤ f (gcKtoZ H k) →
      f (gcKtoZ H k) - z' + gcQK β dU c g k * ψ (gcGK H k, z') ≤
        f (gcKtoZ H k) - gcKtoZ H (gcGK H k) +
          gcQK β dU c g k * ψ (gcGK H k, gcKtoZ H (gcGK H k)) := by
    intro z' hz'
    set p := gcFirmPath H hψ (gcGK H k) z'
    set w : ℕ → Icc (0 : ℝ) kmax := fun n => Nat.casesOn n (gcKtoZ H k) p with hw
    have hwf : GcFirmFeasible f w := fun n => by
      rcases n with _ | n
      · exact hz'
      · exact gcFirmPath_feasible H hψ (gcGK H k) z' n
    have e1 := gc_firm_value_shift H k hwf
    have e2 := gc_firm_value_eq H hψ (gcGK H k) z'
    have hopt := gc_firm_euler_optimal H k hwf rfl
    have e3 := gc_firm_value_shift H k (w := gcKPath H k) fun n => by
      rw [gcKPath_succ_val]
      set kn := (gcGK H)^[n] k
      have := H.c_pos kn kn.2
      rw [H.c_eq kn kn.2] at this
      change g kn ≤ f kn
      linarith
    have hkp : (fun n => gcKPath H k (n + 1)) = gcKPath H (gcGK H k) := funext fun n =>
      gcKPath_succ H k n
    rw [hkp] at e3
    have hge := gc_firm_value_ge H hψ (gcGK H k) (w := gcKPath H (gcGK H k)) fun n => by
      rw [gcKPath_succ_val]
      set kn := (gcGK H)^[n] (gcGK H k)
      have := H.c_pos kn kn.2
      rw [H.c_eq kn kn.2] at this
      change g kn ≤ f kn
      linarith
    have hp : (fun n => w (n + 1)) = p := rfl
    rw [hp] at e1
    change gcFirmV H k w = f (gcKtoZ H k) - z' + _ at e1
    rw [← e2] at e1
    change gcFirmV H k (gcKPath H k) = f (gcKtoZ H k) - gcKtoZ H (gcGK H k) + _ at e3
    have : ψ (gcGK H k, gcKPath H (gcGK H k) 0) = ψ (gcGK H k, gcKtoZ H (gcGK H k)) := rfl
    rw [this] at hge
    nlinarith [mul_le_mul_of_nonneg_left hge hq.le]
  obtain ⟨hh, eh⟩ := gcFirmPolicy_spec hψ (k, gcKtoZ H k)
  have h1 := hbest _ hh
  have h2 := (hψ (k, gcKtoZ H k)).1 _ hgk
  have heq : ψ (k, gcKtoZ H k) = f (gcKtoZ H k) - gcKtoZ H (gcGK H k) +
      gcQK β dU c g k * ψ (gcGK H k, gcKtoZ H (gcGK H k)) := by
    change ψ (k, gcKtoZ H k) = _ at eh
    linarith
  refine ⟨(gc_firm_policy_unique D (gc_planner_f_strictConcave_Icc H) hψ hcv (k, gcKtoZ H k)
    hgk hh heq eh).symm, ?_⟩
  rw [heq, H.c_eq k k.2]
  rfl

/-- **Walras' law** (p. 480) along the planner's path: `ψ(kₙ, kₙ) − q(kₙ) ψ(k_{n+1}, k_{n+1}) =
c(kₙ)`. -/
theorem gc_firm_value_walras (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) (k : Icc a kmax) :
    ψ (k, gcKtoZ H k) - gcQK β dU c g k * ψ (gcGK H k, gcKtoZ H (gcGK H k)) = c k := by
  rw [(ex_16_1f_R3 H hψ hcv k).2]
  ring

/-- `ψ ≥ 0` (it dominates the plan `(z, 0, 0, …)`, all of whose terms are nonnegative). -/
theorem gc_firm_value_nonneg (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (p : Icc a kmax × Icc (0 : ℝ) kmax) : 0 ≤ ψ p := by
  have D := gcPlannerD H
  set z0 : Icc (0 : ℝ) kmax := ⟨0, le_rfl, D.kmax_nonneg⟩
  set w : ℕ → Icc (0 : ℝ) kmax := fun n => Nat.casesOn n p.2 fun _ => z0 with hw
  have hwf : GcFirmFeasible f w := fun n => by
    rcases n with _ | n
    · exact (D.f_mem p.2).1
    · exact (D.f_mem z0).1
  have := gc_firm_value_ge H hψ p.1 hwf
  exact (tsum_nonneg fun n => (gc_firm_term_mem H p.1 hwf n).1).trans this

/-! ### The household's plans -/

/-- An asset plan `b` is feasible in state path `kₙ = gⁿ(k)` if `q(kₙ) b_{n+1} ≤ bₙ`. -/
def GcHhFeasible (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    (b : ℕ → Ici (0 : ℝ)) : Prop :=
  ∀ n, gcQK β dU c g ((gcGK H)^[n] k) * b (n + 1) ≤ b n

/-- The utility `Σₙ βⁿ U(bₙ − q(kₙ) b_{n+1})` of an asset plan. -/
noncomputable def gcHhV (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    (b : ℕ → Ici (0 : ℝ)) : ℝ :=
  ∑' n, β ^ n * U (b n - gcQK β dU c g ((gcGK H)^[n] k) * b (n + 1))

/-- The utility series of a feasible plan converges. -/
theorem gc_hh_summable (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    {b : ℕ → Ici (0 : ℝ)} (hb : GcHhFeasible H k b) :
    Summable fun n => β ^ n * U (b n - gcQK β dU c g ((gcGK H)^[n] k) * b (n + 1)) := by
  obtain ⟨B, hB⟩ := H.U_bdd
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one H.beta_pos.le
    H.beta_lt_one).mul_left B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos H.beta_pos n), mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _ (by linarith [hb n])) (pow_nonneg H.beta_pos.le n)

/-- `β^N Ω → 0` for bounded `Ω`. -/
theorem gc_hh_remainder (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    (Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ) (k : Icc a kmax) (b : ℕ → Ici (0 : ℝ)) :
    Tendsto (fun N => β ^ N * Ω ((gcGK H)^[N] k, b N)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => β ^ N * ‖Ω‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one H.beta_pos.le H.beta_lt_one).mul_const ‖Ω‖
  refine squeeze_zero_norm (fun N => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos H.beta_pos N)]
  exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact Ω.norm_coe_le_norm _)
    (pow_nonneg H.beta_pos.le N)

/-- **`Ω` dominates every feasible asset plan**. -/
theorem gc_hh_value_ge (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ} (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω)
    (k : Icc a kmax) {b : ℕ → Ici (0 : ℝ)} (hb : GcHhFeasible H k b) :
    gcHhV H k b ≤ Ω (k, b 0) := by
  have key : ∀ N, ∑ n ∈ Finset.range N, β ^ n *
      U (b n - gcQK β dU c g ((gcGK H)^[n] k) * b (n + 1)) +
      β ^ N * Ω ((gcGK H)^[N] k, b N) ≤ Ω (k, b 0) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have h1 := (hΩ ((gcGK H)^[N] k, b N)).1 (b (N + 1)) (hb N)
      rw [Finset.sum_range_succ, pow_succ, Function.iterate_succ_apply']
      have hβ := pow_pos H.beta_pos N
      nlinarith [mul_le_mul_of_nonneg_left h1 hβ.le]
  have hl := ((gc_hh_summable H k hb).hasSum.tendsto_sum_nat).add (gc_hh_remainder H Ω k b)
  rw [add_zero] at hl
  exact le_of_tendsto' hl key

/-- The household's policy path from `(k, a)`: `a₀ = a`, `a_{n+1} = ω(kₙ, aₙ)`. -/
noncomputable def gcHhPath (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω)
    (k : Icc a kmax) (x : Ici (0 : ℝ)) : ℕ → Ici (0 : ℝ)
  | 0 => x
  | n + 1 => gcHhPolicy hΩ ((gcGK H)^[n] k, gcHhPath H hΩ k x n)

/-- The household's policy path is feasible. -/
theorem gcHhPath_feasible (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω)
    (k : Icc a kmax) (x : Ici (0 : ℝ)) : GcHhFeasible H k (gcHhPath H hΩ k x) := fun n =>
  (gcHhPolicy_spec hΩ ((gcGK H)^[n] k, gcHhPath H hΩ k x n)).1

/-- **`Ω` is the utility of the policy path**. -/
theorem gc_hh_value_eq (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ} (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω)
    (k : Icc a kmax) (x : Ici (0 : ℝ)) : Ω (k, x) = gcHhV H k (gcHhPath H hΩ k x) := by
  set b := gcHhPath H hΩ k x with hbdef
  have key : ∀ N, ∑ n ∈ Finset.range N, β ^ n *
      U (b n - gcQK β dU c g ((gcGK H)^[n] k) * b (n + 1)) +
      β ^ N * Ω ((gcGK H)^[N] k, b N) = Ω (k, x) := by
    intro N
    induction N with
    | zero => simp [hbdef, gcHhPath]
    | succ N ih =>
      have h1 := (gcHhPolicy_spec hΩ ((gcGK H)^[N] k, b N)).2
      have hb1 : b (N + 1) = gcHhPolicy hΩ ((gcGK H)^[N] k, b N) := rfl
      rw [Finset.sum_range_succ, pow_succ, Function.iterate_succ_apply', hb1]
      rw [← hb1] at h1 ⊢
      rw [← ih, h1]
      ring
  have hl := ((gc_hh_summable H k (gcHhPath_feasible H hΩ k x)).hasSum.tendsto_sum_nat).add
    (gc_hh_remainder H Ω k b)
  rw [add_zero] at hl
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun N => (key N).symm) hl

/-- The utility of an asset plan, one period ahead. -/
theorem gc_hh_value_shift (H : GrowthCertaintyPlanner U f g c dU df β a kmax) (k : Icc a kmax)
    {b : ℕ → Ici (0 : ℝ)} (hb : GcHhFeasible H k b) :
    gcHhV H k b =
      U (b 0 - gcQK β dU c g k * b 1) + β * gcHhV H (gcGK H k) (fun n => b (n + 1)) := by
  rw [gcHhV, (gc_hh_summable H k hb).tsum_eq_zero_add, gcHhV, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Function.iterate_zero_apply]
  congr 1
  congr 1
  ext n
  rw [pow_succ, Function.iterate_succ_apply]
  ring

/-- The candidate asset plan `aₙ = ψ(kₙ, kₙ)`: one firm per household in every period. -/
noncomputable def gcHhCand (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (k : Icc a kmax) (n : ℕ) : Ici (0 : ℝ) :=
  ⟨ψ ((gcGK H)^[n] k, gcKtoZ H ((gcGK H)^[n] k)), gc_firm_value_nonneg H hψ _⟩

/-- Consumption along the candidate plan is `c(kₙ)`. -/
theorem gcHhCand_cons (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) (k : Icc a kmax) (n : ℕ) :
    (gcHhCand H hψ k n : ℝ) - gcQK β dU c g ((gcGK H)^[n] k) * gcHhCand H hψ k (n + 1) =
      c ((gcGK H)^[n] k) := by
  have := gc_firm_value_walras H hψ hcv ((gcGK H)^[n] k)
  simp only [gcHhCand, Function.iterate_succ_apply']
  exact this

/-- The candidate plan is feasible. -/
theorem gcHhCand_feasible (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) (k : Icc a kmax) : GcHhFeasible H k (gcHhCand H hψ k) := fun n => by
  have := gcHhCand_cons H hψ hcv k n
  have := H.c_pos _ ((gcGK H)^[n] k).2
  linarith

/-- **The candidate plan is optimal** (the household's Euler equation `q(kₙ)U′(cₙ) = βU′(c_{n+1})`,
concavity of `U`, and the transversality bound `βᴺ U′(c_N) a_N → 0`). -/
theorem gc_hh_euler_optimal (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) (k : Icc a kmax) {b : ℕ → Ici (0 : ℝ)} (hb : GcHhFeasible H k b)
    (hb0 : b 0 = gcHhCand H hψ k 0) : gcHhV H k b ≤ gcHhV H k (gcHhCand H hψ k) := by
  obtain ⟨Dm, hDm0, hDm⟩ := gc_planner_dUc_bdd H
  set kn : ℕ → Icc a kmax := fun n => (gcGK H)^[n] k with hkn
  set cand := gcHhCand H hψ k
  set qn : ℕ → ℝ := fun n => gcQK β dU c g (kn n) with hqn
  set X : ℕ → ℝ := fun n => β ^ n * U (b n - qn n * b (n + 1)) -
    β ^ n * U (cand n - qn n * cand (n + 1)) with hX
  have hsum : HasSum X (gcHhV H k b - gcHhV H k cand) :=
    (gc_hh_summable H k hb).hasSum.sub (gc_hh_summable H k (gcHhCand_feasible H hψ hcv k)).hasSum
  have hcons : ∀ n, (cand n : ℝ) - qn n * cand (n + 1) = c (kn n) := gcHhCand_cons H hψ hcv k
  have hXle : ∀ n, X n ≤ (β ^ n * dU (c (kn n))) * ((b n : ℝ) - cand n) -
      (β ^ n * dU (c (kn n)) * qn n) * ((b (n + 1) : ℝ) - cand (n + 1)) := fun n => by
    have hcpos := H.c_pos _ (kn n).2
    have ht := gc_concave_le_tangent H.U_strictConcave.concaveOn hcpos
      (by linarith [hb n] : (0 : ℝ) ≤ b n - qn n * b (n + 1)) (H.dU_deriv _ hcpos)
    have hβ := pow_pos H.beta_pos n
    have key : (b n : ℝ) - qn n * b (n + 1) - c (kn n) =
        ((b n : ℝ) - cand n) - qn n * ((b (n + 1) : ℝ) - cand (n + 1)) := by
      rw [← hcons n]; ring
    rw [key] at ht
    have := mul_le_mul_of_nonneg_left ht hβ.le
    simp only [hX]
    rw [hcons n]
    linarith
  have hαγ : ∀ n, β ^ (n + 1) * dU (c (kn (n + 1))) = β ^ n * dU (c (kn n)) * qn n := fun n => by
    have := gc_planner_household_foc H (kn n).2
    simp only [hqn, gcQK]
    have hk1 : ((kn (n + 1) : Icc a kmax) : ℝ) = g (kn n) := by
      simp only [hkn, Function.iterate_succ_apply']
      rfl
    rw [hk1, pow_succ, mul_assoc, ← this]
    ring
  have hle := gc_telescope_le hXle hαγ (by simp [hb0, cand])
  have hV := gc_nonpos_of_partial_le hsum (B := fun N => β ^ (N + 1) * Dm * ‖ψ‖) (by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one H.beta_pos.le H.beta_lt_one).comp
      (tendsto_add_atTop_nat 1)).mul_const Dm).mul_const ‖ψ‖) fun N => by
    refine (hle (N + 1)).trans ?_
    have h1 := (b (N + 1)).2
    have h2 : (cand (N + 1) : ℝ) ≤ ‖ψ‖ := by
      have := ψ.norm_coe_le_norm (kn (N + 1), gcKtoZ H (kn (N + 1)))
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    have h3 := hDm _ (kn (N + 1)).2
    have h4 := (gc_planner_dUc_pos H (kn (N + 1)).2).le
    have hβ := pow_pos H.beta_pos (N + 1)
    have h1' : (0 : ℝ) ≤ b (N + 1) := h1
    have h5 := mul_pos hβ (gc_planner_dUc_pos H (kn (N + 1)).2)
    calc -(β ^ (N + 1) * dU (c (kn (N + 1))) * ((b (N + 1) : ℝ) - cand (N + 1)))
        ≤ β ^ (N + 1) * dU (c (kn (N + 1))) * cand (N + 1) := by nlinarith
      _ ≤ β ^ (N + 1) * Dm * ‖ψ‖ := by
        have hc0 : (0 : ℝ) ≤ cand (N + 1) := (cand (N + 1)).2
        exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hβ.le) h2 hc0
          (mul_nonneg hβ.le hDm0)
  linarith

/-- **(R4)**: `ω(k, ψ(k, k)) = ψ(g(k), g(k))`: a household starting with one firm buys one firm. -/
theorem ex_16_1f_R4 (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) {Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ}
    (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω) (hcvΩ : GcConcaveA Ω)
    (k : Icc a kmax) : gcHhPolicy hΩ (k, gcHhCand H hψ k 0) = gcHhCand H hψ k 1 := by
  have Dh := gc_planner_hhData H
  set x0 := gcHhCand H hψ k 0
  set x1 := gcHhCand H hψ k 1
  have hq := Dh.q_pos k
  have hc1 := gcHhCand_cons H hψ hcv k 0
  simp only [Function.iterate_zero_apply] at hc1
  have hfeas1 : gcQK β dU c g k * x1 ≤ x0 := by linarith [H.c_pos k k.2]
  have hbest : ∀ b' : Ici (0 : ℝ), gcQK β dU c g k * b' ≤ x0 →
      U (x0 - gcQK β dU c g k * b') + β * Ω (gcGK H k, b') ≤
        U (x0 - gcQK β dU c g k * x1) + β * Ω (gcGK H k, x1) := by
    intro b' hb'
    set p := gcHhPath H hΩ (gcGK H k) b'
    set w : ℕ → Ici (0 : ℝ) := fun n => Nat.casesOn n x0 p with hw
    have hwf : GcHhFeasible H k w := fun n => by
      rcases n with _ | n
      · exact hb'
      · have := gcHhPath_feasible H hΩ (gcGK H k) b' n
        simpa [hw, Function.iterate_succ_apply] using this
    have e1 := gc_hh_value_shift H k hwf
    have e2 := gc_hh_value_eq H hΩ (gcGK H k) b'
    have hopt := gc_hh_euler_optimal H hψ hcv k hwf rfl
    have e3 := gc_hh_value_shift H k (gcHhCand_feasible H hψ hcv k)
    have hcs : (fun n => gcHhCand H hψ k (n + 1)) = gcHhCand H hψ (gcGK H k) := funext fun n => by
      simp only [gcHhCand, Function.iterate_succ_apply]
    rw [hcs] at e3
    have hge := gc_hh_value_ge H hΩ (gcGK H k) (gcHhCand_feasible H hψ hcv (gcGK H k))
    have h01 : gcHhCand H hψ (gcGK H k) 0 = x1 := by
      simp only [x1, gcHhCand, Function.iterate_zero_apply, Function.iterate_one]
    rw [h01] at hge
    have hp : (fun n => w (n + 1)) = p := rfl
    rw [hp] at e1
    change gcHhV H k w = U (x0 - gcQK β dU c g k * b') + _ at e1
    rw [← e2] at e1
    change gcHhV H k (gcHhCand H hψ k) = U (x0 - gcQK β dU c g k * x1) + _ at e3
    nlinarith [mul_le_mul_of_nonneg_left hge H.beta_pos.le]
  obtain ⟨hh, eh⟩ := gcHhPolicy_spec hΩ (k, x0)
  have h1 := hbest _ hh
  have h2 := (hΩ (k, x0)).1 _ hfeas1
  have heq : Ω (k, x0) = U (x0 - gcQK β dU c g k * x1) + β * Ω (gcGK H k, x1) := by
    change Ω (k, x0) = _ at eh
    linarith
  exact (gc_hh_policy_unique Dh H.U_strictConcave hΩ hcvΩ (k, x0) hfeas1 hh heq eh).symm

/-! ### The recursive competitive equilibrium -/

/-- **Recursive competitive equilibrium** (pp. 479–480): (R1) `ψ` satisfies (1) and `h` is its
policy; (R2) `Ω` satisfies (2) and `ω` is its policy; (R3) `h(k, k) = g(k)`;
(R4) `ω[k, ψ(k, k)] = ψ[g(k), g(k)]`, for all `k ∈ K`. -/
def GcRecursiveEq (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    (ψ : Icc a kmax × Icc (0 : ℝ) kmax → ℝ) (h : Icc a kmax × Icc (0 : ℝ) kmax → Icc (0 : ℝ) kmax)
    (Ω : Icc a kmax × Ici (0 : ℝ) → ℝ) (ω : Icc a kmax × Ici (0 : ℝ) → Ici (0 : ℝ)) : Prop :=
  (GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ ∧ ∀ p, (h p : ℝ) ≤ f p.2 ∧
    ψ p = f p.2 - h p + gcQK β dU c g p.1 * ψ (gcGK H p.1, h p)) ∧
  (GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω ∧ ∀ p, gcQK β dU c g p.1 * ω p ≤ p.2 ∧
    Ω p = U (p.2 - gcQK β dU c g p.1 * ω p) + β * Ω (gcGK H p.1, ω p)) ∧
  (∀ k, h (k, gcKtoZ H k) = gcKtoZ H (gcGK H k)) ∧
  ∀ k (hk : 0 ≤ ψ (k, gcKtoZ H k)), (ω (k, ⟨ψ (k, gcKtoZ H k), hk⟩) : ℝ) =
    ψ (gcGK H k, gcKtoZ H (gcGK H k))

/-- **Exercise 16.1(f)**: with `ψ`, `Ω` the solutions of (1)–(2) from Exercise 16.1(e) and `h`, `ω`
their policies, (R3) and (R4) hold, so `(g, q, ψ, h, Ω, ω)` is a recursive competitive
equilibrium. -/
theorem ex_16_1f (H : GrowthCertaintyPlanner U f g c dU df β a kmax) :
    ∃ (ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ) (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
      (Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ)
      (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω),
      GcConcaveZ ψ ∧ GcConcaveA Ω ∧ GcRecursiveEq H ψ (gcFirmPolicy hψ) Ω (gcHhPolicy hΩ) := by
  have : Nonempty (Icc a kmax) := ⟨⟨a, le_rfl, H.a_le⟩⟩
  obtain ⟨ψ, hψ, -, hcv, -, -⟩ := ex_16_1e_firm (gcPlannerD H) (gc_planner_f_strictConcave_Icc H)
  obtain ⟨Ω, hΩ, -, hcvΩ, -, -⟩ := ex_16_1e_household (gc_planner_hhData H) H.U_strictConcave
  refine ⟨ψ, hψ, Ω, hΩ, hcv, hcvΩ, ⟨hψ, fun p => gcFirmPolicy_spec hψ p⟩,
    ⟨hΩ, fun p => gcHhPolicy_spec hΩ p⟩, fun k => (ex_16_1f_R3 H hψ hcv k).1, fun k hk => ?_⟩
  have := ex_16_1f_R4 H hψ hcv hΩ hcvΩ k
  simp only [gcHhCand, Function.iterate_zero_apply, Function.iterate_one] at this
  rw [this]

/-! ### Exercise 16.1(g) -/

/-- **Exercise 16.1(g), the sequential allocation**: from `z₀ = k₀` the firm's capital is
`z_t = k_t = g^t(k₀)` and its output `f(z_t) − z_{t+1} = c(k_t)`; from `a₀ = ψ(k₀, k₀)` the
household holds `a_t = ψ(k_t, k_t)` and consumes `a_t − q(k_t) a_{t+1} = c(k_t)`: the goods market
clears in every period. -/
theorem ex_16_1g (H : GrowthCertaintyPlanner U f g c dU df β a kmax)
    {ψ : Icc a kmax × Icc (0 : ℝ) kmax →ᵇ ℝ} (hψ : GcFirmBellman f (gcGK H) (gcQK β dU c g) ψ)
    (hcv : GcConcaveZ ψ) {Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ}
    (hΩ : GcHouseholdBellman U (gcGK H) (gcQK β dU c g) β Ω) (hcvΩ : GcConcaveA Ω)
    (k₀ : Icc a kmax) (t : ℕ) :
    gcFirmPath H hψ k₀ (gcKtoZ H k₀) t = gcKPath H k₀ t ∧
      gcHhPath H hΩ k₀ (gcHhCand H hψ k₀ 0) t = gcHhCand H hψ k₀ t ∧
      f (gcKPath H k₀ t) - gcKPath H k₀ (t + 1) = c ((gcGK H)^[t] k₀) ∧
      (gcHhCand H hψ k₀ t : ℝ) - gcQK β dU c g ((gcGK H)^[t] k₀) * gcHhCand H hψ k₀ (t + 1) =
        c ((gcGK H)^[t] k₀) := by
  have hz : ∀ t, gcFirmPath H hψ k₀ (gcKtoZ H k₀) t = gcKPath H k₀ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change gcFirmPolicy hψ ((gcGK H)^[t] k₀, gcFirmPath H hψ k₀ (gcKtoZ H k₀) t) = _
      rw [ih]
      have := (ex_16_1f_R3 H hψ hcv ((gcGK H)^[t] k₀)).1
      simp only [gcKPath, Function.iterate_succ_apply']
      exact this
  have ha : ∀ t, gcHhPath H hΩ k₀ (gcHhCand H hψ k₀ 0) t = gcHhCand H hψ k₀ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change gcHhPolicy hΩ ((gcGK H)^[t] k₀, gcHhPath H hΩ k₀ (gcHhCand H hψ k₀ 0) t) = _
      rw [ih]
      have := ex_16_1f_R4 H hψ hcv hΩ hcvΩ ((gcGK H)^[t] k₀)
      have e0 : gcHhCand H hψ ((gcGK H)^[t] k₀) 0 = gcHhCand H hψ k₀ t := by
        simp [gcHhCand]
      have e1 : gcHhCand H hψ ((gcGK H)^[t] k₀) 1 = gcHhCand H hψ k₀ (t + 1) := by
        simp only [gcHhCand, Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [e0, e1] at this
      exact this
  refine ⟨hz t, ha t, ?_, gcHhCand_cons H hψ hcv k₀ t⟩
  rw [gcKPath_succ_val, H.c_eq _ ((gcGK H)^[t] k₀).2]
  rfl

/-- **Exercise 16.1(g), the allocation is the one-big-market allocation**: if `k̂ ∈ K`, the
planner's consumption path `x_t = c(g^t(k̂))` is in `X ∩ Y` and maximises `u` there (Euler
equation, concavity, transversality: Theorem 4.15), so it is the unique optimum `x⁰` of
Exercise 16.1(a) — the competitive equilibrium allocation of Exercises 16.1(b)–(c). -/
theorem ex_16_1g_planner (H : GrowthCertaintyPlanner U f g c dU df β a kmax) {khat kbar : ℝ}
    (hG : GrowthCertaintyHyp U f β khat kbar) (hk : khat ∈ Icc a kmax) :
    ∃ x₀ : BddSeq ℝ, (∀ t, x₀ t = c (g^[t] khat)) ∧ x₀ ∈ gcX ∧ x₀ ∈ gcY f khat ∧
      (∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x₀) ∧
      ∀ x ∈ gcX, x ∈ gcY f khat → (∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x) → x = x₀ := by
  obtain ⟨Dm, hDm0, hDm⟩ := gc_planner_dUc_bdd H
  set k₀ : Icc a kmax := ⟨khat, hk⟩
  have hkn : ∀ n, g^[n] khat = ((gcGK H)^[n] k₀ : ℝ) := fun n => (gcGK_iterate H n k₀).symm
  have hmemK : ∀ n, g^[n] khat ∈ Icc a kmax := fun n => by rw [hkn]; exact ((gcGK H)^[n] k₀).2
  have hcb : ∀ t, ‖c (g^[t] khat)‖ ≤ kmax := fun t => by
    have h1 := H.c_pos _ (hmemK t)
    have h2 := H.c_eq _ (hmemK t)
    have h3 := H.f_le _ (H.a_pos.le.trans (hmemK t).1) (hmemK t).2
    have h4 := (H.g_mem _ (hmemK t)).1
    rw [Real.norm_eq_abs, abs_of_pos h1]
    linarith [H.a_pos]
  set x₀ : BddSeq ℝ := BddSeq.mk (fun t => c (g^[t] khat)) kmax hcb
  have hx₀ : ∀ t, x₀ t = c (g^[t] khat) := fun t => rfl
  have hX : x₀ ∈ gcX := mem_gcX.2 fun t => (H.c_pos _ (hmemK t)).le
  have hY : x₀ ∈ gcY f khat := by
    refine ⟨fun t => (H.c_pos _ (hmemK t)).le, fun t => g^[t] khat, rfl,
      fun t => H.a_pos.le.trans (hmemK t).1, fun t => ?_⟩
    dsimp only
    rw [hx₀, H.c_eq _ (hmemK t), Function.iterate_succ_apply']
    linarith
  have hmax : ∀ z ∈ gcX, z ∈ gcY f khat → gcU β U z ≤ gcU β U x₀ := by
    rintro z hz ⟨-, k', hk'0, hk', hk'f⟩
    set kn : ℕ → ℝ := fun n => g^[n] khat with hkndef
    set X : ℕ → ℝ := fun n => β ^ n * U (z n) - β ^ n * U (x₀ n) with hXd
    have hsum : HasSum X (gcU β U z - gcU β U x₀) :=
      (gc_summable hG hz).hasSum.sub (gc_summable hG hX).hasSum
    have hXle : ∀ n, X n ≤ (β ^ n * dU (c (kn n)) * df (kn n)) * (k' n - kn n) -
        (β ^ n * dU (c (kn n))) * (k' (n + 1) - kn (n + 1)) := fun n => by
      have hcpos := H.c_pos _ (hmemK n)
      have hkpos : 0 < kn n := H.a_pos.trans_le (hmemK n).1
      have tU := gc_concave_le_tangent H.U_strictConcave.concaveOn hcpos (mem_gcX.1 hz n)
        (H.dU_deriv _ hcpos)
      have tf := gc_concave_le_tangent H.f_strictConcave.concaveOn hkpos (hk' n)
        (H.df_deriv _ hkpos)
      have hdU := H.dU_pos _ hcpos
      have hβ := pow_pos H.beta_pos n
      have hc : c (kn n) = f (kn n) - kn (n + 1) := by
        rw [H.c_eq _ (hmemK n)]
        simp only [hkndef, Function.iterate_succ_apply']
      have hzle : (z n : ℝ) ≤ f (k' n) - k' (n + 1) := by linarith [hk'f n]
      simp only [hXd, hx₀]
      have e1 : dU (c (kn n)) * ((z n : ℝ) - c (kn n)) ≤
          dU (c (kn n)) * (df (kn n) * (k' n - kn n) - (k' (n + 1) - kn (n + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hdU.le
        rw [hc]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left tU hβ.le, mul_le_mul_of_nonneg_left e1 hβ.le]
    have hαγ : ∀ n, β ^ (n + 1) * dU (c (kn (n + 1))) * df (kn (n + 1)) =
        β ^ n * dU (c (kn n)) := fun n => by
      have he := H.euler _ (hmemK n)
      have h1 : kn (n + 1) = g (kn n) := by simp only [hkndef, Function.iterate_succ_apply']
      rw [h1, he, pow_succ]
      ring
    have hle := gc_telescope_le hXle hαγ (by simp [hkndef, hk'0])
    have hV := gc_nonpos_of_partial_le hsum (B := fun N => β ^ N * Dm * kmax) (by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one H.beta_pos.le H.beta_lt_one).mul_const
        Dm).mul_const kmax) fun N => by
      refine (hle (N + 1)).trans ?_
      rw [hαγ]
      have h1 := hk' (N + 1)
      have h2 := (hmemK (N + 1)).2
      have h3 := hDm _ (hmemK N)
      have h4 := (H.dU_pos _ (H.c_pos _ (hmemK N))).le
      have hβ := pow_pos H.beta_pos N
      have hkm : 0 ≤ kmax := H.a_pos.le.trans H.a_le
      calc -(β ^ N * dU (c (kn N)) * (k' (N + 1) - kn (N + 1)))
          ≤ β ^ N * dU (c (kn N)) * kn (N + 1) := by nlinarith [mul_nonneg hβ.le h4]
        _ ≤ β ^ N * Dm * kmax := mul_le_mul (mul_le_mul_of_nonneg_left h3 hβ.le) h2
            (H.a_pos.le.trans (hmemK (N + 1)).1) (mul_nonneg hβ.le hDm0)
    linarith
  exact ⟨x₀, hx₀, hX, hY, hmax, fun x hx hxY hxmax =>
    gc_optimum_unique hG hx hxY hxmax hX hY hmax⟩

end StokeyLucasPrescott.EquilibriumApplications
