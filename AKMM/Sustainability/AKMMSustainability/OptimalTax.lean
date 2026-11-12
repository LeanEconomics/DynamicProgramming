/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.LogGrowth
import AKMMSustainability.CarbonCycle
import Mathlib.Topology.Order.IntermediateValue

/-!
# The GHKT optimal carbon tax

AKMM, §25.4.2 (pp. 770–771), equations (25.30)–(25.32): the planner's problem with log utility,
Cobb–Douglas production, full depreciation and damages `e^{−γS}`, after Golosov, Hassler,
Krusell and Tsyvinski (2014).

**The planner's economy** (`GHKT`). Output is `Y_t = e^{z_t − γS_t + g(x_t)}K_t^α` and
`C_t + K_{t+1} = Y_t`; the energy choice `x_t ∈ X` enters output through `g` (the log of the
energy and labour terms) and emits `m(x_t) ≥ 0`; atmospheric carbon is
`S_t = S̄_t + Σ_{v≤t}(1 − d_{t−v})m(x_v)` (25.9), with any kernel `0 ≤ 1 − d_j ≤ 1`, and `S̄`
collects `S₀` and legacy carbon. Let `Ψ = Σ_j β^j(1 − d_j)`.

**Optimality** (`ghkt_optimal`). If `e*` maximises `g(x) − γΨm(x)` over `X`, the plan with
`x_t = e*` and the constant saving rate `K_{t+1} = αβY_t` (`ghktOptK`) is feasible
(`ghkt_opt_feasible`), has convergent utility (`ghkt_opt_summable`) and beats every feasible
plan whose utility converges. The proof is the exact finite-horizon decomposition of
`LogGrowth` (`lg_compare`), the exchange of the order of summation in the carbon term
(`ghkt_sum_interchange`), and bounds on the three error terms, which vanish
(`ghkt_overtake`). No first-order condition or transversality condition is assumed.

**The tax** (`ghkt_tax_of_proportional`, `eq_25_31`, `eq_25_32`). `∂F_t/∂S_t / Y_t = −γ`
(25.31); along the optimum `C_t = (1 − αβ)Y_t`, so the marginal externality (25.30) with
`U' = 1/C` and `∂S_{t+j}/∂e_t = 1 − d_j` is `−γY_tΨ`, and the Pigou tax is
`τ_t = Y_t Σ_j β^j γ(1 − d_j)` (25.32); with the kernel (25.10),
`τ_t = γY_t(φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ)))` (`eq_25_32_ghkt`).
Only `C_{t+j}/Y_{t+j}` constant is used.

**Departure.** The book's planner also buys coal and green energy with final goods (25.23), so
that `C/Y` is not constant and (25.32) is not exact there; we prove it in the GHKT benchmark
where energy uses no final goods. The concrete instance (`coalEconomy`) is GHKT's coal sector:
coal produced from labour, `g(x) = ν log x + (1 − α − ν) log(1 − x/χ)`; there `e*` exists
(`ghkt_coal_opt`), the assumptions hold (`ghkt_coal_assumptions`), and the optimal energy use is
the one a firm chooses when emissions are taxed at `τ_t` (`ghkt_coal_pigou`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

/-- The GHKT planner's economy (AKMM, (25.9), (25.20)–(25.23), pp. 768–770). -/
structure GHKT where
  /-- capital share -/
  α : ℝ
  /-- discount factor -/
  β : ℝ
  /-- damage parameter in `e^{−γS}` -/
  γ : ℝ
  /-- carbon kernel `1 − d_j` -/
  k : ℕ → ℝ
  /-- log productivity `z_t` -/
  z : ℕ → ℝ
  /-- carbon not due to the planner's emissions -/
  Sbar : ℕ → ℝ
  /-- the log energy (and labour) term of output -/
  g : ℝ → ℝ
  /-- emissions of an energy choice -/
  m : ℝ → ℝ
  /-- feasible energy choices -/
  X : Set ℝ
  /-- initial capital -/
  K0 : ℝ

/-- The standing assumptions on a GHKT economy. -/
structure GHKTAssumptions (E : GHKT) : Prop where
  α_pos : 0 < E.α
  α_lt : E.α < 1
  β_pos : 0 < E.β
  β_lt : E.β < 1
  γ_nonneg : 0 ≤ E.γ
  k_nonneg : ∀ j, 0 ≤ E.k j
  k_le : ∀ j, E.k j ≤ 1
  z_bdd : ∃ Z, ∀ t, |E.z t| ≤ Z
  Sbar_nonneg : ∀ t, 0 ≤ E.Sbar t
  Sbar_bdd : ∃ S, ∀ t, E.Sbar t ≤ S
  m_nonneg : ∀ x ∈ E.X, 0 ≤ E.m x
  m_bdd : ∃ M, ∀ x ∈ E.X, E.m x ≤ M
  g_bdd : ∃ L, ∀ x ∈ E.X, E.g x ≤ L
  K0_pos : 0 < E.K0

namespace GHKT

variable (E : GHKT)

/-- `Ψ = Σ_j β^j(1 − d_j)`. -/
noncomputable def Psi : ℝ := ∑' j, E.β ^ j * E.k j

/-- Partial sums `Ψ_n = Σ_{j<n} β^j(1 − d_j)`. -/
noncomputable def PsiN (n : ℕ) : ℝ := ∑ j ∈ range n, E.β ^ j * E.k j

/-- AKMM, (25.9), p. 770: atmospheric carbon under the energy path `x`. -/
noncomputable def carbon (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  E.Sbar t + excessCarbon E.k (fun v => E.m (x v)) t

/-- AKMM, (25.21), p. 768: output `Y_t = e^{z_t − γS_t + g(x_t)}K_t^α`. -/
noncomputable def output (K x : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.exp (E.z t - E.γ * E.carbon x t + E.g (x t)) * K t ^ E.α

/-- Consumption from (25.23) with full depreciation: `C_t = Y_t − K_{t+1}`. -/
noncomputable def cons (K x : ℕ → ℝ) (t : ℕ) : ℝ := E.output K x t - K (t + 1)

/-- A feasible plan: initial capital, energy choices in `X`, positive capital and consumption. -/
def Feasible (K x : ℕ → ℝ) : Prop :=
  K 0 = E.K0 ∧ (∀ t, x t ∈ E.X) ∧ (∀ t, 0 < K t) ∧ ∀ t, 0 < E.cons K x t

/-- The candidate optimum: constant energy choice `e*` and saving `K_{t+1} = αβY_t`. -/
noncomputable def optK (es : ℝ) : ℕ → ℝ
  | 0 => E.K0
  | t + 1 => E.α * E.β *
      (Real.exp (E.z t - E.γ * E.carbon (fun _ => es) t + E.g es) * optK es t ^ E.α)

end GHKT

variable {E : GHKT}

/-- The candidate saves `αβ` of output: `K_{t+1} = αβY_t`. -/
theorem ghkt_opt_saving (es : ℝ) (t : ℕ) :
    E.optK es (t + 1) = E.α * E.β * E.output (E.optK es) (fun _ => es) t := rfl

/-- AKMM, p. 770: along the candidate, `C_t = (1 − αβ)Y_t`. -/
theorem ghkt_opt_cons (es : ℝ) (t : ℕ) :
    E.cons (E.optK es) (fun _ => es) t =
      (1 - E.α * E.β) * E.output (E.optK es) (fun _ => es) t := by
  rw [GHKT.cons, ghkt_opt_saving]; ring

/-- `log Y_t = w_t + α log K_t` with `w_t = z_t − γS_t + g(x_t)`. -/
theorem ghkt_log_output {K x : ℕ → ℝ} (t : ℕ) (hK : 0 < K t) :
    Real.log (E.output K x t) =
      (E.z t - E.γ * E.carbon x t + E.g (x t)) + E.α * Real.log (K t) := by
  rw [GHKT.output, Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hK _).ne',
    Real.log_exp, Real.log_rpow hK]

/-- The candidate is feasible. -/
theorem ghkt_opt_feasible (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X) :
    E.Feasible (E.optK es) (fun _ => es) := by
  have hab : 0 < 1 - E.α * E.β := by nlinarith [h.α_pos, h.α_lt, h.β_pos, h.β_lt]
  have hK : ∀ t, 0 < E.optK es t := by
    intro t
    induction t with
    | zero => exact h.K0_pos
    | succ n ih =>
      change 0 < E.α * E.β * (Real.exp _ * E.optK es n ^ E.α)
      have := h.α_pos; have := h.β_pos
      have := Real.rpow_pos_of_pos ih E.α
      positivity
  refine ⟨rfl, fun _ => hes, hK, fun t => ?_⟩
  rw [ghkt_opt_cons]
  have : 0 < E.output (E.optK es) (fun _ => es) t := by
    unfold GHKT.output; have := Real.rpow_pos_of_pos (hK t) E.α; positivity
  positivity

/-- `Σ_j β^j(1 − d_j)` converges to `Ψ`, and its tail beyond `n` lies in `[0, β^n/(1 − β)]`. -/
theorem ghkt_psi (h : GHKTAssumptions E) :
    HasSum (fun j => E.β ^ j * E.k j) E.Psi ∧
      ∀ n, 0 ≤ E.Psi - E.PsiN n ∧ E.Psi - E.PsiN n ≤ E.β ^ n / (1 - E.β) := by
  have hβ0 := h.β_pos.le
  have hs : Summable (fun j => E.β ^ j * E.k j) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0 j) (h.k_nonneg j))
      (fun j => ?_) (summable_geometric_of_lt_one hβ0 h.β_lt)
    have := h.k_le j
    have := pow_nonneg hβ0 j
    nlinarith
  refine ⟨hs.hasSum, fun n => ?_⟩
  have htail : HasSum (fun i => E.β ^ (i + n) * E.k (i + n)) (E.Psi - E.PsiN n) :=
    (hasSum_nat_add_iff' n).mpr hs.hasSum
  have hgeo : HasSum (fun i => E.β ^ (i + n)) (E.β ^ n / (1 - E.β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 h.β_lt).mul_left (E.β ^ n)
    convert this using 1
    · funext i; rw [pow_add]; ring
    · ring
  refine ⟨htail.nonneg fun i => mul_nonneg (pow_nonneg hβ0 _) (h.k_nonneg _),
    hasSum_le (fun i => ?_) htail hgeo⟩
  have := h.k_le (i + n)
  have := pow_nonneg hβ0 (i + n)
  nlinarith

/-- Exchanging the order of summation in the discounted carbon stock:
`Σ_{t<T} β^t Σ_{v≤t}(1 − d_{t−v})d_v = Σ_{v<T} β^v d_v Ψ_{T−v}`. -/
theorem ghkt_sum_interchange (E : GHKT) (d : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ range T, E.β ^ t * excessCarbon E.k d t =
      ∑ v ∈ range T, E.β ^ v * d v * E.PsiN (T - v) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun v => E.β ^ v * d v * E.PsiN (n + 1 - v))]
    have hstep : ∀ v ∈ range n, E.β ^ v * d v * E.PsiN (n + 1 - v) =
        E.β ^ v * d v * E.PsiN (n - v) + E.β ^ n * (E.k (n - v) * d v) := by
      intro v hv
      have hv' : v < n := mem_range.mp hv
      rw [show n + 1 - v = (n - v) + 1 by omega, GHKT.PsiN, sum_range_succ, ← GHKT.PsiN]
      have : E.β ^ v * E.β ^ (n - v) = E.β ^ n := by rw [← pow_add]; congr 1; omega
      linear_combination (d v * E.k (n - v)) * this
    rw [sum_congr rfl hstep, sum_add_distrib, ← mul_sum, excessCarbon, sum_range_succ,
      show n + 1 - n = 1 by omega, Nat.sub_self]
    simp only [GHKT.PsiN, range_one, sum_singleton, pow_zero, one_mul]
    ring

/-- The core estimate behind optimality: for a feasible plan, at every horizon the utility
shortfall against the candidate is at most an error term that vanishes. -/
theorem ghkt_overtake (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X)
    (hopt : ∀ x ∈ E.X, E.g x - E.γ * E.Psi * E.m x ≤ E.g es - E.γ * E.Psi * E.m es)
    {K x : ℕ → ℝ} (hF : E.Feasible K x)
    (hC : Tendsto (fun t => E.β ^ t * Real.log (E.cons K x t)) atTop (𝓝 0)) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ T,
      ∑ t ∈ range T, E.β ^ t * Real.log (E.cons K x t) ≤
        ∑ t ∈ range T, E.β ^ t * Real.log (E.cons (E.optK es) (fun _ => es) t) + err T := by
  obtain ⟨hK0, hX, hKpos, hCpos⟩ := hF
  obtain ⟨Z, hZ⟩ := h.z_bdd
  obtain ⟨Sb, hSb⟩ := h.Sbar_bdd
  obtain ⟨M, hM⟩ := h.m_bdd
  obtain ⟨L, hL⟩ := h.g_bdd
  have hα0 := h.α_pos
  have hβ0 := h.β_pos
  have hβ1 := h.β_lt
  have hγ := h.γ_nonneg
  have hab0 : 0 < E.α * E.β := mul_pos hα0 hβ0
  have hab1 : E.α * E.β < 1 := by nlinarith [h.α_lt]
  have h1ab : 0 < 1 - E.α * E.β := by linarith
  have h1β : 0 < 1 - E.β := by linarith
  have hM0 : 0 ≤ M := le_trans (h.m_nonneg es hes) (hM es hes)
  obtain ⟨hPsi, hTail⟩ := ghkt_psi h
  have hPsi0 : 0 ≤ E.Psi := hPsi.nonneg fun j => mul_nonneg (pow_nonneg hβ0.le j) (h.k_nonneg j)
  set xs : ℕ → ℝ := fun _ => es with hxsdef
  set Ks := E.optK es with hKsdef
  obtain ⟨-, -, hKs, hCs⟩ := ghkt_opt_feasible h hes
  -- carbon stocks are nonnegative and the candidate's grows at most linearly
  have hEC0 : ∀ y : ℕ → ℝ, (∀ t, y t ∈ E.X) → ∀ t,
      0 ≤ excessCarbon E.k (fun v => E.m (y v)) t := by
    intro y hy t
    exact sum_nonneg fun v _ => mul_nonneg (h.k_nonneg _) (h.m_nonneg _ (hy v))
  have hS0 : ∀ t, 0 ≤ E.carbon x t := fun t => add_nonneg (h.Sbar_nonneg t) (hEC0 x hX t)
  have hSs : ∀ t, 0 ≤ E.carbon xs t ∧ E.carbon xs t ≤ Sb + M * (1 + t) := by
    intro t
    refine ⟨add_nonneg (h.Sbar_nonneg t) (hEC0 xs (fun _ => hes) t), ?_⟩
    have : excessCarbon E.k (fun v => E.m (xs v)) t ≤ ∑ v ∈ range (t + 1), M := by
      refine sum_le_sum fun v _ => ?_
      have := h.k_le (t - v); have := h.k_nonneg (t - v)
      have := h.m_nonneg es hes; have := hM es hes
      simp only [xs]; nlinarith
    simp only [sum_const, card_range, nsmul_eq_mul] at this
    unfold GHKT.carbon
    push_cast at this
    linarith [hSb t]
  -- the decomposition of `LogGrowth`
  set w : ℕ → ℝ := fun t => E.z t - E.γ * E.carbon x t + E.g (x t)
  set ws : ℕ → ℝ := fun t => E.z t - E.γ * E.carbon xs t + E.g es
  have hcmp := fun T => lg_compare (β := E.β) hab0 hab1 hβ0 (K := K) (Y := E.output K x)
    (C := E.cons K x) (w := w) (Ks := Ks) (Ys := E.output Ks xs) (Cs := E.cons Ks xs) (ws := ws)
    hKpos hCpos (fun t => by simp [GHKT.cons]) (fun t => ghkt_log_output t (hKpos t))
    hKs hCs (fun t => by simp [GHKT.cons]) (fun t => ghkt_log_output t (hKs t))
    (fun t => ghkt_opt_saving es t) (by rw [hK0]; rfl) T
  -- the energy and carbon term
  have henergy : ∀ T, ∑ t ∈ range T, E.β ^ t * (w t - ws t) ≤
      E.γ * M / (1 - E.β) * (T * E.β ^ T) := by
    intro T
    set dd : ℕ → ℝ := fun v => E.m (x v) - E.m es
    have hsplit : ∀ t, w t - ws t =
        (E.g (x t) - E.g es) - E.γ * excessCarbon E.k dd t := by
      intro t
      simp only [w, ws, GHKT.carbon, excessCarbon, dd, xs, mul_sub, sum_sub_distrib]
      ring
    have hsum : ∑ t ∈ range T, E.β ^ t * (w t - ws t) =
        ∑ v ∈ range T, E.β ^ v * ((E.g (x v) - E.γ * E.Psi * E.m (x v)) -
          (E.g es - E.γ * E.Psi * E.m es)) +
        E.γ * ∑ v ∈ range T, E.β ^ v * dd v * (E.Psi - E.PsiN (T - v)) := by
      have hI := ghkt_sum_interchange E dd T
      have hL : ∑ t ∈ range T, E.β ^ t * (w t - ws t) = ∑ t ∈ range T,
          (E.β ^ t * (E.g (x t) - E.g es) - E.γ * (E.β ^ t * excessCarbon E.k dd t)) :=
        sum_congr rfl fun t _ => by rw [hsplit]; ring
      rw [hL, sum_sub_distrib, ← mul_sum, hI, mul_sum, mul_sum, ← sum_add_distrib,
        ← sum_sub_distrib]
      refine sum_congr rfl fun v _ => ?_
      simp only [dd]
      ring
    rw [hsum]
    have h1 : ∑ v ∈ range T, E.β ^ v * ((E.g (x v) - E.γ * E.Psi * E.m (x v)) -
        (E.g es - E.γ * E.Psi * E.m es)) ≤ 0 :=
      sum_nonpos fun v _ => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0.le v)
        (by linarith [hopt (x v) (hX v)])
    have h2 : ∑ v ∈ range T, E.β ^ v * dd v * (E.Psi - E.PsiN (T - v)) ≤
        ∑ v ∈ range T, M / (1 - E.β) * E.β ^ T := by
      refine sum_le_sum fun v hv => ?_
      have hv' : v < T := mem_range.mp hv
      obtain ⟨t0, t1⟩ := hTail (T - v)
      have hdd : dd v ≤ M := by
        simp only [dd]; linarith [hM (x v) (hX v), h.m_nonneg es hes]
      have hbv := pow_nonneg hβ0.le v
      have hpow : E.β ^ v * E.β ^ (T - v) = E.β ^ T := by rw [← pow_add]; congr 1; omega
      calc E.β ^ v * dd v * (E.Psi - E.PsiN (T - v))
          ≤ E.β ^ v * M * (E.Psi - E.PsiN (T - v)) := by
            have := mul_le_mul_of_nonneg_left hdd hbv
            exact mul_le_mul_of_nonneg_right this t0
        _ ≤ E.β ^ v * M * (E.β ^ (T - v) / (1 - E.β)) :=
            mul_le_mul_of_nonneg_left t1 (mul_nonneg hbv hM0)
        _ = M / (1 - E.β) * E.β ^ T := by rw [← hpow]; field_simp
    simp only [sum_const, card_range, nsmul_eq_mul] at h2
    have := mul_le_mul_of_nonneg_left h2 hγ
    calc _ ≤ 0 + E.γ * (T * (M / (1 - E.β) * E.β ^ T)) := add_le_add h1 this
      _ = _ := by ring
  -- the competitor's terminal capital: `−α log K_T ≤ Z + L − log C_T`
  have hterm : ∀ T, -(E.α * Real.log (K T)) ≤ Z + L - Real.log (E.cons K x T) := by
    intro T
    have hYpos : 0 < E.output K x T := by
      have := hCpos T; have := hKpos (T + 1); unfold GHKT.cons at *; linarith
    have hCY : Real.log (E.cons K x T) ≤ Real.log (E.output K x T) :=
      Real.log_le_log (hCpos T) (by unfold GHKT.cons; linarith [hKpos (T + 1)])
    rw [ghkt_log_output T (hKpos T)] at hCY
    have := (abs_le.mp (hZ T)).2
    have := hL (x T) (hX T)
    have := mul_nonneg hγ (hS0 T)
    linarith
  -- the candidate's capital grows at most linearly in logs
  set cst := |Real.log (E.α * E.β)| + Z + E.γ * (Sb + M) + E.γ * M + |E.g es| with hcst
  have hcst0 : 0 ≤ cst := by
    have : 0 ≤ Sb := le_trans (h.Sbar_nonneg 0) (hSb 0)
    have := mul_nonneg hγ (add_nonneg this hM0)
    have := mul_nonneg hγ hM0
    have := le_trans (abs_nonneg _) (hZ 0)
    rw [hcst]
    linarith [abs_nonneg (Real.log (E.α * E.β)), abs_nonneg (E.g es)]
  have hrec : ∀ t, Real.log (Ks (t + 1)) =
      (Real.log (E.α * E.β) + ws t) + E.α * Real.log (Ks t) := by
    intro t
    rw [hKsdef, ghkt_opt_saving, Real.log_mul hab0.ne' (by
      unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs t) E.α; positivity),
      ghkt_log_output t (hKs t)]
    ring
  have hlin := lg_linear_bound (a := fun t => Real.log (Ks t))
    (c := fun t => Real.log (E.α * E.β) + ws t) hα0.le h.α_lt hcst0 (fun t => by
      obtain ⟨s0, s1⟩ := hSs t
      have hz := abs_le.mp (hZ t)
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hb1 := abs_le.mp (le_refl |Real.log (E.α * E.β)|)
      have hb2 := abs_le.mp (le_refl |E.g es|)
      have hSb0 : 0 ≤ Sb := le_trans (h.Sbar_nonneg 0) (hSb 0)
      have hγS : E.γ * E.carbon xs t ≤ E.γ * (Sb + M * (1 + t)) :=
        mul_le_mul_of_nonneg_left s1 hγ
      have hγS0 : 0 ≤ E.γ * E.carbon xs t := mul_nonneg hγ s0
      rw [abs_le]
      simp only [ws, hcst]
      have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ 0)
      constructor <;> nlinarith [mul_nonneg hγ hM0, mul_nonneg (mul_nonneg hγ hM0) ht,
        abs_nonneg (Real.log (E.α * E.β)), abs_nonneg (E.g es),
        mul_nonneg (abs_nonneg (Real.log (E.α * E.β))) ht, mul_nonneg hZ0 ht,
        mul_nonneg (mul_nonneg hγ (add_nonneg hSb0 hM0)) ht,
        mul_nonneg (abs_nonneg (E.g es)) ht]) hrec
  -- assemble the error term
  set B := 1 / (1 - E.α * E.β) with hB
  have hB0 : 0 ≤ B := by positivity
  set P := |Real.log (Ks 0)| with hP
  set Q := cst / (1 - E.α) with hQ
  refine ⟨fun T => B * (E.γ * M / (1 - E.β) * (T * E.β ^ T)) +
    B * (E.β ^ T * (Z + L) - E.β ^ T * Real.log (E.cons K x T)) +
    B * E.α * (E.β ^ T * (P + Q * T)), ?_, fun T => ?_⟩
  · have t1 := (tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul
      (B * (E.γ * M / (1 - E.β)))
    have t2 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (Z + L)).sub hC
    have t3 := (lg_tendsto_linear hβ0.le hβ1 P Q).const_mul (B * E.α)
    have := (t1.add (t2.const_mul B)).add t3
    simp only [mul_zero, zero_mul, sub_zero, add_zero] at this
    refine this.congr fun T => ?_
    ring
  · have hc := hcmp T
    have he := henergy T
    have ht := hterm T
    have hl : |Real.log (Ks T)| ≤ P + Q * T := hlin T
    have hl' := (abs_le.mp hl).2
    have hbT : 0 ≤ E.β ^ T := pow_nonneg hβ0.le T
    -- bound the terminal term
    have hterm2 : -(E.β ^ T * (E.α / (1 - E.α * E.β)) *
        (Real.log (K T) - Real.log (Ks T))) ≤
        B * (E.β ^ T * (Z + L) - E.β ^ T * Real.log (E.cons K x T)) +
          B * E.α * (E.β ^ T * (P + Q * T)) := by
      have e1 : E.α / (1 - E.α * E.β) = B * E.α := by rw [hB]; ring
      rw [e1]
      have k1 := mul_le_mul_of_nonneg_left ht (mul_nonneg hB0 hbT)
      have k2 := mul_le_mul_of_nonneg_left hl' (mul_nonneg (mul_nonneg hB0 hα0.le) hbT)
      nlinarith
    have hen := mul_le_mul_of_nonneg_left he hB0
    linarith

/-- The candidate's utility converges. -/
theorem ghkt_opt_summable (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X) :
    Summable (fun t => E.β ^ t * Real.log (E.cons (E.optK es) (fun _ => es) t)) := by
  obtain ⟨Z, hZ⟩ := h.z_bdd
  obtain ⟨Sb, hSb⟩ := h.Sbar_bdd
  obtain ⟨M, hM⟩ := h.m_bdd
  have hα0 := h.α_pos
  have hβ0 := h.β_pos
  have hγ := h.γ_nonneg
  have hab0 : 0 < E.α * E.β := mul_pos hα0 hβ0
  have hab1 : E.α * E.β < 1 := by nlinarith [h.α_lt, h.β_lt]
  have hM0 : 0 ≤ M := le_trans (h.m_nonneg es hes) (hM es hes)
  have hSb0 : 0 ≤ Sb := le_trans (h.Sbar_nonneg 0) (hSb 0)
  set xs : ℕ → ℝ := fun _ => es with hxsdef
  set Ks := E.optK es with hKsdef
  obtain ⟨-, -, hKs, hCs⟩ := ghkt_opt_feasible h hes
  have hSs : ∀ t, 0 ≤ E.carbon xs t ∧ E.carbon xs t ≤ Sb + M * (1 + t) := by
    intro t
    refine ⟨add_nonneg (h.Sbar_nonneg t)
      (sum_nonneg fun v _ => mul_nonneg (h.k_nonneg _) (h.m_nonneg _ hes)), ?_⟩
    have : excessCarbon E.k (fun v => E.m (xs v)) t ≤ ∑ v ∈ range (t + 1), M := by
      refine sum_le_sum fun v _ => ?_
      have := h.k_le (t - v); have := h.k_nonneg (t - v)
      have := h.m_nonneg es hes; have := hM es hes
      simp only [xs]; nlinarith
    simp only [sum_const, card_range, nsmul_eq_mul] at this
    unfold GHKT.carbon
    push_cast at this
    linarith [hSb t]
  set ws : ℕ → ℝ := fun t => E.z t - E.γ * E.carbon xs t + E.g es
  set cst := |Real.log (E.α * E.β)| + Z + E.γ * (Sb + M) + E.γ * M + |E.g es| +
    |Real.log (1 - E.α * E.β)| with hcst
  have hcst0 : 0 ≤ cst := by
    have := mul_nonneg hγ (add_nonneg hSb0 hM0)
    have := mul_nonneg hγ hM0
    have := le_trans (abs_nonneg _) (hZ 0)
    rw [hcst]
    linarith [abs_nonneg (Real.log (E.α * E.β)), abs_nonneg (E.g es),
      abs_nonneg (Real.log (1 - E.α * E.β))]
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ 0)
  set c0 := Z + E.γ * (Sb + M) + E.γ * M + |E.g es| with hc0
  have hws : ∀ t, |ws t| ≤ c0 * (1 + t) := by
    intro t
    obtain ⟨s0, s1⟩ := hSs t
    have hz := abs_le.mp (hZ t)
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hγS : E.γ * E.carbon xs t ≤ E.γ * (Sb + M * (1 + t)) :=
      mul_le_mul_of_nonneg_left s1 hγ
    have hγS0 : 0 ≤ E.γ * E.carbon xs t := mul_nonneg hγ s0
    have hb2 := abs_le.mp (le_refl |E.g es|)
    rw [abs_le]
    simp only [ws, hc0]
    constructor <;> nlinarith [mul_nonneg hγ hM0, mul_nonneg (mul_nonneg hγ hM0) ht,
      abs_nonneg (E.g es), mul_nonneg hZ0 ht,
      mul_nonneg (mul_nonneg hγ (add_nonneg hSb0 hM0)) ht,
      mul_nonneg (abs_nonneg (E.g es)) ht]
  have hcst' : cst = |Real.log (E.α * E.β)| + c0 + |Real.log (1 - E.α * E.β)| := by
    rw [hcst, hc0]; ring
  have hc00 : 0 ≤ c0 := by
    rw [hc0]
    have := mul_nonneg hγ (add_nonneg hSb0 hM0)
    have := mul_nonneg hγ hM0
    linarith [abs_nonneg (E.g es)]
  have hrec : ∀ t, Real.log (Ks (t + 1)) =
      (Real.log (E.α * E.β) + ws t) + E.α * Real.log (Ks t) := by
    intro t
    rw [hKsdef, ghkt_opt_saving, Real.log_mul hab0.ne' (by
      unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs t) E.α; positivity),
      ghkt_log_output t (hKs t)]
    ring
  have hlin := lg_linear_bound (a := fun t => Real.log (Ks t))
    (c := fun t => Real.log (E.α * E.β) + ws t) hα0.le h.α_lt hcst0 (fun t => by
      have := hws t
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      calc |Real.log (E.α * E.β) + ws t| ≤ |Real.log (E.α * E.β)| + |ws t| := abs_add_le _ _
        _ ≤ cst * (1 + t) := by
          rw [hcst']
          nlinarith [abs_nonneg (Real.log (1 - E.α * E.β)), abs_nonneg (Real.log (E.α * E.β)),
            mul_nonneg (abs_nonneg (Real.log (1 - E.α * E.β))) ht,
            mul_nonneg (abs_nonneg (Real.log (E.α * E.β))) ht]) hrec
  -- `log C*_t = log(1 − αβ) + w*_t + α log K*_t`
  have hlogC : ∀ t, Real.log (E.cons Ks xs t) =
      Real.log (1 - E.α * E.β) + ws t + E.α * Real.log (Ks t) := by
    intro t
    rw [hKsdef, hxsdef, ghkt_opt_cons, Real.log_mul (by linarith) (by
      unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs t) E.α; positivity),
      ghkt_log_output t (hKs t)]
    ring
  refine Summable.of_norm_bounded (g := fun t : ℕ => E.β ^ t *
    ((cst + E.α * |Real.log (Ks 0)|) + (cst + E.α * (cst / (1 - E.α))) * t))
    (lg_summable_linear hβ0.le h.β_lt _ _) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le t), hlogC]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le t)
  have h1 := hws t
  have h2 := hlin t
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  calc |Real.log (1 - E.α * E.β) + ws t + E.α * Real.log (Ks t)|
      ≤ |Real.log (1 - E.α * E.β)| + |ws t| + E.α * |Real.log (Ks t)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hα0]
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h2 hα0.le
        rw [hcst'] at this ⊢
        nlinarith [abs_nonneg (Real.log (1 - E.α * E.β)), abs_nonneg (Real.log (E.α * E.β)),
          mul_nonneg (abs_nonneg (Real.log (1 - E.α * E.β))) ht,
          mul_nonneg (abs_nonneg (Real.log (E.α * E.β))) ht]

/-- **The GHKT planner's optimum** (AKMM, pp. 770–771). If `e*` maximises `g − γΨm` on `X`,
the plan `x_t = e*`, `K_{t+1} = αβY_t` maximises `Σβ^t log C_t` among all feasible plans whose
utility converges. -/
theorem ghkt_optimal (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X)
    (hopt : ∀ x ∈ E.X, E.g x - E.γ * E.Psi * E.m x ≤ E.g es - E.γ * E.Psi * E.m es)
    {K x : ℕ → ℝ} (hF : E.Feasible K x) {U : ℝ}
    (hU : HasSum (fun t => E.β ^ t * Real.log (E.cons K x t)) U) :
    U ≤ ∑' t, E.β ^ t * Real.log (E.cons (E.optK es) (fun _ => es) t) := by
  obtain ⟨err, herr, hle⟩ := ghkt_overtake h hes hopt hF hU.summable.tendsto_atTop_zero
  exact sust_hasSum_le_of_partial hU (ghkt_opt_summable h hes).hasSum herr
    (Eventually.of_forall hle)

/-- AKMM, (25.31), p. 771: `∂(e^{−γS}Ỹ)/∂S · 1/(e^{−γS}Ỹ) = −γ`: the derivative of output in
the carbon stock is `−γY`. -/
theorem eq_25_31 (z γ g Ka S : ℝ) :
    HasDerivAt (fun S => Real.exp (z - γ * S + g) * Ka)
      (-γ * (Real.exp (z - γ * S + g) * Ka)) S := by
  have := ((((hasDerivAt_id' S).const_mul γ).const_sub z).add_const g).exp.mul_const Ka
  convert this using 1
  ring

/-- AKMM, (25.30), p. 770: the marginal externality with log utility,
`Λ_t = Σ_j β^j (C_t/C_{t+j}) (∂F_{t+j}/∂S_{t+j}) (∂S_{t+j}/∂e_t)`, with `∂F/∂S = −γY` (25.31) and
`∂S_{t+j}/∂e_t = 1 − d_j` (`excessCarbon_pulse`). When consumption is proportional to output
along the path, `Λ_t = −γY_tΨ`. -/
theorem ghkt_tax_of_proportional {β γ c Psi : ℝ} {k Y C : ℕ → ℝ} (hc : c ≠ 0)
    (hY : ∀ t, 0 < Y t) (hCY : ∀ t, C t = c * Y t) (hPsi : HasSum (fun j => β ^ j * k j) Psi)
    (t : ℕ) :
    HasSum (fun j => β ^ j * (C t / C (t + j)) * (-γ * Y (t + j)) * k j) (-(γ * Y t * Psi)) := by
  have := hPsi.mul_left (-(γ * Y t))
  convert this using 1
  · funext j
    rw [hCY, hCY]
    have := (hY (t + j)).ne'
    field_simp
  · ring

/-- **AKMM, (25.30)–(25.32), p. 771: the optimal carbon tax.** Along the planner's optimum the
marginal externality of a unit of emissions at `t` is `−γY_tΨ`, so the Pigou tax is
`τ_t = Y_t Σ_j β^j γ(1 − d_j)`. -/
theorem eq_25_32 (h : GHKTAssumptions E) {es : ℝ} (hes : es ∈ E.X) (t : ℕ) :
    HasSum (fun j => E.β ^ j *
        (E.cons (E.optK es) (fun _ => es) t / E.cons (E.optK es) (fun _ => es) (t + j)) *
        (-E.γ * E.output (E.optK es) (fun _ => es) (t + j)) * E.k j)
      (-(E.output (E.optK es) (fun _ => es) t * ∑' j, E.β ^ j * E.γ * E.k j)) := by
  have hab : 1 - E.α * E.β ≠ 0 := by nlinarith [h.α_pos, h.α_lt, h.β_pos, h.β_lt]
  obtain ⟨-, -, hKs, -⟩ := ghkt_opt_feasible h hes
  have hY : ∀ s, 0 < E.output (E.optK es) (fun _ => es) s := fun s => by
    unfold GHKT.output; have := Real.rpow_pos_of_pos (hKs s) E.α; positivity
  have hP := (ghkt_psi h).1
  have := ghkt_tax_of_proportional (γ := E.γ) hab hY (fun s => ghkt_opt_cons es s) hP t
  have htsum : ∑' j, E.β ^ j * E.γ * E.k j = E.γ * E.Psi := by
    rw [GHKT.Psi, ← tsum_mul_left]
    congr 1; funext j; ring
  rw [htsum]
  convert this using 1
  ring

/-- AKMM, (25.32) with the GHKT kernel (25.10): the optimal tax is
`τ_t = γY_t(φ_L/(1 − β) + (1 − φ_L)φ₀/(1 − β(1 − φ)))`. -/
theorem eq_25_32_ghkt {β γ φL φ0 φ Yt : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) :
    Yt * ∑' j, β ^ j * γ * ghktKernel φL φ0 φ j =
      γ * Yt * (φL / (1 - β) + (1 - φL) * φ0 / (1 - β * (1 - φ))) := by
  have h := (ghktKernel_hasSum (φL := φL) (φ0 := φ0) hβ0 hβ1 hφ hφ1).mul_left γ
  rw [show (fun j => β ^ j * γ * ghktKernel φL φ0 φ j) =
    fun j => γ * (β ^ j * ghktKernel φL φ0 φ j) from funext fun j => by ring, h.tsum_eq]
  ring

/-- GHKT's coal sector: energy `x` is coal produced from labour at productivity `χ`, so output
has the factor `x^ν(1 − x/χ)^{1−α−ν}`, `g(x) = ν log x + (1 − α − ν) log(1 − x/χ)` on `(0, χ)`,
and coal emits one unit of carbon per unit. -/
noncomputable def coalEconomy (α β γ ν χ K0 : ℝ) (k : ℕ → ℝ) : GHKT where
  α := α
  β := β
  γ := γ
  k := k
  z := fun _ => 0
  Sbar := fun _ => 0
  g := fun x => ν * Real.log x + (1 - α - ν) * Real.log (1 - x / χ)
  m := id
  X := Set.Ioo 0 χ
  K0 := K0

/-- The coal economy satisfies the standing assumptions. -/
theorem ghkt_coal_assumptions {α β γ ν χ K0 : ℝ} {k : ℕ → ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 ≤ γ) (hν : 0 ≤ ν) (hαν : α + ν ≤ 1) (hχ : 0 < χ)
    (hK0 : 0 < K0) (hk0 : ∀ j, 0 ≤ k j) (hk1 : ∀ j, k j ≤ 1) :
    GHKTAssumptions (coalEconomy α β γ ν χ K0 k) where
  α_pos := hα0
  α_lt := hα1
  β_pos := hβ0
  β_lt := hβ1
  γ_nonneg := hγ
  k_nonneg := hk0
  k_le := hk1
  z_bdd := ⟨0, fun _ => by simp [coalEconomy]⟩
  Sbar_nonneg := fun _ => le_rfl
  Sbar_bdd := ⟨0, fun _ => le_rfl⟩
  m_nonneg := fun x hx => le_of_lt hx.1
  m_bdd := ⟨χ, fun x hx => le_of_lt hx.2⟩
  g_bdd := ⟨ν * Real.log χ, fun x hx => by
    have hx0 : 0 < x := hx.1
    have h1 : Real.log x ≤ Real.log χ := Real.log_le_log hx0 hx.2.le
    have hxχ : x / χ < 1 := (div_lt_one hχ).mpr hx.2
    have h2 : Real.log (1 - x / χ) ≤ 0 :=
      Real.log_nonpos (by linarith) (by have := div_pos hx0 hχ; linarith)
    have := mul_le_mul_of_nonneg_left h1 hν
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - α - ν) h2
    simp only [coalEconomy]
    linarith⟩
  K0_pos := hK0

/-- In the coal economy, for any marginal damage `c = γΨ` there is an energy choice
`e* ∈ (0, χ)` solving `ν/e − (1 − α − ν)/(χ − e) = c` (by the intermediate value theorem) and it
maximises `g(x) − cx` on `(0, χ)` (tangent-line bounds). -/
theorem ghkt_coal_opt {α ν χ c : ℝ} (hν : 0 < ν) (hαν : α + ν < 1) (hχ : 0 < χ) :
    ∃ es ∈ Set.Ioo 0 χ, ν / es - (1 - α - ν) / (χ - es) = c ∧
      ∀ x ∈ Set.Ioo 0 χ, ν * Real.log x + (1 - α - ν) * Real.log (1 - x / χ) - c * x ≤
        ν * Real.log es + (1 - α - ν) * Real.log (1 - es / χ) - c * es := by
  set f : ℝ → ℝ := fun e => ν * (χ - e) - (1 - α - ν) * e - c * e * (χ - e)
  have hcont : ContinuousOn f (Set.Icc 0 χ) := by fun_prop
  have hf0 : 0 < f 0 := by simp only [f]; nlinarith
  have hfχ : f χ < 0 := by simp only [f]; nlinarith
  obtain ⟨es, hes, hfes⟩ := intermediate_value_Icc' hχ.le hcont ⟨hfχ.le, hf0.le⟩
  have hes0 : 0 < es := by
    rcases hes.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hfes; linarith
  have hesχ : es < χ := by
    rcases hes.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hfes; linarith
  have hχe : 0 < χ - es := by linarith
  have hfoc : ν / es - (1 - α - ν) / (χ - es) = c := by
    simp only [f] at hfes
    field_simp
    linarith
  refine ⟨es, ⟨hes0, hesχ⟩, hfoc, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x / χ := by
    have : x / χ < 1 := (div_lt_one hχ).mpr hx.2; linarith
  have h1e : 0 < 1 - es / χ := by
    have : es / χ < 1 := (div_lt_one hχ).mpr hesχ; linarith
  have t1 := sust_log_le_tangent hx0 hes0
  have t2 := sust_log_le_tangent h1x h1e
  have hzero : ν * ((x - es) / es) + (1 - α - ν) * ((1 - x / χ - (1 - es / χ)) / (1 - es / χ)) -
      c * (x - es) = (x - es) * (ν / es - (1 - α - ν) / (χ - es) - c) := by
    field_simp
    ring
  rw [hfoc, sub_self, mul_zero] at hzero
  have k1 := mul_le_mul_of_nonneg_left t1 hν.le
  have k2 := mul_le_mul_of_nonneg_left t2 (by linarith : 0 ≤ 1 - α - ν)
  nlinarith

/-- AKMM, p. 771, the Pigou principle in the coal economy: the optimal coal use `e*` is the
input a competitive firm chooses when each unit of carbon is taxed at `τ_t = γΨY_t`: its
marginal product net of the labour it displaces equals the tax,
`Y_t(ν/e* − (1 − α − ν)/(χ − e*)) = τ_t`. -/
theorem ghkt_coal_pigou {α ν χ γ Psi es Yt : ℝ}
    (hfoc : ν / es - (1 - α - ν) / (χ - es) = γ * Psi) :
    Yt * (ν / es - (1 - α - ν) / (χ - es)) = γ * Psi * Yt := by
  rw [hfoc]; ring

/-- **The GHKT optimum in the coal economy** (AKMM, pp. 770–771, instance): there is a coal use
`e* ∈ (0, χ)` such that the plan `x_t = e*`, `K_{t+1} = αβY_t` is optimal among all feasible
plans with convergent utility, and it is taxed at (25.32). -/
theorem ghkt_coal_optimal {α β γ ν χ K0 : ℝ} {k : ℕ → ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 ≤ γ) (hν : 0 < ν) (hαν : α + ν < 1) (hχ : 0 < χ)
    (hK0 : 0 < K0) (hk0 : ∀ j, 0 ≤ k j) (hk1 : ∀ j, k j ≤ 1) :
    ∃ es ∈ Set.Ioo 0 χ, ∀ K x : ℕ → ℝ, (coalEconomy α β γ ν χ K0 k).Feasible K x → ∀ U : ℝ,
      HasSum (fun t => β ^ t * Real.log ((coalEconomy α β γ ν χ K0 k).cons K x t)) U →
      U ≤ ∑' t, β ^ t * Real.log ((coalEconomy α β γ ν χ K0 k).cons
        ((coalEconomy α β γ ν χ K0 k).optK es) (fun _ => es) t) := by
  set E := coalEconomy α β γ ν χ K0 k
  have h := ghkt_coal_assumptions (k := k) (K0 := K0) hα0 hα1 hβ0 hβ1 hγ hν.le hαν.le hχ hK0
    hk0 hk1
  obtain ⟨es, hes, -, hmax⟩ := ghkt_coal_opt (α := α) (c := E.γ * E.Psi) hν hαν hχ
  refine ⟨es, hes, fun K x hF U hU => ghkt_optimal (E := E) h hes (fun y hy => ?_) hF hU⟩
  have := hmax y hy
  simpa [E, coalEconomy] using this

end AKMM.Sustainability
