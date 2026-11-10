/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMLargeFirm
import SearchAndMatching.DMSteadyState

/-!
# Exercise 18.1: firms own capital, households trade firm shares

Miao, §18.4, Exercise 18.1, p. 614: "For the model in Section 18.1, suppose that firms own
capital and make investment decisions. Households trade firm shares. Formulate this market
arrangement and define a search equilibrium. Analyze this equilibrium."

**Formulation.** Households have linear utility `Σ βᵗC_t` and budget
`C_t + p_ts_{t+1} = (p_t + d_t)s_t + y_t` (`y_t`: wages, benefits and lump-sum taxes, taken as
given by the portfolio choice). A unit measure of large firms (§18.1, "Large Firms") with
production function `F(K, N)` pays dividends `d_t = F(K_t, N_t) − w_tN_t − κv_t − I_t`, with
`K_{t+1} = (1 − δ)K_t + I_t` and `N_{t+1} = (1 − ρ)N_t + q^v_tv_t`, `v_t ≥ 0`. Wages are Nash
bargained as in (18.26). Optimality is against plans that differ in finitely many periods.

* `dm_ex1_share_euler`: optimal share holdings imply `p_t = β(p_{t+1} + d_{t+1})`;
  `dm_ex1_hhOptimal_of_euler`: conversely (so `dm_Ex1HHOptimal` is satisfiable);
  `dm_ex1_price`: with `βᵀp_T → 0`, `p₀ = Σ βᵗ⁺¹d_{t+1}`, so maximising firm value means
  maximising dividends discounted at `β`.
* `dm_ex1_capital_euler`: the firm's investment Euler equation
  `1 = β(F_K(K_{t+1}, N_{t+1}) + 1 − δ)`; `dm_ex1_job_creation`: the job creation equation
  `κ/q^v_t = β(F_N(K_{t+1}, N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`; `dm_ex1_wage`: the wage
  equation `w_t = η(F_N(K_t, N_t) + κθ_t) + (1 − η)b` (the derivation of (18.15) with `A`
  replaced by the marginal product of labour).
* `dm_Ex1IsSearchEqm`: a search equilibrium.
* Analysis of the steady state with `F(K, N) = AK^aN^{1−a}`: `dm_ex1_FK`, `dm_ex1_FN` (marginal
  products in terms of `k = K/N`), `dm_ex1_kstar_unique` (the capital Euler equation pins down
  `k* = (aA/(1/β − 1 + δ))^{1/(1−a)}`), `dm_ex1_steady` (in a steady state, `θ` solves the basic
  DMP equation (18.18) with `A` replaced by `A_eff = (1 − a)Ak*^a`, and unemployment is
  `u* = ρ/(ρ + θq(θ))`), `dm_ex1_steady_isSearchEqm` and `dm_ex1_searchEqm_exists`: such a steady
  state is a search equilibrium, and one exists in a concrete economy.
-/

namespace Miao.SearchAndMatching

open Filter Topology

/-- Exercise 18.1: the household's consumption `C_t = (p_t + d_t)s_t − p_ts_{t+1} + y_t`. -/
def dm_hhCons (p d y s : ℕ → ℝ) (t : ℕ) : ℝ := (p t + d t) * s t - p t * s (t + 1) + y t

/-- Exercise 18.1: optimal share holdings: no share plan with the same `s₀` that coincides with
`s` from some date `T` on gives higher discounted consumption. -/
def dm_Ex1HHOptimal (β : ℝ) (p d y s : ℕ → ℝ) : Prop :=
  ∀ (T : ℕ) (s' : ℕ → ℝ), s' 0 = s 0 → (∀ t, T ≤ t → s' t = s t) →
    ∑ t ∈ Finset.range T, β ^ t * dm_hhCons p d y s' t ≤
      ∑ t ∈ Finset.range T, β ^ t * dm_hhCons p d y s t

/-- **Exercise 18.1** (Miao, p. 614): optimal share holdings imply the asset-pricing equation
`p_t = β(p_{t+1} + d_{t+1})`. -/
theorem dm_ex1_share_euler {β : ℝ} {p d y s : ℕ → ℝ} (hβ : 0 < β)
    (hopt : dm_Ex1HHOptimal β p d y s) (t : ℕ) : p t = β * (p (t + 1) + d (t + 1)) := by
  have gain : ∀ ε : ℝ, β ^ t * ε * (β * (p (t + 1) + d (t + 1)) - p t) ≤ 0 := by
    intro ε
    set s' : ℕ → ℝ := fun r ↦ s r + if r = t + 1 then ε else 0 with hs'
    have h0 : s' 0 = s 0 := by simp [hs']
    have hag : ∀ r, t + 1 + 1 ≤ r → s' r = s r := by
      intro r hr
      have : r ≠ t + 1 := by omega
      simp [hs', this]
    have h := hopt (t + 1 + 1) s' h0 hag
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
      Finset.sum_range_succ] at h
    have hlow : ∑ r ∈ Finset.range t, β ^ r * dm_hhCons p d y s' r =
        ∑ r ∈ Finset.range t, β ^ r * dm_hhCons p d y s r := by
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr' := Finset.mem_range.mp hr
      have h1 : r ≠ t + 1 := by omega
      have h2 : r ≠ t := by omega
      simp [dm_hhCons, hs', h1, h2]
    rw [hlow] at h
    have ht1 : t ≠ t + 1 := by omega
    have ht3 : t + 1 + 1 ≠ t + 1 := by omega
    simp only [dm_hhCons, hs', ht1, ht3, ↓reduceIte, add_zero] at h
    rw [pow_succ] at h
    nlinarith
  have hbt : 0 < β ^ t := pow_pos hβ t
  have h1 := gain 1
  have h2 := gain (-1)
  have a : β * (p (t + 1) + d (t + 1)) - p t ≤ 0 := by nlinarith
  have b : 0 ≤ β * (p (t + 1) + d (t + 1)) - p t := by nlinarith
  linarith

/-- **Exercise 18.1** (Miao, p. 614): conversely, if `p_t = β(p_{t+1} + d_{t+1})` for all `t`,
every share plan is optimal (households are indifferent at the margin). -/
theorem dm_ex1_hhOptimal_of_euler {β : ℝ} {p d y s : ℕ → ℝ}
    (he : ∀ t, p t = β * (p (t + 1) + d (t + 1))) : dm_Ex1HHOptimal β p d y s := by
  intro T s' h0 hag
  refine le_of_eq ?_
  set D : ℕ → ℝ := fun r ↦ β ^ r * (p r + d r) * (s' r - s r) with hD
  have hterm : ∀ r, β ^ r * dm_hhCons p d y s' r =
      β ^ r * dm_hhCons p d y s r + (D r - D (r + 1)) := by
    intro r
    simp only [dm_hhCons, hD]
    rw [pow_succ]
    linear_combination (-β ^ r * (s' (r + 1) - s (r + 1))) * he r
  rw [Finset.sum_congr rfl fun r _ ↦ hterm r, Finset.sum_add_distrib, Finset.sum_range_sub']
  have hD0 : D 0 = 0 := by simp [hD, h0]
  have hDT : D T = 0 := by simp [hD, hag T le_rfl]
  rw [hD0, hDT, sub_zero, add_zero]

/-- **Exercise 18.1** (Miao, p. 614): iterating `p_t = β(p_{t+1} + d_{t+1})` with `βᵀp_T → 0`
gives the share price as the present value of dividends, `p₀ = Σ_{t ≥ 0} β^{t+1}d_{t+1}`. -/
theorem dm_ex1_price {β : ℝ} {p d : ℕ → ℝ} (he : ∀ t, p t = β * (p (t + 1) + d (t + 1)))
    (htv : Tendsto (fun T ↦ β ^ T * p T) atTop (𝓝 0)) :
    Tendsto (fun T ↦ ∑ t ∈ Finset.range T, β ^ (t + 1) * d (t + 1)) atTop (𝓝 (p 0)) := by
  have hpart : ∀ T, p 0 = ∑ t ∈ Finset.range T, β ^ (t + 1) * d (t + 1) + β ^ T * p T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, he n, pow_succ]
      ring
  have : (fun T ↦ ∑ t ∈ Finset.range T, β ^ (t + 1) * d (t + 1)) =
      fun T ↦ p 0 - β ^ T * p T := by
    funext T; rw [hpart T]; ring
  rw [this]
  simpa using htv.const_sub (p 0)

/-- Exercise 18.1: the firm's dividend `d_t = F(K_t, N_t) − w_tN_t − κv_t − I_t`. -/
def dm_ex1Div (F : ℝ → ℝ → ℝ) (w : ℕ → ℝ) (κ : ℝ) (K I N v : ℕ → ℝ) (t : ℕ) : ℝ :=
  F (K t) (N t) - w t * N t - κ * v t - I t

/-- Exercise 18.1: a feasible plan of the firm: capital accumulation, (18.22) and `v ≥ 0`. -/
def dm_Ex1Feasible (δ ρ : ℝ) (qv K I N v : ℕ → ℝ) : Prop :=
  ∀ t, K (t + 1) = (1 - δ) * K t + I t ∧ N (t + 1) = (1 - ρ) * N t + qv t * v t ∧ 0 ≤ v t

/-- Exercise 18.1: an optimal plan of the firm (value maximisation, i.e. dividends discounted at
`β` by `dm_ex1_price`), against plans with the same `K₀, N₀` coinciding from some date on. -/
def dm_Ex1FirmOptimal (F : ℝ → ℝ → ℝ) (w : ℕ → ℝ) (κ β δ ρ : ℝ) (qv K I N v : ℕ → ℝ) : Prop :=
  dm_Ex1Feasible δ ρ qv K I N v ∧ ∀ (T : ℕ) (K' I' N' v' : ℕ → ℝ),
    dm_Ex1Feasible δ ρ qv K' I' N' v' → K' 0 = K 0 → N' 0 = N 0 →
    (∀ t, T ≤ t → K' t = K t ∧ I' t = I t ∧ N' t = N t ∧ v' t = v t) →
      ∑ t ∈ Finset.range T, β ^ t * dm_ex1Div F w κ K' I' N' v' t ≤
        ∑ t ∈ Finset.range T, β ^ t * dm_ex1Div F w κ K I N v t

/-- **Exercise 18.1** (Miao, p. 614): the firm's investment Euler equation
`1 = β(F_K(K_{t+1}, N_{t+1}) + 1 − δ)`. -/
theorem dm_ex1_capital_euler {F : ℝ → ℝ → ℝ} {w qv K I N v : ℕ → ℝ} {κ β δ ρ FK : ℝ}
    (hopt : dm_Ex1FirmOptimal F w κ β δ ρ qv K I N v) (t : ℕ) (hβ : 0 < β)
    (hF : HasDerivAt (fun k ↦ F k (N (t + 1))) FK (K (t + 1))) :
    1 = β * (FK + 1 - δ) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  set K' : ℝ → ℕ → ℝ := fun ε s ↦ K s + if s = t + 1 then ε else 0 with hK'
  set I' : ℝ → ℕ → ℝ := fun ε s ↦ I s + (if s = t then ε else 0) -
    (if s = t + 1 then (1 - δ) * ε else 0) with hI'
  set φ : ℝ → ℝ := fun ε ↦ β ^ t * -ε + β ^ (t + 1) *
    (F (K (t + 1) + ε) (N (t + 1)) - F (K (t + 1)) (N (t + 1)) + (1 - δ) * ε) with hφ
  have ht1 : t ≠ t + 1 := by omega
  have ht2 : t + 1 ≠ t := by omega
  have ht3 : t + 1 + 1 ≠ t + 1 := by omega
  have hmax : IsLocalMax φ 0 := by
    refine Filter.Eventually.of_forall fun ε ↦ ?_
    have hφ0 : φ 0 = 0 := by simp [hφ]
    rw [hφ0]
    have hfe : dm_Ex1Feasible δ ρ qv (K' ε) (I' ε) N v := by
      intro s
      refine ⟨?_, (hfeas s).2.1, (hfeas s).2.2⟩
      rcases eq_or_ne s t with rfl | hst
      · simp only [hK', hI', ht1, ↓reduceIte, add_zero, sub_zero]
        rw [(hfeas s).1]; ring
      rcases eq_or_ne s (t + 1) with rfl | hst1
      · simp only [hK', hI', ht2, ht3, ↓reduceIte, add_zero]
        rw [(hfeas (t + 1)).1]; ring
      · have h1 : s + 1 ≠ t + 1 := by omega
        simp only [hK', hI', hst, hst1, h1, ↓reduceIte, add_zero, sub_zero]
        exact (hfeas s).1
    have h0 : K' ε 0 = K 0 := by simp [hK']
    have hag : ∀ s, t + 1 + 1 ≤ s → K' ε s = K s ∧ I' ε s = I s ∧ N s = N s ∧ v s = v s := by
      intro s hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [hK', hI', h1, h2]
    have h := hbest (t + 1 + 1) (K' ε) (I' ε) N v hfe h0 rfl hag
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
      Finset.sum_range_succ] at h
    have hlow : ∑ s ∈ Finset.range t, β ^ s * dm_ex1Div F w κ (K' ε) (I' ε) N v s =
        ∑ s ∈ Finset.range t, β ^ s * dm_ex1Div F w κ K I N v s := by
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      have hs' := Finset.mem_range.mp hs
      have h1 : s ≠ t + 1 := by omega
      have h2 : s ≠ t := by omega
      simp [dm_ex1Div, hK', hI', h1, h2]
    rw [hlow] at h
    generalize ∑ s ∈ Finset.range t, β ^ s * dm_ex1Div F w κ K I N v s = S at h
    simp only [dm_ex1Div, hK', hI', hφ, ht1, ht2, ↓reduceIte, add_zero, sub_zero] at h ⊢
    linarith
  have h2 : HasDerivAt (fun ε : ℝ ↦ K (t + 1) + ε) 1 0 := (hasDerivAt_id' 0).const_add _
  have hF' : HasDerivAt (fun k ↦ F k (N (t + 1))) FK (K (t + 1) + 0) := by rwa [add_zero]
  have hFc : HasDerivAt (fun ε ↦ F (K (t + 1) + ε) (N (t + 1))) (FK * 1) 0 := hF'.comp 0 h2
  have hid := hasDerivAt_id' (0 : ℝ)
  have hd : HasDerivAt φ (β ^ t * -1 + β ^ (t + 1) * (FK * 1 + (1 - δ) * 1)) 0 :=
    (hid.neg.const_mul (β ^ t)).add (((hFc.sub_const (F (K (t + 1)) (N (t + 1)))).add
      (hid.const_mul (1 - δ))).const_mul (β ^ (t + 1)))
  have hz := hmax.hasDerivAt_eq_zero hd
  have hbt : 0 < β ^ t := pow_pos hβ t
  have key : β ^ t * (β * (FK + 1 - δ) - 1) = 0 := by
    rw [pow_succ] at hz
    linear_combination hz
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- **Exercise 18.1** (Miao, p. 614): an optimal plan of the capital-owning firm with positive
vacancies at `t, t + 1` satisfies the job creation equation
`κ/q^v_t = β(F_N(K_{t+1}, N_{t+1}) − w_{t+1} + (1 − ρ)κ/q^v_{t+1})` (by `dm_firm_euler` applied
to `F_t(N) = F(K_t, N) − I_t`). -/
theorem dm_ex1_job_creation {F : ℝ → ℝ → ℝ} {w qv K I N v : ℕ → ℝ} {κ β δ ρ FN : ℝ}
    (hopt : dm_Ex1FirmOptimal F w κ β δ ρ qv K I N v) (t : ℕ) (hβ : 0 < β) (hq : 0 < qv t)
    (hq1 : 0 < qv (t + 1)) (hv : 0 < v t) (hv1 : 0 < v (t + 1))
    (hF : HasDerivAt (fun n ↦ F (K (t + 1)) n) FN (N (t + 1))) :
    κ / qv t = β * (FN - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  obtain ⟨hfeas, hbest⟩ := hopt
  have hopt' : dm_FirmOptimal (fun s n ↦ F (K s) n - I s) w κ β ρ qv N v := by
    refine ⟨fun s ↦ (hfeas s).2, fun T N' v' hfe' h0 hag ↦ ?_⟩
    have hfe : dm_Ex1Feasible δ ρ qv K I N' v' := fun s ↦ ⟨(hfeas s).1, hfe' s⟩
    have hag' : ∀ s, T ≤ s → K s = K s ∧ I s = I s ∧ N' s = N s ∧ v' s = v s :=
      fun s hs ↦ ⟨rfl, rfl, hag s hs⟩
    have h := hbest T K I N' v' hfe rfl h0 hag'
    have e : ∀ N₁ v₁ : ℕ → ℝ, ∀ s, dm_ex1Div F w κ K I N₁ v₁ s =
        dm_firmProfit (fun s n ↦ F (K s) n - I s) w κ N₁ v₁ s := by
      intro N₁ v₁ s; simp only [dm_ex1Div, dm_firmProfit]; ring
    simp only [e] at h
    exact h
  exact dm_firm_euler (F := fun s n ↦ F (K s) n - I s) hopt' t hβ hq hq1 hv hv1
    (by simpa using hF.sub_const (I (t + 1)))

/-- **Exercise 18.1** (Miao, p. 614): the Nash-bargained wage in the capital-owning large firm
is `w_t = η(F_N(K_t, N_t) + κθ_t) + (1 − η)b`: the firm's marginal value of a worker
`∂J_t/∂N = F_N(K_t, N_t) − w_t + (1 − ρ)κ/q^v_t` takes the place of `J^F_t`, and the derivation
of (18.15) goes through with `A` replaced by `F_N(K_t, N_t)`. -/
theorem dm_ex1_wage {b κ β ρ η : ℝ} {JF JW JU w qv qu θ FN : ℕ → ℝ} (t : ℕ)
    (h4 : JF t = FN t - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)))
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12t : η * dm_surplus JF JW JU t = JW t - JU t)
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1))
    (h13 : (1 - η) * dm_surplus JF JW JU (t + 1) = κ / (β * qv t))
    (hqu : qu t = θ t * qv t) (hβ : β ≠ 0) (hq : qv t ≠ 0) (hη1 : η ≠ 1) :
    w t = η * (FN t + κ * θ t) + (1 - η) * b :=
  eq_18_15 t h4 h9 h10 h12t h12 h13 hqu hβ hq hη1

/-- **Exercise 18.1** (Miao, p. 614): a **search equilibrium** of the economy with capital:
sequences `C, K, I, N, u, v, θ, w, q^v, p, d` (with `u, v > 0`) such that (18.1)–(18.3) hold,
`d` is the dividend, shares satisfy `p_t = β(p_{t+1} + d_{t+1})` (one share outstanding), the
firm's capital Euler and job creation equations hold (`F_K`, `F_N` the marginal products), the
wage satisfies `w_t = η(F_N + κθ_t) + (1 − η)b`, and the resource constraint
`C_t + I_t + κv_t = F(K_t, N_t)` holds (benefits are financed by lump-sum taxes). -/
def dm_Ex1IsSearchEqm (MF : DMMatchingFn) (F FK FN : ℝ → ℝ → ℝ) (b κ β δ ρ η : ℝ)
    (C K I N u v θ w qv p d : ℕ → ℝ) : Prop :=
  ∀ t, 0 < u t ∧ 0 < v t ∧ θ t = v t / u t ∧ qv t = dm_q MF (θ t) ∧
    N (t + 1) = (1 - ρ) * N t + MF.M (u t) (v t) ∧ u t = 1 - N t ∧
    K (t + 1) = (1 - δ) * K t + I t ∧
    d t = F (K t) (N t) - w t * N t - κ * v t - I t ∧
    p t = β * (p (t + 1) + d (t + 1)) ∧
    1 = β * (FK (K (t + 1)) (N (t + 1)) + 1 - δ) ∧
    κ / qv t = β * (FN (K (t + 1)) (N (t + 1)) - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) ∧
    w t = η * (FN (K t) (N t) + κ * θ t) + (1 - η) * b ∧
    C t + I t + κ * v t = F (K t) (N t)

/-- Exercise 18.1: for `F(K, N) = AK^aN^{1−a}`, `F_K = aA(K/N)^{a−1}`. -/
theorem dm_ex1_FK {A a K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    HasDerivAt (fun k ↦ A * k ^ a * N ^ (1 - a)) (a * A * (K / N) ^ (a - 1)) K := by
  have h := ((Real.hasDerivAt_rpow_const (p := a) (Or.inl hK.ne')).const_mul A).mul_const
    (N ^ (1 - a))
  refine h.congr_deriv ?_
  rw [Real.div_rpow hK.le hN.le]
  have e : N ^ (1 - a) = (N ^ (a - 1))⁻¹ := by
    rw [← Real.rpow_neg hN.le]; ring_nf
  rw [e]
  have : 0 < N ^ (a - 1) := by positivity
  field_simp

/-- Exercise 18.1: for `F(K, N) = AK^aN^{1−a}`, `F_N = (1 − a)A(K/N)^a`. -/
theorem dm_ex1_FN {A a K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    HasDerivAt (fun n ↦ A * K ^ a * n ^ (1 - a)) ((1 - a) * A * (K / N) ^ a) N := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - a) (Or.inl hN.ne')).const_mul (A * K ^ a)
  refine h.congr_deriv ?_
  rw [Real.div_rpow hK.le hN.le]
  have e : N ^ (1 - a - 1) = (N ^ a)⁻¹ := by
    rw [← Real.rpow_neg hN.le]; ring_nf
  rw [e]
  have : 0 < N ^ a := by positivity
  field_simp

/-- Exercise 18.1: the steady-state capital–labour ratio `k* = (aA/(1/β − 1 + δ))^{1/(1−a)}`. -/
noncomputable def dm_ex1_kstar (A a β δ : ℝ) : ℝ := (a * A / (1 / β - 1 + δ)) ^ (1 / (1 - a))

/-- Exercise 18.1: the capital Euler equation `1 = β(aAk^{a−1} + 1 − δ)` pins down the
capital–labour ratio uniquely: `k = k*`. -/
theorem dm_ex1_kstar_unique {A a β δ k : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hβ : 0 < β) (hr : 0 < 1 / β - 1 + δ) (hk : 0 < k) :
    1 = β * (a * A * k ^ (a - 1) + 1 - δ) ↔ k = dm_ex1_kstar A a β δ := by
  set r := 1 / β - 1 + δ with hrdef
  have hc : 0 < a * A / r := by positivity
  have hks : 0 < dm_ex1_kstar A a β δ := Real.rpow_pos_of_pos hc _
  have h1a : (1 - a) ≠ 0 := by linarith
  -- `k*^{a−1} = r/(aA)`
  have hkey : dm_ex1_kstar A a β δ ^ (a - 1) = r / (a * A) := by
    rw [dm_ex1_kstar, ← Real.rpow_mul hc.le]
    have : 1 / (1 - a) * (a - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one, inv_div]
  have hEuler : ∀ x, (1 = β * (a * A * x + 1 - δ) ↔ x = r / (a * A)) := by
    intro x
    rw [hrdef]
    constructor
    · intro h; field_simp; field_simp at h; linarith
    · intro h; rw [h]; field_simp; ring
  rw [hEuler, ← hkey]
  constructor
  · intro h
    have hinj : Set.InjOn (fun x : ℝ ↦ x ^ (a - 1)) (Set.Ioi 0) := by
      intro x hx y hy hxy
      have := congrArg (fun z : ℝ ↦ z ^ (1 / (a - 1))) hxy
      simp only at this
      rwa [← Real.rpow_mul (Set.mem_Ioi.mp hx).le, ← Real.rpow_mul (Set.mem_Ioi.mp hy).le,
        mul_one_div_cancel (by linarith : a - 1 ≠ 0), Real.rpow_one, Real.rpow_one] at this
    exact hinj hk hks h
  · intro h; rw [h]

/-- **Exercise 18.1** (Miao, p. 614): **analysis of the steady state**. With `F = AK^aN^{1−a}`
and a constant job-filling rate, in a steady state with `K, N > 0` the capital Euler equation
gives `K/N = k*`; the job creation and wage equations then reduce to the basic DMP equations with
`A` replaced by the marginal product of labour `A_eff = (1 − a)Ak*^a`: `θ` solves (18.18) with
`A_eff`, the wage is on the wage curve with `A_eff`, and on `v = θu` the employment dynamics give
`u = ρ/(ρ + θq(θ))`. -/
theorem dm_ex1_steady (MF : DMMatchingFn) {A a b κ β δ ρ η K N u θ w : ℝ} (hA : 0 < A)
    (ha0 : 0 < a) (ha1 : a < 1) (hβ : 0 < β) (hr : 0 < 1 / β - 1 + δ) (hρ : 0 < ρ)
    (hK : 0 < K) (hN : 0 < N) (hθ : 0 < θ) (hu : 0 < u)
    (hEuler : 1 = β * (a * A * (K / N) ^ (a - 1) + 1 - δ))
    (hJC : κ / dm_q MF θ = β * ((1 - a) * A * (K / N) ^ a - w + (1 - ρ) * κ / dm_q MF θ))
    (hW : w = η * ((1 - a) * A * (K / N) ^ a + κ * θ) + (1 - η) * b)
    (hB : N = (1 - ρ) * N + MF.M u (θ * u)) (hNu : u = 1 - N) :
    K / N = dm_ex1_kstar A a β δ ∧
      dm_ssLHS MF κ β ρ η θ = β * (1 - η) * ((1 - a) * A * dm_ex1_kstar A a β δ ^ a - b) ∧
      w = dm_wageCurve ((1 - a) * A * dm_ex1_kstar A a β δ ^ a) b κ η θ ∧
      u = dm_uStar MF ρ θ := by
  have hk := (dm_ex1_kstar_unique hA ha0 ha1 hβ hr (div_pos hK hN)).mp hEuler
  rw [hk] at hJC hW
  have h16 := (eq_18_16 MF _ κ β ρ w θ).mp hJC
  have h18 := (eq_18_18 MF _ b κ β ρ η w θ).mp ⟨h16, hW⟩
  refine ⟨hk, h18.1, h18.2, (eq_18_19 MF hρ hθ hu).mp ?_⟩
  have hN' : N = 1 - u := by linarith
  rw [hN'] at hB
  linarith

/-- **Exercise 18.1** (Miao, p. 614): the steady state of the economy with capital is a search
equilibrium: with `k = k*`, `θ` solving (18.18) at `A_eff = (1 − a)Ak*^a`, `u = u*`, `N = 1 − u`,
`K = k*N`, `I = δK`, `v = θu`, the wage on the wage curve, dividends
`d = F − wN − κv − δK`, price `p = βd/(1 − β)` and consumption `C = F − δK − κv`. -/
theorem dm_ex1_steady_isSearchEqm (MF : DMMatchingFn) {A a b κ β δ ρ η θ : ℝ} (hA : 0 < A)
    (ha0 : 0 < a) (ha1 : a < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hr : 0 < 1 / β - 1 + δ)
    (hρ : 0 < ρ) (hθ : 0 < θ)
    (h : dm_ssLHS MF κ β ρ η θ = β * (1 - η) * ((1 - a) * A * dm_ex1_kstar A a β δ ^ a - b)) :
    let u := dm_uStar MF ρ θ
    let N := 1 - u
    let K := dm_ex1_kstar A a β δ * N
    let w := dm_wageCurve ((1 - a) * A * dm_ex1_kstar A a β δ ^ a) b κ η θ
    let d := A * K ^ a * N ^ (1 - a) - w * N - κ * (θ * u) - δ * K
    dm_Ex1IsSearchEqm MF (fun k n ↦ A * k ^ a * n ^ (1 - a))
      (fun k n ↦ a * A * (k / n) ^ (a - 1)) (fun k n ↦ (1 - a) * A * (k / n) ^ a)
      b κ β δ ρ η (fun _ ↦ A * K ^ a * N ^ (1 - a) - δ * K - κ * (θ * u)) (fun _ ↦ K)
      (fun _ ↦ δ * K) (fun _ ↦ N) (fun _ ↦ u) (fun _ ↦ θ * u) (fun _ ↦ θ) (fun _ ↦ w)
      (fun _ ↦ dm_q MF θ) (fun _ ↦ β * d / (1 - β)) (fun _ ↦ d) := by
  intro u N K w d t
  obtain ⟨hu0, hu1⟩ := dm_uStar_mem MF hρ hθ
  have hune : u ≠ 0 := hu0.ne'
  have hN : 0 < N := by simp only [N]; linarith
  have hks : 0 < dm_ex1_kstar A a β δ := Real.rpow_pos_of_pos (by positivity) _
  have hkN : K / N = dm_ex1_kstar A a β δ := by simp only [K]; field_simp
  have hB := (eq_18_19 MF hρ hθ hu0).mpr rfl
  have h16 := ((eq_18_18 MF _ b κ β ρ η w θ).mpr ⟨h, rfl⟩).1
  have hβ1' : 1 - β ≠ 0 := by linarith
  refine ⟨hu0, mul_pos hθ hu0, by field_simp, rfl, ?_, by simp only [N]; ring, by ring, rfl,
    ?_, ?_, ?_, ?_, by ring⟩
  · simp only [N]; rw [← hB]; ring
  · field_simp; ring
  · simp only [hkN]
    exact (dm_ex1_kstar_unique hA ha0 ha1 hβ0 hr hks).mpr rfl
  · simp only [hkN]
    exact (eq_18_16 MF _ κ β ρ w θ).mpr h16
  · simp only [hkN, w, dm_wageCurve]

/-- **Exercise 18.1** (Miao, p. 614): a search equilibrium of the economy with capital exists in
a concrete economy (Cobb–Douglas matching `μ = 1`, `α = 1/2`; `A = 1`, `a = 1/3`, `b = 0`,
`κ = 1`, `β = ρ = η = 1/2`, `δ = 1/10`). -/
theorem dm_ex1_searchEqm_exists :
    ∃ C K I N u v θ w qv p d : ℕ → ℝ,
      dm_Ex1IsSearchEqm (dm_cdMatching 1 (1 / 2) one_pos (by norm_num) (by norm_num))
        (fun k n ↦ 1 * k ^ (1 / 3 : ℝ) * n ^ (1 - 1 / 3 : ℝ))
        (fun k n ↦ 1 / 3 * 1 * (k / n) ^ (1 / 3 - 1 : ℝ))
        (fun k n ↦ (1 - 1 / 3) * 1 * (k / n) ^ (1 / 3 : ℝ))
        0 1 (1 / 2) (1 / 10) (1 / 2) (1 / 2) C K I N u v θ w qv p d := by
  have hAe : 0 < (1 - 1 / 3) * 1 * dm_ex1_kstar 1 (1 / 3) (1 / 2) (1 / 10) ^ (1 / 3 : ℝ) := by
    have : 0 < dm_ex1_kstar 1 (1 / 3) (1 / 2) (1 / 10) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  obtain ⟨θ, ⟨hθ, h⟩, -⟩ := dm_cd_ss_existsUnique (μ := 1) (α := 1 / 2) one_pos (by norm_num)
    (by norm_num) (A := (1 - 1 / 3) * 1 * dm_ex1_kstar 1 (1 / 3) (1 / 2) (1 / 10) ^ (1 / 3 : ℝ))
    (b := 0) (κ := 1) (β := 1 / 2) (ρ := 1 / 2) (η := 1 / 2) one_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAe
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, dm_ex1_steady_isSearchEqm _ one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hθ h⟩

end Miao.SearchAndMatching
