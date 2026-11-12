/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Hyperinflations in the cash-in-advance model

AKMM, §17.3.3, "Hyperinflation", pp. 512–513, with footnotes 11–12. In the CIA model with a
binding constraint, `z = 1`, money growth `M_{t+1} = γM_t` (`γ > 1`) and `u(c, l) = u(c) + l`, real
balances satisfy (17.38) `γm_t = βm_{t+1}u′(m_{t+1})`, with no initial condition.

* `eq_17_36`, `eq_17_37`, `eq_17_38`: the derivation from (17.20)–(17.23).
* `hypIsPath`; `hyp_steady_iff`: the positive steady state `u′(m̄) = γ/β`.
* `hyp_exists_path`: if `u′` is positive, continuous and strictly decreasing and
  `lim_{m→0} m u′(m) = 0`, then from every `m₀ ∈ (0, m̄)` there is a path of (17.38), strictly
  decreasing, converging to `0`.
* `hyp_all_paths`: if moreover `m u′(m)` is strictly increasing, the path from `m₀` is unique
  and every path with `m₀ ∈ (0, m̄)` decreases to `0`; paths with `m₀ > m̄` increase
  (`hyp_above_increasing`), so `m̄` is unstable (footnote 11).
* `hyp_return_lt`: along such paths the real return on money is below the stationary `1/γ`, so
  the CIA binds (footnote 11).
* `hyp_local_stable`, `hyp_local_unstable`: local stability at `0` when `u′ > γ/β` near `0`,
  instability when `u′ < γ/β` near `0` (footnote 11, `u′(0) ≷ γ/β`).
* `hyp_log_unique`: with `u = log`, `m_t = β/γ` is the unique path (footnote 12).

**Departure.** The book says that "for any initial real balances `0 < m₀ < m̄` the path of real
balances defined by (17.38) converges" to zero. Equation (17.38) defines `m_{t+1}` only
implicitly; without monotonicity of `m u′(m)` it may have several solutions, and we prove
existence of a convergent path (`hyp_exists_path`). Convergence of every path, and uniqueness,
are proved under the added hypothesis that `m u′(m)` is strictly increasing (`hyp_all_paths`).
-/

open Filter Topology

namespace AKMM.Money

/-- **AKMM, (17.36)**, p. 513: with a binding CIA, `z = w = 1`, (17.20) `u₁ = λ + µ`, (17.21)
`u₂ = λ` and (17.23) `λ_tR_t = β(λ_{t+1} + µ_{t+1})`, `R_t = p_{m,t}/p_{m,t+1}`, give
`u₂(t)R_t = βu₁(t + 1)`. -/
theorem eq_17_36 {β : ℝ} {U1 U2 lam mu R : ℕ → ℝ} (h20 : ∀ t, U1 t = lam t + mu t)
    (h21 : ∀ t, U2 t = lam t) (h23 : ∀ t, lam t * R t = β * (lam (t + 1) + mu (t + 1)))
    (t : ℕ) : U2 t * R t = β * U1 (t + 1) := by
  rw [h21, h23, h20]

/-- **AKMM, (17.37)**, p. 513: with `M_{t+1} = γM_t` and `m_t = p_{m,t}M_t`,
`p_{m,t}/p_{m,t+1} = γm_t/m_{t+1}`. -/
theorem eq_17_37 {γ pt pt1 Mt : ℝ} (hγ : γ ≠ 0) (hpt1 : pt1 ≠ 0) (hM : Mt ≠ 0) :
    pt / pt1 = γ * (pt * Mt) / (pt1 * (γ * Mt)) := by
  field_simp

/-- **AKMM, (17.38)**, p. 513: with `u(c, l) = u(c) + l` (`u₂ = 1`, `u₁ = u′(c)`, `c = m`),
(17.37) `γu₂m_t/m_{t+1} = βu₁(t + 1)` is `γm_t = βm_{t+1}u′(m_{t+1})`. -/
theorem eq_17_38 {β γ mt mt1 du1 : ℝ} (hmt1 : mt1 ≠ 0) :
    γ * 1 * mt / mt1 = β * du1 ↔ γ * mt = β * (mt1 * du1) := by
  rw [mul_one, div_eq_iff hmt1]
  constructor <;> intro h <;> linarith

/-- AKMM, (17.38): a path of positive real balances. -/
def hypIsPath (β γ : ℝ) (du : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ γ * m t = β * (m (t + 1) * du (m (t + 1)))

/-- AKMM, p. 513: a constant `m̄ > 0` is a path iff `u′(m̄) = γ/β`. -/
theorem hyp_steady_iff {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hmb : 0 < mb) :
    hypIsPath β γ du (fun _ => mb) ↔ du mb = γ / β := by
  unfold hypIsPath
  constructor
  · intro h
    have := (h 0).2
    field_simp
    nlinarith [this]
  · intro h t
    refine ⟨hmb, ?_⟩
    rw [h]; field_simp

/-- One step of (17.38) downward: if `u′` is continuous and strictly decreasing on `(0, ∞)`,
`m u′(m) → 0` as `m → 0⁺`, `u′(m̄) = γ/β` and `0 < x < m̄`, there is `y ∈ (0, x)` with
`γx = βyu′(y)`. -/
theorem hyp_step_exists {β γ mb x : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hlim : Tendsto (fun m => m * du m) (𝓝[>] 0) (𝓝 0)) (hmb : du mb = γ / β)
    (hx : 0 < x) (hxm : x < mb) : ∃ y, 0 < y ∧ y < x ∧ γ * x = β * (y * du y) := by
  have htar : 0 < γ * x / β := by positivity
  have hgx : γ * x / β < x * du x := by
    have : γ / β < du x := hmb ▸ hanti hx (hx.trans hxm) hxm
    calc γ * x / β = x * (γ / β) := by ring
      _ < x * du x := mul_lt_mul_of_pos_left this hx
  obtain ⟨ε, hε, hε0, hεx⟩ : ∃ ε, ε * du ε < γ * x / β ∧ 0 < ε ∧ ε < x := by
    have h1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m * du m < γ * x / β := hlim (gt_mem_nhds htar)
    have h2 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ∈ Set.Ioo 0 x := Ioo_mem_nhdsGT hx
    obtain ⟨ε, h1', h2'⟩ := (h1.and h2).exists
    exact ⟨ε, h1', h2'⟩
  have hgc : ContinuousOn (fun m => m * du m) (Set.Icc ε x) :=
    continuousOn_id.mul (hcont.mono fun m hm => lt_of_lt_of_le hε0 hm.1)
  obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc hεx.le hgc ⟨hε.le, hgx.le⟩
  refine ⟨y, lt_of_lt_of_le hε0 hy.1, lt_of_le_of_ne hy.2 ?_, ?_⟩
  · rintro rfl; simp only at hyv; linarith
  · simp only at hyv; rw [hyv]; field_simp

/-- A strictly decreasing path of (17.38) starting below `m̄` converges to `0` (`u′` continuous
and strictly decreasing, so `m̄` is the only positive steady state). -/
theorem hyp_tendsto_zero {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hmb : du mb = γ / β) (hmb0 : 0 < mb) {m : ℕ → ℝ} (hm : hypIsPath β γ du m)
    (hdec : Antitone m) (h0 : m 0 < mb) : Tendsto m atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range m) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hm t).1.le⟩
  have hL := tendsto_atTop_ciInf hdec hbdd
  set L := ⨅ t, m t
  have hL0 : 0 ≤ L := le_ciInf fun t => (hm t).1.le
  rcases hL0.lt_or_eq with hLpos | hLz
  · exfalso
    have hshift : Tendsto (fun t => m (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have hcL : ContinuousAt du L := hcont.continuousAt (Ioi_mem_nhds hLpos)
    have hlhs : Tendsto (fun t => γ * m t) atTop (𝓝 (γ * L)) := hL.const_mul γ
    have hrhs : Tendsto (fun t => β * (m (t + 1) * du (m (t + 1)))) atTop
        (𝓝 (β * (L * du L))) := (hshift.mul (hcL.tendsto.comp hshift)).const_mul β
    have heq : γ * L = β * (L * du L) :=
      tendsto_nhds_unique hlhs (hrhs.congr fun t => ((hm t).2).symm)
    have hduL : du L = γ / β := by field_simp; nlinarith [heq]
    have hLle : L ≤ m 0 := ciInf_le hbdd 0
    have : L = mb := hanti.injOn hLpos hmb0 (hduL.trans hmb.symm)
    linarith
  · rw [← hLz] at hL; exact hL

/-- **AKMM, p. 513: hyperinflation paths.** If `u′` is continuous and strictly
decreasing on `(0, ∞)`, `lim_{m→0} m u′(m) = 0` and `u′(m̄) = γ/β`, `m̄ > 0`, then for every
`m₀ ∈ (0, m̄)` there is a path of (17.38) from `m₀` that is strictly decreasing and converges to
zero: the value of real balances vanishes in the limit. -/
theorem hyp_exists_path {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hlim : Tendsto (fun m => m * du m) (𝓝[>] 0) (𝓝 0)) (hmb : du mb = γ / β) (hmb0 : 0 < mb)
    {m0 : ℝ} (h0 : 0 < m0) (h1 : m0 < mb) :
    ∃ m : ℕ → ℝ, m 0 = m0 ∧ hypIsPath β γ du m ∧ StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  classical
  have hex : ∀ x, 0 < x ∧ x < mb → ∃ y, 0 < y ∧ y < x ∧ γ * x = β * (y * du y) :=
    fun x hx => hyp_step_exists hβ hγ hcont hanti hlim hmb hx.1 hx.2
  let step : ℝ → ℝ := fun x => if h : 0 < x ∧ x < mb then Classical.choose (hex x h) else 0
  have hstep : ∀ x, 0 < x → x < mb →
      0 < step x ∧ step x < x ∧ γ * x = β * (step x * du (step x)) := fun x hx hxm => by
    have h : 0 < x ∧ x < mb := ⟨hx, hxm⟩
    simp only [step, h, and_self, ↓reduceDIte]
    exact Classical.choose_spec (hex x h)
  let m : ℕ → ℝ := fun t => step^[t] m0
  have hsucc : ∀ t, m (t + 1) = step (m t) := fun t => Function.iterate_succ_apply' _ _ _
  have hinv : ∀ t, 0 < m t ∧ m t < mb := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      rw [hsucc]
      obtain ⟨a, b, -⟩ := hstep _ ih.1 ih.2
      exact ⟨a, b.trans ih.2⟩
  have hpath : hypIsPath β γ du m := fun t => by
    refine ⟨(hinv t).1, ?_⟩
    rw [hsucc]; exact (hstep _ (hinv t).1 (hinv t).2).2.2
  have hanti' : StrictAnti m := strictAnti_nat_of_succ_lt fun t => by
    rw [hsucc]; exact (hstep _ (hinv t).1 (hinv t).2).2.1
  exact ⟨m, rfl, hpath, hanti', hyp_tendsto_zero hβ hcont hanti hmb hmb0 hpath
    hanti'.antitone h1⟩

/-- **AKMM, p. 513**, under the added hypothesis that `m u′(m)` is strictly increasing: every
path of (17.38) with `m₀ ∈ (0, m̄)` is strictly decreasing and converges to `0`, and the path is
determined by `m₀`. -/
theorem hyp_all_paths {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hg : StrictMonoOn (fun m => m * du m) (Set.Ioi 0)) (hmb : du mb = γ / β) (hmb0 : 0 < mb)
    {m : ℕ → ℝ} (hm : hypIsPath β γ du m) (h1 : m 0 < mb) :
    StrictAnti m ∧ Tendsto m atTop (𝓝 0) ∧
      ∀ m' : ℕ → ℝ, hypIsPath β γ du m' → m' 0 = m 0 → m' = m := by
  have hdec : ∀ t, m t < mb → m (t + 1) < m t := fun t ht => by
    have hlt : γ / β < du (m t) := hmb ▸ hanti (hm t).1 hmb0 ht
    have : m (t + 1) * du (m (t + 1)) < m t * du (m t) := by
      have e := (hm t).2
      have : γ * m t < β * (m t * du (m t)) := by
        have := mul_lt_mul_of_pos_left hlt (mul_pos hβ (hm t).1)
        rw [show β * (m t) * (γ / β) = γ * m t by field_simp] at this
        linarith
      nlinarith
    by_contra hn
    have := hg.le_iff_le (hm t).1 (hm (t + 1)).1 |>.2 (not_lt.1 hn)
    linarith
  have hbelow : ∀ t, m t < mb := fun t => by
    induction t with
    | zero => exact h1
    | succ n ih => exact (hdec n ih).trans ih
  have hsa : StrictAnti m := strictAnti_nat_of_succ_lt fun t => hdec t (hbelow t)
  refine ⟨hsa, hyp_tendsto_zero hβ hcont hanti hmb hmb0 hm hsa.antitone h1,
    fun m' hm' h0 => funext fun t => ?_⟩
  induction t with
  | zero => exact h0
  | succ n ih =>
    have e1 := (hm' n).2
    have e2 := (hm n).2
    rw [ih] at e1
    exact hg.injOn (hm' (n + 1)).1 (hm (n + 1)).1
      (mul_left_cancel₀ hβ.ne' (e1.symm.trans e2))

/-- AKMM, footnote 11, p. 513: with `m u′(m)` strictly increasing, a path starting above `m̄`
is strictly increasing: the monetary steady state is unstable. -/
theorem hyp_above_increasing {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hg : StrictMonoOn (fun m => m * du m) (Set.Ioi 0))
    (hmb : du mb = γ / β) (hmb0 : 0 < mb) {m : ℕ → ℝ} (hm : hypIsPath β γ du m)
    (h1 : mb < m 0) : StrictMono m := by
  have hinc : ∀ t, mb < m t → m t < m (t + 1) := fun t ht => by
    have hlt : du (m t) < γ / β := hmb ▸ hanti hmb0 (hm t).1 ht
    have : m t * du (m t) < m (t + 1) * du (m (t + 1)) := by
      have e := (hm t).2
      have : β * (m t * du (m t)) < γ * m t := by
        have := mul_lt_mul_of_pos_left hlt (mul_pos hβ (hm t).1)
        rw [show β * (m t) * (γ / β) = γ * m t by field_simp] at this
        linarith
      nlinarith
    by_contra hn
    have := hg.le_iff_le (hm (t + 1)).1 (hm t).1 |>.2 (not_lt.1 hn)
    linarith
  have habove : ∀ t, mb < m t := fun t => by
    induction t with
    | zero => exact h1
    | succ n ih => exact ih.trans (hinc n ih)
  exact strictMono_nat_of_lt_succ fun t => hinc t (habove t)

/-- AKMM, footnote 11, p. 513: along a decreasing path the gross real return on money
`p_{m,t+1}/p_{m,t} = m_{t+1}/(γm_t)` is below its stationary value `1/γ`, so the CIA binds. -/
theorem hyp_return_lt {γ mt mt1 : ℝ} (hγ : 0 < γ) (hmt : 0 < mt) (hlt : mt1 < mt) :
    mt1 / (γ * mt) < 1 / γ := by
  rw [div_lt_div_iff₀ (by positivity) hγ]; nlinarith

/-- AKMM, footnote 11, p. 513 (local stability at zero): if `u′ ≥ k > γ/β` on `(0, δ)`, every
path staying in `(0, δ)` satisfies `m_t ≤ (γ/(βk))ᵗ m₀` and converges to zero. -/
theorem hyp_local_stable {β γ k δ : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hk : γ / β < k) (hδ : ∀ m, 0 < m → m < δ → k ≤ du m) {m : ℕ → ℝ} (hm : hypIsPath β γ du m)
    (hin : ∀ t, m t < δ) : (∀ t, m t ≤ (γ / (β * k)) ^ t * m 0) ∧ Tendsto m atTop (𝓝 0) := by
  have hk0 : 0 < k := lt_trans (by positivity) hk
  have hstep : ∀ t, m (t + 1) ≤ γ / (β * k) * m t := fun t => by
    have hdu := hδ _ (hm (t + 1)).1 (hin (t + 1))
    have e := (hm t).2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hdu (mul_nonneg hβ.le (hm (t + 1)).1.le)
    nlinarith
  have hbound : ∀ t, m t ≤ (γ / (β * k)) ^ t * m 0 := fun t => by
    induction t with
    | zero => simp
    | succ n ih =>
      calc m (n + 1) ≤ γ / (β * k) * m n := hstep n
        _ ≤ γ / (β * k) * ((γ / (β * k)) ^ n * m 0) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (γ / (β * k)) ^ (n + 1) * m 0 := by ring
  refine ⟨hbound, ?_⟩
  have hr : γ / (β * k) < 1 := by
    rw [div_lt_one (by positivity)]
    rwa [div_lt_iff₀ hβ, mul_comm] at hk
  have hlim : Tendsto (fun t => (γ / (β * k)) ^ t * m 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).mul_const (m 0)
  exact squeeze_zero (fun t => (hm t).1.le) hbound hlim

/-- AKMM, footnote 11, p. 513 (instability at zero): if `0 < u′ ≤ k < γ/β` on `(0, δ)`, a path
in `(0, δ)` moves away from zero, `m_{t+1} ≥ (γ/(βk))m_t > m_t`. -/
theorem hyp_local_unstable {β γ k δ : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hk0 : 0 < k)
    (hk : k < γ / β) (hδ : ∀ m, 0 < m → m < δ → du m ≤ k) {m : ℕ → ℝ}
    (hm : hypIsPath β γ du m) (t : ℕ) (hin : m (t + 1) < δ) :
    γ / (β * k) * m t ≤ m (t + 1) ∧ m t < m (t + 1) := by
  have hdu := hδ _ (hm (t + 1)).1 hin
  have e := (hm t).2
  have h1 : γ / (β * k) * m t ≤ m (t + 1) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hdu (mul_nonneg hβ.le (hm (t + 1)).1.le)
    nlinarith
  refine ⟨h1, lt_of_lt_of_le ?_ h1⟩
  have : 1 < γ / (β * k) := by
    rw [one_lt_div (by positivity)]
    rwa [lt_div_iff₀ hβ, mul_comm] at hk
  nlinarith [(hm t).1]

/-- AKMM, footnote 12, p. 513: with `u = log` (`u′(m) = 1/m`), (17.38) reads `γm_t = β`: the
unique path is `m_t = β/γ`. -/
theorem hyp_log_unique {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (m : ℕ → ℝ) :
    hypIsPath β γ (fun x => x⁻¹) m ↔ ∀ t, m t = β / γ := by
  constructor
  · intro h t
    have e := (h t).2
    rw [mul_inv_cancel₀ (h (t + 1)).1.ne', mul_one] at e
    rw [eq_div_iff hγ.ne']; linarith
  · intro h t
    refine ⟨by rw [h]; positivity, ?_⟩
    rw [h, h, mul_inv_cancel₀ (by positivity), mul_one]; field_simp

end AKMM.Money
